//! Serialization of protocol objects: their byte encoding on the wire and, with the cargo
//! feature `serde`, JSON-friendly text forms.
//!
//! # Bytes
//!
//! The wire format is the arkworks **compressed** canonical encoding, **validated**, without
//! trailing bytes: [`to_bytes`], [`from_bytes`] and the blanket trait [`WireFormat`].
//! A Fiat-Shamir proof ([`FSProof`](crate::sigma::FSProof)) encodes itself: its number of
//! responses as a little-endian `u64`, then its NARG string, whose scalars are big-endian as
//! `draft-irtf-cfrg-sigma-protocols-04` writes them.
//!
//! Implementation notes (not claims of the paper; the paper only asks to "reject malformed
//! input", construction box, `VerifyAtt` step 3 and `VerifyProof` step 3):
//!
//! * Compressed decoding with validation checks that a point is on the curve and in the
//!   prime-order subgroup and that a scalar is canonical (`< p`), so `z` and `z + p` are never
//!   both accepted. Uncompressed input is never accepted by this crate: for BLS12-381 the
//!   uncompressed validated path of arkworks 0.6.0 skips the curve equation.
//! * arkworks validation **accepts** the identity point and the zero scalar. Every
//!   non-degeneracy requirement of the paper (`T ≠ 1`, `σ'_1 ≠ 1`, ...) is therefore an explicit
//!   check in the verifier of the corresponding relation, never a property of decoding. This is
//!   about the VALUES of a statement. One parameter type adds a check of its own to validated
//!   decoding: [`DY`](crate::kiprf::DY) refuses the identity in the place of its
//!   generator, for liveness and not for soundness (module docs of [`crate::kiprf::dy`],
//!   "Degenerate parameters"); its verifier-side check stays in place all the same.
//! * `deserialize_*` reads a prefix of its input; [`from_bytes`] additionally rejects leftovers,
//!   so every accepted byte string is the unique encoding of the value it decodes to.
//!
//! # Text forms (cargo feature `serde`)
//!
//! Implementation note: nothing here is part of the paper. The canonical wire format of this
//! crate stays the byte encoding above (and the fixed-format compact codec of
//! [`crate::pcreds::codec`]);
//! the `serde` layer wraps it for consumers whose messages and stores are JSON (`serde_json`,
//! JCS-canonicalised documents, multibase strings). Its items are `to_multibase`,
//! `from_multibase` and the `#[serde(with = …)]` adapters `canonical` and `secret`.
//!
//! ## Two shapes
//!
//! * **Opaque.** A value with a canonical encoding is ONE string: the multibase **base58btc**
//!   text (prefix `z`) of its compressed canonical bytes, the convention of a W3C Data Integrity
//!   `proofValue`. Keys, credentials, pre-credentials, shows, public parameters, tag parameters,
//!   [`FSProof`](crate::sigma::FSProof) and the secrets are opaque.
//! * **Structured.** The messages of the protocol,
//!   [`AttestationRequest`](crate::pcreds::AttestationRequest),
//!   [`Attestation`](crate::pcreds::Attestation),
//!   [`CredentialRequest`](crate::pcreds::CredentialRequest),
//!   [`Reply`](crate::pcreds::Reply) and [`MembershipProof`](crate::pcreds::MembershipProof), are
//!   JSON objects with camelCase members whose leaves are opaque strings, so that an application
//!   can read, say, the tag of every attestation of a request without decoding group elements:
//!
//! ```json
//! { "tag": "z…", "show": "z…", "proof": "z…" }
//! ```
//!
//! ## Code that is generic over the base or the tag
//!
//! The `Serialize` / `Deserialize` impls of keys, credentials and the like exist per type
//! (`PSVerificationKey`, `BBSPreCredential`, …), not on the associated types of the traits:
//! adding `serde` bounds to [`Backend`](crate::pcreds::Backend) behind a feature would change
//! the trait for every implementor. Generic code uses the adapters instead, which work for
//! anything with a canonical encoding:
//!
//! ```
//! use predicate_credential_system::pcreds::Backend;
//!
//! #[derive(serde::Serialize, serde::Deserialize)]
//! #[serde(bound = "")]
//! struct JoinReply<Bk: Backend> {
//!     #[serde(with = "predicate_credential_system::serialization::canonical")]
//!     pre_credential: Bk::PreCredential,
//! }
//! ```
//!
//! ## Strictness
//!
//! Decoding accepts exactly what encoding produces: base58btc only (any other multibase prefix is
//! an error), compressed canonical bytes, validated group elements (on the curve and in the
//! prime-order subgroup), canonical scalars, no trailing bytes, a structured message only as a
//! map with exactly its members, each once (not as the array of its members, which the derived
//! decoders of `serde` would take), and a [`Reply`](crate::pcreds::Reply) only as `"fail"`,
//! `"issued"` or `{"preCredential": …}`. One object therefore has one JSON form, as it has one
//! binary form. As everywhere in this crate, decoding
//! says nothing about the VALIDITY of an object: the verifiers decide that, and they re-validate
//! what they are given.
//!
//! ## Secrets
//!
//! [`User`](crate::pcreds::User), [`Credential`](crate::pcreds::Credential),
//! [`IssuanceState`](crate::pcreds::IssuanceState) and the signing keys of the bases implement
//! the traits as well, because a consumer has to keep them somewhere (an issuance state, for
//! instance, lives from the credential request until the helper answers). Their text form IS
//! the secret: serialize them only into protected storage and never into logs or messages. The
//! buffers this module owns are wiped after use; copies made inside `serde`, `multibase` or the
//! chosen data format are out of its reach. The helper's key has its own wiped encoding
//! ([`Helper::to_bytes`](crate::pcreds::Helper::to_bytes)).
//!
//! ## Example
//!
//! ```
//! use ark_bls12_381::{Bls12_381, G1Projective};
//! use predicate_credential_system::{
//!     hash::bls12_381::G1Hasher,
//!     kiprf::DDH,
//!     pcreds::{Reply, pairing::{PS, PairingBackend}},
//! };
//!
//! type Bk = PairingBackend<Bls12_381, PS, DDH<G1Projective, G1Hasher>>;
//! let json = serde_json::to_string(&Reply::<Bk>::Issued).unwrap();
//! assert_eq!(json, r#""issued""#);
//! assert_eq!(serde_json::from_str::<Reply<Bk>>(&json).unwrap(), Reply::Issued);
//! ```

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::error::Error;

/// Encodes `value` in the compressed canonical encoding.
///
/// # Errors
/// [`Error::Serialization`] if the value's serializer fails (arkworks group and field elements
/// never do when writing into memory).
pub fn to_bytes<T: CanonicalSerialize + ?Sized>(value: &T) -> Result<Vec<u8>, Error> {
    let mut bytes = Vec::with_capacity(value.compressed_size());
    value.serialize_compressed(&mut bytes)?;
    Ok(bytes)
}

/// Decodes a value from its compressed canonical encoding, with full validation, and rejects
/// trailing bytes.
///
/// # Errors
/// [`Error::Serialization`] for malformed, non-canonical, off-curve or wrong-subgroup input and
/// [`Error::TrailingBytes`] if `bytes` continues after the value.
pub fn from_bytes<T: CanonicalDeserialize>(bytes: &[u8]) -> Result<T, Error> {
    let mut reader = bytes;
    let value = T::deserialize_compressed(&mut reader)?;
    if reader.is_empty() {
        Ok(value)
    } else {
        Err(Error::TrailingBytes)
    }
}

/// Method-call sugar for [`to_bytes`] / [`from_bytes`], implemented for every canonically
/// serializable type (in particular for every public protocol object of this crate).
pub trait WireFormat: CanonicalSerialize + CanonicalDeserialize + Sized {
    /// See [`to_bytes`].
    ///
    /// # Errors
    /// See [`to_bytes`].
    fn to_bytes(&self) -> Result<Vec<u8>, Error> {
        to_bytes(self)
    }

    /// See [`from_bytes`].
    ///
    /// # Errors
    /// See [`from_bytes`].
    fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        from_bytes(bytes)
    }
}

impl<T: CanonicalSerialize + CanonicalDeserialize> WireFormat for T {}

/// The length of the longest multibase base58btc text (`z…`, feature `serde`) of a value of at
/// most `bytes` bytes: the prefix, then at most $`\lceil n\log 256/\log 58\rceil`$ digits for
/// $`n`$ bytes (a leading zero byte is one digit `1`), bounded above by $`1.3657\,n+1`$, as
/// $`\log 256/\log 58 < 1.36566`$. The JSON decoders of the messages refuse a longer leaf
/// before they decode it ([`crate::pcreds::Backend::max_leaf_bytes`]).
#[must_use]
pub const fn max_multibase_len(bytes: usize) -> usize {
    bytes.saturating_mul(13_657) / 10_000 + 2
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Fr, G1Affine, G1Projective};
    use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
    use ark_ff::{BigInteger, PrimeField, Zero};

    use super::*;

    #[test]
    fn round_trip_and_sizes() {
        let p = G1Projective::generator() * Fr::from(7u64);
        let bytes = p.to_bytes().unwrap();
        assert_eq!(bytes.len(), 48);
        assert_eq!(G1Projective::from_bytes(&bytes).unwrap(), p);
        // projective and affine encodings coincide
        assert_eq!(p.into_affine().to_bytes().unwrap(), bytes);

        let s = Fr::from(123_456_789u64);
        let bytes = s.to_bytes().unwrap();
        assert_eq!(bytes.len(), 32);
        assert_eq!(Fr::from_bytes(&bytes).unwrap(), s);
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        let mut bytes = Fr::from(5u64).to_bytes().unwrap();
        bytes.push(0);
        assert_eq!(Fr::from_bytes(&bytes), Err(Error::TrailingBytes));
    }

    #[test]
    fn truncated_input_is_rejected() {
        let bytes = G1Affine::generator().to_bytes().unwrap();
        assert!(matches!(
            G1Affine::from_bytes(&bytes[..47]),
            Err(Error::Serialization(_))
        ));
        assert!(matches!(
            G1Affine::from_bytes(&[]),
            Err(Error::Serialization(_))
        ));
    }

    #[test]
    fn non_canonical_scalar_is_rejected() {
        // the modulus itself is the smallest non-canonical encoding
        let modulus = Fr::MODULUS.to_bytes_le();
        assert_eq!(modulus.len(), 32);
        assert!(matches!(
            Fr::from_bytes(&modulus),
            Err(Error::Serialization(_))
        ));
        assert!(matches!(
            Fr::from_bytes(&[0xff; 32]),
            Err(Error::Serialization(_))
        ));
    }

    #[test]
    fn malformed_point_is_rejected() {
        // all-zero bytes are not a valid compressed BLS12-381 point (the compression flag is unset)
        assert!(matches!(
            G1Affine::from_bytes(&[0u8; 48]),
            Err(Error::Serialization(_))
        ));
    }

    /// Documents the hazard the module docs warn about: decoding does NOT reject the identity.
    #[test]
    fn identity_decodes_successfully() {
        let bytes = G1Affine::zero().to_bytes().unwrap();
        assert_eq!(bytes[0], 0xc0);
        assert!(G1Affine::from_bytes(&bytes).unwrap().is_zero());
        assert!(Fr::from_bytes(&[0u8; 32]).unwrap().is_zero());
    }
}

// ---------------------------------------------------------------------------------------------
// Text forms (cargo feature `serde`)
// ---------------------------------------------------------------------------------------------

#[cfg(feature = "serde")]
pub use self::text::{canonical, from_multibase, secret, to_multibase};

/// The `serde` layer (module docs, "Text forms"). One private module, so that a single `cfg`
/// switches it off; its public items are re-exported above.
#[cfg(feature = "serde")]
mod text {
    use ark_ec::{PrimeGroup, pairing::Pairing};
    use ark_ff::PrimeField;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use zeroize::Zeroizing;

    use crate::{
        error::Error,
        hash::HashToGroup,
        kiprf::{DDH, DY, ProtocolTag},
        pcreds::{
            Attestation, AttestationRequest, Backend, Credential, CredentialRequest,
            IssuanceRecord, IssuanceState, Leaf, MembershipProof, ProofKind, PublicParameters,
            Reply, User,
            pairing::{
                BBSCredential, BBSParams, BBSPreCredential, BBSShow, BBSSigningKey,
                BBSVerificationKey, Base, G1Request, PSPair, PSSigningKey, PSVerificationKey,
                PairingParams,
            },
        },
        sigma::FSProof,
    };
    #[cfg(feature = "lattice")]
    use crate::{
        kiprf::lwr::LWRTag,
        lattice::{Rq, Ternary},
        pcreds::lattice::{
            LatticeParams, LatticePoint, LatticeProof,
            base::{
                VSISCredential, VSISParams, VSISPreCredential, VSISSigningKey, VSISTape,
                VSISVerificationKey,
            },
        },
    };

    /// The one multibase base this module emits and accepts: base58btc, prefix `z`.
    const BASE: multibase::Base = multibase::Base::Base58Btc;

    /// The multibase base58btc text (`z…`) of `bytes`.
    #[must_use]
    pub fn to_multibase(bytes: &[u8]) -> String {
        multibase::encode(BASE, bytes)
    }

    /// The bytes of a multibase base58btc text; the inverse of [`to_multibase`].
    ///
    /// # Errors
    /// [`Error::Serialization`] if `text` is not multibase or uses another base than base58btc.
    pub fn from_multibase(text: &str) -> Result<Vec<u8>, Error> {
        match multibase::decode(text) {
            Ok((BASE, bytes)) => Ok(bytes),
            Ok((base, bytes)) => {
                drop(Zeroizing::new(bytes));
                Err(Error::Serialization(format!(
                    "multibase base {base:?} is not accepted, expected base58btc (prefix 'z')"
                )))
            }
            Err(e) => Err(Error::Serialization(format!("invalid multibase text: {e}"))),
        }
    }

    /// `#[serde(with = "predicate_credential_system::serialization::canonical")]`: any value with a canonical encoding as
    /// one opaque multibase string (compressed, validated, no trailing bytes).
    pub mod canonical {
        use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
        use serde::{Deserialize, Deserializer, Serializer, de::Error as _, ser::Error as _};

        use super::{from_multibase, to_multibase};
        use crate::serialization;

        /// Serializes `value` as the multibase text of its compressed canonical bytes.
        ///
        /// # Errors
        /// The serializer's error if the value cannot be encoded.
        pub fn serialize<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
        where
            T: CanonicalSerialize + ?Sized,
            S: Serializer,
        {
            let bytes = serialization::to_bytes(value).map_err(S::Error::custom)?;
            serializer.serialize_str(&to_multibase(&bytes))
        }

        /// Deserializes a value from the multibase text of its compressed canonical bytes.
        ///
        /// # Errors
        /// The deserializer's error for anything but the strict form described in the
        /// [module docs](crate::serialization).
        pub fn deserialize<'de, T, D>(deserializer: D) -> Result<T, D::Error>
        where
            T: CanonicalDeserialize,
            D: Deserializer<'de>,
        {
            let text = String::deserialize(deserializer)?;
            let bytes = from_multibase(&text).map_err(D::Error::custom)?;
            serialization::from_bytes(&bytes).map_err(D::Error::custom)
        }
    }

    /// As [`canonical`], for secrets: the buffers this module owns are wiped after use.
    pub mod secret {
        use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
        use serde::{Deserialize, Deserializer, Serializer, de::Error as _, ser::Error as _};
        use zeroize::Zeroizing;

        use super::{from_multibase, to_multibase};
        use crate::serialization;

        /// Serializes the secret `value` as the multibase text of its compressed canonical bytes.
        ///
        /// # Errors
        /// The serializer's error if the value cannot be encoded.
        pub fn serialize<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
        where
            T: CanonicalSerialize + ?Sized,
            S: Serializer,
        {
            let bytes = Zeroizing::new(serialization::to_bytes(value).map_err(S::Error::custom)?);
            serialize_bytes(&bytes, serializer)
        }

        /// Serializes already encoded secret bytes.
        pub(super) fn serialize_bytes<S: Serializer>(
            bytes: &[u8],
            serializer: S,
        ) -> Result<S::Ok, S::Error> {
            let text = Zeroizing::new(to_multibase(bytes));
            serializer.serialize_str(&text)
        }

        /// The decoded bytes of a secret, in a buffer that is wiped on drop.
        pub(super) fn deserialize_bytes<'de, D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<Zeroizing<Vec<u8>>, D::Error> {
            let text = Zeroizing::new(String::deserialize(deserializer)?);
            from_multibase(&text)
                .map(Zeroizing::new)
                .map_err(D::Error::custom)
        }

        /// Deserializes a secret from the multibase text of its compressed canonical bytes.
        ///
        /// # Errors
        /// The deserializer's error for anything but the strict form described in the
        /// [module docs](crate::serialization).
        pub fn deserialize<'de, T, D>(deserializer: D) -> Result<T, D::Error>
        where
            T: CanonicalDeserialize,
            D: Deserializer<'de>,
        {
            let bytes = deserialize_bytes(deserializer)?;
            serialization::from_bytes(&bytes).map_err(D::Error::custom)
        }
    }

    /// Opaque implementations through [`canonical`] / [`secret`].
    macro_rules! opaque {
        ($adapter:ident: $( impl[$($generics:tt)*] $ty:ty; )+) => {$(
            impl<$($generics)*> Serialize for $ty {
                fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                    $adapter::serialize(self, serializer)
                }
            }

            impl<'de, $($generics)*> Deserialize<'de> for $ty {
                fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                    $adapter::deserialize(deserializer)
                }
            }
        )+};
    }

    opaque! { canonical:
        impl[F: PrimeField] FSProof<F>;
        impl[Bk: Backend] PublicParameters<Bk>;
        impl[E: Pairing, B: Base<E>, T: ProtocolTag<E::G1>] PairingParams<E, B, T>;
        impl[G: PrimeGroup, H: HashToGroup<G>] DDH<G, H>;
        impl[G: PrimeGroup, H] DY<G, H>;
        impl[E: Pairing] PSVerificationKey<E>;
        impl[E: Pairing] PSPair<E>;
        impl[E: Pairing] G1Request<E>;
        impl[E: Pairing] BBSParams<E>;
        impl[E: Pairing] BBSVerificationKey<E>;
        impl[E: Pairing] BBSPreCredential<E>;
        impl[E: Pairing] BBSShow<E>;
        impl[] IssuanceRecord;
    }

    opaque! { secret:
        impl[Bk: Backend] User<Bk>;
        impl[Bk: Backend] Credential<Bk>;
        impl[Bk: Backend] IssuanceState<Bk>;
        impl[E: Pairing] PSSigningKey<E>;
        impl[E: Pairing] BBSSigningKey<E>;
        impl[E: Pairing] BBSCredential<E>;
    }

    #[cfg(feature = "lattice")]
    opaque! { canonical:
        impl[] LatticeParams;
        impl[] LatticePoint;
        impl[] LatticeProof;
        impl[] VSISParams;
        impl[] VSISVerificationKey;
        impl[] VSISPreCredential;
        impl[] LWRTag;
        impl[] Rq;
    }

    #[cfg(feature = "lattice")]
    opaque! { secret:
        impl[] VSISSigningKey;
        impl[] VSISCredential;
        impl[] VSISTape;
        impl[] Ternary;
    }

    // ---------------------------------------------------------------------------------------------
    // The structured messages: ONE JSON form each
    // ---------------------------------------------------------------------------------------------

    /// The role of a leaf of a structured message ([`Leaf`]), as a type.
    trait Role {
        const LEAF: Leaf;
    }

    macro_rules! roles {
        ($( $(#[$doc:meta])* $name:ident => $leaf:expr; )+) => {$(
            $(#[$doc])*
            struct $name;

            impl Role for $name {
                const LEAF: Leaf = $leaf;
            }
        )+};
    }

    roles! {
        /// `id_Q` or `t`.
        TagLeaf => Leaf::Tag;
        /// `σ*`.
        ShowLeaf => Leaf::Show;
        /// `Ĉ`.
        RequestLeaf => Leaf::Request;
        /// `σ̂`.
        PreCredentialLeaf => Leaf::PreCredential;
        /// `π_id`.
        IdentifierProof => Leaf::Proof(ProofKind::Identifier);
        /// `π_att`.
        AttestationProof => Leaf::Proof(ProofKind::Attestation);
        /// `π_iss`.
        IssuanceProof => Leaf::Proof(ProofKind::Issuance);
        /// `π_prove`.
        PossessionProof => Leaf::Proof(ProofKind::Possession);
    }

    /// A leaf of a structured message: an opaque string through [`canonical`], refused before
    /// it is decoded if it is longer than the multibase text of the longest valid leaf of its
    /// role `R` ([`Backend::max_leaf_bytes`], [`super::max_multibase_len`]).
    struct Bounded<Bk, R, T>(T, core::marker::PhantomData<fn() -> (Bk, R)>);

    impl<'de, Bk: Backend, R: Role, T: ark_serialize::CanonicalDeserialize> Deserialize<'de>
        for Bounded<Bk, R, T>
    {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            use serde::de::Error as _;
            let text = String::deserialize(deserializer)?;
            let max = super::max_multibase_len(Bk::max_leaf_bytes(R::LEAF));
            if text.len() > max {
                return Err(D::Error::custom(format!(
                    "a {:?} leaf of {} characters, longer than the {max} of the longest valid one",
                    R::LEAF,
                    text.len()
                )));
            }
            let bytes = from_multibase(&text).map_err(D::Error::custom)?;
            let value = super::from_bytes(&bytes).map_err(D::Error::custom)?;
            Ok(Bounded(value, core::marker::PhantomData))
        }
    }

    /// A member of a structured message that is itself structured (the attestations of a
    /// credential request).
    struct Plain<T>(T);

    impl<'de, T: Deserialize<'de>> Deserialize<'de> for Plain<T> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            T::deserialize(deserializer).map(Plain)
        }
    }

    /// The decoder of a structured message: a map (never a sequence: the derived decoders of
    /// `serde` also accept a struct as the array of its members, a form that encoding never
    /// produces) with exactly the members that encoding writes, each once.
    macro_rules! structured {
        ($ty:ident<$bk:ident>, $expecting:literal, { $( $field:ident : $member:literal => $de:ty ),+ $(,)? }) => {
            impl<'de, $bk: Backend> Deserialize<'de> for $ty<$bk> {
                fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                    struct MapOnly<$bk>(core::marker::PhantomData<fn() -> $bk>);

                    impl<'de, $bk: Backend> serde::de::Visitor<'de> for MapOnly<$bk> {
                        type Value = $ty<$bk>;

                        fn expecting(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                            f.write_str($expecting)
                        }

                        fn visit_map<A: serde::de::MapAccess<'de>>(
                            self,
                            mut map: A,
                        ) -> Result<Self::Value, A::Error> {
                            use serde::de::Error as _;
                            const MEMBERS: &[&str] = &[$($member),+];
                            $( let mut $field: Option<$de> = None; )+
                            while let Some(key) = map.next_key::<String>()? {
                                match key.as_str() {
                                    $( $member => {
                                        if $field.is_some() {
                                            return Err(A::Error::duplicate_field($member));
                                        }
                                        $field = Some(map.next_value()?);
                                    } )+
                                    other => return Err(A::Error::unknown_field(other, MEMBERS)),
                                }
                            }
                            Ok($ty {
                                $( $field: $field.ok_or_else(|| A::Error::missing_field($member))?.0, )+
                            })
                        }
                    }

                    deserializer.deserialize_map(MapOnly(core::marker::PhantomData))
                }
            }
        };
    }

    structured!(AttestationRequest<Bk>, "an attestation request {\"id\", \"proof\"}", {
        id: "id" => Bounded<Bk, TagLeaf, Bk::Tag>,
        proof: "proof" => Bounded<Bk, IdentifierProof, Bk::Proof>,
    });
    structured!(Attestation<Bk>, "an attestation {\"tag\", \"show\", \"proof\"}", {
        tag: "tag" => Bounded<Bk, TagLeaf, Bk::Tag>,
        show: "show" => Bounded<Bk, ShowLeaf, Bk::Show>,
        proof: "proof" => Bounded<Bk, AttestationProof, Bk::Proof>,
    });
    structured!(CredentialRequest<Bk>, "a credential request {\"id\", \"attestations\", \"request\", \"proof\"}", {
        id: "id" => Bounded<Bk, TagLeaf, Bk::Tag>,
        attestations: "attestations" => Plain<Vec<Attestation<Bk>>>,
        request: "request" => Bounded<Bk, RequestLeaf, Bk::Request>,
        proof: "proof" => Bounded<Bk, IssuanceProof, Bk::Proof>,
    });
    structured!(MembershipProof<Bk>, "a membership proof {\"show\", \"proof\"}", {
        show: "show" => Bounded<Bk, ShowLeaf, Bk::Show>,
        proof: "proof" => Bounded<Bk, PossessionProof, Bk::Proof>,
    });

    /// The decoder of a reply: the strings `"fail"` and `"issued"`, or the one-member map
    /// `{"preCredential": "z…"}`, which is what encoding writes. Not the maps `{"fail": null}`
    /// and `{"issued": null}`, which the derived decoder of an enum accepts as well. A reply is
    /// a value of a self-describing format (JSON).
    impl<'de, Bk: Backend> Deserialize<'de> for Reply<Bk> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            struct OneForm<Bk>(core::marker::PhantomData<fn() -> Bk>);

            impl<'de, Bk: Backend> serde::de::Visitor<'de> for OneForm<Bk> {
                type Value = Reply<Bk>;

                fn expecting(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.write_str("\"fail\", \"issued\" or {\"preCredential\": …}")
                }

                fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Reply<Bk>, E> {
                    match value {
                        "fail" => Ok(Reply::Fail),
                        "issued" => Ok(Reply::Issued),
                        other => Err(E::unknown_variant(other, &["fail", "issued"])),
                    }
                }

                fn visit_map<A: serde::de::MapAccess<'de>>(
                    self,
                    mut map: A,
                ) -> Result<Reply<Bk>, A::Error> {
                    use serde::de::Error as _;
                    let Some(key) = map.next_key::<String>()? else {
                        return Err(A::Error::invalid_length(0, &self));
                    };
                    if key != "preCredential" {
                        return Err(A::Error::unknown_variant(&key, &["preCredential"]));
                    }
                    let pre = map
                        .next_value::<Bounded<Bk, PreCredentialLeaf, Bk::PreCredential>>()?
                        .0;
                    if map.next_key::<String>()?.is_some() {
                        return Err(A::Error::invalid_length(2, &self));
                    }
                    Ok(Reply::PreCredential(pre))
                }
            }

            deserializer.deserialize_any(OneForm(core::marker::PhantomData))
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn multibase_text_is_base58btc_only() {
            let text = to_multibase(&[1, 2, 3]);
            assert!(text.starts_with('z'));
            assert_eq!(from_multibase(&text).unwrap(), vec![1, 2, 3]);
            // the same bytes under another base are refused: one object, one text form
            let other = multibase::encode(multibase::Base::Base64Url, [1, 2, 3]);
            assert!(matches!(
                from_multibase(&other),
                Err(Error::Serialization(_))
            ));
            assert!(matches!(
                from_multibase("not multibase"),
                Err(Error::Serialization(_))
            ));
            assert!(matches!(from_multibase(""), Err(Error::Serialization(_))));
        }
    }
}
