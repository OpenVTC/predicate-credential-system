//! Random oracles and the hashing transcript (paper §2, "Notation").
//!
//! The protocol uses domain-separated random oracles `H_id`, `H_req` and `H_1` (§4.2, `Setup`),
//! and the instantiations hash to the group: `H_id` maps `⟨hvk⟩` to the identifier point `x_0`
//! of a helper key ([`crate::pcreds::Protocol::identifier_point`]), `H_req` maps
//! `⟨pp, hvk, id_Q, j_Q⟩` to the recipient point `x_Q`
//! ([`crate::pcreds::Protocol::recipient_point`]), `H_1` supplies Fiat-Shamir challenges, and
//! `H_2 = htag : Z_p → G_1 \ {1}` is the base of `Tag_DDH`. `H_id` and `H_req` are
//! [`Transcript`]s of the protocol under their own oracle suffixes (`/PCREDS-HID`,
//! `/PCREDS-HREQ`); the generators of `Σ-BBS` and of `Tag_DY` are hashed from the deployment
//! label ([`HashToGroup`]). `H_1` is the SHAKE128 duplex sponge of the IETF CFRG draft
//! `draft-irtf-cfrg-fiat-shamir-04` ([`duplex_sponge`]), which `DeriveChallenge` of
//! `draft-irtf-cfrg-sigma-protocols-04` drives ([`crate::sigma::fiat_shamir`]).
//!
//! Everything below the oracle *names* is an implementation choice of this crate, not something
//! the paper specifies:
//!
//! * **Framing.** A [`Transcript`] absorbs a sequence of `(label, data)` items, each encoded as
//!   `len(label) ‖ label ‖ len(data) ‖ data` with 8-byte little-endian lengths. The encoding of
//!   a sequence is uniquely decodable, hence injective: `("ab", "c")` and `("a", "bc")` hash
//!   differently.
//! * **Domain separation.** Every transcript oracle has the domain-separation tag
//!   [`DOMAIN_PREFIX`]` ‖ suffix` (`PCS-V1/H2`, `PCS-V1/PCREDS-HID`, `PCS-V1/PCREDS-HREQ`,
//!   `PCS-V1/PCREDS-BBS-GENERATORS`, `PCS-V1/DY-GENERATOR`, ...), which is never empty. For
//!   `H_2` and the generator derivations, the *deployment label* stored in the public
//!   parameters is bound as a framed item of the oracle input (not by concatenating it to the
//!   tag), so that no `(suffix, label)` pair can collide with another one. `H_id` and `H_req`
//!   absorb the digest of `pp`, which covers the label.
//! * **`H_1` is deployment-bound only through `ctx`.** The session identifier of a Fiat-Shamir
//!   proof is derived from a tag that names this crate, the version of the tag format, the draft
//!   revision, the flavor, the ciphersuite and the caller's context `ctx`, and from nothing else
//!   ([`crate::sigma::fiat_shamir::tag`]). The paper's `c = H_1(ctx, A)` has no further input,
//!   and its `ctx_j`, `ctx_0` begin with `pp`. Binding a proof to a deployment is therefore the
//!   job of whoever builds `ctx`, which must contain (a digest of) the public parameters. The
//!   protocol does so (every context of [`crate::pcreds`] starts with the digest of `pp`), and so
//!   does the stand-alone tag proof ([`crate::kiprf::prove_tag`] absorbs `pp_Tag`). A statement
//!   whose bases are the same in every deployment would otherwise replay across deployments.
//! * **Hash to field.** The transcript oracles derive scalars with arkworks'
//!   `DefaultFieldHasher<Sha256, 128>`:
//!   `expand_message_xmd` to `L = ⌈(⌈log p⌉ + 128)/8⌉` bytes, read as an integer and reduced mod
//!   `p`. If the `L` bytes are uniform the result is within statistical distance
//!   `p / 2^(8L+2) < 2^-128` of uniform (a uniform integer below `N` reduced mod `p` is at
//!   distance at most `p/4N`; this is the design rationale of RFC 9380 §5). Known caveat:
//!   arkworks pads the expander with `L` instead of 64 zero bytes when hashing to the scalar
//!   field, so the output is **not** RFC 9380 `hash_to_field` and does not interoperate with RFC
//!   hashers. It is used here only as a random oracle into `Z_p`.

pub mod bls12_381;
pub mod duplex_sponge;
#[cfg(any(test, feature = "test-utils"))]
pub mod testing;

use core::fmt::Debug;

use ark_ec::PrimeGroup;
use ark_ff::{
    BigInteger, PrimeField,
    field_hashers::{DefaultFieldHasher, HashToField},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use sha2::{Digest, Sha256};

use crate::{error::Error, serialization};

/// Crate-wide prefix of every domain-separation tag of a transcript oracle.
pub const DOMAIN_PREFIX: &[u8] = b"PCS-V1";
/// Oracle suffix of `H_2 = htag` (hash to group).
pub const H2_SUFFIX: &[u8] = b"/H2";

/// Security parameter of the hash-to-field expansion, in bits.
const SEC_PARAM: usize = 128;

/// The domain-separation tag `PCS-V1 ‖ suffix` of an oracle. Never empty.
#[must_use]
pub fn domain_separation_tag(oracle_suffix: &[u8]) -> Vec<u8> {
    [DOMAIN_PREFIX, oracle_suffix].concat()
}

/// `len(label) ‖ label ‖ len(data) ‖ data`, lengths as 8-byte little-endian integers.
fn frame(sink: &mut impl FnMut(&[u8]), label: &[u8], data: &[u8]) {
    // `usize` is at most 64 bits wide on every supported target, so the casts are lossless.
    sink(&(label.len() as u64).to_le_bytes());
    sink(label);
    sink(&(data.len() as u64).to_le_bytes());
    sink(data);
}

/// SHA-256-backed absorber with injective framing, the common core of `H_id`, `H_req` and of
/// the Fiat-Shamir contexts `ctx` of the protocol. (The Fiat-Shamir challenges themselves come
/// from the duplex sponge of [`duplex_sponge`].)
///
/// Cloning a transcript forks it: both copies continue from the same absorbed prefix.
#[derive(Clone, Debug)]
pub struct Transcript {
    dst: Vec<u8>,
    hasher: Sha256,
}

impl Transcript {
    /// A fresh transcript of the oracle `PCS-V1 ‖ oracle_suffix`. The tag is absorbed as the
    /// first item, so transcripts of different oracles never produce the same digest.
    #[must_use]
    pub fn new(oracle_suffix: &[u8]) -> Self {
        let dst = domain_separation_tag(oracle_suffix);
        let mut transcript = Self {
            dst: dst.clone(),
            hasher: Sha256::new(),
        };
        transcript.append_bytes(b"dst", &dst);
        transcript
    }

    /// Absorbs the item `(label, data)`.
    pub fn append_bytes(&mut self, label: &[u8], data: &[u8]) {
        let hasher = &mut self.hasher;
        frame(&mut |bytes| hasher.update(bytes), label, data);
    }

    /// Absorbs the item `(label, value)` with `value` as an 8-byte little-endian integer.
    pub fn append_u64(&mut self, label: &[u8], value: u64) {
        self.append_bytes(label, &value.to_le_bytes());
    }

    /// Absorbs the item `(label, value)` with `value` in its **compressed** canonical encoding
    /// (the same bytes as [`serialization::to_bytes`]), which covers `G_1`, `G_2`, `G_T` and `Z_p`
    /// elements, and every public protocol object, uniformly.
    ///
    /// # Errors
    /// [`Error::Serialization`] if the serializer of `value` fails; nothing is absorbed then.
    pub fn append_serializable<T: CanonicalSerialize + ?Sized>(
        &mut self,
        label: &[u8],
        value: &T,
    ) -> Result<(), Error> {
        let bytes = serialization::to_bytes(value)?;
        self.append_bytes(label, &bytes);
        Ok(())
    }

    /// SHA-256 digest of everything absorbed so far. The transcript can be extended afterwards.
    #[must_use]
    pub fn digest(&self) -> [u8; 32] {
        self.hasher.clone().finalize().into()
    }

    /// The oracle output in `F`: `hash_to_field(DST, digest)` with the transcript's
    /// domain-separation tag (see the module docs for the exact hash-to-field variant).
    #[must_use]
    pub fn challenge_scalar<F: PrimeField>(&self) -> F {
        let hasher = <DefaultFieldHasher<Sha256, SEC_PARAM> as HashToField<F>>::new(&self.dst);
        let [scalar] = hasher.hash_to_field::<1>(&self.digest());
        scalar
    }
}

// ---------------------------------------------------------------------------------------------
// H_2: hash to group
// ---------------------------------------------------------------------------------------------

/// The canonical fixed-length little-endian encoding of a scalar (identical to its compressed
/// canonical serialization, but infallible).
#[must_use]
pub fn scalar_bytes<F: PrimeField>(scalar: &F) -> Vec<u8> {
    scalar.into_bigint().to_bytes_le()
}

/// The injectively framed input `(deployment, counter, msg)` of a hash-to-group oracle.
/// `counter` is `0` except in the negligible case that an output had to be re-hashed.
#[must_use]
pub fn oracle_input(domain: &[u8], counter: u64, msg: &[u8]) -> Vec<u8> {
    let mut input = Vec::with_capacity(domain.len() + msg.len() + 64);
    let mut sink = |bytes: &[u8]| input.extend_from_slice(bytes);
    frame(&mut sink, b"deployment", domain);
    frame(&mut sink, b"counter", &counter.to_le_bytes());
    frame(&mut sink, b"msg", msg);
    input
}

/// A random oracle into a prime-order group `G` that **never outputs the identity**; models
/// `htag : Z_p → G_1 \ {1}` (§3.1.1) and derives independent generators for the credential
/// bases.
///
/// An instance is bound to a deployment label and is part of the public parameters, hence the
/// serialization bounds. The oracle with suffix `dst_suffix` has the domain-separation tag
/// `PCS-V1 ‖ dst_suffix`; oracles with different suffixes, or different deployment labels, are
/// independent. Generic code takes `H: HashToGroup<E::G1>` as a type parameter because
/// arkworks ships hash-to-curve suites only for BLS12-381 and BLS12-377.
pub trait HashToGroup<G: PrimeGroup>:
    Clone + Debug + PartialEq + Eq + CanonicalSerialize + CanonicalDeserialize + Send + Sync
{
    /// The oracle family of the deployment `domain`.
    ///
    /// # Errors
    /// [`Error::HashToCurve`] if the underlying hash-to-curve suite cannot be instantiated.
    fn new(domain: &[u8]) -> Result<Self, Error>;

    /// The deployment label this instance is bound to.
    fn domain(&self) -> &[u8];

    /// `H_{dst_suffix}(msg) ∈ G \ {1}`. Deterministic. An identity output is re-hashed with an
    /// incremented counter, so the identity is never returned.
    fn hash(&self, dst_suffix: &[u8], msg: &[u8]) -> G;

    /// `htag(s)` for a scalar `s`, hashed in its canonical encoding ([`scalar_bytes`]).
    fn hash_scalar(&self, dst_suffix: &[u8], scalar: &G::ScalarField) -> G {
        self.hash(dst_suffix, &scalar_bytes(scalar))
    }

    /// `n` generators `H_{dst_suffix}(0), …, H_{dst_suffix}(n-1)` with mutually unknown discrete
    /// logarithms (in the random-oracle model), e.g. `h_0, …, h_3` of `Σ-BBS` or `g, h` of
    /// `Σ-MAC`.
    fn generators(&self, dst_suffix: &[u8], n: usize) -> Vec<G> {
        (0..n as u64)
            .map(|i| self.hash(dst_suffix, &i.to_le_bytes()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ec::PrimeGroup;
    use ark_ff::Zero;

    use super::*;
    use crate::serialization::WireFormat;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn framing_is_injective() {
        // ("ab", "c") vs ("a", "bc"): the concatenations coincide, the framed items do not.
        let mut t1 = Transcript::new(b"/TEST");
        t1.append_bytes(b"ab", b"c");
        let mut t2 = Transcript::new(b"/TEST");
        t2.append_bytes(b"a", b"bc");
        assert_ne!(t1.digest(), t2.digest());

        // one item vs the same bytes split over two items
        let mut t3 = Transcript::new(b"/TEST");
        t3.append_bytes(b"x", b"abcd");
        let mut t4 = Transcript::new(b"/TEST");
        t4.append_bytes(b"x", b"ab");
        t4.append_bytes(b"x", b"cd");
        assert_ne!(t3.digest(), t4.digest());

        // an empty item is not a no-op
        let mut t5 = Transcript::new(b"/TEST");
        t5.append_bytes(b"", b"");
        assert_ne!(t5.digest(), Transcript::new(b"/TEST").digest());

        // data moved into the label
        let mut t6 = Transcript::new(b"/TEST");
        t6.append_bytes(b"xabcd", b"");
        assert_ne!(t3.digest(), t6.digest());
    }

    #[test]
    fn framing_bytes_are_as_documented() {
        let mut out = Vec::new();
        frame(&mut |b| out.extend_from_slice(b), b"ab", b"c");
        let mut expected = Vec::new();
        expected.extend_from_slice(&2u64.to_le_bytes());
        expected.extend_from_slice(b"ab");
        expected.extend_from_slice(&1u64.to_le_bytes());
        expected.extend_from_slice(b"c");
        assert_eq!(out, expected);
    }

    /// The oracle suffix of the known answers below. It named the SHA-256 `H_1` of earlier
    /// versions. The transcript framing it pins is the one of `H_id`, `H_req` and the contexts.
    const KAT_SUFFIX: &[u8] = b"/H1";

    #[test]
    fn transcript_is_deterministic_and_forkable() {
        let build = || {
            let mut t = Transcript::new(KAT_SUFFIX);
            t.append_bytes(b"a", b"1");
            t.append_u64(b"n", 7);
            t.append_serializable(b"p", &G1Projective::generator())
                .unwrap();
            t
        };
        assert_eq!(build().digest(), build().digest());
        assert_eq!(
            build().challenge_scalar::<Fr>(),
            build().challenge_scalar::<Fr>()
        );

        let base = build();
        let mut fork = base.clone();
        fork.append_bytes(b"more", b"data");
        assert_ne!(base.digest(), fork.digest());
        assert_eq!(base.digest(), build().digest());
    }

    #[test]
    fn append_serializable_uses_the_compressed_encoding() {
        let p = G1Projective::generator();
        let mut t1 = Transcript::new(b"/TEST");
        t1.append_serializable(b"p", &p).unwrap();
        let mut t2 = Transcript::new(b"/TEST");
        let bytes = p.to_bytes().unwrap();
        assert_eq!(bytes.len(), 48);
        t2.append_bytes(b"p", &bytes);
        assert_eq!(t1.digest(), t2.digest());
    }

    #[test]
    fn oracles_are_domain_separated() {
        // same items, different oracle
        let mut t0 = Transcript::new(b"/PCREDS-HID");
        let mut t1 = Transcript::new(b"/PCREDS-HREQ");
        t0.append_bytes(b"x", b"y");
        t1.append_bytes(b"x", b"y");
        assert_ne!(t0.digest(), t1.digest());
        assert_ne!(t0.challenge_scalar::<Fr>(), t1.challenge_scalar::<Fr>());
        // the same bytes as one item under two oracles
        let mut other = Transcript::new(KAT_SUFFIX);
        other.append_bytes(b"ctx", b"identity");
        let mut hid = Transcript::new(b"/PCREDS-HID");
        hid.append_bytes(b"ctx", b"identity");
        assert_ne!(hid.challenge_scalar::<Fr>(), other.challenge_scalar::<Fr>());
    }

    #[test]
    fn scalar_bytes_equal_the_canonical_serialization() {
        for s in [
            Fr::zero(),
            Fr::from(1u64),
            -Fr::from(1u64),
            Fr::from(u64::MAX),
        ] {
            assert_eq!(scalar_bytes(&s), s.to_bytes().unwrap());
        }
    }

    #[test]
    fn oracle_input_is_injective_in_its_parts() {
        assert_ne!(oracle_input(b"ab", 0, b"c"), oracle_input(b"a", 0, b"bc"));
        assert_ne!(oracle_input(b"d", 0, b"m"), oracle_input(b"d", 1, b"m"));
    }

    /// Known-answer regression vectors: any change of the framing, the domain-separation tags or
    /// the hash-to-field variant shows up here. The expected values were computed by an
    /// independent Python re-implementation of the documented framing and of arkworks'
    /// `expand_message_xmd` variant (SHA-256, `Z_pad` of `L = 48` bytes, big-endian reduction
    /// mod `p`), so they also cross-check this module. They are NOT vectors of an external
    /// specification.
    #[test]
    fn known_answers() {
        let mut t = Transcript::new(KAT_SUFFIX);
        t.append_bytes(b"label", b"data");
        t.append_u64(b"n", 5);
        assert_eq!(
            hex(&t.digest()),
            "cbdf0ce8df056c28618f0c1171a1f238817cb5c0506813b71194b5c8057a052a"
        );
        assert_eq!(
            hex(&t.challenge_scalar::<Fr>().to_bytes().unwrap()),
            "667dd8b9896694540758017abb3e76ec1fa260468ce051d64d9182013dbf5a1c"
        );
    }
}
