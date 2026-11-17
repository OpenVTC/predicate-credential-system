//! `Tag_DY`, the Dodis-Yampolskiy tag (paper §6.1.2, "The Dodis-Yampolskiy instantiation").
//!
//! | paper (box `Tag_DY`) | here |
//! |---|---|
//! | key space `Z_p`, domain `Z_p`, range `T = G_1 \ {1}`; defined only when `K + x ≠ 0` | [`KIPRF::Key`], [`KIPRF::Input`] `= Z_p`, [`KIPRF::Output`] `= G` |
//! | a generator `g_1` "sampled uniformly from `G_1 \ {1}` when the public parameters are generated, independently of all keys" | [`ProtocolTag::setup`]: `g_1` hashed from the deployment label ([`DY::derive`]) |
//! | `TagKeyGen`: `K ← Z_p` (zero IS a key) | [`KIPRF::keygen`] |
//! | `TagEval(K, x)`: if `K + x = 0` return `⊥`; return `g_1^{1/(K+x)}` | [`KIPRF::eval`]: `None` iff `K + x = 0`, else `g · (K+x)^{-1}` |
//! | `t ∈ T`, i.e. `t ≠ 1` | [`SigmaFriendlyKIPRF::valid_tag`] |
//! | `R_Tag`: `t^K = g_1 t^{-x}`, the Schnorr relation with base `t`, target `g_1 t^{-x}`, witness `K` | [`SigmaFriendlyKIPRF::tag_equations`]: ONE equation `g − x·t = K·t`, with the image terms `(g, 1)`, `(t, −x)` |
//!
//! The paper states the instantiation over `G_1`; the code is generic over a prime-order group
//! `G` (additive notation, `g = g_1`). The type parameter `H` is the hash-to-group oracle that
//! derives `g_1` from the deployment label; evaluation never hashes, so every `PrimeGroup` of
//! arkworks works for evaluation.
//!
//! Security (Lemma on `Tag_DY`, §6.1.2): key uniqueness is unconditional, and under the
//! `q`-DDHI assumption in `G_1` the function is weakly pseudorandom on uniform points. Key
//! uniqueness needs no assumption: wherever both evaluations are defined,
//! `g_1^{1/(K+x)} = g_1^{1/(K'+x)}` forces `1/(K+x) = 1/(K'+x)` because `g_1` has order `p`,
//! hence `K = K'`. The reduction for weak pseudorandomness chooses the tag generator itself
//! (`h = ĝ^{f(α)}`, computed from the `q`-DDHI instance), which is why `g_1` is a parameter
//! sampled at setup and not the fixed generator of the group: here it is the output of a random
//! oracle on the deployment label, which a reduction in the random-oracle model programs.
//!
//! # In formulas
//!
//! ```math
//! \mathsf{Tag}_{\mathsf{DY}}(K, x) = g_1^{1/(K+x)} \quad \text{if } K + x \neq 0, \qquad \mathsf{Tag}_{\mathsf{DY}}(K, -K) = \bot
//! ```
//!
//! ```math
//! R_{\mathsf{Tag}} = \bigl\{\, \bigl((t, x),\ K\bigr) \;:\; t \in \mathcal T \wedge t^{K} = g_1\, t^{-x} \,\bigr\}, \qquad \mathcal T = \mathbb G \setminus \{1\}
//! ```
//!
//! # The clause
//!
//! The base of the clause is the instance-dependent tag `t` itself, not a fixed generator.
//! `K·t = g − x·t` is the same as `(K+x)·t = g`. Because `g ≠ 1`, a solution has `K + x ≠ 0` and
//! `t = g^{1/(K+x)}`, and conversely; this is the "Equivalently" of the Lemma's paragraph on
//! proof friendliness. Consequences:
//!
//! * every `t ≠ 1` is the tag of exactly ONE key at the point `x` (`t` has order `p`), and
//! * for `t = 1` the clause reads `1 = g_1` and has no witness at all. Unlike for `Tag_DDH`
//!   (where `t = 1` has the non-key witness `K = 0`), `t ∈ T` is not what keeps the identity out
//!   of `R_Tag` here; it is still the public pre-check of the tag relation and is evaluated as
//!   such.
//!
//! # Undefined evaluations
//!
//! `Tag(K, x) = ⊥` exactly at the one point `x = −K`; [`KIPRF::eval`] reports it as `None` and
//! does nothing else about it. In the protocol ("Undefined evaluations under honest keys are
//! covered by Claim Sampling", §5.1.2):
//!
//! * `Register` fails for `usk = −x_0` ("If `id_P = ⊥`, return `(RegisterFailed, ⊥)`"), with
//!   probability `1/p`; it draws no new key;
//! * an attestation aborts when the attester's key is `usk_P = −x_Q` for the recipient point
//!   `x_Q` of the requester, which no key-generation condition can preclude.
//!
//! Both are the caller's job. The unit tests of this module run `Register` against its undefined
//! point and show the attestation case.
//!
//! # Implementation notes
//!
//! None of the following is a claim of the paper.
//!
//! * **Degenerate parameters.** `pp_Tag` is the generator `g_1`, and the element decoders of
//!   arkworks accept the identity (see [`crate::serialization`]). With `g_1 = 1` every "tag"
//!   would be `1`, and the clause `(K+x)·t = 1` would be satisfied by the public value `K = −x`
//!   for EVERY `t`: `R_Tag` would be vacuous. There are three lines of defence.
//!
//!   1. `DY` has hand-written `Valid` and `CanonicalDeserialize` impls, and VALIDATED
//!      decoding rejects the identity in the place of `g_1`: directly, inside a structure that
//!      derives its decoder, and inside a `Vec`. The decoder of this crate,
//!      [`crate::serialization::from_bytes`], is validated. The reason is liveness, not soundness:
//!      `TagEval` is `⊥` everywhere under a degenerate instance, so every `Register` fails
//!      (`RegisterFailed`), and a caller that retries on `⊥` would spin forever, for a user who
//!      decoded its parameters from an attacker. This does not contradict the convention of [`crate::serialization`]
//!      (non-degeneracy is a check of the verifier, "never a property of decoding"): that
//!      convention is about the values of a statement (`t ≠ 1`, ...), whose checks stay in the
//!      verifiers, while the identity is not a generator and hence no `pp_Tag` at all.
//!   2. Decoding WITHOUT validation (`deserialize_*_unchecked`) checks nothing, here as
//!      everywhere in arkworks. For an instance obtained that way [`DY::is_well_formed`]
//!      tells, and generic code, which cannot see an inherent method, asks the same question
//!      through the hook [`ProtocolTag::is_well_formed`], which
//!      [`Protocol::setup`](crate::pcreds::Protocol::setup) and
//!      [`Protocol::from_public_parameters`](crate::pcreds::Protocol::from_public_parameters)
//!      evaluate before any user registers.
//!   3. Whatever the caller checked, [`SigmaFriendlyKIPRF::valid_tag`] rejects every tag of a
//!      degenerate instance (verifiers are safe in any case) and [`KIPRF::eval`] is `None`
//!      everywhere.
//!
//!   Instances built by [`DY::new`], [`DY::with_generator`], [`DY::derive`] and
//!   [`ProtocolTag::setup`] are well formed. Any OTHER generator in a decoded instance is
//!   harmless: it defines another function, and proofs do not transfer between the two.
//! * **The generator of a deployment.** [`ProtocolTag::setup`] derives `g_1` from the deployment
//!   label with the oracle `H` under its own suffix, so two deployments have independent
//!   generators, and [`Protocol::from_public_parameters`](crate::pcreds::Protocol::from_public_parameters)
//!   accepts a received `pp_Tag` only if it is the derived one. [`DY::new`] (the standard
//!   generator of `G`) remains for stand-alone use of the tag.
//! * **Secrets.** The key is a bare scalar (the traits fix `Key = Z_p`); the caller owns and
//!   wipes it. The temporaries `K + x` and `1/(K+x)` of `TagEval` are `Copy` values that are
//!   not wiped; see the limitations in the crate docs.
//!
//! # Example
//!
//! ```
//! use ark_bls12_381::{Fr, G1Projective as G1};
//! use predicate_credential_system::{
//!     hash::{bls12_381::G1Hasher, Transcript},
//!     kiprf::{prove_tag, verify_tag, KIPRF, ProtocolTag, DY},
//! };
//! use rand::{rngs::StdRng, SeedableRng};
//!
//! let mut rng = StdRng::seed_from_u64(1);
//! let label = b"example deployment";
//! // pp_Tag: the generator g_1 of this deployment
//! let tag = DY::<G1, G1Hasher>::setup(label)?;
//!
//! // a user: usk, and the identifier id = Tag(usk, x_0) = g_1^{1/(usk + x_0)} at an identifier
//! // point x_0 (the protocol derives x_0 = H_id(⟨hvk⟩) from the helper key)
//! let x0: Fr = Transcript::new(b"/EXAMPLE-POINT").challenge_scalar();
//! let usk = tag.keygen(&mut rng);
//! let id = tag.eval(&usk, &x0).expect("⊥ only for usk = −x_0: RegisterFailed");
//! assert_eq!(id * (usk + x0), *tag.generator());
//! // the ONE point outside the domain of this key
//! assert_eq!(tag.eval(&usk, &-usk), None);
//!
//! // a proof of knowledge of the key behind the identifier (the π_id of the protocol)
//! let proof = prove_tag(&tag, &usk, &id, &x0, b"context", &mut rng)?;
//! assert!(verify_tag(&tag, &id, &x0, b"context", &proof));
//! assert!(!verify_tag(&tag, &id, &(x0 + Fr::from(1u64)), b"context", &proof));
//! # Ok::<(), predicate_credential_system::Error>(())
//! ```

use core::{fmt, marker::PhantomData};

use ark_ec::PrimeGroup;
use ark_ff::{Field, UniformRand};
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::rand::{CryptoRng, RngCore};

use super::{KIPRF, ProtocolTag, SigmaFriendlyKIPRF};
use crate::{
    error::Error,
    hash::HashToGroup,
    sigma::{LinearEquation, ScalarVar},
};

/// Oracle suffix under which [`DY::derive`] hashes the deployment label to the generator `g_1`.
pub const GENERATOR_SUFFIX: &[u8] = b"/DY-GENERATOR";

/// The public parameters `pp_Tag` of `Tag_DY` over the group `G`: the generator `g_1`, and the
/// type `H` of the oracle that derives it from a deployment label.
///
/// An instance is part of the public parameters of the protocol, hence the serialization impls.
/// Two instances are equal iff they define the same function. The encoding is the one of `g_1`.
/// Decoding is written by hand (not derived) because VALIDATED decoding rejects the identity in
/// the place of `g_1`; only an instance that was decoded without validation can be degenerate,
/// see [`Self::is_well_formed`] and the module docs ("Degenerate parameters").
pub struct DY<G: PrimeGroup, H> {
    /// The generator `g_1` whose roots are the tags.
    g: G,
    _hasher: PhantomData<fn() -> H>,
}

// Written by hand: a derive would bound the marker type `H`.
impl<G: PrimeGroup, H> Clone for DY<G, H> {
    fn clone(&self) -> Self {
        Self {
            g: self.g,
            _hasher: PhantomData,
        }
    }
}

impl<G: PrimeGroup, H> fmt::Debug for DY<G, H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DY").field("g", &self.g).finish()
    }
}

impl<G: PrimeGroup, H> PartialEq for DY<G, H> {
    fn eq(&self, other: &Self) -> bool {
        self.g == other.g
    }
}

impl<G: PrimeGroup, H> Eq for DY<G, H> {}

impl<G: PrimeGroup, H> DY<G, H> {
    /// `Tag_DY` over the standard generator of `G`, for stand-alone use of the tag. The
    /// protocol derives the generator of a deployment instead ([`ProtocolTag::setup`]).
    #[must_use]
    pub fn new() -> Self {
        Self {
            g: G::generator(),
            _hasher: PhantomData,
        }
    }

    /// `Tag_DY` over the generator `g`.
    ///
    /// # Errors
    /// [`Error::DegenerateInput`] if `g` is the identity, which generates nothing.
    pub fn with_generator(g: G) -> Result<Self, Error> {
        if g.is_zero() {
            return Err(Error::DegenerateInput("g_1 of Tag_DY"));
        }
        Ok(Self {
            g,
            _hasher: PhantomData,
        })
    }

    /// The generator `g_1`.
    #[must_use]
    pub fn generator(&self) -> &G {
        &self.g
    }

    /// Whether `g_1 ≠ 1`, i.e. whether `g_1` generates `G` (the order of `G` is prime). Costs
    /// no group operation; never panics.
    ///
    /// Implementation note, not an algorithm of the paper (module docs, "Degenerate
    /// parameters"). `false` only for an instance that was decoded from an encoding of the
    /// identity WITHOUT validation (`deserialize_*_unchecked`, `Validate::No`); validated
    /// decoding and the constructors never produce one. Under such an instance every
    /// evaluation is `⊥` and every tag is inadmissible; whoever decodes `pp_Tag` without
    /// validation checks this BEFORE running a key-generation loop that restarts on `⊥`.
    /// Generic code reaches the same check as [`ProtocolTag::is_well_formed`].
    #[must_use]
    pub fn is_well_formed(&self) -> bool {
        !self.g.is_zero()
    }

    /// `Err` for the identity in the place of `g_1`.
    fn check_generator(&self) -> Result<(), SerializationError> {
        if self.is_well_formed() {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl<G: PrimeGroup, H: HashToGroup<G>> DY<G, H> {
    /// `pp_Tag` of the deployment `label`: `g_1 := H(label)` under [`GENERATOR_SUFFIX`], the
    /// "uniform" generator of §6.1.2 in the random-oracle model. Deterministic; never the
    /// identity (the contract of [`HashToGroup::hash`]).
    ///
    /// # Errors
    /// [`Error::HashToCurve`] if the oracle cannot be instantiated.
    pub fn derive(label: &[u8]) -> Result<Self, Error> {
        let g = H::new(label)?.hash(GENERATOR_SUFFIX, &[]);
        Self::with_generator(g)
    }
}

impl<G: PrimeGroup, H> Default for DY<G, H> {
    fn default() -> Self {
        Self::new()
    }
}

// The impls below replace the derives and accept exactly what the derived ones would, MINUS the
// identity in the place of `g_1` (module docs, "Degenerate parameters"). arkworks validates on
// two paths, and both are covered:
//
// * `deserialize_with_mode(.., Validate::Yes)`: the direct path, and the path of every structure
//   with a derived decoder, which passes its own mode on to its fields and runs no check
//   afterwards;
// * `Valid::check`: the path of `Vec<T>` and the other length-prefixed collections, which decode
//   their items with `Validate::No` and then run `T::batch_check` (by default `check` on every
//   item).

impl<G: PrimeGroup, H> CanonicalSerialize for DY<G, H> {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.g.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.g.serialized_size(compress)
    }
}

/// Validity of a decoded `pp_Tag`: `g_1` is a valid element of `G` (the element's own check)
/// and is not the identity. Implementation note (module docs, "Degenerate parameters").
impl<G: PrimeGroup, H> Valid for DY<G, H> {
    fn check(&self) -> Result<(), SerializationError> {
        self.g.check()?;
        self.check_generator()
    }
}

/// Decodes `g_1`, with the mode passed on to the element decoder. With [`Validate::Yes`] (in
/// particular through [`crate::serialization::from_bytes`]) the identity is rejected with
/// [`SerializationError::InvalidData`]; with [`Validate::No`] the instance is not checked, which
/// is the contract of the `*_unchecked` decoders of arkworks. Adds no panic to the element
/// decoder. Implementation note (module docs, "Degenerate parameters").
impl<G: PrimeGroup, H> CanonicalDeserialize for DY<G, H> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let tag = Self {
            g: G::deserialize_with_mode(reader, compress, validate)?,
            _hasher: PhantomData,
        };
        if validate == Validate::Yes {
            tag.check_generator()?;
        }
        Ok(tag)
    }
}

impl<G: PrimeGroup, H> KIPRF for DY<G, H> {
    type Key = G::ScalarField;
    type Input = G::ScalarField;
    type Output = G;

    /// `TagKeyGen` (box `Tag_DY`): step 1, `K ← Z_p`; step 2, return `K`.
    ///
    /// The key space is all of `Z_p`, zero included (unlike `Tag_DDH`). Whether the evaluations
    /// a protocol needs are defined under `K` is for that protocol to check (`Register`).
    fn keygen<R: RngCore + CryptoRng + ?Sized>(&self, rng: &mut R) -> Self::Key {
        G::ScalarField::rand(rng)
    }

    /// `TagEval(K, x)` (box `Tag_DY`): step 1, if `K + x = 0` return `⊥`; step 2, return
    /// `g_1^{1/(K+x)}`.
    ///
    /// For a well-formed instance the result is `None` exactly at `x = −K`, and never the
    /// identity (`1/(K+x) ≠ 0` and `g_1` has order `p`). Never panics: the inversion is
    /// `Field::inverse`, which is `None` exactly at zero (field DIVISION by zero would panic).
    ///
    /// Implementation note: `None` at every point for a degenerate instance (`g_1 = 1`, which
    /// only unvalidated decoding produces), whose "tag" would be the identity, outside the range
    /// `G_1 \ {1}` (module docs, "Degenerate parameters").
    fn eval(&self, key: &Self::Key, input: &Self::Input) -> Option<Self::Output> {
        if !self.is_well_formed() {
            return None;
        }
        // 1. if K + x = 0 return ⊥
        let exponent = (*key + *input).inverse()?;
        // 2. return g_1^{1/(K+x)}
        Some(self.g * exponent)
    }
}

impl<G: PrimeGroup, H> SigmaFriendlyKIPRF for DY<G, H> {
    type Group = G;

    /// `t ∈ T = G_1 \ {1}` (§6.1.2); independent of `x`. Every `t ≠ 1` is the tag of exactly
    /// one key at every point, and no defined tag is `1`.
    ///
    /// Implementation note: `false` for EVERY tag of a degenerate instance (`g_1 = 1`, which
    /// only unvalidated decoding produces), under which the clause `t^K = g_1 t^{-x}` is
    /// satisfied by the public value `K = −x` whatever `t` is (module docs, "Degenerate
    /// parameters"). The verifier's protection does not rest on how the instance was decoded.
    fn valid_tag(&self, tag: &G, _input: &G::ScalarField) -> bool {
        self.is_well_formed() && !tag.is_zero()
    }

    /// `R_Tag_DY` as ONE linear equation (Lemma on `Tag_DY`, "Proof friendliness"):
    /// `t^K = g_1 t^{-x}`, the Schnorr relation with base `t`, target `g_1 t^{-x}` and
    /// witness `K`.
    ///
    /// The target is written as the two image terms `(g_1, 1)` and `(t, −x)`, not as the single
    /// element `g_1 − x·t`, so that `g_1`, `t` and `x` are each in the instance that the
    /// Fiat-Shamir challenge absorbs (`draft-irtf-cfrg-sigma-protocols-04`, §3.2).
    ///
    /// The base is the instance-dependent tag itself. For `t = 1` the equation reads `1 = g_1`
    /// and no scalar satisfies it. For `t ≠ 1` exactly one does, and it has `K + x ≠ 0`.
    fn tag_equations(
        &self,
        key: ScalarVar,
        tag: &G,
        input: &G::ScalarField,
    ) -> Vec<LinearEquation<G>> {
        let one = G::ScalarField::ONE;
        vec![LinearEquation {
            image: vec![(self.g, one), (*tag, -*input)],
            terms: vec![(key, *tag, one)],
        }]
    }
}

impl<G: PrimeGroup, H: HashToGroup<G>> ProtocolTag<G> for DY<G, H> {
    const NAME: &'static str = "DY";

    /// `pp_Tag` of the deployment `label`: the generator [`DY::derive`] hashes from it.
    fn setup(label: &[u8]) -> Result<Self, Error> {
        Self::derive(label)
    }

    /// [`DY::is_well_formed`]: `g_1 ≠ 1`. Under a well-formed instance `TagEval(K, x)` is `⊥`
    /// for the ONE key `K = −x` only, which is what the contract of the hook asks for.
    fn is_well_formed(&self) -> bool {
        // The inherent method (inherent associated functions take precedence in a path).
        DY::is_well_formed(self)
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ff::{BigInteger, One, PrimeField, Zero};
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        hash::{Transcript, bls12_381::G1Hasher, testing::InsecureExponentHasher},
        kiprf::{prove_tag, tag_proof_context, tag_relation, verify_tag},
        serialization::WireFormat,
        sigma::{FSProof, LinearRelation, fiat_shamir},
    };

    type G1 = G1Projective;
    type Tag = DY<G1, G1Hasher>;

    const DOMAIN: &[u8] = b"tag-dy-unit-tests";

    /// The standard-generator instance (the algebraic tests compare with `g_1 = G1::generator()`)
    /// and the identifier point `x_0` of the test deployment.
    fn setup() -> (Tag, Fr) {
        (Tag::new(), point(DOMAIN))
    }

    /// A fixed point of the test deployment `domain`, standing for an identifier point.
    fn point<F: PrimeField>(domain: &[u8]) -> F {
        let mut transcript = Transcript::new(b"/TEST-POINT");
        transcript.append_bytes(b"deployment", domain);
        transcript.challenge_scalar()
    }

    /// A degenerate instance (`g_1 = 1`). The only way to one is decoding WITHOUT validation;
    /// validated decoding rejects the encoding (see
    /// `validated_decoding_rejects_the_identity_generator`).
    fn degenerate() -> Tag {
        let bytes = G1::zero().to_bytes().unwrap();
        let tag = Tag::deserialize_compressed_unchecked(&bytes[..]).unwrap();
        assert!(tag.generator().is_zero());
        tag
    }

    /// Yields `0` for the first `zeros` calls of `next_u64`, then the output of a seeded
    /// `StdRng`. `F::rand` reads one `u64` per limb, so four zeros make `TagKeyGen` return the
    /// key `0` over a 4-limb field (the same device as in `crate::sample`).
    struct ZerosThen {
        zeros: usize,
        then: StdRng,
    }

    impl ZerosThen {
        fn new(zeros: usize, seed: u64) -> Self {
            Self {
                zeros,
                then: StdRng::seed_from_u64(seed),
            }
        }
    }

    impl RngCore for ZerosThen {
        fn next_u32(&mut self) -> u32 {
            self.next_u64() as u32
        }

        fn next_u64(&mut self) -> u64 {
            if self.zeros > 0 {
                self.zeros -= 1;
                0
            } else {
                self.then.next_u64()
            }
        }

        fn fill_bytes(&mut self, dest: &mut [u8]) {
            for chunk in dest.chunks_mut(8) {
                let bytes = self.next_u64().to_le_bytes();
                chunk.copy_from_slice(&bytes[..chunk.len()]);
            }
        }

        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), ark_std::rand::Error> {
            self.fill_bytes(dest);
            Ok(())
        }
    }

    // Test-only marker: `TagKeyGen` asks for a `CryptoRng`.
    impl CryptoRng for ZerosThen {}

    // ----- TagKeyGen, TagEval ---------------------------------------------------------------------

    #[test]
    fn evaluation_is_deterministic_and_is_the_inverse_exponent() {
        let mut rng = StdRng::seed_from_u64(0xd701);
        let (tag, _) = setup();
        let (key, s) = (tag.keygen(&mut rng), Fr::rand(&mut rng));
        let t = tag.eval(&key, &s).unwrap();
        assert_eq!(tag.eval(&key, &s).unwrap(), t);
        // an independently constructed instance is the same function
        let (again, _) = setup();
        assert_eq!(again, tag);
        assert_eq!(again.eval(&key, &s).unwrap(), t);
        // it is g_1^{1/(K+s)}: (K+s)·T = g_1, and the exponent is the inverse of K + s, here
        // computed another way (Fermat: x^{p−2})
        assert_eq!(t * (key + s), G1::generator());
        let mut p_minus_2 = Fr::MODULUS;
        assert!(!p_minus_2.sub_with_borrow(&2u64.into()));
        assert_eq!(t, G1::generator() * (key + s).pow(p_minus_2));
        // only K + s matters ...
        assert_eq!(tag.eval(&(key + Fr::one()), &(s - Fr::one())).unwrap(), t);
        // ... so another point, or another key, gives another tag
        assert_ne!(tag.eval(&key, &(s + Fr::one())).unwrap(), t);
        assert_ne!(tag.eval(&(key + Fr::one()), &s).unwrap(), t);
        // K + s = 1: the tag is the generator itself
        assert_eq!(tag.eval(&key, &(Fr::one() - key)).unwrap(), G1::generator());
    }

    /// The key-dependent domain `X_K = Z_p \ {−K}`: `⊥` at `s = −K` and nowhere else.
    #[test]
    fn evaluation_is_undefined_exactly_at_minus_the_key() {
        let mut rng = StdRng::seed_from_u64(0xd702);
        let (tag, x0) = setup();
        let mut keys: Vec<Fr> = (0..8).map(|_| tag.keygen(&mut rng)).collect();
        // edge keys: zero IS a key; the key whose undefined point is x_0
        keys.extend([Fr::zero(), Fr::one(), -Fr::one(), -x0]);
        for key in &keys {
            assert_eq!(tag.eval(key, &-*key), None);
            // a window of points around −K, and points far away from it
            for d in 1u64..=8 {
                for s in [-*key + Fr::from(d), -*key - Fr::from(d)] {
                    let t = tag.eval(key, &s).expect("K + s ≠ 0");
                    assert!(!t.is_zero());
                    assert_eq!(t * (*key + s), G1::generator());
                }
            }
            for _ in 0..4 {
                let s = Fr::rand(&mut rng);
                assert_ne!(s, -*key);
                assert!(tag.eval(key, &s).is_some());
            }
        }
        // K = 0: undefined at s = 0 only, and Tag(0, s) = g_1^{1/s}
        assert_eq!(tag.eval(&Fr::zero(), &Fr::zero()), None);
        let s = Fr::rand(&mut rng);
        assert_eq!(
            tag.eval(&Fr::zero(), &s).unwrap(),
            G1::generator() * s.inverse().unwrap()
        );
        // s = 0: undefined for K = 0 only, and Tag(K, 0) = g_1^{1/K}
        assert_eq!(
            tag.eval(&keys[0], &Fr::zero()).unwrap(),
            G1::generator() * keys[0].inverse().unwrap()
        );
        // the key −x_0 has no identifier
        assert_eq!(tag.eval(&-x0, &x0), None);
    }

    /// `TagKeyGen` samples from `Z_p`, not from `Z_p^*`: fed with zeros it returns the key `0`
    /// (the box of `Tag_DDH` would reject it and draw again).
    #[test]
    fn zero_is_a_key_and_keygen_returns_it() {
        let (tag, _) = setup();
        // control: with this RNG a plain field sample is zero
        assert!(Fr::rand(&mut ZerosThen::new(4, 0xd703)).is_zero());
        let key = tag.keygen(&mut ZerosThen::new(4, 0xd703));
        assert!(key.is_zero());
        // keys are fresh field samples: nothing but the RNG output is consumed
        let mut rng = ZerosThen::new(4, 0xd703);
        let mut reference = ZerosThen::new(4, 0xd703);
        for _ in 0..4 {
            assert_eq!(tag.keygen(&mut rng), Fr::rand(&mut reference));
        }
        // and the zero key is a working key
        let s = Fr::from(5u64);
        let t = tag.eval(&key, &s).unwrap();
        assert_eq!(t * s, G1::generator());
        assert!(tag.valid_tag(&t, &s));
    }

    /// Every randomized algorithm accepts an unsized RNG (`R: ?Sized`), e.g. a trait object.
    #[test]
    fn keygen_accepts_a_dyn_rng() {
        trait DynRng: RngCore + CryptoRng {}
        impl<T: RngCore + CryptoRng> DynRng for T {}

        let mut std_rng = StdRng::seed_from_u64(0xd704);
        let rng: &mut dyn DynRng = &mut std_rng;
        let (tag, _) = setup();
        let key = tag.keygen(rng);
        assert_eq!(key, Fr::rand(&mut StdRng::seed_from_u64(0xd704)));
        let s = Fr::from(3u64);
        let t = tag.eval(&key, &s).unwrap();
        let proof = prove_tag(&tag, &key, &t, &s, b"ctx", rng).unwrap();
        assert!(verify_tag(&tag, &t, &s, b"ctx", &proof));
    }

    // ----- key injectivity -------------------------------------------------------------------------

    /// Key injectivity (Def. "Non-adaptive key-injective pseudorandom function", (i)) on
    /// samples: pairwise distinct keys give pairwise distinct tags at a common point, wherever
    /// both are defined. Evidence on samples, not a proof; for the argument of the Lemma see
    /// the next test.
    #[test]
    fn key_injectivity_on_samples() {
        let mut rng = StdRng::seed_from_u64(0xd705);
        let (tag, x0) = setup();
        let s = Fr::rand(&mut rng);
        let mut keys: Vec<Fr> = (0..24).map(|_| tag.keygen(&mut rng)).collect();
        // edge keys, a pair of neighbours, and the keys that are undefined at the points below
        keys.extend([Fr::zero(), Fr::one(), -Fr::one(), keys[0] + Fr::one()]);
        keys.extend([-s, -x0]);
        for (point, undefined) in [(s, -s), (x0, -x0), (Fr::zero(), Fr::zero())] {
            let defined: Vec<(Fr, G1)> = keys
                .iter()
                .filter_map(|k| tag.eval(k, &point).map(|t| (*k, t)))
                .collect();
            // exactly ONE of the keys is outside the domain at this point
            assert_eq!(defined.len(), keys.len() - 1);
            assert!(defined.iter().all(|(k, _)| *k != undefined));
            for i in 0..defined.len() {
                for j in i + 1..defined.len() {
                    assert_ne!(defined[i].0, defined[j].0);
                    assert_ne!(defined[i].1, defined[j].1, "keys {i} and {j} collide");
                }
            }
        }
    }

    /// The argument of the Lemma on `Tag_DY`, "Key injectivity", step by step: `g_1` has order
    /// `p`, so equal tags have equal exponents, and inversion is injective. In one formula:
    /// `T − T' = g_1^{(K'−K)/((K+s)(K'+s))}`, a NON-zero multiple of a generator for `K ≠ K'`.
    #[test]
    fn key_injectivity_for_the_algebraic_reason() {
        let mut rng = StdRng::seed_from_u64(0xd706);
        let (tag, _) = setup();
        let g = *tag.generator();
        // g_1 ≠ 1 and p·g_1 = 1 with p prime: the order of g_1 is exactly p
        assert!(!g.is_zero());
        assert!(g.mul_bigint(Fr::MODULUS).is_zero());
        for _ in 0..8 {
            let (k1, s) = (tag.keygen(&mut rng), Fr::rand(&mut rng));
            for k2 in [tag.keygen(&mut rng), k1 + Fr::one(), -k1, Fr::zero()] {
                assert_ne!(k1, k2);
                let (t1, t2) = (tag.eval(&k1, &s).unwrap(), tag.eval(&k2, &s).unwrap());
                let coefficient = (k2 - k1) * ((k1 + s) * (k2 + s)).inverse().unwrap();
                assert!(!coefficient.is_zero());
                assert_eq!(t1 - t2, g * coefficient);
                assert_ne!(t1, t2);
                // the same fact seen from one tag: only ITS key inverts it back to g_1
                assert_eq!(t1 * (k1 + s), g);
                assert_ne!(t1 * (k2 + s), g);
            }
        }
    }

    // ----- ValidTag, R_Tag ---------------------------------------------------------------------------

    #[test]
    fn valid_tag_rejects_exactly_the_identity() {
        let mut rng = StdRng::seed_from_u64(0xd707);
        let (tag, x0) = setup();
        let s = Fr::rand(&mut rng);
        for point in [s, x0, Fr::zero()] {
            assert!(!tag.valid_tag(&G1::zero(), &point));
        }
        // every honestly generated, defined tag is admissible (it is never the identity) ...
        for _ in 0..16 {
            let key = tag.keygen(&mut rng);
            let t = tag.eval(&key, &s).unwrap();
            assert!(!t.is_zero());
            assert!(tag.valid_tag(&t, &s));
        }
        // ... and so is any other non-identity element: T = g_1^t is the tag of K = 1/t − s
        let t = Fr::rand(&mut rng);
        let element = G1::generator() * t;
        assert!(tag.valid_tag(&element, &s));
        let key = t.inverse().unwrap() - s;
        assert_eq!(tag.eval(&key, &s).unwrap(), element);
    }

    /// `ValidTag` rejects the identity and NOTHING else, in particular not the honest tags with
    /// the most special exponents: `T = g_1` (`K + s = 1`), `T = g_1^{-1}` (`K + s = −1`), and
    /// their neighbours. Each is evaluated, compared with the expected element, admitted,
    /// proved and verified, at a random point and at the points `0`, `1` and `x_0`; then the
    /// same under another generator `h`, where BOTH `±h` and the standard `±g_1` are honest
    /// tags.
    #[test]
    fn valid_tag_admits_the_generator_its_negative_and_their_neighbours() {
        let mut rng = StdRng::seed_from_u64(0xd71a);
        let (tag, x0) = setup();
        let h = G1::generator() * Fr::from(7u64);
        let other = Tag::from_bytes(&h.to_bytes().unwrap()).unwrap();
        let two = Fr::from(2u64);
        let half = two.inverse().unwrap();
        for s in [Fr::rand(&mut rng), Fr::zero(), Fr::one(), x0] {
            // K + s = e, hence T = g_1^{1/e}
            for (e, exponent) in [
                (Fr::one(), Fr::one()),
                (-Fr::one(), -Fr::one()),
                (two, half),
                (-two, -half),
                (half, two),
                (-half, -two),
            ] {
                assert_eq!(e * exponent, Fr::one());
                let key = e - s;
                for (instance, generator) in [(&tag, G1::generator()), (&other, h)] {
                    let expected = generator * exponent;
                    let t = instance.eval(&key, &s).unwrap();
                    assert_eq!(t, expected);
                    assert!(instance.valid_tag(&t, &s));
                    let proof = prove_tag(instance, &key, &t, &s, b"ctx", &mut rng).unwrap();
                    assert!(verify_tag(instance, &t, &s, b"ctx", &proof));
                }
            }
            // under h, the standard generator and its negative are the tags of K + s = ±7
            for (t, e) in [
                (G1::generator(), Fr::from(7u64)),
                (-G1::generator(), -Fr::from(7u64)),
            ] {
                let key = e - s;
                assert_eq!(other.eval(&key, &s).unwrap(), t);
                assert!(other.valid_tag(&t, &s));
                let proof = prove_tag(&other, &key, &t, &s, b"ctx", &mut rng).unwrap();
                assert!(verify_tag(&other, &t, &s, b"ctx", &proof));
            }
        }
    }

    #[test]
    fn tag_equation_is_satisfied_by_the_key_only() {
        let mut rng = StdRng::seed_from_u64(0xd708);
        let (tag, x0) = setup();
        for (key, s) in [
            (tag.keygen(&mut rng), Fr::rand(&mut rng)),
            (tag.keygen(&mut rng), x0),
            (tag.keygen(&mut rng), Fr::zero()),
            (Fr::zero(), Fr::rand(&mut rng)),
        ] {
            let t = tag.eval(&key, &s).unwrap();
            let (rel, var) = tag_relation(&tag, &t, &s).unwrap();
            assert_eq!(var.index(), 0);
            assert_eq!(rel.num_scalars(), 1);
            // ONE linear equation: base T, target g_1 − s·T as the image terms (g_1, 1), (T, −s)
            assert_eq!(
                rel.linear_equations(),
                [LinearEquation {
                    image: vec![(G1::generator(), Fr::one()), (t, -s)],
                    terms: vec![(var, t, Fr::one())],
                }]
            );
            assert_eq!(
                rel.linear_equations()[0].image_value(),
                G1::generator() - t * s
            );
            assert!(rel.is_satisfied_by(&[key]));
            let other = tag.keygen(&mut rng);
            assert_ne!(other, key);
            assert!(!rel.is_satisfied_by(&[other]));
            assert!(!rel.is_satisfied_by(&[key + Fr::one()]));
            assert!(!rel.is_satisfied_by(&[key - Fr::one()]));
            // the key that is undefined at s is no solution either
            assert!(!rel.is_satisfied_by(&[-s]));
            if !key.is_zero() {
                assert!(!rel.is_satisfied_by(&[-key]));
                assert!(!rel.is_satisfied_by(&[Fr::zero()]));
            }
            assert!(!rel.is_satisfied_by(&[]));
            assert!(!rel.is_satisfied_by(&[key, key]));
        }
    }

    /// For `T = 1` the clause reads `1 = g_1`: no witness at all (for `Tag_DDH` the non-key
    /// `K = 0` is one). The honest prover and the verifier refuse the statement at the public
    /// pre-check `ValidTag`.
    #[test]
    fn identity_tag_has_no_witness_and_is_refused() {
        let mut rng = StdRng::seed_from_u64(0xd709);
        let (tag, x0) = setup();
        let s = Fr::rand(&mut rng);
        let (rel, _) = tag_relation(&tag, &G1::zero(), &s).unwrap();
        for k in [
            Fr::zero(),
            Fr::one(),
            -s,
            Fr::one() - s,
            tag.keygen(&mut rng),
        ] {
            assert!(!rel.is_satisfied_by(&[k]));
            assert_eq!(
                fiat_shamir::prove(&rel, &[k], b"ctx", &mut rng),
                Err(Error::WitnessDoesNotSatisfyRelation)
            );
            // the stand-alone prover stops earlier, at ValidTag
            assert_eq!(
                prove_tag(&tag, &k, &G1::zero(), &s, b"ctx", &mut rng),
                Err(Error::InvalidTag)
            );
        }
        // a valid proof for a real tag does not verify for the identity, at any point
        let key = tag.keygen(&mut rng);
        let t = tag.eval(&key, &s).unwrap();
        let proof = prove_tag(&tag, &key, &t, &s, b"ctx", &mut rng).unwrap();
        assert!(verify_tag(&tag, &t, &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &G1::zero(), &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &G1::zero(), &x0, b"ctx", &proof));
    }

    // ----- the stand-alone proof ---------------------------------------------------------------------

    #[test]
    fn standalone_proof_verifies_and_is_bound_to_tag_point_and_context() {
        let mut rng = StdRng::seed_from_u64(0xd70a);
        let (tag, x0) = setup();
        let s = Fr::rand(&mut rng);
        let key = tag.keygen(&mut rng);
        let t = tag.eval(&key, &s).unwrap();

        let proof = prove_tag(&tag, &key, &t, &s, b"ctx", &mut rng).unwrap();
        assert!(verify_tag(&tag, &t, &s, b"ctx", &proof));
        // compact: the challenge and ONE response
        assert_eq!(proof.responses.len(), 1);
        // proving is randomized, verification is not
        let again = prove_tag(&tag, &key, &t, &s, b"ctx", &mut rng).unwrap();
        assert_ne!(again, proof);
        assert!(verify_tag(&tag, &t, &s, b"ctx", &again));

        // bound to T ...
        let t_other = tag.eval(&(key + Fr::one()), &s).unwrap();
        assert!(!verify_tag(&tag, &t_other, &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &(t + t), &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &-t, &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &G1::zero(), &s, b"ctx", &proof));
        // ... to s (also when the tag is re-evaluated at the new point) ...
        let s_other = s + Fr::one();
        assert!(!verify_tag(&tag, &t, &s_other, b"ctx", &proof));
        let t_at_other = tag.eval(&key, &s_other).unwrap();
        assert!(!verify_tag(&tag, &t_at_other, &s_other, b"ctx", &proof));
        assert!(!verify_tag(&tag, &t, &x0, b"ctx", &proof));
        // ... (the same tag IS a tag at the other point, under the key K − 1, which a proof
        // under K says nothing about) ...
        assert_eq!(tag.eval(&(key - Fr::one()), &s_other).unwrap(), t);
        // ... and to the context.
        assert!(!verify_tag(&tag, &t, &s, b"ctx2", &proof));
        assert!(!verify_tag(&tag, &t, &s, b"", &proof));

        // mauled and malformed proofs
        let mut bad = proof.clone();
        bad.responses[0] += Fr::one();
        assert!(!verify_tag(&tag, &t, &s, b"ctx", &bad));
        let mut bad = proof.clone();
        bad.challenge += Fr::one();
        assert!(!verify_tag(&tag, &t, &s, b"ctx", &bad));
        let mut bad = proof.clone();
        bad.responses.push(Fr::zero());
        assert!(!verify_tag(&tag, &t, &s, b"ctx", &bad));
        let empty = FSProof {
            challenge: proof.challenge,
            responses: vec![],
        };
        assert!(!verify_tag(&tag, &t, &s, b"ctx", &empty));
    }

    #[test]
    fn standalone_prover_refuses_a_wrong_key() {
        let mut rng = StdRng::seed_from_u64(0xd70b);
        let (tag, _) = setup();
        let s = Fr::rand(&mut rng);
        let key = tag.keygen(&mut rng);
        let t = tag.eval(&key, &s).unwrap();
        // another key, a neighbour, the zero key, and the key that is undefined at s
        for wrong in [tag.keygen(&mut rng), key + Fr::one(), Fr::zero(), -s] {
            assert_ne!(wrong, key);
            assert_eq!(
                prove_tag(&tag, &wrong, &t, &s, b"ctx", &mut rng),
                Err(Error::WitnessDoesNotSatisfyRelation)
            );
        }
    }

    // ----- ProtocolTag: the generator of a deployment ---------------------------------------------

    /// `pp_Tag` of a deployment: `g_1` is hashed from the label (§6.1.2: "sampled uniformly from
    /// `G_1 \ {1}` when the public parameters are generated"), deterministically, independently
    /// for two labels, and never the standard generator by accident.
    #[test]
    fn protocol_setup_derives_the_generator_from_the_label() {
        let a = <Tag as ProtocolTag<G1>>::setup(b"deployment-A").unwrap();
        let again = <Tag as ProtocolTag<G1>>::setup(b"deployment-A").unwrap();
        let b = <Tag as ProtocolTag<G1>>::setup(b"deployment-B").unwrap();
        assert_eq!(a, again);
        assert_ne!(a, b);
        assert!(a.is_well_formed() && b.is_well_formed());
        // it is the oracle output under its own suffix, and not the standard generator
        let h = <G1Hasher as HashToGroup<G1>>::new(b"deployment-A").unwrap();
        assert_eq!(*a.generator(), h.hash(GENERATOR_SUFFIX, &[]));
        assert_ne!(*a.generator(), G1::generator());
        assert_eq!(Tag::derive(b"deployment-A").unwrap(), a);
        // the three constructors agree on what a generator is
        assert_eq!(Tag::with_generator(*a.generator()).unwrap(), a);
        assert_eq!(Tag::new(), Tag::default());
        assert_eq!(*Tag::new().generator(), G1::generator());
        assert_eq!(
            Tag::with_generator(G1::zero()),
            Err(Error::DegenerateInput("g_1 of Tag_DY"))
        );
    }

    /// With a generator per deployment a stand-alone proof does not replay from one deployment
    /// to another, even at a common point and under a common context: the two instances are two
    /// functions (see also `another_generator_is_another_function`).
    #[test]
    fn standalone_proof_does_not_replay_across_deployments() {
        let mut rng = StdRng::seed_from_u64(0xd70e);
        let a = <Tag as ProtocolTag<G1>>::setup(b"deployment-A").unwrap();
        let b = <Tag as ProtocolTag<G1>>::setup(b"deployment-B").unwrap();
        let usk = a.keygen(&mut rng);
        let s = Fr::from(42u64);
        let t = a.eval(&usk, &s).unwrap();
        let proof = prove_tag(&a, &usk, &t, &s, b"ctx", &mut rng).unwrap();
        assert!(verify_tag(&a, &t, &s, b"ctx", &proof));
        assert!(!verify_tag(&b, &t, &s, b"ctx", &proof));
        // the same key has another tag at the same point in the other deployment
        assert_ne!(b.eval(&usk, &s).unwrap(), t);
    }

    // ----- encoding, degenerate parameters ------------------------------------------------------------

    #[test]
    fn public_parameters_round_trip() {
        let mut rng = StdRng::seed_from_u64(0xd70f);
        let (tag, _) = setup();
        let bytes = tag.to_bytes().unwrap();
        // pp_Tag = g_1: one compressed G_1 element
        assert_eq!(bytes.len(), 48);
        assert_eq!(bytes, G1::generator().to_bytes().unwrap());
        let back = Tag::from_bytes(&bytes).unwrap();
        assert_eq!(back, tag);
        let (key, s) = (tag.keygen(&mut rng), Fr::rand(&mut rng));
        assert_eq!(back.eval(&key, &s), tag.eval(&key, &s));

        // trailing bytes, truncation and a non-point are rejected
        let mut long = bytes.clone();
        long.push(0);
        assert_eq!(Tag::from_bytes(&long), Err(Error::TrailingBytes));
        assert!(Tag::from_bytes(&bytes[..47]).is_err());
        assert!(Tag::from_bytes(&[0xff; 48]).is_err());
        // and so is the identity, which is an element but not a generator
        assert!(Tag::from_bytes(&G1::zero().to_bytes().unwrap()).is_err());
    }

    /// A structure that contains `pp_Tag` and derives its decoder, the way the public parameters
    /// of the credential system do.
    #[derive(Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
    struct Params {
        x0: Fr,
        tag: Tag,
        label: Vec<u8>,
    }

    /// Module docs, "Degenerate parameters", first line of defence: VALIDATED decoding rejects
    /// the identity in the place of `g_1`, on each of the three paths a decoder of arkworks
    /// takes: the direct one, the derived decoder of a containing structure (which passes its
    /// mode on and runs no check of its own), and a `Vec` (which decodes its items unvalidated
    /// and then runs `Valid::batch_check`). Unvalidated decoding is what it is.
    #[test]
    fn validated_decoding_rejects_the_identity_generator() {
        let invalid = Error::from(SerializationError::InvalidData);
        let identity = G1::zero().to_bytes().unwrap();
        // control: the element decoder itself accepts these bytes (`crate::serialization`)
        assert!(G1::from_bytes(&identity).unwrap().is_zero());

        // direct
        assert_eq!(Tag::from_bytes(&identity), Err(invalid.clone()));
        assert!(matches!(
            Tag::deserialize_compressed(&identity[..]),
            Err(SerializationError::InvalidData)
        ));
        let mut uncompressed = Vec::new();
        G1::zero()
            .serialize_uncompressed(&mut uncompressed)
            .unwrap();
        assert!(
            G1::deserialize_uncompressed(&uncompressed[..])
                .unwrap()
                .is_zero()
        );
        assert!(matches!(
            Tag::deserialize_uncompressed(&uncompressed[..]),
            Err(SerializationError::InvalidData)
        ));
        // without validation nothing is checked: the degenerate instance, which `check` and
        // `is_well_formed` tell apart from a generator
        for bad in [
            Tag::deserialize_compressed_unchecked(&identity[..]).unwrap(),
            Tag::deserialize_uncompressed_unchecked(&uncompressed[..]).unwrap(),
        ] {
            assert_eq!(bad, degenerate());
            assert!(!bad.is_well_formed());
            assert!(matches!(bad.check(), Err(SerializationError::InvalidData)));
            // it still ENCODES (to the bytes that do not decode)
            assert_eq!(bad.to_bytes().unwrap(), identity);
        }
        assert!(Tag::new().check().is_ok());

        // inside a structure with a derived decoder
        let params = |tag: Tag| Params {
            x0: Fr::from(3u64),
            tag,
            label: b"deployment".to_vec(),
        };
        let good = params(Tag::new()).to_bytes().unwrap();
        assert_eq!(Params::from_bytes(&good).unwrap(), params(Tag::new()));
        let bad = params(degenerate()).to_bytes().unwrap();
        assert_eq!(good.len(), bad.len());
        assert_eq!(Params::from_bytes(&bad), Err(invalid.clone()));
        assert_eq!(
            Params::deserialize_compressed_unchecked(&bad[..]).unwrap(),
            params(degenerate())
        );
        // ... whose derived `check` (its own path inside a Vec) asks the instance as well
        assert!(params(Tag::new()).check().is_ok());
        assert!(matches!(
            params(degenerate()).check(),
            Err(SerializationError::InvalidData)
        ));
        assert_eq!(
            Vec::<Params>::from_bytes(
                &vec![params(Tag::new()), params(degenerate())]
                    .to_bytes()
                    .unwrap()
            ),
            Err(invalid.clone())
        );

        // inside a Vec (the `batch_check` path), at any position
        let h = Tag::from_bytes(&(G1::generator() * Fr::from(7u64)).to_bytes().unwrap()).unwrap();
        let good = vec![Tag::new(), h.clone()];
        assert_eq!(
            Vec::<Tag>::from_bytes(&good.to_bytes().unwrap()).unwrap(),
            good
        );
        for bad in [
            vec![degenerate(), Tag::new(), h.clone()],
            vec![Tag::new(), degenerate(), h.clone()],
            vec![Tag::new(), h, degenerate()],
        ] {
            assert_eq!(
                Vec::<Tag>::from_bytes(&bad.to_bytes().unwrap()),
                Err(invalid.clone())
            );
        }
    }

    /// The hand-written decoder must not lose what the derived one did: the group element is
    /// still validated, on the direct path AND by `Valid::check` (the `Vec` path). The witness
    /// is a point of the curve outside the subgroup of order `p` (the cofactor of BLS12-381
    /// `G_1` is not `1`), which compressed encoding represents and only validation rejects.
    #[test]
    fn validated_decoding_still_validates_the_group_element() {
        use ark_bls12_381::{Fq, G1Affine};

        let invalid = Error::from(SerializationError::InvalidData);
        let outside = (1u64..=64)
            .filter_map(|x| G1Affine::get_point_from_x_unchecked(Fq::from(x), false))
            .find(|point| !point.is_in_correct_subgroup_assuming_on_curve())
            .expect("a curve point outside the subgroup among 64 abscissae");
        assert!(outside.is_on_curve());
        let bytes = outside.to_bytes().unwrap();
        // control: the element decoder rejects it, and only because of the subgroup
        assert_eq!(G1::from_bytes(&bytes), Err(invalid.clone()));
        assert_eq!(
            G1Affine::deserialize_compressed_unchecked(&bytes[..]).unwrap(),
            outside
        );

        assert_eq!(Tag::from_bytes(&bytes), Err(invalid.clone()));
        let unchecked = Tag::deserialize_compressed_unchecked(&bytes[..]).unwrap();
        // not the identity, so ONLY the element's own check stands in the way
        assert!(unchecked.is_well_formed());
        assert!(matches!(
            unchecked.check(),
            Err(SerializationError::InvalidData)
        ));
        let mut in_a_vec = Vec::new();
        1u64.serialize_compressed(&mut in_a_vec).unwrap();
        in_a_vec.extend_from_slice(&bytes);
        assert_eq!(Vec::<Tag>::from_bytes(&in_a_vec), Err(invalid));
        // control: the same framing with a generator decodes
        let mut in_a_vec = Vec::new();
        1u64.serialize_compressed(&mut in_a_vec).unwrap();
        in_a_vec.extend_from_slice(&Tag::new().to_bytes().unwrap());
        assert_eq!(Vec::<Tag>::from_bytes(&in_a_vec).unwrap(), vec![Tag::new()]);
    }

    /// The liveness hazard behind the decoder (module docs, "Degenerate parameters"): generic
    /// code runs `Register` under whatever `pp_Tag` it decoded. Every instance that validated
    /// decoding lets through must therefore yield a user key; under the identity "generator" no
    /// attempt ever would (the second line of defence, the hook `ProtocolTag::is_well_formed`, is
    /// the subject of `generic_code_can_refuse_a_degenerate_instance_before_any_restart_loop`).
    #[test]
    fn every_decodable_instance_yields_a_user_key() {
        let mut rng = StdRng::seed_from_u64(0xd71b);
        let (_, x0) = setup();
        let encodings = [
            G1::generator(),
            -G1::generator(),
            G1::generator() * Fr::from(7u64),
            G1::rand(&mut rng),
            G1::zero(),
        ]
        .map(|g| g.to_bytes().unwrap());
        let mut decoded = 0;
        for bytes in &encodings {
            // generic code: decode, then register (one key, as in the box)
            let Ok(instance) = Tag::from_bytes(bytes) else {
                continue;
            };
            decoded += 1;
            let (id, usk) = register(&instance, &x0, &mut rng).expect("RegisterSuccessful");
            assert_eq!(id * (usk + x0), *instance.generator());
            assert!(instance.valid_tag(&id, &x0));
        }
        // everything but the identity decodes
        assert_eq!(decoded, encodings.len() - 1);
        // the hazard itself, for whoever decodes without validation: no attempt succeeds
        let bad = degenerate();
        for _ in 0..64 {
            let usk = bad.keygen(&mut rng);
            assert_eq!(bad.eval(&usk, &x0), None);
        }
    }

    /// The second line of defence (module docs, "Degenerate parameters"). Generic code cannot
    /// call the inherent `DY::is_well_formed`; it asks through the hook of `ProtocolTag`, which
    /// the setup of the protocol evaluates before any restart loop can run.
    #[test]
    fn generic_code_can_refuse_a_degenerate_instance_before_any_restart_loop() {
        fn through_the_trait<G: PrimeGroup, T: ProtocolTag<G>>(tag: &T) -> bool {
            tag.is_well_formed()
        }
        let (good, _) = setup();
        let bad = degenerate();
        assert!(good.is_well_formed() && through_the_trait(&good));
        assert!(!bad.is_well_formed() && !through_the_trait(&bad));
        let derived = <Tag as ProtocolTag<G1>>::setup(DOMAIN).unwrap();
        assert!(through_the_trait(&derived));
    }

    /// A decoded instance with ANOTHER generator is a well-formed instance of another function;
    /// tags and proofs do not transfer.
    #[test]
    fn another_generator_is_another_function() {
        let mut rng = StdRng::seed_from_u64(0xd710);
        let (tag, _) = setup();
        let h = G1::generator() * Fr::from(7u64);
        let other = Tag::from_bytes(&h.to_bytes().unwrap()).unwrap();
        assert!(other.is_well_formed());
        assert_eq!(*other.generator(), h);
        assert_ne!(other, tag);

        let (key, s) = (tag.keygen(&mut rng), Fr::rand(&mut rng));
        let (t, t_other) = (tag.eval(&key, &s).unwrap(), other.eval(&key, &s).unwrap());
        assert_eq!(t_other * (key + s), h);
        assert_ne!(t_other, t);
        assert_eq!(other.eval(&key, &-key), None);

        // each instance proves its own tags, and only those
        let proof = prove_tag(&tag, &key, &t, &s, b"ctx", &mut rng).unwrap();
        assert!(!verify_tag(&other, &t, &s, b"ctx", &proof));
        assert!(!verify_tag(&other, &t_other, &s, b"ctx", &proof));
        assert_eq!(
            prove_tag(&other, &key, &t, &s, b"ctx", &mut rng),
            Err(Error::WitnessDoesNotSatisfyRelation)
        );
        let proof = prove_tag(&other, &key, &t_other, &s, b"ctx", &mut rng).unwrap();
        assert!(verify_tag(&other, &t_other, &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &t_other, &s, b"ctx", &proof));
    }

    /// Module docs, "Degenerate parameters": with `g_1 = 1` the clause is satisfied by the
    /// PUBLIC value `K = −s` for every `T`. A cheating prover builds a Fiat-Shamir proof for the
    /// bare clause under exactly the context the tag verifier derives, so ONLY the instance
    /// check inside `ValidTag` stands between it and acceptance.
    #[test]
    fn degenerate_generator_makes_the_clause_vacuous_and_is_rejected() {
        let mut rng = StdRng::seed_from_u64(0xd711);
        let tag = degenerate();
        assert!(!tag.is_well_formed());
        assert_ne!(tag, Tag::new());
        let s = Fr::rand(&mut rng);

        // no evaluation is defined (its value would be the identity) ...
        for key in [tag.keygen(&mut rng), Fr::zero(), -s, Fr::one() - s] {
            assert_eq!(tag.eval(&key, &s), None);
        }
        // ... and no tag is admissible, although an arbitrary T "has" the witness K = −s
        let t = G1::rand(&mut rng);
        assert!(!t.is_zero());
        let (rel, _) = tag_relation(&tag, &t, &s).unwrap();
        assert!(rel.is_satisfied_by(&[-s]));
        let ctx = tag_proof_context(&tag, &t, &s, b"ctx").unwrap();
        let bare = fiat_shamir::prove(&rel, &[-s], &ctx, &mut rng).unwrap();
        assert!(fiat_shamir::verify(&rel, &ctx, &bare));
        assert!(!tag.valid_tag(&t, &s));
        assert!(!verify_tag(&tag, &t, &s, b"ctx", &bare));
        assert_eq!(
            prove_tag(&tag, &-s, &t, &s, b"ctx", &mut rng),
            Err(Error::InvalidTag)
        );
        // control: under a well-formed instance the same T is admissible and −s is no witness
        let (good, _) = setup();
        assert!(good.valid_tag(&t, &s));
        let (rel, _) = tag_relation(&good, &t, &s).unwrap();
        assert!(!rel.is_satisfied_by(&[-s]));
    }

    // ----- how the protocol handles ⊥ ----------------------------------------------------------

    /// `Register` of the protocol box: one sample `usk ← TagKeyGen`, and `RegisterFailed`
    /// (`None`) if `id = Tag(usk, x_0) = ⊥`.
    fn register<R: RngCore + CryptoRng>(tag: &Tag, x0: &Fr, rng: &mut R) -> Option<(G1, Fr)> {
        let usk = tag.keygen(rng);
        tag.eval(&usk, x0).map(|id| (id, usk))
    }

    /// `Register` fails on the key `usk = −x_0`, which has no identifier, and draws no other key;
    /// `TagKeyGen` alone does not exclude such a key: here it is the zero key, at the
    /// identifier point `x_0 = 0`.
    #[test]
    fn register_fails_on_an_undefined_identifier() {
        let (tag, _) = setup();
        let x0 = Fr::zero();
        let mut rng = ZerosThen::new(4, 0xd712);
        assert_eq!(register(&tag, &x0, &mut rng), None);
        // a second registration draws the next key of the stream, which is defined
        let (id, usk) = register(&tag, &x0, &mut rng).expect("a defined identifier");
        assert!(!usk.is_zero());
        assert_eq!(id * (usk + x0), G1::generator());
        assert!(tag.valid_tag(&id, &x0));
        // control: the same key stream from its second key on
        let mut rng = ZerosThen::new(0, 0xd712);
        assert_eq!(register(&tag, &x0, &mut rng), Some((id, usk)));
    }

    /// The `⊥` that `Register` cannot exclude: an attester's key passes ITS registration and is
    /// undefined at the recipient point `x_Q` of the requester; the attestation aborts
    /// (`Error::UndefinedTag` in the protocol).
    #[test]
    fn attester_key_can_be_undefined_at_the_recipient_point() {
        let (tag, x0) = setup();
        let mut rng = StdRng::seed_from_u64(0xd714);
        let x_q = Fr::rand(&mut rng);
        let usk_p = -x_q;
        // an admissible user key: its identifier is defined ...
        let id_p = tag.eval(&usk_p, &x0).expect("−x_Q ≠ −x_0");
        assert!(tag.valid_tag(&id_p, &x0));
        // ... but t_{P→Q} = Tag(usk_P, x_Q) = ⊥, reported as `None`
        assert_eq!(tag.eval(&usk_p, &x_q), None);
        assert_eq!(
            tag.eval(&usk_p, &x_q).ok_or(Error::UndefinedTag),
            Err(Error::UndefinedTag)
        );
        // every other attester key is fine at this point
        assert!(tag.eval(&(usk_p + Fr::one()), &x_q).is_some());
    }

    // ----- genericity ----------------------------------------------------------------------------------

    fn generic_round_trip<G: PrimeGroup>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let x0: G::ScalarField = point(DOMAIN);
        for tag in [
            DY::<G, InsecureExponentHasher>::new(),
            DY::<G, InsecureExponentHasher>::setup(DOMAIN).unwrap(),
        ] {
            assert!(tag.is_well_formed());
            let g = *tag.generator();
            let usk = tag.keygen(&mut rng);
            let id = tag.eval(&usk, &x0).unwrap();
            assert_eq!(id * (usk + x0), g);
            assert_ne!(id, g * usk);
            assert_eq!(tag.eval(&usk, &-usk), None);
            assert_eq!(tag.eval(&-x0, &x0), None);

            let s = G::ScalarField::rand(&mut rng);
            let t = tag.eval(&usk, &s).unwrap();
            assert!(tag.valid_tag(&t, &s));
            assert!(!tag.valid_tag(&G::zero(), &s));
            assert_ne!(tag.eval(&(usk + G::ScalarField::ONE), &s).unwrap(), t);
            let (rel, _) = tag_relation(&tag, &t, &s).unwrap();
            assert!(rel.is_satisfied_by(&[usk]));
            assert!(!rel.is_satisfied_by(&[usk + G::ScalarField::ONE]));

            let proof = prove_tag(&tag, &usk, &t, &s, b"ctx", &mut rng).unwrap();
            assert!(verify_tag(&tag, &t, &s, b"ctx", &proof));
            assert!(!verify_tag(&tag, &t, &x0, b"ctx", &proof));
            assert!(!verify_tag(&tag, &G::zero(), &s, b"ctx", &proof));
            assert_eq!(
                prove_tag(&tag, &usk, &G::zero(), &s, b"ctx", &mut rng),
                Err(Error::InvalidTag)
            );
            assert_eq!(
                DY::<G, InsecureExponentHasher>::from_bytes(&tag.to_bytes().unwrap()).unwrap(),
                tag
            );
        }
    }

    /// Evaluation needs no hash-to-group, so the tag runs over every prime-order group of
    /// arkworks; the derived generator needs an oracle into the group (here the INSECURE test
    /// oracle, which suffices for the algebra).
    #[test]
    fn generic_over_the_group() {
        generic_round_trip::<ark_bn254::G1Projective>(0xd716);
        generic_round_trip::<ark_bn254::G2Projective>(0xd717);
        generic_round_trip::<ark_bls12_381::G2Projective>(0xd718);
    }
}
