//! `Tag_DDH`, the default tag of the protocol (paper §6.1.1, "The DDH instantiation").
//!
//! | paper (box `Tag_DDH`) | here |
//! |---|---|
//! | key space `Z_p \ {0}`, domain `Z_p`, range `G_1 \ {1}` | [`KIPRF::Key`], [`KIPRF::Input`] `= Z_p`, [`KIPRF::Output`] `= G` |
//! | `TagKeyGen`: `K ← Z_p \ {0}` | [`KIPRF::keygen`] |
//! | `TagEval(K, x)`: `P ← htag(x)`; return `P^K` | [`KIPRF::eval`], [`DDH::htag`] |
//! | `t ∈ T`, i.e. `t ≠ 1` | [`SigmaFriendlyKIPRF::valid_tag`] |
//! | `R_Tag`: the Schnorr relation with base `htag(x)`, target `t`, witness `K` | [`SigmaFriendlyKIPRF::tag_equations`] |
//! | `pp_Tag`: the oracle `htag` of the deployment | [`ProtocolTag::setup`] |
//!
//! The paper states the instantiation over `G_1`; the code is generic over a prime-order group
//! `G`. `htag` is a [`HashToGroup`] oracle with range `G \ {1}`.
//!
//! Security (Lemma on `Tag_DDH`, §6.1.1): in the random-oracle model for `htag` and under DDH
//! in `G_1` the function has key uniqueness, weak pseudorandomness and proof friendliness. Key
//! uniqueness is unconditional: `htag(x) ≠ 1` has order `p`, so `htag(x)^K = htag(x)^{K'}`
//! forces `K = K'`.
//!
//! # In formulas
//!
//! With $`H_2 = \mathsf{htag}`$ a random oracle onto $`\mathbb{G} \setminus \{1\}`$:
//!
//! ```math
//! \mathsf{Tag}_{\mathsf{DDH}}(K, x) = H_2(x)^{K}, \qquad K \in \mathbb{Z}_p \setminus \{0\},\quad x \in \mathbb{Z}_p
//! ```
//!
//! ```math
//! R_{\mathsf{Tag}} = \bigl\{\, \bigl((t, x),\ K\bigr) \;:\; t \in \mathcal T \wedge t = H_2(x)^{K} \,\bigr\}, \qquad \mathcal T = \mathbb G \setminus \{1\}
//! ```
//!
//! # Example
//!
//! ```
//! use ark_bls12_381::{Fr, G1Projective as G1};
//! use predicate_credential_system::{
//!     hash::{bls12_381::G1Hasher, Transcript},
//!     kiprf::{prove_tag, verify_tag, KIPRF, ProtocolTag, DDH},
//! };
//! use rand::{rngs::StdRng, SeedableRng};
//!
//! let mut rng = StdRng::seed_from_u64(1);
//! let label = b"example deployment";
//! let tag = DDH::<G1, G1Hasher>::setup(label)?;
//!
//! // a user: usk, and the identifier id = Tag(usk, x_0) at an identifier point x_0 (the
//! // protocol derives x_0 = H_id(⟨hvk⟩) from the helper key; here a stand-alone oracle output)
//! let x0: Fr = Transcript::new(b"/EXAMPLE-POINT").challenge_scalar();
//! let usk = tag.keygen(&mut rng);
//! let id = tag.eval(&usk, &x0).expect("the domain of Tag_DDH is total");
//!
//! // a proof of knowledge of the key behind the identifier (the π_id of the protocol)
//! let proof = prove_tag(&tag, &usk, &id, &x0, b"context", &mut rng)?;
//! assert!(verify_tag(&tag, &id, &x0, b"context", &proof));
//! assert!(!verify_tag(&tag, &id, &x0, b"another context", &proof));
//! # Ok::<(), predicate_credential_system::Error>(())
//! ```

use ark_ec::PrimeGroup;
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{CryptoRng, RngCore};

use super::{KIPRF, ProtocolTag, SigmaFriendlyKIPRF};
use crate::{
    error::Error,
    hash::{H2_SUFFIX, HashToGroup},
    sample::nonzero_scalar,
    sigma::{LinearEquation, ScalarVar},
};

/// The public parameters `pp_Tag` of `Tag_DDH` over the group `G`: the hash-to-group oracle
/// `htag` of a deployment.
///
/// An instance is part of the public parameters of the protocol, hence the serialization
/// derives. Two instances are equal iff they define the same function.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct DDH<G: PrimeGroup, H: HashToGroup<G>> {
    /// The random oracle behind `htag`, bound to a deployment label.
    hasher: H,
    _group: core::marker::PhantomData<G>,
}

impl<G: PrimeGroup, H: HashToGroup<G>> DDH<G, H> {
    /// `Tag_DDH` (box `Tag_DDH`) with the oracle `hasher` as `htag`.
    #[must_use]
    pub fn new(hasher: H) -> Self {
        Self {
            hasher,
            _group: core::marker::PhantomData,
        }
    }

    /// The oracle behind `htag`.
    #[must_use]
    pub fn hasher(&self) -> &H {
        &self.hasher
    }

    /// `htag(x) ∈ G \ {1}` (box `Tag_DDH`, `TagEval` step 1): the random oracle `H_2` on the
    /// canonical encoding of `x`. Deterministic; never the identity.
    #[must_use]
    pub fn htag(&self, input: &G::ScalarField) -> G {
        self.hasher.hash_scalar(H2_SUFFIX, input)
    }

    /// Always `true`: `Tag_DDH` has no degenerate parameters.
    ///
    /// Implementation note, not an algorithm of the paper ([`ProtocolTag::is_well_formed`]
    /// explains what the check is for). An instance consists of a deployment label, and whatever
    /// it is (assembled or decoded, with or without validation) `htag` has range `G \ {1}`:
    /// every value comes from a [`HashToGroup`] oracle, whose contract excludes the identity.
    /// `TagEval` is therefore defined for every key of the key space `Z_p \ {0}` at every point,
    /// and a `Register` loop runs once.
    #[must_use]
    pub fn is_well_formed(&self) -> bool {
        true
    }
}

impl<G: PrimeGroup, H: HashToGroup<G>> KIPRF for DDH<G, H> {
    type Key = G::ScalarField;
    type Input = G::ScalarField;
    type Output = G;

    /// `TagKeyGen` (box `Tag_DDH`): step 1, `K ← Z_p \ {0}`; step 2, return `K`.
    fn keygen<R: RngCore + CryptoRng + ?Sized>(&self, rng: &mut R) -> Self::Key {
        nonzero_scalar(rng)
    }

    /// `TagEval(K, x)` (box `Tag_DDH`): step 1, `P ← htag(x)`; step 2, return `P^K`.
    ///
    /// The domain is total: for a key of the key space the result is never `⊥` and, because
    /// `P ≠ 1` and `K ≠ 0`, never the identity. `K = 0` lies outside the key space and
    /// evaluates to `None` (its "tag" would be the identity at every point).
    fn eval(&self, key: &Self::Key, input: &Self::Input) -> Option<Self::Output> {
        if key.is_zero() {
            return None;
        }
        let p = self.htag(input);
        Some(p * *key)
    }
}

impl<G: PrimeGroup, H: HashToGroup<G>> SigmaFriendlyKIPRF for DDH<G, H> {
    type Group = G;

    /// `t ∈ T = G \ {1}` (§6.1.1). With `t = 1` the clause `t = htag(x)^K` would only be
    /// satisfied by `K = 0`, which is not a key.
    fn valid_tag(&self, tag: &G, _input: &G::ScalarField) -> bool {
        !tag.is_zero()
    }

    /// `R_Tag_DDH` as ONE linear equation (Lemma on `Tag_DDH`, "Proof friendliness"): after
    /// computing `P = htag(x)`, the Schnorr relation `t = P^K` with base `P`, target `t` and
    /// witness `K`.
    fn tag_equations(
        &self,
        key: ScalarVar,
        tag: &G,
        input: &G::ScalarField,
    ) -> Vec<LinearEquation<G>> {
        vec![LinearEquation::dlog(key, self.htag(input), *tag)]
    }
}

impl<G: PrimeGroup, H: HashToGroup<G>> ProtocolTag<G> for DDH<G, H> {
    const NAME: &'static str = "DDH";

    /// `pp_Tag`: the oracle `htag` of the deployment `label`.
    fn setup(label: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(H::new(label)?))
    }

    /// [`DDH::is_well_formed`]: always `true`, `TagEval` is total on the key space.
    fn is_well_formed(&self) -> bool {
        // The inherent method (inherent associated functions take precedence in a path).
        DDH::is_well_formed(self)
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ff::{Field, One, PrimeField, UniformRand};
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        hash::{Transcript, bls12_381::G1Hasher, testing::InsecureExponentHasher},
        kiprf::{prove_tag, tag_proof_context, tag_relation, verify_tag},
        serialization::WireFormat,
        sigma::{FSProof, LinearRelation, fiat_shamir},
    };

    type G1 = G1Projective;
    type Tag = DDH<G1, G1Hasher>;

    const DOMAIN: &[u8] = b"tag-ddh-unit-tests";

    /// A fixed point of the test deployment `domain`, standing for an identifier point.
    fn point<F: PrimeField>(domain: &[u8]) -> F {
        let mut transcript = Transcript::new(b"/TEST-POINT");
        transcript.append_bytes(b"deployment", domain);
        transcript.challenge_scalar()
    }

    fn setup() -> (Tag, Fr) {
        let x0: Fr = point(DOMAIN);
        (Tag::setup(DOMAIN).unwrap(), x0)
    }

    #[test]
    fn evaluation_is_deterministic() {
        let mut rng = StdRng::seed_from_u64(0xdd01);
        let (tag, _) = setup();
        let (key, s) = (tag.keygen(&mut rng), Fr::rand(&mut rng));
        let t = tag.eval(&key, &s).unwrap();
        assert_eq!(tag.eval(&key, &s).unwrap(), t);
        // an independently constructed instance of the same deployment is the same function
        let (again, _) = setup();
        assert_eq!(again, tag);
        assert_eq!(again.eval(&key, &s).unwrap(), t);
        // and it is `htag(x)^K`
        assert_eq!(t, tag.htag(&s) * key);
        // another point, another deployment: another tag
        assert_ne!(tag.eval(&key, &(s + Fr::one())).unwrap(), t);
        let other = Tag::setup(b"another deployment").unwrap();
        assert_ne!(other.eval(&key, &s).unwrap(), t);
    }

    #[test]
    fn keys_are_nonzero_and_the_zero_key_has_no_tag() {
        let mut rng = StdRng::seed_from_u64(0xdd02);
        let (tag, x0) = setup();
        for _ in 0..64 {
            assert!(!tag.keygen(&mut rng).is_zero());
        }
        let s = Fr::rand(&mut rng);
        assert_eq!(tag.eval(&Fr::zero(), &s), None);
        assert_eq!(tag.eval(&Fr::zero(), &x0), None);
    }

    /// Key uniqueness (Def. "Key-injective PRF", (i)) on samples: pairwise distinct keys give
    /// pairwise distinct tags at a common point. Evidence on samples, not a proof; the proof is
    /// the one-line argument of the Lemma on `Tag_DDH`.
    #[test]
    fn key_uniqueness_on_samples() {
        let mut rng = StdRng::seed_from_u64(0xdd03);
        let (tag, x0) = setup();
        let s = Fr::rand(&mut rng);
        let mut keys: Vec<Fr> = (0..24).map(|_| tag.keygen(&mut rng)).collect();
        // edge keys of the key space, and a pair of neighbours
        keys.extend([Fr::one(), -Fr::one(), Fr::from(2u64), keys[0] + Fr::one()]);
        for point in [s, x0] {
            let tags: Vec<G1> = keys.iter().map(|k| tag.eval(k, &point).unwrap()).collect();
            for i in 0..keys.len() {
                for j in i + 1..keys.len() {
                    assert_ne!(keys[i], keys[j]);
                    assert_ne!(tags[i], tags[j], "keys {i} and {j} collide");
                }
            }
        }
    }

    /// `htag` is the oracle at every point, including the identifier point: nothing is
    /// programmed, so no point is special and no output is the identity.
    #[test]
    fn htag_is_the_oracle_everywhere() {
        let (tag, x0) = setup();
        for s in (0u64..16).map(Fr::from).chain([x0]) {
            let p = tag.htag(&s);
            assert_eq!(p, tag.hasher().hash_scalar(H2_SUFFIX, &s));
            assert!(!p.is_zero());
            assert!(p.mul_bigint(Fr::MODULUS).is_zero());
        }
    }

    /// `ProtocolTag::is_well_formed` is the liveness hook of generic code: under a well-formed
    /// instance a `Register` loop terminates. `Tag_DDH` has no degenerate parameters: whatever
    /// the label is, and however the instance was decoded, every key of the key space has a
    /// defined, admissible tag at every point.
    #[test]
    fn every_instance_is_well_formed_and_total() {
        fn through_the_trait<T: ProtocolTag<G1>>(tag: &T) -> bool {
            tag.is_well_formed()
        }
        let mut rng = StdRng::seed_from_u64(0xdd0f);
        let (tag, x0) = setup();
        let empty = Tag::new(G1Hasher::new(b"").unwrap());
        // decoded without any validation: the contract of the `*_unchecked` decoders
        let mut bytes = Vec::new();
        empty.serialize_compressed(&mut bytes).unwrap();
        let unchecked = Tag::deserialize_compressed_unchecked(&bytes[..]).unwrap();
        assert_eq!(unchecked, empty);

        for (i, tag) in [&tag, &empty, &unchecked].into_iter().enumerate() {
            assert!(tag.is_well_formed(), "case {i}");
            assert!(through_the_trait(tag), "case {i}");
            // what the hook promises: no key of the key space is undefined anywhere
            for s in [x0, Fr::zero(), Fr::one(), -Fr::one(), Fr::rand(&mut rng)] {
                for key in [Fr::one(), -Fr::one(), -s, tag.keygen(&mut rng)] {
                    if key.is_zero() {
                        continue; // −s = 0 is not a key
                    }
                    let t = tag.eval(&key, &s).expect("Tag_DDH is total");
                    assert!(tag.valid_tag(&t, &s), "case {i}");
                }
            }
        }
    }

    #[test]
    fn valid_tag_rejects_exactly_the_identity() {
        let mut rng = StdRng::seed_from_u64(0xdd05);
        let (tag, x0) = setup();
        let s = Fr::rand(&mut rng);
        assert!(!tag.valid_tag(&G1::zero(), &s));
        assert!(!tag.valid_tag(&G1::zero(), &x0));
        // every honestly generated tag is admissible ...
        for _ in 0..16 {
            let key = tag.keygen(&mut rng);
            assert!(tag.valid_tag(&tag.eval(&key, &s).unwrap(), &s));
        }
        // ... and so is any other non-identity element (it is a tag under SOME key)
        assert!(tag.valid_tag(&G1::rand(&mut rng), &s));
    }

    #[test]
    fn tag_equation_is_satisfied_by_the_key_only() {
        let mut rng = StdRng::seed_from_u64(0xdd06);
        let (tag, x0) = setup();
        for s in [Fr::rand(&mut rng), x0] {
            let key = tag.keygen(&mut rng);
            let t = tag.eval(&key, &s).unwrap();
            let (rel, var) = tag_relation(&tag, &t, &s).unwrap();
            assert_eq!(var.index(), 0);
            assert_eq!(rel.num_scalars(), 1);
            // ONE linear equation: base htag(x), target t
            assert_eq!(
                rel.linear_equations(),
                [LinearEquation::dlog(var, tag.htag(&s), t)]
            );
            assert!(rel.is_satisfied_by(&[key]));
            let other = tag.keygen(&mut rng);
            assert!(!rel.is_satisfied_by(&[other]));
            assert!(!rel.is_satisfied_by(&[key + Fr::one()]));
            assert!(!rel.is_satisfied_by(&[-key]));
            assert!(!rel.is_satisfied_by(&[Fr::zero()]));
            assert!(!rel.is_satisfied_by(&[]));
        }
    }

    /// Why `t ∈ T` is a separate public check: the linear clause alone accepts `t = 1` with
    /// the non-key `K = 0`.
    #[test]
    fn identity_tag_satisfies_the_clause_but_not_the_relation() {
        let mut rng = StdRng::seed_from_u64(0xdd07);
        let (tag, _) = setup();
        let s = Fr::rand(&mut rng);
        let (rel, _) = tag_relation(&tag, &G1::zero(), &s).unwrap();
        assert!(rel.is_satisfied_by(&[Fr::zero()]));
        // A cheating prover builds a Fiat-Shamir proof for the bare clause, under exactly the
        // context the tag verifier derives ...
        let ctx = tag_proof_context(&tag, &G1::zero(), &s, b"ctx").unwrap();
        let bare = fiat_shamir::prove(&rel, &[Fr::zero()], &ctx, &mut rng).unwrap();
        assert!(fiat_shamir::verify(&rel, &ctx, &bare));
        // ... so ONLY the public pre-check `t ∈ T` stands between it and acceptance.
        assert!(!verify_tag(&tag, &G1::zero(), &s, b"ctx", &bare));
        // The honest prover refuses the statement as well.
        assert_eq!(
            prove_tag(&tag, &Fr::zero(), &G1::zero(), &s, b"ctx", &mut rng),
            Err(Error::InvalidTag)
        );
    }

    #[test]
    fn standalone_proof_verifies_and_is_bound_to_tag_point_and_context() {
        let mut rng = StdRng::seed_from_u64(0xdd08);
        let (tag, x0) = setup();
        let s = Fr::rand(&mut rng);
        let key = tag.keygen(&mut rng);
        let t = tag.eval(&key, &s).unwrap();

        let proof = prove_tag(&tag, &key, &t, &s, b"ctx", &mut rng).unwrap();
        assert!(verify_tag(&tag, &t, &s, b"ctx", &proof));
        // compact: the challenge and ONE response
        assert_eq!(proof.responses.len(), 1);

        // bound to t ...
        let t_other = tag.eval(&(key + Fr::one()), &s).unwrap();
        assert!(!verify_tag(&tag, &t_other, &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &(t + t), &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &G1::zero(), &s, b"ctx", &proof));
        // ... to x (also when the tag is re-evaluated at the new point) ...
        let s_other = s + Fr::one();
        assert!(!verify_tag(&tag, &t, &s_other, b"ctx", &proof));
        let t_at_other = tag.eval(&key, &s_other).unwrap();
        assert!(!verify_tag(&tag, &t_at_other, &s_other, b"ctx", &proof));
        assert!(!verify_tag(&tag, &t, &x0, b"ctx", &proof));
        // ... to the context ...
        assert!(!verify_tag(&tag, &t, &s, b"ctx2", &proof));
        assert!(!verify_tag(&tag, &t, &s, b"", &proof));
        // ... and to the deployment (another oracle htag).
        let other = Tag::setup(b"another deployment").unwrap();
        assert!(!verify_tag(&other, &t, &s, b"ctx", &proof));

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

    /// `H_1` has no deployment input; a stand-alone proof is bound to its deployment through
    /// `pp_Tag` in the context. Even for a statement whose base and target coincide in two
    /// deployments the proof does not replay.
    #[test]
    fn identifier_proof_does_not_replay_in_another_deployment() {
        let mut rng = StdRng::seed_from_u64(0xdd0f);
        let a = Tag::setup(b"deployment-A").unwrap();
        let b = Tag::setup(b"deployment-B").unwrap();
        let x0: Fr = point(b"deployment-A");
        let usk = a.keygen(&mut rng);
        let id = a.eval(&usk, &x0).unwrap();
        let proof = prove_tag(&a, &usk, &id, &x0, b"ctx", &mut rng).unwrap();
        assert!(verify_tag(&a, &id, &x0, b"ctx", &proof));
        assert!(!verify_tag(&b, &id, &x0, b"ctx", &proof));
    }

    #[test]
    fn standalone_prover_refuses_a_wrong_key() {
        let mut rng = StdRng::seed_from_u64(0xdd09);
        let (tag, _) = setup();
        let s = Fr::rand(&mut rng);
        let key = tag.keygen(&mut rng);
        let t = tag.eval(&key, &s).unwrap();
        let wrong = tag.keygen(&mut rng);
        assert_eq!(
            prove_tag(&tag, &wrong, &t, &s, b"ctx", &mut rng),
            Err(Error::WitnessDoesNotSatisfyRelation)
        );
    }

    #[test]
    fn public_parameters_round_trip() {
        let (tag, x0) = setup();
        let bytes = tag.to_bytes().unwrap();
        let back = Tag::from_bytes(&bytes).unwrap();
        assert_eq!(back, tag);
        assert_eq!(back.htag(&x0), tag.htag(&x0));
        assert_eq!(back.htag(&Fr::from(9u64)), tag.htag(&Fr::from(9u64)));

        let other = Tag::setup(b"another deployment").unwrap();
        assert_ne!(other.to_bytes().unwrap(), bytes);
    }

    // -----------------------------------------------------------------------------------------
    // Genericity: the same code over another group
    // -----------------------------------------------------------------------------------------

    fn generic_round_trip<G: PrimeGroup>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let x0: G::ScalarField = point(DOMAIN);
        let tag = DDH::<G, InsecureExponentHasher>::setup(DOMAIN).unwrap();
        let usk = tag.keygen(&mut rng);
        let id = tag.eval(&usk, &x0).unwrap();
        assert!(tag.valid_tag(&id, &x0));
        let s = G::ScalarField::rand(&mut rng);
        let t = tag.eval(&usk, &s).unwrap();
        assert!(tag.valid_tag(&t, &s));
        assert_ne!(tag.eval(&(usk + G::ScalarField::ONE), &s).unwrap(), t);
        let proof = prove_tag(&tag, &usk, &t, &s, b"ctx", &mut rng).unwrap();
        assert!(verify_tag(&tag, &t, &s, b"ctx", &proof));
        assert!(!verify_tag(&tag, &t, &x0, b"ctx", &proof));
        assert!(!verify_tag(&tag, &G::zero(), &s, b"ctx", &proof));
    }

    #[test]
    fn generic_over_the_group() {
        generic_round_trip::<ark_bn254::G1Projective>(0xdd0b);
        generic_round_trip::<ark_bn254::G2Projective>(0xdd0c);
        generic_round_trip::<ark_bls12_381::G2Projective>(0xdd0d);
    }
}
