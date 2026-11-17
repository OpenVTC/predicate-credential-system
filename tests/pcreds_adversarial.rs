//! Adversarial suite of the protocol `Π_PCreds` (paper §5.2,
//! [`predicate_credential_system::pcreds`]) over its pairing-based instantiations (§6: `Σ-PS`
//! and `Σ-BBS` with `Tag_DDH` and `Tag_DY`, over BLS12-381; the credential-free forgeries also
//! over BN254).
//!
//! Every attack below is MOUNTED against the real code and required to fail with the exact error
//! of the check that stops it. Where the honest algorithms refuse to build the offending object,
//! the adversary builds it from public data only: the relation builders of the backend
//! (`PairingBackend::attestation_relation` and the others), the context functions of the
//! protocol (`Protocol::attestation_context` and the others) and the Fiat–Shamir prover of
//! `predicate_credential_system::sigma`. Wherever the point of a test is that ONE check stops a
//! forgery, the test also asserts that the bare Fiat–Shamir verifier ACCEPTS the forgery, so that
//! nothing else stops it. All randomness is seeded (`StdRng::seed_from_u64`, the seed at the call
//! site or derived from it by a recorded constant).
//!
//! # The attacks named by the paper
//!
//! evaluation.tex, §7.3 "Implementation lessons": "Our test suite includes adversarial tests for
//! each of these attacks, namely degenerate shows for `Σ-PS`, a self-attestation, a proof
//! computed over an unrelated context, a helper attempting to identify `Σ-BBS` attesters from its
//! list of issued values `e`, and a bias measurement of the scalar sampler, and requires each to
//! fail."
//!
//! | attack named by the paper | tests |
//! |---|---|
//! | degenerate shows for `Σ-PS` | `a1_ps_degenerate_shows_*`; for `Σ-BBS`: `a1_bbs_*` |
//! | a self-attestation | `self_attestation_*` (what it means without a self-exclusion tag: see there) |
//! | a proof computed over an unrelated context | `contexts_*` |
//! | a helper identifying `Σ-BBS` attesters from its issued `e` (attack A7) | not in this file: `a7_*` in tests/pcreds_soundness.rs |
//! | a bias measurement of the scalar sampler | `scalar_sampler_is_not_the_biased_reduction` |
//!
//! # All attacks of this file
//!
//! | attack | stopped by | tests |
//! |---|---|---|
//! | A1: credential-free attestation or membership proof from a degenerate show | the public checks of `Π_Possess` in the attestation AND membership verifiers | `a1_ps_degenerate_shows_*`, `a1_bbs_degenerate_shows_*`, `public_checks_in_the_attestation_verifier_*` |
//! | `Σ-BBS` under generators with a known relation: one credential, many tags | transparent setup (`from_public_parameters` re-derives `pp`) | `a1_bbs_weak_generators_and_identity_d` |
//! | identity tags and identifiers (`t = 1`, `id = 1`), the zero key of `Tag_DDH` | `t ∈ T` at the attester, the recipient and the helper | `identity_tags_*`, `zero_key_of_tag_ddh_*` |
//! | self-attestation | `π_att` needs a credential; the issued set `I` | `self_attestation_*` |
//! | proofs over another context (`π_id`, `π_att`, `π_iss`, `π_prove`), proofs of one role in another | contexts rebuilt by the verifier, one oracle per proof | `contexts_*` |
//! | A3/A8: one credential behind a tag of another key; W1: weak Fiat–Shamir | the shared variable `usk`; strong Fiat–Shamir | `one_credential_one_tag_*` |
//! | biased scalar sampling (32 bytes mod `r`) | arkworks rejection sampling | `scalar_sampler_is_not_the_biased_reduction` |
//! | components of order 3 (cofactor of `G_1`): one attester counted twice, a second credential for one key | subgroup re-validation in every verifier | `small_order_components_*`, `small_order_forgeries_*` |
//! | off-subgroup points on the wire; unvalidated decoding | validated decoders; verifiers re-validate | `decoders_reject_off_subgroup_points_*` |
//! | malformed proofs; garbage messages | fixed proof shapes, never a panic | `malformed_proofs_*`, `garbage_never_panics_*` |
//! | objects of another deployment or helper | the digest of `pp` in every object; the helper fingerprint | `other_deployments_and_helpers_*` |
//! | `k = 0`; requests with too many attestations | `Policy`; the optional limit before any verification | `zero_threshold_and_the_attestation_limit` |
//! | one attester counted several times | `N''` is a set of tags | `distinct_sources_count_once_*` |
//! | attestations for another identifier | `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`, `π_id`, `π_iss` | `attestations_are_not_transferable_*` |
//! | reuse of attestations (documented behavior) | bound to `(pp, hvk, id_Q)`, not to a session | `attestations_are_standing_endorsements` |
//! | a malicious helper's answer | `Unblind` verifies (fails closed) | `unblind_fails_closed_*` |
//! | inadmissible helper keys | `hvk ∈ V_pp`, checked once (`HelperKey`) | `inadmissible_helper_keys_are_refused` |
//! | `Tag_DY` undefined points; a degenerate RNG | `UndefinedTag`; `Register` samples once (`RegisterFailed`) | `tag_dy_undefined_points`, `register_fails_on_an_undefined_identifier` |
//! | received parameters that are not `Setup(label)` | `from_public_parameters` | `received_parameters_must_be_derived` |
//! | A1 over a second pairing (BN254, with the insecure test oracle) | the same public checks | `a1_over_bn254_*` |
//!
//! # Not ported from the earlier construction (`pcs`)
//!
//! `Σ-EQ` and `Σ-MAC` are not in the paper and were removed (A3, A4, the EQ halves of A1 and
//! of the robustness tests, `eq_refuses_tag_dy`, the designated-verifier flows); the predicate
//! labels `φ`, `EncPred` and the attribute policy `P` (`AllowList`, `PolicyRejected`) do not exist
//! any more; the self-exclusion tag `T_0` (`SelfAttestation`, its substitution attacks, the
//! `T_0 + P_3` attack, which becomes the `id + P_3` attack of `small_order_forgeries_*`) is
//! replaced by the issued set `I`; there is no separate root path
//! (`RootRequest`, `NotARootPredicate`): the helper admits root users by its decision
//! `d = root` on an ordinary request.

#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

mod common;

use ark_bls12_381::{Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_bn254::Bn254;
use ark_ec::{AffineRepr, PrimeGroup, pairing::Pairing};
use ark_ff::{BigInt, BigInteger, Field, One, PrimeField, UniformRand, Zero};
use ark_serialize::{CanonicalDeserialize, Valid};
use common::{
    BBS, BaseTest, Bk, DDH, DY, Deployment, E, G1, G2, Member, PS, random_attestation,
    random_proof, random_request,
};
use predicate_credential_system::{
    Error,
    hash::testing::InsecureExponentHasher,
    kiprf::{self, ProtocolTag},
    pcreds::{
        Attestation, AttestationRequest, AttestationStatement, Backend, Credential,
        CredentialRequest, Decision, EvaluatedRequest, Helper, HelperKey, IssuanceRecord,
        IssuanceState, MembershipProof, Policy, ProofKind, Protocol, PublicParameters, Reply, User,
        pairing::{
            self, BBSCredential, BBSParams, BBSPreCredential, BBSShow, BBSVerificationKey, Base,
            PSPair, PSVerificationKey, PairingBackend, PairingParams, pairing_product_is_identity,
        },
    },
    serialization::{self, WireFormat},
    sigma::{
        FSProof, LinearEquation, LinearRelation, PairingRelation, Witness, commit, fiat_shamir,
        respond,
    },
};
use rand::{CryptoRng, Rng, RngCore, SeedableRng, rngs::StdRng};

/// A copy of an issuance state, through its encoding: `unblind` consumes the state, and the
/// tests try many pre-credentials against one.
fn copy<Bk: Backend>(state: &IssuanceState<Bk>) -> IssuanceState<Bk> {
    IssuanceState::from_bytes(&state.to_bytes().expect("τ encodes")).expect("τ decodes")
}

// ---------------------------------------------------------------------------------------------
// The adversary's tools
// ---------------------------------------------------------------------------------------------

/// The protocol over the base `B` and the tag `T`.
type Pcreds<B, T> = Protocol<Bk<B, T>>;

/// A credentialed user: the user and its credential.
type Holder<'a, B, T> = (&'a User<Bk<B, T>>, &'a Credential<Bk<B, T>>);

/// `P_3 = (0, 2)`, a point of order 3 on `E(F_q): y² = x³ + 4` OUTSIDE the prime-order subgroup
/// `G_1` (the cofactor of BLS12-381 `G_1` is divisible by 3; `(0, ±√b)` are points of order 3
/// of every curve `y² = x³ + b`, its inflection points on the line `x = 0`).
fn p3() -> G1 {
    let p = G1Affine::new_unchecked(Fq::zero(), Fq::from(2u64));
    assert!(p.is_on_curve() && !p.is_in_correct_subgroup_assuming_on_curve());
    let p: G1 = p.into_group();
    assert!(!p.is_zero() && (p + p + p).is_zero(), "P_3 has order 3");
    p
}

/// A point of the curve of `G_2` OUTSIDE the prime-order subgroup `G_2`.
fn g2_off_subgroup() -> G2 {
    let mut x = Fq2::one();
    loop {
        if let Some(p) = G2Affine::get_point_from_x_unchecked(x, false)
            && p.is_on_curve()
            && !p.is_in_correct_subgroup_assuming_on_curve()
        {
            return p.into_group();
        }
        x += Fq2::one();
    }
}

/// Whether the `G_1` equation `eq` holds for the witness `w` (one clause of a relation).
fn holds(eq: &LinearEquation<G1>, w: &[Fr]) -> bool {
    eq.evaluate(w).is_ok_and(|value| value == eq.image_value())
}

/// The helper's issuing key, read back from its encoding `pp-digest ‖ hvk ‖ sk`
/// ([`Helper::to_bytes`]): what a malicious or compromised helper holds.
fn signing_key<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    helper: &Helper<Bk<B, T>>,
) -> B::SigningKey {
    let bytes = helper.to_bytes().expect("encode the helper");
    let mut reader = &bytes[..];
    let _digest = <[u8; 32]>::deserialize_compressed(&mut reader).expect("pp-digest");
    let _vk = B::VerificationKey::deserialize_compressed(&mut reader).expect("hvk");
    B::SigningKey::deserialize_compressed(&mut reader).expect("sk")
}

/// A [`Credential`] holding an ARBITRARY value of the base: the validated decoder accepts every
/// well-formed value (the identity included), so a holder can always present one.
fn decoded_credential<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    inner: &B::Credential,
) -> Credential<Bk<B, T>> {
    let bytes = serialization::to_bytes(inner).expect("encode");
    serialization::from_bytes(&bytes).expect("a well-formed value decodes")
}

/// `AttestationRequest` and `AttestationRequestResponse`: `attester` (holding `cred`) attests
/// for `recipient` under the sub-session `ssid`.
fn attestation_from<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    pcreds: &Pcreds<B, T>,
    hvk: &HelperKey<Bk<B, T>>,
    (attester, cred): Holder<'_, B, T>,
    recipient: &User<Bk<B, T>>,
    ssid: &[u8],
    rng: &mut StdRng,
) -> Attestation<Bk<B, T>> {
    let contact = b"attester@example";
    let request = pcreds
        .request_attestation(hvk, recipient, ssid, contact, rng)
        .expect("attestation request");
    let pending = pcreds
        .receive_attestation_request(hvk, &request, ssid, contact)
        .expect("π_id");
    pcreds
        .attest(hvk, attester, cred, pending, rng)
        .expect("attest")
}

/// The pair `(user, credential)` of a member.
fn of<B: BaseTest, T: ProtocolTag<G1> + 'static>(member: &Member<B, T>) -> Holder<'_, B, T> {
    (&member.user, &member.cred)
}

/// An attestation request of `recipient`, received (`π_id` checked) by the owner of the contact
/// name `owner@example`.
fn pending_for<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    pcreds: &Pcreds<B, T>,
    hvk: &HelperKey<Bk<B, T>>,
    recipient: &User<Bk<B, T>>,
    ssid: &[u8],
    rng: &mut StdRng,
) -> predicate_credential_system::pcreds::PendingAttestation<Bk<B, T>> {
    let request = pcreds
        .request_attestation(hvk, recipient, ssid, b"owner@example", rng)
        .expect("attestation request");
    pcreds
        .receive_attestation_request(hvk, &request, ssid, b"owner@example")
        .expect("π_id")
}

/// An ordinary request without attestations, admitted with `d = root`.
fn admit_root<Bk2: Backend>(
    pcreds: &Protocol<Bk2>,
    helper: &mut Helper<Bk2>,
    hvk: &HelperKey<Bk2>,
    user: &User<Bk2>,
    ssid: &[u8],
    rng: &mut StdRng,
) -> Credential<Bk2> {
    let (message, state) = pcreds
        .request_credential(hvk, user, Vec::new(), ssid, rng)
        .expect("request");
    let evaluated = pcreds
        .evaluate_request(helper, &message, ssid)
        .expect("evaluate");
    let Reply::PreCredential(pre) = pcreds
        .respond(helper, evaluated, Decision::Root, rng)
        .expect("respond")
    else {
        panic!("a root admission of a new identifier issues");
    };
    pcreds
        .unblind(hvk, user, &pre, copy(&state))
        .expect("unblind")
}

/// The helper's evaluation of a credential request of `user` carrying `attestations`.
fn evaluate_with<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    dep: &Deployment<B, T>,
    user: &User<Bk<B, T>>,
    attestations: Vec<Attestation<Bk<B, T>>>,
    ssid: &[u8],
    rng: &mut StdRng,
) -> EvaluatedRequest<Bk<B, T>> {
    let (message, _) = dep
        .pcreds
        .request_credential(&dep.hvk, user, attestations, ssid, rng)
        .expect("request");
    dep.pcreds
        .evaluate_request(&dep.helper, &message, ssid)
        .expect("evaluate")
}

/// A cheating attester: `π_att` for the recipient `id_q`, the show `show` and the tag of the
/// key `witness[0]` at `x_Q`, proven with the witness `witness` (in the variable order of
/// `R_att`: `usk`, then the variables of the base) under exactly the context an honest verifier
/// rebuilds. Asserts that the BARE Fiat–Shamir verifier accepts the proof.
///
/// # Errors
/// [`Error::WitnessDoesNotSatisfyRelation`] if the clauses do not hold for `witness`.
fn cheat_attestation<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    pcreds: &Pcreds<B, T>,
    hvk: &HelperKey<Bk<B, T>>,
    id_q: &G1,
    show: B::Show,
    witness: &[Fr],
    rng: &mut StdRng,
) -> Result<Attestation<Bk<B, T>>, Error> {
    let xq = pcreds.recipient_point(hvk.vk(), id_q)?;
    let tag =
        <Bk<B, T> as Backend>::tag(pcreds.params(), &witness[0], &xq).ok_or(Error::UndefinedTag)?;
    let relation = <Bk<B, T>>::attestation_relation(pcreds.params(), hvk.vk(), &show, &tag, &xq)?;
    let ctx = pcreds.attestation_context(hvk.vk())?;
    let proof = fiat_shamir::prove(&relation, witness, &ctx, rng)?;
    assert!(
        fiat_shamir::verify(&relation, &ctx, &proof),
        "the bare Fiat–Shamir check accepts the forgery"
    );
    Ok(Attestation { tag, show, proof })
}

/// A cheating member: `π_prove` on `message` for the show `show`, proven with `witness` under
/// the context an honest verifier rebuilds. Asserts that the bare Fiat–Shamir verifier accepts.
///
/// # Errors
/// [`Error::WitnessDoesNotSatisfyRelation`] if the clauses do not hold for `witness`.
fn cheat_membership<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    pcreds: &Pcreds<B, T>,
    hvk: &HelperKey<Bk<B, T>>,
    message: &[u8],
    show: B::Show,
    witness: &[Fr],
    rng: &mut StdRng,
) -> Result<MembershipProof<Bk<B, T>>, Error> {
    let relation = <Bk<B, T>>::possession_relation(pcreds.params(), hvk.vk(), &show)?;
    let ctx = pcreds.prove_context(hvk.vk(), message)?;
    let proof = fiat_shamir::prove(&relation, witness, &ctx, rng)?;
    assert!(
        fiat_shamir::verify(&relation, &ctx, &proof),
        "the bare Fiat–Shamir check accepts the forgery"
    );
    Ok(MembershipProof { show, proof })
}

/// A fresh show of `member`'s credential and the honest witness of `R_att` / `R_Possess` for it
/// (`usk`, then the values of the variables of the base).
fn show_and_witness<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    pcreds: &Pcreds<B, T>,
    hvk: &HelperKey<Bk<B, T>>,
    (user, cred): Holder<'_, B, T>,
    rng: &mut StdRng,
) -> (B::Show, Vec<Fr>) {
    let (show, omega) = B::rerand(
        &pcreds.params().base,
        hvk.vk(),
        user.expose_key(),
        cred.as_inner(),
        rng,
    );
    let mut witness = Witness::new();
    witness.push(*user.expose_key());
    B::possession_witness(cred.as_inner(), &omega, &mut witness);
    (show, witness.to_vec())
}

/// Upper bound on the attempts of [`forge_small_order`]. Heuristically (the challenge treated
/// as a random oracle) one attempt succeeds with probability `3^{-m}` for `m` equations with an
/// element outside `G_1`; wherever the function is used `m = 1` (the tag clause), so the bound
/// is reached with probability about `(2/3)^300 < 10^{-52}`.
const FORGE_ATTEMPTS: usize = 300;

/// A Fiat–Shamir proof that the BARE verifier accepts for a statement that is false only by a
/// component of order 3 (a target or a base shifted by `P_3`), with the witness of the
/// unshifted statement. Every element of such an equation is `X + a·P_3` with `X ∈ G_1`, and the
/// endomorphism of the GLV multiplication of arkworks fixes `P_3`, so every multiple the
/// verifier computes is the multiple of `X` plus an element of `⟨P_3⟩`: the verifier's
/// recomputed commitment differs from the prover's `A` by an element of `⟨P_3⟩` that the
/// challenge and the responses determine. The prover commits to `A + g·P_3` in every such
/// component, for a uniform guess `g ∈ {0, 1, 2}`, and keeps the transcript when the bare
/// verifier accepts it. This is what an implementation that skips the subgroup check of a
/// RECEIVED group element accepts.
fn forge_small_order(
    relation: &PairingRelation<E>,
    witness: &[Fr],
    ctx: &[u8],
    rng: &mut StdRng,
) -> FSProof<Fr> {
    let outside = |p: &G1| p.check().is_err();
    let shifted: Vec<bool> = relation
        .g1_linear_equations()
        .iter()
        .map(|eq| {
            eq.image.iter().any(|(element, _)| outside(element))
                || eq.terms.iter().any(|(_, base, _)| outside(base))
        })
        .collect();
    assert!(shifted.contains(&true), "an element outside G_1");
    let shift = p3();
    let multiples = [G1::zero(), shift, shift + shift];
    for _ in 0..FORGE_ATTEMPTS {
        let (mut commitment, state) = commit(relation, rng).expect("commit");
        for (a, _) in commitment.g1.iter_mut().zip(&shifted).filter(|(_, s)| **s) {
            *a += multiples[rng.gen_range(0..3)];
        }
        let challenge = fiat_shamir::challenge(relation, ctx, &commitment).expect("challenge");
        let proof = FSProof {
            challenge,
            responses: respond(state, witness, &challenge).expect("respond"),
        };
        if fiat_shamir::verify(relation, ctx, &proof) {
            return proof;
        }
    }
    panic!("no forgery in {FORGE_ATTEMPTS} attempts");
}

/// The positions at which `needle` occurs in `haystack`.
fn occurrences(haystack: &[u8], needle: &[u8]) -> Vec<usize> {
    haystack
        .windows(needle.len())
        .enumerate()
        .filter(|(_, window)| *window == needle)
        .map(|(at, _)| at)
        .collect()
}

/// `bytes` with the compressed encoding of the `G_1` element `element` (which must occur exactly
/// once) replaced by that of `element + P_3`, which is on the curve and outside `G_1`.
fn shifted_in(bytes: &[u8], element: &G1) -> Vec<u8> {
    let needle = element.to_bytes().expect("encode");
    let at = occurrences(bytes, &needle);
    assert_eq!(at.len(), 1, "the element occurs once in the encoding");
    let mut out = bytes.to_vec();
    out[at[0]..at[0] + needle.len()]
        .copy_from_slice(&(*element + p3()).to_bytes().expect("encode"));
    out
}

// ---------------------------------------------------------------------------------------------
// Per-base hooks
// ---------------------------------------------------------------------------------------------

/// Per-base hooks of this suite beyond [`BaseTest`].
trait AdversarialBase: BaseTest {
    /// Whether the possession CLAUSES contain the helper's key. `Σ-PS`: yes, `X̃` and `Ỹ` are
    /// pairing arguments of its `G_T` clause, so the honest prover refuses a value that is not
    /// a credential of `usk` under `hvk` ([`Error::WitnessDoesNotSatisfyRelation`]). `Σ-BBS`:
    /// no, its clauses are in `G_1` over the generators of `pp_Σ` and the key enters only through
    /// the public pairing check, so the prover answers and every verifier rejects the show
    /// ([`Error::InvalidCredential`]).
    const CLAUSES_BIND_THE_KEY: bool;

    /// What a verifier returns for an honest show presented under ANOTHER admissible key of the
    /// same deployment: `Σ-PS` fails the proof, `Σ-BBS` the public pairing check.
    fn foreign_key_error() -> Error {
        if Self::CLAUSES_BIND_THE_KEY {
            Error::InvalidProof
        } else {
            Error::InvalidCredential
        }
    }

    /// A credential of uniform elements (no signature behind it).
    fn random_credential(rng: &mut StdRng) -> Self::Credential;
    /// A credential whose signature part is the identity.
    fn degenerate_credential(rng: &mut StdRng) -> Self::Credential;
    /// A pre-credential of uniform elements.
    fn random_pre_credential(rng: &mut StdRng) -> Self::PreCredential;
    /// The pre-credential of identity elements (and zero scalars).
    fn identity_pre_credential() -> Self::PreCredential;
    /// The `G_1` elements of a pre-credential.
    fn pre_credential_elements(pre: &Self::PreCredential) -> Vec<G1>;
    /// One copy of `pre` per `G_1` element, with exactly that element shifted by `dg1`.
    fn pre_credential_variants(pre: &Self::PreCredential, dg1: G1) -> Vec<Self::PreCredential>;
    /// One copy of `cred` per `G_1` element, with exactly that element shifted by `dg1`.
    fn credential_variants(cred: &Self::Credential, dg1: G1) -> Vec<Self::Credential>;
    /// The `G_1` elements of a show.
    fn show_elements(show: &Self::Show) -> Vec<G1>;
    /// One copy of `vk` per group element, shifted by `dg1` (`G_1`) or `dg2` (`G_2`).
    fn key_variants(vk: &Self::VerificationKey, dg1: G1, dg2: G2) -> Vec<Self::VerificationKey>;
    /// The pairing equation of `Verify` ALONE, without the validity and non-identity checks.
    fn pairing_equation(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &Fr,
        cred: &Self::Credential,
    ) -> bool;
    /// A show WITHOUT any credential behind it whose possession clauses hold under the key
    /// `key`, with the values of the further variables of the base.
    fn credential_free_show(pp: &Self::Params, key: &Fr, rng: &mut StdRng)
    -> (Self::Show, Vec<Fr>);
}

impl AdversarialBase for PS {
    const CLAUSES_BIND_THE_KEY: bool = true;

    fn random_credential(rng: &mut StdRng) -> PSPair<E> {
        PSPair {
            s1: G1::rand(rng),
            s2: G1::rand(rng),
        }
    }

    fn degenerate_credential(_rng: &mut StdRng) -> PSPair<E> {
        PSPair {
            s1: G1::zero(),
            s2: G1::zero(),
        }
    }

    fn random_pre_credential(rng: &mut StdRng) -> PSPair<E> {
        Self::random_credential(rng)
    }

    fn identity_pre_credential() -> PSPair<E> {
        PSPair {
            s1: G1::zero(),
            s2: G1::zero(),
        }
    }

    fn pre_credential_elements(pre: &PSPair<E>) -> Vec<G1> {
        vec![pre.s1, pre.s2]
    }

    fn pre_credential_variants(pre: &PSPair<E>, dg1: G1) -> Vec<PSPair<E>> {
        <PS as BaseTest>::show_variants(pre, dg1)
    }

    fn credential_variants(cred: &PSPair<E>, dg1: G1) -> Vec<PSPair<E>> {
        <PS as BaseTest>::show_variants(cred, dg1)
    }

    fn show_elements(show: &PSPair<E>) -> Vec<G1> {
        vec![show.s1, show.s2]
    }

    fn key_variants(vk: &PSVerificationKey<E>, dg1: G1, dg2: G2) -> Vec<PSVerificationKey<E>> {
        vec![
            PSVerificationKey {
                x2: vk.x2 + dg2,
                ..vk.clone()
            },
            PSVerificationKey {
                y2: vk.y2 + dg2,
                ..vk.clone()
            },
            PSVerificationKey {
                y1: vk.y1 + dg1,
                ..vk.clone()
            },
        ]
    }

    fn pairing_equation(_pp: &(), vk: &PSVerificationKey<E>, usk: &Fr, cred: &PSPair<E>) -> bool {
        pairing_product_is_identity::<E>(&[
            (cred.s1, vk.x2 + vk.y2 * usk),
            (-cred.s2, G2::generator()),
        ])
    }

    /// `σ' = (1, 1)`: the clause reads `1 = 1` for every `(usk, t)`.
    fn credential_free_show(_pp: &(), _key: &Fr, rng: &mut StdRng) -> (PSPair<E>, Vec<Fr>) {
        (Self::zero_show(), vec![Fr::rand(rng)])
    }
}

impl AdversarialBase for BBS {
    const CLAUSES_BIND_THE_KEY: bool = false;

    fn random_credential(rng: &mut StdRng) -> BBSCredential<E> {
        BBSCredential {
            a: G1::rand(rng),
            e: Fr::rand(rng),
            rho: Fr::rand(rng),
        }
    }

    fn degenerate_credential(rng: &mut StdRng) -> BBSCredential<E> {
        BBSCredential {
            a: G1::zero(),
            e: Fr::rand(rng),
            rho: Fr::rand(rng),
        }
    }

    fn random_pre_credential(rng: &mut StdRng) -> BBSPreCredential<E> {
        BBSPreCredential {
            a: G1::rand(rng),
            e: Fr::rand(rng),
        }
    }

    fn identity_pre_credential() -> BBSPreCredential<E> {
        BBSPreCredential {
            a: G1::zero(),
            e: Fr::zero(),
        }
    }

    fn pre_credential_elements(pre: &BBSPreCredential<E>) -> Vec<G1> {
        vec![pre.a]
    }

    fn pre_credential_variants(pre: &BBSPreCredential<E>, dg1: G1) -> Vec<BBSPreCredential<E>> {
        vec![BBSPreCredential {
            a: pre.a + dg1,
            e: pre.e,
        }]
    }

    fn credential_variants(cred: &BBSCredential<E>, dg1: G1) -> Vec<BBSCredential<E>> {
        vec![BBSCredential {
            a: cred.a + dg1,
            ..cred.clone()
        }]
    }

    fn show_elements(show: &BBSShow<E>) -> Vec<G1> {
        vec![show.a_bar, show.b_bar, show.d]
    }

    fn key_variants(vk: &BBSVerificationKey<E>, _dg1: G1, dg2: G2) -> Vec<BBSVerificationKey<E>> {
        vec![BBSVerificationKey(vk.0 + dg2)]
    }

    fn pairing_equation(
        pp: &BBSParams<E>,
        vk: &BBSVerificationKey<E>,
        usk: &Fr,
        cred: &BBSCredential<E>,
    ) -> bool {
        let g2 = G2::generator();
        pairing_product_is_identity::<E>(&[
            (cred.a, vk.0 + g2 * cred.e),
            (-pp.b(usk, &cred.rho), g2),
        ])
    }

    /// `(1, D, D)` with `D = B(K, ρ)`: the three clauses hold with `r_1 = r_3 = u = 1` and any
    /// `e`, `v` (see [`a1_bbs_degenerate_shows`]).
    fn credential_free_show(
        pp: &BBSParams<E>,
        key: &Fr,
        rng: &mut StdRng,
    ) -> (BBSShow<E>, Vec<Fr>) {
        let rho = Fr::rand(rng);
        let d = pp.b(key, &rho);
        let one = Fr::one();
        let show = BBSShow {
            a_bar: G1::zero(),
            b_bar: d,
            d,
        };
        // (ρ, r_1, e, r_3, u, v)
        (show, vec![rho, one, Fr::rand(rng), one, one, Fr::rand(rng)])
    }
}

// ---------------------------------------------------------------------------------------------
// A1: credential-free attestations and membership proofs from degenerate shows
// ---------------------------------------------------------------------------------------------

/// A1 for `Σ-PS` ("degenerate shows for `Σ-PS`", evaluation.tex). An adversary WITHOUT a
/// credential picks a show for which the possession clause
/// `e(σ'_1, Ỹ)^usk · e(σ'_1, g̃)^t = e(σ'_2, g̃) · e(σ'_1, X̃)^{-1}` is satisfiable under a key of
/// its choice, and proves `R_att` (or `R_Possess`) under exactly the context the verifier
/// rebuilds.
///
/// * `σ' = (1, 1)`: the clause reads `1 = 1` and holds for EVERY `(usk, t)`; under `k` fresh keys
///   the adversary gets `k` pairwise-distinct tags with bare Fiat–Shamir proofs that verify. Only
///   the public check `σ'_1 ≠ 1` of the attestation verifier stops it
///   ([`Error::InvalidCredential`]), and the helper counts none of them.
/// * `σ' = (1, σ'_2)` with `σ'_2 ≠ 1`: the clause reads `1 = e(σ'_2, g̃)` and has no witness;
///   the same public check rejects the show.
/// * `σ' = (σ'_1, 1)` with `σ'_1 ≠ 1` is NOT degenerate: an honest show takes this value with
///   probability `1/p` (for `t = −(x + y·usk)`), and the public check passes. A witness takes
///   the helper's key: a credential-free prover has none ([`Error::InvalidProof`]), the holder of
///   `(x, y)`, who can issue credentials anyway, attests with it under any key.
fn a1_ps_degenerate_shows<T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let dep = Deployment::<PS, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xa1);
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let honest = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[0]),
        &newcomer,
        b"a1",
        &mut rng,
    );
    assert_eq!(
        dep.pcreds
            .check_attestation(&dep.hvk, newcomer.id(), &honest),
        Ok(())
    );
    let identity = PS::zero_show();

    // σ' = (1, 1): k = 2 credential-free attestations under two fresh keys
    let forged: Vec<_> = (0..2)
        .map(|_| {
            let witness = [Fr::rand(&mut rng), Fr::rand(&mut rng)];
            cheat_attestation(
                &dep.pcreds,
                &dep.hvk,
                newcomer.id(),
                identity.clone(),
                &witness,
                &mut rng,
            )
            .expect("1 = 1 holds for every witness")
        })
        .collect();
    assert_ne!(forged[0].tag, forged[1].tag, "two keys, two tags");
    for att in &forged {
        assert_eq!(
            dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), att),
            Err(Error::InvalidCredential)
        );
    }
    // the helper counts none of them, alone or next to an honest attestation
    for (list, counted) in [
        (forged.clone(), 0),
        (vec![honest.clone(), forged[0].clone()], 1),
    ] {
        let evaluated = evaluate_with(&dep, &newcomer, list, b"a1/request", &mut rng);
        assert_eq!(evaluated.tags().len(), counted);
        assert!(!evaluated.is_valid());
    }
    // a membership proof from σ' = (1, 1)
    let proof = cheat_membership(
        &dep.pcreds,
        &dep.hvk,
        b"m",
        identity,
        &[Fr::rand(&mut rng), Fr::rand(&mut rng)],
        &mut rng,
    )
    .unwrap();
    assert_eq!(
        dep.pcreds.check_membership(&dep.hvk, b"m", &proof),
        Err(Error::InvalidCredential)
    );

    // σ' = (1, σ'_2), σ'_2 ≠ 1: no witness, and the same public check
    let half = PSPair::<E> {
        s1: G1::zero(),
        s2: G1::rand(&mut rng),
    };
    assert_eq!(
        cheat_attestation(
            &dep.pcreds,
            &dep.hvk,
            newcomer.id(),
            half.clone(),
            &[Fr::rand(&mut rng), Fr::rand(&mut rng)],
            &mut rng
        )
        .err(),
        Some(Error::WitnessDoesNotSatisfyRelation)
    );
    let att = Attestation {
        show: half,
        ..honest.clone()
    };
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &att),
        Err(Error::InvalidCredential)
    );

    // σ' = (σ'_1, 1), σ'_1 ≠ 1: the public check passes; the witness takes the helper's key
    let other = PSPair::<E> {
        s1: G1::rand(&mut rng),
        s2: G1::zero(),
    };
    assert!(<PS as Base<E>>::possession_public_check(
        &(),
        dep.hvk.vk(),
        &other
    ));
    let key = Fr::rand(&mut rng);
    assert_eq!(
        cheat_attestation(
            &dep.pcreds,
            &dep.hvk,
            newcomer.id(),
            other.clone(),
            &[key, Fr::rand(&mut rng)],
            &mut rng
        )
        .err(),
        Some(Error::WitnessDoesNotSatisfyRelation)
    );
    let att = Attestation {
        show: other.clone(),
        ..honest
    };
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &att),
        Err(Error::InvalidProof)
    );
    // the holder of (x, y) has the witness t = −(x + y·K) for every K
    let (x, y) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
    let g2 = G2::generator();
    let vk = PSVerificationKey::<E> {
        x2: g2 * x,
        y2: g2 * y,
        y1: G1::generator() * y,
    };
    let known = dep.pcreds.helper_key(&vk).expect("an admissible key");
    let att = cheat_attestation(
        &dep.pcreds,
        &known,
        newcomer.id(),
        other,
        &[key, -(x + y * key)],
        &mut rng,
    )
    .expect("the key holder's witness");
    assert_eq!(
        dep.pcreds.check_attestation(&known, newcomer.id(), &att),
        Ok(())
    );
}

#[test]
fn a1_ps_degenerate_shows_ddh() {
    a1_ps_degenerate_shows::<DDH>(b"adv/a1/ps+ddh", 0xad01_0001);
}

#[test]
fn a1_ps_degenerate_shows_dy() {
    a1_ps_degenerate_shows::<DY>(b"adv/a1/ps+dy", 0xad01_0002);
}

/// The first two possession clauses of `Σ-BBS` and the tag clause, WITHOUT the third clause
/// `D = B̄^u Ā^v`: the two-randomizer show of IETF/TZ, which the paper extends ("the third
/// possession clause ... is not part of the IETF/TZ show", base-instantiations.tex). Variables
/// `(usk, ρ, r_1, e, r_3)`.
fn two_clause_relation<T: ProtocolTag<G1> + 'static>(
    params: &PairingParams<E, BBS, T>,
    show: &BBSShow<E>,
    tag: &G1,
    xq: &Fr,
) -> PairingRelation<E> {
    let pp = &params.base;
    let mut relation = PairingRelation::new();
    let usk = relation.alloc_scalar();
    let vars = relation.alloc_scalars(4);
    let (rho, r1, e, r3) = (vars[0], vars[1], vars[2], vars[3]);
    relation
        .add_g1(LinearEquation::new(
            vec![(r1, show.d), (e, -show.a_bar)],
            show.b_bar,
        ))
        .unwrap();
    relation
        .add_g1(LinearEquation::new(
            vec![(r3, show.d), (usk, -pp.hu), (rho, -pp.hr)],
            pp.h0,
        ))
        .unwrap();
    for equation in params.tag.tag_equations(usk, tag, xq) {
        relation.add_g1(equation).unwrap();
    }
    relation
}

/// A1 for `Σ-BBS`. The show `(Ā, B̄, D)` comes with three clauses (box `Σ-BBS`, `Π_Possess`)
/// `B̄ = D^{r_1} Ā^{-e}`, `h_0 = D^{r_3} h_u^{-usk} h_r^{-ρ}`, `D = B̄^u Ā^v`, and the public
/// checks `Ā ≠ 1`, `D ≠ 1`, `e(Ā, X̃) = e(B̄, g̃)`. Variables `(usk, ρ, r_1, e, r_3, u, v)`. With
/// `D = B(K, ρ) = h_0 h_u^K h_r^ρ` for a key `K` of the adversary's choice:
///
/// * `(1, 1, D)`, the credential-free forgery of the earlier construction: the first two clauses
///   hold with `(r_1, r_3) = (0, 1)` and the pairing equation reads `1 = 1`, so against the
///   two-clause show a bare Fiat–Shamir proof verifies and only `Ā ≠ 1` stops it. The third
///   clause reads `D = 1` and has NO witness, and `Ā ≠ 1` rejects the show
///   ([`Error::InvalidCredential`]).
/// * `(1, D, D)`: all three clauses hold (`r_1 = r_3 = u = 1`); the bare proofs verify, under
///   `k` distinct keys. `Ā ≠ 1` and the pairing check reject the show.
/// * `(Ā, D·Ā^{-e}, D)` with `Ā ≠ 1`: the three clauses hold with `(r_1, r_3, u, v) =
///   (1, 1, 1, e)` and both identity checks pass; the pairing check, the one place where the
///   helper's key enters, rejects it (it holds iff `(Ā, e)` is a BBS signature on `(K, ρ)`).
/// * `D = 1` and `(1, 1, 1)`: the second clause reads `h_0 = h_u^{-usk} h_r^{-ρ}`, a relation
///   among the derived generators that nobody knows; no witness, and `D ≠ 1` rejects the show.
fn a1_bbs_degenerate_shows<T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let dep = Deployment::<BBS, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xa1);
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let honest = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[0]),
        &newcomer,
        b"a1",
        &mut rng,
    );
    assert_eq!(
        dep.pcreds
            .check_attestation(&dep.hvk, newcomer.id(), &honest),
        Ok(())
    );
    let params = dep.pcreds.params().clone();
    let vk = dep.hvk.vk().clone();
    let g2 = G2::generator();
    let pairing_check = |show: &BBSShow<E>| {
        pairing_product_is_identity::<E>(&[(show.a_bar, vk.0), (-show.b_bar, g2)])
    };
    let (zero, one, identity) = (Fr::zero(), Fr::one(), G1::zero());
    let xq = dep.pcreds.recipient_point(&vk, newcomer.id()).unwrap();
    let ctx = dep.pcreds.attestation_context(&vk).unwrap();
    let (key, rho, e) = (Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng));
    let d = params.base.b(&key, &rho);
    let tag = <Bk<BBS, T> as Backend>::tag(&params, &key, &xq).unwrap();
    let attestation_with = |show: BBSShow<E>, rng: &mut StdRng| Attestation::<Bk<BBS, T>> {
        tag,
        show,
        proof: random_proof(<Bk<BBS, T>>::responses(ProofKind::Attestation), rng),
    };

    // (1, 1, D): clauses 1, 2 and the tag clause hold, clause 3 reads D = 1
    let old = BBSShow::<E> {
        a_bar: identity,
        b_bar: identity,
        d,
    };
    assert!(pairing_check(&old), "the pairing equation reads 1 = 1");
    let relation = <Bk<BBS, T>>::attestation_relation(&params, &vk, &old, &tag, &xq).unwrap();
    let [first, second, third, tag_clause] = &relation.g1_linear_equations()[..] else {
        panic!("three possession clauses and the tag clause");
    };
    for _ in 0..4 {
        let (u, v) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
        let w = [key, rho, zero, e, one, u, v];
        assert!(holds(first, &w) && holds(second, &w) && holds(tag_clause, &w));
        assert!(!holds(third, &w), "D = B̄^u Ā^v = 1 for every (u, v)");
        assert!(!relation.is_satisfied_by(&w));
        assert_eq!(
            cheat_attestation(
                &dep.pcreds,
                &dep.hvk,
                newcomer.id(),
                old.clone(),
                &w,
                &mut rng
            )
            .err(),
            Some(Error::WitnessDoesNotSatisfyRelation)
        );
    }
    // against the two-clause show the forgery goes through the bare Fiat–Shamir check
    let two = two_clause_relation(&params, &old, &tag, &xq);
    let w = [key, rho, zero, e, one];
    let proof = fiat_shamir::prove(&two, &w, &ctx, &mut rng).expect("the two clauses hold");
    assert!(fiat_shamir::verify(&two, &ctx, &proof));
    // the protocol rejects the show, whatever the proof
    assert_eq!(
        dep.pcreds.check_attestation(
            &dep.hvk,
            newcomer.id(),
            &attestation_with(old.clone(), &mut rng)
        ),
        Err(Error::InvalidCredential)
    );
    let att = Attestation {
        tag,
        show: old,
        proof,
    };
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &att),
        Err(Error::InvalidCredential)
    );

    // (1, D, D): all three clauses hold; Ā ≠ 1 and the pairing check reject it
    let mut forged = Vec::new();
    for _ in 0..2 {
        let key = Fr::rand(&mut rng);
        let (show, extra) = BBS::credential_free_show(&params.base, &key, &mut rng);
        assert!(show.a_bar.is_zero() && show.b_bar == show.d && !pairing_check(&show));
        let witness: Vec<Fr> = core::iter::once(key).chain(extra).collect();
        let att = cheat_attestation(
            &dep.pcreds,
            &dep.hvk,
            newcomer.id(),
            show.clone(),
            &witness,
            &mut rng,
        )
        .expect("the three clauses hold");
        assert_eq!(
            dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &att),
            Err(Error::InvalidCredential)
        );
        let proof = cheat_membership(&dep.pcreds, &dep.hvk, b"m", show, &witness, &mut rng)
            .expect("the three clauses hold");
        assert_eq!(
            dep.pcreds.check_membership(&dep.hvk, b"m", &proof),
            Err(Error::InvalidCredential)
        );
        forged.push(att);
    }
    assert_ne!(forged[0].tag, forged[1].tag, "two keys, two tags");
    let evaluated = evaluate_with(&dep, &newcomer, forged, b"a1/request", &mut rng);
    assert!(evaluated.tags().is_empty() && !evaluated.is_valid());

    // (Ā, D·Ā^{-e}, D), Ā ≠ 1: only the pairing check rejects it
    let a_bar = G1::rand(&mut rng);
    let general = BBSShow::<E> {
        a_bar,
        b_bar: d - a_bar * e,
        d,
    };
    assert!(!general.a_bar.is_zero() && !general.d.is_zero() && !pairing_check(&general));
    let att = cheat_attestation(
        &dep.pcreds,
        &dep.hvk,
        newcomer.id(),
        general,
        &[key, rho, one, e, one, one, e],
        &mut rng,
    )
    .expect("the three clauses hold");
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &att),
        Err(Error::InvalidCredential)
    );

    // D = 1, and (1, 1, 1): the second clause needs a relation among the generators
    for show in [
        BBSShow::<E> {
            a_bar,
            b_bar: -(a_bar * e),
            d: identity,
        },
        BBSShow::<E> {
            a_bar: identity,
            b_bar: identity,
            d: identity,
        },
    ] {
        let relation = <Bk<BBS, T>>::attestation_relation(&params, &vk, &show, &tag, &xq).unwrap();
        let equations = relation.g1_linear_equations();
        for _ in 0..4 {
            let u = Fr::rand(&mut rng);
            let w = [
                key,
                Fr::rand(&mut rng),
                Fr::rand(&mut rng),
                e,
                Fr::rand(&mut rng),
                u,
                e * u,
            ];
            assert!(holds(&equations[0], &w) && holds(&equations[2], &w));
            assert!(!holds(&equations[1], &w), "h_0 = h_u^{{-usk}} h_r^{{-ρ}}");
        }
        assert_eq!(
            dep.pcreds.check_attestation(
                &dep.hvk,
                newcomer.id(),
                &attestation_with(show, &mut rng)
            ),
            Err(Error::InvalidCredential)
        );
    }
}

#[test]
fn a1_bbs_degenerate_shows_ddh() {
    a1_bbs_degenerate_shows::<DDH>(b"adv/a1/bbs+ddh", 0xad01_0003);
}

#[test]
fn a1_bbs_degenerate_shows_dy() {
    a1_bbs_degenerate_shows::<DY>(b"adv/a1/bbs+dy", 0xad01_0004);
}

/// Why `Σ-BBS` needs DERIVED generators, and what guards them (base-instantiations.tex: the
/// generators are hashed "so that no party (in particular not the key holder) knows a
/// discrete-logarithm relation among them"). Under generators `h_i = g_1^{a_i}` with KNOWN
/// `a_i`, which [`Protocol::setup_with_params`] accepts because they are well formed (its
/// WARNING says so), the second clause `h_0 = D^{r_3} h_u^{-usk} h_r^{-ρ}` has the degenerate
/// witness `r_3 = 0`, `ρ = −(a_0 + a_1 K)/a_2` for EVERY key `K`, and every public check passes:
///
/// * the holder of ONE honestly issued credential attests with `k = 3` pairwise-distinct tags,
///   and the helper's policy accepts a newcomer backed by it alone: the attack works;
/// * the key holder (`x` known) with such a relation attests without any credential through
///   `(Ā, Ā^x, 1)`, which only `D ≠ 1` rejects, and through `(Ā, Ā^x, Ā^δ)` with
///   `(r_1, r_3) = (0, 0)`, which nothing rejects: `D ≠ 1` is checked because the box requires
///   it, soundness does not rest on it;
/// * the defense: a party that RECEIVES these parameters re-derives them from the label
///   ([`Protocol::from_public_parameters`]) and refuses them ([`Error::InvalidPublicParameters`]);
///   under the derived generators the same witnesses do not satisfy the clause.
#[test]
fn a1_bbs_weak_generators_and_identity_d() {
    type Weak = Pcreds<BBS, DDH>;
    let label = b"adv/a1/bbs-weak-generators";
    let mut rng = StdRng::seed_from_u64(0xad01_0005);
    let a = [Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng)];
    assert!(a.iter().all(|a| !a.is_zero()));
    let g1 = G1::generator();
    let weak = BBSParams::<E> {
        h0: g1 * a[0],
        hu: g1 * a[1],
        hr: g1 * a[2],
    };
    let identity_base = |key: Fr| -(a[0] + a[1] * key) * a[2].inverse().unwrap();
    let pcreds = Weak::setup_with_params(
        label,
        PairingParams {
            base: weak.clone(),
            tag: DDH::setup(label).unwrap(),
        },
    )
    .expect("well-formed generators pass the checks of Setup");
    let mut helper = pcreds.helper_keygen(Policy::threshold(3).unwrap(), &mut rng);
    let hvk = pcreds.helper_key(helper.key().vk()).unwrap();
    let member = pcreds.register(&hvk, &mut rng).unwrap();
    let cred = admit_root(&pcreds, &mut helper, &hvk, &member, b"root", &mut rng);
    let newcomer = pcreds.register(&hvk, &mut rng).unwrap();

    // ONE credential, three attestations with distinct tags: (usk, ρ, r_1, e, r_3, u, v) =
    // (K, ρ_K, r_1, e, 0, u, v) next to an honest show
    let mut attestations = Vec::new();
    for _ in 0..3 {
        let key = Fr::rand(&mut rng);
        let rho = identity_base(key);
        assert!(weak.b(&key, &rho).is_zero());
        let (show, honest) = show_and_witness(&pcreds, &hvk, (&member, &cred), &mut rng);
        let w = [
            key,
            rho,
            honest[2],
            honest[3],
            Fr::zero(),
            honest[5],
            honest[6],
        ];
        let att = cheat_attestation(&pcreds, &hvk, newcomer.id(), show, &w, &mut rng)
            .expect("r_3 = 0 with B(K, ρ_K) = 1");
        assert_eq!(
            pcreds.check_attestation(&hvk, newcomer.id(), &att),
            Ok(()),
            "nothing public is wrong"
        );
        attestations.push(att);
    }
    let (message, _) = pcreds
        .request_credential(&hvk, &newcomer, attestations, b"sybil", &mut rng)
        .unwrap();
    let evaluated = pcreds
        .evaluate_request(&helper, &message, b"sybil")
        .unwrap();
    assert_eq!(evaluated.tags().len(), 3);
    assert!(
        evaluated.is_valid(),
        "under weak generators one credential passes for three attesters"
    );
    assert!(matches!(
        pcreds.respond(&mut helper, evaluated, Decision::Policy, &mut rng),
        Ok(Reply::PreCredential(_))
    ));

    // the key holder with a generator relation: D = 1, and D = Ā^δ
    let x = Fr::rand(&mut rng);
    let known = pcreds
        .helper_key(&BBSVerificationKey(G2::generator() * x))
        .expect("V_pp = G_2");
    let (key, a_bar, u, delta) = (
        Fr::rand(&mut rng),
        G1::rand(&mut rng),
        Fr::rand(&mut rng),
        Fr::rand(&mut rng),
    );
    let rho = identity_base(key);
    let att = cheat_attestation(
        &pcreds,
        &known,
        newcomer.id(),
        BBSShow {
            a_bar,
            b_bar: a_bar * x,
            d: G1::zero(),
        },
        &[
            key,
            rho,
            Fr::rand(&mut rng),
            -x,
            Fr::rand(&mut rng),
            u,
            -(x * u),
        ],
        &mut rng,
    )
    .expect("e = −x and B(K, ρ_K) = 1");
    assert_eq!(
        pcreds.check_attestation(&known, newcomer.id(), &att),
        Err(Error::InvalidCredential),
        "only D ≠ 1 rejects"
    );
    let att = cheat_attestation(
        &pcreds,
        &known,
        newcomer.id(),
        BBSShow {
            a_bar,
            b_bar: a_bar * x,
            d: a_bar * delta,
        },
        &[key, rho, Fr::zero(), -x, Fr::zero(), u, delta - x * u],
        &mut rng,
    )
    .expect("(r_1, r_3) = (0, 0)");
    assert_eq!(
        pcreds.check_attestation(&known, newcomer.id(), &att),
        Ok(()),
        "D ≠ 1 is not load-bearing"
    );

    // the defense: received parameters are re-derived from their label
    assert_eq!(
        Weak::from_public_parameters(pcreds.public_parameters().clone()).err(),
        Some(Error::InvalidPublicParameters(
            "the parameters are not derived from the label"
        ))
    );
    let derived = Weak::setup(label).unwrap();
    assert_ne!(derived.params().base, weak);
    for key in [*member.expose_key(), Fr::rand(&mut rng)] {
        assert!(!derived.params().base.b(&key, &identity_base(key)).is_zero());
    }
}

// ---------------------------------------------------------------------------------------------
// Identity tags and identifiers
// ---------------------------------------------------------------------------------------------

/// `t ∈ T` (`T = G_1 \ {1}` for both tags): the identity is neither an attestation tag nor an
/// identifier, at every party that receives one ([`Error::InvalidTag`]): the recipient and the
/// helper for `t`, the attester, the recipient and the helper for `id_Q`. A request whose
/// attestation carries `t = 1` (with `π_iss` over exactly that list) counts nothing.
fn identity_tags<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let dep = Deployment::<B, T>::new(label, 1, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0x1d);
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let att = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[0]),
        &newcomer,
        b"t",
        &mut rng,
    );
    let identity = G1::zero();

    // t = 1
    let bad = Attestation {
        tag: identity,
        ..att.clone()
    };
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &bad),
        Err(Error::InvalidTag)
    );
    let evaluated = evaluate_with(&dep, &newcomer, vec![bad], b"t/request", &mut rng);
    assert!(evaluated.tags().is_empty() && !evaluated.is_valid());

    // id = 1 at the attester, the recipient and the helper
    let request = dep
        .pcreds
        .request_attestation(&dep.hvk, &newcomer, b"s", b"c", &mut rng)
        .unwrap();
    let bad = AttestationRequest {
        id: identity,
        ..request
    };
    assert_eq!(
        dep.pcreds
            .receive_attestation_request(&dep.hvk, &bad, b"s", b"c")
            .err(),
        Some(Error::InvalidTag)
    );
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, &identity, &att),
        Err(Error::InvalidTag)
    );
    let (message, _) = dep
        .pcreds
        .request_credential(&dep.hvk, &newcomer, vec![att], b"id", &mut rng)
        .unwrap();
    let bad = CredentialRequest {
        id: identity,
        ..message
    };
    assert_eq!(
        dep.pcreds.evaluate_request(&dep.helper, &bad, b"id").err(),
        Some(Error::InvalidTag)
    );
}

#[test]
fn identity_tags_ps_ddh() {
    identity_tags::<PS, DDH>(b"adv/identity/ps+ddh", 0xad1d_0001);
}

#[test]
fn identity_tags_ps_dy() {
    identity_tags::<PS, DY>(b"adv/identity/ps+dy", 0xad1d_0002);
}

#[test]
fn identity_tags_bbs_ddh() {
    identity_tags::<BBS, DDH>(b"adv/identity/bbs+ddh", 0xad1d_0003);
}

#[test]
fn identity_tags_bbs_dy() {
    identity_tags::<BBS, DY>(b"adv/identity/bbs+dy", 0xad1d_0004);
}

/// Where `t ∈ T` is the ONLY obstacle: the key `0` of `Tag_DDH`, outside its key space
/// `Z_p \ {0}`, would have the tag `htag(x)^0 = 1` at every point, and the tag clause
/// `t = htag(x)^K` holds for `(t, K) = (1, 0)`. `Register` never produces it
/// ([`Error::UndefinedTag`]). An adversary proves the relations with the witness `0` anyway:
///
/// * `π_id` for `id = 1` verifies under the bare check; the attester refuses `id = 1`;
/// * `π_iss` for `id = 1` (a root-admissible request for the key `0`) verifies under the bare
///   check; the helper refuses `id = 1` before anything else;
/// * with a credential on `usk = 0`, issued by a raw `BlindIssue` outside the protocol, the honest
///   prover of `R_att` produces an attestation with `t = 1` whose show passes the public checks
///   and whose proof verifies under the bare check; only `t ∈ T` rejects it.
///
/// (`Tag_DY` has no such key: `t = 1` makes its clause `t^K = g_1 t^{-x}` read `1 = g_1`.)
fn zero_key_of_tag_ddh<B: AdversarialBase>(label: &[u8], seed: u64) {
    let dep = Deployment::<B, DDH>::new(label, 1, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0x2e70);
    let (zero, identity) = (Fr::zero(), G1::zero());
    assert_eq!(
        dep.pcreds.user(&dep.hvk, zero).err(),
        Some(Error::UndefinedTag)
    );
    let params = dep.pcreds.params().clone();
    let vk = dep.hvk.vk().clone();
    let x0 = *dep.hvk.identifier_point();

    // π_id for id = 1
    let relation = <Bk<B, DDH>>::identifier_relation(&params, &identity, &x0).unwrap();
    let ctx = dep.pcreds.identifier_context(b"s", b"c");
    let proof = fiat_shamir::prove(&relation, &[zero], &ctx, &mut rng).expect("1 = htag(x_0)^0");
    assert!(fiat_shamir::verify(&relation, &ctx, &proof));
    let request = AttestationRequest::<Bk<B, DDH>> {
        id: identity,
        proof,
    };
    assert_eq!(
        dep.pcreds
            .receive_attestation_request(&dep.hvk, &request, b"s", b"c")
            .err(),
        Some(Error::InvalidTag)
    );

    // π_iss for id = 1
    let (request, tau) =
        <Bk<B, DDH> as Backend>::prepare_issue(&params, &vk, &zero, &mut rng).unwrap();
    let relation = <Bk<B, DDH>>::issuance_relation(&params, &vk, &request, &identity, &x0).unwrap();
    let ctx = dep.pcreds.issuance_context(&vk, b"r", &[]).unwrap();
    let proof = fiat_shamir::prove(&relation, &[zero, tau], &ctx, &mut rng)
        .expect("Ĉ opens to usk = 0, and 1 = htag(x_0)^0");
    assert!(fiat_shamir::verify(&relation, &ctx, &proof));
    let message = CredentialRequest {
        id: identity,
        attestations: Vec::new(),
        request: request.clone(),
        proof,
    };
    assert_eq!(
        dep.pcreds
            .evaluate_request(&dep.helper, &message, b"r")
            .err(),
        Some(Error::InvalidTag)
    );

    // t = 1 from a credential on usk = 0
    let sk = signing_key(&dep.helper);
    let pre = <Bk<B, DDH> as Backend>::blind_issue(&params, &sk, &request, &mut rng).unwrap();
    let cred = <Bk<B, DDH> as Backend>::unblind(&params, &vk, &zero, &pre, &tau)
        .expect("a valid credential on usk = 0");
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let xq = dep.pcreds.recipient_point(&vk, newcomer.id()).unwrap();
    let ctx = dep.pcreds.attestation_context(&vk).unwrap();
    let statement = AttestationStatement {
        vk: &vk,
        tag: &identity,
        point: &xq,
    };
    let (show, proof) = <Bk<B, DDH> as Backend>::prove_attestation(
        &params, &statement, &zero, &cred, &ctx, &mut rng,
    )
    .expect("R_att holds: the tag clause reads 1 = htag(x_Q)^0");
    let relation = <Bk<B, DDH>>::attestation_relation(&params, &vk, &show, &identity, &xq).unwrap();
    assert!(fiat_shamir::verify(&relation, &ctx, &proof));
    assert!(B::possession_public_check(&params.base, &vk, &show));
    let att = Attestation {
        tag: identity,
        show,
        proof,
    };
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &att),
        Err(Error::InvalidTag)
    );
    let evaluated = evaluate_with(&dep, &newcomer, vec![att], b"t", &mut rng);
    assert!(evaluated.tags().is_empty());
}

#[test]
fn zero_key_of_tag_ddh_ps() {
    zero_key_of_tag_ddh::<PS>(b"adv/zero-key/ps", 0xad0c_0001);
}

#[test]
fn zero_key_of_tag_ddh_bbs() {
    zero_key_of_tag_ddh::<BBS>(b"adv/zero-key/bbs", 0xad0c_0002);
}

// ---------------------------------------------------------------------------------------------
// Self-attestation
// ---------------------------------------------------------------------------------------------

/// Self-attestation under the protocol of the paper ("a self-attestation", evaluation.tex).
///
/// The earlier construction carried a self-exclusion tag `T_0` in every issuance proof and
/// refused a request whose attestations contained it. The protocol has none: in `F_PCreds` a
/// participant may answer an attestation request that reaches it through its own contact name,
/// with itself as the credentialed source, and the threshold policy `Pol_k` counts the sources
/// `E` of the request. What stops a self-attestation from being an attack is that
///
/// * only a credentialed user can attest at all: `π_att` proves possession of a credential under
///   `hvk`, and the attester's tag key is the certified key (shared variable `usk`), so a user
///   without a credential (holding garbage, a degenerate value or another helper's credential)
///   is refused by the prover or rejected by every verifier; and
/// * a credentialed user already is in the helper's issued set `I`: the helper answers its
///   request `issued`, whether `d = policy` or `d = root`, and `I` does not grow.
///
/// So a valid self-attestation exists (the protocol accepts it, like `F_PCreds`) and obtains
/// nothing.
fn self_attestation<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0x5e1f);
    let issued = dep.helper.store().len();

    // a credentialed member attests for itself, through its own contact name
    let own = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[0]),
        &dep.members[0].user,
        b"self",
        &mut rng,
    );
    assert_eq!(
        dep.pcreds
            .check_attestation(&dep.hvk, dep.members[0].user.id(), &own),
        Ok(()),
        "a valid attestation from a credentialed source"
    );
    let other = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[1]),
        &dep.members[0].user,
        b"other",
        &mut rng,
    );
    for decision in [Decision::Policy, Decision::Root] {
        let (message, _) = dep
            .pcreds
            .request_credential(
                &dep.hvk,
                &dep.members[0].user,
                vec![own.clone(), other.clone()],
                b"self/request",
                &mut rng,
            )
            .unwrap();
        let evaluated = dep
            .pcreds
            .evaluate_request(&dep.helper, &message, b"self/request")
            .unwrap();
        assert_eq!(evaluated.tags().len(), 2, "the self-attestation counts");
        assert!(evaluated.is_valid());
        assert_eq!(
            dep.pcreds
                .respond(&mut dep.helper, evaluated, decision, &mut rng),
            Ok(Reply::Issued),
            "id_Q ∈ I"
        );
    }
    assert_eq!(dep.helper.store().len(), issued);

    // a user without a credential cannot attest, for itself or anybody
    let q = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();

    let mut other_helper = dep
        .pcreds
        .helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let other_hvk = dep.pcreds.helper_key(other_helper.key().vk()).unwrap();
    // q registers with the other helper too, reusing its key, and is admitted there
    let q_there = dep.pcreds.register_reusing(&other_hvk, &q).unwrap();
    let foreign = admit_root(
        &dep.pcreds,
        &mut other_helper,
        &other_hvk,
        &q_there,
        b"q/elsewhere",
        &mut rng,
    );
    let garbage = decoded_credential::<B, T>(&B::random_credential(&mut rng));
    assert_eq!(
        dep.pcreds
            .credential(&dep.hvk, &q, garbage.as_inner().clone())
            .err(),
        Some(Error::InvalidCredential)
    );
    for cred in [&garbage, &foreign] {
        assert!(!dep.pcreds.verify_credential(&dep.hvk, &q, cred));
        let pending = pending_for(&dep.pcreds, &dep.hvk, &q, b"q/self", &mut rng);
        match dep.pcreds.attest(&dep.hvk, &q, cred, pending, &mut rng) {
            Err(e) => {
                assert!(B::CLAUSES_BIND_THE_KEY);
                assert_eq!(e, Error::WitnessDoesNotSatisfyRelation);
            }
            Ok(att) => {
                assert!(!B::CLAUSES_BIND_THE_KEY);
                assert_eq!(
                    dep.pcreds.check_attestation(&dep.hvk, q.id(), &att),
                    Err(Error::InvalidCredential)
                );
            }
        }
    }
    // a degenerate credential: the honest prover answers (its clauses hold), verifiers reject
    let degenerate = decoded_credential::<B, T>(&B::degenerate_credential(&mut rng));
    let pending = pending_for(&dep.pcreds, &dep.hvk, &q, b"q/self", &mut rng);
    let fake = dep
        .pcreds
        .attest(&dep.hvk, &q, &degenerate, pending, &mut rng)
        .expect("the clauses of a degenerate show hold");
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, q.id(), &fake),
        Err(Error::InvalidCredential)
    );
    // next to one genuine attestation it does not reach k = 2
    let genuine = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[0]),
        &q,
        b"q/genuine",
        &mut rng,
    );
    let (message, _) = dep
        .pcreds
        .request_credential(&dep.hvk, &q, vec![fake, genuine], b"q", &mut rng)
        .unwrap();
    let evaluated = dep
        .pcreds
        .evaluate_request(&dep.helper, &message, b"q")
        .unwrap();
    assert_eq!(evaluated.tags().len(), 1);
    assert_eq!(
        dep.pcreds
            .respond(&mut dep.helper, evaluated, Decision::Policy, &mut rng),
        Ok(Reply::Fail)
    );
    assert_eq!(dep.helper.store().len(), issued);
}

#[test]
fn self_attestation_ps_ddh() {
    self_attestation::<PS, DDH>(b"adv/self/ps+ddh", 0xad5e_0001);
}

#[test]
fn self_attestation_ps_dy() {
    self_attestation::<PS, DY>(b"adv/self/ps+dy", 0xad5e_0002);
}

#[test]
fn self_attestation_bbs_ddh() {
    self_attestation::<BBS, DDH>(b"adv/self/bbs+ddh", 0xad5e_0003);
}

#[test]
fn self_attestation_bbs_dy() {
    self_attestation::<BBS, DY>(b"adv/self/bbs+dy", 0xad5e_0004);
}

// ---------------------------------------------------------------------------------------------
// Proofs over unrelated contexts
// ---------------------------------------------------------------------------------------------

/// "A proof computed over an unrelated context" (evaluation.tex; "the verifier must rebuild
/// the proof context"). Every verifier rebuilds the context of its proof from public data, so
/// a proof made for one statement or context is worthless for another ([`Error::InvalidProof`]
/// unless an earlier public check fires):
///
/// * `π_id` under another `ssid`, another contact name, in another deployment, for another
///   identifier, or over a context of the prover's choosing;
/// * `π_att` for another recipient, under another helper key of the deployment, in another
///   deployment under the SAME key, over a context of the prover's choosing; and an
///   attestation's `(σ*, π_att)` as a membership proof and a membership proof as an attestation
///   (one oracle per proof: both have `1 + POSSESSION_VARIABLES` responses);
/// * `π_iss` under another `ssid`, another attestation list (reordered, shortened, one replaced
///   by an equivalent attestation, empty), another helper key, another deployment under the SAME
///   key, another `Ĉ`, another identifier, or over a context of the prover's choosing;
/// * `π_prove` for another message, another helper key, another deployment under the same key,
///   over a context of the prover's choosing, or with the show of another proof.
fn contexts<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xc7);
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let params = pcreds.params().clone();
    let vk = hvk.vk().clone();
    let x0 = *hvk.identifier_point();
    let there = Pcreds::<B, T>::setup(&[label, b"/elsewhere"].concat()).unwrap();
    let there_hvk = there
        .helper_key(&vk)
        .expect("the same key, admissible there");
    let other_helper = pcreds.helper_keygen(Policy::threshold(2).unwrap(), &mut rng);
    let other_hvk = other_helper.key().clone();
    let newcomer = pcreds.register(hvk, &mut rng).unwrap();
    let bystander = pcreds.register(hvk, &mut rng).unwrap();
    let chosen = b"a context of the prover's choosing";

    // π_id
    let (ssid, contact) = (b"att".as_slice(), b"member-0@example".as_slice());
    let request = pcreds
        .request_attestation(hvk, &newcomer, ssid, contact, &mut rng)
        .unwrap();
    assert!(pcreds.verify_attestation_request(hvk, &request, ssid, contact));
    for (s, c) in [(b"other".as_slice(), contact), (ssid, b"other@example")] {
        assert_eq!(
            pcreds
                .receive_attestation_request(hvk, &request, s, c)
                .err(),
            Some(Error::InvalidProof)
        );
    }
    assert_eq!(
        there
            .receive_attestation_request(&there_hvk, &request, ssid, contact)
            .err(),
        Some(Error::InvalidProof)
    );
    // under another helper key of the deployment, π_id is a proof at another identifier point
    assert_eq!(
        pcreds
            .receive_attestation_request(&other_hvk, &request, ssid, contact)
            .err(),
        Some(Error::InvalidProof)
    );
    let stolen = AttestationRequest {
        id: *bystander.id(),
        ..request.clone()
    };
    assert_eq!(
        pcreds
            .receive_attestation_request(hvk, &stolen, ssid, contact)
            .err(),
        Some(Error::InvalidProof)
    );
    let relation = <Bk<B, T>>::identifier_relation(&params, newcomer.id(), &x0).unwrap();
    let proof = fiat_shamir::prove(&relation, &[*newcomer.expose_key()], chosen, &mut rng).unwrap();
    assert!(fiat_shamir::verify(&relation, chosen, &proof));
    let bogus = AttestationRequest {
        id: *newcomer.id(),
        proof,
    };
    assert_eq!(
        pcreds
            .receive_attestation_request(hvk, &bogus, ssid, contact)
            .err(),
        Some(Error::InvalidProof)
    );

    // π_att
    let att0 = attestation_from(pcreds, hvk, of(&dep.members[0]), &newcomer, b"a0", &mut rng);
    let att1 = attestation_from(pcreds, hvk, of(&dep.members[1]), &newcomer, b"a1", &mut rng);
    assert_eq!(pcreds.check_attestation(hvk, newcomer.id(), &att0), Ok(()));
    assert_eq!(
        pcreds.check_attestation(hvk, bystander.id(), &att0),
        Err(Error::InvalidProof)
    );
    assert_eq!(
        pcreds.check_attestation(&other_hvk, newcomer.id(), &att0),
        Err(B::foreign_key_error())
    );
    assert_eq!(
        there.check_attestation(&there_hvk, newcomer.id(), &att0),
        Err(Error::InvalidProof)
    );
    let (show, witness) = show_and_witness(pcreds, hvk, of(&dep.members[0]), &mut rng);
    let xq = pcreds.recipient_point(&vk, newcomer.id()).unwrap();
    let relation = <Bk<B, T>>::attestation_relation(&params, &vk, &show, &att0.tag, &xq).unwrap();
    for ctx in [
        chosen.as_slice(),
        &pcreds.identifier_context(b"a0", b"attester@example"),
    ] {
        let proof = fiat_shamir::prove(&relation, &witness, ctx, &mut rng).unwrap();
        assert!(fiat_shamir::verify(&relation, ctx, &proof));
        let bogus = Attestation {
            tag: att0.tag,
            show: show.clone(),
            proof,
        };
        assert_eq!(
            pcreds.check_attestation(hvk, newcomer.id(), &bogus),
            Err(Error::InvalidProof)
        );
    }
    let membership = pcreds
        .prove(
            hvk,
            &dep.members[0].user,
            &dep.members[0].cred,
            b"message",
            &mut rng,
        )
        .unwrap();
    let as_membership = MembershipProof {
        show: att0.show.clone(),
        proof: att0.proof.clone(),
    };
    assert_eq!(
        pcreds.check_membership(hvk, b"message", &as_membership),
        Err(Error::InvalidProof)
    );
    let as_attestation = Attestation {
        tag: att0.tag,
        show: membership.show.clone(),
        proof: membership.proof.clone(),
    };
    assert_eq!(
        pcreds.check_attestation(hvk, newcomer.id(), &as_attestation),
        Err(Error::InvalidProof)
    );

    // π_iss
    let atts = vec![att0.clone(), att1.clone()];
    let (message, state) = pcreds
        .request_credential(hvk, &newcomer, atts.clone(), b"iss", &mut rng)
        .unwrap();
    let evaluated = pcreds
        .evaluate_request(&dep.helper, &message, b"iss")
        .unwrap();
    assert!(evaluated.is_valid(), "control");
    assert_eq!(
        pcreds
            .evaluate_request(&dep.helper, &message, b"other")
            .err(),
        Some(Error::InvalidProof)
    );
    let refreshed = attestation_from(
        pcreds,
        hvk,
        of(&dep.members[1]),
        &newcomer,
        b"a1'",
        &mut rng,
    );
    assert_eq!(refreshed.tag, att1.tag);
    for list in [
        vec![att1.clone(), att0.clone()],
        vec![att0.clone()],
        vec![att0.clone(), refreshed],
        Vec::new(),
    ] {
        let swapped = CredentialRequest {
            attestations: list,
            ..message.clone()
        };
        assert_eq!(
            pcreds.evaluate_request(&dep.helper, &swapped, b"iss").err(),
            Some(Error::InvalidProof)
        );
    }
    assert_eq!(
        pcreds
            .evaluate_request(&other_helper, &message, b"iss")
            .err(),
        Some(Error::InvalidProof)
    );
    // a helper of the other deployment holding the same key cannot exist (`restore_helper` and
    // the evaluator refuse it, `other_deployments_and_helpers_*`), so its verifier runs here
    // through the backend, on the context it would rebuild
    let statement = predicate_credential_system::pcreds::IssuanceStatement {
        vk: &vk,
        request: &message.request,
        id: &message.id,
        x0: there_hvk.identifier_point(),
    };
    let there_ctx = there.issuance_context(&vk, b"iss", &atts).unwrap();
    assert_eq!(
        <Bk<B, T> as Backend>::check_issuance_proof(
            there.params(),
            &statement,
            &there_ctx,
            &message.proof
        ),
        Err(Error::InvalidProof)
    );
    let (fresh, _) = pcreds
        .request_credential(hvk, &newcomer, atts.clone(), b"iss", &mut rng)
        .unwrap();
    assert_ne!(fresh.request, message.request);
    for swapped in [
        CredentialRequest {
            request: fresh.request,
            ..message.clone()
        },
        CredentialRequest {
            id: *bystander.id(),
            ..message.clone()
        },
    ] {
        assert_eq!(
            pcreds.evaluate_request(&dep.helper, &swapped, b"iss").err(),
            Some(Error::InvalidProof)
        );
    }
    let relation =
        <Bk<B, T>>::issuance_relation(&params, &vk, &message.request, newcomer.id(), &x0).unwrap();
    let witness = [*newcomer.expose_key(), *state.expose_tape()];
    let proof = fiat_shamir::prove(&relation, &witness, chosen, &mut rng).unwrap();
    assert!(fiat_shamir::verify(&relation, chosen, &proof));
    let bogus = CredentialRequest {
        proof,
        ..message.clone()
    };
    assert_eq!(
        pcreds.evaluate_request(&dep.helper, &bogus, b"iss").err(),
        Some(Error::InvalidProof)
    );

    // π_prove
    assert!(pcreds.verify(hvk, b"message", &membership), "control");
    assert_eq!(
        pcreds.check_membership(hvk, b"another message", &membership),
        Err(Error::InvalidProof)
    );
    assert_eq!(
        pcreds.check_membership(&other_hvk, b"message", &membership),
        Err(B::foreign_key_error())
    );
    assert_eq!(
        there.check_membership(&there_hvk, b"message", &membership),
        Err(Error::InvalidProof)
    );
    let (show, witness) = show_and_witness(pcreds, hvk, of(&dep.members[1]), &mut rng);
    let relation = <Bk<B, T>>::possession_relation(&params, &vk, &show).unwrap();
    let proof = fiat_shamir::prove(&relation, &witness, chosen, &mut rng).unwrap();
    assert!(fiat_shamir::verify(&relation, chosen, &proof));
    let bogus = MembershipProof {
        show: show.clone(),
        proof,
    };
    assert_eq!(
        pcreds.check_membership(hvk, b"message", &bogus),
        Err(Error::InvalidProof)
    );
    let swapped = MembershipProof {
        show,
        proof: membership.proof.clone(),
    };
    assert_eq!(
        pcreds.check_membership(hvk, b"message", &swapped),
        Err(Error::InvalidProof)
    );
}

#[test]
fn contexts_ps_ddh() {
    contexts::<PS, DDH>(b"adv/ctx/ps+ddh", 0xadc7_0001);
}

#[test]
fn contexts_ps_dy() {
    contexts::<PS, DY>(b"adv/ctx/ps+dy", 0xadc7_0002);
}

#[test]
fn contexts_bbs_ddh() {
    contexts::<BBS, DDH>(b"adv/ctx/bbs+ddh", 0xadc7_0003);
}

#[test]
fn contexts_bbs_dy() {
    contexts::<BBS, DY>(b"adv/ctx/bbs+dy", 0xadc7_0004);
}

// ---------------------------------------------------------------------------------------------
// One credential, one tag (A3/A8) and weak Fiat–Shamir (W1)
// ---------------------------------------------------------------------------------------------

/// A3/A8: one credential cannot back a tag under ANOTHER key. `R_att` shares the variable
/// `usk` between the possession clauses and the tag clause, so next to an honest show a tag
/// under another key has no witness: the credential's key fails the tag clause, the tag's key
/// fails the possession clauses (`Σ-PS`: the `G_T` clause; `Σ-BBS`: the second clause opens
/// `D` to the certified key), and the prover refuses. A holder that claims another key for its
/// credential all the way through `attest` is refused by the prover (`Σ-PS`) or produces a show
/// that fails the public pairing check (`Σ-BBS`).
///
/// W1/W1b (weak Fiat–Shamir, the break of the reference implementations): the `(c, z)` of an
/// honest attestation, reused for a tag chosen after the challenge, or with another show, does
/// not verify: the challenge absorbs the whole statement.
fn one_credential_one_tag<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
) {
    let dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xa8);
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let params = pcreds.params().clone();
    let vk = hvk.vk().clone();
    let newcomer = pcreds.register(hvk, &mut rng).unwrap();
    let xq = pcreds.recipient_point(&vk, newcomer.id()).unwrap();
    let ctx = pcreds.attestation_context(&vk).unwrap();
    let tag_of = |key: &Fr| <Bk<B, T> as Backend>::tag(&params, key, &xq).unwrap();

    let (show, witness) = show_and_witness(pcreds, hvk, of(&dep.members[0]), &mut rng);
    let own = tag_of(&witness[0]);
    assert!(
        <Bk<B, T>>::attestation_relation(&params, &vk, &show, &own, &xq)
            .unwrap()
            .is_satisfied_by(&witness)
    );
    for _ in 0..3 {
        let key = Fr::rand(&mut rng);
        let relation =
            <Bk<B, T>>::attestation_relation(&params, &vk, &show, &tag_of(&key), &xq).unwrap();
        let mut claimed = witness.clone();
        claimed[0] = key;
        for w in [&witness, &claimed] {
            assert!(!relation.is_satisfied_by(w));
            assert_eq!(
                fiat_shamir::prove(&relation, w, &ctx, &mut rng).err(),
                Some(Error::WitnessDoesNotSatisfyRelation)
            );
        }
    }
    // the credential claimed for another key through `attest`
    let impostor = pcreds.user(hvk, Fr::rand(&mut rng)).unwrap();
    let pending = pending_for(pcreds, hvk, &newcomer, b"impostor", &mut rng);
    match pcreds.attest(hvk, &impostor, &dep.members[0].cred, pending, &mut rng) {
        Err(e) => {
            assert!(B::CLAUSES_BIND_THE_KEY);
            assert_eq!(e, Error::WitnessDoesNotSatisfyRelation);
        }
        Ok(att) => {
            assert!(!B::CLAUSES_BIND_THE_KEY);
            assert_eq!(att.tag, tag_of(impostor.expose_key()));
            assert_eq!(
                pcreds.check_attestation(hvk, newcomer.id(), &att),
                Err(Error::InvalidCredential)
            );
        }
    }

    // W1: the honest (c, z), retargeted to tags chosen after the challenge
    let honest = attestation_from(pcreds, hvk, of(&dep.members[0]), &newcomer, b"w1", &mut rng);
    assert_eq!(
        pcreds.check_attestation(hvk, newcomer.id(), &honest),
        Ok(())
    );
    for _ in 0..3 {
        let att = Attestation {
            tag: tag_of(&Fr::rand(&mut rng)),
            ..honest.clone()
        };
        assert_eq!(
            pcreds.check_attestation(hvk, newcomer.id(), &att),
            Err(Error::InvalidProof)
        );
    }
    // W1b: the show swapped for another member's, or for a fresh show of the same credential
    let other = attestation_from(
        pcreds,
        hvk,
        of(&dep.members[1]),
        &newcomer,
        b"w1b",
        &mut rng,
    );
    let again = attestation_from(
        pcreds,
        hvk,
        of(&dep.members[0]),
        &newcomer,
        b"w1b'",
        &mut rng,
    );
    assert_eq!(again.tag, honest.tag, "the tag is deterministic");
    assert_ne!(again.show, honest.show, "the show is fresh");
    for show in [other.show, again.show] {
        let att = Attestation {
            show,
            ..honest.clone()
        };
        assert_eq!(
            pcreds.check_attestation(hvk, newcomer.id(), &att),
            Err(Error::InvalidProof)
        );
    }
}

#[test]
fn one_credential_one_tag_ps_ddh() {
    one_credential_one_tag::<PS, DDH>(b"adv/a8/ps+ddh", 0xada8_0001);
}

#[test]
fn one_credential_one_tag_ps_dy() {
    one_credential_one_tag::<PS, DY>(b"adv/a8/ps+dy", 0xada8_0002);
}

#[test]
fn one_credential_one_tag_bbs_ddh() {
    one_credential_one_tag::<BBS, DDH>(b"adv/a8/bbs+ddh", 0xada8_0003);
}

#[test]
fn one_credential_one_tag_bbs_dy() {
    one_credential_one_tag::<BBS, DY>(b"adv/a8/bbs+dy", 0xada8_0004);
}

// ---------------------------------------------------------------------------------------------
// The scalar sampler
// ---------------------------------------------------------------------------------------------

/// The value of a 256-bit integer as an `f64` (relative error below `2^{-52}`).
fn to_f64(x: &BigInt<4>) -> f64 {
    x.0.iter().rev().fold(0.0, |acc, &limb| {
        acc * 18_446_744_073_709_551_616.0 + limb as f64
    })
}

/// The Kullback–Leibler divergence `KL(a ‖ b)` of two Bernoulli distributions.
fn kl(a: f64, b: f64) -> f64 {
    a * (a / b).ln() + (1.0 - a) * ((1.0 - a) / (1.0 - b)).ln()
}

/// Number of samples per sampler in [`scalar_sampler_is_not_the_biased_reduction`].
const BIAS_SAMPLES: usize = 5000;

/// "A bias measurement of the scalar sampler" (evaluation.tex: "scalar sampling should reduce 64
/// uniform bytes modulo the group order, not 32: for the scalar field of BLS12-381,
/// `⌊2^256/r⌋ = 2`, so a 32-byte reduction makes the lowest 20.8% of `Z_r` half again as likely
/// as the rest, and that generator supplies `usk`, the issuance randomness, and every blinding
/// factor").
///
/// With `c = 2^256 mod r` (computed exactly below), the 32-byte reduction maps 3 inputs to every
/// value below `c` and 2 to every other value, so a value falls below `c` with probability
/// `p_1 = 3c/2^256 = 3c/(2r + c) ≈ 0.2829`; under a uniform sampler with `p_0 = c/r ≈ 0.2083`.
/// The fraction `p̂` of `N = 5000` samples below `c` is the optimal test statistic (the
/// likelihood ratio of the two distributions is constant on `[0, c)` and on `[c, r)`). A
/// sampler is accepted as uniform iff `|p̂ − p_0| ≤ δ = (p_1 − p_0)/2`. By the Chernoff bound,
/// a uniform sampler fails with probability at most
/// `exp(−N·KL(p_0 + δ ‖ p_0)) + exp(−N·KL(p_0 − δ ‖ p_0))`, and the biased one passes with
/// probability at most `exp(−N·KL(p_1 − δ ‖ p_1))`; both bounds are computed below and asserted
/// to be below `10^{-8}` and `10^{-7}` (for `N = 5000` they are `1.8·10^{-9}` and `2.1·10^{-8}`;
/// `δ` is `6.5` standard deviations of `p̂` under `p_0`). The test is seeded, so its outcome is
/// fixed; the bounds are the probability that an unlucky seed would have failed it.
///
/// Measured: arkworks `UniformRand` for `Fr` (rejection sampling on the Montgomery limbs),
/// `usk` from `Register` for both tags, `τ` from `request_credential`
/// ([`IssuanceState::expose_tape`]), and, as the control that the test detects what it is for,
/// the biased reduction of 32 uniform bytes.
#[test]
fn scalar_sampler_is_not_the_biased_reduction() {
    // r, and c = 2^256 mod r = 2^256 − 2r
    let r = Fr::MODULUS;
    let mut two_r = r;
    assert!(!two_r.mul2(), "2r < 2^256");
    let mut c = BigInt::<4>::zero();
    assert!(c.sub_with_borrow(&two_r), "0 − 2r wraps to 2^256 − 2r");
    assert!(c < r, "⌊2^256/r⌋ = 2");
    assert_eq!(c, Fr::from(2u64).pow([256u64]).into_bigint());
    let p0 = to_f64(&c) / to_f64(&r);
    let p1 = 3.0 * to_f64(&c) / 2f64.powi(256);
    assert!((p0 - 0.208).abs() < 0.001, "the paper's 20.8%: {p0}");
    let delta = (p1 - p0) / 2.0;
    let n = BIAS_SAMPLES as f64;
    let false_failure = (-n * kl(p0 + delta, p0)).exp() + (-n * kl(p0 - delta, p0)).exp();
    let miss = (-n * kl(p1 - delta, p1)).exp();
    assert!(false_failure < 1e-8, "false-failure bound {false_failure}");
    assert!(miss < 1e-7, "miss bound {miss}");
    let below = |samples: &[Fr]| {
        assert_eq!(samples.len(), BIAS_SAMPLES);
        samples.iter().filter(|x| x.into_bigint() < c).count() as f64 / n
    };
    let uniform = |what: &str, samples: &[Fr]| {
        let p = below(samples);
        eprintln!("{what}: {p:.4} of {BIAS_SAMPLES} below c (p_0 = {p0:.4} ± {delta:.4})");
        assert!(
            (p - p0).abs() <= delta,
            "{what}: {p} of the samples below c, expected {p0} ± {delta}"
        );
    };

    let mut rng = StdRng::seed_from_u64(0xad5a_0001);
    let samples: Vec<Fr> = (0..BIAS_SAMPLES).map(|_| Fr::rand(&mut rng)).collect();
    uniform("UniformRand", &samples);

    let pcreds = Pcreds::<PS, DDH>::setup(b"adv/sampler/ddh").unwrap();
    let mut rng = StdRng::seed_from_u64(0xad5a_0002);
    let hvk = pcreds
        .helper_keygen(Policy::threshold(1).unwrap(), &mut rng)
        .key()
        .clone();
    let samples: Vec<Fr> = (0..BIAS_SAMPLES)
        .map(|_| *pcreds.register(&hvk, &mut rng).unwrap().expose_key())
        .collect();
    uniform("usk (Register, Tag_DDH)", &samples);

    let pcreds = Pcreds::<PS, DY>::setup(b"adv/sampler/dy").unwrap();
    let mut rng = StdRng::seed_from_u64(0xad5a_0003);
    let helper = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let hvk = helper.key().clone();
    let samples: Vec<Fr> = (0..BIAS_SAMPLES)
        .map(|_| *pcreds.register(&hvk, &mut rng).unwrap().expose_key())
        .collect();
    uniform("usk (Register, Tag_DY)", &samples);

    let user = pcreds.register(&hvk, &mut rng).unwrap();
    let samples: Vec<Fr> = (0..BIAS_SAMPLES)
        .map(|_| {
            let (_, state) = pcreds
                .request_credential(helper.key(), &user, Vec::new(), b"tau", &mut rng)
                .unwrap();
            *state.expose_tape()
        })
        .collect();
    uniform("τ (request_credential)", &samples);

    // control: the biased reduction of 32 uniform bytes is detected
    let mut rng = StdRng::seed_from_u64(0xad5a_0004);
    let samples: Vec<Fr> = (0..BIAS_SAMPLES)
        .map(|_| {
            let mut bytes = [0u8; 32];
            rng.fill_bytes(&mut bytes);
            Fr::from_le_bytes_mod_order(&bytes)
        })
        .collect();
    let p = below(&samples);
    eprintln!("32-byte reduction: {p:.4} of {BIAS_SAMPLES} below c (p_1 = {p1:.4})");
    assert!(
        p > p0 + delta,
        "the biased sampler is detected: {p} of the samples below c, expected about {p1}"
    );
}

// ---------------------------------------------------------------------------------------------
// Components of small order
// ---------------------------------------------------------------------------------------------

/// Received objects with a component of order 3. The cofactor of BLS12-381 `G_1` is divisible
/// by 3, so a point `P + P_3` is on the curve but outside `G_1`; pairing equations are blind to
/// it, and a Schnorr clause whose statement carries it is forgeable without a witness, in about
/// one attempt in three (`small_order_forgeries_*`). Every verifier re-validates what it receives
/// ([`Error::InvalidGroupElement`] naming the argument), whatever way the object was built:
///
/// * `id_Q + P_3` at the attester, the recipient and the helper (`"id_Q"`);
/// * `t + P_3` at the recipient (`"t"`) and at the helper, which never counts it as a distinct
///   tag, whatever the order (π_iss is made over exactly the list that contains it);
/// * every element of a show, in attestations and membership proofs (`"σ*"`);
/// * the request `Ĉ + P_3` at the helper (`"Ĉ"`);
/// * every element of `hvk` (`"hvk"`) and of a pre-credential (`"σ̂"`);
/// * a credential with a shifted element is refused ([`Error::InvalidCredential`]) although the
///   pairing equation of `Verify` alone ACCEPTS it: the subgroup check of `Verify` is
///   load-bearing.
fn small_order_components<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
) {
    let mut dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0x3);
    let shift = p3();
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let att0 = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[0]),
        &newcomer,
        b"a0",
        &mut rng,
    );
    let att1 = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[1]),
        &newcomer,
        b"a1",
        &mut rng,
    );
    let request = dep
        .pcreds
        .request_attestation(&dep.hvk, &newcomer, b"s", b"c", &mut rng)
        .unwrap();
    let (message, _) = dep
        .pcreds
        .request_credential(
            &dep.hvk,
            &newcomer,
            vec![att0.clone(), att1],
            b"iss",
            &mut rng,
        )
        .unwrap();
    let membership = dep
        .pcreds
        .prove(
            &dep.hvk,
            &dep.members[0].user,
            &dep.members[0].cred,
            b"m",
            &mut rng,
        )
        .unwrap();

    // id_Q
    let bad = AttestationRequest {
        id: request.id + shift,
        ..request
    };
    assert_eq!(
        dep.pcreds
            .receive_attestation_request(&dep.hvk, &bad, b"s", b"c")
            .err(),
        Some(Error::InvalidGroupElement("id_Q"))
    );
    assert_eq!(
        dep.pcreds
            .check_attestation(&dep.hvk, &(*newcomer.id() + shift), &att0),
        Err(Error::InvalidGroupElement("id_Q"))
    );
    let bad = CredentialRequest {
        id: message.id + shift,
        ..message.clone()
    };
    assert_eq!(
        dep.pcreds.evaluate_request(&dep.helper, &bad, b"iss").err(),
        Some(Error::InvalidGroupElement("id_Q"))
    );

    // t: rejected, and never a distinct tag
    let shifted = Attestation {
        tag: att0.tag + shift,
        ..att0.clone()
    };
    assert_eq!(
        dep.pcreds
            .check_attestation(&dep.hvk, newcomer.id(), &shifted),
        Err(Error::InvalidGroupElement("t"))
    );
    for list in [
        vec![att0.clone(), shifted.clone()],
        vec![shifted.clone(), att0.clone()],
    ] {
        let evaluated = evaluate_with(&dep, &newcomer, list, b"t", &mut rng);
        assert_eq!(evaluated.tags(), &[att0.tag]);
        assert!(!evaluated.is_valid());
    }

    // every element of a show
    for show in B::show_variants(&att0.show, shift) {
        let bad = Attestation {
            show,
            ..att0.clone()
        };
        assert_eq!(
            dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &bad),
            Err(Error::InvalidGroupElement("σ*"))
        );
    }
    for show in B::show_variants(&membership.show, shift) {
        let bad = MembershipProof {
            show,
            ..membership.clone()
        };
        assert_eq!(
            dep.pcreds.check_membership(&dep.hvk, b"m", &bad),
            Err(Error::InvalidGroupElement("σ*"))
        );
    }

    // Ĉ
    let mut bad = message.clone();
    bad.request.0 += shift;
    assert_eq!(
        dep.pcreds.evaluate_request(&dep.helper, &bad, b"iss").err(),
        Some(Error::InvalidGroupElement("Ĉ"))
    );

    // hvk
    for vk in B::key_variants(dep.hvk.vk(), shift, g2_off_subgroup()) {
        assert_eq!(
            dep.pcreds.helper_key(&vk).err(),
            Some(Error::InvalidGroupElement("hvk"))
        );
    }

    // σ̂, then the credential
    let user = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let (root, state) = dep
        .pcreds
        .request_credential(&dep.hvk, &user, Vec::new(), b"root", &mut rng)
        .unwrap();
    let evaluated = dep
        .pcreds
        .evaluate_request(&dep.helper, &root, b"root")
        .unwrap();
    let Reply::PreCredential(pre) = dep
        .pcreds
        .respond(&mut dep.helper, evaluated, Decision::Root, &mut rng)
        .unwrap()
    else {
        panic!("a root admission of a new identifier issues");
    };
    for bad in B::pre_credential_variants(&pre, shift) {
        assert_eq!(
            dep.pcreds
                .unblind(&dep.hvk, &user, &bad, copy(&state))
                .err(),
            Some(Error::InvalidGroupElement("σ̂"))
        );
    }
    let cred = dep
        .pcreds
        .unblind(&dep.hvk, &user, &pre, copy(&state))
        .unwrap();
    let base = &dep.pcreds.params().base;
    for bad in B::credential_variants(cred.as_inner(), shift) {
        assert!(
            B::pairing_equation(base, dep.hvk.vk(), user.expose_key(), &bad),
            "the pairing equation is blind to the component of order 3"
        );
        assert_eq!(
            dep.pcreds.credential(&dep.hvk, &user, bad.clone()).err(),
            Some(Error::InvalidCredential)
        );
        assert!(!dep.pcreds.verify_credential(
            &dep.hvk,
            &user,
            &decoded_credential_unchecked::<B, T>(&bad)
        ));
    }
}

/// A [`Credential`] holding `inner`, decoded WITHOUT validation (the validated decoder refuses a
/// point outside `G_1`).
fn decoded_credential_unchecked<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    inner: &B::Credential,
) -> Credential<Bk<B, T>> {
    let bytes = serialization::to_bytes(inner).expect("encode");
    assert!(serialization::from_bytes::<Credential<Bk<B, T>>>(&bytes).is_err());
    Credential::deserialize_compressed_unchecked(&bytes[..]).expect("unvalidated decoding")
}

#[test]
fn small_order_components_ps_ddh() {
    small_order_components::<PS, DDH>(b"adv/p3/ps+ddh", 0xad03_0001);
}

#[test]
fn small_order_components_ps_dy() {
    small_order_components::<PS, DY>(b"adv/p3/ps+dy", 0xad03_0002);
}

#[test]
fn small_order_components_bbs_ddh() {
    small_order_components::<BBS, DDH>(b"adv/p3/bbs+ddh", 0xad03_0003);
}

#[test]
fn small_order_components_bbs_dy() {
    small_order_components::<BBS, DY>(b"adv/p3/bbs+dy", 0xad03_0004);
}

/// The attacks the subgroup checks exist for, turned around (the `small_subgroup_*` regressions
/// of the earlier construction, adapted to the protocol). Each forgery passes the BARE
/// Fiat–Shamir check ([`forge_small_order`]) and is rejected only by the re-validation of the
/// received element:
///
/// * ONE attester, two "distinct" tags: its honest attestation `t` and a second one with the tag
///   `t + P_3` and a proof forged for the shifted statement. Accepted, it would count one source
///   twice; the helper counts it once, the recipient rejects it (`"t"`), the decoders refuse it.
/// * A second credential for ONE key: a credentialed member asks again under `id + P_3`, which is
///   not in the issued set `I`, with `π_iss` (and `π_id` towards an attester) forged for the
///   shifted identifier. Accepted, a root admission would issue to `usk` twice; the helper and
///   the attester refuse `id + P_3` (`"id_Q"`) before any proof is looked at.
fn small_order_forgeries<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
) {
    let dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0x33);
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let params = pcreds.params().clone();
    let vk = hvk.vk().clone();
    let shift = p3();
    let newcomer = pcreds.register(hvk, &mut rng).unwrap();
    let honest = attestation_from(pcreds, hvk, of(&dep.members[0]), &newcomer, b"a0", &mut rng);

    // one attester counted twice
    let xq = pcreds.recipient_point(&vk, newcomer.id()).unwrap();
    let ctx = pcreds.attestation_context(&vk).unwrap();
    let (show, witness) = show_and_witness(pcreds, hvk, of(&dep.members[0]), &mut rng);
    let tag = honest.tag + shift;
    let relation = <Bk<B, T>>::attestation_relation(&params, &vk, &show, &tag, &xq).unwrap();
    let proof = forge_small_order(&relation, &witness, &ctx, &mut rng);
    assert!(
        fiat_shamir::verify(&relation, &ctx, &proof),
        "the bare check accepts"
    );
    let second = Attestation { tag, show, proof };
    assert_eq!(
        pcreds.check_attestation(hvk, newcomer.id(), &second),
        Err(Error::InvalidGroupElement("t"))
    );
    let evaluated = evaluate_with(
        &dep,
        &newcomer,
        vec![honest.clone(), second.clone()],
        b"x2",
        &mut rng,
    );
    assert_eq!(evaluated.tags(), &[honest.tag], "one source");
    assert!(!evaluated.is_valid());
    assert!(matches!(
        Attestation::<Bk<B, T>>::from_compact_bytes(&second.to_compact_bytes().unwrap()),
        Err(Error::Serialization(_))
    ));
    assert!(matches!(
        serialization::from_bytes::<Attestation<Bk<B, T>>>(
            &serialization::to_bytes(&second).unwrap()
        ),
        Err(Error::Serialization(_))
    ));

    // a second credential for one key
    let member = &dep.members[0].user;
    let usk = *member.expose_key();
    let x0 = *hvk.identifier_point();
    let id = *member.id() + shift;
    let (request, tau) =
        <Bk<B, T> as Backend>::prepare_issue(&params, &vk, &usk, &mut rng).unwrap();
    let relation = <Bk<B, T>>::issuance_relation(&params, &vk, &request, &id, &x0).unwrap();
    let ctx = pcreds.issuance_context(&vk, b"again", &[]).unwrap();
    let proof = forge_small_order(&relation, &[usk, tau], &ctx, &mut rng);
    assert!(
        fiat_shamir::verify(&relation, &ctx, &proof),
        "the bare check accepts"
    );
    let message = CredentialRequest {
        id,
        attestations: Vec::new(),
        request,
        proof,
    };
    assert_eq!(
        pcreds
            .evaluate_request(&dep.helper, &message, b"again")
            .err(),
        Some(Error::InvalidGroupElement("id_Q"))
    );
    let relation = <Bk<B, T>>::identifier_relation(&params, &id, &x0).unwrap();
    let ctx = pcreds.identifier_context(b"s", b"c");
    let proof = forge_small_order(&relation, &[usk], &ctx, &mut rng);
    assert!(
        fiat_shamir::verify(&relation, &ctx, &proof),
        "the bare check accepts"
    );
    assert_eq!(
        pcreds
            .receive_attestation_request(hvk, &AttestationRequest { id, proof }, b"s", b"c")
            .err(),
        Some(Error::InvalidGroupElement("id_Q"))
    );
}

#[test]
fn small_order_forgeries_ps_ddh() {
    small_order_forgeries::<PS, DDH>(b"adv/p3-forge/ps+ddh", 0xad33_0001);
}

#[test]
fn small_order_forgeries_ps_dy() {
    small_order_forgeries::<PS, DY>(b"adv/p3-forge/ps+dy", 0xad33_0002);
}

#[test]
fn small_order_forgeries_bbs_ddh() {
    small_order_forgeries::<BBS, DDH>(b"adv/p3-forge/bbs+ddh", 0xad33_0003);
}

#[test]
fn small_order_forgeries_bbs_dy() {
    small_order_forgeries::<BBS, DY>(b"adv/p3-forge/bbs+dy", 0xad33_0004);
}

/// Off-subgroup points on the wire. In the compact encoding (`pcreds::codec`) and in the derived
/// canonical encoding ([`WireFormat`]) of every message, each `G_1` element in turn is replaced
/// by itself plus `P_3`: the validated decoders refuse it
/// ([`Error::Serialization`]). Decoded WITHOUT validation (`deserialize_compressed_unchecked`),
/// the same bytes give an object that the verifier refuses with [`Error::InvalidGroupElement`]
/// (or, for an element of an attestation inside a credential request, [`Error::InvalidProof`]:
/// `π_iss` is bound to the attestations as they were, and the helper verifies it first).
fn decoders_reject_off_subgroup_points<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
) {
    type Request<B, T> = AttestationRequest<Bk<B, T>>;
    let mut dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xdec);
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let request = dep
        .pcreds
        .request_attestation(&dep.hvk, &newcomer, b"s", b"c", &mut rng)
        .unwrap();
    let att = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[0]),
        &newcomer,
        b"a0",
        &mut rng,
    );
    let att1 = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[1]),
        &newcomer,
        b"a1",
        &mut rng,
    );
    let (message, _) = dep
        .pcreds
        .request_credential(
            &dep.hvk,
            &newcomer,
            vec![att.clone(), att1],
            b"iss",
            &mut rng,
        )
        .unwrap();
    let membership = dep
        .pcreds
        .prove(
            &dep.hvk,
            &dep.members[0].user,
            &dep.members[0].cred,
            b"m",
            &mut rng,
        )
        .unwrap();
    let user = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let (root, state) = dep
        .pcreds
        .request_credential(&dep.hvk, &user, Vec::new(), b"root", &mut rng)
        .unwrap();
    let evaluated = dep
        .pcreds
        .evaluate_request(&dep.helper, &root, b"root")
        .unwrap();
    let reply = dep
        .pcreds
        .respond(&mut dep.helper, evaluated, Decision::Root, &mut rng)
        .unwrap();
    let Reply::PreCredential(pre) = reply.clone() else {
        panic!("a root admission of a new identifier issues");
    };
    let refused = |result: Result<(), Error>| matches!(result, Err(Error::Serialization(_)));

    // AttestationRequest: id_Q
    let compact = shifted_in(&request.to_compact_bytes().unwrap(), &request.id);
    assert!(refused(
        Request::<B, T>::from_compact_bytes(&compact).map(drop)
    ));
    let canonical = shifted_in(&serialization::to_bytes(&request).unwrap(), &request.id);
    assert!(refused(
        serialization::from_bytes::<Request<B, T>>(&canonical).map(drop)
    ));
    let unchecked = Request::<B, T>::deserialize_compressed_unchecked(&canonical[..]).unwrap();
    assert_eq!(
        dep.pcreds
            .receive_attestation_request(&dep.hvk, &unchecked, b"s", b"c")
            .err(),
        Some(Error::InvalidGroupElement("id_Q"))
    );

    // Attestation: t and every element of the show
    let mut elements = vec![(att.tag, "t")];
    elements.extend(B::show_elements(&att.show).into_iter().map(|p| (p, "σ*")));
    for (element, what) in &elements {
        let compact = shifted_in(&att.to_compact_bytes().unwrap(), element);
        assert!(refused(
            Attestation::<Bk<B, T>>::from_compact_bytes(&compact).map(drop)
        ));
        let canonical = shifted_in(&serialization::to_bytes(&att).unwrap(), element);
        assert!(refused(
            serialization::from_bytes::<Attestation<Bk<B, T>>>(&canonical).map(drop)
        ));
        let unchecked =
            Attestation::<Bk<B, T>>::deserialize_compressed_unchecked(&canonical[..]).unwrap();
        assert_eq!(
            dep.pcreds
                .check_attestation(&dep.hvk, newcomer.id(), &unchecked),
            Err(Error::InvalidGroupElement(what))
        );
    }

    // CredentialRequest: id_Q, every element of every attestation, Ĉ
    let mut elements = vec![(message.id, Error::InvalidGroupElement("id_Q"))];
    for a in &message.attestations {
        elements.push((a.tag, Error::InvalidProof));
        for p in B::show_elements(&a.show) {
            elements.push((p, Error::InvalidProof));
        }
    }
    elements.push((message.request.0, Error::InvalidGroupElement("Ĉ")));
    for (element, expected) in &elements {
        let compact = shifted_in(&message.to_compact_bytes().unwrap(), element);
        assert!(refused(
            CredentialRequest::<Bk<B, T>>::from_compact_bytes(&compact).map(drop)
        ));
        let canonical = shifted_in(&serialization::to_bytes(&message).unwrap(), element);
        assert!(refused(
            serialization::from_bytes::<CredentialRequest<Bk<B, T>>>(&canonical).map(drop)
        ));
        let unchecked =
            CredentialRequest::<Bk<B, T>>::deserialize_compressed_unchecked(&canonical[..])
                .unwrap();
        assert_eq!(
            dep.pcreds
                .evaluate_request(&dep.helper, &unchecked, b"iss")
                .err()
                .as_ref(),
            Some(expected)
        );
    }

    // MembershipProof: every element of the show
    for element in B::show_elements(&membership.show) {
        let compact = shifted_in(&membership.to_compact_bytes().unwrap(), &element);
        assert!(refused(
            MembershipProof::<Bk<B, T>>::from_compact_bytes(&compact).map(drop)
        ));
        let canonical = shifted_in(&serialization::to_bytes(&membership).unwrap(), &element);
        assert!(refused(
            serialization::from_bytes::<MembershipProof<Bk<B, T>>>(&canonical).map(drop)
        ));
        let unchecked =
            MembershipProof::<Bk<B, T>>::deserialize_compressed_unchecked(&canonical[..]).unwrap();
        assert_eq!(
            dep.pcreds.check_membership(&dep.hvk, b"m", &unchecked),
            Err(Error::InvalidGroupElement("σ*"))
        );
    }

    // Reply: every element of σ̂ (the compact encoding is the canonical one)
    for element in B::pre_credential_elements(&pre) {
        let bytes = shifted_in(&reply.to_compact_bytes().unwrap(), &element);
        assert!(refused(
            Reply::<Bk<B, T>>::from_compact_bytes(&bytes).map(drop)
        ));
        let Reply::PreCredential(unchecked) =
            Reply::<Bk<B, T>>::deserialize_compressed_unchecked(&bytes[..]).unwrap()
        else {
            panic!("the tag byte is untouched");
        };
        assert_eq!(
            dep.pcreds
                .unblind(&dep.hvk, &user, &unchecked, copy(&state))
                .err(),
            Some(Error::InvalidGroupElement("σ̂"))
        );
    }
    assert!(
        dep.pcreds
            .unblind(&dep.hvk, &user, &pre, copy(&state))
            .is_ok()
    );
}

#[test]
fn decoders_reject_off_subgroup_points_ps_ddh() {
    decoders_reject_off_subgroup_points::<PS, DDH>(b"adv/wire/ps+ddh", 0xadde_0001);
}

#[test]
fn decoders_reject_off_subgroup_points_bbs_dy() {
    decoders_reject_off_subgroup_points::<BBS, DY>(b"adv/wire/bbs+dy", 0xadde_0002);
}

/// Users and issuance states read back from storage WITHOUT validation: a user whose identifier
/// is shifted by `P_3` is refused by [`Protocol::check_user`] ([`Error::IdentifierMismatch`]),
/// and an issuance state whose owner is shifted cannot be used to unblind
/// ([`Error::IssuanceStateMismatch`]); validated decoding refuses both.
#[test]
fn unvalidated_secrets_are_rechecked() {
    type B = PS;
    type T = DDH;
    let dep = Deployment::<B, T>::new(b"adv/stored", 1, 0xad5d_0001);
    let mut rng = StdRng::seed_from_u64(0xad5d_0002);
    let user = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let bytes = shifted_in(&user.to_bytes().unwrap(), user.id());
    assert!(serialization::from_bytes::<User<Bk<B, T>>>(&bytes).is_err());
    let stored = User::<Bk<B, T>>::deserialize_compressed_unchecked(&bytes[..]).unwrap();
    assert_eq!(
        dep.pcreds.check_user(&dep.hvk, &stored),
        Err(Error::IdentifierMismatch)
    );
    assert_eq!(dep.pcreds.check_user(&dep.hvk, &user), Ok(()));

    let (_, state) = dep
        .pcreds
        .request_credential(&dep.hvk, &user, Vec::new(), b"r", &mut rng)
        .unwrap();
    let bytes = shifted_in(&state.to_bytes().unwrap(), user.id());
    assert!(serialization::from_bytes::<IssuanceState<Bk<B, T>>>(&bytes).is_err());
    let stored = IssuanceState::<Bk<B, T>>::deserialize_compressed_unchecked(&bytes[..]).unwrap();
    let pre = B::random_pre_credential(&mut rng);
    assert_eq!(
        dep.pcreds.unblind(&dep.hvk, &user, &pre, stored).err(),
        Some(Error::IssuanceStateMismatch)
    );
}

// ---------------------------------------------------------------------------------------------
// Malformed proofs and garbage
// ---------------------------------------------------------------------------------------------

/// Malformations of an honest proof: the wrong number of responses (none, one fewer, one more,
/// 32), a zero challenge (with the honest responses, and with zero responses), a modified or
/// random challenge, each response modified, every response zero.
fn malformed(proof: &FSProof<Fr>, rng: &mut StdRng) -> Vec<FSProof<Fr>> {
    let n = proof.responses.len();
    let with = |challenge: Fr, responses: Vec<Fr>| FSProof {
        challenge,
        responses,
    };
    let mut out = vec![
        with(proof.challenge, Vec::new()),
        with(proof.challenge, proof.responses[..n - 1].to_vec()),
        with(
            proof.challenge,
            [proof.responses.clone(), vec![Fr::one()]].concat(),
        ),
        with(proof.challenge, vec![Fr::one(); 32]),
        with(Fr::zero(), proof.responses.clone()),
        with(Fr::zero(), vec![Fr::zero(); n]),
        with(proof.challenge + Fr::one(), proof.responses.clone()),
        with(Fr::rand(rng), proof.responses.clone()),
        with(proof.challenge, vec![Fr::zero(); n]),
    ];
    for i in 0..n {
        let mut responses = proof.responses.clone();
        responses[i] += Fr::one();
        out.push(with(proof.challenge, responses));
    }
    out
}

/// Every malformation of every proof of the protocol (`π_id`, `π_att`, `π_iss`, `π_prove`) is
/// refused by its verifier with [`Error::InvalidProof`], and the compact encoders refuse a proof
/// whose number of responses is not the constant of its kind ([`Error::LengthMismatch`]): the
/// decoder reads exactly that number, so one response fewer is truncated input and one more is
/// trailing input.
fn malformed_proofs<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let dep = Deployment::<B, T>::new(label, 1, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xbad);
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let newcomer = pcreds.register(hvk, &mut rng).unwrap();
    let request = pcreds
        .request_attestation(hvk, &newcomer, b"s", b"c", &mut rng)
        .unwrap();
    let att = attestation_from(pcreds, hvk, of(&dep.members[0]), &newcomer, b"a", &mut rng);
    let (message, _) = pcreds
        .request_credential(hvk, &newcomer, vec![att.clone()], b"iss", &mut rng)
        .unwrap();
    let membership = pcreds
        .prove(
            hvk,
            &dep.members[0].user,
            &dep.members[0].cred,
            b"m",
            &mut rng,
        )
        .unwrap();
    assert_eq!(
        request.proof.responses.len(),
        <Bk<B, T>>::responses(ProofKind::Identifier)
    );
    assert_eq!(
        att.proof.responses.len(),
        <Bk<B, T>>::responses(ProofKind::Attestation)
    );
    assert_eq!(
        message.proof.responses.len(),
        <Bk<B, T>>::responses(ProofKind::Issuance)
    );
    assert_eq!(
        membership.proof.responses.len(),
        <Bk<B, T>>::responses(ProofKind::Possession)
    );

    for proof in malformed(&request.proof, &mut rng) {
        let bad = AttestationRequest {
            proof,
            ..request.clone()
        };
        assert_eq!(
            pcreds
                .receive_attestation_request(hvk, &bad, b"s", b"c")
                .err(),
            Some(Error::InvalidProof)
        );
    }
    for proof in malformed(&att.proof, &mut rng) {
        let bad = Attestation {
            proof,
            ..att.clone()
        };
        assert_eq!(
            pcreds.check_attestation(hvk, newcomer.id(), &bad),
            Err(Error::InvalidProof)
        );
    }
    for proof in malformed(&message.proof, &mut rng) {
        let bad = CredentialRequest {
            proof,
            ..message.clone()
        };
        assert_eq!(
            pcreds.evaluate_request(&dep.helper, &bad, b"iss").err(),
            Some(Error::InvalidProof)
        );
    }
    for proof in malformed(&membership.proof, &mut rng) {
        let bad = MembershipProof {
            proof,
            ..membership.clone()
        };
        assert_eq!(
            pcreds.check_membership(hvk, b"m", &bad),
            Err(Error::InvalidProof)
        );
    }

    // the fixed format
    let short = |proof: &FSProof<Fr>| FSProof {
        challenge: proof.challenge,
        responses: proof.responses[1..].to_vec(),
    };
    let mismatch = |kind: ProofKind| {
        let expected = <Bk<B, T>>::responses(kind);
        Err(Error::LengthMismatch {
            expected,
            actual: expected - 1,
        })
    };
    assert_eq!(
        AttestationRequest {
            proof: short(&request.proof),
            ..request.clone()
        }
        .to_compact_bytes(),
        mismatch(ProofKind::Identifier)
    );
    assert_eq!(
        Attestation {
            proof: short(&att.proof),
            ..att.clone()
        }
        .to_compact_bytes(),
        mismatch(ProofKind::Attestation)
    );
    assert_eq!(
        CredentialRequest {
            proof: short(&message.proof),
            ..message.clone()
        }
        .to_compact_bytes(),
        mismatch(ProofKind::Issuance)
    );
    assert_eq!(
        MembershipProof {
            proof: short(&membership.proof),
            ..membership.clone()
        }
        .to_compact_bytes(),
        mismatch(ProofKind::Possession)
    );
    let bytes = att.to_compact_bytes().unwrap();
    assert!(matches!(
        Attestation::<Bk<B, T>>::from_compact_bytes(&bytes[..bytes.len() - 32]),
        Err(Error::Serialization(_))
    ));
    let longer = [bytes.clone(), Fr::one().to_bytes().unwrap()].concat();
    assert_eq!(
        Attestation::<Bk<B, T>>::from_compact_bytes(&longer).err(),
        Some(Error::TrailingBytes)
    );
}

#[test]
fn malformed_proofs_ps_ddh() {
    malformed_proofs::<PS, DDH>(b"adv/malformed/ps+ddh", 0xadba_0001);
}

#[test]
fn malformed_proofs_bbs_dy() {
    malformed_proofs::<BBS, DY>(b"adv/malformed/bbs+dy", 0xadba_0002);
}

/// Adversarial byte strings: one flipped bit in the first, the middle and the last byte and in 8
/// seeded positions, truncation to half, one trailing byte, all-zero, all-`0xff`, empty, and a
/// seeded random string of the same length.
fn mutations(bytes: &[u8], rng: &mut StdRng) -> Vec<Vec<u8>> {
    let n = bytes.len();
    assert!(n > 1);
    let mut positions = vec![0, n / 2, n - 1];
    positions.extend((0..8).map(|_| rng.gen_range(0..n)));
    let mut out: Vec<Vec<u8>> = positions
        .into_iter()
        .map(|at| {
            let mut b = bytes.to_vec();
            b[at] ^= 1 << rng.gen_range(0..8);
            b
        })
        .collect();
    out.push(bytes[..n / 2].to_vec());
    out.push([bytes, &[0]].concat());
    out.push(vec![0; n]);
    out.push(vec![0xff; n]);
    out.push(Vec::new());
    let mut random = vec![0; n];
    rng.fill_bytes(&mut random);
    out.push(random);
    out
}

/// Number of rounds of well-typed garbage per base/tag pair in [`garbage_never_panics`].
const GARBAGE_ROUNDS: usize = 24;

/// Robustness: no verifier or decoder panics on adversarial input, and every one rejects it.
///
/// * Well-typed garbage (seeded): uniform elements, the identity in every position, zero
///   proofs, at every verifier: the attester, the recipient, the helper, `Verify`, `Unblind`,
///   the credential constructor.
/// * Byte strings: mutations of valid encodings of every message and stored object, compact and
///   canonical, and random strings of random lengths. A decoder returns an error or a value, and
///   the verifier of a decoded mutation rejects it.
fn garbage_never_panics<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xf0f0);
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let n_id = <Bk<B, T>>::responses(ProofKind::Identifier);
    let n_prove = <Bk<B, T>>::responses(ProofKind::Possession);

    for round in 0..GARBAGE_ROUNDS {
        let id = match round % 3 {
            0 => G1::rand(&mut rng),
            1 => G1::zero(),
            _ => G1::generator(),
        };
        let request = AttestationRequest::<Bk<B, T>> {
            id,
            proof: random_proof(n_id, &mut rng),
        };
        assert!(
            dep.pcreds
                .receive_attestation_request(&dep.hvk, &request, b"s", b"c")
                .is_err()
        );
        let att = random_attestation::<B, T>(&mut rng);
        assert!(dep.pcreds.check_attestation(&dep.hvk, &id, &att).is_err());
        let mut message = random_request::<B, T>(2, &mut rng);
        message.id = id;
        assert!(
            dep.pcreds
                .evaluate_request(&dep.helper, &message, b"r")
                .is_err()
        );
        let proof = MembershipProof::<Bk<B, T>> {
            show: B::random_show(&mut rng),
            proof: random_proof(n_prove, &mut rng),
        };
        assert!(dep.pcreds.check_membership(&dep.hvk, b"m", &proof).is_err());
        // the identity everywhere
        let zero = Attestation::<Bk<B, T>> {
            tag: G1::zero(),
            show: B::zero_show(),
            proof: FSProof {
                challenge: Fr::zero(),
                responses: vec![Fr::zero(); <Bk<B, T>>::responses(ProofKind::Attestation)],
            },
        };
        assert!(
            dep.pcreds
                .check_attestation(&dep.hvk, newcomer.id(), &zero)
                .is_err()
        );
        let zero_message = CredentialRequest::<Bk<B, T>> {
            id: G1::zero(),
            attestations: vec![zero.clone(), zero],
            request: predicate_credential_system::pcreds::pairing::G1Request(G1::zero()),
            proof: FSProof {
                challenge: Fr::zero(),
                responses: vec![Fr::zero(); <Bk<B, T>>::responses(ProofKind::Issuance)],
            },
        };
        assert!(
            dep.pcreds
                .evaluate_request(&dep.helper, &zero_message, b"r")
                .is_err()
        );
        let zero_proof = MembershipProof::<Bk<B, T>> {
            show: B::zero_show(),
            proof: FSProof {
                challenge: Fr::zero(),
                responses: vec![Fr::zero(); n_prove],
            },
        };
        assert!(
            dep.pcreds
                .check_membership(&dep.hvk, b"m", &zero_proof)
                .is_err()
        );
        // pre-credentials and credentials
        let (_, state) = dep
            .pcreds
            .request_credential(&dep.hvk, &newcomer, Vec::new(), b"g", &mut rng)
            .unwrap();
        for pre in [
            B::random_pre_credential(&mut rng),
            B::identity_pre_credential(),
        ] {
            assert!(
                dep.pcreds
                    .unblind(&dep.hvk, &newcomer, &pre, copy(&state))
                    .is_err()
            );
        }
        for cred in [
            B::random_credential(&mut rng),
            B::degenerate_credential(&mut rng),
        ] {
            assert!(dep.pcreds.credential(&dep.hvk, &newcomer, cred).is_err());
        }
    }

    // byte strings
    let request = dep
        .pcreds
        .request_attestation(&dep.hvk, &newcomer, b"s", b"c", &mut rng)
        .unwrap();
    let att = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        of(&dep.members[0]),
        &newcomer,
        b"a",
        &mut rng,
    );
    let (message, _) = dep
        .pcreds
        .request_credential(&dep.hvk, &newcomer, vec![att.clone()], b"iss", &mut rng)
        .unwrap();
    let membership = dep
        .pcreds
        .prove(
            &dep.hvk,
            &dep.members[0].user,
            &dep.members[0].cred,
            b"m",
            &mut rng,
        )
        .unwrap();
    let user = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let (root, state) = dep
        .pcreds
        .request_credential(&dep.hvk, &user, Vec::new(), b"root", &mut rng)
        .unwrap();
    let evaluated = dep
        .pcreds
        .evaluate_request(&dep.helper, &root, b"root")
        .unwrap();
    let reply = dep
        .pcreds
        .respond(&mut dep.helper, evaluated, Decision::Root, &mut rng)
        .unwrap();
    let Reply::PreCredential(pre) = reply.clone() else {
        panic!("a root admission of a new identifier issues");
    };
    let cred = dep
        .pcreds
        .unblind(&dep.hvk, &user, &pre, copy(&state))
        .unwrap();
    let pp = dep.pcreds.public_parameters().clone();
    let (pcreds, hvk, helper) = (&dep.pcreds, &dep.hvk, &dep.helper);

    let strings = |valid: &[u8], rng: &mut StdRng| {
        let mut all = mutations(valid, rng);
        for _ in 0..8 {
            let mut random = vec![0; rng.gen_range(0..2 * valid.len())];
            rng.fill_bytes(&mut random);
            all.push(random);
        }
        all
    };
    for bytes in strings(&request.to_compact_bytes().unwrap(), &mut rng) {
        if let Ok(r) = AttestationRequest::<Bk<B, T>>::from_compact_bytes(&bytes) {
            assert!(
                pcreds
                    .receive_attestation_request(hvk, &r, b"s", b"c")
                    .is_err()
            );
        }
    }
    for bytes in strings(&serialization::to_bytes(&request).unwrap(), &mut rng) {
        if let Ok(r) = serialization::from_bytes::<AttestationRequest<Bk<B, T>>>(&bytes) {
            assert!(
                pcreds
                    .receive_attestation_request(hvk, &r, b"s", b"c")
                    .is_err()
            );
        }
    }
    for bytes in strings(&att.to_compact_bytes().unwrap(), &mut rng) {
        if let Ok(a) = Attestation::<Bk<B, T>>::from_compact_bytes(&bytes) {
            assert!(pcreds.check_attestation(hvk, newcomer.id(), &a).is_err());
        }
    }
    for bytes in strings(&serialization::to_bytes(&att).unwrap(), &mut rng) {
        if let Ok(a) = serialization::from_bytes::<Attestation<Bk<B, T>>>(&bytes) {
            assert!(pcreds.check_attestation(hvk, newcomer.id(), &a).is_err());
        }
    }
    for bytes in strings(&message.to_compact_bytes().unwrap(), &mut rng) {
        if let Ok(m) = CredentialRequest::<Bk<B, T>>::from_compact_bytes(&bytes) {
            assert!(pcreds.evaluate_request(helper, &m, b"iss").is_err());
        }
    }
    for bytes in strings(&serialization::to_bytes(&message).unwrap(), &mut rng) {
        if let Ok(m) = serialization::from_bytes::<CredentialRequest<Bk<B, T>>>(&bytes) {
            assert!(pcreds.evaluate_request(helper, &m, b"iss").is_err());
        }
    }
    for bytes in strings(&membership.to_compact_bytes().unwrap(), &mut rng) {
        if let Ok(p) = MembershipProof::<Bk<B, T>>::from_compact_bytes(&bytes) {
            assert!(pcreds.check_membership(hvk, b"m", &p).is_err());
        }
    }
    for bytes in strings(&serialization::to_bytes(&membership).unwrap(), &mut rng) {
        if let Ok(p) = serialization::from_bytes::<MembershipProof<Bk<B, T>>>(&bytes) {
            assert!(pcreds.check_membership(hvk, b"m", &p).is_err());
        }
    }
    for bytes in strings(&reply.to_compact_bytes().unwrap(), &mut rng) {
        if let Ok(Reply::PreCredential(p)) = Reply::<Bk<B, T>>::from_compact_bytes(&bytes) {
            assert!(pcreds.unblind(hvk, &user, &p, copy(&state)).is_err());
        }
    }
    for bytes in strings(&user.to_bytes().unwrap(), &mut rng) {
        if let Ok(u) = serialization::from_bytes::<User<Bk<B, T>>>(&bytes) {
            assert!(pcreds.check_user(hvk, &u).is_err());
        }
    }
    for bytes in strings(&cred.to_bytes().unwrap(), &mut rng) {
        if let Ok(c) = serialization::from_bytes::<Credential<Bk<B, T>>>(&bytes) {
            assert!(!pcreds.verify_credential(hvk, &user, &c));
        }
    }
    for bytes in strings(&state.to_bytes().unwrap(), &mut rng) {
        if let Ok(s) = serialization::from_bytes::<IssuanceState<Bk<B, T>>>(&bytes) {
            assert!(pcreds.unblind(hvk, &user, &pre, s).is_err());
        }
    }
    for bytes in strings(&serialization::to_bytes(&pp).unwrap(), &mut rng) {
        if let Ok(p) = serialization::from_bytes::<PublicParameters<Bk<B, T>>>(&bytes) {
            assert!(Pcreds::<B, T>::from_public_parameters(p).is_err());
        }
    }
    // controls
    assert!(pcreds.unblind(hvk, &user, &pre, copy(&state)).is_ok());
    assert!(Pcreds::<B, T>::from_public_parameters(pp).is_ok());
}

#[test]
fn garbage_never_panics_ps_ddh() {
    garbage_never_panics::<PS, DDH>(b"adv/garbage/ps+ddh", 0xadf0_0001);
}

#[test]
fn garbage_never_panics_bbs_dy() {
    garbage_never_panics::<BBS, DY>(b"adv/garbage/bbs+dy", 0xadf0_0002);
}

// ---------------------------------------------------------------------------------------------
// Another deployment, another helper
// ---------------------------------------------------------------------------------------------

/// Objects of another deployment or helper (implementation notes of `pcreds::protocol`, "One
/// deployment per object"). Every algorithm refuses
///
/// * a [`HelperKey`] checked under another deployment ([`Error::InvalidKey`]);
/// * a [`Helper`] of another deployment, to evaluate, to respond, or to be restored
///   ([`Error::InvalidKey`]): a helper key of deployment A cannot issue in deployment B;
/// * a [`User`] of another deployment ([`Error::IdentifierMismatch`]), and a pending attestation
///   received under another deployment;
/// * an [`IssuanceState`] of another deployment or another user ([`Error::IssuanceStateMismatch`]);
/// * an [`EvaluatedRequest`] evaluated by another helper, of the same or another deployment
///   ([`Error::InvalidKey`]), without touching the issued set of the helper asked.
///
/// The boundary, as documented on [`Helper`]: nothing else ties a KEY to a deployment. A
/// credential of `Σ-PS` is a signature on `usk` under `hvk` and nothing more, so if the users of
/// deployment B accept the verification key of A's helper as their helper key, a `Σ-PS`
/// credential issued in A verifies, for the same `usk`, in B; that is why the [`Helper`] is bound
/// to one deployment. (A `Σ-BBS` credential signs `h_0 h_u^usk h_r^ρ` with generators derived
/// from the label, and does not verify in another deployment.)
fn other_deployments_and_helpers<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
) {
    let mut a = Deployment::<B, T>::new(&[label, b"/A"].concat(), 1, seed);
    let mut b = Deployment::<B, T>::new(&[label, b"/B"].concat(), 1, seed + 1);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xab);
    assert_ne!(a.pcreds.parameters_digest(), b.pcreds.parameters_digest());
    let policy = Policy::threshold(1).unwrap();
    let a_user = a.pcreds.register(&a.hvk, &mut rng).unwrap();
    let b_user = b.pcreds.register(&b.hvk, &mut rng).unwrap();
    let a_pending = pending_for(&a.pcreds, &a.hvk, &a_user, b"s", &mut rng);
    let b_pending = pending_for(&b.pcreds, &b.hvk, &b_user, b"s", &mut rng);
    let b_att = b
        .pcreds
        .attest(
            &b.hvk,
            &b.members[0].user,
            &b.members[0].cred,
            b_pending,
            &mut rng,
        )
        .unwrap();
    let b_proof = b
        .pcreds
        .prove(
            &b.hvk,
            &b.members[0].user,
            &b.members[0].cred,
            b"m",
            &mut rng,
        )
        .unwrap();
    let (a_message, a_state) = a
        .pcreds
        .request_credential(&a.hvk, &a_user, Vec::new(), b"r", &mut rng)
        .unwrap();
    let (b_message, b_state) = b
        .pcreds
        .request_credential(&b.hvk, &b_user, Vec::new(), b"r", &mut rng)
        .unwrap();
    let evaluated = b
        .pcreds
        .evaluate_request(&b.helper, &b_message, b"r")
        .unwrap();
    let Reply::PreCredential(b_pre) = b
        .pcreds
        .respond(&mut b.helper, evaluated, Decision::Root, &mut rng)
        .unwrap()
    else {
        panic!("a root admission of a new identifier issues");
    };
    let (bp, bh) = (&b.pcreds, &b.hvk);
    let (b_member, b_cred) = (&b.members[0].user, &b.members[0].cred);

    // the helper key of A, in B
    let a_key = &a.hvk;
    assert_eq!(
        bp.attest(
            a_key,
            b_member,
            b_cred,
            pending_for(bp, bh, &b_user, b"s", &mut rng),
            &mut rng
        )
        .err(),
        Some(Error::InvalidKey)
    );
    assert_eq!(
        bp.check_attestation(a_key, b_user.id(), &b_att),
        Err(Error::InvalidKey)
    );
    assert_eq!(
        bp.request_credential(a_key, &b_user, Vec::new(), b"r", &mut rng)
            .err(),
        Some(Error::InvalidKey)
    );
    assert_eq!(
        bp.unblind(a_key, &b_user, &b_pre, copy(&b_state)).err(),
        Some(Error::InvalidKey)
    );
    assert_eq!(
        bp.credential(a_key, b_member, b_cred.as_inner().clone())
            .err(),
        Some(Error::InvalidKey)
    );
    assert!(!bp.verify_credential(a_key, b_member, b_cred));
    assert_eq!(
        bp.prove(a_key, b_member, b_cred, b"m", &mut rng).err(),
        Some(Error::InvalidKey)
    );
    assert_eq!(
        bp.check_membership(a_key, b"m", &b_proof),
        Err(Error::InvalidKey)
    );

    // the helper of A, in B: it cannot evaluate, issue, or be restored there
    assert_eq!(
        bp.evaluate_request(&a.helper, &b_message, b"r").err(),
        Some(Error::InvalidKey)
    );
    let evaluated = bp.evaluate_request(&b.helper, &b_message, b"r").unwrap();
    assert_eq!(
        bp.respond(&mut a.helper, evaluated, Decision::Root, &mut rng)
            .err(),
        Some(Error::InvalidKey)
    );
    let bytes = a.helper.to_bytes().unwrap();
    assert_eq!(
        bp.restore_helper(&bytes, policy, IssuanceRecord::new())
            .err(),
        Some(Error::InvalidKey)
    );
    assert!(
        a.pcreds
            .restore_helper(&bytes, policy, IssuanceRecord::new())
            .is_ok()
    );

    // users, pending attestations and issuance states of A, in B
    let (a_member, a_cred) = (&a.members[0].user, &a.members[0].cred);
    assert_eq!(
        bp.request_attestation(bh, &a_user, b"s", b"c", &mut rng)
            .err(),
        Some(Error::IdentifierMismatch)
    );
    assert_eq!(
        bp.attest(
            bh,
            a_member,
            a_cred,
            pending_for(bp, bh, &b_user, b"s", &mut rng),
            &mut rng
        )
        .err(),
        Some(Error::IdentifierMismatch)
    );
    assert_eq!(
        bp.attest(bh, b_member, b_cred, a_pending, &mut rng).err(),
        Some(Error::IdentifierMismatch)
    );
    assert_eq!(
        bp.request_credential(bh, &a_user, Vec::new(), b"r", &mut rng)
            .err(),
        Some(Error::IdentifierMismatch)
    );
    assert_eq!(
        bp.unblind(bh, &a_user, &b_pre, copy(&a_state)).err(),
        Some(Error::IdentifierMismatch)
    );
    assert_eq!(
        bp.prove(bh, a_member, a_cred, b"m", &mut rng).err(),
        Some(Error::IdentifierMismatch)
    );
    assert_eq!(
        bp.credential(bh, a_member, a_cred.as_inner().clone()).err(),
        Some(Error::IdentifierMismatch)
    );
    assert!(!bp.verify_credential(bh, a_member, a_cred));
    assert_eq!(bp.check_user(bh, &a_user), Err(Error::IdentifierMismatch));
    assert_eq!(
        bp.unblind(bh, &b_user, &b_pre, copy(&a_state)).err(),
        Some(Error::IssuanceStateMismatch)
    );
    let other = bp.register(bh, &mut rng).unwrap();
    let (_, other_state) = bp
        .request_credential(bh, &other, Vec::new(), b"o", &mut rng)
        .unwrap();
    assert_eq!(
        bp.unblind(bh, &b_user, &b_pre, copy(&other_state)).err(),
        Some(Error::IssuanceStateMismatch)
    );
    assert!(
        bp.unblind(bh, &b_user, &b_pre, copy(&b_state)).is_ok(),
        "control"
    );

    // evaluated requests answered by another helper: of the same deployment, and of A
    let mut second = bp.helper_keygen(policy, &mut rng);
    let fresh = bp.register(bh, &mut rng).unwrap();
    let (message, _) = bp
        .request_credential(bh, &fresh, Vec::new(), b"f", &mut rng)
        .unwrap();
    let evaluated = bp.evaluate_request(&b.helper, &message, b"f").unwrap();
    assert_eq!(
        bp.respond(&mut second, evaluated, Decision::Root, &mut rng)
            .err(),
        Some(Error::InvalidKey)
    );
    assert!(second.store().is_empty());
    let evaluated = a
        .pcreds
        .evaluate_request(&a.helper, &a_message, b"r")
        .unwrap();
    let issued = b.helper.store().len();
    assert_eq!(
        b.pcreds
            .respond(&mut b.helper, evaluated, Decision::Root, &mut rng)
            .err(),
        Some(Error::InvalidKey)
    );
    assert_eq!(b.helper.store().len(), issued);

    // the boundary: if B's users accept A's verification key, A's credentials verify in B
    // exactly when the bases' parameters coincide (Σ-PS: pp_Σ is empty; Σ-BBS: the generators
    // are derived from the label)
    let b_view = b
        .pcreds
        .helper_key(a.hvk.vk())
        .expect("a key admissible anywhere");
    let a_member_in_b = b
        .pcreds
        .user(&b_view, *a.members[0].user.expose_key())
        .unwrap();
    let transferred = b.pcreds.credential(
        &b_view,
        &a_member_in_b,
        a.members[0].cred.as_inner().clone(),
    );
    if a.pcreds.params().base == b.pcreds.params().base {
        assert!(transferred.is_ok());
    } else {
        assert_eq!(transferred.err(), Some(Error::InvalidCredential));
    }
}

#[test]
fn other_deployments_and_helpers_ps_dy() {
    other_deployments_and_helpers::<PS, DY>(b"adv/cross/ps+dy", 0xadab_0001);
}

#[test]
fn other_deployments_and_helpers_bbs_ddh() {
    other_deployments_and_helpers::<BBS, DDH>(b"adv/cross/bbs+ddh", 0xadab_0003);
}

// ---------------------------------------------------------------------------------------------
// The policy
// ---------------------------------------------------------------------------------------------

/// `Pol_k` needs `k ≥ 1` ([`Error::ZeroThreshold`]; "the threshold policy never accepts a first
/// request" only because `k ≥ 1`), and a limit below `k` is refused. A helper that limits the
/// attestations of a request (optional; there is no limit by default, and `Pol_k` counts any
/// number of attestations) checks the limit FIRST: a request with `limit + 1` attestations is
/// refused with [`Error::TooManyAttestations`] although its identifier is the identity, its
/// request lies outside `G_1`, its attestations carry shifted tags and its proof is garbage —
/// every later check would have failed, so nothing was verified before the limit. At the limit
/// the next checks run, in the documented order: `id_Q ∈ T`, `Ĉ`, `π_iss`. A request with no
/// attestations under `d = policy` fails: the requester has no way to choose `d = root`. The
/// compact decoder does not allocate ahead of its input for a count taken from the wire.
#[test]
fn zero_threshold_and_the_attestation_limit() {
    assert_eq!(Policy::threshold(0).err(), Some(Error::ZeroThreshold));
    assert!(matches!(
        Policy::threshold(3).unwrap().with_max_attestations(2),
        Err(Error::DegenerateInput(_))
    ));
    let mut dep = Deployment::<PS, DDH>::new(b"adv/cap", 2, 0xadca_0001);
    let mut rng = StdRng::seed_from_u64(0xadca_0002);
    assert_eq!(dep.helper.policy().max_attestations(), None);
    // without a limit, a long garbage request goes on to the next checks
    let long = random_request::<PS, DDH>(64, &mut rng);
    assert_eq!(
        dep.pcreds.evaluate_request(&dep.helper, &long, b"r").err(),
        Some(Error::InvalidProof)
    );
    // a helper with the limit 2
    let limited = dep.pcreds.helper_keygen(
        Policy::threshold(2)
            .unwrap()
            .with_max_attestations(2)
            .unwrap(),
        &mut rng,
    );
    assert_eq!(limited.policy().max_attestations(), Some(2));

    let mut message = random_request::<PS, DDH>(3, &mut rng);
    message.id = G1::zero();
    message.request.0 += p3();
    for att in &mut message.attestations {
        att.tag += p3();
    }
    assert_eq!(
        dep.pcreds.evaluate_request(&limited, &message, b"r").err(),
        Some(Error::TooManyAttestations { max: 2, actual: 3 })
    );
    let flood = CredentialRequest {
        attestations: vec![message.attestations[0].clone(); 4096],
        ..message.clone()
    };
    assert_eq!(
        dep.pcreds.evaluate_request(&limited, &flood, b"r").err(),
        Some(Error::TooManyAttestations {
            max: 2,
            actual: 4096
        })
    );
    message.attestations.truncate(2);
    assert_eq!(
        dep.pcreds.evaluate_request(&limited, &message, b"r").err(),
        Some(Error::InvalidTag)
    );
    message.id = G1::rand(&mut rng);
    assert_eq!(
        dep.pcreds.evaluate_request(&limited, &message, b"r").err(),
        Some(Error::InvalidGroupElement("Ĉ"))
    );
    message.request.0 = G1::rand(&mut rng);
    assert_eq!(
        dep.pcreds.evaluate_request(&limited, &message, b"r").err(),
        Some(Error::InvalidProof)
    );
    // a raised limit lets a longer request through to the next check
    let generous = dep.pcreds.helper_keygen(
        Policy::threshold(2)
            .unwrap()
            .with_max_attestations(4)
            .unwrap(),
        &mut rng,
    );
    let long = random_request::<PS, DDH>(4, &mut rng);
    assert_eq!(
        dep.pcreds.evaluate_request(&generous, &long, b"r").err(),
        Some(Error::InvalidProof)
    );

    // no attestations, d = policy
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let issued = dep.helper.store().len();
    let (message, _) = dep
        .pcreds
        .request_credential(&dep.hvk, &newcomer, Vec::new(), b"first", &mut rng)
        .unwrap();
    let evaluated = dep
        .pcreds
        .evaluate_request(&dep.helper, &message, b"first")
        .unwrap();
    assert!(!evaluated.is_valid());
    assert_eq!(
        dep.pcreds
            .respond(&mut dep.helper, evaluated, Decision::Policy, &mut rng),
        Ok(Reply::Fail)
    );
    assert_eq!(dep.helper.store().len(), issued);

    // a count of u32::MAX with nothing behind it
    let bytes = [
        newcomer.id().to_bytes().unwrap(),
        u32::MAX.to_le_bytes().to_vec(),
    ]
    .concat();
    assert!(matches!(
        CredentialRequest::<Bk<PS, DDH>>::from_compact_bytes(&bytes),
        Err(Error::Serialization(_))
    ));
}

/// One source counts once ("a source counts once", §5.1): the tag of an attester for a
/// recipient is deterministic, so two attestations of one member (fresh shows, the same tag)
/// and one attestation twice count as ONE in `N''`, in any order. An attestation that fails
/// verification does not block a valid one with the same tag, in either order. `k − 1`
/// distinct sources fail, `k` succeed.
fn distinct_sources_count_once<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
) {
    let dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xd5);
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let from = |j: usize, ssid: &[u8], rng: &mut StdRng| {
        attestation_from(
            &dep.pcreds,
            &dep.hvk,
            of(&dep.members[j]),
            &newcomer,
            ssid,
            rng,
        )
    };
    let att = from(0, b"a", &mut rng);
    let again = from(0, b"b", &mut rng);
    let other = from(1, b"c", &mut rng);
    assert_eq!(att.tag, again.tag);
    assert_ne!(att.show, again.show);
    for list in [
        vec![att.clone(), again.clone()],
        vec![again.clone(), att.clone()],
        vec![att.clone(), att.clone()],
        vec![att.clone()],
    ] {
        let evaluated = evaluate_with(&dep, &newcomer, list, b"r", &mut rng);
        assert_eq!(evaluated.tags(), &[att.tag]);
        assert!(!evaluated.is_valid());
    }
    let mut broken = other.clone();
    broken.proof.challenge += Fr::one();
    for list in [
        vec![broken.clone(), other.clone()],
        vec![other.clone(), broken],
    ] {
        let evaluated = evaluate_with(&dep, &newcomer, list, b"r", &mut rng);
        assert_eq!(evaluated.tags(), &[other.tag]);
    }
    let evaluated = evaluate_with(&dep, &newcomer, vec![att, other], b"r", &mut rng);
    assert_eq!(evaluated.tags().len(), 2);
    assert!(evaluated.is_valid());
}

#[test]
fn distinct_sources_count_once_ps_ddh() {
    distinct_sources_count_once::<PS, DDH>(b"adv/distinct/ps+ddh", 0xadd5_0001);
}

#[test]
fn distinct_sources_count_once_bbs_dy() {
    distinct_sources_count_once::<BBS, DY>(b"adv/distinct/bbs+dy", 0xadd5_0002);
}

/// Attestations are not transferable (Remark "Attestations and issuance"; the
/// `attestations_are_not_transferable` test of the earlier construction). An attestation for
/// the victim does not verify for anybody else (`x_Q = H_req(⟨pp, hvk, id_Q⟩)`), counts nothing in
/// another requester's request, and cannot be redeemed under the victim's identifier without the
/// victim's key (`π_iss`; the cheating prover has no witness); the thief cannot even collect
/// attestations for the victim's identifier (`π_id`).
fn attestations_are_not_transferable<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
) {
    let dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0x7f);
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let victim = pcreds.register(hvk, &mut rng).unwrap();
    let thief = pcreds.register(hvk, &mut rng).unwrap();
    let atts: Vec<_> = (0..2)
        .map(|j| {
            attestation_from(
                pcreds,
                hvk,
                of(&dep.members[j]),
                &victim,
                &[j as u8],
                &mut rng,
            )
        })
        .collect();
    assert_eq!(
        pcreds.check_attestation(hvk, thief.id(), &atts[0]),
        Err(Error::InvalidProof)
    );
    let evaluated = evaluate_with(&dep, &thief, atts.clone(), b"t", &mut rng);
    assert!(evaluated.tags().is_empty() && !evaluated.is_valid());
    let (message, state) = pcreds
        .request_credential(hvk, &thief, atts.clone(), b"t", &mut rng)
        .unwrap();
    let forged = CredentialRequest {
        id: *victim.id(),
        ..message.clone()
    };
    assert_eq!(
        pcreds.evaluate_request(&dep.helper, &forged, b"t").err(),
        Some(Error::InvalidProof)
    );
    let relation = <Bk<B, T>>::issuance_relation(
        pcreds.params(),
        hvk.vk(),
        &message.request,
        victim.id(),
        hvk.identifier_point(),
    )
    .unwrap();
    // neither the thief's key (the tag clause fails) nor the victim's (the opening of Ĉ fails)
    for usk in [thief.expose_key(), victim.expose_key()] {
        assert!(!relation.is_satisfied_by(&[*usk, *state.expose_tape()]));
    }
    // grafted into the victim's request, an attestation for the thief counts nothing
    let for_thief = attestation_from(pcreds, hvk, of(&dep.members[1]), &thief, b"g", &mut rng);
    let evaluated = evaluate_with(
        &dep,
        &victim,
        vec![atts[0].clone(), for_thief],
        b"v",
        &mut rng,
    );
    assert_eq!(evaluated.tags(), &[atts[0].tag]);
    assert!(!evaluated.is_valid());
    // π_id: the thief cannot ask for attestations under the victim's identifier
    let request = pcreds
        .request_attestation(hvk, &thief, b"s", b"c", &mut rng)
        .unwrap();
    let stolen = AttestationRequest {
        id: *victim.id(),
        ..request
    };
    assert_eq!(
        pcreds
            .receive_attestation_request(hvk, &stolen, b"s", b"c")
            .err(),
        Some(Error::InvalidProof)
    );
}

#[test]
fn attestations_are_not_transferable_ps_ddh() {
    attestations_are_not_transferable::<PS, DDH>(b"adv/xfer/ps+ddh", 0xad7f_0001);
}

#[test]
fn attestations_are_not_transferable_bbs_dy() {
    attestations_are_not_transferable::<BBS, DY>(b"adv/xfer/bbs+dy", 0xad7f_0002);
}

/// Documented behavior, not an attack: attestations are standing endorsements. `π_att` "has no
/// context: its statement fixes the recipient through `x_Q`, and the attestation may be used in
/// several credential requests" (protocol box). So a requester keeps its attestations across
/// requests: one that failed with too few attestations is repeated with more, reusing the old
/// ones, and issues; a further request with the same attestations is valid but answered `issued`.
/// They are bound to `(pp, hvk, id_Q)`: under another helper of the deployment they count
/// nothing.
#[test]
fn attestations_are_standing_endorsements() {
    let dep = Deployment::<PS, DDH>::new(b"adv/standing", 2, 0xad57_0001);
    let mut dep = dep;
    let mut rng = StdRng::seed_from_u64(0xad57_0002);
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let atts: Vec<_> = (0..2)
        .map(|j| {
            attestation_from(
                &dep.pcreds,
                &dep.hvk,
                of(&dep.members[j]),
                &newcomer,
                &[j as u8],
                &mut rng,
            )
        })
        .collect();
    let replies: Vec<_> = [vec![atts[0].clone()], atts.clone(), atts.clone()]
        .into_iter()
        .enumerate()
        .map(|(i, list)| {
            let ssid = [b'r', i as u8];
            let (message, state) = dep
                .pcreds
                .request_credential(&dep.hvk, &newcomer, list, &ssid, &mut rng)
                .unwrap();
            let evaluated = dep
                .pcreds
                .evaluate_request(&dep.helper, &message, &ssid)
                .unwrap();
            let reply = dep
                .pcreds
                .respond(&mut dep.helper, evaluated, Decision::Policy, &mut rng)
                .unwrap();
            if let Reply::PreCredential(pre) = &reply {
                assert!(
                    dep.pcreds
                        .unblind(&dep.hvk, &newcomer, pre, copy(&state))
                        .is_ok()
                );
            }
            reply
        })
        .collect();
    assert_eq!(replies[0], Reply::Fail);
    assert!(matches!(replies[1], Reply::PreCredential(_)));
    assert_eq!(replies[2], Reply::Issued);

    let other = dep
        .pcreds
        .helper_keygen(Policy::threshold(2).unwrap(), &mut rng);
    let other_hvk = dep.pcreds.helper_key(other.key().vk()).unwrap();
    // the newcomer registers with the other helper too: another identifier, another x_Q
    let newcomer_there = dep.pcreds.register_reusing(&other_hvk, &newcomer).unwrap();
    assert_ne!(newcomer_there.id(), newcomer.id());
    let (message, _) = dep
        .pcreds
        .request_credential(&other_hvk, &newcomer_there, atts, b"elsewhere", &mut rng)
        .unwrap();
    let evaluated = dep
        .pcreds
        .evaluate_request(&other, &message, b"elsewhere")
        .unwrap();
    assert!(evaluated.tags().is_empty() && !evaluated.is_valid());
}

// ---------------------------------------------------------------------------------------------
// A malicious helper; inadmissible keys
// ---------------------------------------------------------------------------------------------

/// `Unblind` fails closed (protocol box: "check `Verify(hvk, usk_Q, σ_Q) = 1`") against a
/// malicious helper's answer ([`Error::InvalidPreCredential`]): uniform elements, the identity,
/// `BlindIssue` on another user's request, `BlindIssue` on the requester's OTHER request (the
/// randomness `τ` must be kept from `PrepareIssue` to `Unblind`), and the right pre-credential
/// with the state of the other request. The protocol's helper issues on exactly the `Ĉ` it
/// evaluated ("issuance must run on the proof"): its answer unblinds with the request's state.
fn unblind_fails_closed<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0xb1);
    let user = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let other = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let (message, state) = dep
        .pcreds
        .request_credential(&dep.hvk, &user, Vec::new(), b"r", &mut rng)
        .unwrap();
    let (second, second_state) = dep
        .pcreds
        .request_credential(&dep.hvk, &user, Vec::new(), b"r2", &mut rng)
        .unwrap();
    let (other_message, _) = dep
        .pcreds
        .request_credential(&dep.hvk, &other, Vec::new(), b"o", &mut rng)
        .unwrap();
    let sk = signing_key(&dep.helper);
    let params = dep.pcreds.params().clone();
    let blind = |request: &CredentialRequest<Bk<B, T>>, rng: &mut StdRng| {
        <Bk<B, T> as Backend>::blind_issue(&params, &sk, &request.request, rng).unwrap()
    };
    let refused = Some(Error::InvalidPreCredential);
    for _ in 0..3 {
        let pre = B::random_pre_credential(&mut rng);
        assert_eq!(
            dep.pcreds
                .unblind(&dep.hvk, &user, &pre, copy(&state))
                .err(),
            refused
        );
    }
    let pre = B::identity_pre_credential();
    assert_eq!(
        dep.pcreds
            .unblind(&dep.hvk, &user, &pre, copy(&state))
            .err(),
        refused
    );
    for wrong in [&other_message, &second] {
        let pre = blind(wrong, &mut rng);
        assert_eq!(
            dep.pcreds
                .unblind(&dep.hvk, &user, &pre, copy(&state))
                .err(),
            refused
        );
    }
    let pre = blind(&message, &mut rng);
    assert_eq!(
        dep.pcreds
            .unblind(&dep.hvk, &user, &pre, copy(&second_state))
            .err(),
        refused
    );
    let cred = dep
        .pcreds
        .unblind(&dep.hvk, &user, &pre, copy(&state))
        .unwrap();
    assert!(dep.pcreds.verify_credential(&dep.hvk, &user, &cred));

    let evaluated = dep
        .pcreds
        .evaluate_request(&dep.helper, &message, b"r")
        .unwrap();
    let Reply::PreCredential(pre) = dep
        .pcreds
        .respond(&mut dep.helper, evaluated, Decision::Root, &mut rng)
        .unwrap()
    else {
        panic!("a root admission of a new identifier issues");
    };
    assert_eq!(
        dep.pcreds
            .unblind(&dep.hvk, &user, &pre, copy(&second_state))
            .err(),
        refused
    );
    assert!(
        dep.pcreds
            .unblind(&dep.hvk, &user, &pre, copy(&state))
            .is_ok()
    );
}

#[test]
fn unblind_fails_closed_ps_ddh() {
    unblind_fails_closed::<PS, DDH>(b"adv/unblind/ps+ddh", 0xadb1_0001);
}

#[test]
fn unblind_fails_closed_bbs_dy() {
    unblind_fails_closed::<BBS, DY>(b"adv/unblind/bbs+dy", 0xadb1_0002);
}

/// `hvk ∈ V_pp`, checked once by [`Protocol::helper_key`] (every algorithm takes the checked
/// [`HelperKey`]). `Σ-PS`: `V_pp` requires `Ỹ ≠ 1`, `Y ≠ 1` and `e(Y, g̃) = e(g_1, Ỹ)`; keys
/// violating each are refused ([`Error::InvalidKey`]), a key with a component outside the group
/// with [`Error::InvalidGroupElement`] although the pairing test alone accepts a `Y` shifted by
/// `P_3`. Why `Ỹ = 1` must be refused: under `(X̃, 1, 1)` a credential does not depend on `usk`,
/// and ONE credential satisfies `R_att` next to tags under any key. `Σ-BBS`: `V_pp = G_2`
/// (`x ← Z_p`, so `X̃ = 1` is a key of `KeyGen`); only an element outside `G_2` is refused.
#[test]
fn inadmissible_helper_keys_are_refused() {
    let dep = Deployment::<PS, DDH>::new(b"adv/keys/ps", 1, 0xadce_0001);
    let mut rng = StdRng::seed_from_u64(0xadce_0002);
    let vk = dep.hvk.vk().clone();
    let (g1, g2) = (G1::generator(), G2::generator());
    for bad in [
        PSVerificationKey {
            y2: G2::zero(),
            ..vk.clone()
        },
        PSVerificationKey {
            y1: G1::zero(),
            ..vk.clone()
        },
        PSVerificationKey {
            y1: G1::zero(),
            y2: G2::zero(),
            ..vk.clone()
        },
        PSVerificationKey {
            y1: vk.y1 + g1,
            ..vk.clone()
        },
    ] {
        assert_eq!(dep.pcreds.helper_key(&bad).err(), Some(Error::InvalidKey));
    }
    let shifted = PSVerificationKey {
        y1: vk.y1 + p3(),
        ..vk.clone()
    };
    assert!(
        pairing_product_is_identity::<E>(&[(shifted.y1, g2), (-g1, shifted.y2)]),
        "the pairing is blind to P_3"
    );
    assert_eq!(
        dep.pcreds.helper_key(&shifted).err(),
        Some(Error::InvalidGroupElement("hvk"))
    );
    assert!(
        dep.pcreds
            .helper_key(&PSVerificationKey {
                x2: G2::zero(),
                ..vk.clone()
            })
            .is_ok(),
        "X̃ = 1 is in V_pp (x ← Z_p)"
    );

    // under (X̃, 1, 1): one credential, tags under any key
    let x = Fr::rand(&mut rng);
    let degenerate = PSVerificationKey::<E> {
        x2: g2 * x,
        y2: G2::zero(),
        y1: G1::zero(),
    };
    let u = Fr::rand(&mut rng);
    let cred = PSPair::<E> {
        s1: g1 * u,
        s2: g1 * (u * x),
    };
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let xq = dep
        .pcreds
        .recipient_point(&degenerate, newcomer.id())
        .unwrap();
    for _ in 0..3 {
        let key = Fr::rand(&mut rng);
        assert!(<PS as Base<E>>::verify(&(), &degenerate, &key, &cred));
        let (show, omega) = <PS as Base<E>>::rerand(&(), &degenerate, &key, &cred, &mut rng);
        let mut witness = Witness::new();
        witness.push(key);
        <PS as Base<E>>::possession_witness(&cred, &omega, &mut witness);
        let tag = <Bk<PS, DDH> as Backend>::tag(dep.pcreds.params(), &key, &xq).unwrap();
        assert!(
            <Bk<PS, DDH>>::attestation_relation(dep.pcreds.params(), &degenerate, &show, &tag, &xq)
                .unwrap()
                .is_satisfied_by(&witness)
        );
    }

    // Σ-BBS
    let bbs = Pcreds::<BBS, DDH>::setup(b"adv/keys/bbs").unwrap();
    assert!(bbs.helper_key(&BBSVerificationKey(G2::zero())).is_ok());
    assert_eq!(
        bbs.helper_key(&BBSVerificationKey(G2::rand(&mut rng) + g2_off_subgroup()))
            .err(),
        Some(Error::InvalidGroupElement("hvk"))
    );
}

// ---------------------------------------------------------------------------------------------
// Undefined tags, restart loops, received parameters
// ---------------------------------------------------------------------------------------------

/// `Tag_DY` is undefined at `x = −K`. An attester whose key is `−x_Q` cannot attest for `Q`
/// ([`Error::UndefinedTag`]; protocol docs: "`Tag_DY`: `usk_P = −x_Q`"), and attests for
/// everybody else; the key `−x_0` has no identifier.
#[test]
fn tag_dy_undefined_points() {
    let mut dep = Deployment::<PS, DY>::new(b"adv/dy/undefined", 1, 0xadd1_0001);
    let mut rng = StdRng::seed_from_u64(0xadd1_0002);
    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let xq = dep
        .pcreds
        .recipient_point(dep.hvk.vk(), newcomer.id())
        .unwrap();
    let unlucky = dep.pcreds.user(&dep.hvk, -xq).expect("−x_Q + x_0 ≠ 0");
    let cred = dep.admit_root(&unlucky).unwrap();
    let pending = pending_for(&dep.pcreds, &dep.hvk, &newcomer, b"u", &mut rng);
    assert_eq!(
        dep.pcreds
            .attest(&dep.hvk, &unlucky, &cred, pending, &mut rng)
            .err(),
        Some(Error::UndefinedTag)
    );
    let other = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let att = attestation_from(
        &dep.pcreds,
        &dep.hvk,
        (&unlucky, &cred),
        &other,
        b"o",
        &mut rng,
    );
    assert_eq!(
        dep.pcreds.check_attestation(&dep.hvk, other.id(), &att),
        Ok(())
    );
    assert_eq!(
        dep.pcreds
            .user(&dep.hvk, -*dep.hvk.identifier_point())
            .err(),
        Some(Error::UndefinedTag)
    );
}

/// A degenerate RNG that replays the four Montgomery limbs of one field element forever: every
/// call of `Fr::rand` on it returns that element (arkworks samples the limbs and rejects values
/// `≥ r`).
struct Replay {
    limbs: [u64; 4],
    calls: usize,
}

impl RngCore for Replay {
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    fn next_u64(&mut self) -> u64 {
        let limb = self.limbs[self.calls % 4];
        self.calls += 1;
        limb
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        for chunk in dest.chunks_mut(8) {
            let bytes = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&bytes[..chunk.len()]);
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

// Test-only marker: the protocol asks for a `CryptoRng`.
impl CryptoRng for Replay {}

/// `Register` samples ONE key ("If `id_P = ⊥`, return `(RegisterFailed, ⊥)`"; implementation
/// notes of `pcreds::protocol`, "No restart loops"). Under `Tag_DY` an RNG that yields `−x_0`
/// makes that sample `⊥`, and `Register` fails ([`Error::UndefinedTag`]) after one sample of four
/// limbs, without drawing another key. The same key is defined under another helper key, whose
/// identifier point differs.
#[test]
fn register_fails_on_an_undefined_identifier() {
    let pcreds = Pcreds::<PS, DY>::setup(b"adv/register-once").unwrap();
    let mut rng = StdRng::seed_from_u64(0xad1e_0001);
    let hvk = pcreds
        .helper_keygen(Policy::threshold(1).unwrap(), &mut rng)
        .key()
        .clone();
    let bad = -*hvk.identifier_point();
    let mut replay = Replay {
        limbs: bad.0.0,
        calls: 0,
    };
    assert_eq!(Fr::rand(&mut replay), bad, "the RNG replays −x_0");
    replay.calls = 0;
    assert_eq!(
        pcreds.register(&hvk, &mut replay).err(),
        Some(Error::UndefinedTag)
    );
    assert_eq!(replay.calls, 4, "one sample of four limbs, no restart");
    assert_eq!(pcreds.user(&hvk, bad).err(), Some(Error::UndefinedTag));
    let other = pcreds
        .helper_keygen(Policy::threshold(1).unwrap(), &mut rng)
        .key()
        .clone();
    assert!(pcreds.user(&other, bad).is_ok(), "another key, another x_0");
}

/// Received public parameters are accepted only if they are what `Setup` derives from their own
/// label ([`Protocol::from_public_parameters`]; [`Error::InvalidPublicParameters`]): another
/// label, generators with a known discrete-logarithm relation (well formed, so
/// [`Protocol::setup_with_params`] takes them), another label on the same parameters, and
/// parameters other than the expected ones. An identity generator is refused even by
/// `setup_with_params`. A degenerate `Tag_DY` instance (its generator the identity, reachable
/// only through unvalidated decoding) is refused before any restart loop can run.
#[test]
fn received_parameters_must_be_derived() {
    type Scheme = Pcreds<BBS, DDH>;
    let label = b"adv/received-pp";
    let pcreds = Scheme::setup(label).unwrap();
    let pp = pcreds.public_parameters().clone();
    let refused = |pp: PublicParameters<Bk<BBS, DDH>>| match Scheme::from_public_parameters(pp) {
        Err(Error::InvalidPublicParameters(what)) => what,
        other => panic!("accepted, or refused for another reason: {other:?}"),
    };
    let mut bad = pp.clone();
    bad.label = b"adv/received-pp/another".to_vec();
    assert_eq!(
        refused(bad),
        "the parameters are not derived from the label"
    );
    let mut bad = pp.clone();
    bad.params.base.hr = bad.params.base.hu * Fr::from(2u64);
    assert!(Scheme::setup_with_params(label, bad.params.clone()).is_ok());
    assert_eq!(
        refused(bad.clone()),
        "the parameters are not derived from the label"
    );
    assert_eq!(
        Scheme::from_public_parameters_with_params(pp.clone(), &bad.params).err(),
        Some(Error::InvalidPublicParameters(
            "the parameters are not the expected ones"
        ))
    );
    let mut bad = pp.clone();
    bad.label = b"adv/received-pp/other".to_vec();
    assert_eq!(
        refused(bad),
        "the parameters are not derived from the label"
    );
    let mut params = pp.params.clone();
    params.base.h0 = G1::zero();
    assert_eq!(
        Scheme::setup_with_params(label, params).err(),
        Some(Error::DegenerateInput("BBS generators"))
    );
    let received = PublicParameters::<Bk<BBS, DDH>>::from_bytes(&pp.to_bytes().unwrap()).unwrap();
    let rebuilt = Scheme::from_public_parameters(received).unwrap();
    assert_eq!(rebuilt.parameters_digest(), pcreds.parameters_digest());

    // a degenerate Tag_DY
    type DyScheme = Pcreds<PS, DY>;
    let identity = G1::zero().to_bytes().unwrap();
    assert!(serialization::from_bytes::<DY>(&identity).is_err());
    let degenerate = DY::deserialize_compressed_unchecked(&identity[..]).unwrap();
    assert!(!degenerate.is_well_formed());
    // Refused before any restart loop can run, as `ProtocolTag::is_well_formed` documents:
    // `PairingBackend::check_params` asks for degeneracy before it re-validates `pp_Tag`.
    assert_eq!(
        DyScheme::setup_with_params(
            label,
            PairingParams {
                base: (),
                tag: degenerate.clone(),
            }
        )
        .err(),
        Some(Error::DegenerateInput("pp_Tag"))
    );
    let mut pp = DyScheme::setup(label).unwrap().public_parameters().clone();
    pp.params.tag = degenerate;
    assert!(matches!(
        DyScheme::from_public_parameters(pp),
        Err(Error::InvalidPublicParameters(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// "Verification must re-impose what the algebra drops"
// ---------------------------------------------------------------------------------------------

/// evaluation.tex, "Verification must re-impose what the algebra drops": "Each possession
/// verifier has to check the received credential encoding ... before evaluating the
/// discrete-logarithm clauses. It is easy to check these only in the ordinary credential
/// verifier and to omit them in the attestation verifier ... The omission is not theoretical:
/// the all-zero 48-byte encoding of a `G_1` element deserializes to the identity and
/// round-trips, so the resulting credential-free forgery travels on the wire."
///
/// Here: a credential-free show whose clauses hold under the adversary's key (`Σ-PS`: `(1, 1)`;
/// `Σ-BBS`: `(1, D, D)`) yields an attestation and a membership proof that pass the bare
/// Fiat–Shamir check, survive the compact and the canonical encoding unchanged, and are rejected
/// by the attestation verifier, the helper's count and the membership verifier
/// ([`Error::InvalidCredential`]), exactly as the credential verifier rejects the degenerate
/// credential itself.
///
/// On the encoding (a difference to the paper's wording, for this codec): the 48-byte encoding
/// of the identity of BLS12-381 `G_1` in arkworks is `0xc0 ‖ 0^47` (compression and infinity
/// flags); the all-zero string is REFUSED (the compression flag is unset).
fn public_checks_in_the_attestation_verifier<B: AdversarialBase, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
) {
    let dep = Deployment::<B, T>::new(label, 2, seed);
    let mut rng = StdRng::seed_from_u64(seed ^ 0x1e55);
    let identity = G1::zero().to_bytes().unwrap();
    assert_eq!(identity[0], 0xc0);
    assert!(identity[1..].iter().all(|byte| *byte == 0));
    assert!(G1::from_bytes(&identity).unwrap().is_zero());
    assert!(matches!(
        G1::from_bytes(&[0u8; 48]),
        Err(Error::Serialization(_))
    ));

    let newcomer = dep.pcreds.register(&dep.hvk, &mut rng).unwrap();
    let mut forged = Vec::new();
    for _ in 0..2 {
        let key = Fr::rand(&mut rng);
        let (show, extra) = B::credential_free_show(&dep.pcreds.params().base, &key, &mut rng);
        let witness: Vec<Fr> = core::iter::once(key).chain(extra).collect();
        let att = cheat_attestation(
            &dep.pcreds,
            &dep.hvk,
            newcomer.id(),
            show.clone(),
            &witness,
            &mut rng,
        )
        .expect("the clauses hold");
        let proof = cheat_membership(&dep.pcreds, &dep.hvk, b"m", show, &witness, &mut rng)
            .expect("the clauses hold");
        let att = Attestation::<Bk<B, T>>::from_compact_bytes(&att.to_compact_bytes().unwrap())
            .expect("the forgery travels on the wire");
        let att = serialization::from_bytes::<Attestation<Bk<B, T>>>(
            &serialization::to_bytes(&att).unwrap(),
        )
        .expect("in both encodings");
        let proof =
            MembershipProof::<Bk<B, T>>::from_compact_bytes(&proof.to_compact_bytes().unwrap())
                .unwrap();
        assert_eq!(
            dep.pcreds.check_attestation(&dep.hvk, newcomer.id(), &att),
            Err(Error::InvalidCredential)
        );
        assert_eq!(
            dep.pcreds.check_membership(&dep.hvk, b"m", &proof),
            Err(Error::InvalidCredential)
        );
        forged.push(att);
    }
    let evaluated = evaluate_with(&dep, &newcomer, forged, b"r", &mut rng);
    assert!(evaluated.tags().is_empty());
    assert_eq!(
        dep.pcreds
            .credential(&dep.hvk, &newcomer, B::degenerate_credential(&mut rng))
            .err(),
        Some(Error::InvalidCredential)
    );
}

#[test]
fn public_checks_in_the_attestation_verifier_ps_ddh() {
    public_checks_in_the_attestation_verifier::<PS, DDH>(b"adv/lesson/ps+ddh", 0xad1e_0001);
}

#[test]
fn public_checks_in_the_attestation_verifier_bbs_dy() {
    public_checks_in_the_attestation_verifier::<BBS, DY>(b"adv/lesson/bbs+dy", 0xad1e_0002);
}

// ---------------------------------------------------------------------------------------------
// A second pairing
// ---------------------------------------------------------------------------------------------

/// `G_1` of BN254.
type BnG1 = <Bn254 as Pairing>::G1;
/// The scalar field of BN254.
type BnFr = <Bn254 as Pairing>::ScalarField;
/// `Tag_DDH` over BN254 `G_1`.
type DDH2<H> = kiprf::DDH<BnG1, H>;
/// `Tag_DY` over BN254 `G_1`.
type DY2<H> = kiprf::DY<BnG1, H>;

/// A1 over a second pairing, BN254: the credential-free forgeries and the identity tag are
/// rejected by the same checks as over BLS12-381 (the negative half of the conformance flows of
/// the earlier construction, which ran over both curves). arkworks
/// ships no hash-to-curve suite for BN254, so `htag` and the generators of `Σ-BBS` come from the
/// INSECURE test oracle [`InsecureExponentHasher`] (known discrete logarithms): the runs show
/// that the library code is generic over the pairing, not that BN254 is a supported
/// deployment. The forgeries do not use the known logarithms.
fn a1_over_bn254<B: Base<Bn254>, T: ProtocolTag<BnG1> + 'static>(
    label: &[u8],
    seed: u64,
    forgery: impl Fn(&B::Params, &BnFr, &mut StdRng) -> (B::Show, Vec<BnFr>),
) {
    type Backend2<B, T> = PairingBackend<Bn254, B, T>;
    let mut rng = StdRng::seed_from_u64(seed);
    let pcreds = Protocol::<Backend2<B, T>>::setup(label).unwrap();
    let mut helper = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let hvk = pcreds.helper_key(helper.key().vk()).unwrap();
    let member = pcreds.register(&hvk, &mut rng).unwrap();
    let cred = admit_root(&pcreds, &mut helper, &hvk, &member, b"root", &mut rng);
    let newcomer = pcreds.register(&hvk, &mut rng).unwrap();
    let request = pcreds
        .request_attestation(&hvk, &newcomer, b"s", b"c", &mut rng)
        .unwrap();
    let pending = pcreds
        .receive_attestation_request(&hvk, &request, b"s", b"c")
        .unwrap();
    let honest = pcreds
        .attest(&hvk, &member, &cred, pending, &mut rng)
        .unwrap();
    assert_eq!(
        pcreds.check_attestation(&hvk, newcomer.id(), &honest),
        Ok(())
    );

    let xq = pcreds.recipient_point(hvk.vk(), newcomer.id()).unwrap();
    let ctx = pcreds.attestation_context(hvk.vk()).unwrap();
    let mut tags = Vec::new();
    for _ in 0..2 {
        let key = BnFr::rand(&mut rng);
        let (show, extra) = forgery(&pcreds.params().base, &key, &mut rng);
        let tag = <Backend2<B, T> as Backend>::tag(pcreds.params(), &key, &xq).unwrap();
        let relation =
            <Backend2<B, T>>::attestation_relation(pcreds.params(), hvk.vk(), &show, &tag, &xq)
                .unwrap();
        let witness: Vec<BnFr> = core::iter::once(key).chain(extra).collect();
        let proof = fiat_shamir::prove(&relation, &witness, &ctx, &mut rng)
            .expect("the clauses of the credential-free show hold");
        assert!(fiat_shamir::verify(&relation, &ctx, &proof));
        let att = Attestation { tag, show, proof };
        assert_eq!(
            pcreds.check_attestation(&hvk, newcomer.id(), &att),
            Err(Error::InvalidCredential)
        );
        tags.push(tag);
    }
    assert_ne!(tags[0], tags[1]);
    let identity = Attestation {
        tag: BnG1::zero(),
        ..honest
    };
    assert_eq!(
        pcreds.check_attestation(&hvk, newcomer.id(), &identity),
        Err(Error::InvalidTag)
    );
}

/// `σ' = (1, 1)` of `Σ-PS` over BN254.
fn ps_identity_show(_pp: &(), _key: &BnFr, rng: &mut StdRng) -> (PSPair<Bn254>, Vec<BnFr>) {
    let zero = BnG1::zero();
    (PSPair { s1: zero, s2: zero }, vec![BnFr::rand(rng)])
}

/// `(1, D, D)` of `Σ-BBS` over BN254, `D = B(K, ρ)`; the witness `(ρ, 1, e, 1, 1, v)`.
fn bbs_identity_show(
    pp: &BBSParams<Bn254>,
    key: &BnFr,
    rng: &mut StdRng,
) -> (BBSShow<Bn254>, Vec<BnFr>) {
    let rho = BnFr::rand(rng);
    let d = pp.b(key, &rho);
    let one = BnFr::one();
    let show = BBSShow {
        a_bar: BnG1::zero(),
        b_bar: d,
        d,
    };
    (
        show,
        vec![rho, one, BnFr::rand(rng), one, one, BnFr::rand(rng)],
    )
}

#[test]
fn a1_over_bn254_ps() {
    a1_over_bn254::<pairing::PS, DDH2<InsecureExponentHasher>>(
        b"adv/bn254/ps+ddh",
        0xadb2_0001,
        ps_identity_show,
    );
    a1_over_bn254::<pairing::PS, DY2<InsecureExponentHasher>>(
        b"adv/bn254/ps+dy",
        0xadb2_0002,
        ps_identity_show,
    );
}

#[test]
fn a1_over_bn254_bbs() {
    a1_over_bn254::<pairing::BBS<InsecureExponentHasher>, DDH2<InsecureExponentHasher>>(
        b"adv/bn254/bbs+ddh",
        0xadb2_0003,
        bbs_identity_show,
    );
    a1_over_bn254::<pairing::BBS<InsecureExponentHasher>, DY2<InsecureExponentHasher>>(
        b"adv/bn254/bbs+dy",
        0xadb2_0004,
        bbs_identity_show,
    );
}
