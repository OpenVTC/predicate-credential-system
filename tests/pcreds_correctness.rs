//! Correctness of the protocol `Π_PCreds` (`predicate_credential_system::pcreds`, paper §5.2)
//! through the PUBLIC API, for the four pairing-based instantiations of §6 (`Σ-PS`, `Σ-BBS` ×
//! `Tag_DDH`, `Tag_DY` over BLS12-381) and, for genericity, over BN254. This is what has to hold
//! for the protocol to be usable at all, with the negatives that each hinge on ONE check of the
//! protocol box; the adversarial suites are separate files.
//!
//! # Map to the protocol box
//!
//! The protocol box of `Π_PCreds` is pcreds-protocol.tex, lines 346-443; the numbers in
//! parentheses are its lines.
//!
//! | protocol box | tests |
//! |---|---|
//! | Inputs (347-348): `pp`, `hvk`, `Pol_k`; "users return `⊥` if `hvk ∉ V_pp`" | `Net::on` (every user checks `hvk` once), `any_number_of_attestations_and_an_optional_limit` (`Pol_k` with `k ≥ 1`, `|N''| ≥ k` among any number of attestations, the optional limit) |
//! | `Setup` (350) | `received_public_parameters_must_be_the_derived_ones`, `objects_of_one_deployment_are_refused_in_another`, the correctness flows (`pp` travels) |
//! | `Helper` (352): `(hvk, sk) ← KeyGen(pp)`, `I ← ∅` | `helper_restarts_keep_the_key_and_the_record`, `a_helper_key_serves_one_deployment` |
//! | `Register` (354-357): `usk` until `Tag(usk, x_0) ≠ ⊥` | `users_from_keys_and_from_storage`, `tag_dy_attester_at_its_undefined_point` |
//! | `ContactRegister` (359-362) | none: routes are the contact service's; a contact name is a byte string here |
//! | `AttestationRequest` (364-376): `π_id` under `(ssid, P̃)`, checked by the owner of `P̃` | `identifier_proofs_are_bound_to_session_contact_and_identifier` |
//! | `AttestationRequestResponse` (378-397): `t_{P→Q} = Tag(usk_P, x_Q)`, `σ*`, `π_att`; `Q` checks | `attestations_are_bound_to_their_recipient`, `tag_dy_attester_at_its_undefined_point` |
//! | `CredentialRequest` (399-416): `Ĉ`, `π_iss` under `(ssid, att⃗)`; the helper checks `π_iss`, computes `N''` and `v` | `issuance_proofs_are_bound_to_session_and_attestations`, `the_helper_counts_distinct_valid_tags`, `any_number_of_attestations_and_an_optional_limit` |
//! | `CredentialRequestResponse` (418-426): `Fail`, `issued`, `σ̂ ← BlindIssue(sk, Ĉ)`; `Unblind` and `Verify` | the correctness flows, `root_admission_is_the_helpers_decision`, `a_member_attesting_for_itself_is_answered_issued`, `a_delayed_reply_is_unblinded_with_the_stored_state`, `a_failing_store_releases_nothing`, `helper_processes_sharing_a_store_issue_once`, `unblind_rejects_garbage_pre_credentials`, `issuance_states_are_per_request` |
//! | `Prove` (428-437), `Verify` (439-442) | `membership_proofs_are_bound_to_message_key_and_holder`, the correctness flows |
//! | across the box: one deployment, one helper key | `helper_keys_bind_every_object`, `objects_of_one_deployment_are_refused_in_another`, `a_helper_key_serves_one_deployment` |
//!
//! Two rules of the box hold by the TYPES of the API and have no negative test: an attester
//! answers only a `PendingAttestation`, which exists only after `π_id` was checked (line 374),
//! and the helper responds only to an `EvaluatedRequest`, which exists only after `π_iss` was
//! checked (line 413), so that issuance is gated by the issuance proof.
//!
//! # Conventions
//!
//! Every run is seeded (`StdRng::seed_from_u64`; the seed is a literal at every call site).
//! Sizes are those of the fixed-format compact encoding (`pcreds::codec`) unless said otherwise;
//! the expected values are counted from the objects of §6.2 in `expected_sizes`, independently
//! of the constants of the library. The BN254 runs put the INSECURE test oracle
//! `hash::testing::InsecureExponentHasher` behind every hash-to-group oracle: they show that the
//! code is generic over the pairing, not that BN254 is a supported deployment.
//!
//! This suite replaces `tests/pcs_correctness.rs` of the earlier construction (`pcs::PCS`). Its
//! tests of what no longer exists (`Σ-EQ`, predicate labels and attribute policies, the
//! self-exclusion tag `T_0`, the separate root path) have no counterpart here.

#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

mod common;

use std::{cell::RefCell, rc::Rc};

use ark_bls12_381::Fr;
use ark_bn254::Bn254;
use ark_ec::{PrimeGroup, pairing::Pairing};
use ark_ff::{One, UniformRand, Zero};
use ark_serialize::CanonicalSerialize;
use common::{BBS, Bk, DDH, DY, E, G1, PS};
use predicate_credential_system::{
    Error,
    hash::{HashToGroup, bls12_381::G1Hasher, testing::InsecureExponentHasher},
    kiprf::{self, ProtocolTag},
    pcreds::{
        Attestation, AttestationRequest, Backend, Credential, CredentialRequest, Decision,
        EvaluatedRequest, Helper, HelperKey, IssuanceRecord, IssuanceState, IssuanceStore,
        MembershipProof, Policy, ProofKind, Protocol, PublicParameters, Reply, User,
        pairing::{self, BBSParams, BBSPreCredential, Base, PSPair, PairingBackend, PairingParams},
    },
    serialization::{self, WireFormat},
    sigma::fiat_shamir,
};
use rand::{SeedableRng, rngs::StdRng};

/// A copy of an issuance state, through its encoding: `unblind` consumes the state, and a test
/// that tries several pre-credentials stores the state and reads it back for each.
fn copy<Bk: Backend>(state: &IssuanceState<Bk>) -> IssuanceState<Bk> {
    IssuanceState::from_bytes(&state.to_bytes().expect("τ encodes")).expect("τ decodes")
}

// ---------------------------------------------------------------------------------------------
// The two bases
// ---------------------------------------------------------------------------------------------

/// What this suite needs to know about a credential base beyond `Base`: the layout of its
/// objects (§6.2), counted here independently of the constants of the library, and the one kind
/// of negative case in which the two bases answer differently.
trait BaseFacts {
    /// `G_1` elements of a show `σ*`: `(σ'_1, σ'_2)` of `Σ-PS`; `(Ā, B̄, D)` of `Σ-BBS`.
    const SHOW_G1: usize;
    /// Responses of `π_att` and of `π_prove`, one per variable of `R_Possess` (the tag clause of
    /// `R_att` is linear in `usk` and adds none): `z_usk, z_t` for `Σ-PS`;
    /// `z_usk, z_ρ, z_{r_1}, z_e, z_{r_3}, z_u, z_v` for `Σ-BBS`.
    const POSSESSION_RESPONSES: usize;
    /// `(G_1, Z_p)` elements of a pre-credential `σ̂`: `(σ_1, σ_2)` of `Σ-PS`; `(A, e)` of `Σ-BBS`.
    const PRE_CREDENTIAL: (usize, usize);
    /// `(G_1, Z_p)` elements of a credential `σ`: `(σ_1, σ_2)` of `Σ-PS`; `(A, e, ρ)` of `Σ-BBS`.
    const CREDENTIAL: (usize, usize);
    /// Whether the public check of a show is a pairing equation in `hvk`: `e(Ā, X̃) = e(B̄, g̃)`
    /// for `Σ-BBS`, whereas `Σ-PS` checks `σ'_1 ≠ 1` only.
    const SHOW_HAS_PAIRING_CHECK: bool;
}

impl BaseFacts for pairing::PS {
    const SHOW_G1: usize = 2;
    const POSSESSION_RESPONSES: usize = 2;
    const PRE_CREDENTIAL: (usize, usize) = (2, 0);
    const CREDENTIAL: (usize, usize) = (2, 0);
    const SHOW_HAS_PAIRING_CHECK: bool = false;
}

impl<H> BaseFacts for pairing::BBS<H> {
    const SHOW_G1: usize = 3;
    const POSSESSION_RESPONSES: usize = 7;
    const PRE_CREDENTIAL: (usize, usize) = (1, 1);
    const CREDENTIAL: (usize, usize) = (1, 2);
    const SHOW_HAS_PAIRING_CHECK: bool = true;
}

/// Responses of `π_iss`: `z_usk` and `z_ρ` of `R_iss` (`C = g_1^ρ Y^usk` for `Σ-PS`,
/// `C h_0^{-1} = h_u^usk h_r^ρ` for `Σ-BBS`, the tag clause at `(id, x_0)` adding none).
const ISSUANCE_RESPONSES: usize = 2;
/// Responses of `π_id`: `z_usk` of `R_Tag`.
const IDENTIFIER_RESPONSES: usize = 1;

/// The rejection of an honest show checked under ANOTHER helper key (an attestation or a
/// membership proof): the public pairing check under `Σ-BBS`, the proof under `Σ-PS`, whose
/// public check does not involve the key.
fn foreign_key_error<B: BaseFacts>() -> Error {
    if B::SHOW_HAS_PAIRING_CHECK {
        Error::InvalidCredential
    } else {
        Error::InvalidProof
    }
}

/// What becomes of a show made from a credential that does not belong to `(usk, hvk)` (another
/// holder's, or one issued under another key): under `Σ-PS` the honest prover refuses, because
/// `ReRand` does not use `usk` and `R_Possess` then has no witness; under `Σ-BBS` `ReRand` uses
/// the CLAIMED `usk`, the clauses hold, and the public pairing check of the show fails.
fn assert_foreign_credential_refused<B: BaseFacts, V>(
    made: Result<V, Error>,
    check: impl FnOnce(&V) -> Result<(), Error>,
) {
    match made {
        Err(error) => {
            assert!(!B::SHOW_HAS_PAIRING_CHECK, "unexpected refusal: {error:?}");
            assert_eq!(error, Error::WitnessDoesNotSatisfyRelation);
        }
        Ok(value) => {
            assert!(B::SHOW_HAS_PAIRING_CHECK, "Σ-PS must refuse the witness");
            assert_eq!(check(&value), Err(Error::InvalidCredential));
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Sizes
// ---------------------------------------------------------------------------------------------

/// Sizes in bytes of the objects of a flow at threshold `k`. Everything is the compact encoding
/// (`pcreds::codec`) except `credential`, which is not a message (canonical encoding).
#[derive(Debug, PartialEq, Eq)]
struct Sizes {
    /// `id_Q ‖ π_id`.
    attestation_request: usize,
    /// `|att| = |t ‖ σ* ‖ π_att|`.
    attestation: usize,
    /// `|π|` of the paper: the `k` attestations, `Ĉ` and `π_iss` (`CredentialRequest::size`).
    request: usize,
    /// `σ* ‖ π_prove`.
    membership_proof: usize,
    /// The reply `σ̂`: one tag byte, then the pre-credential.
    reply: usize,
    /// `σ`.
    credential: usize,
}

/// The sizes counted from the objects of §6.2: a proof is its challenge and its responses, an
/// element is in its compressed encoding (BLS12-381: `G_1` 48 B, `Z_p` 32 B; BN254: `G_1` 32 B,
/// `Z_p` 32 B), and the tag `t`, `id_Q` and `Ĉ` are one `G_1` element each.
fn expected_sizes<E: Pairing, B: BaseFacts>(k: usize) -> Sizes {
    let g1 = E::G1::generator().compressed_size();
    let fr = E::ScalarField::one().compressed_size();
    let attestation = g1 + B::SHOW_G1 * g1 + (1 + B::POSSESSION_RESPONSES) * fr;
    Sizes {
        attestation_request: g1 + (1 + IDENTIFIER_RESPONSES) * fr,
        attestation,
        request: k * attestation + g1 + (1 + ISSUANCE_RESPONSES) * fr,
        membership_proof: B::SHOW_G1 * g1 + (1 + B::POSSESSION_RESPONSES) * fr,
        reply: 1 + B::PRE_CREDENTIAL.0 * g1 + B::PRE_CREDENTIAL.1 * fr,
        credential: B::CREDENTIAL.0 * g1 + B::CREDENTIAL.1 * fr,
    }
}

// ---------------------------------------------------------------------------------------------
// A deployment and its members
// ---------------------------------------------------------------------------------------------

/// A credentialed user and the contact name through which it is asked for attestations
/// (`ContactRegister`, line 361: the route itself is the contact service's).
struct Member<Bk: Backend> {
    user: User<Bk>,
    cred: Credential<Bk>,
    contact: Vec<u8>,
}

/// A deployment of `Π_PCreds` for the instantiation `Bk`: the protocol (`pp`), the helper with
/// its record `I`, the helper key as the users checked it, a seeded RNG, and counters for fresh
/// sub-session identifiers and contact names.
struct Net<Bk: Backend> {
    pcreds: Protocol<Bk>,
    helper: Helper<Bk>,
    hvk: HelperKey<Bk>,
    rng: StdRng,
    sessions: u64,
    contacts: u64,
}

impl<Bk: Backend> Net<Bk> {
    /// The deployment `label` with a helper under `Pol_k` (no limit on attestations).
    fn new(label: &[u8], k: usize, seed: u64) -> Self {
        Self::with_policy(label, Policy::threshold(k).expect("k ≥ 1"), seed)
    }

    /// The deployment `label` with a helper under `policy`.
    fn with_policy(label: &[u8], policy: Policy, seed: u64) -> Self {
        Self::on(Protocol::setup(label).expect("Setup"), policy, seed)
    }

    /// `Helper` (line 352) on the protocol `pcreds`: `(hvk, sk) ← KeyGen(pp)` and `I ← ∅`; every
    /// user checks the published `hvk` once ("users return `⊥` if `hvk ∉ V_pp`", line 348).
    fn on(pcreds: Protocol<Bk>, policy: Policy, seed: u64) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        let helper = pcreds.helper_keygen(policy, &mut rng);
        assert!(helper.store().is_empty(), "I ← ∅");
        let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
        assert_eq!(&hvk, helper.key());
        Self {
            pcreds,
            helper,
            hvk,
            rng,
            sessions: 0,
            contacts: 0,
        }
    }

    /// A fresh sub-session identifier.
    fn ssid(&mut self) -> Vec<u8> {
        self.sessions += 1;
        format!("ssid-{}", self.sessions).into_bytes()
    }

    /// `Register` (line 356).
    fn register(&mut self) -> User<Bk> {
        let user = self
            .pcreds
            .register(&self.hvk, &mut self.rng)
            .expect("Register");
        assert_eq!(self.pcreds.check_user(&self.hvk, &user), Ok(()));
        user
    }

    /// An attestation from `member` for `user`, through the member's contact name.
    fn attestation(&mut self, member: &Member<Bk>, user: &User<Bk>) -> Attestation<Bk> {
        self.attestation_via(member, user, &member.contact)
    }

    /// `AttestationRequest` and `AttestationRequestResponse` (lines 364-397): `user` sends
    /// `(id_Q, π_id)` to the owner of the contact name `contact` (here `member`), who checks
    /// `π_id` and attests; `user` checks the attestation on receipt.
    fn attestation_via(
        &mut self,
        member: &Member<Bk>,
        user: &User<Bk>,
        contact: &[u8],
    ) -> Attestation<Bk> {
        let ssid = self.ssid();
        let request = self
            .pcreds
            .request_attestation(&self.hvk, user, &ssid, contact, &mut self.rng)
            .expect("π_id");
        let pending = self
            .pcreds
            .receive_attestation_request(&self.hvk, &request, &ssid, contact)
            .expect("the owner of P̃ checks π_id");
        assert_eq!(pending.id(), user.id());
        let att = self
            .pcreds
            .attest(
                &self.hvk,
                &member.user,
                &member.cred,
                pending,
                &mut self.rng,
            )
            .expect("attest");
        assert_eq!(
            self.pcreds.check_attestation(&self.hvk, user.id(), &att),
            Ok(())
        );
        att
    }

    /// `CredentialRequest` (line 401) under a fresh `ssid`: the ssid, the message for the
    /// helper, and the requester's state.
    fn request(
        &mut self,
        user: &User<Bk>,
        attestations: Vec<Attestation<Bk>>,
    ) -> (Vec<u8>, CredentialRequest<Bk>, IssuanceState<Bk>) {
        let ssid = self.ssid();
        let (message, state) = self
            .pcreds
            .request_credential(&self.hvk, user, attestations, &ssid, &mut self.rng)
            .expect("CredentialRequest");
        (ssid, message, state)
    }

    /// The helper on a credential request (line 411).
    fn try_evaluate(
        &self,
        message: &CredentialRequest<Bk>,
        ssid: &[u8],
    ) -> Result<EvaluatedRequest<Bk>, Error> {
        self.pcreds.evaluate_request(&self.helper, message, ssid)
    }

    /// `try_evaluate` of a request whose `π_iss` verifies.
    fn evaluate(&self, message: &CredentialRequest<Bk>, ssid: &[u8]) -> EvaluatedRequest<Bk> {
        self.try_evaluate(message, ssid).expect("π_iss")
    }

    /// `CredentialRequestResponse` (line 420) with the decision `decision`.
    fn respond(&mut self, evaluated: EvaluatedRequest<Bk>, decision: Decision) -> Reply<Bk> {
        self.pcreds
            .respond(&mut self.helper, evaluated, decision, &mut self.rng)
            .expect("CredentialRequestResponse")
    }

    /// The helper's two steps on `message`.
    fn answer(
        &mut self,
        message: &CredentialRequest<Bk>,
        ssid: &[u8],
        decision: Decision,
    ) -> Reply<Bk> {
        let evaluated = self.evaluate(message, ssid);
        self.respond(evaluated, decision)
    }

    /// `Unblind` and the check `Verify` (line 423) of a reply that must be a pre-credential.
    fn unblind(
        &self,
        user: &User<Bk>,
        reply: Reply<Bk>,
        state: IssuanceState<Bk>,
    ) -> Credential<Bk> {
        let pre = match reply {
            Reply::PreCredential(pre) => pre,
            other => panic!("expected σ̂, got {other:?}"),
        };
        let cred = self
            .pcreds
            .unblind(&self.hvk, user, &pre, state)
            .expect("Unblind");
        assert!(self.pcreds.verify_credential(&self.hvk, user, &cred));
        cred
    }

    /// The member `user` with the credential `cred` and a fresh contact name.
    fn member(&mut self, user: User<Bk>, cred: Credential<Bk>) -> Member<Bk> {
        self.contacts += 1;
        Member {
            user,
            cred,
            contact: format!("member-{}@example", self.contacts).into_bytes(),
        }
    }

    /// A root user (Remark "Root users and chaining"): an ordinary request without
    /// attestations, admitted by the helper's decision `d = root`.
    fn admit_root(&mut self, user: User<Bk>) -> Member<Bk> {
        let (ssid, message, state) = self.request(&user, Vec::new());
        let reply = self.answer(&message, &ssid, Decision::Root);
        let cred = self.unblind(&user, reply, state);
        self.member(user, cred)
    }

    /// `n` fresh root users.
    fn roots(&mut self, n: usize) -> Vec<Member<Bk>> {
        (0..n)
            .map(|_| {
                let user = self.register();
                self.admit_root(user)
            })
            .collect()
    }

    /// A newcomer admitted with `d = policy` on `attestations`.
    fn join(&mut self, user: User<Bk>, attestations: Vec<Attestation<Bk>>) -> Member<Bk> {
        let (ssid, message, state) = self.request(&user, attestations);
        let reply = self.answer(&message, &ssid, Decision::Policy);
        let cred = self.unblind(&user, reply, state);
        self.member(user, cred)
    }

    /// A newcomer's issuance with every reply of `CredentialRequestResponse` (line 420), on `k`
    /// attestations from distinct sources:
    ///
    /// 1. the first `k − 1` alone: `|N''| = k − 1`, `v = invalid`, `d = policy`: `Fail`, and `I`
    ///    is unchanged;
    /// 2. all `k` in a new request (an attestation has no session context and "may be used in
    ///    several credential requests", line 389): `σ̂`, and `id_Q` enters `I`;
    /// 3. the same once more: `issued`, which carries nothing; the requester keeps the credential
    ///    of step 2 (line 421).
    fn join_with_every_reply(
        &mut self,
        user: User<Bk>,
        attestations: Vec<Attestation<Bk>>,
    ) -> Member<Bk> {
        let k = self.helper.policy().k();
        assert_eq!(attestations.len(), k);
        let before = self.helper.store().len();

        let (ssid, short, _) = self.request(&user, attestations[..k - 1].to_vec());
        let evaluated = self.evaluate(&short, &ssid);
        assert_eq!(evaluated.tags().len(), k - 1);
        assert!(!evaluated.is_valid());
        assert_eq!(self.respond(evaluated, Decision::Policy), Reply::Fail);
        assert_eq!(self.helper.store().len(), before, "Fail records nothing");

        let (ssid, message, state) = self.request(&user, attestations.clone());
        let evaluated = self.evaluate(&message, &ssid);
        let tags: Vec<Bk::Tag> = attestations.iter().map(|att| att.tag.clone()).collect();
        assert_eq!(
            (evaluated.ssid(), evaluated.id(), evaluated.tags()),
            (&ssid[..], user.id(), &tags[..])
        );
        assert!(evaluated.is_valid());
        let reply = self.respond(evaluated, Decision::Policy);
        assert_eq!(self.helper.store().len(), before + 1);
        let cred = self.unblind(&user, reply, state);

        let (ssid, again, _) = self.request(&user, attestations);
        assert_eq!(self.answer(&again, &ssid, Decision::Policy), Reply::Issued);
        assert_eq!(self.helper.store().len(), before + 1);
        assert!(self.pcreds.verify_credential(&self.hvk, &user, &cred));
        self.member(user, cred)
    }
}

// ---------------------------------------------------------------------------------------------
// Correctness and chaining, for every pair and over a second pairing
// ---------------------------------------------------------------------------------------------

/// The whole protocol box at threshold `k`, with CHAINING over several generations (Remark
/// "Root users and chaining"): `k` root users; two generations of `k` newcomers, each attested
/// by the `k` members of the generation before and by nobody else; a last newcomer attested by
/// the second generation, whose messages go through the compact codec; it attests in turn and
/// proves membership on a message. Every credential past the roots traces back to them through
/// attestations only. Returns the sizes of what it sent.
fn correctness_flow<E, B, T>(label: &[u8], seed: u64, k: usize) -> Sizes
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let mut net = Net::<PairingBackend<E, B, T>>::new(label, k, seed);

    // Setup (line 350): pp travels as bytes, and its receiver accepts it as the derived one.
    let bytes = net.pcreds.public_parameters().to_bytes().expect("pp");
    let received = PublicParameters::<PairingBackend<E, B, T>>::from_bytes(&bytes).expect("pp");
    let rebuilt = Protocol::from_public_parameters(received).expect("the derived pp");
    assert_eq!(rebuilt.parameters_digest(), net.pcreds.parameters_digest());

    // Generation 0: the root users. Generations 1 and 2: attested by the generation before.
    let mut generation = net.roots(k);
    for _ in 1..=2 {
        let mut next = Vec::with_capacity(k);
        for i in 0..k {
            let user = net.register();
            let attestations: Vec<_> = generation
                .iter()
                .map(|member| net.attestation(member, &user))
                .collect();
            next.push(if i == 0 {
                net.join_with_every_reply(user, attestations)
            } else {
                net.join(user, attestations)
            });
        }
        generation = next;
    }

    // Generation 3: one newcomer, every message through the compact codec (`pcreds::codec`).
    let user = net.register();
    let source = &generation[0];
    let ssid = net.ssid();
    let request = net
        .pcreds
        .request_attestation(&net.hvk, &user, &ssid, &source.contact, &mut net.rng)
        .expect("π_id");
    let request_bytes = request.to_compact_bytes().expect("compact");
    assert_eq!(request_bytes.len(), request.compact_size());
    let decoded = AttestationRequest::from_compact_bytes(&request_bytes).expect("decodes");
    assert_eq!(decoded, request);
    // The derived canonical encoding length-prefixes the responses of π_id (a u64: 8 bytes).
    assert_eq!(
        request.to_bytes().expect("canonical").len(),
        request_bytes.len() + 8
    );
    let pending = net
        .pcreds
        .receive_attestation_request(&net.hvk, &decoded, &ssid, &source.contact)
        .expect("π_id");
    let att = net
        .pcreds
        .attest(&net.hvk, &source.user, &source.cred, pending, &mut net.rng)
        .expect("attest");
    let att_bytes = att.to_compact_bytes().expect("compact");
    assert_eq!(att_bytes.len(), att.size());
    let decoded = Attestation::from_compact_bytes(&att_bytes).expect("decodes");
    assert_eq!(decoded, att);
    assert_eq!(
        net.pcreds.check_attestation(&net.hvk, user.id(), &decoded),
        Ok(())
    );
    assert_eq!(
        Attestation::from_bytes(&att.to_bytes().expect("canonical")).expect("decodes"),
        att
    );
    assert_eq!(
        att.to_bytes().expect("canonical").len(),
        att_bytes.len() + 8
    );

    let mut attestations = vec![decoded];
    attestations.extend(
        generation[1..]
            .iter()
            .map(|member| net.attestation(member, &user)),
    );
    let (ssid, message, state) = net.request(&user, attestations);
    let message_bytes = message.to_compact_bytes().expect("compact");
    assert_eq!(message_bytes.len(), message.compact_size());
    // "the wire format adds id_Q and the count" (a 4-byte count) to |π|
    assert_eq!(
        message.compact_size(),
        message.id.compressed_size() + 4 + message.size()
    );
    let decoded = CredentialRequest::from_compact_bytes(&message_bytes).expect("decodes");
    assert_eq!(decoded, message);
    // Canonical: a u64 count instead of the u32 (+4), and a u64 length prefix in each of the
    // k + 1 proofs (+8 each).
    assert_eq!(
        message.to_bytes().expect("canonical").len(),
        message_bytes.len() + 4 + 8 * (k + 1)
    );
    let evaluated = net.evaluate(&decoded, &ssid);
    assert!(evaluated.is_valid());
    let reply = net.respond(evaluated, Decision::Policy);
    let reply_bytes = reply.to_compact_bytes().expect("compact");
    assert_eq!(reply_bytes.len(), reply.compact_size());
    assert_eq!(reply_bytes, reply.to_bytes().expect("canonical"));
    let reply = Reply::from_compact_bytes(&reply_bytes).expect("decodes");
    let cred = net.unblind(&user, reply, state);
    let newest = net.member(user, cred);

    // The newest member attests for a later newcomer, and proves membership on a message.
    let later = net.register();
    net.attestation(&newest, &later);
    let proof = net
        .pcreds
        .prove(&net.hvk, &newest.user, &newest.cred, b"hello", &mut net.rng)
        .expect("Prove");
    let proof_bytes = proof.to_compact_bytes().expect("compact");
    assert_eq!(proof_bytes.len(), proof.size());
    let decoded = MembershipProof::from_compact_bytes(&proof_bytes).expect("decodes");
    assert_eq!(decoded, proof);
    assert_eq!(
        proof.to_bytes().expect("canonical").len(),
        proof_bytes.len() + 8
    );
    assert!(net.pcreds.verify(&net.hvk, b"hello", &decoded));
    assert!(!net.pcreds.verify(&net.hvk, b"goodbye", &decoded));

    // A credential is bound to its holder's key; I holds each of the 3k + 1 identifiers once.
    assert!(
        !net.pcreds
            .verify_credential(&net.hvk, &generation[0].user, &newest.cred)
    );
    assert_eq!(net.helper.store().len(), 3 * k + 1);

    Sizes {
        attestation_request: request_bytes.len(),
        attestation: att_bytes.len(),
        request: message.size(),
        membership_proof: proof_bytes.len(),
        reply: reply_bytes.len(),
        credential: newest.cred.to_bytes().expect("canonical").len(),
    }
}

#[test]
fn ps_with_tag_ddh_is_correct() {
    for (seed, k) in [(0xa11c_0001, 1), (0xa11c_0002, 2), (0xa11c_0005, 5)] {
        assert_eq!(
            correctness_flow::<E, PS, DDH>(b"pcreds/correctness/ps+ddh", seed, k),
            expected_sizes::<E, PS>(k)
        );
    }
}

#[test]
fn ps_with_tag_dy_is_correct() {
    for (seed, k) in [(0xa12c_0001, 1), (0xa12c_0002, 2), (0xa12c_0005, 5)] {
        assert_eq!(
            correctness_flow::<E, PS, DY>(b"pcreds/correctness/ps+dy", seed, k),
            expected_sizes::<E, PS>(k)
        );
    }
}

#[test]
fn bbs_with_tag_ddh_is_correct() {
    for (seed, k) in [(0xa13c_0001, 1), (0xa13c_0002, 2), (0xa13c_0005, 5)] {
        assert_eq!(
            correctness_flow::<E, BBS, DDH>(b"pcreds/correctness/bbs+ddh", seed, k),
            expected_sizes::<E, BBS>(k)
        );
    }
}

#[test]
fn bbs_with_tag_dy_is_correct() {
    for (seed, k) in [(0xa14c_0001, 1), (0xa14c_0002, 2), (0xa14c_0005, 5)] {
        assert_eq!(
            correctness_flow::<E, BBS, DY>(b"pcreds/correctness/bbs+dy", seed, k),
            expected_sizes::<E, BBS>(k)
        );
    }
}

/// The sizes of the paper's table `tab:sizes` (evaluation.tex, lines 11-24: BLS12-381,
/// compressed group elements, either tag), against the counts of `expected_sizes`, which the
/// correctness flows measure for every pair and `k`: `|att|`, `|π|` at `k = 5`, `|cred|` and the
/// membership proof.
#[test]
fn sizes_are_those_of_the_paper() {
    let (ps, bbs) = (expected_sizes::<E, PS>(5), expected_sizes::<E, BBS>(5));
    // Σ-PS: |att| = (t, σ'_1, σ'_2) 3·48 + (c, z_usk, z_t) 3·32; |π| = 5·240 + Ĉ 48 +
    // (c, z_usk, z_ρ) 3·32; σ = (σ_1, σ_2); π = (σ'_1, σ'_2) 2·48 + 3·32.
    assert_eq!(
        (
            ps.attestation,
            ps.request,
            ps.credential,
            ps.membership_proof
        ),
        (240, 1344, 96, 192)
    );
    // Σ-BBS: |att| = (t, Ā, B̄, D) 4·48 + (c and 7 responses) 8·32; |π| = 5·448 + 48 + 3·32;
    // σ = (A, e, ρ) 48 + 2·32; π = 3·48 + 8·32.
    assert_eq!(
        (
            bbs.attestation,
            bbs.request,
            bbs.credential,
            bbs.membership_proof
        ),
        (448, 2384, 112, 400)
    );
    // Beyond the table: id_Q ‖ π_id = 48 + 2·32, and the reply 1 ‖ σ̂ (σ̂ = 2·48, or 48 + 32).
    assert_eq!((ps.attestation_request, ps.reply), (112, 97));
    assert_eq!((bbs.attestation_request, bbs.reply), (112, 81));
    // |π| = k·|att| + |Ĉ| + |π_iss| for every k.
    for k in [1, 2, 5, 17] {
        assert_eq!(
            expected_sizes::<E, PS>(k).request,
            (3 * k + 1) * 48 + (3 * k + 3) * 32
        );
        assert_eq!(
            expected_sizes::<E, BBS>(k).request,
            (4 * k + 1) * 48 + (8 * k + 3) * 32
        );
    }
    // The counts of this suite agree with the library's (one response for usk, one per variable
    // the clauses of the base allocate).
    for (kind, ps_responses, bbs_responses) in [
        (
            ProofKind::Identifier,
            IDENTIFIER_RESPONSES,
            IDENTIFIER_RESPONSES,
        ),
        (
            ProofKind::Attestation,
            PS::POSSESSION_RESPONSES,
            BBS::POSSESSION_RESPONSES,
        ),
        (
            ProofKind::Possession,
            PS::POSSESSION_RESPONSES,
            BBS::POSSESSION_RESPONSES,
        ),
        (ProofKind::Issuance, ISSUANCE_RESPONSES, ISSUANCE_RESPONSES),
    ] {
        assert_eq!(PairingBackend::<E, PS, DDH>::responses(kind), ps_responses);
        assert_eq!(PairingBackend::<E, BBS, DY>::responses(kind), bbs_responses);
    }
}

type BnG1 = <Bn254 as Pairing>::G1;
type BnDDH = kiprf::DDH<BnG1, InsecureExponentHasher>;
type BnDY = kiprf::DY<BnG1, InsecureExponentHasher>;
type BnBBS = pairing::BBS<InsecureExponentHasher>;

/// The code is generic over the pairing: the whole correctness flow, with chaining, over BN254
/// for the four pairs (the INSECURE test oracle behind `htag`, the generator of `Tag_DY` and the
/// generators of `Σ-BBS`).
#[test]
fn round_trips_over_a_second_pairing_engine() {
    let runs = [
        (
            correctness_flow::<Bn254, PS, BnDDH>(b"pcreds/bn254/ps+ddh", 0xb254_0001, 2),
            expected_sizes::<Bn254, PS>(2),
        ),
        (
            correctness_flow::<Bn254, PS, BnDY>(b"pcreds/bn254/ps+dy", 0xb254_0002, 2),
            expected_sizes::<Bn254, PS>(2),
        ),
        (
            correctness_flow::<Bn254, BnBBS, BnDDH>(b"pcreds/bn254/bbs+ddh", 0xb254_0003, 2),
            expected_sizes::<Bn254, BnBBS>(2),
        ),
        (
            correctness_flow::<Bn254, BnBBS, BnDY>(b"pcreds/bn254/bbs+dy", 0xb254_0004, 1),
            expected_sizes::<Bn254, BnBBS>(1),
        ),
    ];
    for (measured, expected) in runs {
        assert_eq!(measured, expected);
    }
    // BN254 (G_1: 32 B compressed, Z_p: 32 B): |att| = 3·32 + 3·32 for Σ-PS, 4·32 + 8·32 for
    // Σ-BBS.
    assert_eq!(
        (
            expected_sizes::<Bn254, PS>(2).attestation,
            expected_sizes::<Bn254, BnBBS>(2).attestation
        ),
        (192, 384)
    );
}

// ---------------------------------------------------------------------------------------------
// CredentialRequestResponse: Fail, issued, root admission
// ---------------------------------------------------------------------------------------------

/// Remark "Root users and chaining": `Pol_k` "never accepts a first request", so the helper
/// admits root users by its decision `d = root` on an ORDINARY request, which issues
/// regardless of the policy value (line 420). It bypasses neither the record `I` nor `π_iss`.
fn root_admission<Bk: Backend>(label: &[u8], seed: u64) {
    let mut net = Net::<Bk>::new(label, 2, seed);
    let user = net.register();
    let (ssid, message, state) = net.request(&user, Vec::new());
    let evaluated = net.evaluate(&message, &ssid);
    assert!(evaluated.tags().is_empty());
    assert!(!evaluated.is_valid());
    assert_eq!(net.respond(evaluated, Decision::Policy), Reply::Fail);
    assert!(net.helper.store().is_empty());
    // `respond` consumed the evaluated request ("pending state is consumed on completion",
    // line 348); to admit the requester, the helper evaluates the same message again.
    let reply = net.answer(&message, &ssid, Decision::Root);
    let cred = net.unblind(&user, reply, state);
    let root = net.member(user, cred);

    // d = root issues below the threshold as well (k − 1 = 1 attestation), with the ordinary
    // format: the root user attests like any member.
    let newcomer = net.register();
    let att = net.attestation(&root, &newcomer);
    let (ssid, message, state) = net.request(&newcomer, vec![att]);
    let evaluated = net.evaluate(&message, &ssid);
    assert_eq!(evaluated.tags().len(), 1);
    assert!(!evaluated.is_valid());
    let reply = net.respond(evaluated, Decision::Root);
    net.unblind(&newcomer, reply, state);
    assert_eq!(net.helper.store().len(), 2);

    // d = root does not bypass I ...
    let (ssid, message, _) = net.request(&root.user, Vec::new());
    assert_eq!(net.answer(&message, &ssid, Decision::Root), Reply::Issued);
    // ... nor π_iss: a request whose proof fails has no evaluation for any decision to answer.
    let stranger = net.register();
    let (_, message, _) = net.request(&stranger, Vec::new());
    assert_eq!(
        net.try_evaluate(&message, b"not the ssid of the request")
            .err(),
        Some(Error::InvalidProof)
    );
    assert_eq!(net.helper.store().len(), 2);
}

#[test]
fn root_admission_is_the_helpers_decision() {
    root_admission::<Bk<PS, DDH>>(b"pcreds/root/ps+ddh", 0x2001_0001);
    root_admission::<Bk<PS, DY>>(b"pcreds/root/ps+dy", 0x2001_0002);
    root_admission::<Bk<BBS, DDH>>(b"pcreds/root/bbs+ddh", 0x2001_0003);
    root_admission::<Bk<BBS, DY>>(b"pcreds/root/bbs+dy", 0x2001_0004);
}

/// The self-exclusion tag `T_0` of the earlier construction is gone: "the helper keeps the set
/// `I` of identifiers it has issued to, issues at most once per identifier, and answers later
/// valid requests with `issued`" (`pcreds` module docs). A member's attestation for its OWN
/// identifier is a valid attestation and counts, but a member is in `I`.
fn self_attestation<Bk: Backend>(label: &[u8], seed: u64) {
    let mut net = Net::<Bk>::new(label, 2, seed);
    let members = net.roots(2);
    let me = &members[0];
    let own = net.attestation(me, &me.user);
    let other = net.attestation(&members[1], &me.user);
    let (ssid, message, _) = net.request(&me.user, vec![own, other]);
    let evaluated = net.evaluate(&message, &ssid);
    assert_eq!(evaluated.tags().len(), 2);
    assert!(evaluated.is_valid());
    assert_eq!(net.respond(evaluated, Decision::Policy), Reply::Issued);
    assert_eq!(net.helper.store().len(), 2);
}

#[test]
fn a_member_attesting_for_itself_is_answered_issued() {
    self_attestation::<Bk<PS, DDH>>(b"pcreds/self/ps+ddh", 0x5e1f_0001);
    self_attestation::<Bk<BBS, DY>>(b"pcreds/self/bbs+dy", 0x5e1f_0002);
}

/// Remark "Concurrency": "an honest helper records its first issuance to an identifier before
/// releasing the response, so delaying a reply leaves the reservation intact". The requester
/// stores its `IssuanceState` (`τ`) until the reply arrives; a second request meanwhile is
/// answered `issued`, which carries nothing, and the requester keeps nothing of it (line 421:
/// "otherwise it retains the acknowledgement until it receives a credential"). The delayed `σ̂`
/// unblinds with the RESTORED state of the first request.
fn delayed_reply<Bk: Backend>(label: &[u8], seed: u64) {
    let mut net = Net::<Bk>::new(label, 1, seed);
    let root = net.roots(1).pop().expect("a root");
    let user = net.register();
    let att = net.attestation(&root, &user);
    let (ssid, message, state) = net.request(&user, vec![att.clone()]);
    let stored = state.to_bytes().expect("τ encodes");
    drop(state);
    let delayed = net.answer(&message, &ssid, Decision::Policy);

    // Asked again before σ̂ arrives, the helper answers `issued`: one tag byte, nothing else.
    let (ssid, again, state_again) = net.request(&user, vec![att]);
    let reply = net.answer(&again, &ssid, Decision::Policy);
    assert_eq!(reply, Reply::Issued);
    assert_eq!(reply.to_compact_bytes().expect("compact"), [1u8]);
    let Reply::PreCredential(pre) = delayed else {
        panic!("the first request was issued");
    };
    // σ̂ was issued on the first Ĉ: the state of the second request does not unblind it.
    assert_eq!(
        net.pcreds.unblind(&net.hvk, &user, &pre, state_again).err(),
        Some(Error::InvalidPreCredential)
    );

    // The state read back from storage belongs to its requester and its deployment ...
    let restored = IssuanceState::<Bk>::from_bytes(&stored).expect("τ decodes");
    assert_eq!(
        net.pcreds
            .unblind(&net.hvk, &root.user, &pre, copy(&restored))
            .err(),
        Some(Error::IssuanceStateMismatch)
    );
    let elsewhere = Protocol::<Bk>::setup(b"pcreds/delayed/another deployment").expect("Setup");
    let helper_elsewhere =
        elsewhere.helper_keygen(Policy::threshold(1).expect("k ≥ 1"), &mut net.rng);
    let user_elsewhere = elsewhere
        .register(helper_elsewhere.key(), &mut net.rng)
        .expect("Register");
    assert_eq!(
        elsewhere
            .unblind(
                helper_elsewhere.key(),
                &user_elsewhere,
                &pre,
                copy(&restored)
            )
            .err(),
        Some(Error::IssuanceStateMismatch)
    );
    // ... and unblinds the delayed σ̂.
    net.unblind(&user, Reply::PreCredential(pre), restored);
    assert_eq!(net.helper.store().len(), 2);
}

#[test]
fn a_delayed_reply_is_unblinded_with_the_stored_state() {
    delayed_reply::<Bk<PS, DDH>>(b"pcreds/delayed/ps+ddh", 0xde1a_0001);
    delayed_reply::<Bk<PS, DY>>(b"pcreds/delayed/ps+dy", 0xde1a_0002);
    delayed_reply::<Bk<BBS, DDH>>(b"pcreds/delayed/bbs+ddh", 0xde1a_0003);
    delayed_reply::<Bk<BBS, DY>>(b"pcreds/delayed/bbs+dy", 0xde1a_0004);
}

// ---------------------------------------------------------------------------------------------
// Bindings: recipient, session, contact name, helper key
// ---------------------------------------------------------------------------------------------

/// `AttestationRequestResponse` (lines 378-397): the tag `t_{P→Q} = Tag(usk_P, x_Q)` lives at the
/// recipient point `x_Q = H_req(⟨pp, hvk, id_Q⟩)`, and `π_att` "fixes the recipient through
/// `x_Q`" (line 389). `F_PCreds`, "Attestation tags": the tag is fixed for the pair (source,
/// recipient), "even through different contact names".
fn recipient_binding<E, B, T>(label: &[u8], seed: u64)
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let policy = Policy::threshold(2).expect("k ≥ 1");
    let mut net = Net::<PairingBackend<E, B, T>>::with_policy(label, policy, seed);
    let members = net.roots(2);
    let (q, r) = (net.register(), net.register());
    let att = net.attestation(&members[0], &q);

    // For id_Q, not for id_R; and the identity is not an identifier.
    assert_eq!(
        net.pcreds.check_attestation(&net.hvk, r.id(), &att),
        Err(Error::InvalidProof)
    );
    assert!(!net.pcreds.verify_attestation(&net.hvk, r.id(), &att));
    assert_eq!(
        net.pcreds.check_attestation(&net.hvk, &E::G1::zero(), &att),
        Err(Error::InvalidTag)
    );

    // One tag per (source, recipient), with a fresh show per attestation.
    let again = net.attestation_via(&members[0], &q, b"another contact name of member 0");
    assert_eq!(again.tag, att.tag);
    assert_ne!(again.show, att.show);
    let other_source = net.attestation(&members[1], &q);
    let other_recipient = net.attestation(&members[0], &r);
    assert_ne!(other_source.tag, att.tag);
    assert_ne!(other_recipient.tag, att.tag);

    // In R's credential request, Q's attestations count for nothing ...
    let for_q = vec![att.clone(), other_source.clone()];
    let (ssid, message, _) = net.request(&r, for_q.clone());
    let evaluated = net.evaluate(&message, &ssid);
    assert!(evaluated.tags().is_empty());
    assert_eq!(net.respond(evaluated, Decision::Policy), Reply::Fail);
    // ... and Q's own request, re-addressed to id_R, fails π_iss, which is bound to id_Q.
    let (ssid, message, state) = net.request(&q, for_q);
    let mut readdressed = message.clone();
    readdressed.id = *r.id();
    assert_eq!(
        net.try_evaluate(&readdressed, &ssid).err(),
        Some(Error::InvalidProof)
    );

    // One component of an attestation changed: Q rejects it, and the helper does not count it.
    let one = E::ScalarField::one();
    let mut moved = att.clone();
    moved.tag += E::G1::generator();
    let mut identity = att.clone();
    identity.tag = E::G1::zero();
    let mut other_show = att.clone();
    other_show.show = other_source.show.clone();
    let mut challenge = att.clone();
    challenge.proof.challenge += one;
    let mut response = att.clone();
    response.proof.responses[0] += one;
    let tampered = vec![
        (moved, Error::InvalidProof),
        (identity, Error::InvalidTag),
        (other_show, Error::InvalidProof),
        (challenge, Error::InvalidProof),
        (response, Error::InvalidProof),
    ];
    for (bad, reason) in &tampered {
        assert_eq!(
            net.pcreds.check_attestation(&net.hvk, q.id(), bad),
            Err(reason.clone())
        );
    }
    let (ssid_bad, bad, _) = net.request(&q, tampered.into_iter().map(|(att, _)| att).collect());
    let evaluated = net.evaluate(&bad, &ssid_bad);
    assert!(evaluated.tags().is_empty());
    assert_eq!(net.respond(evaluated, Decision::Policy), Reply::Fail);

    // Control: Q's honest request is issued.
    let reply = net.answer(&message, &ssid, Decision::Policy);
    net.unblind(&q, reply, state);
}

#[test]
fn attestations_are_bound_to_their_recipient() {
    recipient_binding::<E, PS, DDH>(b"pcreds/recipient/ps+ddh", 0x2ec1_0001);
    recipient_binding::<E, PS, DY>(b"pcreds/recipient/ps+dy", 0x2ec1_0002);
    recipient_binding::<E, BBS, DDH>(b"pcreds/recipient/bbs+ddh", 0x2ec1_0003);
    recipient_binding::<E, BBS, DY>(b"pcreds/recipient/bbs+dy", 0x2ec1_0004);
}

/// `AttestationRequest` (lines 364-376): `π_id ← zkPoK_{(ssid, P̃)}{((id_Q, x_0), usk_Q) ∈ R_Tag}`,
/// checked by the owner of the contact name `P̃` for `id_Q ∈ T` under the context `(ssid, P̃)`.
fn identifier_proof_binding<E, B, T>(label: &[u8], seed: u64)
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let mut net = Net::<PairingBackend<E, B, T>>::new(label, 1, seed);
    let (q, other) = (net.register(), net.register());
    let (ssid, contact) = (&b"ssid-1"[..], &b"alice@example"[..]);
    let request = net
        .pcreds
        .request_attestation(&net.hvk, &q, ssid, contact, &mut net.rng)
        .expect("π_id");
    let pending = net
        .pcreds
        .receive_attestation_request(&net.hvk, &request, ssid, contact)
        .expect("π_id verifies");
    assert_eq!(
        (pending.ssid(), pending.contact(), pending.id()),
        (ssid, contact, q.id())
    );
    assert!(
        net.pcreds
            .verify_attestation_request(&net.hvk, &request, ssid, contact)
    );

    // Another sub-session, another contact name (of the same owner, or of anybody), and the same
    // bytes split differently between ssid and P̃ (the context frames each item).
    for (ssid, contact) in [
        (&b"ssid-2"[..], contact),
        (ssid, &b"bob@example"[..]),
        (&b"ssid-1alice@example"[..], &b""[..]),
        (&b""[..], &b"ssid-1alice@example"[..]),
        (&b"ssid-1a"[..], &b"lice@example"[..]),
    ] {
        assert_eq!(
            net.pcreds
                .receive_attestation_request(&net.hvk, &request, ssid, contact)
                .err(),
            Some(Error::InvalidProof)
        );
        assert!(
            !net.pcreds
                .verify_attestation_request(&net.hvk, &request, ssid, contact)
        );
    }

    // Bound to id_Q: the proof vouches for no other identifier; the identity is none; and a
    // tampered proof fails.
    let mut forged = request.clone();
    forged.id = *other.id();
    assert_eq!(
        net.pcreds
            .receive_attestation_request(&net.hvk, &forged, ssid, contact)
            .err(),
        Some(Error::InvalidProof)
    );
    forged.id = E::G1::zero();
    assert_eq!(
        net.pcreds
            .receive_attestation_request(&net.hvk, &forged, ssid, contact)
            .err(),
        Some(Error::InvalidTag)
    );
    let mut forged = request.clone();
    forged.proof.challenge += E::ScalarField::one();
    assert!(
        !net.pcreds
            .verify_attestation_request(&net.hvk, &forged, ssid, contact)
    );

    // Bound to the deployment: not a request in another one, where q is not a user either.
    let elsewhere = Protocol::<PairingBackend<E, B, T>>::setup(b"pcreds/pi-id/another deployment")
        .expect("Setup");
    let hvk_elsewhere = elsewhere.helper_key(net.hvk.vk()).expect("hvk ∈ V_pp");
    assert_eq!(
        elsewhere
            .receive_attestation_request(&hvk_elsewhere, &request, ssid, contact)
            .err(),
        Some(Error::InvalidProof)
    );
    assert_eq!(
        elsewhere
            .request_attestation(&hvk_elsewhere, &q, ssid, contact, &mut net.rng)
            .err(),
        Some(Error::IdentifierMismatch)
    );

    // The empty ssid and contact name are a context like any other.
    let request = net
        .pcreds
        .request_attestation(&net.hvk, &q, b"", b"", &mut net.rng)
        .expect("π_id");
    assert!(
        net.pcreds
            .verify_attestation_request(&net.hvk, &request, b"", b"")
    );
    assert!(
        !net.pcreds
            .verify_attestation_request(&net.hvk, &request, b"", b"\0")
    );
}

#[test]
fn identifier_proofs_are_bound_to_session_contact_and_identifier() {
    identifier_proof_binding::<E, PS, DDH>(b"pcreds/pi-id/ps+ddh", 0x1d00_0001);
    identifier_proof_binding::<E, PS, DY>(b"pcreds/pi-id/ps+dy", 0x1d00_0002);
    identifier_proof_binding::<E, BBS, DDH>(b"pcreds/pi-id/bbs+ddh", 0x1d00_0003);
    identifier_proof_binding::<E, BBS, DY>(b"pcreds/pi-id/bbs+dy", 0x1d00_0004);
}

/// `CredentialRequest` (lines 399-416): `π_iss ← zkPoK_{(ssid, att⃗)}{((hvk, Ĉ, id_Q), (usk_Q, τ))
/// ∈ R_iss}`, checked by the helper under the context `(ssid, att⃗)` it REBUILDS (§7.3, "The
/// verifier must rebuild the proof context").
fn issuance_proof_binding<E, B, T>(label: &[u8], seed: u64)
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let policy = Policy::threshold(2).expect("k ≥ 1");
    let mut net = Net::<PairingBackend<E, B, T>>::with_policy(label, policy, seed);
    let members = net.roots(3);
    let q = net.register();
    let atts: Vec<_> = members
        .iter()
        .map(|member| net.attestation(member, &q))
        .collect();
    let (ssid, message, state) = net.request(&q, atts[..2].to_vec());
    assert!(net.try_evaluate(&message, &ssid).is_ok());

    // Bound to the sub-session ...
    assert_eq!(
        net.try_evaluate(&message, b"another ssid").err(),
        Some(Error::InvalidProof)
    );
    // ... to the list of attestations: one dropped, two swapped, one replaced, one appended, all
    // removed ...
    let one = E::ScalarField::one();
    let mut variants = Vec::new();
    let mut variant = message.clone();
    variant.attestations.pop();
    variants.push(variant);
    let mut variant = message.clone();
    variant.attestations.swap(0, 1);
    variants.push(variant);
    let mut variant = message.clone();
    variant.attestations[1] = atts[2].clone();
    variants.push(variant);
    let mut variant = message.clone();
    variant.attestations.push(atts[2].clone());
    variants.push(variant);
    let mut variant = message.clone();
    variant.attestations.clear();
    variants.push(variant);
    // ... to Ĉ (another request of the same user) ...
    let (_, other_request, _) = net.request(&q, atts[..2].to_vec());
    assert_ne!(other_request.request, message.request);
    let mut variant = message.clone();
    variant.request = other_request.request.clone();
    variants.push(variant);
    // ... and to its own responses.
    let mut variant = message.clone();
    variant.proof.responses[0] += one;
    variants.push(variant);
    let mut variant = message.clone();
    variant.proof.responses.push(one);
    variants.push(variant);
    let mut variant = message.clone();
    variant.proof.responses.pop();
    variants.push(variant);
    for variant in &variants {
        assert_eq!(
            net.try_evaluate(variant, &ssid).err(),
            Some(Error::InvalidProof)
        );
    }
    // id_Q ∈ T is checked first.
    let mut variant = message.clone();
    variant.id = E::G1::zero();
    assert_eq!(
        net.try_evaluate(&variant, &ssid).err(),
        Some(Error::InvalidTag)
    );

    // A cheating prover with the honest witness (usk_Q, τ) proves R_iss under a context of its
    // own choosing: the bare Fiat-Shamir proof verifies, the helper rejects it. The same prover
    // under the context the helper rebuilds is accepted.
    let relation = PairingBackend::<E, B, T>::issuance_relation(
        net.pcreds.params(),
        net.hvk.vk(),
        &message.request,
        &message.id,
        net.hvk.identifier_point(),
    )
    .expect("R_iss");
    let witness = [*q.expose_key(), *state.expose_tape()];
    let mut bogus = message.clone();
    bogus.proof = fiat_shamir::prove(&relation, &witness, b"a context of my own", &mut net.rng)
        .expect("the witness satisfies R_iss");
    assert!(fiat_shamir::verify(
        &relation,
        b"a context of my own",
        &bogus.proof
    ));
    assert_eq!(
        net.try_evaluate(&bogus, &ssid).err(),
        Some(Error::InvalidProof)
    );
    let ctx = net
        .pcreds
        .issuance_context(net.hvk.vk(), &ssid, &message.attestations)
        .expect("ctx");
    let mut rebuilt = message.clone();
    rebuilt.proof =
        fiat_shamir::prove(&relation, &witness, &ctx, &mut net.rng).expect("the same witness");
    assert!(net.try_evaluate(&rebuilt, &ssid).is_ok());

    // Control: the honest request is issued.
    let reply = net.answer(&message, &ssid, Decision::Policy);
    net.unblind(&q, reply, state);
}

#[test]
fn issuance_proofs_are_bound_to_session_and_attestations() {
    issuance_proof_binding::<E, PS, DDH>(b"pcreds/pi-iss/ps+ddh", 0x155e_0001);
    issuance_proof_binding::<E, PS, DY>(b"pcreds/pi-iss/ps+dy", 0x155e_0002);
    issuance_proof_binding::<E, BBS, DDH>(b"pcreds/pi-iss/bbs+ddh", 0x155e_0003);
    issuance_proof_binding::<E, BBS, DY>(b"pcreds/pi-iss/bbs+dy", 0x155e_0004);
}

/// Two helpers of ONE deployment: everything made under one helper key is refused under the
/// other. `hvk` is part of the statements of `π_att`, `π_iss` and `π_prove`, and of
/// `x_Q = H_req(⟨pp, hvk, id_Q⟩)`.
fn helper_key_binding<E, B, T>(label: &[u8], seed: u64)
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let mut net = Net::<PairingBackend<E, B, T>>::new(label, 1, seed);
    let mut other = net
        .pcreds
        .helper_keygen(Policy::threshold(1).expect("k ≥ 1"), &mut net.rng);
    let hvk_2 = net.pcreds.helper_key(other.key().vk()).expect("hvk ∈ V_pp");
    assert_ne!(hvk_2, net.hvk);
    let member = net.roots(1).pop().expect("a root");
    let q = net.register();
    let att = net.attestation(&member, &q);

    // Attestations and membership proofs made under hvk, checked under hvk_2.
    assert_eq!(
        net.pcreds.check_attestation(&hvk_2, q.id(), &att),
        Err(foreign_key_error::<B>())
    );
    let proof = net
        .pcreds
        .prove(&net.hvk, &member.user, &member.cred, b"m", &mut net.rng)
        .expect("Prove");
    assert_eq!(
        net.pcreds.check_membership(&hvk_2, b"m", &proof),
        Err(foreign_key_error::<B>())
    );
    // A user belongs to one helper key; with its key registered under hvk_2 too, a credential
    // under hvk is none under hvk_2, and cannot be shown under it.
    assert_eq!(
        net.pcreds
            .prove(&hvk_2, &member.user, &member.cred, b"m", &mut net.rng)
            .err(),
        Some(Error::IdentifierMismatch)
    );
    let member_2 = net
        .pcreds
        .register_reusing(&hvk_2, &member.user)
        .expect("Register");
    assert_ne!(member_2.id(), member.user.id(), "x_0 is the key's");
    assert!(
        !net.pcreds
            .verify_credential(&hvk_2, &member_2, &member.cred)
    );
    assert_foreign_credential_refused::<B, _>(
        net.pcreds
            .prove(&hvk_2, &member_2, &member.cred, b"m", &mut net.rng),
        |proof| net.pcreds.check_membership(&hvk_2, b"m", proof),
    );

    // A credential request for hvk is refused by the other helper ...
    let (ssid, message, state) = net.request(&q, vec![att]);
    assert_eq!(
        net.pcreds.evaluate_request(&other, &message, &ssid).err(),
        Some(Error::InvalidProof)
    );
    // ... and a request evaluated by one helper is answered by that helper only.
    let evaluated = net.evaluate(&message, &ssid);
    assert_eq!(
        net.pcreds
            .respond(&mut other, evaluated, Decision::Policy, &mut net.rng)
            .err(),
        Some(Error::InvalidKey)
    );
    assert!(other.store().is_empty());
    assert_eq!(net.helper.store().len(), 1);

    // A pre-credential of the other helper does not unblind under hvk (fail-closed Unblind).
    let at_other = b"a sub-session with the other helper";
    let q_2 = net.pcreds.register_reusing(&hvk_2, &q).expect("Register");
    let (message_2, state_2) = net
        .pcreds
        .request_credential(&hvk_2, &q_2, Vec::new(), at_other, &mut net.rng)
        .expect("CredentialRequest");
    let evaluated = net
        .pcreds
        .evaluate_request(&other, &message_2, at_other)
        .expect("π_iss");
    let Ok(Reply::PreCredential(pre_2)) =
        net.pcreds
            .respond(&mut other, evaluated, Decision::Root, &mut net.rng)
    else {
        panic!("the other helper admits q");
    };
    assert_eq!(
        net.pcreds.unblind(&net.hvk, &q, &pre_2, copy(&state)).err(),
        Some(Error::InvalidPreCredential)
    );
    // the state of the request under hvk_2 belongs to q's identifier under hvk_2
    assert_eq!(
        net.pcreds
            .unblind(&net.hvk, &q, &pre_2, copy(&state_2))
            .err(),
        Some(Error::IssuanceStateMismatch)
    );
    let cred_2 = net
        .pcreds
        .unblind(&hvk_2, &q_2, &pre_2, state_2)
        .expect("under hvk_2");
    assert!(!net.pcreds.verify_credential(&net.hvk, &q, &cred_2));

    // Control: q's request for hvk is still answered by its helper.
    let reply = net.answer(&message, &ssid, Decision::Policy);
    net.unblind(&q, reply, state);
}

#[test]
fn helper_keys_bind_every_object() {
    helper_key_binding::<E, PS, DDH>(b"pcreds/hvk/ps+ddh", 0x4e1b_0001);
    helper_key_binding::<E, PS, DY>(b"pcreds/hvk/ps+dy", 0x4e1b_0002);
    helper_key_binding::<E, BBS, DDH>(b"pcreds/hvk/bbs+ddh", 0x4e1b_0003);
    helper_key_binding::<E, BBS, DY>(b"pcreds/hvk/bbs+dy", 0x4e1b_0004);
}

// ---------------------------------------------------------------------------------------------
// Prove and Verify
// ---------------------------------------------------------------------------------------------

/// `Prove` and `Verify` (lines 428-442): `π = (σ*, π_prove)` with `π_prove ← zkPoK_m{…}` is bound
/// to the message `m`, to `hvk`, and to a credential of the prover's own key.
fn membership_proofs<E, B, T>(label: &[u8], seed: u64)
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let mut net = Net::<PairingBackend<E, B, T>>::new(label, 1, seed);
    let member = net.roots(1).pop().expect("a root");
    let outsider = net.register();
    let proof = net
        .pcreds
        .prove(&net.hvk, &member.user, &member.cred, b"hello", &mut net.rng)
        .expect("Prove");
    assert_eq!(
        net.pcreds.check_membership(&net.hvk, b"hello", &proof),
        Ok(())
    );
    assert!(net.pcreds.verify(&net.hvk, b"hello", &proof));

    // Bound to m, byte for byte.
    for m in [&b"goodbye"[..], b"", b"hell", b"hello\0", b"Hello"] {
        assert_eq!(
            net.pcreds.check_membership(&net.hvk, m, &proof),
            Err(Error::InvalidProof)
        );
    }
    let empty = net
        .pcreds
        .prove(&net.hvk, &member.user, &member.cred, b"", &mut net.rng)
        .expect("Prove");
    assert!(net.pcreds.verify(&net.hvk, b"", &empty));
    assert!(!net.pcreds.verify(&net.hvk, b"\0", &empty));

    // ReRand: two proofs on one message carry different shows, and both verify; a show and a
    // proof of two different proofs do not combine.
    let again = net
        .pcreds
        .prove(&net.hvk, &member.user, &member.cred, b"hello", &mut net.rng)
        .expect("Prove");
    assert_ne!(again.show, proof.show);
    assert!(net.pcreds.verify(&net.hvk, b"hello", &again));
    let mut mixed = proof.clone();
    mixed.show = again.show.clone();
    assert_eq!(
        net.pcreds.check_membership(&net.hvk, b"hello", &mixed),
        Err(Error::InvalidProof)
    );
    let mut tampered = proof.clone();
    tampered.proof.challenge += E::ScalarField::one();
    assert!(!net.pcreds.verify(&net.hvk, b"hello", &tampered));
    let mut tampered = proof.clone();
    tampered.proof.responses.pop();
    assert!(!net.pcreds.verify(&net.hvk, b"hello", &tampered));

    // Bound to hvk: another helper of the same deployment.
    let other = net
        .pcreds
        .helper_keygen(Policy::threshold(1).expect("k ≥ 1"), &mut net.rng);
    let hvk_2 = net.pcreds.helper_key(other.key().vk()).expect("hvk ∈ V_pp");
    assert_eq!(
        net.pcreds.check_membership(&hvk_2, b"hello", &proof),
        Err(foreign_key_error::<B>())
    );

    // Bound to the holder: an outsider can neither show the member's credential, nor claim it,
    // nor attest with it.
    assert_foreign_credential_refused::<B, _>(
        net.pcreds
            .prove(&net.hvk, &outsider, &member.cred, b"hello", &mut net.rng),
        |proof| net.pcreds.check_membership(&net.hvk, b"hello", proof),
    );
    assert_eq!(
        net.pcreds
            .credential(&net.hvk, &outsider, member.cred.as_inner().clone())
            .err(),
        Some(Error::InvalidCredential)
    );
    let q = net.register();
    let request = net
        .pcreds
        .request_attestation(&net.hvk, &q, b"ssid", b"outsider@example", &mut net.rng)
        .expect("π_id");
    let pending = net
        .pcreds
        .receive_attestation_request(&net.hvk, &request, b"ssid", b"outsider@example")
        .expect("π_id");
    assert_foreign_credential_refused::<B, _>(
        net.pcreds
            .attest(&net.hvk, &outsider, &member.cred, pending, &mut net.rng),
        |att| net.pcreds.check_attestation(&net.hvk, q.id(), att),
    );
    // Control: the holder's own credential, wrapped again, is accepted.
    assert!(
        net.pcreds
            .credential(&net.hvk, &member.user, member.cred.as_inner().clone())
            .is_ok()
    );
}

#[test]
fn membership_proofs_are_bound_to_message_key_and_holder() {
    membership_proofs::<E, PS, DDH>(b"pcreds/membership/ps+ddh", 0x3e3b_0001);
    membership_proofs::<E, PS, DY>(b"pcreds/membership/ps+dy", 0x3e3b_0002);
    membership_proofs::<E, BBS, DDH>(b"pcreds/membership/bbs+ddh", 0x3e3b_0003);
    membership_proofs::<E, BBS, DY>(b"pcreds/membership/bbs+dy", 0x3e3b_0004);
}

// ---------------------------------------------------------------------------------------------
// The policy: any number of attestations, an optional limit, and counting N''
// ---------------------------------------------------------------------------------------------

/// `Policy`: `Pol_k` needs `k ≥ 1`, and it accepts iff the request has `k` or MORE distinct valid
/// tags, whatever number of attestations it carries (protocol box, line 414): by default a
/// request with more than `k` attestations is evaluated like any other. A helper MAY set a limit
/// on that number (an implementation note, not part of the paper; at least `k`): a request above
/// it is refused with `TooManyAttestations` BEFORE anything is verified, and at the limit it is
/// evaluated.
fn attestation_limit<E, B, T>(label: &[u8], seed: u64)
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let policy = Policy::threshold(2).expect("k ≥ 1");
    assert_eq!((policy.k(), policy.max_attestations()), (2, None));
    assert!(!policy.accepts(1) && policy.accepts(2) && policy.accepts(3));
    assert!(matches!(
        policy.with_max_attestations(1),
        Err(Error::DegenerateInput(_))
    ));
    assert_eq!(Policy::threshold(0).err(), Some(Error::ZeroThreshold));
    let capped = policy.with_max_attestations(4).expect("4 ≥ k");
    assert_eq!((capped.k(), capped.max_attestations()), (2, Some(4)));

    let mut net = Net::<PairingBackend<E, B, T>>::with_policy(label, policy, seed);
    let members = net.roots(5);
    let q = net.register();
    let atts: Vec<_> = members
        .iter()
        .map(|member| net.attestation(member, &q))
        .collect();

    // No limit by default: five attestations at k = 2 are evaluated, and all five count.
    let (ssid, five, _) = net.request(&q, atts.clone());
    let evaluated = net
        .try_evaluate(&five, &ssid)
        .expect("more than k attestations are fine");
    assert_eq!(evaluated.tags().len(), 5);
    assert!(evaluated.is_valid());

    // The same helper key with the limit 4 (the policy is the helper's input, kept apart from
    // its key).
    let key = net.helper.to_bytes().expect("the key encodes");
    let lenient = net
        .pcreds
        .restore_helper(&key, capped, IssuanceRecord::new())
        .expect("restore");
    let (ssid, five, _) = net.request(&q, atts.clone());
    let too_many = Some(Error::TooManyAttestations { max: 4, actual: 5 });
    assert_eq!(
        net.pcreds.evaluate_request(&lenient, &five, &ssid).err(),
        too_many
    );
    // Refused before any verification: with π_iss and every attestation broken, the answer is
    // the same ...
    let one = E::ScalarField::one();
    let mut broken = five.clone();
    broken.proof.challenge += one;
    for att in &mut broken.attestations {
        att.proof.challenge += one;
    }
    assert_eq!(
        net.pcreds.evaluate_request(&lenient, &broken, &ssid).err(),
        too_many
    );
    // ... while at the limit the broken π_iss is what is refused, and the honest request is
    // evaluated, with 4 distinct tags.
    let (ssid, four, _) = net.request(&q, atts[..4].to_vec());
    let mut broken = four.clone();
    broken.proof.challenge += one;
    assert_eq!(
        net.pcreds.evaluate_request(&lenient, &broken, &ssid).err(),
        Some(Error::InvalidProof)
    );
    let evaluated = net
        .pcreds
        .evaluate_request(&lenient, &four, &ssid)
        .expect("at the limit");
    assert_eq!(evaluated.tags().len(), 4);
    assert!(evaluated.is_valid());
}

#[test]
fn any_number_of_attestations_and_an_optional_limit() {
    attestation_limit::<E, PS, DDH>(b"pcreds/cap/ps+ddh", 0xca90_0001);
    attestation_limit::<E, PS, DY>(b"pcreds/cap/ps+dy", 0xca90_0002);
    attestation_limit::<E, BBS, DDH>(b"pcreds/cap/bbs+ddh", 0xca90_0003);
    attestation_limit::<E, BBS, DY>(b"pcreds/cap/bbs+dy", 0xca90_0004);
}

/// The helper's step (ii) of `CredentialRequest` (line 414): `N''` is the set of tags `t` of the
/// attestations in `att⃗` with `t ∈ T` and a valid `π_att` at `x_Q`, and `v = valid` iff
/// `|N''| ≥ k`. Duplicates and invalid attestations are allowed and add nothing;
/// a source counts once whatever contact name it was reached through.
fn counting<E, B, T>(label: &[u8], seed: u64)
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let k = 2;
    let policy = Policy::threshold(k).expect("k ≥ 1");
    let mut net = Net::<PairingBackend<E, B, T>>::with_policy(label, policy, seed);
    let members = net.roots(3);
    let (q, r) = (net.register(), net.register());
    let a = net.attestation(&members[0], &q);
    let a_again = net.attestation_via(&members[0], &q, b"a second contact name of member 0");
    let b = net.attestation(&members[1], &q);
    let c_for_r = net.attestation(&members[2], &r);
    let mut b_broken = b.clone();
    b_broken.proof.challenge += E::ScalarField::one();
    let mut outside_t = b.clone();
    outside_t.tag = E::G1::zero();
    let (t_a, t_b) = (a.tag, b.tag);
    assert_eq!(a_again.tag, t_a);

    let cases = [
        // one attestation twice
        (vec![a.clone(), a.clone()], vec![t_a]),
        // one source twice, through two contact names
        (vec![a.clone(), a_again.clone()], vec![t_a]),
        // an attestation for another recipient
        (vec![a.clone(), c_for_r.clone()], vec![t_a]),
        // a broken proof
        (vec![a.clone(), b_broken.clone()], vec![t_a]),
        // a tag outside T
        (vec![a.clone(), outside_t.clone()], vec![t_a]),
        // an invalid attestation does not shadow a valid one with the same tag
        (
            vec![
                b_broken.clone(),
                a.clone(),
                a_again.clone(),
                c_for_r.clone(),
                outside_t.clone(),
                b.clone(),
            ],
            vec![t_a, t_b],
        ),
        // N'' is listed in the order of the request
        (vec![b.clone(), a.clone()], vec![t_b, t_a]),
    ];
    for (attestations, expected) in cases {
        let (ssid, message, _) = net.request(&q, attestations);
        let evaluated = net.evaluate(&message, &ssid);
        assert_eq!(evaluated.tags(), &expected[..]);
        assert_eq!(evaluated.is_valid(), expected.len() >= k);
    }

    // The reply follows v.
    let (ssid, message, _) = net.request(&q, vec![a.clone(), a_again, b_broken.clone()]);
    assert_eq!(net.answer(&message, &ssid, Decision::Policy), Reply::Fail);
    let (ssid, message, state) = net.request(&q, vec![b_broken, a, c_for_r, b]);
    let reply = net.answer(&message, &ssid, Decision::Policy);
    net.unblind(&q, reply, state);
}

#[test]
fn the_helper_counts_distinct_valid_tags() {
    counting::<E, PS, DDH>(b"pcreds/counting/ps+ddh", 0xc0de_0001);
    counting::<E, PS, DY>(b"pcreds/counting/ps+dy", 0xc0de_0002);
    counting::<E, BBS, DDH>(b"pcreds/counting/bbs+ddh", 0xc0de_0003);
    counting::<E, BBS, DY>(b"pcreds/counting/bbs+dy", 0xc0de_0004);
}

// ---------------------------------------------------------------------------------------------
// Persistence: the helper, users, credentials
// ---------------------------------------------------------------------------------------------

/// The helper persists its key (`Helper::to_bytes`: pp-digest ‖ hvk ‖ sk) and its record `I`
/// separately, and restarts with `Protocol::restore_helper`.
fn helper_restarts<Bk: Backend>(label: &[u8], seed: u64) {
    let mut net = Net::<Bk>::new(label, 1, seed);
    let root = net.roots(1).pop().expect("a root");
    let user = net.register();
    let att = net.attestation(&root, &user);
    let early = net.join(user, vec![att]);
    assert_eq!(net.helper.store().len(), 2);

    let key = net.helper.to_bytes().expect("the key encodes");
    let record = net.helper.store().to_bytes().expect("I encodes");
    let policy = *net.helper.policy();
    let restored = net
        .pcreds
        .restore_helper(
            &key,
            policy,
            IssuanceRecord::from_bytes(&record).expect("I decodes"),
        )
        .expect("restore");
    assert_eq!(restored.key(), net.helper.key());
    assert_eq!(restored.policy(), &policy);
    assert_eq!(restored.store(), net.helper.store());
    net.helper = restored;

    // The restored helper keeps issuing under the same hvk ...
    let user = net.register();
    let att = net.attestation(&early, &user);
    let late = net.join(user, vec![att]);
    assert!(
        net.pcreds
            .verify_credential(&net.hvk, &early.user, &early.cred)
    );
    // ... and, with the restored I, answers `issued` for an identifier issued before the restart.
    let att = net.attestation(&late, &early.user);
    let (ssid, message, _) = net.request(&early.user, vec![att]);
    assert_eq!(net.answer(&message, &ssid, Decision::Policy), Reply::Issued);
    assert_eq!(net.helper.store().len(), 3);

    // Implementation note of `IssuanceRecord`: kept in memory only, I does not survive a restart.
    // A helper restarted WITHOUT its record issues to the same identifier a second time: "at
    // most once per identifier" is exactly as durable as the store.
    let mut amnesiac = net
        .pcreds
        .restore_helper(&key, policy, IssuanceRecord::new())
        .expect("restore");
    let evaluated = net
        .pcreds
        .evaluate_request(&amnesiac, &message, &ssid)
        .expect("π_iss");
    assert!(matches!(
        net.pcreds
            .respond(&mut amnesiac, evaluated, Decision::Policy, &mut net.rng),
        Ok(Reply::PreCredential(_))
    ));

    // Restored only under THIS deployment, with the sk behind hvk, from an exact encoding.
    let elsewhere = Protocol::<Bk>::setup(b"pcreds/restart/another deployment").expect("Setup");
    assert_eq!(
        elsewhere
            .restore_helper(&key, policy, IssuanceRecord::new())
            .err(),
        Some(Error::InvalidKey)
    );
    let other = net.pcreds.helper_keygen(policy, &mut net.rng);
    let other_key = other.to_bytes().expect("the key encodes");
    let head = net.pcreds.parameters_digest().compressed_size() + net.hvk.vk().compressed_size();
    let mut spliced = key[..head].to_vec();
    spliced.extend_from_slice(&other_key[head..]);
    let restore = |bytes: &[u8]| {
        net.pcreds
            .restore_helper(bytes, policy, IssuanceRecord::new())
            .err()
    };
    assert_eq!(restore(&spliced), Some(Error::InvalidKey));
    let mut trailing = key.to_vec();
    trailing.push(0);
    assert_eq!(restore(&trailing), Some(Error::TrailingBytes));
    assert!(matches!(
        restore(&key[..key.len() - 1]),
        Some(Error::Serialization(_))
    ));
    assert!(restore(&key).is_none());
}

#[test]
fn helper_restarts_keep_the_key_and_the_record() {
    helper_restarts::<Bk<PS, DDH>>(b"pcreds/restart/ps+ddh", 0x4e57_0001);
    helper_restarts::<Bk<PS, DY>>(b"pcreds/restart/ps+dy", 0x4e57_0002);
    helper_restarts::<Bk<BBS, DDH>>(b"pcreds/restart/bbs+ddh", 0x4e57_0003);
    helper_restarts::<Bk<BBS, DY>>(b"pcreds/restart/bbs+dy", 0x4e57_0004);
}

/// `Register` (line 356) and its counterparts for a user whose key exists already: the user of a
/// given key (`Protocol::user`), and a user read back from storage (`User::to_bytes`,
/// `WireFormat::from_bytes`, `Protocol::check_user`). A credential goes to storage and back
/// likewise (`Credential::to_bytes`, `Protocol::verify_credential`).
fn users_from_keys<E, B, T>(label: &[u8], seed: u64)
where
    E: Pairing,
    B: Base<E> + BaseFacts,
    T: ProtocolTag<E::G1> + 'static,
{
    let mut net = Net::<PairingBackend<E, B, T>>::new(label, 1, seed);
    let root = net.roots(1).pop().expect("a root");
    let user = net.register();

    // The user of a given key: id = Tag(usk, x_0), deterministically.
    let again = net
        .pcreds
        .user(&net.hvk, *user.expose_key())
        .expect("a key of Register");
    assert_eq!(again.id(), user.id());
    assert_eq!(net.pcreds.check_user(&net.hvk, &again), Ok(()));

    // Storage: usk ‖ id ‖ pp-digest ‖ helper fingerprint.
    let bytes = user.to_bytes().expect("the user encodes");
    let (usk_len, id_len) = (
        user.expose_key().compressed_size(),
        user.id().compressed_size(),
    );
    assert_eq!(
        bytes.len(),
        usk_len + id_len + net.pcreds.parameters_digest().len() + net.hvk.fingerprint().len()
    );
    assert_eq!(user.helper_fingerprint(), net.hvk.fingerprint());
    let restored = User::<PairingBackend<E, B, T>>::from_bytes(&bytes).expect("decodes");
    assert_eq!(restored.id(), user.id());
    assert_eq!(restored.parameters_digest(), net.pcreds.parameters_digest());
    assert_eq!(net.pcreds.check_user(&net.hvk, &restored), Ok(()));
    // Decoding is not checking: another user's identifier decodes, and check_user refuses it.
    let other = net.register();
    let mut spliced = bytes[..usk_len].to_vec();
    spliced.extend_from_slice(&serialization::to_bytes(other.id()).expect("id"));
    spliced.extend_from_slice(&bytes[usk_len + id_len..]);
    let wrong = User::<PairingBackend<E, B, T>>::from_bytes(&spliced).expect("decodes");
    assert_eq!(
        net.pcreds.check_user(&net.hvk, &wrong),
        Err(Error::IdentifierMismatch)
    );
    let elsewhere = Protocol::<PairingBackend<E, B, T>>::setup(b"pcreds/users/another deployment")
        .expect("Setup");
    let hvk_elsewhere = elsewhere.helper_key(net.hvk.vk()).expect("hvk ∈ V_pp");
    assert_eq!(
        elsewhere.check_user(&hvk_elsewhere, &restored),
        Err(Error::IdentifierMismatch)
    );
    let mut trailing = bytes.to_vec();
    trailing.push(0);
    assert_eq!(
        User::<PairingBackend<E, B, T>>::from_bytes(&trailing).err(),
        Some(Error::TrailingBytes)
    );

    // The restored user carries on: it is attested and obtains a credential ...
    let att = net.attestation(&root, &restored);
    let member = net.join(restored, vec![att]);
    // ... which goes to storage and back. It certifies the KEY: it verifies for every user value
    // of that key (`again` was rebuilt from it above), and for no other key.
    let cred_bytes = member.cred.to_bytes().expect("the credential encodes");
    let cred = Credential::<PairingBackend<E, B, T>>::from_bytes(&cred_bytes).expect("decodes");
    assert_eq!(cred, member.cred);
    assert!(net.pcreds.verify_credential(&net.hvk, &member.user, &cred));
    assert!(net.pcreds.verify_credential(&net.hvk, &again, &cred));
    assert!(!net.pcreds.verify_credential(&net.hvk, &root.user, &cred));
    assert!(!net.pcreds.verify_credential(&net.hvk, &other, &cred));
    let proof = net
        .pcreds
        .prove(
            &net.hvk,
            &member.user,
            &cred,
            b"after a restart",
            &mut net.rng,
        )
        .expect("Prove");
    assert!(net.pcreds.verify(&net.hvk, b"after a restart", &proof));
}

#[test]
fn users_from_keys_and_from_storage() {
    users_from_keys::<E, PS, DDH>(b"pcreds/users/ps+ddh", 0x05e2_0001);
    users_from_keys::<E, PS, DY>(b"pcreds/users/ps+dy", 0x05e2_0002);
    users_from_keys::<E, BBS, DDH>(b"pcreds/users/bbs+ddh", 0x05e2_0003);
    users_from_keys::<E, BBS, DY>(b"pcreds/users/bbs+dy", 0x05e2_0004);
}

// ---------------------------------------------------------------------------------------------
// The issuance store
// ---------------------------------------------------------------------------------------------

/// A store that answers but cannot record (its disk is full).
struct FailingStore;

impl IssuanceStore for FailingStore {
    fn contains(&self, _id: &[u8]) -> Result<bool, Error> {
        Ok(false)
    }

    fn record(&mut self, _id: &[u8]) -> Result<bool, Error> {
        Err(Error::Storage("disk full".to_owned()))
    }
}

/// The set `I` on storage shared by several helper processes, one handle per process. The tests
/// are single-threaded; `IssuanceRecord::record` is the atomic insert-if-absent.
#[derive(Clone, Default)]
struct SharedStore(Rc<RefCell<IssuanceRecord>>);

impl IssuanceStore for SharedStore {
    fn contains(&self, id: &[u8]) -> Result<bool, Error> {
        self.0.borrow().contains(id)
    }

    fn record(&mut self, id: &[u8]) -> Result<bool, Error> {
        self.0.borrow_mut().record(id)
    }
}

/// Remark "Concurrency" and `IssuanceStore`: `respond` runs `BlindIssue`, then records `id_Q`,
/// and releases the pre-credential only if the record succeeded: if the store fails, nothing is
/// released. `Fail` does not consult the store.
fn failing_store<Bk: Backend>(label: &[u8], seed: u64) {
    let mut net = Net::<Bk>::new(label, 1, seed);
    let root = net.roots(1).pop().expect("a root");
    let q = net.register();
    let att = net.attestation(&root, &q);
    let (ssid, message, state) = net.request(&q, vec![att]);

    let key = net.helper.to_bytes().expect("the key encodes");
    let policy = *net.helper.policy();
    let mut broken = net
        .pcreds
        .restore_helper(&key, policy, FailingStore)
        .expect("restore");
    for decision in [Decision::Policy, Decision::Root] {
        let evaluated = net
            .pcreds
            .evaluate_request(&broken, &message, &ssid)
            .expect("π_iss");
        assert!(evaluated.is_valid());
        assert_eq!(
            net.pcreds
                .respond(&mut broken, evaluated, decision, &mut net.rng),
            Err(Error::Storage("disk full".to_owned()))
        );
    }
    let (ssid_empty, empty, _) = net.request(&q, Vec::new());
    let evaluated = net
        .pcreds
        .evaluate_request(&broken, &empty, &ssid_empty)
        .expect("π_iss");
    assert_eq!(
        net.pcreds
            .respond(&mut broken, evaluated, Decision::Policy, &mut net.rng),
        Ok(Reply::Fail)
    );

    // Nothing was issued: the helper on a working store issues to q, and q's state unblinds it.
    assert_eq!(net.helper.store().len(), 1);
    let reply = net.answer(&message, &ssid, Decision::Policy);
    net.unblind(&q, reply, state);
}

#[test]
fn a_failing_store_releases_nothing() {
    failing_store::<Bk<PS, DDH>>(b"pcreds/failing-store/ps+ddh", 0xf5f5_0001);
    failing_store::<Bk<BBS, DY>>(b"pcreds/failing-store/bbs+dy", 0xf5f5_0002);
}

/// "On storage shared by several helper processes no identifier is issued to twice" (`pcreds`
/// protocol notes): two processes with one key and one store, each issuing to one requester.
fn shared_store<Bk: Backend>(label: &[u8], seed: u64) {
    let mut net = Net::<Bk>::new(label, 1, seed);
    let root = net.roots(1).pop().expect("a root");
    let key = net.helper.to_bytes().expect("the key encodes");
    let policy = *net.helper.policy();
    let shared = SharedStore::default();
    let mut first = net
        .pcreds
        .restore_helper(&key, policy, shared.clone())
        .expect("restore");
    let mut second = net
        .pcreds
        .restore_helper(&key, policy, shared.clone())
        .expect("restore");
    issue_once(&mut net, &root, &mut first, &mut second);
    issue_once(&mut net, &root, &mut second, &mut first);
    assert_eq!(shared.0.borrow().len(), 2);
}

/// One requester and two helper processes on one store. Both evaluate the request; `issuer`
/// records first and issues. For `other` the store reports the identifier as recorded already,
/// and the reply is `issued`, also for `d = root`.
fn issue_once<Bk: Backend>(
    net: &mut Net<Bk>,
    root: &Member<Bk>,
    issuer: &mut Helper<Bk, SharedStore>,
    other: &mut Helper<Bk, SharedStore>,
) {
    let q = net.register();
    let att = net.attestation(root, &q);
    let (ssid, message, state) = net.request(&q, vec![att]);
    let at_issuer = net
        .pcreds
        .evaluate_request(issuer, &message, &ssid)
        .expect("π_iss");
    let at_other = net
        .pcreds
        .evaluate_request(other, &message, &ssid)
        .expect("π_iss");
    let reply = net
        .pcreds
        .respond(issuer, at_issuer, Decision::Policy, &mut net.rng)
        .expect("respond");
    assert_eq!(
        net.pcreds
            .respond(other, at_other, Decision::Policy, &mut net.rng),
        Ok(Reply::Issued)
    );
    let at_other = net
        .pcreds
        .evaluate_request(other, &message, &ssid)
        .expect("π_iss");
    assert_eq!(
        net.pcreds
            .respond(other, at_other, Decision::Root, &mut net.rng),
        Ok(Reply::Issued)
    );
    net.unblind(&q, reply, state);
    let id = serialization::to_bytes(q.id()).expect("id");
    assert_eq!(issuer.store().contains(&id), Ok(true));
    assert_eq!(other.store().contains(&id), Ok(true));
}

#[test]
fn helper_processes_sharing_a_store_issue_once() {
    shared_store::<Bk<PS, DY>>(b"pcreds/shared-store/ps+dy", 0x5a5a_0001);
    shared_store::<Bk<BBS, DDH>>(b"pcreds/shared-store/bbs+ddh", 0x5a5a_0002);
}

/// A store in which another process records every identifier between the check and the record
/// of `respond`: `contains` says no, `record` finds it recorded.
struct RacingStore;

impl IssuanceStore for RacingStore {
    fn contains(&self, _id: &[u8]) -> Result<bool, Error> {
        Ok(false)
    }

    fn record(&mut self, _id: &[u8]) -> Result<bool, Error> {
        Ok(false)
    }
}

/// The race of two helper processes inside `respond`: the identifier was not recorded when
/// `respond` looked, `BlindIssue` ran, and the record then finds it recorded by the other
/// process. The pre-credential is discarded and the reply is `issued`, for both decisions.
fn lost_race<Bk: Backend>(label: &[u8], seed: u64) {
    let mut net = Net::<Bk>::new(label, 1, seed);
    let root = net.roots(1).pop().expect("a root");
    let q = net.register();
    let att = net.attestation(&root, &q);
    let (ssid, message, _state) = net.request(&q, vec![att]);
    let key = net.helper.to_bytes().expect("the key encodes");
    let mut racing = net
        .pcreds
        .restore_helper(&key, *net.helper.policy(), RacingStore)
        .expect("restore");
    for decision in [Decision::Policy, Decision::Root] {
        let evaluated = net
            .pcreds
            .evaluate_request(&racing, &message, &ssid)
            .expect("π_iss");
        assert_eq!(
            net.pcreds
                .respond(&mut racing, evaluated, decision, &mut net.rng),
            Ok(Reply::Issued)
        );
    }
}

#[test]
fn a_lost_race_releases_nothing() {
    lost_race::<Bk<PS, DDH>>(b"pcreds/lost-race/ps+ddh", 0x1a5e_0001);
    lost_race::<Bk<BBS, DY>>(b"pcreds/lost-race/bbs+dy", 0x1a5e_0002);
}

/// The backend-generic tests of this suite at the lattice instantiation
/// (`pcreds::lattice::LatticeBackend`): the same protocol logic over lattice objects and Jali
/// proofs. Heavy (Jali proofs of seconds each); run in release:
/// `cargo test --release --features lattice --test pcreds_correctness lattice`.
#[cfg(feature = "lattice")]
mod lattice {
    use predicate_credential_system::pcreds::lattice::LatticeBackend as Lattice;

    use super::*;

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "heavy: Jali proofs; runs in release builds"
    )]
    fn root_admission_lattice() {
        root_admission::<Lattice>(b"pcreds/root/lattice", 0x2001_0101);
    }

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "heavy: Jali proofs; runs in release builds"
    )]
    fn self_attestation_lattice() {
        self_attestation::<Lattice>(b"pcreds/self/lattice", 0x5e1f_0101);
    }

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "heavy: Jali proofs; runs in release builds"
    )]
    fn delayed_reply_lattice() {
        delayed_reply::<Lattice>(b"pcreds/delayed/lattice", 0xde1a_0101);
    }

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "heavy: Jali proofs; runs in release builds"
    )]
    fn helper_restarts_lattice() {
        helper_restarts::<Lattice>(b"pcreds/restart/lattice", 0x4e57_0101);
    }

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "heavy: Jali proofs; runs in release builds"
    )]
    fn failing_store_lattice() {
        failing_store::<Lattice>(b"pcreds/failing-store/lattice", 0xf5f5_0101);
    }

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "heavy: Jali proofs; runs in release builds"
    )]
    fn shared_store_and_lost_race_lattice() {
        shared_store::<Lattice>(b"pcreds/shared-store/lattice", 0x5a5a_0101);
        lost_race::<Lattice>(b"pcreds/lost-race/lattice", 0x1a5e_0101);
    }
}

// ---------------------------------------------------------------------------------------------
// Setup: received public parameters, deployments
// ---------------------------------------------------------------------------------------------

/// `Err(InvalidPublicParameters)` whose reason names `what`.
fn assert_refused<Bk: Backend>(result: Result<Protocol<Bk>, Error>, what: &str) {
    match result {
        Err(Error::InvalidPublicParameters(reason)) => {
            assert!(
                reason.contains(what),
                "refused for {reason:?}, not {what:?}"
            );
        }
        Err(other) => panic!("expected InvalidPublicParameters ({what}), got {other:?}"),
        Ok(_) => panic!("accepted public parameters with a modified {what}"),
    }
}

/// The checks of a received `pp` that hold for every pair: `Setup` is transparent (line 350),
/// so a received `pp` is accepted only as what `Setup` derives from the label it carries.
fn received_pp<B: Base<E>, T: ProtocolTag<G1> + 'static>(label: &[u8]) {
    let pcreds = Protocol::<Bk<B, T>>::setup(label).expect("Setup");
    let pp = pcreds.public_parameters().clone();
    let back = Protocol::from_public_parameters(
        PublicParameters::<Bk<B, T>>::from_bytes(&pp.to_bytes().expect("pp")).expect("pp"),
    )
    .expect("the derived pp");
    assert_eq!(back.parameters_digest(), pcreds.parameters_digest());
    assert_eq!(back.public_parameters(), &pp);

    // The pp of this label carried under another label.
    let mut bad = pp.clone();
    bad.label = b"pcreds/pp/another deployment".to_vec();
    assert_refused(Protocol::from_public_parameters(bad), "parameters");
    // The label of another deployment with the parameters of this one.
    let other = Protocol::<Bk<B, T>>::setup(b"pcreds/pp/another deployment")
        .expect("Setup")
        .public_parameters()
        .clone();
    let mut bad = other.clone();
    bad.params = pp.params.clone();
    assert_refused(Protocol::from_public_parameters(bad), "parameters");

    // Against parameters the receiver expects.
    assert!(Protocol::from_public_parameters_with_params(pp.clone(), &pp.params).is_ok());
    assert_refused(
        Protocol::from_public_parameters_with_params(other, &pp.params),
        "expected",
    );
}

/// `Protocol::from_public_parameters` accepts the derived `pp` and refuses a modified `x_0`,
/// modified base parameters (the generators of `Σ-BBS`) and modified tag parameters (the
/// generator of `Tag_DY`, the domain of `Tag_DDH`), with `InvalidPublicParameters`: parameters
/// that are merely well formed are not good enough.
#[test]
fn received_public_parameters_must_be_the_derived_ones() {
    received_pp::<PS, DDH>(b"pcreds/pp/ps+ddh");
    received_pp::<PS, DY>(b"pcreds/pp/ps+dy");
    received_pp::<BBS, DDH>(b"pcreds/pp/bbs+ddh");
    received_pp::<BBS, DY>(b"pcreds/pp/bbs+dy");

    // pp_Σ of Σ-BBS: the generators of another label, two of them swapped, the identity.
    let label = b"pcreds/pp/bbs-generators";
    let pp = Protocol::<Bk<BBS, DDH>>::setup(label)
        .expect("Setup")
        .public_parameters()
        .clone();
    let base = &pp.params.base;
    for modified in [
        <BBS as Base<E>>::setup(b"pcreds/pp/another deployment").expect("generators"),
        BBSParams {
            h0: base.hu,
            hu: base.h0,
            hr: base.hr,
        },
        BBSParams {
            h0: G1::zero(),
            ..base.clone()
        },
    ] {
        let mut bad = pp.clone();
        bad.params.base = modified;
        assert_refused(Protocol::from_public_parameters(bad), "parameters");
    }

    // pp_Tag of Tag_DY: the standard generator of G_1, the generator of another label, a
    // multiple of the derived one.
    let label = b"pcreds/pp/dy-generator";
    let pp = Protocol::<Bk<PS, DY>>::setup(label)
        .expect("Setup")
        .public_parameters()
        .clone();
    let derived = *pp.params.tag.generator();
    for modified in [
        DY::new(),
        DY::derive(b"pcreds/pp/another deployment").expect("generator"),
        DY::with_generator(derived * Fr::from(2u64)).expect("generator"),
    ] {
        let mut bad = pp.clone();
        bad.params.tag = modified;
        assert_refused(Protocol::from_public_parameters(bad), "parameters");
    }

    // pp_Tag of Tag_DDH: the oracle htag of another deployment label.
    let label = b"pcreds/pp/ddh-domain";
    let pp = Protocol::<Bk<BBS, DDH>>::setup(label)
        .expect("Setup")
        .public_parameters()
        .clone();
    let mut bad = pp.clone();
    bad.params.tag = DDH::new(
        <G1Hasher as HashToGroup<G1>>::new(b"pcreds/pp/another deployment").expect("oracle"),
    );
    assert_refused(Protocol::from_public_parameters(bad), "parameters");

    // `setup_with_params`: parameters that are NOT derived from the label make a deployment of
    // their own, with another digest; its pp is refused as derived and accepted as expected.
    let custom = PairingParams {
        base: <BBS as Base<E>>::setup(b"pcreds/pp/elsewhere").expect("generators"),
        tag: DDH::setup(label).expect("htag"),
    };
    let derived = Protocol::<Bk<BBS, DDH>>::setup(label).expect("Setup");
    let custom_pcreds =
        Protocol::<Bk<BBS, DDH>>::setup_with_params(label, custom.clone()).expect("Setup");
    assert_ne!(
        custom_pcreds.parameters_digest(),
        derived.parameters_digest()
    );
    let custom_pp = custom_pcreds.public_parameters().clone();
    assert_refused(
        Protocol::from_public_parameters(custom_pp.clone()),
        "derived",
    );
    assert!(Protocol::from_public_parameters_with_params(custom_pp.clone(), &custom).is_ok());
    assert_refused(
        Protocol::from_public_parameters_with_params(custom_pp, derived.params()),
        "expected",
    );
}

/// Objects made for one deployment are refused in another, even under the same `vk` and with
/// the same algebraic parameters: `Σ-PS` (empty `pp_Σ`) with `Tag_DY` over the standard
/// generator, set up with `setup_with_params` for two labels. Only the label (and `x_0`, derived
/// from it) separates the two, and the digest of `pp` leads every context.
#[test]
fn objects_of_one_deployment_are_refused_in_another() {
    let params = PairingParams {
        base: (),
        tag: DY::new(),
    };
    let here_pcreds =
        Protocol::<Bk<PS, DY>>::setup_with_params(b"pcreds/deployments/here", params.clone())
            .expect("Setup");
    let policy = Policy::threshold(1).expect("k ≥ 1");
    let mut here = Net::on(here_pcreds, policy, 0xc205_5001);
    let there = Protocol::<Bk<PS, DY>>::setup_with_params(b"pcreds/deployments/there", params)
        .expect("Setup");
    assert_eq!(here.pcreds.params(), there.params());
    assert_ne!(here.pcreds.parameters_digest(), there.parameters_digest());

    let root = here.roots(1).pop().expect("a root");
    let q = here.register();
    let ssid = here.ssid();
    let request = here
        .pcreds
        .request_attestation(&here.hvk, &q, &ssid, &root.contact, &mut here.rng)
        .expect("π_id");
    let pending = here
        .pcreds
        .receive_attestation_request(&here.hvk, &request, &ssid, &root.contact)
        .expect("π_id");
    let att = here
        .pcreds
        .attest(&here.hvk, &root.user, &root.cred, pending, &mut here.rng)
        .expect("attest");
    let proof = here
        .pcreds
        .prove(&here.hvk, &root.user, &root.cred, b"m", &mut here.rng)
        .expect("Prove");

    // `there` checks the same vk once, under its own pp: the objects of `here` are refused.
    let hvk_there = there.helper_key(here.hvk.vk()).expect("hvk ∈ V_pp");
    assert_eq!(hvk_there.vk(), here.hvk.vk());
    assert_ne!(hvk_there, here.hvk);
    assert_eq!(
        there
            .receive_attestation_request(&hvk_there, &request, &ssid, &root.contact)
            .err(),
        Some(Error::InvalidProof)
    );
    assert_eq!(
        there.check_attestation(&hvk_there, q.id(), &att),
        Err(Error::InvalidProof)
    );
    assert_eq!(
        there.check_membership(&hvk_there, b"m", &proof),
        Err(Error::InvalidProof)
    );

    // Keys, users, pending requests, states and evaluated requests of `here` belong to it.
    let mut rng = StdRng::seed_from_u64(0xc205_5002);
    let user_there = there.register(&hvk_there, &mut rng).expect("Register");
    let mut helper_there = there.helper_keygen(policy, &mut rng);
    assert_eq!(
        there.check_attestation(&here.hvk, q.id(), &att),
        Err(Error::InvalidKey)
    );
    assert_eq!(
        there
            .request_attestation(&hvk_there, &q, &ssid, &root.contact, &mut rng)
            .err(),
        Some(Error::IdentifierMismatch)
    );
    assert_eq!(
        there.check_user(&hvk_there, &root.user),
        Err(Error::IdentifierMismatch)
    );
    assert!(!there.verify_credential(&hvk_there, &root.user, &root.cred));
    // the request received again in `here` (the first pending request was consumed)
    let pending = here
        .pcreds
        .receive_attestation_request(&here.hvk, &request, &ssid, &root.contact)
        .expect("π_id");
    assert_eq!(
        there
            .attest(&hvk_there, &user_there, &root.cred, pending, &mut rng)
            .err(),
        Some(Error::IdentifierMismatch)
    );
    let (ssid, message, state) = here.request(&q, vec![att]);
    assert_eq!(
        there
            .request_credential(&here.hvk, &user_there, Vec::new(), &ssid, &mut rng)
            .err(),
        Some(Error::InvalidKey)
    );
    assert_eq!(
        there.evaluate_request(&here.helper, &message, &ssid).err(),
        Some(Error::InvalidKey)
    );
    let evaluated = here.evaluate(&message, &ssid);
    assert_eq!(
        there
            .respond(&mut helper_there, evaluated, Decision::Policy, &mut rng)
            .err(),
        Some(Error::InvalidKey)
    );
    let reply = here.answer(&message, &ssid, Decision::Policy);
    let Reply::PreCredential(pre) = reply.clone() else {
        panic!("q is issued in `here`");
    };
    assert_eq!(
        there
            .unblind(&hvk_there, &user_there, &pre, copy(&state))
            .err(),
        Some(Error::IssuanceStateMismatch)
    );
    // Control: in `here`, the reply unblinds.
    here.unblind(&q, reply, state);
}

/// Implementation note of `Helper` (src/pcreds/types.rs): "Nothing else ties a key to a
/// deployment: a credential of `Σ-PS` is a signature under `hvk` and nothing more, so a helper
/// that served two deployment labels with one key would certify, in each of them, users of the
/// other." Both halves: the `Σ-PS` credential of `here`, held under the same key `usk` in
/// `there`, IS a credential of `there` under the same `vk` (and attests there); `there` refuses
/// to run a helper on the key of `here`. Under `Σ-BBS` the generators of `pp_Σ` come from the
/// label, and the transfer fails at the base already.
#[test]
fn a_helper_key_serves_one_deployment() {
    let policy = Policy::threshold(1).expect("k ≥ 1");
    let mut here = Net::<Bk<PS, DDH>>::new(b"pcreds/one-key/here", 1, 0x0e1e_0001);
    let member = here.roots(1).pop().expect("a root");
    let there = Protocol::<Bk<PS, DDH>>::setup(b"pcreds/one-key/there").expect("Setup");
    let mut rng = StdRng::seed_from_u64(0x0e1e_0002);
    let hvk_there = there.helper_key(here.hvk.vk()).expect("hvk ∈ V_pp");
    let user_there = there
        .user(&hvk_there, *member.user.expose_key())
        .expect("a key of Register");
    assert_ne!(user_there.id(), member.user.id(), "id is a tag at x_0");
    let cred_there = there
        .credential(&hvk_there, &user_there, member.cred.as_inner().clone())
        .expect("a Σ-PS credential is a signature on usk alone");
    let newcomer = there.register(&hvk_there, &mut rng).expect("Register");
    let request = there
        .request_attestation(&hvk_there, &newcomer, b"ssid", b"member@there", &mut rng)
        .expect("π_id");
    let pending = there
        .receive_attestation_request(&hvk_there, &request, b"ssid", b"member@there")
        .expect("π_id");
    let att = there
        .attest(&hvk_there, &user_there, &cred_there, pending, &mut rng)
        .expect("attest");
    assert_eq!(
        there.check_attestation(&hvk_there, newcomer.id(), &att),
        Ok(())
    );
    let key = here.helper.to_bytes().expect("the key encodes");
    assert_eq!(
        there
            .restore_helper(&key, policy, IssuanceRecord::new())
            .err(),
        Some(Error::InvalidKey)
    );

    let mut here = Net::<Bk<BBS, DDH>>::new(b"pcreds/one-key/here", 1, 0x0e1e_0003);
    let member = here.roots(1).pop().expect("a root");
    let there = Protocol::<Bk<BBS, DDH>>::setup(b"pcreds/one-key/there").expect("Setup");
    let hvk_there = there.helper_key(here.hvk.vk()).expect("hvk ∈ V_pp");
    let user_there = there
        .user(&hvk_there, *member.user.expose_key())
        .expect("a key of Register");
    assert_eq!(
        there
            .credential(&hvk_there, &user_there, member.cred.as_inner().clone())
            .err(),
        Some(Error::InvalidCredential)
    );
    let key = here.helper.to_bytes().expect("the key encodes");
    assert_eq!(
        there
            .restore_helper(&key, policy, IssuanceRecord::new())
            .err(),
        Some(Error::InvalidKey)
    );
}

// ---------------------------------------------------------------------------------------------
// Tag_DY: undefined evaluations
// ---------------------------------------------------------------------------------------------

/// `Tag_DY` (§6.1.2) is `⊥` at the one point `x = −K`: `Register` (line 356) skips the key
/// `−x_0`, and an attester whose key is `usk_P = −x_Q` for the recipient point `x_Q` of `Q`
/// cannot attest for `Q` ("an attestation aborts", `kiprf::dy`), while it attests for everybody
/// else.
fn tag_dy_undefined<B: Base<E> + BaseFacts>(label: &[u8], seed: u64) {
    let mut net = Net::<Bk<B, DY>>::new(label, 1, seed);
    let x0 = *net.hvk.identifier_point();
    assert_eq!(
        net.pcreds.user(&net.hvk, -x0).err(),
        Some(Error::UndefinedTag)
    );

    let q = net.register();
    let xq = net
        .pcreds
        .recipient_point(net.hvk.vk(), q.id())
        .expect("x_Q");
    assert_ne!(xq, x0, "H_req has values in X \\ {{x_0}}");
    let unlucky = net
        .pcreds
        .user(&net.hvk, -xq)
        .expect("x_Q ≠ x_0: −x_Q is a key");
    let unlucky = net.admit_root(unlucky);
    let ssid = net.ssid();
    let request = net
        .pcreds
        .request_attestation(&net.hvk, &q, &ssid, &unlucky.contact, &mut net.rng)
        .expect("π_id");
    let pending = net
        .pcreds
        .receive_attestation_request(&net.hvk, &request, &ssid, &unlucky.contact)
        .expect("π_id");
    assert_eq!(
        net.pcreds
            .attest(
                &net.hvk,
                &unlucky.user,
                &unlucky.cred,
                pending,
                &mut net.rng
            )
            .err(),
        Some(Error::UndefinedTag)
    );
    // For any other recipient it attests like any member, and Q is attested by others.
    let r = net.register();
    net.attestation(&unlucky, &r);
    let other = net.roots(1).pop().expect("a root");
    let att = net.attestation(&other, &q);
    net.join(q, vec![att]);
}

#[test]
fn tag_dy_attester_at_its_undefined_point() {
    tag_dy_undefined::<PS>(b"pcreds/dy-undefined/ps", 0xd1d1_0001);
    tag_dy_undefined::<BBS>(b"pcreds/dy-undefined/bbs", 0xd1d1_0002);

    // Tag_DDH is total on its key space Z_p \ {0}: the key −x_Q attests for Q like any other,
    // and 0 is no key.
    let mut net = Net::<Bk<PS, DDH>>::new(b"pcreds/dy-undefined/ddh", 1, 0xd1d1_0003);
    let q = net.register();
    let xq = net
        .pcreds
        .recipient_point(net.hvk.vk(), q.id())
        .expect("x_Q");
    let user = net.pcreds.user(&net.hvk, -xq).expect("a key");
    let attester = net.admit_root(user);
    net.attestation(&attester, &q);
    assert_eq!(
        net.pcreds.user(&net.hvk, Fr::zero()).err(),
        Some(Error::UndefinedTag)
    );
}

// ---------------------------------------------------------------------------------------------
// Unblind
// ---------------------------------------------------------------------------------------------

/// `Unblind` fails closed (line 423: "check `Verify(hvk, usk_Q, σ_Q) = 1`"): garbage
/// pre-credentials, genuine ones altered, and genuine ones of another request do not unblind;
/// a state belongs to its requester.
fn garbage_pre_credentials<B: Base<E> + BaseFacts, T: ProtocolTag<G1> + 'static>(
    label: &[u8],
    seed: u64,
    garbage: impl Fn(&B::PreCredential, &mut StdRng) -> Vec<B::PreCredential>,
) {
    let mut net = Net::<Bk<B, T>>::new(label, 1, seed);
    let (q, r) = (net.register(), net.register());
    let (ssid, message, state) = net.request(&q, Vec::new());
    let Reply::PreCredential(genuine) = net.answer(&message, &ssid, Decision::Root) else {
        panic!("d = root issues");
    };
    for pre in garbage(&genuine, &mut net.rng) {
        assert_eq!(
            net.pcreds.unblind(&net.hvk, &q, &pre, copy(&state)).err(),
            Some(Error::InvalidPreCredential)
        );
    }
    let (ssid_r, message_r, state_r) = net.request(&r, Vec::new());
    let Reply::PreCredential(pre_r) = net.answer(&message_r, &ssid_r, Decision::Root) else {
        panic!("d = root issues");
    };
    assert_eq!(
        net.pcreds.unblind(&net.hvk, &q, &pre_r, copy(&state)).err(),
        Some(Error::InvalidPreCredential)
    );
    assert_eq!(
        net.pcreds.unblind(&net.hvk, &r, &pre_r, copy(&state)).err(),
        Some(Error::IssuanceStateMismatch)
    );
    // Control.
    net.unblind(&q, Reply::PreCredential(genuine), state);
    net.unblind(&r, Reply::PreCredential(pre_r), state_r);
}

#[test]
fn unblind_rejects_garbage_pre_credentials() {
    garbage_pre_credentials::<PS, DDH>(b"pcreds/garbage/ps", 0x6a2b_0001, |genuine, rng| {
        vec![
            PSPair {
                s1: G1::rand(rng),
                s2: G1::rand(rng),
            },
            PSPair {
                s1: G1::zero(),
                s2: G1::zero(),
            },
            PSPair {
                s1: genuine.s1,
                s2: genuine.s2 + G1::generator(),
            },
            PSPair {
                s1: genuine.s1 * Fr::from(2u64),
                s2: genuine.s2,
            },
        ]
    });
    garbage_pre_credentials::<BBS, DY>(b"pcreds/garbage/bbs", 0x6a2b_0002, |genuine, rng| {
        vec![
            BBSPreCredential {
                a: G1::rand(rng),
                e: Fr::rand(rng),
            },
            BBSPreCredential {
                a: G1::zero(),
                e: Fr::zero(),
            },
            BBSPreCredential {
                a: genuine.a,
                e: genuine.e + Fr::one(),
            },
            BBSPreCredential {
                a: genuine.a + G1::generator(),
                e: genuine.e,
            },
        ]
    });
}

/// The issuance state is the randomness `τ` of ONE request (`CredentialRequest` (i), line 403:
/// "Sample `τ`"): two requests have independent `Ĉ = PrepareIssue(hvk, usk_Q; τ)`, and the
/// pre-credential of one does not unblind with the state of the other. The states are secret.
#[test]
fn issuance_states_are_per_request() {
    // Σ-BBS: Ĉ = B(usk, τ) = h_0 h_u^usk h_r^τ.
    let mut net = Net::<Bk<BBS, DDH>>::new(b"pcreds/state/bbs", 1, 0x57a7_e001);
    let q = net.register();
    let (ssid_1, message_1, state_1) = net.request(&q, Vec::new());
    let (ssid_2, message_2, state_2) = net.request(&q, Vec::new());
    assert_ne!(message_1.request, message_2.request);
    for (message, state) in [(&message_1, &state_1), (&message_2, &state_2)] {
        assert_eq!(
            message.request.0,
            net.pcreds
                .params()
                .base
                .b(q.expose_key(), state.expose_tape())
        );
    }
    assert_eq!(format!("{state_1:?}"), "IssuanceState(<redacted>)");
    let Reply::PreCredential(pre_1) = net.answer(&message_1, &ssid_1, Decision::Root) else {
        panic!("d = root issues");
    };
    assert_eq!(
        net.pcreds.unblind(&net.hvk, &q, &pre_1, state_2).err(),
        Some(Error::InvalidPreCredential)
    );
    net.unblind(&q, Reply::PreCredential(pre_1), state_1);
    assert_eq!(
        net.answer(&message_2, &ssid_2, Decision::Root),
        Reply::Issued
    );

    // Σ-PS: Ĉ = g_1^τ Y^usk, with Y = g_1^y of hvk.
    let mut net = Net::<Bk<PS, DY>>::new(b"pcreds/state/ps", 1, 0x57a7_e002);
    let q = net.register();
    let (_, message, state) = net.request(&q, Vec::new());
    assert_eq!(
        message.request.0,
        G1::generator() * state.expose_tape() + net.hvk.vk().y1 * q.expose_key()
    );
}
