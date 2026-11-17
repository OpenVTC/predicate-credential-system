//! Predicate credentials: the ideal functionality `F_PCreds` and the protocol `Π_PCreds` of the
//! paper (§4), generic over an instantiation of its building blocks.
//!
//! "A predicate credential system (PCreds) lets users obtain a credential from a helper once
//! enough credentialed users satisfying some policy attest for them, and then prove anonymously
//! that they are credentialed or that a message comes from a credentialed user" (§4). Security is
//! defined by the ideal functionality `F_PCreds` (§4.1), and `Π_PCreds` realizes it for the
//! threshold policy `Pol_k` (Theorem "Security of `Π_PCreds`", §4.3).
//!
//! # The interfaces of `F_PCreds`
//!
//! | `F_PCreds` (§4.1) | `Π_PCreds` (§4.2) | here |
//! |---|---|---|
//! | (setup, helper) | `pp = (pp_Σ, H_id, H_req, H_1)`; `(hvk, sk) ← KeyGen(pp)`, `I ← ∅`; `x_0 = H_id(⟨hvk⟩)` | [`Protocol::setup`], [`Protocol::helper_keygen`]; users check `hvk` once and derive `x_0`: [`Protocol::helper_key`] |
//! | `Register` | `usk ← TagKeyGen(1^λ)` (or a reused one), `id = Tag(usk, x_0)`, `RegisterFailed` if `⊥` | [`Protocol::register`], [`Protocol::register_reusing`] |
//! | `ContactRegister` | a route with the contact service | (the application's contact service) |
//! | `AttestationRequest` | `π_id` under `(ssid, P̃)`; the owner checks it | [`Protocol::request_attestation`], [`Protocol::receive_attestation_request`] |
//! | `AttestationRequestResponse` | `att = (t_{P→Q}, σ*, π_att)` at `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`; `Q` checks it | [`Protocol::attest`], [`Protocol::check_attestation`] |
//! | `CredentialRequest` | `(id_Q, att⃗, Ĉ, π_iss)`; the helper checks `π_iss` and counts `N''` | [`Protocol::request_credential`], [`Protocol::evaluate_request`] |
//! | `CredentialRequestResponse` | `Fail`, `issued`, or `σ̂ ← BlindIssue(sk, Ĉ)`; `Unblind` and `Verify` | [`Protocol::respond`], [`Protocol::unblind`] |
//! | `Prove` | `σ* = ReRand(…)`, `π_prove` under `m` | [`Protocol::prove`] |
//! | `Verify` | the check of `π_prove` | [`Protocol::verify`] |
//!
//! # Instantiations
//!
//! "Our starting point is a credential base `Σ` that certifies a user's secret tag key `usk`",
//! with a key-injective PRF `Tag` and an online simulation-extractable NIZK (§4.2). The code is
//! generic in the same way: [`Protocol`] is written once over a [`Backend`], one instantiation of
//! the three. [`pairing::PairingBackend`] is the pairing-based instantiation of §5 (`Σ-PS` and
//! `Σ-BBS` with `Tag_DDH` and `Tag_DY` over BLS12-381, generalized Schnorr proofs); the
//! post-quantum instantiation of §5.2.3 (`Σ-vSIS` with the short-key `Tag_LWR` and Jali proofs) is
//! `lattice::LatticeBackend` (feature `lattice`).
//!
//! # Example
//!
//! Two root users are admitted by the helper, attest for a newcomer, who obtains a credential
//! under the threshold policy `Pol_2` and proves membership on a message:
//!
//! ```
//! use ark_bls12_381::{Bls12_381, G1Projective};
//! use predicate_credential_system::{
//!     hash::bls12_381::G1Hasher,
//!     kiprf::DDH,
//!     pcreds::{Decision, Policy, Reply, pairing::{PS, PairingProtocol}},
//! };
//! use rand::{SeedableRng, rngs::StdRng};
//!
//! type Scheme = PairingProtocol<Bls12_381, PS, DDH<G1Projective, G1Hasher>>;
//!
//! let mut rng = StdRng::seed_from_u64(1);
//! let pcreds = Scheme::setup(b"example deployment")?;
//! let mut helper = pcreds.helper_keygen(Policy::threshold(2)?, &mut rng);
//! // a user checks the published helper key once, which derives its identifier point x_0
//! let hvk = pcreds.helper_key(helper.key().vk())?;
//!
//! // Root users: ordinary requests, admitted by the helper's decision d = root.
//! let mut members = Vec::new();
//! for i in 0..2 {
//!     let user = pcreds.register(&hvk, &mut rng)?;
//!     let ssid = format!("root-{i}").into_bytes();
//!     let (message, state) = pcreds.request_credential(&hvk, &user, Vec::new(), &ssid, &mut rng)?;
//!     let evaluated = pcreds.evaluate_request(&helper, &message, &ssid)?;
//!     let Reply::PreCredential(pre) = pcreds.respond(&mut helper, evaluated, Decision::Root, &mut rng)? else {
//!         unreachable!("a root admission issues");
//!     };
//!     let cred = pcreds.unblind(&hvk, &user, &pre, state)?;
//!     members.push((user, cred));
//! }
//!
//! // A newcomer asks each member for an attestation, through the member's contact name.
//! let newcomer = pcreds.register(&hvk, &mut rng)?;
//! let mut attestations = Vec::new();
//! for (j, (member, cred)) in members.iter().enumerate() {
//!     let (ssid, contact) = (format!("att-{j}").into_bytes(), format!("member-{j}").into_bytes());
//!     let request = pcreds.request_attestation(&hvk, &newcomer, &ssid, &contact, &mut rng)?;
//!     let pending = pcreds.receive_attestation_request(&hvk, &request, &ssid, &contact)?;
//!     let att = pcreds.attest(&hvk, member, cred, pending, &mut rng)?;
//!     pcreds.check_attestation(&hvk, newcomer.id(), &att)?;
//!     attestations.push(att);
//! }
//!
//! // The credential request: the helper sees id_Q, the tags and the policy result.
//! let (message, state) = pcreds.request_credential(&hvk, &newcomer, attestations, b"req", &mut rng)?;
//! let evaluated = pcreds.evaluate_request(&helper, &message, b"req")?;
//! assert!(evaluated.is_valid());
//! let Reply::PreCredential(pre) = pcreds.respond(&mut helper, evaluated, Decision::Policy, &mut rng)? else {
//!     unreachable!("a valid request is issued");
//! };
//! let cred = pcreds.unblind(&hvk, &newcomer, &pre, state)?;
//!
//! // Anonymous use: a membership proof on a message.
//! let proof = pcreds.prove(&hvk, &newcomer, &cred, b"hello", &mut rng)?;
//! assert!(pcreds.verify(&hvk, b"hello", &proof));
//! # Ok::<(), predicate_credential_system::Error>(())
//! ```
//!
//! # Differences from the earlier construction
//!
//! The earlier, game-based construction of the paper was implemented by a module `pcs`, which
//! this crate no longer has (the git tag `pcs-final` keeps it).
//!
//! * A credential certifies `usk` alone, with no public attribute or predicate label (Remark
//!   "Additional attributes" describes the extension). `Σ-PS` shows are blinded by a fresh
//!   offset, `(σ_1^r, (σ_2 σ_1^t)^r)`, so a show is a uniform pair; `Σ-BBS` shows carry the third
//!   possession clause `D = B̄^u Ā^v`, and the credential keeps `ρ`.
//! * There is no self-exclusion tag: the helper keeps the set `I` of identifiers it has issued
//!   to, issues at most once per identifier, and answers later valid requests with `issued`.
//! * The requester proves ownership of its identifier to each attester (`π_id`); the attestation
//!   proof has no session context; the recipient point is `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`.
//! * The identifier point is `x_0 = H_id(⟨hvk⟩)`, one per helper key, not a point of `pp`: a
//!   user's identifiers under two helper keys are evaluations at independent points.
//! * Membership proofs on a message are separate from issuance.
//! * The helper decides root admission on an ordinary request (`d = root`); there is no separate
//!   root request.

mod backend;
pub mod codec;
mod context;
#[cfg(feature = "lattice")]
pub mod lattice;
pub mod pairing;
mod protocol;
pub mod types;

pub use self::{
    backend::{AttestationStatement, Backend, IssuanceStatement, Leaf, ProofKind},
    protocol::{PendingAttestation, Protocol},
    types::{
        Attestation, AttestationRequest, Credential, CredentialRequest, Decision, EvaluatedRequest,
        Helper, HelperKey, IssuanceRecord, IssuanceState, IssuanceStore, MembershipProof, Policy,
        PublicParameters, Reply, User,
    },
};
