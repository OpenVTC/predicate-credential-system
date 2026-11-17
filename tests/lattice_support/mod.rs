//! Shared code of the lattice integration tests (`lattice_protocol.rs`, `lattice_flows.rs`,
//! `lattice_adversarial.rs`, `lattice_attacks.rs`, `lattice_parallel.rs`, `lattice_sizes.rs`).
//! Everything goes through the PUBLIC API of the crate: the protocol
//! [`predicate_credential_system::pcreds::Protocol`] over
//! [`predicate_credential_system::pcreds::lattice::LatticeBackend`], and the backend's
//! associated functions for a CHEATING PROVER that proves real statements under contexts or
//! for statements that the honest protocol would not choose.
//!
//! * [`Deployment`]: one deployment with ONE real helper key (`KeyGen` = an NTRU trapdoor) and
//!   root members with credentials; every randomized step draws from one seeded RNG, recorded
//!   at the call site.
//! * [`timed`]: wall-clock timing of a step, printed with `--nocapture`.
//!
//! Proofs of this backend take seconds and up to about 0.7 GB each: the suites run their heavy
//! tests in release builds only (`#[cfg_attr(debug_assertions, ignore)]` or `#[ignore]`, with the
//! command in the reason).
#![allow(dead_code)] // each test binary uses a part of this module

use std::time::Instant;

use predicate_credential_system::{
    Error,
    pcreds::{
        Attestation, Credential, CredentialRequest, Decision, Helper, HelperKey, IssuanceState,
        Policy, Protocol, Reply, User,
        lattice::{LatticeBackend, LatticeProtocol},
    },
};
use rand::{SeedableRng, rngs::StdRng};

/// The backend of these suites.
pub type Bk = LatticeBackend;

/// What a requester gets back from the helper: a credential (unblinded and verified), or the
/// helper's `Fail` or `issued`.
pub enum Outcome {
    /// The pre-credential was unblinded into this credential (boxed: it is far larger than the
    /// other variants).
    Credential(Box<Credential<Bk>>),
    /// `(ssid, Fail)`.
    Fail,
    /// `(ssid, issued)`.
    Issued,
}

impl Outcome {
    /// The credential; panics for `Fail` and `issued`.
    pub fn credential(self) -> Credential<Bk> {
        match self {
            Self::Credential(cred) => *cred,
            Self::Fail => panic!("the helper answered Fail"),
            Self::Issued => panic!("the helper answered issued"),
        }
    }

    /// Whether the helper answered `Fail`.
    pub fn is_fail(&self) -> bool {
        matches!(self, Self::Fail)
    }

    /// Whether the helper answered `issued`.
    pub fn is_issued(&self) -> bool {
        matches!(self, Self::Issued)
    }
}

/// A member of a deployment: a user with a credential.
pub struct Member {
    pub user: User<Bk>,
    pub cred: Credential<Bk>,
}

/// A deployment: the protocol, its helper under a policy, the checked helper key, root members
/// with credentials, and a seeded RNG.
pub struct Deployment {
    pub pcreds: LatticeProtocol,
    pub helper: Helper<Bk>,
    pub hvk: HelperKey<Bk>,
    pub members: Vec<Member>,
    pub rng: StdRng,
    /// A counter for fresh sub-session identifiers.
    ssid: u64,
}

impl Deployment {
    /// The deployment `label` under `Pol_k` with `roots` root members.
    pub fn new(label: &[u8], k: usize, roots: usize, seed: u64) -> Self {
        Self::with_policy(label, Policy::threshold(k).expect("k ≥ 1"), roots, seed)
    }

    /// The deployment `label` under `policy` with `roots` root members.
    pub fn with_policy(label: &[u8], policy: Policy, roots: usize, seed: u64) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        let pcreds = Protocol::setup(label).expect("setup");
        let helper = pcreds.helper_keygen(policy, &mut rng);
        let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
        let mut deployment = Self {
            pcreds,
            helper,
            hvk,
            members: Vec::new(),
            rng,
            ssid: 0,
        };
        for _ in 0..roots {
            let user = deployment.register();
            let cred = deployment.admit_root(&user).expect("root admission");
            deployment.members.push(Member { user, cred });
        }
        deployment
    }

    /// A fresh sub-session identifier.
    pub fn ssid(&mut self) -> Vec<u8> {
        self.ssid += 1;
        format!("ssid-{}", self.ssid).into_bytes()
    }

    /// `Register`.
    pub fn register(&mut self) -> User<Bk> {
        self.pcreds
            .register(&self.hvk, &mut self.rng)
            .expect("register")
    }

    /// An ordinary request without attestations, admitted with `d = root`; the credential.
    ///
    /// # Errors
    /// Whatever the protocol returns on the way.
    pub fn admit_root(&mut self, user: &User<Bk>) -> Result<Credential<Bk>, Error> {
        let ssid = self.ssid();
        let (message, state) =
            self.pcreds
                .request_credential(&self.hvk, user, Vec::new(), &ssid, &mut self.rng)?;
        Ok(self
            .answer(user, &message, state, &ssid, Decision::Root)?
            .credential())
    }

    /// The helper evaluates `message` under `ssid` and responds with `decision`; the requester
    /// unblinds a pre-credential.
    ///
    /// # Errors
    /// Whatever the protocol returns.
    pub fn answer(
        &mut self,
        user: &User<Bk>,
        message: &CredentialRequest<Bk>,
        state: IssuanceState<Bk>,
        ssid: &[u8],
        decision: Decision,
    ) -> Result<Outcome, Error> {
        let evaluated = self.pcreds.evaluate_request(&self.helper, message, ssid)?;
        Ok(
            match self
                .pcreds
                .respond(&mut self.helper, evaluated, decision, &mut self.rng)?
            {
                Reply::PreCredential(pre) => Outcome::Credential(Box::new(
                    self.pcreds.unblind(&self.hvk, user, &pre, state)?,
                )),
                Reply::Fail => Outcome::Fail,
                Reply::Issued => Outcome::Issued,
            },
        )
    }

    /// An attestation from member `j` for `user`, through `AttestationRequest` and
    /// `AttestationRequestResponse`.
    pub fn attestation(&mut self, j: usize, user: &User<Bk>) -> Attestation<Bk> {
        let ssid = self.ssid();
        let contact = format!("member-{j}@example").into_bytes();
        let request = self
            .pcreds
            .request_attestation(&self.hvk, user, &ssid, &contact, &mut self.rng)
            .expect("attestation request");
        let pending = self
            .pcreds
            .receive_attestation_request(&self.hvk, &request, &ssid, &contact)
            .expect("π_id");
        let member = &self.members[j];
        self.pcreds
            .attest(
                &self.hvk,
                &member.user,
                &member.cred,
                pending,
                &mut self.rng,
            )
            .expect("attest")
    }

    /// One attestation from each of the first `n` members for `user`.
    pub fn attestations(&mut self, user: &User<Bk>, n: usize) -> Vec<Attestation<Bk>> {
        (0..n).map(|j| self.attestation(j, user)).collect()
    }

    /// A credential request of `user` with `attestations` under a fresh `ssid`: the message, the
    /// state and the `ssid`.
    pub fn request(
        &mut self,
        user: &User<Bk>,
        attestations: Vec<Attestation<Bk>>,
    ) -> (CredentialRequest<Bk>, IssuanceState<Bk>, Vec<u8>) {
        let ssid = self.ssid();
        let (message, state) = self
            .pcreds
            .request_credential(&self.hvk, user, attestations, &ssid, &mut self.rng)
            .expect("request");
        (message, state, ssid)
    }

    /// A newcomer with a credential obtained through one attestation from each of the first `n`
    /// members, under the helper's policy.
    pub fn newcomer(&mut self, n: usize) -> Member {
        let user = self.register();
        let attestations = self.attestations(&user, n);
        let (message, state, ssid) = self.request(&user, attestations);
        let cred = self
            .answer(&user, &message, state, &ssid, Decision::Policy)
            .expect("issuance")
            .credential();
        Member { user, cred }
    }
}

/// Runs `f`, prints its wall-clock time under `name` (visible with `--nocapture`), and returns
/// its result.
pub fn timed<T>(name: &str, f: impl FnOnce() -> T) -> T {
    let start = Instant::now();
    let out = f();
    println!("[time] {name}: {:.2} s", start.elapsed().as_secs_f64());
    out
}
