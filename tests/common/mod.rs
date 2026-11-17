//! Shared fixtures for the integration suites of the protocol (`pcreds_*.rs`,
//! `serialization.rs`, `serde_json.rs`).
//!
//! This module is compiled into each suite that declares `mod common;`; not every suite uses
//! every item (hence the blanket `allow(dead_code)`). Everything here drives the crate through
//! its PUBLIC API only. All randomness is seeded (`StdRng::seed_from_u64`, the seed recorded at
//! every call site) and reproducible.

#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs
#![allow(dead_code)]

use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ff::{UniformRand, Zero};
use predicate_credential_system::{
    Error,
    hash::bls12_381::G1Hasher,
    kiprf::{self, ProtocolTag},
    pcreds::{
        Attestation, Credential, CredentialRequest, Decision, Helper, HelperKey, IssuanceState,
        Policy, Protocol, Reply, User,
        pairing::{self, BBSShow, Base, G1Request, PSPair, PairingBackend},
    },
    sigma::FSProof,
};
use rand::{SeedableRng, rngs::StdRng};

pub type E = Bls12_381;
pub type G1 = G1Projective;
pub type G2 = G2Projective;
pub type PS = pairing::PS;
pub type BBS = pairing::BBS<G1Hasher>;
pub type DDH = kiprf::DDH<G1, G1Hasher>;
pub type DY = kiprf::DY<G1, G1Hasher>;
/// The pairing backend for the base `B` and the tag `T` over BLS12-381.
pub type Bk<B, T> = PairingBackend<E, B, T>;

/// Per-base test hooks that the generic suites need and the public interface does not expose:
/// random and degenerate shows and requests, and the group-element decomposition of a show (for
/// exhaustive mutation).
pub trait BaseTest: Base<E, Request = G1Request<E>> {
    /// Number of group elements in a show (`Σ-PS`: 2, `Σ-BBS`: 3).
    const NUM_SHOW_ELEMENTS: usize;

    /// A show of uniform group elements (a valid encoding, no credential behind it).
    fn random_show(rng: &mut StdRng) -> Self::Show;
    /// A show with every group element the identity.
    fn zero_show() -> Self::Show;
    /// One copy of `show` per group element, each with exactly that element shifted by `dg1`.
    /// Length is [`Self::NUM_SHOW_ELEMENTS`].
    fn show_variants(show: &Self::Show, dg1: G1) -> Vec<Self::Show>;
}

impl BaseTest for PS {
    const NUM_SHOW_ELEMENTS: usize = 2;

    fn random_show(rng: &mut StdRng) -> PSPair<E> {
        PSPair {
            s1: G1::rand(rng),
            s2: G1::rand(rng),
        }
    }

    fn zero_show() -> PSPair<E> {
        PSPair {
            s1: G1::zero(),
            s2: G1::zero(),
        }
    }

    fn show_variants(show: &PSPair<E>, dg1: G1) -> Vec<PSPair<E>> {
        vec![
            PSPair {
                s1: show.s1 + dg1,
                s2: show.s2,
            },
            PSPair {
                s1: show.s1,
                s2: show.s2 + dg1,
            },
        ]
    }
}

impl BaseTest for BBS {
    const NUM_SHOW_ELEMENTS: usize = 3;

    fn random_show(rng: &mut StdRng) -> BBSShow<E> {
        BBSShow {
            a_bar: G1::rand(rng),
            b_bar: G1::rand(rng),
            d: G1::rand(rng),
        }
    }

    fn zero_show() -> BBSShow<E> {
        BBSShow {
            a_bar: G1::zero(),
            b_bar: G1::zero(),
            d: G1::zero(),
        }
    }

    fn show_variants(show: &BBSShow<E>, dg1: G1) -> Vec<BBSShow<E>> {
        vec![
            BBSShow {
                a_bar: show.a_bar + dg1,
                ..show.clone()
            },
            BBSShow {
                b_bar: show.b_bar + dg1,
                ..show.clone()
            },
            BBSShow {
                d: show.d + dg1,
                ..show.clone()
            },
        ]
    }
}

/// A uniformly random compact proof with `responses` responses (it verifies for nothing).
pub fn random_proof(responses: usize, rng: &mut StdRng) -> FSProof<Fr> {
    FSProof {
        challenge: Fr::rand(rng),
        responses: (0..responses).map(|_| Fr::rand(rng)).collect(),
    }
}

/// An attestation of random group elements and a random proof of the right shape.
pub fn random_attestation<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    rng: &mut StdRng,
) -> Attestation<Bk<B, T>> {
    Attestation {
        tag: G1::rand(rng),
        show: B::random_show(rng),
        proof: random_proof(1 + B::POSSESSION_VARIABLES, rng),
    }
}

/// A credential request of random group elements with `k` random attestations.
pub fn random_request<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    k: usize,
    rng: &mut StdRng,
) -> CredentialRequest<Bk<B, T>> {
    CredentialRequest {
        id: G1::rand(rng),
        attestations: (0..k).map(|_| random_attestation::<B, T>(rng)).collect(),
        request: G1Request(G1::rand(rng)),
        proof: random_proof(1 + B::ISSUANCE_VARIABLES, rng),
    }
}

/// What a requester gets back from the helper: a credential (unblinded and verified), or the
/// helper's `Fail` or `issued`.
pub enum Outcome<B: Base<E>, T: ProtocolTag<G1> + 'static> {
    /// The pre-credential was unblinded into this credential.
    Credential(Credential<Bk<B, T>>),
    /// `(ssid, Fail)`.
    Fail,
    /// `(ssid, issued)`.
    Issued,
}

impl<B: Base<E>, T: ProtocolTag<G1> + 'static> Outcome<B, T> {
    /// The credential; panics for `Fail` and `issued`.
    pub fn credential(self) -> Credential<Bk<B, T>> {
        match self {
            Self::Credential(cred) => cred,
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
pub struct Member<B: Base<E>, T: ProtocolTag<G1> + 'static> {
    pub user: User<Bk<B, T>>,
    pub cred: Credential<Bk<B, T>>,
}

/// A deployment: the protocol, its helper under `Pol_k`, the checked helper key, and `k` root
/// members with credentials.
pub struct Deployment<B: Base<E>, T: ProtocolTag<G1> + 'static> {
    pub pcreds: Protocol<Bk<B, T>>,
    pub helper: Helper<Bk<B, T>>,
    pub hvk: HelperKey<Bk<B, T>>,
    pub members: Vec<Member<B, T>>,
    pub rng: StdRng,
    /// A counter for fresh sub-session identifiers.
    ssid: u64,
}

impl<B: Base<E>, T: ProtocolTag<G1> + 'static> Deployment<B, T> {
    /// The deployment `label` with threshold `k` and `k` root members.
    pub fn new(label: &[u8], k: usize, seed: u64) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        let pcreds = Protocol::setup(label).expect("setup");
        let helper = pcreds.helper_keygen(Policy::threshold(k).expect("k ≥ 1"), &mut rng);
        let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
        let mut deployment = Self {
            pcreds,
            helper,
            hvk,
            members: Vec::new(),
            rng,
            ssid: 0,
        };
        for _ in 0..k {
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
    pub fn register(&mut self) -> User<Bk<B, T>> {
        self.pcreds
            .register(&self.hvk, &mut self.rng)
            .expect("register")
    }

    /// An ordinary request without attestations, admitted with `d = root`; the credential.
    ///
    /// # Errors
    /// Whatever the protocol returns on the way.
    pub fn admit_root(&mut self, user: &User<Bk<B, T>>) -> Result<Credential<Bk<B, T>>, Error> {
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
        user: &User<Bk<B, T>>,
        message: &CredentialRequest<Bk<B, T>>,
        state: IssuanceState<Bk<B, T>>,
        ssid: &[u8],
        decision: Decision,
    ) -> Result<Outcome<B, T>, Error> {
        let evaluated = self.pcreds.evaluate_request(&self.helper, message, ssid)?;
        Ok(
            match self
                .pcreds
                .respond(&mut self.helper, evaluated, decision, &mut self.rng)?
            {
                Reply::PreCredential(pre) => {
                    Outcome::Credential(self.pcreds.unblind(&self.hvk, user, &pre, state)?)
                }
                Reply::Fail => Outcome::Fail,
                Reply::Issued => Outcome::Issued,
            },
        )
    }

    /// An attestation from member `j` for `user`, through `AttestationRequest` and
    /// `AttestationRequestResponse`.
    pub fn attestation(&mut self, j: usize, user: &User<Bk<B, T>>) -> Attestation<Bk<B, T>> {
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

    /// One attestation from each member for `user`.
    pub fn attestations(&mut self, user: &User<Bk<B, T>>) -> Vec<Attestation<Bk<B, T>>> {
        (0..self.members.len())
            .map(|j| self.attestation(j, user))
            .collect()
    }

    /// A newcomer with a credential obtained through `k` attestations under `Pol_k`.
    pub fn newcomer(&mut self) -> Member<B, T> {
        let user = self.register();
        let attestations = self.attestations(&user);
        let ssid = self.ssid();
        let (message, state) = self
            .pcreds
            .request_credential(&self.hvk, &user, attestations, &ssid, &mut self.rng)
            .expect("request");
        let cred = self
            .answer(&user, &message, state, &ssid, Decision::Policy)
            .expect("issuance")
            .credential();
        Member { user, cred }
    }
}
