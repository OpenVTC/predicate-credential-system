//! Interoperability of `Σ-BBS` under IETF parameters (`pcreds::pairing::ietf`) with
//! `affinidi-bbs` 0.3.3, the BBS crate of the Affinidi / OpenVTC stack (IETF BBS, ciphersuite
//! BLS12-381-SHA-256, curve backend `bls12_381_plus`). The two stacks share no type: everything
//! crosses as bytes, through the `to_ietf_bytes` / `from_ietf_bytes` bridges, and through their
//! public hashing functions for the parameters.
//!
//! The deployments follow "Setting up a deployment" of the module docs: the helper's key is made
//! by THEIR `keygen` first, `pp` is set up after it with `Protocol::setup_with_params`, and the
//! helper is restored from that key. What is shown, per interface of `ietf::Interface`:
//!
//! * (i) a credential issued THROUGH THE PROTOCOL (`request_credential`, `evaluate_request`,
//!   `respond`, `unblind`) is an IETF BBS signature on `(usk, ρ)`. THEIR verifier checks it for
//!   `Blind` (`blind_verify`: `usk` the image of a committed byte string, `ρ` the
//!   `secret_prover_blind`) and for `BlindPseudonym` (`blind_verify_with_nym`: every input a
//!   scalar). Their core `verify` takes byte messages only, and `ρ` from `PrepareIssue` is
//!   uniform, so for `Core` the test compares THEIR `B` for the two scalars (from their own
//!   generator and domain functions) with OURS, the verification equation being the same;
//! * (ii) a signature THEY issued on `(usk, ρ)` is a credential of the protocol:
//!   `Protocol::credential` accepts it, and its holder proves membership and attests for a
//!   newcomer, whom the helper (holding THEIR key) then issues a credential, back to (i);
//! * (iii) a receiver of `pp` accepts the IETF parameters only if it derives the same ones;
//! * (iv) the show is the IETF/TZ show, but the proofs are not IETF proofs (two more responses,
//!   another challenge): neither verifier accepts the other's proofs.
//!
//! Finding pinned by `blind_issuance_with_no_signer_message_crosses_both_ways`: affinidi-bbs
//! 0.3.3 accepts blind signing with ZERO signer messages (their `blind_sign` and `blind_verify`
//! with `messages = []`). The blind and pseudonym drafts have test vectors of that shape, against
//! which affinidi-bbs tests its own `blind_sign` and which the unit tests of the module check. So
//! `Interface::Blind` certifies exactly `(usk, ρ)`, as `Interface::BlindPseudonym` does.
//!
//! Our side is seeded (`StdRng::seed_from_u64`, the seed at each test). Their `commit`,
//! `nym_commit` and `proof_gen` draw their random scalars from the operating system
//! (affinidi-bbs 0.3.3 offers no seeded variant in its public API), so those values differ
//! between runs; every assertion holds for every choice of them.

use affinidi_bbs::{self as abbs, Ciphersuite};
use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::{UniformRand, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use predicate_credential_system::{
    Error,
    hash::bls12_381::G1Hasher,
    kiprf::{DDH, ProtocolTag},
    pcreds::{
        Attestation, Credential, Decision, Helper, HelperKey, IssuanceRecord, MembershipProof,
        Policy, Protocol, Reply, User,
        pairing::{
            BBS, BBSCredential, BBSParams, BBSShow, BBSSigningKey, BBSVerificationKey, Base,
            G1Request, PairingBackend, PairingParams,
            ietf::{self, Interface},
        },
    },
};
use rand::{SeedableRng, rngs::StdRng};

type E = Bls12_381;
type Bbs = BBS<G1Hasher>;
type Tag = DDH<G1Projective, G1Hasher>;
type Bk = PairingBackend<E, Bbs, Tag>;
type Scheme = Protocol<Bk>;

const CS: Ciphersuite = Ciphersuite::Bls12381Sha256;
const LABEL: &[u8] = b"test/bbs-ietf-interop";
const HEADER: &[u8] = b"did:webvh:example:community";
const INTERFACES: [Interface; 3] = [Interface::Core, Interface::Blind, Interface::BlindPseudonym];
/// Byte strings whose IETF scalars serve as `usk` or `ρ` where THEIR API takes bytes.
const USK_BYTES: &[u8] = b"a byte string whose IETF scalar is the member's usk";
const RHO_BYTES: &[u8] = b"a byte string whose IETF scalar is rho";
const NEWCOMER_BYTES: &[u8] = b"a byte string whose IETF scalar is the newcomer's usk";

// ----- the bridge: bytes only ------------------------------------------------------------------

/// A key pair made by THEIR `keygen`, and the same pair as OUR types.
struct Keys {
    sk: abbs::SecretKey,
    pk: abbs::PublicKey,
    our_sk: BBSSigningKey<E>,
    vk: BBSVerificationKey<E>,
}

fn keys(material: &[u8]) -> Keys {
    let sk = abbs::keygen(material, b"interop").expect("their keygen");
    let pk = abbs::sk_to_pk(&sk);
    let our_sk = BBSSigningKey::from_ietf_bytes(&sk.to_bytes()).expect("their SK as ours");
    let vk = BBSVerificationKey::from_ietf_bytes(&pk.to_bytes()).expect("their PK as ours");
    assert_eq!(
        our_sk.verification_key(),
        vk,
        "both stacks derive the same PK"
    );
    assert_eq!(our_sk.to_ietf_bytes()[..], sk.to_bytes()[..]);
    Keys { sk, pk, our_sk, vk }
}

/// THEIR signature `(A, e)` as OUR credential, with the certified `ρ` it does not carry.
fn ours(signature: &abbs::Signature, rho: &Fr) -> BBSCredential<E> {
    BBSCredential::from_ietf_bytes(&signature.to_bytes(), rho).expect("their signature as ours")
}

/// OUR credential as THEIR signature; `ρ` stays behind.
fn theirs(cred: &BBSCredential<E>) -> abbs::Signature {
    abbs::Signature::from_bytes(&cred.to_ietf_bytes().expect("encode")).expect("ours as theirs")
}

fn their_scalar(x: &Fr) -> abbs::Scalar {
    abbs::hash::scalar_from_bytes(&ietf::scalar_to_be_bytes(x)).expect("canonical scalar")
}

fn our_scalar(x: &abbs::Scalar) -> Fr {
    ietf::scalar_from_be_bytes(&abbs::hash::scalar_to_bytes(x)).expect("canonical scalar")
}

fn compressed(point: &G1Projective) -> [u8; 48] {
    let mut out = [0u8; 48];
    point
        .into_affine()
        .serialize_compressed(&mut out[..])
        .expect("encode");
    out
}

/// THEIR `blind_verify` on OUR credential: signer messages, committed messages, and `ρ` as the
/// `secret_prover_blind`.
fn blind_verdict(
    pk: &abbs::PublicKey,
    cred: &BBSCredential<E>,
    signer: &[&[u8]],
    committed: &[&[u8]],
    rho: &Fr,
) -> bool {
    abbs::blind_verify(
        pk,
        &theirs(cred),
        HEADER,
        signer,
        committed,
        their_scalar(rho),
        CS,
    )
    .expect("their blind_verify")
}

/// THEIR `blind_verify_with_nym` on OUR credential, with no signer and no other committed
/// message: `nym_secret = prover_nym + signer_nym_entropy`, and `ρ` of the credential as the
/// `secret_prover_blind`.
fn nym_verdict(
    pk: &abbs::PublicKey,
    cred: &BBSCredential<E>,
    prover_nym: &Fr,
    entropy: &Fr,
) -> bool {
    abbs::blind_verify_with_nym(
        pk,
        &theirs(cred),
        HEADER,
        &[],
        &[],
        their_scalar(prover_nym),
        their_scalar(entropy),
        their_scalar(&cred.rho),
        CS,
    )
    .expect("their blind_verify_with_nym")
}

// ----- deployments under IETF parameters -------------------------------------------------------

/// The parameters of a deployment under the IETF form of `Σ-BBS` for the helper key `vk`: `pp_Σ`
/// from `(interface, vk, header)`, `pp_Tag` from the label as in `Setup`.
fn ietf_params(
    interface: Interface,
    vk: &BBSVerificationKey<E>,
    header: &[u8],
    label: &[u8],
) -> PairingParams<E, Bbs, Tag> {
    PairingParams {
        base: BBSParams::ietf(interface, vk, header).expect("IETF parameters"),
        tag: Tag::setup(label).expect("pp_Tag"),
    }
}

/// A deployment under the IETF parameters of THEIR helper key.
struct Deployment {
    keys: Keys,
    pcreds: Scheme,
    helper: Helper<Bk>,
    hvk: HelperKey<Bk>,
    ssid: u64,
}

impl Deployment {
    /// The helper's key exists FIRST (made by THEIR `keygen`), `pp` is set up after it, and the
    /// helper is built from the key pair with `Protocol::helper_from_key_pair`, which checks
    /// that the secret key belongs to `hvk`.
    fn new(interface: Interface, material: &[u8], k: usize) -> Self {
        let keys = keys(material);
        let pcreds =
            Scheme::setup_with_params(LABEL, ietf_params(interface, &keys.vk, HEADER, LABEL))
                .expect("setup under the IETF parameters");
        let sk = BBSSigningKey::from_ietf_bytes(&keys.sk.to_bytes()).expect("their SK as ours");
        let policy = Policy::threshold(k).expect("k ≥ 1");
        let helper = pcreds
            .helper_from_key_pair(keys.vk.clone(), sk, policy, IssuanceRecord::new())
            .expect("THEIR key as the helper's");
        // the same key through the stored encoding of the helper
        let restored = pcreds
            .restore_helper(
                &helper.to_bytes().expect("encoding"),
                policy,
                IssuanceRecord::new(),
            )
            .expect("restore");
        assert_eq!(restored.key(), helper.key());
        let hvk = pcreds.helper_key(&keys.vk).expect("hvk ∈ V_pp");
        assert_eq!(helper.key(), &hvk);
        Self {
            keys,
            pcreds,
            helper,
            hvk,
            ssid: 0,
        }
    }

    fn ssid(&mut self) -> Vec<u8> {
        self.ssid += 1;
        format!("ssid-{}", self.ssid).into_bytes()
    }

    /// `pp_Σ`.
    fn base(&self) -> &BBSParams<E> {
        &self.pcreds.params().base
    }

    /// The protocol's issuance to `user`: the request, the helper's evaluation and response
    /// under `decision`, and the unblinding (which verifies).
    fn issue(
        &mut self,
        user: &User<Bk>,
        attestations: Vec<Attestation<Bk>>,
        decision: Decision,
        rng: &mut StdRng,
    ) -> Credential<Bk> {
        let ssid = self.ssid();
        let (message, state) = self
            .pcreds
            .request_credential(&self.hvk, user, attestations, &ssid, rng)
            .expect("request");
        let evaluated = self
            .pcreds
            .evaluate_request(&self.helper, &message, &ssid)
            .expect("evaluate");
        let reply = self
            .pcreds
            .respond(&mut self.helper, evaluated, decision, rng)
            .expect("respond");
        let Reply::PreCredential(pre) = reply else {
            panic!("the helper must issue, got {reply:?}");
        };
        self.pcreds
            .unblind(&self.hvk, user, &pre, state)
            .expect("unblind")
    }

    /// What a credential does: its holder proves membership on a message and attests for
    /// `newcomer`, who is then issued a credential under `Pol_1`, which is returned.
    fn use_credential(
        &mut self,
        holder: &User<Bk>,
        cred: &Credential<Bk>,
        newcomer: &User<Bk>,
        rng: &mut StdRng,
    ) -> Credential<Bk> {
        assert!(self.pcreds.verify_credential(&self.hvk, holder, cred));
        let proof = self
            .pcreds
            .prove(&self.hvk, holder, cred, b"hello", rng)
            .expect("prove");
        assert!(self.pcreds.verify(&self.hvk, b"hello", &proof));
        assert!(!self.pcreds.verify(&self.hvk, b"goodbye", &proof));

        let (ssid, contact) = (self.ssid(), b"member@example");
        let request = self
            .pcreds
            .request_attestation(&self.hvk, newcomer, &ssid, contact, rng)
            .expect("attestation request");
        let pending = self
            .pcreds
            .receive_attestation_request(&self.hvk, &request, &ssid, contact)
            .expect("π_id");
        let att = self
            .pcreds
            .attest(&self.hvk, holder, cred, pending, rng)
            .expect("attest");
        assert_eq!(
            self.pcreds
                .check_attestation(&self.hvk, newcomer.id(), &att),
            Ok(())
        );
        let issued = self.issue(newcomer, vec![att], Decision::Policy, rng);
        assert!(self.pcreds.verify_credential(&self.hvk, newcomer, &issued));
        issued
    }
}

// ----- the parameters ----------------------------------------------------------------------------

/// Our hashing primitives, and `BBSParams::ietf` for every interface, are THEIR public
/// functions, byte for byte.
#[test]
fn our_parameters_are_their_parameters() {
    let k = keys(b"hashing: key material of at least thirty-two bytes");
    assert_eq!(Interface::Core.api_id(), CS.api_id());
    assert_eq!(Interface::Blind.api_id(), CS.blind_api_id());
    assert_eq!(Interface::BlindPseudonym.api_id(), CS.pseudonym_api_id());
    let dst = b"a domain separation tag";
    for len in [1, 32, 48, 100, 255 * 32] {
        assert_eq!(
            ietf::expand_message_xmd(b"msg", dst, len).unwrap(),
            abbs::hash::expand_msg_xmd(b"msg", dst, len).unwrap()
        );
    }
    assert_eq!(
        their_scalar(&ietf::hash_to_scalar(b"msg", dst).unwrap()),
        abbs::hash::hash_to_scalar(b"msg", dst, CS).unwrap()
    );
    let point_to_bytes = abbs::generators::point_to_bytes;
    assert_eq!(
        compressed(&ietf::p1().unwrap()),
        point_to_bytes(&abbs::generators::p1_generator())
    );

    for interface in INTERFACES {
        let api_id = interface.api_id();
        for message in [&b""[..], USK_BYTES, RHO_BYTES] {
            assert_eq!(
                their_scalar(&ietf::message_to_scalar(interface, message).unwrap()),
                abbs::hash::messages_to_scalars_with_api_id(&[message], &api_id, CS).unwrap()[0]
            );
        }
        // the generator lists (of the signer, and of the committed part), and the domain
        let lists = core::iter::once(api_id.clone()).chain(interface.blind_generators_api_id());
        for list in lists {
            let ours = ietf::create_generators(4, &list).unwrap();
            let theirs = abbs::generators::create_generators_with_api_id(4, &list, CS).unwrap();
            assert_eq!(
                ours.iter().map(compressed).collect::<Vec<_>>(),
                theirs.iter().map(point_to_bytes).collect::<Vec<_>>()
            );
            let domain = ietf::calculate_domain(&k.vk, &ours[0], &ours[1..], HEADER, &api_id);
            assert_eq!(
                their_scalar(&domain.unwrap()),
                abbs::generators::calculate_domain_with_api_id(
                    &k.pk,
                    &theirs[0],
                    &theirs[1..],
                    HEADER,
                    &api_id,
                    CS
                )
                .unwrap()
            );
        }
        // BBSParams::ietf, rebuilt from THEIR functions: (Q_1, h_u, h_r), and the domain over
        // the two generators in the order of the signed values
        let create = |count, api_id: &[u8]| {
            abbs::generators::create_generators_with_api_id(count, api_id, CS).unwrap()
        };
        let (q1, hu, hr, covered) = match interface.blind_generators_api_id() {
            None => {
                let g = create(3, &api_id);
                (g[0], g[1], g[2], vec![g[1], g[2]])
            }
            Some(blind_api_id) => {
                let (q1, blind) = (create(1, &api_id)[0], create(2, &blind_api_id));
                (q1, blind[1], blind[0], blind)
            }
        };
        let domain = abbs::generators::calculate_domain_with_api_id(
            &k.pk, &q1, &covered, HEADER, &api_id, CS,
        )
        .unwrap();
        let pp = BBSParams::ietf(interface, &k.vk, HEADER).unwrap();
        assert_eq!(
            compressed(&pp.h0),
            point_to_bytes(&(abbs::generators::p1_generator() + q1 * domain))
        );
        assert_eq!(compressed(&pp.hu), point_to_bytes(&hu));
        assert_eq!(compressed(&pp.hr), point_to_bytes(&hr));
    }
}

// ----- the three interfaces ----------------------------------------------------------------------

#[test]
fn core_signatures_are_credentials_and_back() {
    let mut rng = StdRng::seed_from_u64(0x1e7f_2001);
    let mut d = Deployment::new(
        Interface::Core,
        b"core interface: key material of at least 32 bytes",
        1,
    );
    let scalar = |m: &[u8]| ietf::message_to_scalar(Interface::Core, m).expect("scalar");
    let (usk, rho) = (scalar(USK_BYTES), scalar(RHO_BYTES));
    let member = d.pcreds.user(&d.hvk, usk).expect("user");

    // (ii) THEY sign the two messages; with ρ, the signature is OUR credential on usk …
    let signature =
        abbs::sign(&d.keys.sk, &d.keys.pk, HEADER, &[USK_BYTES, RHO_BYTES]).expect("their sign");
    let cred = d
        .pcreds
        .credential(&d.hvk, &member, ours(&signature, &rho))
        .expect("their signature is our credential");
    // … with THIS ρ only, for THIS user only, under THESE parameters only
    let refused = Some(Error::InvalidCredential);
    let other_rho = rho + Fr::from(1u64);
    assert_eq!(
        d.pcreds
            .credential(&d.hvk, &member, ours(&signature, &other_rho))
            .err(),
        refused
    );
    let stranger = d.pcreds.register(&d.hvk, &mut rng).expect("register");
    assert_eq!(
        d.pcreds
            .credential(&d.hvk, &stranger, ours(&signature, &rho))
            .err(),
        refused
    );
    let label_derived = Scheme::setup(LABEL).expect("setup");
    let hvk_there = label_derived.helper_key(&d.keys.vk).expect("hvk");
    let member_there = label_derived.user(&hvk_there, usk).expect("user");
    assert_eq!(
        label_derived
            .credential(&hvk_there, &member_there, ours(&signature, &rho))
            .err(),
        refused
    );
    // … and it does what a credential does; the newcomer is issued one BY THE PROTOCOL
    let newcomer = d.pcreds.register(&d.hvk, &mut rng).expect("register");
    let issued = d.use_credential(&member, &cred, &newcomer, &mut rng);

    // (i) The newcomer's credential is an IETF signature on (usk, ρ). THEIR core verifier
    // takes byte messages only and ρ is uniform, so THEIR B for the two scalars, built from
    // their generators and domain, is compared with OURS (both sides verify
    // e(A, PK·BP_2^e) = e(B, BP_2), and `keys` checked that BP_2 = g̃).
    let (usk_n, rho_n) = (*newcomer.expose_key(), issued.as_inner().rho);
    let g = abbs::generators::create_generators(3, CS).unwrap();
    let domain =
        abbs::generators::calculate_domain(&d.keys.pk, &g[0], &g[1..], HEADER, CS).unwrap();
    let their_b = abbs::generators::p1_generator()
        + g[0] * domain
        + g[1] * their_scalar(&usk_n)
        + g[2] * their_scalar(&rho_n);
    assert_eq!(
        abbs::generators::point_to_bytes(&their_b),
        compressed(&d.base().b(&usk_n, &rho_n))
    );
    assert_eq!(&ours(&theirs(issued.as_inner()), &rho_n), issued.as_inner());

    // OUR BlindIssue, the helper's algorithm in `respond`, is THEIR Sign on a request for two
    // byte-string scalars
    let request = G1Request(d.base().b(&usk, &rho));
    let pre = <Bbs as Base<E>>::blind_issue(d.base(), &d.keys.our_sk, &request, &mut rng)
        .expect("BlindIssue");
    let signed = theirs(&BBSCredential {
        a: pre.a,
        e: pre.e,
        rho,
    });
    let verdict = |header: &[u8], messages: &[&[u8]]| {
        abbs::verify(&d.keys.pk, &signed, header, messages).expect("their verify")
    };
    assert!(verdict(HEADER, &[USK_BYTES, RHO_BYTES]));
    assert!(!verdict(HEADER, &[USK_BYTES, NEWCOMER_BYTES]));
    assert!(!verdict(b"another header", &[USK_BYTES, RHO_BYTES]));
}

#[test]
fn blind_issuance_with_no_signer_message_crosses_both_ways() {
    let mut rng = StdRng::seed_from_u64(0x1e7f_2002);
    let mut d = Deployment::new(
        Interface::Blind,
        b"blind interface: key material of at least 32 bytes",
        1,
    );
    // their committed messages are byte strings: the users' keys are their IETF scalars
    let scalar = |m: &[u8]| ietf::message_to_scalar(Interface::Blind, m).expect("scalar");
    let member = d.pcreds.user(&d.hvk, scalar(USK_BYTES)).expect("user");
    let newcomer = d.pcreds.user(&d.hvk, scalar(NEWCOMER_BYTES)).expect("user");

    // (ii) THEIR prover commits to usk, THEIR signer signs blindly with NO signer message: the
    // signature on (secret_prover_blind, usk) is OUR credential with ρ = secret_prover_blind
    let (commitment, spb) = abbs::commit(&[USK_BYTES], CS).expect("their commit");
    let signature = abbs::blind_sign(&d.keys.sk, &d.keys.pk, &commitment, HEADER, &[], CS)
        .expect("their blind_sign, with zero signer messages");
    assert!(
        abbs::blind_verify(&d.keys.pk, &signature, HEADER, &[], &[USK_BYTES], spb, CS)
            .expect("their blind_verify")
    );
    let rho = our_scalar(&spb);
    let cred = d
        .pcreds
        .credential(&d.hvk, &member, ours(&signature, &rho))
        .expect("their blind signature is our credential");
    // OUR BlindIssue answers THEIR commitment C' (its first 48 bytes) once the public part is
    // multiplied in: C = h_0 · C' = B(usk, spb)
    let c_prime: G1Projective = G1Affine::deserialize_compressed(&commitment[..48])
        .expect("C'")
        .into();
    let request = G1Request(d.base().h0 + c_prime);
    assert_eq!(request.0, d.base().b(&scalar(USK_BYTES), &rho));
    let pre = <Bbs as Base<E>>::blind_issue(d.base(), &d.keys.our_sk, &request, &mut rng)
        .expect("BlindIssue");
    let answered = BBSCredential {
        a: pre.a,
        e: pre.e,
        rho,
    };
    assert!(blind_verdict(
        &d.keys.pk,
        &answered,
        &[],
        &[USK_BYTES],
        &rho
    ));

    // the member attests; the newcomer is issued a credential BY THE PROTOCOL …
    let issued = d.use_credential(&member, &cred, &newcomer, &mut rng);
    // (i) … which THEIR blind verifier accepts, with ρ as the secret_prover_blind
    let (cred_n, rho_n) = (issued.as_inner(), issued.as_inner().rho);
    let pk = &d.keys.pk;
    let signer_message: &[u8] = b"a signer message";
    assert!(blind_verdict(pk, cred_n, &[], &[NEWCOMER_BYTES], &rho_n));
    assert!(!blind_verdict(
        pk,
        cred_n,
        &[],
        &[NEWCOMER_BYTES],
        &(rho_n + Fr::from(1u64))
    ));
    assert!(!blind_verdict(pk, cred_n, &[], &[USK_BYTES], &rho_n));
    assert!(!blind_verdict(
        pk,
        cred_n,
        &[signer_message],
        &[NEWCOMER_BYTES],
        &rho_n
    ));
    // a blind signature is not a core signature: other api_id, other generators and domain
    assert!(!matches!(
        abbs::verify(pk, &theirs(cred_n), HEADER, &[NEWCOMER_BYTES, RHO_BYTES]),
        Ok(true)
    ));

    // a root admission is the same object
    let root_bytes: &[u8] = b"a root user's byte string";
    let root = d.pcreds.user(&d.hvk, scalar(root_bytes)).expect("user");
    let root_cred = d.issue(&root, Vec::new(), Decision::Root, &mut rng);
    let root_rho = root_cred.as_inner().rho;
    assert!(blind_verdict(
        &d.keys.pk,
        root_cred.as_inner(),
        &[],
        &[root_bytes],
        &root_rho
    ));
}

#[test]
fn the_pseudonym_interface_certifies_usk_for_zero_entropy() {
    let mut rng = StdRng::seed_from_u64(0x1e7f_2003);
    let mut d = Deployment::new(
        Interface::BlindPseudonym,
        b"pseudonym interface: key material, 32+ bytes",
        1,
    );
    let zero = Fr::zero();

    // (i) a root admission through the protocol, for a user with a RANDOM key: every input of
    // THEIR nym verifier is a scalar, so it checks the credential as it is
    let root = d.pcreds.register(&d.hvk, &mut rng).expect("register");
    let root_cred = d.issue(&root, Vec::new(), Decision::Root, &mut rng);
    assert!(nym_verdict(
        &d.keys.pk,
        root_cred.as_inner(),
        root.expose_key(),
        &zero
    ));
    let epsilon = Fr::rand(&mut rng);
    assert!(!nym_verdict(
        &d.keys.pk,
        root_cred.as_inner(),
        root.expose_key(),
        &epsilon
    ));

    // (ii) THEIR prover commits to the member's usk, THEIR signer signs with entropy 0
    let member = d.pcreds.register(&d.hvk, &mut rng).expect("register");
    let (commitment, spb) =
        abbs::nym_commit(their_scalar(member.expose_key()), &[], CS).expect("their nym_commit");
    let rho = our_scalar(&spb);
    let sign = |entropy: &Fr| {
        let signature = abbs::blind_sign_with_nym(
            &d.keys.sk,
            &d.keys.pk,
            &commitment,
            their_scalar(entropy),
            HEADER,
            &[],
            CS,
        )
        .expect("their blind_sign_with_nym");
        ours(&signature, &rho)
    };
    let (signed, moved) = (sign(&zero), sign(&epsilon));
    let cred = d
        .pcreds
        .credential(&d.hvk, &member, signed)
        .expect("their nym signature is our credential");
    // with entropy ε ≠ 0 the certified key is usk + ε: not the key behind the member's
    // identifier, but the key of another user, with another identifier
    assert_eq!(
        d.pcreds.credential(&d.hvk, &member, moved.clone()).err(),
        Some(Error::InvalidCredential)
    );
    let shifted = d
        .pcreds
        .user(&d.hvk, *member.expose_key() + epsilon)
        .expect("user");
    assert_ne!(shifted.id(), member.id());
    assert!(d.pcreds.credential(&d.hvk, &shifted, moved).is_ok());

    // the member attests; the newcomer (a random key) is issued a credential by the protocol,
    // which THEIR nym verifier accepts
    let newcomer = d.pcreds.register(&d.hvk, &mut rng).expect("register");
    let issued = d.use_credential(&member, &cred, &newcomer, &mut rng);
    assert!(nym_verdict(
        &d.keys.pk,
        issued.as_inner(),
        newcomer.expose_key(),
        &zero
    ));
    assert!(!nym_verdict(
        &d.keys.pk,
        issued.as_inner(),
        member.expose_key(),
        &zero
    ));
}

// ----- receivers, and what is not covered --------------------------------------------------------

#[test]
fn receivers_accept_the_ietf_parameters_only_if_they_derive_them() {
    let mut rng = StdRng::seed_from_u64(0x1e7f_2004);
    let mut d = Deployment::new(
        Interface::BlindPseudonym,
        b"receiver: helper key material, 32+ bytes...",
        1,
    );
    let received = d.pcreds.public_parameters().clone();

    // a receiver recomputes pp_Σ from (hvk, header) and pp_Tag from the label, and gets the
    // deployment: the same digest, and it verifies the deployment's proofs
    let expected = ietf_params(Interface::BlindPseudonym, &d.keys.vk, HEADER, LABEL);
    let receiver = Scheme::from_public_parameters_with_params(received.clone(), &expected)
        .expect("the parameters the receiver derived");
    assert_eq!(receiver.parameters_digest(), d.pcreds.parameters_digest());
    let member = d.pcreds.register(&d.hvk, &mut rng).expect("register");
    let cred = d.issue(&member, Vec::new(), Decision::Root, &mut rng);
    let proof = d
        .pcreds
        .prove(&d.hvk, &member, &cred, b"m", &mut rng)
        .expect("prove");
    let hvk = receiver.helper_key(&d.keys.vk).expect("hvk ∈ V_pp");
    assert!(receiver.verify(&hvk, b"m", &proof));

    // any other derivation is refused, in particular pp derived for another key than the
    // published hvk (V_pp = G_2 admits every key, so this comparison is what binds them)
    let refused = Some(Error::InvalidPublicParameters(
        "the parameters are not the expected ones",
    ));
    let other_key = keys(b"receiver: another key material of 32+ bytes....");
    for other in [
        ietf_params(
            Interface::BlindPseudonym,
            &d.keys.vk,
            b"another header",
            LABEL,
        ),
        ietf_params(Interface::Blind, &d.keys.vk, HEADER, LABEL),
        ietf_params(Interface::Core, &d.keys.vk, HEADER, LABEL),
        ietf_params(Interface::BlindPseudonym, &other_key.vk, HEADER, LABEL),
        ietf_params(
            Interface::BlindPseudonym,
            &d.keys.vk,
            HEADER,
            b"another label",
        ),
    ] {
        assert_eq!(
            Scheme::from_public_parameters_with_params(received.clone(), &other).err(),
            refused
        );
    }
    // the label-derived check refuses them, as it must
    assert_eq!(
        Scheme::from_public_parameters(received.clone()).err(),
        Some(Error::InvalidPublicParameters(
            "the parameters are not derived from the label"
        ))
    );
    // pp no longer carries x_0 (x_0 = H_id(⟨hvk⟩) is the key's): the expected parameters under
    // another label are the pp of ANOTHER deployment, whose digest, and so every context and
    // oracle, differs; a receiver that expects a label compares it
    let original = Scheme::from_public_parameters_with_params(received.clone(), &expected)
        .expect("the expected parameters");
    let mut relabelled = received;
    relabelled.label = b"another label".to_vec();
    let other = Scheme::from_public_parameters_with_params(relabelled, &expected)
        .expect("another deployment with the expected parameters");
    assert_eq!(other.label(), b"another label");
    assert_ne!(other.parameters_digest(), original.parameters_digest());
}

/// (iv) The show is the IETF/TZ show: THEIR `ProofGen` on a credential produces an `(Ā, B̄, D)`
/// that passes OUR public checks of `Π_Possess`. The proofs are not each other's: theirs carries
/// `(ê, r̂_1, r̂_3, m̂_usk, m̂_ρ, c)`, ours `c` and seven responses, two more, for the third clause
/// `D = B̄^u Ā^v` ("it costs two extra scalars per show", §6.2.2), and the challenges differ.
#[test]
fn the_show_is_the_ietf_show_but_the_proofs_differ() {
    const PH: &[u8] = b"a presentation header";
    let mut rng = StdRng::seed_from_u64(0x1e7f_2005);
    let d = Deployment::new(
        Interface::Core,
        b"presentation: key material of at least 32 bytes",
        1,
    );
    let scalar = |m: &[u8]| ietf::message_to_scalar(Interface::Core, m).expect("scalar");
    let member = d.pcreds.user(&d.hvk, scalar(USK_BYTES)).expect("user");
    let messages = [USK_BYTES, RHO_BYTES];
    let signature = abbs::sign(&d.keys.sk, &d.keys.pk, HEADER, &messages).expect("their sign");
    let cred = d
        .pcreds
        .credential(&d.hvk, &member, ours(&signature, &scalar(RHO_BYTES)))
        .expect("credential");

    // THEIR proof, with both messages undisclosed
    let their_proof = abbs::proof_gen(&d.keys.pk, &signature, HEADER, PH, &messages, &[])
        .expect("their ProofGen");
    assert!(
        abbs::proof_verify(&d.keys.pk, &their_proof, HEADER, PH, &[], &[])
            .expect("their ProofVerify")
    );
    let bytes = their_proof.to_bytes();
    let point = |i: usize| -> G1Projective {
        G1Affine::deserialize_compressed(&bytes[48 * i..48 * (i + 1)])
            .expect("a point of their proof")
            .into()
    };
    let show = BBSShow {
        a_bar: point(0),
        b_bar: point(1),
        d: point(2),
    };
    assert!(<Bbs as Base<E>>::possession_public_check(
        d.base(),
        &d.keys.vk,
        &show
    ));

    // OUR proof on the same credential: (Ā, B̄, D), c and 7 responses; theirs: 6 scalars
    let our_proof = d
        .pcreds
        .prove(&d.hvk, &member, &cred, PH, &mut rng)
        .expect("prove");
    assert_eq!(bytes.len(), 3 * 48 + 6 * 32);
    assert_eq!(our_proof.size(), 3 * 48 + 8 * 32);
    // neither verifier accepts the other's proof
    let our_bytes = our_proof.to_compact_bytes().expect("encode");
    assert_eq!(our_bytes.len(), our_proof.size());
    assert!(!matches!(
        abbs::proof_verify(
            &d.keys.pk,
            &abbs::Proof::from_bytes(&our_bytes),
            HEADER,
            PH,
            &[],
            &[]
        ),
        Ok(true)
    ));
    assert!(MembershipProof::<Bk>::from_compact_bytes(bytes).is_err());
}
