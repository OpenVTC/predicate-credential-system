//! Attacks on the lattice construction (`LatticePCS`, feature `lattice`), each mounted against
//! the real code with ONE real helper key and required to fail with the expected error: the
//! verifier-side tampering of attestations and issuance proofs, replays between the root path
//! and the ordinary path and across deployments and helper keys, duplicate attesters,
//! self-attestation, wrong attestation counts, policy violations, a helper key at the issuance
//! cap; and byte fuzzing of every decoder. The ports of the harness's relation-level checks (the
//! `φ` forgery, non-canonical tags, false witnesses, the exact norm bound) are unit tests of
//! `pcs::lattice::relations`, because they build statements directly.
//!
//! The flows share one fixture (three root members, a recipient with two attestations and an
//! issuance proof for `k = 2`, about 35 s) and are `#[ignore]`d; run them in release, one at a
//! time:
//! `RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_adversarial -- --ignored`.
//! The fuzzing tests run in every `cargo test`.
#![cfg(feature = "lattice")]

use std::sync::OnceLock;

use predicate_credential_system::{
    Error, LatticePCS,
    cred::{VSIS, vsis::VSISVerificationKey},
    kiprf::lwr::LWRTag,
    lattice::{BinaryPoly, Q_MAX, Rq},
    pcs::{
        AllowList, HelperSecretKey, Predicate, PredicateCredentialSystem, SetupParams,
        lattice::{
            Attestation, Credential, IssuanceProof, IssuanceState, Proof, RootRequest,
            UserSecretKey,
        },
    },
    serialization::WireFormat,
};
use rand::{RngCore, SeedableRng, rngs::StdRng};

type Pcs = LatticePCS<AllowList<BinaryPoly>>;

const LABEL: &[u8] = b"lattice-adversarial";

struct Member {
    id: LWRTag,
    usk: UserSecretKey,
    cred: Credential,
    f: Predicate,
}

/// One deployment, one helper key, three root members (two under `f_root`, one under
/// `f_other`, which the policy does not count), and a recipient with two attestations and an
/// issuance proof for `f = f_2`.
struct Fixture {
    pcs: Pcs,
    hvk: VSISVerificationKey,
    hsk: HelperSecretKey<VSIS>,
    f_root: Predicate,
    f: Predicate,
    members: Vec<Member>,
    root_request: RootRequest,
    recipient: (LWRTag, UserSecretKey),
    attestations: Vec<Attestation>,
    proof: IssuanceProof,
    state_bytes: Vec<u8>,
}

fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let mut rng = StdRng::seed_from_u64(0xad7e_0001);
        let f_root = Predicate::root(b"founders".to_vec());
        let f_other = Predicate::root(b"others".to_vec());
        let f = Predicate::new(2, b"members".to_vec());
        let open = LatticePCS::setup(SetupParams::new(LABEL.to_vec())).unwrap();
        let policy = open.allow_list([&f_root, &f]);
        let pcs =
            LatticePCS::from_public_parameters(open.public_parameters().clone(), policy).unwrap();
        let (hvk, hsk) = pcs.helper_keygen(&mut rng);
        let mut members = Vec::new();
        let mut root_request = None;
        for f_j in [&f_root, &f_root, &f_other] {
            let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
            let (request, state) = pcs.root_request(&hvk, f_j, &id, &usk, &mut rng).unwrap();
            let pre = pcs
                .issue_root(&hvk, &hsk, f_j, &id, &request, &mut rng)
                .unwrap();
            let cred = pcs.unblind(&hvk, &usk, f_j, &pre, &state).unwrap();
            root_request.get_or_insert(request);
            members.push(Member {
                id,
                usk,
                cred,
                f: f_j.clone(),
            });
        }
        let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
        let attestations: Vec<Attestation> = members[..2]
            .iter()
            .map(|m| {
                pcs.attest(&hvk, &m.usk, &m.f, &m.cred, &id, &mut rng)
                    .unwrap()
            })
            .collect();
        let (proof, state) = pcs
            .prove(&hvk, &f, &id, &usk, &attestations, &mut rng)
            .unwrap();
        Fixture {
            pcs,
            hvk,
            hsk,
            f_root,
            f,
            members,
            root_request: root_request.unwrap(),
            recipient: (id, usk),
            attestations,
            proof,
            state_bytes: state.to_bytes().unwrap().to_vec(),
        }
    })
}

fn bump(tag: &LWRTag, row: usize) -> LWRTag {
    let mut entries = *tag.entries();
    entries[row] = entries[row].wrapping_add(1);
    LWRTag::from_entries(entries)
}

/// Verifier-side tampering of an attestation (H/flow.rs:436-488): every change of the tag, of
/// `φ_j`, of the recipient, of the helper key, of the deployment, or of the proof bytes is
/// refused.
#[test]
#[ignore = "heavy: shared fixture and six R_att verifications (run in release)"]
fn tampered_attestations_are_refused() {
    let fx = fixture();
    let (pcs, hvk) = (&fx.pcs, &fx.hvk);
    let id = &fx.recipient.0;
    let att = &fx.attestations[0];
    assert_eq!(pcs.check_attestation(hvk, id, att), Ok(()));
    // the tag changed in one row
    let mut a = att.clone();
    a.tag = bump(&a.tag, 3);
    assert_eq!(pcs.check_attestation(hvk, id, &a), Err(Error::InvalidProof));
    // the disclosed φ changed in one bit (still binary)
    let mut a = att.clone();
    let mut phi = *a.phi.as_bytes();
    phi[5] ^= 1;
    a.phi = BinaryPoly::from_bytes(phi);
    assert_eq!(pcs.check_attestation(hvk, id, &a), Err(Error::InvalidProof));
    // presented for another recipient
    assert_eq!(
        pcs.check_attestation(hvk, &fx.members[0].id, att),
        Err(Error::InvalidProof)
    );
    // under another helper key of the same deployment
    let mut rng = StdRng::seed_from_u64(0xad7e_0002);
    let (other_hvk, _) = pcs.helper_keygen(&mut rng);
    assert_eq!(
        pcs.check_attestation(&other_hvk, id, att),
        Err(Error::InvalidProof)
    );
    // in another deployment, under the same helper key
    let elsewhere = LatticePCS::setup(SetupParams::new(b"lattice-adversarial/2".to_vec())).unwrap();
    assert_eq!(
        elsewhere.check_attestation(hvk, id, att),
        Err(Error::InvalidProof)
    );
    // one proof bit flipped, the proof truncated by one byte, a byte appended
    let mut bytes = att.proof.as_bytes().to_vec();
    let middle = bytes.len() / 2;
    bytes[middle] ^= 1;
    let a = Attestation {
        proof: Proof::from_bytes(bytes).unwrap(),
        ..att.clone()
    };
    assert_eq!(pcs.check_attestation(hvk, id, &a), Err(Error::InvalidProof));
    let mut bytes = att.proof.as_bytes().to_vec();
    bytes.pop();
    let a = Attestation {
        proof: Proof::from_bytes(bytes).unwrap(),
        ..att.clone()
    };
    assert_eq!(pcs.check_attestation(hvk, id, &a), Err(Error::InvalidProof));
    let mut bytes = att.proof.as_bytes().to_vec();
    bytes.push(0);
    let a = Attestation {
        proof: Proof::from_bytes(bytes).unwrap(),
        ..att.clone()
    };
    assert_eq!(pcs.check_attestation(hvk, id, &a), Err(Error::InvalidProof));
    // the proof of another attestation for the same recipient
    let a = Attestation {
        proof: fx.attestations[1].proof.clone(),
        ..att.clone()
    };
    assert_eq!(pcs.check_attestation(hvk, id, &a), Err(Error::InvalidProof));
}

/// Verifier-side and flow-level checks of `VerifyProof` (H/flow.rs:536-586): counts, duplicate
/// attesters, self-exclusion, a changed `C` or `T_0`, another predicate in `ctx_0`, a tampered
/// attestation inside `π`, and replays between the root path and the ordinary path.
#[test]
#[ignore = "heavy: shared fixture and several R_issue / R_att verifications (run in release)"]
fn tampered_issuance_proofs_are_refused() {
    let fx = fixture();
    let (pcs, hvk, f) = (&fx.pcs, &fx.hvk, &fx.f);
    let id = &fx.recipient.0;
    let proof = &fx.proof;
    assert_eq!(pcs.check_proof(hvk, f, id, proof), Ok(()));
    // k ± 1 attestations, and the threshold of another predicate
    let mut fewer = proof.clone();
    fewer.attestations.pop();
    assert_eq!(
        pcs.check_proof(hvk, f, id, &fewer),
        Err(Error::WrongAttestationCount {
            expected: 2,
            actual: 1
        })
    );
    let f3 = Predicate::new(3, b"members".to_vec());
    assert_eq!(
        pcs.check_proof(hvk, &f3, id, proof),
        Err(Error::WrongAttestationCount {
            expected: 3,
            actual: 2
        })
    );
    assert_eq!(
        pcs.check_proof(hvk, &fx.f_root, id, proof),
        Err(Error::ZeroThreshold)
    );
    // the same attester twice
    let mut twice = proof.clone();
    twice.attestations[1] = twice.attestations[0].clone();
    assert_eq!(
        pcs.check_proof(hvk, f, id, &twice),
        Err(Error::DuplicateAttester)
    );
    // the self-exclusion tag among the attester tags
    let mut selfish = proof.clone();
    selfish.t0 = selfish.attestations[1].tag.clone();
    assert_eq!(
        pcs.check_proof(hvk, f, id, &selfish),
        Err(Error::SelfAttestation)
    );
    // C changed, T_0 changed, another predicate with the same threshold in ctx_0
    let mut c = proof.c.coeffs().to_vec();
    c[0] = (c[0] + 1) % predicate_credential_system::lattice::Q;
    let changed_c = IssuanceProof {
        c: Rq::from_coeffs(&c).unwrap(),
        ..proof.clone()
    };
    assert_eq!(
        pcs.check_proof(hvk, f, id, &changed_c),
        Err(Error::InvalidProof)
    );
    let changed_t0 = IssuanceProof {
        t0: bump(&proof.t0, 0),
        ..proof.clone()
    };
    assert_eq!(
        pcs.check_proof(hvk, f, id, &changed_t0),
        Err(Error::InvalidProof)
    );
    let f_b = Predicate::new(2, b"membersb".to_vec());
    assert_eq!(
        pcs.check_proof(hvk, &f_b, id, proof),
        Err(Error::InvalidProof)
    );
    // one attestation proof bit flipped inside π: the attestations are part of ctx_0, so π_0
    // (verified first) already fails
    let mut tampered = proof.clone();
    let mut bytes = tampered.attestations[1].proof.as_bytes().to_vec();
    let at = bytes.len() / 3;
    bytes[at] ^= 4;
    tampered.attestations[1].proof = Proof::from_bytes(bytes).unwrap();
    assert_eq!(
        pcs.check_proof(hvk, f, id, &tampered),
        Err(Error::InvalidProof)
    );
    // the issuance proof replayed as a root request, and a root request as an issuance proof
    let replayed = RootRequest {
        c: proof.c.clone(),
        t0: proof.t0.clone(),
        proof: proof.proof.clone(),
    };
    assert_eq!(
        pcs.check_root_request(hvk, &fx.f_root, id, &replayed),
        Err(Error::InvalidProof)
    );
    let root = &fx.root_request;
    let member = &fx.members[0].id;
    let as_issuance = IssuanceProof {
        attestations: proof.attestations.clone(),
        c: root.c.clone(),
        t0: root.t0.clone(),
        proof: root.proof.clone(),
    };
    assert_eq!(
        pcs.check_proof(hvk, f, member, &as_issuance),
        Err(Error::InvalidProof)
    );
    assert_eq!(
        pcs.check_root_request(hvk, &fx.f_root, member, root),
        Ok(())
    );
    // the root request under another root predicate, and for another identifier
    assert_eq!(
        pcs.check_root_request(hvk, &Predicate::root(b"others".to_vec()), member, root),
        Err(Error::InvalidProof)
    );
    assert_eq!(
        pcs.check_root_request(hvk, &fx.f_root, id, root),
        Err(Error::InvalidProof)
    );
    // proof-gated issuance: nothing is issued for a refused proof (a copy of the key, so that
    // its counter is this test's alone)
    let mut rng = StdRng::seed_from_u64(0xad7e_0003);
    let hsk = HelperSecretKey::<VSIS>::from_bytes(&fx.hsk.to_bytes().unwrap()).unwrap();
    let before = hsk.signing_key().issued();
    assert_eq!(
        pcs.issue(hvk, &hsk, f, id, &changed_c, &mut rng).err(),
        Some(Error::InvalidProof)
    );
    assert_eq!(hsk.signing_key().issued(), before);
}

/// The honest `Prove` refuses what the verifier would refuse: an attester whose credential the
/// policy does not count (`f_other`), a self-attestation (the recipient, once credentialed,
/// endorsing itself), the same attester twice, and an attestation for another recipient.
#[test]
#[ignore = "heavy: shared fixture, an issuance and two attestations (run in release)"]
fn the_honest_prover_refuses_what_the_verifier_refuses() {
    let fx = fixture();
    let (pcs, hvk, f) = (&fx.pcs, &fx.hvk, &fx.f);
    let (id, usk) = (&fx.recipient.0, &fx.recipient.1);
    let mut rng = StdRng::seed_from_u64(0xad7e_0004);
    // an attester under f_other: the policy rejects it (before any proof is checked)
    let other = &fx.members[2];
    let att_other = pcs
        .attest(hvk, &other.usk, &other.f, &other.cred, id, &mut rng)
        .unwrap();
    assert!(pcs.verify_attestation(hvk, id, &att_other));
    let with_other = [fx.attestations[0].clone(), att_other.clone()];
    assert_eq!(
        pcs.prove(hvk, f, id, usk, &with_other, &mut rng).err(),
        Some(Error::PolicyRejected)
    );
    let mut forged = fx.proof.clone();
    forged.attestations = with_other.to_vec();
    assert_eq!(
        pcs.check_proof(hvk, f, id, &forged),
        Err(Error::PolicyRejected)
    );
    // ... while a helper with P ≡ 1 counts it
    let open: LatticePCS =
        LatticePCS::from_public_parameters(pcs.public_parameters().clone(), Default::default())
            .unwrap();
    assert!(open.prove(hvk, f, id, usk, &with_other, &mut rng).is_ok());
    // the same attester twice
    let twice = [fx.attestations[0].clone(), fx.attestations[0].clone()];
    assert_eq!(
        pcs.prove(hvk, f, id, usk, &twice, &mut rng).err(),
        Some(Error::DuplicateAttester)
    );
    // an attestation for another recipient
    let foreign = pcs
        .attest(
            hvk,
            &fx.members[1].usk,
            &fx.members[1].f,
            &fx.members[1].cred,
            &fx.members[0].id,
            &mut rng,
        )
        .unwrap();
    let mixed = [fx.attestations[0].clone(), foreign];
    assert_eq!(
        pcs.prove(hvk, f, id, usk, &mixed, &mut rng).err(),
        Some(Error::InvalidAttestation)
    );
    // self-attestation: the recipient gets its credential and endorses itself
    let state = IssuanceState::from_bytes(&fx.state_bytes).unwrap();
    let pre = pcs.issue(hvk, &fx.hsk, f, id, &fx.proof, &mut rng).unwrap();
    let cred = pcs.unblind(hvk, usk, f, &pre, &state).unwrap();
    let selfie = pcs.attest(hvk, usk, f, &cred, id, &mut rng).unwrap();
    assert!(pcs.verify_attestation(hvk, id, &selfie));
    let with_self = [fx.attestations[0].clone(), selfie];
    assert_eq!(
        pcs.prove(hvk, f, id, usk, &with_self, &mut rng).err(),
        Some(Error::SelfAttestation)
    );
}

/// A helper key at the issuance cap issues nothing, after the proof check (con:220-221).
#[test]
#[ignore = "heavy: shared fixture and one VerifyProof (run in release)"]
fn a_helper_key_at_the_cap_issues_nothing() {
    let fx = fixture();
    let mut bytes = fx.hsk.to_bytes().unwrap().to_vec();
    let at = predicate_credential_system::cred::vsis::VSISSigningKey::BYTES - 8;
    bytes[at..at + 8].copy_from_slice(&(Q_MAX - 1).to_le_bytes());
    let hsk = HelperSecretKey::<VSIS>::from_bytes(&bytes).unwrap();
    let mut rng = StdRng::seed_from_u64(0xad7e_0005);
    let (pcs, hvk, f) = (&fx.pcs, &fx.hvk, &fx.f);
    let id = &fx.recipient.0;
    assert!(pcs.issue(hvk, &hsk, f, id, &fx.proof, &mut rng).is_ok());
    assert_eq!(hsk.signing_key().remaining(), 0);
    assert_eq!(
        pcs.issue(hvk, &hsk, f, id, &fx.proof, &mut rng).err(),
        Some(Error::IssuanceCapReached)
    );
    let member = &fx.members[0].id;
    assert_eq!(
        pcs.issue_root(hvk, &hsk, &fx.f_root, member, &fx.root_request, &mut rng)
            .err(),
        Some(Error::IssuanceCapReached)
    );
}

// ---------------------------------------------------------------------------------------------
// Decoders: no panics on arbitrary bytes, and strictness
// ---------------------------------------------------------------------------------------------

/// Every decoder of the lattice objects, fed random bytes of many lengths (and random bytes
/// behind a plausible length prefix), returns an error or a value, and never panics. Values that
/// decode re-encode to the same bytes (canonicity).
#[test]
fn decoders_never_panic_on_arbitrary_bytes() {
    let mut rng = StdRng::seed_from_u64(0xad7e_0010);
    let f = Predicate::new(2, b"f".to_vec());
    let lengths = [
        0usize, 1, 3, 4, 5, 255, 256, 335, 336, 337, 467, 468, 469, 2559, 2560, 2900, 5887, 5888,
        5889, 6000,
    ];
    for round in 0..16u32 {
        for &len in &lengths {
            let mut bytes = vec![0u8; len];
            rng.fill_bytes(&mut bytes);
            // also with a small, plausible proof length where a decoder would read one
            for at in [0usize, 464, 2896] {
                if round % 2 == 1 && bytes.len() >= at + 4 {
                    let small = rng.next_u32() % 64;
                    bytes[at..at + 4].copy_from_slice(&small.to_le_bytes());
                }
            }
            if let Ok(v) = Attestation::from_compact_bytes(&bytes) {
                assert_eq!(v.to_compact_bytes().unwrap(), bytes);
            }
            if let Ok(v) = IssuanceProof::from_compact_bytes(&bytes, &f) {
                assert_eq!(v.to_compact_bytes().unwrap(), bytes);
            }
            if let Ok(v) = RootRequest::from_compact_bytes(&bytes) {
                assert_eq!(v.to_compact_bytes().unwrap(), bytes);
            }
            let _ = <IssuanceProof as WireFormat>::from_bytes(&bytes);
            let _ = <Proof as WireFormat>::from_bytes(&bytes);
            if let Ok(v) = <Credential as WireFormat>::from_bytes(&bytes) {
                assert_eq!(&*v.to_bytes().unwrap(), &bytes);
            }
            let _ = IssuanceState::from_bytes(&bytes);
            let _ = <UserSecretKey as WireFormat>::from_bytes(&bytes);
            let _ = <LWRTag as WireFormat>::from_bytes(&bytes);
            let _ = <VSISVerificationKey as WireFormat>::from_bytes(&bytes);
            let _ = <HelperSecretKey<VSIS> as WireFormat>::from_bytes(&bytes);
        }
    }
}

/// A non-canonical tag `T + p z` (bb:232) cannot be represented: every 336-byte string is the
/// encoding of a tag with entries below `p = 2^16`, and `ValidTag` holds for it; a φ with a
/// coefficient outside {0, 1} cannot be represented either (every 128-byte string is binary).
#[test]
fn non_canonical_tags_and_non_binary_phi_are_unrepresentable() {
    let mut rng = StdRng::seed_from_u64(0xad7e_0011);
    for _ in 0..64 {
        let mut bytes = [0u8; LWRTag::BYTES];
        rng.fill_bytes(&mut bytes);
        let tag = LWRTag::from_bytes(&bytes).unwrap();
        assert!(predicate_credential_system::kiprf::lwr::LWR.valid_tag(&tag));
        assert_eq!(tag.to_bytes(), bytes);
        let mut phi = [0u8; BinaryPoly::BYTES];
        rng.fill_bytes(&mut phi);
        let phi = BinaryPoly::from_bytes(phi);
        assert!((0..1024).all(|i| phi.coefficient(i) <= 1));
    }
}
