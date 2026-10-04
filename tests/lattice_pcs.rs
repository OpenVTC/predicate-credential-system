//! The lattice construction (`LatticePCS`, feature `lattice`) through its public API, with ONE
//! real helper key (an NTRU trapdoor) and real Jali proofs: Def. "Correctness" with root
//! issuance and chaining, proof-gated issuance, the sizes of the README row, and the checks that
//! need no proof.
//!
//! Every attestation is a Jali proof for `R_att` of about 83 KB that takes seconds and about
//! 0.5 GiB to prove or verify, so the flows are heavy:
//!
//! * `quick_end_to_end_k1` runs in release builds (it is ignored when debug assertions are on):
//!   `cargo test --release --features lattice --test lattice_pcs`, about 30 s;
//! * the others are `#[ignore]`d; run them one at a time, in release:
//!   `RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_pcs -- --ignored --nocapture`.
//!
//! The light tests run in every `cargo test`.
#![cfg(feature = "lattice")]

use std::time::Instant;

use predicate_credential_system::{
    Error, LatticePCS,
    cred::{
        CredentialBase, VSIS,
        vsis::{VSISCredential, VSISHiddenMessage, VSISIssuanceState, VSISSigningKey},
    },
    kiprf::{
        KIPRF,
        lwr::{LWR, LWRTag},
    },
    lattice::{
        BinaryPoly, Q_MAX, Rq, Ternary,
        sets::{ATT_PROOF_MAX_BYTES, ISSUE_PROOF_MAX_BYTES, ParameterSets},
    },
    pcs::{
        AllowList, AttributePolicy, HelperSecretKey, Predicate, PredicateCredentialSystem,
        SetupParams,
        lattice::{
            Attestation, Credential, IssuanceProof, IssuanceState, Proof, RootRequest,
            UserSecretKey,
        },
    },
    serialization::WireFormat,
};
use rand::{SeedableRng, rngs::StdRng};

type Pcs = LatticePCS<AllowList<BinaryPoly>>;

/// A deployment whose helper counts attesters with root credentials and with credentials of the
/// threshold predicate `f`, as `docs/operating-a-helper.md` asks (no `P ≡ 1`).
fn deployment(label: &[u8], f: &Predicate, f_root: &Predicate) -> Pcs {
    let open = LatticePCS::setup(SetupParams::new(label.to_vec())).unwrap();
    let policy = open.allow_list([f_root, f]);
    LatticePCS::from_public_parameters(open.public_parameters().clone(), policy).unwrap()
}

/// A user with a root credential issued through the root path.
struct Member {
    id: LWRTag,
    usk: UserSecretKey,
    cred: Credential,
    f: Predicate,
}

fn root_member(
    pcs: &Pcs,
    hvk: &<Pcs as PredicateCredentialSystem>::HelperVerificationKey,
    hsk: &HelperSecretKey<VSIS>,
    f_root: &Predicate,
    rng: &mut StdRng,
) -> (Member, RootRequest) {
    let (id, usk) = pcs.user_keygen(rng).unwrap();
    let (request, state) = pcs.root_request(hvk, f_root, &id, &usk, rng).unwrap();
    assert!(pcs.verify_root_request(hvk, f_root, &id, &request));
    let pre = pcs
        .issue_root(hvk, hsk, f_root, &id, &request, rng)
        .unwrap();
    let cred = pcs.unblind(hvk, &usk, f_root, &pre, &state).unwrap();
    assert!(pcs.verify_cred(hvk, &usk, f_root, &cred));
    (
        Member {
            id,
            usk,
            cred,
            f: f_root.clone(),
        },
        request,
    )
}

fn secs(t: Instant) -> f64 {
    t.elapsed().as_secs_f64()
}

/// Def. "Correctness" at `k = 1` with one helper key: root issuance, an attestation, `Prove`,
/// `VerifyProof`, `Issue`, `Unblind`, `VerifyCred`, and the wire round trips of every object.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: Jali proofs; runs in release builds (cargo test --release)"
)]
fn quick_end_to_end_k1() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0001);
    let f_root = Predicate::root(b"founders".to_vec());
    let f = Predicate::new(1, b"members".to_vec());
    let pcs = deployment(b"lattice-pcs/quick", &f, &f_root);
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);

    let t = Instant::now();
    let (founder, request) = root_member(&pcs, &hvk, &hsk, &f_root, &mut rng);
    let root_s = secs(t);
    assert_eq!(hsk.signing_key().issued(), 1);

    let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
    let t = Instant::now();
    let att = pcs
        .attest(&hvk, &founder.usk, &founder.f, &founder.cred, &id, &mut rng)
        .unwrap();
    let attest_s = secs(t);
    let t = Instant::now();
    assert_eq!(pcs.check_attestation(&hvk, &id, &att), Ok(()));
    let verify_att_s = secs(t);
    // the attestation is bound to its recipient
    assert_eq!(
        pcs.check_attestation(&hvk, &founder.id, &att),
        Err(Error::InvalidProof)
    );

    let attestations = [att];
    let t = Instant::now();
    let (proof, state) = pcs
        .prove(&hvk, &f, &id, &usk, &attestations, &mut rng)
        .unwrap();
    let prove_s = secs(t);
    let t = Instant::now();
    assert_eq!(pcs.check_proof(&hvk, &f, &id, &proof), Ok(()));
    let verify_s = secs(t);
    let pre = pcs.issue(&hvk, &hsk, &f, &id, &proof, &mut rng).unwrap();
    let cred = pcs.unblind(&hvk, &usk, &f, &pre, &state).unwrap();
    assert!(pcs.verify_cred(&hvk, &usk, &f, &cred));
    assert!(!pcs.verify_cred(&hvk, &usk, &f_root, &cred));
    assert!(!pcs.verify_cred(&hvk, &founder.usk, &f, &cred));
    assert_eq!(hsk.signing_key().issued(), 2);

    // wire round trips: compact and canonical encodings of the public objects, the secrets'
    // own encodings
    let att = &attestations[0];
    assert_eq!(
        Attestation::from_compact_bytes(&att.to_compact_bytes().unwrap()).unwrap(),
        *att
    );
    assert_eq!(
        IssuanceProof::from_compact_bytes(&proof.to_compact_bytes().unwrap(), &f).unwrap(),
        proof
    );
    assert_eq!(
        IssuanceProof::from_bytes(&WireFormat::to_bytes(&proof).unwrap()).unwrap(),
        proof
    );
    assert_eq!(
        RootRequest::from_compact_bytes(&request.to_compact_bytes().unwrap()).unwrap(),
        request
    );
    let cred_bytes = cred.to_bytes().unwrap();
    assert_eq!(cred_bytes.len(), Credential::BYTES);
    assert_eq!(
        <Credential as WireFormat>::from_bytes(&cred_bytes).unwrap(),
        cred
    );
    assert_eq!(
        <VSISCredential as WireFormat>::from_bytes(&WireFormat::to_bytes(&pre).unwrap()).unwrap(),
        pre
    );
    // the fixed overheads of the README row
    assert_eq!(att.compact_size(), 468 + att.proof.len());
    assert_eq!(
        proof.compact_size(),
        att.compact_size() + 2900 + proof.proof.len()
    );
    assert_eq!(request.compact_size(), 2900 + request.proof.len());
    println!(
        "k = 1 [release, one thread]: root request + issue_root {root_s:.2} s; attest {attest_s:.2} s; \
         verify_att {verify_att_s:.2} s; prove {prove_s:.2} s; verify_proof {verify_s:.2} s; \
         |π_att| = {} B, |π_0| = {} B, |π_root| = {} B",
        att.proof.len(),
        proof.proof.len(),
        request.proof.len()
    );
}

/// The main flow of the validation harness (H/flow.rs:299-597, positive path) at `k = 3`,
/// with ONE helper key: root issuance for `U1..U3` under `f_root` and `U4` under `f_other`, three
/// attestations for the recipient `U5`, each verified, `Prove`, `VerifyProof`, `Issue`,
/// `Unblind`, `VerifyCred`, and composition: `U5`'s new credential attests for `U1`, and counts
/// under the policy as an attester of an `f_3` credential.
#[test]
#[ignore = "heavy: 4 root issuances, 5 attestations, a k = 3 issuance (about 90 s in release)"]
fn flow_k3_with_chaining() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0004);
    let f_root = Predicate::root(b"f_root".to_vec());
    let f_other = Predicate::root(b"f_other".to_vec());
    let f = Predicate::new(3, b"f_3".to_vec());
    let pcs = deployment(b"lattice-pcs/flow", &f, &f_root);
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);
    let t_all = Instant::now();
    // 1. root issuance (rem:chain): U1..U3 under f_root, U4 under f_other
    let mut members = Vec::new();
    for f_j in [&f_root, &f_root, &f_root, &f_other] {
        members.push(root_member(&pcs, &hvk, &hsk, f_j, &mut rng).0);
    }
    assert_eq!(hsk.signing_key().issued(), 4);
    // 2. attestations U1..U3 → U5, each verified
    let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
    let attestations: Vec<Attestation> = members[..3]
        .iter()
        .map(|m| {
            let att = pcs
                .attest(&hvk, &m.usk, &m.f, &m.cred, &id, &mut rng)
                .unwrap();
            assert_eq!(pcs.check_attestation(&hvk, &id, &att), Ok(()));
            att
        })
        .collect();
    // tags of distinct attesters are distinct, and none is the recipient's own
    let s = pcs.tag_point(&id);
    let own = LWR.eval(usk.expose_ternary(), &s).unwrap();
    for (i, a) in attestations.iter().enumerate() {
        assert_ne!(a.tag, own);
        assert!(attestations[i + 1..].iter().all(|b| b.tag != a.tag));
        assert_eq!(a.phi, pcs.enc_pred(&f_root));
    }
    // 3. Prove, VerifyProof, Issue, Unblind, VerifyCred
    let (proof, state) = pcs
        .prove(&hvk, &f, &id, &usk, &attestations, &mut rng)
        .unwrap();
    assert!(pcs.verify_proof(&hvk, &f, &id, &proof));
    assert_eq!(proof.t0, own);
    let pre = pcs.issue(&hvk, &hsk, &f, &id, &proof, &mut rng).unwrap();
    let cred = pcs.unblind(&hvk, &usk, &f, &pre, &state).unwrap();
    assert!(pcs.verify_cred(&hvk, &usk, &f, &cred));
    assert_eq!(hsk.signing_key().issued(), 5);
    // 4. composition: the new credential attests for U1, and its label is admitted
    let u1 = &members[0];
    let chained = pcs.attest(&hvk, &usk, &f, &cred, &u1.id, &mut rng).unwrap();
    assert_eq!(pcs.check_attestation(&hvk, &u1.id, &chained), Ok(()));
    assert_eq!(chained.phi, pcs.enc_pred(&f));
    assert!(pcs.policy().accepts(&[chained.phi]));
    assert!(!pcs.policy().accepts(&[pcs.enc_pred(&f_other)]));
    println!(
        "k = 3 flow with chaining: {:.1} s [release, one thread]",
        secs(t_all)
    );
}

/// The checks that need no proof: the root path's predicate, `ZeroThreshold`, the attestation
/// count, the identifier, the helper key's deployment, and `Unblind` / `VerifyCred` on a
/// pre-credential that the helper's base issues directly (no Jali involved).
#[test]
fn checks_that_need_no_proof() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0002);
    let f_root = Predicate::root(b"founders".to_vec());
    let f = Predicate::new(1, b"members".to_vec());
    let pcs = deployment(b"lattice-pcs/light", &f, &f_root);
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);
    let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
    let (other_id, _) = pcs.user_keygen(&mut rng).unwrap();
    assert_eq!(
        pcs.root_request(&hvk, &f, &id, &usk, &mut rng).err(),
        Some(Error::NotARootPredicate)
    );
    assert_eq!(
        pcs.root_request(&hvk, &f_root, &other_id, &usk, &mut rng)
            .err(),
        Some(Error::IdentifierMismatch)
    );
    assert_eq!(
        pcs.prove(&hvk, &f_root, &id, &usk, &[], &mut rng).err(),
        Some(Error::ZeroThreshold)
    );
    assert_eq!(
        pcs.prove(&hvk, &f, &id, &usk, &[], &mut rng).err(),
        Some(Error::WrongAttestationCount {
            expected: 1,
            actual: 0
        })
    );

    // Unblind and VerifyCred on a pre-credential of the base (a C the user computed)
    let x0 = [Ternary::sample(&mut rng), Ternary::sample(&mut rng)];
    let phi = pcs.enc_pred(&f);
    let sigma = &pcs.public_parameters().pp_sigma;
    let m_hid = VSISHiddenMessage::new(usk.expose_ternary().clone(), x0.clone());
    let c = VSIS::issuance_encoding(
        sigma,
        &hvk,
        &m_hid,
        &phi,
        &VSISIssuanceState::new(x0.clone()),
    )
    .unwrap();
    let pre = VSIS::blind_issue(sigma, hsk.signing_key(), &c, &phi, &mut rng).unwrap();
    let state_bytes = |usk: &Ternary, phi: &BinaryPoly| {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&usk.to_bytes());
        bytes.extend_from_slice(&x0[0].to_bytes());
        bytes.extend_from_slice(&x0[1].to_bytes());
        bytes.extend_from_slice(phi.as_bytes());
        bytes
    };
    let state = IssuanceState::from_bytes(&state_bytes(usk.expose_ternary(), &phi)).unwrap();
    assert_eq!(state.to_bytes().unwrap().len(), IssuanceState::BYTES);
    let cred = pcs.unblind(&hvk, &usk, &f, &pre, &state).unwrap();
    assert!(pcs.verify_cred(&hvk, &usk, &f, &cred));
    // the state of another key, or of another predicate
    let other = Ternary::sample(&mut rng);
    let foreign = IssuanceState::from_bytes(&state_bytes(&other, &phi)).unwrap();
    assert_eq!(
        pcs.unblind(&hvk, &usk, &f, &pre, &foreign).err(),
        Some(Error::IssuanceStateMismatch)
    );
    assert_eq!(
        pcs.unblind(&hvk, &usk, &f_root, &pre, &state).err(),
        Some(Error::IssuanceStateMismatch)
    );
    // a pre-credential for another C (another x_0) fails closed
    let other_c = VSIS::issuance_encoding(
        sigma,
        &hvk,
        &VSISHiddenMessage::new(usk.expose_ternary().clone(), [x0[1].clone(), x0[0].clone()]),
        &phi,
        &VSISIssuanceState::new([x0[1].clone(), x0[0].clone()]),
    )
    .unwrap();
    let wrong = VSIS::blind_issue(sigma, hsk.signing_key(), &other_c, &phi, &mut rng).unwrap();
    assert_eq!(
        pcs.unblind(&hvk, &usk, &f, &wrong, &state).err(),
        Some(Error::InvalidPreCredential)
    );
    // a pre-credential under another helper key
    let (hvk2, hsk2) = pcs.helper_keygen(&mut rng);
    let pre2 = VSIS::blind_issue(sigma, hsk2.signing_key(), &c, &phi, &mut rng).unwrap();
    assert_eq!(
        pcs.unblind(&hvk, &usk, &f, &pre2, &state).err(),
        Some(Error::InvalidPreCredential)
    );
    assert!(pcs.unblind(&hvk2, &usk, &f, &pre2, &state).is_ok());

    // a helper key of another deployment, or a mismatched hvk, is refused before any proof is
    // looked at (the proof below would not verify anyway)
    let elsewhere = deployment(b"lattice-pcs/elsewhere", &f, &f_root);
    let (hvk3, hsk3) = elsewhere.helper_keygen(&mut rng);
    let request = RootRequest {
        c: c.clone(),
        t0: id.clone(),
        proof: Proof::from_bytes(vec![0; 64]).unwrap(),
    };
    assert_eq!(
        pcs.issue_root(&hvk3, &hsk3, &f_root, &id, &request, &mut rng)
            .err(),
        Some(Error::InvalidKey)
    );
    assert_eq!(
        pcs.issue_root(&hvk2, &hsk, &f_root, &id, &request, &mut rng)
            .err(),
        Some(Error::InvalidKey)
    );
    assert_eq!(
        pcs.issue_root(&hvk, &hsk, &f, &id, &request, &mut rng)
            .err(),
        Some(Error::NotARootPredicate)
    );
    // garbage proof bytes: refused by Jali's strict decoder (InvalidProof), quickly
    assert_eq!(
        pcs.check_root_request(&hvk, &f_root, &id, &request),
        Err(Error::InvalidProof)
    );
    assert_eq!(
        pcs.issue_root(&hvk, &hsk, &f_root, &id, &request, &mut rng)
            .err(),
        Some(Error::InvalidProof)
    );
    // nothing was issued for the refused requests: 3 base calls under hsk, 1 under hsk2
    assert_eq!(hsk.signing_key().issued(), 2);
    assert_eq!(hsk2.signing_key().issued(), 1);
}

/// A Jali proof longer than twice the estimate of its parameter set is refused before any Jali
/// work ([`ATT_PROOF_MAX_BYTES`], [`ISSUE_PROOF_MAX_BYTES`]), and the reason shows the order: an
/// oversized attestation proof inside `π` fails the public part of `CheckAtts_P`
/// (`InvalidAttestation`) before `π_0`, garbage here, is looked at (which gives `InvalidProof`).
/// The decoders refuse the same objects.
#[test]
fn oversized_proofs_are_refused_before_any_work() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0006);
    let f_root = Predicate::root(b"founders".to_vec());
    let f = Predicate::new(1, b"members".to_vec());
    let pcs = deployment(b"lattice-pcs/bounds", &f, &f_root);
    let (hvk, _) = pcs.helper_keygen(&mut rng);
    let (id, _) = pcs.user_keygen(&mut rng).unwrap();
    // canonical tags for the attester and for the self-exclusion tag
    let (tag, _) = pcs.user_keygen(&mut rng).unwrap();
    let (t0, _) = pcs.user_keygen(&mut rng).unwrap();
    let att = |len: usize| Attestation {
        tag: tag.clone(),
        phi: pcs.enc_pred(&f_root),
        proof: Proof::from_bytes(vec![0; len]).unwrap(),
    };
    let c = Rq::from_i64(&[1; 1024]).unwrap();
    let proof = |att_len: usize, pi0_len: usize| IssuanceProof {
        attestations: vec![att(att_len)],
        c: c.clone(),
        t0: t0.clone(),
        proof: Proof::from_bytes(vec![0; pi0_len]).unwrap(),
    };
    let start = Instant::now();
    assert_eq!(
        pcs.check_attestation(&hvk, &id, &att(ATT_PROOF_MAX_BYTES + 1)),
        Err(Error::InvalidProof)
    );
    assert_eq!(
        pcs.check_proof(&hvk, &f, &id, &proof(ATT_PROOF_MAX_BYTES + 1, 64)),
        Err(Error::InvalidAttestation)
    );
    assert_eq!(
        pcs.check_proof(&hvk, &f, &id, &proof(64, ISSUE_PROOF_MAX_BYTES + 1)),
        Err(Error::InvalidProof)
    );
    let request = RootRequest {
        c: c.clone(),
        t0: t0.clone(),
        proof: Proof::from_bytes(vec![0; ISSUE_PROOF_MAX_BYTES + 1]).unwrap(),
    };
    assert_eq!(
        pcs.check_root_request(&hvk, &f_root, &id, &request),
        Err(Error::InvalidProof)
    );
    println!("four oversized proofs refused in {:?}", start.elapsed());
    // within the bounds, the garbage reaches Jali's decoder: π_0 first (InvalidProof)
    assert_eq!(
        pcs.check_proof(&hvk, &f, &id, &proof(64, 64)),
        Err(Error::InvalidProof)
    );
    // the encoders and the decoders refuse the same objects
    assert!(att(ATT_PROOF_MAX_BYTES + 1).to_compact_bytes().is_err());
    assert!(
        proof(64, ISSUE_PROOF_MAX_BYTES + 1)
            .to_compact_bytes()
            .is_err()
    );
    assert!(request.to_compact_bytes().is_err());
    let mut bytes = att(ATT_PROOF_MAX_BYTES).to_compact_bytes().unwrap();
    assert_eq!(
        Attestation::from_compact_bytes(&bytes).unwrap(),
        att(ATT_PROOF_MAX_BYTES)
    );
    bytes[464..468].copy_from_slice(&(ATT_PROOF_MAX_BYTES as u32 + 1).to_le_bytes());
    bytes.push(0);
    assert!(Attestation::from_compact_bytes(&bytes).is_err());
}

/// The helper secret key carries the issuance count, so a key restored at the cap refuses to
/// issue ([`Error::IssuanceCapReached`]), here through the base's `BlindIssue` that `Issue`
/// and `issue_root` call after their proof checks.
#[test]
fn a_helper_key_at_the_cap_refuses() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0003);
    let f_root = Predicate::root(b"founders".to_vec());
    let f = Predicate::new(1, b"members".to_vec());
    let pcs = deployment(b"lattice-pcs/cap", &f, &f_root);
    let (_, hsk) = pcs.helper_keygen(&mut rng);
    let mut bytes = hsk.to_bytes().unwrap().to_vec();
    assert_eq!(bytes.len(), VSISSigningKey::BYTES + 2560 + 32);
    // the count is the last 8 bytes of the signing key's encoding
    let at = VSISSigningKey::BYTES - 8;
    bytes[at..at + 8].copy_from_slice(&Q_MAX.to_le_bytes());
    let full = HelperSecretKey::<VSIS>::from_bytes(&bytes).unwrap();
    assert_eq!(full.signing_key().remaining(), 0);
    let sigma = &pcs.public_parameters().pp_sigma;
    let c = Rq::from_i64(&[1; 1024]).unwrap();
    assert_eq!(
        VSIS::blind_issue(sigma, full.signing_key(), &c, &pcs.enc_pred(&f), &mut rng).err(),
        Some(Error::IssuanceCapReached)
    );
}

/// The sizes of the README row with real proofs at `k = 5` (one helper key): the fixed
/// overheads exactly, and each Jali proof within [0.95, 1] of the estimate of its parameter
/// set (Jali proofs vary by tens of bytes with the seed). Prints the measured sizes.
#[test]
#[ignore = "heavy: 5 root issuances, 5 attestations and a k = 5 proof (about 2 minutes in release)"]
fn sizes_at_k5() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0005);
    let f_root = Predicate::root(b"founders".to_vec());
    let f = Predicate::new(5, b"members".to_vec());
    let pcs = deployment(b"lattice-pcs/sizes", &f, &f_root);
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);
    let sets = ParameterSets::load().unwrap();
    let estimate = |p: &predicate_credential_system::jali::params::TboxParams| {
        p.check().unwrap().estimated_proof_bytes
    };
    let (att_estimate, issue_estimate) = (estimate(&sets.att), estimate(&sets.issue));
    let in_band = |len: usize, estimate: usize| len * 100 >= estimate * 95 && len <= estimate;

    let mut members = Vec::new();
    let mut requests = Vec::new();
    for _ in 0..5 {
        let (member, request) = root_member(&pcs, &hvk, &hsk, &f_root, &mut rng);
        members.push(member);
        requests.push(request);
    }
    let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
    let attestations: Vec<Attestation> = members
        .iter()
        .map(|m| {
            pcs.attest(&hvk, &m.usk, &m.f, &m.cred, &id, &mut rng)
                .unwrap()
        })
        .collect();
    let (proof, state) = pcs
        .prove(&hvk, &f, &id, &usk, &attestations, &mut rng)
        .unwrap();
    let pre = pcs.issue(&hvk, &hsk, &f, &id, &proof, &mut rng).unwrap();
    let cred = pcs.unblind(&hvk, &usk, &f, &pre, &state).unwrap();
    assert!(pcs.verify_cred(&hvk, &usk, &f, &cred));

    for att in &attestations {
        assert_eq!(att.compact_size(), 468 + att.proof.len());
        assert!(
            in_band(att.proof.len(), att_estimate),
            "{} vs {att_estimate}",
            att.proof.len()
        );
    }
    let jali: usize = attestations.iter().map(|a| a.proof.len()).sum();
    assert_eq!(
        proof.compact_size(),
        5 * 468 + jali + 2900 + proof.proof.len()
    );
    assert_eq!(
        WireFormat::to_bytes(&proof).unwrap().len(),
        proof.compact_size() + 4
    );
    assert!(in_band(proof.proof.len(), issue_estimate));
    for request in &requests {
        assert_eq!(request.compact_size(), 2900 + request.proof.len());
        assert!(in_band(request.proof.len(), issue_estimate));
    }
    assert_eq!(cred.to_bytes().unwrap().len(), 5888);
    assert_eq!(WireFormat::to_bytes(&pre).unwrap().len(), 5376);
    assert_eq!(WireFormat::to_bytes(&hvk).unwrap().len(), 2560);
    assert_eq!(hsk.to_bytes().unwrap().len(), 8489);
    assert_eq!(usk.to_bytes().unwrap().len(), 256);
    assert_eq!(state.to_bytes().unwrap().len(), 896);
    let att_sizes: Vec<usize> = attestations.iter().map(Attestation::compact_size).collect();
    let root_sizes: Vec<usize> = requests.iter().map(RootRequest::compact_size).collect();
    println!(
        "SIZES k = 5 (bytes, compact): att {att_sizes:?} (Jali R_att {:?}, estimate {att_estimate}); \
         π {} (π_0 {}, estimate {issue_estimate}); root requests {root_sizes:?}; cred {}; ĉred {}; hvk {}; \
         hsk {}; usk {}; st_iss {}",
        attestations
            .iter()
            .map(|a| a.proof.len())
            .collect::<Vec<_>>(),
        proof.compact_size(),
        proof.proof.len(),
        Credential::BYTES,
        VSISCredential::BYTES,
        2560,
        8489,
        256,
        IssuanceState::BYTES,
    );
}
