//! The protocol `Π_PCreds` at the lattice instantiation (`pcreds::lattice::LatticeBackend`):
//! one complete flow, and the checks that need no proof (setup and received parameters, helper
//! keys, users, states, the encodings, the bounds on proofs).
//!
//! The flow runs Jali proofs and runs in release builds:
//!
//! ```text
//! cargo test --release --features lattice --test lattice_protocol -- --nocapture
//! ```
//!
//! `a_helper_at_its_cap_records_nothing` (heavy) runs with `-- --ignored` in release.
#![cfg(feature = "lattice")]

mod lattice_support;

use ark_serialize::CanonicalSerialize;
use lattice_support::{Bk, Deployment, timed};
use predicate_credential_system::{
    Error,
    hash::Transcript,
    kiprf::lwr::LWRTag,
    lattice::{
        Q_MAX, Rq, STRAIGHT_LINE, Ternary, oracles,
        sets::{
            ATT_PROOF_MAX_BYTES, ISS_PROOF_MAX_BYTES, POSSESS_PROOF_MAX_BYTES, TAG_PROOF_MAX_BYTES,
        },
    },
    pcreds::{
        Attestation, AttestationRequest, Backend, CredentialRequest, Decision, IssuanceRecord,
        IssuanceState, MembershipProof, Policy, ProofKind, Protocol, PublicParameters, Reply, User,
        lattice::{LatticeBackend, LatticeParams, LatticePoint, LatticeProof, LatticeProtocol},
    },
    serialization::{WireFormat, from_bytes, to_bytes},
};
use rand::{RngCore, SeedableRng, rngs::StdRng};

/// The complete flow at `k = 1` with every message through its compact and canonical encodings:
/// root admission, `π_id`, an attestation, a credential request, issuance, a membership proof.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: Jali proofs; runs in release builds (cargo test --release --features lattice --test lattice_protocol)"
)]
fn quick_end_to_end_k1() {
    let mut d = timed("setup, KeyGen and one root admission", || {
        Deployment::new(b"lattice-protocol/k1", 1, 1, 0x1a77_0001)
    });
    let pcreds = d.pcreds.clone();
    // the published pp round trips and is accepted by a verifier that derives its own
    let pp_bytes = to_bytes(pcreds.public_parameters()).unwrap();
    let received: PublicParameters<Bk> = from_bytes(&pp_bytes).unwrap();
    let verifier = LatticeProtocol::from_public_parameters(received).unwrap();
    assert_eq!(verifier.parameters_digest(), pcreds.parameters_digest());
    // the verifier checks the published helper key and derives its identifier point itself
    let hvk = verifier.helper_key(d.hvk.vk()).unwrap();
    assert_eq!(hvk.identifier_point(), d.hvk.identifier_point());

    // AttestationRequest: π_id, through the compact encoding
    let newcomer = d.register();
    let ssid = d.ssid();
    let contact = b"member-0@example".to_vec();
    let request = timed("π_id", || {
        pcreds
            .request_attestation(&d.hvk, &newcomer, &ssid, &contact, &mut d.rng)
            .unwrap()
    });
    let wire = request.to_compact_bytes().unwrap();
    assert_eq!(wire.len(), request.compact_size());
    assert_eq!(wire.len(), LWRTag::BYTES + 4 + request.proof.len());
    let request = AttestationRequest::<Bk>::from_compact_bytes(&wire).unwrap();
    let pending = timed("check π_id", || {
        verifier
            .receive_attestation_request(&hvk, &request, &ssid, &contact)
            .unwrap()
    });
    // another sub-session or contact: the identifier proof does not verify
    assert!(!verifier.verify_attestation_request(&hvk, &request, b"another ssid", &contact));
    assert!(!verifier.verify_attestation_request(&hvk, &request, &ssid, b"another contact"));

    // AttestationRequestResponse
    let member = &d.members[0];
    let att = timed("π_att", || {
        pcreds
            .attest(&d.hvk, &member.user, &member.cred, pending, &mut d.rng)
            .unwrap()
    });
    assert!(att.proof.len() <= ATT_PROOF_MAX_BYTES);
    let wire = att.to_compact_bytes().unwrap();
    assert_eq!(wire.len(), att.size());
    let att = Attestation::<Bk>::from_compact_bytes(&wire).unwrap();
    timed("check π_att", || {
        verifier
            .check_attestation(&hvk, newcomer.id(), &att)
            .unwrap()
    });

    // CredentialRequest and CredentialRequestResponse
    let (message, state, ssid) = timed("π_iss", || d.request(&newcomer, vec![att.clone()]));
    let wire = message.to_compact_bytes().unwrap();
    assert_eq!(wire.len(), message.compact_size());
    let message = CredentialRequest::<Bk>::from_compact_bytes(&wire).unwrap();
    let evaluated = timed("evaluate the request", || {
        d.pcreds
            .evaluate_request(&d.helper, &message, &ssid)
            .unwrap()
    });
    assert!(evaluated.is_valid());
    assert_eq!(evaluated.tags(), std::slice::from_ref(&att.tag));
    let reply = d
        .pcreds
        .respond(&mut d.helper, evaluated, Decision::Policy, &mut d.rng)
        .unwrap();
    let wire = reply.to_compact_bytes().unwrap();
    let Reply::PreCredential(pre) = Reply::<Bk>::from_compact_bytes(&wire).unwrap() else {
        panic!("a valid request is issued");
    };
    // the requester's state can be stored until the reply arrives
    let state = IssuanceState::<Bk>::from_bytes(&state.to_bytes().unwrap()).unwrap();
    let cred = d.pcreds.unblind(&d.hvk, &newcomer, &pre, state).unwrap();
    assert!(d.pcreds.verify_credential(&d.hvk, &newcomer, &cred));
    // a second request of the same identifier is answered issued
    let attestations = d.attestations(&newcomer, 1);
    let (again, again_state, again_ssid) = d.request(&newcomer, attestations);
    assert!(
        d.answer(
            &newcomer,
            &again,
            again_state,
            &again_ssid,
            Decision::Policy
        )
        .unwrap()
        .is_issued()
    );
    assert_eq!(d.helper.store().len(), 2);

    // Prove and Verify
    let proof = timed("π_prove", || {
        d.pcreds
            .prove(&d.hvk, &newcomer, &cred, b"hello", &mut d.rng)
            .unwrap()
    });
    assert!(proof.proof.len() <= POSSESS_PROOF_MAX_BYTES);
    let wire = proof.to_compact_bytes().unwrap();
    assert_eq!(wire.len(), proof.size());
    let proof = MembershipProof::<Bk>::from_compact_bytes(&wire).unwrap();
    timed("check π_prove", || {
        verifier.check_membership(&hvk, b"hello", &proof).unwrap()
    });
    assert_eq!(
        verifier.check_membership(&hvk, b"another message", &proof),
        Err(Error::InvalidProof)
    );
    println!(
        "[size] |π_id| = {}, |π_att| = {}, |π_iss| = {}, |π_prove| = {} bytes",
        request.proof.len(),
        att.proof.len(),
        message.proof.len(),
        proof.proof.len()
    );
}

/// A helper whose key is at the issuance cap: `BlindIssue` refuses, and `respond` records
/// nothing, so the identifier can still be issued to under a new key (`respond` runs
/// `BlindIssue` before the record).
#[test]
#[ignore = "heavy: one π_iss; cargo test --release --features lattice --test lattice_protocol -- --ignored"]
fn a_helper_at_its_cap_records_nothing() {
    let mut d = Deployment::new(b"lattice-protocol/cap", 1, 0, 0x1a77_0002);
    // the helper's key, stored with its count advanced to the cap, then restored
    let bytes = d.helper.to_bytes_reserving(Q_MAX).unwrap();
    let mut at_cap = d
        .pcreds
        .restore_helper(&bytes, *d.helper.policy(), IssuanceRecord::new())
        .unwrap();
    let user = d.register();
    let ssid = d.ssid();
    let (message, _state) = d
        .pcreds
        .request_credential(&d.hvk, &user, Vec::new(), &ssid, &mut d.rng)
        .unwrap();
    let evaluated = d.pcreds.evaluate_request(&at_cap, &message, &ssid).unwrap();
    assert_eq!(
        d.pcreds
            .respond(&mut at_cap, evaluated, Decision::Root, &mut d.rng)
            .unwrap_err(),
        Error::IssuanceCapReached
    );
    assert!(at_cap.store().is_empty(), "nothing recorded");
    // the same request at the helper with its true count is issued
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &message, &ssid)
        .unwrap();
    assert!(matches!(
        d.pcreds
            .respond(&mut d.helper, evaluated, Decision::Root, &mut d.rng)
            .unwrap(),
        Reply::PreCredential(_)
    ));
    assert_eq!(d.helper.store().len(), 1);
}

// ---------------------------------------------------------------------------------------------
// Checks that need no proof
// ---------------------------------------------------------------------------------------------

/// `Setup` is transparent: the parameters are the label's, a received `pp` is accepted only if
/// it is what `Setup` derives, and the encoding of the parameters is strict.
#[test]
fn setup_is_transparent_and_received_parameters_are_checked() {
    let a = LatticeProtocol::setup(b"lattice-protocol/setup").unwrap();
    let b = LatticeProtocol::setup(b"lattice-protocol/setup").unwrap();
    assert_eq!(a.parameters_digest(), b.parameters_digest());
    assert_eq!(a.public_parameters(), b.public_parameters());
    let other = LatticeProtocol::setup(b"lattice-protocol/another").unwrap();
    assert_ne!(a.parameters_digest(), other.parameters_digest());
    assert_eq!(LatticeBackend::name(), "vSIS+LWR");

    // the encoding of pp round trips, with the label, and is refused under another label
    let bytes = to_bytes(a.public_parameters()).unwrap();
    let back: PublicParameters<Bk> = from_bytes(&bytes).unwrap();
    assert_eq!(&back, a.public_parameters());
    assert!(LatticeProtocol::from_public_parameters(back.clone()).is_ok());
    let mut relabelled = back.clone();
    relabelled.label = b"lattice-protocol/another".to_vec();
    assert!(matches!(
        LatticeProtocol::from_public_parameters(relabelled),
        Err(Error::InvalidPublicParameters(_))
    ));
    let mut foreign = back;
    foreign.params = other.params().clone();
    assert!(matches!(
        LatticeProtocol::from_public_parameters(foreign),
        Err(Error::InvalidPublicParameters(_))
    ));

    // the parameters' encoding is strict: a changed constant, pin, revision or placement, a
    // truncated or extended encoding
    let params = to_bytes(a.params()).unwrap();
    assert_eq!(params.len(), a.params().compressed_size());
    let back: LatticeParams = from_bytes(&params).unwrap();
    assert_eq!(&back, a.params());
    let label_len = 8 + a.label().len();
    for offset in [
        label_len,                                  // the format version
        label_len + 8 * 16 + 12_800 + 32,           // the first pin
        label_len + 8 * 16 + 12_800 + 32 + 128 + 8, // the Jali revision
        params.len() - 1,                           // the placement
    ] {
        let mut bad = params.clone();
        bad[offset] ^= 1;
        assert!(
            from_bytes::<LatticeParams>(&bad).is_err(),
            "offset {offset}"
        );
    }
    assert!(from_bytes::<LatticeParams>(&params[..params.len() - 1]).is_err());
    let mut long = params;
    long.push(0);
    assert_eq!(
        from_bytes::<LatticeParams>(&long).unwrap_err(),
        Error::TrailingBytes
    );
}

/// The identifier point and the recipient points: `x_Q` depends on `hvk` and `id_Q`, is never
/// `x_0`, and the points encode strictly.
#[test]
fn recipient_points_are_bound_to_the_helper_and_the_requester() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0003);
    let pcreds = LatticeProtocol::setup(b"lattice-protocol/points").unwrap();
    let helper = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let other = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let hvk = helper.key().clone();
    let (alice, bob) = (
        pcreds.register(&hvk, &mut rng).unwrap(),
        pcreds.register(&hvk, &mut rng).unwrap(),
    );
    // x_0 = H_id(⟨hvk⟩): one per helper key, derived again by anyone from the key
    let x0 = hvk.identifier_point().clone();
    assert!(matches!(x0, LatticePoint::Identifier(_)));
    assert_eq!(pcreds.identifier_point(hvk.vk()).unwrap(), x0);
    assert_ne!(other.key().identifier_point(), &x0);
    let x = |vk, id| pcreds.recipient_point(vk, id).unwrap();
    let xa = x(helper.key().vk(), alice.id());
    assert_ne!(xa, x0);
    assert_eq!(xa, x(helper.key().vk(), alice.id()));
    assert_ne!(xa, x(helper.key().vk(), bob.id()));
    assert_ne!(xa, x(other.key().vk(), alice.id()));
    // the recipient point is H_req of the transcript the protocol frames
    let LatticePoint::Request(d) = &xa else {
        panic!("a recipient point")
    };
    let _ = Transcript::new(b"/PCREDS-HREQ"); // the oracle the protocol uses (src/pcreds/context.rs)
    assert_eq!(d.len(), 32);
    // encodings
    for p in [x0.clone(), xa.clone()] {
        let bytes = to_bytes(&p).unwrap();
        assert_eq!(bytes.len(), p.compressed_size());
        assert_eq!(from_bytes::<LatticePoint>(&bytes).unwrap(), p);
    }
    assert!(from_bytes::<LatticePoint>(&[2; 33]).is_err());
    assert!(from_bytes::<LatticePoint>(&[1, 0, 0]).is_err());
    assert!(from_bytes::<LatticePoint>(&[0; 32]).is_err());
    assert_eq!(
        from_bytes::<LatticePoint>(&[0; 34]).unwrap_err(),
        Error::TrailingBytes
    );
    // the matrices differ, and each is H_mat under its oracle's label
    assert_ne!(pcreds.params().matrix(&xa), pcreds.params().matrix(&x0));
    let LatticePoint::Identifier(d0) = &x0 else {
        unreachable!("an identifier point")
    };
    assert_eq!(
        pcreds.params().matrix(&x0),
        oracles::identifier_point(b"lattice-protocol/points", d0)
    );
}

/// A helper key is checked once and bound to one deployment; it is stored and restored with its
/// issuance count, also ahead of the true one.
#[test]
fn helper_keys_are_bound_to_one_deployment_and_carry_their_count() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0004);
    let pcreds = LatticeProtocol::setup(b"lattice-protocol/keys").unwrap();
    let policy = Policy::threshold(2).unwrap();
    let helper = pcreds.helper_keygen(policy, &mut rng);
    let hvk = pcreds.helper_key(helper.key().vk()).unwrap();
    assert_eq!(&hvk, helper.key());

    let bytes = helper.to_bytes().unwrap();
    let restored = pcreds
        .restore_helper(&bytes, policy, IssuanceRecord::new())
        .unwrap();
    assert_eq!(restored.key(), helper.key());
    // ahead by n: the stored count is n, the plain encoding has 0
    let ahead = helper.to_bytes_reserving(7).unwrap();
    assert_eq!(ahead.len(), bytes.len());
    assert_ne!(&ahead[..], &bytes[..]);
    assert_eq!(&ahead[ahead.len() - 8..], &7u64.to_le_bytes());
    assert_eq!(&bytes[bytes.len() - 8..], &0u64.to_le_bytes());
    assert!(
        pcreds
            .restore_helper(&ahead, policy, IssuanceRecord::new())
            .is_ok()
    );
    // under another deployment the key is refused
    let elsewhere = LatticeProtocol::setup(b"lattice-protocol/elsewhere").unwrap();
    assert_eq!(
        elsewhere
            .restore_helper(&bytes, policy, IssuanceRecord::new())
            .unwrap_err(),
        Error::InvalidKey
    );
    // another key's trapdoor with this hvk is refused
    let other = pcreds.helper_keygen(policy, &mut rng);
    let mut mixed = bytes[..32 + 2560].to_vec();
    mixed.extend_from_slice(&other.to_bytes().unwrap()[32 + 2560..]);
    assert_eq!(
        pcreds
            .restore_helper(&mixed, policy, IssuanceRecord::new())
            .unwrap_err(),
        Error::InvalidKey
    );
    // truncated and extended encodings
    assert!(
        pcreds
            .restore_helper(&bytes[..bytes.len() - 1], policy, IssuanceRecord::new())
            .is_err()
    );
    let mut long = bytes.to_vec();
    long.push(0);
    assert_eq!(
        pcreds
            .restore_helper(&long, policy, IssuanceRecord::new())
            .unwrap_err(),
        Error::TrailingBytes
    );
    assert_eq!(format!("{helper:?}").matches("<redacted>").count(), 1);
}

/// Users and their identifiers: `Register`, a user from a given key, the check of a stored user.
#[test]
fn users_are_registered_and_checked() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0005);
    let pcreds = LatticeProtocol::setup(b"lattice-protocol/users").unwrap();
    let helper = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let hvk = helper.key().clone();
    let user = pcreds.register(&hvk, &mut rng).unwrap();
    pcreds.check_user(&hvk, &user).unwrap();
    let key = Ternary::sample(&mut rng);
    let again = pcreds.user(&hvk, key.clone()).unwrap();
    assert_eq!(again.id(), pcreds.user(&hvk, key).unwrap().id());
    assert_ne!(again.id(), user.id());
    // a user stored and read back
    let stored = User::<Bk>::from_bytes(&user.to_bytes().unwrap()).unwrap();
    pcreds.check_user(&hvk, &stored).unwrap();
    assert_eq!(stored.id(), user.id());
    // under another deployment
    let elsewhere = LatticeProtocol::setup(b"lattice-protocol/elsewhere").unwrap();
    let hvk_elsewhere = elsewhere.helper_key(hvk.vk()).unwrap();
    assert_eq!(
        elsewhere.check_user(&hvk_elsewhere, &user).unwrap_err(),
        Error::IdentifierMismatch
    );
    assert_eq!(
        elsewhere.check_user(&hvk, &user).unwrap_err(),
        Error::InvalidKey
    );
    // under another helper key of the deployment: another user, with the same key
    let other = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    assert_eq!(
        pcreds.check_user(other.key(), &user).unwrap_err(),
        Error::IdentifierMismatch
    );
    let reused = pcreds.register_reusing(other.key(), &user).unwrap();
    pcreds.check_user(other.key(), &reused).unwrap();
    assert_ne!(reused.id(), user.id());
    assert_eq!(reused.expose_key(), user.expose_key());
    assert_eq!(format!("{user:?}").matches("<redacted>").count(), 1);
}

/// A proof longer than its kind's bound is refused before any work: by the compact decoders, by
/// the backend's encoder, and by every verifier of the protocol.
#[test]
fn oversized_proofs_are_refused_before_any_work() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0006);
    let pcreds = LatticeProtocol::setup(b"lattice-protocol/oversized").unwrap();
    let helper = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let hvk = pcreds.helper_key(helper.key().vk()).unwrap();
    let user = pcreds.register(&hvk, &mut rng).unwrap();
    let long = |n: usize| LatticeProof::from_bytes(vec![0u8; n + 1]).unwrap();
    for (kind, max) in [
        (ProofKind::Identifier, TAG_PROOF_MAX_BYTES),
        (ProofKind::Attestation, ATT_PROOF_MAX_BYTES),
        (ProofKind::Issuance, ISS_PROOF_MAX_BYTES),
        (ProofKind::Possession, POSSESS_PROOF_MAX_BYTES),
    ] {
        assert_eq!(LatticeProof::max_bytes(kind), max);
        let proof = long(max);
        let mut wire = Vec::new();
        assert!(matches!(
            LatticeBackend::serialize_proof_compact(kind, &proof, &mut wire),
            Err(Error::LengthMismatch { .. })
        ));
        // a forged length above the bound, with no proof behind it
        let mut forged = ((max + 1) as u32).to_le_bytes().to_vec();
        forged.extend_from_slice(&[0; 16]);
        assert!(LatticeBackend::deserialize_proof_compact(kind, &forged[..]).is_err());
    }
    // the verifiers refuse at once (no Jali work: these would take seconds otherwise)
    let start = std::time::Instant::now();
    let request = AttestationRequest::<Bk> {
        id: user.id().clone(),
        proof: long(TAG_PROOF_MAX_BYTES),
    };
    assert!(matches!(
        pcreds.receive_attestation_request(&hvk, &request, b"s", b"c"),
        Err(Error::InvalidProof)
    ));
    let att = Attestation::<Bk> {
        tag: user.id().clone(),
        show: (),
        proof: long(ATT_PROOF_MAX_BYTES),
    };
    assert_eq!(
        pcreds.check_attestation(&hvk, user.id(), &att).unwrap_err(),
        Error::InvalidProof
    );
    let message = CredentialRequest::<Bk> {
        id: user.id().clone(),
        attestations: vec![att],
        request: Rq::zero(),
        proof: long(ISS_PROOF_MAX_BYTES),
    };
    assert_eq!(
        pcreds
            .evaluate_request(&helper, &message, b"s")
            .unwrap_err(),
        Error::InvalidProof
    );
    let proof = MembershipProof::<Bk> {
        show: (),
        proof: long(POSSESS_PROOF_MAX_BYTES),
    };
    assert_eq!(
        pcreds.check_membership(&hvk, b"m", &proof).unwrap_err(),
        Error::InvalidProof
    );
    assert!(
        start.elapsed().as_secs_f64() < 2.0,
        "refused before any proof work"
    );
}

/// The decoders of every received object never panic on arbitrary bytes, and what they accept
/// re-encodes to the same bytes.
#[test]
fn decoders_never_panic_on_arbitrary_bytes() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0007);
    for len in [
        0usize, 1, 3, 4, 31, 32, 33, 336, 768, 2560, 5376, 6144, 10_000,
    ] {
        for _ in 0..8 {
            let mut bytes = vec![0u8; len];
            rng.fill_bytes(&mut bytes);
            fn round_trip<T: WireFormat + PartialEq + core::fmt::Debug>(bytes: &[u8]) {
                if let Ok(v) = T::from_bytes(bytes) {
                    assert_eq!(v.to_bytes().unwrap(), bytes);
                }
            }
            round_trip::<LWRTag>(&bytes);
            round_trip::<LatticePoint>(&bytes);
            round_trip::<LatticeProof>(&bytes);
            round_trip::<Rq>(&bytes);
            let _ = Reply::<Bk>::from_bytes(&bytes);
            let _ = AttestationRequest::<Bk>::from_compact_bytes(&bytes);
            let _ = Attestation::<Bk>::from_compact_bytes(&bytes);
            let _ = CredentialRequest::<Bk>::from_compact_bytes(&bytes);
            let _ = MembershipProof::<Bk>::from_compact_bytes(&bytes);
            let _ = from_bytes::<LatticeParams>(&bytes);
            let _ = IssuanceState::<Bk>::from_bytes(&bytes);
            let _ = User::<Bk>::from_bytes(&bytes);
        }
    }
    // a proof's canonical encoding: its length, then its bytes
    let proof = LatticeProof::from_bytes(vec![7; 10]).unwrap();
    let bytes = to_bytes(&proof).unwrap();
    assert_eq!(&bytes[..4], &10u32.to_le_bytes());
    assert_eq!(from_bytes::<LatticeProof>(&bytes).unwrap(), proof);
    assert!(LatticeProof::from_bytes(vec![0; LatticeProof::MAX_BYTES + 1]).is_err());
}

/// Every lattice object has the documented size.
#[test]
fn the_objects_have_the_documented_sizes() {
    let mut rng = StdRng::seed_from_u64(0x1a77_0008);
    let label = b"lattice-protocol/sizes";
    let pcreds = LatticeProtocol::setup(label).unwrap();
    // `LE64(|L|) ‖ L ‖ LatticeParams`, with `LatticeParams` = `LE64(|L|) ‖ L`, 16 words, `pp_Σ`,
    // the seed, four pins, the Jali version (5) and the placement (31), and in the extractable
    // build the argument system (20) and the four pins of the extraction sets
    let extractable = if STRAIGHT_LINE { 8 + 20 + 4 * 32 } else { 0 };
    assert_eq!(
        to_bytes(pcreds.public_parameters()).unwrap().len(),
        13_156 + 2 * label.len() + extractable
    );
    let helper = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let user = pcreds.register(helper.key(), &mut rng).unwrap();
    // a point: its kind and the 32-byte digest of its oracle's transcript
    assert_eq!(to_bytes(helper.key().identifier_point()).unwrap().len(), 33);
    assert_eq!(to_bytes(helper.key().vk()).unwrap().len(), 2560);
    assert_eq!(helper.to_bytes().unwrap().len(), 32 + 2560 + 5897);
    assert_eq!(to_bytes(user.id()).unwrap().len(), LWRTag::BYTES);
    assert_eq!(LWRTag::BYTES, 336);
    assert_eq!(user.to_bytes().unwrap().len(), 256 + 336 + 32 + 32);
    assert_eq!(to_bytes(&()).unwrap().len(), 0);
    let _: Protocol<Bk> = pcreds;
}
