//! End to end, one test per claim of the design (`design-docs/vetting-hidden-vetters-pcs.md`),
//! adversarial cases included, on `pcreds` (README, "Changes for `pcreds`"). Counting is VTI's
//! own `requirements::evaluate`, unchanged.

use chrono::{DateTime, NaiveDate, TimeZone, Utc};
use pcs_vetting_prototype::{
    ProtoError,
    applicant::ApplicantEngine,
    meta::StatementMeta,
    scheme::point_text,
    token::TokenWallet,
    vetter::{HiddenAttestation, VetterEngine},
    vtc::{Decision, Vtc},
};
use predicate_credential_system::Error as PcsError;
use rand::{SeedableRng, rngs::StdRng};
use serde_json::json;
use vta_sdk::{
    protocols::vetting::{IDENTITY_VETTING_ENDORSEMENT_TYPE, VettingMethod, VettingRelationship},
    vetting::requirements::Need,
};

const COMMUNITY: &str = "did:example:kernel-vtc";
const R: usize = 3; // tokens per tick in these tests

fn now() -> DateTime<Utc> {
    Utc.with_ymd_and_hms(2026, 9, 22, 12, 0, 0).unwrap()
}

fn requirements() -> serde_json::Value {
    json!({
        "version": "0.1",
        "statementType": IDENTITY_VETTING_ENDORSEMENT_TYPE,
        "minStatements": 2,
        "minByMethod": { "inPerson": 1 },
        "acceptedMethods": ["inPerson", "video", "priorAcquaintance"],
        "requiredClaims": ["name.legal"],
        "maxStatementAge": "P120D",
        "eligibleVetters": { "role": "vetter" },
        "independence": {
            "maxByDeclaredRelationship": { "family": 0 },
            "requireConsistentIdentityCommitment": true
        }
    })
}

struct World {
    rng: StdRng,
    vtc: Vtc,
    vetters: Vec<VetterEngine>,
}

/// A community in period 2026-09 with `n` enrolled vetters, each with one drip.
fn world(seed: u64, n: usize) -> World {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut vtc = Vtc::new(COMMUNITY, "2026-09", requirements(), &mut rng).unwrap();
    let mut vetters = Vec::new();
    for i in 0..n {
        let member = format!("member-{i}");
        vtc.grant(&member);
        let mut v = VetterEngine::new(&member);
        v.enroll(&mut vtc, &mut rng).unwrap();
        let label = vtc.current_token_label().to_string();
        v.drip(&mut vtc, 1, &label, R, &mut rng).unwrap();
        vetters.push(v);
    }
    World { rng, vtc, vetters }
}

fn meta(app: &ApplicantEngine, vtc: &Vtc, method: VettingMethod) -> StatementMeta {
    app.statement_meta(
        vtc,
        StatementMeta {
            community: String::new(),
            requirements_digest: String::new(),
            method,
            claims_verified: vec!["name.legal".into()],
            liveness_confirmed: true,
            declared_relationship: VettingRelationship::None,
            identity_commitment: "zCommitmentOfThisApplication".into(),
            card_digest_multibase: "zCardDigest".into(),
            valid_from: NaiveDate::from_ymd_opt(2026, 9, 20).unwrap(),
            valid_until: NaiveDate::from_ymd_opt(2027, 1, 18).unwrap(),
            token_label: String::new(),
            token_serial: String::new(),
        },
    )
}

/// One vetting session: the applicant's request, accept (reserves a token), human check,
/// attest.
fn vet(w: &mut World, j: usize, app: &ApplicantEngine, method: VettingMethod) -> HiddenAttestation {
    let m = meta(app, &w.vtc, method);
    let request = app
        .vetting_request(&w.vtc, &w.vetters[j].member, &mut w.rng)
        .unwrap();
    let r = w.vetters[j].accept(None, 2).unwrap();
    w.vetters[j]
        .attest(&w.vtc, &r, &request, m, &mut w.rng)
        .unwrap()
}

fn submit(w: &mut World, app: &ApplicantEngine) -> Result<Decision, ProtoError> {
    let c = w.vtc.challenge(&mut w.rng);
    let sub = app.submit(&w.vtc, &c, &mut w.rng)?;
    w.vtc.submit(&sub, now())
}

// -------------------------------------------------------------------------------------------

#[test]
fn admits_on_two_hidden_vetters_and_names_none() {
    let mut w = world(1, 3);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob-kernel", &mut w.rng).unwrap();
    let a = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.receive(&w.vtc, a).unwrap();
    let b = vet(&mut w, 1, &bob, VettingMethod::Video);
    bob.receive(&w.vtc, b).unwrap();

    let d = submit(&mut w, &bob).unwrap();
    assert!(d.evaluation.satisfied(), "{:?}", d.evaluation);
    assert_eq!(d.evaluation.distinct_vetters(), 2);

    // The facts the policy sees name no vetter: no member id, no vetter PCS id.
    let facts = serde_json::to_string(&d.statements).unwrap();
    for v in &w.vetters {
        assert!(!facts.contains(&v.member), "facts leak {}", v.member);
        for id in v.ids() {
            assert!(!facts.contains(&point_text(id).unwrap()));
        }
    }
    assert!(
        d.statements
            .iter()
            .all(|s| s.issuer.starts_with('z') && s.verified && s.counted)
    );
}

#[test]
fn request_more_then_admit_on_resubmission() {
    let mut w = world(2, 3);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let v = vet(&mut w, 1, &bob, VettingMethod::Video);
    bob.receive(&w.vtc, v).unwrap();

    let d = submit(&mut w, &bob).unwrap();
    assert!(!d.evaluation.satisfied());
    assert_eq!(
        d.evaluation.needs,
        vec![
            Need::Statements(1),
            Need::Method(VettingMethod::InPerson, 1)
        ]
    );

    let p = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.receive(&w.vtc, p).unwrap();
    let d = submit(&mut w, &bob).unwrap();
    assert!(d.evaluation.satisfied(), "{:?}", d.evaluation);
    // The first vetter's token came back with the same (id, tag): already counted, no anomaly.
    assert!(
        w.vtc.tokens.anomalies.is_empty(),
        "{:?}",
        w.vtc.tokens.anomalies
    );
}

#[test]
fn one_vetter_counts_once_across_submissions() {
    let mut w = world(3, 3);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let first = vet(&mut w, 0, &bob, VettingMethod::Video);
    bob.receive(&w.vtc, first).unwrap();
    submit(&mut w, &bob).unwrap();

    // The same vetter vets again, e.g. in person, and the client swaps it in.
    let second = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.replace(&w.vtc, second).unwrap();
    let d = submit(&mut w, &bob).unwrap();
    // Two statements on record, one tag: counted once.
    assert_eq!(d.statements.len(), 2);
    assert_eq!(d.evaluation.distinct_vetters(), 1);
    assert!(
        d.statements
            .iter()
            .any(|s| s.failures.contains(&"same-vetter".to_string()))
    );
}

#[test]
fn a_double_spent_token_does_not_count() {
    let mut w = world(4, 3);
    let mut alice = ApplicantEngine::new(&w.vtc, "did:example:alice", &mut w.rng).unwrap();
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();

    let for_alice = vet(&mut w, 0, &alice, VettingMethod::InPerson);
    let reused = for_alice.token.clone();
    alice.receive(&w.vtc, for_alice).unwrap();
    submit(&mut w, &alice).unwrap();

    // A cheating vetter reuses Alice's spent token for Bob.
    let m = meta(&bob, &w.vtc, VettingMethod::InPerson);
    let request = bob.vetting_request(&w.vtc, "member-0", &mut w.rng).unwrap();
    let cheat = w.vetters[0]
        .attest_with_token(&w.vtc, reused, &request, m, &mut w.rng)
        .unwrap();
    bob.receive(&w.vtc, cheat).unwrap(); // the signature itself is valid
    let honest = vet(&mut w, 1, &bob, VettingMethod::Video);
    bob.receive(&w.vtc, honest).unwrap();

    let d = submit(&mut w, &bob).unwrap();
    assert!(!d.evaluation.satisfied());
    assert_eq!(d.evaluation.distinct_vetters(), 1);
    assert!(
        d.statements
            .iter()
            .any(|s| s.failures.contains(&"token-double-spend".to_string()))
    );
    assert_eq!(
        w.vtc.tokens.anomalies.len(),
        1,
        "the VTC notices, without naming anyone"
    );
}

#[test]
fn tokens_and_metadata_cannot_move_between_attestations() {
    let mut w = world(5, 3);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let a = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.receive(&w.vtc, a).unwrap();
    let b = vet(&mut w, 1, &bob, VettingMethod::Video);
    bob.receive(&w.vtc, b).unwrap();

    // Swap the tokens only: the metadata names the other serial.
    let c = w.vtc.challenge(&mut w.rng);
    let mut sub = bob.submit(&w.vtc, &c, &mut w.rng).unwrap();
    let (t0, t1) = (sub.statements[0].1.clone(), sub.statements[1].1.clone());
    sub.statements[0].1 = t1;
    sub.statements[1].1 = t0;
    let d = w.vtc.submit(&sub, now()).unwrap();
    assert_eq!(d.evaluation.distinct_vetters(), 0);
    assert!(
        d.statements
            .iter()
            .all(|s| s.failures.contains(&"token-mismatch".to_string()))
    );

    // Swap the metadata too (claim "inPerson" for the video vetter): `π_iss` is bound to the
    // metadata of every statement in order, and the request breaks.
    let c = w.vtc.challenge(&mut w.rng);
    let mut sub = bob.submit(&w.vtc, &c, &mut w.rng).unwrap();
    sub.statements.swap(0, 1);
    assert_eq!(
        w.vtc.submit(&sub, now()).err(),
        Some(ProtoError::ProofRejected(PcsError::InvalidProof))
    );
}

#[test]
fn a_challenge_is_single_use_and_bound_to_the_proof() {
    let mut w = world(6, 2);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let a = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.receive(&w.vtc, a).unwrap();
    let c = w.vtc.challenge(&mut w.rng);
    let sub = bob.submit(&w.vtc, &c, &mut w.rng).unwrap();
    w.vtc.submit(&sub, now()).unwrap();
    assert_eq!(
        w.vtc.submit(&sub, now()).err(),
        Some(ProtoError::BadChallenge)
    );

    // A request made for one challenge does not verify under another (it is the `ssid`).
    let c2 = w.vtc.challenge(&mut w.rng);
    let mut replay = sub.clone();
    replay.challenge = c2;
    assert_eq!(
        w.vtc.submit(&replay, now()).err(),
        Some(ProtoError::ProofRejected(PcsError::InvalidProof))
    );
    // ... nor for another join DID (the id binding is in the proof context).
    let c3 = w.vtc.challenge(&mut w.rng);
    let mut other = bob.submit(&w.vtc, &c3, &mut w.rng).unwrap();
    other.join_did = "did:example:mallory".into();
    assert_eq!(
        w.vtc.submit(&other, now()).err(),
        Some(ProtoError::ProofRejected(PcsError::InvalidProof))
    );
}

#[test]
fn a_closed_token_label_means_no_token() {
    let mut w = world(7, 3);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let a = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.receive(&w.vtc, a).unwrap();
    let b = vet(&mut w, 1, &bob, VettingMethod::Video);
    bob.receive(&w.vtc, b).unwrap();
    let c = w.vtc.challenge(&mut w.rng);
    let sub = bob.submit(&w.vtc, &c, &mut w.rng).unwrap();

    let label = w.vtc.current_token_label().to_string();
    w.vtc.tokens.close_label(&label);
    let d = w.vtc.submit(&sub, now()).unwrap();
    assert_eq!(d.evaluation.distinct_vetters(), 0);
    assert!(
        d.statements
            .iter()
            .all(|s| s.failures.contains(&"no-token".to_string()))
    );
}

#[test]
fn an_application_lives_in_one_period_and_is_refreshed_across_a_rotation() {
    let mut w = world(8, 3);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    assert_eq!(bob.period(), "2026-09");
    let a = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    let old = a.clone();
    bob.receive(&w.vtc, a).unwrap();

    // Rotate: 2026-10 is current, 2026-09 still live. Vetters 0 and 1 enrol under 2026-10 and
    // draw its tokens. Vetter 1 still holds its 2026-09 credential and vets Bob under his
    // period, so the application in flight completes.
    w.vtc.rotate("2026-10", &mut w.rng).unwrap();
    let label = w.vtc.current_token_label().to_string();
    for j in [0, 1] {
        w.vetters[j].enroll(&mut w.vtc, &mut w.rng).unwrap();
        w.vetters[j]
            .drip(&mut w.vtc, 31, &label, R, &mut w.rng)
            .unwrap();
    }
    let b = vet(&mut w, 1, &bob, VettingMethod::Video);
    let sessions = [old.session.clone(), b.session.clone()];
    let old_tags = [old.attestation.tag, b.attestation.tag];
    bob.receive(&w.vtc, b).unwrap();
    let d = submit(&mut w, &bob).unwrap();
    assert!(d.evaluation.satisfied(), "{:?}", d.evaluation);

    // A vetter enrolled under 2026-10 only cannot vet an application of 2026-09.
    w.vtc.grant("member-3");
    let mut newcomer = VetterEngine::new("member-3");
    newcomer.enroll(&mut w.vtc, &mut w.rng).unwrap();
    newcomer
        .drip(&mut w.vtc, 31, &label, R, &mut w.rng)
        .unwrap();
    let request = bob.vetting_request(&w.vtc, "member-3", &mut w.rng).unwrap();
    let r = newcomer.accept(None, 32).unwrap();
    let m = meta(&bob, &w.vtc, VettingMethod::InPerson);
    assert_eq!(
        newcomer.attest(&w.vtc, &r, &request, m, &mut w.rng).err(),
        Some(ProtoError::NoCredentialForPeriod("2026-09".into()))
    );

    // 2026-09 is dropped: Bob's application under it fails as a whole.
    let c = w.vtc.challenge(&mut w.rng);
    let late = bob.submit(&w.vtc, &c, &mut w.rng).unwrap();
    w.vtc.drop_period("2026-09").unwrap();
    assert_eq!(
        w.vtc.submit(&late, now()).err(),
        Some(ProtoError::PeriodNotLive("2026-09".into()))
    );

    // Bob registers under 2026-10 and asks his two vetters to refresh the sessions he had: no
    // new vetting, a fresh token each, and new tags, under a new key and for a new identifier.
    let mut bob10 = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    assert_eq!(bob10.period(), "2026-10");
    let mut refreshed = Vec::new();
    for j in [0, 1] {
        let request = bob10
            .vetting_request(&w.vtc, &w.vetters[j].member, &mut w.rng)
            .unwrap();
        let att = w.vetters[j]
            .refresh(&w.vtc, &sessions[j], &request, &mut w.rng)
            .unwrap();
        assert_ne!(att.attestation.tag, old_tags[j]);
        refreshed.push(att.clone());
        bob10.receive(&w.vtc, att).unwrap();
    }
    let d = submit(&mut w, &bob10).unwrap();
    assert!(d.evaluation.satisfied(), "{:?}", d.evaluation);
    assert_eq!(d.evaluation.distinct_vetters(), 2);

    // A request is evaluated under its period's key alone: an attestation of the old
    // application, forced into Bob's new request, does not verify there and does not count.
    let c = w.vtc.challenge(&mut w.rng);
    let mixed = bob10
        .submit_attestations(&w.vtc, &c, &[&refreshed[0], &old], &mut w.rng)
        .unwrap();
    let d = w.vtc.submit(&mixed, now()).unwrap();
    let old_id = old.meta.digest().unwrap();
    let row = d.statements.iter().find(|s| s.id == old_id).unwrap();
    assert!(!row.verified && !row.counted);
    assert!(row.failures.contains(&"unverified".to_string()));
    assert_eq!(d.evaluation.distinct_vetters(), 2);
}

#[test]
fn a_dropped_period_fails_the_whole_request() {
    let mut w = world(9, 3);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let a = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.receive(&w.vtc, a).unwrap();
    let c = w.vtc.challenge(&mut w.rng);
    let sub = bob.submit(&w.vtc, &c, &mut w.rng).unwrap();

    w.vtc.rotate("2026-10", &mut w.rng).unwrap();
    w.vtc.drop_period("2026-09").unwrap();
    assert_eq!(
        w.vtc.submit(&sub, now()).err(),
        Some(ProtoError::PeriodNotLive("2026-09".into()))
    );
    // The current period cannot be dropped: rotate first.
    assert_eq!(
        w.vtc.drop_period("2026-10").err(),
        Some(ProtoError::DropsCurrentPeriod("2026-10".into()))
    );
}

#[test]
fn a_member_holds_one_credential_per_period() {
    let mut w = world(10, 1);
    // Enrolling again under the same period is refused, and so is a second engine (a twin key)
    // for the same member.
    assert!(matches!(
        w.vetters[0].enroll(&mut w.vtc, &mut w.rng),
        Err(ProtoError::AlreadyIssued { .. })
    ));
    let mut twin = VetterEngine::new("member-0");
    assert!(matches!(
        twin.enroll(&mut w.vtc, &mut w.rng),
        Err(ProtoError::AlreadyIssued { .. })
    ));
    // Under the next period, whichever engine enrols first holds the member's one credential.
    // The VTC does not link a member's identifiers across periods, and does not need to, as no
    // request spans two.
    w.vtc.rotate("2026-10", &mut w.rng).unwrap();
    twin.enroll(&mut w.vtc, &mut w.rng).unwrap();
    assert!(matches!(
        w.vetters[0].enroll(&mut w.vtc, &mut w.rng),
        Err(ProtoError::AlreadyIssued { .. })
    ));
    // Without a grant there is no credential.
    let mut stranger = VetterEngine::new("member-9");
    assert_eq!(
        stranger.enroll(&mut w.vtc, &mut w.rng).err(),
        Some(ProtoError::NotAVetter("member-9".into()))
    );

    // A removed vetter keeps its credential of a live period until that period leaves the
    // window, gets nothing under the next period, and cannot attest at all once the period is
    // dropped.
    let label = w.vtc.current_token_label().to_string();
    twin.drip(&mut w.vtc, 31, &label, R, &mut w.rng).unwrap();
    let carol = ApplicantEngine::new(&w.vtc, "did:example:carol", &mut w.rng).unwrap();
    let early = carol
        .vetting_request(&w.vtc, "member-0", &mut w.rng)
        .unwrap();
    let late = carol
        .vetting_request(&w.vtc, "member-0", &mut w.rng)
        .unwrap();
    w.vtc.revoke("member-0");
    w.vtc.rotate("2026-11", &mut w.rng).unwrap();
    assert_eq!(
        twin.enroll(&mut w.vtc, &mut w.rng).err(),
        Some(ProtoError::NotAVetter("member-0".into()))
    );
    let r = twin.accept(None, 32).unwrap();
    let m = meta(&carol, &w.vtc, VettingMethod::InPerson);
    twin.attest(&w.vtc, &r, &early, m.clone(), &mut w.rng)
        .unwrap();
    w.vtc.drop_period("2026-10").unwrap();
    let r = twin.accept(None, 32).unwrap();
    assert_eq!(
        twin.attest(&w.vtc, &r, &late, m, &mut w.rng).err(),
        Some(ProtoError::PeriodNotLive("2026-10".into()))
    );
}

#[test]
fn withdrawal_by_tag_stops_counting_and_cannot_be_forged() {
    let mut w = world(11, 3);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let a = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.receive(&w.vtc, a).unwrap();
    let b = vet(&mut w, 1, &bob, VettingMethod::Video);
    let b_tag = b.attestation.tag;
    bob.receive(&w.vtc, b).unwrap();
    assert!(submit(&mut w, &bob).unwrap().evaluation.satisfied());

    // Vetter 2 cannot withdraw vetter 1's statement: its proof is for its own tag.
    let period = bob.period().to_string();
    let (tag2, proof2) = w.vetters[2]
        .withdraw(&w.vtc, &period, bob.id(), &mut w.rng)
        .unwrap();
    let (tag1, proof1) = w.vetters[1]
        .withdraw(&w.vtc, &period, bob.id(), &mut w.rng)
        .unwrap();
    assert_eq!(tag1, b_tag, "the withdrawal names the statement's own tag");
    assert!(!w.vtc.withdraw(&period, bob.id(), &tag1, &proof2).unwrap());
    assert!(!w.vtc.withdraw(&period, bob.id(), &tag2, &proof1).unwrap() || tag1 == tag2);

    // Vetter 1 withdraws its own: no identity in the notice, only the tag and the proof.
    assert!(w.vtc.withdraw(&period, bob.id(), &tag1, &proof1).unwrap());
    let d = w.vtc.evaluate(&point_text(bob.id()).unwrap(), now());
    assert!(!d.evaluation.satisfied());
    assert!(
        d.statements
            .iter()
            .any(|s| s.revoked && s.failures.contains(&"revoked".to_string()))
    );
}

#[test]
fn drip_is_once_per_tick_and_reservations_bound_capacity() {
    let mut w = world(12, 1);
    let label = w.vtc.current_token_label().to_string();
    // A second fetch in the same tick is refused.
    assert!(matches!(
        w.vetters[0].drip(&mut w.vtc, 1, &label, R, &mut w.rng),
        Err(ProtoError::AlreadyServedThisTick { .. })
    ));
    // R tokens: R reservations, then atCapacity until the next tick.
    let rs: Vec<_> = (0..R)
        .map(|_| w.vetters[0].accept(None, 2).unwrap())
        .collect();
    assert_eq!(
        w.vetters[0].accept(None, 2).err(),
        Some(ProtoError::AtCapacity { available_from: 2 })
    );
    // A decline releases the token.
    w.vetters[0].decline(&rs[0]);
    assert!(w.vetters[0].accept(None, 2).is_ok());
    w.vetters[0]
        .drip(&mut w.vtc, 2, &label, R, &mut w.rng)
        .unwrap();
    assert_eq!(w.vetters[0].tokens_held(), 2 * R);

    // A personal limit below the drip: local, never sent, still refuses.
    let mut w = world(13, 1);
    w.vetters[0].personal_limit = Some(1);
    let bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    vet(&mut w, 0, &bob, VettingMethod::InPerson);
    assert!(w.vetters[0].tokens_free() > 0);
    assert!(matches!(
        w.vetters[0].accept(None, 2),
        Err(ProtoError::AtCapacity { .. })
    ));
}

#[test]
fn opening_proofs_are_bound_to_their_request() {
    let mut w = world(14, 1);
    let label = w.vtc.current_token_label().to_string();
    let tvk = w.vtc.tokens.tvk(&label).unwrap().clone();
    let mut wallet = TokenWallet::new();
    // Proofs made for tick 5, presented for tick 6.
    let reqs = wallet
        .prepare(&tvk, &label, "member-0", 5, 2, &mut w.rng)
        .unwrap();
    assert_eq!(
        w.vtc.drip("member-0", 6, &label, &reqs, &mut w.rng).err(),
        Some(ProtoError::BadOpeningProof(0))
    );
    // ... or by another member.
    w.vtc.grant("member-7");
    assert_eq!(
        w.vtc.drip("member-7", 5, &label, &reqs, &mut w.rng).err(),
        Some(ProtoError::BadOpeningProof(0))
    );
}

#[test]
fn event_mode_needs_a_group_an_outside_approver_and_dies_after_the_event() {
    let mut w = world(15, 4);
    let members = ["member-0", "member-1", "member-2"];
    assert!(matches!(
        w.vtc
            .approve_event("summit", &members[..2], "admin", 3, &mut w.rng),
        Err(ProtoError::EventRefused(_))
    ));
    assert!(matches!(
        w.vtc
            .approve_event("summit", &members, "member-0", 3, &mut w.rng),
        Err(ProtoError::EventRefused(_))
    ));
    let event = w
        .vtc
        .approve_event("summit", &members, "admin", 3, &mut w.rng)
        .unwrap();

    // Outside the group: refused. Inside: served.
    assert!(matches!(
        w.vetters[3].drip(&mut w.vtc, 2, &event, 20, &mut w.rng),
        Err(ProtoError::EventRefused(_))
    ));
    w.vetters[0]
        .drip(&mut w.vtc, 2, &event, 20, &mut w.rng)
        .unwrap();
    w.vetters[1]
        .drip(&mut w.vtc, 2, &event, 20, &mut w.rng)
        .unwrap();

    // Event tokens are preferred during the event and verify like any other.
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    for (j, method) in [(0, VettingMethod::InPerson), (1, VettingMethod::Video)] {
        let m = meta(&bob, &w.vtc, method);
        let request = bob
            .vetting_request(&w.vtc, &w.vetters[j].member, &mut w.rng)
            .unwrap();
        let r = w.vetters[j].accept(Some(&event), 3).unwrap();
        assert_eq!(r.label, event);
        let att = w.vetters[j]
            .attest(&w.vtc, &r, &request, m, &mut w.rng)
            .unwrap();
        bob.receive(&w.vtc, att).unwrap();
    }
    let c = w.vtc.challenge(&mut w.rng);
    let late = bob.submit(&w.vtc, &c, &mut w.rng).unwrap();
    assert!(submit(&mut w, &bob).unwrap().evaluation.satisfied());

    // After the grace period the event label closes: 19 leftover event tokens are gone, the
    // monthly drip (R, untouched) remains.
    assert_eq!(w.vetters[0].tokens_held(), R + 19);
    w.vtc.close_event("summit");
    w.vetters[0].expire(&w.vtc);
    assert_eq!(w.vetters[0].tokens_held(), R);
    // A submission prepared under the event (its challenge `c` still unused) now fails on the
    // closed label: every statement is `no-token`, nothing counts.
    let d = w.vtc.submit(&late, now()).unwrap();
    assert_eq!(d.evaluation.distinct_vetters(), 0);
    assert!(
        d.statements
            .iter()
            .all(|s| s.failures.contains(&"no-token".to_string()))
    );
}

// --- review fixes (PR #5) ------------------------------------------------------------------

#[test]
fn a_root_request_is_bound_to_the_member_that_submits_it() {
    use pcs_vetting_prototype::vtc::enrolment_ssid;
    let mut w = world(20, 0);
    w.vtc.grant("member-a");
    w.vtc.grant("member-b");
    // Member A's root request, captured by member B and submitted as B's.
    let period = w.vtc.current_period().to_string();
    let hvk = w.vtc.hvk(&period).unwrap().clone();
    let user = w.vtc.pcreds().register(&hvk, &mut w.rng).unwrap();
    let ssid = enrolment_ssid(COMMUNITY, "member-a", &period);
    let (message, _) = w
        .vtc
        .pcreds()
        .request_credential(&hvk, &user, Vec::new(), &ssid, &mut w.rng)
        .unwrap();
    assert!(
        w.vtc
            .issue_vetter_root("member-b", &period, &message, &mut w.rng)
            .is_err()
    );
    // A is not locked out, and B can still enrol for itself.
    VetterEngine::new("member-a")
        .enroll(&mut w.vtc, &mut w.rng)
        .unwrap();
    VetterEngine::new("member-b")
        .enroll(&mut w.vtc, &mut w.rng)
        .unwrap();
}

#[test]
fn rotate_refuses_a_live_period_name() {
    let mut w = world(21, 0);
    assert_eq!(
        w.vtc.rotate("2026-09", &mut w.rng).err(),
        Some(ProtoError::PeriodExists("2026-09".into()))
    );
    w.vtc.rotate("2026-10", &mut w.rng).unwrap();
    assert_eq!(
        w.vtc.rotate("2026-09", &mut w.rng).err(),
        Some(ProtoError::PeriodExists("2026-09".into()))
    );
    assert_eq!(w.vtc.live_periods(), vec!["2026-10", "2026-09"]);
}

#[test]
fn a_request_over_the_attestation_limit_is_refused_before_verification() {
    use pcs_vetting_prototype::vtc::MAX_ATTESTATIONS;
    let mut w = world(22, 1);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let a = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bob.receive(&w.vtc, a.clone()).unwrap();
    let many: Vec<&HiddenAttestation> = std::iter::repeat_n(&a, MAX_ATTESTATIONS + 1).collect();
    let c = w.vtc.challenge(&mut w.rng);
    let sub = bob
        .submit_attestations(&w.vtc, &c, &many, &mut w.rng)
        .unwrap();
    assert_eq!(
        w.vtc.submit(&sub, now()).err(),
        Some(ProtoError::TooManyAttestations {
            count: MAX_ATTESTATIONS + 1,
            max: MAX_ATTESTATIONS,
        })
    );
}

#[test]
fn an_ineligible_statement_does_not_burn_its_token() {
    let mut w = world(23, 2);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    // An expired statement: verified, but not eligible.
    let mut m = meta(&bob, &w.vtc, VettingMethod::InPerson);
    m.valid_until = NaiveDate::from_ymd_opt(2026, 9, 21).unwrap();
    let request = bob.vetting_request(&w.vtc, "member-0", &mut w.rng).unwrap();
    let r = w.vetters[0].accept(None, 2).unwrap();
    let expired = w.vetters[0]
        .attest(&w.vtc, &r, &request, m, &mut w.rng)
        .unwrap();
    let token = expired.token.clone();
    bob.receive(&w.vtc, expired).unwrap();
    let d = submit(&mut w, &bob).unwrap();
    assert!(d.statements[0].failures.contains(&"expired".to_string()));
    assert!(!d.statements[0].eligible);

    // The corrected statement on the same token counts, and the VTC logs no anomaly.
    let mut carol = ApplicantEngine::new(&w.vtc, "did:example:carol", &mut w.rng).unwrap();
    let m = meta(&carol, &w.vtc, VettingMethod::InPerson);
    let request = carol
        .vetting_request(&w.vtc, "member-0", &mut w.rng)
        .unwrap();
    let corrected = w.vetters[0]
        .attest_with_token(&w.vtc, token, &request, m, &mut w.rng)
        .unwrap();
    carol.receive(&w.vtc, corrected).unwrap();
    let d = submit(&mut w, &carol).unwrap();
    assert!(d.statements[0].eligible, "{:?}", d.statements[0].failures);
    assert!(w.vtc.tokens.anomalies.is_empty());
}

#[test]
fn a_failed_replacement_keeps_the_old_attestation() {
    let mut w = world(24, 1);
    let mut bob = ApplicantEngine::new(&w.vtc, "did:example:bob", &mut w.rng).unwrap();
    let first = vet(&mut w, 0, &bob, VettingMethod::Video);
    bob.receive(&w.vtc, first).unwrap();
    // A refresh whose metadata no longer matches what was attested fails verification.
    let mut bad = vet(&mut w, 0, &bob, VettingMethod::InPerson);
    bad.meta.method = VettingMethod::Video;
    assert!(matches!(
        bob.replace(&w.vtc, bad),
        Err(ProtoError::AttestationRejected(_))
    ));
    assert_eq!(bob.held(), 1);
}
