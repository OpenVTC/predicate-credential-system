//! The main flows of `Π_PCreds` at the lattice instantiation, end to end through the public API:
//! root admission, issuance under `Pol_k` with `k` attestations, chaining (a newcomer attests for
//! the next one), membership proofs, and the helper's answers `Fail` and `issued`.
//!
//! Heavy: every attestation is a Jali proof of seconds and up to about 0.7 GB. Run in release:
//!
//! ```text
//! RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_flows -- --ignored --nocapture
//! ```
#![cfg(feature = "lattice")]

mod lattice_support;

use lattice_support::{Deployment, Member, timed};
use predicate_credential_system::{
    Error,
    pcreds::{Decision, IssuanceState},
    serialization::WireFormat,
};

/// `Pol_3` with three roots: a newcomer with three attestations is issued; the newcomer attests,
/// with two roots, for a second newcomer (chaining); both prove membership on messages; a
/// request with two valid attestations is answered `Fail` (and `issued` under `d = root`); a
/// second request of an issued identifier is answered `issued`; a request whose attestations
/// repeat one source counts it once.
#[test]
#[ignore = "heavy: about 2 minutes in release (cargo test --release --features lattice --test lattice_flows -- --ignored)"]
fn main_flow_k3() {
    let mut d = timed("setup and three root admissions", || {
        Deployment::new(b"lattice-flows/k3", 3, 3, 0xf10_0003)
    });
    // a newcomer with three attestations
    let alice = timed("a newcomer with three attestations", || d.newcomer(3));
    assert!(d.pcreds.verify_credential(&d.hvk, &alice.user, &alice.cred));
    assert_eq!(d.helper.store().len(), 4);

    // chaining: alice and two roots attest for bob
    let bob = d.register();
    let mut attestations = vec![d.attestation(0, &bob), d.attestation(1, &bob)];
    let ssid = d.ssid();
    let contact = b"alice@example".to_vec();
    let request = d
        .pcreds
        .request_attestation(&d.hvk, &bob, &ssid, &contact, &mut d.rng)
        .unwrap();
    let pending = d
        .pcreds
        .receive_attestation_request(&d.hvk, &request, &ssid, &contact)
        .unwrap();
    attestations.push(
        d.pcreds
            .attest(&d.hvk, &alice.user, &alice.cred, pending, &mut d.rng)
            .unwrap(),
    );
    for att in &attestations {
        d.pcreds.check_attestation(&d.hvk, bob.id(), att).unwrap();
    }
    let (message, state, ssid) = d.request(&bob, attestations.clone());
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &message, &ssid)
        .unwrap();
    assert!(evaluated.is_valid());
    assert_eq!(evaluated.tags().len(), 3);
    let bob_cred = d
        .answer(&bob, &message, state, &ssid, Decision::Policy)
        .unwrap()
        .credential();
    let bob = Member {
        user: bob,
        cred: bob_cred,
    };

    // membership proofs
    for (member, m) in [(&alice, &b"from alice"[..]), (&bob, &b"from bob"[..])] {
        let proof = d
            .pcreds
            .prove(&d.hvk, &member.user, &member.cred, m, &mut d.rng)
            .unwrap();
        assert!(d.pcreds.verify(&d.hvk, m, &proof));
        assert_eq!(
            d.pcreds
                .check_membership(&d.hvk, b"another message", &proof),
            Err(Error::InvalidProof)
        );
    }

    // two valid attestations of three: Fail, unless the helper admits the requester as a root
    let carol = d.register();
    let two = d.attestations(&carol, 2);
    let (message, state, ssid) = d.request(&carol, two);
    // the requester keeps its state until a credential arrives (it is consumed by each answer)
    let stored = state.to_bytes().unwrap();
    assert!(
        d.answer(&carol, &message, state, &ssid, Decision::Policy)
            .unwrap()
            .is_fail()
    );
    assert!(
        d.pcreds
            .evaluate_request(&d.helper, &message, &ssid)
            .map(|e| !e.is_valid())
            .unwrap()
    );
    let state = IssuanceState::from_bytes(&stored).unwrap();
    let carol_cred = d
        .answer(&carol, &message, state, &ssid, Decision::Root)
        .unwrap()
        .credential();
    assert!(d.pcreds.verify_credential(&d.hvk, &carol, &carol_cred));

    // an issued identifier: issued, whatever the request carries
    let (message, state, ssid) = d.request(&alice.user, Vec::new());
    assert!(
        d.answer(&alice.user, &message, state, &ssid, Decision::Root)
            .unwrap()
            .is_issued()
    );

    // one source twice counts once: three attestations from two sources do not meet Pol_3
    let dave = d.register();
    let repeated = vec![
        d.attestation(0, &dave),
        d.attestation(0, &dave),
        d.attestation(1, &dave),
    ];
    assert_eq!(
        repeated[0].tag, repeated[1].tag,
        "one source, one tag per recipient"
    );
    assert_ne!(repeated[0].proof, repeated[1].proof, "fresh coins");
    let (message, _, ssid) = d.request(&dave, repeated);
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &message, &ssid)
        .unwrap();
    assert_eq!(evaluated.tags().len(), 2);
    assert!(!evaluated.is_valid());
}
