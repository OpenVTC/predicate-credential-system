//! A CHEATING PROVER at the lattice instantiation: real Jali proofs, made with the backend's
//! public associated functions ([`LatticeBackend`] as a [`Backend`]) for statements and
//! contexts that the honest protocol would not choose, and the protocol's verdict on each.
//!
//! * a proof made under the context of another role, another helper key or another sub-session;
//! * a proof of one role presented in another (an attestation proof as a membership proof, and
//!   the other way round, and an identifier proof as an attestation proof);
//! * an attestation for another requester, or under another helper key, in a request;
//! * one source attesting twice (fresh coins, one tag), and a member attesting for itself.
//!
//! Heavy (Jali proofs of seconds each); run in release:
//!
//! ```text
//! RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_attacks -- --ignored
//! ```
#![cfg(feature = "lattice")]

mod lattice_support;

use lattice_support::{Bk, Deployment};
use predicate_credential_system::{
    Error,
    pcreds::{
        Attestation, AttestationStatement, Backend, Decision, MembershipProof, Policy, Reply,
        lattice::LatticeBackend,
    },
};

/// An attestation proof whose statement is right but whose context is that of another role,
/// another key or another session, and proofs presented in a role they were not made for: each
/// is refused.
#[test]
#[ignore = "heavy: four R_att proofs and their verifications (run in release with --ignored)"]
fn proofs_under_wrong_contexts_and_roles_are_refused() {
    let mut d = Deployment::new(b"lattice-attacks/contexts", 1, 1, 0xa7_0001);
    let alice = d.register();
    let xq = d.pcreds.recipient_point(d.hvk.vk(), alice.id()).unwrap();
    let member = &d.members[0];
    let usk = member.user.expose_key();
    let tag = LatticeBackend::tag(d.pcreds.params(), usk, &xq).unwrap();
    let statement = AttestationStatement {
        vk: d.hvk.vk(),
        tag: &tag,
        point: &xq,
    };
    let other_helper = d
        .pcreds
        .helper_keygen(Policy::threshold(1).unwrap(), &mut d.rng);
    let wrong_contexts = [
        // the context of π_prove on a message, of π_iss, of π_id
        d.pcreds.prove_context(d.hvk.vk(), b"m").unwrap(),
        d.pcreds.issuance_context(d.hvk.vk(), b"ssid", &[]).unwrap(),
        d.pcreds.identifier_context(b"ssid", b"contact"),
        // the attestation context of another helper key
        d.pcreds
            .attestation_context(other_helper.key().vk())
            .unwrap(),
    ];
    for ctx in wrong_contexts {
        let ((), proof) = LatticeBackend::prove_attestation(
            d.pcreds.params(),
            &statement,
            usk,
            member.cred.as_inner(),
            &ctx,
            &mut d.rng,
        )
        .unwrap();
        // it verifies under the context it was made for, and is refused by the protocol
        assert_eq!(
            LatticeBackend::check_attestation_proof(
                d.pcreds.params(),
                &statement,
                &(),
                &ctx,
                &proof
            ),
            Ok(())
        );
        let att = Attestation::<Bk> {
            tag: tag.clone(),
            show: (),
            proof,
        };
        assert_eq!(
            d.pcreds.check_attestation(&d.hvk, alice.id(), &att),
            Err(Error::InvalidProof)
        );
    }

    // an honest attestation proof presented as a membership proof, and the other way round
    let att = d.attestation(0, &alice);
    let as_membership = MembershipProof::<Bk> {
        show: (),
        proof: att.proof.clone(),
    };
    assert_eq!(
        d.pcreds.check_membership(&d.hvk, b"m", &as_membership),
        Err(Error::InvalidProof)
    );
    let member = &d.members[0];
    let membership = d
        .pcreds
        .prove(&d.hvk, &member.user, &member.cred, b"m", &mut d.rng)
        .unwrap();
    let as_attestation = Attestation::<Bk> {
        tag: att.tag.clone(),
        show: (),
        proof: membership.proof,
    };
    assert_eq!(
        d.pcreds
            .check_attestation(&d.hvk, alice.id(), &as_attestation),
        Err(Error::InvalidProof)
    );
    // an identifier proof of alice as an attestation proof for alice
    let request = d
        .pcreds
        .request_attestation(&d.hvk, &alice, b"s", b"c", &mut d.rng)
        .unwrap();
    let as_attestation = Attestation::<Bk> {
        tag: att.tag,
        show: (),
        proof: request.proof,
    };
    assert_eq!(
        d.pcreds
            .check_attestation(&d.hvk, alice.id(), &as_attestation),
        Err(Error::InvalidProof)
    );
}

/// What a request may carry that does not count: an attestation for another requester, one
/// under another helper key, a second attestation of one source.
#[test]
#[ignore = "heavy: six attestations and three evaluations (run in release with --ignored)"]
fn attestations_that_do_not_count() {
    let mut d = Deployment::new(b"lattice-attacks/count", 2, 2, 0xa7_0002);
    let alice = d.register();
    let bob = d.register();
    // member 0 for alice, member 1 for bob: in alice's request, bob's does not count
    let for_alice = d.attestation(0, &alice);
    let for_bob = d.attestation(1, &bob);
    let (message, _, ssid) = d.request(&alice, vec![for_alice.clone(), for_bob]);
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &message, &ssid)
        .unwrap();
    assert_eq!(evaluated.tags(), std::slice::from_ref(&for_alice.tag));
    assert!(!evaluated.is_valid());
    // member 0 twice, with fresh coins: one tag, counted once
    let again = d.attestation(0, &alice);
    assert_eq!(again.tag, for_alice.tag);
    let (message, _, ssid) = d.request(&alice, vec![for_alice.clone(), again]);
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &message, &ssid)
        .unwrap();
    assert_eq!(evaluated.tags().len(), 1);
    assert!(!evaluated.is_valid());
    // a member of another helper attests under that helper's key: not under this one. Alice
    // registers with that helper too (her key reused, another identifier there)
    let mut other = Deployment::new(b"lattice-attacks/count", 1, 1, 0xa7_0003);
    let alice_there = other.pcreds.register_reusing(&other.hvk, &alice).unwrap();
    assert_ne!(alice_there.id(), alice.id());
    let ssid_att = other.ssid();
    let request = other
        .pcreds
        .request_attestation(&other.hvk, &alice_there, &ssid_att, b"c", &mut other.rng)
        .unwrap();
    let pending = other
        .pcreds
        .receive_attestation_request(&other.hvk, &request, &ssid_att, b"c")
        .unwrap();
    let member = &other.members[0];
    let foreign = other
        .pcreds
        .attest(
            &other.hvk,
            &member.user,
            &member.cred,
            pending,
            &mut other.rng,
        )
        .unwrap();
    assert_eq!(
        d.pcreds.check_attestation(&d.hvk, alice.id(), &foreign),
        Err(Error::InvalidProof)
    );
}

/// A member's own attestation in its own request: the helper evaluates it like any other, and
/// answers `issued`, because the member's identifier was issued to.
#[test]
#[ignore = "heavy: two attestations and one evaluation (run in release with --ignored)"]
fn a_member_attesting_for_itself_is_answered_issued() {
    let mut d = Deployment::new(b"lattice-attacks/self", 2, 2, 0xa7_0004);
    let ssid = d.ssid();
    let request = d
        .pcreds
        .request_attestation(&d.hvk, &d.members[0].user, &ssid, b"self", &mut d.rng)
        .unwrap();
    let pending = d
        .pcreds
        .receive_attestation_request(&d.hvk, &request, &ssid, b"self")
        .unwrap();
    let member = &d.members[0];
    let own = d
        .pcreds
        .attest(&d.hvk, &member.user, &member.cred, pending, &mut d.rng)
        .unwrap();
    let user = &d.members[0].user;
    let other = {
        let ssid = format!("other-{}", 1).into_bytes();
        let request = d
            .pcreds
            .request_attestation(&d.hvk, user, &ssid, b"c", &mut d.rng)
            .unwrap();
        let pending = d
            .pcreds
            .receive_attestation_request(&d.hvk, &request, &ssid, b"c")
            .unwrap();
        let m = &d.members[1];
        d.pcreds
            .attest(&d.hvk, &m.user, &m.cred, pending, &mut d.rng)
            .unwrap()
    };
    let ssid = b"self-request".to_vec();
    let (message, _state) = d
        .pcreds
        .request_credential(&d.hvk, user, vec![own, other], &ssid, &mut d.rng)
        .unwrap();
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &message, &ssid)
        .unwrap();
    assert_eq!(evaluated.tags().len(), 2);
    assert!(evaluated.is_valid());
    assert_eq!(
        d.pcreds
            .respond(&mut d.helper, evaluated, Decision::Policy, &mut d.rng)
            .unwrap(),
        Reply::Issued
    );
}
