//! Tampered and misdirected messages at the lattice instantiation: every verifier of the
//! protocol refuses them, with the documented reason.
//!
//! * an attestation with another tag, proof bytes that are flipped, truncated or extended,
//!   checked for another requester, under another helper key or in another deployment;
//! * a credential request with another `ssid`, another order or selection of attestations,
//!   another request `Ĉ` or another identifier;
//! * a membership proof on another message, under another key, or with flipped bytes;
//! * an identifier proof for another sub-session, contact or identifier.
//!
//! Heavy (Jali verifications of seconds each); run in release:
//!
//! ```text
//! RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_adversarial -- --ignored
//! ```
#![cfg(feature = "lattice")]

mod lattice_support;

use lattice_support::{Bk, Deployment};
use predicate_credential_system::{
    Error,
    lattice::{Rq, Ternary},
    pcreds::{
        Attestation, AttestationRequest, CredentialRequest, MembershipProof, Policy,
        lattice::{LatticeProof, LatticeProtocol},
    },
};
use rand::{SeedableRng, rngs::StdRng};

/// `proof` with byte `i` flipped, truncated by one byte, and extended by one byte.
fn tampered(proof: &LatticeProof) -> Vec<LatticeProof> {
    let bytes = proof.as_bytes();
    let mut flipped = bytes.to_vec();
    flipped[bytes.len() / 2] ^= 1;
    let mut truncated = bytes.to_vec();
    truncated.pop();
    let mut extended = bytes.to_vec();
    extended.push(0);
    [flipped, truncated, extended]
        .into_iter()
        .map(|b| LatticeProof::from_bytes(b).unwrap())
        .collect()
}

#[test]
#[ignore = "heavy: one attestation and eight R_att verifications (run in release with --ignored)"]
fn tampered_attestations_are_refused() {
    let mut d = Deployment::new(b"lattice-adversarial/att", 1, 1, 0xad_0001);
    let alice = d.register();
    let att = d.attestation(0, &alice);
    d.pcreds
        .check_attestation(&d.hvk, alice.id(), &att)
        .unwrap();
    // another (valid) tag: the tag of the same member at another requester's point
    let bob = d.register();
    let bob_att = d.attestation(0, &bob);
    let swapped = Attestation::<Bk> {
        tag: bob_att.tag.clone(),
        ..att.clone()
    };
    assert_eq!(
        d.pcreds.check_attestation(&d.hvk, alice.id(), &swapped),
        Err(Error::InvalidProof)
    );
    // flipped, truncated, extended proof bytes
    for proof in tampered(&att.proof) {
        let bad = Attestation::<Bk> {
            proof,
            ..att.clone()
        };
        assert_eq!(
            d.pcreds.check_attestation(&d.hvk, alice.id(), &bad),
            Err(Error::InvalidProof)
        );
    }
    // for another requester: the recipient point differs
    assert_eq!(
        d.pcreds.check_attestation(&d.hvk, bob.id(), &att),
        Err(Error::InvalidProof)
    );
    // under another helper key, and in another deployment
    let other_helper = d
        .pcreds
        .helper_keygen(Policy::threshold(1).unwrap(), &mut d.rng);
    let other_hvk = d.pcreds.helper_key(other_helper.key().vk()).unwrap();
    assert_eq!(
        d.pcreds.check_attestation(&other_hvk, alice.id(), &att),
        Err(Error::InvalidProof)
    );
    let elsewhere = LatticeProtocol::setup(b"lattice-adversarial/elsewhere").unwrap();
    let hvk_elsewhere = elsewhere.helper_key(d.hvk.vk()).unwrap();
    assert_eq!(
        elsewhere.check_attestation(&hvk_elsewhere, alice.id(), &att),
        Err(Error::InvalidProof)
    );
    // a helper key of another deployment is refused before anything
    assert_eq!(
        d.pcreds.check_attestation(&hvk_elsewhere, alice.id(), &att),
        Err(Error::InvalidKey)
    );
}

#[test]
#[ignore = "heavy: two attestations, three R_iss proofs and their verifications (run in release with --ignored)"]
fn tampered_credential_requests_are_refused() {
    let mut d = Deployment::new(b"lattice-adversarial/iss", 2, 2, 0xad_0002);
    let alice = d.register();
    let attestations = d.attestations(&alice, 2);
    let (message, _state, ssid) = d.request(&alice, attestations.clone());
    assert!(
        d.pcreds
            .evaluate_request(&d.helper, &message, &ssid)
            .unwrap()
            .is_valid()
    );
    // another ssid: the context of π_iss differs
    assert_eq!(
        d.pcreds
            .evaluate_request(&d.helper, &message, b"another ssid")
            .unwrap_err(),
        Error::InvalidProof
    );
    // another order, another selection of the attestations: the context differs
    let mut reordered = message.clone();
    reordered.attestations.reverse();
    assert_eq!(
        d.pcreds
            .evaluate_request(&d.helper, &reordered, &ssid)
            .unwrap_err(),
        Error::InvalidProof
    );
    let mut dropped = message.clone();
    dropped.attestations.pop();
    assert_eq!(
        d.pcreds
            .evaluate_request(&d.helper, &dropped, &ssid)
            .unwrap_err(),
        Error::InvalidProof
    );
    // another request Ĉ (another user's), another identifier
    let bob = d.register();
    let (bob_message, _, _) = d.request(&bob, Vec::new());
    let swapped = CredentialRequest::<Bk> {
        request: bob_message.request.clone(),
        ..message.clone()
    };
    assert_eq!(
        d.pcreds
            .evaluate_request(&d.helper, &swapped, &ssid)
            .unwrap_err(),
        Error::InvalidProof
    );
    let renamed = CredentialRequest::<Bk> {
        id: bob.id().clone(),
        ..message.clone()
    };
    assert_eq!(
        d.pcreds
            .evaluate_request(&d.helper, &renamed, &ssid)
            .unwrap_err(),
        Error::InvalidProof
    );
    // a wiped request is no element of R_q
    let mut wiped = message.clone();
    wiped.request = {
        use zeroize::Zeroize;
        let mut c = Rq::one();
        c.zeroize();
        c
    };
    assert_eq!(
        d.pcreds
            .evaluate_request(&d.helper, &wiped, &ssid)
            .unwrap_err(),
        Error::InvalidIssuanceEncoding
    );
    // flipped proof bytes
    for proof in tampered(&message.proof) {
        let bad = CredentialRequest::<Bk> {
            proof,
            ..message.clone()
        };
        assert_eq!(
            d.pcreds
                .evaluate_request(&d.helper, &bad, &ssid)
                .unwrap_err(),
            Error::InvalidProof
        );
    }
}

#[test]
#[ignore = "heavy: one membership proof and six verifications (run in release with --ignored)"]
fn tampered_membership_proofs_and_identifier_proofs_are_refused() {
    let mut d = Deployment::new(b"lattice-adversarial/prove", 1, 1, 0xad_0003);
    let member = &d.members[0];
    let proof = d
        .pcreds
        .prove(&d.hvk, &member.user, &member.cred, b"m", &mut d.rng)
        .unwrap();
    assert!(d.pcreds.verify(&d.hvk, b"m", &proof));
    assert_eq!(
        d.pcreds.check_membership(&d.hvk, b"m'", &proof),
        Err(Error::InvalidProof)
    );
    for p in tampered(&proof.proof) {
        let bad = MembershipProof::<Bk> { show: (), proof: p };
        assert_eq!(
            d.pcreds.check_membership(&d.hvk, b"m", &bad),
            Err(Error::InvalidProof)
        );
    }
    let other_helper = d
        .pcreds
        .helper_keygen(Policy::threshold(1).unwrap(), &mut d.rng);
    let other_hvk = d.pcreds.helper_key(other_helper.key().vk()).unwrap();
    assert_eq!(
        d.pcreds.check_membership(&other_hvk, b"m", &proof),
        Err(Error::InvalidProof)
    );

    // π_id: another sub-session, contact or identifier
    let alice = d.register();
    let request = d
        .pcreds
        .request_attestation(&d.hvk, &alice, b"s", b"c", &mut d.rng)
        .unwrap();
    assert!(
        d.pcreds
            .verify_attestation_request(&d.hvk, &request, b"s", b"c")
    );
    assert!(
        !d.pcreds
            .verify_attestation_request(&d.hvk, &request, b"s'", b"c")
    );
    assert!(
        !d.pcreds
            .verify_attestation_request(&d.hvk, &request, b"s", b"c'")
    );
    let bob = d.register();
    let renamed = AttestationRequest::<Bk> {
        id: bob.id().clone(),
        proof: request.proof.clone(),
    };
    assert_eq!(
        d.pcreds
            .receive_attestation_request(&d.hvk, &renamed, b"s", b"c")
            .unwrap_err(),
        Error::InvalidProof
    );
}

/// The honest provers refuse what no verifier would accept, before any proof work: a
/// credential of another user, a credential under another key, a wiped credential.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "two root admissions: one R_iss proof each (run in release)"
)]
fn the_honest_provers_refuse_false_witnesses() {
    let mut rng = StdRng::seed_from_u64(0xad_0004);
    let mut d = Deployment::new(b"lattice-adversarial/witness", 1, 2, 0xad_0005);
    let (alice, bob) = (&d.members[0], &d.members[1]);
    // alice's key with bob's credential
    assert_eq!(
        d.pcreds
            .prove(&d.hvk, &alice.user, &bob.cred, b"m", &mut rng)
            .unwrap_err(),
        Error::WitnessDoesNotSatisfyRelation
    );
    // under another helper key
    let other = d
        .pcreds
        .helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let other_hvk = d.pcreds.helper_key(other.key().vk()).unwrap();
    // a user belongs to one helper key ...
    assert_eq!(
        d.pcreds
            .prove(&other_hvk, &alice.user, &alice.cred, b"m", &mut rng)
            .unwrap_err(),
        Error::IdentifierMismatch
    );
    // ... and with its key registered under the other one, its credential is none there
    let alice_there = d.pcreds.register_reusing(&other_hvk, &alice.user).unwrap();
    assert_eq!(
        d.pcreds
            .prove(&other_hvk, &alice_there, &alice.cred, b"m", &mut rng)
            .unwrap_err(),
        Error::WitnessDoesNotSatisfyRelation
    );
    // an attestation with another user's credential
    let carol = d.pcreds.register(&d.hvk, &mut rng).unwrap();
    let request = d
        .pcreds
        .request_attestation(&d.hvk, &carol, b"s", b"c", &mut rng)
        .unwrap();
    let pending = d
        .pcreds
        .receive_attestation_request(&d.hvk, &request, b"s", b"c")
        .unwrap();
    assert_eq!(
        d.pcreds
            .attest(&d.hvk, &alice.user, &bob.cred, pending, &mut rng)
            .unwrap_err(),
        Error::WitnessDoesNotSatisfyRelation
    );
    // a user that is not the key of its stored identifier cannot exist: `user` derives it
    let _ = d.pcreds.user(&d.hvk, Ternary::sample(&mut rng)).unwrap();
    let _ = &mut d.rng;
}
