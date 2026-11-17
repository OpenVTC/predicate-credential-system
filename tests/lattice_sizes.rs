//! The sizes of the messages of `Π_PCreds` at the lattice instantiation, measured on real
//! proofs (they vary by tens of bytes with the proof seed): the identifier proof, an attestation,
//! a credential request at `k = 5` (the `|π|` of the paper's size table: the attestations, `Ĉ`
//! and `π_iss`), a membership proof, and the pre-credential. Prints a table; the bounds of
//! `lattice::sets` hold for every proof.
//!
//! ```text
//! RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_sizes -- --ignored --nocapture
//! ```
//!
//! It measures the build it runs in: the default extractable one, whose proofs carry the LinHC
//! part, or with `--features lattice-plain` the plain one.
#![cfg(feature = "lattice")]

mod lattice_support;

use lattice_support::{Bk, Deployment, timed};
use predicate_credential_system::{
    lattice::sets::{
        ATT_PROOF_MAX_BYTES, ISS_PROOF_MAX_BYTES, POSSESS_PROOF_MAX_BYTES, TAG_PROOF_MAX_BYTES,
    },
    pcreds::{Decision, Reply},
};

#[test]
#[ignore = "measurement: five root admissions, five attestations and a k = 5 request (about 2 minutes in release)"]
fn sizes_at_k5() {
    let mut d = timed("setup and five root admissions", || {
        Deployment::new(b"lattice-sizes/k5", 5, 5, 0x512e_0005)
    });
    let alice = d.register();
    let request = d
        .pcreds
        .request_attestation(&d.hvk, &alice, b"ssid", b"member-0@example", &mut d.rng)
        .unwrap();
    let attestations = timed("five attestations", || d.attestations(&alice, 5));
    let (message, _state, ssid) = timed("the credential request", || {
        d.request(&alice, attestations.clone())
    });
    let evaluated = timed("its evaluation", || {
        d.pcreds
            .evaluate_request(&d.helper, &message, &ssid)
            .unwrap()
    });
    assert!(evaluated.is_valid());
    let Reply::PreCredential(pre) = d
        .pcreds
        .respond(&mut d.helper, evaluated, Decision::Policy, &mut d.rng)
        .unwrap()
    else {
        panic!("issued")
    };
    let member = &d.members[0];
    let proof = d
        .pcreds
        .prove(&d.hvk, &member.user, &member.cred, b"m", &mut d.rng)
        .unwrap();

    assert!(request.proof.len() <= TAG_PROOF_MAX_BYTES);
    assert!(
        attestations
            .iter()
            .all(|a| a.proof.len() <= ATT_PROOF_MAX_BYTES)
    );
    assert!(message.proof.len() <= ISS_PROOF_MAX_BYTES);
    assert!(proof.proof.len() <= POSSESS_PROOF_MAX_BYTES);
    let reply = Reply::<Bk>::PreCredential(pre).to_compact_bytes().unwrap();
    println!("| object | bytes |");
    println!("|---|---|");
    println!(
        "| attestation request (id_Q ‖ π_id) | {} |",
        request.compact_size()
    );
    for (j, att) in attestations.iter().enumerate() {
        println!("| attestation {j} (t ‖ π_att) | {} |", att.size());
    }
    println!(
        "| |π| at k = 5 (attestations, Ĉ, π_iss) | {} |",
        message.size()
    );
    println!(
        "| credential request on the wire | {} |",
        message.compact_size()
    );
    println!("| reply with σ̂ | {} |", reply.len());
    println!("| membership proof (π_prove) | {} |", proof.size());
}
