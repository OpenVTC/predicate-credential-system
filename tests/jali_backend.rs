//! The `jali` feature: the standalone lattice zero-knowledge library is reachable through the
//! re-export `predicate_credential_system::jali` and proves and verifies a commitment opening.
//! Seeds are fixed test fixtures; this checks the wiring, not the lattice protocols themselves,
//! which Jali's own test suite covers.

use predicate_credential_system::jali::{
    abdlop::Abdlop,
    math::{Poly, PolyVec},
    params::toy_d64,
};

#[test]
fn jali_backend_proves_and_verifies_a_commitment_opening() {
    let scheme = Abdlop::new([1; 32], toy_d64()).unwrap();
    let ring = scheme.ring().clone();
    let bounded = PolyVec::new(
        ring.clone(),
        vec![Poly::constant(ring.clone(), 1); scheme.bounded_len()],
    )
    .unwrap();
    let messages = PolyVec::zero(ring, scheme.message_len());
    let (commitment, opening) = scheme.commit_with_seed(bounded, messages, [2; 32]).unwrap();
    let proof = scheme
        .prove_with_seed(&commitment, &opening, b"pcs/jali-backend", [3; 32])
        .unwrap();
    let bytes = scheme.encode_proof(&proof).unwrap();
    let decoded = scheme.decode_proof(&bytes).unwrap();
    scheme
        .verify(&commitment, &decoded, b"pcs/jali-backend")
        .unwrap();
    assert!(
        scheme
            .verify(&commitment, &decoded, b"pcs/another-context")
            .is_err()
    );
}
