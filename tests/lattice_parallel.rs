//! The `k` attestation verifications of `CheckAtts_P` in `LatticePCS` (feature `lattice`), which
//! `VerifyProof` (and so `Issue`) and `Prove` run in parallel with the feature `parallel` and one
//! after the other without it, with the same results. With ONE real helper key and real Jali
//! proofs, at `k = 3`:
//!
//! * a valid request is accepted (`VerifyProof`, `Issue`, `Unblind`, `VerifyCred`), also by a
//!   verifier whose policy is not `Sync` (a closure over an `Rc`);
//! * a request with exactly ONE invalid attestation, at the first, the middle or the last
//!   position, is refused with `InvalidAttestation` by `VerifyProof` and by `Prove`. Two kinds of
//!   invalid attestation: one made for ANOTHER recipient (a valid proof under another context and
//!   attester point) and an honest one with a proof byte flipped. `VerifyProof` reaches the
//!   attestation proofs only after a valid `π_0` over the list, which the honest `Prove` refuses
//!   to make, so the cheating prover of `lattice_support` (`Port`) proves `π_0` over each list, as
//!   in `lattice_attacks.rs`.
//!
//! With `parallel`, every `VerifyProof` verdict is also computed in rayon pools of 1, 2 and 3
//! threads, where the three verifications run in batches of 1 (one after the other), of 2 then 1,
//! and of 3: a failure is met in the first batch, in a later one or within the only one. The
//! verdicts are asserted to be the expected ones in every pool and in both builds; the tests
//! print them, with the time of each call. Heavy (`#[ignore]`); run them in release, once per
//! build, one test at a time:
//!
//! ```text
//! RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_parallel -- --include-ignored --nocapture
//! RUST_TEST_THREADS=1 cargo test --release --features lattice,parallel --test lattice_parallel -- --include-ignored --nocapture
//! ```
//!
//! The light test (no proof) runs in every `cargo test`: a policy that is not `Sync` still gives
//! a verifier, in both builds, and runs on the calling thread.
#![cfg(feature = "lattice")]
#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

mod lattice_support;

use std::{cell::Cell, fmt::Debug, rc::Rc, sync::OnceLock, time::Instant};

use lattice_support::*;
use predicate_credential_system::{
    Error, LatticePCS,
    cred::{VSIS, vsis::VSISVerificationKey},
    kiprf::lwr::{LWR, LWRTag},
    lattice::{BinaryPoly, D, M, Rq, Ternary},
    pcs::{
        AttributePolicy, HelperSecretKey, Predicate, PredicateCredentialSystem, SetupParams,
        lattice::{Attestation, IssuanceProof, IssuanceState, Proof},
    },
};
use rand::{SeedableRng, rngs::StdRng};

const LABEL: &[u8] = b"lattice-parallel";

/// The threshold: three attestations, so that an invalid one can be first, in the middle or last.
const K: u32 = 3;

/// One deployment, ONE helper key, the root members A, B and C, a recipient R with the honest
/// attestations A→R, B→R, C→R and an honest issuance proof for `f = f_3`, and two invalid
/// attestations for R: A→S, made for another recipient S, and A→R with a proof byte flipped.
struct Fixture {
    pcs: Pcs,
    hvk: VSISVerificationKey,
    hsk: HelperSecretKey<VSIS>,
    f: Predicate,
    port: Port,
    r: Member,
    atts: Vec<Attestation>,
    proof: IssuanceProof,
    state_bytes: Vec<u8>,
    foreign: Attestation,
    flipped: Attestation,
}

fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let t = Instant::now();
        let mut rng = StdRng::seed_from_u64(0x9a7a_11e1);
        let f_root = Predicate::root(b"founders".to_vec());
        let f = Predicate::new(K, b"members".to_vec());
        let pcs = deployment(LABEL, &[&f_root, &f]);
        let (hvk, hsk) = pcs.helper_keygen(&mut rng);
        let mut members = Vec::new();
        for name in ["A", "B", "C"] {
            let mut m = Member::new(&pcs, name, &mut rng);
            root_issue(&pcs, &hvk, &hsk, &mut m, &f_root, &mut rng);
            members.push(m);
        }
        let r = Member::new(&pcs, "R", &mut rng);
        let s = Member::new(&pcs, "S", &mut rng);
        let attest = |m: &Member, id: &LWRTag, rng: &mut StdRng| {
            pcs.attest(&hvk, &m.usk, m.f(), m.cred(), id, rng).unwrap()
        };
        let atts: Vec<Attestation> = members.iter().map(|m| attest(m, &r.id, &mut rng)).collect();
        let foreign = attest(&members[0], &s.id, &mut rng);
        let mut bytes = atts[0].proof.as_bytes().to_vec();
        let middle = bytes.len() / 2;
        bytes[middle] ^= 1;
        let flipped = Attestation {
            proof: Proof::from_bytes(bytes).unwrap(),
            ..atts[0].clone()
        };
        let (proof, state) = pcs.prove(&hvk, &f, &r.id, &r.usk, &atts, &mut rng).unwrap();
        println!("fixture: {:.1} s", secs(t));
        Fixture {
            port: Port::new(pcs.public_parameters()),
            state_bytes: state.to_bytes().unwrap().to_vec(),
            pcs,
            hvk,
            hsk,
            f,
            r,
            atts,
            proof,
            foreign,
            flipped,
        }
    })
}

impl Fixture {
    /// The cheating prover's request over `list`: R's honest `R_issue` statement with a fresh
    /// `x_0`, proven under `ctx_0` over `list` (it skips `CheckAtts_P`), checked by Jali.
    fn request_over(&self, list: &[Attestation], rng: &mut StdRng) -> IssuanceProof {
        let pp = self.pcs.public_parameters();
        let usk = self.r.usk.expose_ternary();
        let x0 = [Ternary::sample(rng), Ternary::sample(rng)];
        let c = commitment(&pp.pp_sigma, &usk.to_rq(), [&x0[0].to_rq(), &x0[1].to_rq()]);
        let (id, e0) = LWR.eval_with_error(usk, &pp.c0).unwrap();
        assert_eq!(id, self.r.id);
        let s = self.pcs.tag_point(&id);
        let (t0, e1) = LWR.eval_with_error(usk, &s).unwrap();
        let st = self
            .port
            .r_issue(&c, &tag_values(&id), &self.port.rows(&s), &tag_values(&t0));
        let w = self.port.issue_witness(
            &ints(usk),
            [&ints(&x0[0]), &ints(&x0[1])],
            e0.entries(),
            e1.entries(),
        );
        let set = &self.port.sets.issue;
        let ctx = self
            .pcs
            .issuance_context(&self.hvk, &self.f, &id, &c, &t0, list);
        let proof = self.port.prove(&st, set, &w, &ctx, rng).unwrap();
        assert_eq!(self.port.verify(&st, set, &proof, &ctx), Ok(()));
        IssuanceProof {
            attestations: list.to_vec(),
            c,
            t0,
            proof: Proof::from_bytes(proof).unwrap(),
        }
    }
}

/// The value of `f` on the calling thread (the default pool) and, with `parallel`, in rayon pools
/// of 1, 2 and 3 threads, which must all agree; prints the time of each call.
fn in_pools<T: PartialEq + Debug + Send>(what: &str, f: impl Fn() -> T + Sync) -> T {
    let t = Instant::now();
    let value = f();
    print!("  {what}: {value:?}; {:.2} s (default pool)", secs(t));
    #[cfg(feature = "parallel")]
    for threads in [1, 2, 3] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap();
        let t = Instant::now();
        let other = pool.install(&f);
        print!(", {:.2} s ({threads} threads)", secs(t));
        assert_eq!(other, value, "{what}: {threads} threads");
    }
    println!();
    value
}

/// A valid request at `k = 3` is accepted in every pool, the helper issues on it, and the
/// credential is real; a verifier whose policy is not `Sync` accepts it as well, and runs its
/// policy once.
#[test]
#[ignore = "heavy: the shared fixture (about 1 minute) and four to seven verifications of a k = 3 request (run in release)"]
fn a_valid_request_at_k3_is_accepted() {
    let fx = fixture();
    let (pcs, hvk, r) = (&fx.pcs, &fx.hvk, &fx.r);
    println!(
        "parallel attestation verification: {}",
        cfg!(feature = "parallel")
    );
    assert_eq!(
        in_pools("VerifyProof, valid", || pcs
            .check_proof(hvk, &fx.f, &r.id, &fx.proof)),
        Ok(())
    );
    assert!(pcs.verify_proof(hvk, &fx.f, &r.id, &fx.proof));
    let mut rng = StdRng::seed_from_u64(0x9a7a_11e2);
    let pre = pcs
        .issue(hvk, &fx.hsk, &fx.f, &r.id, &fx.proof, &mut rng)
        .unwrap();
    let state = IssuanceState::from_bytes(&fx.state_bytes).unwrap();
    let cred = pcs.unblind(hvk, &r.usk, &fx.f, &pre, &state).unwrap();
    assert!(pcs.verify_cred(hvk, &r.usk, &fx.f, &cred));

    // The same allow list as a closure over an `Rc`: neither `Send` nor `Sync`.
    let calls = Rc::new(Cell::new(0usize));
    let allowed = pcs.policy().clone();
    let counted = Rc::clone(&calls);
    let policy = move |phis: &[BinaryPoly]| {
        counted.set(counted.get() + 1);
        allowed.accepts(phis)
    };
    let verifier =
        LatticePCS::from_public_parameters(pcs.public_parameters().clone(), policy).unwrap();
    let t = Instant::now();
    assert_eq!(verifier.check_proof(hvk, &fx.f, &r.id, &fx.proof), Ok(()));
    println!(
        "  VerifyProof, valid, a policy that is not Sync: Ok; {:.2} s",
        secs(t)
    );
    assert_eq!(calls.get(), 1);
}

/// A request with exactly one invalid attestation, at each position, is refused with
/// `InvalidAttestation` by `Prove` (its `CheckAtts_P`) and, after a valid `π_0` over the list, by
/// `VerifyProof` in every pool.
#[test]
#[ignore = "heavy: the shared fixture (about 1 minute), seven R_issue proofs and 30 to 100 R_att verifications (run in release)"]
fn one_invalid_attestation_is_refused_at_every_position() {
    let fx = fixture();
    let (pcs, hvk, r) = (&fx.pcs, &fx.hvk, &fx.r);
    println!(
        "parallel attestation verification: {}",
        cfg!(feature = "parallel")
    );
    let mut rng = StdRng::seed_from_u64(0x9a7a_11e3);
    // the honest attestations of the lists are valid ...
    for att in &fx.atts[1..] {
        assert_eq!(pcs.check_attestation(hvk, &r.id, att), Ok(()));
    }
    let mut verdicts = Vec::new();
    for (kind, bad) in [
        ("made for another recipient", &fx.foreign),
        ("with a proof byte flipped", &fx.flipped),
    ] {
        // ... and the invalid one is invalid for R, but passes every public check of a list
        assert_eq!(
            pcs.check_attestation(hvk, &r.id, bad),
            Err(Error::InvalidProof)
        );
        for position in 0..3 {
            let mut list = fx.atts[1..].to_vec();
            list.insert(position, bad.clone());
            let what = format!("one attestation {kind} at position {position}");
            let t = Instant::now();
            let refused = pcs.prove(hvk, &fx.f, &r.id, &r.usk, &list, &mut rng).err();
            println!("  Prove, {what}: {refused:?}; {:.2} s", secs(t));
            assert_eq!(refused, Some(Error::InvalidAttestation), "Prove, {what}");
            let request = fx.request_over(&list, &mut rng);
            let verdict = in_pools(&format!("VerifyProof, {what}"), || {
                pcs.check_proof(hvk, &fx.f, &r.id, &request)
            });
            assert_eq!(
                verdict,
                Err(Error::InvalidAttestation),
                "VerifyProof, {what}"
            );
            verdicts.push((what, refused, verdict));
        }
    }
    // the control: the cheating prover's request over the honest list is accepted, so the
    // refusals above are the invalid attestation's (π_0 verifies before the attestation proofs:
    // a bad π_0 would have been InvalidProof)
    let request = fx.request_over(&fx.atts, &mut rng);
    let t = Instant::now();
    assert_eq!(pcs.check_proof(hvk, &fx.f, &r.id, &request), Ok(()));
    println!(
        "  VerifyProof, the cheating prover's request over the honest list: Ok; {:.2} s",
        secs(t)
    );
    println!("verdicts:");
    for (what, prove, verify) in verdicts {
        println!("  {what}: Prove {prove:?}, VerifyProof {verify:?}");
    }
}

/// A policy that is neither `Send` nor `Sync` (a closure over an `Rc`) gives a verifier, with or
/// without `parallel`: the parallel attestation verification shares no part of the policy. The
/// policy runs once, on the calling thread; a request it refuses costs no proof.
#[test]
fn a_policy_that_is_not_sync_still_gives_a_verifier() {
    let calls = Rc::new(Cell::new(0usize));
    let counted = Rc::clone(&calls);
    let policy = move |phis: &[BinaryPoly]| {
        counted.set(counted.get() + 1);
        phis.is_empty()
    };
    let open = LatticePCS::setup(SetupParams::new(LABEL.to_vec())).unwrap();
    let pcs = LatticePCS::from_public_parameters(open.public_parameters().clone(), policy).unwrap();
    let mut rng = StdRng::seed_from_u64(0x9a7a_11e4);
    let (hvk, _hsk) = pcs.helper_keygen(&mut rng);
    let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
    let f = Predicate::new(1, b"members".to_vec());
    // a well-formed request whose one attestation the policy refuses: no Jali work
    let request = IssuanceProof {
        attestations: vec![Attestation {
            tag: LWRTag::from_entries([1; M]),
            phi: BinaryPoly::from_bytes([0; BinaryPoly::BYTES]),
            proof: Proof::from_bytes(vec![0; 64]).unwrap(),
        }],
        c: Rq::from_i64(&[3; D]).unwrap(),
        t0: LWRTag::from_entries([2; M]),
        proof: Proof::from_bytes(vec![0; 64]).unwrap(),
    };
    assert_eq!(
        pcs.check_proof(&hvk, &f, &id, &request),
        Err(Error::PolicyRejected)
    );
    assert_eq!(calls.get(), 1);
    assert_eq!(
        pcs.prove(&hvk, &f, &id, &usk, &request.attestations, &mut rng)
            .err(),
        Some(Error::PolicyRejected)
    );
    assert_eq!(calls.get(), 2);
}
