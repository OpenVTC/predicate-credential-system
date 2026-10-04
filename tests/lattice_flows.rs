//! The main flow of the validation harness (`pcs-128-v2/setR/harness/src/flow.rs:297-597`,
//! `main_flow`), ported to `LatticePCS` with ONE real helper key (an NTRU trapdoor), at `k = 3`
//! and `k = 5`, as the harness ran it (82/82 and 94/94 checks with its PRC flow).
//!
//! Every check of the harness's MAIN flow is an assertion here, marked `H` in the log
//! (`3k + 47` of them: 56 at `k = 3`, 62 at `k = 5`); the checks this suite adds (controls,
//! PCS-API variants, wire round trips) are marked `+`. The PRC flow of the harness
//! (`prc_flow`) is out of scope: the trait has no `Req` and no session context `χ`.
//!
//! How the harness's checks map to the construction:
//!
//! * Positive paths and verifier-side checks run through the PCS API on objects that went
//!   through their wire encodings.
//! * The false-witness checks (`Error::Witness` of the honest prover) run Jali's witness check
//!   on the statement of an independent port of the harness's builders (`lattice_support::Port`);
//!   the credentials they need on messages outside `M_Σ` are REAL preimages under the one helper
//!   key (`lattice_support::Trapdoor`). Where the PCS API can express the false witness, its
//!   refusal is checked too (`WitnessDoesNotSatisfyRelation`, `IdentifierMismatch`).
//! * The harness's "Σ-vSIS Verify" checks on `x_1`, `usk`, `x_0` with a coefficient 2 and on a
//!   non-binary `φ` become "cannot be represented": the types (`Ternary`, `BinaryPoly`) refuse
//!   those values, and so do their decoders.
//! * The exact ℓ2 bound of `s` uses a key `h'` solved from a chosen `s` (the harness's device): no
//!   preimage of the real key has a norm near `⌊β_s²⌋` (honest `‖s‖² ≈ 1.4·10^10 ≪ 9.1·10^10`).
//! * The non-canonical tags `T + p e_0` cannot be represented (`u16` entries, `p = 2^16`); Jali
//!   accepts a fresh proof for `T + p e_0`, which is a proof for `T` as well, so it buys no second
//!   tag: next to the attester's own attestation it is a duplicate.
//! * The self-attestation and the policy check, which the harness's honest prover does not run,
//!   are checked against the honest `Prove` (which refuses) AND against a cheating prover's
//!   request with a valid `π_0` (which the verifier refuses).
//!
//! Heavy: Jali proofs of seconds and about 0.5 GiB each. Run in release, one at a time:
//! `RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_flows -- --ignored --nocapture`
//! (3.6 minutes at `k = 3` and 4.6 minutes at `k = 5` on an Apple M4, one thread; peak RSS 0.76 GB).
#![cfg(feature = "lattice")]
#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

mod lattice_support;

use std::time::Instant;

use lattice_support::*;
use predicate_credential_system::{
    Error,
    cred::{
        CredentialBase, VSIS,
        vsis::{VSISCredential, VSISVerificationKey},
    },
    jali,
    kiprf::lwr::{LWR, LWRTag},
    lattice::{BinaryPoly, D, P, Q, Rq, S_BOUND, Ternary, oracles},
    pcs::{
        AttributePolicy, Predicate, PredicateCredentialSystem,
        lattice::{Attestation, Credential, IssuanceProof, Proof, RootRequest, UserSecretKey},
    },
    serialization::WireFormat,
};
use rand::{SeedableRng, rngs::StdRng};

#[test]
#[ignore = "heavy: about 4 minutes in release (Jali proofs of 0.5 GiB each)"]
fn main_flow_k3() {
    main_flow(3, 0x00f1_0003);
}

#[test]
#[ignore = "heavy: about 5 minutes in release (Jali proofs of 0.5 GiB each)"]
fn main_flow_k5() {
    main_flow(5, 0x00f1_0005);
}

/// `main_flow` of H/flow.rs with `k` attesters U1..Uk (root credentials under `f_root`), U(k+1)
/// with a root credential under `f_other` (outside the policy), and the recipient U(k+2).
#[allow(clippy::too_many_lines)] // the harness's flow, section by section
fn main_flow(k: usize, seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut log = Log::new(&format!(
        "main flow, k = {k} (H/flow.rs:299-597), seed {seed:#x}"
    ));
    let k32 = u32::try_from(k).unwrap();
    let f_root = Predicate::root(b"f_root".to_vec());
    let f_other = Predicate::root(b"f_other".to_vec());
    let f_k = Predicate::new(k32, format!("f_{k}").into_bytes());
    let label = format!("lattice-flows/k{k}");
    // P admits the root label and the label of f_k (H/flow.rs:304-305)
    let pcs = deployment(label.as_bytes(), &[&f_root, &f_k]);
    let open = open_verifier(&pcs);
    let port = Port::new(pcs.public_parameters());
    let sigma = pcs.public_parameters().pp_sigma.clone();
    let (phi_root, phi_k, phi_other) = (
        pcs.enc_pred(&f_root),
        pcs.enc_pred(&f_k),
        pcs.enc_pred(&f_other),
    );

    // ONE helper key, and the keys through their encodings
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);
    let (hvk, hsk) = (wire_hvk(&hvk), wire_hsk(&hsk));
    let trapdoor = Trapdoor::of(&hsk);
    let h = hvk.h().clone();

    let mut users: Vec<Member> = (1..=k + 2)
        .map(|i| Member::new(&pcs, &format!("U{i}"), &mut rng))
        .collect();
    for u in &mut users {
        u.usk = wire_usk(&u.usk);
        u.id = wire_tag(&u.id);
        assert_eq!(pcs.identity(&u.usk), Ok(u.id.clone()));
    }
    let (other, r) = (k, k + 1);

    // -----------------------------------------------------------------------------------------
    log.section("1. root issuance (R_issue under ctx_root, rem:chain)");
    let t = Instant::now();
    for (ui, user) in users.iter_mut().enumerate().take(k + 1) {
        let f_j = if ui == other { &f_other } else { &f_root };
        let (request, state) = pcs
            .root_request(&hvk, f_j, &user.id, &user.usk, &mut rng)
            .unwrap();
        let request = wire_root_request(&request);
        log.ok(
            H,
            &format!("root request of {} verifies", user.name),
            pcs.check_root_request(&hvk, f_j, &user.id, &request),
        );
        let pre = pcs
            .issue_root(&hvk, &hsk, f_j, &user.id, &request, &mut rng)
            .unwrap();
        let (pre, state) = (wire_pre(&pre), wire_state(&state));
        let cred = pcs.unblind(&hvk, &user.usk, f_j, &pre, &state).unwrap();
        let cred = wire_credential(&cred);
        log.holds(
            H,
            &format!(
                "BlindIssue (one helper key) + Unblind/VerifyCred for {}",
                user.name
            ),
            pcs.verify_cred(&hvk, &user.usk, f_j, &cred),
        );
        user.cred = Some(cred);
        user.f = Some(f_j.clone());
    }
    log.holds(
        X,
        "the helper key counted one preimage per root credential",
        hsk.signing_key().issued() == u64::try_from(k + 1).unwrap(),
    );
    println!("  root issuance of {} users: {:.1} s", k + 1, secs(t));

    let id_r = users[r].id.clone();
    let s_r = pcs.tag_point(&id_r);
    let rows_r = port.rows(&s_r);

    // -----------------------------------------------------------------------------------------
    log.section("2. attestations U1..Uk -> recipient (R_att at H_0(id))");
    let mut atts = Vec::new();
    let mut max_e = 0u8;
    for u in &users[..k] {
        let t = Instant::now();
        let att = pcs
            .attest(&hvk, &u.usk, u.f(), u.cred(), &id_r, &mut rng)
            .unwrap();
        let attest_s = secs(t);
        let att = wire_attestation(&att);
        let t = Instant::now();
        log.ok(
            H,
            &format!("attestation {} -> U{} verifies", u.name, r + 1),
            pcs.check_attestation(&hvk, &id_r, &att),
        );
        println!(
            "    Attest {attest_s:.2} s, VerifyProofAtt {:.2} s, |att| = {} B",
            secs(t),
            att.compact_size()
        );
        let (tag, e) = LWR.eval_with_error(u.usk.expose_ternary(), &s_r).unwrap();
        assert_eq!(tag, att.tag);
        max_e = max_e.max(e.entries().iter().map(|x| x.unsigned_abs()).max().unwrap());
        atts.push(att);
    }
    log.holds(
        X,
        &format!("honest rounding errors reach max |e| = {max_e} <= (γ-1)/2 = 7"),
        max_e <= 7,
    );

    // ---- R_att false witnesses (H/flow.rs:337-434) ------------------------------------------
    log.section("2a. R_att false witnesses (the honest prover's witness check)");
    let u1 = &users[0];
    let cred1 = u1.cred().clone();
    let usk1 = ints(u1.usk.expose_ternary());
    let x0_1 = [ints(&cred1.x0[0]), ints(&cred1.x0[1])];
    let x0_1_ref = [x0_1[0].as_slice(), x0_1[1].as_slice()];
    let x1_1 = ints(cred1.cred.x1());
    let (tag1, e1) = LWR.eval_with_error(u1.usk.expose_ternary(), &s_r).unwrap();
    let t1 = tag_values(&tag1);
    let bphi_root = sigma.b_phi().mul(&phi_root.to_rq());
    let st_att = port.r_att(&h, &bphi_root, &rows_r, &t1);
    let honest_att_w = port.att_witness_of(&u1.usk, &cred1, e1.entries());
    log.ok_jali(
        X,
        "control: the port's R_att accepts U1's honest witness",
        port.check_witness(&st_att, &port.sets.att, &honest_att_w),
    );
    // another user's usk with U1's credential and tag
    let usk2 = ints(users[1].usk.expose_ternary());
    let w = port.att_witness(
        (cred1.cred.s0(), cred1.cred.s1()),
        &x1_1,
        &usk2,
        x0_1_ref,
        e1.entries(),
    );
    log.witness(
        H,
        "another user's usk with U1's credential and tag",
        port.check_witness(&st_att, &port.sets.att, &w),
    );
    log.refused(
        X,
        "Attest refuses another user's key with U1's credential (before any proving work)",
        pcs.attest(&hvk, &users[1].usk, &f_root, &cred1, &id_r, &mut rng),
        Error::WitnessDoesNotSatisfyRelation,
    );
    // T_0 ± 1 with e_0 ± γ: the equation holds modulo q_t, but |e_0| > 7
    for by in [1i128, -1] {
        let mut shifted = t1;
        shifted[0] = (shifted[0] + by).rem_euclid(i128::from(P));
        let mut e2 = *e1.entries();
        e2[0] = i8::try_from(i128::from(e2[0]) + 15 * by).unwrap();
        let st = port.r_att(&h, &bphi_root, &rows_r, &shifted);
        let w = port.att_witness_of(&u1.usk, &cred1, &e2);
        log.witness(
            H,
            &format!(
                "shifted tag T_0 {} 1 with e_0 {} γ: |e_0| = {} > 7",
                if by > 0 { '+' } else { '-' },
                if by > 0 { '+' } else { '-' },
                e2[0].unsigned_abs()
            ),
            port.check_witness(&st, &port.sets.att, &w),
        );
    }
    // x_1 with a coefficient 2: no Ternary holds it, and the credential decoder refuses the code
    let mut two = vec![0i8; D];
    two[0] = 2;
    let mut bytes = WireFormat::to_bytes(&cred1.cred).unwrap();
    bytes[2 * 2560] = (bytes[2 * 2560] & 0b1111_1100) | 0b10; // code 10 in coefficient 0 of x_1
    log.holds(
        H,
        "Σ-vSIS Verify: a credential with ‖x_1‖∞ = 2 > β_x cannot be represented (Ternary refuses 2, the decoder the code 10)",
        Ternary::from_coeffs(&two).is_err()
            && <VSISCredential as WireFormat>::from_bytes(&bytes).is_err(),
    );
    let mut x1_bad = x1_1.clone();
    x1_bad[0] = 2;
    let x0_rq = [cred1.x0[0].to_rq(), cred1.x0[1].to_rq()];
    let t_bad = target(
        &sigma,
        &u1.usk.expose_ternary().to_rq(),
        [&x0_rq[0], &x0_rq[1]],
        &rq(&x1_bad),
        &phi_root.to_rq(),
    );
    let (s0, s1) = trapdoor.preimage(&t_bad, &mut rng);
    log.holds(
        X,
        "control: a real preimage of the x_1 = 2 target under the helper key (s_0 + h s_1 = t, ‖s‖² <= ⌊β_s²⌋)",
        rq_i32(&s0).add(&h.mul(&rq_i32(&s1))) == t_bad && norm_sq(&s0, &s1) <= S_BOUND,
    );
    let w = port.att_witness((&s0, &s1), &x1_bad, &usk1, x0_1_ref, e1.entries());
    log.witness(
        H,
        "x_1 with a coefficient 2 > β_x = 1 (a real preimage for it)",
        port.check_witness(&st_att, &port.sets.att, &w),
    );
    // ‖s‖² at ⌊β_s²⌋ + 1 and at ⌊β_s²⌋, under a key h' solved from s (H/flow.rs:367-395)
    let t_1 = rq_i32(cred1.cred.s0()).add(&h.mul(&rq_i32(cred1.cred.s1())));
    let s1_inv = rq_i32(cred1.cred.s1()).inverse().expect("s_1 is a unit");
    let norm_s1 = norm_sq(&[], cred1.cred.s1());
    for (total, accepted) in [(S_BOUND + 1, false), (S_BOUND, true)] {
        let s0p = vector_with_norm(total - norm_s1);
        let hp = t_1.sub(&rq_i32(&s0p)).mul(&s1_inv);
        let hvk_p = VSISVerificationKey::from_h(hp);
        let cred_p = Credential {
            cred: VSISCredential::from_parts(
                s0p.clone(),
                cred1.cred.s1().to_vec(),
                cred1.cred.x1().clone(),
            )
            .unwrap(),
            x0: cred1.x0.clone(),
        };
        assert_eq!(cred_p.cred.norm_sq(), total);
        if accepted {
            log.holds(
                H,
                "Σ-vSIS Verify accepts ‖s‖² = ⌊β_s²⌋ (key solved from s)",
                pcs.verify_cred(&hvk_p, &u1.usk, &f_root, &cred_p),
            );
            let t = Instant::now();
            let att_p = pcs
                .attest(&hvk_p, &u1.usk, &f_root, &cred_p, &id_r, &mut rng)
                .unwrap();
            let att_p = wire_attestation(&att_p);
            log.ok(
                H,
                "R_att boundary: ‖s‖² = ⌊β_s²⌋ proves and verifies (exact ℓ2 bound)",
                pcs.check_attestation(&hvk_p, &id_r, &att_p),
            );
            println!("    boundary attestation: {:.1} s", secs(t));
        } else {
            log.holds(
                H,
                "Σ-vSIS Verify refuses ‖s‖² = ⌊β_s²⌋ + 1 (key solved from s)",
                !pcs.verify_cred(&hvk_p, &u1.usk, &f_root, &cred_p),
            );
            log.refused(
                H,
                "R_att false witness: ‖s‖² = ⌊β_s²⌋ + 1 (Attest refuses it)",
                pcs.attest(&hvk_p, &u1.usk, &f_root, &cred_p, &id_r, &mut rng),
                Error::WitnessDoesNotSatisfyRelation,
            );
        }
    }
    // usk with a coefficient 2: no UserSecretKey holds it; credential and tag computed from it
    let mut usk_bytes = u1.usk.to_bytes().unwrap().to_vec();
    usk_bytes[0] = (usk_bytes[0] & 0b1111_1100) | 0b10;
    log.holds(
        H,
        "Σ-vSIS Verify: a credential on a usk with a coefficient 2 cannot be represented (UserSecretKey is ternary, its decoder refuses the code 10)",
        Ternary::from_coeffs(&two).is_err()
            && <UserSecretKey as WireFormat>::from_bytes(&usk_bytes).is_err(),
    );
    let mut usk_bad = usk1.clone();
    usk_bad[0] = 2;
    let t_bad = target(
        &sigma,
        &rq(&usk_bad),
        [&x0_rq[0], &x0_rq[1]],
        &cred1.cred.x1().to_rq(),
        &phi_root.to_rq(),
    );
    let (s0, s1) = trapdoor.preimage(&t_bad, &mut rng);
    let (tag_b, e_b) = harness_tag_eval(&usk_bad, &s_r);
    let st_u = port.r_att(&h, &bphi_root, &rows_r, &tag_b);
    let w = port.att_witness((&s0, &s1), &x1_1, &usk_bad, x0_1_ref, &e_b);
    log.witness(
        H,
        "usk with a coefficient 2 > β_u = 1 (a real preimage and the tag computed from it)",
        port.check_witness(&st_u, &port.sets.att, &w),
    );
    // x_0 with a coefficient 2
    let mut cred_bytes = cred1.to_bytes().unwrap().to_vec();
    cred_bytes[5376] = (cred_bytes[5376] & 0b1111_1100) | 0b10; // coefficient 0 of x_{0,0}
    log.holds(
        H,
        "Σ-vSIS Verify: a credential with an x_0 coefficient 2 cannot be represented (the credential decoder refuses the code 10)",
        <Credential as WireFormat>::from_bytes(&cred_bytes).is_err(),
    );
    let mut x0_bad = x0_1[0].clone();
    x0_bad[0] = 2;
    let t_bad = target(
        &sigma,
        &u1.usk.expose_ternary().to_rq(),
        [&rq(&x0_bad), &x0_rq[1]],
        &cred1.cred.x1().to_rq(),
        &phi_root.to_rq(),
    );
    let (s0, s1) = trapdoor.preimage(&t_bad, &mut rng);
    let w = port.att_witness((&s0, &s1), &x1_1, &usk1, [&x0_bad, &x0_1[1]], e1.entries());
    log.witness(
        H,
        "x_0 with a coefficient 2 > β_r = 1 (a real preimage for it)",
        port.check_witness(&st_att, &port.sets.att, &w),
    );
    // a credential on a non-binary φ: no BinaryPoly holds it; Jali proves it (φ is public); no
    // binary φ that an attestation can carry makes the verifier's statement accept it
    log.holds(
        H,
        "Σ-vSIS Verify: a credential on a non-binary φ cannot be represented (every φ is a BinaryPoly)",
        (0..=255u8).all(|b| {
            let phi = BinaryPoly::from_bytes([b; BinaryPoly::BYTES]);
            (0..D).all(|i| phi.coefficient(i) <= 1)
        }),
    );
    let mut phi_nb = phi_ints(&phi_root);
    phi_nb[0] = 2;
    let t_nb = target(
        &sigma,
        &u1.usk.expose_ternary().to_rq(),
        [&x0_rq[0], &x0_rq[1]],
        &cred1.cred.x1().to_rq(),
        &rq(&phi_nb),
    );
    let (s0, s1) = trapdoor.preimage(&t_nb, &mut rng);
    let st_nb = port.r_att(&h, &sigma.b_phi().mul(&rq(&phi_nb)), &rows_r, &t1);
    let w = port.att_witness((&s0, &s1), &x1_1, &usk1, x0_1_ref, e1.entries());
    let ctx_nb = pcs.attestation_context(&hvk, &id_r, &phi_root, &tag1);
    let t = Instant::now();
    let proof_nb = port
        .prove(&st_nb, &port.sets.att, &w, &ctx_nb, &mut rng)
        .unwrap();
    log.ok_jali(
        X,
        "Jali proves and verifies R_att for a credential on the non-binary φ",
        port.verify(&st_nb, &port.sets.att, &proof_nb, &ctx_nb),
    );
    let parity: Vec<u8> = phi_nb
        .iter()
        .map(|&x| u8::try_from(x % 2).unwrap())
        .collect();
    for (kind, claimed, what) in [
        (
            H,
            phi_root,
            "the credential's φ with coefficient 0 replaced",
        ),
        (X, binary(&parity), "φ mod 2"),
    ] {
        let att = Attestation {
            tag: tag1.clone(),
            phi: claimed,
            proof: Proof::from_bytes(proof_nb.clone()).unwrap(),
        };
        log.refused(
            kind,
            &format!(
                "R_att verifier: non-binary φ (Jali proves it; presented as {what}, it is refused)"
            ),
            pcs.check_attestation(&hvk, &id_r, &att),
            Error::InvalidProof,
        );
    }
    println!("    non-binary φ: {:.1} s", secs(t));

    // ---- R_att verifier-side tamper checks (H/flow.rs:436-488) -------------------------------
    log.section("2b. R_att verifier-side tamper checks");
    let a1 = atts[0].clone();
    let refuse_att = |log: &mut Log,
                      kind: Kind,
                      name: &str,
                      hvk: &VSISVerificationKey,
                      id: &LWRTag,
                      att: &Attestation| {
        log.refused(
            kind,
            name,
            pcs.check_attestation(hvk, id, att),
            Error::InvalidProof,
        );
    };
    let a = Attestation {
        tag: bump(&a1.tag, 3),
        ..a1.clone()
    };
    refuse_att(
        &mut log,
        H,
        "tag id_{1->r} changed in one row",
        &hvk,
        &id_r,
        &a,
    );
    let mut phi_bytes = *a1.phi.as_bytes();
    phi_bytes[5] ^= 1;
    let a = Attestation {
        phi: BinaryPoly::from_bytes(phi_bytes),
        ..a1.clone()
    };
    refuse_att(
        &mut log,
        H,
        "disclosed φ changed in one bit (still binary)",
        &hvk,
        &id_r,
        &a,
    );
    refuse_att(
        &mut log,
        H,
        "attestation presented for another recipient",
        &hvk,
        &users[other].id,
        &a1,
    );
    let (hvk2, _) = pcs.helper_keygen(&mut rng);
    refuse_att(
        &mut log,
        H,
        "another issuer key (a second HKeyGen of the same deployment)",
        &hvk2,
        &id_r,
        &a1,
    );
    // the honest proof under other contexts: the port's statement IS the library's (control)
    let pp_digest = *pcs.parameters_digest();
    let ctx_1 = pcs.attestation_context(&hvk, &id_r, &a1.phi, &a1.tag);
    log.holds(
        X,
        "control: ctx_j as docs/encodings.md frames it is the library's",
        attestation_context_as(
            b"/LATTICE-CTX-ATT",
            &pp_digest,
            &hvk,
            &id_r,
            &a1.phi,
            &a1.tag,
            b"",
        ) == ctx_1,
    );
    log.ok_jali(
        X,
        "control: the port's R_att verifies the library's proof (same statement)",
        port.verify(&st_att, &port.sets.att, a1.proof.as_bytes(), &ctx_1),
    );
    let ctx_label = attestation_context_as(
        b"/LATTICE-CTX-ATT-OTHER",
        &pp_digest,
        &hvk,
        &id_r,
        &a1.phi,
        &a1.tag,
        b"",
    );
    log.refused_jali(
        H,
        "other context label (ctx_j under another oracle suffix)",
        port.verify(&st_att, &port.sets.att, a1.proof.as_bytes(), &ctx_label),
        jali::Error::InvalidProof,
    );
    let ctx_hvk2 = pcs.attestation_context(&hvk2, &id_r, &a1.phi, &a1.tag);
    log.refused_jali(
        H,
        "another helper identifier hvk in ctx (statement under the real hvk)",
        port.verify(&st_att, &port.sets.att, a1.proof.as_bytes(), &ctx_hvk2),
        jali::Error::InvalidProof,
    );
    let mut bytes = a1.proof.as_bytes().to_vec();
    let middle = bytes.len() / 2;
    bytes[middle] ^= 1;
    let a = Attestation {
        proof: Proof::from_bytes(bytes).unwrap(),
        ..a1.clone()
    };
    refuse_att(&mut log, H, "one proof bit flipped", &hvk, &id_r, &a);
    let mut bytes = a1.proof.as_bytes().to_vec();
    bytes.pop();
    let a = Attestation {
        proof: Proof::from_bytes(bytes).unwrap(),
        ..a1.clone()
    };
    refuse_att(&mut log, H, "proof truncated by one byte", &hvk, &id_r, &a);
    let mut compact = a1.to_compact_bytes().unwrap();
    compact[336..464].fill(0xff);
    log.holds(
        H,
        "φ = 2 everywhere cannot be represented: the bytes of φ decode to a binary φ (here all ones)",
        Attestation::from_compact_bytes(&compact)
            .is_ok_and(|a| (0..D).all(|i| a.phi.coefficient(i) == 1)),
    );
    // non-canonical tag T + p e_0
    log.holds(
        H,
        "non-canonical tag T + p e_0 cannot be represented (u16 entries, p = 2^16)",
        u16::try_from(u32::from(a1.tag.entries()[0]) + P).is_err(),
    );
    let mut lifted = t1;
    lifted[0] += i128::from(P);
    let st_lifted = port.r_att(&h, &bphi_root, &rows_r, &lifted);
    let t = Instant::now();
    let proof_lifted = port
        .prove(&st_lifted, &port.sets.att, &honest_att_w, &ctx_1, &mut rng)
        .unwrap();
    log.ok_jali(
        H,
        "Jali alone accepts a fresh proof for T + p e_0 (same statement mod q_t)",
        port.verify(&st_lifted, &port.sets.att, &proof_lifted, &ctx_1),
    );
    log.ok_jali(
        X,
        "... and that proof is a proof for the canonical T as well",
        port.verify(&st_att, &port.sets.att, &proof_lifted, &ctx_1),
    );
    let att_lifted = Attestation {
        tag: tag1.clone(),
        phi: phi_root,
        proof: Proof::from_bytes(proof_lifted).unwrap(),
    };
    log.ok(
        X,
        "presented (as T: the only encoding), it is U1's attestation",
        pcs.check_attestation(&hvk, &id_r, &att_lifted),
    );
    let mut twice = atts.clone();
    twice[1] = att_lifted;
    log.refused(
        H,
        "VerifyProofAtt/ValidTag: T + p e_0 buys no second tag (next to U1's own attestation: DuplicateAttester)",
        pcs.prove(&hvk, &f_k, &id_r, &users[r].usk, &twice, &mut rng),
        Error::DuplicateAttester,
    );
    println!("    non-canonical tag: {:.1} s", secs(t));

    // -----------------------------------------------------------------------------------------
    log.section("3. issuance: Prove (R_issue), VerifyProof (CheckAtts_P, P), Issue, Unblind");
    let usk_r = &users[r].usk;
    let t = Instant::now();
    let (proof, state) = pcs
        .prove(&hvk, &f_k, &id_r, usk_r, &atts, &mut rng)
        .unwrap();
    let prove_s = secs(t);
    let proof = wire_issuance_proof(&proof, &f_k);
    let t = Instant::now();
    log.ok(
        H,
        &format!("VerifyProof of U{}'s request (k = {k})", r + 1),
        pcs.check_proof(&hvk, &f_k, &id_r, &proof),
    );
    let verify_s = secs(t);
    let t = Instant::now();
    let pre = pcs
        .issue(&hvk, &hsk, &f_k, &id_r, &proof, &mut rng)
        .unwrap();
    let issue_s = secs(t);
    let (pre, state) = (wire_pre(&pre), wire_state(&state));
    let cred_r = pcs.unblind(&hvk, usk_r, &f_k, &pre, &state).unwrap();
    let cred_r = wire_credential(&cred_r);
    log.holds(
        H,
        &format!(
            "BlindIssue (one helper key) + Unblind/VerifyCred for U{}",
            r + 1
        ),
        pcs.verify_cred(&hvk, usk_r, &f_k, &cred_r),
    );
    log.holds(
        X,
        "the credential is bound to (usk, f_k): not valid for f_root, nor for U1's key",
        !pcs.verify_cred(&hvk, usk_r, &f_root, &cred_r)
            && !pcs.verify_cred(&hvk, &users[0].usk, &f_k, &cred_r),
    );
    log.holds(
        X,
        "the helper key counted k + 2 preimages",
        hsk.signing_key().issued() == u64::try_from(k + 2).unwrap(),
    );
    let pi_bytes = proof.compact_size();
    println!(
        "  issuance: |π| = {pi_bytes} B (k x |att| + 2900 + |π_0| = {} + 2900 + {}); Prove {prove_s:.1} s, VerifyProof {verify_s:.1} s, Issue {issue_s:.1} s",
        proof
            .attestations
            .iter()
            .map(Attestation::compact_size)
            .sum::<usize>(),
        proof.proof.len()
    );

    // ---- R_issue false witnesses (H/flow.rs:506-534) -----------------------------------------
    log.section("3a. R_issue false witnesses");
    let c0 = &pcs.public_parameters().c0;
    let (id_check, e_id) = LWR.eval_with_error(usk_r.expose_ternary(), c0).unwrap();
    assert_eq!(id_check, id_r);
    let (t0, e_ii) = LWR.eval_with_error(usk_r.expose_ternary(), &s_r).unwrap();
    assert_eq!(t0, proof.t0);
    let (id_t, t0_t) = (tag_values(&id_r), tag_values(&t0));
    let uskr = ints(usk_r.expose_ternary());
    let x0_r = [ints(&cred_r.x0[0]), ints(&cred_r.x0[1])];
    let x0_r_ref = [x0_r[0].as_slice(), x0_r[1].as_slice()];
    let st_iss = port.r_issue(&proof.c, &id_t, &rows_r, &t0_t);
    let honest_iss_w = port.issue_witness(&uskr, x0_r_ref, e_id.entries(), e_ii.entries());
    log.ok_jali(
        X,
        "control: the port's R_issue accepts the recipient's honest witness",
        port.check_witness(&st_iss, &port.sets.issue, &honest_iss_w),
    );
    let mut x0_bad = x0_r[0].clone();
    x0_bad[0] = 2;
    let c_bad = commitment(&sigma, &rq(&uskr), [&rq(&x0_bad), &rq(&x0_r[1])]);
    let w = port.issue_witness(&uskr, [&x0_bad, &x0_r[1]], e_id.entries(), e_ii.entries());
    log.witness(
        H,
        "x_0 with a coefficient 2 > β_r (C computed from it)",
        port.check_witness(
            &port.r_issue(&c_bad, &id_t, &rows_r, &t0_t),
            &port.sets.issue,
            &w,
        ),
    );
    let w = port.issue_witness(&usk1, x0_r_ref, e_id.entries(), e_ii.entries());
    log.witness(
        H,
        "another user's usk for the recipient's C, id and id_{i->i}",
        port.check_witness(&st_iss, &port.sets.issue, &w),
    );
    log.refused(
        X,
        "Prove refuses another user's key for the recipient's identifier",
        pcs.prove(&hvk, &f_k, &id_r, &users[0].usk, &atts, &mut rng),
        Error::IdentifierMismatch,
    );
    let mut usk_bad = uskr.clone();
    usk_bad[0] = 2;
    let c_b = commitment(&sigma, &rq(&usk_bad), [&rq(&x0_r[0]), &rq(&x0_r[1])]);
    let (id_b, e_idb) = harness_tag_eval(&usk_bad, c0);
    let s_b = oracles::tag_point(pcs.label(), &tag_of(&id_b));
    let (ii_b, e_iib) = harness_tag_eval(&usk_bad, &s_b);
    let w = port.issue_witness(&usk_bad, x0_r_ref, &e_idb, &e_iib);
    log.witness(
        H,
        "usk with a coefficient 2 > β_u (C, id and id_{i->i} computed from it)",
        port.check_witness(
            &port.r_issue(&c_b, &id_b, &port.rows(&s_b), &ii_b),
            &port.sets.issue,
            &w,
        ),
    );
    let mut shifted = t0_t;
    shifted[0] = (shifted[0] + 1) % i128::from(P);
    let mut e_shifted = *e_ii.entries();
    e_shifted[0] += 15;
    let w = port.issue_witness(&uskr, x0_r_ref, e_id.entries(), &e_shifted);
    log.witness(
        H,
        "id_{i->i} shifted by 1 in row 0 with |e_0| > (γ-1)/2",
        port.check_witness(
            &port.r_issue(&proof.c, &id_t, &rows_r, &shifted),
            &port.sets.issue,
            &w,
        ),
    );

    // ---- VerifyProof: verifier-side and flow-level checks (H/flow.rs:536-586) ---------------
    log.section("3b. VerifyProof: verifier-side and flow-level checks");
    let with = |attestations: Vec<Attestation>| IssuanceProof {
        attestations,
        ..proof.clone()
    };
    let mut dup = atts.clone();
    dup[1] = dup[0].clone();
    log.refused(
        H,
        "the same attester twice",
        pcs.check_proof(&hvk, &f_k, &id_r, &with(dup)),
        Error::DuplicateAttester,
    );
    let f_more = Predicate::new(k32 + 1, format!("f_{}", k + 1).into_bytes());
    log.refused(
        H,
        &format!("threshold {} with {k} attestations", k + 1),
        pcs.check_proof(&hvk, &f_more, &id_r, &proof),
        Error::WrongAttestationCount {
            expected: k + 1,
            actual: k,
        },
    );
    let f_less = Predicate::new(k32 - 1, format!("f_{}", k - 1).into_bytes());
    log.refused(
        X,
        &format!("threshold {} with {k} attestations", k - 1),
        pcs.check_proof(&hvk, &f_less, &id_r, &proof),
        Error::WrongAttestationCount {
            expected: k - 1,
            actual: k,
        },
    );
    let compact = proof.to_compact_bytes().unwrap();
    log.holds(
        X,
        "the compact decoder for f_{k±1} refuses the proof's bytes",
        IssuanceProof::from_compact_bytes(&compact, &f_more).is_err()
            && IssuanceProof::from_compact_bytes(&compact, &f_less).is_err(),
    );
    let mut c = proof.c.coeffs().to_vec();
    c[0] = (c[0] + 1) % Q;
    log.refused(
        H,
        "commitment C changed",
        pcs.check_proof(
            &hvk,
            &f_k,
            &id_r,
            &IssuanceProof {
                c: Rq::from_coeffs(&c).unwrap(),
                ..proof.clone()
            },
        ),
        Error::InvalidProof,
    );
    log.refused(
        H,
        "self-exclusion tag id_{i->i} changed",
        pcs.check_proof(
            &hvk,
            &f_k,
            &id_r,
            &IssuanceProof {
                t0: bump(&proof.t0, 0),
                ..proof.clone()
            },
        ),
        Error::InvalidProof,
    );
    let f_b = Predicate::new(k32, format!("f_{k}b").into_bytes());
    log.refused(
        H,
        "another predicate f (same threshold) in ctx_0",
        pcs.check_proof(&hvk, &f_b, &id_r, &proof),
        Error::InvalidProof,
    );
    let replayed = RootRequest {
        c: proof.c.clone(),
        t0: proof.t0.clone(),
        proof: proof.proof.clone(),
    };
    log.refused(
        H,
        "issuance proof replayed as a root request (ctx_root)",
        pcs.check_root_request(&hvk, &f_root, &id_r, &replayed),
        Error::InvalidProof,
    );
    let mut tampered = atts.clone();
    let mut bytes = tampered[1].proof.as_bytes().to_vec();
    let at = bytes.len() / 3;
    bytes[at] ^= 4;
    tampered[1].proof = Proof::from_bytes(bytes).unwrap();
    log.refused(
        H,
        "one attestation proof bit flipped (π_0 binds the attestations)",
        pcs.check_proof(&hvk, &f_k, &id_r, &with(tampered.clone())),
        Error::InvalidProof,
    );
    // ... and with π_0 re-proven over the tampered list, CheckAtts_P itself refuses it
    let ctx0 = pcs.issuance_context(&hvk, &f_k, &id_r, &proof.c, &proof.t0, &tampered);
    let t = Instant::now();
    let pi0 = port
        .prove(&st_iss, &port.sets.issue, &honest_iss_w, &ctx0, &mut rng)
        .unwrap();
    log.refused(
        X,
        "... with π_0 re-proven over the tampered list (cheating prover): CheckAtts_P refuses the attestation",
        pcs.check_proof(
            &hvk,
            &f_k,
            &id_r,
            &IssuanceProof {
                attestations: tampered,
                proof: Proof::from_bytes(pi0).unwrap(),
                ..proof.clone()
            },
        ),
        Error::InvalidAttestation,
    );
    println!(
        "    tampered attestation with a valid π_0: {:.1} s",
        secs(t)
    );
    log.holds(
        H,
        "non-canonical id_{i->i} + p e_0 cannot be represented (u16 entries)",
        u16::try_from(u32::from(proof.t0.entries()[0]) + P).is_err() && LWR.valid_tag(&proof.t0),
    );
    log.holds(
        H,
        "non-canonical identifier id + p e_0 cannot be represented (u16 entries)",
        u16::try_from(u32::from(id_r.entries()[0]) + P).is_err() && LWR.valid_tag(&id_r),
    );
    // self-attestation: U1 requests with an attestation from itself
    let t = Instant::now();
    let u1 = &users[0];
    let id_1 = u1.id.clone();
    let s_1 = pcs.tag_point(&id_1);
    let self_att = pcs
        .attest(&hvk, &u1.usk, u1.f(), u1.cred(), &id_1, &mut rng)
        .unwrap();
    log.ok(
        X,
        "the self-attestation U1 -> U1 verifies on its own",
        pcs.check_attestation(&hvk, &id_1, &self_att),
    );
    let mut list = vec![self_att];
    for u in &users[1..k] {
        list.push(
            pcs.attest(&hvk, &u.usk, u.f(), u.cred(), &id_1, &mut rng)
                .unwrap(),
        );
    }
    log.refused(
        X,
        "Prove refuses the self-attestation",
        pcs.prove(&hvk, &f_k, &id_1, &u1.usk, &list, &mut rng),
        Error::SelfAttestation,
    );
    let cheat = |attestations: &[Attestation], rng: &mut StdRng| -> IssuanceProof {
        let x0 = [Ternary::sample(rng), Ternary::sample(rng)];
        let c = commitment(
            &sigma,
            &u1.usk.expose_ternary().to_rq(),
            [&x0[0].to_rq(), &x0[1].to_rq()],
        );
        let (id, e0) = LWR.eval_with_error(u1.usk.expose_ternary(), c0).unwrap();
        let (t0, e1) = LWR.eval_with_error(u1.usk.expose_ternary(), &s_1).unwrap();
        let st = port.r_issue(&c, &tag_values(&id), &port.rows(&s_1), &tag_values(&t0));
        let w = port.issue_witness(
            &usk1,
            [&ints(&x0[0]), &ints(&x0[1])],
            e0.entries(),
            e1.entries(),
        );
        let ctx = pcs.issuance_context(&hvk, &f_k, &id_1, &c, &t0, attestations);
        let pi0 = port.prove(&st, &port.sets.issue, &w, &ctx, rng).unwrap();
        assert_eq!(port.verify(&st, &port.sets.issue, &pi0, &ctx), Ok(()));
        IssuanceProof {
            attestations: attestations.to_vec(),
            c,
            t0,
            proof: Proof::from_bytes(pi0).unwrap(),
        }
    };
    let selfish = cheat(&list, &mut rng);
    log.holds(
        X,
        "U1's self-exclusion tag is its self-attestation's tag (both are Tag(usk_1, H_0(id_1)))",
        selfish.t0 == list[0].tag,
    );
    log.refused(
        H,
        "self-attestation (U1 endorses U1), with a valid π_0",
        pcs.check_proof(&hvk, &f_k, &id_1, &selfish),
        Error::SelfAttestation,
    );
    log.refused(
        X,
        "... also under P ≡ 1",
        open.check_proof(&hvk, &f_k, &id_1, &selfish),
        Error::SelfAttestation,
    );
    // the policy: one attester holds an f_other credential
    let uo = &users[other];
    let mut list2 = list[1..].to_vec();
    list2.push(
        pcs.attest(&hvk, &uo.usk, uo.f(), uo.cred(), &id_1, &mut rng)
            .unwrap(),
    );
    log.holds(
        X,
        "the f_other attester discloses φ_other, which P does not admit",
        list2[k - 1].phi == phi_other && !pcs.policy().accepts(&[phi_other]),
    );
    log.refused(
        X,
        "Prove refuses an attester label outside P",
        pcs.prove(&hvk, &f_k, &id_1, &u1.usk, &list2, &mut rng),
        Error::PolicyRejected,
    );
    let outside = cheat(&list2, &mut rng);
    log.refused(
        H,
        "an attester label f_other outside P, with a valid π_0",
        pcs.check_proof(&hvk, &f_k, &id_1, &outside),
        Error::PolicyRejected,
    );
    log.ok(
        X,
        "... while a verifier with P ≡ 1 accepts the same request (only P refuses it)",
        open.check_proof(&hvk, &f_k, &id_1, &outside),
    );
    println!("    self-attestation and policy: {:.1} s", secs(t));

    // -----------------------------------------------------------------------------------------
    log.section("4. composition: the recipient's new credential attests for U1");
    let t = Instant::now();
    let chained = pcs
        .attest(&hvk, usk_r, &f_k, &cred_r, &id_1, &mut rng)
        .unwrap();
    let chained = wire_attestation(&chained);
    log.ok(
        H,
        &format!("chained attestation U{} -> U1 verifies", r + 1),
        pcs.check_attestation(&hvk, &id_1, &chained),
    );
    log.holds(
        X,
        "its label is φ_k = EncPred(f_k), which P admits",
        chained.phi == phi_k && pcs.policy().accepts(&[chained.phi]),
    );
    println!("    chained attestation: {:.1} s", secs(t));
    log.holds(
        X,
        "Σ-vSIS keys verify what they issued and nothing of another key",
        !VSIS::verify(
            &sigma,
            &hvk2,
            &VSIS::encode_message(
                &sigma,
                &predicate_credential_system::cred::vsis::VSISHiddenMessage::new(
                    usk_r.expose_ternary().clone(),
                    cred_r.x0.clone(),
                ),
                &phi_k,
            )
            .unwrap(),
            &cred_r.cred,
        ),
    );

    log.finish(3 * k + 47);
}
