//! The short-key `Tag_LWR` and the oracles of the lattice instantiation through the public API
//! (feature `lattice`): the tags of the protocol (identifiers at the identifier point `x_0` of
//! `H_id`, attestation tags at the recipient points of `H_req`), and the agreement of the tag evaluation with the tag clauses as
//! Jali checks them, in INDEPENDENT re-implementations of the statements `R_Tag` and `R_iss`
//! built from the public Jali API with the layouts of the embedded parameter sets.
//!
//! The timing probe at the end is `#[ignore]`d; run it in release:
//! `cargo test --release --features lattice --test lattice_tag -- --ignored --nocapture`.
#![cfg(feature = "lattice")]

use std::{collections::BTreeMap, sync::Arc};

use predicate_credential_system::{
    Error,
    jali::{
        self,
        math::{Poly, Ring},
        statement::{Norm, Placement, Statement},
    },
    kiprf::{
        KIPRF,
        lwr::{LWR, LWRTag, RoundingError, TagMatrix},
    },
    lattice::{
        D, E_BOUND, E_COUNT, E_DEG, ELL_R, GAMMA, M, Q, Q_T, Rq, Ternary,
        oracles::{h_mat, identifier_point, request_point},
        sets::ParameterSets,
    },
};
use rand::{RngCore, SeedableRng, rngs::StdRng};

const DEPLOYMENT: &[u8] = b"lattice-tag integration tests";

/// The `H_id` digest of the identifier point of the tests (the protocol's digest of `⟨hvk⟩`).
const HVK_DIGEST: [u8; 32] = [0x1d; 32];

/// The identifier point `x_0 = H_mat("hid" ‖ d)` of the tests' helper key in `deployment`.
fn x0_of(deployment: &[u8]) -> TagMatrix {
    identifier_point(deployment, &HVK_DIGEST)
}

/// A recipient point for a random transcript digest.
fn recipient(rng: &mut StdRng) -> TagMatrix {
    let mut d = [0u8; 32];
    rng.fill_bytes(&mut d);
    request_point(DEPLOYMENT, &d)
}

/// The tags of one recipient and three attesters: the recipient's identifier at `x_0`, a
/// recipient point `x_Q`, the attestation tags. The tags are pairwise distinct and valid, each is
/// explained by its own key only, and the attestation tags are bound to the recipient point and
/// to the deployment.
#[test]
fn the_tags_of_an_issuance() {
    let mut rng = StdRng::seed_from_u64(0x7a61);
    let tag = LWR;
    let x0 = x0_of(DEPLOYMENT);
    let usk = tag.keygen(&mut rng);
    let id = tag.eval(&usk, &x0).unwrap();
    // a verifier re-derives x_0 from the deployment label and the key's digest
    assert_eq!(x0_of(DEPLOYMENT), x0);
    assert_eq!(h_mat(DEPLOYMENT, &[b"hid", &HVK_DIGEST[..]].concat()), x0);
    // another helper key, another identifier point and identifier
    let other_key = identifier_point(DEPLOYMENT, &[0x2e; 32]);
    assert_ne!(other_key, x0);
    assert_ne!(tag.eval(&usk, &other_key).unwrap(), id);
    let xq = recipient(&mut rng);
    assert_ne!(xq, x0);

    let attesters: Vec<Ternary> = (0..3).map(|_| tag.keygen(&mut rng)).collect();
    let tags: Vec<(LWRTag, RoundingError)> = attesters
        .iter()
        .map(|k| tag.eval_with_error(k, &xq).unwrap())
        .collect();
    // t ∈ T for every tag, pairwise distinct (distinct sources count distinctly)
    assert!(tag.valid_tag(&id));
    for (i, (t, _)) in tags.iter().enumerate() {
        assert!(tag.valid_tag(t));
        for (u, _) in &tags[i + 1..] {
            assert_ne!(t, u);
        }
    }
    for (i, key) in attesters.iter().enumerate() {
        for (j, (t, e)) in tags.iter().enumerate() {
            assert_eq!(tag.explains(key, &xq, t, e), i == j, "key {i}, tag {j}");
        }
    }
    // an attester's tag at another recipient point differs (recipient-scoped linkability)
    let other = recipient(&mut rng);
    assert_ne!(tag.eval(&attesters[0], &other).unwrap(), tags[0].0);
    // one key, one tag per point: the evaluation is deterministic
    assert_eq!(tag.eval(&attesters[0], &xq).unwrap(), tags[0].0);
    // and bound to the deployment
    assert_ne!(tag.eval(&usk, &x0_of(b"another deployment")).unwrap(), id);
    // H_req and H_id are H_mat under their labels
    let d = [9u8; 32];
    assert_eq!(
        request_point(DEPLOYMENT, &d),
        h_mat(DEPLOYMENT, &[b"req", &d[..]].concat())
    );
}

/// Every 336-byte string is a canonical tag (`t ∈ T` is a type invariant at `p = 2^16`), and a
/// tag survives the crate's canonical encoding.
#[test]
fn every_tag_encoding_is_canonical() {
    use predicate_credential_system::serialization::{from_bytes, to_bytes};
    let mut rng = StdRng::seed_from_u64(0x7a62);
    let id = LWR.eval(&LWR.keygen(&mut rng), &x0_of(DEPLOYMENT)).unwrap();
    let bytes = to_bytes(&id).unwrap();
    assert_eq!(bytes.len(), LWRTag::BYTES);
    assert_eq!(from_bytes::<LWRTag>(&bytes).unwrap(), id);
    for fill in [0x00u8, 0xff, 0x80, 0x7f] {
        let t = LWRTag::from_bytes(&[fill; LWRTag::BYTES]).unwrap();
        assert!(LWR.valid_tag(&t));
        assert_eq!(t.to_bytes(), vec![fill; LWRTag::BYTES]);
    }
    assert!(matches!(
        LWRTag::from_bytes(&[0; LWRTag::BYTES + 1]),
        Err(Error::Serialization(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// Agreement with Jali's tag clauses (independent builders of R_Tag and R_iss)
// ---------------------------------------------------------------------------------------------

/// The representative of `x` modulo `m` in `(−m/2, m/2]`.
fn centred(x: i128, m: i128) -> i128 {
    let r = x.rem_euclid(m);
    if r > m / 2 { r - m } else { r }
}

/// An element of `R_q` with centred coefficients.
fn lift(ring: &Arc<Ring>, x: &Rq) -> Poly {
    let c = x
        .coeffs()
        .iter()
        .map(|&v| centred(i128::from(v), i128::from(Q)))
        .collect();
    Poly::new(ring.clone(), c).unwrap()
}

/// Clause `j` is `ct(σ(a_j) usk + X^{-8 (j mod 128)} e_{⌊j/128⌋}) − γ T_j = 0` modulo `q_t`,
/// with the tag entries as raw integers (so that a test can pass `T + p`).
fn tag_clauses(
    st: &mut Statement,
    rt: &Arc<Ring>,
    a: &TagMatrix,
    t: &[i128],
) -> Result<(), jali::Error> {
    for (j, (row, &tj)) in a.rows().zip(t).enumerate() {
        let a = Poly::new(
            rt.clone(),
            row.iter()
                .map(|&x| centred(i128::from(x), i128::from(Q_T)))
                .collect(),
        )?
        .auto();
        let clause = st
            .variable_in(rt, "usk", 0)?
            .scale(&a)?
            .add(&st.coefficient_in(rt, "e", j / E_DEG, j % E_DEG)?)?
            .add(&st.constant_in(Poly::constant(rt.clone(), -i128::from(GAMMA) * tj))?)?;
        st.const_coeff_zero(clause)?;
    }
    Ok(())
}

/// The rounding-error block: two subring elements of degree 128, exact bound 7.
fn declare_e(st: &mut Statement) -> Result<(), jali::Error> {
    st.var_subring(
        "e",
        E_COUNT,
        E_DEG,
        Norm::LinfExact(E_BOUND),
        Placement::Ajtai,
    )?;
    Ok(())
}

/// `R_Tag` at `(t, a)`: blocks `usk`, `e`.
fn r_tag(a: &TagMatrix, t: &[i128]) -> Result<Statement, jali::Error> {
    let rc = Ring::new(i128::from(Q), D)?;
    let rt = Ring::new(i128::from(Q_T), D)?;
    let mut st = Statement::new(rc);
    st.var("usk", 1, Norm::LinfExact(1))?;
    declare_e(&mut st)?;
    tag_clauses(&mut st, &rt, a, t)?;
    Ok(st)
}

/// `R_iss` with the opening `C = b_u usk + B_r x_0` and `id` at `x_0`: blocks `usk`, `x0`, `e`.
fn r_iss(
    b_u: &Rq,
    b_r: &[Rq; ELL_R],
    c: &Rq,
    a: &TagMatrix,
    t: &[i128],
) -> Result<Statement, jali::Error> {
    let rc = Ring::new(i128::from(Q), D)?;
    let rt = Ring::new(i128::from(Q_T), D)?;
    let mut st = Statement::new(rc.clone());
    st.var("usk", 1, Norm::LinfExact(1))?;
    st.var("x0", ELL_R, Norm::LinfExact(1))?;
    declare_e(&mut st)?;
    let mut com = st.variable_in(&rc, "usk", 0)?.scale(&lift(&rc, b_u))?;
    for (k, b) in b_r.iter().enumerate() {
        com = com.add(&st.variable_in(&rc, "x0", k)?.scale(&lift(&rc, b))?)?;
    }
    com = com.add(&st.constant_in(lift(&rc, c).neg())?)?;
    st.eq_mod_p(com)?;
    tag_clauses(&mut st, &rt, a, t)?;
    Ok(st)
}

/// Entry `j` of `e` is coefficient `8 (j mod 128)` of element `⌊j/128⌋`.
fn e_subring(ring: &Arc<Ring>, e: &[i8; M]) -> Vec<Poly> {
    let stride = D / E_DEG;
    let mut out = vec![vec![0i128; D]; E_COUNT];
    for (j, &x) in e.iter().enumerate() {
        out[j / E_DEG][stride * (j % E_DEG)] = i128::from(x);
    }
    out.into_iter()
        .map(|c| Poly::new(ring.clone(), c).unwrap())
        .collect()
}

fn ternary_poly(ring: &Arc<Ring>, t: &Ternary) -> Poly {
    Poly::new(
        ring.clone(),
        t.coeffs().iter().map(|&x| i128::from(x)).collect(),
    )
    .unwrap()
}

fn entries(t: &LWRTag) -> Vec<i128> {
    t.entries().iter().map(|&x| i128::from(x)).collect()
}

/// The witness check of Jali's prover accepts `(usk, e)` for the tag of
/// [`LWR::eval_with_error`] in `R_Tag` compiled with the embedded `tag` set, and refuses the
/// shifted tag `T + 1` (with its honest error, and with the error `e + γ` outside the exact
/// bound), a perturbed error, and accepts a non-canonical `T + p` with the honest witness (the
/// relation alone does not refuse it: the public `t ∈ T` is what does).
#[test]
fn jali_accepts_the_tags_and_errors_of_the_evaluation() {
    let mut rng = StdRng::seed_from_u64(0x7a63);
    let sets = ParameterSets::load().unwrap();
    let rc = Ring::new(i128::from(Q), D).unwrap();
    let usk = LWR.keygen(&mut rng);
    let xq = recipient(&mut rng);
    let (t, e) = LWR.eval_with_error(&usk, &xq).unwrap();
    let witness = |e: &[i8; M]| {
        BTreeMap::from([
            ("usk".to_string(), vec![ternary_poly(&rc, &usk)]),
            ("e".to_string(), e_subring(&rc, e)),
        ])
    };
    let compile = |t: &[i128]| r_tag(&xq, t).unwrap().compile(sets.tag.clone()).unwrap();
    let t_t = entries(&t);
    let honest = compile(&t_t);
    assert!(honest.map_witness(&witness(e.entries())).is_ok());
    // a perturbed error
    let mut e_bad = *e.entries();
    e_bad[M - 1] = if e_bad[M - 1] == 7 {
        6
    } else {
        e_bad[M - 1] + 1
    };
    assert_eq!(
        honest.map_witness(&witness(&e_bad)).err(),
        Some(jali::Error::Witness)
    );
    // T + 1 in one row: the honest error no longer satisfies the clause ...
    let mut shifted = t_t.clone();
    shifted[5] += 1;
    let shifted = compile(&shifted);
    assert_eq!(
        shifted.map_witness(&witness(e.entries())).err(),
        Some(jali::Error::Witness)
    );
    // ... and the error that would (e + γ) is outside the exact bound 7
    let mut e_shifted = *e.entries();
    e_shifted[5] += 15;
    assert!(e_shifted[5] > 7);
    assert_eq!(
        shifted.map_witness(&witness(&e_shifted)).err(),
        Some(jali::Error::Witness)
    );
    // the non-canonical encoding T + p has exactly the witnesses of T
    let mut lifted = t_t;
    lifted[0] += 1 << 16;
    assert!(compile(&lifted).map_witness(&witness(e.entries())).is_ok());
}

/// The same for the identifier clause of `R_iss`, with the opening of the request, against the
/// embedded `iss` set: the honest witness passes, a perturbed error or another opening fails.
#[test]
fn jali_accepts_the_identifier_and_the_opening_of_a_request() {
    let mut rng = StdRng::seed_from_u64(0x7a64);
    let sets = ParameterSets::load().unwrap();
    let rc = Ring::new(i128::from(Q), D).unwrap();
    // public data: any elements of R_q (the parameter set covers the worst case)
    let uniform = |rng: &mut StdRng| {
        let c: Vec<i64> = (0..D)
            .map(|_| i64::from(rand::Rng::gen_range(rng, 0..Q)))
            .collect();
        Rq::from_i64(&c).unwrap()
    };
    let b_u = uniform(&mut rng);
    let b_r: [Rq; ELL_R] = core::array::from_fn(|_| uniform(&mut rng));
    let usk = LWR.keygen(&mut rng);
    let x0: [Ternary; ELL_R] = core::array::from_fn(|_| Ternary::sample(&mut rng));
    let c = b_r
        .iter()
        .zip(&x0)
        .fold(b_u.mul(&usk.to_rq()), |c, (b, x)| c.add(&b.mul(&x.to_rq())));
    let a = x0_of(DEPLOYMENT);
    let (id, e) = LWR.eval_with_error(&usk, &a).unwrap();
    let witness = |x0: &[Ternary; ELL_R], e: &[i8; M]| {
        BTreeMap::from([
            ("usk".to_string(), vec![ternary_poly(&rc, &usk)]),
            (
                "x0".to_string(),
                x0.iter().map(|x| ternary_poly(&rc, x)).collect(),
            ),
            ("e".to_string(), e_subring(&rc, e)),
        ])
    };
    let compiled = r_iss(&b_u, &b_r, &c, &a, &entries(&id))
        .unwrap()
        .compile(sets.iss.clone())
        .unwrap();
    assert!(compiled.map_witness(&witness(&x0, e.entries())).is_ok());
    let mut e_bad = *e.entries();
    e_bad[0] = if e_bad[0] == -7 { -6 } else { e_bad[0] - 1 };
    assert_eq!(
        compiled.map_witness(&witness(&x0, &e_bad)).err(),
        Some(jali::Error::Witness)
    );
    let mut other = x0.clone();
    other[0] = Ternary::sample(&mut rng);
    assert_eq!(
        compiled.map_witness(&witness(&other, e.entries())).err(),
        Some(jali::Error::Witness)
    );
    // the layouts are those of the sets: R_Tag does not compile against the iss set
    assert!(
        r_tag(&a, &entries(&id))
            .unwrap()
            .compile(sets.iss.clone())
            .is_err()
    );
}

/// Wall-clock costs of the tag stage's functions (one thread, this machine). A measurement aid
/// for the notes, not a benchmark (`benches/lattice.rs` has those): run in release with
/// `--ignored --nocapture`.
#[test]
#[ignore = "timing probe; run in release with --ignored --nocapture"]
fn timing_probe() {
    use std::time::Instant;
    let mut rng = StdRng::seed_from_u64(0x7a65);
    let reps = 50u32;
    let t = Instant::now();
    let mut x0 = x0_of(DEPLOYMENT);
    for i in 0..reps {
        x0 = x0_of(&[DEPLOYMENT, &i.to_le_bytes()].concat());
    }
    let h_mat_time = t.elapsed() / reps;
    let key = LWR.keygen(&mut rng);
    let t = Instant::now();
    let mut acc = 0u32;
    for _ in 0..reps * 20 {
        let (tag, e) = LWR.eval_with_error(&key, &x0).unwrap();
        acc = acc
            .wrapping_add(u32::from(tag.entries()[0]))
            .wrapping_add(e.entries()[0] as u32);
    }
    let eval_time = t.elapsed() / (reps * 20);
    let t = Instant::now();
    for _ in 0..reps * 20 {
        acc = acc.wrapping_add(u32::from(LWR.keygen(&mut rng).coeffs()[0] as u8));
    }
    let keygen_time = t.elapsed() / (reps * 20);
    // the SHAKE128 share of H_mat: squeezing the 458,752 bytes a matrix reads on average
    let t = Instant::now();
    let mut buf = vec![0u8; 458_752];
    for i in 0..reps {
        use shake::{ExtendableOutput, Shake128, Update, XofReader};
        let mut h = Shake128::default();
        h.update(&i.to_le_bytes());
        h.finalize_xof().read(&mut buf);
        acc = acc.wrapping_add(u32::from(buf[i as usize]));
    }
    let shake_time = t.elapsed() / reps;
    println!(
        "H_mat (one matrix): {h_mat_time:?} (of which raw SHAKE128 output: {shake_time:?}); TagEval \
         with error: {eval_time:?}; TagKeyGen: {keygen_time:?} (checksum {acc})"
    );
}
