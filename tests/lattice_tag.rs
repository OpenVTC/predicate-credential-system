//! The short-key `Tag_LWR` and the oracles of the lattice instantiation through the public API
//! (feature `lattice`): the tag chain of `UKeyGen`, `Attest` and `Prove` (construction.tex,
//! con:124-125, con:134, con:157), and the agreement of the tag evaluation with the tag clauses
//! as Jali checks them in the statement `R_issue`, built exactly as the validation harness
//! builds it (`pcs-128-v2/setR/harness/src/rel.rs:44-118`, the layout the embedded parameter set
//! was derived for).
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
        D, E_BOUND, E_COUNT, E_DEG, GAMMA, M, Q, Q_T, Rq, Ternary,
        oracles::{h0, identity_point, pred_enc, tag_point},
        sets::ParameterSets,
    },
    pcs::Predicate,
};
use rand::{SeedableRng, rngs::StdRng};

const DEPLOYMENT: &[u8] = b"lattice-tag integration tests";

/// The tag chain of one recipient and three attesters (con:124-125, con:134, con:157): the
/// recipient's identifier at `c_0`, the attester point `s = H_0(⟨id⟩)` that every party derives
/// from the public identifier alone, the attester tags and the self-exclusion tag. The tags are
/// pairwise distinct, valid, and each is explained by its own key only.
#[test]
fn the_tag_chain_of_an_issuance() {
    let mut rng = StdRng::seed_from_u64(0x7a61);
    let tag = LWR;
    let c0 = identity_point(DEPLOYMENT);
    let usk = tag.keygen(&mut rng);
    let id = tag.eval(&usk, &c0).unwrap();
    // a verifier re-derives c_0 and s from the deployment label and the public identifier
    assert_eq!(identity_point(DEPLOYMENT), c0);
    let s = tag_point(DEPLOYMENT, &id);
    assert_eq!(h0(DEPLOYMENT, &id.to_bytes()), s);
    assert_ne!(s, c0);

    let attesters: Vec<Ternary> = (0..3).map(|_| tag.keygen(&mut rng)).collect();
    let mut tags: Vec<(LWRTag, RoundingError)> = attesters
        .iter()
        .map(|k| tag.eval_with_error(k, &s).unwrap())
        .collect();
    let (t0, e1) = tag.eval_with_error(&usk, &s).unwrap();
    tags.push((t0.clone(), e1));
    // ValidTag on every tag (con:152, con:171), pairwise distinct (CheckAtts_P), T_0 not among
    // the attester tags (self-exclusion)
    assert!(tag.valid_tag(&id));
    for (i, (t, _)) in tags.iter().enumerate() {
        assert!(tag.valid_tag(t));
        for (u, _) in &tags[i + 1..] {
            assert_ne!(t, u);
        }
    }
    let keys: Vec<&Ternary> = attesters.iter().chain([&usk]).collect();
    for (i, key) in keys.iter().enumerate() {
        for (j, (t, e)) in tags.iter().enumerate() {
            assert_eq!(tag.explains(key, &s, t, e), i == j, "key {i}, tag {j}");
        }
    }
    // self-attestation is caught: the recipient's own "attester tag" IS the self-exclusion tag
    assert_eq!(tag.eval(&usk, &s).unwrap(), t0);
    // tags are bound to the identifier: the same attester at another recipient's point
    let other_id = tag.eval(&tag.keygen(&mut rng), &c0).unwrap();
    let other_s = tag_point(DEPLOYMENT, &other_id);
    assert_ne!(tag.eval(&attesters[0], &other_s).unwrap(), tags[0].0);
    // and to the deployment
    assert_ne!(
        tag.eval(&usk, &identity_point(b"another deployment"))
            .unwrap(),
        id
    );
}

/// Every 336-byte string is a canonical tag (`ValidTag` is a type invariant at `p = 2^16`,
/// bb:232), and a tag survives the crate's canonical encoding.
#[test]
fn every_tag_encoding_is_canonical() {
    use predicate_credential_system::serialization::{from_bytes, to_bytes};
    let mut rng = StdRng::seed_from_u64(0x7a62);
    let id = LWR
        .eval(&LWR.keygen(&mut rng), &identity_point(DEPLOYMENT))
        .unwrap();
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

/// `EncPred` through the public API: deterministic, binary by type, and injective on the
/// predicates a deployment would use.
#[test]
fn predicate_encodings_differ() {
    let predicates = [
        Predicate::new(1, "members"),
        Predicate::new(2, "members"),
        Predicate::new(1, "member"),
        Predicate::root("members"),
        Predicate::root(""),
    ];
    let phis: Vec<_> = predicates.iter().map(|f| pred_enc(DEPLOYMENT, f)).collect();
    for (i, phi) in phis.iter().enumerate() {
        assert_eq!(&pred_enc(DEPLOYMENT, &predicates[i]), phi);
        assert!((0..D).all(|c| phi.coefficient(c) <= 1));
        for other in &phis[i + 1..] {
            assert_ne!(phi, other);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Agreement with Jali's tag clauses (R_issue as in harness/src/rel.rs:44-118)
// ---------------------------------------------------------------------------------------------

/// The representative of `x` modulo `m` in `(−m/2, m/2]` (harness `common::centred`).
fn centred(x: i128, m: i128) -> i128 {
    let r = x.rem_euclid(m);
    if r > m / 2 { r - m } else { r }
}

/// `lift_c` of rel.rs:36-38: an element of `R_q` with centred coefficients.
fn lift(ring: &Arc<Ring>, x: &Rq) -> Poly {
    let c = x
        .coeffs()
        .iter()
        .map(|&v| centred(i128::from(v), i128::from(Q)))
        .collect();
    Poly::new(ring.clone(), c).unwrap()
}

/// rel.rs:47-60: clause `j` is `ct(σ(a_j) usk + X^{-8 (j mod 128)} e_{⌊j/128⌋}) − γ T_j = 0`
/// modulo `q_t`, with the tag entries as raw integers (so that a test can pass `T + p`).
fn tag_clauses(
    st: &mut Statement,
    rt: &Arc<Ring>,
    e_name: &str,
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
            .add(&st.coefficient_in(rt, e_name, j / E_DEG, j % E_DEG)?)?
            .add(&st.constant_in(Poly::constant(rt.clone(), -i128::from(GAMMA) * tj))?)?;
        st.const_coeff_zero(clause)?;
    }
    Ok(())
}

/// `R_issue` (rel.rs:99-118) with two tags: `C = b_u usk + B_r x_0`, `id` at `c_0` (error
/// `e0`), `T_0` at `s` (error `e1`). Block names, order and norms as the parameter set expects.
fn r_issue(
    b_u: &Rq,
    b_r: &[Rq; 2],
    c: &Rq,
    tags: [(&TagMatrix, &[i128]); 2],
) -> Result<Statement, jali::Error> {
    let rc = Ring::new(i128::from(Q), D)?;
    let rt = Ring::new(i128::from(Q_T), D)?;
    let mut st = Statement::new(rc.clone());
    st.var("usk", 1, Norm::LinfExact(1))?;
    st.var("x0", 2, Norm::LinfExact(1))?;
    for name in ["e0", "e1"] {
        st.var_subring(
            name,
            E_COUNT,
            E_DEG,
            Norm::LinfExact(E_BOUND),
            Placement::Ajtai,
        )?;
    }
    let mut com = st.variable_in(&rc, "usk", 0)?.scale(&lift(&rc, b_u))?;
    for (k, b) in b_r.iter().enumerate() {
        com = com.add(&st.variable_in(&rc, "x0", k)?.scale(&lift(&rc, b))?)?;
    }
    com = com.add(&st.constant_in(lift(&rc, c).neg())?)?;
    st.eq_mod_p(com)?;
    for (name, (a, t)) in ["e0", "e1"].into_iter().zip(tags) {
        tag_clauses(&mut st, &rt, name, a, t)?;
    }
    Ok(st)
}

/// `e_subring` of harness/src/pcs.rs:145-153: entry `j` is coefficient `8 (j mod 128)` of
/// element `⌊j/128⌋`.
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

/// The witness check of Jali's prover accepts `(usk, x_0, e0, e1)` for the tags of
/// [`LWR::eval_with_error`] in `R_issue` compiled with the embedded `issue` set, and refuses the
/// shifted tag `T + 1` (with its honest error, and with the error `e + γ` outside the exact
/// bound), a non-canonical `T + p` with the honest witness only through the relation (the
/// public `ValidTag` is what refuses it), and a perturbed error.
#[test]
fn jali_accepts_the_tags_and_errors_of_the_evaluation() {
    let mut rng = StdRng::seed_from_u64(0x7a63);
    let sets = ParameterSets::load().unwrap();
    let rc = Ring::new(i128::from(Q), D).unwrap();
    // public data: any elements of R_q (the parameter set covers the worst case)
    let uniform = |rng: &mut StdRng| {
        let c: Vec<i64> = (0..D)
            .map(|_| i64::from(rand::Rng::gen_range(rng, 0..Q)))
            .collect();
        Rq::from_i64(&c).unwrap()
    };
    let (b_u, b_r) = (uniform(&mut rng), [uniform(&mut rng), uniform(&mut rng)]);
    let usk = LWR.keygen(&mut rng);
    let x0 = [Ternary::sample(&mut rng), Ternary::sample(&mut rng)];
    let c = b_u
        .mul(&usk.to_rq())
        .add(&b_r[0].mul(&x0[0].to_rq()))
        .add(&b_r[1].mul(&x0[1].to_rq()));
    let c0 = identity_point(DEPLOYMENT);
    let (id, e0) = LWR.eval_with_error(&usk, &c0).unwrap();
    let s = tag_point(DEPLOYMENT, &id);
    let (t0, e1) = LWR.eval_with_error(&usk, &s).unwrap();

    let witness = |e0: &[i8; M], e1: &[i8; M]| {
        BTreeMap::from([
            ("usk".to_string(), vec![ternary_poly(&rc, &usk)]),
            (
                "x0".to_string(),
                x0.iter().map(|x| ternary_poly(&rc, x)).collect(),
            ),
            ("e0".to_string(), e_subring(&rc, e0)),
            ("e1".to_string(), e_subring(&rc, e1)),
        ])
    };
    // one compilation per statement (a compilation costs about as much as all witness checks)
    let compile = |id_entries: &[i128], t0_entries: &[i128]| {
        r_issue(&b_u, &b_r, &c, [(&c0, id_entries), (&s, t0_entries)])
            .and_then(|st| st.compile(sets.issue.clone()))
            .unwrap()
    };
    let (id_t, t0_t) = (entries(&id), entries(&t0));
    let honest = compile(&id_t, &t0_t);
    assert!(
        honest
            .map_witness(&witness(e0.entries(), e1.entries()))
            .is_ok()
    );
    // a perturbed error in the identifier's clauses
    let mut e_bad = *e0.entries();
    e_bad[M - 1] = if e_bad[M - 1] == 7 {
        6
    } else {
        e_bad[M - 1] + 1
    };
    assert_eq!(
        honest.map_witness(&witness(&e_bad, e1.entries())).err(),
        Some(jali::Error::Witness)
    );

    // T_0 + 1 in one row: the honest error no longer satisfies the clause ...
    let mut shifted = t0_t.clone();
    shifted[5] += 1;
    let shifted = compile(&id_t, &shifted);
    assert_eq!(
        shifted
            .map_witness(&witness(e0.entries(), e1.entries()))
            .err(),
        Some(jali::Error::Witness)
    );
    // ... and the error that would (e + γ) is outside the exact bound 7
    let mut e_shifted = *e1.entries();
    e_shifted[5] += 15;
    assert!(e_shifted[5] > 7);
    assert_eq!(
        shifted
            .map_witness(&witness(e0.entries(), &e_shifted))
            .err(),
        Some(jali::Error::Witness)
    );

    // the non-canonical encoding T + p (bb:232) has exactly the witnesses of T: the relation
    // alone does not refuse it, which is why every verifier checks ValidTag first (con:171)
    let mut lifted = t0_t.clone();
    lifted[0] += 1 << 16;
    assert!(
        compile(&id_t, &lifted)
            .map_witness(&witness(e0.entries(), e1.entries()))
            .is_ok()
    );
}

/// Wall-clock costs of the tag stage's functions (one thread, this machine). A measurement aid
/// for the notes, not a benchmark (`benches/lattice.rs` has those): run in release with
/// `--ignored --nocapture`.
#[test]
#[ignore = "timing probe; run in release with --ignored --nocapture"]
fn timing_probe() {
    use std::time::Instant;
    let mut rng = StdRng::seed_from_u64(0x7a64);
    let reps = 50u32;
    let t = Instant::now();
    let mut c0 = identity_point(DEPLOYMENT);
    for i in 0..reps {
        c0 = identity_point(&[DEPLOYMENT, &i.to_le_bytes()].concat());
    }
    let h0_time = t.elapsed() / reps;
    let key = LWR.keygen(&mut rng);
    let t = Instant::now();
    let mut acc = 0u32;
    for _ in 0..reps * 20 {
        let (tag, e) = LWR.eval_with_error(&key, &c0).unwrap();
        acc = acc
            .wrapping_add(u32::from(tag.entries()[0]))
            .wrapping_add(e.entries()[0] as u32);
    }
    let eval_time = t.elapsed() / (reps * 20);
    let t = Instant::now();
    for i in 0..reps * 20 {
        let phi = pred_enc(DEPLOYMENT, &Predicate::new(i, "members"));
        acc = acc.wrapping_add(u32::from(phi.as_bytes()[0]));
    }
    let pred_time = t.elapsed() / (reps * 20);
    let t = Instant::now();
    for _ in 0..reps * 20 {
        acc = acc.wrapping_add(u32::from(LWR.keygen(&mut rng).coeffs()[0] as u8));
    }
    let keygen_time = t.elapsed() / (reps * 20);
    // the SHAKE128 share of H_0: squeezing the 458,752 bytes a matrix reads on average
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
        "H_0 (one matrix): {h0_time:?} (of which raw SHAKE128 output: {shake_time:?}); TagEval \
         with error: {eval_time:?}; EncPred: {pred_time:?}; TagKeyGen: {keygen_time:?} \
         (checksum {acc})"
    );
}
