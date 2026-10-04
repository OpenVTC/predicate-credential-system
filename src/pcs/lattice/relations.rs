//! The relations `R_att` and `R_issue` of the lattice construction in Jali's statement API,
//! ported EXACTLY from the validated harness (`pcs-128-v2/setR/harness/src/rel.rs:36-153` and
//! `pcs.rs:145-153`): the parameter sets of [`crate::lattice::sets`] were derived for these
//! layouts, and Jali's `compile` refuses any other ("compiled witness dimensions").
//!
//! **`R_att`** over $`\mathbb Z_q[X]/(X^{1024} + 1)`$, blocks in this order:
//!
//! | name | count | norm | placement |
//! |---|---|---|---|
//! | `s` | 2 | `L2Squared(90,803,788,942)` | **BDLOP** |
//! | `x1` | 1 | `LinfExact(1)` | Ajtai |
//! | `usk` | 1 | `LinfExact(1)` | Ajtai |
//! | `x0` | 2 | `LinfExact(1)` | Ajtai |
//! | `e` | 2, subring degree 128 | `LinfExact(7)` | Ajtai |
//!
//! constraints: one `eq_mod_p` over $`\mathbb Z_q`$,
//! $`(s_0 + h s_1 - b_u\,usk - \sum_k b_{r,k} x_{0,k} - b_\phi\phi)\cdot(v - x_1) - 1 = 0`$ (the
//! constant $`b_\phi\phi`$ computed in $`R_q`$), then for $`j < 168`$ one `const_coeff_zero` over
//! $`\mathbb Z_{q_t}`$, $`\mathrm{ct}(\sigma(a_j)\,usk + X^{-8(j \bmod 128)} e_{\lfloor j/128\rfloor} - \gamma T_j) = 0`$
//! with $`\sigma(a_j)`$ = `Poly::auto` of row $`j`$ lifted centred. Since
//! $`\mathrm{ct}(\sigma(a)\,u) = \langle a, u\rangle`$, clause $`j`$ is
//! $`\langle a_j, usk\rangle + e_j = \gamma T_j \bmod q_t`$, the tag relation of bb:247.
//!
//! **`R_issue`** (and the root flow) over $`\mathbb Z_q[X]/(X^{1024} + 1)`$: blocks `usk` (1,
//! `LinfExact(1)`), `x0` (2, `LinfExact(1)`), `e0`, `e1` (2 each, subring degree 128,
//! `LinfExact(7)`), all Ajtai; constraints `eq_mod_p`$`(b_u\,usk + \sum_k b_{r,k} x_{0,k} - C)`$,
//! then the 168 tag clauses at $`(c_0, id)`$ on `e0` and the 168 at $`(s_i, id_{i \to i})`$ on `e1`.
//!
//! Witness maps: `s` = $`(s_0, s_1)`$, `x1`, `usk`, `x0` as statement-ring polynomials of their
//! integer coefficients; a rounding-error vector $`e \in [-7, 7]^{168}`$ as two elements with
//! $`e_j`$ at coefficient $`8(j \bmod 128)`$ of element $`\lfloor j / 128\rfloor`$ (Jali's witness
//! map refuses nonzero coefficients outside the subring).
//!
//! The norms are all EXACT (`L2Squared`, `LinfExact`; never Jali's approximate `Norm::Linf`), so
//! by Jali's design a verified proof bounds every extracted block by its declared bound
//! (`Compiled::extraction_bound` returns the declared bound for exact norms). That is a property
//! Jali's design claims, not a proven theorem: Jali's knowledge soundness under Fiat-Shamir is
//! not written out, and its extraction rewinds where the paper assumes an online extractor
//! ([`super`], "What the paper claims"). For the rounding errors this is what
//! rem:relaxed-extraction (con:213-215) requires: with $`\|e\|_\infty \le \lfloor\gamma/2\rfloor`$
//! a key explains at most one valid tag per matrix (lem:tag-lwr-determinism, bb:282-287).
//!
//! **What the relation does not check.** The constants are reduced modulo the modulus of their
//! constraint, so the public checks of the verifier stay essential (con:151-152, con:171): a
//! non-canonical tag $`T + pz`$ has exactly the witnesses of $`T`$ (bb:232), and a non-binary
//! $`\phi`$ admits the credential-free witness $`s = 0`$ of the proof of lem:base-vsis. The types
//! of the construction cannot represent either ([`LWRTag`],
//! [`BinaryPoly`](crate::lattice::BinaryPoly)); the builders here take raw values so that the
//! unit tests can show both effects on the relation itself.
//!
//! **Seed bridge.** Every proof gets a fresh 32-byte seed from the caller's RNG
//! (`lattice::fresh_seed`) for `Compiled::prove_bytes_with_seed`; a `RestartLimit` is retried
//! with a new fresh seed, at most [`MAX_PROOF_ATTEMPTS`] times.

use std::{collections::BTreeMap, sync::Arc};

use ark_std::rand::{CryptoRng, RngCore};
use jali::{
    math::{Poly, Ring},
    params::TboxParams,
    statement::{Norm, Placement, Statement},
};

use super::types::PublicParameters;
use crate::{
    error::Error,
    kiprf::lwr::{LWRTag, RoundingError, TagMatrix},
    lattice::{
        BETA_R, BETA_U, BETA_X, D, E_BOUND, E_COUNT, E_DEG, ELL_R, GAMMA, M, Q, Q_T, Rq, S_BOUND,
        Ternary, fresh_seed, jali_error,
    },
};

/// Attempts of a proof with fresh seeds before a `RestartLimit` of Jali is reported as
/// [`Error::LatticeBackend`].
pub(crate) const MAX_PROOF_ATTEMPTS: usize = 3;

/// The names of the rounding-error blocks of `R_issue`, in declaration order (rel.rs:96).
const E_NAMES: [&str; 2] = ["e0", "e1"];

/// A witness: named blocks of statement-ring polynomials. Jali's [`Poly`] wipes its
/// coefficients on drop, so a dropped witness leaves no copy of its values in the heap.
pub(crate) type Witness = BTreeMap<String, Vec<Poly>>;

// The layouts below are those of the parameter sets: two components of s (w = 2), ℓ_r = 2, and
// the 168 rounding errors in two subring elements of degree 128.
const _: () = assert!(ELL_R == 2 && E_COUNT == 2 && E_DEG == 128 && M == 168);

/// The representative of `x ∈ [0, m)` in $`(-m/2, m/2]`$ (the harness's `centred`).
fn centred(x: u32, m: u32) -> i128 {
    let (x, m) = (i128::from(x), i128::from(m));
    if x > m / 2 { x - m } else { x }
}

/// The two rings of the statements, built once per [`super::LatticePCS`]: the statement ring
/// $`\mathbb Z_q[X]/(X^{1024}+1)`$ and the tag ring $`\mathbb Z_{q_t}[X]/(X^{1024}+1)`$, over
/// which the tag clauses are built (`variable_in`, `constant_in`).
#[derive(Clone, Debug)]
pub(crate) struct Rings {
    /// $`\mathbb Z_q[X]/(X^{1024}+1)`$, $`q = 1{,}048{,}573`$.
    pub(crate) c: Arc<Ring>,
    /// $`\mathbb Z_{q_t}[X]/(X^{1024}+1)`$, $`q_t = 983{,}040`$.
    pub(crate) t: Arc<Ring>,
}

impl Rings {
    pub(crate) fn new() -> Result<Self, Error> {
        Ok(Self {
            c: Ring::new(i128::from(Q), D).map_err(jali_error)?,
            t: Ring::new(i128::from(Q_T), D).map_err(jali_error)?,
        })
    }
}

/// `lift_c` of rel.rs:36-38: an element of $`R_q`$ as a statement-ring polynomial of its centred
/// coefficients.
fn lift(ring: &Arc<Ring>, x: &Rq) -> Result<Poly, jali::Error> {
    Poly::new(
        ring.clone(),
        x.coeffs().iter().map(|&v| centred(v, Q)).collect(),
    )
}

/// The polynomial of `ring` with the integer coefficients `values` (exactly $`d`$ of them). Jali
/// wipes the input vector after the reduction.
pub(crate) fn int_poly(
    ring: &Arc<Ring>,
    values: impl IntoIterator<Item = i128>,
) -> Result<Poly, Error> {
    Poly::new(ring.clone(), values.into_iter().collect()).map_err(jali_error)
}

/// A ternary polynomial as a statement-ring polynomial (witness map of rel.rs:131-153).
pub(crate) fn ternary_poly(ring: &Arc<Ring>, x: &Ternary) -> Result<Poly, Error> {
    int_poly(ring, x.coeffs().iter().map(|&c| i128::from(c)))
}

/// `e_subring` of pcs.rs:145-153: the rounding errors as [`E_COUNT`] elements of the subring of
/// degree [`E_DEG`], with $`e_j`$ at coefficient $`(1024/128)\,(j \bmod 128)`$ of element
/// $`\lfloor j/128\rfloor`$ (statement-ring polynomials).
pub(crate) fn e_subring(ring: &Arc<Ring>, e: &[i8; M]) -> Result<Vec<Poly>, Error> {
    let stride = D / E_DEG;
    let mut out = vec![vec![0i128; D]; E_COUNT];
    for (j, &x) in e.iter().enumerate() {
        out[j / E_DEG][stride * (j % E_DEG)] = i128::from(x);
    }
    // `Poly::new` wipes each vector it consumes
    out.into_iter()
        .map(|c| Poly::new(ring.clone(), c).map_err(jali_error))
        .collect()
}

/// The entries of a tag as the integers the tag clauses use. The builders take raw `i128`
/// values (rel.rs:56: the constant is $`-\gamma T_j`$), so that a test can pass the non-canonical
/// $`T + p`$, which no [`LWRTag`] represents.
pub(crate) fn tag_values(tag: &LWRTag) -> [i128; M] {
    tag.entries().map(i128::from)
}

/// The rows $`\sigma(a_0), \dots, \sigma(a_{m-1})`$ of a tag matrix as tag-ring polynomials: row
/// $`j`$ lifted centred, then `Poly::auto` (rel.rs:51). Built once per matrix: for $`c_0`$ once
/// per [`super::LatticePCS`], for $`s_i = H_0(\langle id_i\rangle)`$ once per call, shared by the
/// $`k`$ attestations and $`\pi_0`$.
#[derive(Clone, Debug)]
pub(crate) struct TagRows(Vec<Poly>);

impl TagRows {
    pub(crate) fn new(rings: &Rings, a: &TagMatrix) -> Result<Self, Error> {
        a.rows()
            .map(|row| {
                Poly::new(
                    rings.t.clone(),
                    row.iter().map(|&x| centred(x, Q_T)).collect(),
                )
                .map(|p| p.auto())
                .map_err(jali_error)
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Self)
    }
}

/// What every statement of a deployment shares, built once per [`super::LatticePCS`]: the rings,
/// the public elements of `pp_Σ` lifted to the statement ring (with the negations the builders
/// use), and the rows of $`c_0`$.
#[derive(Clone, Debug)]
pub(crate) struct Constants {
    pub(crate) rings: Rings,
    /// $`v`$.
    v: Poly,
    /// $`b_u`$ and $`-b_u`$.
    b_u: Poly,
    neg_b_u: Poly,
    /// $`B_r`$ and $`-B_r`$.
    b_r: [Poly; ELL_R],
    neg_b_r: [Poly; ELL_R],
    /// The rows of $`c_0 = H_0(\texttt{"identity"})`$.
    pub(crate) c0: TagRows,
}

impl Constants {
    pub(crate) fn new(pp: &PublicParameters) -> Result<Self, Error> {
        let rings = Rings::new()?;
        let sigma = &pp.pp_sigma;
        let lifted = |x: &Rq| lift(&rings.c, x).map_err(jali_error);
        let v = lifted(sigma.v())?;
        let b_u = lifted(sigma.b_u())?;
        let b_r = [lifted(&sigma.b_r()[0])?, lifted(&sigma.b_r()[1])?];
        let c0 = TagRows::new(&rings, &pp.c0)?;
        Ok(Self {
            v,
            neg_b_u: b_u.neg(),
            neg_b_r: [b_r[0].neg(), b_r[1].neg()],
            b_u,
            b_r,
            c0,
            rings,
        })
    }
}

/// rel.rs:61-65: a rounding-error block, two subring elements of degree [`E_DEG`] (the proof
/// degree) with the exact bound $`\lfloor\gamma/2\rfloor = 7`$, in the Ajtai part.
fn declare_e(st: &mut Statement, name: &str) -> Result<(), jali::Error> {
    st.var_subring(
        name,
        E_COUNT,
        E_DEG,
        Norm::LinfExact(E_BOUND),
        Placement::Ajtai,
    )?;
    Ok(())
}

/// rel.rs:44-60: for every row $`j`$, the clause
/// $`\mathrm{ct}(\sigma(a_j)\,usk + X^{-8(j \bmod 128)} e_{\lfloor j/128\rfloor} - \gamma T_j) = 0 \bmod q_t`$
/// over the tag ring, on the block `e_name`.
fn tag_clauses(
    st: &mut Statement,
    rt: &Arc<Ring>,
    e_name: &str,
    rows: &TagRows,
    tag: &[i128; M],
) -> Result<(), jali::Error> {
    for (j, (a, &tj)) in rows.0.iter().zip(tag).enumerate() {
        let clause = st
            .variable_in(rt, "usk", 0)?
            .scale(a)?
            .add(&st.coefficient_in(rt, e_name, j / E_DEG, j % E_DEG)?)?
            .add(&st.constant_in(Poly::constant(rt.clone(), -i128::from(GAMMA) * tj))?)?;
        st.const_coeff_zero(clause)?;
    }
    Ok(())
}

/// `R_att` (rel.rs:67-94) for the public statement $`(h, b_\phi\phi, s_i, T)`$: `h` is the helper
/// key, `bphi_phi` the constant $`b_\phi\phi \in R_q`$ (an [`Rq`], so that a test can pass the
/// non-binary $`\phi`$ of the forgery of lem:base-vsis), `rows` the rows of the attester point
/// $`s_i`$ and `tag` the entries of $`T = id_{j \to i}`$.
pub(crate) fn r_att(
    k: &Constants,
    h: &Rq,
    bphi_phi: &Rq,
    rows: &TagRows,
    tag: &[i128; M],
) -> Result<Statement, Error> {
    build_att(k, h, bphi_phi, rows, tag).map_err(jali_error)
}

fn build_att(
    k: &Constants,
    h: &Rq,
    bphi_phi: &Rq,
    rows: &TagRows,
    tag: &[i128; M],
) -> Result<Statement, jali::Error> {
    let rc = &k.rings.c;
    let mut st = Statement::new(rc.clone());
    st.var_placed("s", 2, Norm::L2Squared(S_BOUND), Placement::Bdlop)?;
    st.var("x1", 1, Norm::LinfExact(BETA_X))?;
    st.var("usk", 1, Norm::LinfExact(BETA_U))?;
    st.var("x0", ELL_R, Norm::LinfExact(BETA_R))?;
    declare_e(&mut st, "e")?;
    // r = A s - b_u usk - B_r x_0 - b_phi phi with A = [1 | h], g = v - x_1.
    let a = [Poly::constant(rc.clone(), 1), lift(rc, h)?];
    let mut r = st.constant_in(Poly::zero(rc.clone()))?;
    for (i, a) in a.iter().enumerate() {
        r = r.add(&st.variable_in(rc, "s", i)?.scale(a)?)?;
    }
    r = r.add(&st.variable_in(rc, "usk", 0)?.scale(&k.neg_b_u)?)?;
    for (i, b) in k.neg_b_r.iter().enumerate() {
        r = r.add(&st.variable_in(rc, "x0", i)?.scale(b)?)?;
    }
    r = r.add(&st.constant_in(lift(rc, bphi_phi)?.neg())?)?;
    let g = st.constant_in(k.v.clone())?.add(
        &st.variable_in(rc, "x1", 0)?
            .scale(&Poly::constant(rc.clone(), -1))?,
    )?;
    let possession = r
        .product_affine(&g)?
        .add(&st.constant_in(Poly::constant(rc.clone(), -1))?)?;
    st.eq_mod_p(possession)?;
    tag_clauses(&mut st, &k.rings.t, "e", rows, tag)?;
    Ok(st)
}

/// `R_issue` (rel.rs:98-118) with its two tag clauses, for the public statement
/// $`(C, (c_0, id), (s_i, id_{i \to i}))`$: `c` is the issuance encoding, `tags` the rows and
/// entries of the identifier at $`c_0`$ (block `e0`) and of the self-exclusion tag at $`s_i`$
/// (block `e1`). The same relation serves issuance proofs and root requests; their contexts and
/// parameter sets differ.
pub(crate) fn r_issue(
    k: &Constants,
    c: &Rq,
    tags: [(&TagRows, &[i128; M]); 2],
) -> Result<Statement, Error> {
    build_issue(k, c, tags).map_err(jali_error)
}

fn build_issue(
    k: &Constants,
    c: &Rq,
    tags: [(&TagRows, &[i128; M]); 2],
) -> Result<Statement, jali::Error> {
    let rc = &k.rings.c;
    let mut st = Statement::new(rc.clone());
    st.var("usk", 1, Norm::LinfExact(BETA_U))?;
    st.var("x0", ELL_R, Norm::LinfExact(BETA_R))?;
    for name in E_NAMES {
        declare_e(&mut st, name)?;
    }
    let mut com = st.variable_in(rc, "usk", 0)?.scale(&k.b_u)?;
    for (i, b) in k.b_r.iter().enumerate() {
        com = com.add(&st.variable_in(rc, "x0", i)?.scale(b)?)?;
    }
    com = com.add(&st.constant_in(lift(rc, c)?.neg())?)?;
    st.eq_mod_p(com)?;
    for (name, (rows, tag)) in E_NAMES.into_iter().zip(tags) {
        tag_clauses(&mut st, &k.rings.t, name, rows, tag)?;
    }
    Ok(st)
}

/// The witness of `R_att` (rel.rs:131-141) from its statement-ring polynomials: `s` =
/// $`(s_0, s_1)`$, `x1`, `usk`, `x0` and the rounding errors `e` ([`e_subring`]).
pub(crate) fn att_witness(
    s: [Poly; 2],
    x1: Poly,
    usk: Poly,
    x0: [Poly; ELL_R],
    e: Vec<Poly>,
) -> Witness {
    BTreeMap::from([
        ("s".to_string(), s.into()),
        ("x1".to_string(), vec![x1]),
        ("usk".to_string(), vec![usk]),
        ("x0".to_string(), x0.into()),
        ("e".to_string(), e),
    ])
}

/// The witness of `R_issue` (rel.rs:142-153): `usk`, `x0` and the rounding errors of the two tag
/// clauses, `e0` at $`c_0`$ and `e1` at $`s_i`$.
pub(crate) fn issue_witness(usk: Poly, x0: [Poly; ELL_R], e: [Vec<Poly>; 2]) -> Witness {
    let mut w = BTreeMap::from([
        ("usk".to_string(), vec![usk]),
        ("x0".to_string(), x0.into()),
    ]);
    for (name, e) in E_NAMES.into_iter().zip(e) {
        w.insert(name.to_string(), e);
    }
    w
}

/// The typed witness of `R_issue`: `usk`, $`x_0`$ and the rounding errors of $`id`$ at $`c_0`$
/// and of $`id_{i \to i}`$ at $`s_i`$.
pub(crate) fn issue_witness_of(
    rings: &Rings,
    usk: &Ternary,
    x0: &[Ternary; ELL_R],
    e0: &RoundingError,
    e1: &RoundingError,
) -> Result<Witness, Error> {
    let rc = &rings.c;
    Ok(issue_witness(
        ternary_poly(rc, usk)?,
        [ternary_poly(rc, &x0[0])?, ternary_poly(rc, &x0[1])?],
        [e_subring(rc, e0.entries())?, e_subring(rc, e1.entries())?],
    ))
}

/// Compiles `statement` against `params` and proves it for `witness` under `context`: the seed
/// bridge. Each attempt draws a FRESH 32-byte seed from `rng` (`Compiled::prove_bytes_with_seed`;
/// the seed buffer is wiped on drop, Jali wipes its copy), and a `RestartLimit` is retried with a
/// new seed, at most [`MAX_PROOF_ATTEMPTS`] times.
///
/// # Errors
/// [`Error::WitnessDoesNotSatisfyRelation`] if Jali's witness map refuses the witness (the honest
/// prover's check: a norm, a subring position, or a constraint); [`Error::LatticeBackend`] if
/// the statement does not compile against the set, or after [`MAX_PROOF_ATTEMPTS`] restarts.
pub(crate) fn prove<R: RngCore + CryptoRng + ?Sized>(
    statement: &Statement,
    params: &TboxParams,
    pp_seed: [u8; 32],
    witness: &Witness,
    context: &[u8],
    rng: &mut R,
) -> Result<Vec<u8>, Error> {
    let compiled = statement.compile(params.clone()).map_err(jali_error)?;
    for _ in 0..MAX_PROOF_ATTEMPTS {
        let seed = fresh_seed(rng);
        match compiled.prove_bytes_with_seed(pp_seed, witness, context, *seed) {
            Err(jali::Error::RestartLimit) => {}
            result => return result.map_err(jali_error),
        }
    }
    Err(Error::LatticeBackend(format!(
        "jali: the prover exhausted its restarts with {MAX_PROOF_ATTEMPTS} fresh seeds"
    )))
}

/// Compiles `statement` against `params` and verifies the proof `bytes` under `context`.
///
/// # Errors
/// [`Error::InvalidProof`] if Jali rejects the proof or its encoding;
/// [`Error::LatticeBackend`] if the statement does not compile (it always does for the
/// statements of this module).
pub(crate) fn verify(
    statement: &Statement,
    params: &TboxParams,
    pp_seed: [u8; 32],
    bytes: &[u8],
    context: &[u8],
) -> Result<(), Error> {
    let compiled = statement.compile(params.clone()).map_err(jali_error)?;
    compiled
        .verify_bytes(pp_seed, bytes, context)
        .map_err(jali_error)
}

#[cfg(test)]
mod tests {
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        cred::{
            CredentialBase, VSIS,
            vsis::{VSISCredential, VSISHiddenMessage, VSISPublicParams, VSISSigningKey},
        },
        kiprf::{KIPRF, lwr::LWR},
        lattice::{BinaryPoly, P, oracles, sets::ParameterSets},
        pcs::Predicate,
    };

    const LABEL: &[u8] = b"PCS-LATTICE-RELATION-TESTS";

    /// One deployment with ONE real helper key (TrapGen).
    struct Fixture {
        pp: PublicParameters,
        k: Constants,
        sets: ParameterSets,
        h: Rq,
        sk: VSISSigningKey,
        rng: StdRng,
    }

    /// A user key and a credential of the helper on `(usk, φ, x_0)`.
    struct Holder {
        usk: Ternary,
        x0: [Ternary; 2],
        phi: BinaryPoly,
        cred: VSISCredential,
    }

    fn fixture(seed: u64) -> Fixture {
        let mut rng = StdRng::seed_from_u64(seed);
        let pp = PublicParameters::derive(LABEL).unwrap();
        let (vk, sk) = VSIS::keygen(&pp.pp_sigma, &mut rng);
        Fixture {
            k: Constants::new(&pp).unwrap(),
            sets: ParameterSets::load().unwrap(),
            h: vk.h().clone(),
            pp,
            sk,
            rng,
        }
    }

    impl Fixture {
        fn sigma(&self) -> &VSISPublicParams {
            &self.pp.pp_sigma
        }

        fn holder(&mut self) -> Holder {
            let usk = Ternary::sample(&mut self.rng);
            let x0 = [
                Ternary::sample(&mut self.rng),
                Ternary::sample(&mut self.rng),
            ];
            let phi = oracles::pred_enc(LABEL, &Predicate::root("founders"));
            let m_hid = VSISHiddenMessage::new(usk.clone(), x0.clone());
            let m = VSIS::encode_message(&self.pp.pp_sigma, &m_hid, &phi).unwrap();
            let cred = VSIS::sign(&self.pp.pp_sigma, &self.sk, &m, &mut self.rng).unwrap();
            Holder { usk, x0, phi, cred }
        }

        /// The attester point of a fresh recipient, `s = H_0(⟨id⟩)`, and its rows.
        fn scope(&mut self) -> (TagMatrix, TagRows) {
            let usk = Ternary::sample(&mut self.rng);
            let id = LWR.eval(&usk, &self.pp.c0).unwrap();
            let s = oracles::tag_point(LABEL, &id);
            let rows = TagRows::new(&self.k.rings, &s).unwrap();
            (s, rows)
        }

        /// `R_att` with `b_φ φ` computed from a binary `φ`.
        fn att_statement(&self, h: &Rq, phi: &Rq, rows: &TagRows, tag: &[i128; M]) -> Statement {
            r_att(&self.k, h, &self.sigma().b_phi().mul(phi), rows, tag).unwrap()
        }

        /// `map_witness` of the compiled `R_att`: the honest prover's witness check.
        fn att_check(&self, statement: &Statement, w: &Witness) -> Result<(), jali::Error> {
            statement
                .compile(self.sets.att.clone())
                .unwrap()
                .map_witness(w)
                .map(|_| ())
        }
    }

    fn ints(ring: &Arc<Ring>, s: &[i32]) -> Poly {
        int_poly(ring, s.iter().map(|&x| i128::from(x))).unwrap()
    }

    fn tern(ring: &Arc<Ring>, x: &Ternary) -> Poly {
        ternary_poly(ring, x).unwrap()
    }

    fn rq_of(c: &[i128]) -> Rq {
        Rq::from_i64(&c.iter().map(|&x| x as i64).collect::<Vec<_>>()).unwrap()
    }

    /// The witness of `R_att` from typed parts.
    fn witness(
        ring: &Arc<Ring>,
        s0: &[i32],
        s1: &[i32],
        x1: &Ternary,
        usk: &Ternary,
        x0: &[Ternary; 2],
        e: &[i8; M],
    ) -> Witness {
        att_witness(
            [ints(ring, s0), ints(ring, s1)],
            tern(ring, x1),
            tern(ring, usk),
            [tern(ring, &x0[0]), tern(ring, &x0[1])],
            e_subring(ring, e).unwrap(),
        )
    }

    /// The coefficients of `x` with coefficient `i` replaced by `value`.
    fn with_coefficient(x: &Ternary, i: usize, value: i128) -> Vec<i128> {
        let mut c: Vec<i128> = x.coeffs().iter().map(|&v| i128::from(v)).collect();
        c[i] = value;
        c
    }

    /// The harness's `tag_eval` (H/pcs.rs:129-142) on an arbitrary integer key, e.g. one with a
    /// coefficient 2: the rounding error stays within 7 whatever the key's norm.
    fn harness_tag_eval(usk: &[i128], a: &TagMatrix) -> ([i128; M], [i8; M]) {
        let (gamma, pt, qt) = (i128::from(GAMMA), i128::from(P), i128::from(Q_T));
        let mut t = [0i128; M];
        let mut e = [0i8; M];
        for (j, row) in a.rows().enumerate() {
            let w: i128 = row.iter().zip(usk).map(|(&x, y)| i128::from(x) * y).sum();
            t[j] = ((2 * w.rem_euclid(qt) + gamma) / (2 * gamma)).rem_euclid(pt);
            let ej = (gamma * t[j] - w).rem_euclid(qt);
            e[j] = (if ej > qt / 2 { ej - qt } else { ej }) as i8;
        }
        (t, e)
    }

    /// The statements have the shapes the embedded parameter sets were derived for: each compiles
    /// against its set (`R_issue` against both of its twins) and not against the other one, with
    /// the blocks of the derivation (H/rel.rs; `report-att`: `s` in the BDLOP part).
    #[test]
    fn the_statements_compile_against_their_parameter_sets() {
        let mut f = fixture(0x7e1_0001);
        let holder = f.holder();
        let (s, rows) = f.scope();
        let (tag, _) = LWR.eval_with_error(&holder.usk, &s).unwrap();
        let att = f.att_statement(&f.h, &holder.phi.to_rq(), &rows, &tag_values(&tag));
        assert!(att.compile(f.sets.att.clone()).is_ok());
        assert!(att.compile(f.sets.issue.clone()).is_err());
        let (id, _) = LWR.eval_with_error(&holder.usk, &f.pp.c0).unwrap();
        let c = f.sigma().commitment(&holder.usk, &holder.x0).unwrap();
        let issue = r_issue(
            &f.k,
            &c,
            [(&f.k.c0, &tag_values(&id)), (&rows, &tag_values(&tag))],
        )
        .unwrap();
        assert!(issue.compile(f.sets.issue.clone()).is_ok());
        assert!(issue.compile(f.sets.issue_root.clone()).is_ok());
        assert!(issue.compile(f.sets.att.clone()).is_err());
        let shape: Vec<_> = att
            .blocks(128)
            .unwrap()
            .into_iter()
            .map(|b| (b.name, b.rows, b.norm, b.placement))
            .collect();
        let expected = [
            ("s", 16, Norm::L2Squared(S_BOUND), Placement::Bdlop),
            ("x1", 16, Norm::LinfExact(1), Placement::Ajtai),
            ("usk", 16, Norm::LinfExact(1), Placement::Ajtai),
            ("x0", 32, Norm::LinfExact(1), Placement::Ajtai),
            ("e", 8, Norm::LinfExact(7), Placement::Ajtai),
        ]
        .map(|(n, r, norm, p)| (n.to_string(), r, norm, p));
        assert_eq!(shape, expected);
        let names: Vec<_> = issue
            .blocks(128)
            .unwrap()
            .into_iter()
            .map(|b| (b.name, b.placement))
            .collect();
        assert_eq!(
            names,
            ["usk", "x0", "e0", "e1"].map(|n| (n.to_string(), Placement::Ajtai))
        );
    }

    /// The honest witness of `R_att` satisfies the relation (Jali's witness map accepts it), and
    /// the false witnesses of the harness's main flow (H/flow.rs:337-434) are refused by the
    /// honest prover's check: another key, a shifted tag with its error moved outside the exact
    /// bound, and an `x_1`, a `usk` or an `x_0` with a coefficient 2, each with a real preimage of
    /// the helper key for exactly that message.
    #[test]
    fn honest_attestation_witnesses_pass_and_false_ones_are_refused() {
        let mut f = fixture(0x7e1_0002);
        let holder = f.holder();
        let other = f.holder();
        let (s, rows) = f.scope();
        let ring = f.k.rings.c.clone();
        let sigma = f.sigma().clone();
        let (tag, e) = LWR.eval_with_error(&holder.usk, &s).unwrap();
        let t = tag_values(&tag);
        let statement = f.att_statement(&f.h, &holder.phi.to_rq(), &rows, &t);
        let cred = holder.cred.clone();
        let honest = witness(
            &ring,
            cred.s0(),
            cred.s1(),
            cred.x1(),
            &holder.usk,
            &holder.x0,
            e.entries(),
        );
        assert_eq!(f.att_check(&statement, &honest), Ok(()));
        // another user's usk with this credential and tag
        let w = witness(
            &ring,
            cred.s0(),
            cred.s1(),
            cred.x1(),
            &other.usk,
            &holder.x0,
            e.entries(),
        );
        assert_eq!(f.att_check(&statement, &w), Err(jali::Error::Witness));
        // T ± 1 with e ± γ: the equation holds modulo q_t, but |e_0| > 7
        for by in [1i128, -1] {
            let mut shifted = t;
            shifted[0] = (shifted[0] + by).rem_euclid(i128::from(P));
            let mut e2 = *e.entries();
            e2[0] = (i128::from(e2[0]) + by * i128::from(GAMMA)) as i8;
            assert!(e2[0].unsigned_abs() > 7);
            let statement = f.att_statement(&f.h, &holder.phi.to_rq(), &rows, &shifted);
            let w = witness(
                &ring,
                cred.s0(),
                cred.s1(),
                cred.x1(),
                &holder.usk,
                &holder.x0,
                &e2,
            );
            assert_eq!(f.att_check(&statement, &w), Err(jali::Error::Witness));
        }
        // the target t = (v − x_1)^{-1} + b_u usk + B_r x_0 + b_φ φ of a message
        let target = |usk: &Rq, x0: [&Rq; 2], x1: &Rq, phi: &Rq| {
            let y = sigma.v().sub(x1).inverse().unwrap();
            y.add(&sigma.b_u().mul(usk))
                .add(&sigma.b_r()[0].mul(x0[0]))
                .add(&sigma.b_r()[1].mul(x0[1]))
                .add(&sigma.b_phi().mul(phi))
        };
        let usk_rq = holder.usk.to_rq();
        let x0_rq = [holder.x0[0].to_rq(), holder.x0[1].to_rq()];
        let x1_rq = cred.x1().to_rq();
        let phi_rq = holder.phi.to_rq();
        let x0_ref = [&x0_rq[0], &x0_rq[1]];
        // x_1 with a coefficient 2 > β_x, with a real preimage of ITS target
        let x1_bad = with_coefficient(cred.x1(), 0, 2);
        let t_bad = target(&usk_rq, x0_ref, &rq_of(&x1_bad), &phi_rq);
        let pre = f.sk.sample_preimage(&t_bad, &mut f.rng).unwrap();
        let w = att_witness(
            [ints(&ring, &pre.s0), ints(&ring, &pre.s1)],
            int_poly(&ring, x1_bad).unwrap(),
            tern(&ring, &holder.usk),
            [tern(&ring, &holder.x0[0]), tern(&ring, &holder.x0[1])],
            e_subring(&ring, e.entries()).unwrap(),
        );
        assert_eq!(f.att_check(&statement, &w), Err(jali::Error::Witness));
        // usk with a coefficient 2 > β_u: the credential AND the tag computed from it
        let usk_bad = with_coefficient(&holder.usk, 0, 2);
        let t_bad = target(&rq_of(&usk_bad), x0_ref, &x1_rq, &phi_rq);
        let pre = f.sk.sample_preimage(&t_bad, &mut f.rng).unwrap();
        let (tag_bad, e_bad) = harness_tag_eval(&usk_bad, &s);
        let statement_u = f.att_statement(&f.h, &phi_rq, &rows, &tag_bad);
        let w = att_witness(
            [ints(&ring, &pre.s0), ints(&ring, &pre.s1)],
            tern(&ring, cred.x1()),
            int_poly(&ring, usk_bad).unwrap(),
            [tern(&ring, &holder.x0[0]), tern(&ring, &holder.x0[1])],
            e_subring(&ring, &e_bad).unwrap(),
        );
        assert_eq!(f.att_check(&statement_u, &w), Err(jali::Error::Witness));
        // x_0 with a coefficient 2 > β_r
        let x0_bad = with_coefficient(&holder.x0[0], 0, 2);
        let t_bad = target(&usk_rq, [&rq_of(&x0_bad), &x0_rq[1]], &x1_rq, &phi_rq);
        let pre = f.sk.sample_preimage(&t_bad, &mut f.rng).unwrap();
        let w = att_witness(
            [ints(&ring, &pre.s0), ints(&ring, &pre.s1)],
            tern(&ring, cred.x1()),
            tern(&ring, &holder.usk),
            [int_poly(&ring, x0_bad).unwrap(), tern(&ring, &holder.x0[1])],
            e_subring(&ring, e.entries()).unwrap(),
        );
        assert_eq!(f.att_check(&statement, &w), Err(jali::Error::Witness));
    }

    /// The exact l2 bound of `s` (H/flow.rs:367-395): with `‖s‖² = ⌊β_s²⌋ + 1` the witness is
    /// refused, with `‖s‖² = ⌊β_s²⌋` and `⌊β_s²⌋ − 1` it is accepted, each for a key `h` solved
    /// from `s` (a relation-level device; the helper's key is not involved).
    #[test]
    fn the_norm_bound_of_s_is_exact() {
        let mut f = fixture(0x7e1_0003);
        let holder = f.holder();
        let (s, rows) = f.scope();
        let ring = f.k.rings.c.clone();
        let (tag, e) = LWR.eval_with_error(&holder.usk, &s).unwrap();
        let cred = &holder.cred;
        let as_rq =
            |c: &[i32]| Rq::from_i64(&c.iter().map(|&x| i64::from(x)).collect::<Vec<_>>()).unwrap();
        // the target t = s_0 + h s_1 of the credential under the real key
        let s1 = as_rq(cred.s1());
        let t = as_rq(cred.s0()).add(&f.h.mul(&s1));
        let s1_inv = s1.inverse().expect("s_1 is a unit");
        let norm_s1: u64 = cred
            .s1()
            .iter()
            .map(|&x| (i64::from(x) * i64::from(x)) as u64)
            .sum();
        for (total, accepted) in [(S_BOUND + 1, false), (S_BOUND, true), (S_BOUND - 1, true)] {
            // s_0' with ‖s_0'‖² = total − ‖s_1‖², greedily as a sum of squares
            let mut rest = total - norm_s1;
            let mut s0 = vec![0i32; D];
            for c in &mut s0 {
                let x = rest.isqrt();
                *c = x as i32;
                rest -= x * x;
                if rest == 0 {
                    break;
                }
            }
            assert_eq!(rest, 0);
            // h' = (t − s_0') s_1^{-1}, so that s_0' + h' s_1 = t
            let h = t.sub(&as_rq(&s0)).mul(&s1_inv);
            let statement = f.att_statement(&h, &holder.phi.to_rq(), &rows, &tag_values(&tag));
            let w = witness(
                &ring,
                &s0,
                cred.s1(),
                cred.x1(),
                &holder.usk,
                &holder.x0,
                e.entries(),
            );
            let norm: u64 = s0
                .iter()
                .chain(cred.s1())
                .map(|&x| (i64::from(x) * i64::from(x)) as u64)
                .sum();
            assert_eq!(norm, total);
            assert_eq!(
                f.att_check(&statement, &w).is_ok(),
                accepted,
                "‖s‖² = {total}"
            );
        }
    }

    /// The credential-free forgery of the proof of lem:base-vsis (bb:892): for ANY short `usk`,
    /// `x_0`, `x_1` with `v − x_1` a unit, `s = 0` satisfies the possession clause for
    /// `b_φ φ := −b_u usk − B_r x_0 − (v − x_1)^{-1}`. Jali's relation accepts that witness (the
    /// tag clauses hold for the tag of `usk`), so only the public check `φ ∈ M_pub` refuses it;
    /// the forged `φ` is not binary, and no [`BinaryPoly`] carries it.
    #[test]
    fn the_phi_forgery_satisfies_the_relation_but_phi_is_not_binary() {
        let mut f = fixture(0x7e1_0004);
        let (s, rows) = f.scope();
        let ring = f.k.rings.c.clone();
        let usk = Ternary::sample(&mut f.rng);
        let x0 = [Ternary::sample(&mut f.rng), Ternary::sample(&mut f.rng)];
        let x1 = Ternary::sample(&mut f.rng);
        let (tag, e) = LWR.eval_with_error(&usk, &s).unwrap();
        let sigma = f.sigma();
        let y = sigma.v().sub(&x1.to_rq()).inverse().unwrap();
        let bphi_phi = sigma.commitment(&usk, &x0).unwrap().neg().sub(&y);
        let statement = r_att(&f.k, &f.h, &bphi_phi, &rows, &tag_values(&tag)).unwrap();
        let zero = vec![0i32; D];
        let w = witness(&ring, &zero, &zero, &x1, &usk, &x0, e.entries());
        assert_eq!(f.att_check(&statement, &w), Ok(()));
        // φ = b_φ^{-1} (b_φ φ) is far from binary
        let phi = sigma.b_phi().inverse().unwrap().mul(&bphi_phi);
        let binary = phi.coeffs().iter().filter(|&&x| x <= 1).count();
        assert!(binary < 8, "{binary} binary coefficients");
    }

    /// bb:232: the non-canonical encoding `T + p` has exactly the witnesses of `T`; only
    /// `ValidTag` (an invariant of [`LWRTag`]) stops it.
    #[test]
    fn non_canonical_tags_have_the_witnesses_of_canonical_ones() {
        let mut f = fixture(0x7e1_0005);
        let holder = f.holder();
        let (s, rows) = f.scope();
        let ring = f.k.rings.c.clone();
        let (tag, e) = LWR.eval_with_error(&holder.usk, &s).unwrap();
        let mut lifted = tag_values(&tag);
        lifted[0] += i128::from(P);
        let statement = f.att_statement(&f.h, &holder.phi.to_rq(), &rows, &lifted);
        let cred = &holder.cred;
        let w = witness(
            &ring,
            cred.s0(),
            cred.s1(),
            cred.x1(),
            &holder.usk,
            &holder.x0,
            e.entries(),
        );
        assert_eq!(f.att_check(&statement, &w), Ok(()));
    }

    /// `R_issue` (H/flow.rs:506-534): the honest witness passes; another user's key for this
    /// `C`, `id` and `T_0`, an `x_0` with a coefficient 2 (and `C` computed from it), and a shifted
    /// `T_0` with its error outside the exact bound are refused.
    #[test]
    fn issuance_witnesses() {
        let mut f = fixture(0x7e1_0006);
        let holder = f.holder();
        let other = f.holder();
        let ring = f.k.rings.c.clone();
        let (id, e0) = LWR.eval_with_error(&holder.usk, &f.pp.c0).unwrap();
        let s = oracles::tag_point(LABEL, &id);
        let rows = TagRows::new(&f.k.rings, &s).unwrap();
        let (t0, e1) = LWR.eval_with_error(&holder.usk, &s).unwrap();
        let c = f.sigma().commitment(&holder.usk, &holder.x0).unwrap();
        let check = |statement: &Statement, w: &Witness| {
            statement
                .compile(f.sets.issue.clone())
                .unwrap()
                .map_witness(w)
                .map(|_| ())
        };
        let (id_t, t0_t) = (tag_values(&id), tag_values(&t0));
        let statement = r_issue(&f.k, &c, [(&f.k.c0, &id_t), (&rows, &t0_t)]).unwrap();
        let honest = issue_witness_of(&f.k.rings, &holder.usk, &holder.x0, &e0, &e1).unwrap();
        assert_eq!(check(&statement, &honest), Ok(()));
        let w = issue_witness_of(&f.k.rings, &other.usk, &holder.x0, &e0, &e1).unwrap();
        assert_eq!(check(&statement, &w), Err(jali::Error::Witness));
        // x_0 with a coefficient 2, C computed from it
        let x0_bad = with_coefficient(&holder.x0[0], 0, 2);
        let sigma = f.sigma();
        let c_bad = sigma
            .b_u()
            .mul(&holder.usk.to_rq())
            .add(&sigma.b_r()[0].mul(&rq_of(&x0_bad)))
            .add(&sigma.b_r()[1].mul(&holder.x0[1].to_rq()));
        let statement_x = r_issue(&f.k, &c_bad, [(&f.k.c0, &id_t), (&rows, &t0_t)]).unwrap();
        let w = issue_witness(
            tern(&ring, &holder.usk),
            [int_poly(&ring, x0_bad).unwrap(), tern(&ring, &holder.x0[1])],
            [
                e_subring(&ring, e0.entries()).unwrap(),
                e_subring(&ring, e1.entries()).unwrap(),
            ],
        );
        assert_eq!(check(&statement_x, &w), Err(jali::Error::Witness));
        // T_0 + 1 in row 0 with e_1 + γ
        let mut shifted = t0_t;
        shifted[0] = (shifted[0] + 1) % i128::from(P);
        let mut e_shifted = *e1.entries();
        e_shifted[0] += 15;
        let statement_t = r_issue(&f.k, &c, [(&f.k.c0, &id_t), (&rows, &shifted)]).unwrap();
        let w = issue_witness(
            tern(&ring, &holder.usk),
            [tern(&ring, &holder.x0[0]), tern(&ring, &holder.x0[1])],
            [
                e_subring(&ring, e0.entries()).unwrap(),
                e_subring(&ring, &e_shifted).unwrap(),
            ],
        );
        assert_eq!(check(&statement_t, &w), Err(jali::Error::Witness));
    }

    /// The witness layout of the rounding errors (pcs.rs:145-153).
    #[test]
    fn rounding_errors_sit_in_the_subring() {
        let ring = Rings::new().unwrap().c;
        let mut e = [0i8; M];
        for (j, x) in e.iter_mut().enumerate() {
            *x = (j % 15) as i8 - 7;
        }
        let polys = e_subring(&ring, &e).unwrap();
        assert_eq!(polys.len(), 2);
        for (j, &x) in e.iter().enumerate() {
            let p = &polys[j / 128];
            assert_eq!(p.coefficient_i128(8 * (j % 128)).unwrap(), i128::from(x));
        }
        for p in &polys {
            for i in (0..D).filter(|i| i % 8 != 0) {
                assert_eq!(p.coefficient_i128(i).unwrap(), 0);
            }
        }
        // element 1 holds e_128..e_167, then zeros
        for i in 40..128 {
            assert_eq!(polys[1].coefficient_i128(8 * i).unwrap(), 0);
        }
    }

    /// The prover refuses a false witness with the crate's error, before any proving work, and
    /// reports a statement that does not match the set as a backend error.
    #[test]
    fn the_prover_maps_its_errors() {
        let mut f = fixture(0x7e1_0007);
        let holder = f.holder();
        let (id, e0) = LWR.eval_with_error(&holder.usk, &f.pp.c0).unwrap();
        let s = oracles::tag_point(LABEL, &id);
        let rows = TagRows::new(&f.k.rings, &s).unwrap();
        let (t0, e1) = LWR.eval_with_error(&holder.usk, &s).unwrap();
        let c = f.sigma().commitment(&holder.usk, &holder.x0).unwrap();
        let statement = r_issue(
            &f.k,
            &c,
            [(&f.k.c0, &tag_values(&id)), (&rows, &tag_values(&t0))],
        )
        .unwrap();
        let other = Ternary::sample(&mut f.rng);
        let w = issue_witness_of(&f.k.rings, &other, &holder.x0, &e0, &e1).unwrap();
        let ctx = [7u8; 32];
        let seed = f.pp.jali_pp_seed;
        assert_eq!(
            prove(&statement, &f.sets.issue, seed, &w, &ctx, &mut f.rng),
            Err(Error::WitnessDoesNotSatisfyRelation)
        );
        let w = issue_witness_of(&f.k.rings, &holder.usk, &holder.x0, &e0, &e1).unwrap();
        assert!(matches!(
            prove(&statement, &f.sets.att, seed, &w, &ctx, &mut f.rng),
            Err(Error::LatticeBackend(_))
        ));
    }

    /// Where the time of a proof goes, per stage (one thread, this machine): the rows of a tag
    /// matrix, the statement builders, `compile`, the witness map, proving and verifying, for
    /// `R_att` and `R_issue`. A measurement aid for the notes; run in release with
    /// `cargo test --release --features lattice --lib -- --ignored --nocapture timing_probe`.
    #[test]
    #[ignore = "timing probe; run in release with --ignored --nocapture"]
    fn timing_probe() {
        use std::time::Instant;
        let ms = |t: Instant| t.elapsed().as_secs_f64() * 1e3;
        let mut f = fixture(0x7e1_0009);
        let holder = f.holder();
        let ring = f.k.rings.c.clone();
        let (id, e0) = LWR.eval_with_error(&holder.usk, &f.pp.c0).unwrap();
        let t = Instant::now();
        let s = oracles::tag_point(LABEL, &id);
        let h0_ms = ms(t);
        let t = Instant::now();
        let rows = TagRows::new(&f.k.rings, &s).unwrap();
        let rows_ms = ms(t);
        let (t0, e1) = LWR.eval_with_error(&holder.usk, &s).unwrap();
        let ctx = [3u8; 32];
        let seed = f.pp.jali_pp_seed;
        // R_att
        let t = Instant::now();
        let statement = f.att_statement(&f.h, &holder.phi.to_rq(), &rows, &tag_values(&t0));
        let build_att = ms(t);
        let t = Instant::now();
        let compiled = statement.compile(f.sets.att.clone()).unwrap();
        let compile_att = ms(t);
        let cred = holder.cred.clone();
        let w = witness(
            &ring,
            cred.s0(),
            cred.s1(),
            cred.x1(),
            &holder.usk,
            &holder.x0,
            e1.entries(),
        );
        let t = Instant::now();
        compiled.map_witness(&w).unwrap();
        let map_att = ms(t);
        let t = Instant::now();
        let proof = compiled
            .prove_bytes_with_seed(seed, &w, &ctx, [4; 32])
            .unwrap();
        let prove_att = ms(t);
        let t = Instant::now();
        compiled.verify_bytes(seed, &proof, &ctx).unwrap();
        let verify_att = ms(t);
        // R_issue
        let c = f.sigma().commitment(&holder.usk, &holder.x0).unwrap();
        let t = Instant::now();
        let statement = r_issue(
            &f.k,
            &c,
            [(&f.k.c0, &tag_values(&id)), (&rows, &tag_values(&t0))],
        )
        .unwrap();
        let build_issue = ms(t);
        let t = Instant::now();
        let compiled = statement.compile(f.sets.issue.clone()).unwrap();
        let compile_issue = ms(t);
        let w = issue_witness_of(&f.k.rings, &holder.usk, &holder.x0, &e0, &e1).unwrap();
        let t = Instant::now();
        compiled.map_witness(&w).unwrap();
        let map_issue = ms(t);
        let t = Instant::now();
        let proof_issue = compiled
            .prove_bytes_with_seed(seed, &w, &ctx, [5; 32])
            .unwrap();
        let prove_issue = ms(t);
        let t = Instant::now();
        compiled.verify_bytes(seed, &proof_issue, &ctx).unwrap();
        let verify_issue = ms(t);
        let t = Instant::now();
        let _ = Constants::new(&f.pp).unwrap();
        let constants_ms = ms(t);
        let t = Instant::now();
        let _ = ParameterSets::load().unwrap();
        let sets_ms = ms(t);
        let t = Instant::now();
        let _: crate::pcs::lattice::LatticePCS = crate::pcs::PredicateCredentialSystem::setup(
            crate::pcs::SetupParams::new(LABEL.to_vec()),
        )
        .unwrap();
        let setup_ms = ms(t);
        println!(
            "H_0 {h0_ms:.2} ms; TagRows {rows_ms:.2} ms; Constants::new {constants_ms:.2} ms; \
             ParameterSets::load {sets_ms:.2} ms; Setup {setup_ms:.2} ms\n\
             R_att: build {build_att:.1} ms, compile {compile_att:.1} ms, map_witness {map_att:.1} ms, \
             prove {prove_att:.1} ms (incl. map), verify {verify_att:.1} ms; {} B\n\
             R_issue: build {build_issue:.1} ms, compile {compile_issue:.1} ms, map_witness {map_issue:.1} ms, \
             prove {prove_issue:.1} ms (incl. map), verify {verify_issue:.1} ms; {} B",
            proof.len(),
            proof_issue.len()
        );
    }

    /// Heavy: the forgery of
    /// [`the_phi_forgery_satisfies_the_relation_but_phi_is_not_binary`] PROVES AND VERIFIES in
    /// Jali, and so does a fresh proof for the non-canonical `T + p`, which is also a proof for
    /// `T`. Run in release:
    /// `cargo test --release --features lattice --lib -- --ignored proofs_for`.
    #[test]
    #[ignore = "heavy: three R_att proofs and verifications (0.5 GiB, about 10 s each in release)"]
    fn proofs_for_the_relation_level_attacks_verify_in_jali() {
        let mut f = fixture(0x7e1_0008);
        let (s, rows) = f.scope();
        let ring = f.k.rings.c.clone();
        let ctx = [9u8; 32];
        let seed = f.pp.jali_pp_seed;
        // the φ forgery, s = 0
        let usk = Ternary::sample(&mut f.rng);
        let x0 = [Ternary::sample(&mut f.rng), Ternary::sample(&mut f.rng)];
        let x1 = Ternary::sample(&mut f.rng);
        let (tag, e) = LWR.eval_with_error(&usk, &s).unwrap();
        let sigma = f.sigma().clone();
        let y = sigma.v().sub(&x1.to_rq()).inverse().unwrap();
        let bphi_phi = sigma.commitment(&usk, &x0).unwrap().neg().sub(&y);
        let statement = r_att(&f.k, &f.h, &bphi_phi, &rows, &tag_values(&tag)).unwrap();
        let zero = vec![0i32; D];
        let w = witness(&ring, &zero, &zero, &x1, &usk, &x0, e.entries());
        let proof = prove(&statement, &f.sets.att, seed, &w, &ctx, &mut f.rng).unwrap();
        assert_eq!(verify(&statement, &f.sets.att, seed, &proof, &ctx), Ok(()));
        // T + p: a fresh proof verifies for the non-canonical statement ...
        let holder = f.holder();
        let (tag, e) = LWR.eval_with_error(&holder.usk, &s).unwrap();
        let mut lifted = tag_values(&tag);
        lifted[0] += i128::from(P);
        let statement = f.att_statement(&f.h, &holder.phi.to_rq(), &rows, &lifted);
        let cred = &holder.cred;
        let w = witness(
            &ring,
            cred.s0(),
            cred.s1(),
            cred.x1(),
            &holder.usk,
            &holder.x0,
            e.entries(),
        );
        let proof = prove(&statement, &f.sets.att, seed, &w, &ctx, &mut f.rng).unwrap();
        assert_eq!(verify(&statement, &f.sets.att, seed, &proof, &ctx), Ok(()));
        // ... and is a proof for the canonical statement too: Jali binds T modulo q_t
        let canonical = f.att_statement(&f.h, &holder.phi.to_rq(), &rows, &tag_values(&tag));
        assert_eq!(verify(&canonical, &f.sets.att, seed, &proof, &ctx), Ok(()));
    }
}
