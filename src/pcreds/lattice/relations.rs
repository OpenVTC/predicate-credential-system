//! The four relations of `Π_PCreds` (§5.2, "Relations") for `Σ-vSIS` with the short-key
//! `Tag_LWR`, in Jali's statement API: `R_Tag` (`π_id`), `R_att` (`π_att`), `R_iss` (`π_iss`) and
//! `R_Possess` (`π_prove`), each sharing the coefficient vector of `usk` across its clauses.
//!
//! Every relation is over $`\mathbb Z_q[X]/(X^{1024} + 1)`$, with the tag clauses over the tag
//! ring $`\mathbb Z_{q_t}[X]/(X^{1024} + 1)`$. The blocks, in declaration order (a parameter set
//! is derived for exactly one layout, and Jali's `compile` refuses any other):
//!
//! | relation | blocks | constraints | parameter set |
//! |---|---|---|---|
//! | `R_Tag` at $`(t, x)`$ | `usk` (1, `LinfExact(1)`), `e` (2, subring degree 128, `LinfExact(7)`) | the 168 tag clauses of $`t`$ at $`x`$ | [`ParameterSets::tag`](crate::lattice::sets::ParameterSets::tag) |
//! | `R_att` at $`(\mathsf{hvk}, \varepsilon, t, x_Q)`$ | `s` (2, [`S_NORM`]: `L2SquaredRange { min: 1, max: 90,803,788,942 }`, placement [`ATT_S_PLACEMENT`]), `x1`, `usk`, `x0` (3), all `LinfExact(1)`, then `e` | the possession equation, the 168 tag clauses of $`t`$ at $`x_Q`$ | [`ParameterSets::att`](crate::lattice::sets::ParameterSets::att) |
//! | `R_iss` at $`(\mathsf{hvk}, C, \mathsf{id})`$ | `usk`, `x0` (3), `e` | the opening of $`C`$, the 168 tag clauses of $`\mathsf{id}`$ at $`x_0`$ | [`ParameterSets::iss`](crate::lattice::sets::ParameterSets::iss) |
//! | `R_Possess` at $`(\mathsf{hvk}, \varepsilon)`$ | `s` (2, [`S_NORM`], placement [`POSSESS_S_PLACEMENT`]), `x1`, `usk`, `x0` (3) | the possession equation | [`ParameterSets::possess`](crate::lattice::sets::ParameterSets::possess) |
//!
//! with the possession equation (one `eq_mod_p` over $`\mathbb Z_q`$, box "`Σ-vSIS` credential
//! base", $`\Pi_{\Possess}`$)
//!
//! ```math
//! \bigl(s_0 + h s_1 - b_u\,\mathsf{usk} - \textstyle\sum_k b_{r,k} x_{0,k}\bigr)\cdot(v - x_1) - 1 = 0,
//! ```
//!
//! the opening of the request ($`\Pi_{\mathsf{PrepareIssue}}`$, one `eq_mod_p` over
//! $`\mathbb Z_q`$) $`b_u\,\mathsf{usk} + \sum_k b_{r,k} x_{0,k} - C = 0`$, and for $`j < 168`$
//! the tag clause (one `const_coeff_zero` over $`\mathbb Z_{q_t}`$)
//! $`\mathrm{ct}(\sigma(a_j)\,\mathsf{usk} + X^{-8(j \bmod 128)} e_{\lfloor j/128\rfloor} - \gamma T_j) = 0`$
//! with $`\sigma(a_j)`$ = `Poly::auto` of row $`j`$ of the matrix lifted centred. Since
//! $`\mathrm{ct}(\sigma(a)\,u) = \langle a, u\rangle`$, clause $`j`$ is
//! $`\langle a_j, \mathsf{usk}\rangle + e_j = \gamma T_j \bmod q_t`$, the relation
//! $`R_{\mathsf{Tag}_{\mathsf{LWR}}}`$ of §6.1.3.
//!
//! Witness maps: `s` = $`(s_0, s_1)`$, `x1`, `usk`, `x0` as statement-ring polynomials of their
//! integer coefficients; a rounding-error vector $`e \in [-7, 7]^{168}`$ as two elements with
//! $`e_j`$ at coefficient $`8(j \bmod 128)`$ of element $`\lfloor j / 128\rfloor`$ (Jali's witness
//! map refuses nonzero coefficients outside the subring).
//!
//! The norms are all EXACT (`L2Squared`, `LinfExact`, never Jali's approximate `Norm::Linf`), so
//! by Jali's design a verified proof bounds every extracted block by its declared bound
//! (`Compiled::extraction_bound` returns the declared bound for exact norms). That is a property
//! Jali's design claims, not a proven theorem. In the plain build (feature `lattice-plain`) Jali's
//! knowledge soundness under Fiat–Shamir is not written out, and its extraction rewinds where the
//! paper assumes an online extractor. In the default, extractable build
//! ([`STRAIGHT_LINE`](crate::lattice::STRAIGHT_LINE)) the proofs are Jali's straight-line
//! extractable proofs, whose extractor decrypts the further transcripts from the proof's LinHC
//! commitment instead of rewinding, and Jali gives that argument as an outline in the classical
//! random-oracle model, with the status of each step. For
//! the rounding errors this is what rem:relaxed-extraction requires: with
//! $`\|e\|_\infty \le \lfloor\gamma/2\rfloor`$ a key explains at most one valid tag per matrix
//! (lem:tag-lwr-determinism).
//!
//! **What the relations do not check.**
//!
//! * The constants are reduced modulo the modulus of their constraint, so the public checks of
//!   the verifier stay essential: a non-canonical tag $`T + pz`$ has exactly the witnesses of
//!   $`T`$. The types of the backend cannot represent one ([`LWRTag`]).
//!
//! **The lower bound on `s`.** $`\Pi_{\Possess}`$ proves $`1 \le \|s\|^2 \le \beta_s^2`$: `s` is
//! declared with Jali's two-sided exact norm [`S_NORM`], whose lower bound Jali proves with one
//! more committed binary polynomial and one constant-coefficient equation at the proof modulus
//! (one more Ajtai row in `R_att` and `R_Possess`).
//!
//! **Seed bridge.** Every proof gets a fresh 32-byte seed from the caller's RNG
//! (`lattice::fresh_seed`) for `Compiled::prove_bytes_with_seed`, or for
//! `Compiled::prove_extractable_bytes_with_seed` in the extractable build. A `RestartLimit` is
//! retried with a new fresh seed, at most [`MAX_PROOF_ATTEMPTS`] times.

use std::{collections::BTreeMap, sync::Arc};

use ark_std::rand::{CryptoRng, RngCore};
use jali::{
    math::{Poly, Ring},
    statement::{Compiled, Norm, Placement, Statement},
};

use super::base::{VSISCredential, VSISParams, VSISTape};
use crate::{
    error::Error,
    kiprf::lwr::{LWRTag, RoundingError, TagMatrix},
    lattice::{
        BETA_R, BETA_U, BETA_X, D, E_BOUND, E_COUNT, E_DEG, ELL_R, GAMMA, M, Q, Q_T, Rq, S_BOUND,
        STRAIGHT_LINE, Ternary, fresh_seed, jali_error, sets::ProofSet,
    },
};

/// Attempts of a proof with fresh seeds before a `RestartLimit` of Jali is reported as
/// [`Error::LatticeBackend`].
pub(crate) const MAX_PROOF_ATTEMPTS: usize = 3;

/// Where `R_Possess` holds `s`: the part of Jali's commitment that the derivation of
/// [`ParameterSets::possess`](crate::lattice::sets::ParameterSets::possess) chose (its report,
/// `placement.chosen`).
pub(crate) const POSSESS_S_PLACEMENT: Placement = Placement::Bdlop;

/// Where `R_att` holds `s`: the part of Jali's commitment that the derivation of
/// [`ParameterSets::att`](crate::lattice::sets::ParameterSets::att) chose (its report,
/// `placement.chosen`).
pub(crate) const ATT_S_PLACEMENT: Placement = Placement::Bdlop;

/// A witness: named blocks of statement-ring polynomials. Jali's [`Poly`] wipes its
/// coefficients on drop, so a dropped witness leaves no copy of its values in the heap.
pub(crate) type Witness = BTreeMap<String, Vec<Poly>>;

// The layouts below are those of the parameter sets: two components of s (w = 2), ℓ_r = 3, and
// the 168 rounding errors in two subring elements of degree 128.
const _: () = assert!(ELL_R == 3 && E_COUNT == 2 && E_DEG == 128 && M == 168);

/// The representative of `x ∈ [0, m)` in $`(-m/2, m/2]`$.
fn centred(x: u32, m: u32) -> i128 {
    let (x, m) = (i128::from(x), i128::from(m));
    if x > m / 2 { x - m } else { x }
}

/// The two rings of the statements: the statement ring $`\mathbb Z_q[X]/(X^{1024}+1)`$ and the
/// tag ring $`\mathbb Z_{q_t}[X]/(X^{1024}+1)`$, over which the tag clauses are built
/// (`variable_in`, `constant_in`).
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

/// An element of $`R_q`$ as a statement-ring polynomial of its centred coefficients.
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

/// A ternary polynomial as a statement-ring polynomial.
pub(crate) fn ternary_poly(ring: &Arc<Ring>, x: &Ternary) -> Result<Poly, Error> {
    int_poly(ring, x.coeffs().iter().map(|&c| i128::from(c)))
}

/// The rounding errors as [`E_COUNT`] elements of the subring of degree [`E_DEG`], with $`e_j`$
/// at coefficient $`(1024/128)\,(j \bmod 128)`$ of element $`\lfloor j/128\rfloor`$
/// (statement-ring polynomials).
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
/// values (the constant is $`-\gamma T_j`$), so that a test can pass the non-canonical
/// $`T + p`$, which no [`LWRTag`] represents.
pub(crate) fn tag_values(tag: &LWRTag) -> [i128; M] {
    tag.entries().map(i128::from)
}

/// The rows $`\sigma(a_0), \dots, \sigma(a_{m-1})`$ of a tag matrix as tag-ring polynomials: row
/// $`j`$ lifted centred, then `Poly::auto`. Built once per matrix: for $`x_0`$ once per
/// deployment ([`Constants`]), for a recipient point $`x_Q`$ once per statement.
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

/// What every statement of a deployment shares, built once per deployment: the rings and the
/// public elements of `pp_Σ` lifted to the statement ring (with the negations the builders use).
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
}

impl Constants {
    pub(crate) fn new(sigma: &VSISParams) -> Result<Self, Error> {
        let rings = Rings::new()?;
        let lifted = |x: &Rq| lift(&rings.c, x).map_err(jali_error);
        let v = lifted(sigma.v())?;
        let b_u = lifted(sigma.b_u())?;
        let b_r = sigma
            .b_r()
            .iter()
            .map(lifted)
            .collect::<Result<Vec<_>, _>>()?;
        let b_r: [Poly; ELL_R] = b_r
            .try_into()
            .map_err(|_| Error::LatticeBackend("B_r has ell_r columns".into()))?;
        Ok(Self {
            v,
            neg_b_u: b_u.neg(),
            neg_b_r: core::array::from_fn(|k| b_r[k].neg()),
            b_u,
            b_r,
            rings,
        })
    }
}

/// A rounding-error block, two subring elements of degree [`E_DEG`] (the proof degree) with the
/// exact bound $`\lfloor\gamma/2\rfloor = 7`$, in the Ajtai part.
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

/// The norm of `s` in `R_att` and `R_Possess`: $`1\le\|s\|^2\le\lfloor\beta_s^2\rfloor`$, both
/// bounds exact. The lower bound is the condition $`s\neq0`$ of $`\Pi_{\Possess}`$ ("prove
/// knowledge of $`(s, x_1, \mathsf{usk}, x_0)`$ with $`1\le\|s\|^2\le\beta_s^2`$"), which the
/// argument system must extract exactly.
pub(crate) const S_NORM: Norm = Norm::L2SquaredRange {
    min: 1,
    max: S_BOUND,
};

/// The blocks of a credential, in the order of `R_att` and `R_Possess`: `s` ([`S_NORM`], in the
/// part `s_placement`), `x1`, `usk`, `x0`.
fn declare_credential(st: &mut Statement, s_placement: Placement) -> Result<(), jali::Error> {
    st.var_placed("s", 2, S_NORM, s_placement)?;
    st.var("x1", 1, Norm::LinfExact(BETA_X))?;
    st.var("usk", 1, Norm::LinfExact(BETA_U))?;
    st.var("x0", ELL_R, Norm::LinfExact(BETA_R))?;
    Ok(())
}

/// The possession equation $`(A s - b_u\,\mathsf{usk} - B_r x_0)(v - x_1) - 1 = 0`$ over
/// $`\mathbb Z_q`$, with $`A = [1 \mid h]`$.
fn possession_equation(st: &mut Statement, k: &Constants, h: &Rq) -> Result<(), jali::Error> {
    let rc = &k.rings.c;
    let a = [Poly::constant(rc.clone(), 1), lift(rc, h)?];
    let mut r = st.constant_in(Poly::zero(rc.clone()))?;
    for (i, a) in a.iter().enumerate() {
        r = r.add(&st.variable_in(rc, "s", i)?.scale(a)?)?;
    }
    r = r.add(&st.variable_in(rc, "usk", 0)?.scale(&k.neg_b_u)?)?;
    for (i, b) in k.neg_b_r.iter().enumerate() {
        r = r.add(&st.variable_in(rc, "x0", i)?.scale(b)?)?;
    }
    let g = st.constant_in(k.v.clone())?.add(
        &st.variable_in(rc, "x1", 0)?
            .scale(&Poly::constant(rc.clone(), -1))?,
    )?;
    let possession = r
        .product_affine(&g)?
        .add(&st.constant_in(Poly::constant(rc.clone(), -1))?)?;
    st.eq_mod_p(possession)?;
    Ok(())
}

/// For every row $`j`$, the clause
/// $`\mathrm{ct}(\sigma(a_j)\,\mathsf{usk} + X^{-8(j \bmod 128)} e_{\lfloor j/128\rfloor} - \gamma T_j) = 0 \bmod q_t`$
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

/// `R_Tag` for the public statement $`(t, x)`$: `rows` are the rows of the matrix $`x`$, `tag`
/// the entries of $`t`$.
pub(crate) fn r_tag(k: &Constants, rows: &TagRows, tag: &[i128; M]) -> Result<Statement, Error> {
    let build = || -> Result<Statement, jali::Error> {
        let mut st = Statement::new(k.rings.c.clone());
        st.var("usk", 1, Norm::LinfExact(BETA_U))?;
        declare_e(&mut st, "e")?;
        tag_clauses(&mut st, &k.rings.t, "e", rows, tag)?;
        Ok(st)
    };
    build().map_err(jali_error)
}

/// `R_att` for the public statement $`(\mathsf{hvk}, \varepsilon, t, x_Q)`$: `h` is the helper
/// key, `rows` the rows of the recipient point $`x_Q`$ and `tag` the entries of $`t`$.
pub(crate) fn r_att(
    k: &Constants,
    h: &Rq,
    rows: &TagRows,
    tag: &[i128; M],
) -> Result<Statement, Error> {
    let build = || -> Result<Statement, jali::Error> {
        let mut st = Statement::new(k.rings.c.clone());
        declare_credential(&mut st, ATT_S_PLACEMENT)?;
        declare_e(&mut st, "e")?;
        possession_equation(&mut st, k, h)?;
        tag_clauses(&mut st, &k.rings.t, "e", rows, tag)?;
        Ok(st)
    };
    build().map_err(jali_error)
}

/// `R_iss` for the public statement $`(\mathsf{hvk}, C, \mathsf{id})`$: the opening of `c` and
/// the tag clauses of the identifier at the identifier point $`x_0`$ (`rows`, `id`). The key
/// does not enter the relation (the request does not depend on it); it enters the context.
pub(crate) fn r_iss(
    k: &Constants,
    c: &Rq,
    rows: &TagRows,
    id: &[i128; M],
) -> Result<Statement, Error> {
    let build = || -> Result<Statement, jali::Error> {
        let rc = &k.rings.c;
        let mut st = Statement::new(rc.clone());
        st.var("usk", 1, Norm::LinfExact(BETA_U))?;
        st.var("x0", ELL_R, Norm::LinfExact(BETA_R))?;
        declare_e(&mut st, "e")?;
        let mut com = st.variable_in(rc, "usk", 0)?.scale(&k.b_u)?;
        for (i, b) in k.b_r.iter().enumerate() {
            com = com.add(&st.variable_in(rc, "x0", i)?.scale(b)?)?;
        }
        com = com.add(&st.constant_in(lift(rc, c)?.neg())?)?;
        st.eq_mod_p(com)?;
        tag_clauses(&mut st, &k.rings.t, "e", rows, id)?;
        Ok(st)
    };
    build().map_err(jali_error)
}

/// `R_Possess` for the public statement $`(\mathsf{hvk}, \varepsilon)`$: the possession equation
/// under the helper key `h`.
pub(crate) fn r_possess(k: &Constants, h: &Rq) -> Result<Statement, Error> {
    let build = || -> Result<Statement, jali::Error> {
        let mut st = Statement::new(k.rings.c.clone());
        declare_credential(&mut st, POSSESS_S_PLACEMENT)?;
        possession_equation(&mut st, k, h)?;
        Ok(st)
    };
    build().map_err(jali_error)
}

/// The blocks of a credential as a witness: `s` = $`(s_0, s_1)`$, `x1`, `usk`, `x0`.
fn credential_blocks(
    ring: &Arc<Ring>,
    cred: &VSISCredential,
    usk: &Ternary,
) -> Result<Witness, Error> {
    let pre = cred.pre();
    let x0 = cred.x0();
    Ok(BTreeMap::from([
        (
            "s".to_string(),
            vec![
                int_poly(ring, pre.s0().iter().map(|&x| i128::from(x)))?,
                int_poly(ring, pre.s1().iter().map(|&x| i128::from(x)))?,
            ],
        ),
        ("x1".to_string(), vec![ternary_poly(ring, pre.x1())?]),
        ("usk".to_string(), vec![ternary_poly(ring, usk)?]),
        (
            "x0".to_string(),
            x0.iter()
                .map(|x| ternary_poly(ring, x))
                .collect::<Result<_, _>>()?,
        ),
    ]))
}

/// The witness of `R_Tag`: `usk` and the rounding errors `e` of the tag at its point.
pub(crate) fn tag_witness(
    rings: &Rings,
    usk: &Ternary,
    e: &RoundingError,
) -> Result<Witness, Error> {
    let rc = &rings.c;
    Ok(BTreeMap::from([
        ("usk".to_string(), vec![ternary_poly(rc, usk)?]),
        ("e".to_string(), e_subring(rc, e.entries())?),
    ]))
}

/// The witness of `R_att`: the credential blocks and the rounding errors of the attestation
/// tag at $`x_Q`$.
pub(crate) fn att_witness(
    rings: &Rings,
    cred: &VSISCredential,
    usk: &Ternary,
    e: &RoundingError,
) -> Result<Witness, Error> {
    let mut w = credential_blocks(&rings.c, cred, usk)?;
    w.insert("e".to_string(), e_subring(&rings.c, e.entries())?);
    Ok(w)
}

/// The witness of `R_iss`: `usk`, $`x_0`$ and the rounding errors of the identifier at the
/// identifier point.
pub(crate) fn iss_witness(
    rings: &Rings,
    usk: &Ternary,
    tape: &VSISTape,
    e: &RoundingError,
) -> Result<Witness, Error> {
    let rc = &rings.c;
    let x0 = tape.x0();
    Ok(BTreeMap::from([
        ("usk".to_string(), vec![ternary_poly(rc, usk)?]),
        (
            "x0".to_string(),
            x0.iter()
                .map(|x| ternary_poly(rc, x))
                .collect::<Result<_, _>>()?,
        ),
        ("e".to_string(), e_subring(rc, e.entries())?),
    ]))
}

/// The witness of `R_Possess`: the credential blocks.
pub(crate) fn possess_witness(
    rings: &Rings,
    cred: &VSISCredential,
    usk: &Ternary,
) -> Result<Witness, Error> {
    credential_blocks(&rings.c, cred, usk)
}

/// Compiles `statement` against the parameter set of `set` and proves it for `witness` under
/// `context`, in this build's mode ([`STRAIGHT_LINE`]): the seed bridge. Each attempt draws a
/// FRESH 32-byte seed from `rng` (the seed buffer is wiped on drop, and Jali wipes its copy), and
/// a `RestartLimit` is retried with a new seed, at most [`MAX_PROOF_ATTEMPTS`] times.
///
/// # Errors
/// [`Error::WitnessDoesNotSatisfyRelation`] if Jali's witness map refuses the witness (the honest
/// prover's check: a norm, a subring position, or a constraint). [`Error::LatticeBackend`] if
/// the statement does not compile against the set, or after [`MAX_PROOF_ATTEMPTS`] restarts.
pub(crate) fn prove<R: RngCore + CryptoRng + ?Sized>(
    statement: &Statement,
    set: ProofSet<'_>,
    pp_seed: [u8; 32],
    witness: &Witness,
    context: &[u8],
    rng: &mut R,
) -> Result<Vec<u8>, Error> {
    let compiled = statement.compile(set.params.clone()).map_err(jali_error)?;
    for _ in 0..MAX_PROOF_ATTEMPTS {
        let seed = fresh_seed(rng);
        match prove_in_mode(&compiled, set, pp_seed, witness, context, *seed) {
            Err(jali::Error::RestartLimit) => {}
            result => return result.map_err(jali_error),
        }
    }
    Err(Error::LatticeBackend(format!(
        "jali: the prover exhausted its restarts with {MAX_PROOF_ATTEMPTS} fresh seeds"
    )))
}

/// One proof with `seed`: Jali's straight-line extractable mode with the extraction set of `set`
/// in the extractable build, plain Fiat–Shamir otherwise.
fn prove_in_mode(
    compiled: &Compiled,
    set: ProofSet<'_>,
    pp_seed: [u8; 32],
    witness: &Witness,
    context: &[u8],
    seed: [u8; 32],
) -> Result<Vec<u8>, jali::Error> {
    if STRAIGHT_LINE {
        compiled.prove_extractable_bytes_with_seed(pp_seed, set.extraction, witness, context, seed)
    } else {
        compiled.prove_bytes_with_seed(pp_seed, witness, context, seed)
    }
}

/// Compiles `statement` against the parameter set of `set` and verifies the proof `bytes` under
/// `context`, in this build's mode ([`STRAIGHT_LINE`]): a proof of the other mode is refused.
///
/// # Errors
/// [`Error::InvalidProof`] if Jali rejects the proof or its encoding.
/// [`Error::LatticeBackend`] if the statement does not compile (it always does for the
/// statements of this module).
pub(crate) fn verify(
    statement: &Statement,
    set: ProofSet<'_>,
    pp_seed: [u8; 32],
    bytes: &[u8],
    context: &[u8],
) -> Result<(), Error> {
    let compiled = statement.compile(set.params.clone()).map_err(jali_error)?;
    if STRAIGHT_LINE {
        compiled.verify_extractable_bytes(pp_seed, set.extraction, bytes, context)
    } else {
        compiled.verify_bytes(pp_seed, bytes, context)
    }
    .map_err(jali_error)
}

/// The statements at their WORST-CASE public data, the export the parameter sets are derived
/// from: every public coefficient at the largest centred absolute value of its modulus, so that
/// the bounds Jali derives from the constants (`max_integer_coefficient`, `linf_bound`) hold for
/// every instance. `(name, statement)` for `tag`, `att`, `iss` and `possess`.
#[cfg(test)]
pub(crate) fn worst_case_statements() -> Result<Vec<(&'static str, Statement)>, Error> {
    // (q - 1)/2 is the largest |x| in (-q/2, q/2]; q_t/2 = 491,520 the largest in the tag ring
    let max_q = vec![(Q - 1) / 2; D];
    let max_rq = Rq::from_coeffs(&max_q)?;
    let sigma = VSISParams::worst_case(max_rq.clone());
    let k = Constants::new(&sigma)?;
    let matrix = TagMatrix::from_entries(vec![Q_T / 2; M * D])?;
    let rows = TagRows::new(&k.rings, &matrix)?;
    // γ T_j ≡ q_t/2 (mod q_t) at T_j = 2^15: the constant of every clause at its largest
    let tag = [i128::from(Q_T / 2 / GAMMA); M];
    Ok(vec![
        ("tag", r_tag(&k, &rows, &tag)?),
        ("att", r_att(&k, &max_rq, &rows, &tag)?),
        ("iss", r_iss(&k, &max_rq, &rows, &tag)?),
        ("possess", r_possess(&k, &max_rq)?),
    ])
}

#[cfg(test)]
mod tests {
    use jali::{math::U256, params::TboxParams};
    use rand::{RngCore, SeedableRng, rngs::StdRng};

    use super::{
        super::{
            LatticeParams, LatticePoint,
            base::{VSIS, VSISPreCredential, VSISSigningKey, VSISVerificationKey},
        },
        *,
    };
    use crate::{
        lattice::{P, sets::ParameterSets},
        pcreds::ProofKind,
    };

    const LABEL: &[u8] = b"PCREDS-LATTICE-RELATION-TESTS";

    /// The probe modulus of the export: a prime that no constraint uses, so that every
    /// constraint is lifted as at the proof modulus the tool will choose
    /// (`tools/params/README.md` of Jali, "Deriving a parameter set", step 1).
    const PROBE_MODULUS: u64 = 1_099_511_627_917;

    /// One deployment with ONE real helper key (TrapGen).
    struct Fixture {
        params: LatticeParams,
        vk: VSISVerificationKey,
        sk: VSISSigningKey,
        rng: StdRng,
    }

    fn fixture(seed: u64) -> Fixture {
        let mut rng = StdRng::seed_from_u64(seed);
        let params = LatticeParams::derive(LABEL).unwrap();
        let (vk, sk) = VSIS::keygen(&mut rng);
        Fixture {
            params,
            vk,
            sk,
            rng,
        }
    }

    impl Fixture {
        fn k(&self) -> &Constants {
            self.params.constants()
        }

        fn sets(&self) -> &ParameterSets {
            self.params.parameter_sets()
        }

        /// A user key and a credential of the helper on it.
        fn holder(&mut self) -> (Ternary, VSISCredential) {
            let usk = Ternary::sample(&mut self.rng);
            let tape = VSISTape::sample(&mut self.rng);
            let c = VSIS::prepare_issue(self.params.sigma(), &usk, &tape).unwrap();
            let pre = VSIS::blind_issue(self.params.sigma(), &self.sk, &c, &mut self.rng).unwrap();
            let cred = VSIS::unblind(self.params.sigma(), &self.vk, &usk, &pre, &tape).unwrap();
            (usk, cred)
        }

        /// The identifier point `x_0 = H_id(⟨hvk⟩)` of the fixture's helper key, as the
        /// protocol derives it.
        fn x0(&self) -> LatticePoint {
            let pcreds = crate::pcreds::lattice::LatticeProtocol::setup(LABEL).unwrap();
            pcreds.identifier_point(&self.vk).unwrap()
        }

        /// A fresh recipient point.
        fn recipient(&mut self) -> LatticePoint {
            let mut d = [0u8; 32];
            self.rng.fill_bytes(&mut d);
            LatticePoint::Request(d)
        }

        /// `map_witness` of `statement` compiled against `set`: the honest prover's witness
        /// check.
        fn check(&self, statement: &Statement, set: &TboxParams, w: &Witness) -> bool {
            statement
                .compile(set.clone())
                .unwrap()
                .map_witness(w)
                .is_ok()
        }
    }

    fn ints(ring: &Arc<Ring>, s: &[i32]) -> Poly {
        int_poly(ring, s.iter().map(|&x| i128::from(x))).unwrap()
    }

    /// The coefficients of `x` with coefficient `i` replaced by `value`.
    fn with_coefficient(x: &Ternary, i: usize, value: i128) -> Vec<i128> {
        let mut c: Vec<i128> = x.coeffs().iter().map(|&v| i128::from(v)).collect();
        c[i] = value;
        c
    }

    /// `x` as an element of R_q, from integer coefficients.
    fn rq_of(c: &[i128]) -> Rq {
        Rq::from_i64(&c.iter().map(|&x| x as i64).collect::<Vec<_>>()).unwrap()
    }

    /// The tag evaluation of the validation harness on an arbitrary integer key, e.g. one with a
    /// coefficient 2: the rounding error stays within 7 whatever the key's norm.
    fn tag_eval_ints(usk: &[i128], a: &TagMatrix) -> ([i128; M], [i8; M]) {
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

    /// The blocks of a statement: `(name, rows, norm, placement)`.
    fn shape(st: &Statement) -> Vec<(String, usize, Norm, Placement)> {
        st.blocks(crate::lattice::PROOF_DEGREE)
            .unwrap()
            .into_iter()
            .map(|b| (b.name, b.rows, b.norm, b.placement))
            .collect()
    }

    fn block(
        name: &str,
        rows: usize,
        norm: Norm,
        p: Placement,
    ) -> (String, usize, Norm, Placement) {
        (name.to_string(), rows, norm, p)
    }

    /// The statements have the layouts their parameter sets were derived for: each compiles
    /// against its own set and no other, at worst-case public data and on a real instance.
    #[test]
    fn the_statements_compile_against_their_parameter_sets() {
        let f = fixture(0x7e1_0001);
        let sets = f.sets();
        let named = [
            ("tag", &sets.tag),
            ("att", &sets.att),
            ("iss", &sets.iss),
            ("possess", &sets.possess),
        ];
        for (name, st) in worst_case_statements().unwrap() {
            for (other, set) in named {
                assert_eq!(
                    st.compile((*set).clone()).is_ok(),
                    name == other,
                    "{name} against {other}"
                );
            }
        }
        let exact = |b| Norm::LinfExact(b);
        let (a, b) = (Placement::Ajtai, Placement::Bdlop);
        let credential = [
            block("s", 16, S_NORM, b),
            block("x1", 16, exact(1), a),
            block("usk", 16, exact(1), a),
            block("x0", 16 * ELL_R, exact(1), a),
        ];
        let e = block("e", 8, exact(7), a);
        let statements = worst_case_statements().unwrap();
        assert_eq!(
            shape(&statements[0].1),
            [block("usk", 16, exact(1), a), e.clone()]
        );
        let mut att = credential.to_vec();
        att.push(e.clone());
        assert_eq!(shape(&statements[1].1), att);
        assert_eq!(
            shape(&statements[2].1),
            [
                block("usk", 16, exact(1), a),
                block("x0", 16 * ELL_R, exact(1), a),
                e
            ]
        );
        assert_eq!(shape(&statements[3].1), credential);
        assert_eq!(POSSESS_S_PLACEMENT, Placement::Bdlop);
    }

    /// The exports under `tools/lattice/sets/` (the input of the derivation of the sets) are the
    /// ones these statements give: a change of a statement shows up here before it shows up as a
    /// set that does not compile.
    #[test]
    fn the_committed_exports_are_current() {
        let committed = [
            (
                "tag",
                include_str!("../../../tools/lattice/sets/tag.export.json"),
            ),
            (
                "att",
                include_str!("../../../tools/lattice/sets/att.export.json"),
            ),
            (
                "iss",
                include_str!("../../../tools/lattice/sets/iss.export.json"),
            ),
            (
                "possess",
                include_str!("../../../tools/lattice/sets/possess.export.json"),
            ),
        ];
        for ((name, st), (file, json)) in
            worst_case_statements().unwrap().into_iter().zip(committed)
        {
            assert_eq!(name, file);
            let requirements = st
                .requirements(crate::lattice::PROOF_DEGREE, U256::from_u64(PROBE_MODULUS))
                .unwrap();
            let now = serde_json::json!({
                "requirements": requirements,
                "blocks": st.blocks(crate::lattice::PROOF_DEGREE).unwrap(),
            });
            let then: serde_json::Value = serde_json::from_str(json).unwrap();
            assert_eq!(now, then, "{name}");
        }
    }

    /// Honest witnesses satisfy their relations (Jali's witness map accepts them).
    #[test]
    fn honest_witnesses_satisfy_the_relations() {
        let mut f = fixture(0x7e1_0002);
        let (usk, cred) = f.holder();
        let xq = f.recipient();
        let k = f.k();
        let rings = &k.rings;
        // R_Tag at x_0 and at x_Q
        for point in [f.x0(), xq.clone()] {
            let (t, e) = f.params.eval(&usk, &point).unwrap();
            let st = r_tag(k, &f.params.rows(&point).unwrap(), &tag_values(&t)).unwrap();
            assert!(f.check(&st, &f.sets().tag, &tag_witness(rings, &usk, &e).unwrap()));
        }
        // R_att at x_Q
        let (t, e) = f.params.eval(&usk, &xq).unwrap();
        let st = r_att(k, f.vk.h(), &f.params.rows(&xq).unwrap(), &tag_values(&t)).unwrap();
        assert!(f.check(
            &st,
            &f.sets().att,
            &att_witness(rings, &cred, &usk, &e).unwrap()
        ));
        // R_iss at x_0
        let tape = VSISTape::new(cred.x0().clone());
        let c = VSIS::prepare_issue(f.params.sigma(), &usk, &tape).unwrap();
        let (id, e0) = f.params.eval(&usk, &f.x0()).unwrap();
        let st = r_iss(k, &c, &f.params.rows(&f.x0()).unwrap(), &tag_values(&id)).unwrap();
        assert!(f.check(
            &st,
            &f.sets().iss,
            &iss_witness(rings, &usk, &tape, &e0).unwrap()
        ));
        // R_Possess
        let st = r_possess(k, f.vk.h()).unwrap();
        assert!(f.check(
            &st,
            &f.sets().possess,
            &possess_witness(rings, &cred, &usk).unwrap()
        ));
    }

    /// False witnesses are refused by the honest prover's check: another key, a tag at another
    /// point, another opening of C, another helper key, and a credential whose x_1, usk or x_0
    /// has a coefficient 2 together with a REAL preimage of the helper key for exactly that
    /// message (the exact ℓ∞ bounds are what refuses those).
    #[test]
    fn false_witnesses_are_refused() {
        let mut f = fixture(0x7e1_0003);
        let (usk, cred) = f.holder();
        let (other_usk, other_cred) = f.holder();
        let xq = f.recipient();
        let k = f.k().clone();
        let rings = &k.rings;
        let ring = &rings.c;
        let sets = f.sets().clone();
        let rows = f.params.rows(&xq).unwrap();
        let (t, e) = f.params.eval(&usk, &xq).unwrap();

        // R_Tag: the key of another user, the tag of another point
        let st = r_tag(&k, &rows, &tag_values(&t)).unwrap();
        let (_, e_other) = f.params.eval(&other_usk, &xq).unwrap();
        assert!(!f.check(
            &st,
            &sets.tag,
            &tag_witness(rings, &other_usk, &e_other).unwrap()
        ));
        let (_, e0) = f.params.eval(&usk, &f.x0()).unwrap();
        assert!(!f.check(&st, &sets.tag, &tag_witness(rings, &usk, &e0).unwrap()));
        assert!(f.check(&st, &sets.tag, &tag_witness(rings, &usk, &e).unwrap()));

        // R_att: the credential of another user with this user's tag; this user's credential
        // under another helper key
        let st = r_att(&k, f.vk.h(), &rows, &tag_values(&t)).unwrap();
        assert!(!f.check(
            &st,
            &sets.att,
            &att_witness(rings, &other_cred, &usk, &e).unwrap()
        ));
        let (vk2, _) = VSIS::keygen(&mut f.rng);
        let st2 = r_att(&k, vk2.h(), &rows, &tag_values(&t)).unwrap();
        assert!(!f.check(
            &st2,
            &sets.att,
            &att_witness(rings, &cred, &usk, &e).unwrap()
        ));

        // R_iss: the opening of another user's request
        let tape = VSISTape::new(cred.x0().clone());
        let c = VSIS::prepare_issue(f.params.sigma(), &usk, &tape).unwrap();
        let (id, e_id) = f.params.eval(&usk, &f.x0()).unwrap();
        let x0_rows = f.params.rows(&f.x0()).unwrap();
        let st = r_iss(&k, &c, &x0_rows, &tag_values(&id)).unwrap();
        let other_tape = VSISTape::new(other_cred.x0().clone());
        assert!(!f.check(
            &st,
            &sets.iss,
            &iss_witness(rings, &usk, &other_tape, &e_id).unwrap()
        ));

        // R_Possess: a coefficient 2 in x_1, usk or x_0, with a real preimage of exactly that
        // message; the honest one passes
        let sigma = f.params.sigma().clone();
        let st = r_possess(&k, f.vk.h()).unwrap();
        for which in ["x1", "usk", "x0"] {
            let x1 = if which == "x1" {
                with_coefficient(cred.pre().x1(), 5, 2)
            } else {
                with_coefficient(cred.pre().x1(), 0, i128::from(cred.pre().x1().coeffs()[0]))
            };
            let u = if which == "usk" {
                with_coefficient(&usk, 7, 2)
            } else {
                with_coefficient(&usk, 0, i128::from(usk.coeffs()[0]))
            };
            // x_0 with a coefficient 2 in its first component, or as issued
            let x0: Vec<Vec<i128>> = cred
                .x0()
                .iter()
                .enumerate()
                .map(|(j, x)| {
                    if which == "x0" && j == 0 {
                        with_coefficient(x, 9, 2)
                    } else {
                        x.coeffs().iter().map(|&v| i128::from(v)).collect()
                    }
                })
                .collect();
            // t = (v - x_1)^{-1} + b_u usk + B_r x_0, and a preimage of it
            let y = sigma.v().sub(&rq_of(&x1)).inverse().unwrap();
            let target = sigma
                .b_r()
                .iter()
                .zip(&x0)
                .fold(y.add(&sigma.b_u().mul(&rq_of(&u))), |t, (b, x)| {
                    t.add(&b.mul(&rq_of(x)))
                });
            let s = f.sk.sample_preimage(&target, &mut f.rng).unwrap();
            let w = BTreeMap::from([
                (
                    "s".to_string(),
                    vec![ints(ring, s.s0()), ints(ring, s.s1())],
                ),
                ("x1".to_string(), vec![int_poly(ring, x1.clone()).unwrap()]),
                ("usk".to_string(), vec![int_poly(ring, u.clone()).unwrap()]),
                (
                    "x0".to_string(),
                    x0.iter()
                        .map(|x| int_poly(ring, x.clone()).unwrap())
                        .collect(),
                ),
            ]);
            assert!(!f.check(&st, &sets.possess, &w), "{which} = 2");
        }
        assert!(f.check(
            &st,
            &sets.possess,
            &possess_witness(rings, &cred, &usk).unwrap()
        ));
    }

    /// `s = 0` under public parameters crafted so that the possession equation holds for it
    /// ($`b_u = -(v - x_1)^{-1}`$, $`\mathsf{usk} = 1`$, $`x_0 = 0`$): every other condition of
    /// `R_Possess` holds, and the lower bound of [`S_NORM`] refuses the witness
    /// ($`\Pi_{\Possess}`$: $`1 \le \|s\|^2`$). Under the upper bound alone, which the first port
    /// proved, it was a witness.
    #[test]
    fn s_equal_to_zero_is_refused_by_the_lower_bound() {
        let mut f = fixture(0x7e1_0006);
        let (_, cred) = f.holder();
        let sigma = f.params.sigma().clone();
        let x1 = cred.pre().x1();
        let g = sigma.v().sub(&x1.to_rq());
        let y = g.inverse().unwrap();
        let crafted = VSISParams::from_elements(sigma.v().clone(), y.neg(), sigma.b_r().clone());
        // (A·0 − b_u·1 − B_r·0)(v − x_1) = y (v − x_1) = 1
        assert_eq!(y.mul(&g), Rq::one());
        let k = Constants::new(&crafted).unwrap();
        let ring = &k.rings.c;
        let mut one = vec![0i128; D];
        one[0] = 1;
        let zero = || int_poly(ring, vec![0i128; D]).unwrap();
        let w = BTreeMap::from([
            ("s".to_string(), vec![zero(), zero()]),
            ("x1".to_string(), vec![ternary_poly(ring, x1).unwrap()]),
            ("usk".to_string(), vec![int_poly(ring, one).unwrap()]),
            ("x0".to_string(), (0..ELL_R).map(|_| zero()).collect()),
        ]);
        let st = r_possess(&k, f.vk.h()).unwrap();
        assert!(!f.check(&st, &f.sets().possess, &w));
        assert_eq!(
            S_NORM,
            Norm::L2SquaredRange {
                min: 1,
                max: S_BOUND
            }
        );
    }

    /// A key with a coefficient 2 has a tag at x_Q whose rounding error is within 7, and the
    /// tag clauses alone accept it; only the exact bound on `usk` refuses the witness.
    #[test]
    fn the_key_bound_is_what_refuses_a_long_key() {
        let mut f = fixture(0x7e1_0004);
        let (usk, _) = f.holder();
        let xq = f.recipient();
        let a = f.params.matrix(&xq);
        let long = with_coefficient(&usk, 3, 2);
        let (t, e) = tag_eval_ints(&long, &a);
        let k = f.k();
        let st = r_tag(k, &f.params.rows(&xq).unwrap(), &t).unwrap();
        let w = BTreeMap::from([
            ("usk".to_string(), vec![int_poly(&k.rings.c, long).unwrap()]),
            ("e".to_string(), e_subring(&k.rings.c, &e).unwrap()),
        ]);
        assert!(e.iter().all(|&x| u64::from(x.unsigned_abs()) <= E_BOUND));
        assert!(!f.check(&st, &f.sets().tag, &w));
    }

    /// A non-canonical tag `T + p` has exactly the witnesses of `T`: the constants are reduced
    /// modulo q_t, so the range check `t ∈ T` of the verifier is what refuses it (the type
    /// `LWRTag` cannot represent one).
    #[test]
    fn non_canonical_tags_have_the_witnesses_of_canonical_ones() {
        let mut f = fixture(0x7e1_0005);
        let (usk, _) = f.holder();
        let xq = f.recipient();
        let (t, e) = f.params.eval(&usk, &xq).unwrap();
        let mut shifted = tag_values(&t);
        shifted[17] += i128::from(P);
        let k = f.k();
        let rows = f.params.rows(&xq).unwrap();
        let st = r_tag(k, &rows, &shifted).unwrap();
        assert!(f.check(
            &st,
            &f.sets().tag,
            &tag_witness(&k.rings, &usk, &e).unwrap()
        ));
    }

    /// Real proofs: each relation proves and verifies, and a proof does not verify under another
    /// context, for another statement, or under another relation's parameter set. Heavy (Jali
    /// proofs of seconds each); runs in release builds.
    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "heavy: Jali proofs; runs in release builds"
    )]
    fn proofs_verify_and_are_bound_to_their_statement_and_context() {
        let mut f = fixture(0x7e1_0006);
        let (usk, cred) = f.holder();
        let xq = f.recipient();
        let k = f.k().clone();
        let rings = &k.rings;
        let sets = f.sets().clone();
        let seed = *f.params.jali_pp_seed();
        let (ctx, other_ctx) = ([1u8; 32], [2u8; 32]);
        let (t, e) = f.params.eval(&usk, &xq).unwrap();
        let rows = f.params.rows(&xq).unwrap();

        // R_att
        let st = r_att(&k, f.vk.h(), &rows, &tag_values(&t)).unwrap();
        let w = att_witness(rings, &cred, &usk, &e).unwrap();
        let proof = prove(
            &st,
            sets.of(ProofKind::Attestation),
            seed,
            &w,
            &ctx,
            &mut f.rng,
        )
        .unwrap();
        assert!(proof.len() <= crate::lattice::sets::ATT_PROOF_MAX_BYTES);
        assert_eq!(
            verify(&st, sets.of(ProofKind::Attestation), seed, &proof, &ctx),
            Ok(())
        );
        assert_eq!(
            verify(
                &st,
                sets.of(ProofKind::Attestation),
                seed,
                &proof,
                &other_ctx
            ),
            Err(Error::InvalidProof)
        );
        let (vk2, _) = VSIS::keygen(&mut f.rng);
        let st2 = r_att(&k, vk2.h(), &rows, &tag_values(&t)).unwrap();
        assert_eq!(
            verify(&st2, sets.of(ProofKind::Attestation), seed, &proof, &ctx),
            Err(Error::InvalidProof)
        );

        // R_Tag
        let st = r_tag(&k, &rows, &tag_values(&t)).unwrap();
        let w = tag_witness(rings, &usk, &e).unwrap();
        let proof = prove(
            &st,
            sets.of(ProofKind::Identifier),
            seed,
            &w,
            &ctx,
            &mut f.rng,
        )
        .unwrap();
        assert!(proof.len() <= crate::lattice::sets::TAG_PROOF_MAX_BYTES);
        assert_eq!(
            verify(&st, sets.of(ProofKind::Identifier), seed, &proof, &ctx),
            Ok(())
        );
        assert_eq!(
            verify(
                &st,
                sets.of(ProofKind::Identifier),
                seed,
                &proof,
                &other_ctx
            ),
            Err(Error::InvalidProof)
        );
        let (id, _) = f.params.eval(&usk, &f.x0()).unwrap();
        let x0_rows = f.params.rows(&f.x0()).unwrap();
        let elsewhere = r_tag(&k, &x0_rows, &tag_values(&id)).unwrap();
        assert_eq!(
            verify(
                &elsewhere,
                sets.of(ProofKind::Identifier),
                seed,
                &proof,
                &ctx
            ),
            Err(Error::InvalidProof)
        );

        // R_iss
        let tape = VSISTape::new(cred.x0().clone());
        let c = VSIS::prepare_issue(f.params.sigma(), &usk, &tape).unwrap();
        let (_, e0) = f.params.eval(&usk, &f.x0()).unwrap();
        let st = r_iss(&k, &c, &x0_rows, &tag_values(&id)).unwrap();
        let w = iss_witness(rings, &usk, &tape, &e0).unwrap();
        let proof = prove(
            &st,
            sets.of(ProofKind::Issuance),
            seed,
            &w,
            &ctx,
            &mut f.rng,
        )
        .unwrap();
        assert!(proof.len() <= crate::lattice::sets::ISS_PROOF_MAX_BYTES);
        assert_eq!(
            verify(&st, sets.of(ProofKind::Issuance), seed, &proof, &ctx),
            Ok(())
        );
        assert_eq!(
            verify(&st, sets.of(ProofKind::Issuance), seed, &proof, &other_ctx),
            Err(Error::InvalidProof)
        );

        // R_Possess
        let st = r_possess(&k, f.vk.h()).unwrap();
        let w = possess_witness(rings, &cred, &usk).unwrap();
        let proof = prove(
            &st,
            sets.of(ProofKind::Possession),
            seed,
            &w,
            &ctx,
            &mut f.rng,
        )
        .unwrap();
        assert!(proof.len() <= crate::lattice::sets::POSSESS_PROOF_MAX_BYTES);
        assert_eq!(
            verify(&st, sets.of(ProofKind::Possession), seed, &proof, &ctx),
            Ok(())
        );
        assert_eq!(
            verify(
                &st,
                sets.of(ProofKind::Possession),
                seed,
                &proof,
                &other_ctx
            ),
            Err(Error::InvalidProof)
        );
        let st2 = r_possess(&k, vk2.h()).unwrap();
        assert_eq!(
            verify(&st2, sets.of(ProofKind::Possession), seed, &proof, &ctx),
            Err(Error::InvalidProof)
        );
        // a refused witness: the prover maps Jali's witness check
        let other = VSISPreCredential::from_parts(
            cred.pre().s0().to_vec(),
            cred.pre().s1().to_vec(),
            Ternary::zero(),
        )
        .unwrap();
        let bad = possess_witness(
            rings,
            &VSISCredential::from_parts(other, VSISTape::new(cred.x0().clone())),
            &usk,
        )
        .unwrap();
        assert_eq!(
            prove(
                &st,
                sets.of(ProofKind::Possession),
                seed,
                &bad,
                &ctx,
                &mut f.rng
            ),
            Err(Error::WitnessDoesNotSatisfyRelation)
        );
    }

    /// Each build proves and verifies in its own mode only ([`STRAIGHT_LINE`]): a proof of the
    /// other mode, made with Jali directly for the same statement, context and sets, is refused,
    /// and the build's own proof does not verify in the other mode. On `R_Tag`, the cheapest
    /// relation. Heavy (Jali proofs of seconds each), so it runs in release builds.
    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "heavy: Jali proofs, which run in release builds"
    )]
    fn proofs_are_in_the_mode_of_the_build() {
        let mut f = fixture(0x7e1_0007);
        let (usk, _) = f.holder();
        let xq = f.recipient();
        let k = f.k().clone();
        let sets = f.sets().clone();
        let set = sets.of(ProofKind::Identifier);
        let seed = *f.params.jali_pp_seed();
        let ctx = [3u8; 32];
        let (t, e) = f.params.eval(&usk, &xq).unwrap();
        let st = r_tag(&k, &f.params.rows(&xq).unwrap(), &tag_values(&t)).unwrap();
        let w = tag_witness(&k.rings, &usk, &e).unwrap();
        let own = prove(&st, set, seed, &w, &ctx, &mut f.rng).unwrap();
        assert_eq!(verify(&st, set, seed, &own, &ctx), Ok(()));
        // exactly the size of a proof of its build (half the bound), and longer than every plain
        // proof (29,112 bytes for this set) exactly in the extractable build, whose proofs carry
        // the LinHC part
        let size = crate::lattice::sets::TAG_PROOF_MAX_BYTES / 2;
        assert_eq!(own.len(), size, "{} bytes", own.len());
        assert_eq!(own.len() > 29_112, STRAIGHT_LINE, "{} bytes", own.len());
        let compiled = st.compile(set.params.clone()).unwrap();
        let mut proof_seed = [0u8; 32];
        f.rng.fill_bytes(&mut proof_seed);
        let other = if STRAIGHT_LINE {
            compiled.prove_bytes_with_seed(seed, &w, &ctx, proof_seed)
        } else {
            compiled.prove_extractable_bytes_with_seed(seed, set.extraction, &w, &ctx, proof_seed)
        }
        .unwrap();
        assert_eq!(
            verify(&st, set, seed, &other, &ctx),
            Err(Error::InvalidProof)
        );
        let other_mode = if STRAIGHT_LINE {
            compiled.verify_bytes(seed, &own, &ctx)
        } else {
            compiled.verify_extractable_bytes(seed, set.extraction, &own, &ctx)
        };
        assert!(other_mode.is_err());
    }

    /// Writes `Statement::requirements` and `Statement::blocks` of the four statements at their
    /// worst-case public data, at the proof degree 128, to `$PCREDS_EXPORT_DIR/<name>.export.json`:
    /// the input of the requests under `tools/lattice/sets/` (the README there has the
    /// commands).
    #[test]
    #[ignore = "export for Jali's parameter tool: PCREDS_EXPORT_DIR=<dir> cargo test --release --features lattice --lib -- --ignored export_requirements"]
    fn export_requirements() {
        let dir = std::env::var("PCREDS_EXPORT_DIR").expect("PCREDS_EXPORT_DIR");
        for (name, st) in worst_case_statements().unwrap() {
            let requirements = st
                .requirements(crate::lattice::PROOF_DEGREE, U256::from_u64(PROBE_MODULUS))
                .unwrap();
            let json = serde_json::json!({
                "requirements": requirements,
                "blocks": st.blocks(crate::lattice::PROOF_DEGREE).unwrap(),
            });
            let path = std::path::Path::new(&dir).join(format!("{name}.export.json"));
            std::fs::write(&path, serde_json::to_string_pretty(&json).unwrap()).unwrap();
            println!("wrote {}", path.display());
        }
    }
}
