//! Statements of generalized Schnorr proofs: linear relations over prime-order groups, in the
//! representation of the IETF CFRG draft `draft-irtf-cfrg-sigma-protocols-04` ("Sigma -04").
//!
//! The paper (§2.3, "Generalized Schnorr protocols") proves conjunctions of discrete-logarithm
//! representation statements `T_i = ∏_j B_ij^{x_j}`. We use the equivalent "preimage of a group
//! homomorphism" view: a statement is a linear map `φ : F^n → H` into a product `H` of
//! prime-order groups with common scalar field `F`, together with an image `Y ∈ H`. A witness is
//! `x ∈ F^n` with `φ(x) = Y`.
//!
//! A witness coordinate is a [`ScalarVar`]. A coordinate that occurs in several equations is
//! *one* variable, so it gets one mask and one response: the witness-preserving AND composition
//! of Def. "Sigma protocol" holds by construction.
//!
//! # The representation of Sigma -04 (§3.2)
//!
//! A relation over one group is the draft's `LinearRelation`: a list of group elements, where
//! `elements[i]` has the element index `i + 2` (index 0 is the identity and index 1 the generator
//! of the group, both implicit), and a list of equations. An equation ([`IndexedEquation`]) has
//! image terms `(element_index, coeff)`, its left-hand side `Σ coeff · element`, and terms
//! `(scalar_index, element_index, coeff)`, its right-hand side `Σ coeff · x[scalar] · element`.
//! Coefficients are public scalars. A constant of the statement (an element that carries no
//! witness scalar) is an image term, never a term with a scalar "fixed" to 1, and a statement
//! that depends on a sum or a multiple of elements lists each element with its coefficient
//! (§3.2: "all group elements processed by the verifier MUST appear in the statement"). So the
//! clause `t^K = g_1 t^{-x}` of `Tag_DY` is the image `(g_1, 1), (t, −x)` with the term
//! `(K, t, 1)`, never the single element `g_1 − x·t`.
//!
//! [`GroupRelation`] holds a relation over one group in this form. Its builder takes equations
//! by value ([`LinearEquation`]) and interns their elements: the identity becomes index 0, the
//! generator of the group index 1, and every other element gets the next free index at its
//! first occurrence (image terms before terms, in order), so that an element that occurs twice
//! has one index. [`GroupRelation::declare_element`] fixes indices in advance (the draft's
//! compiler assigns them in declaration order, §3.4), and
//! [`GroupRelation::from_instance_bytes`] reads a serialized instance as it is.
//!
//! * [`LinearRelation::validate`] is `ValidateInstance` (§3.5): every count and index below
//!   `2^32`, every element index below `num_elements`, and every element of the list used by
//!   at least one equation.
//! * [`LinearRelation::serialize_instance`] is `SerializeLinearRelation` (§3.6): `LE(4)` counts
//!   and indices, coefficients in the scalar codec, then the elements in the group codec
//!   ([`crate::sigma::codec`]).
//! * [`LinearRelation::num_scalars`] is the draft's `num_scalars`: the largest scalar index that
//!   a term uses, plus one. A variable that is allocated and never used after the last one that
//!   is used is not part of the instance (§3.2), and gets no response.
//!
//! # The pairing extension (this crate, not the draft)
//!
//! [`PairingRelation`] holds equations in `G_1`, in `G_2` and in `G_T` of a pairing `e` over one
//! shared variable space. The draft covers one prime-order group, so:
//!
//! * a [`PairingRelation`] WITHOUT `G_2` and `G_T` equations is the draft's `LinearRelation`
//!   over `G_1`, byte for byte (the same validation, serialization and ciphersuite),
//! * every other [`PairingRelation`] is a relation of this crate's extension, with the
//!   identifier `pcs-sigma-pairing_Shake128_…` in its tag ([`crate::sigma::ciphersuite`]).
//!
//! The extension keeps the draft's structure for each group. `G_1` and `G_2` each have their own
//! element list (indices 0 and 1 the identity and the generator of that group). A `G_T` equation
//! ([`IndexedGtEquation`]) refers to the pairing `e(P, Q)` of a `G_1` element and a `G_2`
//! element by the pair of their indices: image terms `(g1_index, g2_index, coeff)` and terms
//! `(scalar_index, g1_index, g2_index, coeff)`. No element of `G_T` is part of the instance: its
//! bases are pairings of `G_1` and `G_2` elements that are listed individually, so a statement
//! is bound to the pairing preimages, not only to their pairing (`e(2P, Q)` and `e(P, 2Q)` are
//! different statements). Its serialization is
//!
//! ```text
//! SerializePairingRelation(rel) =
//!     equations(G_1 equations) ‖ equations(G_2 equations)
//!     ‖ LE(number of G_T equations, 4)
//!     ‖ for each G_T equation:
//!           LE(number of image terms, 4)
//!           ‖ for each (i_1, i_2, coeff): LE(i_1, 4) ‖ LE(i_2, 4) ‖ scalar(coeff)
//!           ‖ LE(number of terms, 4)
//!           ‖ for each (s, i_1, i_2, coeff): LE(s, 4) ‖ LE(i_1, 4) ‖ LE(i_2, 4) ‖ scalar(coeff)
//!     ‖ LE(number of G_1 elements, 4) ‖ G_1 elements
//!     ‖ LE(number of G_2 elements, 4) ‖ G_2 elements
//! ```
//!
//! where `equations(…)` is the equation part of `SerializeLinearRelation` (the count, then each
//! equation's image terms and terms, §3.6). Every count is explicit and every item has a fixed
//! length, so the encoding is prefix-free and injective. Validation is that of §3.5 for both
//! groups, with the pairs of the `G_T` equations counting as uses of their elements. The
//! commitment of the extension is `G_1 commitments ‖ G_2 commitments ‖ G_T commitments`, each in
//! its group's codec.
//!
//! A `G_T` equation is evaluated lazily: neither prover nor verifier exponentiates in `G_T`. A
//! scalar is multiplied into the `G_1` side of a pair, and the equation costs one multi-pairing
//! (one final exponentiation).

use core::{cell::OnceCell, fmt::Debug};

use ark_ec::{
    CurveGroup, PrimeGroup,
    pairing::{Pairing, PairingOutput},
};
use ark_ff::{One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use super::{
    ciphersuite::{group_suite, pairing_suite},
    codec::{
        element_from_bytes, element_len, read_count, read_scalar, write_count, write_element,
        write_scalar,
    },
};
use crate::error::Error;

/// Handle to a witness coordinate `x_j` of a relation (its scalar index `j`).
///
/// Handles are created by `alloc_scalar` of a relation and are only meaningful for the relation
/// that allocated them (or one with at least as many variables).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScalarVar(usize);

impl ScalarVar {
    /// The index of the coordinate in witness and response vectors.
    #[must_use]
    pub fn index(self) -> usize {
        self.0
    }
}

// ---------------------------------------------------------------------------------------------
// Equations by value: what the relation builders take
// ---------------------------------------------------------------------------------------------

/// One linear equation in the group `G`, by value:
/// `Σ_k a_k · A_k = Σ_i b_i · x[v_i] · B_i` (multiplicatively `∏ A_k^{a_k} = ∏ B_i^{b_i x_{v_i}}`).
///
/// The image terms `(A_k, a_k)` are the left-hand side (the constants of the statement), the
/// terms `(v_i, B_i, b_i)` the right-hand side. The coefficients are public scalars. The order
/// of the tuples follows the draft's `(element_index, coeff)` and
/// `(scalar_index, element_index, coeff)` (§3.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearEquation<G: PrimeGroup> {
    /// The image terms `(element, coefficient)`.
    pub image: Vec<(G, G::ScalarField)>,
    /// The terms `(variable, base, coefficient)`. A variable may occur several times.
    pub terms: Vec<(ScalarVar, G, G::ScalarField)>,
}

impl<G: PrimeGroup> LinearEquation<G> {
    /// The equation `target = Σ_i x[var_i] · base_i`: one image term and every coefficient 1.
    #[must_use]
    pub fn new(terms: Vec<(ScalarVar, G)>, target: G) -> Self {
        let one = G::ScalarField::one();
        Self {
            image: vec![(target, one)],
            terms: terms
                .into_iter()
                .map(|(var, base)| (var, base, one))
                .collect(),
        }
    }

    /// The Schnorr statement `target = x[var] · base` of Def. "Schnorr sigma protocol"
    /// (`T = P^x`).
    #[must_use]
    pub fn dlog(var: ScalarVar, base: G, target: G) -> Self {
        Self::new(vec![(var, base)], target)
    }

    /// The value `Σ_k a_k · A_k` of the left-hand side.
    #[must_use]
    pub fn image_value(&self) -> G {
        self.image
            .iter()
            .map(|(element, coeff)| *element * coeff)
            .sum()
    }

    /// The value `Σ_i b_i · x[v_i] · B_i` of the right-hand side at `scalars`.
    ///
    /// # Errors
    /// [`Error::UnallocatedVariable`] if a variable has no value in `scalars`.
    pub fn evaluate(&self, scalars: &[G::ScalarField]) -> Result<G, Error> {
        let mut acc = G::zero();
        for (var, base, coeff) in &self.terms {
            acc += *base * (*coeff * *lookup(scalars, *var)?);
        }
        Ok(acc)
    }
}

/// A formal sum of pairings `Σ_k e(P_k, Q_k)` (multiplicatively `∏_k e(P_k, Q_k)`), kept
/// unevaluated.
pub type PairingProduct<E> = Vec<(<E as Pairing>::G1, <E as Pairing>::G2)>;

/// One linear equation in `G_T`, by value and in **lazy pairing form**:
/// `Σ_k a_k · e(P_k, Q_k) = Σ_i b_i · x[v_i] · e(P'_i, Q'_i)`.
///
/// Example: the `Σ-PS` possession clause
/// `e(σ'_1, Ỹ)^usk · e(σ'_1, g̃)^t = e(σ'_2, g̃) · e(σ'_1, X̃)^{-1}` has the image terms
/// `(σ'_2, g̃, 1), (σ'_1, X̃, −1)` and the terms `(usk, σ'_1, Ỹ, 1), (t, σ'_1, g̃, 1)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GtEquation<E: Pairing> {
    /// The image terms `(P, Q, coefficient)`: `Σ coeff · e(P, Q)`.
    pub image: Vec<GtImageTerm<E>>,
    /// The terms `(variable, P, Q, coefficient)`: `Σ coeff · x[var] · e(P, Q)`.
    pub terms: Vec<GtTerm<E>>,
}

/// An image term `(P, Q, coeff)` of a [`GtEquation`]: `coeff · e(P, Q)`.
pub type GtImageTerm<E> = (
    <E as Pairing>::G1,
    <E as Pairing>::G2,
    <E as Pairing>::ScalarField,
);

/// A term `(variable, P, Q, coeff)` of a [`GtEquation`]: `coeff · x[variable] · e(P, Q)`.
pub type GtTerm<E> = (
    ScalarVar,
    <E as Pairing>::G1,
    <E as Pairing>::G2,
    <E as Pairing>::ScalarField,
);

impl<E: Pairing> GtEquation<E> {
    /// The equation `Σ e(target) = Σ_i x[var_i] · Σ e(product_i)` with every coefficient 1: a
    /// variable multiplied by a product of pairings becomes one term per pair, with the same
    /// variable (as `Y = x · (E_0 + E_1)` becomes `x · E_0 + x · E_1` in §3.2).
    #[must_use]
    pub fn new(terms: Vec<(ScalarVar, PairingProduct<E>)>, target: PairingProduct<E>) -> Self {
        let one = E::ScalarField::one();
        Self {
            image: target.into_iter().map(|(p, q)| (p, q, one)).collect(),
            terms: terms
                .into_iter()
                .flat_map(|(var, product)| product.into_iter().map(move |(p, q)| (var, p, q, one)))
                .collect(),
        }
    }
}

/// `Σ_k e(P_k, Q_k)` (multiplicatively `∏_k e(P_k, Q_k)`) with one Miller loop per pair and ONE
/// final exponentiation. The empty product is the identity of `G_T`.
///
/// This is the panic-free form of `Pairing::multi_pairing`, shared by the `G_T` equations of
/// this module and by the pairing-product verification equations of the credential bases.
///
/// # Errors
/// [`Error::DegenerateInput`] if the final exponentiation is undefined (a zero Miller-loop
/// value). Implementation note: this does not happen for points of `G_1 × G_2`, identity
/// included. The error exists so that no input can cause a panic.
pub fn pairing_product<E: Pairing>(pairs: &[(E::G1, E::G2)]) -> Result<PairingOutput<E>, Error> {
    let (ps, qs): (Vec<E::G1>, Vec<E::G2>) = pairs.iter().copied().unzip();
    let ps = E::G1::normalize_batch(&ps);
    let qs = E::G2::normalize_batch(&qs);
    // `multi_pairing` unwraps the final exponentiation; going through the `Option` keeps this
    // path panic-free whatever the inputs are.
    E::final_exponentiation(E::multi_miller_loop(ps, qs)).ok_or(Error::DegenerateInput(
        "final exponentiation of a zero Miller loop value",
    ))
}

// ---------------------------------------------------------------------------------------------
// Equations by index: the representation of the draft
// ---------------------------------------------------------------------------------------------

/// An equation of a relation over one group in the sparse form of Sigma -04 §3.2.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexedEquation<F> {
    /// The image terms `(element_index, coeff)`.
    pub image: Vec<(usize, F)>,
    /// The terms `(scalar_index, element_index, coeff)`.
    pub terms: Vec<(ScalarVar, usize, F)>,
}

/// A `G_T` equation of the pairing extension: element references are pairs
/// `(g1_index, g2_index)` standing for `e(P, Q)` (module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexedGtEquation<F> {
    /// The image terms `(g1_index, g2_index, coeff)`.
    pub image: Vec<(usize, usize, F)>,
    /// The terms `(scalar_index, g1_index, g2_index, coeff)`.
    pub terms: Vec<(ScalarVar, usize, usize, F)>,
}

// ---------------------------------------------------------------------------------------------
// The statement interface
// ---------------------------------------------------------------------------------------------

/// The statement interface the sigma protocol ([`crate::sigma::protocol`]) and its Fiat-Shamir
/// transform ([`crate::sigma::fiat_shamir`]) are written against: a linear map `φ : F^n → H`,
/// an image `Y ∈ H`, and the encodings that the Fiat-Shamir transform absorbs.
pub trait LinearRelation {
    /// The common scalar field `F = Z_p` of all groups of the statement, and the challenge
    /// space `C` of the protocol.
    type Scalar: PrimeField;
    /// An element of the image group `H` (one group element per equation).
    type Image: Clone + Debug + PartialEq + Eq + CanonicalSerialize + CanonicalDeserialize;

    /// The number `n` of witness coordinates: `num_scalars` of Sigma -04 §3.2, the largest
    /// scalar index a term uses plus one (0 without terms).
    fn num_scalars(&self) -> usize;

    /// `φ(scalars)`: `map(instance, scalars)` of Sigma -04 §3.3.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless `scalars.len() == self.num_scalars()`.
    fn evaluate(&self, scalars: &[Self::Scalar]) -> Result<Self::Image, Error>;

    /// `φ(z) − c·Y`: the commitment a verifier reconstructs from challenge and responses
    /// (`SimulateCommitment` of Sigma -04 §4.4, multiplicatively `∏ B_i^{z_i} · T^{-c}`).
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless `z.len() == self.num_scalars()`.
    fn recompute_commitment(
        &self,
        c: &Self::Scalar,
        z: &[Self::Scalar],
    ) -> Result<Self::Image, Error>;

    /// Whether `φ(witness) = Y`, i.e. `(statement, witness) ∈ R`. `false` on a wrong length.
    fn is_satisfied_by(&self, witness: &[Self::Scalar]) -> bool;

    /// `ValidateInstance` of Sigma -04 §3.5 (and its analogue for the pairing extension).
    ///
    /// # Errors
    /// [`Error::InvalidInstance`] naming the failed check.
    fn validate(&self) -> Result<(), Error>;

    /// `SerializeLinearRelation` of Sigma -04 §3.6 (or the serialization of the pairing
    /// extension, module docs): the encoded instance that `DeriveChallenge` absorbs. It covers
    /// the shape of the statement and every element and coefficient of it, so a proof is bound
    /// to each of them.
    ///
    /// # Errors
    /// [`Error::InvalidInstance`] for a count or an index of `2^32` or more, and
    /// [`Error::Serialization`] if an element cannot be encoded.
    fn serialize_instance(&self) -> Result<Vec<u8>, Error>;

    /// `Group.serialize(commitment)`: the commitment bytes that `DeriveChallenge` absorbs (per
    /// group, `G_1` then `G_2` then `G_T`, for the pairing extension).
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless `image` has one element per equation, and
    /// [`Error::Serialization`] if an element cannot be encoded.
    fn serialize_image(&self, image: &Self::Image) -> Result<Vec<u8>, Error>;

    /// The ciphersuite identifier that enters the tag ([`crate::sigma::ciphersuite`]).
    fn suite_id(&self) -> String;
}

// ---------------------------------------------------------------------------------------------
// Shared machinery
// ---------------------------------------------------------------------------------------------

/// The element table of one group: identity (index 0), generator (index 1, computed at most
/// once), then the listed elements.
struct Table<'a, G> {
    elements: &'a [G],
    generator: OnceCell<G>,
}

impl<'a, G: PrimeGroup> Table<'a, G> {
    fn new(elements: &'a [G]) -> Self {
        Self {
            elements,
            generator: OnceCell::new(),
        }
    }

    fn get(&self, index: usize) -> Result<G, Error> {
        match index {
            0 => Ok(G::zero()),
            1 => Ok(*self.generator.get_or_init(G::generator)),
            i => self
                .elements
                .get(i - 2)
                .copied()
                .ok_or(Error::InvalidInstance(OUT_OF_RANGE)),
        }
    }
}

const TOO_LARGE: &str = "a count or index of 2^32 or more";
const OUT_OF_RANGE: &str = "an element index beyond the elements of the instance";
const UNUSED: &str = "an element that no equation uses";

/// The index of `value` in the table of `elements`, appending it if it is new: the identity is
/// 0, the generator 1.
fn intern<G: PrimeGroup>(elements: &mut Vec<G>, generator: &OnceCell<G>, value: &G) -> usize {
    if value.is_zero() {
        return 0;
    }
    if value == generator.get_or_init(G::generator) {
        return 1;
    }
    if let Some(i) = elements.iter().position(|e| e == value) {
        return i + 2;
    }
    elements.push(*value);
    elements.len() + 1
}

fn check_vars(vars: impl Iterator<Item = ScalarVar>, allocated: usize) -> Result<(), Error> {
    for var in vars {
        if var.0 >= allocated {
            return Err(Error::UnallocatedVariable {
                index: var.0,
                allocated,
            });
        }
    }
    Ok(())
}

fn lookup<F>(scalars: &[F], var: ScalarVar) -> Result<&F, Error> {
    scalars.get(var.0).ok_or(Error::UnallocatedVariable {
        index: var.0,
        allocated: scalars.len(),
    })
}

fn check_len(expected: usize, actual: usize) -> Result<(), Error> {
    if expected == actual {
        Ok(())
    } else {
        Err(Error::LengthMismatch { expected, actual })
    }
}

/// `scale · element` for a PUBLIC scale, without a multiplication for `0` and `±1`.
fn scaled<G: PrimeGroup>(element: G, scale: G::ScalarField) -> G {
    if scale.is_zero() {
        G::zero()
    } else if scale.is_one() {
        element
    } else if (-scale).is_one() {
        -element
    } else {
        element * scale
    }
}

/// `Σ coeff · x[s] · element(index)` over the terms of `eq`. The scalars may be secret (masks,
/// witness), so every term costs one multiplication, whatever its value.
fn eval_terms<G: PrimeGroup>(
    table: &Table<'_, G>,
    eq: &IndexedEquation<G::ScalarField>,
    scalars: &[G::ScalarField],
) -> Result<G, Error> {
    let mut acc = G::zero();
    for (var, index, coeff) in &eq.terms {
        let x = *lookup(scalars, *var)?;
        if *index != 0 {
            acc += table.get(*index)? * (*coeff * x);
        }
    }
    Ok(acc)
}

/// `factor · Σ coeff · element(index)` over the image terms of `eq`, for a PUBLIC factor.
fn eval_image<G: PrimeGroup>(
    table: &Table<'_, G>,
    eq: &IndexedEquation<G::ScalarField>,
    factor: G::ScalarField,
) -> Result<G, Error> {
    let mut acc = G::zero();
    for (index, coeff) in &eq.image {
        if *index != 0 {
            acc += scaled(table.get(*index)?, factor * coeff);
        }
    }
    Ok(acc)
}

/// The largest scalar index plus one over terms.
fn max_scalar(vars: impl Iterator<Item = ScalarVar>) -> usize {
    vars.map(|v| v.0 + 1).max().unwrap_or(0)
}

/// The uses of the listed elements of one group, for check 3 of §3.5.
struct Uses {
    used: Vec<bool>,
}

impl Uses {
    fn new(listed: usize) -> Self {
        Self {
            used: vec![false; listed],
        }
    }

    /// Checks 1 and 2 of §3.5 for one element index, and records its use.
    fn index(&mut self, index: usize) -> Result<(), Error> {
        fits(index)?;
        if index >= self.used.len() + 2 {
            return Err(Error::InvalidInstance(OUT_OF_RANGE));
        }
        if index >= 2 {
            self.used[index - 2] = true;
        }
        Ok(())
    }

    /// Check 3 of §3.5.
    fn all_used(&self) -> Result<(), Error> {
        if self.used.iter().all(|u| *u) {
            Ok(())
        } else {
            Err(Error::InvalidInstance(UNUSED))
        }
    }
}

/// Check 1 of §3.5 for a count or an index.
fn fits(n: usize) -> Result<(), Error> {
    u32::try_from(n)
        .map(|_| ())
        .map_err(|_| Error::InvalidInstance(TOO_LARGE))
}

/// Checks 1 and 2 of §3.5 for the equations of one group, recording the element uses.
fn validate_equations<F>(equations: &[IndexedEquation<F>], uses: &mut Uses) -> Result<(), Error> {
    fits(equations.len())?;
    for eq in equations {
        fits(eq.image.len())?;
        fits(eq.terms.len())?;
        for (index, _) in &eq.image {
            uses.index(*index)?;
        }
        for (var, index, _) in &eq.terms {
            fits(var.0)?;
            uses.index(*index)?;
        }
    }
    Ok(())
}

/// The equation part of `SerializeLinearRelation` (§3.6, steps 2 to 12).
fn write_equations<F: PrimeField>(
    out: &mut Vec<u8>,
    equations: &[IndexedEquation<F>],
) -> Result<(), Error> {
    write_count(out, equations.len())?;
    for eq in equations {
        write_count(out, eq.image.len())?;
        for (index, coeff) in &eq.image {
            write_count(out, *index)?;
            write_scalar(out, coeff);
        }
        write_count(out, eq.terms.len())?;
        for (var, index, coeff) in &eq.terms {
            write_count(out, var.0)?;
            write_count(out, *index)?;
            write_scalar(out, coeff);
        }
    }
    Ok(())
}

/// `Group.serialize(elements)`.
fn write_elements<G: CanonicalSerialize>(out: &mut Vec<u8>, elements: &[G]) -> Result<(), Error> {
    elements.iter().try_for_each(|e| write_element(out, e))
}

/// The value form of an equation by index.
fn resolve<G: PrimeGroup>(
    table: &Table<'_, G>,
    eq: &IndexedEquation<G::ScalarField>,
) -> Result<LinearEquation<G>, Error> {
    Ok(LinearEquation {
        image: eq
            .image
            .iter()
            .map(|(index, coeff)| Ok((table.get(*index)?, *coeff)))
            .collect::<Result<_, Error>>()?,
        terms: eq
            .terms
            .iter()
            .map(|(var, index, coeff)| Ok((*var, table.get(*index)?, *coeff)))
            .collect::<Result<_, Error>>()?,
    })
}

// ---------------------------------------------------------------------------------------------
// Equations in one group
// ---------------------------------------------------------------------------------------------

/// A conjunction of linear equations in ONE prime-order group `G` over a shared variable space:
/// the draft's `LinearRelation` (§3.2). The statement type of the stand-alone tag proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GroupRelation<G: PrimeGroup> {
    allocated: usize,
    elements: Vec<G>,
    equations: Vec<IndexedEquation<G::ScalarField>>,
}

impl<G: PrimeGroup> Default for GroupRelation<G> {
    fn default() -> Self {
        Self::new()
    }
}

impl<G: PrimeGroup> GroupRelation<G> {
    /// The empty relation: no variables, no elements, no equations.
    #[must_use]
    pub fn new() -> Self {
        Self {
            allocated: 0,
            elements: Vec::new(),
            equations: Vec::new(),
        }
    }

    /// Allocates a fresh witness coordinate.
    pub fn alloc_scalar(&mut self) -> ScalarVar {
        let var = ScalarVar(self.allocated);
        self.allocated += 1;
        var
    }

    /// Allocates `n` fresh witness coordinates.
    pub fn alloc_scalars(&mut self, n: usize) -> Vec<ScalarVar> {
        (0..n).map(|_| self.alloc_scalar()).collect()
    }

    /// The element index of `element`, listing it if it is new (0 for the identity, 1 for the
    /// generator). Elements declared before the equations that use them get their indices in
    /// declaration order, as the draft's compiler assigns them (§3.4). An element that no
    /// equation uses makes the instance invalid (§3.5, check 3).
    pub fn declare_element(&mut self, element: G) -> usize {
        intern(&mut self.elements, &OnceCell::new(), &element)
    }

    /// Adds an equation to the conjunction, listing its new elements (module docs).
    ///
    /// # Errors
    /// [`Error::UnallocatedVariable`] if the equation refers to a variable that was not
    /// allocated in this relation. The relation is unchanged then.
    pub fn add_equation(&mut self, equation: LinearEquation<G>) -> Result<(), Error> {
        check_vars(
            equation.terms.iter().map(|(var, _, _)| *var),
            self.allocated,
        )?;
        let generator = OnceCell::new();
        let elements = &mut self.elements;
        let image = equation
            .image
            .iter()
            .map(|(element, coeff)| (intern(elements, &generator, element), *coeff))
            .collect();
        let terms = equation
            .terms
            .iter()
            .map(|(var, element, coeff)| (*var, intern(elements, &generator, element), *coeff))
            .collect();
        self.equations.push(IndexedEquation { image, terms });
        Ok(())
    }

    /// The listed elements: `elements()[i]` has the element index `i + 2`.
    #[must_use]
    pub fn elements(&self) -> &[G] {
        &self.elements
    }

    /// The element of the given index (0 the identity, 1 the generator), if there is one.
    #[must_use]
    pub fn element(&self, index: usize) -> Option<G> {
        Table::new(&self.elements).get(index).ok()
    }

    /// The equations, by index.
    #[must_use]
    pub fn equations(&self) -> &[IndexedEquation<G::ScalarField>] {
        &self.equations
    }

    /// The equations by value: every index replaced by its element.
    #[must_use]
    pub fn linear_equations(&self) -> Vec<LinearEquation<G>> {
        let table = Table::new(&self.elements);
        // the indices of a relation of this type are in range (validated or interned)
        self.equations
            .iter()
            .filter_map(|eq| resolve(&table, eq).ok())
            .collect()
    }

    /// Reads a relation from its serialization (`SerializeLinearRelation`, §3.6) and validates
    /// it (§3.5). The elements are decoded with full validation. The counts on the wire are
    /// untrusted, and nothing is allocated ahead of the input that backs it.
    ///
    /// The draft specifies the serialization only. This is its inverse, used to run the draft's
    /// test vectors, whose instances are given as bytes.
    ///
    /// # Errors
    /// [`Error::InvalidInstance`] for truncated or malformed input and for an invalid instance,
    /// [`Error::Serialization`] for an invalid group element.
    pub fn from_instance_bytes(bytes: &[u8]) -> Result<Self, Error> {
        const MALFORMED: &str = "a truncated or malformed instance encoding";
        let malformed = || Error::InvalidInstance(MALFORMED);
        let mut input = bytes;
        let num_equations = read_count(&mut input).ok_or_else(malformed)?;
        let mut equations = Vec::new();
        for _ in 0..num_equations {
            let mut image = Vec::new();
            for _ in 0..read_count(&mut input).ok_or_else(malformed)? {
                let index = read_count(&mut input).ok_or_else(malformed)?;
                let coeff = read_scalar(&mut input).ok_or_else(malformed)?;
                image.push((index, coeff));
            }
            let mut terms = Vec::new();
            for _ in 0..read_count(&mut input).ok_or_else(malformed)? {
                let scalar = read_count(&mut input).ok_or_else(malformed)?;
                let index = read_count(&mut input).ok_or_else(malformed)?;
                let coeff = read_scalar(&mut input).ok_or_else(malformed)?;
                terms.push((ScalarVar(scalar), index, coeff));
            }
            equations.push(IndexedEquation { image, terms });
        }
        let ne = element_len::<G>();
        if ne == 0 || !input.len().is_multiple_of(ne) {
            return Err(malformed());
        }
        let elements = input
            .chunks(ne)
            .map(element_from_bytes)
            .collect::<Result<Vec<G>, Error>>()?;
        let mut relation = Self {
            allocated: 0,
            elements,
            equations,
        };
        relation.allocated = relation.num_scalars();
        relation.validate()?;
        Ok(relation)
    }

    fn image_parts(&self, c: &G::ScalarField, z: &[G::ScalarField]) -> Result<Vec<G>, Error> {
        check_len(self.num_scalars(), z.len())?;
        let table = Table::new(&self.elements);
        let minus_c = -*c;
        self.equations
            .iter()
            .map(|eq| Ok(eval_terms(&table, eq, z)? + eval_image(&table, eq, minus_c)?))
            .collect()
    }
}

impl<G: PrimeGroup> LinearRelation for GroupRelation<G> {
    type Scalar = G::ScalarField;
    type Image = Vec<G>;

    fn num_scalars(&self) -> usize {
        max_scalar(
            self.equations
                .iter()
                .flat_map(|eq| eq.terms.iter().map(|(var, _, _)| *var)),
        )
    }

    fn evaluate(&self, scalars: &[Self::Scalar]) -> Result<Self::Image, Error> {
        check_len(self.num_scalars(), scalars.len())?;
        let table = Table::new(&self.elements);
        self.equations
            .iter()
            .map(|eq| eval_terms(&table, eq, scalars))
            .collect()
    }

    fn recompute_commitment(
        &self,
        c: &Self::Scalar,
        z: &[Self::Scalar],
    ) -> Result<Self::Image, Error> {
        self.image_parts(c, z)
    }

    fn is_satisfied_by(&self, witness: &[Self::Scalar]) -> bool {
        self.image_parts(&Self::Scalar::one(), witness)
            .is_ok_and(|image| image.iter().all(Zero::is_zero))
    }

    fn validate(&self) -> Result<(), Error> {
        let mut uses = Uses::new(self.elements.len());
        validate_equations(&self.equations, &mut uses)?;
        uses.all_used()
    }

    fn serialize_instance(&self) -> Result<Vec<u8>, Error> {
        let mut out = Vec::new();
        write_equations(&mut out, &self.equations)?;
        write_elements(&mut out, &self.elements)?;
        Ok(out)
    }

    fn serialize_image(&self, image: &Self::Image) -> Result<Vec<u8>, Error> {
        check_len(self.equations.len(), image.len())?;
        let mut out = Vec::with_capacity(image.len() * element_len::<G>());
        write_elements(&mut out, image)?;
        Ok(out)
    }

    fn suite_id(&self) -> String {
        group_suite::<G>()
    }
}

// ---------------------------------------------------------------------------------------------
// Equations in G_1, G_2 and G_T
// ---------------------------------------------------------------------------------------------

/// An element of the image group `G_1^a × G_2^b × G_T^c` of a [`PairingRelation`]: one group
/// element per equation, in insertion order within each group.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PairingImage<E: Pairing> {
    /// Components of the `G_1` equations.
    pub g1: Vec<E::G1>,
    /// Components of the `G_2` equations.
    pub g2: Vec<E::G2>,
    /// Components of the `G_T` equations.
    pub gt: Vec<PairingOutput<E>>,
}

impl<E: Pairing> PairingImage<E> {
    /// Whether every component is the identity.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.g1.iter().all(Zero::is_zero)
            && self.g2.iter().all(Zero::is_zero)
            && self.gt.iter().all(Zero::is_zero)
    }
}

/// A conjunction of linear equations in `G_1`, `G_2` and `G_T` of a pairing `E` over ONE shared
/// variable space: the statement type of `R_Tag`, `R_att`, `R_iss` and `R_Possess` (§5.1).
/// Without `G_2` and `G_T` equations it is the draft's `LinearRelation` over `G_1`, otherwise a
/// relation of this crate's extension (module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingRelation<E: Pairing> {
    allocated: usize,
    g1_elements: Vec<E::G1>,
    g2_elements: Vec<E::G2>,
    g1: Vec<IndexedEquation<E::ScalarField>>,
    g2: Vec<IndexedEquation<E::ScalarField>>,
    gt: Vec<IndexedGtEquation<E::ScalarField>>,
}

impl<E: Pairing> Default for PairingRelation<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E: Pairing> PairingRelation<E> {
    /// The empty relation: no variables, no elements, no equations.
    #[must_use]
    pub fn new() -> Self {
        Self {
            allocated: 0,
            g1_elements: Vec::new(),
            g2_elements: Vec::new(),
            g1: Vec::new(),
            g2: Vec::new(),
            gt: Vec::new(),
        }
    }

    /// Allocates a fresh witness coordinate.
    pub fn alloc_scalar(&mut self) -> ScalarVar {
        let var = ScalarVar(self.allocated);
        self.allocated += 1;
        var
    }

    /// Allocates `n` fresh witness coordinates.
    pub fn alloc_scalars(&mut self, n: usize) -> Vec<ScalarVar> {
        (0..n).map(|_| self.alloc_scalar()).collect()
    }

    /// [`GroupRelation::declare_element`] for the `G_1` elements.
    pub fn declare_g1_element(&mut self, element: E::G1) -> usize {
        intern(&mut self.g1_elements, &OnceCell::new(), &element)
    }

    /// Adds an equation in `G_1`.
    ///
    /// # Errors
    /// [`Error::UnallocatedVariable`] if the equation refers to an unallocated variable. The
    /// relation is unchanged then.
    pub fn add_g1(&mut self, equation: LinearEquation<E::G1>) -> Result<(), Error> {
        let indexed = Self::index_equation(&mut self.g1_elements, self.allocated, &equation)?;
        self.g1.push(indexed);
        Ok(())
    }

    /// Adds an equation in `G_2`.
    ///
    /// # Errors
    /// [`Error::UnallocatedVariable`] if the equation refers to an unallocated variable. The
    /// relation is unchanged then.
    pub fn add_g2(&mut self, equation: LinearEquation<E::G2>) -> Result<(), Error> {
        let indexed = Self::index_equation(&mut self.g2_elements, self.allocated, &equation)?;
        self.g2.push(indexed);
        Ok(())
    }

    /// Adds an equation in `G_T`, in lazy pairing form.
    ///
    /// # Errors
    /// [`Error::UnallocatedVariable`] if the equation refers to an unallocated variable. The
    /// relation is unchanged then.
    pub fn add_gt(&mut self, equation: GtEquation<E>) -> Result<(), Error> {
        check_vars(
            equation.terms.iter().map(|(var, _, _, _)| *var),
            self.allocated,
        )?;
        let (gen1, gen2) = (OnceCell::new(), OnceCell::new());
        let (g1, g2) = (&mut self.g1_elements, &mut self.g2_elements);
        let image = equation
            .image
            .iter()
            .map(|(p, q, coeff)| (intern(g1, &gen1, p), intern(g2, &gen2, q), *coeff))
            .collect();
        let terms = equation
            .terms
            .iter()
            .map(|(var, p, q, coeff)| (*var, intern(g1, &gen1, p), intern(g2, &gen2, q), *coeff))
            .collect();
        self.gt.push(IndexedGtEquation { image, terms });
        Ok(())
    }

    fn index_equation<G: PrimeGroup>(
        elements: &mut Vec<G>,
        allocated: usize,
        equation: &LinearEquation<G>,
    ) -> Result<IndexedEquation<G::ScalarField>, Error> {
        check_vars(equation.terms.iter().map(|(var, _, _)| *var), allocated)?;
        let generator = OnceCell::new();
        let image = equation
            .image
            .iter()
            .map(|(element, coeff)| (intern(elements, &generator, element), *coeff))
            .collect();
        let terms = equation
            .terms
            .iter()
            .map(|(var, element, coeff)| (*var, intern(elements, &generator, element), *coeff))
            .collect();
        Ok(IndexedEquation { image, terms })
    }

    /// Whether the relation has no `G_2` and no `G_T` equation, and so is the draft's
    /// `LinearRelation` over `G_1` (module docs).
    #[must_use]
    pub fn is_g1_only(&self) -> bool {
        self.g2.is_empty() && self.gt.is_empty()
    }

    /// The listed `G_1` elements: `g1_elements()[i]` has the `G_1` index `i + 2`.
    #[must_use]
    pub fn g1_elements(&self) -> &[E::G1] {
        &self.g1_elements
    }

    /// The listed `G_2` elements: `g2_elements()[i]` has the `G_2` index `i + 2`.
    #[must_use]
    pub fn g2_elements(&self) -> &[E::G2] {
        &self.g2_elements
    }

    /// The `G_1` equations, by index.
    #[must_use]
    pub fn g1_equations(&self) -> &[IndexedEquation<E::ScalarField>] {
        &self.g1
    }

    /// The `G_2` equations, by index.
    #[must_use]
    pub fn g2_equations(&self) -> &[IndexedEquation<E::ScalarField>] {
        &self.g2
    }

    /// The `G_T` equations, by index pairs.
    #[must_use]
    pub fn gt_equations(&self) -> &[IndexedGtEquation<E::ScalarField>] {
        &self.gt
    }

    /// The `G_1` equations by value.
    #[must_use]
    pub fn g1_linear_equations(&self) -> Vec<LinearEquation<E::G1>> {
        let table = Table::new(&self.g1_elements);
        self.g1
            .iter()
            .filter_map(|eq| resolve(&table, eq).ok())
            .collect()
    }

    /// The `G_2` equations by value.
    #[must_use]
    pub fn g2_linear_equations(&self) -> Vec<LinearEquation<E::G2>> {
        let table = Table::new(&self.g2_elements);
        self.g2
            .iter()
            .filter_map(|eq| resolve(&table, eq).ok())
            .collect()
    }

    /// The `G_T` equations by value.
    #[must_use]
    pub fn gt_linear_equations(&self) -> Vec<GtEquation<E>> {
        let (t1, t2) = (Table::new(&self.g1_elements), Table::new(&self.g2_elements));
        let resolve_gt = |eq: &IndexedGtEquation<E::ScalarField>| -> Result<GtEquation<E>, Error> {
            Ok(GtEquation {
                image: eq
                    .image
                    .iter()
                    .map(|(i1, i2, coeff)| Ok((t1.get(*i1)?, t2.get(*i2)?, *coeff)))
                    .collect::<Result<_, Error>>()?,
                terms: eq
                    .terms
                    .iter()
                    .map(|(var, i1, i2, coeff)| Ok((*var, t1.get(*i1)?, t2.get(*i2)?, *coeff)))
                    .collect::<Result<_, Error>>()?,
            })
        };
        self.gt
            .iter()
            .filter_map(|eq| resolve_gt(eq).ok())
            .collect()
    }

    /// `Σ coeff · scale(s) · e(P, Q)` over the given pairs with ONE multi-pairing, for
    /// `scale(s)` the scalar of each pair.
    fn gt_value(
        t1: &Table<'_, E::G1>,
        t2: &Table<'_, E::G2>,
        pairs: impl Iterator<Item = (usize, usize, E::ScalarField)>,
    ) -> Result<PairingOutput<E>, Error> {
        let mut product = Vec::new();
        for (i1, i2, scalar) in pairs {
            // e(1, Q) = e(P, 1) = 1
            if i1 != 0 && i2 != 0 {
                product.push((t1.get(i1)? * scalar, t2.get(i2)?));
            }
        }
        pairing_product::<E>(&product)
    }

    /// The image of `φ(z) − c·Y` (for `c = 0`: `φ(z)`).
    fn image_parts(
        &self,
        c: &E::ScalarField,
        z: &[E::ScalarField],
    ) -> Result<PairingImage<E>, Error> {
        check_len(self.num_scalars(), z.len())?;
        let (t1, t2) = (Table::new(&self.g1_elements), Table::new(&self.g2_elements));
        let minus_c = -*c;
        let g1 = self
            .g1
            .iter()
            .map(|eq| Ok(eval_terms(&t1, eq, z)? + eval_image(&t1, eq, minus_c)?))
            .collect::<Result<_, Error>>()?;
        let g2 = self
            .g2
            .iter()
            .map(|eq| Ok(eval_terms(&t2, eq, z)? + eval_image(&t2, eq, minus_c)?))
            .collect::<Result<_, Error>>()?;
        let gt = self
            .gt
            .iter()
            .map(|eq| {
                let mut pairs = Vec::with_capacity(eq.terms.len() + eq.image.len());
                for (var, i1, i2, coeff) in &eq.terms {
                    pairs.push((*i1, *i2, *coeff * *lookup(z, *var)?));
                }
                if !c.is_zero() {
                    pairs.extend(
                        eq.image
                            .iter()
                            .map(|(i1, i2, coeff)| (*i1, *i2, minus_c * coeff)),
                    );
                }
                Self::gt_value(&t1, &t2, pairs.into_iter())
            })
            .collect::<Result<_, Error>>()?;
        Ok(PairingImage { g1, g2, gt })
    }
}

impl<E: Pairing> LinearRelation for PairingRelation<E> {
    type Scalar = E::ScalarField;
    type Image = PairingImage<E>;

    fn num_scalars(&self) -> usize {
        let linear = self
            .g1
            .iter()
            .chain(&self.g2)
            .flat_map(|eq| eq.terms.iter().map(|(var, _, _)| *var));
        let gt = self
            .gt
            .iter()
            .flat_map(|eq| eq.terms.iter().map(|(var, _, _, _)| *var));
        max_scalar(linear.chain(gt))
    }

    fn evaluate(&self, scalars: &[Self::Scalar]) -> Result<Self::Image, Error> {
        self.image_parts(&Self::Scalar::zero(), scalars)
    }

    fn recompute_commitment(
        &self,
        c: &Self::Scalar,
        z: &[Self::Scalar],
    ) -> Result<Self::Image, Error> {
        self.image_parts(c, z)
    }

    fn is_satisfied_by(&self, witness: &[Self::Scalar]) -> bool {
        self.image_parts(&Self::Scalar::one(), witness)
            .is_ok_and(|image| image.is_zero())
    }

    fn validate(&self) -> Result<(), Error> {
        let mut uses1 = Uses::new(self.g1_elements.len());
        validate_equations(&self.g1, &mut uses1)?;
        if self.is_g1_only() {
            return uses1.all_used();
        }
        let mut uses2 = Uses::new(self.g2_elements.len());
        validate_equations(&self.g2, &mut uses2)?;
        fits(self.gt.len())?;
        for eq in &self.gt {
            fits(eq.image.len())?;
            fits(eq.terms.len())?;
            for (i1, i2, _) in &eq.image {
                uses1.index(*i1)?;
                uses2.index(*i2)?;
            }
            for (var, i1, i2, _) in &eq.terms {
                fits(var.0)?;
                uses1.index(*i1)?;
                uses2.index(*i2)?;
            }
        }
        uses1.all_used()?;
        uses2.all_used()
    }

    fn serialize_instance(&self) -> Result<Vec<u8>, Error> {
        let mut out = Vec::new();
        write_equations(&mut out, &self.g1)?;
        if self.is_g1_only() {
            // SerializeLinearRelation over G_1, exactly as the draft
            write_elements(&mut out, &self.g1_elements)?;
            return Ok(out);
        }
        write_equations(&mut out, &self.g2)?;
        write_count(&mut out, self.gt.len())?;
        for eq in &self.gt {
            write_count(&mut out, eq.image.len())?;
            for (i1, i2, coeff) in &eq.image {
                write_count(&mut out, *i1)?;
                write_count(&mut out, *i2)?;
                write_scalar(&mut out, coeff);
            }
            write_count(&mut out, eq.terms.len())?;
            for (var, i1, i2, coeff) in &eq.terms {
                write_count(&mut out, var.0)?;
                write_count(&mut out, *i1)?;
                write_count(&mut out, *i2)?;
                write_scalar(&mut out, coeff);
            }
        }
        write_count(&mut out, self.g1_elements.len())?;
        write_elements(&mut out, &self.g1_elements)?;
        write_count(&mut out, self.g2_elements.len())?;
        write_elements(&mut out, &self.g2_elements)?;
        Ok(out)
    }

    fn serialize_image(&self, image: &Self::Image) -> Result<Vec<u8>, Error> {
        check_len(self.g1.len(), image.g1.len())?;
        check_len(self.g2.len(), image.g2.len())?;
        check_len(self.gt.len(), image.gt.len())?;
        let mut out = Vec::new();
        write_elements(&mut out, &image.g1)?;
        write_elements(&mut out, &image.g2)?;
        write_elements(&mut out, &image.gt)?;
        Ok(out)
    }

    fn suite_id(&self) -> String {
        if self.is_g1_only() {
            group_suite::<E::G1>()
        } else {
            pairing_suite::<E>()
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
    use ark_ff::UniformRand;
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::sigma::codec::scalar_to_bytes;

    type G1 = G1Projective;
    type G2 = G2Projective;

    fn le4(n: u32) -> Vec<u8> {
        n.to_le_bytes().to_vec()
    }

    fn compressed<G: CanonicalSerialize>(g: &G) -> Vec<u8> {
        let mut out = Vec::new();
        g.serialize_compressed(&mut out).unwrap();
        out
    }

    #[test]
    fn unallocated_variables_are_rejected() {
        let mut big = GroupRelation::<G1>::new();
        let vars = big.alloc_scalars(3);
        assert_eq!(
            vars.iter().map(|v| v.index()).collect::<Vec<_>>(),
            [0, 1, 2]
        );

        let mut small = GroupRelation::<G1>::new();
        let x = small.alloc_scalar();
        let g = G1::generator();
        let h = g * Fr::from(3u64);
        assert_eq!(
            small.add_equation(LinearEquation::dlog(vars[2], h, h)),
            Err(Error::UnallocatedVariable {
                index: 2,
                allocated: 1
            })
        );
        // nothing was listed
        assert!(small.equations().is_empty() && small.elements().is_empty());
        assert_eq!(small.add_equation(LinearEquation::dlog(x, g, g)), Ok(()));

        let mut rel = PairingRelation::<Bls12_381>::new();
        let q = G2::generator() * Fr::from(5u64);
        let unallocated = Err(Error::UnallocatedVariable {
            index: 0,
            allocated: 0,
        });
        assert_eq!(rel.add_g1(LinearEquation::dlog(x, h, h)), unallocated);
        assert_eq!(rel.add_g2(LinearEquation::dlog(x, q, q)), unallocated);
        assert_eq!(
            rel.add_gt(GtEquation::new(vec![(x, vec![(h, q)])], vec![(h, q)])),
            unallocated
        );
        assert_eq!(rel, PairingRelation::new());
    }

    #[test]
    fn wrong_lengths_are_errors_not_panics() {
        let mut rng = StdRng::seed_from_u64(0x5e1a);
        let mut rel = PairingRelation::<Bls12_381>::new();
        let x = rel.alloc_scalar();
        let y = rel.alloc_scalar();
        let (g, h) = (G1::generator(), G2::generator());
        let (a, b) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
        rel.add_g1(LinearEquation::new(
            vec![(x, g), (y, g * a)],
            g * (a + a * b),
        ))
        .unwrap();
        rel.add_gt(GtEquation::new(vec![(y, vec![(g, h)])], vec![(g * b, h)]))
            .unwrap();
        assert!(rel.is_satisfied_by(&[a, b]));
        assert!(!rel.is_satisfied_by(&[b, a]));
        for bad in [&[][..], &[a][..], &[a, b, a][..]] {
            let mismatch = Error::LengthMismatch {
                expected: 2,
                actual: bad.len(),
            };
            assert_eq!(rel.evaluate(bad).unwrap_err(), mismatch);
            assert_eq!(rel.recompute_commitment(&a, bad).unwrap_err(), mismatch);
            assert!(!rel.is_satisfied_by(bad));
        }
    }

    #[test]
    fn empty_relation_is_trivially_satisfied() {
        let rel = GroupRelation::<G1>::new();
        assert!(rel.is_satisfied_by(&[]));
        assert_eq!(rel.evaluate(&[]).unwrap(), Vec::<G1>::new());
        assert_eq!(rel.validate(), Ok(()));
        // the empty relation of the draft's vector E0: `LE(0, 4)`
        assert_eq!(rel.serialize_instance().unwrap(), le4(0));
        let rel = PairingRelation::<Bls12_381>::new();
        assert!(rel.is_satisfied_by(&[]));
        assert!(rel.evaluate(&[]).unwrap().is_zero());
        assert_eq!(rel.serialize_instance().unwrap(), le4(0));
    }

    /// Identity bases, identity images and empty pairing products are legal inputs of the
    /// algebra: they must be evaluated without panicking (rejecting degenerate statements is the
    /// job of the public checks of the caller, not of the relation).
    #[test]
    fn degenerate_statements_do_not_panic() {
        use crate::sigma::{FSProof, fiat_shamir};

        let mut rng = StdRng::seed_from_u64(0x5e1b);
        let (o1, o2) = (G1::zero(), G2::zero());
        let (g, h) = (G1::generator(), G2::generator());
        let mut rel = PairingRelation::<Bls12_381>::new();
        let x = rel.alloc_scalar();
        rel.add_g1(LinearEquation::dlog(x, o1, o1)).unwrap();
        rel.add_g1(LinearEquation::new(vec![], o1)).unwrap();
        rel.add_g2(LinearEquation::dlog(x, o2, o2)).unwrap();
        // the vacuous Σ-PS clause of a degenerate shown credential σ' = (1, 1)
        rel.add_gt(GtEquation::new(
            vec![(x, vec![(o1, h)])],
            vec![(o1, h), (o1, h)],
        ))
        .unwrap();
        rel.add_gt(GtEquation::new(vec![(x, vec![(g, o2)])], vec![]))
            .unwrap();
        rel.add_gt(GtEquation::new(vec![], vec![])).unwrap();
        rel.add_gt(GtEquation::new(vec![(x, vec![])], vec![(o1, o2)]))
            .unwrap();
        // nothing but the identities and the generators: no element is listed
        assert!(rel.g1_elements().is_empty() && rel.g2_elements().is_empty());
        assert_eq!(rel.validate(), Ok(()));

        // vacuous: EVERY scalar is a witness, which is exactly why verifiers must run the
        // non-degeneracy checks themselves
        let any = Fr::rand(&mut rng);
        assert!(rel.is_satisfied_by(&[any]));
        assert!(rel.evaluate(&[any]).unwrap().is_zero());
        let proof = fiat_shamir::prove(&rel, &[any], b"ctx", &mut rng).unwrap();
        assert!(fiat_shamir::verify(&rel, b"ctx", &proof));
        let garbage = FSProof {
            challenge: any,
            responses: vec![Fr::rand(&mut rng)],
        };
        assert!(!fiat_shamir::verify(&rel, b"ctx", &garbage));
    }

    /// The builder lists each element once, with the identity at index 0 and the generator at
    /// index 1, in the order of first occurrence (image terms before terms).
    #[test]
    fn elements_are_interned() {
        let g = G1::generator();
        let (h, t) = (g * Fr::from(7u64), g * Fr::from(11u64));
        let mut rel = GroupRelation::<G1>::new();
        let x = rel.alloc_scalar();
        rel.add_equation(LinearEquation::dlog(x, h, t)).unwrap();
        rel.add_equation(LinearEquation::dlog(x, g, h)).unwrap();
        rel.add_equation(LinearEquation::new(vec![(x, t), (x, G1::zero())], t))
            .unwrap();
        assert_eq!(rel.elements(), [t, h]);
        let one = Fr::one();
        assert_eq!(
            rel.equations(),
            [
                IndexedEquation {
                    image: vec![(2, one)],
                    terms: vec![(x, 3, one)]
                },
                IndexedEquation {
                    image: vec![(3, one)],
                    terms: vec![(x, 1, one)]
                },
                IndexedEquation {
                    image: vec![(2, one)],
                    terms: vec![(x, 2, one), (x, 0, one)]
                },
            ]
        );
        assert_eq!(rel.element(0), Some(G1::zero()));
        assert_eq!(rel.element(1), Some(g));
        assert_eq!(rel.element(4), None);
        // the value form gives the equations back
        assert_eq!(rel.linear_equations()[0], LinearEquation::dlog(x, h, t));
    }

    /// The Chaum-Pedersen relation of Sigma -04 §3.4, declared as `ChaumPedersen(H, X, Y)`,
    /// serializes to the layout that §3.6 prints, and validates.
    #[test]
    fn serialization_follows_section_3_6() {
        let mut rng = StdRng::seed_from_u64(0x5e1c);
        let g = G1::generator();
        let x = Fr::rand(&mut rng);
        let h = g * Fr::rand(&mut rng);
        let (big_x, big_y) = (g * x, h * x);
        let mut rel = GroupRelation::<G1>::new();
        let var = rel.alloc_scalar();
        assert_eq!([h, big_x, big_y].map(|e| rel.declare_element(e)), [2, 3, 4]);
        rel.add_equation(LinearEquation::dlog(var, g, big_x))
            .unwrap();
        rel.add_equation(LinearEquation::dlog(var, h, big_y))
            .unwrap();
        assert_eq!(rel.validate(), Ok(()));
        assert!(rel.is_satisfied_by(&[x]));

        let one = scalar_to_bytes(&Fr::one());
        let expected = [
            le4(2),
            le4(1),
            le4(3),
            one.clone(), // image: X
            le4(1),
            le4(0),
            le4(1),
            one.clone(), // term: x * G
            le4(1),
            le4(4),
            one.clone(), // image: Y
            le4(1),
            le4(0),
            le4(2),
            one, // term: x * H
            compressed(&h),
            compressed(&big_x),
            compressed(&big_y),
        ]
        .concat();
        assert_eq!(rel.serialize_instance().unwrap(), expected);
        // and back
        let parsed = GroupRelation::<G1>::from_instance_bytes(&expected).unwrap();
        assert_eq!(parsed.serialize_instance().unwrap(), expected);
        assert_eq!(parsed.equations(), rel.equations());
        assert_eq!(parsed.elements(), rel.elements());
    }

    #[test]
    fn invalid_instances_are_refused() {
        let g = G1::generator();
        let h = g * Fr::from(3u64);
        // check 3: a declared element that no equation uses
        let mut rel = GroupRelation::<G1>::new();
        let x = rel.alloc_scalar();
        rel.declare_element(g * Fr::from(9u64));
        rel.add_equation(LinearEquation::dlog(x, h, h)).unwrap();
        assert_eq!(rel.validate(), Err(Error::InvalidInstance(UNUSED)));
        // check 2: an index beyond the elements, from the wire (one element follows, index 3)
        let one = scalar_to_bytes(&Fr::one());
        let bytes = [
            le4(1),
            le4(1),
            le4(2),
            one.clone(),
            le4(1),
            le4(0),
            le4(3),
            one.clone(),
            compressed(&h),
        ]
        .concat();
        assert_eq!(
            GroupRelation::<G1>::from_instance_bytes(&bytes).unwrap_err(),
            Error::InvalidInstance(OUT_OF_RANGE)
        );
        // truncation anywhere, and a partial element
        let good = [
            le4(1),
            le4(1),
            le4(2),
            one.clone(),
            le4(1),
            le4(0),
            le4(1),
            one,
            compressed(&h),
        ]
        .concat();
        assert!(GroupRelation::<G1>::from_instance_bytes(&good).is_ok());
        for cut in 0..good.len() {
            assert!(
                GroupRelation::<G1>::from_instance_bytes(&good[..cut]).is_err(),
                "cut at {cut}"
            );
        }
        // a hostile count is refused without an allocation of its size
        let mut hostile = good.clone();
        hostile[..4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(GroupRelation::<G1>::from_instance_bytes(&hostile).is_err());
        // a non-canonical coefficient
        let mut bad = good.clone();
        bad[12..44].copy_from_slice(&[0xff; 32]);
        assert!(GroupRelation::<G1>::from_instance_bytes(&bad).is_err());
    }

    /// A pairing relation without `G_2` and `G_T` equations is the draft's relation over `G_1`.
    /// With them, it has the extension's layout of the module docs.
    #[test]
    fn pairing_relations_serialize_as_documented() {
        let g = G1::generator();
        let (p, t) = (g * Fr::from(5u64), g * Fr::from(15u64));
        let q = G2::generator() * Fr::from(7u64);
        let mut single = GroupRelation::<G1>::new();
        let mut pairing = PairingRelation::<Bls12_381>::new();
        let (x, y) = (single.alloc_scalar(), pairing.alloc_scalar());
        assert_eq!(x, y);
        single.add_equation(LinearEquation::dlog(x, p, t)).unwrap();
        pairing.add_g1(LinearEquation::dlog(x, p, t)).unwrap();
        assert!(pairing.is_g1_only());
        assert_eq!(
            pairing.serialize_instance().unwrap(),
            single.serialize_instance().unwrap()
        );
        assert_eq!(pairing.suite_id(), single.suite_id());

        // one G_T equation: e(t, g̃) = x · e(p, q) − e(p, g̃)·0, written with a coefficient
        let minus = -Fr::one();
        pairing
            .add_gt(GtEquation {
                image: vec![(t, G2::generator(), Fr::one())],
                terms: vec![(x, p, q, Fr::from(3u64)), (x, t, q, minus)],
            })
            .unwrap();
        assert!(!pairing.is_g1_only());
        assert_eq!(pairing.validate(), Ok(()));
        let one = scalar_to_bytes(&Fr::one());
        let expected = [
            // the G_1 equation: t = x · p (t is G_1 index 2, p index 3)
            le4(1),
            le4(1),
            le4(2),
            one.clone(),
            le4(1),
            le4(0),
            le4(3),
            one.clone(),
            // no G_2 equation
            le4(0),
            // one G_T equation: image (t, g̃), terms (x, p, q, 3), (x, t, q, −1)
            le4(1),
            le4(1),
            le4(2),
            le4(1),
            one,
            le4(2),
            le4(0),
            le4(3),
            le4(2),
            scalar_to_bytes(&Fr::from(3u64)),
            le4(0),
            le4(2),
            le4(2),
            scalar_to_bytes(&minus),
            // the elements
            le4(2),
            compressed(&t),
            compressed(&p),
            le4(1),
            compressed(&q),
        ]
        .concat();
        assert_eq!(pairing.serialize_instance().unwrap(), expected);
        assert_eq!(pairing.suite_id(), "pcs-sigma-pairing_Shake128_BLS12381");
        // 3·e(p, q) − e(t, q) = e(t, g̃) holds for no x in general, but evaluates
        let z = [Fr::from(2u64)];
        let image = pairing.evaluate(&z).unwrap();
        let expected_gt =
            pairing_product::<Bls12_381>(&[(p * Fr::from(6u64), q), (t * -Fr::from(2u64), q)])
                .unwrap();
        assert_eq!(image.gt, [expected_gt]);
        let bytes = pairing.serialize_image(&image).unwrap();
        assert_eq!(bytes.len(), 48 + 576);
    }

    /// The statement is bound to its shape, to every element, to the variable of each term and
    /// to the pairing preimages: different relations, different instances.
    #[test]
    fn instance_encoding_separates_statements() {
        let enc = |rel: &PairingRelation<Bls12_381>| rel.serialize_instance().unwrap();
        let g = G1::generator();
        let p = g * Fr::from(2u64);

        // one equation with two terms vs two equations with one term each
        let mut r1 = PairingRelation::<Bls12_381>::new();
        let x = r1.alloc_scalar();
        r1.add_g1(LinearEquation::new(vec![(x, p), (x, p)], p))
            .unwrap();
        let mut r2 = PairingRelation::<Bls12_381>::new();
        let x = r2.alloc_scalar();
        r2.add_g1(LinearEquation::dlog(x, p, p)).unwrap();
        r2.add_g1(LinearEquation::dlog(x, p, p)).unwrap();
        assert_ne!(enc(&r1), enc(&r2));

        // which variable a base belongs to is part of the statement
        let mut r6 = PairingRelation::<Bls12_381>::new();
        let (x, y) = (r6.alloc_scalar(), r6.alloc_scalar());
        let mut r7 = r6.clone();
        r6.add_g1(LinearEquation::new(vec![(x, p), (y, p + p)], p))
            .unwrap();
        r7.add_g1(LinearEquation::new(vec![(y, p), (x, p + p)], p))
            .unwrap();
        assert_ne!(enc(&r6), enc(&r7));

        // the same G_T value from different preimages: e(2P, Q) = e(P, 2Q)
        let q = G2::generator() * Fr::from(3u64);
        let gt = |pq: (G1, G2)| {
            let mut rel = PairingRelation::<Bls12_381>::new();
            let x = rel.alloc_scalar();
            rel.add_gt(GtEquation::new(vec![(x, vec![(p, q)])], vec![pq]))
                .unwrap();
            rel
        };
        assert_ne!(enc(&gt((p + p, q))), enc(&gt((p, q + q))));

        // a trailing unused variable is not part of the instance (§3.2)
        let mut r8 = r2.clone();
        r8.alloc_scalar();
        assert_eq!(enc(&r8), enc(&r2));
        assert_eq!(r8.num_scalars(), r2.num_scalars());
    }
}
