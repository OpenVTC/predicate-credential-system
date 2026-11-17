//! Key-injective pseudorandom functions, the *tags* of the protocol (paper §3.1, Def.
//! "Key-injective PRF"; instantiations in §5.1).
//!
//! Every public value of a user is a tag evaluation under its secret key `usk`: the identifier
//! is `id = Tag(usk, x_0)` at the identifier point `x_0 = H_id(⟨hvk⟩)` of the helper key, and an
//! attestation from `P` to `Q` carries the attestation tag `t_{P→Q} = Tag(usk_P, x_Q)` at the
//! recipient point `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`, `j_Q` the least counter with `x_Q ≠ x_0`
//! (§4.2, "Identifiers and attestation tags").
//!
//! ```math
//! id = \mathsf{Tag}(usk, x_0), \quad x_0 = H_{\mathsf{id}}(\langle hvk \rangle), \qquad t_{P \to Q} = \mathsf{Tag}(usk_P, x_Q), \quad x_Q = H_{\mathsf{req}}(\langle pp, hvk, id_Q, j_Q \rangle)
//! ```
//!
//! This module holds the trait definitions and the stand-alone proof of `R_Tag`
//! ([`prove_tag`], [`verify_tag`]), which is the identifier proof `π_id` of the protocol. The
//! instantiations of the paper are
//!
//! * [`DDH`] = `Tag_DDH` (§6.1.1): key space `Z_p \ {0}`, `Tag(K, x) = htag(x)^K`, range
//!   `T = G_1 \ {1}`, clause `t = htag(x)^K` (base `htag(x)`, target `t`);
//! * [`DY`] = `Tag_DY` (§6.1.2): key space `Z_p`, `Tag(K, x) = g_1^{1/(K+x)}`, `⊥` iff
//!   `K + x = 0`, range `T = G_1 \ {1}`, clause `t^K = g_1 t^{-x}` (base `t`, target
//!   `g_1 − x·t`), with a generator `g_1` of the deployment;
//! * `LWR` = the short-key `Tag_LWR` (§6.1.3, feature `lattice`), used by the post-quantum
//!   instantiation.

pub mod ddh;
pub mod dy;
#[cfg(feature = "lattice")]
pub mod lwr;

use core::fmt::Debug;

use ark_ec::PrimeGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{CryptoRng, RngCore};
use zeroize::Zeroize;

#[cfg(feature = "lattice")]
pub use self::lwr::LWR;
pub use self::{ddh::DDH, dy::DY};
use crate::{
    error::Error,
    hash::Transcript,
    sigma::{FSProof, GroupRelation, LinearEquation, ScalarVar, Witness, fiat_shamir},
};

/// The scalar field of the group a sigma-friendly tag lives in; its key and input space.
pub type Scalar<T> = <<T as SigmaFriendlyKIPRF>::Group as PrimeGroup>::ScalarField;

/// A key-injective PRF `(TagKeyGen, TagEval)` with key space `K`, domain `X` and range `T`
/// (Def. "Key-injective PRF", §4.1).
///
/// The paper requires (i) *key uniqueness*: `Tag(K, x) ≠ Tag(K', x)` for distinct keys, with
/// probability over a uniform point `x`, (ii) *weak pseudorandomness* on uniform points, and
/// (iii) *proof friendliness*. An instance (`&self`) carries the public parameters of the
/// function (a generator, the hash-to-group oracle).
pub trait KIPRF {
    /// The key space `K`. A key is secret: hold it in a container that wipes it on drop.
    type Key: Zeroize;
    /// The domain `X` of evaluation points.
    type Input;
    /// The range `Y`.
    type Output: PartialEq;

    /// `TagKeyGen(1^λ) → K`.
    fn keygen<R: RngCore + CryptoRng + ?Sized>(&self, rng: &mut R) -> Self::Key;

    /// `TagEval(K, x) → t / ⊥`, written `Tag(K, x)`. Deterministic. `None` is `⊥`: the point
    /// lies outside the key-dependent domain of a partial-domain instantiation (`Tag_DY`).
    ///
    /// Implementation note: a key outside the key space (e.g. `0` for `Tag_DDH`, whose key
    /// space is `Z_p \ {0}`) must also evaluate to `None`; its "tag" would be the identity.
    fn eval(&self, key: &Self::Key, input: &Self::Input) -> Option<Self::Output>;
}

/// A KI-PRF whose relation
/// `R_Tag = { ((t, x), K) : t ∈ T ∧ t = TagEval(K, x) }`
/// has a witness-preserving AND-composable sigma protocol ("proof friendliness" of Def.
/// "Key-injective PRF", §4.1).
///
/// Here this means: keys and points are scalars of a prime-order group, tags are group
/// elements, and `t = Tag(K, x)` is equivalent (given `t ∈ T`) to linear equations in the
/// single witness `K`, which the proof layer composes with other clauses sharing `K = usk`.
pub trait SigmaFriendlyKIPRF:
    KIPRF<Key = Scalar<Self>, Input = Scalar<Self>, Output = <Self as SigmaFriendlyKIPRF>::Group>
{
    /// The prime-order group of the tags; `G_1` in the pairing-based instantiations.
    type Group: PrimeGroup;

    /// The public membership test `t ∈ T` of the tag range: accepts every honestly generated,
    /// defined tag and rejects every encoding that would make `R_Tag` vacuous (`t = 1` for both
    /// group instantiations of the paper). The verifier evaluates it as a public pre-check; the
    /// sigma protocol does not enforce it.
    fn valid_tag(&self, tag: &Self::Group, input: &Scalar<Self>) -> bool;

    /// The linear clauses of `R_Tag` for the public statement `(tag, input)`, with the key as
    /// the witness variable `key` (shared with every other clause that uses the same variable).
    ///
    /// For every `(tag, input)` with `valid_tag(tag, input)`, a scalar `K` satisfies the
    /// returned equations if and only if `tag = Tag(K, input)`.
    fn tag_equations(
        &self,
        key: ScalarVar,
        tag: &Self::Group,
        input: &Scalar<Self>,
    ) -> Vec<LinearEquation<Self::Group>>;
}

/// What the protocol needs from a tag over the group `G` (`G = E::G1` for the pairing
/// instantiations of §6) beyond [`SigmaFriendlyKIPRF`]: public parameters `pp_Tag` that are
/// derived from the deployment label (transparent setup) and canonically encodable, because they
/// are part of `pp` and enter its digest.
pub trait ProtocolTag<G: PrimeGroup>:
    SigmaFriendlyKIPRF<Group = G>
    + Clone
    + Debug
    + PartialEq
    + Eq
    + CanonicalSerialize
    + CanonicalDeserialize
    + Send
    + Sync
{
    /// The name of the tag; it enters the digest of `pp`, so two tags under one deployment label
    /// never share a digest.
    const NAME: &'static str;

    /// `pp_Tag` for the deployment `label`. Deterministic: the protocol accepts received
    /// parameters only if they equal the derived ones.
    ///
    /// # Errors
    /// [`Error::HashToCurve`] if the hash-to-group oracle cannot be instantiated.
    fn setup(label: &[u8]) -> Result<Self, Error>;

    /// Whether THIS instance is a usable `pp_Tag`. `false` for a DEGENERATE instance: one under
    /// which `TagEval` is `⊥` at every point (and `t ∈ T` fails for every tag), such as a
    /// `Tag_DY` instance whose generator is the identity. Deterministic; costs no group
    /// operation; never panics.
    ///
    /// Implementation note, not an algorithm of the paper, whose `pp_Tag` is always an output of
    /// `Setup`. Every instance built by [`Self::setup`] is well formed. The question arises for
    /// an instance that was assembled or decoded in another way, in particular WITHOUT
    /// validation (`deserialize_*_unchecked`), and it is a question of LIVENESS: verifiers are
    /// protected in any case, because [`SigmaFriendlyKIPRF::valid_tag`] of a degenerate instance
    /// rejects everything, but `Register` samples keys until `Tag(usk, x_0) ≠ ⊥`, and under a
    /// degenerate instance such a loop never terminates. Generic code cannot see the inherent
    /// checks of an instantiation; this hook is how it asks, and the setup of the protocol
    /// ([`crate::pcreds::Protocol`]) refuses a degenerate instance with
    /// [`Error::DegenerateInput`] before any restart loop can run.
    ///
    /// Contract for implementors: if this returns `true`, then for every point `x` at most ONE
    /// key `K` that [`KIPRF::keygen`] can output has `eval(K, x) = None` (none for `Tag_DDH`,
    /// the key `K = −x` for `Tag_DY`), so one iteration of the `Register` loop restarts with
    /// probability at most `1/p` for a uniform key.
    fn is_well_formed(&self) -> bool;
}

// ---------------------------------------------------------------------------------------------
// The stand-alone sigma protocol for R_Tag
// ---------------------------------------------------------------------------------------------

/// Oracle suffix of the Fiat-Shamir context of a stand-alone tag proof.
const TAG_PROOF_SUFFIX: &[u8] = b"/TAG-PROOF";

/// The statement `((t, x), ·) ∈ R_Tag` as a relation in the single witness `K`: a fresh
/// [`GroupRelation`] holding [`SigmaFriendlyKIPRF::tag_equations`], and the variable of `K`
/// (index 0).
///
/// `t ∈ T` is NOT part of the linear relation; [`verify_tag`] evaluates it as the public
/// pre-check.
///
/// # Errors
/// Propagates [`Error::UnallocatedVariable`] from a tag that returns malformed equations (none
/// of this crate does).
pub fn tag_relation<T: SigmaFriendlyKIPRF>(
    prf: &T,
    tag: &T::Group,
    input: &Scalar<T>,
) -> Result<(GroupRelation<T::Group>, ScalarVar), Error> {
    let mut rel = GroupRelation::new();
    let key = rel.alloc_scalar();
    for equation in prf.tag_equations(key, tag, input) {
        rel.add_equation(equation)?;
    }
    Ok((rel, key))
}

/// `ctx' = (pp_Tag, t, x, ctx)`. Implementation notes:
///
/// * `H_1` has no deployment input of its own (see [`crate::hash`]), so a proof is tied to a
///   deployment only through its context. The parameters `pp_Tag` (for `Tag_DDH` the deployment
///   label of `htag`, for `Tag_DY` the generator of the deployment) are therefore part of it.
/// * Fiat-Shamir already absorbs every base and target of the statement; naming `(t, x)` as
///   well makes the binding to the evaluation point independent of how an instantiation encodes
///   `x` into its equations.
fn tag_proof_context<T: SigmaFriendlyKIPRF + CanonicalSerialize>(
    prf: &T,
    tag: &T::Group,
    input: &Scalar<T>,
    ctx: &[u8],
) -> Result<Vec<u8>, Error> {
    let mut transcript = Transcript::new(TAG_PROOF_SUFFIX);
    transcript.append_serializable(b"pp-tag", prf)?;
    transcript.append_serializable(b"tag", tag)?;
    transcript.append_serializable(b"input", input)?;
    transcript.append_bytes(b"ctx", ctx);
    Ok(transcript.digest().to_vec())
}

/// `π ← zkPoK_ctx{ ((t, x), K) ∈ R_Tag }`: a stand-alone Fiat-Shamir proof of knowledge of the
/// key behind a tag ("proof friendliness" of Def. "Key-injective PRF").
///
/// The protocol composes the same equations with the clauses of a credential base under one
/// shared variable `usk` for its attestation and issuance proofs; its identifier proof `π_id`
/// is a proof of this relation alone. The proof is bound to the parameters `pp_Tag` (hence the
/// serialization bound), to `(t, x)` and to `ctx`.
///
/// # Errors
/// [`Error::InvalidTag`] if `t ∉ T`; [`Error::WitnessDoesNotSatisfyRelation`] if
/// `t ≠ Tag(K, x)`.
pub fn prove_tag<T, R>(
    prf: &T,
    key: &Scalar<T>,
    tag: &T::Group,
    input: &Scalar<T>,
    ctx: &[u8],
    rng: &mut R,
) -> Result<FSProof<Scalar<T>>, Error>
where
    T: SigmaFriendlyKIPRF + CanonicalSerialize,
    R: RngCore + CryptoRng + ?Sized,
{
    if !prf.valid_tag(tag, input) {
        return Err(Error::InvalidTag);
    }
    let (rel, _) = tag_relation(prf, tag, input)?;
    let witness = Witness::from(vec![*key]);
    fiat_shamir::prove(
        &rel,
        &witness,
        &tag_proof_context(prf, tag, input, ctx)?,
        rng,
    )
}

/// Verifies a proof of [`prove_tag`] for the parameters `prf`, the public statement `(t, x)` and
/// the context `ctx`: the public pre-check `t ∈ T`, then Fiat-Shamir verification of the tag
/// equations. Never panics.
#[must_use]
pub fn verify_tag<T: SigmaFriendlyKIPRF + CanonicalSerialize>(
    prf: &T,
    tag: &T::Group,
    input: &Scalar<T>,
    ctx: &[u8],
    proof: &FSProof<Scalar<T>>,
) -> bool {
    if !prf.valid_tag(tag, input) {
        return false;
    }
    let (Ok((rel, _)), Ok(full_ctx)) = (
        tag_relation(prf, tag, input),
        tag_proof_context(prf, tag, input, ctx),
    ) else {
        return false;
    };
    fiat_shamir::verify(&rel, &full_ctx, proof)
}
