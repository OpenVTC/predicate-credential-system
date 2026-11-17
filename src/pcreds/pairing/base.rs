//! The pairing-based credential bases of the paper (§6.2): `Σ-PS` and `Σ-BBS`, each certifying
//! the user key `usk` alone, with the relations `R_PrepareIssue` and `R_Possess` of Def.
//! "Credential base" (§4.2) as sigma-protocol clauses.
//!
//! | paper | here |
//! |---|---|
//! | `PGen(1^λ)` | [`Base::setup`]; [`Base::check_params`] for received parameters |
//! | `KeyGen(pp)` | [`Base::keygen`] |
//! | the admissible key domain `V_pp` | [`Base::admissible_key`] |
//! | `PrepareIssue(vk, usk; τ)` | [`Base::prepare_issue`] |
//! | `BlindIssue(sk, Ĉ)` | [`Base::blind_issue`] |
//! | `Unblind(vk, usk, σ̂, τ)` | [`Base::unblind`] |
//! | `Verify(vk, usk, σ)` | [`Base::verify`] |
//! | `ReRand(vk, usk, σ; ω)` | [`Base::rerand`] |
//! | `Π_PrepareIssue`, `Π_Possess` | [`Base::issuance_clauses`], [`Base::possession_clauses`] and their public checks |
//!
//! In every relation the shared key `usk` is variable 0, allocated by the caller; the clauses of
//! a base allocate their further variables after it ([`Base::ISSUANCE_VARIABLES`],
//! [`Base::POSSESSION_VARIABLES`] many), and the witness functions push the values of exactly
//! those variables, in the same order.
//!
//! # Implementation notes
//!
//! * **Secrets.** Signing keys, show witnesses and the inverse `1/(x+e)` of `Σ-BBS` issuance are
//!   wiped; signing keys and show witnesses print as `<redacted>`, and so does the certified
//!   randomizer `ρ` of a `Σ-BBS` credential. Witnesses are pushed into the wiping
//!   [`Witness`].
//! * **Received values.** The public checks re-validate every group element they receive
//!   (curve and prime-order subgroup, `ark_serialize::Valid::check`): pairing equations do not
//!   see a component of small order in a `G_1` argument, so "decoded with validation" is not
//!   assumed anywhere.

use core::fmt::Debug;

use ark_ec::{PrimeGroup, pairing::Pairing};
use ark_ff::{Field, One, UniformRand, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use ark_std::rand::{CryptoRng, RngCore};
use zeroize::{Zeroize, ZeroizeOnDrop};

use crate::{
    error::Error,
    hash::HashToGroup,
    sample::nonzero_scalar,
    sigma::{GtEquation, LinearEquation, PairingRelation, ScalarVar, Witness, pairing_product},
};

/// Whether every group element of `value` lies on its curve and in the prime-order subgroup.
pub(crate) fn is_valid<V: Valid + ?Sized>(value: &V) -> bool {
    value.check().is_ok()
}

/// Whether the pairing product `∏ e(P_i, Q_i)` is the identity of `G_T`: one multi-pairing for
/// a pairing equation moved to one side. Never panics; an undefined product counts as "not the
/// identity".
#[must_use]
pub fn pairing_product_is_identity<E: Pairing>(pairs: &[(E::G1, E::G2)]) -> bool {
    pairing_product::<E>(pairs).is_ok_and(|product| product.is_zero())
}

/// A sigma-friendly credential base in the sense of Def. "Credential base" (§4.2), over the
/// pairing `E`, certifying a key `usk ∈ Z_p`.
pub trait Base<E: Pairing>: Sized + Clone + Debug + PartialEq + Eq + Send + Sync + 'static {
    /// Public parameters `pp_Σ`.
    type Params: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;
    /// The issuing key `sk`. Secret: wiped on drop, redacted in `Debug`.
    type SigningKey: Zeroize + ZeroizeOnDrop + Debug + CanonicalSerialize + CanonicalDeserialize;
    /// The verification key `vk`.
    type VerificationKey: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;
    /// The public issuance request `Ĉ`.
    type Request: Clone + Debug + PartialEq + Eq + CanonicalSerialize + CanonicalDeserialize;
    /// The pre-credential `σ̂`.
    type PreCredential: Clone + Debug + PartialEq + Eq + CanonicalSerialize + CanonicalDeserialize;
    /// The credential `σ`. Private to its holder.
    type Credential: Clone
        + Debug
        + PartialEq
        + Eq
        + Zeroize
        + CanonicalSerialize
        + CanonicalDeserialize;
    /// The public credential encoding `σ*` of a show.
    type Show: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;
    /// The witness part of the show randomness `ω`. Secret.
    type ShowWitness: Zeroize + ZeroizeOnDrop;
    /// The name of the base; it enters the digest of `pp`.
    const NAME: &'static str;
    /// Whether [`Self::unblind`] already checks `Verify` (as `Σ-BBS` does in the paper), so that
    /// the protocol need not check it again.
    const UNBLIND_VERIFIES: bool;
    /// The number of variables [`Self::issuance_clauses`] allocates after `usk`.
    const ISSUANCE_VARIABLES: usize;
    /// The number of variables [`Self::possession_clauses`] allocates after `usk`.
    const POSSESSION_VARIABLES: usize;

    /// `PGen`, deterministic in the deployment label.
    ///
    /// # Errors
    /// [`Error::HashToCurve`] if a hash-to-group oracle cannot be instantiated;
    /// [`Error::DegenerateInput`] if a derived generator is the identity.
    fn setup(label: &[u8]) -> Result<Self::Params, Error>;

    /// The checks of `pp_Σ` received from outside: every group element is valid and no
    /// generator is the identity. Whether the parameters are the DERIVED ones is the protocol's
    /// check ([`crate::pcreds::Protocol::from_public_parameters`]).
    ///
    /// # Errors
    /// [`Error::InvalidGroupElement`] or [`Error::DegenerateInput`].
    fn check_params(pp: &Self::Params) -> Result<(), Error>;

    /// `KeyGen(pp)`.
    fn keygen<R: RngCore + CryptoRng + ?Sized>(
        pp: &Self::Params,
        rng: &mut R,
    ) -> (Self::VerificationKey, Self::SigningKey);

    /// Membership in the admissible key domain `V_pp`, including the validity of every group
    /// element of `vk`.
    fn admissible_key(pp: &Self::Params, vk: &Self::VerificationKey) -> bool;

    /// Whether `sk` is the signing key behind `vk` (for a helper key read back from storage).
    fn key_pair_matches(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        sk: &Self::SigningKey,
    ) -> bool;

    /// `PrepareIssue(vk, usk; τ)`, with the issuance randomness `τ ∈ Z_p`; `None` for `⊥`.
    fn prepare_issue(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &E::ScalarField,
        tau: &E::ScalarField,
    ) -> Option<Self::Request>;

    /// `BlindIssue(sk, Ĉ)`; `None` for `⊥`.
    fn blind_issue<R: RngCore + CryptoRng + ?Sized>(
        pp: &Self::Params,
        sk: &Self::SigningKey,
        request: &Self::Request,
        rng: &mut R,
    ) -> Option<Self::PreCredential>;

    /// `Unblind(vk, usk, σ̂, τ)`; `None` for `⊥`.
    fn unblind(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &E::ScalarField,
        pre: &Self::PreCredential,
        tau: &E::ScalarField,
    ) -> Option<Self::Credential>;

    /// `Verify(vk, usk, σ)`, including the validity of every group element of `σ`.
    fn verify(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &E::ScalarField,
        cred: &Self::Credential,
    ) -> bool;

    /// `ReRand(vk, usk, σ; ω)` on fresh randomness: the show and the witness part of `ω`.
    fn rerand<R: RngCore + CryptoRng + ?Sized>(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &E::ScalarField,
        cred: &Self::Credential,
        rng: &mut R,
    ) -> (Self::Show, Self::ShowWitness);

    /// The public checks of `Π_PrepareIssue` on `(vk, Ĉ)`, for a key that has passed
    /// [`Self::admissible_key`] (the caller checks the key once), including the validity of
    /// every group element of `Ĉ`.
    fn issuance_public_check(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        request: &Self::Request,
    ) -> bool;

    /// The clauses of `Π_PrepareIssue` for `(vk, Ĉ)`, on the shared variable `usk`; they
    /// allocate [`Self::ISSUANCE_VARIABLES`] further variables.
    ///
    /// # Errors
    /// Propagates [`Error::UnallocatedVariable`] from the relation.
    fn issuance_clauses(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        request: &Self::Request,
        relation: &mut PairingRelation<E>,
        usk: ScalarVar,
    ) -> Result<(), Error>;

    /// Pushes the values of the variables that [`Self::issuance_clauses`] allocated, in order.
    fn issuance_witness(tau: &E::ScalarField, witness: &mut Witness<E::ScalarField>);

    /// The public checks of `Π_Possess` on `(vk, σ*)`, for a key that has passed
    /// [`Self::admissible_key`] (the caller checks the key once), including the validity of
    /// every group element of `σ*`.
    fn possession_public_check(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        show: &Self::Show,
    ) -> bool;

    /// The clauses of `Π_Possess` for `(vk, σ*)`, on the shared variable `usk`; they allocate
    /// [`Self::POSSESSION_VARIABLES`] further variables.
    ///
    /// # Errors
    /// Propagates [`Error::UnallocatedVariable`] from the relation.
    fn possession_clauses(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        show: &Self::Show,
        relation: &mut PairingRelation<E>,
        usk: ScalarVar,
    ) -> Result<(), Error>;

    /// Pushes the values of the variables that [`Self::possession_clauses`] allocated, in
    /// order.
    fn possession_witness(
        cred: &Self::Credential,
        omega: &Self::ShowWitness,
        witness: &mut Witness<E::ScalarField>,
    );
}

// ---------------------------------------------------------------------------------------------
// Σ-PS
// ---------------------------------------------------------------------------------------------

/// `Σ-PS` (§6.2.1): Pointcheval–Sanders signatures on `usk`, blind issuance on the Pedersen
/// request `C = g_1^ρ Y^usk`, and shows `(σ_1^r, (σ_2 σ_1^t)^r)` that are uniform pairs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PS;

/// `vk = (X̃, Ỹ, Y) = (g̃^x, g̃^y, g_1^y)`.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PSVerificationKey<E: Pairing> {
    /// `X̃ = g̃^x`.
    pub x2: E::G2,
    /// `Ỹ = g̃^y`.
    pub y2: E::G2,
    /// `Y = g_1^y`.
    pub y1: E::G1,
}

/// `sk = (x, y)`; only `x` is needed to issue, so only `x` is kept. Secret: wiped on drop,
/// redacted in `Debug`.
#[derive(Zeroize, ZeroizeOnDrop, CanonicalSerialize, CanonicalDeserialize)]
pub struct PSSigningKey<E: Pairing> {
    x: E::ScalarField,
}

impl<E: Pairing> Debug for PSSigningKey<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("PSSigningKey(<redacted>)")
    }
}

/// A pair `(σ_1, σ_2)` of `G_1` elements: credential, pre-credential, or show.
#[derive(Clone, Debug, PartialEq, Eq, Zeroize, CanonicalSerialize, CanonicalDeserialize)]
pub struct PSPair<E: Pairing> {
    /// `σ_1`.
    pub s1: E::G1,
    /// `σ_2`.
    pub s2: E::G1,
}

/// The request `C = g_1^ρ Y^usk`.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct G1Request<E: Pairing>(pub E::G1);

/// The witness part `t` of the show randomness of `Σ-PS`. Secret: wiped on drop, redacted in
/// `Debug`.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct PSShowWitness<F: Zeroize>(F);

impl<F: Zeroize> Debug for PSShowWitness<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("PSShowWitness(<redacted>)")
    }
}

impl<E: Pairing> Base<E> for PS {
    type Params = ();
    type SigningKey = PSSigningKey<E>;
    type VerificationKey = PSVerificationKey<E>;
    type Request = G1Request<E>;
    type PreCredential = PSPair<E>;
    type Credential = PSPair<E>;
    type Show = PSPair<E>;
    type ShowWitness = PSShowWitness<E::ScalarField>;
    const NAME: &'static str = "PS";
    const UNBLIND_VERIFIES: bool = false;
    const ISSUANCE_VARIABLES: usize = 1;
    const POSSESSION_VARIABLES: usize = 1;

    fn setup(_label: &[u8]) -> Result<(), Error> {
        Ok(())
    }

    fn check_params((): &()) -> Result<(), Error> {
        Ok(())
    }

    fn keygen<R: RngCore + CryptoRng + ?Sized>(
        (): &(),
        rng: &mut R,
    ) -> (PSVerificationKey<E>, PSSigningKey<E>) {
        let x = E::ScalarField::rand(rng);
        let mut y: E::ScalarField = nonzero_scalar(rng);
        let vk = PSVerificationKey {
            x2: E::G2::generator() * x,
            y2: E::G2::generator() * y,
            y1: E::G1::generator() * y,
        };
        y.zeroize();
        (vk, PSSigningKey { x })
    }

    fn admissible_key((): &(), vk: &PSVerificationKey<E>) -> bool {
        is_valid(vk)
            && !vk.y2.is_zero()
            && !vk.y1.is_zero()
            && pairing_product_is_identity::<E>(&[
                (vk.y1, E::G2::generator()),
                (-E::G1::generator(), vk.y2),
            ])
    }

    fn key_pair_matches((): &(), vk: &PSVerificationKey<E>, sk: &PSSigningKey<E>) -> bool {
        vk.x2 == E::G2::generator() * sk.x
    }

    fn prepare_issue(
        (): &(),
        vk: &PSVerificationKey<E>,
        usk: &E::ScalarField,
        tau: &E::ScalarField,
    ) -> Option<G1Request<E>> {
        Some(G1Request(E::G1::generator() * tau + vk.y1 * usk))
    }

    fn blind_issue<R: RngCore + CryptoRng + ?Sized>(
        (): &(),
        sk: &PSSigningKey<E>,
        request: &G1Request<E>,
        rng: &mut R,
    ) -> Option<PSPair<E>> {
        if !is_valid(&request.0) {
            return None;
        }
        let mut u: E::ScalarField = nonzero_scalar(rng);
        let pre = PSPair {
            s1: E::G1::generator() * u,
            s2: (E::G1::generator() * sk.x + request.0) * u,
        };
        u.zeroize();
        Some(pre)
    }

    fn unblind(
        (): &(),
        _vk: &PSVerificationKey<E>,
        _usk: &E::ScalarField,
        pre: &PSPair<E>,
        tau: &E::ScalarField,
    ) -> Option<PSPair<E>> {
        // "Pre-credentials ... are pairs in G_1^2 with nonidentity first component"; `⊥` "on a
        // malformed input".
        if !is_valid(pre) || pre.s1.is_zero() {
            return None;
        }
        Some(PSPair {
            s1: pre.s1,
            s2: pre.s2 - pre.s1 * tau,
        })
    }

    fn verify((): &(), vk: &PSVerificationKey<E>, usk: &E::ScalarField, cred: &PSPair<E>) -> bool {
        is_valid(cred)
            && !cred.s1.is_zero()
            && pairing_product_is_identity::<E>(&[
                (cred.s1, vk.x2 + vk.y2 * usk),
                (-cred.s2, E::G2::generator()),
            ])
    }

    fn rerand<R: RngCore + CryptoRng + ?Sized>(
        (): &(),
        _vk: &PSVerificationKey<E>,
        _usk: &E::ScalarField,
        cred: &PSPair<E>,
        rng: &mut R,
    ) -> (PSPair<E>, PSShowWitness<E::ScalarField>) {
        let mut r: E::ScalarField = nonzero_scalar(rng);
        let t = PSShowWitness(E::ScalarField::rand(rng));
        let show = PSPair {
            s1: cred.s1 * r,
            s2: (cred.s2 + cred.s1 * t.0) * r,
        };
        r.zeroize();
        (show, t)
    }

    fn issuance_public_check((): &(), _vk: &PSVerificationKey<E>, request: &G1Request<E>) -> bool {
        is_valid(&request.0)
    }

    fn issuance_clauses(
        (): &(),
        vk: &PSVerificationKey<E>,
        request: &G1Request<E>,
        relation: &mut PairingRelation<E>,
        usk: ScalarVar,
    ) -> Result<(), Error> {
        let rho = relation.alloc_scalar();
        // C = g_1^ρ Y^usk
        relation.add_g1(LinearEquation::new(
            vec![(usk, vk.y1), (rho, E::G1::generator())],
            request.0,
        ))
    }

    fn issuance_witness(tau: &E::ScalarField, witness: &mut Witness<E::ScalarField>) {
        witness.push(*tau);
    }

    fn possession_public_check((): &(), _vk: &PSVerificationKey<E>, show: &PSPair<E>) -> bool {
        is_valid(show) && !show.s1.is_zero()
    }

    fn possession_clauses(
        (): &(),
        vk: &PSVerificationKey<E>,
        show: &PSPair<E>,
        relation: &mut PairingRelation<E>,
        usk: ScalarVar,
    ) -> Result<(), Error> {
        let t = relation.alloc_scalar();
        let g2 = E::G2::generator();
        let one = E::ScalarField::one();
        // e(σ'_1, Ỹ)^usk · e(σ'_1, g̃)^t = e(σ'_2, g̃) · e(σ'_1, X̃)^{-1}: the inverse is the
        // coefficient −1 on the pair (σ'_1, X̃), so that σ'_1 itself is in the instance
        relation.add_gt(GtEquation {
            image: vec![(show.s2, g2, one), (show.s1, vk.x2, -one)],
            terms: vec![(usk, show.s1, vk.y2, one), (t, show.s1, g2, one)],
        })
    }

    fn possession_witness(
        _cred: &PSPair<E>,
        omega: &PSShowWitness<E::ScalarField>,
        witness: &mut Witness<E::ScalarField>,
    ) {
        witness.push(omega.0);
    }
}

// ---------------------------------------------------------------------------------------------
// Σ-BBS
// ---------------------------------------------------------------------------------------------

/// Oracle suffix of the generators `h_0, h_u, h_r` of `Σ-BBS`.
pub const BBS_GENERATORS_SUFFIX: &[u8] = b"/PCREDS-BBS-GENERATORS";

/// `Σ-BBS` (§6.2.2): BBS signatures on `B(usk, ρ) = h_0 h_u^usk h_r^ρ`, which the helper signs
/// directly; the credential keeps `ρ`, and a show is the two-randomizer blinded credential
/// `(Ā, B̄, D)` with the three-clause possession proof of the paper.
pub struct BBS<H>(core::marker::PhantomData<fn() -> H>);

// Written by hand: a derive would bound the marker type `H`.
impl<H> Clone for BBS<H> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<H> Copy for BBS<H> {}

impl<H> Debug for BBS<H> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("BBS")
    }
}

impl<H> Default for BBS<H> {
    fn default() -> Self {
        Self(core::marker::PhantomData)
    }
}

impl<H> PartialEq for BBS<H> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<H> Eq for BBS<H> {}

/// The generators `h_0, h_u, h_r` of `pp`, derived by hashing fixed labels.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct BBSParams<E: Pairing> {
    /// `h_0`.
    pub h0: E::G1,
    /// `h_u`.
    pub hu: E::G1,
    /// `h_r`.
    pub hr: E::G1,
}

impl<E: Pairing> BBSParams<E> {
    /// `B(usk, ρ) = h_0 h_u^usk h_r^ρ`.
    #[must_use]
    pub fn b(&self, usk: &E::ScalarField, rho: &E::ScalarField) -> E::G1 {
        self.h0 + self.hu * usk + self.hr * rho
    }
}

/// `vk = X̃ = g̃^x`.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct BBSVerificationKey<E: Pairing>(pub E::G2);

/// `sk = x`. Secret: wiped on drop, redacted in `Debug`.
#[derive(Zeroize, ZeroizeOnDrop, CanonicalSerialize, CanonicalDeserialize)]
pub struct BBSSigningKey<E: Pairing>(pub(super) E::ScalarField);

impl<E: Pairing> Debug for BBSSigningKey<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("BBSSigningKey(<redacted>)")
    }
}

/// The pre-credential `(A, e)`.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct BBSPreCredential<E: Pairing> {
    /// `A = C^{1/(x+e)}`.
    pub a: E::G1,
    /// `e`.
    pub e: E::ScalarField,
}

/// The credential `(A, e, ρ)`. Private to its holder; `ρ`, which the helper never sees, prints
/// as `<redacted>`.
#[derive(Clone, PartialEq, Eq, Zeroize, CanonicalSerialize, CanonicalDeserialize)]
pub struct BBSCredential<E: Pairing> {
    /// `A`.
    pub a: E::G1,
    /// `e`.
    pub e: E::ScalarField,
    /// The issuance randomness `ρ`.
    pub rho: E::ScalarField,
}

impl<E: Pairing> Debug for BBSCredential<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BBSCredential")
            .field("a", &self.a)
            .field("e", &self.e)
            .field("rho", &"<redacted>")
            .finish()
    }
}

/// The show `(Ā, B̄, D)`.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct BBSShow<E: Pairing> {
    /// `Ā = A^{r_1 r_2}`.
    pub a_bar: E::G1,
    /// `B̄ = D^{r_1} Ā^{-e}`.
    pub b_bar: E::G1,
    /// `D = B(usk, ρ)^{r_2}`.
    pub d: E::G1,
}

/// The witness part `(r_1, r_2)` of the show randomness. Secret: wiped on drop, redacted in
/// `Debug`.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct BBSShowWitness<F: Zeroize> {
    r1: F,
    r2: F,
}

impl<F: Zeroize> Debug for BBSShowWitness<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("BBSShowWitness(<redacted>)")
    }
}

impl<E: Pairing, H: HashToGroup<E::G1> + 'static> Base<E> for BBS<H> {
    type Params = BBSParams<E>;
    type SigningKey = BBSSigningKey<E>;
    type VerificationKey = BBSVerificationKey<E>;
    type Request = G1Request<E>;
    type PreCredential = BBSPreCredential<E>;
    type Credential = BBSCredential<E>;
    type Show = BBSShow<E>;
    type ShowWitness = BBSShowWitness<E::ScalarField>;
    const NAME: &'static str = "BBS";
    const UNBLIND_VERIFIES: bool = true;
    const ISSUANCE_VARIABLES: usize = 1;
    const POSSESSION_VARIABLES: usize = 6;

    fn setup(label: &[u8]) -> Result<BBSParams<E>, Error> {
        let hasher = H::new(label)?;
        let mut generators = hasher.generators(BBS_GENERATORS_SUFFIX, 3).into_iter();
        let mut next = || {
            generators
                .next()
                .ok_or(Error::DegenerateInput("BBS generators"))
        };
        let params = BBSParams {
            h0: next()?,
            hu: next()?,
            hr: next()?,
        };
        Self::check_params(&params)?;
        Ok(params)
    }

    fn check_params(pp: &BBSParams<E>) -> Result<(), Error> {
        if !is_valid(pp) {
            return Err(Error::InvalidGroupElement("pp_Σ"));
        }
        if pp.h0.is_zero() || pp.hu.is_zero() || pp.hr.is_zero() {
            return Err(Error::DegenerateInput("BBS generators"));
        }
        Ok(())
    }

    fn keygen<R: RngCore + CryptoRng + ?Sized>(
        _pp: &BBSParams<E>,
        rng: &mut R,
    ) -> (BBSVerificationKey<E>, BBSSigningKey<E>) {
        let x = E::ScalarField::rand(rng);
        (BBSVerificationKey(E::G2::generator() * x), BBSSigningKey(x))
    }

    fn admissible_key(_pp: &BBSParams<E>, vk: &BBSVerificationKey<E>) -> bool {
        is_valid(vk)
    }

    fn key_pair_matches(
        _pp: &BBSParams<E>,
        vk: &BBSVerificationKey<E>,
        sk: &BBSSigningKey<E>,
    ) -> bool {
        vk.0 == E::G2::generator() * sk.0
    }

    fn prepare_issue(
        pp: &BBSParams<E>,
        _vk: &BBSVerificationKey<E>,
        usk: &E::ScalarField,
        tau: &E::ScalarField,
    ) -> Option<G1Request<E>> {
        let c = pp.b(usk, tau);
        (!c.is_zero()).then_some(G1Request(c))
    }

    fn blind_issue<R: RngCore + CryptoRng + ?Sized>(
        _pp: &BBSParams<E>,
        sk: &BBSSigningKey<E>,
        request: &G1Request<E>,
        rng: &mut R,
    ) -> Option<BBSPreCredential<E>> {
        if !is_valid(&request.0) || request.0.is_zero() {
            return None;
        }
        loop {
            let e = E::ScalarField::rand(rng);
            if let Some(mut inverse) = (sk.0 + e).inverse() {
                let a = request.0 * inverse;
                // With the public e, 1/(x+e) gives away x.
                inverse.zeroize();
                return Some(BBSPreCredential { a, e });
            }
        }
    }

    fn unblind(
        pp: &BBSParams<E>,
        vk: &BBSVerificationKey<E>,
        usk: &E::ScalarField,
        pre: &BBSPreCredential<E>,
        tau: &E::ScalarField,
    ) -> Option<BBSCredential<E>> {
        let cred = BBSCredential {
            a: pre.a,
            e: pre.e,
            rho: *tau,
        };
        Self::verify(pp, vk, usk, &cred).then_some(cred)
    }

    fn verify(
        pp: &BBSParams<E>,
        vk: &BBSVerificationKey<E>,
        usk: &E::ScalarField,
        cred: &BBSCredential<E>,
    ) -> bool {
        let b = pp.b(usk, &cred.rho);
        is_valid(cred)
            && !cred.a.is_zero()
            && !b.is_zero()
            && pairing_product_is_identity::<E>(&[
                (cred.a, vk.0 + E::G2::generator() * cred.e),
                (-b, E::G2::generator()),
            ])
    }

    fn rerand<R: RngCore + CryptoRng + ?Sized>(
        pp: &BBSParams<E>,
        _vk: &BBSVerificationKey<E>,
        usk: &E::ScalarField,
        cred: &BBSCredential<E>,
        rng: &mut R,
    ) -> (BBSShow<E>, BBSShowWitness<E::ScalarField>) {
        let omega = BBSShowWitness {
            r1: nonzero_scalar(rng),
            r2: nonzero_scalar(rng),
        };
        let d = pp.b(usk, &cred.rho) * omega.r2;
        let a_bar = cred.a * (omega.r1 * omega.r2);
        let b_bar = d * omega.r1 - a_bar * cred.e;
        (BBSShow { a_bar, b_bar, d }, omega)
    }

    fn issuance_public_check(
        _pp: &BBSParams<E>,
        _vk: &BBSVerificationKey<E>,
        request: &G1Request<E>,
    ) -> bool {
        is_valid(&request.0) && !request.0.is_zero()
    }

    fn issuance_clauses(
        pp: &BBSParams<E>,
        _vk: &BBSVerificationKey<E>,
        request: &G1Request<E>,
        relation: &mut PairingRelation<E>,
        usk: ScalarVar,
    ) -> Result<(), Error> {
        let rho = relation.alloc_scalar();
        let one = E::ScalarField::one();
        // C h_0^{-1} = h_u^usk h_r^ρ: the image terms (C, 1) and (h_0, −1), so that C and h_0
        // are each in the instance
        relation.add_g1(LinearEquation {
            image: vec![(request.0, one), (pp.h0, -one)],
            terms: vec![(usk, pp.hu, one), (rho, pp.hr, one)],
        })
    }

    fn issuance_witness(tau: &E::ScalarField, witness: &mut Witness<E::ScalarField>) {
        witness.push(*tau);
    }

    fn possession_public_check(
        _pp: &BBSParams<E>,
        vk: &BBSVerificationKey<E>,
        show: &BBSShow<E>,
    ) -> bool {
        is_valid(show)
            && !show.a_bar.is_zero()
            && !show.d.is_zero()
            && pairing_product_is_identity::<E>(&[
                (show.a_bar, vk.0),
                (-show.b_bar, E::G2::generator()),
            ])
    }

    fn possession_clauses(
        pp: &BBSParams<E>,
        _vk: &BBSVerificationKey<E>,
        show: &BBSShow<E>,
        relation: &mut PairingRelation<E>,
        usk: ScalarVar,
    ) -> Result<(), Error> {
        let vars = relation.alloc_scalars(6);
        let (rho, r1, e, r3, u, v) = (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);
        let one = E::ScalarField::one();
        // The negative exponents are coefficients −1 on the elements themselves.
        // B̄ = D^{r_1} Ā^{-e}
        relation.add_g1(LinearEquation {
            image: vec![(show.b_bar, one)],
            terms: vec![(r1, show.d, one), (e, show.a_bar, -one)],
        })?;
        // h_0 = D^{r_3} h_u^{-usk} h_r^{-ρ}
        relation.add_g1(LinearEquation {
            image: vec![(pp.h0, one)],
            terms: vec![(r3, show.d, one), (usk, pp.hu, -one), (rho, pp.hr, -one)],
        })?;
        // D = B̄^u Ā^v
        relation.add_g1(LinearEquation::new(
            vec![(u, show.b_bar), (v, show.a_bar)],
            show.d,
        ))
    }

    fn possession_witness(
        cred: &BBSCredential<E>,
        omega: &BBSShowWitness<E::ScalarField>,
        witness: &mut Witness<E::ScalarField>,
    ) {
        // (ρ, r_1, e, r_3 = 1/r_2, u = 1/r_1, v = e·u); r_1, r_2 are nonzero by `rerand`
        let mut u = omega.r1.inverse().unwrap_or_default();
        witness.push(cred.rho);
        witness.push(omega.r1);
        witness.push(cred.e);
        witness.push(omega.r2.inverse().unwrap_or_default());
        witness.push(u);
        witness.push(cred.e * u);
        u.zeroize();
    }
}
