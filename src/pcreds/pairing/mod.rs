//! The pairing-based instantiations of `Π_PCreds` (§5): the credential bases `Σ-PS` and
//! `Σ-BBS` ([`base`]) with the tags `Tag_DDH` and `Tag_DY` ([`crate::kiprf`]), and generalized
//! Schnorr proofs with the Fiat–Shamir transform ([`crate::sigma`]) as the NIZK.
//!
//! [`PairingBackend<E, B, T>`] is the [`Backend`] for the pairing `E`, the base `B` and the tag
//! `T`; [`PairingProtocol<E, B, T>`] is the protocol over it. The paper's main instantiation is
//! `Σ-PS` with `Tag_DDH`:
//!
//! ```
//! use ark_bls12_381::{Bls12_381, G1Projective};
//! use predicate_credential_system::{
//!     hash::bls12_381::G1Hasher,
//!     kiprf::DDH,
//!     pcreds::pairing::{PS, PairingProtocol},
//! };
//!
//! type Scheme = PairingProtocol<Bls12_381, PS, DDH<G1Projective, G1Hasher>>;
//! let protocol = Scheme::setup(b"example deployment")?;
//! # Ok::<(), predicate_credential_system::Error>(())
//! ```
//!
//! # The relations
//!
//! In every relation the shared key `usk` is variable 0 (§4.2, "Relations": "sharing the
//! hidden key `usk`"):
//!
//! | relation | clauses | variables after `usk` |
//! |---|---|---|
//! | `R_Tag` at `(t, x)` (`π_id`) | the tag clause | none |
//! | `R_att` at `(hvk, σ*, t, x)` | the clauses of `Π_Possess`, the tag clause | [`Base::POSSESSION_VARIABLES`] |
//! | `R_iss` at `(hvk, Ĉ, id)` | the clauses of `Π_PrepareIssue`, the tag clause at `(id, x_0)` with `x_0 = H_id(⟨hvk⟩)` | [`Base::ISSUANCE_VARIABLES`] |
//! | `R_Possess` at `(hvk, σ*)` (`π_prove`) | the clauses of `Π_Possess` | [`Base::POSSESSION_VARIABLES`] |
//!
//! The relation builders ([`PairingBackend::attestation_relation`] and the others) are public:
//! they are functions of public data, and a test harness that runs the interactive protocol,
//! its simulator and its extractor ([`crate::sigma`]) needs exactly the relations the proofs
//! use.
//!
//! The Fiat–Shamir transform and the encoding of the proofs follow the IETF CFRG drafts
//! `draft-irtf-cfrg-sigma-protocols-04` and `draft-irtf-cfrg-fiat-shamir-04` (compact NARG
//! strings, [`crate::sigma::fiat_shamir`]), with the context of each proof in its tag. The
//! relations with `G_1` equations only (`π_id`, the proofs of `Σ-BBS`, `π_iss` of `Σ-PS`) are the
//! draft's, under its ciphersuite `sigma-proofs_Shake128_BLS12381`. The relations of `Σ-PS` with
//! its `G_T` clause (`π_att`, `π_prove`) use the pairing extension of [`crate::sigma::relation`].
//!
//! The proofs are plain Fiat–Shamir proofs; the paper's theorem assumes an online
//! simulation-extractable NIZK, which this crate does not implement (crate docs,
//! "Limitations").

pub mod base;
pub mod ietf;

use core::{fmt, marker::PhantomData};

use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, Valid, Write};
use ark_std::rand::{CryptoRng, RngCore};
use zeroize::Zeroize;

pub use self::base::{
    BBS, BBSCredential, BBSParams, BBSPreCredential, BBSShow, BBSSigningKey, BBSVerificationKey,
    Base, G1Request, PS, PSPair, PSSigningKey, PSVerificationKey, pairing_product_is_identity,
};
use super::{
    Protocol,
    backend::{AttestationStatement, Backend, IssuanceStatement, Leaf, ProofKind},
};
use crate::{
    error::Error,
    hash::Transcript,
    kiprf::ProtocolTag,
    sigma::{FSProof, LinearRelation, PairingRelation, Witness, fiat_shamir},
};

/// The protocol over the pairing-based instantiation `(E, B, T)`.
pub type PairingProtocol<E, B, T> = Protocol<PairingBackend<E, B, T>>;

/// The bound of [`Backend::max_leaf_bytes`] for every leaf of a pairing-based message: far above
/// the largest one (the attestation proof of `Σ-BBS`, a challenge and seven responses, 264 bytes
/// canonically, over BLS12-381), and small enough that the base58btc decoding of a text at the
/// bound costs well under a millisecond.
pub const MAX_LEAF_BYTES: usize = 4096;

/// Re-validation of a value that comes from another party: every group element in it is on its
/// curve and in the prime-order subgroup (`ark_serialize::Valid::check`, which is what validated
/// decoding runs). `what` names the argument in the error.
fn validate<V: Valid + ?Sized>(value: &V, what: &'static str) -> Result<(), Error> {
    value.check().map_err(|_| Error::InvalidGroupElement(what))
}

/// The parameters `(pp_Σ, pp_Tag)` of a deployment of the pairing-based instantiations.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PairingParams<E: Pairing, B: Base<E>, T: ProtocolTag<E::G1>> {
    /// `pp_Σ`, the parameters of the credential base.
    pub base: B::Params,
    /// `pp_Tag`, the tag function.
    pub tag: T,
}

/// The marker of [`PairingBackend`]: `Send`, `Sync` and `'static` whatever its parameters are.
type Marker<E, B, T> = PhantomData<fn() -> (E, B, T)>;

/// The [`Backend`] of the pairing-based instantiations: the pairing `E`, the credential base
/// `B` (`Σ-PS` or `Σ-BBS`) and the tag `T` (`Tag_DDH` or `Tag_DY`) over `G_1`. A marker type.
pub struct PairingBackend<E, B, T>(Marker<E, B, T>);

// Written by hand: derives would bound the type parameters.
impl<E, B, T> Clone for PairingBackend<E, B, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E, B, T> Copy for PairingBackend<E, B, T> {}

impl<E, B, T> Default for PairingBackend<E, B, T> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<E, B, T> PartialEq for PairingBackend<E, B, T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<E, B, T> Eq for PairingBackend<E, B, T> {}

impl<E, B, T> fmt::Debug for PairingBackend<E, B, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PairingBackend")
    }
}

impl<E, B, T> PairingBackend<E, B, T>
where
    E: Pairing,
    B: Base<E>,
    T: ProtocolTag<E::G1> + 'static,
{
    /// The number of responses of a proof of the given kind: one for `usk`, and one per
    /// variable the clauses of the base allocate. Tag clauses add none (they are linear in the
    /// key alone).
    #[must_use]
    pub const fn responses(kind: ProofKind) -> usize {
        match kind {
            ProofKind::Identifier => 1,
            ProofKind::Attestation | ProofKind::Possession => 1 + B::POSSESSION_VARIABLES,
            ProofKind::Issuance => 1 + B::ISSUANCE_VARIABLES,
        }
    }

    /// [`Error::LengthMismatch`] unless the relation has `expected` variables.
    fn expect_variables(relation: &PairingRelation<E>, expected: usize) -> Result<(), Error> {
        let actual = relation.num_scalars();
        if actual == expected {
            Ok(())
        } else {
            Err(Error::LengthMismatch { expected, actual })
        }
    }

    /// `R_Tag` for `(t, x)`: the tag clause on the variable `usk`.
    ///
    /// # Errors
    /// Propagates the errors of the relation.
    pub fn identifier_relation(
        params: &PairingParams<E, B, T>,
        tag: &E::G1,
        point: &E::ScalarField,
    ) -> Result<PairingRelation<E>, Error> {
        let mut relation = PairingRelation::new();
        let usk = relation.alloc_scalar();
        for equation in params.tag.tag_equations(usk, tag, point) {
            relation.add_g1(equation)?;
        }
        Self::expect_variables(&relation, Self::responses(ProofKind::Identifier))?;
        Ok(relation)
    }

    /// `R_att` for `(hvk, σ*, t, x)`: the clauses of `Π_Possess` and the tag clause, sharing
    /// `usk`.
    ///
    /// # Errors
    /// Propagates the errors of the clause builders; [`Error::LengthMismatch`] if the base
    /// allocates another number of variables than it declares.
    pub fn attestation_relation(
        params: &PairingParams<E, B, T>,
        vk: &B::VerificationKey,
        show: &B::Show,
        tag: &E::G1,
        point: &E::ScalarField,
    ) -> Result<PairingRelation<E>, Error> {
        let mut relation = PairingRelation::new();
        let usk = relation.alloc_scalar();
        B::possession_clauses(&params.base, vk, show, &mut relation, usk)?;
        for equation in params.tag.tag_equations(usk, tag, point) {
            relation.add_g1(equation)?;
        }
        Self::expect_variables(&relation, Self::responses(ProofKind::Attestation))?;
        Ok(relation)
    }

    /// `R_iss` for `(hvk, Ĉ, id)`: the clauses of `Π_PrepareIssue` and the tag clause at
    /// `(id, x_0)`, sharing `usk`.
    ///
    /// # Errors
    /// Propagates the errors of the clause builders; [`Error::LengthMismatch`] if the base
    /// allocates another number of variables than it declares.
    pub fn issuance_relation(
        params: &PairingParams<E, B, T>,
        vk: &B::VerificationKey,
        request: &B::Request,
        id: &E::G1,
        x0: &E::ScalarField,
    ) -> Result<PairingRelation<E>, Error> {
        let mut relation = PairingRelation::new();
        let usk = relation.alloc_scalar();
        B::issuance_clauses(&params.base, vk, request, &mut relation, usk)?;
        for equation in params.tag.tag_equations(usk, id, x0) {
            relation.add_g1(equation)?;
        }
        Self::expect_variables(&relation, Self::responses(ProofKind::Issuance))?;
        Ok(relation)
    }

    /// `R_Possess` for `(hvk, σ*)`: the clauses of `Π_Possess`.
    ///
    /// # Errors
    /// Propagates the errors of the clause builders; [`Error::LengthMismatch`] if the base
    /// allocates another number of variables than it declares.
    pub fn possession_relation(
        params: &PairingParams<E, B, T>,
        vk: &B::VerificationKey,
        show: &B::Show,
    ) -> Result<PairingRelation<E>, Error> {
        let mut relation = PairingRelation::new();
        let usk = relation.alloc_scalar();
        B::possession_clauses(&params.base, vk, show, &mut relation, usk)?;
        Self::expect_variables(&relation, Self::responses(ProofKind::Possession))?;
        Ok(relation)
    }

    /// The witness `(usk, ω)` of `R_att` and `R_Possess`, in the variable order of their
    /// relations, in a buffer that is wiped on drop.
    fn possession_witness(
        usk: &E::ScalarField,
        cred: &B::Credential,
        omega: &B::ShowWitness,
    ) -> Witness<E::ScalarField> {
        let mut witness = Witness::with_capacity(1 + B::POSSESSION_VARIABLES);
        witness.push(*usk);
        B::possession_witness(cred, omega, &mut witness);
        witness
    }

    /// [`Error::InvalidProof`] unless `proof` verifies for `relation` under `ctx`.
    fn verified(
        relation: &PairingRelation<E>,
        ctx: &[u8],
        proof: &FSProof<E::ScalarField>,
    ) -> Result<(), Error> {
        if fiat_shamir::verify(relation, ctx, proof) {
            Ok(())
        } else {
            Err(Error::InvalidProof)
        }
    }
}

impl<E, B, T> Backend for PairingBackend<E, B, T>
where
    E: Pairing,
    B: Base<E>,
    T: ProtocolTag<E::G1> + 'static,
{
    type Params = PairingParams<E, B, T>;
    type UserKey = E::ScalarField;
    type Point = E::ScalarField;
    type Tag = E::G1;
    type VerificationKey = B::VerificationKey;
    type SigningKey = B::SigningKey;
    type Request = B::Request;
    type IssuanceTape = E::ScalarField;
    type PreCredential = B::PreCredential;
    type Credential = B::Credential;
    type Show = B::Show;
    type Proof = FSProof<E::ScalarField>;

    fn name() -> String {
        format!("{}+{}", B::NAME, T::NAME)
    }

    fn setup(label: &[u8]) -> Result<Self::Params, Error> {
        let params = PairingParams {
            base: B::setup(label)?,
            tag: T::setup(label)?,
        };
        Self::check_params(&params)?;
        Ok(params)
    }

    fn check_params(params: &Self::Params) -> Result<(), Error> {
        B::check_params(&params.base)?;
        // Degeneracy first: the `Valid` check of an instance may refuse a degenerate instance
        // too (`Tag_DY` with the identity as its generator), which is not a value outside its
        // group but no `pp_Tag` at all.
        if !params.tag.is_well_formed() {
            return Err(Error::DegenerateInput("pp_Tag"));
        }
        validate(&params.tag, "pp_Tag")
    }

    /// `x_0 = H_id(⟨hvk⟩)`: the transcript's output in `Z_p` (its oracle suffix `/PCREDS-HID`
    /// separates it from `H_req`).
    fn identifier_point(_params: &Self::Params, transcript: &Transcript) -> E::ScalarField {
        transcript.challenge_scalar()
    }

    /// `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`: the transcript's output in `Z_p` (oracle suffix
    /// `/PCREDS-HREQ`).
    fn request_point(_params: &Self::Params, transcript: &Transcript) -> E::ScalarField {
        transcript.challenge_scalar()
    }

    fn tag_keygen<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        rng: &mut R,
    ) -> E::ScalarField {
        params.tag.keygen(rng)
    }

    fn tag(params: &Self::Params, usk: &E::ScalarField, point: &E::ScalarField) -> Option<E::G1> {
        params.tag.eval(usk, point)
    }

    fn check_tag(
        params: &Self::Params,
        tag: &E::G1,
        point: &E::ScalarField,
        what: &'static str,
    ) -> Result<(), Error> {
        validate(tag, what)?;
        if params.tag.valid_tag(tag, point) {
            Ok(())
        } else {
            Err(Error::InvalidTag)
        }
    }

    fn keygen<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        rng: &mut R,
    ) -> (B::VerificationKey, B::SigningKey) {
        B::keygen(&params.base, rng)
    }

    fn check_key(params: &Self::Params, vk: &B::VerificationKey) -> Result<(), Error> {
        validate(vk, "hvk")?;
        if B::admissible_key(&params.base, vk) {
            Ok(())
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn key_pair_matches(
        params: &Self::Params,
        vk: &B::VerificationKey,
        sk: &B::SigningKey,
    ) -> bool {
        B::key_pair_matches(&params.base, vk, sk)
    }

    fn prepare_issue<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        vk: &B::VerificationKey,
        usk: &E::ScalarField,
        rng: &mut R,
    ) -> Result<(B::Request, E::ScalarField), Error> {
        // One sample: "If Ĉ = ⊥, output (CredentialRequestFailed, ssid) and stop this call".
        let mut tau = E::ScalarField::rand(rng);
        // A request that the verifier of R_iss would refuse is refused here as well.
        match B::prepare_issue(&params.base, vk, usk, &tau) {
            Some(request) if B::issuance_public_check(&params.base, vk, &request) => {
                Ok((request, tau))
            }
            _ => {
                tau.zeroize();
                Err(Error::InvalidIssuanceEncoding)
            }
        }
    }

    fn blind_issue<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        sk: &B::SigningKey,
        request: &B::Request,
        rng: &mut R,
    ) -> Result<B::PreCredential, Error> {
        B::blind_issue(&params.base, sk, request, rng).ok_or(Error::InvalidIssuanceEncoding)
    }

    fn unblind(
        params: &Self::Params,
        vk: &B::VerificationKey,
        usk: &E::ScalarField,
        pre: &B::PreCredential,
        tau: &E::ScalarField,
    ) -> Result<B::Credential, Error> {
        validate(pre, "σ̂")?;
        let mut cred =
            B::unblind(&params.base, vk, usk, pre, tau).ok_or(Error::InvalidPreCredential)?;
        if B::UNBLIND_VERIFIES || B::verify(&params.base, vk, usk, &cred) {
            Ok(cred)
        } else {
            cred.zeroize();
            Err(Error::InvalidPreCredential)
        }
    }

    fn verify(
        params: &Self::Params,
        vk: &B::VerificationKey,
        usk: &E::ScalarField,
        cred: &B::Credential,
    ) -> bool {
        B::verify(&params.base, vk, usk, cred)
    }

    fn prove_tag<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        tag: &E::G1,
        point: &E::ScalarField,
        usk: &E::ScalarField,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<FSProof<E::ScalarField>, Error> {
        if !params.tag.valid_tag(tag, point) {
            return Err(Error::InvalidTag);
        }
        let relation = Self::identifier_relation(params, tag, point)?;
        let mut witness = Witness::with_capacity(1);
        witness.push(*usk);
        fiat_shamir::prove(&relation, &witness, ctx, rng)
    }

    fn check_tag_proof(
        params: &Self::Params,
        tag: &E::G1,
        point: &E::ScalarField,
        ctx: &[u8],
        proof: &FSProof<E::ScalarField>,
    ) -> Result<(), Error> {
        let relation = Self::identifier_relation(params, tag, point)?;
        Self::verified(&relation, ctx, proof)
    }

    fn prove_attestation<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        statement: &AttestationStatement<'_, Self>,
        usk: &E::ScalarField,
        cred: &B::Credential,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<(B::Show, FSProof<E::ScalarField>), Error> {
        let (show, omega) = B::rerand(&params.base, statement.vk, usk, cred, rng);
        let relation = Self::attestation_relation(
            params,
            statement.vk,
            &show,
            statement.tag,
            statement.point,
        )?;
        let witness = Self::possession_witness(usk, cred, &omega);
        let proof = fiat_shamir::prove(&relation, &witness, ctx, rng)?;
        Ok((show, proof))
    }

    fn check_attestation_proof(
        params: &Self::Params,
        statement: &AttestationStatement<'_, Self>,
        show: &B::Show,
        ctx: &[u8],
        proof: &FSProof<E::ScalarField>,
    ) -> Result<(), Error> {
        validate(show, "σ*")?;
        if !B::possession_public_check(&params.base, statement.vk, show) {
            return Err(Error::InvalidCredential);
        }
        let relation =
            Self::attestation_relation(params, statement.vk, show, statement.tag, statement.point)?;
        Self::verified(&relation, ctx, proof)
    }

    fn prove_issuance<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        statement: &IssuanceStatement<'_, Self>,
        usk: &E::ScalarField,
        tau: &E::ScalarField,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<FSProof<E::ScalarField>, Error> {
        let relation = Self::issuance_relation(
            params,
            statement.vk,
            statement.request,
            statement.id,
            statement.x0,
        )?;
        let mut witness = Witness::with_capacity(1 + B::ISSUANCE_VARIABLES);
        witness.push(*usk);
        B::issuance_witness(tau, &mut witness);
        fiat_shamir::prove(&relation, &witness, ctx, rng)
    }

    fn check_issuance_proof(
        params: &Self::Params,
        statement: &IssuanceStatement<'_, Self>,
        ctx: &[u8],
        proof: &FSProof<E::ScalarField>,
    ) -> Result<(), Error> {
        validate(statement.request, "Ĉ")?;
        if !B::issuance_public_check(&params.base, statement.vk, statement.request) {
            return Err(Error::InvalidIssuanceEncoding);
        }
        let relation = Self::issuance_relation(
            params,
            statement.vk,
            statement.request,
            statement.id,
            statement.x0,
        )?;
        Self::verified(&relation, ctx, proof)
    }

    fn prove_possession<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        vk: &B::VerificationKey,
        usk: &E::ScalarField,
        cred: &B::Credential,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<(B::Show, FSProof<E::ScalarField>), Error> {
        let (show, omega) = B::rerand(&params.base, vk, usk, cred, rng);
        let relation = Self::possession_relation(params, vk, &show)?;
        let witness = Self::possession_witness(usk, cred, &omega);
        let proof = fiat_shamir::prove(&relation, &witness, ctx, rng)?;
        Ok((show, proof))
    }

    fn check_possession_proof(
        params: &Self::Params,
        vk: &B::VerificationKey,
        show: &B::Show,
        ctx: &[u8],
        proof: &FSProof<E::ScalarField>,
    ) -> Result<(), Error> {
        validate(show, "σ*")?;
        if !B::possession_public_check(&params.base, vk, show) {
            return Err(Error::InvalidCredential);
        }
        let relation = Self::possession_relation(params, vk, show)?;
        Self::verified(&relation, ctx, proof)
    }

    fn proof_compact_size(proof: &FSProof<E::ScalarField>) -> usize {
        proof.compact_size()
    }

    /// [`MAX_LEAF_BYTES`] for every leaf: the leaves are a few group elements, and a proof of at
    /// most eight scalars (264 bytes canonically).
    fn max_leaf_bytes(_leaf: Leaf) -> usize {
        MAX_LEAF_BYTES
    }

    fn serialize_proof_compact<W: Write>(
        kind: ProofKind,
        proof: &FSProof<E::ScalarField>,
        writer: W,
    ) -> Result<(), Error> {
        let expected = Self::responses(kind);
        if proof.responses.len() != expected {
            return Err(Error::LengthMismatch {
                expected,
                actual: proof.responses.len(),
            });
        }
        proof.serialize_compact(writer)
    }

    fn deserialize_proof_compact<R: Read>(
        kind: ProofKind,
        reader: R,
    ) -> Result<FSProof<E::ScalarField>, Error> {
        FSProof::deserialize_compact(reader, Self::responses(kind))
    }
}
