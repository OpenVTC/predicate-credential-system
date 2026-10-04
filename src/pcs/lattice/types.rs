//! The protocol objects of the lattice construction: `pp`, keys, credentials, attestations,
//! issuance proofs, root requests and the issuance state.
//!
//! | paper | here | encoding (bytes) |
//! |---|---|---|
//! | `pp = (pp_Σ, pp_Tag, EncPred, H_0, H_1, c_0)` and Jali's `pp_seed` | [`PublicParameters`] | none: derived from the label |
//! | `hvk = h`, `hsk = (sk, hvk)` | [`VSISVerificationKey`](crate::cred::vsis::VSISVerificationKey), [`HelperSecretKey<VSIS>`](crate::pcs::HelperSecretKey) | 2560; 5897 + 2560 + 32 |
//! | `usk` | [`UserSecretKey`] | 256 |
//! | `id`, $`id_{j \to i}`$, $`id_{i \to i}`$ | [`LWRTag`] | 336 |
//! | `cred = ((s, x_1), x_0)` | [`Credential`] | 5120 + 256 + 512 = 5888 |
//! | $`\widehat{cred} = (s, x_1)`$ | [`VSISPreCredential`](crate::cred::vsis::VSISPreCredential) | 5376 |
//! | $`att_j = (id_{j \to i}, cred^*_j = \bot, \phi_j, \pi_j)`$ | [`Attestation`] | 336 + 128 + 4 + $`\lvert\pi_j\rvert`$ |
//! | $`\pi = ((att_j)_j, C, id_{i \to i}, \pi_0)`$ | [`IssuanceProof`] | canonical: 4 + compact; compact: $`\sum_j\lvert att_j\rvert`$ + 2560 + 336 + 4 + $`\lvert\pi_0\rvert`$ |
//! | the root request $`(C, id_{i \to i}, \pi_0)`$ | [`RootRequest`] | 2560 + 336 + 4 + $`\lvert\pi_0\rvert`$ |
//! | $`st_{\mathsf{iss}} = (m_{\mathsf{hid}}, \phi, \rho)`$, $`\rho = x_0 = m_{\mathsf{aux}}`$ | [`IssuanceState`] | 256 + 512 + 128 = 896 |
//!
//! A Jali proof ([`Proof`]) travels with a 4-byte little-endian length: its length varies by
//! tens of bytes with the proof seed, and Jali's decoder neither reads nor tolerates a length
//! (it rejects truncation and trailing bytes). Inside the protocol objects a proof is bounded by
//! its parameter set, at twice the set's estimated size: an attestation's $`\pi_j`$ by
//! [`ATT_PROOF_MAX_BYTES`] (171,216 bytes), the $`\pi_0`$ of an issuance proof or a root request
//! by [`ISSUE_PROOF_MAX_BYTES`] (85,824 bytes). The encoders, the decoders and the verifiers of
//! [`super::LatticePCS`] refuse a longer proof before any work on it (a stand-alone [`Proof`]
//! keeps Jali's own limit, 16 MiB). The canonical encoding of an issuance proof starts with the
//! number of attestations (4 bytes little-endian); the compact encoding of [`super::codec`]
//! omits it and takes $`k`$ from the predicate, as in the pairing codec. For an attestation and a
//! root request the two encodings coincide.
//!
//! Every field is a type whose values are canonical by construction ([`Rq`], [`LWRTag`],
//! [`BinaryPoly`], [`Ternary`]), and every decoder enforces canonicity whatever `Validate` flag
//! it is given: unlike group elements, nothing has to be re-validated after decoding. The one
//! value a type admits beyond its space is a WIPED element (`Zeroize` empties [`Rq`] and
//! [`Ternary`]); the encoders refuse it ([`SerializationError::InvalidData`]) and the algorithms
//! of [`super::LatticePCS`] treat it as malformed input.

use core::fmt;

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use crate::{
    cred::{
        CredentialBase, VSIS,
        vsis::{VSISCredential, VSISPublicParams},
    },
    error::Error,
    kiprf::lwr::{LWR, LWRTag, TagMatrix},
    lattice::{
        BinaryPoly, ELL_R, Rq, Ternary, oracles,
        sets::{ATT_PROOF_MAX_BYTES, ISSUE_PROOF_MAX_BYTES},
        xof,
    },
    pcs::HelperSecretKey,
};

/// Bytes of the length prefix of a Jali proof.
pub(super) const LENGTH_BYTES: usize = 4;

/// A Jali proof: the bytes of `Compiled::prove_bytes_with_seed`, at most [`Proof::MAX_BYTES`].
/// Public.
///
/// Encoding: `LE32(len) ‖ bytes` ([`Self::encoded_size`] bytes). The decoder refuses a length
/// above [`Self::MAX_BYTES`] before it reads the proof, and it allocates only as the input
/// arrives, so a forged length on a short input fails fast. Inside an [`Attestation`], an
/// [`IssuanceProof`] or a [`RootRequest`] the bound is the one of the proof's parameter set
/// (module docs). Jali's own decoder is strict (truncation, trailing bytes, non-canonical codes),
/// so a valid proof has exactly one encoding.
#[derive(Clone, PartialEq, Eq)]
pub struct Proof(Vec<u8>);

impl Proof {
    /// The largest stand-alone proof, Jali's own decoding limit (16 MiB). Proofs of this
    /// instantiation have about 83 KB (`R_att`) and 41 KB (`R_issue`), and the protocol objects
    /// accept at most twice their estimates ([`ATT_PROOF_MAX_BYTES`], [`ISSUE_PROOF_MAX_BYTES`]).
    pub const MAX_BYTES: usize = 1 << 24;

    /// Writes `LE32(len) ‖ bytes`, refusing a proof longer than `max`.
    fn write_bounded<W: Write>(&self, mut writer: W, max: usize) -> Result<(), SerializationError> {
        if self.0.len() > max.min(Self::MAX_BYTES) {
            return Err(SerializationError::InvalidData);
        }
        // MAX_BYTES < 2^32: the cast is lossless
        writer.write_all(&(self.0.len() as u32).to_le_bytes())?;
        writer.write_all(&self.0)?;
        Ok(())
    }

    /// Reads `LE32(len) ‖ bytes`, refusing a length above `max` before it reads the proof.
    fn read_bounded<R: Read>(mut reader: R, max: usize) -> Result<Self, SerializationError> {
        let mut length = [0u8; LENGTH_BYTES];
        reader.read_exact(&mut length)?;
        let length = u32::from_le_bytes(length) as usize;
        if length > max.min(Self::MAX_BYTES) {
            return Err(SerializationError::InvalidData);
        }
        // `take` + `read_to_end` grows the buffer with the input, so a forged length does not
        // allocate the maximum up front
        let mut bytes = Vec::new();
        reader
            .by_ref()
            .take(length as u64)
            .read_to_end(&mut bytes)?;
        if bytes.len() != length {
            return Err(SerializationError::IoError(std::io::Error::from(
                std::io::ErrorKind::UnexpectedEof,
            )));
        }
        Ok(Self(bytes))
    }

    /// Wraps proof bytes.
    ///
    /// # Errors
    /// [`Error::Serialization`] above [`Self::MAX_BYTES`].
    pub fn from_bytes(bytes: Vec<u8>) -> Result<Self, Error> {
        if bytes.len() > Self::MAX_BYTES {
            return Err(Error::Serialization(format!(
                "Jali proof of {} bytes, more than {}",
                bytes.len(),
                Self::MAX_BYTES
            )));
        }
        Ok(Self(bytes))
    }

    /// The proof bytes, as Jali encodes them.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// The length of the proof in bytes, $`|\pi|`$.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the proof has no bytes (no proof of this crate is empty).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Bytes of the encoding: the 4-byte length and the proof.
    #[must_use]
    pub fn encoded_size(&self) -> usize {
        LENGTH_BYTES + self.0.len()
    }
}

impl fmt::Debug for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Proof({} bytes)", self.0.len())
    }
}

impl CanonicalSerialize for Proof {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.write_bounded(writer, Self::MAX_BYTES)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        self.encoded_size()
    }
}

impl Valid for Proof {
    fn check(&self) -> Result<(), SerializationError> {
        if self.0.len() <= Self::MAX_BYTES {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl CanonicalDeserialize for Proof {
    /// Refuses a length above [`Proof::MAX_BYTES`], whatever `validate` says.
    fn deserialize_with_mode<R: Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Self::read_bounded(reader, Self::MAX_BYTES)
    }
}

/// The public parameters of the lattice construction, all derived from the deployment label
/// (transparent `Setup`; bb:795, "from public randomness"): `pp_Σ` of `Σ-vSIS`, the tag
/// (constants), $`c_0 = H_0(\texttt{"identity"})`$, and Jali's public seed. `EncPred`, `H_0` and
/// `H_1` are fixed functions of the label.
///
/// Implementation note: `pp_seed`, the seed from which Jali expands the public matrices of its
/// commitments, is not part of the paper's `pp` (con:110-114); it has to come from public
/// randomness all the same, never from the helper, so it is derived from the label like
/// everything else (`/LATTICE-JALI-SEED`, [`crate::lattice`]). The parameter sets of Jali are
/// constants of the crate ([`crate::lattice::sets`]); the digest of `pp`
/// ([`Self::digest`]) covers them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicParameters {
    /// The deployment label.
    pub label: Vec<u8>,
    /// $`pp_\Sigma = (v, b_u, b_\phi, B_r)`$.
    pub pp_sigma: VSISPublicParams,
    /// $`pp_{\mathsf{Tag}}`$: the constants of tag set R.
    pub pp_tag: LWR,
    /// $`c_0 = H_0(\texttt{"identity"})`$.
    pub c0: TagMatrix,
    /// Jali's public seed `pp_seed` (`/LATTICE-JALI-SEED`).
    pub jali_pp_seed: [u8; 32],
}

impl PublicParameters {
    /// `Setup` steps 1-2 (con:110-114) for the deployment `label`: `pp_Σ` of `Σ-vSIS` (bb:795),
    /// the constants of the tag, $`c_0 = H_0(\texttt{"identity"})`$ (con:112, con:210) and Jali's
    /// `pp_seed`. About 1 ms, most of it the 168 × 1024 entries of $`c_0`$.
    ///
    /// # Errors
    /// The errors of [`CredentialBase::setup`] for `Σ-vSIS` (none occur).
    pub(crate) fn derive(label: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            label: label.to_vec(),
            pp_sigma: VSIS::setup(label)?,
            pp_tag: LWR,
            c0: oracles::identity_point(label),
            jali_pp_seed: xof::jali_pp_seed(label),
        })
    }
}

/// A user secret key `usk`: the tag key, uniform on $`\{-1, 0, 1\}^n`$, and the first component
/// of every credential's hidden message. Secret: wiped on drop, not `Clone`, redacted.
///
/// Encoding: one [`Ternary`] ([`Self::BYTES`] bytes); [`Self::to_bytes`] writes it into a buffer
/// that is wiped on drop.
pub struct UserSecretKey(pub(super) Ternary);

impl UserSecretKey {
    /// Bytes of the encoding.
    pub const BYTES: usize = Ternary::BYTES;

    /// Wraps a ternary polynomial as a user key.
    #[must_use]
    pub fn from_ternary(usk: Ternary) -> Self {
        Self(usk)
    }

    /// The secret polynomial.
    #[must_use]
    pub fn expose_ternary(&self) -> &Ternary {
        &self.0
    }

    /// The encoding of `usk` in a buffer that is wiped on drop. The way back is
    /// [`WireFormat::from_bytes`](crate::serialization::WireFormat::from_bytes).
    ///
    /// Implementation note: this inherent method takes precedence over the blanket
    /// [`WireFormat::to_bytes`](crate::serialization::WireFormat::to_bytes), which would return
    /// the same bytes in a plain `Vec<u8>` that nobody wipes.
    ///
    /// # Errors
    /// [`Error::Serialization`] for a wiped key.
    pub fn to_bytes(&self) -> Result<Zeroizing<Vec<u8>>, Error> {
        if self.0.check().is_err() {
            return Err(Error::Serialization("a wiped user key".into()));
        }
        Ok(self.0.to_bytes())
    }
}

impl Zeroize for UserSecretKey {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

/// The polynomial wipes itself on drop.
impl ZeroizeOnDrop for UserSecretKey {}

impl fmt::Debug for UserSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("UserSecretKey(<redacted>)")
    }
}

impl CanonicalSerialize for UserSecretKey {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.0.serialized_size(compress)
    }
}

impl Valid for UserSecretKey {
    fn check(&self) -> Result<(), SerializationError> {
        self.0.check()
    }
}

impl CanonicalDeserialize for UserSecretKey {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ternary::deserialize_with_mode(reader, compress, validate).map(Self)
    }
}

/// The lattice helper key `hsk = (sk, hvk)` with the digest of its `pp`: `sk` is a
/// [`VSISSigningKey`](crate::cred::vsis::VSISSigningKey), which carries the issuance count.
impl HelperSecretKey<VSIS> {
    /// The encoding of `hsk` ([`HelperSecretKey::to_bytes`]: `sk ‖ hvk ‖ pp-digest`, 8489 bytes)
    /// with the issuance count inside `sk` ADVANCED by `n`, saturating at $`Q_{\max}`$
    /// ([`VSISSigningKey::to_bytes_reserving`](crate::cred::vsis::VSISSigningKey::to_bytes_reserving)),
    /// in a buffer that is wiped on drop. A helper stores it BEFORE it answers up to `n` more
    /// requests, and stores again before `hsk.signing_key().issued()` passes the count it stored
    /// last; a restart from the stored copy then never reuses a unit of the cap
    /// (`docs/operating-a-helper.md`). The in-memory count is unchanged, and
    /// `to_bytes_reserving(0)` equals [`HelperSecretKey::to_bytes`].
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped key; [`Error::Serialization`] if `hvk` was wiped.
    pub fn to_bytes_reserving(&self, n: u64) -> Result<Zeroizing<Vec<u8>>, Error> {
        let sk = self.sk.to_bytes_reserving(n)?;
        // the field order of the derived encoding of `HelperSecretKey`: sk, hvk, pp_digest
        let mut bytes = Zeroizing::new(Vec::with_capacity(
            sk.len() + self.hvk.compressed_size() + self.pp_digest.compressed_size(),
        ));
        bytes.extend_from_slice(&sk);
        self.hvk.serialize_compressed(&mut *bytes)?;
        self.pp_digest.serialize_compressed(&mut *bytes)?;
        Ok(bytes)
    }
}

/// A credential $`cred = (cred_\Sigma, m_{\mathsf{aux}}) = ((s, x_1), x_0)`$. Private to its holder:
/// it is the witness of every attestation it makes. Redacted in `Debug`, wiped on drop (its
/// parts are), compared in constant time (both parts, without a short circuit between them).
///
/// Encoding: $`cred_\Sigma`$ ([`VSISCredential`], 5376 bytes) ‖ $`x_{0,0}`$ ‖ $`x_{0,1}`$
/// ([`Ternary`], 256 bytes each): [`Self::BYTES`] bytes. [`Self::to_bytes`] writes it into a
/// buffer that is wiped on drop. Decoding checks canonicity, not validity (that is
/// [`PredicateCredentialSystem::verify_cred`](crate::pcs::PredicateCredentialSystem::verify_cred)).
#[derive(Clone)]
pub struct Credential {
    /// $`cred_\Sigma = (s, x_1)`$.
    pub cred: VSISCredential,
    /// $`m_{\mathsf{aux}} = x_0`$.
    pub x0: [Ternary; ELL_R],
}

impl Credential {
    /// Bytes of the encoding: $`5376 + 2 \cdot 256`$.
    pub const BYTES: usize = VSISCredential::BYTES + ELL_R * Ternary::BYTES;

    /// The encoding in a buffer that is wiped on drop (the type docs). The way back is
    /// [`WireFormat::from_bytes`](crate::serialization::WireFormat::from_bytes).
    ///
    /// # Errors
    /// [`Error::Serialization`] for a wiped credential.
    pub fn to_bytes(&self) -> Result<Zeroizing<Vec<u8>>, Error> {
        // sized up front: the buffer never moves, so no unwiped copy is left behind
        let mut bytes = Zeroizing::new(Vec::with_capacity(Self::BYTES));
        self.serialize_compressed(&mut *bytes)?;
        Ok(bytes)
    }
}

impl PartialEq for Credential {
    /// In constant time: every part is compared in constant time, and the parts are combined
    /// with `&`, so a difference in $`cred_\Sigma`$ does not skip the comparison of $`x_0`$.
    fn eq(&self, other: &Self) -> bool {
        (self.cred == other.cred)
            & self
                .x0
                .iter()
                .zip(&other.x0)
                .fold(true, |equal, (a, b)| equal & a.ct_eq(b))
    }
}

impl Eq for Credential {}

impl fmt::Debug for Credential {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Credential(<redacted>)")
    }
}

/// Its parts wipe themselves on drop.
impl ZeroizeOnDrop for Credential {}

impl Zeroize for Credential {
    fn zeroize(&mut self) {
        self.cred.zeroize();
        self.x0.zeroize();
    }
}

impl CanonicalSerialize for Credential {
    /// Fails for a wiped credential.
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.cred.serialize_with_mode(&mut writer, compress)?;
        for x in &self.x0 {
            x.serialize_with_mode(&mut writer, compress)?;
        }
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for Credential {
    fn check(&self) -> Result<(), SerializationError> {
        self.cred.check()?;
        self.x0.iter().try_for_each(Valid::check)
    }
}

impl CanonicalDeserialize for Credential {
    /// Canonical parts, whatever `validate` says (no code `−2^{19}` in $`s`$, no ternary code
    /// `10`).
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let cred = VSISCredential::deserialize_with_mode(&mut reader, compress, validate)?;
        let x0_0 = Ternary::deserialize_with_mode(&mut reader, compress, validate)?;
        let x0_1 = Ternary::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(Self {
            cred,
            x0: [x0_0, x0_1],
        })
    }
}

/// An attestation $`att_j = (id_{j \to i}, \phi_j, \pi_j)`$ for an identifier $`id_i`$ (`cred* = ⊥`
/// is empty and omitted): the attester's tag at $`s_i = H_0(\langle id_i\rangle)`$, the label of its
/// credential, and the Jali proof for `R_att` under $`ctx_j`$.
///
/// The fields are public, and the verifiers make no assumption about how a value was built: the
/// tag and $`\phi_j`$ are canonical by type (`ValidTag` and $`\phi_j \in \mathcal M_{\mathsf{pub}}`$
/// hold for every value), and the proof is checked by Jali against the statement the verifier
/// rebuilds.
///
/// Encoding (canonical and compact alike): $`id_{j \to i}`$ (336) ‖ $`\phi_j`$ (128) ‖
/// `LE32(|π_j|)` ‖ $`\pi_j`$, with $`|\pi_j| \le`$ [`ATT_PROOF_MAX_BYTES`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Attestation {
    /// $`id_{j \to i} = \mathsf{Tag}(usk_j, s_i)`$.
    pub tag: LWRTag,
    /// $`\phi_j = \mathsf{EncPred}(f_j)`$.
    pub phi: BinaryPoly,
    /// $`\pi_j`$.
    pub proof: Proof,
}

impl Attestation {
    /// The bytes of the encoding besides the Jali proof: the tag, $`\phi_j`$ and the length.
    pub const FIXED_BYTES: usize = LWRTag::BYTES + BinaryPoly::BYTES + LENGTH_BYTES;

    pub(super) fn write<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        self.tag.serialize_compressed(&mut writer)?;
        self.phi.serialize_compressed(&mut writer)?;
        self.proof.write_bounded(&mut writer, ATT_PROOF_MAX_BYTES)
    }

    pub(super) fn read<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        Ok(Self {
            tag: LWRTag::deserialize_compressed(&mut reader)?,
            phi: BinaryPoly::deserialize_compressed(&mut reader)?,
            proof: Proof::read_bounded(&mut reader, ATT_PROOF_MAX_BYTES)?,
        })
    }
}

impl CanonicalSerialize for Attestation {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.write(writer)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::FIXED_BYTES + self.proof.len()
    }
}

impl Valid for Attestation {
    fn check(&self) -> Result<(), SerializationError> {
        bounded(&self.proof, ATT_PROOF_MAX_BYTES)
    }
}

/// [`SerializationError::InvalidData`] for a proof longer than `max`.
fn bounded(proof: &Proof, max: usize) -> Result<(), SerializationError> {
    if proof.len() <= max {
        Ok(())
    } else {
        Err(SerializationError::InvalidData)
    }
}

impl CanonicalDeserialize for Attestation {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Self::read(reader)
    }
}

/// An issuance proof $`\pi = ((att_j)_{j \in [k]}, C, id_{i \to i}, \pi_0)`$.
///
/// $`id_{i \to i}`$ is a mandatory field: a proof without the self-exclusion tag does not exist in
/// this format. The fields are public, and `VerifyProof` makes no assumption about how a value
/// was built (a wiped $`C`$ is refused as [`Error::InvalidIssuanceEncoding`]).
///
/// Encoding: canonical `LE32(k)` ‖ compact; compact ([`super::codec`]):
/// $`att_1 \| \dots \| att_k`$ ‖ $`C`$ (2560) ‖ $`id_{i \to i}`$ (336) ‖ `LE32(|π_0|)` ‖ $`\pi_0`$,
/// with $`|\pi_0| \le`$ [`ISSUE_PROOF_MAX_BYTES`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IssuanceProof {
    /// $`(att_j)_{j \in [k]}`$, forwarded verbatim. A verifier accepts EXACTLY $`k`$.
    pub attestations: Vec<Attestation>,
    /// $`C = b_u\,usk + B_r x_0`$.
    pub c: Rq,
    /// The self-exclusion tag $`id_{i \to i} = \mathsf{Tag}(usk, s_i)`$.
    pub t0: LWRTag,
    /// $`\pi_0`$, the Jali proof for `R_issue` under $`ctx_0`$.
    pub proof: Proof,
}

impl IssuanceProof {
    /// The bytes of the compact encoding besides the attestations and the Jali proof: $`C`$,
    /// $`id_{i \to i}`$ and the length of $`\pi_0`$.
    pub const FIXED_BYTES: usize = Rq::BYTES + LWRTag::BYTES + LENGTH_BYTES;

    /// The compact encoding: no number of attestations.
    pub(super) fn write_compact<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        for attestation in &self.attestations {
            attestation.write(&mut writer)?;
        }
        self.c.check()?;
        self.c.serialize_compressed(&mut writer)?;
        self.t0.serialize_compressed(&mut writer)?;
        self.proof.write_bounded(&mut writer, ISSUE_PROOF_MAX_BYTES)
    }

    /// The compact encoding of a proof with exactly `k` attestations.
    pub(super) fn read_compact<R: Read>(mut reader: R, k: u32) -> Result<Self, SerializationError> {
        // Not `with_capacity(k)`: `k` may be large and the input short. Every attestation consumes
        // at least `Attestation::FIXED_BYTES` of input, so the vector never outgrows it.
        let mut attestations = Vec::new();
        for _ in 0..k {
            attestations.push(Attestation::read(&mut reader)?);
        }
        Ok(Self {
            attestations,
            c: Rq::deserialize_compressed(&mut reader)?,
            t0: LWRTag::deserialize_compressed(&mut reader)?,
            proof: Proof::read_bounded(&mut reader, ISSUE_PROOF_MAX_BYTES)?,
        })
    }
}

impl CanonicalSerialize for IssuanceProof {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        let k =
            u32::try_from(self.attestations.len()).map_err(|_| SerializationError::InvalidData)?;
        writer.write_all(&k.to_le_bytes())?;
        self.write_compact(writer)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        LENGTH_BYTES
            + self
                .attestations
                .iter()
                .map(|a| Attestation::FIXED_BYTES + a.proof.len())
                .sum::<usize>()
            + Self::FIXED_BYTES
            + self.proof.len()
    }
}

impl Valid for IssuanceProof {
    fn check(&self) -> Result<(), SerializationError> {
        self.attestations.iter().try_for_each(Valid::check)?;
        self.c.check()?;
        bounded(&self.proof, ISSUE_PROOF_MAX_BYTES)
    }
}

impl CanonicalDeserialize for IssuanceProof {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut k = [0u8; LENGTH_BYTES];
        reader.read_exact(&mut k)?;
        Self::read_compact(reader, u32::from_le_bytes(k))
    }
}

/// A root request $`(C, id_{i \to i}, \pi_0)`$ (Remark "Chaining and the base case"), with
/// $`\pi_0`$ for `R_issue` under $`ctx_{\mathsf{root}}`$ and the parameter set `issue-root`.
///
/// Encoding (canonical and compact alike): $`C`$ (2560) ‖ $`id_{i \to i}`$ (336) ‖
/// `LE32(|π_0|)` ‖ $`\pi_0`$, with $`|\pi_0| \le`$ [`ISSUE_PROOF_MAX_BYTES`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootRequest {
    /// $`C = b_u\,usk + B_r x_0`$.
    pub c: Rq,
    /// $`id_{i \to i} = \mathsf{Tag}(usk, s_i)`$.
    pub t0: LWRTag,
    /// $`\pi_0`$.
    pub proof: Proof,
}

impl RootRequest {
    /// The bytes of the encoding besides the Jali proof.
    pub const FIXED_BYTES: usize = Rq::BYTES + LWRTag::BYTES + LENGTH_BYTES;

    pub(super) fn write<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        self.c.check()?;
        self.c.serialize_compressed(&mut writer)?;
        self.t0.serialize_compressed(&mut writer)?;
        self.proof.write_bounded(&mut writer, ISSUE_PROOF_MAX_BYTES)
    }

    pub(super) fn read<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        Ok(Self {
            c: Rq::deserialize_compressed(&mut reader)?,
            t0: LWRTag::deserialize_compressed(&mut reader)?,
            proof: Proof::read_bounded(&mut reader, ISSUE_PROOF_MAX_BYTES)?,
        })
    }
}

impl CanonicalSerialize for RootRequest {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.write(writer)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::FIXED_BYTES + self.proof.len()
    }
}

impl Valid for RootRequest {
    fn check(&self) -> Result<(), SerializationError> {
        self.c.check()?;
        bounded(&self.proof, ISSUE_PROOF_MAX_BYTES)
    }
}

impl CanonicalDeserialize for RootRequest {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Self::read(reader)
    }
}

/// The issuance state $`st_{\mathsf{iss}} = (m_{\mathsf{hid}}, \phi, \rho) = ((usk, x_0), \phi, x_0)`$,
/// stored once as $`(usk, x_0, \phi)`$: "the issuance randomizer $`x_0`$ is simultaneously the
/// local issuance state and a certified hidden component" (bb:808). Secret: wiped on drop, not
/// `Clone`, redacted.
///
/// It can be stored until the helper answers ([`Self::to_bytes`], [`Self::from_bytes`]):
/// `usk ‖ x_{0,0} ‖ x_{0,1} ‖ φ`, [`Self::BYTES`] bytes, as secret as `usk`.
pub struct IssuanceState {
    pub(super) usk: Ternary,
    pub(super) x0: [Ternary; ELL_R],
    pub(super) phi: BinaryPoly,
}

impl IssuanceState {
    /// Bytes of the encoding: $`256 + 2 \cdot 256 + 128`$.
    pub const BYTES: usize = (1 + ELL_R) * Ternary::BYTES + BinaryPoly::BYTES;

    /// The encoding `usk ‖ x_{0,0} ‖ x_{0,1} ‖ φ`, in a buffer that is wiped on drop.
    ///
    /// # Errors
    /// [`Error::Serialization`] for a wiped state.
    pub fn to_bytes(&self) -> Result<Zeroizing<Vec<u8>>, Error> {
        // sized up front: the buffer never moves, so no unwiped copy is left behind
        let mut bytes = Zeroizing::new(Vec::with_capacity(Self::BYTES));
        self.usk.serialize_compressed(&mut *bytes)?;
        for x in &self.x0 {
            x.serialize_compressed(&mut *bytes)?;
        }
        self.phi.serialize_compressed(&mut *bytes)?;
        Ok(bytes)
    }

    /// Decodes [`Self::to_bytes`], canonically.
    ///
    /// # Errors
    /// [`Error::Serialization`] on malformed input; [`Error::TrailingBytes`] if `bytes`
    /// continues after the state.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut reader = bytes;
        let usk = Ternary::deserialize_compressed(&mut reader)?;
        let x0_0 = Ternary::deserialize_compressed(&mut reader)?;
        let x0_1 = Ternary::deserialize_compressed(&mut reader)?;
        let phi = BinaryPoly::deserialize_compressed(&mut reader)?;
        if !reader.is_empty() {
            return Err(Error::TrailingBytes);
        }
        Ok(Self {
            usk,
            x0: [x0_0, x0_1],
            phi,
        })
    }
}

impl Zeroize for IssuanceState {
    fn zeroize(&mut self) {
        self.usk.zeroize();
        self.x0.zeroize();
    }
}

/// Its secret parts wipe themselves on drop ($`\phi`$ is public).
impl ZeroizeOnDrop for IssuanceState {}

impl fmt::Debug for IssuanceState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("IssuanceState(<redacted>)")
    }
}

#[cfg(test)]
mod tests {
    use rand::{RngCore, SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        cred::vsis::VSISHiddenMessage,
        lattice::{D, Q},
        serialization::{from_bytes, to_bytes},
    };

    fn proof_of(len: usize, rng: &mut StdRng) -> Proof {
        let mut bytes = vec![0u8; len];
        rng.fill_bytes(&mut bytes);
        Proof::from_bytes(bytes).unwrap()
    }

    fn tag(rng: &mut StdRng) -> LWRTag {
        let mut bytes = [0u8; LWRTag::BYTES];
        rng.fill_bytes(&mut bytes);
        LWRTag::from_bytes(&bytes).unwrap()
    }

    fn rq(rng: &mut StdRng) -> Rq {
        let c: Vec<i64> = (0..D).map(|_| i64::from(rng.next_u32())).collect();
        Rq::from_i64(&c).unwrap()
    }

    fn attestation(len: usize, rng: &mut StdRng) -> Attestation {
        let mut phi = [0u8; BinaryPoly::BYTES];
        rng.fill_bytes(&mut phi);
        Attestation {
            tag: tag(rng),
            phi: BinaryPoly::from_bytes(phi),
            proof: proof_of(len, rng),
        }
    }

    #[test]
    fn proofs_carry_their_length_and_refuse_bad_ones() {
        let mut rng = StdRng::seed_from_u64(0x7c01);
        let proof = proof_of(1000, &mut rng);
        let bytes = to_bytes(&proof).unwrap();
        assert_eq!(bytes.len(), 1004);
        assert_eq!(&bytes[..4], &1000u32.to_le_bytes());
        assert_eq!(from_bytes::<Proof>(&bytes).unwrap(), proof);
        assert_eq!(proof.len(), 1000);
        assert_eq!(proof.encoded_size(), 1004);
        assert_eq!(format!("{proof:?}"), "Proof(1000 bytes)");
        // truncation, a longer length, trailing bytes
        assert!(from_bytes::<Proof>(&bytes[..1003]).is_err());
        let mut longer = bytes.clone();
        longer[..4].copy_from_slice(&1001u32.to_le_bytes());
        assert!(from_bytes::<Proof>(&longer).is_err());
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(from_bytes::<Proof>(&trailing), Err(Error::TrailingBytes));
        // a length above 16 MiB is refused before anything is read or allocated
        let mut forged = vec![0u8; 8];
        forged[..4].copy_from_slice(&(Proof::MAX_BYTES as u32 + 1).to_le_bytes());
        assert!(from_bytes::<Proof>(&forged).is_err());
        let mut at_limit = vec![0u8; 8];
        at_limit[..4].copy_from_slice(&(Proof::MAX_BYTES as u32).to_le_bytes());
        assert!(from_bytes::<Proof>(&at_limit).is_err()); // truncated, not refused for its size
        assert!(Proof::from_bytes(vec![0; Proof::MAX_BYTES + 1]).is_err());
        assert!(Proof::from_bytes(vec![0; Proof::MAX_BYTES]).is_ok());
    }

    /// The encodings of the module docs, with fake proofs of fixed lengths: the fixed overheads
    /// (468 per attestation, 2900 per proof or root request, 4 more for the canonical form of a
    /// proof), round trips, strictness.
    #[test]
    fn encodings_have_the_documented_layout() {
        let mut rng = StdRng::seed_from_u64(0x7c02);
        let att = attestation(83_150, &mut rng);
        let bytes = to_bytes(&att).unwrap();
        assert_eq!(Attestation::FIXED_BYTES, 468);
        assert_eq!(bytes.len(), 468 + 83_150);
        assert_eq!(&bytes[..LWRTag::BYTES], &att.tag.to_bytes()[..]);
        assert_eq!(&bytes[336..464], att.phi.as_bytes());
        assert_eq!(&bytes[464..468], &83_150u32.to_le_bytes());
        assert_eq!(from_bytes::<Attestation>(&bytes).unwrap(), att);

        let proof = IssuanceProof {
            attestations: (0..3).map(|i| attestation(83_100 + i, &mut rng)).collect(),
            c: rq(&mut rng),
            t0: tag(&mut rng),
            proof: proof_of(41_150, &mut rng),
        };
        let bytes = to_bytes(&proof).unwrap();
        assert_eq!(IssuanceProof::FIXED_BYTES, 2900);
        assert_eq!(
            bytes.len(),
            4 + 3 * 468 + 83_100 + 83_101 + 83_102 + 2900 + 41_150
        );
        assert_eq!(&bytes[..4], &3u32.to_le_bytes());
        assert_eq!(from_bytes::<IssuanceProof>(&bytes).unwrap(), proof);
        // a count that does not match the attestations that follow
        let mut wrong = bytes.clone();
        wrong[..4].copy_from_slice(&4u32.to_le_bytes());
        assert!(from_bytes::<IssuanceProof>(&wrong).is_err());
        wrong[..4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(from_bytes::<IssuanceProof>(&wrong).is_err());

        let request = RootRequest {
            c: rq(&mut rng),
            t0: tag(&mut rng),
            proof: proof_of(41_160, &mut rng),
        };
        let bytes = to_bytes(&request).unwrap();
        assert_eq!(bytes.len(), 2900 + 41_160);
        assert_eq!(&bytes[..Rq::BYTES], &request.c.to_bytes()[..]);
        assert_eq!(from_bytes::<RootRequest>(&bytes).unwrap(), request);
        // a coefficient of C equal to q is not canonical
        let mut bad = bytes.clone();
        bad[0] = (Q & 0xff) as u8;
        bad[1] = ((Q >> 8) & 0xff) as u8;
        bad[2] = (bad[2] & 0xf0) | ((Q >> 16) & 0x0f) as u8;
        assert!(from_bytes::<RootRequest>(&bad).is_err());
        // a wiped C has no encoding
        let mut wiped = request.clone();
        wiped.c.zeroize();
        assert!(to_bytes(&wiped).is_err());
    }

    /// Inside the protocol objects a proof is bounded by its parameter set (twice the estimate):
    /// the bound itself is accepted, one byte more is refused by the encoder, by `check` and by
    /// the decoder, which refuses the length before it reads the proof.
    #[test]
    fn proofs_inside_protocol_objects_are_bounded_by_their_sets() {
        let mut rng = StdRng::seed_from_u64(0x7c04);
        assert_eq!(
            (ATT_PROOF_MAX_BYTES, ISSUE_PROOF_MAX_BYTES),
            (171_216, 85_824)
        );
        let att = attestation(ATT_PROOF_MAX_BYTES, &mut rng);
        let bytes = to_bytes(&att).unwrap();
        assert_eq!(from_bytes::<Attestation>(&bytes).unwrap(), att);
        let long = attestation(ATT_PROOF_MAX_BYTES + 1, &mut rng);
        assert!(to_bytes(&long).is_err());
        assert!(long.check().is_err());
        // the same bytes with a forged length one above the bound, and the bytes present
        let mut forged = bytes.clone();
        forged[464..468].copy_from_slice(&(ATT_PROOF_MAX_BYTES as u32 + 1).to_le_bytes());
        forged.push(0);
        assert!(from_bytes::<Attestation>(&forged).is_err());
        // a forged length of 16 MiB on a short input: refused for its size
        let mut huge = bytes[..468].to_vec();
        huge[464..468].copy_from_slice(&(Proof::MAX_BYTES as u32).to_le_bytes());
        assert!(from_bytes::<Attestation>(&huge).is_err());

        let request = RootRequest {
            c: rq(&mut rng),
            t0: tag(&mut rng),
            proof: proof_of(ISSUE_PROOF_MAX_BYTES, &mut rng),
        };
        let bytes = to_bytes(&request).unwrap();
        assert_eq!(from_bytes::<RootRequest>(&bytes).unwrap(), request);
        let mut long = request.clone();
        long.proof = proof_of(ISSUE_PROOF_MAX_BYTES + 1, &mut rng);
        assert!(to_bytes(&long).is_err());
        assert!(long.check().is_err());
        let mut forged = bytes.clone();
        forged[2896..2900].copy_from_slice(&(ISSUE_PROOF_MAX_BYTES as u32 + 1).to_le_bytes());
        forged.push(0);
        assert!(from_bytes::<RootRequest>(&forged).is_err());

        let proof = IssuanceProof {
            attestations: vec![attestation(83_000, &mut rng)],
            c: rq(&mut rng),
            t0: tag(&mut rng),
            proof: proof_of(ISSUE_PROOF_MAX_BYTES, &mut rng),
        };
        assert!(to_bytes(&proof).is_ok());
        let mut long = proof.clone();
        long.proof = proof_of(ISSUE_PROOF_MAX_BYTES + 1, &mut rng);
        assert!(to_bytes(&long).is_err());
        assert!(long.check().is_err());
        let mut long = proof;
        long.attestations[0] = attestation(ATT_PROOF_MAX_BYTES + 1, &mut rng);
        assert!(to_bytes(&long).is_err());
        assert!(long.check().is_err());
    }

    #[test]
    fn secrets_have_fixed_sizes_and_are_redacted() {
        let mut rng = StdRng::seed_from_u64(0x7c03);
        let usk = UserSecretKey::from_ternary(Ternary::sample(&mut rng));
        assert_eq!(usk.to_bytes().unwrap().len(), UserSecretKey::BYTES);
        assert_eq!(UserSecretKey::BYTES, 256);
        assert_eq!(
            from_bytes::<UserSecretKey>(&usk.to_bytes().unwrap())
                .unwrap()
                .expose_ternary(),
            usk.expose_ternary()
        );
        assert_eq!(format!("{usk:?}"), "UserSecretKey(<redacted>)");
        let mut phi = [0u8; BinaryPoly::BYTES];
        rng.fill_bytes(&mut phi);
        let state = IssuanceState {
            usk: Ternary::sample(&mut rng),
            x0: [Ternary::sample(&mut rng), Ternary::sample(&mut rng)],
            phi: BinaryPoly::from_bytes(phi),
        };
        let bytes = state.to_bytes().unwrap();
        assert_eq!(bytes.len(), IssuanceState::BYTES);
        assert_eq!(IssuanceState::BYTES, 896);
        let back = IssuanceState::from_bytes(&bytes).unwrap();
        assert!(back.usk.ct_eq(&state.usk) && back.x0 == state.x0 && back.phi == state.phi);
        let mut longer = bytes.to_vec();
        longer.push(0);
        assert!(matches!(
            IssuanceState::from_bytes(&longer),
            Err(Error::TrailingBytes)
        ));
        assert!(IssuanceState::from_bytes(&bytes[..895]).is_err());
        // the ternary code 10 is not canonical
        let mut bad = bytes.to_vec();
        bad[300] = 0b0000_0010;
        assert!(IssuanceState::from_bytes(&bad).is_err());
        assert_eq!(format!("{state:?}"), "IssuanceState(<redacted>)");
        let mut wiped = state;
        wiped.zeroize();
        assert!(wiped.to_bytes().is_err());
        assert_eq!(Credential::BYTES, 5888);
    }

    /// `hsk` stored ahead of issuance: the count inside `sk` is advanced, every other byte is the
    /// plain encoding, and the in-memory count is unchanged.
    #[test]
    fn the_helper_key_can_be_stored_ahead_of_issuance() {
        let mut rng = StdRng::seed_from_u64(0x7c05);
        let pp = VSIS::setup(b"types").unwrap();
        let (vk, sk) = VSIS::keygen(&pp, &mut rng);
        let hsk = HelperSecretKey::<VSIS>::new(sk, vk, [7; 32]);
        let plain = hsk.to_bytes().unwrap();
        assert_eq!(plain.len(), 8489);
        assert_eq!(&hsk.to_bytes_reserving(0).unwrap()[..], &plain[..]);
        let ahead = hsk.to_bytes_reserving(1000).unwrap();
        assert_eq!(ahead.len(), plain.len());
        assert_eq!(&ahead[5889..5897], &1000u64.to_le_bytes());
        assert_eq!(&ahead[..5889], &plain[..5889]);
        assert_eq!(&ahead[5897..], &plain[5897..]);
        let back = from_bytes::<HelperSecretKey<VSIS>>(&ahead).unwrap();
        assert_eq!(back.signing_key().issued(), 1000);
        assert_eq!(back.verification_key(), hsk.verification_key());
        assert_eq!(back.parameters_digest(), &[7; 32]);
        assert_eq!(hsk.signing_key().issued(), 0);
        // worker threads share one in-memory key (docs/operating-a-helper.md)
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<HelperSecretKey<VSIS>>();
    }

    /// Credentials are equal iff both parts are.
    #[test]
    fn credentials_compare_all_their_parts() {
        let mut rng = StdRng::seed_from_u64(0x7c06);
        let pp = VSIS::setup(b"types").unwrap();
        let (_vk, sk) = VSIS::keygen(&pp, &mut rng);
        let x0 = [Ternary::sample(&mut rng), Ternary::sample(&mut rng)];
        let m_hid = VSISHiddenMessage::new(Ternary::sample(&mut rng), x0.clone());
        let m = VSIS::encode_message(&pp, &m_hid, &BinaryPoly::zero()).unwrap();
        let cred = Credential {
            cred: VSIS::sign(&pp, &sk, &m, &mut rng).unwrap(),
            x0: x0.clone(),
        };
        assert_eq!(cred, cred.clone());
        let other_x0 = Credential {
            cred: cred.cred.clone(),
            x0: [x0[0].clone(), Ternary::sample(&mut rng)],
        };
        assert_ne!(cred, other_x0);
        let other_cred = Credential {
            cred: VSIS::sign(&pp, &sk, &m, &mut rng).unwrap(),
            x0,
        };
        assert_ne!(cred, other_cred);
    }
}
