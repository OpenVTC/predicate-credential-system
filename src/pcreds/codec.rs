//! The fixed-format compact encoding of the messages of `Π_PCreds`: the encoding whose sizes are
//! those of the paper's size table (§7.1, `tab:sizes`).
//!
//! | object | bytes |
//! |---|---|
//! | [`AttestationRequest`] | `id_Q ‖ π_id` |
//! | [`Attestation`] | `t ‖ σ* ‖ π_att` |
//! | [`CredentialRequest`] | `id_Q ‖ n ‖ att_1 ‖ … ‖ att_n ‖ Ĉ ‖ π_iss`, `n` a 4-byte little-endian count |
//! | [`MembershipProof`] | `σ* ‖ π_prove` |
//! | [`Reply`] | one byte (`0` Fail, `1` issued, `2` pre-credential), then `σ̂` |
//!
//! Every element is in the compressed canonical encoding of arkworks and is decoded WITH
//! validation ([`crate::serialization`]); trailing bytes are rejected. A proof is written in the
//! fixed format of its kind ([`Backend::serialize_proof_compact`]): the number of its responses
//! is a constant of the instantiation, never a number taken from the wire.
//!
//! The one length on the wire is the number `n` of attestations of a credential request, which
//! the requester chooses (protocol box: "every tag in `N'` names a stored attestation"). The
//! decoder never allocates ahead of the input: every attestation consumes input, so the vector
//! never outgrows it. A helper may also limit the number it verifies
//! ([`Policy::with_max_attestations`](super::Policy::with_max_attestations)).
//!
//! Over BLS12-381 (`G_1`: 48 B, `G_2`: 96 B, `Z_p`: 32 B) this gives `|att| = 240 / 448` B and
//! `|π| = 1344 / 2384` B at `k = 5` for `Σ-PS` / `Σ-BBS`, where `|π|`
//! ([`CredentialRequest::size`]) counts the `k` attestations, `Ĉ` and `π_iss` as in the paper;
//! the wire format adds `id_Q` and the count. The DERIVED canonical encoding of the same objects
//! is self-describing (it length-prefixes the responses and the attestations); tests say which
//! of the two they measure.

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, Write};

use super::{
    backend::{Backend, ProofKind},
    types::{Attestation, AttestationRequest, CredentialRequest, MembershipProof, Reply},
};
use crate::error::Error;

/// [`Error::TrailingBytes`] unless the input was consumed completely.
fn finish<V>(value: V, rest: &[u8]) -> Result<V, Error> {
    if rest.is_empty() {
        Ok(value)
    } else {
        Err(Error::TrailingBytes)
    }
}

/// The compact encoding of `value`, written by `write` into a buffer of `size` bytes.
fn to_compact<V>(
    value: &V,
    size: usize,
    write: impl FnOnce(&V, &mut Vec<u8>) -> Result<(), Error>,
) -> Result<Vec<u8>, Error> {
    let mut bytes = Vec::with_capacity(size);
    write(value, &mut bytes)?;
    Ok(bytes)
}

impl<Bk: Backend> AttestationRequest<Bk> {
    /// Size in bytes of the compact encoding.
    #[must_use]
    pub fn compact_size(&self) -> usize {
        self.id.compressed_size() + Bk::proof_compact_size(&self.proof)
    }

    /// Writes `id_Q ‖ π_id`.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] if `π_id` does not have the fixed format;
    /// [`Error::Serialization`] if the writer fails.
    pub fn serialize_compact<W: Write>(&self, mut writer: W) -> Result<(), Error> {
        self.id.serialize_compressed(&mut writer)?;
        Bk::serialize_proof_compact(ProofKind::Identifier, &self.proof, writer)
    }

    /// Reads one attestation request, with validation, and leaves the reader behind it.
    ///
    /// # Errors
    /// [`Error::Serialization`] on truncated, malformed or non-canonical input.
    pub fn deserialize_compact<R: Read>(mut reader: R) -> Result<Self, Error> {
        Ok(Self {
            id: Bk::Tag::deserialize_compressed(&mut reader)?,
            proof: Bk::deserialize_proof_compact(ProofKind::Identifier, reader)?,
        })
    }

    /// The compact encoding.
    ///
    /// # Errors
    /// As [`Self::serialize_compact`].
    pub fn to_compact_bytes(&self) -> Result<Vec<u8>, Error> {
        to_compact(self, self.compact_size(), |v, w| v.serialize_compact(w))
    }

    /// Decodes the compact encoding, with validation.
    ///
    /// # Errors
    /// As [`Self::deserialize_compact`]; [`Error::TrailingBytes`] if `bytes` continues after
    /// the request.
    pub fn from_compact_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut reader = bytes;
        let value = Self::deserialize_compact(&mut reader)?;
        finish(value, reader)
    }
}

impl<Bk: Backend> Attestation<Bk> {
    /// Size in bytes of the compact encoding: `t`, `σ*` and `π_att` (the `|att|` of the paper's
    /// size table).
    #[must_use]
    pub fn size(&self) -> usize {
        self.tag.compressed_size()
            + self.show.compressed_size()
            + Bk::proof_compact_size(&self.proof)
    }

    /// Writes `t ‖ σ* ‖ π_att`.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] if `π_att` does not have the fixed format;
    /// [`Error::Serialization`] if the writer fails.
    pub fn serialize_compact<W: Write>(&self, mut writer: W) -> Result<(), Error> {
        self.tag.serialize_compressed(&mut writer)?;
        self.show.serialize_compressed(&mut writer)?;
        Bk::serialize_proof_compact(ProofKind::Attestation, &self.proof, writer)
    }

    /// Reads one attestation, with validation, and leaves the reader behind it.
    ///
    /// # Errors
    /// [`Error::Serialization`] on truncated, malformed or non-canonical input.
    pub fn deserialize_compact<R: Read>(mut reader: R) -> Result<Self, Error> {
        Ok(Self {
            tag: Bk::Tag::deserialize_compressed(&mut reader)?,
            show: Bk::Show::deserialize_compressed(&mut reader)?,
            proof: Bk::deserialize_proof_compact(ProofKind::Attestation, reader)?,
        })
    }

    /// The compact encoding.
    ///
    /// # Errors
    /// As [`Self::serialize_compact`].
    pub fn to_compact_bytes(&self) -> Result<Vec<u8>, Error> {
        to_compact(self, self.size(), |v, w| v.serialize_compact(w))
    }

    /// Decodes the compact encoding, with validation.
    ///
    /// # Errors
    /// As [`Self::deserialize_compact`]; [`Error::TrailingBytes`] if `bytes` continues after
    /// the attestation.
    pub fn from_compact_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut reader = bytes;
        let value = Self::deserialize_compact(&mut reader)?;
        finish(value, reader)
    }
}

impl<Bk: Backend> CredentialRequest<Bk> {
    /// Size in bytes of the attestations, the request `Ĉ` and `π_iss`: the `|π|` of the paper's
    /// size table (`id_Q` and the count are not counted).
    #[must_use]
    pub fn size(&self) -> usize {
        self.attestations
            .iter()
            .map(Attestation::size)
            .sum::<usize>()
            + self.request.compressed_size()
            + Bk::proof_compact_size(&self.proof)
    }

    /// Size in bytes of the compact encoding: [`Self::size`], `id_Q` and the 4-byte count.
    #[must_use]
    pub fn compact_size(&self) -> usize {
        self.id.compressed_size() + 4 + self.size()
    }

    /// Writes `id_Q ‖ n ‖ att_1 ‖ … ‖ att_n ‖ Ĉ ‖ π_iss`.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] for more than `u32::MAX` attestations or a proof that does not
    /// have the fixed format; [`Error::Serialization`] if the writer fails.
    pub fn serialize_compact<W: Write>(&self, mut writer: W) -> Result<(), Error> {
        let count = u32::try_from(self.attestations.len()).map_err(|_| Error::LengthMismatch {
            expected: u32::MAX as usize,
            actual: self.attestations.len(),
        })?;
        self.id.serialize_compressed(&mut writer)?;
        writer
            .write_all(&count.to_le_bytes())
            .map_err(|e| Error::Serialization(e.to_string()))?;
        for attestation in &self.attestations {
            attestation.serialize_compact(&mut writer)?;
        }
        self.request.serialize_compressed(&mut writer)?;
        Bk::serialize_proof_compact(ProofKind::Issuance, &self.proof, writer)
    }

    /// Reads one credential request, with validation, and leaves the reader behind it.
    ///
    /// # Errors
    /// [`Error::Serialization`] on truncated, malformed or non-canonical input.
    pub fn deserialize_compact<R: Read>(mut reader: R) -> Result<Self, Error> {
        let id = Bk::Tag::deserialize_compressed(&mut reader)?;
        let mut count = [0u8; 4];
        reader
            .read_exact(&mut count)
            .map_err(|e| Error::Serialization(e.to_string()))?;
        // Not `with_capacity(count)`: the count comes from the wire. Every attestation consumes
        // input, so the vector never outgrows the input.
        let mut attestations = Vec::new();
        for _ in 0..u32::from_le_bytes(count) {
            attestations.push(Attestation::deserialize_compact(&mut reader)?);
        }
        Ok(Self {
            id,
            attestations,
            request: Bk::Request::deserialize_compressed(&mut reader)?,
            proof: Bk::deserialize_proof_compact(ProofKind::Issuance, reader)?,
        })
    }

    /// The compact encoding.
    ///
    /// # Errors
    /// As [`Self::serialize_compact`].
    pub fn to_compact_bytes(&self) -> Result<Vec<u8>, Error> {
        to_compact(self, self.compact_size(), |v, w| v.serialize_compact(w))
    }

    /// Decodes the compact encoding, with validation.
    ///
    /// # Errors
    /// As [`Self::deserialize_compact`]; [`Error::TrailingBytes`] if `bytes` continues after
    /// the request.
    pub fn from_compact_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut reader = bytes;
        let value = Self::deserialize_compact(&mut reader)?;
        finish(value, reader)
    }
}

impl<Bk: Backend> MembershipProof<Bk> {
    /// Size in bytes of the compact encoding: `σ*` and `π_prove`.
    #[must_use]
    pub fn size(&self) -> usize {
        self.show.compressed_size() + Bk::proof_compact_size(&self.proof)
    }

    /// Writes `σ* ‖ π_prove`.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] if `π_prove` does not have the fixed format;
    /// [`Error::Serialization`] if the writer fails.
    pub fn serialize_compact<W: Write>(&self, mut writer: W) -> Result<(), Error> {
        self.show.serialize_compressed(&mut writer)?;
        Bk::serialize_proof_compact(ProofKind::Possession, &self.proof, writer)
    }

    /// Reads one membership proof, with validation, and leaves the reader behind it.
    ///
    /// # Errors
    /// [`Error::Serialization`] on truncated, malformed or non-canonical input.
    pub fn deserialize_compact<R: Read>(mut reader: R) -> Result<Self, Error> {
        Ok(Self {
            show: Bk::Show::deserialize_compressed(&mut reader)?,
            proof: Bk::deserialize_proof_compact(ProofKind::Possession, reader)?,
        })
    }

    /// The compact encoding.
    ///
    /// # Errors
    /// As [`Self::serialize_compact`].
    pub fn to_compact_bytes(&self) -> Result<Vec<u8>, Error> {
        to_compact(self, self.size(), |v, w| v.serialize_compact(w))
    }

    /// Decodes the compact encoding, with validation.
    ///
    /// # Errors
    /// As [`Self::deserialize_compact`]; [`Error::TrailingBytes`] if `bytes` continues after
    /// the proof.
    pub fn from_compact_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut reader = bytes;
        let value = Self::deserialize_compact(&mut reader)?;
        finish(value, reader)
    }
}

impl<Bk: Backend> Reply<Bk> {
    /// Size in bytes of the compact encoding: one byte, and `σ̂` if present.
    #[must_use]
    pub fn compact_size(&self) -> usize {
        self.compressed_size()
    }

    /// The compact encoding (the canonical one: one byte, then `σ̂`).
    ///
    /// # Errors
    /// [`Error::Serialization`] if `σ̂` cannot be serialized.
    pub fn to_compact_bytes(&self) -> Result<Vec<u8>, Error> {
        crate::serialization::to_bytes(self)
    }

    /// Decodes the compact encoding, with validation.
    ///
    /// # Errors
    /// [`Error::Serialization`] on malformed input or an unknown tag byte;
    /// [`Error::TrailingBytes`] if `bytes` continues after the reply.
    pub fn from_compact_bytes(bytes: &[u8]) -> Result<Self, Error> {
        crate::serialization::from_bytes(bytes)
    }
}
