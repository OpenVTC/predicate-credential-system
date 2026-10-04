//! The fixed-format compact encoding of the lattice attestations, issuance proofs and root
//! requests (the paper's "parse π in a fixed format", §5.5), whose sizes the README reports:
//!
//! | object | bytes | size |
//! |---|---|---|
//! | `att_j` | $`id_{j \to i}`$ (336) ‖ $`\phi_j`$ (128) ‖ `LE32(len(π_j))` ‖ $`\pi_j`$ | $`468 + \lvert\pi_j\rvert`$ |
//! | `π` | $`att_1 \Vert \dots \Vert att_k`$ ‖ $`C`$ (2560) ‖ $`id_{i \to i}`$ (336) ‖ `LE32(len(π_0))` ‖ $`\pi_0`$, $`k`$ from the predicate | $`\sum_j \lvert att_j\rvert + 2900 + \lvert\pi_0\rvert`$ |
//! | root request | $`C`$ ‖ $`id_{i \to i}`$ ‖ `LE32(len(π_0))` ‖ $`\pi_0`$ | $`2900 + \lvert\pi_0\rvert`$ |
//!
//! The canonical encoding ([`super::types`]) is the same except that an issuance proof starts
//! with `LE32(k)`. Unlike the pairing codec ([`crate::pcs::codec`]), a length IS read from the
//! wire, the one of each Jali proof (at most [`Proof::MAX_BYTES`](super::Proof::MAX_BYTES)): Jali
//! proofs vary in length by tens of bytes with the proof seed. The number of attestations is
//! not read: it is the threshold of the predicate the verifier is about to check the proof for,
//! so a proof with $`k \pm 1`$ attestations does not decode for $`f_k`$.
//!
//! Every element is canonical by type and decoded strictly (no coefficient $`\ge q`$ in $`C`$,
//! every 336-byte string is a valid tag, every 128-byte string a binary $`\phi`$); trailing bytes
//! are rejected. At proof degree 128 the Jali proofs of this instantiation have about
//! 83.1 KB (`R_att`) and 41.1 KB (`R_issue`), so `|att| ≈ 83.6 KB` and `|π| ≈ 462 KB` at
//! $`k = 5`$; the README has the measured figures.

use ark_serialize::{Read, Write};

use super::types::{Attestation, IssuanceProof, RootRequest};
use crate::{error::Error, pcs::Predicate};

/// [`Error::TrailingBytes`] unless the input was consumed completely.
fn finish<V>(value: V, rest: &[u8]) -> Result<V, Error> {
    if rest.is_empty() {
        Ok(value)
    } else {
        Err(Error::TrailingBytes)
    }
}

impl Attestation {
    /// Size in bytes of the compact encoding: $`468 + |\pi_j|`$.
    #[must_use]
    pub fn compact_size(&self) -> usize {
        Self::FIXED_BYTES + self.proof.len()
    }

    /// Writes $`id_{j \to i} \| \phi_j \| \mathrm{LE32}(|\pi_j|) \| \pi_j`$.
    ///
    /// # Errors
    /// [`Error::Serialization`] if the writer fails.
    pub fn serialize_compact<W: Write>(&self, writer: W) -> Result<(), Error> {
        Ok(self.write(writer)?)
    }

    /// Reads one attestation and leaves the reader behind it.
    ///
    /// # Errors
    /// [`Error::Serialization`] on truncated input or a proof length above
    /// [`Proof::MAX_BYTES`](super::Proof::MAX_BYTES).
    pub fn deserialize_compact<R: Read>(reader: R) -> Result<Self, Error> {
        Ok(Self::read(reader)?)
    }

    /// The compact encoding.
    ///
    /// # Errors
    /// As [`Self::serialize_compact`].
    pub fn to_compact_bytes(&self) -> Result<Vec<u8>, Error> {
        let mut bytes = Vec::with_capacity(self.compact_size());
        self.serialize_compact(&mut bytes)?;
        Ok(bytes)
    }

    /// Decodes the compact encoding.
    ///
    /// # Errors
    /// As [`Self::deserialize_compact`]; [`Error::TrailingBytes`] if `bytes` continues after
    /// the attestation.
    pub fn from_compact_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut reader = bytes;
        let attestation = Self::deserialize_compact(&mut reader)?;
        finish(attestation, reader)
    }
}

impl IssuanceProof {
    /// Size in bytes of the compact encoding: $`\sum_j |att_j| + 2900 + |\pi_0|`$.
    #[must_use]
    pub fn compact_size(&self) -> usize {
        self.attestations
            .iter()
            .map(Attestation::compact_size)
            .sum::<usize>()
            + Self::FIXED_BYTES
            + self.proof.len()
    }

    /// Writes $`att_1 \| \dots \| att_k \| C \| id_{i \to i} \| \mathrm{LE32}(|\pi_0|) \| \pi_0`$.
    /// The number of attestations is not written: the decoder takes it from the predicate.
    ///
    /// # Errors
    /// [`Error::Serialization`] for a wiped $`C`$, or if the writer fails.
    pub fn serialize_compact<W: Write>(&self, writer: W) -> Result<(), Error> {
        Ok(self.write_compact(writer)?)
    }

    /// Reads a proof for the predicate `f`, i.e. with EXACTLY `f.threshold` attestations, and
    /// leaves the reader behind it.
    ///
    /// # Errors
    /// [`Error::ZeroThreshold`] for a root predicate (there is no issuance proof for it);
    /// [`Error::Serialization`] on truncated or non-canonical input.
    pub fn deserialize_compact<R: Read>(reader: R, f: &Predicate) -> Result<Self, Error> {
        if f.is_root() {
            return Err(Error::ZeroThreshold);
        }
        Ok(Self::read_compact(reader, f.threshold)?)
    }

    /// The compact encoding.
    ///
    /// # Errors
    /// As [`Self::serialize_compact`].
    pub fn to_compact_bytes(&self) -> Result<Vec<u8>, Error> {
        let mut bytes = Vec::with_capacity(self.compact_size());
        self.serialize_compact(&mut bytes)?;
        Ok(bytes)
    }

    /// Decodes the compact encoding of a proof for the predicate `f`.
    ///
    /// # Errors
    /// As [`Self::deserialize_compact`]; [`Error::TrailingBytes`] if `bytes` continues after
    /// the proof (in particular for a proof with more than `f.threshold` attestations).
    pub fn from_compact_bytes(bytes: &[u8], f: &Predicate) -> Result<Self, Error> {
        let mut reader = bytes;
        let proof = Self::deserialize_compact(&mut reader, f)?;
        finish(proof, reader)
    }
}

impl RootRequest {
    /// Size in bytes of the compact encoding: $`2900 + |\pi_0|`$.
    #[must_use]
    pub fn compact_size(&self) -> usize {
        Self::FIXED_BYTES + self.proof.len()
    }

    /// Writes $`C \| id_{i \to i} \| \mathrm{LE32}(|\pi_0|) \| \pi_0`$.
    ///
    /// # Errors
    /// [`Error::Serialization`] for a wiped $`C`$, or if the writer fails.
    pub fn serialize_compact<W: Write>(&self, writer: W) -> Result<(), Error> {
        Ok(self.write(writer)?)
    }

    /// Reads one root request and leaves the reader behind it.
    ///
    /// # Errors
    /// [`Error::Serialization`] on truncated or non-canonical input.
    pub fn deserialize_compact<R: Read>(reader: R) -> Result<Self, Error> {
        Ok(Self::read(reader)?)
    }

    /// The compact encoding.
    ///
    /// # Errors
    /// As [`Self::serialize_compact`].
    pub fn to_compact_bytes(&self) -> Result<Vec<u8>, Error> {
        let mut bytes = Vec::with_capacity(self.compact_size());
        self.serialize_compact(&mut bytes)?;
        Ok(bytes)
    }

    /// Decodes the compact encoding.
    ///
    /// # Errors
    /// As [`Self::deserialize_compact`]; [`Error::TrailingBytes`] if `bytes` continues after
    /// the request.
    pub fn from_compact_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut reader = bytes;
        let request = Self::deserialize_compact(&mut reader)?;
        finish(request, reader)
    }
}

#[cfg(test)]
mod tests {
    use rand::{RngCore, SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        kiprf::lwr::LWRTag,
        lattice::{BinaryPoly, D, Rq},
        pcs::lattice::types::Proof,
        serialization::WireFormat,
    };

    /// Jali proof lengths at proof degree 128 [measured by the validation flows: R_att
    /// 83,124-83,195 B, R_issue 41,139-41,171 B]: fake proofs of such lengths for the layout
    /// tests. The real proofs are in the integration tests.
    const ATT_PROOF: usize = 83_150;
    const ISSUE_PROOF: usize = 41_150;

    fn proof(len: usize, rng: &mut StdRng) -> Proof {
        let mut bytes = vec![0u8; len];
        rng.fill_bytes(&mut bytes);
        Proof::from_bytes(bytes).unwrap()
    }

    fn tag(rng: &mut StdRng) -> LWRTag {
        let mut bytes = [0u8; LWRTag::BYTES];
        rng.fill_bytes(&mut bytes);
        LWRTag::from_bytes(&bytes).unwrap()
    }

    fn attestation(rng: &mut StdRng) -> Attestation {
        let mut phi = [0u8; BinaryPoly::BYTES];
        rng.fill_bytes(&mut phi);
        Attestation {
            tag: tag(rng),
            phi: BinaryPoly::from_bytes(phi),
            proof: proof(ATT_PROOF + (rng.next_u32() % 40) as usize, rng),
        }
    }

    fn issuance_proof(k: usize, rng: &mut StdRng) -> IssuanceProof {
        let c: Vec<i64> = (0..D).map(|_| i64::from(rng.next_u32())).collect();
        IssuanceProof {
            attestations: (0..k).map(|_| attestation(rng)).collect(),
            c: Rq::from_i64(&c).unwrap(),
            t0: tag(rng),
            proof: proof(ISSUE_PROOF, rng),
        }
    }

    /// The sizes of the README row in THIS encoding, as for the pairing instantiations
    /// (`pcs::codec`, `compact_sizes_over_bls12_381`): the fixed overheads are exact, the Jali
    /// proofs vary with the seed.
    #[test]
    fn compact_sizes_of_the_lattice_row() {
        fn sizes(seed: u64) -> (usize, usize, usize, Vec<usize>, usize) {
            let mut rng = StdRng::seed_from_u64(seed);
            let proof = issuance_proof(5, &mut rng);
            let att = proof.attestations[0].clone();
            let request = RootRequest {
                c: proof.c.clone(),
                t0: proof.t0.clone(),
                proof: proof.proof.clone(),
            };
            let sizes = (
                att.to_compact_bytes().unwrap().len(),
                proof.to_compact_bytes().unwrap().len(),
                request.to_compact_bytes().unwrap().len(),
            );
            assert_eq!(
                sizes,
                (
                    att.compact_size(),
                    proof.compact_size(),
                    request.compact_size()
                )
            );
            // the canonical encoding of a proof is 4 bytes longer (its count); the other two are
            // the compact encoding
            assert_eq!(proof.to_bytes().unwrap().len(), sizes.1 + 4);
            assert_eq!(att.to_bytes().unwrap().len(), sizes.0);
            assert_eq!(request.to_bytes().unwrap().len(), sizes.2);
            let jali: Vec<usize> = proof.attestations.iter().map(|a| a.proof.len()).collect();
            (sizes.0, sizes.1, sizes.2, jali, proof.proof.len())
        }
        let (att, pi, root, jali, pi0) = sizes(0x7c0d_e001);
        assert_eq!(att - jali[0], 468);
        assert_eq!(pi - jali.iter().sum::<usize>() - 5 * 468 - pi0, 2900);
        assert_eq!(root - pi0, 2900);
        assert_eq!(
            (
                Attestation::FIXED_BYTES,
                IssuanceProof::FIXED_BYTES,
                RootRequest::FIXED_BYTES
            ),
            (468, 2900, 2900)
        );
    }

    fn is_serialization_error<V>(result: Result<V, Error>) -> bool {
        matches!(result, Err(Error::Serialization(_)))
    }

    /// Round trips, and the strictness of the decoder: truncation, trailing bytes, a forged proof
    /// length, and a number of attestations that is taken from the predicate and from nowhere
    /// else.
    #[test]
    fn round_trips_and_strict_decoding() {
        let mut rng = StdRng::seed_from_u64(0x7c0d_e002);
        let f = |k: u32| Predicate::new(k, b"f".to_vec());
        let att = attestation(&mut rng);
        let bytes = att.to_compact_bytes().unwrap();
        assert_eq!(Attestation::from_compact_bytes(&bytes).unwrap(), att);
        for cut in [0, 1, 335, 336, 464, 467, 468, bytes.len() - 1] {
            assert!(is_serialization_error(Attestation::from_compact_bytes(
                &bytes[..cut]
            )));
        }
        let mut longer = bytes.clone();
        longer.push(0);
        assert_eq!(
            Attestation::from_compact_bytes(&longer),
            Err(Error::TrailingBytes)
        );
        // the streaming decoder leaves the reader right behind the attestation
        let mut reader = &longer[..];
        assert_eq!(Attestation::deserialize_compact(&mut reader).unwrap(), att);
        assert_eq!(reader, &[0]);
        // a forged length above 16 MiB, and one that runs past the end
        let mut forged = bytes.clone();
        forged[464..468].copy_from_slice(&(Proof::MAX_BYTES as u32 + 1).to_le_bytes());
        assert!(is_serialization_error(Attestation::from_compact_bytes(
            &forged
        )));
        forged[464..468].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(is_serialization_error(Attestation::from_compact_bytes(
            &forged
        )));
        forged[464..468].copy_from_slice(&((ATT_PROOF + 100) as u32).to_le_bytes());
        assert!(is_serialization_error(Attestation::from_compact_bytes(
            &forged
        )));

        for k in [1usize, 2, 5] {
            let proof = issuance_proof(k, &mut rng);
            let bytes = proof.to_compact_bytes().unwrap();
            let k32 = u32::try_from(k).unwrap();
            assert_eq!(
                IssuanceProof::from_compact_bytes(&bytes, &f(k32)).unwrap(),
                proof
            );
            // the label of the predicate plays no role for the FORMAT
            assert!(
                IssuanceProof::from_compact_bytes(&bytes, &Predicate::new(k32, b"g".to_vec()))
                    .is_ok()
            );
            // k + 1: truncated (or garbage where an attestation was expected); k − 1: trailing
            // bytes, or garbage where C was expected
            assert!(IssuanceProof::from_compact_bytes(&bytes, &f(k32 + 1)).is_err());
            if k > 1 {
                assert!(IssuanceProof::from_compact_bytes(&bytes, &f(k32 - 1)).is_err());
            }
            assert_eq!(
                IssuanceProof::from_compact_bytes(&bytes, &f(0)),
                Err(Error::ZeroThreshold)
            );
            assert!(is_serialization_error(IssuanceProof::from_compact_bytes(
                &bytes[..bytes.len() - 1],
                &f(k32)
            )));
            let mut longer = bytes.clone();
            longer.push(0);
            assert_eq!(
                IssuanceProof::from_compact_bytes(&longer, &f(k32)),
                Err(Error::TrailingBytes)
            );
            // the canonical encoding round-trips through the blanket wire format
            assert_eq!(
                IssuanceProof::from_bytes(&proof.to_bytes().unwrap()).unwrap(),
                proof
            );
        }

        let request = RootRequest {
            c: Rq::from_i64(&[3; D]).unwrap(),
            t0: tag(&mut rng),
            proof: proof(ISSUE_PROOF, &mut rng),
        };
        let bytes = request.to_compact_bytes().unwrap();
        assert_eq!(RootRequest::from_compact_bytes(&bytes).unwrap(), request);
        assert!(is_serialization_error(RootRequest::from_compact_bytes(
            &bytes[..bytes.len() - 1]
        )));
        let mut longer = bytes;
        longer.push(7);
        assert_eq!(
            RootRequest::from_compact_bytes(&longer),
            Err(Error::TrailingBytes)
        );
    }

    /// The predicate's threshold is attacker-independent but may be large: decoding fails on the
    /// first missing byte and does not allocate for `f.threshold` attestations up front.
    #[test]
    fn a_huge_threshold_fails_fast() {
        let mut rng = StdRng::seed_from_u64(0x7c0d_e003);
        let bytes = issuance_proof(2, &mut rng).to_compact_bytes().unwrap();
        let huge = Predicate::new(u32::MAX, b"f".to_vec());
        assert!(is_serialization_error(IssuanceProof::from_compact_bytes(
            &bytes, &huge
        )));
        assert!(is_serialization_error(IssuanceProof::from_compact_bytes(
            &[],
            &huge
        )));
    }
}
