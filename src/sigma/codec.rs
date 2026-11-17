//! The byte encodings of the Fiat–Shamir transform: how counts, scalars and group elements are
//! written into the serialized instance, the serialized commitment and the NARG string
//! (`draft-irtf-cfrg-sigma-protocols-04`, "Sigma -04" below, and
//! `draft-irtf-cfrg-fiat-shamir-04`, "FS -04").
//!
//! | value | bytes | source |
//! |---|---|---|
//! | a count or an index `n` | `LE(n, 4)`: four bytes, little-endian, refused for `n ≥ 2^32` | Sigma -04 §3.6 |
//! | a scalar `s ∈ Z_p` | `I2OSP(s, N_s)`: `N_s` bytes, big-endian (`N_s = 32` for BLS12-381), decoded from exactly `N_s` bytes and refused for `s ≥ p` | Sigma -04 §8.2.2 |
//! | a group element | its compressed arkworks encoding, decoded with full validation | see below |
//!
//! The group encodings, per group of BLS12-381:
//!
//! * `G_1`: the compressed 48-byte encoding of `draft-irtf-cfrg-pairing-friendly-curves-15`,
//!   §5.3 and §5.4, with vectors in its Appendix D.1 (the ZCash format: the x-coordinate
//!   big-endian, with the compression, infinity and sign flags in the three top bits of the first
//!   byte, the identity as `0xc0` and 47 zero bytes), which is `serialize` of Sigma -04 §8.2.1
//!   (`N_e = 48`). arkworks writes exactly these bytes, and its validated decoding refuses a
//!   cleared compression flag, an x-coordinate `≥ q`, a point off the curve and a point outside
//!   `G_1`. `tests/ietf_vectors.rs` runs the Sigma draft's adversarial vectors for each of these.
//! * `G_2`: the compressed 96-byte encoding of the same sections (`x = x_0 + x_1 u` as
//!   `x_1 ‖ x_0`, each big-endian, flags in the first byte). This crate's extension uses it. The
//!   Sigma draft does not define a ciphersuite over `G_2`.
//! * `G_T`: an element of the subgroup of order `p` of `F_{q^12}^*` as `SerializeField(a, q, 12)`,
//!   the default field serialization of FS -04 Appendix A.2.4: its 12 coordinates over `F_q`,
//!   each `LE(a_i, 48)`, in the order of arkworks' tower basis (`F_{q^2} = F_q[u]/(u² + 1)`,
//!   `F_{q^6} = F_{q^2}[v]/(v³ − (u + 1))`, `F_{q^12} = F_{q^6}[w]/(w² − v)`, coordinates
//!   `c0.c0.c0, c0.c0.c1, c0.c1.c0, …, c1.c2.c1`), 576 bytes. arkworks writes exactly these bytes
//!   (a unit test compares them with the coordinates). Only this crate's extension uses it.
//!
//! Over a group of another curve (tests run BN254) the encoding is the compressed arkworks
//! encoding of that group, and the ciphersuite identifier says so (`crate::sigma::ciphersuite`).

use ark_ff::{BigInteger, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::{error::Error, hash::duplex_sponge::ns};

/// `N_s`: the length of a serialized scalar of `F` (32 for the scalar field of BLS12-381).
#[must_use]
pub fn scalar_len<F: PrimeField>() -> usize {
    ns::<F>()
}

/// Appends `I2OSP(s, N_s)`, the big-endian encoding of the canonical representative of `s`
/// (Sigma -04 §8.2.2, `serialize`).
pub fn write_scalar<F: PrimeField>(out: &mut Vec<u8>, scalar: &F) {
    let be = scalar.into_bigint().to_bytes_be();
    let n = scalar_len::<F>();
    // `s < p < 256^{N_s}`: the bytes in front of the last `N_s` are zero
    debug_assert!(be[..be.len() - n].iter().all(|b| *b == 0));
    out.extend_from_slice(&be[be.len() - n..]);
}

/// `I2OSP(s, N_s)` as a vector.
#[must_use]
pub fn scalar_to_bytes<F: PrimeField>(scalar: &F) -> Vec<u8> {
    let mut out = Vec::with_capacity(scalar_len::<F>());
    write_scalar(&mut out, scalar);
    out
}

/// `deserialize` of Sigma -04 §8.2.2 for exactly `N_s` bytes: `OS2IP(bytes)`, and `None` unless
/// the length is `N_s` and the value is below `p`. One scalar has one encoding.
#[must_use]
pub fn scalar_from_bytes<F: PrimeField>(bytes: &[u8]) -> Option<F> {
    if bytes.len() != scalar_len::<F>() {
        return None;
    }
    let value = F::from_be_bytes_mod_order(bytes);
    // canonical iff re-encoding the reduced value gives the input back
    (scalar_to_bytes(&value) == bytes).then_some(value)
}

/// Reads the next scalar (`N_s` bytes, strict) from the front of `input`.
pub(crate) fn read_scalar<F: PrimeField>(input: &mut &[u8]) -> Option<F> {
    let n = scalar_len::<F>();
    if input.len() < n {
        return None;
    }
    let (head, rest) = input.split_at(n);
    let value = scalar_from_bytes(head)?;
    *input = rest;
    Some(value)
}

/// Appends `LE(n, 4)` (Sigma -04 §3.6).
///
/// # Errors
/// [`Error::InvalidInstance`] for `n ≥ 2^32`, which no valid instance has (§3.5, check 1).
pub(crate) fn write_count(out: &mut Vec<u8>, n: usize) -> Result<(), Error> {
    let n =
        u32::try_from(n).map_err(|_| Error::InvalidInstance("a count or index of 2^32 or more"))?;
    out.extend_from_slice(&n.to_le_bytes());
    Ok(())
}

/// Reads `LE(n, 4)` from the front of `input`.
pub(crate) fn read_count(input: &mut &[u8]) -> Option<usize> {
    let (head, rest) = input.split_first_chunk::<4>()?;
    *input = rest;
    usize::try_from(u32::from_le_bytes(*head)).ok()
}

/// `N_e`: the length of the encoding of an element of `G` (48, 96 and 576 for `G_1`, `G_2` and
/// `G_T` of BLS12-381). Every element of an arkworks group has an encoding of this length.
#[must_use]
pub fn element_len<G: CanonicalSerialize + Zero>() -> usize {
    G::zero().compressed_size()
}

/// Appends the encoding of a group element (module docs).
///
/// # Errors
/// [`Error::Serialization`] if arkworks refuses to encode it (it does not for points of its
/// groups).
pub(crate) fn write_element<G: CanonicalSerialize>(
    out: &mut Vec<u8>,
    element: &G,
) -> Result<(), Error> {
    element.serialize_compressed(&mut *out)?;
    Ok(())
}

/// Decodes exactly one group element from `bytes`, with full validation (on the curve, in the
/// prime-order subgroup, canonical), and refuses bytes left over.
///
/// # Errors
/// [`Error::Serialization`] for an invalid encoding, [`Error::TrailingBytes`] for leftovers.
pub(crate) fn element_from_bytes<G: CanonicalDeserialize>(bytes: &[u8]) -> Result<G, Error> {
    crate::serialization::from_bytes(bytes)
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
    use ark_ec::{
        PrimeGroup,
        pairing::{Pairing, PairingOutput},
    };
    use ark_ff::{Field, One};

    use super::*;

    /// `G_T` elements are written as `SerializeField(a, q, 12)` of FS -04 Appendix A.2.4: the 12
    /// coordinates in arkworks' tower basis, each `LE(a_i, 48)`.
    #[test]
    fn gt_elements_are_the_default_field_serialization_of_their_coordinates() {
        let gt = Bls12_381::pairing(
            G1Projective::generator() * Fr::from(3u64),
            G2Projective::generator() * Fr::from(5u64),
        );
        let mut ours = Vec::new();
        write_element(&mut ours, &gt).unwrap();
        let mut by_coordinates = Vec::new();
        let mut count = 0;
        for coordinate in gt.0.to_base_prime_field_elements() {
            let le = coordinate.into_bigint().to_bytes_le();
            assert_eq!(le.len(), 48);
            by_coordinates.extend_from_slice(&le);
            count += 1;
        }
        assert_eq!(count, 12);
        assert_eq!(ours, by_coordinates);
        assert_eq!(ours.len(), 576);
        assert_eq!(element_len::<PairingOutput<Bls12_381>>(), 576);
        // the identity is the field element 1: the first coordinate 1, the others 0
        let mut identity = Vec::new();
        write_element(&mut identity, &PairingOutput::<Bls12_381>::zero()).unwrap();
        assert!(identity[0] == 1 && identity[1..].iter().all(|b| *b == 0));
        assert!(PairingOutput::<Bls12_381>::zero().0.is_one());
    }

    #[test]
    fn element_lengths_of_bls12_381() {
        assert_eq!(element_len::<G1Projective>(), 48);
        assert_eq!(element_len::<G2Projective>(), 96);
    }

    #[test]
    fn scalars_are_big_endian_and_strict() {
        let x = Fr::from(0x0102_0304u64);
        let bytes = scalar_to_bytes(&x);
        assert_eq!(bytes.len(), 32);
        assert_eq!(bytes[28..], [1, 2, 3, 4]);
        assert!(bytes[..28].iter().all(|b| *b == 0));
        assert_eq!(scalar_from_bytes::<Fr>(&bytes), Some(x));
        // p − 1 is the largest canonical value, p and 2^256 − 1 are refused
        let largest = scalar_to_bytes(&-Fr::one());
        assert_eq!(scalar_from_bytes::<Fr>(&largest), Some(-Fr::one()));
        let p = Fr::MODULUS.to_bytes_be();
        assert_eq!(scalar_from_bytes::<Fr>(&p), None);
        assert_eq!(scalar_from_bytes::<Fr>(&[0xff; 32]), None);
        // exactly N_s bytes
        assert_eq!(scalar_from_bytes::<Fr>(&bytes[1..]), None);
        assert_eq!(
            scalar_from_bytes::<Fr>(&[bytes.clone(), vec![0]].concat()),
            None
        );
        let mut input = &[bytes.clone(), vec![7]].concat()[..];
        assert_eq!(read_scalar::<Fr>(&mut input), Some(x));
        assert_eq!(input, [7]);
    }

    #[test]
    fn counts_are_four_bytes_little_endian() {
        let mut out = Vec::new();
        write_count(&mut out, 0x0102_0304).unwrap();
        assert_eq!(out, [4, 3, 2, 1]);
        assert_eq!(
            write_count(&mut out, 1 << 32),
            Err(Error::InvalidInstance("a count or index of 2^32 or more"))
        );
        let mut input = &[4u8, 3, 2, 1, 9][..];
        assert_eq!(read_count(&mut input), Some(0x0102_0304));
        assert_eq!(input, [9]);
        assert_eq!(read_count(&mut &[1u8, 2, 3][..]), None);
    }
}
