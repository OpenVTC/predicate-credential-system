//! The ring elements of the lattice instantiation, shared by [`VSIS`](crate::cred::VSIS),
//! [`LWR`](crate::kiprf::LWR) and the construction: elements of $`R_q`$ ([`Rq`]), short
//! polynomials with coefficients in $`\{-1, 0, 1\}`$ ([`Ternary`]) and binary polynomials
//! ([`BinaryPoly`]), with their canonical fixed-length encodings.
//!
//! | type | paper | encoding (bytes) |
//! |---|---|---|
//! | [`Rq`] | $`v, b_u, b_\phi, B_r, h, C, t \in R_q`$ | 20-bit little-endian packing of the canonical coefficients in $`[0, q)`$ (2560) |
//! | [`Ternary`] | `usk`, the components of $`x_0`$, $`x_1`$ | 2-bit two's complement per coefficient, little-endian packing; the code `10` ($`-2`$) is rejected (256) |
//! | [`BinaryPoly`] | $`\phi = \mathsf{EncPred}(f) \in \mathcal M_{\mathsf{pub}}`$ | bit $`i`$ = coefficient $`i`$, least significant bit first (128) |
//!
//! Every byte string of the right length that decodes is the unique encoding of its value, and
//! the decoders check this whatever `Validate` flag they are given: canonicity is an invariant of
//! the types, not a property of how a value was obtained. In particular a non-binary $`\phi`$
//! (the credential-free forgery of the proof of lem:base-vsis) and a coefficient of $`C`$ or $`h`$
//! outside $`[0, q)`$ cannot be represented at all.
//!
//! Signed integers of other widths (the preimage $`s`$ of `Σ-vSIS`, 20 bits) use the same
//! two's-complement packing (`pack_signed`, `unpack_signed`, crate-internal).

use core::fmt;

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::rand::{CryptoRng, RngCore};
use ntru_trapdoor::{Params, RqPoly};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use super::{D, Q};
use crate::error::Error;

/// `ntru-trapdoor`'s parameter set: the ring $`R_q`$ and the trapdoor of `Σ-vSIS`.
pub(crate) const NTRU: Params = Params::PCS;

/// `ntru-trapdoor` checks the ring of its parameter set in every constructor (`1 ≤ logn ≤ 10`,
/// `3 ≤ q < 2^25`). [`NTRU`] passes those checks (the unit tests run them), so for it they
/// cannot fail.
fn in_pcs_ring<T>(result: Result<T, ntru_trapdoor::Error>) -> T {
    match result {
        Ok(value) => value,
        Err(error) => unreachable!("ntru-trapdoor refused the PCS ring: {error}"),
    }
}

// ---------------------------------------------------------------------------------------------
// R_q
// ---------------------------------------------------------------------------------------------

/// An element of $`R_q = \mathbb Z_q[X]/(X^{1024} + 1)`$, $`q = 1{,}048{,}573`$, with canonical
/// coefficients in $`[0, q)`$ (coefficient $`i`$ of $`X^i`$ at index $`i`$).
///
/// Arithmetic is `ntru-trapdoor`'s: exact products by a two-prime NTT (about 28 µs; 19 µs with a
/// prepared operand), inversion and the unit test by the norm tower (about 58 µs and 30 µs), all
/// with masks instead of branches; only the `None` of [`Rq::inverse`] depends on the value.
///
/// Not wiped on drop (most elements are public); wrap a secret one (`usk` as a ring element, a
/// target $`t`$) in [`Zeroizing`]. `Debug` prints neither coefficients nor a digest.
///
/// A WIPED element (`Zeroize` empties it) is no element of $`R_q`$: it has an empty encoding,
/// [`Valid::check`] refuses it, and the arithmetic panics on it (the `# Panics` sections). Every
/// value that this crate makes or decodes has its $`d`$ coefficients, and the algorithms of the
/// crate refuse a wiped input before they compute with it.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Rq(RqPoly);

impl Rq {
    /// Bytes of the canonical encoding: $`1024 \cdot 20 / 8`$.
    pub const BYTES: usize = 2560;

    /// The zero element.
    #[must_use]
    pub fn zero() -> Self {
        Self(in_pcs_ring(RqPoly::zero(&NTRU)))
    }

    /// The unit element $`1`$.
    #[must_use]
    pub fn one() -> Self {
        let mut c = vec![0u32; D];
        c[0] = 1;
        Self(in_pcs_ring(RqPoly::from_coeffs(&NTRU, &c)))
    }

    /// From canonical coefficients, each in $`[0, q)`$.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless there are exactly $`d = 1024`$ coefficients;
    /// [`Error::Serialization`] for a coefficient $`\ge q`$.
    pub fn from_coeffs(c: &[u32]) -> Result<Self, Error> {
        check_len(c.len())?;
        RqPoly::from_coeffs(&NTRU, c)
            .map(Self)
            .map_err(|_| Error::Serialization("coefficient of R_q not below q".into()))
    }

    /// From arbitrary integers, reduced modulo $`q`$.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless there are exactly $`d = 1024`$ values.
    pub fn from_i64(c: &[i64]) -> Result<Self, Error> {
        check_len(c.len())?;
        Ok(Self(in_pcs_ring(RqPoly::from_i64(&NTRU, c))))
    }

    /// The canonical coefficients, each in $`[0, q)`$.
    #[must_use]
    pub fn coeffs(&self) -> &[u32] {
        self.0.coeffs()
    }

    /// The centred representatives, in $`(-q/2, q/2]`$.
    #[must_use]
    pub fn to_centered(&self) -> Vec<i32> {
        self.0.to_centered()
    }

    /// `self + other`.
    ///
    /// # Panics
    /// If exactly one operand was wiped (the degrees differ).
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self(self.0.add(&other.0))
    }

    /// `self - other`.
    ///
    /// # Panics
    /// If exactly one operand was wiped (the degrees differ).
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        Self(self.0.sub(&other.0))
    }

    /// `-self`.
    #[must_use]
    pub fn neg(&self) -> Self {
        Self(self.0.neg())
    }

    /// `self · other`, exactly.
    ///
    /// # Panics
    /// If an operand was wiped.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        assert!(
            self.is_element() && other.is_element(),
            "Rq::mul: a wiped operand"
        );
        Self(self.0.mul(&other.0))
    }

    /// The inverse in $`R_q`$, or `None` if `self` is not a unit.
    ///
    /// # Panics
    /// If `self` was wiped.
    #[must_use]
    pub fn inverse(&self) -> Option<Self> {
        assert!(self.is_element(), "Rq::inverse: a wiped element");
        self.0.inverse().map(Self)
    }

    /// Whether `self` is a unit of $`R_q`$.
    ///
    /// # Panics
    /// If `self` was wiped.
    #[must_use]
    pub fn is_invertible(&self) -> bool {
        assert!(self.is_element(), "Rq::is_invertible: a wiped element");
        self.0.is_invertible()
    }

    /// The canonical encoding ([`Self::BYTES`] bytes); empty for a wiped element, which no
    /// decoder accepts.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        if self.is_element() {
            self.0.to_bytes()
        } else {
            Vec::new()
        }
    }

    /// Whether `self` is an element of $`R_q`$: it is unless it was wiped.
    fn is_element(&self) -> bool {
        self.0.matches(&NTRU)
    }

    /// Decodes the canonical encoding.
    ///
    /// # Errors
    /// [`Error::Serialization`] for a wrong length, a coefficient $`\ge q`$ or a nonzero padding
    /// bit (there is none at $`d = 1024`$, 20 bits per coefficient).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        RqPoly::from_bytes(&NTRU, bytes)
            .map(Self)
            .map_err(|e| Error::Serialization(format!("R_q element: {e}")))
    }

    /// The `ntru-trapdoor` element, for the full arithmetic of that crate (prepared products,
    /// `samp_pre` targets).
    #[must_use]
    pub(crate) fn poly(&self) -> &RqPoly {
        &self.0
    }

    /// Wraps an `ntru-trapdoor` element of the PCS ring.
    ///
    /// # Panics
    /// If `poly` belongs to another ring (a programming error: every element of this crate is
    /// built from [`NTRU`]).
    #[must_use]
    pub(crate) fn from_poly(poly: RqPoly) -> Self {
        assert!(
            poly.matches(&NTRU),
            "Rq::from_poly: not an element of the PCS ring"
        );
        Self(poly)
    }
}

fn check_len(actual: usize) -> Result<(), Error> {
    if actual == D {
        Ok(())
    } else {
        Err(Error::LengthMismatch {
            expected: D,
            actual,
        })
    }
}

impl Zeroize for Rq {
    /// Wipes the coefficients (and empties the element).
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl fmt::Debug for Rq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Rq(..)")
    }
}

impl CanonicalSerialize for Rq {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        writer.write_all(&self.to_bytes())?;
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for Rq {
    fn check(&self) -> Result<(), SerializationError> {
        if self.0.matches(&NTRU) {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl CanonicalDeserialize for Rq {
    /// Always checks canonicity, whatever `validate` says (module docs).
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = vec![0u8; Self::BYTES];
        reader.read_exact(&mut bytes)?;
        Self::from_bytes(&bytes).map_err(|_| SerializationError::InvalidData)
    }
}

// ---------------------------------------------------------------------------------------------
// Ternary polynomials
// ---------------------------------------------------------------------------------------------

/// A polynomial of $`R`$ with coefficients in $`\{-1, 0, 1\}`$ (`‖·‖_∞ ≤ 1`): the user key
/// `usk` (whose coefficient vector is the key of the short-key `Tag_LWR`, so the tag and the
/// credential refer to the same object, sec:inst-base-vsis), the components of $`x_0`$ and the
/// signing randomness $`x_1`$.
///
/// Secret in every use: wiped on drop, compared in constant time, redacted in `Debug`. `Clone`
/// because credentials and messages that contain one are.
#[derive(Clone)]
pub struct Ternary(Vec<i8>);

impl Ternary {
    /// Bytes of the canonical encoding: 2 bits per coefficient.
    pub const BYTES: usize = D / 4;

    /// A uniform element of $`\{-1, 0, 1\}^d`$.
    ///
    /// Exact: bytes of the RNG below $`243 = 3^5`$ are written in base 3, each giving five
    /// independent uniform digits $`t \in \{0, 1, 2\}`$, and the coefficient is $`t - 1`$; bytes
    /// from 243 on are discarded (probability $`13/256`$), which reveals only how many were.
    pub fn sample<R: RngCore + CryptoRng + ?Sized>(rng: &mut R) -> Self {
        // Exact capacity: no reallocation leaves copies behind.
        let mut c = Vec::with_capacity(D);
        let mut buf = Zeroizing::new([0u8; 64]);
        'fill: loop {
            rng.fill_bytes(&mut *buf);
            for &byte in buf.iter() {
                if byte >= 243 {
                    continue;
                }
                let mut x = byte;
                for _ in 0..5 {
                    if c.len() == D {
                        break 'fill;
                    }
                    c.push((x % 3) as i8 - 1);
                    x /= 3;
                }
            }
        }
        Self(c)
    }

    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        Self(vec![0; D])
    }

    /// From coefficients in $`\{-1, 0, 1\}`$.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless there are exactly $`d = 1024`$ coefficients;
    /// [`Error::InvalidMessage`] for a coefficient outside $`\{-1, 0, 1\}`$.
    pub fn from_coeffs(c: &[i8]) -> Result<Self, Error> {
        check_len(c.len())?;
        if c.iter().any(|&x| !(-1..=1).contains(&x)) {
            return Err(Error::InvalidMessage);
        }
        Ok(Self(c.to_vec()))
    }

    /// The coefficients, each in $`\{-1, 0, 1\}`$.
    #[must_use]
    pub fn coeffs(&self) -> &[i8] {
        &self.0
    }

    /// The element of $`R_q`$ with these coefficients. Secret like `self`: the caller wipes it
    /// ([`Zeroizing`]). Branch-free.
    ///
    /// # Panics
    /// If `self` was wiped (it then has no coefficients; every algorithm of the crate refuses a
    /// wiped polynomial before it gets here).
    #[must_use]
    pub fn to_rq(&self) -> Rq {
        let mut c: Zeroizing<Vec<u32>> = Zeroizing::new(
            self.0
                .iter()
                .map(|&x| {
                    // x + q in [q - 1, q + 1], then subtract q iff it is at least q
                    let u = (i64::from(x) + i64::from(Q)) as u32;
                    u - (Q & 0u32.wrapping_sub(u32::from(u >= Q)))
                })
                .collect(),
        );
        let rq = Self::to_rq_checked(&c);
        c.zeroize();
        rq
    }

    fn to_rq_checked(c: &[u32]) -> Rq {
        Rq(in_pcs_ring(RqPoly::from_coeffs(&NTRU, c)))
    }

    /// Equality in constant time (no early exit on the first difference).
    #[must_use]
    pub fn ct_eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        let diff = self
            .0
            .iter()
            .zip(other.0.iter())
            .fold(0u8, |acc, (&a, &b)| acc | (a ^ b) as u8);
        diff == 0
    }

    /// The canonical encoding ([`Self::BYTES`] bytes) in a buffer that is wiped on drop:
    /// coefficient $`i`$ is the 2-bit two's complement code at bits $`2i, 2i + 1`$
    /// (`0 → 00`, `1 → 01`, `−1 → 11`), little-endian within each byte. A WIPED polynomial has
    /// no encoding: the result is then empty, which no decoder accepts (and not the 256 zero
    /// bytes of the zero polynomial, a valid key).
    #[must_use]
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        if self.0.len() != D {
            return Zeroizing::new(Vec::new());
        }
        let mut out = Zeroizing::new(vec![0u8; Self::BYTES]);
        for (byte, chunk) in out.iter_mut().zip(self.0.as_chunks::<4>().0) {
            *byte = chunk
                .iter()
                .enumerate()
                .fold(0u8, |acc, (k, &x)| acc | (((x as u8) & 3) << (2 * k)));
        }
        out
    }

    /// Decodes the canonical encoding; rejects a wrong length and the code `10`.
    ///
    /// # Errors
    /// [`Error::Serialization`].
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != Self::BYTES {
            return Err(Error::Serialization(format!(
                "ternary polynomial: {} bytes, expected {}",
                bytes.len(),
                Self::BYTES
            )));
        }
        let mut c = Vec::with_capacity(D);
        let mut bad = 0u8;
        for &byte in bytes {
            for k in 0..4 {
                let code = (byte >> (2 * k)) & 3;
                bad |= u8::from(code == 2);
                // sign extension of a 2-bit two's complement code
                c.push(((code << 6) as i8) >> 6);
            }
        }
        let value = Self(c);
        if bad == 0 {
            Ok(value)
        } else {
            Err(Error::Serialization(
                "ternary polynomial: coefficient code 10".into(),
            ))
        }
    }
}

impl PartialEq for Ternary {
    /// In constant time ([`Ternary::ct_eq`]).
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other)
    }
}

impl Eq for Ternary {}

impl Zeroize for Ternary {
    /// Wipes the coefficients and the spare capacity, then empties the polynomial.
    fn zeroize(&mut self) {
        self.0.as_mut_slice().zeroize();
        self.0.spare_capacity_mut().zeroize();
        self.0.clear();
    }
}

impl Drop for Ternary {
    fn drop(&mut self) {
        self.zeroize();
    }
}

impl ZeroizeOnDrop for Ternary {}

impl fmt::Debug for Ternary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Ternary(<redacted>)")
    }
}

impl CanonicalSerialize for Ternary {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        if self.0.len() != D {
            return Err(SerializationError::InvalidData);
        }
        writer.write_all(&self.to_bytes())?;
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for Ternary {
    fn check(&self) -> Result<(), SerializationError> {
        if self.0.len() == D && self.0.iter().all(|&x| (-1..=1).contains(&x)) {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl CanonicalDeserialize for Ternary {
    /// Always checks canonicity, whatever `validate` says (module docs).
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = Zeroizing::new([0u8; Self::BYTES]);
        reader.read_exact(&mut *bytes)?;
        Self::from_bytes(&*bytes).map_err(|_| SerializationError::InvalidData)
    }
}

// ---------------------------------------------------------------------------------------------
// Binary polynomials
// ---------------------------------------------------------------------------------------------

/// A polynomial of $`R`$ with binary coefficients: the public message
/// $`\phi = \mathsf{EncPred}(f) \in \mathcal M_{\mathsf{pub}}`$ of `Σ-vSIS`. Bit $`i`$ of the
/// 128 bytes (least significant bit first) is coefficient $`i`$, so every value is binary: the
/// check $`\phi \in \mathcal M_{\mathsf{pub}}`$ of `VerifyProofAtt` (con:151) is an invariant of
/// the type, and the non-binary $`\phi`$ of the credential-free forgery (bb:892) cannot be
/// represented.
/// Public.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BinaryPoly([u8; Self::BYTES]);

impl BinaryPoly {
    /// Bytes of the encoding: one bit per coefficient.
    pub const BYTES: usize = D / 8;

    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        Self([0; Self::BYTES])
    }

    /// The polynomial whose coefficient $`i`$ is bit $`i \bmod 8`$ of byte $`\lfloor i/8 \rfloor`$.
    /// Every byte string is one.
    #[must_use]
    pub fn from_bytes(bytes: [u8; Self::BYTES]) -> Self {
        Self(bytes)
    }

    /// The encoding.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; Self::BYTES] {
        &self.0
    }

    /// Coefficient $`i`$, in $`\{0, 1\}`$.
    ///
    /// # Panics
    /// If $`i \ge d`$.
    #[must_use]
    pub fn coefficient(&self, i: usize) -> u8 {
        (self.0[i / 8] >> (i % 8)) & 1
    }

    /// The element of $`R_q`$ with these coefficients.
    #[must_use]
    pub fn to_rq(&self) -> Rq {
        let c: Vec<u32> = (0..D).map(|i| u32::from(self.coefficient(i))).collect();
        Rq(in_pcs_ring(RqPoly::from_coeffs(&NTRU, &c)))
    }
}

impl fmt::Debug for BinaryPoly {
    /// The first eight bytes in hex.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("BinaryPoly(")?;
        for byte in &self.0[..8] {
            write!(f, "{byte:02x}")?;
        }
        f.write_str("..)")
    }
}

impl CanonicalSerialize for BinaryPoly {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        writer.write_all(&self.0)?;
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for BinaryPoly {
    const TRIVIAL_CHECK: bool = true;

    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for BinaryPoly {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = [0u8; Self::BYTES];
        reader.read_exact(&mut bytes)?;
        Ok(Self(bytes))
    }
}

// ---------------------------------------------------------------------------------------------
// Signed packing
// ---------------------------------------------------------------------------------------------

/// Appends `values` in `w`-bit two's complement, $`2 \le w \le 32`$, as a little-endian bit
/// string (value $`i`$ at bits $`[iw, (i+1)w)`$; byte $`k`$ holds bits $`[8k, 8k + 8)`$), the last
/// byte zero-padded. This is `ntru-trapdoor`'s secret-key packing (fn-dsa's `trim_i8_encode`)
/// generalised; the preimage $`s`$ of `Σ-vSIS` uses $`w = 20`$.
///
/// # Errors
/// [`SerializationError::InvalidData`] unless every value lies in
/// $`(-2^{w-1}, 2^{w-1})`$ (the value $`-2^{w-1}`$ is excluded so that the code is symmetric);
/// nothing is written then.
pub(crate) fn pack_signed(
    values: &[i32],
    w: u32,
    out: &mut Vec<u8>,
) -> Result<(), SerializationError> {
    assert!((2..=32).contains(&w), "pack_signed: width {w}");
    let limit = 1i64 << (w - 1);
    if values.iter().any(|&v| i64::from(v).abs() >= limit) {
        return Err(SerializationError::InvalidData);
    }
    let mask = (1u64 << w) - 1;
    let mut acc = 0u64;
    let mut bits = 0u32;
    out.reserve((values.len() * w as usize).div_ceil(8));
    for &v in values {
        acc |= (u64::from(v as u32) & mask) << bits;
        bits += w;
        while bits >= 8 {
            out.push(acc as u8);
            acc >>= 8;
            bits -= 8;
        }
    }
    if bits > 0 {
        out.push(acc as u8);
    }
    acc.zeroize();
    Ok(())
}

/// Reads `n` values of [`pack_signed`] from exactly $`\lceil nw/8 \rceil`$ bytes, into a buffer
/// that is wiped on drop.
///
/// # Errors
/// [`SerializationError::InvalidData`] for a wrong length, the value $`-2^{w-1}`$ or a nonzero
/// padding bit.
pub(crate) fn unpack_signed(
    bytes: &[u8],
    n: usize,
    w: u32,
) -> Result<Zeroizing<Vec<i32>>, SerializationError> {
    assert!((2..=32).contains(&w), "unpack_signed: width {w}");
    if bytes.len() != (n * w as usize).div_ceil(8) {
        return Err(SerializationError::InvalidData);
    }
    let mask = (1u64 << w) - 1;
    let sign = 1u64 << (w - 1);
    let mut out = Zeroizing::new(Vec::with_capacity(n));
    let mut acc = 0u64;
    let mut bits = 0u32;
    let mut bad = false;
    let mut src = bytes.iter();
    for _ in 0..n {
        while bits < w {
            // the length check guarantees enough bytes
            let byte = src.next().ok_or(SerializationError::InvalidData)?;
            acc |= u64::from(*byte) << bits;
            bits += 8;
        }
        let v = acc & mask;
        acc >>= w;
        bits -= w;
        bad |= v == sign;
        // sign extension of a w-bit two's complement value
        out.push((v ^ sign).wrapping_sub(sign) as u32 as i32);
    }
    bad |= acc != 0 || src.next().is_some();
    acc.zeroize();
    if bad {
        Err(SerializationError::InvalidData)
    } else {
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::serialization::{from_bytes, to_bytes};

    #[test]
    fn the_pcs_ring_passes_the_checks_of_ntru_trapdoor() {
        assert!(NTRU.validate().is_ok());
        assert!(RqPoly::zero(&NTRU).is_ok());
        assert_eq!(NTRU.rq_bytes(), Rq::BYTES);
        assert_eq!(Rq::zero().coeffs().len(), D);
        assert_eq!(Rq::one().mul(&Rq::one()), Rq::one());
    }

    #[test]
    fn rq_encoding_is_canonical() {
        let mut rng = StdRng::seed_from_u64(0x7121);
        let c: Vec<i64> = (0..D).map(|_| rng.next_u64() as i64).collect();
        let a = Rq::from_i64(&c).unwrap();
        let bytes = to_bytes(&a).unwrap();
        assert_eq!(bytes.len(), Rq::BYTES);
        assert_eq!(from_bytes::<Rq>(&bytes).unwrap(), a);
        // coefficient 0 set to q: rejected
        let mut bad = bytes.clone();
        bad[0] = (Q & 0xff) as u8;
        bad[1] = ((Q >> 8) & 0xff) as u8;
        bad[2] = (bad[2] & 0xf0) | ((Q >> 16) & 0x0f) as u8;
        assert!(from_bytes::<Rq>(&bad).is_err());
        assert!(from_bytes::<Rq>(&bytes[..Rq::BYTES - 1]).is_err());
        assert!(Rq::from_coeffs(&[0; D - 1]).is_err());
        assert!(Rq::from_coeffs(&[Q; D]).is_err());
        // inverse
        let inv = a.inverse().unwrap();
        assert_eq!(a.mul(&inv), Rq::one());
        assert!(!Rq::zero().is_invertible());
        assert_eq!(format!("{a:?}"), "Rq(..)");
    }

    #[test]
    fn ternary_sampling_encoding_and_wiping() {
        let mut rng = StdRng::seed_from_u64(0x7122);
        let t = Ternary::sample(&mut rng);
        assert_eq!(t.coeffs().len(), D);
        let counts = [-1i8, 0, 1].map(|v| t.coeffs().iter().filter(|&&x| x == v).count());
        assert_eq!(counts.iter().sum::<usize>(), D);
        // each value about d/3 = 341 times (6 standard deviations: ±90)
        assert!(
            counts.iter().all(|&c| (251..=431).contains(&c)),
            "{counts:?}"
        );
        // encoding: 2-bit two's complement, the code 10 rejected
        let bytes = to_bytes(&t).unwrap();
        assert_eq!(bytes.len(), Ternary::BYTES);
        assert_eq!(from_bytes::<Ternary>(&bytes).unwrap(), t);
        let mut c = vec![0i8; D];
        c[0] = 1;
        c[1] = -1;
        c[5] = -1;
        let u = Ternary::from_coeffs(&c).unwrap();
        let ub = u.to_bytes();
        assert_eq!(ub[0], 0b0000_1101);
        assert_eq!(ub[1], 0b0000_1100);
        let mut bad = ub.to_vec();
        bad[0] = 0b0000_0010;
        assert!(Ternary::from_bytes(&bad).is_err());
        assert!(Ternary::from_coeffs(&[2; D]).is_err());
        // to_rq maps -1 to q - 1
        let r = u.to_rq();
        assert_eq!(r.coeffs()[0], 1);
        assert_eq!(r.coeffs()[1], Q - 1);
        assert_eq!(r.coeffs()[2], 0);
        // constant-time equality, redaction, wiping
        assert_eq!(u.clone(), u);
        assert_ne!(u, Ternary::zero());
        assert_eq!(format!("{u:?}"), "Ternary(<redacted>)");
        let mut w = u.clone();
        w.zeroize();
        assert!(w.coeffs().is_empty());
        assert!(to_bytes(&w).is_err());
        // a wiped polynomial has no encoding: not the 256 zero bytes of the zero polynomial
        assert!(w.to_bytes().is_empty());
        assert_eq!(Ternary::zero().to_bytes().len(), Ternary::BYTES);
        assert!(Ternary::from_bytes(&w.to_bytes()).is_err());
    }

    /// The documented panics on wiped values (`# Panics` of `Ternary::to_rq` and `Rq::mul`).
    #[test]
    fn arithmetic_on_wiped_values_panics() {
        let mut w = Ternary::zero();
        w.zeroize();
        assert!(std::panic::catch_unwind(|| w.to_rq()).is_err());
        let mut r = Rq::one();
        r.zeroize();
        assert!(r.to_bytes().is_empty());
        let one = Rq::one();
        assert!(std::panic::catch_unwind(|| r.mul(&one)).is_err());
        assert!(std::panic::catch_unwind(|| one.add(&r)).is_err());
        assert!(std::panic::catch_unwind(|| r.inverse()).is_err());
    }

    #[test]
    fn binary_polynomials() {
        let mut bytes = [0u8; BinaryPoly::BYTES];
        bytes[0] = 0b1000_0001;
        bytes[127] = 0x80;
        let phi = BinaryPoly::from_bytes(bytes);
        assert_eq!(phi.coefficient(0), 1);
        assert_eq!(phi.coefficient(1), 0);
        assert_eq!(phi.coefficient(7), 1);
        assert_eq!(phi.coefficient(D - 1), 1);
        let r = phi.to_rq();
        assert_eq!(r.coeffs()[7], 1);
        assert_eq!(r.coeffs().iter().filter(|&&x| x != 0).count(), 3);
        let encoded = to_bytes(&phi).unwrap();
        assert_eq!(encoded, bytes);
        assert_eq!(from_bytes::<BinaryPoly>(&encoded).unwrap(), phi);
        assert_eq!(format!("{phi:?}"), "BinaryPoly(8100000000000000..)");
    }

    #[test]
    fn signed_packing_round_trips_and_is_strict() {
        let mut rng = StdRng::seed_from_u64(0x7123);
        for w in [2u32, 3, 7, 12, 19, 20, 32] {
            let limit = (1i64 << (w - 1)) - 1;
            for n in [1usize, 3, 8, 1024] {
                let values: Vec<i32> = (0..n)
                    .map(|_| ((rng.next_u64() % (2 * limit as u64 + 1)) as i64 - limit) as i32)
                    .collect();
                let mut out = Vec::new();
                pack_signed(&values, w, &mut out).unwrap();
                assert_eq!(out.len(), (n * w as usize).div_ceil(8));
                assert_eq!(&*unpack_signed(&out, n, w).unwrap(), &values, "w {w} n {n}");
            }
            // -2^(w-1) is neither written nor read
            let mut out = Vec::new();
            assert!(pack_signed(&[-(1i64 << (w - 1)) as i32], w, &mut out).is_err());
            assert!(out.is_empty());
        }
        // 20 bits: the code 0x80000 (-2^19) is rejected, as is a nonzero padding bit
        let bad = [0x00, 0x00, 0x08];
        assert!(unpack_signed(&bad, 1, 20).is_err());
        let padded = [0x01, 0x00, 0x10];
        assert!(unpack_signed(&padded, 1, 20).is_err());
        assert_eq!(&*unpack_signed(&[0x01, 0x00, 0x00], 1, 20).unwrap(), &[1]);
        assert_eq!(&*unpack_signed(&[0xff, 0xff, 0x0f], 1, 20).unwrap(), &[-1]);
    }
}
