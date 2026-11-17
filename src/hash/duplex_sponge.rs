//! The duplex sponge of the IETF CFRG draft `draft-irtf-cfrg-fiat-shamir-04` over SHAKE128: the
//! random oracle of the Fiat–Shamir transform of [`crate::sigma::fiat_shamir`].
//!
//! * [`DuplexSponge`] is the XOF duplex sponge of §4.2 with the suite SHAKE128 of §9.1 (rate
//!   `R = 168` bytes). `Init(session_id)` absorbs `session_id ‖ zeros(R − 32)`. `Absorb` appends
//!   its input with no separator, and an empty absorb is a no-op. Consecutive squeezes continue
//!   one output stream, which a non-empty absorb restarts over everything absorbed so far.
//! * [`derive_session_id`] is `DeriveSessionID` of §5.1.
//! * [`decode_field`] is `DecodeField(buf, p, 1)` of Appendix A.1.3 for a prime field, which is
//!   `DecodeUint` of Appendix A.1.2: `N_s + 16` bytes read as a little-endian integer and
//!   reduced modulo `p`. [`squeeze_scalar`] squeezes those bytes and decodes them.
//!
//! The state keeps an incremental SHAKE128 context of everything absorbed and squeezes from a
//! reader over a copy of it, as §4.2.3 recommends instead of re-hashing on every squeeze. Both
//! give the same output. `tests/ietf_vectors.rs` runs the draft's SHAKE128 vectors (Appendix C)
//! against this module.

use core::fmt;

use ark_ff::PrimeField;
use shake::{ExtendableOutput, Shake128, Shake128Reader, Update, XofReader};
use zeroize::Zeroizing;

/// The rate `R` of SHAKE128 in bytes (§9.1).
pub const RATE: usize = 168;

/// The 32-byte domain separator of `DeriveSessionID` (§5.1).
pub const SESSION_ID_DOMAIN: &[u8; 32] = b"irtf-cfrg-fiat-shamir/session-id";

/// The XOF duplex sponge of §4.2 over SHAKE128.
///
/// Cloning a sponge forks it: the copy continues from the same state, including the position in
/// the current output stream.
#[derive(Clone)]
pub struct DuplexSponge {
    absorbed: Shake128,
    reader: Option<Shake128Reader>,
}

impl fmt::Debug for DuplexSponge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("DuplexSponge(SHAKE128)")
    }
}

impl DuplexSponge {
    /// `Init(session_id)`: the state that has absorbed `session_id ‖ zeros(R − 32)`.
    #[must_use]
    pub fn new(session_id: &[u8; 32]) -> Self {
        let mut absorbed = Shake128::default();
        absorbed.update(session_id);
        absorbed.update(&[0u8; RATE - 32]);
        Self {
            absorbed,
            reader: None,
        }
    }

    /// `Absorb(x)`. Absorbing the empty string leaves the state unchanged.
    pub fn absorb(&mut self, x: &[u8]) {
        if !x.is_empty() {
            self.absorbed.update(x);
            self.reader = None;
        }
    }

    /// `Squeeze(len(out))`, written into `out`.
    pub fn squeeze(&mut self, out: &mut [u8]) {
        let absorbed = &self.absorbed;
        self.reader
            .get_or_insert_with(|| absorbed.clone().finalize_xof())
            .read(out);
    }

    /// `Squeeze(N)` as an array.
    #[must_use]
    pub fn squeeze_array<const N: usize>(&mut self) -> [u8; N] {
        let mut out = [0u8; N];
        self.squeeze(&mut out);
        out
    }
}

/// `DeriveSessionID(tag)` (§5.1): the 32 bytes squeezed after absorbing `tag` into the sponge
/// started with the domain separator [`SESSION_ID_DOMAIN`].
#[must_use]
pub fn derive_session_id(tag: &[u8]) -> [u8; 32] {
    let mut sponge = DuplexSponge::new(SESSION_ID_DOMAIN);
    sponge.absorb(tag);
    sponge.squeeze_array()
}

/// `N_s` of the prime field `F`: the least number of bytes with `256^{N_s} ≥ p`, which is
/// `⌈bits(p)/8⌉` for a prime `p` (32 for the scalar field of BLS12-381).
#[must_use]
pub fn ns<F: PrimeField>() -> usize {
    F::MODULUS_BIT_SIZE.div_ceil(8) as usize
}

/// `DecodeField(buf, p, 1)` of Appendix A.1.3, for the prime field `F`: `LE2IP(buf) mod p`.
/// `None` unless `buf` has exactly `N_s + 16` bytes, the length the draft asserts.
///
/// The 16 extra bytes bound the statistical distance of the output from uniform on a uniform
/// `buf` by `2^-128` (Appendix A.1.2).
#[must_use]
pub fn decode_field<F: PrimeField>(buf: &[u8]) -> Option<F> {
    // `from_le_bytes_mod_order` reads the bytes as a little-endian integer and reduces it modulo
    // `p` (Horner's rule from the most significant byte). `tests/ietf_vectors.rs` compares it with
    // a plain big-integer reduction.
    (buf.len() == ns::<F>() + 16).then(|| F::from_le_bytes_mod_order(buf))
}

/// `DecodeField(sponge.Squeeze(N_s + 16), p, 1)`: one element of `F` from the sponge, as
/// `DeriveChallenge` of the Sigma draft (§5.2) and the seeded generator of its test vectors
/// (Appendix A.1) draw it.
pub fn squeeze_scalar<F: PrimeField>(sponge: &mut DuplexSponge) -> F {
    let mut buf = Zeroizing::new(vec![0u8; ns::<F>() + 16]);
    sponge.squeeze(&mut buf);
    F::from_le_bytes_mod_order(&buf)
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Fr;

    use super::*;

    #[test]
    fn absorbing_in_pieces_and_squeezing_in_pieces_are_one_stream() {
        let sid = [7u8; 32];
        let mut a = DuplexSponge::new(&sid);
        a.absorb(b"abc");
        a.absorb(b"");
        a.absorb(b"def");
        let mut b = DuplexSponge::new(&sid);
        b.absorb(b"abcdef");
        let whole: [u8; 300] = b.squeeze_array();
        let mut pieces = Vec::new();
        for n in [1usize, 167, 0, 2, 130] {
            let mut buf = vec![0u8; n];
            a.squeeze(&mut buf);
            pieces.extend_from_slice(&buf);
        }
        assert_eq!(pieces, whole);
        // a clone continues the stream where its original stood
        let mut c = a.clone();
        assert_eq!(c.squeeze_array::<16>(), a.squeeze_array::<16>());
        // a non-empty absorb restarts the stream over everything absorbed
        let mut d = DuplexSponge::new(&sid);
        d.absorb(b"abcdef");
        let _ = d.squeeze_array::<5>();
        d.absorb(b"g");
        let mut e = DuplexSponge::new(&sid);
        e.absorb(b"abcdefg");
        assert_eq!(d.squeeze_array::<32>(), e.squeeze_array::<32>());
    }

    #[test]
    fn decode_field_takes_ns_plus_16_bytes() {
        assert_eq!(ns::<Fr>(), 32);
        assert_eq!(decode_field::<Fr>(&[0u8; 47]), None);
        assert_eq!(decode_field::<Fr>(&[0u8; 49]), None);
        assert_eq!(decode_field::<Fr>(&[0u8; 48]), Some(Fr::from(0u64)));
        let mut one = [0u8; 48];
        one[0] = 1;
        assert_eq!(decode_field::<Fr>(&one), Some(Fr::from(1u64)));
        // little-endian: the byte at position 1 weighs 256
        let mut x = [0u8; 48];
        x[1] = 1;
        assert_eq!(decode_field::<Fr>(&x), Some(Fr::from(256u64)));
    }

    #[test]
    fn squeeze_scalar_is_decode_field_of_the_next_48_bytes() {
        let mut a = DuplexSponge::new(&[3u8; 32]);
        a.absorb(b"x");
        let mut b = a.clone();
        let bytes: [u8; 48] = b.squeeze_array();
        assert_eq!(
            squeeze_scalar::<Fr>(&mut a),
            decode_field::<Fr>(&bytes).unwrap()
        );
        // and the stream continues
        assert_eq!(a.squeeze_array::<8>(), b.squeeze_array::<8>());
    }
}
