//! SHAKE128 with the crate's framing: the extendable-output function behind the random oracles
//! of the lattice instantiation (`H_mat`, `EncPred`) and behind the expansion of the public
//! parameters from the deployment label.
//!
//! An oracle input is the SHAKE128 absorption of the item `("dst", "PCS-V1" ‖ suffix)` followed
//! by the caller's items `(label, data)`, each framed as in [`crate::hash`]:
//! `LE64(|label|) ‖ label ‖ LE64(|data|) ‖ data`. The framing is injective, and oracles with
//! different suffixes are independent:
//!
//! | suffix | items | output |
//! |---|---|---|
//! | `/LATTICE-PP` | `deployment`, `element` (`v`, `b_u`, `b_phi`, `B_r[0]`, `B_r[1]`) | one element of $`R_q`$ ([`Stream::uniform_rq`]) |
//! | `/LATTICE-HMAT` | `deployment`, `input` | a matrix of $`\mathbb Z_{q_t}^{m \times n}`$ (`H_mat`, [`crate::lattice::oracles`]) |
//! | `/LATTICE-PREDENC` | `deployment`, `input` | the first $`d`$ bits (`EncPred`, [`crate::lattice::oracles`]) |
//! | `/LATTICE-JALI-SEED` | `deployment` | the 32-byte public seed of Jali ([`jali_pp_seed`]) |
//!
//! **Uniform sampling.** [`Stream::uniform_20`] reads the output as a little-endian bit string
//! (bit $`8k + j`$ is bit $`j`$ of byte $`k`$), cuts it into consecutive 20-bit chunks, each read
//! little-endian, and accepts a chunk iff it is below the modulus; the accepted values fill the
//! output in order (row-major for a matrix). Both moduli of the instantiation have bit length
//! $`\mathrm{bitlen}(q - 1) = \mathrm{bitlen}(q_t - 1) = 20`$: every chunk is accepted with
//! probability $`q / 2^{20} > 0.99999`$, resp. $`q_t / 2^{20} = 0.9375`$, and every output is
//! exactly uniform. Five bytes are two chunks.

use shake::{ExtendableOutput, Shake128, Shake128Reader, Update, XofReader};

use super::{D, Q, ring::Rq};
use crate::hash::DOMAIN_PREFIX;

/// Oracle suffix of the expansion of `pp_Σ = (v, b_u, b_φ, B_r)`.
pub(crate) const PP_SUFFIX: &[u8] = b"/LATTICE-PP";
/// Oracle suffix of `H_mat`.
pub(crate) const HMAT_SUFFIX: &[u8] = b"/LATTICE-HMAT";
/// Oracle suffix of `EncPred` (domain-separated from `H_0 = H_mat("tag" ‖ ·)`, con:65).
pub(crate) const PREDENC_SUFFIX: &[u8] = b"/LATTICE-PREDENC";
/// Oracle suffix of Jali's public seed `pp_seed`.
pub(crate) const JALI_SEED_SUFFIX: &[u8] = b"/LATTICE-JALI-SEED";

/// The SHAKE128 rate in bytes; the output buffer holds five blocks (840 bytes, a multiple of 5).
const RATE: usize = 168;
const BUFFER: usize = 5 * RATE;

/// An oracle input being absorbed (module docs).
pub(crate) struct Xof(Shake128);

impl Xof {
    /// A fresh input of the oracle `PCS-V1 ‖ oracle_suffix`, which is absorbed as the item
    /// `("dst", PCS-V1 ‖ suffix)`.
    pub(crate) fn new(oracle_suffix: &[u8]) -> Self {
        let mut xof = Self(Shake128::default());
        xof.absorb(b"dst", &[DOMAIN_PREFIX, oracle_suffix].concat());
        xof
    }

    /// Absorbs the item `(label, data)`: `LE64(|label|) ‖ label ‖ LE64(|data|) ‖ data`.
    pub(crate) fn absorb(&mut self, label: &[u8], data: &[u8]) -> &mut Self {
        // `usize` is at most 64 bits wide on every supported target, so the casts are lossless.
        self.0.update(&(label.len() as u64).to_le_bytes());
        self.0.update(label);
        self.0.update(&(data.len() as u64).to_le_bytes());
        self.0.update(data);
        self
    }

    /// The output stream.
    pub(crate) fn finish(self) -> Stream {
        Stream {
            reader: self.0.finalize_xof(),
            buf: [0; BUFFER],
            pos: BUFFER,
        }
    }
}

/// The output of an oracle, read in order.
pub(crate) struct Stream {
    reader: Shake128Reader,
    buf: [u8; BUFFER],
    pos: usize,
}

impl Stream {
    fn next_byte(&mut self) -> u8 {
        if self.pos == BUFFER {
            self.reader.read(&mut self.buf);
            self.pos = 0;
        }
        let byte = self.buf[self.pos];
        self.pos += 1;
        byte
    }

    /// The next `out.len()` bytes.
    pub(crate) fn fill(&mut self, out: &mut [u8]) {
        for byte in out {
            *byte = self.next_byte();
        }
    }

    /// Fills `out` with uniform values below `modulus` (module docs), $`2^{19} < `$ `modulus`
    /// $`\le 2^{20}`$.
    ///
    /// # Panics
    /// If `modulus` is outside that range (both moduli of the instantiation are inside).
    pub(crate) fn uniform_20(&mut self, modulus: u32, out: &mut [u32]) {
        assert!(
            (1 << 19) < modulus && modulus <= (1 << 20),
            "uniform_20: the modulus must have bit length 20 after subtracting 1"
        );
        let mut filled = 0;
        while filled < out.len() {
            let b = [
                self.next_byte(),
                self.next_byte(),
                self.next_byte(),
                self.next_byte(),
                self.next_byte(),
            ];
            let first = u32::from(b[0]) | (u32::from(b[1]) << 8) | ((u32::from(b[2]) & 0x0f) << 16);
            let second = (u32::from(b[2]) >> 4) | (u32::from(b[3]) << 4) | (u32::from(b[4]) << 12);
            for chunk in [first, second] {
                if chunk < modulus && filled < out.len() {
                    out[filled] = chunk;
                    filled += 1;
                }
            }
        }
    }

    /// A uniform element of $`R_q`$: [`Self::uniform_20`] at $`q`$ for its $`d`$ coefficients.
    pub(crate) fn uniform_rq(&mut self) -> Rq {
        let mut c = vec![0u32; D];
        self.uniform_20(Q, &mut c);
        match Rq::from_coeffs(&c) {
            Ok(element) => element,
            Err(_) => unreachable!("uniform_20 returns d values below q"),
        }
    }
}

/// The element `name` of `pp_Σ` for the deployment label `deployment`: [`Stream::uniform_rq`] of
/// the oracle `/LATTICE-PP` with the items `("deployment", deployment)` and `("element", name)`.
/// The names are `v`, `b_u`, `b_phi`, `B_r[0]` and `B_r[1]` (ASCII).
pub(crate) fn pp_element(deployment: &[u8], name: &[u8]) -> Rq {
    let mut xof = Xof::new(PP_SUFFIX);
    xof.absorb(b"deployment", deployment)
        .absorb(b"element", name);
    xof.finish().uniform_rq()
}

/// Jali's public seed `pp_seed` for the deployment label `deployment`: the first 32 bytes of the
/// oracle `/LATTICE-JALI-SEED` with the item `("deployment", deployment)`. Public randomness, never
/// chosen by the helper (bb:795, "from public randomness").
pub(crate) fn jali_pp_seed(deployment: &[u8]) -> [u8; 32] {
    let mut xof = Xof::new(JALI_SEED_SUFFIX);
    xof.absorb(b"deployment", deployment);
    let mut seed = [0u8; 32];
    xof.finish().fill(&mut seed);
    seed
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The deployment label of the known answers. They were computed independently with
    /// Python's `hashlib.shake_128` (`tools/lattice/ref_oracles.py`).
    const KAT_DEPLOYMENT: &[u8] = b"PCS-LATTICE-KAT";

    #[test]
    fn framing_is_the_documented_byte_string() {
        // SHAKE128 of the framed input, computed by hand from the module docs
        let mut expected = Vec::new();
        for (label, data) in [
            (&b"dst"[..], &b"PCS-V1/LATTICE-PP"[..]),
            (b"deployment", KAT_DEPLOYMENT),
            (b"element", b"v"),
        ] {
            expected.extend_from_slice(&(label.len() as u64).to_le_bytes());
            expected.extend_from_slice(label);
            expected.extend_from_slice(&(data.len() as u64).to_le_bytes());
            expected.extend_from_slice(data);
        }
        let mut reference = Shake128::default();
        reference.update(&expected);
        let mut want = [0u8; 10];
        reference.finalize_xof().read(&mut want);
        let mut xof = Xof::new(PP_SUFFIX);
        xof.absorb(b"deployment", KAT_DEPLOYMENT)
            .absorb(b"element", b"v");
        let mut got = [0u8; 10];
        xof.finish().fill(&mut got);
        assert_eq!(got, want);
        // the first ten bytes of that stream (Python reference)
        assert_eq!(
            got,
            [0x66, 0xc1, 0x3b, 0x2b, 0x7c, 0x0e, 0x44, 0x07, 0xbc, 0xc7]
        );
    }

    #[test]
    fn known_answers() {
        assert_eq!(
            jali_pp_seed(KAT_DEPLOYMENT),
            [
                0x2f, 0x74, 0x22, 0xb9, 0x74, 0xaa, 0x61, 0x55, 0x89, 0x62, 0x99, 0x86, 0x57, 0xba,
                0x3c, 0x3a, 0x92, 0xe4, 0x7a, 0x91, 0x9c, 0x5d, 0xef, 0x8f, 0x05, 0x78, 0x21, 0xd7,
                0xc7, 0x01, 0xd0, 0x1a
            ]
        );
        let kat: [(&[u8], [u32; 4], u32, u32); 5] = [
            (b"v", [770406, 508595, 476174, 818112], 192742, 537406709),
            (b"b_u", [444343, 26088, 417981, 121684], 367357, 565256750),
            (
                b"b_phi",
                [801507, 195483, 356755, 209711],
                879905,
                541107186,
            ),
            (b"B_r[0]", [259614, 480301, 168799, 919508], 4759, 544383178),
            (
                b"B_r[1]",
                [225220, 853749, 851519, 200578],
                210172,
                548614151,
            ),
        ];
        for (name, first, last, sum) in kat {
            let element = pp_element(KAT_DEPLOYMENT, name);
            let c = element.coeffs();
            assert_eq!(&c[..4], &first, "{}", String::from_utf8_lossy(name));
            assert_eq!(c[D - 1], last);
            assert_eq!(c.iter().fold(0u32, |acc, &x| acc.wrapping_add(x)), sum);
        }
    }

    #[test]
    fn uniform_sampling_rejects_and_separates() {
        // q_t: a chunk is rejected with probability 1/16, so 2000 values need about 2133 chunks
        let mut xof = Xof::new(HMAT_SUFFIX);
        xof.absorb(b"input", b"x");
        let mut out = vec![0u32; 2000];
        xof.finish().uniform_20(super::super::Q_T, &mut out);
        assert!(out.iter().all(|&x| x < super::super::Q_T));
        // another label, another deployment: other outputs
        assert_ne!(pp_element(b"a", b"v"), pp_element(b"b", b"v"));
        assert_ne!(pp_element(b"a", b"v"), pp_element(b"a", b"b_u"));
        assert_ne!(jali_pp_seed(b"a"), jali_pp_seed(b"b"));
    }
}
