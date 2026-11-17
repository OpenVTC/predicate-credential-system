//! The random oracles of the lattice tag (§5.1.3, "Random oracles"), each bound to the
//! deployment label like the oracles of [`crate::hash`]:
//!
//! | paper | here | bytes ([`crate::lattice`]'s XOF, module `xof`) |
//! |---|---|---|
//! | $`H_{\mathsf{mat}} : \{0,1\}^* \to \mathbb Z_{q_t}^{m \times n}`$, an extendable-output function with "rejection-sampling each entry" | [`h_mat`] | SHAKE128 of `("dst", "PCS-V1/LATTICE-HMAT")`, `("deployment", label)`, `("input", y)`; consecutive 20-bit chunks below $`q_t`$, row-major |
//! | "Instantiate $`H_{\mathsf{id}}`$ … by $`H_{\mathsf{mat}}`$ under [its own] label"; "the identifier point is $`\mathbf X_0 = H_{\mathsf{id}}(\langle\mathsf{hvk}\rangle)`$" | [`identifier_point`] | $`y = \texttt{hid} \| d`$ |
//! | "… and $`H_{\mathsf{req}}`$ … by $`H_{\mathsf{mat}}`$ under distinct labels of the same fixed length" | [`request_point`] | $`y = \texttt{req} \| d`$ |
//!
//! Each item is framed as `LE64(|label|) ‖ label ‖ LE64(|data|) ‖ data` (module `xof`); the
//! labels and suffixes are ASCII.
//!
//! **`H_id` and `H_req`.** The protocol frames the input of each oracle into a transcript of its
//! own: $`\langle\mathsf{hvk}\rangle`$ after the digest of `pp` for the identifier point
//! (`/PCREDS-HID`, [`crate::pcreds::Protocol::identifier_point`]), and $`\langle pp,
//! \mathsf{hvk}, \mathsf{id}_Q, j_Q\rangle`$ for a recipient point (`/PCREDS-HREQ`,
//! [`crate::pcreds::Protocol::recipient_point`]). The lattice backend hands the transcript's
//! 32-byte digest $`d`$ to $`H_{\mathsf{mat}}`$ under the oracle's label:
//! $`x_0 = H_{\mathsf{mat}}(\texttt{hid} \| d)`$ and $`x_Q = H_{\mathsf{mat}}(\texttt{req} \|
//! d)`$. In the random-oracle model each is a random oracle on its tuple, up to collisions of the
//! digest.
//!
//! # The paper's requirements, and how these bytes meet them
//!
//! * **Uniform entries**: every accepted 20-bit chunk is uniform below $`q_t`$, so
//!   $`H_{\mathsf{mat}}`$ is a uniform matrix when SHAKE128 is modelled as a random oracle; this
//!   is the input distribution of lem:tag-lwr-short and of the weak pseudorandomness of
//!   `Tag_LWR`.
//! * **Fixed-length labels**: the labels `hid` of $`H_{\mathsf{id}}`$ and `req` of
//!   $`H_{\mathsf{req}}`$ both have length 3, so their inputs never collide: the two are
//!   independent oracles.
//! * **"`j_Q` is the least nonnegative counter for which `x_Q ≠ x_0`"**: the protocol does so, on
//!   the backend's points; the lattice backend represents a point by its input to
//!   $`H_{\mathsf{mat}}`$ and compares the MATRICES ([`crate::pcreds::Backend::same_point`]).
//!   The inputs of the two oracles never coincide, and distinct inputs give the same matrix only
//!   with probability $`q_t^{-mn}`$ in the random-oracle model, so the counter is `0` but on that
//!   event.
//!
//! # Cost
//!
//! An `H_mat` matrix is $`m n = 172{,}032`$ entries; a chunk is accepted with probability
//! $`q_t/2^{20} = 15/16`$, so it reads about $`172{,}032 \cdot 16/15 \cdot 2.5 = 458{,}752`$
//! bytes of SHAKE128 output: about 0.6 ms on an Apple M4 core, of which 0.35 ms is SHAKE128
//! itself. The backend derives a matrix when it evaluates a tag or builds a statement.

use super::{
    D, M, Q_T,
    xof::{HMAT_SUFFIX, Xof},
};
use crate::kiprf::lwr::TagMatrix;

/// The label of $`H_{\mathsf{id}}`$ inside $`H_{\mathsf{mat}}`$'s input. Fixed length 3.
pub(crate) const H_ID_LABEL: &[u8] = b"hid";
/// The label of $`H_{\mathsf{req}}`$ inside $`H_{\mathsf{mat}}`$'s input. Fixed length 3, as
/// the label of $`H_{\mathsf{id}}`$.
pub(crate) const H_REQ_LABEL: &[u8] = b"req";

const _: () = assert!(H_ID_LABEL.len() == H_REQ_LABEL.len());

/// $`H_{\mathsf{mat}}(y)`$ for the deployment label `deployment` (module docs): the $`m n`$
/// entries in row-major order (entry $`(j, i)`$ at index $`n j + i`$), each the next accepted
/// 20-bit chunk of SHAKE128 below $`q_t`$.
#[must_use]
pub fn h_mat(deployment: &[u8], input: &[u8]) -> TagMatrix {
    let mut xof = Xof::new(HMAT_SUFFIX);
    xof.absorb(b"deployment", deployment)
        .absorb(b"input", input);
    let mut entries = vec![0u32; M * D];
    xof.finish().uniform_20(Q_T, &mut entries);
    match TagMatrix::from_entries(entries) {
        Ok(matrix) => matrix,
        Err(_) => unreachable!("uniform_20 returns m·n values below q_t"),
    }
}

/// $`x_0 = H_{\mathsf{id}}(\langle\mathsf{hvk}\rangle) = H_{\mathsf{mat}}(\texttt{"hid"} \|
/// d)`$ for the digest $`d`$ of the protocol's `H_id` transcript of a helper key (module docs),
/// the point of the identifiers $`\mathsf{id} = \mathsf{Tag}(\mathsf{usk}, x_0)`$ under that
/// key.
#[must_use]
pub fn identifier_point(deployment: &[u8], digest: &[u8; 32]) -> TagMatrix {
    h_mat(deployment, &[H_ID_LABEL, digest].concat())
}

/// $`x_Q = H_{\mathsf{mat}}(\texttt{"req"} \| d)`$, the recipient point for the digest $`d`$ of
/// the protocol's `H_req` transcript (module docs), at which the attestation tags for the
/// requester $`Q`$ are evaluated.
#[must_use]
pub fn request_point(deployment: &[u8], digest: &[u8; 32]) -> TagMatrix {
    h_mat(deployment, &[H_REQ_LABEL, digest].concat())
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};
    use shake::{ExtendableOutput, Shake128, Update, XofReader};

    use super::*;
    use crate::{hash::DOMAIN_PREFIX, kiprf::lwr::LWR, lattice::Ternary};

    /// The deployment label of the known answers, as in the module `xof`. The answers were
    /// computed independently with Python's `hashlib.shake_128` and exact rationals
    /// (`tools/lattice/ref_tag.py`, output `tools/lattice/ref_tag.out`); the first ones also by
    /// `tools/lattice/ref_oracles.py`.
    const KAT: &[u8] = b"PCS-LATTICE-KAT";

    /// `(first four entries, entry n (row 1, column 0), last entry, sum mod 2^32,
    /// SHA-256 of the 20-bit packing)`.
    type Summary = ([u32; 4], u32, u32, u32, &'static str);

    fn check_summary(a: &TagMatrix, (first, row1, last, sum, sha): Summary) {
        let e = a.entries();
        assert_eq!(e.len(), M * D);
        assert_eq!(&e[..4], &first);
        assert_eq!(e[D], row1);
        assert_eq!(e[M * D - 1], last);
        assert_eq!(e.iter().fold(0u32, |acc, &x| acc.wrapping_add(x)), sum);
        assert_eq!(hex(&Sha256::digest(a.to_bytes())), sha);
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// The key of the known answers: `k_i = ((i · 0x9E3779B1 mod 2^32) >> 16) mod 3 − 1`.
    fn kat_key() -> Ternary {
        let c: Vec<i8> = (0..D as u32)
            .map(|i| ((i.wrapping_mul(0x9E37_79B1) >> 16) % 3) as i8 - 1)
            .collect();
        Ternary::from_coeffs(&c).unwrap()
    }

    /// The digest `00 01 … 1f`.
    fn counting_digest() -> [u8; 32] {
        core::array::from_fn(|i| i as u8)
    }

    /// The `H_id` digest of the known answers: SHA-256 of `x_0 of the known answers`.
    fn identifier_digest() -> [u8; 32] {
        Sha256::digest(b"x_0 of the known answers").into()
    }

    /// SHAKE128 of the framed items, written out by hand from the module docs.
    fn shake_framed(suffix: &[u8], items: &[(&[u8], &[u8])], n: usize) -> Vec<u8> {
        let mut input = Vec::new();
        let dst = [DOMAIN_PREFIX, suffix].concat();
        for (label, data) in [(&b"dst"[..], &dst[..])]
            .into_iter()
            .chain(items.iter().copied())
        {
            input.extend_from_slice(&(label.len() as u64).to_le_bytes());
            input.extend_from_slice(label);
            input.extend_from_slice(&(data.len() as u64).to_le_bytes());
            input.extend_from_slice(data);
        }
        let mut shake = Shake128::default();
        shake.update(&input);
        let mut out = vec![0u8; n];
        shake.finalize_xof().read(&mut out);
        out
    }

    #[test]
    fn known_answers_of_the_matrix_oracles() {
        check_summary(
            &identifier_point(KAT, &identifier_digest()),
            (
                [496_402, 514_285, 814_601, 373_056],
                631_574,
                159_920,
                2_864_530_562,
                "83c01a4e4e6c40c17e20fbd030a2bfe853def93ca4d74d9cbcecf411bae4cb03",
            ),
        );
        check_summary(
            &h_mat(KAT, b""),
            (
                [545_446, 401_439, 109_968, 657_601],
                528_570,
                564_259,
                3_107_952_684,
                "eb1b192a6fba3de658597381af2f5d64b41b9214bb81a0a5d40eabeece90783d",
            ),
        );
        check_summary(
            &identifier_point(KAT, &counting_digest()),
            (
                [24_050, 949_323, 677_267, 672_253],
                285_799,
                385_935,
                2_967_721_726,
                "28dda871f4c553e056bd375f7fedd48bf85e6537bd3acc0cf1d928162754e408",
            ),
        );
        check_summary(
            &request_point(KAT, &counting_digest()),
            (
                [428_025, 418_361, 942_340, 678_679],
                105_245,
                615_441,
                2_927_140_858,
                "79f2ea330ea17730f898ebf167ab8aed56ec61870aac328a71b7ff534e74b9cf",
            ),
        );
        check_summary(
            &identifier_point(b"PCS-LATTICE-KAT2", &identifier_digest()),
            (
                [531_995, 678_842, 870_265, 822_108],
                475_009,
                276_185,
                2_856_260_866,
                "4296e8dc03ab533d2dc61675af5d0fcc319307f03dad728c25c61fdbe87db836",
            ),
        );
    }

    /// `id = Tag(K, x_0)` and the attestation tag `t = Tag(K, x_Q)` at a recipient point, for a
    /// fixed key, with the rounding errors.
    #[test]
    fn known_answers_of_the_tag_chain() {
        let key = kat_key();
        let counts = [-1i8, 0, 1].map(|v| key.coeffs().iter().filter(|&&x| x == v).count());
        assert_eq!(counts, [348, 328, 348]);
        assert_eq!(&key.coeffs()[..8], &[-1, -1, 1, -1, 1, 1, 1, 1]);

        let x0 = identifier_point(KAT, &identifier_digest());
        let (id, e0) = LWR.eval_with_error(&key, &x0).unwrap();
        assert_eq!(
            &id.entries()[..8],
            &[40_124, 45_340, 45_497, 37_072, 39_407, 5796, 34_078, 41_901]
        );
        assert_eq!(id.entries()[M - 1], 41_524);
        assert_eq!(
            hex(&Sha256::digest(id.to_bytes())),
            "8be2ced09c3f47fadf4110f242dd1c0aa7bd4ea01f53022ff836e210c2daf227"
        );
        assert_eq!(&e0.entries()[..8], &[-7, -7, 6, -2, 0, -2, -5, 3]);
        assert_eq!(e0.entries().iter().map(|&x| i32::from(x)).sum::<i32>(), -34);
        assert_eq!(
            e0.entries()
                .iter()
                .map(|&x| i32::from(x).pow(2))
                .sum::<i32>(),
            2858
        );

        let digest: [u8; 32] = Sha256::digest(b"x_Q of the known answers").into();
        let xq = request_point(KAT, &digest);
        check_summary(
            &xq,
            (
                [660_069, 503_211, 256_051, 178_542],
                814_747,
                446_670,
                2_934_527_322,
                "c1b4d631b87ce0e44f7f39c7e3f2676670838e134a2ce7ab0bf05b987f11a262",
            ),
        );
        let (t, e1) = LWR.eval_with_error(&key, &xq).unwrap();
        assert_eq!(
            &t.entries()[..8],
            &[59_292, 62_291, 39_066, 48_753, 3332, 31_645, 28_896, 21_133]
        );
        assert_eq!(t.entries()[M - 1], 51_009);
        assert_eq!(
            hex(&Sha256::digest(t.to_bytes())),
            "3a937362c115c7d96bfc64ac7da6514fc75d4d34e22ce018666e5af823fd669c"
        );
        assert_eq!(&e1.entries()[..8], &[6, 2, 2, -1, 6, -1, -6, 4]);
        assert_eq!(e1.entries().iter().map(|&x| i32::from(x)).sum::<i32>(), 97);
        assert_eq!(
            e1.entries()
                .iter()
                .map(|&x| i32::from(x).pow(2))
                .sum::<i32>(),
            3037
        );
    }

    /// `H_mat` is the documented byte string: SHAKE128 of the framed items, read as a
    /// little-endian bit string in 20-bit chunks (here: each 5-byte group as one 40-bit integer,
    /// split into its low and high halves), chunks below `q_t` accepted in order.
    #[test]
    fn h_mat_is_the_documented_byte_string() {
        let input = b"an input";
        let stream = shake_framed(
            b"/LATTICE-HMAT",
            &[(b"deployment", KAT), (b"input", input)],
            8 * 1024,
        );
        let mut want = Vec::new();
        for group in stream.as_chunks::<5>().0 {
            let v = group
                .iter()
                .rev()
                .fold(0u64, |acc, &b| (acc << 8) | u64::from(b));
            for chunk in [v & 0xf_ffff, v >> 20] {
                if chunk < u64::from(Q_T) {
                    want.push(u32::try_from(chunk).unwrap());
                }
            }
        }
        assert!(want.len() > 3000);
        let a = h_mat(KAT, input);
        assert_eq!(&a.entries()[..want.len()], &want[..]);
        // a rejected chunk occurred within the compared prefix (probability 1/16 per chunk)
        assert!(want.len() < 2 * stream.len() / 5);
    }

    /// `H_id` is `H_mat` under the 3-byte label `hid`, `H_req` under the 3-byte label `req`.
    #[test]
    fn the_points_are_h_mat_under_their_labels() {
        let d = counting_digest();
        let mut y = b"hid".to_vec();
        y.extend_from_slice(&d);
        assert_eq!(identifier_point(KAT, &d), h_mat(KAT, &y));
        let mut y = b"req".to_vec();
        y.extend_from_slice(&d);
        assert_eq!(request_point(KAT, &d), h_mat(KAT, &y));
        assert_eq!(H_ID_LABEL.len(), 3);
        assert_eq!(H_REQ_LABEL.len(), 3);
    }

    /// Separation: another deployment, another digest, another label give other outputs; in
    /// particular an identifier point is no recipient point, not even for the same digest.
    #[test]
    fn the_oracles_are_separated() {
        let d = identifier_digest();
        let x0 = identifier_point(KAT, &d);
        assert_ne!(x0, identifier_point(b"PCS-LATTICE-KAT2", &d));
        assert_ne!(x0, h_mat(KAT, &d));
        let mut e = d;
        e[31] ^= 1;
        assert_ne!(x0, identifier_point(KAT, &e));
        assert_ne!(request_point(KAT, &e), request_point(KAT, &d));
        // the same digest under H_id and H_req: other matrices
        assert_ne!(request_point(KAT, &d), x0);
        assert_ne!(
            request_point(KAT, &d),
            request_point(b"PCS-LATTICE-KAT2", &d)
        );
        // deterministic
        assert_eq!(x0, identifier_point(KAT, &d));
    }

    /// The entries of an identifier point look uniform (16 equal bins of `[0, q_t)`, each within
    /// 6 standard deviations). Evidence that the rejection sampling keeps the uniform
    /// distribution, not a proof.
    #[test]
    fn outputs_look_uniform() {
        let x0 = identifier_point(KAT, &identifier_digest());
        let mut bins = [0u32; 16];
        for &x in x0.entries() {
            bins[(x / (Q_T / 16)) as usize] += 1;
        }
        // 172,032 / 16 = 10,752 per bin, σ = √(10,752 · 15/16) ≈ 100.4
        assert!(
            bins.iter()
                .all(|&b| (10_752 - 603..=10_752 + 603).contains(&b)),
            "{bins:?}"
        );
    }
}
