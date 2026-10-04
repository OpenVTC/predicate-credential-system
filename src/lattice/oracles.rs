//! The random oracles of the lattice instantiation (construction.tex, "Random oracles of the
//! lattice tag", con:210; the predicate encoding, con:59-65), each bound to the deployment label
//! like the oracles of [`crate::hash`]:
//!
//! | paper | here | bytes ([`crate::lattice`]'s XOF, module `xof`) |
//! |---|---|---|
//! | $`H_{\mathsf{mat}} : \{0,1\}^* \to \mathbb Z_{q_t}^{m \times n}`$, "an extendable-output function and rejection-sampling each entry to be uniform in $`\mathbb Z_{q_t}`$" (con:210) | [`h_mat`] | SHAKE128 of `("dst", "PCS-V1/LATTICE-HMAT")`, `("deployment", label)`, `("input", y)`; consecutive 20-bit chunks below $`q_t`$, row-major |
//! | $`H_0(x) = H_{\mathsf{mat}}(\texttt{"tag"} \| x)`$ (con:210) | [`h0`] | $`y = \texttt{tag} \| x`$ (the label `tag` has the fixed length 3) |
//! | $`c_0 = H_0(\texttt{"identity"})`$ (con:59, con:112, con:210) | [`identity_point`] | $`y = \texttt{tagidentity}`$ |
//! | $`s_i = H_0(\langle id_i\rangle)`$ (con:134, con:157, con:171, con:210) | [`tag_point`] | $`y = \texttt{tag} \| \langle id_i \rangle`$, $`\langle id\rangle`$ = the 336-byte [`LWRTag`] encoding |
//! | $`\mathsf{EncPred}(f)`$ for `Σ-vSIS`: "the $`d`$ coefficients of $`\phi`$ from the first $`d`$ output bits of a random oracle on $`\texttt{"predicate"} \| \langle f \rangle`$, domain-separated from $`H_0`$" (con:65) | [`pred_enc`] | SHAKE128 of `("dst", "PCS-V1/LATTICE-PREDENC")`, `("deployment", label)`, `("input", "predicate" ‖ ⟨f⟩)`; bit $`i`$ (least significant first) is coefficient $`i`$ |
//!
//! Each item is framed as `LE64(|label|) ‖ label ‖ LE64(|data|) ‖ data` (module `xof`); the
//! labels and suffixes are ASCII. $`\langle f\rangle`$ is [`Predicate::canonical_bytes`]
//! (`LE32(threshold) ‖ LE64(|label|) ‖ label`).
//!
//! # The paper's requirements, and how these bytes meet them
//!
//! * **Uniform entries** (con:210): every accepted 20-bit chunk is uniform below $`q_t`$, so
//!   $`H_{\mathsf{mat}}`$ is a uniform matrix when SHAKE128 is modelled as a random oracle; this
//!   is the input distribution of lem:tag-lwr-short (bb:270-279) and of the weak
//!   pseudorandomness of `Tag_LWR`.
//! * **Injective identifier encoding whose image excludes `identity`** (con:210):
//!   $`\langle id\rangle`$ is the fixed-length (336-byte) tag encoding, injective, and never the
//!   8-byte string `identity`, so $`c_0`$ is never an attester point $`s_i`$ by construction.
//! * **Fixed-length labels** (con:210): the label `tag` of $`H_0`$ has length 3; the oracles
//!   $`H_{\mathsf{req}}`$ and $`H_{\mathsf{subj}}`$ of the PRC appendix would be
//!   $`H_{\mathsf{mat}}`$ under labels of the same length (e.g. `req`, `sbj`) with the exclusion
//!   counter of con:210. They are not implemented: the PRC is out of scope.
//! * **`EncPred` domain-separated from `H_0`, collision resistant** (con:65): a separate oracle
//!   suffix, and $`d = 1024`$ output bits. An adversary making $`Q`$ queries finds a collision
//!   with probability at most $`Q^2/2^{d+1}`$ in the random-oracle model (con:65); SHAKE128 itself
//!   has 128-bit collision resistance.
//!
//! # Cost
//!
//! An `H_mat` matrix is $`m n = 172{,}032`$ entries; a chunk is accepted with probability
//! $`q_t/2^{20} = 15/16`$, so it reads about $`172{,}032 \cdot 16/15 \cdot 2.5 = 458{,}752`$
//! bytes of SHAKE128 output: about 0.6 ms on an Apple M4 core, of which 0.35 ms is SHAKE128
//! itself. `EncPred` reads 128 bytes (under 1 µs). The construction derives $`c_0`$ once per
//! deployment and $`s_i`$ once per call.

use super::{
    D, M, Q_T,
    ring::BinaryPoly,
    xof::{HMAT_SUFFIX, PREDENC_SUFFIX, Xof},
};
use crate::{
    kiprf::lwr::{LWRTag, TagMatrix},
    pcs::Predicate,
};

/// The label of $`H_0`$ inside $`H_{\mathsf{mat}}`$'s input (con:210). Fixed length 3.
pub(crate) const H0_LABEL: &[u8] = b"tag";
/// The input of $`c_0 = H_0(\texttt{"identity"})`$ (con:59, con:210).
pub(crate) const IDENTITY: &[u8] = b"identity";
/// The prefix of `EncPred`'s input $`\texttt{"predicate"} \| \langle f\rangle`$ (con:62, con:65).
pub(crate) const PREDICATE: &[u8] = b"predicate";

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

/// $`H_0(x) = H_{\mathsf{mat}}(\texttt{"tag"} \| x)`$ (con:210).
#[must_use]
pub fn h0(deployment: &[u8], x: &[u8]) -> TagMatrix {
    h_mat(deployment, &[H0_LABEL, x].concat())
}

/// $`c_0 = H_0(\texttt{"identity"})`$, the point of the identifiers $`id = \mathsf{Tag}(usk, c_0)`$
/// (con:112, con:124, con:210).
#[must_use]
pub fn identity_point(deployment: &[u8]) -> TagMatrix {
    h0(deployment, IDENTITY)
}

/// $`s = H_0(\langle id\rangle)`$, the point of the attester tags and of the self-exclusion tag
/// for the identifier `id` (con:134, con:157, con:210). $`\langle id\rangle`$ is the 336-byte
/// encoding of [`LWRTag`].
#[must_use]
pub fn tag_point(deployment: &[u8], id: &LWRTag) -> TagMatrix {
    h0(deployment, &id.to_bytes())
}

/// $`\phi = \mathsf{EncPred}(f)`$, a binary polynomial (con:65): the first $`d = 1024`$ bits of
/// SHAKE128 on $`\texttt{"predicate"} \| \langle f\rangle`$ under the oracle suffix
/// `/LATTICE-PREDENC`; coefficient $`i`$ is bit $`i \bmod 8`$ (least significant first) of
/// output byte $`\lfloor i/8\rfloor`$. Collision resistant: SHAKE128 with $`d = 1024`$ output
/// bits gives $`\min(c/2, d/2) = 128`$ bits (capacity $`c = 256`$).
#[must_use]
pub fn pred_enc(deployment: &[u8], f: &Predicate) -> BinaryPoly {
    let mut xof = Xof::new(PREDENC_SUFFIX);
    xof.absorb(b"deployment", deployment)
        .absorb(b"input", &[PREDICATE, &f.canonical_bytes()].concat());
    let mut bytes = [0u8; BinaryPoly::BYTES];
    xof.finish().fill(&mut bytes);
    BinaryPoly::from_bytes(bytes)
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
            &identity_point(KAT),
            (
                [482_358, 65_488, 336_476, 223_542],
                515_568,
                343_167,
                2_804_724_483,
                "ec3111430ff9e7186edc12570763ecf27b297494dcb30109d1e9b61c678f260e",
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
            &tag_point(KAT, &LWRTag::from_entries([0; M])),
            (
                [614_355, 612_176, 283_401, 916_547],
                642_036,
                892_218,
                2_657_427_365,
                "f1e4425442e1561f7856b34bb2f212357df3c73282f223850af047b37f7436c6",
            ),
        );
        check_summary(
            &identity_point(b"PCS-LATTICE-KAT2"),
            (
                [639_487, 691_531, 586_486, 467_938],
                908_949,
                523_514,
                2_861_984_416,
                "5bb41d82e89a43bc1324fef64d250e7402ba4ffdcaad652fbbeaf991b87295ed",
            ),
        );
    }

    /// `id = Tag(K, c_0)`, `s = H_0(⟨id⟩)` and `id_{i→i} = Tag(K, s)` for a fixed key: the chain
    /// of `UKeyGen` and `Prove` (con:124-125, con:157), with the rounding errors.
    #[test]
    fn known_answers_of_the_tag_chain() {
        let key = kat_key();
        let counts = [-1i8, 0, 1].map(|v| key.coeffs().iter().filter(|&&x| x == v).count());
        assert_eq!(counts, [348, 328, 348]);
        assert_eq!(&key.coeffs()[..8], &[-1, -1, 1, -1, 1, 1, 1, 1]);

        let (id, e0) = LWR.eval_with_error(&key, &identity_point(KAT)).unwrap();
        assert_eq!(
            &id.entries()[..8],
            &[2103, 33_573, 734, 479, 17_264, 58_395, 43_288, 6023]
        );
        assert_eq!(id.entries()[M - 1], 47_060);
        assert_eq!(
            hex(&Sha256::digest(id.to_bytes())),
            "e4943987e9accd94191bb22a9236e97dc6742ab0d72d2a11a4cc8d185ac3ec65"
        );
        assert_eq!(&e0.entries()[..8], &[0, -3, 7, 3, 6, -2, -1, 0]);
        assert_eq!(e0.entries().iter().map(|&x| i32::from(x)).sum::<i32>(), 114);
        assert_eq!(
            e0.entries()
                .iter()
                .map(|&x| i32::from(x).pow(2))
                .sum::<i32>(),
            3450
        );

        let s = tag_point(KAT, &id);
        check_summary(
            &s,
            (
                [110_440, 962_016, 361_061, 366_864],
                233_915,
                413_170,
                3_056_796_031,
                "fa7cae47017914a86d8bb229533aa04368be03679152137109bd3d525385226d",
            ),
        );
        let (t0, e1) = LWR.eval_with_error(&key, &s).unwrap();
        assert_eq!(
            &t0.entries()[..8],
            &[
                39_472, 27_086, 15_114, 47_192, 49_015, 49_389, 10_031, 58_227
            ]
        );
        assert_eq!(t0.entries()[M - 1], 14_263);
        assert_eq!(
            hex(&Sha256::digest(t0.to_bytes())),
            "a60d7947faa4a9b3e8d860d574ba61abc165a58c1c5576cc265e2ca2932adedf"
        );
        assert_eq!(&e1.entries()[..8], &[-4, -2, -6, 2, -7, 2, 2, -5]);
        assert_eq!(e1.entries().iter().map(|&x| i32::from(x)).sum::<i32>(), -23);
        assert_eq!(
            e1.entries()
                .iter()
                .map(|&x| i32::from(x).pow(2))
                .sum::<i32>(),
            3337
        );
    }

    #[test]
    fn known_answers_of_the_predicate_encoding() {
        assert_eq!(
            hex(pred_enc(KAT, &Predicate::new(5, "members")).as_bytes()),
            "80602108a32f61e5cdc04e78eb3ba344f4dae31f8f0cdf9e1d7166e467a5eca47d69f41f857ef25b98322b\
             16feaf9e1e5415f7bd3b1a4c0f3b1f539265f069f9406ac363fb9f1fdd008950104d8008ed56346278fc87\
             a24bb95f225fb4d07306c6e47879a47bf6422dde7b42af885d968be4cbb5c6fffe0c8a94a9b237f18337"
        );
        assert_eq!(
            hex(pred_enc(KAT, &Predicate::root("root")).as_bytes()),
            "1ad13ff74f079a72dcfcb2bd2bd1e7ec075b1124112cdcf02863018b1a0fb83d4851a747699e6b3595d78c\
             9e68e2e97c066c7e9594b16a3acf28416dcbfc7b48fd4f2de29eba943747cd4cecc94a4d0a178ed1e6c9be\
             23bf1a1ab5ba09035d64fb6cef9dca375f84392277d701f0a70d7b10407d833f5fe2f10f9b14ce451039"
        );
        assert_eq!(
            hex(&pred_enc(KAT, &Predicate::new(1, "")).as_bytes()[..16]),
            "c28adbc05354e695e1be2b68c723322d"
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

    #[test]
    fn pred_enc_is_the_documented_byte_string() {
        let f = Predicate::new(3, "a label");
        let mut y = b"predicate".to_vec();
        y.extend_from_slice(&3u32.to_le_bytes());
        y.extend_from_slice(&7u64.to_le_bytes());
        y.extend_from_slice(b"a label");
        assert_eq!(y[9..], f.canonical_bytes()[..]);
        let want = shake_framed(
            b"/LATTICE-PREDENC",
            &[(b"deployment", KAT), (b"input", &y)],
            BinaryPoly::BYTES,
        );
        let phi = pred_enc(KAT, &f);
        assert_eq!(&phi.as_bytes()[..], &want[..]);
        for i in [0, 1, 7, 8, 500, D - 1] {
            assert_eq!(
                phi.coefficient(i),
                (want[i / 8] >> (i % 8)) & 1,
                "coefficient {i}"
            );
        }
    }

    /// `H_0` is `H_mat` under the 3-byte label `tag` (con:210), and the points of the construction
    /// are `H_0` at `identity` and at the tag encoding.
    #[test]
    fn the_points_are_h0_under_the_label_tag() {
        let mut id = [0u16; M];
        for (j, t) in id.iter_mut().enumerate() {
            *t = (j as u16).wrapping_mul(0x9e37);
        }
        let id = LWRTag::from_entries(id);
        assert_eq!(identity_point(KAT), h_mat(KAT, b"tagidentity"));
        assert_eq!(identity_point(KAT), h0(KAT, b"identity"));
        let mut y = b"tag".to_vec();
        y.extend_from_slice(&id.to_bytes());
        assert_eq!(tag_point(KAT, &id), h_mat(KAT, &y));
        assert_eq!(tag_point(KAT, &id), h0(KAT, &id.to_bytes()));
        assert_eq!(H0_LABEL.len(), 3);
    }

    /// Separation: another deployment, another input, another label give other outputs; in
    /// particular `c_0` is not the attester point of any identifier (con:210), not even of one
    /// whose encoding starts with the bytes `identity`, and `EncPred` is not `H_mat` on the
    /// same input.
    #[test]
    fn the_oracles_are_separated() {
        let c0 = identity_point(KAT);
        assert_ne!(c0, identity_point(b"PCS-LATTICE-KAT2"));
        assert_ne!(c0, h_mat(KAT, b"identity"));
        assert_ne!(c0, h0(KAT, b"identity\0"));
        let mut entries = [0u16; M];
        for (t, pair) in entries.iter_mut().zip(b"identity".chunks(2)) {
            *t = u16::from_le_bytes([pair[0], pair[1]]);
        }
        let id = LWRTag::from_entries(entries);
        assert!(id.to_bytes().starts_with(b"identity"));
        assert_ne!(tag_point(KAT, &id), c0);
        let mut other = entries;
        other[M - 1] = 1;
        assert_ne!(
            tag_point(KAT, &LWRTag::from_entries(other)),
            tag_point(KAT, &id)
        );

        let f = Predicate::new(5, "members");
        let phi = pred_enc(KAT, &f);
        assert_ne!(phi, pred_enc(b"PCS-LATTICE-KAT2", &f));
        assert_ne!(phi, pred_enc(KAT, &Predicate::new(4, "members")));
        assert_ne!(phi, pred_enc(KAT, &Predicate::new(5, "member")));
        assert_ne!(
            pred_enc(KAT, &Predicate::root("")),
            pred_enc(KAT, &Predicate::new(1, ""))
        );
        // the same input under the H_mat suffix gives other bytes
        let y = [PREDICATE, &f.canonical_bytes()].concat();
        let hmat_bytes = shake_framed(
            b"/LATTICE-HMAT",
            &[(b"deployment", KAT), (b"input", &y)],
            BinaryPoly::BYTES,
        );
        assert_ne!(&phi.as_bytes()[..], &hmat_bytes[..]);
        // deterministic
        assert_eq!(phi, pred_enc(KAT, &f));
        assert_eq!(c0, identity_point(KAT));
    }

    /// The entries of `c_0` and the bits of `EncPred` look uniform (16 equal bins of `[0, q_t)`,
    /// each within 6 standard deviations; the number of ones of `φ` likewise). Evidence that the
    /// rejection sampling keeps the uniform distribution, not a proof.
    #[test]
    fn outputs_look_uniform() {
        let c0 = identity_point(KAT);
        let mut bins = [0u32; 16];
        for &x in c0.entries() {
            bins[(x / (Q_T / 16)) as usize] += 1;
        }
        // 172,032 / 16 = 10,752 per bin, σ = √(10,752 · 15/16) ≈ 100.4
        assert!(
            bins.iter()
                .all(|&b| (10_752 - 603..=10_752 + 603).contains(&b)),
            "{bins:?}"
        );
        let ones: u32 = pred_enc(KAT, &Predicate::new(5, "members"))
            .as_bytes()
            .iter()
            .map(|b| b.count_ones())
            .sum();
        // 1024 bits, σ = 16
        assert!((512 - 96..=512 + 96).contains(&ones), "{ones}");
    }
}
