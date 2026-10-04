//! `Tag_LWR`, the short-key random-input LWR tag of the post-quantum instantiation
//! (building-blocks.tex, sec:inst-tag-lwr, bb:176-294; the short-key variant bb:256-257).
//! Feature `lattice`.
//!
//! | paper | here |
//! |---|---|
//! | key space $`S_{\beta_u}^n = \{K \in \mathbb Z^n : \|K\|_\infty \le \beta_u\}`$, $`\beta_u = 1`$, `TagKeyGen` uniform on it (bb:257) | `Key = `[`Ternary`] (the coefficient vector of `usk`, bb:808), [`KIPRF::keygen`] |
//! | inputs $`A \in \mathbb Z_{q_t}^{m \times n}`$, uniform: $`c_0 = H_0(\texttt{"identity"})`$ and $`s_i = H_0(\langle id_i\rangle)`$ (con:210) | [`TagMatrix`] ([`crate::lattice::oracles`]) |
//! | $`\mathsf{TagEval}(K, A) = \lfloor AK \rceil_p \in \mathbb Z_p^m`$, rounding "coefficientwise to the nearest element modulo $`p`$" (bb:218, bb:226-229) | [`KIPRF::eval`], [`LWR::eval_with_error`] |
//! | the rounding error $`e`$ with $`AK + e = \gamma T \bmod q_t`$, $`\|e\|_\infty \le \lfloor\gamma/2\rfloor`$ (bb:245-249) | [`RoundingError`], the witness of the tag clauses |
//! | "$`K`$ explains $`T`$ at $`A`$ within $`(\beta_u, \lfloor\gamma/2\rfloor)`$" (bb:266) | [`LWR::explains`] |
//! | $`\mathsf{ValidTag}(T, A) = [T \in \{0, \dots, p - 1\}^m]`$ (bb:232) | [`LWR::valid_tag`]; an invariant of [`LWRTag`] at $`p = 2^{16}`$ |
//!
//! The construction evaluates the tag in `UKeyGen` ($`id_i = \mathsf{Tag}(usk_i, c_0)`$,
//! con:124-125), in `Attest` ($`id_{j \to i} = \mathsf{Tag}(usk_j, s_i)`$, con:134) and in `Prove`
//! ($`id_{i \to i} = \mathsf{Tag}(usk_i, s_i)`$, con:157), and checks `ValidTag` on every tag it
//! receives (con:152, con:171).
//!
//! # In formulas
//!
//! For row $`j`$ with $`w_j = \langle a_j, K\rangle \bmod q_t \in [0, q_t)`$ and odd $`\gamma`$,
//!
//! ```math
//! T_j = \Bigl\lfloor \frac{w_j}{\gamma} + \frac12 \Bigr\rfloor \bmod p = \Bigl\lfloor \frac{2 w_j + \gamma}{2\gamma} \Bigr\rfloor \bmod p, \qquad e_j = \bigl(\gamma T_j - w_j\bigr) \bmod^{\pm} q_t \in [-\lfloor\gamma/2\rfloor, \lfloor\gamma/2\rfloor],
//! ```
//!
//! with no ties ($`w_j/\gamma + 1/2`$ is never an integer for odd $`\gamma`$), so that
//! $`AK + e = \gamma T \bmod q_t`$ row by row. When $`\lfloor w_j/\gamma + 1/2\rfloor = p`$
//! ($`w_j \ge q_t - \lfloor\gamma/2\rfloor`$) the tag entry is its canonical representative
//! $`0`$, which $`\gamma p = q_t \equiv 0`$ makes consistent. The statements prove each row as
//! $`\mathrm{ct}(\sigma(a_j)\,usk + X^{-8(j \bmod 128)} e_{\lfloor j/128\rfloor}) = \gamma T_j \bmod q_t`$
//! (the error vector as two subring elements of degree 128) with the EXACT bound
//! $`\|e\|_\infty \le 7`$ (`Norm::LinfExact`, rem:relaxed-extraction, con:213-215): by
//! lem:tag-lwr-determinism (bb:282-287) a key then explains at most one valid tag per matrix,
//! which is what makes distinct tags count distinct attesters. By lem:tag-lwr-short (bb:270-279)
//! at $`m = 168`$ ($`\psi = q_t/30 = 2^{15}`$, $`15m \ge 1024\log_2 5 + 128`$), no two distinct
//! ternary keys explain the same tag at a uniform matrix, except with probability at most
//! $`2^{-128}`$ over the matrix.
//!
//! # Exactness and cost
//!
//! The inner products are exact in `i32`: $`|\langle a_j, K\rangle| \le n (q_t - 1) \beta_u =
//! 1{,}006{,}631{,}936 < 2^{31}`$ (a compile-time assertion), which lets them vectorise. An
//! evaluation is $`m n = 172{,}032`$ multiply-adds and $`m`$ roundings, about 10 µs on an Apple
//! M4 core; deriving the matrix (`H_mat`, about 0.6 ms) costs far more.
//!
//! # Side channels
//!
//! The evaluation is written without branches, early exits or table lookups on the key, and it
//! reduces with the constant divisors $`q_t`$ and $`2\gamma`$, which compilers turn into
//! multiplications. In the aarch64 release build (rustc 1.99) the compiled evaluation has no
//! division instruction and branches only on loop counters, the public sizes of the key and the
//! matrix, an address-alias check and the final refusal of a key outside the key space, which a
//! [`Ternary`] is only after it was wiped. Whether the multiplications run in data-independent
//! time is a property of the CPU, which this crate does not configure. `TagKeyGen` reveals only
//! the number of rejected bytes ([`Ternary::sample`]).

use core::fmt;

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::rand::{CryptoRng, RngCore};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use super::KIPRF;
use crate::{
    error::Error,
    lattice::{BETA_U, D, E_BOUND, GAMMA, M, P, Q_T, Ternary},
};

/// The short-key `Tag_LWR` with the constants of tag set R ([`crate::lattice`]): $`n = 1024`$,
/// $`q_t = 983{,}040`$, $`p = 2^{16}`$, $`\gamma = 15`$, $`m = 168`$, $`\beta_u = 1`$.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LWR;

/// A tag input $`A \in \mathbb Z_{q_t}^{m \times n}`$: $`m = 168`$ rows of $`n = 1024`$ entries in
/// $`[0, q_t)`$, row-major. Public.
///
/// Encoding (only for digests, e.g. of $`c_0`$ in the digest of `pp`): the entries in row-major
/// order at 20 bits each, little-endian bit packing (430,080 bytes). Matrices never travel: both
/// sides derive them from `H_mat`.
#[derive(Clone, PartialEq, Eq)]
pub struct TagMatrix(Vec<u32>);

impl TagMatrix {
    /// $`m`$, the number of rows.
    pub const ROWS: usize = M;
    /// $`n`$, the number of columns.
    pub const COLUMNS: usize = D;

    /// From the $`m \cdot n`$ entries in row-major order.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] for another number of entries; [`Error::InvalidTag`] for an
    /// entry $`\ge q_t`$.
    pub fn from_entries(entries: Vec<u32>) -> Result<Self, Error> {
        if entries.len() != M * D {
            return Err(Error::LengthMismatch {
                expected: M * D,
                actual: entries.len(),
            });
        }
        if entries.iter().any(|&x| x >= Q_T) {
            return Err(Error::InvalidTag);
        }
        Ok(Self(entries))
    }

    /// The entries in row-major order.
    #[must_use]
    pub fn entries(&self) -> &[u32] {
        &self.0
    }

    /// Row $`a_j`$.
    ///
    /// # Panics
    /// If $`j \ge m`$.
    #[must_use]
    pub fn row(&self, j: usize) -> &[u32] {
        &self.0[j * D..(j + 1) * D]
    }

    /// The rows $`a_0, \dots, a_{m-1}`$.
    pub fn rows(&self) -> impl ExactSizeIterator<Item = &[u32]> {
        self.row_arrays().iter().map(<[u32; D]>::as_slice)
    }

    /// The $`m`$ rows as arrays (the invariant: exactly $`m \cdot n`$ entries).
    fn row_arrays(&self) -> &[[u32; D]] {
        self.0.as_chunks::<D>().0
    }

    /// The digest encoding (type docs): 20-bit little-endian packing, row-major.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.0.len() * 20 / 8);
        let mut acc = 0u64;
        let mut bits = 0u32;
        for &x in &self.0 {
            acc |= u64::from(x) << bits;
            bits += 20;
            while bits >= 8 {
                out.push(acc as u8);
                acc >>= 8;
                bits -= 8;
            }
        }
        if bits > 0 {
            out.push(acc as u8);
        }
        out
    }
}

impl fmt::Debug for TagMatrix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TagMatrix({M} × {D})")
    }
}

/// A tag $`T \in \mathbb Z_p^m`$ in its canonical encoding: $`m = 168`$ entries in
/// $`\{0, \dots, p - 1\}`$. At $`p = 2^{16}`$ every `u16` is such an entry, so the non-canonical
/// encodings $`T + pz`$ that `ValidTag` exists to refuse (sec:inst-tag-lwr) cannot be
/// represented. The identifier `id`, the attester tags $`id_{j \to i}`$ and the self-exclusion
/// tag $`id_{i \to i}`$ are values of this type. Public.
///
/// Encoding: the entries as 2-byte little-endian integers, in order (336 bytes). Equality and
/// hashing compare the entries: the distinctness and self-exclusion checks of `CheckAtts_P`
/// compare encodings, and here an encoding IS the tag.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct LWRTag([u16; M]);

impl LWRTag {
    /// Bytes of the encoding.
    pub const BYTES: usize = 2 * M;

    /// The tag with these entries.
    #[must_use]
    pub fn from_entries(entries: [u16; M]) -> Self {
        Self(entries)
    }

    /// The entries $`T_0, \dots, T_{m-1}`$.
    #[must_use]
    pub fn entries(&self) -> &[u16; M] {
        &self.0
    }

    /// The encoding ([`Self::BYTES`] bytes).
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.iter().flat_map(|t| t.to_le_bytes()).collect()
    }

    /// Decodes the encoding; every byte string of [`Self::BYTES`] bytes is a tag.
    ///
    /// # Errors
    /// [`Error::Serialization`] for another length.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != Self::BYTES {
            return Err(Error::Serialization(format!(
                "LWR tag: {} bytes, expected {}",
                bytes.len(),
                Self::BYTES
            )));
        }
        let mut entries = [0u16; M];
        for (t, pair) in entries.iter_mut().zip(bytes.as_chunks::<2>().0) {
            *t = u16::from_le_bytes(*pair);
        }
        Ok(Self(entries))
    }
}

impl fmt::Debug for LWRTag {
    /// The first four entries in hex.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LWRTag({:04x}{:04x}{:04x}{:04x}..)",
            self.0[0], self.0[1], self.0[2], self.0[3]
        )
    }
}

impl CanonicalSerialize for LWRTag {
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

impl Valid for LWRTag {
    const TRIVIAL_CHECK: bool = true;

    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for LWRTag {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = [0u8; Self::BYTES];
        reader.read_exact(&mut bytes)?;
        Self::from_bytes(&bytes).map_err(|_| SerializationError::InvalidData)
    }
}

/// The rounding error $`e = \gamma T - AK \bmod^{\pm} q_t \in [-7, 7]^m`$ of an evaluation: the
/// witness of the tag clauses. Secret (with $`A`$ and $`T`$ it constrains the key): wiped on drop,
/// redacted in `Debug`.
#[derive(Clone)]
pub struct RoundingError([i8; M]);

impl RoundingError {
    /// From its entries, each in $`[-\lfloor\gamma/2\rfloor, \lfloor\gamma/2\rfloor]`$. For
    /// [`LWR::eval_with_error`] and for tests that build false witnesses: the entries are NOT
    /// checked here ([`LWR::explains`] and the proof system check them).
    #[must_use]
    pub fn from_entries(entries: [i8; M]) -> Self {
        Self(entries)
    }

    /// The entries $`e_0, \dots, e_{m-1}`$.
    #[must_use]
    pub fn entries(&self) -> &[i8; M] {
        &self.0
    }
}

impl Zeroize for RoundingError {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl Drop for RoundingError {
    fn drop(&mut self) {
        self.zeroize();
    }
}

impl ZeroizeOnDrop for RoundingError {}

impl fmt::Debug for RoundingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("RoundingError(<redacted>)")
    }
}

// ---------------------------------------------------------------------------------------------
// TagEval
// ---------------------------------------------------------------------------------------------

// The inner products are exact in `i32`: |⟨a_j, K⟩| ≤ n (q_t − 1) β_u < 2^31, and after adding
// OFFSET = n q_t they lie in (0, 2^31).
const _: () = {
    assert!((D as u64) * (Q_T as u64 - 1) * BETA_U < 1 << 31);
    assert!(2 * (D as u64) * (Q_T as u64) < 1 << 31);
    assert!(BETA_U == 1 && GAMMA % 2 == 1);
    // the rounding below: 2 u + γ and γ p fit in u32, and P is a power of two
    assert!(2 * (Q_T as u64) + GAMMA as u64 <= u32::MAX as u64 && P.is_power_of_two());
};

/// $`n q_t \equiv 0 \pmod{q_t}`$: added to an inner product $`w`$, $`|w| < n q_t`$, it gives a
/// representative of $`w \bmod q_t`$ in $`(0, 2^{31})`$.
const OFFSET: i32 = (D as u32 * Q_T) as i32;

/// The key as `i32` coefficients for the inner products. `false` outside
/// $`S_1^n = \{-1, 0, 1\}^n`$, which for a [`Ternary`] means a wiped key (no coefficients): its
/// constructors and decoders admit nothing else. Branch-free in the coefficients.
fn widen(key: &Ternary, out: &mut [i32; D]) -> bool {
    let Ok(coeffs) = <&[i8; D]>::try_from(key.coeffs()) else {
        return false;
    };
    let mut outside = 0u8;
    for (o, &x) in out.iter_mut().zip(coeffs) {
        outside |= u8::from(x.unsigned_abs() > 1);
        *o = i32::from(x);
    }
    outside == 0
}

/// $`\langle a_j, K\rangle`$ over the integers. Exact: the wrapping operations never wrap (the
/// compile-time assertion above), and they let the compiler vectorise without overflow checks.
#[inline]
fn inner(row: &[u32; D], key: &[i32; D]) -> i32 {
    row.iter().zip(key).fold(0, |acc, (&a, &k)| {
        acc.wrapping_add((a as i32).wrapping_mul(k))
    })
}

/// $`(T_j, e_j)`$ from the inner product $`w = \langle a_j, K\rangle`$, $`|w| < n q_t`$ (module
/// docs). Branch-free: two divisions by constants.
#[inline]
fn round(w: i32) -> (u16, i8) {
    // u = w mod q_t ∈ [0, q_t)
    let u = (w + OFFSET) as u32 % Q_T;
    // ⌊u/γ + 1/2⌋ ∈ [0, p], exact (no ties for odd γ)
    let t = (2 * u + GAMMA) / (2 * GAMMA);
    // γ t − u ∈ [−⌊γ/2⌋, ⌊γ/2⌋] as an integer; it is ≡ γ (t mod p) − w (mod q_t) since γ p = q_t
    let e = (GAMMA * t) as i32 - u as i32;
    debug_assert!(u64::from(e.unsigned_abs()) <= E_BOUND);
    ((t % P) as u16, e as i8)
}

impl LWR {
    /// $`(T, e)`$ with $`T = \mathsf{TagEval}(K, A) = \lfloor AK \rceil_p`$ (bb:226-229) and the
    /// rounding error $`e = \gamma T - AK \bmod^{\pm} q_t`$, $`\|e\|_\infty \le 7`$ (bb:245-249;
    /// module docs). `None` only for a key outside $`S_{\beta_u}^n`$, i.e. a wiped [`Ternary`].
    ///
    /// Bit for bit the evaluation of the validation harness the parameter sets were derived and
    /// checked with (`pcs.rs:129-142`), which a unit test runs as the reference.
    ///
    /// The widened copy of the key is wiped before returning. Like every value returned by
    /// value in Rust, the error is moved out of this function's frame by a copy, and that stale
    /// copy is not wiped (the crate's limitation "temporaries may stay on the stack").
    #[must_use]
    pub fn eval_with_error(
        &self,
        key: &Ternary,
        input: &TagMatrix,
    ) -> Option<(LWRTag, RoundingError)> {
        let mut k = Zeroizing::new([0i32; D]);
        if !widen(key, &mut k) {
            return None;
        }
        let mut tag = [0u16; M];
        let mut error = RoundingError([0; M]);
        for ((t, e), row) in tag
            .iter_mut()
            .zip(error.0.iter_mut())
            .zip(input.row_arrays())
        {
            (*t, *e) = round(inner(row, &k));
        }
        Some((LWRTag(tag), error))
    }

    /// $`\mathsf{ValidTag}(T, A) = [T \in \{0, \dots, p - 1\}^m]`$ (bb:232). True for every
    /// [`LWRTag`] at $`p = 2^{16}`$; evaluated on every tag all the same, as the public pre-check
    /// of `VerifyProofAtt` (con:152) and `VerifyProof` (con:171). The matrix $`A`$ is not needed.
    #[must_use]
    pub fn valid_tag(&self, tag: &LWRTag) -> bool {
        tag.0.iter().all(|&t| u32::from(t) < P)
    }

    /// Whether the key $`K`$ explains the tag $`T`$ at $`A`$ within
    /// $`(\beta_u, \lfloor\gamma/2\rfloor)`$ with the error $`e`$ (bb:266):
    /// $`\|K\|_\infty \le 1`$, $`\|e\|_\infty \le \lfloor\gamma/2\rfloor = 7`$ and
    /// $`AK + e = \gamma T \pmod{q_t}`$, with $`\mathsf{ValidTag}(T, A)`$. This is the relation the
    /// tag clauses of `R_att` and `R_issue` prove, checked on plain integers.
    ///
    /// Not used by the protocol (the proof system checks the relation); for tests and for
    /// honest-prover sanity checks. Not constant time in the error. By lem:tag-lwr-determinism
    /// (bb:282-287), a key explains at most one valid tag at a given matrix: the one of
    /// [`Self::eval_with_error`].
    #[must_use]
    pub fn explains(
        &self,
        key: &Ternary,
        input: &TagMatrix,
        tag: &LWRTag,
        error: &RoundingError,
    ) -> bool {
        let mut k = Zeroizing::new([0i32; D]);
        if !widen(key, &mut k) || !self.valid_tag(tag) {
            return false;
        }
        input
            .row_arrays()
            .iter()
            .zip(tag.0.iter().zip(error.0.iter()))
            .all(|(row, (&t, &e))| {
                let lhs =
                    i64::from(inner(row, &k)) + i64::from(e) - i64::from(GAMMA * u32::from(t));
                u64::from(e.unsigned_abs()) <= E_BOUND && lhs.rem_euclid(i64::from(Q_T)) == 0
            })
    }
}

impl KIPRF for LWR {
    /// The coefficient vector of `usk`, uniform on $`\{-1, 0, 1\}^n`$.
    type Key = Ternary;
    /// $`A \in \mathbb Z_{q_t}^{m \times n}`$.
    type Input = TagMatrix;
    /// $`T \in \mathbb Z_p^m`$.
    type Output = LWRTag;

    /// `TagKeyGen`: uniform on $`S_{\beta_u}^n = \{-1, 0, 1\}^n`$ (bb:257; [`Ternary::sample`],
    /// exact).
    fn keygen<R: RngCore + CryptoRng + ?Sized>(&self, rng: &mut R) -> Self::Key {
        Ternary::sample(rng)
    }

    /// `TagEval(K, A) = ⌊AK⌉_p`: [`LWR::eval_with_error`] without the error (which is wiped).
    /// Total on the key space: `Tag_LWR` has no `⊥`.
    fn eval(&self, key: &Self::Key, input: &Self::Input) -> Option<Self::Output> {
        self.eval_with_error(key, input).map(|(tag, _error)| tag)
    }
}

#[cfg(test)]
mod tests {
    use rand::{Rng, SeedableRng, rngs::StdRng};

    use super::*;
    use crate::serialization::{from_bytes, to_bytes};

    /// The harness's `tag_eval` (pcs-128-v2/setR/harness/src/pcs.rs:129-142), verbatim in
    /// `i128`: the evaluation the parameter sets and the 82/94-check flows were validated with.
    fn harness_tag_eval(usk: &[i8], a: &TagMatrix) -> (Vec<i128>, Vec<i128>) {
        let (gamma, pt, qt) = (i128::from(GAMMA), i128::from(P), i128::from(Q_T));
        let centred = |x: i128, m: i128| {
            let r = x.rem_euclid(m);
            if r > m / 2 { r - m } else { r }
        };
        let mut t = Vec::with_capacity(M);
        let mut e = Vec::with_capacity(M);
        for row in a.rows() {
            let w: i128 = row
                .iter()
                .zip(usk)
                .map(|(&x, &y)| i128::from(x) * i128::from(y))
                .sum();
            let tj = ((2 * w.rem_euclid(qt) + gamma) / (2 * gamma)).rem_euclid(pt);
            let ej = centred(gamma * tj - w, qt);
            assert!(ej.abs() <= (gamma - 1) / 2, "honest rounding error");
            t.push(tj);
            e.push(ej);
        }
        (t, e)
    }

    fn random_matrix(rng: &mut StdRng) -> TagMatrix {
        TagMatrix::from_entries((0..M * D).map(|_| rng.gen_range(0..Q_T)).collect()).unwrap()
    }

    /// A random matrix whose rows `j < first.len()` start with `first[j]`.
    fn matrix_with_first_column(first: &[u32], rng: &mut StdRng) -> TagMatrix {
        let mut entries: Vec<u32> = (0..M * D).map(|_| rng.gen_range(0..Q_T)).collect();
        for (j, &x) in first.iter().enumerate() {
            entries[j * D] = x;
        }
        TagMatrix::from_entries(entries).unwrap()
    }

    /// The key `sign · X^0`: then `⟨a_j, K⟩ = sign · a_{j,0}`.
    fn unit_key(sign: i8) -> Ternary {
        let mut c = vec![0i8; D];
        c[0] = sign;
        Ternary::from_coeffs(&c).unwrap()
    }

    /// Checks `(T, e)` against the harness and against the relation `AK + e = γT (mod q_t)`,
    /// `|e| ≤ 7`, `T < p` with an independent inner product.
    fn check_against_references(key: &Ternary, a: &TagMatrix) -> (LWRTag, RoundingError) {
        let (tag, e) = LWR.eval_with_error(key, a).unwrap();
        let (want_t, want_e) = harness_tag_eval(key.coeffs(), a);
        for j in 0..M {
            assert_eq!(i128::from(tag.0[j]), want_t[j], "T_{j}");
            assert_eq!(i128::from(e.0[j]), want_e[j], "e_{j}");
            let w: i64 = a
                .row(j)
                .iter()
                .zip(key.coeffs())
                .map(|(&x, &k)| i64::from(x) * i64::from(k))
                .sum();
            let lhs = w + i64::from(e.0[j]) - i64::from(GAMMA) * i64::from(tag.0[j]);
            assert_eq!(lhs.rem_euclid(i64::from(Q_T)), 0, "row {j}");
            assert!(i64::from(e.0[j]).unsigned_abs() <= E_BOUND);
        }
        assert!(LWR.explains(key, a, &tag, &e));
        assert_eq!(LWR.eval(key, a), Some(tag.clone()));
        (tag, e)
    }

    #[test]
    fn tags_encode_as_little_endian_entries() {
        let mut entries = [0u16; M];
        entries[0] = 0x1234;
        entries[M - 1] = 0xffff;
        let tag = LWRTag::from_entries(entries);
        let bytes = to_bytes(&tag).unwrap();
        assert_eq!(bytes.len(), LWRTag::BYTES);
        assert_eq!(&bytes[..2], &[0x34, 0x12]);
        assert_eq!(&bytes[LWRTag::BYTES - 2..], &[0xff, 0xff]);
        assert_eq!(from_bytes::<LWRTag>(&bytes).unwrap(), tag);
        assert!(from_bytes::<LWRTag>(&bytes[1..]).is_err());
        assert_eq!(format!("{tag:?}"), "LWRTag(1234000000000000..)");
    }

    #[test]
    fn matrices_check_their_entries() {
        assert!(TagMatrix::from_entries(vec![0; M * D - 1]).is_err());
        let mut entries = vec![0u32; M * D];
        entries[5] = Q_T;
        assert_eq!(
            TagMatrix::from_entries(entries.clone()),
            Err(Error::InvalidTag)
        );
        entries[5] = Q_T - 1;
        entries[D] = 7;
        let a = TagMatrix::from_entries(entries).unwrap();
        assert_eq!(a.row(1)[0], 7);
        assert_eq!(a.rows().len(), M);
        assert_eq!(a.row_arrays().len(), M);
        let bytes = a.to_bytes();
        assert_eq!(bytes.len(), M * D * 20 / 8);
        // entry 5 = q_t - 1 = 0xeffff at bits [100, 120)
        assert_eq!(&bytes[12..15], &[0xf0, 0xff, 0xef]);
    }

    /// The evaluation equals the harness's on random keys and matrices, and satisfies the
    /// relation of the tag clauses.
    #[test]
    fn evaluation_matches_the_harness_and_the_relation() {
        let mut rng = StdRng::seed_from_u64(0x1a01);
        for _ in 0..4 {
            let a = random_matrix(&mut rng);
            for _ in 0..4 {
                let key = LWR.keygen(&mut rng);
                check_against_references(&key, &a);
            }
        }
    }

    /// Rows crafted at the rounding boundaries (module docs): `⟨a, K⟩ ≡ γt + 7` rounds down to
    /// `t` with `e = −7`, `γt + 8` up to `t + 1` with `e = 7`, and at `t = p − 1` the round-up
    /// wraps to the canonical `0`.
    #[test]
    fn rounding_at_the_boundaries() {
        let mut rng = StdRng::seed_from_u64(0x1a02);
        let g = GAMMA;
        // (a_{j,0}, T_j, e_j) under K = X^0
        let cases: [(u32, u16, i8); 12] = [
            (0, 0, 0),
            (7, 0, -7),
            (8, 1, 7),
            (g, 1, 0),
            (g * 1234 + 7, 1234, -7),
            (g * 1234 + 8, 1235, 7),
            (g * 40_000, 40_000, 0),
            (g * (P - 1), 0xffff, 0),
            (g * (P - 1) + 7, 0xffff, -7),
            (g * (P - 1) + 8, 0, 7),
            (Q_T - 1, 0, 1),
            (1, 0, -1),
        ];
        let first: Vec<u32> = cases.iter().map(|c| c.0).collect();
        let a = matrix_with_first_column(&first, &mut rng);
        let (tag, e) = check_against_references(&unit_key(1), &a);
        for (j, &(_, t, err)) in cases.iter().enumerate() {
            assert_eq!((tag.0[j], e.0[j]), (t, err), "case {j}");
        }
        // under K = −X^0, ⟨a_j, K⟩ = −a_{j,0}: the negative inner products wrap modulo q_t
        let neg: [(u32, u16, i8); 5] = [
            (1, 0, 1),
            (7, 0, 7),
            (8, 0xffff, -7),
            (g, 0xffff, 0),
            (Q_T - 1, 0, -1),
        ];
        let first: Vec<u32> = neg.iter().map(|c| c.0).collect();
        let a = matrix_with_first_column(&first, &mut rng);
        let (tag, e) = check_against_references(&unit_key(-1), &a);
        for (j, &(_, t, err)) in neg.iter().enumerate() {
            assert_eq!((tag.0[j], e.0[j]), (t, err), "negative case {j}");
        }
    }

    /// The largest inner products in absolute value, `±n (q_t − 1)`, and their neighbours are
    /// exact (the `i32` argument of the module docs).
    #[test]
    fn extreme_inner_products_are_exact() {
        let ones = Ternary::from_coeffs(&[1; D]).unwrap();
        let minus = Ternary::from_coeffs(&[-1; D]).unwrap();
        let alternating =
            Ternary::from_coeffs(&(0..D).map(|i| [1, -1, 0][i % 3]).collect::<Vec<_>>()).unwrap();
        for fill in [Q_T - 1, Q_T - 2, 0, 1, Q_T / 2] {
            let a = TagMatrix::from_entries(vec![fill; M * D]).unwrap();
            for key in [&ones, &minus, &alternating, &Ternary::zero()] {
                check_against_references(key, &a);
            }
        }
        // w = n (q_t − 1) = 1,006,631,936: u = 982,016, T = round(65,467.73) = 65,468, e = 4
        let a = TagMatrix::from_entries(vec![Q_T - 1; M * D]).unwrap();
        let (tag, e) = LWR.eval_with_error(&ones, &a).unwrap();
        assert_eq!((tag.0[0], e.0[0]), (65_468, 4));
        assert_eq!(
            round(i32::try_from(D as u64 * u64::from(Q_T - 1)).unwrap()),
            (65_468, 4)
        );
        // w = −n (q_t − 1) ≡ 1,024: T = round(68.27) = 68, e = 1020 − 1024 = −4
        let (tag, e) = LWR.eval_with_error(&minus, &a).unwrap();
        assert_eq!((tag.0[0], e.0[0]), (68, -4));
    }

    /// Every rounding error in `[−7, 7]` occurs (and nothing else does): random inner products
    /// are uniform modulo γ.
    #[test]
    fn every_rounding_error_occurs() {
        let mut rng = StdRng::seed_from_u64(0x1a03);
        let a = random_matrix(&mut rng);
        let mut seen = [0usize; 15];
        for _ in 0..8 {
            let (_, e) = LWR.eval_with_error(&LWR.keygen(&mut rng), &a).unwrap();
            for &x in e.entries() {
                seen[usize::try_from(i64::from(x) + 7).unwrap()] += 1;
            }
        }
        // 8 · 168 = 1344 errors, about 90 per value
        assert!(seen.iter().all(|&c| c > 30), "{seen:?}");
    }

    /// `None` exactly outside the key space: a wiped key has no coefficients.
    #[test]
    fn a_wiped_key_has_no_tag() {
        let mut rng = StdRng::seed_from_u64(0x1a04);
        let a = random_matrix(&mut rng);
        let mut key = LWR.keygen(&mut rng);
        let (tag, e) = LWR.eval_with_error(&key, &a).unwrap();
        assert!(LWR.explains(&key, &a, &tag, &e));
        key.zeroize();
        assert!(LWR.eval_with_error(&key, &a).is_none());
        assert_eq!(LWR.eval(&key, &a), None);
        assert!(!LWR.explains(&key, &a, &tag, &e));
        // the zero key is a key (TagKeyGen outputs it with probability 3^-1024) and has a tag
        assert_eq!(
            LWR.eval(&Ternary::zero(), &a),
            Some(LWRTag::from_entries([0; M]))
        );
    }

    /// `TagKeyGen` is uniform on `{−1, 0, 1}^n` (bb:257): frequencies on 64 keys, and fresh keys.
    #[test]
    fn keygen_is_uniform_on_the_key_space() {
        let mut rng = StdRng::seed_from_u64(0x1a05);
        let keys: Vec<Ternary> = (0..64).map(|_| LWR.keygen(&mut rng)).collect();
        let mut counts = [0usize; 3];
        for key in &keys {
            assert_eq!(key.coeffs().len(), D);
            for &x in key.coeffs() {
                counts[usize::try_from(x + 1).unwrap()] += 1;
            }
        }
        // 65,536 coefficients, each value 21,845 ± 6σ (σ ≈ 120.7)
        assert!(
            counts
                .iter()
                .all(|&c| (21_845 - 725..=21_845 + 725).contains(&c)),
            "{counts:?}"
        );
        for i in 0..keys.len() {
            for j in i + 1..keys.len() {
                assert_ne!(keys[i], keys[j]);
            }
        }
    }

    /// Determinism, and key injectivity on samples (lem:tag-lwr-short is the proof; this is
    /// evidence): distinct keys, including keys that differ in one coefficient, give distinct
    /// tags at a common uniform matrix.
    #[test]
    fn tags_are_deterministic_and_distinct_keys_give_distinct_tags() {
        let mut rng = StdRng::seed_from_u64(0x1a06);
        let a = random_matrix(&mut rng);
        let mut keys: Vec<Ternary> = (0..24).map(|_| LWR.keygen(&mut rng)).collect();
        // neighbours of keys[0]: one coefficient changed by 1 and by 2
        for (i, delta) in [(0usize, 1i8), (517, 2), (1023, 1)] {
            let mut c = keys[0].coeffs().to_vec();
            c[i] = if c[i] + delta > 1 {
                c[i] + delta - 3
            } else {
                c[i] + delta
            };
            keys.push(Ternary::from_coeffs(&c).unwrap());
        }
        keys.push(Ternary::zero());
        let tags: Vec<LWRTag> = keys.iter().map(|k| LWR.eval(k, &a).unwrap()).collect();
        for (key, tag) in keys.iter().zip(&tags) {
            assert_eq!(&LWR.eval(key, &a).unwrap(), tag);
        }
        for i in 0..keys.len() {
            for j in i + 1..keys.len() {
                assert_ne!(keys[i], keys[j]);
                assert_ne!(tags[i], tags[j], "keys {i} and {j} collide");
            }
        }
    }

    /// `ValidTag` holds for every tag: exhaustively over one entry, through the encoding.
    #[test]
    fn valid_tag_holds_for_every_encoding() {
        let mut entries = [0x5a5au16; M];
        for v in 0..=u16::MAX {
            entries[0] = v;
            entries[M - 1] = v.rotate_left(3);
            let tag = LWRTag::from_bytes(&LWRTag::from_entries(entries).to_bytes()).unwrap();
            assert_eq!(tag.entries(), &entries);
            assert!(LWR.valid_tag(&tag));
        }
    }

    /// [`LWR::explains`] is the relation of the tag clauses: it accepts the honest `(T, e)` and
    /// refuses a changed tag, a changed error, an error outside `[−7, 7]` and another key.
    #[test]
    fn explains_is_the_relation_of_the_tag_clauses() {
        let mut rng = StdRng::seed_from_u64(0x1a07);
        let a = random_matrix(&mut rng);
        let key = LWR.keygen(&mut rng);
        let (tag, e) = LWR.eval_with_error(&key, &a).unwrap();
        assert!(LWR.explains(&key, &a, &tag, &e));
        // T_0 ± 1 with e_0 ± γ satisfies AK + e = γT (mod q_t) but |e_0| > 7
        let mut t1 = *tag.entries();
        let mut e1 = *e.entries();
        t1[0] = t1[0].wrapping_add(1);
        e1[0] += 15;
        assert!(!LWR.explains(&key, &a, &LWRTag::from_entries(t1), &RoundingError(e1)));
        // a changed error, a changed tag entry
        let mut e2 = *e.entries();
        e2[M - 1] = if e2[M - 1] == 7 { 6 } else { e2[M - 1] + 1 };
        assert!(!LWR.explains(&key, &a, &tag, &RoundingError(e2)));
        let mut t3 = *tag.entries();
        t3[100] ^= 1;
        assert!(!LWR.explains(&key, &a, &LWRTag::from_entries(t3), &e));
        // another key (the honest error of the other key does not help either)
        let other = LWR.keygen(&mut rng);
        let (_, e_other) = LWR.eval_with_error(&other, &a).unwrap();
        assert!(!LWR.explains(&other, &a, &tag, &e));
        assert!(!LWR.explains(&other, &a, &tag, &e_other));
    }

    /// lem:tag-lwr-determinism, second claim (bb:283): with an error bound of
    /// `⌈γ/2⌉ = 8` instead of the exact `⌊γ/2⌋ = 7`, a row with `⟨a, K⟩ ≡ γt + 7` is explained by
    /// `t` (`e = −7`) AND by `t + 1` (`e = 8`). That is why the statements prove the bound exactly
    /// (`LinfExact(7)`) and why `explains` refuses `|e| = 8`.
    #[test]
    fn determinism_needs_the_exact_error_bound() {
        let mut rng = StdRng::seed_from_u64(0x1a08);
        let a = matrix_with_first_column(&[GAMMA * 77 + 7], &mut rng);
        let key = unit_key(1);
        let (tag, e) = LWR.eval_with_error(&key, &a).unwrap();
        assert_eq!((tag.0[0], e.0[0]), (77, -7));
        let mut t2 = *tag.entries();
        let mut e2 = *e.entries();
        t2[0] = 78;
        e2[0] = 8;
        // the relation modulo q_t holds for the second explanation ...
        let w = i64::from(a.row(0)[0]);
        assert_eq!(
            (w + i64::from(e2[0]) - i64::from(GAMMA) * i64::from(t2[0])).rem_euclid(i64::from(Q_T)),
            0
        );
        // ... but its error is outside the exact bound
        assert!(!LWR.explains(&key, &a, &LWRTag::from_entries(t2), &RoundingError(e2)));
    }

    #[test]
    fn rounding_errors_are_redacted_and_wiped() {
        let mut rng = StdRng::seed_from_u64(0x1a09);
        let a = random_matrix(&mut rng);
        let (_, mut e) = LWR.eval_with_error(&LWR.keygen(&mut rng), &a).unwrap();
        assert_eq!(format!("{e:?}"), "RoundingError(<redacted>)");
        assert!(e.entries().iter().any(|&x| x != 0));
        e.zeroize();
        assert!(e.entries().iter().all(|&x| x == 0));
    }
}
