//! The post-quantum (lattice) instantiation of the construction (paper §5.2, "A Post-Quantum
//! Instantiation"): the shared foundations of the credential base `Σ-vSIS`
//! ([`VSIS`](crate::cred::VSIS)), the short-key tag `Tag_LWR` ([`LWR`](crate::kiprf::LWR)) and
//! the construction [`LatticePCS`](crate::pcs::lattice::LatticePCS). Feature `lattice`.
//!
//! | paper | here |
//! |---|---|
//! | `R_q = Z_q[X]/(X^d + 1)`, `d = 1024`, `q = 1,048,573` (building-blocks.tex, sec:inst-base-vsis) | [`Rq`] (arithmetic by `ntru-trapdoor`) |
//! | short messages `usk`, `x_0`, `x_1` with `‖·‖_∞ ≤ 1` | [`Ternary`] |
//! | binary public messages `φ ∈ M_pub` | [`BinaryPoly`] |
//! | the tag set R `(γ, p, q_t, m) = (15, 2^16, 983,040, 168)`, the bounds of `M_Σ`, `⌊β_s²⌋` | the constants of this module |
//! | the issuance cap `Q_max = 2^48` (construction.tex, "Issuance cap") | [`Q_MAX`] |
//! | `H_mat`, `H_0`, `c_0`, `EncPred` (construction.tex, "Random oracles of the lattice tag"; con:59-65) | [`oracles`] |
//! | the proof system: Jali's parameter sets for `R_att`, `R_issue` and the root flow | [`sets`] |
//!
//! # Fixed parameters
//!
//! One parameter set, the 128-bit set of docs/design-notes.md (tag set R, proof degree 128,
//! `β_r = 1`): ring degree $`d = n = 1024`$, ring modulus $`q = 2^{20} - 3`$ (prime,
//! $`\equiv 5 \bmod 8`$), NTRU width $`w = 2`$ ($`A = [1 \mid h]`$), $`\ell_r = 2`$,
//! $`\beta_u = \beta_x = \beta_r = 1`$, $`\lfloor\beta_s^2\rfloor = 90{,}803{,}788{,}942`$, and the
//! short-key LWR tag with $`\gamma = 15`$, $`p = 2^{16}`$, $`q_t = \gamma p = 983{,}040`$,
//! $`m = 168`$ (the smallest $`m`$ of lem:tag-lwr-short at $`\lambda = 128`$), whose rounding
//! errors are bounded EXACTLY by $`\lfloor\gamma/2\rfloor = 7`$ (rem:relaxed-extraction). The
//! Jali parameter sets in [`sets`] were derived for exactly these values and for exactly the
//! statement layouts of [`LatticePCS`](crate::pcs::lattice::LatticePCS); changing any constant
//! here means deriving new sets.
//!
//! # Randomness
//!
//! Every randomized algorithm takes the crate's `rng: &mut R` (rand 0.8). Jali and
//! `ntru-trapdoor` take 32-byte seeds instead; each call gets a FRESH seed drawn from the caller's
//! RNG (`fresh_seed`), never reused: one per Jali proof (the multi-theorem zero-knowledge bound
//! assumes it), one per `SampPre` call ("fresh coins in every call", building-blocks.tex, "The
//! implemented preimage sampler"), one per `TrapGen`.
//!
//! # Side channels
//!
//! Performance comes first. The ring arithmetic of `ntru-trapdoor` uses masks, and `SampPre`
//! keeps fn-dsa's isochronous sampler structure, but `SampPre`'s floating-point arithmetic and
//! rejection loops, key generation and all of Jali (arithmetic, sampling, rejection, decoding)
//! run in variable time.

pub mod oracles;
pub mod ring;
pub mod sets;
pub(crate) mod xof;

use ark_std::rand::{CryptoRng, RngCore};
use zeroize::Zeroizing;

pub use self::ring::{BinaryPoly, Rq, Ternary};
use crate::error::Error;

/// The ring degree $`d`$ of $`R_q`$, which is also the dimension $`n`$ of the tag key (the
/// coefficient vector of `usk`).
pub const D: usize = 1024;
/// The prime ring modulus $`q = 2^{20} - 3 = 1{,}048{,}573 \equiv 5 \bmod 8`$:
/// $`X^{1024} + 1`$ splits into two irreducible factors of degree 512 modulo $`q`$.
pub const Q: u32 = 1_048_573;
/// The odd rounding ratio $`\gamma = q_t / p`$ of the tag.
pub const GAMMA: u32 = 15;
/// The tag output modulus $`p = 2^{16}`$. Tag entries are `u16`: every encoding is canonical,
/// so `ValidTag` is an invariant of the type [`LWRTag`](crate::kiprf::lwr::LWRTag).
pub const P: u32 = 1 << 16;
/// The composite tag modulus $`q_t = \gamma p = 983{,}040`$ (written $`q`$ in
/// sec:inst-tag-lwr).
pub const Q_T: u32 = GAMMA * P;
/// The number $`m`$ of tag rows: the smallest $`m`$ with
/// $`m\log\psi \ge n\log(4\beta_u + 1) + \lambda`$, $`\psi = q_t/(4\lfloor\gamma/2\rfloor + 2\beta_u)`$,
/// at $`\lambda = 128`$ (lem:tag-lwr-short): $`\psi = 2^{15}`$, $`m \ge 2505.65/15`$.
pub const M: usize = 168;
/// The EXACT bound $`\lfloor\gamma/2\rfloor = (\gamma - 1)/2 = 7`$ on the rounding errors of the
/// tag clauses (rem:relaxed-extraction, lem:tag-lwr-determinism).
pub const E_BOUND: u64 = (GAMMA as u64 - 1) / 2;
/// $`\beta_u`$: `usk` is uniform on $`\{-1, 0, 1\}^n`$.
pub const BETA_U: u64 = 1;
/// $`\beta_x`$: the signing randomness $`x_1`$ is uniform on $`\{-1, 0, 1\}^d`$.
pub const BETA_X: u64 = 1;
/// $`\beta_r`$: each component of $`x_0`$ is uniform on $`\{-1, 0, 1\}^d`$.
pub const BETA_R: u64 = 1;
/// $`\ell_r`$, the number of components of $`x_0`$ (and of $`B_r`$).
pub const ELL_R: usize = 2;
/// $`\lfloor\beta_s^2\rfloor = \lfloor\varsigma^2 \cdot 2d\rfloor = 90{,}803{,}788{,}942`$: the
/// exact bound on $`\|s\|^2`$ of `Verify`, of the possession relation and of `SampPre`.
pub const S_BOUND: u64 = 90_803_788_942;
/// The degree of Jali's proof ring.
pub const PROOF_DEGREE: usize = 128;
/// The degree of the subring elements that hold a rounding-error vector $`e \in \mathbb Z^m`$ in
/// the statements: the proof degree.
pub const E_DEG: usize = PROOF_DEGREE;
/// The number $`\lceil m / e_{\deg}\rceil = 2`$ of subring elements per rounding-error vector.
pub const E_COUNT: usize = M.div_ceil(E_DEG);
/// The issuance cap $`Q_{\max} = 2^{48}`$: the number of `SampPre` calls (`Sign` and
/// `BlindIssue`) that one helper key answers (construction.tex, "Issuance cap"). The helper then
/// rotates its key.
pub const Q_MAX: u64 = 1 << 48;
/// The Jali commit this crate is built and pinned against (`Cargo.toml`). It enters the digest of
/// the lattice `pp`: Jali promises no stability of its proof encoding or transcripts.
pub const JALI_REVISION: &str = "0cd24f38bd84e2e48d2dcb63f34d2d17cba2a90d";

// The constants are consistent with each other and with the layouts the parameter sets were
// derived for.
const _: () = {
    assert!(Q_T == 983_040 && GAMMA % 2 == 1);
    assert!(E_BOUND == 7);
    assert!(
        P == 1 << 16,
        "tags are u16: ValidTag is then a type invariant"
    );
    assert!(D.is_multiple_of(E_DEG) && E_DEG.is_multiple_of(PROOF_DEGREE));
    assert!(E_COUNT * E_DEG >= M && (E_COUNT - 1) * E_DEG < M);
    assert!(E_COUNT == 2);
};

/// A fresh, secret, uniform 32-byte seed from the caller's RNG, in a buffer that is wiped on
/// drop: the seed bridge from the crate's rand-0.8 RNG to the seeded entry points of Jali
/// (`Compiled::prove_bytes_with_seed`) and of `ntru-trapdoor` (`trapgen`, `samp_pre`). Draw one
/// per call and never reuse it.
pub(crate) fn fresh_seed<R: RngCore + CryptoRng + ?Sized>(rng: &mut R) -> Zeroizing<[u8; 32]> {
    let mut seed = Zeroizing::new([0u8; 32]);
    rng.fill_bytes(&mut *seed);
    seed
}

/// Maps an error of Jali to this crate's [`Error`]:
///
/// | Jali | here |
/// |---|---|
/// | `Witness` (the honest prover's witness check) | [`Error::WitnessDoesNotSatisfyRelation`] |
/// | `InvalidProof`, `Encoding` (a verifier's rejection) | [`Error::InvalidProof`] |
/// | anything else (`Parameter`, `Dimension`, `Overflow`, `Index`, `RingMismatch`, `Randomness`, `RestartLimit`) | [`Error::LatticeBackend`] |
///
/// `RestartLimit` (4096 rejected attempts of the prover) is retried with a fresh seed by the
/// caller before it is mapped.
pub(crate) fn jali_error(error: jali::Error) -> Error {
    match error {
        jali::Error::Witness => Error::WitnessDoesNotSatisfyRelation,
        jali::Error::InvalidProof | jali::Error::Encoding => Error::InvalidProof,
        other => Error::LatticeBackend(format!("jali: {other}")),
    }
}

/// Maps an error of `ntru-trapdoor` to this crate's [`Error`]: a malformed encoding is
/// [`Error::Serialization`], an inconsistent trapdoor is [`Error::InvalidKey`], and anything
/// else (`SampPreExhausted`, `KeygenExhausted`, `InvalidParams`, `Mismatch`, `NotInvertible`) is
/// [`Error::LatticeBackend`].
pub(crate) fn ntru_error(error: ntru_trapdoor::Error) -> Error {
    match error {
        ntru_trapdoor::Error::InvalidLength | ntru_trapdoor::Error::InvalidEncoding => {
            Error::Serialization(format!("ntru-trapdoor: {error}"))
        }
        ntru_trapdoor::Error::InvalidKey | ntru_trapdoor::Error::LeafOutOfRange => {
            Error::InvalidKey
        }
        other => Error::LatticeBackend(format!("ntru-trapdoor: {other}")),
    }
}

#[cfg(test)]
mod tests {
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;

    /// The constants agree with `ntru-trapdoor`'s PCS set and with lem:tag-lwr-short.
    #[test]
    fn constants_agree_with_the_trapdoor_set_and_the_lemma() {
        let ntru = ntru_trapdoor::Params::PCS;
        assert_eq!(ntru.n(), D);
        assert_eq!(ntru.q, Q);
        assert_eq!(ntru.beta_sq, S_BOUND);
        assert_eq!(ntru.rq_bytes(), Rq::BYTES);
        // lem:tag-lwr-short at λ = 128, with the honest bounds (β_u, ⌊γ/2⌋): ψ = q_t / 30 = 2^15
        let psi = f64::from(Q_T) / (4.0 * E_BOUND as f64 + 2.0 * BETA_U as f64);
        assert_eq!(psi, 32768.0);
        let rhs = D as f64 * (4.0 * BETA_U as f64 + 1.0).log2() + 128.0;
        let m = (rhs / psi.log2()).ceil() as usize;
        assert_eq!(m, M);
        assert!((M - 1) as f64 * psi.log2() < rhs);
    }

    /// `JALI_REVISION` is the commit that `Cargo.toml` pins.
    #[test]
    fn jali_revision_is_the_pinned_commit() {
        let manifest = include_str!("../../Cargo.toml");
        assert!(manifest.contains(&format!("rev = \"{JALI_REVISION}\"")));
    }

    /// One seed per call: consecutive seeds differ.
    #[test]
    fn fresh_seeds_differ() {
        let mut rng = StdRng::seed_from_u64(1);
        let a = fresh_seed(&mut rng);
        let b = fresh_seed(&mut rng);
        assert_ne!(*a, *b);
    }

    #[test]
    fn errors_map_as_documented() {
        assert_eq!(
            jali_error(jali::Error::Witness),
            Error::WitnessDoesNotSatisfyRelation
        );
        assert_eq!(jali_error(jali::Error::InvalidProof), Error::InvalidProof);
        assert_eq!(jali_error(jali::Error::Encoding), Error::InvalidProof);
        assert!(matches!(
            jali_error(jali::Error::RestartLimit),
            Error::LatticeBackend(_)
        ));
        assert!(matches!(
            ntru_error(ntru_trapdoor::Error::InvalidEncoding),
            Error::Serialization(_)
        ));
        assert_eq!(
            ntru_error(ntru_trapdoor::Error::InvalidKey),
            Error::InvalidKey
        );
        assert!(matches!(
            ntru_error(ntru_trapdoor::Error::SampPreExhausted),
            Error::LatticeBackend(_)
        ));
    }
}
