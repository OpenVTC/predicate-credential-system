//! `Σ-vSIS`, the post-quantum credential base of §6.2.3 ("The vSIS instantiation
//! (post-quantum)", box "`Σ-vSIS` credential base"): the proof-friendly lattice signatures of
//! DKLW25 in the committed-message form of BLNS23, on an NTRU trapdoor ($`A = [1 \mid h]`$,
//! $`w = 2`$) from `ntru-trapdoor`. Feature `lattice`.
//!
//! | paper | here |
//! |---|---|
//! | `PGen`: uniform $`v, b_u \in R_q`$, $`B_r \in R_q^{1 \times \ell_r}`$ from public randomness | [`VSIS::setup`] ([`VSISParams`], expanded from the deployment label) |
//! | `KeyGen`: $`(A, td_A) \gets \mathsf{TrapGen}(R, q, w)`$ | [`VSIS::keygen`] |
//! | the certified message $`\mathsf{usk} \in R`$, $`\|\mathsf{usk}\|_\infty \le \beta_u`$ | [`Ternary`] |
//! | the issuance randomness $`x_0 \gets \mathcal D_r`$ | [`VSISTape`] |
//! | `PrepareIssue`: $`C = b_u\,\mathsf{usk} + B_r x_0 \bmod q`$ | [`VSIS::prepare_issue`] |
//! | `BlindIssue`: $`x_1`$, $`t = (v - x_1)^{-1} + C`$, $`s \gets \mathsf{SampPre}(td_A, t, \varsigma)`$ | [`VSIS::blind_issue`] → [`VSISPreCredential`] $`(s, x_1)`$ |
//! | `Unblind`, which verifies | [`VSIS::unblind`] → [`VSISCredential`] $`(s, x_1, x_0)`$ |
//! | `Verify` | [`VSIS::verify`], in product form |
//! | `ReRand` outputs the empty encoding $`\varepsilon`$ | the show of the backend is `()` |
//! | $`\Pi_{\mathsf{PrepareIssue}}`$, $`\Pi_{\Possess}`$ | Jali statements of the backend (`relations`) |
//! | "The implemented preimage sampler": $`s \in \Lambda_t`$ exactly, fresh coins per call | `ntru_trapdoor::samp_pre` with a fresh seed, then an exact check |
//! | the issuance cap $`Q_{\max} = 2^{48}`$ ("Issuance cap") | the counter of [`VSISSigningKey`] |
//!
//! # In formulas
//!
//! With $`x_1 \gets \mathcal X_1 = \{x \in R : \|x\|_\infty \le \beta_x\}`$ resampled until
//! $`v - x_1`$ is a unit, `BlindIssue` samples a preimage of the target
//!
//! ```math
//! t = (v - x_1)^{-1} + C, \qquad C = b_u\,\mathsf{usk} + B_r x_0, \qquad s \gets \mathsf{SampPre}(td_A, t, \varsigma),
//! ```
//!
//! and `Verify` accepts $`(s, x_1, x_0)`$ on $`\mathsf{usk}`$ iff every component has its
//! length (only a wiped value has not), $`0 < \|s\|^2 \le \lfloor\beta_s^2\rfloor`$ and
//!
//! ```math
//! \bigl(s_0 + h s_1 - b_u\,\mathsf{usk} - B_r x_0\bigr)\cdot(v - x_1) = 1 \bmod q,
//! ```
//!
//! the product form of the box's equation $`As = (v - x_1)^{-1} + b_u\,\mathsf{usk} + B_r x_0`$
//! together with "$`v - x_1`$ is invertible": a product equals $`1`$ iff both factors are units
//! and each is the inverse of the other, so the two forms accept exactly the same inputs, and the
//! product form needs no inversion. The norm conditions $`\|\mathsf{usk}\|_\infty \le \beta_u`$,
//! $`\|x_0\|_\infty \le \beta_r`$ and $`x_1 \in \mathcal X_1`$ hold by type ([`Ternary`],
//! $`\beta_u = \beta_r = \beta_x = 1`$).
//!
//! # What the paper asks of the parameters, and how this code meets it
//!
//! * **The hiding of the request.** lem:base-vsis (b) rests on the knapsack form of
//!   $`\mathsf{MLWE}_{\ell_r,q,\mathcal D_r}`$: $`(B_r, B_r x_0)`$ is pseudorandom (the
//!   computational hiding of BLNS23, Thm. 8.2). Here $`\mathcal D_r`$ is uniform on
//!   $`(\{-1, 0, 1\}^d)^{\ell_r}`$ with $`\ell_r = 3`$: dividing by $`B_{r,0}`$ gives module
//!   LWE with one sample, a ternary secret of rank 2 and a ternary error, which lattice-estimator
//!   (commit `53da598`, rough mode) prices at $`2^{344.9}`$; at $`\ell_r = 2`$ it is
//!   $`2^{130.8}`$, under three bits above 128 before the factor $`2Q_{\mathsf{iss}}`$ of the
//!   theorem (`tools/lattice/hiding_estimate.sage`). The statistical variant, the regularity bound
//!   $`\Delta((B_r, B_r x_0), (B_r, U)) = \mathsf{negl}`$, needs $`\ell_r \ge 13`$ ternary
//!   components (the entropy of $`x_0`$ must exceed $`d \log_2 q`$), and the paper's definition
//!   of issuance simulatability asks only for computational closeness.
//! * **$`s \neq 0`$ in the proofs.** $`\Pi_{\Possess}`$ proves $`1 \le \|s\|^2 \le
//!   \beta_s^2`$, and the argument system must extract $`s \neq 0`$ exactly. The relations of
//!   the backend bound `s` with Jali's two-sided exact norm (`relations::S_NORM`,
//!   `Norm::L2SquaredRange { min: 1, max: ⌊β_s²⌋ }`: one binary witness for $`\|s\|^2 - 1`$, the
//!   argument of §5.2.3, "The lower bound on $`\|s\|^2`$"), and
//!   `Verify` checks $`\|s\| > 0`$.
//! * **$`\mathcal V_{\mathsf{pp}}`$.** The paper makes it the whole key space; this
//!   code takes $`\mathcal V_{\mathsf{pp}} = R_q`$ ([`VSISVerificationKey`]), since issuance
//!   simulatability holds for every key (lem:base-vsis (b)).
//! * **Not estimated:** the concrete hardness of $`\mathsf{IntGenISIS}_f`$ (the one-more vSIS
//!   assumption) with $`k = 1 + \ell_r = 4`$ columns of $`B`$ and message bound 1 ("the concrete
//!   parameters of the assumption must be set for these values").
//!
//! # Encodings
//!
//! | object | bytes | size |
//! |---|---|---|
//! | [`VSISParams`] | $`v \| b_u \| B_{r,0} \| B_{r,1} \| B_{r,2}`$, each an [`Rq`] | 12,800 |
//! | [`VSISSigningKey`] | `ntru-trapdoor`'s secret-key encoding (5889) $`\|`$ `LE64(issued)` | 5897 |
//! | [`VSISVerificationKey`] | $`h`$, an [`Rq`] | 2560 |
//! | [`VSISTape`] | $`x_{0,0} \| x_{0,1} \| x_{0,2}`$, each a [`Ternary`] | 768 |
//! | [`VSISPreCredential`] | $`s_0 \| s_1`$ at 20 bits per coefficient, two's complement, little-endian bit packing; then $`x_1`$ | 5376 |
//! | [`VSISCredential`] | the pre-credential, then $`x_0`$ | 6144 |
//!
//! Every decoder checks canonicity whatever `Validate` flag it gets (the module docs of
//! [`crate::lattice::ring`]). Decoding the signing key validates the trapdoor
//! ($`fG - gF = q`$, $`f`$ invertible) and rebuilds its expanded form. Decoding says nothing
//! about the validity of a credential: that is [`VSIS::verify`].
//!
//! # The implemented preimage sampler
//!
//! `SampPre` is `ntru-trapdoor`'s Falcon-style fast-Fourier sampler (`samp_pre`). It computes
//! the lattice point in floating point and rounds it; the rounding is exact with a MEASURED
//! margin, not by proof. The paper requires more: "an implementation must compute this $`s`$
//! exactly, in integer arithmetic, so that $`s \in \Lambda_t`$". So before a preimage leaves the
//! signing key, the key checks $`s_0 + h s_1 = t \bmod q`$ in exact integer arithmetic together
//! with $`\|s\|^2 \le \lfloor\beta_s^2\rfloor`$, and refuses a sample that fails
//! ([`Error::LatticeBackend`]; never observed). Each call receives a fresh 32-byte seed from the
//! caller's RNG, never reused ("must use fresh coins in every call"): the helper's RNG must be a
//! CSPRNG seeded by the operating system, since `TrapGen` and every `SampPre` call draw their
//! coins from it.
//!
//! # The issuance cap
//!
//! lem:base-vsis assumes that a key answers at most $`Q_{\max}`$ calls of `BlindIssue`, and the
//! paper sets $`Q_{\max} = 2^{48}`$ ("Issuance cap"). [`VSISSigningKey`] counts them: each call
//! reserves one unit of the counter ATOMICALLY before it calls `SampPre` (a compare-and-swap that
//! increments only below $`Q_{\max}`$), and fails with [`Error::IssuanceCapReached`] once
//! $`Q_{\max}`$ units are used, so concurrent issuance through a shared `&VSISSigningKey` never
//! exceeds the cap. A reservation is consumed even when `SampPre` then fails (conservative). The
//! count is part of the key's encoding: a helper that stores its key stores the count, and a
//! helper that restores an OLD copy resets it (the operator's responsibility,
//! `docs/operating-a-helper.md`). [`VSISSigningKey::to_bytes_reserving`] stores a count AHEAD of
//! the true one, for a helper that persists before it issues. The counter lives in ONE value:
//! two values decoded from the same bytes count independently, so a deployment runs one live
//! instance per stored key (threads share it by reference). The rotation itself (a new key, a
//! new `hvk`) belongs to the helper.
//!
//! # Implementation notes
//!
//! Not in the paper, and each one only refuses inputs that are not what their type stands for:
//!
//! * Every value of [`Ternary`] lies in its message space by construction, except a WIPED one
//!   (`zeroize` empties it). The algorithms therefore check only the lengths: `PrepareIssue`
//!   returns `⊥` and `Verify` returns `false` for a wiped component; `BlindIssue` returns
//!   [`Error::InvalidIssuanceEncoding`] for a wiped $`C`$; a wiped signing key signs nothing
//!   ([`Error::InvalidKey`]). None of the algorithms panics; only the constructor
//!   [`VSISVerificationKey::from_h`] does, on a wiped $`h`$.
//! * The resampling loops are bounded: `KeyGen` tries `TrapGen` with 4 fresh seeds (each fails
//!   only after 4096 rejected candidates, while about 1 in 20 is accepted) and panics after that;
//!   $`x_1`$ is drawn at most $`\lambda = 128`$ times, as in the box, after which
//!   [`Error::LatticeBackend`] is returned. Over the uniform $`v`$ of `PGen`, $`v - x_1`$ is a
//!   non-unit with probability about $`2/q^{512}`$ for each $`x_1`$ ($`X^{1024} + 1`$ has two
//!   irreducible factors of degree 512 modulo $`q`$).
//!
//! # Side channels
//!
//! Performance comes first. The ring arithmetic of `ntru-trapdoor` uses masks (the inverse
//! reveals only whether an element is a unit), message comparisons and credential equality are
//! constant time, and the secret intermediates of `PrepareIssue`, `BlindIssue` and `Verify` are
//! wiped. The rejection loops of [`Ternary::sample`] and of `SampPre`, `SampPre`'s floating-point
//! arithmetic and `TrapGen` run in variable time (the module docs of [`crate::lattice`]).
//!
//! # Example
//!
//! Issuance, as the protocol runs it:
//!
//! ```
//! use predicate_credential_system::{
//!     lattice::Ternary,
//!     pcreds::lattice::base::{VSIS, VSISTape},
//! };
//! use rand::{SeedableRng, rngs::StdRng};
//!
//! // seeded so that the example is reproducible; a helper uses `rand::rngs::OsRng` (the
//! // trapdoor is a function of the RNG's output)
//! let mut rng = StdRng::seed_from_u64(1);
//! let pp = VSIS::setup(b"example deployment");
//! let (vk, sk) = VSIS::keygen(&mut rng); // TrapGen, about 6 ms
//! let usk = Ternary::sample(&mut rng);
//! let tape = VSISTape::sample(&mut rng);
//!
//! // user: C = PrepareIssue    helper: BlindIssue(sk, C)    user: Unblind (it verifies)
//! let c = VSIS::prepare_issue(&pp, &usk, &tape).expect("an admissible message");
//! let pre = VSIS::blind_issue(&pp, &sk, &c, &mut rng)?;
//! let cred = VSIS::unblind(&pp, &vk, &usk, &pre, &tape)?;
//! assert!(VSIS::verify(&pp, &vk, &usk, &cred));
//! assert_eq!(sk.issued(), 1); // one SampPre call under the cap
//! # Ok::<(), predicate_credential_system::Error>(())
//! ```

use core::{
    fmt,
    sync::atomic::{AtomicU64, Ordering},
};

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::rand::{CryptoRng, RngCore};
use ntru_trapdoor::{
    ExpandedKey, Preimage, PreparedRqPoly, PublicKey, RqPoly, SecretKey, samp_pre, trapgen,
};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use crate::{
    error::Error,
    lattice::{
        D, ELL_R, Q_MAX, Rq, S_BOUND, Ternary, fresh_seed, ntru_error,
        ring::{NTRU, pack_signed, unpack_signed},
        xof::pp_element,
    },
};

/// Bits per coefficient of $`s_0`$ and $`s_1`$ in the credential encoding (two's complement).
const S_BITS: u32 = 20;
/// Bytes of one half of $`s`$: $`1024 \cdot 20 / 8`$.
const S_HALF_BYTES: usize = D * S_BITS as usize / 8;
/// The largest encodable $`|s_i|`$, $`2^{19} - 1`$ (the code $`-2^{19}`$ is rejected). Every
/// credential that verifies has $`|s_i| \le \lfloor\beta_s\rfloor = 301{,}336`$.
const S_MAX_ABS: u32 = (1 << (S_BITS - 1)) - 1;
/// Bytes of `ntru-trapdoor`'s secret-key encoding at the PCS set: the header `0xAA`, then
/// $`f, g`$ at 10 and $`F, G`$ at 13 bits per coefficient.
const SECRET_KEY_BYTES: usize = 1 + 2 * (D * 10 / 8) + 2 * (D * 13 / 8);
/// `TrapGen` calls (each with a fresh seed) before `KeyGen` gives up.
const KEYGEN_ATTEMPTS: usize = 4;
/// Draws of $`x_1`$ before `BlindIssue` gives up: $`\lambda = 128`$, as in the box ("return
/// `⊥` after $`\lambda`$ failed attempts").
const X1_ATTEMPTS: usize = 128;
/// The name of column `k` of $`B_r`$ in the oracle `/LATTICE-PP` (`lattice::xof::pp_element`):
/// `B_r[k]`, the index in decimal (ASCII). The other elements are named `v` and `b_u`.
fn b_r_name(k: usize) -> Vec<u8> {
    format!("B_r[{k}]").into_bytes()
}

// The fixed-size code below is for the trapdoor set and the ring of the PCS set.
const _: () = assert!(SECRET_KEY_BYTES == 5889 && S_HALF_BYTES == 2560);

/// Whether `x` is an element of $`\{-1, 0, 1\}^d`$. Every [`Ternary`] is, unless it was wiped.
fn is_short(x: &Ternary) -> bool {
    x.coeffs().len() == D
}

/// Whether `x` is the unit element $`1`$, without an early exit.
fn is_one(x: &Rq) -> bool {
    let c = x.coeffs();
    c.len() == D
        && c.iter()
            .enumerate()
            .fold(0u32, |acc, (i, &v)| acc | (v ^ u32::from(i == 0)))
            == 0
}

/// `p · x` for a prepared public operand `p` (four NTTs instead of six).
fn times(p: &PreparedRqPoly, x: &Rq) -> Rq {
    Rq::from_poly(p.mul(x.poly()))
}

/// The credential base `Σ-vSIS` (marker type; the algorithms of the box are its associated
/// functions).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct VSIS;

// ---------------------------------------------------------------------------------------------
// Public parameters
// ---------------------------------------------------------------------------------------------

/// The public parameters $`pp_\Sigma = (v, b_u, B_r)`$, uniform in $`R_q`$ and expanded from the
/// deployment label (`/LATTICE-PP`, element names `v`, `b_u`, `B_r[0]` to `B_r[2]`): "the uniform
/// elements must come from public randomness, for example by expanding a published seed, so that
/// nobody — the helper included — knows a short relation among them". The norm bounds, the width
/// $`\varsigma`$ and the distribution $`\mathcal D_r`$ of the box are the constants of
/// [`crate::lattice`] and of `ntru-trapdoor`'s PCS set.
///
/// The value also keeps $`b_u`$ and $`B_r`$ prepared for products (NTT form, built once by
/// [`VSIS::setup`] and by decoding), so that `PrepareIssue` costs $`1 + \ell_r`$ and `Verify`
/// $`2 + \ell_r`$ products with a prepared operand.
///
/// Encoding: $`v \| b_u \| B_{r,0} \| B_{r,1} \| B_{r,2}`$, $`2 + \ell_r`$ [`Rq`] ([`Self::BYTES`]
/// bytes). Equality compares these elements.
#[derive(Clone)]
pub struct VSISParams {
    v: Rq,
    b_u: Rq,
    b_r: [Rq; ELL_R],
    /// $`b_u`$ and $`B_r`$ prepared for products.
    prepared: Prepared,
}

/// The public columns of `pp_Σ` in the NTT form of `ntru-trapdoor`'s products.
#[derive(Clone)]
struct Prepared {
    b_u: PreparedRqPoly,
    b_r: [PreparedRqPoly; ELL_R],
}

impl VSISParams {
    /// Bytes of the encoding: $`2 + \ell_r`$ elements of $`R_q`$.
    pub const BYTES: usize = (2 + ELL_R) * Rq::BYTES;

    /// The parameters with these elements, and their prepared forms.
    pub(crate) fn from_elements(v: Rq, b_u: Rq, b_r: [Rq; ELL_R]) -> Self {
        let prepared = Prepared {
            b_u: b_u.poly().prepare(),
            b_r: core::array::from_fn(|k| b_r[k].poly().prepare()),
        };
        Self {
            v,
            b_u,
            b_r,
            prepared,
        }
    }

    /// $`v`$, the key of the inverse family $`f_v(x_1) = (v - x_1)^{-1}`$.
    #[must_use]
    pub fn v(&self) -> &Rq {
        &self.v
    }

    /// $`b_u`$, the commitment column of `usk`.
    #[must_use]
    pub fn b_u(&self) -> &Rq {
        &self.b_u
    }

    /// $`B_r = (B_{r,0}, B_{r,1}, B_{r,2})`$, the commitment columns of $`x_0`$.
    #[must_use]
    pub fn b_r(&self) -> &[Rq; ELL_R] {
        &self.b_r
    }

    /// Parameters with every element equal to `x`: the worst-case public data of the export of
    /// the relations to Jali's parameter tool (`relations`).
    #[cfg(test)]
    pub(crate) fn worst_case(x: Rq) -> Self {
        Self::from_elements(x.clone(), x.clone(), core::array::from_fn(|_| x.clone()))
    }

    /// The four elements in the order of the encoding.
    fn elements(&self) -> impl Iterator<Item = &Rq> {
        [&self.v, &self.b_u].into_iter().chain(&self.b_r)
    }

    /// $`C = b_u\,\mathsf{usk} + B_r x_0 \bmod q`$, with the prepared columns ($`1 + \ell_r`$
    /// products).
    /// $`C`$ is public; the products of its terms are secret and wiped. `None` for a wiped
    /// `usk` or $`x_0`$ (module docs, "Implementation notes").
    pub(crate) fn commitment(&self, usk: &Ternary, x0: &[Ternary; ELL_R]) -> Option<Rq> {
        if !is_short(usk) || !x0.iter().all(is_short) {
            return None;
        }
        let mut c = Zeroizing::new(times(&self.prepared.b_u, &Zeroizing::new(usk.to_rq())));
        for (b, x) in self.prepared.b_r.iter().zip(x0) {
            let term = Zeroizing::new(times(b, &Zeroizing::new(x.to_rq())));
            c = Zeroizing::new(c.add(&term));
        }
        Some(core::mem::replace(&mut *c, Rq::zero()))
    }

    /// `BlindIssue` step 1: $`x_1 \gets \mathcal X_1`$ uniform ([`Ternary::sample`],
    /// $`\beta_x = 1`$), resampled until $`v - x_1`$ is a unit; returns $`x_1`$ and
    /// $`(v - x_1)^{-1}`$.
    ///
    /// # Errors
    /// [`Error::LatticeBackend`] after [`X1_ATTEMPTS`] draws (module docs: never in practice).
    fn sample_x1<R: RngCore + CryptoRng + ?Sized>(
        &self,
        rng: &mut R,
    ) -> Result<(Ternary, Zeroizing<Rq>), Error> {
        for _ in 0..X1_ATTEMPTS {
            let x1 = Ternary::sample(rng);
            let g = Zeroizing::new(self.v.sub(&Zeroizing::new(x1.to_rq())));
            if let Some(y) = g.inverse() {
                return Ok((x1, Zeroizing::new(y)));
            }
        }
        Err(Error::LatticeBackend(format!(
            "Σ-vSIS: v - x_1 was not a unit for {X1_ATTEMPTS} draws of x_1"
        )))
    }

    /// The first factor of `Verify`'s product form, $`s_0 + h s_1 - b_u\,\mathsf{usk} - B_r
    /// x_0`$: $`2 + \ell_r`$ products with prepared operands ($`h`$, $`b_u`$ and the columns of
    /// $`B_r`$).
    /// `None` for inputs of the wrong length. Secret: wiped.
    fn residual(
        &self,
        vk: &VSISVerificationKey,
        usk: &Ternary,
        x0: &[Ternary; ELL_R],
        s: &Preimage,
    ) -> Option<Zeroizing<Rq>> {
        let s0 = Zeroizing::new(RqPoly::from_i32(&NTRU, &s.s0).ok()?);
        let s1 = Zeroizing::new(RqPoly::from_i32(&NTRU, &s.s1).ok()?);
        let h_s1 = Zeroizing::new(vk.pk.h_prepared().mul(&s1));
        let a_s = Zeroizing::new(Rq::from_poly(s0.add(&h_s1)));
        let c = Zeroizing::new(self.commitment(usk, x0)?);
        Some(Zeroizing::new(a_s.sub(&c)))
    }
}

impl PartialEq for VSISParams {
    fn eq(&self, other: &Self) -> bool {
        self.v == other.v && self.b_u == other.b_u && self.b_r == other.b_r
    }
}

impl Eq for VSISParams {}

impl fmt::Debug for VSISParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISParams(v, b_u, B_r)")
    }
}

impl CanonicalSerialize for VSISParams {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        for element in self.elements() {
            element.serialize_with_mode(&mut writer, compress)?;
        }
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for VSISParams {
    fn check(&self) -> Result<(), SerializationError> {
        self.elements().try_for_each(|element| element.check())
    }
}

impl CanonicalDeserialize for VSISParams {
    /// $`2 + \ell_r`$ canonical elements of $`R_q`$, whatever `validate` says; prepares the
    /// columns.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut element = || Rq::deserialize_with_mode(&mut reader, compress, validate);
        let v = element()?;
        let b_u = element()?;
        let b_r = (0..ELL_R)
            .map(|_| element())
            .collect::<Result<Vec<_>, _>>()?;
        let b_r = b_r
            .try_into()
            .map_err(|_| SerializationError::InvalidData)?;
        Ok(Self::from_elements(v, b_u, b_r))
    }
}

// ---------------------------------------------------------------------------------------------
// Keys
// ---------------------------------------------------------------------------------------------

/// The signing key: the NTRU trapdoor $`td_A = (f, g, F, G)`$ with its expanded form (the
/// ffLDL tree, built once per key), its public key $`h`$ (for the exact check of every preimage,
/// module docs), and the issuance counter of the cap $`Q_{\max}`$ (module docs). Secret: wiped on
/// drop, redacted in `Debug`, not `Clone`. `Sync`: one key serves several threads, and the
/// counter is shared by all of them; two values decoded from the same bytes do NOT share it.
///
/// Encoding: `ntru-trapdoor`'s secret-key encoding (5889 bytes: header `0xAA`, $`f, g`$ at 10
/// bits and $`F, G`$ at 13 bits per coefficient) followed by the number of preimages issued so
/// far as 8 bytes little-endian; [`Self::BYTES`] bytes. Decoding validates the trapdoor
/// ($`fG - gF = q`$, the coefficient widths, $`f`$ invertible), rebuilds the expanded key and
/// $`h = g f^{-1}`$, and refuses a count above $`Q_{\max}`$. The count read is the one at the
/// time of encoding: persist the key after issuing, or BEFORE issuing with
/// [`Self::to_bytes_reserving`] (module docs, "The issuance cap").
pub struct VSISSigningKey {
    sk: SecretKey,
    ek: ExpandedKey,
    /// $`h = g f^{-1}`$ of this trapdoor, with $`h`$ prepared for products. Public.
    pk: PublicKey,
    issued: AtomicU64,
}

impl VSISSigningKey {
    /// Bytes of the encoding: the trapdoor and the 8-byte count.
    pub const BYTES: usize = SECRET_KEY_BYTES + 8;

    /// The number of `SampPre` calls this key has answered, i.e. the number of units of the cap
    /// reserved so far.
    #[must_use]
    pub fn issued(&self) -> u64 {
        self.issued.load(Ordering::SeqCst)
    }

    /// The number of `SampPre` calls left before the cap $`Q_{\max}`$.
    #[must_use]
    pub fn remaining(&self) -> u64 {
        Q_MAX.saturating_sub(self.issued())
    }

    /// The verification key $`h = g f^{-1}`$ of this trapdoor (computed when the key was made or
    /// decoded).
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped key.
    pub fn verification_key(&self) -> Result<VSISVerificationKey, Error> {
        self.ensure_usable()?;
        Ok(VSISVerificationKey {
            h: Rq::from_poly(self.pk.h().clone()),
            pk: self.pk.clone(),
        })
    }

    /// The encoding of the key with its count ADVANCED by `n` (saturating at $`Q_{\max}`$), in a
    /// buffer that is wiped on drop: what a helper stores BEFORE it answers up to `n` more calls,
    /// so that a restart from the stored copy (after a crash, say) never reuses a unit of the cap.
    /// The in-memory count is unchanged, and `to_bytes_reserving(0)` is the plain encoding. Store
    /// again before [`Self::issued`] passes the count stored last. A stored count above the true
    /// one only makes the key reach the cap earlier.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped key.
    pub fn to_bytes_reserving(&self, n: u64) -> Result<Zeroizing<Vec<u8>>, Error> {
        self.encode(self.issued().saturating_add(n).min(Q_MAX))
    }

    /// The trapdoor's encoding followed by `count`, in a buffer of exact capacity (no
    /// reallocation leaves copies of the trapdoor behind) that is wiped on drop.
    fn encode(&self, count: u64) -> Result<Zeroizing<Vec<u8>>, Error> {
        self.ensure_usable()?;
        let mut bytes = Zeroizing::new(Vec::with_capacity(Self::BYTES));
        bytes.extend_from_slice(&self.sk.to_bytes());
        bytes.extend_from_slice(&count.to_le_bytes());
        debug_assert_eq!(bytes.len(), Self::BYTES);
        Ok(bytes)
    }

    /// Reserves one `SampPre` call under the cap, atomically: a compare-and-swap loop that
    /// increments the counter only while it is below $`Q_{\max}`$ (the logic of
    /// `AtomicU64::try_update`, written out because that name is stable only from Rust 1.95 on and
    /// its predecessor `fetch_update` is deprecated from 1.99 on). Called by `BlindIssue` BEFORE
    /// it samples.
    ///
    /// # Errors
    /// [`Error::IssuanceCapReached`] once $`Q_{\max}`$ calls were reserved.
    fn reserve_preimage(&self) -> Result<(), Error> {
        let mut n = self.issued.load(Ordering::SeqCst);
        while n < Q_MAX {
            match self
                .issued
                .compare_exchange_weak(n, n + 1, Ordering::SeqCst, Ordering::SeqCst)
            {
                Ok(_) => return Ok(()),
                Err(current) => n = current,
            }
        }
        Err(Error::IssuanceCapReached)
    }

    /// Whether the key holds a trapdoor (it does unless it was wiped).
    fn is_usable(&self) -> bool {
        self.sk.f().len() == D
    }

    /// [`Error::InvalidKey`] for a wiped key.
    fn ensure_usable(&self) -> Result<(), Error> {
        if self.is_usable() {
            Ok(())
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// `SampPre(td_A, t, ς)` under the cap: reserves one unit of the counter, calls `samp_pre`
    /// with a fresh 32-byte seed from `rng` ("fresh coins in every call"), and releases the
    /// sample only if it IS a short preimage of $`t`$, checked exactly
    /// ([`Self::is_short_preimage`]; "in integer arithmetic, so that $`s \in \Lambda_t`$").
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped key; [`Error::IssuanceCapReached`] at the cap;
    /// [`Error::LatticeBackend`] if `samp_pre` fails (a target outside $`R_q`$, or all its
    /// attempts rejected, which has probability below $`2^{-5000}`$ at the PCS set) or returns a
    /// vector that is not a short preimage of $`t`$ (a floating-point rounding failure; never
    /// observed).
    fn preimage<R: RngCore + CryptoRng + ?Sized>(
        &self,
        t: &Rq,
        rng: &mut R,
    ) -> Result<Preimage, Error> {
        self.ensure_usable()?;
        self.reserve_preimage()?;
        let seed = fresh_seed(rng);
        let s = samp_pre(&self.ek, t.poly(), &seed).map_err(ntru_error)?;
        if self.is_short_preimage(t, &s) {
            Ok(s)
        } else {
            Err(Error::LatticeBackend(
                "SampPre: the sample is not a short preimage of its target (refused)".into(),
            ))
        }
    }

    /// Whether $`s_0 + h s_1 = t \bmod q`$, in exact integer arithmetic (one product with the
    /// prepared $`h`$), and $`\|s\|^2 \le \lfloor\beta_s^2\rfloor`$ (`u128` accumulation):
    /// `ntru_trapdoor::verify` under this key's $`h`$.
    fn is_short_preimage(&self, t: &Rq, s: &Preimage) -> bool {
        ntru_trapdoor::verify(&self.pk, t.poly(), s, S_BOUND)
    }

    /// TEST HOOK: `SampPre` on an arbitrary target $`t`$ with a fresh seed, counted toward the
    /// cap, for false-witness tests of the relations (an $`x_1`$ with a coefficient 2 needs a real
    /// preimage of its own target). Never part of the protocol: the helper samples only at the
    /// targets of `BlindIssue`. Feature `test-utils` outside this crate's tests.
    ///
    /// # Errors
    /// As `BlindIssue`: [`Error::InvalidKey`], [`Error::IssuanceCapReached`],
    /// [`Error::LatticeBackend`].
    #[cfg(any(test, feature = "test-utils"))]
    pub fn sample_preimage<R: RngCore + CryptoRng + ?Sized>(
        &self,
        t: &Rq,
        rng: &mut R,
    ) -> Result<VSISPreimage, Error> {
        self.preimage(t, rng).map(|s| VSISPreimage { s })
    }
}

impl Zeroize for VSISSigningKey {
    /// Wipes the trapdoor and the expanded key (the public count is kept). A wiped key signs
    /// nothing and cannot be encoded ([`Error::InvalidKey`]).
    fn zeroize(&mut self) {
        self.sk.zeroize();
        self.ek.zeroize();
    }
}

/// Both parts wipe themselves on drop (`ntru-trapdoor`).
impl ZeroizeOnDrop for VSISSigningKey {}

impl fmt::Debug for VSISSigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISSigningKey(<redacted>)")
    }
}

impl CanonicalSerialize for VSISSigningKey {
    /// Fails for a wiped key.
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        let bytes = self
            .encode(self.issued())
            .map_err(|_| SerializationError::InvalidData)?;
        writer.write_all(&bytes)?;
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for VSISSigningKey {
    /// The key holds a trapdoor and the count does not exceed $`Q_{\max}`$. (The trapdoor itself
    /// was validated when the value was made: by `TrapGen` or by decoding.)
    fn check(&self) -> Result<(), SerializationError> {
        if self.is_usable() && self.issued() <= Q_MAX {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl CanonicalDeserialize for VSISSigningKey {
    /// Always validates the trapdoor, whatever `validate` says.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = Zeroizing::new([0u8; Self::BYTES]);
        reader.read_exact(&mut *bytes)?;
        let (trapdoor, count) = bytes.split_at(SECRET_KEY_BYTES);
        let mut le = [0u8; 8];
        le.copy_from_slice(count);
        let issued = u64::from_le_bytes(le);
        if issued > Q_MAX {
            return Err(SerializationError::InvalidData);
        }
        let sk =
            SecretKey::from_bytes(&NTRU, trapdoor).map_err(|_| SerializationError::InvalidData)?;
        let ek = ExpandedKey::new(&sk).map_err(|_| SerializationError::InvalidData)?;
        // cannot fail for a validated trapdoor (f is invertible)
        let pk = sk
            .public_key()
            .map_err(|_| SerializationError::InvalidData)?;
        Ok(Self {
            sk,
            ek,
            pk,
            issued: AtomicU64::new(issued),
        })
    }
}

/// The verification key $`\mathsf{hvk} = h`$, with $`A = [1 \mid h]`$. Every canonically encoded
/// $`h \in R_q`$ is a key: the admissible key domain $`\mathcal V_{\mathsf{pp}}`$ is all of $`R_q`$
/// (the whole key space, as the paper states it; issuance simulatability holds for
/// every key, lem:base-vsis (b), and a public membership test for the range of `KeyGen` would
/// solve decisional NTRU), so [`VSIS::admissible_key`] refuses only a wiped key. Keeps
/// $`h`$ prepared for the product of `Verify`.
///
/// Encoding: $`h`$ ([`Rq`], [`Self::BYTES`] bytes). Equality compares $`h`$.
#[derive(Clone)]
pub struct VSISVerificationKey {
    h: Rq,
    pk: PublicKey,
}

impl VSISVerificationKey {
    /// Bytes of the encoding.
    pub const BYTES: usize = Rq::BYTES;

    /// The key $`A = [1 \mid h]`$.
    ///
    /// # Panics
    /// If `h` was wiped (`Zeroize` empties an [`Rq`], which is then no element of $`R_q`$; every
    /// other value is accepted).
    #[must_use]
    pub fn from_h(h: Rq) -> Self {
        match PublicKey::from_h(&NTRU, h.poly().clone()) {
            Ok(pk) => Self { h, pk },
            Err(error) => {
                panic!("VSISVerificationKey::from_h: h is not an element of R_q: {error}")
            }
        }
    }

    /// $`h`$.
    #[must_use]
    pub fn h(&self) -> &Rq {
        &self.h
    }
}

impl PartialEq for VSISVerificationKey {
    fn eq(&self, other: &Self) -> bool {
        self.h == other.h
    }
}

impl Eq for VSISVerificationKey {}

impl fmt::Debug for VSISVerificationKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISVerificationKey(h)")
    }
}

impl CanonicalSerialize for VSISVerificationKey {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.h.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for VSISVerificationKey {
    fn check(&self) -> Result<(), SerializationError> {
        self.h.check()
    }
}

impl CanonicalDeserialize for VSISVerificationKey {
    /// A canonical element of $`R_q`$, whatever `validate` says.
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        Rq::deserialize_with_mode(reader, compress, validate).map(Self::from_h)
    }
}

// ---------------------------------------------------------------------------------------------
// The issuance randomness
// ---------------------------------------------------------------------------------------------

/// The issuance randomness $`\tau = x_0 \gets \mathcal D_r`$ of the requester, kept from
/// `PrepareIssue` to `Unblind` and then in the credential ("a credential is a triple
/// $`(s, x_1, x_0)`$, which keeps the request randomizer"). Here $`\mathcal D_r`$ is uniform on
/// $`(\{-1, 0, 1\}^d)^{\ell_r}`$ with $`\ell_r = 3`$, under which the request is pseudorandom
/// by MLWE (module docs). Secret: wiped on drop, redacted in `Debug`, not `Clone`.
///
/// Encoding: $`x_{0,0} \| x_{0,1} \| x_{0,2}`$, $`\ell_r`$ [`Ternary`] ([`Self::BYTES`] bytes).
pub struct VSISTape([Ternary; ELL_R]);

impl VSISTape {
    /// Bytes of the encoding.
    pub const BYTES: usize = ELL_R * Ternary::BYTES;

    /// $`x_0 \gets \mathcal D_r`$: two uniform ternary elements.
    pub fn sample<R: RngCore + CryptoRng + ?Sized>(rng: &mut R) -> Self {
        Self(core::array::from_fn(|_| Ternary::sample(rng)))
    }

    /// $`x_0`$ from its components.
    #[must_use]
    pub fn new(x0: [Ternary; ELL_R]) -> Self {
        Self(x0)
    }

    /// $`x_0`$.
    #[must_use]
    pub fn x0(&self) -> &[Ternary; ELL_R] {
        &self.0
    }

    /// `a == b`, in constant time.
    #[must_use]
    pub fn ct_eq(&self, other: &Self) -> bool {
        self.0
            .iter()
            .zip(&other.0)
            .fold(true, |equal, (x, y)| equal & x.ct_eq(y))
    }

    /// Whether no component was wiped.
    fn is_short(&self) -> bool {
        self.0.iter().all(is_short)
    }

    /// A copy, for the credential that keeps $`x_0`$. Crate-internal: a tape is not `Clone`.
    fn duplicate(&self) -> Self {
        Self(self.0.clone())
    }
}

impl Zeroize for VSISTape {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

/// Its components wipe themselves on drop.
impl ZeroizeOnDrop for VSISTape {}

impl fmt::Debug for VSISTape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISTape(<redacted>)")
    }
}

impl CanonicalSerialize for VSISTape {
    /// Fails for a wiped component.
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        for x in &self.0 {
            x.serialize_with_mode(&mut writer, compress)?;
        }
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for VSISTape {
    fn check(&self) -> Result<(), SerializationError> {
        self.0.iter().try_for_each(Valid::check)
    }
}

impl CanonicalDeserialize for VSISTape {
    /// Two canonical [`Ternary`], whatever `validate` says.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let x0 = (0..ELL_R)
            .map(|_| Ternary::deserialize_with_mode(&mut reader, compress, validate))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self(
            x0.try_into().map_err(|_| SerializationError::InvalidData)?,
        ))
    }
}

// ---------------------------------------------------------------------------------------------
// Pre-credentials and credentials
// ---------------------------------------------------------------------------------------------

/// A preimage $`s = (s_0, s_1)`$ returned by the test hook
/// [`VSISSigningKey::sample_preimage`].
#[cfg(any(test, feature = "test-utils"))]
pub struct VSISPreimage {
    s: Preimage,
}

#[cfg(any(test, feature = "test-utils"))]
impl fmt::Debug for VSISPreimage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISPreimage(<redacted>)")
    }
}

#[cfg(any(test, feature = "test-utils"))]
impl VSISPreimage {
    /// $`s_0`$.
    #[must_use]
    pub fn s0(&self) -> &[i32] {
        &self.s.s0
    }

    /// $`s_1`$.
    #[must_use]
    pub fn s1(&self) -> &[i32] {
        &self.s.s1
    }
}

/// A pre-credential $`\widehat{\sigma} = (s, x_1)`$ of `BlindIssue`: the preimage
/// $`s = (s_0, s_1)`$ with $`s_0 + h s_1 = t`$ and the signing randomness $`x_1`$. The helper
/// sends it to the requester; with $`x_0`$ it becomes the credential. Compared in constant time.
///
/// Encoding: $`s_0 \| s_1`$ at 20 bits per coefficient in two's complement
/// ([`crate::lattice::ring`], `pack_signed`; $`|s_i| < 2^{19}`$, while every verifying
/// credential has $`|s_i| \le \lfloor\beta_s\rfloor = 301{,}336`$), then $`x_1`$ ([`Ternary`]):
/// [`Self::BYTES`] bytes.
#[derive(Clone)]
pub struct VSISPreCredential {
    s: Preimage,
    x1: Ternary,
}

impl VSISPreCredential {
    /// Bytes of the encoding: $`2 \cdot 2560 + 256`$.
    pub const BYTES: usize = 2 * S_HALF_BYTES + Ternary::BYTES;

    /// $`(s, x_1)`$ from its parts. The vectors are wiped when the value is dropped, and on
    /// every error path.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless $`s_0`$, $`s_1`$ and $`x_1`$ have $`d`$ coefficients
    /// (a wiped $`x_1`$ has none); [`Error::InvalidCredential`] for a coefficient with
    /// $`|s_i| \ge 2^{19}`$ (not encodable).
    pub fn from_parts(s0: Vec<i32>, s1: Vec<i32>, x1: Ternary) -> Result<Self, Error> {
        let s = Preimage { s0, s1 };
        for actual in [s.s0.len(), s.s1.len(), x1.coeffs().len()] {
            if actual != D {
                return Err(Error::LengthMismatch {
                    expected: D,
                    actual,
                });
            }
        }
        if s.s0
            .iter()
            .chain(&s.s1)
            .any(|&c| c.unsigned_abs() > S_MAX_ABS)
        {
            return Err(Error::InvalidCredential);
        }
        Ok(Self { s, x1 })
    }

    /// $`s_0`$, the coefficients that multiply $`1`$.
    #[must_use]
    pub fn s0(&self) -> &[i32] {
        &self.s.s0
    }

    /// $`s_1`$, the coefficients that multiply $`h`$.
    #[must_use]
    pub fn s1(&self) -> &[i32] {
        &self.s.s1
    }

    /// $`\|s\|^2`$, saturating.
    #[must_use]
    pub fn norm_sq(&self) -> u64 {
        self.s.norm_sq()
    }

    /// $`x_1`$.
    #[must_use]
    pub fn x1(&self) -> &Ternary {
        &self.x1
    }

    /// Whether all three parts have $`d`$ coefficients (they do unless the value was wiped).
    fn is_well_formed(&self) -> bool {
        self.s.s0.len() == D && self.s.s1.len() == D && is_short(&self.x1)
    }

    /// Whether every coefficient of $`s`$ is encodable.
    fn is_encodable(&self) -> bool {
        self.s
            .s0
            .iter()
            .chain(&self.s.s1)
            .all(|&c| c.unsigned_abs() <= S_MAX_ABS)
    }
}

impl PartialEq for VSISPreCredential {
    /// In constant time (no early exit on the first difference; the lengths are public).
    fn eq(&self, other: &Self) -> bool {
        if self.s.s0.len() != other.s.s0.len() || self.s.s1.len() != other.s.s1.len() {
            return false;
        }
        let diff = self
            .s
            .s0
            .iter()
            .zip(&other.s.s0)
            .chain(self.s.s1.iter().zip(&other.s.s1))
            .fold(0u32, |acc, (&a, &b)| acc | (a ^ b) as u32);
        (diff == 0) & self.x1.ct_eq(&other.x1)
    }
}

impl Eq for VSISPreCredential {}

impl Zeroize for VSISPreCredential {
    fn zeroize(&mut self) {
        self.s.zeroize();
        self.x1.zeroize();
    }
}

/// Both parts wipe themselves on drop.
impl ZeroizeOnDrop for VSISPreCredential {}

impl fmt::Debug for VSISPreCredential {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISPreCredential(<redacted>)")
    }
}

impl CanonicalSerialize for VSISPreCredential {
    /// Fails for a wiped pre-credential and for a coefficient $`|s_i| \ge 2^{19}`$.
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        if !self.is_well_formed() {
            return Err(SerializationError::InvalidData);
        }
        // Exact capacity: no reallocation leaves copies of the witness behind.
        let mut bytes = Zeroizing::new(Vec::with_capacity(Self::BYTES));
        pack_signed(&self.s.s0, S_BITS, &mut bytes)?;
        pack_signed(&self.s.s1, S_BITS, &mut bytes)?;
        bytes.extend_from_slice(&self.x1.to_bytes());
        debug_assert_eq!(bytes.len(), Self::BYTES);
        writer.write_all(&bytes)?;
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for VSISPreCredential {
    fn check(&self) -> Result<(), SerializationError> {
        if self.is_well_formed() && self.is_encodable() {
            self.x1.check()
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl CanonicalDeserialize for VSISPreCredential {
    /// Always checks canonicity (no code $`-2^{19}`$, no ternary code `10`), whatever `validate`
    /// says; does not check the norm (that is `Verify`).
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = Zeroizing::new([0u8; Self::BYTES]);
        reader.read_exact(&mut *bytes)?;
        let (s_bytes, x1_bytes) = bytes.split_at(2 * S_HALF_BYTES);
        let (s0_bytes, s1_bytes) = s_bytes.split_at(S_HALF_BYTES);
        let mut s0 = unpack_signed(s0_bytes, D, S_BITS)?;
        let mut s1 = unpack_signed(s1_bytes, D, S_BITS)?;
        // From here on the preimage owns the coefficients and wipes them on drop.
        let s = Preimage {
            s0: core::mem::take(&mut *s0),
            s1: core::mem::take(&mut *s1),
        };
        let x1 = Ternary::from_bytes(x1_bytes).map_err(|_| SerializationError::InvalidData)?;
        Ok(Self { s, x1 })
    }
}

/// A credential $`\sigma = (s, x_1, x_0)`$: the pre-credential and the issuance randomness it
/// was requested with. It is the WITNESS of the possession relation (the show is the empty
/// encoding), so it is secret to its holder: wiped on drop, redacted in `Debug`, compared in
/// constant time. (The helper saw $`(s, x_1)`$ at issuance; zero knowledge is what keeps the
/// proofs unlinkable.)
///
/// Encoding: the [`VSISPreCredential`], then the [`VSISTape`]: [`Self::BYTES`] bytes.
pub struct VSISCredential {
    pre: VSISPreCredential,
    x0: VSISTape,
}

impl VSISCredential {
    /// Bytes of the encoding: $`5376 + 512`$.
    pub const BYTES: usize = VSISPreCredential::BYTES + VSISTape::BYTES;

    /// $`(s, x_1, x_0)`$ from a pre-credential and an issuance randomness; unchecked (that is
    /// [`VSIS::verify`]).
    #[must_use]
    pub fn from_parts(pre: VSISPreCredential, x0: VSISTape) -> Self {
        Self { pre, x0 }
    }

    /// The pre-credential $`(s, x_1)`$.
    #[must_use]
    pub fn pre(&self) -> &VSISPreCredential {
        &self.pre
    }

    /// $`x_0`$.
    #[must_use]
    pub fn x0(&self) -> &[Ternary; ELL_R] {
        self.x0.x0()
    }

    /// Whether every component has its length (it has unless the value was wiped).
    fn is_well_formed(&self) -> bool {
        self.pre.is_well_formed() && self.x0.is_short()
    }
}

impl Clone for VSISCredential {
    fn clone(&self) -> Self {
        Self {
            pre: self.pre.clone(),
            x0: self.x0.duplicate(),
        }
    }
}

impl PartialEq for VSISCredential {
    /// In constant time.
    fn eq(&self, other: &Self) -> bool {
        (self.pre == other.pre) & self.x0.ct_eq(&other.x0)
    }
}

impl Eq for VSISCredential {}

impl Zeroize for VSISCredential {
    fn zeroize(&mut self) {
        self.pre.zeroize();
        self.x0.zeroize();
    }
}

/// Both parts wipe themselves on drop.
impl ZeroizeOnDrop for VSISCredential {}

impl fmt::Debug for VSISCredential {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISCredential(<redacted>)")
    }
}

impl CanonicalSerialize for VSISCredential {
    /// Fails for a wiped credential.
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.pre.serialize_with_mode(&mut writer, compress)?;
        self.x0.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        Self::BYTES
    }
}

impl Valid for VSISCredential {
    fn check(&self) -> Result<(), SerializationError> {
        self.pre.check()?;
        self.x0.check()
    }
}

impl CanonicalDeserialize for VSISCredential {
    /// Strict, as its two parts.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let pre = VSISPreCredential::deserialize_with_mode(&mut reader, compress, validate)?;
        let x0 = VSISTape::deserialize_with_mode(reader, compress, validate)?;
        Ok(Self { pre, x0 })
    }
}

// ---------------------------------------------------------------------------------------------
// The base
// ---------------------------------------------------------------------------------------------

impl VSIS {
    /// `PGen` for the deployment label `label`: the four elements of [`VSISParams`], each the
    /// uniform element of $`R_q`$ that the oracle `/LATTICE-PP` outputs for the items
    /// `("deployment", label)` and `("element", name)` (`lattice::xof::pp_element`, rejection
    /// sampling of 20-bit chunks below $`q`$). Public randomness: SHAKE128 of the label, so
    /// nobody knows a trapdoor or a short relation for them (in the random-oracle model).
    #[must_use]
    pub fn setup(label: &[u8]) -> VSISParams {
        VSISParams::from_elements(
            pp_element(label, b"v"),
            pp_element(label, b"b_u"),
            core::array::from_fn(|k| pp_element(label, &b_r_name(k))),
        )
    }

    /// `KeyGen`: $`(A = [1 \mid h], td_A) \gets \mathsf{TrapGen}`$ from a fresh 32-byte seed
    /// (`ntru_trapdoor::trapgen` at the PCS set, about 6 ms), and the expanded key; the counter
    /// starts at 0. The trapdoor is independent of `pp_Σ` and is a function of the seed: `rng`
    /// must be a CSPRNG seeded by the operating system (module docs).
    ///
    /// # Panics
    /// Only if `TrapGen` fails for 4 fresh seeds in a row (a seed fails when 4096 candidates are
    /// rejected, which does not happen in practice: about 1 candidate in 20 is accepted).
    pub fn keygen<R: RngCore + CryptoRng + ?Sized>(
        rng: &mut R,
    ) -> (VSISVerificationKey, VSISSigningKey) {
        for _ in 0..KEYGEN_ATTEMPTS {
            let seed = fresh_seed(rng);
            let Ok((pk, sk)) = trapgen(&NTRU, &seed) else {
                continue;
            };
            // Cannot fail for a key of TrapGen, which built and checked the same tree.
            let Ok(ek) = ExpandedKey::new(&sk) else {
                continue;
            };
            let vk = VSISVerificationKey {
                h: Rq::from_poly(pk.h().clone()),
                pk: pk.clone(),
            };
            let sk = VSISSigningKey {
                sk,
                ek,
                pk,
                issued: AtomicU64::new(0),
            };
            return (vk, sk);
        }
        panic!("Σ-vSIS KeyGen: TrapGen failed for {KEYGEN_ATTEMPTS} fresh seeds");
    }

    /// $`h \in \mathcal V_{\mathsf{pp}}`$: every canonically encoded element of $`R_q`$, which
    /// every value of [`VSISVerificationKey`] is unless it was wiped.
    #[must_use]
    pub fn admissible_key(vk: &VSISVerificationKey) -> bool {
        vk.h.coeffs().len() == D
    }

    /// Whether `sk` is the trapdoor of `vk`: the public key of the trapdoor is $`h`$.
    #[must_use]
    pub fn key_pair_matches(vk: &VSISVerificationKey, sk: &VSISSigningKey) -> bool {
        sk.is_usable() && Rq::from_poly(sk.pk.h().clone()) == vk.h
    }

    /// `PrepareIssue(vk, usk; x_0)`: `⊥` (`None`) if $`\|\mathsf{usk}\|_\infty > \beta_u`$ or
    /// $`\|x_0\|_\infty > \beta_r`$, which for the types here means a wiped component;
    /// otherwise $`C = b_u\,\mathsf{usk} + B_r x_0 \bmod q`$ ($`1 + \ell_r`$ products with
    /// prepared operands). The key does not enter.
    #[must_use]
    pub fn prepare_issue(pp: &VSISParams, usk: &Ternary, tape: &VSISTape) -> Option<Rq> {
        pp.commitment(usk, tape.x0())
    }

    /// `BlindIssue(sk, C)`:
    /// 1. $`x_1 \gets \mathcal X_1`$ until $`v - x_1`$ is a unit, `⊥` after $`\lambda`$
    ///    attempts;
    /// 2. $`t = (v - x_1)^{-1} + C`$;
    /// 3. $`s \gets \mathsf{SampPre}(td_A, t, \varsigma)`$ with a fresh seed, under the cap;
    /// 4. $`\widehat{\sigma} = (s, x_1)`$.
    ///
    /// Every $`C \in R_q`$ is accepted, as in the box: the protocol calls this only after it
    /// verified the issuance proof (the proof-gated oracle of lem:base-vsis (d.i)).
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped key; [`Error::InvalidIssuanceEncoding`] for a wiped
    /// $`C`$; [`Error::IssuanceCapReached`] at the cap; [`Error::LatticeBackend`] if a bounded
    /// loop gives up (module docs).
    pub fn blind_issue<R: RngCore + CryptoRng + ?Sized>(
        pp: &VSISParams,
        sk: &VSISSigningKey,
        c: &Rq,
        rng: &mut R,
    ) -> Result<VSISPreCredential, Error> {
        sk.ensure_usable()?;
        if c.coeffs().len() != D {
            return Err(Error::InvalidIssuanceEncoding);
        }
        let (x1, y) = pp.sample_x1(rng)?;
        let t = Zeroizing::new(y.add(c));
        let s = sk.preimage(&t, rng)?;
        Ok(VSISPreCredential { s, x1 })
    }

    /// `Unblind(vk, usk, (s, x_1), x_0)`: the credential $`(s, x_1, x_0)`$ if `Verify` accepts
    /// it, `⊥` otherwise (the box verifies here).
    ///
    /// # Errors
    /// [`Error::InvalidPreCredential`] if `Verify` rejects.
    pub fn unblind(
        pp: &VSISParams,
        vk: &VSISVerificationKey,
        usk: &Ternary,
        pre: &VSISPreCredential,
        tape: &VSISTape,
    ) -> Result<VSISCredential, Error> {
        let cred = VSISCredential::from_parts(pre.clone(), tape.duplicate());
        if Self::verify(pp, vk, usk, &cred) {
            Ok(cred)
        } else {
            Err(Error::InvalidPreCredential)
        }
    }

    /// `Verify(vk, usk, (s, x_1, x_0))`, in the product form of the module docs: `false` unless
    /// every component has its length (only a wiped value has not), $`0 < \|s\|^2 \le
    /// \lfloor\beta_s^2\rfloor`$ (exact, `u128` accumulation), and
    /// $`(s_0 + h s_1 - b_u\,\mathsf{usk} - B_r x_0)\cdot(v - x_1) = 1`$. Four products with
    /// prepared operands and one plain product. Never panics.
    #[must_use]
    pub fn verify(
        pp: &VSISParams,
        vk: &VSISVerificationKey,
        usk: &Ternary,
        cred: &VSISCredential,
    ) -> bool {
        // The norm conditions; "v - x_1 is invertible" is part of the product form.
        let norm = cred.pre.norm_sq();
        if !is_short(usk) || !cred.is_well_formed() || norm == 0 || norm > S_BOUND {
            return false;
        }
        let Some(residual) = pp.residual(vk, usk, cred.x0.x0(), &cred.pre.s) else {
            return false;
        };
        let g = Zeroizing::new(pp.v.sub(&Zeroizing::new(cred.pre.x1.to_rq())));
        is_one(&Zeroizing::new(residual.mul(&g)))
    }
}

#[cfg(test)]
mod tests {
    use std::thread;

    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        lattice::Q,
        serialization::{from_bytes, to_bytes},
    };

    const LABEL: &[u8] = b"PCS-VSIS-UNIT-TESTS";

    struct Fixture {
        pp: VSISParams,
        vk: VSISVerificationKey,
        sk: VSISSigningKey,
        rng: StdRng,
    }

    /// `pp` of [`LABEL`] and ONE real helper key (TrapGen).
    fn fixture(seed: u64) -> Fixture {
        let mut rng = StdRng::seed_from_u64(seed);
        let pp = VSIS::setup(LABEL);
        let (vk, sk) = VSIS::keygen(&mut rng);
        Fixture { pp, vk, sk, rng }
    }

    /// A uniform key and issuance randomness.
    fn message(rng: &mut StdRng) -> (Ternary, VSISTape) {
        (Ternary::sample(rng), VSISTape::sample(rng))
    }

    /// `x` with its coefficient `i` replaced by another value of {-1, 0, 1}.
    fn changed(x: &Ternary, i: usize) -> Ternary {
        let mut c = x.coeffs().to_vec();
        c[i] = if c[i] == 1 { 0 } else { c[i] + 1 };
        Ternary::from_coeffs(&c).unwrap()
    }

    fn rq_of(values: &[i32]) -> Rq {
        Rq::from_i64(&values.iter().map(|&x| i64::from(x)).collect::<Vec<_>>()).unwrap()
    }

    /// A vector of length d whose squared norm is exactly `n` (greedy sum of squares).
    fn with_norm_sq(mut n: u64) -> Vec<i32> {
        let mut v = vec![0i32; D];
        let mut i = 0;
        while n > 0 {
            let a = n.isqrt();
            v[i] = i32::try_from(a).unwrap();
            n -= a * a;
            i += 1;
        }
        v
    }

    /// A credential of the fixture's key on a fresh message.
    fn issued(fx: &mut Fixture) -> (Ternary, VSISCredential) {
        let (usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
        let cred = VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).unwrap();
        (usk, cred)
    }

    // ----- PGen -----------------------------------------------------------------------------

    /// `pp_Σ` is the expansion of the label under the documented element names (the known answers
    /// are those of `lattice::xof`, computed independently with Python's hashlib).
    #[test]
    fn setup_expands_the_label_under_the_documented_names() {
        let pp = VSIS::setup(b"PCS-LATTICE-KAT");
        let kat: [(&Rq, [u32; 4], u32, u32); 4] = [
            (pp.v(), [770406, 508595, 476174, 818112], 192742, 537406709),
            (pp.b_u(), [444343, 26088, 417981, 121684], 367357, 565256750),
            (
                &pp.b_r()[0],
                [259614, 480301, 168799, 919508],
                4759,
                544383178,
            ),
            (
                &pp.b_r()[1],
                [225220, 853749, 851519, 200578],
                210172,
                548614151,
            ),
        ];
        for (k, (element, first, last, sum)) in kat.into_iter().enumerate() {
            let c = element.coeffs();
            assert_eq!(&c[..4], &first, "element {k}");
            assert_eq!(c[D - 1], last, "element {k}");
            assert_eq!(c.iter().fold(0u32, |acc, &x| acc.wrapping_add(x)), sum);
        }
        // deterministic, separated by the label, 2 + ℓ_r distinct elements
        assert_eq!(VSIS::setup(LABEL), VSIS::setup(LABEL));
        let other = VSIS::setup(b"another deployment");
        let ours = VSIS::setup(LABEL);
        for (a, b) in ours.elements().zip(other.elements()) {
            assert_ne!(a, b);
        }
        let e: Vec<&Rq> = ours.elements().collect();
        assert_eq!(e.len(), 2 + ELL_R);
        for i in 0..e.len() {
            for j in i + 1..e.len() {
                assert_ne!(e[i], e[j]);
            }
        }
        assert_eq!(format!("{ours:?}"), "VSISParams(v, b_u, B_r)");
    }

    #[test]
    fn public_parameters_round_trip_with_their_prepared_columns() {
        let mut rng = StdRng::seed_from_u64(0x5151_0001);
        let pp = VSIS::setup(LABEL);
        let bytes = to_bytes(&pp).unwrap();
        assert_eq!(bytes.len(), VSISParams::BYTES);
        assert_eq!(bytes.len(), 12_800);
        let back: VSISParams = from_bytes(&bytes).unwrap();
        assert_eq!(back, pp);
        assert!(back.check().is_ok());
        // the prepared columns of the decoded value compute the same products
        let (usk, tape) = message(&mut rng);
        assert_eq!(
            VSIS::prepare_issue(&back, &usk, &tape),
            VSIS::prepare_issue(&pp, &usk, &tape)
        );
        // a coefficient q in the last element, a short and a long input are refused
        let mut bad = bytes.clone();
        let at = 3 * Rq::BYTES;
        bad[at] = (Q & 0xff) as u8;
        bad[at + 1] = ((Q >> 8) & 0xff) as u8;
        bad[at + 2] = (bad[at + 2] & 0xf0) | ((Q >> 16) & 0x0f) as u8;
        assert!(from_bytes::<VSISParams>(&bad).is_err());
        assert!(from_bytes::<VSISParams>(&bytes[..bytes.len() - 1]).is_err());
        let mut long = bytes;
        long.push(0);
        assert_eq!(
            from_bytes::<VSISParams>(&long).unwrap_err(),
            Error::TrailingBytes
        );
    }

    // ----- KeyGen ---------------------------------------------------------------------------

    #[test]
    fn keygen_outputs_a_trapdoor_for_its_key() {
        let fx = fixture(0x5151_0002);
        assert_eq!(fx.sk.verification_key().unwrap(), fx.vk);
        assert!(VSIS::admissible_key(&fx.vk));
        assert!(VSIS::key_pair_matches(&fx.vk, &fx.sk));
        assert_eq!(fx.sk.issued(), 0);
        assert_eq!(fx.sk.remaining(), Q_MAX);
        assert_eq!(fx.sk.sk.to_bytes().len(), SECRET_KEY_BYTES);
        // a fresh seed per call: another key, which the first trapdoor does not match
        let mut rng = StdRng::seed_from_u64(0x5151_0003);
        let (vk2, sk2) = VSIS::keygen(&mut rng);
        assert_ne!(vk2, fx.vk);
        assert!(!VSIS::key_pair_matches(&vk2, &fx.sk));
        assert!(!VSIS::key_pair_matches(&fx.vk, &sk2));
        // V_pp is every canonical h: any element is a key
        let any = VSISVerificationKey::from_h(VSIS::setup(b"h").v().clone());
        assert!(VSIS::admissible_key(&any));
        assert_eq!(format!("{any:?}"), "VSISVerificationKey(h)");
        let bytes = to_bytes(&fx.vk).unwrap();
        assert_eq!(bytes.len(), VSISVerificationKey::BYTES);
        assert_eq!(from_bytes::<VSISVerificationKey>(&bytes).unwrap(), fx.vk);
    }

    #[test]
    fn the_signing_key_is_shared_across_threads() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<VSISSigningKey>();
        assert_send_sync::<VSISParams>();
        assert_send_sync::<VSISVerificationKey>();
        assert_send_sync::<VSISPreCredential>();
        assert_send_sync::<VSISCredential>();
    }

    // ----- PrepareIssue, BlindIssue, Unblind, Verify -----------------------------------------

    /// `PrepareIssue` is b_u usk + B_r x_0, computed with the plain products here.
    #[test]
    fn prepare_issue_is_the_documented_sum() {
        let mut fx = fixture(0x5151_0004);
        let (usk, tape) = message(&mut fx.rng);
        let pp = &fx.pp;
        let expected = pp
            .b_r()
            .iter()
            .zip(tape.x0())
            .fold(pp.b_u().mul(&usk.to_rq()), |c, (b, x)| {
                c.add(&b.mul(&x.to_rq()))
            });
        assert_eq!(VSIS::prepare_issue(pp, &usk, &tape).unwrap(), expected);
    }

    #[test]
    fn issued_credentials_verify() {
        let mut fx = fixture(0x5151_0005);
        let (usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
        let cred = VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).unwrap();
        assert_eq!(cred.pre(), &pre);
        assert!(cred.x0().iter().zip(tape.x0()).all(|(a, b)| a == b));
        assert!(VSIS::verify(&fx.pp, &fx.vk, &usk, &cred));
        assert!(pre.norm_sq() <= S_BOUND && pre.norm_sq() > 0);
        assert_eq!(fx.sk.issued(), 1);
        // fresh coins: two pre-credentials on one request differ
        let again = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
        assert_ne!(again, pre);
        assert_eq!(fx.sk.issued(), 2);
    }

    #[test]
    fn verify_refuses_every_changed_input() {
        let mut fx = fixture(0x5151_0007);
        let (usk, cred) = issued(&mut fx);
        let (pp, vk) = (&fx.pp, &fx.vk);
        assert!(VSIS::verify(pp, vk, &usk, &cred));

        // another usk
        assert!(!VSIS::verify(pp, vk, &changed(&usk, 0), &cred));
        // another x_0 component, another x_1, another s_0, another s_1
        let pre = cred.pre();
        let x0 = cred.x0();
        // a changed coefficient in the first and in the last component of x_0
        let with = |k: usize, i: usize| {
            let mut x0 = x0.clone();
            x0[k] = changed(&x0[k], i);
            VSISTape::new(x0)
        };
        let tampered = [
            VSISCredential::from_parts(pre.clone(), with(0, 500)),
            VSISCredential::from_parts(pre.clone(), with(ELL_R - 1, 1023)),
            VSISCredential::from_parts(
                VSISPreCredential::from_parts(
                    pre.s0().to_vec(),
                    pre.s1().to_vec(),
                    changed(pre.x1(), 11),
                )
                .unwrap(),
                VSISTape::new(x0.clone()),
            ),
            {
                let mut s0 = pre.s0().to_vec();
                s0[17] += 1;
                VSISCredential::from_parts(
                    VSISPreCredential::from_parts(s0, pre.s1().to_vec(), pre.x1().clone()).unwrap(),
                    VSISTape::new(x0.clone()),
                )
            },
            {
                let mut s1 = pre.s1().to_vec();
                s1[900] -= 1;
                VSISCredential::from_parts(
                    VSISPreCredential::from_parts(pre.s0().to_vec(), s1, pre.x1().clone()).unwrap(),
                    VSISTape::new(x0.clone()),
                )
            },
        ];
        for t in &tampered {
            assert!(!VSIS::verify(pp, vk, &usk, t));
        }

        // another key, other parameters
        let (vk2, _) = VSIS::keygen(&mut fx.rng);
        assert!(!VSIS::verify(pp, &vk2, &usk, &cred));
        let pp2 = VSIS::setup(b"another deployment");
        assert!(!VSIS::verify(&pp2, vk, &usk, &cred));
    }

    /// `Verify` accepts ‖s‖² = ⌊β_s²⌋ and refuses ⌊β_s²⌋ + 1: s_1 = 1 and an s_0 of the chosen
    /// norm, under the key h = t - s_0 for which A s = t (every h is a key).
    #[test]
    fn verify_enforces_the_norm_bound_exactly() {
        let mut rng = StdRng::seed_from_u64(0x5151_0008);
        let pp = VSIS::setup(LABEL);
        let (usk, tape) = message(&mut rng);
        let (x1, y) = pp.sample_x1(&mut rng).unwrap();
        let c = VSIS::prepare_issue(&pp, &usk, &tape).unwrap();
        let t = y.add(&c);
        let mut s1 = vec![0i32; D];
        s1[0] = 1;
        for (norm, accepted) in [(S_BOUND - 1, true), (S_BOUND, true), (S_BOUND + 1, false)] {
            let s0 = with_norm_sq(norm - 1);
            let vk = VSISVerificationKey::from_h(t.sub(&rq_of(&s0)));
            let cred = VSISCredential::from_parts(
                VSISPreCredential::from_parts(s0, s1.clone(), x1.clone()).unwrap(),
                VSISTape::new(tape.x0().clone()),
            );
            assert_eq!(cred.pre().norm_sq(), norm);
            assert_eq!(
                VSIS::verify(&pp, &vk, &usk, &cred),
                accepted,
                "‖s‖² = {norm}"
            );
        }
    }

    /// `Verify` requires `0 < ‖s‖` ("Return 0 unless … 0 < ‖s‖ ≤ β_s"). With parameters built
    /// by hand so that `s = 0` satisfies the equation (`b_u = −(v − x_1)^{-1}`, `usk = 1`,
    /// `x_0 = 0`, so that `A·0 − b_u·usk − B_r·x_0 = (v − x_1)^{-1}`), only that check refuses
    /// the credential. The possession proofs refuse such a witness too, by the lower bound on
    /// $`\|s\|^2`$ (`relations`, `s_equal_to_zero_is_refused_by_the_lower_bound`).
    #[test]
    fn verify_refuses_s_equal_to_zero() {
        let mut rng = StdRng::seed_from_u64(0x5151_0009);
        let honest = VSIS::setup(LABEL);
        let (x1, y) = honest.sample_x1(&mut rng).unwrap();
        let pp = VSISParams::from_elements(honest.v().clone(), y.neg(), honest.b_r().clone());
        let mut one = vec![0i8; D];
        one[0] = 1;
        let usk = Ternary::from_coeffs(&one).unwrap();
        let tape = VSISTape::new(core::array::from_fn(|_| Ternary::zero()));
        let zero = VSISPreCredential::from_parts(vec![0; D], vec![0; D], x1).unwrap();
        let cred = VSISCredential::from_parts(zero, tape);
        let (vk, _) = VSIS::keygen(&mut rng);
        // the equation holds: (A·0 − b_u·usk − B_r·0)(v − x_1) = (v − x_1)^{-1}(v − x_1) = 1
        let residual = pp.residual(&vk, &usk, cred.x0(), &cred.pre().s).unwrap();
        let g = pp.v().sub(&cred.pre().x1().to_rq());
        assert!(is_one(&residual.mul(&g)));
        assert_eq!(cred.pre().norm_sq(), 0);
        assert!(!VSIS::verify(&pp, &vk, &usk, &cred));
    }

    /// Without the norm check the product form accepts a far-away preimage of the same target:
    /// s'_1 = s_1 + 1 and s'_0 = t - h s'_1 (centred) satisfy A s' = t with ‖s'‖² ≈ 2^46.
    #[test]
    fn the_norm_check_is_what_refuses_a_long_preimage() {
        let mut fx = fixture(0x5151_000a);
        let (usk, cred) = issued(&mut fx);
        let pre = cred.pre();
        let h = fx.vk.h();
        let t = rq_of(pre.s0()).add(&h.mul(&rq_of(pre.s1())));
        let mut s1 = pre.s1().to_vec();
        s1[0] += 1;
        let s0 = t.sub(&h.mul(&rq_of(&s1))).to_centered();
        let long = VSISCredential::from_parts(
            VSISPreCredential::from_parts(s0, s1, pre.x1().clone()).unwrap(),
            VSISTape::new(cred.x0().clone()),
        );
        assert!(long.pre().norm_sq() > S_BOUND);
        let residual = fx
            .pp
            .residual(&fx.vk, &usk, long.x0(), &long.pre().s)
            .unwrap();
        let g = fx.pp.v().sub(&long.pre().x1().to_rq());
        assert!(is_one(&residual.mul(&g)), "the equation holds");
        assert!(!VSIS::verify(&fx.pp, &fx.vk, &usk, &long));
    }

    #[test]
    fn unblind_fails_closed() {
        let mut fx = fixture(0x5151_000b);
        let (usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        // issued on another C (another x_0)
        let mut x0 = tape.x0().clone();
        x0[0] = changed(&x0[0], 3);
        let other = VSISTape::new(x0);
        let c2 = VSIS::prepare_issue(&fx.pp, &usk, &other).unwrap();
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c2, &mut fx.rng).unwrap();
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).unwrap_err(),
            Error::InvalidPreCredential
        );
        // issued under another key
        let (_, sk2) = VSIS::keygen(&mut fx.rng);
        let pre = VSIS::blind_issue(&fx.pp, &sk2, &c, &mut fx.rng).unwrap();
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).unwrap_err(),
            Error::InvalidPreCredential
        );
        // the right pre-credential with another issuance randomness, or another key
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &other).unwrap_err(),
            Error::InvalidPreCredential
        );
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &changed(&usk, 9), &pre, &tape).unwrap_err(),
            Error::InvalidPreCredential
        );
        assert!(VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).is_ok());
    }

    /// The preimages have the width of the PCS set: E‖s‖² = 2dσ² for the coset Gaussian of
    /// σ = ς/√(2π) = 2656.42. The standard deviation of ‖s‖²/(2dσ²) is √(2/2048) = 1/32 per
    /// preimage, so in the normal approximation one preimage leaves ±20% with probability about
    /// 2^-32.6 and the mean of 8 leaves ±5% with probability about 2^-17.3 [computed]. x_1 is
    /// uniform ternary.
    #[test]
    fn preimages_and_x1_have_the_documented_distributions() {
        let mut fx = fixture(0x5151_000c);
        let (usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        let sigma = ntru_trapdoor::Params::PCS.sigma;
        let expected = 2.0 * D as f64 * sigma * sigma;
        let mut total = 0.0;
        let mut counts = [0usize; 3];
        for _ in 0..8 {
            let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
            let ratio = pre.norm_sq() as f64 / expected;
            assert!((0.8..1.2).contains(&ratio), "‖s‖²/(2dσ²) = {ratio}");
            assert!(pre.is_encodable());
            total += ratio;
            for &x in pre.x1().coeffs() {
                counts[(x + 1) as usize] += 1;
            }
        }
        let mean = total / 8.0;
        assert!((0.95..1.05).contains(&mean), "mean ‖s‖²/(2dσ²) = {mean}");
        // 8192 uniform ternary coefficients: each value 2731 ± 256 (6 standard deviations)
        assert!(
            counts.iter().all(|&n| (2475..=2987).contains(&n)),
            "{counts:?}"
        );
    }

    /// `SampPre` on an arbitrary target (the test hook): an exact, short preimage, counted.
    #[test]
    fn the_test_hook_samples_preimages_of_arbitrary_targets() {
        let mut fx = fixture(0x5151_000d);
        for k in 0..3u64 {
            let t = VSIS::setup(&k.to_le_bytes()).v().clone();
            let s = fx.sk.sample_preimage(&t, &mut fx.rng).unwrap();
            assert!(ntru_trapdoor::verify(&fx.vk.pk, t.poly(), &s.s, S_BOUND));
        }
        assert_eq!(fx.sk.issued(), 3);
    }

    /// The exact check every preimage passes before it is released (`s ∈ Λ_t` in integer
    /// arithmetic): it accepts the sampler's outputs and refuses a vector one unit off in either
    /// half, a preimage presented for another target, and a long vector of the coset.
    #[test]
    fn preimages_are_checked_exactly_before_release() {
        let mut fx = fixture(0x5151_000e);
        let t = VSIS::setup(b"target").v().clone();
        let s = fx.sk.sample_preimage(&t, &mut fx.rng).unwrap().s;
        assert!(fx.sk.is_short_preimage(&t, &s));
        let other = VSIS::setup(b"other target").v().clone();
        assert!(!fx.sk.is_short_preimage(&other, &s));
        for half in 0..2 {
            let mut off = Preimage {
                s0: s.s0.clone(),
                s1: s.s1.clone(),
            };
            if half == 0 {
                off.s0[5] += 1;
            } else {
                off.s1[5] += 1;
            }
            assert!(off.norm_sq() <= S_BOUND, "only the coset equation fails");
            assert!(!fx.sk.is_short_preimage(&t, &off));
        }
        // a vector of the same coset (s plus the lattice vector (q, 0)) that is too long
        let mut long = Preimage {
            s0: s.s0.clone(),
            s1: s.s1.clone(),
        };
        long.s0[0] += i32::try_from(Q).unwrap();
        assert!(ntru_trapdoor::verify(&fx.vk.pk, t.poly(), &long, u64::MAX));
        assert!(!fx.sk.is_short_preimage(&t, &long));
    }

    /// A helper stores a count AHEAD of the true one before it issues (`to_bytes_reserving`):
    /// the stored key decodes with the advanced count, the in-memory count is unchanged, and the
    /// advance saturates at the cap.
    #[test]
    fn the_count_can_be_stored_ahead_of_issuance() {
        let mut fx = fixture(0x5151_000f);
        let (usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        for _ in 0..3 {
            VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
        }
        assert_eq!(
            &fx.sk.to_bytes_reserving(0).unwrap()[..],
            &to_bytes(&fx.sk).unwrap()[..]
        );
        let ahead = fx.sk.to_bytes_reserving(10).unwrap();
        assert_eq!(ahead.len(), VSISSigningKey::BYTES);
        assert_eq!(&ahead[SECRET_KEY_BYTES..], &13u64.to_le_bytes());
        assert_eq!(
            &ahead[..SECRET_KEY_BYTES],
            &to_bytes(&fx.sk).unwrap()[..SECRET_KEY_BYTES]
        );
        assert_eq!(fx.sk.issued(), 3);
        let restored: VSISSigningKey = from_bytes(&ahead).unwrap();
        assert_eq!(restored.issued(), 13);
        let pre = VSIS::blind_issue(&fx.pp, &restored, &c, &mut fx.rng).unwrap();
        assert!(VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).is_ok());
        assert_eq!(restored.issued(), 14);
        // saturation at the cap: the stored key decodes and refuses to issue
        fx.sk.issued.store(Q_MAX - 2, Ordering::SeqCst);
        let at_cap: VSISSigningKey = from_bytes(&fx.sk.to_bytes_reserving(5).unwrap()).unwrap();
        assert_eq!(at_cap.remaining(), 0);
        assert_eq!(
            VSIS::blind_issue(&fx.pp, &at_cap, &c, &mut fx.rng).unwrap_err(),
            Error::IssuanceCapReached
        );
        assert_eq!(
            fx.sk.to_bytes_reserving(u64::MAX).unwrap()[SECRET_KEY_BYTES..],
            Q_MAX.to_le_bytes()
        );
        // a wiped key has no encoding
        let mut wiped = from_bytes::<VSISSigningKey>(&ahead).unwrap();
        wiped.zeroize();
        assert_eq!(wiped.to_bytes_reserving(1).unwrap_err(), Error::InvalidKey);
    }

    // ----- the issuance cap -----------------------------------------------------------------

    #[test]
    fn the_issuance_cap_is_enforced() {
        let mut fx = fixture(0x5151_0010);
        let (usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        fx.sk.issued.store(Q_MAX - 1, Ordering::SeqCst);
        assert_eq!(fx.sk.remaining(), 1);
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
        assert!(VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).is_ok());
        assert_eq!((fx.sk.issued(), fx.sk.remaining()), (Q_MAX, 0));
        for _ in 0..3 {
            assert_eq!(
                VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap_err(),
                Error::IssuanceCapReached
            );
            let t = fx.pp.v().clone();
            assert!(matches!(
                fx.sk.sample_preimage(&t, &mut fx.rng),
                Err(Error::IssuanceCapReached)
            ));
        }
        assert_eq!(fx.sk.issued(), Q_MAX);
        // the count travels with the key, and a key at the cap stays at the cap
        let back: VSISSigningKey = from_bytes(&to_bytes(&fx.sk).unwrap()).unwrap();
        assert_eq!(back.issued(), Q_MAX);
        assert_eq!(
            VSIS::blind_issue(&fx.pp, &back, &c, &mut fx.rng).unwrap_err(),
            Error::IssuanceCapReached
        );
    }

    /// 16 threads share a key with 10 calls left: exactly 10 pre-credentials come out.
    #[test]
    fn concurrent_issuance_never_exceeds_the_cap() {
        let mut fx = fixture(0x5151_0011);
        let (usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        fx.sk.issued.store(Q_MAX - 10, Ordering::SeqCst);
        let (pp, sk, c) = (&fx.pp, &fx.sk, &c);
        let results: Vec<Result<VSISPreCredential, Error>> = thread::scope(|scope| {
            let handles: Vec<_> = (0..16u64)
                .map(|i| {
                    scope.spawn(move || {
                        let mut rng = StdRng::seed_from_u64(i);
                        (0..2)
                            .map(|_| VSIS::blind_issue(pp, sk, c, &mut rng))
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            handles
                .into_iter()
                .flat_map(|h| h.join().unwrap())
                .collect()
        });
        assert_eq!(results.iter().filter(|x| x.is_ok()).count(), 10);
        assert!(
            results
                .iter()
                .filter_map(|x| x.as_ref().err())
                .all(|e| *e == Error::IssuanceCapReached)
        );
        assert_eq!(sk.issued(), Q_MAX);
        for pre in results.iter().flatten() {
            assert!(VSIS::unblind(pp, &fx.vk, &usk, pre, &tape).is_ok());
        }
    }

    // ----- encodings ------------------------------------------------------------------------

    #[test]
    fn the_signing_key_round_trips_with_its_count() {
        let mut fx = fixture(0x5151_0012);
        let (usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        for _ in 0..3 {
            VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
        }
        let bytes = to_bytes(&fx.sk).unwrap();
        assert_eq!(bytes.len(), VSISSigningKey::BYTES);
        assert_eq!(bytes.len(), 5897);
        assert_eq!(bytes[0], 0xAA);
        assert_eq!(&bytes[SECRET_KEY_BYTES..], &3u64.to_le_bytes());
        let back: VSISSigningKey = from_bytes(&bytes).unwrap();
        assert!(back.check().is_ok());
        assert_eq!(back.issued(), 3);
        assert_eq!(back.verification_key().unwrap(), fx.vk);
        assert!(VSIS::key_pair_matches(&fx.vk, &back));
        let pre = VSIS::blind_issue(&fx.pp, &back, &c, &mut fx.rng).unwrap();
        assert!(VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).is_ok());
        assert_eq!((back.issued(), fx.sk.issued()), (4, 3));

        // a count at the cap decodes, one above does not
        let mut at_cap = bytes.clone();
        at_cap[SECRET_KEY_BYTES..].copy_from_slice(&Q_MAX.to_le_bytes());
        assert_eq!(
            from_bytes::<VSISSigningKey>(&at_cap).unwrap().remaining(),
            0
        );
        let mut above = bytes.clone();
        above[SECRET_KEY_BYTES..].copy_from_slice(&(Q_MAX + 1).to_le_bytes());
        assert!(from_bytes::<VSISSigningKey>(&above).is_err());
        // another header; F[0] changed (fG - gF ≠ q); truncated; trailing bytes
        let mut header = bytes.clone();
        header[0] = 0xAB;
        assert!(from_bytes::<VSISSigningKey>(&header).is_err());
        let mut trapdoor = bytes.clone();
        trapdoor[1 + 2 * (D * 10 / 8)] ^= 1;
        assert!(from_bytes::<VSISSigningKey>(&trapdoor).is_err());
        assert!(from_bytes::<VSISSigningKey>(&bytes[..bytes.len() - 1]).is_err());
        let mut long = bytes;
        long.push(0);
        assert_eq!(
            from_bytes::<VSISSigningKey>(&long).unwrap_err(),
            Error::TrailingBytes
        );
    }

    #[test]
    fn credentials_and_tapes_round_trip_strictly() {
        let mut fx = fixture(0x5151_0013);
        let (usk, cred) = issued(&mut fx);
        let bytes = to_bytes(&cred).unwrap();
        assert_eq!(bytes.len(), VSISCredential::BYTES);
        assert_eq!(bytes.len(), 6144);
        let back: VSISCredential = from_bytes(&bytes).unwrap();
        assert_eq!(back, cred);
        assert!(back.check().is_ok());
        assert!(VSIS::verify(&fx.pp, &fx.vk, &usk, &back));
        // the layout: s_0[0] in the low 20 bits, then x_1, then x_0
        let pre = cred.pre();
        let low =
            u32::from(bytes[0]) | u32::from(bytes[1]) << 8 | (u32::from(bytes[2]) & 0xf) << 16;
        assert_eq!(((low << 12) as i32) >> 12, pre.s0()[0]);
        assert_eq!(
            &bytes[2 * S_HALF_BYTES..VSISPreCredential::BYTES],
            &pre.x1().to_bytes()[..]
        );
        assert_eq!(
            &bytes[VSISPreCredential::BYTES..VSISPreCredential::BYTES + Ternary::BYTES],
            &cred.x0()[0].to_bytes()[..]
        );
        let pre_bytes = to_bytes(pre).unwrap();
        assert_eq!(pre_bytes.len(), VSISPreCredential::BYTES);
        assert_eq!(pre_bytes.len(), 5376);
        assert_eq!(&pre_bytes[..], &bytes[..VSISPreCredential::BYTES]);
        assert_eq!(&from_bytes::<VSISPreCredential>(&pre_bytes).unwrap(), pre);
        // the code -2^19, the ternary code 10, truncation, trailing bytes
        let mut bad = bytes.clone();
        bad[0] = 0;
        bad[1] = 0;
        bad[2] = (bad[2] & 0xf0) | 0x08;
        assert!(from_bytes::<VSISCredential>(&bad).is_err());
        let mut bad = bytes.clone();
        bad[2 * S_HALF_BYTES] = (bad[2 * S_HALF_BYTES] & 0xfc) | 0b10;
        assert!(from_bytes::<VSISCredential>(&bad).is_err());
        let mut bad = bytes.clone();
        bad[VSISPreCredential::BYTES] = (bad[VSISPreCredential::BYTES] & 0xfc) | 0b10;
        assert!(from_bytes::<VSISCredential>(&bad).is_err());
        assert!(from_bytes::<VSISCredential>(&bytes[..bytes.len() - 1]).is_err());
        let mut long = bytes;
        long.push(0);
        assert_eq!(
            from_bytes::<VSISCredential>(&long).unwrap_err(),
            Error::TrailingBytes
        );

        let mut rng = StdRng::seed_from_u64(1);
        let tape = VSISTape::sample(&mut rng);
        let state = to_bytes(&tape).unwrap();
        assert_eq!(state.len(), VSISTape::BYTES);
        assert_eq!(state.len(), 768);
        let back: VSISTape = from_bytes(&state).unwrap();
        assert!(back.ct_eq(&tape));
        assert!(back.check().is_ok());
    }

    #[test]
    fn pre_credentials_are_assembled_from_checked_parts() {
        let x1 = Ternary::zero();
        let ok = VSISPreCredential::from_parts(vec![1; D], vec![-1; D], x1.clone()).unwrap();
        assert_eq!(ok.norm_sq(), 2 * D as u64);
        assert_eq!(
            VSISPreCredential::from_parts(vec![0; D - 1], vec![0; D], x1.clone()).unwrap_err(),
            Error::LengthMismatch {
                expected: D,
                actual: D - 1
            }
        );
        assert_eq!(
            VSISPreCredential::from_parts(vec![0; D], vec![0; D + 1], x1.clone()).unwrap_err(),
            Error::LengthMismatch {
                expected: D,
                actual: D + 1
            }
        );
        let mut wiped = x1.clone();
        wiped.zeroize();
        assert_eq!(
            VSISPreCredential::from_parts(vec![0; D], vec![0; D], wiped).unwrap_err(),
            Error::LengthMismatch {
                expected: D,
                actual: 0
            }
        );
        let mut s0 = vec![0; D];
        s0[5] = 1 << 19;
        assert_eq!(
            VSISPreCredential::from_parts(s0, vec![0; D], x1.clone()).unwrap_err(),
            Error::InvalidCredential
        );
        let mut s1 = vec![0; D];
        s1[5] = -(1 << 19) + 1;
        assert!(VSISPreCredential::from_parts(vec![0; D], s1, x1).is_ok());
    }

    // ----- secrets and wiped values ----------------------------------------------------------

    #[test]
    fn secrets_are_redacted_and_wiped_and_wiped_values_are_refused() {
        fn assert_zeroize_on_drop<T: ZeroizeOnDrop>() {}
        assert_zeroize_on_drop::<VSISSigningKey>();
        assert_zeroize_on_drop::<VSISTape>();
        assert_zeroize_on_drop::<VSISPreCredential>();
        assert_zeroize_on_drop::<VSISCredential>();

        let mut fx = fixture(0x5151_0014);
        let (mut usk, tape) = message(&mut fx.rng);
        let c = VSIS::prepare_issue(&fx.pp, &usk, &tape).unwrap();
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap();
        let mut cred = VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &tape).unwrap();
        for (value, expected) in [
            (format!("{:?}", fx.sk), "VSISSigningKey(<redacted>)"),
            (format!("{tape:?}"), "VSISTape(<redacted>)"),
            (format!("{pre:?}"), "VSISPreCredential(<redacted>)"),
            (format!("{cred:?}"), "VSISCredential(<redacted>)"),
        ] {
            assert_eq!(value, expected);
        }

        // a wiped credential: no verification, no encoding
        let kept = cred.clone();
        cred.zeroize();
        assert!(cred.pre().s0().is_empty() && cred.x0()[0].coeffs().is_empty());
        assert!(!VSIS::verify(&fx.pp, &fx.vk, &usk, &cred));
        assert!(to_bytes(&cred).is_err());
        assert!(cred.check().is_err());
        assert_ne!(cred, kept);

        // a wiped C
        let mut wiped_c = c.clone();
        wiped_c.zeroize();
        assert_eq!(
            VSIS::blind_issue(&fx.pp, &fx.sk, &wiped_c, &mut fx.rng).unwrap_err(),
            Error::InvalidIssuanceEncoding
        );

        // a wiped tape: no request, no credential
        let mut wiped_tape = VSISTape::new(tape.x0().clone());
        wiped_tape.zeroize();
        assert_eq!(VSIS::prepare_issue(&fx.pp, &usk, &wiped_tape), None);
        assert!(to_bytes(&wiped_tape).is_err());
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &usk, &pre, &wiped_tape).unwrap_err(),
            Error::InvalidPreCredential
        );

        // a wiped key usk: no request, no verification
        usk.zeroize();
        assert_eq!(VSIS::prepare_issue(&fx.pp, &usk, &tape), None);
        assert!(!VSIS::verify(&fx.pp, &fx.vk, &usk, &kept));

        // a wiped signing key issues nothing and consumes nothing
        let before = fx.sk.issued();
        fx.sk.zeroize();
        assert_eq!(
            VSIS::blind_issue(&fx.pp, &fx.sk, &c, &mut fx.rng).unwrap_err(),
            Error::InvalidKey
        );
        assert!(matches!(
            fx.sk.sample_preimage(&c, &mut fx.rng),
            Err(Error::InvalidKey)
        ));
        assert_eq!(fx.sk.verification_key().unwrap_err(), Error::InvalidKey);
        assert!(!VSIS::key_pair_matches(&fx.vk, &fx.sk));
        assert!(to_bytes(&fx.sk).is_err());
        assert!(fx.sk.check().is_err());
        assert_eq!(fx.sk.issued(), before);
    }

    #[test]
    fn helpers() {
        assert!(is_one(&Rq::one()));
        assert!(!is_one(&Rq::zero()));
        let mut x = vec![0u32; D];
        x[0] = 1;
        x[1] = 1;
        assert!(!is_one(&Rq::from_coeffs(&x).unwrap()));
        let mut wiped = Rq::one();
        wiped.zeroize();
        assert!(!is_one(&wiped));
        let mut rng = StdRng::seed_from_u64(0x5151_0015);
        let a = VSISTape::sample(&mut rng);
        assert!(a.ct_eq(&a.duplicate()));
        let mut x0 = a.x0().clone();
        x0[ELL_R - 1] = changed(&x0[ELL_R - 1], 0);
        assert!(!a.ct_eq(&VSISTape::new(x0)));
        assert_eq!(
            with_norm_sq(S_BOUND)
                .iter()
                .map(|&x| i64::from(x).pow(2) as u64)
                .sum::<u64>(),
            S_BOUND
        );
    }
}
