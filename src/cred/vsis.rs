//! `Σ-vSIS`, the post-quantum credential base (building-blocks.tex, sec:inst-base-vsis,
//! bb:791-868): the proof-friendly lattice signatures of DKLW25 in the committed-message form of
//! BLNS23, on an NTRU trapdoor ($`A = [1 \mid h]`$, $`w = 2`$) from `ntru-trapdoor`. Feature
//! `lattice`.
//!
//! | paper (protocol box "Σ-vSIS credential base", bb:810-860) | here |
//! |---|---|
//! | `pp`: uniform $`v, b_u, b_\phi \in R_q`$, $`B_r \in R_q^{1 \times \ell_r}`$ from public randomness (bb:795) | [`VSISPublicParams`], [`CredentialBase::setup`] (expanded from the deployment label) |
//! | `KeyGen`: $`(A, td_A) \gets \mathsf{TrapGen}(R, q, w)`$ (bb:811-815) | [`CredentialBase::keygen`] |
//! | $`m_{\mathsf{hid}} = (usk, x_0)`$, $`m_{\mathsf{pub}} = \phi`$, $`m = (usk, \phi, x_0)`$ (bb:796-804) | [`VSISHiddenMessage`], [`BinaryPoly`], [`VSISMessage`] |
//! | $`\mathsf{Com}((usk, x_0), \phi; x_0) = b_u\,usk + B_r x_0`$ (bb:806) | [`CredentialBase::issuance_encoding`] |
//! | `Sign` (bb:817-825; step 5, bb:823, returns `⊥` if $`\|s\| > \beta_s`$) | [`CredentialBase::sign`] |
//! | `Verify` (bb:827-831) | [`CredentialBase::verify`], in product form |
//! | `ReRand → (⊥, cred)` (bb:833-836) | [`CredentialBase::rerand`], `ShownCredential = ()` |
//! | `BlindIssue(sk, C, φ)` (bb:838-844) | [`CredentialBase::blind_issue`] |
//! | `Unblind`, which verifies (bb:846-849) | [`CredentialBase::unblind`] |
//! | `Possess` (bb:851-859) | not here: the possession relation is a Jali statement of the construction ([`crate::pcs::lattice`]) |
//! | "The implemented preimage sampler" (bb:863-864): exact $`s \in \Lambda_t`$, fresh coins per call | `ntru_trapdoor::samp_pre` with a fresh seed per call |
//! | $`\mathcal V_{\mathsf{pp}}`$ = all canonically encoded $`h`$ (construction.tex, con:194) | [`CredentialBase::is_well_formed_key`] |
//! | the issuance cap $`Q_{\max} = 2^{48}`$ (lem:base-vsis, bb:868; construction.tex, "Issuance cap", con:220-221) | the counter of [`VSISSigningKey`] |
//!
//! # In formulas
//!
//! With $`x_1 \gets \mathcal X_1 = \{x \in R : \|x\|_\infty \le \beta_x\}`$ resampled until
//! $`v - x_1`$ is a unit (bb:808), `Sign` and `BlindIssue` sample a preimage of the target
//!
//! ```math
//! t = (v - x_1)^{-1} + C + b_\phi \phi, \qquad C = b_u\,usk + B_r x_0, \qquad s \gets \mathsf{SampPre}(td_A, t, \varsigma),
//! ```
//!
//! and `Verify` accepts $`(s, x_1)`$ on $`m = (usk, \phi, x_0)`$ iff $`m \in \mathcal M_\Sigma`$,
//! $`x_1 \in \mathcal X_1`$, $`\|s\|^2 \le \lfloor\beta_s^2\rfloor`$ and
//!
//! ```math
//! \bigl(s_0 + h s_1 - b_u\,usk - b_\phi\phi - B_r x_0\bigr)\cdot(v - x_1) = 1 \bmod q,
//! ```
//!
//! the product form of the box's equation $`As = (v - x_1)^{-1} + \dots`$ together with "$`v - x_1`$
//! is invertible" (bb:829-830): a product equals $`1`$ iff both factors are units and each is the
//! inverse of the other, so the two forms accept exactly the same inputs, and the product form
//! needs no inversion.
//!
//! `Sign` is literally `Com` followed by the code of `BlindIssue` (the same function samples
//! $`x_1`$, builds $`t`$ and calls `SampPre`), then the norm check of step 5. This is the
//! issuance-indistinguishability argument of lem:base-vsis in code: for a fixed message, `Sign`
//! and `Unblind ∘ BlindIssue` run the same instructions on the same target and consume the RNG
//! in the same order (a unit test checks that they return the same credential for the same RNG
//! seed).
//!
//! # Encodings
//!
//! | object | bytes | size |
//! |---|---|---|
//! | [`VSISPublicParams`] | $`v \| b_u \| b_\phi \| B_{r,0} \| B_{r,1}`$, each an [`Rq`] | 12,800 |
//! | [`VSISSigningKey`] | `ntru-trapdoor`'s secret-key encoding (5889) $`\|`$ `LE64(issued)` | 5897 |
//! | [`VSISVerificationKey`] | $`h`$, an [`Rq`] | 2560 |
//! | [`VSISIssuanceState`] | $`x_{0,0} \| x_{0,1}`$, each a [`Ternary`] | 512 |
//! | [`VSISCredential`] ($`= \widehat{cred}`$) | $`s_0 \| s_1`$ at 20 bits per coefficient, two's complement, little-endian bit packing; then $`x_1`$ | 5376 |
//!
//! Every decoder checks canonicity whatever `Validate` flag it gets (the module docs of
//! [`crate::lattice::ring`]). Decoding the signing key validates the trapdoor
//! ($`fG - gF = q`$, $`f`$ invertible) and rebuilds its expanded form. Decoding says nothing
//! about the validity of a credential: that is [`CredentialBase::verify`].
//!
//! # The implemented preimage sampler
//!
//! `SampPre` is `ntru-trapdoor`'s Falcon-style fast-Fourier sampler (`samp_pre`, coin label
//! `ntru-trapdoor/v1/samp-pre`). It computes the lattice point $`v = zB`$ in floating point and
//! rounds it, $`s = (t, 0) - \mathrm{rint}(v)`$; the rounding is exact with a MEASURED margin
//! (its error is about $`2^{-26.9}`$ at this parameter set, `ntru-trapdoor`'s README), not by
//! proof. The paper requires more: "an implementation must compute this $`s`$ exactly, in integer
//! arithmetic, so that $`s \in \Lambda_t`$" (bb:864). So before a preimage leaves the signing key,
//! the key checks $`s_0 + h s_1 = t \bmod q`$ in exact integer arithmetic (one product with the
//! prepared $`h`$, about 20 µs) together with $`\|s\|^2 \le \lfloor\beta_s^2\rfloor`$, and refuses
//! a sample that fails ([`Error::LatticeBackend`]; never observed). `samp_pre` resamples
//! internally while $`\|s\|^2 > \lfloor\beta_s^2\rfloor`$ (at most 27 attempts), so `Sign` step 5
//! never fires, and the cap counts CALLS of `SampPre`, not attempts.
//!
//! Each call receives a fresh 32-byte seed from the caller's RNG ([`crate::lattice`],
//! "Randomness"), never reused (bb:864: "must use fresh coins in every call, never reusing
//! them"): the helper's RNG must be a CSPRNG seeded by the operating system, never a seeded or
//! replayed generator, since `TrapGen` (the trapdoor itself) and every `SampPre` call draw their
//! coins from it. The key is expanded once (the ffLDL tree, [`VSISSigningKey`]), so a call costs
//! about 180 µs (161 µs of `samp_pre`, `ntru-trapdoor`'s README, and the exact check). Its
//! distribution is the one `ntru-trapdoor` documents: the coset Gaussian of width
//! $`\sigma = \varsigma/\sqrt{2\pi} = 2656.42`$ up to a measured (not proved) floating-point
//! Rényi budget; lem:base-vsis is stated for exactly this situation (it requires only that the
//! output lie in $`\Lambda_t`$ and be short, and assumes `IntGenISIS_f` in the falsifiable form
//! whose challenger runs the implemented sampler).
//!
//! # The issuance cap
//!
//! lem:base-vsis (bb:868) assumes that a key answers at most $`Q_{\max}`$ calls of `Sign` and
//! `BlindIssue`; construction.tex sets $`Q_{\max} = 2^{48}`$ and makes the helper count them and
//! rotate its key (con:221). [`VSISSigningKey`] counts them: each call reserves one unit of the
//! counter ATOMICALLY before it calls `SampPre` (a compare-and-swap that increments only below
//! $`Q_{\max}`$), and fails with [`Error::IssuanceCapReached`] once $`Q_{\max}`$ units are used, so
//! concurrent issuance through a shared `&VSISSigningKey` never exceeds the cap. A reservation is
//! consumed even when `SampPre` then fails (conservative). The count is part of the key's
//! encoding: a helper that stores its key stores the count, and a helper that restores an OLD
//! copy resets it (the operator's responsibility, `docs/operating-a-helper.md`).
//! [`VSISSigningKey::to_bytes_reserving`] stores a count AHEAD of the true one, for a helper that
//! persists before it issues. The counter lives in ONE value: two values decoded from the same
//! bytes count independently, so a deployment runs one live instance per stored key (threads
//! share it by reference). The rotation itself (a new `HKeyGen`, a new `hvk`) belongs to the
//! helper.
//!
//! # Implementation notes
//!
//! Not in the paper, and each one only refuses inputs that are not what their type stands for:
//!
//! * Every value of [`Ternary`] and [`BinaryPoly`] lies in its message space by construction,
//!   except a WIPED [`Ternary`] (`zeroize` empties it). The algorithms therefore check only the
//!   lengths: `Sign` and the encoding maps return [`Error::InvalidMessage`] and `Verify` returns
//!   `false` for a wiped component; `BlindIssue` returns [`Error::InvalidIssuanceEncoding`] for a
//!   wiped $`C`$; a wiped signing key signs nothing ([`Error::InvalidKey`]). None of the
//!   algorithms panics; only the constructor [`VSISVerificationKey::from_h`] does, on a wiped
//!   $`h`$.
//! * `Com` and `Unblind` receive $`x_0`$ twice, inside $`m_{\mathsf{hid}}`$ (resp. $`m`$) and as the
//!   issuance state $`r = x_0`$. As for `Σ-BBS`, they return [`Error::InvalidMessage`] when the
//!   two differ (compared in constant time); the box uses one $`x_0`$.
//! * `ReRand` returns [`Error::InvalidCredential`] for a wiped credential, which is no credential
//!   and no witness.
//! * The resampling loops are bounded: `KeyGen` tries `TrapGen` with 4 fresh seeds (each fails
//!   only after 4096 rejected candidates, while about 1 in 20 is accepted) and panics after that;
//!   $`x_1`$ is drawn at most 64 times, after which [`Error::LatticeBackend`] is returned. Over the
//!   uniform $`v`$ of `Setup`, $`v - x_1`$ is a non-unit with probability about $`2/q^{512}`$ for
//!   each $`x_1`$ ($`X^{1024} + 1`$ has two irreducible factors of degree 512 modulo $`q`$); for the
//!   fixed $`v`$, bb:795 argues that at most one short $`x_1`$ can agree with $`v`$ modulo either
//!   factor.
//!
//! # Side channels
//!
//! Performance comes first. The ring arithmetic of `ntru-trapdoor` uses masks (the inverse reveals
//! only whether an element is a unit), message comparisons and credential equality are constant
//! time, and the secret intermediates of `Com`, `Sign`, `BlindIssue` and `Verify` are wiped. The
//! rejection loops of [`Ternary::sample`] and of `SampPre`, `SampPre`'s floating-point arithmetic
//! and `TrapGen` run in variable time (the module docs of [`crate::lattice`]).
//!
//! # Example
//!
//! Encoded issuance (Def. "Credential base", correctness), then a signature on the same message:
//!
//! ```
//! use predicate_credential_system::{
//!     cred::{
//!         CredentialBase, VSIS,
//!         vsis::{VSISHiddenMessage, VSISIssuanceState},
//!     },
//!     lattice::{BinaryPoly, Ternary},
//! };
//! use rand::{SeedableRng, rngs::StdRng};
//!
//! // seeded so that the example is reproducible; a signer uses `rand::rngs::OsRng` (the
//! // trapdoor is a function of the RNG's output)
//! let mut rng = StdRng::seed_from_u64(1);
//! let pp = VSIS::setup(b"example deployment")?;
//! let (vk, sk) = VSIS::keygen(&pp, &mut rng); // TrapGen, about 6 ms
//! let usk = Ternary::sample(&mut rng);
//! let x0 = [Ternary::sample(&mut rng), Ternary::sample(&mut rng)];
//! let phi = BinaryPoly::from_bytes([0x5a; BinaryPoly::BYTES]);
//! let m_hid = VSISHiddenMessage::new(usk, x0.clone());
//! let r = VSISIssuanceState::new(x0);
//!
//! // user: C = Com(m_hid, φ; x_0)    helper: BlindIssue(sk, C, φ)    user: Unblind (it verifies)
//! let c = VSIS::issuance_encoding(&pp, &vk, &m_hid, &phi, &r)?;
//! let pre = VSIS::blind_issue(&pp, &sk, &c, &phi, &mut rng)?;
//! let m = VSIS::encode_message(&pp, &m_hid, &phi)?;
//! let cred = VSIS::unblind(&pp, &vk, &m, &pre, &r)?;
//! assert!(VSIS::verify(&pp, &vk, &m, &cred));
//!
//! let signed = VSIS::sign(&pp, &sk, &m, &mut rng)?;
//! assert!(VSIS::verify(&pp, &vk, &m, &signed));
//! assert_eq!(sk.issued(), 2); // two SampPre calls under the cap
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

use super::CredentialBase;
use crate::{
    error::Error,
    lattice::{
        BinaryPoly, D, ELL_R, Q_MAX, Rq, S_BOUND, Ternary, fresh_seed, ntru_error,
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
/// Draws of $`x_1`$ before `Sign` / `BlindIssue` give up.
const X1_ATTEMPTS: usize = 64;
/// The element names of `pp_Σ` in the oracle `/LATTICE-PP` (`lattice::xof::pp_element`), in the
/// order of the encoding.
const PP_NAMES: [&[u8]; 5] = [b"v", b"b_u", b"b_phi", b"B_r[0]", b"B_r[1]"];

// The names above and the fixed-size code below are for ℓ_r = 2, as are the parameter sets.
const _: () = assert!(ELL_R == 2 && SECRET_KEY_BYTES == 5889 && S_HALF_BYTES == 2560);

/// Whether `x` is an element of $`\{-1, 0, 1\}^d`$. Every [`Ternary`] is, unless it was wiped.
fn is_short(x: &Ternary) -> bool {
    x.coeffs().len() == D
}

/// `a == b` for two vectors $`x_0`$, in constant time.
fn same_x0(a: &[Ternary; ELL_R], b: &[Ternary; ELL_R]) -> bool {
    a.iter()
        .zip(b)
        .fold(true, |equal, (x, y)| equal & x.ct_eq(y))
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

/// The credential base `Σ-vSIS` (marker type; all algorithms are the associated functions of
/// [`CredentialBase`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct VSIS;

// ---------------------------------------------------------------------------------------------
// Public parameters
// ---------------------------------------------------------------------------------------------

/// The public parameters $`pp_\Sigma = (v, b_u, b_\phi, B_r)`$, uniform in $`R_q`$ and expanded
/// from the deployment label (`/LATTICE-PP`, element names `v`, `b_u`, `b_phi`, `B_r[0]`,
/// `B_r[1]`): "from public randomness, so that nobody, the helper included, knows a short
/// relation among them" (bb:795). The norm bounds and the width $`\varsigma`$ of the box are the
/// constants of [`crate::lattice`] and of `ntru-trapdoor`'s PCS set.
///
/// The value also keeps $`b_u`$, $`b_\phi`$ and $`B_r`$ prepared for products (NTT form, built
/// once by `Setup` and by decoding), so that `Com` costs three and `Verify` five products with a
/// prepared operand (about 19 µs each instead of 28 µs).
///
/// Encoding: $`v \| b_u \| b_\phi \| B_{r,0} \| B_{r,1}`$, five [`Rq`] ([`Self::BYTES`] bytes).
/// Equality compares these five elements.
#[derive(Clone)]
pub struct VSISPublicParams {
    v: Rq,
    b_u: Rq,
    b_phi: Rq,
    b_r: [Rq; ELL_R],
    /// $`b_u`$, $`b_\phi`$, $`B_r`$ prepared for products.
    prepared: Prepared,
}

/// The public columns of `pp_Σ` in the NTT form of `ntru-trapdoor`'s products.
#[derive(Clone)]
struct Prepared {
    b_u: PreparedRqPoly,
    b_phi: PreparedRqPoly,
    b_r: [PreparedRqPoly; ELL_R],
}

impl VSISPublicParams {
    /// Bytes of the encoding: five elements of $`R_q`$.
    pub const BYTES: usize = 5 * Rq::BYTES;

    /// The parameters with these elements, and their prepared forms.
    fn from_elements(v: Rq, b_u: Rq, b_phi: Rq, b_r: [Rq; ELL_R]) -> Self {
        let prepared = Prepared {
            b_u: b_u.poly().prepare(),
            b_phi: b_phi.poly().prepare(),
            b_r: core::array::from_fn(|k| b_r[k].poly().prepare()),
        };
        Self {
            v,
            b_u,
            b_phi,
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

    /// $`b_\phi`$, the column of the public message $`\phi`$.
    #[must_use]
    pub fn b_phi(&self) -> &Rq {
        &self.b_phi
    }

    /// $`B_r = (B_{r,0}, B_{r,1})`$, the commitment columns of $`x_0`$.
    #[must_use]
    pub fn b_r(&self) -> &[Rq; ELL_R] {
        &self.b_r
    }

    /// The five elements in the order of the encoding.
    fn elements(&self) -> [&Rq; 5] {
        [&self.v, &self.b_u, &self.b_phi, &self.b_r[0], &self.b_r[1]]
    }

    /// $`C = \mathsf{Com}((usk, x_0), \phi; x_0) = b_u\,usk + B_r x_0 \bmod q`$ (bb:806), with the
    /// prepared columns (three products). $`C`$ is public; the products of its terms are secret
    /// and wiped.
    ///
    /// # Errors
    /// [`Error::InvalidMessage`] for a wiped `usk` or $`x_0`$ (module docs, "Implementation
    /// notes").
    pub(crate) fn commitment(&self, usk: &Ternary, x0: &[Ternary; ELL_R]) -> Result<Rq, Error> {
        if !is_short(usk) || !x0.iter().all(is_short) {
            return Err(Error::InvalidMessage);
        }
        let mut c = Zeroizing::new(times(&self.prepared.b_u, &Zeroizing::new(usk.to_rq())));
        for (b, x) in self.prepared.b_r.iter().zip(x0) {
            let term = Zeroizing::new(times(b, &Zeroizing::new(x.to_rq())));
            c = Zeroizing::new(c.add(&term));
        }
        Ok(core::mem::replace(&mut *c, Rq::zero()))
    }

    /// $`b_\phi\phi \bmod q`$, with the prepared $`b_\phi`$. Public.
    pub(crate) fn phi_term(&self, phi: &BinaryPoly) -> Rq {
        times(&self.prepared.b_phi, &phi.to_rq())
    }

    /// `Sign` step 2 and `BlindIssue` step 1 (bb:820, bb:840): $`x_1 \gets \mathcal X_1`$ uniform
    /// ([`Ternary::sample`], $`\beta_x = 1`$), resampled until $`v - x_1`$ is a unit; returns
    /// $`x_1`$ and $`(v - x_1)^{-1}`$.
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

    /// The target $`t = (v - x_1)^{-1} + C + b_\phi\phi \bmod q`$ of `Sign` step 3 (with
    /// $`C = b_u\,usk + B_r x_0`$, bb:821) and of `BlindIssue` step 2 (bb:841).
    fn target(&self, y: &Rq, c: &Rq, phi: &BinaryPoly) -> Zeroizing<Rq> {
        let partial = Zeroizing::new(y.add(c));
        Zeroizing::new(partial.add(&self.phi_term(phi)))
    }

    /// The first factor of `Verify`'s product form,
    /// $`s_0 + h s_1 - b_u\,usk - b_\phi\phi - B_r x_0`$: five products with prepared operands
    /// ($`h`$, $`b_u`$, $`B_{r,0}`$, $`B_{r,1}`$, $`b_\phi`$). `None` for inputs of the wrong
    /// length. Secret: wiped.
    fn residual(
        &self,
        vk: &VSISVerificationKey,
        m: &VSISMessage,
        s: &Preimage,
    ) -> Option<Zeroizing<Rq>> {
        let s0 = Zeroizing::new(RqPoly::from_i32(&NTRU, &s.s0).ok()?);
        let s1 = Zeroizing::new(RqPoly::from_i32(&NTRU, &s.s1).ok()?);
        let h_s1 = Zeroizing::new(vk.pk.h_prepared().mul(&s1));
        let a_s = Zeroizing::new(Rq::from_poly(s0.add(&h_s1)));
        let c = Zeroizing::new(self.commitment(&m.usk, &m.x0).ok()?);
        let partial = Zeroizing::new(a_s.sub(&c));
        Some(Zeroizing::new(partial.sub(&self.phi_term(&m.phi))))
    }
}

impl PartialEq for VSISPublicParams {
    fn eq(&self, other: &Self) -> bool {
        self.v == other.v
            && self.b_u == other.b_u
            && self.b_phi == other.b_phi
            && self.b_r == other.b_r
    }
}

impl Eq for VSISPublicParams {}

impl fmt::Debug for VSISPublicParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISPublicParams(v, b_u, b_phi, B_r)")
    }
}

impl CanonicalSerialize for VSISPublicParams {
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

impl Valid for VSISPublicParams {
    fn check(&self) -> Result<(), SerializationError> {
        self.elements()
            .iter()
            .try_for_each(|element| element.check())
    }
}

impl CanonicalDeserialize for VSISPublicParams {
    /// Five canonical elements of $`R_q`$, whatever `validate` says; prepares the columns.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut element = || Rq::deserialize_with_mode(&mut reader, compress, validate);
        let v = element()?;
        let b_u = element()?;
        let b_phi = element()?;
        let b_r = [element()?, element()?];
        Ok(Self::from_elements(v, b_u, b_phi, b_r))
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
/// ($`fG - gF = q`$, the coefficient widths, $`f`$ invertible; about 77 µs), rebuilds the expanded
/// key (about 52 µs) and $`h = g f^{-1}`$ (about 0.1 ms), and refuses a count above $`Q_{\max}`$.
/// The count read is the one at the time of encoding: persist the key after issuing, or BEFORE
/// issuing with [`Self::to_bytes_reserving`] (module docs, "The issuance cap").
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

    /// The number of `SampPre` calls (`Sign` and `BlindIssue`) this key has answered, i.e. the
    /// number of units of the cap reserved so far.
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
    /// decoded). For a helper that checks a stored key pair (`HelperSecretKey::new` cannot).
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
    /// its predecessor `fetch_update` is deprecated from 1.99 on). Called by `Sign` and
    /// `BlindIssue` BEFORE they sample.
    ///
    /// # Errors
    /// [`Error::IssuanceCapReached`] once $`Q_{\max}`$ calls were reserved.
    pub(crate) fn reserve_preimage(&self) -> Result<(), Error> {
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
    /// with a fresh 32-byte seed from `rng` (`Sign` step 4, `BlindIssue` step 3; bb:864, "fresh
    /// coins in every call"), and releases the sample only if it IS a short preimage of $`t`$,
    /// checked exactly ([`Self::is_short_preimage`]; bb:864, "in integer arithmetic, so that
    /// $`s \in \Lambda_t`$").
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped key; [`Error::IssuanceCapReached`] at the cap;
    /// [`Error::LatticeBackend`] if `samp_pre` fails (a target outside $`R_q`$, or all its
    /// attempts rejected, which has probability below $`2^{-5000}`$ at the PCS set) or returns a
    /// vector that is not a short preimage of $`t`$ (a floating-point rounding failure; never
    /// observed, the measured margin is about $`2^{26}`$).
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
    /// prepared $`h`$: four NTTs, about 20 µs), and $`\|s\|^2 \le \lfloor\beta_s^2\rfloor`$
    /// (`u128` accumulation): `ntru_trapdoor::verify` under this key's $`h`$.
    fn is_short_preimage(&self, t: &Rq, s: &Preimage) -> bool {
        ntru_trapdoor::verify(&self.pk, t.poly(), s, S_BOUND)
    }

    /// TEST HOOK: `SampPre` on an arbitrary target $`t`$ with a fresh seed, counted toward the
    /// cap, for false-witness tests of the relations (an $`x_1`$ with a coefficient 2 needs a real
    /// preimage of its own target). Never part of a protocol: the helper samples only at the
    /// targets of `Sign` and `BlindIssue`.
    ///
    /// # Errors
    /// As `Sign` step 4: [`Error::InvalidKey`], [`Error::IssuanceCapReached`],
    /// [`Error::LatticeBackend`].
    #[cfg(any(test, feature = "test-utils"))]
    #[cfg_attr(not(test), allow(dead_code))] // the construction's tests use it
    pub(crate) fn sample_preimage<R: RngCore + CryptoRng + ?Sized>(
        &self,
        t: &Rq,
        rng: &mut R,
    ) -> Result<Preimage, Error> {
        self.preimage(t, rng)
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
/// $`h \in R_q`$ is a key: $`\mathcal V_{\mathsf{pp}}`$ is relaxed to all of them (con:194: a public
/// membership test for the range of `KeyGen` would solve decisional NTRU), so
/// [`CredentialBase::is_well_formed_key`] has nothing to refuse. Keeps $`h`$ prepared for the
/// product of `Verify` (computed on first use).
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
// Messages and the issuance state
// ---------------------------------------------------------------------------------------------

/// The hidden message $`m_{\mathsf{hid}} = (usk, x_0) \in \mathcal M_{\mathsf{hid}}`$ (bb:798).
/// Secret: wiped on drop, redacted in `Debug`.
pub struct VSISHiddenMessage {
    usk: Ternary,
    x0: [Ternary; ELL_R],
}

impl VSISHiddenMessage {
    /// $`(usk, x_0)`$. Every pair of [`Ternary`] is in $`\mathcal M_{\mathsf{hid}}`$
    /// ($`\beta_u = \beta_r = 1`$).
    #[must_use]
    pub fn new(usk: Ternary, x0: [Ternary; ELL_R]) -> Self {
        Self { usk, x0 }
    }

    /// `usk`.
    #[must_use]
    pub fn usk(&self) -> &Ternary {
        &self.usk
    }

    /// $`x_0`$.
    #[must_use]
    pub fn x0(&self) -> &[Ternary; ELL_R] {
        &self.x0
    }

    /// $`m_{\mathsf{hid}} \in \mathcal M_{\mathsf{hid}}`$: no component was wiped.
    fn is_in_message_space(&self) -> bool {
        is_short(&self.usk) && self.x0.iter().all(is_short)
    }
}

impl Zeroize for VSISHiddenMessage {
    fn zeroize(&mut self) {
        self.usk.zeroize();
        self.x0.zeroize();
    }
}

/// Its components wipe themselves on drop.
impl ZeroizeOnDrop for VSISHiddenMessage {}

impl fmt::Debug for VSISHiddenMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISHiddenMessage(<redacted>)")
    }
}

/// The signed message $`m = \mathsf{Enc}_\Sigma((usk, x_0), \phi) = (usk, \phi, x_0) \in
/// \mathcal M_\Sigma`$ (bb:802-804). Secret (it contains `usk`): wiped on drop, redacted in
/// `Debug`. Made by [`CredentialBase::encode_message`].
pub struct VSISMessage {
    usk: Ternary,
    phi: BinaryPoly,
    x0: [Ternary; ELL_R],
}

impl VSISMessage {
    /// `usk`.
    #[must_use]
    pub fn usk(&self) -> &Ternary {
        &self.usk
    }

    /// $`\phi`$.
    #[must_use]
    pub fn phi(&self) -> &BinaryPoly {
        &self.phi
    }

    /// $`x_0`$.
    #[must_use]
    pub fn x0(&self) -> &[Ternary; ELL_R] {
        &self.x0
    }

    /// $`m \in \mathcal M_\Sigma`$: no component was wiped ($`\phi`$ is binary by type).
    fn is_in_message_space(&self) -> bool {
        is_short(&self.usk) && self.x0.iter().all(is_short)
    }
}

impl Zeroize for VSISMessage {
    fn zeroize(&mut self) {
        self.usk.zeroize();
        self.x0.zeroize();
    }
}

/// Its secret components wipe themselves on drop ($`\phi`$ is public).
impl ZeroizeOnDrop for VSISMessage {}

impl fmt::Debug for VSISMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISMessage(<redacted>)")
    }
}

/// The local issuance state $`r = x_0`$ ("the issuance randomizer $`x_0`$ is simultaneously the
/// local issuance state and a certified hidden component", stored at the PCS layer as
/// $`m_{\mathsf{aux}} = x_0`$; bb:808). Secret: wiped on drop, redacted in `Debug`.
///
/// Encoding: $`x_{0,0} \| x_{0,1}`$, two [`Ternary`] ([`Self::BYTES`] bytes).
pub struct VSISIssuanceState([Ternary; ELL_R]);

impl VSISIssuanceState {
    /// Bytes of the encoding.
    pub const BYTES: usize = ELL_R * Ternary::BYTES;

    /// $`r = x_0`$.
    #[must_use]
    pub fn new(x0: [Ternary; ELL_R]) -> Self {
        Self(x0)
    }

    /// $`x_0`$.
    #[must_use]
    pub fn x0(&self) -> &[Ternary; ELL_R] {
        &self.0
    }
}

impl Zeroize for VSISIssuanceState {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

/// Its components wipe themselves on drop.
impl ZeroizeOnDrop for VSISIssuanceState {}

impl fmt::Debug for VSISIssuanceState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VSISIssuanceState(<redacted>)")
    }
}

impl CanonicalSerialize for VSISIssuanceState {
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

impl Valid for VSISIssuanceState {
    fn check(&self) -> Result<(), SerializationError> {
        self.0.iter().try_for_each(Valid::check)
    }
}

impl CanonicalDeserialize for VSISIssuanceState {
    /// Two canonical [`Ternary`], whatever `validate` says.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let first = Ternary::deserialize_with_mode(&mut reader, compress, validate)?;
        let second = Ternary::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(Self([first, second]))
    }
}

// ---------------------------------------------------------------------------------------------
// Credentials
// ---------------------------------------------------------------------------------------------

/// A credential (and a pre-credential) $`(s, x_1)`$: the preimage $`s = (s_0, s_1)`$ with
/// $`s_0 + h s_1 = t`$ and the signing randomness $`x_1`$. It is the WITNESS of the possession
/// relation (the show is the zero-knowledge argument alone, `cred* = ⊥`, bb:835), so it is secret
/// to its holder: wiped on drop, redacted in `Debug`, compared in constant time. (The helper saw
/// it at issuance; zero knowledge is what keeps shows unlinkable.)
///
/// Encoding: $`s_0 \| s_1`$ at 20 bits per coefficient in two's complement
/// ([`crate::lattice::ring`], `pack_signed`; $`|s_i| < 2^{19}`$, while every verifying credential
/// has $`|s_i| \le \lfloor\beta_s\rfloor = 301{,}336`$), then $`x_1`$ ([`Ternary`]): [`Self::BYTES`]
/// bytes.
#[derive(Clone)]
pub struct VSISCredential {
    s: Preimage,
    x1: Ternary,
}

/// A pre-credential $`\widehat{cred} = (s, x_1)`$ has the format of a credential.
pub type VSISPreCredential = VSISCredential;

impl VSISCredential {
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
}

impl PartialEq for VSISCredential {
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

impl Eq for VSISCredential {}

impl Zeroize for VSISCredential {
    fn zeroize(&mut self) {
        self.s.zeroize();
        self.x1.zeroize();
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
    /// Fails for a wiped credential and for a coefficient $`|s_i| \ge 2^{19}`$.
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

impl Valid for VSISCredential {
    fn check(&self) -> Result<(), SerializationError> {
        let encodable = self
            .s
            .s0
            .iter()
            .chain(&self.s.s1)
            .all(|&c| c.unsigned_abs() <= S_MAX_ABS);
        if self.is_well_formed() && encodable {
            self.x1.check()
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl CanonicalDeserialize for VSISCredential {
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

// ---------------------------------------------------------------------------------------------
// The base
// ---------------------------------------------------------------------------------------------

/// Steps 2-4 of `Sign` and steps 1-3 of `BlindIssue` (bb:820-822, bb:840-842), ONE code path for
/// both: $`x_1`$, the target $`t = (v - x_1)^{-1} + C + b_\phi\phi`$, then `SampPre` under the cap
/// with a fresh seed.
fn issue_preimage<R: RngCore + CryptoRng + ?Sized>(
    pp: &VSISPublicParams,
    sk: &VSISSigningKey,
    c: &Rq,
    phi: &BinaryPoly,
    rng: &mut R,
) -> Result<VSISCredential, Error> {
    let (x1, y) = pp.sample_x1(rng)?;
    let t = pp.target(&y, c, phi);
    let s = sk.preimage(&t, rng)?;
    Ok(VSISCredential { s, x1 })
}

impl CredentialBase for VSIS {
    /// $`(v, b_u, b_\phi, B_r)`$.
    type PublicParams = VSISPublicParams;
    /// $`td_A`$ with the issuance counter.
    type SigningKey = VSISSigningKey;
    /// $`h`$.
    type VerificationKey = VSISVerificationKey;
    /// $`(usk, x_0)`$.
    type HiddenMessage = VSISHiddenMessage;
    /// $`\phi`$, binary.
    type PublicMessage = BinaryPoly;
    /// $`(usk, \phi, x_0)`$.
    type Message = VSISMessage;
    /// $`r = x_0`$.
    type IssuanceState = VSISIssuanceState;
    /// $`C = b_u\,usk + B_r x_0`$.
    type IssuanceEncoding = Rq;
    /// $`(s, x_1)`$.
    type Credential = VSISCredential;
    /// $`(s, x_1)`$.
    type PreCredential = VSISPreCredential;
    /// `cred* = ⊥`: there is no public credential encoding.
    type ShownCredential = ();
    /// $`\omega = cred`$.
    type ShowState = VSISCredential;

    /// `pp_Σ` for the deployment label `domain` (bb:795): the five elements of
    /// [`VSISPublicParams`], each the uniform element of $`R_q`$ that the oracle `/LATTICE-PP`
    /// outputs for the items `("deployment", domain)` and `("element", name)`
    /// (`lattice::xof::pp_element`, rejection sampling of 20-bit chunks below $`q`$). Public
    /// randomness: SHAKE128 of the label, so nobody knows a trapdoor or a short relation for
    /// them (in the random-oracle model). Infallible; about 70 µs (with the preparation of the
    /// columns).
    fn setup(domain: &[u8]) -> Result<Self::PublicParams, Error> {
        let [v, b_u, b_phi, b_r0, b_r1] = PP_NAMES.map(|name| pp_element(domain, name));
        Ok(VSISPublicParams::from_elements(v, b_u, b_phi, [b_r0, b_r1]))
    }

    /// `KeyGen` (bb:811-815): $`(A = [1 \mid h], td_A) \gets \mathsf{TrapGen}`$ from a fresh
    /// 32-byte seed (`ntru_trapdoor::trapgen` at the PCS set, about 6 ms), and the expanded key;
    /// the counter starts at 0. `pp` does not enter (the trapdoor is independent of `pp_Σ`).
    /// The trapdoor is a function of the seed: `rng` must be a CSPRNG seeded by the operating
    /// system (module docs, "The implemented preimage sampler").
    ///
    /// # Panics
    /// Only if `TrapGen` fails for 4 fresh seeds in a row (a seed fails when 4096 candidates are
    /// rejected, which does not happen in practice: about 1 candidate in 20 is accepted).
    fn keygen<R: RngCore + CryptoRng + ?Sized>(
        _pp: &Self::PublicParams,
        rng: &mut R,
    ) -> (Self::VerificationKey, Self::SigningKey) {
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

    /// $`h \in \mathcal V_{\mathsf{pp}}`$ iff it is a canonically encoded element of $`R_q`$
    /// (con:194), which every value of [`VSISVerificationKey`] is.
    fn is_well_formed_key(_pp: &Self::PublicParams, vk: &Self::VerificationKey) -> bool {
        vk.h.coeffs().len() == D
    }

    /// `Sign` (bb:817-825):
    /// 1. $`m \in \mathcal M_\Sigma`$ (by type; a wiped component is refused);
    /// 2. $`x_1 \gets \mathcal X_1`$ until $`v - x_1`$ is a unit;
    /// 3. $`t = (v - x_1)^{-1} + b_u\,usk + b_\phi\phi + B_r x_0`$, computed as
    ///    $`(v - x_1)^{-1} + C + b_\phi\phi`$ with $`C = \mathsf{Com}`$;
    /// 4. $`s \gets \mathsf{SampPre}(td_A, t, \varsigma)`$ with a fresh seed, under the cap;
    /// 5. `⊥` if $`\|s\|^2 > \lfloor\beta_s^2\rfloor`$ (bb:823; never fires, because `samp_pre`
    ///    itself resamples above the bound);
    /// 6. $`(s, x_1)`$.
    ///
    /// Steps 2-4 are the code of `BlindIssue` (module docs). About 0.3 ms.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped key; [`Error::InvalidMessage`] for a wiped message
    /// (step 1); [`Error::IssuanceCapReached`] at the cap; [`Error::InvalidCredential`] at step
    /// 5; [`Error::LatticeBackend`] if a bounded loop gives up (module docs).
    fn sign<R: RngCore + CryptoRng + ?Sized>(
        pp: &Self::PublicParams,
        sk: &Self::SigningKey,
        m: &Self::Message,
        rng: &mut R,
    ) -> Result<Self::Credential, Error> {
        sk.ensure_usable()?;
        if !m.is_in_message_space() {
            return Err(Error::InvalidMessage);
        }
        let c = pp.commitment(&m.usk, &m.x0)?;
        let cred = issue_preimage(pp, sk, &c, &m.phi, rng)?;
        if cred.norm_sq() > S_BOUND {
            return Err(Error::InvalidCredential);
        }
        Ok(cred)
    }

    /// `Verify` (bb:827-831), in the product form of the module docs: `false` unless
    /// $`m \in \mathcal M_\Sigma`$, $`x_1 \in \mathcal X_1`$ and $`s`$ have their lengths (only a
    /// wiped value has not), $`\|s\|^2 \le \lfloor\beta_s^2\rfloor`$ (exact, `u128`
    /// accumulation), and
    /// $`(s_0 + h s_1 - b_u\,usk - b_\phi\phi - B_r x_0)\cdot(v - x_1) = 1`$. Five products with
    /// prepared operands and one plain product, about 0.14 ms. Never panics.
    fn verify(
        pp: &Self::PublicParams,
        vk: &Self::VerificationKey,
        m: &Self::Message,
        cred: &Self::Credential,
    ) -> bool {
        // Step 1; "v - x_1 is invertible" is part of the product form of step 2.
        if !m.is_in_message_space() || !cred.is_well_formed() || cred.norm_sq() > S_BOUND {
            return false;
        }
        // Step 2.
        let Some(residual) = pp.residual(vk, m, &cred.s) else {
            return false;
        };
        let g = Zeroizing::new(pp.v.sub(&Zeroizing::new(cred.x1.to_rq())));
        is_one(&Zeroizing::new(residual.mul(&g)))
    }

    /// $`\mathsf{Enc}_\Sigma((usk, x_0), \phi) = (usk, \phi, x_0)`$ (bb:804).
    ///
    /// # Errors
    /// [`Error::InvalidMessage`] for a wiped component.
    fn encode_message(
        _pp: &Self::PublicParams,
        m_hid: &Self::HiddenMessage,
        m_pub: &Self::PublicMessage,
    ) -> Result<Self::Message, Error> {
        if !m_hid.is_in_message_space() {
            return Err(Error::InvalidMessage);
        }
        Ok(VSISMessage {
            usk: m_hid.usk.clone(),
            phi: *m_pub,
            x0: m_hid.x0.clone(),
        })
    }

    /// $`C = \mathsf{Com}_{vk}((usk, x_0), \phi; x_0) = b_u\,usk + B_r x_0 \bmod q`$ (bb:806;
    /// `vk` and $`\phi`$ do not enter: the signer adds $`b_\phi\phi`$). Three products with
    /// prepared operands, about 66 µs.
    ///
    /// # Errors
    /// [`Error::InvalidMessage`] if the issuance state $`r`$ is not the $`x_0`$ of
    /// $`m_{\mathsf{hid}}`$ (implementation note, as for `Σ-BBS`), or for a wiped component.
    fn issuance_encoding(
        pp: &Self::PublicParams,
        _vk: &Self::VerificationKey,
        m_hid: &Self::HiddenMessage,
        _m_pub: &Self::PublicMessage,
        r: &Self::IssuanceState,
    ) -> Result<Self::IssuanceEncoding, Error> {
        if !same_x0(&r.0, &m_hid.x0) {
            return Err(Error::InvalidMessage);
        }
        pp.commitment(&m_hid.usk, &m_hid.x0)
    }

    /// `ReRand → (⊥, cred)` (bb:833-836): nothing is randomized; the credential becomes the
    /// show state, the witness of the possession argument.
    ///
    /// # Errors
    /// [`Error::InvalidCredential`] for a wiped credential (implementation note).
    fn rerand<R: RngCore + CryptoRng + ?Sized>(
        _pp: &Self::PublicParams,
        _vk: &Self::VerificationKey,
        _m: &Self::Message,
        cred: &Self::Credential,
        _rng: &mut R,
    ) -> Result<(Self::ShownCredential, Self::ShowState), Error> {
        if !cred.is_well_formed() {
            return Err(Error::InvalidCredential);
        }
        Ok(((), cred.clone()))
    }

    /// `BlindIssue` (bb:838-844):
    /// 1. $`x_1 \gets \mathcal X_1`$ until $`v - x_1`$ is a unit;
    /// 2. $`t = (v - x_1)^{-1} + C + b_\phi\phi`$;
    /// 3. $`s \gets \mathsf{SampPre}(td_A, t, \varsigma)`$ with a fresh seed, under the cap;
    /// 4. $`\widehat{cred} = (s, x_1)`$.
    ///
    /// Every $`C \in R_q`$ is accepted, as in the box: the construction calls this only after
    /// `VerifyProof` (con:177-178). About 0.25 ms (an inversion, one product, `SampPre`).
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped key; [`Error::InvalidIssuanceEncoding`] for a wiped
    /// $`C`$; [`Error::IssuanceCapReached`] at the cap; [`Error::LatticeBackend`] if a bounded
    /// loop gives up (module docs).
    fn blind_issue<R: RngCore + CryptoRng + ?Sized>(
        pp: &Self::PublicParams,
        sk: &Self::SigningKey,
        c: &Self::IssuanceEncoding,
        m_pub: &Self::PublicMessage,
        rng: &mut R,
    ) -> Result<Self::PreCredential, Error> {
        sk.ensure_usable()?;
        if c.coeffs().len() != D {
            return Err(Error::InvalidIssuanceEncoding);
        }
        issue_preimage(pp, sk, c, m_pub, rng)
    }

    /// `Unblind` (bb:846-849): returns $`\widehat{cred}`$ iff `Verify` accepts it (unlike the
    /// pairing bases, the box of `Σ-vSIS` verifies here; the construction relies on it, con:184).
    ///
    /// # Errors
    /// [`Error::InvalidMessage`] if the issuance state $`r`$ is not the $`x_0`$ of $`m`$
    /// (implementation note, as for `Σ-BBS`); [`Error::InvalidPreCredential`] if `Verify`
    /// rejects.
    fn unblind(
        pp: &Self::PublicParams,
        vk: &Self::VerificationKey,
        m: &Self::Message,
        pre: &Self::PreCredential,
        r: &Self::IssuanceState,
    ) -> Result<Self::Credential, Error> {
        if !same_x0(&r.0, &m.x0) {
            return Err(Error::InvalidMessage);
        }
        if Self::verify(pp, vk, m, pre) {
            Ok(pre.clone())
        } else {
            Err(Error::InvalidPreCredential)
        }
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
        pp: VSISPublicParams,
        vk: VSISVerificationKey,
        sk: VSISSigningKey,
        rng: StdRng,
    }

    /// `pp` of [`LABEL`] and ONE real helper key (TrapGen).
    fn fixture(seed: u64) -> Fixture {
        let mut rng = StdRng::seed_from_u64(seed);
        let pp = VSIS::setup(LABEL).unwrap();
        let (vk, sk) = VSIS::keygen(&pp, &mut rng);
        Fixture { pp, vk, sk, rng }
    }

    /// A uniform hidden message, a random binary φ and the matching issuance state.
    fn message(rng: &mut StdRng) -> (VSISHiddenMessage, BinaryPoly, VSISIssuanceState) {
        let usk = Ternary::sample(rng);
        let x0 = [Ternary::sample(rng), Ternary::sample(rng)];
        let mut phi = [0u8; BinaryPoly::BYTES];
        rng.fill_bytes(&mut phi);
        (
            VSISHiddenMessage::new(usk, x0.clone()),
            BinaryPoly::from_bytes(phi),
            VSISIssuanceState::new(x0),
        )
    }

    /// `x` with its coefficient `i` replaced by another value of {-1, 0, 1}.
    fn changed(x: &Ternary, i: usize) -> Ternary {
        let mut c = x.coeffs().to_vec();
        c[i] = if c[i] == 1 { 0 } else { c[i] + 1 };
        Ternary::from_coeffs(&c).unwrap()
    }

    fn flip_bit(phi: &BinaryPoly, i: usize) -> BinaryPoly {
        let mut bytes = *phi.as_bytes();
        bytes[i / 8] ^= 1 << (i % 8);
        BinaryPoly::from_bytes(bytes)
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

    fn m_of(pp: &VSISPublicParams, m_hid: &VSISHiddenMessage, phi: &BinaryPoly) -> VSISMessage {
        VSIS::encode_message(pp, m_hid, phi).unwrap()
    }

    // ----- Setup ----------------------------------------------------------------------------

    /// `pp_Σ` is the expansion of the label under the documented element names (the known answers
    /// are those of `lattice::xof`, computed independently with Python's hashlib).
    #[test]
    fn setup_expands_the_label_under_the_documented_names() {
        let pp = VSIS::setup(b"PCS-LATTICE-KAT").unwrap();
        let kat: [(&Rq, [u32; 4], u32, u32); 5] = [
            (pp.v(), [770406, 508595, 476174, 818112], 192742, 537406709),
            (pp.b_u(), [444343, 26088, 417981, 121684], 367357, 565256750),
            (
                pp.b_phi(),
                [801507, 195483, 356755, 209711],
                879905,
                541107186,
            ),
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
        // deterministic, separated by the label, five distinct elements
        assert_eq!(VSIS::setup(LABEL).unwrap(), VSIS::setup(LABEL).unwrap());
        let other = VSIS::setup(b"another deployment").unwrap();
        let ours = VSIS::setup(LABEL).unwrap();
        for (a, b) in ours.elements().iter().zip(other.elements()) {
            assert_ne!(*a, b);
        }
        let e = ours.elements();
        for i in 0..5 {
            for j in i + 1..5 {
                assert_ne!(e[i], e[j]);
            }
        }
        assert_eq!(format!("{ours:?}"), "VSISPublicParams(v, b_u, b_phi, B_r)");
    }

    #[test]
    fn public_parameters_round_trip_with_their_prepared_columns() {
        let mut rng = StdRng::seed_from_u64(0x5151_0001);
        let pp = VSIS::setup(LABEL).unwrap();
        let bytes = to_bytes(&pp).unwrap();
        assert_eq!(bytes.len(), VSISPublicParams::BYTES);
        assert_eq!(bytes.len(), 12_800);
        let back: VSISPublicParams = from_bytes(&bytes).unwrap();
        assert_eq!(back, pp);
        assert!(back.check().is_ok());
        // the prepared columns of the decoded value compute the same products
        let (m_hid, phi, _) = message(&mut rng);
        assert_eq!(
            back.commitment(m_hid.usk(), m_hid.x0()).unwrap(),
            pp.commitment(m_hid.usk(), m_hid.x0()).unwrap()
        );
        assert_eq!(back.phi_term(&phi), pp.phi_term(&phi));
        // a coefficient q in the last element, a short and a long input are refused
        let mut bad = bytes.clone();
        let at = 4 * Rq::BYTES;
        bad[at] = (Q & 0xff) as u8;
        bad[at + 1] = ((Q >> 8) & 0xff) as u8;
        bad[at + 2] = (bad[at + 2] & 0xf0) | ((Q >> 16) & 0x0f) as u8;
        assert!(from_bytes::<VSISPublicParams>(&bad).is_err());
        assert!(from_bytes::<VSISPublicParams>(&bytes[..bytes.len() - 1]).is_err());
        let mut long = bytes;
        long.push(0);
        assert_eq!(
            from_bytes::<VSISPublicParams>(&long).unwrap_err(),
            Error::TrailingBytes
        );
    }

    // ----- KeyGen ---------------------------------------------------------------------------

    #[test]
    fn keygen_outputs_a_trapdoor_for_its_key() {
        let fx = fixture(0x5151_0002);
        assert_eq!(fx.sk.verification_key().unwrap(), fx.vk);
        assert!(VSIS::is_well_formed_key(&fx.pp, &fx.vk));
        assert_eq!(fx.sk.issued(), 0);
        assert_eq!(fx.sk.remaining(), Q_MAX);
        assert_eq!(fx.sk.sk.to_bytes().len(), SECRET_KEY_BYTES);
        // a fresh seed per call: another key
        let mut rng = StdRng::seed_from_u64(0x5151_0003);
        let (vk2, _) = VSIS::keygen(&fx.pp, &mut rng);
        assert_ne!(vk2, fx.vk);
        // V_pp is every canonical h (con:194): any element is a key
        let any = VSISVerificationKey::from_h(VSIS::setup(b"h").unwrap().v().clone());
        assert!(VSIS::is_well_formed_key(&fx.pp, &any));
        assert_eq!(format!("{any:?}"), "VSISVerificationKey(h)");
        let bytes = to_bytes(&fx.vk).unwrap();
        assert_eq!(bytes.len(), VSISVerificationKey::BYTES);
        assert_eq!(from_bytes::<VSISVerificationKey>(&bytes).unwrap(), fx.vk);
    }

    #[test]
    fn the_signing_key_is_shared_across_threads() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<VSISSigningKey>();
        assert_send_sync::<VSISPublicParams>();
        assert_send_sync::<VSISVerificationKey>();
        assert_send_sync::<VSISCredential>();
    }

    // ----- Com, Sign, BlindIssue, Unblind, Verify --------------------------------------------

    /// `Com` is b_u usk + B_r x_0 (bb:806), computed with the plain products here; φ and vk do not
    /// enter; the issuance state must be the x_0 of the message.
    #[test]
    fn com_is_the_documented_sum() {
        let mut fx = fixture(0x5151_0004);
        let (m_hid, phi, r) = message(&mut fx.rng);
        let pp = &fx.pp;
        let expected = pp
            .b_u()
            .mul(&m_hid.usk().to_rq())
            .add(&pp.b_r()[0].mul(&m_hid.x0()[0].to_rq()))
            .add(&pp.b_r()[1].mul(&m_hid.x0()[1].to_rq()));
        let c = VSIS::issuance_encoding(pp, &fx.vk, &m_hid, &phi, &r).unwrap();
        assert_eq!(c, expected);
        let other_vk = VSISVerificationKey::from_h(pp.v().clone());
        let other_phi = flip_bit(&phi, 3);
        assert_eq!(
            VSIS::issuance_encoding(pp, &other_vk, &m_hid, &other_phi, &r).unwrap(),
            c
        );
        assert_eq!(pp.phi_term(&phi), pp.b_phi().mul(&phi.to_rq()));
        // r ≠ x_0 of m_hid
        let r2 = VSISIssuanceState::new([changed(&r.x0()[0], 7), r.x0()[1].clone()]);
        assert_eq!(
            VSIS::issuance_encoding(pp, &fx.vk, &m_hid, &phi, &r2).unwrap_err(),
            Error::InvalidMessage
        );
    }

    #[test]
    fn signed_and_blindly_issued_credentials_verify() {
        let mut fx = fixture(0x5151_0005);
        let (m_hid, phi, r) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        let cred = VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap();
        assert!(VSIS::verify(&fx.pp, &fx.vk, &m, &cred));
        assert!(cred.norm_sq() <= S_BOUND);
        assert_eq!(fx.sk.issued(), 1);

        let c = VSIS::issuance_encoding(&fx.pp, &fx.vk, &m_hid, &phi, &r).unwrap();
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &phi, &mut fx.rng).unwrap();
        let unblinded = VSIS::unblind(&fx.pp, &fx.vk, &m, &pre, &r).unwrap();
        assert_eq!(unblinded, pre);
        assert!(VSIS::verify(&fx.pp, &fx.vk, &m, &unblinded));
        assert_eq!(fx.sk.issued(), 2);
        // fresh coins: two signatures on one message differ
        assert_ne!(cred, unblinded);
        // ReRand → (⊥, cred)
        let ((), omega) = VSIS::rerand(&fx.pp, &fx.vk, &m, &cred, &mut fx.rng).unwrap();
        assert_eq!(omega, cred);
    }

    /// Issuance indistinguishability as code-path identity (lem:base-vsis): for one message, `Sign`
    /// and `Unblind ∘ BlindIssue` run the same instructions on the same target and consume the RNG
    /// in the same order, so with the same RNG seed they return the SAME credential. (Test only:
    /// the coins are reused here on purpose; with the same arithmetic that is harmless.)
    #[test]
    fn sign_and_blind_issuance_are_one_code_path() {
        let mut fx = fixture(0x5151_0006);
        let (m_hid, phi, r) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        let c = VSIS::issuance_encoding(&fx.pp, &fx.vk, &m_hid, &phi, &r).unwrap();
        let signed = VSIS::sign(&fx.pp, &fx.sk, &m, &mut StdRng::seed_from_u64(42)).unwrap();
        let pre =
            VSIS::blind_issue(&fx.pp, &fx.sk, &c, &phi, &mut StdRng::seed_from_u64(42)).unwrap();
        let unblinded = VSIS::unblind(&fx.pp, &fx.vk, &m, &pre, &r).unwrap();
        assert_eq!(signed, unblinded);
        assert_eq!(fx.sk.issued(), 2);
    }

    #[test]
    fn verify_refuses_every_changed_input() {
        let mut fx = fixture(0x5151_0007);
        let (m_hid, phi, _) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        let cred = VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap();
        let (pp, vk) = (&fx.pp, &fx.vk);
        assert!(VSIS::verify(pp, vk, &m, &cred));

        // another message: usk, either component of x_0, φ
        let x0 = m_hid.x0();
        let others = [
            VSISHiddenMessage::new(changed(m_hid.usk(), 0), x0.clone()),
            VSISHiddenMessage::new(m_hid.usk().clone(), [changed(&x0[0], 500), x0[1].clone()]),
            VSISHiddenMessage::new(m_hid.usk().clone(), [x0[0].clone(), changed(&x0[1], 1023)]),
        ];
        for other in &others {
            assert!(!VSIS::verify(pp, vk, &m_of(pp, other, &phi), &cred));
        }
        assert!(!VSIS::verify(
            pp,
            vk,
            &m_of(pp, &m_hid, &flip_bit(&phi, 1000)),
            &cred
        ));

        // another x_1, another s_0, another s_1
        let x1 = changed(cred.x1(), 11);
        let tampered = [
            VSISCredential::from_parts(cred.s0().to_vec(), cred.s1().to_vec(), x1).unwrap(),
            {
                let mut s0 = cred.s0().to_vec();
                s0[17] += 1;
                VSISCredential::from_parts(s0, cred.s1().to_vec(), cred.x1().clone()).unwrap()
            },
            {
                let mut s1 = cred.s1().to_vec();
                s1[900] -= 1;
                VSISCredential::from_parts(cred.s0().to_vec(), s1, cred.x1().clone()).unwrap()
            },
        ];
        for t in &tampered {
            assert!(!VSIS::verify(pp, vk, &m, t));
        }

        // another key, other parameters
        let (vk2, _) = VSIS::keygen(pp, &mut fx.rng);
        assert!(!VSIS::verify(pp, &vk2, &m, &cred));
        let pp2 = VSIS::setup(b"another deployment").unwrap();
        assert!(!VSIS::verify(&pp2, vk, &m_of(&pp2, &m_hid, &phi), &cred));
    }

    /// `Verify` accepts ‖s‖² = ⌊β_s²⌋ and refuses ⌊β_s²⌋ + 1 (bb:829): s_1 = 1 and an s_0 of the
    /// chosen norm, under the key h = t - s_0 for which A s = t (every h is a key, con:194). The
    /// validation harness of the parameter sets built its boundary cases the same way (a key
    /// solved for a chosen s).
    #[test]
    fn verify_enforces_the_norm_bound_exactly() {
        let mut rng = StdRng::seed_from_u64(0x5151_0008);
        let pp = VSIS::setup(LABEL).unwrap();
        let (m_hid, phi, _) = message(&mut rng);
        let m = m_of(&pp, &m_hid, &phi);
        let (x1, y) = pp.sample_x1(&mut rng).unwrap();
        let c = pp.commitment(m.usk(), m.x0()).unwrap();
        let t = pp.target(&y, &c, &phi);
        let mut s1 = vec![0i32; D];
        s1[0] = 1;
        for (norm, accepted) in [(S_BOUND - 1, true), (S_BOUND, true), (S_BOUND + 1, false)] {
            let s0 = with_norm_sq(norm - 1);
            let vk = VSISVerificationKey::from_h(t.sub(&rq_of(&s0)));
            let cred = VSISCredential::from_parts(s0, s1.clone(), x1.clone()).unwrap();
            assert_eq!(cred.norm_sq(), norm);
            assert_eq!(VSIS::verify(&pp, &vk, &m, &cred), accepted, "‖s‖² = {norm}");
        }
    }

    /// Without the norm check the product form accepts a far-away preimage of the same target:
    /// s'_1 = s_1 + 1 and s'_0 = t - h s'_1 (centred) satisfy A s' = t with ‖s'‖² ≈ 2^46.
    #[test]
    fn the_norm_check_is_what_refuses_a_long_preimage() {
        let mut fx = fixture(0x5151_0009);
        let (m_hid, phi, _) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        let cred = VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap();
        let h = fx.vk.h();
        let t = rq_of(cred.s0()).add(&h.mul(&rq_of(cred.s1())));
        let mut s1 = cred.s1().to_vec();
        s1[0] += 1;
        let s0 = t.sub(&h.mul(&rq_of(&s1))).to_centered();
        let long = VSISCredential::from_parts(s0, s1, cred.x1().clone()).unwrap();
        assert!(long.norm_sq() > S_BOUND);
        let residual = fx.pp.residual(&fx.vk, &m, &long.s).unwrap();
        let g = fx.pp.v().sub(&long.x1().to_rq());
        assert!(is_one(&residual.mul(&g)), "the equation holds");
        assert!(!VSIS::verify(&fx.pp, &fx.vk, &m, &long));
    }

    #[test]
    fn unblind_fails_closed() {
        let mut fx = fixture(0x5151_000a);
        let (m_hid, phi, r) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        let c = VSIS::issuance_encoding(&fx.pp, &fx.vk, &m_hid, &phi, &r).unwrap();
        // issued for another φ: does not verify on m
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &flip_bit(&phi, 0), &mut fx.rng).unwrap();
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &m, &pre, &r).unwrap_err(),
            Error::InvalidPreCredential
        );
        // issued on another C (another x_0)
        let c2 = VSIS::issuance_encoding(
            &fx.pp,
            &fx.vk,
            &VSISHiddenMessage::new(
                m_hid.usk().clone(),
                [changed(&r.x0()[0], 3), r.x0()[1].clone()],
            ),
            &phi,
            &VSISIssuanceState::new([changed(&r.x0()[0], 3), r.x0()[1].clone()]),
        )
        .unwrap();
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c2, &phi, &mut fx.rng).unwrap();
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &m, &pre, &r).unwrap_err(),
            Error::InvalidPreCredential
        );
        // issued under another key
        let (_, sk2) = VSIS::keygen(&fx.pp, &mut fx.rng);
        let pre = VSIS::blind_issue(&fx.pp, &sk2, &c, &phi, &mut fx.rng).unwrap();
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &m, &pre, &r).unwrap_err(),
            Error::InvalidPreCredential
        );
        // the right pre-credential with an issuance state that is not the x_0 of m
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &phi, &mut fx.rng).unwrap();
        let r2 = VSISIssuanceState::new([r.x0()[0].clone(), changed(&r.x0()[1], 9)]);
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &m, &pre, &r2).unwrap_err(),
            Error::InvalidMessage
        );
        assert!(VSIS::unblind(&fx.pp, &fx.vk, &m, &pre, &r).is_ok());
    }

    /// The preimages have the width of the PCS set: E‖s‖² = 2dσ² for the coset Gaussian of
    /// σ = ς/√(2π) = 2656.42. The standard deviation of ‖s‖²/(2dσ²) is √(2/2048) = 1/32 per
    /// preimage, so in the normal approximation one preimage leaves ±20% with probability about
    /// 2^-32.6 and the mean of 8 leaves ±5% with probability about 2^-17.3 [computed]. x_1 is
    /// uniform ternary.
    #[test]
    fn preimages_and_x1_have_the_documented_distributions() {
        let mut fx = fixture(0x5151_000b);
        let (m_hid, phi, r) = message(&mut fx.rng);
        let c = VSIS::issuance_encoding(&fx.pp, &fx.vk, &m_hid, &phi, &r).unwrap();
        let sigma = ntru_trapdoor::Params::PCS.sigma;
        let expected = 2.0 * D as f64 * sigma * sigma;
        let mut total = 0.0;
        let mut counts = [0usize; 3];
        for _ in 0..8 {
            let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &phi, &mut fx.rng).unwrap();
            let ratio = pre.norm_sq() as f64 / expected;
            assert!((0.8..1.2).contains(&ratio), "‖s‖²/(2dσ²) = {ratio}");
            assert!(
                pre.s0()
                    .iter()
                    .chain(pre.s1())
                    .all(|&x| x.unsigned_abs() <= S_MAX_ABS)
            );
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
        let mut fx = fixture(0x5151_000c);
        for k in 0..3u64 {
            let t = VSIS::setup(&k.to_le_bytes()).unwrap().v().clone();
            let s = fx.sk.sample_preimage(&t, &mut fx.rng).unwrap();
            assert!(ntru_trapdoor::verify(&fx.vk.pk, t.poly(), &s, S_BOUND));
        }
        assert_eq!(fx.sk.issued(), 3);
    }

    /// The exact check every preimage passes before it is released (bb:864: `s ∈ Λ_t` in integer
    /// arithmetic): it accepts the sampler's outputs and refuses a vector one unit off in either
    /// half, a preimage presented for another target, and a long vector of the coset.
    #[test]
    fn preimages_are_checked_exactly_before_release() {
        let mut fx = fixture(0x5151_0016);
        let t = VSIS::setup(b"target").unwrap().v().clone();
        let s = fx.sk.sample_preimage(&t, &mut fx.rng).unwrap();
        assert!(fx.sk.is_short_preimage(&t, &s));
        let other = VSIS::setup(b"other target").unwrap().v().clone();
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
        let mut fx = fixture(0x5151_0017);
        let (m_hid, phi, _) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        for _ in 0..3 {
            VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap();
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
        let cred = VSIS::sign(&fx.pp, &restored, &m, &mut fx.rng).unwrap();
        assert!(VSIS::verify(&fx.pp, &fx.vk, &m, &cred));
        assert_eq!(restored.issued(), 14);
        // saturation at the cap: the stored key decodes and refuses to sign
        fx.sk.issued.store(Q_MAX - 2, Ordering::SeqCst);
        let at_cap: VSISSigningKey = from_bytes(&fx.sk.to_bytes_reserving(5).unwrap()).unwrap();
        assert_eq!(at_cap.remaining(), 0);
        assert_eq!(
            VSIS::sign(&fx.pp, &at_cap, &m, &mut fx.rng).unwrap_err(),
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

    // ----- the issuance cap (con:220-221) ----------------------------------------------------

    #[test]
    fn the_issuance_cap_is_enforced() {
        let mut fx = fixture(0x5151_000d);
        let (m_hid, phi, r) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        let c = VSIS::issuance_encoding(&fx.pp, &fx.vk, &m_hid, &phi, &r).unwrap();
        fx.sk.issued.store(Q_MAX - 1, Ordering::SeqCst);
        assert_eq!(fx.sk.remaining(), 1);
        let pre = VSIS::blind_issue(&fx.pp, &fx.sk, &c, &phi, &mut fx.rng).unwrap();
        assert!(VSIS::unblind(&fx.pp, &fx.vk, &m, &pre, &r).is_ok());
        assert_eq!((fx.sk.issued(), fx.sk.remaining()), (Q_MAX, 0));
        for _ in 0..3 {
            assert_eq!(
                VSIS::blind_issue(&fx.pp, &fx.sk, &c, &phi, &mut fx.rng).unwrap_err(),
                Error::IssuanceCapReached
            );
            assert_eq!(
                VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap_err(),
                Error::IssuanceCapReached
            );
            let t = fx.pp.v().clone();
            assert_eq!(
                fx.sk.sample_preimage(&t, &mut fx.rng).unwrap_err(),
                Error::IssuanceCapReached
            );
        }
        assert_eq!(fx.sk.issued(), Q_MAX);
        // the count travels with the key, and a key at the cap stays at the cap
        let back: VSISSigningKey = from_bytes(&to_bytes(&fx.sk).unwrap()).unwrap();
        assert_eq!(back.issued(), Q_MAX);
        assert_eq!(
            VSIS::blind_issue(&fx.pp, &back, &c, &phi, &mut fx.rng).unwrap_err(),
            Error::IssuanceCapReached
        );
    }

    /// 16 threads share a key with 10 calls left: exactly 10 pre-credentials come out.
    #[test]
    fn concurrent_issuance_never_exceeds_the_cap() {
        let mut fx = fixture(0x5151_000e);
        let (m_hid, phi, r) = message(&mut fx.rng);
        let c = VSIS::issuance_encoding(&fx.pp, &fx.vk, &m_hid, &phi, &r).unwrap();
        fx.sk.issued.store(Q_MAX - 10, Ordering::SeqCst);
        let (pp, sk, c, phi) = (&fx.pp, &fx.sk, &c, &phi);
        let results: Vec<Result<VSISCredential, Error>> = thread::scope(|scope| {
            let handles: Vec<_> = (0..16u64)
                .map(|i| {
                    scope.spawn(move || {
                        let mut rng = StdRng::seed_from_u64(i);
                        (0..2)
                            .map(|_| VSIS::blind_issue(pp, sk, c, phi, &mut rng))
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
        let m = m_of(pp, &m_hid, phi);
        for pre in results.iter().flatten() {
            assert!(VSIS::verify(pp, &fx.vk, &m, pre));
        }
    }

    // ----- encodings ------------------------------------------------------------------------

    #[test]
    fn the_signing_key_round_trips_with_its_count() {
        let mut fx = fixture(0x5151_000f);
        let (m_hid, phi, _) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        for _ in 0..3 {
            VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap();
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
        let cred = VSIS::sign(&fx.pp, &back, &m, &mut fx.rng).unwrap();
        assert!(VSIS::verify(&fx.pp, &fx.vk, &m, &cred));
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
    fn credentials_and_issuance_states_round_trip_strictly() {
        let mut fx = fixture(0x5151_0010);
        let (m_hid, phi, r) = message(&mut fx.rng);
        let m = m_of(&fx.pp, &m_hid, &phi);
        let cred = VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap();
        let bytes = to_bytes(&cred).unwrap();
        assert_eq!(bytes.len(), VSISCredential::BYTES);
        assert_eq!(bytes.len(), 5376);
        let back: VSISCredential = from_bytes(&bytes).unwrap();
        assert_eq!(back, cred);
        assert!(back.check().is_ok());
        assert!(VSIS::verify(&fx.pp, &fx.vk, &m, &back));
        // the layout: s_0[0] in the low 20 bits, x_1 in the last 256 bytes
        let low =
            u32::from(bytes[0]) | u32::from(bytes[1]) << 8 | (u32::from(bytes[2]) & 0xf) << 16;
        assert_eq!(((low << 12) as i32) >> 12, cred.s0()[0]);
        assert_eq!(&bytes[2 * S_HALF_BYTES..], &cred.x1().to_bytes()[..]);
        // the code -2^19, the ternary code 10, truncation, trailing bytes
        let mut bad = bytes.clone();
        bad[0] = 0;
        bad[1] = 0;
        bad[2] = (bad[2] & 0xf0) | 0x08;
        assert!(from_bytes::<VSISCredential>(&bad).is_err());
        let mut bad = bytes.clone();
        bad[2 * S_HALF_BYTES] = (bad[2 * S_HALF_BYTES] & 0xfc) | 0b10;
        assert!(from_bytes::<VSISCredential>(&bad).is_err());
        assert!(from_bytes::<VSISCredential>(&bytes[..bytes.len() - 1]).is_err());
        let mut long = bytes;
        long.push(0);
        assert_eq!(
            from_bytes::<VSISCredential>(&long).unwrap_err(),
            Error::TrailingBytes
        );

        let state = to_bytes(&r).unwrap();
        assert_eq!(state.len(), VSISIssuanceState::BYTES);
        assert_eq!(state.len(), 512);
        let back: VSISIssuanceState = from_bytes(&state).unwrap();
        assert!(same_x0(back.x0(), r.x0()));
        assert!(back.check().is_ok());
    }

    #[test]
    fn credentials_are_assembled_from_checked_parts() {
        let x1 = Ternary::zero();
        let ok = VSISCredential::from_parts(vec![1; D], vec![-1; D], x1.clone()).unwrap();
        assert_eq!(ok.norm_sq(), 2 * D as u64);
        assert_eq!(
            VSISCredential::from_parts(vec![0; D - 1], vec![0; D], x1.clone()).unwrap_err(),
            Error::LengthMismatch {
                expected: D,
                actual: D - 1
            }
        );
        assert_eq!(
            VSISCredential::from_parts(vec![0; D], vec![0; D + 1], x1.clone()).unwrap_err(),
            Error::LengthMismatch {
                expected: D,
                actual: D + 1
            }
        );
        let mut wiped = x1.clone();
        wiped.zeroize();
        assert_eq!(
            VSISCredential::from_parts(vec![0; D], vec![0; D], wiped).unwrap_err(),
            Error::LengthMismatch {
                expected: D,
                actual: 0
            }
        );
        let mut s0 = vec![0; D];
        s0[5] = 1 << 19;
        assert_eq!(
            VSISCredential::from_parts(s0, vec![0; D], x1.clone()).unwrap_err(),
            Error::InvalidCredential
        );
        let mut s1 = vec![0; D];
        s1[5] = -(1 << 19) + 1;
        assert!(VSISCredential::from_parts(vec![0; D], s1, x1).is_ok());
    }

    // ----- secrets and wiped values ----------------------------------------------------------

    #[test]
    fn secrets_are_redacted_and_wiped_and_wiped_values_are_refused() {
        fn assert_zeroize_on_drop<T: ZeroizeOnDrop>() {}
        assert_zeroize_on_drop::<VSISSigningKey>();
        assert_zeroize_on_drop::<VSISHiddenMessage>();
        assert_zeroize_on_drop::<VSISMessage>();
        assert_zeroize_on_drop::<VSISIssuanceState>();
        assert_zeroize_on_drop::<VSISCredential>();

        let mut fx = fixture(0x5151_0011);
        let (mut m_hid, phi, mut r) = message(&mut fx.rng);
        let mut m = m_of(&fx.pp, &m_hid, &phi);
        let c = VSIS::issuance_encoding(&fx.pp, &fx.vk, &m_hid, &phi, &r).unwrap();
        let mut cred = VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap();
        for (value, expected) in [
            (format!("{:?}", fx.sk), "VSISSigningKey(<redacted>)"),
            (format!("{m_hid:?}"), "VSISHiddenMessage(<redacted>)"),
            (format!("{m:?}"), "VSISMessage(<redacted>)"),
            (format!("{r:?}"), "VSISIssuanceState(<redacted>)"),
            (format!("{cred:?}"), "VSISCredential(<redacted>)"),
        ] {
            assert_eq!(value, expected);
        }

        // a wiped credential: no verification, no show, no encoding
        let kept = cred.clone();
        cred.zeroize();
        assert!(cred.s0().is_empty() && cred.s1().is_empty() && cred.x1().coeffs().is_empty());
        assert!(!VSIS::verify(&fx.pp, &fx.vk, &m, &cred));
        assert_eq!(
            VSIS::rerand(&fx.pp, &fx.vk, &m, &cred, &mut fx.rng).unwrap_err(),
            Error::InvalidCredential
        );
        assert!(to_bytes(&cred).is_err());
        assert!(cred.check().is_err());
        assert_ne!(cred, kept);

        // a wiped C
        let mut wiped_c = c.clone();
        wiped_c.zeroize();
        assert_eq!(
            VSIS::blind_issue(&fx.pp, &fx.sk, &wiped_c, &phi, &mut fx.rng).unwrap_err(),
            Error::InvalidIssuanceEncoding
        );

        // a wiped message, hidden message and issuance state
        m.zeroize();
        assert!(m.usk().coeffs().is_empty());
        assert!(!VSIS::verify(&fx.pp, &fx.vk, &m, &kept));
        assert_eq!(
            VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap_err(),
            Error::InvalidMessage
        );
        let m = m_of(&fx.pp, &m_hid, &phi);
        r.zeroize();
        assert_eq!(
            VSIS::unblind(&fx.pp, &fx.vk, &m, &kept, &r).unwrap_err(),
            Error::InvalidMessage
        );
        assert!(to_bytes(&r).is_err());
        m_hid.zeroize();
        assert_eq!(
            VSIS::encode_message(&fx.pp, &m_hid, &phi).unwrap_err(),
            Error::InvalidMessage
        );
        assert_eq!(
            VSIS::issuance_encoding(&fx.pp, &fx.vk, &m_hid, &phi, &r).unwrap_err(),
            Error::InvalidMessage
        );

        // a wiped key signs nothing and consumes nothing
        let before = fx.sk.issued();
        fx.sk.zeroize();
        assert_eq!(
            VSIS::sign(&fx.pp, &fx.sk, &m, &mut fx.rng).unwrap_err(),
            Error::InvalidKey
        );
        assert_eq!(
            VSIS::blind_issue(&fx.pp, &fx.sk, &c, &phi, &mut fx.rng).unwrap_err(),
            Error::InvalidKey
        );
        assert_eq!(
            fx.sk.sample_preimage(&c, &mut fx.rng).unwrap_err(),
            Error::InvalidKey
        );
        assert_eq!(fx.sk.verification_key().unwrap_err(), Error::InvalidKey);
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
        let mut rng = StdRng::seed_from_u64(0x5151_0012);
        let a = [Ternary::sample(&mut rng), Ternary::sample(&mut rng)];
        assert!(same_x0(&a, &a.clone()));
        assert!(!same_x0(&a, &[a[0].clone(), changed(&a[1], 0)]));
        assert_eq!(
            with_norm_sq(S_BOUND)
                .iter()
                .map(|&x| i64::from(x).pow(2) as u64)
                .sum::<u64>(),
            S_BOUND
        );
    }
}
