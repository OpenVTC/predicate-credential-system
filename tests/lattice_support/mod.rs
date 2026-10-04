//! Shared code of the heavy lattice integration tests (`lattice_flows.rs`, `lattice_attacks.rs`,
//! `lattice_sizes.rs`, `lattice_parallel.rs`). Everything goes through the PUBLIC API of the
//! crate, the `jali` re-export and the public API of `ntru-trapdoor`; nothing here is a hook into
//! the library.
//!
//! * Deployments with ONE real helper key (`HKeyGen` = an NTRU trapdoor) and members with root
//!   credentials.
//! * [`Log`]: the check log of the validation harness (`[PASS] section: check -> detail`),
//!   counting the harness's own checks (`H`) apart from the checks added here (`X`). Every
//!   check is an assertion: the first failure panics with its section and name.
//! * [`Port`]: a CHEATING PROVER. An independent port of the harness's statement builders
//!   (`pcs-128-v2/setR/harness/src/rel.rs:36-153`, `pcs.rs:145-153`), so that a test can prove
//!   what the honest prover refuses to prove: false witnesses (Jali's witness check), proofs
//!   under chosen contexts, non-canonical tags, a non-binary `φ`, and issuance proofs `π_0` over
//!   attestation lists that `CheckAtts_P` rejects. Its statements must be the library's
//!   exactly; the tests check that the library's verifier accepts the port's honest proofs and
//!   that the port verifies the library's proofs, before they rely on it.
//! * [`Trapdoor`]: the helper's NTRU trapdoor, decoded from the encoding of `hsk` with
//!   `ntru-trapdoor`'s own decoder, for REAL preimages of arbitrary targets under the one helper
//!   key. The false-witness checks of the harness need credentials on messages outside `M_Σ`
//!   (`x_1`, `usk` or `x_0` with a coefficient 2, a non-binary `φ`), which no algorithm of the
//!   construction signs. Its calls do not count toward the helper's issuance cap: it is a test
//!   device, not the helper.
#![allow(dead_code)] // each test binary uses a part of this module
#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

use std::{collections::BTreeMap, fmt::Debug, sync::Arc, time::Instant};

use predicate_credential_system::{
    Error, LatticePCS,
    cred::{
        VSIS,
        vsis::{VSISCredential, VSISPreCredential, VSISPublicParams, VSISVerificationKey},
    },
    hash::Transcript,
    jali::{
        self,
        math::{Poly, Ring},
        params::TboxParams,
        statement::{Norm, Placement, Statement},
    },
    kiprf::lwr::{LWRTag, TagMatrix},
    lattice::{
        BETA_R, BETA_U, BETA_X, BinaryPoly, D, E_BOUND, E_COUNT, E_DEG, GAMMA, M, P, Q, Q_T, Rq,
        S_BOUND, Ternary, sets::ParameterSets,
    },
    pcs::{
        AllowList, HelperSecretKey, Predicate, PredicateCredentialSystem, SetupParams,
        lattice::{
            Attestation, Credential, IssuanceProof, IssuanceState, PublicParameters, RootRequest,
            UserSecretKey,
        },
    },
    serialization::WireFormat,
};
use rand::{RngCore, rngs::StdRng};

/// The construction with an allow-list policy over the disclosed labels.
pub type Pcs = LatticePCS<AllowList<BinaryPoly>>;

/// A deployment whose helper counts the attesters with credentials of `admitted` (the operator
/// rule of `docs/operating-a-helper.md`: no `P ≡ 1`).
pub fn deployment(label: &[u8], admitted: &[&Predicate]) -> Pcs {
    let open = LatticePCS::setup(SetupParams::new(label.to_vec())).unwrap();
    let policy = open.allow_list(admitted.iter().copied());
    LatticePCS::from_public_parameters(open.public_parameters().clone(), policy).unwrap()
}

/// The same `pp` with the policy `P ≡ 1` (a control verifier: a request it accepts is refused
/// by the allow-list verifier for its labels alone).
pub fn open_verifier(pcs: &Pcs) -> LatticePCS {
    LatticePCS::from_public_parameters(pcs.public_parameters().clone(), Default::default()).unwrap()
}

/// A user, with a credential once it has one.
pub struct Member {
    pub name: String,
    pub id: LWRTag,
    pub usk: UserSecretKey,
    pub cred: Option<Credential>,
    pub f: Option<Predicate>,
}

impl Member {
    pub fn new(pcs: &Pcs, name: &str, rng: &mut StdRng) -> Self {
        let (id, usk) = pcs.user_keygen(rng).unwrap();
        Self {
            name: name.to_string(),
            id,
            usk,
            cred: None,
            f: None,
        }
    }

    pub fn cred(&self) -> &Credential {
        self.cred.as_ref().expect("the member has a credential")
    }

    pub fn f(&self) -> &Predicate {
        self.f.as_ref().expect("the member has a credential")
    }
}

/// Root issuance of `member` under `f_root` (rem:chain), every object through its wire format;
/// returns the request.
pub fn root_issue(
    pcs: &Pcs,
    hvk: &VSISVerificationKey,
    hsk: &HelperSecretKey<VSIS>,
    member: &mut Member,
    f_root: &Predicate,
    rng: &mut StdRng,
) -> RootRequest {
    let (request, state) = pcs
        .root_request(hvk, f_root, &member.id, &member.usk, rng)
        .unwrap();
    let request = wire_root_request(&request);
    let pre = pcs
        .issue_root(hvk, hsk, f_root, &member.id, &request, rng)
        .unwrap();
    let pre = wire_pre(&pre);
    let state = wire_state(&state);
    let cred = pcs.unblind(hvk, &member.usk, f_root, &pre, &state).unwrap();
    let cred = wire_credential(&cred);
    assert!(pcs.verify_cred(hvk, &member.usk, f_root, &cred));
    member.cred = Some(cred);
    member.f = Some(f_root.clone());
    request
}

pub fn secs(t: Instant) -> f64 {
    t.elapsed().as_secs_f64()
}

// ---------------------------------------------------------------------------------------------
// The check log
// ---------------------------------------------------------------------------------------------

/// Whose check: one of the validation harness's (`H`, mapped to the construction), or one added
/// by this suite (`X`: controls, PCS-API variants, round trips).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Harness,
    Extra,
}

pub use Kind::{Extra as X, Harness as H};

/// The harness's check log, as assertions.
pub struct Log {
    title: String,
    section: String,
    pub harness: usize,
    pub extra: usize,
    started: Instant,
}

impl Log {
    pub fn new(title: &str) -> Self {
        println!("==== {title} ====");
        Self {
            title: title.to_string(),
            section: String::new(),
            harness: 0,
            extra: 0,
            started: Instant::now(),
        }
    }

    pub fn section(&mut self, name: &str) {
        println!(
            "\n== {name} == [{:.1} s]",
            self.started.elapsed().as_secs_f64()
        );
        self.section = name.to_string();
    }

    fn pass(&mut self, kind: Kind, name: &str, detail: &str) {
        let tag = match kind {
            H => {
                self.harness += 1;
                "H"
            }
            X => {
                self.extra += 1;
                "+"
            }
        };
        println!("  [PASS {tag}] {}: {name} -> {detail}", self.section);
    }

    fn fail(&self, name: &str, detail: &str) -> ! {
        panic!(
            "[FAIL] {} / {}: {name} -> {detail}",
            self.title, self.section
        )
    }

    /// The check holds.
    pub fn holds(&mut self, kind: Kind, name: &str, condition: bool) {
        if !condition {
            self.fail(name, "does not hold");
        }
        self.pass(kind, name, "holds");
    }

    /// Accepted (`Ok`).
    pub fn ok<T>(&mut self, kind: Kind, name: &str, result: Result<T, Error>) -> T {
        match result {
            Ok(value) => {
                self.pass(kind, name, "accepted");
                value
            }
            Err(e) => self.fail(name, &format!("refused: {e:?}")),
        }
    }

    /// Accepted by Jali (`Ok`).
    pub fn ok_jali<T>(&mut self, kind: Kind, name: &str, result: Result<T, jali::Error>) -> T {
        match result {
            Ok(value) => {
                self.pass(kind, name, "accepted (Jali)");
                value
            }
            Err(e) => self.fail(name, &format!("refused by Jali: {e:?}")),
        }
    }

    /// Refused with exactly `expected`.
    pub fn refused<T: Debug>(
        &mut self,
        kind: Kind,
        name: &str,
        result: Result<T, Error>,
        expected: Error,
    ) {
        match result {
            Err(e) if e == expected => self.pass(kind, name, &format!("refused: {e:?}")),
            Err(e) => self.fail(name, &format!("refused with {e:?}, expected {expected:?}")),
            Ok(v) => self.fail(name, &format!("ACCEPTED ({v:?}), expected {expected:?}")),
        }
    }

    /// Refused by Jali with exactly `expected`.
    pub fn refused_jali(
        &mut self,
        kind: Kind,
        name: &str,
        result: Result<(), jali::Error>,
        expected: jali::Error,
    ) {
        match result {
            Err(e) if e == expected => self.pass(kind, name, &format!("refused by Jali: {e:?}")),
            Err(e) => self.fail(name, &format!("Jali: {e:?}, expected {expected:?}")),
            Ok(()) => self.fail(name, &format!("ACCEPTED, expected {expected:?}")),
        }
    }

    /// A false witness, refused by the honest prover's witness check (`Error::Witness`).
    pub fn witness(&mut self, kind: Kind, name: &str, result: Result<(), jali::Error>) {
        self.refused_jali(kind, name, result, jali::Error::Witness);
    }

    /// Prints the counts and asserts the number of harness checks.
    pub fn finish(&self, expected_harness: usize) {
        println!(
            "\n{}: {} harness checks and {} added checks passed in {:.1} s",
            self.title,
            self.harness,
            self.extra,
            self.started.elapsed().as_secs_f64()
        );
        assert_eq!(
            self.harness, expected_harness,
            "every check of the harness's flow is ported"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Wire round trips: every object a flow passes on goes through its encodings first
// ---------------------------------------------------------------------------------------------

/// An attestation through its compact and canonical encodings (they coincide): `468 + |π_j|`.
pub fn wire_attestation(att: &Attestation) -> Attestation {
    let compact = att.to_compact_bytes().unwrap();
    assert_eq!(compact.len(), att.compact_size());
    assert_eq!(compact.len(), Attestation::FIXED_BYTES + att.proof.len());
    assert_eq!(Attestation::FIXED_BYTES, 468);
    assert_eq!(WireFormat::to_bytes(att).unwrap(), compact);
    let back = Attestation::from_compact_bytes(&compact).unwrap();
    assert_eq!(&back, att);
    assert_eq!(
        <Attestation as WireFormat>::from_bytes(&compact).unwrap(),
        back
    );
    back
}

/// An issuance proof for `f` through its compact encoding (`k` from `f`) and its canonical one
/// (`LE32(k)` first): `Σ_j |att_j| + 2900 + |π_0|`, and 4 more.
pub fn wire_issuance_proof(proof: &IssuanceProof, f: &Predicate) -> IssuanceProof {
    let compact = proof.to_compact_bytes().unwrap();
    assert_eq!(compact.len(), proof.compact_size());
    let expected: usize = proof
        .attestations
        .iter()
        .map(Attestation::compact_size)
        .sum::<usize>()
        + IssuanceProof::FIXED_BYTES
        + proof.proof.len();
    assert_eq!(compact.len(), expected);
    assert_eq!(IssuanceProof::FIXED_BYTES, 2900);
    let canonical = WireFormat::to_bytes(proof).unwrap();
    assert_eq!(canonical.len(), compact.len() + 4);
    assert_eq!(
        &canonical[..4],
        &u32::try_from(proof.attestations.len())
            .unwrap()
            .to_le_bytes()
    );
    assert_eq!(&canonical[4..], &compact[..]);
    let back = IssuanceProof::from_compact_bytes(&compact, f).unwrap();
    assert_eq!(&back, proof);
    assert_eq!(
        <IssuanceProof as WireFormat>::from_bytes(&canonical).unwrap(),
        back
    );
    back
}

/// A root request through its encoding (compact = canonical): `2900 + |π_0|`.
pub fn wire_root_request(request: &RootRequest) -> RootRequest {
    let compact = request.to_compact_bytes().unwrap();
    assert_eq!(compact.len(), request.compact_size());
    assert_eq!(
        compact.len(),
        RootRequest::FIXED_BYTES + request.proof.len()
    );
    assert_eq!(WireFormat::to_bytes(request).unwrap(), compact);
    let back = RootRequest::from_compact_bytes(&compact).unwrap();
    assert_eq!(&back, request);
    assert_eq!(
        <RootRequest as WireFormat>::from_bytes(&compact).unwrap(),
        back
    );
    back
}

/// `cred = ((s, x_1), x_0)`: 5888 bytes.
pub fn wire_credential(cred: &Credential) -> Credential {
    let bytes = cred.to_bytes().unwrap();
    assert_eq!(bytes.len(), Credential::BYTES);
    assert_eq!(Credential::BYTES, 5888);
    let back = <Credential as WireFormat>::from_bytes(&bytes).unwrap();
    assert!(back == *cred);
    back
}

/// `ĉred = (s, x_1)`: 5376 bytes.
pub fn wire_pre(pre: &VSISPreCredential) -> VSISPreCredential {
    let bytes = WireFormat::to_bytes(pre).unwrap();
    assert_eq!(bytes.len(), VSISCredential::BYTES);
    assert_eq!(VSISCredential::BYTES, 5376);
    let back = <VSISPreCredential as WireFormat>::from_bytes(&bytes).unwrap();
    assert!(back == *pre);
    back
}

/// `st_iss`: 896 bytes.
pub fn wire_state(state: &IssuanceState) -> IssuanceState {
    let bytes = state.to_bytes().unwrap();
    assert_eq!(bytes.len(), IssuanceState::BYTES);
    assert_eq!(IssuanceState::BYTES, 896);
    let back = IssuanceState::from_bytes(&bytes).unwrap();
    assert_eq!(&*back.to_bytes().unwrap(), &*bytes);
    back
}

/// `usk`: 256 bytes.
pub fn wire_usk(usk: &UserSecretKey) -> UserSecretKey {
    let bytes = usk.to_bytes().unwrap();
    assert_eq!(bytes.len(), UserSecretKey::BYTES);
    assert_eq!(UserSecretKey::BYTES, 256);
    let back = <UserSecretKey as WireFormat>::from_bytes(&bytes).unwrap();
    assert!(back.expose_ternary().ct_eq(usk.expose_ternary()));
    back
}

/// `hvk = h`: 2560 bytes.
pub fn wire_hvk(hvk: &VSISVerificationKey) -> VSISVerificationKey {
    let bytes = WireFormat::to_bytes(hvk).unwrap();
    assert_eq!(bytes.len(), VSISVerificationKey::BYTES);
    assert_eq!(VSISVerificationKey::BYTES, 2560);
    let back = <VSISVerificationKey as WireFormat>::from_bytes(&bytes).unwrap();
    assert_eq!(&back, hvk);
    back
}

/// `hsk = (sk, hvk)` with the digest of `pp`: 5897 + 2560 + 32 = 8489 bytes; the issuance count
/// travels with it.
pub fn wire_hsk(hsk: &HelperSecretKey<VSIS>) -> HelperSecretKey<VSIS> {
    let bytes = hsk.to_bytes().unwrap();
    assert_eq!(bytes.len(), 8489);
    let back = <HelperSecretKey<VSIS> as WireFormat>::from_bytes(&bytes).unwrap();
    assert_eq!(back.verification_key(), hsk.verification_key());
    assert_eq!(back.parameters_digest(), hsk.parameters_digest());
    assert_eq!(back.signing_key().issued(), hsk.signing_key().issued());
    back
}

/// `id`, `T`: 336 bytes.
pub fn wire_tag(tag: &LWRTag) -> LWRTag {
    let bytes = WireFormat::to_bytes(tag).unwrap();
    assert_eq!(bytes.len(), LWRTag::BYTES);
    assert_eq!(LWRTag::BYTES, 336);
    let back = <LWRTag as WireFormat>::from_bytes(&bytes).unwrap();
    assert_eq!(&back, tag);
    back
}

/// Sets coefficient `j` of a 20-bit packed element of `R_q` (little-endian bit order, the
/// encoding of `Rq`, `hvk` and `C`) to `value`, which may be a non-canonical code `≥ q`.
pub fn set_coefficient_20(bytes: &mut [u8], j: usize, value: u32) {
    assert!(value < 1 << 20);
    for bit in 0..20 {
        let at = 20 * j + bit;
        let mask = 1u8 << (at % 8);
        if (value >> bit) & 1 == 1 {
            bytes[at / 8] |= mask;
        } else {
            bytes[at / 8] &= !mask;
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Ring helpers
// ---------------------------------------------------------------------------------------------

/// The integer coefficients of a ternary polynomial.
pub fn ints(x: &Ternary) -> Vec<i128> {
    x.coeffs().iter().map(|&c| i128::from(c)).collect()
}

/// An element of `R_q` from integer coefficients (reduced modulo `q`).
pub fn rq(c: &[i128]) -> Rq {
    Rq::from_i64(
        &c.iter()
            .map(|&x| i64::try_from(x).unwrap())
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

/// An element of `R_q` from the coefficients of one half of a preimage.
pub fn rq_i32(c: &[i32]) -> Rq {
    Rq::from_i64(&c.iter().map(|&x| i64::from(x)).collect::<Vec<_>>()).unwrap()
}

/// `‖(s_0, s_1)‖²`.
pub fn norm_sq(s0: &[i32], s1: &[i32]) -> u64 {
    s0.iter()
        .chain(s1)
        .map(|&x| u64::from(x.unsigned_abs()).pow(2))
        .sum()
}

/// The coefficients of `φ` as integers.
pub fn phi_ints(phi: &BinaryPoly) -> Vec<i128> {
    (0..D).map(|i| i128::from(phi.coefficient(i))).collect()
}

/// The binary polynomial with the coefficients `bits` (each 0 or 1).
pub fn binary(bits: &[u8]) -> BinaryPoly {
    assert_eq!(bits.len(), D);
    let mut bytes = [0u8; BinaryPoly::BYTES];
    for (i, &b) in bits.iter().enumerate() {
        assert!(b <= 1);
        bytes[i / 8] |= b << (i % 8);
    }
    BinaryPoly::from_bytes(bytes)
}

/// The target of `Sign` / `BlindIssue` for a message, with any integer coefficients:
/// `t = (v − x_1)^{-1} + b_u usk + B_r x_0 + b_φ φ` (bb:820).
pub fn target(sigma: &VSISPublicParams, usk: &Rq, x0: [&Rq; 2], x1: &Rq, phi: &Rq) -> Rq {
    sigma
        .v()
        .sub(x1)
        .inverse()
        .expect("v − x_1 is a unit")
        .add(&sigma.b_u().mul(usk))
        .add(&sigma.b_r()[0].mul(x0[0]))
        .add(&sigma.b_r()[1].mul(x0[1]))
        .add(&sigma.b_phi().mul(phi))
}

/// `C = b_u usk + B_r x_0` for any integer coefficients.
pub fn commitment(sigma: &VSISPublicParams, usk: &Rq, x0: [&Rq; 2]) -> Rq {
    sigma
        .b_u()
        .mul(usk)
        .add(&sigma.b_r()[0].mul(x0[0]))
        .add(&sigma.b_r()[1].mul(x0[1]))
}

/// The entries of a tag as integers (the statement builders take raw values, so that a test can
/// pass the non-canonical `T + p`).
pub fn tag_values(tag: &LWRTag) -> [i128; M] {
    tag.entries().map(i128::from)
}

/// The harness's `tag_eval` (H/pcs.rs:129-142) on any integer key, e.g. one with a coefficient
/// 2: `T_j = round(⟨a_j, usk⟩ / γ) mod p` and its error `e_j = γ T_j − ⟨a_j, usk⟩` centred mod
/// `q_t` (at most `(γ − 1)/2` whatever the key).
pub fn harness_tag_eval(usk: &[i128], a: &TagMatrix) -> ([i128; M], [i8; M]) {
    let (gamma, pt, qt) = (i128::from(GAMMA), i128::from(P), i128::from(Q_T));
    let mut t = [0i128; M];
    let mut e = [0i8; M];
    for (j, row) in a.rows().enumerate() {
        let w: i128 = row.iter().zip(usk).map(|(&x, y)| i128::from(x) * y).sum();
        t[j] = ((2 * w.rem_euclid(qt) + gamma) / (2 * gamma)).rem_euclid(pt);
        let ej = (gamma * t[j] - w).rem_euclid(qt);
        e[j] = i8::try_from(if ej > qt / 2 { ej - qt } else { ej }).unwrap();
    }
    (t, e)
}

/// The tag with the entries `t` (each below `p`).
pub fn tag_of(t: &[i128; M]) -> LWRTag {
    LWRTag::from_entries(t.map(|x| u16::try_from(x).unwrap()))
}

/// `T` with row `row` incremented modulo `p`.
pub fn bump(tag: &LWRTag, row: usize) -> LWRTag {
    let mut entries = *tag.entries();
    entries[row] = entries[row].wrapping_add(1);
    LWRTag::from_entries(entries)
}

/// The greedy vector of `D` integers with squared norm exactly `total` (the largest square first;
/// four squares suffice for every integer, the greedy needs a few more).
pub fn vector_with_norm(total: u64) -> Vec<i32> {
    let mut rest = total;
    let mut out = vec![0i32; D];
    for c in &mut out {
        let x = rest.isqrt();
        *c = i32::try_from(x).unwrap();
        rest -= x * x;
        if rest == 0 {
            break;
        }
    }
    assert_eq!(rest, 0);
    out
}

// ---------------------------------------------------------------------------------------------
// The cheating prover: an independent port of the harness's statements
// ---------------------------------------------------------------------------------------------

/// A witness: named blocks of statement-ring polynomials.
pub type Witness = BTreeMap<String, Vec<Poly>>;

/// The representative of `x` modulo `m` in `(−m/2, m/2]` (harness `common::centred`).
fn centred(x: i128, m: i128) -> i128 {
    let r = x.rem_euclid(m);
    if r > m / 2 { r - m } else { r }
}

/// The statement builders of H/rel.rs at the constants of one deployment, the embedded parameter
/// sets, and Jali's public seed of that deployment.
pub struct Port {
    pub rc: Arc<Ring>,
    pub rt: Arc<Ring>,
    v: Poly,
    b_u: Poly,
    b_r: [Poly; 2],
    pub c0_rows: Vec<Poly>,
    pub sets: ParameterSets,
    pub pp_seed: [u8; 32],
}

impl Port {
    pub fn new(pp: &PublicParameters) -> Self {
        let rc = Ring::new(i128::from(Q), D).unwrap();
        let rt = Ring::new(i128::from(Q_T), D).unwrap();
        let lift = |x: &Rq| Self::lift_in(&rc, x);
        let sigma = &pp.pp_sigma;
        let port = Self {
            v: lift(sigma.v()),
            b_u: lift(sigma.b_u()),
            b_r: [lift(&sigma.b_r()[0]), lift(&sigma.b_r()[1])],
            c0_rows: Vec::new(),
            sets: ParameterSets::load().unwrap(),
            pp_seed: pp.jali_pp_seed,
            rc: rc.clone(),
            rt,
        };
        Self {
            c0_rows: port.rows(&pp.c0),
            ..port
        }
    }

    /// `lift_c` (rel.rs:36-38): centred coefficients in the statement ring.
    fn lift_in(rc: &Arc<Ring>, x: &Rq) -> Poly {
        Poly::new(
            rc.clone(),
            x.coeffs()
                .iter()
                .map(|&v| centred(i128::from(v), i128::from(Q)))
                .collect(),
        )
        .unwrap()
    }

    pub fn lift(&self, x: &Rq) -> Poly {
        Self::lift_in(&self.rc, x)
    }

    /// The rows `σ(a_j)` of a tag matrix: centred modulo `q_t`, then `auto` (rel.rs:51).
    pub fn rows(&self, a: &TagMatrix) -> Vec<Poly> {
        a.rows()
            .map(|row| {
                Poly::new(
                    self.rt.clone(),
                    row.iter()
                        .map(|&x| centred(i128::from(x), i128::from(Q_T)))
                        .collect(),
                )
                .unwrap()
                .auto()
            })
            .collect()
    }

    /// rel.rs:61-65.
    fn declare_e(st: &mut Statement, name: &str) -> Result<(), jali::Error> {
        st.var_subring(
            name,
            E_COUNT,
            E_DEG,
            Norm::LinfExact(E_BOUND),
            Placement::Ajtai,
        )?;
        Ok(())
    }

    /// rel.rs:44-60: `ct(σ(a_j) usk + X^{-8 (j mod 128)} e_{⌊j/128⌋}) − γ T_j = 0` mod `q_t`.
    fn tag_clauses(
        &self,
        st: &mut Statement,
        e_name: &str,
        rows: &[Poly],
        tag: &[i128; M],
    ) -> Result<(), jali::Error> {
        let rt = &self.rt;
        for (j, (a, &tj)) in rows.iter().zip(tag).enumerate() {
            let clause = st
                .variable_in(rt, "usk", 0)?
                .scale(a)?
                .add(&st.coefficient_in(rt, e_name, j / E_DEG, j % E_DEG)?)?
                .add(&st.constant_in(Poly::constant(rt.clone(), -i128::from(GAMMA) * tj))?)?;
            st.const_coeff_zero(clause)?;
        }
        Ok(())
    }

    /// `R_att` (rel.rs:67-94) for `(h, b_φ φ, s, T)` with `s` in the BDLOP part.
    pub fn r_att(&self, h: &Rq, bphi_phi: &Rq, rows: &[Poly], tag: &[i128; M]) -> Statement {
        self.build_att(h, bphi_phi, rows, tag).unwrap()
    }

    fn build_att(
        &self,
        h: &Rq,
        bphi_phi: &Rq,
        rows: &[Poly],
        tag: &[i128; M],
    ) -> Result<Statement, jali::Error> {
        let rc = &self.rc;
        let mut st = Statement::new(rc.clone());
        st.var_placed("s", 2, Norm::L2Squared(S_BOUND), Placement::Bdlop)?;
        st.var("x1", 1, Norm::LinfExact(BETA_X))?;
        st.var("usk", 1, Norm::LinfExact(BETA_U))?;
        st.var("x0", 2, Norm::LinfExact(BETA_R))?;
        Self::declare_e(&mut st, "e")?;
        let a = [Poly::constant(rc.clone(), 1), self.lift(h)];
        let mut r = st.constant_in(Poly::zero(rc.clone()))?;
        for (i, a) in a.iter().enumerate() {
            r = r.add(&st.variable_in(rc, "s", i)?.scale(a)?)?;
        }
        r = r.add(&st.variable_in(rc, "usk", 0)?.scale(&self.b_u.neg())?)?;
        for (i, b) in self.b_r.iter().enumerate() {
            r = r.add(&st.variable_in(rc, "x0", i)?.scale(&b.neg())?)?;
        }
        r = r.add(&st.constant_in(self.lift(bphi_phi).neg())?)?;
        let g = st.constant_in(self.v.clone())?.add(
            &st.variable_in(rc, "x1", 0)?
                .scale(&Poly::constant(rc.clone(), -1))?,
        )?;
        let possession = r
            .product_affine(&g)?
            .add(&st.constant_in(Poly::constant(rc.clone(), -1))?)?;
        st.eq_mod_p(possession)?;
        self.tag_clauses(&mut st, "e", rows, tag)?;
        Ok(st)
    }

    /// `R_issue` (rel.rs:98-118) for `(C, (c_0, id), (s, T_0))`.
    pub fn r_issue(&self, c: &Rq, id: &[i128; M], s_rows: &[Poly], t0: &[i128; M]) -> Statement {
        self.build_issue(c, id, s_rows, t0).unwrap()
    }

    fn build_issue(
        &self,
        c: &Rq,
        id: &[i128; M],
        s_rows: &[Poly],
        t0: &[i128; M],
    ) -> Result<Statement, jali::Error> {
        let rc = &self.rc;
        let mut st = Statement::new(rc.clone());
        st.var("usk", 1, Norm::LinfExact(BETA_U))?;
        st.var("x0", 2, Norm::LinfExact(BETA_R))?;
        for name in ["e0", "e1"] {
            Self::declare_e(&mut st, name)?;
        }
        let mut com = st.variable_in(rc, "usk", 0)?.scale(&self.b_u)?;
        for (i, b) in self.b_r.iter().enumerate() {
            com = com.add(&st.variable_in(rc, "x0", i)?.scale(b)?)?;
        }
        com = com.add(&st.constant_in(self.lift(c).neg())?)?;
        st.eq_mod_p(com)?;
        self.tag_clauses(&mut st, "e0", &self.c0_rows, id)?;
        self.tag_clauses(&mut st, "e1", s_rows, t0)?;
        Ok(st)
    }

    fn poly(&self, c: &[i128]) -> Poly {
        Poly::new(self.rc.clone(), c.to_vec()).unwrap()
    }

    fn poly_i32(&self, c: &[i32]) -> Poly {
        Poly::new(self.rc.clone(), c.iter().map(|&x| i128::from(x)).collect()).unwrap()
    }

    /// `e_subring` (pcs.rs:145-153): `e_j` at coefficient `8 (j mod 128)` of element `⌊j/128⌋`.
    pub fn e_subring(&self, e: &[i8; M]) -> Vec<Poly> {
        let stride = D / E_DEG;
        let mut out = vec![vec![0i128; D]; E_COUNT];
        for (j, &x) in e.iter().enumerate() {
            out[j / E_DEG][stride * (j % E_DEG)] = i128::from(x);
        }
        out.into_iter().map(|c| self.poly(&c)).collect()
    }

    /// The witness of `R_att` (rel.rs:131-141) from integer coefficients.
    pub fn att_witness(
        &self,
        s: (&[i32], &[i32]),
        x1: &[i128],
        usk: &[i128],
        x0: [&[i128]; 2],
        e: &[i8; M],
    ) -> Witness {
        BTreeMap::from([
            (
                "s".to_string(),
                vec![self.poly_i32(s.0), self.poly_i32(s.1)],
            ),
            ("x1".to_string(), vec![self.poly(x1)]),
            ("usk".to_string(), vec![self.poly(usk)]),
            ("x0".to_string(), vec![self.poly(x0[0]), self.poly(x0[1])]),
            ("e".to_string(), self.e_subring(e)),
        ])
    }

    /// The honest witness of `R_att` for a holder: its credential, key and the error of its tag.
    pub fn att_witness_of(&self, usk: &UserSecretKey, cred: &Credential, e: &[i8; M]) -> Witness {
        self.att_witness(
            (cred.cred.s0(), cred.cred.s1()),
            &ints(cred.cred.x1()),
            &ints(usk.expose_ternary()),
            [&ints(&cred.x0[0]), &ints(&cred.x0[1])],
            e,
        )
    }

    /// The witness of `R_issue` (rel.rs:142-153).
    pub fn issue_witness(
        &self,
        usk: &[i128],
        x0: [&[i128]; 2],
        e0: &[i8; M],
        e1: &[i8; M],
    ) -> Witness {
        BTreeMap::from([
            ("usk".to_string(), vec![self.poly(usk)]),
            ("x0".to_string(), vec![self.poly(x0[0]), self.poly(x0[1])]),
            ("e0".to_string(), self.e_subring(e0)),
            ("e1".to_string(), self.e_subring(e1)),
        ])
    }

    /// The honest prover's witness check (`map_witness` of the compiled statement).
    pub fn check_witness(
        &self,
        st: &Statement,
        set: &TboxParams,
        w: &Witness,
    ) -> Result<(), jali::Error> {
        st.compile(set.clone())?.map_witness(w).map(|_| ())
    }

    /// Proves `st` for `w` under `ctx` with a fresh seed from `rng` (a restart is retried with a
    /// new seed, at most 3 times, as the library's seed bridge does).
    pub fn prove(
        &self,
        st: &Statement,
        set: &TboxParams,
        w: &Witness,
        ctx: &[u8],
        rng: &mut StdRng,
    ) -> Result<Vec<u8>, jali::Error> {
        let compiled = st.compile(set.clone())?;
        let mut last = jali::Error::RestartLimit;
        for _ in 0..3 {
            let mut seed = [0u8; 32];
            rng.fill_bytes(&mut seed);
            match compiled.prove_bytes_with_seed(self.pp_seed, w, ctx, seed) {
                Err(jali::Error::RestartLimit) => last = jali::Error::RestartLimit,
                result => return result,
            }
        }
        Err(last)
    }

    /// Verifies `proof` for `st` under `ctx`.
    pub fn verify(
        &self,
        st: &Statement,
        set: &TboxParams,
        proof: &[u8],
        ctx: &[u8],
    ) -> Result<(), jali::Error> {
        st.compile(set.clone())?
            .verify_bytes(self.pp_seed, proof, ctx)
    }
}

/// `ctx_j` as `docs/encodings.md` frames it, under any oracle suffix and with any `cred*` item:
/// with `"/LATTICE-CTX-ATT"` and an empty `cred*` it is [`LatticePCS::attestation_context`].
pub fn attestation_context_as(
    suffix: &[u8],
    pp_digest: &[u8; 32],
    hvk: &VSISVerificationKey,
    id: &LWRTag,
    phi: &BinaryPoly,
    tag: &LWRTag,
    cred_star: &[u8],
) -> [u8; 32] {
    let mut transcript = Transcript::new(suffix);
    transcript.append_bytes(b"pp", pp_digest);
    transcript.append_bytes(b"hvk", &hvk.h().to_bytes());
    transcript.append_bytes(b"id", &id.to_bytes());
    transcript.append_bytes(b"phi", phi.as_bytes());
    transcript.append_bytes(b"T", &tag.to_bytes());
    transcript.append_bytes(b"cred*", cred_star);
    transcript.digest()
}

// ---------------------------------------------------------------------------------------------
// The helper's trapdoor, for real preimages of arbitrary targets
// ---------------------------------------------------------------------------------------------

/// The NTRU trapdoor inside `hsk`, decoded and expanded by `ntru-trapdoor` itself.
pub struct Trapdoor {
    ek: ntru_trapdoor::ExpandedKey,
}

impl Trapdoor {
    /// The trapdoor of `hsk`: the first 5889 bytes of its encoding are `ntru-trapdoor`'s
    /// secret-key encoding (the `VSISSigningKey` layout: trapdoor ‖ 8-byte count).
    pub fn of(hsk: &HelperSecretKey<VSIS>) -> Self {
        let bytes = hsk.to_bytes().unwrap();
        let trapdoor_bytes = predicate_credential_system::cred::vsis::VSISSigningKey::BYTES - 8;
        let sk = ntru_trapdoor::SecretKey::from_bytes(
            &ntru_trapdoor::Params::PCS,
            &bytes[..trapdoor_bytes],
        )
        .unwrap();
        Self {
            ek: ntru_trapdoor::ExpandedKey::new(&sk).unwrap(),
        }
    }

    /// `s = (s_0, s_1) ← SampPre(td, t)` with a fresh seed: `s_0 + h s_1 = t`, `‖s‖² ≤ ⌊β_s²⌋`.
    pub fn preimage(&self, t: &Rq, rng: &mut StdRng) -> (Vec<i32>, Vec<i32>) {
        let t =
            ntru_trapdoor::RqPoly::from_coeffs(&ntru_trapdoor::Params::PCS, t.coeffs()).unwrap();
        let mut seed = [0u8; 32];
        rng.fill_bytes(&mut seed);
        let s = ntru_trapdoor::samp_pre(&self.ek, &t, &seed).unwrap();
        (s.s0.clone(), s.s1.clone())
    }
}
