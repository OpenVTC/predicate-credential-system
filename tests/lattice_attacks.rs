//! Attacks on the lattice construction (`LatticePCS`, feature `lattice`) by a CHEATING PROVER,
//! with ONE real helper key (an NTRU trapdoor) and real Jali proofs.
//!
//! The honest algorithms refuse to build most of these requests, so a verifier-side check is only
//! exercised by a prover that skips the honest checks. `lattice_support::Port` is that prover: an
//! independent port of the harness's statement builders, proving with Jali directly, under any
//! context. The control `the_cheating_provers_proofs_are_the_librarys` shows that its honest
//! proofs are accepted by the library and yield real credentials; each attack below then makes
//! a request whose proofs are VALID (checked with Jali) and shows which check of the box refuses
//! it, with which error:
//!
//! | attack | refused by |
//! |---|---|
//! | the `φ` forgery (credential-free witness, non-binary `φ`, bb:892) | no `BinaryPoly` carries it; presented with any binary `φ`: `InvalidProof`; inside `π`: `InvalidAttestation` |
//! | non-canonical tags `T + p e`, `id_{i→i} + p e` (bb:232) | unrepresentable; the proof is a proof for `T`, so it buys no second attester (`DuplicateAttester`) and no escape from self-exclusion (`SelfAttestation`) |
//! | duplicate attesters (fresh proofs, even under two credentials) | `DuplicateAttester` (deterministic tags, lem:tag-lwr-determinism) |
//! | a self attester | `SelfAttestation`; `π_0` binds `id_{i→i}` to the key (a false `id_{i→i}` has no witness) |
//! | the wrong `k` | `WrongAttestationCount`, `ZeroThreshold`, the decoders |
//! | wrong contexts and labels (deployment, oracle suffix, `cred*`, role, `f`, `hvk`, order) | `InvalidProof` |
//! | replayed and mixed proofs | `InvalidProof`, `InvalidKey`; reuse by the same recipient is ACCEPTED by design (rem:replay) |
//! | a non-canonical `C` or `h` | the decoders; a wiped `C`: `InvalidIssuanceEncoding` |
//! | a tampered credential | `VerifyCred`, `Unblind` (`InvalidPreCredential`), `Attest` (`WitnessDoesNotSatisfyRelation`) |
//! | the issuance cap | `IssuanceCapReached` after the last unit; refused requests consume nothing |
//!
//! The heavy tests share one fixture (two root members, a recipient with two attestations and an
//! issuance proof for `k = 2`; about 30 s) and are `#[ignore]`d. Run them in release, one at a
//! time: `RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_attacks -- --ignored --nocapture`.
//! The two light tests (no Jali proof) run in every `cargo test`.
#![cfg(feature = "lattice")]
#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

mod lattice_support;

use std::{sync::OnceLock, time::Instant};

use lattice_support::*;
use predicate_credential_system::{
    Error, LatticePCS,
    cred::{
        CredentialBase, VSIS,
        vsis::{VSISCredential, VSISHiddenMessage, VSISSigningKey, VSISVerificationKey},
    },
    jali::{math::Poly, params::TboxParams, statement::Statement},
    kiprf::lwr::{LWR, LWRTag},
    lattice::{BinaryPoly, D, M, P, Q, Q_MAX, Rq, Ternary},
    pcs::{
        HelperSecretKey, Predicate, PredicateCredentialSystem, SetupParams,
        lattice::{
            Attestation, Credential, IssuanceProof, IssuanceState, Proof, RootRequest,
            UserSecretKey,
        },
    },
    serialization::WireFormat,
};
use rand::{SeedableRng, rngs::StdRng};
use zeroize::Zeroize;

const LABEL: &[u8] = b"lattice-attacks";

/// One deployment, ONE helper key, the root members A and B (under `f_root`; the policy admits
/// `f_root` and `f`, not `f_other`), and a recipient R with the attestations A→R and B→R and an
/// honest issuance proof for `f = f_2`.
struct Fixture {
    pcs: Pcs,
    open: LatticePCS,
    port: Port,
    hvk: VSISVerificationKey,
    hsk: HelperSecretKey<VSIS>,
    f_root: Predicate,
    f_other: Predicate,
    f: Predicate,
    a: Member,
    b: Member,
    root_request_a: RootRequest,
    r: Member,
    atts: Vec<Attestation>,
    proof: IssuanceProof,
    state_bytes: Vec<u8>,
}

fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let t = Instant::now();
        let mut rng = StdRng::seed_from_u64(0xa77a_c000);
        let f_root = Predicate::root(b"founders".to_vec());
        let f_other = Predicate::root(b"others".to_vec());
        let f = Predicate::new(2, b"members".to_vec());
        let pcs = deployment(LABEL, &[&f_root, &f]);
        let (hvk, hsk) = pcs.helper_keygen(&mut rng);
        let mut a = Member::new(&pcs, "A", &mut rng);
        let mut b = Member::new(&pcs, "B", &mut rng);
        let root_request_a = root_issue(&pcs, &hvk, &hsk, &mut a, &f_root, &mut rng);
        root_issue(&pcs, &hvk, &hsk, &mut b, &f_root, &mut rng);
        let r = Member::new(&pcs, "R", &mut rng);
        let atts: Vec<Attestation> = [&a, &b]
            .iter()
            .map(|m| {
                pcs.attest(&hvk, &m.usk, m.f(), m.cred(), &r.id, &mut rng)
                    .unwrap()
            })
            .collect();
        let (proof, state) = pcs.prove(&hvk, &f, &r.id, &r.usk, &atts, &mut rng).unwrap();
        println!("fixture: {:.1} s", secs(t));
        Fixture {
            open: open_verifier(&pcs),
            port: Port::new(pcs.public_parameters()),
            state_bytes: state.to_bytes().unwrap().to_vec(),
            pcs,
            hvk,
            hsk,
            f_root,
            f_other,
            f,
            a,
            b,
            root_request_a,
            r,
            atts,
            proof,
        }
    })
}

impl Fixture {
    /// A copy of the helper key with its own counter.
    fn hsk(&self) -> HelperSecretKey<VSIS> {
        <HelperSecretKey<VSIS> as WireFormat>::from_bytes(&self.hsk.to_bytes().unwrap()).unwrap()
    }

    fn bphi(&self, phi: &BinaryPoly) -> Rq {
        self.pcs
            .public_parameters()
            .pp_sigma
            .b_phi()
            .mul(&phi.to_rq())
    }

    /// The attestation of `m` for `id` proven by the cheating prover with the HONEST witness,
    /// under the context `ctx(T, φ)` of its choice.
    fn port_attestation(
        &self,
        m: &Member,
        id: &LWRTag,
        ctx: impl Fn(&LWRTag, &BinaryPoly) -> [u8; 32],
        rng: &mut StdRng,
    ) -> Attestation {
        let s = self.pcs.tag_point(id);
        let (tag, e) = LWR.eval_with_error(m.usk.expose_ternary(), &s).unwrap();
        let phi = self.pcs.enc_pred(m.f());
        let st = self.port.r_att(
            self.hvk.h(),
            &self.bphi(&phi),
            &self.port.rows(&s),
            &tag_values(&tag),
        );
        let w = self.port.att_witness_of(&m.usk, m.cred(), e.entries());
        let proof = self
            .port
            .prove(&st, &self.port.sets.att, &w, &ctx(&tag, &phi), rng)
            .unwrap();
        Attestation {
            tag,
            phi,
            proof: Proof::from_bytes(proof).unwrap(),
        }
    }

    /// `st_iss = (usk ‖ x_0 ‖ φ)` for an opening.
    fn state(&self, usk: &UserSecretKey, x0: &[Ternary; 2], f: &Predicate) -> IssuanceState {
        let mut bytes = usk.to_bytes().unwrap().to_vec();
        bytes.extend_from_slice(&x0[0].to_bytes());
        bytes.extend_from_slice(&x0[1].to_bytes());
        bytes.extend_from_slice(self.pcs.enc_pred(f).as_bytes());
        IssuanceState::from_bytes(&bytes).unwrap()
    }
}

/// What a (cheating) prover of `R_issue` holds for a user: a fresh `x_0`, `C`, the honest tags
/// `id`, `id_{i→i}` with their rounding errors, and the rows of `s = H_0(id)`.
struct Opening {
    usk: Vec<i128>,
    x0: [Ternary; 2],
    c: Rq,
    id: LWRTag,
    t0: LWRTag,
    e0: [i8; M],
    e1: [i8; M],
    rows: Vec<Poly>,
}

impl Opening {
    fn new(fx: &Fixture, usk: &UserSecretKey, rng: &mut StdRng) -> Self {
        let pp = fx.pcs.public_parameters();
        let x0 = [Ternary::sample(rng), Ternary::sample(rng)];
        let c = commitment(
            &pp.pp_sigma,
            &usk.expose_ternary().to_rq(),
            [&x0[0].to_rq(), &x0[1].to_rq()],
        );
        let (id, e0) = LWR.eval_with_error(usk.expose_ternary(), &pp.c0).unwrap();
        let s = fx.pcs.tag_point(&id);
        let (t0, e1) = LWR.eval_with_error(usk.expose_ternary(), &s).unwrap();
        Self {
            usk: ints(usk.expose_ternary()),
            x0,
            c,
            id,
            t0,
            e0: *e0.entries(),
            e1: *e1.entries(),
            rows: fx.port.rows(&s),
        }
    }

    /// `R_issue` with raw tag values (so that a test can pass `T + p e`).
    fn statement(&self, port: &Port, id: &[i128; M], t0: &[i128; M]) -> Statement {
        port.r_issue(&self.c, id, &self.rows, t0)
    }

    fn honest_statement(&self, port: &Port) -> Statement {
        self.statement(port, &tag_values(&self.id), &tag_values(&self.t0))
    }

    fn witness(&self, port: &Port) -> Witness {
        port.issue_witness(
            &self.usk,
            [&ints(&self.x0[0]), &ints(&self.x0[1])],
            &self.e0,
            &self.e1,
        )
    }

    /// `π_0` for `st` under `ctx`, checked by Jali before it is returned.
    fn prove(
        &self,
        fx: &Fixture,
        st: &Statement,
        set: &TboxParams,
        ctx: &[u8],
        rng: &mut StdRng,
    ) -> Proof {
        let w = self.witness(&fx.port);
        let bytes = fx.port.prove(st, set, &w, ctx, rng).unwrap();
        assert_eq!(fx.port.verify(st, set, &bytes, ctx), Ok(()));
        Proof::from_bytes(bytes).unwrap()
    }

    /// `ctx_0` of this opening for `(hvk, f)` and an attestation list.
    fn ctx0(
        &self,
        fx: &Fixture,
        hvk: &VSISVerificationKey,
        f: &Predicate,
        atts: &[Attestation],
    ) -> [u8; 32] {
        fx.pcs
            .issuance_context(hvk, f, &self.id, &self.c, &self.t0, atts)
    }

    /// The honest statement proven under `ctx_0` over `atts` (the cheating prover's request: it
    /// skips `CheckAtts_P`).
    fn request(
        &self,
        fx: &Fixture,
        f: &Predicate,
        atts: &[Attestation],
        rng: &mut StdRng,
    ) -> IssuanceProof {
        let ctx = self.ctx0(fx, &fx.hvk, f, atts);
        let proof = self.prove(
            fx,
            &self.honest_statement(&fx.port),
            &fx.port.sets.issue,
            &ctx,
            rng,
        );
        self.issuance_proof(atts, proof)
    }

    fn issuance_proof(&self, atts: &[Attestation], proof: Proof) -> IssuanceProof {
        IssuanceProof {
            attestations: atts.to_vec(),
            c: self.c.clone(),
            t0: self.t0.clone(),
            proof,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The control
// ---------------------------------------------------------------------------------------------

/// The cheating prover's HONEST proofs are the library's: an attestation, an issuance proof and a
/// root request made by `Port` are accepted by `LatticePCS`, and the issuance and the root
/// request yield real credentials; the port verifies the library's own proofs. Every attack below
/// relies on this: what the library refuses there, it refuses for the attacked property alone.
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and about 35 s of Jali proofs (run in release)"]
fn the_cheating_provers_proofs_are_the_librarys() {
    let fx = fixture();
    let (pcs, hvk) = (&fx.pcs, &fx.hvk);
    let mut log = Log::new("control: the cheating prover");
    let mut rng = StdRng::seed_from_u64(0xa77a_c001);
    log.section("attestations");
    let att = fx.port_attestation(
        &fx.a,
        &fx.r.id,
        |t, phi| pcs.attestation_context(hvk, &fx.r.id, phi, t),
        &mut rng,
    );
    let att = wire_attestation(&att);
    log.ok(
        X,
        "the port's attestation A→R is accepted by VerifyProofAtt",
        pcs.check_attestation(hvk, &fx.r.id, &att),
    );
    log.holds(
        X,
        "its tag and φ are the library's (only the proof's coins differ)",
        att.tag == fx.atts[0].tag && att.phi == fx.atts[0].phi && att.proof != fx.atts[0].proof,
    );
    let s = pcs.tag_point(&fx.r.id);
    let st = fx.port.r_att(
        hvk.h(),
        &fx.bphi(&fx.atts[0].phi),
        &fx.port.rows(&s),
        &tag_values(&fx.atts[0].tag),
    );
    let ctx = pcs.attestation_context(hvk, &fx.r.id, &fx.atts[0].phi, &fx.atts[0].tag);
    log.ok_jali(
        X,
        "the port's R_att verifies the library's attestation A→R",
        fx.port
            .verify(&st, &fx.port.sets.att, fx.atts[0].proof.as_bytes(), &ctx),
    );

    log.section("issuance");
    let opening = Opening::new(fx, &fx.r.usk, &mut rng);
    let proof = opening.request(fx, &fx.f, &fx.atts, &mut rng);
    let proof = wire_issuance_proof(&proof, &fx.f);
    log.ok(
        X,
        "the port's issuance proof for R is accepted by VerifyProof",
        pcs.check_proof(hvk, &fx.f, &fx.r.id, &proof),
    );
    let hsk = fx.hsk();
    let pre = log.ok(
        X,
        "Issue answers it",
        pcs.issue(hvk, &hsk, &fx.f, &fx.r.id, &proof, &mut rng),
    );
    let state = fx.state(&fx.r.usk, &opening.x0, &fx.f);
    let cred = log.ok(
        X,
        "Unblind with the cheating prover's state",
        pcs.unblind(hvk, &fx.r.usk, &fx.f, &pre, &state),
    );
    log.holds(
        X,
        "a real credential",
        pcs.verify_cred(hvk, &fx.r.usk, &fx.f, &cred),
    );
    log.ok_jali(
        X,
        "the port's R_issue verifies the library's issuance proof",
        fx.port.verify(
            &fx.port.r_issue(
                &fx.proof.c,
                &tag_values(&fx.r.id),
                &fx.port.rows(&s),
                &tag_values(&fx.proof.t0),
            ),
            &fx.port.sets.issue,
            fx.proof.proof.as_bytes(),
            &pcs.issuance_context(hvk, &fx.f, &fx.r.id, &fx.proof.c, &fx.proof.t0, &fx.atts),
        ),
    );

    log.section("root path");
    let n = Member::new(pcs, "N", &mut rng);
    let opening = Opening::new(fx, &n.usk, &mut rng);
    let ctx = pcs.root_context(hvk, &fx.f_root, &n.id, &opening.c, &opening.t0);
    let proof = opening.prove(
        fx,
        &opening.honest_statement(&fx.port),
        &fx.port.sets.issue_root,
        &ctx,
        &mut rng,
    );
    let request = RootRequest {
        c: opening.c.clone(),
        t0: opening.t0.clone(),
        proof,
    };
    log.ok(
        X,
        "the port's root request is accepted",
        pcs.check_root_request(hvk, &fx.f_root, &n.id, &request),
    );
    let pre = log.ok(
        X,
        "issue_root answers it",
        pcs.issue_root(hvk, &hsk, &fx.f_root, &n.id, &request, &mut rng),
    );
    let state = fx.state(&n.usk, &opening.x0, &fx.f_root);
    let cred = pcs.unblind(hvk, &n.usk, &fx.f_root, &pre, &state).unwrap();
    log.holds(
        X,
        "a real root credential",
        pcs.verify_cred(hvk, &n.usk, &fx.f_root, &cred),
    );
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// The φ forgery
// ---------------------------------------------------------------------------------------------

/// The credential-free forgery of the proof of lem:base-vsis (bb:892): a user M WITHOUT a
/// credential takes `s = 0` and `b_φ φ* := −C(usk_M, x_0) − (v − x_1)^{-1}`, which satisfies the
/// possession clause, so Jali proves and verifies `R_att` for `φ*`. The check `φ ∈ M_pub`
/// (con:151) is what refuses it: `φ*` is not binary, no `BinaryPoly` carries it, and with any
/// binary `φ` in the attestation the verifier rebuilds another statement: `InvalidProof`; inside
/// an issuance request, the honest prover and the verifier (after a valid `π_0`) refuse it as an
/// attestation (`InvalidAttestation`), under any policy.
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and about 40 s of Jali proofs (run in release)"]
fn the_phi_forgery_needs_a_non_binary_phi() {
    let fx = fixture();
    let (pcs, hvk) = (&fx.pcs, &fx.hvk);
    let sigma = &pcs.public_parameters().pp_sigma;
    let mut log = Log::new("the φ forgery");
    let mut rng = StdRng::seed_from_u64(0xa77a_c002);
    let m = Member::new(pcs, "M", &mut rng); // no credential
    let x0 = [Ternary::sample(&mut rng), Ternary::sample(&mut rng)];
    let x1 = Ternary::sample(&mut rng);
    let s = pcs.tag_point(&fx.r.id);
    let (tag, e) = LWR.eval_with_error(m.usk.expose_ternary(), &s).unwrap();
    let y = sigma.v().sub(&x1.to_rq()).inverse().unwrap();
    let bphi_forged = commitment(
        sigma,
        &m.usk.expose_ternary().to_rq(),
        [&x0[0].to_rq(), &x0[1].to_rq()],
    )
    .neg()
    .sub(&y);
    let st = fx
        .port
        .r_att(hvk.h(), &bphi_forged, &fx.port.rows(&s), &tag_values(&tag));
    let zero = vec![0i32; D];
    let w = fx.port.att_witness(
        (&zero, &zero),
        &ints(&x1),
        &ints(m.usk.expose_ternary()),
        [&ints(&x0[0]), &ints(&x0[1])],
        e.entries(),
    );
    log.section("the relation alone");
    log.ok_jali(
        X,
        "s = 0 is a witness of R_att for φ* (no credential)",
        fx.port.check_witness(&st, &fx.port.sets.att, &w),
    );
    let phi_root = pcs.enc_pred(&fx.f_root);
    let ctx = pcs.attestation_context(hvk, &fx.r.id, &phi_root, &tag);
    let forged = fx
        .port
        .prove(&st, &fx.port.sets.att, &w, &ctx, &mut rng)
        .unwrap();
    log.ok_jali(
        X,
        "Jali proves and verifies the forgery",
        fx.port.verify(&st, &fx.port.sets.att, &forged, &ctx),
    );
    let phi_star = sigma.b_phi().inverse().unwrap().mul(&bphi_forged);
    let binary_coefficients = phi_star.coeffs().iter().filter(|&&x| x <= 1).count();
    log.holds(
        X,
        &format!("φ* is not binary ({binary_coefficients} of 1024 coefficients in {{0, 1}})"),
        binary_coefficients < 8,
    );

    log.section("the construction");
    let parity: Vec<u8> = phi_star
        .coeffs()
        .iter()
        .map(|&x| u8::try_from(x % 2).unwrap())
        .collect();
    for (phi, what) in [(phi_root, "φ_root"), (binary(&parity), "φ* mod 2")] {
        let att = Attestation {
            tag: tag.clone(),
            phi,
            proof: Proof::from_bytes(forged.clone()).unwrap(),
        };
        log.refused(
            X,
            &format!("VerifyProofAtt refuses the forgery presented with {what}"),
            pcs.check_attestation(hvk, &fx.r.id, &att),
            Error::InvalidProof,
        );
    }
    let forged_att = Attestation {
        tag,
        phi: phi_root,
        proof: Proof::from_bytes(forged).unwrap(),
    };
    let list = [fx.atts[0].clone(), forged_att];
    log.refused(
        X,
        "Prove refuses it in w (CheckAtts_P)",
        pcs.prove(hvk, &fx.f, &fx.r.id, &fx.r.usk, &list, &mut rng),
        Error::InvalidAttestation,
    );
    let request = Opening::new(fx, &fx.r.usk, &mut rng).request(fx, &fx.f, &list, &mut rng);
    log.refused(
        X,
        "VerifyProof refuses it after a valid π_0 (InvalidAttestation)",
        pcs.check_proof(hvk, &fx.f, &fx.r.id, &request),
        Error::InvalidAttestation,
    );
    log.refused(
        X,
        "... and so does a verifier with P ≡ 1",
        fx.open.check_proof(hvk, &fx.f, &fx.r.id, &request),
        Error::InvalidAttestation,
    );
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// Non-canonical tags
// ---------------------------------------------------------------------------------------------

/// bb:232, con:171: a non-canonical tag `T + p e` has exactly the witnesses of `T`, and a proof
/// for it is a proof for `T`. The tags of this crate cannot carry `T + p e` (`u16` entries,
/// `p = 2^16`), so what such a proof buys is the canonical `T`: no second attester tag next to the
/// attester's own (`DuplicateAttester`), and no self-exclusion tag other than the real one
/// (`SelfAttestation`).
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and about 40 s of Jali proofs (run in release)"]
fn non_canonical_tags_buy_nothing() {
    let fx = fixture();
    let (pcs, hvk) = (&fx.pcs, &fx.hvk);
    let mut log = Log::new("non-canonical tags");
    let mut rng = StdRng::seed_from_u64(0xa77a_c003);
    log.section("encodings");
    log.holds(
        X,
        "every 336-byte string is ONE canonical tag (entries below p) and re-encodes to itself",
        (0..64u8).all(|i| {
            let bytes = [i.wrapping_mul(37) ^ 0xa5; LWRTag::BYTES];
            LWRTag::from_bytes(&bytes).is_ok_and(|t| {
                t.to_bytes() == bytes && t.entries().iter().all(|&x| u32::from(x) < P)
            })
        }),
    );
    log.holds(
        X,
        "T + p does not fit an entry: the u16 entry of T + p IS T",
        fx.atts[0]
            .tag
            .entries()
            .iter()
            .all(|&x| u16::try_from(u32::from(x) + P).is_err()),
    );

    log.section("an attester tag T + p e");
    let s = pcs.tag_point(&fx.r.id);
    let rows = fx.port.rows(&s);
    let (tag_a, e_a) = LWR.eval_with_error(fx.a.usk.expose_ternary(), &s).unwrap();
    let phi_root = pcs.enc_pred(&fx.f_root);
    let canonical = fx
        .port
        .r_att(hvk.h(), &fx.bphi(&phi_root), &rows, &tag_values(&tag_a));
    let mut lifted = tag_values(&tag_a);
    lifted[0] += i128::from(P);
    lifted[150] += 2 * i128::from(P); // a row of the second subring element, z = 2
    let st_lifted = fx.port.r_att(hvk.h(), &fx.bphi(&phi_root), &rows, &lifted);
    let w = fx
        .port
        .att_witness_of(&fx.a.usk, fx.a.cred(), e_a.entries());
    let ctx = pcs.attestation_context(hvk, &fx.r.id, &phi_root, &tag_a);
    let proof = fx
        .port
        .prove(&st_lifted, &fx.port.sets.att, &w, &ctx, &mut rng)
        .unwrap();
    log.ok_jali(
        X,
        "Jali proves and verifies R_att for T + p e (rows 0 and 150)",
        fx.port.verify(&st_lifted, &fx.port.sets.att, &proof, &ctx),
    );
    log.ok_jali(
        X,
        "the same proof verifies for the canonical T",
        fx.port.verify(&canonical, &fx.port.sets.att, &proof, &ctx),
    );
    let second = Attestation {
        tag: tag_a,
        phi: phi_root,
        proof: Proof::from_bytes(proof).unwrap(),
    };
    log.ok(
        X,
        "presented (T is its only encoding), it is A's attestation for R",
        pcs.check_attestation(hvk, &fx.r.id, &second),
    );
    let list = [fx.atts[0].clone(), second];
    log.refused(
        X,
        "with A's own attestation, Prove refuses it (DuplicateAttester)",
        pcs.prove(hvk, &fx.f, &fx.r.id, &fx.r.usk, &list, &mut rng),
        Error::DuplicateAttester,
    );
    let request = Opening::new(fx, &fx.r.usk, &mut rng).request(fx, &fx.f, &list, &mut rng);
    log.refused(
        X,
        "... and so does VerifyProof after a valid π_0",
        pcs.check_proof(hvk, &fx.f, &fx.r.id, &request),
        Error::DuplicateAttester,
    );

    log.section("a self-exclusion tag id_{i→i} + p e");
    // A collects a self-attestation and B's attestation, and shifts its id_{i→i} by p to escape
    // the self-exclusion check
    let att_aa = fx
        .pcs
        .attest(hvk, &fx.a.usk, fx.a.f(), fx.a.cred(), &fx.a.id, &mut rng)
        .unwrap();
    let att_ba = fx
        .pcs
        .attest(hvk, &fx.b.usk, fx.b.f(), fx.b.cred(), &fx.a.id, &mut rng)
        .unwrap();
    let list = [att_aa, att_ba];
    let opening = Opening::new(fx, &fx.a.usk, &mut rng);
    log.holds(
        X,
        "A's id_{i→i} is the tag of its self-attestation",
        opening.t0 == list[0].tag,
    );
    let mut t0_lifted = tag_values(&opening.t0);
    t0_lifted[0] += i128::from(P);
    let st = opening.statement(&fx.port, &tag_values(&opening.id), &t0_lifted);
    let ctx = opening.ctx0(fx, hvk, &fx.f, &list);
    let proof = opening.prove(fx, &st, &fx.port.sets.issue, &ctx, &mut rng);
    log.ok_jali(
        X,
        "π_0 for id_{i→i} + p e_0 verifies for the canonical id_{i→i} too",
        fx.port.verify(
            &opening.honest_statement(&fx.port),
            &fx.port.sets.issue,
            proof.as_bytes(),
            &ctx,
        ),
    );
    log.refused(
        X,
        "presented (id_{i→i} is its only encoding), the request is a self-attestation",
        pcs.check_proof(hvk, &fx.f, &fx.a.id, &opening.issuance_proof(&list, proof)),
        Error::SelfAttestation,
    );

    log.section("an identifier id + p e");
    let opening = Opening::new(fx, &fx.r.usk, &mut rng);
    let mut id_lifted = tag_values(&opening.id);
    id_lifted[7] += i128::from(P);
    let st = opening.statement(&fx.port, &id_lifted, &tag_values(&opening.t0));
    let ctx = opening.ctx0(fx, hvk, &fx.f, &fx.atts);
    let proof = opening.prove(fx, &st, &fx.port.sets.issue, &ctx, &mut rng);
    log.ok_jali(
        X,
        "π_0 for id + p e verifies for the canonical id: one key, one identifier, one attester point H_0(id)",
        fx.port.verify(
            &opening.honest_statement(&fx.port),
            &fx.port.sets.issue,
            proof.as_bytes(),
            &ctx,
        ),
    );
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// Duplicate attesters and self-attestation
// ---------------------------------------------------------------------------------------------

/// One key is one attester (lem:tag-lwr-determinism): a second attestation of A for R with fresh
/// coins, and one under a second credential of A (another label), have A's tag, so with A's first
/// attestation they are refused (`DuplicateAttester`) by the honest prover and, after a valid
/// `π_0`, by the verifier, also under `P ≡ 1`.
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and about 30 s of Jali proofs (run in release)"]
fn duplicate_attesters_are_one_attester() {
    let fx = fixture();
    let (pcs, hvk) = (&fx.pcs, &fx.hvk);
    let mut log = Log::new("duplicate attesters");
    log.section("A attests for R twice");
    let mut rng = StdRng::seed_from_u64(0xa77a_c004);
    let again = pcs
        .attest(hvk, &fx.a.usk, fx.a.f(), fx.a.cred(), &fx.r.id, &mut rng)
        .unwrap();
    log.ok(
        X,
        "A's second attestation for R verifies",
        pcs.check_attestation(hvk, &fx.r.id, &again),
    );
    log.holds(
        X,
        "fresh coins: another proof, the same tag",
        again.proof != fx.atts[0].proof && again.tag == fx.atts[0].tag,
    );
    let list = [fx.atts[0].clone(), again];
    log.refused(
        X,
        "Prove refuses the pair",
        pcs.prove(hvk, &fx.f, &fx.r.id, &fx.r.usk, &list, &mut rng),
        Error::DuplicateAttester,
    );
    let request = Opening::new(fx, &fx.r.usk, &mut rng).request(fx, &fx.f, &list, &mut rng);
    log.refused(
        X,
        "VerifyProof refuses it after a valid π_0",
        pcs.check_proof(hvk, &fx.f, &fx.r.id, &request),
        Error::DuplicateAttester,
    );
    log.refused(
        X,
        "... also under P ≡ 1",
        fx.open.check_proof(hvk, &fx.f, &fx.r.id, &request),
        Error::DuplicateAttester,
    );
    // A obtains a second credential (another root label) and attests with it
    let hsk = fx.hsk();
    let mut a2 = Member {
        name: "A (second credential)".into(),
        id: fx.a.id.clone(),
        usk: UserSecretKey::from_ternary(fx.a.usk.expose_ternary().clone()),
        cred: None,
        f: None,
    };
    root_issue(pcs, hvk, &hsk, &mut a2, &fx.f_other, &mut rng);
    let other_label = pcs
        .attest(hvk, &a2.usk, a2.f(), a2.cred(), &fx.r.id, &mut rng)
        .unwrap();
    log.ok(
        X,
        "A's attestation under its second credential verifies",
        pcs.check_attestation(hvk, &fx.r.id, &other_label),
    );
    log.holds(
        X,
        "another label, the same tag: the tag depends on (usk_A, id_R) only",
        other_label.phi != fx.atts[0].phi && other_label.tag == fx.atts[0].tag,
    );
    let list = [fx.atts[0].clone(), other_label];
    log.refused(
        X,
        "Prove refuses the pair under P ≡ 1 too",
        fx.open
            .prove(hvk, &fx.f, &fx.r.id, &fx.r.usk, &list, &mut rng),
        Error::DuplicateAttester,
    );
    let request = Opening::new(fx, &fx.r.usk, &mut rng).request(fx, &fx.f, &list, &mut rng);
    log.refused(
        X,
        "VerifyProof (P ≡ 1) refuses it after a valid π_0",
        fx.open.check_proof(hvk, &fx.f, &fx.r.id, &request),
        Error::DuplicateAttester,
    );
    log.finish(0);
}

/// rem:selfexcl: R, once credentialed, endorses itself. Its self-attestation verifies, but its tag
/// IS `id_{i→i}`, so the honest prover and the verifier (after a valid `π_0`, under any policy)
/// refuse it (`SelfAttestation`). A false `id_{i→i}` has no witness: `π_0` binds it to `usk`.
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and about 20 s of Jali proofs (run in release)"]
fn a_self_attester_is_refused() {
    let fx = fixture();
    let (pcs, hvk) = (&fx.pcs, &fx.hvk);
    let mut log = Log::new("self-attestation");
    log.section("R endorses itself");
    let mut rng = StdRng::seed_from_u64(0xa77a_c005);
    let hsk = fx.hsk();
    let pre = pcs
        .issue(hvk, &hsk, &fx.f, &fx.r.id, &fx.proof, &mut rng)
        .unwrap();
    let state = IssuanceState::from_bytes(&fx.state_bytes).unwrap();
    let cred = pcs.unblind(hvk, &fx.r.usk, &fx.f, &pre, &state).unwrap();
    let selfie = pcs
        .attest(hvk, &fx.r.usk, &fx.f, &cred, &fx.r.id, &mut rng)
        .unwrap();
    log.ok(
        X,
        "R's self-attestation verifies on its own",
        pcs.check_attestation(hvk, &fx.r.id, &selfie),
    );
    log.holds(X, "its tag is R's id_{i→i}", selfie.tag == fx.proof.t0);
    let list = [fx.atts[0].clone(), selfie];
    log.refused(
        X,
        "Prove refuses it",
        pcs.prove(hvk, &fx.f, &fx.r.id, &fx.r.usk, &list, &mut rng),
        Error::SelfAttestation,
    );
    let opening = Opening::new(fx, &fx.r.usk, &mut rng);
    let request = opening.request(fx, &fx.f, &list, &mut rng);
    log.refused(
        X,
        "VerifyProof refuses it after a valid π_0",
        pcs.check_proof(hvk, &fx.f, &fx.r.id, &request),
        Error::SelfAttestation,
    );
    log.refused(
        X,
        "... also under P ≡ 1",
        fx.open.check_proof(hvk, &fx.f, &fx.r.id, &request),
        Error::SelfAttestation,
    );
    // dodging the check with another id_{i→i}: the statement then has no witness
    let w = opening.witness(&fx.port);
    for (t0, what) in [
        (bump(&opening.t0, 0), "id_{i→i} + 1 in one row"),
        (fx.atts[1].tag.clone(), "B's tag at s_R"),
    ] {
        let st = opening.statement(&fx.port, &tag_values(&opening.id), &tag_values(&t0));
        log.witness(
            X,
            &format!("π_0 with a false id_{{i→i}} ({what}) has no witness"),
            fx.port.check_witness(&st, &fx.port.sets.issue, &w),
        );
    }
    // T_0 + 1 satisfies the clause with e + γ, which is outside the exact bound 7
    let mut e1 = opening.e1;
    e1[0] = i8::try_from(i32::from(e1[0]) + 15).unwrap();
    assert!(e1[0] > 7);
    let w = fx.port.issue_witness(
        &opening.usk,
        [&ints(&opening.x0[0]), &ints(&opening.x0[1])],
        &opening.e0,
        &e1,
    );
    let st = opening.statement(
        &fx.port,
        &tag_values(&opening.id),
        &tag_values(&bump(&opening.t0, 0)),
    );
    log.witness(
        X,
        "... nor with the error moved by γ (|e| > 7: the exact bound)",
        fx.port.check_witness(&st, &fx.port.sets.issue, &w),
    );
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// The wrong k
// ---------------------------------------------------------------------------------------------

/// `VerifyProof` compares the number of attestations with the threshold of `f_k` (con:194):
/// a proof with `k ± 1` attestations, for a root predicate or for an absurd threshold is refused
/// before any proof is looked at, and its encoding does not decode for another `k`.
#[test]
#[ignore = "heavy: the shared fixture (about 30 s); the checks themselves need no proof"]
fn the_wrong_k_is_refused() {
    let fx = fixture();
    let (pcs, hvk, proof) = (&fx.pcs, &fx.hvk, &fx.proof);
    let mut log = Log::new("the wrong k");
    log.section("R's proof for f_2 checked for other thresholds");
    let mut rng = StdRng::seed_from_u64(0xa77a_c006);
    let f1 = Predicate::new(1, b"members".to_vec());
    let f3 = Predicate::new(3, b"members".to_vec());
    let huge = Predicate::new(u32::MAX, b"members".to_vec());
    for (f, expected) in [
        (&f1, 1usize),
        (&f3, 3),
        (&huge, usize::try_from(u32::MAX).unwrap()),
    ] {
        log.refused(
            X,
            &format!("VerifyProof for k = {expected} with 2 attestations"),
            pcs.check_proof(hvk, f, &fx.r.id, proof),
            Error::WrongAttestationCount {
                expected,
                actual: 2,
            },
        );
    }
    log.refused(
        X,
        "VerifyProof for a root predicate",
        pcs.check_proof(hvk, &fx.f_root, &fx.r.id, proof),
        Error::ZeroThreshold,
    );
    let mut fewer = proof.clone();
    fewer.attestations.pop();
    log.refused(
        X,
        "VerifyProof for k = 2 with 1 attestation",
        pcs.check_proof(hvk, &fx.f, &fx.r.id, &fewer),
        Error::WrongAttestationCount {
            expected: 2,
            actual: 1,
        },
    );
    let mut more = proof.clone();
    more.attestations.push(fx.atts[0].clone());
    log.refused(
        X,
        "VerifyProof for k = 2 with 3 attestations",
        pcs.check_proof(hvk, &fx.f, &fx.r.id, &more),
        Error::WrongAttestationCount {
            expected: 2,
            actual: 3,
        },
    );
    log.refused(
        X,
        "Prove for k = 2 with 1 attestation",
        pcs.prove(hvk, &fx.f, &fx.r.id, &fx.r.usk, &fx.atts[..1], &mut rng),
        Error::WrongAttestationCount {
            expected: 2,
            actual: 1,
        },
    );
    let hsk = fx.hsk();
    log.refused(
        X,
        "Issue for k = 3 (any VerifyProof failure is InvalidProof for the helper)",
        pcs.issue(hvk, &hsk, &f3, &fx.r.id, proof, &mut rng),
        Error::InvalidProof,
    );
    log.holds(
        X,
        "... and nothing was issued",
        hsk.signing_key().issued() == fx.hsk.signing_key().issued(),
    );
    let compact = proof.to_compact_bytes().unwrap();
    log.holds(
        X,
        "the compact encoding decodes for k = 2 only (k = 1, 3 and 2^32 − 1 fail, the last one fast)",
        IssuanceProof::from_compact_bytes(&compact, &fx.f).is_ok()
            && IssuanceProof::from_compact_bytes(&compact, &f1).is_err()
            && IssuanceProof::from_compact_bytes(&compact, &f3).is_err()
            && IssuanceProof::from_compact_bytes(&compact, &huge).is_err(),
    );
    log.refused(
        X,
        "no compact issuance proof for a root predicate",
        IssuanceProof::from_compact_bytes(&compact, &fx.f_root),
        Error::ZeroThreshold,
    );
    let mut canonical = WireFormat::to_bytes(proof).unwrap();
    for k in [1u32, 3, u32::MAX] {
        canonical[..4].copy_from_slice(&k.to_le_bytes());
        log.holds(
            X,
            &format!("the canonical encoding with LE32(k) = {k} does not decode"),
            <IssuanceProof as WireFormat>::from_bytes(&canonical).is_err(),
        );
    }
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// Wrong contexts and labels
// ---------------------------------------------------------------------------------------------

/// Proofs made with the HONEST witness but under a context other than the one the verifier
/// rebuilds are refused (`InvalidProof`): an attestation under another deployment's `ctx_j`,
/// under another oracle's label, with a non-empty `cred*`, or under the recipient's `ctx_root`;
/// an issuance proof under `ctx_root`, for another `f` with the same threshold, under another
/// `hvk`, or over the attestations in another order; a root request under the issuance oracle or
/// another deployment's `ctx_root`. Under its own context each of them is accepted (the order
/// of the attestations is bound, not prescribed).
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and about 75 s of Jali proofs (run in release)"]
fn proofs_under_wrong_contexts_and_labels_are_refused() {
    let fx = fixture();
    let (pcs, hvk) = (&fx.pcs, &fx.hvk);
    let mut log = Log::new("wrong contexts and labels");
    let mut rng = StdRng::seed_from_u64(0xa77a_c007);
    let elsewhere =
        LatticePCS::setup(SetupParams::new(b"lattice-attacks/elsewhere".to_vec())).unwrap();
    let pp_digest = *pcs.parameters_digest();
    let id_r = &fx.r.id;

    log.section("attestations A→R");
    let opening = Opening::new(fx, &fx.r.usk, &mut rng); // R's request, for the ctx_root case
    type Ctx<'a> = Box<dyn Fn(&LWRTag, &BinaryPoly) -> [u8; 32] + 'a>;
    let cases: [(&str, Ctx<'_>); 4] = [
        (
            "ctx_j of another deployment",
            Box::new(|t, phi| elsewhere.attestation_context(hvk, id_r, phi, t)),
        ),
        (
            "ctx_j's items under the label of ctx_0 (/LATTICE-CTX-ISSUE)",
            Box::new(|t, phi| {
                attestation_context_as(b"/LATTICE-CTX-ISSUE", &pp_digest, hvk, id_r, phi, t, b"")
            }),
        ),
        (
            "ctx_j with a non-empty cred*",
            Box::new(|t, phi| {
                attestation_context_as(b"/LATTICE-CTX-ATT", &pp_digest, hvk, id_r, phi, t, &[0])
            }),
        ),
        (
            "the recipient's ctx_root",
            Box::new(|_, _| pcs.root_context(hvk, &fx.f_root, id_r, &opening.c, &opening.t0)),
        ),
    ];
    for (what, ctx) in cases {
        let att = fx.port_attestation(&fx.a, id_r, ctx, &mut rng);
        log.refused(
            X,
            &format!("an attestation proven under {what}"),
            pcs.check_attestation(hvk, id_r, &att),
            Error::InvalidProof,
        );
    }

    log.section("issuance proofs for R");
    let (hvk2, _) = pcs.helper_keygen(&mut rng);
    let f_b = Predicate::new(2, b"members-b".to_vec());
    let honest = opening.honest_statement(&fx.port);
    let swapped = [fx.atts[1].clone(), fx.atts[0].clone()];
    let set = &fx.port.sets.issue;
    let wrong: [(&str, [u8; 32]); 4] = [
        (
            "ctx_root (the root role)",
            pcs.root_context(hvk, &fx.f_root, id_r, &opening.c, &opening.t0),
        ),
        (
            "ctx_0 for another f with the same threshold",
            opening.ctx0(fx, hvk, &f_b, &fx.atts),
        ),
        (
            "ctx_0 under another hvk",
            opening.ctx0(fx, &hvk2, &fx.f, &fx.atts),
        ),
        (
            "ctx_0 over the attestations in another order",
            opening.ctx0(fx, hvk, &fx.f, &swapped),
        ),
    ];
    for (what, ctx) in wrong {
        let proof = opening.prove(fx, &honest, set, &ctx, &mut rng);
        log.refused(
            X,
            &format!("π_0 proven under {what}"),
            pcs.check_proof(hvk, &fx.f, id_r, &opening.issuance_proof(&fx.atts, proof)),
            Error::InvalidProof,
        );
    }
    let proof = opening.prove(
        fx,
        &honest,
        set,
        &opening.ctx0(fx, hvk, &fx.f, &swapped),
        &mut rng,
    );
    log.ok(
        X,
        "control: the attestations in another order, with the π_0 for that order, are accepted",
        pcs.check_proof(hvk, &fx.f, id_r, &opening.issuance_proof(&swapped, proof)),
    );

    log.section("root requests");
    let n = Member::new(pcs, "N", &mut rng);
    let opening = Opening::new(fx, &n.usk, &mut rng);
    let honest = opening.honest_statement(&fx.port);
    let root_set = &fx.port.sets.issue_root;
    let wrong: [(&str, [u8; 32]); 2] = [
        (
            "the issuance oracle (ctx_0 with no attestation)",
            opening.ctx0(fx, hvk, &fx.f_root, &[]),
        ),
        (
            "ctx_root of another deployment",
            elsewhere.root_context(hvk, &fx.f_root, &n.id, &opening.c, &opening.t0),
        ),
    ];
    for (what, ctx) in wrong {
        let proof = opening.prove(fx, &honest, root_set, &ctx, &mut rng);
        let request = RootRequest {
            c: opening.c.clone(),
            t0: opening.t0.clone(),
            proof,
        };
        log.refused(
            X,
            &format!("a root request proven under {what}"),
            pcs.check_root_request(hvk, &fx.f_root, &n.id, &request),
            Error::InvalidProof,
        );
    }
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// Replays and mixes
// ---------------------------------------------------------------------------------------------

/// Replays and mixes of honest proofs: an attestation for another recipient, the parts of two
/// requests of one recipient, a request for another identifier or in another deployment (where
/// the policy already refuses the labels, `EncPred` being per deployment, and a `P ≡ 1` verifier
/// refuses `π_0`), a root request for another identifier or root label, are refused. Two replays are ACCEPTED by
/// design: the recipient's attestations reused for another predicate (rem:replay, "standing
/// endorsements"), and the same request issued twice (the helper is stateless; each `BlindIssue`
/// samples a fresh `x_1`, so the two preimages are for two targets).
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and about 55 s of Jali proofs (run in release)"]
fn replayed_and_mixed_proofs() {
    let fx = fixture();
    let (pcs, hvk, proof) = (&fx.pcs, &fx.hvk, &fx.proof);
    let mut log = Log::new("replays and mixes");
    let mut rng = StdRng::seed_from_u64(0xa77a_c008);
    log.section("refused");
    log.refused(
        X,
        "A's attestation for R presented for B",
        pcs.check_attestation(hvk, &fx.b.id, &fx.atts[0]),
        Error::InvalidProof,
    );
    let (second, _) = pcs
        .prove(hvk, &fx.f, &fx.r.id, &fx.r.usk, &fx.atts, &mut rng)
        .unwrap();
    log.holds(
        X,
        "R's second request: another C (fresh x_0), the same id_{i→i}",
        second.c != proof.c && second.t0 == proof.t0,
    );
    log.refused(
        X,
        "C of the first request with π_0 of the second",
        pcs.check_proof(
            hvk,
            &fx.f,
            &fx.r.id,
            &IssuanceProof {
                proof: second.proof.clone(),
                ..proof.clone()
            },
        ),
        Error::InvalidProof,
    );
    log.refused(
        X,
        "C of the second request with π_0 of the first",
        pcs.check_proof(
            hvk,
            &fx.f,
            &fx.r.id,
            &IssuanceProof {
                proof: proof.proof.clone(),
                ..second.clone()
            },
        ),
        Error::InvalidProof,
    );
    log.refused(
        X,
        "R's request presented for B",
        pcs.check_proof(hvk, &fx.f, &fx.b.id, proof),
        Error::InvalidProof,
    );
    let elsewhere = deployment(b"lattice-attacks/elsewhere", &[&fx.f_root, &fx.f]);
    log.refused(
        X,
        "R's request in another deployment: its allow list does not admit this deployment's φ_root (EncPred depends on the label)",
        elsewhere.check_proof(hvk, &fx.f, &fx.r.id, proof),
        Error::PolicyRejected,
    );
    log.refused(
        X,
        "... and with P ≡ 1 there, π_0 does not verify under the other ctx_0 (pp leads every context)",
        open_verifier(&elsewhere).check_proof(hvk, &fx.f, &fx.r.id, proof),
        Error::InvalidProof,
    );
    log.refused(
        X,
        "the helper key of this deployment does not issue in another one",
        elsewhere.issue(hvk, &fx.hsk(), &fx.f, &fx.r.id, proof, &mut rng),
        Error::InvalidKey,
    );
    log.refused(
        X,
        "A's root request presented for B",
        pcs.check_root_request(hvk, &fx.f_root, &fx.b.id, &fx.root_request_a),
        Error::InvalidProof,
    );
    log.refused(
        X,
        "A's root request under another root label",
        pcs.check_root_request(hvk, &fx.f_other, &fx.a.id, &fx.root_request_a),
        Error::InvalidProof,
    );

    log.section("accepted by design");
    let f_b = Predicate::new(2, b"members-b".to_vec());
    let (reuse, state) = pcs
        .prove(hvk, &f_b, &fx.r.id, &fx.r.usk, &fx.atts, &mut rng)
        .unwrap();
    log.ok(
        X,
        "rem:replay: R's attestations reused for another predicate f_b",
        pcs.check_proof(hvk, &f_b, &fx.r.id, &reuse),
    );
    let hsk = fx.hsk();
    let pre = pcs
        .issue(hvk, &hsk, &f_b, &fx.r.id, &reuse, &mut rng)
        .unwrap();
    let cred = pcs.unblind(hvk, &fx.r.usk, &f_b, &pre, &state).unwrap();
    log.holds(
        X,
        "... and the credential for f_b is real",
        pcs.verify_cred(hvk, &fx.r.usk, &f_b, &cred),
    );
    let before = hsk.signing_key().issued();
    let pre1 = pcs
        .issue(hvk, &hsk, &fx.f, &fx.r.id, proof, &mut rng)
        .unwrap();
    let pre2 = pcs
        .issue(hvk, &hsk, &fx.f, &fx.r.id, proof, &mut rng)
        .unwrap();
    log.holds(
        X,
        "the same request issued twice: two preimages for two targets (fresh x_1), two units of the cap",
        pre1.x1() != pre2.x1() && pre1.s0() != pre2.s0() && hsk.signing_key().issued() == before + 2,
    );
    for pre in [pre1, pre2] {
        let state = IssuanceState::from_bytes(&fx.state_bytes).unwrap();
        let cred = pcs.unblind(hvk, &fx.r.usk, &fx.f, &pre, &state).unwrap();
        log.holds(
            X,
            "... and both unblind to real credentials",
            pcs.verify_cred(hvk, &fx.r.usk, &fx.f, &cred),
        );
    }
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// The issuance cap
// ---------------------------------------------------------------------------------------------

/// The cap `Q_max = 2^48` (con:220-221) is a constant of the crate, so a SMALL cap is emulated by
/// a helper key restored with 2 units left (`Q_max − 2` issued). `Issue` and `issue_root` share
/// the count; refused requests (a bad proof, a mismatched key) consume nothing; at the cap both
/// refuse (`IssuanceCapReached`), after their proof checks, and the key's encoding keeps the
/// count. An OLDER encoding of the key rolls the count back: persisting the key after issuing is
/// the operator's rule (docs/operating-a-helper.md); the test records that behaviour.
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and about 15 s of Jali verifications (run in release)"]
fn issuance_stops_at_a_small_cap() {
    let fx = fixture();
    let (pcs, hvk, proof) = (&fx.pcs, &fx.hvk, &fx.proof);
    let mut log = Log::new("the issuance cap (2 units left)");
    log.section("one helper key restored with Q_max − 2 preimages issued");
    let mut rng = StdRng::seed_from_u64(0xa77a_c009);
    let mut bytes = fx.hsk.to_bytes().unwrap().to_vec();
    let at = VSISSigningKey::BYTES - 8;
    bytes[at..at + 8].copy_from_slice(&(Q_MAX - 2).to_le_bytes());
    let restored_with_two = bytes.clone();
    let hsk = <HelperSecretKey<VSIS> as WireFormat>::from_bytes(&bytes).unwrap();
    log.holds(X, "2 units left", hsk.signing_key().remaining() == 2);
    let pre = log.ok(
        X,
        "Issue answers (1 left)",
        pcs.issue(hvk, &hsk, &fx.f, &fx.r.id, proof, &mut rng),
    );
    let state = IssuanceState::from_bytes(&fx.state_bytes).unwrap();
    log.holds(
        X,
        "the pre-credential is real",
        pcs.unblind(hvk, &fx.r.usk, &fx.f, &pre, &state)
            .is_ok_and(|cred| pcs.verify_cred(hvk, &fx.r.usk, &fx.f, &cred)),
    );
    let mut c = proof.c.coeffs().to_vec();
    c[3] = (c[3] + 1) % Q;
    let bad = IssuanceProof {
        c: Rq::from_coeffs(&c).unwrap(),
        ..proof.clone()
    };
    log.refused(
        X,
        "a refused proof ...",
        pcs.issue(hvk, &hsk, &fx.f, &fx.r.id, &bad, &mut rng),
        Error::InvalidProof,
    );
    let (other_hvk, _) = pcs.helper_keygen(&mut rng);
    log.refused(
        X,
        "a mismatched helper key ...",
        pcs.issue(&other_hvk, &hsk, &fx.f, &fx.r.id, proof, &mut rng),
        Error::InvalidKey,
    );
    log.holds(
        X,
        "... consume nothing (1 left)",
        hsk.signing_key().remaining() == 1,
    );
    log.ok(
        X,
        "issue_root answers (0 left): the root path counts too",
        pcs.issue_root(
            hvk,
            &hsk,
            &fx.f_root,
            &fx.a.id,
            &fx.root_request_a,
            &mut rng,
        ),
    );
    log.holds(
        X,
        "0 left",
        hsk.signing_key().remaining() == 0 && hsk.signing_key().issued() == Q_MAX,
    );
    log.refused(
        X,
        "Issue at the cap",
        pcs.issue(hvk, &hsk, &fx.f, &fx.r.id, proof, &mut rng),
        Error::IssuanceCapReached,
    );
    log.refused(
        X,
        "issue_root at the cap",
        pcs.issue_root(
            hvk,
            &hsk,
            &fx.f_root,
            &fx.a.id,
            &fx.root_request_a,
            &mut rng,
        ),
        Error::IssuanceCapReached,
    );
    log.holds(
        X,
        "the refusals consume nothing",
        hsk.signing_key().issued() == Q_MAX,
    );
    let at_cap =
        <HelperSecretKey<VSIS> as WireFormat>::from_bytes(&hsk.to_bytes().unwrap()).unwrap();
    log.refused(
        X,
        "the key's encoding keeps the count: the decoded key refuses too",
        pcs.issue_root(
            hvk,
            &at_cap,
            &fx.f_root,
            &fx.a.id,
            &fx.root_request_a,
            &mut rng,
        ),
        Error::IssuanceCapReached,
    );
    let older = <HelperSecretKey<VSIS> as WireFormat>::from_bytes(&restored_with_two).unwrap();
    log.holds(
        X,
        "an OLDER encoding rolls the count back (2 left): persist the key after issuing",
        older.signing_key().remaining() == 2,
    );
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// Tampered credentials
// ---------------------------------------------------------------------------------------------

/// A credential that is not the attester's own does not attest: tampered `s`, `x_1` or `x_0`, the
/// attester's credential presented for another label, or another member's credential with the
/// attester's key are refused by the honest prover's witness check before any proving work
/// (`WitnessDoesNotSatisfyRelation`); `VerifyCred` rejects each of them.
#[test]
#[ignore = "heavy: the shared fixture (about 30 s) and five Jali witness checks (run in release)"]
fn tampered_credentials_cannot_attest() {
    let fx = fixture();
    let (pcs, hvk) = (&fx.pcs, &fx.hvk);
    let mut log = Log::new("tampered credentials");
    log.section("A attests for R with a credential that is not its own");
    let mut rng = StdRng::seed_from_u64(0xa77a_c00a);
    let cred = fx.a.cred();
    let mut s0 = cred.cred.s0().to_vec();
    s0[0] += 1;
    let mut x1 = cred.cred.x1().coeffs().to_vec();
    x1[1] = if x1[1] == 1 { 0 } else { 1 };
    let mut x0 = cred.x0[0].coeffs().to_vec();
    x0[2] = if x0[2] == -1 { 0 } else { -1 };
    let tampered = [
        (
            "s_0 + 1 in one coefficient",
            Credential {
                cred: VSISCredential::from_parts(
                    s0,
                    cred.cred.s1().to_vec(),
                    cred.cred.x1().clone(),
                )
                .unwrap(),
                x0: cred.x0.clone(),
            },
        ),
        (
            "x_1 changed in one coefficient",
            Credential {
                cred: VSISCredential::from_parts(
                    cred.cred.s0().to_vec(),
                    cred.cred.s1().to_vec(),
                    Ternary::from_coeffs(&x1).unwrap(),
                )
                .unwrap(),
                x0: cred.x0.clone(),
            },
        ),
        (
            "x_0 changed in one coefficient",
            Credential {
                cred: cred.cred.clone(),
                x0: [Ternary::from_coeffs(&x0).unwrap(), cred.x0[1].clone()],
            },
        ),
        ("B's credential", fx.b.cred().clone()),
    ];
    for (what, bad) in &tampered {
        log.holds(
            X,
            &format!("VerifyCred rejects A's key with {what}"),
            !pcs.verify_cred(hvk, &fx.a.usk, &fx.f_root, bad),
        );
        log.refused(
            X,
            &format!("Attest refuses A's key with {what}"),
            pcs.attest(hvk, &fx.a.usk, &fx.f_root, bad, &fx.r.id, &mut rng),
            Error::WitnessDoesNotSatisfyRelation,
        );
    }
    log.holds(
        X,
        "VerifyCred rejects A's credential for another label",
        !pcs.verify_cred(hvk, &fx.a.usk, &fx.f_other, cred),
    );
    log.refused(
        X,
        "Attest refuses A's credential presented for another label (φ is EncPred(f_j))",
        pcs.attest(hvk, &fx.a.usk, &fx.f_other, cred, &fx.r.id, &mut rng),
        Error::WitnessDoesNotSatisfyRelation,
    );
    log.finish(0);
}

// ---------------------------------------------------------------------------------------------
// Light tests: no Jali proof
// ---------------------------------------------------------------------------------------------

/// A non-canonical `C` (a coefficient `q`, `q + 1` or `q + 2 = 2^20 − 1` in its 20-bit field) does
/// not decode in an issuance proof or a root request, compact or canonical; a non-canonical `h`
/// does not decode as `hvk`, alone or inside `hsk`; and a wiped `C` (the one value of `Rq` outside
/// `R_q`) is refused by the verifiers (`InvalidIssuanceEncoding`) and by the encoders.
#[test]
fn non_canonical_c_and_h_are_refused() {
    let mut rng = StdRng::seed_from_u64(0xa77a_c00b);
    let f = Predicate::new(2, b"members".to_vec());
    let f_root = Predicate::root(b"founders".to_vec());
    let pcs = deployment(LABEL, &[&f_root, &f]);
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);
    let (id, _) = pcs.user_keygen(&mut rng).unwrap();
    let c = Rq::from_i64(
        &(0..D)
            .map(|i| i64::try_from(i).unwrap() * 7919)
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let att = Attestation {
        tag: id.clone(),
        phi: pcs.enc_pred(&f_root),
        proof: Proof::from_bytes(vec![7; 100]).unwrap(),
    };
    let proof = IssuanceProof {
        attestations: vec![att.clone(), att],
        c: c.clone(),
        t0: id.clone(),
        proof: Proof::from_bytes(vec![9; 50]).unwrap(),
    };
    let request = RootRequest {
        c: c.clone(),
        t0: id.clone(),
        proof: Proof::from_bytes(vec![5; 60]).unwrap(),
    };
    let compact = proof.to_compact_bytes().unwrap();
    let canonical = WireFormat::to_bytes(&proof).unwrap();
    let root = request.to_compact_bytes().unwrap();
    let c_at = 2 * (Attestation::FIXED_BYTES + 100); // C follows the two attestations
    for value in [Q, Q + 1, Q + 2] {
        assert_eq!(Q + 2, (1 << 20) - 1);
        for j in [0usize, 511, D - 1] {
            let mut bytes = compact.clone();
            set_coefficient_20(&mut bytes[c_at..c_at + Rq::BYTES], j, value);
            assert!(IssuanceProof::from_compact_bytes(&bytes, &f).is_err());
            let mut bytes = canonical.clone();
            set_coefficient_20(&mut bytes[4 + c_at..4 + c_at + Rq::BYTES], j, value);
            assert!(<IssuanceProof as WireFormat>::from_bytes(&bytes).is_err());
            let mut bytes = root.clone();
            set_coefficient_20(&mut bytes[..Rq::BYTES], j, value);
            assert!(RootRequest::from_compact_bytes(&bytes).is_err());
            assert!(<RootRequest as WireFormat>::from_bytes(&bytes).is_err());
            let mut bytes = WireFormat::to_bytes(&hvk).unwrap();
            set_coefficient_20(&mut bytes, j, value);
            assert!(<VSISVerificationKey as WireFormat>::from_bytes(&bytes).is_err());
            let mut bytes = hsk.to_bytes().unwrap().to_vec();
            let h_at = VSISSigningKey::BYTES;
            set_coefficient_20(&mut bytes[h_at..h_at + Rq::BYTES], j, value);
            assert!(<HelperSecretKey<VSIS> as WireFormat>::from_bytes(&bytes).is_err());
        }
        let mut coeffs = c.coeffs().to_vec();
        coeffs[0] = value;
        assert!(Rq::from_coeffs(&coeffs).is_err());
    }
    // the canonical values next to the boundary decode
    let mut bytes = root.clone();
    set_coefficient_20(&mut bytes[..Rq::BYTES], 0, Q - 1);
    assert!(RootRequest::from_compact_bytes(&bytes).is_ok());
    // a wiped C: no encoding, and the verifiers refuse it before any proof
    let mut wiped = proof.clone();
    wiped.c.zeroize();
    assert!(wiped.to_compact_bytes().is_err());
    assert!(WireFormat::to_bytes(&wiped).is_err());
    assert_eq!(
        pcs.check_proof(&hvk, &f, &id, &wiped),
        Err(Error::InvalidIssuanceEncoding)
    );
    let mut wiped = request;
    wiped.c.zeroize();
    assert!(wiped.to_compact_bytes().is_err());
    assert_eq!(
        pcs.check_root_request(&hvk, &f_root, &id, &wiped),
        Err(Error::InvalidIssuanceEncoding)
    );
    // BlindIssue refuses a wiped C too, and consumes nothing
    let mut c_wiped = c;
    c_wiped.zeroize();
    assert_eq!(
        VSIS::blind_issue(
            &pcs.public_parameters().pp_sigma,
            hsk.signing_key(),
            &c_wiped,
            &pcs.enc_pred(&f),
            &mut rng
        )
        .err(),
        Some(Error::InvalidIssuanceEncoding)
    );
    assert_eq!(hsk.signing_key().issued(), 0);
}

/// `VerifyCred` and `Unblind` on tampered credentials, without a proof: a credential that the
/// helper signed (`Σ-vSIS.Sign` under the one key) verifies; each change of `s_0`, `s_1`, `x_1`,
/// `x_0`, of the key, the label or the helper key makes `VerifyCred` reject it and `Unblind`
/// refuse it as a pre-credential (`InvalidPreCredential`); a single bit flipped in its encoding
/// either does not decode or does not verify.
#[test]
fn tampered_credentials_fail_verification() {
    let mut rng = StdRng::seed_from_u64(0xa77a_c00c);
    let f = Predicate::new(2, b"members".to_vec());
    let f_root = Predicate::root(b"founders".to_vec());
    let pcs = deployment(LABEL, &[&f_root, &f]);
    let sigma = &pcs.public_parameters().pp_sigma;
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);
    let (hvk2, _) = pcs.helper_keygen(&mut rng);
    let (_, usk) = pcs.user_keygen(&mut rng).unwrap();
    let (_, other) = pcs.user_keygen(&mut rng).unwrap();
    let x0 = [Ternary::sample(&mut rng), Ternary::sample(&mut rng)];
    let phi = pcs.enc_pred(&f);
    let m = VSIS::encode_message(
        sigma,
        &VSISHiddenMessage::new(usk.expose_ternary().clone(), x0.clone()),
        &phi,
    )
    .unwrap();
    let signed = VSIS::sign(sigma, hsk.signing_key(), &m, &mut rng).unwrap();
    let cred = Credential {
        cred: signed.clone(),
        x0: x0.clone(),
    };
    assert!(pcs.verify_cred(&hvk, &usk, &f, &cred));
    let state = || {
        let mut bytes = usk.to_bytes().unwrap().to_vec();
        bytes.extend_from_slice(&x0[0].to_bytes());
        bytes.extend_from_slice(&x0[1].to_bytes());
        bytes.extend_from_slice(phi.as_bytes());
        IssuanceState::from_bytes(&bytes).unwrap()
    };
    assert!(pcs.unblind(&hvk, &usk, &f, &signed, &state()).is_ok());

    let with = |s0: &[i32], s1: &[i32], x1: &Ternary| {
        VSISCredential::from_parts(s0.to_vec(), s1.to_vec(), x1.clone()).unwrap()
    };
    let (s0, s1, x1) = (signed.s0(), signed.s1(), signed.x1());
    let mut variants = Vec::new();
    for j in [0usize, 77, D - 1] {
        for delta in [-1i32, 1] {
            let mut t = s0.to_vec();
            t[j] += delta;
            variants.push(with(&t, s1, x1));
            let mut t = s1.to_vec();
            t[j] += delta;
            variants.push(with(s0, &t, x1));
        }
        let mut t = x1.coeffs().to_vec();
        t[j] = (t[j] + 2) % 3 - 1; // another ternary value
        variants.push(with(s0, s1, &Ternary::from_coeffs(&t).unwrap()));
    }
    for pre in &variants {
        let bad = Credential {
            cred: pre.clone(),
            x0: x0.clone(),
        };
        assert!(!pcs.verify_cred(&hvk, &usk, &f, &bad));
        assert_eq!(
            pcs.unblind(&hvk, &usk, &f, pre, &state()).err(),
            Some(Error::InvalidPreCredential)
        );
    }
    let mut t = x0[1].coeffs().to_vec();
    t[5] = (t[5] + 2) % 3 - 1;
    let bad = Credential {
        cred: signed.clone(),
        x0: [x0[0].clone(), Ternary::from_coeffs(&t).unwrap()],
    };
    assert!(!pcs.verify_cred(&hvk, &usk, &f, &bad));
    assert!(!pcs.verify_cred(&hvk, &other, &f, &cred));
    assert!(!pcs.verify_cred(&hvk, &usk, &f_root, &cred));
    assert!(!pcs.verify_cred(&hvk2, &usk, &f, &cred));
    assert_eq!(
        pcs.unblind(&hvk2, &usk, &f, &signed, &state()).err(),
        Some(Error::InvalidPreCredential)
    );
    // one bit flipped anywhere in the encoding
    let bytes = cred.to_bytes().unwrap();
    for at in (0..Credential::BYTES).step_by(37) {
        let mut flipped = bytes.to_vec();
        flipped[at] ^= 1 << (at % 8);
        if let Ok(decoded) = <Credential as WireFormat>::from_bytes(&flipped) {
            assert!(!pcs.verify_cred(&hvk, &usk, &f, &decoded), "bit {at}");
        }
    }
}
