//! An interactive walkthrough of hidden-vetter admission, for an audience of cryptographers.
//!
//! The same flow as `tests/end_to_end.rs`, one stage at a time: every group element that goes
//! over the wire is printed, and every equation the scheme relies on is recomputed live from the
//! values on screen (the walkthrough peeks at secret keys to do so; a real engine never would).
//!
//!     cargo run -p pcs-vetting-prototype --release --example walkthrough
//!
//! Every stage is computed up front (the run is seeded, so it is the same every time), then
//! paged: Enter or `n` next, `b` back, a number jumps to that stage, `q` quits. Flags: `--auto`
//! prints every stage and exits, `--no-clear` keeps the scrollback. `NO_COLOR` turns colour off.

use std::{
    cell::RefCell,
    fmt::Write as _,
    io::{self, BufRead, Write as _},
};

use ark_bls12_381::{Bls12_381, G2Projective};
use ark_ec::{PrimeGroup, pairing::Pairing};
use chrono::{NaiveDate, TimeZone, Utc};
use pcs_vetting_prototype::{
    applicant::ApplicantEngine,
    meta::{StatementMeta, id_binding},
    scheme::{
        E, Fr, G1, deployment_label, hidden_vetting_predicate, point_text, scalar_text,
        token_deployment_label, vetter_predicate,
    },
    token::TokenParams,
    vetter::{HiddenAttestation, VetterEngine},
    vtc::{Decision, Submission, Vtc},
};
use predicate_credential_system::{
    cred::ps::{PSCredential, PSVerificationKey},
    kiprf::KIPRF,
    serialization::{to_bytes, to_multibase},
};
use rand::{SeedableRng, rngs::StdRng};
use serde_json::json;
use vta_sdk::protocols::vetting::{
    IDENTITY_VETTING_ENDORSEMENT_TYPE, VettingMethod, VettingRelationship,
};

const COMMUNITY: &str = "did:example:kernel-vtc";
const PERIOD: &str = "2026-09";
/// The flow, as the breadcrumb shows it. Every stage belongs to one phase.
const PHASES: [&str; 9] = [
    "Intro",
    "Setup",
    "Enrolment",
    "Vetting",
    "Admission",
    "Privacy",
    "Abuse",
    "Withdrawal",
    "Summary",
];

// ---------------------------------------------------------------------------------------------
// Presentation
// ---------------------------------------------------------------------------------------------

struct Page {
    phase: &'static str,
    title: String,
    who: String,
    body: String,
}

/// Collects the stages as pages; [`Ui::present`] shows them.
struct Ui {
    color: bool,
    pages: RefCell<Vec<Page>>,
}

impl Ui {
    fn paint(&self, code: &str, s: &str) -> String {
        if self.color {
            format!("\x1b[{code}m{s}\x1b[0m")
        } else {
            s.to_string()
        }
    }

    fn line(&self, text: &str) {
        let mut pages = self.pages.borrow_mut();
        let page = pages.last_mut().expect("a stage is open");
        let _ = writeln!(page.body, "{text}");
    }

    /// Open a new stage.
    fn stage(&self, phase: &'static str, title: &str, who: &str) {
        debug_assert!(PHASES.contains(&phase));
        self.pages.borrow_mut().push(Page {
            phase,
            title: title.to_string(),
            who: who.to_string(),
            body: String::new(),
        });
    }

    /// Prose.
    fn say(&self, text: &str) {
        for line in text.lines() {
            self.line(&format!("   {line}"));
        }
    }

    /// A formula or a relation.
    fn math(&self, text: &str) {
        for line in text.lines() {
            self.line(&format!("      {}", self.paint("36", line)));
        }
    }

    /// A value that exists in this run.
    fn val(&self, name: &str, value: &str) {
        self.line(&format!("      {:<22} {}", self.paint("33", name), value));
    }

    /// An equation recomputed live.
    fn check(&self, what: &str, ok: bool) {
        let mark = if ok {
            self.paint("1;32", "✓")
        } else {
            self.paint("1;31", "✗")
        };
        self.line(&format!("      {mark} {what}"));
    }

    /// Text shown verbatim (wire data).
    fn raw(&self, text: &str) {
        for line in text.lines() {
            self.line(&format!("      {}", self.paint("2", line)));
        }
    }

    fn gap(&self) {
        self.line("");
    }

    /// The breadcrumb: every phase, the current one highlighted with its progress.
    fn breadcrumb(&self, pages: &[Page], at: usize) -> String {
        let current = pages[at].phase;
        let here = PHASES.iter().position(|p| *p == current).unwrap_or(0);
        let in_phase: Vec<usize> = (0..pages.len())
            .filter(|&i| pages[i].phase == current)
            .collect();
        let pos = in_phase.iter().position(|&i| i == at).unwrap_or(0);
        let crumbs: Vec<String> = PHASES
            .iter()
            .enumerate()
            .map(|(i, p)| match i.cmp(&here) {
                std::cmp::Ordering::Less => self.paint("32", p),
                std::cmp::Ordering::Equal if in_phase.len() > 1 => {
                    self.paint("1;7", &format!(" {p} {}/{} ", pos + 1, in_phase.len()))
                }
                std::cmp::Ordering::Equal => self.paint("1;7", &format!(" {p} ")),
                std::cmp::Ordering::Greater => self.paint("2", p),
            })
            .collect();
        format!("   {}", crumbs.join(&self.paint("2", " › ")))
    }

    fn render(&self, pages: &[Page], at: usize, clear: bool) {
        let p = &pages[at];
        if clear {
            print!("\x1b[2J\x1b[H");
        }
        println!();
        let n = format!(" {}/{} ", at + 1, pages.len());
        println!("{}  {}", self.paint("1;7", &n), self.paint("1", &p.title));
        println!("{}", self.paint("2", &format!("   {}", p.who)));
        println!();
        print!("{}", p.body);
    }

    /// Show the pages: all at once with `auto`, otherwise one at a time under the presenter's
    /// control.
    fn present(&self, auto: bool, clear: bool) {
        let pages = self.pages.borrow();
        if auto {
            for at in 0..pages.len() {
                self.render(&pages, at, false);
                println!("\n{}", self.breadcrumb(&pages, at));
            }
            return;
        }
        let mut at = 0;
        let mut note = String::new();
        loop {
            self.render(&pages, at, clear);
            let last = pages.len();
            // At the bottom, beside the prompt: a long stage scrolls its top off the screen.
            println!("\n{}", self.breadcrumb(&pages, at));
            print!(
                "{}{}",
                self.paint(
                    "2",
                    &format!("   ⏎/n next · b back · 1–{last} jump · q quit ")
                ),
                self.paint("33", &note)
            );
            io::stdout().flush().ok();
            note.clear();
            let mut input = String::new();
            if io::stdin().lock().read_line(&mut input).unwrap_or(0) == 0 {
                println!();
                return;
            }
            match input.trim() {
                "" | "n" => {
                    if at + 1 < last {
                        at += 1;
                    } else {
                        note = "(last stage)".into();
                    }
                }
                "b" | "p" => {
                    if at > 0 {
                        at -= 1;
                    } else {
                        note = "(first stage)".into();
                    }
                }
                "q" => {
                    println!();
                    return;
                }
                other => match other.parse::<usize>() {
                    Ok(k) if (1..=last).contains(&k) => at = k - 1,
                    _ => note = format!("(no stage {other:?})"),
                },
            }
        }
    }
}

/// A group element or scalar: a hex excerpt of its compressed encoding, and its size.
fn hx<T: ark_serialize::CanonicalSerialize>(v: &T) -> String {
    let b = to_bytes(v).expect("serializable");
    let h: String = b.iter().map(|x| format!("{x:02x}")).collect();
    if h.len() > 32 {
        format!("{}…{}  ({} B)", &h[..20], &h[h.len() - 8..], b.len())
    } else {
        format!("{h}  ({} B)", b.len())
    }
}

fn short(s: &str) -> String {
    if s.chars().count() > 24 {
        format!("{}…", s.chars().take(24).collect::<String>())
    } else {
        s.to_string()
    }
}

/// `e(σ_1, X̃ Ỹ_1^{m_1} Ỹ_2^{m_2}) = e(σ_2, g̃)`, recomputed.
fn ps_verify(vk: &PSVerificationKey<E>, m1: &Fr, m2: &Fr, s1: &G1, s2: &G1) -> bool {
    let rhs = vk.x_tilde + vk.y1_tilde * m1 + vk.y2_tilde * m2;
    Bls12_381::pairing(*s1, rhs) == Bls12_381::pairing(*s2, G2Projective::generator())
}

// ---------------------------------------------------------------------------------------------
// The scenario
// ---------------------------------------------------------------------------------------------

fn now() -> chrono::DateTime<Utc> {
    Utc.with_ymd_and_hms(2026, 9, 22, 12, 0, 0).unwrap()
}

fn meta(app: &ApplicantEngine, vtc: &Vtc, method: VettingMethod) -> StatementMeta {
    app.statement_meta(
        vtc,
        StatementMeta {
            community: String::new(),
            requirements_digest: String::new(),
            method,
            claims_verified: vec!["name.legal".into()],
            liveness_confirmed: true,
            declared_relationship: VettingRelationship::None,
            identity_commitment: "zCommitmentOfThisApplication".into(),
            card_digest_multibase: "zCardDigest".into(),
            valid_from: NaiveDate::from_ymd_opt(2026, 9, 20).unwrap(),
            valid_until: NaiveDate::from_ymd_opt(2027, 1, 18).unwrap(),
            token_label: String::new(),
            token_serial: String::new(),
        },
    )
}

fn vet(
    vtc: &Vtc,
    v: &mut VetterEngine,
    app: &ApplicantEngine,
    method: VettingMethod,
    rng: &mut StdRng,
) -> HiddenAttestation {
    let r = v.accept(None, 2).unwrap();
    let m = meta(app, vtc, method);
    v.attest(vtc, &r, app.id(), m, rng).unwrap()
}

fn show_decision(ui: &Ui, d: &Decision) {
    ui.say(
        "The facts handed to VTI's counting rule (vta-sdk `requirements::evaluate`, unchanged):",
    );
    for s in &d.statements {
        ui.val(
            "vetter (= tag T_j)",
            &format!(
                "{}  {:?}  counted={}  {:?}",
                short(&s.issuer),
                s.method,
                s.counted,
                s.failures
            ),
        );
    }
    let e = &d.evaluation;
    let verdict = if e.satisfied() {
        ui.paint("1;32", "ADMIT")
    } else {
        ui.paint("1;33", "requestMore")
    };
    ui.val(
        "evaluate",
        &format!(
            "distinct vetters = {}, needs = {:?}  →  {verdict}",
            e.distinct_vetters(),
            e.needs
        ),
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let auto = args.iter().any(|a| a == "--auto");
    let clear = !args.iter().any(|a| a == "--no-clear");
    let ui = Ui {
        color: std::env::var_os("NO_COLOR").is_none(),
        pages: RefCell::new(Vec::new()),
    };
    let mut rng = StdRng::seed_from_u64(7);
    let g1 = G1::generator();

    // ── 1 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Intro",
        "Hidden-vetter admission with a Predicate Credential System",
        "the problem, and the cast",
    );
    ui.say(
        "A community (a VTC) admits a member only if k of its vetters have checked the person.\n\
         Today each vetter signs an endorsement with their own DID, so the community learns\n\
         exactly who vetted whom: a social graph of who-knows-whom, and pressure on vetters.",
    );
    ui.gap();
    ui.say("Goal: the applicant proves");
    ui.math("\"k DISTINCT holders of a CURRENT vetter credential attested to me\"");
    ui.say("and the community learns k and the per-statement metadata it counts, but not which vetters.");
    ui.gap();
    ui.say("Cast:");
    ui.val(
        "VTC",
        "the community; PCS *helper* (issues credentials, verifies proofs)",
    );
    ui.val("alice, carol, dave", "members with the vetter role");
    ui.val("bob", "applicant");
    ui.gap();
    ui.say(
        "Instantiation: the modular threshold construction of the PCS paper (§5.1) with\n\
         Σ-PS (Pointcheval–Sanders) as the credential base and Tag_DDH as the key-injective PRF,\n\
         over BLS12-381. Proofs are Σ-protocols compiled with Fiat–Shamir.",
    );

    // ── 2 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Setup",
        "Setup: public parameters and the helper key",
        "VTC",
    );
    let requirements = json!({
        "version": "0.1",
        "statementType": IDENTITY_VETTING_ENDORSEMENT_TYPE,
        "minStatements": 2,
        "minByMethod": { "inPerson": 1 },
        "acceptedMethods": ["inPerson", "video", "priorAcquaintance"],
        "requiredClaims": ["name.legal"],
        "maxStatementAge": "P120D",
        "eligibleVetters": { "role": "vetter" },
        "independence": {
            "maxByDeclaredRelationship": { "family": 0 },
            "requireConsistentIdentityCommitment": true
        }
    });
    let mut vtc = Vtc::new(COMMUNITY, PERIOD, requirements, &mut rng).unwrap();
    let hvk = vtc.hvk().clone();
    ui.say("Groups: e : G1 × G2 → GT (type 3). Compressed: |G1| = 48 B, |G2| = 96 B, |Fr| = 32 B.");
    ui.gap();
    ui.say(
        "pp is derived from a fixed deployment label: H_0 and H_2 are domain-separated by it, and",
    );
    ui.say("H_1 (Fiat–Shamir) sees it through digest(pp), which leads every context:");
    ui.val(
        "label",
        &String::from_utf8_lossy(&deployment_label(COMMUNITY)),
    );
    ui.val("digest(pp)", &hx(vtc.open().parameters_digest()));
    ui.val("c_0 = H_0(\"identity\")", &hx(vtc.open().identity_point()));
    ui.math("Tag_DDH(K, s) = H_2(s)^K        with H_2 programmed so that H_2(c_0) = g_1");
    ui.gap();
    ui.say("HKeyGen → hsk = (x, y_1, y_2) ← Z_p × (Z_p*)², and the public hvk:");
    ui.val("X̃  = g̃^x", &hx(&hvk.x_tilde));
    ui.val("Ỹ_1 = g̃^y1", &hx(&hvk.y1_tilde));
    ui.val("Ỹ_2 = g̃^y2", &hx(&hvk.y2_tilde));
    ui.val("Y_1 = g_1^y1", &hx(&hvk.y1));
    ui.check(
        "hvk is in the range of KeyGen: Ỹ_1, Ỹ_2 ≠ 1 and e(Y_1, g̃) = e(g_1, Ỹ_1)",
        hvk.is_well_formed(),
    );
    ui.gap();
    ui.say("The helper does NOT run with the default policy P ≡ 1. Its policy is an AllowList of");
    ui.say("the live vetter classes, so only credentials of a live period count:");
    for phi in vtc.live_vetter_phis().unwrap() {
        ui.val("φ(vetter/2026-09)", &hx(&phi));
    }
    ui.math("φ = EncPred(f) = H_0(\"predicate\" ‖ ⟨f⟩),   f = (threshold 0, \"vetter/2026-09\"): a root predicate");
    ui.say(
        "The epoch lives in the class label, not in pp: identities stay fixed across rotations,",
    );
    ui.say("and one proof may mix attestations from two live periods.");

    // ── 3 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Enrolment",
        "A vetter's key: one usk for life",
        "alice's VTA (her PCS engine)",
    );
    let mut vetters = Vec::new();
    for name in ["alice", "carol", "dave"] {
        vtc.grant(name);
        vetters.push(VetterEngine::new(name, &vtc, &mut rng).unwrap());
    }
    let alice_usk = *vetters[0].usk_scalar();
    let alice_id = *vetters[0].id();
    ui.say("UKeyGen: usk ← Z_p*, and the public identifier is the tag at the identity point:");
    ui.val("usk  (secret)", &hx(&alice_usk));
    ui.val("id = Tag(usk, c_0)", &hx(&alice_id));
    ui.check(
        "id = H_2(c_0)^usk = g_1^usk   (recomputed)",
        alice_id == g1 * alice_usk
            && vtc
                .open()
                .tag()
                .eval(&alice_usk, vtc.open().identity_point())
                == Some(alice_id),
    );
    ui.gap();
    ui.say("The VTC binds this id to alice's member record at her first enrolment and refuses any");
    ui.say(
        "other id for her afterwards. That is the Sybil defence: one member, one key, so one tag",
    );
    ui.say("per applicant, so one vote, however many periods she enrols in.");

    // ── 4 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Enrolment",
        "Root credential: blind issuance of a PS signature on (usk, φ)",
        "alice ⇄ VTC",
    );
    let phi_v = vtc.open().enc_pred(&vetter_predicate(PERIOD)).unwrap();
    let trace = vetters[0].enroll_traced(&mut vtc, &mut rng).unwrap();
    ui.say("1. alice → VTC: the root request (C, T_0, π_root)");
    ui.math("C   = Com(usk, φ; ρ) = g_1^ρ · Y_1^usk                     ρ ← Z_p");
    ui.math("T_0 = Tag(usk, H_0(id))");
    ui.math("π_root : PoK{ (usk, ρ) : C = g_1^ρ Y_1^usk  ∧  id = H_2(c_0)^usk  ∧  T_0 = H_2(H_0(id))^usk }");
    ui.val("C", &hx(&trace.request.encoding));
    ui.val("T_0", &hx(&trace.request.t0));
    ui.val(
        "π_root",
        &format!(
            "challenge + {} responses = {} B   (under ctx_root ≠ ctx_0: never replayable as a proof)",
            trace.request.proof.responses.len(),
            trace.request.proof.compact_size()
        ),
    );
    ui.gap();
    ui.say("2. VTC: verifies π_root, checks the grant (alice holds the vetter role), binds");
    ui.say("   member → id, refuses a second credential this period, then BlindIssue:");
    ui.math("u ← Z_p*,   σ̂ = ( g_1^u ,  (g_1^x · C · g_1^{y_2 φ})^u )");
    ui.val("σ̂_1", &hx(&trace.pre.sigma_1));
    ui.val("σ̂_2", &hx(&trace.pre.sigma_2));
    ui.say("   The VTC never sees usk; φ enters only here, as g_1^{y_2 φ}.");
    ui.gap();
    ui.say("3. alice: Unblind, σ = (σ̂_1, σ̂_2 / σ̂_1^ρ) = (h, h^{x + y_1·usk + y_2·φ}),  h = g_1^u");
    let cred: PSCredential<E> = vetters[0].credential(PERIOD).unwrap().cred.clone();
    ui.val("σ_1", &hx(&cred.sigma_1));
    ui.val("σ_2", &hx(&cred.sigma_2));
    ui.check(
        "e(σ_1, X̃ · Ỹ_1^usk · Ỹ_2^φ) = e(σ_2, g̃): a PS signature on (usk, φ)",
        ps_verify(&hvk, &alice_usk, &phi_v, &cred.sigma_1, &cred.sigma_2),
    );
    ui.check(
        "and NOT on any other class φ' (here φ' = φ + 1)",
        !ps_verify(
            &hvk,
            &alice_usk,
            &(phi_v + Fr::from(1u64)),
            &cred.sigma_1,
            &cred.sigma_2,
        ),
    );
    for v in vetters.iter_mut().skip(1) {
        v.enroll(&mut vtc, &mut rng).unwrap();
    }
    ui.gap();
    ui.say("carol and dave enrol the same way.");

    // ── 5 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Enrolment",
        "Attestation tokens: a blind, rate-limited budget",
        "VTC → each vetter, on a drip",
    );
    ui.say(
        "Anonymity creates a problem: nothing would stop a vetter attesting for 1,000 applicants.",
    );
    ui.say("So each attestation spends a token, and tokens drip at a fixed rate per member.");
    ui.say("Tokens are themselves PS blind signatures, under a SEPARATE key tvk, never hvk");
    ui.say("(a PS signature on (s, φ) under hvk would be a PCS credential whose \"usk\" s the vetter knows).");
    ui.gap();
    let tparams = TokenParams::new(COMMUNITY).unwrap();
    let tlabel = vtc.current_token_label().to_string();
    let phi_t = tparams.phi(&tlabel).unwrap();
    ui.val(
        "token deployment",
        &String::from_utf8_lossy(&token_deployment_label(COMMUNITY)),
    );
    ui.val("label", &tlabel);
    ui.val("φ_token", &hx(&phi_t));
    ui.gap();
    ui.say("Per tick, the vetter draws fresh serials s_i and sends only commitments:");
    ui.math("C_i = g_1^{ρ_i} · Y_1t^{s_i}      PoK{(s_i, ρ_i)} bound to (tvk, label, member, tick, i, C_i)");
    let (reqs, pres) = vetters[0]
        .drip_traced(&mut vtc, 1, &tlabel, 3, &mut rng)
        .unwrap();
    for (i, (r, p)) in reqs.iter().zip(&pres).enumerate() {
        ui.val(&format!("C_{i}"), &hx(&r.commitment));
        ui.val(&format!("σ̂_{i},1  (blind sig)"), &hx(&p.sigma_1));
    }
    ui.say(
        "The VTC signs once per (member, label, tick), which is the rate limit, and never learns",
    );
    ui.say(
        "s_i. At spend time the vetter reveals s_i with a RE-RANDOMISED signature, so the spend is",
    );
    ui.say("unlinkable to the issuance; the VTC keeps a spent set per label.");
    for v in vetters.iter_mut().skip(1) {
        v.drip(&mut vtc, 1, &tlabel, 3, &mut rng).unwrap();
    }
    ui.gap();
    ui.val(
        "tokens held",
        &format!(
            "alice {}, carol {}, dave {}",
            vetters[0].tokens_held(),
            vetters[1].tokens_held(),
            vetters[2].tokens_held()
        ),
    );

    // ── 6 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Vetting",
        "The applicant: a fresh key per application",
        "bob's VTA",
    );
    let mut bob = ApplicantEngine::new(&vtc, "did:example:bob", &mut rng).unwrap();
    let bob_id = *bob.id();
    let s_bob = vtc.open().tag_point(&bob_id).unwrap();
    ui.say("bob runs UKeyGen too, but for THIS application only: his id does not link his");
    ui.say("applications to each other, or to any other identifier he has.");
    ui.val("usk_B (secret)", &hx(bob.usk_scalar()));
    ui.val("id_B = g_1^usk_B", &hx(&bob_id));
    ui.gap();
    ui.say("Everything about bob's application is evaluated at one point:");
    ui.math("s_B = H_0(id_B)");
    ui.val("s_B", &hx(&s_bob));
    ui.say(
        "Every vetter's tag for bob is H_2(s_B)^{usk_j}: a PRF output keyed by the VETTER, at a",
    );
    ui.say("point fixed by the APPLICANT. Same vetter + same applicant → same tag (so they count once);");
    ui.say("same vetter + different applicant → unrelated tag (under DDH in G1).");

    // ── 7 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Vetting",
        "carol attests for bob (video call)",
        "carol's VTA → bob",
    );
    let a_carol = vet(&vtc, &mut vetters[1], &bob, VettingMethod::Video, &mut rng);
    let carol_usk = *vetters[1].usk_scalar();
    let carol_cred = vetters[1].credential(PERIOD).unwrap().cred.clone();
    ui.say(
        "After the human check, carol's engine spends a token and attests. The statement metadata",
    );
    ui.say("(what VTI counts) is the application context app_j, hashed into ctx_j:");
    let m = &a_carol.meta;
    ui.val("method", &format!("{:?}", m.method));
    ui.val("claimsVerified", &format!("{:?}", m.claims_verified));
    ui.val(
        "validFrom / validUntil",
        &format!(
            "{} / {}   (days only: no timing side channel)",
            m.valid_from, m.valid_until
        ),
    );
    ui.val(
        "tokenLabel / Serial",
        &format!("{} / {}", m.token_label, short(&m.token_serial)),
    );
    ui.say(
        "The token serial sits inside app_j, so a token cannot be moved to another attestation.",
    );
    ui.gap();
    let att = &a_carol.attestation;
    ui.say("att_j = (T_j, cred*_j, φ_j, π_j):");
    ui.math("T_j     = H_2(s_B)^{usk_C}");
    ui.math("cred*_j = (σ_1^r, σ_2^r),  r ← Z_p*        (perfect re-randomisation of carol's credential)");
    ui.math("π_j : PoK{ usk : e(σ'_1, Ỹ_1)^usk = e(σ'_2, g̃) · e(σ'_1, X̃ Ỹ_2^φ)^{-1}  ∧  T_j = H_2(s_B)^usk }");
    ui.math("      under ctx_j = H(pp, hvk, id_B, φ_j, T_j, cred*_j, app_j)");
    ui.val("T_j", &hx(&att.tag));
    ui.val(
        "T_j (multibase)",
        &format!(
            "{}   ← how it appears in the VTC's facts",
            short(&point_text(&att.tag).unwrap())
        ),
    );
    ui.val("σ'_1", &hx(&att.shown.sigma_1));
    ui.val("σ'_2", &hx(&att.shown.sigma_2));
    ui.val(
        "φ_j",
        &format!(
            "{}   = φ(vetter/2026-09): the CLASS is disclosed, not the holder",
            hx(&att.phi)
        ),
    );
    ui.val(
        "π_j",
        &format!(
            "challenge + {} response (usk, shared by both clauses) = {} B",
            att.proof.responses.len(),
            att.proof.compact_size()
        ),
    );
    ui.val(
        "|att_j| total",
        &format!("{} B", to_bytes(att).unwrap().len()),
    );
    ui.gap();
    ui.say("Live checks with carol's secret key (which only her engine has):");
    ui.check(
        "T_j = H_2(s_B)^{usk_C}",
        vtc.open().tag().eval(&carol_usk, &s_bob) == Some(att.tag),
    );
    ui.check(
        "cred*_j is still a PS signature on (usk_C, φ):  e(σ'_1, X̃ Ỹ_1^usk Ỹ_2^φ) = e(σ'_2, g̃)",
        ps_verify(
            &hvk,
            &carol_usk,
            &att.phi,
            &att.shown.sigma_1,
            &att.shown.sigma_2,
        ),
    );
    ui.check(
        "cred*_j ≠ carol's stored σ (no linkage to the credential the VTC issued)",
        att.shown.sigma_1 != carol_cred.sigma_1 && att.shown.sigma_2 != carol_cred.sigma_2,
    );
    ui.check(
        "the tag is NOT carol's id (id_C = g_1^usk_C is what the VTC saw at enrolment)",
        att.tag != *vetters[1].id(),
    );

    // ── 8 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Vetting",
        "bob checks the attestation on receipt",
        "bob's VTA",
    );
    ui.say("So that a bad attestation fails at the vetting session, not at the join:");
    let app_j = a_carol.meta.context_bytes().unwrap();
    ui.check(
        "VerifyAtt(hvk, id_B, att_j) under the rebuilt ctx_j (app_j included)",
        vtc.open()
            .check_attestation_in_context(&hvk, &bob_id, att, &app_j)
            .is_ok(),
    );
    ui.check(
        "φ_j ∈ live vetter classes (from the VTC's manifest)",
        vtc.live_vetter_phis().unwrap().contains(&att.phi),
    );
    let tvk = vtc.tokens.tvk().clone();
    let t = &a_carol.token;
    ui.check(
        "token: e(σ'_1, X̃_t Ỹ_1t^s Ỹ_2t^φ_token) = e(σ'_2, g̃) under tvk, s = the revealed serial",
        ps_verify(&tvk, &t.serial, &phi_t, &t.shown.sigma_1, &t.shown.sigma_2),
    );
    ui.check(
        "the serial in app_j is the token's serial",
        a_carol.meta.token_serial == scalar_text(&t.serial).unwrap(),
    );
    let mut tampered = a_carol.meta.clone();
    tampered.method = VettingMethod::InPerson;
    ui.check(
        "tampering with app_j (video → inPerson) breaks π_j",
        vtc.open()
            .check_attestation_in_context(&hvk, &bob_id, att, &tampered.context_bytes().unwrap())
            .is_err(),
    );
    bob.receive(&vtc, a_carol).unwrap();

    // ── 9 ────────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Admission",
        "bob proves: \"k = 1 distinct vetter attested to me\"",
        "bob → VTC",
    );
    let sub = submit_traced(&ui, &mut vtc, &bob, &mut rng);
    let d = vtc.submit(&sub, now()).unwrap();
    ui.gap();
    show_decision(&ui, &d);
    ui.say(
        "Policy needs 2 vetters, at least one in person. The proof was valid; the count is short.",
    );

    // ── 10 ───────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Admission",
        "alice attests in person; bob resubmits with k = 2",
        "alice → bob → VTC",
    );
    let a_alice = vet(
        &vtc,
        &mut vetters[0],
        &bob,
        VettingMethod::InPerson,
        &mut rng,
    );
    let t_alice = a_alice.attestation.tag;
    bob.receive(&vtc, a_alice).unwrap();
    let sub2 = submit_traced(&ui, &mut vtc, &bob, &mut rng);
    let d = vtc.submit(&sub2, now()).unwrap();
    ui.gap();
    show_decision(&ui, &d);
    ui.say(
        "carol's token comes back with the same (id_B, T_j): already counted, not a double spend.",
    );

    // ── wire ─────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Admission",
        "The presentation, as the VTC receives it",
        "bob → VTC: vtc/join-requests/submit/0.3, member extensions.hiddenVetting",
    );
    wire_stage(&ui, &vtc, &sub2);

    // ── 11 ───────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Privacy",
        "What did the VTC learn?",
        "the VTC's view vs. the ground truth",
    );
    ui.say("The VTC knows every vetter's id (it bound them at enrolment):");
    for v in &vetters {
        ui.val(&v.member, &short(&point_text(v.id()).unwrap()));
    }
    ui.say("…and the facts it counted for bob name only the tags:");
    for s in &d.statements {
        ui.val("tag", &short(&s.issuer));
    }
    let facts = serde_json::to_string(&d.statements).unwrap();
    for v in &vetters {
        ui.check(
            &format!(
                "{} appears in the facts by neither member name nor id",
                v.member
            ),
            !facts.contains(&v.member) && !facts.contains(&point_text(v.id()).unwrap()),
        );
    }
    ui.gap();
    ui.say("Linking a tag to a vetter means deciding whether (g_1, g_1^usk, H_2(s_B), H_2(s_B)^usk) is a");
    ui.say("DDH tuple: infeasible in G1 of BLS12-381. The VTC could test it with usk; it never has it.");
    ui.gap();
    ui.say("Same vetter, different applicant → unrelated tag:");
    let frank = ApplicantEngine::new(&vtc, "did:example:frank", &mut rng).unwrap();
    let s_frank = vtc.open().tag_point(frank.id()).unwrap();
    let t_alice_frank = vtc.open().tag().eval(&alice_usk, &s_frank).unwrap();
    ui.val(
        "alice's tag for bob",
        &short(&point_text(&t_alice).unwrap()),
    );
    ui.val(
        "alice's tag for frank",
        &short(&point_text(&t_alice_frank).unwrap()),
    );
    ui.say("Same vetter, same applicant → same tag (deterministic PRF), so a vetter cannot count twice:");
    ui.check(
        "Tag(usk_A, s_B) recomputed = the tag alice sent",
        vtc.open().tag().eval(&alice_usk, &s_bob) == Some(t_alice),
    );
    ui.gap();
    ui.say("What the VTC DOES learn: k, each statement's metadata, the period of each attester's");
    ui.say(
        "credential (φ_j), and each token's label and serial (spent once, unlinkable to issuance).",
    );

    // ── 12 ───────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Abuse",
        "Attack: a vetter double-spends a token",
        "dave (cheating), eve, frank → VTC",
    );
    let mut eve = ApplicantEngine::new(&vtc, "did:example:eve", &mut rng).unwrap();
    let a_eve = vet(
        &vtc,
        &mut vetters[2],
        &eve,
        VettingMethod::InPerson,
        &mut rng,
    );
    let reused = a_eve.token.clone();
    eve.receive(&vtc, a_eve).unwrap();
    let c = vtc.challenge(&mut rng);
    let sub = eve.submit(&vtc, &c, &mut rng).unwrap();
    vtc.submit(&sub, now()).unwrap();
    ui.say("dave vets eve honestly; eve submits; dave's token serial enters the spent set.");
    ui.say("dave then attests for frank, re-using that same token:");
    let mut frank = frank;
    let m = meta(&frank, &vtc, VettingMethod::InPerson);
    let cheat = vetters[2]
        .attest_with_token(&vtc, PERIOD, reused, frank.id(), m, &mut rng)
        .unwrap();
    ui.val("serial", &short(&scalar_text(&cheat.token.serial).unwrap()));
    ui.check(
        "the attestation and the token signature are individually valid: frank's engine accepts it",
        frank.receive(&vtc, cheat).is_ok(),
    );
    let honest = vet(
        &vtc,
        &mut vetters[1],
        &frank,
        VettingMethod::Video,
        &mut rng,
    );
    frank.receive(&vtc, honest).unwrap();
    let c = vtc.challenge(&mut rng);
    let sub = frank.submit(&vtc, &c, &mut rng).unwrap();
    let d = vtc.submit(&sub, now()).unwrap();
    ui.gap();
    show_decision(&ui, &d);
    ui.val("VTC anomaly log", &format!("{:?}", vtc.tokens.anomalies));
    ui.say("The VTC sees one serial under two different (id, tag) pairs and does not count it.");
    ui.say("(issuer-not-vetter is VTI's generic code for a statement the VTC marked ineligible.)");
    ui.say("It cannot say who cheated: the token was blind-issued, and the tags are unlinkable.");

    // ── 13 ───────────────────────────────────────────────────────────────────────────────────
    ui.stage(
        "Withdrawal",
        "Withdrawal by tag",
        "carol → VTC (from any sender)",
    );
    ui.say(
        "carol changes her mind about bob. She sends the tag and a proof that she knows its key,",
    );
    ui.say("bound to (community, id_B), and nothing that links to her id:");
    ui.math("PoK{ K : T = H_2(s_B)^K }   under ctx = (\"withdraw\", community, id_B)");
    let (t_c, proof_c) = vetters[1].withdraw(&vtc, &bob_id, &mut rng).unwrap();
    let (_, proof_a) = vetters[0].withdraw(&vtc, &bob_id, &mut rng).unwrap();
    ui.val("T", &hx(&t_c));
    ui.val("proof", &format!("{} B", proof_c.compact_size()));
    ui.check(
        "alice cannot withdraw carol's statement (her proof does not verify against carol's tag)",
        !vtc.withdraw(&bob_id, &t_c, &proof_a).unwrap(),
    );
    ui.check(
        "carol's own withdrawal verifies",
        vtc.withdraw(&bob_id, &t_c, &proof_c).unwrap(),
    );
    let d = vtc.evaluate(&point_text(&bob_id).unwrap(), now());
    ui.gap();
    show_decision(&ui, &d);

    // ── 14 ───────────────────────────────────────────────────────────────────────────────────
    ui.stage("Summary", "What rests on what", "summary and caveats");
    ui.say("Security (paper, random-oracle model):");
    ui.val(
        "unforgeability",
        "PS assumption (or q-MSDH-1) + one-more security of PS blind issuance",
    );
    ui.val(
        "attester anonymity",
        "DDH in G1 (Tag_DDH is a KI-PRF); perfect re-randomisation of PS",
    );
    ui.val(
        "predicate soundness",
        "key injectivity of the tag: distinct tags ⇒ distinct keys ⇒ distinct vetters",
    );
    ui.val(
        "self-exclusion",
        "T_0 ∉ {T_j}: bob cannot count himself even if he is a vetter",
    );
    ui.gap();
    ui.say("Caveats:");
    ui.say(
        "• Plain Fiat–Shamir: the theorems hold for sequential issuance and constant k. The VTC",
    );
    ui.say("  serialises its signing keys behind a lock; straight-line extraction is the paper's default.");
    ui.say("• Every received group element is subgroup-checked: the cofactor of BLS12-381 G1 is");
    ui.say("  divisible by 3, and T + P_3 would otherwise pass as a \"distinct\" tag.");
    ui.say("• This is an in-memory prototype: no transport, DIDs, persistence or JCS canonicalisation.");
    ui.gap();
    ui.say("Design: openvtc/docs/design/vetting-hidden-vetters-pcs.md");
    ui.say(
        "Code:   predicate-credential-system (src/pcs, src/cred/ps.rs, src/kiprf/ddh.rs), demo/",
    );
    ui.present(auto, clear);
}

/// The k = 2 submission in the wire form production uses (`vti-vetting-pcs::wire`,
/// mirrored in openvtc), then what is inside `proof`.
fn wire_stage(ui: &Ui, vtc: &Vtc, sub: &Submission) {
    let mb = |b: Vec<u8>| to_multibase(&b);
    let id_text = point_text(&sub.id).unwrap();
    let wire = json!({
        "suite": "ps-ddh-bls12381",
        "id": id_text,
        "joinDid": sub.join_did,
        "idBinding": id_binding(&id_text, &vtc.community, vtc.requirements_digest(), &sub.join_did),
        "challenge": sub.challenge,
        "statements": sub.statements.iter().map(|(meta, t)| json!({
            "meta": meta,
            "token": {
                "label": t.label,
                "serial": scalar_text(&t.serial).unwrap(),
                "shown": mb(to_bytes(&t.shown).unwrap()),
            },
        })).collect::<Vec<_>>(),
        "proof": mb(to_bytes(&sub.proof).unwrap()),
    });
    ui.say("The join request carries a VP with NO vetting credentials in it, and this member");
    ui.say("(binary values: multibase base58btc over the canonical compressed encoding):");
    ui.gap();
    ui.raw(&serde_json::to_string_pretty(&wire).unwrap());
    ui.gap();
    ui.say("Inside `proof`, π = ((att_j), C, T_0, π_0), byte by byte:");
    let len = |b: &[u8]| b.len();
    let mut total = 8; // the length prefix of the attestation list
    ui.val("k", &format!("{:>4} B   u64 length prefix", 8));
    for (j, a) in sub.proof.attestations.iter().enumerate() {
        let t = len(&to_bytes(&a.tag).unwrap());
        let c = len(&to_bytes(&a.shown).unwrap());
        let f = len(&to_bytes(&a.phi).unwrap());
        let p = len(&to_bytes(&a.proof).unwrap());
        total += t + c + f + p;
        ui.val(
            &format!("att_{}", j + 1),
            &format!(
                "{:>4} B   T_j {t} (G1) + cred*_j {c} (2×G1) + φ_j {f} (Fr) + π_j {p} (c, z_usk + u64 len)",
                t + c + f + p
            ),
        );
    }
    let c = len(&to_bytes(&sub.proof.encoding).unwrap());
    let t0 = len(&to_bytes(&sub.proof.t0).unwrap());
    let p0 = len(&to_bytes(&sub.proof.proof).unwrap());
    total += c + t0 + p0;
    ui.val("C", &format!("{c:>4} B   G1"));
    ui.val("T_0", &format!("{t0:>4} B   G1"));
    ui.val("π_0", &format!("{p0:>4} B   c, z_usk, z_ρ + u64 len"));
    ui.check(
        &format!("{total} B in total = the decoded length of `proof`"),
        total == to_bytes(&sub.proof).unwrap().len(),
    );
    ui.gap();
    ui.say("The VTC, in order: consume the challenge (single use) → decode, refusing any point off the");
    ui.say(
        "curve or outside the prime-order subgroup → rebuild app_j from each `meta` and app_0 from",
    );
    ui.say(
        "(challenge, audience, joinDid, idBinding) → VerifyProof under AllowList{live vetter φ} →",
    );
    ui.say(
        "per statement: token under tvk, serial into the spent set → StatementFacts → evaluate.",
    );
}

/// Build an applicant's submission, printing what goes into it.
fn submit_traced(ui: &Ui, vtc: &mut Vtc, app: &ApplicantEngine, rng: &mut StdRng) -> Submission {
    let c = vtc.challenge(rng);
    let sub = app.submit(vtc, &c, rng).unwrap();
    let k = sub.proof.attestations.len();
    let f = hidden_vetting_predicate(u32::try_from(k).unwrap_or(u32::MAX));
    ui.val("VTC challenge", &format!("{c}   (single use)"));
    ui.say(&format!(
        "π = ((att_j)_{{j≤{k}}}, C, T_0, π_0) for f_k = (k = {k}, \"{}\"), a VERIFY-ONLY predicate:",
        String::from_utf8_lossy(&f.label)
    ));
    ui.say("the VTC checks π as an issuance proof and admits on it, but never issues a credential under f_k.");
    ui.math("C   = g_1^ρ · Y_1^usk_B");
    ui.math("T_0 = H_2(s_B)^usk_B                                           (self-exclusion tag)");
    ui.math(
        "π_0 : PoK{ (usk_B, ρ) : C = g_1^ρ Y_1^usk_B ∧ id_B = g_1^usk_B ∧ T_0 = H_2(s_B)^usk_B }",
    );
    ui.math("      under ctx_0 = H(pp, hvk, f_k, id_B, C, T_0, att_1..k, app_1..k, app_0)");
    ui.math(
        "app_0 = (challenge, audience, joinDid, H(id_B, community, requirementsDigest, joinDid))",
    );
    ui.val("C", &hx(&sub.proof.encoding));
    ui.val("T_0", &hx(&sub.proof.t0));
    for a in &sub.proof.attestations {
        ui.val("T_j", &hx(&a.tag));
    }
    ui.val("|π|", &format!("{} B", to_bytes(&sub.proof).unwrap().len()));
    ui.check(
        "T_0 recomputed from usk_B",
        vtc.open()
            .tag()
            .eval(app.usk_scalar(), &vtc.open().tag_point(app.id()).unwrap())
            == Some(sub.proof.t0),
    );
    ui.say(
        "VTC: rebuilds every context from public data (never takes context bytes from bob), then",
    );
    ui.math("CheckAtts_P:  every att_j verifies ∧ T_j pairwise distinct ∧ T_0 ∉ {T_j} ∧ P(φ_1..φ_k) = 1");
    ui.say("…then per statement: token signature under tvk, serial into the spent set, metadata → facts.");
    sub
}
