//! The walkthrough as data: the flow of `examples/walkthrough.rs`, stage by stage, with every
//! value registered and every equation recomputed.
//!
//! The engines are called in exactly the order the terminal walkthrough calls them, and the
//! extra work done here (recomputing equations, pairings, re-encoding) draws no randomness, so
//! for the same seed every value on the page equals the one the terminal prints.
//!
//! Each stage is a flow of numbered actions in the order the engines ran them. Each action names
//! the engine calls it made, so the page can show them running, and each message carries its
//! content as JSON: the submission in its wire form, the VTC's answer in the shape of the join
//! ceremony's verdict, and every other message as the in-memory object it is, written out by the
//! crate's `serde` layer (multibase base58btc leaves). A ledger records who holds what after
//! each stage, and how each application stands against the policy.

use std::error::Error;

use ark_bls12_381::{Bls12_381, Fq, G2Projective};
use ark_ec::{PrimeGroup, pairing::Pairing, pairing::PairingOutput};
use ark_ff::PrimeField;
use chrono::{DateTime, NaiveDate, TimeZone, Utc};
use pcs_vetting_prototype::{
    applicant::ApplicantEngine,
    meta::{StatementMeta, id_binding},
    scheme::{
        E, Fr, G1, deployment_label, point_text, scalar_text, token_deployment_label,
        vetter_predicate,
    },
    token::TokenParams,
    trace,
    vetter::{HiddenAttestation, VetterEngine},
    vtc::{Decision, Submission, Vtc},
};
use predicate_credential_system::{
    cred::ps::PSVerificationKey,
    kiprf::KIPRF,
    serialization::{to_bytes, to_multibase},
    sigma::{LinearRelation, fiat_shamir},
};
use rand::{SeedableRng, rngs::StdRng};
use serde_json::{Value as J, json};
use vta_sdk::protocols::vetting::{
    IDENTITY_VETTING_ENDORSEMENT_TYPE, VettingMethod, VettingRelationship,
};

use crate::model::{
    Check, Fig, Ledger, Run, Stage, Val, checks, derive, goal, hex, line, line_md, line_ok,
};

pub type R<T> = Result<T, Box<dyn Error>>;

pub const COMMUNITY: &str = "did:example:kernel-vtc";
pub const PERIOD: &str = "2026-09";
/// The terminal walkthrough's seed: with it, both show the same values.
pub const DEFAULT_SEED: u64 = 7;

pub const PHASES: [&str; 9] = [
    "Overview",
    "Setup",
    "Enrolment",
    "Vetting",
    "Admission",
    "Privacy",
    "Abuse",
    "Withdrawal",
    "Summary",
];

pub fn now() -> DateTime<Utc> {
    Utc.with_ymd_and_hms(2026, 9, 22, 12, 0, 0).unwrap()
}

pub fn requirements() -> J {
    json!({
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
    })
}

pub fn meta(app: &ApplicantEngine, vtc: &Vtc, method: VettingMethod) -> StatementMeta {
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

/// One vetting session: accept (reserves a token), human check, attest.
pub fn vet(
    vtc: &Vtc,
    v: &mut VetterEngine,
    app: &ApplicantEngine,
    method: VettingMethod,
    rng: &mut StdRng,
) -> R<HiddenAttestation> {
    let r = v.accept(None, 2)?;
    let m = meta(app, vtc, method);
    Ok(v.attest(vtc, &r, app.id(), m, rng)?)
}

pub fn pair(a: &G1, b: &G2Projective) -> PairingOutput<E> {
    Bls12_381::pairing(*a, *b)
}

/// Both sides of `e(σ_1, X̃ Ỹ_1^{m_1} Ỹ_2^{m_2}) = e(σ_2, g̃)`.
pub fn ps_sides(
    vk: &PSVerificationKey<E>,
    m1: &Fr,
    m2: &Fr,
    s1: &G1,
    s2: &G1,
) -> (PairingOutput<E>, PairingOutput<E>) {
    let rhs = vk.x_tilde + vk.y1_tilde * m1 + vk.y2_tilde * m2;
    (pair(s1, &rhs), pair(s2, &G2Projective::generator()))
}

pub fn len<T: ark_serialize::CanonicalSerialize + ?Sized>(v: &T) -> usize {
    to_bytes(v).map(|b| b.len()).unwrap_or(0)
}

/// The JSON form of a protocol object, through the crate's `serde` layer.
fn sj<T: serde::Serialize + ?Sized>(v: &T) -> R<J> {
    Ok(serde_json::to_value(v)?)
}

/// The submission as the VTC receives it (`vti-vetting-pcs::wire`, mirrored in openvtc).
pub fn wire_json(vtc: &Vtc, sub: &Submission) -> R<J> {
    let mb = |b: Vec<u8>| to_multibase(&b);
    let id_text = point_text(&sub.id)?;
    let mut statements = Vec::new();
    for (m, t) in &sub.statements {
        statements.push(json!({
            "meta": m,
            "token": {
                "label": t.label,
                "serial": scalar_text(&t.serial)?,
                "shown": mb(to_bytes(&t.shown)?),
            },
        }));
    }
    Ok(json!({
        "suite": "ps-ddh-bls12381",
        "id": id_text,
        "joinDid": sub.join_did,
        "idBinding": id_binding(&id_text, &vtc.community, vtc.requirements_digest(), &sub.join_did),
        "challenge": sub.challenge,
        "statements": statements,
        "proof": mb(to_bytes(&sub.proof)?),
    }))
}

/// The VTC's answer to a submission, in the shape of the join ceremony's `Verdict`
/// (`vta-sdk`, `protocols::join_requests`: an `effect` and its `with`), as a policy that admits
/// on the count alone would give it.
pub fn verdict_json(d: &Decision) -> J {
    if d.evaluation.satisfied() {
        json!({ "effect": "allow", "with": {} })
    } else {
        json!({
            "effect": "requestMore",
            "with": { "needs": d.evaluation.needs.iter().map(|n| n.to_wire()).collect::<Vec<_>>() },
        })
    }
}

/// An attestation as a vetter's engine hands it over, with its metadata and spent token.
fn attestation_json(h: &HiddenAttestation) -> R<(J, usize)> {
    let j = json!({
        "attestation": sj(&h.attestation)?,
        "meta": sj(&h.meta)?,
        "token": {
            "label": h.token.label,
            "serial": scalar_text(&h.token.serial)?,
            "shown": sj(&h.token.shown)?,
        },
    });
    let n = len(&h.attestation) + len(&h.token.serial) + len(&h.token.shown);
    Ok((j, n))
}

/// The applicant asks a vetter for a statement: his identifier and the part of the metadata he
/// fills (`ApplicantEngine::statement_meta`).
fn vetting_request_json(vtc: &Vtc, id: &G1) -> R<J> {
    Ok(json!({
        "id": point_text(id)?,
        "template": {
            "community": vtc.community,
            "requirementsDigest": vtc.requirements_digest(),
        },
    }))
}

/// Register the values of an attestation that its JSON quotes, so the JSON links to them.
fn register_attestation(run: &mut Run, key: &str, tex: &str, h: &HiddenAttestation) -> R<()> {
    run.val(
        Val::encoded(
            &format!("{key}.shown"),
            &format!(r"\cred^*_{tex}"),
            "G1",
            &to_bytes(&h.attestation.shown)?,
        )
        .note("$(\\sigma'_1, \\sigma'_2)$, the re-randomised credential: two $\\G_1$ points in one encoding."),
    );
    run.val(
        Val::encoded(
            &format!("{key}.tok.shown"),
            r"\sigma'^{\mathrm{tok}}",
            "G1",
            &to_bytes(&h.token.shown)?,
        )
        .note("The spent token's re-randomised signature: two $\\G_1$ points in one encoding."),
    );
    Ok(())
}

/// The VTC's handling of a submission, timed as one call with the inner calls nested.
pub fn vtc_submit(
    vtc: &mut Vtc,
    sub: &Submission,
) -> Result<Decision, pcs_vetting_prototype::ProtoError> {
    trace::span(
        "VTC",
        "Vtc::submit",
        "consume the challenge, rebuild every context, VerifyProof, tokens, facts, count",
        || vtc.submit(sub, now()),
    )
}

/// What the run looks like at the point every lab experiment starts from: bob admitted on
/// carol's and alice's attestations (step 9).
pub struct World {
    pub rng: StdRng,
    pub vtc: Vtc,
    pub vetters: Vec<VetterEngine>,
    pub bob: ApplicantEngine,
    pub a_carol: HiddenAttestation,
    pub a_alice: HiddenAttestation,
    pub sub2: Submission,
    pub ledger: Ledger,
}

pub fn actors() -> J {
    json!({
        "vtc": { "name": "VTC", "role": "the community, PCS helper" },
        "public": { "name": "everyone", "role": "members and applicants" },
        "vetters": { "name": "vetters", "role": "alice, carol, dave" },
        "alice": { "name": "alice", "role": "vetter" },
        "carol": { "name": "carol", "role": "vetter" },
        "dave": { "name": "dave", "role": "vetter" },
        "bob": { "name": "bob", "role": "applicant" },
        "eve": { "name": "eve", "role": "applicant" },
        "frank": { "name": "frank", "role": "applicant" },
        "alice-2": { "name": "alice-2", "role": "alice's second persona" },
        "mallory": { "name": "mallory", "role": "not a vetter" },
        "walkthrough": { "name": "walkthrough", "role": "peeks at secrets" },
    })
}

fn tokens_md(v: &VetterEngine, label: &str) -> String {
    let n = v.tokens_held();
    format!("{n} token{} for `{label}`", if n == 1 { "" } else { "s" })
}

// ---------------------------------------------------------------------------------------------
// Stages 1-10: up to bob's admission
// ---------------------------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
pub fn admitted(seed: u64) -> R<(Run, World)> {
    let mut run = Run::default();
    let mut ledger = Ledger::default();
    let mut rng = StdRng::seed_from_u64(seed);
    let g1 = G1::generator();
    let g2 = G2Projective::generator();

    // ── 1 · intro: built last, in `full`, so that its map of messages can quote their sizes ───

    // ── 2 · setup ──────────────────────────────────────────────────────────────────────────
    let (vtc, calls) = trace::record(|| Vtc::new(COMMUNITY, PERIOD, requirements(), &mut rng));
    let mut vtc = vtc?;
    let hvk = vtc.hvk().clone();
    let tparams = TokenParams::new(COMMUNITY)?;
    let tlabel = vtc.current_token_label().to_string();
    let phi_t = tparams.phi(&tlabel)?;
    {
        let open = vtc.open();
        let label = String::from_utf8_lossy(&deployment_label(COMMUNITY)).to_string();
        run.val(
            Val::text("pp.label", r"\textsf{label}", &label)
                .who(&["public"])
                .note("The deployment label. Every public parameter is derived from it."),
        );
        run.val(
            Val::bytes("pp.digest", r"\mathrm{digest}(\mathsf{pp})", open.parameters_digest())
                .who(&["public"])
                .note("Leads every Fiat–Shamir context ($\\ctx_j$, $\\ctx_0$, $\\ctx_{\\mathrm{root}}$): $H_1$ sees the deployment only through it."),
        );
        run.val(
            Val::fr("pp.c0", "c_0", open.identity_point())
                .who(&["public"])
                .note("$c_0 = H_0(\\texttt{\"identity\"})$. $H_2$ is programmed so that $H_2(c_0) = g_1$, so every identifier is $g_1^{usk}$."),
        );
        run.val(
            Val::hidden("hsk", r"\mathsf{hsk}", "Fr")
                .who(&["vtc"])
                .note("$(x, y_1, y_2)$, kept inside the VTC. The walkthrough never reads it."),
        );
        run.val(
            Val::g2("hvk.Xt", r"\tilde X", &hvk.x_tilde)
                .who(&["public"])
                .note("$\\tilde g^{x}$"),
        );
        run.val(
            Val::g2("hvk.Y1t", r"\tilde Y_1", &hvk.y1_tilde)
                .who(&["public"])
                .note("$\\tilde g^{y_1}$"),
        );
        run.val(
            Val::g2("hvk.Y2t", r"\tilde Y_2", &hvk.y2_tilde)
                .who(&["public"])
                .note("$\\tilde g^{y_2}$"),
        );
        run.val(
            Val::g1("hvk.Y1", "Y_1", &hvk.y1)
                .who(&["public"])
                .note("$g_1^{y_1}$: the base of $usk$ in every commitment $C$"),
        );
        run.val(
            Val::bytes_mb("hvk", r"\hvk", &to_bytes(&hvk)?)
                .who(&["public"])
                .note("The whole key $(\\tilde X, \\tilde Y_1, \\tilde Y_2, Y_1)$ in one canonical encoding, as the manifest carries it."),
        );
        run.val(Val::gt(
            "setup.lhs",
            r"e(Y_1, \tilde g)",
            &pair(&hvk.y1, &g2),
        ));
        run.val(Val::gt(
            "setup.rhs",
            r"e(g_1, \tilde Y_1)",
            &pair(&g1, &hvk.y1_tilde),
        ));
        let phis = vtc.live_vetter_phis()?;
        run.val(
            Val::fr("phi.v", r"\varphi_{v}", &phis[0])
                .who(&["public"])
                .note("$\\EncPred$ of the root predicate $(0, \\texttt{vetter/2026-09})$: the class a vetter credential certifies. Public, and not hiding."),
        );
        let tvk = vtc.tokens.tvk().clone();
        run.val(
            Val::bytes_mb("tvk", r"\tvk", &to_bytes(&tvk)?)
                .who(&["public"])
                .note("The token key $(\\tilde X_t, \\tilde Y_{1,t}, \\tilde Y_{2,t}, Y_{1,t})$: a second PS key, never $\\hvk$."),
        );
        run.val(Val::text("tok.deploy", r"\textsf{token label}", &String::from_utf8_lossy(&token_deployment_label(COMMUNITY))).who(&["public"]).note("The token deployment: its own $\\mathsf{pp}$, so $\\varphi_{\\mathrm{tok}}$ can never collide with a vetter class."));
        run.val(Val::text("tok.label", r"\textsf{token/2026-09}", &tlabel).who(&["public"]));
        run.val(
            Val::fr("tok.phi", r"\varphi_{\mathrm{tok}}", &phi_t)
                .who(&["public"])
                .note("$\\EncPred$ of the token label under the token deployment."),
        );
        run.val(
            Val::g1("tvk.Y1", r"Y_{1,t}", &tvk.y1)
                .who(&["public"])
                .note("$g_1^{y_{1,t}}$ of the token key $\\tvk$: the base of the serial in a token commitment."),
        );
        let manifest = json!({
            "suite": "ps-ddh-bls12381",
            "deployment": label,
            "parametersDigest": hex(open.parameters_digest()),
            "hvk": sj(&hvk)?,
            "liveClasses": [{ "label": format!("vetter/{PERIOD}"), "phi": scalar_text(&phis[0])? }],
            "tokens": {
                "deployment": String::from_utf8_lossy(&token_deployment_label(COMMUNITY)),
                "labels": [tlabel],
                "tvk": sj(&tvk)?,
            },
            "requirements": requirements(),
        });
        let published = len(&hvk) + len(&tvk) + len(&phis[0]) + 32;

        let mut s = Stage::new(
            "setup",
            "Setup",
            "Public parameters and the community's key",
            "VTC",
            "Everything public is derived from one fixed deployment label. The VTC then generates \
             the long-lived key that will sign every vetter's credential, a second key for \
             tokens, and publishes both with its policy.",
        );
        s.parties(&["vtc", "public"]);
        s.fig(
            Fig::new(&["vtc", "public"], "Setup, HKeyGen and the token key, run once by the VTC.")
                .step("vtc", "runs Setup: every public parameter, derived from its deployment label")
                .uses(&["PCS::setup"])
                .act("vtc", r"\mathsf{pp} = (\mathsf{pp}_{\Sigma}, \mathsf{pp}_{\mathsf{Tag}}, \EncPred, H_0, H_1, c_0) \gets \mathsf{Setup}(\V{pp.label}{\textsf{label}})", &["pp.label", "pp.digest"])
                .act("vtc", r"\V{pp.c0}{c_0} := H_0(\str{identity}), \qquad H_2(c_0) := \gone", &["pp.c0"])
                .aside("$H_0$ and $H_2$ are domain-separated by the label; $H_1$ (Fiat–Shamir) sees it through $\\mathrm{digest}(\\mathsf{pp})$, which leads every context")
                .step("vtc", "runs HKeyGen, which is PS KeyGen: the Pointcheval–Sanders key pair that will sign every vetter credential")
                .uses(&["PCS::helper_keygen"])
                .act("vtc", r"\mathsf{hsk} = \V{hsk}{(x,\, y_1,\, y_2)} \sample \Z_p \times (\Z_p^{*})^{2}", &["hsk"])
                .act(
                    "vtc",
                    r"\hvk := (\V{hvk.Xt}{\tilde X}, \V{hvk.Y1t}{\tilde Y_1}, \V{hvk.Y2t}{\tilde Y_2}, \V{hvk.Y1}{Y_1}) = (\gtil^{x}, \gtil^{y_1}, \gtil^{y_2}, \gone^{y_1})",
                    &["hvk.Xt", "hvk.Y1t", "hvk.Y2t", "hvk.Y1"],
                )
                .aside("the PS public key for two messages, $usk$ (hidden) and $\\varphi$ (public): $\\tilde X, \\tilde Y_1, \\tilde Y_2$ verify signatures, and $Y_1 = g_1^{y_1}$ is the base of $usk$ in the commitment $C$ that blind issuance signs")
                .check(
                    "vtc",
                    r"\tilde Y_1 \ne 1,\ \ \tilde Y_2 \ne 1,\ \ e(\V{hvk.Y1}{Y_1}, \gtil) = e(\gone, \V{hvk.Y1t}{\tilde Y_1})",
                    hvk.is_well_formed(),
                    "$\\hvk$ is in the range of KeyGen, so a credential under it binds a key",
                )
                .detail(checks(
                    "Both sides of the pairing equation",
                    vec![
                        Check::new(hvk.is_well_formed(), "$\\hvk$ is well formed: one pairing product")
                            .tex(r"e(\V{hvk.Y1}{Y_1}, \gtil) = e(\gone, \V{hvk.Y1t}{\tilde Y_1})")
                            .sides("setup.lhs", "setup.rhs")
                            .by("anyone, from public data"),
                    ],
                ))
                .step("vtc", "sets its policy: only credentials of the live period count")
                .uses(&["PCS::allow_list"])
                .act(
                    "vtc",
                    r"\V{phi.v}{\varphi_v} := \EncPred(f_{\mathrm{root}}) = H_0\bigl(\str{predicate} \,\|\, \langle 0, \str{vetter/2026-09} \rangle\bigr)",
                    &["phi.v"],
                )
                .act("vtc", r"P := \mathsf{AllowList}\{\V{phi.v}{\varphi_v}\}", &[])
                .aside("never the default $P \\equiv 1$: only credentials of a live period count")
                .step("vtc", "runs PS KeyGen again: an independent Pointcheval–Sanders key pair, for attestation tokens")
                .uses(&["TokenIssuer::new"])
                .act(
                    "vtc",
                    r"(\V{tvk}{\tvk}, \tsk) \gets \mathsf{PS.KeyGen}, \quad \V{tok.phi}{\varphi_{\mathrm{tok}}} := \EncPred(\V{tok.label}{\textsf{token/2026-09}})",
                    &["tvk", "tok.phi"],
                )
                .aside("a separate key, because under $\\hvk$ a signature on $(s, \\varphi)$ would be a vetter credential whose “$usk$” $s$ the vetter knows; and a deployment label of its own, so a token class never collides with a vetter class")
                .step("vtc", "publishes what everyone needs to check credentials and tokens")
                .send(
                    "vtc",
                    "public",
                    r"(\V{hvk}{\hvk},\ \V{tvk}{\tvk},\ \V{phi.v}{\varphi_v},\ \text{requirements})",
                    &["hvk", "tvk", "phi.v"],
                    Some(published),
                )
                .named("the vetting entries of its manifest")
                .json("memory", &manifest)
                .highlight(&["hvk", "liveClasses", "minStatements", "minByMethod"])
                .aside("the code places these in the join manifest's `vetting.anonymity` member; the prototype keeps them in memory, so the field names are its own"),
        );
        s.outcome(
            "info",
            "Set up",
            "The VTC alone holds its two signing keys, $\\mathsf{hsk}$ and $\\mathsf{tsk}$. \
             Anyone can now check a vetter credential against $\\hvk$ and a token against \
             $\\tvk$, and read the policy the VTC counts with: two vetters, one of them in \
             person.",
        );
        s.section("In detail");
        let gt1 = pair(&g1, &g2);
        s.table(
            "The groups of BLS12-381, as encoded here",
            &["group", "what it is", "compressed"],
            vec![
                vec![
                    "$\\G_1$".into(),
                    format!("points of $E(\\mathbb{{F}}_q)$ of prime order $p$; generator $g_1$; $q$ has {} bits", Fq::MODULUS_BIT_SIZE),
                    format!("{} B", len(&g1)),
                ],
                vec!["$\\G_2$".into(), "points of the twist $E'(\\mathbb{F}_{q^2})$ of order $p$; generator $\\tilde g$".into(), format!("{} B", len(&g2))],
                vec!["$\\G_T$".into(), "the order-$p$ subgroup of $\\mathbb{F}_{q^{12}}^{*}$; $e : \\G_1 \\times \\G_2 \\to \\G_T$ (type 3)".into(), format!("{} B", len(&gt1))],
                vec!["$\\Z_p$".into(), format!("scalars; $p$ has {} bits", Fr::MODULUS_BIT_SIZE), format!("{} B", len(&Fr::from(1u64)))],
            ],
        );
        s.callout(
            "info",
            "The epoch lives in the class label `vetter/<period>`, not in $\\mathsf{pp}$. \
             Identifiers stay fixed across rotations, and one proof may mix attestations from \
             two live periods.",
        );
        s.calls(calls);
        s.lab(&["rotation"]);
        ledger.set(
            "vtc",
            "keys",
            r"$\mathsf{hsk}$ and $\mathsf{tsk}$, its two signing keys",
            true,
        );
        ledger.set("public", "keys", r"$\mathsf{pp}$, $\hvk$ and $\tvk$", false);
        ledger.set(
            "public",
            "policy",
            r"the live class $\varphi_v$ and the requirements: 2 vetters, 1 in person",
            false,
        );
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 3 · a vetter's key ─────────────────────────────────────────────────────────────────
    let (vetters, calls) = trace::record(|| -> R<Vec<VetterEngine>> {
        let mut out = Vec::new();
        for name in ["alice", "carol", "dave"] {
            vtc.grant(name);
            out.push(VetterEngine::new(name, &vtc, &mut rng)?);
        }
        Ok(out)
    });
    let mut vetters = vetters?;
    let alice_usk = *vetters[0].usk_scalar();
    let alice_id = *vetters[0].id();
    {
        run.val(
            Val::fr("alice.usk", r"\usk_A", &alice_usk)
                .secret()
                .who(&["alice"])
                .note("alice's secret key, for life. Read through a demo hook."),
        );
        for (i, (name, letter)) in [("alice", "A"), ("carol", "C"), ("dave", "D")]
            .iter()
            .enumerate()
        {
            let v = &vetters[i];
            run.val(
                Val::g1(&format!("{name}.id"), &format!("id_{letter}"), v.id())
                    .who(&[name, "vtc"])
                    .note(&format!("{name}'s identifier $g_1^{{usk_{letter}}}$; the VTC binds it to her member record at enrolment.")),
            );
        }
        let ok = alice_id == g1 * alice_usk
            && vtc
                .open()
                .tag()
                .eval(&alice_usk, vtc.open().identity_point())
                == Some(alice_id);
        let mut s = Stage::new(
            "vetter-key",
            "Enrolment",
            "A vetter's key: one usk for life",
            "the VTAs of alice, carol and dave (each vetter's PCS engine)",
            "The community has three vetters: alice, carol and dave. Each needs a key of their \
             own. Its identifier is what the VTC binds to the vetter's member record at \
             enrolment, and the key is what makes the vetter's tags differ from every other \
             vetter's, so that two vetters count as two. The same key serves in every period, so \
             a vetter's tags never change.",
        );
        s.parties(&["vtc", "alice", "carol", "dave"]);
        s.fig(
            Fig::new(
                &["vtc", "alice", "carol", "dave"],
                "UKeyGen, run by each vetter's engine.",
            )
            .step(
                "vtc",
                "gives three members the vetter role: alice, carol and dave",
            )
            .say(
                "vtc",
                "member records: alice, carol and dave hold the vetter role",
            )
            .aside("who may enrol is the community's decision, outside the scheme")
            .step(
                "alice",
                "draws her secret key, once for life, and derives her identifier",
            )
            .uses(&["PCS::user_keygen"])
            .act(
                "alice",
                r"\V{alice.usk}{\usk_A} \sample \Z_p^{*}",
                &["alice.usk"],
            )
            .act(
                "alice",
                r"\V{alice.id}{id_A} := \Tag(\usk_A, c_0) = H_2(c_0)^{\usk_A} = \gone^{\usk_A}",
                &["alice.id"],
            )
            .check(
                "alice",
                r"\V{alice.id}{id_A} = \gone^{\V{alice.usk}{\usk_A}}",
                ok,
                "recomputed from her key",
            )
            .step(
                "carol",
                "does the same: an independent key, and its identifier",
            )
            .uses(&["PCS::user_keygen"])
            .act(
                "carol",
                r"\usk_C \sample \Z_p^{*}, \quad \V{carol.id}{id_C} := \gone^{\usk_C}",
                &["carol.id"],
            )
            .step(
                "dave",
                "does the same: an independent key, and its identifier",
            )
            .uses(&["PCS::user_keygen"])
            .act(
                "dave",
                r"\usk_D \sample \Z_p^{*}, \quad \V{dave.id}{id_D} := \gone^{\usk_D}",
                &["dave.id"],
            ),
        );
        s.outcome(
            "info",
            "Three vetters, three keys",
            "alice, carol and dave each hold a secret key, and their identifiers are public. \
             Nothing has been sent yet: the VTC binds each identifier to its member record at \
             enrolment, in the next step. Later, carol and alice vouch for bob (steps 6 and 9), \
             and dave plays the cheat in the double-spend case (step 12).",
        );
        s.section("Why one key for life");
        s.p(
            "The VTC binds $id_A$ to alice's member record at her first enrolment and refuses any \
             other identifier for her afterwards. This is the Sybil defence: one member, one \
             key. So a vetter has one tag per applicant, and counts once per applicant, however \
             many periods she enrols in.",
        );
        s.calls(calls);
        s.lab(&["twin-key"]);
        ledger.set(
            "vtc",
            "grants",
            "the vetter role: alice, carol, dave",
            false,
        );
        for (name, l) in [("alice", "A"), ("carol", "C"), ("dave", "D")] {
            ledger.set(name, "usk", &format!(r"$\usk_{l}$"), true);
            ledger.set(name, "id", &format!(r"$id_{l} = g_1^{{\usk_{l}}}$"), false);
        }
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 4 · root credential ────────────────────────────────────────────────────────────────
    let phi_v = vtc.open().enc_pred(&vetter_predicate(PERIOD))?;
    let (enrolled, calls) = trace::record(|| -> R<_> {
        let t = vetters[0].enroll_traced(&mut vtc, &mut rng)?;
        for v in vetters.iter_mut().skip(1) {
            v.enroll(&mut vtc, &mut rng)?;
        }
        Ok(t)
    });
    let etrace = enrolled?;
    {
        let cred = vetters[0]
            .credential(PERIOD)
            .ok_or("alice has no credential")?
            .cred
            .clone();
        let f_root = vetter_predicate(PERIOD);
        let root_ok = vtc
            .open()
            .verify_root_request(&hvk, &f_root, &alice_id, &etrace.request);
        run.val(Val::hidden("alice.rho", r"\rho", "Fr").who(&["alice"]).note("The blinding scalar. Kept in alice's issuance state; not exposed, even to the walkthrough."));
        run.val(Val::g1("alice.C", "C", &etrace.request.encoding).who(&["alice", "vtc"]).note("A Pedersen-style commitment to $usk_A$: perfectly hiding, so the VTC learns nothing about the key."));
        run.val(
            Val::g1("alice.T0", "T_0", &etrace.request.t0)
                .who(&["alice", "vtc"])
                .note("alice's tag at her own point $s_A = H_0(id_A)$."),
        );
        run.val(
            Val::proof(
                "alice.piroot",
                r"\pi_{\mathrm{root}}",
                &etrace.request.proof,
            )
            .who(&["alice", "vtc"]),
        );
        run.val(
            Val::g1("alice.hs1", r"\hat\sigma_1", &etrace.pre.sigma_1)
                .who(&["alice", "vtc"])
                .note("$g_1^{u}$ for a fresh $u$."),
        );
        run.val(Val::g1("alice.hs2", r"\hat\sigma_2", &etrace.pre.sigma_2).who(&["alice", "vtc"]));
        run.val(
            Val::encoded("alice.hs", r"\hat\sigma", "G1", &to_bytes(&etrace.pre)?)
                .who(&["alice", "vtc"])
                .note("$(\\hat\\sigma_1, \\hat\\sigma_2)$ in one encoding: two $\\G_1$ points."),
        );
        run.val(Val::g1("alice.s1", r"\sigma_1", &cred.sigma_1).secret().who(&["alice"]).note("Equal to $\\hat\\sigma_1$, which the VTC sent. Showing $\\sigma$ as is would identify alice, so every attestation re-randomises it."));
        run.val(
            Val::g1("alice.s2", r"\sigma_2", &cred.sigma_2)
                .secret()
                .who(&["alice"])
                .note("$\\hat\\sigma_2 / \\hat\\sigma_1^{\\rho}$: the VTC has never seen it."),
        );
        let (l, r) = ps_sides(&hvk, &alice_usk, &phi_v, &cred.sigma_1, &cred.sigma_2);
        run.val(Val::gt(
            "alice.lhs",
            r"e(\sigma_1, \tilde X \tilde Y_1^{usk_A} \tilde Y_2^{\varphi})",
            &l,
        ));
        run.val(Val::gt("alice.rhs", r"e(\sigma_2, \tilde g)", &r));
        let (l2, r2) = ps_sides(
            &hvk,
            &alice_usk,
            &(phi_v + Fr::from(1u64)),
            &cred.sigma_1,
            &cred.sigma_2,
        );
        run.val(Val::gt(
            "alice.lhs2",
            r"e(\sigma_1, \tilde X \tilde Y_1^{usk_A} \tilde Y_2^{\varphi + 1})",
            &l2,
        ));
        run.val(Val::gt("alice.rhs2", r"e(\sigma_2, \tilde g)", &r2));
        let request = json!({
            "member": "alice",
            "id": point_text(&alice_id)?,
            "request": sj(&etrace.request)?,
        });
        let request_len = len(&alice_id) + len(&etrace.request);

        let mut s = Stage::new(
            "root-credential",
            "Enrolment",
            "Blind issuance of a root credential",
            "alice ⇄ VTC",
            "alice obtains a Pointcheval–Sanders signature on $(usk_A, \\varphi_v)$ without \
             revealing $usk_A$. She sends a commitment, the VTC signs it blind, and she unblinds \
             the result.",
        );
        s.parties(&["alice", "vtc", "carol", "dave"]);
        s.fig(
            Fig::new(&["alice", "vtc", "carol", "dave"], "Root enrolment: a root request, BlindIssue, Unblind.")
                .step("alice", "commits to her key, and proves that one key is behind everything she sends")
                .uses(&["PCS::root_request"])
                .act("alice", r"f_{\mathrm{root}} := (0, \str{vetter/2026-09}), \quad \varphi := \EncPred(f_{\mathrm{root}})", &["phi.v"])
                .act("alice", r"\V{alice.rho}{\rho} \sample \Z_p, \quad \V{alice.C}{C} := \gone^{\rho} \cdot \V{hvk.Y1}{Y_1}^{\usk_A}", &["alice.rho", "alice.C"])
                .act("alice", r"s_A := H_0(id_A), \quad \V{alice.T0}{T_0} := H_2(s_A)^{\usk_A}", &["alice.T0"])
                .act(
                    "alice",
                    r"\V{alice.piroot}{\pi_{\mathrm{root}}} \gets \PoK_{\ctx_{\mathrm{root}}}\bigl\{(\usk, \rho) : C = \gone^{\rho} Y_1^{\usk} \wedge id_A = \gone^{\usk} \wedge T_0 = H_2(s_A)^{\usk}\bigr\}",
                    &["alice.piroot"],
                )
                .send(
                    "alice",
                    "vtc",
                    r"(\V{alice.id}{id_A},\ \V{alice.C}{C},\ \V{alice.T0}{T_0},\ \V{alice.piroot}{\pi_{\mathrm{root}}})",
                    &["alice.id", "alice.C", "alice.T0", "alice.piroot"],
                    Some(request_len),
                )
                .named("the root request")
                .json("memory", &request)
                .step("vtc", "checks the request and the grant, then signs blind (PS BlindIssue)")
                .uses(&["Vtc::issue_vetter_root"])
                .check("vtc", r"\VerifyFS(\ctx_{\mathrm{root}}, \V{alice.piroot}{\pi_{\mathrm{root}}}) = 1", root_ok, "$C$, $id_A$ and $T_0$ are under one key, which alice knows")
                .say("vtc", "alice holds the vetter grant; $id_A$ is bound to alice (first enrolment); she holds no credential yet under `vetter/2026-09`")
                .aside("policy checks outside the scheme: the request proves one key, not that the key should be admitted")
                .act(
                    "vtc",
                    r"u \sample \Z_p^{*}, \quad (\V{alice.hs1}{\hat\sigma_1}, \V{alice.hs2}{\hat\sigma_2}) := \bigl(\gone^{u},\ (\gone^{x} \cdot C \cdot \gone^{y_2 \varphi})^{u}\bigr)",
                    &["alice.hs1", "alice.hs2"],
                )
                .aside("the VTC never sees $usk_A$; $\\varphi$ enters only here, as $g_1^{y_2\\varphi}$")
                .send("vtc", "alice", r"\V{alice.hs}{\hat\sigma} = (\V{alice.hs1}{\hat\sigma_1}, \V{alice.hs2}{\hat\sigma_2})", &["alice.hs"], Some(len(&etrace.pre)))
                .named("the blind signature")
                .json("memory", &json!({ "preCredential": sj(&etrace.pre)? }))
                .step("alice", "unblinds the signature (PS Unblind), and keeps it only if it verifies")
                .uses(&["PCS::unblind"])
                .act(
                    "alice",
                    r"\sigma := (\V{alice.s1}{\sigma_1}, \V{alice.s2}{\sigma_2}) = (\hat\sigma_1,\ \hat\sigma_2 \cdot \hat\sigma_1^{-\rho}) = \bigl(h,\ h^{x + y_1 \usk_A + y_2 \varphi}\bigr)",
                    &["alice.s1", "alice.s2"],
                )
                .aside("with $h = g_1^{u}$: a PS signature on $(usk_A, \\varphi)$")
                .check("alice", r"e(\sigma_1, \tilde X \tilde Y_1^{\usk_A} \tilde Y_2^{\varphi}) = e(\sigma_2, \gtil)", l == r, "Unblind keeps $\\sigma$ only if it verifies")
                .detail(checks(
                    "Checked live",
                    vec![
                        Check::new(l == r, "a PS signature on $(usk_A, \\varphi)$")
                            .tex(r"e(\V{alice.s1}{\sigma_1}, \V{hvk.Xt}{\tilde X}\, \V{hvk.Y1t}{\tilde Y_1}^{\V{alice.usk}{\usk_A}}\, \V{hvk.Y2t}{\tilde Y_2}^{\V{phi.v}{\varphi}}) = e(\V{alice.s2}{\sigma_2}, \gtil)")
                            .sides("alice.lhs", "alice.rhs")
                            .by("walkthrough, with alice's key"),
                        Check::new(l2 != r2, "and not on any other class: here $\\varphi' = \\varphi + 1$")
                            .tex(r"e(\sigma_1, \tilde X \tilde Y_1^{\usk_A} \tilde Y_2^{\varphi + 1}) \ne e(\sigma_2, \gtil)")
                            .sides("alice.lhs2", "alice.rhs2")
                            .by("walkthrough, with alice's key"),
                        Check::new(cred.sigma_1 == etrace.pre.sigma_1, "$\\sigma_1 = \\hat\\sigma_1$: the VTC knows the first half of alice's credential")
                            .tex(r"\V{alice.s1}{\sigma_1} = \V{alice.hs1}{\hat\sigma_1}")
                            .by("walkthrough"),
                    ],
                ))
                .step("carol", "enrols the same way, with her own key")
                .uses(&["PCS::root_request", "Vtc::issue_vetter_root", "PCS::unblind"])
                .say("carol", "a root request for $id_C$, a blind signature from the VTC, and her own credential $\\sigma_C$ on $(usk_C, \\varphi_v)$")
                .step("dave", "enrols the same way")
                .uses(&["PCS::root_request", "Vtc::issue_vetter_root", "PCS::unblind"])
                .say("dave", "the same three messages, for a credential $\\sigma_D$ on $(usk_D, \\varphi_v)$"),
        );
        s.outcome(
            "ok",
            "Enrolled",
            "alice, carol and dave each hold a root credential: a PS signature on \
             $(\\usk, \\varphi_v)$. The VTC has bound $id_A$, $id_C$ and $id_D$ to their member \
             records, and has never seen a key.",
        );
        s.section("Who saw what");
        s.table(
            "",
            &["", "values"],
            vec![
                vec!["the VTC saw".into(), "$id_A$ (member record), $C$, $T_0$, $\\pi_{\\mathrm{root}}$, and $\\hat\\sigma$, which it computed".into()],
                vec!["the VTC never saw".into(), "$usk_A$, $\\rho$, $\\sigma_2$".into()],
            ],
        );
        s.calls(calls);
        s.lab(&["twin-key"]);
        ledger.set(
            "vtc",
            "bound",
            r"$id_A$, $id_C$, $id_D$, bound to alice, carol and dave",
            false,
        );
        ledger.set(
            "vtc",
            "issued",
            "3 root credentials for `vetter/2026-09`",
            false,
        );
        for (name, l) in [("alice", "A"), ("carol", "C"), ("dave", "D")] {
            ledger.set(
                name,
                "cred",
                &format!(r"$\sigma_{l}$, a credential on $(\usk_{l}, \varphi_v)$"),
                true,
            );
        }
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 5 · tokens ─────────────────────────────────────────────────────────────────────────
    let (dripped, calls) = trace::record(|| -> R<_> {
        let d = vetters[0].drip_traced(&mut vtc, 1, &tlabel, 3, &mut rng)?;
        for v in vetters.iter_mut().skip(1) {
            v.drip(&mut vtc, 1, &tlabel, 3, &mut rng)?;
        }
        Ok(d)
    });
    let (reqs, pres) = dripped?;
    {
        let mut cs = Vec::new();
        let mut hs = Vec::new();
        let mut requests = Vec::new();
        let mut pre_json = Vec::new();
        for (i, (r, p)) in reqs.iter().zip(&pres).enumerate() {
            cs.push(
                run.val(
                    Val::g1(&format!("alice.tok.C{i}"), &format!("C_{i}"), &r.commitment)
                        .who(&["alice", "vtc"]),
                ),
            );
            run.val(
                Val::proof(
                    &format!("alice.tok.pi{i}"),
                    &format!(r"\pi_{i}"),
                    &r.opening_proof,
                )
                .who(&["alice", "vtc"]),
            );
            hs.push(
                run.val(
                    Val::encoded(
                        &format!("alice.tok.hs{i}"),
                        &format!(r"\hat\sigma_{i}"),
                        "G1",
                        &to_bytes(p)?,
                    )
                    .who(&["alice", "vtc"])
                    .note(
                        "A blind PS signature under $\\tsk$: two $\\G_1$ points in one encoding.",
                    ),
                ),
            );
            requests.push(json!({
                "commitment": point_text(&r.commitment)?,
                "openingProof": sj(&r.opening_proof)?,
            }));
            pre_json.push(sj(p)?);
        }
        let cs_ref: Vec<&str> = cs.iter().map(String::as_str).collect();
        let hs_ref: Vec<&str> = hs.iter().map(String::as_str).collect();
        let up: usize = reqs
            .iter()
            .map(|r| len(&r.commitment) + len(&r.opening_proof))
            .sum();
        let down: usize = pres.iter().map(len).sum();
        let token_request = json!({
            "member": "alice", "label": tlabel, "tick": 1, "requests": requests,
        });
        let token_answer = json!({ "label": tlabel, "tick": 1, "preCredentials": pre_json });

        let mut s = Stage::new(
            "tokens",
            "Enrolment",
            "Attestation tokens: a blind, rate-limited budget",
            "VTC → each vetter, on a drip",
            "The credential of step 3 is all a vetter needs to make an attestation that verifies. \
             Anonymous vetters could then attest without limit, so the deployment adds a rate \
             limit that the PCS scheme does not have: an attestation counts only if it spends a \
             token, and tokens drip to every vetter at the same fixed rate. A token is a blind \
             PS signature on a serial the VTC never sees, under a separate key.",
        );
        s.parties(&["alice", "vtc", "carol", "dave"]);
        s.fig(
            Fig::new(&["alice", "vtc", "carol", "dave"], "One tick of the drip: three tokens per vetter.")
                .step("alice", "draws three secret serials and commits to each")
                .uses(&["TokenWallet::prepare"])
                .act(
                    "alice",
                    r"s_i, \rho_i \sample \Z_p, \quad C_i := \gone^{\rho_i} \cdot \V{tvk.Y1}{Y_{1,t}}^{s_i} \qquad (i = 0, 1, 2)",
                    &cs_ref,
                )
                .act("alice", r"\pi_i \gets \PoK\bigl\{(s_i, \rho_i) : C_i = \gone^{\rho_i} Y_{1,t}^{s_i}\bigr\}", &[])
                .aside("each bound to $(\\tvk, \\text{label}, \\text{member}, \\text{tick}, i, C_i)$, so it cannot be replayed into another request")
                .send("alice", "vtc", r"(C_i, \pi_i)_{i < 3}", &cs_ref, Some(up))
                .named("the token request")
                .json("memory", &token_request)
                .step("vtc", "checks each opening and the rate limit, then signs blind (PS BlindIssue, under $\\tsk$)")
                .uses(&["Vtc::drip"])
                .check("vtc", r"\VerifyFS(\ctx_i, \pi_i) = 1 \quad (i < 3)", true, "alice knows each opening")
                .say("vtc", "alice holds a grant, and this is her first request for (`token/2026-09`, tick 1)")
                .aside("the rate limit: one blind signature per (member, label, tick)")
                .act(
                    "vtc",
                    r"\hat\sigma_i := \bigl(\gone^{u_i},\ (\gone^{x_t} \cdot C_i \cdot \gone^{y_{2,t}\varphi_{\mathrm{tok}}})^{u_i}\bigr)",
                    &hs_ref,
                )
                .send("vtc", "alice", r"(\hat\sigma_i)_{i < 3}", &hs_ref, Some(down))
                .named("three blind signatures")
                .json("memory", &token_answer)
                .step("alice", "unblinds each token (PS Unblind), and keeps those that verify")
                .uses(&["TokenWallet::receive"])
                .act_md("alice", r"$\sigma_i := \Unblind(\hat\sigma_i, \rho_i)$, kept iff $\Verify(\tvk, (s_i, \varphi_{\mathrm{tok}}), \sigma_i)$", &[])
                .step("carol", "fetches her drip the same way")
                .uses(&["TokenWallet::prepare", "Vtc::drip", "TokenWallet::receive"])
                .say("carol", "three fresh serials, three blind signatures")
                .step("dave", "fetches the same drip")
                .uses(&["TokenWallet::prepare", "Vtc::drip", "TokenWallet::receive"])
                .say("dave", "the drip is unconditional and the same for every vetter: three tokens per tick"),
        );
        s.outcome(
            "ok",
            "Every vetter holds three tokens",
            "The VTC signed nine serials it has never seen. At spend time a vetter reveals the \
             serial with a re-randomised signature, so the spend cannot be linked to the \
             issuance; the VTC keeps one spent set per label.",
        );
        s.section("In detail");
        s.p(
            "Why a separate key: under $\\hvk$, a PS signature on $(s, \\varphi)$ would be a PCS \
             credential whose \"$usk$\" $s$ the vetter knows.",
        );
        s.values(
            "Token parameters",
            &["tok.deploy", "tok.label", "tok.phi", "tvk.Y1"],
        );
        s.callout(
            "warn",
            "A token is not bound to the key of the vetter who spends it: any vetter can spend \
             any token it holds. Colluding vetters can therefore pool tokens, and the cap then \
             holds per colluding group.",
        );
        s.calls(calls);
        s.lab(&["capacity"]);
        for v in &vetters {
            ledger.set(&v.member, "tokens", &tokens_md(v, &tlabel), false);
        }
        ledger.set(
            "vtc",
            "drip",
            "tick 1 served to alice, carol and dave",
            false,
        );
        ledger.set(
            "vtc",
            "spent",
            "spent set for `token/2026-09`: empty",
            false,
        );
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 6 · the applicant ──────────────────────────────────────────────────────────────────
    let (bob, calls) = trace::record(|| ApplicantEngine::new(&vtc, "did:example:bob", &mut rng));
    let mut bob = bob?;
    let bob_id = *bob.id();
    let s_bob = vtc.open().tag_point(&bob_id)?;
    {
        run.val(
            Val::fr("bob.usk", r"\usk_B", bob.usk_scalar())
                .secret()
                .who(&["bob"])
                .note("Fresh for this application only."),
        );
        run.val(Val::g1("bob.id", "id_B", &bob_id).who(&["bob", "vetters", "vtc"]));
        run.val(
            Val::fr("bob.s", "s_B", &s_bob)
                .who(&["public"])
                .note("The point at which every vetter's tag for bob is evaluated."),
        );
        let mut s = Stage::new(
            "applicant-key",
            "Vetting",
            "The applicant: a fresh key for each application",
            "bob's VTA",
            "bob runs the same key generation, but for this application only, so $id_B$ links \
             to nothing else he has. Everything about his application is evaluated at one point \
             derived from $id_B$.",
        );
        s.parties(&["bob"]);
        s.fig(
            Fig::new(&["bob"], "UKeyGen for one application, and the tag point.")
                .step("bob", "draws a fresh key, for this application only")
                .uses(&["PCS::user_keygen"])
                .act("bob", r"\V{bob.usk}{\usk_B} \sample \Z_p^{*}", &["bob.usk"])
                .act("bob", r"\V{bob.id}{id_B} := \gone^{\usk_B}", &["bob.id"])
                .step(
                    "bob",
                    "derives the point at which every vetter's tag for him is evaluated",
                )
                .act("bob", r"\V{bob.s}{s_B} := H_0(id_B)", &["bob.s"]),
        );
        s.outcome(
            "info",
            "bob has applied, and holds nothing yet",
            "The policy needs statements from two distinct vetters, one of them in person. \
             bob has none so far.",
        );
        s.section("Every vetter's tag for bob");
        s.math(r"T_j \;=\; \Tag(\usk_j, \V{bob.s}{s_B}) \;=\; H_2(s_B)^{\usk_j}");
        s.p("A PRF output keyed by the *vetter*, at a point fixed by the *applicant*. Three properties carry the scheme:");
        s.table(
            "",
            &["property", "consequence", "rests on"],
            vec![
                vec![
                    "deterministic".into(),
                    "same vetter, same applicant: the same tag, so a vetter counts once".into(),
                    "nothing".into(),
                ],
                vec![
                    "key-injective".into(),
                    "distinct keys give distinct tags, so distinct tags mean distinct vetters"
                        .into(),
                    "unconditional: $H_2(s_B) \\ne 1$ has prime order $p$".into(),
                ],
                vec![
                    "pseudorandom".into(),
                    "same vetter, another applicant: an unrelated tag".into(),
                    "DDH in $\\G_1$, $H_2$ a random oracle".into(),
                ],
            ],
        );
        s.calls(calls);
        ledger.set("bob", "usk", r"$\usk_B$, fresh for this application", true);
        ledger.set("bob", "id", r"$id_B = g_1^{\usk_B}$", false);
        ledger.app("bob", goal("collecting", &[], None, "no attestation yet"));
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 7 · carol attests ──────────────────────────────────────────────────────────────────
    let (a_carol, calls) =
        trace::record(|| vet(&vtc, &mut vetters[1], &bob, VettingMethod::Video, &mut rng));
    let a_carol = a_carol?;
    let carol_usk = *vetters[1].usk_scalar();
    let carol_cred = vetters[1]
        .credential(PERIOD)
        .ok_or("carol has no credential")?
        .cred
        .clone();
    {
        let att = &a_carol.attestation;
        let m = &a_carol.meta;
        let app_j = m.context_bytes()?;
        run.val(
            Val::fr("carol.usk", r"\usk_C", &carol_usk)
                .secret()
                .who(&["carol"]),
        );
        run.val(
            Val::g1("carol.T", "T_1", &att.tag)
                .who(&["carol", "bob", "vtc"])
                .note("carol's tag for bob. The VTC will see it, and cannot tell whose it is."),
        );
        run.val(
            Val::g1("carol.sh1", r"\sigma'_1", &att.shown.sigma_1).who(&["carol", "bob", "vtc"]),
        );
        run.val(
            Val::g1("carol.sh2", r"\sigma'_2", &att.shown.sigma_2).who(&["carol", "bob", "vtc"]),
        );
        run.val(Val::proof("carol.pi", r"\pi_1", &att.proof).who(&["carol", "bob", "vtc"]));
        run.val(
            Val::fr("carol.serial", "s", &a_carol.token.serial)
                .who(&["carol", "bob", "vtc"])
                .note("The token's serial, revealed at spend time and bound into $app_j$."),
        );
        run.val(Val::text("carol.app", r"\app_1", &String::from_utf8_lossy(&app_j)).who(&["carol", "bob", "vtc"]).note("The statement metadata, as hashed into $ctx_j$ (serde JSON behind a domain prefix; a production encoding would be JCS)."));
        register_attestation(&mut run, "carol", "1", &a_carol)?;
        let s_ok = vtc.open().tag().eval(&carol_usk, &s_bob) == Some(att.tag);
        let (l, r) = ps_sides(
            &hvk,
            &carol_usk,
            &att.phi,
            &att.shown.sigma_1,
            &att.shown.sigma_2,
        );
        run.val(Val::gt(
            "carol.lhs",
            r"e(\sigma'_1, \tilde X \tilde Y_1^{usk_C} \tilde Y_2^{\varphi})",
            &l,
        ));
        run.val(Val::gt("carol.rhs", r"e(\sigma'_2, \tilde g)", &r));

        // Inside π_1: the verifier's recomputation, done here from public data (shown at step 7).
        let rel = vtc
            .open()
            .attestation_relation(&hvk, &att.shown, &att.phi, &att.tag, &s_bob)?;
        let ctx = vtc.open().attestation_context_with_app(
            &hvk,
            &bob_id,
            &att.phi,
            &att.tag,
            &att.shown,
            Some(app_j.as_slice()),
        )?;
        let a = rel.recompute_commitment(&att.proof.challenge, &att.proof.responses)?;
        let c2 = fiat_shamir::challenge(&rel, &ctx, &a)?;
        run.val(Val::fr("carol.pi.c", "c", &att.proof.challenge).who(&["carol", "bob", "vtc"]));
        run.val(
            Val::fr("carol.pi.z", "z", &att.proof.responses[0])
                .who(&["carol", "bob", "vtc"])
                .note("$z = r + c \\cdot usk_C$ for carol's mask $r$."),
        );
        run.val(Val::bytes("carol.ctx", r"\ctx_1", &ctx).who(&["public"]).note("The digest of $(\\mathsf{pp}, \\hvk, id_B, \\varphi_1, T_1, cred^*_1, app_1)$, rebuilt by every verifier from public data."));
        if let Some(gt) = a.gt.first() {
            run.val(Val::gt("carol.A.gt", r"A'_T", gt));
        }
        if let Some(p) = a.g1.first() {
            run.val(Val::g1("carol.A.g1", r"A'_1", p));
        }
        run.val(Val::fr("carol.c2", r"c'", &c2));
        let fs_ok = c2 == att.proof.challenge;
        let (att_json, att_bytes) = attestation_json(&a_carol)?;
        let vreq = vetting_request_json(&vtc, &bob_id)?;

        let mut s = Stage::new(
            "attest",
            "Vetting",
            "carol attests for bob",
            "bob ⇄ carol's VTA",
            "bob asks carol to vet him. After the human check, a video call, carol's engine \
             spends a token and attests: a tag for bob, a fresh re-randomisation of her \
             credential, and one proof that both use the same key.",
        );
        s.parties(&["bob", "carol"]);
        s.fig(
            Fig::new(&["bob", "carol"], "A vetting session, then Attest, as run by carol's engine.")
                .step("bob", "asks carol to vet him")
                .send("bob", "carol", r"\V{bob.id}{id_B} \text{ and a metadata template}", &["bob.id"], Some(len(&bob_id)))
                .named("the vetting request")
                .json("memory", &vreq)
                .aside("bob fills the community and the requirements digest; the vetter fills the rest")
                .step("carol", "checks bob, by video call")
                .say("carol", "a human check: legal name verified, liveness confirmed")
                .aside("this is the vetting itself; everything after it is cryptography")
                .step("carol", "spends one of her tokens")
                .uses(&["TokenWallet::spend"])
                .act_md("carol", r"reveal the serial $\V{carol.serial}{s}$, and show the token's signature re-randomised, $\ReRand(\sigma^{\mathrm{tok}})$", &["carol.serial", "carol.tok.shown"])
                .step("carol", "completes the statement and attests")
                .uses(&["PCS::attest_in_context"])
                .act_md("carol", r"$\V{carol.app}{\app_1} :=$ the statement's metadata, including the serial $s$", &["carol.app"])
                .aside("the serial sits inside $app_1$, so the token cannot move to another attestation")
                .act("carol", r"\V{carol.T}{T_1} := H_2(\V{bob.s}{s_B})^{\usk_C}", &["carol.T"])
                .act("carol", r"r \sample \Z_p^{*}, \quad \cred^*_1 := (\V{carol.sh1}{\sigma'_1}, \V{carol.sh2}{\sigma'_2}) = (\sigma_1^{r}, \sigma_2^{r})", &["carol.sh1", "carol.sh2"])
                .aside("a perfect re-randomisation: $(\\sigma'_1, \\sigma'_2)$ is a uniformly fresh signature on the same message")
                .act("carol", r"\V{carol.ctx}{\ctx_1} := H(\mathsf{pp}, \hvk, id_B, \varphi_v, T_1, \cred^*_1, \app_1)", &["carol.ctx"])
                .act(
                    "carol",
                    r"\V{carol.pi}{\pi_1} \gets \PoK_{\ctx_1}\bigl\{\usk : e(\sigma'_1, \tilde Y_1)^{\usk} = e(\sigma'_2, \gtil)\, e(\sigma'_1, \tilde X \tilde Y_2^{\varphi_v})^{-1} \wedge T_1 = H_2(s_B)^{\usk}\bigr\}",
                    &["carol.pi"],
                )
                .aside("one $\\Sigma$-protocol, two clauses, one shared witness: a single response")
                .send(
                    "carol",
                    "bob",
                    r"att_1 = (\V{carol.T}{T_1}, \V{carol.shown}{\cred^*_1}, \V{phi.v}{\varphi_v}, \V{carol.pi}{\pi_1}),\ \app_1,\ \text{token}",
                    &["carol.T", "carol.shown", "phi.v", "carol.pi"],
                    Some(att_bytes),
                )
                .named("the attestation, its metadata and the spent token")
                .json("memory", &att_json)
                .highlight(&["tag", "method", "tokenSerial", "serial"])
                .detail(checks(
                    "Checked live, with carol's secret key (which only her engine has)",
                    vec![
                        Check::new(s_ok, "the tag is carol's PRF at bob's point")
                            .tex(r"\V{carol.T}{T_1} = H_2(\V{bob.s}{s_B})^{\V{carol.usk}{\usk_C}}")
                            .by("walkthrough, with carol's key"),
                        Check::new(l == r, "$cred^*_1$ is still a PS signature on $(usk_C, \\varphi_v)$")
                            .tex(r"e(\V{carol.sh1}{\sigma'_1}, \tilde X \tilde Y_1^{\usk_C} \tilde Y_2^{\varphi_v}) = e(\V{carol.sh2}{\sigma'_2}, \gtil)")
                            .sides("carol.lhs", "carol.rhs")
                            .by("walkthrough, with carol's key"),
                        Check::new(
                            att.shown.sigma_1 != carol_cred.sigma_1 && att.shown.sigma_2 != carol_cred.sigma_2,
                            "$cred^*_1$ shares no component with the credential the VTC issued: no linkage to issuance",
                        )
                        .tex(r"\sigma'_1 \ne \sigma_1, \ \ \sigma'_2 \ne \sigma_2")
                        .by("walkthrough"),
                        Check::new(att.tag != *vetters[1].id(), "the tag is not carol's identifier $id_C$, the value the VTC bound at enrolment")
                            .tex(r"\V{carol.T}{T_1} \ne \V{carol.id}{id_C}")
                            .by("walkthrough"),
                    ],
                )),
        );
        s.outcome(
            "info",
            "carol has attested",
            "carol spent one token and sent bob $att_1$. Its tag $T_1$ is carol's PRF at bob's \
             point: the VTC, which knows $id_C$, will not be able to tell that it is hers. bob \
             checks it before keeping it, next.",
        );
        s.section("In detail");
        s.p(
            "The validity dates are days, with no time of day: an exact time would let the VTC \
             line statements up with vetter activity.",
        );
        s.table(
            "The size of $att_1$, in its canonical encoding",
            &["part", "encoding", "bytes"],
            vec![
                vec![
                    "$T_1$".into(),
                    "one $\\G_1$ point".into(),
                    len(&att.tag).to_string(),
                ],
                vec![
                    "$cred^*_1$".into(),
                    "two $\\G_1$ points".into(),
                    len(&att.shown).to_string(),
                ],
                vec![
                    "$\\varphi_v$".into(),
                    "one scalar".into(),
                    len(&att.phi).to_string(),
                ],
                vec![
                    "$\\pi_1$".into(),
                    "$c$, $z$ and an 8-byte length".into(),
                    len(&att.proof).to_string(),
                ],
                vec!["total".into(), "".into(), len(att).to_string()],
            ],
        );
        s.calls(calls);
        s.lab(&["tamper", "same-vetter"]);
        ledger.set("carol", "tokens", &tokens_md(&vetters[1], &tlabel), false);
        ledger.set(
            "bob",
            "atts",
            "$att_1$ from carol (video), not yet checked",
            false,
        );
        ledger.app(
            "bob",
            goal(
                "collecting",
                &[VettingMethod::Video],
                None,
                "one attestation in hand, not yet checked",
            ),
        );
        s.state(ledger.snapshot());
        run.stage(s);

        // ── 8 · bob checks on receipt ──────────────────────────────────────────────────────
        let verify_ok = vtc
            .open()
            .check_attestation_in_context(&hvk, &bob_id, att, &app_j)
            .is_ok();
        let live_ok = vtc.live_vetter_phis()?.contains(&att.phi);
        let tvk = vtc.tokens.tvk().clone();
        let t = &a_carol.token;
        let (tl, tr) = ps_sides(&tvk, &t.serial, &phi_t, &t.shown.sigma_1, &t.shown.sigma_2);
        run.val(Val::gt("carol.tok.lhs", r"e(\sigma'^{\mathrm{tok}}_1, \tilde X_t \tilde Y_{1,t}^{s} \tilde Y_{2,t}^{\varphi_{\mathrm{tok}}})", &tl));
        run.val(Val::gt(
            "carol.tok.rhs",
            r"e(\sigma'^{\mathrm{tok}}_2, \tilde g)",
            &tr,
        ));
        let serial_ok = a_carol.meta.token_serial == scalar_text(&t.serial)?;
        let mut tampered = a_carol.meta.clone();
        tampered.method = VettingMethod::InPerson;
        let tamper =
            vtc.open()
                .check_attestation_in_context(&hvk, &bob_id, att, &tampered.context_bytes()?);

        let (received, calls) = trace::record(|| bob.receive(&vtc, a_carol.clone()));
        received?;
        let mut s = Stage::new(
            "receive",
            "Vetting",
            "bob checks the attestation on receipt",
            "bob's VTA",
            "So that a bad attestation fails during the vetting session rather than at the join, \
             bob's engine verifies everything it can before keeping it.",
        );
        s.parties(&["bob"]);
        s.fig(
            Fig::new(&["bob"], "What bob's engine checks before it keeps $att_1$.")
                .step("bob", "verifies the attestation under a context he rebuilds himself")
                .uses(&["PCS::check_attestation_in_context"])
                .check_md("bob", r"$\VerifyAtt(\hvk, \V{bob.id}{id_B}, att_1)$ under the rebuilt $\ctx_1$", verify_ok, "subgroup checks of every point, $T_1 \\ne 1$, $\\sigma'_1 \\ne 1$, then $\\mathsf{Verify}_{\\mathsf{FS}}(\\ctx_1, \\pi_1)$")
                .detail(derive(
                    "Inside the last check: the Fiat–Shamir verification, recomputed",
                    "From public data only, as `fiat_shamir::verify` does it.",
                    vec![
                        line(r"\pi_1 = (\V{carol.pi.c}{c},\ \V{carol.pi.z}{z})", &["carol.pi.c", "carol.pi.z"]),
                        line_md("what carol sent: the challenge and one response, for the witness $usk_C$ that both clauses share"),
                        line(
                            r"\V{carol.A.gt}{A'_T} := e(\sigma'_1, \tilde Y_1)^{z} \cdot \bigl(e(\sigma'_2, \gtil)\, e(\sigma'_1, \tilde X \tilde Y_2^{\varphi_v})^{-1}\bigr)^{-c}",
                            &["carol.A.gt"],
                        ),
                        line(r"\V{carol.A.g1}{A'_1} := H_2(s_B)^{z} \cdot T_1^{-c}", &["carol.A.g1"]),
                        line_ok(
                            r"\V{carol.c2}{c'} := H_1\bigl(\V{carol.ctx}{\ctx_1},\ \text{statement},\ (A'_T, A'_1)\bigr) = c",
                            &["carol.ctx", "carol.c2"],
                            fs_ok,
                            "accept iff the recomputed commitment hashes back to $c$. The statement (every base and target) is hashed too: strong Fiat–Shamir",
                        ),
                    ],
                ))
                .step("bob", "checks that the class is a live vetter class")
                .check("bob", r"\V{phi.v}{\varphi_v} \in \{\text{live vetter classes}\}", live_ok, "from the VTC's manifest")
                .step("bob", "checks that the token is the one the statement names")
                .check("bob", r"\app_1.\mathsf{tokenSerial} = \V{carol.serial}{s}", serial_ok, "and the labels agree")
                .step("bob", "checks the token's signature under the token key")
                .uses(&["token::verify_spend"])
                .check(
                    "bob",
                    r"e(\sigma'^{\mathrm{tok}}_1, \tilde X_t \tilde Y_{1,t}^{s}\, \tilde Y_{2,t}^{\varphi_{\mathrm{tok}}}) = e(\sigma'^{\mathrm{tok}}_2, \gtil)",
                    tl == tr,
                    "the token is a signature under $\\tvk$ on the revealed serial",
                )
                .detail(checks(
                    "Both sides of the token's pairing equation",
                    vec![
                        Check::new(tl == tr, "the token verifies under $\\tvk$, with the revealed serial")
                            .tex(r"e(\sigma'^{\mathrm{tok}}_1, \tilde X_t \tilde Y_{1,t}^{s} \tilde Y_{2,t}^{\varphi_{\mathrm{tok}}}) = e(\sigma'^{\mathrm{tok}}_2, \gtil)")
                            .sides("carol.tok.lhs", "carol.tok.rhs")
                            .by("bob's engine (public data)"),
                    ],
                )),
        );
        s.outcome(
            "ok",
            "bob keeps $att_1$, and can see what is missing",
            "One statement, by video, from a credentialed vetter. The policy needs two from \
             distinct vetters, one of them in person: bob is one short, and the missing one must \
             be in person.",
        );
        s.section("Also checked: editing the metadata afterwards");
        s.checks(
            "",
            vec![
                Check::new(tamper.is_err(), "editing $app_1$ after the fact (video → in person) breaks $\\pi_1$")
                    .tex(r"\VerifyAtt(\hvk, id_B, att_1)\ \text{under}\ \ctx_1[\mathsf{method} := \mathsf{inPerson}] = 0")
                    .observed(match &tamper { Err(e) => format!("Err({e})"), Ok(()) => "Ok(())".into() })
                    .by("walkthrough"),
            ],
        );
        s.p(
            "The challenge of $\\pi_1$ is a hash of $\\ctx_1$, and $\\ctx_1$ contains $app_1$: \
             any change to the metadata changes the challenge the verifier recomputes. The lab \
             lets you edit any field and watch the challenge diverge.",
        );
        s.calls(calls);
        s.lab(&["tamper", "steal"]);
        ledger.set("bob", "atts", "$att_1$ from carol (video), verified", false);
        ledger.app(
            "bob",
            goal(
                "collecting",
                &[VettingMethod::Video],
                None,
                "one statement in hand; the missing one must be in person",
            ),
        );
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 9 · prove k = 1 ────────────────────────────────────────────────────────────────────
    let (step, calls) = trace::record(|| -> R<(Submission, Decision)> {
        let c = vtc.challenge(&mut rng);
        let sub = bob.submit(&vtc, &c, &mut rng)?;
        let d = vtc_submit(&mut vtc, &sub)?;
        Ok((sub, d))
    });
    let (sub1, d1) = step?;
    {
        register_submission(&mut run, "sub1", &sub1)?;
        let t0_ok = vtc.open().tag().eval(bob.usk_scalar(), &s_bob) == Some(sub1.proof.t0);
        let wire = wire_json(&vtc, &sub1)?;
        let mut s = Stage::new(
            "prove-k1",
            "Admission",
            "bob proves one vetter, and the count is short",
            "bob ⇄ VTC",
            "bob proves that $k = 1$ distinct vetter attested to him. The proof verifies, but \
             the policy needs two vetters, one of them in person.",
        );
        s.parties(&["bob", "vtc"]);
        s.fig(proof_fig(&run, &sub1, None, 1, &d1, &wire)?);
        s.outcome(
            "more",
            "The count is short: request more",
            &format!(
                "The proof is valid: bob holds one attestation from a credentialed vetter. But \
                 the policy needs two, one of them in person, so the VTC answers `requestMore` \
                 with what is missing: {}.",
                needs_md(&d1)
            ),
        );
        s.section("In detail");
        s.checks(
            "Checked live",
            vec![
                Check::new(t0_ok, "$T_0$ is bob's own tag at his point")
                    .tex(r"\V{sub1.T0}{T_0} = H_2(s_B)^{\V{bob.usk}{\usk_B}}")
                    .by("walkthrough, with bob's key"),
            ],
        );
        s.p(
            "$f_k = (k, \\texttt{\"hidden-vetting\"})$ is a *verify-only* predicate: the VTC \
             checks $\\pi$ as an issuance proof and admits on it, but never issues a credential \
             under it.",
        );
        s.calls(calls);
        s.lab(&["replay"]);
        ledger.set(
            "vtc",
            "spent",
            "spent set for `token/2026-09`: 1 serial",
            false,
        );
        ledger.set(
            "vtc",
            "facts",
            r"for $id_B$: 1 statement counted, by video",
            false,
        );
        ledger.app(
            "bob",
            goal("requestMore", &[], Some(&d1), "the VTC asks for more"),
        );
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 10 · alice attests in person, bob proves k = 2 ─────────────────────────────────────
    let (step, calls) = trace::record(|| -> R<(HiddenAttestation, Submission, Decision)> {
        let a_alice = vet(
            &vtc,
            &mut vetters[0],
            &bob,
            VettingMethod::InPerson,
            &mut rng,
        )?;
        bob.receive(&vtc, a_alice.clone())?;
        let c = vtc.challenge(&mut rng);
        let sub = bob.submit(&vtc, &c, &mut rng)?;
        let d = vtc_submit(&mut vtc, &sub)?;
        Ok((a_alice, sub, d))
    });
    let (a_alice, sub2, d2) = step?;
    {
        run.val(
            Val::g1("alice.T", "T_2", &a_alice.attestation.tag)
                .who(&["alice", "bob", "vtc"])
                .note("alice's tag for bob."),
        );
        run.val(
            Val::proof("alice.pi", r"\pi_2", &a_alice.attestation.proof)
                .who(&["alice", "bob", "vtc"]),
        );
        run.val(
            Val::fr("alice.serial", r"s_2", &a_alice.token.serial)
                .who(&["alice", "bob", "vtc"])
                .note("alice's token serial, bound into $app_2$."),
        );
        register_attestation(&mut run, "alice", "2", &a_alice)?;
        register_submission(&mut run, "sub2", &sub2)?;
        let wire = wire_json(&vtc, &sub2)?;
        let vreq = vetting_request_json(&vtc, &bob_id)?;
        let mut s = Stage::new(
            "prove-k2",
            "Admission",
            "alice attests in person; bob proves two vetters",
            "alice → bob → VTC",
            "alice vets bob in person. bob proves $k = 2$ with both attestations under a fresh \
             challenge, and the VTC admits him.",
        );
        s.parties(&["alice", "bob", "vtc"]);
        s.fig(proof_fig(
            &run,
            &sub2,
            Some((&a_alice, &vreq)),
            2,
            &d2,
            &wire,
        )?);
        s.outcome(
            "ok",
            "Admitted",
            "Two distinct vetters, one of them in person: nothing is missing, and the VTC \
             answers `allow`. It counted two tags and never learned whose they are. carol's \
             attestation came back with the same $(id_B, T_1)$: counted once, not flagged as a \
             double spend.",
        );
        s.section("In detail");
        s.checks(
            "Checked live",
            vec![
                Check::new(sub1.proof.t0 == sub2.proof.t0, "$T_0$ is the same in both submissions: a function of $(usk_B, s_B)$ only")
                    .tex(r"\V{sub1.T0}{T_0^{(1)}} = \V{sub2.T0}{T_0^{(2)}}")
                    .by("anyone"),
                Check::new(sub1.proof.encoding != sub2.proof.encoding, "$C$ is fresh in each submission: a new $\\rho$ every time")
                    .tex(r"\V{sub1.C}{C^{(1)}} \ne \V{sub2.C}{C^{(2)}}")
                    .by("anyone"),
                Check::new(
                    sub1.proof.attestations[0].tag == sub2.proof.attestations[0].tag,
                    "carol's attestation returns with the same $(id_B, T_1)$: already counted, not a double spend",
                )
                .tex(r"T_1^{(1)} = T_1^{(2)}")
                .by("the VTC's spent set"),
            ],
        );
        s.calls(calls);
        s.lab(&["replay", "same-vetter", "cofactor", "self-vetting"]);
        ledger.set("alice", "tokens", &tokens_md(&vetters[0], &tlabel), false);
        ledger.set(
            "bob",
            "atts",
            "$att_1$ from carol (video) and $att_2$ from alice (in person)",
            false,
        );
        ledger.set(
            "vtc",
            "spent",
            "spent set for `token/2026-09`: 2 serials",
            false,
        );
        ledger.set(
            "vtc",
            "facts",
            r"for $id_B$: 2 statements counted, under two tags it cannot attribute",
            false,
        );
        ledger.app("bob", goal("allow", &[], Some(&d2), "admitted"));
        s.state(ledger.snapshot());
        run.stage(s);
    }

    let world = World {
        rng,
        vtc,
        vetters,
        bob,
        a_carol,
        a_alice,
        sub2,
        ledger,
    };
    Ok((run, world))
}

/// What is missing, in words, with the wire strings.
fn needs_md(d: &Decision) -> String {
    let wire: Vec<String> = d
        .evaluation
        .needs
        .iter()
        .map(|n| format!("`{}`", n.to_wire()))
        .collect();
    match wire.len() {
        0 => "nothing".to_string(),
        1 => wire[0].clone(),
        _ => format!(
            "{} and {}",
            wire[..wire.len() - 1].join(", "),
            wire[wire.len() - 1]
        ),
    }
}

/// Register the parts of a submission under `key`.
fn register_submission(run: &mut Run, key: &str, sub: &Submission) -> R<()> {
    run.val(
        Val::text(
            &format!("{key}.challenge"),
            r"\mathsf{challenge}",
            &sub.challenge,
        )
        .who(&["vtc", "bob"])
        .note("16 random bytes from the VTC, valid once."),
    );
    run.val(Val::g1(&format!("{key}.C"), "C", &sub.proof.encoding).who(&["bob", "vtc"]).note("$g_1^{\\rho} Y_1^{usk_B}$ for a fresh $\\rho$: the commitment an issuance would sign."));
    run.val(
        Val::g1(&format!("{key}.T0"), "T_0", &sub.proof.t0)
            .who(&["bob", "vtc"])
            .note("bob's own tag at his point: the self-exclusion tag."),
    );
    run.val(Val::proof(&format!("{key}.pi0"), r"\pi_0", &sub.proof.proof).who(&["bob", "vtc"]));
    run.val(
        Val::bytes_mb(&format!("{key}.pi"), r"\pi", &to_bytes(&sub.proof)?)
            .who(&["bob", "vtc"])
            .note(
                "The whole issuance proof $((att_j)_j, C, T_0, \\pi_0)$ in its canonical encoding.",
            ),
    );
    Ok(())
}

/// The flow of a submission with `k` attestations (stages 9 and 10). `d` is what the VTC
/// returned: the proof checks hold because `Vtc::submit` returned a decision at all; the token
/// row is read off the decision.
fn proof_fig(
    run: &Run,
    sub: &Submission,
    fresh: Option<(&HiddenAttestation, &J)>,
    k: usize,
    d: &Decision,
    wire: &J,
) -> R<Fig> {
    let tokens_ok = d
        .statements
        .iter()
        .all(|s| !s.failures.iter().any(|f| f.contains("token")));
    let key = if k == 1 { "sub1" } else { "sub2" };
    let v = |s: &str| format!("{key}.{s}");
    let (c, t0, pi0, ch, pi) = (v("C"), v("T0"), v("pi0"), v("challenge"), v("pi"));
    let lanes: &[&str] = if fresh.is_some() {
        &["alice", "bob", "vtc"]
    } else {
        &["bob", "vtc"]
    };
    let mut fig = Fig::new(
        lanes,
        &format!("Prove and VerifyProof for $f_{k}$, under the VTC's single-use challenge."),
    );
    if let Some((a, vreq)) = fresh {
        let (att_json, att_bytes) = attestation_json(a)?;
        fig = fig
            .step("bob", "asks alice to vet him")
            .send("bob", "alice", r"\V{bob.id}{id_B} \text{ and a metadata template}", &["bob.id"], Some(48))
            .named("the vetting request")
            .json("memory", vreq)
            .step("alice", "checks bob in person, spends a token and attests")
            .uses(&["TokenWallet::spend", "PCS::attest_in_context"])
            .say("alice", "a human check, in person: legal name verified, liveness confirmed")
            .act_md("alice", r"$\V{alice.T}{T_2} := H_2(s_B)^{\usk_A}$, $\cred^*_2$ and $\V{alice.pi}{\pi_2}$, as carol did", &["alice.T", "alice.pi"])
            .send("alice", "bob", r"att_2 = (\V{alice.T}{T_2}, \V{alice.shown}{\cred^*_2}, \varphi_v, \V{alice.pi}{\pi_2}),\ \app_2,\ \text{token}", &["alice.T", "alice.shown", "alice.pi"], Some(att_bytes))
            .named("the attestation, its metadata and the spent token")
            .json("memory", &att_json)
            .highlight(&["tag", "method"])
            .step("bob", "checks $att_2$ on receipt, as he checked $att_1$")
            .uses(&["PCS::check_attestation_in_context", "token::verify_spend"])
            .check_md("bob", r"$\VerifyAtt(\hvk, id_B, att_2) = 1$, and the token verifies under $\tvk$", true, "he now holds two attestations");
    }
    let atts = if k == 1 { "att_1" } else { "att_1, att_2" };
    let tj = if k == 1 {
        r"T_0 \notin \{T_1\}"
    } else {
        r"T_1 \ne T_2,\ T_0 \notin \{T_1, T_2\}"
    };
    let token_uses: Vec<&str> = std::iter::repeat_n("TokenIssuer::signature_ok", k)
        .chain(std::iter::repeat_n("TokenIssuer::record_spend", k))
        .collect();
    let verdict = verdict_json(d);
    let admit = d.evaluation.satisfied();
    let fig = fig
        .step("vtc", "sends a fresh challenge")
        .uses(&["Vtc::challenge"])
        .send("vtc", "bob", &format!(r"\V{{{ch}}}{{\mathsf{{challenge}}}}"), &[ch.as_str()], Some(16))
        .named("the challenge")
        .json("memory", &json!({ "challenge": sub.challenge }))
        .aside("16 random bytes, remembered until used once")
        .step("bob", &format!("proves $k = {k}$ under that challenge"))
        .uses(&["PCS::prove_in_context"])
        .act("bob", &format!(r"f_{k} := ({k}, \str{{hidden-vetting}})"), &[])
        .act("bob", &format!(r"\rho \sample \Z_p, \quad \V{{{c}}}{{C}} := \gone^{{\rho}} Y_1^{{\usk_B}}, \quad \V{{{t0}}}{{T_0}} := H_2(s_B)^{{\usk_B}}"), &[c.as_str(), t0.as_str()])
        .act("bob", r"\app_0 := \bigl(\mathsf{challenge}, \mathsf{audience}, \mathsf{joinDid}, H(id_B, \mathsf{community}, \mathsf{reqDigest}, \mathsf{joinDid})\bigr)", &[])
        .aside("binds the proof to this challenge and to the persona DID bob joins with")
        .act(
            "bob",
            &format!(r"\V{{{pi0}}}{{\pi_0}} \gets \PoK_{{\ctx_0}}\bigl\{{(\usk, \rho) : C = \gone^{{\rho}} Y_1^{{\usk}} \wedge id_B = \gone^{{\usk}} \wedge T_0 = H_2(s_B)^{{\usk}}\bigr\}}"),
            &[pi0.as_str()],
        )
        .aside(&format!("$\\ctx_0 = H(\\mathsf{{pp}}, \\hvk, f_{k}, id_B, C, T_0, {atts}, (app_j)_j, app_0)$"))
        .send(
            "bob",
            "vtc",
            &format!(r"\V{{bob.id}}{{id_B}},\ \mathsf{{joinDid}},\ (\app_j, \text{{token}}_j)_j,\ \V{{{pi}}}{{\pi}} = ({atts}, C, T_0, \pi_0)"),
            &["bob.id", pi.as_str()],
            Some(len(&sub.proof)),
        )
        .named("the join submission")
        .json("wire", wire)
        .highlight(&["proof", "id", "challenge"])
        .aside("the hidden-vetting member of `vtc/join-requests/submit/0.3`; step 10 takes it apart byte by byte")
        .step("vtc", "checks the challenge and every point, then verifies the proof")
        .uses(&["PCS::check_proof_in_context"])
        .check_md("vtc", "the challenge is known and unused, and is now consumed", true, "single use")
        .check_md("vtc", "every point is on its curve and in the prime-order subgroup", true, "before anything is computed from it")
        .check("vtc", &format!(r"\CheckAtts:\ \textstyle\bigwedge_j \VerifyAtt(att_j),\ {tj},\ P(\varphi_j) = 1"), true, "rebuilding each $\\ctx_j$ from public data, never taking context bytes from bob")
        .check("vtc", r"\VerifyFS(\ctx_0, \pi_0) = 1", true, "$\\pi_0$ binds the attestations, the contexts and the challenge to $id_B$")
        .step("vtc", if k == 1 { "checks the token, and records its serial" } else { "checks each token, and records its serial" })
        .uses(&token_uses)
        .check_md("vtc", r"per token: $\Verify(\tvk, \cdot) = 1$, and the serial goes into the spent set", tokens_ok, "a serial seen before under the same $(id, T)$ counts once and is not a double spend")
        .step("vtc", "counts the statements with VTI's rule")
        .uses(&["vetting::requirements::evaluate"])
        .act_md("vtc", r"the facts, with $T_j$ where the vetter's DID used to be, go to `evaluate`", &[])
        .detail(run.decision(
            d,
            "The facts handed to VTI's counting rule (vta-sdk `requirements::evaluate`, unchanged)",
        ))
        .step("vtc", if admit { "admits bob" } else { "asks for more" })
        .send(
            "vtc",
            "bob",
            if admit { r"\textsf{allow}" } else { r"\textsf{requestMore}(\textit{needs})" },
            &[],
            None,
        )
        .named("the verdict")
        .json("verdict", &verdict)
        .highlight(&["effect", "needs"])
        .aside(if admit {
            "a real VTC also issues the membership credential here; the prototype stops at the decision"
        } else {
            "the `needs` strings are vta-sdk's own grammar for what is missing"
        });
    Ok(fig)
}

// ---------------------------------------------------------------------------------------------
// Stages 11-15
// ---------------------------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
pub fn full(seed: u64) -> R<Run> {
    let (mut run, w) = admitted(seed)?;
    let World {
        mut rng,
        mut vtc,
        mut vetters,
        bob,
        a_carol: _,
        a_alice,
        sub2,
        mut ledger,
    } = w;
    let bob_id = *bob.id();
    let s_bob = vtc.open().tag_point(&bob_id)?;
    let alice_usk = *vetters[0].usk_scalar();
    let t_alice = a_alice.attestation.tag;
    let tlabel = vtc.current_token_label().to_string();

    // ── 11 · the wire ──────────────────────────────────────────────────────────────────────
    {
        let wire = wire_json(&vtc, &sub2)?;
        let bytes = to_bytes(&sub2.proof)?;
        // The byte map: every part of π at its offset, checked against the encoding.
        let mut segments = Vec::new();
        let mut off = 0usize;
        let mut all_match = true;
        let mut seg = |label: &str,
                       kind: &str,
                       vid: Option<&str>,
                       group: &str,
                       part: Vec<u8>,
                       md: &str| {
            let n = part.len();
            let ok = bytes.get(off..off + n) == Some(part.as_slice());
            all_match &= ok;
            segments.push(json!({ "label": label, "kind": kind, "vid": vid, "group": group, "bytes": n, "offset": off, "md": md }));
            off += n;
        };
        seg(
            "k",
            "len",
            None,
            "",
            (sub2.proof.attestations.len() as u64)
                .to_le_bytes()
                .to_vec(),
            "u64 length of the attestation list",
        );
        for (j, a) in sub2.proof.attestations.iter().enumerate() {
            let g = format!("att_{}", j + 1);
            let tvid = run.by_mb(&point_text(&a.tag)?).map(str::to_string);
            seg(
                &format!("T_{}", j + 1),
                "G1",
                tvid.as_deref(),
                &g,
                to_bytes(&a.tag)?,
                "the tag",
            );
            seg(
                &format!("cred^*_{}", j + 1),
                "G1",
                None,
                &g,
                to_bytes(&a.shown)?,
                "$(\\sigma'_1, \\sigma'_2)$: two $\\G_1$ points",
            );
            seg(
                &format!("\\varphi_{}", j + 1),
                "Fr",
                Some("phi.v"),
                &g,
                to_bytes(&a.phi)?,
                "the class",
            );
            seg(
                &format!("\\pi_{}", j + 1),
                "proof",
                None,
                &g,
                to_bytes(&a.proof)?,
                "$c$, an 8-byte length, $z$",
            );
        }
        seg(
            "C",
            "G1",
            Some("sub2.C"),
            "",
            to_bytes(&sub2.proof.encoding)?,
            "the commitment",
        );
        seg(
            "T_0",
            "G1",
            Some("sub2.T0"),
            "",
            to_bytes(&sub2.proof.t0)?,
            "the self-exclusion tag",
        );
        seg(
            "\\pi_0",
            "proof",
            Some("sub2.pi0"),
            "",
            to_bytes(&sub2.proof.proof)?,
            "$c$, an 8-byte length, $z_{usk}$, $z_\\rho$",
        );
        let total_ok = off == bytes.len();

        let mut s = Stage::new(
            "wire",
            "Admission",
            "The submission on the wire",
            "bob → VTC: vtc/join-requests/submit/0.3, member extensions.hiddenVetting",
            "The join request carries a presentation with no vetting credentials in it, and \
             this member. Binary values are multibase base58btc over the canonical compressed \
             encoding.",
        );
        s.parties(&["bob", "vtc"]);
        s.block(json!({
            "t": "json",
            "title": "extensions.hiddenVetting, as the VTC received it at step 10",
            "kind": "wire",
            "json": serde_json::to_string_pretty(&wire)?,
            "highlight": ["proof", "id", "challenge"],
        }));
        s.block(json!({
            "t": "bytemap",
            "title": "Inside `proof`: $\\pi = ((att_j)_j, C, T_0, \\pi_0)$, byte by byte",
            "total": bytes.len(),
            "segments": segments,
        }));
        s.checks(
            "Checked live",
            vec![
                Check::new(
                    all_match && total_ok,
                    &format!(
                        "every part matches the encoding of `proof` byte for byte, {} B in all",
                        bytes.len()
                    ),
                )
                .by("walkthrough"),
            ],
        );
        s.h("What the VTC does with it, in order");
        s.list(
            true,
            &[
                "Consume the challenge (single use).",
                "Decode, refusing any point off its curve or outside the prime-order subgroup.",
                "Rebuild $app_j$ from each `meta`, and $app_0$ from (challenge, audience, joinDid, idBinding).",
                "`VerifyProof` under $\\mathsf{AllowList}\\{\\text{live vetter } \\varphi\\}$.",
                "Per statement: the token under $\\tvk$, the serial into the spent set.",
                "Build `StatementFacts` with the tag as the vetter, and count with VTI's `evaluate`.",
            ],
        );
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 12 · privacy ───────────────────────────────────────────────────────────────────────
    let d = vtc.evaluate(&point_text(&bob_id)?, now());
    let (frank, calls) =
        trace::record(|| ApplicantEngine::new(&vtc, "did:example:frank", &mut rng));
    let frank = frank?;
    {
        let s_frank = vtc.open().tag_point(frank.id())?;
        let t_alice_frank = vtc
            .open()
            .tag()
            .eval(&alice_usk, &s_frank)
            .ok_or("tag undefined")?;
        run.val(Val::g1("frank.id", "id_F", frank.id()).who(&["frank"]));
        run.val(Val::g1("alice.T.frank", r"T_{A,F}", &t_alice_frank).who(&["walkthrough"]).note("alice's tag at frank's point, computed with her key: what she would send frank."));
        let facts = serde_json::to_string(&d.statements)?;
        let mut tags = Vec::new();
        for st in &d.statements {
            tags.push(json!({ "vid": run.by_mb(&st.issuer), "issuer": st.issuer, "method": st.method.to_string() }));
        }
        let mut truth = Vec::new();
        for st in &d.statements {
            let mut row = Vec::new();
            for v in &vetters {
                let t = vtc
                    .open()
                    .tag()
                    .eval(v.usk_scalar(), &s_bob)
                    .ok_or("tag undefined")?;
                row.push(point_text(&t)? == st.issuer);
            }
            truth.push(row);
        }
        let n = vetters.len();
        let k = d.statements.len();
        let mut checks_ = Vec::new();
        for v in &vetters {
            checks_.push(
                Check::new(
                    !facts.contains(&v.member) && !facts.contains(&point_text(v.id())?),
                    &format!(
                        "{} appears in the facts by neither member name nor identifier",
                        v.member
                    ),
                )
                .by("walkthrough"),
            );
        }
        checks_.push(
            Check::new(
                vtc.open().tag().eval(&alice_usk, &s_bob) == Some(t_alice),
                "same vetter, same applicant: the same tag, so a vetter cannot count twice",
            )
            .tex(r"\Tag(\usk_A, s_B) = \V{alice.T}{T_2}")
            .by("walkthrough, with alice's key"),
        );
        checks_.push(
            Check::new(
                t_alice_frank != t_alice,
                "same vetter, another applicant: an unrelated tag",
            )
            .tex(r"\V{alice.T.frank}{T_{A,F}} \ne \V{alice.T}{T_{A,B}}")
            .by("walkthrough, with alice's key"),
        );

        let mut s = Stage::new(
            "privacy",
            "Privacy",
            "What the VTC learned",
            "the VTC's view against the ground truth",
            "The VTC knows every vetter's identifier. The facts it counted for bob name only \
             tags, and nothing it holds tells it which identifier a tag belongs to.",
        );
        s.parties(&["vtc"]);
        s.block(json!({
            "t": "privacy",
            "vetters": vetters.iter().map(|v| json!({ "name": v.member, "vid": format!("{}.id", v.member) })).collect::<Vec<_>>(),
            "tags": tags,
            "truth": truth,
        }));
        s.h("Why the VTC cannot fill in the table");
        s.math(r"\bigl(\gone,\ \V{alice.id}{id_A} = \gone^{\usk_A},\ H_2(\V{bob.s}{s_B}),\ \V{alice.T}{T} \bigr) \overset{?}{=} \bigl(g,\ g^{a},\ h,\ h^{a}\bigr)");
        s.p(
            "Matching a tag $T$ to an identifier $id_v$ means deciding whether \
             $(g_1, id_v, H_2(s_B), T)$ is a Diffie–Hellman tuple. That is the DDH problem in \
             $\\G_1$, assumed hard in BLS12-381 (the SXDH setting of a type-3 pairing; the \
             pairing does not help, since $H_2(s_B)$ and $T$ have no $\\G_2$ counterparts). With \
             $usk_v$ the test is one exponentiation; the VTC never has it.",
        );
        s.checks("Checked live", checks_);
        s.callout(
            "warn",
            &format!(
                "Anonymity is relative to the live vetters, whom the VTC knows. Here there are \
                 {n} of them and $k = {k}$: from the count alone, with a uniform prior over which \
                 {k} attested, each vetter is one of bob's attesters with probability \
                 $\\binom{{{nm}}}{{{km}}} / \\binom{{{n}}}{{{k}}} = {k}/{n}$. The metadata (one \
                 attestation by video, one in person) can narrow it further. A community with few \
                 vetters cannot hide much.",
                nm = n - 1,
                km = k.saturating_sub(1),
            ),
        );
        s.p(
            "What the VTC *does* learn: $k$, each statement's metadata, the period of each \
             attester's credential ($\\varphi_j$), and each token's label and serial (spent \
             once, unlinkable to its issuance).",
        );
        s.calls(calls);
        ledger.set("frank", "id", r"$id_F$, a fresh application", false);
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 13 · double spend ──────────────────────────────────────────────────────────────────
    let (step, calls) = trace::record(|| -> R<_> {
        let mut eve = ApplicantEngine::new(&vtc, "did:example:eve", &mut rng)?;
        let a_eve = vet(
            &vtc,
            &mut vetters[2],
            &eve,
            VettingMethod::InPerson,
            &mut rng,
        )?;
        let reused = a_eve.token.clone();
        let t_eve = a_eve.attestation.tag;
        eve.receive(&vtc, a_eve)?;
        let c = vtc.challenge(&mut rng);
        let sub = eve.submit(&vtc, &c, &mut rng)?;
        let d_eve = vtc_submit(&mut vtc, &sub)?;
        let mut frank = frank;
        let m = meta(&frank, &vtc, VettingMethod::InPerson);
        let cheat = vetters[2].attest_with_token(&vtc, PERIOD, reused, frank.id(), m, &mut rng)?;
        let t_frank = cheat.attestation.tag;
        let serial = cheat.token.serial;
        let accepted = frank.receive(&vtc, cheat).is_ok();
        let honest = vet(
            &vtc,
            &mut vetters[1],
            &frank,
            VettingMethod::Video,
            &mut rng,
        )?;
        frank.receive(&vtc, honest)?;
        let c = vtc.challenge(&mut rng);
        let sub = frank.submit(&vtc, &c, &mut rng)?;
        let d = vtc_submit(&mut vtc, &sub)?;
        Ok((*eve.id(), t_eve, t_frank, serial, accepted, d_eve, d, frank))
    });
    let (eve_id, t_eve, t_frank, serial, accepted, d_eve, d3, _frank) = step?;
    {
        run.val(Val::g1("eve.id", "id_E", &eve_id).who(&["eve", "dave", "vtc"]));
        run.val(
            Val::fr("dave.serial", r"s^{*}", &serial)
                .who(&["dave", "eve", "frank", "vtc"])
                .note("The one token dave spends twice."),
        );
        run.val(Val::g1("dave.T.eve", r"T_{D,E}", &t_eve).who(&["dave", "eve", "vtc"]));
        run.val(Val::g1("dave.T.frank", r"T_{D,F}", &t_frank).who(&["dave", "frank", "vtc"]));
        let anomaly = vtc.tokens.anomalies.last().cloned().unwrap_or_default();
        let mut s = Stage::new(
            "double-spend",
            "Abuse",
            "A vetter double-spends a token",
            "dave (cheating), eve, frank → VTC",
            "dave vets eve honestly, then reuses the same token to attest for frank. Each \
             attestation is valid on its own; the spent set catches the second spend, without \
             learning who cheated.",
        );
        s.parties(&["dave", "eve", "frank", "vtc"]);
        s.fig(
            Fig::new(
                &["dave", "eve", "frank", "vtc"],
                "One token, two attestations.",
            )
            .step("eve", "applies, with a fresh key")
            .uses(&["PCS::user_keygen"])
            .act("eve", r"\V{eve.id}{id_E} := \gone^{\usk_E}", &["eve.id"])
            .step("dave", "vets eve honestly, in person, and attests")
            .uses(&["TokenWallet::spend", "PCS::attest_in_context"])
            .send(
                "dave",
                "eve",
                r"att = (\V{dave.T.eve}{T_{D,E}}, \dots),\ \text{token } \V{dave.serial}{s^{*}}",
                &["dave.T.eve", "dave.serial"],
                None,
            )
            .named("an attestation")
            .step("eve", "checks it, proves $k = 1$ and submits")
            .uses(&[
                "PCS::check_attestation_in_context",
                "token::verify_spend",
                "Vtc::challenge",
                "PCS::prove_in_context",
            ])
            .send("eve", "vtc", r"\pi_E \text{ for } f_1", &["eve.id"], None)
            .named("eve's submission")
            .step("vtc", "verifies it, and records dave's serial as spent")
            .uses(&[
                "PCS::check_proof_in_context",
                "TokenIssuer::signature_ok",
                "TokenIssuer::record_spend",
                "vetting::requirements::evaluate",
            ])
            .act_md(
                "vtc",
                r"$\V{dave.serial}{s^{*}} \mapsto (\V{eve.id}{id_E}, T_{D,E})$ in the spent set",
                &["dave.serial"],
            )
            .send("vtc", "eve", r"\textsf{requestMore}", &[], None)
            .named("the verdict")
            .json("verdict", &verdict_json(&d_eve))
            .aside("eve has one statement of the two she needs")
            .step("dave", "attests for frank, reusing the same token")
            .uses(&["PCS::attest_in_context"])
            .send(
                "dave",
                "frank",
                r"att' = (\V{dave.T.frank}{T_{D,F}}, \dots),\ \text{the same token } s^{*}",
                &["dave.T.frank", "dave.serial"],
                None,
            )
            .named("a second attestation, on a spent token")
            .aside(
                "an adversary hook: an honest engine never re-spends; nothing stops a modified one",
            )
            .step("frank", "accepts it: on its own it is valid")
            .uses(&["PCS::check_attestation_in_context", "token::verify_spend"])
            .check(
                "frank",
                r"\VerifyAtt(att') = 1 \ \wedge\ \Verify(\tvk, s^{*}) = 1",
                accepted,
                "individually valid: frank's engine cannot know the token was spent",
            )
            .step("frank", "is also vetted by carol, by video, then submits")
            .uses(&[
                "TokenWallet::spend",
                "PCS::attest_in_context",
                "PCS::check_attestation_in_context",
                "token::verify_spend",
                "Vtc::challenge",
                "PCS::prove_in_context",
            ])
            .say(
                "frank",
                "now holds two attestations: dave's (in person) and carol's (video)",
            )
            .send("frank", "vtc", r"\pi_F \text{ for } f_2", &[], None)
            .named("frank's submission")
            .step(
                "vtc",
                "verifies the proof: two valid attestations, two distinct tags",
            )
            .uses(&["PCS::check_proof_in_context"])
            .check(
                "vtc",
                r"\VerifyProof(\pi_F) = 1",
                true,
                "the proof itself is sound",
            )
            .step(
                "vtc",
                "checks the tokens: $s^*$ was spent before, under another $(id, T)$",
            )
            .uses(&[
                "TokenIssuer::signature_ok",
                "TokenIssuer::record_spend",
                "TokenIssuer::signature_ok",
                "TokenIssuer::record_spend",
            ])
            .check_md(
                "vtc",
                r"$s^{*}$ was spent before, under $(id_E, T_{D,E}) \ne (id_F, T_{D,F})$",
                false,
                "a double spend: that statement is not counted",
            )
            .step("vtc", "counts what is left")
            .uses(&["vetting::requirements::evaluate"])
            .detail(run.decision(&d3, "frank's facts"))
            .send(
                "vtc",
                "frank",
                r"\textsf{requestMore}(\textit{needs})",
                &[],
                None,
            )
            .named("the verdict")
            .json("verdict", &verdict_json(&d3))
            .highlight(&["needs"]),
        );
        s.outcome(
            "warn",
            "Caught, but not attributed",
            &format!(
                "frank's second statement does not count, so he is still short: {}. The VTC \
                 logged the anomaly ({anomaly}). It cannot say who cheated: the token was \
                 blind-issued, and dave's tags for eve and frank are unrelated.",
                needs_md(&d3)
            ),
        );
        s.section("In detail");
        s.kv(
            "The VTC's anomaly log",
            vtc.tokens
                .anomalies
                .iter()
                .map(|a| ("anomaly", a.clone()))
                .collect(),
        );
        s.p(
            "`issuer-not-vetter` is VTI's generic code for a statement the VTC marked \
             ineligible.",
        );
        s.calls(calls);
        ledger.set("dave", "tokens", &tokens_md(&vetters[2], &tlabel), false);
        ledger.set("carol", "tokens", &tokens_md(&vetters[1], &tlabel), false);
        ledger.set(
            "vtc",
            "anomalies",
            "anomaly log: one serial presented twice",
            false,
        );
        ledger.app(
            "eve",
            goal("requestMore", &[], Some(&d_eve), "one statement so far"),
        );
        ledger.app(
            "frank",
            goal(
                "requestMore",
                &[],
                Some(&d3),
                "dave's statement did not count",
            ),
        );
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 14 · withdrawal ────────────────────────────────────────────────────────────────────
    // carol's withdrawal is verified before alice's attempt; neither verification draws
    // randomness, so the values are those of the terminal walkthrough.
    let (step, calls) = trace::record(|| -> R<_> {
        let (t_c, proof_c) = vetters[1].withdraw(&vtc, &bob_id, &mut rng)?;
        let honest = vtc.withdraw(&bob_id, &t_c, &proof_c)?;
        let (_, proof_a) = vetters[0].withdraw(&vtc, &bob_id, &mut rng)?;
        let forged = vtc.withdraw(&bob_id, &t_c, &proof_a)?;
        let d = vtc.evaluate(&point_text(&bob_id)?, now());
        Ok((t_c, proof_c, proof_a, forged, honest, d))
    });
    let (t_c, proof_c, proof_a, forged, honest, d4) = step?;
    {
        run.val(Val::proof("carol.piw", r"\pi_w", &proof_c).who(&["carol", "vtc"]));
        run.val(
            Val::proof("alice.piw", r"\pi'_w", &proof_a)
                .who(&["alice", "vtc"])
                .note("alice's proof for her own tag at bob's point."),
        );
        let notice = |proof: &predicate_credential_system::sigma::FSProof<Fr>| -> R<J> {
            Ok(json!({ "id": point_text(&bob_id)?, "tag": point_text(&t_c)?, "proof": sj(proof)? }))
        };
        let size = len(&bob_id) + len(&t_c) + len(&proof_c);
        let mut s = Stage::new(
            "withdraw",
            "Withdrawal",
            "Withdrawal by tag",
            "carol → VTC, from any sender",
            "carol changes her mind about bob. She sends the tag and a proof that she knows the \
             key behind it, bound to the community and to $id_B$, and nothing that links to her \
             identifier.",
        );
        s.parties(&["carol", "alice", "vtc"]);
        s.fig(
            Fig::new(&["alice", "carol", "vtc"], "Withdrawal by tag, and an attempt to withdraw someone else's statement.")
                .step("carol", "recomputes her tag for bob, and proves she knows its key")
                .uses(&["kiprf::prove_tag"])
                .act("carol", r"\V{carol.T}{T_1} := H_2(s_B)^{\usk_C}", &["carol.T"])
                .aside("recomputed from her key: the tag she gave bob")
                .act("carol", r"\V{carol.piw}{\pi_w} \gets \PoK_{\ctx_w}\bigl\{K : T_1 = H_2(s_B)^{K}\bigr\}, \quad \ctx_w = (\str{withdraw}, \mathsf{community}, id_B)", &["carol.piw"])
                .send("carol", "vtc", r"(\V{bob.id}{id_B}, \V{carol.T}{T_1}, \V{carol.piw}{\pi_w})", &["bob.id", "carol.T", "carol.piw"], Some(size))
                .named("the withdrawal notice")
                .json("memory", &notice(&proof_c)?)
                .aside("from a fresh sender: nothing in it names carol")
                .step("vtc", "verifies the proof, and withdraws the statement under that tag")
                .uses(&["kiprf::verify_tag"])
                .check_md("vtc", r"$\mathsf{verify}(\pi_w) = 1$, so $(id_B, T_1)$ is withdrawn", honest, "")
                .step("alice", "tries to withdraw carol's statement with a proof for her own key")
                .uses(&["kiprf::prove_tag"])
                .send("alice", "vtc", r"(id_B, T_1, \V{alice.piw}{\pi'_w})", &["alice.piw"], Some(size))
                .named("a forged notice")
                .json("memory", &notice(&proof_a)?)
                .step("vtc", "rejects it")
                .uses(&["kiprf::verify_tag"])
                .check("vtc", r"\mathsf{verify}(\pi'_w) = 1", forged, "alice's proof is for her own tag; she cannot withdraw carol's statement")
                .step("vtc", "counts bob's statements again")
                .uses(&["vetting::requirements::evaluate"])
                .detail(run.decision(&d4, "bob's facts after the withdrawal")),
        );
        s.outcome(
            "more",
            "carol's statement no longer counts",
            &format!(
                "bob's facts now count one vetter. Counted again now, his application would get \
                 `requestMore`, missing {}. Whether a withdrawal after admission should undo it \
                 is a rule the design leaves open.",
                needs_md(&d4)
            ),
        );
        s.calls(calls);
        ledger.set("vtc", "withdrawn", r"withdrawn: $(id_B, T_1)$", false);
        ledger.set(
            "vtc",
            "facts",
            r"for $id_B$: 1 statement counted, 1 withdrawn",
            false,
        );
        ledger.app(
            "bob",
            goal(
                "recount",
                &[],
                Some(&d4),
                "admitted at step 9; counted again now, short of one statement",
            ),
        );
        s.state(ledger.snapshot());
        run.stage(s);
    }

    // ── 15 · summary ───────────────────────────────────────────────────────────────────────
    {
        let mut s = Stage::new(
            "summary",
            "Summary",
            "What rests on what",
            "assumptions, limits and caveats",
            "The properties the run exercised, what each rests on, and where it showed up.",
        );
        s.table(
            "Security, as the paper states it for this construction (random-oracle model)",
            &["property", "what it gives here", "rests on", "seen in"],
            vec![
                vec!["unforgeability".into(), "only the VTC can make vetter credentials and tokens".into(), "the PS assumption (or $q$-MSDH-1) and one-more security of PS blind issuance".into(), "[3](#/stage/root-credential), [4](#/stage/tokens)".into()],
                vec!["attester anonymity".into(), "a tag does not reveal its vetter".into(), "DDH in $\\G_1$ ($\\Tag_{\\mathsf{DDH}}$ is a KI-PRF); perfect re-randomisation of PS".into(), "[6](#/stage/attest), [11](#/stage/privacy)".into()],
                vec!["predicate soundness".into(), "$k$ distinct tags mean $k$ distinct keys, so $k$ distinct members".into(), "key injectivity of the tag (unconditional), knowledge extraction, and the VTC's one-key-per-member binding".into(), "[2](#/stage/vetter-key), [9](#/stage/prove-k2)".into()],
                vec!["self-exclusion".into(), "$T_0 \\notin \\{T_j\\}$: the application key cannot attest for itself".into(), "key injectivity".into(), "[8](#/stage/prove-k1)".into()],
                vec!["binding and freshness".into(), "a proof is bound to its contexts and to one single-use challenge".into(), "$H_1$ a random oracle; the statement is hashed (strong Fiat–Shamir)".into(), "[10](#/stage/wire)".into()],
            ],
        );
        s.callout(
            "warn",
            "Self-exclusion excludes a *key*, not a person. The applicant's key is fresh for \
             every application, so a vetter can attest for a second persona of their own: \
             $T_0$ is under the new key and differs from the vetter's tag. Only $k \\ge 2$ \
             distinct vetters and the token cap limit this; the lab runs it.",
        );
        s.h("Caveats");
        s.list(
            false,
            &[
                "Plain Fiat–Shamir. The theorems hold for sequential issuance and constant $k$; the VTC serialises each signing key behind a lock. Straight-line extractable proofs are the paper's default instantiation.",
                "Every received group element is subgroup-checked. The cofactor of $\\G_1$ in BLS12-381 is divisible by 3, and $T + P_3$ for a point $P_3$ of order 3 would otherwise pass as a *distinct* tag. The lab mounts the attack.",
                "Anonymity is relative to the set of live vetters, which the VTC knows.",
                "This is an in-memory prototype: no transport, no DIDs, no persistence, no JCS canonicalisation. Messages other than the submission are in-memory objects; the page shows them as the crate's serde JSON.",
            ],
        );
        s.p(
            "This prototype runs the `predicate-credential-system` crate of this repository, \
             which implements the modular threshold construction in its explicit \
             self-exclusion format: a class label $\\varphi$ on every credential and a \
             self-exclusion tag $T_0$ in every proof. The formulas on these pages follow the \
             crate's documentation.",
        );
        s.table(
            "Where to read the code",
            &["what", "where"],
            vec![
                vec![
                    "the construction: Attest, Prove, VerifyProof, CheckAtts, root requests".into(),
                    "`src/pcs/construction.rs`".into(),
                ],
                vec![
                    "contexts $\\ctx_j$, $\\ctx_0$ and the digest of $\\mathsf{pp}$".into(),
                    "`src/pcs/context.rs`".into(),
                ],
                vec![
                    "$\\Sigma$-PS: sign, verify, re-randomise, blind issuance".into(),
                    "`src/cred/ps.rs`".into(),
                ],
                vec![
                    "$\\Tag_{\\mathsf{DDH}}$ and the tag proofs".into(),
                    "`src/kiprf/ddh.rs`, `src/kiprf/mod.rs`".into(),
                ],
                vec!["Fiat–Shamir".into(), "`src/sigma/fiat_shamir.rs`".into()],
                vec![
                    "JSON forms of the protocol objects (feature `serde`)".into(),
                    "`src/serialization.rs`".into(),
                ],
                vec![
                    "the VTC, the vetter and applicant engines, tokens".into(),
                    "`demo/src/`".into(),
                ],
                vec![
                    "the design".into(),
                    "`openvtc/docs/design/vetting-hidden-vetters-pcs.md`".into(),
                ],
            ],
        );
        s.state(ledger.snapshot());
        run.stage(s);
    }

    let s = intro(&run);
    run.stages.insert(0, s.to_json());
    Ok(run)
}

/// The binary size of the message called `name` in the flow of stage `stage`, as the page shows it.
fn msg_bytes(run: &Run, stage: &str, name: &str) -> Option<usize> {
    let st = run.stages.iter().find(|s| s["id"] == stage)?;
    st["blocks"]
        .as_array()?
        .iter()
        .filter(|b| b["t"] == "flow")
        .filter_map(|b| b["actions"].as_array())
        .flatten()
        .find(|a| a["msg"]["name"] == name)
        .and_then(|a| a["msg"]["bytes"].as_u64())
        .and_then(|n| usize::try_from(n).ok())
}

/// Step 0, the overview: the problem, the instantiation, every message of the run, and what each step does.
#[allow(clippy::too_many_lines)]
fn intro(run: &Run) -> Stage {
    let b = |stage: &str, name: &str| msg_bytes(run, stage, name);
    let mut s = Stage::new(
        "intro",
        "Overview",
        "Vouching without naming the voucher",
        "an overview: the problem, the instantiation, and every message of the run; nothing runs on this page",
        "An OpenVTC community (a VTC) admits a newcomer once $k$ of its vetters have checked \
         them, under a policy such as *two vetters, one of them in person*. Today every \
         vetter signs with their own DID, so the VTC accumulates a graph of who vouched for \
         whom, and vetters can be pressed about the people they vouched for. Here the \
         applicant proves the count instead, and the vetters stay hidden.",
    );
    s.parties(&["vtc", "vetters", "bob"]);
    s.table(
        "The instantiation",
        &["", "what this run uses", "in the code"],
        vec![
            vec![
                "credentials".into(),
                "$\\Sigma$-PS: Pointcheval–Sanders signatures on $(\\usk, \\varphi)$, issued blind on a commitment to $\\usk$ and shown re-randomised".into(),
                "`cred::PS`".into(),
            ],
            vec![
                "tags".into(),
                "$\\Tag_{\\mathsf{DDH}}(K, s) = H_2(s)^K$ in $\\G_1$: a key-injective PRF, pseudorandom under DDH. $H_2$ is the RFC 9380 hash to $\\G_1$ (`BLS12381G1_XMD:SHA-256_SSWU_RO_`), programmed so that $H_2(c_0) = g_1$".into(),
                "`kiprf::DDH`".into(),
            ],
            vec![
                "proofs".into(),
                "$\\Sigma$-protocols for linear relations over $\\G_1$ and $\\G_T$, made non-interactive with Fiat–Shamir; the challenge hashes the context, the statement and the commitment".into(),
                "`sigma`".into(),
            ],
            vec![
                "tokens".into(),
                "not part of the PCS scheme: the deployment's rate limit. A second PS key $\\tvk$ signs secret serials blind, and an attestation counts only if it spends one".into(),
                "`demo/src/token.rs`".into(),
            ],
            vec![
                "groups".into(),
                "BLS12-381, a type-3 pairing $e : \\G_1 \\times \\G_2 \\to \\G_T$".into(),
                "arkworks 0.6".into(),
            ],
            vec![
                "construction".into(),
                "the modular threshold construction of the predicate credential system, in the crate's explicit self-exclusion format: a class $\\varphi$ on every credential, a tag $T_0$ in every proof".into(),
                "`pcs::PCS`".into(),
            ],
            vec![
                "not used here".into(),
                "the crate's other credential bases (BBS, EQ, MAC) and its Dodis–Yampolskiy PRF".into(),
                "".into(),
            ],
        ],
    );
    let k1 = b("prove-k1", "the join submission");
    let k2 = b("prove-k2", "the join submission");
    let sizes = match (k1, k2) {
        (Some(a), Some(c)) => format!(
            "the proof is {a} B for $k = 1$ (step 8) and {c} B for $k = 2$ (step 9); the statements' metadata travels beside it"
        ),
        _ => "the statements' metadata travels beside the proof".to_string(),
    };
    s.fig(
        Fig::new(
            &["vetters", "bob", "vtc"],
            "Who sends what to whom, in the order of the run. Nothing runs on this page: the step linked from each row runs its part, with its values.",
        )
        .overview()
        .phase("Once per period, before any application: each vetter's VTA and the VTC")
        .step(
            "vetters",
            "enrol, each with a commitment to her key and a proof that one key is behind it",
        )
        .send(
            "vetters",
            "vtc",
            r"\text{root request } (id_j, C, T_0, \pi_{\mathrm{root}})",
            &[],
            b("root-credential", "the root request"),
        )
        .go("root-credential")
        .step(
            "vtc",
            "signs each request blind: a credential on a key it never sees",
        )
        .send(
            "vtc",
            "vetters",
            r"\text{blind signature } \hat\sigma",
            &[],
            b("root-credential", "the blind signature"),
        )
        .go("root-credential")
        .phase("On a fixed schedule, the same for every vetter: the token drip")
        .step(
            "vetters",
            "fetch tokens: commitments to fresh secret serials",
        )
        .send(
            "vetters",
            "vtc",
            r"\text{token request } (C_i, \pi_i)_{i < 3}",
            &[],
            b("tokens", "the token request"),
        )
        .go("tokens")
        .step("vtc", "signs them blind, at most once per tick")
        .send(
            "vtc",
            "vetters",
            r"\text{blind signatures } (\hat\sigma_i)_{i < 3}",
            &[],
            b("tokens", "three blind signatures"),
        )
        .go("tokens")
        .phase("A vetting session, VTA to VTA: the VTC takes no part")
        .step("bob", "asks a vetter to vet him")
        .send(
            "bob",
            "vetters",
            r"id_B \text{ and a metadata template}",
            &[],
            b("attest", "the vetting request"),
        )
        .go("attest")
        .step(
            "vetters",
            "attest after the human check, each spending a token",
        )
        .send(
            "vetters",
            "bob",
            r"att_j = (T_j, \cred^*_j, \varphi_j, \pi_j),\ \app_j,\ \text{token}",
            &[],
            b(
                "attest",
                "the attestation, its metadata and the spent token",
            ),
        )
        .go("attest")
        .phase("Admission, once per submission: bob's VTA and the VTC")
        .step("vtc", "sends bob a single-use challenge")
        .send(
            "vtc",
            "bob",
            r"\mathsf{challenge}",
            &[],
            b("prove-k1", "the challenge"),
        )
        .go("prove-k1")
        .step("bob", "proves that $k$ distinct vetters attested to him")
        .send(
            "bob",
            "vtc",
            r"\pi = \bigl((att_j)_{j \le k}, C, T_0, \pi_0\bigr) \text{ and the statements}",
            &[],
            None,
        )
        .aside(&sizes)
        .go("prove-k1")
        .step(
            "vtc",
            "verifies the proof, counts the distinct tags, and answers",
        )
        .send(
            "vtc",
            "bob",
            r"\textsf{allow} \text{ or } \textsf{requestMore}(\textit{needs})",
            &[],
            None,
        )
        .go("prove-k2")
        .phase("At any time later, from any sender")
        .step(
            "vetters",
            "can withdraw a statement at any time, by its tag alone",
        )
        .send(
            "vetters",
            "vtc",
            r"(id_B, T_j, \pi_w)",
            &[],
            b("withdraw", "the withdrawal notice"),
        )
        .go("withdraw"),
    );
    s.p(
        "The VTC is on most of these arrows because it is the PCS *helper*: it issues the \
         credentials and the tokens, and it verifies the proof. But enrolment happens once per \
         period and the drip on a fixed schedule, for every vetter alike, and the vetting \
         session itself, where a vetter meets bob and attests, never reaches the VTC. Of an \
         application, the VTC sees only the submission round and any withdrawal: a proof, the \
         statements' metadata and spent tokens. None of them names a vetter or links to one; \
         [step 11](#/stage/privacy) shows what the VTC does learn.",
    );
    s.p(
        "Each party's messages are sent by its VTA, the member's own agent, where the engines of \
         `demo/src` run. The prototype has no transport: network metadata such as timing or \
         addresses is outside what these pages show.",
    );
    s.h("What bob proves");
    s.math(
        r"\underbrace{\textstyle\bigwedge_{j=1}^{k} \VerifyAtt(\hvk, id_B, att_j)}_{\text{each from a credentialed vetter}} \;\wedge\; \underbrace{|\{T_1, \dots, T_k\}| = k}_{\text{from }k\text{ distinct vetters}} \;\wedge\; \underbrace{T_0 \notin \{T_j\}}_{\text{not under his own key}} \;\wedge\; \underbrace{P(\varphi_1, \dots, \varphi_k) = 1}_{\text{in a live period}}",
    );
    s.p(
        "This is the check $\\CheckAtts$ of the construction, followed by a proof of \
         knowledge $\\pi_0$ that binds it to bob's identifier. The VTC learns $k$, the \
         metadata of each statement (method, claims, validity) and the period of each \
         vetter's credential. It does not learn which vetters attested.",
    );
    let wire = k2.map_or_else(
        || "the proof".to_string(),
        |n| format!("the {n}-byte proof"),
    );
    s.section("What each step does");
    s.table(
        "",
        &["step", "between", "what happens"],
        vec![
            vec!["[1. Setup](#/stage/setup)".into(), "VTC".into(), "derives $\\mathsf{pp}$ from a deployment label, generates the credential key $\\hvk$ and the token key $\\tvk$, and publishes them with the policy".into()],
            vec!["[2. A vetter's key](#/stage/vetter-key)".into(), "each vetter".into(), "draws a secret key $\\usk$ once for life; her identifier is $id = g_1^{\\usk}$".into()],
            vec!["[3. Root credential](#/stage/root-credential)".into(), "alice ⇄ VTC".into(), "blind issuance of a PS signature on $(\\usk_A, \\varphi_v)$; the VTC binds $id_A$ to alice and never sees $\\usk_A$".into()],
            vec!["[4. Tokens](#/stage/tokens)".into(), "vetters ⇄ VTC".into(), "the drip: blind PS signatures on secret serials, three per vetter per tick; an attestation counts only if it spends one".into()],
            vec!["[5. The applicant](#/stage/applicant-key)".into(), "bob".into(), "a fresh key for this application; every vetter's tag for bob will be $H_2(s_B)^{\\usk_j}$, with $s_B = H_0(id_B)$".into()],
            vec!["[6. carol attests](#/stage/attest)".into(), "bob ⇄ carol".into(), "after a video call, carol spends a token and attests: her tag $T_1$, a re-randomised credential, and one $\\Sigma$-proof bound to the statement's metadata".into()],
            vec!["[7. bob checks it](#/stage/receive)".into(), "bob".into(), "$\\VerifyAtt$ under a context he rebuilds himself, the class, and the token".into()],
            vec!["[8. Prove one](#/stage/prove-k1)".into(), "bob ⇄ VTC".into(), "bob proves $k = 1$ under a fresh challenge; the proof verifies, but the count is short: `requestMore`".into()],
            vec!["[9. Prove two](#/stage/prove-k2)".into(), "alice, bob, VTC".into(), "alice attests in person; bob proves $k = 2$; the VTC answers `allow`".into()],
            vec!["[10. The wire](#/stage/wire)".into(), "bob → VTC".into(), format!("the submission as the VTC receives it, and {wire} inside it, byte by byte")],
            vec!["[11. Privacy](#/stage/privacy)".into(), "VTC".into(), "what the VTC knows, against the ground truth; matching a tag to a vetter is a DDH instance".into()],
            vec!["[12. Double spend](#/stage/double-spend)".into(), "dave, eve, frank, VTC".into(), "dave spends one token on two attestations; the spent set refuses the second without naming dave".into()],
            vec!["[13. Withdrawal](#/stage/withdraw)".into(), "carol → VTC".into(), "carol withdraws her statement by its tag, with a proof that she knows its key; alice cannot withdraw it".into()],
            vec!["[14. Summary](#/stage/summary)".into(), "".into(), "what each property rests on, the caveats, and where to read the code".into()],
        ],
    );
    s.section("The cast");
    s.table(
        "",
        &["", "role", "runs"],
        vec![
            vec!["VTC".into(), "the community; the PCS *helper*: issues credentials and tokens, verifies proofs, counts".into(), "`vtc.rs`".into()],
            vec!["alice, carol, dave".into(), "members with the vetter role".into(), "`vetter.rs`, in each vetter's VTA".into()],
            vec!["bob".into(), "the applicant".into(), "`applicant.rs`, in his VTA".into()],
            vec!["eve, frank".into(), "two more applicants, for the abuse case".into(), "`applicant.rs`".into()],
        ],
    );
    s.callout(
        "info",
        "Every value on these pages comes from one live, seeded run of the prototype in \
         `demo/`, and every ✓ is recomputed from those values. Where a check needs a secret \
         key, the walkthrough reads it through a demo hook and says so; a real engine never \
         exposes it.",
    );
    s.state(json!({ "parties": [], "apps": [] }));
    s
}
