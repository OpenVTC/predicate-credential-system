//! What the page renders: a registry of the values of one run, and stages made of typed blocks.
//!
//! Every group element, scalar and byte string the page shows is registered once, with its
//! canonical compressed encoding, its size, who holds it and whether it is secret. Blocks and
//! TeX refer to values by id (`\V{id}{tex}` in TeX), so the page can link every symbol of a
//! formula to the concrete value it stands for in this run.
//!
//! A stage reads like a stage of the terminal walkthrough: a flow of numbered actions (who
//! computes what, what goes to whom, what is checked), the outcome, and the state of every party
//! afterwards.

use std::collections::HashMap;

use ark_ec::pairing::PairingOutput;
use ark_serialize::CanonicalSerialize;
use pcs_vetting_prototype::{
    scheme::{E, Fr, G1},
    trace::Span,
    vtc::Decision,
};
use predicate_credential_system::{
    serialization::{to_bytes, to_multibase},
    sigma::FSProof,
};
use serde_json::{Map, Value as J, json};
use vta_sdk::protocols::vetting::VettingMethod;

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn enc<T: CanonicalSerialize + ?Sized>(v: &T) -> Vec<u8> {
    to_bytes(v).expect("every protocol value serializes")
}

/// Who an actor string of the engines refers to, as the page names it.
pub fn actor_key(actor: &str) -> String {
    actor
        .strip_prefix("did:example:")
        .unwrap_or(actor)
        .to_lowercase()
}

// ---------------------------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------------------------

/// A value of the run, under construction. `Run::val` registers it.
pub struct Val(Map<String, J>);

impl Val {
    fn new(id: &str, tex: &str, kind: &str) -> Self {
        let mut m = Map::new();
        m.insert("id".into(), id.into());
        m.insert("tex".into(), tex.into());
        m.insert("kind".into(), kind.into());
        Self(m)
    }

    fn with_bytes(id: &str, tex: &str, kind: &str, bytes: &[u8]) -> Self {
        let mut v = Self::new(id, tex, kind);
        v.0.insert("hex".into(), hex(bytes).into());
        v.0.insert("bytes".into(), bytes.len().into());
        v
    }

    /// The multibase text too, since that is how the value travels in JSON.
    fn with_mb(mut self, bytes: &[u8]) -> Self {
        self.0.insert("mb".into(), to_multibase(bytes).into());
        self
    }

    pub fn g1(id: &str, tex: &str, p: &G1) -> Self {
        let b = enc(p);
        Self::with_bytes(id, tex, "G1", &b).with_mb(&b)
    }

    pub fn g2<T: CanonicalSerialize>(id: &str, tex: &str, p: &T) -> Self {
        let b = enc(p);
        Self::with_bytes(id, tex, "G2", &b).with_mb(&b)
    }

    pub fn gt(id: &str, tex: &str, p: &PairingOutput<E>) -> Self {
        Self::with_bytes(id, tex, "GT", &enc(p))
    }

    pub fn fr(id: &str, tex: &str, s: &Fr) -> Self {
        let b = enc(s);
        Self::with_bytes(id, tex, "Fr", &b).with_mb(&b)
    }

    /// A Fiat–Shamir proof in its compact form `c ‖ z_1 ‖ … ‖ z_n`. Its canonical encoding, the
    /// one messages carry, adds an 8-byte length; that text is kept as `mb`, so a proof quoted
    /// in a message links back here.
    pub fn proof(id: &str, tex: &str, p: &FSProof<Fr>) -> Self {
        let mut b = Vec::new();
        p.serialize_compact(&mut b).expect("compact proof");
        let mut v = Self::with_bytes(id, tex, "proof", &b).with_mb(&enc(p));
        v.0.insert(
            "note".into(),
            format!(
                "Compact form: the challenge $c$ and {} response{}, {} B. The canonical encoding in messages adds an 8-byte length.",
                p.responses.len(),
                if p.responses.len() == 1 { "" } else { "s" },
                b.len()
            )
            .into(),
        );
        v
    }

    pub fn bytes(id: &str, tex: &str, b: &[u8]) -> Self {
        Self::with_bytes(id, tex, "bytes", b)
    }

    /// Bytes that travel in multibase, like a whole proof or a key.
    pub fn bytes_mb(id: &str, tex: &str, b: &[u8]) -> Self {
        Self::with_bytes(id, tex, "bytes", b).with_mb(b)
    }

    /// A composite of one group, like a signature `(σ_1, σ_2)`: one encoding, one multibase
    /// string in messages.
    pub fn encoded(id: &str, tex: &str, kind: &str, b: &[u8]) -> Self {
        Self::with_bytes(id, tex, kind, b).with_mb(b)
    }

    pub fn text(id: &str, tex: &str, s: &str) -> Self {
        let mut v = Self::new(id, tex, "text");
        v.0.insert("text".into(), s.into());
        v.0.insert("bytes".into(), s.len().into());
        v
    }

    /// A secret the engines keep to themselves; the walkthrough cannot read it either.
    pub fn hidden(id: &str, tex: &str, kind: &str) -> Self {
        let mut v = Self::new(id, tex, kind);
        v.0.insert("secret".into(), true.into());
        v.0.insert("hidden".into(), true.into());
        v
    }

    /// A secret the walkthrough reads through a demo hook (a real engine never exposes it).
    pub fn secret(mut self) -> Self {
        self.0.insert("secret".into(), true.into());
        self
    }

    /// Who holds the value.
    pub fn who(mut self, who: &[&str]) -> Self {
        self.0.insert("who".into(), json!(who));
        self
    }

    pub fn note(mut self, md: &str) -> Self {
        self.0.insert("note".into(), md.into());
        self
    }
}

// ---------------------------------------------------------------------------------------------
// Flows: what happens in a stage, action by action
// ---------------------------------------------------------------------------------------------

/// A protocol flow: numbered actions, each by one party. An action is what one party does in
/// one go: computations and checks in its own column, often ending with a message to another
/// party. The page plays the actions in order, with the engine calls each one made.
///
/// Rows of a party other than the current action's start a new action, and so does a row after
/// a message, so flows written row by row (the lab's) group into actions by themselves.
pub struct Fig {
    lanes: Vec<String>,
    caption: String,
    actions: Vec<Map<String, J>>,
    /// The last thing added was a message: an aside attaches to it.
    last_send: bool,
    overview: bool,
}

fn new_action(actor: &str, title: Option<&str>) -> Map<String, J> {
    let mut a = Map::new();
    a.insert("actor".into(), actor.into());
    if let Some(t) = title {
        a.insert("title".into(), t.into());
    }
    a.insert("rows".into(), J::Array(Vec::new()));
    a
}

impl Fig {
    pub fn new(lanes: &[&str], caption: &str) -> Self {
        Self {
            lanes: lanes.iter().map(|l| (*l).to_string()).collect(),
            caption: caption.to_string(),
            actions: Vec::new(),
            last_send: false,
            overview: false,
        }
    }

    fn open_for(&mut self, actor: &str) -> &mut Map<String, J> {
        let reuse = matches!(self.actions.last(),
            Some(a) if a.get("actor").and_then(J::as_str) == Some(actor) && !a.contains_key("msg"));
        if !reuse {
            self.actions.push(new_action(actor, None));
        }
        self.last_send = false;
        self.actions.last_mut().expect("an action is open")
    }

    fn row(mut self, lane: &str, row: J) -> Self {
        if let Some(J::Array(rows)) = self.open_for(lane).get_mut("rows") {
            rows.push(row);
        }
        self
    }

    /// A heading between actions: when, and between whom, the actions that follow happen.
    pub fn phase(mut self, md: &str) -> Self {
        let mut sep = Map::new();
        sep.insert("sep".into(), md.into());
        self.actions.push(sep);
        self.last_send = false;
        self
    }

    /// Start a new action by `actor`, titled in plain words ("signs the request blind").
    pub fn step(mut self, actor: &str, title: &str) -> Self {
        self.actions.push(new_action(actor, Some(title)));
        self.last_send = false;
        self
    }

    /// A computation in `lane`, with the values it produces.
    pub fn act(self, lane: &str, tex: &str, vals: &[&str]) -> Self {
        self.row(lane, json!({ "t": "act", "tex": tex, "vals": vals }))
    }

    /// A computation said in words with inline TeX (`$…$`), where a formula would be prose.
    pub fn act_md(self, lane: &str, text: &str, vals: &[&str]) -> Self {
        self.row(lane, json!({ "t": "act", "text": text, "vals": vals }))
    }

    /// A check said in words with inline TeX; `md` says what it establishes.
    pub fn check_md(self, lane: &str, text: &str, ok: bool, md: &str) -> Self {
        self.row(
            lane,
            json!({ "t": "check", "text": text, "ok": ok, "md": md }),
        )
    }

    /// A step in words, in `lane` (a human check, a policy decision).
    pub fn say(self, lane: &str, md: &str) -> Self {
        self.row(lane, json!({ "t": "say", "md": md }))
    }

    /// A verification run by `lane`; `md` says what it establishes.
    pub fn check(self, lane: &str, tex: &str, ok: bool, md: &str) -> Self {
        self.row(
            lane,
            json!({ "t": "check", "tex": tex, "ok": ok, "md": md }),
        )
    }

    /// A message from one party to another. It ends the sender's current action, or is an
    /// action of its own.
    pub fn send(
        mut self,
        from: &str,
        to: &str,
        tex: &str,
        vals: &[&str],
        bytes: Option<usize>,
    ) -> Self {
        let attach = matches!(self.actions.last(),
            Some(a) if a.get("actor").and_then(J::as_str) == Some(from) && !a.contains_key("msg"));
        if !attach {
            self.actions.push(new_action(from, None));
        }
        let a = self.actions.last_mut().expect("an action is open");
        a.insert("to".into(), to.into());
        a.insert(
            "msg".into(),
            json!({ "tex": tex, "vals": vals, "bytes": bytes }),
        );
        self.last_send = true;
        self
    }

    fn last(&mut self) -> Option<&mut Map<String, J>> {
        self.actions.last_mut()
    }

    fn last_msg(&mut self) -> Option<&mut Map<String, J>> {
        match self.last().and_then(|a| a.get_mut("msg")) {
            Some(J::Object(m)) => Some(m),
            _ => None,
        }
    }

    /// The name of the last message, in plain words ("the root request").
    pub fn named(mut self, name: &str) -> Self {
        if let Some(m) = self.last_msg() {
            m.insert("name".into(), name.into());
        }
        self
    }

    /// The content of the last message, as JSON. `kind` says what the JSON is: `wire` (the
    /// format the VTC receives), `verdict` (the shape of the join ceremony's answer) or
    /// `memory` (an in-memory message of the prototype, shown as JSON).
    pub fn json(mut self, kind: &str, value: &J) -> Self {
        let text = serde_json::to_string_pretty(value).unwrap_or_default();
        if let Some(m) = self.last_msg() {
            m.insert("kind".into(), kind.into());
            m.insert("json".into(), text.into());
        }
        self
    }

    /// Members of the last message's JSON to highlight.
    pub fn highlight(mut self, keys: &[&str]) -> Self {
        if let Some(m) = self.last_msg() {
            m.insert("highlight".into(), json!(keys));
        }
        self
    }

    /// The engine calls the current action makes, matched in order against the stage's trace.
    pub fn uses(mut self, calls: &[&str]) -> Self {
        if let Some(a) = self.last() {
            a.insert("uses".into(), json!(calls));
        }
        self
    }

    /// A block shown inside the current action: both sides of a pairing, a derivation, facts.
    pub fn detail(mut self, block: J) -> Self {
        if let Some(a) = self.last() {
            let d = a.entry("detail").or_insert_with(|| J::Array(Vec::new()));
            if let J::Array(v) = d {
                v.push(block);
            }
        }
        self
    }

    /// The current action links to a stage (the overview of the intro).
    pub fn go(mut self, stage: &str) -> Self {
        if let Some(a) = self.last() {
            a.insert("go".into(), stage.into());
        }
        self
    }

    /// A short note under the last row, or under the last message.
    pub fn aside(mut self, md: &str) -> Self {
        let to_msg = self.last_send;
        if to_msg {
            if let Some(m) = self.last_msg() {
                m.insert("aside".into(), md.into());
            }
        } else if let Some(J::Array(rows)) = self.last().and_then(|a| a.get_mut("rows"))
            && let Some(J::Object(row)) = rows.last_mut()
        {
            row.insert("aside".into(), md.into());
        }
        self
    }

    /// Show the flow as a static map of messages (the intro's overview): nothing is played, and
    /// no action of it runs on its page.
    pub fn overview(mut self) -> Self {
        self.overview = true;
        self
    }

    fn to_json(&self) -> J {
        json!({
            "t": if self.overview { "map" } else { "flow" },
            "lanes": self.lanes, "caption": self.caption, "actions": self.actions,
        })
    }
}

// ---------------------------------------------------------------------------------------------
// Checks and derivations
// ---------------------------------------------------------------------------------------------

/// A claim recomputed in this run.
pub struct Check(Map<String, J>);

impl Check {
    pub fn new(ok: bool, md: &str) -> Self {
        let mut m = Map::new();
        m.insert("ok".into(), ok.into());
        m.insert("md".into(), md.into());
        Self(m)
    }

    pub fn tex(mut self, tex: &str) -> Self {
        self.0.insert("tex".into(), tex.into());
        self
    }

    /// The two sides of a pairing equation, as `G_T` values of the registry.
    pub fn sides(mut self, lhs: &str, rhs: &str) -> Self {
        self.0.insert("sides".into(), json!([lhs, rhs]));
        self
    }

    /// What the code returned, verbatim (e.g. an error message).
    pub fn observed(mut self, text: impl Into<String>) -> Self {
        self.0.insert("observed".into(), text.into().into());
        self
    }

    /// Who runs the check: an engine, or the walkthrough peeking at a secret.
    pub fn by(mut self, who: &str) -> Self {
        self.0.insert("by".into(), who.into());
        self
    }
}

/// A block of checks, for a stage or inside an action.
pub fn checks(title: &str, items: Vec<Check>) -> J {
    let items: Vec<J> = items.into_iter().map(|c| J::Object(c.0)).collect();
    json!({ "t": "checks", "title": title, "items": items })
}

/// A derivation, line by line.
pub fn derive(title: &str, md: &str, lines: Vec<J>) -> J {
    json!({ "t": "derive", "title": title, "md": md, "lines": lines })
}

/// One line of a derivation: a formula, the values it involves, and optionally a verdict.
pub fn line(tex: &str, vals: &[&str]) -> J {
    json!({ "tex": tex, "vals": vals })
}

pub fn line_ok(tex: &str, vals: &[&str], ok: bool, md: &str) -> J {
    json!({ "tex": tex, "vals": vals, "ok": ok, "md": md })
}

pub fn line_md(md: &str) -> J {
    json!({ "md": md })
}

// ---------------------------------------------------------------------------------------------
// Stages
// ---------------------------------------------------------------------------------------------

pub struct Stage {
    id: String,
    phase: String,
    title: String,
    who: String,
    lede: String,
    parties: Vec<String>,
    blocks: Vec<J>,
    calls: Vec<J>,
    lab: Vec<String>,
    state: Option<J>,
}

impl Stage {
    pub fn new(id: &str, phase: &str, title: &str, who: &str, lede: &str) -> Self {
        Self {
            id: id.into(),
            phase: phase.into(),
            title: title.into(),
            who: who.into(),
            lede: lede.into(),
            parties: Vec::new(),
            blocks: Vec::new(),
            calls: Vec::new(),
            lab: Vec::new(),
            state: None,
        }
    }

    /// The parties of this stage, in the order the header shows them.
    pub fn parties(&mut self, who: &[&str]) {
        self.parties = who.iter().map(|s| (*s).to_string()).collect();
    }

    pub fn p(&mut self, md: &str) {
        self.blocks.push(json!({ "t": "p", "md": md }));
    }

    pub fn h(&mut self, text: &str) {
        self.blocks.push(json!({ "t": "h", "text": text }));
    }

    /// A divider before the material that explains a stage rather than runs it.
    pub fn section(&mut self, text: &str) {
        self.blocks.push(json!({ "t": "section", "text": text }));
    }

    pub fn math(&mut self, tex: &str) {
        self.blocks.push(json!({ "t": "math", "tex": tex }));
    }

    pub fn fig(&mut self, fig: Fig) {
        self.blocks.push(fig.to_json());
    }

    /// What the stage achieved, and what is still missing. `tone`: `ok`, `more`, `warn` or
    /// `info`.
    pub fn outcome(&mut self, tone: &str, title: &str, md: &str) {
        self.blocks
            .push(json!({ "t": "outcome", "tone": tone, "title": title, "md": md }));
    }

    pub fn checks(&mut self, title: &str, items: Vec<Check>) {
        self.blocks.push(checks(title, items));
    }

    pub fn derive(&mut self, title: &str, md: &str, lines: Vec<J>) {
        self.blocks.push(derive(title, md, lines));
    }

    pub fn values(&mut self, title: &str, ids: &[&str]) {
        self.blocks
            .push(json!({ "t": "values", "title": title, "ids": ids }));
    }

    pub fn callout(&mut self, tone: &str, md: &str) {
        self.blocks
            .push(json!({ "t": "callout", "tone": tone, "md": md }));
    }

    pub fn list(&mut self, ordered: bool, items: &[&str]) {
        self.blocks
            .push(json!({ "t": "list", "ordered": ordered, "items": items }));
    }

    pub fn table(&mut self, title: &str, head: &[&str], rows: Vec<Vec<String>>) {
        self.blocks
            .push(json!({ "t": "table", "title": title, "head": head, "rows": rows }));
    }

    pub fn kv(&mut self, title: &str, items: Vec<(&str, String)>) {
        let items: Vec<J> = items
            .into_iter()
            .map(|(k, v)| json!({ "k": k, "v": v }))
            .collect();
        self.blocks
            .push(json!({ "t": "kv", "title": title, "items": items }));
    }

    pub fn block(&mut self, block: J) {
        self.blocks.push(block);
    }

    pub fn calls(&mut self, spans: Vec<Span>) {
        self.calls.extend(spans.into_iter().map(|s| span_json(&s)));
    }

    pub fn lab(&mut self, ids: &[&str]) {
        self.lab.extend(ids.iter().map(|s| (*s).to_string()));
    }

    /// Who holds what once the stage is over (see [`Ledger`]).
    pub fn state(&mut self, state: J) {
        self.state = Some(state);
    }

    pub fn to_json(&self) -> J {
        json!({
            "id": self.id, "phase": self.phase, "title": self.title, "who": self.who,
            "lede": self.lede, "parties": self.parties, "blocks": self.blocks,
            "calls": self.calls, "lab": self.lab, "state": self.state,
        })
    }
}

pub fn span_json(s: &Span) -> J {
    json!({
        "depth": s.depth, "actor": actor_key(&s.actor), "call": s.call, "runs": s.runs,
        "us": (s.nanos as f64) / 1000.0, "error": s.error, "note": s.note,
    })
}

// ---------------------------------------------------------------------------------------------
// The state of the world between stages
// ---------------------------------------------------------------------------------------------

/// Who holds what, and how each application stands, as the stages go by. Each snapshot marks
/// what changed since the previous one.
#[derive(Default)]
pub struct Ledger {
    parties: Vec<(String, Vec<Item>)>,
    apps: Vec<(String, J, u32)>,
    tick: u32,
}

struct Item {
    key: String,
    md: String,
    secret: bool,
    changed: u32,
}

impl Ledger {
    /// Set what `who` holds under `key` (replacing what was there).
    pub fn set(&mut self, who: &str, key: &str, md: &str, secret: bool) {
        let tick = self.tick;
        let items = match self.parties.iter_mut().position(|(w, _)| w == who) {
            Some(i) => &mut self.parties[i].1,
            None => {
                self.parties.push((who.to_string(), Vec::new()));
                &mut self.parties.last_mut().expect("just pushed").1
            }
        };
        match items.iter_mut().find(|i| i.key == key) {
            Some(i) if i.md == md && i.secret == secret => {}
            Some(i) => {
                i.md = md.to_string();
                i.secret = secret;
                i.changed = tick;
            }
            None => items.push(Item {
                key: key.to_string(),
                md: md.to_string(),
                secret,
                changed: tick,
            }),
        }
    }

    /// How the application of `subject` stands (see [`goal`]).
    pub fn app(&mut self, subject: &str, goal: J) {
        let tick = self.tick;
        match self.apps.iter_mut().find(|(s, _, _)| s == subject) {
            Some((_, g, _)) if *g == goal => {}
            Some((_, g, changed)) => {
                *g = goal;
                *changed = tick;
            }
            None => self.apps.push((subject.to_string(), goal, tick)),
        }
    }

    pub fn snapshot(&mut self) -> J {
        let tick = self.tick;
        self.tick += 1;
        json!({
            "parties": self.parties.iter().map(|(who, items)| json!({
                "who": who,
                "items": items.iter().map(|i| json!({
                    "md": i.md, "secret": i.secret, "new": i.changed == tick,
                })).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "apps": self.apps.iter().map(|(s, g, changed)| {
                let mut g = g.clone();
                g["subject"] = s.as_str().into();
                g["new"] = (*changed == tick).into();
                g
            }).collect::<Vec<_>>(),
        })
    }
}

/// How an application stands against the policy of this run (`minStatements` distinct vetters,
/// `minByMethod.inPerson` of them in person): from the VTC's decision when there is one, else
/// from what the applicant holds.
pub fn goal(status: &str, held: &[VettingMethod], d: Option<&Decision>, md: &str) -> J {
    let req = crate::scenario::requirements();
    let need_all = req["minStatements"].as_u64().unwrap_or(0);
    let need_in_person = req["minByMethod"]["inPerson"].as_u64().unwrap_or(0);
    let (count, in_person, needs) = match d {
        Some(d) => (
            d.evaluation.distinct_vetters(),
            d.evaluation
                .by_method
                .get(&VettingMethod::InPerson)
                .copied()
                .unwrap_or(0) as usize,
            d.evaluation
                .needs
                .iter()
                .map(|n| n.to_wire())
                .collect::<Vec<_>>(),
        ),
        None => (
            held.len(),
            held.iter()
                .filter(|m| **m == VettingMethod::InPerson)
                .count(),
            Vec::new(),
        ),
    };
    json!({
        "status": status,
        "source": if d.is_some() { "vtc" } else { "held" },
        "items": [
            { "md": "distinct vetters", "have": count, "need": need_all },
            { "md": "in person", "have": in_person, "need": need_in_person },
        ],
        "needs": needs,
        "md": md,
    })
}

// ---------------------------------------------------------------------------------------------
// The run
// ---------------------------------------------------------------------------------------------

#[derive(Default)]
pub struct Run {
    values: Map<String, J>,
    /// multibase text → value id, so that a tag or an identifier quoted in the facts or on the
    /// wire links back to its value.
    by_mb: HashMap<String, String>,
    pub stages: Vec<J>,
}

impl Run {
    /// Register a value (the first registration of an id wins) and return its id.
    pub fn val(&mut self, v: Val) -> String {
        let id = v.0["id"].as_str().unwrap_or_default().to_string();
        if let Some(mb) = v.0.get("mb").and_then(J::as_str) {
            self.by_mb
                .entry(mb.to_string())
                .or_insert_with(|| id.clone());
        }
        self.values.entry(id.clone()).or_insert(J::Object(v.0));
        id
    }

    pub fn by_mb(&self, mb: &str) -> Option<&str> {
        self.by_mb.get(mb).map(String::as_str)
    }

    pub fn stage(&mut self, s: Stage) {
        self.stages.push(s.to_json());
    }

    pub fn values(&self) -> &Map<String, J> {
        &self.values
    }

    /// The facts the VTC handed to VTI's counting rule, and its verdict. The facts are the
    /// VTC's `StatementRecord`s, serialised as they are.
    pub fn decision(&self, d: &Decision, title: &str) -> J {
        let e = &d.evaluation;
        let statements: Vec<J> = d
            .statements
            .iter()
            .map(|s| {
                json!({
                    "id": s.id, "issuer": s.issuer, "vid": self.by_mb(&s.issuer),
                    "method": s.method.to_string(), "counted": s.counted,
                    "eligible": s.eligible, "revoked": s.revoked, "failures": s.failures,
                })
            })
            .collect();
        json!({
            "t": "decision", "title": title, "admit": e.satisfied(),
            "distinct": e.distinct_vetters(),
            "needs": e.needs.iter().map(|n| n.to_wire()).collect::<Vec<_>>(),
            "statements": statements,
            "json": serde_json::to_string_pretty(&d.statements).unwrap_or_default(),
        })
    }
}
