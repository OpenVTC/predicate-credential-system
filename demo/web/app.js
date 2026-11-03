/* Hidden vetting, step by step: the page. Plain JavaScript, no build step, no network beyond
   this server. Every piece of data is inserted as text or through KaTeX, never as HTML.

   A step plays like a stage of the terminal walkthrough: its numbered actions run one after
   another, each showing the engine calls it made (with the times measured in the run) before its
   result, its message (as JSON) and its checks appear. The pacing is for the audience: the whole
   run was computed by the server when the page loaded. */
"use strict";
(() => {
  // ------------------------------------------------------------------------------ state
  const S = {
    run: null,          // the run document from /api/run
    values: {},         // the value registry in use for the page on screen
    stageIndex: {},     // stage id -> index
    stageJson: [],      // stringified stages, for "appears in"
    mbIndex: {},        // multibase text -> value id
    route: { kind: "stage", id: "intro" },
    selected: null,
    presenting: false,
    showVals: true,
    pace: "auto",
    seen: new Set(),    // stages played to the end, for this seed
    player: null,       // the player of the page on screen
    items: [],          // the actions of the page on screen
    userScrollAt: 0,
    lab: {},            // lab results by id
    labNonce: {},
    labParam: {},
  };
  /** Pace: a factor on every delay. `manual` waits for a key before each action. */
  const PACE = { auto: 1, slow: 1.8, manual: 0.75, instant: 0 };
  const store = {
    get(k) { try { return window.localStorage.getItem(k); } catch { return null; } },
    set(k, v) { try { window.localStorage.setItem(k, v); } catch { /* private mode */ } },
  };
  const reducedMotion = () => window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  // ------------------------------------------------------------------------------ DOM helpers
  function el(tag, attrs, ...kids) {
    const n = document.createElement(tag);
    if (attrs) {
      for (const [k, v] of Object.entries(attrs)) {
        if (v == null || v === false) continue;
        if (k === "class") n.className = v;
        else if (k === "text") n.textContent = v;
        else if (k.startsWith("on")) n.addEventListener(k.slice(2), v);
        else n.setAttribute(k, v === true ? "" : v);
      }
    }
    for (const kid of kids) if (kid != null && kid !== false) n.append(kid);
    return n;
  }
  const $ = (sel, root = document) => root.querySelector(sel);
  const svgNS = "http://www.w3.org/2000/svg";
  function svg(viewBox, paths, cls) {
    const s = document.createElementNS(svgNS, "svg");
    s.setAttribute("viewBox", viewBox);
    s.setAttribute("aria-hidden", "true");
    if (cls) s.setAttribute("class", cls);
    for (const p of paths) {
      const [d, pc] = Array.isArray(p) ? p : [p, null];
      const path = document.createElementNS(svgNS, "path");
      path.setAttribute("d", d);
      if (pc) path.setAttribute("class", pc);
      s.append(path);
    }
    return s;
  }
  const icon = (paths, cls) => svg("0 0 24 24", paths, cls);
  function mark(ok) {
    return el("span", { class: ok ? "mark-ok" : "mark-no", role: "img", "aria-label": ok ? "holds" : "fails" },
      icon(ok ? ["M5 12.5l4.2 4.2L19 7"] : ["M7 7l10 10M17 7L7 17"]));
  }
  const capFirst = (s) => (s ? s.charAt(0).toUpperCase() + s.slice(1) : s);
  const sleepPlain = (ms) => new Promise((r) => setTimeout(r, ms));

  // ------------------------------------------------------------------------------ KaTeX
  const MACROS = {
    "\\V": "\\htmlData{v=#1}{#2}",
    "\\Ga": "\\htmlClass{k-G1}{#1}",
    "\\Gb": "\\htmlClass{k-G2}{#1}",
    "\\gone": "\\htmlClass{k-G1}{g_1}",
    "\\gtil": "\\htmlClass{k-G2}{\\tilde g}",
    "\\G": "\\mathbb{G}",
    "\\Z": "\\mathbb{Z}",
    "\\sample": "\\xleftarrow{\\$}",
    "\\Tag": "\\mathsf{Tag}",
    "\\PoK": "\\mathsf{PoK}",
    "\\ctx": "\\mathsf{ctx}",
    "\\usk": "\\mathit{usk}",
    "\\hvk": "\\mathsf{hvk}",
    "\\tvk": "\\mathsf{tvk}",
    "\\tsk": "\\mathsf{tsk}",
    "\\app": "\\mathit{app}",
    "\\cred": "\\mathit{cred}",
    "\\EncPred": "\\mathsf{EncPred}",
    "\\Unblind": "\\mathsf{Unblind}",
    "\\ReRand": "\\mathsf{ReRand}",
    "\\Verify": "\\mathsf{Verify}",
    "\\VerifyFS": "\\mathsf{Verify}_{\\mathsf{FS}}",
    "\\VerifyAtt": "\\mathsf{VerifyAtt}",
    "\\VerifyProof": "\\mathsf{VerifyProof}",
    "\\CheckAtts": "\\mathsf{CheckAtts}_P",
    "\\str": "\\texttt{\"#1\"}",
  };
  const KATEX_OPTS = {
    throwOnError: false,
    strict: "ignore",
    macros: MACROS,
    trust: (ctx) => ctx.command === "\\htmlData" || ctx.command === "\\htmlClass",
  };
  function tex(target, src, display = false) {
    try {
      window.katex.render(src, target, { ...KATEX_OPTS, displayMode: display });
    } catch {
      target.textContent = src;
    }
    decorate(target);
    return target;
  }
  function texSpan(src, cls) { return tex(el("span", { class: cls }), src); }

  /** Colour every linked symbol by the group of its value, and wire it to the inspector. */
  function decorate(root) {
    for (const n of root.querySelectorAll("[data-v]")) {
      const v = S.values[n.dataset.v];
      if (!v) continue;
      n.classList.add("k-" + v.kind);
      if (v.secret) n.classList.add("secret");
      bindValue(n, n.dataset.v);
    }
  }
  function bindValue(node, vid) {
    node.addEventListener("mouseenter", () => light(vid, true));
    node.addEventListener("mouseleave", () => light(vid, false));
    node.addEventListener("click", (e) => { e.stopPropagation(); select(vid); });
  }
  function light(vid, on) {
    const q = CSS.escape(vid);
    for (const n of document.querySelectorAll(`[data-v="${q}"], [data-vid="${q}"]`)) n.classList.toggle("lit", on);
  }

  // ------------------------------------------------------------------------------ inline markup
  // $tex$, **bold**, *italic*, `code`, [text](#/route)
  const INLINE = /(\$[^$]+\$)|(\*\*[^*]+\*\*)|(\*[^*\s][^*]*\*)|(`[^`]+`)|(\[[^\]]+\]\(#\/[^)\s]+\))/g;
  function md(text, target) {
    if (text == null) return target;
    let last = 0;
    const re = new RegExp(INLINE.source, "g");
    let m;
    while ((m = re.exec(text))) {
      if (m.index > last) target.append(text.slice(last, m.index));
      const s = m[0];
      if (m[1]) target.append(texSpan(s.slice(1, -1)));
      else if (m[2]) target.append(md(s.slice(2, -2), el("strong")));
      else if (m[3]) target.append(md(s.slice(1, -1), el("em")));
      else if (m[4]) target.append(el("code", { text: s.slice(1, -1) }));
      else if (m[5]) {
        const mm = /^\[([^\]]+)\]\((#\/[^)]+)\)$/.exec(s);
        target.append(md(mm[1], el("a", { href: mm[2] })));
      }
      last = re.lastIndex;
    }
    if (last < text.length) target.append(text.slice(last));
    return target;
  }
  /** TeX and markup stripped, for titles and tooltips. */
  function plain(s) {
    return String(s || "")
      .replace(/\$([^$]*)\$/g, (_, t) => t.replace(/\\(?:mathsf|mathit|mathrm|textsf|text|V)\{([^}]*)\}/g, "$1").replace(/\\[a-zA-Z]+\s?|[{}^]/g, "").replace(/_/g, ""))
      .replace(/[*`]/g, "");
  }

  // ------------------------------------------------------------------------------ values
  const KIND_NAME = { G1: "𝔾₁", G2: "𝔾₂", GT: "𝔾_T element", Fr: "scalar in ℤ_p", bytes: "bytes", text: "text", proof: "Fiat–Shamir proof" };
  function kindName(v) {
    if (v.kind === "G1") return v.bytes > 48 ? `${v.bytes / 48} points of 𝔾₁` : "𝔾₁ point";
    if (v.kind === "G2") return v.bytes > 96 ? "𝔾₂ points" : "𝔾₂ point";
    return KIND_NAME[v.kind] || v.kind;
  }
  function shortHex(hex) { return hex.length > 22 ? `${hex.slice(0, 8)}…${hex.slice(-6)}` : hex; }
  function chip(vid, opts = {}) {
    const v = S.values[vid];
    if (!v) return null;
    const b = el("button", { type: "button", class: `chip k-${v.kind}${v.secret ? " secret" : ""}`, "data-vid": vid,
      title: v.hidden ? "secret, not exposed" : `${kindName(v)}, ${v.bytes} B` });
    b.append(texSpan(v.tex, "sym"));
    if (v.hidden) {
      b.append(el("span", { class: "hex", text: "not exposed" }));
    } else if (v.kind === "text") {
      if (!opts.symOnly) b.append(el("span", { class: "hex", text: v.text.length > 26 ? v.text.slice(0, 24) + "…" : v.text }));
    } else if (!opts.symOnly) {
      b.append(el("span", { class: "hex", text: shortHex(v.hex) }));
      if (opts.size !== false) b.append(el("span", { class: "sz", text: `${v.bytes} B` }));
    }
    if (v.secret) b.prepend(icon(["M7 11V8.5a5 5 0 0 1 10 0V11", "M5.5 11h13v9h-13z"], "lock"));
    bindValue(b, vid);
    if (S.selected === vid) b.classList.add("sel");
    return b;
  }
  function chips(vids) {
    const box = el("div", { class: "vals" });
    for (const vid of vids || []) { const c = chip(vid); if (c) box.append(c); }
    return box.childElementCount ? box : null;
  }
  function copyButton(text, label = "Copy") {
    if (!navigator.clipboard) return null;
    const b = el("button", { type: "button", class: "mini", text: label });
    b.addEventListener("click", async (e) => {
      e.stopPropagation();
      try { await navigator.clipboard.writeText(text); b.textContent = "Copied"; b.classList.add("copied"); } catch { b.textContent = "Copy failed"; }
      setTimeout(() => { b.textContent = label; b.classList.remove("copied"); }, 1400);
    });
    return b;
  }

  // ------------------------------------------------------------------------------ actors
  function actorOf(id) { return (S.run.actors && S.run.actors[id]) || { name: id, role: "" }; }
  function actorChip(id) {
    const a = actorOf(id);
    const c = el("span", { class: `actor ${id}`, title: a.role });
    const av = el("span", { class: "av", "aria-hidden": "true" });
    if (id === "vtc") av.append(icon(["M4 20h16", "M5.5 20V10m4.33 10V10m4.34 10V10m4.33 10V10", "M3.5 10 12 4.5 20.5 10z"]));
    else if (id === "public") av.textContent = "∀";
    else if (id === "vetters") av.append(icon(["M8 9.5a2 2 0 1 0 0 .01M16 9.5a2 2 0 1 0 0 .01M12 15a2 2 0 1 0 0 .01"]));
    else av.textContent = (a.name || id).charAt(0).toUpperCase();
    c.append(av, el("span", { text: a.name }));
    return c;
  }
  function arrow() {
    return el("span", { class: "arrow", "aria-label": "to" }, svg("0 0 34 12", [["M1 6h30", "shaft"], "M26.5 1.8 31.5 6l-5 4.2"]));
  }

  // ------------------------------------------------------------------------------ JSON
  const JSON_RE = /("(?:[^"\\]|\\.)*")(\s*:)?|(-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)|\b(true|false|null)\b/g;
  function jsonPre(src, { highlight = [], shorten = true } = {}) {
    const pre = el("pre", { class: "json" });
    const hl = new Set(highlight || []);
    const re = new RegExp(JSON_RE.source, "g");
    let last = 0, m;
    while ((m = re.exec(src))) {
      if (m.index > last) pre.append(src.slice(last, m.index));
      if (m[1] && m[2]) {
        const key = m[1].slice(1, -1);
        pre.append(el("span", { class: `k${hl.has(key) ? " hl" : ""}`, text: m[1] }), m[2]);
      } else if (m[1]) pre.append(jsonString(m[1], shorten));
      else if (m[3]) pre.append(el("span", { class: "n", text: m[3] }));
      else if (m[4]) pre.append(el("span", { class: "b", text: m[4] }));
      last = re.lastIndex;
    }
    if (last < src.length) pre.append(src.slice(last));
    return pre;
  }
  function jsonString(quoted, shorten) {
    const str = quoted.slice(1, -1);
    const vid = S.mbIndex[str];
    const v = vid && S.values[vid];
    const long = str.length > 40;
    const short = `"${str.slice(0, 14)}…${str.slice(-6)}"`;
    if (v) {
      const s = el("span", { class: `link k-${v.kind}`, "data-vid": vid, title: `${plain("$" + v.tex + "$")}, ${v.bytes} B: select to inspect`, text: shorten && long ? short : quoted });
      bindValue(s, vid);
      return s;
    }
    if (shorten && long) {
      const s = el("span", { class: "s cut", tabindex: "0", role: "button", title: `${str.length} characters: select to show them all`, text: short });
      let open = false;
      const toggle = (e) => { e.stopPropagation(); open = !open; s.textContent = open ? quoted : short; };
      s.addEventListener("click", toggle);
      s.addEventListener("keydown", (e) => { if (e.key === "Enter") toggle(e); });
      return s;
    }
    return el("span", { class: "s", text: quoted });
  }
  function jsonBox(src, highlight, { shorten = true, clamp = 18 } = {}) {
    const lines = src.split("\n").length;
    const pre = jsonPre(src, { highlight, shorten });
    const wrap = el("div", { class: "msg-json" }, pre);
    const tools = el("div", { class: "json-tools" }, copyButton(src, "Copy JSON"));
    wrap.append(tools);
    if (lines > clamp) {
      pre.classList.add("clamped");
      const more = el("button", { type: "button", class: "mini json-more", text: `Show all ${lines} lines` });
      more.addEventListener("click", () => {
        const c = pre.classList.toggle("clamped");
        more.textContent = c ? `Show all ${lines} lines` : "Show fewer lines";
      });
      wrap.append(more);
    }
    return wrap;
  }

  // ------------------------------------------------------------------------------ blocks
  const RENDER = {
    p: (b) => md(b.md, el("p", { class: "prose" })),
    h: (b) => md(b.text, el("h2")),
    section: (b) => md(b.text, el("h2", { class: "section-h" })),
    math: (b) => tex(el("div", { class: "math-block" }), b.tex, true),
    outcome: renderOutcome,
    map: renderMap,
    checks: renderChecks,
    derive: renderDerive,
    values: renderValues,
    callout: (b) => md(b.md, el("div", { class: `callout ${b.tone || ""}`, role: b.tone === "warn" ? "note" : null })),
    list: (b) => {
      const l = el(b.ordered ? "ol" : "ul", { class: "list" });
      for (const it of b.items) l.append(md(it, el("li")));
      return l;
    },
    table: renderTable,
    kv: renderKv,
    json: renderJson,
    decision: renderDecision,
    bytemap: renderBytemap,
    privacy: renderPrivacy,
  };
  function renderBlock(b) { const f = RENDER[b.t]; return f ? f(b) : null; }

  function blockTitle(text, aside) {
    const t = md(text, el("h3", { class: "block-title" }));
    if (aside) t.append(el("span", { class: "aside", text: aside }));
    return t;
  }

  /** The blocks of a stage into `parent`. Everything after the flow waits for it ("later").
      Returns the flow's actions, for the player. */
  function renderBlocks(blocks, parent, calls, inline) {
    let items = [];
    let after = false;
    for (const b of blocks) {
      let node;
      if (b.t === "flow" && !items.length) {
        const f = renderFlow(b, calls || []);
        node = f.node;
        items = f.items;
      } else {
        node = renderBlock(b);
      }
      if (!node) continue;
      if (after) node.classList.add("later");
      parent.append(node);
      if (b.t === "flow") after = true;
      if (b.t === "outcome" && inline) {
        inline.classList.add("later");
        parent.append(inline);
        inline = null;
      }
    }
    if (inline) { if (after) inline.classList.add("later"); parent.append(inline); }
    return items;
  }

  // --- the flow: numbered actions ---------------------------------------------------
  /** Which recorded calls each action made: its `uses`, matched in order against the trace, each
      with the calls nested inside it. */
  function matchCalls(actions, calls) {
    const parent = calls.map((c, k) => {
      for (let j = k - 1; j >= 0; j -= 1) if (calls[j].depth < c.depth) return j;
      return null;
    });
    const used = new Array(calls.length).fill(false);
    return actions.map((a) => {
      const got = [];
      for (const name of a.uses || []) {
        const k = calls.findIndex((c, j) => !used[j] && c.call === name);
        if (k < 0) continue;
        used[k] = true;
        got.push(k);
        for (let j = k + 1; j < calls.length && calls[j].depth > calls[k].depth; j += 1) { used[j] = true; got.push(j); }
      }
      got.sort((x, y) => x - y);
      const set = new Set(got);
      return got.map((k) => ({ ...calls[k], k, top: parent[k] == null || !set.has(parent[k]) }));
    });
  }
  function actionTime(spans) { return spans.filter((s) => s.top).reduce((t, s) => t + s.us, 0); }

  function renderFlow(b, calls) {
    const node = el("section", { class: `flow${S.showVals ? "" : " no-vals"}` });
    const tools = el("div", { class: "flow-tools" },
      el("button", { type: "button", class: "mini", title: "Play this step again (R)", text: "Replay", onclick: replay }),
      b.actions.some((a) => (a.rows || []).some((r) => r.vals && r.vals.length)) &&
        el("button", { type: "button", class: "mini vals-toggle", title: "Show or hide the values under the formulas (V)", text: S.showVals ? "Hide values" : "Show values", onclick: toggleVals }));
    node.append(el("div", { class: "flow-head" },
      el("div", null, el("h2", { text: "What happens" }), " ", md(b.caption, el("span", { class: "caption" }))), tools));
    const list = el("ol", { class: "actions" });
    const real = b.actions.filter((a) => !a.sep);
    const spans = matchCalls(real, calls);
    const items = [];
    for (const a of b.actions) {
      // a heading between actions: when, and between whom, the next ones happen
      if (a.sep) { list.append(md(a.sep, el("li", { class: "sep" }))); continue; }
      const k = items.length;
      const it = renderAction(a, k, spans[k]);
      list.append(it.el);
      items.push(it);
    }
    node.append(list);
    return { node, items };
  }

  function renderAction(a, i, spans) {
    const li = el("li", { class: "action pending" });
    const main = el("div", { class: "a-main" });
    const who = el("div", { class: "a-who" }, actorChip(a.actor));
    if (a.to) who.append(arrow(), actorChip(a.to));
    const meta = el("div", { class: "a-meta" });
    if (a.msg && a.msg.bytes) meta.append(el("span", { title: "binary payload", text: `${a.msg.bytes} B` }));
    const t = actionTime(spans);
    const timeEl = spans.length ? el("span", { class: "t", title: "measured in this run", text: "" }) : null;
    if (timeEl) meta.append(timeEl);
    const head = el("div", { class: "a-head" }, who, meta);
    if (a.title) head.append(md(capFirst(a.title), el("div", { class: "a-title" })));
    main.append(head);

    // what runs: shown while the action computes, folded away afterwards
    const run = el("div", { class: "a-run" });
    const base = spans.length ? Math.min(...spans.map((s) => s.depth)) : 0;
    for (const s of spans) {
      const line = el("div", { class: `run-line pending depth-${Math.min(2, s.depth - base)}`, "data-t": fmtTime(s.us) });
      if (s.error) line.dataset.err = "1";
      const fn = el("span", { class: "fn" });
      if (s.actor !== a.actor) fn.append(el("span", { class: "by", text: `${actorOf(s.actor).name} ` }));
      fn.append(el("code", { text: s.call }));
      const runs = subsup(s.runs, el("span", { class: "runs" }));
      if (s.note) runs.append(el("span", { class: "note", text: `→ ${s.note}` }));
      if (s.error) runs.append(el("span", { class: "err", text: `→ ${s.error}` }));
      line.append(el("span", { class: "st" }), fn, runs, el("span", { class: "t", text: "" }));
      run.append(line);
    }
    if (!spans.length) run.append(el("div", { class: "run-wait" }, el("span", { class: "spin" }), el("span", { text: waitText(a) })));
    main.append(run);
    const ran = spans.length
      ? el("details", { class: "ran", hidden: true }, el("summary", null, icon(["M9 6l6 6-6 6"], "chev"),
        spans.filter((s) => s.top).length === 1 ? el("span", null, "ran ", el("code", { text: spans.find((s) => s.top).call })) :
          el("span", { text: `ran ${spans.filter((s) => s.top).length} engine calls` }),
        el("span", { text: ` in ${fmtTime(t)}` })))
      : null;
    if (ran) main.append(ran);

    const body = el("div", { class: "a-body" });
    for (const r of a.rows || []) body.append(renderRow(r));
    if (a.detail && a.detail.length) {
      const d = el("div", { class: "a-detail" });
      for (const blk of a.detail) { const n = renderBlock(blk); if (n) d.append(n); }
      body.append(d);
    }
    if (a.msg) body.append(renderMessage(a));
    if (a.go) {
      const s = S.run.stages[S.stageIndex[a.go]];
      if (s) body.append(el("a", { class: "go-link", href: `#/stage/${a.go}` }, `Open step ${S.stageIndex[a.go]}: `, md(s.title, el("span"))));
    }
    main.append(body);
    li.append(el("div", { class: "a-node", "aria-hidden": "true", text: String(i + 1) }), main);
    const failed = (a.rows || []).some((r) => r.t === "check" && !r.ok) || spans.some((s) => s.error);
    return { el: li, data: a, spans, run, ran, timeEl, time: t, failed, index: i };
  }

  function waitText(a) {
    const name = actorOf(a.actor).name;
    const rows = a.rows || [];
    if (a.msg && !rows.length) return `${name} sends ${plain(a.msg.name || "a message")}${a.to ? ` to ${actorOf(a.to).name}` : ""}…`;
    if (rows.length && rows.every((r) => r.t === "say")) return `${name}: ${plain(a.title || rows[0].md)}`;
    if (rows.length && rows.every((r) => r.t === "check")) return `${name} checks…`;
    return `${name} computes…`;
  }

  function renderRow(r) {
    const row = el("div", { class: `r ${r.t}${r.t === "check" && !r.ok ? " failed" : ""}` });
    const formula = () => (r.text ? md(r.text, el("div", { class: "formula text" })) : tex(el("div", { class: "formula" }), r.tex));
    if (r.t === "act") {
      row.append(el("span", { class: "glyph", "aria-hidden": "true", text: "·" }), formula());
      const v = chips(r.vals);
      if (v) row.append(v);
    } else if (r.t === "say") {
      row.append(el("span", { class: "glyph", "aria-hidden": "true", text: "“" }), md(r.md, el("div", { class: "says" })));
    } else if (r.t === "check") {
      row.append(mark(r.ok), formula());
      if (r.md) row.append(md(r.md, el("span", { class: "verdict-md" })));
    }
    if (r.aside) row.append(md(r.aside, el("span", { class: "aside" })));
    return row;
  }

  const KIND_BADGE = {
    wire: ["wire format", "The format the VTC receives: the hidden-vetting member of vtc/join-requests/submit/0.3 (vti-vetting-pcs::wire)."],
    verdict: ["verdict", "The VTC's answer in the shape of the join ceremony's Verdict (vta-sdk): an effect, and what it carries."],
    memory: ["in memory, as JSON", "The prototype has no transport: this message is an in-memory object, written out here by the crate's serde layer (multibase base58btc for group elements, scalars and proofs)."],
  };
  function renderMessage(a) {
    const m = a.msg;
    if (!m.json && !m.name) {
      const line = el("div", { class: "msg-line" }, el("span", { class: "msg-label", text: "sends" }), tex(el("span", { class: "msg-tex" }), m.tex));
      const v = chips(m.vals);
      if (v) line.append(v);
      if (m.aside) line.append(md(m.aside, el("span", { class: "aside" })));
      return line;
    }
    const allow = m.kind === "verdict" && /"effect":\s*"allow"/.test(m.json || "");
    const box = el("div", { class: `msg${m.kind === "verdict" ? " verdict-msg" : ""}${allow ? " allow" : ""}` });
    const tags = el("span", { class: "msg-tags" });
    if (m.kind && KIND_BADGE[m.kind]) tags.append(el("span", { class: `badge kind-${m.kind}`, title: KIND_BADGE[m.kind][1], text: KIND_BADGE[m.kind][0] }));
    if (m.bytes) tags.append(el("span", { class: "badge size", title: "binary payload: the canonical encodings of the values it carries", text: `${m.bytes} B` }));
    box.append(el("div", { class: "msg-head" }, md(capFirst(m.name || "message"), el("span", { class: "msg-name" })), tags));
    box.append(tex(el("div", { class: "msg-tex" }), m.tex));
    if (!m.json) { const v = chips(m.vals); if (v) box.append(v); }
    if (m.aside) box.append(md(m.aside, el("span", { class: "aside" })));
    if (m.json) box.append(jsonBox(m.json, m.highlight));
    else box.classList.add("bare");
    return box;
  }

  // --- the intro's map of messages: static, nothing is played ------------------------
  function renderMap(b) {
    const box = el("section", { class: "map" });
    box.append(el("div", { class: "map-head" }, el("h2", { text: "The protocol at a glance" }), md(b.caption, el("p"))));
    for (const a of b.actions) {
      if (a.sep) { box.append(md(a.sep, el("div", { class: "map-group" }))); continue; }
      const who = el("div", { class: "who" }, actorChip(a.actor));
      if (a.to) who.append(arrow(), actorChip(a.to));
      const what = el("div", { class: "what" });
      if (a.title) what.append(md(capFirst(a.title), el("div", { class: "t" })));
      if (a.msg) what.append(tex(el("div", { class: "m" }), a.msg.tex));
      if (a.msg && a.msg.aside) what.append(md(a.msg.aside, el("span", { class: "aside" })));
      const size = el("div", { class: "sz", text: a.msg && a.msg.bytes ? `${a.msg.bytes} B` : "" });
      const st = a.go != null && S.stageIndex[a.go] != null ? S.run.stages[S.stageIndex[a.go]] : null;
      const go = el("div", { class: "go" });
      if (st) go.append(el("a", { href: `#/stage/${a.go}`, title: plain(st.title), text: `step ${S.stageIndex[a.go]}` }));
      box.append(el("div", { class: "map-row" }, who, what, size, go));
    }
    return box;
  }

  // --- the outcome -----------------------------------------------------------------
  function renderOutcome(b) {
    const glyph = b.tone === "ok" ? mark(true)
      : b.tone === "more" || b.tone === "warn" ? el("span", { class: "mark-more", "aria-hidden": "true", text: "!" })
        : el("span", { class: "mark-info", "aria-hidden": "true", text: "i" });
    return el("section", { class: `outcome ${b.tone || "info"}`, role: "status" }, glyph, md(b.title, el("h3")), md(b.md, el("p")));
  }

  // --- checks, derivations, values -------------------------------------------------
  function renderChecks(b) {
    const box = el("section", { class: "checks" });
    if (b.title) box.append(blockTitle(b.title));
    const list = el("ul", { class: "check-list" });
    for (const c of b.items) {
      const item = el("li", { class: "check-item" }, mark(c.ok));
      const body = el("div");
      body.append(md(c.md, el("div", { class: "check-claim" })));
      if (c.tex) body.append(tex(el("div", { class: "check-tex" }), c.tex, false));
      item.append(body);
      if (c.observed) {
        const err = c.observed.startsWith("Err");
        item.append(el("div", { class: `observed ${err ? "err" : "ok"}`, text: c.observed }));
      }
      if (c.sides) {
        const [l, r] = c.sides;
        const lv = S.values[l], rv = S.values[r];
        if (lv && rv) {
          const same = lv.hex === rv.hex;
          item.append(el("div", { class: "sides" },
            el("span", { class: "insp-title", text: "left" }), chip(l),
            el("span", { class: "insp-title", text: "right" }), chip(r),
            md(same ? `the two ${lv.bytes}-byte $\\G_T$ elements are equal, byte for byte` : "the two $\\G_T$ elements differ",
              el("span", { class: `eq ${same ? "same" : "diff"}` }))));
        }
      }
      if (c.by) item.append(el("div", { class: "check-meta" }, el("span", { class: "by", text: c.by })));
      list.append(item);
    }
    box.append(list);
    return box;
  }

  function renderDerive(b) {
    const box = el("section", { class: "derive" }, blockTitle(b.title));
    if (b.md) box.append(md(b.md, el("p", { class: "derive-intro" })));
    const lines = el("div", { class: "derive-lines" });
    for (const l of b.lines) {
      const line = el("div", { class: "derive-line" });
      if (l.tex) {
        line.append("ok" in l ? mark(l.ok) : el("span"), tex(el("div", { class: "d-tex" }), l.tex));
        const v = chips(l.vals);
        if (v) line.append(v);
        if (l.md) line.append(md(l.md, el("div", { class: "d-md" })));
      } else {
        line.classList.add("note");
        line.append(el("span"), md(l.md, el("div", { class: "d-md" })));
      }
      lines.append(line);
    }
    box.append(lines);
    return box;
  }

  function renderValues(b) {
    const box = el("section", { class: "table-block" }, blockTitle(b.title));
    const list = el("div", { class: "values-list" });
    for (const vid of b.ids) {
      const v = S.values[vid];
      if (!v) continue;
      list.append(texSpan(v.tex, "vl-sym"));
      const val = el("div", { class: "vl-val" }, chip(vid, { size: true }));
      if (v.note) val.append(md(v.note, el("span", { class: "vl-note" })));
      list.append(val);
    }
    box.append(list);
    return box;
  }

  function renderTable(b) {
    const box = el("section", { class: "table-block" });
    if (b.title) box.append(blockTitle(b.title));
    const t = el("table", { class: "tbl" });
    if (b.head && b.head.some((h) => h)) {
      const tr = el("tr");
      for (const h of b.head) tr.append(md(h, el("th")));
      t.append(el("thead", null, tr));
    }
    const tb = el("tbody");
    for (const row of b.rows) {
      const tr = el("tr");
      for (const c of row) tr.append(md(c, el("td", { class: c.length <= 14 || /^(\[\d+\]\([^)]*\),?\s*)+$/.test(c) ? "nw" : null })));
      tb.append(tr);
    }
    t.append(tb);
    box.append(el("div", { class: "table-scroll" }, t));
    return box;
  }

  function renderKv(b) {
    const box = el("section", { class: "kv-block" }, blockTitle(b.title));
    const dl = el("dl", { class: "kv" });
    for (const it of b.items) dl.append(el("dt", { text: it.k }), el("dd", { text: it.v, class: /^[\w:/.,-]+$/.test(it.v) && /[\d/:]/.test(it.v) ? "mono" : null }));
    box.append(dl);
    return box;
  }

  // --- JSON as a block (the whole submission at step 11) ------------------------------
  function renderJson(b) {
    const box = el("section", { class: "wire" });
    const head = el("div", { class: "decision-head" }, blockTitle(b.title));
    if (b.kind && KIND_BADGE[b.kind]) head.append(el("span", { class: `badge kind-${b.kind}`, title: KIND_BADGE[b.kind][1], text: KIND_BADGE[b.kind][0] }));
    box.append(head, jsonBox(b.json, b.highlight, { shorten: false, clamp: 80 }));
    return box;
  }

  // --- VTI's decision ------------------------------------------------------------------
  function renderDecision(b) {
    const box = el("section", { class: "decision" });
    const head = el("div", { class: "decision-head" }, blockTitle(b.title));
    const v = el("div", { class: `verdict ${b.admit ? "admit" : "more"}` });
    if (b.admit) v.append(el("strong", { text: "satisfied" }), el("span", { text: `${b.distinct} distinct vetter${b.distinct === 1 ? "" : "s"} counted; nothing is missing.` }));
    else {
      v.append(el("strong", { text: "not yet" }), el("span", { text: `${b.distinct} distinct vetter${b.distinct === 1 ? "" : "s"} counted; still missing ` }));
      b.needs.forEach((nd, i) => { if (i) v.lastChild.append(", "); v.lastChild.append(el("code", { text: nd })); });
    }
    const t = el("table", { class: "facts" });
    t.append(el("thead", null, el("tr", null, el("th", { text: "vetter (its tag)" }), el("th", { text: "method" }), el("th", { text: "counted" }), el("th", { text: "failures" }))));
    const tb = el("tbody");
    for (const s of b.statements) {
      const who = s.vid ? chip(s.vid, { size: false }) : el("code", { text: s.issuer.slice(0, 18) + "…" });
      const f = el("td");
      if (s.failures.length) for (const code of s.failures) f.append(el("span", { class: "pill", text: code }));
      else f.append(el("span", { class: "insp-title", text: "none" }));
      tb.append(el("tr", null, el("td", null, who), el("td", { text: s.method }),
        el("td", { class: s.counted ? "counted-yes" : "counted-no", text: s.counted ? "yes" : "no" }), f));
    }
    t.append(tb);
    const tableView = el("div", { class: "table-scroll" }, t);
    const views = el("div", null, tableView);
    if (b.json) {
      const jsonView = jsonBox(b.json, ["counted", "failures", "issuer"]);
      jsonView.hidden = true;
      views.append(jsonView);
      const tog = el("button", { type: "button", class: "mini", text: "Show as JSON" });
      tog.addEventListener("click", () => {
        const showJson = jsonView.hidden;
        jsonView.hidden = !showJson;
        tableView.hidden = showJson;
        tog.textContent = showJson ? "Show as a table" : "Show as JSON";
      });
      head.append(tog);
    }
    box.append(head, v, views);
    return box;
  }

  // --- the byte map ----------------------------------------------------------------------
  function renderBytemap(b) {
    const box = el("section", { class: "bytemap" }, blockTitle(b.title, `${b.total} B`));
    const groups = el("div", { class: "bm-groups", "aria-hidden": "true" });
    const bar = el("div", { class: "bm-bar", role: "img", "aria-label": `${b.total} bytes, in ${b.segments.length} parts` });
    const info = el("div", { class: "bm-info", text: "Point at a part to see where it sits." });
    let i = 0;
    while (i < b.segments.length) {
      const g = b.segments[i].group;
      let bytes = 0, j = i;
      while (j < b.segments.length && b.segments[j].group === g) { bytes += b.segments[j].bytes; j += 1; }
      const span = el("span", { class: g ? "" : "none" });
      span.style.flexGrow = String(bytes);
      span.style.flexBasis = "0";
      if (g) span.append("att", el("sub", { text: g.split("_")[1] || "" }));
      groups.append(span);
      i = j;
    }
    b.segments.forEach((s, k) => {
      const alt = s.group && s.group.endsWith("2");
      const seg = el("div", { class: `bm-seg ${s.kind}${alt ? " alt" : ""}`, "data-vid": s.vid || null });
      seg.style.flexGrow = String(s.bytes);
      seg.style.flexBasis = "0";
      seg.append(texSpan(s.label));
      const show = () => {
        info.replaceChildren(el("b", null, texSpan(s.label)), ` ${s.bytes} bytes at offset ${s.offset}. `);
        md(s.md, info);
        if (s.vid) light(s.vid, true);
        seg.classList.add("lit");
      };
      const hide = () => { if (s.vid) light(s.vid, false); seg.classList.remove("lit"); };
      seg.addEventListener("mouseenter", show);
      seg.addEventListener("mouseleave", hide);
      if (s.vid) seg.addEventListener("click", () => select(s.vid));
      seg.dataset.k = String(k);
      bar.append(seg);
    });
    const axis = el("div", { class: "bm-axis" }, el("span", { text: "0" }), el("span", { text: `${b.total} B` }));
    box.append(groups, bar, axis, info);
    requestAnimationFrame(() => {
      for (const seg of bar.children) {
        const lab = seg.firstChild;
        if (lab && lab.scrollWidth > seg.clientWidth - 4) lab.style.visibility = "hidden";
      }
    });
    return box;
  }

  // --- the privacy view ------------------------------------------------------------------
  function renderPrivacy(b) {
    const box = el("section", { class: "privacy" });
    const left = el("div", { class: "priv-col" }, el("h4", { text: "What the VTC holds" }));
    const ids = el("div", { class: "priv-ids" });
    for (const v of b.vetters) ids.append(el("span", { text: v.name }), chip(v.vid, { size: false }));
    left.append(ids, el("p", { text: "Bound to member records at enrolment." }));
    const tagsBox = el("div", { class: "priv-ids" });
    const tagName = (t, j) => (t.vid && S.values[t.vid] ? texSpan(S.values[t.vid].tex) : el("span", { text: `tag ${j + 1}` }));
    b.tags.forEach((t) => tagsBox.append(el("span", { text: t.method }), t.vid ? chip(t.vid, { size: false }) : el("code", { text: t.issuer.slice(0, 16) })));
    left.append(el("h4", { text: "…and the tags in the facts it counted for bob" }), tagsBox);
    const right = el("div", { class: "priv-col" }, el("h4", { text: "Which vetter made which tag?" }));
    const m = el("table", { class: "matrix" });
    const hr = el("tr", null, el("th"));
    for (const v of b.vetters) hr.append(el("th", { text: v.name }));
    m.append(hr);
    const cells = [];
    b.tags.forEach((t, j) => {
      const tr = el("tr", null, el("th", { class: "rowh" }, tagName(t, j)));
      b.vetters.forEach((v, k) => {
        const td = el("td", { text: "?", "aria-label": `tag ${j + 1}, ${v.name}: unknown` });
        cells.push([td, b.truth[j][k], `tag ${j + 1}, ${v.name}`]);
        tr.append(td);
      });
      m.append(tr);
    });
    let shown = false;
    const btn = el("button", { type: "button", class: "btn ghost", text: "Fill it in with the vetters' secret keys" });
    btn.addEventListener("click", () => {
      shown = !shown;
      for (const [td, yes, name] of cells) {
        td.className = shown ? (yes ? "yes" : "no") : "";
        td.textContent = shown ? (yes ? "made it" : "·") : "?";
        td.setAttribute("aria-label", `${name}: ${shown ? (yes ? "made it" : "did not") : "unknown"}`);
      }
      btn.textContent = shown ? "Hide the ground truth" : "Fill it in with the vetters' secret keys";
    });
    right.append(m, el("div", { class: "priv-actions" }, btn),
      md("Each cell asks whether $T = H_2(s_B)^{\\usk_v}$: a DDH instance. The walkthrough answers it with each vetter's key; the VTC holds only the identifiers on the left.", el("p")));
    box.append(el("div", { class: "priv-grid" }, left, right));
    return box;
  }

  // --- calls -----------------------------------------------------------------------------
  /** The engines describe their calls in plain text ("T_0 = H_2(s)^usk"): set x_1, x^y, x_{ab}
      as sub- and superscripts. A base longer than three characters is code (issue_root), left alone. */
  function subsup(text, target) {
    const re = /([_^])(\{[^}]*\}|[\p{L}\p{M}\p{N}*']+)/gu;
    let last = 0, m;
    while ((m = re.exec(text))) {
      const before = text.slice(0, m.index);
      const base = /[\p{L}\p{M}\p{N}']*$/u.exec(before)[0];
      const afterParen = /[)}]$/.test(before);
      if (!afterParen && (base.length === 0 || [...base].length > 3)) continue;
      target.append(text.slice(last, m.index));
      const body = m[2].startsWith("{") ? m[2].slice(1, -1) : m[2];
      target.append(subsup(body, el(m[1] === "_" ? "sub" : "sup")));
      last = re.lastIndex;
    }
    target.append(text.slice(last));
    return target;
  }
  function fmtTime(us) {
    if (us < 1) return "<1 µs";
    if (us < 1000) return `${us.toFixed(0)} µs`;
    return `${(us / 1000).toFixed(2)} ms`;
  }
  function renderCalls(calls, profile) {
    if (!calls || !calls.length) return null;
    const total = calls.filter((c) => c.depth === 0).reduce((a, c) => a + c.us, 0);
    const max = Math.max(...calls.map((c) => c.us), 1);
    const det = el("details", { class: "calls" });
    det.append(el("summary", null, icon(["M9 6l6 6-6 6"], "chev"), "Every engine call of this step",
      el("span", { class: "aside", text: `${calls.length} call${calls.length === 1 ? "" : "s"}, ${fmtTime(total)} in all, timed in this run (${profile} build)` })));
    const list = el("ol", { class: "call-list" });
    for (const c of calls) {
      const fn = el("span", { class: "fn", text: c.call });
      fn.style.paddingLeft = `${c.depth * 16}px`;
      if (c.depth) fn.style.borderLeft = "1px solid var(--rule)";
      const runs = subsup(c.runs, el("span", { class: "runs" }));
      if (c.note) runs.append(el("span", { class: "note", text: `→ ${c.note}` }));
      if (c.error) runs.append(el("span", { class: "err", text: `→ ${c.error}` }));
      const bar = el("i");
      bar.style.width = `${Math.max(2, (c.us / max) * 44)}px`;
      list.append(el("li", { class: `call${c.error ? " failed" : ""}` },
        el("span", { class: "who", text: actorOf(c.actor).name }), fn, runs, el("span", { class: "t" }, bar, fmtTime(c.us))));
    }
    det.append(list, el("div", { class: "call-total" }, el("span", { text: "top-level calls, wall clock" }), el("span", { text: fmtTime(total) })));
    return det;
  }

  // ------------------------------------------------------------------------------ where things stand
  function involvedIn(st) {
    const set = new Set((st && st.parties) || []);
    if (set.has("vetters")) for (const v of ["alice", "carol", "dave"]) set.add(v);
    return set;
  }
  const APP_STATUS = {
    collecting: ["collecting statements", "collecting"],
    requestMore: ["requestMore", "requestMore"],
    allow: ["admitted", "allow"],
    recount: ["recount: requestMore", "recount"],
  };
  function renderState(state, title, sub, involved, highlight) {
    const box = el("section", { class: "state" }, el("h2", { text: title }));
    if (sub) box.append(el("div", { class: "sub", text: sub }));
    if (!state || (!state.parties.length && !state.apps.length)) {
      box.append(el("p", { class: "state-empty", text: "Nothing yet: no key has been generated, and nobody holds anything." }));
      return box;
    }
    if (state.apps.length) box.append(renderApps(state.apps, highlight));
    const list = el("ul", { class: "parties" });
    for (const p of state.parties) {
      const idle = involved && involved.size && !involved.has(p.who) && !(highlight && p.items.some((it) => it.new));
      const ul = el("ul");
      for (const it of p.items) ul.append(md(it.md, el("li", { class: `${it.secret ? "secret" : ""}${highlight && it.new ? " new" : ""}`, title: highlight && it.new ? "new in this step" : null })));
      if (idle) {
        const det = el("details", { class: "party idle" }, el("summary", null, actorChip(p.who), el("span", { class: "count", text: `${p.items.length} item${p.items.length === 1 ? "" : "s"}, not in this step` })), ul);
        list.append(el("li", null, det));
      } else {
        list.append(el("li", { class: "party" }, actorChip(p.who), ul));
      }
    }
    box.append(list);
    return box;
  }
  /** Each application against the policy: what it has, and what is still missing. */
  function renderApps(appsList, highlight) {
    const apps = el("div", { class: "apps" }, el("h3", { text: "Applications, against the policy" }));
    for (const a of appsList) {
      const [label, cls] = APP_STATUS[a.status] || [a.status, ""];
      const card = el("div", { class: `app-card${highlight && a.new ? " new" : ""}` },
        el("div", { class: "app-top" }, actorChip(a.subject), el("span", { class: `app-status ${cls}`, text: label })));
      for (const n of a.items) {
        const pips = el("span", { class: "pips", "aria-hidden": "true" });
        for (let k = 0; k < n.need; k += 1) pips.append(el("i", { class: k < n.have ? "have" : null }));
        card.append(el("div", { class: "need" }, el("span", null, n.md, el("span", { class: "count", text: `${Math.min(n.have, n.need)} of ${n.need}` })), pips));
      }
      if (a.needs && a.needs.length) {
        const nd = el("div", { class: "app-needs" }, el("span", { class: "app-note", text: "missing" }));
        for (const s of a.needs) nd.append(el("code", { text: s }));
        card.append(nd);
      }
      card.append(el("div", { class: "app-note", text: `${a.source === "vtc" ? "as the VTC counted it" : "what the applicant holds"}: ${a.md}` }));
      apps.append(card);
    }
    return apps;
  }
  function showRail(state, title, sub, involved, highlight) {
    $("#rail").replaceChildren(renderState(state, title, sub, involved, highlight));
  }

  // ------------------------------------------------------------------------------ the player
  class Player {
    constructor(items, hooks) {
      this.items = items;
      this.hooks = hooks;
      this.i = -1;
      this.skipping = false;
      this.cancelled = false;
      this.done = false;
      this.waiting = null;
      this.pending = new Set();
    }
    get factor() { return PACE[S.pace] ?? 1; }
    sleep(ms) {
      const t = ms * this.factor;
      if (this.skipping || this.cancelled || t <= 0) return Promise.resolve();
      return new Promise((res) => {
        const f = () => { clearTimeout(h); this.pending.delete(f); res(); };
        const h = setTimeout(f, t);
        this.pending.add(f);
      });
    }
    waitKey() {
      if (this.skipping || this.cancelled) return Promise.resolve();
      return new Promise((res) => { this.waiting = () => { this.waiting = null; res(); }; updateBar(); });
    }
    flush() { for (const f of [...this.pending]) f(); if (this.waiting) this.waiting(); }
    next() { if (this.waiting) this.waiting(); }
    skip() { this.skipping = true; this.flush(); }
    cancel() { this.cancelled = true; this.flush(); }
    async play() {
      if (this.hooks.start) this.hooks.start();
      // time to read the step's title and introduction before anything runs
      await this.sleep(S.pace === "manual" ? 0 : 1100);
      for (let i = 0; i < this.items.length; i += 1) {
        if (this.cancelled) return;
        this.i = i;
        if (S.pace === "manual" && !this.skipping) {
          await this.waitKey();
          if (this.cancelled) return;
        }
        await this.runItem(this.items[i]);
      }
      if (this.cancelled) return;
      this.done = true;
      if (this.hooks.finish) this.hooks.finish();
      updateBar();
    }
    async runItem(it) {
      const fast = this.skipping || this.factor === 0;
      setItem(it, "running");
      updateBar();
      if (!fast) follow(it.el);
      const lines = [...it.run.querySelectorAll(".run-line")];
      if (lines.length) {
        const per = Math.max(150, Math.min(460, 1500 / lines.length));
        for (const ln of lines) {
          ln.classList.remove("pending");
          ln.classList.add("on");
          await this.sleep(per);
          finishLine(ln);
        }
        await this.sleep(150);
      } else {
        await this.sleep(560);
      }
      setItem(it, "done");
      updateBar();
      await this.sleep(dwell(it.data));
    }
  }
  function finishLine(ln) {
    ln.classList.remove("pending", "on");
    ln.classList.add(ln.dataset.err ? "bad" : "ok");
    ln.querySelector(".t").textContent = ln.dataset.t;
  }
  function dwell(a) {
    return Math.min(1900, 450 + 150 * ((a.rows || []).length) + (a.msg ? 500 : 0) + (a.detail ? 300 : 0));
  }
  function setItem(it, state) {
    it.state = state;
    it.el.classList.remove("pending", "running", "done");
    it.el.classList.add(state);
    if (state === "done") {
      it.el.classList.toggle("failed", it.failed);
      for (const ln of it.run.querySelectorAll(".run-line")) finishLine(ln);
      if (it.ran) { it.ran.append(it.run); it.ran.hidden = false; }
      else it.run.hidden = true;
      if (it.timeEl) {
        it.timeEl.replaceChildren(el("span", { class: it.spans.some((s) => s.error) ? "bad" : "ok", text: it.spans.some((s) => s.error) ? "✗ " : "✓ " }), fmtTime(it.time));
      }
    }
  }
  /** Like a terminal: when an action starts below the fold, bring its head up to the middle of
      the view, so that the end of the previous one stays visible above it. Never while the reader
      has just scrolled. */
  function follow(node) {
    if (Date.now() - S.userScrollAt < 2500) return;
    const top = $(".stepbar").getBoundingClientRect().bottom + 12;
    const r = node.getBoundingClientRect();
    const vh = window.innerHeight;
    const behavior = reducedMotion() ? "auto" : "smooth";
    if (r.top > vh * 0.72) window.scrollBy({ top: r.top - vh * 0.42, behavior });
    else if (r.top < top) window.scrollBy({ top: r.top - top - 8, behavior });
  }
  function stopPlayer() {
    if (S.player) S.player.cancel();
    S.player = null;
    S.items = [];
  }
  /** Play `items`, or show them done at once (a step already seen, or pace "instant"). */
  function startPlayer(items, hooks) {
    S.items = items;
    if (!items.length || hooks.seen || S.pace === "instant") {
      for (const it of items) setItem(it, "done");
      S.player = null;
      hooks.finish();
      updateBar();
      return;
    }
    const p = new Player(items, hooks);
    S.player = p;
    updateBar();
    p.play();
  }
  function activePlayer() { return S.player && !S.player.done && !S.player.cancelled ? S.player : null; }
  function primary() {
    const p = activePlayer();
    if (p && p.waiting) { p.next(); return; }
    if (p) { p.skip(); return; }
    go(1);
  }

  // ------------------------------------------------------------------------------ the step bar
  function phaseText(st) {
    const same = S.run.stages.filter((s) => s.phase === st.phase);
    return same.length > 1 ? `${st.phase}, ${same.indexOf(st) + 1} of ${same.length}` : st.phase;
  }
  function updateBar() {
    if (!S.run) return;
    const r = S.route;
    const stages = S.run.stages;
    const lab = S.run.lab;
    let pos = [], phase = "", prevT = null, nextT = null;
    if (r.kind === "stage") {
      const i = S.stageIndex[r.id];
      const st = stages[i];
      pos = i === 0 ? ["Overview"] : ["Step ", el("b", { text: String(i) }), ` of ${stages.length - 1}`];
      phase = i === 0 ? "step 0" : phaseText(st);
      prevT = i > 0 ? `${i - 1}. ${plain(stages[i - 1].title)}` : null;
      nextT = i + 1 < stages.length ? `${i + 1}. ${plain(stages[i + 1].title)}` : "The attack lab";
    } else if (r.kind === "labindex") {
      pos = ["The attack lab"];
      phase = `${lab.length} experiments`;
      prevT = `${stages.length - 1}. ${plain(stages[stages.length - 1].title)}`;
      nextT = lab[0].title;
    } else {
      const k = lab.findIndex((l) => l.id === r.id);
      pos = ["Experiment ", el("b", { text: String(k + 1) }), ` of ${lab.length}`];
      phase = lab[k] ? lab[k].kind : "";
      prevT = k > 0 ? lab[k - 1].title : "The attack lab";
      nextT = k + 1 < lab.length ? lab[k + 1].title : null;
    }
    $("#pos").replaceChildren(...pos);
    $("#phase-pos").textContent = phase;
    const prev = $("#prev");
    prev.disabled = !prevT;
    $("#prev-title").textContent = prevT || "";
    const next = $("#next");
    const p = activePlayer();
    const n = S.items.length;
    next.classList.toggle("running", !!p);
    next.classList.toggle("primary", !p);
    if (p && p.waiting) {
      $("#next-small").textContent = `Action ${p.i + 1} of ${n}`;
      $("#next-title").textContent = "Run it";
      next.disabled = false;
    } else if (p) {
      $("#next-small").textContent = p.i < 0 ? `${n} actions to play` : `Playing action ${p.i + 1} of ${n}`;
      $("#next-title").textContent = "Show the rest now";
      next.disabled = false;
    } else {
      $("#next-small").textContent = "Next";
      $("#next-title").textContent = nextT || "";
      next.disabled = !nextT;
    }
    // the actions of this step, and what is running
    const dots = $("#act-dots");
    dots.replaceChildren(...S.items.map((it) => el("li", { class: it.state === "done" ? (it.failed ? "done failed" : "done") : it.state === "running" ? "running" : null })));
    const status = $("#status");
    const running = S.items.find((it) => it.state === "running");
    if (p && p.waiting) {
      const it = S.items[p.i];
      status.replaceChildren(`Next: ${actorOf(it.data.actor).name} ${plain(it.data.title || "acts")}. Press → or Space.`);
    } else if (running) {
      const a = running.data;
      const call = running.run.querySelector(".run-line.on code");
      if (call) status.replaceChildren(`${actorOf(a.actor).name} computes `, el("code", { text: call.textContent }));
      else status.replaceChildren(waitText(a));
    } else if (p && p.i < 0) {
      status.textContent = `${n} action${n === 1 ? "" : "s"} in this step; the first one starts in a moment.`;
    } else if (p) {
      const it = S.items[p.i];
      status.textContent = `Action ${p.i + 1} of ${n} done: ${actorOf(it.data.actor).name} ${plain(it.data.title || "acted")}.`;
    } else if (r.kind === "stage" && !S.items.length) {
      status.textContent = r.id === "intro" ? "An overview: nothing runs in this step." : "Nothing new runs in this step: it examines the run.";
    } else if (S.items.length) {
      const calls = S.items.reduce((c, it) => c + it.spans.filter((s) => s.top).length, 0);
      const t = S.items.reduce((c, it) => c + it.time, 0);
      status.textContent = calls
        ? `Done: ${n} action${n === 1 ? "" : "s"}, ${calls} engine call${calls === 1 ? "" : "s"}, ${fmtTime(t)} measured.`
        : `Done: ${n} action${n === 1 ? "" : "s"}.`;
    } else {
      status.textContent = "";
    }
  }
  // the status names the call that is running right now
  setInterval(() => { if (activePlayer()) updateBar(); }, 200);

  // ------------------------------------------------------------------------------ pages
  function renderStagePage(id) {
    stopPlayer();
    const stages = S.run.stages;
    const i = S.stageIndex[id] ?? 0;
    const st = stages[i];
    S.values = S.run.values;
    const art = el("article", { class: "step", "aria-labelledby": "step-title" });
    const head = el("header", { class: "step-head" });
    const h1 = el("h1", { id: "step-title" }, el("span", { class: "n", text: String(i) }));
    md(st.title, h1);
    head.append(h1, el("p", { class: "who", text: st.who }), md(st.lede, el("p", { class: "lede" })));
    art.append(head);
    const involved = involvedIn(st);
    const inline = el("div", { class: "state-inline" });
    const items = renderBlocks(st.blocks, art, st.calls, inline);
    const calls = renderCalls(st.calls, S.run.meta.profile);
    if (calls) { if (items.length) calls.classList.add("later"); art.append(calls); }
    if (st.lab && st.lab.length) {
      const t = el("div", { class: "trylab" }, el("span", { text: "Try it in the lab:" }));
      for (const lid of st.lab) {
        const info = S.run.lab.find((x) => x.id === lid);
        if (info) t.append(el("a", { href: `#/lab/${lid}`, text: info.title }));
      }
      if (items.length) t.classList.add("later");
      art.append(t);
    }
    art.append(pager(i));
    show(art);
    document.title = `${i}. ${plain(st.title)} · Hidden vetting`;
    const before = i > 0 ? stages[i - 1].state : null;
    const after = () => {
      for (const n of art.querySelectorAll(".later")) n.classList.add("shown");
      const when = i === 0 ? "nothing has run yet" : `after step ${i}`;
      showRail(st.state, "Where things stand", when, involved, true);
      inline.replaceChildren(renderState(st.state, "Where things stand", when, involved, true));
      S.seen.add(st.id);
      markNav();
    };
    markNav();
    showRail(before, "Where things stand", i > 0 ? `before step ${i}, while it runs` : "nothing has run yet", involved, false);
    startPlayer(items, { seen: S.seen.has(st.id), finish: after });
  }

  function pager(i) {
    const stages = S.run.stages;
    const nav = el("nav", { class: "pager", "aria-label": "Previous and next step" });
    if (i > 0) {
      const p = stages[i - 1];
      nav.append(el("a", { href: `#/stage/${p.id}`, class: "prev" }, el("span", { text: i - 1 === 0 ? "Previous: the overview" : `Previous: step ${i - 1}` }), md(p.title, el("b"))));
    }
    if (i + 1 < stages.length) {
      const n = stages[i + 1];
      nav.append(el("a", { href: `#/stage/${n.id}`, class: "next" }, el("span", { text: `Next: step ${i + 1}` }), md(n.title, el("b"))));
    } else {
      nav.append(el("a", { href: "#/lab", class: "next" }, el("span", { text: "Next" }), el("b", { text: "The attack lab" })));
    }
    return nav;
  }

  function labStartState() {
    const k = S.stageIndex["prove-k2"];
    return k == null ? null : S.run.stages[k].state;
  }

  function renderLabIndex() {
    stopPlayer();
    S.values = S.run.values;
    const art = el("article", { class: "step" });
    art.append(el("header", { class: "step-head" }, el("h1", { text: "The attack lab" }),
      el("p", { class: "who", text: "experiments run live, from the state of step 9 of this run" })));
    art.append(md("Each experiment replays the run up to bob's admission with the same seed, so its values are the walkthrough's, then tries something. What the code returns is shown verbatim. *Attacks* must be refused; *defences* show a mechanism at work; a *limit* is accepted, because the cryptography does not prevent it.", el("p", { class: "lede" })));
    const list = el("div", { class: "lab-index" });
    for (const x of S.run.lab) {
      list.append(el("a", { class: "lab-card", href: `#/lab/${x.id}` }, el("b", { text: x.title }), el("span", { class: `kind-tag ${x.kind}`, text: x.kind }), md(x.threat, el("p"))));
    }
    art.append(list);
    show(art);
    markNav();
    showRail(labStartState(), "Where the lab starts", "after step 9: bob admitted", null, false);
    updateBar();
    document.title = "The attack lab · Hidden vetting";
  }

  function renderLabPage(id) {
    stopPlayer();
    const x = S.run.lab.find((l) => l.id === id);
    if (!x) { location.hash = "#/lab"; return; }
    S.values = S.run.values;
    const art = el("article", { class: "step lab-head" });
    const verb = x.kind === "attack" ? "Run the attack" : "Run it";
    art.append(el("header", { class: "step-head" }, el("h1", { text: x.title }),
      el("p", { class: "who" }, el("span", { class: `kind-tag ${x.kind}`, text: x.kind }), " ", `from step ${S.stageIndex[x.stage] ?? 0} of seed ${S.run.meta.seed}`)));
    art.append(md(x.threat, el("p", { class: "threat" })));
    const controls = el("div", { class: "lab-controls" });
    let select = null;
    if (x.params) {
      select = el("select", { class: "select", "aria-label": "What to edit" });
      for (const p of x.params) select.append(el("option", { value: p.value, text: p.label }));
      if (S.labParam[id]) select.value = S.labParam[id];
      controls.append(select);
    }
    const run = el("button", { type: "button", class: "btn", text: verb });
    const again = el("button", { type: "button", class: "btn ghost", text: "Run again with fresh randomness" });
    controls.append(run, again);
    art.append(controls);
    const out = el("div", { class: "lab-result", "aria-live": "polite" });
    art.append(out);
    const go = async (fresh) => {
      stopPlayer();
      if (fresh) S.labNonce[id] = (S.labNonce[id] || 0) + 1;
      const param = select ? select.value : null;
      S.labParam[id] = param;
      run.disabled = again.disabled = true;
      out.replaceChildren(el("div", { class: "banner running", role: "status" }, el("span", { class: "spin" }), el("span", { text: "Running the experiment on the server…" })));
      try {
        const [res] = await Promise.all([
          fetch(`/api/lab/${encodeURIComponent(id)}`, {
            method: "POST",
            headers: { "Content-Type": "application/json", "X-PCS-Demo": "1" },
            body: JSON.stringify({ seed: S.run.meta.seed, nonce: S.labNonce[id] || 0, param }),
          }),
          sleepPlain(350 * (PACE[S.pace] ?? 1)),
        ]);
        const data = await res.json();
        if (!res.ok) throw new Error(data.error || res.statusText);
        S.lab[id] = data;
        if (S.route.kind === "lab" && S.route.id === id) renderLabResult(out, data, true);
        markLabRan(id);
      } catch (e) {
        out.replaceChildren(el("div", { class: "error-box", text: `The experiment did not run: ${e.message}` }));
      } finally {
        run.disabled = again.disabled = false;
      }
    };
    run.addEventListener("click", () => go(false));
    again.addEventListener("click", () => go(true));
    if (select) select.addEventListener("change", () => go(false));
    const idx = S.run.lab.findIndex((l) => l.id === id);
    const nav = el("nav", { class: "pager", "aria-label": "Previous and next experiment" });
    const prev = S.run.lab[idx - 1];
    nav.append(prev
      ? el("a", { href: `#/lab/${prev.id}`, class: "prev" }, el("span", { text: "Previous experiment" }), el("b", { text: prev.title }))
      : el("a", { href: "#/lab", class: "prev" }, el("span", { text: "Back to" }), el("b", { text: "The attack lab" })));
    const next = S.run.lab[idx + 1];
    if (next) nav.append(el("a", { href: `#/lab/${next.id}`, class: "next" }, el("span", { text: "Next experiment" }), el("b", { text: next.title })));
    art.append(nav);
    show(art);
    markNav();
    showRail(labStartState(), "Where the lab starts", "after step 9: bob admitted", null, false);
    updateBar();
    document.title = `${x.title} · the attack lab`;
    if (S.lab[id] && S.lab[id].seedRun === S.run.meta.seed) renderLabResult(out, S.lab[id], false);
  }

  function renderLabResult(out, data, animate) {
    data.seedRun = S.run.meta.seed;
    S.values = { ...S.run.values, ...data.values };
    const st = data.stage;
    const banner = el("div", { class: "banner running", role: "status" }, el("span", { class: "spin" }), el("span", { text: "Running the experiment…" }));
    out.replaceChildren(banner, md(st.lede, el("p", { class: "lede" })));
    const items = renderBlocks(st.blocks, out, st.calls, null);
    const calls = renderCalls(st.calls, S.run.meta.profile);
    if (calls) { calls.classList.add("later"); out.append(calls); }
    const finish = () => {
      const tone = data.verdict.tone;
      const lead = tone === "blocked" ? "Refused. " : tone === "limit" ? "Accepted, by design. " : "Accepted. ";
      const rest = data.verdict.text.replace(/^(Rejected|Refused|Accepted|Capped)[^:]*:\s*/, "");
      banner.className = `banner ${tone}`;
      banner.replaceChildren(mark(tone !== "accepted"), md(rest.charAt(0).toUpperCase() + rest.slice(1), el("span", null, el("b", { text: lead }))));
      for (const n of out.querySelectorAll(".later")) n.classList.add("shown");
      if (!items.length) for (const n of out.querySelectorAll(":scope > *")) n.classList.add("shown");
    };
    if (!items.length) {
      for (const n of out.querySelectorAll(".later")) n.classList.remove("later");
      finish();
      updateBar();
      return;
    }
    startPlayer(items, { seen: !animate, finish });
  }

  function show(node) {
    const main = $("#main");
    main.replaceChildren(node);
    window.scrollTo({ top: 0 });
    main.focus({ preventScroll: true });
    renderInspector();
  }

  // ------------------------------------------------------------------------------ navigation chrome
  function buildChrome() {
    // the track: phases, a dot per step
    const ol = el("ol");
    for (const ph of S.run.phases) {
      const stages = S.run.stages.filter((s) => s.phase === ph);
      if (!stages.length) continue;
      const dots = el("span", { class: "dots" });
      for (const s of stages) {
        const i = S.stageIndex[s.id];
        dots.append(el("a", { class: "dot", href: `#/stage/${s.id}`, "data-stage": s.id, title: `${i}. ${plain(s.title)}`, "aria-label": `Step ${i}: ${plain(s.title)}` }));
      }
      ol.append(el("li", { class: "ph", "data-phase": ph }, el("a", { class: "ph-name", href: `#/stage/${stages[0].id}`, text: ph }), dots));
    }
    ol.append(el("li", { class: "ph", "data-phase": "Lab" }, el("a", { class: "ph-name", href: "#/lab", text: "Lab" }),
      el("span", { class: "dots" }, el("a", { class: "dot lab", href: "#/lab", title: "The attack lab", "aria-label": "The attack lab" }))));
    $("#track").replaceChildren(ol);

    // the drawer: every step and every experiment
    const nav = $("#outline");
    nav.replaceChildren();
    let list = null, phase = null;
    S.run.stages.forEach((s, i) => {
      if (s.phase !== phase) {
        phase = s.phase;
        nav.append(el("h3", { text: phase }));
        list = el("ol");
        nav.append(list);
      }
      list.append(el("li", null, el("a", { href: `#/stage/${s.id}`, "data-stage": s.id },
        el("span", { class: "num", text: String(i) }), md(s.title, el("span")))));
    });
    nav.append(el("h3", null, el("a", { href: "#/lab", text: "Attack lab" })));
    const lab = el("ol");
    for (const x of S.run.lab) {
      lab.append(el("li", null, el("a", { href: `#/lab/${x.id}`, "data-lab": x.id, title: x.kind },
        el("span", { class: `tick ${x.kind}`, "aria-label": x.kind }), el("span", { text: x.title }))));
    }
    nav.append(lab);

    const m = S.run.meta;
    const info = $("#run-info");
    info.replaceChildren();
    const first = el("div");
    first.append("seed ", el("b", { text: String(m.seed) }));
    if (m.seed === m.defaultSeed) first.append(", as in the terminal");
    info.append(first);
    if (m.seed !== m.defaultSeed) {
      info.append(el("button", { type: "button", class: "back", text: `use seed ${m.defaultSeed}`, onclick: () => setSeed(m.defaultSeed) }));
    } else {
      info.append(el("div", { text: m.profile === "release" ? `computed in ${Math.round(m.ms)} ms` : "debug build: slow timings" }));
    }
  }

  function markNav() {
    const r = S.route;
    for (const a of document.querySelectorAll("#outline a")) {
      a.removeAttribute("aria-current");
      if (a.dataset.stage) a.classList.toggle("seen", S.seen.has(a.dataset.stage));
    }
    const sel = r.kind === "stage" ? `#outline a[data-stage="${CSS.escape(r.id)}"]` : r.kind === "lab" ? `#outline a[data-lab="${CSS.escape(r.id)}"]` : null;
    const cur = sel ? $(sel) : null;
    if (cur) cur.setAttribute("aria-current", "page");
    const curPhase = r.kind === "stage" ? S.run.stages[S.stageIndex[r.id]].phase : "Lab";
    for (const li of document.querySelectorAll("#track .ph")) {
      const ph = li.dataset.phase;
      li.classList.toggle("current", ph === curPhase);
      const stages = S.run.stages.filter((s) => s.phase === ph);
      li.classList.toggle("done", stages.length > 0 && stages.every((s) => S.seen.has(s.id)));
    }
    for (const d of document.querySelectorAll("#track .dot")) {
      const sid = d.dataset.stage;
      d.classList.toggle("current", r.kind === "stage" ? sid === r.id : !sid);
      d.classList.toggle("done", sid ? S.seen.has(sid) : false);
      if (d.classList.contains("current")) d.setAttribute("aria-current", "step"); else d.removeAttribute("aria-current");
    }
    openOutline(false);
  }
  function markLabRan(id) {
    const t = $(`#outline a[data-lab="${CSS.escape(id)}"] .tick`);
    if (t) t.classList.add("ran");
  }
  function openOutline(on) {
    $("#outline").classList.toggle("open", on);
    $("#scrim").hidden = !on;
    $("#menu").setAttribute("aria-expanded", on ? "true" : "false");
  }

  // ------------------------------------------------------------------------------ inspector
  function select(vid) {
    S.selected = vid;
    for (const c of document.querySelectorAll(".chip.sel")) c.classList.remove("sel");
    for (const c of document.querySelectorAll(`.chip[data-vid="${CSS.escape(vid)}"]`)) c.classList.add("sel");
    renderInspector();
    $("#inspector").classList.add("open");
  }
  function closeInspector() {
    $("#inspector").classList.remove("open");
    S.selected = null;
    for (const c of document.querySelectorAll(".chip.sel")) c.classList.remove("sel");
  }
  function renderInspector() {
    const box = $("#inspector");
    box.replaceChildren();
    const close = el("button", { type: "button", class: "tool icon insp-close", title: "Close (Esc)", onclick: closeInspector },
      icon(["M6.5 6.5l11 11M17.5 6.5l-11 11"]), el("span", { class: "sr-only", text: "Close the inspector" }));
    box.append(close);
    const v = S.selected && S.values[S.selected];
    if (!v) { box.append(...legend()); return; }
    box.append(el("div", { class: "insp-title", text: "Value" }), tex(el("div", { class: "insp-sym" }), v.tex, false));
    const tags = el("div", { class: "insp-tags" }, el("span", { class: `tag k-${v.kind}`, text: kindName(v) }));
    if (!v.hidden && v.bytes != null) tags.append(el("span", { class: "tag", text: v.kind === "text" ? `${v.bytes} B of text` : `${v.bytes} B${v.kind === "proof" ? " compact" : v.kind === "bytes" ? "" : " compressed"}` }));
    if (v.secret) tags.append(el("span", { class: "tag", text: "secret" }));
    box.append(tags);
    if (v.hidden) {
      box.append(el("div", { class: "secret-box", text: `Secret, and not exposed. ${holdersText(v)} keeps it; the walkthrough cannot read it either.` }));
    } else if (v.secret) {
      box.append(el("div", { class: "secret-box", text: `Secret. ${holdersText(v)} alone holds it. It is shown here only because the walkthrough reads it through a demo hook; a real engine never exposes it.` }));
    }
    if (v.note) box.append(el("div", { class: "insp-sec" }, md(v.note, el("p", { class: "insp-note" }))));
    if (v.kind === "text") {
      box.append(section("Value", el("div", { class: "insp-text", text: v.text }), v.text));
    } else if (v.hex) {
      const grid = el("div", { class: "hexgrid" });
      for (let k = 0; k < v.hex.length; k += 8) grid.append(el("span", { text: v.hex.slice(k, k + 8) }));
      box.append(section(v.kind === "proof" ? "Compact encoding, hex" : "Canonical compressed encoding, hex", grid, v.hex));
      if (v.mb) box.append(section(v.kind === "proof" ? "Canonical encoding (with its 8-byte length), multibase, as in messages" : "Multibase (base58btc), as in messages", el("div", { class: "insp-text", text: v.mb }), v.mb));
    }
    if (v.who && v.who.length) {
      const h = el("div", { class: "holders" });
      for (const w of v.who) h.append(el("span", { class: "tag", text: w === "public" ? "everyone" : actorOf(w).name }));
      box.append(el("div", { class: "insp-sec" }, el("h4", { text: "Held by" }), h));
    }
    const uses = appearsIn(S.selected);
    if (uses.length) {
      const ul = el("ul", { class: "where" });
      for (const i of uses) {
        const s = S.run.stages[i];
        ul.append(el("li", null, el("a", { href: `#/stage/${s.id}` }, `${i}. `, md(s.title, el("span")))));
      }
      box.append(el("div", { class: "insp-sec" }, el("h4", { text: "Appears in" }), ul));
    }
  }
  function holdersText(v) {
    const w = (v.who || []).filter((x) => x !== "public").map((x) => actorOf(x).name);
    return w.length ? w.join(" and ") : "Its owner";
  }
  function section(title, body, copyText) {
    const h = el("h4", null, el("span", { text: title }));
    if (copyText && navigator.clipboard) {
      const b = el("button", { type: "button", text: "Copy" });
      b.addEventListener("click", async () => {
        try { await navigator.clipboard.writeText(copyText); b.textContent = "Copied"; b.classList.add("copied"); } catch { b.textContent = "Copy failed"; }
        setTimeout(() => { b.textContent = "Copy"; b.classList.remove("copied"); }, 1400);
      });
      h.append(b);
    }
    return el("div", { class: "insp-sec" }, h, body);
  }
  function appearsIn(vid) {
    const needle1 = `"${vid}"`, needle2 = `{${vid}}`;
    const out = [];
    S.stageJson.forEach((j, i) => { if (j.includes(needle1) || j.includes(needle2)) out.push(i); });
    return out;
  }
  function legend() {
    const rows = [
      ["k-G1", "\\G_1", "points of $\\G_1$: identifiers, tags, commitments, signatures. 48 B."],
      ["k-G2", "\\G_2", "points of $\\G_2$: the VTC's key $\\tilde X, \\tilde Y_1, \\tilde Y_2$. 96 B."],
      ["k-GT", "\\G_T", "pairing values: both sides of every pairing equation. 576 B."],
      ["k-Fr", "\\Z_p", "scalars: keys, serials, challenges, responses, classes $\\varphi$. 32 B."],
      ["k-bytes", "H", "bytes: digests, contexts, proofs, keys, metadata."],
      ["secret", "\\usk", "hatched: a secret. Shown only because the walkthrough peeks."],
    ];
    const box = el("div", { class: "legend" });
    for (const [cls, sym, text] of rows) {
      box.append(el("div", { class: "legend-row" }, tex(el("span", { class: `sw ${cls}` }), sym), md(text, el("p"))));
    }
    return [
      el("div", { class: "insp-title", text: "How to read the formulas" }),
      el("p", { class: "insp-note", text: "Colour tells the group a symbol lives in." }),
      box,
      el("p", { class: "insp-hint", text: "Select any coloured symbol in a formula, any value, or any coloured string in a message, to see its full encoding, who holds it, and where else it appears." }),
    ];
  }

  // ------------------------------------------------------------------------------ help dialog
  function buildHelp() {
    const body = $("#help-body");
    body.replaceChildren();
    body.append(el("section", null, el("h3", { text: "A step" }),
      md("Every step has the same parts, like a stage of the terminal walkthrough. The bar at the top says which step this is, which action is running and which engine call it is in. The step then lists its **actions**, numbered, each by one party: what it computes, what it checks, and what it sends to whom. A message shows its content as JSON: the join submission in its **wire format**, the VTC's answer as a **verdict**, and every other message as the **in-memory** object it is in this prototype, written out by the crate's serde layer. After the actions comes the **outcome**, and the panel on the right (below, on a narrow screen) says **where things stand**: who holds what, and what each application is still missing.", el("p"))));
    body.append(el("section", null, el("h3", { text: "Pacing" }),
      md("Each action first shows the engine calls it made, one by one, then its result. The whole run was computed by the server when the page loaded; the delays are there so that an audience can follow, and the times shown are the ones measured in that run. Choose *slow*, *one action per key* or *instant* in the bar.", el("p"))));
    const keys = [
      [["→"], "the next action (one action per key), or show the rest of the step, or the next step"],
      [["←"], "the previous step"],
      [["Space"], "as →, in presenter mode or one action per key; it scrolls otherwise"],
      [["R"], "play this step again"],
      [["1", "…", "9"], "the first step of a phase"],
      [["S"], "the list of every step"],
      [["L"], "the attack lab"],
      [["P"], "presenter mode: larger type, the state below each step"],
      [["V"], "show or hide the values under the formulas"],
      [["T"], "light or dark"],
      [["Esc"], "close this, the list or the inspector"],
    ];
    const kg = el("div", { class: "keys-grid" });
    for (const [ks, what] of keys) {
      const k = el("span");
      ks.forEach((x, i) => { if (i) k.append(" "); k.append(el("kbd", { text: x })); });
      kg.append(k, el("span", { text: what }));
    }
    body.append(el("section", null, el("h3", { text: "Keys" }), kg));
    const notation = [
      ["\\G_1, \\G_2, \\G_T,\\ e", "groups of prime order $p$ of BLS12-381 and the pairing $e : \\G_1 \\times \\G_2 \\to \\G_T$ (type 3)"],
      ["\\gone, \\gtil", "the generators of $\\G_1$ and $\\G_2$"],
      ["H_0", "hash to $\\Z_p$, typed: the identity point $c_0$, the class $\\EncPred(f)$, the tag point $s = H_0(id)$"],
      ["H_1", "the Fiat–Shamir challenge, over the context, the statement and the commitment"],
      ["H_2", "hash to $\\G_1 \\setminus \\{1\\}$, programmed so that $H_2(c_0) = g_1$"],
      ["\\usk,\\ id = g_1^{\\usk}", "a key and its identifier; vetters keep one for life, applicants draw one per application"],
      ["T = H_2(s)^{\\usk}", "a tag, $\\Tag_{\\mathsf{DDH}}(\\usk, s)$: deterministic, key-injective, pseudorandom under DDH"],
      ["\\varphi = \\EncPred(f)", "the class a credential certifies, e.g. the root predicate $(0, \\texttt{vetter/2026-09})$"],
      ["\\hvk,\\ \\tvk", "the VTC's PS keys for credentials and for tokens: $(\\tilde X, \\tilde Y_1, \\tilde Y_2, Y_1)$"],
      ["\\hat\\sigma,\\ \\sigma,\\ \\sigma'", "a blind PS signature, the unblinded one, a re-randomised showing"],
      ["C = g_1^{\\rho} Y_1^{\\usk}", "the commitment an issuance proof carries"],
      ["att_j = (T_j, \\cred^*_j, \\varphi_j, \\pi_j)", "an attestation"],
      ["\\pi = ((att_j)_j, C, T_0, \\pi_0)", "the proof of $k$ distinct attestations; $T_0$ is the prover's own tag"],
      ["\\ctx_j,\\ \\ctx_0", "the Fiat–Shamir contexts, always rebuilt by the verifier from public data"],
      ["\\app_j,\\ \\app_0", "application contexts: a statement's metadata; the challenge and the join binding"],
    ];
    const dl = el("dl", { class: "notation" });
    for (const [sym, text] of notation) dl.append(tex(el("dt"), sym), md(text, el("dd")));
    body.append(el("section", null, el("h3", { text: "Colour" }), ...legend().slice(2, 3)));
    body.append(el("section", null, el("h3", { text: "Notation" }), dl));
  }
  function openHelp(on) {
    const h = $("#help");
    h.hidden = !on;
    if (on) $("#help-close").focus();
  }

  // ------------------------------------------------------------------------------ routing
  function parseHash() {
    const h = location.hash.replace(/^#\/?/, "");
    const [kind, id] = h.split("/");
    if (kind === "lab") return { kind: id ? "lab" : "labindex", id };
    if (kind === "stage" && id && S.stageIndex[id] != null) return { kind: "stage", id };
    return { kind: "stage", id: "intro" };
  }
  function route() {
    if (!S.run) return;
    S.route = parseHash();
    closeInspector();
    if (S.route.kind === "stage") renderStagePage(S.route.id);
    else if (S.route.kind === "labindex") renderLabIndex();
    else renderLabPage(S.route.id);
    updateBar();
  }
  function go(delta) {
    const lab = S.run.lab;
    const stages = S.run.stages;
    if (S.route.kind === "labindex") {
      location.hash = delta < 0 ? `#/stage/${stages[stages.length - 1].id}` : `#/lab/${lab[0].id}`;
      return;
    }
    if (S.route.kind === "lab") {
      const i = lab.findIndex((l) => l.id === S.route.id) + delta;
      if (i < 0) location.hash = "#/lab";
      else if (i < lab.length) location.hash = `#/lab/${lab[i].id}`;
      return;
    }
    const i = S.stageIndex[S.route.id] + delta;
    if (i >= 0 && i < stages.length) location.hash = `#/stage/${stages[i].id}`;
    else if (i >= stages.length) location.hash = "#/lab";
  }
  function replay() {
    if (S.route.kind === "stage") {
      S.seen.delete(S.route.id);
      renderStagePage(S.route.id);
      updateBar();
    } else if (S.route.kind === "lab" && S.lab[S.route.id]) {
      stopPlayer();
      renderLabResult($(".lab-result"), S.lab[S.route.id], true);
    }
  }

  // ------------------------------------------------------------------------------ loading
  async function load(seed) {
    const q = seed == null ? "" : `?seed=${encodeURIComponent(seed)}`;
    const res = await fetch(`/api/run${q}`);
    const data = await res.json();
    if (!res.ok) throw new Error(data.error || res.statusText);
    S.run = data;
    S.values = data.values;
    S.stageIndex = {};
    data.stages.forEach((s, i) => { S.stageIndex[s.id] = i; });
    S.stageJson = data.stages.map((s) => JSON.stringify(s));
    S.mbIndex = {};
    for (const [id, v] of Object.entries(data.values)) if (v.mb && !(v.mb in S.mbIndex)) S.mbIndex[v.mb] = id;
    S.lab = {};
    S.selected = null;
    S.seen = new Set();
  }
  async function setSeed(seed) {
    const btn = $("#reseed");
    btn.disabled = true;
    btn.textContent = "Computing…";
    try {
      stopPlayer();
      await load(seed);
      const url = new URL(location.href);
      if (seed === S.run.meta.defaultSeed) url.searchParams.delete("seed"); else url.searchParams.set("seed", String(seed));
      history.replaceState(null, "", url);
      buildChrome();
      route();
    } catch (e) {
      $("#main").replaceChildren(el("div", { class: "error-box", text: `The run failed: ${e.message}` }));
    } finally {
      btn.disabled = false;
      btn.textContent = "New randomness";
    }
  }

  // ------------------------------------------------------------------------------ theme, presenter, values, pace, keys
  function applyTheme(t) {
    if (t) document.documentElement.setAttribute("data-theme", t);
    else document.documentElement.removeAttribute("data-theme");
  }
  function currentTheme() {
    const t = document.documentElement.getAttribute("data-theme");
    if (t) return t;
    return window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
  }
  function toggleTheme() {
    const next = currentTheme() === "dark" ? "light" : "dark";
    applyTheme(next);
    store.set("pcs.theme", next);
  }
  function setPresenting(on) {
    S.presenting = on;
    $("#app").classList.toggle("presenting", on);
    $("#present").setAttribute("aria-pressed", on ? "true" : "false");
  }
  function toggleVals() {
    S.showVals = !S.showVals;
    store.set("pcs.showVals", S.showVals ? "1" : "0");
    for (const f of document.querySelectorAll(".flow")) f.classList.toggle("no-vals", !S.showVals);
    for (const b of document.querySelectorAll(".vals-toggle")) b.textContent = S.showVals ? "Hide values" : "Show values";
  }
  function setPace(p) {
    if (!(p in PACE)) return;
    S.pace = p;
    store.set("pcs.pace", p);
    $("#pace").value = p;
    const pl = activePlayer();
    if (pl && p === "instant") pl.skip();
    else if (pl && p !== "manual" && pl.waiting) pl.next();
    updateBar();
  }

  function onKey(e) {
    if (e.metaKey || e.ctrlKey || e.altKey) return;
    const t = e.target;
    if (t && (t.tagName === "INPUT" || t.tagName === "SELECT" || t.tagName === "TEXTAREA")) return;
    if (["PageDown", "PageUp", "Home", "End", "ArrowDown", "ArrowUp"].includes(e.key)) S.userScrollAt = Date.now();
    const helpOpen = !$("#help").hidden;
    if (e.key === "Escape") {
      if (helpOpen) openHelp(false);
      else { closeInspector(); openOutline(false); }
      return;
    }
    if (helpOpen) return;
    const onControl = t && (t.tagName === "BUTTON" || t.tagName === "A" || t.tagName === "SUMMARY");
    switch (e.key) {
      case "ArrowRight": case "PageDown": case "j":
        if (e.key === "PageDown") return;
        e.preventDefault(); primary(); break;
      case "ArrowLeft": case "k":
        e.preventDefault(); go(-1); break;
      case "Enter":
        if (onControl) return;
        e.preventDefault(); primary(); break;
      case " ":
        if (!(S.presenting || S.pace === "manual") || onControl) { S.userScrollAt = Date.now(); return; }
        e.preventDefault(); primary(); break;
      case "r": case "R": replay(); break;
      case "p": case "P": setPresenting(!S.presenting); break;
      case "t": case "T": toggleTheme(); break;
      case "v": case "V": toggleVals(); break;
      case "l": case "L": location.hash = "#/lab"; break;
      case "s": case "S": openOutline(!$("#outline").classList.contains("open")); break;
      case "?": openHelp(true); break;
      default:
        if (/^[1-9]$/.test(e.key)) {
          const ph = S.run.phases[Number(e.key) - 1];
          const first = ph && S.run.stages.find((s) => s.phase === ph);
          if (first) location.hash = `#/stage/${first.id}`;
        }
    }
  }

  // ------------------------------------------------------------------------------ start
  async function start() {
    const t = store.get("pcs.theme");
    if (t === "light" || t === "dark") applyTheme(t);
    S.showVals = store.get("pcs.showVals") !== "0";
    const p = store.get("pcs.pace");
    if (p && p in PACE) S.pace = p;
    $("#pace").value = S.pace;
    $("#pace").addEventListener("change", (e) => setPace(e.target.value));
    $("#theme").addEventListener("click", toggleTheme);
    $("#present").addEventListener("click", () => setPresenting(!S.presenting));
    $("#help-btn").addEventListener("click", () => openHelp(true));
    $("#help-close").addEventListener("click", () => openHelp(false));
    $("#help").addEventListener("click", (e) => { if (e.target === e.currentTarget) openHelp(false); });
    $("#menu").addEventListener("click", () => openOutline(!$("#outline").classList.contains("open")));
    $("#scrim").addEventListener("click", () => openOutline(false));
    $("#prev").addEventListener("click", () => go(-1));
    $("#next").addEventListener("click", primary);
    $("#reseed").addEventListener("click", () => {
      const r = new Uint32Array(1);
      crypto.getRandomValues(r);
      setSeed(r[0]);
    });
    for (const ev of ["wheel", "touchmove"]) window.addEventListener(ev, () => { S.userScrollAt = Date.now(); }, { passive: true });
    document.addEventListener("keydown", onKey);
    window.addEventListener("hashchange", route);
    const seed = new URL(location.href).searchParams.get("seed");
    try {
      await load(seed && /^\d+$/.test(seed) ? seed : null);
    } catch (e) {
      $("#main").replaceChildren(el("div", { class: "error-box", text: `The server did not answer (${e.message}). Is cargo run -p pcs-vetting-prototype --release --example walkthrough-web still running?` }));
      return;
    }
    buildChrome();
    buildHelp();
    route();
  }
  start();
})();
