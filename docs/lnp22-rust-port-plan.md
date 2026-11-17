# A native Rust library for the LNP22 lattice proof system: implementation plan

This document is the specification and work plan for a pure-Rust implementation of the
zero-knowledge proof system of Lyubashevsky, Nguyen and Plançon, "Lattice-Based Zero-Knowledge
Proofs and Applications: Shorter, Simpler, and More General" (ePrint 2022/284, "LNP22"), at the
level of functionality of IBM's C library LaZer (ePrint 2024/1846), plus the pieces LaZer does not
offer. It is written for an implementing agent that has this file, the LNP22 paper, and a checkout
of LaZer, and nothing else from the conversation that produced it.

Everything stated as fact below was read first-hand in one of these sources:

- LNP22, ePrint 2022/284, version with 84 pages (page and figure numbers refer to that version).
- LaZer, `https://github.com/lazer-crypto/lazer`, commit `e382e584daabfe6e241503be194ee1f9049b15c4`
  (2026-09-25, "add support for falcon-1024"), MIT licence, copyright IBM 2022-2026. File and
  function names refer to that commit. Line numbers are given only where a detail is easy to miss.
- The LaZer paper, ePrint 2024/1846 (CCS 2024), for the design of the linear front end.
- LaZer's parameter scripts were RUN (Sage 10.9, macOS) on `tests/lnp-tbox-params1.sage`; the
  output reproduces the checked-in `tests/lnp-tbox-params1.h` exactly. LaZer's C code was NOT
  built or run: it requires an x86-64 Linux host with AVX-512 and AES-NI, and none was available.
  Every statement about LaZer's run-time behaviour is therefore a reading of the source, and is
  marked "(reading)" where it matters. Nothing here was checked against Nguyen's thesis
  (DOI 10.3929/ethz-b-000574844), which LaZer's scripts cite as "[1]" for several constants.

The crate built from this plan is named **Jali** and lives in `jali/`; the working name `lnp22`
used below refers to it.

Conventions: math is written in GitHub-flavoured Markdown (`$…$` inline, ```math blocks), so this
file renders on GitHub and, if copied into rustdoc with the KaTeX header described in §12, in the
API documentation as well. "Paper" means LNP22. `file.c:function` names LaZer code.

---

## 0. Summary and decisions

**What exists.** LaZer's C layer implements the complete LNP22 protocol stack: the ABDLOP
commitment with Dilithium-style compression (`abdlop.c`), the proof of one quadratic relation with
the automorphism $\sigma_{-1}$ (`lnp-quad.c`), of many quadratic relations (`lnp-quad-many.c`), of
quadratic relations whose constant coefficient vanishes (`lnp-quad-eval.c`), and the full
"toolbox" of Section 5 of the paper — approximate range proofs, exact Euclidean-norm proofs,
binary proofs, packed signs (`lnp-tbox.c`, `lnp.c`). Only LaZer's Python front end
(`python/lazer.py`, `lin-proofs.c`) is restricted to linear relations $A w + t = 0$ with norm
bounds. The premise that LaZer implements only the linear part of LNP22 is therefore wrong for the
C library and right for the Python API. The port covers the whole C stack.

**What is new in the port.** Three things LaZer does not have, in decreasing order of importance
for the credential work this library is meant for:

1. Quadratic statements over a *statement ring* $R_{p,d'} = \mathbb{Z}_p[X]/(X^{d'}+1)$ that
   differs from the proof-system ring $R_{q,d}$ (LaZer's `quad_toisoring` has the quadratic branch
   disabled, `quad.c:191`, and its modulus lifting handles only linear relations). §7.
2. A high-level statement builder with named variables, automatic degree lowering and modulus
   lifting, replacing hand-written sparse matrices in LaZer's interleaved index space. §7.
3. A deliberate policy towards LaZer's deviations from the paper. LaZer is not a transcription
   of LNP22: it incorporates later optimisations (some cited to Nguyen's thesis, some from the
   blind-signature and anonymous-credential papers its demos implement) and engineering choices
   made for speed. Those are adopted. It also contains deviations that, on reading, weaken
   properties the paper proves (challenge derivation, Fiat–Shamir order, one verifier check, two
   samplers). Those are not ported; §10 lists every deviation found, classifies it, and gives the
   port's decision. A `lazer-compat` test mode reproduces LaZer's byte formats and challenge
   derivations so that proofs produced by LaZer's honest prover serve as known-answer tests.

**Policy on paper versus LaZer.** The paper is the authority on the protocol's message order,
challenge derivation and verification equations, because that is what its security proofs
cover; the port follows it there. LaZer is the authority on everything the paper leaves open or
does inefficiently: representation of the witness and of quadratic forms, arithmetic, encodings,
parameter search, the constants of the rejection samplers, the treatment of the challenge set,
how the linear front end avoids committing to carries. Where the two disagree, §10 records the
disagreement, whether LaZer's version has a documented rationale, and what the port does. The
default is: adopt LaZer's optimisation when it is an optimisation; keep the paper's order and
checks when LaZer's change has no visible rationale and weakens a proven property. Both the
thesis LaZer cites and the follow-up papers should be consulted by the implementer before the
first release, because this document could not check them (§15).

**Architecture in one paragraph.** One Rust crate (working name `lnp22`; the final name is the
owner's choice) with layers: integers and rings (`i128` coefficients, residue-number-system NTT
over 62-bit primes, exact CRT), samplers (AES-256-CTR or SHAKE128 PRG, uniform, binomial,
discrete Gaussian with $\sigma = 1.55\cdot 2^k$, rejection sampling in 128-bit fixed point),
codec (LaZer's bit-level encodings), commitment (`abdlop`), the protocol tower (`quad`,
`quad_many`, `quad_eval`, `tbox`), the statement layer (`lnp`, `lin`, `statement`), and
parameters (`params`, with a Sage/Python generator in `tools/`). No C dependencies, no `unsafe`
outside an optional SIMD NTT. Tests at every layer with independent oracles, criterion
benchmarks, rustdoc with KaTeX. §8–§13.

**Order of work.** Milestones M0–M7 in §13; each has acceptance criteria. M1–M4 reproduce LaZer
(and pass its proofs in compat mode); M5 ports the linear front end and the parameter generator;
M6 adds quadratic statements over arbitrary rings; M7 is performance and release.

---

## 1. Background: what LaZer is, exactly

### 1.1 Layers (reading of the tree at `e382e584`)

| Layer | Files | Status |
|---|---|---|
| Integers, vectors, matrices | `int.c`, `intvec.c`, `intmat.c`; types in `lazer-in2.h` | multi-limb sign-magnitude integers on 64-bit limbs (`int_t {limbs, nlimbs, neg}`) |
| Polynomial rings | `polyring.c`, `poly.c`, `polyvec.c`, `polymat.c`, `spolyvec.c`, `spolymat.c`, `moduli.h`, `ntt.c`, `hexl.cpp`, `mont.h` | coefficient domain = `int_t` per coefficient; "CRT domain" = residues modulo 50-bit NTT primes, transformed with Intel HEXL; `d ∈ {64, 128}` only (`moduli_d64`, `moduli_d128`) |
| Randomness | `rng.c`, `aes256ctr*.c`, `shake128.c`, `urandom.c`, `brandom.c`, `grandom.c`, `rejection.c` | AES-256-CTR PRG by default (`config.h: RNG RNG_AES256CTR`), SHAKE128 for hashing; MPFR at 128-bit precision for rejection sampling |
| Encodings | `coder.c`, `bytes.c` | bit-level packing of uniform values, Gaussian values (unary + binary), Dilithium hints |
| Compression | `dcompress.c` | Power2Round, Decompose, MakeGHint, UseGHint (Appendix A of the paper) |
| Commitment | `abdlop.c` | keygen from a seed, commit, opening proof with compression (Fig. 18) |
| Quadratic proofs | `lnp-quad.c`, `lnp-quad-many.c`, `lnp-quad-eval.c` | Figs. 6, 7, 8 with the $\lambda/2$ garbage trick of Section 4.4 |
| Toolbox | `lnp-tbox.c` (+ `lnp-tbox.h` slot offsets) | Fig. 10: ARP, exact $\ell_2$, binary, packed signs, all as equations for `quad_eval` |
| Statement object | `lnp.c` | prover/verifier state, `set_witness`, `set_statement_{quadeqs, evaleqs, l2, bin, arp}`, statement hashing, proof (de)serialisation |
| Linear front end | `lin-proofs.c`, `quad.c` (`lin_toisoring`) | $A w + t = 0$ over $R_{p,d'}$ with per-block $\ell_2$ or binary bounds; degree lowering; modulus lifting; contains a specialised COPY of the toolbox |
| Parameter generation | `scripts/*.sage` | `codegen.sage` (helpers, moduli), `abdlop-codegen.sage`, `lnp-quad-codegen.sage`, `lnp-quad-eval-codegen.sage`, `lnp-tbox-codegen.sage`, `lin-codegen.sage`, `moduli.sage` |
| Applications | `blindsig.c`, `python/*` demos, `labrador*` | blind signature, anonymous credentials, Kyber/Falcon proofs; LaBRADOR succinct proofs (out of scope here) |
| Python | `python/lazer.py` (CFFI) | ring arithmetic, `lin_prover_state_t`/`lin_verifier_state_t` only |

`lnp.c` (the generic statement object with quadratic equations) is not exercised by any test,
demo or Python code in the tree (reading; `tests/lnp-tbox-test.c` calls `lnp_tbox_prove`
directly), and it has index-convention inconsistencies with `lnp-tbox.c` (§10.3). The tested
path is `lin-proofs.c`, whose toolbox copy differs from `lnp-tbox.c` in its challenge domains
(§10.3). Proofs of the two copies are not interchangeable.

### 1.2 Build constraints (README at `e382e584`)

Linux x86-64, kernel ≥ 4.18, AVX-512 and AES instruction sets, gcc ≥ 13.2, Sage ≥ 10.2, HEXL
(`third_party/hexl-development.zip`), Falcon reference code (`third_party/Falcon-impl-20211101.zip`),
GMP and MPFR, `-march=native`. None of this ports; the Rust library must depend on none of it.

### 1.3 Licence

MIT. Porting the algorithms, constants (`moduli.h`, `grandom.c: CDF155`) and encodings is
unproblematic; keep LaZer's copyright notice where tables are copied verbatim.

---

## 2. Mathematical background and notation (LNP22 Sections 2, 4.4, 5.3)

All of this section is "standard result, from the paper" unless marked.

### 2.1 Rings, norms, automorphism

- $R = \mathbb{Z}[X]/(X^d+1)$, $d$ a power of two; $R_q = R/qR$. LaZer supports $d \in \{64, 128\}$
  for the proof ring; statement rings of larger degree are lowered to it (§7.2).
- $q = q_1 \cdots q_n$, $n \in \{1, 2\}$, each $q_i \equiv 5 \pmod 8$ prime, $q_1 < q_2$. Then
  $X^d + 1 \equiv (X^{d/2} - r)(X^{d/2} + r) \pmod{q_i}$ splits into $l = 2$ factors. Consequences
  used everywhere: Lemma 2.5 (small nonzero elements are invertible: $\|f\|_\infty < q_1^{1/2}/\sqrt2$
  or $\|f\| < q_1^{1/2}$), Lemma 2.6 ($\sigma_{-1}$-invariant nonzero elements are invertible), and
  a nonzero linear form vanishes on a uniform $\mathbb{Z}_q$ challenge with probability at most
  $1/q_1$, a nonzero polynomial evaluated on a uniform $R_q$ challenge vanishes with probability
  at most $q_1^{-d/2}$ (Lemma 4.3).
- $\sigma = \sigma_{-1}$, $\sigma(X) = X^{-1} = -X^{d-1}$. On coefficient vectors:
  $\sigma(a)_0 = a_0$, $\sigma(a)_{d/2} = -a_{d/2}$, $\sigma(a)_i = -a_{d-i}$ otherwise
  (`intvec.c:intvec_auto`).
- $T(\vec a, \vec b) := \sum_{i<k} \sigma(a_i)\, b_i \in R$ for $\vec a, \vec b \in \mathbb{Z}^{kd}$
  read as $k$ polynomials (Eq. 16); its constant coefficient is $\langle \vec a, \vec b\rangle$
  (Lemma 2.4). This is how integer inner products become constant coefficients of ring elements.
- $\mathrm{Tr}(x) := 2^{-1}(x + \sigma(x))$ (Section 4.4). $\mathrm{Tr}(x)_0 = x_0$,
  $\mathrm{Tr}(x)_{d/2} = 0$; $X^{d/2}\mathrm{Tr}(x)$ has coefficient $0$ at position $0$ and $x_0$
  at position $d/2$ (Lemma 4.7). `poly.c:poly_tracemap` computes $\mathrm{Tr}$ directly.
- Norms on coefficient vectors: $\|\cdot\|$ is $\ell_2$, $\|\cdot\|_\infty$ uses centred
  representatives in $(-q/2, q/2]$. $S_\gamma = \{x \in R_q : \|x\|_\infty \le \gamma\}$.
- Multiplication by $X^j$ (`intvec_lrot` by $j$) is a signed rotation: $(X^j a)_i = a_{i-j}$ for
  $i \ge j$ and $-a_{d+i-j}$ for $i < j$.

### 2.2 Distributions

- $D_s^\ell$: discrete Gaussian on $\mathbb{Z}^\ell$ with $\rho(z) \propto \exp(-\|z\|^2/(2s^2))$.
  Tail bound (Lemma 2.2): $\Pr[\|z\| > t\, s\sqrt{md}] < (t e^{(1-t^2)/2})^{md}$; $t = 1.64$ is used
  for $md = 256$ and $2^{-128}$.
- $\mathrm{Bin}_\kappa = \sum_{i\le\kappa}(a_i - b_i)$, $a_i, b_i \leftarrow \{0,1\}$; $\mathrm{Bin}_1$
  is uniform on $\{-1, 0, 1\}$ with weights $1/4, 1/2, 1/4$. LaZer samples it as one bit minus
  one bit (`brandom.c`).
- Uniform on $\mathbb{Z}_q$, on $[-\nu, \nu]$, on $\{x \in R_q : x_0 = 0\}$ etc. as needed.

### 2.3 Rejection sampling (Lemma 2.14, Figs. 1 and 2)

For $v$ with $\|v\| \le T$ and $s = \gamma T$:

- $\mathrm{Rej}_1(z, v, s)$: $u \leftarrow [0,1)$; reject iff $u > \frac1M \exp\!\big(\frac{-2\langle z,v\rangle + \|v\|^2}{2s^2}\big)$,
  $M = \exp(14/\gamma + 1/(2\gamma^2))$ for $2^{-128}$ statistical distance. LaZer uses the general
  form $M = \exp\big(\sqrt{2(\kappa+1)/\log_2 e}\,/\gamma + 1/(2\gamma^2)\big)$ with $\kappa = 128$,
  i.e. $13.37/\gamma$ instead of $14/\gamma$ (`codegen.sage: std_gamma2M`).
- $\mathrm{Rej}_2$: as $\mathrm{Rej}_1$ but reject immediately if $\langle z, v\rangle < 0$,
  $M = \exp(1/(2\gamma^2))$; leaks one bit, needs Extended-MLWE. LaZer does not implement it.
- $\mathrm{Rej}_0$ (bimodal): $\beta \leftarrow \{0,1\}$, $z = y + (-1)^\beta v$; reject iff
  $u > 1/\big(M \exp(-\|v\|^2/(2s^2)) \cosh(\langle z, v\rangle/s^2)\big)$, $M = \exp(1/(2\gamma^2))$.
  The sign flip is part of the algorithm; without it the output is biased (§3.3).
- Standard deviations (p. 17, Section 6.1): $s_1 = \gamma_1 \eta \alpha$ for the Ajtai part with
  $\|s_1\| \le \alpha$; $s_2 = \gamma_2 \eta \nu \sqrt{m_2 d}$ for the randomness
  $s_2 \leftarrow [-\nu,\nu]^{m_2 d}$; $s^{(e)} = \gamma^{(e)}\sqrt{337}\,\alpha^{(e)}$ and
  $s^{(d)} = \gamma^{(d)}\sqrt{337}\,\alpha^{(d)}$ for the range-proof masks. LaZer rounds every
  standard deviation to the nearest $1.55 \cdot 2^k$ (`codegen.sage: round_stdev`) and recomputes
  $\gamma$ from the rounded value.

### 2.4 Challenge space (Section 2.7)

$C = \{c \in S_\kappa : \sigma(c) = c,\ (\|\sigma(c^k) c^k\|_1)^{1/(2k)} \le \eta\}$ with $k = 32$
in the paper's tables. Fig. 3 ($d = 128$): $\kappa = 2$, $\eta = 59$, $|C| \approx 2^{147}$.
LaZer's parameter scripts hard-code $(\kappa, \eta, |C|) = (8, 140, 2^{129})$ for $d = 64$ and
$(2, 59, 2^{147})$ for $d = 128$ (`lnp-tbox-codegen.sage:118-128`), and its sampler
(`intvec.c:_intvec_urandom_autostable`) draws $d/2$ coefficients uniformly from $[-\kappa, \kappa]$,
sets coefficient $d/2$ to $0$ and mirrors $c_{d-i} = -c_i$; it does NOT apply the $\eta$ filter of
Eq. (21). The paper's tables say roughly 99 % of $S_\kappa^\sigma$ satisfy the filter. Decision for
the port: sample as LaZer does, document that $\eta$ is a bound that holds for all but about 1 %
of challenges, and keep the option to enable the filter (§10.6, item 23).

### 2.5 Approximate range proof lemmas (Section 2.4)

- Lemma 2.7: $R \leftarrow \mathrm{Bin}_1^{k \times m}$: $\Pr[\|R\vec w + \vec y\|_\infty < \tfrac12\|\vec w\|_\infty] \le 2^{-k}$.
- Lemma 2.8 (heuristic): $R \leftarrow \mathrm{Bin}_\kappa^{256\times m}$:
  $\Pr[\|R \vec w\|^2 < 13\kappa\|\vec w\|^2] \le 2^{-256}$, $\Pr[\|R\vec w\|^2 > 337\kappa\|\vec w\|^2] \le 2^{-128}$.
  The constants 13, 26, 337 in the protocol come from here.
- Lemma 2.9: $b \le q/(41 m)$, $\|\vec w\| \ge b$: $\Pr_{R \leftarrow \mathrm{Bin}_1^{256\times m}}[\|R\vec w + \vec y \bmod q\| < \tfrac12 b \sqrt{26}] < 2^{-128}$.

### 2.6 Hardness assumptions

$\mathrm{MSIS}_{n, m, B}$ over $R_q$ (find short $z$ with $A z = 0$), $\mathrm{MLWE}_{m,\lambda,\chi}$,
and Extended-MLWE (Def. 2.13) for zero-knowledge with $\mathrm{Rej}_2$ or bimodal sampling.
Parameter scripts target root Hermite factor $\delta \le 1.0044$ for both (LaZer) or $< 1.0045$
(paper). §5.

---

## 3. The protocol stack, as it must be implemented

This section is the normative core. Each sub-protocol is stated as the paper gives it, then the
concrete choices LaZer makes (message layouts, hashing, encodings) are given, and finally the
port's decision. Symbol map: paper $n$ = LaZer `kmsis`; $m_1, \ell, m_2, \lambda, \nu, D, \gamma$
are the same letters (`m1, l, m2, lambda, nu, D, gamma`); paper $\kappa$ (challenge coefficient
bound) = LaZer `omega`; $\eta$ = `eta`; $s_i$ = `stdev_i` $= 1.55\cdot 2^{\texttt{log2stdev}_i}$;
paper $(y^{(e)}, b^{(e)}, z^{(e)}, R^{(e)}, e^{(e)})$ = LaZer `(y3, beta3, z3, R, s3)`;
$(y^{(d)}, b^{(d)}, z^{(d)}, R^{(d)}, e^{(d)})$ = `(y4, beta4, z4, Rprime, s4)`; paper $x$
(binary decompositions of the $\ell_2$ slack) = `upsilon`; paper $h_i$ = LaZer `h`; paper's
Dilithium hint $h$ = LaZer `hint`; paper $g$ = `g` committed as `tg`; paper $t$ (garbage
$g_1$ commitment) = `t` = last entry of `tB`.

### 3.1 ABDLOP commitment (Fig. 4, Appendix A Eq. 81)

Public matrices from a 32-byte seed `ppseed` (`abdlop.c:abdlop_keygen`):
$A_1 \in R_q^{n\times m_1}$ (domain 0), $A_2' \in R_q^{n\times(m_2-n)}$ (domain 1),
$B' \in R_q^{(\ell+\ell_{\mathrm{ext}})\times(m_2-n)}$ (domain 2), each entry a uniform polynomial
(§4.2 for the exact derivation). Structured form (Eq. 81): $A_2 = [A_2' \mid I_n]$,
$B = [B' \mid 0]$, $s_2 = (s_{2,1}, s_{2,2}) \in R_q^{m_2-n} \times R_q^n$.

Commitment to $s_1 \in R_q^{m_1}$ ($\|s_1\| \le \alpha$) and $m \in R_q^{\ell + \ell_{\mathrm{ext}}}$
with $s_2 \leftarrow [-\nu, \nu]^{m_2 d}$ (`abdlop.c:abdlop_commit`):

```math
t_A = A_1 s_1 + A_2' s_{2,1} + s_{2,2},\qquad
t_{A,1} = \mathrm{Power2Round}_q(t_A, D),\quad t_{A,2} = t_A - 2^D t_{A,1},\qquad
t_B = B' s_{2,1} + m .
```

Only $t_{A,1}$ and $t_B$ are published; $t_{A,2}$ ($\|t_{A,2}\|_\infty \le 2^{D-1}$) stays with the
prover. The extension part of $m$ (length $\ell_{\mathrm{ext}}$) is filled in later by the
sub-protocols (masks $y^{(e)}, y^{(d)}$, sign $b$, garbage $g$, garbage $g_1$); the corresponding
rows of $t_B$ are computed by them, not by `commit`.

### 3.2 Opening proof with compression (Fig. 18, Theorem A.2)

Given the transcript hash `hash` (32 bytes), prove knowledge of an opening of $(t_{A,1}, t_B)$:

```
P: y1 ← D_{s1}^{m1};  y2 = (y21, y22) ← D_{s2}^{m2};  w := A1 y1 + A2' y21 + y22;
   (w1, w0) := Decompose_q(w, γ)                      -- coefficient-wise, Fig. 17
   c := H(hash ‖ enc(w1))                              -- §3.7 for enc, §4 for H
   z1 := y1 + c s1;  z2 := y2 + c s2;  Rej on (z1, c s1) and (z2, c s2)   -- §2.3
   z22 := z22 − c t_{A,2} − w0;  if ‖(z21, z22)‖ > B: restart
   h := MakeGHint_q(z22, γ w1 − z22, γ)                -- per coefficient
   send (c, z1, z21, h)
V: w1' := UseGHint_q(h, A1 z1 + A2' z21 − c 2^D t_{A,1}, γ)
   accept iff c = H(hash ‖ enc(w1')), ‖z1‖ ≤ s1 √(2 m1 d),
              ‖(z21, A1 z1 + A2' z21 − c 2^D t_{A,1} − γ w1')‖ ≤ B, ‖h‖∞ ≤ (q−1)/(2γ)
```

with $B = s_2\sqrt{2 m_2 d} + \eta 2^{D-1}\sqrt{nd} + \gamma\sqrt{nd}/2$ (Theorem A.2;
`lnp-tbox-codegen.sage: Bound_`). Compression functions (Fig. 17), all on integers
$r \in \mathbb{Z}_q$ taken in $[0, q)$:

```
Power2Round_q(r, D):  r0 := r mod± 2^D;  return (r − r0)/2^D
Decompose_q(r, γ):    r0 := r mod± γ;  if r − r0 = q − 1 then (r1, r0) := (0, r0 − 1)
                      else r1 := (r − r0)/γ;  return (r1, r0)          -- needs γ | q − 1, γ even
HighBits = r1, LowBits = r0
MakeGHint_q(z, r, γ): m := (q−1)/γ;  return (HighBits(r + z) − HighBits(r)) mod± m
UseGHint_q(y, r, γ):  m := (q−1)/γ;  return (HighBits(r) + y) mod m
```

Lemma A.1: for $\|z\|_\infty \le \gamma/2$, `UseGHint(MakeGHint(z, r), r) = HighBits(r + z)`.
LaZer (`dcompress.c`) matches this; its `use_ghint` returns values in $[0, m)$ and `make_ghint`
values in $(-m/2, m/2]$ ($m$ even) or $[-(m-1)/2, (m-1)/2]$ ($m$ odd).

**LaZer deviations (reading, `abdlop.c:abdlop_verify`, `lnp-quad.c:lnp_quad_verify`).**
(a) The verifier's second norm check is on $A_1 z_1 + A_2' z_{2,1} - c 2^D t_{A,1} - \gamma w_1$
ALONE (the reconstructed $z_{2,2}$), not on $(z_{2,1}, \cdot)$ as in Fig. 18; $\|z_{2,1}\|$ is never
bounded by the verifier. The prover restricts itself to $\|(z_{2,1}, z_{2,2})\| \le B$. Since
$A_2'$ has more columns than rows, an unbounded $z_{2,1}$ lets a prover hit any target in the first
verification equation; whether this yields a full attack on the toolbox was not worked out, but
the extraction argument of Theorem A.2 needs the joint bound. (b) The hint check is
$\|h\|_\infty \le m$ instead of $\le m/2$; harmless (the hint only reconstructs $w_1$, which is then
checked through the hash). **Port:** implement Fig. 18 literally, including $z_{2,1}$ in the norm.

The verifier's first bound is stored by LaZer as $2 m_1 d \cdot 1.55^2 \cdot 2^{2\,\texttt{log2stdev1}}$
computed as $\lfloor 962 \cdot 2 m_1 d \cdot 2^{2 \texttt{log2stdev1}} / 400 \rfloor$; the port
should store $\lfloor (s_1\sqrt{2m_1 d})^2 \rfloor$ as a parameter.

### 3.3 One quadratic relation with automorphisms: $\Pi^{(2)}$ (Fig. 6, Section 4.1)

Extended witness (paper) $s = (s_1, \sigma(s_1), m, \sigma(m)) \in R_q^{2(m_1+\ell)}$. Statement:
$f(s) = s^{\mathsf T} R_2 s + r_1^{\mathsf T} s + r_0 = 0$ in $R_q$ with public
$R_2 \in R_q^{2(m_1+\ell)\times 2(m_1+\ell)}$ (upper triangular suffices), $r_1$, $r_0$. Extra public
$b \in R_q^{m_2}$ (LaZer: the last row `bextprime` of $B'$), one extra BDLOP slot $t$.

```
P: y1 ← D_{s1}^{m1}, y2 ← D_{s2}^{m2};  w := A1 y1 + A2 y2
   y := (y1, σ(y1), −B y2, −σ(B y2))                        -- Eq. 29
   g1 := sᵀ R2 y + yᵀ R2 s + r1ᵀ y;   t := bᵀ s2 + g1;   v := yᵀ R2 y + bᵀ y2
   send (w, t, v);  receive c;  z1 := c s1 + y1, z2 := c s2 + y2, Rej
V: z := (z1, σ(z1), c t_B − B z2, σ(c t_B − B z2));  f := c t − bᵀ z2       -- Eq. 30
   accept iff norms as in §3.2, A1 z1 + A2 z2 = w + c t_A, and
              zᵀ R2 z + c r1ᵀ z + c² r0 − f = v
```

The identity behind it (Eq. 31): $z^{\mathsf T}R_2 z + c\, r_1^{\mathsf T} z + c^2 r_0 = c^2 f(s) + c\, g_1 + g_0$
with $g_0 = y^{\mathsf T} R_2 y$; the verifier recomputes $v$ from the response and $c$ (non-interactive:
$w$ and $v$ are never sent, only hashed). Theorem 4.2: completeness, simulation under
Extended-MLWE$_{n+\ell+1, m_2-n-\ell-1}$, knowledge soundness with the norm bounds of §3.2 and
extraction in expected time about $2T$ producing $(\bar s_1, \bar s_2, \bar m, \bar c)$ with
$\|\bar c\|_\infty \le 2\kappa$.

**LaZer's index layout (normative for compat mode, `lnp-quad.c`).** The extended witness is
INTERLEAVED, not blocked: index $2i$ holds variable $i$ and index $2i+1$ holds $\sigma$ of it, for
$i < m_1$ over $s_1$ and $i \in [m_1, m_1+\ell)$ over $m$:

```math
s^{\mathrm{LaZer}} = (s_{1,0}, \sigma(s_{1,0}), s_{1,1}, \sigma(s_{1,1}), \dots, m_0, \sigma(m_0), \dots)
```

`R2` is a sorted sparse upper-triangular matrix (`spolymat_t`, entries `(row ≤ col, poly)`), `r1` a
sorted sparse vector (`spolyvec_t`), `r0` a polynomial. $t$ is the last element of `tB`
(`tB = (tB_, …, t)`), $b^{\mathsf T}$ is the last row of `Bprime`, and $v$ is a plain polynomial.
With compression (§3.2) the hash input for $c$ is $(t, v, w_1)$: `enc(t)` and `enc(v)` with
$\lceil\log_2 q\rceil$ bits per coefficient, values in $[0,q)$, then `enc(w1)` with
$\lceil\log_2 m\rceil$ bits per coefficient, $m = (q-1)/\gamma$ (`lnp-quad.c:215-220`).

**Rejection sampling for $z_2$ (reading, `lnp-quad.c:236-275`; paper Section 6.1, Fig. 12).**
$z_1$ uses $\mathrm{Rej}_1$ with $(M_1, s_1^2)$ in both. For $z_2$ the paper's own parameter set
uses $\gamma_2 = 1$, which is only possible with a sampler whose $M = \exp(1/(2\gamma^2))$: that is
$\mathrm{Rej}_2$ (Fig. 1, right: reject when $\langle z, v\rangle < 0$, acceptance about $1/(2M)$,
leaks one bit, needs Extended-MLWE). The bimodal $\mathrm{Rej}_0$ cannot be used for $z_2$ at all:
flipping the sign of $c\,s_2$ breaks the verification equation $A_1 z_1 + A_2 z_2 = w + c\,t_A$
(there is no committed sign to absorb it, unlike the range-proof masks). LaZer's `rej2 == 2`
branch (the default of `lnp-tbox-codegen.sage:73`) applies the bimodal acceptance formula
$1/(M e^{-\|v\|^2/2s^2}\cosh(\langle z,v\rangle/s^2))$ to the UNFLIPPED $z_2 = y_2 + c s_2$, with
$M_2 = \exp(1/(2\gamma_2^2))$, citing "one-time commitments ([1], chapter 7)". The output density
is then $D_s(z)\cdot 2/(1 + e^{-2\langle z, v\rangle/s^2})$: a smooth relative of $\mathrm{Rej}_2$
that leaks a function of $\langle z, c s_2\rangle$ instead of its sign, with about twice the
acceptance rate. This is plausibly the thesis' optimisation and should be adopted once the
thesis argument has been read. Independently of that, the branch passes `stdev1sqr` instead of
`stdev2sqr` as the variance (reading), which for $s_1 \gg s_2$ makes the test accept almost
always and removes the masking effect on $z_2$: a defect, §10.4 item 11. **Port:** implement
$\mathrm{Rej}_1$, $\mathrm{Rej}_2$ and LaZer's smooth variant as selectable policies for $z_2$,
each with the correct $s_2$; default to $\mathrm{Rej}_2$ until the thesis argument is checked,
then switch the default to LaZer's variant if it holds.

### 3.4 Many quadratic relations: $\Pi^{(2)}_{\mathrm{many}}$ (Fig. 7, Section 4.2)

Verifier sends $\mu_1, \dots, \mu_N \leftarrow R_q$; prover runs $\Pi^{(2)}$ on
$f = \sum_j \mu_j f_j$, i.e. $R_2 = \sum \mu_j R_{2,j}$, $r_1 = \sum \mu_j r_{1,j}$,
$r_0 = \sum \mu_j r_{0,j}$. Soundness error $2/|C| + q_1^{-d/2}$. LaZer
(`lnp-quad-many.c:_schwartz_zippel_poly`) derives the $\mu_j$ as $N$ uniform polynomials from the
current transcript hash with `polyvec_urandom(mu, q, log2q, hash, 0)` (domains
$(0 \ll 32) \mid (j+1)$, §4.2), without absorbing anything new.

### 3.5 Vanishing constant coefficients: $\Pi^{(2)}_{\mathrm{eval}}$ (Fig. 8, Sections 4.3–4.4)

Statement: $f_j(s) = 0$ for $j \in [N]$ (all coefficients) and $F_j(s)$ has constant coefficient
$0$ for $j \in [M]$, all $f_j, F_j$ quadratic in $s = (s_1, \sigma(s_1), m, \sigma(m))$.

With the Section 4.4 optimisation ($\lambda$ even, $\lambda/2$ garbage polynomials):

```
P: g_1..g_{λ/2} ← {x ∈ R_q : x_0 = x_{d/2} = 0};  t_g := B_g s2 + g;  send t_g
V: Γ = (γ_{i,j}) ← Z_q^{λ × M}
P: for i ∈ [λ/2]:  a^{(i)} := Σ_j γ_{2i−1,j} F_j(s),  b^{(i)} := Σ_j γ_{2i,j} F_j(s)
                   h_i := g_i + Tr(a^{(i)}) + X^{d/2} Tr(b^{(i)})                 -- Eq. 40
   send h;  run Π_many on (f_1..f_N, f_{N+1}..f_{N+λ/2}) where
   f_{N+i}(s, g) := g_i + Tr(Σ_j γ_{2i−1,j} F_j)(s) + X^{d/2} Tr(Σ_j γ_{2i,j} F_j)(s) − h_i   -- Eq. 41
V: accept iff Π_many verifies and h_{i,0} = h_{i,d/2} = 0 for all i
```

$\mathrm{Tr}$ of a quadratic function (Lemma 4.8): with $U$ the permutation matrix with
$\sigma(s) = U s$ on the extended witness,
```math
\mathrm{Tr}(f)(x) = x^{\mathsf T}\tfrac{R_2 + U^{\mathsf T}\sigma(R_2)U}{2}\, x
 + \tfrac{r_1^{\mathsf T} + \sigma(r_1^{\mathsf T})U}{2}\, x + \tfrac{r_0 + \sigma(r_0)}{2}.
```
In LaZer's interleaved layout $U$ swaps each pair $(2i, 2i+1)$: on a sparse matrix, entry
$(r, c)$ with polynomial $p$ goes to $(r \oplus 1, c \oplus 1)$ with $\sigma(p)$, re-sorted and kept
upper triangular (`lnp-quad-eval.c:_shuffleauto2x2submatssparse`, `_shuffleautovecsparse`;
the case $(r, c) = (2i, 2i+1)$ maps to itself with $\sigma$ applied). The final quadratic
equation $f_{N+i}$ has an extra linear term $+1$ at the index of $g_i$ in the witness (the $g_i$
are appended to $m$, hence to the interleaved vector, at index $2(m_1 + \ell_{\text{before } g} + i)$)
and $r_0 \mathrel{-}= h_i$.

Theorem 4.5: soundness error $2/|C| + q_1^{-d/2} + q_1^{-\lambda}$; the $q_1^{-\lambda}$ term
requires the $\lambda$ rows of $\Gamma$ to be independent uniform challenges. **LaZer (reading)
does not achieve this in the toolbox: see §10.1.** Simulatability is under
Extended-MLWE$_{n+\ell+\lambda+1,\ m_2-n-\ell-\lambda-1}$ in the paper's Fig. 8 count; with the
Section 4.4 halving only $\lambda/2$ garbage slots are committed, and LaZer's simulatability
check accordingly uses $m_2 - n - \ell - \lambda/2 - (\text{range-proof slots}) - 2$ (§5.2, step 10).

Standalone `lnp-quad-eval.c` (reading) zeroes only coefficient $0$ of each $g_i$ and checks only
coefficient $0$ of $h_i$ although it builds both $\mathrm{Tr}$ and $X^{d/2}\mathrm{Tr}$ terms; the
$X^{d/2}$ term is then unchecked. The toolbox copy zeroes and checks both $0$ and $d/2$. **Port:**
always both.

### 3.6 The toolbox: Fig. 10, Sections 5.1–5.4

Inputs (paper Eqs. 50–54), all over the ABDLOP witness $(s_1, m)$ and its $\sigma$-image:

| Statement | Paper | LaZer name | LaZer inputs |
|---|---|---|---|
| quadratic equations in $R_q$ | (50) $f_i(s) = 0$, $i \in [\rho]$ | quadeqs, $N$ | `R2[], r1[], r0[]` |
| vanishing constant coefficients | (51) $\tilde F_i(s) = 0$, $i \in [\rho_{\mathrm{eval}}]$ | evaleqs, $M$ | `R2prime[], r1prime[], r0prime[]` |
| approximate $\ell_\infty$ | (52) $\|D_i s - u_i\|_\infty \le \beta_i^{(d)}$ | arp, one block of $n'$ rows | `Ds (n' × m1), Dm (n' × l), u (n')` |
| exact $\ell_2$ | (53) $\|E_i s - v_i\| \le \beta_i^{(e)}$, $i \in [v_e]$ | l2, $Z$ blocks of $n_i$ rows | `Es[i], Em[i], v[i]`, bounds `l2Bsqr[i]` $= \beta_i^2$ |
| binary | (54) $E_{\mathrm{bin}} s - v_{\mathrm{bin}} \in \{0,1\}^{k_{\mathrm{bin}} d}$ | bin, $n_{\mathrm{bin}}$ rows | `Ps (nbin × m1), Pm (nbin × l), f (nbin)` |

(LaZer's convention is $+v$, $+u$, $+f$ where the paper writes $-v_i$, $-u_i$, $-v_{\mathrm{bin}}$.)

**Reduction (Section 5.2).** For each exact block $i$ the prover appends to the Ajtai part the binary
decomposition $x_i$ of $(\beta_i^{(e)})^2 - \|E_i s - v_i\|^2 \ge 0$; LaZer calls the vector of these
$Z$ polynomials $\upsilon$ and stores it as the last $Z$ entries of `s1` (so `tbox.m1` $= m_1 + Z$).
LaZer's `int_binexp` writes the binary expansion into the $\lceil\log_2 q\rceil$ low coefficients
of one polynomial, and the "powers of two" vector $p_i$ contains $2^j$ exactly for
$2^j \le \beta_i^2$ (so $\langle p_i, x_i\rangle < 2\beta_i^2$; the paper uses length
$2\log\beta_i$). Then, with $x' := (x \,\|\, E_{\mathrm{bin}} s - v_{\mathrm{bin}})$:

- (58) $\langle x', x' - \vec 1\rangle = 0$ over $\mathbb{Z}$ $\Rightarrow$ $x'$ binary (Lemma 5.2).
- (59) $\langle E_i s - v_i, E_i s - v_i\rangle + \langle p_i, x_i\rangle = (\beta_i^{(e)})^2$ over $\mathbb{Z}$.
- Both are proved modulo $q$ as vanishing constant coefficients, and lifted to $\mathbb{Z}$ by an
  approximate range proof on $e^{(e)} := ((E_i s - v_i)_i,\ x')$ showing $\|e^{(e)}\| \le B^{(e)}$
  with $(B^{(e)})^2 + \sqrt{(v_e + k_{\mathrm{bin}}) d}\, B^{(e)} < q$ and
  $2\max_i(\beta_i^{(e)})^2 + (B^{(e)})^2 - 1 < q$ (Theorem 5.3). LaZer's checks are
  $q > B_{\mathrm{arp}}^2 + B_{\mathrm{arp}}\sqrt{n_{\mathrm{bin}} d}$, $q > B_{\mathrm{arp}}^2 + B_{\mathrm{arp}}\sqrt d$,
  and $q > 3\beta_i^2 + B_{\mathrm{arp}}^2$ per block, with $B_{\mathrm{arp}} = 2\sqrt{256/26}\, t\, s^{(e)}$
  and $t = \sqrt{1 + \ln 2} \approx 1.30$ (`lnp-tbox-codegen.sage:334-352`; the paper uses
  $t = 1.64$ for the same role in Theorem 5.3 — note the discrepancy, use the paper's).
- The approximate statement (52) gets its own range proof on $e^{(d)} := (D s - u)$.

**Approximate range proof (Fig. 9, Section 5.1) as used in Fig. 10.** For $x \in \{e, d\}$:

```
P: b^{(x)} ← {−1, 1}  (a constant polynomial);  y^{(x)} ← D_{s^{(x)}}^{256/d}
   t^{(x)} := B^{(x)} s2 + y^{(x)};   t_b := b_bᵀ s2 + b   (b packs both signs, §5.3: b = b^{(e)} + X^{d/2} b^{(d)})
   send (t^{(e)}, t^{(d)}, t_b)
V: R^{(x)} ← Bin_1^{256 × dim(e^{(x)})}
P: z⃗^{(x)} := b^{(x)} R^{(x)} e⃗^{(x)} + y⃗^{(x)}  (as 256-dim integer vectors);  Rej_0 on (z⃗^{(x)}, b^{(x)} R^{(x)} e⃗^{(x)});  send z⃗^{(x)}
V: ‖z⃗^{(e)}‖ ≤ t √256 s^{(e)}  (LaZer: ‖z3‖² ≤ Bz3sqr = ⌊(1.64 · 16 · s3)²⌋)
   ‖z⃗^{(d)}‖∞ ≤ 14 s^{(d)}      (LaZer: ‖z4‖∞ ≤ Bz4 = ⌊16 · s4⌋)
```

The equations that tie everything together (paper Eqs. 62–69) are all "constant coefficient
vanishes" statements over the extended witness $s^* = (s_2;\ (s_1, x);\ (m, y^{(e)}, y^{(d)}, b))$
plus two quadratic equations:

| Family | Equation(s) | Count |
|---|---|---|
| sign is $\pm1$ | $(b^{(x)} - 1)(b^{(x)} + 1) = 0$ in $R_q$ | 2 (quadratic, all coefficients) |
| sign is an integer | $T(X^j, b^{(x)})_0 = 0$ for $j = 1..d-1$ | $2(d-1)$ |
| binary ($x'$) | $T(x', x' - \vec 1)_0 = 0$ | 1 (LaZer: 1 for $\upsilon$ and 1 for the user's binary block) |
| exact $\ell_2$ block $i$ | $T(E_i s - v_i, E_i s - v_i)_0 + T(p_i, x_i)_0 - \beta_i^2 = 0$ | $v_e = Z$ |
| projection $e$ | $z^{(e)}_j - T(b^{(e)} r^{(e)}_j, e^{(e)})_0 - y^{(e)}_j = 0$, $j = 1..256$ | 256 |
| projection $d$ | $z^{(d)}_j - T(b^{(d)} r^{(d)}_j, e^{(d)})_0 - y^{(d)}_j = 0$ | 256 |
| user's | $\tilde F_i(s) = 0$ | $M$ |

Here $r^{(x)}_j$ is row $j$ of $R^{(x)}$ read as $\dim(e^{(x)})/d$ polynomials, and $y^{(x)}_j$
denotes coefficient $j$ of the vector $y^{(x)}$. All $M + 2(d-1) + 2 + Z + 512$ evaluation
equations and the $N + 2$ quadratic equations are handed to $\Pi_{\mathrm{eval}}$ of §3.5.

**Packed signs (Section 5.3).** One BDLOP slot holds $b = b^{(e)} + X^{d/2} b^{(d)}$;
$b^{(e)} = 2^{-1}(b + \sigma(b))$, $b^{(d)} = 2^{-1}(X^{d/2} b + \sigma(X^{d/2} b))$. LaZer's two
quadratic equations (`lnp-tbox.c:520-580`), in the interleaved index $i_\beta$ of $b$:
$(b^{(e)})^2 - 1 = \tfrac14 b^2 + \tfrac12 b\sigma(b) + \tfrac14\sigma(b)^2 - 1$ and
$(b^{(d)})^2 - 1 = -\tfrac14 b^2 + \tfrac12 b\sigma(b) - \tfrac14\sigma(b)^2 - 1$, i.e. sparse
$R_2$ entries $(i_\beta, i_\beta), (i_\beta, i_\beta+1), (i_\beta+1, i_\beta+1)$ equal to
$(\tfrac14, \tfrac12, \tfrac14)$ resp. $(-\tfrac14, \tfrac12, -\tfrac14)$ and $r_0 = -1$. The
"sign is an integer" equations are the linear forms $r_1[i_\beta] = r_1[i_\beta+1] = \tfrac12 X^j$
(for $b^{(e)}$) and $r_1[i_\beta] = \mp\tfrac12 X^{j+d/2}$, $r_1[i_\beta+1] = \pm\tfrac12 X^{j+d/2}$
with the negacyclic wrap (for $b^{(d)}$), `lnp-tbox.c:__schwartz_zippel_accumulate_beta3/4`.

**LaZer's witness layout for the toolbox (normative for compat mode).** With
$\ell_{\mathrm{off}} := [n_{\mathrm{ex}} > 0]\cdot 256/d + [n' > 0]\cdot 256/d$:

```
s1  = (s1_ [m1], upsilon [Z])                                    -- Ajtai part, length m1 + Z
m   = (m_ [l], y3 [256/d if nex>0], y4 [256/d if n'>0], beta [1], g [λ/2], t [1])   -- BDLOP part
tB  = (tB_, ty3, ty4, tbeta, tg, t)    -- same order;  lext = loff + 1 + λ/2 + 1
interleaved indices:  i_{s1,j} = 2j;  i_{υ,j} = 2(m1 + j);  i_{m,j} = 2(m1 + Z + j);
                      i_{y3,j} = 2(m1 + Z + l + j);  i_{y4,j} = 2(m1 + Z + l + 256/d·[nex>0] + j);
                      i_β = 2(m1 + Z + l + loff);  i_{g,j} = i_β + 2 + 2j;   (+1 for the σ-image)
```

`nex = nbin + Σ_i n_i + Z` is the length of $e^{(e)}$ in polynomials
(order: binary block, then the $Z$ exact blocks, then $\upsilon$); `nprime` $= n'$. The user's
equations are given in the index space $2(m_1 + \ell)$ WITHOUT $\upsilon$ and are scattered
into the internal space by shifting indices $\ge 2m_1$ by $2Z$ (`lnp.c:_scatter_smat`).
LaZer's parameter generator always reserves both `y3` and `y4` slots
(`lext = 2·256/d + 1 + λ/2 + 1`), and the C code's $\beta$ offset assumes both are present, so in
practice LaZer requires both an exact/binary block and an ARP block. **Port:** derive
$\ell_{\mathrm{ext}}$ from the blocks actually present and support each independently.

### 3.7 Fiat–Shamir transcript (Appendix B.3 of the paper; LaZer's concrete order)

Paper (Fig. B.3, p. 74–77): $a_1 = (t_A, t^{(e)})$, $R^{(e)} \leftarrow \mathrm{RO}_1(pp, x, a_1)$;
$a_2 = (\vec z^{(e)}, t_g)$, $\Gamma \leftarrow \mathrm{RO}_2(pp, x, a_1, a_2)$; $a_3 = (h_i)_i$,
$\mu \leftarrow \mathrm{RO}_3(\dots, a_3)$; $a_4 = (t, w, v)$, $c \leftarrow \mathrm{RO}_4(\dots, a_4)$;
$a_5 = (z_1, z_2)$; proof $= (a_1, \dots, a_5)$ with $w, v$ recomputed by the verifier. The
knowledge-soundness proof (Theorem B.7) is for this order.
Jali keeps the Fiat–Shamir transform, so its proofs are extracted by rewinding and are not
claimed to be online (straight-line) extractable; the PCS paper's post-quantum instantiation,
which assumes a multi-theorem online-extractable argument, needs updating when it adopts Jali
(see `jali/docs/design-notes.md`, "Fiat–Shamir, rewinding and online extraction").

LaZer's order (reading of `lnp.c:lnp_prover_prove`, `abdlop.c`, `lnp-tbox.c`, `lnp-quad*.c`),
where `H(x) = SHAKE128(x)` truncated to 32 bytes and `enc(·)` is §3.8:

```
h0 := H(ppseed ‖ [Hq] ‖ [He] ‖ [Hl2] ‖ [Hbin] ‖ [Harp])         -- statement hashes present iff N, M, Z, nbin, n' > 0 (§3.9)
h1 := H(h0 ‖ enc(tA1; log2q − D bits) ‖ enc(tB[0..l); log2q bits) ‖ pad)        -- abdlop_hashcomm; only the l plain BDLOP rows
c34 := H(h1 ‖ [enc(ty3)] ‖ [enc(ty4)] ‖ enc(tbeta) ‖ pad);  R rows i<256 ← Bin1(PRG(c34, dom = i)),  R' rows ← PRG(c34, dom = 256 + i)
h2 := c34                                                        -- z3, z4 are NOT absorbed;  hash0 := h2 is kept
h3 := H(h2 ‖ enc(tg) ‖ pad)
Γ  : per equation family, uniform Z_q values from PRG(h3, dom = family offset)   -- except the 512 projection rows, which use PRG(hash0, …)   (§10.1)
μ  : λ/2 + 2 + N uniform polynomials from PRG(h3, dom = (0 ≪ 32) | (j+1))         -- h_i are NOT absorbed
c  := autostable(PRG(H(h3 ‖ enc(t) ‖ enc(v) ‖ enc(w1; log2m bits) ‖ pad), dom 0))
```

**Port (default mode):** the paper's order is what Theorem B.7 covers, and LaZer's changes to it
have no visible rationale and create the problems of §10.1: absorb $\vec z^{(e)}, \vec z^{(d)}$
and $t_g$ before deriving $\Gamma$; derive $\Gamma$ as one matrix
$\mathbb{Z}_q^{\lambda \times M_{\mathrm{tot}}}$ from that hash; absorb $h$ before $\mu$; use
distinct domain tags for every derivation. Everything else about the transcript (SHAKE128,
32-byte chaining, the encodings, hashing $w_1$ rather than $w$) is LaZer's and is kept. Compat
mode reproduces the LaZer order above bit for bit, so that LaZer-generated honest proofs verify.

### 3.8 Encodings (`coder.c`) — normative for compat mode and the default proof format

Bit stream, least-significant bit of each byte first (`_byte[nbytes] |= (1 << _bit)`,
`_bit = 0..7`). Elements:

- `enc_urandom(v, m, mbits)`: each integer $v_i \in [0, m)$ as its `mbits` low bits, LSB first.
  Vectors and matrices element by element (row-major for matrices; upper triangle only for
  `urandom4diag`). Sparse matrix (`urandom5`): 16-bit little-endian count, then per entry 16-bit
  LE row and column, then the polynomials; sparse vector (`urandom6`): 16-bit LE count, 16-bit LE
  indices, polynomials. Decoding rejects a value $\ge m$.
- `enc_grandom(v, log2o)` for a centred Gaussian coefficient $z$ with $\sigma = 1.55 \cdot 2^{\texttt{log2o}}$:
  $a\sigma := 2^{\texttt{log2o}+1}$; $z_0 := z \bmod a\sigma \in [-a\sigma/2, a\sigma/2)$;
  $z_1 := (z - z_0)/a\sigma$; write $z_1$ in unary as $n$ ones followed by a zero with
  $n = -2z_1$ for $z_1 \le 0$ and $n = 2z_1 - 1$ for $z_1 > 0$; then $z_0$ in two's complement,
  `log2o + 1` bits, LSB first. About $2.57 + \log_2\sigma$ bits per coefficient (paper Section 6.1).
- `enc_ghint(h)`: $0 \mapsto$ `00`, $1 \mapsto$ `01` (bit0 = 0, bit1 = 1), $-1 \mapsto$ `10`,
  $k \ge 2 \mapsto$ `11` + $(2k-4)$ zeros + `1`, $k \le -2 \mapsto$ `11` + $(2|k|-3)$ zeros + `1`.
  (Decoder: after `11`, count $j$ zeros before the next one; even $j \mapsto (j+4)/2$, odd
  $j \mapsto -(j+3)/2$.) This is the prefix-free code of the paper's Table 3.
- `enc_end`: one `1` bit then zeros to the byte boundary; the decoder checks exactly this.

**Proof byte layout** (`lnp.c:_lnp_tbox_encproof`), in order:
`tB` (all $\ell + \ell_{\mathrm{ext}}$ polynomials, `log2q` bits/coeff, values in $[0,q)$),
`h` ($\lambda/2$ polynomials, `log2q` bits), `tA1` (`log2q − D` bits), `c` (all $d$ coefficients,
`log2omega` bits each, value $c_i + \omega \in [0, 2\omega]$), `hint` (ghint code), `z1`
(grandom, `log2stdev1`), `z21` (grandom, `log2stdev2`), `z3` (grandom, `log2stdev3`), `z4`
(grandom, `log2stdev4`), `end`. `prooflen` in the parameter set is the size in bytes
(17 800 for `tbox_params1`). Hash inputs (§3.7) use the same element encodings with their own
`end` padding; `abdlop_hashcomm` absorbs a fixed length
$\lceil (n d(\log_2 q - D) + \ell d \log_2 q)/8\rceil + 1$ bytes, which equals the encoded length
for $d \in \{64, 128\}$.

### 3.9 Statement hashing (`lnp.c:_lnp_hash_statement_*`)

`Hq` = SHAKE128 over the concatenation, equation by equation, of
`enc5(R2_i) ‖ enc6(r1_i) ‖ enc2(r0_i) ‖ end` (each present component, polynomials with `log2q`
bits after reduction to $[0, q)$); `He` likewise for the evaluation equations; `Hl2` over
`enc4(Es_i) ‖ enc4(Em_i) ‖ enc3(v_i) ‖ end` for $i < Z$; `Hbin` over `enc4(Ps) ‖ enc4(Pm) ‖ enc3(f) ‖ end`;
`Harp` over `enc4(Ds) ‖ enc4(Dm) ‖ enc3(u) ‖ end`. The linear front end hashes only `Harp`
(its selector tables are compile-time constants). **Port:** hash every public input, including
dimensions and the parameter-set identifier, with length prefixes, in default mode.

---

## 4. Randomness, hashing and samplers

### 4.1 Hash and PRG

- **Hash** `H`: SHAKE128 (FIPS 202, domain byte `0x1F`; `shake128.c` is a standard Keccak), always
  truncated to 32 bytes and chained: `hash := H(hash ‖ payload)`. Rust: `sha3::Shake128`.
- **PRG** `PRG(seed: [u8; 32], dom: u64)`: LaZer's default (`config.h`) is AES-256-CTR with key
  `seed` and initial counter block `LE64(dom) ‖ 0^8`, incremented as a big-endian 128-bit integer
  per block (`aes256ctr.c: incbe`). Rust: `ctr::Ctr128BE<aes::Aes256>` keystream with that block
  as IV reproduces the stream (partial-block caching is automatic). The alternative
  (`RNG_SHAKE128`) absorbs `seed ‖ LE64(dom)` and squeezes. The port implements both behind a
  trait and uses AES-256-CTR by default (compat with LaZer's checked-in builds).
- **Composite domains.** LaZer builds the 64-bit domain as `(dom32 << 32) | index32` through a
  host-endian union (`dom.h`); the port defines it as this arithmetic expression. Index rules
  (reading of `polyvec.c`, `polymat.c`, `intmat.c`): a vector element $i$ uses `index32 = i + 1`;
  a matrix entry $(i, j)$ uses `i · ncols + j`; an integer matrix row $i$ uses `i · ncols` (one
  stream per row); an integer vector uses the 64-bit domain it is given, unchanged.

### 4.2 Samplers (specification; LaZer's algorithms unless a defect is noted)

**Uniform modulo $m$ with `mbits` $= \lceil\log_2 m\rceil$ (`urandom.c:_urandom_i64`).** Take
`mbits` bits per element from the stream, LSB first (bit $j$ of element $i$ is stream bit
$i\cdot\texttt{mbits} + j$ of the current buffer); reject and redraw if the value is $\ge m$.
LaZer requests $\lceil \texttt{mbits}\cdot \ell/8\rceil$ bytes for the $\ell$ still-missing elements
in each pass, continuing the same stream. Defect: for `mbits` $\ge 60$ LaZer branches to
`_urandom_bnd(0, (m-1)/2)` and returns values in $[0, (m-1)/2]$ only (`urandom.c:15-29`,
marked `XXX`). The port samples the full range for every modulus; compat mode need not
reproduce the defect because no shipped LaZer parameter set has `log2q` $\ge 60$ (largest seen:
51, `anon_cred` P2).

**Uniform in $[lo, hi]$ (`_urandom_bnd`).** Used for $s_2 \leftarrow [-\nu, \nu]^{m_2 d}$: sample the
magnitude range $[0, hi - lo]$ by rejection on the minimal number of bits, then add $lo$.

**$\mathrm{Bin}_k$ (`brandom.c:_brandom`).** Stream of $\lceil 2k\ell/8\rceil$ bytes; element $i$ is
$\sum_{j<k} \mathrm{bit}(ik + j) - \sum_{j<k}\mathrm{bit}(k\ell + ik + j)$. The range-proof matrices
use $k = 1$: row $i$ of $R^{(e)}$ is `_brandom(nex·d, 1, cseed, i)`, row $i$ of $R^{(d)}$ is
`_brandom(nprime·d, 1, cseed, 256 + i)` (§3.7).

**$\sigma$-stable challenge (`intvec.c:_intvec_urandom_autostable`).** $d/2$ values uniform in
$[0, 2\omega]$ (bits $= \lceil\log_2(2\omega+1)\rceil$, rejection), minus $\omega$; coefficient $d/2$
is $0$; $c_{d-i} = -c_i$ for $0 < i < d/2$.

**Discrete Gaussian, $\sigma = 1.55\cdot 2^t$ (`grandom.c`).** Per polynomial (domain as in §4.1),
one stream. First $\lceil t d/8\rceil$ bytes give $d$ uniform values $u_j \in [0, 2^t)$
(bit-packed, LSB first). Then for each $j$: $c := u_j/2^t \in [0,1)$, $k \leftarrow D_{1.55,\,c}$
(a Gaussian on $\mathbb{Z}$ centred at $c$), $z_j := 2^t k - u_j$. Since $z_j/2^t = k - c$ and
$u_j$ is uniform, $z_j$ is distributed as $D_{1.55\cdot 2^t}$ up to the variation of
$\rho_{1.55}(\mathbb{Z} + c)$ in $c$, which is about $2 e^{-2\pi^2 \cdot 1.55^2} \approx 2^{-67}$
relative (Poisson summation; the implementer should compute this constant and state it in the
docs). The base sampler `gaussian155(c)` is Falcon-style: draw a bit $b$; draw $k \ge 0$ from a
half-Gaussian of width $1.55$ by a 128-bit cumulative table (`CDF155[21]`, compared against 16
random bytes, `k` = number of table entries above the random value); set $k := k + 1$ if $b = 1$
else $k := -k$; accept with probability $\exp(-x)$, $x = ((k-c)^2 - (k-b)^2)/(2\cdot 1.55^2)$, via a
Bernoulli-exp test (`BerExp`: 64 random bits for the $2^{-\lfloor x/\ln 2\rfloor}$ part, 53 bits
against $\exp(-r)\cdot 2^{53}$ for the remainder $r$); repeat until accepted. Constants: copy
`CDF155` verbatim (with attribution); replace `exp_small` (an fdlibm polynomial that LaZer uses
outside its designed interval, `grandom.c:37-39`) by Falcon's 63-bit `expm_p63` polynomial or by
`f64::exp` with a documented precision argument.

Defects not to port: (i) `gaussian155` keeps the spare sign bits in a `static` buffer, so outputs
depend on call history and the sampler is not thread-safe; (ii) for $t \ge 24$ LaZer calls a
per-coefficient sampler that re-initialises the stream from the same `(seed, dom)`, so all $d$
coefficients of the polynomial receive the same value (`intvec.c:_intvec_grandom`,
`grandom.c:_grandom_sample`); the `blindsig` P2 set has `log2stdev4 = 29`. The port keeps all
sampler state local, uses one stream per polynomial for every $t$, and takes the top 53 bits of
$u_j$ for $c$ when $t > 53$.

**Signs $b^{(e)}, b^{(d)}$.** One fresh bit each from a dedicated stream (LaZer's bit indexing
skips a bit and reuses one across restarts, `lnp-tbox.c:1615-1640`; harmless, not reproduced).

### 4.3 Rejection sampling (`rejection.c`)

Inputs are exact: $\langle z, v\rangle$ and $\langle v, v\rangle$ (up to about $2^{200}$
for the largest parameters; use a 256-bit signed type), $\sigma^2$ as an exact fraction (for
the width $1.55\cdot 2^t$ it is $961\cdot 4^t/400$), `scM` $= \lfloor M \cdot 2^{128} + \tfrac12\rfloor$,
and $u \leftarrow [0, 2^{128})$ (16 stream bytes, little-endian).
**Correction, 2026-09-28:** this plan first said $\sigma^2$ is an integer from the parameter set,
copying LaZer's `stdevNsq = nint(stdevN^2)`. The sampler draws at the fractional $\sigma^2$, and
rejecting with a rounded one distorts the accepted responses in a witness-dependent way: a
numerical estimate puts the statistical distance at $2^{-20.9}$ to $2^{-20.2}$ per proof for
`tbox_params1` with a witness at its norm bound, almost all from $z_4$ at $t = 8$.

- Standard: reject iff $\texttt{scM}\cdot u > 2^{256}\exp\!\big((\langle v,v\rangle - 2\langle z,v\rangle)/(2\sigma^2)\big)$.
- Bimodal / LaZer-smooth: reject iff $\texttt{scM}\cdot u \cdot \exp(-\langle v,v\rangle/(2\sigma^2))\cosh(\langle z,v\rangle/\sigma^2) > 2^{256}$.
- $\mathrm{Rej}_2$ (paper Fig. 1 right): reject iff $\langle z, v\rangle < 0$, else the standard test
  with $M = \exp(1/(2\gamma^2))$.

LaZer evaluates these with MPFR at 128-bit precision. The port has no MPFR: evaluate
$\exp$ and $\cosh$ in fixed point with at least 128 fractional bits (range-reduce
$x = A/D$ to $x = n\ln 2 + r$, $|r| \le \tfrac12\ln 2$, Taylor series in 256-bit fixed point;
or `dashu-float` at 192 bits, MIT/Apache). At the same $\sigma^2$, decisions agree with LaZer's
except when the two sides are within about $2^{-100}$ relative, which never happens in practice
and does not affect the statistical-distance argument. Because the port uses the exact
$\sigma^2$ and LaZer the rounded one, on the same $u$ they also differ with probability of order
$|\sigma^2 - \mathrm{round}(\sigma^2)|/\sigma^2$ per test; verifying LaZer proofs is unaffected.
Test against `mpmath` at 300 bits (§11).

### 4.4 Determinism and restarts

`prove(seed)` is a pure function of `(pp_seed, statement, witness, seed)`. LaZer expands the
prover seed with SHAKE128 into sub-seeds (`lnp.c:1405-1470`: 64 bytes → `s2` seed and
sub-protocol seed; `lnp-tbox.c:290-297`: 96 bytes → range-proof rejection seed, garbage seed,
final-round seed; `lnp-quad.c:149-152`: mask seed) and increments a domain counter per
attempt. Restart granularity is per round: the range-proof round (`y3, y4, b, z3, z4`) repeats
until its two rejection tests pass, the final round (`y1, y2, c, z1, z2`) repeats until its tests
and the norm bound pass; the commitment and the earlier rounds are kept. Rejected attempts are
never output, so this is sound for the non-interactive prover and lowers the expected work
from $\prod M_i$ global restarts to $M_1 M_2$ plus $M_3 M_4$ round restarts. Adopt. Randomised
proving takes a `CryptoRngCore` and draws the 32-byte seed from it.
**Correction, 2026-09-29:** in Jali, `prove(seed)` is a pure function of
`(pp_seed, statement, witness, context, seed)`: every prover and verifier takes an application
context (`jali/docs/protocol.md#application-context`). Jali also does not use LaZer's fixed
sub-seeds. Apart from the evaluation-proof seed, which the toolbox draws from its own keyed
stream (`jali/docs/encodings.md#secret-key-derivation`), each call derives its secret keys
from the seed and its own inputs (`rand::derive_key`, `jali/docs/protocol.md#seeds`), so one
seed may serve several calls without two different calls sharing randomness, while identical
calls return identical outputs; with a reused seed, zero-knowledge holds only relative to that
equality pattern.
Randomised proving takes a `rand_core` 0.10 `CryptoRng` and draws a fresh seed per call.

---

## 5. Parameters

### 5.1 Inputs of a parameter set

From `lnp-tbox-codegen.sage` (toolbox) and `lin-codegen.sage` (linear front end):

| Input | Meaning |
|---|---|
| `d ∈ {64, 128}` | proof-ring degree |
| `log2q`, optional `log2q1` | target bit sizes of $q$ (and of $q_1$ if $q = q_1 q_2$) |
| `m1`, `l` | lengths of $s_1$ (Ajtai) and $m$ (BDLOP) in $R_q$ elements, before $\upsilon$ |
| `alpha` | $\|s_1\| \le \alpha$ |
| `nbin` | rows of the binary block |
| `n[]`, `B[]` | rows and $\ell_2$ bounds of the $Z$ exact blocks |
| `nprime`, `Bprime` | rows and $\ell_\infty$ bound of the approximate block |
| `gamma1..gamma4` | rejection-sampling slack factors, defaults $14, 1, 5, 5$ |
| `rejs1..rejs4` | policies, defaults $1, 2, 2, 2$ (standard, LaZer-smooth, bimodal, bimodal) |
| constants | `KAPPA = 128`, `DELTA128 = 1.0044`, `L = 2`, `T = 1.64`, `NADDS = 128`, `nu = 1`, `nbit = 50` |

### 5.2 Derivation (port of `lnp-tbox-codegen.sage`, in this order)

1. $\lambda := 2\lceil 128/(2\log_2 q_1)\rceil$ (with $q_1 = q$ for one prime). Even by construction.
2. Challenge set: $d = 64 \Rightarrow (\omega, \eta, |C|) = (8, 140, 2^{129})$; $d = 128 \Rightarrow (2, 59, 2^{147})$.
   `log2omega` $= \lceil\log_2(2\omega+1)\rceil$.
3. $Z := |B|$; $n_{\mathrm{ex}} := \sum_i n_i + n_{\mathrm{bin}} + Z$; $\alpha_3 := \sqrt{\sum_i B_i^2 + (n_{\mathrm{bin}} + Z)d}$;
   $\alpha_4 := \sqrt{n'd}\,B'$ (approximate block present iff $n' > 0$ and $B' > 0$).
   **Correction, 2026-09-28:** this plan first said $\alpha_4 := B'$, copying LaZer. LNP22 Fig. 10
   needs a Euclidean bound $\alpha^{(d)} \ge \|e^{(d)}\|$, and $B'$ bounds single coefficients.
4. $s_1 := \mathrm{round}(\gamma_1 \eta\sqrt{\alpha^2 + Zd})$, $s_3 := \mathrm{round}(\gamma_3\sqrt{337}\alpha_3)$,
   $s_4 := \mathrm{round}(\gamma_4\sqrt{337}\alpha_4)$, where `round` picks the nearest
   $1.55\cdot 2^k$; recompute each $\gamma_i$ from the rounded value.
5. $k_{\mathrm{MLWE}}$ := smallest MLWE rank with $\delta \le 1.0044$ for secrets uniform in
   $[-\nu, \nu]$ (binary search; LaZer calls the Albrecht–Player–Scott estimator bundled as
   `third_party/estimator.py` with the enumeration and sieving cost models and takes the
   maximum $\delta_0$ over `usvp`, `dec`, `dual`). §5.4 on how the port obtains this number.
6. $n$ (`kmsis`) := smallest with $\delta_{\mathrm{MSIS}}(\mathrm{Bound}, n, d, 2^{\log_2 q}) < 1.0044$
   and $\mathrm{Bound} < 2^{\log_2 q}$, where for each candidate
   $m_2 := k_{\mathrm{MLWE}} + n + \ell + \lambda/2 + 256/d + 1 + [\text{approx}]\cdot 256/d + 1$,
   $s_2 := \mathrm{round}(\gamma_2\eta\nu\sqrt{m_2 d})$ (recompute $\gamma_2$),
   $\mathrm{Bound}_\ast := s_2\sqrt{2 m_2 d} + \eta 2^{D-1}\sqrt{nd} + \gamma\sqrt{nd}/2$,
   $B_1 := 2 s_1\sqrt{2(m_1 + Z)d}$, $B_2 := 2\,\mathrm{Bound}_\ast$,
   $\mathrm{Bound} := 4\eta\sqrt{B_1^2 + B_2^2}$, with $D = \gamma = 0$ at this stage, and
   $\delta_{\mathrm{MSIS}}(\beta, n, d, q) := 2^{(\log_2\beta)^2/(4 n d \log_2 q)}$.
7. $\gamma$: start at $2^{\log_2 q}$ and halve while MSIS stays hard. Then choose the primes:
   $q_1$ := smallest prime $\equiv 5 \pmod 8$ at or above $2^{\log_2 q_1}$ found by stepping in
   multiples of $8$; $q_2$ likewise from $\lceil 2^{\log_2 q}/(8 q_1)\rceil\cdot 8 + 5$; $q := q_1$ or
   $q_1 q_2$; then $\gamma$ := an even divisor of $q - 1$ in $(4\gamma/5, \gamma]$ (retry with the
   next $q_1$ if none exists); $m := (q-1)/\gamma$.
8. $D$: largest with MSIS hard, $\mathrm{Bound} < 2^{\log_2 q}$ and $2^{D-1}\omega d < \gamma$.
9. $M_1 := \exp(\sqrt{2\cdot 129/\log_2 e}/\gamma_1 + 1/(2\gamma_1^2))$, $M_2 := \exp(1/(2\gamma_2^2))$
   (for `rejs2 = 2`; standard formula for `rejs2 = 1`), $M_3, M_4 := \exp(1/(2\gamma_{3,4}^2))$;
   expected repetitions $M_1 M_2 M_3 (M_4)$.
10. Checks. Completeness: $(m_1 + Z)d \ge 5\cdot 128$ and $m_2 d \ge 5\cdot 128$.
    Simulatability: $k_{\mathrm{MLWE}} = m_2 - n - \ell - \lambda/2 - 256/d - [\text{approx}]256/d - 2 \ge 0$.
    Knowledge soundness with $B_{\mathrm{arp}} := 2\sqrt{256/26}\,t\,s_3$ (LaZer: $t = \sqrt{1+\ln 2}$;
    the port should use the paper's $t = 1.64$ and also report LaZer's value):
    $q \ge 41\, n_{\mathrm{ex}} d\, B_{\mathrm{arp}}$; $q > B_{\mathrm{arp}}^2 + B_{\mathrm{arp}}\sqrt{n_{\mathrm{bin}} d}$;
    $q > B_{\mathrm{arp}}^2 + B_{\mathrm{arp}}\sqrt d$; $q > 3B_i^2 + B_{\mathrm{arp}}^2$ for each exact block.
    Knowledge error $\le 1/(2|C|) + q_1^{-d/2} + q_1^{-\lambda} + 2^{-128} + 2^{-256}$ (valid only with
    independent $\Gamma$ rows, §10.1).
11. Proof size in bits (LaZer's formula, with $\lceil\log q\rceil$ written $\log q$):
    $n d(\log q - D) + (\ell + 256/d + 1 + [\text{approx}]256/d + \lambda + 1) d \log q$
    $+ \lceil\log_2(2\omega+1)\rceil d + (m_1 + Z) d\lceil\log_2 s_1 + 2.5\rceil + (m_2 - n) d\lceil\log_2 s_2 + 2.5\rceil$
    $+ 256\lceil\log_2 s_3 + 2.5\rceil + [\text{approx}]\,256\lceil\log_2 s_4 + 2.5\rceil + 2.25\, n d$.
    `prooflen` $= \lceil \text{bits}/8\rceil$. This is an estimate of the variable-length encoding;
    the actual encoded length varies slightly per proof (LaZer allocates $1.2\times$).
12. Stored constants: `q, qminus1, m, mby2, gamma, gammaby2, pow2D, pow2Dby2, Bsq = ⌊Bound_∗²⌋,
    scM1..4 = round(M_i · 2^128), stdev1sq..4sq = round(s_i²), inv2, inv4 (centred mod q), n[],
    Bz3sqr = ⌊(1.64 · 16 · s3)²⌋, Bz4 = ⌊16 · s4⌋, l2Bsq_i = round(B_i²), Pmodq, Ppmodq_i`, the
    RNS prime list (§6.2), and the three ABDLOP views of the same set: `tbox`
    ($\ell$, $\ell_{\mathrm{ext}} = 2\cdot 256/d + 1 + \lambda/2 + 1$), `quad_eval`
    ($\ell + 2\cdot 256/d + 1$, $\lambda/2 + 1$) and `quad_many` ($\ell + 2\cdot 256/d + 1 + \lambda/2$, $1$).
    **Correction, 2026-09-28:** LaZer stores `stdevNsq` rounded; the port does not, and its
    rejection tests use the exact $s_i^2$ (§4.3).

The linear front end's driver (`lin-codegen.sage`) adds: the statement modulus $p$ and degree
$d'$, $k := d'/d$, the witness partition with per-block $\ell_2$ bound or "binary" flag, an
optional $\ell_\infty$ bound $S$ on the witness, and computes
$\log_2 q := \lceil\log_2(2(1+\psi)(P + n_{\mathrm{cols}} P d' S) + 1)\rceil$ with $P = (p-1)/2$ and a
hard-coded slack $\psi = 3358$; `nprime` $:= k\cdot n_{\mathrm{rows}}$, $B' := (P + n_{\mathrm{cols}} P d' S)/p$;
`nbin` $:= k\cdot$(binary slots), `n[i]` $:= k\cdot$(rows of block $i$); then it searches the
Ajtai/BDLOP split: start with the whole witness in $s_1$, repeatedly move the block with the
largest $\ell_2$ bound to $m$ while the proof size decreases and all checks pass. The paper's
extraction bound for the $\ell_\infty$ range proof is $B^{(d)} = 28\sqrt{337}\gamma^{(d)}\alpha^{(d)}
= 28 s^{(d)}$ (Theorem 5.3), twice its verifier bound $14 s^{(d)}$. LaZer's verifier accepts
$16 s_4$, so with that verifier the extraction bound is $32 s_4$; LaZer prints
$\psi = 2\gamma_4\sqrt{377\cdot 256}$ (a typo for 337), which matches $32 s_4$, and uses 3358 in the
front end. Soundness of the lifting needs only $q > F + p\cdot 2\,\mathrm{Bz4}$, because
$f - p\,y$ is a multiple of $q$ that is smaller than $q$ in absolute value; a check of the form
$q > 2(F + 28 s_4 p)$ implies it. (A 2026-09-28 audit briefly flagged the 28 as unsound for a
$16 s_4$ verifier; it is not, because of the factor 2.)

### 5.3 Reference parameter sets

`tests/lnp-tbox-params1.sage` → (regenerated here, identical to the checked-in header):

| Symbol | Value |
|---|---|
| $d$, $q$, $\lceil\log q\rceil$ | 64, 1099511627917 (prime, $\equiv 5 \bmod 8$), 41 |
| RNS primes | 2 (of the `d64` table) |
| $\gamma$, $m = (q-1)/\gamma$, $D$ | 65202, 16863158, 7 |
| $n$ (`kmsis`), $m_1 + Z$, $m_2$, $\ell$, $\ell_{\mathrm{ext}}$ | 12, 12 (= 10 + 2), 56, 2, 16 |
| $\lambda$, $\nu$, $\omega$, `log2omega`, $\eta$ | 4, 1, 8, 5, 140 |
| $s_1, s_2, s_3, s_4$ | $1.55\cdot 2^{16}, 1.55\cdot 2^{12}, 1.55\cdot 2^{10}, 1.55\cdot 2^{8}$ |
| `rejs` | 1, 2, 2, 2 |
| $n_{\mathrm{bin}}$, $n$, $B$, $n'$, $B'$, $n_{\mathrm{ex}}$ | 2, [2, 1], [$\sqrt{128}, \sqrt{64}$], 2, 4, 7 |
| `Bsq`, `Bz3sqr`, `Bz4` | 3487433255883, 1734566565, 6348 |
| `prooflen` | 17 800 bytes |

Other shipped sets to reproduce (values from the generated headers): Kyber-1024 secret-key
proof (`python/kyber1024`: $d = 64$, $\lceil\log q\rceil = 37$, $m_1 + Z = 33$, $m_2 = 54$, $n = 19$,
$n' = 16$, 19 726 bytes), `anon_cred` P1 (42 bits, 20 186 bytes) and P2 (51 bits, 3 RNS primes,
$m_1 + Z = 50$, $m_2 = 64$, 30 064 bytes), `blindsig` P1/P2. The paper's Fig. 12 set
($q = 2^{32} - 99$, $d = 128$, 14.4 KB) uses $\lambda = 4$, $n = 9$, $m_1 = 8$, $m_2 = 25$, $D = 9$,
$\gamma = 131052$; the transcription agent could not reproduce its 14.4 KB from the printed
formula and found one Theorem 5.3 inequality violated by about 13 % under a literal reading;
treat Fig. 12 as illustrative and regenerate with the tool.

### 5.4 Hardness estimation in the port

- MSIS: the closed form of step 6, in Rust (`f64` suffices).
- MLWE: needs a lattice estimator. Keep this in the Sage/Python tool (`tools/params/`, port of
  `codegen.sage` + `lnp-tbox-codegen.sage` + `lin-codegen.sage`), replacing the bundled old
  estimator by the current `lattice-estimator` and recording its commit and cost models in the
  output. The Rust `params` module takes $k_{\mathrm{MLWE}}$ and the reported $\delta$ as inputs
  with that provenance, re-derives every other quantity, re-checks every inequality, and refuses
  sets that fail. Shipped sets live as JSON in `params/sets/` with the generator command in a
  comment, and are also exposed as Rust constants.
  **Correction, 2026-09-30:** JSON has no comments, and a `TboxParams` holds strings and
  vectors, so no constant. In Jali each shipped set is a function in `params/mod.rs`, not in a
  `sets.rs`: `tbox_params1`, which the original command of `jali/docs/parameters.md` derives
  but for the `log_sigma[3]` it keeps from LaZer, and `kyber1024_d64`, `kyber1024_d128` and
  `demo_d64`, whose documentation names the request from which
  `tools/params/lnp_params.py regenerate` writes the JSON in `src/params/sets/` and its copy
  in `tools/params/sets/`.


---

## 6. Arithmetic layer

### 6.1 Representations

- **Coefficients** are `i128`, centred in $(-q/2, q/2]$ after every reduction. This covers every
  $q$ LaZer's demos use (34–51 bits) and the lifted moduli the credential statements need
  (estimated 60–80 bits, §7.3) with room for unreduced sums. LaZer's multi-limb `int_t` is not
  needed; a `crypto_bigint::U256`/`I256`-style type is used only for squared norms, inner
  products in rejection sampling, and CRT reconstruction.
- **`Poly`**: `Vec<i128>` of length $d$ plus a shared ring handle (`Arc<Ring>`; the ring holds
  $q$, $d$, $\lceil\log q\rceil$, $2^{-1}$, $4^{-1}$ and the RNS/NTT context). Debug assertions
  check ring identity on every binary operation.
- **`PolyNtt`**: the same element in residue-number-system NTT form, `Vec<u64>` of length
  $k\cdot d$ (residues modulo $k$ primes, each in NTT order). Conversions are explicit
  (`to_ntt`, `from_ntt`); no implicit state flag as in LaZer's `poly->crt`. Matrix–vector
  products and quadratic forms accumulate in NTT form and convert once.
- **Containers**: `PolyVec`, `PolyMat` (row-major), `SparsePolyMat` (sorted `(u16 row, u16 col,
  Poly)` with `row ≤ col`, i.e. upper triangular, checked at construction), `SparsePolyVec`,
  `IntVec`/`IntMat` over `i128`. Views by stride are replaced by slices and index helpers; the
  interleaved layout of §3.3 is encoded by a small `Idx` type (`Idx::var(i)`, `Idx::conj(i)`).
  **Correction, 2026-09-29:** Jali had this type but nothing used it, and it was removed;
  equations use the plain indices $2i$ and $2i+1$ (`jali/docs/protocol.md`).

### 6.2 Multiplication: RNS over NTT-friendly primes

$q \equiv 5 \pmod 8$ is not NTT-friendly, so products in $R_q$ are computed exactly over the
integers and reduced: choose primes $p_1 > p_2 > \dots$ with $p_i \equiv 1 \pmod{2d}$ and
$P = \prod p_i > (q-1)^2\, d\cdot \mathrm{NADDS} + 1$ with $\mathrm{NADDS} = 128$ (LaZer's rule,
`codegen.sage: min_P`; it bounds the coefficient of a sum of up to 128 products of unreduced
inputs in $(-q, q)$). Every accumulation of more than `NADDS` products must reduce in between;
the port tracks the count in debug builds.

- LaZer uses 50-bit primes (HEXL's range), 11 per degree in `moduli.h`, roots of unity chosen as
  the smallest primitive $2d$-th root in absolute value, Montgomery form with $R = 2^{64}$.
  The port uses primes just below $2^{62}$ (fewer primes: two suffice up to $q \approx 2^{54}$,
  three up to $2^{85}$ for $d = 128$), generated once by `tools/params/moduli.py` for
  $d \in \{64, 128\}$ (and $256, 512, 1024$ for statement rings) and stored as constants with
  their roots. Multiplication uses `u128` products with Montgomery or Shoup reduction;
  twiddles precomputed in bit-reversed order (Longa–Naehrig style, as in Kyber/Dilithium).
- Forward/inverse NTT are iterative radix-2 over $d \in \{64, 128\}$ (and larger for statement
  rings); the inverse multiplies by $d^{-1}$. Correctness oracle: schoolbook negacyclic product
  in `i128`.
- **Exact CRT** (`from_ntt`): for each coefficient with residues $x_i \in [0, p_i)$ compute
  $c_i := x_i\cdot k_i \bmod p_i$ with $k_i := (P/p_i)^{-1} \bmod p_i$, then
  $X := \sum_i c_i\,(P/p_i) \bmod P$ in a 320-bit integer, centre to $(-P/2, P/2]$, and reduce
  modulo $q$. All integer arithmetic; no floating point. (LaZer's `poly_fromcrt` instead uses the
  identity $X \bmod q = \sum_i c_i\,((P/p_i) \bmod q) - r\,(P \bmod q)$ with
  $r = \mathrm{round}(\sum_i c_i/p_i)$ computed in single-precision `float`, `poly.c:672-747`;
  correct while $|X| \le P/4$, but the port should not depend on `float`.)
- `tfhe-ntt` (Zama) offers prime and "native" negacyclic NTT plans, but it is licensed
  BSD-3-Clause-Clear, which the credential project's dependency policy does not admit; it may be
  used at most as an optional benchmark comparison. The NTT is a few hundred lines; write it.
- SIMD: none in the first version. Keep the NTT in one module with a scalar reference so a
  later `std::arch` (AVX2/NEON) version can be added behind a feature, being the only place
  with `unsafe`.

### 6.3 Operations needed by the protocols (from LaZer's API surface)

Polynomials: add, sub, neg, scalar multiply by $\mathbb{Z}_q$ and by $R_q$, `auto` ($\sigma$),
`tracemap`, `lrot`/`rrot` (multiply by $X^{\pm j}$), `lshift`/`rshift` (multiply/divide by $2^j$),
`mod` (reduce), `redc` (centre), `redp` (to $[0,q)$), `l2sqr`, `linf`, `eq`, `toisoring`/`fromisoring`
(§7.2), `set_coeff`, `binexp` (binary expansion into a polynomial, plus the powers-of-two
vector). Vectors/matrices: `mul` (dense), `mulsparse` (sparse matrix × vector), `dot`, `dot2`
(sparse · dense), `addmul`, `submul`, `scale`, `auto`, `lrot`, `get_row/col/submat` views,
`urandom`/`grandom`/`brandom` fills, `dcompress_*` coefficient-wise. Sparse: `insert`, `sort`,
`scale`, `add`, `lrot`, `auto` with the pair shuffle of §3.5, `is_upperdiag`.

### 6.4 Cost model (to guide profiling, not a promise)

Dominant prover costs per attempt: $A_1 y_1$, $A_2' y_{2,1}$, $B' s_{2,1}$ (dense
$n\times m_1$, $n\times(m_2-n)$, $(\ell+\ell_{\mathrm{ext}})\times(m_2-n)$ products, each $O(k d\log d)$
per NTT plus pointwise work); the quadratic form $s^{\mathsf T}R_2 y$ and $y^{\mathsf T}R_2 y$
(one product per nonzero of $R_2$; the toolbox's $R_2$ has $O((m_1+\ell)^2)$ nonzeros from the
binary and $\ell_2$ equations); the Schwartz–Zippel folding (scalar-times-sparse, cheap); the
range-proof matrix products $R e$ (integer, $256\times n_{\mathrm{ex}} d$ ternary matrix) and,
in the verifier and prover, $V R$ ($\lambda \times 256$ times $256\times n_{\mathrm{ex}}d$) followed
by $(VR)\cdot E_s$ etc. ($\lambda n_{\mathrm{ex}} m_1$ polynomial products). LaZer's reported
prove/verify times are not available here (nothing was run); measure early (§12).

---

## 7. Statement layers

Three layers, from low to high. The two lower ones exist in LaZer; the third is new.

### 7.1 `lnp`: the generic statement object (port of `lnp.c`, fixed)

```rust
pub struct Prover  { /* params, pp_seed, A1, A2', B', statement, witness (zeroized on drop) */ }
pub struct Verifier{ /* params, pp_seed, A1, A2', B', statement */ }

impl Prover {
    pub fn new(pp_seed: [u8; 32], params: Arc<TboxParams>) -> Self;
    pub fn set_witness(&mut self, s1: &PolyVec, m: &PolyVec) -> Result<(), Error>;
    pub fn set_quadratic_eqs(&mut self, eqs: &[QuadEq]) -> Result<(), Error>;   // f_i(s) = 0 in R_q
    pub fn set_eval_eqs(&mut self, eqs: &[QuadEq]) -> Result<(), Error>;        // const coeff of F_i(s) = 0
    pub fn set_l2_blocks(&mut self, blocks: &[L2Block]) -> Result<(), Error>;   // ||E_s s1 + E_m m + v||_2 <= B_i
    pub fn set_binary_block(&mut self, block: &BinBlock) -> Result<(), Error>;  // P_s s1 + P_m m + f in {0,1}
    pub fn set_arp_block(&mut self, block: &ArpBlock) -> Result<(), Error>;     // ||D_s s1 + D_m m + u||_inf <= B'
    pub fn prove(&mut self, rng: &mut impl CryptoRngCore) -> Result<Vec<u8>, Error>;
    pub fn prove_with_seed(&mut self, seed: [u8; 32]) -> Result<Vec<u8>, Error>;
}
impl Verifier { /* same setters; */ pub fn verify(&self, proof: &[u8]) -> Result<(), Error>; }

pub struct QuadEq { pub r2: SparsePolyMat, pub r1: SparsePolyVec, pub r0: Option<Poly> }
pub struct L2Block { pub e_s: Option<PolyMat>, pub e_m: Option<PolyMat>, pub v: Option<PolyVec>, pub bound_sq: U256 }
pub struct BinBlock{ pub p_s: Option<PolyMat>, pub p_m: Option<PolyMat>, pub f: Option<PolyVec> }
pub struct ArpBlock{ pub d_s: Option<PolyMat>, pub d_m: Option<PolyMat>, pub u: Option<PolyVec> }
```

**Correction, 2026-09-29:** in Jali, `prove`, `prove_bytes` and their `_with_seed` variants take
an application `context: &[u8]` before the RNG or seed, and `verify` and `verify_bytes` take it
after the proof; a proof verifies only under the context it was made with
(`jali/docs/protocol.md#application-context`). The sketch differs from the code in other
details too (typed proofs next to their byte encodings, `&self` receivers, fallible
constructors); `jali/src/lnp.rs` is authoritative.

Conventions: equations are indexed from $0$ (LaZer's `lnp.c` mixes an offset convention with
`lnp-tbox.c`'s zero-based one, §10.3); `QuadEq` uses the user index space $2(m_1 + \ell)$ of
§3.3 (plain indices $2i$, $2i+1$ in Jali, which has no `Idx` type); the object inserts
$\upsilon$ (computed from the $\ell_2$ blocks once both witness and blocks are set,
`lnp.c:_lnp_prover_set_witness_upsilon`), scatters indices, builds the toolbox equations of
§3.6, runs the protocol, and encodes with §3.8. The prover checks its own statement before
proving (LaZer does this only with `ASSERT` enabled) and returns an error instead of producing
an invalid proof. The verifier reads a proof with the strict decoder (values in range, exact
padding, exact length) before any arithmetic.

### 7.2 `lin`: linear relations over another ring (port of `lin-proofs.c`)

Statement: $A w + t = 0$ over $R_{p,d'}$ with $A \in R_{p,d'}^{r\times c}$, witness
$w \in R_{p,d'}^{c}$ partitioned into blocks that are either $\ell_2$-bounded or binary.
Parameters from the driver of §5.2 (`LinParams { tbox, d', p, p_inv_mod_q, k, s1_indices,
m_indices, bin_selector, l2_selectors }`).

**Degree lowering.** $R' = \mathbb{Z}_q[X]/(X^{kd}+1)$ is a free module of rank $k$ over
$R = \mathbb{Z}_q[Y]/(Y^d+1)$, $Y = X^k$, with basis $1, X, \dots, X^{k-1}$:
$a = \sum_{i<k} X^i a_i(Y)$ with $(a_i)_j = a_{kj+i}$ (`poly.c:poly_toisoring`). Multiplication
$a\cdot b$ has components
```math
(ab)_t = \sum_{i+j = t} a_i b_j + Y\sum_{i+j = t+k} a_i b_j ,
```
so a public multiplier $a$ becomes the $k\times k$ block over $R$ with entry $(t, l)$ equal to
$a_{t-l}$ for $t \ge l$ and $Y a_{t-l+k}$ for $t < l$ (`quad.c:quad_toisoring`, linear branch);
$A \in R'^{r\times c}$ becomes $\hat A \in R^{kr\times kc}$ and $w$ becomes
$\hat w = (w_{0,0}, \dots, w_{0,k-1}, w_{1,0}, \dots) \in R^{kc}$. The constant coefficient of
$a \in R'$ is the constant coefficient of $a_0 \in R$, so one "constant coefficient vanishes"
statement over $R'$ becomes one over $R$ (component $0$), whereas "$a = 0$" becomes $k$
statements. The automorphism $\sigma'$ of $R'$ maps component $i$ to component $k - i$ with a
factor $-Y^{d-1}$ (for $i \ge 1$) and applies $\sigma$ to the coefficients; support for
$\sigma'$ in user statements is optional (not needed for the credential relations).

**Modulus lifting without carries (LaZer's optimisation, adopt).** Instead of committing to the
quotient $v = (Aw + t)/p$, prove the approximate range statement
$\|p^{-1}(\hat A \hat w + \hat t) \bmod q\|_\infty \le B'$ with
$B' = (P + c\,P\,d'\,S)/p$, $P = (p-1)/2$, $S \ge \|w\|_\infty$: the prover's small vector is
exactly the integer quotient, and the ARP's guarantee $\|y\|_\infty \le 2\,\mathrm{Bz4} \le 32 s_4$
together with $q > F + 32 s_4\,p$, where $F \ge \|Aw+t\|_\infty$, implies $Aw + t = p\,y$ over $\mathbb{Z}$ (LaZer paper §3.1, Eq. 6). The
public inputs are `Ds = p^{-1}·Â[:, s1_indices]`, `Dm = p^{-1}·Â[:, m_indices]`,
`u = p^{-1}·t̂` reduced modulo $q$ and centred (`lin-proofs.c:_lin_set_statement_A/_t`). The
caller must pass $A$ and $t$ with centred lifts of their mod-$p$ coefficients; LaZer's Python
demo passes $[0, p)$ representatives and thereby halves its margin (reading; the port rejects
non-centred inputs or centres them itself).

**Norm statements.** Blocks are selections of witness coordinates, so `Es`, `Em`, `Ps` are
selector matrices; LaZer keeps a specialised toolbox copy for this. The port uses the generic
toolbox with selector matrices represented sparsely (one nonzero per row), which is equivalent
and avoids a second copy of 3 000 lines.

### 7.3 `statement`: quadratic relations over arbitrary $(p, d')$ — new

Goal: the user writes a relation over $R_{p,d'}$ in named variables, with per-variable norm
bounds, and the library produces the toolbox statement over $R_{q,d}$, the lowered witness, and
the required proof-system parameters. Two mechanisms beyond §7.2:

**(a) Degree lowering of quadratic forms.** For $s \in R'^{c}$ and an upper-triangular
$R_2 \in R'^{c\times c}$, the component-$t$ of $s^{\mathsf T}R_2 s$ is
```math
\big(s^{\mathsf T} R_2 s\big)_t = \sum_{a\le b}\ \sum_{\substack{i, j, m \in [0,k)\\ i+j+m \equiv t\ (k)}} Y^{\lfloor (i+j+m)/k\rfloor}\, s_{a,i}\,(R_{2,ab})_m\, s_{b,j},
```
i.e. block $(a, b)$ of the lowered form for output component $t$ has $(i, j)$ entry
$Y^{\lfloor (i+j+m)/k\rfloor}(R_{2,ab})_m$ with $m = (t - i - j) \bmod k$ and the power of $Y$ in
$\{0, 1, 2\}$. The lowered form must then be re-symmetrised to upper triangular (add the
$(b,i)<(a,j)$ entries to their mirror). LaZer has this code but disabled (`quad.c:191`,
`if (quad && 0)`); the port implements and tests it against direct evaluation in $R'$ for random
inputs. As in §7.2, a quadratic equation over $R'$ becomes $k$ equations over $R$; an
evaluation equation becomes one.

**(b) Modulus lifting with committed carries.** The implicit-carry trick of §7.2 needs the
relation to be linear in the witness. For a quadratic $f(s) \equiv 0 \pmod p$ over $R'$:
introduce the carry $v := f(s)/p \in R'^{\,r}$ as a new witness block in the BDLOP part, prove
$\hat f(\hat s) - p\,\hat v = 0$ over $R_q$ as ordinary quadratic equations (it is quadratic in
$\hat s$ and linear in $\hat v$), and add an approximate $\ell_\infty$ statement on $\hat v$
(`ArpBlock` with `Dm` selecting the carry slots). Bounds: with $\|s\|$ bounds $\beta$ (from the
exact $\ell_2$ statements) and public coefficients centred modulo $p$,
$F := \max_{\text{rows}}\|f(s)\|_\infty$ is bounded via $\|ab\|_\infty \le \|a\|_2\|b\|_2$ for
$a, b \in R'$; $V := \lceil F/p\rceil$ bounds $\|v\|_\infty$ for the honest prover; the
extractor's $\hat v$ satisfies $\|\hat v\|_\infty \le 2\,\mathrm{Bz4} \le 32 s_4$, where $s_4$ is
sized from the Euclidean bound $\sqrt{n'd}\,V$ (corrected 2026-09-28; this passage first wrote
$\psi V$), so $q > F + 32 s_4 p$ makes $\hat f(\hat s) = p\hat v$ hold over
$\mathbb{Z}$ and hence $f(s) \equiv 0 \pmod p$. Because the carries sit in the BDLOP part they
cost $r k$ full-size polynomials of commitment; when $r$ is small (one or two equations, as in
the credential relations) this is cheaper than the alternatives. When $p = q$ (the statement
already lives in the proof ring, possible when $p \equiv 5 \pmod 8$ and the norm inequalities
of §5.2 step 10 hold), no carries are needed.

**Builder API sketch.**

```rust
let mut st = Statement::new(StatementRing { p, d: 64 * k });      // the user's ring
let s  = st.var("s",  c, Norm::L2(beta));                          // short witness block
let x1 = st.var("x1", 1, Norm::Binary);                            // example: binary block
let h  = st.var("h",  1, Norm::Unbounded);                         // committed, no bound (BDLOP)
st.eq_mod_p(expr!(A * s + b * x1 - t))                             // linear: implicit carry (7.2)
  .eq_mod_p(expr!((A * s - C) * (y - x1) - 1))                     // quadratic: committed carry (7.3b)
  .const_coeff_zero(expr!(...));                                   // evaluation statement
let compiled = st.compile(&param_tool_output)?;                    // lowers, lifts, checks bounds
let proof = compiled.prover(pp_seed).witness(&w)?.prove(&mut rng)?;
```

Expressions are polynomials of degree $\le 2$ in the variables with public $R_{p,d'}$
coefficients; `compile` returns the `lnp` statement, the witness map, the list of derived
parameters ($\log_2 q$ lower bound, block sizes) for the parameter tool, and the sizes. The
motivating instance is the credential base of the owner's paper (Section 3.2.5): possession
$(A s - C)(y - x_1) = 1$ over $R_{q'}$ with $q' \equiv 5 \pmod 8$, $\|s\| \le \beta$, $y$ public, plus a
learning-with-rounding tag $A K + e = \gamma T$; both are quadratic-or-linear with norm bounds
and fit this builder.

---

## 8. Crate layout, dependencies, features

```
lnp22/                         working name; edition 2024; rust-version 1.95; #![forbid(unsafe_code)]
├── Cargo.toml
├── README.md                  OpenVTC-style, short (as in the credential crate)
├── docs/                      design-notes.md, protocol.md (this file, trimmed), encodings.md,
│                              parameters.md, testing-and-benchmarks.md, katex-header.html
├── src/
│   ├── lib.rs                 crate docs (with formulas), re-exports, naming policy
│   ├── error.rs               Error enum: every rejection reason is a variant, no secrets in messages
│   ├── params/                mod.rs (Ring/Abdlop/QuadEval/Tbox/Lin param structs), derive.rs (§5.2 steps 1–4, 6–12),
│   │                          check.rs (step 10), sets.rs + sets/*.json (reference sets), moduli.rs (RNS primes)
│   ├── math/                  int.rs (i128/U256 helpers), ring.rs, rns.rs, ntt.rs, poly.rs, vec.rs, mat.rs,
│   │                          sparse.rs, iso.rs (degree lowering incl. quadratic forms)
│   ├── rand/                  prg.rs (AES-256-CTR / SHAKE128, domains), uniform.rs, binomial.rs, gauss.rs, reject.rs, fixed.rs (fixed-point exp/cosh)
│   ├── codec/                 bits.rs (bit writer/reader), elements.rs (urandom/grandom/ghint codes), proof.rs (layout §3.8), statement_hash.rs (§3.9)
│   ├── transcript.rs          H chaining, domain tags, default vs lazer-compat order (§3.7)
│   ├── dcompress.rs           Fig. 17
│   ├── abdlop.rs              keygen, commit, opening proof (Fig. 18)
│   ├── quad.rs, quad_many.rs, quad_eval.rs
│   ├── tbox/                  layout.rs (§3.6 indices), arp.rs (z3/z4 round), equations.rs (families), fold.rs (Schwartz–Zippel), prove.rs, verify.rs
│   ├── lnp.rs                 §7.1
│   ├── lin.rs                 §7.2
│   └── statement/             §7.3: expr.rs, lower.rs, lift.rs, compile.rs
├── tests/                     integration tests (§11)
├── benches/                   criterion (§12)
├── kat/                       known-answer vectors: json produced by tools/, consumed by tests
└── tools/
    ├── params/                Sage/Python: moduli.py, lnp_params.py (port of the codegen scripts), lin_params.py → json
    ├── kat/                   Python references (coder, PRG derivations, samplers) with mpmath/pycryptodome
    └── lazer-kat/             C harness against liblazer producing proofs + intermediate hashes (x86-64 Linux only)
```

Dependencies (versions and licences checked on crates.io on 2026-09-25): `sha3 0.12`
(SHAKE128), `aes 0.9` + `ctr 0.10` (PRG), `crypto-bigint 0.7` (Apache-2.0 OR MIT; 256/320-bit
integers), `zeroize 1.9`, `rand_core 0.10`, `subtle 2.6` (optional constant-time helpers),
`serde 1` (optional feature `serde`, for parameter sets and proofs' JSON forms), optionally
`dashu-float 0.6` (MIT OR Apache-2.0) if the fixed-point exp is not hand-written. Dev:
`criterion 0.8`, `proptest 1.11`, `serde_json`, `hex`. Not used: `tfhe`/`tfhe-ntt`
(BSD-3-Clause-Clear), `rug` (GMP/MPFR bindings), anything with a C build.

Features: `serde`; `parallel` (rayon over matrix rows and over the 256 range-proof rows);
`lazer-compat` (LaZer's transcript order and challenge derivations, for interoperability tests
only; the verifier stays strict); `test-utils` (deterministic PRG hooks). No `unsafe`
anywhere in the first release.

Naming: snake_case functions, CamelCase types, no Greek letters or subscripts in identifiers;
paper symbols appear in the rustdoc "In formulas" sections next to each item.

---

## 9. LaZer source → Rust module map

| LaZer | Rust | Notes |
|---|---|---|
| `int.c`, `intvec.c`, `intmat.c` | `math/int.rs`, `math/vec.rs`, `math/mat.rs` | `i128` + `U256` replace `int_t`; `binexp` → `math/int.rs` |
| `moduli.h`, `moduli.sage`, `polyring.c`, `mont.h`, `ntt.c`, `hexl.cpp` | `params/moduli.rs`, `math/ring.rs`, `math/rns.rs`, `math/ntt.rs` | new prime tables (62-bit); own NTT; exact CRT |
| `poly.c`, `polyvec.c`, `polymat.c`, `spolyvec.c`, `spolymat.c`, `quad.c` | `math/poly.rs`, `math/vec.rs`, `math/mat.rs`, `math/sparse.rs`, `math/iso.rs` | explicit NTT-form type; quadratic isoring enabled |
| `rng.c`, `aes256ctr*.c`, `shake128.c` | `rand/prg.rs`, `transcript.rs` | RustCrypto |
| `urandom.c`, `brandom.c`, `grandom.c`, `rejection.c` | `rand/uniform.rs`, `rand/binomial.rs`, `rand/gauss.rs`, `rand/reject.rs`, `rand/fixed.rs` | defects of §10.4 fixed |
| `coder.c`, `bytes.c` | `codec/` | bit-exact |
| `dcompress.c` | `dcompress.rs` | as is |
| `abdlop.c` | `abdlop.rs` | verifier checks $(z_{2,1}, z_{2,2})$ |
| `lnp-quad.c`, `lnp-quad-many.c`, `lnp-quad-eval.c` | `quad.rs`, `quad_many.rs`, `quad_eval.rs` | eval zeroes/checks both coefficients |
| `lnp-tbox.c`, `lnp-tbox.h` | `tbox/` | independent $\Gamma$; paper's transcript order |
| `lnp.c` | `lnp.rs` | zero-based equation indices; strict decoding |
| `lin-proofs.c` | `lin.rs` | generic toolbox with sparse selectors instead of a copy |
| `scripts/*.sage` | `tools/params/*.py` + `params/derive.rs`, `params/check.rs` | search in Sage/Python, validation in Rust |
| `tests/*-test.c`, `tests/*-params*.sage` | `tests/`, `kat/`, `params/sets/` | |
| `blindsig.c`, `python/*`, `labrador*`, `falcon*` | — | out of scope (applications; LaBRADOR; Falcon sampler lives in the credential crate's own NTRU module) |


---

## 10. Register of LaZer's deviations from LNP22, and the port's decisions

Every item is a reading of the source at `e382e584`; none was confirmed by running LaZer. Items
marked **C** look like defects and are not ported (default mode); the implementer should confirm
each with the harness of §11.4 before reporting upstream, and the `lazer-compat` mode reproduces
only those that affect interoperability of honest proofs. Items marked **A** are improvements over
the paper's text and are adopted. Items marked **B** are neutral engineering choices, kept.

### 10.1 C — Fiat–Shamir order and challenge derivation in the toolbox

1. **$h$ is never absorbed before $\mu$ (`lnp-tbox.c:731-760`, `lnp-quad-many.c:34`).** The
   $\lambda/2$ polynomials $h_i$ enter only as $r_0 \mathrel{-}= h_i$ of the equations
   $f_{\lambda/2+2+N+i}$ and through the check $h_{i,0} = h_{i,d/2} = 0$; the folding challenges
   $\mu$ are derived from the hash after $t_g$, so a prover knows $\mu$ before choosing $h$.
   Sketch of a forgery for $\lambda/2 \ge 2$ (LaZer's sets have $\lambda = 4$): let one user
   equation be false, $f_1(s) = e \ne 0$; set $h_i := g_i + T_i(s) + \delta_i$ where the
   $\delta_i$ solve the single $R_q$-linear equation $\sum_i \mu_{N'+i}\delta_i = -\mu_1 e$ subject
   to $\delta_{i,0} = \delta_{i,d/2} = 0$ ($(\lambda/2)(d-2)$ free coefficients against $d$ linear
   conditions, solvable whenever some $\mu_{N'+i}$ is invertible); every remaining step is honest
   for the modified equations, which the real witness satisfies. The paper's order (Appendix B.3:
   $a_3 = h$ is hashed before $\mu$) prevents this. **Port:** absorb `enc(h)` before deriving $\mu$.
2. **The 512 projection equations use challenges from `hash0`, taken before $t_g$ (and before
   $z^{(e)}, z^{(d)}$) are absorbed (`lnp-tbox.c:366, 641-658`; `lin-proofs.c:619` carries the
   comment "XXX why hash0 needed ??").** The prover therefore knows the projection rows' folding
   coefficients before committing to $g$, and the two free coefficients $g_{i,0}, g_{i,d/2}$ of each
   garbage polynomial (never checked, only their effect on $h_i$ is) can be chosen to cancel any
   defect of those rows. The range proof is then not binding, and with it the lifting of the
   exact-$\ell_2$ and binary statements from $\mathbb{Z}_q$ to $\mathbb{Z}$. Also $z^{(e)}, z^{(d)}$
   themselves are never hashed (they are bound only through these equations). **Port:** absorb
   `enc(z3) ‖ enc(z4) ‖ enc(tg)` and derive all of $\Gamma$ from the resulting hash (paper: $a_2$).
3. **Shared Schwartz–Zippel challenges (`lnp-tbox.c:__schwartz_zippel_accumulate2`;
   `lin-proofs.c:2226-2236` re-samples with identical `(seed, dom)`).** One pair of challenge
   vectors is applied to all $\lambda/2$ accumulators for the user evaluation equations, the sign
   equations, $\upsilon$, the binary block and the $\ell_2$ blocks; only the projection rows get a
   $\lambda\times 256$ matrix. The $\lambda/2$ repetitions thus give 2 independent $\mathbb{Z}_q$
   checks, not $\lambda$: knowledge error $\approx q_1^{-2}$ ($2^{-80}$ at 40 bits) where the
   scripts assume $q_1^{-\lambda}$. Worse, the $Z$ exact blocks are folded with the SAME scalar
   (`__schwartz_zippel_accumulate_l2` calls the accumulator inside `for i < Z` with a fixed `dom`),
   so only $\sum_i(\|e_i\|^2 + \langle p_i, \upsilon_i\rangle - \beta_i^2) = 0$ is enforced: a
   prover may exceed bound $\beta_1$ by $\delta$ and compensate with slack $\delta$ in block 2.
   **Port:** $\Gamma \in \mathbb{Z}_q^{\lambda\times M_{\mathrm{tot}}}$ with one fresh column per
   evaluation equation and one fresh row per accumulator half, exactly as Fig. 8/10.
4. **Unrelated derivations share `(hash, dom)` values** ($\mu$ via `polyvec_urandom(…, hash, 0)`
   uses domains $(0\ll32)|(j+1)$; the evaluation challenges use small domains under the same
   key). No exploit, but the port tags every derivation with a distinct domain constant.

### 10.2 C — Verifier checks

5. **$\|z_{2,1}\|$ is not checked** (`abdlop.c:537-541`, `lnp-quad.c:499-505`); Fig. 18 bounds
   $\|(z_{2,1},\ A_1 z_1 + A_2' z_{2,1} - c 2^D t_{A,1} - \gamma w_1)\| \le B$. Without it the
   extracted randomness is unbounded and the MSIS binding argument of Theorem A.2 does not
   apply (since $A_2'$ has $m_2 - n > n$ columns, a prover can solve the first verification
   equation for $z_{2,1}$ for any short $z_1$ of its choice; a complete forgery was not worked
   out). **Port:** Fig. 18 literally. Honest LaZer proofs satisfy it because LaZer's prover
   enforces the joint bound on itself.
6. Hint bound $\|h\|_\infty \le m$ instead of $m/2$: harmless; port uses $\le (q-1)/(2\gamma)$.
7. Standalone `lnp-quad-eval.c` checks only $h_{i,0}$ although it folds with both $\mathrm{Tr}$ and
   $X^{d/2}\mathrm{Tr}$: the second half is wasted (soundness $q_1^{-\lambda/2}$). The toolbox copy
   checks both. **Port:** both, everywhere.

### 10.3 C — `lnp.c` versus `lnp-tbox.c`

8. `lnp.c` stores and hashes user equations at offsets `QUADEQ_INPUT_OFF`/`EVALEQ_INPUT_OFF`
   but `lnp_tbox_prove` reads them from index 0; array dimensions differ (`np` vs `n_`); the
   `ASSERT(N > 0)` precedes the first assignment; `_verify_statement` checks evaluation equations
   with the quadratic arrays. The generic statement object is unused in the tree; the linear
   front end carries its own toolbox copy with $\lambda$-scaled challenge domains
   (`lin-proofs.c:565-631`), so proofs of the two copies are not interchangeable. **Port:** one
   toolbox, zero-based equation indices, dimensions derived from the present blocks.

### 10.4 C — Samplers and rejection (prover-side; zero-knowledge, not soundness)

9. `_urandom` samples $[0, (m-1)/2]$ for `mbits` $\ge 60$ (§4.2).
10. Gaussian: process-global sign-bit cache; constant polynomials for $t \ge 24$ (§4.2).
11. `rej2 == 2` uses `stdev1sqr` (§3.3): the acceptance test degenerates and $z_2$ is effectively
    unmasked beyond $y_2$'s own width.
12. Sign bits for $b^{(e)}, b^{(d)}$: skipped and reused bit positions (§4.2).
13. `lin-proofs.c` scales the `Dm` block of the $z^{(d)}$ equations by $2^{-1}$ twice
    (`:2991-3024` vs `:3098`); only reachable with $\ell > 0$, which no shipped set uses.

### 10.5 A — LaZer improvements to adopt

14. Implicit-carry modulus lifting for linear relations (§7.2), saving the commitment to $v$.
15. Ajtai/BDLOP split search minimising proof size (§5.2, driver).
16. The smooth bimodal-style test for $z_2$ with $M_2 = \exp(1/(2\gamma_2^2))$, after the thesis
    argument is checked (§3.3); until then $\mathrm{Rej}_2$ with the same $M_2$.
17. $M_1$ with $\sqrt{2\cdot 129/\log_2 e} \approx 13.37$ instead of the paper's rounded $14$.
18. Standard deviations rounded to $1.55\cdot 2^k$: one table-driven Gaussian sampler and the
    cheap unary+binary encoding of §3.8.
19. Interleaved witness layout with sparse upper-triangular quadratic forms and the pair
    shuffle for $\sigma$ (§3.3, §3.5): all toolbox equations are sparse in it.
20. Hashing $w_1$ (compressed) rather than $w$, recomputing $v$ and $w_1$ on the verifier side,
    chaining a 32-byte SHAKE128 state, and sending the challenge $c$ (paper Section 6.1 leaves
    this open).
21. Per-round restarts after rejection (§4.4).
22. Selector-based norm blocks in the linear front end (as sparse matrices in the port).

### 10.6 B — Neutral choices kept

23. No $\eta$ filter on challenges (§2.4); $\eta$ enters only the parameter analysis.
24. $\|z^{(d)}\|_\infty \le 16 s^{(d)}$ (paper: $14 s^{(d)}$) and $t \approx 1.30$ in one soundness
    inequality (paper $1.64$): the port's parameter checker implements the paper's inequalities
    and reports LaZer's values alongside.
25. AES-256-CTR as PRG, SHAKE128 as hash; 50-bit RNS primes with HEXL (port: 62-bit, own NTT).
26. Both range-proof blocks always allocated (port: only present blocks).
27. Public matrices from `ppseed` with domains 0, 1, 2; statement hash as SHAKE128 of the coded
    statement components; proof layout of §3.8 (default mode adds length prefixes and a
    parameter-set identifier to the statement hash).

---

## 11. Testing

Independent oracles for every layer; no test may use the code under test as its own reference.

### 11.1 Unit tests (per module, `cargo test`)

- `math`: NTT forward/inverse round trip and product against schoolbook `i128` negacyclic
  multiplication for every RNS prime and $d \in \{64, 128, 256\}$; RNS to/from with exact CRT
  against `crypto-bigint` big-integer reconstruction; accumulation of `NADDS` products stays
  exact; `auto`, `tracemap`, `lrot` identities (Lemma 2.4: constant coefficient of $T(a,b)$ equals
  $\langle a, b\rangle$; Lemma 4.7; Lemma 4.8 on random quadratic forms) as property tests
  (`proptest`); degree lowering (§7.2, §7.3a) against direct evaluation in $R'$; `dcompress`
  Lemma A.1 exhaustively for a small $q$ and randomly for the reference $q$'s.
- `rand`: PRG streams against Python (`pycryptodome` AES-CTR, `hashlib.shake_128`) KATs for
  the composite domains of §4.1; uniform/bounded/binomial/autostable samplers against a Python
  re-implementation of `urandom.c`/`brandom.c`/`intvec.c` (bit-exact); Gaussian sampler:
  determinism, sample mean and variance within tolerance, $\chi^2$ against the exact
  $D_\sigma$ probabilities for $\sigma = 1.55\cdot 2^k$, $k \le 6$, tail counts against Lemma 2.2,
  and a check that all $d$ coefficients differ for large $k$ (regression for §10.4);
  rejection tests against `mpmath` at 300 bits on $10^5$ random inputs plus constructed
  near-boundary cases, and the measured acceptance rate within statistical error of $1/M$.
- `codec`: round trips for every element code, bit-exact KATs from a Python re-implementation
  of `coder.c`, decoder rejection of out-of-range values, bad padding, truncation, trailing bytes.
- `params`: regenerated `tbox_params1`, `kyber1024`, `anon_cred` P1/P2 sets equal the values of
  §5.3; every check of §5.2 step 10 rejects a set with one input perturbed.

### 11.2 Protocol tests (`tests/`)

- Completeness: random witnesses and statements for `abdlop`, `quad`, `quad_many`, `quad_eval`
  and the full toolbox, for each combination of present blocks ($N, M, Z, n_{\mathrm{bin}}, n'$
  zero or not), for $d = 64$ and $128$, for one-prime $q$ and, without binary, exact-norm or range blocks, two-prime $q$,
  several seeds; the linear front
  end on the Kyber-1024 and demo statements; the statement builder on a quadratic relation with
  committed carries (§7.3) at small parameters.
- Negatives, one check per test: each proof field perturbed (`tB`, `h`, `tA1`, `c`, `hint`, `z1`,
  `z21`, `z3`, `z4`) and each of the verifier's inequalities pushed just over its bound; wrong
  statement, wrong `pp_seed`, wrong parameter set; non-canonical encodings.
- Soundness regressions for §10 (each a cheating prover built from the honest one): adaptive
  $h$ after $\mu$ (10.1.1) rejected; garbage-coefficient absorption of a false projection row
  (10.1.2) rejected; slack borrowing between two $\ell_2$ blocks (10.1.3) rejected; large
  $z_{2,1}$ solving the first verification equation (10.2.5) rejected.
- Extraction evidence: an interactive harness with injected challenges runs the final round
  twice with $c \ne c'$ on the same prefix and recovers $(\bar s_1, \bar s_2, \bar m)$ satisfying
  the commitment and the folded quadratic equation (Lemma 3.1 / Theorem 4.2 structure).
- Determinism: `prove_with_seed` is reproducible across platforms (x86-64, arm64), byte for byte.

### 11.3 Cross-implementation tests with LaZer (`lazer-compat`)

Build LaZer on a real x86-64 Linux machine with AVX-512 (Docker on Apple Silicon cannot run
AVX-512 code; QEMU user emulation is untested for it) using the checked-in generated headers,
and run `tools/lazer-kat` against `liblazer`: for `tbox_params1` and the Kyber-1024 set, fixed
`ppseed`, fixed statements and witnesses, produce (a) the expanded $A_1, A_2', B'$, (b) coder
outputs for known vectors, (c) proofs from `lnp_prover_prove` and from the `lin_*` API with
fixed prover seeds, (d) with a small patch, every intermediate 32-byte hash. Rust tests then
check (a)–(b) bit-exactly, verify (c) in compat mode, and compare (d). This validates
arithmetic, encodings, layouts and the LaZer transcript; the default mode is validated by the
soundness regressions and the paper.

### 11.4 Confirming the §10 findings

The same harness, with a malicious-prover build of LaZer (a few dozen lines each for 10.1.1,
10.1.2, 10.1.3), decides whether the forgeries verify. Do this before reporting to the LaZer
authors, and record the outcome in `docs/design-notes.md`.

### 11.5 Gates

`cargo fmt --check`, `cargo clippy --all-targets --all-features -- -D warnings`,
`RUSTDOCFLAGS='-D warnings' cargo doc --no-deps`, `cargo test` (debug and release), `cargo deny
check` (licences: MIT, Apache-2.0, BSD-3-Clause, Unicode; no BSD-3-Clause-Clear, no LGPL), an
MSRV job, Linux/macOS/Windows on x86-64 and arm64.

---

## 12. Benchmarks and documentation

### 12.1 Benchmarks (`benches/`, criterion)

Each benchmark prints the sizes it handles first (proof bytes, actual versus `prooflen`;
commitment bytes) and then times: NTT forward/inverse per prime and degree; polynomial product;
dense and sparse matrix–vector products at the reference dimensions; Gaussian sampling per
polynomial for each $\sigma$ in use; one rejection test; `abdlop` commit/prove/verify;
`quad`/`quad_many`/`quad_eval` prove/verify; toolbox prove/verify for `tbox_params1`,
`kyber1024`, `anon_cred` P2 and the credential relation of §7.3; the number of restarts per
proof (expected $M_1 M_2$ and $M_3 M_4$). Record CPU, `rustc` version, features and seeds with
every published number (`docs/testing-and-benchmarks.md`). Compare with LaZer's timings only on
the same machine and say so; none were measured here.

### 12.2 API documentation

Rustdoc for every public item, with an "In formulas" section giving the paper's notation and a
pointer to the paper figure or section. Formulas are written inside code so Markdown never
touches the LaTeX: ``$`…`$`` inline and fenced ```math blocks for display; this is also
GitHub-flavoured Markdown's math syntax, so `README.md` and `docs/*.md` render identically on
GitHub. Rendering in rustdoc uses a KaTeX header (copy `docs/katex-header.html` from the
credential crate: KaTeX 0.17.0 from jsDelivr with SRI hashes and a small deferred script that
converts the two code forms; without JavaScript the LaTeX source stays readable). Wiring:

```toml
[package.metadata.docs.rs]
features = ["serde"]
rustdoc-args = ["--html-in-header", "docs/katex-header.html", "--cfg", "docsrs"]
```
```toml
# .cargo/config.toml
[alias]
docs = ["rustdoc", "--lib", "--features", "serde", "--open", "--", "--html-in-header", "docs/katex-header.html"]
```

`README.md` is included as the crate documentation (`#![doc = include_str!("../README.md")]`) so
its examples are doctests; `docs/` holds the guides listed in §8, each linked from
`docs/README.md`; `RUSTDOCFLAGS='-D warnings'` is a gate. Every deviation decision of §10 and
every "(reading)" claim that later gets confirmed or refuted is recorded in
`docs/design-notes.md` with the date and the evidence.

---

## 13. Milestones and acceptance criteria

Work items inside a milestone are independent unless stated; milestones are ordered by
dependency, not by calendar.

**M0 — Skeleton.** Crate, CI gates, `docs/` with the KaTeX header, `Error`, parameter structs
with JSON loading, `params::check` implementing §5.2 step 10, the RNS prime tables and the
`tools/params` scripts producing the four reference sets of §5.3 with the current
lattice-estimator (numbers recorded with provenance). *Accept:* regenerated `tbox_params1`
equals §5.3 in every field; a perturbed set is rejected by `check`.

**M1 — Arithmetic, randomness, codec.** `math/` (§6), `rand/` (§4.2–4.3), `codec/` (§3.8),
`dcompress`, `transcript`. *Accept:* all §11.1 tests pass, including bit-exact PRG, sampler and
coder KATs from the Python references; NTT products exact for $10^4$ random pairs per prime;
rejection decisions match `mpmath` on $10^5$ inputs.

**M2 — ABDLOP.** `abdlop.rs` with compression (§3.1–3.2). *Accept:* completeness for
`tbox_params1` dimensions and the paper's Fig. 12 dimensions; every negative of §11.2 for this
layer; the two-transcript extraction harness recovers the opening.

**M3 — Quadratic proofs.** `quad`, `quad_many`, `quad_eval` (§3.3–3.5). *Accept:* completeness
for random quadratic and evaluation statements with $N, M$ up to 16 at $d = 64$ and $128$;
negatives; the $\lambda/2$ garbage construction checked by asserting $h_{i,0} = h_{i,d/2} = 0$ for
honest provers and nonzero for a prover with one false evaluation equation.

**M4 — Toolbox and statement object.** `tbox/`, `lnp.rs`, proof (de)serialisation, default and
`lazer-compat` transcripts. *Accept:* completeness for all block combinations; all §11.2
negatives and soundness regressions; encoded proofs within 1 % of `prooflen`; in compat mode
the LaZer-produced proofs of §11.3 verify (requires the x86-64 harness; if no such machine is
available, defer this criterion to M5 and say so in the docs).

**M5 — Linear front end and parameter tooling.** `lin.rs` (§7.2) including degree lowering and
implicit-carry lifting; `tools/params/lin_params.py`; the Kyber-1024 and demo statements
end to end. *Accept:* proofs for the Kyber-1024 statement at the shipped parameter set verify;
sizes match §5.3; compat-mode interop with LaZer's `lin_*` proofs if the harness exists.

**M6 — Quadratic statements over arbitrary rings.** `statement/` (§7.3): expression language,
quadratic degree lowering, committed carries with the $q$ lower bound, parameter export for the
tool. *Accept:* the possession relation $(As - C)(y - x_1) = 1 \bmod q'$ with $\|s\| \le \beta$
proves and verifies at a parameter set produced by the tool; a false relation is rejected;
lowering and lifting are each tested against direct evaluation.

**M7 — Performance and release.** Profiling against the §6.4 model; lazy reduction; optional
`parallel`; optional SIMD NTT crate; zeroization audit (`s1, s2, m`, masks, seeds); benchmark
report; crates.io release under the chosen name. *Accept:* published benchmark table; no
`unsafe` in the main crate; `cargo deny` clean.

Rough relative sizes (uncertain): M1 and M4 are the largest (each about a third of the total);
M6 is the most mathematically delicate; M0, M2, M3, M5, M7 are each roughly half of M1.

---

## 14. Risks and open questions

1. **The §10.1 findings are readings, not demonstrations.** If confirmed they mean that
   LaZer-produced proofs are not sound as generated; the port's default mode is unaffected, but
   interoperability (`lazer-compat`) would then be a test-only facility, never a deployment
   option. Confirm early (§11.4).
2. **Thesis and follow-up papers unread.** The smooth $z_2$ rejection (§3.3), the constants
   $(\omega, \eta, |C|)$, $\sqrt{337}$, $41$, $26$, the $2.25$ bits per hint coefficient, and possibly
   other choices come from Nguyen's thesis or from ePrint 2023/077 and 2023/560, whose protocols
   LaZer's demos implement. Read them before fixing defaults; the port's parameter checker must
   cite where each constant comes from.
3. **Parameter sizes for the credential relations.** The lifted modulus for a quadratic
   relation with committed carries (§7.3b) grows with the norm of $f(s)$; estimated 60–80 bits,
   which the `i128` design covers, but the resulting proof size (tens of KB) has not been
   computed. Run the parameter tool on the actual relation early in M6. Since the 2026-09-28
   correction of $\alpha_4$, $s_4$ grows with $\sqrt{n'd}$, and the lifted modulus with it by up
   to $\tfrac12\log_2(n'd)$ bits.
4. **Performance without HEXL/AVX-512.** A portable Rust NTT will be slower than HEXL; how
   much is unknown until measured. The RNS design with fewer, larger primes partly compensates.
5. **Rejection-sampling precision.** No MPFR; the fixed-point $\exp$/$\cosh$ must be tested to
   the stated precision and documented; at the same variance, decisions may differ from LaZer's
   in negligible cases (LaZer's rounded variance adds non-negligible differences, §4.3).
6. **Two-prime moduli.** `lnp-tbox-codegen.sage` has an unassigned variable on the two-prime
   path (`log2q1_` is set only in the one-prime branch, lines 87–92), so no shipped set uses
   $q = q_1 q_2$; the port supports it but has no LaZer reference values. **Correction,
   2026-09-28:** the range proofs are unsound for $q = q_1 q_2$. Their sign check uses that
   $\mathbb Z_q$ is an integral domain (LNP22, proof of Prop. 5.1), and the CRT value
   $(1 \bmod q_1, -1 \bmod q_2)$ also squares to one. Binary, exact-norm and range blocks need a
   prime $q$.
7. **Constant time.** Neither LaZer nor this plan claims constant-time behaviour; say so once
   in the README and nowhere else, as the credential crate does.
8. **Formal verification candidates** (optional, Lean 4/Mathlib): Lemma 2.4 ($T$ constant
   coefficient), Lemma 4.7/4.8 (trace identities), Lemma 5.2 (binary from $\langle x, x - 1\rangle = 0$),
   Lemma A.1 (hint correctness), the coder round trip, and the degree-lowering multiplication
   identity of §7.2. Each is self-contained and would raise the assurance of the corresponding
   Rust code above testing.

---

## 15. References

Verified on 2026-09-25 by fetching the ePrint pages (titles) or by reading the files named.

- Vadim Lyubashevsky, Ngoc Khanh Nguyen, Maxime Plançon. *Lattice-Based Zero-Knowledge Proofs
  and Applications: Shorter, Simpler, and More General.* IACR ePrint 2022/284 (CRYPTO 2022).
  Figures 1–3, 4–10, 12, 17, 18; Sections 2–6; Appendices A, B.3.
- Vadim Lyubashevsky, Gregor Seiler, Patrick Steuer. *The LaZer Library: Lattice-Based Zero
  Knowledge and Succinct Proofs for Quantum-Safe Privacy.* IACR ePrint 2024/1846 (CCS 2024).
  Section 3 (linear proof layer, Eq. 6), Section 4 (parameter generator), Section 5 (Python).
- LaZer source: `https://github.com/lazer-crypto/lazer`, commit `e382e584…`, MIT.
  Parameter scripts cite "[1] Lattice-Based Zero-Knowledge Proofs Under a Few Dozen Kilobytes,
  https://doi.org/10.3929/ethz-b-000574844" (Ngoc Khanh Nguyen's ETH thesis; not read here).
- Ward Beullens, Vadim Lyubashevsky, Ngoc Khanh Nguyen, Gregor Seiler. *Lattice-Based Blind
  Signatures: Short, Efficient, and Round-Optimal.* IACR ePrint 2023/077. Implemented by
  LaZer's `blindsig` demo; a likely source of LaZer's deviations from LNP22 (not read here).
- Jonathan Bootle, Vadim Lyubashevsky, Ngoc Khanh Nguyen, Alessandro Sorniotti. *A Framework
  for Practical Anonymous Credentials from Lattices.* IACR ePrint 2023/560. Implemented by
  LaZer's `anon_cred` demo (not read here).
- Ward Beullens, Gregor Seiler. *LaBRADOR: Compact Proofs for R1CS from Module-SIS.* IACR
  ePrint 2022/1341. Present in LaZer (`labrador*`), out of scope.
- Rust crates checked on crates.io on 2026-09-25: `sha3 0.12.0`, `aes 0.9.3`, `ctr 0.10.1`,
  `crypto-bigint 0.7.5`, `zeroize 1.9.0`, `rand_core 0.10.1`, `subtle 2.6.1`, `dashu 0.6.1`
  (MIT OR Apache-2.0), `astro-float 0.9.6` (MIT), `proptest 1.11.0`, `criterion 0.8.2`,
  `tfhe-ntt 0.7.1` (BSD-3-Clause-Clear; not used).

---

## Appendix A. Symbol table

| Paper | LaZer | Rust (suggested) | Meaning |
|---|---|---|---|
| $d$, $q$, $q_1$, $l = 2$ | `d`, `q`, `q1`, `L` | `ring.d`, `ring.q` | ring degree, modulus, smallest prime factor, number of factors of $X^d+1$ |
| $n$ | `kmsis` | `n_msis` | MSIS rank, rows of $A_1, A_2$ |
| $m_1$, $\ell$, $m_2$ | `m1` (incl. $Z$), `l`, `m2` | `m1`, `l`, `m2` | Ajtai, BDLOP and randomness lengths |
| $\ell_{\mathrm{ext}}$ | `lext` | `l_ext` | extension slots of $m$ |
| $\lambda$ | `lambda` | `lambda` | number of $\mathbb{Z}_q$ repetitions; $\lambda/2$ garbage polynomials |
| $\kappa$ (challenge bound), $\eta$, $C$ | `omega`, `eta`, `Csize` | `omega`, `eta` | challenge coefficients in $[-\omega, \omega]$ |
| $\nu$ | `nu` | `nu` | $s_2$ coefficients in $[-\nu, \nu]$ |
| $s_1, s_2, s^{(e)}, s^{(d)}$ | `stdev1..4` $= 1.55\cdot 2^{\texttt{log2stdev}}$ | `sigma[1..4]` | Gaussian widths |
| $\gamma_1, \gamma_2, \gamma^{(e)}, \gamma^{(d)}$ | `gamma1..4` | `slack[1..4]` | rejection slack factors |
| $M$ | `scM` $= \mathrm{round}(M 2^{128})$ | `m_scaled` | rejection constant |
| $D$, $\gamma$, $m = (q-1)/\gamma$ | `D`, `gamma`, `m` | `d_bits`, `gamma`, `hint_mod` | compression parameters |
| $B$ | `Bsq` $= \lfloor B^2\rfloor$ | `b_sq` | verifier bound on $(z_{2,1}, z_{2,2})$ |
| $t_A, t_{A,1}, t_{A,2}, t_B$ | `tA`, `tA1`, `tA2`, `tB` | same | commitment parts |
| $w, w_1, w_0$ | `w`, `w1`, `w0` | same | first message and its decomposition |
| $y^{(e)}, b^{(e)}, z^{(e)}, R^{(e)}, e^{(e)}$ | `y3`, `beta3`, `z3`, `R`, `s3` | `y_e`, `b_e`, `z_e`, `r_e`, `e_e` | exact-norm range proof |
| $y^{(d)}, b^{(d)}, z^{(d)}, R^{(d)}, e^{(d)}$ | `y4`, `beta4`, `z4`, `Rprime`, `s4` | `y_d`, … | approximate range proof |
| $x$ (slack decompositions) | `upsilon` | `upsilon` | appended to $s_1$ |
| $g$, $t_g$, $h_i$ | `g`, `tg`, `h` | `garbage`, `t_g`, `h` | evaluation-proof garbage and responses |
| $g_1$, $t$, $v$ | `g1`, `t`, `v` | same | quadratic-proof garbage, its commitment, first message |
| Dilithium hint $h$ | `hint` | `hint` | |
| $\Gamma$, $\mu$, $c$ | `V`, `mu`, `c` | `gamma_matrix`, `mu`, `c` | challenges |
| $\alpha$, $\beta_i^{(e)}$, $\beta^{(d)}$ | `alpha`, `B[i]`, `Bprime` | `alpha`, `l2_bounds`, `linf_bound` | norm bounds |
| $c^{(e)} = n_{\mathrm{ex}} d$, $n'$ | `nex`, `nprime` | `n_ex`, `n_prime` | dimensions of $e^{(e)}$, $e^{(d)}$ in polynomials |

## Appendix B. LaZer function cross-reference (commit `e382e584`)

| Function | File:line | Role |
|---|---|---|
| `abdlop_keygen / commit / enccomm / hashcomm / prove / verify` | `abdlop.c:28, 87, 155, 213, 253, 438` | §3.1–3.2 |
| `lnp_quad_prove / verify` | `lnp-quad.c:9, 329` | §3.3 |
| `_schwartz_zippel_poly`, `lnp_quad_many_prove / verify` | `lnp-quad-many.c:6, 78, 154` | §3.4 |
| `_shuffleauto*`, `_schwartz_zippel_int`, `_lnp_quad_eval_prove`, `lnp_quad_eval_prove / verify` | `lnp-quad-eval.c:36, 62, 121, 320, 524, 611, 686` | §3.5 |
| `lnp_tbox_prove / verify` | `lnp-tbox.c:167, 832` | §3.6 |
| `_lnp_tbox_compute_z34 / _check_z34`, `_expand_R_i / _expand_Rprime_i` | `lnp-tbox.c:1367, 1804, 1956, 1964` | range-proof round |
| `__schwartz_zippel_accumulate{,_,2,_beta3,_beta4,_upsilon,_bin,_l2,_z4,_z3}`, `__schwartz_zippel_auto` | `lnp-tbox.c:2069, 2150, 2333, 2369, 2423, 2493, 2562, 2770, 3000, 3298, 2224` | equation families and folding |
| `_lnp_hash_statement_*`, `_lnp_init`, `_lnp_prover_set_witness_upsilon`, `set_statement_*`, `_lnp_tbox_encproof / decproof`, `_lnp_hash_pp_and_statement`, `lnp_prover_prove`, `lnp_verifier_verify` | `lnp.c:117–359, 411, 502, 669–1031, 1081, 1158, 1232, 1405, 1472` | §7.1, §3.8, §3.9 |
| `lin_toisoring`, `quad_toisoring` | `quad.c:9, 96` | §7.2 (quadratic branch disabled at `:191`) |
| `_lin_set_statement_A / _t`, `lin_prover_set_witness`, `_lin_prover_prove`, `_lin_verifier_verify` | `lin-proofs.c:4606, 4663, 4725, 4402, 4471` | §7.2 |
| `coder_enc_*`, `coder_dec_*` | `coder.c` | §3.8 |
| `dcompress_decompose / power2round / use_ghint / make_ghint` | `dcompress.c` | §3.2 |
| `rej_standard`, `rej_bimodal` | `rejection.c:73, 149` | §4.3 |
| `gaussian155`, `_grandom_sample_i32`, `_grandom_sample` | `grandom.c` | §4.2 |
| `_urandom`, `_urandom_bnd`, `_urandom_i64` | `urandom.c` | §4.2 |
| `_brandom` | `brandom.c` | §4.2 |
| `_rng_init / _rng_urandom` | `rng.c` | §4.1 |
| `poly_toisoring / fromisoring / tocrt / fromcrt / tracemap / auto / urandom_autostable` | `poly.c:347, 380, 591, 655, 908, 950, 887` | §6, §2.1 |
| `intvec_auto / lrot / _intvec_urandom_autostable`, `int_binexp` | `intvec.c:425, 212, 595`, `int.c` | §2.1, §3.6 |
| `moduli_list`, `min_P`, `get_delta_msis / mlwe`, `std_gamma2M`, `bim_gamma2M`, `round_stdev` | `scripts/codegen.sage` | §5 |
| parameter search and checks | `scripts/lnp-tbox-codegen.sage`, `scripts/lin-codegen.sage` | §5.2 |
