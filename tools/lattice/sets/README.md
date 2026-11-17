# The Jali parameter sets of the lattice backend

The lattice backend (`src/pcreds/lattice/`) proves four relations with Jali, each under its own
parameter set embedded in `src/lattice/sets/` and pinned by SHA-256 (`src/lattice/sets.rs`):

| relation (proof) | set | origin |
|---|---|---|
| `R_Tag` (`π_id`) | `params-tag-beta443.json` | derived for the first port; the pinned Jali derives it again byte for byte |
| `R_att` (`π_att`) | `params-att-lr3-beta439.json` | derived here |
| `R_iss` (`π_iss`) | `params-iss-lr3-beta439.json` | derived here |
| `R_Possess` (`π_prove`) | `params-possess-lr3-beta439.json` | derived here |

The statements are those of the backend: the issuance randomness `x_0` has `ℓ_r = 3` ternary
components (the request is then pseudorandom under MLWE, `src/pcreds/lattice/base.rs`, and
`hiding_estimate.sage` in `tools/lattice/`), and `s` is bounded on both sides,
`1 ≤ ‖s‖² ≤ ⌊β_s²⌋` (`Norm::L2SquaredRange` of Jali), so that the proofs extract `s ≠ 0`. A set
is valid for exactly one statement layout (block names and order, exact norms, placements, the
shape of the constraints); Jali's `compile` refuses any other, and the unit test
`pcreds::lattice::relations::tests::the_statements_compile_against_their_parameter_sets` checks
that each statement compiles against its own set and no other.

## What is in this directory

| file | what |
|---|---|
| `<name>.export.json` | `Statement::requirements` and `Statement::blocks` of the relation at its WORST-CASE public data (every public coefficient at the largest centred absolute value of its modulus), at proof degree 128 and the probe modulus 1,099,511,627,917 (a prime no constraint uses). Jali derives bounds such as `max_integer_coefficient` from the constants of a statement, so the worst case makes the set valid for every instance. Written by the ignored unit test `export_requirements`; the unit test `the_committed_exports_are_current` compares them with the statements. |
| `make_requests.py` | writes the requests from the exports |
| `<name>.request.json` | the requests of Jali's parameter tool (schema `jali-params-request/2`) |
| `<name>.report.json` | the tool's reports, with the lattice-estimator verdict (`estimator_check`) |

## The policy

Block sizes of at least 439 for both the MLWE and the MSIS estimate (core-SVP 128 bits,
`"hardness": {"policy": "beta", "beta_min": 439}`), a single prime proof modulus found by the
tool's search, the set refused unless lattice-estimator's rough mode reaches 128 bits on both
instances (`--estimator-target 128`, lattice-estimator at the commit the tool pins), and the proof
modulus proven prime in Sage. `s` is movable in `R_att` and `R_Possess`: the tool chose the BDLOP
part for both, which `relations::ATT_S_PLACEMENT` and `relations::POSSESS_S_PLACEMENT` declare.

`R_Tag` asks for `beta_min` 443: at 439 its smallest MLWE rank (17, uSVP block size 442) misses
the estimator gate (the dual-hybrid attack costs 2^127.3, block size 436). At 443 the rank is 18
(uSVP 478, dual hybrid 2^137.4); 446 and 450 give the same set but for its `id` and `estimator`.

| set | proof modulus (prime, ≡ 5 mod 8) | MLWE rank; uSVP block size; cheapest attack of lattice-estimator (rough) | MSIS block size; lattice-estimator (rough) | estimated proof bytes |
|---|---|---|---|---|
| `tag` | 44,737,418,205,541 (≈ 2^45.35) | 18; 478; dual hybrid 2^137.37 | 459; 2^134.03 | 29,168 |
| `att` | 800,602,353,498,606,932,557 (≈ 2^69.44) | 26; 447; dual hybrid 2^129.36 | 456; 2^133.15 | 90,216 |
| `iss` | 381,754,410,435,781 (≈ 2^48.44) | 19; 471; dual hybrid 2^135.78 | 440; 2^128.48 | 46,208 |
| `possess` | 800,602,353,498,606,932,557 (≈ 2^69.44) | 26; 447; dual hybrid 2^129.36 | 457; 2^133.44 | 84,904 |

The estimates in the last column are those of the derivation, with Jali 0.1. Since Jali 0.2.0
every field of a proof has a fixed width and `estimated_proof_bytes` is the exact size of every
proof: 29,112, 90,168, 46,152 and 84,856 bytes for these sets, which are unchanged.

The three components of `x_0` are 48 binary rows of the Ajtai part at proof degree 128 (two bits
per ternary coefficient), 16 more than the two of the first port, and the lower bound on `‖s‖²`
adds one row to each of `R_att` and `R_Possess`: the first port's estimates were 85,608 bytes for
`R_att`, 39,472 for `R_iss` and 78,424 for `R_Possess`. The statistical variant, `ℓ_r = 13` for
the regularity bound, needed 208 rows and sets estimated at 141,416, 98,132 and 136,104 bytes
(derived on 2026-10-18 by the same tool and policy, and not kept).

## Reproducing the sets

The derivation of 2026-10-18 (17:27 CST) used Jali at revision
`5ee737bb85c404327118aaec109d7802eb1db90b`, whose library code the pinned release Jali 0.1.0
has (tool version `jali-params 3`; the tool is not in the crates.io package), run by SageMath 10.9
(its Python 3.14.3, with mpmath 1.4.1 and sympy 1.14.0) for the derivation and the estimator gate,
and lattice-estimator at `53da5982597709ba0fdf94ea37a84d822310fd84`. The set for `R_Tag` and its
report came out byte for byte as committed. An earlier derivation of the same day (for the
statistical variant) also ran in Python 3.12.13 with the pinned packages of Jali's
`tools/requirements.txt` (mpmath 1.3.0, sympy 1.14.0, pycryptodome 3.23.0) and derived the same
sets as SageMath.

```sh
# 1. the exports (from the repository root)
PCREDS_EXPORT_DIR=tools/lattice/sets cargo test --release --features lattice --lib -- \
    --ignored export_requirements
# 2. the requests
python3 tools/lattice/sets/make_requests.py
# 3. the sets and reports, with the estimator gate (in a clone of Jali at 5ee737b)
git clone https://github.com/malb/lattice-estimator
git -C lattice-estimator checkout 53da5982597709ba0fdf94ea37a84d822310fd84
for n in tag att iss possess; do
  JALI_LATTICE_ESTIMATOR_DIR=$PWD/lattice-estimator sage -python $JALI/tools/params/lnp_params.py \
      derive tools/lattice/sets/$n.request.json --estimator-target 128 \
      --params $n.json --report tools/lattice/sets/$n.report.json
done
# 4. the primality proofs of the moduli
sage -c "import json
for n in ['tag', 'att', 'iss', 'possess']:
    q = Integer(json.load(open(n + '.json'))['prime_factors'][0])
    print(n, q, q.is_prime(proof=True), q % 8)"
# 5. install: copy <n>.json to src/lattice/sets/params-<n>-lr3-beta<b>.json (tag:
#    params-tag-beta443.json) and update the pins, ids and bounds in src/lattice/sets.rs
```

The reports record the hashes of the tool's files and of the request, and an `environment`
block; `estimator` strings start with the tool's version and enter Jali's transcript.

## Extraction sets

The default, extractable build (plain with the feature `lattice-plain`) proves in Jali's straight-line extractable
mode (Katsumata's transform), which takes an extraction set besides each parameter set: the rank
`n'` and the modulus `q'` of the LinHC commitment to the final opening's witness, `m'`
polynomials of degree 128 (`m' = m1 + |l2_rows| + m2 - n_msis`). They are embedded in
`src/lattice/sets/` as `extraction-<set>.json`, pinned by SHA-256 (`src/lattice/sets.rs`), and
checked by Jali against their parameter sets, which derive the modulus again from the rank.

The policy is that of the parameter sets. Jali's tool (`lnp_params.py extraction`) takes the
least rank whose MLWE estimate (uSVP, ADPS16) reaches block size 439 (443 for `tag`, as its
parameter set) at the modulus that the rank gives, and lattice-estimator's rough mode must then
reach 128 bits on the commitment's hiding instance, MLWE of rank `n'` with `2m'` samples (Jali's
`docs/security.md`, "Straight-line extraction", step 6). `att` asks for block size 444: at 439
its rank is 23, and the dual hybrid attack costs 2^127.9 there. The second instance, keys with a
trapdoor, is MLWE of rank `m'` with `n'` samples (step 2). The rough mode finds no attack at that
number of samples, so it is priced with `m'` samples per secret coefficient instead, more than a
key gives, which bounds the instance from below.

| set | `m'` | `n'` | `q'` | hiding instance, cheapest attack (rough) | key instance | LinHC part (estimate) | extractable proof (estimate) |
|---|---|---|---|---|---|---|---|
| `tag` | 52 | 22 | 176,371,585,881,524,249 (≈ 2^57.29) | dual hybrid 2^132.9 (β 455), uSVP 2^134.6 | dual hybrid 2^402.1 | 140,864 | 170,032 (5.83 × 29,168) |
| `att` | 149 | 24 | 3,857,128,248,596,167,189 (≈ 2^61.74) | dual hybrid 2^135.5 (β 464), uSVP 2^136.9 | no finite cost, uSVP block size 4649 | 414,112 | 504,328 (5.59 × 90,216) |
| `iss` | 101 | 23 | 2,036,323,750,691,491,993 (≈ 2^60.82) | dual hybrid 2^130.5 (β 447), uSVP 2^132.0 | no finite cost, uSVP block size 2972 | 279,952 | 326,160 (7.06 × 46,208) |
| `possess` | 139 | 23 | 3,606,003,552,620,118,107 (≈ 2^61.65) | dual hybrid 2^128.2 (β 439), uSVP 2^129.6 | no finite cost, uSVP block size 4289 | 386,544 | 471,448 (5.55 × 84,904) |

"No finite cost" is the rough mode's output for those key instances. The block sizes next to it
come from the primal uSVP condition of ADPS16, which `extraction_estimate.sage` evaluates as well
and which reproduces the estimator's uSVP block size in every case where the estimator gives a
finite cost (the five above). The LinHC part of a proof is `t_1` and `t_2`,
`2m' · 128 · bits(q' - 1)` bits, and `z'`, `(n' + 2m') · 128` coefficients of `t' + 4` bits each,
Jali's fixed width since 0.2.0, so the sizes are exact (`extraction_sizes.py`). Jali 0.1 used
variable-length codes, and the table's figures were then estimates at `ceil(log2(σ') + 2.5)`
bits per coefficient, the same width. With Jali 0.2.0 the extractable proofs are 169,976,
504,280, 326,104 and 471,400 bytes, the plain proofs being 56, 48, 56 and 48 bytes shorter than
estimated. The bound of a proof in the extractable build is twice the size of the extractable
proof.

### Reproducing the extraction sets

The derivation of 2026-11-15 (UTC) used Jali at `976c9bd` (the release 0.1.1, tool version
`jali-params 3`) in Python 3.12.13 with the pinned packages of Jali's `tools/requirements.txt`,
and SageMath 10.9 with lattice-estimator at `53da5982597709ba0fdf94ea37a84d822310fd84` for the
estimates.

```sh
# 1. the sets (from the repository root, in a clone of Jali at 976c9bd)
for pair in tag-beta443:443 att-lr3-beta439:444 iss-lr3-beta439:439 possess-lr3-beta439:439; do
  n=${pair%%:*}; b=${pair##*:}
  python3 $JALI/tools/params/lnp_params.py extraction src/lattice/sets/params-$n.json \
      --policy beta --beta-min $b --output src/lattice/sets/extraction-$n.json
done
# 2. the estimates of both instances (lattice-estimator checkout as above)
sage tools/lattice/extraction_estimate.sage lattice-estimator
# 3. the sizes of the LinHC parts, the *_LINHC_BYTES constants of src/lattice/sets.rs
python3 tools/lattice/sets/extraction_sizes.py $JALI
# 4. install: update the pins in src/lattice/sets.rs
```

## The tag's own hardness

`Tag_LWR` with a short key is decisional LWR with a ternary secret and any number of samples, an
assumption the paper takes directly (no reduction from LWE reaches this regime). Read as LWE with
a uniform error on `[-7, 7]` (the rounding error of `γ = 15`), lattice-estimator at the commit
above prices it at 2^151.7 in rough mode (dual hybrid, block size 518; uSVP 2^157.4) and 2^175.5
with the default attacks (dual hybrid; BDD 2^179.4, uSVP 2^182.0), and the Arora–Ge attack at
2^219.8. `lwr_estimate.sage` (in `tools/lattice/`) reproduces these figures:
`sage tools/lattice/lwr_estimate.sage <lattice-estimator checkout>`.

## The hiding of the request

The request `C = b_u usk + B_r x_0` is pseudorandom under the knapsack form of
`MLWE_{ℓ_r, q, D_r}` (lem:base-vsis (b)): after a division by `B_r[0]`, module LWE with one
sample, a ternary secret of rank `ℓ_r - 1` and a ternary error, at `d = 1024`, `q = 2^20 - 3`.
lattice-estimator at the commit above prices it in rough mode at 2^344.9 for `ℓ_r = 3` (uSVP,
block size 1181) and at 2^130.8 for `ℓ_r = 2` (dual hybrid, block size 448), which leaves under
three bits above 128 before the factor `2 Q_iss` of the theorem. `hiding_estimate.sage` (in
`tools/lattice/`) reproduces these figures:
`sage tools/lattice/hiding_estimate.sage <lattice-estimator checkout>`.
