#!/usr/bin/env python3
"""Writes the requests of Jali's parameter tool for the relations of the lattice backend.

Input: `<name>.export.json` (in this directory), the output of the ignored unit test
`pcreds::lattice::relations::tests::export_requirements`: `Statement::requirements` and
`Statement::blocks` of the relation at its worst-case public data, at proof degree 128 and a
probe modulus that no constraint uses. Output: `<name>.request.json`, a request of schema
`jali-params-request/2` for `lnp_params.py derive` (README.md in this directory).

The policy is the one of the earlier sets of this crate: block sizes at least 439 (128 classical
bits under core-SVP for both the MLWE and the MSIS estimate), a single prime proof modulus
found by the tool's search, and the set refused unless lattice-estimator's rough mode reaches
128 bits (`--estimator-target 128`). For `R_Tag` the smallest MLWE rank at `beta_min` 439 (17,
uSVP block size 442) misses that gate: the dual-hybrid attack costs 2^127.3 (block size 436).
Its request asks for `beta_min` 443, which moves it to rank 18 (uSVP 478, dual hybrid 2^137.4).
`s` is movable in `R_att` and `R_Possess` (the tool chooses its part of the commitment); every
other block stays where the export declares it.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
STATEMENT_MODULUS = 1_048_573  # q = 2^20 - 3, the modulus of the statement ring
RELATIONS = {
    "tag": ("pcreds128-g15-k16-mdef-d128-tag-beta443", "R_Tag (pi_id)", None, 443),
    "att": ("pcreds128-g15-k16-mdef-d128-lr3-att-beta439", "R_att (pi_att)", ["s"], 439),
    "iss": ("pcreds128-g15-k16-mdef-d128-lr3-iss-beta439", "R_iss (pi_iss)", None, 439),
    "possess": ("pcreds128-g15-k16-mdef-d128-lr3-possess-beta439", "R_Possess (pi_prove)",
                ["s"], 439),
}

# What else the relation depends on. R_Tag's note is that of its first derivation (beta_r does
# not enter R_Tag), so that its request, and with it its set, stay byte for byte the same.
NOTES = {
    "tag": "beta_r 1",
    "att": "x_0 ternary, ell_r 3; 1 <= ||s||^2 <= floor(beta_s^2)",
    "iss": "x_0 ternary, ell_r 3",
    "possess": "x_0 ternary, ell_r 3; 1 <= ||s||^2 <= floor(beta_s^2)",
}


def request(name):
    set_id, what, movable, beta_min = RELATIONS[name]
    export = json.loads((HERE / f"{name}.export.json").read_text())
    statement = {
        "source": "requirements",
        "requirements": export["requirements"],
        "statement_modulus": STATEMENT_MODULUS,
        "blocks": export["blocks"],
    }
    if movable:
        statement["movable"] = movable
    return {
        "schema": "jali-params-request/2",
        "id": set_id,
        "mode": "native",
        "degree": 128,
        "modulus": {"search": {"factors": 1}},
        "hardness": {"policy": "beta", "beta_min": beta_min},
        "statement": statement,
        "note": f"{what} of the lattice backend of predicate-credential-system "
                f"(tag set R: gamma 15, p 2^16, q_t 983040, m 168; {NOTES[name]}), "
                "exported at worst-case public data",
    }


def main():
    names = sys.argv[1:] or list(RELATIONS)
    for name in names:
        path = HERE / f"{name}.request.json"
        path.write_text(json.dumps(request(name), indent=2) + "\n")
        print(f"wrote {path.name}")


if __name__ == "__main__":
    main()
