#!/usr/bin/env python3
"""The size of the LinHC part of an extractable Jali proof for each relation of the lattice
backend (its default build), the figures behind the `*_LINHC_BYTES` constants of
src/lattice/sets.rs.

An extractable proof (Jali 0.2.0, `codec::proof::encode_extractable`) is the plain proof with t_1
and t_2 at the end of its first message (m' polynomials each, every coefficient modulo q' in
bits(q' - 1) bits) and z'_1, z'_2, z'_3 at its end (n', m' and m' polynomials, every coefficient
in the fixed width t' + 4 bits, Jali's code for the width 1.55 * 2^t'). Every field has a fixed
width, so the sizes are exact. Jali 0.1 used variable-length Gaussian codes, and these figures
were its estimate, ceil(log2(sigma') + 2.5) = t' + 4 bits per coefficient, the same number. The
derived LinHC parameters (m', the message bound B, eta, t', q') come from the code of Jali's
parameter tool, which the crate's derivation agrees with exactly. Run from the repository root
with a checkout of Jali (tools/params is not in the crates.io package):

    python3 tools/lattice/sets/extraction_sizes.py <Jali checkout>
"""
import json
import math
import os
import sys

sys.path.insert(0, os.path.join(sys.argv[1], "tools", "params"))
from jali_params import extraction, rustcheck  # noqa: E402

SETS = os.path.join("src", "lattice", "sets")
NAMES = ["tag-beta443", "att-lr3-beta439", "iss-lr3-beta439", "possess-lr3-beta439"]

for name in NAMES:
    with open(os.path.join(SETS, f"params-{name}.json")) as f:
        params, _, _ = rustcheck.from_json(f.read())
    with open(os.path.join(SETS, f"extraction-{name}.json")) as f:
        ext = json.load(f)
    derived, _ = rustcheck.check_params(params)
    length, bound, eta, d = extraction.shape(params)
    rank = ext["rank"]
    linhc = extraction.linhc(d, rank, length, bound, eta)
    q = linhc["modulus"]
    if q != int(ext["modulus"]):
        sys.exit(f"{name}: the extraction set's modulus is not the derived one")
    t = linhc["log_sigma"]
    gaussian = t + 4
    assert gaussian == math.ceil(math.log2(1.55 * 2 ** t) + 2.5)
    uniform_bits = 2 * length * d * (q - 1).bit_length()
    gaussian_bits = (rank + 2 * length) * d * gaussian
    assert (uniform_bits + gaussian_bits) % 8 == 0
    linhc_bytes = (uniform_bits + gaussian_bits) // 8
    plain = derived["estimated_proof_bytes"]
    print(f"{name}: m' = {length}, n' = {rank}, d = {d}, bits(q' - 1) = {(q - 1).bit_length()}, "
          f"t' = {t}, {gaussian} bits per Gaussian coefficient: LinHC part {linhc_bytes} bytes "
          f"(t_1, t_2 {uniform_bits // 8}, z' {gaussian_bits // 8}), plain proof {plain}, "
          f"extractable proof {plain + linhc_bytes} ({(plain + linhc_bytes) / plain:.2f} times)")
