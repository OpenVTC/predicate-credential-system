# The two MLWE instances behind each extraction set of the lattice backend (its default,
# extractable build), as lattice-estimator prices them. An extraction set fixes the rank n'
# and the modulus q' of Jali's LinHC commitment (Katsumata's construction 1, MLWE), which commits
# to the m' polynomials of degree d of the final opening's witness with ternary randomness:
#
#   hiding: (t_1, t_2) = (p(A s'_1 + s'_2), p(B s'_1 + s'_3) + e) is pseudorandom under MLWE of
#     rank n' with 2m' samples (Jali's docs/security.md, "Straight-line extraction", step 6):
#     LWE with secret dimension n' d and 2 m' d samples.
#   key: a key (A, D_1 A + D_2) with a trapdoor looks uniform under MLWE with the rows of D_1 as
#     secrets, of rank m' with n' samples (step 2): LWE with secret dimension m' d and n' d
#     samples. With so few samples the rough mode finds no attack (it prices them at infinity),
#     so the instance is priced with m' d samples, more than a key gives. An attacker can always
#     ignore samples, so the instance itself costs at least as much.
#
# Secrets and errors are uniform on {-1, 0, 1}. m' = m1 + |l2_rows| + m2 - n_msis is read from
# the parameter set. Each instance is also priced by the primal uSVP condition of ADPS16
# (sigma sqrt(beta) <= delta^(2 beta - D - 1) q^(m/D), D = n + m + 1, over the number m of
# samples used), which reproduces the estimator's uSVP block sizes wherever the estimator
# returns a finite cost. Run with a checkout of lattice-estimator (the sets used commit
# 53da5982597709ba0fdf94ea37a84d822310fd84), from the repository root:
#
#     sage tools/lattice/extraction_estimate.sage <lattice-estimator checkout>
#
# Output of 2026-11-15 UTC (SageMath 10.9), rough mode, cheapest attack on the hiding instance: tag
# 2^132.9 (dual hybrid, beta 455, uSVP 2^134.6), att 2^135.5 (dual hybrid, beta 464, uSVP
# 2^136.9), iss 2^130.5 (dual hybrid, beta 447, uSVP 2^132.0), possess 2^128.2 (dual hybrid,
# beta 439, uSVP 2^129.6). Key instances: tag 2^402.1 (dual hybrid, beta 1377, uSVP 2^412.3),
# att, iss and possess no finite cost, with ADPS16 uSVP block sizes 4649, 2972 and 4289.
import json
import math
import os
import sys

sys.path.insert(0, sys.argv[1])
from estimator import *

SETS = os.path.join("src", "lattice", "sets")
NAMES = ["tag-beta443", "att-lr3-beta439", "iss-lr3-beta439", "possess-lr3-beta439"]


def delta(b):
    b = float(b)
    return ((math.pi * b) ** (1.0 / b) * b / (2.0 * math.pi * math.e)) ** (1.0 / (2.0 * (b - 1.0)))


def usvp_beta(n, q, max_m):
    """The least block size of the ADPS16 uSVP condition over m <= max_m (steps of 64)."""
    sigma, logq, best = math.sqrt(2.0 / 3.0), float(math.log2(q)), None
    for m in range(256, int(max_m) + 1, 64):
        d = int(n) + m + 1

        def ok(b):
            return (math.log(sigma) + 0.5 * math.log(b)
                    <= (2 * b - d - 1) * math.log(delta(b)) + float(m) / d * logq * math.log(2.0))

        lo, hi = 50, d
        if not ok(hi):
            continue
        while hi - lo > 1:
            mid = (lo + hi) // 2
            lo, hi = (lo, mid) if ok(mid) else (mid, hi)
        best = hi if best is None else min(best, hi)
    return best


for name in NAMES:
    params = json.load(open(os.path.join(SETS, "params-%s.json" % name)))
    ext = json.load(open(os.path.join(SETS, "extraction-%s.json" % name)))
    d = params["degree"]
    length = params["m1"] + len(params["l2_rows"]) + params["m2"] - params["n_msis"]
    rank, q = ext["rank"], int(ext["modulus"])
    print("%s: d = %d, m' = %d, n' = %d, q' = %d (2^%.2f)" % (name, d, length, rank, q,
                                                             float(math.log2(q))))
    for what, n, m in (("hiding", rank * d, 2 * length * d), ("key", length * d, length * d)):
        lwe = LWE.Parameters(n=n, q=q, Xs=ND.Uniform(-1, 1), Xe=ND.Uniform(-1, 1), m=m,
                             tag="%s %s" % (name, what))
        print(lwe)
        print("rough:")
        LWE.estimate.rough(lwe)
        b = usvp_beta(n, q, m)
        print("ADPS16 uSVP: beta %d, 2^%.1f" % (b, 0.292 * b))
        sys.stdout.flush()
