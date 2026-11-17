# The hiding of the issuance request C = b_u usk + B_r x_0 of the lattice backend, as
# lattice-estimator prices it. lem:base-vsis (b) rests on the knapsack form of
# MLWE_{l_r, q, D_r}: (B_r, B_r x_0) is pseudorandom for uniform B_r in R_q^{1 x l_r} and x_0
# uniform on ternary vectors (the computational hiding of BLNS23, Thm. 8.2). Dividing by B_r[0]
# (a unit except with probability about 2 q^-512) gives LWE in normal form with one ring sample:
# secret x_0[1..] of dimension (l_r - 1) d, error x_0[0], d = 1024 samples, q = 2^20 - 3.
# Run with a checkout of lattice-estimator (the parameter sets used commit
# 53da5982597709ba0fdf94ea37a84d822310fd84):
#
#     sage tools/lattice/hiding_estimate.sage <lattice-estimator checkout>
#
# Output of 2026-10-18 (SageMath 10.9), rough mode: l_r = 3 (this backend) 2^344.9 (uSVP, beta
# 1181; dual hybrid 2^740.4); l_r = 2 2^130.8 (dual hybrid, beta 448; uSVP 2^134.6).
import sys
sys.path.insert(0, sys.argv[1])
from estimator import *

d, q = 1024, 1048573
for l_r in (3, 2):
    params = LWE.Parameters(n=(l_r - 1) * d, q=q, Xs=ND.Uniform(-1, 1), Xe=ND.Uniform(-1, 1), m=d,
                            tag="MLWE knapsack, l_r = %d" % l_r)
    print(params)
    print("rough:")
    LWE.estimate.rough(params)
    sys.stdout.flush()
