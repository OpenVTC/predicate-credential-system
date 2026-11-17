# The hardness of the short-key Tag_LWR of the lattice backend, as lattice-estimator prices it:
# decisional LWR with a ternary secret (n = 1024) and any number of samples, read as LWE modulo
# q_t = 983,040 with a uniform error on [-7, 7], the rounding error of floor(p x / q_t) for
# gamma = q_t / p = 15 (tag-instantiations.tex: "concrete parameters rest on cryptanalysis").
# Run with a checkout of lattice-estimator (the parameter sets used commit
# 53da5982597709ba0fdf94ea37a84d822310fd84):
#
#     sage tools/lattice/lwr_estimate.sage <lattice-estimator checkout>
#
# Output of 2026-10-18 (SageMath 10.9): rough 2^151.7 (dual hybrid, beta 518; uSVP 2^157.4),
# default attacks 2^175.5 (dual hybrid; BDD 2^179.4, uSVP 2^182.0), Arora-Ge 2^219.8.
import sys
sys.path.insert(0, sys.argv[1])
from estimator import *

params = LWE.Parameters(n=1024, q=983040, Xs=ND.Uniform(-1, 1), Xe=ND.Uniform(-7, 7), m=oo,
                        tag="Tag_LWR short key")
print(params)
print("rough:")
LWE.estimate.rough(params)
print("default attacks:")
LWE.estimate(params, deny_list=("arora-gb",))
print("arora-gb:")
print(LWE.arora_gb(params))
