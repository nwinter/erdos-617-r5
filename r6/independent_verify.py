#!/usr/bin/env python3
"""FULLY INDEPENDENT verification (exhaustive itertools; no clever clique search)
of a class-0 candidate: symmetric, 0-diagonal, edge count, alpha<=5 (no independent
6-set), omega<=5 (no K_6), cap-16 (every 7-set <=16 edges)."""
import json, sys
import numpy as np
from itertools import combinations
path = sys.argv[1] if len(sys.argv) > 1 else "data/r6/candidates/class0_n31_k6free_best.json"
d = json.load(open(path)); A = np.array(d["adj"], dtype=np.int64); n = d["n"]
print(f"file: {path}  claims n={n}, m={d.get('m','?')}")
# structural sanity
assert A.shape == (n, n), "shape"
assert (A == A.T).all(), "NOT SYMMETRIC"
assert (np.diag(A) == 0).all(), "NONZERO DIAGONAL"
assert ((A == 0) | (A == 1)).all(), "non-0/1 entries"
m = int(A.sum() // 2); print(f"  symmetric, 0-diagonal, 0/1: OK.  edges m = {m}")

# alpha<=5: NO independent 6-set (exhaustive over all 6-subsets)
indep6 = None
for S in combinations(range(n), 6):
    ok = True
    for a, b in combinations(S, 2):
        if A[a, b]: ok = False; break
    if ok: indep6 = S; break
print(f"  alpha<=5 (no independent 6-set): {'OK' if indep6 is None else 'FAIL '+str(indep6)}")

# omega<=5: NO K_6 (exhaustive over all 6-subsets)
k6 = None
for S in combinations(range(n), 6):
    ok = True
    for a, b in combinations(S, 2):
        if not A[a, b]: ok = False; break
    if ok: k6 = S; break
print(f"  omega<=5 (K_6-free):            {'OK' if k6 is None else 'FAIL '+str(k6)}")

# cap-16: every 7-set spans <=16 edges (numpy, exhaustive)
sevens = np.array(list(combinations(range(n), 7)))
ec = np.zeros(len(sevens), dtype=np.int64)
for i in range(7):
    for j in range(i + 1, 7):
        ec += A[sevens[:, i], sevens[:, j]]
mx = int(ec.max()); bad = int((ec > 16).sum())
print(f"  cap-16 (max edges in a 7-set):  max={mx}  violations={bad}  {'OK' if bad == 0 else 'FAIL'}")

allok = indep6 is None and k6 is None and bad == 0
print(f"\n  INDEPENDENT VERDICT: {'*** VALID: alpha<=5, omega<=5, cap-16 ALL CLEAN ***' if allok else '*** INVALID ***'}")
print(f"  => m*(alpha<=5,omega<=5,cap-16) <= {m}  (constructive upper bound)" if allok else "")
