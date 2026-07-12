#!/usr/bin/env python3
"""Computational verification of the hand-proof counting framework for MH''.

Framework (see review_queue/mh2-handproof-wip.md):
G = G_0[V_out] on N vertices (N=21 for n=25; N=20 for n=24), conditions:
  alpha(G) <= 4;  for every v: alpha(G[W_v]) <= 3 where W_v = V_out minus
  N[v];  cap-11; K_6-free;  e(G) <= C(N,2) - 4*minTuran(other classes).

Counting identity (exact):  sum_v e(G[W_v]) = (N)e - sum d_v^2 + 3t.
Lower bound: sum_v f(N-1-d_v) where f(m) = min edges of alpha<=3 graph on m
vertices = C(m,2) - ex(m,K_4)  (complement Turan).
Cherry bound: 3t <= sum_v C(d_v,2).

This script:
 1. checks the identity and bounds EXACTLY on the verified n=24 witness
    (must be consistent - falsification guard);
 2. runs the degree-sequence LP (integer scan, no Jensen) for N=21 and N=20:
    for each e, is there any degree sequence making the necessary condition
      N*e - sum d^2 + sum C(d,2) >= sum f(N-1-d)   [uses 3t <= cherries]
    hold?  Reports the feasible e-window at each N.
Usage: .venv/bin/python tools/handproof_check.py [WITNESS24.json]
"""
import json, sys
from itertools import combinations
from functools import lru_cache


def turan_ex(m, r):
    """ex(m, K_{r+1}) = edges of Turan graph T_r(m)."""
    q, s = divmod(m, r)
    # s parts of size q+1, r-s of size q
    intra = s * (q + 1) * q // 2 + (r - s) * q * (q - 1) // 2
    return m * (m - 1) // 2 - intra


def f3(m):
    """min edges with alpha <= 3 on m vertices (complement K_4-free)."""
    if m <= 3:
        return 0
    return m * (m - 1) // 2 - turan_ex(m, 3)


def witness_check(path):
    d = json.load(open(path))
    M, n = d["colours"], d["n"]
    Vout = list(range(4, n))
    N = len(Vout)
    adj = {v: set() for v in Vout}
    for i in Vout:
        for j in Vout:
            if i != j and M[i][j] == 0:
                adj[i].add(j)
    e = sum(len(adj[v]) for v in Vout) // 2
    deg = {v: len(adj[v]) for v in Vout}
    t = 0
    for a, b, c in combinations(Vout, 3):
        if b in adj[a] and c in adj[a] and c in adj[b]:
            t += 1
    lhs = sum(1 for v in Vout for x, y in combinations(sorted(set(Vout) - {v} - adj[v]), 2)
              if y in adj[x])
    ident = N * e - sum(deg[v] ** 2 for v in Vout) + 3 * t
    rhs = sum(f3(N - 1 - deg[v]) for v in Vout)
    cherries = sum(deg[v] * (deg[v] - 1) // 2 for v in Vout)
    print(f"witness {path}: N={N}, e={e}, t={t}, degs={sorted(deg.values())}")
    print(f"  identity check: sum e(W_v) = {lhs}  vs  Ne - sumd^2 + 3t = {ident}  "
          f"{'OK' if lhs == ident else 'MISMATCH!!'}")
    print(f"  lower bound sum f(N-1-d) = {rhs}  (<= {lhs}? {'OK' if rhs <= lhs else 'VIOLATED - framework wrong!'})")
    print(f"  cherry bound: 3t = {3*t} <= {cherries}  {'OK' if 3*t <= cherries else 'VIOLATED'}")
    # per-vertex alpha(W_v) <= 3 direct check
    ok = True
    for v in Vout:
        W = sorted(set(Vout) - {v} - adj[v])
        for S in combinations(W, 4):
            if not any(y in adj[x] for x, y in combinations(S, 2)):
                ok = False
                break
        if not ok:
            break
    print(f"  per-vertex alpha(G[W_v])<=3: {'holds for all v' if ok else 'FAILS (witness not h4?)'}")


def lp_scan(N, dmax=12):
    """For each e: exists degree sequence (integers, sum=2e) with
    N*e - sum d^2 + sum C(d,2) >= sum f3(N-1-d)?  Greedy/DP over per-vertex
    'profit' p(d) = -d^2 + C(d,2) - f3(N-1-d); need  N*e + sum_v p(d_v) >= 0
    with sum d_v = 2e. Maximize sum p subject to sum d = 2e via DP."""
    emin = None
    # per-class Turan floor for the other 4 classes on N vertices:
    others_min = 4 * (N * (N - 1) // 2 - turan_ex(N, 5))
    emax_budget = N * (N - 1) // 2 - others_min
    feas = []
    p = {d: -d * d + d * (d - 1) // 2 - f3(N - 1 - d) for d in range(dmax + 1)}
    for e in range(0, emax_budget + 1):
        # maximize sum_v p(d_v), sum d_v = 2e, N vertices: DP
        NEG = -10 ** 9
        dp = [NEG] * (2 * e + 1)
        dp[0] = 0
        for _ in range(N):
            nd = [NEG] * (2 * e + 1)
            for s in range(2 * e + 1):
                if dp[s] == NEG:
                    continue
                for d in range(min(dmax, 2 * e - s) + 1):
                    val = dp[s] + p[d]
                    if val > nd[s + d]:
                        nd[s + d] = val
            dp = nd
        best = dp[2 * e]
        if best != NEG and N * e + best >= 0:
            feas.append(e)
    print(f"N={N}: budget e<= {emax_budget}; necessary-condition-feasible e: "
          f"{feas[:3]}..{feas[-3:] if len(feas)>3 else feas} ({len(feas)} values)"
          if feas else f"N={N}: NO feasible e — framework alone would prove MH'' at this N (check!)")
    return feas


def g2(m):
    """min edges with alpha <= 2 on m vertices (complement triangle-free)."""
    if m <= 2:
        return 0
    return m * (m - 1) // 2 - (m * m // 4)


def fstar(m, dmax=None):
    """Improved lower bound for e(H), H on m vertices with alpha(H) <= 3 AND
    the level-2 per-vertex conditions alpha(H[W_u]) <= 2 (floors g2).
    Necessary condition: m*e - sum d^2 + sum C(d,2) >= sum g2(m-1-d).
    Returns the smallest e admitting a degree sequence, floored at f3(m)."""
    if dmax is None:
        dmax = m - 1
    p = {d: -d * d + d * (d - 1) // 2 - g2(m - 1 - d) for d in range(dmax + 1)}
    lo = f3(m)
    for e in range(lo, m * (m - 1) // 2 + 1):
        NEG = -10 ** 9
        dp = [NEG] * (2 * e + 1)
        dp[0] = 0
        for _ in range(m):
            nd = [NEG] * (2 * e + 1)
            for s in range(2 * e + 1):
                if dp[s] == NEG:
                    continue
                for d in range(min(dmax, 2 * e - s) + 1):
                    if dp[s] + p[d] > nd[s + d]:
                        nd[s + d] = dp[s] + p[d]
            dp = nd
        if dp[2 * e] != NEG and m * e + dp[2 * e] >= 0:
            return e
    return m * (m - 1) // 2


def lp_scan2(N, dmax=14):
    """Level-1 scan using the level-2-improved floors fstar."""
    F = {m: max(f3(m), fstar(m)) for m in range(0, N)}
    print(f"N={N}: floors f vs f*: " +
          ", ".join(f"{m}:{f3(m)}/{F[m]}" for m in range(12, N)))
    others_min = 4 * (N * (N - 1) // 2 - turan_ex(N, 5))
    emax_budget = N * (N - 1) // 2 - others_min
    p = {d: -d * d + d * (d - 1) // 2 - F[N - 1 - d] for d in range(dmax + 1)}
    feas = []
    for e in range(0, emax_budget + 1):
        NEG = -10 ** 9
        dp = [NEG] * (2 * e + 1)
        dp[0] = 0
        for _ in range(N):
            nd = [NEG] * (2 * e + 1)
            for s in range(2 * e + 1):
                if dp[s] == NEG:
                    continue
                for d in range(min(dmax, 2 * e - s) + 1):
                    if dp[s] + p[d] > nd[s + d]:
                        nd[s + d] = dp[s] + p[d]
            dp = nd
        if dp[2 * e] != NEG and N * e + dp[2 * e] >= 0:
            feas.append(e)
    if feas:
        print(f"N={N} (level-2 floors): feasible e window: [{feas[0]}, {feas[-1]}] ({len(feas)} values)")
    else:
        print(f"N={N} (level-2 floors): WINDOW EMPTY — necessary conditions unsatisfiable!")
    return feas


if __name__ == "__main__":
    if len(sys.argv) > 1:
        witness_check(sys.argv[1])
    for N in (20, 21):
        lp_scan(N)
    for N in (20, 21):
        lp_scan2(N)
