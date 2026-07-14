#!/usr/bin/env python3
"""HYBRID assessment: can route A's cap-recursion DP sharpen route B's density floors
(the L_r(|D|) complementary-Turan bounds in section 7) enough to shrink the surviving
table rows?  G (minority graph) has alpha<=r, omega<=r (K_{r+1} capped), cap-16.  So
G[D] admits a DP bound P_r(m) with alpha<=r, omega<=r, cap-16 -- possibly > L_r(m)."""
from math import comb
from routeB_arith import turan, L, comb as _c

INF = float('inf')
CAP = {5: 11, 6: 16}


def b(r, d):
    C = CAP[r]
    if d < r:
        return comb(d, 2)
    return (C - r) * d * (d - 1) // (r * (r - 1))


def ex_Kt(n, t):
    return turan(n, t - 1)


def u(r, d):
    # omega(G) <= r  => N(v) is K_r-free  => e(N(v)) <= ex(d, K_r) = t_{r-1}(d)
    return min(b(r, d), ex_Kt(d, r))


def dp_min(r, q, Pprev):
    tp = {}
    for d in range(q):
        w = q - 1 - d
        if 0 <= w < len(Pprev) and Pprev[w] != INF:
            tp[d] = 2 * Pprev[w] + 2 * d * d - q * d - 2 * u(r, d)
    if not tp:
        return INF
    feas = sorted(tp)
    for m in range(0, q * (q - 1) // 2 + 1):
        t = 2 * m
        dp = [INF] * (t + 1)
        dp[0] = 0
        for _ in range(q):
            nd = [INF] * (t + 1)
            for acc in range(t + 1):
                if dp[acc] == INF:
                    continue
                for d in feas:
                    if acc + d <= t and dp[acc] + tp[d] < nd[acc + d]:
                        nd[acc + d] = dp[acc] + tp[d]
            dp = nd
        if dp[t] != INF and dp[t] <= 0:
            return m
    return INF


def P_table(r, a_max, q_max):
    """alpha<=a, omega<=r, cap-CAP[r]."""
    omega = r
    P = {1: [0 if q == 0 else (comb(q, 2) if q <= omega else INF) for q in range(q_max + 1)]}
    for a in range(2, a_max + 1):
        Pa = [INF] * (q_max + 1)
        Pa[0] = 0
        for q in range(1, q_max + 1):
            dp = dp_min(r, q, P[a - 1])
            direct = comb(q, 2) - turan(q, a)          # complementary Turan (alpha<=a)
            Pa[q] = max(direct, dp) if dp != INF else direct
        P[a] = Pa
    return P


def compare(r):
    n = r * r + 1
    emax = comb(n, 2) // r
    # D-sizes appearing in the section-7 table
    P = P_table(r, r, n)
    print(f"  r={r}: DP P_{r}(m) [alpha<=r, omega<=r, cap-{CAP[r]}] vs L_{r}(m) [complementary Turan]:")
    Dsizes = sorted(set(n - (r - 1) - c for c in range(1, r + 1)))
    for m in Dsizes:
        dpv = P[r][m]
        lv = L(m, r)
        boost = dpv - lv
        print(f"    m={m:3d}: L_{r}={lv:3d}  DP={dpv:3d}  boost={boost:+d}")
    # recompute the section-7 table with DP floor instead of L_r, count surviving rows
    from routeB_arith import stability
    st = stability(r)
    Pstar = r * r
    hand_L = 0
    hand_DP = 0
    for row in st['rows']:
        sigma, c, D = row['sigma'], row['c'], row['D']
        # with DP floor
        budget_dp = emax - sigma - comb(c, 2) - P[r][D]
        maxP_dp = sigma + c - 1 + (budget_dp // c) if budget_dp >= 0 else -1
        if row['maxP'] > Pstar:
            hand_L += 1
        if budget_dp >= 0 and maxP_dp > Pstar:
            hand_DP += 1
    print(f"    section-7 rows needing hand-exclusion: with L_r floor = {hand_L}, "
          f"with DP floor = {hand_DP}  (DP {'shrinks' if hand_DP < hand_L else 'does NOT shrink'} the burden)")


if __name__ == "__main__":
    compare(5)
    print()
    compare(6)
