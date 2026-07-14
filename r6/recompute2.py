#!/usr/bin/env python3
"""r6/recompute2.py -- clean, correct cap-recursion DP (fixes the INF/nonexistence
handling of recompute.py's dp_min_edges) parameterised by r.

Rigorous objects:
  P_a(q) = min edges of a graph on q vertices with alpha<=a, omega<=r-1, cap-cap(r).
  The DP over degree sequences implements the NECESSARY condition
      sum_v Phi_a(d_v) <= 0,   Phi_a(d) = P_{a-1}(q-1-d) + d^2 - (q/2) d - u(d),
  where u(d) upper-bounds e(G[N(v)]) (cap + K_{r-1}-free) and P_{a-1} lower-bounds
  e(G[W_v]) (W_v = non-neighbourhood, alpha drops by 1).  It returns:
    * the least m for which SOME feasible degree multiset (sum=2m) meets sum Phi<=0
      -> a rigorous LOWER BOUND on P_a(q);
    * INF (nonexistence proof) if NO m up to C(q,2) admits such a multiset.
  This is the SAME method that PROVED M(12)=none at r=5 (SAT-confirmed).

We combine with:
  * complement-Turan / Brouwer direct lower bounds,
  * Ramsey nonexistence at the base (alpha<=2 & omega<=r-1 needs q<R(3,r)),
  * SAT-exact overrides (r=5 M-values; r=6 M6(9,10,11)) which only RAISE values.

VALIDATION: fed the r=5 SAT base this reproduces L(13..20)=24,31,38,46,53,62,73,84
and e(H)=P_4(21)=58 (the proven r=5 numbers).  Then applied to r=6.
"""
from math import comb

INF = float('inf')


# ---------- pinned combinatorics ----------
def cap(r):            return comb(r + 1, 2) - (r - 1)
def own_edge_cap(r):   return comb(r, 2) - (r - 1)
def minority(r):       return comb(r * r, 2) // r
def S_size(r):         return r * r - r + 1


def turan(n, parts):
    if parts <= 0:
        return 0
    q, s = divmod(n, parts)
    return comb(n, 2) - (s * comb(q + 1, 2) + (parts - s) * comb(q, 2))


def ex_Kt(n, t):       return turan(n, t - 1)


def b(r, d):
    if d < r:
        return comb(d, 2)
    return (cap(r) - r) * d * (d - 1) // (r * (r - 1))


def u(r, d):           return min(b(r, d), ex_Kt(d, r - 1))


# Ramsey numbers R(3,k): triangle-free graph with independence number < k exists
# iff n < R(3,k).  R(3,3..8) = 6,9,14,18,23,28.
R3 = {3: 6, 4: 9, 5: 14, 6: 18, 7: 23, 8: 28}


def dp_min_edges(r, q, Pprev):
    """Least m with a feasible degree multiset (q vertices, sum 2m) meeting
    sum 2*Phi <= 0; INF if none exists (nonexistence proof)."""
    twophi = {}
    for d in range(0, q):
        w = q - 1 - d
        if 0 <= w < len(Pprev) and Pprev[w] != INF:
            twophi[d] = 2 * Pprev[w] + 2 * d * d - q * d - 2 * u(r, d)
    if not twophi:
        return INF
    feas = sorted(twophi)
    maxm = q * (q - 1) // 2
    for m in range(0, maxm + 1):
        tgt = 2 * m
        dp = [INF] * (tgt + 1)
        dp[0] = 0
        for _ in range(q):
            nd = [INF] * (tgt + 1)
            for acc in range(tgt + 1):
                if dp[acc] == INF:
                    continue
                base = dp[acc]
                for d in feas:
                    if acc + d <= tgt and base + twophi[d] < nd[acc + d]:
                        nd[acc + d] = base + twophi[d]
            dp = nd
        if dp[tgt] != INF and dp[tgt] <= 0:
            return m
    return INF


def P_table(r, a_max, q_max, sat=None):
    """sat(a,q) -> exact min edges, or INF for 'no graph', or None if unknown."""
    omega = r - 1
    P = {1: [0 if q == 0 else (comb(q, 2) if q <= omega else INF) for q in range(q_max + 1)]}
    for a in range(2, a_max + 1):
        Pa = [INF] * (q_max + 1)
        Pa[0] = 0
        for q in range(1, q_max + 1):
            # Ramsey nonexistence at base level
            if a == 2 and q >= R3.get(r, 10 ** 9):
                Pa[q] = INF
                continue
            dp = dp_min_edges(r, q, P[a - 1])
            sv = sat(a, q) if sat else None
            if sv == INF or dp == INF:
                Pa[q] = INF
                continue
            direct = comb(q, 2) - turan(q, a)          # alpha<=a : complement K_{a+1}-free
            val = max(direct, dp)
            if sv is not None:
                val = max(val, sv)
            Pa[q] = val
        P[a] = Pa
    return P


# ---------- SAT overrides ----------
def r5_sat(a, q):
    if a != 2:
        return None
    if q <= 8:
        return comb(q, 2) - (q * q // 4)
    return {9: 19, 10: 25, 11: 35, 12: INF, 13: INF}.get(q, None)


def r6_sat(a, q):
    if a != 2:
        return None
    if q <= 8:
        return comb(q, 2) - (q * q // 4)
    return {9: 16, 10: 20, 11: 29}.get(q, None)   # SAT-exact; 12+ unknown -> None


# ---------- Brouwer ordinary-colour bounds ----------
def eF_brouwer(r):
    S = S_size(r)
    return comb(S, 2) - (turan(S, r) - (S // r) + 1)


# ---------- validation ----------
def validate_r5():
    P = P_table(5, 4, 21, sat=r5_sat)
    claims = {13: 24, 14: 31, 15: 38, 16: 46, 17: 53, 18: 62, 19: 73, 20: 84}
    ok = all(P[3][s] == c for s, c in claims.items()) and P[4][21] == 58
    print("VALIDATION r=5:", {s: P[3][s] for s in claims}, "e(H)=P4(21)=", P[4][21],
          "->", "PASS" if ok else "FAIL")
    return ok


def show_base(r, sat, q_max):
    """print P_2 (M-values) with nonexistence threshold."""
    P = P_table(r, 2, q_max, sat=sat)
    row = []
    thresh = None
    for q in range(6, q_max + 1):
        v = P[2][q]
        row.append((q, 'none' if v == INF else v))
        if v == INF and thresh is None:
            thresh = q
    print(f"  r={r} P_2 (alpha<=2,omega<={r-1},cap-{cap(r)}) M-values: {row}")
    print(f"  r={r} recursion nonexistence threshold: first 'none' at q={thresh}")
    return thresh


def report(r, sat):
    S = S_size(r)
    print(f"\n{'='*66}\n r={r}  K_{{{r*r+1}}}; S={S}; cap-{cap(r)}; own-edge-cap {own_edge_cap(r)}; "
          f"minority {minority(r)}\n{'='*66}")
    show_base(r, sat, S)
    P = P_table(r, r - 1, S, sat=sat)
    eH = P[r - 1][S]
    eF = eF_brouwer(r)
    tot = comb(S, 2)
    print(f"  P-ladder at S={S}: " + " ".join(
        f"P{a}={'none' if P[a][S]==INF else P[a][S]}" for a in range(2, r)))
    print(f"  e(H)>=P_{r-1}({S}) = {'none' if eH==INF else eH}   (rigorous DP lower bound)")
    print(f"  e(F_i)>=Brouwer  = {eF}")
    for excl in (0, 1):
        s = (eH if eH != INF else 0) + (r - 1) * (eF + excl)
        d = s - tot
        print(f"    fill(excl+{excl}): {eH}+{r-1}*{eF+excl} = {s} vs C(S,2)={tot}  "
              f"Delta={d:+d}  {'CLOSES' if d>=0 else f'SHORT {-d}'}")


if __name__ == "__main__":
    validate_r5()
    report(5, r5_sat)
    report(6, r6_sat)
