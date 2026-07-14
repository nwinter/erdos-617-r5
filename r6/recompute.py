#!/usr/bin/env python3
"""SUPERSEDED by r6/recompute2.py.  This first pass had a bug: dp_min_edges returned
`maxm` instead of INF when the recursion PROVES nonexistence (the analogue of
r=5's M(12)=none), which corrupted the propagation upward.  recompute2.py fixes
this and is the authoritative script.  Kept for the debugging record.

r6/recompute.py  --  exact arithmetic reconnaissance of the extension-obstruction
chain at general r (focus r=6, Erdos-Gyarfas at K_{r^2+1}=K_37).

MIRRORS tools/verify_gpt_arith.py but parameterised by r, and prints the r=5
numbers alongside the r=6 numbers so every claimed analogue can be diffed.

Nothing here is a proof.  Every number is an EXACTLY-COMPUTED lower bound built
from:
  (i)   pinned definitions (cap, own-edge cap, minority, S, target) -- pure combinatorics;
  (ii)  Brouwer's non-r-partite Turan bound applied to a single colour class;
  (iii) the cap-recursion DP (identity (4.1)/(4.2) of the mh2 candidate), which
        yields a *rigorous lower bound* on min-edges of a cap-capped, alpha-capped,
        omega-capped graph.  The DP can UNDER-estimate the true minimum (SAT gives
        more, as at r=5 where M(9)=19 > Turan 16); so a "closes" verdict from the DP
        is conservative-safe, a "breaks" verdict from the DP is only suggestive
        (the SAT-boosted base might rescue it) and is flagged as such.

Base level P_2 (alpha<=2): we take max(complement-Turan floor, cap-DP-from-clique).
The complement-Turan floor  C(q,2) - floor(q^2/4)  is ALWAYS a valid lower bound
for an alpha<=2 graph (complement is triangle-free).  cap/omega only raise it.
"""
from math import floor, comb
from fractions import Fraction


# ---------- pinned combinatorial quantities (pure definitions) ----------

def cap(r):
    """max edges of one colour allowed in an (r+1)-set of a balanced r-colouring.
    (r+1)-set has C(r+1,2) edges; the r-1 OTHER colours each need >=1 edge to be
    seen, so own colour <= C(r+1,2) - (r-1)."""
    return comb(r + 1, 2) - (r - 1)


def own_edge_cap(r):
    """step-5 tightness cap: an r-vertex blocker T_{c'} must carry >=1 edge of each
    of the r-1 other colours (all distinct), so <= C(r,2) - (r-1) of its own colour."""
    return comb(r, 2) - (r - 1)


def minority(r):
    """delete a vertex -> r^2 vertices; sum_c e(G_c) = C(r^2,2); minority <= average."""
    return comb(r * r, 2) // r


def S_size(r):
    """[MH''] deletes an (r-1)-vertex hitter from K_{r^2}: S = r^2 - (r-1)."""
    return r * r - (r - 1)


def turan(n, parts):
    """t_parts(n): edges of the Turan graph = complete multipartite, parts balanced."""
    q, s = divmod(n, parts)
    # s parts of size q+1, parts-s parts of size q
    intra = s * comb(q + 1, 2) + (parts - s) * comb(q, 2)
    return comb(n, 2) - intra


def ex_Kt(n, t):
    """ex(n, K_t) = Turan number = t_{t-1}(n): max edges K_t-free graph."""
    return turan(n, t - 1)


# ---------- neighbourhood edge bound b(d) and u(d) ----------

def b(r, d):
    """cap-bound on e(G[N(v)]) for deg-d vertex.  An r-subset A of N(v) makes {v}uA
    an (r+1)-set: r (spoke) + e(A) <= cap, so e(A) <= cap-r.  Double count r-subsets:
      e(N(v)) <= (cap-r) * C(d,r)/C(d-2,r-2) = (cap-r) d(d-1)/(r(r-1)).
    For d < r the neighbourhood is too small for the cap to bite: b(d)=C(d,2)."""
    if d < r:
        return comb(d, 2)
    num = (cap(r) - r) * d * (d - 1)
    den = r * (r - 1)
    return num // den


def u(r, d):
    """omega(H)<=r-1  =>  N(v) is K_{r-1}-free, so also e(N(v)) <= ex(d, K_{r-1})."""
    return min(b(r, d), ex_Kt(d, r - 1))


# ---------- the cap-recursion DP for P_a(q) = min edges, alpha<=a, omega<=r-1, cap ----------

INF = float('inf')


def complement_turan_floor(q):
    """valid lower bound for alpha<=2 graph: complement triangle-free."""
    return comb(q, 2) - (q * q // 4)


def P_table(r, a_max, q_max, base2=None):
    """Return dict a -> list P[a][q] for q=0..q_max, a=1..a_max.
    P[a][q] = rigorous lower bound on min edges of a graph on q vertices with
    alpha<=a, omega<=r-1, cap-cap(r).
    P[1][q] = C(q,2) if q<=r-1 (a clique), else INF.
    base2: optional function q -> (value or None) giving SAT-exact M-values for the
      alpha<=2 base.  None from base2 means 'no such graph' (INF).  Where base2 is
      not supplied we fall back to the complement-Turan floor (a valid lower bound).
    P[a][q] for a>=2: max( valid floors , DP-recursion via P[a-1] )."""
    omega = r - 1
    P = {}
    P[1] = [0 if q == 0 else (comb(q, 2) if q <= omega else INF) for q in range(q_max + 1)]
    for a in range(2, a_max + 1):
        Pa = [INF] * (q_max + 1)
        Pa[0] = 0
        for q in range(1, q_max + 1):
            if a == 2 and base2 is not None:
                bv = base2(q)
                Pa[q] = INF if bv is None else bv
                continue
            direct = 0
            if a == 2:
                direct = max(direct, complement_turan_floor(q))
            direct = max(direct, comb(q, 2) - turan(q, a))  # alpha<=a: complement K_{a+1}-free
            dp_bound = dp_min_edges(r, q, P[a - 1], u_func=lambda d: u(r, d))
            Pa[q] = max(direct, dp_bound)
        P[a] = Pa
    return P


def r5_sat_base(q):
    """SAT-verified M-values for alpha<=2, omega<=4, cap-11 (the r=5 base),
    exactly as tools/verify_gpt_arith.py uses them."""
    if q <= 8:
        return comb(q, 2) - (q * q // 4)
    return {9: 19, 10: 25, 11: 35}.get(q, None)


# r=6 base M6(s) = min edges alpha<=2, omega<=5, cap-16.
# EXACT (SAT, r6/sat_base.py): M6(9)=16, M6(10)=20, M6(11)=29.
# For s<=8 cap/omega void => complement-Turan is exact.
# For s in 12..17 we use complement-Turan as a valid LOWER bound (true M6 higher;
#   boost only grows).  For s>=18 no such graph (R(3,6)=18): complement is
#   triangle-free with alpha<=5, impossible on >=18 vertices.
R6_SAT = {9: 16, 10: 20, 11: 29}


def r6_base_lower(q):
    """valid LOWER bound base: exact where SAT-known, else complement-Turan floor,
    None (no graph) for q>=18 by Ramsey R(3,6)=18."""
    if q >= 18:
        return None
    if q in R6_SAT:
        return R6_SAT[q]
    return comb(q, 2) - (q * q // 4)


def r6_base_optimistic(q):
    """OPTIMISTIC base to bracket from above: assume the r=6 boost tracks the r=5
    boost pattern shifted by +2 in s (omega<=5 vs omega<=4 lets the two-clique
    extremal survive 2 more vertices).  r=5 boosts over Turan were:
      s: 9,10,11,12,13  boost: +3,+5,+10,inf,inf  (M(11)=none actually, use +10)
    shift +2:  s:11,12,13,14,15 boost +3? no -- we KNOW s=11 boost is +4 (SAT).
    Use SAT(9,10,11), then apply an r5-shaped increasing boost for 12..17 capped at
    the Ramsey nonexistence (>=18 none).  This is a heuristic UPPER-ish bracket,
    NOT rigorous; used only to show even a generous base does not close r=6."""
    if q >= 18:
        return None
    if q in R6_SAT:
        return R6_SAT[q]
    if q <= 8:
        return comb(q, 2) - (q * q // 4)
    turanf = comb(q, 2) - (q * q // 4)
    # generous escalating boost for 12..17
    boost = {12: 9, 13: 15, 14: 22, 15: 30, 16: 39, 17: 49}.get(q, 0)
    return turanf + boost


def dp_min_edges(r, q, Pprev, u_func):
    """Smallest m such that some feasible degree multiset on q vertices (sum d = 2m)
    has sum_v 2*Phi(d_v) <= 0, where 2*Phi(d) = 2*Pprev[q-1-d] + 2 d^2 - q d - 2 u(d).
    Degrees d with Pprev[q-1-d] == INF are infeasible (W_v too big / no graph)."""
    # precompute 2*Phi(d) for feasible d
    twophi = {}
    for d in range(0, q):
        w = q - 1 - d
        if w < 0 or w >= len(Pprev) or Pprev[w] == INF:
            continue
        twophi[d] = 2 * Pprev[w] + 2 * d * d - q * d - 2 * u_func(d)
    if not twophi:
        return INF
    feas_d = sorted(twophi)
    maxm = q * (q - 1) // 2
    for m in range(0, maxm + 1):
        target = 2 * m
        # DP over exactly q vertices, sum of degrees = target, minimise sum 2phi
        NEG = float('inf')
        dp = [NEG] * (target + 1)
        dp[0] = 0
        for _ in range(q):
            nd = [NEG] * (target + 1)
            for acc in range(target + 1):
                if dp[acc] == NEG:
                    continue
                base = dp[acc]
                for d in feas_d:
                    if acc + d <= target:
                        val = base + twophi[d]
                        if val < nd[acc + d]:
                            nd[acc + d] = val
                dp = dp  # noop
            dp = nd
        if dp[target] != NEG and dp[target] <= 0:
            return m
    return maxm  # fallback (should not hit)


# ---------- Brouwer bound on a single ordinary colour class F_i ----------

def eF_brouwer(r):
    """e(F_i) >= C(S,2) - [ t_r(S) - floor(S/r) + 1 ]  where S = r^2-r+1.
    F_i is K_r-free (an F_i-K_r would be an H-independent r-set, alpha(H)<=r-1),
    complement J_i is K_{r+1}-free with alpha(J_i)=omega(F_i)<=r-1, not r-partite
    (r*(r-1) < S).  Brouwer with Turan-rank r."""
    S = S_size(r)
    tr = turan(S, r)
    return comb(S, 2) - (tr - (S // r) + 1)


def eF_inX_brouwer(r):
    """inside a K_r of H, X = S - K_r has |X| = r^2-r+1-r = r^2-2r+1 = (r-1)^2.
    F_i[X] is K_{r-1}-free (an F_i-K_{r-1}? no: an F_i-(r-1)-clique is H[X]-indep
    (r-1)-set; alpha(H[X])<=r-2). complement K_r-free, alpha<=r-2, not (r-1)-partite.
    Brouwer Turan-rank r-1 on (r-1)^2 vertices."""
    X = (r - 1) ** 2
    rr = r - 1
    trr = turan(X, rr)
    return comb(X, 2) - (trr - (X // rr) + 1)


# ---------- main report ----------

def report(r):
    S = S_size(r)
    print(f"\n{'='*70}\n  r = {r}   (Erdos-Gyarfas at K_{{{r*r+1}}}; delete vertex -> K_{{{r*r}}})\n{'='*70}")
    print(f"  cap  (max own-colour edges in an (r+1)={r+1}-set) = {cap(r)}"
          f"   [= C({r+1},2) - (r-1) = {comb(r+1,2)} - {r-1}]")
    print(f"  own-edge cap (step-5, r-vertex blocker)          = {own_edge_cap(r)}"
          f"   [= C({r},2) - (r-1) = {comb(r,2)} - {r-1}]")
    print(f"  minority bound  e(G_m) <= C({r*r},2)/{r}            = {minority(r)}")
    print(f"  [MH''] hitter = (r-1)={r-1}-set; S = |remaining| = {S}   (= r^2-r+1)")
    print(f"  alpha(H) <= r-1 = {r-1};  alpha(F_i) <= r = {r};  omega(all) <= r-1 = {r-1}")
    print(f"  total to fill: C(S,2) = C({S},2) = {comb(S,2)}")

    # Brouwer for F_i
    eF = eF_brouwer(r)
    print(f"\n  --- ordinary colour F_i (Brouwer) ---")
    print(f"  e(F_i) >= {eF}  (before equality-exclusion; r=5 then +1 by A/B endgame)")

    # recursion for e(H) = P_{r-1}(S)
    a_max = r - 1
    print(f"\n  --- special colour H = P_{{{a_max}}}(S) via cap-recursion DP ---")
    P = P_table(r, a_max, S)
    # print the ladder of P_a at the sizes that matter
    for a in range(2, a_max + 1):
        vals = {q: (P[a][q] if P[a][q] != INF else 'INF') for q in range(max(0, S - 6), S + 1)}
        print(f"  P_{a}(q) near S: {vals}")
    eH_dp = P[a_max][S]
    # plain complement-Turan on H for comparison
    eH_plain = comb(S, 2) - turan(S, r - 1)
    print(f"  e(H) plain complement-Turan floor (no cap) = {eH_plain}")
    print(f"  e(H) cap-recursion DP lower bound          = {eH_dp}")

    # the decisive sum
    print(f"\n  --- the decisive fill inequality  e(H) + (r-1) e(F_i)  vs  C(S,2) ---")
    total = comb(S, 2)
    for label, eHval in (("DP-floor", eH_dp), ("plain-Turan", eH_plain)):
        s = eHval + (r - 1) * eF
        delta = s - total
        verdict = "CLOSES (over/at full)" if delta >= 0 else f"SHORT by {-delta} (GAP/BREAK unless base boosted)"
        print(f"   using e(H)[{label:11s}]={eHval:4d}, e(F_i)={eF}: "
              f"{eHval} + {r-1}*{eF} = {s}  vs {total}   Delta={delta:+d}   {verdict}")

    # the K_r-exclusion (section 5 analogue) sum, inside X
    print(f"\n  --- section-5 (H is K_r-free) fill inside X = S - K_r, |X|=(r-1)^2={(r-1)**2} ---")
    X = (r - 1) ** 2
    # e(H[X]) >= P_{r-2}(X): alpha(H[X]) <= r-2
    if r - 2 >= 1:
        PX = P_table(r, max(2, r - 2), X)
        aX = r - 2
        eHX = PX[aX][X] if aX >= 2 else comb(X, 2)  # r=3 edge case
    else:
        eHX = comb(X, 2)
    eFX = eF_inX_brouwer(r)
    sX = eHX + (r - 1) * eFX
    totX = comb(X, 2)
    print(f"   e(H[X]) >= P_{{{r-2}}}({X}) = {eHX};  e(F_i[X]) >= {eFX} (Brouwer rank {r-1})")
    print(f"   {eHX} + {r-1}*{eFX} = {sX}  vs C({X},2)={totX}   Delta={sX-totX:+d}   "
          f"{'CLOSES' if sX>totX else 'SHORT'}")


def validate_r5():
    """Check the DP machinery reproduces the PROVEN r=5 L-table and e(H)>=58 when
    fed the SAT-verified alpha<=2 base.  If this passes, the same DP at r=6 with a
    SAT r=6 base is trustworthy."""
    print("\n" + "#" * 70 + "\n# VALIDATION: r=5 DP with SAT base must reproduce L-table + e(H)>=58\n" + "#" * 70)
    P = P_table(5, 4, 21, base2=r5_sat_base)
    claims_L = {13: 24, 14: 31, 15: 38, 16: 46, 17: 53, 18: 62, 19: 73, 20: 84}
    ok = True
    for s, c in claims_L.items():
        got = P[3][s]
        flag = "OK" if got == c else f"*** MISMATCH claim {c} ***"
        if got != c:
            ok = False
        print(f"  L({s}) = {got}   {flag}")
    eH = P[4][21]
    print(f"  e(H) = P_4(21) = {eH}   {'OK (>=58)' if eH >= 58 else '*** below 58 ***'}")
    print(f"  VALIDATION {'PASSED' if ok and eH >= 58 else 'FAILED'}")
    return ok and eH >= 58


def r6_eH_brackets():
    """Compute e(H)=P_5(31) at r=6 under three bases: pure complement-Turan (loose
    lower), partial-SAT-lower (rigorous lower, uses SAT M6(9,10,11)), and an
    optimistic escalating base (heuristic upper-ish bracket).  Compare to the fill
    target 465 - 5*e(F)."""
    print("\n" + "#" * 70 + "\n# r=6  e(H)=P_5(31) under three bases; fill target vs 465\n" + "#" * 70)
    eF = eF_brouwer(6)  # 69
    for name, base in (("pure-Turan   ", None),
                       ("SAT-lower    ", r6_base_lower),
                       ("optimistic   ", r6_base_optimistic)):
        P = P_table(6, 5, 31, base2=base)
        eH = P[5][31]
        for excl in (0, 1, 2):
            eFx = eF + excl
            s = eH + 5 * eFx
            d = s - 465
            tag = "CLOSES" if d >= 0 else f"SHORT {-d}"
            if excl == 1:
                print(f"  base={name} e(H)={eH:3d}  e(F)={eFx} (excl+{excl}):  "
                      f"{eH}+5*{eFx}={s}  vs 465  Delta={d:+d}  {tag}")
    # also print the P-ladder for the SAT-lower base
    P = P_table(6, 5, 31, base2=r6_base_lower)
    print("  SAT-lower ladder at S=31: "
          f"P2={P[2][31] if P[2][31]!=INF else 'INF'} P3={P[3][31]} P4={P[4][31]} P5={P[5][31]}")
    print("  (r=5 calibration: pure-Turan DP undershot truth by exactly 1 at the top;")
    print("   if the same holds at r=6 the SAT-lower e(H) is within ~1-3 of the true min.)")


if __name__ == "__main__":
    validate_r5()
    for r in (5, 6):
        report(r)
    r6_eH_brackets()
