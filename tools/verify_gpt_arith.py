#!/usr/bin/env python3
"""Exact arithmetic verification of Sections 4.2-4.3 of
review_queue/mh2-gpt56-candidate.md (the recursion that yields e(H) >= 58).

Inputs taken as given here (verified separately BY SAT in verify_gpt_tables.py):
  M-values for alpha<=2, omega<=4, cap-11 graphs:
    m <= 8: M(m) = C(m,2) - floor(m^2/4)   (complement triangle-free; cap void)
    M(9)=19, M(10)=25, M(11)=35, and NO graph for m >= 12.
Checked here:
  (i)   b(d) = floor(3d(d-1)/10) for d>=5, C(d,2) for d<=4; u(d)=min(b, ex(d,K_4)).
  (ii)  Phi_s(d) = M(s-1-d) + d^2 - (s/2)d - u(d)  for feasible d (s-1-d <= 11),
        with d infeasible (no graph on W_v) when s-1-d >= 12, i.e. d <= s-13.
        L(s) := min over degree sequences: smallest e such that some sequence
        (d_v) with sum d = 2e and all d feasible has sum Phi_s(d_v) <= 0.
        The candidate claims L: 13:24, 14:31, 15:38, 16:46, 17:53, 18:62,
        19:73, 20:84.  We compute L(s) exactly by DP (rational arithmetic via
        doubling: use 2*Phi to avoid halves).
  (iii) Psi(d) = L(20-d) + d^2 - (21/2)d - u(d) >= 52 - (19/2)d for 0<=d<=20,
        and the conclusion 0 >= sum Psi(d_v) >= 21*52 - (19/2)*2e => e >= 58.
Any mismatch is printed loudly.
"""
from math import floor


def ex_k4(m):
    q, s = divmod(m, 3)
    intra = s * (q + 1) * q // 2 + (3 - s) * q * (q - 1) // 2
    return m * (m - 1) // 2 - intra


def M(m):
    if m < 0:
        return None
    if m <= 8:
        return m * (m - 1) // 2 - (m * m // 4)
    return {9: 19, 10: 25, 11: 35}.get(m, None)  # None = no graph exists


def b(d):
    return d * (d - 1) // 2 if d <= 4 else (3 * d * (d - 1)) // 10


def u(d):
    return min(b(d), ex_k4(d))


def two_phi(s, d):
    m = M(s - 1 - d)
    if m is None:
        return None  # infeasible degree
    return 2 * m + 2 * d * d - s * d - 2 * u(d)


def L(s, dmax=None):
    if dmax is None:
        dmax = s - 1
    feas_d = [d for d in range(dmax + 1) if two_phi(s, d) is not None]
    best = None
    for e in range(0, s * (s - 1) // 2 + 1):
        NEG = 10 ** 9
        dp = [NEG] * (2 * e + 1)
        dp[0] = 0
        for _ in range(s):
            nd = [NEG] * (2 * e + 1)
            for acc in range(2 * e + 1):
                if dp[acc] == NEG:
                    continue
                for d in feas_d:
                    if acc + d <= 2 * e and dp[acc] + two_phi(s, d) < nd[acc + d]:
                        nd[acc + d] = dp[acc] + two_phi(s, d)
            dp = nd
        if dp[2 * e] != NEG and dp[2 * e] <= 0:
            best = e
            break
    return best


def main():
    claims_L = {13: 24, 14: 31, 15: 38, 16: 46, 17: 53, 18: 62, 19: 73, 20: 84}
    print("(ii) L(s) recomputed exactly from the recursion vs candidate claims:")
    Lgot = {}
    for s in range(13, 21):
        got = L(s)
        Lgot[s] = got
        ok = "OK" if got == claims_L[s] else f"*** MISMATCH (claim {claims_L[s]}) ***"
        print(f"   L({s}) = {got}   {ok}", flush=True)

    print("(iii) Psi(d) >= 52 - 19d/2 check (2*Psi >= 104 - 19d), and slacks:")
    def Lfun(m):
        if m <= 12:
            return m * (m - 1) // 2 - ex_k4(m)  # plain complement-Turan floor
        return Lgot[m]
    bad = []
    slacks = []
    for d in range(0, 21):
        m = 20 - d
        two_psi = 2 * Lfun(m) + 2 * d * d - 21 * d - 2 * u(d)
        slack = two_psi - (104 - 19 * d)
        slacks.append(slack // 2 if slack % 2 == 0 else slack / 2)
        if slack < 0:
            bad.append((d, slack))
    print(f"   slacks (claimed 32,21,11,4,1,0,0,2,...): {slacks}")
    print(f"   all nonnegative: {'YES' if not bad else f'NO *** {bad} ***'}")
    print(f"   conclusion: 0 >= 21*52 - (19/2)*2e  =>  e >= 1092/19 = {1092/19:.2f} => e >= 58"
          f"   {'OK' if 1092/19 > 57 else 'CHECK'}")


if __name__ == "__main__":
    main()
