#!/usr/bin/env python3
"""Cross-r trend of the decisive fill inequality, PLAIN (no cap boost).
Shows how the 'plain deficit' Delta_plain(r) that the cap boost must cover grows
with r, explaining why r=5 is a knife-edge (Delta_total=0) and predicting r=6.

Plain bounds (rigorous, cap-free):
  e(H)   >= C(S,2) - t_{r-1}(S)                       [alpha(H)<=r-1: complement K_r-free]
  e(F_i) >= C(S,2) - t_r(S) + floor(S/r) - 1          [Brouwer, K_r-free class]
  S = r^2 - r + 1;  total = C(S,2);  (r-1) ordinary colours + 1 special.
Delta_plain = e(H) + (r-1) e(F_i) - C(S,2).
The cap-recursion boost on H plus the F equality-exclusions must cover -Delta_plain.
"""
from math import comb


def turan(n, parts):
    q, s = divmod(n, parts)
    return comb(n, 2) - (s * comb(q + 1, 2) + (parts - s) * comb(q, 2))


print(f"{'r':>2} {'S':>4} {'C(S,2)':>7} {'eH_plain':>9} {'eF_plain':>9} "
      f"{'sum':>6} {'Delta_plain':>11} {'per-F share':>11}")
for r in range(3, 10):
    S = r * r - r + 1
    tot = comb(S, 2)
    eH = tot - turan(S, r - 1)
    eF = tot - turan(S, r) + (S // r) - 1
    ssum = eH + (r - 1) * eF
    d = ssum - tot
    # 'per-F share': how much each ordinary colour is below the average tot/r
    avg = tot / r
    print(f"{r:>2} {S:>4} {tot:>7} {eH:>9} {eF:>9} {ssum:>6} {d:>11} {avg - eF:>11.2f}")

print("\nInterpretation: Delta_plain is what the cap-boost(H) + F-exclusions must cover.")
print("r=5: cap-boost gave +13 (45->58), F-excl +4 (37->38 x4) => exactly cancels -17.")
print("Watch how -Delta_plain grows vs the cap-boost capacity (which scales ~ with the")
print("cap slack cap(r)-C(r+1,2)*(density) and dampens through r-2 recursion levels).")
