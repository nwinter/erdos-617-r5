#!/usr/bin/env python3
"""Part C ([MM]-analogue peeling + budget) and Part E (full slack table)."""
import sys
from importlib import import_module
sys.path.insert(0, 'r6')
R = import_module('recompute2')
from math import comb
INF = R.INF

print("="*70); print(" PART C:  [MM]-analogue structure at r=6"); print("="*70)
for r in (5, 6):
    n1 = r*r                      # vertices after deleting the K_37 apex
    T = r                         # blocker size (all-equal case)
    H = n1 - T                    # G - T
    aH = r - 1                    # alpha(G-T) <= r-1
    ownc = R.own_edge_cap(r)
    budget = R.minority(r)        # e(G) <= C(r^2,2)/r
    # peeling disjoint K_r cliques: k of them, alpha(R)<=aH-k, R=H-kr vertices
    cases = []
    k = 0
    while k*r <= H:
        Rsz = H - k*r
        aR = aH - k
        if aR <= 1 and Rsz > r:      # forced into another clique
            k += 1; continue
        # a case is possible if a graph on Rsz with alpha<=aR, omega<=r-1 can exist
        # (k=aH-1 gives aR=1 on Rsz: clique, needs Rsz<=r-1 else forces next clique)
        if aR >= 0 and (aR >= 2 or Rsz <= r):
            cases.append(k)
        k += 1
        if k > aH+1: break
    # clean: max cliques limited by alpha; k=aH-1 collapses to aH when Rsz>r
    # recompute cleanly:
    maxk = aH               # aH disjoint K_r cover aH*r <= H? need aH*r<=H
    poss = []
    for k in range(0, aH+1):
        Rsz = H - k*r
        if Rsz < 0: continue
        aR = aH - k
        if k == aH-1 and (H - (aH-1)*r) == r:   # leaves exactly one more K_r
            continue                            # collapses to k=aH
        poss.append(k)
    print(f"\n r={r}: H=G-T has {H} vtcs, alpha(H)<={aH}, omega<={r-1}, cap-{R.cap(r)};"
          f" e(G)<={budget}, e(G[T])<={ownc}")
    print(f"   disjoint-K_{r} peel cases k in {poss}   ({len(poss)} cases; r=5 had 4: [0,1,2,4])")
    # K_r-free floor (k=0 case) via recursion, and budget slack
    P = R.P_table(r, r-1, H, sat=(R.r5_sat if r==5 else R.r6_sat))
    eH_free = P[r-1][H]
    print(f"   k=0 (H is K_{r}-free): e(H) >= P_{r-1}({H}) = {eH_free}"
          f"   => x+s <= e(G)-e(H) <= {budget}-{eH_free} = {budget-eH_free} (budget slack for T-edges)")
    print(f"   r=5 analogue slack was 60-50=10; here {budget-eH_free}.")

print("\n"+"="*70); print(" PART E:  full slack table, every chain inequality"); print("="*70)
rows = []
for r in (5, 6):
    S = R.S_size(r)
    P = R.P_table(r, r-1, S, sat=(R.r5_sat if r==5 else R.r6_sat))
    eH = P[r-1][S]; eF = R.eF_brouwer(r); tot = comb(S,2)
    rows.append((r, S, R.cap(r), R.own_edge_cap(r), R.minority(r),
                 eH, eF, eH+(r-1)*(eF+1), tot, eH+(r-1)*(eF+1)-tot))
print(f"\n{'r':>2}{'S':>4}{'cap':>5}{'ownc':>5}{'minor':>7}{'eH':>5}{'eF':>5}"
      f"{'fill(+1F)':>10}{'C(S,2)':>8}{'MAIN Delta':>11}")
for row in rows:
    print("".join(f"{x:>{w}}" for x,w in zip(row,[2,4,5,5,7,5,5,10,8,11])))
print("\n r=5 MAIN Delta = 0 (proven: closes via equality endgame).")
print(" r=6 MAIN Delta < 0  => the [MH''] fill inequality BREAKS: the min-edge")
print("     H and ordinary colours do NOT fill K_31; a 5-blocker is not excluded.")
