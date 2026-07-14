#!/usr/bin/env python3
"""What structure does the DP e(H)>=98 imply? Extract Phi_5(d) and the optimal
(most-negative) degree multiset the recursion forces for a NEAR-MINIMUM class-0
graph on 31 vtcs (alpha<=5, omega<=5, cap-16)."""
import sys; from importlib import import_module
sys.path.insert(0,'r6'); R=import_module('recompute2'); from math import comb
INF=R.INF
r,q = 6,31
P=R.P_table(r,r-1,q,sat=R.r6_sat)
Pprev=P[r-2]  # P_4, used on W_v
print("Phi_5(d) = P_4(30-d) + d^2 - (31/2)d - u(d)   [x2 to avoid halves]")
rows=[]
for d in range(0,q):
    w=q-1-d
    if 0<=w<len(Pprev) and Pprev[w]!=INF:
        twophi=2*Pprev[w]+2*d*d-q*d-2*R.u(r,d)
        rows.append((d,Pprev[w],R.u(r,d),twophi/2))
for d,pw,ud,phi in rows:
    print(f"  d={d:2d}: P_4(30-d={30-d:2d})={pw:3d}  u(d)={ud:3d}  Phi_5={phi:+.1f}")
# feasible degrees and the min-edge sequence
feas=[d for d,_,_,_ in rows]
print(f"\n feasible degrees (P_4(30-d) finite): {feas}")
# the recursion needs sum Phi<=0 with 31 vertices; find min m
best=None
for m in range(80,120):
    tgt=2*m; dp=[INF]*(tgt+1); dp[0]=0; par=[[None]*(tgt+1) for _ in range(1)]
    # track a witness degree multiset
    seqs=[None]*(tgt+1); seqs[0]=()
    for _ in range(q):
        nd=[INF]*(tgt+1); ns=[None]*(tgt+1)
        for acc in range(tgt+1):
            if dp[acc]==INF: continue
            for d,pw,ud,_ in rows:
                tp=2*pw+2*d*d-q*d-2*ud
                if acc+d<=tgt and dp[acc]+tp<nd[acc+d]:
                    nd[acc+d]=dp[acc]+tp; ns[acc+d]=(seqs[acc] or ())+(d,)
        dp=nd; seqs=ns
    if dp[tgt]!=INF and dp[tgt]<=0:
        best=(m,seqs[tgt]); break
print(f"\n DP first closes at m={best[0]}  (e(H)>={best[0]})")
from collections import Counter
print(f" witness degree multiset: {dict(sorted(Counter(best[1]).items()))}")
print(f" => a near-min class-0 concentrates on these degrees; avg deg {2*best[0]/31:.2f}")
