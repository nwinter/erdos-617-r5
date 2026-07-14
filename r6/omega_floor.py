#!/usr/bin/env python3
"""Does the DP floor include omega<=r-1, and how much does it add? Calibrate against
the KNOWN r=5 ground truth m*=58 (proven, DP-tight). Then read off r=6."""
import sys; from importlib import import_module
sys.path.insert(0,'r6'); R=import_module('recompute2'); from math import comb
INF=R.INF

def floor_with_omega(r, omega, sat):
    """recompute P_{r-1}(S) but with a custom omega (clique bound). omega=big => no clique constraint."""
    import importlib
    # monkeypatch: u(d)=min(b, ex(d,omega+1 clique => K_{omega+1}-free nbhd)); clique base <=omega
    S=R.S_size(r)
    # build P-table with overridden omega
    q_max=S
    P={1:[0 if q==0 else (comb(q,2) if q<=omega else INF) for q in range(q_max+1)]}
    def u_custom(d):
        b=R.b(r,d)
        # neighbourhood is K_omega-free (a K_omega in N(v)+v=K_{omega+1}); ex(d,K_omega)
        exk=R.ex_Kt(d, omega)   # K_omega-free
        return min(b, exk)
    def dp(q, Pprev):
        tp={}
        for d in range(q):
            w=q-1-d
            if 0<=w<len(Pprev) and Pprev[w]!=INF:
                tp[d]=2*Pprev[w]+2*d*d-q*d-2*u_custom(d)
        if not tp: return INF
        feas=sorted(tp); maxm=q*(q-1)//2
        for m in range(maxm+1):
            t=2*m; d0=[INF]*(t+1); d0[0]=0
            for _ in range(q):
                nd=[INF]*(t+1)
                for acc in range(t+1):
                    if d0[acc]==INF: continue
                    for d in feas:
                        if acc+d<=t and d0[acc]+tp[d]<nd[acc+d]: nd[acc+d]=d0[acc]+tp[d]
                d0=nd
            if d0[t]!=INF and d0[t]<=0: return m
        return INF
    R3=R.R3.get(r,10**9)
    for a in range(2,r):
        Pa=[INF]*(q_max+1); Pa[0]=0
        for q in range(1,q_max+1):
            if a==2 and q>=R3: Pa[q]=INF; continue
            dpv=dp(q,P[a-1]); sv=sat(a,q) if sat else None
            if sv==INF or dpv==INF: Pa[q]=INF; continue
            direct=comb(q,2)-R.turan(q,a); val=max(direct,dpv)
            if sv is not None: val=max(val,sv)
            Pa[q]=val
        P[a]=Pa
    return P[r-1][S]

# r=5 calibration: true m*=58 (omega=4). Also without omega (omega=big).
print("r=5 special class (alpha<=4, on S=21):")
print("  with omega<=4 (true):", floor_with_omega(5,4,R.r5_sat), " [known ground truth 58]")
print("  omega<=20 (no clique bound):", floor_with_omega(5,20,R.r5_sat))
print()
print("r=6 special class (alpha<=5, on S=31):")
print("  with omega<=5 (the object-A floor):", floor_with_omega(6,5,R.r6_sat), " [vs ceiling 120]")
print("  omega<=30 (no clique bound):", floor_with_omega(6,30,R.r6_sat))
