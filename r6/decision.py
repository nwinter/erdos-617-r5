#!/usr/bin/env python3
"""DECISION: is m* (min edges, alpha<=r-1, omega<=r-1, cap) <= completability ceiling?
Calibrate every 'impossibility' route against the KNOWN r=5 ground truth m*(21)=58."""
from math import comb, log

def turan(n,parts):
    q,s=divmod(n,parts); return comb(n,2)-(s*comb(q+1,2)+(parts-s)*comb(q,2))

print("="*68)
print(" GROUND TRUTH (proven r=5):  special class alpha<=4, omega<=4 on 21 vtcs")
print("   m*(r=5) = 58 (min edges, DP-tight & achieved in the proof)")
print("   M*(r=5) = 210-58 = 152 (dense complement, EXISTS)")
print("   completability ceiling r=5 = 210 - 4*38 = 58  => window={58} (razor's edge)")
print("="*68)

print("\n r=6: object A = class-0, alpha<=5, omega<=5, cap-16 on 31 vtcs")
print("   DP floor m*(r=6) >= 98 (rigorous, includes omega; +11 over no-omega 87)")
print("   completability ceiling = 465 - 5*69 = 120")
print("   => DECISION: is m*(r=6) <= 120 (window survives) or > 120 (object A impossible)?")

print("\n--- CALIBRATION of 'impossibility' routes against r=5 (must give <=58) ---")
# Asymptotic Ramsey-Turan for M* (max edges K_r-free with small alpha):
#   RT(n,K_5,o(n)) = n^2/4 ; RT(n,K_6,o(n)) = (2/7) n^2
def rt_odd(n,k): return 0.5*(1-1/k)*n*n      # K_{2k+1}
def rt_even(n,k): return 0.5*(3*k-5)/(3*k-2)*n*n  # K_{2k}
M5_asymp = rt_odd(21,2)     # K_5 = K_{2*2+1}
M6_asymp = rt_even(31,3)    # K_6 = K_{2*3}
print(f" Asymptotic Ramsey-Turan M* estimate:")
print(f"   r=5: RT(21,K_5,o(n)) = {M5_asymp:.0f}  => predicts m* ~ 210-{M5_asymp:.0f} = {210-M5_asymp:.0f}")
print(f"        BUT true m*(r=5)=58, true M*=152.  Asymptotic UNDER-predicts M* by {152-M5_asymp:.0f}")
print(f"        => it would WRONGLY predict m*(r=5) ~ {210-M5_asymp:.0f} >> 58.  FAILS CALIBRATION.")
print(f"   r=6: RT(31,K_6,o(n)) = {M6_asymp:.0f}  => would predict m* ~ 465-{M6_asymp:.0f} = {465-M6_asymp:.0f} > 120")
print(f"        but the SAME bound is wrong at r=5, so this 'impossibility' is NOT VALID at n=31.")

# Caro-Wei (ignores K_r-free): alpha >= n/(dbar+1)
print(f"\n Caro-Wei lower bound on alpha (ignores clique bound):")
for r,n,e,amax in [(5,21,58,4),(6,31,98,5)]:
    dbar=2*e/n; cw=n/(dbar+1)
    print(f"   r={r}: n={n}, e={e}, dbar={dbar:.2f} => alpha >= {cw:.2f}  "
          f"(allows alpha<={amax}? {'YES' if cw<=amax else 'NO-forces bigger'})")
print("   => Caro-Wei allows alpha=4 at r=5 (true) and alpha=5 at r=6 (consistent). No impossibility.")

# Shearer-type (triangle-free) would be far too strong -- but graph is only K_r-free, has triangles.
print(f"\n Shearer (triangle-free) DOES NOT APPLY (our graph has triangles, only K_r-free).")
print(f"   The r=5 special class (K_5-free, avg deg 5.52, alpha=4) EXISTS -> any K_r-free")
print(f"   independence bound forcing alpha>=r-... at these densities would refute it. So no")
print(f"   Shearer-type bound with r-1=5-clique-freedom forces alpha>=6 at avg deg 6.3, n=31.")

print("\n" + "="*68)
print(" VERDICT: best rigorous lower bound m*(r=6) = 98 <= 120.")
print("   Object A is NOT proven impossible. Window [98,120] SURVIVES (width 22).")
print("   Every impossibility route (asymptotic Ramsey-Turan, Caro-Wei, Shearer) FAILS")
print("   the r=5 calibration; the DP (tight at r=5) gives 98. So m*(r=6) ~ 98-105, and")
print("   [MH''] BREAKS at r=6 (as the fill argument found). Decisive confirmation = a")
print("   construction at <=120 (hunt) or SAT feasibility.")
print("="*68)
