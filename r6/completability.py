#!/usr/bin/env python3
"""The completability window for class-0 edges, and the K_6-free obstruction margin."""
from math import comb
def turan(n,parts):
    q,s=divmod(n,parts); return comb(n,2)-(s*comb(q+1,2)+(parts-s)*comb(q,2))

# each ordinary class F_i (alpha<=6, K_6-free) needs >= Brouwer:
S=31; eF = comb(S,2)-(turan(S,6)-(S//6)+1)
print(f"e(F_i) >= Brouwer = {eF} per ordinary class (5 of them)")
print(f"COMPLETABILITY: e(class0) + 5*e(F_i) = C(31,2)=465, e(F_i)>={eF}")
print(f"  => e(class0) <= 465 - 5*{eF} = {465-5*eF}   (HARD upper bound for a completable class-0)")
print(f"  DP lower bound e(class0) >= 98.")
print(f"  => class-0 edge window: [98, {465-5*eF}]; completion slack = {465-5*eF} - e(class0).")
for E in (98, 105, 110, 118, 120):
    perF=(465-E)/5; slack=(465-5*eF)-E
    print(f"    e(class0)={E}: complement 5 classes avg {perF:.1f} each (min {eF}), "
          f"total slack {465-E-5*eF:+d}  {'INFEASIBLE' if slack<0 else ''}")

# K_6-free obstruction margin (section-5 analogue), plain-Turan version (no DP needed)
print("\nK_6-FREE OBSTRUCTION (why 5xK_6 is invalid):")
X=25  # class-0 has K_6=Q, X=31-6
e0=comb(X,2)-turan(X,4)                      # alpha(class0[X])<=4: complement K_5-free
eFX=comb(X,2)-(turan(X,5)-(X//5)+1)          # class-i[X] K_5-free, Brouwer rank 5
print(f"  if class-0 has a K_6: on X={X}, e(class0[X])>={e0} (plain Turan, no DP), "
      f"e(F_i[X])>={eFX} (Brouwer)")
print(f"  sum >= {e0}+5*{eFX} = {e0+5*eFX} > C(25,2)={comb(25,2)}  => CONTRADICTION (margin {e0+5*eFX-comb(25,2)})")
print(f"  => class-0 MUST be K_6-free. The 5xK_6 sketch (omega=6) cannot be completed.")
