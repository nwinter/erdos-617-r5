#!/usr/bin/env python3
"""Robustness of the r=6 BREAK: (1) if the nonexistence threshold q=17 is wrong
(P_2(17) actually exists), e(H) only DROPS (more feasible degrees) -> break worse.
(2) the derived cap-16 is load-bearing: what if it were the task's guessed 15?"""
import sys; from importlib import import_module
sys.path.insert(0, 'r6'); R = import_module('recompute2'); from math import comb
INF = R.INF

# (1) pretend P_2(17..) are finite (complement-Turan) instead of none
def r6_sat_17finite(a, q):
    if a != 2: return None
    if q <= 8: return comb(q,2)-(q*q//4)
    if q in (9,10,11): return {9:16,10:20,11:29}[q]
    return None   # let recursion decide (it will still say none via dp); to force
# force finiteness by monkeypatching R3 threshold up and giving direct floors:
orig_R3 = dict(R.R3)
R.R3[6] = 100   # disable Ramsey nonexistence for the test
def r6_force_finite(a,q):
    if a!=2: return None
    if q<=8: return comb(q,2)-(q*q//4)
    if q in (9,10,11): return {9:16,10:20,11:29}[q]
    if 12<=q<=30: return comb(q,2)-(q*q//4)  # pretend all exist at Turan floor
    return None
P = R.P_table(6,5,31,sat=r6_force_finite)
print("(1) if alpha<=2 graphs existed at all sizes (no nonexistence): e(H)=P_5(31) =",
      P[5][31], "(<=98 => break >= 17, i.e. worse)")
R.R3 = orig_R3  # restore

# (2) cap sensitivity: temporarily force cap(6)=15 and 16 and 17
import types
for capval in (15, 16, 17):
    R.cap = (lambda cv: (lambda r: cv if r==6 else comb(r+1,2)-(r-1)))(capval)
    P = R.P_table(6,5,31,sat=R.r6_sat)
    eH = P[5][31]; eF = R.eF_brouwer(6); tot=comb(31,2)
    fill = eH+5*(eF+1)
    print(f"(2) hypothetical cap-{capval}: e(H)={eH}, fill(+1F)={fill} vs {tot}  "
          f"Delta={fill-tot:+d}  {'CLOSES' if fill>=tot else 'BREAKS'}")
# restore
R.cap = lambda r: comb(r+1,2)-(r-1)
print("\n  (correct cap is 16, derived: C(7,2)-(r-1)=21-5=16; task's guess '15' is wrong.")
print("   Even the tighter cap-15 would still BREAK; cap-16 breaks by more.)")
