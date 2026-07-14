#!/usr/bin/env python3
"""How high can r=6 e(H)=P_5(31) go as M6(12..16) rise?  Brackets the true e(H)
(which uses SAT-exact M6) to test whether the fill can reach 465-5*70=115.
Also calibrates: r=5 e(H) under DP-only base vs SAT base (the base-boost size)."""
from importlib import import_module
import sys
sys.path.insert(0, 'r6')
R = import_module('recompute2')
INF = R.INF


def eH(r, sat, S=None):
    S = S or R.S_size(r)
    P = R.P_table(r, r - 1, S, sat=sat)
    return P[r - 1][S]


# --- r=5 base-boost calibration ---
def r5_nosat(a, q):   # DP-from-P_1 only (no SAT M-values), Ramsey handles >=14
    return None
def r5_full(a, q):
    return R.r5_sat(a, q)
print("r=5 e(H): DP-only base =", eH(5, r5_nosat), " ; SAT base =", eH(5, r5_full),
      " (boost =", eH(5, r5_full) - eH(5, r5_nosat), ")")

# --- r=6 e(H) as M6(12..16) rise ---
# scenario base functions: exact 9,10,11; 12..16 set to given tuple; >=17 none
def make_r6(vals):   # vals = dict q->value for 12..16
    def f(a, q):
        if a != 2:
            return None
        if q <= 8:
            return R.comb(q, 2) - (q * q // 4)
        if q in (9, 10, 11):
            return {9: 16, 10: 20, 11: 29}[q]
        if q in vals:
            return vals[q]
        if q >= 17:
            return INF
        return None
    return f

turan = lambda q: R.comb(q, 2) - (q * q // 4)
scenarios = {
    "DP-lower (current)": None,   # let recursion fill 12..16
    "Turan floor":        {q: turan(q) for q in range(12, 17)},
    "Turan+r5boost":      {12: turan(12)+9, 13: turan(13)+15, 14: turan(14)+22,
                           15: turan(15)+30, 16: turan(16)+40},
    "aggressive(+near-none)": {12: 45, 13: 60, 14: 78, 15: 98, 16: 118},
}
print("\nr=6 e(H)=P_5(31) and fill vs 465 (e_F=70):")
for name, vals in scenarios.items():
    sat = R.r6_sat if vals is None else make_r6(vals)
    v = eH(6, sat)
    fill = v + 5 * 70
    print(f"  {name:24s}: M6(12..16)={vals if vals else 'DP: 36,46,56,68,80'}")
    print(f"  {'':24s}  e(H)={v}, fill={v}+350={fill} vs 465  Delta={fill-465:+d}"
          f"  {'CLOSES' if fill>=465 else 'SHORT '+str(465-fill)}")
