from math import comb
from itertools import combinations

def t(n, r):
    if r == 0: return comb(n, 2)
    q, s = divmod(n, r)
    return comb(n, 2) - ((r - s) * comb(q, 2) + s * comb(q + 1, 2))

def sav(n, r):
    return (n // r - 1) if n >= 2 * r + 1 else 2

def sigma2(p):
    return sum(p[i] * p[j] for i in range(len(p)) for j in range(i + 1, len(p)))

def gen(total, r, minv):
    if r == 1:
        if total >= minv: yield (total,)
        return
    for first in range(minv, total - minv * (r - 1) + 1):
        for rest in gen(total - first, r - 1, minv):
            yield (first,) + rest

# Identity checks: r*Q = n^2 + s(r-s);  2r*t = (r-1)n^2 - s(r-s);
#   r*sum(p^2) - n^2 = sum_{i<j}(p_i-p_j)^2  (Lagrange)
def Q(n, r):
    q, s = divmod(n, r); return (r - s) * q * q + s * (q + 1) ** 2
bad = 0
for r in range(1, 8):
    for n in range(0, 40):
        q, s = divmod(n, r)
        assert r * Q(n, r) == n * n + s * (r - s), (n, r)
        assert 2 * t(n, r) == n * n - Q(n, r), (n, r)
        assert 2 * r * t(n, r) == (r - 1) * n * n - s * (r - s), (n, r)
print("identity checks OK")

# two_bad_bound over wide range, parts >= 2 and separately >= 1
for minv in (2, 1):
    bad = tight = checked = 0
    worst = None; worst_slack = 10**9
    for r in range(2, 7):
        for n in range(2 * r, 42):
            for p in gen(n, r, minv):
                checked += 1
                lhs = sigma2(p) - min(p) + sav(n, r)
                slack = t(n, r) - lhs
                if slack < 0: bad += 1;
                elif slack == 0: tight += 1
                if slack < worst_slack: worst_slack = slack; worst = (r, n, p)
    print(f"minv={minv}: checked={checked} violations={bad} tight={tight} worst_slack={worst_slack} at {worst}")

# Reformulated (Lagrange) target for main regime, parts>=2:
#   sum_{i<j}(p_i-p_j)^2 >= s(r-s) + 2r*(sav - min)
badL = 0
for r in range(2, 7):
    for n in range(2 * r + 1, 42):   # main regime
        q, s = divmod(n, r)
        for p in gen(n, r, 2):
            L = sum((p[i]-p[j])**2 for i,j in combinations(range(r),2))
            R = s*(r-s) + 2*r*(sav(n,r) - min(p))
            if L < R: badL += 1
print("Lagrange main-regime violations:", badL)

# small regime n in [r+3, 2r], sav=2, parts>=2 -- but note n>=2r needs parts>=2 => all parts exactly 2 when n=2r
badS = 0
for r in range(2, 7):
    for n in range(r + 3, 2 * r + 1):
        for p in gen(n, r, 2):
            lhs = sigma2(p) - min(p) + 2
            if lhs > t(n, r): badS += 1; print("small FAIL", r, n, p)
print("small-regime (n<=2r) violations:", badS)
