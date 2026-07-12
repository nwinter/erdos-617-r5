# Quantitative Turán slack check for KP Case A (closed-form route).
# t_r(n) = edges of Turán graph = balanced complete r-partite.
# sav(n,r) = n//r - 1 if n >= 2r+1 else 2  (KP Thm 1 both regimes)
# Case A needs: kpSaving(n,r) <= kpSaving(d,r-1) + (t_r(n) - t_{r-1}(d) - d*(n-d))
# for all d that can arise: H[D] non-(r-1)-partite => d >= (r-1)+2 = r+1, and d <= n-1 (C nonempty).
from math import comb
def t(n,r):
    if r==0: return comb(n,2)
    q,rem = divmod(n,r)
    # r-partite balanced: rem parts of size q+1, r-rem of size q
    # edges = C(n,2) - within-part pairs
    within = rem*comb(q+1,2) + (r-rem)*comb(q,2)
    return comb(n,2) - within
def sav(n,r):
    return (n//r - 1) if n >= 2*r+1 else 2
bad=[]
for r in range(2,6):
    for n in range(r+3, 40):
        for d in range(r+1, n):  # d>=r+1 (non-(r-1)-partite needs >=r vertices; use r+1 to be safe), d<=n-1
            lhs = sav(n,r)
            slack = t(n,r) - t(d,r-1) - d*(n-d)
            rhs = sav(d,r-1) + slack
            if slack < 0:
                bad.append(("SLACK<0",r,n,d,slack))
            if lhs > rhs:
                bad.append(("FAIL",r,n,d,lhs,rhs,slack))
print("checked r=2..5, n up to 39, d in [r+1,n-1]")
print("violations:", len(bad))
for b in bad[:20]: print(b)
