from math import comb
import itertools

def t(n, r):
    if r == 0: return comb(n, 2)
    q, s = divmod(n, r)
    return comb(n, 2) - ((r - s) * comb(q, 2) + s * comb(q + 1, 2))

def sav(n, r):
    return (n // r - 1) if n >= 2 * r + 1 else 2

def sigma2(p):
    return sum(p[i] * p[j] for i in range(len(p)) for j in range(i + 1, len(p)))

def gen(total, k, minv):
    if k == 1:
        if total >= minv: yield (total,)
        return
    for first in range(minv, total - minv * (k - 1) + 1):
        for rest in gen(total - first, k - 1, minv):
            yield (first,) + rest

# lemma3 setup: r parts = l ones + k big parts (k=r-l>=2), each big >=2, n = l + sum(big) + 1
# candidate simplified bounds (want each <= t_r(n)):
#  (A) sigma2(1^l, big) + n - 2 + sav              [drop m entirely]
#  (Ap) sigma2(1^l, big) + l + sum(big) - 1 + sav  [= (A) since n-2 = l+sum(big)-1]
#  (C) sigma2(1^l, big) + l + sum(big) - ns - nt + 1 + sav   [constr_le, ns,nt two smallest big]
#  (B) full: min over-approx by max_m [ -m1 m2 + sum m ] + sigma2 + l + sav
badA = badC = badB = 0
tightA = tightC = 0
chk = 0
for r in range(2, 8):
    for l in range(0, r - 1):
        k = r - l
        if k < 2: continue
        for bign in range(2 * k, 40 - l):
            n = l + bign + 1
            if n < r + 3 or n > 40: continue
            for big in gen(bign, k, 2):
                chk += 1
                s2 = sigma2([1] * l + list(big))
                # (A)
                A = s2 + n - 2 + sav(n, r)
                if A > t(n, r): badA += 1
                elif A == t(n, r): tightA += 1
                # (C): two smallest big parts
                sb = sorted(big)
                ns, nt = sb[0], sb[1]
                C = s2 + l + sum(big) - ns - nt + 1 + sav(n, r)
                if C > t(n, r): badC += 1
                elif C == t(n, r): tightC += 1
                # (B): worst-case over m in [1,ni]  (only for small to keep fast)
                if k <= 4 and bign <= 16:
                    worst = -10**9
                    for ms in itertools.product(*[range(1, ni + 1) for ni in big]):
                        m1, m2 = sorted(ms)[:2]
                        worst = max(worst, -m1 * m2 + sum(ms))
                    B = s2 + l + worst + sav(n, r)
                    if B > t(n, r): badB += 1
print(f"checked={chk}")
print(f"(A) drop-m:  violations={badA} tight={tightA}")
print(f"(C) constr:  violations={badC} tight={tightC}")
print(f"(B) full-worst-m: violations={badB}")

# --- SUB-LEMMA G (optimization step): does Lemma-3 bound (6) route through constr_le? ---
# Need: sum(m) - m1*m2 <= sum(n) - ns - nt + 1  (ns,nt two smallest n; m1,m2 two smallest m)
# i.e. bound(6) <= e(G(seq)).  If TRUE, combinatorial Lemma 3 can emit e(G)<=e(G(seq)) and
# feed constr_le directly (no separate optimization lemma needed at the interface).
import itertools as it
badG = chk = 0
for k in range(2, 6):
    for bign in range(2*k, 22):
        for nv in gen(bign, k, 2):
            ns_, nt_ = sorted(nv)[:2]
            for ms in it.islice(it.product(*[range(1, ni+1) for ni in nv]), 0, 3000):
                chk += 1
                m1, m2 = sorted(ms)[:2]
                if sum(ms) - m1*m2 > sum(nv) - ns_ - nt_ + 1:
                    badG += 1
print(f"SUBLEMMA-G (bound6 <= e(G(seq))): checked={chk} violations={badG}")
