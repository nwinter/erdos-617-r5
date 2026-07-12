# Numeric pre-checks (falsify-before-prove) for the TWO arithmetic backbone lemmas
# that let kp_caseB (KP Thm 4 Case B) stay in t_r-form, AVOIDING both the G(n)
# construction formula and KP's "maximality of G" argument.  Both verified: 0 violations.
#
#   two_bad_bound :  sigma2(parts) - min(parts) + kpSaving n r  <=  t_r(n)
#                    for any r parts each >= 2 summing to n.
#     (Case B, two-bad-parts sub-case: paper gives e(G) <= sigma2(d) - (d1+d2)/2
#      <= sigma2(d) - d1; then this arithmetic closes e(G) + kpSaving <= t_r WITHOUT
#      needing "contradicts maximality of G".)
#
#   constr_le :  e(G(seq)) + kpSaving n r  <=  t_r(n)   for every valid r-sequence,
#     where e(G(seq)) = sigma2(seq) + sigma1(seq) - n_s - n_t + 1  (KP formula (4)),
#     seq sums to n-1, >= 2 parts are >1, n_s,n_t = two smallest parts >1.
#     (This is what KP Lemma 3's output "e(G) <= e(G(seq))" feeds into. Proving it
#      = proving pr(n) <= t_r(n) - kpSaving in the *construction* world = Lemma 5/Thm 1
#      optimization, but as PURE ARITHMETIC, no graphs.)  Also confirms
#      max_seq e(G(seq)) == t_r - kpSaving (main regime), i.e. the bound is TIGHT.
from math import comb
from collections import defaultdict

def t(n, r):
    if r == 0: return comb(n, 2)
    q, s = divmod(n, r)
    return comb(n, 2) - ((r - s) * comb(q, 2) + s * comb(q + 1, 2))

def sav(n, r):
    return (n // r - 1) if n >= 2 * r + 1 else 2

def sigma2(parts):
    return sum(parts[i] * parts[j] for i in range(len(parts)) for j in range(i + 1, len(parts)))

def gen(total, r, minv):
    if r == 1:
        if total >= minv: yield (total,)
        return
    for first in range(minv, total - minv * (r - 1) + 1):
        for rest in gen(total - first, r - 1, minv):
            yield (first,) + rest

# --- two_bad_bound ---
bad = tight = checked = 0
for r in range(2, 7):
    for n in range(2 * r, 30):
        for parts in gen(n, r, 2):
            checked += 1
            lhs = sigma2(list(parts)) - min(parts) + sav(n, r)
            if lhs > t(n, r): bad += 1; print("two_bad FAIL", r, n, parts)
            elif lhs == t(n, r): tight += 1
print(f"two_bad_bound: checked={checked} violations={bad} tight={tight}")

# --- constr_le ---
def eG(seq):
    big = sorted(x for x in seq if x > 1)
    return sigma2(list(seq)) + sum(seq) - big[0] - big[1] + 1

bad = tight = checked = 0
mx = defaultdict(int)
for r in range(2, 7):
    for n in range(r + 3, 28):
        for seq in gen(n - 1, r, 1):
            if sum(1 for x in seq if x > 1) < 2: continue
            checked += 1
            lhs = eG(seq) + sav(n, r)
            if lhs > t(n, r): bad += 1; print("constr FAIL", r, n, seq)
            elif lhs == t(n, r): tight += 1
            if n < 22: mx[(n, r)] = max(mx[(n, r)], eG(seq))
print(f"constr_le: checked={checked} violations={bad} tight={tight}")
print("max_seq e(G(seq)) == t_r - kpSaving (main regime):",
      all(mx[(n, r)] == t(n, r) - sav(n, r) for (n, r) in mx if n >= 2 * r + 1))

# --- Lemma3 PRE-optimization bound (BONUS finding, F6i): the successor can SKIP KP's
# "simple optimization" (m1=1, m_i=n_i) step.  The bound BEFORE optimizing already gives
# the target for ALL valid m_i in [1,n_i]:
#   sigma2(1^l, n_1..n_{r-l}) - m1*m2 + l + sum m_i + kpSaving n r  <=  t_r(n)
# (m1,m2 the two smallest m_i; l<=r-2; n_i>=2; n = l + sum n_i + 1).  0 violations / 4.1M.
import itertools
def gen2(total, k, minv):
    if k == 1:
        if total >= minv: yield (total,)
        return
    for f in range(minv, total - minv * (k - 1) + 1):
        for rest in gen2(total - f, k - 1, minv): yield (f,) + rest
bad = checked = 0
for r in range(2, 6):
    for l in range(0, r - 1):
        rl = r - l
        if rl < 2: continue
        for bign in range(2 * rl, 22):
            n = l + bign + 1
            if n > 24: continue
            for ns in gen2(bign, rl, 2):
                s2 = sigma2([1] * l + list(ns))
                for ms in itertools.islice(itertools.product(*[range(1, ni + 1) for ni in ns]), 0, 4000):
                    checked += 1
                    m1, m2 = sorted(ms)[:2]
                    if s2 - m1 * m2 + l + sum(ms) + sav(n, r) > t(n, r): bad += 1
print(f"lemma3_arith (pre-opt): checked={checked} violations={bad}")
