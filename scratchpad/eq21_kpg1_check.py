"""D4 numeric pre-check for kpG1 (|A*|=1 variant), the |A*|=1 iso class.
Verifies exactly the facts kpG1's Lean native_decide lemmas will assert:
  e(kpG1)=173, K6-free, alpha<=4, and AB21 on the complement with A={4,5,6,7,20},B={0,1,2,3}.
Mirrors kpRel in KPConstruction.lean but with A*={0} (singleton)."""
from itertools import combinations

def kpRel1(a, b):
    if a == b:
        return False
    if a < 20 and b < 20:
        # complete 5-partite minus edges {4,0}
        return (a // 4 != b // 4) and not (
            (a == 4 and b == 0) or (b == 4 and a == 0))
    o = b if a == 20 else a
    return o == 0 or o == 4 or (8 <= o < 20)

adj = [[kpRel1(a, b) for b in range(21)] for a in range(21)]
# symmetry + loopless sanity
assert all(adj[a][b] == adj[b][a] for a in range(21) for b in range(21))
assert all(not adj[a][a] for a in range(21))

def compl(a, b):
    return a != b and not adj[a][b]

# edge count
E = sum(1 for a in range(21) for b in range(a+1, 21) if adj[a][b])
print(f"e(kpG1) = {E}  (want 173)")

# K6-free: no 6-clique
def is_clique(S):
    return all(adj[a][b] for a, b in combinations(S, 2))
k6 = any(is_clique(S) for S in combinations(range(21), 6))
print(f"has K6: {k6}  (want False)")

# alpha <= 4: no independent 5-set
def is_indep(S):
    return all(not adj[a][b] for a, b in combinations(S, 2))
ind5 = any(is_indep(S) for S in combinations(range(21), 5))
print(f"has independent 5-set: {ind5}  (want False)")

# AB21 on complement F = kpG1^c with A={4,5,6,7,20}, B={0,1,2,3}
A = [4, 5, 6, 7, 20]; B = [0, 1, 2, 3]
def eF(S):
    return sum(1 for a, b in combinations(S, 2) if compl(a, b))
eA, eB, eAB = eF(A), eF(B), eF(A+B)
nonA = [(a, b) for a, b in combinations(A, 2) if not compl(a, b)]
print(f"e_F(A)={eA} (want 9), nonedges in A={nonA} (want exactly [(4,20)]), "
      f"e_F(B)={eB} (want 6), e_F(A∪B)={eAB} (want 19)")
ok = E == 173 and not k6 and not ind5 and eA == 9 and nonA == [(4, 20)] and eB == 6 and eAB == 19
print("ALL kpG1 D4 facts hold:", ok)
