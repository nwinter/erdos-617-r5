#!/usr/bin/env python3
"""INDEPENDENT checker for a Phase-1 class-0 candidate graph (task #77). No shared code with
graph_a5cap.c. Reads {"n":N,"adj":[[0/1 matrix]]} and verifies, by direct enumeration:
  alpha(G) <= 5  : no independent 6-set (every 6-set has >=1 edge);
  cap-16         : no 7-set spans >=17 edges.
Reports edge count. Exit 0 iff both hold.
Usage: python3 tools/checkG.py GRAPH.json
"""
import sys, json
from itertools import combinations

def main():
    d = json.load(open(sys.argv[1]))
    n, A = d["n"], d["adj"]
    assert len(A) == n and all(len(r) == n for r in A)
    for i in range(n):
        assert A[i][i] == 0
        for j in range(n):
            assert A[i][j] == A[j][i] and A[i][j] in (0, 1)
    m = sum(A[i][j] for i in range(n) for j in range(i + 1, n))
    indep6 = k6 = 0
    for S in combinations(range(n), 6):
        e = sum(A[a][b] for a, b in combinations(S, 2))
        if e == 0:
            indep6 += 1        # independent 6-set => alpha>=6
        elif e == 15:
            k6 += 1            # complete K_6 => omega>=6
    overcap = 0
    for S in combinations(range(n), 7):
        if sum(A[a][b] for a, b in combinations(S, 2)) >= 17:
            overcap += 1
    ok = (indep6 == 0 and overcap == 0 and k6 == 0)
    print(f"checkG: n={n} edges={m}  independent-6-sets={indep6} (alpha<=5 iff 0)  K_6s={k6} (omega<=5 iff 0)  overcap-7-sets={overcap} (cap-16 iff 0)")
    print("  =>", "VALID class-0 graph (alpha<=5, omega<=5, cap-16)" if ok else "NOT valid")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
