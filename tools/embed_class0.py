#!/usr/bin/env python3
"""Phase-2 seed: embed a Phase-1 class-0 graph (alpha<=5, cap-16) as colour 0 of a 6-colouring,
with the complement edges given a spread of colours 1..5. Then run the FREEZE0 Phase-2 search:

    FREEZE0=1 ./tools/locsearch6a N SEED MAXSTEPS OUT.json NOISE BEST GREEDYK

which fixes class 0 and only recolours 1..5 to reach alpha(G_c)<=6 + cap-16 (object A).

Usage: python3 tools/embed_class0.py GRAPH.json OUT.json [SEED]
"""
import json, sys, random

def main():
    g = json.load(open(sys.argv[1])); out = sys.argv[2]
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    n, A = g["n"], g["adj"]
    rng = random.Random(seed)
    M = [[-1] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if A[i][j]:
                M[i][j] = M[j][i] = 0                       # class 0 = the Phase-1 graph
            else:
                M[i][j] = M[j][i] = 1 + ((i + 2 * j + rng.randrange(5)) % 5)   # spread 1..5
    json.dump({"r": 6, "n": n, "colours": M}, open(out, "w"))
    m0 = sum(A[i][j] for i in range(n) for j in range(i + 1, n))
    print(f"embedded class-0 graph ({m0} edges) as colour 0; {n*(n-1)//2 - m0} between-edges spread 1..5 -> {out}")

if __name__ == "__main__":
    main()
