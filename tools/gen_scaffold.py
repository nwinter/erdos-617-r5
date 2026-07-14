#!/usr/bin/env python3
"""Object-A scaffold seed (n<=30): class 0 = 5 disjoint cliques (each <=6, so alpha(G_0)=5 and
no class-0 cap violation), between-edges given a spread of colours 1..5 for a Phase-2 freeze
search (FREEZE0=1 ./tools/locsearch6a ...). Cliques cap at 5*6=30 vertices — at n=31 class 0
cannot be a union of cliques (cap-16 forbids K_7), which is why n=31 needs the two-phase attack.

Usage: python3 tools/gen_scaffold.py N OUT.json [SEED]
"""
import json, sys, random

def main():
    n = int(sys.argv[1]); out = sys.argv[2]
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    if n > 30:
        sys.exit("scaffold (5 cliques <=6) only reaches n=30; n=31 needs the two-phase attack")
    # 5 clique sizes as balanced as possible, each <=6
    sizes = [n // 5 + (1 if i < n % 5 else 0) for i in range(5)]
    assert max(sizes) <= 6 and sum(sizes) == n, sizes
    parts, v = [], 0
    for s in sizes:
        parts.append(list(range(v, v + s))); v += s
    part_of = {u: i for i, p in enumerate(parts) for u in p}
    pos = {u: k for p in parts for k, u in enumerate(p)}
    rng = random.Random(seed)
    M = [[-1] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if part_of[i] == part_of[j]:
                M[i][j] = M[j][i] = 0                       # within-clique -> class 0
            else:                                            # between -> spread of 1..5
                pi, pj = part_of[i], part_of[j]
                c = 1 + ((pos[i] + 2 * pos[j] + 3 * (pi + pj) + rng.randrange(5)) % 5)
                M[i][j] = M[j][i] = c
    json.dump({"r": 6, "n": n, "colours": M}, open(out, "w"))
    print(f"scaffold n={n} clique sizes {sizes} -> {out}")

if __name__ == "__main__":
    main()
