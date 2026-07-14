#!/usr/bin/env python3
"""Extend a balanced-colouring candidate by one vertex (warm-start seed for n -> n+1).

Reads an n-vertex r=6 colouring (verify.py format) and writes an (n+1)-vertex colouring with a
new vertex whose n new edges are coloured randomly in 0..5 (seeded). The old n x n block is
copied verbatim, so if the input is balanced on K_n the output agrees with it on the old
vertices -- exactly the warm start that made the r=5 ladder ~1000x faster than cold search.

Usage: python3 tools/extend_vertex6.py IN.json OUT.json [SEED]
"""
import json, sys, random

def main():
    if len(sys.argv) < 3:
        sys.exit("usage: extend_vertex6.py IN.json OUT.json [SEED]")
    inp, outp = sys.argv[1], sys.argv[2]
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    d = json.load(open(inp))
    r, n, M = d["r"], d["n"], d["colours"]
    rng = random.Random(seed)
    m = n + 1
    NM = [[-1] * m for _ in range(m)]
    for i in range(n):
        for j in range(n):
            NM[i][j] = M[i][j]
    for i in range(n):
        c = rng.randrange(r)
        NM[i][n] = NM[n][i] = c
    json.dump({"r": r, "n": m, "colours": NM}, open(outp, "w"))
    print(f"extended n={n} -> n={m} (seed {seed}) -> {outp}")

if __name__ == "__main__":
    main()
