#!/usr/bin/env python3
"""Decode a SAT model (kissat/cadical 'v' lines) into a colouring JSON.

Usage: python3 tools/sat_decode.py MAP.map.json SOLVER_OUTPUT.txt OUT.json
Then run tools/verify.py OUT.json — verify.py is the referee.
"""
import json, sys


def main():
    mapf, solf, outf = sys.argv[1:4]
    with open(mapf) as f:
        mp = json.load(f)
    r, n, edges = mp["r"], mp["n"], [tuple(e) for e in mp["edges"]]
    true_vars = set()
    with open(solf) as f:
        for line in f:
            if line.startswith("v"):
                for tok in line.split()[1:]:
                    x = int(tok)
                    if x > 0:
                        true_vars.add(x)
    M = [[-1] * n for _ in range(n)]
    for k, (i, j) in enumerate(edges):
        cs = [c for c in range(r) if (k * r + c + 1) in true_vars]
        if len(cs) != 1:
            print(f"decode error: edge {(i,j)} has colours {cs}"); sys.exit(2)
        M[i][j] = M[j][i] = cs[0]
    with open(outf, "w") as f:
        json.dump({"r": r, "n": n, "colours": M}, f)
    print(f"wrote {outf}; now run: python3 tools/verify.py {outf}")


if __name__ == "__main__":
    main()
