#!/usr/bin/env python3
"""Crux probe: does a balanced 5-colouring of K_25 exist in which some colour
class c has a 4-vertex hitting set T with alpha(G_c - T) <= 4?

WLOG (vertex relabelling; colour relabelling) c = 0 and T = {0,1,2,3}.
Encoding: balanced-K_25 base (no symmetry breaking beyond the WLOG fixing,
which uses up the freedom) + for every 5-subset S of {4,...,24}: some edge
inside S has colour 0.

UNSAT  => Lemma H'': every class of every balanced 5-colouring of K_25 has
          hitting number >= 5 (all extension parts have size exactly 5) —
          restores the extension-obstruction chain (see NOTES.md).
SAT    => exotic colourings exist; extract witness and TEST EXTENSION
          immediately (they evade the main obstruction).

Usage: python3 tools/probe_h4.py --out X.cnf   (then kissat)
"""
import argparse, json, sys, os
from itertools import combinations

sys.path.insert(0, os.path.dirname(__file__))
from sat_encode import build


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    r, n = 5, 25
    nv, clauses, edges = build(r, n, set())  # NO symmetry breaking: WLOG uses it
    eidx = {e: i for i, e in enumerate(edges)}
    v = lambda k, c: k * r + c + 1
    extra = 0
    for S in combinations(range(4, n), 5):
        clauses.append([v(eidx[(x, y)], 0) for x, y in combinations(S, 2)])
        extra += 1
    with open(a.out, "w") as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    with open(a.out.replace(".cnf", "") + ".map.json", "w") as f:
        json.dump({"r": r, "n": n, "edges": edges, "sym": []}, f)
    print(f"wrote {a.out}: {nv} vars, {len(clauses)} clauses ({extra} h4 clauses)")


if __name__ == "__main__":
    main()
