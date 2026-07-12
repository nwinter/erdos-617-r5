#!/usr/bin/env python3
"""Export the minority-lemma constraint system as a static DIMACS CNF, for
INDEPENDENT verification with a different solver (kissat) + DRAT + drat-trim.

Constraints (same mathematical content as tools/minority.py, but built here
with a DIFFERENT global cardinality encoding — totalizer instead of
seqcounter — and no incremental solving):
  - one boolean per edge of K_n (vars 1..C(n,2), lex order)
  - every (a+1)-subset: at least one edge
  - every (a+1)-subset: at least one non-edge (K_{a+1}-free; subsumed by caps
    when present, kept anyway — harmless)
  - global: at most M edges (totalizer)
  - local caps: for each subset S listed in CAPS.json: at most D edges of S
    (totalizer). CAPS.json comes from a converged tools/minority.py --cegar
    run. UNSAT of this static CNF is sound for the lemma: it is a SUBSET of
    the full constraint family {every (a+1)-set spans <= D edges}.

Usage: .venv/bin/python tools/minority_export.py N A M CAPS.json OUT.cnf
       (CAPS.json may be the string "none" for no local caps)
"""
import json, sys
from itertools import combinations
from pysat.card import CardEnc, EncType


def main():
    n, a, m = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    capsf, outf = sys.argv[4], sys.argv[5]
    D = (a + 1) * a // 2 - (a - 1)
    ev = {}
    k = 0
    for i, j in combinations(range(n), 2):
        k += 1
        ev[(i, j)] = k
    top = k
    clauses = []
    for S in combinations(range(n), a + 1):
        lits = [ev[(x, y)] for x, y in combinations(S, 2)]
        clauses.append(lits)
        clauses.append([-l for l in lits])
    card = CardEnc.atmost(lits=list(range(1, k + 1)), bound=m,
                          top_id=top, encoding=EncType.totalizer)
    clauses.extend(card.clauses)
    top = max(top, card.nv)
    ncaps = 0
    if capsf != "none":
        caps = json.load(open(capsf))
        assert caps["n"] == n and caps["a"] == a and caps["D"] == D
        for S in caps["capped_subsets"]:
            lits = [ev[tuple(sorted((x, y)))] for x, y in combinations(S, 2)]
            loc = CardEnc.atmost(lits=lits, bound=D, top_id=top,
                                 encoding=EncType.totalizer)
            clauses.extend(loc.clauses)
            top = max(top, loc.nv)
            ncaps += 1
    with open(outf, "w") as f:
        f.write(f"p cnf {top} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    print(f"wrote {outf}: {top} vars, {len(clauses)} clauses, {ncaps} local caps, D={D}")


if __name__ == "__main__":
    main()
