#!/usr/bin/env python3
"""Batch experiment: sample balanced 5-colourings of K_25 by local search,
referee each with tools/verify.py, test one-vertex extendability (SAT), and
record structural invariants including the hitting numbers h_c.

h_c := min |T| such that the colour-c class minus T has no independent 5-set
(equivalently alpha(G_c - T) <= 4). A balanced K_25 colouring extends to K_26
only if V splits into disjoint T_0..T_4 with alpha(G_c - T_c) <= 4, so
sum_c h_c <= 25 is necessary.

Usage: .venv/bin/python tools/batch25.py SEED_START SEED_END [--no-h]
Appends one TSV line per seed to data/batch25_results.tsv.
--no-h skips the (slower) exact hitting-number computation.
Non-converging seeds (120k-step budget) are skipped silently-ish.
"""
import json, os, subprocess, sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

ROOT = os.path.join(os.path.dirname(__file__), "..")


def independent_5sets(adj, n=25):
    """All independent 5-subsets of graph given by adjacency matrix (True=edge)."""
    out = []
    # prune with sorted enumeration
    for S in combinations(range(n), 5):
        ok = True
        for a in range(4):
            for b in range(a + 1, 5):
                if adj[S[a]][S[b]]:
                    ok = False; break
            if not ok: break
        if ok:
            out.append(S)
    return out


def hitting_number(sets5, n=25):
    """Exact min-size vertex set hitting every set in sets5 (SAT + card, decreasing k)."""
    if not sets5:
        return 0
    # greedy upper bound
    from collections import Counter
    rem = list(sets5); T = set()
    while rem:
        cnt = Counter(v for S in rem for v in S)
        v = cnt.most_common(1)[0][0]
        T.add(v); rem = [S for S in rem if v not in S]
    ub = len(T)
    k = ub
    while k > 0:
        s = Cadical195()
        for S in sets5:
            s.add_clause([v + 1 for v in S])
        cnf = CardEnc.atmost(lits=list(range(1, n + 1)), bound=k - 1, top_id=n, encoding=EncType.seqcounter)
        for cl in cnf.clauses:
            s.add_clause(cl)
        if s.solve():
            k -= 1; s.delete()
        else:
            s.delete(); return k
    return 0


def analyse(path):
    d = json.load(open(path))
    M, n, r = d["colours"], d["n"], d["r"]
    sizes, monos, hs = [], [], []
    for c in range(r):
        adj = [[M[i][j] == c for j in range(n)] for i in range(n)]
        sizes.append(sum(adj[i][j] for i in range(n) for j in range(i + 1, n)))
        i5 = independent_5sets(adj, n)
        mono = sum(1 for F in combinations(range(n), 5)
                   if all(M[a][b] == c for a, b in combinations(F, 2)))
        monos.append(mono)
        hs.append(hitting_number(i5, n))
    return sizes, monos, hs


def main():
    s0, s1 = int(sys.argv[1]), int(sys.argv[2])
    no_h = "--no-h" in sys.argv
    outp = os.path.join(ROOT, "data", "batch25_results.tsv")
    newf = not os.path.exists(outp)
    with open(outp, "a") as out:
        if newf:
            out.write("seed\tverified\textends\tsizes\tmonoK5\th_c\tsum_h\n")
        for seed in range(s0, s1 + 1):
            cand = os.path.join(ROOT, "data", "candidates", f"b25_{seed}.json")
            p = subprocess.run([os.path.join(ROOT, "tools", "locsearch"), "25", str(seed), "120000", "-", "10"],
                               capture_output=True, text=True)
            if p.returncode != 0:
                continue  # non-converged seed: skip
            open(cand, "w").write(p.stdout)
            v = subprocess.run(["python3", os.path.join(ROOT, "tools", "verify.py"), cand],
                               capture_output=True, text=True)
            verified = v.stdout.startswith("BALANCED")
            e = subprocess.run([sys.executable, os.path.join(ROOT, "tools", "extend.py"), cand],
                               capture_output=True, text=True)
            extends = "SAT #1" in e.stdout
            if no_h:
                d = json.load(open(cand)); M, n = d["colours"], d["n"]
                sizes = [sum(M[i][j] == c for i in range(n) for j in range(i + 1, n)) for c in range(5)]
                monos = [sum(1 for F in combinations(range(n), 5)
                             if all(M[a][b] == c for a, b in combinations(F, 2))) for c in range(5)]
                hs = [-1] * 5
            else:
                sizes, monos, hs = analyse(cand)
            line = f"{seed}\t{verified}\t{extends}\t{sorted(sizes)}\t{sum(monos)}\t{sorted(hs)}\t{sum(hs)}"
            out.write(line + "\n"); out.flush()
            print(line, flush=True)
            if extends:
                print(f"!!! seed {seed} EXTENDS - run extend.py --out and verify.py IMMEDIATELY", flush=True)


if __name__ == "__main__":
    main()
