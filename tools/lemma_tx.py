#!/usr/bin/env python3
"""Empirical tests of Lemma T and Lemma X on saved balanced K_25 colourings.

Lemma T (candidate): for every colour c, every 5-set T with
    alpha(G_c - T) <= 4 is a monochromatic-c K_5.
Lemma X (candidate): any two monochromatic K_5s of DIFFERENT colours
    intersect (in exactly one vertex, by edge-disjointness).

For each input file: enumerate all 5-sets T per class with alpha(G_c-T)<=4
(complete enumeration over C(25,5)=53130 subsets x 5 classes, with a cheap
alpha check), classify them, and check pairwise cross-colour intersections
of mono-K_5s.

Usage: .venv/bin/python tools/lemma_tx.py FILE.json [...]
"""
import json, sys
from itertools import combinations


def alpha_le(adjbits, verts, k):
    """alpha(G[verts]) <= k? adjbits[v] = bitmask of neighbours. Small B&B."""
    verts = sorted(verts)

    def rec(cand_mask, size):
        # can we still exceed k?
        if size > k:
            return False
        if cand_mask == 0:
            return True
        rem = bin(cand_mask).count("1")
        if size + rem <= k:
            return True
        v = (cand_mask & -cand_mask).bit_length() - 1
        rest = cand_mask & ~(1 << v)
        if not rec(rest & ~adjbits[v], size + 1):
            return False
        if size + rem - 1 > k:
            if not rec(rest, size):
                return False
        return True

    m = 0
    for v in verts:
        m |= 1 << v
    return rec(m, 0)


def main():
    for path in sys.argv[1:]:
        d = json.load(open(path))
        M, n = d["colours"], d["n"]
        allmono = {}
        report = []
        lemT = True
        for c in range(5):
            adjbits = [0] * n
            for i in range(n):
                for j in range(n):
                    if i != j and M[i][j] == c:
                        adjbits[i] |= 1 << j
            mono = [F for F in combinations(range(n), 5)
                    if all(M[a][b] == c for a, b in combinations(F, 2))]
            allmono[c] = [set(F) for F in mono]
            monoset = set(map(frozenset, mono))
            hitters, nonmono_hitters = 0, []
            for T in combinations(range(n), 5):
                rest = [v for v in range(n) if v not in T]
                if alpha_le(adjbits, rest, 4):
                    hitters += 1
                    if frozenset(T) not in monoset:
                        nonmono_hitters.append(T)
            if nonmono_hitters:
                lemT = False
            report.append((c, len(mono), hitters, len(nonmono_hitters),
                           nonmono_hitters[:3]))
        # Lemma X
        xviol = []
        for c1 in range(5):
            for c2 in range(c1 + 1, 5):
                for A in allmono[c1]:
                    for B in allmono[c2]:
                        if not (A & B):
                            xviol.append((c1, c2, sorted(A), sorted(B)))
        print(f"== {path}")
        for c, nm, nh, nnm, ex in report:
            print(f"  class {c}: {nm} mono-K5s, {nh} minimal hitting 5-sets, "
                  f"{nnm} NON-mono hitters{(' e.g. ' + str(ex)) if ex else ''}")
        print(f"  Lemma T: {'HOLDS' if lemT else 'FAILS'};  "
              f"Lemma X: {'HOLDS' if not xviol else f'FAILS ({len(xviol)} disjoint cross-colour pairs, e.g. {xviol[:1]})'}")


if __name__ == "__main__":
    main()
