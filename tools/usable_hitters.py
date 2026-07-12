#!/usr/bin/env python3
"""For each class of each saved balanced K_25: enumerate all 5-sets T with
alpha(G_c - T) <= 4, report per-hitter: internal c-edge count and usability.

Usability (necessary for T to serve as T_c in a one-vertex extension):
T must contain >= 1 edge of every colour c' != c  (else T is an independent
5-set of some other class G_{c'} disjoint from T_{c'}... precisely: in an
extension partition, T_{c'} hits all independent 5-sets of G_{c'}; T_c is
disjoint from T_{c'}, so T_c must NOT be independent in G_{c'}).
Equivalently: M(T) subseteq {c} where M = missing colours of the 5-set.

Usage: .venv/bin/python tools/usable_hitters.py FILE.json [...]
"""
import json, sys
from itertools import combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from lemma_tx import alpha_le


def main():
    for path in sys.argv[1:]:
        d = json.load(open(path))
        M, n = d["colours"], d["n"]
        print(f"== {path}")
        anyusable = False
        for c in range(5):
            adjbits = [0] * n
            for i in range(n):
                for j in range(n):
                    if i != j and M[i][j] == c:
                        adjbits[i] |= 1 << j
            e_c = sum(M[i][j] == c for i in range(n) for j in range(i + 1, n))
            hitters = []
            for T in combinations(range(n), 5):
                rest = [v for v in range(n) if v not in T]
                if alpha_le(adjbits, rest, 4):
                    own = sum(M[a][b] == c for a, b in combinations(T, 2))
                    missing = set(range(5)) - set(M[a][b] for a, b in combinations(T, 2))
                    usable = missing <= {c}
                    hitters.append((T, own, sorted(missing), usable))
                    anyusable |= usable
            us = sum(1 for h in hitters if h[3])
            print(f"  class {c} ({e_c}e): {len(hitters)} hitters, "
                  f"own-edge counts {sorted(h[1] for h in hitters)}, usable: {us}"
                  + (f"  {[h for h in hitters if h[3]][:2]}" if us else ""))
        print(f"  => extension {'NOT excluded by hitter usability' if anyusable else 'excluded: some class... (check all classes usable=0? see above)'}")


if __name__ == "__main__":
    main()
