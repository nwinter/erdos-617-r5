#!/usr/bin/env python3
"""Exhaustive check of the r=7 weight-vector lemma used in
review_queue/mm-gpt56-candidate.md, §5 ("If r=7"), and required as a
hand-checkable finite fact by requirement 4 of the external review
(review_queue/reviews-received/review-of-our-r5-by-external-team.md).

Claim: the only nonnegative integer 5-tuple (d_1,...,d_5) with sum 12 in which
at least seven of the ten pair-sums d_i+d_j (i<j) are >= 6 is (0,0,0,6,6),
up to order.

This is a self-contained finite enumeration (no dependencies); it corroborates
the hand proof given inline in the candidate document. A hand proof is the
primary artifact; this script is the machine cross-check.
"""
from itertools import combinations_with_replacement, combinations


def solutions():
    out = []
    for t in combinations_with_replacement(range(0, 13), 5):
        if sum(t) != 12:
            continue
        ge6 = sum(1 for a, b in combinations(t, 2) if a + b >= 6)
        if ge6 >= 7:
            out.append((tuple(sorted(t)), ge6))
    return sorted(set(out))


def main():
    sols = solutions()
    print("nonneg integer 5-tuples, sum 12, >=7 pair-sums >=6:")
    for t, k in sols:
        print(f"   {t}   (#pair-sums>=6 = {k})")
    uniq = {t for t, _ in sols}
    ok = uniq == {(0, 0, 0, 6, 6)}
    print(f"unique solution is (0,0,0,6,6): {'OK' if ok else '*** MISMATCH ***'}")


if __name__ == "__main__":
    main()
