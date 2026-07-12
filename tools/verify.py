#!/usr/bin/env python3
"""Ground-truth checker for balanced r-colourings (Erdős problem #617).

DO NOT MODIFY THIS FILE. It is the referee for this repo. If you believe it is
wrong, document your reasoning in NOTES.md and stop for review.

A candidate colouring is a JSON file:

    {
      "r": 5,                  // number of colours
      "n": 26,                 // number of vertices
      "colours": [[...], ...]  // n x n symmetric matrix; entries in 0..r-1; diagonal -1
    }

Definition (PROBLEM.md): the colouring is BALANCED iff every (r+1)-subset of
vertices sees all r colours among the C(r+1,2) edges inside it.

Usage:
    python3 tools/verify.py CANDIDATE.json      # full scan; prints verdict + violation count
    python3 tools/verify.py --selftest          # verify the checker against known cases

Exit codes: 0 = BALANCED, 1 = NOT balanced, 2 = malformed input / selftest failure.

Note for search code: this checker does a full O(n^(r+1)) scan and is the
referee, not the engine. Local search should implement its own incremental
scoring and call this only on promising candidates.
"""
import sys, json, time
from itertools import combinations


def load(path):
    with open(path) as f:
        d = json.load(f)
    r, n, M = d["r"], d["n"], d["colours"]
    if not (isinstance(r, int) and r >= 2):
        raise ValueError("r must be an integer >= 2")
    if not (isinstance(n, int) and n >= r + 1):
        raise ValueError("n must be an integer >= r+1")
    if len(M) != n or any(len(row) != n for row in M):
        raise ValueError("colours must be an n x n matrix")
    for i in range(n):
        if M[i][i] != -1:
            raise ValueError(f"diagonal entry ({i},{i}) must be -1")
        for j in range(n):
            if i == j:
                continue
            c = M[i][j]
            if not (isinstance(c, int) and 0 <= c < r):
                raise ValueError(f"entry ({i},{j})={c!r} not an integer in 0..{r-1}")
            if M[j][i] != c:
                raise ValueError(f"matrix not symmetric at ({i},{j})")
    return r, n, M


def check(r, n, M, max_report=5):
    """Full scan. Returns (balanced, total_subsets, violations, examples)."""
    full = (1 << r) - 1
    violations = 0
    examples = []
    total = 0
    for S in combinations(range(n), r + 1):
        total += 1
        seen = 0
        for a in range(r):  # a < b over the subset; early exit when all colours seen
            row = M[S[a]]
            for b in range(a + 1, r + 1):
                seen |= 1 << row[S[b]]
            if seen == full:
                break
        if seen != full:
            violations += 1
            if len(examples) < max_report:
                missing = [c for c in range(r) if not (seen >> c) & 1]
                examples.append((S, missing))
    return violations == 0, total, violations, examples


def report(r, n, M, label=""):
    t0 = time.time()
    balanced, total, violations, examples = check(r, n, M)
    dt = time.time() - t0
    tag = f" [{label}]" if label else ""
    if balanced:
        print(f"BALANCED{tag}: r={r}, n={n}; all {total} subsets of size {r+1} see all {r} colours. ({dt:.2f}s)")
    else:
        print(f"NOT BALANCED{tag}: r={r}, n={n}; {violations} of {total} subsets miss a colour. ({dt:.2f}s)")
        for S, missing in examples:
            print(f"  e.g. subset {S} missing colour(s) {missing}")
    return balanced


def pentagon():
    """r=2, n=5 balanced witness: cycle edges colour 0, diagonals colour 1."""
    n = 5
    M = [[-1] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                M[i][j] = 0 if (j - i) % n in (1, n - 1) else 1
    return 2, n, M


def selftest():
    ok = True

    # 1. Pentagon must be balanced.
    r, n, M = pentagon()
    if report(r, n, M, "pentagon r=2 n=5"):
        print("  expected BALANCED: ok")
    else:
        print("  SELFTEST FAILURE: pentagon should be balanced"); ok = False

    # 1b. Cross-check the on-disk copy if present.
    import os
    p = os.path.join(os.path.dirname(__file__), "..", "data", "small_cases", "pentagon_r2.json")
    if os.path.exists(p):
        rf, nf, Mf = load(p)
        if (rf, nf, Mf) == (r, n, M):
            print("  data/small_cases/pentagon_r2.json matches the in-memory witness: ok")
        else:
            print("  SELFTEST FAILURE: on-disk pentagon differs from in-memory witness"); ok = False

    # 2. Monochromatic K5 (r=2) must fail with exactly C(5,3)=10 violations.
    M1 = [[-1 if i == j else 0 for j in range(5)] for i in range(5)]
    balanced, total, violations, _ = check(2, 5, M1)
    if not balanced and violations == 10 and total == 10:
        print("mono K5: 10/10 subsets violate: ok")
    else:
        print(f"SELFTEST FAILURE: mono K5 gave balanced={balanced}, violations={violations}/{total}"); ok = False

    # 3. Malformed input must be rejected.
    try:
        bad = {"r": 2, "n": 3, "colours": [[-1, 0, 1], [1, -1, 0], [1, 0, -1]]}  # asymmetric
        import tempfile
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
            json.dump(bad, f); tmp = f.name
        load(tmp)
        print("SELFTEST FAILURE: asymmetric matrix accepted"); ok = False
    except ValueError:
        print("asymmetric input rejected: ok")

    # 4. Deterministic pseudo-random 5-colouring of K26: overwhelmingly likely NOT balanced.
    #    (Timing here is the benchmark for the full n=26 scan.)
    #    LCG so the matrix is identical across runs and platforms.
    state = 20260705
    M2 = [[-1] * 26 for _ in range(26)]
    for i in range(26):
        for j in range(i + 1, 26):
            state = (state * 6364136223846793005 + 1442695040888963407) % (1 << 64)
            c = (state >> 33) % 5
            M2[i][j] = M2[j][i] = c
    balanced = report(5, 26, M2, "pseudo-random r=5 n=26")
    if balanced:
        print("  !!! pseudo-random colouring is BALANCED - if reproducible this DISPROVES the conjecture; save and verify immediately")
    else:
        print("  expected NOT BALANCED for random colouring: ok")

    print("SELFTEST", "PASSED" if ok else "FAILED")
    return 0 if ok else 2


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--selftest":
        sys.exit(selftest())
    if len(sys.argv) != 2:
        print(__doc__); sys.exit(2)
    try:
        r, n, M = load(sys.argv[1])
    except (ValueError, KeyError, json.JSONDecodeError, OSError) as e:
        print(f"MALFORMED INPUT: {e}"); sys.exit(2)
    sys.exit(0 if report(r, n, M) else 1)


if __name__ == "__main__":
    main()
