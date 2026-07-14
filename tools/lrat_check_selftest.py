#!/usr/bin/env python3
"""Self-test for lrat_check_independent.py (Task B).

(a) Accepts a known-good cadical LRAT on a 10-variable UNSAT formula
    (pigeonhole PHP(5 pigeons, 2 holes), which needs 5*2 = 10 variables).
(b) Rejects the same proof after each of three corruptions:
      - one RUP hint removed,
      - one clause literal flipped,
      - the final empty-clause line deleted.
Exit 0 iff all sub-tests behave as required.
"""
from __future__ import annotations
import itertools, subprocess, sys, tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lrat_check_independent import check, LRATError


def php_5_2():
    """PHP(5,2): 5 pigeons, 2 holes, var(i,h) = 2*(i-1)+h, i in 1..5, h in 1,2."""
    def var(i, h):
        return 2 * (i - 1) + h
    clauses = []
    for i in range(1, 6):                       # each pigeon in some hole
        clauses.append([var(i, 1), var(i, 2)])
    for h in (1, 2):                            # no two pigeons share a hole
        for i, j in itertools.combinations(range(1, 6), 2):
            clauses.append([-var(i, h), -var(j, h)])
    return 10, clauses


def write_cnf(path, nvars, clauses):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")


def expect_accept(cnf, lrat, label):
    try:
        res = check(cnf, lrat)
        print(f"  [PASS] {label}: VERIFIED UNSAT "
              f"(add={res['additions']} del={res['deletions']})")
        return True
    except LRATError as e:
        print(f"  [FAIL] {label}: expected accept, got REJECTED: {e}")
        return False


def expect_reject(cnf, lrat, label):
    try:
        check(cnf, lrat)
        print(f"  [FAIL] {label}: expected REJECT, but it verified")
        return False
    except LRATError as e:
        print(f"  [PASS] {label}: correctly REJECTED ({e})")
        return True


def main():
    ok = True
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        cnf = d / "php52.cnf"
        lrat = d / "php52.lrat"
        nvars, clauses = php_5_2()
        write_cnf(cnf, nvars, clauses)
        proc = subprocess.run(
            ["cadical", "--plain", "--lrat=true", "--binary=false", "-q",
             str(cnf), str(lrat)],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if proc.returncode != 20:
            print(f"  [FAIL] cadical did not report UNSAT (rc={proc.returncode})")
            return 1
        lines = lrat.read_text().splitlines()

        # (a) accept the untouched proof
        ok &= expect_accept(cnf, lrat, "known-good cadical LRAT (10-var PHP)")

        # locate the final empty-clause addition line and a non-empty addition
        def parse(line):
            f = line.split()
            if len(f) >= 2 and f[1] == "d":
                return None
            vals = list(map(int, f[1:]))
            sp = vals.index(0)
            return vals[:sp], vals[sp + 1:-1]  # clause, hints

        empty_idx = None
        litflip_idx = None
        for idx, line in enumerate(lines):
            p = parse(line)
            if p is None:
                continue
            clause, hints = p
            if not clause and empty_idx is None:
                empty_idx = idx
            if clause and litflip_idx is None:
                litflip_idx = idx
        assert empty_idx is not None, "no empty-clause line found"

        # (b1) remove one hint from the empty-clause derivation
        m1 = list(lines)
        f = m1[empty_idx].split()
        # form: id 0 h1 h2 ... 0  -> drop first hint (index 2)
        assert f[1] == "0" and len(f) >= 4
        f2 = f[:2] + f[3:]
        m1[empty_idx] = " ".join(f2)
        p1 = d / "m_hint.lrat"; p1.write_text("\n".join(m1) + "\n")
        ok &= expect_reject(cnf, p1, "one hint removed")

        # (b2) flip one literal in a non-empty learned clause (or in the CNF)
        if litflip_idx is not None:
            m2 = list(lines)
            f = m2[litflip_idx].split()
            f[1] = str(-int(f[1]))          # flip first literal of the clause
            m2[litflip_idx] = " ".join(f)
            p2 = d / "m_flip.lrat"; p2.write_text("\n".join(m2) + "\n")
            ok &= expect_reject(cnf, p2, "one literal flipped (learned clause)")
        else:
            cnf2 = d / "m_flip.cnf"
            cl2 = [list(c) for c in clauses]
            cl2[0][0] = -cl2[0][0]
            write_cnf(cnf2, nvars, cl2)
            ok &= expect_reject(cnf2, lrat, "one literal flipped (CNF clause)")

        # (b3) delete the final empty-clause line
        m3 = [ln for i, ln in enumerate(lines) if i != empty_idx]
        p3 = d / "m_noempty.lrat"; p3.write_text("\n".join(m3) + "\n")
        ok &= expect_reject(cnf, p3, "empty clause deleted")

    print("SELFTEST", "PASSED" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
