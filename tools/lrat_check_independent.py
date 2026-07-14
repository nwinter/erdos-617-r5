#!/usr/bin/env python3
"""Independent strict RUP-LRAT checker (Task B, ROUND-2026-07-14).

Written from the LRAT specification, with no dependency on the external
candidate's bundled checkers.  A clause addition is accepted only if reverse
unit propagation over the *listed positive hints*, starting from the negation
of the new clause, reaches a conflict; every intermediate hint must be a unit
under the running assignment and the chain must end in a conflict.  Deletions
are tracked; a deleted or unknown clause used as a hint is rejected.  Clause
ids must be fresh and monotone.  The proof is accepted only if the empty clause
is derived (i.e. the formula is certified UNSAT).  Any deviation is rejected.

Scope: RUP proofs only (all hints positive).  A negative hint (RAT step) is
rejected outright rather than silently accepted -- the load-bearing bundle was
verified RAT-free before this checker was relied upon.

Usage:  lrat_check_independent.py CNF LRAT
Exit 0 == certified UNSAT; nonzero == rejected / not UNSAT.
"""
from __future__ import annotations
import sys


class LRATError(Exception):
    pass


def read_cnf(path):
    nvars = ncls = None
    clauses = []
    cur = []
    with open(path) as f:
        for raw in f:
            s = raw.strip()
            if not s or s[0] == "c":
                continue
            if s[0] == "p":
                fld = s.split()
                if len(fld) != 4 or fld[1] != "cnf":
                    raise LRATError("malformed DIMACS header")
                nvars, ncls = int(fld[2]), int(fld[3])
                continue
            for tok in s.split():
                v = int(tok)
                if v == 0:
                    clauses.append(tuple(cur))
                    cur = []
                else:
                    if nvars is not None and abs(v) > nvars:
                        raise LRATError(f"literal {v} exceeds header nvars {nvars}")
                    cur.append(v)
    if cur:
        raise LRATError("CNF ends mid-clause (missing 0)")
    if ncls is not None and len(clauses) != ncls:
        raise LRATError(f"CNF clause count {len(clauses)} != header {ncls}")
    return nvars, clauses


def rup_derives(clause, hints, db, assign):
    """Strict RUP-with-hints. assign: dict var->bool (scratch, pre-cleared).

    Assign the negation of `clause`; then walk hints in order.  Each hint must
    be a unit (extend assignment) until one hint is fully falsified (conflict).
    Returns True on conflict, raises LRATError on any malformed step.
    """
    for lit in clause:
        v = abs(lit)
        want = lit < 0            # negation of clause: literal lit is made false
        if v in assign and assign[v] != want:
            raise LRATError("tautological clause / inconsistent negation")
        assign[v] = want
    for h in hints:
        if h <= 0:
            raise LRATError("negative/zero hint (RAT unsupported by this checker)")
        if h not in db:
            raise LRATError(f"hint {h} refers to a deleted or unknown clause")
        unassigned = None
        conflict = True
        for lit in db[h]:
            v = abs(lit)
            val = assign.get(v)
            if val is None:
                if unassigned is not None:
                    # two or more unassigned -> not unit -> cannot propagate here
                    raise LRATError(f"hint {h} is not unit under the running assignment")
                unassigned = lit
                conflict = False
            elif val == (lit > 0):
                raise LRATError(f"hint {h} is already satisfied in the RUP chain")
            # else: literal false, continue
        if conflict:
            return True
        # unit: force the single unassigned literal true
        assign[abs(unassigned)] = unassigned > 0
    raise LRATError("hint chain exhausted without reaching a conflict")


def check(cnf_path, lrat_path):
    nvars, clauses = read_cnf(cnf_path)
    db = {}
    for i, cl in enumerate(clauses, 1):
        db[i] = cl
    max_id = len(clauses)
    additions = deletions = 0
    empty_derived = False
    seen_ids = set(db)
    with open(lrat_path) as f:
        for lineno, raw in enumerate(f, 1):
            fld = raw.split()
            if not fld:
                continue
            try:
                cid = int(fld[0])
            except ValueError:
                raise LRATError(f"line {lineno}: bad clause id {fld[0]!r}")
            if len(fld) >= 2 and fld[1] == "d":
                for tok in fld[2:]:
                    d = int(tok)
                    if d == 0:
                        break
                    db.pop(d, None)          # tolerate double-delete, but drop it
                deletions += 1
                continue
            vals = list(map(int, fld[1:]))
            try:
                split = vals.index(0)
            except ValueError:
                raise LRATError(f"line {lineno}: missing clause terminator")
            clause = vals[:split]
            rest = vals[split + 1:]
            if not rest or rest[-1] != 0:
                raise LRATError(f"line {lineno}: missing hint terminator")
            hints = rest[:-1]
            if cid <= max_id or cid in seen_ids:
                raise LRATError(f"line {lineno}: clause id {cid} reused or not fresh")
            assign = {}
            rup_derives(clause, hints, db, assign)   # raises on failure
            db[cid] = tuple(clause)
            seen_ids.add(cid)
            max_id = cid
            additions += 1
            if not clause:
                empty_derived = True
                break    # empty clause reached: UNSAT established
    if not empty_derived:
        raise LRATError("proof did not derive the empty clause")
    return {"verified": True, "unsat": True, "nvars": nvars,
            "initial_clauses": len(clauses), "additions": additions,
            "deletions": deletions}


def main(argv):
    if len(argv) != 3:
        print(__doc__)
        return 2
    try:
        res = check(argv[1], argv[2])
    except LRATError as e:
        print(f"REJECTED: {e}")
        return 1
    print(f"VERIFIED UNSAT: initial={res['initial_clauses']} "
          f"additions={res['additions']} deletions={res['deletions']} "
          f"nvars={res['nvars']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
