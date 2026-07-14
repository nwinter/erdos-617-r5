#!/usr/bin/env python3
"""Task B steps 3-5: regenerate full CNFs, audit origin maps (independently),
replay compact LRATs with OUR checker, re-solve compact CNFs with kissat.

Every verdict here comes from: subprocess(cadical/kissat), our regeneration of
the bundle encoders, and our own lrat_check_independent + origin reconstruction.
The bundle's lrat_core / check_lrat are NOT imported.
"""
from __future__ import annotations
import hashlib, json, subprocess, sys, tempfile, time
from pathlib import Path

REPO = Path("/Users/winter/research/erdos-617")
BUNDLE = REPO / "review_queue/external-candidate-B/cert-bundle"
P25 = BUNDLE / "p25_certificate"
sys.path.insert(0, str(REPO / "tools"))
from lrat_check_independent import check as lrat_check, read_cnf, LRATError

ENV = {"PYTHONDONTWRITEBYTECODE": "1", "PATH": __import__("os").environ["PATH"]}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def regen_signature(name, out):
    subprocess.run([sys.executable, "encode.py", "--pattern", name, "--output", str(out)],
                   cwd=P25, env=ENV, check=True, stdout=subprocess.DEVNULL)


def regen_orbit(idx, out):
    subprocess.run([sys.executable, "defect_lemma.py", "--mask-index", str(idx), "--output", str(out)],
                   cwd=P25, env=ENV, check=True, stdout=subprocess.DEVNULL)


def audit_origin(full_clauses, full_nvars, compact_cnf, origin):
    """Independent origin-map audit. Returns dict of findings; raises on failure."""
    _cn, compact = read_cnf(compact_cnf)
    ids = list(map(int, origin["selected_original_clause_ids"]))
    old = list(map(int, origin["new_to_old_variable"]))
    # (i) renaming injective (review requirement 2)
    if len(old) != len(set(old)):
        raise AssertionError("new_to_old_variable is NOT injective")
    # (ii) old vars are valid full-formula variables
    if old and (min(old) < 1 or max(old) > full_nvars):
        raise AssertionError("new_to_old maps outside full variable range")
    # (iii) compact clause count matches recorded id count
    if len(compact) != len(ids):
        raise AssertionError(f"compact clauses {len(compact)} != recorded ids {len(ids)}")
    # (iv) selected ids in range and strictly increasing (well-formed core)
    if ids and (min(ids) < 1 or max(ids) > len(full_clauses)):
        raise AssertionError("selected_original_clause_ids out of range")
    if any(ids[i] >= ids[i + 1] for i in range(len(ids) - 1)):
        raise AssertionError("selected_original_clause_ids not strictly increasing")
    # (v) every compact clause de-renames to the exact recorded full clause
    for cclause, cid in zip(compact, ids):
        for lit in cclause:
            if abs(lit) < 1 or abs(lit) > len(old):
                raise AssertionError("compact literal outside compact var range")
        recon = tuple(old[abs(l) - 1] if l > 0 else -old[abs(l) - 1] for l in cclause)
        if recon != full_clauses[cid - 1]:
            raise AssertionError(f"compact clause != full[{cid}] under renaming")
    return {"compact_clauses": len(compact), "compact_vars": len(old),
            "injective": True, "origin_reconstructs": True}


def kissat(path):
    r = subprocess.run(["kissat", "-q", str(path)], stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL)
    return r.returncode  # 20=UNSAT, 10=SAT


def process(kind, key, regen_fn, compact_cnf, compact_lrat, origin_path, tmp):
    row = {"kind": kind, "key": key}
    origin = json.loads(Path(origin_path).read_text())
    full = tmp / "full.cnf"
    regen_fn(full)
    h = sha256(full)
    row["full_cnf_sha256_match"] = (h == origin["full_cnf_sha256"])
    row["full_cnf_sha256"] = h
    fnv, fcl = read_cnf(full)
    # sanity: regenerated full clause count matches origin record
    row["full_clauses_match"] = (len(fcl) == origin["full_clauses"])
    try:
        row.update(audit_origin(fcl, fnv, compact_cnf, origin))
        row["origin_ok"] = True
    except AssertionError as e:
        row["origin_ok"] = False
        row["origin_error"] = str(e)
    # LRAT replay with OUR checker
    try:
        res = lrat_check(str(compact_cnf), str(compact_lrat))
        row["lrat_verified"] = res["verified"] and res["unsat"]
        row["lrat_additions"] = res["additions"]
        row["lrat_deletions"] = res["deletions"]
    except LRATError as e:
        row["lrat_verified"] = False
        row["lrat_error"] = str(e)
    # kissat fault-diversity re-solve of compact CNF
    row["kissat_rc"] = kissat(compact_cnf)
    row["kissat_unsat"] = (row["kissat_rc"] == 20)
    return row


def main():
    t0 = time.time()
    rows = []
    man = json.loads((P25 / "full_p25_manifest.json").read_text())
    dman = json.loads((P25 / "defect_manifest.json").read_text())
    with tempfile.TemporaryDirectory() as d:
        tmp = Path(d)
        # 7 signatures
        for pat in man["patterns"]:
            name = pat["pattern"]
            row = process("signature", name,
                          lambda out, n=name: regen_signature(n, out),
                          P25 / pat["compact_cnf"], P25 / pat["compact_lrat"],
                          P25 / pat["origin"], tmp)
            rows.append(row)
            print(f"[sig {name:12s}] full_hash={'OK' if row['full_cnf_sha256_match'] else 'MISMATCH'} "
                  f"origin={'OK' if row['origin_ok'] else 'FAIL'} "
                  f"lrat={'UNSAT' if row['lrat_verified'] else 'FAIL'} "
                  f"kissat={'UNSAT' if row['kissat_unsat'] else row['kissat_rc']} "
                  f"({time.time()-t0:.0f}s)", flush=True)
        # 58 orbits
        for br in dman["branches"]:
            idx = br["mask_index"]
            row = process("orbit", idx,
                          lambda out, i=idx: regen_orbit(i, out),
                          P25 / br["compact_cnf"], P25 / br["compact_lrat"],
                          P25 / br["origin"], tmp)
            rows.append(row)
            if idx % 10 == 0 or not (row["full_cnf_sha256_match"] and row["origin_ok"] and row["lrat_verified"] and row["kissat_unsat"]):
                print(f"[orbit {idx:02d}] full_hash={'OK' if row['full_cnf_sha256_match'] else 'MISMATCH'} "
                      f"origin={'OK' if row['origin_ok'] else 'FAIL'} "
                      f"lrat={'UNSAT' if row['lrat_verified'] else 'FAIL'} "
                      f"kissat={'UNSAT' if row['kissat_unsat'] else row['kissat_rc']} "
                      f"({time.time()-t0:.0f}s)", flush=True)
    # summary
    def allok(r):
        return r["full_cnf_sha256_match"] and r["full_clauses_match"] and r["origin_ok"] and r["lrat_verified"] and r["kissat_unsat"]
    n_ok = sum(allok(r) for r in rows)
    print(f"\n=== {n_ok}/{len(rows)} fully verified (hash+origin+lrat+kissat) in {time.time()-t0:.0f}s ===")
    for r in rows:
        if not allok(r):
            print("  NOT-FULLY-OK:", r["kind"], r["key"],
                  {k: r.get(k) for k in ("full_cnf_sha256_match", "full_clauses_match", "origin_ok", "origin_error", "lrat_verified", "lrat_error", "kissat_rc")})
    Path("/private/tmp/claude-501/-Users-winter-research-erdos-617/6e908324-b2c0-4c6c-9413-c6d8812a5533/scratchpad/taskB/replay_66.json").write_text(json.dumps(rows, indent=1))
    print("wrote replay_66.json")


if __name__ == "__main__":
    main()
