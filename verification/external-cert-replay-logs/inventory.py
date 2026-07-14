#!/usr/bin/env python3
"""Task B step 1: inventory + hashes + manifest cross-checks (independent)."""
import hashlib, json, os, sys
from pathlib import Path

BUNDLE = Path("/Users/winter/research/erdos-617/review_queue/external-candidate-B/cert-bundle")
P25 = BUNDLE / "p25_certificate"
UNIFIED = BUNDLE / "p25_defect_unified"

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()

def rat_scan(lrat_path):
    """Return (n_add, n_del, n_empty, has_rat, malformed) for an LRAT file."""
    n_add = n_del = n_empty = 0
    has_rat = False
    malformed = None
    with open(lrat_path) as f:
        for lineno, raw in enumerate(f, 1):
            fields = raw.split()
            if not fields:
                continue
            if len(fields) >= 2 and fields[1] == "d":
                n_del += 1
                continue
            vals = list(map(int, fields[1:]))
            try:
                split = vals.index(0)
            except ValueError:
                malformed = f"line {lineno}: no clause terminator"
                break
            clause = vals[:split]
            rest = vals[split + 1:]
            if not rest or rest[-1] != 0:
                malformed = f"line {lineno}: no hint terminator"
                break
            hints = rest[:-1]
            if any(h < 0 for h in hints):
                has_rat = True
            n_add += 1
            if not clause:
                n_empty += 1
    return n_add, n_del, n_empty, has_rat, malformed

report = {"files": {}, "checks": []}

# 1. hash every file in bundle
allfiles = sorted(p for p in BUNDLE.rglob("*") if p.is_file())
for p in allfiles:
    report["files"][str(p.relative_to(BUNDLE))] = {"sha256": sha256(p), "bytes": p.stat().st_size}
print(f"hashed {len(allfiles)} files")

# 2. RAT scan of all 66 LRATs
lrats = sorted(BUNDLE.rglob("*.lrat"))
rat_any = False
for lr in lrats:
    na, nd, ne, rat, mal = rat_scan(lr)
    rel = str(lr.relative_to(BUNDLE))
    report["files"][rel].update({"lrat_add": na, "lrat_del": nd, "lrat_empty": ne, "lrat_has_rat": rat, "lrat_malformed": mal})
    if rat:
        rat_any = True
    if mal:
        print(f"MALFORMED {rel}: {mal}")
    if ne != 1:
        print(f"WARN {rel}: empty-clause derivations = {ne} (expected 1)")
print(f"scanned {len(lrats)} LRATs; any RAT steps = {rat_any}")

# 3. full_p25_manifest cross-check
man = json.loads((P25 / "full_p25_manifest.json").read_text())
def check(name, ok, detail=""):
    report["checks"].append({"name": name, "ok": bool(ok), "detail": detail})
    if not ok:
        print(f"  FAIL {name}: {detail}")

for pat in man["patterns"]:
    base = P25
    ccnf = base / pat["compact_cnf"]
    clrat = base / pat["compact_lrat"]
    origin = base / pat["origin"]
    h_cnf = sha256(ccnf); h_lrat = sha256(clrat)
    check(f"full_p25/{pat['pattern']}/compact_cnf_sha", h_cnf == pat["compact_cnf_sha256"], f"{h_cnf} vs {pat['compact_cnf_sha256']}")
    check(f"full_p25/{pat['pattern']}/compact_lrat_sha", h_lrat == pat["compact_lrat_sha256"], f"{h_lrat} vs {pat['compact_lrat_sha256']}")
    orig = json.loads(origin.read_text())
    # origin's own recorded compact hashes must match committed files
    check(f"full_p25/{pat['pattern']}/origin_compact_cnf_sha", orig["compact_cnf_sha256"] == h_cnf, f"origin={orig['compact_cnf_sha256']}")
    check(f"full_p25/{pat['pattern']}/origin_compact_lrat_sha", orig.get("compact_lrat_sha256") == h_lrat, f"origin={orig.get('compact_lrat_sha256')}")
    # manifest compact_variables / clauses vs origin
    check(f"full_p25/{pat['pattern']}/compact_vars", pat["compact_variables"] == orig["compact_variables"], f"{pat['compact_variables']} vs {orig['compact_variables']}")

# 4. defect_manifest cross-check
dman = json.loads((P25 / "defect_manifest.json").read_text())
print(f"defect manifest: orbit_count={dman.get('orbit_count')}, branches={len(dman['branches'])}")
for br in dman["branches"]:
    ccnf = P25 / br["compact_cnf"]
    clrat = P25 / br["compact_lrat"]
    origin = P25 / br["origin"]
    h_cnf = sha256(ccnf); h_lrat = sha256(clrat)
    mi = br["mask_index"]
    check(f"defect/mask_{mi:02d}/compact_cnf_sha", h_cnf == br["compact_cnf_sha256"], f"{h_cnf} vs {br['compact_cnf_sha256']}")
    check(f"defect/mask_{mi:02d}/compact_lrat_sha", h_lrat == br["compact_lrat_sha256"], f"{h_lrat} vs {br['compact_lrat_sha256']}")
    orig = json.loads(origin.read_text())
    check(f"defect/mask_{mi:02d}/origin_compact_cnf_sha", orig["compact_cnf_sha256"] == h_cnf, "")

# 5. unified
uo = json.loads((UNIFIED / "certificates" / "unified_unsym.origin.json").read_text())
ucnf = UNIFIED / "certificates" / "unified_unsym.cnf"
ulrat = UNIFIED / "certificates" / "unified_unsym.lrat"
h_ucnf = sha256(ucnf); h_ulrat = sha256(ulrat)
check("unified/origin_compact_cnf_sha", uo["compact_cnf_sha256"] == h_ucnf, f"origin={uo['compact_cnf_sha256']} file={h_ucnf}")
check("unified/origin_compact_lrat_sha", uo.get("compact_lrat_sha256") == h_ulrat, f"origin={uo.get('compact_lrat_sha256')} file={h_ulrat}")
print(f"unified: full_cnf_sha256={uo['full_cnf_sha256']}, compact_vars={uo['compact_variables']}, full_clauses={uo['full_clauses']}")

# 6. manifest file hash vs candidate's recorded 028eef...
man_hash = sha256(P25 / "full_p25_manifest.json")
RECORDED = "028eefead2cb883ffd3f47e64ae5a3a005f3442417c9178f4b010c4e63626a75"
report["manifest_file_sha256"] = man_hash
report["manifest_recorded_sha256"] = RECORDED
report["manifest_hash_match"] = (man_hash == RECORDED)
print(f"\nfull_p25_manifest.json sha256 = {man_hash}")
print(f"candidate recorded            = {RECORDED}")
print(f"MATCH = {man_hash == RECORDED}")

# 7. control file hashes recorded inside manifests
control_full = sha256(P25 / "full_p25_budget66_control.json")
check("full control_sha256 in manifest", man.get("control_sha256") == control_full, f"{man.get('control_sha256')} vs {control_full}")
control_cap12 = sha256(P25 / "cap12_control.json")
check("cap12 control_sha256 in defect manifest", dman.get("cap12_control_sha256") == control_cap12, f"{dman.get('cap12_control_sha256')} vs {control_cap12}")
orbit_audit = sha256(P25 / "mask_orbits.json")
check("orbit_audit_sha256 in defect manifest", dman.get("orbit_audit_sha256") == orbit_audit, f"{dman.get('orbit_audit_sha256')} vs {orbit_audit}")

n_fail = sum(1 for c in report["checks"] if not c["ok"])
print(f"\n=== {len(report['checks'])} checks, {n_fail} FAIL ===")
Path("/private/tmp/claude-501/-Users-winter-research-erdos-617/6e908324-b2c0-4c6c-9413-c6d8812a5533/scratchpad/taskB/inventory_report.json").write_text(json.dumps(report, indent=1, sort_keys=True))
print("wrote inventory_report.json")
