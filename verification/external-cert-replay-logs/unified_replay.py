#!/usr/bin/env python3
"""Task B: full independent audit of the 66th (unified) certificate."""
from __future__ import annotations
import hashlib, json, subprocess, sys, time
from pathlib import Path

REPO = Path("/Users/winter/research/erdos-617")
U = REPO / "review_queue/external-candidate-B/cert-bundle/p25_defect_unified/certificates"
WS = Path("/private/tmp/claude-501/-Users-winter-research-erdos-617/6e908324-b2c0-4c6c-9413-c6d8812a5533/scratchpad/taskB")
sys.path.insert(0, str(REPO / "tools"))
from lrat_check_independent import check as lrat_check, read_cnf, LRATError

t0 = time.time()
res = {}
origin = json.loads((U / "unified_unsym.origin.json").read_text())

# 1. full CNF hash already confirmed; parse regenerated full CNF
full_cnf = WS / "unified_full.cnf"
h = hashlib.sha256(full_cnf.read_bytes()).hexdigest()
res["full_cnf_sha256_match"] = (h == origin["full_cnf_sha256"])
fnv, fcl = read_cnf(full_cnf)
res["full_clauses_match"] = (len(fcl) == origin["full_clauses"])
res["full_variables_match"] = (fnv == origin["full_variables"])
print(f"[{time.time()-t0:.0f}s] full parsed: {len(fcl)} clauses, {fnv} vars, hash_match={res['full_cnf_sha256_match']}")

# 2. independent origin-map audit
_cn, compact = read_cnf(U / "unified_unsym.cnf")
ids = list(map(int, origin["selected_original_clause_ids"]))
old = list(map(int, origin["new_to_old_variable"]))
res["injective"] = (len(old) == len(set(old)))
res["old_in_range"] = (min(old) >= 1 and max(old) <= fnv)
res["counts_match"] = (len(compact) == len(ids) == origin["selected_clauses"])
res["ids_increasing"] = all(ids[i] < ids[i+1] for i in range(len(ids)-1))
res["ids_in_range"] = (min(ids) >= 1 and max(ids) <= len(fcl))
mismatches = 0
for cclause, cid in zip(compact, ids):
    recon = tuple(old[abs(l)-1] if l > 0 else -old[abs(l)-1] for l in cclause)
    if recon != fcl[cid-1]:
        mismatches += 1
res["origin_reconstructs"] = (mismatches == 0)
res["origin_mismatches"] = mismatches
res["origin_ok"] = all([res["injective"], res["old_in_range"], res["counts_match"],
                        res["ids_increasing"], res["ids_in_range"], res["origin_reconstructs"]])
print(f"[{time.time()-t0:.0f}s] origin audit: injective={res['injective']} "
      f"reconstructs={res['origin_reconstructs']} (mismatches={mismatches}) ok={res['origin_ok']}")

# 3. kissat re-solve compact (fault diversity)
r = subprocess.run(["kissat", "-q", str(U / "unified_unsym.cnf")],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
res["kissat_rc"] = r.returncode
res["kissat_unsat"] = (r.returncode == 20)
print(f"[{time.time()-t0:.0f}s] kissat compact: {'UNSAT' if res['kissat_unsat'] else r.returncode}")

# 4. our-checker replay of the 38MB LRAT (slow)
print(f"[{time.time()-t0:.0f}s] replaying unified LRAT with our checker ...", flush=True)
try:
    lr = lrat_check(str(U / "unified_unsym.cnf"), str(U / "unified_unsym.lrat"))
    res["lrat_verified"] = lr["verified"] and lr["unsat"]
    res["lrat_additions"] = lr["additions"]
    res["lrat_deletions"] = lr["deletions"]
except LRATError as e:
    res["lrat_verified"] = False
    res["lrat_error"] = str(e)
print(f"[{time.time()-t0:.0f}s] LRAT replay: verified={res.get('lrat_verified')} "
      f"add={res.get('lrat_additions')} del={res.get('lrat_deletions')} err={res.get('lrat_error')}")

res["all_ok"] = all([res["full_cnf_sha256_match"], res["full_clauses_match"],
                     res["origin_ok"], res["kissat_unsat"], res.get("lrat_verified", False)])
print(f"[{time.time()-t0:.0f}s] UNIFIED all_ok = {res['all_ok']}")
(WS / "unified_result.json").write_text(json.dumps(res, indent=1))
print("wrote unified_result.json")
