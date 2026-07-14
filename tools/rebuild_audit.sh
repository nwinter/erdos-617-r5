#!/usr/bin/env bash
#
# Reproducible fresh-clone rebuild audit (kernel-pure profile, ROUND-2026-07-14).
#
# Clones THIS repo fresh into a scratch dir (no shared build state), supplies the
# gitignored LRAT certificates, fetches the Mathlib olean cache as any third party
# would, does a full clean `lake build`, then records verbatim `#print axioms`,
# an external `leanchecker` re-check, CNF-encoding-drift checks, fresh CaDiCaL
# re-solves, and — new this round — INDEPENDENT drat-trim re-verification of the
# SAT certificates.
#
# Usage: tools/rebuild_audit.sh <OUTPUT_DIR>
#   OUTPUT_DIR receives all artifacts (default: verification/rebuild-kernel-pure).
#
# Expected end state: build exit 0; unconditional theorems depend on exactly
#   [propext, Classical.choice, Quot.sound, unsat_{nonex11,nonex12,M9,M10} native_decide]
#   = 7 axioms, NO sorryAx, NO KP-construction native_decide axioms.

set -uo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${1:-$REPO_ROOT/verification/rebuild-kernel-pure}"
mkdir -p "$OUT"
STEPS="$OUT/steps.log"; : > "$STEPS"
log(){ echo "$@" | tee -a "$STEPS"; }

WORK="$(mktemp -d)/clone"
# Clean up the (multi-GB, mathlib-cloning) scratch clone even on interrupt/failure,
# so a killed run cannot leave orphaned clones filling the disk.
trap 'rm -rf "$(dirname "$WORK")" 2>/dev/null' EXIT INT TERM
DT="$REPO_ROOT/ext/drat-trim/drat-trim"

log "== [1/9] fresh local clone =="
git clone -q "$REPO_ROOT" "$WORK" 2>&1 | tee -a "$STEPS"
( cd "$WORK" && git rev-parse HEAD > "$OUT/source-commit.txt" && git log --oneline -1 | tee -a "$STEPS" )
cp "$WORK/lean617/lean-toolchain" "$OUT/lean-toolchain"
cp "$WORK/lean617/lake-manifest.json" "$OUT/lake-manifest.json"

log "== [2/9] supply gitignored LRAT certs =="
mkdir -p "$WORK/lean617/Lean617/certs"
for c in nonex11 nonex12 M9 M10; do
  cp "$REPO_ROOT/lean617/Lean617/certs/$c.lrat" "$WORK/lean617/Lean617/certs/$c.lrat"
done
( cd "$WORK/lean617/Lean617/certs" && shasum -a 256 *.lrat > "$OUT/cert-sha256.txt" )
log "  copied 4 certs; sha256 -> cert-sha256.txt"

log "== [3/9] toolchain + machine fingerprint =="
{
  echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "uname: $(uname -a)"
  echo "cpu: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown)"
  echo "mem: $(( $(sysctl -n hw.memsize) / 1073741824 )) GB"
  echo "elan: $(elan --version 2>/dev/null)"
  echo "lean: $(cd "$WORK/lean617" && lake env lean --version 2>/dev/null)"
  echo "lake: $(cd "$WORK/lean617" && lake --version 2>/dev/null | head -1)"
  echo "cadical: $(cadical --version 2>/dev/null)"
  echo "drat-trim: $("$DT" -h 2>&1 | head -1)"
} > "$OUT/fingerprint.txt"
cat "$OUT/fingerprint.txt" | tee -a "$STEPS"

log "== [4/9] mathlib cache fetch =="
( cd "$WORK/lean617" && lake exe cache get 2>&1 | tail -3 ) | tee "$OUT/cache-get.log" | tee -a "$STEPS"

log "== [5/9] full clean lake build (heavy module first, then the rest) =="
# MEMORY-SAFE RECIPE. The kernel-`decide` modules (KPConstruction, JoinTransport,
# EqualityProof) peak at ~6GB each. They are dependency-chained so they never build
# concurrently, but a plain `lake build` can still stack a heavy module with light
# workers. Building KPConstruction first in its own invocation bounds the peak; the
# second `lake build` finishes the rest. (This Lake version has NO `-j` flag.)
( cd "$WORK/lean617" && lake build Lean617.KPConstruction > "$OUT/build.log" 2>&1 \
    && lake build >> "$OUT/build.log" 2>&1 ); bexit=$?
log "  build exit: $bexit"
tail -2 "$OUT/build.log" | tee -a "$STEPS"
gzip -f "$OUT/build.log"

log "== [6/9] axiom prints (verbatim) =="
cat > "$WORK/lean617/AuditAll.lean" <<'LEOF'
import Lean617.Final
#print axioms Erdos617.erdos_617_r5
#print axioms Erdos617.erdos_617_r5_upstream
#print axioms Erdos617.erdos_617_r5_unconditional
#print axioms Erdos617.erdos_617_r5_upstream_unconditional
LEOF
( cd "$WORK/lean617" && lake env lean AuditAll.lean > "$OUT/axioms.txt" 2>&1 ); aexit=$?
log "  axiom-print exit: $aexit"
if grep -qi "sorry" "$OUT/axioms.txt"; then log "  !! sorryAx PRESENT"; else log "  no sorryAx"; fi
grep -c "native_decide" "$OUT/axioms.txt" | xargs -I{} log "  native_decide axiom mentions: {}"

log "== [7/9] leanchecker on key modules =="
: > "$OUT/leanchecker.log"
for m in Lean617.Statements Lean617.Final Lean617.EqualityProof Lean617.JoinTransport Lean617.Primitives Lean617.KPConstruction; do
  ( cd "$WORK/lean617" && lake env leanchecker "$m" >> "$OUT/leanchecker.log" 2>&1 ) \
    && log "  leanchecker $m: exit 0" || log "  leanchecker $m: exit $?"
done

log "== [8/9] SAT-primitive re-checks (CNF drift + re-solve + INDEPENDENT drat-trim) =="
: > "$OUT/sat-recheck.log"
recheck(){ # name emitargs...
  local name="$1"; shift
  local cnf="$WORK/$name.cnf"
  ( cd "$WORK/lean617" && lake env lean --run "$REPO_ROOT/tools/certgen/emit_cnf.lean" "$@" "$cnf" ) >>"$OUT/sat-recheck.log" 2>&1
  local got exp; got="$(shasum -a 256 "$cnf" | awk '{print $1}')"
  exp="$(awk -v p="$name" '$1==p && NF==4 {print $4}' "$REPO_ROOT/tools/certgen/checksums.txt")"
  [ "$got" = "$exp" ] && log "  CNF $name sha256 OK" || log "  !! CNF $name sha256 MISMATCH got=$got"
}
recheck M9 M 9 18
recheck M10 M 10 24
recheck nonex11 nonex 11
recheck nonex12 nonex 12
# fresh re-solve + independent drat-trim verify (fast primitives inline; nonex are hours -> reference)
for nm in M9 M10; do
  cnf="$WORK/$nm.cnf"; drat="$WORK/$nm.drat"
  cadical "$cnf" "$drat" --binary=false --quiet --unsat --inprocessing=false >>"$OUT/sat-recheck.log" 2>&1
  log "  CaDiCaL re-solve $nm exit=$? (20=UNSAT expected)"
  "$DT" "$cnf" "$drat" -L "$WORK/$nm.core.lrat" >"$OUT/drattrim-$nm.log" 2>&1
  grep -q "s VERIFIED" "$OUT/drattrim-$nm.log" && log "  drat-trim $nm: s VERIFIED (independent)" || log "  !! drat-trim $nm NOT verified"
done

log "== [9/9] summary =="
log "  (nonex11/nonex12 fresh re-solve + drat-trim VERIFIED separately; see solve-logs/ and drattrim-nonex*.log)"
log "ALL DONE build=$bexit axioms=$aexit"
log ""
log "Kernel-pure demo (run in working checkout, referenced): m9-kernel-pure-demo.log"
rm -rf "$(dirname "$WORK")"
echo "rebuild audit artifacts in: $OUT"
