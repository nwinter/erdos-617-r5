#!/bin/bash
# Resumable cube worker: solve every cube in CUBEDIR with kissat + DRAT,
# check each UNSAT proof with drat-trim, record verdicts. Idempotent: cubes
# with a recorded verified verdict are skipped, so spot preemptions are
# harmless — just rerun this script (or run it on many machines against a
# shared/synced CUBEDIR; workers claim cubes via atomic mkdir locks).
#
# Usage: run_cubes.sh CUBEDIR [JOBS]
# Env:   KISSAT (default kissat), DRATTRIM (default drat-trim),
#        KEEP_PROOFS=1 to keep .drat files (default: delete after check).
#
# Outputs per cube in CUBEDIR/results/: cube_<i>.verdict containing
# "UNSAT VERIFIED" | "SAT" (+ model file) | "UNSAT UNVERIFIED(reason)".
# Exit summary: counts. ALL cubes "UNSAT VERIFIED" => base CNF is UNSAT.
set -u
CUBEDIR=$1
JOBS=${2:-$(sysctl -n hw.ncpu 2>/dev/null || nproc)}
KISSAT=${KISSAT:-kissat}
DRATTRIM=${DRATTRIM:-drat-trim}
RES="$CUBEDIR/results"; LOCKS="$CUBEDIR/locks"
mkdir -p "$RES" "$LOCKS"

solve_one() {
  local cnf=$1
  local id
  id=$(basename "$cnf" .cnf)
  local verdict="$RES/$id.verdict"
  [ -s "$verdict" ] && return 0                      # already done
  mkdir "$LOCKS/$id" 2>/dev/null || return 0         # someone else has it
  trap 'rmdir "$LOCKS/'"$id"'" 2>/dev/null' RETURN
  local drat="$RES/$id.drat" out="$RES/$id.out"
  "$KISSAT" -q "$cnf" "$drat" > "$out" 2>&1
  if grep -q "^s SATISFIABLE" "$out"; then
    grep "^v" "$out" > "$RES/$id.model"
    echo "SAT" > "$verdict"                          # base has a model!
  elif grep -q "^s UNSATISFIABLE" "$out"; then
    if "$DRATTRIM" "$cnf" "$drat" | grep -q VERIFIED; then
      echo "UNSAT VERIFIED" > "$verdict"
    else
      echo "UNSAT UNVERIFIED(drat-trim failed)" > "$verdict"
    fi
  else
    return 1                                         # killed/preempted: retry later
  fi
  [ "${KEEP_PROOFS:-0}" = "1" ] || rm -f "$drat"
}
export -f solve_one 2>/dev/null || true
export RES LOCKS KISSAT DRATTRIM KEEP_PROOFS

# simple portable job pool (avoids GNU parallel dependency)
i=0
for cnf in "$CUBEDIR"/cube_*.cnf; do
  solve_one "$cnf" &
  i=$((i+1))
  [ $((i % JOBS)) -eq 0 ] && wait
done
wait

sat=$(grep -l "^SAT" "$RES"/*.verdict 2>/dev/null | wc -l | tr -d ' ')
okv=$(grep -l "UNSAT VERIFIED" "$RES"/*.verdict 2>/dev/null | wc -l | tr -d ' ')
tot=$(ls "$CUBEDIR"/cube_*.cnf | wc -l | tr -d ' ')
echo "cubes: $tot, UNSAT-verified: $okv, SAT: $sat, pending: $((tot - okv - sat))"
[ "$sat" -gt 0 ] && echo "!!! SAT cube found - base is SATISFIABLE; decode the model"
[ "$okv" = "$tot" ] && echo "ALL CUBES UNSAT+VERIFIED => BASE CNF IS UNSAT (certified)"
