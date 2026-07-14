#!/bin/bash
# Self-chaining ladder for balanced 6-colourings (r=6): climb n -> n+1 by warm-starting each
# rung from the previous rung's solution plus one random vertex. This is the r=5 ladder
# methodology (RESULTS.md R6: warm-chaining is ~1000x faster than cold). A rung that fails to
# reach 0 within MAXSTEPS across ATTEMPTS independent tries is the empirical floor for this
# chain (its best-seen colouring is saved for analysis / successor resume).
#
# verify.py is the referee: every 0-violation rung is confirmed BALANCED before we climb.
#
# Usage: warmchain6.sh TAG START_N END_N SEED MAXSTEPS NOISE GREEDYK INIT
#   TAG       label for output/log files (e.g. A)
#   START_N   first rung; END_N last rung to attempt
#   SEED      base seed
#   MAXSTEPS  per-attempt step budget
#   NOISE     random-edge percent (e.g. 12)
#   GREEDYK   greedy edges sampled per step (e.g. 6)
#   INIT      warm start for START_N: a JSON path, or "-" for random
set -u
ATTEMPTS=3                      # independent tries per rung before declaring a floor
ROOT="/Users/winter/research/erdos-617"
cd "$ROOT" || exit 2
TAG="$1"; START_N="$2"; END_N="$3"; SEED="$4"; MAXSTEPS="$5"; NOISE="$6"; GREEDYK="$7"; INIT="$8"
LOG="data/r6/logs/chain_${TAG}.log"
CAND="data/r6/candidates"
mkdir -p "$CAND" data/r6/logs

echo "=== chain $TAG start $(date '+%F %T') : n=${START_N}..${END_N} seed=${SEED} maxsteps=${MAXSTEPS} noise=${NOISE} greedyk=${GREEDYK} attempts=${ATTEMPTS} init=${INIT}" >> "$LOG"

n="$START_N"
prevwin=""                      # last balanced colouring (n-1 vertices); empty at chain start
while [ "$n" -le "$END_N" ]; do
    success=0
    a=1
    while [ "$a" -le "$ATTEMPTS" ]; do
        aseed=$(( SEED + 1000 * a + n ))
        if [ -z "$prevwin" ]; then
            init="$INIT"                        # first rung: use the given INIT (or "-")
        else
            init="${CAND}/chain_${TAG}_n${n}.init${a}.json"
            python3 tools/extend_vertex6.py "$prevwin" "$init" "$aseed" >> "$LOG" 2>&1
        fi
        best="${CAND}/chain_${TAG}_n${n}.best.json"
        win="${CAND}/chain_${TAG}_n${n}.win.json"
        tmp="${CAND}/chain_${TAG}_n${n}.attempt${a}.tmp"
        echo "--- [$(date '+%T')] chain $TAG rung n=$n attempt $a/$ATTEMPTS (seed $aseed) init=$init" >> "$LOG"
        # locsearch6 prints JSON to stdout ONLY on a 0-violation success; write it to a .tmp and
        # promote to .win.json ONLY after verify.py confirms it, so a .win.json is always a witness
        # (never an empty placeholder that a name-based scan could misread as a verified win).
        ./tools/locsearch6 "$n" "$aseed" "$MAXSTEPS" "$init" "$NOISE" "$best" "$GREEDYK" > "$tmp" 2>> "$LOG"
        if [ -s "$tmp" ] && python3 tools/verify.py "$tmp" >> "$LOG" 2>&1; then
            mv "$tmp" "$win"
            echo "*** WIN chain $TAG n=$n BALANCED (verify.py, attempt $a) -> $win" | tee -a "$LOG"
            prevwin="$win"; success=1; break
        else
            rm -f "$tmp"
            echo "    chain $TAG n=$n attempt $a did not reach a verified 0" >> "$LOG"
        fi
        a=$(( a + 1 ))
    done
    if [ "$success" -eq 1 ]; then
        n=$(( n + 1 ))
    else
        echo ">>> FLOOR chain $TAG: rung n=$n unsolved in $ATTEMPTS x $MAXSTEPS steps; best-seen in ${CAND}/chain_${TAG}_n${n}.best.json" | tee -a "$LOG"
        break
    fi
done
echo "=== chain $TAG done $(date '+%F %T') at floor n=$((n-1)) (highest verified balanced)" >> "$LOG"
