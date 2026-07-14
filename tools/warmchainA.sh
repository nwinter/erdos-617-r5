#!/bin/bash
# Warm-chaining hunt for r=6 "object A" (task #77): climb n -> n+1 keeping the A-profile
# (cap-16, alpha(G_0)<=5, alpha(G_c)<=6) at total=0. Seeds from AG(2,5)-unmerged K_25 (itself
# object A). The money rung is n=31: an object A there refutes the [MH2]-analogue.
#
# Each rung's 0-violation hit is INDEPENDENTLY re-verified by tools/checkA.py (house rule: the
# checker shares no code with the search scorer) before climbing. Witnesses saved under data/r6/.
#
# Usage: warmchainA.sh TAG START_N END_N SEED MAXSTEPS NOISE GREEDYK INIT
set -u
ATTEMPTS=3
ROOT="/Users/winter/research/erdos-617"
cd "$ROOT" || exit 2
TAG="$1"; START_N="$2"; END_N="$3"; SEED="$4"; MAXSTEPS="$5"; NOISE="$6"; GREEDYK="$7"; INIT="$8"
LOG="data/r6/logs/hunt_${TAG}.log"
CAND="data/r6/candidates"
mkdir -p "$CAND" data/r6/logs
echo "=== hunt $TAG start $(date '+%F %T') : n=${START_N}..${END_N} seed=${SEED} maxsteps=${MAXSTEPS} noise=${NOISE} greedyk=${GREEDYK} init=${INIT}" >> "$LOG"

n="$START_N"; prevwin=""
while [ "$n" -le "$END_N" ]; do
    success=0; a=1
    while [ "$a" -le "$ATTEMPTS" ]; do
        aseed=$(( SEED + 1000*a + n ))
        if [ -z "$prevwin" ]; then init="$INIT"; else
            init="${CAND}/hunt_${TAG}_n${n}.init${a}.json"
            python3 tools/extend_vertex6.py "$prevwin" "$init" "$aseed" >> "$LOG" 2>&1
        fi
        best="${CAND}/hunt_${TAG}_n${n}.best.json"; win="${CAND}/hunt_${TAG}_n${n}.win.json"
        tmp="${CAND}/hunt_${TAG}_n${n}.attempt${a}.tmp"
        echo "--- [$(date '+%T')] hunt $TAG rung n=$n attempt $a/$ATTEMPTS (seed $aseed)" >> "$LOG"
        # locsearch6a prints JSON to stdout ONLY on total=0; capture to .tmp and promote to
        # .win.json ONLY after checkA confirms it, so a .win.json is always a verified object A.
        ./tools/locsearch6a "$n" "$aseed" "$MAXSTEPS" "$init" "$NOISE" "$best" "$GREEDYK" > "$tmp" 2>> "$LOG"
        if [ -s "$tmp" ] && python3 tools/checkA.py "$tmp" >> "$LOG" 2>&1; then
            mv "$tmp" "$win"
            echo "*** OBJECT A chain $TAG n=$n CONFIRMED (checkA, attempt $a) -> $win" | tee -a "$LOG"
            cp "$win" "${CAND}/objA_n${n}.json"      # keep the highest per-n witness
            prevwin="$win"; success=1; break
        else
            rm -f "$tmp"
            echo "    hunt $TAG n=$n attempt $a did not reach a checkA-confirmed 0" >> "$LOG"
        fi
        a=$(( a + 1 ))
    done
    if [ "$success" -eq 1 ]; then n=$(( n + 1 )); else
        echo ">>> WALL hunt $TAG: object A not found at n=$n in $ATTEMPTS x $MAXSTEPS steps; best in ${CAND}/hunt_${TAG}_n${n}.best.json" | tee -a "$LOG"
        break
    fi
done
echo "=== hunt $TAG done $(date '+%F %T') at highest object-A n=$((n-1))" >> "$LOG"
