# r=6 ladder: determining N(6) — the largest n with a balanced 6-colouring of K_n

**STATUS (2026-07-14, n=29 WALL-RUNG ASSAULT):** The ladder = the joint gate (object A = balanced
K_31 + one class α≤5; see r6/blocker-hunt.md). Verified floor **N(6) ≥ 28**. n=29 EXHAUSTION EVENT:
the first 5-chain fleet (G/H/P/Q/R) all FLOORED at n=28 — 3 attempts each at n=29 (2–3M steps),
best-seen residuals H=3, P=7, R=9, Q=17, G=30 (chain_*_n29.best.json). Best died at ~1–3
violations = STICKY ENDGAME, not an r=5-grade wall (those pinned at 24+ for ≥18h). RELAUNCHED a
focused n=29 assault (wall-rung protocol, this file's §6): 5 chains W1–W5 warm-started from the
best snapshots (W1/W2 from H=3, W3 from P=7, W4 from R=9, W5 fresh-perturbed from balanced_n28),
endgame-tuned params (noise 3–5, greedyk 16–20), 6M steps × 3 attempts, FIXED verified-win-only
script. Logs: `data/r6/logs/chain_W{1..5}.log`. Escalation bar: if all 5 fresh warm attempts die
pinned at 1–3 residual for hours, THEN treat 29 as candidate-wall and run the R6 evidence
discipline (longer runs, more seeds, deficiency-signature analysis). On a win: verify, commit,
warm-chain 30. Next lever if the simple assault fails: the "final-violation tactic" (bias moves
onto the vertices of the residual violated 7-set(s) — needs a small locsearch6 change).

**STATUS (2026-07-13, setup + launch + climbing):** r=6 search tooling built, validated against
the referee, and a warm-chaining ladder fleet launched and climbing. Goal: find the empirical
wall N(6) = largest n admitting a balanced 6-colouring of K_n (every 7 vertices see all 6
colours). Conjecture (Erdős–Gyárfás, PROBLEM.md) predicts N(6) ≤ 36 = 6²; there is **no affine
plane of order 6**, so unlike r=5 there is no construction known to reach 36. Open interval
**[26, 36]**.

**Verified this session: N(6) ≥ 28** (referee-checked witnesses balanced_n20/26/28.json).
- **N(6) ≥ 26** by construction: AG(2,5) UNMERGED as 6 colours on K_25 (each class = 5 disjoint
  K_5's, α=5, balanced) + one vertex (α ≤ 6). General pattern **N(r) ≥ (r−1)²+1 when r−1 is a
  prime power** — `tools/gen_ag_r6.py`, witness `data/r6/candidates/balanced_n26.json`
  (score6=0, verify.py BALANCED; independently cross-checked against the literature agent's
  k26_r6.json, also 0/BALANCED).
- **N(6) ≥ 27, 28** by warm-chaining up from that K_26 (fast: 26→28 in seconds — the ~1000×
  warm speedup). n=29 is the current frontier and is sticky (see §4).

This file is written for a successor session with no memory of this one. `tools/verify.py` is
the untouchable referee; everything here calls it on candidates and never edits it.

---

## 1. Tools built (all in `tools/`, committed)

- **`locsearch6.c` → `locsearch6`** — r=6 local search (fork of `locsearch.c`). Minimizes the
  number of 7-subsets missing a colour by focused random walk with incremental scoring
  (`set_colour`/`delta` over the per-edge subset lists). Fork changes: `R=6`, `NMAX=38`, 7
  nested enumeration loops, `EPS=21` edges/subset, big arrays malloc'd to `NS=C(n,7)`.
  - **Adaptive greedy (critical):** each greedy step evaluates only `GREEDYK` of the 21 edges'
    deltas during bulk descent (cheap — each delta scans `edeg=C(n-2,5)` subsets, e.g. 278k at
    n=36 over a 50MB cnt array = cache-miss-bound), but switches to **full greedy (all 21) +
    low noise (≤5) once violations < `ENDGAME`=3000**. Without this the endgame will not
    converge: with `GREEDYK=4` a cold n=20 stalled at 169 violations after 1.1M steps; with
    the adaptive fix it reaches 0 in 238 steps.
  - Build: `cc -O3 -o tools/locsearch6 tools/locsearch6.c`
  - Usage: `./tools/locsearch6 N SEED MAXSTEPS [INIT.json|- [NOISE_PCT [BESTOUT [GREEDYK]]]]`
    - JSON of a 0-violation solution goes to **stdout only on success**; best-seen always to
      BESTOUT; progress + time-based heartbeats (~30s) to stderr. `MAXSTEPS=0` = score-only.

- **`score6.c` → `score6`** — fast standalone violation scorer (mirrors verify.py's bitmask
  exactly; ~0.02s at n=36). For baseline scoring and cross-checks. NOT the referee.
  Build: `cc -O3 -o tools/score6 tools/score6.c`. Usage: `./tools/score6 CAND.json`.

- **`gen_r6.py`** — builds + scores algebraic K_36 constructions (difference/Cayley colourings
  on Z_6×Z_6, product colourings), writes them to `data/r6/constructions/`, and copies the best
  to `constructions/best_n36.json`. Run: `python3 tools/gen_r6.py`.

- **`extend_vertex6.py`** — extends an n-colouring to n+1 by adding a vertex with random edge
  colours (the warm-start seed for a ladder step). `python3 tools/extend_vertex6.py IN OUT [SEED]`.

- **`warmchain6.sh`** — self-chaining ladder: solve rung n, verify BALANCED, extend by one
  vertex, climb to n+1; up to `ATTEMPTS=3` independent tries per rung before declaring a floor.
  `warmchain6.sh TAG START_N END_N SEED MAXSTEPS NOISE GREEDYK INIT`. Logs to
  `data/r6/logs/chain_<TAG>.log`; per-rung solutions to `data/r6/candidates/chain_<TAG>_n<k>.win.json`.

---

## 2. Validation evidence (done 2026-07-13)

- **Three-way agreement** (referee vs fast scorer vs search's internal count) on deterministic
  random colourings: n=10 → 8 violations by all three; n=12 → 61 by all three. Confirms
  `score6` and `locsearch6`'s enumeration + incremental initial count match `verify.py`.
- **End-to-end**: `locsearch6` driven to 0 at n=20 → `verify.py` reports
  `BALANCED: r=6, n=20; all 77520 subsets of size 7 see all 6 colours`. A wrong incremental
  delta would either stall or emit a false 0 the referee rejects; neither happened. Saved:
  `data/r6/candidates/balanced_n20.json` (referee-verified). (n=20 balanced also follows for
  all n≤20 by monotonicity, so N(6) ≥ 20 trivially; the real question is the top end.)

## 3. Baseline constructions at n=36 (`python3 tools/gen_r6.py`, 2026-07-13)

Violations out of C(36,7)=8,347,680 seven-subsets. **The key finding: algebra alone gets to
~2% violations at n=36 and no closer — the quantitative shadow of "no affine plane of order 6".**

| construction | violations | note |
|---|---|---|
| C_greedy3hard | **172,728** (2.07%) | 3 safe partition-classes (vert/horiz/one diagonal) + greedy pack of the rest into 3 colours — the best |
| A_linear4 | 273,024 | 4 linear classes + best 2-split of leftover difference-classes |
| B_linear3diag | 511,056 | (3,3)-pairs freed to the hard colours |
| P_product | 613,908 | K_6×K_6 rook-ish product |
| random plain | ~950k–1.09M | reference |
| random Cayley | 2.1M–2.9M | *worse* than random-plain — random difference-colourings have very uneven class independence |

Why no better: an affine plane of order 6 would give 7 hexad-partitions covering every pair
exactly once → 6 pigeonhole-safe colours after one merge (the r=5 AG(2,5) trick). Over Z_6 only
the units {1,5} give Latin "slopes", so at most ~3 pairwise-disjoint hexad-partitions exist
(rows, cols, one diagonal); 6 partitions could cover only 6×90=540 < 630 pairs anyway. The
remaining colours are sparse Cayley graphs with large independence → many 7-subsets miss them.
`best_n36.json` (172,728) is a structured warm start, but a **direct** locsearch probe of n=36
from it barely moved (147k after 8k steps at ~128 steps/s) — n=36 is far above the wall.
The wall is found by **climbing warm from below**, not by attacking n=36 cold.

---

## 4. Fleet (current: 3 warm-chaining ladders, after redirecting to the K_26 frontier)

History: launched 5 climbers from n=20 (A–E); trimmed to 3 (A,B,C) at load ~45; then retired the
two redundant low climbers (A,B, at n=24) and launched two chains from the **verified K_26 seed**
once the literature agent supplied it — much more efficient than climbing cold from 20. Current:

| chain | start | seed | noise | greedyk | note |
|---|---|---|---|---|---|
| C | 20 | 3000 | 14 | 5 | independent low climber (cross-check), ~n=25 |
| G | 28 | 9000 | 10 | 8 | frontier, retuned H-style from balanced_n28.json |
| H | 26 | 8000 | 10 | 8 | frontier, from balanced_n26.json |

All → n=37, `MAXSTEPS`=2,000,000/attempt, 3 attempts/rung. G,H climbed 26→28 in seconds.
(G was originally noise 12/greedyk 6 from K_26 and stalled at n=29 in a bad basin at ~3177
violations; retuned to H-style params from the K_28 win per the observation below. Fleet held
at 3 by team-lead direction — the rest of the machine load is the owner's live parallel work.)
- Wrapper PIDs in `data/r6/logs/fleet_pids.txt` (the `warmchain6.sh` shells; the `locsearch6`
  workers are their children, one per chain, changing each rung). Logs `data/r6/logs/chain_{C,G,H}.log`.
- **Signal:** highest n a chain verifies BALANCED before a rung exhausts 3×2M steps is its floor;
  **N(6) ≥ max floor.** Watch for `*** WIN` / `>>> FLOOR`.
- **Current frontier: n=29, and it is STICKY.** Both G and H stall on n=29 attempt 1 (H pinned at
  ~29 residual violations in the full-greedy endgame; G in a worse basin at ~3177). This is NOT
  yet a wall — only attempt 1 of 3 has run, and the endgame is stochastically sticky (cf. cold
  n=25 stalling at 37 yet warm chains solving 25 trivially). If all 3 attempts on n=29 stall
  across multiple chains/seeds, that is real evidence the wall is at 28.
- **Tuning observation:** near the frontier, H (noise 10, greedyk 8) converges far better than
  G (noise 12, greedyk 6) — lower noise + larger greedyk is better once rungs get hard.
- **Read on the wall:** cold search walls in the high-20s; warm-chaining from K_26 reached 28
  instantly and is now working n=29. The parallel theory work (memory note / r6/feasibility.md)
  argues the r=5 chain obstruction *weakens* at r=6 (deficit trend 0,−5,−17,−39 for r=3..6),
  which would let N(6) run higher than the r=5 analogy suggests — possibly well into the 30s.
  So the wall is genuinely open in [28, 36]; let the chains (and more seeds at the sticky rung)
  decide. Do NOT over-trust a single-attempt stall.

### Machine note
Shared machine (20 cores, 64GB). At launch the load was ~28–32 from the user's *other* work
(a "von" python project, the r5 Lean build, long-running r5 SAT probes, desktop apps). Our 5
workers run at ~75% CPU each (contended). Memory grows with n (~1.2GB/worker at n=36). If the
machine is starved, reduce the fleet (see kill recipe) — a floor from fewer chains is still valid.

---

## 5. Kill / resume recipe (survives session restarts — launched via nohup)

**Check status:**
```
grep -hE 'WIN|FLOOR|rung n=' data/r6/logs/chain_*.log | tail
ps -o pid,%cpu,etime,command -ax | grep '[t]ools/locsearch6'   # live workers + their rung
```
**Kill the whole fleet** (wrappers + workers). NB use the exact string `tools/locsearch6` so it
does NOT match the r=5 `tools/locsearch`/`locsearch_h4` binaries:
```
pkill -f 'warmchain6.sh'; pkill -f 'tools/locsearch6'
```
**Resume / extend a chain** from where it stopped: each rung's best-seen is saved. To continue
chain A that floored at n=k, warm-start the next attempt from the last win:
```
./tools/warmchain6.sh A <k> 37 <newseed> 4000000 11 6 data/r6/candidates/chain_A_n<k-1>.win.json
```
or hammer a single hard rung directly with more steps / different noise:
```
./tools/locsearch6 <k> <seed> 8000000 data/r6/candidates/chain_A_n<k>.init1.json 12 out.json 8
python3 tools/verify.py out.json   # referee
```
**Any 0-violation result MUST be confirmed by `verify.py` and saved under `data/r6/candidates/`.**

## 6. Successor playbook (value order)

1. **Read the floors.** `grep FLOOR data/r6/logs/chain_*.log` and `grep WIN ... | tail`. The
   max verified-balanced n across chains is the current N(6) lower bound. Record it in RESULTS.md
   with the verify.py command (a balanced K_n witness is a real W3-style result).
2. **Confirm the wall.** For the rung n = floor+1 where chains stall, run many more seeds
   (warm from the floor's win) — the r=5 discipline: a floor is only credible after multiple
   independent walkers pin the same residual. If several seeds all stall well above 0 at the
   same n, that is strong evidence N(6) = floor.
3. **If a chain reaches n=36:** that would show N(6) ≥ 36 despite no affine plane — a notable
   result. Immediately try n=37 (the conjecture's K_{r²+1}); a balanced K_37 would DISPROVE
   Erdős 617 at r=6. Save + verify + STOP for review (do not self-certify a disproof).
4. **Push warm starts harder** at the wall: restart-from-best diversity, lower endgame noise,
   larger GREEDYK, or seed from a *different* chain's floor colouring. Consider a SAT/CP attack
   on the single wall rung (as the r=5 campaign did with the h4 instances).
5. **Structure-mine** the highest balanced K_n found: colour-class independence numbers, class
   sizes, whether it resembles the Z_6² difference colourings or is fully non-algebraic — this
   informs whether a construction or an impossibility proof is the right next target.
