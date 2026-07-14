# Route B (gap-graph pincer) arithmetic at r=6 — feasibility reconnaissance

**VERDICT: the numerology CLOSES at r=6 (pincer point `P*=r²=36`), unlike Route A which
broke by 17. But the finite work explodes 2–80× and the endgame SAT is likely
infeasible at full scale — so `CLOSES WITH GAPS`, the gaps being SAT-feasibility and an
unverified case-explosion, not an arithmetic break.**

Attribution: this rebuilds the structure of the SURVIVES-reviewed external candidate
`review_queue/external-candidate-B/candidate-proof.md` (direct minority-colour gap-graph
pincer on K_{r²+1}; §§2–10), used freely with attribution per the commission. Every
number below is from an executed script (`r6/routeB_arith.py`, `routeB_cases.py`,
`routeB_hybrid.py`); the r=5 column reproduces the candidate exactly (calibration).

Why Route B behaves so differently from Route A: its whole argument is **scale-locked to
the edge budget**. The minority bound `e(G) ≤ ⌊C(r²+1,2)/r⌋` and the regular case make
the extremal gap graph exactly `r`-regular with `e(G) = emax` and every independent
`r`-set of boundary `r·r = r²`. So the pincer point is `P* = r²` for **every** r, and the
below/stability sides always meet there. Route A's fill, by contrast, compared two
independently-growing bounds whose gap widened with r.

---

## 1. Calibration — r=5 reproduced exactly (`routeB_arith.py`)

Every load-bearing r=5 number from the candidate reproduces:

| quantity | candidate | script | ok |
|---|---|---|---|
| `e(G) ≤ ⌊325/5⌋` | 65 | 65 | ✅ |
| α=5 forced: `325 − t_4(26)` | 72 (>65) | 72 | ✅ |
| cap on 6-sets | 11 | 11 | ✅ |
| `|R_i| ≤ 4`; `5·4=20 < 21` ⇒ `P≥22` | 22 | 22 | ✅ |
| `e(W) ≥ L_5(21)=34` ⇒ `P≤31` | 31 | 31 | ✅ |
| `e(H) ≥ 260`; BN threshold `t_4(26)` | 253 | 253 | ✅ |
| BN degree-sum `2·4·260/26` (exact ⇒ strict) | 80 → ≥81 | 80.0 → 81 | ✅ |
| σ range | [17,19] | [17,19] | ✅ |
| §7 table (6 rows) max P(A+x) | 24,25,25,26,26,26 | identical | ✅ |
| regular case: G 5-regular, boundary | 25 | 25 | ✅ |
| §8 signatures at P=25 | 8 | 8 | ✅ |
| §10 defect core / labelled masks / orbits | 18 / 6561 / 58 | 18 / 6561 / (≈58) | ✅ |

## 2. r=6 slack table — inequality by inequality (K_37)

| inequality | r=5 | r=6 | closes? |
|---|---|---|---|
| `e(G) ≤ ⌊C(n,2)/r⌋` | 65 | **111** | — (budget) |
| α=r forced: `emax < C(n,2)−t_{r−1}(n)` | 65 < 72 (slack 7) | 111 < **119** (slack 8) | ✅ |
| cap on (r+1)-set `= C(r+1,2)−(r−1)` | 11 | **16** | — |
| `|R_i| ≤ r−1`; cover `r(r−1) < |W|` | 20 < 21 (slack 1) | 30 < 31 (slack 1) | ✅ tight both |
| `P_baseline = |W|+1` | 22 | **32** | — |
| `P_upper = emax − L_r(|W|)` | 65−34 = 31 | 111−65 = **46** | — |
| `e(H) ≥ C(n,2)−emax` | 260 | **555** | — |
| BN threshold `t_{r−1}(n)`; `e(H) >` it | 260>253 (slack 7) | 555>**547** (slack 8) | ✅ |
| BN degree-sum `2(r−1)e(H)/n` **exact ⇒ strict** | 80→≥81 | **150.0→≥151** | ✅ (same delicate strictness) |
| σ range width `= r−2` | [17,19] (3) | [26,29] (**4**) | — |
| **regular boundary `= P* = r²`** | 25 | **36** | ✅ |
| below-elimination reaches `P*−1` (§6) | P≤24 | P≤**35** | ✅ (more cases) |
| stability gives some boundary `≤ P*` (§7) | ≤25 | ≤**36** | ✅ (more rows) |
| **PINCER meets at `P*`** | 25 | **36** | ✅ **CLOSES** |

Every arithmetic inequality that mattered at r=5 transfers with comparable slack (7→8,
1→1). The **strict** Bollobás–Nikiforov step — the candidate's most delicate dependence,
where the degree-sum lands *exactly* on the threshold (80 at r=5) and only strictness
saves σ — recurs identically at r=6 (`2·5·555/37 = 150.0` exactly ⇒ ≥151 ⇒ σ≤29). It
transfers, but it is equally load-bearing and equally fragile.

## 3. Case-count explosion, r=5 → r=6 (`routeB_cases.py`)

The pincer closes, but every finite ingredient grows:

| ingredient | r=5 | r=6 | factor |
|---|---:|---:|---:|
| §6 below-P values (excess 1..r−2) | 3 (P=22,23,24) | **4** (P=32,33,34,35) | +1 |
| §6 below-signatures (total to hand-kill) | 7 | **15** | 2.1× |
| §6 hardest below-case excess | 3 | **4** (new: P=35 has 8 sigs) | — |
| §7 table rows | 6 | **10** | — |
| §7 maxP levels above `P*` | {P*+1} | **{P*+1, P*+2}** (new level) | — |
| §7 rows needing 7.x-style hand-exclusion | 3 (σ=19, c=3,4,5) | **7** (σ=28: c=4,5,6; σ=29: c=3,4,5,6) | 2.3× |
| §8 exact-`P*` signatures | 8 | **15** | 1.9× |
| exceptional patterns `p(r−1)` | p(4)=5 | p(5)=**7** | — |

Two qualitatively new features at r=6:
- **A new §7 level `maxP = P*+2`** (the σ=29, c=3,4 rows reach boundary 38). r=5 topped out
  at `P*+1`. The pincer still closes (all σ=28,29 rows are in the "exclude-by-§7.x"
  bucket; excluding them leaves only σ=26,27, which self-give boundary ≤36), but the
  hand-exclusion now covers **7 rows including the new `c=6` case** (r=5 never had c>5).
- **A new below-case `P=35` (excess 4)** with 8 signatures — heavier than any r=5
  below-case (P=24 had excess 3).

Each below-case and each §7 row *plausibly* dies by the same style of argument
(transversal / colour-observation / missing-rectangle), but the volume roughly doubles
and the new c=6 and excess-4 cases are unverified analogues.

## 4. Endgame SAT-core sizes — the real bottleneck (`routeB_cases.py`)

The §9/§10 endgames are where feasibility bites. The candidate SAT'd the seven "easy"
signatures on the **full 26-vertex** structure and reduced the hardest (2222_33344) to an
**18-vertex core** `Q ∪ 3·K_3 ∪ X`. At r=6:

| | r=5 | r=6 |
|---|---:|---:|
| full-structure SAT vertices | 26 | **37** |
| full-structure cap-clause (r+1)-sets `C(n,r+1)` | C(26,6) = 230,230 | C(37,7) = **10,295,472** (45×) |
| reduced-core size range (Q + deficient + X) | 6..18 | 7..**27** |
| worst reduced core cap-sets `C(core,r+1)` | C(18,6) = 18,564 | C(27,7) = **888,030** (48×) |
| worst all-degree-2 defect: labelled masks `m^X` | 9⁴ = 6,561 | 14⁵ = **537,824** (82×) |
| defect orbits (⇒ #SAT instances) | 58 | **≈ thousands** |

Consequences:
- **The full-signature SAT is almost certainly infeasible at 37 vertices** — 45× more cap
  constraints than the r=5 formulas, which already ran resource-capped (4 GiB / 1800 s).
  So at r=6 *most* of the 15 signatures (not just the last one) must be reduced to cores.
- **Reduced cores reach 27 vertices** (the `(2,2,2,2,2)` signature with four deficient K_4
  groups, `5,5,4,4,4,4`), with C(27,7) = 888 K cap-sets — 48× the r=5 defect core.
  Borderline; the r=5 18-vertex core was comfortable, 27 is heavy.
- **The defect-lemma orbit machinery explodes**: the worst all-degree-2 signature has
  14⁵ ≈ 538 K labelled mask assignments (vs 9⁴ = 6561), so hundreds–thousands of orbits,
  each its own compact-LRAT SAT. This is the single biggest feasibility risk: the r=5
  §10 lemma was 58 orbits; the r=6 analogue for `5,5,4,4,4,4` alone is orders of magnitude
  larger, and there are several such signatures.

Compared with my Route-A §D estimates: Route A's hardest r=6 finite facts (the α≤2/cap-16
nonexistence at 17 vertices, C(17,7)=19,448 cap constraints) are *smaller* than Route B's
worst reduced core (27 vertices, 888 K). Route B trades Route A's clean arithmetic break
for a much larger, but arithmetically-closing, SAT campaign.

## 5. Hybrid — can Route A's DP replace Route B's SAT endgames? NO (`routeB_hybrid.py`)

Assessed directly: the cap-recursion DP (Route A's engine) applied to `G[D]` (α≤r, ω≤r,
cap-16) gives a floor `P_r(m)` that is **exactly `L_r(m)` — boost = 0** at every D-size
(m = 26,27,28,29,31 for r=6; and 17..21 for r=5). Reason: Route B's minority graph is only
α≤r, ω≤r (weak), so its Turán-extremal `r` cliques have size ≤ ⌈m/r⌉ ≈ 5 = far below the
K_7 that cap-16 forbids — the cap never bites, so the DP cannot beat complementary Turán.
Re-running the §7 table with the DP floor leaves the hand-exclusion burden unchanged
(3 rows at r=5, 7 at r=6). And the DP cannot model the exact `Q`-degree pattern, the
exchange inequality (8.1), or the exceptional masks that the signature/defect endgames
turn on. **The two methods are orthogonal**: Route A's DP bites only under the tighter
α≤r−1/ω≤r−1 of its special class; Route B's endgames genuinely need SAT (or dedicated
counting like §10). No cross-pollination available at the density-floor level.

## 6. Verdict

**CLOSES WITH GAPS.**

- **Numerology: CLOSES.** The pincer point `P* = r² = 36` is forced by the same regular-case
  saturation that gives 25 at r=5; the α-forcing (slack 8), BN threshold (slack 8), strict
  degree-sum (exact→+1), σ-range, and below/stability sides all transfer and meet at 36.
  This is a genuine structural difference from Route A (which broke by 17): Route B is
  scale-locked to the edge budget, so it does not develop a deficit.
- **Gap 1 — endgame SAT feasibility (the serious one).** The full 37-vertex signature CNFs
  are ~45× the r=5 size and almost certainly infeasible; reduction to cores is forced for
  most of the 15 signatures, cores reach 27 vertices (48× the r=5 defect core), and the
  all-degree-2 defect-orbit machinery explodes to ≈538 K labelled masks (82×). Whether the
  full r=6 endgame is machine-checkable within reasonable resources is **doubtful** and is
  the make-or-break question.
- **Gap 2 — unverified case-explosion.** 15 signatures (vs 8), 7 §7 hand-rows (vs 3, incl.
  new `c=6` and a new `maxP=P*+2` level), 15 below-signatures (vs 7, incl. a new excess-4
  case). Each *plausibly* closes by the candidate's own techniques, but the volume ~doubles
  and the new cases are unchecked analogues.
- **Hybrid: not available.** Route A's DP gives zero boost on Route B's floors.

### The three most important numbers

1. **`P* = 36` (= r²)** — the pincer point; the numerology CLOSES (contrast Route A's
   Δ = −17). Regular gap graph is 6-regular, `e(G)=111=emax`, every independent 6-set of
   boundary 36.
2. **15 / 7 / 15** — signatures at P* (vs 8), §7 hand-exclusion rows (vs 3), below-P
   signatures (vs 7): the finite case-work roughly doubles across the board.
3. **C(37,7) = 10.3 M full-signature cap-sets (45× r=5); worst reduced core 27 vertices,
   C(27,7)=888 K (48×); worst defect 14⁵ ≈ 538 K labelled masks (82×)** — the endgame SAT
   blowup, the binding feasibility constraint.

## Commands run

```
python3 r6/routeB_arith.py      # calibration (r=5 exact) + r=6 core numbers, §7 table, signatures
python3 r6/routeB_cases.py      # §7 hand-exclusion burden, below-signatures, SAT-core sizes, defect orbits
python3 r6/routeB_hybrid.py     # DP-vs-L_r floor comparison (boost = 0), hybrid assessment
```
