# r=6 chain arithmetic reconnaissance (Erdős–Gyárfás at K₃₇)

**STATUS: the r=5 extension-obstruction chain BREAKS at r=6.** The break is at the
[MH″]-analogue: its fill inequality `e(H) + 5·e(F) ≥ C(31,2)=465` fails by **≥17
edges** (best case 448 vs 465). At r=5 the same inequality closes *exactly*
(`58 + 4·38 = 210 = C(21,2)`, Δ=0, razor's edge). The r=6 constraints (cap-16,
own-cap 10, α≤5/ω≤5) are all looser relative to the graph sizes, so the
cap-recursion boost that precisely saves r=5 falls short at r=6.

This is arithmetic reconnaissance only — no proofs, no Lean. Every number below
comes from an executed script (commands in the last section). The DP machinery is
**calibrated**: fed the r=5 SAT base it reproduces the *proven* r=5 L-table
(24,31,38,46,53,62,73,84), `e(H)=P₄(21)=58`, and `P₄(20)=50` (matching [MM] §2's
`m≥50`) exactly — see `recompute2.py` `VALIDATION r=5: … PASS`.

---

## Two corrections to the task's stated premises (both re-derived from scratch)

1. **The r=6 cap is 16, not 15.** A balanced 6-colouring needs every 7-set to see
   all 6 colours. A 7-set has C(7,2)=21 edges; if one colour has k of them the
   other 5 colours share 21−k and each needs ≥1, so k ≤ 16. k=17 leaves only 4
   edges for 5 colours → one missing. **cap = C(r+1,2)−(r−1) = 21−5 = 16.** (The
   task's "≥16 leaves ≤5 for 5 colours, one missing" is off: 16 leaves exactly 5,
   which *can* cover 5 colours; the true forbidden threshold is 17.) The cap value
   is load-bearing but the verdict is robust to it: hypothetical cap-15 breaks by
   14, cap-16 by 17, cap-17 by 19 (`robustness.py`).

2. **S = 31 = 36−5, not 30 = 36−6.** The [MH″]-analogue rules out a *5-blocker*
   (a 5-set T, since we must exclude |T_c| ≤ r−1 = 5), so the vertex-deleted graph
   after removing the (r−1)=5-vertex hitter has S = r²−r+1 = **31** vertices. The
   task's "36−6=30" uses hitter = r = 6; the r=5 precedent uses hitter = r−1 = 4
   (S=21=25−4), so the hitter is (r−1)=5 and S=31. (Using 30 would only change the
   target to C(30,2)=435; the verdict is unchanged.)

---

## A. The chain skeleton at r=6 (which steps transfer as pure combinatorics)

Delete an apex vertex from K₃₇ → balanced 6-colouring of K₃₆ (36 vertices);
`T_c = {v : χ(apex,v)=c}` partition the 36 vertices. All pinned quantities
transfer by the same derivations as r=5:

| quantity | formula | r=5 | r=6 | transfers? |
|---|---|---|---|---|
| cap (max own-colour edges in an (r+1)-set) | C(r+1,2)−(r−1) | 11 | **16** | yes (re-derived) |
| own-edge cap (step-5, r-vertex blocker) | C(r,2)−(r−1) | 6 | **10** | yes |
| minority class edge bound | C(r²,2)/r | 60 | **105** | yes |
| S after (r−1)-hitter | r²−r+1 | 21 | **31** | yes |
| total to fill | C(S,2) | 210 | **465** | — |
| α(H), ω(H) (special colour) | ≤ r−1 | ≤4, ≤4 | ≤5, ≤5 | yes |
| α(F_i), ω(F_i) (ordinary) | α≤r, ω≤r−1 | ≤5, ≤4 | ≤6, ≤5 | yes |
| |T_c| forced value | Σ=r², each ≥r ⇒ =r | 5 | 6 | **only if [MH″] holds** |

Steps 1–3 (restriction preserves balance; α(G_c)≤r invariants; cap; minority ≤
average) are pure combinatorics and transfer verbatim. **Step 4 (`|T_c|=6` for
all c) is the first step that needs a real lemma — the [MH″]-analogue — and that
is exactly where the arithmetic breaks.**

### A.1 object A is exactly "balanced K₃₁ with class 0 tightened to α≤5" (verified)

The full **object A** (a 6-colouring of K₃₁ with α₀≤5, α_c≤6 for c=1..5, cap-16 on all
classes) is *identical* to **a balanced 6-colouring of K₃₁ whose class 0 is tightened to
α≤5**, and cap-16 is an implied consequence, not an extra hypothesis. Proof: "balanced" =
every 7-set sees all 6 colours = every 7-set has a c-edge for each c = no independent
7-set in any G_c = **α(G_c)≤6 for all c**. So (⟹) object A has α₀≤5≤6 and α_c≤6, hence
all α(G_c)≤6, hence balanced; and balance forces cap-16 (a 7-set with ≥17 of one colour
leaves ≤4 edges for the other 5 → a colour missing), so the cap hypothesis is redundant.
(⟸) balanced gives α_c≤6 and cap-16 for free; adding α₀≤5 completes object A's hypotheses.
**Verified numerically** (`equivalence_check.py`) on the hunt's real balanced K₂₈: over
all C(28,7)=1.18M 7-sets, "balanced" ⟺ "α(G_c)≤6 ∀c" (both hold), and cap-16 holds with
the bound *tight* (max single-colour count in a 7-set = exactly 16). The same algebra
gives the r=5 mirror: R7's reduced object (profile (4,5,5,5,5), cap-11, K₆-free on K₂₁) =
"balanced 5-colouring of K₂₁ with one class at α≤4" — matching how the h4-witnesses were
hunted (balanced + hitter objective).

**Gating consequence: object A ⟹ N(6) ≥ 31.** Object A *is* a balanced 6-colouring of K₃₁
(forgetting the α₀≤5 tightening), so building it at n=31 requires a balanced 6-colouring
of K₃₁ to exist first — i.e. the balance ladder must reach 31. With the verified balance
floor at n=28 (n=29 grinding), Phase-2-at-31 is gated on the ladder, which explains its
high-violation pinning: it is trying to tighten a balanced K₃₁ that has not yet been
built. Correct order: extend the balance ladder to 31, then tighten class 0 to α≤5.

## B. The [MH″]-analogue recursion at r=6

The r=5 [MH″] reduces to: no 5-colouring of K₂₁ with class independence numbers
(4,5,5,5,5), all cap-11 and K₆-free, and proves it by **filling K₂₁**:
`e(H)≥58` (cap-recursion) + `e(F_i)≥38` (Brouwer) with `58+4·38 = 210 = C(21,2)`
exactly, then excludes the forced equality (§6–7).

The r=6 analogue reduces to: no 6-colouring of **K₃₁** with independence numbers
(5,6,6,6,6,6), all **cap-16** and **K₇-free**. Two structural differences:

- **Brouwer is applied to a single colour class' complement** J_i = ̄F_i, which is
  K₇-free (r_Turán = **6**) with α(J_i)=ω(F_i)≤5, not 6-partite (6·5=30<31), on
  **S=31** vertices (task said "K₇-free, r_Turán=6, on 30=36−6" — the r_Turán=6 and
  K₇-free are right; the size is 31=36−5, see correction #2). Brouwer gives
  `e(F_i) ≥ C(31,2) − [t₆(31) − ⌊31/6⌋ + 1] = 465 − 396 = 69` (before any
  equality-exclusion; r=5's analogue was 37→38, so r=6 is ≈69→70).

- **The cap-recursion gains an extra level.** H has α≤5 (vs α≤4 at r=5), so the
  ladder is P₂→P₃→P₄→**P₅** (four levels) instead of P₂→P₃→P₄ (three). Here
  `P_a(q)` = min edges of a q-vertex graph with α≤a, ω≤r−1, cap. The r=5 "L-table"
  is P₃; the r=6 recursion runs one level deeper.

**r=6 P-ladder at S=31** (rigorous DP lower bounds; `recompute2.py`, `ladder.py`):

```
P_3 (α≤3): …  27:155  28:168  29:184  30:199  31:217
P_4 (α≤4): …  27:100  28:109  29:119  30:129  31:139
P_5 (α≤5): …  27:65   28:72   29:81   30:89   31:98      ← e(H) endpoint
```

**Endpoint: `e(H) ≥ 98`** (analogue of r=5's `e(H) ≥ 58`).

**Base M₆(s) = min edges for α≤2, ω≤5, cap-16** (SAT, `sat_base.py`):
`M₆(9)=16, M₆(10)=20, M₆(11)=29`. Note 9,10 show **no boost** over the
complement-Turán floor (16,20) — because ω≤5 permits the two-clique extremal
K₅∪K₅ that ω≤4 forbade at r=5 (where M(9)=19>16). The boost first appears at s=11
(+4). **Recursion nonexistence threshold: q=17** (no α≤2/ω≤5/cap-16 graph on 17
vertices), vs q=12 at r=5 — the constraints bite ~5 vertices later.

**Robustness of `e(H)≥98`:** it is *insensitive* to the unknown M₆(12..16) — driven
to 98 by the nonexistence threshold and the u(d) neighbourhood caps, not the middle
base values (`sensitivity.py`: e(H)=98 whether M₆(12..16) are the DP floors
36,46,56,68,80 or aggressively boosted to 45,60,78,98,118). The r=5 calibration —
DP-with-SAT-base is *tight* (=58=truth) — indicates 98 is close to the true minimum,
not a loose bound. And if the nonexistence threshold q=17 is wrong (graphs do exist),
e(H) only *drops* → the break only worsens (`robustness.py`).

## C. The [MM]-analogue (moot — downstream of the broken [MH″] — but rebuilt)

[MM]-analogue at r=6: no G on 36 vertices with α(G)≤6, cap-16, e(G)≤105, plus a
6-set T with α(G−T)≤5, e(G[T])≤10. Peeling disjoint K₆'s from H=G−T (30 vertices,
α≤5):

- **Five cases** for the max number of disjoint K₆'s: **{0,1,2,3,5}** (r=5 had four:
  {0,1,2,4}). The new case is k=3 (leaves 12 vertices with α≤2). k=4 collapses to 5.
- K₆-free case (k=0): `e(H) ≥ P₅(30) = 89`, so the budget leaves
  `e(T,H)+e(G[T]) ≤ 105−89 = 16` for the T-incidences — **more slack than r=5's
  60−50 = 10**.

So even *in isolation* the [MM]-analogue is shakier at r=6 (more budget slack + an
extra case to close), but it is moot: the chain never reaches it because step 4
([MH″]) fails first.

## D. Finite-fact inventory an r=6 proof would need, with SAT-size estimates

| fact (r=6) | r=5 counterpart | r=6 SAT cost signal |
|---|---|---|
| M₆(9)=16, M₆(10)=20, M₆(11)=29 (α≤2,ω≤5,cap-16 minima) | M(9)=19,M(10)=25 "easy" | **done here** (seconds–minutes) |
| M₆(12..16) minima | — | **M₆(12) did not finish in 15 min** — already harder than the entire r=5 base |
| nonexistence M₆(17)=none (α≤2,ω≤5,cap-16) | nonex11/nonex12 (340/455 MB LRAT) | C(17,7)=**19 448** cap constraints (vs C(11,6)=462), atmost-16-of-21 each → est. **10–100× the r=5 LRAT**, likely 3–30 GB; certification probably infeasible |
| L₆(s) (α≤3), N₆(s) (α≤4) direct SAT to validate P₃/P₄ | L(13..16) SAT-checked | strictly harder than M₆ (larger α, same cap blow-up) — likely infeasible past small s |
| [MM] pivotal "no α≤2 cap-16 graph on 17 vtcs, any ω" | "no α≤2 cap-11 graph on 11 vtcs" (the load-bearing ω-free fact) | same instance as M₆(17) nonexistence — the r=6 analogue of the single most expensive r=5 fact, ~40× the cap constraints |

The r=6 cap encoding scales with C(s,7) seven-sets (vs C(s,6) six-sets at r=5) and
a wider atmost (16-of-21 vs 11-of-15). Every base/nonexistence fact is
**substantially heavier** than its r=5 counterpart, and several look **infeasible**
to certify. This compounds the arithmetic break: even if one wanted to push the r=6
chain, the finite-fact base is a second, independent obstacle.

## E. Verdict — per-inequality slack, r=5 vs r=6

| chain inequality | r=5 | r=6 | classification |
|---|---|---|---|
| cap value (own colour in (r+1)-set) | 11 | 16 | TRANSFERS (re-derived) |
| own-edge cap (step-5 tightness) | 6 | 10 | TRANSFERS |
| minority edge bound | 60 | 105 | TRANSFERS |
| class invariants α≤r, ω≤r−1 | ✓ | ✓ | TRANSFERS |
| **[MH″] fill: e(H)+(r−1)e(F) vs C(S,2)** | **58+4·38 = 210 = C(21,2), Δ=0** | **98+5·70 = 448 < 465, Δ=−17** | **BREAKS** |
| step-5 own-edge tightness usable? | yes (needs |T_c|=r) | vacuous (|T_c|=6 not forced) | BREAKS (via [MH″]) |
| [MM] four/five-case counting | closes, budget slack 10 | moot; slack 16 + extra case | shakier (moot) |

**Full slack table** (`mm_and_slack.py`, `recompute2.py`):

```
 r   S  cap ownc minor  e(H)  e(F)  fill(+1F)  C(S,2)  MAIN Δ
 5  21   11    6    60    58    37       210     210        0   ← closes (proven)
 6  31   16   10   105    98    69       448     465      −17   ← BREAKS
```

**Plain-deficit trend** (Brouwer/Turán only, before any cap boost; `trend.py`):
the deficit the cap-recursion must cover grows far faster than the boost supplies:

```
 r:            3    4    5    6    7
 Δ_plain:      0   −5  −17  −39  −74
```

At r=3 the fill closes with **no cap needed** (Δ_plain=0 — consistent with r=3
being elementary). r=5 is the knife-edge where the full machinery *exactly* cancels
−17: cap-boost on H of +13 (45→58) plus F-exclusions +4 (37→38, ×4) = +17. At r=6
the plain deficit is −39 but the machinery delivers only +17 on H (81→98) plus +5
on the five F's (69→70 each) = **+22 total, leaving −17**. The knife-edge is a
knife-edge: r=6 falls off it.

### Classification: **BREAKS**, at the [MH″]-analogue, by ≥17 edges.

The fill inequality that forces `|T_c|=6` cannot be established: the minimum-edge
special colour H and the five minimum-edge ordinary colours do **not** fill K₃₁ —
they leave ≥17 edges of slack. Hence a 5-blocker is not excluded, step 4 fails, and
the chain collapses before [MM]. Because the r=5 bounds are tight (calibrated), the
17-edge deficit is real, not an artifact of loose estimation: it says balanced-type
6-colourings of K₃₁ with a 5-blocker are *not* obstructed by this counting, and are
very likely to exist (a construction search — the local-search task — would confirm).

### The three most important numbers

1. **Δ_MAIN(r=6) = −17** (fill 448 vs C(31,2)=465), against **Δ_MAIN(r=5) = 0**.
2. **e(H) ≥ 98** (robust; would need ≥115 to close) vs the proven r=5 `e(H)=58`.
3. **Plain deficit −39 (r=6) vs −17 (r=5)**, while the cap-boost that *exactly*
   covers 17 at r=5 supplies only ≈ +21 at r=6.

---

## F. Construction addendum (task #77 follow-up: explicit extremal class-0)

> **DECISIVE FINDING (`verify_candidates.py`): every class-0 candidate the hunt has
> produced contains a K₆ — so none can be completed, which is exactly why Phase 2
> grinds.** Checked `class0_n31_m104` (K₆ on {1,4,5,18,20,24}), `class0_n31_m118`,
> `g31min_s2` (102 edges, same K₆), `g31min_s7` (119 edges, K₆ {2,3,6,12,13,19}),
> `base5k6_s1/s3` (K₆ {0..5} *and* α=6). All are α≤5 but **not K₆-free**. The
> §5-analogue below proves any completable class-0 is K₆-free (margin 36), so
> Phase 2 on these is doomed regardless of how long it runs. **Fix: add the ω≤5
> (K₆-free) constraint to the class-0 search.** The good news: their edge counts
> (102–119) are already inside the completability window, so a K₆-free re-optimisation
> should land a completable class-0.


The hunt lane asked whether the `e(H)≥98` bound comes with explicit extremal
structure, and for a near-extremal class-0 graph (31 vtcs, α≤5, cap-16). Answers:

**Is the DP bound-only? Yes.** `e(H)≥98` is a *degree-sequence* lower bound
(the necessary condition Σ Φ₅(d_v)≤0), not a construction — it exhibits no graph.
But it does pin structure of any near-minimum solution (below).

**Two rigorous facts that reframe the hunt (neither uses the DP):**

1. **Completability window: e(class-0) ∈ [98, 120].** Each of the 5 ordinary
   classes needs `e(F_i) ≥ 69` (Brouwer). Since the six classes partition
   `E(K₃₁)=465`, a *completable* class-0 must satisfy `e(class-0) ≤ 465 − 5·69 =
   **120**`. Completion slack `= 120 − e(class-0)`, split among the 5 ordinary
   classes. **This explains why Phase 2 grinds at 118 edges: slack = 2 — the
   complement's 5 classes average 69.4 each against a hard floor of 69, essentially
   rigid.** Minimising class-0 toward 98 raises the slack to as much as 22
   (complement classes ≈73 each). Sweet spot: get class-0 as low as achievable.
   (`completability.py`.)

2. **Class-0 MUST be K₆-free — so the 5×K₆ sketch is invalid.** The §5-analogue:
   if class-0 contains a K₆ = Q, then on X = 31−6 = 25 vertices every x has
   `deg₀(x,Q)≤1` (cap-16), forcing `α(class-0[X])≤4`; then `e(class-0[X]) ≥ 66`
   (plain Turán, *no DP*) and each `e(F_i[X]) ≥ 54` (Brouwer, K₅-free), so
   `66 + 5·54 = 336 > C(25,2) = 300` — contradiction, **margin 36**. Hence no
   completable class-0 has a K₆. The team lead's `5×K₆` (ω=6) cannot be completed;
   this is very likely the real obstruction behind the Phase 2 grind (independently
   of edge count). **Recommendation: class-0 must be K₆-free (ω≤5).** Both G and
   its complement are then K₆-free — a Ramsey (6,6)-type graph on 31 vertices.
   Concrete witness (`test_sketch.py`): `5×K₆ + apex` (80 edges) is **doubly
   broken** — ω=6 (five disjoint K₆'s) *and* α=6 (independent set {1,7,13,19,25,30}
   = one un-hit vertex per block + apex). And the two repairs conflict: breaking a
   K₆ into a K₆-free graph on 6 vertices *raises* its independence (α≥2), making the
   α≤5 problem worse. The clique-block family is a structural dead end.

3. **ALL SIX classes are K₆-free in any valid completion — PROVEN, hard contradiction
   (not a margin), including the ordinary classes (α budget 6).** If an ordinary class
   F_i (i∈{1..5}) contained a K₆ on a 6-set Q, then all 15 pairs inside Q have colour i,
   so *none* has colour 0 — i.e. **Q is an independent 6-set in class-0**, forcing
   α(class-0) ≥ 6, contradicting α(class-0) ≤ 5 *by definition*. This is a one-line
   logical contradiction, stronger than §5's counting argument for class-0's own K₆ (and
   it does *not* use the ordinary class's own α≤6 — it is driven entirely by
   α(class-0)≤5). Consequences for the Phase-2 objective: **(a)** adding ω≤5 to *all six*
   classes is sound pruning — it removes only provably-dead configurations (the exact
   basin that stalled Phase-2); **(b)** a reported Phase-2 "zero" carrying a K₆ in *any*
   class is impossible for a genuinely valid completion, so it signals a **bug** in a
   checker or a colouring whose class-0 independence number is actually 6, not ≤5.
   (Ordinary classes are also K₇-free via cap-16, so ω(F_i) ≤ 5 throughout — the same
   fact used for the Brouwer bound e(F_i) ≥ 69.)

**Structure theorem the DP implies about near-minimum class-0 (`degree_profile.py`):**
Φ₅(d) is minimised near d=13–15, but the min-edge degree *multiset* (m=98) is
**{deg 5:×10, deg 6:×1, deg 7:×20}** — average 6.32, i.e. an **irregular,
sparse, ~6–7-regular graph, NOT a union of cliques**. Corroboration: a
disjoint-clique cover is impossible (5 cliques of size ≤5 cover ≤25 < 31), and
**no circulant C₃₁(S) achieves α≤5,ω≤5 below degree 10 (155 edges), and even those
all fail cap-16** (`circulant.py`) — so the extremal class-0 is genuinely
non-vertex-transitive and irregular. Greedy edge-removal from K₃₁ stalls at 172.

**Caveat on the achievable minimum.** `e(class-0) ≥ 98` is a *lower* bound and,
unlike r=5 (where the DP-with-SAT-base was tight), the r=6 base is only partly
SAT-pinned, so the true minimum may sit above 98. Evidence brackets it in
**[98, 120]**: DP floor 98; the team lead's construction gives ≤118; circulants
need ≥155 (not near-extremal). Do not assume 98 is reachable — target the lowest
completable value you can verify, anywhere in [98, 118].

**Explicit candidates — spec for the hunt.** Producing a *minimal* explicit graph
is Python-bottlenecked (verifying cap-16 = scanning C(31,7)=2.6M 7-sets, ~30s per
check — fine once, infeasible inside a search loop), so the min-construction is
squarely the C-hunt's job (task #77). The precise spec I derived for it:

> **class-0 target:** 31 vertices, **α≤5, ω≤5 (K₆-free), cap-16**, edge count in
> **[98, 120]** — *as low as verifiably achievable* (each edge below 120 buys one
> unit of completion slack). Degree profile ~6–7-regular (DP witness
> {5:×10,6:×1,7:×20}); irregular, non-vertex-transitive, not a clique union.

**Two refinements from probing the hunt's m104 (`repair.py`, `walk.py`):**
- **m104 already satisfies cap-16** — so K₆-free is the *only* missing constraint
  on the hunt's best candidate.
- But its K₆ is **α-load-bearing**: every local edge-repair that kills the K₆
  breaks α≤5 (removing a clique edge opens an independent 6-set that can only be
  re-closed by an edge that re-creates a K₆). So a K₆-free class-0 cannot be
  patched from m104 — it must be searched from scratch, and the K₆-free minimum
  likely sits *above* 104 (still inside [98,120]).
- **The three constraints α≤5 ∧ ω≤5 ∧ cap-16 at e≤120 are a tight joint sweet
  spot.** A WalkSAT that optimises only α≤5 ∧ ω≤5 (leaving cap-16 to a final
  check) drifts to 150–186 edges, *all* cap-failing. **cap-16 must be inside the
  search objective, not a post-hoc filter.** This is why a Python search can't hit
  it and the C hunt should optimise all three jointly (plus a low-edge pressure).

Background CEGAR (`r6/cegar3.py`, upfront-α + lazy ω/cap) did not converge at
E≤120 within its window (the first SAT solve alone is very slow at this tight
boundary). Net: the explicit min K₆-free class-0 is a job for the C tooling with
the spec above; the analysis here tells it exactly what to look for and why every
current candidate fails.

## G. The decision: ω-constrained floor vs the 120 ceiling (task #77 theory side)

**The single number: the ω-constrained floor is `m* ≥ 98`, and `98 ≤ 120`, so the
class-0 *component* is NOT proven impossible — the counting window `[98, 120]` survives.
This closes the impossibility route and keeps the fill-style proof dead, but does NOT by
itself refute the [MH″]-analogue: object A = the full 6-colouring remains uncompleted
(the window is necessary, not sufficient — see the epistemic-status note below).**
(`omega_floor.py`, `decision.py`.)

The question. **Terminology (canonical, per r6/blocker-hunt.md): "object A" = the FULL
6-colouring of K₃₁** (class-0 with α≤5 + five ordinary classes with α≤6, cap-16
throughout). This section studies its *class-0 component*: a graph on 31 vertices with
α≤5, ω≤5 (K₆-free, required by §F), cap-16. Let `m*` = the component's minimum edge
count. Completability needs `m* ≤ 120` (§F, a *necessary* counting condition). So:
`m* > 120` ⟹ no valid class-0 component ⟹ object A impossible ⟹ **[MH″] TRUE at r=6**
(the campaign's biggest possible finding); `m* ≤ 120` ⟹ the window survives and the
fill-style proof stays dead — but object A itself still requires a Phase-2 completion.
Since `e(H)≥98` was the input to the fill argument, this *is* the same question as "is
the fill deficit real?".

**The floor already includes ω≤5.** The DP's `u(d)=min(b(d), ex(d,K₅))` (neighbourhoods
are K₅-free) and its clique base encode ω≤5; recomputing with the clique bound removed
gives 87, so ω≤5 contributes **+11** (87→98). So 98 is a genuine ω-constrained floor.

**Why 98 is trustworthy — and why the impossibility routes are not — is settled by
calibrating against the PROVEN r=5 case**, where the analogous `m*(21) = 58` exactly
(DP-tight, achieved in the accepted proof; there `m* = ceiling = 58`, the razor's edge).
Any lower-bound method must return ≤58 at r=5:

| method | r=5 output | valid? | r=6 output | usable? |
|---|---|---|---|---|
| **cap-recursion DP (mine)** | **58 = truth** | ✅ tight | **98** | yes → floor |
| asymptotic Ramsey–Turán `RT(n,K₆,o(n))=2n²/7` | predicts m*≈**100** | ❌ (truth 58) | 190 | **no** — fails calibration |
| Caro–Wei `α≥n/(d̄+1)` | α≥3.2 (allows 4 ✓) | ✅ but weak | α≥4.2 (allows 5) | no impossibility |
| Shearer (triangle-free) | n/a (graph has triangles) | — | — | inapplicable |

The asymptotic Ramsey–Turán bound — the natural "impossibility" candidate — **under-
predicts the dense complement M\* by 42 at r=5** (says 110, truth 152), so it would
wrongly force `m*(r=5)≈100 > 58`. It cannot be trusted to force `m*(r=6) > 120`. The r=5
special class is a concrete witness that a K₅-free graph with α≤4 exists at average
degree 5.52 on 21 vertices, so no K₆-free/Shearer independence bound can force α≥6 at the
analogous r=6 density (avg degree 6.3 on 31) without contradicting it.

**The only calibrated method (the DP) gives 98 < 120.** The +22 gap to the ceiling is
exactly the fill deficit; the DP is robust (insensitive to the unknown middle base, §B)
and tight at r=5, so `m* ≈ 98–110`, below 120. The window survives.

**CONSTRUCTIVE CONFIRMATION (2026-07-13): window confirmed BOTH directions.** The hunt
produced `data/r6/candidates/class0_n31_k6free_best.json` (m=115), and my *fully
independent* exhaustive checker (`independent_verify.py`: itertools enumeration for α/ω,
numpy for cap-16 — deliberately not reusing the bitset clique code) confirms it:
symmetric, 115 edges, **α≤5 clean, ω≤5 (K₆-free) clean, cap-16 clean (max 7-set edges =
16, 0 violations)**. So `m* ≤ 115`, and combined with the DP floor:

> **m\* ∈ [98, 115] ⊂ [·, 120]: a valid CLASS-0 COMPONENT exists (independently verified
> witness at 115 ≤ 120), so the impossibility route is closed and the fill-style proof of
> the r=6 [MH″]-analogue stays dead — BREAK, now constructive, not just calibrated.**
>
> **Epistemic status of the lemma itself: NOT YET REFUTED.** Object A (the full
> 6-colouring) has not been constructed; the counting window being open is necessary,
> not sufficient, for completion. The [MH″]-analogue is refuted if and only if Phase 2
> produces a full colouring passing the independent checker (all six classes). Until
> then the honest statement is: "unprovable by the r=5 fill method (Δ=−17), impossibility
> disproved at the component level, completion open."

This also settles the SAT probe (α≤5∧ω≤5∧e≤120 is SAT by this witness), which was
therefore killed. The earlier honest caveat ("98 is only a lower bound") is discharged:
the 115-edge witness supplies the missing upper anchor.

```
# corrected, validated recomputation (authoritative); reproduces r=5 L-table + e(H)=58
python3 r6/recompute2.py

# SAT base (α≤2, ω≤5, cap-16): M6(9)=16, M6(10)=20, M6(11)=29; M6(12) did not finish
.venv/bin/python r6/sat_base.py M 9 13          # (timed out after M6(11); 15-min retry on 12,13 also timed out)

# cross-r plain-deficit trend  0,−5,−17,−39,−74
python3 r6/trend.py

# e(H) insensitivity to the unknown M6(12..16) base
python3 r6/sensitivity.py

# [MM]-analogue peeling (5 cases {0,1,2,3,5}) + full slack table
python3 r6/mm_and_slack.py

# robustness: nonexistence-threshold and cap-value (15/16/17) sensitivity
python3 r6/robustness.py

# full P-ladder at both r
python3 r6/ladder.py
```

Superseded: `r6/recompute.py` (first pass; had an INF/nonexistence-handling bug in
the DP, fixed in `recompute2.py`; kept for the debugging record).
