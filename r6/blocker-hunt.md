# r=6 5-blocker hunt (task #77): empirically refute the [MH″]-analogue

**STATUS (2026-07-13, PIVOTED — the two lanes are one problem):** object A = a BALANCED K_31 with
one class tightened to α≤5. Derivation (team-lead, accepted; r6-arith sanity-checking): balanced
at r=6 ⟺ α(G_c)≤6 for ALL c; object A adds α₀≤5 (⇒≤6) + cap-16 (which balance implies). So
**object A exists ⟹ balanced K_31 exists ⟹ N(6) ≥ 31**, and the r=6 mirror of the r=5 h4-witnesses
(balanced + hitter). CONSEQUENCE: Phase-2 at n=31 CANNOT succeed unless a balanced K_31 exists —
and the balance ladder's verified floor is only 28 (n=29 grinding). That is exactly why Phase-2
pinned at 41k: it was demanding balanced-K_31-plus at a height plain balance hasn't reached.

**PIVOT:** killed the Phase-2 attempts; all workers now on the BALANCE frontier (multi-seed wall
attack n=29→30→31, chains G/H/P/Q/R, r=5 h4 discipline). If balanced K_31 verifies, IT is the
Phase-2 seed (warm-start, drive one class's α 6→5 — the h4 methodology, proven at r=5). If the
balance ladder WALLS below 31 with r=5-grade evidence (multi-seed, long-pin, deficiency signature),
the hunt's answer FLIPS: object A impossible at 31 for want of balanced K_31 ⇒ [MH″]-analogue
likely TRUE — document like RESULTS R6. Either outcome is a real result.

Objects A confirmed at n=25, 26, 27 (each is a balanced K_n with a tightened class). Two-phase
Phase-1 result stands and is reusable: checkG-verified K_6-free α≤5 cap-16 class-0 graphs exist in
[98,120] (m=115) — the class-0 *component* is settled, but a component is not a completion.

## The target and what it refutes

`r6/feasibility.md` argues the r=5 extension-obstruction chain BREAKS at r=6 at the
[MH″]-analogue: the fill inequality `e(H)+5·e(F) ≥ C(31,2)=465` fails by ≥17 edges, so the
step forcing `|T_c|=6` cannot be established — meaning a **5-blocker** on S=31 vertices is *not
excluded by the counting*, and "very likely exists". This hunt tries to **exhibit** one.

**Object A** — a 6-colouring of K_31 (team-lead spec, task #77) with:
1. **cap-16**: every 7-set spans ≤16 edges of any single class (subsumes K₇-freeness);
2. **α(G_0) ≤ 5**: class 0 has no independent 6-set (every 6-set has a colour-0 edge);
3. **α(G_c) ≤ 6**, c=1..5: no independent 7-set (every 7-set has a colour-c edge).

No balance is imposed. If A exists at n=31, the weak-hypothesis [MH″]-analogue is **FALSE** — the
fill argument is chasing a false statement, and no fill-style repair can save the chain at r=6.

**Refutation scope discipline (do not overclaim).** `tools/checkA.py` reports, for every hit, three
independent things so we state exactly what each object kills:
- **A-profile** (V_cap, V_missed, V_alpha0 all 0) → refutes the **weak-hypothesis** [MH″]-analogue.
- **V_omega = 0** (every class K₆-free, ω≤5) → also refutes the **full** feasibility.md statement,
  whose invariant list includes ω(G_c) ≤ 5. (An A-object may have a mono-K₆ and thus *not* be
  ω-clean; the n=26 witness below is such a case.)
- **V_balance = 0** (every 7-set sees all 6 colours) → also a **B-object**, refuting the
  balanced-hypothesis version; `tools/verify.py` is the referee for balance.
Note conditions 2+3 alone force balance (α bounds ⇒ every 7-set sees every colour), so every A-object
is automatically balanced — confirmed empirically. The genuinely stronger property is ω≤5.

## Tools (in `tools/`)

- **`locsearch6a.c` → `locsearch6a`** — local search for object A. Two subset families:
  7-subsets (cap-16 + α(G_c)≤6) and 6-subsets (α(G_0)≤5). Incremental scoring mirrors locsearch6;
  the 6-family is only touched when a recolour involves colour 0. Adaptive greedy (full greedy +
  low noise once <2000 violations). `MAXSTEPS=0` prints the component breakdown for cross-checks.
  Build: `cc -O3 -o tools/locsearch6a tools/locsearch6a.c`.
- **`checkA.py`** — INDEPENDENT brute-force checker (pure Python, no shared code with the C
  scorer). Re-verifies conditions 1-3 and reports ω and balance. The referee for object A.
- **`warmchainA.sh`** — self-chaining hunt: solve rung n → checkA-confirm → extend a vertex → climb.
  `warmchainA.sh TAG START END SEED MAXSTEPS NOISE GREEDYK INIT`; 3 attempts/rung.

## Validation evidence (2026-07-13)

- **Scorer init vs independent checker:** on random colourings, locsearch6a's breakdown ==
  checkA's, exactly: n=14 (cap 0 / missed 234 / alpha0 123), n=22 (0 / 15132 / 3318).
- **Seed = object A:** AG(2,5)-unmerged K_25 (class-by-direction, 6 colours) is confirmed object A
  by checkA (V_cap=V_missed=V_alpha0=0), *and* ω-clean, *and* balanced. `objA_ag_n25.json`.
  (This already shows the A-family exists low, mirroring the r=5 h4-witnesses at n=17..24.)
- **Incremental machinery end-to-end:** extend AG-K25 to n=26 (360 alpha0 violations from the new
  random vertex) → locsearch6a drives to 0 in 2 steps → checkA confirms OBJECT A at n=26. A wrong
  delta would stall or emit a false 0 the checker rejects; neither happened. (This n=26 witness has
  V_omega=1 — one mono-K₆ — so it refutes the weak + balanced versions but not the ω-version.)

## Fleet

3 hunt chains HA/HB/HC (seeds 100/200/300; noise 12/14/10, greedyk 6/5/8) warm-chaining
`objA_ag_n25.json` → n=34, 3 attempts/rung, MAXSTEPS 3M. Logs `data/r6/logs/hunt_{HA,HB,HC}.log`;
per-n witnesses saved `data/r6/candidates/objA_n<k>.json`. Footprint: 3 here + G,H on the N(6)
ladder = 5 total (the cap). Kill: `pkill -f 'warmchainA.sh'; pkill -f 'tools/locsearch6a'`.

## Outcomes

- **Object A confirmed at n = 25 (AG seed), 26, 27** (checkA-verified). The one-vertex warm-chain
  then stalls: n=28+ needs class 0 *over-dense* (α≤5 wants ≥65 class-0 edges on 28 vtx vs a
  balanced ~63), so single-edge moves thrash on the alpha0↔missed tension. (Duplication extends
  AG-K25 cleanly only to n=26 — two point-duplications force an independent 7-set in some class.)

### Two-phase attack at n=31 (team-lead plan; class 0 provably NOT a clique union — cap-16 bans K_7)

- **Phase 1 does NOT wall.** `tools/graph_a5cap` (standalone binary search for a single graph with
  α≤5 + cap-16, then greedy-sparsify + LNS minimisation) finds valid class-0 graphs on 31
  vertices. **`data/r6/candidates/class0_n31_m118.json`: 118 edges, INDEPENDENTLY checkG-confirmed**
  (0 independent-6-sets, 0 over-cap-7-sets). This is the good scenario — object A is *plausible*,
  matching feasibility.md's Δ=−17 prediction, NOT the "Phase-1 walls ⇒ lemma holds structurally"
  scenario. (118 edges leaves 347 for classes 1..5 ≈ 69 each; the tight target is ≤115 ⇒ ≥70 each,
  the minimizer keeps running toward it.)
  - The clique start (5 cliques 7,6,6,6,6, m=81) is a TRAP: it has 1 cap violation (the K_7) but
    removing any clique edge instantly makes an independent 6-set; a valid graph is genuinely
    non-clique, found from random-dense init + edge minimisation.
- **ω≤5 CORRECTION (r6-arith, 2026-07-13).** r6-arith PROVED a K_6 in class 0 makes completion
  impossible (cap ⇒ deg≤1 into each other clique ⇒ α≤4 on the other 25 ⇒ 66+5·54=336>300). Every
  candidate above (m104/m118, and the BASE5K6 family = 5 K_6's) CONTAINS a K_6 → unfillable. So
  Phase 1's objective is now **α≤5 + ω≤5 (K_6-free) + cap-16, minimise edges, window [98,120]**.
  `graph_a5cap` 6-family now also flags full 6-sets (K_6); `checkG.py` reports K_6 count. Result:
  K_6-free valid graphs DO exist in-window — checkG-verified at m=127, minimised to **m=115**
  (`class0_n31_k6free_best.json`). ω raised the floor 104→~115 but stayed ≤120, so NOT the
  "escalate" signal. **Escalation rule (r6-arith):** if serious effort can't get a K_6-free
  α≤5 cap-16 graph under ~120 edges, escalate (lemma-might-be-TRUE) — currently satisfied (115).
  **Joint objective is mandatory** (r6-arith eb64f44): optimising only α+ω (WalkSAT) drifts to
  150–186 edges with 100% cap-16 failures; graph_a5cap scores all THREE {α≤5, ω≤5, cap-16}
  simultaneously with edge minimisation, which is why m=115 satisfies all three (checkG-confirmed).
  **Consistency note:** the completability window width (120−98 = 22) ≈ the fill deficit (17) +
  small slack — r6-arith's DP and the fill analysis agree, and the K_6-free (ω≤5) requirement was
  the hidden constraint that stalled every earlier Phase-2 attempt.
  **STOP-AND-AUDIT:** object A as defined does NOT forbid ordinary-class (1..5) K_6s. So if a
  zero-violation completion has an ordinary K_6 AND r6-arith rules ordinary K_6-exclusion *proven*,
  that is a bug, not a result — audit, do not claim. (Ruling pending; until then don't enforce
  ω on classes 1..5, but check it on any completion.)
- **Phase 2 is the HEADLINE GATE and is HARD.** `FREEZE0=1 ./tools/locsearch6a` fixes class 0 and
  searches only colours 1..5 (α(G_c)≤6 + cap-16). On the m=115 graph it PINNED at ~41k residual
  missed-colour violations (1.6% of C(31,7)); 3 parallel attempts on diverse class-0 graphs
  (m=115/118/127, strong params) launched to test "some complements 5-colour, some don't".
  - **ω(F_i)≤5 is AUTOMATIC here, no objective term needed:** FREEZE0 never touches class 0, so
    class 0 stays α₀≤5 ⇒ every 6-set has a class-0 edge ⇒ no 6-set is mono in colours 1..5 ⇒
    ω(G_c)≤5 for c=1..5 at every step (r6-arith's own proof, applied to the frozen class 0);
    ω(G_0)≤5 since class 0 is K_6-free. `checkA` reports K_6 count on all 6 classes = the audit;
    if it ever fires, class 0 wasn't really α≤5 (a bug). Still: **check ω on all 6 classes of any
    zero-violation completion before claiming object A.**
  - **Feasibility is tight per-7-set:** cap-16 on class 0 ⇒ every 7-set has ≥5 between-edges;
    a cap-TIGHT 7-set (16 class-0 edges) has exactly 5 between-edges that must be a RAINBOW (all
    5 colours) to see every colour. Sparse class 0 (m≈115) has few cap-tight 7-sets, so the 41k
    pin is likely NOT that obstruction — it looks more like search-weakness / a bad basin from the
    naive between-start, or the complement being genuinely un-5-colourable for that graph.
  - Levers: diverse class-0 pool; a structured between-start (not the random spread); lowest-e
    class-0 for max slack; a stronger solver for the 5-colouring CSP; or r6-arith structural
    insight on which valid class-0 complements 5-colour. May not fall by local search alone.
- If a Phase-2 hit reaches 0: checkA (independent) + tools/verify.py, state precisely which
  statement it refutes (weak / ω-clean / balanced), save, commit, escalate.

## Tools added for the two-phase attack
- `tools/graph_a5cap.c` (Phase-1 single-graph search; RANDP init, MINROUNDS/KICK LNS minimiser),
  `tools/checkG.py` (independent Phase-1 checker), `tools/embed_class0.py` (graph → FREEZE0 seed),
  `tools/gen_scaffold.py` (5-clique class-0 seed, n≤30), `FREEZE0` mode in `tools/locsearch6a.c`.
