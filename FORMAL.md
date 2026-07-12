# Lean formalization of the r=5 resolution — status ledger

Goal: a Lean 4 + Mathlib proof of `Erdos617.Main` (= upstream formal-conjectures
`erdos_617` at r=5), replacing every informal link of R9's chain with checked code.
Project: `lean617/` (Lean 4.30, Mathlib via cache). Status board below is the
single source of truth; update it with every merged milestone.

## Decomposition and status

| id | item | difficulty | status |
|----|------|-----------|--------|
| F0 | project builds; `Statements.lean` compiles with sorries | setup | DONE (2026-07-10) |
| F1 | statement fidelity: `Main` ⟺ upstream erdos_617 (r=5); `main_iff_no_balanced` | easy | DONE (2026-07-10) |
| F2 | chain deduction (`chain_deduction`): the 6-step argument of extension-chain.md | medium | DONE (2026-07-10), sorry-free |
| F3 | SAT-primitive bridge: verified-LRAT route for the four primitives (nonex11, nonex12, M9≥19, M10≥25). Investigate `Std.Tactic.BVDecide`'s LRAT checker / `Std.Sat.CNF` for direct use; drat-trim → LRAT conversion of data/sat/prim_*.drat; then the encoding-correctness lemmas (graph on Fin 11 exists ⟺ CNF satisfiable) | medium-hard, R&D | DONE (2026-07-10): `primFacts : PrimFacts` in `Primitives.lean`; carries `ofReduceBool` (native_decide) |
| F4 | counting identity (4.1)/(4.2) + neighbourhood bound (4.3) in Lean | medium | DONE (2026-07-10), sorry-free |
| F5 | L-table recursion (Φ/Ψ arithmetic; from F3+F4; finite checks may use `decide` on small arithmetic) | medium | DONE (2026-07-10), sorry-free, CONDITIONAL on `PrimFacts` (F3) |
| F6 | Brouwer/Kang–Pikhurko theorem (n ≥ 2r+1, K_{r+1}-free, non-r-partite ⇒ e ≤ t_r(n) − ⌊n/r⌋ + 1) + the equality classification for (r,n) ∈ {(5,21),(5,16),(5,15)} | HARD (research formalization; Mathlib has Turán via `SimpleGraph.isTuranMaximal`, nothing beyond) | **INTERFACE DONE (2026-07-10)**, sorry-free CONDITIONAL on `BrouwerFacts`; F7 unblocked. **DISCHARGE 2026-07-11: foundations sorry-free on main (`BrouwerDischarge.lean`: `turan_step`, `symmG_edgeCount_eq`); the full induction SKELETON `kp_upper` + `brouwerFacts : BrouwerFacts` compiles (scratch `BrouwerInduction.lean`) — reduced to exactly THREE named sorries: `caseA_slack` (arithmetic, NUMERICALLY VERIFIED true), `kp_caseB` (Lemma 3 + good/bad split, HARD), `equality21` (F6h). See "F6 DISCHARGE PROGRESS" below.** **F6i: `caseA_slack` discharged (sorry-free). F6j/F6k: BOTH Case-B arithmetic backbones discharged sorry-free (`two_bad_aux`, `constr_le`); `kp_caseB` reduced to a PURELY graph-theoretic core (partition transport + good/bad dichotomy + Lemma-3 K_{r+1}-counting) — see the F6j/F6k DECOMPOSITION ROADMAP below. 2 sorries remain (`kp_caseB`, `equality21`).** **F6t/F6u/F6v (2026-07-11, runner 13): `BrouwerInduction.lean` now has exactly 3 sorries (`kp_lemma3` STEPs 1–5,7; the `some-part≤1` guard; `equality21`). Sorry-free & axiom-clean this session: `gnr_colorable_small` (n≤r+2 emptiness), Case-B WIRED to `kp_caseB_impl` (old opaque `kp_caseB` deleted), and — the keystone — ALL of `kp_lemma3`'s STEP 6 inequality (5): `fiber_card_le`, `prod_le_sum_bad`, `missing_edges_ge` (counting) + `transversal_has_bad_pair` (graph→hbad bridge). See F6t/F6u/F6v notes.** **F6aa (2026-07-12): singleton guard CLOSED sorry-free (Route MI) ⇒ `kp_saving` PROVEN & axiom-clean. F6ab (2026-07-12): `saving` field discharged; the last F6 sorry (`equality21` = `exists_AB21_iso`) RETIRED and replaced by the hypothesis-only `KPEqualityClassification` (its exact statement). `brouwerFacts_of (h : KPEqualityClassification) : BrouwerFacts` assembles the full structure from PROVEN `kp_saving` + the one hypothesis, via the verified `equality21_final ∘ equality21_transport`. NET: F6 is now sorry-free, conditional on exactly `KPEqualityClassification` (a published classical result); Brouwer's bound itself is proven. See "EQUALITY CORE — F6ab" below.** |
| F7 | [MH″] assembly (§§3–7 of mh2 candidate, incl. the repaired steps) | hard, long | **DONE — sorry-free (2026-07-10, lean617/Lean617/MH2Proof.lean; full `lake build` clean)**, CONDITIONAL on (pf : PrimFacts)(bf : BrouwerFacts). `lemma_MH2_of` + `MH2Ctx.endgame` axiom-clean (propext/Classical/Quot only; NO sorryAx/native_decide — `#print axioms` confirmed). Complete: §1 `lemma_MH2_of`, §3 `edgeCount_Fi_ge_38`, §4.3 `edgeCount_ge_58`, §5 `H_cliqueFree5`, §6 `MH2Ctx.false_of`, §7.1 `delta_ge_5`/`count16_false`, **§7 endgame `MH2Ctx.endgame` (F7e)**. Shares `turan3_general`/`Lfloor`(≈F8 `ell`)/`alphaAtMost_comap_gen` — F8 dedupes at its merge; F7e's `edgeCountIn_insert_eq'` is primed to avoid clashing with `MMProof.edgeCountIn_insert_eq` (identical stmt; F9 may dedup). |
| F8 | [MM] assembly (peeling lemma + 4 cases incl. the adopted r=7 repair) | hard, long | **DONE — sorry-free (2026-07-10, `lean617/Lean617/MMProof.lean`, full `lake build` clean).** `lemma_MM_of (pf : PrimFacts) : MM` axiom-clean (`#print axioms` = propext/Classical.choice/Quot.sound; NO sorryAx, NO native_decide). CONDITIONAL on `(pf : PrimFacts)` only (NO `BrouwerFacts`). All four cases of the {0,1,2,4}-K₅ split closed: §2 (F8c), §3 (F8d), §5 incl. `all_hit` ρ-counting (F8g), §4 `section4_one` (F8h). Full-chain audit `chain_deduction (lemma_MH2_of primFacts bf) (lemma_MM_of primFacts)` = propext/Classical/Quot + SAT native_decide axioms, NO sorryAx (BrouwerFacts stays a hypothesis). |
| F9 | final: `erdos_617_r5` sorry-free; CI check (`lake build` clean) | — | DONE (2026-07-11); **UPDATED F6ab (2026-07-12): `erdos_617_r5 (h : KPEqualityClassification) : Main`** (was `(bf : BrouwerFacts)`) + upstream-shaped corollary, both conditional on the single hypothesis `KPEqualityClassification`. ZERO sorryAx project-wide; axioms = 3 standard + 4 named SAT-reflection (primFacts) — **unchanged by F6ab** (`kp_saving` axiom-clean; `kpG` native_decide does NOT enter — hypothesis route). Full build clean (8495 jobs); `tools/axiom_audit.sh` PASS; `leanchecker` per-module exit 0. Aggregator `Lean617.lean` now bundles BrouwerInduction/BrouwerMax/GuardScaffold/KPConstruction/Equality21 (all sorry-free). |

## KP-EQUALITY CORE — the single remaining research object (entry point for the next leg)

> **EQUALITY CORE — F6ab (2026-07-12, relay runner 16): hypothesis NARROWED, `saving` PROVEN.**
> With `kp_saving` closed sorry-free & axiom-clean (F6aa), F6ab retired the last `sorry` and made the
> final theorem conditional on exactly ONE classical result:
> - **New Prop (`Lean617/Equality21.lean`):** `def KPEqualityClassification : Prop := <the exact
>   former `exists_AB21_iso` statement>` — every extremal colour class `F` (α≤5, K₅-free, e=37) is
>   `≅` some `H` with `AB21 H`. This is the (5,21) Kang–Pikhurko equality classification.
> - **`exists_AB21_iso` (the sorry) DELETED**; `equality21_final` refactored to take
>   `(h : KPEqualityClassification)` and derive `AB21 F` via the VERIFIED `equality21_transport`.
> - **`brouwerFacts_of (h : KPEqualityClassification) : BrouwerFacts`** assembles the interface from
>   PROVEN `kp_saving` (`saving`) + `equality21_final h` (`equality21`). The old sorried
>   `brouwerFacts` (BrouwerInduction.lean) is RETIRED (nothing consumed it).
> - **`Final.lean`:** `erdos_617_r5 (h : KPEqualityClassification) : Main` and `_upstream` likewise;
>   `lemma_MH2 (h) := lemma_MH2_of primFacts (brouwerFacts_of h)`.
> - **Aggregator** now bundles BrouwerInduction/BrouwerMax/GuardScaffold/KPConstruction/Equality21;
>   FULL `lake build` clean (8495 jobs), ZERO sorry anywhere; `axiom_audit.sh` PASS; `leanchecker`
>   per-module exit 0.
> - **Axiom profile UNCHANGED** = 3 standard + 4 SAT native_decide. The `kpG` construction's
>   native_decide facts do NOT enter the final theorems: the `equality21` field is discharged via the
>   HYPOTHESIS route (`equality21_final ∘ equality21_transport`), which never touches `kpG`. (The
>   verified numeric witness `AB21_kpG_compl` is still built, for the record and the D1–D4 campaign,
>   but is off the final theorem's dependency path.)
> - **What remains (optional D1–D4 campaign):** PROVE `KPEqualityClassification` (using `kpG` +
>   `native_decide` over the 2 iso classes) to make `erdos_617_r5` unconditional. Everything below in
>   this section is the roadmap/scratch for that; the "two sorries" framing is now HISTORICAL (only
>   the `KPEqualityClassification` hypothesis is open, and it is no longer a Lean `sorry`).
>
> **UPDATE (2026-07-12, F6aa): the guard is now CLOSED sorry-free** via Route MI
> (`guard_somepart_closure` in `BrouwerInduction.lean`); `kp_caseB_impl`/`kp_upper`/`kp_saving` are
> axiom-clean, `guard_singleton_closure_OPEN` retired. **`equality21` (Sorry 2) is the SOLE remaining
> sorry.** See **"SINGLETON GUARD — CLOSED sorry-free (2026-07-12, F6aa)"** below for the lemma list.
>
> **CORRECTION (2026-07-12, guard-analysis runner — the analysis this section was gated on).**
> This section's central claim — that the singleton guard and `equality21` are "ONE object" both
> needing the extremal classification, with the guard requiring max-size — is REFUTED for the guard.
> The `some-part ≤ 1` guard closes from **max-DEGREE alone** via `main_ineq` + `c ≥ 3`, needing NO
> max-size, NO `guard_singleton_closure_OPEN`, NO `GuardScaffold.lean`, NO `z`-witness, and NO link
> to `equality21`. See **"SINGLETON GUARD — analysis (2026-07-12)"** below for the full pinned
> argument (Route MI: two verified-true arithmetic lemmas + ~150 lines wiring). So the guard is NOT a
> research object — `equality21` (Sorry 2) is the SOLE remaining research object. Sorry 1
> (`guard_singleton_closure_OPEN`) and its whole max-size scaffold can be RETIRED; the guard is
> dischargeable in `kp_caseB_impl` directly. The rest of this section (equality21) stands.

**READ THIS FIRST if you are picking up the F6 discharge.** After runner 14 (lean-f6g),
`kp_lemma3` is FULLY sorry-free (the campaign's summit) and BOTH remaining gaps have been
reduced to clean, isolated, honestly-stated sorries with all their verified machinery banked.
The two sorries are — mathematically — **ONE object: the equality/extremal classification of
the Kang–Pikhurko Theorem 4 bound.** This section consolidates them. The detailed historical
notes ("SINGLETON REDUCTION", "equality21 — TRANSPORT REDUCTION DONE") remain below as the
record; this is the orientation.

The whole `t_r`-form upper-bound apparatus (`caseA_slack`, `two_bad_aux`, `lemma3_arith`,
`kp_lemma3`) deliberately AVOIDS the construction side — it never needs to know what an
extremal graph looks like, only that the arithmetic slack covers `kpSaving`. Both remaining
sorries are exactly the questions that apparatus cannot answer: **"what does a graph that is
maximum / extremal for the KP bound actually look like?"** KP Theorem 4's proof answers this
(the extremal graphs are the constructions `G(n₁,…,n_r)` with Lemma 5's optimal sequence); the
next leg is to formalise THAT answer, once the guard-analysis agent's KP re-read + numerics pin
down its exact shape. **This is gated on that analysis — no Lean budget until it reports.**

### The two sorries, exact statements (the guard-analysis agent's precise input)

**Sorry 1 — `guard_singleton_closure_OPEN`** (`Lean617/GuardScaffold.lean`). The last open step
of `kp_caseB_impl`'s `some-part ≤ 1` guard, singleton sub-case, for a MAX-SIZE counterexample:

```lean
theorem guard_singleton_closure_OPEN {n r : ℕ} (hr : 2 ≤ r) (G : SimpleGraph (Fin n))
    (x : Fin n) (hn : r + 3 ≤ n) (hCF : G.CliqueFree (r + 1)) (hchi : ¬ G.Colorable r)
    (hmax : ∀ y, G.degree y ≤ G.degree x)
    (hmaxE : ∀ G' : SimpleGraph (Fin n), G'.CliqueFree (r + 1) → ¬ G'.Colorable r →
      edgeCountIn G' Finset.univ ≤ edgeCountIn G Finset.univ)
    (κ : Fin n → Fin (r - 1))
    (hproper : ∀ u ∈ G.neighborFinset x, ∀ v ∈ G.neighborFinset x, G.Adj u v → κ u ≠ κ v)
    (i0 : Fin (r - 1)) (w : Fin n)
    (hsingleton : (G.neighborFinset x).filter (fun v => κ v = i0) = {w})
    (hc2 : 2 ≤ n - (G.neighborFinset x).card) :
    ∃ (z : Fin n) (κ' : Fin n → Fin r),
      ∀ u v, u ≠ z → v ≠ z → G.Adj u v → κ' u ≠ κ' v := sorry
```

The conclusion is EXACTLY `kp_lemma3`'s hypothesis (`∃ z, χ(G−z) ≤ r`); `kp_lemma3` then closes
the guard's bound. So the guard reduces to: **produce the deletion witness `z`.**

**Sorry 2 — `exists_AB21_iso`** (`Lean617/Equality21.lean`). The `(5,21)` equality classification,
reduced (transport verified) to: every extremal colour-class `F` is isomorphic to a construction
bearing the A/B structure:

```lean
def AB21 (H : SimpleGraph (Fin 21)) : Prop :=
  ∃ A B : Finset (Fin 21), Disjoint A B ∧ A.card = 5 ∧ B.card = 4 ∧
    (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ H.Adj x y ∧
      (∀ u ∈ A, ∀ w ∈ A, u ≠ w →
        (¬ H.Adj u w ↔ (u = x ∧ w = y) ∨ (u = y ∧ w = x)))) ∧
    (∀ u ∈ B, ∀ w ∈ B, u ≠ w → H.Adj u w) ∧
    edgeCountIn H (A ∪ B) = 19

theorem exists_AB21_iso (F : SimpleGraph (Fin 21)) (hα : alphaAtMost F 5)
    (hK5 : F.CliqueFree 5) (he : edgeCountIn F Finset.univ = 37) :
    ∃ (H : SimpleGraph (Fin 21)) (σ : Fin 21 ≃ Fin 21),
      (∀ a b, F.Adj a b ↔ H.Adj (σ a) (σ b)) ∧ AB21 H := sorry
```

### Why they are the SAME object

KP Theorem 4's proof delivers two things at once: the bound `e ≤ t_r(n) − ⌊n/r⌋ + 1` AND the
classification of the graphs attaining it (the extremal graphs are precisely the constructions
`G(n₁,…,n_r)` with Lemma 5's optimal sequence). The remaining sorries are that classification,
read at two levels of the SAME induction:

- **`exists_AB21_iso` IS the classification at the leaf `(5,21)`:** an extremal `J = Fᶜ`
  (`K₆`-free, `α ≤ 4`, `e = 173 = p₅(21)`) must be `≅ G((4,4,4,4,4))`.
- **`guard_singleton_closure_OPEN` is the classification used one level up, for the BOUND:** to
  close Case B for a *maximum* counterexample with a singleton colour class `{w}`, we must know
  its extremal structure forces a vertex `z` whose deletion drops `χ` to `r`. The singleton (with
  `w` adjacent to ALL of `C`, i.e. `W_C = ∅` — PROVED, see machinery below) is a fingerprint of
  near-extremal structure; `z` provably EXISTS (576/576 numerics) but naming it needs the same
  structural knowledge the equality analysis provides.

**[CORRECTED 2026-07-12 — see "EQUALITY21 — analysis": TWO iso classes, not three; |A*|=1 ≅ |A*|=3. The fusion conjecture below is MOOT (guard closes via Route MI). Historical text follows.]**
**The 3-variant finding is the bridge between them** (runner-14, verified computationally):
[**CORRECTED 2026-07-12 — it is a 2-element family, not 3; `|A*|=1 ≅ |A*|=3` by nauty `labelg`; see
"EQUALITY21 — analysis" below.** Also this "bridge to the guard" is MOOT: the guard closes independently
via Route MI, not via any equality trace.]
`G((4,4,4,4,4))` is NOT a single graph but a **3-element isomorphism-class family** —
`|A*| ∈ {1,2,3}`, with `deg x = 13 + |A*| ∈ {14,15,16}`. `kpG` (KPConstruction.lean) is only the
`|A*| = 2` member. This freedom is precisely the extremal slack the equality analysis must
characterise, and it is the same slack that makes the guard closure subtle (the two "obvious"
guard colourings are falsified because they ignore which variant `G` sits at).

**OPEN CONJECTURE that would fuse the two (for guard-analysis to confirm/refute):** the guard's
singleton configuration (`|D_{i0}| = 1`) is exactly the `|A*| = 1` extremal variant. If true, a
SINGLE equality trace through `kp_upper` closes both sorries — the guard's `z` is read off the
`|A*| = 1` construction, and `exists_AB21_iso`'s `|A*| = 1` case is the same graph. This is the
highest-value thing the analysis could establish.

### Verified machinery each sorry consumes (all sorry-free, banked, axiom-clean)

**For `guard_singleton_closure_OPEN`:**
- `singleton_adj_all_C` (GuardScaffold.lean) — `w` (singleton vertex) is `G`-adjacent to ALL of
  `C = V∖Γx`. So `W_C = ∅`. (This CORRECTS f6f's "≥2 misses" framing — maximality forces 0 misses.)
- `clique_hits_singleton` (GuardScaffold.lean) — a size-`(r−1)` `G`-clique in the `(r−1)`-partite
  `Γx` is a transversal, hence hits the singleton class `{w}`; the transversal engine behind the above.
- `max_size_saturated`, `exists_max_counterexample` (BrouwerMax.lean) — the max-size reduction:
  a non-edge `uv` of a maximum counterexample has an `(r−1)`-clique adjacent to both (avoiding `u,v`).
- `kp_lemma3` (BrouwerInduction.lean) — **the SINK.** Once `z` is produced, `kp_lemma3` closes
  `e(G) + kpSaving ≤ t_r(n)`. Fully sorry-free.
- Also available in-context: `colorable_of_C_indep`, `no_Kr_plus_edge`, `good_witness_adj`
  (BrouwerInduction.lean) — the `Kr+1`/`χ≤r` contradiction toolkit.
- ESTABLISHED but not enough on its own: `C` is NOT independent (else `κ` + a fresh colour on `C`
  is a proper `r`-colouring, contra `hchi`); and `χ(G−w) ≤ (r−2) + χ(G[C])` needs `G[C]` bipartite,
  which does NOT follow from `W_C = ∅`. The gap is genuinely the structural/criticality argument.

**For `exists_AB21_iso`:**
- `equality21_reduce` (Equality21.lean) — `e(F) = 37 ⇒ J = Fᶜ` is `K₆`-free, `α ≤ 4`, `e = 173`
  (extremal). VERIFIED.
- `edgeCountIn_iso`, `equality21_transport` (Equality21.lean) — the VARIANT-AGNOSTIC transport:
  any `H` with `AB21 H` and any iso `F ≅ H` gives `AB21 F`. VERIFIED sorry-free. This is why
  `exists_AB21_iso` needs only "F ≅ SOME construction with AB21", not a specific one.
- `AB21_kpG_compl : AB21 kpGᶜ` (Equality21.lean) — the `|A*| = 2` witness, from the
  native-decide-backed `kpG_compl_AB_structure`.
- KPConstruction.lean anchors (native_decide-backed, sorry-free): `kpG`, `kpG_edgeCount` (= 173),
  `kpG_cliqueFree` (`K₆`-free), `kpG_alpha` (`α ≤ 4`), `kpG_compl_AB_structure`.
- `equality21_final = equality21_transport ∘ exists_AB21_iso` (Equality21.lean) — assembled; IS
  the `brouwerFacts.equality21` field, wired at the finish line once the core lands.

### What the guard-analysis agent's findings need to pin down (per sorry)

**For the guard (`guard_singleton_closure_OPEN`):**
1. **KP re-read (possible upstream mis-decomposition):** does KP Theorem 4 actually route
   small/singleton parts through the `χ(G−z) = r` + Lemma 3 mechanism, or does it (a) handle them
   INSIDE Lemma 3, or (b) avoid singletons entirely by a different colouring choice / maximality
   invocation? If (a)/(b), the guard's `some-part ≤ 1` split is a Lean-structuring ARTIFACT, and
   the right move is the deferred `kp_upper` max-size restructure (thread `hmaxE`, reshape Case B),
   after which this sorry dissolves rather than being proved.
2. **Numeric verify/falsify the EXACT statement above** on small `(n,r)` where Case B genuinely
   arises. NB Case B does NOT arise for max-size `G` at `(6,3),(7,3),(7,4)` (guard numeric probe,
   `scratchpad/gc_bipartite_check.py`) — the agent must reach larger `n` or CONSTRUCT Case-B
   instances directly. A single counterexample kills the statement (⇒ the decomposition is wrong,
   route (1)); confirmation across a real range is the green light to formalise.
3. **The mechanism for `z`** if the statement holds: the two obvious colourings are falsified
   (min-degree non-neighbourhood is not independent; the "recolour `{w}∪M(w)`" fails). A working
   `z` is always a non-neighbour of a minimum-degree vertex (576/576) but by a non-obvious route —
   likely a criticality/saturation argument on the maximum structure. Literature check: "is a
   `K_{r+1}`-saturated non-`r`-colourable MAXIMUM graph `r`-colourable after one vertex deletion?"

**For `exists_AB21_iso`:**
1. **Confirm Lemma 5's optimal-sequence classification at `(5,21)`:** that `(4,4,4,4,4)` is the
   unique optimal sequence and every extremal `J` is a `G((4,4,4,4,4))` construction (this is the
   equality trace: each `dᵢ = nᵢ` for `i ≥ 3`, `m₁ = 1`, equality in inequality (5) forces all
   missing edges into one `G[M₁,Mᵢ]`, every `V∖Y` vertex has ≤ 1 `Y`-non-neighbour, …).
2. **Confirm the 3 variants are the complete list** and which actually occur as extremal `J`:
   `|A*| ∈ {1,2,3}` (`deg x ∈ {14,15,16}`) — verify no fourth iso-class, and whether all three are
   realised (if only some, `exists_AB21_iso` ranges over fewer `H`).
3. **The unifying conjecture** (see above): is `|A*| = 1` ⟺ the guard's singleton case? Confirming
   this collapses both sorries to one equality trace.

### The output the next leg produces (once un-gated)

- **Guard:** either (route 1) restructure `kp_upper` Case B to carry `hmaxE`/max-size and the
  singleton sorry dissolves; or (route 3) formalise the criticality argument INTO
  `guard_singleton_closure_OPEN`. Then wire the guard's remaining `sorry` in `kp_caseB_impl` and
  also close the `some-part = 0` (empty) sub-case via `two_bad` at `k+1 < r` blocks + `pr`
  monotonicity (the `t_{r−1}(n)` Turán shortcut is FALSIFIED — see the RUNNER-14 UPDATE note).
- **equality21:** define `kpG₁`, `kpG₃` (the `|A*| = 1,3` variants), prove `AB21 kpGᵢᶜ` by
  `native_decide` (two cheap witnesses, mirroring `kpG_compl_AB_structure`), then the equality
  trace `J ≅ kpGᵢ`. `equality21_transport` already handles the rest.
- **Finish line (from the original F6 brief, after BOTH land):** wire
  `brouwerFacts.equality21 := equality21_final` (BrouwerInduction imports Equality21, or move
  `brouwerFacts`), add BrouwerInduction to the aggregator, rewire `Final.lean` to DROP the `bf`
  hypothesis (`erdos_617_r5 : Main` unconditional), full `lake build`, `#print axioms
  erdos_617_r5` (the KPConstruction/Equality21 `native_decide` axioms join the profile — update
  `tools/axiom_allowlist.txt` + RELEASE.md/FORMAL.md), re-run `lake env leanchecker` per changed
  module, close RELEASE.md R1, commit "F6 COMPLETE: BrouwerFacts discharged".

## Design notes (F0, 2026-07-10)

Definitional choices in `Lean617/Statements.lean` (the anchor for F1/F2):
- Colourings are `c : Sym2 (Fin n) → Fin 5` (total, incl. diagonal); matches
  upstream `coloring : Sym2 V → Fin r`. Colour class `colourClass c k` is the
  `SimpleGraph` with `Adj u v := u ≠ v ∧ c s(u,v) = k`.
- Independence: own `IsIndep G S := ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v`
  over `Finset` (avoids `Set`/`Finset` coercion friction with Mathlib's
  `SimpleGraph.IsIndepSet`). "α(G−T) ≤ m" is phrased as
  `∀ S, IsIndep G S → Disjoint S T → S.card ≤ m`.
- Edge counting: ONE idiom, `edgeCountIn G S := (S.sym2.filter (· ∈ G.edgeSet)).card`
  (noncomputable; `open scoped Classical` for the filter). Total edges =
  `edgeCountIn G Finset.univ`. Verified helper `card_offdiag`:
  `(S.sym2.filter (¬ ·.IsDiag)).card = S.card.choose 2` gives the C(n,2) counts
  (15, 10, 300). Bridge `mem_colourClass_edgeSet` characterises class edges.
- `MH2` is the ∃-form (no 4-set kills all independent 5-sets of a class);
  `MM` is the ∀…→ False form. Both proved (F7/F8) or consumed (F2) as stated.
- F1 fidelity: `Main` is kept over `Fin 26` (F2 needs the concrete type for
  MH2/MM). `main_imp_upstream` proves `Main` ⇒ the upstream `erdos_617` shape
  for an *arbitrary* `V` with `card V = 5^2+1`, transporting a colouring along
  any `V ≃ Fin 26`. So the `Fin 26` phrasing loses no generality.
  `main_iff_no_balanced` ties `Main` to "no balanced colouring of K_26".
- F2 chain deduction (`chain_deduction : MH2 → MM → Main`) is sorry-free
  (`#print axioms`: only propext/Classical.choice/Quot.sound). Structure mirrors
  extension-chain.md steps 1–6. Named helper lemmas (all sorry-free):
  `mem_colourClass_edgeSet`, `card_offdiag`, `edgeCountIn_colourClass`,
  `sum_edgeCountIn_colourClass` (colour classes partition off-diagonal pairs);
  `indep_le_five` (α≤5), `cap_eleven` (6-set 11-edge cap), `all_eq_five`
  (5×five=25 forces all fives), `isIndep_of_edgeCountIn_zero`,
  `balanced_restrict` (K_26↾→K_25). Inside `chain_deduction`: `x = Fin.last 25`,
  `c'` = restriction along `Fin.castSucc`, `T k` = spoke-colour fibres, then
  `step2` (α(G_k−T_k)≤4), `step4ge`/`step4` (|T_k|=5 via MH2+monotonicity),
  minority `m` via `exists_min_image` (≤60 edges), `step5` (≤6 own edges), and
  `step6` instantiates MM. Only remaining sorries in the whole file are
  `lemma_MH2` (F7) and `lemma_MM` (F8).

## Design notes (F4, 2026-07-10)

`Lean617/Counting.lean` (sorry-free; `#print axioms` on all exports = only
propext/Classical.choice/Quot.sound). Everything is over `SimpleGraph (Fin q)`
with `open scoped Classical`; `variable {q} (G)`. Final lemma names:

**Elementary `edgeCountIn` facts (for F5/F7/F8):**
- `edgeCountIn_mono : S ⊆ S' → edgeCountIn G S ≤ edgeCountIn G S'`
- `edgeCountIn_le_choose_two : edgeCountIn G S ≤ S.card.choose 2`
- `edgeCountIn_eq_filter_edgeFinset` (count from the edge side; the workhorse)
- `edgeCountIn_univ_eq_card_edgeFinset : edgeCountIn G univ = G.edgeFinset.card`

**W_v and the double-count swap:**
- `complClosedNbhd G v := univ \ insert v (G.neighborFinset v)` — this is the
  paper's `W_v = V \ N[v]`; `mem_complClosedNbhd : x ∈ W_v ↔ x ≠ v ∧ ¬G.Adj v x`.
- `sum_edgeCountIn_swap G T : ∑ v, edgeCountIn G (T v) = ∑ e ∈ E, #{v | e ∈ (T v).sym2}`.
- support: `mem_sym2_complClosedNbhd_edge`, `mem_sym2_neighborFinset`,
  `per_edge_count` (incl.-excl.; NO edge hypothesis needed), `card_edgeFinset_filter_mem`
  (incidences = degree), `sum_endpointDeg_eq_sum_sq_degree` (handshake for `∑ deg²`).

**(4.1)/(4.2):**
- `sum_edgeCountIn_compl_nbhd_add_sq_deg` — **the identity F5 consumes**, in
  triangle-free form: `(∑ v, e(W_v)) + ∑ v, (deg v)² = q·e(G) + ∑ v, e(N v)`.
  Rearranged this is §4.2's `∑ (e(W_v) − e(N v)) = q·e(G) − ∑ deg²`.
- `three_mul_card_cliqueFinset_three : 3 * #(G.cliqueFinset 3) = ∑ v, e(N v)` — (4.2),
  the triangle count is Mathlib's `cliqueFinset 3`; proved by edge/triangle incidence
  double count (`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`).
- `sum_edgeCountIn_compl_nbhd` — (4.1) literal triangle form:
  `... = q·e(G) + 3·#(G.cliqueFinset 3)`, immediate from the two above.

  DEVIATION (documented): (4.1) is stated as an ADDITION, not with the informal's
  `q·e(G) − ∑ deg²`. Over ℕ that subtraction truncates and is FALSE for dense graphs
  (e.g. `K_q`: `∑ deg² > q·e(G)`), so the faithful ℕ statement moves `∑ deg²` to the
  LHS. Mathematically identical; F5 rearranges freely with omega/linarith.

**(4.3) cap-11 neighbourhood bound:**
- `nbhd_bound_cap11 (hcap : ∀ S, S.card = 6 → edgeCountIn G S ≤ 11) (hd : G.degree v = d)
  (hd5 : 5 ≤ d) : 10 * edgeCountIn G (N v) ≤ 3*d*(d-1)`.
  Floor-free multiplied form (informal `⌊3d(d-1)/10⌋`); consumers divide as needed.
  Support lemmas: `card_powersetCard_five_filter_pair` (a 5-subset containing a fixed
  pair: `C(|s|-2,3)`), `edgeCountIn_add_card_le_insert` (step 1: `e(A)+|A| ≤ e(insert v A)`),
  `sum_powersetCard_edgeCountIn` (step 2 double count: `∑_{A⊆N v,|A|=5} e(A) = e(N v)·C(d-2,3)`).
  Arithmetic core `60·C(d,5) = 3d(d-1)·C(d-2,3)` via `Nat.choose_mul` (trinomial revision)
  + `descFactorial` for `2·C(d,2)=d(d-1)`.

Collaboration: (4.2) drafted by codex gpt-5.6-sol (it found the
`bipartiteAbove/Below` route), then compile-repaired here (2 fixes: `smul_eq_mul`
cast, reversed `card_eq_three`). Everything else authored + compiled in this session.

## Design notes (F5, 2026-07-10)

`Lean617/LTable.lean` (sorry-free; `#print axioms` on `L13..L19`, `Mfloor_le_of_props`,
`edgeCountIn_comap`, `mantel_general`, `edgeCountIn_nbhd_le_ufloor` = only
propext/Classical.choice/Quot.sound — **no `ofReduceBool`**; all finite checks use
plain `decide`, never `native_decide`). Everything CONDITIONAL on `PrimFacts` (F3).

**PrimFacts (F3 must discharge these four VERBATIM — a `structure … : Prop`):**
- `nonex11 : ∀ G : SimpleGraph (Fin 11), capAtMost11 G → alphaAtMost G 2 → False`
- `nonex12 : ∀ G : SimpleGraph (Fin 12), capAtMost11 G → alphaAtMost G 2 → False`
- `M9  : ∀ G : SimpleGraph (Fin 9),  capAtMost11 G → alphaAtMost G 2 → G.CliqueFree 5 → 19 ≤ edgeCountIn G univ`
- `M10 : ∀ G : SimpleGraph (Fin 10), capAtMost11 G → alphaAtMost G 2 → G.CliqueFree 5 → 25 ≤ edgeCountIn G univ`
where `capAtMost11 G := ∀ S, S.card = 6 → edgeCountIn G S ≤ 11` and
`alphaAtMost G m := ∀ S, IsIndep G S → S.card ≤ m` (both new `def`s here, over
`SimpleGraph (Fin n)`; `capAtMost11` is defeq to MM's inline cap hypothesis).
NOTE (i)/(ii) are ω-free (per the adversarial review's strengthening); the L-table
proof only needs (i) (it deletes any `|W_v| ≥ 11` down to 11 vertices), but all four
are bundled since F7's §4.1 M-recursion consumes (ii) and the M9/M10 values.

**L-lemma shape F7/F8 consume (one lemma per s, cleanest given `Fin s` dependence):**
`L{s} (h : PrimFacts) (X : SimpleGraph (Fin s)) (hα3 : alphaAtMost X 3)
  (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : {L} ≤ edgeCountIn X Finset.univ`
for `(s,L) ∈ {(13,24),(14,31),(15,38),(16,46),(17,53),(18,62),(19,73)}`.

**M-floor family F7/F8 consume:** `Mfloor : ℕ → ℕ` (Mantel `C(m,2)−⌊m²/4⌋` for m≤8,
`19,25` for m=9,10, `0` for m≥11 — unused there) and
`Mfloor_le_of_props (h : PrimFacts) (Y : SimpleGraph (Fin t)) : alphaAtMost Y 2 →
  Y.CliqueFree 5 → capAtMost11 Y → t ≤ 10 → Mfloor t ≤ edgeCountIn Y univ`.

**Key infrastructure (reusable):**
- Transport along `f : Fin t ↪ Fin s` via `SimpleGraph.comap`: `edgeCountIn_comap`
  (`edgeCountIn (X.comap f) T = edgeCountIn X (T.image f)`), `isIndep_comap`,
  `cliqueFree_comap` (Mathlib `CliqueFree.comap` + `Embedding.comap.isContained`),
  `exists_embedding_image_eq` (`Finset.orderEmbOfFin` gives the range-`W` embedding).
- Mantel: NO ready Mantel in Mathlib. Route = `mantel_general` (complement is
  `CliqueFree 3`; Turán `isTuranMaximal_turanGraph` extremality bounds `e(Gᶜ) ≤
  e(turanGraph t 2)`) + per-`t` `decide` on `(turanGraph t 2).edgeFinset.card ≤ ⌊t²/4⌋`.
  Needed the complement edge identity `edgeCountIn G univ + edgeCountIn Gᶜ univ =
  C(t,2)` (own idiom, `card_filter_add_card_filter_not` on the off-diagonal base).
- Per-vertex: `Mfloor_le_edgeCountIn_complNbhd` (α-drop `alpha_W` + transport +
  `Mfloor_le_of_props`), `complNbhd_card_le_ten` (restrict to 11 + `nonex11`),
  `edgeCountIn_nbhd_le_ufloor` (`ufloor(4)=5` by a direct K₄-free/K₅ argument,
  `⌊3d(d−1)/10⌋` from F4's `nbhd_bound_cap11` for d≥5, `C(d,2)` for d≤3).
- Assembly (per s, concrete numerals so `omega` stays linear): F4 identity
  `sum_edgeCountIn_compl_nbhd_add_sq_deg` + handshake + the summed per-degree affine
  bound `affineBound_{s}` (checked by `interval_cases d <;> decide` over the feasible
  range `d ∈ [s−11, s−1]`, i.e. `|W_v| ≤ 10` — never uses `Mfloor(11)`). The informal
  DP is replaced by these affine bounds; the `⌈s·A_s/2B_s⌉ = L(s)` step is `omega`.

DEVIATIONS from `tools/verify_gpt_arith.py` (both STRENGTHEN, machine-checked in
`scratchpad/check_affine_f5.py`): (a) feasible `d ≥ s−11` not `s−12` (11-vertex
nonexistence, so `Mfloor(11)=35` is never used — only makes the floor larger);
(b) the `u(d)=min(b,ex(d,K₄))` refinement is needed at EXACTLY `d=4` (`u(4)=5<b(4)=6`);
elsewhere `u=b`. `u=b` alone breaks the affine bound at `d=4` for `s=13,14,15`.

## Design notes (F6, 2026-07-10)

`Lean617/Brouwer.lean` (sorry-free; all exports axiom-clean = only
propext/Classical.choice/Quot.sound, no `sorryAx`/`ofReduceBool`). Everything is
CONDITIONAL on `BrouwerFacts` (the bundled external theorem, discharge pending),
exactly as F5's L-table is conditional on `PrimFacts`.

**Route decision:** Mathlib gives the *Turán* bound (`isTuranMaximal_turanGraph`
⇒ `cliqueFree_edgeCountIn_le_turan : CliqueFree (r+1) → e ≤ #(turanGraph n r).edgeFinset`)
and the closed form `card_edgeFinset_turanGraph`, so `t_5(15/16/21)=90/102/176` are
kernel-`decide` facts (`turan_5_{15,16,21}`). It does NOT give the `⌊n/r⌋−1` saving
for non-r-partite graphs, nor the extremal classification — the KP paper's proof of
those is an **induction on r** (Thm 4 + Lemma 3 + a Zykov-type symmetrisation; full
text extracted to scratchpad/kp.txt). Since the induction reduces r=5 through
r=2,3,4, "concrete instances" (route B) do not escape the general argument, so the
irreducible core is one general `saving` field.

**DESIGN LOCK — the "172-sharpening" shortcut is FALSE** (scratchpad/brouwer_design_lock.py):
`G((4,4,4,4,4))` is K₆-free on 21 vertices with α ≤ 4 and *exactly* 173 edges (all
|A*| ∈ {1,2,3}). So α ≤ 4 + K₆-free does NOT force e ≤ 172; §3's equality step
genuinely needs the KP classification, delivered as `BrouwerFacts.equality21`.

**F6 exports (F7 consumes VERBATIM; all take `(bf : BrouwerFacts)`):**
- `brouwer_bound_21 (bf) (J : SimpleGraph (Fin 21)) (hω : J.CliqueFree 6)
  (hα : alphaAtMost J 4) : edgeCountIn J Finset.univ ≤ 173`  — C1, §3.
- `brouwer_bound_16 (bf) (J : SimpleGraph (Fin 16)) (hω : J.CliqueFree 6)
  (hα : alphaAtMost J 3) : edgeCountIn J Finset.univ ≤ 100`  — C2/C3, §5 & §7.1.
- `brouwer_15_colorable (bf) (J : SimpleGraph (Fin 15)) (hω : J.CliqueFree 6)
  (he : 89 ≤ edgeCountIn J Finset.univ) : J.Colorable 5`  — C4, §7.2 (contrapositive;
  note `alphaAtMost J 3` does NOT force non-5-partite at n=15 since 5·3=15, so C4 is
  delivered in the `Colorable`/e≥89 form the informal §7.2 actually uses, NOT as an
  α-bound. F7 then combines `Colorable 5` with `α(F_i[W])≤3` to force `5K_3`).
- `brouwer_21_equality (bf) (F : SimpleGraph (Fin 21)) (hα : alphaAtMost F 5)
  (hK5 : F.CliqueFree 5) (he : edgeCountIn F Finset.univ = 37) : ∃ A B, Disjoint A B
  ∧ A.card=5 ∧ B.card=4 ∧ (∃ x∈A, ∃ y∈A, x≠y ∧ ¬F.Adj x y ∧ ∀ u∈A,∀ w∈A, u≠w →
  (¬F.Adj u w ↔ (u=x∧w=y)∨(u=y∧w=x))) ∧ (∀ u∈B,∀ w∈B, u≠w → F.Adj u w)
  ∧ edgeCountIn F (A∪B)=19`  — C1-equality, §3. Stated in COLOUR-CLASS (`F=F_i`)
  terms: `F[A]=K_5−xy`, `F[B]=K_4`, and 9+6+4=19 F-edges in A∪B (so exactly 4 cross
  `i`-edges). If F7 needs a different phrasing of the cross count, adjust the field
  (it is a hypothesis, so cheap to reshape).

**Reusable bridges (F7 will need these to move between `F_i` and `J_i = F_iᶜ`):**
- `alphaAtMost_iff_compl_cliqueFree (F) (m) : alphaAtMost F m ↔ Fᶜ.CliqueFree (m+1)`,
  plus specialisations `compl_cliqueFree_six_of_alphaAtMost_five` (α(F)≤5 ⇒ Fᶜ K₆-free)
  and `alphaAtMost_compl_four_of_cliqueFree_five` (F K₅-free ⇒ α(Fᶜ)≤4).
- `isIndep_iff_compl_isClique`, `not_colorable_of_alphaAtMost (J) (hα:alphaAtMost J k)
  (hlt: r*k<n) : ¬ J.Colorable r`.
- LTable already has `edgeCountIn_add_compl : e(G)+e(Gᶜ)=C(t,2)` for the 210−173=37 step.

**`BrouwerFacts` (the discharge target — the ONLY remaining F6 gap):**
- `saving : ∀ {n r}, 0<r → 2r+1≤n → ∀ G, G.CliqueFree (r+1) → ¬G.Colorable r →
  edgeCountIn G univ + (n/r − 1) ≤ #(turanGraph n r).edgeFinset` (Brouwer's bound).
- `equality21 : …` (KP Thm 4 classification at (5,21), as consumed by `brouwer_21_equality`).
Both are literature-VERIFIED (papers/brouwer-kang-pikhurko.md). Discharge = formalising
KP Thm 4's induction-on-r upper bound + the (5,21) equality case; a genuine
research-formalization effort, currently the isolated hard core.

**Discharge roadmap** (`kp_upper` by strong induction on `r` over `Fin n`, then
specialise to the `saving` field; KP proof text scratchpad/kp_proof.txt). Do
everything in `t_r`-form (the `caseA_slack` arithmetic lets us AVOID formalising the
`G(n)` construction + Lemma 5 for the *upper bound* — but see F6h for equality):
- **[DONE, `BrouwerProof.lean`, sorry-free]** Zykov symmetrisation `symmG G x`:
  `symmG_cliqueFree`, `symmG_edgeCount_ge` (`e(G) ≤ e(H)`, `x` max-degree),
  `no_clique_r_in_nbhd` (H[D] is `K_r`-free).
- **[DONE, `BrouwerDischarge.lean`, sorry-free on main]** `edgeCountIn_univ_of_cone`,
  `symmG_edgeCount_eq` (`e(H)=e(G[Γx])+d(n−d)`), `joinTuran`+`joinTuran_cliqueFree`,
  `turan_step` (`t_r(d)+d(n−d) ≤ t_{r+1}(n)` via Turán maximality).
- **[DONE, `BrouwerInduction.lean` scratch, sorry-free]** `exists_induced_on_nbhd`
  (transport `G[Γx]`→`Fin d` via comap kit), base cases `r∈{0,1}` (`cliqueFree_one/two`
  ⇒ contradiction), and the **full `kp_upper` skeleton** (max-deg `x`, symmetrise,
  case-split on `X=H[Γx]` (r−1)-colourable, Case A assembled via IH+`turan_step`+
  `caseA_slack`, `d>0`, all wired to `brouwerFacts : BrouwerFacts`).
- **[DONE #1, F6i — `caseA_slack`]** the arithmetic
  `t_{r−1}(d)+d(n−d)+kpSaving n r ≤ t_r(n)+kpSaving d (r−1)` for `2≤r, 0<d<n`.
  DISCHARGED sorry-free via the closed-form route (`two_mul_turan` + regime-split SOS; see
  the "caseA_slack (F6i) — DONE" note below in F6 DISCHARGE PROGRESS). The bounded
  `interval_cases` fallback was NOT used (general `n` is genuinely needed since the `saving`
  field is `∀ {n r}`). `kpSaving n r := if 2r+1≤n then n/r−1 else 2` (both KP Thm 1 regimes — needed
  because Case A descends below `2(r−1)+1`).
- **[TODO #2, HARD ~500-900 lines — `kp_caseB`]** H[D] (r−1)-partite: KP Thm 4 Case B
  + Lemma 3. **STRATEGY REFINED (F6i): the WHOLE of Case B stays in `t_r`-form and needs
  NEITHER the `G(n)` construction NOR KP's "maximality of G".** The trick is two PURE-
  ARITHMETIC backbone lemmas (both NUMERICALLY VERIFIED, 0 violations, scratchpad/
  check_kp_caseB_arith.py) that absorb the construction comparison, exactly as
  `caseA_slack` absorbed the Case-A one:
    * `two_bad_bound`: `σ₂(parts) − min(parts) + kpSaving n r ≤ t_r(n)` for any `r` parts
      each `≥2` summing to `n`. Equivalent to `kpSaving n r − min ≤ t_r(n) − σ₂(parts)`
      (imbalance covers it); note `σ₂(parts) = e(complete r-partite) ≤ t_r(n)` is Turán
      (`cliqueFree_edgeCountIn_le_turan` on the complete-r-partite graph) and the `−min`
      refinement is the balanced-minimises-Σp² fact. ~150-250 lines arithmetic.
    * `constr_le`: `e(G(seq)) + kpSaving n r ≤ t_r(n)` for every valid `r`-sequence, where
      `e(G(seq)) = σ₂(seq)+σ₁(seq)−n_s−n_t+1` (KP formula (4), seq sums to `n−1`, ≥2 parts
      >1). This is what KP Lemma 3's output `e(G) ≤ e(G(seq))` feeds into. It equals
      `pr(n) ≤ t_r−kpSaving` as pure arithmetic (Lemma 5/Thm 1 optimisation); tight (max
      over seq = `t_r−kpSaving`). ~200-350 lines (the seq optimisation is the work).
  With those two lemmas, the COMBINATORIAL part only has to REACH the LHS bounds:
  (a) if some part `d_i=1` ⇒ Lemma 3 directly; (b) Lemma 3 (`∃y, χ(G−y)=r` ⇒ `e(G) ≤
  e(G(seq))`): r-colour `G−y`, `Y={y}∪singletons` a clique (else G r-colourable),
  `M_i={z∈N_i:Γ(z)⊇Y}≠∅` (recolour), `l≤r−2`, missing-edge ineq (5) `Σē_ij≥m₁m₂`; the
  paper's "optimisation (6)" (mᵢ=nᵢ, m₁=1) is NO LONGER needed as a separate step —
  **VERIFIED (F6i, 0 violations / 4.1M cases)** that the PRE-optimisation Lemma-3 bound
  already gives the target for ALL `mᵢ∈[1,nᵢ]`:
    `lemma3_arith : σ₂(1^l,n₁..n_{r-l}) − m₁m₂ + l + Σmᵢ + kpSaving n r ≤ t_r(n)`
  (`l≤r−2`, `nᵢ≥2`, `n=l+Σnᵢ+1`, `m₁,m₂` the two smallest `mᵢ`). So the successor can prove
  `lemma3_arith` INSTEAD of `constr_le`+optimisation and feed it directly from the M_i
  sizes — no `e(G(seq))` naming, no exchange argument. This is likely the single cleanest
  arithmetic target for the Lemma-3 path; (c) good/bad dichotomy: **two bad ⇒
  `e(G) ≤ σ₂(d)−(d₁+d₂)/2 ≤ σ₂(d)−d₁`, close via `two_bad_bound` — NO maximality needed**
  (the paper only invoked maximality to CHARACTERISE extremal graphs, not for the bound);
  all good ⇒ `G[C]` empty ⇒ χ≤r (contra `hchi`) or `G⊇K_{r+1}` (contra `hCF`); unique bad
  ⇒ `∃z, χ(G−z)≤r` ⇒ Lemma 3. The `r=2` base is the inductive step specialised (D=Γx
  independent so H[D] trivially 1-partite; the unique/all-good analysis is vacuous — route
  via Lemma 3 with the singleton colouring). **Land `two_bad_bound` + `constr_le` FIRST
  (self-contained arithmetic, reusable, `#print axioms` clean); then the combinatorial
  Lemma 3 + good/bad on top.**
- **[TODO #3, HARD — `equality21` (F6h)]** the `(5,21)` equality classification. Here
  the `t_r`-form does NOT suffice: needs the KP construction `G((4,4,4,4,4))` structure
  (Lemma 5 optimal sequences ⇒ only (4,4,4,4,4) survives K₅-freeness ⇒ the A/B shape).
  scratchpad/verify_equality21.py has the computational cross-check of the exact
  conclusion. Depends on the equality-case analysis of the same induction.
Hardest link BY FAR: `kp_caseB` (Lemma 3 + good/bad). `caseA_slack` is the cheapest
remaining win. Total remaining est. ~1000–1800 lines.

## F6 DISCHARGE PROGRESS (2026-07-11)

**Route decision (LOCKED): Kang–Pikhurko induction, both regimes. SAT deferred.**
Rationale: the `saving` field is consumed by F7 ONLY via the four Brouwer.lean exports
(`brouwer_bound_21/16`, `brouwer_15_colorable`, `brouwer_21_equality`) at r=5,
n∈{15,16,21}. But (a) `brouwer_15_colorable` needs *positive* 5-colourability (not a
single UNSAT instance) so is not SAT-reducible; (b) `equality21` is a ∀-graph/∃-structure
classification, not a clean UNSAT; both need KP-style work regardless. The general
induction delivers all three bounds uniformly and is axiomatically cleaner (no extra
`native_decide`). c1_probe.log was empty (unstarted) at session start. If the C1/C2
probes ("n=21 α≤4 K6free e≥174 UNSAT" / "n=16 α≤3 K6free e≥101 UNSAT") later land, they
could *redundantly* discharge `brouwer_bound_21/16` but the KP route still needed for
n=15 + equality21, so not worth the extra axioms + huge LRAT certs (nonex11 was 256MB at
11 vtxs; n=21 with edge-cardinality would be far larger).

**State (F6i, 2026-07-11): `brouwerFacts : BrouwerFacts` COMPILES, reduced to 2 sorries.**
`caseA_slack` is now DISCHARGED (sorry-free, axiom-clean `[propext, Classical.choice,
Quot.sound]`). Remaining sorryAx sources: exactly `kp_caseB` and `equality21`. `turan_step`,
`two_mul_turan`, `caseA_slack`, and all foundations are axiom-clean. Discharging the 2
remaining sorries makes `brouwerFacts` axiom-clean and `erdos_617_r5 brouwerFacts : Main`
UNCONDITIONAL (modulo the existing primFacts `native_decide`).

**`caseA_slack` (F6i) — DONE.** New reusable division-free Turán identity (near the top of
BrouwerInduction, also useful for `equality21`):
  `two_mul_turan (n r) (1≤r) : 2*(turanGraph n r).edgeFinset.card
     = (n/r)*(n + n%r)*(r-1) + (n%r)*(n%r-1)`
derived from `card_edgeFinset_turanGraph` by clearing the `/(2r)` (`Nat.sq_sub_sq`,
`Nat.mul_div_mul_left`, evenness `Nat.even_mul_pred_self`). `caseA_slack` proof: double the
goal, `rw [two_mul_turan n r, two_mul_turan d (r-1)]`, `set q=n/r,s=n%r,qp=d/(r-1),sp=d%(r-1)`,
`split_ifs` on the two `kpSaving` regimes (4 branches MM/MS/SM/SS). `turan_step` gives
`hbase` (the ≥0 Turán slack) which closes the easy directions by `omega`; the hard directions
`zify` to ℤ and `nlinarith` on the VERIFIED B-identity
  `2t_r(n)-2t_{r-1}(d)-2d(n-d) = Q*(r(r-1)Q+2(r-1)s-2r*sp) + (s-sp)(s-sp-1)`, `Q=q-qp`
with explicit SOS product hints (MM Q=1 factorises as `s(s+1)+(r-2-sp)(2s+r+1-sp)`; Q≥2 uses
`bracket ≥ 2r-2 > 0`; SM forces `n=2r,d=2r-1` a single tight point). CAST GOTCHAS that cost
time: (i) `zify` needs `1≤r, 1≤r-1, 1≤q, 1≤qp` passed explicitly or `↑(r-1)`, `↑(q-1)`
(savings) stay uncast and nlinarith silently fails; (ii) `s*(s-1)` casts via a helper
`cast_pred : ↑a*↑(a-1) = ↑a*(↑a-1)`; (iii) `subst` FAILS on `set`-bound vars — use `rw` of
the value equalities instead; (iv) substitute `n,d` via `rw [hnZ, hdZ]` BEFORE the final
nlinarith so it works on `{q,s,qp,sp,r}` only (else heartbeat blowup — needs maxHeartbeats
2000000). Numeric pre-checks: scratchpad/check_caseA_full.py (0 violations, full range).

**Files:**
- `lean617/Lean617/BrouwerDischarge.lean` — **ON MAIN, sorry-free, in aggregator.**
  Foundations (cone decomposition, `symmG_edgeCount_eq`, `joinTuran`, `turan_step`).
  Imports `BrouwerProof` + `MH2Proof` (reuses `crossE`/`edgeCountIn_disjoint_union` — no
  duplication; a later refactor could extract `crossE` to a shared low-level module).
- `lean617/Lean617/BrouwerInduction.lean` — **ON MAIN, WIP, 2 sorries, NOT in aggregator**
  (so the default `lake build Lean617` / `erdos_617_r5` path stays sorry-free). Contains
  `kpSaving`, `two_mul_turan` (sorry-free), `caseA_slack` (**sorry-free, F6i**),
  `sig2`+`two_bad_aux` (**sorry-free, F6j**), `constr_base`+`constr_le` (**sorry-free, F6k**),
  `exists_induced_on_nbhd`, `kp_caseB` (SORRY, line ~443), `kp_upper` (skeleton, sorry-free
  body), `kp_saving`, `brouwerFacts` (`equality21` SORRY, line ~537).
  Successor: `lake env lean Lean617/BrouwerInduction.lean` to iterate (or, much faster, a
  scratch module `import Lean617.BrouwerInduction` to develop against the built olean, then
  paste back — full-file compile is ~100s). Discharge the 2 remaining sorries (all remaining
  work is the graph theory in the `kp_caseB` DECOMPOSITION ROADMAP above; the arithmetic is
  done), then add to the aggregator and wire `Final.lean` to drop `bf`. maxHeartbeats 2000000.

**Key facts a successor needs:**
- `kpSaving` MUST carry both regimes (`if 2r+1≤n then n/r−1 else 2`): the induction
  descends to `(d, r−1)` with `d=|Γx|≤n−1`, which for r=4,5 can fall below `2(r−1)+1`.
- The Case A arithmetic (`caseA_slack`) works because the Turán slack
  `t_r(n)−t_{r−1}(d)−d(n−d)` always covers `kpSaving n r − kpSaving d (r−1)` — this is
  what lets us stay in `t_r`-form (no `G(n)` construction) for the *upper bound*.
- Gotcha: `X : SimpleGraph (Fin (G.neighborFinset x).card)` — do NOT `rw` the
  neighbourhood/its card in any hyp whose type mentions `X` (motive ill-typed; f's type
  depends on the card). Keep everything in `(G.neighborFinset x).card` and let `omega`
  abstract the nonlinear `card*(n−card)`.
- Mathlib: `exists_maximal_degree_vertex` gives `maxDegree = degree x` (convert to the
  `∀ y, degree y ≤ degree x` form via `degree_le_maxDegree`); `card_edgeFinset_turanGraph`
  (closed form), `card_edgeFinset_turanGraph_add` (+r block recursion), `turanGraph_cliqueFree`.

## F6 DISCHARGE PROGRESS (2026-07-11, F6j/F6k — BOTH arithmetic backbones DONE)

**State: `brouwerFacts` still 2 sorries (`kp_caseB`, `equality21`), but the ENTIRE
arithmetic side of Case B is now sorry-free on main.** The remaining work in `kp_caseB`
is PURELY graph-theoretic (no more arithmetic). Commits: `806eac1` (F6j), `d8d2b13` (F6k).

**`two_bad_aux` (F6j, sorry-free) + `constr_le`/`constr_base` (F6k, sorry-free).** New
helper `sig2 : List ℕ → ℕ` (head-recursive σ₂: `sig2 (a::L) = a*L.sum + sig2 L`;
permutation-invariant value). The two backbones:
- `two_bad_aux (L) (hsorted : Pairwise (·≥·) L) (h2 : ∀x∈L, 2≤x) (m) (hm : m∈L)
  (hmle : ∀x∈L, m≤x) : sig2 L + kpSaving L.sum L.length ≤ t_{L.length}(L.sum) + m`
  — i.e. `σ₂(parts) − min + kpSaving n r ≤ t_r(n)` for `r` parts each `≥2` summing to `n`.
- `constr_le (ns nt) (hns2 : 2≤ns) (hnst : ns≤nt) (L) (hL : ∀x∈L, x=1 ∨ nt≤x)
  : sig2 (ns::nt::L) + (Σ+1) + kpSaving (Σ+1) r ≤ t_r(Σ+1) + ns + nt`
  — i.e. `e(G(seq)) + kpSaving n r ≤ t_r(n)`, `e(G(seq))=σ₂(seq)+σ₁(seq)−n_s−n_t+1` (KP (4)),
  `seq = ns::nt::L`, `ns≤nt` the two smallest parts `≥2`, rest each `=1` or `≥nt`.

**THE KEY TECHNIQUE (reused for both):** each REDUCES BY LIST INDUCTION to `caseA_slack`.
Peel one part `a` (head of a `≥`-sorted list for two_bad; any of `L` for constr_le); the σ₂
recursion gives `σ₂ = a·(Σ rest) + σ₂(rest)`, and the inductive step is EXACTLY `caseA_slack`
(`n := Σ+1`/`Σ`, `d := Σrest+1`/`Σrest`) because `kpSaving(n−a, r−1)` cancels between IH and
`caseA_slack`. The min (two_bad) / two-smallest `ns,nt` (constr_le) RIDE ALONG untouched
(peel the max / peel from `L` only). Base: `r=1` (two_bad, `t_1=0`) / `r=2` (constr_base,
`two_mul_turan` + factored `nlinarith` hint `(Q−ns)(Q−ns−1)≥0` even / `sq_nonneg(Q−ns)` odd).
GOTCHA that cost time: `set n := …` does NOT rewrite the Fin-index (first) arg of
`turanGraph n r` (dependent motive) — so instantiate `caseA_slack` at the *literal* `Σ+1`
and only `rw` the SECOND args (`length−1→length`, `N−d→a`), which are Fin-independent and safe.
Falsify-first: scratchpad/two_bad_route.py, lemma3_route.py (both 0 violations; the crude
"drop-m" bound (A) FAILS at 137885/6.3M, proving the `−min`/`−n_s−n_t` refinement is essential).

**`kp_caseB` DECOMPOSITION ROADMAP (all that remains — pure graph theory).** `kp_caseB`
hyps: `r≥2`, `G:SimpleGraph (Fin n)`, `x` (max-degree), `G.CliqueFree (r+1)`, `¬G.Colorable r`,
`X = G[Γx]` transported to `Fin |Γx|`, `X.CliqueFree r`, **`X.Colorable (r−1)`** (the Case B
discriminant). Goal `e(G) + kpSaving n r ≤ t_r(n)`. The skeleton already gives
`e(G) ≤ e(H) = e(X) + d·(n−d)` (`symmG_edgeCount_ge/eq` + `hXcount`). Decompose into:
- **(A) partition transport** [~40-80 lines infra]: from `X.Colorable (r−1)` + the embedding
  `f : Fin d ↪ Fin n` (image `Γx`, from `exists_embedding_image_eq`) produce a proper
  `(r−1)`-colouring `κ : Fin n → Fin (r−1)` of `G` on `Γx`; set `Dᵢ = {v∈Γx : κ v = i}`,
  `dᵢ=|Dᵢ|`, `d=Σdᵢ`, `c=n−d`. Mathlib: `SimpleGraph.Coloring`, `Colorable`; invert `f` via
  `Finset`/choice on `Γx`. (Reverse of `exists_induced_on_nbhd`'s clique transport.)
- **(B) degenerate guards** [~40 lines]: `c≥2` (else `c≤1` ⇒ `H` — hence, via `dG≤dH` +
  colouring lift, `G` — is `r`-partite ⇒ `¬hchi`); `d≥1`; some `dᵢ=0` collapses to fewer parts.
- **(C) `≥2` bad parts ⇒ two_bad_aux** [~120-200 lines]: "good" `Dᵢ` = `∃yᵢ∈Dᵢ` adjacent in
  `G` to all of `V∖Dᵢ`. If `D₁,D₂` bad, show `e(G) ≤ σ₂(d₁,…,d_{r−1},c) − min` (two bad
  vertices each miss `≥1` inside their non-part; `σ₂` = complete-`r`-partite bound on the
  `Dᵢ,C` blocks). Build the parts list/vector `(d₁,…,d_{r−1},c)` (ANY order) and feed
  **`two_bad_finset`** (`Fin r → ℕ` form) or **`two_bad_list`** (unsorted list, F6n — both sort
  internally via `mergeSort`, so no manual sorting), then `omega`. `σ₂(p) = sig2 (ofFn p)`.
- **(D) all good ⇒ contradiction** [~60 lines]: all good ⇒ `G[C]` empty (else the good
  witnesses + a `C`-edge span `K_{r+1}`, `¬hCF`) ⇒ `χ(G)≤r` (`¬hchi`).
- **(E) unique bad ⇒ Lemma 3** [~80 lines]: the one bad `D₁`: if every `y∈D₁` misses `≥2` in
  `C` then `e(G)≤σ₂(d)−2d₁ < σ₂(d)−d₁` (still two_bad_aux, stronger); else `∃y₁∈D₁, z∈C` the
  unique non-neighbour ⇒ `{y₁}∪good-witnesses` is an `(r−1)`-clique adjacent to `C∖{z}` ⇒
  `χ(G−z)≤r` ⇒ **(F)**.
- **(F) `kp_lemma3`** [THE HARD CORE, ~250-450 lines]: `r≥2, n≥r+3, G∈Gₙ,ᵣ, ∃y χ(G−y)=r
  ⇒ e(G) + kpSaving n r ≤ t_r(n)`, closed by **`lemma3_arith`** (F6m — see below). Internals:
  `r`-colour `G−y` (classes `{y₁},…,{y_l}` singletons + `N₁,…,N_{r−l}` of size `nᵢ≥2`);
  `Y={y,y₁,…,y_l}` a clique (else `r`-colourable); `Mᵢ={z∈Nᵢ:Γ(z)⊇Y}≠∅` (recolour argument,
  else `G` `r`-colourable), `mᵢ=|Mᵢ|`; `l≤r−2`; missing-edge ineq (5) `Σē_ij ≥ m₁m₂` (counts
  `K_{r+1}` copies — a product `Πmᵢ` / greedy-extension argument, the single hardest step) gives
  `e(G) ≤ σ₂(1^l,nvec) − m₁m₂ + l + Σmᵢ`. **Then feed the `mᵢ` DIRECTLY to `lemma3_arith` — NO
  optimisation step (6), NO `e(G(seq))`.** `r=2` base: `D=Γx` independent (K₃-free) ⇒ trivial
  1-partition, good/bad vacuous, route via Lemma 3 with the singleton colouring.

**`lemma3_arith` (F6m — DONE, sorry-free, axiom-clean).** `σ₂(1^l,nvec) − m₁m₂ + l + Σmᵢ +
kpSaving n r ≤ t_r(n)` (as `…+kpSaving ≤ t_r + m₁m₂` in ℕ), verified 0 viol / 4.1M
(scratchpad/check_kp_caseB_arith.py). Interface: pull the two smallest-`m` big classes to the
front as `(na,ma),(nb,mb)` (SORTED by size `na≤nb`; product `ma·mb` is symmetric so this is the
paper's `m₁m₂`), rest `L : List (ℕ×ℕ)` of `(nᵢ,mᵢ)` with `2≤nᵢ, 1≤mᵢ≤nᵢ`, `l` ones. Proof:
`constr_le` (now WEAKENED to accept ANY two `≥2` front parts + rest `≥1` — the proof only ever
needed each `L`-part `≥1`) + `(ma−1)(mb−1)≥0` + `Σ_L m ≤ Σ_L n` (`snd_sum_le_fst_sum`), combined
by `omega`. This SUPERSEDES the constr_le→optimisation route: SUB-LEMMA G is absorbed (it is
exactly the `omega` step here). NOTE: my backbones did NOT need the `σ₂(parts) ≤ t_r` complete-
multipartite/Turán transport (the peel→caseA_slack recursion sidesteps it) — that ~80-120-line
budget is saved.

**Arithmetic wiring (DONE, sorry-free, axiom-clean):** (C),(E) → `two_bad_aux`; (F) →
`lemma3_arith`. What is left is entirely combinatorial — the missing MathLib gap is a
colouring↔partition bridge (A) and the `K_{r+1}`-counting inequality (5). No new arithmetic
is needed.

**`equality21` (F6h, still SORRY):** unchanged; needs the `G((4,4,4,4,4))` construction
structure (Lemma 5 optimal-sequence classification), genuinely after (F). t_r-form does NOT
suffice here (see F6 design lock). scratchpad/verify_equality21.py has the target cross-check.

## F6 DISCHARGE PROGRESS (2026-07-11, F6q/F6r/F6s — Case-B good/bad dichotomy DONE)

**State: the ENTIRE Case-B good/bad dichotomy (sub-lemmas A–E) is formalised sorry-free
except two isolated gaps: `kp_lemma3` (sub-lemma F, the K_{r+1}-counting core) and the
`some-part ≤ 1` guard. All in `BrouwerInduction.lean` as `kp_caseB_impl` (the new Case-B
core, takes the `(r−1)`-colouring `κ` directly).** Commits F6q (`dcfd131`), F6r (`1bdeef4`),
F6s (`727a4a9`). Sub-lemma A is F6o (`colorable_restrict_of_comap`, a parallel runner).

**THE KEY WORKHORSE — `main_ineq` (F6q, sorry-free):** the clean degree inequality
`2·e(G) + Σ_{v∈D} defc(v) ≤ 2·σ₂(blocks)`, where `D = Γx`, `blocks = (d₀,…,d_{r−2}, c)`
(the `r−1` colour-part sizes + `c = |C| = n−d`), `defc(v) = n − |D_{κv}| − d_G(v)` is
`v`'s deficiency outside its own part. The ONLY inequality used is the max-degree bound on
`C` (`Σ_{v∈C} d_G(v) ≤ c·d = ∆·|C|`); EVERYTHING ELSE IS EXACT. Derivation: `2e(G) = Σ_v d(v)`,
split `D`/`C`; on `D`, `d(v) = (n − d_{κv}) − defc(v)` (neighbours avoid own part, `Dᵢ` indep);
`Σ_i d_i(n−d_i) + c·d = 2σ₂` (arithmetic, `c+d=n`). Support: `two_edge_le_sum_degree_add`
(INEQ-1), `degree_le_of_part`, `sqsum`/`sqsum_ofFn`/`sqsum_append` bridging to `two_mul_sig2`.
This REPLACES KP's informal edge-accounting; it is the maximality-free heart of Case B.

**`caseB_close` (F6q, sorry-free):** given all parts `≥2`, `c≥2`, a block-minimum `m`, and
`Σ defc ≥ 2m`, closes `e(G)+kpSaving ≤ t_r` via `main_ineq` + `two_bad_list`. (`e(G) ≤ σ₂−m`
and `two_bad_list`: `σ₂+kpSaving ≤ t_r+m`, `omega`.) `list_has_min` helper.

**Good/bad reusable helpers (F6r, sorry-free):**
- `no_Kr_plus_edge`: an `(r−1)`-clique + a cross edge (two outside vertices adjacent to all of
  it and each other) ⇒ `K_{r+1}` (contra `CliqueFree`). The single Kr+1-contradiction lemma.
- `colorable_of_C_indep`: `C = univ∖Γx` independent ⇒ `G.Colorable r` (κ on `D` + a fresh colour
  on `C`; `Coloring.mk`). The r-colourability lemma for the c≤1 guard and all-good-empty case.
- `good_witness_adj`: a `defc = 0` part vertex is adjacent to everything outside its part
  (`Γ(y) = univ∖Dᵢ` by cardinality: `deg = n − |Dᵢ|`).

**Good/bad dispatch `kp_caseB_impl` (F6r+F6s), sorry-free for:**
- **c ≤ 1 guard (sub-lemma B, c-part):** `C` has ≤1 vertex ⇒ independent ⇒ `colorable_of_C_indep`
  ⇒ contra `hchi`.
- **all parts good (sub-lemma D):** good witnesses form an `(r−1)`-clique `K`; a `C`-edge ⇒
  `no_Kr_plus_edge` (Kr+1), else `C` independent ⇒ `colorable_of_C_indep` (χ≤r). Both contra.
- **≥2 bad parts (sub-lemma C):** two disjoint bad parts ⇒ `Σ defc ≥ d_i+d_j ≥ 2m` ⇒ `caseB_close`.
- **unique bad part, every vertex misses ≥2 (sub-lemma E, two_bad branch):** `Σ defc ≥ 2d_{i0} ≥ 2m`
  ⇒ `caseB_close`.
- **unique bad part, a 1-miss vertex `v1` (sub-lemma E, Lemma-3 branch, F6s):** `v1`'s unique
  non-neighbour `z` outside its part is found (`|W|=1`); good witnesses (all adjacent to `v1`,
  so none `= z`) `+ v1` form an `(r−1)`-clique `K` adjacent to everything outside `D` except `z`.
  `z ∈ D` ⇒ `K` adjacent to all `C` ⇒ Kr+1/χ≤r contra; `z ∈ C` ⇒ `K` adjacent to `C∖{z}` ⇒
  Kr+1 (edge in `C∖{z}`) or the explicit r-colouring proper off `z` ⇒ `kp_lemma3`.

**REMAINING GAP 1 — `some-part ≤ 1` guard (`kp_caseB_impl`, one SORRY):** a colour part with
`d_i ≤ 1` breaks `two_bad` (verified: 119 arith violations at min=1). Structure:
- `d_i = 0` (empty part): CLEANLY handled by "drop empty parts, use `k+1 < r` blocks" — VERIFIED
  `pr(n,r) = t_r(n) − kpSaving` is NON-DECREASING in `r` (0 violations, so `two_bad` at `k+1`
  blocks gives `e(G) ≤ pr(n,k+1) ≤ pr(n,r)`). Needs a small `pr_mono` arith lemma + a
  `caseB_close` variant taking `k+1 ≤ r` blocks. ~40 lines, DOABLE (successor).
- `d_i = 1` (singleton `{w}`): PARTIAL result proved-in-analysis — **a singleton part is BAD when
  `c ≥ 2`** (if good, `deg(w)=n−1=∆` ⇒ `deg(x)=n−1` ⇒ `c=1`, contra). If `defc(w)=1` the sub-lemma-E
  Lemma-3 route already applies (no `caseB_close` needed). The residual hard case is a singleton
  with `defc(w) ≥ 2` and its `≥2` misses in `C`: `two_bad` gives only `e ≤ σ₂−1` (insufficient),
  and removing ONE `C`-vertex does not make `G` r-colourable, so no `kp_lemma3` either. **This is
  exactly where KP invokes MAXIMALITY of `G`** (paper Thm 4: "each `dᵢ ≥ 2` … otherwise Lemma 3").
  RESOLUTION for the successor: prove `kp_upper` for a MAX-size `G ∈ Gₙ,ᵣ` (finite class, nonempty
  since `G` witnesses it ⇒ `Finset.exists_max_image`; then `e(G') ≤ e(Gmax)`), giving the
  maximality hypothesis KP uses. OR find a recolouring argument (essential-singleton: `w` adjacent
  to ≥1 in every part).

**REMAINING GAP 2 — `kp_lemma3` (sub-lemma F, the HARD core, SORRY):** stated as
`kp_lemma3 (hr) (G) (hn : r+3 ≤ n) (hCF) (hchi) (z) (κ' : Fin n → Fin r)
  (hproper' : ∀ u v, u≠z → v≠z → Adj u v → κ' u ≠ κ' v) : e(G)+kpSaving ≤ t_r`. Both Lemma-3
routes (unique-bad-1-miss, some-part≤1) feed it. FULL PROOF SKELETON (worked out + numerically
verified this session — the edge-accounting identity below is 0-violations, so the ONLY genuinely
hard step is inequality (5)):
- STEP 1 (classes). `Dᵢ = (univ.erase z).filter(κ'·=i)`, `i:Fin r`, each `G`-independent (κ'
  proper off z). Split by size: `l` singletons `{y₁},…,{y_l}`, big `N₁,…,N_{r−l}` (`nᵢ≥2`), plus
  possibly EMPTY classes (colour unused on `G−z`; an empty class lets z take that colour ⇒ `G`
  r-colourable ⇒ contra `hchi`, ruling empties out). `n = 1 + l + Σnᵢ`.
- STEP 2 (Y clique, ~30-40 lines). `Y={z,y₁,…,y_l}`. Non-adjacent pair in `Y` ⇒ recolour (z→its
  non-neighbour singleton's colour, or merge two singletons freeing a colour for z) ⇒ `G`
  r-colourable ⇒ contra. So `Y = K_{l+1}`.
- STEP 3 (Mᵢ≠∅, ~40-60 lines). `Mᵢ={u∈Nᵢ:Γ(u)⊇Y}`, `mᵢ=|Mᵢ|`. If `Mᵢ=∅`, each `x∈Nᵢ` picks
  `f(x)∈Y` with `x⊀f(x)`; `l+1` sets `{y}∪f⁻¹(y)` (independent) partition `Y∪Nᵢ` ⇒ r-colouring ⇒
  contra. So `mᵢ≥1`.
- STEP 4 (l≤r−2, ~20 lines). `l=r−1` ⇒ `Y=K_r` + `x∈M₁` ⇒ `K_{r+1}` (contra `hCF`); `l=r` ⇒
  `n≤r+1<r+3` (contra `hn`). So `l≤r−2` (⇒ ≥2 big classes; `m₁,m₂` two smallest `mᵢ`).
- STEP 5 (edge accounting, ~60-80 lines). `e(G)=e(G−z)+d_G(z)`; `e(G−z)=σ₂(sizes)−Σēij`; bound
  Y–Nᵢ edges `Σ_{u∈Nᵢ}|Γ(u)∩Y| ≤ mᵢ(l+1)+(nᵢ−mᵢ)l = mᵢ+l·nᵢ`. Sum ⇒
  `e(G) ≤ C(l+1,2)+σ₂(nvec)−Σēij+Σmᵢ+l·Σnᵢ`. VERIFIED IDENTITY (0 viol):
  `C(l+1,2)+σ₂(nvec)+Σmᵢ+l·Σnvec = σ₂(1^l,nvec)+l+Σmᵢ`, so **`e(G) ≤ σ₂(1^l,n₁..n_{r−l})+l−Σēij+Σmᵢ`.**
- STEP 6 (inequality (5), THE HARD CORE) — **DONE, sorry-free (F6u, `missing_edges_ge`).** See
  the F6u note below; the graph supplies `hbad` (no rainbow-clique transversal) and the two
  smallest `Mᵢ`; the lemma outputs `Σ_{i<j} ē_ij ≥ m₁m₂` as a `Finset`-sum over ordered pairs.
- STEP 7 (feed `lemma3_arith`, ~30 lines). Steps 5+6 ⇒ `e(G) ≤ σ₂(1^l,nvec)−m₁m₂+l+Σmᵢ`. Two big
  classes with smallest `mᵢ` = `(na,ma),(nb,mb)` (sorted `na≤nb`), rest `L:List(ℕ×ℕ)`; `lemma3_arith`
  gives `σ₂(na::nb::(1^l++nrest))+l+(ma+mb+ΣL.snd)+kpSaving ≤ t_r+ma·mb`; `sig2_perm` matches, `omega`.

Estimate ~350–500 lines; steps 2,3 (recolour) and step 6 (inequality 5) are the hard/long ones,
the rest is bookkeeping + the verified arithmetic. `lemma3_arith` (sorry-free) is the exact sink.

## F6 DISCHARGE PROGRESS (2026-07-11, F6t — small-`n` lemma + wiring DONE; sorries 4→3)

**State: `BrouwerInduction.lean` now has exactly 3 sorries** (was 4): `kp_lemma3` (sub-lemma F),
`kp_caseB_impl`'s `some-part ≤ 1` guard, `equality21`. The OLD opaque `kp_caseB` is **deleted**;
`kp_upper`'s Case B is wired directly into `kp_caseB_impl`. Full lib (`lake build Lean617`) still
builds sorry-free (BrouwerInduction is NOT in the aggregator). Runner 13.

**Small-`n` emptiness `gnr_colorable_small` (F6t, sorry-free, axiom-clean).** `n ≤ r+2 ∧
CliqueFree(r+1) ⇒ Colorable r` (⇒ `hn : r+3 ≤ n` at every Case-B entry). Reusable helpers now in
`BrouwerInduction.lean`:
- `colorable_of_proper_on (T) (c₀ : Fin n → Fin k) (proper on T) : Colorable (k + (n − |T|))` — the
  workhorse: colour `T` with `c₀` (`Fin.castAdd`, `< k`), inject `Tᶜ` (`Fin.natAdd ∘ equivFinOfCardEq`, `≥ k`).
- `colorable_of_indep` (one independent set, `k=1`), `exists_nonedge` (`K_k`-free on `Fin m`, `k≤m`).
- The `n=r+2` case: no-independent-triple + no-two-disjoint-non-edges ⇒ some `v` incident to all
  non-edges ⇒ `univ.erase v = K_{r+1}` (contra). Else colour via `colorable_of_indep` (triple, `k=1`)
  or `colorable_of_proper_on` (two pairs, `k=2`).

**Wiring `kp_upper` → `kp_caseB_impl` (F6t, done).** Case-B branch now: `exists_embedding_image_eq`
exposes `f : Fin |Γx| ↪ Fin n`; `X := G.comap f` with `hXcount`/`hXCF` inline (K_r-transport copied
from `exists_induced_on_nbhd`); `hn : r+3 ≤ n` from `gnr_colorable_small` (contrapositive of `hchi`);
`κ0 : Fin n → ℕ` from `colorable_restrict_of_comap G f (hXdef ▸ hXcol)`, converted to
`Fin (r−1)` via `⟨κ0 v % (r−1), _⟩` (the `% (r−1)` is identity on `Γx` since `κ0 < r−1` there, so
`hproper` transfers). Case A unchanged.

**REMAINING (3 sorries), keystone-first:** `kp_lemma3` is the keystone — the `some-part ≤ 1` guard's
singleton subcase routes through it (singleton ⇒ maximality ⇒ `χ(G−z)=r` ⇒ Lemma 3), so the guard
cannot close without it; `kp_lemma3` itself needs NO maximality (standalone). So the max-size
reduction only pays off AFTER `kp_lemma3`. `equality21` is independent (∀-F uniqueness, hard).
See the STEP 1–7 skeleton above; STEP 6 (inequality (5), transversal counting) is the single hardest.

**F6w (runner 13): max-size machinery `Lean617/BrouwerMax.lean` (NEW file, sorry-free, axiom-clean).**
Imports `BrouwerDischarge`; sits below `BrouwerInduction` (which will `import` it for the guard).
- `exists_max_counterexample`: `G(n,r)` (`K_{r+1}`-free, non-`r`-colourable) is finite
  (`Fintype (SimpleGraph (Fin n))`); a witness ⇒ a max-edge member `Gmax` (`Finset.exists_max_image`).
- `max_size_saturated (hmaxE) (u v) (u≠v) (¬Adj u v) : ∃ K, IsClique K ∧ |K|=r−1 ∧ u,v∉K ∧
  (∀w∈K, Adj u w) ∧ (∀w∈K, Adj v w)`. Adding `uv` to a max `Gmax` strictly raises `e` (`G ⊔ edge u v`,
  strict `edgeFinset` subset — GOTCHA: `mem_edgeFinset` needs `simp only`, not `rw`, else the
  `fintypeEdgeSetSup ≠ fintypeEdgeSet` instance clash), so by `hmaxE` it has a `K_{r+1}` using `uv`,
  giving the `(r−1)`-clique. `hmaxE : ∀ G', CF → ¬Col → e(G') ≤ e(Gmax)` is what the max-size
  reduction of `kp_upper` supplies. NB `gnr_colorable_small` kept in `BrouwerInduction` (working).

## SINGLETON REDUCTION — pinned argument (runner 13 / lean-f6f, final act, 2026-07-11)

> CONSOLIDATED: for orientation and the exact isolated sorry, see **"KP-EQUALITY CORE"** near
> the top. This section is the detailed historical record of the guard's singleton analysis.


The one step in Case B that neither [KP] nor prior FORMAL notes spell out: how a `some-part ≤ 1`
(singleton) part, with maximality, forces some `z` with `χ(G−z)=r` so `kp_lemma3` applies.

**Setup.** `G` a MAX-SIZE member of `G(n,r)` (`K_{r+1}`-free, `¬r`-colourable, `n≥r+3`), Case B:
`H[D]` is `(r−1)`-partite, `D=Γx=⊍_{i=1}^{r−1} Dᵢ` (each `Dᵢ` `G`-independent), `c=|C|=n−d≥2`, and
some `D_{i0}` has `|D_{i0}|≤1`. Goal `e(G)+kpSaving ≤ t_r`, via `kp_lemma3` (hypothesis: `∃z,
(G−z).Colorable r`). The max-size reduction (`exists_max_counterexample`) supplies `hmaxE`, whence
`max_size_saturated`.

**NUMERIC VALIDATION (falsification-first; `scratchpad/singleton_check{,2,3}.py`, brute force over
EVERY max-size `G∈G(n,r)`):**
- `(n,r)=(6,3)`: `pr=10`, 72 max-size graphs — **72/72** have some `z` with `χ(G−z)≤3`.
- `(7,3)`: `pr=15`, 252 graphs — **252/252**.  `(7,4)`: `pr=16`, 252 graphs — **252/252**.
So `kp_lemma3`'s hypothesis holds for EVERY max-size counterexample (576/576) — the singleton is
NOT an exception. A witnessing `z` is always a non-neighbour of a minimum-degree vertex (576/576).
BUT two natural colouring MECHANISMS are **FALSIFIED** (so the reduction is subtle, not one line):
(i) the non-neighbour set `M(w)=V∖N[w]` of a min-degree `w` is NOT independent (0/72, 0/252);
(ii) "colour `{w}∪M(w)` one colour, `(r−1)`-colour `N(w)`" fails (0/72, 0/252). The working `z`'s
removal breaks non-colourability by a non-obvious route.

**RIGOROUS SCAFFOLD (established):**
1. A singleton part is BAD when `c≥2`: if `D_{i0}={w}` had `defc(w)=0` then `deg(w)=n−1=Δ(G)=deg(x)`,
   so `x` is universal ⇒ `C={x}` ⇒ `c=1`, contra. (`good_witness_adj`-style.)
2. [IF `{w}` is the unique bad part, others good] `{w}∪{good witnesses yⱼ}` is an `(r−1)`-clique
   adjacent to all of `C` except `w`'s `C`-non-neighbours `W_C`; hence `C∖W_C` is independent (an
   edge there ⇒ `K_{r+1}` via `no_Kr_plus_edge`).
3. `|W_C|=1` (unique `C`-miss `z`) ⇒ `C∖{z}` independent ⇒ `χ(G−z)≤r` ⇒ `kp_lemma3`. THIS IS
   ALREADY the sub-lemma-E route in `kp_caseB_impl`; a singleton with a 1-miss needs no new work.

**THE CRUX (unresolved):** unique bad singleton `{w}` with `|W_C|≥2`. `two_bad` gives only
`e(G)≤σ₂−1` (block-min `=1`), insufficient (verified). `C∖W_C` indep (scaffold 2) but only ONE `z`
may be deleted; the other misses `W_C∖{z}` obstruct a direct `r`-colouring (they need not be
mutually non-adjacent). Numerics say a good `z` EXISTS but its colouring is subtle. This is exactly
where KP's maximality is essential and where the argument is not written down.

**RECOMMENDATION for f6g (two routes):**
- (A) CLEAN-LEMMA route (preferred if provable): `∀ max-size G∈G(n,r), n≥r+3, ∃z, (G−z).Colorable r`
  (validated 576/576). If provable, the guard — indeed all of Case B for max-size `G` — collapses to
  "pick `z`, apply `kp_lemma3`", sidestepping the good/bad analysis for the BOUND. Mechanism is OPEN
  (the two obvious colourings are falsified); likely a criticality/one-deletion argument on the
  max-size structure. Worth a literature check ("`(χ>r)`-extremal `K_{r+1}`-free graph is `r`-colourable
  after one vertex deletion?").
- (B) KP route: pin the `≥2`-miss argument via maximality. Candidate: iterate `max_size_saturated`
  over the misses to show `W_C` is INDEPENDENT (then colour `W_C∖{z}` with `w`'s colour `i0` after
  deleting one `z∈W_C`). Decide it with a TARGETED numeric check ("for max-size `G` with a bad
  singleton, are its `≥2` `C`-misses mutually non-adjacent?") — I ran out of budget before isolating
  the singleton structure inside the enumerator; f6g should run it before coding.

**BrouwerMax exports (stable, for f6g):**
`exists_max_counterexample (G) (hCF) (hchi) : ∃ Gmax, CF Gmax ∧ ¬Col Gmax ∧ ∀ G', CF→¬Col→e(G')≤e(Gmax)`
and `max_size_saturated (hr:1≤r) (G) (hCF) (hchi) (hmaxE:∀G',CF→¬Col→e(G')≤e(G)) (u v) (u≠v)
(¬Adj u v) : ∃ K, IsClique K ∧ |K|=r−1 ∧ u∉K ∧ v∉K ∧ (∀w∈K, Adj u w) ∧ (∀w∈K, Adj v w)`.
If route (B) needs the `K_{r+1}`'s clique in a SPECIFIC location (e.g. `K∩C`), that is NOT provided —
`max_size_saturated` only guarantees `K` avoids `u,v` and is adjacent to both; a strengthened export
would be a new lemma.

**RUNNER-14 UPDATE (2026-07-12, lean-f6g) — the crux REFRAMED (W_C=∅, not ≥2), closure still OPEN:**
- **KEY LEMMA (proof sketch verified, not yet formalised): the singleton part vertex `w` is adjacent
  to ALL of `C`.** For any `z ∈ C∖{x}` (`¬Adj x z`, `x≠z`), `max_size_saturated x z` yields an
  `(r−1)`-clique `K ⊆ N(x)=D` adjacent to `z`. `G[D]` is `(r−1)`-partite (via `κ`, `hproper`), so a
  size-`(r−1)` `G`-clique in it is a TRANSVERSAL (one vertex per `κ`-class), hence hits the singleton
  class `i0={w}` ⇒ `w ∈ K` ⇒ `Adj w z`. And `Adj w x` (`w∈Γx`). So `w` adj ALL `C`, i.e. `W_C=∅`.
  This CORRECTS f6f's framing: the obstruction is NOT "≥2 misses" — maximality forces 0 misses.
- **BUT the closure is still open.** `W_C=∅` ⇒ `C` is NOT independent (else `κ` on `D` + fresh colour on
  `C` is a proper `r`-colouring ⇒ contra `hchi`), so a `C`-edge exists. Deleting `w`: `χ(G−w) ≤ (r−2) +
  χ(G[C])` (disjoint colour ranges: `r−2` for the other parts `D∖{w}`, the rest for `C`), which needs
  `G[C]` bipartite — does NOT follow from `W_C=∅`. And "`w` adj all `C`" is SPECIAL to the singleton
  (only its unique vertex lies in every transversal `K_z`; other parts get no fixed `C`-good witness),
  so one CANNOT build an `(r−1)`-clique adjacent to all `C` for the all-good/`Kr+1` contradiction.
- **EMPTY-part sub-case (`d_{i0}=0`):** the "`H` is `(r−1)`-partite ⇒ `e(G) ≤ t_{r−1}(n)`" shortcut is
  **FALSIFIED** — `t_{r−1}(n) + kpSaving n r ≤ t_r(n)` FAILS at the tight end (e.g. `(n,r)=(8,5)`:
  `t₄(8)+kpSaving = 24+2 = 26 > 25 = t₅(8)`). So `e(G) ≤ t_{r−1}` is NOT sufficient. Use f6f's route
  instead: `two_bad` at `k+1 < r` blocks (nonempty parts + `C`) + `pr` monotonicity (`pr(n,k+1) ≤
  pr(n,r)`, `pr = t − kpSaving`, verified non-decreasing in `r`). NB the guard's `by_cases` only exposes
  ONE small part `i0`; there may be OTHER small parts, so the block-dropping must handle a general count.
- **VERDICT:** the singleton `≥`-part guard is a genuine research step (open closure for `W_C=∅`), NOT a
  ~40-100-line close. Recommend: formalise the KEY LEMMA (`w` adj all `C`) + empty-case Turán, then a
  dedicated attack on "`χ(G[C])≤2` / `∃z χ(G−z)≤r` for max-size `G`" (lit check: does a `K_{r+1}`-saturated
  non-`r`-colourable maximum graph become `r`-colourable after ONE vertex deletion?).

## SINGLETON GUARD — CLOSED sorry-free (2026-07-12, F6aa, lean617_f7; Route MI)

**DONE.** The `some-part ≤ 1` guard of `kp_caseB_impl` is now discharged **sorry-free and
axiom-clean** in `BrouwerInduction.lean`, exactly per the Route-MI analysis below. `#print axioms`:
`kp_caseB_impl`, `kp_upper`, `kp_saving` are all `[propext, Classical.choice, Quot.sound]` (CLEAN —
they do NOT route through `equality21`); `brouwerFacts` retains `sorryAx` from `equality21` ONLY.
The former `guard_singleton_closure_OPEN` (max-size / Lemma-3 route) is RETIRED from
`GuardScaffold.lean`; `singleton_adj_all_C`/`clique_hits_singleton` kept as standalone verified
lemmas, `BrouwerMax.lean` kept as sorry-free banked machinery. **`equality21` is now the SOLE
remaining sorry in the KP upper-bound leg.**

New sorry-free lemmas added to `BrouwerInduction.lean` (before `kp_caseB_impl`):
- `turan_le_succ` (`t_r(n) ≤ t_{r+1}(n)`, from `turan_step` at `d=n`);
- `turan_addvertex` (`t_r(n) ≤ t_r(n−1) + (n−2)` for `2r+1 ≤ n`, `2 ≤ r`; `two_mul_turan` + div/mod);
- `m0_lift` (the 0-part lift `kpSaving n (r+1) + t_r(n) ≤ kpSaving n r + t_{r+1}(n)`; easy regimes via
  monotonicity, the hard mixed-regime `n ∈ {2r+1,2r+2}` via `turan_step d=n−1` + `turan_addvertex`);
- `baseAB` (`[s,c]` base, `s ≤ 1`, `c ≥ 3`, via `two_mul_turan`);
- `sig2AB_core` (the peel induction: `2·σ₂(s::c::L) + 2·kpSaving ≤ 2·t + s·(c−1)`, head-peel — `0`
  head via `m0_lift`, positive head via `caseA_slack`, base via `baseAB`; L parts ≥ 0 arbitrary);
- `guard_somepart_closure` (graph wiring: `c ≥ 3` from `colorable_of_C_indep`; `main_ineq`; blocks
  matched to `p i0 :: c :: L` via sum+sqsum equality with `Fin.sum_univ_succAbove` — no `List.Perm`
  surgery; the singleton/empty cases UNIFY as `p i0 · (c−1) ≤ Σ defc`).

Numerics for Lemmas A/B (doubled form) and `m0_lift`: `scratchpad/guard_lemmaAB_doubled.py`,
`guard_m0_extra.py` (0 violations; A/B hold for ALL `n ≥ 3`, not just `n ≥ r+3`; tight at
`(1,2,3)`/`(0,2,2,3)`). The peel handles arbitrary extra `0`/`1` middle parts. **NB the empty case
does NOT go through the `t_{r−1}(n)` shortcut (that is FALSE, per the DEAD END below); Lemma B uses
`σ₂(blocks)` with actual sizes AND `c ≥ 3`.**

## SINGLETON GUARD — analysis (2026-07-12, math-analysis runner; NO Lean edits)

**VERDICT (supersedes the RUNNER-13/14 "needs max-size" framing above).** The `some-part ≤ 1`
guard (`kp_caseB_impl` sorry at `BrouwerInduction.lean:2077`) is TRUE and PROVABLE from the
EXISTING hypotheses — **max-DEGREE (`hmax`) only, NO max-size, NO `BrouwerMax`, NO `kp_lemma3`,
NO good/bad dichotomy.** It closes by the SAME maximality-free edge count (`main_ineq`) the rest of
Case B uses, once one observes `c ≥ 3`. The runner-13/14 pursuit of `exists_max_counterexample` /
`max_size_saturated` / "`w` adj all `C`" (`W_C=∅`) was a WRONG TURN — that machinery is not needed
for the guard. Est. **~250–400 Lean lines**: ~120 wiring (steps 0–2 below) + two fresh arithmetic
lemmas (~80–150 each, SAME family/technique as the already-proven `two_bad_aux`/`constr_le`).

Task-1 classification: closest to **(c)** "maximality is used in a different spot than our
transcription", sharpened: KP's "otherwise Lemma 3" is a VALID but non-minimal route; the part is
closed WITHOUT Lemma 3 (and without maximality) at all.

### Task 1 — what KP actually does with parts of size ≤ 1
[Thm 4, para "Hence, we can assume that H[D] is (r−1)-partite …"]: *"Let d_i = |D_i|, d = |D|, and
c = |C|. **We can assume that each d_i is at least 2 for otherwise the required upper bound follows
by Lemma 3.** Also, c ≥ 2 for otherwise G = H is r-partite."* So KP dispatches `d_i ≤ 1` to Lemma 3
(`∃y χ(G−y)=r`) in ONE terse sentence, no mechanism. That route IS valid (verified below: `∃z
χ(G−z)≤r` holds for EVERY max-degree singleton config), but constructing `y` is nontrivial — `y=w`
does NOT work in general (`χ(G−w)≤r` fails on 4/64 configs at n=8; the witness `z` is a specific
`C`-vertex needing a non-obvious r-colouring). Our transcription does not need it.

### Task 2 — falsification / verification (brute-force + `geng` iso-enum; `scratchpad/guard_*.py`)
- The guard is NOT vacuous but heavily constrained. With `x` a GENUINE max-degree vertex: `n=r+3,r+4`
  (r=2,3,4) give **0** singleton/empty configs; the config first appears at `n=r+5` (n=8,r=3: 39
  singleton+1 empty; n=9,r=3: 919+13; n=9,r=4: 116+0). For ARBITRARY (non-max) `x`, thousands even
  at n=6 — so requiring `x` MAX-DEGREE is exactly the constraint. [`guard_relaxed.py`,`guard_geng.py`]
- **`c ≥ 3` ALWAYS** (min c = 3 across every enumerated case) — and PROVABLE, not just empirical:
  `c ≤ 2 ⇒ C = univ∖Γx is independent` (`x` is isolated in `G[C]`; any `C`-edge forces two vertices
  of `C∖{x}`, i.e. `c ≥ 3`) `⇒ colorable_of_C_indep ⇒ G.Colorable r ⇒` contra `hchi`.
- **Both candidate routes hold with ZERO failures** on every max-degree singleton/empty config
  (n=8,9; r=3,4): (i) `∃z χ(G−z)≤r` [Lemma-3 route], and (ii) `e(G) ≤ σ₂(blocks) − 2` [`main_ineq`
  route]. NB 85 graphs in `G_{9,3}` have NO valid `z`, but NONE admit a max-degree singleton config
  — the config graphs are precisely the Lemma-3-nice ones. [`guard_decide.py`]
- **Max-size is NOT needed.** `kp_caseB_impl` carries only `hmax`; both routes close from it.
- Informative (not required for the proof): the singleton is NEVER the unique bad part (always ≥2
  bad parts), and ≥2 `C`-vertices are always deletable. [`guard_profile.py`]

### Task 3 — CORRECT pinned argument (Route MI; mechanical, for a Lean runner)
Let `blocks := (List.ofFn fun i:Fin (r−1) => (D.filter (κ·=i)).card) ++ [n − D.card]` (exactly
`main_ineq`'s list), `c := n − D.card`, `σ₂ := sig2 blocks`, `t := (turanGraph n r).edgeFinset.card`.
Uses ONLY proven lemmas (`main_ineq`, `degree_le_of_part`, `colorable_of_C_indep`, `two_mul_turan`)
plus TWO new arithmetic lemmas (statements + numeric truth below).

**(0) Strengthen the c-guard split to `c ≥ 3`.** Change the outer `by_cases 2 ≤ n−D.card` so that
`n−D.card ≤ 2` ⇒ contra (currently only `≤ 1` is handled at line 2078). Proof: `hchi
(colorable_of_C_indep hr G x κ hproper hCindep)` where `hCindep : ∀ u∉D, ∀ v∉D, ¬Adj u v`: given
`Adj u v`, `u∉D`, `v∉D`, get `u≠x` (else `v∉Γx ⇒ ¬Adj x v`) and `v≠x`; then `{u,v} ⊆ (univ∖D)∖{x}`
so `2 ≤ (univ∖D).card − 1`, i.e. `3 ≤ n−D.card`, contra `≤ 2`. Subsumes the existing `c≤1` branch;
the surviving branch gives `hc3 : 3 ≤ c` in scope for the guard.

**(1) `main_ineq` (PROVEN).** `have hmain := main_ineq G x hmax κ hDindep` gives
`2*e(G) + Σ_{v∈D}(n − |D_{κv}| − deg v) ≤ 2*σ₂` (`hDindep` already in context). Every summand `≥ 0`
by `degree_le_of_part`.

**(2) dispatch on `hsing : ∃ i:Fin (r−1), (D.filter (κ·=i)).card = 1`.**

**(2a) SOME part `= 1` (SINGLETON `{w}`).** `Finset.card_eq_one` ⇒ `w`, `w∈D`, `κ w = i0`,
`|D_{i0}| = 1`. Then `defc(w) = n − 1 − deg w` and `deg w ≤ deg x = D.card = n − c`
(`hmax` + `card_neighborFinset_eq_degree`), so `c − 1 ≤ defc(w)`. As all summands `≥ 0` and `w∈D`,
`c − 1 ≤ Σdefc`, so with `hmain`: `2*e(G) + (c−1) ≤ 2*σ₂`. Close with **Lemma A** (`singleton_arith`):
> `blocks` has an entry `= 1`, last entry `c ≥ 3`, `sum = n`, `length = r`
> ⇒ `2*σ₂ + 2*kpSaving n r ≤ 2*t + (c − 1)`.
`omega [hmain, defc bound, singleton_arith]` ⇒ `e(G) + kpSaving n r ≤ t`. ✓

**(2b) NO part `= 1`** (so the small part `i0` has card `0`, EMPTY). `blocks` has a `0` entry;
`Σdefc ≥ 0` + `hmain` ⇒ `2*e(G) ≤ 2*σ₂`. Close with **Lemma B** (`empty_arith`):
> `blocks` has an entry `= 0`, last entry `c ≥ 3`, `sum = n`, `length = r`
> ⇒ `2*σ₂ + 2*kpSaving n r ≤ 2*t`.
`omega` ⇒ goal. ✓

**Lemmas A/B are numerically VERIFIED** — 0 violations over `2≤r≤8`, `r+3≤n≤25`, ALL block vectors
(`scratchpad/guard_arith.py` + doubled-form check). Both are TIGHT (slack 0 at `r=3,n=6,(1,2,3)`
and `r=4,n=7,(0,2,2,3)`), so BOTH the `−(c−1)` and the `c ≥ 3` hypothesis are essential. Proof
pattern (successor): identical to the existing `two_bad_aux`/`constr_le` — `two_mul_turan` to clear
the Turán `/(2r)`, then peel a NONZERO block and recurse to `caseA_slack` (this is how `two_bad_aux`
ITSELF is proven, NOT a call to it); the size-1 (resp. size-0) block and the `c` block ride along in
the tail, base case length 2 (`[1,c]` / `[0,c]`). Lemma A allows extra `0` entries too (verified), so
a config with BOTH a `0` and a `1` part routes through (2a).
DEAD END to skip: proving Lemma B as `two_bad_aux(nonzero parts) + (p_k(n)+min ≤ p_r(n))` FAILS —
the `+min` slack is too lossy (11 violations, e.g. `r=4,n=7,k=3`: `p_3(7)+2 = 17 > 16 = p_4(7)`).
The direct peel is necessary. (`scratchpad/guard_arith.py` final block has both checks.)

### Corrections to prior notes on THIS crux
- **Max-size NOT required.** Runner-13 REMAINING-GAP-1 ("This is exactly where KP invokes MAXIMALITY")
  and runner-14 VERDICT ("genuine research step; open closure for `W_C=∅`") BOTH over-estimated it.
  `c ≥ 3` + `main_ineq` close it directly; `BrouwerMax.lean` is unnecessary for the guard.
- **The empty-part `t_{r−1}(n)` Turán shortcut is FALSE** (runner-14 "empty-case Turán", line ~829;
  the `pr`-monotonicity idea at REMAINING-GAP-1 line ~659). `t_{r−1}(n) + kpSaving n r ≤ t_r(n)`
  FAILS in the `kpSaving=2` regime (`r=5,n=8`: `24+2 = 26 > 25 = t_5(8)`). The empty case needs
  Lemma B (`σ₂(blocks)` with ACTUAL sizes AND `c ≥ 3`), NOT the loose `e ≤ t_{r−1}(n)`.
- KP's `d_i ≥ 2` guard is a REAL case (arises `n ≥ r+5`), but resolved by one `main_ineq`, not Lemma 3.

## F6 DISCHARGE PROGRESS (2026-07-11, F6u — inequality (5) DONE sorry-free; kp_lemma3's hardest step)

**State: `kp_lemma3`'s STEP 6 (inequality (5), the acknowledged single hardest step) is now
formalised sorry-free** in `BrouwerInduction.lean` as three lemmas (axiom-clean
`[propext, Classical.choice, Quot.sound]`), placed just before `kp_lemma3`. Sorry count unchanged
(3) — `kp_lemma3` still `sorry` (STEPs 1–5,7 remain) — but the mathematically hard part is done.
Runner 13.

- **`fiber_card_le M (i≠j) u v : #{t ∈ ∏Mₕ | t i = u, t j = v} ≤ ∏_{h≠i,j} |M h|`.** The pinned-
  coordinate fiber embeds into `piFinset M'` (`M' i = {u}`, `M' j = {v}`, else `M h`);
  `Fintype.card_piFinset` + `mul_prod_erase` ×2 evaluate the product.
- **`prod_le_sum_bad M Adj (hbad : ∀ t ∈ ∏Mₕ, ∃ i j, i<j ∧ ¬Adj (t i)(t j)) : ∏|Mᵢ| ≤
  Σ_{i<j} ē_ij · ∏_{h≠i,j}|Mₕ|`.** The transversal covering: `hbad` (from `K_{r+1}`-freeness +
  `Y`-clique) covers `piFinset M` by `P.biUnion (BP p).biUnion (fiber)`; `card_biUnion_le` ×2 +
  `fiber_card_le`. `ē_ij = #((M i ×ˢ M j).filter ¬Adj)`.
- **`missing_edges_ge M (nonempty) Adj hbad ia ib (ia≠ib) (min a) (2nd-min b) :
  |M ia|·|M ib| ≤ Σ_{i<j} ē_ij`.** Cancels the common `Q = ∏_{h≠ia,ib}|Mₕ| > 0` and `m_a m_b > 0`
  (`Nat.le_of_mul_le_mul_left/right`); needs `m_a m_b ≤ m_i m_j` for every pair (3-case argument
  from the two-smallest hypotheses).
- **`transversal_has_bad_pair G hCF Y (clique, |Y|=l+1) (k+l+1=r+1) M (pairwise-disjoint,
  disjoint-from-Y, all-Mᵢ-adj-Y) : ∀ t ∈ ∏Mₕ, ∃ i<j, ¬Adj (t i)(t j)`.** The GRAPH side of STEP 6
  — supplies `missing_edges_ge`'s `hbad`. Proof: else `Y ∪ image t` is an `(l+1)+k = r+1`-clique
  (`t` injective from disjointness; `image t` disjoint from `Y`), contra `hCF`. So STEP 6 is now
  FULLY sorry-free (both the counting AND the freeness bridge); the successor wires `Y := {z}∪
  singletons`, `M i := (Nᵢ).filter (Γ⊇Y)`, `k := r−l`, `l := #singletons`.

**How `kp_lemma3` will call it (STEP 6 wiring, for the successor):** instantiate `Adj := G.Adj`,
`M := fun i => (Nᵢ).filter (Γ(·) ⊇ Y)` (the `Mᵢ`), `k := r − l` (number of big classes, `≥ 2` by
STEP 4). `hbad`: given a transversal `t`, `{z,y₁,…,y_l} ∪ {t i}` would be `K_{r+1}` (all `t i` adj
all of `Y`, `Y` a clique) unless some `t i, t j` non-adjacent ⇒ `no_Kr_plus_edge`/`hCF`. Then
`Σ_{i<j} ē_ij ≥ m₁m₂` feeds STEP 5's `e(G) ≤ σ₂(1^l,nvec) + l − Σ ē_ij + Σmᵢ` to give
`e(G) ≤ σ₂(1^l,nvec) − m₁m₂ + l + Σmᵢ`, then `lemma3_arith` (STEP 7). NB `missing_edges_ge`'s sum
is over ORDERED pairs `i<j` (`Fin k × Fin k`, `p.1<p.2`); STEP 5's `ē_ij` bookkeeping must match
that indexing (or convert to `Sym2`/unordered).

## F6 DISCHARGE PROGRESS (2026-07-11, F6y/F6z — kp_lemma3 FULLY sorry-free)

**State (runner 14, lean-f6g; committed `735b095` "F6z", builds on `ed605a2` "F6y"): `kp_lemma3`
is COMPLETELY PROVED, axiom-clean (`#print axioms kp_lemma3 = [propext, Classical.choice,
Quot.sound]`).** STEPs 1 (classes `Cᵢ=(univ.erase z).filter(κ'·=i)` + each non-empty via recolour),
2 (Y clique), 3 (`Mᵢ≠∅`), 4 (`l≤r−2 ⇒ k≥2`), 5 (edge-count, F6z below), 6 (transversal counting,
prior), 7 (`lemma3_arith` feed) are ALL sorry-free. Builds clean (`lake build
Lean617.BrouwerInduction`). **File sorries: 3 → 2** — `kp_caseB_impl` some-part≤1 [F6w/F6x other
runner; note its Lemma-3 singleton route is now UNBLOCKED since kp_lemma3 is done], `equality21`.

**F6z (STEP 5, the edge-count `hstep5`) — new sorry-free lemmas before `kp_lemma3`:**
- `sum_sym (g) (hsymm) : ∑ₐ∑_b g a b = ∑ₐ g a a + 2·∑_{a<b} g a b` (symmetric double-sum split;
  `sum_product'` + trichotomy filter partition + prod-swap reindex for the `>` part).
- `crossE_comm : crossE G A B = crossE G B A` (`crossE_eq_product` + `card_nbij'` swap).
- `edgeCountIn_bigs (D1) : e((univ:Fin k).biUnion N) = ∑_{a<b} crossE(Nₐ,N_b)` for pairwise-disjoint
  independent `N` (via `crossE_self` `= 2e`, crossE bilinearity over the biUnion, `sum_sym`, diag `=0`).
- `kp_lemma3_count`: the full KP edge-accounting given the interface (`V = Y ⊔ Bigs`, `M⊆N` all-adj-Y,
  `hNMmiss`). (A) `edgeCountIn_disjoint_union`; (B) `e(Y)≤C(l+1,2)`; (C) `crossE(Bigs,Y) ≤ Σ(mₐ+l·nₐ)`
  (split `N a` by `M a`); (D) per-pair `crossE(Nₐ,N_b)+ē_ab ≤ nₐn_b` (`M⊆N`, Adj/¬Adj disjoint) + D1 +
  the `σ₂=Σ_{a<b}nₐn_b` identity (`sum_sym` + `two_mul_sig2`); (E) arith identity (subtraction-free,
  `two_mul_sig2` on both lists + `2·C(l+1,2)=l²+l`).
- `kp_lemma3`'s `hstep5` calls `kp_lemma3_count` with in-context interface derivations
  (`hNdisj`/`hNindep` from `hCdisj`/`hCindep`+`bigEmb`; `hpart : univ = Y ∪ Bigs`; `hYBdisj`; `hNMmiss`).

**New sorry-free reusable lemmas (placed just before `kp_lemma3`):**
- `recolor_z G z κ' hproper' c hc` : recolour `z→c` when no `z`-neighbour has colour `c` ⇒ `Colorable r`.
- `recolor_zb … i j hij hbz hbi hzj` : merge-recolour `b→i`, `z→j` (`i≠j`) ⇒ `Colorable r`.
  (STEP 2's Y-clique = 2× `recolor_z` + 1× `recolor_zb`; STEP 3's `Mᵢ≠∅` is a bespoke `l+1`-slot
  f-split colouring, inline.)
- `kp_lemma3_finish {r n l k} … (hcount) : e + kpSaving n r ≤ t_r(n)` : STEP 7 — from the `Fin k`
  class data (`nn,mm`, two smallest-`m` `ia,ib`) + the STEP 5+6 output `hcount`, pull `ia,ib` to
  the front and apply `lemma3_arith`. sig2 matched via `two_mul_sig2` (sum + sqsum), not list perm.
- `sqsum_replicate_one`, `sum_replicate_one` (list helpers).

**kp_lemma3 internal scaffold (all sorry-free):** `Big/Sing` split of `Fin r`; `bigEmb : Fin k ↪o
Fin r` (`Big.orderEmbOfFin`); `N a = C (bigEmb a)`, `Y = insert z (Sing.biUnion C)`, `M a =
(N a).filter (∀ y∈Y, Adj · y)`; `hlk : l+k=r`, `hn_eq : n = 1+l+Σ nn`, `hYcard : |Y|=l+1`
(sorry-free); two-smallest `ia,ib` via `Finset.exists_min_image`; STEP 6 via `transversal_has_bad_pair`
+ `missing_edges_ge`; STEP 7 via `kp_lemma3_finish`.

**REMAINING — STEP 5 (`hstep5`, the ONLY kp_lemma3 gap) ROADMAP:** prove
`e(G) + Σ_{p:p.1<p.2} ((M p.1 ×ˢ M p.2).filter ¬Adj).card ≤ sig2(1^l ++ ofFn (N·).card) + l + Σ_a |M a|`.
Tools all present: `crossE`, `crossE_self` (`= 2·e`), `crossE_union_right`, `crossE_eq_product`,
`edgeCountIn_disjoint_union` (MH2Proof); `edgeCountIn_le_choose_two` (Counting). Route:
- (A) partition `univ = Y ⊔ Bigs`, `Bigs = (univ:Finset (Fin k)).biUnion N`; `edgeCountIn_disjoint_union`
  ⇒ `e(G) = e(Y) + crossE(Bigs,Y) + e(Bigs)`.
- (B) `e(Y) ≤ (l+1).choose 2` (`edgeCountIn_le_choose_two` + `hYcard`).
- (C) `crossE(Bigs,Y) ≤ Σ_a (|M a| + l·|N a|)` : split `Σ_{u∈Bigs}` by `N a` (`Finset.sum_biUnion`,
  N disjoint); `u∈M a ⇒ |Y.filter(Adj u)| = |Y| = l+1`; `u∉M a ⇒ misses ≥1 of Y ⇒ ≤ l`.
- (D) `e(Bigs) + Σ_p miss(p) ≤ σ₂(nvec)` : `e(Bigs) = Σ_{a<b} crossE(N a,N b)` (from `crossE_self` on
  `Bigs` + crossE bilinearity over the `N`-biUnion + symmetric-sum split of `Fin k × Fin k` into `</=/>`;
  diagonal `crossE(N a,N a)=0` by `N a` indep, off-diag pairs collapse via crossE symmetry); then
  per-pair `crossE(N a,N b) + miss(a,b) ≤ n_a n_b` (`M⊆N`, Adj/¬Adj disjoint subsets of `N a ×ˢ N b`);
  and `Σ_{a<b} n_a n_b = sig2(ofFn (N·).card)` (`two_mul_sig2` + double-sum expansion).
- (E) combine with the verified identity `C(l+1,2)+σ₂(nvec)+l·Σn = σ₂(1^l,nvec)+l`.
Est. ~130–170 lines; crux is (D)'s `crossE`-symmetric-sum decomposition of `e(Bigs)`. Best developed
as a standalone counting lemma (rich `N/M/Y` interface) so only one line of `kp_lemma3` changes.

## equality21 — TRANSPORT REDUCTION DONE (2026-07-12, F6z, lean-f6g): reduced to ONE research sorry

> CONSOLIDATED: for orientation and how this unifies with the guard, see **"KP-EQUALITY CORE"**
> near the top. This section is the detailed record of the transport reduction + 3-variant finding.


**`Lean617/Equality21.lean` (committed `62636b8`, standalone) reduces `equality21` to a SINGLE
honestly-stated research sorry `exists_AB21_iso`, with the ENTIRE transport VERIFIED sorry-free &
axiom-clean (`[propext, Classical.choice, Quot.sound]`):**
- `AB21 (H)` — the A/B-structure predicate (`equality21`'s conclusion, factored out).
- `equality21_reduce` — `e(F)=37 ⇒ J=Fᶜ` is `K₆`-free, `α≤4`, `e(J)=173` (extremal). VERIFIED.
- `edgeCountIn_iso (F H σ) (hiso) (S) : edgeCountIn F S = edgeCountIn H (S.image σ)` — reusable. VERIFIED.
- `equality21_transport (F H σ) (hiso : F ≅ H) (hH : AB21 H) : AB21 F` — VARIANT-AGNOSTIC transport. VERIFIED.
- `AB21_kpG_compl : AB21 kpGᶜ` — from `kpG_compl_AB_structure` (the `|A*|=2` witness).
- `exists_AB21_iso (F) (α≤5, K₅-free, e=37) : ∃ H σ, (F ≅ H) ∧ AB21 H` — **the ONLY sorry** = KP Thm 4 equality.
- `equality21_final = equality21_transport ∘ exists_AB21_iso : AB21 F` = the `brouwerFacts.equality21` field.

**KEY finding: the (5,21) extremal graph is NOT unique** — `G((4,4,4,4,4))` has THREE non-isomorphic
variants (`|A*|∈{1,2,3}`, `deg x = 13+|A*| ∈ {14,15,16}`); `kpG` is only the `|A*|=2` one. The
variant-agnostic `equality21_transport` (takes any `H` + `AB21 H`) handles all 3, so `exists_AB21_iso`
is the clean remaining core. To finish `exists_AB21_iso`: `equality21_reduce` gives `J` extremal;
then KP Thm 4 (`J` is a construction `G((4,4,4,4,4))`) + Lemma 5 (unique opt seq) pin `J ≅ kpGᵢ` for
one of the 3 variants; provide `AB21 kpGᵢᶜ` (`AB21_kpG_compl` for `i=2`; two more cheap `native_decide`s
for `i=1,3` once `kpG₁,kpG₃` are defined). **The genuinely-hard part is `J` being a construction** — the
same page-long KP equality analysis that resists the guard. FINISH LINE: wire `brouwerFacts.equality21
:= equality21_final` (needs `BrouwerInduction` to import `Equality21`, or move `brouwerFacts` later).

### (Original scoping, 2026-07-11:)

`equality21 : ∀ F : SimpleGraph (Fin 21), α(F)≤5 → F.CliqueFree 5 → e(F)=37 → ∃ A B, <A/B structure>`.
This is the KP **Theorem 4 equality classification** (∀-F uniqueness) at `(5,21)` — genuinely
research-scale (KP paper pp. 3–4, the `~1`-page equality analysis + Lemma 5), NOT a quick close.
Recommended decomposition (the existence half is ALREADY done in `KPConstruction.lean`):
1. **Reduce to the complement.** `J := Fᶜ`. `e(F)=37 ⇒ e(J) = C(21,2) − 37 = 210 − 37 = 173 = p₅(21)`
   (`edgeCountIn_add_compl`, `(21).choose 2 = 210`). `J` is `K₆`-free (`compl_cliqueFree_six_of_alphaAtMost_five`)
   and `α(J)≤4` (`alphaAtMost_compl_four_of_cliqueFree_five`). So `J ∈ 𝒢₂₁,₅` is **extremal** (attains 173).
2. **[HARD, the research core] `J ≅ kpG`.** Every extremal `J` is isomorphic to the specific construction
   `kpG = G((4,4,4,4,4))` (`KPConstruction.lean`): `∃ σ : Fin 21 ≃ Fin 21, ∀ a b, J.Adj a b ↔ kpG.Adj (σ a) (σ b)`.
   This is KP Thm 4 equality (traces equality through the whole `kp_upper` induction: each `dᵢ=nᵢ` for `i≥3`,
   `m₁=1`, equality in (5) forces all missing edges into one `G[M₁,Mᵢ]`, `m₂≠n₂`, every `V∖Y` vertex has ≤1
   Y-non-neighbour, …) + Lemma 5 (the optimal seq for `(5,21)` is `(4,4,4,4,4)`, unique up to the `A*∈{1,2,3}`
   isomorphism class). Needs a genuine equality-tracking rewrite of `kp_upper` — do NOT expect a short proof.
3. **Transport.** `KPConstruction.kpG_compl_AB_structure` already PROVES the `∃ A B <structure>` for `F = kpGᶜ`
   (`A={4,5,6,7,20}`, `B={0,1,2,3}`, `native_decide`-backed). Given the iso `σ` from step 2, `F = J ᶜ ≅ kpGᶜ`,
   so set `A' = A.map σ⁻¹`, `B' = B.map σ⁻¹` and push the (dis)equalities/counts through `σ` (a graph iso
   preserves `Adj`, `card`, `edgeCountIn`). Mechanical (~60–100 lines) once step 2 exists.
So `equality21` is essentially ONE hard sub-lemma (step 2, `J ≅ kpG`) + bookkeeping. `kpG_edgeCount` (=173),
`kpG_cliqueFree` (K₆-free), `kpG_alpha` (α≤4), `kpG_compl_AB_structure` are the sorry-free anchors it cites.
NB the KPConstruction anchors use `native_decide`, so `equality21` (hence `erdos_617_r5`) will pick up the
native-decide axiom set — update `tools/axiom_allowlist.txt` + RELEASE.md when it lands.

## EQUALITY21 — analysis (2026-07-12, math-analysis runner; NO Lean edits)

**VERDICT.** `exists_AB21_iso` is TRUE and IS the KP Theorem-4 equality classification at `(5,21)` —
a genuine **multi-session research formalization** (the single largest remaining piece; there is NO
short certificate — see feasibility). Two FACTUAL CORRECTIONS to the record above (both verified by
nauty `labelg` canonical forms + full enumeration): **(1) there are exactly TWO iso classes of extremal
graph, not three** — `|A*|=1 ≅ |A*|=3` (they share degree sequence `(14,16⁸,17¹²)` and canonical form;
`x` and `y` swap roles, `A ↔ Nₛ∖A`). `|A*|=2` is the other class (degseq `(15²,16⁷,17¹²)`). **(2) Lemma 5
at `(5,21)` has THREE optimal sequences, not one** — `{(3,3,4,5,5),(3,4,4,4,5),(4,4,4,4,4)}`, all giving
`e=173`; `(4,4,4,4,4)` is singled out NOT by edge-count but by the **`α≤4` hypothesis** (the other two have
a size-5 part ⇒ `α≥5`). The KP-EQUALITY-CORE "guard = |A*|=1" fusion conjecture is MOOT (the guard closes
independently via Route MI — see SINGLETON GUARD analysis).

### Task 1 — KP's equality argument, pinned (Thm 4 "cases of equality" + Lemma 5)
KP re-runs the bound proof tracking tightness. Two branches from the max-degree vertex `x`, `D=Γx`,
`H=symmG`, `C=V∖D`:
- **`G[D]` not `(r−1)`-partite:** by induction `G[D]≅G(m)`; *"each vertex `y∈D` is connected in `G` to
  everything in `C`: otherwise `d_G(y)<d_H(y)` and `e(G)<e(H)`, a contradiction to the maximality of `G`.
  It follows that `G[C]` is the empty graph and `G` is as desired."* — i.e. equality in `d_G≤d_H` forces
  `G[C]=∅` and `D–C` complete.
- **`G[D]` is `(r−1)`-partite:** *"there is a vertex `y` … such that `G−y` is `(r−1)`-partite. Let the parts
  of `V'=V∖{y}` be `{y₁},…,{y_l},N₁,…,N_{r−l}`. Of all possible choices of `y` and an `(r−1)`-partition of
  `V'`, take one which minimizes `l`."* Then the forced structure (equality in Lemma-3's (5) and (6)):
  *"We must have `mᵢ=nᵢ` for `i≥3` and `m₁=1`. As we have equality in (5), all missing edges in `G[Nᵢ,Nⱼ]`
  lie between `M₁` and `M₂∪…∪M_k` … In fact, all missing edges lie inside just one `G[M₁,Mᵢ]` for otherwise
  starting with `Y∪M₁` we can greedily add `zᵢ∈Mᵢ` … to get a `K_{r+1}`."* Then *"The case `m₂=n₂` is
  impossible … `every vertex of V∖Y` has at most one non-neighbor in `Y`"* (equality in (6)), *"It is
  impossible that some two vertices `w,z∈Y` have degree `<n−1` … `n₁=n₂=2` … `G[N₁∪N₂∪{w,z}]` … is
  3-colorable ⇒ χ(G)≤r, contradiction."* Conclusion: *"all missing edges in `G[Y,V∖Y]` are between
  `(N₁∖M₁)∪(N₂∖M₂)` and some `z∈Y` … in order to maximize `e(G)` we must have that `n₁,n₂` are the two
  smallest `nᵢ`, which is precisely what our construction says."*
- **Lemma 5** (which sequences are optimal): for `r≤(n−1)/2` (the `(5,21)` regime, `5≤10`), the optimal
  sequences are exactly those satisfying `n₁≥2 (7)`, `n₂≤n₁+1 (8)`, `n_r≤n₁+2 (9)`, `n_r≤n₃+1 (10)`; the
  Remark: *"there are from one to three different sequences"* (here THREE — matches numerics).

### Task 2 — numerics (scripts `scratchpad/eq21_*.py`; nauty geng+labelg)
- **Lemma 5 at `(5,21)`** [`eq21_lemma5.py`]: exactly 3 optimal sequences `(3,3,4,5,5),(3,4,4,4,5),(4,4,4,4,4)`,
  each `e(G(seq))=173`. Confirms KP's "1–3 sequences" Remark.
- **`α≤4` selects `(4,4,4,4,4)` uniquely** [`eq21_variants.py`]: the other two optimal seqs build `K₆`-free
  173-edge graphs with `α≥5` (a size-5 part is an independent 5-set), so they are NOT extremal for the `J`
  problem. Clean reason: `Σ=20` into 5 parts `≤4` forces ALL parts `=4` (`5·4=20`), and only all-parts-`≤4`
  gives `α≤4`. So the `α≤4` hypothesis short-circuits KP's general Lemma-5 optimisation.
- **`(4,4,4,4,4)` variants** [`eq21_variants.py`,`eq21_validate.py`]: `|A|∈{1,2,3}` all give `K₆`-free, `α=4`,
  `e=173`, and all have `AB21` on the complement. Exactly **2 iso classes** (`|A|=1≅|A|=3`; `|A|=2` distinct),
  both `AB21`. So `exists_AB21_iso`'s witness `H` ranges over **2** classes, both already `AB21` (one is
  `kpGᶜ`, `|A*|=2`; the other, `|A*|=1`, needs its own `kpG₁` + one `native_decide` for `AB21 kpG₁ᶜ`).
- **Classification METHOD validated** [`eq21_validate.py`]: max-size `𝒢_{n,r}` = the `G(opt-seq)` constructions
  EXACTLY (canonical-form match) for `(7,3),(8,3),(9,3),(8,4),(9,4)` — including the true `α=r−1` analog
  `(7,3)` (`n=r²−r+1`) and the multi-class case `(9,3)` (2 classes, matched). Strong evidence KP Thm-4
  equality (extremal ⇒ construction) is correct where enumeration is feasible. `n=21` itself is FAR out of
  brute-force reach (no `geng` at 21).
- **F7 needs the full `AB21`** (`MH2Proof.lean:400`): it destructures `A=K₅−e` at the specific non-adjacent
  pair, `B=K₄`, and the 19-edge count for its colour-counting `§3` contradiction. NOT weakenable.

### Task 3 — feasibility + decomposition
**Honest assessment: multi-session research formalization, ~1500–3000 Lean lines** (comparable to the whole
bound proof `kp_upper`+`kp_lemma3`, which it re-traces under equality). No shortcut:
- **native_decide over all graphs** — infeasible (`2^210`).
- **SAT/UNSAT certificate** for "∃ `K₅`-free, `α≤5`, 37-edge `F` with `¬AB21`" — the `¬AB21` encoding is a
  `∀` over `C(21,5)·C(16,4)≈3.7·10⁷` subset-pairs; instance + certificate almost certainly intractable, and
  it is the WRONG shape for the repo's per-primitive LRAT pattern. NOT recommended.
- **The real path = formalise KP's equality trace** (Approach A), specialised by `α≤4`:
  D1. **Symmetrisation equality** (`e(J)=e(H)=173`): forces `Σ_{v∈D} defc(v)=0` in `main_ineq` ⇒ every `D`-vertex
      adjacent to all of `C` and `G[C]` empty ⇒ `J` = join of `G[D]` with independent `C`. (Reuses `main_ineq`,
      `symmG_edgeCount_eq`; the equality direction of the already-proven pieces.)
  D2. **`G[D]` is 4-partite with the balanced partition**: the Case-B equality; with `α(J)≤4` and the join
      structure, the `≥2`-bad / good-witness analysis collapses (`Σdefc=0` ⇒ all parts "good"), forcing the
      partition. `α≤4` ⇒ all 5 blocks (4 `D`-parts + `C`) have size `≤4`, summing to 21 ⇒ sizes `(4,4,4,4,4)`
      with one block being `C`. **This is the crux and needs the equality-tracking rewrite.**
  D3. **The `x`-vertex freedom** (`A⊂Nₛ` proper) ⇒ `J ≅` one of the **2** constructions.
  D4. **Transport** (DONE: `equality21_transport`) ⇒ `AB21 F`. Add `kpG₁` (the `|A*|=1` graph) + `AB21 kpG₁ᶜ`
      (`native_decide`) so the witness set is complete.
  The α≤4 specialisation genuinely shrinks the work vs KP's general Lemma-5 optimisation (D2 replaces it), but
  D1–D2 still require re-examining the induction's equality cases — the multi-session core.

### Corrections to the record (apply when convenient; not done here — analysis only)
- `Equality21.lean:92–94` comment and this file's KP-EQUALITY-CORE + transport sections say "THREE
  non-isomorphic variants": it is **TWO** (`|A*|=1≅|A*|=3`). `equality21_transport` is variant-agnostic so
  the code is unaffected, but the witness enumeration is 2 (`kpGᶜ` + one more), not 3.
- "Lemma 5 (unique opt seq)" / "the optimal seq is `(4,4,4,4,4)`, unique": there are **3 optimal sequences**;
  `α≤4` (not optimality) selects `(4,4,4,4,4)`. The Lean proof should invoke `α≤4 ⇒ all parts ≤4 ⇒ (4,4,4,4,4)`,
  which is cleaner than KP's general Lemma 5.

## Design notes (F3, 2026-07-10)

`primFacts : PrimFacts` is proved sorry-free in `Lean617/Primitives.lean` (chain:
`PrimEncoding → PrimBridge → PrimMBridge → Primitives`). Discharges all four PrimFacts fields.

**Route:** each primitive is a CNF whose UNSAT is kernel-checked by `Std.Tactic.BVDecide`'s
`verifyCert`/`verifyCert_correct` (public, sound: `verifyCert cnf cert = true → cnf.Unsat`),
reflected by `native_decide`. The CNF is defined in Lean as `CNF Nat` data (`Erdos617F3`
namespace); a `assign`/`assignM` bridge shows any graph with the properties yields a satisfying
assignment, so `cnf.Unsat` ⇒ the graph statement (`nonex_of_unsat`, `M_of_unsat`).

**Encoding** (`PrimEncoding`): edge `{a,b}` (a<b) ↦ variable `edgeVarL [a,b] = a*n+b`. Families:
`alphaClauses` (α≤2: every 3-set has an edge), `omegaClauses` (ω≤4: every 5-set omits an edge),
`capClauses` (cap-11: every 6-set, every 12-of-15 pairs omits one), and — for M9/M10 — a Sinz
sequential-counter `cardClauses n k` ("≤k edges", `List.range'`-generated, auxiliary
`auxVar = n²+i·k+j`). `nonexCNF n = alpha++cap`; `MCNF n k = alpha++omega++cap++card`.

**Bridge** (`PrimBridge`/`PrimMBridge`): `assign G v = G.Adj (v/n%n) (v%n)`; for M, `assignM` sets
counter vars to partial-sum bits `sbit`. Per-family satisfaction (`alpha/omega/cap_clause_sat`,
`cardA..E_sat`); the cap/edge-count injections reuse a `s2 : pair → Sym2` nodup lemma
(`pairsOf_map_s2_nodup`). `M_of_unsat` uses `edgeCountIn G univ ≤ k` (contrapositive of ≥k+1).

**Pipeline** (documented in [[f3-lrat-pipeline]]; tooling in `lean617_f3/`): `emitDimacs cnf`
(streaming DIMACS == `Std.Sat.CNF.dimacs`, `+1` shift) → `cadical f.cnf f.lrat --lrat
--binary=false --quiet --shrink=0 --unsat --inprocessing=false` → `trimtool` (`LRAT.trim` +
`lratProofToString`) → the trimmed `.lrat`, embedded by `include_str` and `native_decide`d.

**TWO non-obvious LRAT requirements** (both took real debugging):
1. `--inprocessing=false` — else cadical introduces FRESH variables (gate/BVA) beyond
   `cnf.numLiterals`; `convertLRAT` sizes to `numLiterals+1`, so those clause-actions convert to
   `none` and are SILENTLY SKIPPED → formula diverges → `rupFailure`. (Padding can't fix it.)
2. `LRAT.trim` — the checker ignores stated ids and appends sequentially, so gapped ids
   (drat-trim `-L`, or cadical skips) break the id↔index lockstep. Trim renumbers consecutively.
   (This is exactly what bv_decide's `LratCert.load` does.)

**DEVIATION from the original assets:** the seeded `data/sat/prim_*.lrat` (drat-trim `-L`, gapped
ids) are NOT usable by Lean's checker; F3 re-solves with cadical+`--inprocessing=false`+trim. New
certs (`Lean617/certs/*.lrat`, git-ignored, ~340MB/454MB/2MB/19MB) are the ground truth for F3.

**AXIOM FOOTPRINT:** `primFacts` carries `Lean.ofReduceBool` (via `native_decide`) in addition to
propext/Classical.choice/Quot.sound. This is UNAVOIDABLE for machine-scale SAT reflection and is
exactly what `bv_decide` produces; F5's `PrimFacts`-conditional L-table stays `native_decide`-free
itself but the final assembly inherits `ofReduceBool` once `primFacts` is plugged in.

## Design notes (F8, 2026-07-10)

`Lean617/MMProof.lean` — assembly of `lemma_MM_of (pf : PrimFacts) : MM` (informal:
review_queue/mm-gpt56-candidate.md, incl. the adopted r=7 repair). CONDITIONAL on
`PrimFacts` (F3) only; `#print axioms`-relevant fact — it does **not** use `BrouwerFacts`
(§2 uses the plain-Turán/ℓ floors + F5 L-lemmas). Full lib builds clean; 4 sorries left.

**Verified (sorry-free) building blocks:**
- §0: `IsCliqueOn`, `edgeCountIn_eq_choose_of_clique`, `edgeCountIn_insert_ge_mm`,
  `indeg_clique5_le_one` (cap-11 ⇒ ≤1 neighbour into any K₅), `not_isCliqueOn_of_cliqueFree`,
  transport `alphaAtMost_comap_mm`, `cliqueFree_comap_of_no_clique`.
- §2 machinery: `turan3_general_mm` (α≤3 complement-Turán), `ell` table (vector (4)),
  `ell_le_fin`/`ell_le_edgeCountIn`, `alpha_W_gen`, `affineBound_20_mm`, `A20` (20-vtx
  α≤4 K₅-free cap-11 ⇒ e≥50 = informal m≥50), `Mfloor_le_edgeCountIn` (α≤2 subset floor).
- §1 peeling: `one_peel`, `peel_list`, `peel_alpha_bound` (its α(H)≤4 contradiction).
- Edge budget: `crossCount`, `card_cross_eq_crossCount` (cross-edge bijection),
  `edgeCountIn_univ_split` (e(G)=e(H)+e(T)+e(T,H)).
- §2 counting: `sum_U_counting` (the (9) ordered-non-edge count `c·(20−2s)≤8·crossCount`;
  `|A|≤2·e(G[T])` via a 2-to-1 fibre bound).
- Main `lemma_MM_of`: the by_cases {0,1,2,4} split; §2 K₅-free case (`section2_free`)
  discharges e(H)≥53 (c=3, ℓ18) and e(H)∈{51,52} (c=4, ℓ17) via `nonedge_U_ge`+counting.
- §4/§5 entry floors: `edge_R_ge_38` (R=15,α≤3,e≥L15=38), `edge_B_ge_25` (B=10,α≤2,e≥M10=25).

**§2 m=50 DONE (F8c, sorry-free).** New reusable infra now in MMProof.lean (before
`section2_free`): `edgeCountIn_insert_eq` (insert edge-count equality),
`edgeCountIn_union_disjoint_eq` (3-way disjoint split, induction on B),
`sum_adj_filter_eq_two_mul` (set handshake `∑_{u∈U}d_U(u)=2e(U)`), `deltaH_ge_three`
(δ(H)≥3 via `d+ℓ(19−d)≥55>50`), `no_four_set_alpha3` (a 4-set U⊆H with α(H∖U)≤3 gives
e(H)≥ℓ(16)+6=52>50 via the subset handshake `incident(U)=Σd_H(u)−e(H[U])≥12−6`),
`nonedge_residual_alpha3` (α(H−U_{tt'})≤3). Endgame: every |U_{tt'}|≥5 (else the 4-set
is U_{tt'} itself), then `sum_U_counting` c=5 ⇒ 5r≤4x≤4r ⇒ omega.

**§3 four-K₅ DONE (F8d, sorry-free).** New reusable helpers in MMProof.lean before
`section3_four`: `card_filter_not_ge`, `saturate_contra` (the elementary transversal
fact, contrapositive: matchings + no independent transversal ⇒ every part-vertex has a
neighbour in each other part), `no_indep_six` (α≤5 ⇒ no 6 pairwise-distinct nonadjacent
vertices), `cross_match` (K₅ in-degree ≤1 transported to Aᵢ⊆Qᵢ). `section3_four`: Q4 =
leftover clique (peel k=3), a non-edge tt′, Aᵢ=Qᵢ∖N(t,t′) (|Aᵢ|≥3), the 6 saturations
(`doSat`) ⇒ each cross ≥3 ⇒ e(H)≥58 via 3 disjoint splits ⇒ s+x≤2 ⇒ an independent
triple P⊆T (Mfloor 5=4) ⇒ greedy transversal q₁q₂q₃ (forbidden-by-P ≤ crossCount ≤2) ⇒
`no_indep_six`.

**§5 ASSEMBLED (F8e, 2026-07-10) — `section5_two` down to ONE sorry (`all_hit`).**
All r-branches done: r=5,6 (2 disjoint non-edges ⇒ D≥12), r=8,9 (Hamilton C₅ ⇒ 2D≥30),
r=10 (all dᵢ=3, five disjoint 3-sets in a 10-set), r=7 (weight vector (0,0,0,6,6) forces a
0-degree vertex in a non-edge ⇒ `collapse_of_zero`), r=4 (star: zero-leaf ⇒ collapse; else
the (28)–(32) `sec5_star_endgame` — 5-regular B, e(B[Z])=e(B[C])=6, cap-11 finish). New
sorry-free infra in MMProof.lean: `nonex11_transport`, `sec5_Bt_clique_false`,
`sec5_hit_union_ge`, `sec5_D_le`, `sec5_eB_D_le`, `edgeCount_five`, `s_expand`,
`toNat_decide'`, `twoDisjoint`/`fiveCycle`/`starOrDisjoint` (kernel-`decide` finite facts,
Bool-expr form + `or_assoc`/`and_assoc` rcases normalisation), `deg_split`, `cross_symm`,
`sec5_star_endgame`. Inside `section5_two`: vertex extraction, `hdsum`/`hunioncard` (via
`all_hit`), `close2`/`disjClose`/`cycClose`, `collapse_of_zero`, the `s∈{0..6}` split,
`sec5_r4_star`.

**STUCK-LIST: CLEARED — both remaining sorries eliminated (2026-07-10).**

**F8g — `all_hit` DONE (`section5_two` sorry-free).** The §5 (22)–(24) ρ-counting via two
new lemmas: `sec5_unhit_core` (an independent 4-set disjoint from two disjoint 5-cliques
forces each vertex a neighbour in each `Q_ℓ` and a `Q₁`–`Q₂` edge — the missed-vertex
analysis: `|M_ℓ|=1` via `indeg_clique5_le_one`+`no_indep_six`) and `sec5_all_hit` (the
global count). Realised `p`/`min p 5` interchangeable given `hcaseb`, so the count uses
plain `p`; `CB2` carried as an ordered-pair count bounded by `2r` and `a(a-1)`; final
arithmetic omega-closed after `interval_cases` on `ρ`; `ρ=5 ⇒ r=10,D=0,s=0 ⇒` independent
6-set. Handshake uses the offdiag-8D route (`Fintype.sum_prod_type` + `show` for the
`(a,b).1` projections).

**F8h — `section4_one` DONE (MMProof sorry-free).** New reusable helpers before
`section4_one`: `indep5_missedQ_false`, `exists_missed_in_clique5`, `cover5_le`,
`cover_3plus2_le`, `offdiag_prod_card`, `sum_offdiag_fst`/`_snd`, and `sec4_elim` (the (16)
elimination as `interval_cases a <;> interval_cases p <;> omega`, with `cb`/`hcbaa : cb+a≤a*a`
passed as data — omega does NOT handle `min`, so all `min`s were removed from the derivation).
Body: budget (13) [reuses the §5 `crossCount`/`edgeCountIn_univ_split` pattern]; per-edge
(14) `hcasea`/(15) `hcaseb` [residual α≤2 via `indep5_missedQ_false`+`nonex11_transport`, the
`hcaseb` P-removal via a `0<d_Q` filter]; weighted count `10r ≤ 8D + p·CB2` (`Finset.card_filter`
for the indicator sum, `sum_offdiag_fst/snd` for 8D); `sec4_elim` ⇒ survivor disjunction.
Dispatch: §4.1 (`p+a≤1`) via `starOrDisjoint`/`twoDisjoint`/`fiveCycle` (two-disjoint ⇒ D≥10
⇒ s≤2 ⇒ 5-cycle 2D≥25 contra) + the `hstarcase` star endgame (`X=R+t_c`, α≤3 via
`α(R−N_R(c))≤2`, e(X)≤44; K₅-free ⇒ `ell 16=46` contra, K₅-through-`t_c` ⇒ 11-vtx α≤2 set ⇒
`nonex11_transport`); (4,5,10) pigeonhole (≤1 zero-degree vertex ⇒ D≥4>3); §4.2 fixed-pair
(13-vtx triple `S` via `nonex11`, `M=Q∖N_Q(S)` with `|M|=2`, `hMforce` the 6-set forcing,
`F` bipartite between the two colour classes ⇒ `e(F)≤6<8≤r` via `A1×A2 ∪ A2×A1` and a
`x+y≤5 ⇒ xy≤6` check).

**Lean gotchas hit this session (for successors):** (i) `omega` has NO `min`/`max` support —
strip them and pass the products/bounds as separate hypotheses/`interval_cases`. (ii) `h ▸ e`
often fails with "expected result type of cast is [blank]" for `∈`/`Adj` casts — use
`by rw [h]/[← h]; exact …` or `by rintro rfl; exact …` instead. (iii) `·` bullets do NOT parse
inside an inline `(by …)` term or after `;` on one line — use `exacts […]` or a single
`<;> first | …`. (iv) `rcases hp with rfl` on `p = x` may eliminate the *vertex* `x` (breaking
later refs) — use `obtain hpe|… := hp` then `rw [hpe, hqe]` on the goal (no subst). (v) after
`Fintype.sum_prod_type`, reduce `(a,b).1/.2` with a `show`, not `dsimp only`. (vi) `Finset.card_sdiff`
is `#(s\t)=#s-#(s∩t)` (no subset arg) — use `Finset.card_sdiff_of_subset` + `omega`.

**Verified §5 scaffold (F8d session; compiles, not yet merged — recreate in the
`section5_two` body).** These foundational facts build cleanly and are the starting
point for §5; the successor should re-derive them then attack the case analysis.
- `edgeH_ge_45`: `e(H) ≥ 45` from `e(Q1)+e(Q2)+e(B) ≤ e(H)` (two `edgeCountIn_add_le_union_disjoint`)
  + `e(Qᵢ)=10` + `e(B)≥25` (`edge_B_ge_25`). [Note: the informal `m=45+b+c` EQUALITY needs
  `edgeCountIn_union_disjoint_eq` twice with the cross terms = `c`; the `≥45` inequality
  above is all the budget needs — `D ≤ crossCount ≤ 5+r` follows from `e(H)≥45` + `he60`.]
- `α(B) ≤ 2`: `peel_alpha_bound ctx [Q1,Q2]` (verbatim the `edge_B_ge_25` internal, k=2).
- `crossCount G T ≤ 5 + (10 − s)`: from `edgeCountIn_univ_split` + `e(H)≥45` + `ctx.he60`.
- **KEY reduction for the hitting dichotomy** (avoids re-deriving the informal's "hit" def):
  for an F-edge `{t,t'}` (t,t'∈T, ¬Adj), if `dₜ+dₜ' ≤ 5` then `|B∖(Zₜ∪Zₜ')| ≥ 5`, and this
  α≤2 subset of B is NOT a clique (else K₅ in B, contra `hBfree`/ω(B)≤4), so it has a
  nonedge `{u,v}` ⇒ `{t,t',u,v}` INDEPENDENT 4-set. Missed sets `Mℓ = Qℓ ∖ N({t,t',u,v})`
  have `|Mℓ|≥1` (each of the 4 has ≤1 nbr in Qℓ by `indeg_clique5_le_one`, so ≤4 hit).
  For NO independent 6-set, every `w₁∈M₁, w₂∈M₂` must be adjacent; but Q1–Q2 is a matching
  (indeg ≤1), so `|M₁|=|M₂|=1` and the two missed vertices are the matched pair — this is
  the informal's forced "unhit structure" (22), derived cleanly via `no_indep_six`. So the
  successor gets: **`dₜ+dₜ'≥6` OR the unhit-structure**; the ρ-counting (24) then gives h=0.

MERGE dedup with F7: renamed 4 helpers (`alphaAtMost_comap_mm`, `edgeCountIn_insert_ge_mm`,
`turan3_general_mm`, `affineBound_20_mm`) — F7's `LTableExt.turan3_general` is identical,
its `affineBound_20` differs (α≤4 range `9≤d`); F8's `A20` = F7's `L20` up to that.

## Ground rules

- The informal proofs are FROZEN references (review_queue/*.md as accepted+repaired);
  formalization must not silently change the mathematics — discrepancies discovered
  during formalization go to review_queue as amendments.
- Compile-iterate loop belongs to subagents/codex; this ledger + git are the interface.
  Each F-item lands as its own commit ("F2: chain deduction, sorry-free").
- Statement fidelity (F1) reviewed against the upstream Lean statement TEXT (papers/
  ergy99.md §8) before anything else — a wrong statement poisons everything.
- Escape hatches if F6 proves too hard: (a) formalize only the three instantiations
  (r=5, n∈{15,16,21}) of Brouwer's bound rather than the general theorem — still
  nontrivial but concrete; (b) re-prove those instances by SAT-certificate at the
  graph level (min-edge bounds on ≤ 21 vertices are finite statements — LARGE but
  conceptually the same as F3; likely too large for LRAT in practice at n=21 — assess).

## Design notes (F7, 2026-07-10)

`Lean617/MH2Proof.lean` (merged; `lake build Lean617.MH2Proof` clean). Everything
CONDITIONAL on `(pf : PrimFacts)(bf : BrouwerFacts)`. The frozen reference is
`review_queue/mh2-gpt56-candidate.md` INCLUDING the "Post-review repairs" (§5 Case B
via the ω-free 11-vertex nonexistence `pf.nonex11`).

**Architecture.** A `structure MH2Ctx` packages the five colour graphs on `Fin 21`
(the 21 non-`T` vertices) and the properties inherited from balancedness of `K₂₅` and
the `α(G_k−T)≤4` assumption: `Gc : Fin 5 → SimpleGraph (Fin 21)`, `k`, `col`, and
fields `adj_iff` (`(Gc i).Adj u v ↔ u≠v ∧ col u v = i`), `cap`, `alpha5`, `alphaH`,
`edgeSumOn` (colours partition every subset's pairs), `sees6` (every 6-set sees every
colour). §1 (`lemma_MH2_of`) does `by_contra` + `push Not` to get `α(G_k−T)≤4`, builds
`f : Fin 21 ↪ Fin 25` (image `univ∖T`), and assembles an `MH2Ctx` via `comap`; the
graph-theoretic contradiction is `MH2Ctx.false_of`. This cleanly separates the
colouring plumbing from §§3–7.

**Shared L-table extension — `Lean617/LTableExt.lean` (F7-owned, commit "F7a")**:
`turan3_general` (complement-Turán r=3 for `α≤3`), `affineBound_20`+`L20 = 84` (F5
method, equality at d=9), `Lfloor` (literal piecewise: `C(s,2)−t₃(s)` for `s≤12`,
`24..84` for `s∈[13,20]`) + `Lfloor_le_of_props` (`t≤20`). Namespace `Erdos617`, imports
`Lean617.LTable`. Arithmetic pre-checked in scratchpad/check_f7_arith.py. **Per team-lead
decision F7 OWNS these names** (moved OUT of MH2Proof.lean into LTableExt.lean); **F8
consumes them and deletes its `ell`/`turan3_general` duplicates**. `alphaAtMost_comap_gen`
still lives in MH2Proof.lean (F8 keeps its own copy or we co-locate later).

**Reusable graph helpers**: `edgeCountIn_clique`, `cliqueFree6_of_capAtMost11`,
`alphaAtMost_comap_gen`/`cliqueFree_comap_of` (general-m comap transport),
`edgeCountIn_ge_Lfloor` (α≤3 subset ⟹ Lfloor floor), `clique_card_le_of_cliqueFree`,
`card_complNbhd_indep_succ` (α-drop), `edgeCountIn_insert_ge`, `brouwer_Fi_on16`
(K₄-free 16-subset ⟹ e≥20), `exists_edge_of_edgeCountIn_pos`,
`edgeCountIn_union_le_cross` (disjoint-union edge split, ≤ form), `sees_colour`.

**Done + axiom-clean** (propext/Classical/Quot only, no sorryAx/native_decide):
§3 `MH2Ctx.edgeCount_Fi_ge_38` (Brouwer 173 ⟹ e≥37; equality `=37` ⟹ `bf.equality21`
A/B structure ⟹ the `A×B` colour-cross count `4(i)+5(k)+3·4(j)=21 > 20`),
§4.3 `edgeCount_ge_58` (Ψ recursion, `affineBoundPsi` d∈[0,20]),
§5 `H_cliqueFree5` (5.1/5.2 + Case B vacuous via `pf.nonex11` + count 46+4·20=126>120),
§6 (equality forcing in `false_of`), §7.1 `delta_ge_5` + degree-5 vertex, `count16_false`.

**§7 ENDGAME — DONE (F7e, 2026-07-10), `MH2Ctx.endgame` sorry-free & axiom-clean.**
Fix degree-5 `v`; `A = N_H(v)`, `Q = A∪{v}` (|Q|=6), `W = complClosedNbhd H v = univ∖Q`
(|W|=15); `r=e_H(A)`, `w=e_H(W)`, `c=crossE H A W`. Implementation, keyed to the earlier
sub-steps:
- **Cross-count infra** (`section Endgame7Infra`, general `SimpleGraph (Fin s)`): `crossE G A B
  := ∑_{a∈A} #{b∈B : Adj a b}`; lemmas `crossE_union_right`/`_insert_left`/`_singleton_left`
  /`_singleton_right`/`_eq_product`/`crossE_biUnion_right`, `sum_degree_eq_crossE_univ`;
  the two workhorses `crossE_self : crossE G A A = 2·e(G[A])` (fiberwise 2-to-1 over edges) and
  `edgeCountIn_disjoint_union` (equality partition, ⊇/disjointness/injOn added to the `le_cross`
  template) + `edgeCountIn_insert_eq'` (from it).
- **(steps 1-3) (r,w,c) system** (`omega` on atoms): partition `58 = e_H(Q)+w+crossE(Q,W)` with
  `e_H(Q)=r+5`, `crossE(Q,W)=crossE(A,W)=c` (v⊥W); handshake `∑_{x∈A} deg = crossE A univ =
  crossE A Q + c = (2r+5) + c`, δ≥5 ⟹ `2r+c≥20`; `w≥38` (`edgeCountIn_ge_Lfloor` at 15).
- **(step 4) five i-triangles**: `hlow` gives ordinary `i` with `e(F_i[W])≤16` (else ∑>67);
  `F_i[W]` K₄-free; transport to `Fin 15`, `edgeCountIn_add_compl` ⟹ `e((F_i[W])ᶜ)≥89` ⟹
  `brouwer_15_colorable` ⟹ `Colorable 5`; new lemma `clique_cover_of_compl_colorable` (colour
  classes are `F_i[W]`-cliques ≤ ω=3 summing to 15 ⟹ all triangles) ⟹ `C : Fin 5 → Finset`,
  transported back to `W` (card 3, disjoint, biUnion=W, H-independent).
- **(step 5) X_j + c≥10**: `Xset j = Q.filter (no H-edge to C_j)` is an H-clique (`hXset_clique`)
  so `|Xset j|≤4` ⟹ `|Aset j|≥2`; `crossE Q (C j)≥|Aset j|` (`card_filter_one_le_sum`) and
  `crossE Q W = ∑_j crossE Q (C j)` ⟹ `c≥10`; `omega` pins `(r,w,c)=(5,38,10)`.
- **(step 6) ρ + finish**: equality forces `crossE Q (C j)=|Aset j|=2` per j; `sum_le_one_of_sum_eq_card_filter`
  ⟹ each `q∈Q` sends ≤1 edge to `C_j`; degree split `d_H(x)=1+d_F(x)+e_W(x)` (crossE over
  {v}⊎A⊎W) with `e_W(x)+ρ_x=5` ⟹ `ρ_x≤d_F(x)+1`; `∑ρ_x=15=∑(d_F+1)` ⟹ equality ⟹ `ρ_x≥1` ⟹
  each `x∈A` in an H-triangle in `A`; transport `A→Fin 5`, apply the FINITE FACT
  `five_edge_no_triangle_cover` (5-vtx 5-edge triangle-covered ⟹ False, via δ≥2 ⟹ 2-regular ⟹
  a triangle closes a 3-set, leaving a degree-≤1 vertex — kernel `decide`-free, hand degree
  argument, `#print axioms` clean).
- **Gotchas hit (new):** `Set.PairwiseDisjoint` vs the expanded `∀ i j, i≠j → Disjoint` form
  (`Finset.card_biUnion` wants the latter — used it throughout); do NOT `rw [show (5:ℕ)=…]` when
  `Fin 5` is in scope (rewrites the `5` inside `Fin 5`, motive-ill-typed — use `Finset.sum_congr`
  to `∑ 1` instead); `Finset.card_sdiff_of_subset` (not `card_sdiff`); `mt Finset.mem_singleton.mp/.mpr`
  for `∉`-from-`≠`; `SimpleGraph.compl_adj` needs `by rw` (not `.2` on the unapplied family);
  `Prod.ext_iff.mpr` (not `Prod.ext`).

## Collaboration protocol

gpt-5.6-sol (codex CLI, read-only sandbox) is used for: drafting Lean proofs of
stated lemmas, Mathlib API hunting, and repairing failed compiles (give it the file
+ error output). Claude session/subagents: statement design, integration, compile
loop, review, commits. All agent-produced Lean must compile locally before commit;
no trust without `lake build`.
