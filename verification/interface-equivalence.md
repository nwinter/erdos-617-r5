# Statement-interface equivalence — external `interface-B` vs our `Main`

**VERIFICATION-ROUND.md, Task 3.** Verdict up front: **EQUIVALENT.** The external
Lean statement interface `review_queue/external-candidate-B/interface-B.lean.txt`
and our own statements (`lean617/Lean617/Statements.lean`, `Final.lean`) formalize
the *same* problem — erdosproblems.com #617 = Erdős–Gyárfás Conjecture 1 [ErGy99],
specialized to `r = 5` (no balanced 5-colouring of `K₂₆`) — via the *same* upstream
declaration, `google-deepmind/formal-conjectures`'s `Erdos617.erdos_617` at `r = 5`.
The equivalence is not just token-level: it is now **machine-checked, sorry-free**,
in `lean617/Lean617/InterfaceCross.lean`.

Method: (a) grep the external interface for any repo/commit/SHA pin and compare what
each side pins; (b) definition-by-definition semantic comparison of the two encodings
against each other and against PROBLEM.md; (c) transcribe the external interface's
final definitions *verbatim* into Lean and prove them `↔ Main`, sorry-free, then read
off the axiom profiles. Retrieval dates: interface-B read 2026-07-13; upstream
`erdos_617` text is our repo's verified copy in `papers/ergy99.md` §8 (fetched via
GitHub API 2026-07-05).

---

## 1. Upstream-source pinning comparison

### 1a. What interface-B pins

`interface-B.lean.txt` is 129 lines: `import Mathlib`, `set_option autoImplicit
false`, `namespace Erdos617`, then the definitions and lemmas. A grep for any
repository / commit / SHA / URL marker returns **only** `import Mathlib`:

```
$ grep -niE 'formal-conjectures|deepmind|commit|sha|github|http|rev[ :]|import' \
      review_queue/external-candidate-B/interface-B.lean.txt
7:import Mathlib
```

So interface-B carries **no explicit repo/commit/SHA pin.** What it *does* pin is a
declaration **name plus a literal type shape**, stated in its docstrings:

- lines 39–45 (`UpstreamStatement`): its body is *"the exact outer binder order and
  conclusion of the public `Erdos617.erdos_617` declaration … The hypothesis `hr` is
  retained even though it does not occur in the conclusion, exactly as in the upstream
  declaration."*
- lines 54–57 (`upstreamStatement_iff_literal`): *"the right side is the exact type of
  the public upstream declaration after its theorem name."*

i.e. interface-B pins the **declaration `Erdos617.erdos_617`** and reifies its type as
a `Prop`, but does not say from which repository/commit that declaration comes.

### 1b. What we pin (our F1 fidelity target)

Our fidelity chain targets `google-deepmind/formal-conjectures`,
`FormalConjectures/ErdosProblems/617.lean`, declaration **`Erdos617.erdos_617`** —
recorded verbatim, **VERIFIED** (fetched via GitHub API 2026-07-05) in
`papers/ergy99.md` §8, and cross-reviewed token-for-token in RELEASE.md
§Statement-fidelity (R3, two independent model families, 0 mismatches). The upstream
text (papers/ergy99.md §8):

```lean
theorem erdos_617 (r : ℕ) (hr : r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = r^2 + 1) (coloring : Sym2 V → Fin r) :
    ∃ (S : Finset V) (k : Fin r),
      S.card = r + 1 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k
```

**The declaration name interface-B pins — `Erdos617.erdos_617` — is exactly the name of
this formal-conjectures declaration** (papers/ergy99.md line 8 states plainly that the
`google-deepmind/formal-conjectures` Lean statement *is* `Erdos617.erdos_617`, and §8
gives its text). So the two sides pin the *same declaration*; interface-B merely omits
the repository coordinates that we supply.

### 1c. Shape comparison at r = 5 (token level)

Interface-B's `UpstreamStatement r _hr` reifies `erdos_617`'s type — turning the
signature binders after `(r) (hr)` into `∀`/`→` inside a `Prop` — and
`UpstreamStatementR5 := UpstreamStatement 5 (by norm_num)`. Since `_hr` never occurs in
the body, `UpstreamStatementR5` unfolds to:

```lean
∀ {V : Type} [Fintype V] [DecidableEq V], Fintype.card V = 5^2 + 1 →
  ∀ coloring : Sym2 V → Fin 5,
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k
```

Our `main_imp_upstream` (Statements.lean:180) / `erdos_617_r5_upstream` (Final.lean:58)
conclusion is:

```lean
∀ {V : Type} [Fintype V] [DecidableEq V], Fintype.card V = 5 ^ 2 + 1 →
  ∀ (coloring : Sym2 V → Fin 5),
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k
```

These are **token-identical**: `Fintype.card V = 5^2 + 1`, `Sym2 V → Fin 5`,
`S.card = 5 + 1`, `∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k`. Both equal the type
of upstream `erdos_617` at `r := 5`. The only representational difference:

- upstream `erdos_617` is a **theorem** whose `hr : r ≥ 3` is a live signature binder;
- interface-B keeps `hr` as an **unused explicit parameter `_hr`** of a `Prop`-valued
  `def`, and at `r = 5` discharges it with `(by norm_num : 5 ≥ 3)`;
- our `main_imp_upstream`/`erdos_617_r5_upstream` **drops** `hr` entirely (trivially
  satisfied at `r = 5`).

All three choices yield the *same* `Prop` at `r = 5` (an unused hypothesis changes no
mathematics; supplying it and ignoring it, or omitting it because it is provable, give
definitionally equal statements). Our R3 review already found dropping `hr` sound; here
interface-B keeps it, and both reduce to the identical statement.

**Verdict (a): SAME STATEMENT.** Both interface-B and our fidelity proof formalize the
identical upstream declaration `Erdos617.erdos_617` at `r = 5`. Only the *provenance
metadata* differs (we cite repo+commit-era retrieval + an R3 token-identity review;
interface-B cites the declaration name + literal shape with no repo/SHA).

---

## 2. Definition-by-definition semantic comparison

Below, "theirs" = `Erdos617.InterfaceB.*` (the verbatim transcription in
InterfaceCross.lean), "ours" = `Erdos617.*` (Statements.lean). PROBLEM.md pins: an
r-colouring is a function on the edge set; **balanced** = *every* `(r+1)`-subset sees
*all* `r` colours among its `C(r+1,2)` edges; the `r = 5` target is "does `K₂₆` admit a
balanced 5-colouring" (conjecture: NO).

| concept | theirs (interface-B) | ours (Statements.lean) | relationship |
|---|---|---|---|
| "S sees colour k" | `SeesColor c S k := ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u,v) = k` | encoded as `¬ Misses c S k` (no standalone def) | `SeesColor c S k ↔ ¬ Misses c S k` (classical) |
| "no edge of S has colour k" | inner clause of `HasMissingColor`: `∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k` | `Misses c S k := ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k` | **identical clause, verbatim** |
| balanced | `Balanced c := ∀ S, S.card = r+1 → ∀ k, SeesColor c S k` | `Balanced c := ∀ S, S.card = 6 → ∀ k, ¬ Misses c S k` | same statement: `r+1 = 6` at `r=5`; inner `SeesColor ↔ ¬Misses` |
| missing-colour witness | `HasMissingColor c := ∃ S k, S.card = r+1 ∧ (no edge of S coloured k)` | `Main` body: `∃ S k, S.card = 6 ∧ (no edge of S coloured k)` | same; `hasMissingColor_iff_not_balanced` ↔ `main_iff_no_balanced` |
| "no balanced 5-colouring" | `NoBalancedFiveColoring := ∀ {V}[Fintype][DecEq], card V = 26 → ∀ c, ¬ Balanced c` | `Main := ∀ c : Sym2 (Fin 26)→Fin 5, ∃ S k, …`; `main_iff_no_balanced : Main ↔ ∀ c, ¬ Balanced c` | **equivalent — proven** `interfaceB_noBalanced_iff_main` |
| exact-upstream r=5 shape | `UpstreamStatementR5 := UpstreamStatement 5 _` | `main_imp_upstream` concl / `erdos_617_r5_upstream` | **token-identical — proven** `interfaceB_upstreamR5_iff_main` |

### The `u ≠ v` / `Sym2` diagonal analysis

Both encodings represent an edge as `s(u,v) : Sym2 V` (unordered), and both guard every
edge reference with an explicit **`u ≠ v`**:

- theirs — `SeesColor` witnesses require `u ≠ v ∧ …`; `HasMissingColor`'s clause is
  `u ≠ v → …`;
- ours — `Misses` is `u ≠ v → …`.

Consequences, identical on both sides:
- **Diagonal values are irrelevant.** `c` is total on `Sym2 V`, so it also assigns a
  colour to diagonal pairs `s(v,v)`; but the `u ≠ v` guard means no diagonal `s(v,v)` is
  ever consulted in "sees"/"misses". This matches PROBLEM.md's "function on the edge set"
  (edges = 2-element subsets = off-diagonal `Sym2`). Neither encoding lets a diagonal
  colour affect balancedness.
- **Ordered double-quantification is harmless.** Both write `∀ u ∈ S, ∀ v ∈ S` (resp.
  `∃ u ∈ S, ∃ v ∈ S`) over ordered pairs, but `s(u,v) = s(v,u)` collapses each to the
  same `Sym2` element, so the extra ordering is a no-op (same `Prop`). (Our R3 review
  noted this for `Misses`; it holds identically for `SeesColor`.)
- **Colour totality.** Codomain `Fin 5` on both sides: every edge gets exactly one of
  5 colours; matches PROBLEM.md's `{0,…,r−1}`, `r = 5`.

### The single classical bridge

The only inner-shape difference is **positive existential vs negated universal**:
theirs states "sees" as `SeesColor` (an `∃`), ours as `¬ Misses` (a `¬∀`). These are
equivalent by `¬∀ ↔ ∃¬`, which needs classical logic. Interface-B's own
`hasMissingColor_iff_not_balanced` discharges it with `classical`; our development runs
under `open scoped Classical`. No semantic daylight — both are the *same classical
statement*; only the surface encoding of "sees" differs, and the bridge is compiled
(it is the load-bearing step of `interfaceB_noBalanced_iff_main`).

### The only non-cosmetic structural gap — and its bridge

Interface-B's `Balanced`/`SeesColor` are **polymorphic** over `r` and an **arbitrary**
vertex type `V`, and `NoBalancedFiveColoring` carries the cardinality hypothesis
`Fintype.card V = 26` **on itself** (not on `Balanced`). Ours is monomorphic:
`Balanced`/`Misses`/`Main` live over `Fin n` / `Fin 26` with no cardinality hypothesis.
Bridging "arbitrary card-26 `V`" and "`Fin 26`" is exactly what our `main_imp_upstream`
does (transport along `Fintype.equivFinOfCardEq : V ≃ Fin 26`). This is the backward
direction of `interfaceB_upstreamR5_iff_main`, and it is the reason the equivalence is a
theorem to prove rather than `Iff.rfl`. It is machine-checked; there is no loss of
generality in our `Fin 26` phrasing.

### Cardinality audit (no off-by-one)

- vertices: theirs `card V = 26`; upstream `r²+1 = 26` at `r=5`; ours `Fin 26` /
  `5^2+1`. **26 = 5²+1.** ✓
- subset size: theirs `S.card = r+1 = 6`; ours `S.card = 6` (`= 5+1` in the upstream
  shape). **6 = 5+1.** ✓
- colours: `Fin 5` on both. ✓

No `25/26` or `5/6` confusion anywhere.

**Verdict (b): the two final statement shapes are mathematically equivalent** — proven,
not merely asserted (next section).

---

## 3. The Lean cross-check — `lean617/Lean617/InterfaceCross.lean`

The external interface's definitions and internal lemmas are transcribed **verbatim**
(lines 13–127 of interface-B.lean.txt, modulo only the namespace line `Erdos617` →
`Erdos617.InterfaceB`, docstrings preserved) into `namespace Erdos617.InterfaceB`. That
this transcription — `def`s *and* their `Iff.rfl`/classical proofs
(`balanced_iff_every_set_sees_every_color`, `upstreamStatement_iff_literal`,
`hasMissingColor_iff_not_balanced`, `upstreamStatementR5_iff_noBalancedFiveColoring`,
`upstreamR5_of_clean`) — compiles unchanged under our toolchain
(`leanprover/lean4:v4.30.0`, Mathlib `v4.30.0`) is itself part of the fidelity check.
(Compilation also self-confirms name resolution: `NoBalancedFiveColoring`'s body
`¬ Balanced coloring` type-checks over an arbitrary `V` only because `Balanced` resolves
to the inner `Erdos617.InterfaceB.Balanced`, not our `Fin`-restricted `Erdos617.Balanced`
— which would not type-check there.)

Then, sorry-free:

| theorem | statement | axioms |
|---|---|---|
| `interfaceB_upstreamR5_iff_main` | `InterfaceB.UpstreamStatementR5 ↔ Erdos617.Main` | `{propext, Classical.choice, Quot.sound}` (pure) |
| `interfaceB_noBalanced_iff_main` | `InterfaceB.NoBalancedFiveColoring ↔ Erdos617.Main` | `{propext, Classical.choice, Quot.sound}` (pure) |
| `interfaceB_upstreamR5_unconditional` | `InterfaceB.UpstreamStatementR5` | the 17 below |
| `interfaceB_noBalanced_unconditional` | `InterfaceB.NoBalancedFiveColoring` | the 17 below |

Proof routing:
- `interfaceB_upstreamR5_iff_main` — forward: instantiate their arbitrary-`V` statement
  at `V = Fin 26` (`Fintype.card (Fin 26) = 5^2+1` by `norm_num`), read off
  `S.card = 5+1 = 6`. Backward: exactly our `main_imp_upstream`.
- `interfaceB_noBalanced_iff_main` — compose the interface's own transcribed
  `upstreamStatementR5_iff_noBalancedFiveColoring` (`.symm`) with the equivalence above.
- the two `*_unconditional` corollaries — transport our completed
  `Erdos617.erdos_617_r5_unconditional : Main` through the respective `.mpr`.

The two **equivalences are axiom-pure** (standard three only): they add no reflection or
mathematical axiom — pure logic plus the `Fin 26 ↔ card-26 V` transport. The two
**transported corollaries** carry exactly the profile of
`erdos_617_r5_unconditional` — **17 axioms, no `sorryAx`**:

- 3 standard: `propext`, `Classical.choice`, `Quot.sound`;
- 4 SAT `native_decide`: `unsat_M9`, `unsat_M10`, `unsat_nonex11`, `unsat_nonex12`
  (`…_native.native_decide.ax_1_1`);
- 10 KP-construction `native_decide`: `kpG_giso_cone3` (×1), `kpG1_giso_cone3` (×1),
  `kpG_compl_AB_structure` (ax_1_1..1_4 = ×4), `kpG1_compl_AB_structure`
  (ax_1_1..1_4 = ×4).

This is identical to the documented unconditional profile (RELEASE.md R1;
`tools/axiom_allowlist.txt`: "3 standard + 4 SAT + 10 D-campaign = 17"). The corollaries
being unconditional theorems (no mathematical hypothesis) shows the external targets are
not merely equivalent to `Main` but *discharged* by our proof.

### Build / gate status (this machine, `lean617/`, toolchain `v4.30.0`)

- `lake build Lean617` (aggregator now imports `Lean617.InterfaceCross`): **PASS** —
  `Build completed successfully (8498 jobs)`, exit 0. `InterfaceCross.lean` builds
  warning-clean.
- `tools/sorry_grep.sh`: **PASS** (no real `sorry`).
- `tools/axiom_audit.sh`: **PASS** — the six audited finals
  (`lemma_MM`, `lemma_MH2`, `erdos_617_r5`, `erdos_617_r5_upstream`,
  `erdos_617_r5_unconditional`, `erdos_617_r5_upstream_unconditional`) are untouched by
  this file; their profiles are unchanged. `AxiomAudit.lean` audits only those six, so
  the new theorems do not enter the gate; their KP-construction `native_decide` axioms
  would in any case be matched by the existing `glob:*native_decide*` allowlist entry.

---

## 4. Verdict

**EQUIVALENT.** The external `interface-B` and our statements formalize the identical
problem — erdosproblems.com #617 / Erdős–Gyárfás Conjecture 1 [ErGy99] at `r = 5`
(no balanced 5-colouring of `K₂₆`) — through the identical upstream declaration
`google-deepmind/formal-conjectures` `Erdos617.erdos_617` specialized to `r = 5`.

- (a) Same upstream statement: interface-B pins the declaration name `Erdos617.erdos_617`
  + literal type shape (no repo/SHA); we pin the same declaration with repo coordinates +
  an R3 token-identity review. Their `UpstreamStatementR5` is token-identical to our
  `erdos_617_r5_upstream` conclusion and to upstream `erdos_617` at `r=5`.
- (b) Same mathematics: the definitions agree clause-for-clause (identical `u ≠ v`
  diagonal handling, identical cardinalities `26 = 5²+1`, `6 = 5+1`, `Fin 5` colours);
  the only encoding differences are "sees" as `∃` vs `¬∀` (one classical bridge) and
  arbitrary-`V` vs `Fin 26` (the `main_imp_upstream` transport).
- (c) Machine-checked: `interfaceB_upstreamR5_iff_main` and `interfaceB_noBalanced_iff_main`
  prove `↔ Main` sorry-free (axiom-pure); the two `*_unconditional` corollaries discharge
  the external targets outright with the disclosed 17-axiom profile of
  `erdos_617_r5_unconditional`.

No discrepancy found; this is **not** a five-alarm situation. The external interface is a
faithful alternative phrasing of the same `r = 5` statement our proof resolves.

---

*Files:* `lean617/Lean617/InterfaceCross.lean` (transcription + equivalences +
corollaries), aggregator `lean617/Lean617.lean` (imports it). *Inputs:*
`review_queue/external-candidate-B/interface-B.lean.txt`, `lean617/Lean617/Statements.lean`,
`lean617/Lean617/Final.lean`, `papers/ergy99.md` §8, RELEASE.md §Statement-fidelity,
PROBLEM.md. *Date:* 2026-07-13.
