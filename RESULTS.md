# Verified results

Entries here require a stated verification method: a script run (with exact command line and commit hash), a citation actually retrieved and read, or a completed adversarial review of a review_queue/ item. Date every entry. Nothing enters on confidence alone.

## R12. LEAN FORMALIZATION UNCONDITIONAL (2026-07-12): `erdos_617_r5_unconditional : Main` — no mathematical hypothesis remains

**Statement.** The D1–D4 campaign (relay runners 17–21) proved `KPEqualityClassification` — the Kang–Pikhurko (2005) equality classification at (5,21) — inside Lean: `kp_equality_classification_proven` (Lean617/JoinTransport.lean), via (D1) a symmetrisation/cone argument for extremal graphs, (D2) the forced-c=4 cone descent (5,21)→(4,17)→(3,13)→(2,9) with per-level degree forcing, (D3) join-transport reassembly (`coneExtend` functoriality: an extremal (5,21) graph is three nested cones over its (2,9) base), and (D4) the finite base classification `base_classification` — every 9-vertex triangle-free graph with α≤4, e=17, Δ≤4 is isomorphic to one of the two nauty-confirmed classes, proved by pure local counting (deg-2 apex structure; deg-3 s~t adjacency via an independence squeeze) with explicit `Equiv` witnesses, no graph-enumeration brute force. `Final.lean` now exports `erdos_617_r5_unconditional : Main` and `erdos_617_r5_upstream_unconditional` (the formal-conjectures-shaped corollary). The conditional `erdos_617_r5 (h : KPEqualityClassification)` remains exported for readers who prefer to audit the classification separately.

**Verification (re-run independently by the orchestrator on tracked HEAD 3fb4ca4, 2026-07-12).** Full `lake build` clean (8497 jobs, exit 0); `tools/sorry_grep.sh` PASS; `tools/axiom_audit.sh` PASS with `#print axioms erdos_617_r5_unconditional` = [propext, Classical.choice, Quot.sound] + 4 SAT-reflection axioms (unsat_M9/M10/nonex11/nonex12) + 10 KP-construction `native_decide` witnesses (kpG/kpG1 cone-isos and AB21-complement structure) = 17 axioms, **no sorryAx**; per-module `leanchecker` exit 0 (EqualityProof/JoinTransport/Final). `Statements.lean` and `tools/verify.py` byte-identical to v1.0 (git diff empty), so the proven statement is unchanged. Commits: 2bbe9d7…3fb4ca4.

## R11. LEAN FORMALIZATION COMPLETE MODULO ONE CLASSICAL STATEMENT (2026-07-12): `erdos_617_r5 : KPEqualityClassification → Main`, zero sorries in the entire build

**Statement.** The formalization campaign concluded (16 relay runners + 2 analysis agents): Brouwer's bound itself — the full Kang–Pikhurko Theorem-1 induction (Case A, the good/bad dichotomy, Lemma 3 with its K_{r+1}-counting core, the singleton guard) — is **proven in Lean, axiom-clean** (`kp_saving`, `kp_upper`: [propext, Classical.choice, Quot.sound]). The final theorem is conditional on exactly ONE published statement, `KPEqualityClassification` — the Kang–Pikhurko equality classification at (5,21) — which is literature-verified (papers/brouwer-kang-pikhurko.md) and independently numerically validated by full isomorph-free enumeration at five nearby parameter families (FORMAL.md "EQUALITY21 — analysis"; note the corrections recorded there: two extremal iso-classes, not three). Axiom profile of the final theorems: the three standard axioms + the four named SAT-reflection axioms — unchanged.

**Verification.** Commit 30db6f2 (+ audits re-run independently): full `lake build` clean over the complete aggregator (8495 jobs, zero sorries anywhere), `tools/sorry_grep.sh` PASS, `tools/axiom_audit.sh` PASS, `lake env leanchecker` per-module exit 0 on all touched modules. Optional future work (FORMAL.md D1–D4, est. 3–6 sessions): prove `KPEqualityClassification`, making the theorem unconditional modulo the SAT reflections.

## R10. LEAN FORMALIZATION of R9 (2026-07-11): `erdos_617_r5 (bf : BrouwerFacts) : Main`, zero sorries project-wide

**Statement.** The full R9 chain is formalized in Lean 4 + Mathlib (`lean617/`, ~5000 lines): the chain deduction, lemma [MH″] (including the reviewed §7 endgame), lemma [MM] (all four cases including the adopted r=7 repair), the L-table recursion, the counting identities, and the four SAT primitives (via cadical-LRAT certificates checked by Lean's verified checker). The final theorem `Erdos617.erdos_617_r5` and its upstream-shaped corollary `erdos_617_r5_upstream` (matching google-deepmind/formal-conjectures `erdos_617` at r=5 over an arbitrary 26-element vertex type) carry exactly one explicit mathematical hypothesis: `BrouwerFacts` — the classical Brouwer (1981)/Kang–Pikhurko (2005) bound + equality classification (literature-verified; formal discharge scoped in FORMAL.md F6, symmetrisation engine already formalized).

**Verification.** `lake build` clean (8489 jobs), zero `sorry` in the project; `#print axioms Erdos617.erdos_617_r5` = [propext, Classical.choice, Quot.sound] + four named SAT-reflection axioms (ofReduceBool via native_decide — the same trust base as Lean's `bv_decide`; certificate regeneration recipe in FORMAL.md F3). Campaign ledger: FORMAL.md (F0–F9 all DONE except the F6 BrouwerFacts discharge, in progress). Formalization authored by seven Claude subagent sessions with gpt-5.6-sol as lemma co-prover, per-milestone compile-verified commits.

## R9. MAIN THEOREM (chain complete, every link adversarially reviewed): there is no balanced 5-colouring of K_26 — Erdős Problem 617 holds at r = 5 (2026-07-10)

**Statement.** Every 5-colouring of the edges of $K_{26}$ contains six vertices whose induced $K_6$ misses at least one colour. Equivalently $N(5) = 25$: the affine-plane colourings of $K_{25}$ (R1) are optimal. This affirms the Erdős–Gyárfás conjecture (Problem 617) in its first open case, extending their $r=3,4$ [ErGy99].

**Proof structure (three links, each with its own adversarial review):**
1. **Chain deduction** (`review_queue/extension-chain.md`, reviewed & ACCEPTED 2026-07-05): if [MH″] and [MM] hold, no balanced 5-colouring of $K_{26}$ exists. Elementary: delete a vertex, partition the 25 others by the colour toward the deleted vertex; [MH″] forces all parts to have exactly 5 vertices; disjointness+tightness forces every part to carry ≤ 6 own-colour edges; [MM] forbids exactly that configuration at the minority colour.
2. **[MH″]** (R7; `review_queue/mh2-gpt56-candidate.md`, reviewed & ACCEPTED MODULO 2026-07-10, repairs applied): no balanced 5-colouring of $K_{25}$ has a colour class whose independent 5-sets can be killed by deleting 4 vertices.
3. **[MM]** (R8; `review_queue/mm-gpt56-candidate.md`, reviewed & ACCEPTED MODULO 2026-07-10, the single r=7 repair adopted from the reviewer's own write-out): no graph on 25 vertices with $\alpha \le 5$, cap-11, ≤ 60 edges admits a 5-set $T$ with $\alpha(G-T) \le 4$ spanning ≤ 6 internal edges.

**External inputs, all verified:** Brouwer's non-partite Turán bound with the Kang–Pikhurko equality classification (retrieved and read, all five uses checked faithful — `papers/brouwer-kang-pikhurko.md`); classical facts ($R(4,4)=18$ implicitly via Turán tables, Turán's theorem). **Machine inputs, all certified:** four primitive SAT facts (nonexistence of α≤2 cap-11 graphs on 11 and 12 vertices — ω-free, confirmed by 4 and 2 independent encodings respectively; $M(9) \ge 19$ and $M(10) \ge 25$ with ω≤4) with kissat DRAT certificates checked by drat-trim (`data/sat/prim_*`); the L-table is derived from these by verified exact arithmetic (`tools/verify_gpt_arith.py`), not by solver trust.

**Provenance note.** The proofs of [MH″] and [MM] were authored by gpt-5.6-sol (OpenAI) from self-contained briefs prepared by this session; the chain deduction, the reduction framework, all empirical structure-mining, brief preparation, and the verification/review infrastructure are this session's. Each proof was verified by: exact recomputation of every table, SAT confirmation of every small value (catching one benign strengthening — M(11) is a nonexistence, not a minimum — and one error in the author's own brief, flagged by the prover), literature verification of the external theorem, and independent fresh-session adversarial review. **Caveat: this is an internal review chain. Before public claims, the standard for a result of this significance is independent expert verification and, ideally, formalization (a Lean statement of Problem 617 exists in google-deepmind/formal-conjectures).**

**Corollaries.** $N(5) = 25$ exactly (with R1). The conjecture's pattern $N(r) = r^2$ holds for $r \in \{3,4,5\}$.

## R8. THEOREM (adversarially reviewed): Lemma [MM] (2026-07-10)

**Statement.** There is no graph $G$ on 25 vertices with $\alpha(G) \le 5$, every 6-set spanning ≤ 11 edges, $e(G) \le 60$, and a 5-vertex set $T$ with $\alpha(G-T) \le 4$ and $e(G[T]) \le 6$.

**Verification.** Proof by gpt-5.6-sol at `review_queue/mm-gpt56-candidate.md`: case analysis on the maximum number of disjoint $K_5$'s in $G-T$ (a peeling lemma shows this is 0, 1, 2 or 4). Author-session checks: §2 g-table exact (20/20 entries), §4 inequality-(16) case scan exact, §4.2 fixed-pair argument hand-verified, budget decompositions verified. Fresh-session adversarial review: ACCEPTED MODULO one missing conclusion (§5, r=7), which the reviewer closed with the candidate's own r=4 argument (write-out adopted); reviewer additionally re-verified the ω-caveat audit, the r=4 endgame edge counts, and the small lemmas. Primitive SAT inputs DRAT-certified.

## R1. N(5) ≥ 25: balanced 5-colourings of K_25 exist (2026-07-05)

**Statement.** The affine plane AG(2,5) yields balanced 5-colourings of $K_{25}$: identify the 25 vertices with $\mathbb{F}_5^2$, colour each edge by the direction (parallel class) of the unique line through its endpoints — 6 classes — then merge any two directions into a single colour. All 15 choices of merged pair give a balanced colouring.

**Verification.** `python3 tools/gen_ag25.py --all-merges` then `python3 tools/verify.py data/candidates/ag25_merge_<a>_<b>.json` for all 15 files: each reports `BALANCED: r=5, n=25; all 177100 subsets of size 6 see all 5 colours`. Run 2026-07-05 on the scaffold commit (see git log).

**Consequences.** By monotonicity (PROBLEM.md), balanced 5-colourings of $K_n$ exist for all $n \le 25$, so $N(5) \ge 25$. The conjecture predicts $N(5) = 25$. The r=5 case therefore reduces to the single question "does a balanced 5-colouring of $K_{26}$ exist?": every $n \le 25$ is now settled (SAT), and $n = 26$ is precisely the conjecture's claim. No small-case frontier search below 25 is needed.

**Why it's balanced (proof sketch, not yet reviewed — the *verified* claim is the referee run above).** An unmerged class is 5 disjoint $K_5$'s covering all 25 points, so any 6 points repeat a line ⇒ independence number 5. The merged class, in coordinates where the two directions are rows and columns, is the rook's graph on the 5×5 grid; an independent set uses each row and column at most once ⇒ independence number 5. A 6-set missing colour $c$ would be independent in class $c$.

## R2. No AG(2,5) merged colouring of K_25 extends to a balanced K_26 (computational; 2026-07-05)

**Statement.** For each of the 15 colourings of R1, there is **no** assignment of colours to 25 new-vertex edges making the resulting 5-colouring of $K_{26}$ balanced.

**Verification.** `.venv/bin/python tools/extend.py data/candidates/ag25_merge_<a>_<b>.json` for all 15 files: each reports UNSAT (CaDiCaL 1.9.5 via pysat on a 125-variable, 12620-clause instance encoding: for every 5-subset $F$ of the old vertices and every colour $c$ missing inside $F$, some new edge into $F$ has colour $c$ — this is exactly balancedness of all 6-sets through the new vertex). Sanity check of the tool: `tools/extend.py data/small_cases/pentagon_r2.json` reports UNSAT, matching $N(2)=5$ ($R(3,3)=6$). Run 2026-07-05.

**Scope.** This kills only the one-vertex extension of *these 15* colourings (all conjecturally isomorphic). It does not by itself say anything about other balanced colourings of $K_{25}$. A hand proof of a stronger statement (non-extendability for every prime power $r$) is queued at `review_queue/ag-nonextension.md`, not yet reviewed.

## R3. Balanced 5-colourings of K_25 are plentiful and structurally diverse, and none sampled extends (2026-07-05)

**Statement.** Local search (tools/locsearch.c, focused walk, noise 10%) finds balanced 5-colourings of $K_{25}$ from random starts routinely (~15% of seeds within 120k steps). 40+ distinct samples were generated (data/candidates/b25_*.json, ls25_seed1.json); every one passes `tools/verify.py` (BALANCED, 177100/177100); they include non-AG colourings (e.g. class-size profile (52,54,58,68,68) vs AG's (50,50,50,50,100) — edge-count profiles are isomorphism invariants). **Every sample fails one-vertex extension** (`tools/extend.py`: UNSAT for each; data/batch25_results.tsv column `extends` all False).

**Uniform structural facts across all samples (empirical, tools in repo):** exactly 25 monochromatic $K_5$s per colouring (5 per class); exact hitting numbers $h_c = 5$ for every class (data/hpass.log); every minimal hitting 5-set spans 9 or 10 own-colour edges — never ≤ 6, the "usability" bar from the extension-chain argument (data/usable_hitters_all.log, 225 class-scans, zero usable).

**Verification.** Each sample: `python3 tools/verify.py data/candidates/b25_<seed>.json` (referee) and `.venv/bin/python tools/extend.py <same>`. Batch driver: `tools/batch25.py`. Run 2026-07-05.

## R5. THEOREM (adversarially reviewed): merged affine-plane colourings never extend, for every prime power q ≥ 3 (2026-07-05)

**Statement.** For every prime power $q \ge 3$: the balanced $q$-colouring of $K_{q^2}$ built from $AG(2,q)$ by colouring edges by direction and merging two parallel classes admits **no** balanced one-vertex extension to $K_{q^2+1}$.

**Verification method.** Hand proof at `review_queue/ag-nonextension.md`, adversarially reviewed by an independent fresh session on 2026-07-05: verdict ACCEPTED (review appended to that file; three cosmetic fixes applied post-review, no mathematical changes). Computational cross-checks: $q=5$ — 15/15 merge choices UNSAT (R2, `tools/extend.py`); $q=3$ — reviewer's own independent exhaustive search over all $3^9$ extension maps for all 6 merge choices, zero balanced extensions. The reviewer additionally verified the construction's balancedness by pigeonhole, making the result self-contained.

**Significance.** The only construction in the literature achieving $N(r) \ge r^2$ (ErGy99's, see papers/ergy99.md) is exactly one vertex short of disproving the conjecture, *provably*, for every prime power $r \ge 3$ — not just $r=5$. Any counterexample to the conjecture must be structurally non-affine.

## R7. THEOREM (adversarially reviewed): Lemma [MH″] — no balanced 5-colouring of K_25 admits a 4-set hitter (2026-07-10)

**Statement.** There is no balanced 5-colouring of $K_{25}$ with a colour $c$ and a 4-vertex set $T$ such that $\alpha(G_c - T) \le 4$. Equivalently (and this is what is proved): no 5-colouring of $K_{21}$ in which every colour class is $K_6$-free and every 6-set spans ≤ 11 edges of any one class has colour-graph independence numbers $(4,5,5,5,5)$.

**Provenance and verification (full chain).** Proof authored by gpt-5.6-sol (OpenAI, via codex CLI, 2026-07-10) from a self-contained brief; document at `review_queue/mh2-gpt56-candidate.md`. Verified by: (i) literature agent — the load-bearing external theorem (Brouwer 1981 bound for non-$r$-partite $K_{r+1}$-free graphs; Kang–Pikhurko 2005 equality classification) retrieved and read, all five uses FAITHFUL, arithmetic recomputed (papers/brouwer-kang-pikhurko.md); (ii) exact recomputation of the entire §4 recursion (tools/verify_gpt_arith.py — all eight L(s) values, slack sequence, e≥58); (iii) SAT confirmation of every small exact value: M(9)=19, M(10)=25, M(12) nonexistence, and M(11) strengthened to **nonexistence** (three independent encodings); (iv) line-by-line hand check (author session); (v) fresh-session adversarial review: **ACCEPTED MODULO one repairable gap** (§5's ω(H[L])≤4 justification), repaired via the machine-verified ω-free 11-vertex nonexistence lemma — repairs applied and documented in the same file. The proof explicitly demonstrates non-applicability at n=24 (§8), matching the verified witnesses of R6.

**Consequence.** Combined with the adversarially-reviewed deduction of `review_queue/extension-chain.md`, the r=5 case of Erdős Problem 617 now rests on the SINGLE remaining machine lemma [MM] (no ≤60-edge class on 25 vertices with a usable 5-hitter).

## R6. The h4 phase transition: hitter colourings exist for n = 17..24 and are referee-verified; five independent searches wall at n = 25 (2026-07-06..09; EVIDENCE, not proof)

**Definitions.** An *h4-witness at n* is a balanced 5-colouring of $K_n$ together with a 4-vertex set $T$ (WLOG $\{0,1,2,3\}$) and a colour (WLOG 0) such that $\alpha(G_0 - T) \le 4$. The chain lemma [MH″] (review_queue/extension-chain.md) asserts none exists at $n = 25$.

**Verified facts.** h4-witnesses EXIST at every $n \in \{17,\dots,24\}$: found by kissat (n ≤ 22; solve times 0.7s/5.8s/5.1s/46s/372s/~5000s — ~×8 per vertex) and by local search (n = 23, 24; `tools/locsearch_h4.c`); each stored under `data/candidates/` (h4_witness_n20/22.json, h4hunt_n23_s2.json, h4hunt_n24_w.json) and **each passes tools/verify.py (BALANCED) plus an exact independent-5-set check of the hitter condition** (commands in git log around this entry). Notably the n=24 witness was found in 80k local-search steps (~1 minute) by warm-chaining from the n=23 witness.

**Evidence at n = 25 (NOT a proof).** Five independent hunts (2 cold random-start, 3 warm-chained from the verified n=24 witness, different seeds) each descended to **exactly 24** unsatisfied hitter 5-sets and remained pinned there for ≥18h wall / ≥36 CPU-hours apiece (best-trail logs in data/candidates/h4hunt_n25_*.log). In near-floor states every violated 5-set passes through the newest vertex (in one run, through a single vertex pair) — the same "deficiency-1" signature as the K_26 direct searches (whose independent walkers all wall at ~800 violations, every violation through one vertex pair). Interpretation: the hitter constraint costs exactly one vertex of slack; the h4 family dies between 24 and 25. **Conjecture (machine-checkable, open): MH″ — no h4-witness at n = 25.** If proved (e.g. cluster-scale cube-and-conquer producing DRAT), the adversarially-reviewed chain (review_queue/extension-chain.md) reduces Erdős 617 at r=5 to the single remaining lemma [MM].

## R4. Six sampled balanced K_24 colourings admit no two-vertex extension (2026-07-05)

**Statement.** For 6 balanced colourings of $K_{24}$ (vertex-deleted restrictions of two K_25 samples), the *joint* two-new-vertex extension problem (all 49 new edges simultaneously) is UNSAT.

**Verification.** `.venv/bin/python tools/extend2.py data/candidates/k24_*.json` → "UNSAT: no 2-vertex extension" ×6. Run 2026-07-05. (Note: these K_24s are restrictions; freshly-generated K_24s not yet tested at scale.)

