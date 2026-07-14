# Review by team A — external candidate B (`candidate-proof.md`)

Date: 2026-07-14. Requested by VERIFICATION-ROUND.md Task 2 (human collaborator,
2026-07-13). Provenance of the candidate deliberately withheld and not investigated;
only the mathematics was judged, per the round's ground rule.

**Protocol.** Two independent fresh-eyes reviewers with disjoint mandates, both
instructed to adopt the working stance that the document contains at least one fatal
gap and to hunt for the weakest inference:

- **Reviewer α** — the internal mathematical chain (§§2–8, §10 counting, §11), every
  number recomputed, load-bearing arithmetic reproduced by script. Full line-by-line
  notes: `review-alpha-notes.md` (402 lines, written incrementally during review).
- **Reviewer β** — literature faithfulness (all cited theorems retrieved from the
  actual sources, not the candidate's paraphrases) and the certificate-semantics
  reductions of §§9–10 (statement level; certificates themselves treated as given per
  the task instruction).

Per the round's instruction, the two machine-checked lemmas (the §9 seven-signature
lemma and the §10 three-K₃ defect lemma) were treated as **given facts** exactly as
stated; everything else was in scope.

---

## VERDICT: SURVIVES

No fatal error and no genuine mathematical gap was found in anything within scope.
Every recomputed number reproduces exactly: the §3 boundary bounds, the §4 five-part
transversal lemma (all four `a`-cases including the exact inclusion–exclusion at
`a=3`), the §5–§6 case eliminations, the §7 stability table (all six rows), the
exhaustive enumerations behind (7.4)/(7.5), the eight-signature exhaustiveness in §8,
the exchange inequality (8.1), and the §10 double-count (2R ≥ 39 vs R ≤ 19). The
citation statements are faithful to the actual sources, correctly conditioned at
every application site, and the CNF reductions are relaxations in the safe direction,
so UNSAT genuinely excludes the encoded graphs. Logic sweep: no circularity (§7 does
not depend on §§4–6; (6.1) is proven universally before its only use in §8), and the
quantifier structure of (7.7) is consistent.

**Weakest internal inference (stated per protocol even though the verdict is
SURVIVES):** the §7.3 incidence-budget step at candidate line ~470 — the blanket
"at most 16 incidences altogether" is too loose for the `(5,4,4,3,3)` base-10
sub-case (16 − 10 = 6 does not strictly beat the 6 needed); the argument is rescued
because that row FORCES `e(C,D) = 15` exactly, giving budget 5 < 6. The mathematics
is right; the exposition cites the wrong constant. (Finding E1 below.)

**Most delicate external dependence:** the argument needs the *strict* inequality in
Bollobás–Nikiforov (their Theorem 2) — the degree-sum bound computes to exactly 80,
and only strictness yields σ ≤ 19, on which the entire §7 table rests. Reviewer β
confirmed from the retrieved paper that the strict conclusion is real (equality forces
regularity, and the candidate quarantines the regular case separately first). Fragile
but correct.

---

## Reviewer α (internal chain) — summary

Full derivations in `review-alpha-notes.md`. Verdict SURVIVES; findings:

| id | line | severity | finding |
|---|---|---|---|
| E1 | ~470 | non-fatal (exposition) | §7.3 "at most 16 incidences" too loose for the `(5,4,4,3,3)` case; forced `e(C,D)=15` closes it — the text should cite 15 there |
| A1 | ~835 | non-fatal (artifact) | §11 cites `data/candidates/affine_k25_r5.json`, absent in this repository; the mathematically identical committed certificate `ag25_merge_0_inf.json` (slopes 0 and ∞ merged = the horizontal+vertical construction) was run through `tools/verify.py` here: BALANCED, 177,100/177,100 |

Three least-obvious steps, expanded in full in the notes file:
1. **§4, five-part lemma at `a=3`**: derivation of the exact inclusion–exclusion
   `U = 27 − 3k + w − t` over the 27 small transversals (`w` = degree-2 vertices,
   `t` = triangles, vertex-disjoint so `3t ≤ w`; `w ≥ 2k − 9` from the degree sum),
   and the closing comparison `16U > 36(10−k)` for `k = 6,7,8,9`.
2. **§6, triangle sub-case of the `3,3,4,4,4` endgame**: all six bipartite degrees
   are forced to 1 (zero-degree is killed by the missing-rectangle rule plus the
   `K_{3,2}`/`K_{2,3}` exclusion), the anchored cap forces the incidences to be a
   bijection, third-exceptional missing-rectangles force every remaining pair, so
   `H = G[A,B]` is complete — and then `A ∪ B` spans `K_6` = 15 > 11 edges of one
   colour, the (GAP) contradiction.
3. **§7, the intersection bound (7.1)** `c ≥ 22 − σ`: the reconciliation is that
   `Σ_H d(a) = (100 − σ)` includes the 12 incidence-contributions of the six
   A-internal edges (A is an H-clique K₄); incidences from outside are `88 − σ`,
   each of the 22 outside vertices contributes at most 4, and a vertex outside the
   common neighbourhood contributes at most 3 — giving `|C| ≥ (88 − σ) − 3·22 =
   22 − σ`. The candidate's constant is right; the naive count that ignores the
   A-internal edges would give a wrong (weaker) bound.

## Reviewer β (literature + certificate semantics) — summary

- **A1, Bollobás–Nikiforov**: retrieved — "The sum of degrees in cliques,"
  arXiv:math/0410218, **Theorem 2**, quoted faithfully including the load-bearing
  strictness (see above); hypothesis set (`m ≥ t_r(n)`, nonregular, r-clique
  indexing, only `n ≥ r`) matches the application exactly. FAITHFUL.
- **A2, Brouwer (complement form)**: exactly the dual of the form verified in this
  repository's `papers/brouwer-kang-pikhurko.md`; constants `+⌊n/t⌋−2` ↔ `−⌊n/t⌋+1`
  and the `n > 2t` regime check; application at `(n,t) = (19,5)`, `T(19,5) = 27`,
  threshold 28, `19 > 10`. FAITHFUL.
- **A3, Turán + equality**: all values reproduced (`t_4(26)=253`, `t_5(26)=270`,
  `L_5(17,18,19) = 21,24,27`, the full §7 table). FAITHFUL.
- **A4, Erdős–Gyárfás**: attribution and construction match the repository's
  verified `papers/ergy99.md`. FAITHFUL.
- **B1–B5, reduction semantics**: every clause class added by the encodings is a
  true consequence for a real gap graph of the encoded signature (safe relaxation),
  so UNSAT ⇒ nonexistence; all eight signature degree-sums equal 25; the
  compact-core protocol is sound given per-clause origin reconstruction plus
  injective renaming; the 58-orbit count was reproduced independently two ways
  (canonical representatives and Burnside over the order-288 group); the §10
  application site establishes exactly the defect lemma's premises; the
  fault-diversity runs (Kissat/Sinz, the cap-66 and cap-12 controls) are hygiene,
  not load-bearing. SOUND.
- **C, definition cross-check**: the candidate's balanced definition and 0/12
  thresholds match PROBLEM.md's pinned definition. (Independently, this round's
  Task 3 kernel-checked that the companion interface's statement is equivalent to
  this repository's `Main` — see `verification/interface-equivalence.md`.)

---

## Required before publication

1. **Pin the Bollobás–Nikiforov reference**: arXiv:math/0410218, Theorem 2; verify
   final venue/year (the candidate's note filename says 2005; only the 2004 arXiv
   preprint was confirmed here) and record a content hash of the retrieved source.
2. **State the compact-core injectivity requirement explicitly**: the origin-map
   check must certify that the compact→full variable renaming is injective (not
   merely that each compact clause is reconstructable) — that is the exact formal
   requirement for compact-UNSAT ⇒ full-UNSAT.
3. **Fix the §11 artifact**: commit `affine_k25_r5.json` or cite the existing
   equivalent certificate; as run here, the equivalent construction passes the
   referee (BALANCED, 177,100/177,100).
4. **Tighten §7.3's incidence budget** (finding E1): cite the forced `e(C,D) = 15`
   in the `(5,4,4,3,3)` sub-case instead of the blanket ≤ 16.
5. **Independent certificate replay**: this review treated the §9/§10 certified
   lemmas as given, per instruction. A full external audit must replay the LRAT
   certificates (the candidate documents resource-capped replay commands) and audit
   `encode.py`'s fixed-structure emission against §9's prose semantics — the one
   part of the trust chain nobody in this round examined.

**Bottom line:** a genuinely different proof of the same theorem from ours
(direct minority-colour analysis on K₂₆; no extension-obstruction chain), and it
survived the same adversarial standard we applied to our own lemmas. Subject to
items 1–5, team A finds no obstacle to publication.
