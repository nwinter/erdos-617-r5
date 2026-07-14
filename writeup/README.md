# Write-up: the r = 5 case of Erdős Problem 617 (two-proofs paper)

`erdos617-r5.tex` is an arXiv-ready LaTeX note (amsart). It is a **verification-ready
report**, not an authored announcement: it presents a *candidate resolution* of the
first open case (r = 5) of the Erdős–Gyárfás balanced-colouring conjecture —
**there is no balanced 5-colouring of K₂₆; equivalently N(5) = 25** — produced and
internally reviewed by AI systems and offered for independent verification.

**Version 2.0 (draft, 2026-07-14): two-proofs merge.** The paper now contains **two
independent proofs** of the same theorem, produced by two separate AI efforts that shared
the problem scaffold but no mathematical route:

- **Proof A** (Part I) — *local*: delete a vertex, partition the other 25 by colour, reduce
  to two lemmas [MH″], [MM] on a single colour class; a cap-11 recursion + Brouwer/Kang–Pikhurko
  + four SAT facts close it.
- **Proof B** (Part II) — *global*: no deletion; a minority "gap graph" on K₂₆ and a pincer on
  the boundary P(Q) = Σ deg over independent 5-sets (five-part transversal lemma ⇒ P ≥ 25
  everywhere; Bollobás–Nikiforov strict + Brouwer stability ⇒ P ≤ 25 somewhere), then eight
  exact-P = 25 signatures excluded by 66 LRAT certificates + a counting lemma. Uses **no**
  Kang–Pikhurko.

Section 2 ("How to verify this report") is the reader's guide to checking either proof.

> **Proof B is pending an accuracy pass by its authors.** Every Proof-B section
> (Sections 11–14) carries a visible `[Pending accuracy pass by the proof's authors.]`
> marker and a global footnote: the Proof-B exposition is the Proof-A authors' faithful
> *rendering* of the Proof-B team's source document, awaiting that team's sign-off. Do
> not treat the Proof-B prose as the Proof-B team's own words until that pass is done.

## Compiling

The document uses only standard packages (`amsmath`, `amssymb`, `amsthm`,
`mathtools`, `geometry`, `microtype`, `enumitem`, `booktabs`, `array`, `hyperref`,
`xcolor`) and a self-contained `thebibliography` — no `.bib` file, no external
assets. Any modern TeX distribution compiles it.

```sh
latexmk -pdf erdos617-r5.tex
```

or `pdflatex erdos617-r5.tex` twice (the second pass resolves cross-references).
Output: `erdos617-r5.pdf` (~36 pages). The build is clean: no errors, no undefined
references, no overfull/underfull boxes.

## What the paper contains

| § | contents |
|---|----------|
| 1 | the conjecture and its history; the two main theorems; the **two-proofs** framing and their independence; provenance-in-brief; organisation |
| 2 | **How to verify**: the two Lean formalisations and their kernel-checked equivalence; a 30-min machine path (axiom audit of either), a reading path (either proof suffices), a completist audit, and what is *not* yet claimed |
| 3 | **Shared preliminaries**: notation, **cap-11**, elementary facts, and the shared affine lower bound N(5) ≥ 25 (both merge choices, one committed certificate) |
| **Part I — Proof A** | |
| 4 | the extension-obstruction reduction (two lemmas [MH″], [MM]; the chain) |
| 5 | the shared cap-11 toolkit (Brouwer + Kang–Pikhurko equality, counting identity, M/L tables, four SAT facts) |
| 6 | Lemma [MH″] (21-vertex reduction; e(Fᵢ) ≥ 38; e(H) ≥ 58; H is K₅-free — repaired ω-free route; the endgame; why it fails at n = 24) |
| 7 | Lemma [MM] (peeling; the {0,1,2,4}-K₅ case split; the repaired ν = 7 closure) |
| 8 | Theorem B: merged affine K_{q²} colourings never extend (all prime powers q ≥ 3) |
| 9 | Proof A's four SAT certificates (CNF, sizes, two verification paths, regeneration) |
| 10 | Proof A's Lean 4 formalisation (`erdos_617_r5_unconditional`; the D1–D4 KP discharge; the **7-axiom** profile after this round's kernel-purity migration — the 10 KP-construction facts moved to kernel `decide`, 4 SAT `native_decide` reflections remain) |
| **Part II — Proof B** | *(all sections marked pending author accuracy pass)* |
| 11 | overview, ingredients (BN strict, Brouwer stability), and the gap-graph reduction |
| 12 | the lower frontier P(Q) ≥ 25 (five-part transversal lemma; P = 22, 23, 24 excluded) |
| 13 | the upper frontier P(Q) ≤ 25 (regular branch; BN ⇒ σ ≤ 19; the six-row table; c ∈ {3,4,5}; the E1 correction) |
| 14 | the exact boundary P = 25 (eight signatures; exchange inequality; seven by certified SAT; the eighth by the three-K₃ defect lemma and 2R ≥ 39 vs R ≤ 19) |
| **Part III — Comparison and disclosure** | |
| 15 | comparison of the two proofs (route, inputs, discovery, Lean profiles, mutual review, effort **with honest-comparison caveats**, the interface equivalence) |
| 16 | provenance: status; who did what (incl. the shared-base-model dual-role note); the review chains; what has/has not been verified; **authorship placeholder** |
| App. A | verification methodology: the full audit trail (internal + mutual review, fresh-clone rebuilds, cert replay, kernel-checked equivalence, the 117-seconds independence audit) |
| App. B | the empirical phase-transition data behind Proof A's lemma statements |

## Sources (frozen)

Proof A (unchanged in substance from the v1.1 single-proof dossier):

- statement / N(r) framing: `../PROBLEM.md`; verified results: `../RESULTS.md`
- the reduction (reviewed): `../review_queue/extension-chain.md`
- Lemma [MH″] / [MM] (reviewed, repaired, punch-list-integrated):
  `../review_queue/mh2-gpt56-candidate.md`, `../review_queue/mm-gpt56-candidate.md`
- affine non-extension: `../review_queue/ag-nonextension.md`
- classical input: `../papers/brouwer-kang-pikhurko.md`; Lean campaign: `../FORMAL.md`
- certificates + arithmetic checks: `../data/sat/prim_*`, `../tools/verify_gpt_arith.py`

Proof B (the control experiment; rendered here, pending author pass):

- source proof: `../review_queue/external-candidate-B/candidate-proof.md`
- team-A review of it (SURVIVES; findings E1, A1): `../review_queue/external-candidate-B/review-by-team-A.md`
  and `review-alpha-notes.md`
- context / de-anonymisation / honest-comparison caveats: `two-proofs-context.md`

Cross-verification (Appendix A):

- team-B review of Proof A (SURVIVES ×3): `../review_queue/reviews-received/review-of-our-r5-by-external-team.md`;
  its punch-list integration: `../verification/punch-list-disposition.md`
- fresh-clone rebuild: `../verification/rebuild-2026-07-13/`
- kernel-checked statement equivalence: `../verification/interface-equivalence.md`
  (`lean617/Lean617/InterfaceCross.lean`)
- independent certificate replay (66/66 UNSAT, encoding faithful): `../verification/external-cert-replay.md`

## Status caveat

Per the repository's ground rules and §16 of the paper, this is an **internal** verification
chain — author sessions on both sides, fresh-session adversarial reviewers, exact
recomputation, two Lean formalisations, a mutual hostile review round, and a kernel-checked
statement equivalence. It has **not** yet been refereed by an independent human expert; no
amount of mutual AI review substitutes for that. Neither Lean proof carries a mathematical
hypothesis, but each has a disclosed trust base: **Proof A** trusts 3 standard + 4 SAT
`native_decide` reflection axioms = **7 axioms**. This round's kernel-purity migration
(Task A) moved the 10 KP-construction facts from `native_decide` to kernel `decide`
(dropping the profile from 17 to 7, committed and regression-guarded by
`tools/axiom_allowlist.txt` / `FORMAL.md`); the 4 SAT reflections remain because their
kernel-checked LRAT route cannot yet be bridged to the `CNF.Unsat` shape (a performance
limit), and are independently DRAT-checked. **Proof B** discharges its SAT through
Mathlib's kernel-checked `lrat_proof` and lists **exactly** the 3 standard axioms. The two
formalisations are kernel-certified to be about the identical `google-deepmind/formal-conjectures`
statement at r = 5. The author list and the Proof-B accuracy pass are the two open
publication items; the paper flags both plainly.
