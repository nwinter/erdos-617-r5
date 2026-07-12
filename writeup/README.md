# Write-up: the r = 5 case of Erdős Problem 617

`erdos617-r5.tex` is an arXiv-ready LaTeX note (amsart). It is a **verification-ready
report**, not an authored announcement: it presents a *candidate resolution* of the
first open case (r = 5) of the Erdős–Gyárfás balanced-colouring conjecture —
**there is no balanced 5-colouring of K₂₆; equivalently N(5) = 25** — produced and
internally reviewed by AI systems and offered for independent verification. Section 2
of the paper ("How to verify this report") is the reader's guide to checking it.

## Compiling

The document uses only standard packages (`amsmath`, `amssymb`, `amsthm`,
`mathtools`, `geometry`, `microtype`, `enumitem`, `booktabs`, `array`, `hyperref`,
`xcolor`) and a self-contained `thebibliography` — no `.bib` file, no external
assets. Any modern TeX distribution compiles it.

```sh
pdflatex erdos617-r5.tex
pdflatex erdos617-r5.tex        # second pass resolves cross-references + citations
```

or, equivalently,

```sh
latexmk -pdf erdos617-r5.tex
```

Output: `erdos617-r5.pdf` (~24 pages). The build is clean: no errors, no undefined
references, no overfull boxes above ~14 pt.

## What the paper contains

| § | contents |
|---|----------|
| 1 | the conjecture, its history (ErGy99: r=3,4; false at r=2; the r² vs r²+1 phenomenon), the two main theorems, and the verification-ready framing |
| 2 | **How to verify this report**: a 30-min machine path (statement audit + `lake build` + `#print axioms`), a 120-min reading path, a completist certificate/literature audit, and what is deliberately *not* yet claimed |
| 3 | definitions (balanced, colour class, **cap-11**, hitter, minority), elementary facts, the two lemmas [MH″] and [MM], and the elementary reduction proving the main theorem from them |
| 4 | the shared **cap-11 toolkit**: Brouwer's non-partite Turán theorem + Kang–Pikhurko equality, the counting identity, the neighbourhood bound, the four SAT-certified small-graph facts, the M- and L-tables |
| 5 | proof of Lemma [MH″] (21-vertex reduction; e(Fᵢ)≥38; e(H)≥58; H is K₅-free — the repaired ω-free route; equality; the endgame; why it fails at n=24) |
| 6 | proof of Lemma [MM] (peeling; the {0,1,2,4}-K₅ case split; all four cases, including the repaired ν=7 closure) |
| 7 | Theorem B: merged affine-plane colourings of K_{q²} never extend, all prime powers q≥3 |
| 8 | the four SAT certificates (exact CNF statements, encoding, sizes, solver/checker versions, two independent verification paths, regeneration recipe) |
| 9 | the Lean 4 formalization (what is proved — incl. Brouwer's bound `kp_saving`; the single remaining `KPEqualityClassification` hypothesis; the axiom profile; how to check) |
| 10 | full AI-provenance disclosure, the owner's process-not-content status statement, the adversarial-review chain, and an honest account of what has and has not been verified |
| App. A | the empirical phase-transition data (R6) that motivated the lemma statements |

## Sources (frozen)

The mathematics is transcribed, unchanged, from the repository's research record:

- statement / N(r) framing: `../PROBLEM.md`
- verified results R1–R10: `../RESULTS.md`
- the reduction (reviewed): `../review_queue/extension-chain.md`
- Lemma [MH″] (reviewed, repaired): `../review_queue/mh2-gpt56-candidate.md`
- Lemma [MM] (reviewed, repaired): `../review_queue/mm-gpt56-candidate.md`
- affine non-extension (reviewed): `../review_queue/ag-nonextension.md`
- history/context: `../papers/ergy99.md`
- the classical input: `../papers/brouwer-kang-pikhurko.md`
- the Lean campaign: `../FORMAL.md`
- certificates + arithmetic checks: `../data/sat/prim_*`, `../tools/verify_gpt_arith.py`

The **repaired** versions of the two lemmas (as accepted by adversarial review) are
what the paper presents: the ω-free 11-vertex nonexistence route in §5.4, and the
ν = 7 closure in §6.5.

## Status caveat

Per the repository's ground rules and §10 of the paper, this is an **internal**
verification chain (author sessions + fresh-session adversarial reviewers + exact
recomputation + SAT certificates + a Lean formalization). It has **not** yet been
refereed by an independent human expert, and the Lean development still carries one
classical statement — the Kang–Pikhurko equality classification at (5,21),
`KPEqualityClassification` — as an assumed hypothesis rather than a proved lemma.
(Brouwer's edge bound, formerly also assumed, is now proved in Lean: `kp_saving`,
axiom-clean. The axiom profile is unchanged: 3 standard + 4 SAT-reflection.) The
paper states these points plainly; they are the appropriate next standard, not a
defect hidden in the write-up.
