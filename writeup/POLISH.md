# Polish log — `erdos617-r5.tex`, community-norms pass (2026-07-11)

A writing-polish pass against established community norms. **No mathematical content,
no machine-fact numbering, and no honesty/provenance language was altered** (the
repository's "never claim unconditional" rule is binding and was preserved verbatim).
Every edit below was recompiled with `pdflatex` and the build kept clean.

## Norms consulted

1. **Terence Tao, "Advice on writing papers"** (linked from the erdosproblems wiki as
   the community's writing reference). Sub-articles read:
   - *Use the introduction to "sell" the key points* — state merits/novelty; state
     main results prominently; compare/contrast with prior literature; show why the
     result is new; discuss why hypotheses cannot be dropped; outline proof strategy.
   - *Describe the results accurately* — neither overstate nor understate; acknowledge
     limitations openly; distinguish proven from speculative; descriptive section
     titles, not "Step 2".
   - *Organise the paper* — new section at each major turning point; statement before
     proof (milestones as prominent self-contained results); technical material to the
     back.
   - *Motivate the paper* — reader always aware of the near/long-term objective; label
     heuristics; explain the innovation early.
   - *Use good notation* — emphasise important parameters; global notation up front,
     local near use; consistency with the literature; avoid shadowing; TeX macros for
     conflicts; no "cute" notation.
   - *Create lemmas* — modular, "easy to use not easy to prove", self-contained
     statements.
2. **erdosproblems.com forum thread `/forum/thread/671`** (retrieved 2026-07-11 by
   `curl`; the thread is the discussion for *Problem* #671, but its comments are the
   community's paper-formatting guidance). Thomas Bloom and Kevin Barreto describe the
   norms they apply to AI-assisted Erdős write-ups: keep the **title brief**; the
   **abstract ≤ 6 sentences**; **section headings and paragraph breaks used sparingly**;
   rigorous and self-contained; **only standard, conventional terminology** (they call
   out AI-invented terms like "fan"/"template" as a fix target — "check that all
   terminology used is standard conventional terminology in the surrounding
   literature"); **no flashy or uncapitalised lemma titles**; avoid verbosity
   (`Let X,Y,Z be A,B,C, respectively` over three separate `let`s; do not restate
   trivial definitions); use display math sparingly for simple steps.
3. **`papers/erdosproblems-comms.md`** (already in the repo) — AI disclosure required;
   the report is built for verifier hand-off; keep an honesty inventory; site citation
   format; add literature context and method-novelty to raise a solution's value.

## Assessment against the requested dimensions

| dimension | verdict | action |
|---|---|---|
| **Title** | Brief, accurate, honest ("candidate resolution … with machine verification"). The two honesty qualifiers ("candidate", "machine verification") are load-bearing and must stay. | kept as-is |
| **Abstract** | Runs ~10 sentences / 3 paragraphs, longer than Bloom's ≤6-sentence guideline. Every sentence is load-bearing (problem, result, method, by-product, Lean status, the verification-ready framing, signposting), and the honesty framing must appear up front. Cutting it would remove either mathematical content or binding honesty language. | kept as-is by design; reasoning recorded here |
| **Notation consistency** | Already strong: `\Ncap` avoids clashing with the natural-number set; the `r → ρ` rename in §5.6 (with its footnote) is a textbook shadowing fix; `cap-11`, `hitter`, `minority` are all defined (and "minority" is the source paper's own term). No inconsistencies found. Three *unused* draft macros were present. | removed unused macros (below) |
| **Statement-before-proof** | Already strong: Theorems A/B stated in the introduction; Lemmas [MH″]/[MM] stated in §3 before their proofs in §5–6; descriptive section/subsection titles throughout. | no change needed |
| **Introduction structure** (context → statement → method comparison → *"what insight allowed success where prior methods failed"*) | The first three were present; the fourth — the explicit "why the earlier method stalls and what we do instead" — was **only implicit** (scattered across §1.2, §5.7, App. A). | **added a dedicated subsection** (below) |
| **Citation completeness/format** | The one external theorem (Brouwer 1981) was cited only to an unfetchable 1981 technical report; the *secondary source actually consulted* for its statement (`papers/brouwer-kang-pikhurko.md`) was uncited; load-bearing refs lacked DOIs. | added the secondary source + DOIs (below) |

## Edits made (all compile-clean)

1. **Preamble — removed three unused draft macros** (`\alphanum`, `\Kfree`, `\todo`).
   The `\todo` macro in particular signalled draft state. No rendered output changes.
2. **Introduction — new subsection §1.4, "Why $r=5$ resists the earlier method"**
   (inserted between *Results* and *Method and provenance*). This is the substantive
   addition and the one the brief flagged as possibly weak. It explicitly answers *what
   insight let this succeed where the earlier method fails*, drawn entirely from
   already-established repository material (RESULTS R6/R9, §5.7, App. A) — **no new
   mathematical claim**:
   - *Why the $r=3,4$ method stops:* Erdős–Gyárfás analyse a minority colour class
     directly via Brooks + a single Ramsey number with a unique extremal graph; at
     $r=5$ the Ramsey inputs proliferate with no anchoring extremal structure, and the
     matching upper bound needs a projective plane of order $6$, which does not exist.
   - *What replaces it:* the vertex-deletion **reduction** turns the problem into two
     statements about a single graph; **one** classical input (Brouwer + Kang–Pikhurko)
     drives a uniform recursion in place of case-by-case Ramsey analysis; only four
     ≤12-vertex facts go to SAT; and the lemma thresholds were **read off the empirical
     phase transition** — hitter configurations die at exactly $n=25$, the "+1" costing
     one vertex of slack, resurfacing in-proof as $21 = 4\cdot5+1$.
   This complements (does not duplicate) the following *Method and provenance*
   subsection, which gives the layer-by-layer breakdown and the AI-provenance
   disclosure; the two are cross-referenced.
3. **§4 (toolkit) — footnote on Theorem 3.4 (Brouwer)** recording that Brouwer's 1981
   report is not readily available online and that the bound is quoted in the form
   stated and attributed to Brouwer by Ren–Wang–Wang–Yang (arXiv:2404.07486), with the
   equality classification taken from the primary Kang–Pikhurko source. This matches
   the verification actually done in `papers/brouwer-kang-pikhurko.md` and improves the
   report's checkability.
4. **§10 (provenance) — cited the secondary Brouwer source** where the text already
   referred to "a secondary statement of Brouwer's bound".
5. **Bibliography** — added the DOI to `[ErGy99]` and `[KP05]`, and added the new
   reference `[RWWY]` (Ren, Wang, Wang, Yang, *Extremal triangle-free graphs with
   chromatic number at least four*, arXiv:2404.07486, 2024 — author list and title
   verified against the arXiv page 2026-07-11). Existing `\cite` keys and their numbers
   are unaffected (bibliography uses keys; RWWY appended last).
6. **§2 — inserted an `\allowbreak`** inside the unbreakable Lean identifier
   `erdos\_617\_r5\_upstream` to clear a pre-existing 24 pt overfull `\hbox` (present in
   the baseline). No rendered text changes; the identifier is unchanged. Largest
   remaining overfull is now 13.5 pt.

## Deliberately NOT changed

- **All mathematical content**, every equation, table, and proof step — untouched.
- **The machine-fact numbering** (Fact 3.x, items (M1)–(M4)) and all theorem/lemma
  numbers — untouched (no numbered environment was added or removed; the new material
  is plain prose, so no cross-reference shifted).
- **The honesty/provenance language** — the "verification-ready report, not an authored
  announcement" framing, the "sorry-free *modulo* BrouwerFacts + four SAT axioms"
  wording, the "internal review chain / not independently refereed" caveats, and the
  "what has and has not been verified" section — preserved verbatim. The added intro
  subsection and Brouwer footnote are consistent with, and reinforce, that framing.
- **The abstract and title** — see the assessment table above.

## Compile status

`pdflatex erdos617-r5.tex` (×2): **clean** — exit 0, no errors, no undefined
references, no undefined citations. Output: `erdos617-r5.pdf`, **24 pages** (was 23;
the new subsection added one page). Largest overfull `\hbox` 13.5 pt (under the ~14 pt
bar the README states).
