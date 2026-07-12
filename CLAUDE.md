# erdos-617

A serious research attempt to resolve Erdős Problem #617 (the Erdős–Gyárfás balanced-colouring conjecture), focused on the first open case $r=5$: does $K_{26}$ admit a 5-colouring in which every 6 vertices see all 5 colours?

**PROBLEM.md holds the exact statement, pinned definitions, and worked examples. It is the definition of done.**

## Ground rules

1. **PROBLEM.md governs.** Re-derive its worked examples before any other work. If your reading of the problem ever disagrees with a worked example, your reading is wrong.
2. **Falsify before proving.** Every conjectured lemma or construction gets tested computationally on small cases before proof effort is spent on it.
3. **`tools/verify.py` is ground truth** for candidate colourings. Never edit it. If you believe it is wrong, write your reasoning in NOTES.md and stop for review. It is the referee, not the search engine — search code should implement its own incremental scoring and call the referee on candidates.
4. **State lives in files**, written for a successor session that has no memory of this one:
   - `NOTES.md` — current best thinking. Keep a one-line `STATUS:` at the top and a "next actions" list.
   - `ATTACKS.md` — every failed or abandoned approach, and *why* it failed. A dead end documented is progress.
   - `RESULTS.md` — verified statements only. Each entry records its verification method (script run with command line, citation actually retrieved, or completed review) and date. Nothing enters on confidence alone.
   - `review_queue/` — candidate proofs awaiting adversarial review by a fresh session. Nothing moves from here to RESULTS.md by its author's own judgement.
   - `papers/` — notes on retrieved literature, each with source link and retrieval date. Distinguish VERIFIED (you read the source) from LEAD (recollection or secondhand).
5. **The unit of victory is the smallest new true statement.** A verified partial result beats an unverified whole.
6. **Never claim "proof complete."** Claim "candidate, awaiting review" and queue it.
7. **Commit early and often** with plain descriptive messages. The git log is part of the research record.

## Verified problem facts (checked against erdosproblems.com, 2026-07-05)

- Conjecture of Erdős and Gyárfás [ErGy99]; open; site status FALSIFIABLE (a finite counterexample would settle it).
- Proved for $r=3$ and $r=4$ [ErGy99]. False for $r=2$ (pentagon colouring of $K_5$; equivalently $R(3,3)=6$).
- The property fails for infinitely many $r$ if $r^2+1$ is replaced by $r^2$ [ErGy99] — so balanced r-colourings of $K_{r^2}$ exist infinitely often, and any proof must use the "+1" crucially.
- A formalised statement of the problem exists (site metadata `formalized: yes`, updated 2026-01-24) — useful for definition-pinning.
