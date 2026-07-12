This is a serious, independent research attempt on Erdős problem 617 (erdosproblems.com/617). It is the first of a small number of parallel attempts; later attempts, if any, will start from different assigned directions. So commit to this lane rather than hedging across every possible approach - a lane that dies cleanly, with its failure documented in ATTACKS.md, is a useful outcome.

Read CLAUDE.md and PROBLEM.md first, in full. PROBLEM.md is the definition of done. Before any other work: re-derive its worked examples yourself, and run tools/verify.py --selftest. If your reading of the problem ever disagrees with a worked example, your reading is wrong.

Your assigned lane (computational-structural, r equal to 5):

1. Build the search infrastructure. Encode the r=5 case - a 5-colouring of the edges of K_26 in which every 6 vertices see all 5 colours - as SAT or constraint problems with aggressive symmetry breaking (vertex relabelling, colour permutation), and separately as local-search optimisation (maximise the number of 6-subsets seeing all 5 colours, with incremental scoring in your own search code; verify.py is the referee, not the engine).
2. Warm-start from structure. Investigate algebraic colourings - finite geometry over GF(5), the affine plane of order 5 on 25 points, Cayley and rotational colourings of K_25 and K_26 - as candidate near-balanced colourings. Measure how close each gets and study exactly where they fail.
3. Decide small cases computationally. Find the largest n such that K_n admits a balanced 5-colouring, pushing n upward from small values; establishing the exact frontier even well below 26, with UNSAT certificates, is a verified result worth recording in RESULTS.md. Extract structural patterns from optimal and near-optimal colourings.
4. Convert structure into mathematics. Any empirical regularity (forced colour-degree bounds, forced local structure) should be stated precisely as a conjecture, tested on small cases first, and then proved as a lemma if it survives. Queue candidate proofs in review_queue - do not self-certify.

Retrieve the Erdős-Gyárfás 1999 paper early (see papers/known-results.md for leads): their r=3,4 proofs and their balanced colourings of K_r_squared are the closest known structures to the target, and their methods define the known frontier. Record what you actually find in papers/ with links and retrieval dates.

Tractability context, all true as of July 2026: long-tail Erdős problems with finite certificates are exactly the class where AI systems have produced genuinely new, expert-verified mathematics in the past twelve months - Erdős problem 728 was resolved via a GPT-5-series model plus Lean verification in January 2026, and the Erdős unit-distance conjecture was disproved by an explicit construction from a reasoning model in May 2026, verified by a panel including Gowers, Alon and Sawin. For this problem, Erdős and Gyárfás settled r=3 and r=4 by hand; as far as the literature we have checked shows, r=5 has never been seriously attacked computationally. Both outcomes at r=5 are wins: an explicit balanced colouring of K_26 disproves the full conjecture, and a proof or certified UNSAT result that none exists settles a new case.

Rules of engagement:
- No survey of the problem's history, no remarks about difficulty or fame. Your output is work.
- Falsify before proving: every conjectured lemma or construction gets tested by code on small cases before proof effort is spent.
- Every load-bearing claim gets one of: a citation you actually retrieved and checked (notes in papers/), a computation reproducible from this repo, or an entry in review_queue awaiting adversarial review. Confidence is not evidence.
- Run tools/verify.py on every candidate colouring the moment it exists. Never modify verify.py.
- Checkpoint to NOTES.md (STATUS line at top), ATTACKS.md, RESULTS.md as you go. Write for a successor session with no memory of this one. Commit often.
- If you reach a natural pause, do not stop to ask - choose the next highest-value action yourself and continue. If a question genuinely needs the human collaborator, leave it at the top of NOTES.md and continue on other threads. This session has no token limit. End only when you are out of productive moves, leaving NOTES.md in a state a successor session can resume from.

Deliverables, best first:
1. A balanced 5-colouring of K_26 that passes tools/verify.py (disproves the conjecture).
2. A proof, or solver-generated certificate that survives independent checking, that no balanced 5-colouring of K_26 exists (settles the r=5 case).
3. Verified smaller results: the exact balanced-colouring frontier for small n, proved lemmas, verified structural constraints that shrink the search space.
4. A clean, documented dead lane in ATTACKS.md.

Begin.
