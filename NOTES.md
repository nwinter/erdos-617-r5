STATUS (2026-07-12, D-CAMPAIGN COMPLETE): **`erdos_617_r5_unconditional : Main` — the Lean result carries NO mathematical hypothesis.** Runners 17–21 proved `KPEqualityClassification` in Lean (D1 cone extraction, D2 forced-c=4 descent 21→17→13→9, D3 `coneExtend` join-transport, D4 the (2,9) base classification by pure local counting). Orchestrator re-verified on tracked HEAD 3fb4ca4: full build 8497 jobs exit 0, sorry_grep PASS, axiom_audit PASS (17 axioms: 3 standard + 4 SAT + 10 KP-construction native_decide; no sorryAx), Statements.lean/verify.py byte-identical to v1.0. See RESULTS.md R12, FORMAL.md "D-CAMPAIGN COMPLETE". Next: writeup flip (R2 refresh, agent spawned), v1.1 public export, then the owner go-live checklist (OUTREACH-DRAFTS.md). Honesty framing unchanged: AI-authored, machine-checked, no human referee yet — "unconditional" refers to mathematical hypotheses only, never skip the native_decide/AI-authorship caveats.

PREVIOUS STATUS (2026-07-12, runner 17): D-CAMPAIGN IN PROGRESS — proving KPEqualityClassification (D1-D4) to make erdos_617_r5 unconditional modulo SAT reflections. **D1 (cone extraction, `d1_cone`), D2a (top-level part size c=4, `d2a_deg17`), and D4-prep (`kpG1` + `AB21_kpG1_compl`, the 2nd extremal witness) ALL LANDED sorry-free & axiom-clean** in lean617/Lean617/EqualityProof.lean (NON-aggregated dev file) + KPConstruction/Equality21. KEY INSIGHT: the "forced-c=4 descent" (verified scratchpad/eq21_descent.py) collapses D2 to iterating the (D1,D2a) cone step 3× down 21->17->13->9, then reassembling — see FORMAL.md "D-CAMPAIGN PROGRESS (2026-07-12, runner 17)" for the full roadmap. Remaining: D2b (recurse the descent), base (2,9), D3 (reassemble to kpG/kpG1 iso), D4-finish (aggregate + axiom audit). D2b is the bulk. NB lean617_f7/ is a GITIGNORED scratch worktree — merge milestones to tracked lean617/. Public export v1.0-public is BUILT AND VERIFIED; the D-campaign does NOT block go-live (ships the conditional theorem; v1.1 follows if/when D lands).

PREVIOUS STATUS (2026-07-12): RELEASE PREP — everything done except R1 (BrouwerFacts discharge, relay running) and the owner's R8 decisions. See RELEASE.md (tracker), FORMAL.md (Lean state). DISCHARGE RELAY STATE: BrouwerInduction.lean has 4 sorries (kp_lemma3; kp_caseB_impl some-part<=1 guard [does NOT need max-size: closes via main_ineq + c>=3; Route MI, see FORMAL.md "SINGLETON GUARD — analysis (2026-07-12)"]; old kp_caseB awaiting rewire to the DONE dichotomy kp_caseB_impl; equality21 [its entire citation surface is anchored sorry-free in KPConstruction.lean]). Runner lean-f6f (13th) is on: max-size reduction -> kp_lemma3 -> wiring -> equality21. ORCHESTRATION PATTERN FOR SUCCESSOR SESSIONS: spawn general-purpose runners against FORMAL.md's latest roadmap section, one at a time (or two with explicit file ownership), each: sync lean617_f7 scratch from main, compile-every-edit, merge milestones as F6x commits, >45min-stuck => named sorry + FORMAL.md note, consolidate-clean near budget. On full discharge: aggregator + Final.lean rewire (drop bf), axiom fixture update (KPConstruction native_decide axioms join), RELEASE.md R1+R6+R7 close-out, re-run R11's leanchecker audit, then tag v1.0.

STATUS (2026-07-10): **RESOLVED (internal review chain complete): Erdős Problem 617 holds at r = 5 — no balanced 5-colouring of K_26 exists; N(5) = 25.** See RESULTS.md R9 (main theorem) assembling three adversarially-reviewed links: the chain deduction + [MH″] (R7) + [MM] (R8), with all primitive machine facts DRAT-certified and the one external theorem literature-verified. Proof authorship: the two hard lemmas by gpt-5.6-sol from this session's briefs; deduction, reduction framework, verification infrastructure, and reviews by this session and its subagents.

## Next actions (post-resolution)

1. **Write-up**: assemble a self-contained paper/note from extension-chain.md + the two
   (repaired) candidate proofs + the certificate manifest. Everything needed is in
   review_queue/ and data/sat/prim_*. Include the r=3,4 context and the N(r)=r² picture.
2. **External verification**: this is an internal chain (author + fresh-session reviewers +
   machine checks). Independent human expert review is the required next standard. Consider
   also Lean formalization — the problem has a formal statement in
   google-deepmind/formal-conjectures (erdos_617); the proofs are elementary + finite checks,
   a strong candidate for formalization.
3. **Communication decision (human collaborator)**: erdosproblems.com lists another person
   working on #617 (site comment, accessed 2026-07-05); decide on timing/coordination before
   public claims.
4. Optional cleanups: DRAT certificates for the four primitives (running at time of writing;
   confirm data/sat/prim_*.out show UNSAT + drat-trim VERIFIED); the h4/h4b instances and
   cloud kit are now moot for the main result (keep for the record).

# Working notes

## Questions for the human collaborator

1. **Compute budget decision**: certifying [MH″] (and then [MM]) wants cluster-scale
   cube-and-conquer (march_cu + kissat, expect 10²–10³ CPU-days; DRAT-checkable).
   Worth provisioning? The payoff is settling Erdős 617 at r=5 modulo the second lemma,
   with the deduction already reviewed. Alternatively a hand-proof route exists (below).

## What is PROVED (see RESULTS.md; verification methods recorded there)

- R1: N(5) ≥ 25 (AG(2,5) referee-verified).
- R5 (THEOREM, adversarially reviewed): merged-AG colourings of K_{q²} never extend, q ≥ 3 prime power.
- R2/R3/R4: AG and 120+ sampled balanced K_25s do not extend; K_24 restrictions fail 2-extension.
- Chain deduction (reviewed ACCEPTED): [MH″] ∧ [MM] ⟹ no balanced 5-colouring of K_26.

## What is EVIDENCED but OPEN

- [MH″]: no balanced K_25 + 4-set hitter. h4-witnesses verified at n=17..24; five independent
  searches wall at exactly 24 residual violations at n=25, all through the newest vertex (R6).
- [MM]: no ≤60-edge class with a usable (≤6 own-edge) 5-hitter. All 600+ sampled class-hitters
  span 9–10 own edges. Pure-graph CEGAR non-convergent; needs same treatment as MH″.
- L5′ (alternative single-lemma route via minority density caps): same certification barrier.

## Successor playbook (in value order)

1. **Hand-proof of [MH″] via the deficiency-1 structure.** Empirics: in every near-floor state
   the unsatisfied hitter 5-sets all contain one common vertex. Suggested lemma shape: in a
   balanced K_25 with α(G_0 − T) ≤ 4 (|T|=4), count colour-0 edges forced OUTSIDE T's
   neighbourhood — the 21-vertex remainder needs α(G_0[rest]) ≤ 4 which forces ≥ μ edges (μ(21)
   witness has 80; exact μ unknown) while cap-11 and the OTHER four classes' α ≤ 5 constraints
   compete for the same pairs. The floor-24 snapshot (data/candidates/h4_floor25_exact.json,
   bounded run may still be writing) records exactly which 5-sets resist — read it first.
2. **Cluster cube-and-conquer for [MH″]** (if budget granted): use data/sat/r5_n25_h4b.cnf
   (sound single symmetry cut), split with march_cu to ~10⁴ cubes, kissat each with DRAT,
   drat-trim check, then lift to the uncut instance or re-verify WLOG soundness (documented in
   tools/probe_h4b.py). Then the same machinery for [MM] (tools/monolith.py mm — full-cap
   variant; do NOT run two monoliths concurrently on <96GB RAM).
3. **[MM] strengthening**: if its pure-graph form is SAT (CEGAR was converging toward models),
   re-pose WITH colouring context like MH″ (add the four other classes as variables) — bigger
   but the WLOG/structure may make it behave like h4b rather than the free-graph version.
4. **W1 (counterexample) is de-prioritized**: every structured and random corner sampled dies
   at the same tightness. If attempted anyway: the h4-witness colourings at n=23/24 are the
   most exotic objects found — try extending THOSE to K_25+x/K_26 (they evade the usability
   obstruction pattern... at their own n; extend.py works for any n).
5. Housekeeping: tools/ are documented in each file's docstring; verify.py untouched (referee);
   .venv has pysat; ext/drat-trim built; data/candidates/ holds all witnesses (referee-verified).

## Tooling facts (hard-won)

- locsearch(_h4).c: ~0.3ms/step; noise 10; warm-chaining n→n+1 is ~1000× faster than cold.
- kissat ≫ cadical-pysat for monoliths; but SAT-side of this family belongs to local search.
- pkill -f patterns match Monitor command strings (kills monitors!) — use exact binary names.
- Monitors do not survive session restarts; tracked background Bash tasks notify reliably.
- Two >4GB CNFs cannot run concurrently in 64GB (learned-clause growth); solo is fine.
- pysat CardEnc: always bump pool.top by enc.nv (spurious-UNSAT bug documented in ATTACKS.md).
