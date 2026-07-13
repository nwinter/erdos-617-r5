# Release checklist — "nothing left to do" tracker for third-party sharing

Target state: a public, self-documenting repository + verification-ready report that a
mathematician can assess without trusting any AI or the owner. Sharing decisions
(will0708 notification, Gray Swan network, arXiv, erdosproblems.com comment) are the
OWNER's; everything below is preparation.

| # | item | owner | status |
|---|------|-------|--------|
| R1 | BrouwerFacts discharge (last formal gap) — or documented-hypothesis fallback with the SAT-shortcut swap if probes land | lean-f6b relay → F6aa/F6ab → D1–D4 (runners 17–21, 2026-07-12) | **DISCHARGED — `erdos_617_r5_unconditional : Main` carries NO mathematical hypothesis.** `BrouwerFacts.saving` (Brouwer's bound) was proven axiom-clean (`kp_saving`, F6aa). The remaining hypothesis `KPEqualityClassification` (the (5,21) KP equality classification) is now itself **PROVEN in Lean** (`kp_equality_classification_proven`, `Lean617.JoinTransport`): the D1–D4 cone-descent `(5,21)→(4,17)→(3,13)→(2,9)` + join-transport reassembly + the `(2,9)` base classification (`base_classification`, closed sorry-free by lean-d5). `Final.lean` exports `erdos_617_r5_unconditional`/`_upstream_unconditional`; aggregator bundles `EqualityProof` + `JoinTransport`. Full `lake build` clean (**8497 jobs, ZERO sorry**); `tools/axiom_audit.sh` **PASS**; `tools/sorry_grep.sh` **PASS**; `leanchecker` on EqualityProof/JoinTransport/Final exit 0. **Axiom profile of the unconditional theorem: 3 standard + 4 SAT `native_decide` + 10 KP-construction `native_decide` witnesses = 17, NO sorryAx.** The conditional `erdos_617_r5 (h : KPEqualityClassification)` remains exported (3 standard + 4 SAT) for readers who prefer to cite the classification. **Net: unconditional modulo the standard axioms + disclosed `native_decide` reflection.** |
| R2 | Write-up: verification-ready report (reframed: owner-not-claiming, verify-in-30-min section, full AI disclosure) | writeup agent | DONE 2026-07-11 (23pp, compiles clean, no-unconditional rule enforced, grep-honesty fix; commits 00981c5/5feda8e/9781c80) |
| R3 | Statement-fidelity cross-review ×2 (different model families) of Statements.lean/Final.lean vs PROBLEM.md vs upstream | to spawn | PASS 2026-07-11 (Opus 4.8 audit + gpt-5.6-sol, independent) — 0 mismatches; see §Statement-fidelity review |
| R4 | Upstream-verbatim theorem: derive the formal-conjectures `erdos_617` r=5 instance literally | integrator | CLOSED-BY-R3 (2026-07-12): transcription verified token-identical (R3, three methods incl. independent model); a literal Lake import of formal-conjectures was assessed and rejected — it pins its own Mathlib and would fork the toolchain for zero semantic gain. Optional future hardening. |
| R5 | Public repo packaging: top-level README (15-min verify path), LICENSE, CI (lake build + axiom audit + sorry-grep), directory map, certificate regeneration script, fresh-clone verification test | repo-pkg agent | **DONE 2026-07-11** (see §Repo packaging below) — **BLOCKER for owner: git history must be purged of the 4 dead `data/sat/prim_*.lrat` blobs before any GitHub push (2 exceed the 100 MB hard limit)** |
| R6 | Final axiom/sorry audit on the release commit; tag v1.0 | integrator | audits PASSED on 30db6f2 (sorry gate, axiom audit, sorryAx=0 independently re-run); tag after writeup delta lands |
| R7 | Prune/attribute: review_queue docs finalized, RESULTS/NOTES/FORMAL cross-links checked | integrator | IN PROGRESS (final pass with the tag) |
| R8 | [owner] choose sharing route(s) and send | OWNER | DECIDED 2026-07-12: clean-history export (built: ../erdos-617-public; **v1.1-public tagged 2026-07-12 evening** — carries the UNCONDITIONAL theorem + flipped writeup; v1.0-public retained as the first commit; exclusion set: the 8 SAT .check/.lratlog logs, copyrighted KP full-text (pointer kept), and OUTREACH-DRAFTS.md (owner-private; added to the exclusion set at v1.1); paper ships as .tex in-repo instead of arXiv). Outreach drafts updated to the no-hypothesis framing. Remaining owner actions: create GitHub repo + push (both tags), attach cert release asset (certs-v1.0.tgz — UNCHANGED and still valid for v1.1: the 10 new axioms are build-time native_decide, not external certificates), send drafts (checklist in OUTREACH-DRAFTS.md). |
| R9 | Wiki-checklist mapping (teorth wiki "AI solved an Erdos problem" + linked docs) | lean-validate agent | IN PROGRESS |
| R10 | Owner's plain-language summary (communicable key ideas) | integrator | DONE 2026-07-11 (OWNER-SUMMARY.md) |
| R11 | Official Lean validation (did_you_prove_it + ValidatingProofs + lean4checker + exploit screen) | lean-validate agent | **PASS 2026-07-11** — see §Official validation run. Build 0 errors; axioms = standard 3 + 4 disclosed SAT native_decide, no sorryAx, `BrouwerFacts` is a hypothesis not an axiom; toolchain-bundled `leanchecker` re-checks all 14 authored modules (exit 0); exploit screen clean. Only caveat unchanged: `BrouwerFacts`-conditional (R1). **[UPDATE 2026-07-12: R1 now DISCHARGED — `erdos_617_r5_unconditional` carries no mathematical hypothesis; a re-audit of the unconditional theorem shows 3 standard + 4 SAT + 10 KP-construction `native_decide` axioms, still no `sorryAx`. This validation snapshot predates the D1–D4 discharge and its 14-module count.]** |
| R12 | Forward/backward citation sweep (ErGy99, KP05) | polish-sweep agent | **DONE 2026-07-11** — sweep clean: no work since 1999 on the balanced conjecture/$g_r(2)$/the r=5 case (novelty holds), Brouwer/KP bound uncorrected in the literature (`BrouwerFacts` input safe); Füredi–Ramamurthi attribution corrected. Log `papers/citation-sweep.md`; see §Citation sweep + writing polish. |
| R13 | Writing polish per Tao advice + forum thread 671 tips | polish-sweep agent | **DONE 2026-07-11** — polished `writeup/erdos617-r5.tex` vs Tao's advice + erdosproblems forum-671 norms (Bloom/Barreto); added intro "why r=5 resists the earlier method" (the explicit insight question), secondary Brouwer cite + DOIs. No math/honesty-language change; compiles clean (24pp). Change log `writeup/POLISH.md`; commit 7c13c8c. |

Notes:
- The "explain it yourself" forum norm applies to POSTING claims; this package is instead
  built for handoff to verifying mathematicians (trust-transferable: statements audit +
  lake build + certificates). Owner explicitly not claiming personal verification.
- Honesty inventory to keep visible in README + report: (i) BrouwerFacts status at release;
  (ii) native_decide trust base for SAT primitives; (iii) internal-only review chain
  (3 fresh Claude sessions + machine checks + literature agent); (iv) authorship map.

## Statement-fidelity review (2026-07-11)

**Overall verdict: PASS — all audited definitions and theorem statements are FAITHFUL. Zero
MISMATCH findings.** The Lean statements in `Lean617/Statements.lean` and `Lean617/Final.lean`
faithfully encode Erdős #617 at r=5 as pinned in PROBLEM.md and as stated by the upstream
`google-deepmind/formal-conjectures` `erdos_617` (specialised to r=5). The one material caveat is
status, not fidelity: the final theorems are conditional on the `BrouwerFacts` hypothesis, which
the code advertises correctly. **[UPDATE 2026-07-12: this snapshot predates F6ab + D1–D4; the
hypothesis is now `KPEqualityClassification` and it is itself PROVEN — `erdos_617_r5_unconditional`
is hypothesis-free. See R1.]** This audit covers *statements only*; it does not re-verify proofs
(kernel-guaranteed given faithful statements + the sorry-free axiom audit below), nor that
`BrouwerFacts` is a true theorem (R1 / literature), nor the SAT CNF-encoding bridges (separate review).

**Method (all three prongs run):** (1) line-by-line semantic audit against (a) PROBLEM.md,
(b) the upstream `erdos_617` text in `papers/ergy99.md` §8, (c) the informal `[MH″]`/`[MM]` in
`review_queue/extension-chain.md`; (2) executable Lean cross-checks (`#print`/`#eval`/`decide`
examples on tiny instances, plus `#print axioms`) — scratch file preserved at
`scratchpad/r3_fidelity/FidelityCheck.lean`, run under `lake env lean` with genuine (non-Classical)
`Decidable` instances so the props actually compute; (3) an independent second model, `gpt-5.6-sol`
via `codex`, which did NOT author these files (input `scratchpad/r3_fidelity/codex_input.txt`, full
output `scratchpad/r3_fidelity/gpt56sol_findings.txt`, verbatim findings below).

### Per-definition / per-theorem verdicts (my audit)

| object | `Statements.lean` | verdict | note |
|---|---|---|---|
| `colourClass` | L41 | FAITHFUL | `Adj u v := u ≠ v ∧ c s(u,v) = k`; the `u ≠ v` guard makes diagonal colours `c s(v,v)` irrelevant; symmetry/looplessness discharged. |
| `Misses` | L50 | FAITHFUL | `∀ u∈S ∀ v∈S, u≠v → c s(u,v) ≠ k` = "no interior edge of S has colour k". Ordered-pair double-quantification is harmless (same Prop; `s(u,v)=s(v,u)`). |
| `Balanced` | L55 | FAITHFUL | `∀ S, #S = 6 → ∀ k, ¬ Misses c S k` = "every 6-subset sees all 5 colours". Correct direction (sees-all, not misses); 6 = r+1. |
| `IsIndep` | L59 | FAITHFUL | `∀ u∈S ∀ v∈S, u≠v → ¬ G.Adj u v` = graph independence. |
| `edgeCountIn` | L63 | FAITHFUL | `(S.sym2.filter (· ∈ G.edgeSet)).card`. `edgeSet` excludes diagonals; `Sym2` collapses `{u,v}` to one element ⇒ each edge counted **once**, no loops. Confirmed executably (sum over colours = C(5,2), not 2·C(5,2)) and by `card_offdiag`/`sum_edgeCountIn_colourClass`. |
| `MH2` | L137 | FAITHFUL | `∀ balanced c:K₂₅, ∀ k, ∀ T (#T=4), ∃ S (#S=5, Disjoint S T, indep in colourClass c k)`. Exactly the negation of "some 4-set T makes α(Gₖ−T) ≤ 4"; matches `[MH″]`. Cardinalities 25/5/4 correct. |
| `MM` | L146 | FAITHFUL | Nonexistence (⟶ `False`) of G on Fin 25 with α(G)≤5, every 6-set ≤11 edges, ≤60 edges, and a 5-set T with α(G−T)≤4 spanning ≤6 own-edges. All six premises + directions match `[MM]`; `IsIndep G S ∧ Disjoint S T` correctly encodes α(G−T). |
| `Main` | L157 | FAITHFUL | `∀ c:K₂₆, ∃ S k, #S=6 ∧ (no interior edge coloured k)` = upstream r=5 shape over `Fin 26`. No 25/26 or 5/6 off-by-one. |
| `main_iff_no_balanced` | L162 | FAITHFUL | `Main ↔ ∀ c, ¬ Balanced c` — confirms `Main` means "no balanced 5-colouring of K₂₆". |
| `main_imp_upstream` | L180 | FAITHFUL | Transports `Main` to the upstream shape over an **arbitrary** 26-element `V` (`Fintype.card V = 5^2+1`, `#S = 5+1`) via any `V ≃ Fin 26` ⇒ using `Fin 26` in `Main` loses no generality. Keeps upstream's `5^2+1`/`5+1` syntactic form (maximally faithful). Dropping upstream's `hr : r≥3` is sound (trivially satisfied at r=5). |
| `erdos_617_r5` | `Final.lean` L36 | FAITHFUL (conditional) | `(bf : BrouwerFacts) → Main`. Honest conditional. |
| `erdos_617_r5_upstream` | `Final.lean` L40 | FAITHFUL (conditional) | `(bf : BrouwerFacts) → (upstream r=5 conclusion over arbitrary V)`. |

Cross-check vs upstream `erdos_617` (ergy99.md §8) at r=5: `main_imp_upstream`/`erdos_617_r5_upstream`
reproduce it token-for-token (`Fintype.card V = 5^2+1`, `Sym2 V → Fin 5`, `∃ S k, #S = 5+1 ∧ ∀ u∈S ∀ v∈S, u≠v → coloring s(u,v) ≠ k`).
(R4 — deriving from the *literally imported* upstream `def` rather than this hand-transcription — remains
the strictly stronger check and is still worth doing, but the transcription is verified identical here.)

### Executable cross-check results (`scratchpad/r3_fidelity/FidelityCheck.lean`, all pass)

- `#print` of `Misses`/`Balanced`/`Main`/`MH2`/`MM` prints bodies identical to the intended shapes above.
- Hand-crafted colourings decide correctly: all-colour-0 triangle **misses** colour 1 and **does not miss** colour 0; all-colour-0 `K₆` is **not** `Balanced`; the `c s(i,j)=(i+j) mod 5` colouring of `K₆` **is** `Balanced` (a genuine non-vacuous positive case, exercising the ∀-6-subset / ∀-colour structure).
- Edge-count once-only: pentagon on `K₅` gives `edgeCountIn (colourClass · 0) = 5`, `(colourClass · 1) = 5`, and `∑_k edgeCountIn = 10 = C(5,2)` — via the real (noncomputable) `edgeCountIn` rewritten by the kernel-proved `edgeCountIn_colourClass`/`sum_edgeCountIn_colourClass`. Double-counting or loop inclusion would have overshot 10. `¬ (colourClass · 0).Adj 0 0` confirms looplessness.
- `Balanced` on `Fin 5` is vacuously `True` (no 6-subsets) — confirms the cardinality quantifier is exactly `= 6`.
- **Axiom audit (`#print axioms`, sorry-free):** `erdos_617_r5`, `erdos_617_r5_upstream`, `lemma_MH2`, `lemma_MM` each depend on exactly `{propext, Classical.choice, Quot.sound}` + the four SAT `native_decide` axioms (`unsat_{nonex11,nonex12,M9,M10}`). `main_iff_no_balanced` and `main_imp_upstream` are pure (`{propext, Classical.choice, Quot.sound}`). **No `sorryAx` anywhere; `BrouwerFacts` never appears as an axiom — it is consumed as an explicit hypothesis.** This matches Final.lean's advertised profile exactly and confirms the entire dependency tree of the final theorems is sorry-free modulo the disclosed `BrouwerFacts` input.

### Independent review — gpt-5.6-sol (verbatim findings; it did not author these files)

> I found no statement-fidelity errors in the requested definitions or theorem statements. The
> cardinalities, quantifier directions, inequalities, and diagonal handling all match the supplied
> mathematics.
>
> `colourClass` — FAITHFUL (diagonal values `c s(v,v)` never create graph edges; symmetry inherited).
> `Misses` — FAITHFUL ("no interior edge of S has colour k"; `u ≠ v` guard makes diagonal colours irrelevant).
> `Balanced` — FAITHFUL ("every 6-subset sees all five colours"; negation and quantifiers correct).
> `IsIndep` — FAITHFUL. `edgeCountIn` — FAITHFUL (Sym2 = one element per edge; edgeSet off-diagonal ⇒ no loop inclusion, no double counting; corroborated by `card_offdiag` and the sum-to-C(|S|,2) lemma).
> Totality of `c : Sym2 V → Fin 5` — FAITHFUL (every in-scope property excludes diagonals; mirrors upstream).
> `MH2` — FAITHFUL (K₂₅; every colour k; every T with |T|=4; independent S with |S|=5; Disjoint S T; equivalent to "no 4-set T makes α(Gₖ−T) ≤ 4").
> `MM` — FAITHFUL (25 vertices; α≤5; every 6-set ≤11 edges; ≤60 total; 5-set T; α(G−T)≤4 via Disjoint S T; T spans ≤6; ⟶ False; all inequality directions correct).
> `Main` — FAITHFUL (exact r=5 specialization of upstream; no 25/26 or 5/6 off-by-one).
> `main_imp_upstream` — FAITHFUL (upstream shape over arbitrary V; `Fin 26` loses no generality; dropped `hr:5≥3` is trivially satisfied).
> Final theorems + `BrouwerFacts` — FAITHFUL, with a status qualification: `BrouwerFacts` is an honest,
> explicit package of substantive graph-theoretic hypotheses (Brouwer saving + Kang–Pikhurko equality
> classification), "not False, not Main, and not a premise manufactured from the coloring under
> consideration"; nat-subtraction `n/r − 1` is safe under `r>0, 2r+1≤n`. "MISMATCH(HIGH) **only if** it
> is represented elsewhere as an unconditional completed Lean proof of Erdős #617 at r=5."

### Carried-forward item (release-honesty, not a fidelity defect)

Both reviewers independently flag the same single caveat: the final theorems are `BrouwerFacts → …`.
The Lean code states this honestly (Final.lean docstring "modulo BrouwerFacts"; RELEASE R1 "IN PROGRESS").
**Action for R2/R5 (writeup + README):** ensure no public artifact describes `erdos_617_r5` as an
*unconditional* proof; state the `BrouwerFacts` dependency (and the four `native_decide` SAT axioms)
in every honesty inventory. If R1 discharges `BrouwerFacts` (`Lean617.BrouwerProof`), re-run this
axiom audit — the `BrouwerFacts` hypothesis should vanish and the profile reduce to the standard three
plus the four SAT axioms.

## Repo packaging (R5) — done 2026-07-11

Delivered (all commands dry-run locally; the honesty inventory of R5's notes above is
reproduced in `README.md`):

- **`README.md`** — the top-level dossier: the 15-minute verification path (audit
  Statements.lean + Final.lean → `lake build` → `tools/axiom_audit.sh` with the exact
  expected output → `tools/sorry_grep.sh`), the honesty inventory, the 2-hour and
  completist paths, directory map, provenance map, certificate-distribution note.
- **`LICENSE`** — Apache-2.0 (verbatim, from the Mathlib copy; Mathlib is also Apache-2.0).
- **`.github/workflows/verify.yml`** — two jobs: `fidelity` (fast: `lake build
  Lean617.Statements` + sorry gate, no certs) and `machine-check` (regenerate certs +
  full `lake build` + axiom audit). Cannot run Actions locally; YAML validated and every
  step's command dry-run locally.
- **`tools/regen_certificates.sh`** + **`tools/certgen/`** (`emit_cnf.lean`,
  `trim_lrat.lean`, `checksums.txt`) — regenerate the four LRAT certs from the shipped
  `PrimEncoding.lean` CNF definitions. **Validated:** M9 and M10 regenerate **bit-for-bit
  identical** to the shipped certs (sha256 match); CNF checksums verified against the
  manifest.
- **`tools/axiom_audit.sh`**, **`tools/sorry_grep.sh`**, **`lean617/AxiomAudit.lean`** —
  the gate scripts (both pass locally; audit output = the standard three axioms + the four
  SAT `native_decide` axioms, no `sorryAx`, `BrouwerFacts` absent — matches the R3 review).

Measured facts (Apple Silicon, this machine): full `native_decide` recheck of all four
certs = **~127 s, ~1.1 GB peak RAM** (so full verification is feasible on standard
runners); `lake build` warm-replay ≈ 10 s.

### Fresh-clone acid test — PASSED

`git clone file://…` to a temp dir, then followed the README verbatim (Mathlib via
`lake exe cache get`; certs supplied = the "download" path). Results: clone succeeds and
every README-referenced file is present; certs correctly absent until supplied, then
sha256-match the manifest; **`lake build` from the clone's own source (all proof modules
compiled fresh + the four native_decide checks) completed in ~254 s / ~4 min**;
`tools/axiom_audit.sh` PASSED (fixture-based; standard three + four SAT native_decide, no
sorry); `tools/sorry_grep.sh` PASSED; `tools/regen_certificates.sh M9` regenerated the
certificate from the clone's built `PrimEncoding` to the identical sha256. The oversized
blobs remain in the clone's history (confirming the push blocker above). Nothing needed
fixing beyond wording (the build-time figure) and one internal README anchor.

Expected-axioms are now a single fixture `tools/axiom_allowlist.txt` (per team-lead: if R1
discharges BrouwerFacts and its proof adds axioms, it's a one-line edit there — the audit
reads the fixture; verified it rejects any axiom not listed and any sorry).

### Personal-info scan (repo will be public)

- **No owner PII** in tracked files: no `nick@grayswan.ai`, no `grayswan`, no `/Users/winter`
  paths remain. The **one** finding — `scratchpad/r3_fidelity/gpt56sol_findings.txt` had 17
  `/Users/winter/research/erdos-617/…` absolute paths in its markdown links (added by the R3
  commit) — was **sanitized** to repo-relative paths (content otherwise unchanged). Listed
  here per the "report, don't silently scrub" rule.
- Only other emails in tracked files are `kang@…`, `pikhurko@…` in
  `scratchpad/kp_proof.txt` — the published Kang–Pikhurko paper's author contacts (benign
  academic info, part of the extracted proof text). Left as-is.

### Cleanups performed (all reversible; files kept on disk)

`git rm --cached` (untracked, still gitignored + on disk): the two compiled binaries
`tools/locsearch{,_h4}` (built from tracked `.c`); `scratchpad/poc/poc.{cnf,drat,lrat}`;
and the four **dead** `data/sat/prim_*.lrat` certs (superseded per FORMAL.md F3 — the
drat-trim `-L` gapped-id versions Lean cannot use; the working certs live git-ignored in
`lean617/Lean617/certs/`). `.gitignore` extended to cover all of these.

### ⚠ BLOCKER for the owner — purge git history before the first GitHub push

`git rm --cached` removes those blobs from the **tip** tree only; **history still contains
them**, and two exceed GitHub's **100 MB per-file hard limit** (`prim_nonex12.lrat` 344 MB,
`prim_nonex11.lrat` 257 MB; `.git` is ~1.2 GB). **GitHub will reject the push until history
is rewritten.** These certs are dead weight (unusable + regenerable), so purge them
entirely — this keeps the rest of the research-record history intact:

```sh
# from a FRESH clone/mirror, with no other agents working; rewrites all commit hashes:
pip install git-filter-repo
git filter-repo --invert-paths \
  --path data/sat/prim_nonex11.lrat --path data/sat/prim_nonex12.lrat \
  --path data/sat/prim_M9_ge19.lrat --path data/sat/prim_M10_ge25.lrat
# then re-add the remote and force-push the cleaned history.
```

(Alternative if the blobs must be retained: `git lfs migrate import --include="data/sat/prim_*.lrat"`
— also rewrites history, and adds LFS bandwidth/storage friction. Not recommended for dead files.)
This is a destructive history rewrite and an owner decision (ground rule 7 values the git
log), so it was NOT executed here.

### Certificate distribution (the ~815 MB working certs)

`lean617/Lean617/certs/*.lrat` (~340 + 455 + 19 + 2 MB) stay git-ignored. Recommended:
attach them to a GitHub **Release** (owner uploads once) for a fast download path, and keep
`tools/regen_certificates.sh` as the trustless regenerate-locally path. CI regenerates them
from scratch, so it needs no release asset.

## Official validation run (2026-07-11)

Ran the official leanprover-community "Did you prove it?" checklist
(`leanprover-community.github.io/did_you_prove_it.html`) and the Lean reference
manual's "Validating a Lean Proof" escalation ladder
(`lean-lang.org/doc/reference/latest/ValidatingProofs/`) against `lean617/` (final
theorems `Erdos617.erdos_617_r5` and `erdos_617_r5_upstream` in
`Lean617/Final.lean`), plus a disclaimer-8 exploit screen
(`teorth/erdosproblems` wiki). Toolchain `leanprover/lean4:v4.30.0`; Mathlib pinned
`v4.30.0` (rev `c5ea0035…`). Every command below was executed on this machine.

**OVERALL: PASS.** Repo compiles clean (0 errors); the four final theorems' only
axioms are the standard three (`propext`, `Classical.choice`, `Quot.sound`) plus the
four disclosed SAT `native_decide` reflections; **no `sorryAx`**; `BrouwerFacts` is
an explicit `structure … : Prop` hypothesis, **never an axiom**; the
toolchain-bundled `leanchecker` (the in-Lean successor to `lean4checker`) re-checks
**all 14 authored modules through the kernel with no error**; and the exploit screen
is clean (no `unsafe` / `@[implemented_by]` / `@[extern]` / `partial def` /
custom-axiom / notation-override / custom-`Decidable`-instance). The one honest,
already-advertised caveat is unchanged and is a matter of *status, not fidelity*: the
finals are conditional on `BrouwerFacts` (R1 IN PROGRESS), and the four native_decide
axioms are a native-compiler trust base (identical to Mathlib's `bv_decide`),
separately justified by the regenerable LRAT certificates.

### did_you_prove_it.html checklist — item by item

| # | check | result |
|---|-------|--------|
| 1 | code in a correctly-formatted Lean repository (a stray file is not enough) | **PASS** — `lean617/` is a Lake project: `lakefile.toml`, `lean-toolchain` (`leanprover/lean4:v4.30.0`), `lake-manifest.json` (Mathlib pinned `v4.30.0`, rev `c5ea0035…`; aesop/Qq/Cli also `v4.30.0`), root `Lean617.lean` importing every module incl. `Lean617.Final`. |
| 2 | repository compiles (`lake build`, no errors) | **PASS** — `lake build Lean617.Final Lean617` → `Build completed successfully (8490 jobs)`, exit 0, ~10 s warm replay. **Zero `error` lines**; output is only Mathlib *lint warnings* (push_neg deprecation, `show`→`change`, header/long-line style, "native_decide not allowed in mathlib" style lint) — none affect soundness. |
| 3 | the proof is actually being checked (main-theorem file in the build) | **PASS** — `Lean617.lean` (the default target) does `import Lean617.Final`; the build log shows `Replayed Lean617.Final` → `Built Lean617`. The four final theorems are elaborated and kernel-accepted by the build itself. |
| 4 | `#print axioms` ⊆ {propext, Classical.choice, Quot.sound} (+ documented extras) | **PASS with disclosed extras** — verbatim audit below. Each final = the standard three **plus exactly four** `native_decide` axioms. **No `sorryAx`. No `Lean.ofReduceBool` / `Lean.trustCompiler`. `BrouwerFacts` absent** (explicit hypothesis, not an axiom). |
| 5 | does the work prove what is claimed | **PASS (statements audited)** — see **RELEASE R3** (statement-fidelity cross-review, 2026-07-11: Opus 4.8 + independent gpt-5.6-sol, 0 MISMATCH; `Statements.lean`/`Final.lean` faithfully encode Erdős #617 at r=5 vs PROBLEM.md and the upstream `erdos_617`). Re-confirmed here by printing the kernel-accepted statements (below). The `BrouwerFacts` conditionality is stated honestly in-code. |

### Axiom audit — verbatim (`lake env lean AxiomAudit.lean`)

```
'Erdos617.lemma_MM' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Erdos617.unsat_M10._native.native_decide.ax_1_1,
 Erdos617.unsat_M9._native.native_decide.ax_1_1,
 Erdos617.unsat_nonex11._native.native_decide.ax_1_1,
 Erdos617.unsat_nonex12._native.native_decide.ax_1_1]
'Erdos617.lemma_MH2'          depends on axioms: [ …identical 7-axiom profile… ]
'Erdos617.erdos_617_r5'       depends on axioms: [ …identical 7-axiom profile… ]
'Erdos617.erdos_617_r5_upstream' depends on axioms: [ …identical 7-axiom profile… ]
```

All four finals share the **same** profile: `{propext, Classical.choice, Quot.sound}`
+ four SAT axioms. The axioms are the Lean-4.29+ **per-computation** form
`…_native.native_decide.ax_1_1` (one dedicated axiom per `native_decide` call), *not*
the older monolithic `Lean.ofReduceBool` / `Lean.trustCompiler`. The four names map
one-to-one to the four `native_decide` sites in `Primitives.lean` (L29/32/35/38):
`unsat_nonex11`, `unsat_nonex12`, `unsat_M9`, `unsat_M10` — the UNSAT reflections of
the four CNF instances, each discharged by Lean's own verified LRAT checker
`Std.Tactic.BVDecide.Reflect.verifyCert` on an embedded certificate. **Nothing else
entered the axiom set.** `BrouwerFacts` does **not** appear — it is consumed as the
explicit hypothesis `(bf : BrouwerFacts)`.
(Doc nit for a future edit, not a defect: the `Final.lean` / `Primitives.lean`
docstrings still describe the SAT trust base as `Lean.ofReduceBool`; the toolchain
actually emits the four per-computation axioms above. Same native-compiler trust,
cleaner externally-checkable form.)

### lean4checker / leanchecker (Re-Checking Proofs — ValidatingProofs §3)

**Version note (material):** the standalone `leanprover/lean4checker` repo is
**deprecated and being archived** — per its own README, "lean4checker has been merged
into the Lean 4 repository itself, and is now distributed as `leanchecker` with every
Lean toolchain (starting from v4.28.0)." Its latest tag is `v4.29.0-rc8` — **there is
no `v4.30.0` tag**. We therefore used the **toolchain-bundled `leanchecker`**
(`…/leanprover--lean4---v4.30.0/bin/leanchecker`, invoked via `lake env leanchecker`).
This is the exact-version-matched official checker — built from the same v4.30.0
source as the kernel that produced our `.olean`s — which is *strictly stronger* than
building the deprecated repo against a mismatched toolchain, and is the same tool
`lean-action`'s `lean4checker: true` CI step now runs. It re-reads the compiled
`.olean` declarations and **replays them through the Lean kernel**.

**Verdict: PASS — all 14 authored modules re-check with exit 0, no errors.**

| module | exit | time | | module | exit | time |
|---|---|---|---|---|---|---|
| Statements | 0 | 10 s | | PrimBridge | 0 | 9 s |
| Counting | 0 | 9 s | | PrimMBridge | 0 | 9 s |
| LTable | 0 | 9 s | | Primitives *(native_decide)* | 0 | 11 s |
| LTableExt | 0 | 9 s | | MH2Proof | 0 | 10 s |
| Brouwer | 0 | 9 s | | MMProof | 0 | 23 s |
| BrouwerProof | 0 | 9 s | | Final | 0 | 9 s |
| BrouwerDischarge | 0 | 9 s | | **(14/14)** | **0** | **~141 s total** |

Each module was checked in its **own process** (`lake env leanchecker Lean617.<M>`),
replaying that module's declarations on top of its trusted imports — this covers
every declaration **we authored**, including the native_decide module `Primitives`
and the two large proof files. Mathlib / Lean-core imports are trusted here (standard,
independently-checked infrastructure; re-checking all 10 786 search-path oleans is the
parallel no-arg mode, which additionally re-verifies Mathlib and is out of scope).
A single warm `leanchecker Lean617.Final` alone = exit 0, 45 s.

**Honest operational finding (not a soundness issue):** a first attempt to check all
14 modules in **one** `leanchecker` invocation was **killed by the OS (`exit 137` =
SIGKILL) at 118 s** — multi-module mode accumulates every replayed declaration in one
growing environment and exceeded RAM on this project (the earlier note measured ~1.1 GB
for a single native_decide recheck; 14 modules at once blows past that). This was a
**memory kill, not a kernel rejection** — no error was emitted, and re-running the
modules **individually all pass** (table above). Guidance for CI/reviewers: check
per-module (or use the parallel no-arg mode), not one giant multi-arg call.

**How `leanchecker` handles the native_decide-extended environment (documented per
request):** it **succeeds with no special handling**. Under the Lean-4.29+ scheme each
`native_decide` result is reified as a *declared axiom* (`…native_decide.ax_1_1`);
`leanchecker` replays that axiom as a trusted constant (an axiom has no proof term to
re-check) and kernel-checks every theorem that cites it. It does **not** — and cannot —
re-execute the native SAT computation; that trust lives in the axiom, exactly as the
ValidatingProofs manual states for the post-4.29 mechanism. So `leanchecker` here
proves the **absence of environment-hacking** (no metaprogrammed / kernel-bypassing
declarations) and that every non-native proof kernel-replays; the four SAT axioms
remain the disclosed native trust base, justified separately by the regenerable LRAT
certificates. The `--fresh` mode and the `comparator` + external-checker "gold
standard" (ValidatingProofs §4 — for adversarial proof-marketplace / high-reward
settings) would additionally re-check Mathlib / sandbox a malicious build; they are
not warranted for an honest formalization and were not run — and they would not change
the status of the four native_decide axioms in any case.

### Disclaimer-8 exploit screen (grep of `Lean617/*.lean`)

| pattern screened | expectation | finding |
|---|---|---|
| `axiom` declarations | none (Lean provides its own) | **NONE** in our sources |
| `unsafe` | none | **NONE** |
| `@[implemented_by]` | none | **NONE** |
| `@[extern]` | none | **NONE** (4 hits are the words "external/externally" in comments) |
| `partial def` | none in proof code | **NONE** |
| `macro_rules` / `macro` / `notation` / `syntax` / `infix*` / `prefix` / `postfix` / `elab` | none (could disguise statements) | **NONE** |
| custom `instance` / `deriving` | none | **NONE** (3 "instance" hits are comment prose) |
| custom `Decidable` instances (could make `decide` lie) | none | **NONE** — every `Decidable*` use is a *standard binder* (`[DecidableEq α]`, `[DecidableRel G.Adj]`, `[Decidable P]`) or a `linter.unusedDecidableInType` `set_option`; **zero** custom instances, so `decide`/`native_decide` use only Mathlib/Lean's trusted decidability |
| `sorry` / `admit` / `sorryAx` | none in code | **NONE** (only docstring prose "sorry-free") |
| `Lean.ofReduceBool` / `Lean.trustCompiler` as a real axiom | none | **NONE** (one docstring mention; the real trust base is the 4 per-computation native_decide axioms) |
| attributes used anywhere | benign only | only `@[simp]` (×4) |
| `native_decide` calls | exactly 4 (the SAT reflections) | **exactly 4** — `Primitives.lean` L29/32/35/38 |
| **`BrouwerFacts` is a structure/hypothesis, NOT an axiom** | required | **CONFIRMED** — `Brouwer.lean:181  structure BrouwerFacts : Prop where …`; absent from every `#print axioms`; taken as `(bf : BrouwerFacts)` |

Incidental (flagged for cleanliness, not soundness): a stale `Lean617/AxCheck.olean`
build artifact has no corresponding source and is imported by nothing (not in Final's
closure; `.lake` is git-ignored). `Lean617/Basic.lean` is the untouched lake template
stub `def hello := "world"`, imported nowhere (and has no olean).

### Printed statements — verbatim (`lake env lean StatementPrint.lean`)

Confirms the finals say what R3 audited (item 5), at the level of what the kernel
accepted:

```
erdos_617_r5 : BrouwerFacts → Main
erdos_617_r5_upstream : BrouwerFacts →
  ∀ {V : Type} [Fintype V] [DecidableEq V], Fintype.card V = 5 ^ 2 + 1 →
    ∀ (coloring : Sym2 V → Fin 5),
      ∃ S k, S.card = 5 + 1 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k
lemma_MH2 : BrouwerFacts → MH2
lemma_MM  : MM
Erdos617.Main : ∀ (c : Sym2 (Fin 26) → Fin 5),
  ∃ S k, S.card = 6 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k
Erdos617.Balanced c := ∀ S, S.card = 6 → ∀ k, ¬ Misses c S k
Erdos617.Misses c S k := ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k
structure Erdos617.BrouwerFacts : Prop  (0 parameters)
  fields:  saving      : …K_{r+1}-free, non-r-colourable ⇒ e(G)+(⌊n/r⌋−1) ≤ t_r(n)   (Brouwer)
           equality21  : …the n=21, α≤5, K₅-free, 37-edge equality classification   (Kang–Pikhurko)
main_iff_no_balanced : Main ↔ ∀ (c : Sym2 (Fin 26) → Fin 5), ¬ Erdos617.Balanced c
```

`BrouwerFacts`'s two fields are genuine graph-theoretic statements (Brouwer's saving
bound; the Kang–Pikhurko n=21 equality classification) — not `False`, not `Main`, and
not a premise manufactured from the colouring under consideration; `main_iff_no_balanced`
confirms `Main` means exactly "no balanced 5-colouring of K₂₆."

### Disclaimers 2 / 4 / 6 / 10 → our mitigations

**Disclaimer 2 (many problems lack a thorough literature review; "open" is provisional
— AI has "solved" already-solved problems).** #617 is a *named* Erdős–Gyárfás
conjecture with a real partial-progress trail (proved for r=3, 4; false for r=2; the
"+1" shown necessary), i.e. disclaimer-5's "stronger evidence of difficulty," not an
obscure one-off. Mitigation: the `papers/` literature review with VERIFIED-vs-LEAD
provenance, and — crucially — the whole result is *conditional on* a named classical
input (`BrouwerFacts` = Brouwer 1981 / Kang–Pikhurko 2005) rather than silently
re-deriving it, so the literature dependency is explicit and auditable. Residual risk:
we have not exhaustively searched for a prior *full* resolution of the r=5 case; R1 and
the `papers/` notes track this.

**Disclaimer 4 (Erdős or the site sometimes stated the problem incorrectly; the literal
statement may be a technicality).** Mitigation = right-version fidelity review:
`PROBLEM.md` pins the exact statement + worked examples against erdosproblems.com, and
**R3** cross-reviewed `Statements.lean`/`Final.lean` against both PROBLEM.md and the
upstream `google-deepmind/formal-conjectures` `erdos_617` (specialised to r=5), two
independent model families, 0 mismatches. `main_imp_upstream` transports our `Fin 26`
statement to the upstream arbitrary-`V`, `5^2+1`/`5+1` shape token-for-token — so we
prove the intended question, not an easier lookalike. R4 (deriving from the *literally
imported* upstream `def`) remains the strictly-stronger open check.

**Disclaimer 6 (evaluate holistically; an AI solution may lack surrounding
insight/context).** Acknowledged as the AI-writing caveat: the machine-found proof
ships with a verification-ready report (`writeup/`, README) supplying context,
provenance, and the reduction chain [MH″]→[MM]→SAT, but we do **not** claim it carries
the theory-building value a human paper would; the honesty inventory states the
internal-only review chain (fresh Claude sessions + machine checks + a literature
agent) and full AI authorship. The unit of value claimed is the verified conditional
statement, not a publication-grade contribution.

**Disclaimer 10 (status is provisional — revisable by new literature, found errors, or
reformulation).** Mitigation = the no-rush plan: nothing is asserted "proof complete"
(ground rule 6); the finals are openly conditional on `BrouwerFacts` (R1 IN PROGRESS);
candidate proofs sit in `review_queue/` for fresh-session adversarial review; RESULTS.md
admits only method-verified statements; and the owner explicitly does not claim personal
verification. This validation run is itself provisional evidence, dated and reproducible
(every command is in this section), not a final verdict.

## Citation sweep + writing polish (R12, R13) — done 2026-07-11

**R12 — citation sweep (`papers/citation-sweep.md`).** Forward/backward sweep of [ErGy99]
and [KP05] (the wiki "real literature review — forward+backward citation search" item).
**Clean on both axes.** *Novelty:* no publication since 1999 addresses the balanced
conjecture, $g_r(2)$, or the r=5 case — every forward citation of [ErGy99] is on the *split*
side ($f_r$) or unrelated colouring topics, and direct searches for the quantity return
nothing; corroborated by erdosproblems.com/617 (FALSIFIABLE, "no solutions claimed", last
edited 2026-04-01) and `formal-conjectures` tagging only r=3,4. The r=5 result appears
genuinely new. *Correctness:* the Brouwer(1981)/Kang–Pikhurko(2005) non-r-partite Turán bound
behind `BrouwerFacts` has been reproved/restated (Ren–Wang–Wang–Yang 2024, now cited in the
writeup) and extended (stability-constant, spectral, generalized-book host graphs) but **never
corrected** — no erratum; the exact r=5 application is safe. One bookkeeping correction: the
"Füredi 2002" follow-up is **Füredi–Ramamurthi** (JGT 40(4) 226–237), not Füredi–Gyárfás, and
is split-side; fixed in `papers/ergy99.md` and `papers/known-results.md`.

**R13 — writing polish (`writeup/POLISH.md`).** Polished `writeup/erdos617-r5.tex` against
Tao's "advice on writing papers" and the erdosproblems forum-671 norms (Bloom/Barreto on
AI-assisted write-ups: brief title, terse abstract, standard terminology only, no flashy lemma
titles). **No mathematical content, machine-fact numbering, or honesty/provenance language was
altered.** Substantive addition: a new introduction subsection *"Why r=5 resists the earlier
method"* that explicitly answers the "what insight let this succeed where prior methods failed"
question (drawn from RESULTS R6/R9 — reduction + one Brouwer/KP input + 4 SAT facts; thresholds
read off the empirical phase transition; the "+1" as 21=4·5+1). Also: added the secondary
Brouwer source (arXiv:2404.07486) as a footnote/cite and DOIs to [ErGy99]/[KP05]; removed 3
unused draft macros; cleared a pre-existing 24 pt overfull. Recompiles clean (24 pp, no
undefined refs/cites). Commit 7c13c8c.
