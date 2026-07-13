# Erdős Problem 617 at r = 5 — a machine-checked candidate resolution

This repository contains a **candidate resolution of the first open case (r = 5)**
of the Erdős–Gyárfás balanced-colouring conjecture
([Erdős Problem 617](https://www.erdosproblems.com/617)):

> **Theorem (candidate).** There is no balanced 5-colouring of $K_{26}$. Equivalently,
> every 5-colouring of the edges of $K_{26}$ has 6 vertices whose induced $K_6$ omits
> at least one colour; equivalently $N(5) = 25$.

The proof is formalized in **Lean 4 + Mathlib**. The final theorem
`erdos_617_r5_unconditional : Main` is `sorry`-free and carries **no mathematical
hypothesis**: the classical Kang–Pikhurko (2005) equality classification of the extremal
Turán graphs at $(r,n) = (5,21)$ — on which the result was previously conditional — is now
itself **proved** in Lean, via a cone-descent $(5,21)\to(4,17)\to(3,13)\to(2,9)$ and a
finite $(2,9)$ base classification. (Brouwer's 1981 Turán bound was already proved.) What
remains in the trust base is fully disclosed and audited: the three standard Lean axioms
plus `native_decide` kernel reflection for four SAT certificates and a handful of finite
graph-construction facts (the same `ofReduceBool` trust base as Lean's `bv_decide`).

> ### Please read this first — what "candidate" means
>
> This is an **internally-reviewed, machine-checked** result that has **not** been
> refereed by an independent human expert. Two honest caveats are load-bearing and are
> spelled out in [the honesty inventory](#what-verified-modulo-means-the-honesty-inventory):
> (1) the entire Lean development — the two central lemmas AND the now-formalized
> Kang–Pikhurko equality classification — was authored by an AI (gpt-5.6-sol and Claude
> sessions) and reviewed only by fresh AI sessions, not (yet) by human referees; and (2)
> the proof rests on `native_decide` (Lean's `ofReduceBool` kernel reflection) for four SAT
> certificates and several finite graph-construction facts — a compiler-level trust
> assumption, disclosed and audited in the axiom profile. The Kang–Pikhurko classification
> the result was previously *conditional* on is now **proved** in Lean, so `Main` no longer
> depends on any mathematical hypothesis — but that removes a mathematical assumption, not
> the two caveats above.
> The repository is built so that **you do not have to trust any of that** — you can
> audit the Lean statement and re-run the machine checks yourself, in the order below.

**New to the problem?** Start with the
[interactive introduction](https://nwinter.github.io/erdos-617-r5/explainer.html) — an
illustrated explainer: the construction that achieves 25 points (with an in-browser
re-verification of all 177,100 six-point sets), the shape of the impossibility proof, the
search data, and the full who-did-what. It was itself adversarially fact-checked against
this repository. (The same self-contained file ships here as
[`explainer.html`](explainer.html) — open it locally from a clone; no network, no build.)

---

## The 15-minute verification path

The highest-value check costs nothing but your attention: **confirm that the Lean
statement really is Erdős 617 at r = 5, and that the proof of it is `sorry`-free and
rests only on the expected axioms.** You do not need to read the 5000-line proof to do
this — you need to read ~200 lines of *statements* and trust Lean's kernel for the rest.

### Step 1 — Audit the statement (no build required, ~10 min)

Read these two short files:

- **`lean617/Lean617/Statements.lean`** (~420 lines, but the load-bearing part is ~120):
  the definitions `colourClass`, `Balanced`, `IsIndep`, `edgeCountIn`; the target
  `Main`; and — crucially — `main_iff_no_balanced` and **`main_imp_upstream`**, which
  proves `Main` implies the [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  statement `erdos_617` specialized to r = 5, over an *arbitrary* 26-element vertex
  type. This is the check that the formalization did not prove a convenient
  mis-statement.
- **`lean617/Lean617/Final.lean`** (~85 lines): the final assembly. The unconditional
  `erdos_617_r5_unconditional : Main` (and its upstream-shaped corollary
  `erdos_617_r5_upstream_unconditional`) is the headline theorem — it discharges the former
  hypothesis with the proved `kp_equality_classification_proven`. The conditional
  `erdos_617_r5 (h : KPEqualityClassification) : Main` remains, for readers who prefer to
  audit the classification separately.

Satisfy yourself that `Main` / `erdos_617_r5_upstream` says what the problem says.
`PROBLEM.md` has the exact problem statement and worked examples to check against.

### Step 2 — Build and run the machine checks (~a few minutes of compute)

```sh
cd lean617
lake exe cache get          # download the pinned Mathlib build (~6 GB oleans; minutes)
# --- obtain the SAT certificates (see "Certificates" below); then: ---
lake build                  # kernel-checks everything, incl. the 4 SAT certs
```

The four LRAT certificates (~815 MB total) are **not** stored in git; obtain them first
by regeneration or download — see [Certificates](#certificates-how-to-obtain-the-815-mb-of-lrat)
below. With the Mathlib cache fetched (`lake exe cache get`) and the certificates present,
a full `lake build` from a fresh clone — compiling every proof module from source and
kernel-checking the four certificates via `native_decide` — took **~4 minutes** end to end
in the fresh-clone test (measured ~254 s on Apple Silicon; of that, the `native_decide`
certificate check alone is ~2 min / ~1.1 GB RAM). A warm rebuild is seconds. Mathlib itself
is **not** recompiled — `lake exe cache get` fetches its prebuilt `.olean`s.

### Step 3 — Axiom audit (expected output shown)

```sh
tools/axiom_audit.sh        # or, directly:  cd lean617 && lake env lean AxiomAudit.lean
```

Every one of the four final theorems must depend on **exactly** these axioms:

```
'Erdos617.erdos_617_r5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Erdos617.unsat_M10._native.native_decide.ax_1_1,
 Erdos617.unsat_M9._native.native_decide.ax_1_1,
 Erdos617.unsat_nonex11._native.native_decide.ax_1_1,
 Erdos617.unsat_nonex12._native.native_decide.ax_1_1]
```

- `propext, Classical.choice, Quot.sound` — the three standard Lean axioms.
- the `native_decide` axioms — the `ofReduceBool` reflection trust base (the same as Lean's
  `bv_decide`): four for the SAT certificates, plus — for the **unconditional**
  `erdos_617_r5_unconditional` — ten for the finite Kang–Pikhurko construction facts (two
  cone-isomorphism witnesses, two A/B complement structures). **17 axioms total.**
- **No `sorryAx`.** `tools/axiom_audit.sh` fails if any `sorry` or any *other* axiom appears.
- The still-available *conditional* `erdos_617_r5 (h : KPEqualityClassification)` takes the
  classification as a hypothesis (so it carries only the 3 standard + 4 SAT axioms); the
  unconditional theorem discharges that hypothesis with the proved
  `kp_equality_classification_proven`, which is where the ten construction axioms enter.

### Step 4 — Sorry gate

```sh
tools/sorry_grep.sh         # source-level check: no real `sorry` in the Lean sources
```

That is the whole trust-transfer: **read ~200 lines, run four commands.** Everything
else is checked by Lean's kernel.

---

## What "verified modulo" means: the honesty inventory

Keep these four points in view; they are the difference between "machine-checked" and
"proved". They are reproduced from `RELEASE.md` and expanded in §9 of the write-up.

1. **The Kang–Pikhurko equality classification is now formalized — but by the same AI
   pipeline, not proved from a textbook and not human-refereed.** The result was previously
   `erdos_617_r5 (h : KPEqualityClassification) : Main`, conditional on the Kang–Pikhurko
   (2005) classification of the extremal $K_6$-free graphs at $(r,n) = (5,21)$ (every
   extremal colour class is isomorphic to the $G((4,4,4,4,4))$ shape). That hypothesis is
   now **discharged in Lean** (`kp_equality_classification_proven`, `Lean617.JoinTransport`)
   by a cone-descent $(5,21)\to(4,17)\to(3,13)\to(2,9)$, a join-transport reassembly, and a
   finite $(2,9)$ base classification — so `erdos_617_r5_unconditional : Main` has **no
   mathematical hypothesis**. Brouwer's 1981 Turán bound (formerly bundled into the same
   hypothesis, the two-field `BrouwerFacts`) was already proved (`kp_saving`, axiom-clean).
   The honest reservation: this discharge is a fresh, load-bearing formalization authored by
   the same AI pipeline as the rest (item 4), reviewed only by AI sessions (item 3), and its
   base/construction steps lean on `native_decide` (item 2). The classification itself is a
   *published, classical result* (`papers/brouwer-kang-pikhurko.md`), so a reader who
   distrusts the new Lean discharge can instead audit the still-exported conditional
   `erdos_617_r5` and supply the classification as a cited hypothesis.

2. **The SAT primitives use `native_decide` (compiler trust).** The four small-graph
   facts (nonexistence of certain α ≤ 2 cap-11 graphs on 11 and 12 vertices; edge lower
   bounds M(9) ≥ 19 and M(10) ≥ 25) are proved by kernel-checking CaDiCaL LRAT
   certificates via `Std.Tactic.BVDecide`'s verified checker, reflected with
   `native_decide`. This trusts the Lean **compiler** (not just the kernel), exactly as
   `bv_decide` does. The certificates are regenerable from scratch (`tools/regen_certificates.sh`);
   the CNFs are emitted from the *same* Lean definitions the proof checks, so there is no
   second, drifting encoding. **The unconditional theorem adds ten more `native_decide`
   axioms** of the same kind: finite facts about the explicit Kang–Pikhurko constructions
   `kpG`/`kpG1` (two cone-isomorphism witnesses and two A/B complement structures) used by
   `kp_equality_classification_proven`. Same `ofReduceBool` compiler trust; each is a decidable
   check on a fixed graph on ≤ 21 vertices.

3. **The review chain is internal.** Correctness rests on: the author sessions'
   self-checks; **fresh-session adversarial reviews** (independent Claude sessions) of
   each informal link; exact recomputation of every table (`tools/verify_gpt_arith.py`);
   SAT confirmation of every small value; a literature agent's retrieval and check of
   the one external theorem; and the Lean formalization itself. **No independent human
   mathematician has refereed this.** That is the appropriate next step, not something
   already done.

4. **Authorship is mixed human/AI and is disclosed in full** (see
   [Provenance](#provenance--authorship-map)). The reduction, the verification/review
   infrastructure, the empirical structure-mining, and the entire Lean formalization
   were done by Claude sessions (operated by the repository owner); the two hard lemmas
   [MH″] and [MM] were authored by gpt-5.6-sol (OpenAI). The owner does **not** claim to
   have personally verified every line; the repository is the verification apparatus that
   lets a third party do so.

---

## The 2-hour path — read the mathematics

If you want to understand *why* it is true, read the three informal proofs, each with
its adversarial review appended:

- **`review_queue/extension-chain.md`** — the elementary reduction: `[MH″]` ∧ `[MM]`
  ⟹ no balanced 5-colouring of $K_{26}$. (Reviewed, ACCEPTED.)
- **`review_queue/mh2-gpt56-candidate.md`** — Lemma **[MH″]** (a 4-set cannot kill all
  independent 5-sets of a colour class of a balanced $K_{25}$). (Reviewed, ACCEPTED
  MODULO repairs, which are applied and marked.)
- **`review_queue/mm-gpt56-candidate.md`** — Lemma **[MM]** (no ≤ 60-edge colour class on
  25 vertices with a "usable" 5-hitter). (Reviewed, ACCEPTED MODULO the one r = 7 repair,
  adopted.)

`writeup/erdos617-r5.tex` is a single self-contained arXiv-style note presenting all of
this for a human reader (compile with `pdflatex`; see `writeup/README.md`).

---

## The completist path — regenerate the SAT certificates from scratch

The four certificates are not trusted blobs; they are regenerable, and the CNFs they
certify are emitted from the shipped Lean definitions:

```sh
tools/regen_certificates.sh              # all four; or e.g.  tools/regen_certificates.sh M9 M10
```

For each primitive this (1) emits the DIMACS CNF from `nonexCNF` / `MCNF` in
`lean617/Lean617/PrimEncoding.lean` — the *same* definitions the proof checks — and
verifies its sha256 against `tools/certgen/checksums.txt`; (2) solves it with CaDiCaL
(`--inprocessing=false`, LRAT); (3) trims/renumbers the LRAT for Lean's checker. Then
`cd lean617 && lake build` re-checks the fresh certificates. `tools/certgen/checksums.txt`
documents the canonical CNF checksums and the reference certificate checksums (with a
note on which are reproducible bit-for-bit). See `FORMAL.md` F3 for the two non-obvious
requirements (`--inprocessing=false` and the trim step) and the full rationale.

The `native_decide` trust base can be avoided entirely at the cost of re-checking the
LRAT proofs with an external verified checker (e.g. `cake_lpr`) against the emitted CNFs;
the CNF checksums in the manifest are what to check against.

---

## Directory map

```
PROBLEM.md         Exact problem statement, pinned definitions, worked examples (the "definition of done").
RESULTS.md         Verified results R1–R10, each with its verification method and date.
FORMAL.md          The Lean formalization campaign ledger (F0–F9): decomposition, design notes, status.
RELEASE.md         Release checklist and the honesty inventory this README reproduces.
NOTES.md / ATTACKS.md   Research record: current thinking; failed/abandoned approaches and why.

lean617/           The Lean 4 + Mathlib formalization (Lean 4.30.0, Mathlib v4.30.0).
  Lean617/
    Statements.lean   Definitions, the target `Main`, statement fidelity (`main_imp_upstream`), chain deduction.
    Final.lean        Final assembly: `erdos_617_r5 (h : KPEqualityClassification) : Main` + upstream corollary.
    MH2Proof.lean     Lemma [MH″], sorry-free (conditional on PrimFacts, BrouwerFacts).
    MMProof.lean      Lemma [MM], sorry-free (conditional on PrimFacts).
    Counting.lean, LTable.lean, LTableExt.lean   The cap-11 counting identities and L/M tables.
    Brouwer.lean, BrouwerProof.lean   The `BrouwerFacts` interface + formal discharge.
    BrouwerInduction.lean   Brouwer's `saving` bound PROVEN (`kp_saving`, axiom-clean).
    KPConstruction.lean, Equality21.lean   The `G((4,4,4,4,4))` witness; `KPEqualityClassification` +
                        `brouwerFacts_of` (assembles `BrouwerFacts` from `kp_saving` + the one hypothesis).
    PrimEncoding.lean, PrimBridge.lean, PrimMBridge.lean, Primitives.lean   SAT primitives: CNF encoding,
                        graph⇄CNF bridges, and `primFacts : PrimFacts` (via the LRAT certificates).
    certs/            The four LRAT certificates (git-ignored, ~815 MB; regenerate or download).
  AxiomAudit.lean     `#print axioms` on the four final theorems (used by tools/axiom_audit.sh).

review_queue/      The three informal proofs + affine non-extension, each with its adversarial review.
papers/            Notes on retrieved literature (Erdős–Gyárfás, Brouwer–Kang–Pikhurko) + comms norms.
writeup/           The arXiv-style write-up (erdos617-r5.tex); compile with pdflatex.
data/              SAT instances/logs, candidate colourings (R1–R6), arithmetic-check outputs.
tools/             verify.py (the referee for candidate colourings) + search/analysis code +
  regen_certificates.sh, axiom_audit.sh, sorry_grep.sh, certgen/   the release verification scripts.
```

`tools/verify.py` is the independent (non-Lean) referee for candidate *colourings*: it
directly checks whether a given colouring is balanced. It is ground truth for the finite
objects in `data/` (e.g. the $K_{25}$ balanced colourings witnessing $N(5) \ge 25$).

---

## Provenance / authorship map

Reproduced from `RESULTS.md` R9/R10.

- **The two hard lemmas** [MH″] and [MM] were **authored by gpt-5.6-sol** (OpenAI, via
  the codex CLI) from self-contained briefs.
- **Everything else** — the chain deduction and reduction framework, all empirical
  structure-mining, brief preparation, the verification/review infrastructure, and the
  **entire Lean formalization** (seven Claude subagent sessions, with gpt-5.6-sol as a
  lemma co-prover) — was done by **Claude sessions**, operated by the repository owner.
- **Verification** of each informal link: exact recomputation of every table; SAT
  confirmation of every small value; literature retrieval and check of the external
  theorem; and independent fresh-session adversarial review.
- **External inputs:** Brouwer's non-partite Turán bound + Kang–Pikhurko equality
  classification (retrieved and read — `papers/brouwer-kang-pikhurko.md`); Turán's
  theorem (via Mathlib).

See `papers/erdosproblems-comms.md` for how the erdosproblems.com community expects
AI-assisted results to be disclosed and submitted — this repository is built to that
standard.

---

## Certificates: how to obtain the ~815 MB of LRAT

The four LRAT certificates (`lean617/Lean617/certs/{nonex11,nonex12,M9,M10}.lrat`,
~340 MB + ~455 MB + ~2 MB + ~19 MB) are **git-ignored** — they are too large for git and
are reproducible. Two ways to get them, in order of convenience:

1. **Download** them from this repository's GitHub **Release** assets (a one-time upload
   by the maintainer), unpack into `lean617/Lean617/certs/`, and check them against
   `tools/certgen/checksums.txt`.
2. **Regenerate** them with `tools/regen_certificates.sh` (needs CaDiCaL). This is the
   trustless option and reproduces the small certificates bit-for-bit; the two large ones
   are re-solved (any valid UNSAT certificate is accepted by the Lean checker).

CI regenerates them from scratch (see `.github/workflows/verify.yml`).

---

## Toolchain, license, CI

- **Lean** 4.30.0 with **Mathlib** v4.30.0 (pinned in `lean617/lean-toolchain` and
  `lean617/lake-manifest.json`). Install via [`elan`](https://github.com/leanprover/elan).
- **CaDiCaL** (any recent version) for certificate regeneration; **Python 3** for
  `tools/verify.py`.
- **License:** Apache-2.0 (`LICENSE`). Mathlib, on which this depends, is also Apache-2.0.
- **CI** (`.github/workflows/verify.yml`): a fast `fidelity` job (build `Statements.lean`
  + sorry gate; no certificates) and a full `machine-check` job (regenerate certificates,
  `lake build`, axiom audit).
