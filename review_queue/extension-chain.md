# ACCEPTED AND DISCHARGED: the extension-obstruction chain for r=5

Author session: 2026-07-05. FINAL STATUS (2026-07-12): the deduction below was
adversarially reviewed and ACCEPTED (see appended review); both machine
hypotheses were subsequently PROVED — [MH″] and [MM] as informal theorems with
their own adversarial reviews (mh2-/mm-gpt56-candidate.md; RESULTS.md R7/R8),
and then FORMALIZED in Lean sorry-free (lean617/, FORMAL.md). The chain
deduction itself is the Lean theorem `chain_deduction`. Historical candidate
text follows unchanged.

## Statement

**Theorem (candidate).** There is no balanced 5-colouring of $K_{26}$
(equivalently, Erdős Problem 617 holds at $r=5$).

## Machine inputs

- **[MH″] (pending, data/sat/r5_n25_h4.out):** there is no balanced 5-colouring
  of $K_{25}$ together with a colour $c$ and a 4-vertex set $T$ such that
  $\alpha(G_c - T) \le 4$. (WLOG $c=0$, $T=\{0,1,2,3\}$ by relabelling; the SAT
  instance encodes exactly this.)
- **[MM] (pending, data/sat/lemma_m_60.log):** there is no graph $G$ on 25
  vertices with $\alpha(G)\le 5$, every 6-set spanning $\le 11$ edges,
  $e(G) \le 60$, together with a 5-set $T$, $\alpha(G-T)\le 4$, such that $T$
  spans $\le 6$ edges of $G$. (Per review: what the CEGAR run establishes on
  UNSAT is the *subset-capped relaxation* — only the lazily-added 6-set caps
  are present — which implies the fully-capped [MM] a fortiori, and that is
  all step 6 needs.)

## Proof of the Theorem from [MH″] + [MM]

1. Suppose $\chi$ is a balanced 5-colouring of $K_{26}$. Fix any vertex $x$;
   let $V' = V \setminus \{x\}$ (25 vertices) and $\chi' = \chi|_{V'}$, a
   balanced 5-colouring of $K_{25}$ (restriction preserves balance). Let
   $G_0,\dots,G_4$ be the colour classes of $\chi'$ and
   $T_c = \{v \in V' : \chi(xv) = c\}$, a partition of $V'$.

2. For every $c$: $\alpha(G_c - T_c) \le 4$. [If $F$ were an independent 5-set
   of $G_c$ avoiding $T_c$, the 6-set $\{x\} \cup F$ would miss colour $c$:
   inside $F$ nothing is $c$ ($F$ independent in $G_c$), and no edge $xv$,
   $v \in F$, is coloured $c$ ($F \cap T_c = \emptyset$).]

3. Every class of $\chi'$ satisfies: $\alpha(G_c) \le 5$ (an independent 6-set
   is a 6-set missing $c$) and **cap-11**: every 6-set spans $\le 11$ edges of
   $G_c$ (a 6-set with $\ge 12$ edges of one colour has $\le 3$ other edges,
   so sees $\le 4$ colours). Also $\sum_c e(G_c) = \binom{25}{2} = 300$, so the
   minority class $G_m$ has $e(G_m) \le 60$ (minimum $\le$ average $= 60$;
   if several classes tie for minimum, fix any one of them as $m$).

4. By [MH″], no class has a 4-set (hence no smaller set, add arbitrary
   vertices: if $|T|<4$ and $\alpha(G_c-T)\le4$ then any 4-superset $T^+ \supseteq T$
   also has $\alpha(G_c-T^+)\le4$, contradicting [MH″]) killing its independent
   5-sets. Hence $|T_c| \ge 5$ for all $c$. Since $\sum_c |T_c| = 25$:
   $|T_c| = 5$ for every $c$.

5. **Tightness/usability step.** Fix colours $c \ne c'$. $T_{c'}$ is a 5-set
   disjoint from $T_c$. If $T_{c'}$ contained no edge of colour $c$, it would
   be an independent 5-set of $G_c$ avoiding $T_c$ — contradicting step 2.
   So **$T_{c'}$ contains at least one edge of every colour $c \ne c'$**: at
   least 4 pairwise-distinct edges among its $\binom{5}{2}=10$ that are not of
   colour $c'$. Hence $T_{c'}$ spans at most $10 - 4 = 6$ edges of colour $c'$.

6. Apply step 5 with $c' = m$ (the minority colour): $T_m$ is a 5-set with
   $\alpha(G_m - T_m) \le 4$ (step 2) spanning $\le 6$ edges of $G_m$ (step 5),
   inside a graph $G_m$ with $\alpha \le 5$, cap-11, $e \le 60$ (step 3).
   This is exactly a witness to the SAT question of [MM]. By [MM] no such
   configuration exists. Contradiction. $\blacksquare$

## Empirical support (falsification attempts that failed to falsify)

- 42+ sampled balanced 5-colourings of $K_{25}$ (local search, referee-verified)
  plus AG(2,5): every class's minimal hitting 5-sets span 9 or 10 own-colour
  edges (tools/usable_hitters.py) — comfortably above the $\le 6$ usability bar.
- All sampled colourings and AG: one-vertex extension UNSAT (tools/extend.py);
  six K_24 restrictions: two-vertex extension UNSAT (tools/extend2.py).
- Exact hitting numbers: $h_c = 5$ for all classes of all samples (data/hpass.log).

## Known risks / what reviewers should attack

- **[MH″] might come back SAT** — then classes with $h=4$ exist inside real
  colourings, |T| profiles like (4,5,5,5,6) are live, and steps 4–6 collapse
  for the size-6 part (usability bar becomes $\binom{6}{2}-4 = 11$, vacuous).
  The chain would need a case analysis on size profiles with new machine
  lemmas per profile. (The pure graph relaxation of MH″ IS satisfiable —
  80-edge witness on 21 vertices, see ATTACKS.md — so MH″ genuinely depends
  on the surrounding colouring.)
- Step 5 needs $|T_{c'}| = 5$ EXACTLY (a 4-point set contains no 5-set) — this
  is why step 4 must deliver all-fives.
- [MM]'s $e \le 60$: uses minority at $n=25$ ($\lfloor 300/5 \rfloor = 60$). Check.
- CEGAR soundness for UNSAT verdicts: lazily-added caps are a SUBSET of the
  full valid constraint family, so UNSAT is sound; but every UNSAT must be
  re-verified via the static-CNF export + kissat + DRAT + drat-trim protocol.
- The step-2/step-5 interplay quantifies over the SAME vertex-deleted
  colouring $\chi'$ for all colours — no colour-mixing subtlety, but check.

## Adversarial review of the deduction (2026-07-05, fresh session)

Reviewer scope: verify that the Theorem follows from [MH″] + [MM] as black-box
UNSAT hypotheses (verdicts confirmed still pending: `data/sat/r5_n25_h4.out`
empty; `data/sat/lemma_m_60.log` mid-CEGAR at round 139). I read PROBLEM.md,
this file, and the encoders `tools/sat_encode.py`, `tools/probe_h4.py`,
`tools/lemma_m.py`, `tools/verify.py` in full, and re-ran `probe_h4.py` to
confirm clause structure. I did NOT run the solvers; the deduction is reviewed
as a conditional implication.

### Step-by-step findings

**Step 1 (restriction + partition) — SOUND.** $\chi' = \chi|_{V'}$ is balanced:
every 6-subset of $V'$ is a 6-subset of $V$, so it already sees all 5 colours
under $\chi$, and the edge colours are unchanged by restriction. The $T_c$ are
the fibres of the map $v \mapsto \chi(xv)$, hence a genuine partition of the 25
vertices of $V'$; $\sum_c|T_c| = 25$. Correct. (Implicit: only a *single* vertex
$x$ is fixed — the whole chain derives one contradiction from one $x$, which is
all that is needed to refute existence of $\chi$. Verified this is not secretly
a "for all $x$" argument.)

**Step 2 ($\alpha(G_c - T_c)\le 4$) — SOUND, airtight.** An independent 5-set
$F$ of $G_c$ with $F\cap T_c=\varnothing$ makes $\{x\}\cup F$ a genuine 6-set
($x\notin V'\supseteq F$) that misses colour $c$: no interior edge is $c$ ($F$
independent in $G_c$), and no spoke $xv$ is $c$ ($v\notin T_c$). This violates
balance of the *full* $K_{26}$ colouring — the one place the argument legitimately
reaches past $\chi'$ back to $\chi$. "$\alpha\le 4$" ⟺ "no independent 5-set"
(any larger independent set contains a 5-subset), matching what is proved.

**Step 3 (class invariants) — SOUND. Arithmetic verified.**
- $\alpha(G_c)\le 5$: an independent 6-set is a 6-set of $K_{25}$ missing $c$,
  violating balance of $\chi'$. Correct. (Also forces every colour to appear;
  not needed downstream but true.)
- cap-11: 15 edges in a 6-set; $\ge 12$ of colour $c$ leaves $\le 3$ for the
  other four colours ⟹ $\le 1+3 = 4$ distinct colours seen ⟹ balance violated.
  Threshold is exactly 11 (11 of one colour leaves 4 edges, which *can* realise
  the other 4 colours — no contradiction), so "$\le 11$" is the correct and
  tight bound. Holds for every class including $m$.
- $\sum_c e(G_c)=\binom{25}{2}=300$; minority $\le\lfloor 300/5\rfloor = 60$.
  Correct (min $\le$ average; average is an integer $=60$).

**Step 4 ($|T_c|=5$ for all $c$) — SOUND, given [MH″].** For any $c$ with
$|T_c|\le 4$: take any 4-superset $T^+\supseteq T_c$ inside $V'$ (room exists,
$|V'|=25$); deleting the extra vertices cannot raise the independence number
(an independent set of $G_c-T^+$ is one of $G_c-T_c$), so $\alpha(G_c-T^+)\le
\alpha(G_c-T_c)\le 4$ by step 2. That 4-set contradicts [MH″] applied to the
balanced $K_{25}$-colouring $\chi'$ and colour $c$. Hence $|T_c|\ge 5$ ∀$c$, and
with $\sum|T_c|=25$, all $=5$. The monotonicity direction ("delete more ⟹ $\alpha$
no larger") is used correctly.

**Step 5 (usability, the heart) — SOUND, counting verified.** For $c\ne c'$:
$T_{c'}$ is a 5-set disjoint from $T_c$ (partition), hence $T_{c'}\subseteq
V'\setminus T_c$. If $T_{c'}$ spanned no colour-$c$ edge it would be an
independent 5-set of $G_c$ avoiding $T_c$, i.e. $\alpha(G_c-T_c)\ge 5$,
contradicting step 2 — so $T_{c'}$ contains $\ge 1$ edge of each of the 4
colours $\ne c'$. These 4 edges are **pairwise distinct**: an edge carries one
colour, so edges of distinct colours are distinct edges. Of the $\binom{5}{2}=10$
interior edges, $\ge 4$ are non-$c'$, so $\le 6$ are colour $c'$. The existence
of a colour-$c$ edge is *derived* (not assumed), so no hidden "colour $c$ occurs"
premise. Correct; the "$=5$ exactly" prerequisite from step 4 is genuinely needed
and genuinely available.

**Step 6 (instantiate [MM]) — SOUND. Hypothesis-match checked exhaustively.**
Take $c'=m$. The pair $(G_m, T_m)$ on the 25 vertices $V'$ satisfies every [MM]
premise: $\alpha(G_m)\le 5$ (3), cap-11 on every 6-set (3), $e(G_m)\le 60$ (3,
minority), $|T_m|=5$ (4), $\alpha(G_m-T_m)\le 4$ (2), own-edges $\le 6$ (5). [MM]
forbids exactly such a pair. Contradiction; no balanced 5-colouring of $K_{26}$.
K_25/K_26 bookkeeping is clean throughout: all of $G_c,T_c$,[MH″],[MM] live on
the 25-vertex $V'$; only step 2 touches $K_{26}$.

### Encoding fidelity (checkability of the two machine hypotheses)

**[MH″] / `probe_h4.py` — faithful, WLOG sound.** Base `build(5,25,∅)` is the
standard one-hot + covering encoding whose models are exactly balanced
$K_{25}$-colourings (matches `verify.py`'s definition). The added clauses, one
per 5-subset $S\subseteq\{4,\dots,24\}$ asserting some interior edge is colour 0,
encode precisely $\alpha(G_0-\{0,1,2,3\})\le 4$. So SAT ⟺ ∃ balanced colouring
with $c=0,T=\{0,1,2,3\}$ killing $G_0$'s independent 5-sets. The WLOG is sound:
colour-relabelling ($c\to 0$) and vertex-relabelling ($T\to\{0,1,2,3\}$) act on
disjoint objects, both preserve balance and independence numbers, so every
counterexample maps to a model and vice-versa; UNSAT ⟺ [MH″]. Critically the
instance adds **no** symmetry breaking (`sym=∅`) — correct, since rowsort/
colourprec would re-use the same vertex/colour freedom already spent by the WLOG
and could make it unsound. Re-ran the encoder: 1500 vars, 909149 clauses,
exactly $\binom{21}{5}=20349$ "h4" clauses, $\binom{25}{6}\cdot5=885500$ covering
clauses — matches the mathematics. Precise and checkable.

**[MM] / `lemma_m.py` — faithful; UNSAT-soundness holds in every relaxed
direction.** Encoded constraints: (a) $\alpha(G)\le5$ as "every 6-set has an
edge" (exactly $\alpha\le5$); $e\le60$ atmost; $|T|=5$ (atleast∧atmost);
$\alpha(G-T)\le4$ as "every 5-set meets $T$ or has an edge" (exact); own-edges
via $y_{ij}$ with clause $(\lnot e_{ij}\lor\lnot t_i\lor\lnot t_j\lor y_{ij})$,
i.e. $e_{ij}\land t_i\land t_j\Rightarrow y_{ij}$, and $\sum y\le6$. The
one-directional $y$-clause is sufficient: it forces $y$ true on every own-edge,
so $\sum y\ge$#own-edges; $y$ occurs only positively (implication + atmost), so a
spurious $y=$true can only tighten $\sum y\le6$ — never creates a false model,
and the real config sets $y=$own-indicator to realise own$\le6$. Cap-11 is
CEGAR'd; the terminal UNSAT is on a formula carrying a **subset** of the full
cap-11 family, a relaxation, so UNSAT there ⟹ UNSAT of the fully-capped instance
⟹ [MM]. Every encoded premise is a genuine property of the real $(G_m,T_m)$
(none is stricter than the mathematics), so if the code is UNSAT the real pair
cannot exist. Direction of soundness is correct throughout.

### Implicit assumptions surfaced (all benign)

1. Minority colour $m$ well-defined up to ties; any minimiser has $e\le60$ (min
   $\le$ average) — ties are fine, pick one.
2. A single fixed $x$ suffices; the chain is not a disguised "for all $x$".
3. pysat `CardEnc` (seqcounter/totalizer) auxiliary encodings are faithful — a
   standard trusted dependency; the DRAT re-verification protocol in NOTES.md /
   this file's risk list must run on the **final** CNF including all CEGAR caps
   (saved to `data/sat/lemma_m_caps_e60.json`) to discharge it.
4. [MM] is a *pure-graph* relaxation (forgets that $G_m$ came from a colouring).
   Sound here (real $G_m$ satisfies the graph premises), but — as the risk list
   already notes for MH″ — if the pure-graph MM lands SAT, the chain needs more
   colouring structure encoded. This bears on whether the verdict lands, not on
   the validity of the implication.

### Findings ledger

- FATAL: none.
- FIXABLE: none affecting validity.
- COSMETIC: (i) state explicitly in [MM]'s prose that the *established*
  statement is the subset-capped relaxation (still ⟹ the fully-capped [MM],
  which is all step 6 needs). (ii) Add the "minority well-defined up to ties"
  remark to step 3. Neither changes the argument.

### Verdict

**DEDUCTION ACCEPTED (conditional on [MH″] and [MM]).** All six steps and both
encodings are sound; the two machine hypotheses are stated precisely enough to
be machine-checkable and their prose matches their CNF via sound reductions
(colour/vertex-relabelling WLOG for [MH″]; subset-cap CEGAR relaxation for [MM]).
No FATAL or validity-affecting FIXABLE issue found; only two cosmetic
clarifications. The conditional theorem stands or falls entirely on the two
pending UNSAT verdicts and their independent DRAT re-verification.
