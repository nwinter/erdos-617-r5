# N(6) / composite-r literature sweep — is a balanced 6-colouring of K_36 even possible?

**Run 2026-07-13** by the literature agent, at the team lead's request, as the natural
follow-on to the resolved r=5 case (N(5)=25). Companion to the fresh r=6 search effort
(tasks #73–76). This is the repo's **first** document on the composite-r / N(6) question.

**Grading.** **VERIFIED** = I read the primary source (or a very recent verified project
file) during this sweep, or ran the check myself. **LEAD** = search-snippet / recollection /
attribution not pinned to a read source.

**Notation (from `PROBLEM.md`, do not conflate with g_r(2)).** N(r) = largest n admitting a
*balanced* r-colouring of K_n = every (r+1)-subset sees all r colours = every colour class
(as a graph) has independence number α ≤ r. Conjecture #617 is **N(r) ≤ r²** for all r ≥ 3.
The r=5 case (N(5)=25) is this project's resolved result.

---

## Headline

- **Is N(6) ≥ 36 known? NO — genuinely OPEN, and unstudied.** The only construction proving
  N(r) ≥ r² is the affine-plane colouring, which for r=6 needs an **affine plane of order 6**
  — this **does not exist** (Bruck–Ryser; Tarry's resolution of Euler's 36-officers problem;
  the max number of MOLS(6) is 1). No substitute construction reaching K_36 is known.
- **Best known lower bound: N(6) ≥ 26**, now **machine-verified by `tools/verify.py`** this
  session (see §2). It comes from the affine plane of order **5** (which *does* exist), used as
  6 separate colours on K_25 (α=5 each), plus a free +1 vertex. This is far below 36 — the gap
  **[26, 36] is the whole open question at r=6.**
- **Is N(6) ≤ 36 (the conjecture) proved for r=6? NO.** Nor is N(6) < 36 proved. Both bounds of
  the interval are open, so a priori **N(6) ∈ [26, 36], and even N(6) ≥ 37 (a counterexample to
  #617 at r=6) is not excluded** by anything in the literature.
- **Who has worked on it since 1999? No one**, on the balanced conjecture / N(r) values — the
  R12 citation sweep's "no progress since 1999" verdict is **reconfirmed here specifically for
  the composite-r / lower-bound side** with fresh targeted searches (§4). The closest *active*
  problem (Gyárfás large monochromatic components) runs into the **same** missing object,
  AG(2,6), and treats it as a known hard gap (§3) — a useful methodological template.

---

## 1. Is N(6) ≥ 36 known? (the lower-bound question) — OPEN

**The standard construction needs AG(2,6), which does not exist.** [ErGy99] §5 (our verified
read, `papers/ergy99.md`): the balanced r-colouring of K_{r²} is built from the **affine plane
of order r**: r+1 parallel classes, r−1 of them used as single colours and one colour = the
union of two classes; each colour class then has α = r. For r=6 this requires the affine plane
of order 6.

- **VERIFIED — no affine plane of order 6.** Equivalent to: no two orthogonal Latin squares of
  order 6 (Euler's conjecture for order 6, proved by Tarry 1900 by exhaustion; also Bruck–Ryser
  gives non-existence for orders ≡ 1,2 mod 4 that aren't sums of two squares — 6 is handled by
  Tarry directly). The maximum number of MOLS of order 6 is **1** (so no 4-net, no transversal
  design TD(4,6), no resolvable 2-(36,6,1) design). Standard; also surfaced in this sweep's
  searches. (Wikipedia "Affine plane (incidence geometry)"; Colbourn–Dinitz *Handbook of
  Combinatorial Designs*.)
- **VERIFIED — [ErGy99] claims the r² lower bound only "for infinitely many r".** The paper's
  own phrasing (site + `papers/ergy99.md` §8, formal variant `.r2`) is that the property fails
  at r² "for infinitely many r" — i.e. the prime powers, where AG(2,r) exists. It makes **no**
  claim for composite non-prime-power r, and does **not** mention r=6 specifically. So even in
  the founding paper, the composite-r lower bound is simply absent, not asserted.

**Why counting does not settle it (and why the affine plane looks structurally unique).** A
colour class with α ≤ 6 on 36 vertices has a K_7-free complement, so by Turán the complement
has ≤ t_6(36) = (5/6)·36²/2 = 540 edges, i.e. **each colour needs ≥ 90 edges**. Six colours
need ≥ 540 of the C(36,2) = 630 edges — slack exactly **90 = one colour's worth**. So counting
gives **no obstruction** to N(6) ≥ 36; it also shows any balanced 6-colouring of K_36 must be
Turán-extremal on five colours (each = 90 edges = 6 disjoint K_6's, the affine parallel classes)
with the sixth doubled (180 edges) — exactly the affine-plane profile. The affine plane is the
only known object hitting this tight profile, and it is the one that doesn't exist at order 6.
This is the crux: the problem is delicate precisely because the natural extremal structure is
forbidden, without a counting reason forbidding the *value*.

---

## 2. Best known lower bound: N(6) ≥ 26 (VERIFIED this session)

**Construction (affine plane of order 5, used as SIX colours + one free vertex).**
Take AG(2,5) = Z₅×Z₅ (25 points, 6 parallel classes = slopes 0..4 and vertical). Colour each
edge by its **direction**, giving **6 colours**, each colour class = 5 disjoint K₅'s, so **α = 5**
for every colour. (This is [ErGy99]'s affine construction *without* merging two classes — legal
because we have exactly 6 = 5+1 parallel classes to spend on 6 colours.) That already gives a
balanced 6-colouring of K_25. Now **α = 5 < 6 leaves one unit of slack**: add a 26th vertex and
colour all its edges colour 0. Any colour-c independent set either avoids the new vertex (≤ 5) or
is {new vertex} ∪ (colour-c-independent set in the base) (≤ 1+5 = 6). So every colour keeps
α ≤ 6 ⇒ every 7-subset of K_26 sees all 6 colours.

- **VERIFIED (referee):** `python3 tools/verify.py k26_r6.json` →
  `BALANCED: r=6, n=26; all 657800 subsets of size 7 see all 6 colours.` (exit 0, this session).
  Build script + JSON in scratchpad; trivially reproducible.
- **General form:** whenever **r−1 is a prime power**, AG(2,r−1) as r colours gives a balanced
  r-colouring of K_{(r−1)²} with α = r−1, hence **N(r) ≥ (r−1)² + 1**. For r=6: (r−1)²+1 = **26**.
  (Note (r−1)²+1 = r²−2r+2, i.e. **10 short of r²=36** — that deficit is exactly the price of
  AG(2,6) not existing.)
- **Honest status:** 26 is a *floor*, almost certainly not tight, and is likely improvable by
  the search fleet (tasks #73–76). I did not attempt to push it; the literature offers nothing
  better (it offers nothing at all — see §4), so as a *known* lower bound, 26 stands.

**Upper side — nothing known.** No proof of N(6) ≤ 36 for r=6 (the conjecture), and no proof of
N(6) < 36. The r=5 impossibility used the Brouwer / Kang–Pikhurko non-r-partite Turán bound at
specific (r,n); whether that machinery reaches r=6 is a separate open question for the proof
effort, not something the literature has done.

---

## 3. Constructions at composite r, and the closest analog (Gyárfás mono-components)

**What structures could substitute for the missing AG(2,6)?** All the natural design-theory
substitutes for a resolvable 2-(36,6,1) design are limited by the same MOLS(6)=1 fact:

- **Nets / MOLS.** A k-net of order 6 ⟺ (k−2) MOLS(6). Since max MOLS(6) = 1, the best is a
  **3-net** (rows + columns + one Latin square = 3 parallel classes of K₆'s), covering only
  3·90 = 270 of the 630 edges by clean clique-parallel-classes; the affine plane would give 7
  such classes (7·90 = 630). The remaining 360 edges have no clique-partition structure — the
  gap a clever 6-colouring would have to fill by other means. (VERIFIED: net ⟺ MOLS equivalence,
  standard; TD(k,6) exists only for k ≤ 3.)
- **Group-divisible / transversal designs on Z₆×Z₆, algebraic slope colourings.** In Z₆ the
  slope-line construction covers only pairs whose x-difference is a **unit** (∈{1,5}) plus the
  vertical class; pairs with x-difference a zero-divisor (2,3,4) are **uncovered** — the concrete
  face of "no affine plane of order 6". So Z₆×Z₆ gives at most ~4 clean parallel classes, not 7.
  (My derivation; elementary.) Weaker designs (near-resolvable, pairwise-balanced, GDDs) are not
  known to assemble into 6 classes each with α ≤ 6 — this is unstudied.
- **Truncating a bigger plane (AG(2,7), 49 points, exists).** A conceivable avenue: delete
  points from AG(2,7) to reach K_n (26 < n ≤ 36) with 6 colours of α ≤ 6. Not a known
  construction; flagged as a search direction, not a result.

**Closest active problem — Gyárfás large monochromatic components (same missing object).**
This is the most useful analog and a methodological template, though it is a **different**
quantity (component size, not bounded independence). VERIFIED from arXiv:2302.04487 (intro) and
corroborated across the mono-component cluster (Conlon's `monocomp.pdf`, arXiv:2204.11360):

> Gyárfás: every r-colouring of K_n has a monochromatic component with ≥ n/(r−1) vertices, and
> this is **best possible whenever r−1 is a prime power and n is a multiple of (r−1)²** — the
> tight colouring being "**K_{(r−1)²} together with r decompositions into r−1 vertex-disjoint
> copies of K_{r−1}**", i.e. **the affine plane of order r−1**.

That extremal object is *literally the same kind of object* as our balanced construction. Two
precise points for us:
1. **Same missing object, different r.** Our balanced N(r) ≥ r² needs AG(2,**r**) (obstruction
   at **r=6**); the mono-component tight bound needs AG(2,**r−1**) (obstruction at **r=7**). Both
   are blocked by the non-existence of **AG(2,6)**.
2. **The field's response to the missing plane** is the template: an unconditional but **weaker**
   bound. **LEAD** (Google snippet of a mono-component paper; exact source/attribution not pinned
   in the fetch): when there is no affine plane of order r−1, the component bound improves to
   **(r−1)n/(r²−2r)** — i.e. the missing plane is handled by a separate, weaker argument, not by
   a substitute plane. The analogy suggests our composite-r case likewise will not have a clean
   "substitute design" and may need a bespoke argument (or a computer search) on both sides.

---

## 4. Who has worked on this since 1999? — no one (reconfirmed for composite r)

The R12 citation sweep (`papers/citation-sweep.md`, 2026-07-11) already found **no work since
1999** on the balanced conjecture / g_r(2) / the r=5 case. I **reconfirmed this specifically for
the composite-r / lower-bound side** with fresh targeted searches (2026-07-13):

- **VERIFIED (searches run):** queries for balanced r-colouring lower bounds at composite r,
  N(6)=36 / K_36, "g_r(2)" / "balanced (r,2)-coloring" at r=6, and design substitutes for AG(2,6)
  all returned **only different problems** — overwhelmingly the Erdős–Gyárfás **function**
  f(n,p,q) (generalized Ramsey: 2212.06957, 2504.05647, 1704.01156, Balogh color-energy
  2102.11466), the **monochromatic-components** line (§3), and unrelated "balanced colouring"
  namesakes (equitable/neighbourhood-balanced colourings, ER-hypergraph balanced independent
  sets). **Nothing** computes or bounds N(6) or studies the composite-r balanced case.
- **VERIFIED (recent project read):** erdosproblems.com/617 (via `papers/erdosproblems-comms.md`,
  fetched 2026-07-11 — my direct WebFetch today returned HTTP 403, a bot-block, so I rely on the
  2-day-old verified read): status FALSIFIABLE, **no solutions/partial claims in comments**, one
  comment (not a claim), self-tags "eigensolver likes it" / "will0708 currently working". **No
  mention of r=6, composite r, or the lower-bound question** anywhere on the page.
- **Do-not-conflate register still applies** (see `papers/citation-sweep.md` §5): EG *function*,
  EG *cycle* conjecture, EG–Pyber partition, "balanceable" graphs, ER-hypergraph balanced
  colourings — all different, all discarded.

**Conclusion:** the composite-r / N(6) lower-bound question is **open and, as far as the indexed
literature shows, has never been posed in print.** Confidence: high (same caveat as always — a
sweep cannot see unpublished work, e.g. will0708's self-tagged effort).

---

## 5. Bottom line + most useful leads

**Bottom line.** N(6) is wide open on **both** sides. Verified today: **26 ≤ N(6)**. The
conjecture predicts N(6) ≤ 36; neither ≤ 36 nor < 36 is proved for r=6, and ≥ 37 (a
counterexample to #617) is not excluded. The r=5 machinery (affine plane of order 5 exists;
Brouwer/KP Turán bound) does **not** transfer: AG(2,6) does not exist, so the natural tight
construction of K_36 is forbidden, while nothing forbids the *value* 36 — that tension is the r=6
problem in one sentence.

**Three most useful leads.**
1. **The Gyárfás mono-component analog (arXiv:2302.04487; Conlon `monocomp.pdf`;
   arXiv:2204.11360).** Same forbidden object AG(2,6); the field's move was a weaker
   unconditional bound rather than a substitute design. Read these for (a) how "no affine plane
   of order 6" is argued around, and (b) the exact tight object = K_{(r−1)²} split into K_{r−1}'s.
   Chase the citation for the **(r−1)n/(r²−2r)** improvement (LEAD — likely Füredi-style) to see
   the technique.
2. **The MOLS(6)=1 obstruction as the precise barrier** (Tarry 1900; Bruck–Ryser; Colbourn–Dinitz
   *Handbook*). Best net is a 3-net (270/630 edges clean); this quantifies exactly how far short
   the design-theory toolkit falls and frames whether a bespoke (non-plane) K_36 colouring can
   exist — the concrete target for the search fleet.
3. **The verified baseline N(6) ≥ 26 and the general N(r) ≥ (r−1)²+1 (r−1 a prime power).**
   Feeds tasks #74/#75 directly (referee-validated r=6 candidate + a scored baseline to beat).
   The research target is the interval **[26, 36]**: push the lower bound up by search, and/or
   attempt the N(6) ≤ 36 proof — knowing the r=5 method does not obviously generalize.

---

## Sources (retrieved 2026-07-13 unless noted)

- **VERIFIED** [ErGy99] affine construction / "infinitely many r" phrasing — via `papers/ergy99.md`
  (renyi.hu PDF read 2026-07-05); https://www.sciencedirect.com/science/article/pii/S0012365X98003239
- **VERIFIED** erdosproblems.com/617 state — via `papers/erdosproblems-comms.md` (fetched
  2026-07-11; my 2026-07-13 WebFetch → HTTP 403 bot-block); https://www.erdosproblems.com/617
- **VERIFIED (referee, this session)** N(6) ≥ 26 — `tools/verify.py` on the AG(2,5)-as-6-colours
  + 1 construction: BALANCED r=6 n=26, all 657800 7-subsets see all 6 colours.
- **VERIFIED** Gyárfás mono-component bound tight when r−1 a prime power, n multiple of (r−1)² —
  arXiv:2302.04487 (*Large monochromatic components in colorings of complete hypergraphs*),
  https://arxiv.org/abs/2302.04487 ; cluster: Conlon *Monochromatic components with many edges*
  http://www.its.caltech.edu/~dconlon/monocomp.pdf ; arXiv:2204.11360
- **LEAD** improved mono-component bound (r−1)n/(r²−2r) when no affine plane of order r−1 —
  Google snippet of the above cluster; exact source/attribution not pinned (chase it).
- **VERIFIED** no affine plane of order 6 / max MOLS(6)=1 / net ⟺ MOLS / TD(k,6) only k ≤ 3 —
  standard (Tarry 1900; Bruck–Ryser); Wikipedia *Affine plane (incidence geometry)*; transversal
  designs ⟺ MOLS, arXiv:1501.03518 and Colbourn–Dinitz *Handbook of Combinatorial Designs*.
- **VERIFIED (searches run 2026-07-13)** no indexed work on N(6) / composite-r balanced case —
  targeted WebSearch queries all returned different problems (EG function, mono-components,
  balanced-colouring namesakes); consistent with `papers/citation-sweep.md` (2026-07-11).

---

## One-paragraph summary for the successor session

After N(5)=25 was resolved, the natural next question — **is N(6) ≥ 36?** — is **open and
unstudied**. The obstruction is sharp: the only known construction achieving N(r) ≥ r² is the
affine-plane colouring, and it needs the **affine plane of order 6, which does not exist**
(Tarry/Bruck–Ryser; MOLS(6)=1). Counting gives no obstruction to K_36 (each colour needs ≥ 90
edges, six colours need 540 ≤ 630), but the tight profile it forces is exactly the forbidden
affine plane. The best construction that survives uses the affine plane of order **5** (which
exists) as 6 colours on K_25 plus a free vertex, giving a **referee-verified N(6) ≥ 26** — 10
short of 36, the deficit being precisely the missing AG(2,6). No one has published on this since
[ErGy99] (reconfirmed for the composite-r side); the closest active problem (Gyárfás
mono-components) hits the same missing AG(2,6) and answers it with a weaker unconditional bound
rather than a substitute design. So N(6) ∈ [26, 36] with **both** ends open — including the
possibility N(6) ≥ 37, which would disprove #617 at r=6.
