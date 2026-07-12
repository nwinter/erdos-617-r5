# ACCEPTED (adversarial review 2026-07-05, see below): merged affine-plane colourings never extend

Author session: 2026-07-05. Status: **ACCEPTED by fresh-session adversarial review**
(verdict at end of file; cosmetic fixes applied post-review). Recorded as RESULTS.md R5.
Computational cross-checks: q=5 (RESULTS.md R2, 15/15 UNSAT), q=3 (reviewer's independent
exhaustive search, all 6 merges × 3^9 maps).

## Statement

Let $q \ge 3$ be a prime power and let $\mathcal{C}$ be the balanced $q$-colouring of $K_{q^2}$
obtained from the affine plane $AG(2,q)$ as follows: identify the vertices with the $q^2$
points; there are $q+1$ parallel classes (directions) of lines; fix two distinct directions
$d_1, d_2$ and merge them into colour $0$; the remaining $q-1$ directions $e_1,\dots,e_{q-1}$
become colours $1,\dots,q-1$; every edge is coloured by the direction of the unique line
through its endpoints.

**Claim.** $\mathcal{C}$ admits no balanced one-vertex extension: there is no map
$\varphi : V(K_{q^2}) \to \{0,\dots,q-1\}$ (colours of the edges from a new vertex $x$)
such that every $(q+1)$-subset of $V(K_{q^2+1})$ containing $x$ sees all $q$ colours.

## Facts used (all standard for affine planes)

(F1) Each parallel class partitions the $q^2$ points into $q$ lines of $q$ points.
(F2) Two lines from different parallel classes intersect in exactly one point.
(F3) Every pair of distinct points lies on exactly one line; "collinear in direction $d$"
     is an equivalence relation whose classes are the lines of direction $d$.

## Proof

A $(q+1)$-set through $x$ is $\{x\} \cup F$ with $|F| = q$. It sees all $q$ colours iff
every colour missing inside $F$ appears among $\{\varphi(p) : p \in F\}$.

**Step 1: every colour class of $\varphi$ has exactly $q$ points.**
Let $L$ be any line. As a $q$-set of vertices, $L$ is monochromatic in $\mathcal{C}$
(its colour is that of $L$'s direction), so the $q-1$ other colours are missing inside $L$,
and $\varphi$ must use all $q-1$ of them on the $q$ points of $L$. In particular, for any
colour $c$ and any parallel class $D$ that is **not** among the direction(s) mapped to $c$,
colour $c$ appears on every line of $D$. Each of the $q$ colours has at least one such
class $D$: colour $0$'s exempt directions are $\{d_1,d_2\}$, leaving $q-1 \ge 2$ qualifying
classes; each colour $c \ne 0$ has the single exempt direction $e_c$, leaving $q \ge 3$
qualifying classes. A point lies on exactly one line of $D$ (F1), so
$|\varphi^{-1}(c)| \ge q$ for every $c$. Since $\sum_c |\varphi^{-1}(c)| = q^2$ and there are
$q$ colours, equality holds: $|\varphi^{-1}(c)| = q$ for all $c$.

**Step 2: for $c \in \{1,\dots,q-1\}$, the set $T_c := \varphi^{-1}(c)$ is a line of
direction $e_c$.**
Colour $c$ is exempt only on lines of direction $e_c$ (those are the only lines containing
colour-$c$ edges of $\mathcal{C}$). So for each of the other $q$ parallel classes
($d_1, d_2$, and the $e_j$, $j \ne c$), $T_c$ hits all $q$ lines of the class; since
$|T_c| = q$ and each point hits one line per class (F1), $T_c$ has **exactly one point on
each line of each non-exempt class**. Hence no two points of $T_c$ are collinear in any
non-exempt direction; by (F3) every pair of points of $T_c$ is collinear in direction $e_c$.
Collinearity in the fixed direction $e_c$ is an equivalence relation (F3), and all
$\binom{q}{2}$ pairs of $T_c$ are in it, so all $q$ points of $T_c$ lie on a single line of
direction $e_c$; as lines have exactly $q$ points (F1), $T_c$ *is* such a line.

**Step 3: contradiction.**
Since $q \ge 3$, there are $q - 1 \ge 2$ unmerged colours; pick two distinct ones,
$c \ne c'$. $T_c$ and $T_{c'}$ are lines of the distinct directions
$e_c \ne e_{c'}$, hence intersect in exactly one point $p$ (F2). Then
$\varphi(p) = c$ and $\varphi(p) = c'$, contradiction, since colour classes are disjoint.
$\blacksquare$ (For $q = 2$ the argument does not apply — there is only one unmerged
colour, so Step 3 is vacuous. The reviewer's exhaustive check shows the *conclusion*
happens to hold at $q=2$ as well, but this proof does not establish it.)

## Remarks for the reviewer

- Step 1's "at least one exempt-free class per colour" count: colour $0$'s exempt classes
  are $\{d_1, d_2\}$, leaving $q - 1 \ge 2$ classes that force it; colour $c \ne 0$'s exempt
  class is $\{e_c\}$, leaving $q$ classes. Both are $\ge 1$ for $q \ge 3$. Check.
- Step 2 needs $q \ge 3$ only through Step 3; Step 2 itself is fine for $q \ge 2$.
- The claim is *consistent with* but much weaker than the conjecture: it does not exclude
  non-AG balanced colourings of $K_{q^2}$, nor extensions thereof.
- Computational cross-check at $q=5$: RESULTS.md R2 (15/15 UNSAT).
- Reviewer should specifically try to break Step 2's "all pairs collinear in $e_c$ ⇒ one
  line" (this uses that collinearity-in-a-direction is transitive, i.e. parallelism
  partitions points — true in any affine plane) and Step 1's exactness bookkeeping.

## Adversarial review (2026-07-05, fresh session)

Reviewed against PROBLEM.md and the affine-plane facts. Method: hand-verification of
every step plus an **independent** brute-force at $q=3$ (own $AG(2,3)$ construction, not
the repo's tooling). Repo commit at review: `7fef0da`.

**Preliminary — the premise ("$\mathcal C$ is balanced") is genuinely true, and the proof
does not even need it.** For any direction $D$ and any $(q+1)$-set $S$, pigeonhole ($q+1$
points into the $q$ parallel lines of $D$) puts two points of $S$ on a common $D$-line, so
colour $\mathrm{col}(D)$ appears in $S$; ranging $D$ over all $q+1$ directions hits all $q$
colours, so every $(q+1)$-set sees all colours. The non-extension proof itself uses only
the structure of $\mathcal C$ (that lines are monochromatic), never balancedness of the
$x$-free subsets, so it is logically self-contained. Good.

**Step 1 — CORRECT.** The load-bearing fact is that *every* line $L$ is monochromatic:
its $q$ points are pairwise collinear in $L$'s own direction (two points determine the
unique line $L$), so all $\binom{q}{2}$ interior edges carry $\mathrm{col}(L)$ and $L$
misses all $q-1$ other colours. Since $|L|=q$, $L$ is a legitimate constraint set $F$, and
the extension constraint forces $\varphi(L)$ to contain every missing colour — this is
airtight and holds for **all** lines, exactly as the reviewer prompt flagged to check.
Consequently, for colour $c$ and any direction $D$ with $\mathrm{col}(D)\ne c$, colour $c$
lands on every one of the $q$ *disjoint* lines of $D$ (F1), giving $\ge q$ distinct points,
so $|\varphi^{-1}(c)|\ge q$. Exempt-class bookkeeping verified: colour $0$ has exempt
directions $\{d_1,d_2\}$, leaving $q-1\ge2$ forcing classes; each colour $c\ne0$ has the
single exempt direction $e_c$, leaving $q$ forcing classes. Both $\ge1$, so the bound
applies to all $q$ colours; $\sum_c|\varphi^{-1}(c)|=q^2$ forces equality $|\varphi^{-1}(c)|=q$.
(The prose "$q$ classes… since $q+1\ge3$" is a garbled justification — the correct reason is
$q-1\ge1$ resp. $q\ge1$ — but the conclusion is right. COSMETIC.)

**Step 2 — CORRECT.** For $c\in\{1,\dots,q-1\}$: the only lines coloured $c$ have direction
$e_c$, so for each of the $q$ non-exempt directions ($d_1,d_2$ and $e_j,\,j\ne c$; count
$2+(q-2)=q$) every line has $\mathrm{col}\ne c$, hence meets $T_c$. With $|T_c|=q$ points and
$q$ disjoint lines all met, it is a bijection: exactly one point of $T_c$ per line of each
non-exempt direction. So no two points of $T_c$ share a non-exempt direction; since every
pair is collinear in exactly one of the $q+1$ directions and $q$ of them are excluded, every
pair is collinear in $e_c$. "Same $e_c$-line" is the block relation of the $e_c$-partition
(F1/F3), a bona fide equivalence relation; all pairs of $T_c$ collinear in $e_c$ ⇒ all of
$T_c$ in one block ⇒ (block has $q$ points $=|T_c|$) $T_c$ **is** that line. The transitivity
step the prompt singled out is legitimate — it is "same block of a partition", not a
fragile transitivity — and I could not break it.

**Step 3 — CORRECT.** For $q\ge3$ there are $q-1\ge2$ unmerged colours; pick $c\ne c'$, get
lines $T_c,T_{c'}$ of distinct directions $e_c\ne e_{c'}$ (the map $c\mapsto e_c$ is
injective). F2 ("two lines of different parallel classes meet in exactly one point") is a
correct affine-plane fact and is applied correctly: the intersection point $p$ would satisfy
$\varphi(p)=c=c'$, impossible. **$q=3$ edge case explicitly checked**: unmerged colours are
exactly $\{1,2\}$, two distinct values, so Step 3 fires. The proof is coordinate-free (only
F1–F3), so it holds for every prime-power order including non-prime $q$ (e.g. $q=4$ over
$\mathbb F_4$), not just prime-field cases.

**Computational checks (independent, this session).**
- `q3_check.py` (own $AG(2,3)$; scratchpad): verifies F1 (4 classes, each 3 lines of 3),
  F2 (every cross-class line pair meets in 1 point), F3 (each pair on a unique line/direction);
  then for **all 6** merge choices confirms $\mathcal C$ is balanced and **exhausts all
  $3^9=19683$ maps $\varphi$** — zero balanced extensions in every case. Matches the theorem
  at $q=3$. (Runtime 0.1s.)
- Boundary probe at $q=2$ (all 3 merges, full $2^4$ search): $\mathcal C$ balanced, **0**
  balanced extensions. So the *conclusion* is in fact also true at $q=2$, but this proof
  cannot reach it (only one unmerged colour, Step 3 vacuous) — the author's $q=2$ caveat is
  therefore accurate. No conflict with $N(2)=5$: this $K_4$ colouring has a $(4,2)$
  colour/edge split, not the pentagon's $(3,3)$, so it is simply a balanced $K_4$ colouring
  that does not extend.
- $q=5$: independently already recorded as UNSAT for all 15 merges (RESULTS.md R2); consistent.

**Gaps found.** All COSMETIC; none affect correctness:
1. The "Statement" header says "Let $q$ be a prime power"; the proof establishes the claim
   only for $q\ge3$ (Step 3), which is also the stated target. Add "$\ge 3$" to the header
   for precision. (The conclusion happens to be true at $q=2$ too, but is *not proved here*.)
2. Two garbled/unfinished sentences: Step 1's "$q$ classes… at least one for each colour
   since $q+1\ge3$", and Step 3's "$q\ge2$, so there are at least… for $q\ge3$". The intended
   content is correct; recommend rewriting for readability.
3. The closing $q=2$ parenthetical ("the pentagon extends… rather, exists") is muddled;
   the substantive point (proof inapplicable at $q=2$, consistent with $N(2)=5$) is correct.

**Scope reminder (not a defect).** As the author notes, this kills only one-vertex extensions
of the *merged-AG* colourings; it says nothing about non-AG balanced colourings of $K_{q^2}$.
It is a clean structural result, strictly weaker than the conjecture.

VERDICT: ACCEPTED (correct as stated for $q\ge3$; cosmetic fixes 1–3 above recommended).
