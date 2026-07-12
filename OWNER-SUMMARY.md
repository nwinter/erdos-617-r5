# Plain-language summary (for the owner to present honestly)

*Purpose: the erdosproblems community's due-diligence standard asks whether you can
communicate the key ideas of a solution without consulting the AI. This document is
that communication, at the honest altitude: the shape of the argument and the shape
of the evidence, without the technical interior.*

## The problem

Take 26 points and draw all 325 connecting edges. Colour each edge with one of 5
colours. Question: can you do it so that **every** group of 6 points sees **all 5
colours** among its 15 edges? Erdős and Gyárfás conjectured NO (for 26 = 5²+1 points;
they proved the analogous claims for 3 and 4 colours by hand in 1999). With 25 = 5²
points it IS possible — there's an elegant colouring from finite geometry (the
"affine plane"). So the entire question is whether one extra point can be
accommodated. That one-point cliff is the whole phenomenon.

## What was found

The conjecture is TRUE for 5 colours: 26 points cannot be coloured this way. The
argument has one elementary reduction and two hard lemmas.

**The reduction.** Suppose a valid 26-point colouring existed. Delete any point:
what remains is a valid 25-point colouring, plus a "recipe" — for each remaining
point, the colour of its edge to the deleted one. That recipe splits the 25 points
into 5 colour-groups, and validity forces each group to *plug every hole* of its
colour: wherever 5 points show no red edge among themselves, the red group must
touch them (else those 5 plus the deleted point would be a redless 6-group).

**Lemma 1 (tightness).** Counting forces the recipe to be perfectly rigid: each of
the five groups has exactly 5 points, no slack anywhere. The recurring mechanism —
which shows up at every level of this proof — is that 5·k+1 points can never be
covered by five groups of k: one point always sticks out. The conjecture's "+1"
propagates down every layer of the argument (26 → 25 → 21 = 4·5+1) and is precisely
what breaks the extremal configurations.

**Lemma 2 (the scarcest colour can't pay).** Because the groups are disjoint and
perfectly tight, each group is forced to contain edges of *every other* colour —
leaving at most 6 of its 10 internal edges in its own colour. But the scarcest
colour (some colour has at most a fifth of the 300 remaining edges) provably cannot
supply a 5-point group that both plugs all its holes and is that colour-poor
internally. Proving this takes a case analysis over the possible clique structures,
one classical theorem from 1981/2005 about near-extremal graphs, and four small
finite facts established by exhaustive computer search with independently checkable
certificates.

## Why this succeeded where hand methods stalled

Erdős and Gyárfás's own proofs for 3 and 4 colours already strained at the seams of
hand case-analysis. The r=5 case adds two ingredients that machines supply well:
(1) large-scale structure discovery — thousands of computer experiments mapped
exactly where the problem gets tight, which pointed to the reduction; (2) certified
finite computation — the four bedrock facts are checked by SAT solvers whose
"impossible" answers come with proof certificates that independent standard tools
(and the Lean proof assistant) re-verify.

## What the evidence is, and what it is not

- Two AI systems did the mathematics (Anthropic's Claude: the reduction, the
  framework, the verification infrastructure; OpenAI's gpt-5.6-sol: the two lemma
  proofs, from precise briefs). Three independent fresh-context AI reviews attacked
  the proofs; two repairs were found and adopted.
- Nearly everything is formalized in Lean 4: a computer kernel has checked the
  reduction and both lemmas end-to-end. The formal proof currently carries one
  explicitly-stated classical input (the 1981/2005 theorem — its literature sources
  were retrieved and verified, and its formalization is in progress) and relies on
  Lean's compiled-computation mechanism for the four certificate checks.
- **No human has yet verified the mathematics.** I (the owner) have verified the
  *process* — the review trail, the builds, the certificates — but not the content.
  That is exactly why this package exists in the form it does: everything is
  arranged so a qualified mathematician can verify it efficiently (statements audit
  ≈ 200 lines; one command re-checks the formal proof; the informal write-up is
  self-contained at 23 pages).

If it holds up, the result settles the first open case of a 1999 Erdős–Gyárfás
conjecture (Erdős Problem #617) and shows the affine-plane colouring of 25 points
is exactly optimal.
