# Known results and literature leads

Two evidence grades. **VERIFIED** = read directly from the cited source during this project (link + date). **LEAD** = recollection or secondhand; check the actual source before relying on it, then upgrade or correct.

## VERIFIED (from https://www.erdosproblems.com/617, accessed 2026-07-05)

- Conjecture of Erdős and Gyárfás, references [ErGy99] and [Er99]. Status: open, FALSIFIABLE.
- [ErGy99] proved the conjecture for $r=3$ and $r=4$, observed it is false for $r=2$, and showed the property fails for infinitely many $r$ when $r^2+1$ is replaced by $r^2$ (i.e. balanced r-colourings of $K_{r^2}$ exist for infinitely many $r$).
- No solutions, partial or complete, claimed in the site's comments as of the access date. One user ("will0708") is flagged as currently working on it.
- Site metadata: `formalized: yes` (updated 2026-01-24) — a formal (Lean) statement of the problem exists; likely in the google-deepmind/formal-conjectures repository or linked from the site. Retrieve it to double-pin definitions.

## LEADS (unverified — retrieve, then upgrade or correct)

- [ErGy99] is likely: P. Erdős and A. Gyárfás, "Split and balanced colorings of complete graphs", Discrete Mathematics (c. 1999). Retrieve the actual paper; extract (a) the r=3,4 proof technique, (b) the explicit balanced colourings of $K_{r^2}$ and for which $r$ they exist (suspect algebraic/finite-geometry structure, possibly prime powers — affine plane of order r has $r^2$ points, which is suggestive), (c) any remarks on r=5 or on $n$ strictly between $r^2$ and $r^2+1$... note there is no integer strictly between them, so the entire question is the single vertex.
- The $r=2$ falsity is equivalent to $R(3,3)=6$ with the pentagon as the $n=5$ witness (PROBLEM.md worked example 1); this suggests viewing balanced colourings as a "local Ramsey" / covering condition. Search terms: balanced colouring, split colouring, local Ramsey number, mixed Ramsey, covering designs, Gyárfás survey.
- Whether $N(r)=r^2$ exactly for the ErGy constructions' values of $r$ appears open per the site's framing; the conjecture is exactly the claim $N(r)\leq r^2$ for all $r\geq 3$.

## Citation sweep (R12, forward/backward, 2026-07-11)

Full log in `papers/citation-sweep.md`. The three LEADS above have all been actioned:
[ErGy99] retrieved and read (`papers/ergy99.md`, VERIFIED); the $r=2 \equiv R(3,3)=6$
framing confirmed; and $N(5)=25$ now settled by this project (RESULTS R9). New sweep findings,
graded:

- **VERIFIED — no work since 1999 addresses the balanced conjecture / $g_r(2)$ / the $r=5$
  case.** A forward-citation sweep of [ErGy99] and direct searches for "balanced $(r,2)$-
  coloring"/"$g_r(2)$"/#617 return only (i) the *split* line ($f_r$) and (ii) unrelated
  edge-colouring topics. No 2025–2026 preprint claims a #617 proof or counterexample.
  Corroborated by erdosproblems.com/617 (FALSIFIABLE, "no solutions claimed", last edited
  2026-04-01) and by `formal-conjectures` tagging only $r=3,4$ solved. **The $r=5$ result
  appears genuinely new.**
- **VERIFIED — the Brouwer(1981)/Kang–Pikhurko(2005) non-$r$-partite Turán bound has never
  been corrected.** It is reproved, restated (Ren–Wang–Wang–Yang 2024, arXiv:2404.07486, now
  cited in the writeup) and *extended* (asymptotic stability constant — Balogh–Clemen–Lavrov–
  Lidický–Pfender 2020, *Making $K_{r+1}$-free graphs $r$-partite*, CPC; spectral analogues;
  generalized-book host graphs) but the exact edge bound the project uses is untouched. No
  erratum. `BrouwerFacts` input is safe.
- **VERIFIED (correction) — the "Füredi 2002" follow-up is Füredi–*Ramamurthi*, not
  Füredi–Gyárfás.** Full citation: Z. Füredi and R. Ramamurthi, *On splittable colorings of
  graphs and hypergraphs*, J. Graph Theory **40**(4) (2002) 226–237, DOI `10.1002/jgt.10044`
  (Crossref-verified). Scope is the *split* side (LEAD; Wiley abstract was 403) — it does not
  bear on the balanced $r=5$ question. Corrected in `papers/ergy99.md`.
- **Do not conflate** (recurring namesakes, all different problems): the Erdős–Gyárfás
  *function* $f(n,p,q)$ (generalized Ramsey), the Erdős–Gyárfás *cycle* conjecture (Wikipedia),
  the Erdős–Gyárfás–Pyber monochromatic-partition conjecture, "balanceable" graphs, and
  "balanced colorings" of Erdős–Rényi hypergraphs.

## Retrieval log

- **2026-07-05** — erdosproblems.com/617: FALSIFIABLE, no solutions claimed; refs [ErGy99] [Er99]; proved r=3,4 (see `PROBLEM.md`).
- **2026-07-05** — [ErGy99] full text (renyi.hu PDF) read; conjecture, r=3,4 proofs, affine construction, $r^2+1\le g_r(2)\le r^2+r+1$ (see `papers/ergy99.md`).
- **2026-07-10** — [KP05] primary PDF (matstud.org.ua) read in full; Brouwer bound + equality classification, all five project uses FAITHFUL, no discrepancies (see `papers/brouwer-kang-pikhurko.md`).
- **2026-07-11** — Ren–Wang–Wang–Yang arXiv:2404.07486 (secondary Brouwer statement) author/title verified; added to the writeup bibliography.
- **2026-07-11** — Forward/backward citation sweep of [ErGy99] and [KP05] (this section; full log `papers/citation-sweep.md`): novelty and correctness both clean; Füredi–Ramamurthi attribution corrected.
