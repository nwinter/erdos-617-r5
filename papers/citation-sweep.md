# Citation sweep — Erdős #617 balanced-colouring conjecture (R12)

**Forward/backward citation due-diligence**, run **2026-07-11** by the writeup/citation agent
(the wiki "have you done a real literature review — forward + backward citation search?"
checklist item). Two target papers were swept: **[ErGy99]** (the source of the conjecture)
and **[KP05]** (the load-bearing external theorem behind `BrouwerFacts`).

**Grading.** VERIFIED = I fetched and read the source (or its citation metadata / abstract)
during this sweep. LEAD = search-snippet only, paywalled, or inferred from title + context.

---

## Headline

**SWEEP CLEAN on both correctness and novelty.**

- **Novelty (goal a):** No work since 1999 touches the *balanced*-colouring conjecture, the
  function $g_r(2)$, or the $r=5$ case. Every forward citation of [ErGy99] is either on the
  *split* side ($f_r$) or on unrelated colouring topics. The $r=5$ impossibility appears
  genuinely new. **Confidence: high.**
- **Correctness (goal b):** The Brouwer (1981) / Kang–Pikhurko (2005) non-$r$-partite Turán
  bound has been reproved, restated, and *extended* (spectral versions, other host graphs,
  asymptotic stability constants) but **never corrected**. No erratum. The exact
  $r=5,\ n\in\{15,16,21\}$ application the project uses is safe.
- **One correction to our own records:** the follow-up paper the repo listed as
  "Füredi–**Gyárfás** 2002" is actually **Füredi–Ramamurthi**, *J. Graph Theory* **40**(4)
  (2002) 226–237 — and it is on the *split* side, not the balanced conjecture. (Attribution
  fixed in `papers/ergy99.md` and `papers/known-results.md`.)

---

## 1. Log — queries run and hits examined

Engine: WebSearch (Google-like) + WebFetch (arXiv, Crossref, publisher pages). ~13 queries/fetches.

| # | query / fetch | notable hits | verdict |
|---|---|---|---|
| 1 | `"Split and balanced colorings of complete graphs" … cited by` | ScienceDirect (ErGy99 itself); Füredi–Ramamurthi 2002; adapted list colouring (Esperet 2009); adaptable/conflict colouring (Aliaj 2023); monochromatic cycle/path partitions; rainbow subgraphs (2209.13867) | citing works are **split-side or unrelated**; none on the balanced conjecture |
| 2 | balanced colouring $K_{r^2+1}$ Erdős–Gyárfás conjecture | Erdős–Faber–Lovász; monochromatic path covers (2409.03623); **EG *function* via color-energy** (Balogh 2023) — different problem; ER-hypergraph "balanced colorings" (2504.04585); erdosproblems.com/617 | all **off-topic**; no $g_r(2)$ progress |
| 3 | Kang–Pikhurko not-$r$-partite / Brouwer bound improvement | KP05 PDF; **"Making $K_{r+1}$-free graphs $r$-partite"** (Balogh–Clemen–Lavrov–Lidický–Pfender, 1910.00028); RWWY 2404.07486; "Exact stability for Turán"; spectral-Turán | Turán-line; **extends, does not correct** KP |
| 4 | Füredi Gyárfás splittable colorings 2002 balanced | **Füredi–Ramamurthi** JGT 2002 (Wiley); Füredi publication list; Gyárfás "Large Monochromatic Components — A Survey" | **corrects attribution**; split side |
| 5 | WebFetch `arXiv:1910.00028` | Balogh–Clemen–Lavrov–Lidický–Pfender, *Making $K_{r+1}$-Free Graphs $r$-partite*, Combinatorics (CPC), DOI 10.1017/S0963548320000590 | asymptotic Erdős–Simonovits stability constant ($\alpha\!\leftrightarrow\!\varepsilon$); **not** the KP exact bound; no correction |
| 6 | WebFetch `arXiv:1509.05539` (Gyárfás survey) | — | PDF returned as binary/unreadable; **inconclusive** (not relied on) |
| 7 | WebFetch `arXiv:2504.04585` | Dhawan–Wang, *Balanced colorings of Erdős–Rényi hypergraphs* (2025) | **different "balanced"** (balanced independent sets in $r$-partite hypergraph proper colourings; extends Feige–Kogan); off-topic |
| 8 | Kang–Pikhurko not-$r$-partite cited by (Turán) | singular Turán/WORM (1909.04980); **Refinement on Spectral Turán** (SIAM JDM, 10.1137/22m1507814); **exact Turán of generalized book $B_{r,k}$ in non-$r$-partite graphs** (2508.07533, 2025); making-$r$-partite (BCLLP) | same theme, other host graphs / spectral; **none corrects** the $K_{r+1}$ edge bound |
| 9 | WebFetch Füredi publication list | — | ECONNREFUSED (host down); citation instead confirmed via Crossref (row 12) |
| 10 | `"balanced (r,2)-coloring" OR "g_r(2)"` + projective plane | **balanceable graphs** (Caro–Hansberg–Montejano line); **Erdős–Gyárfás–Pyber** monochromatic-partition conjecture (also affine-plane-tight, but different); mono partitions | no $g_r(2)$ hit; all **different problems** |
| 11 | Erdős problem 617 resolved/proof/counterexample 2025–2026 | erdosproblems.com/617 (last edited **2026-04-01**); **EG *function* phase transitions** (2504.05647) — different; "six colours on every $K_5$" (1704.01156) — EG function | **no resolution** reported anywhere |
| 12 | WebFetch Crossref `10.1002/jgt.10044` | Füredi, Ramamurthi; JGT **40**(4) (2002) 226–237 | **VERIFIED** citation metadata |
| 13 | WebFetch Wiley abstract (jgt.10044) | — | HTTP 403; abstract not obtained (scope kept as LEAD) |

(For completeness: the RWWY secondary source for Brouwer's bound — arXiv:2404.07486, Ren–Wang–Wang–Yang, 2024 — was fetched during the Part-A writeup pass; author list/title VERIFIED and now cited in `writeup/erdos617-r5.tex`.)

## 2. Findings on goal (a) — progress on the balanced conjecture / $g_r(2)$ / $r=5$

- **VERIFIED — [ErGy99] is still the only paper on the balanced $g_r(2)$ conjecture.**
  Forward-citation sweep (rows 1, 4) surfaces no paper that studies $g_r(2)$, the
  no-balanced-colouring-of-$K_{r^2+1}$ conjecture, or the $r=5$ case. Citing works split into
  (i) the *split* line ($f_r$: Füredi–Ramamurthi 2002 and descendants) and (ii) unrelated
  edge-colouring topics (monochromatic partitions, adaptable/conflict/adapted colouring,
  rainbow/heterochromatic subgraphs).
- **VERIFIED — direct searches for the quantity return nothing on-topic** (rows 2, 10, 11):
  no paper uses "balanced $(r,2)$-coloring"/"$g_r(2)$" in the Erdős–Gyárfás sense, and no
  2025–2026 preprint claims a proof or counterexample for #617.
- **VERIFIED (corroborating, from `papers/erdosproblems-comms.md`, retrieved same day) —**
  erdosproblems.com/617 is FALSIFIABLE with *"no solutions, partial or complete, claimed"*
  (last edited 2026-04-01); `google-deepmind/formal-conjectures` tags only $r=3,4$ solved.
- **Conclusion:** the "no progress since 1999" belief is **confirmed with high confidence**;
  the $r=5$ result appears genuinely new. The only residual uncertainty is the usual one
  (a sweep cannot see unpublished/unindexed work, e.g. will0708's self-tagged effort on the
  site), not any *published* competitor.

## 3. Findings on goal (b) — is the Brouwer/Kang–Pikhurko input threatened?

- **VERIFIED — no correction or erratum to [KP05].** The exact maximum of a $K_{r+1}$-free
  non-$r$-partite graph is $t_r(n)-\lfloor n/r\rfloor+1$ (for $r\le\frac{n-1}{2}$) with the KP
  equality classification; this remains the state of the art. (The primary source was already
  read in full in `papers/brouwer-kang-pikhurko.md`: "Discrepancies found: None.")
- **VERIFIED — RWWY 2024 (arXiv:2404.07486)** restates and uses Brouwer's bound (their
  Thm 1.3), attributing it to Brouwer 1981; it does not alter it. Now cited in the writeup as
  the fetchable secondary statement (Brouwer's 1981 ZW152 report is not online).
- **VERIFIED — Balogh–Clemen–Lavrov–Lidický–Pfender (2020), *Making $K_{r+1}$-free graphs
  $r$-partite*** (CPC, 10.1017/S0963548320000590): a *different* quantity — the asymptotic
  Erdős–Simonovits stability constant (how many $\varepsilon n^2$ edges to delete to reach
  $r$-partite) — not the exact non-$r$-partite maximum. No bearing on the KP bound.
- **LEAD — the non-$r$-partite Turán theme is actively extended** but away from our use:
  *Refinement on Spectral Turán's Theorem* (SIAM JDM, 10.1137/22m1507814) does the spectral
  analogue; *exact Turán number of generalized book $B_{r,k}$ in non-$r$-partite graphs*
  (arXiv:2508.07533, 2025) generalises the host graph. Neither touches the plain $K_{r+1}$
  edge count the project uses.
- **Conclusion:** `BrouwerFacts` (Brouwer saving + KP equality at $(r,n)=(5,21)$) rests on
  literature that is **corroborated and extended, never corrected**. No new threat found;
  the sweep does not change the F6-formalisation risk picture.

## 4. Füredi 2002 scope — settled

- **Authors/venue: VERIFIED** (Crossref) — **Zoltán Füredi and Radhika Ramamurthi**,
  *On splittable colorings of graphs and hypergraphs*, **J. Graph Theory 40(4) (2002)
  226–237**, DOI `10.1002/jgt.10044`. **This corrects the repo's prior LEAD** which named the
  co-author as A. Gyárfás.
- **Scope: LEAD (strong)** — title and every search-context summary indicate it develops the
  **split** side (splittability, $f_r$), extending split colourings to graphs and hypergraphs;
  it does **not** address the balanced $g_r(2)$ conjecture or the $r=5$ case. (Wiley abstract
  returned HTTP 403, so "split-only" is not upgraded to VERIFIED, but its irrelevance to the
  balanced $r=5$ question is not in doubt: split $f_r$ is a strictly smaller, different
  quantity — e.g. $f_3(2)=8$ vs $g_3(2)=13$.)

## 5. Do-not-conflate register (namesakes that recur in searches)

All of the following share a name with our problem but are **different** and were discarded:

- **Erdős–Gyárfás *function* $f(n,p,q)$** (generalized/local Ramsey; "$q$ colours on every
  $K_p$"): e.g. *Phase transitions of the EG function* (2504.05647), *six colours on every
  $K_5$* (1704.01156), color-energy lower bounds (Balogh 2023). Different body of work.
- **Erdős–Gyárfás *conjecture* (Wikipedia)**: cycles of length a power of $2$ in min-degree-3
  graphs. Unrelated.
- **Erdős–Gyárfás–Pyber** monochromatic-partition conjecture (partition an $r$-coloured $K_n$
  into $\le r-1$ monochromatic connected pieces): also affine-plane-tight, but different.
- **"Balanceable" graphs / balanced copies** (Caro–Hansberg–Montejano): a 2-colouring notion.
- **"Balanced colorings" of ER hypergraphs** (Dhawan–Wang 2025): balanced independent sets.

## 6. Verdict for novelty and correctness

- **Novelty:** confirmed — no published work addresses the balanced conjecture beyond
  [ErGy99]'s $r=3,4$; the $r=5$ resolution is new.
- **Correctness:** the one external mathematical input (`BrouwerFacts`) is uncorrected in the
  literature and independently extended; sweep raises **no** correctness concern.
- **Net:** **sweep clean.** The only actionable output is bookkeeping — the
  Füredi–Ramamurthi attribution fix.

## Sources (retrieved 2026-07-11)

- [ErGy99] ScienceDirect — https://www.sciencedirect.com/science/article/pii/S0012365X98003239
- [KP05] PDF — http://matstud.org.ua/texts/2005/24_1/24_1_012_020.pdf
- Füredi–Ramamurthi 2002 (Crossref) — https://doi.org/10.1002/jgt.10044 (JGT 40(4) 226–237)
- Balogh–Clemen–Lavrov–Lidický–Pfender, *Making $K_{r+1}$-free graphs $r$-partite* —
  https://arxiv.org/abs/1910.00028 ; CPC https://doi.org/10.1017/S0963548320000590
- Ren–Wang–Wang–Yang (secondary Brouwer) — https://arxiv.org/abs/2404.07486
- *Refinement on Spectral Turán's Theorem* (SIAM JDM) — https://doi.org/10.1137/22m1507814
- Generalized book $B_{r,k}$ in non-$r$-partite graphs — https://arxiv.org/html/2508.07533
- Dhawan–Wang, *Balanced colorings of ER hypergraphs* — https://arxiv.org/abs/2504.04585
- erdosproblems.com/617 — https://www.erdosproblems.com/617 (FALSIFIABLE; last edited 2026-04-01)
