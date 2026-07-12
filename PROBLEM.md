# Erdős Problem #617 — exact statement and definition of done

Source: T. F. Bloom, Erdős Problem #617, https://www.erdosproblems.com/617, accessed 2026-07-05.
Page last edited 2026-04-01. Status there: **FALSIFIABLE** — "Open, but could be disproved with a finite counterexample."

## Statement (verbatim from the source)

> Let $r\geq 3$. If the edges of $K_{r^2+1}$ are $r$-coloured then there exist $r+1$ vertices with at least one colour missing on the edges of the induced $K_{r+1}$.

Site remark, verbatim:

> In other words, there is no balanced colouring. A conjecture of Erdős and Gyárfás [ErGy99], who proved it for $r=3$ and $r=4$ (and observed it is false for $r=2$), and showed this property fails for infinitely many $r$ if we replace $r^2+1$ by $r^2$.

## Pinned definitions

- An **r-colouring** of $K_n$ is a function from the edge set to $\{0,\dots,r-1\}$ (not necessarily surjective).
- An r-colouring of $K_n$ is **balanced** (following the site's usage) if **every** $(r+1)$-subset $S$ of the vertices sees **all** $r$ colours among the $\binom{r+1}{2}$ edges inside $S$.
- The conjecture, restated: for every $r\geq 3$, $K_{r^2+1}$ has **no** balanced r-colouring.
- **Monotonicity** (elementary, verify for yourself): a balanced r-colouring of $K_n$ restricts to a balanced r-colouring of any $K_m$, $r+1\leq m\leq n$, on a subset of vertices. So it is natural to define $N(r)$ = the largest $n$ admitting a balanced r-colouring of $K_n$. The conjecture says $N(r)\leq r^2$ for all $r\geq 3$; ErGy99 says $N(r)\geq r^2$ for infinitely many $r$; $N(2)=5$.
- **First open case, and the focus of this repo: $r=5$. Does $K_{26}$ admit a balanced 5-colouring?** The conjecture predicts NO.

## Worked examples (re-derive these before doing anything else)

1. **(r=2, n=5, balanced — PASSES verify.py)** Pentagon colouring of $K_5$: colour 0 on the 5-cycle edges $\{i,i+1 \bmod 5\}$, colour 1 on the 5 "diagonals" $\{i,i+2 \bmod 5\}$. Balanced because a 3-set missing colour 1 would be a triangle in $C_5$ (none exist), and a 3-set missing colour 0 would be a triangle in the complement of $C_5$, which is again a 5-cycle (none exist). This witnesses $N(2)\geq 5$, i.e. the conjecture's statement is FALSE for $r=2$ at $n=2^2+1=5$. File: `data/small_cases/pentagon_r2.json`.
2. **(r=2, n=5, not balanced — FAILS verify.py)** All 10 edges colour 0: the set $\{0,1,2\}$ sees only colour 0, so colour 1 is missing. Exactly $\binom{5}{3}=10$ violating 3-sets.
3. **(r=2, n=6 — statement-level example)** No balanced 2-colouring of $K_6$ exists: $R(3,3)=6$ means every 2-colouring of $K_6$ has a monochromatic triangle, which is a 3-set missing a colour. Hence $N(2)=5$ exactly. This is the shape of phenomenon the conjecture asserts at $n=r^2+1$ for every $r\geq 3$.
4. **(the target, r=5, n=26)** A JSON certificate (format in `tools/verify.py` docstring) for which `verify.py` reports BALANCED would disprove the full conjecture.

If your reading of the problem disagrees with any worked example, your reading is wrong — stop and re-read.

## What counts as a win, in decreasing order

- **W1.** A balanced 5-colouring of $K_{26}$ that passes `tools/verify.py` → the conjecture is disproved outright.
- **W2.** A proof — human-readable, or a solver-generated certificate (e.g. DRAT) that survives independent checking — that no balanced 5-colouring of $K_{26}$ exists → the $r=5$ case is settled, extending Erdős–Gyárfás ($r=3,4$).
- **W3.** Verified partial results: the exact value of the largest $n$ with a balanced 5-colouring of $K_n$ for as large a range as computable; proved structural lemmas about balanced colourings; verified constraints that shrink the search space.

All three are real results. W3 is the ratchet that makes W1/W2 reachable across sessions.
