# How solutions are communicated to / via erdosproblems.com

**Retrieved 2026-07-11** by research agent, for the human owner's decision-making on the r=5 candidate.
Grading: **VERIFIED** = I fetched and read the primary source; **LEAD** = secondhand (search summary, recollection, or inferred).

---

## TL;DR — recommended sequence

For a candidate resolution with a Lean formalization, the community-blessed path (this is exactly the
situation the site's own wiki page "What to do when I think I managed to get AI to solve an Erdős problem"
was written for) is:

1. **[Owner's call] Do the due-diligence checklist first** — literature review, understand the proof
   well enough to explain it without the AI, sanity-check that it isn't solving a mis-stated/technicality
   version. (See §4.) A short, suspiciously elementary proof of a long-standing problem is a *red flag* to
   the community, so pre-empt it.
2. **Get a `sorry`-free, axiom-clean Lean proof** and verify it yourself per the leanprover-community
   "did_you_prove_it" guide. The site treats a valid Lean certificate as the thing that "significantly
   increases the chance your solution receives expert attention." Ideally the *statement* is formalized by
   a human/third party, not by the proving AI (guards against misformalization). **Note:** #617 is
   FALSIFIABLE — the win is a *counterexample* (an explicit balanced colouring of K_26), which is a finite
   object that can be checked directly and formalized as "this colouring has the property," a much lower
   formalization bar than a universal proof.
3. **Post to the #617 problem/forum page** with a short informal summary + a link to an external PDF and
   the Lean repo. Disclose AI assistance. Do **not** paste the full proof inline. This is the submission;
   there is no separate form. (Registration required to comment.)
4. **[Owner's call] Coordinate with will0708** — a user has publicly self-tagged "Currently working on
   this problem" on the #617 page. Erdős problems are explicitly "not a competition"; a courtesy heads-up
   before a public claim is in keeping with site norms (§6).
5. **Let the community assess before amplifying.** The wiki's #1 cautionary note is *avoid rushing to
   announce*; several AI claims were walked back days later. The site status is Thomas Bloom's editorial
   call and changes when he's satisfied.
6. **[Owner's call] arXiv preprint / write-up.** For a formalized result the Lean cert can trigger the
   status change *before* a preprint exists (that's what happened with #728). A clean arXiv note titled
   "Resolution of Erdős Problem #617" (or "A balanced 5-colouring of K_26…") with the repo link is the
   standard durable artifact and can follow. An invited blog post on the site is a possible later step if
   Bloom asks for one.

Steps 1, 4, and 6 are the human owner's judgement calls. Steps 2–3 and 5 are mechanical / etiquette.

---

## 1. Editorial mechanics — who runs it, how status changes

**Two distinct properties, don't conflate them:**

- **erdosproblems.com** — the canonical site. Made and run by **Thomas Bloom** (mathematician; site
  launched ~May 2023). The open/solved status of each problem "reflects the current belief of the owner of
  this website," i.e. Bloom decides officially. *(VERIFIED: FAQ + #617 page text.)*
- **github.com/teorth/erdosproblems** — a *community database* mirror, "Maintained by Thomas Bloom and
  Terence Tao." Its status labels are an **"unofficial crowdsourced classification"**; the CONTRIBUTING.md
  explicitly says erdosproblems.com is "the more reliable source" when the two disagree. *(VERIFIED:
  README + CONTRIBUTING.md.)*

**How to change a status:** There is no formal submission form. The FAQ says plainly: *"If you have an
update on the status of any problem, please leave a comment below the problem or email me at
thomas.bloom@… ."* Changes to the GitHub database go via **pull request editing `data/problems.yaml`**
(the "ground truth" file), but the CONTRIBUTING guide routes *mathematical* discussion of solutions to the
erdosproblems.com problem page, not the repo. *(VERIFIED.)*

**Evidence bar:** For the official site, Bloom updates when convinced. In practice for hard problems the
community expects either (a) a proof a human has understood and verified, or (b) a `sorry`-free Lean
formalization. The GitHub `formalized` field is auto-generated from the
**google-deepmind/formal-conjectures** repo. Status vocabulary (from CONTRIBUTING.md): `proved`,
`disproved`, `solved`, `falsifiable`, `verifiable`, `decidable`, `open`, plus set-theory variants. #617 is
currently **`falsifiable`** — open, but disprovable by a finite counterexample. *(VERIFIED.)*

## 2. The comment / forum system + etiquette

The site has a per-problem discussion forum. **You must Login/Register to post.** Comments are moderated
(Bloom + moderators); rule-breaking comments are silently not shown. The forum's stated purpose is
pointed: *"for human mathematicians to exchange ideas… this site does not exist to serve as a benchmark
for AI progress, or for people to request feedback on their AI-generated proofs if they do not understand
them themselves."* *(VERIFIED: /forum/ policy page.)*

The **binding rules** (quoted/paraphrased from the forum policy):
1. AI assistance in generating ideas or wording is **allowed but must be disclosed**. All mathematical
   claims must be **independently verified by a human before posting**.
2. **If you don't understand the mathematics yourself, don't post it.**
3. **Long proofs must not be pasted inline — link to an external PDF.** If the PDF is AI-generated, you
   must have read and understood it.
4. If you think an AI solved a problem, read the wiki advice first; only post once you have *either*
   (a) understood and verified it yourself, *or* (b) a `sorry`- and bug-free Lean formalization.
5. **The harder the problem, the higher the bar.** A suspiciously short proof that waves away a key
   difficulty "will likely not be allowed."

Customary announcement style (from observed threads): a short comment on the problem page — one paragraph
of what was proved + method — with links to the preprint and Lean repo. Not a full write-up in the comment.

## 3. Norms for AI-assisted solutions (this is a well-trodden path now)

The GitHub wiki (last updated 2026-06-30) has an entire section on AI contributions, including a page
literally titled **"What to do when I think I managed to get AI to solve an Erdős problem."** *(VERIFIED.)*
Its checklist, which doubles as what the community will judge the submission against:

- Can you communicate the main ideas **without consulting the AI**? If not, red flag.
- Do you understand *why the problem was posed* and could you be solving the wrong version? (Erdős or the
  site sometimes stated problems imprecisely — "disclaimer 4".)
- Have you done a real literature review (Google Scholar / MathSciNet / zbMATH, forward+backward citation
  search)? Many "open" problems were already solved in the literature.
- Does the method look suspiciously short/elementary, prove far more than asked, or not use the
  hypotheses? All red flags for a mis-formalized version.
- **Best practices:** ask an AI to *critically* attack the proof (guarding against sycophancy); write to
  professional standards; **produce a Lean formalization and verify it** (the single biggest lever for
  getting expert attention); have the *statement* formalized by a human/third party.
- **Then** announce on the problem page. And: **"Avoid rushing to announce" — it has happened many times
  that an AI proof was announced on social media after preliminary positive comments, only to be corrected
  days later.** Wait for community assessment.

Formalization policy nuance (CONTRIBUTING.md): Lean proofs *conditional* on prior results are accepted if
those results are either widely-accepted published results (that don't trivially contain the answer) or are
themselves formalized. Watch for the disclaimer-8 exploits: unproved axioms, misformalized statements, and
suspiciously short/long proofs.

## 4. Case studies — how recent AI-assisted solutions were handled

### Erdős #728 — first credited autonomous AI solution (Jan 2026) *(VERIFIED: #728 page, blog, arXiv abstract)*

- **What/who:** Solved by Kevin Barreto operating **GPT-5.2 Pro (OpenAI)** for the informal argument +
  **Aristotle (Harmonic)** for the Lean proof. The problem statement was *ambiguous* with trivial
  solutions; the AI resolved the interpretation "in the spirit intended." The #728 page now credits it in
  prose: *"Barreto and ChatGPT-5.2 have proved that…"* and is labeled **PROVED (LEAN)**.
- **Sequence & timing:** Lean proof completed ~**Jan 6, 2026**; the problem page was edited to
  PROVED (LEAN) the **same day (last edited 06 Jan 2026)** — i.e. the verified Lean certificate drove the
  status change *immediately*, before any preprint. An arXiv write-up (**arXiv:2601.07421**, "Resolution of
  Erdős Problem #728: a writeup of Aristotle's Lean proof," authored by **Nat Sothanaphan** — a
  mathematician who wrote up the machine proof for human readers) was submitted **Jan 12** (rev. Jan 26).
  Barreto was then **invited by Bloom** to write a first-person site blog post, **"Problem 728 and the use
  of AI on Erdős problems," 26 Jan 2026.**
- **Credit model:** the operator/human-in-the-loop is the named author; the AI systems are named
  explicitly (OpenAI GPT-5.2, Harmonic Aristotle); a separate mathematician did the accessible write-up.
- **Verification:** Terence Tao is reported to have personally vouched for / verified the autonomous
  status, which cemented consensus. *(LEAD — this specific "Tao verified it himself" claim is from a
  secondhand Medium piece; the Lean cert is the VERIFIED artifact.)*

### Unit-distance conjecture disproof — Erdős #90/#92 (May 2026) *(VERIFIED: Notable-cases wiki; LEAD on author list)*

- **What:** An **OpenAI-generated** counterexample disproving the unit-distance conjecture (resolved #90,
  also disproved #92) — a much-studied problem, so a bigger deal than #728.
- **Artifacts:** a human-verified write-up **arXiv:2605.20695** ("Remarks on the disproof of the unit
  distance conjecture") plus a companion lower-bound paper **arXiv:2605.20579**, a **MathOverflow**
  discussion, and a site **blog post** (forum/thread/blog:6, "Sum-product, unit distances, and number
  fields," Bloom, 31 May 2026). *(VERIFIED via Notable-cases wiki links.)*
- **Credit/verification:** the "Remarks…" paper is a **human expert** write-up/verification of the
  AI-produced construction; reported authors include Noga Alon, Thomas Bloom, W. T. Gowers and others.
  *(LEAD — author list is from a search summary, not the arXiv page itself.)* Pattern here: because it's a
  *construction/disproof* (not Lean-formalized), the durable artifact was an **arXiv preprint written and
  checked by human experts**, then announced via site blog + MathOverflow.

**Two credit/announcement patterns, pick by artifact type:**
- *Formalized proof* (#728 model): Lean cert → post on problem page → status flips fast → arXiv write-up +
  invited blog follow. Best fit if we have a Lean-checked object.
- *Human-checkable construction/disproof* (unit-distance model): arXiv preprint (human-verified) → announce
  on problem page / blog / MathOverflow. Fits a counterexample colouring even without full Lean.

Other AI-assisted precedents on the site: #1026 (Dec 2025, blog by Tao), #1196 (Apr 2026, blog by Tao). All
were announced on-site with an arXiv link and a narrative blog post. There is a standing **"AI
Contributions" general forum thread (625+ posts)** where such results are also surfaced.

## 5. The #617 page specifically *(VERIFIED: fetched 2026-07-11)*

- **Status: FALSIFIABLE** — "Open, but could be disproved with a finite counterexample." Last edited
  **01 April 2026.** Formalised statement: **Yes** (statement, not solution).
- **Statement on the page** matches our PROBLEM.md: *"Let r≥3. If the edges of K_{r²+1} are r-coloured
  then there exist r+1 vertices with at least one colour missing on the edges of the induced K_{r+1}."*
  Refs [ErGy99] [Er99]. Proved r=3,4; false r=2; fails for infinitely many r if r²+1 → r².
- **Comments/claims: none.** The page states outright *"There are no solutions, partial or complete,
  claimed in the comments."* There is **1 comment** on the problem (author not the claimant).
- **Self-tags (sentiment widgets, not claims):**
  - "Likes this problem" → **eigensolver**
  - **"Currently working on this problem" → will0708**
  - "Interested in collaborating" → none; "looks difficult/tractable" → none; formalisation tags → none.
- **Read on will0708:** this is a self-selected "I'm working on it" flag, **not** a posted result or
  partial claim. So the field is open, but someone has planted a flag. See §6.
- **Citation format the site wants:** *T. F. Bloom, Erdős Problem #617, https://www.erdosproblems.com/617,
  accessed 2026-07-11.* (And: cite Erdős's original sources for the problem itself.)

## 6. Coordination courtesy (will0708)

Site culture is explicitly **anti-competitive**: the wiki states *"Erdős problems are not a competition…
an overly competitive lens is detrimental to the collaborative spirit of modern mathematics and is
generally discouraged."* It also advises, when you have a candidate, to run it past domain experts
"provided you stay respectful of their time," and to coordinate ongoing efforts (the OEIS/issue guidance
uses GitHub issues to "record this effort and coordinate discussion"). *(VERIFIED.)*

Given will0708's public "Currently working on this problem" tag with no posted results, the courteous move
before any public claim is a brief, friendly heads-up (a comment on the #617 page or a DM via the site
inbox) acknowledging their interest. This is a judgement call for the human owner, not a hard site rule —
but it's cheap insurance and squarely in the site's collaborative spirit. There is no evidence will0708 has
a competing result, so this is about courtesy, not priority disputes.

## 7. Write-up artifact standards

- **Where:** arXiv is the standard home for the durable write-up (all recent AI-assisted resolutions used
  arXiv). The site itself hosts only short comments + occasional invited blog posts; long content lives in
  an external PDF you link.
- **Title/format:** "Resolution of Erdős Problem #N: …" is the established title pattern (cf. 2601.07421).
  For a counterexample, a descriptive title ("A balanced 5-colouring of K_26 disproving…") works too.
  Length: short is fine and normal — #728's note is a brief paper. Professional writing standards expected
  (the wiki links Tao's "advice on writing papers"). Disclaimer 6/7: a bare solution may have "less utility
  than usual"; adding literature context, related problems (here r≥6, the r²-vs-r²+1 boundary), and the
  method's novelty raises its value and its odds of being publishable.
- **For the formalized component:** link the Lean repo, state the Lean toolchain/Mathlib version, confirm
  it's `sorry`-free and axiom-clean, and point to the leanprover-community verification instructions. If
  the referee `verify.py` also checks the candidate colouring, include it and its command line as
  independent (non-Lean) corroboration.

---

## Sources (all retrieved 2026-07-11 unless noted)

- **VERIFIED** erdosproblems.com **FAQ** — https://www.erdosproblems.com/faq (Bloom is owner; status via
  comment/email; do your own lit search)
- **VERIFIED** erdosproblems.com **forum policy** — https://www.erdosproblems.com/forum/ (comment rules,
  AI disclosure, external-PDF rule, registration)
- **VERIFIED** erdosproblems.com **#617** — https://www.erdosproblems.com/617 (FALSIFIABLE; no claims;
  will0708 self-tag; last edited 01 Apr 2026)
- **VERIFIED** erdosproblems.com **#728** — https://www.erdosproblems.com/728 (PROVED (LEAN); Barreto +
  ChatGPT-5.2 credit; last edited 06 Jan 2026)
- **VERIFIED** erdosproblems.com **blog: Problem 728 and the use of AI** — Kevin Barreto, 26 Jan 2026 —
  https://www.erdosproblems.com/forum/thread/blog:2
- **VERIFIED** GitHub **teorth/erdosproblems README + CONTRIBUTING.md** —
  https://github.com/teorth/erdosproblems (unofficial crowdsourced status; PR to data/problems.yaml;
  formalization policy; "Maintained by Thomas Bloom and Terence Tao")
- **VERIFIED** GitHub wiki **"What to do when I think I managed to get AI to solve an Erdős problem"** —
  https://github.com/teorth/erdosproblems/wiki (due-diligence checklist; "avoid rushing to announce")
- **VERIFIED** GitHub wiki **Disclaimers-and-caveats**, **Notable-cases**, **Getting-started-with-AI**,
  **AI-contributions** (wiki frozen as of 2026-06-30)
- **VERIFIED** arXiv **2601.07421** abstract — "Resolution of Erdős Problem #728: a writeup of Aristotle's
  Lean proof," Nat Sothanaphan, submitted 12 Jan 2026 — https://arxiv.org/abs/2601.07421
- **LEAD** unit-distance disproof — arXiv:2605.20695 / :2605.20579; Notable-cases lists it under #90/#92,
  blog:6 (Bloom, 31 May 2026), MathOverflow. Author list (Alon/Bloom/Gowers) from search summary, not the
  arXiv page itself.
- **LEAD** "Terence Tao verified every proof himself" — secondhand Medium article; treat as context, the
  Lean certificate is the verified fact.
- **CONTEXT** Tao blog on the crowdsourced project (Aug 31 2025) —
  https://terrytao.wordpress.com/2025/08/31/
- **CONTEXT** Xena Project on formalization of Erdős problems (Dec 5 2025) —
  https://xenaproject.wordpress.com/2025/12/05/
