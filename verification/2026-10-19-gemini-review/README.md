# Independent review of the Gemini continuation — 19 October 2026

The new Cohn all-noncube theorem is a real addition to this proof repository.
It compiled with only `propext`, `Classical.choice`, and `Quot.sound`, and the
newly compiled module passed bundled-Lean kernel replay. An independent-context
mathematical review found no defect in the seed, invariant, growth or final
positive/pairwise-coprime/noncube statement. The mathematical source was unchanged
during these checks and matches the published proof commit
`a54cd54b44bc9b565cdb40e3b8ee9e935aa53e61`.

This is a new checked theorem in our project, **not an established new complete
JSP solution or prize priority**. Cohn's all-noncube condition strengthens the
already proved r=3 question; it was not a missing hypothesis of Nitaj's r=3
theorem. The previous project theorem legitimately allowed cubes.

## Same-scope predecessor

PR265, opened on 16 September 2026, already submitted the same all-noncube
infinitude result. Its fixed source is `pcycho/awards` at
`255a6f7e4de24b3a65626fd6860fc31c66b4b8ac`, directory
`submissions/jsp-000780-cohn-noncube/`. This review retrieved and independently
compiled unchanged `Prize939.lean`, `CohnNoncube.lean` and `Audit.lean` using the
same Lean4.33.1 and Mathlib pin. All three exited0. The expanded audit theorem
contains positivity, all three pairwise coprimality conditions, all three
3-powerful conditions, a+b=c, all three noncube conditions, and infinitude.
Its final axioms are the same standard three. We did not replay the predecessor
with a second kernel or rebuild Mathlib from source.

The review comment at
`https://github.com/TheJustinSunPrize/awards/pull/265#issuecomment-5749759383`
states the complete-original-problem requirement and says the submission is
being closed for partial progress. It was posted on 20 September; the PR closed
on 24 September. GitHub labels its author `CONTRIBUTOR`. The comment does not
identify a failing theorem, a missing parameter, or a final committee scope
decision. It is a relevant scope objection, not a mathematical refutation or
an official priority award to the predecessor. Closed PRs remain relevant
prior-art evidence.

Thus the new theorem does not establish that our project is first, that the
JSP scope is only r=3, or that an award will follow. Historical publication
after a problem was posed does not settle formalization priority or eligibility.

## Corrections completed

- E124's degenerate k=0 Melfi addition was already deleted by Gemini. The current
  file is byte-identical to the pre-Gemini file; the positive-cutoff question
  remains incomplete.
- PR5088 linked a nonexistent full SHA beginning `5fe0477`. The correct SHA is
  `5fe04774e75dbfac811c45d1bc235a38c5e97838`. Both its body and catalogue link
  were repaired. The BEGL96 page range was corrected to133–147.
- PR5098 and PR5107 had draft=true but still described themselves as Ready
  scope reviews. Their titles, bodies and proposed catalogue rows now identify
  the p≥3 and k=1 statements as known restricted cases, with p≥5 and k≥2
  respectively still unproved. The valid wrapper theorems were retained and
  independently compiled; they are not new solutions of those original problems.
- PR5089 retains the new theorem and its scope-review status. Its body now
  discloses PR265, the independent same-scope build and the earlier scope
  objection. Its reproduction command builds the module before replay, so it
  does not accidentally replay an old or missing project olean.
- All four edited bodies and three changed catalogue files were read back and
  matched the prepared content. No new award PR, issue or comment was created;
  no Ready/Draft state was changed by this review.

Current count: **5 Ready /27 Draft**, consisting of two complete scoped-proof
reviews, three scope reviews and27 incomplete drafts. Ready is a review state,
not a verified count of complete original problems or awards. Existing scope
and priority issues for the other Ready PRs remain.

## Next investment decision

Keep the checked noncube theorem and maintain accurate existing submissions.
Direct the main implementation effort toward other official JSP problems with
an available complete mathematical proof and a verified, bounded formalization
gap. Do not restart all27 open-core drafts as routine repairs. Reopen a draft
only when a new full proof, a concrete missing lemma with a known proof, or an
explicitly accepted independent scope makes a complete submission plausible.
Completing a known subcase alone does not meet that test.

The assertion that all easy entries have been taken is unsupported: the latest
discovery ledger contains34 records reviewed at different depths out of294,
with260 still without substantive review. Conversely that unreviewed remainder
is not evidence of260 vacant or feasible opportunities. Select a concrete
candidate and verify its hardest step before extensive parallel work.

## Evidence and limits

[Result](RESULT.json), [proof review](PROOF_REVIEW.md),
[our compile](E939-build.json), [our replay](E939-replay.json),
[predecessor compile](prior-build.json), [predecessor actual axiom output](prior-Audit-build.log),
[published corrections](publication-verified.json).

The Leiden PDF endpoint failed with TLS errors (HTTPS) and502 (HTTP) in this
review, so the original two-page scan was not independently reread. The exact
seed arithmetic and general proof were independently checked; this does not
claim fresh historical-paper verification. Third-party proof sources remain
local research inputs, not redistributed as our work. Build/replay used pinned
Mathlib caches and Lean's own kernel, not a second kernel implementation.
