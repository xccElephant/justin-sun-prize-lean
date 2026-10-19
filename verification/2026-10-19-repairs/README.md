# Existing-submission proof repairs — 19 October 2026

Verified proof commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`. This is a repair batch for existing submissions, not a claim that all original problems have been solved. No new prize problem was submitted.

## Completed substantive missing results

- **Erdős672:** `four_ap_ne_sq` proves that the product of four positive terms of a nonconstant arithmetic progression is never a square, without coprimality or size restrictions. `erdos_672_four_two` gives the original k=4,l=2 interface. Both descent branches, conic parametrization, gcd normalization and the well-founded argument are proved.
- **Erdős711:** `erdos_711.parts.ii` is now unconditional. A finite Hall certificate (416 required indices,414 possible neighbors) at N=5000, exact restriction/scaling, and van Doorn's splice yield the divergence for every sufficiently large n, with m=4n. The former core hypothesis is no longer required.
- **Erdős939:** the infinite-family construction now covers every r>=6, instead of only6,7,8. The terms form a genuine Finset of cardinality r-2, are positive, have setwise gcd1, and each term and their sum is r-powerful. Pairwise coprimality is not claimed.
- **Erdős238:** the c2<2 branch now has every positive c1, every sufficiently large real x, and length strictly above c1 log x, removing the former explicit prime-index hypothesis.

## Other verified repair steps

- Erdos124: gcd necessity for nonzero exponent cutoff, bounded subset-sum approximation, and actual distinct-exponent residue representatives. Sufficiency is not claimed.
- Erdos261: for each finite r, one rational has at least2^r canonical representations, with full summability and distinct denominator-set proof. The rational may depend on r; this is not one rational with continuum many representations.
- Erdos372: an explicit largest-prime-factor existence statement without a custom function in its type; infinitude is not claimed.
- Erdos727: exact factorial/carry equivalence and offset carry lemmas; the construction of infinitely many suitable simultaneous prime-pair congruences remains absent.

All outstanding full-problem obligations remain in `targets.json`. In particular, completing the named subproblem does not set the whole JSP catalog record to solved. PR5080 is now ready for maintainer scope review of its complete finite-existence proof. The29 remaining drafts retain their unresolved requirements. Review readiness does not assert acceptance or eligibility; see [current review status](REVIEW_STATUS.md).

## Verification

The entire project built successfully: **8740 Lake jobs**, exit0. Source hashes before and after the build were identical. The changed modules were checked with Lean4.33.1, mathlib0df444a360eaa60ab8c11dca51a86af692955474, and pinned dependency caches. Bundled Lean kernel replay passed for all eight changed modules through the retained individual audit records. Exact target checks and separate semantic reviews accompany the batch. Only propext, Classical.choice and Quot.sound were observed for the claimed targets.

The replay uses Lean's kernel, not an independent implementation. Imported dependency caches were used; no from-scratch Mathlib rebuild is claimed. Generated theorem counts are not counts of mathematical problems. Development failures are retained in local working evidence and are not represented as successful final proofs.

To reproduce:

```sh
git checkout de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe
lake exe cache get
lake build
lake env lean JspBounties/Erdos672.lean
lake env lean JspBounties/Erdos711.lean
lake env leanchecker JspBounties.Erdos672 JspBounties.Erdos711
```

The check files here belong to this later evidence commit; to run them against the selected proof version, copy `checks/` into that checkout or pass their external path to `lake env lean` after building the selected proof version.

## Mathematical attribution

The four-term product argument follows Tamás Erdélyi, *On the equation a(a+d)(a+2d)(a+3d)=x²*, the author-hosted four-page paper (source code's pp.3–4 reference concerns its descent portion; the full argument spans pp.1–4). The Lean implementation and normalization were written in this repair task. The711 splice is credited to Wouter van Doorn, arXiv:2601.16972, Lemma2; its restriction/scaling idea also appears in Erdős–Pomerance(1980), and the finite Hall certificate was independently generated. The939 binomial construction is credited to GPT-5.5 Pro prompted by Liam Price (forum post24May2026); the delivered Lean proof was newly written and no externally unlicensed Lean source is distributed. Borwein–Loring and Melfi are credited for the relevant261/124 mathematical steps.

These are local formalization contributions with known mathematical sources, not claims of new mathematics, earliest priority or guaranteed prizes. External source documents and unsuccessful development probes are not bundled here. Source details and limits are in the individual reports.
