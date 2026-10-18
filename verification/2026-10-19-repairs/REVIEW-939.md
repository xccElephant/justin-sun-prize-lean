# Independent review of Erdos939 General construction

Reviewed 2026-10-19. Verdict: **no actionable mathematical or formal-statement defect found** in `General` or `erdos_939.variants.infinite_of_six_le`.

Reviewed source SHA-256: `d7f1d37fa33413ac4f09b027ece083c207d7ea2735e807748e58b2f27ce703ac`.
Only this review file was written; Erdos939 was not edited.

## Acceptance checks

- **Setwise vs pairwise coprime — correct for the actual target.** `Finset.Coprime` is `S.gcd id = 1`; both this definition and `Erdos939Sums` were compared with HEAD and are unchanged. `family_coprime` (939:969) supplies a coprime pair consisting of the first power and the j=1 monomial, which suffices for gcd of the whole set to be 1. The monomials all contain `B^r`, so the family is deliberately **not pairwise coprime**. No claim of pairwise coprimality is proved. Any external summary must preserve “setwise gcd 1”. This is a scope boundary, not a defect in the delivered theorem.
- **Coefficient Finset duplicates — excluded.** `smallCoefficients` has precisely the integers `1 ≤ c < pieces`. `coefficient_spec` proves `remainder > pieces` from the sum bound and `r² < 2*choose(r,3)`. Thus insertion cannot collide; subtraction is not truncated; all coefficients are positive, cardinality is `pieces`, and their sum is exactly the original cubic coefficient.
- **Label duplicates — excluded.** The first label image is injective on exponent and erases exponent 3; the second is injective on coefficient and has exponent 3. `labels_disjoint` separates the two images. Repeated coefficients at different exponents (e.g. 12 at j=1 and j=5 for r=6) are allowed labels and are not collapsed.
- **Actual integer term duplicates — excluded.** `term_valuation` (939:910) proves valuation at prime q is `r*(r-j)` because every coefficient divides positive B and q>B. `label_bounds` ensures `j≤r`, so truncated subtraction cannot destroy injectivity. Equal terms imply equal exponents; cancellation of a strictly positive remaining factor then implies equal coefficients. `term_injective` (939:930) is used in both `sum_image` and `card_image_of_injOn`.
- **First term collision — excluded independently.** Every monomial is divisible by `B^r` since j≥1. The first power is coprime to `B^r`; equality would force `B^r=1`, contradicted by B>1 and r≥6. `first_not_mem` (939:956) is used for both insertion cardinality and sum.
- **r=6 / minimal splitting — correct.** `pieces 6=1`, `smallCoefficients 6=∅`, `coefficients 6={40}`, `labels 6={(1,12),(3,40),(5,12)}`. Together with the distinct first power, there are exactly four terms, i.e. r−2. No hidden demand for two or more split cubic pieces exists. r=7 also has one cubic piece. Odd/even r are covered by `((r+1)/2 - 1) + (r/2 - 2) + 1 = r-2` under r≥6.
- **Fullness and positivity — genuine.** Each positive coefficient divides B; j≥1 lets `full_monomial_term` absorb it into a factor `c*B^r`. The first and total are r-th powers. q>B and r>0 give a strictly positive natural subtraction; no zero-fullness loophole occurs.
- **Binomial sum — correct.** `binomial_difference` assumes Y≤X and uses the odd binomial terms. `labels_sum` replaces only the cubic coefficient with its exact positive partition. `family_spec` (939:994) sums a Finset only after proving all duplicates absent.
- **Parameter injection — correct direction and sufficient domain.** `family_injective` (939:1017) sends equality of sets to equality of sums `(q^r+B^r)^r`, cancels the outer strictly increasing power, common addend, then inner power. Hence different allowed primes yield different sets and different totals. B depends on r alone. Arbitrarily large primes give an infinite parameter domain for every fixed r.
- **Final quantifier — exact.** `infinite_of_six_le` (939:1041) proves `∀ r ≥ 6, (Erdos939Sums r).Infinite`, not just r=6,7,8 or a subsequence of exponents. It takes the infinite injective image and includes it in the target. r=4,5 infinitude remains outside scope and is explicitly excluded in the construction comment.

## Independent verification

Ran `lake env lean --stdin` against the built module with:

1. An example having exactly the final `∀ r ≥ 6` type.
2. Kernel-checked r=6 values above, including exact labels and card=4.
3. An example extracting the complete target fields directly from `family_spec`: card r−2, gcd=1, r-full sum, and positive r-full members.
4. An example proving different prime parameters above B give different `sumFamily` sets using the public injection theorem.
5. `#print axioms` for `family_spec`, `term_injective`, and `infinite_of_six_le`.

Exit code 0. Printed dependencies for all three: `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or problem-specific axiom.

Also independently calculated exact integer families for every r=6..30 using q=B+1 (coprime to B; the Lean valuation argument uses the stronger prime condition). Checked coefficient cardinality/distinctness/positivity, actual term distinctness/card r−2, binomial total, overall gcd 1, first-term coprimality with each monomial, and common `B^r` divisor of the monomials. All passed. These finite checks supplement, rather than replace, the general Lean proof.

The built olean was newer than the reviewed source; the existing whole-module build log succeeded. `git diff --check` was clean. The proof source contains no sorry/admit/native_decide/unsafe or added axiom declaration (the “zero-sorry” occurrence is documentation).

## Review lenses and limits

No pre-existing proof or definition was deleted in this change. New abstractions represent the coefficient partition, labels, and family needed to control actual Finset cardinality. Existing callers still see the same `Erdos939Sums` definition; the new final theorem and `family_spec` were independently instantiated. Mathlib APIs were checked against installed source and compiled, not inferred from memory. Attribution is retained in the construction comment; this review assessed the local proof rather than copying or reviewing external proof code. Broad `import Mathlib` and unused simp warnings are not correctness findings.
