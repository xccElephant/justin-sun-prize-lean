# Bounded sidecar: JSP-000644 and JSP-000679

Decision: **stop both candidates at existing full-problem source endpoints; neither is admitted as a demonstrated missing implementation route.** This is a bounded semantic/source review, not a kernel certification or a claim of prize eligibility. No PR mutation, implementation copying, or competitor build was performed. External Lean files saved here are read-only source evidence, not submission code.

## Fixed evidence

Original awards catalog: `fd8fa66abb4e21df828fdebc25298e9ad75521bd`, `problems/catalog-0601-0700.md`: JSP644 lines 739–754; JSP679 lines 1343–1358. Both say Solved / Lean No / Eligible No. These fields and the title-hit lists from `LEAN_CANDIDATES.json` and `PR_METADATA.json` were used only as leads. `NEXT_STRATEGY.md` appended census was read (1072 / 677 / 295 / 37 / 258).

Existing plby source: **`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`**. Working checkout was clean. Fixed-commit remote downloads of both top-level Lean files matched local bytes. Paths below are relative to `reference/lean-proofs/src/latest/`. Dates crossed the local midnight boundary during assessment; evidence directory retains the requested 2026-10-19 name.

## JSP-000644 = Erdős784

Full displayed original obligation is saved in `erdos784.html:401`: for each C>0, existence of an exponent and a positive implied constant, uniformly over all sufficiently large x and all integer A⊆[1,x] with reciprocal mass ≤C, giving at least a constant times x/(log x)^c nonmultiples. The displayed text allows 1; explanatory text at line 419 explicitly discusses the intended exclusion of 1. It is not simply a request for some positive asymptotic density.

**Complete source endpoint for the literal reading:** `ErdosProblems/Erdos784.lean:1762`,
`erdos_784 {C : ℝ} (_hC : 0 < C) : LiteralAnswer C ↔ C < 1`.
Definitions at lines 55–100 fix reciprocal mass, actual divisibility, integer prefixes, and the quantifier order ∃c,K>0 ∃N₀ ∀N≥N₀ ∀A. Literal failure at C≥1 uses A={1} (1733–1758); C<1 uses the actual covered/uncovered partition and union bound (104–216).

**Complete source endpoint for intended reading:** same file line 1722,
`erdos_784_corrected {C : ℝ} (hC : 0 < C) : CorrectedAnswer C ↔ C ≤ 1`.
The C=1 theorem at 705–714 provides exponent **3**, sufficient for the question although weaker than sharp x/log x. C>1 is genuinely refuted through a boundary-set construction, not assumed: reciprocal mass estimate at 883, negligible boundary cardinality at 1427, eventual admissibility at 1570, sub-polylog survivor size at 1644, contradiction at 1691–1718. The additional analytic module imports Mathlib, with no custom number-theory proposition assumption in its interface. No `sorry`, `admit`, `axiom`, or `opaque` declaration was found in these two actual proof modules. ComparatorChallenges files are statement templates containing `sorry`; they are not the submitted proof modules.

Primary theorem source: Andreas Weingartner, **The Schinzel-Szekeres function**, arXiv **2310.13038v2**, 13 June 2025; saved PDF and extracted text. §1.3, condition (3), and **Theorem 5**, printed p.4 (`weingartner-v2.txt:188–218`) give H(x,z) ≍ x^(exp(1-z))/log x uniformly for 1≤z≤Z. This yields the intended threshold; the union bound supplies 0<C<1. A={1} settles the literal distinction. The sharper asymptotic is not an extra obligation of the displayed question.

Lean uses N∈ℕ instead of real x. This does not leave a number-theory gap: put N=floor x; the integer set and survivors are unchanged, and for sufficiently large x, N≥x/2 and log N≤log x. A natural-prefix bound therefore gives the real-prefix bound after halving its constant. No new prize route arises from this routine bridge.

## JSP-000679 = Erdős823

Original sequence obligation saved in `erdos823.html:401`: **∀α≥1**, positive integer sequences with equal σ term by term and quotient limit α. Catalog wording expands this to all positive target reals.

Primary full theorem: Paul Pollack, **Remarks on fibers of the sum-of-divisors function** (2015), **Theorem 1**, printed p.1 (`pollack-preimages-maier3.txt:25–30`): every β>0 admits arbitrarily close equal-σ quotients. Full §2 proof is in the saved author-hosted PDF `https://www.pollack-math.net/preimages-maier3.pdf`. It uses an unequal-slope prime-pair theorem, abundancy-log density, and pairwise coprime multiplication. It is not an elementary finite-witness theorem.

**Full exact sequence endpoint:** `ErdosProblems/Erdos823.lean:72–84`,
`erdos_823 : ∀ α : ℝ, 1 ≤ α → ∃ n m : ℕ → ℕ, (∀k,0<n k) ∧ (∀k,0<m k) ∧ (∀k,σ 1 (n k)=σ 1 (m k)) ∧ Tendsto (fun k ↦ (n k:ℝ)/(m k:ℝ)) atTop (nhds α)`.
The preceding theorem at 44–67 builds sequences using error 1/(k+1). Its prime input is supplied, not passed as a final theorem hypothesis: `Erdos823/AffineSieveS2.lean:3880–3896` proves `affinePrimePairProperty_105`; lines 3811–3834 assemble unconditional Bombieri–Vinogradov and ordinary PNT. `Assembly.lean:66–75` maintains genuine σ-equality using coprimality; 137–210 proves arbitrary logarithmic/ordinary approximation. The seven actual Erdős823 modules contain no `sorry`, `admit`, custom `axiom`, or `opaque` declaration.

Dependency pin: `lakefile.lean:24–25` fixes FormalPantheon/BoundedGaps at **`ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`**, plus the compatibility patches in plby's fixed commit. Read-only downloads show BV `Proof/MainTheorem.lean:14–15` is a theorem invoking the weighted proof endpoint, and ordinary PNT `Proof/MainTheorem.lean:17–38` is a theorem from prime-counting equivalence. This bounded review did **not** recursively certify the entire large transitive analytic development; no concrete discrepancy justified a full build. Source endpoint completeness is the decisive stop criterion, not a claim that a fresh build passed.

Catalog-positive targets below 1 require only inversion: for 0<α<1 apply the endpoint to β=1/α, then exchange n and m. Quotients invert because both sequences are positive; continuity of inversion at β≠0 gives limit α and σ equality is symmetric. Dependencies: `Tendsto.inv₀`, positive Nat casts, and field simplification. This is a wrapper over the existing full result, not a missing mathematical core or credible new priority claim.

Later PR4731 is weaker: fixed source `kunjunsong-code/jsp-000679-lean@da127f8f5b8973da9ea42f8cec646ab74a891e3d`, `Jsp/JSP000679.lean:76–86` proves existence of one equal-σ pair/triple only. No real target, epsilon, or convergence occurs in its final types. It does not independently settle the problem; the stronger plby endpoint already exists. Live PR4731 metadata and file diff are saved.

## Result and limits

**Zero new implementation targets admitted.** Both have full-scope fixed source endpoints with direct line evidence. No genuine bounded mathematical lemma remains uncovered here. The all-positive inversion and real-prefix bridges are routine consequence wrappers. Neither compilation, PR title, absent documentation (`tex/784.tex` / `tex/823.tex` was not locally present), nor catalog metadata was treated as evidence of vacancy or proof validity. Prize acceptance and exhaustive transitive kernel review remain outside this bounded assessment.
