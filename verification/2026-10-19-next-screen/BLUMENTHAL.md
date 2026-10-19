# Blumenthal / JSP000404 / E504: source findings, not a new solution

This review obtained the complete primary source: Bl. Sendov, *Minimax of the
angles in a plane configuration of points*, Acta Mathematica Hungarica69 (1995),
27–46. The Hungarian Academy journal scan was downloaded from
`https://real-j.mtak.hu/7467/1/ActaMathHung_69.pdf`. Pages27–46 were extracted;
the printed page39 was also visually inspected. The full132,038,438-byte volume
has SHA256 `785a71aa2fb338fc7a2964653d75eae4234e83bb9e881ecd1d6d1f02944ec123`.

## A definite source-definition mismatch

PR2804 names `Yi-111-a/jsp-000404-blumenthal-sendov` at fixed commit
`f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061`. Its `lean/JSP404/Defs.lean`
defines `alpha N` directly as the proposed piecewise formula, selected by
`Nat.clog 2 N`. `Main.lean` proves `sendov_minimax_angle` by unfolding that
definition. There is no finite planar configuration, Euclidean angle,
infimum/supremum or proof connecting this numeric definition to the geometric
quantity in those two files. The repository's acceptance prose describes the
geometric problem but is not a proof of that connection.

Thus this fixed advertised theorem is not evidence of a complete geometric
formalization. This conclusion does not require compiling it: a correct proof
of the displayed definitional identity would still not establish the missing
geometric equivalence. No claim of deliberate deception is made.

## Formula discrepancy in the primary source

For the lower interval `2^m < N ≤ 2^m + 2^(m−2)`, final Theorem4.1 on printed
page42 gives `π(1−2/(2m+1))`. Introductory equation1.1 on page27 prints numerator1.
The current E504 page also displays the numerator1 version after reindexing.
The final expression is consistent with the paper's stated five-point value
`3π/5`; the numerator1 version gives `4π/5`. The review does not attribute the
origin of the discrepancy solely to the website.

PR42 documents the discrepancy and proves a geometric five-point bound.
PR100 and PR647 record further finite and dyadic results; PR300 explicitly
limits itself to partial results. These are not presumed complete because
they compile or carry a theorem named after the problem.

## What remains unclosed

Lemma4.1 (printed pp.37–40) seeks the full cardinality bound for perfect
generalized configurations. After the two- and three-center cases it states
maximizing integer-weight profiles for four centers and for general s, without
exhibiting a derivation of those maxima or the inductive transition. Reading
this does not give us an already understood complete proof to translate.
Other submissions report a suspected gap, but this review does not elevate
their statements to proof that the final theorem is false or unknown worldwide.

A local floating-point probe used four centers
`(-1,0),(1,0),(0,1/2),(0,2/3)` and `u/2=15/4`. The maximum center angle was
about126.87 degrees, below the tested132-degree cap. Applying the paper's
angular-gap floor expression numerically produced weights `(4,4,1,1)`, total10,
where the four-center intermediate profile on page39 totals9. However10 equals
the final bound `2^3+2^(3−2)`; it does not violate that final bound.

This probe is **not an exact Lean certificate**, an independently verified
generalized-configuration counterexample, or a disproof of the classification.
It records a concrete issue to examine if a replacement general argument is
attempted. The source file `four-center-exploration.json` preserves these limits.

## Disposition

No new Lean implementation or award PR was started. Before admitting this
problem, we need a complete general lower-bound argument, with all geometric
and combinatorial restrictions checked, or an exact counterexample to the
actual target. A numerical formula defined as the answer, finite cases, or a
gap in one published proof cannot substitute for that result.

Exact fetched sources, PR bodies, extracted primary text and page images are
retained under `reports/opportunity-2026-10-19-next/blumenthal/`; hashes are in
the adjacent source manifest. No competitor PR or official record was modified.
