# Erdős 939 repair sources and boundary

Checked 2026-10-19.

- Source-compatible target and definition: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/939.lean . The local `Erdos939Sums` definition remains unchanged, including positivity and Finset distinctness.
- Mathematical construction: Liam Price's forum post, 24 May 2026, attributing the argument to GPT-5.5 Pro: https://www.erdosproblems.com/forum/thread/939#post-6640 . Expand the odd part of `(X+Y)^r-(X-Y)^r`, split the cubic coefficient, and choose a prime parameter above a multiple of all coefficients.
- The forum links an Aristotle Lean autoformalization. No explicit license was established. The decoded source and copied adaptation were removed. The delivered proof is newly written using Finset labels `(exponent, coefficient)`, Finset coefficient splitting and a direct infinite image argument. No external Lean source is included.
- The provenance library also records the manuscript license as unstated: https://github.com/plasma-ai/erdos/blob/main/library/diophantine_problems/price_2026_infinite_r_powerful_sums/_index.md . It is a discovery aid, not the mathematical authority.

Acceptance checks: exact target `∀ r ≥ 6, (Erdos939Sums r).Infinite`; positive elements; card `r-2`; setwise gcd 1; powerful summands and sum; parameter injectivity; axiom audit. `Targets.lean` was executed before implementation and failed with unknown target; see `red.log`.

Boundary: the binomial construction has too many summands at r=4 and r=5; splitting cannot reduce their number. No positive r=4 witness or r=4/5 infinitude proof is supplied. Existing r=5 nonemptiness remains a separate result. This is not a complete resolution of the broader existence question or all JSP problems.

Validation completed: `lake build JspBounties.Erdos939` passed (see build-reviewed.log); independent Targets.lean passed (green.log), including all r>=6, r=9, r=100 and family_spec. All audited new proof closures are [propext, Classical.choice, Quot.sound]. Two unused simp-argument warnings remain in labels_sum and do not alter theorem checking.
