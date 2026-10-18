# Erdos124 repair status — 2026-10-19

## Completed exact new result

`erdos124.gcd_eq_one_of_eventually`: for every finite D and every nonzero k,
eventual membership in the original power sumset implies `D.gcd id = 1`.
No base lower bound or reciprocal-sum hypothesis is needed.

`erdos124.not_eventually_of_one_lt_gcd`: for nonzero k and `1 < D.gcd id`,
the original sumset is not cofinite (expressed as negated atTop eventual membership).

`erdos124.necessary_conditions`: combines the new gcd necessity and the existing
reciprocal-sum converse. It is explicitly a necessary condition, not a solution of
the positive-cutoff conjecture.

Additional proved auxiliary steps: `subset_sum_gap_bound`,
`residue_representative`, and `exists_mem_sumsOfDistinctPowers_modEq`.
The residue construction uses an injective exponent map into a Finset, so each
exponent is used at most once. The empty residue representative is permitted by
the original definition, but no zero term or repeated-base Waring sum is used to
assert completeness.

## Original primary targets remain incomplete

- `erdos124.ne_zero_three_four_seven`: NOT proved (FC fixes k=1).
- Its strengthening for all k≥1: NOT proved.
- `erdos124.melfi_construction`: NOT proved.
- The general finite gcd1 positive-cutoff sufficiency: NOT proved.

Missing declaration checks were run before implementation; red.log records both
original missing targets and gcd-red.log records the new exact gcd targets.
Definitions and pre-existing theorem hypotheses were not changed.

## Sources and attribution

- FC source: https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/124.lean (saved FC-124.lean, copyright/license retained).
- Burr, Erdős, Graham, W. Wen-Ching Li, Complete sequences of sets of integer powers,
  Acta Arith. 77 (1996), 133–138, https://matwbn.icm.edu.pl/ksiazki/aa/aa77/aa7722.pdf
  (begl.pdf and begl.txt). Page 137 asserts the largest missing integer for {3,4,7}
  at cutoff 1 is 581, using Mignotte–Waldschmidt two-logarithm estimates. It does
  not supply the full small-set proof or a finite modular certificate.
- Giuseppe Melfi, On certain positive integer sequences (2004), Proposition 1,
  https://arxiv.org/pdf/math/0404555 (melfi.pdf and melfi.txt).
  This supplies A={p*n² : n≥1}∪{p+1}, with a prime p chosen large enough.
  Our Euler-period auxiliary construction follows this proposition; no external
  Lean proof code was copied.
- R. Sprague, Über Zerlegungen in n-te Potenzen mit lauter verschiedenen Grundzahlen,
  Math. Z. 51 (1948), 466–468, DOI 10.1007/BF01185779, identified through the original
  Melfi reference and Crossref metadata. Publisher fetch returned HTML, not the
  paper: sprague-access-response.html. We do NOT claim to have read its proof.

## Specific mathematical missing bridges

For {3,4,7}, a finite consecutive interval does not automatically extend forever:
all future weight additions must preserve interval overlap. At reciprocal sum 1,
the needed margin depends on simultaneous clustering of the three next powers.
A modular exploration eliminated many candidate small weighted differences but
left nine cases using the tested moduli. The scripts and logs are exploratory,
not Lean proofs; they do not establish a universal exponent bound or sufficiency.
The nine remaining cases are in modular_followup2.log. A real completion needs
either a kernel-checked modular certificate with explicit transient exponents and
an interval-extension theorem, or the required quantitative two-logarithm bound.

For Melfi, the residue-class step is proved. The essential missing input is
Sprague's statement: for every positive k, all sufficiently large naturals are
sums of distinct positive (2*k)-th powers. Local mathlib search found no theorem
with this statement. Lagrange's four-squares theorem permits repetitions and
addresses k=1 only; a bounded-number-of-fourth-powers result also permits
repetitions unless distinctness is explicitly proved and does not cover every k.
The further construction steps (strictly increasing enumeration of A, reciprocal
series estimate arbitrarily small, and combining bounded residue representatives
with eventual multiples of p^k) are also not yet implemented. No Sprague or core
completeness assumption was added to a claimed final theorem.

## Verification

Actual source compilation: green.log and artifact-build.log.
Exact public types, including k≥1 negated cofinite and the base-4/mod-3^k residue
specialization: exact-checks.lean and exact-checks.log.
Full theorem axiom enumeration: all-theorems.lean and all-theorems.log.
Kernel replay of the freshly built olean: kernel-replay.log and kernel-replay.exit.
No Git commit or external PR was created. All task writes are confined to
JspBounties/Erdos124.lean and this verification directory.

Final verification: all four compilations exited 0; kernel replay exited 0.
Full audit enumerated 78 theorem declarations (including generated ones),
with no axioms outside propext, Classical.choice, Quot.sound.
Pre-existing definitions and theorem bodies compare byte-for-byte unchanged.
