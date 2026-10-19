# Parallel repair campaign — 2026-10-19

## Complete two-number theorem for JSP-000736

`Erdos885.TwoNumbers.literal_two_number_witnesses` proves that for every natural
k there are two positive integers N<M and exactly k distinct positive common
factor differences. `literal_two_numbers` proves the corresponding intersection
cardinality bound. N and M may depend on k.

This is complete for the literal two-number catalog statement, subject to
maintainer confirmation of that scope and terminology. It does not prove the
stronger original Erdős #885 conjecture involving k distinct integers. No award,
priority or novelty claim follows from the technical verification.

- [Self-contained mathematical proof](Erdos885-MATHEMATICAL-PROOF.md).
- [Independent review result](Erdos885-review.json).
- [Independent exact statements and positive-factor definition bridge](Independent885.lean).
- [Independent check output](Erdos885-independent.log).
- [Main build result](Erdos885-build.json).
- [Author source compile log](Erdos885-final-source.log).
- [Author exact target checks](Erdos885-ExactTargets.lean) and [output](Erdos885-exact-targets.log).
- [Bundled kernel replay output](Erdos885-kernel-replay.log).

All commands listed as successful exited 0. The independent check was rerun
from the checked-in `Independent885.lean` before publication and exited 0.
The source SHA256 was unchanged throughout the checks:
`652df654369c775e8afd8df238009a41ff5a2e2a1edce52f8da85a71ad4080d3`.
Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

From the selected proof commit:

```sh
lake exe cache get
lake build +JspBounties.Erdos885
lake env lean -j1 verification/2026-10-19-parallel/Independent885.lean
lake env leanchecker JspBounties.Erdos885
```

The proof uses only `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx` or assumed elliptic-curve infinitude theorem. Kernel replay uses Lean's
own kernel with the pinned dependency caches. It is not an independent kernel
implementation or a from-scratch rebuild of dependencies. The isolated author
olean and project-build olean have different hashes; both paths were checked,
and no claim of byte identity is made.

## Campaign scope

The campaign partitions all 32 existing PR records into 16 work/review groups,
run in batches with a maximum of six simultaneous agents. Completion of a group
report is not completion of its mathematical problems. Detailed campaign outcomes
and live submission counts are maintained separately as groups finish.

Only curated proof evidence is published here. Exploratory failures, third-party
papers and unverified work files remain outside this evidence package.
