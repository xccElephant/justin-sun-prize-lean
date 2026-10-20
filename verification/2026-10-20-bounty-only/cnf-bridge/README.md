# n12 graph-to-CNF feasibility gate — October 20, 2026

The first complete semantic bridge is proved: for every A ⊆ [1,12] with nine
vertices and six even vertices, its induced coprime graph contains a five-cycle.
The proof assumes a counterexample, normalizes it using proved compression,
constructs all156 variable values, proves all321 original clauses, then applies
the unmodified archived LRAT refutation. This covers the same small instance
as the prior direct20-set proof; it is not a new complete bounty problem.

The new route does not import or use the earlier finite coverage theorem.
`CycleWitness.lean` extracts only the general witness interface, with an added
subset adapter. Counter rows are proved symbolically from counts for arbitrary
B, rather than verified by enumerating eligible sets. Seven concrete C5s are
credited to Cecil Jentges. The formula is parsed directly from his fixed
archive; the output of our Python proof generator must typecheck against it.

## Validation

- All new modules compiled successfully on Lean4.33.1 and the locked Mathlib.
- Joint `Research/Erdos883/Check.lean` compile exited0, including the original
  modules and attributed part(ii), plus a conversion of the LRAT graph result
  to an actual IsCycle walk of length5. See `combined.log`.
- Final graph and normalization targets use only propext, Classical.choice,
  Quot.sound. The LRAT semantic refutation uses only propext.
- A threshold shifted by one fails the archived-clause proof; a repeated
  vertex fails IsCycleWitness. Both negative controls exited1 for the expected
  semantic reason. Sources are stored as `.lean.txt` to keep them out of builds.
- Independent review found no substantive concern. It additionally checked
  every membership-mask counter assignment, exact archived bytes, all seven
  cycle witnesses, and the RUP/LRAT steps. It did not compile Lean; parent
  successful builds separately supply that evidence.
- Generator output reproduces the reviewed source exactly. `SOURCE_MANIFEST.json`
  binds all current Lean source, generator and the CNF/LRAT bytes.

## General count preservation

`CompressionCounts.lean` proves that simultaneous support and equal-support
prefix normalization preserves size/even count and weakly increases the number
of selected odd multiples of three. The lower bound is a candidate constraint;
normalization is derived, never assumed. This is the ingredient needed to keep
a missing-count upper bound, not a completed cmax-constrained certificate.

## Next bounded implementation

Build reusable clause and cycle-block verification, then apply it to the already
replayed n36/b3/l6 archive (598 thirteen-cycle witnesses). The n12 generated
proof is deliberately transparent, but scaling its roughly2700 lines of repeated
clause proofs to99 instances is inappropriate. Prime-swap/lex constraints,
cmax integration, remaining finite arithmetic coverage and analytic tails are
still unproved. Formalization priority and bounty eligibility remain unresolved.
No award PR was created or changed by this work.

The historical `../RESULT.json` and `../SOURCE_MANIFEST.json` describe the prior
0687997 stage; they are retained unchanged. Use the manifests in this directory
for the new source state. No additional leanchecker run was made; the earlier
120-second timeout is still not recorded as passed.

After review and compilation, one trailing blank line was removed from
CycleWitness.lean. No tokens or declarations changed; the source manifest
records the final bytes and the independent review retains its original hash.
