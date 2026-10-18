# Erdos261 repair handoff

Scope: only `JspBounties/Erdos261.lean` and this directory. No commits or PRs.
The original `Erdos261Prop` and `Erdos261InfiniteRepresentation` definitions are unchanged.

## Actual result

`erdos_261.variants.arbitrarily_many_representations (r : ℕ)` proves

```
∃ x : ℚ, (2 : Cardinal) ^ (r : Cardinal) ≤
  #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}
```

The rational is explicit: `2 - ∑ i : Fin r, dyadicWeight (blockStart i.val)`.
For each Boolean vector remove either the singleton `n_i` or the equal-mass
interval `(n_i,n_i+i+2]`, where `n_i = 2^(i+3)-(i+2)-2`.
The full replacement supports are disjoint. The resulting cofinite positive
set is enumerated by its order isomorphism with ℕ. A marker `n_i` distinguishes
the two choices, proving an injection into canonical representations.
This ensures strict increase, no repeated denominator, rational convergence,
and a genuinely different denominator set for every Boolean vector.

Other retained general results:
- `finite_deletion_representation`: canonical rational representation after any finite deletion.
- `canonicalEnumeration_range` and `canonicalEnumeration_representation`.
- `representations_le_continuum`: every canonical fiber has cardinal at most continuum.
- `interiorRemainder_successor`: every strictly interior integer remainder has an interior successor.
- `interiorRemainder_branch_iff`: at layer n, both successors are strictly interior iff `2*r = n+2`.
- `interiorRemainder_branch_values`: the two successors are `1` and `n+2`.
- `interiorRemainder_complement` and `interiorRemainder_complement_step`: complementary paths.

The experimental 1..9 finite cases were removed from the main file following
coordinator steering. They are not presented as a repair of part ii.

## Core goals NOT completed

Part ii remains `∀ n > 0, Erdos261Prop n`. It asks for a finite decomposition
for every positive n, not finiteness of the number of decompositions.
No argument proved termination for every n. Greedy finite computations do
not supply this missing quantifier.

Part iii remains `∃ x : ℚ, 𝔠 ≤ #{a | Erdos261InfiniteRepresentation x a}`.
The proved result has quantifiers `∀ r, ∃ x_r`; it does not give `∃ x, ∀ r`,
and even the latter alone would not establish continuum cardinality.
No axiom, sorry, modified representation definition, or conditional theorem
named `parts.ii`/`parts.iii` has been inserted.

### Precise continuum obstruction and next mathematical interface

For x=1, scaled integer remainders satisfy
`R_n = 2*R_(n-1) - b_n*n` and `0 < R_n < n+2`.
Every interior state extends forever (the one-step lemma is proved).
Both children remain interior exactly at the central state
`2*R_(n-1) = n+1`; their remainders are 1 and n+1.
The two children follow complementary paths until the next central return.
A finite recurrence search cannot establish infinitely many returns.
The coordinator checked the smallest-branch orbit through 10^6 layers:
branching indices (zero-based previous layer) were
0, 2, 78, 234, 430, 1502, 2942, 6058, 6618, 18910, 54222,
with no further branch seen before 10^6. This is supplied numerical evidence,
not a theorem. Our reproducible local search only runs through 20000.

The next useful theorem would show infinitely many central returns for an
explicit rational initial state, or construct a closed binary subtree with
both child paths possessing further central descendants. Complementarity
alone supplies no such return and no repeating time-index map was found.
With that theorem, the path injection and telescoping remainder bound could
establish one rational continuum fiber. Alternatively, a sparse-block route
must construct an outside-denominator subset of exactly the missing rational
mass; deleting full blocks breaks naive tail-domination at their boundaries.
The all-positive total x=2 cannot carry optional blocks: strict positivity
forces inclusion of every positive denominator.

## Red and verification

- `Red.lean` / `red.log`: original parts ii/iii identifiers missing (watched red).
- `red-intermediate.lean` / `red-intermediate.log`: new general declarations missing before insertion.
- `green-final.log`: final whole-file compilation and printed axiom dependencies.
- `Erdos261.olean`: compiled final module, stored here to respect output scope.
- `remainder_search.py` / `.json`: explicitly exploratory finite graph search.

The final printed dependencies are only the standard Lean axioms
`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or problem-specific axiom.

## Sources / attribution

The equal-mass identity is attributed in the source to Peter Borwein and
Terry A. Loring (1990), as in the original module. The new glue proofs and
finite-block construction were written locally; no external Lean proof code
was copied. Mathlib APIs were checked against the installed v4.33.1 sources.
The remainder route was suggested by the coordinating agent.

Read-only source checks:
- https://www.erdosproblems.com/261
- https://www.erdosproblems.com/forum/discuss/261
- https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/261.lean

FC currently labels ii/iii open; this was not treated as a reason to stop.
