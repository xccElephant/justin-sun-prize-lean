# Erdős 883 / JSP-000734: bounded implementation candidate

**This is an incomplete research development, not an award submission.**

**Allocation update, later on October20:** this candidate is now in reserve.
The planned n36 expansion is not the default next action. The user requires a
credible complete award submission; unresolved earlier-priority evidence and
the remaining all-n dependencies prevent treating this research gate as an
admitted bounty implementation. The verified code remains intact. See
`verification/2026-10-20-award-path/DECISION.md` for the re-entry conditions and
newly read Della Pietra endpoint evidence. The technical next steps below apply
only if this candidate is readmitted.
The objective is the complete pair of original questions: all permitted odd
cycles for every n, and eventual complete tripartite K(1,l,l) subgraphs.

The currently explored part-(i) route is Cecil Jentges's
*Ordered-weight certificates for odd cycles in dense coprime graphs*, fixed
version `wizardscurtain/erdos-883-ordered-weight-proof` at
`b5738d8944340f0ac9434f70f689316b18497026` (October12,2026). The mathematical
argument and finite certificate data are credited to Jentges. We have not
established global formalization priority or prize eligibility.

## Proven here

- `Compression.lean` proves support-enlarging replacement maps the new coprime
  graph into the original graph, preserving absence of any graph H. Finite
  maximization gives a counterexample of the same size and even count that is
  both support-compressed and prefix-ordered within equal-support classes.
  The two maximizations are nested; no commuting-normalization assumption is
  used. These Lean proofs were independently authored in this project.
- `CompressionCounts.lean` strengthens simultaneous normalization to preserve a
  lower bound on the selected odd multiples of three. This is the count
  monotonicity needed by cmax-constrained certificates; those certificates
  have not yet been integrated.
- `CycleWitness.lean` contains the generic cycle-witness graph interface,
  extracted without changes to the existing theorem statements. Its subset
  adapter supplies actual copies from recorded cycles.
- `FiniteWitness.lean` proves a direct cycle-table-to-graph-containment theorem.
  It verifies all20 admissible sets for n=12, cardinality9 and even count6,
  then obtains a five-cycle. This is an end-to-end finite integration test,
  not an all-n proof and not a proof of the compressed SAT encoding.
- `SequentialCounter.lean` proves prefix count recurrence, monotonicity,
  increment and overflow lemmas for arbitrary input predicates.
- `SatCertificate.lean` exposes Mathlib's parsed DIMACS formula and reconstructed
  LRAT semantic refutation. `N12Certificate.lean` provides the exact archived
  formula and explicit assignment to all156 variables, with member/complement
  count bridges and even-unit derivation.
- `N12Clauses.lean` proves all321 original clauses from a normalized no-C5
  counterexample, using prefix counts for144 auxiliaries and Jentges's seven
  cycle witnesses. `n12_b0_has_five_cycle_via_lrat` discharges normalization and
  obtains the actual graph theorem from an arbitrary eligible A. The module
  does not import `FiniteWitness.lean` or its coverage theorem.
  `scripts/generate_n12_bridge.py` reproduces the clause proofs and checks exact
  archived clause order. The generator is untrusted; Lean checks its output
  against the independently parsed original formula. This proves a second
  route to the same small instance, not broader numerical coverage.
- `ThirdParty/PartII.lean` is the attributed complete fixed-l second-question
  proof from `baobingzhang/jsp-000734-erdos883-lean` at
  `f87d2d526a9f736818133baed805fff4a1e94d10`. Minimal Mathlib API compatibility
  edits preserve all86 declaration signatures and every definition body.
  The Apache-2.0 license is retained. This result is prior third-party work.
- `Check.lean` jointly imports these modules, checks that the graph definitions
  are definitionally equal, restates the compression conclusion in the prior
  graph, and converts the n12 result to an actual IsCycle walk of length5.

The original six-target joint check exited0 on
Lean4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
The new bridge and counts also compile, with no axioms beyond the standard
three; the LRAT refutation itself needs only `propext`. Final combined evidence
is recorded in `verification/2026-10-20-bounty-only/cnf-bridge/`.
No `sorry`, `admit`, `native_decide` or project axiom is used. The finite table's
coverage check locally sets maxRecDepth10000; it still uses ordinary kernel
reduction via `decide`.

## Reproduce

Run from the repository root. These research modules are intentionally outside
the existing submitted `JspBounties` default build target.

```sh
lake env lean -o Research/Erdos883/Compression.olean Research/Erdos883/Compression.lean
lake env lean -o Research/Erdos883/ThirdParty/PartII.olean Research/Erdos883/ThirdParty/PartII.lean
export LEAN_PATH="$(lake env printenv LEAN_PATH):$(pwd)"
lake env lean -o Research/Erdos883/CompressionCounts.olean Research/Erdos883/CompressionCounts.lean
lake env lean -o Research/Erdos883/CycleWitness.olean Research/Erdos883/CycleWitness.lean
lake env lean -o Research/Erdos883/SequentialCounter.olean Research/Erdos883/SequentialCounter.lean
lake env lean -o Research/Erdos883/SatCertificate.olean Research/Erdos883/SatCertificate.lean
lake env lean -o Research/Erdos883/N12Certificate.olean Research/Erdos883/N12Certificate.lean
python3 Research/Erdos883/scripts/generate_n12_bridge.py
lake env lean -o Research/Erdos883/N12Clauses.olean Research/Erdos883/N12Clauses.lean
lake env lean -o Research/Erdos883/FiniteWitness.olean Research/Erdos883/FiniteWitness.lean
lake env lean -o Research/Erdos883/Check.olean Research/Erdos883/Check.lean
```

An additional bundled `leanchecker -v Research.Erdos883.Check` run was terminated
after120seconds. It is **not recorded as passed**, nor is the timeout a proof
failure. This checker uses Lean's kernel, not a second kernel implementation.

## Outstanding gate before committing to the full candidate

1. Integrate the proven missing-count monotonicity in cmax instances, and prove
   simultaneous prime-swap lexicographic canonicalization.
2. Generalize the completed n12 bridge to varying size/even/odd-multiple
   counters and larger recorded cycles. Avoid expanding every clause into
   large repeated proof text for all99 instances; prove reusable schema
   verification first, then test n36/b3/l6. Lex auxiliary assignments remain
   open. The n12 instance has no cmax or prime-swap constraints.
3. Reconstruct and kernel-check all99 LRAT obligations and670,834 recorded cycle
   witnesses. Two unmodified proof files (n12,b0,l2 and n36,b3,l6) have already
   replayed through Mathlib's `lrat_proof`; deleting the final step in the first
   was rejected. n12 now has its graph bridge; n36 remains CNF-only.
4. Complete every finite arithmetic family, the exceptional cases and167 block
   certificates through10^8. Stored success flags are not proof inputs.
5. Prove uniform infinite-range estimates, including primorial continuation,
   finite prime-class counts, Euler-product tail bounds and interval bounds.
6. Recheck the inaccessible Pan all-n Lean source cited by Jentges and compare
   public proof history before claiming priority. A404 is not proof of absence.

The first complete compressed-graph-to-CNF feasibility gate has passed for
n12/b0/l2. Independent source/data review found no substantive concern; shifted
counter-threshold and repeated-cycle-vertex negative controls were rejected.
Next investment is reusable encoding/block verification and the existing n36
certificate. Full analytic formalization remains substantial after this gate. No percentage completion or promised award is assigned.

Evidence, exact build hashes, scoped independent reviews and source search:
`verification/2026-10-20-bounty-only/` and
`reports/bounty-only-2026-10-20/883/`.
