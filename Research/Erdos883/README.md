# Erdős 883 / JSP-000734: bounded implementation candidate

**This is an incomplete research development, not an award submission.**
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
- `FiniteWitness.lean` proves a direct cycle-table-to-graph-containment theorem.
  It verifies all20 admissible sets for n=12, cardinality9 and even count6,
  then obtains a five-cycle. This is an end-to-end finite integration test,
  not an all-n proof and not a proof of the compressed SAT encoding.
- `ThirdParty/PartII.lean` is the attributed complete fixed-l second-question
  proof from `baobingzhang/jsp-000734-erdos883-lean` at
  `f87d2d526a9f736818133baed805fff4a1e94d10`. Minimal Mathlib API compatibility
  edits preserve all86 declaration signatures and every definition body.
  The Apache-2.0 license is retained. This result is prior third-party work.
- `Check.lean` jointly imports these modules, checks that the graph definitions
  are definitionally equal, restates the compression conclusion in the prior
  graph, and converts the n12 result to an actual IsCycle walk of length5.

All six targets printed by `Check.lean` have exactly
`propext`, `Classical.choice`, `Quot.sound`. The joint check exited0 on
Lean4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
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
lake env lean -o Research/Erdos883/FiniteWitness.olean Research/Erdos883/FiniteWitness.lean
lake env lean -o Research/Erdos883/Check.olean Research/Erdos883/Check.lean
```

An additional bundled `leanchecker -v Research.Erdos883.Check` run was terminated
after120seconds. It is **not recorded as passed**, nor is the timeout a proof
failure. This checker uses Lean's kernel, not a second kernel implementation.

## Outstanding gate before committing to the full candidate

1. Preserve the missing-odd-multiples-of-three constraint where used, and prove
   simultaneous prime-swap lexicographic canonicalization.
2. Construct sequential-counter/lex auxiliary assignments and prove arbitrary
   cycle-free sets map to the exact CNFs. Prefix-cycle blocking clauses must
   also be justified by actual graph witnesses.
3. Reconstruct and kernel-check all99 LRAT obligations and670,834 recorded cycle
   witnesses. Two unmodified proof files (n12,b0,l2 and n36,b3,l6) have already
   replayed through Mathlib's `lrat_proof`; deleting the final step in the first
   was rejected. This validates those CNFs only, not their intended graph use.
4. Complete every finite arithmetic family, the exceptional cases and167 block
   certificates through10^8. Stored success flags are not proof inputs.
5. Prove uniform infinite-range estimates, including primorial continuation,
   finite prime-class counts, Euler-product tail bounds and interval bounds.
6. Recheck the inaccessible Pan all-n Lean source cited by Jentges and compare
   public proof history before claiming priority. A404 is not proof of absence.

Next investment is limited to one complete compressed-graph-to-CNF instance.
It must pass without extra mathematical assumptions before expanding to all
finite certificates. Full analytic formalization remains substantial even if
that succeeds. No percentage completion or promised award is assigned.

Evidence, exact build hashes, scoped independent reviews and source search:
`verification/2026-10-20-bounty-only/` and
`reports/bounty-only-2026-10-20/883/`.
