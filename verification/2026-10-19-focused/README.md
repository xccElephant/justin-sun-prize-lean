# Focused candidate checks and mapping repair — 19 October 2026

No new complete mathematical proof or award PR resulted. Existing PRs were read
back as four ready and 28 drafts, with unchanged heads. The work does not establish
an award, priority win, or independent acceptance of another author's proof.

Three candidates received concrete source checks: JSP000878/E1058,
JSP000884/E1064 and JSP000831/E998. All have existing sources with the relevant
full endpoints. The precise scope and verification limits are recorded in
[CANDIDATES.json](CANDIDATES.json). None was admitted for new implementation.
The cumulative ledger now has 34 records with documented checks of varying
depth and 260 without substantive review. These are not 34 independent proof audits.

The E1058 root classifies every positive solution as one of 1 through 5. Its
first-two-primes predicate, instantiated analytic estimate and certificate
assembly were read. E1064 supplies the actual density-one totient inequality,
as well as infinitely many reverse inequalities. Weak or incorrectly linked
PRs do not remove the separate complete source. E998's old endpoint counterexample
is narrower than Kesten's interval-length characterization, but PR101 points to
another source containing the characterization. Its definitions, final root and
both direction assemblies were read. No independent Lean build or kernel replay
was run for these candidates in this pass.

Other endpoint reads and recent-paper leads remain preliminary local research.
They were not promoted into additional completed candidate audits. In particular,
the bipartite-link hypergraph lead still has no established JSP mapping or award
path, so no implementation or new-problem submission was started. The user asked
what a proposed scope expansion meant; that was not approval to expand it.
The work remains focused on the official problem bank.

## A concrete tooling correction

The old discovery table contained four statement mismatches:

- JSP000307 points to E372, not E371: descending largest prime factors.
- JSP000377 points to E465, not E464: planar integer-distance avoidance.
- JSP000865 points to E1042, not E1043: logarithmic capacity and components.
- JSP000896 points to E1078, not E1077: multipartite transversal cliques.

[MAPPING_CORRECTIONS.json](MAPPING_CORRECTIONS.json) identifies the original
problem pages. The table's other rows remain unverified discovery hints; fixing
these four rows is not an audit of the whole mapping.

Three selectors now load the table next to the scripts, instead of a nonexistent
root-level file. They no longer infer missing mappings by adding a numerical
offset. Unknown mappings are skipped explicitly, and output labels describe
metadata leads rather than asserting proof vacancy or prize qualification.
The heuristic generator writes `reports/mapping-proposals.json`, which is separate
from the selector input and cannot silently overwrite these corrections.

The statement-based regression test first failed on all four wrong pairs.
An independent code review then found that module-style invocation failed with
the new import. Subprocess tests reproduced that failure for all three selectors;
relative/package imports fixed it. The final suite passed three tests, including
all three actual module invocations. The loader also works from a different
working directory. The final agent re-review disconnected; the coordinator
reviewed the import fix and the passing outputs directly.

```sh
python3 -B -m unittest discover -s scripts -p test_problem_mapping.py
```

No project Lean sources, toolchain, Mathlib pin or award PRs changed. Source
snapshots and fuller local notes remain under `reports/focused-2026-10-19/`;
third-party proof code and papers are not bundled here as our work.
[Result](RESULT.json) · [Local evidence hashes](SOURCES.json).
