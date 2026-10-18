# Verification snapshot — 19 October 2026

This local audit verifies the proof sources at commit `fa0f84367bd744d6f135472327dfddc2158c4535`; it is not an award decision. The 32 submitted PRs refer to 27 distinct source files, whose Git blobs and three project configuration files were identical to this snapshot. The source files have not been changed by the reproduction fixes.

All 34 Lean modules (33 problem modules and Basic) were freshly elaborated with Lean 4.33.1. The 198 in-source axiom reports were complete. An auditor-generated script additionally enumerated 2,514 theorem declarations, including generated auxiliary theorems, and observed only `propext`, `Classical.choice`, and `Quot.sound`. All 34 modules passed the bundled `leanchecker` replay from their imported environments. Imports used pinned dependency caches; an independent external kernel checker and a from-source rebuild of all dependencies were not performed.

The original default Lake library build failed because `JspBounties.*` includes an absent `JspBounties.lean`. The local repair uses `JspBounties.+`, selecting the 34 actual modules; the repaired project build completed successfully (2609 jobs). `check_lean.sh` was changed to run `lake env lean` relative to its own directory, and was tested from a relocated checkout. These are project-reproduction fixes, not changes to the mathematical sources. Do not report the repaired build as a successful build of the old commit.

The Lean toolchain commit is `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. All nine dependency Git revisions matched the lockfile. Proof execution used a macOS sandbox with network access disabled and filesystem writes restricted to the audit directory.

## Scope findings

Successful checking establishes the stated theorems, not correspondence to a whole prize problem. Of the 32 submissions, the review found two complete scoped original problems (#348 and the yes/no part of #365), 27 records with broader-scope gaps, and three submissions whose catalog scope needs clarification (#372, #124 and the triples variant of #939). Ten old catalog changes referenced 23 nonexistent theorem names. Those defective references and other inaccurate declarations are being corrected; old failure results are retained as historical findings.

The independent Bridge348 and Bridge365 definitions were checked against the intended indexed-deletion and positive-powerful-number questions. These bridges import the submission and use Lean's own kernel; they are not an independent external checker.

## Reproduction

```sh
lake exe cache get
lake build
./check_lean.sh JspBounties/Erdos348.lean
./check_lean.sh JspBounties/Erdos365.lean
lake env leanchecker JspBounties.Erdos348 JspBounties.Erdos365
lake env lean verification/2026-10-19/Bridge348.lean
lake env lean verification/2026-10-19/Bridge365.lean
```

The repaired project commit is `70ca9dbd7ee3832a6bd87d24b3fa94c7cf881aa6`; this report is committed after that selected proof-project version. Historical proof completion dates, attribution, scope and priority require independent public evidence. No uniqueness or prize eligibility is asserted by this report.

Scope recheck: [finite existence versus infinitude](SCOPE_RECHECK.md). The earlier 28/2 split was too categorical for JSP-000307; its literal existence question is already proved.
