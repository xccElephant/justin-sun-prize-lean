# Opportunity screening, round 2 — 19 October 2026

This continuation found **no new complete-proof candidate approved for prize-oriented
implementation**. The existing 32 PRs were read back unchanged: four ready and
28 drafts, with identical heads. No new award PR, comment, or mathematical project
source change was made.

The round adds **17 new documented pool-record checks**: ten include definitions,
core proof steps or concrete fixed-version evidence; seven are explicitly limited
to the actual endpoint and surrounding code. Together with round 1, 31 pool
records have documented checks. They are not 31 complete independent proof audits.

## Candidate-pool correction

The original filter required the entire Lean-proof field to equal `No`. It missed
three records whose field starts `No —` and explicitly says the linked proof is
incomplete. At unchanged official main
`fd8fa66abb4e21df828fdebc25298e9ad75521bd`, the corrected Solved/Lean-No pool is
**294, not 291**. There are still 395 records with a Solved status prefix in the
1,072-entry catalogue.

The additions are JSP001059 (full Hilbert16 uniform bounds), JSP001068 (combined
ionization conjectures), and JSP001071 (Grothendieck homotopy hypothesis). Their
published scope notes were read; the full mathematics and proof dependencies
were not audited. They remain unapproved. These are major missing theories,
not identified small Lean repairs. [Exact added fields](POOL_CORRECTION.json).

The cumulative [candidate ledger](../2026-10-19-discovery/CANDIDATE_LEDGER.json)
contains all 294 entries: **31 with documented checks and 263 without substantive
review**, including the three newly added scope-flag-only entries. The earlier
all-title-hit observation applies to the original 291 entries, not automatically
to the corrected pool. The reused 4,509-PR title index matches 293 of the 294;
JSP001059 has no title match in that snapshot. Neither a match nor no match
establishes proof availability or priority.

## Findings that changed the decision

**JSP000513 / Erdős632.** The DHS counterexample is suitable for a finite, complete
negative answer, but its exact proof already exists. The arbitrary-palette
definition, universal positive-list construction, negative gadget, and final
root-clique uniformization were read against the primary paper. The coordinator
then independently compiled all **six unchanged fixed-source modules**, with
Lean4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; all exited0.
The root `Erdos632.not_erdos_632` printed only `propext`, `Classical.choice`,
`Quot.sound`. The source header names4.33.0; no source adaptation was made.
[Build record](E632-build-results.json), [axiom output](E632-axioms.log). A separate root-module kernel replay exceeded its120-second cap; [result](E632-replay-result.json). It is **not** recorded as a successful replay, and the timeout is not a mathematical counterexample.

**JSP000622 / Erdős758.** A different fixed source supplies the table for every
1≤n≤19, with `zmax` over all simple graphs and both universal upper bounds and
existential lower witnesses. The all-extension-mask coverage induction, the
twelve-vertex pattern premise, the graph-to-clause consumer and one concrete
certificate chain were read. The source was not independently compiled and not
every LRAT certificate was replayed. This is credible same-scope evidence,
not an award judgment.

**JSP000511/512, ordinary planarity.** The older plby definitions demand extra
face/Euler data or a recursive triangulation certificate. Those definitions alone
do not establish completeness for arbitrary ordinary drawings. Later fixed sources
in PR4712 and PR922 use ordinary continuous crossing-free drawings, supply
topological-to-combinatorial bridges, and have actual arbitrary-palette coloring
endpoints; the latter also supplies sharpness. The final statements and definitions
were read, but the complete topological proof closures were not rebuilt. The
initially identified older-source gap is therefore not an established vacant
implementation opportunity.

**JSP000257 / Erdős306, outside the original Solved pool.** The September26 paper
really has one remaining Ramanujan inequality in its ancillary Lean source.
Tang's earlier development really contains two named analytic axioms. However,
PR1469 points to a separate completion replacing them by eventual PNT and Mertens
estimates. Its fixed actual all-rational endpoint and analytic bridge were read.
The downloaded source/configuration hashes agree with the package's successful
build and standard-axiom receipts. The file's historical `UNCOMPILED DRAFT`
comment is explicitly superseded by those receipts; it is not evidence of a
current failure. These are author-provided execution records verified against
the selected bytes, not a full independent rebuild. No duplicate completion was
started.

**JSP000248/250/259/360.** The unit-fraction and bounded-lcm entries have genuine
fixed-source density, two-sided estimate, eventual interval-shape, or sharp
asymptotic endpoints. Several small-instance submissions and misleading scopes
exist too. Those weak submissions cannot be used to ignore stronger existing
sources. E292's density theorem does not claim a pointwise classification;
E308's result is eventual. Their exact limits remain in the review records.

**JSP000400/527.** The plby E496 positive-alpha statement and E651 subexponential
statement leave core mathematical inputs unproved at their old public entrypoints.
Other fixed packages supply actual short-vector/small-value or geometric-extraction
inputs and full point-set endpoints. Their actual statements and assemblies were
read. Large imported closures were not independently audited, so their validity
and priority are not certified by this report.

[Ten core/source reviews](CORE_REVIEWS.json) and
[seven limited endpoint checks](ENDPOINT_SPOT_CHECKS.json) preserve evidence depth,
exact sources and remaining uncertainty. The seven spot checks must not be treated
as fully verified competitive exclusions.

## New-paper route

Recent papers were checked against the catalogue rather than assuming that any
new Erdős theorem belongs to the prize bank.

- **Bipartite-link hypergraph counterexample:** a nine-vertex template, weighted
  497-vertex construction, and balanced blow-ups yield a concrete finite route.
  Template bipartitions and numerical counts were independently checked in Python.
  No exact JSP or numbered Erdős mapping was established in this bounded pass.
  Lean vacancy is also unknown. It remains unadmitted, not a new prize submission.
- **E786 and E522:** the new papers explicitly provide author Lean developments.
  The paper statements and linked author documentation were read; full source
  correctness and priority were not independently certified. Their older Open
  metadata is not evidence of a vacant formalization.
- **E506 and E1117:** new papers distinguish old partial results from broader
  conclusions and point to existing author formalizations. A short proof of only
  selected cases is not substituted for the entire catalogue question.
- **E374:** the new factorial-product paper relies on substantial sieve,
  exponential-sum and prime-distribution results. It is not a bounded elementary
  implementation opportunity established here; the paper also distinguishes
  growth order from still-open density limits.
- **Prescribed-density minimal bases:** the September8 parameter theorem is
  different from the robust-deletion question E330. No automatic JSP mapping or
  new prize opportunity is inferred.

[Recent-paper dispositions](RECENT_PAPER_LEADS.json). Search output, source text,
fixed proof snippets and the finite hypergraph certificate remain local under
`reports/discovery-2026-10-19-round2/`. Third-party proof code and papers are not
published here as the applicant's work.

## Reproducibility and limits

This report uses three bounded review agents plus coordinator source reading,
read-only live GitHub/arXiv/original-source retrieval, and one independent
six-module Lean build. Failed API requests were not interpreted as absent proofs.
The existing PR heads and draft states were compared with the saved campaign
ledger. [Result](RESULT.json), [source manifest](EVIDENCE_MANIFEST.json).

No claimed prize amount, priority win, official mathematical acceptance or new
complete submission resulted. The objective continues. The next pass should
start with the 263 entries without substantive review and the clearly labelled
unresolved-source leads, reusing this evidence rather than revisiting the same
false gaps. Implementation still requires complete original scope, an understood
proof, feasible missing work, contribution/priority evidence and a valid award path.
