# Further bounded candidate review

Date: **2026-10-20, Asia/Shanghai**. Official main was checked at the beginning
and end and remained `fd8fa66abb4e21df828fdebc25298e9ad75521bd`.
No new complete JSP proof, new award PR, or admitted implementation target.
Existing submissions were reread: **5 Ready and 27 Draft**, with no mutations.

Twelve previously unreviewed solved/no-recorded-Lean pool entries now have
specific scope/source records, bringing the 295-row ledger to **65 records of
varying depth and 230 without substantive review**. Four are independent
sidecar paper/source checks; eight are narrower coordinator statement/assembly
checks. None underwent an independent Lean build in this round. Source
availability is not being represented as independent proof certification.

## Four delegated candidates

- **JSP428/E534:** exact maximum for a pairwise noncoprime subset of [1,N]
  containing N. The actual endpoint optimizes over the prime-prefix candidates,
  beyond the earlier disproved two-candidate guess. Primary Ahlswede–Khachatrian
  paper and fixed source assembly read. No missing bounded step established.
- **JSP475/E586:** Schinzel covering question. The fixed source proves a
  dividing pair in every finite nontrivial covering system. Its seed, guarded
  sieve recurrence, finite certificate and tail are supplied by named proved
  declarations. Full 2018 author preprint obtained; not mislabeled the final
  2022 publisher version. No missing bounded step established.
- **JSP464/E574:** an existing k=3 construction completely refutes the original
  universal asymptotic conjecture. A September 30 comment by **GordonLtron**, with
  GitHub **COLLABORATOR** association, accompanies PR504's closure and objects
  that the broader catalogue wording demands the extremal number itself. This
  is a recorded adverse scope decision for that submission, not a refutation of
  the mathematical disproof or evidence of a final committee ruling on every
  possible future submission. No complete route to the broader demand found.
- **JSP628/E767:** the exact eventual extremal formula for every k>0 and every
  n≥3k+3 already has a fixed source. Actual cycle/chord predicates, finite
  extremum, lower construction and crucial upper-bound assembly were checked.

Reports copied here as `JSP428.md`, `JSP475.md`, and `GRAPHS.md`; their relative
raw-evidence links resolve in their original directories under
`reports/other-candidates-2026-10-20/` (428,475,graphs respectively).

## Eight coordinator checks

Common plby source pin: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.

- **JSP243/E286:** a short-interval unit-fraction result must not be reduced to
  the fixed [2,6] example. plby's term-count interval statement is also weaker
  than the original ratio question. PR4711 supplies
  `H0W4RD-dev/croot-unit-fractions@a8b4cac51866d7d9cf78b0ef70266feee06b3237`.
  Its actual `Croot/Main.lean` was read: the upper interval construction, lower
  logarithmic bound, shortest-end limit, bounded-ratio infinitude and cofinite
  liminf equal to e all occur as unconditional endpoints. The proof-critical
  Proposition1/2 closure was not independently audited or built.
- **JSP315/E381:** plby's Nicolas upper bound answers the original universal
  yes/no question, but the broader growth request also motivates a lower bound.
  PR914's `CollinYuanjieRen/awards@58d540b9a1de809493cf54ca149de6e59ae9d81b`,
  `submissions/jsp-000315-cyr/Erdos381Lower.lean`, supplies the two-sided
  formulation. The actual root and its proved gap input were identified;
  this pass did not independently audit its entire lower-bound dependency chain.
- **JSP364/E449:** actual strict divisor pairs d1<d2<2d1 are counted, and the
  source constructs a positive-density progression on which r(n)>K tau(n), for
  any K. Read the definitions, amplifier/CRT progression and final density
  contradiction. This is the correct E449 question, not the different E448
  dyadic-bin statistic previously suggested by the stale mapping.
- **JSP397/E491:** the original function is additive on coprime inputs, not
  necessarily completely additive. `logarithmic_uniform_bound` and the final
  `erdos_491` retain this scope; homogenization and completely-additive rigidity
  are proved inputs, not final assumptions. Those assembly declarations were
  read, without a full transitive proof audit.
- **JSP503/E622:** the source counts actual vertex subsets whose induced graph
  has an ordinary Hamiltonian cycle, allowing chords. It supplies all three
  regular-Dirac-graph cases and the uniform (1/2−epsilon)2^(2n) bound. Definitions
  and assembly match the fetched original question; the old E621 map was wrong.
- **JSP601/E733:** the actual counting object is a sorted list/multiset of
  line cardinalities, retaining repetitions but requiring distinct geometric
  lines. The finiteness and exp(C sqrt(n)) upper bound have a source endpoint.
  The original webpage additionally asks about existence/value of a normalized
  counting limit in commentary. This pass does not certify that additional
  limit or infer that it is an accepted independent prize scope. The recorded
  upper-bound question already has a proof source.
- **JSP753/E908:** both the webpage's erroneous continuous-summand wording and
  the historical measurable-summand wording are addressed in source. The former
  has a Heaviside counterexample; the latter an unconditional decomposition
  into an AE-measurable function, an additive function and a function whose
  translate increments vanish a.e., with exceptional sets allowed to depend on
  the increment. Actual definitions and assembly read; no full analytic audit.
- **JSP204/E227:** source correctly gives an entire nonpolynomial power series
  with the ordinary maximum-term/maximum-modulus ratio tending to 1/2. This
  answers the original yes/no question. It does **not** establish a classification
  of all possible limits. PR846 explicitly discloses that narrower scope and
  makes no first-formalization claim. The catalogue's phrase “determine the
  limiting ratio” may motivate a broader reading, but that scope is not approved
  and no complete route was obtained. This remains a **scope/research lead**,
  not an admitted vacancy.

## The E227 lead and retrieval limit

The original problem page reports that Clunie and Hayman realized every value
in [0,1/2]. That statement alone does not establish that no other limit is
possible, and this review does not claim it. The existing fixed source constructs
the endpoint 1/2 only; the inspected PRs 846 and 4995 concern that same negative
answer, while 4834 links a different candidate source without a complete scope
analysis here.

Crossref confirms the 1964 paper **The maximum term of a power series 1**,
DOI `10.1007/BF02807433`, and the distinct 1965 part2, DOI `10.1007/BF02806378`.
The publisher PDF and fulltext routes returned the HTML article landing page,
not the 44-page paper. The saved files are labeled `.html`; no full paper read
is claimed. The missing full mathematical argument and unconfirmed independent
scope prevent implementation admission. A possible extension of an existing
disproof is not automatically a missing original-problem obligation.

## Corrections and verification

Four more stale discovery mappings were fixed using fetched original statements
and catalogue bibliographies: **204→227,364→449,503→622,753→908**. Four regression
subtests failed first; the whole six-test suite passed after correction
(10.204 seconds). This is a selector correction, not new mathematics.

The broad read of additional top-level files was not counted as full candidate
review. No competitor code was copied into our proof modules, no blanket build
of competitors was run, and no existing award PR was edited. Both bounded
agents completed and were closed. Remaining work is to find a complete original
scope with an understood proof and a genuine missing formalization; this round
did not establish one.

Raw sources, live PR evidence and source hashes are retained under
`reports/other-candidates-2026-10-20/`. `CANDIDATES.json` gives exact pins and
evidence limits for each new ledger record. The 65/230 counts track documented
assessment, not valid proofs, solved problems, priority or expected awards.
