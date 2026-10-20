# Final bounded pass: two number-theory candidates

Date: October20,2026. Selected previously unreviewed entries JSP87 and JSP388.
Neither is admitted to new implementation: actual fixed sources already contain
matching unconditional final theorem bodies. This is a source/scope check, not
a new compiler run, independent full axiom audit, or award determination.

## JSP87 / Erdős69

The original webpage asks whether sum(n>=2) omega(n)/2^n is irrational, where
omega counts distinct prime factors. It records the unconditional Tao–Teräväinen
result; the earlier prime-tuples hypothesis is not the only known mathematics.
The original page, authenticated PR3850, fixed raw root and local source were read.

`plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e`,
`src/latest/ErdosProblems/Erdos69.lean`, `Erdos69.erdos_69`, states exactly the
irrationality of the shifted n+2 series. It is not merely Tao's identity relating
the two sums. Its proof obtains an integer multiple from rationality, proves
the same characteristic function norm tends to zero while its distance from
one tends to zero, and contradicts the triangle inequality.

Read `CorrectionErrorBounds.lean` and `TruncationErrorBounds.lean`: the two
limit inputs have actual proved bodies, using composite-dilation correction
and tail estimates, not prime-tuples as a final assumption. `ElementaryArithmetic`
contains the actual omega-based series and a summability proof; `BinarySeries`
proves the exact shift from n=0 to n=2. Selected files match fixed git blobs and
live root bytes; see coordinator-source-check.json. The deeper characteristic
function, CRT and prime-estimate proof cone was not fully audited or built.
No concrete missing final theorem was found. PR3850 remains open/unmerged;
registration status itself is not the basis for exclusion.

## JSP388 / Erdős477

The original existence question is one integer polynomial of degree>=2 and a
complement that represents every integer uniquely as a pair of summand values.
The question does not require classification of all polynomials. Original
webpage and FormalConjectures477 were read; the former includes Bloom's September5
proof exposition of the finite-avoidance/greedy construction and the determinant
bounds for even powers>=6. In particular, a complete sixth-power witness suffices.

At the same plby pin, `Erdos477.erdos_477 : OriginalStatement` constructs X^6.
`OriginalStatement` uses the real polynomial degree and `IsTiling` expands to
unique pairs in A x range(f.eval), not uniqueness of polynomial inputs. The
integer-power/nonnegative-power range bridge is supplied, so even-power
noninjectivity is not a loophole.

Read `SixthPowerTiling.lean`: finite avoidance is proved by a union bound from
sublinear bad-shift counts, then passed to the greedy tiling theorem.
`Counting/BadShiftCount.lean` proves the actual O(N^(249/250)) bound from a
selected integer-surface count and height control; `SelectedSurfaceBound.lean`
assembles that surface count, including the zero-middle-coordinate case.
These are actual proof bodies rather than hypotheses in the final theorem.
The larger determinant/curve development was not independently rebuilt or fully
audited. No demonstrated missing original-scope endpoint was found.

Authenticated PR343 is an additional attributed complete compatibility-port
submission at ketianzhang1-lang/jsp-000301-lean@a9eae7a01edade3d5d9a386144dcd2848b4de917.
It explicitly credits the plby affirmative result and separates its quadratic
obstruction and translation work. Its build claims were not rerun. Exclusion
rests on source scope, not these claims or the existence of a PR.

## Freshness and limits

Official awards main rechecked as96e23a628707cf10d23e38d882fec1340f5e8ef4;
latest PR still5121. The new items since5117 are MathDB process changes, already
seen in the prior round. No new mathematical lead appeared in that bounded
latest-ten check. This does not exhaust the whole problem bank or prove that
all worthwhile opportunities have disappeared.

Python urllib initially received403 for the original pages; curl retrieved
HTTP200 and the full question/exposition text, saved alongside this report.
Both fixed Lean roots matched local blobs. No source edits, proof builds,
award PR mutations, third-party messages or new submissions occurred.
