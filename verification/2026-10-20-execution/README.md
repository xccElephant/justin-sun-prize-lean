# Bounded source checks and a mathematical capacity attempt

Work crossed midnight from 2026-10-19 into **2026-10-20 Asia/Shanghai**.
Official main remained `fd8fa66abb4e21df828fdebc25298e9ad75521bd`.

**No new full JSP proof, new award PR, or verified prize vacancy was obtained.**
The 32 existing PRs were reread: five Ready (5076,5079,5080,5089,5095) and
27 Draft. These status labels do not establish prize acceptance or priority.

## Candidate decisions

Sixteen previously unreviewed entries now have bounded source/scope records.
The strongest four paper-backed checks are JSP641,644,679,1018; the remaining
twelve are narrower statement/endpoint/assembly checks. None was independently
rebuilt this round, and none is certified globally first or formally accepted.
Their exact pins and evidence depths are in `CANDIDATES.json`.

- JSP448/E557: the missing catalogue source already exists in PR574's original
  `zhangjun725/erdos557` repository. Read the entire pinned Basic.lean reduction
  and the all-k,n tree endpoint. No newly missing reduction.
- JSP641/E781 and JSP1018/E1213: the combinatorics sidecar obtained a primary
  waves paper and a complete author-published consecutive-block proof, compared
  precise definitions and stronger competing endpoints. Both already covered.
- JSP644/E784 and JSP679/E823: the number-theory sidecar read primary papers
  and checked full threshold / arbitrary equal-sigma-ratio endpoint types.
  Both already covered. Real-prefix and reciprocal wrappers are not new scope.
- JSP211/E240,281/E339,603/E735,782/E941,854/E1027,857/E1031,1010/E1205,
  1019/E1214: actual full-scope source entries were found after checking meanings
  rather than trusting filenames or old ID offsets. Large dependencies remain
  unverified in this bounded pass.
- JSP320/E387: the commonly referenced plby endpoint **really is conditional**.
  However PR296's separate original repository supplies the full unconditional
  negative answer. Read Canonical, Main, MainAssembly, ConvenientError and
  SeparatedError at the fixed pin. The last two named limits are supplied by
  proved declarations, not final hypotheses. Their entire analytic closure was
  not rebuilt; this is a concrete existing-source lead, not a kernel certificate.
- JSP900/E1083: read PR4994 and its actual main theorem giving both asymptotic
  bounds in every d≥3. The underlying mathematical claim remains review pending.
- JSP936/E1129: plby's small-node theorem is insufficient on its own, but
  PR121's separate source proves the full free-node minimizer equivalence.
  Read its pinned Main.lean; did not independently verify every imported core.

This changes the 295-row pool ledger from 37 to **53** varied-depth records,
leaving **242** without substantive review. It does not turn 16 title hits into
16 certified valid proofs. The 2026-10-19 census stays a historical snapshot.

Additional Open-row leads were checked without adding them to this solved pool:
JSP137/E131 has a prior exact-growth integration; JSP940/E1133 has a prior
full robust-interpolation source (actual final types read). JSP826 has two
all-forest submissions, inspected only at PR-body level; do not call that a
completed mathematical verification. JSP630/E769 and JSP638/E778 still have
open general questions in the fetched original pages; no complete route found.

## Actual mathematical work: Sendov's capacity gap

Continued the existing JSP404/E504 gap rather than restarting its source audit.
Sendov's unsupported general weight maximum remains the obstacle. For centers
with angle cap π(1−1/t), the proposed bound is Σ2^k_i≤2^floor(t) in the first
half interval, and ≤2^floor(t)+2^(floor(t)−2) in the second.

1. A seeded random exploration tested **192,000** configurations of 3–10 centers
   at eight parameter values. There were 145,520 feasible configuration/parameter
   pairs; no violation of the final bound was found. This is floating-point
   exploration, neither proof nor evidence of an exhaustive search.
2. A targeted four-center exploration tested **1,680,000** configurations for
   t near the half/integer endpoints through t=15.999. No feasible violation
   occurred. Empty feasible batches record no best witness.
3. An independent mathematical sidecar disproved a proposed **abstract** shortcut:
   edge-color K5 by i+j modulo5. Every pair of color classes has bipartite union,
   yet five vertices exceed 2². Thus adjacent-sector union bipartiteness alone
   cannot prove the desired bound. The regular pentagon at t=5/2 is the boundary
   geometry; this does **not** disprove Sendov's final bound.

The strict angular slack and geometric realization constraints are essential.
No complete replacement for Lemma4.1 was obtained. Do not turn either a failed
proof route or an intermediate inequality counterexample into an award claim.
The attempt and executable probe are retained in `blumenthal-capacity/` here;
the detailed raw results are under reports/opportunity-2026-10-20-execution/.

## Prize-route sidecar

The official 49-problem MathDB pilot explicitly permits Exposition even for an
open conjecture, without requiring Lean. However its rollout still says
`prepared`, with no activation timestamp/evidence. Selection of the first
satisfactory exposition is a committee decision; empty candidate cells do not
mean an available slot. No concrete reward amount or currently executable
exposition award path was established. This is a watch item, not grounds to
divert the main effort or make a claim. Exact primary-source report is copied
to `PILOT_ROUTE.md`.

## Reproducibility and follow-up

Nine newly verified mappings and ten stale mappings from the already-audited
repair queue pass a watched-red-to-green regression suite; see `MAPPINGS.md`.
Proof modules and all award PR states were untouched.
Raw third-party files are read-only evidence, not claimed contribution code.
Further implementation requires an actual complete route; this round did not
establish one. Avoid repeating these same endpoint searches or spending time
on wrappers that earlier full results already imply.
