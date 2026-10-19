# Parallel repair campaign: results and remaining work

Date: 2026-10-19, Asia/Shanghai. This campaign covered the 32 existing submissions. No new prize problem was opened. The user's full objective—every existing problem reaching a complete, potentially qualifying submission—**has not been achieved**.

## Delivered and published

- **New complete literal-catalogue result:** E885/JSP-000736, two positive integers with arbitrarily many common positive factor differences. The mathematical argument, exact Lean endpoints, positive-factor definition bridge, and bundled kernel replay are public at proof commit `1e438109a14119d26f891252a9dcc865a8a42ef4`. PR5095 was updated and marked ready for explicit scope review. The stronger original k-integer conjecture remains unproved.
- **Additional checked repairs:** E338 exact least ordinary order, E413 endpoint-correct conditional deduction, E602 scope and invalid-route certificates, E596/E668 counting/extremal reductions, E44 scope wording and E699 JSP mapping. Source/evidence commit: `36c356983c53bfd9ceec618f58107942b9afbcb1`. The seven affected draft PRs were updated in place and their heads, bodies and draft state read back successfully.
- **Verification:** integrated `lake build` passed 8,740 jobs with all 34 source hashes unchanged; nineteen relevant new target signatures and their axioms were checked, and the six additional changed modules passed kernel replay. E885's two new endpoints were independently checked before its publication. Only standard axioms were observed. This uses Lean's own kernel and pinned imported caches, not an independent kernel implementation or from-scratch Mathlib rebuild.
- **Current remote state:** 32 open PRs, 28 drafts, four ready. PR5076/5079 are complete scoped-proof reviews. PR5080/5095 are literal-scope review requests. No organizer award approval or payment has been established.

See [verification](README.md), [E885 proof](Erdos885-MATHEMATICAL-PROOF.md), [E885 publication](PR5095-published.json), [seven draft updates](partial-pr-updates.json), and [all 32 records](CAMPAIGN_LEDGER.json).

## Delegation accounting

Nineteen actual agent instances were dispatched: sixteen planned work/review groups, one replacement for a disconnected scope worker, one independent integration reviewer and one focused followup for three inadequately investigated problems. At most six ran simultaneously. All sixteen group reports are present. The disconnected worker did not produce a complete result; the replacement supplied the scope review. A completed report means the bounded assigned investigation finished, not that its original conjectures were solved.

The groups and final mathematical outcomes are below. Every unresolved record remains retained in the repair queue.

### 1. nt-cover-factorial

PRs: #5098, #5107.

E273 still needs a covering using primes at least 5; deleting the modulus-2 class leaves total reciprocal mass 7/9 and cannot be repaired by residue reassignment alone. E727 still needs the mixed-factorial infinitude construction and the squared-factorial conjecture. No full solution.

### 2. nt-dyadic

PRs: #5099.

Finite representation multiplicity is retained. A single rational with continuum many representations and finite decomposition for every positive parameter remain unproved. The direct infinite sparse-block route produces an irrational mass without a compensating construction.

### 3. nt-bases

PRs: #5088.

The positive-cutoff exact representation theorem, the {3,4,7} case and Melfi construction remain missing. Necessary gcd conditions and finite residue representatives do not establish eventual exact coverage.

### 4. nt-density-products

PRs: #5077, #5084, #5085.

The initial group supplied scope checks only; the separate followup completed actual mathematical attempts. E302 ordinary subadditivity and superadditivity both fail on explicit finite examples. E291 finite-prime simultaneous avoidance does not cover all primes up to its own returned witness. E367 gcd and CRT control do not yield exponent 2+epsilon; Pell pairs refute the proposed modulus-to-size shortcut. All three full statements remain open in this work.

### 5. nt-prime-gaps

PRs: #5092, #5094.

E287 lacks the unconditional all-length gap statement; E699 lacks the general sufficiently-large common prime bound. Counterexamples concern proposed intermediate lemmas, not the original questions. E699 header mapping corrected to JSP-000569.

### 6. nt-multiples

PRs: #5096.

The general finite-set multiples inequality is missing. An exact counterexample disproves a proposed stronger incremental insertion inequality; it still satisfies the original inequality, so it does not solve the problem negatively.

### 7. nt-factor-differences

PRs: #5095.

Complete arbitrary-k TWO-number result proved with rational doubling, 2-adic valuation descent and finite denominator clearing. Independent review passed. Submitted for literal scope review; arbitrary k-NUMBER conjecture not proved.

### 8. nt-additive-bases

PRs: #5093.

Bateman’s example now has least ordinary order exactly h for each h>=3 and no restricted order. This closes the exact-order gap in the example, not the general classification, bounds, equality or finite-deletion questions. E339 remains separate.

### 9. graph-core

PRs: #5091, #5082, #5081.

E23 general bipartite deletion bound, E617 general r-colour case and E628 arbitrary Tihany partitions remain missing. Existing special cases and route analyses do not remove the required general parameters.

### 10. graph-johnson

PRs: #5078.

The remaining prime-(k+1) Johnson colouring cases are unproved. Divisibility and spectral equality conditions supply no contradiction in those cases. A misidentified arXiv reference in research notes was identified; active source has no such false identifier.

### 11. geometry-extremal

PRs: #5083, #5087, #5102.

E503 general and low-dimensional matching upper bounds, E670 fixed-dimension asymptotic constant, and E657 fixed-plane superlinear distance growth remain unproved. Varying dimension does not answer fixed-dimension limits.

### 12. graph-geometry-ramsey

PRs: #5100, #5101.

Six new general counting/reduction lemmas compile and replay. E596 still lacks the actual C4/C6 finite Ramsey input and full classification. E668 still lacks eventual growth of the number of global maximizers up to planar isometry.

### 13. nt-analytic

PRs: #5103, #5104, #5106.

E238 arbitrary c2>=2 prime runs remain missing. E413 now maps Lau v3’s endpoint range correctly, but its analytic sieve/moment core remains a hypothesis. E711 parts.ii stays fully proved; the uniform n^(1+o(1)) upper bound is missing.

### 14. nt-sidon

PRs: #5105.

The near-optimal extension of an arbitrary prescribed finite Sidon set remains missing. Mixed A+S=S+S collisions invalidate a simple bounded-deletion argument. Neither an empty-start construction nor assumed Singer/prime-density inputs meet the original requirement.

### 15. set-theory-property-b

PRs: #5086.

Original arbitrary ground/index scope confirmed. Countable members do not imply countable union. Ten checked reduction/obstruction certificates clarify invalid routes, but no complete Property B proof or valid original counterexample was found.

### 16. scope-eligibility

PRs: #5076, #5079, #5080, #5088, #5089, #5090, #5097.

E348/E365 complete stated scopes retained, with earlier competition disclosed. E372 finite existence complete but infinitude unresolved. E124 cutoff scope and E939 triples/catalogue scope remain unresolved. All r>=6 powerful-sum families and the four-term square-product exclusion are retained as completed subproblems, not whole catalogue solutions. Independent E885 proof review was additionally completed.

## Findings that were corrected during review

The E338 HHP03 bibliographic suspicion was checked against the authors' institutional research portal and withdrawn: the header metadata matches DOI 10.1515/crll.2003.055. It was not used in the new Bateman proof. The E44 all-sufficiently-large-M statement was an additional stronger probe, not an extra user requirement; even the actual original exists-M target remains missing. Historical findings and failed proof logs are not acceptance evidence.

One preexisting composition limitation remains: E365 and E939 each define `Nat.Full`, so a single file importing both conflicts. The project builds independent problem modules and the submissions use their individual imports. This campaign does not claim a successful aggregate import of all modules.

## Remaining objective and next work

The current deliverable is a complete literal-scope submission plus verified partial repairs, accurate public PRs and a 32-record obligation ledger. It is not all problems solved, all drafts repaired, or confirmed prize eligibility.

Continue within the existing queue. Prioritize complete published mathematical arguments whose missing formal steps can be bounded, while keeping exact original acceptance statements fixed. Resolve the two submitted catalog-scope discrepancies through their existing review requests. For research gaps, record the precise missing lemma or valid counterexample requirement, and do not promote a weaker statement by renaming it. Earlier complete work, contribution attribution, qualifying dates and organizer decisions remain separate from Lean correctness. No reliable per-problem award amount or expected revenue is established here.

The full queue is retained at [REPAIR_QUEUE.md](../2026-10-19-repairs/REPAIR_QUEUE.md). Nothing has been marked abandoned or awarded.
