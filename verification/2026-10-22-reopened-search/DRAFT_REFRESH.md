# Draft original-problem refresh — 22 October 2026

**Result: one concrete full mathematical route newly identified in our record: Erdős 488 / JSP-000395 / PR5096 has a full refutation of the original multiples inequality, with preexisting standalone Lean.** This corrects the old classification that the full mathematical question still lacks a route. It does not complete our existing PR5096 source, establish fresh priority, or supply a first-Lean prize opportunity. No other complete original route was identified in this bounded refresh.

Checked on 2026-10-22, approximately 15:40–15:50 Asia/Shanghai (07:40–07:50 UTC). This is a correction to our knowledge, not evidence of a result first published after the October 19 repair queue. The E488 public claim was submitted **2026-09-05 23:44:58** (website timestamp; timezone unspecified), and its proof note reports Jig server verification on **5 September 2026**. Independent source fetching and type/definition inspection were performed here; compilation and independent review of the informal mathematics are assigned to the parent and were not duplicated.

## E488 exact endpoint and original-scope match

Write `F_A(x) = #{j ∈ [1,x] : ∃ a ∈ A, a ∣ j}`. PR5096's source `JspBounties/Erdos488.lean` defines `multiplesIn A x` by this exact interval filter and `B_card A x` as its cardinality (lines 58–64). The original inequality is

`F_A(m)/m < 2 F_A(n)/n`, for `m > n ≥ max A`.

For positive endpoints this is equivalent to `n * F_A(m) < 2 * m * F_A(n)`. The external source proves the strict reverse, **`2 * m * F_A(n) < n * F_A(m)`**, with a nonempty finite set of positive generators and every generator ≤ n. The direction therefore matches and refutes the original question. Interchanging the endpoint letters must also interchange their denominators; no reversed density convention was used.

Two pinned files were fetched:

- Original standalone source: `raw-evidence/draft-leads/488-Counterexample.lean`, repository `WoshuaJolk/jig-verifier`, commit `ccf4a26cb8a8c49f476d44304070a2b677da4d7e`, path `Submissions/ErdosMultiplesSmoothRefuted/Counterexample.lean`. SHA-256 `37d2f3b46b3979d676ad50802fa9e2c08eaaf1cd859dee85271ad3e5ca639fe2`, exactly matching the proof note. `finite_counterexample` begins at line 451; terminal `proof` at line 484 is the literal negation of the universal cross-multiplied multiples inequality.
- Exact Formal Conjectures adapter: `raw-evidence/draft-leads/488-Erdos488-pinned.lean`, gist revision `9bbb516e782229c8ee2fe08dfe3bd53acac8b258`. It contains the full construction plus `Erdos488ExactAdapter.refutation : ¬ proposition` at line 522. Its proposition at lines 515–520 is `∀ A : Finset ℕ, A.Nonempty → 0 ∉ A → 1 ∉ A → letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}; ∀ᵉ n (m > n), A.max ≤ n → card(B∩[1,m])/(m:ℚ) < 2*card(B∩[1,n])/n`. It proves the exclusion of 1, handles `Finset.max`, identifies the interval-filter cardinalities and clears the positive rational denominators. There is no extra primitivity, bounded-cardinality, excess, or analytic assumption. The source is not named `fixedCounterexample.lean`; these are the actual published filenames and endpoints discovered from the gist.

The construction takes primes below 257, their odd-prime product Q, T=256^k for a proved k<4096, A equal to the smooth integers in (T,256T], n=256T, and m=2TQ. Finite growth/counting and the checked comparison `3Q < 16φ(Q)` yield the strict reverse inequality. The exact witness k is established to exist in a finite range rather than enumerated. The parent owns independent assessment of this argument.

This is **the original multiples predicate `∃ a ∈ A, a ∣ j`**, not the earlier nonmultiples misprint `∀ a ∈ A, a ∤ j`. Our PR5096's `erdos_488_nonmultiples_false` is a different theorem. Its singleton, pair, contains-2 and conditional insertion theorems remain restricted affirmative results; discovering the external refutation does not retroactively change those proofs. The source header's historical `JSP-000396` label is inconsistent with the corrected PR body; the authoritative record here is JSP-000395 / E488.

**Priority implication:** the same original scope already has a public Lean source by Declan Gessel, prepared with GPT-6 Astra, and a September 5 verification claim. This is not fresh first-proof or first-Lean work for us. Organizer award eligibility is not independently adjudicated here. Neither the source's comments nor the reported standard-axiom audit substitute for the parent's independent compilation. No `sorry`, `admit`, `native_decide`, or project axiom declaration was found by token inspection; this worker did not run Lean.

## E727 and other leads

E727's live page still says “open even for k=2”, but Johan Land's public repository README, retrieved 2026-10-22, claims complete no-sorry endpoints for **k=3 and k=2**, linked to a paper dated **6 September 2026**; the website claim was submitted **2026-09-07 02:22:40**. Thus the website can lag source claims. This worker did not inspect the dependency proof chain or independently verify these endpoints. The README expressly says it does not address general k; consequently it is not a complete original route for PR5107.

Other checked claim summaries remain narrower than their originals: E302 has improved upper/lower density bounds (September 13); E617 claims fixed r=5,6,7,8,9 cases (July 18–31), explicitly leaving universal r open; E602's October 1 claim studies finite hypergraphs and explicitly does not resolve the arbitrary-index infinite problem; E273's July 27 claim is only a lower bound on possible covering period; E338's October 1 claim assumes positive lower density; E699's accepted July 18 claim covers only j≤3i/2 or n=2j, while the July 25 claim leaves i=3 and unspecified finite exceptions. These were triaged from public claim pages, not independently proved or compiled.

## All 27 original pages and database comparison

All 27 requested original pages returned HTTP 200; their complete HTML and extracted text are retained in `raw-evidence/draft-pages/`, with timestamps and SHA-256 in `manifest.json`. The live database `data/problems.yaml` was retrieved and every requested entry compared with the October 19 snapshot. **No informal solved/proved/disproved or formal-proof status changed.** Only E338's statement-formalization flag changed from no to yes, dated **2026-10-19**; its informal state remains open and formal proof state unformalized. Status alone demonstrably misses E488's concrete proof source.

| Original ID | Live informal state | Change against October 19 snapshot |
| --- | --- | --- |
| 302 | open | Unchanged |
| 835 | verifiable | Unchanged |
| 628 | falsifiable | Unchanged |
| 617 | falsifiable | Unchanged |
| 503 | open | Unchanged |
| 291 | open | Unchanged |
| 367 | open | Unchanged |
| 602 | open | Unchanged |
| 670 | open | Unchanged |
| 124 | open | Unchanged |
| 939 | open | Unchanged |
| 23 | falsifiable | Unchanged |
| 287 | falsifiable | Unchanged |
| 338 | open | Statement flag only: no → yes, 2026-10-19 |
| 699 | falsifiable | Unchanged |
| 488 | falsifiable | Unchanged |
| 672 | verifiable | Unchanged |
| 273 | open | Unchanged |
| 261 | open | Unchanged |
| 596 | open | Unchanged |
| 668 | open | Unchanged |
| 657 | open | Unchanged |
| 238 | open | Unchanged |
| 413 | open | Unchanged |
| 44 | open | Unchanged |
| 711 | open | Unchanged |
| 727 | open | Unchanged |

“Falsifiable” and “verifiable” indicate unresolved problems with potential finite counterexamples/witnesses, not completed disproofs/proofs. E939 here means only the r≥4 sum scope, not the separately completed triples branch. The October 22 feedback record supersedes the October 19 count: 27 Draft PRs and five Ready PRs, with PR5089 Ready for triples scope review.

## Evidence and limits

Baseline read: `verification/2026-10-19-repairs/REPAIR_QUEUE.md`, `REVIEW_STATUS.md`, `reports/progress-2026-10-19/review-corrections.md`, `reports/draft-status-2026-10-19/README.md`, `DRAFTS.json`, and `reports/feedback-2026-10-22/README.md`. All 27 pages and live database entries were read; comments and proof-claim threads were selectively read for 302,617,602,273,727,488,338,699,835. Raw forum captures are in `raw-evidence/draft-forums/`. Source leads, pinned E488 files, proof note and E727/E338 READMEs are in `raw-evidence/draft-leads/`; normalized database differences are in `raw-evidence/draft-status-comparison.json`.

Public GitHub API requests for the gist/tree hit HTTP 403 rate limits; direct pinned raw-source URLs succeeded. An initial guessed pinned gist filename URL returned 404, then the actual current pinned raw URL was extracted from the fetched gist and successfully saved. Those failures are recorded in the lead manifest. No exhaustive literature/priority audit, full website history audit, revalidation of every claim, or general-k E727 route was performed. No project proof changed, no commit, PR action, message or external write was made. The bounded stop is **one full-scope route identified with existing Lean; no further complete route found in checked evidence**, not a claim that the remaining 26 are globally unsolved.
