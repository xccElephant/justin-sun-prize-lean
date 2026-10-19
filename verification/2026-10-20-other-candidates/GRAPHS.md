# JSP464 and JSP628: bounded original-scope / endpoint check

Checked 2026-10-20, Asia/Shanghai (live retrieval began 2026-10-19 16:29 UTC). Scope was these two official JSP entries only, with an eight-minute ceiling. Neither is admitted for implementation. No new mathematical proof, complete Lean proof, prize submission, commit, or external mutation was made. Third-party sources below are review evidence, not our work.

Read `NEXT_STRATEGY.md` through its final update and the selected records in `verification/2026-10-19-discovery/CANDIDATE_LEDGER.json`. Baseline remains 295 solved entries without a catalog-confirmed complete Lean proof; 53 entries with varied-depth records and 242 remaining before this review. This report does not edit that shared ledger or increment certified-completion counts. Independent read-only retrievals were performed within the delegated sidecar.

Official catalog pin: `fd8fa66abb4e21df828fdebc25298e9ad75521bd`. Existing plby proof pin: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. The map's 464→574 and 628→767 entries agree here, but correspondence was checked against actual problem text, catalog bibliography, and proof definitions rather than inferred from the map.

| Candidate | Existing original-question endpoint | Decision |
| --- | --- | --- |
| JSP464 / Erdős574 | `Erdos574.not_erdos_574`, plby `src/latest/ErdosProblems/Erdos574.lean` | Existing full negative answer to the original universal conjecture; separate explicit catalog-scope rejection in live PR504. No credible complete-prize route identified. |
| JSP628 / Erdős767 | `Erdos767.erdos_767`, plby `src/latest/ErdosProblems/Erdos767.lean:1566` | Existing complete eventual equality for every positive k; no actual missing formalization lemma identified. Stop. |

## JSP464: exact question, construction, and scope blocker

The live Erdős574 page asks whether, for every integer k≥2,

`ex(n; {C_(2k-1), C_(2k)}) = (1+o(1)) (n/2)^(1+1/k)`.

This is one universally quantified yes/no conjecture. Disproving k=3 answers that original conjecture completely; it does not determine the actual extremal number for every k. The page reports LUW94b counterexamples for k=3 and k=5, and an alternative k=3 result in FNV06. The k=2 links and later related problems are contextual references, not extra clauses in the displayed question. The official JSP catalog instead uses the broad wording “How many edges can a graph have ...” and cites those same papers. See [original-page capture](evidence/erdos574.txt) and [fixed catalog excerpt](evidence/catalog-0401-0500.md.excerpt).

At the plby pin, the admissibility predicate is genuinely `(cycleGraph (2*k-1)).Free G ∧ (cycleGraph (2*k)).Free G`. The extremal number is a finite supremum over every admissible labelled simple graph on `Fin n`; it is not a stipulated numerical formula. The comparison function uses real powers. The final theorem's entire type is:

```lean
theorem Erdos574.not_erdos_574 :
  ¬ (∀ k : ℕ, 2 ≤ k →
    (fun n : ℕ ↦ (consecutiveCycleExtremalNumber k n : ℝ)) ~[atTop]
      erdos574Comparison k)
```

See [fixed source](evidence/Erdos574.lean). This final theorem has no LUW existence hypothesis, cycle-freeness hypothesis, supplied asymptotic inequality, or other unproved mathematical premise.

The finite construction and analytic contradiction are concrete. With q=2^(2a+1), points and lines are triples over the finite field of order q, with incidence `l.y-p.y=l.x*p.x` and `l.z-p.z=l.y*p.x`. There are q³ points, two copies of each of q³ lines, and 2q neighbours at every point, giving 3q³ vertices and 2q⁴ edges. `AffinePolarity.no_incidence_C4` follows from uniqueness of a line through two distinct points; `no_incidence_C6` uses the three-variable Vandermonde calculation, whose polynomial identities and nonzero factors are explicitly proved. The duplicated line side still has no hexagon: three different lines give the original hexagon contradiction, two distinct underlying lines give a quadrilateral contradiction, and three copies of one line are impossible with only two labels. Bipartiteness excludes C5. Isomorphism to `Fin (3*q^3)` bridges the construction to the real extremal function. The final argument proves a uniform ratio gap greater than 11/10 along these unbounded orders and contradicts asymptotic equivalence. These are already implemented steps, not missing lemmas for us.

Live PR3998 remains open and names exactly this plby pin. Live PR504 is closed, not merged; its body references a second source at `CollinYuanjieRen/awards`, commit `e3ce0e774f169915e554e7bdeb0a3496a7e3b885`. We did not retrieve that second implementation after finding the plby endpoint. Its title/body alone are not treated as proof certification.

Crucially, the live PR504 closure comment dated **2026-09-30 08:40:40 UTC** explicitly says that failing to determine the exact extremal number constitutes incomplete catalog scope. It also gives attribution/identity and repository-architecture objections. Preserve those as the recorded reasons for that submission's rejection; do not extrapolate them into a general mathematical invalidity verdict on the plby theorem or claim that all future submissions are categorically rejected. See [live PR504](evidence/pr504.json), [closure comment](evidence/pr504-comments.json), and [live PR3998](evidence/pr3998.json).

**Stop condition:** the original universal conjecture already has an unconditional full source endpoint, while the broader catalog interpretation has an explicit adverse scope notice. We have neither a new complete determination nor a bounded known proof route for that broader demand. Renaming the existing negative answer would not resolve either obstacle. Award eligibility is not established.

## JSP628: all-positive-k eventual equality is already present

The live original question defines g_k(n) as the maximum number of edges in an n-vertex graph with no cycle containing k distinct chords incident to one cycle vertex, and asks whether

`g_k(n) = (k+1)n - (k+1)^2`

for sufficiently large n. The positive-k convention is explicit in the corresponding Formal Conjectures statement (`∀ k ≥ 1`). The narrative's Czipszer upper bound, Pósa k=1 threshold n≥4, Erdős k=2/3 observations, and Lewin historical remark are background results; they are not additional questions requiring every small-n value to be determined. Jiang's uniform n≥3k+3 theorem implies the complete original eventual question, including k=1. See [original-page capture](evidence/erdos767.txt) and [fixed catalog excerpt](evidence/catalog-0601-0700.md.excerpt).

The existing definition is exactly a Mathlib simple cycle plus an injective selector of k opposite endpoints satisfying `c.IsChord s(v, f i)`. It forbids a cycle having **at least** k distinct incident chords, not just cycles having exactly k total chords. The graph maximum ranges over all labelled graphs; the finite-supremum vs Formal Conjectures `sSup` presentation is a definitional representation difference, not an absent geometric bridge. The selected predicate agrees literally with the current Formal Conjectures predicate after argument order.

At the same plby pin the final type is:

```lean
theorem Erdos767.erdos_767 (k n : ℕ) (hk : 0 < k)
    (hn : 3 * k + 3 ≤ n) :
  chordCycleExtremalNumber k n =
    (k + 1) * n - (k + 1) ^ 2
```

See [fixed source, endpoint](evidence/Erdos767.lean#L1566). Its only explicit mathematical premises are the intended parameter restrictions. This is stronger than an existential unknown threshold.

The lower bound uses K_(k+1,n-k-1), proves chord avoidance for every simple cycle, counts the edges, and transports to the labelled extremal problem. The upper bound uses low-degree deletion and strong induction from n=3(k+1). The base is supplied by `jiang_base`, using `cyclic_free_edge_bound`, not left as a Bondy hypothesis. In the two-connected nonspanning case, `Erdos767Dirac.exists_nonspanning_longestCycle_lowDegree` supplies a possibly different longest cycle and an exterior vertex with `2*degree ≤ cycle.length`. Its proof uses an actual best-lollipop construction and `BestLollipop.relative_low_degree`; the case split and fan-splicing lemmas are project dependencies. Cut vertices and disconnected components are handled by genuine induced-subgraph and Erdős–Gallai bounds. This closes the actual global forcing proof. The separately present `jiang_base_of_bondy` is conditional, but the public final endpoint calls the unconditional `jiang_base` instead.

The live Formal Conjectures file explicitly records `formal_proof ...` linking to this exact plby pin and line 1566. Its own declaration has `sorry`, as do its variant declarations; that file is a statement registry with an external proof link, not itself a completed proof. We inspected the linked source above. See [live Formal Conjectures capture](evidence/fc767.lean).

Live PR4048 remains open and links that same proof. Live PR573 remains open; it now expressly disclaims first-formalization credit and references `Allen20202020/erdos-767-sharpness` at `d8adb111e7ca285b58b56d30fc052a2e5a825202` plus the plby pin. Its `JSP628Full.original_resolution` is exactly:

```lean
theorem original_resolution (k : ℕ) (hk : 0 < k) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Erdos767.chordCycleExtremalNumber k n =
      (k + 1) * n - (k + 1) ^ 2 :=
  ⟨3 * k + 3, fun n hn => Erdos767.erdos_767 k n hk hn⟩
```

We retrieved that wrapper and its exact statement correspondence, then stopped looking for further source endpoints. Its incremental least-threshold lower bounds do not reopen the original eventual equality. The package expressly does not claim the newer Chen–Ning improved upper threshold. Its contributor-run NaNoda record reports 12,952 checked declarations and standard three permitted axioms; we preserved it as an external claim, not a check run by us. See [live PR573](evidence/pr573.json), [wrapper](evidence/allen-original-Main.lean), [correspondence](evidence/allen-statement.md), and [external check record](evidence/allen-independent.json).

**Stop condition:** a full source endpoint for every positive k and every order beyond a proved uniform threshold already exists, with the same actual cycle/chord definitions and extremal maximum. No missing core formalization lemma or first-complete-prize vacancy was found. Do not pursue newer threshold refinements as a substitute for an original-scope vacancy.

## Verification depth and retrieval limits

The transitive local project-import scan found **7 project modules for E574 and 27 for E767**, with no missing local import and no text-scan flags for executable `sorry`, `admit`, declared `axiom`, or declared `opaque`. The audit is reproducible in [project-import-audit.json](evidence/project-import-audit.json), and all scanned files are preserved under `evidence/plby-source/`. This is a textual dependency scan plus reading of definitions, endpoints, and selected crucial assembly; it is not an exhaustive independent mathematical audit, a Lean compilation, an axiom closure check, or kernel replay. We made no build attempt because the bounded screening procedure stops once a decisive existing endpoint is found.

The exact original conjecture wording was fetched live from the numbered Erdős pages, and source correspondence was checked against the pinned catalog and actual Lean definitions. The UCSD historical problem-collection page timed out; Jiang's publisher page returned 403. Neither historical paper's complete original text was obtained or independently checked in this bounded pass. Therefore this report does not claim a newly independently verified complete informal proof from the journal papers. This limitation does not create a missing formalization route after the existing unconditional endpoints have been located.

Unauthenticated GitHub API curl returned 403; read-only `gh api` succeeded for selected PRs and PR504 comments. HTML PR pages were also fetched. All selected live PR heads, timestamps, provenance, retrieval limitations, and saved-file hashes are in [provenance.json](evidence/provenance.json); URL retrieval records are in [fetch-manifest.json](evidence/fetch-manifest.json). No claim of absolute global priority, committee acceptance, or payable award is made.

Outcome: **0 new admitted implementation candidates; 0 newly completed proofs.** These are two additional bounded review records, with the stated limits. No shared ledger or existing PR state was changed.
