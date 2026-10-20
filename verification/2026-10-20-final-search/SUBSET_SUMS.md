# Final bounded subset-sum audit — 2026-10-20

**Verdict: neither candidate is admitted as a doable new problem. Stop the candidate search.** Both fail the required complete-final-theorem-absence gate: an already-published, exactly pinned local source contains an unconditional endpoint covering the original mathematical question. This is a substantive definition/statement/input inspection, not a rejection based on PR titles or the catalog's Lean field. This audit does **not** establish independent compilation, kernel replay, organizer acceptance, award eligibility, or priority.

| Candidate | Correct original | Actual requested endpoint | Decision |
| --- | --- | --- | --- |
| JSP-000632 | Erdős #771 | f(n)/(n/log n) → 1/2, with the universal target followed by an existential avoiding subset | Existing full-scope source endpoint; no new-work admission |
| JSP-000725 | Erdős #874 | k(N)/sqrt N → 2, where k optimizes over every admissible subset of [1,N] | Existing full-scope source endpoint, plus eventual exact formula; no new-work admission |

## Pins, endpoints and scope of evidence

Work was confined to these two candidates in `/Users/xcc/Project/justin-sun-prize-lean`. Workspace HEAD: `4964100c01983155f8e29f4138082fe58a8df405`. Read-only references:

- `reference/awards`: `87402fe6cbbff6844f7e324f30a4348477b196a4`.
- `reference/lean-proofs` (`plby/lean-proofs`): **`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`**. This is also the proof pin cited by the decisive live PRs.
- `reference/erdosproblems`: `6f63fe53e757f2976fd8559c1e02f0726074c38f`.
- `reference/formal-conjectures`: `e754a78c74a3f2bbc38e4f2063b5f6eed51bde39`. No `771.lean` or `874.lean` exists in its Erdős directory at this checkout; absence there is not proof absence elsewhere. Erdős #632 concerns a different problem and was not used as this candidate's source.

The local discovery ledger marks both `unreviewed_beyond_metadata` and not approved for implementation. The catalog lists both Solved / Lean No / Eligible No. Those administrative fields do not override actual proof-source evidence. Catalog bibliographies independently match #771's Alon–Freiman 1988 result and #874's Straus / Erdős–Nicolas–Sárközy / Deshouillers–Freiman results.

Live read-only checks on 2026-10-20: the original pages `https://www.erdosproblems.com/771` and `/874`; GitHub pull-request API endpoints for awards PRs #4049, #4126 and #361. Raw pages, extracted text, raw PR JSON, and PR bodies are saved in `evidence/`. #4049 remains open at head `183eb074d400952a2758975abd79f5312f68bbf5`; #4126 remains open at `576ace98c791dc51bc5bcf82402697f4fb192fe3`; neither is merged. Both explicitly register the external proof at the above full pin. These observations establish a public prior source submission, not acceptance. #361 is supplemental evidence only: its body identifies the same imported #874 upper proof plus a natural/integer statement bridge at another repository's pin. That external bridge was not built or exhaustively audited here and is unnecessary to the verdict.

The actual project is **`reference/lean-proofs/src/latest`**, not its repository root. Toolchain: `leanprover/lean4:v4.33.0`; exact manifest and Lake configuration copied to evidence. The current workspace's v4.33.1 cache cannot be assumed to verify this v4.33.0 project.

## JSP-000632 / Erdős #771

The live original defines f(n) as the largest cardinality such that **for every positive m there exists S ⊆ {1,…,n} of that cardinality with no subset summing to m**. The avoiding set can depend on m. It is not an optimization over an arbitrary externally supplied finite integer set. The catalog's broad wording is resolved by the original statement, bibliography and explicit PR mapping; no invented arbitrary-set generalization was admitted.

At the proof pin, `src/latest/ErdosProblems/Erdos771.lean` defines:

- `AvoidsSubsetSum m S := m ∉ S.subsetSum` (line 45).
- `AdmissibleCard n k := ∀ m, 0 < m → ∃ S, S ⊆ Icc 1 n ∧ S.card = k ∧ AvoidsSubsetSum m S` (line 49).
- `erdosF n := Nat.findGreatest (AdmissibleCard n) n` (line 59).

The empty set supplies cardinality zero for every positive target. `erdosF_spec`, downward closure of admissibility, and `admissibleCard_iff_le_erdosF` connect the maximum to the actual universal-target optimization. Zero is excluded as a target because the empty subset sums to zero. Positivity of the ambient interval prevents negative-integer or zero-element ambiguities.

**Final endpoint:** `Erdos771.erdosF_asymptotic` at line 4528, and `Erdos771.erdos_771` at line 4547, both state

```lean
Tendsto (fun n : ℕ =>
  (erdosF n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)))
  atTop (𝓝 (1 / 2 : ℝ))
```

Neither takes an unproved asymptotic, representation theorem, or structural certificate as an argument. The final theorem is proved from `erdosF_asymptotic`. The peculiar `Iff.mp … trivial` wrapper does not weaken its type: its substantive branch invokes that asymptotic theorem.

The direct difficult upper input is `afTarget_mem_subsetSum` (4087): every A ⊆ [1,n] above the explicit threshold represents the same selected positive target. Its hypotheses are only eventual numerical size conditions and the ambient/cardinality conditions. The threshold is `n / s + 16 * binaryScale n ^ 16 + s`; the target is the LCM at a maximal cutoff, and s is its least positive nondivisor. `eventually_erdosF_lt_afCardThreshold` (4223) discharges the size conditions, then the threshold ratio tends to 1/2. The final upper step uses this eventual theorem, not a free representation hypothesis.

The difficult representation chain is implemented: `af_uniform_representation` (4000) → `uniform_divisible_representation` (2945) → `exists_long_multiples` (2795) → `exists_sparse_seed_progression` (2637). These construct dense coverage of multiples, with exponential-decay conditions discharged by the later seed estimates. The prime-power residue endpoint supplies the missing residue needed to reach the common target; the least nondivisor is proved to be a prime power. The lower side uses multiples of a small prime not dividing m; large m exceeds the sum of the entire interval. Chebyshev/prime asymptotics control that prime uniformly and identify the LCM cutoff scale. Thus the input seam is substantial analytic and additive mathematics, not an elementary fixed-set powerset calculation.

The live original attributes the lower bound to Erdős–Graham and the complementary upper bound to Alon–Freiman [AlFr88]. Its classical target cutoff is n²/(20(log n)²). The source uses adjusted polylogarithmic cutoffs and proves their limiting scale; literal equality with the exposition's chosen cutoff is not needed for the same final theorem. This audit traced the route and read the decisive types/bodies; it did not reconstruct and independently verify every inequality of the complete historical proof. The source header refers to `tex/771.tex`, but that exact path is absent locally, so no claim of having read that exposition is made.

## JSP-000725 / Erdős #874

The live original maximizes |A| over A ⊆ {1,…,N} for which sums of r distinct elements and sums of s distinct elements are disjoint whenever r,s ≥ 1 and r ≠ s. Equal sums of the same cardinality are permitted. This is not the stronger all-subset-sums-distinct property.

At the pin, `Erdos874/Foundations.lean` defines `restrictedSumset r A` as the image of `A.powersetCard r` under integer summation (35); `IsAdmissible` compares different positive layers (65); `ambient N := Icc 1 (N : ℤ)` (139); `boundedAdmissibleFamily` filters the entire powerset of that interval (151); and **`k N := (boundedAdmissibleFamily N).sup Finset.card`** (168). Attainment of the maximum and `card_le_k` establish optimization over all competitors, rather than just an interval construction. The equivalence with cardinality-determined subset sums is proved, including the empty-subset case for positive ambient sets (122). Overlapping subsets are permitted: cancellation is not confused with disjointness of summand sets.

**Final endpoints in `Erdos874.lean`:**

- `Erdos874.erdos_874_lower_bound` (45): for every N, `Nat.sqrt (4*N+1) - 1 ≤ k N`.
- `Erdos874.erdos_874_eventual_exact` (102): eventually `k N = strausLength N`, where the length is `Nat.sqrt (4*N+1) - 1`.
- `Erdos874.erdos_874` (109): `Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.sqrt N) atTop (nhds 2)`.

The latter two are unconditional. In particular, the final proof supplies `hasEventuallyLargeSetStructure` to `eventually_maximizers_density_endgame`; it does not leave either as a hypothesis. Conditional adapter theorems appear earlier in the file, but the public endpoints close that seam.

Direct hard input inspection:

1. `Structure.hasEventuallyLargeSetStructure` (502) follows from the proved `eventually_hasLargeSetStructure` (379). It constructs the Deshouillers–Freiman structure for arbitrary bounded admissible A with |A| > (49/25)√N. The exceptional subset has ≤10⁵N^(5/12) elements, a restricted layer contains a long arithmetic progression with ≥3N^(5/6) terms, and the regular part lies in a short progression with ≤N^(7/12) terms, sharing a positive difference.
2. The structure proof selects a small fourth sum layer, invokes the implemented restricted-sum progression engine, and supplies the finite modular/residue/room estimates. `FreimanThreeKInductive.freiman_three_k_minus_four_inductive_explicit` (196) supplies the inverse small-doubling theorem using `lev_smelianski_self_sum_inductive`, rather than assuming Freiman's theorem as a new axiom. Modular structure and endpoint orientation are substantial proof modules.
3. `EndpointOrientation.eventually_maximizers_density_endgame` (553) constructs the density certificate via `eventually_extractedCentralBlock`. The final file supplies the established structure theorem to it.
4. `ExactUpper.card_sq_le_of_density_endgame` (393) proves `(A.card+1)^2 ≤ 4*N+1`. Applying it to actual maximizers gives the matching eventual upper bound. Straus's terminal interval supplies the lower bound for every N; integer-square-root asymptotics then give the limit 2.

The live original and catalog cite [DeFr99] for the large-N solution, and PR #361 points to its Theorem 1, pages 141–142. That paper was not fetched in this bounded audit. The independently read local chain already rules out theorem absence. No all-small-N exact optimality or classification of all maximizers is asserted.

## Verification limits and stopping decision

The saved source-import inventories are `evidence/cone-771.json` and `cone-874.json`. Recursively following explicit non-Mathlib imports found **39 local modules / 56,219 lines** for #771 and **41 / 25,160** for #874. Every inventoried local file was byte-compared with `git show` at the full proof pin; all matched. A lexical check after comment stripping found no `sorry`, `admit`, `axiom` or `native_decide` in those local modules. This is a source inventory and token screen, not Lean's declaration-level axiom analysis. Comparator challenge stubs contain `sorry` but are not imported by these solution roots and do not establish a solution gap.

#771 has unresolved external import boundaries in this inventory: `Batteries.Tactic.Lemma` and `BoundedGaps.BombieriVinogradov.Proof.MainTheorem`. The saved manifest pins those dependencies; the external code and its transitive Mathlib trust cone were not audited or built. #874's followed non-Mathlib imports are local, but Mathlib itself was likewise not rebuilt. PR bodies' axiom-hygiene and build statements remain submitter claims. **No independent successful build or kernel replay of either endpoint is claimed here.**

Admission required all three: absence of an existing complete endpoint, a complete known mathematical proof, and controlled Lean difficulty. The first already fails for both; the inspected implementation routes also show substantial dependencies. There is no established genuine mathematical/Lean endpoint gap to implement. A future verification failure might motivate a separate repair investigation, but no such failure was demonstrated here and it cannot be treated as a new candidate.

Only report/evidence files were created. No mathematical source edits, dependency updates, builds, remote mutation or further candidates. The bounded search ends with **zero admitted new problems**.
