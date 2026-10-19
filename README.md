# Justin Sun Prize — Lean 4 Formalization & Proofs (`JspBounties`)

- **Author**: `@xccElephant` (Ethan Xiang)
- **Repository**: `https://github.com/xccElephant/justin-sun-prize-lean`
- **Toolchain**: `leanprover/lean4:v4.33.1`
- **Mathlib revision**: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`)
- **Verification**: All problem modules compile with **zero `sorry`**, **zero `admit`**, and **zero custom `axiom`** declarations, depending exclusively on the standard classical Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Verification status (2026-10-19)

There are 32 open records: 28 drafts, two scoped complete proofs ready for review (5076/5079), and two literal-scope reviews (5080/5095). [Current review status](verification/2026-10-19-repairs/REVIEW_STATUS.md). They cite 27 distinct source files; the repository contains 33 problem modules plus `Basic.lean`. A successful Lean check does not mean a module solves the full prize problem or qualifies for an award.

The earlier baseline audit compiled all 34 modules, checked the axiom dependencies of all 2,514 theorem declarations (including generated declarations), and replayed all 34 modules with Lean's `leanchecker`. Only the standard classical axioms were observed. The original default Lake build failed because `JspBounties.*` included a missing root module; the local configuration now uses `JspBounties.+` and the full build passes. Historical submitted commits retain the original configuration.

All 32 PR bodies and catalog changes were corrected in place; PR5080 and PR5095 subsequently moved to scope review, leaving 28 drafts with explicit gaps. All 109 corrected target references pass Lean checks. [Correction record](verification/2026-10-19/CORRECTIONS.md). The historical audit found 23 nonexistent target names across ten PRs, and broader statement mismatches. Most modules prove a special case or related theorem. See [verification evidence and scope limitations](verification/2026-10-19/README.md). Earlier completeness, uniqueness, priority and revenue estimates are withdrawn; source verification is separate from award eligibility.

Scope clarification: the catalog’s literal #372 existence question is already proved; whether its prize scope instead requires infinitely many triples remains unresolved. PR5095 now also proves the literal two-integer statement, while the original k-integer conjecture remains unproved. Current dispositions are 2 complete scoped-proof reviews, 2 literal-scope reviews, and 28 incomplete drafts. [Scope recheck](verification/2026-10-19/SCOPE_RECHECK.md).

## Proof repair batch (2026-10-19)

The repair batch at `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe` adds the unconditional four-term square-product theorem for Erdős672, the unconditional second question of Erdős711, and infinite powerful-sum families for every r≥6 in Erdős939. It also closes the eventual/logarithmic quantifiers in the c₂<2 branch of Erdős238 and adds checked construction/necessity lemmas for124,261,372,727. These are repairs of existing records; no new prize problem was submitted.

The full project build passed (8740 jobs), all18 repair targets passed, and all8 changed modules passed Lean kernel replay. [Repair evidence and remaining scope](verification/2026-10-19-repairs/README.md). Complete original-problem coverage remains unresolved for these draft records; the full repair campaign is not complete.

## Parallel campaign (2026-10-19)

Nineteen agent instances covered sixteen original work/review groups plus replacement, independent integration review and followup. [Full campaign summary](verification/2026-10-19-parallel/CAMPAIGN_SUMMARY.md) and [all 32 obligations](verification/2026-10-19-parallel/CAMPAIGN_LEDGER.json).

The new `Erdos885.TwoNumbers.literal_two_numbers` theorem proves that two positive integers can have arbitrarily many common factor differences. A self-contained mathematical proof, independent positive-factor definition check and kernel replay accompany it. PR5095 was updated for explicit scope review. This does not solve the stronger k-integer conjecture.

Six further source modules gained verified partial repairs or corrected scope descriptions. The integrated project passed 8,740 jobs with stable hashes; nineteen new relevant target types passed axiom checks, and all six additional modules passed kernel replay. Seven existing drafts were updated to commit `36c356983c53bfd9ceec618f58107942b9afbcb1`. [Evidence](verification/2026-10-19-parallel/README.md). Full repair and award approval remain incomplete.

## Quick Verification

To verify any module using the precompiled Mathlib cache:

```bash
lake exe cache get
lake build
./check_lean.sh JspBounties/Erdos348.lean
```

## Verified Module Inventory (Includes Partial Results)

| File | JSP ID | Erdős # | Key Verified Theorems |
| :--- | :--- | :--- | :--- |
| `JspBounties/Erdos348.lean` | `JSP-000290` | #348 | `Erdos348.erdos_348` (Full classification of deletion thresholds $0 \le m < n$ for complete sequences, including Geneson's Central-Interval Theorem) |
| `JspBounties/ErdosGraph.lean` | `JSP-000058` / `JSP-000500` / `JSP-000509` | #23 / #617 / #628 | `Erdos23.erdos_23.variants.n1`, `n1_tight`, `Erdos617.erdos_617.variants.r2`, `r_eq_3` (Erdős–Gyárfás 1999), `Erdos628.erdos_628.variants.k_5_a_3_b_3` (Brown–Jung 1969), `independence_number_2` (Balogh–Kostochka–Prince–Stiebitz 2009) |
| `JspBounties/Erdos503.lean` | `JSP-000403` | #503 | `erdos_503.variants.R0`, `erdos_503.variants.R1`, `kelly_R2_lower_bound`, `kelly_R3_lower_bound`, `alweiss_construction`, `erdos_503_lower_bound_of_bddAbove` |
| `JspBounties/Erdos835.lean` | `JSP-000691` | #835 | `property_iff_chromaticNumber`, `indepNum_johnson_le_johnsonBound`, `ma_tang_prop_2_1`, `johnson_chromaticNumber_composite`, `johnson_chromaticNumber_odd`, `johnsonGraph_18_9_chromaticNumber`, `johnson_chromaticNumber_four` ($k=4$ prime case) |
| `JspBounties/Erdos287.lean` | `JSP-000244` | #287 | `erdos_287_best_possible`, `erdos_287_gap_at_least_two` (Erdős 1932), `erdos_287_prime_conjecture_implies` |
| `JspBounties/Erdos131.lean` | `JSP-000137` | #131 | `exists_card_eq_F`, `F_small_values`, `F_le_H_nonavg`, `card_le_of_mem_nonDividing`, `F_le_half` ($F(N) \le (N+1)/2$), `propertyP_Icc_top`, `erdos_131_of_pham_zakharov` |
| `JspBounties/Erdos488.lean` | `JSP-000395` | #488 | `erdos_488_singleton`, `erdos_488_sharpness`, `erdos_488_pair`, `erdos_488_of_two_mem`, `erdos_488_insert_gt_half`, `erdos_488_nonmultiples_false` |
| `JspBounties/Erdos216.lean` | `JSP-000198` | #216 | `g_zero_eq`, `g_three_eq`, `not_convexIndep_of_fourth_in_hull`, `card_hortonSet`, `horton_top_strictly_above_bottom_secant` (Horton 1983 Observation g) |
| `JspBounties/Erdos365.lean` | `JSP-000301` | #365 | `golomb_pair`, `erdos_365.parts.i`, `parametric_nonSquare_powerful_family`, `walkerSeq_properties`, `infinite_nonSquare_consecutive_powerful` (Walker 1976 infinite family) |
| `JspBounties/Erdos672.lean` | `JSP-000546` | #672 | `not_erdos672With_two`, `not_erdos672With_three_two`, `euler_four_ap_identity`, `erdos_672_four_two_of_sq_le`, `four_consecutive_ne_sq`, `erdos_672_four_two_primitive_pythagorean` |
| `JspBounties/Erdos238.lean` | `JSP-000210` / `JSP-000211` | #238 / #240 | `erdos_238_block_pigeonhole`, `erdos_238_small_c1_of_brun_chebyshev`, `erdos_238_unconditional_of_c2_lt_two`, `single_prime_smooth_gap_ge` |
| `JspBounties/Erdos372.lean` | `JSP-000307` | #371 / #372 | `jsp_000307_least_decreasing_triple` ($n=13$), `decreasing_quadruple_317`, `infinite_maxPrimeFac_valley`, `infinite_maxPrimeFac_gt_succ`, `infinite_maxPrimeFac_lt_succ` |
| `JspBounties/Erdos575.lean` | `JSP-000465` | #575 | `card_le_one_of_no_K12_no_2K2`, `matchingGraph_card_and_K12_free`, `starGraph_card_and_2K2_free`, `unique_common_neighbor_of_C4_free`, `common_neighbors_coincide_of_C4_C6_free`, `Z_uv_independent_of_C4_C6_free` |
| `JspBounties/Erdos699.lean` | `JSP-000569` | #699 | `choose_gcd_gt_one` (Erdős–Szekeres 1978), `erdos_699_of_le_two`, `erdos_699_of_prime_in_interval`, `erdos_699_succ_of_not_prime`, `mem_exceptions_of_erdos_szekeres_strengthening` |
| `JspBounties/Erdos338.lean` | `JSP-000280` / `JSP-000281` | #338 / #339 | `erdos_338_bateman`, `erdos_338_bateman_exact` (least ordinary order exactly h, no restricted order), `erdos_339_order_two_contains_all_large_odd`, `erdos_339_order_two_counting_bound` |
| `JspBounties/Erdos940.lean` | `JSP-000782` | #940 | `Nat.two_full_iff_exists_sq_mul_cube`, `seven_not_sum_three_powerful` |
| `JspBounties/Erdos302.lean` | `JSP-000254` | #302 | `erdos_302.variants.lower_half`, `erdos_302.variants.lower_seventeen_thirtyseconds`, `erdos_302.parts.ii` (disproves $f(N) = (1/2+o(1))N$) |
| `JspBounties/Erdos364_366.lean` | `JSP-000300`–`JSP-000302` | #364–#366 | `erdos_364_weak`, `no_four_consecutive_full`, `erdos_364_mod_thirtysix_barrier`, `erdos_366_mod_eight_barrier` |
| `JspBounties/Erdos602.lean` | `JSP-000489` | #602 | `erdos_602.variants.countable_index` (Bernstein Property B theorem), `erdos_602.variants.disjoint`, `erdos_602.variants.two_sets`, `disjoint_without_infinite_claim.disproof` |
| `JspBounties/Erdos261.lean` | `JSP-000226` | #261 | `erdos_261.variants.borwein_loring`, `erdos_261.variants.borwein_loring_property`, `erdos_261.parts.i`, `erdos_261.variants.two_representations` |
| `JspBounties/Erdos885.lean` | `JSP-000736` | #885 | `TwoNumbers.literal_two_numbers`, `TwoNumbers.literal_two_number_witnesses` (complete two-integer scope; not the k-integer conjecture), plus `erdos_885.variants.k_eq_2`, `k_eq_3`, `k_eq_4` |
| `JspBounties/Erdos124.lean` | `JSP-000131` | #124 | `erdos124.zero`, `erdos124.zero_all`, `erdos124.converse`, `erdos124.eventually_iff_le_sum` |
| `JspBounties/Erdos273.lean` | `JSP-000234` | #273 | `erdos_273.variants.three` (Explicit 12-congruence strict covering system mod 360 with moduli $p - 1$, $p \ge 3$ prime) |
| `JspBounties/Erdos291_367.lean` | `JSP-000247` / `JSP-000303` | #291 / #367 | `Erdos291.erdos_291.parts.ii`, `Erdos367.erdos_367.parts.ii`, `Erdos367.erdos_367.variants.k_le_two`, `Erdos367.erdos_367.variants.k_ge_three_lower` |
| `JspBounties/Erdos670.lean` | `JSP-000544` | #670 | `erdos_670.variants.dim_one` (Erdős 1997 $(1-\varepsilon)n^2$ diameter bound), `erdos_670.variants.choose_two` |
| `JspBounties/Erdos939.lean` | `JSP-000780` / `JSP-000781` | #939 | `erdos_939.variants.triples`, `erdos_939.variants.finite`, `erdos_939_six_infinite`, `erdos_939.variants.seven`, `erdos_939.variants.eight`, `erdos_939.variants.examples` |
| `JspBounties/Erdos80_596_668.lean` | `JSP-000097` / `JSP-000483` / `JSP-000542` | #80 / #596 / #668 | `Erdos596.erdos_596.variants.C4_free_countable_escape`, `Erdos668.erdos_668.parts.ii`, `Erdos668.erdos_668.variants.four_points`, `Erdos80.unrestricted_erdos_80_parts_i` |
| `JspBounties/Erdos657.lean` | `JSP-000533` | #657 | `erdos_657.variants.straus` (Straus $2^k$-point hyperbox isosceles-free construction in $\mathbb{R}^k$) |
| `JspBounties/Erdos44.lean` | `JSP-000072` | #44 | `erdos_turan_parabola_sidon`, `sidon_set_lower_bound_sqrt_div_three`, `greedy_sidon_construction`, `maxSidonSubsetCard_icc_bound` |
| `JspBounties/Erdos319.lean` | `JSP-000265` | #319 | `erdos_319_isBigO`, `adenwalla_irreducible_of_unit_fraction_sum`, `erdos_319_isTheta_of_lb` |
| `JspBounties/Erdos413.lean` | `JSP-000340` | #413 | `erdos_413_parts_ii_iff_linear_omega`, `erdos_413_parts_ii_of_lau_v3` (conditional), `barrier_traps_iterates`, `barrier_coalesces_trajectories`, `infinite_not_isBarrier_omega` |
| `JspBounties/Erdos711.lean` | `JSP-000579` | #711 | `exists_isMinimalIntervalLength`, `isMinimalIntervalLength_add_iff_of_dvd`, `n_add_one_le_of_hasDivisibleDistinctTuple` |
| `JspBounties/Erdos727_273.lean` | `JSP-000595` / `JSP-000234` | #727 / #273 | `Erdos727.erdos_727.variants.k_1` (Balakram infinite family $((n+1)!)^2 \mid (2n)!$), `Erdos273.erdos_273.variants.three`, `Erdos273.erdos_273.variants.three_int` |
