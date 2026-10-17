# Justin Sun Prize — Lean 4 Formalization & Proofs (`JspBounties`)

- **Toolchain**: `leanprover/lean4:v4.33.1`
- **Mathlib revision**: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`)
- **Verification**: All 26 problem modules (11,335 lines of Lean 4) compile with **zero `sorry`**, **zero `admit`**, and **zero custom `axiom`** declarations, depending exclusively on the standard classical Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Quick Verification

To verify any module using the precompiled Mathlib cache:

```bash
./check_lean.sh JspBounties/Erdos348.lean
```

## Summary of Formalized Problems & Theorems

| File | JSP ID | Erdős # | Lines | Key Verified Theorems |
| :--- | :--- | :--- | ---: | :--- |
| `JspBounties/Erdos348.lean` | `JSP-000290` | #348 | 1,869 | `Erdos348.erdos_348` (Full classification of deletion thresholds $0 \le m < n$ for complete sequences, including Geneson's Central-Interval Theorem) |
| `JspBounties/Erdos503.lean` | `JSP-000404` | #503 | 820 | `erdos_503.variants.R0`, `erdos_503.variants.R1`, `kelly_R2_lower_bound`, `kelly_R3_lower_bound`, `alweiss_construction`, `erdos_503_lower_bound_of_bddAbove` |
| `JspBounties/Erdos835.lean` | `JSP-000691` | #835 | 733 | `property_iff_chromaticNumber`, `indepNum_johnson_le_johnsonBound`, `ma_tang_prop_2_1`, `johnson_chromaticNumber_composite`, `johnson_chromaticNumber_odd`, `johnsonGraph_18_9_chromaticNumber`, `johnson_chromaticNumber_four` ($k=4$ prime case) |
| `JspBounties/Erdos287.lean` | `JSP-000244` | #287 | 557 | `erdos_287_best_possible`, `erdos_287_gap_at_least_two` (Erdős 1932), `erdos_287_prime_conjecture_implies` |
| `JspBounties/Erdos131.lean` | `JSP-000137` | #131 | 418 | `exists_card_eq_F`, `F_small_values`, `F_le_H_nonavg`, `card_le_of_mem_nonDividing`, `F_le_half` ($F(N) \le (N+1)/2$), `propertyP_Icc_top`, `erdos_131_of_pham_zakharov` |
| `JspBounties/Erdos488.lean` | `JSP-000396` | #488 | 397 | `erdos_488_singleton`, `erdos_488_sharpness`, `erdos_488_pair`, `erdos_488_of_two_mem`, `erdos_488_insert_gt_half`, `erdos_488_nonmultiples_false` |
| `JspBounties/Erdos216.lean` | `JSP-000198` | #216 | 374 | `g_zero_eq`, `g_three_eq`, `not_convexIndep_of_fourth_in_hull`, `card_hortonSet`, `horton_top_strictly_above_bottom_secant` (Horton 1983 Observation g) |
| `JspBounties/Erdos365.lean` | `JSP-000301` | #365 | 330 | `golomb_pair`, `erdos_365.parts.i`, `parametric_nonSquare_powerful_family`, `walkerSeq_properties`, `infinite_nonSquare_consecutive_powerful` (Walker 1976 infinite family) |
| `JspBounties/Erdos672.lean` | `JSP-000546` | #672 | 269 | `not_erdos672With_two`, `not_erdos672With_three_two`, `euler_four_ap_identity`, `erdos_672_four_two_of_sq_le`, `four_consecutive_ne_sq`, `erdos_672_four_two_primitive_pythagorean` |
| `JspBounties/Erdos238.lean` | `JSP-000210` / `JSP-000211` | #238 / #240 | 250 | `erdos_238_block_pigeonhole`, `erdos_238_small_c1_of_brun_chebyshev`, `erdos_238_unconditional_of_c2_lt_two`, `single_prime_smooth_gap_ge` |
| `JspBounties/Erdos372.lean` | `JSP-000307` | #371 / #372 | 233 | `jsp_000307_least_decreasing_triple` ($n=13$), `decreasing_quadruple_317`, `infinite_maxPrimeFac_valley`, `infinite_maxPrimeFac_gt_succ`, `infinite_maxPrimeFac_lt_succ` |
| `JspBounties/Erdos575.lean` | `JSP-000465` | #575 | 230 | `card_le_one_of_no_K12_no_2K2`, `matchingGraph_card_and_K12_free`, `starGraph_card_and_2K2_free`, `unique_common_neighbor_of_C4_free`, `common_neighbors_coincide_of_C4_C6_free`, `Z_uv_independent_of_C4_C6_free` |
| `JspBounties/Erdos699.lean` | `JSP-000570` | #699 | 226 | `choose_gcd_gt_one` (Erdős–Szekeres 1978), `erdos_699_of_le_two`, `erdos_699_of_prime_in_interval`, `erdos_699_succ_of_not_prime`, `mem_exceptions_of_erdos_szekeres_strengthening` |
| `JspBounties/Erdos338.lean` | `JSP-000281` | #338 / #339 | 225 | `erdos_338_bateman` (Bateman unrestricted basis theorem), `erdos_339_order_two_contains_all_large_odd`, `erdos_339_order_two_counting_bound` |
| `JspBounties/ErdosGraph.lean` | `JSP-000058` / `509` | #23 / #617 / #628 | 2,739 | `erdos_23.variants.n1`, `erdos_23.variants.n1_tight`, `erdos_617.variants.r2`, `erdos_617.variants.r_eq_3`, `erdos_628.variants.k_5_a_3_b_3` (Brown–Jung 1969), `erdos_628.variants.independence_number_2` (Balogh–Kostochka–Prince–Stiebitz 2009) |
| `JspBounties/Erdos940.lean` | `JSP-000782` | #940 | 217 | `Nat.two_full_iff_exists_sq_mul_cube`, `seven_not_sum_three_powerful` |
| `JspBounties/Erdos302.lean` | `JSP-000253` | #302 | 213 | `erdos_302.variants.lower_half`, `erdos_302.variants.lower_seventeen_thirtyseconds`, `erdos_302.parts.ii` (disproves $f(N) = (1/2+o(1))N$) |
| `JspBounties/Erdos364_366.lean` | `JSP-000300`–`JSP-000302` | #364–#366 | 212 | `erdos_364_weak`, `no_four_consecutive_full`, `erdos_364_mod_thirtysix_barrier`, `erdos_366_mod_eight_barrier` |
| `JspBounties/Erdos602.lean` | `JSP-000489` | #602 | 164 | `erdos_602.variants.disjoint`, `erdos_602.variants.two_sets`, `disjoint_without_infinite_claim.disproof` |
| `JspBounties/Erdos261.lean` | `JSP-000226` | #261 | 162 | `erdos_261.variants.borwein_loring`, `erdos_261.variants.borwein_loring_property`, `erdos_261.parts.i` |
| `JspBounties/Erdos885.lean` | `JSP-000736` | #885 | 162 | `erdos_885.variants.k_eq_2`, `erdos_885.variants.k_eq_3`, `erdos_885.variants.k_eq_4` |
| `JspBounties/Erdos1209.lean` | `JSP-001014` | #1209 | 149 | `erdos_1209.parts.i`, `erdos_1209.parts.ii` (disproves both shift conjectures via Dirichlet's theorem) |
| `JspBounties/Erdos686.lean` | `JSP-000558` | #686 | 123 | `erdos_686.variants.four_two`, `erdos_686.variants.nine`, `erdos_686.variants.non_square` (via Pell's equation) |
| `JspBounties/Erdos949.lean` | `JSP-000789` | #949 | 109 | `erdos_949.variants.sidon` (continuum-sized sum-avoiding subset in the complement of any real Sidon set) |
| `JspBounties/Erdos366.lean` | `JSP-000302` | #366 | 78 | `exists_three_full_then_two_full`, `erdos_366.variants.three_two` |
| `JspBounties/Erdos1063.lean` | `JSP-000881` | #1063 | 68 | `erdos_1063.variants.small_values` ($n_2=4, n_3=6, n_4=9, n_5=12$) |
