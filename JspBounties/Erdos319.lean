/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Erdős Problem 319 (`FormalConjectures/ErdosProblems/319.lean`): Irreducible Signed Unit-Fraction Zero-Sums

*References:*
- [erdosproblems.com/319](https://www.erdosproblems.com/319)
- [Cr01] Croot, III, Ernest S., *On unit fractions with denominators in short intervals*.
  Acta Arith. 99 (2001), 99–114.

This file formalizes complete, zero-`sorry` proofs for `FormalConjectures/ErdosProblems/319.lean`:
1. **Unconditional Upper Bound (`c_nonneg_and_le`, `erdos_319_isBigO`)**:
   For any $N \in \mathbb{N}$, if $c(N)$ is the maximum size of an irreducible signed unit-fraction
   zero-sum $A \subseteq \{1, \ldots, N\}$, then $0 \le c(N) \le N$, and hence
   `c =O[atTop] erdos_319.variants.isTheta.answer`.
2. **Adenwalla's Irreducible Signed Unit-Fraction Construction (`adenwalla_irreducible_of_unit_fraction_sum`)**:
   For any finite set $B \subseteq \{2, \ldots, N\}$ with $\sum_{n \in B} \frac{1}{n} = 1$,
   adjoining $1$ with sign $\delta(1) = -1$ and setting $\delta(n) = +1$ for $n \in B$ yields
   a subset $A = \{1\} \cup B \subseteq \{1, \ldots, N\}$ of cardinality $|B| + 1$ with
   $\sum_{n \in A} \frac{\delta(n)}{n} = 0$ such that **every** non-empty proper subset
   $A' \subsetneq A$ has $\sum_{n \in A'} \frac{\delta(n)}{n} \ne 0$ (strictly positive if $1 \notin A'$,
   strictly negative if $1 \in A'$).
3. **Unconditional Explicit Witnesses (`four_le_c_of_six_le`, `five_le_c_of_fortytwo_le`)**:
   Using $B = \{2, 3, 6\}$ and $B = \{2, 3, 7, 42\}$, proves unconditionally that $c(N) \ge 4$ for
   all $N \ge 6$ and $c(N) \ge 5$ for all $N \ge 42$.
4. **Deduction of `erdos_319.variants.lb` from Croot (`erdos_319_lb_of_croot`) and Complete Proof
   of `erdos_319.variants.isTheta` from `erdos_319.variants.lb` (`erdos_319_isTheta_of_lb`)**:
   Proves that Croot's [Cr01] unit-fraction theorem implies `erdos_319.variants.lb`, and that
   `erdos_319.variants.lb` together with `erdos_319_isBigO` implies
   `c =Θ[atTop] erdos_319.variants.isTheta.answer` (`erdos_319.variants.isTheta`).
-/

open Filter Asymptotics Finset
open scoped Topology Real

namespace Erdos319

/-- The asymptotic growth answer $\Theta(N)$ for Erdős Problem 319. -/
def erdos_319.variants.isTheta.answer : ℕ → ℝ := fun N ↦ (N : ℝ)

/-- The set of cardinalities `(#A : ℝ)` of subsets $A \subseteq \{1, \ldots, N\}$ admitting an
irreducible signed unit-fraction zero-sum. -/
def erdos319Set (N : ℕ) : Set ℝ :=
  { (#A : ℝ) | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 1 N)
    (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
      ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) }

/-!
## Part 1: Unconditional Upper Bound $0 \le c(N) \le N$ and $c(N) = O(N)$
-/

/-- The empty set `∅` always belongs to `erdos319Set N`, witnessing `0 ∈ erdos319Set N`. -/
lemma zero_mem_erdos319Set (N : ℕ) : (0 : ℝ) ∈ erdos319Set N := by
  refine ⟨∅, Finset.empty_subset _, ⟨fun _ => 1, by simp, ?_⟩, by simp⟩
  intro A' hA'
  exfalso
  exact Finset.not_ssubset_empty A' hA'

/-- Every element of `erdos319Set N` lies in $[0, N]$. -/
lemma mem_erdos319Set_bounds {N : ℕ} {x : ℝ} (hx : x ∈ erdos319Set N) :
    0 ≤ x ∧ x ≤ N := by
  rcases hx with ⟨A, hA_sub, _, rfl⟩
  refine ⟨by positivity, ?_⟩
  have hcard : #A ≤ N := by
    calc
      #A ≤ #(Finset.Icc 1 N) := Finset.card_le_card hA_sub
      _ = N := by simp
  exact_mod_cast hcard

/-- If `IsGreatest (erdos319Set N) (c N)` holds, then $0 \le c(N) \le N$. -/
lemma c_nonneg_and_le {N : ℕ} {cN : ℝ} (h : IsGreatest (erdos319Set N) cN) :
    0 ≤ cN ∧ cN ≤ N :=
  mem_erdos319Set_bounds h.1

/-- **Unconditional Upper Bound (`erdos_319_isBigO`)**:
If $c(N)$ is the maximum size of an irreducible signed unit-fraction zero-sum in $\{1, \ldots, N\}$,
then `c =O[atTop] erdos_319.variants.isTheta.answer`. -/
theorem erdos_319_isBigO (c : ℕ → ℝ) (h : ∀ N, IsGreatest (erdos319Set N) (c N)) :
    c =O[atTop] erdos_319.variants.isTheta.answer := by
  refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards with N
  obtain ⟨hc0, hcN⟩ := c_nonneg_and_le (h N)
  simp only [erdos_319.variants.isTheta.answer, Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg hc0, abs_of_nonneg (by positivity)]
  exact hcN

/-!
## Part 2: Adenwalla's Irreducible Signed Unit-Fraction Construction
-/

/-- The sign assignment $\delta(1) = -1$ and $\delta(n) = +1$ for $n \ne 1$. -/
def adenwallaSign (n : ℕ) : ℤˣ :=
  if n = 1 then -1 else 1

/-- **Adenwalla's Irreducible Signed Unit-Fraction Theorem (`adenwalla_irreducible_of_unit_fraction_sum`)**:
Let $B \subseteq \{2, \ldots, N\}$ be a finite set of integers whose reciprocals sum to $1$:
$$\sum_{n \in B} \frac{1}{n} = 1.$$
Then $A = \mathrm{insert}\ 1\ B \subseteq \{1, \ldots, N\}$ has cardinality $|B| + 1$, and with
$\delta = \mathrm{adenwallaSign}$ ($\delta(1) = -1$, $\delta(n) = +1$ for $n \ge 2$), satisfies:
1. $\sum_{n \in A} \frac{\delta(n)}{n} = 0$, and
2. for every non-empty proper subset $A' \subsetneq A$, $\sum_{n \in A'} \frac{\delta(n)}{n} \ne 0$. -/
theorem adenwalla_irreducible_of_unit_fraction_sum {N : ℕ} {B : Finset ℕ}
    (hB_sub : B ⊆ Finset.Icc 2 N) (hB_sum : ∑ n ∈ B, (1 : ℚ) / n = 1) :
    insert 1 B ⊆ Finset.Icc 1 N ∧
      #(insert 1 B) = #B + 1 ∧
      (∑ n ∈ insert 1 B, (adenwallaSign n : ℚ) / n = 0 ∧
        ∀ A' ⊂ insert 1 B, A'.Nonempty → ∑ n ∈ A', (adenwallaSign n : ℚ) / n ≠ 0) := by
  have hB_not_mem_one : 1 ∉ B := by
    intro h1
    have := (Finset.mem_Icc.mp (hB_sub h1)).1
    omega
  have hN_ge_two : 2 ≤ N := by
    have hB_ne : B.Nonempty := by
      by_contra! hemp
      rw [hemp, Finset.sum_empty] at hB_sum
      norm_num at hB_sum
    obtain ⟨b, hb⟩ := hB_ne
    have := Finset.mem_Icc.mp (hB_sub hb)
    omega
  have hB_term_pos : ∀ n ∈ B, (0 : ℚ) < (adenwallaSign n : ℚ) / n := by
    intro n hn
    have hn_ge : 2 ≤ n := (Finset.mem_Icc.mp (hB_sub hn)).1
    have hn_ne : n ≠ 1 := by omega
    simp only [adenwallaSign, if_neg hn_ne, Units.val_one, Int.cast_one]
    have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have h_total_sum : ∑ n ∈ insert 1 B, (adenwallaSign n : ℚ) / n = 0 := by
    rw [Finset.sum_insert hB_not_mem_one]
    have h1_term : (adenwallaSign 1 : ℚ) / (1 : ℕ) = -1 := by
      simp [adenwallaSign]
    have hB_eq : ∑ n ∈ B, (adenwallaSign n : ℚ) / n = ∑ n ∈ B, (1 : ℚ) / n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn_ge : 2 ≤ n := (Finset.mem_Icc.mp (hB_sub hn)).1
      have hn_ne : n ≠ 1 := by omega
      simp [adenwallaSign, hn_ne]
    rw [h1_term, hB_eq, hB_sum]
    ring
  refine ⟨?_, Finset.card_insert_of_notMem hB_not_mem_one, h_total_sum, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxB
    · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · have hxIcc := Finset.mem_Icc.mp (hB_sub hxB)
      exact Finset.mem_Icc.mpr ⟨by omega, hxIcc.2⟩
  · intro A' hA'_ssub hA'_ne
    by_cases h1A' : 1 ∈ A'
    · -- Case `1 ∈ A'`: the complement `(insert 1 B) \ A'` is a nonempty subset of `B`.
      let C := (insert 1 B) \ A'
      have hC_ne : C.Nonempty := Finset.sdiff_nonempty.mpr hA'_ssub.not_subset
      have hC_sub_B : C ⊆ B := by
        intro x hx
        obtain ⟨hx_ins, hx_not⟩ := Finset.mem_sdiff.mp hx
        rcases Finset.mem_insert.mp hx_ins with rfl | hxB
        · exact (hx_not h1A').elim
        · exact hxB
      have hC_pos : 0 < ∑ n ∈ C, (adenwallaSign n : ℚ) / n :=
        Finset.sum_pos (fun n hn => hB_term_pos n (hC_sub_B hn)) hC_ne
      have hsplit : ∑ n ∈ A', (adenwallaSign n : ℚ) / n +
          ∑ n ∈ C, (adenwallaSign n : ℚ) / n =
          ∑ n ∈ insert 1 B, (adenwallaSign n : ℚ) / n := by
        dsimp [C]
        rw [add_comm, Finset.sum_sdiff hA'_ssub.subset]
      rw [h_total_sum] at hsplit
      linarith
    · -- Case `1 ∉ A'`: `A'` is a nonempty subset of `B`, so its sum is strictly positive.
      have hA'_sub_B : A' ⊆ B := by
        intro x hx
        rcases Finset.mem_insert.mp (hA'_ssub.subset hx) with rfl | hxB
        · exact (h1A' hx).elim
        · exact hxB
      have hA'_pos : 0 < ∑ n ∈ A', (adenwallaSign n : ℚ) / n :=
        Finset.sum_pos (fun n hn => hB_term_pos n (hA'_sub_B hn)) hA'_ne
      linarith

/-- Consequently, under the hypotheses of `adenwalla_irreducible_of_unit_fraction_sum`,
`(#B + 1 : ℝ) ∈ erdos319Set N`. -/
lemma card_add_one_mem_erdos319Set_of_unit_fraction_sum {N : ℕ} {B : Finset ℕ}
    (hB_sub : B ⊆ Finset.Icc 2 N) (hB_sum : ∑ n ∈ B, (1 : ℚ) / n = 1) :
    ((#B + 1 : ℕ) : ℝ) ∈ erdos319Set N := by
  obtain ⟨hsub, hcard, hsum, hirr⟩ := adenwalla_irreducible_of_unit_fraction_sum hB_sub hB_sum
  exact ⟨insert 1 B, hsub, ⟨adenwallaSign, hsum, hirr⟩, by exact_mod_cast hcard⟩

/-!
## Part 3: Unconditional Explicit Witnesses ($c(N) \ge 4$ for $N \ge 6$, $c(N) \ge 5$ for $N \ge 42$)
-/

/-- For every $N \ge 6$, $\{1, 2, 3, 6\} \subseteq \{1, \ldots, N\}$ is an irreducible signed
unit-fraction zero-sum of size $4$, so $4 \in \mathrm{erdos319Set}(N)$. -/
theorem four_mem_erdos319Set {N : ℕ} (hN : 6 ≤ N) : (4 : ℝ) ∈ erdos319Set N := by
  let B : Finset ℕ := {2, 3, 6}
  have hB_sub : B ⊆ Finset.Icc 2 N := by
    intro x hx
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]
    rcases hx with rfl | rfl | rfl <;> omega
  have hB_sum : ∑ n ∈ B, (1 : ℚ) / n = 1 := by
    dsimp [B]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  have hmem := card_add_one_mem_erdos319Set_of_unit_fraction_sum hB_sub hB_sum
  have hcard : #B = 3 := by decide
  simpa [hcard] using hmem

/-- For every $N \ge 42$, $\{1, 2, 3, 7, 42\} \subseteq \{1, \ldots, N\}$ is an irreducible signed
unit-fraction zero-sum of size $5$, so $5 \in \mathrm{erdos319Set}(N)$. -/
theorem five_mem_erdos319Set {N : ℕ} (hN : 42 ≤ N) : (5 : ℝ) ∈ erdos319Set N := by
  let B : Finset ℕ := {2, 3, 7, 42}
  have hB_sub : B ⊆ Finset.Icc 2 N := by
    intro x hx
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  have hB_sum : ∑ n ∈ B, (1 : ℚ) / n = 1 := by
    dsimp [B]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  have hmem := card_add_one_mem_erdos319Set_of_unit_fraction_sum hB_sub hB_sum
  have hcard : #B = 4 := by decide
  simpa [hcard] using hmem

/-!
## Part 4: Deduction of `erdos_319.variants.lb` from Croot and Proof of `erdos_319.variants.isTheta`
-/

/-- `erdos319Set N` is bounded above by $N$. -/
lemma bddAbove_erdos319Set (N : ℕ) : BddAbove (erdos319Set N) :=
  ⟨N, fun _ hx => (mem_erdos319Set_bounds hx).2⟩

/-- **Adenwalla's Deduction of `erdos_319.variants.lb` from Croot [Cr01]**:
If for some $o = o(1)$, eventually every $\{2, \ldots, N\}$ contains a subset $B$ of size at least
$(1 - 1/e + o(N))N$ whose reciprocals sum to $1$, then `erdos_319.variants.lb` holds. -/
theorem erdos_319_lb_of_croot
    (hcroot : ∃ (o : ℕ → ℝ), (o =o[atTop] (1 : ℕ → ℝ)) ∧
      ∀ᶠ N : ℕ in atTop, ∃ B : Finset ℕ, B ⊆ Finset.Icc 2 N ∧
        ∑ n ∈ B, (1 : ℚ) / n = 1 ∧ (1 - 1 / rexp 1 + o N) * N ≤ (#B : ℝ)) :
    ∃ (o : ℕ → ℝ), (o =o[atTop] (1 : ℕ → ℝ)) ∧
      ∀ᶠ N in atTop, (1 - 1 / rexp 1 + o N) * N ≤ sSup (erdos319Set N) := by
  obtain ⟨o, ho, hev⟩ := hcroot
  refine ⟨o, ho, ?_⟩
  filter_upwards [hev] with N ⟨B, hB_sub, hB_sum, hB_lb⟩
  have hmem := card_add_one_mem_erdos319Set_of_unit_fraction_sum hB_sub hB_sum
  have hle_sup : ((#B + 1 : ℕ) : ℝ) ≤ sSup (erdos319Set N) :=
    le_csSup (bddAbove_erdos319Set N) hmem
  push_cast at hle_sup
  linarith

/-- Lower bound helper: $1 < \exp(1)$, so $0 < 1 - 1 / \exp(1)$. -/
lemma one_sub_inv_exp_one_pos : 0 < 1 - 1 / rexp 1 := by
  have hexp1 : 1 < rexp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hdiv : 1 / rexp 1 < 1 := (div_lt_one (Real.exp_pos 1)).mpr hexp1
  linarith

/-- **Complete Proof of `erdos_319.variants.isTheta` from `erdos_319.variants.lb`**:
Combining the unconditional upper bound $c(N) \le N$ (`erdos_319_isBigO`) with the lower bound
`erdos_319.variants.lb` proves `c =Θ[atTop] erdos_319.variants.isTheta.answer`. -/
theorem erdos_319_isTheta_of_lb
    (hlb : ∃ (o : ℕ → ℝ), (o =o[atTop] (1 : ℕ → ℝ)) ∧
      ∀ᶠ N in atTop, (1 - 1 / rexp 1 + o N) * N ≤ sSup (erdos319Set N))
    (c : ℕ → ℝ)
    (h : ∀ N, IsGreatest (erdos319Set N) (c N)) :
    c =Θ[atTop] erdos_319.variants.isTheta.answer := by
  refine ⟨erdos_319_isBigO c h, ?_⟩
  obtain ⟨o, ho, hev⟩ := hlb
  set α : ℝ := (1 - 1 / rexp 1) / 2
  have hα : 0 < α := half_pos one_sub_inv_exp_one_pos
  have ho_bound : ∀ᶠ N in atTop, ‖o N‖ ≤ α * ‖(1 : ℕ → ℝ) N‖ :=
    ho.bound hα
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / α, ?_⟩
  filter_upwards [hev, ho_bound] with N hN_lb hN_o
  simp only [Real.norm_eq_abs, Pi.one_apply, abs_one, mul_one] at hN_o
  have ho_ge : -α ≤ o N := (abs_le.mp hN_o).1
  have hcoef : α ≤ 1 - 1 / rexp 1 + o N := by
    dsimp [α] at ho_ge ⊢
    linarith
  have hcsup : sSup (erdos319Set N) = c N := (h N).isLUB.csSup_eq ⟨0, zero_mem_erdos319Set N⟩
  rw [hcsup] at hN_lb
  have hαN : α * (N : ℝ) ≤ c N := by
    calc
      α * (N : ℝ) ≤ (1 - 1 / rexp 1 + o N) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ c N := hN_lb
  obtain ⟨hc0, _⟩ := c_nonneg_and_le (h N)
  simp only [erdos_319.variants.isTheta.answer, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg hc0]
  exact (le_div_iff₀' hα).mpr hαN |>.trans_eq (by ring)

end Erdos319

#print axioms Erdos319.erdos_319_isBigO
#print axioms Erdos319.adenwalla_irreducible_of_unit_fraction_sum
#print axioms Erdos319.four_mem_erdos319Set
#print axioms Erdos319.five_mem_erdos319Set
#print axioms Erdos319.erdos_319_lb_of_croot
#print axioms Erdos319.erdos_319_isTheta_of_lb
