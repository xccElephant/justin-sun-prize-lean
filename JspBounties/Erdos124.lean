/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 124 (`JSP-000131`): Complete Sequences of Sums of Distinct Powers

*References:*
- [erdosproblems.com/124](https://www.erdosproblems.com/124) (`JSP-000131`)
- [BEGL96] Burr, S. A., Erdős, P., Graham, R. L., and Li, W. Wen-Ching,
  *Complete sequences of sets of integer powers*. Acta Arith. 77 (1996), 133–138.
- [Er97] Erdős, P., *Problems in number theory*. New Zealand J. Math. 26 (1997), 155–160.

## Mathematical Summary

For an integer base $d \ge 3$ and minimum exponent $k \in \mathbb{N}$, let
`sumsOfDistinctPowers d k` denote the set of integers that can be written as a sum of distinct
powers $d^i$ with $i \ge k$ (i.e., numbers in base $d$ using only digits $\{0, 1\}$ and divisible
by $d^k$).

This file proves the complete characterization for the $k = 0$ Erdős Problem 124 and its
necessity theorems in Lean 4 (`v4.33.1`) with zero `sorry`:

1. **Core Structural Theory (`sumsOfDistinctPowers`)**:
   - Antitonicity in $k$ (`sumsOfDistinctPowers_anti`), sumset inclusion
     (`sum_sumsOfDistinctPowers_subset_zero`), $k = 0 \leftrightarrow k = 1$ digit-splitting
     decomposition (`sumsOfDistinctPowers_zero_eq`), and exact divisibility by $d^k$
     (`pow_dvd_of_mem_sumsOfDistinctPowers`).
2. **Brown's Finset Completeness Criterion (`subset_sum_complete`)**:
   - A tie-free Finset induction theorem showing that if every element $a \in I$ of a finite
     weighted set satisfies $w(a) \le 1 + \sum_{x \in I, w(x) < w(a)} w(x)$, then every integer
     $0 \le n \le \sum_{x \in I} w(x)$ is a subset sum.
3. **Strong Solution of `erdos124.zero` (`erdos124.zero_all`, `erdos124.zero`)**:
   - Proves that if $\forall d \in D, 3 \le d$ and $1 \le \sum_{d \in D} (d - 1)^{-1}$, then
     **every** natural number $n \ge 0$ belongs to $\sum_{d \in D} \mathrm{sumsOfDistinctPowers}\ d\ 0$,
     yielding `erdos124.zero` as an immediate corollary.
4. **Pomerance's Converse (`exists_simultaneous_power_window`, `erdos124.converse`, `erdos124.converse_of_k`)**:
   - Proves via a single-pass Dirichlet box principle on $\alpha_d = S / \ln d$ that for any
     $E > 1$, there exist arbitrarily large integers $n$ simultaneously satisfying
     $n < d^{k_d} \le E n$ for all $d \in D$.
   - Deduces Pomerance's converse `erdos124.converse` (and its generalization `erdos124.converse_of_k`
     for arbitrary $k \in \mathbb{N}$) and the full equivalences `erdos124.eventually_iff_le_sum`
     and `erdos124.forall_iff_le_sum`.
-/

open Filter Set
open scoped BigOperators Pointwise

namespace Erdos124

/-!
## Part 1: Core Definitions and Structural Lemmas
-/

/-- The set of integers which are the sum of distinct powers `d ^ i` with `i ≥ k`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

/-- `0` belongs to `sumsOfDistinctPowers d k` for every `d` and `k`. -/
theorem zero_mem_sumsOfDistinctPowers (d k : ℕ) : 0 ∈ sumsOfDistinctPowers d k :=
  ⟨∅, by simp, by simp⟩

/-- Any single power `d ^ i` with `k ≤ i` belongs to `sumsOfDistinctPowers d k`. -/
theorem pow_mem_sumsOfDistinctPowers {d k i : ℕ} (hi : k ≤ i) :
    d ^ i ∈ sumsOfDistinctPowers d k :=
  ⟨{i}, by simp [hi], by simp⟩

/-- `sumsOfDistinctPowers d k` is antitone in the minimum exponent `k`. -/
theorem sumsOfDistinctPowers_anti {d k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    sumsOfDistinctPowers d k₂ ⊆ sumsOfDistinctPowers d k₁ := by
  rintro x ⟨s, hs, rfl⟩
  exact ⟨s, fun i hi => le_trans hk (hs i hi), rfl⟩

/-- `0` belongs to the pointwise sum `∑ d ∈ D, sumsOfDistinctPowers d k`. -/
theorem zero_mem_sum_sumsOfDistinctPowers (D : Finset ℕ) (k : ℕ) :
    0 ∈ ∑ d ∈ D, sumsOfDistinctPowers d k := by
  rw [Set.mem_finsetSum]
  exact ⟨fun _ => 0, fun _ => zero_mem_sumsOfDistinctPowers _ _, by simp⟩

/-- Every element of `sumsOfDistinctPowers d k` is divisible by `d ^ k`. -/
theorem pow_dvd_of_mem_sumsOfDistinctPowers {d k x : ℕ}
    (hx : x ∈ sumsOfDistinctPowers d k) : d ^ k ∣ x := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine Finset.dvd_sum (fun i hi => ?_)
  exact pow_dvd_pow d (hs i hi)

/-- Pointwise sum inclusion: for any `k`, `∑ d ∈ D, sumsOfDistinctPowers d k` is contained in
`∑ d ∈ D, sumsOfDistinctPowers d 0`. -/
theorem sum_sumsOfDistinctPowers_subset_zero (D : Finset ℕ) (k : ℕ) :
    (∑ d ∈ D, sumsOfDistinctPowers d k) ⊆ ∑ d ∈ D, sumsOfDistinctPowers d 0 := by
  intro x hx
  rw [Set.mem_finsetSum] at hx ⊢
  obtain ⟨g, hg, rfl⟩ := hx
  exact ⟨g, fun hd => sumsOfDistinctPowers_anti (Nat.zero_le k) (hg hd), rfl⟩

/-- Every element of `sumsOfDistinctPowers d 0` decomposes as `c + y` with `c ∈ {0, 1}`
and `y ∈ sumsOfDistinctPowers d 1`. -/
theorem sumsOfDistinctPowers_zero_eq (d : ℕ) :
    sumsOfDistinctPowers d 0 = ({0, 1} : Set ℕ) + sumsOfDistinctPowers d 1 := by
  ext x
  rw [Set.mem_add]
  constructor
  · rintro ⟨s, -, rfl⟩
    by_cases h0 : 0 ∈ s
    · refine ⟨1, by simp, ∑ i ∈ s.erase 0, d ^ i, ⟨s.erase 0, ?_, rfl⟩, ?_⟩
      · intro i hi
        have hne : i ≠ 0 := (Finset.mem_erase.mp hi).1
        omega
      · have h := Finset.add_sum_erase s (fun i => d ^ i) h0
        simpa using h
    · refine ⟨0, by simp, ∑ i ∈ s, d ^ i, ⟨s, ?_, rfl⟩, by simp⟩
      intro i hi
      have hne : i ≠ 0 := fun h => h0 (h ▸ hi)
      omega
  · rintro ⟨c, hc, y, ⟨s, hs, rfl⟩, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨s, fun _ _ => Nat.zero_le _, by simp⟩
    · have h0 : 0 ∉ s := fun h => by have := hs 0 h; omega
      refine ⟨insert 0 s, fun _ _ => Nat.zero_le _, ?_⟩
      rw [Finset.sum_insert h0, pow_zero]

/-!
## Part 2: Brown's Completeness Criterion for Finite Weight Systems
-/

/-- **Brown's Completeness Criterion (Finset form)**:
If a finite set `I` with weight function `w : α → ℕ` satisfies
`w a ≤ 1 + ∑ x ∈ I.filter (fun x => w x < w a), w x` for every `a ∈ I`,
then every natural number `n ≤ ∑ x ∈ I, w x` is the weight sum of some subset `J ⊆ I`. -/
theorem subset_sum_complete {α : Type*} [DecidableEq α] (w : α → ℕ) :
    ∀ (k : ℕ) (I : Finset α), I.card = k →
      (∀ a ∈ I, w a ≤ 1 + ∑ x ∈ I.filter (fun x => w x < w a), w x) →
      ∀ n ≤ ∑ x ∈ I, w x, ∃ J ⊆ I, ∑ x ∈ J, w x = n
  | 0, I, hcard, _, n, hn => by
    rw [Finset.card_eq_zero.mp hcard] at hn ⊢
    simp only [Finset.sum_empty, nonpos_iff_eq_zero] at hn
    subst hn
    exact ⟨∅, Finset.Subset.refl _, by simp⟩
  | k + 1, I, hcard, hbrown, n, hn => by
    have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, hmax⟩ := I.exists_max_image w hIne
    let I' := I.erase a
    have hI'card : I'.card = k := by
      have := Finset.card_erase_add_one ha
      dsimp [I']
      omega
    have hsum_I : ∑ x ∈ I, w x = w a + ∑ x ∈ I', w x :=
      (Finset.add_sum_erase I w ha).symm
    have hfilter_eq : ∀ b ∈ I',
        I'.filter (fun x => w x < w b) = I.filter (fun x => w x < w b) := by
      intro b hb
      ext x
      simp only [I', Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hxI⟩, hlt⟩
        exact ⟨hxI, hlt⟩
      · rintro ⟨hxI, hlt⟩
        refine ⟨⟨?_, hxI⟩, hlt⟩
        rintro rfl
        have hba : w b ≤ w x := hmax b (Finset.mem_of_mem_erase hb)
        omega
    have hI'brown : ∀ b ∈ I', w b ≤ 1 + ∑ x ∈ I'.filter (fun x => w x < w b), w x := by
      intro b hb
      rw [hfilter_eq b hb]
      exact hbrown b (Finset.mem_of_mem_erase hb)
    have hsub_a : I.filter (fun x => w x < w a) ⊆ I' := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      exact Finset.mem_erase.mpr ⟨fun h => by subst h; omega, hx.1⟩
    have hwa_le : w a ≤ 1 + ∑ x ∈ I', w x := by
      have h1 := hbrown a ha
      have h2 : ∑ x ∈ I.filter (fun x => w x < w a), w x ≤ ∑ x ∈ I', w x :=
        Finset.sum_le_sum_of_subset hsub_a
      omega
    by_cases hn_le : n ≤ ∑ x ∈ I', w x
    · obtain ⟨J, hJI', hJsum⟩ := subset_sum_complete w k I' hI'card hI'brown n hn_le
      exact ⟨J, hJI'.trans (Finset.erase_subset a I), hJsum⟩
    · have hwa_n : w a ≤ n := by omega
      have hsub_le : n - w a ≤ ∑ x ∈ I', w x := by omega
      obtain ⟨J', hJ'I', hJ'sum⟩ :=
        subset_sum_complete w k I' hI'card hI'brown (n - w a) hsub_le
      have haJ' : a ∉ J' := fun h => (Finset.mem_erase.mp (hJ'I' h)).1 rfl
      refine ⟨insert a J', Finset.insert_subset ha (hJ'I'.trans (Finset.erase_subset a I)), ?_⟩
      rw [Finset.sum_insert haJ', hJ'sum]
      omega

/-!
## Part 3: Proof of `erdos124.zero_all` and `erdos124.zero`
-/

/-- Lower bound for the sum of powers strictly less than `q`:
if `∀ d ∈ D, 3 ≤ d` and `1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹`, then for every `q ≥ 1` with `q - 1 ≤ n`,
the sum of `d ^ i` over all pairs `(d, i) ∈ D ×ˢ range (n + 1)` with `d ^ i ≤ n` and `d ^ i < q`
is at least `q - 1`. -/
lemma pred_le_sum_powers_lt {D : Finset ℕ} (hD : ∀ d ∈ D, 3 ≤ d)
    (hsum : 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹) {n q : ℕ} (hq1 : 1 ≤ q) (hqn : q - 1 ≤ n) :
    q - 1 ≤ ∑ p ∈ ((D ×ˢ Finset.range (n + 1)).filter (fun p => p.1 ^ p.2 ≤ n)).filter
      (fun p => p.1 ^ p.2 < q), p.1 ^ p.2 := by
  classical
  have hex : ∀ d : ℕ, 3 ≤ d → ∃ k : ℕ, q ≤ d ^ k := fun d hd =>
    ⟨q, (Nat.lt_pow_self (by omega : 1 < d)).le⟩
  let k : ℕ → ℕ := fun d => if hd : 3 ≤ d then Nat.find (hex d hd) else 0
  have hk_ge : ∀ d ∈ D, q ≤ d ^ k d := by
    intro d hd
    have hd3 := hD d hd
    dsimp [k]
    rw [dif_pos hd3]
    exact Nat.find_spec (hex d hd3)
  have hk_lt : ∀ d ∈ D, ∀ i < k d, d ^ i < q := by
    intro d hd i hi
    have hd3 := hD d hd
    dsimp [k] at hi
    rw [dif_pos hd3] at hi
    exact Nat.lt_of_not_ge (Nat.find_min (hex d hd3) hi)
  have hfibre_le : ∀ d ∈ D,
      ∑ i ∈ Finset.range (k d), d ^ i ≤
        ∑ i ∈ (Finset.range (n + 1)).filter (fun i => d ^ i ≤ n ∧ d ^ i < q), d ^ i := by
    intro d hd
    apply Finset.sum_le_sum_of_subset
    intro i hi
    have hik : i < k d := Finset.mem_range.mp hi
    have hpow_lt : d ^ i < q := hk_lt d hd i hik
    have hpow_le : d ^ i ≤ n := by omega
    have hd3 : 3 ≤ d := hD d hd
    have hi_lt_pow : i < d ^ i := Nat.lt_pow_self (by omega : 1 < d)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpow_le, hpow_lt⟩
  have hprod_eq :
      ∑ p ∈ ((D ×ˢ Finset.range (n + 1)).filter (fun p => p.1 ^ p.2 ≤ n)).filter
          (fun p => p.1 ^ p.2 < q), p.1 ^ p.2 =
        ∑ d ∈ D, ∑ i ∈ (Finset.range (n + 1)).filter (fun i => d ^ i ≤ n ∧ d ^ i < q), d ^ i := by
    rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_filter]
  have hsum_ge :
      ∑ d ∈ D, ∑ i ∈ Finset.range (k d), d ^ i ≤
        ∑ p ∈ ((D ×ˢ Finset.range (n + 1)).filter (fun p => p.1 ^ p.2 ≤ n)).filter
          (fun p => p.1 ^ p.2 < q), p.1 ^ p.2 := by
    rw [hprod_eq]
    exact Finset.sum_le_sum hfibre_le
  have hrat_term : ∀ d ∈ D,
      ((q - 1 : ℕ) : ℚ) * (d - 1 : ℚ)⁻¹ ≤ (∑ i ∈ Finset.range (k d), d ^ i : ℕ) := by
    intro d hd
    have hd3 : 3 ≤ d := hD d hd
    have hd1_pos : (0 : ℚ) < (d : ℚ) - 1 := by
      have : (3 : ℚ) ≤ d := by exact_mod_cast hd3
      linarith
    have hgeom : ((∑ i ∈ Finset.range (k d), d ^ i : ℕ) : ℚ) =
        ((d : ℚ) ^ k d - 1) / ((d : ℚ) - 1) := by
      push_cast
      exact geom_sum_eq (by exact_mod_cast (by omega : d ≠ 1)) (k d)
    rw [hgeom, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hd1_pos.le)
    have hq_le : (q : ℚ) ≤ (d : ℚ) ^ k d := by exact_mod_cast hk_ge d hd
    have hq_sub : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := Nat.cast_sub hq1
    linarith
  have hrat_sum :
      ((q - 1 : ℕ) : ℚ) ≤ ((∑ d ∈ D, ∑ i ∈ Finset.range (k d), d ^ i : ℕ) : ℚ) := by
    calc
      ((q - 1 : ℕ) : ℚ) = ((q - 1 : ℕ) : ℚ) * 1 := (mul_one _).symm
      _ ≤ ((q - 1 : ℕ) : ℚ) * ∑ d ∈ D, (d - 1 : ℚ)⁻¹ :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
      _ = ∑ d ∈ D, ((q - 1 : ℕ) : ℚ) * (d - 1 : ℚ)⁻¹ := Finset.mul_sum _ _ _
      _ ≤ ∑ d ∈ D, ((∑ i ∈ Finset.range (k d), d ^ i : ℕ) : ℚ) := Finset.sum_le_sum hrat_term
      _ = ((∑ d ∈ D, ∑ i ∈ Finset.range (k d), d ^ i : ℕ) : ℚ) := by push_cast; rfl
  have hnat_sum : q - 1 ≤ ∑ d ∈ D, ∑ i ∈ Finset.range (k d), d ^ i := by
    exact_mod_cast hrat_sum
  exact le_trans hnat_sum hsum_ge

/-- **Strong form of Erdős Problem 124 (`k = 0`)**:
Every natural number `n ≥ 0` (not merely all sufficiently large `n`) belongs to
`∑ d ∈ D, sumsOfDistinctPowers d 0` whenever `∀ d ∈ D, 3 ≤ d` and
`1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹`. -/
theorem erdos124.zero_all (D : Finset ℕ) (hD : ∀ d ∈ D, 3 ≤ d)
    (hsum : 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹) (n : ℕ) :
    n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0 := by
  classical
  let U : Finset (ℕ × ℕ) := D ×ˢ Finset.range (n + 1)
  let w : ℕ × ℕ → ℕ := fun p => p.1 ^ p.2
  let I : Finset (ℕ × ℕ) := U.filter (fun p => w p ≤ n)
  have hbrown : ∀ a ∈ I, w a ≤ 1 + ∑ x ∈ I.filter (fun x => w x < w a), w x := by
    intro a ha
    have haU : a ∈ D ×ˢ Finset.range (n + 1) := (Finset.mem_filter.mp ha).1
    have han : w a ≤ n := (Finset.mem_filter.mp ha).2
    have haD : a.1 ∈ D := (Finset.mem_product.mp haU).1
    have hd3 : 3 ≤ a.1 := hD a.1 haD
    have hwa_pos : 1 ≤ w a := Nat.one_le_pow a.2 a.1 (by omega)
    have hle : w a - 1 ≤ ∑ x ∈ I.filter (fun x => w x < w a), w x :=
      pred_le_sum_powers_lt hD hsum hwa_pos (by omega : w a - 1 ≤ n)
    omega
  have hn_le_sum : n ≤ ∑ x ∈ I, w x := by
    have hle : (n + 1) - 1 ≤ ∑ x ∈ I.filter (fun p => w p < n + 1), w x :=
      pred_le_sum_powers_lt hD hsum (Nat.le_add_left 1 n) (le_refl n)
    have hsub : I.filter (fun p => w p < n + 1) ⊆ I := Finset.filter_subset _ _
    have hsum_le : ∑ x ∈ I.filter (fun p => w p < n + 1), w x ≤ ∑ x ∈ I, w x :=
      Finset.sum_le_sum_of_subset hsub
    omega
  obtain ⟨J, hJI, hJsum⟩ := subset_sum_complete w I.card I rfl hbrown n hn_le_sum
  have hJU : J ⊆ D ×ˢ Finset.range (n + 1) := hJI.trans (Finset.filter_subset _ _)
  rw [Set.mem_finsetSum]
  refine ⟨fun d => ∑ i ∈ (Finset.range (n + 1)).filter (fun i => (d, i) ∈ J), d ^ i, ?_, ?_⟩
  · intro d _
    exact ⟨(Finset.range (n + 1)).filter (fun i => (d, i) ∈ J), fun _ _ => Nat.zero_le _, rfl⟩
  · have hprod :
        (∑ d ∈ D, ∑ i ∈ (Finset.range (n + 1)).filter (fun i => (d, i) ∈ J), d ^ i) =
          ∑ p ∈ J, w p := by
      calc
        (∑ d ∈ D, ∑ i ∈ (Finset.range (n + 1)).filter (fun i => (d, i) ∈ J), d ^ i) =
            ∑ d ∈ D, ∑ i ∈ Finset.range (n + 1), if (d, i) ∈ J then w (d, i) else 0 := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.sum_filter]
        _ = ∑ p ∈ D ×ˢ Finset.range (n + 1), if p ∈ J then w p else 0 :=
          (Finset.sum_product D (Finset.range (n + 1)) (fun p => if p ∈ J then w p else 0)).symm
        _ = ∑ p ∈ (D ×ˢ Finset.range (n + 1)).filter (fun p => p ∈ J), w p :=
          (Finset.sum_filter _ _).symm
        _ = ∑ p ∈ J, w p := by
          congr 1
          ext p
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hJU h, h⟩⟩
    rw [hprod, hJsum]

/-- **Erdős Problem 124 (`k = 0`)**:
If `∀ d ∈ D, 3 ≤ d` and `1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹`, then all sufficiently large integers belong
to `∑ d ∈ D, sumsOfDistinctPowers d 0`. -/
theorem erdos124.zero :
    ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ →
      ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0 := by
  intro D hD hsum
  exact Filter.Eventually.of_forall (erdos124.zero_all D hD hsum)

/-!
## Part 4: Pomerance's Converse (`erdos124.converse`) and Complete Characterization
-/

/-- If two nonnegative reals `a, b` have the same natural floor after scaling by `N > 0`,
they differ by less than `1 / N`. -/
lemma abs_sub_lt_one_div_of_floor_mul_eq {a b : ℝ} {N : ℕ} (hN : 0 < N)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (h : ⌊a * N⌋₊ = ⌊b * N⌋₊) : |a - b| < 1 / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hab1 : a * N < b * N + 1 := by
    have e := Nat.lt_floor_add_one (a * N)
    rw [h] at e
    have e2 := Nat.floor_le (mul_nonneg hb0 hNr.le)
    linarith
  have hab2 : b * N < a * N + 1 := by
    have e := Nat.lt_floor_add_one (b * N)
    rw [← h] at e
    have e2 := Nat.floor_le (mul_nonneg ha0 hNr.le)
    linarith
  have habs : |a * N - b * N| < 1 := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hfactor : a * N - b * N = (a - b) * N := (sub_mul a b N).symm
  rw [hfactor, abs_mul, abs_of_pos hNr] at habs
  rwa [lt_div_iff₀ hNr]

/-- **Simultaneous Power Window Lemma (via Dirichlet's Box Principle)**:
For any finite set `D` of bases `d ≥ 3`, any `E > 1`, and any threshold `N₀`, there exists a
positive integer `n ≥ N₀` such that for every `d ∈ D`, some power `d ^ k` lies in the window
`n < d ^ k ≤ E * n`. -/
theorem exists_simultaneous_power_window {D : Finset ℕ} (hD : ∀ d ∈ D, 3 ≤ d)
    {E : ℝ} (hE : 1 < E) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ 1 ≤ n ∧ ∀ d ∈ D, ∃ k : ℕ, n < d ^ k ∧ ((d ^ k : ℕ) : ℝ) ≤ E * n := by
  classical
  let B : ℝ := 1 + ∑ d ∈ D, Real.log (d : ℝ)
  have hlog_pos : ∀ d ∈ D, 0 < Real.log (d : ℝ) := by
    intro d hd
    have hd3 := hD d hd
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hlog_lt_B : ∀ d ∈ D, Real.log (d : ℝ) < B := by
    intro d hd
    have hle : Real.log (d : ℝ) ≤ ∑ x ∈ D, Real.log (x : ℝ) :=
      Finset.single_le_sum (fun x hx => (hlog_pos x hx).le) hd
    dsimp [B]
    linarith
  have hB1 : 1 ≤ B := by
    have hsum_nn : 0 ≤ ∑ d ∈ D, Real.log (d : ℝ) :=
      Finset.sum_nonneg (fun d hd => (hlog_pos d hd).le)
    dsimp [B]
    linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  let E₁ : ℝ := (E + 1) / 2
  have hE₁_gt : 1 < E₁ := by dsimp [E₁]; linarith
  have hE₁_lt : E₁ < E := by dsimp [E₁]; linarith
  have hE₁_pos : 0 < E₁ := lt_trans zero_lt_one hE₁_gt
  have hlogE₁ : 0 < Real.log E₁ := Real.log_pos hE₁_gt
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (max 1 (2 * B / Real.log E₁))
  have hN1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN_gt
  have hNpos : 0 < N := by exact_mod_cast (lt_trans zero_lt_one hN1)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have h2BN : 2 * B / N < Real.log E₁ := by
    have hlt : 2 * B / Real.log E₁ < N := lt_of_le_of_lt (le_max_right _ _) hN_gt
    rw [div_lt_iff₀ hlogE₁] at hlt
    rw [div_lt_iff₀ hNr]
    linarith
  have hexp_2BN : Real.exp (2 * B / N) ≤ E₁ := by
    rw [← Real.exp_log hE₁_pos]
    exact (Real.exp_lt_exp.mpr h2BN).le
  obtain ⟨M, hM_gt⟩ := exists_nat_gt (max (N₀ : ℝ) (E₁ / (E - E₁)) + 1)
  have hM_N₀_r : (N₀ : ℝ) + 1 < M := by
    have := le_max_left (N₀ : ℝ) (E₁ / (E - E₁))
    linarith
  have hM_N₀ : N₀ ≤ M := by
    have : (N₀ : ℝ) < M := by linarith
    exact (Nat.cast_lt.mp this).le
  have hM1_r : (1 : ℝ) < M := by
    have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    linarith
  have hM1 : 1 ≤ M := by
    have : (0 : ℝ) < M := lt_trans zero_lt_one hM1_r
    have : 0 < M := Nat.cast_pos.mp this
    omega
  have hM_E : E₁ / (E - E₁) < M := by
    have := le_max_right (N₀ : ℝ) (E₁ / (E - E₁))
    linarith
  have hM_E_mul : E₁ < M * (E - E₁) := (div_lt_iff₀ (by linarith)).mp hM_E
  let S : ℝ := Real.log M + B
  have hlogM_pos : 0 < Real.log M := Real.log_pos hM1_r
  have hS_pos : 0 < S := add_pos hlogM_pos hBpos
  let α : D → ℝ := fun d => S / Real.log (d.1 : ℝ)
  have hα_pos : ∀ d : D, 0 < α d := fun d => div_pos hS_pos (hlog_pos d.1 d.2)
  have hbox : ∀ (j : Fin (N ^ Fintype.card D + 1)) (d : D),
      ⌊Int.fract ((j : ℕ) * α d) * N⌋₊ < N := by
    intro j d
    have h0 : (0 : ℝ) ≤ Int.fract ((j : ℕ) * α d) * (N : ℝ) :=
      mul_nonneg (Int.fract_nonneg _) hNr.le
    rw [Nat.floor_lt h0]
    calc
      Int.fract ((j : ℕ) * α d) * (N : ℝ) < 1 * (N : ℝ) :=
        mul_lt_mul_of_pos_right (Int.fract_lt_one _) hNr
      _ = (N : ℝ) := one_mul _
  let b : Fin (N ^ Fintype.card D + 1) → D → Fin N :=
    fun j d => ⟨⌊Int.fract ((j : ℕ) * α d) * N⌋₊, hbox j d⟩
  have hcard : Fintype.card (D → Fin N) < Fintype.card (Fin (N ^ Fintype.card D + 1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    exact Nat.lt_succ_self _
  obtain ⟨j, j', hne, hbb⟩ := Fintype.exists_ne_map_eq_of_card_lt b hcard
  obtain ⟨j₁, j₂, h12, hbb12⟩ :
      ∃ j₁ j₂ : Fin (N ^ Fintype.card D + 1), j₁ < j₂ ∧ b j₁ = b j₂ := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨j, j', h, hbb⟩
    · exact ⟨j', j, h, hbb.symm⟩
  have h12v : (j₁ : ℕ) < (j₂ : ℕ) := Fin.lt_def.mp h12
  let m : ℕ := (j₂ : ℕ) - (j₁ : ℕ)
  have hm1 : 1 ≤ m := by omega
  have hm1_r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  let Y : ℝ := (m : ℝ) * S - B / N
  have hY_ge_logM : Real.log M ≤ Y := by
    have hmS : S ≤ (m : ℝ) * S := le_mul_of_one_le_left hS_pos.le hm1_r
    have hBN : B / N ≤ B := div_le_self hBpos.le hN1.le
    dsimp [Y, S] at hmS ⊢
    linarith
  let n : ℕ := ⌊Real.exp Y⌋₊
  have hM_le_expY : (M : ℝ) ≤ Real.exp Y := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < M)]
    exact Real.exp_le_exp.mpr hY_ge_logM
  have hM_le_n : M ≤ n := Nat.le_floor hM_le_expY
  have hn_le_expY : (n : ℝ) ≤ Real.exp Y := Nat.floor_le (Real.exp_pos Y).le
  have hexpY_lt_n1 : Real.exp Y < (n : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp Y)
  refine ⟨n, le_trans hM_N₀ hM_le_n, le_trans hM1 hM_le_n, ?_⟩
  intro d hd
  let d' : D := ⟨d, hd⟩
  have hj_le : ((j₁ : ℕ) : ℝ) * α d' ≤ ((j₂ : ℕ) : ℝ) * α d' :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h12v.le) (hα_pos d').le
  have hfloor_le : ⌊((j₁ : ℕ) : ℝ) * α d'⌋ ≤ ⌊((j₂ : ℕ) : ℝ) * α d'⌋ :=
    Int.floor_mono hj_le
  let kz : ℤ := ⌊((j₂ : ℕ) : ℝ) * α d'⌋ - ⌊((j₁ : ℕ) : ℝ) * α d'⌋
  have hkz_nn : 0 ≤ kz := sub_nonneg.mpr hfloor_le
  let k : ℕ := kz.toNat
  have hk_cast : (k : ℝ) = (kz : ℝ) := by
    have : (k : ℤ) = kz := Int.toNat_of_nonneg hkz_nn
    exact_mod_cast this
  have hfloor_eq : ⌊Int.fract ((j₁ : ℕ) * α d') * N⌋₊ = ⌊Int.fract ((j₂ : ℕ) * α d') * N⌋₊ :=
    congrArg Fin.val (congrFun hbb12 d')
  have hdiff_fract :
      (m : ℝ) * α d' - (k : ℝ) =
        Int.fract (((j₂ : ℕ) : ℝ) * α d') - Int.fract (((j₁ : ℕ) : ℝ) * α d') := by
    have hmc : (m : ℝ) = ((j₂ : ℕ) : ℝ) - ((j₁ : ℕ) : ℝ) := Nat.cast_sub h12v.le
    rw [hk_cast]
    dsimp [kz]
    rw [hmc, Int.cast_sub, sub_mul, ← Int.self_sub_floor (((j₂ : ℕ) : ℝ) * α d'),
      ← Int.self_sub_floor (((j₁ : ℕ) : ℝ) * α d')]
    ring
  have habs_α : |(m : ℝ) * α d' - (k : ℝ)| < 1 / N := by
    rw [hdiff_fract]
    exact abs_sub_lt_one_div_of_floor_mul_eq hNpos (Int.fract_nonneg _) (Int.fract_nonneg _)
      hfloor_eq.symm
  have hlogd : 0 < Real.log (d : ℝ) := hlog_pos d hd
  have hα_mul : α d' * Real.log (d : ℝ) = S := div_mul_cancel₀ S hlogd.ne'
  have habs_S : |(m : ℝ) * S - (k : ℝ) * Real.log (d : ℝ)| < B / N := by
    have hrew : (m : ℝ) * S - (k : ℝ) * Real.log (d : ℝ) =
        ((m : ℝ) * α d' - (k : ℝ)) * Real.log (d : ℝ) := by
      rw [sub_mul, mul_assoc, hα_mul]
    rw [hrew, abs_mul, abs_of_pos hlogd]
    calc
      |(m : ℝ) * α d' - (k : ℝ)| * Real.log (d : ℝ) < (1 / N) * B :=
        mul_lt_mul'' habs_α (hlog_lt_B d hd) (abs_nonneg _) hlogd.le
      _ = B / N := by ring
  have hbounds := abs_sub_lt_iff.mp habs_S
  have hY_lt : Y < (k : ℝ) * Real.log (d : ℝ) := by
    dsimp [Y]
    linarith [hbounds.1]
  have hk_lt_Y : (k : ℝ) * Real.log (d : ℝ) < Y + 2 * B / N := by
    have h2div : 2 * B / (N : ℝ) = 2 * (B / (N : ℝ)) := by ring
    dsimp [Y]
    linarith [hbounds.2, h2div]
  have hd_pos : (0 : ℝ) < d := by
    have := hD d hd
    exact_mod_cast (by omega : 0 < d)
  have hexp_k : Real.exp ((k : ℝ) * Real.log (d : ℝ)) = ((d ^ k : ℕ) : ℝ) := by
    rw [Real.exp_nat_mul, Real.exp_log hd_pos, Nat.cast_pow]
  refine ⟨k, ?_, ?_⟩
  · have hlt_r : (n : ℝ) < ((d ^ k : ℕ) : ℝ) := by
      rw [← hexp_k]
      exact lt_of_le_of_lt hn_le_expY (Real.exp_lt_exp.mpr hY_lt)
    exact Nat.cast_lt.mp hlt_r
  · have hM_le_n_r : (M : ℝ) ≤ n := by exact_mod_cast hM_le_n
    have hn1_E₁ : ((n : ℝ) + 1) * E₁ ≤ E * (n : ℝ) := by
      have : (M : ℝ) * (E - E₁) ≤ (n : ℝ) * (E - E₁) :=
        mul_le_mul_of_nonneg_right hM_le_n_r (by linarith)
      linarith
    calc
      ((d ^ k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log (d : ℝ)) := hexp_k.symm
      _ ≤ Real.exp (Y + 2 * B / N) := (Real.exp_lt_exp.mpr hk_lt_Y).le
      _ = Real.exp Y * Real.exp (2 * B / N) := Real.exp_add Y (2 * B / N)
      _ ≤ ((n : ℝ) + 1) * E₁ :=
        mul_le_mul hexpY_lt_n1.le hexp_2BN (Real.exp_pos _).le (by positivity)
      _ ≤ E * (n : ℝ) := hn1_E₁

/-- Geometric upper bound on elements of `sumsOfDistinctPowers d 0`:
if `2 ≤ d`, `a ∈ sumsOfDistinctPowers d 0`, and `a < d ^ k`, then every exponent `i ∈ s`
satisfies `i < k`, so `(a : ℝ) ≤ ((d : ℝ) ^ k - 1) / ((d : ℝ) - 1)`. -/
theorem sumsOfDistinctPowers_le_of_lt_pow {d k a : ℕ} (hd : 2 ≤ d)
    (ha : a ∈ sumsOfDistinctPowers d 0) (hlt : a < d ^ k) :
    (a : ℝ) ≤ ((d : ℝ) ^ k - 1) / ((d : ℝ) - 1) := by
  obtain ⟨s, -, rfl⟩ := ha
  have hsub : s ⊆ Finset.range k := by
    intro i hi
    have h1 : d ^ i ≤ ∑ j ∈ s, d ^ j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
    have h2 : d ^ i < d ^ k := lt_of_le_of_lt h1 hlt
    exact Finset.mem_range.mpr ((Nat.pow_lt_pow_iff_right (by omega : 1 < d)).mp h2)
  have hle : ∑ i ∈ s, d ^ i ≤ ∑ i ∈ Finset.range k, d ^ i :=
    Finset.sum_le_sum_of_subset hsub
  have hcast : ((∑ i ∈ Finset.range k, d ^ i : ℕ) : ℝ) =
      ((d : ℝ) ^ k - 1) / ((d : ℝ) - 1) := by
    push_cast
    exact geom_sum_eq (by exact_mod_cast (by omega : d ≠ 1)) k
  rw [← hcast]
  exact Nat.cast_le.mpr hle

/-- **Pomerance's Converse (`erdos124.converse`)**:
If `∀ d ∈ D, 3 ≤ d` and all sufficiently large natural numbers belong to
`∑ d ∈ D, sumsOfDistinctPowers d 0`, then `1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹`. -/
theorem erdos124.converse {D : Finset ℕ} (hD₃ : ∀ d ∈ D, 3 ≤ d)
    (h : ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0) :
    1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ := by
  by_contra hcon
  let σ : ℝ := ∑ d ∈ D, ((d : ℝ) - 1)⁻¹
  have hσ : σ < 1 := by
    have h1 : (∑ d ∈ D, (d - 1 : ℚ)⁻¹ : ℚ) < 1 := lt_of_not_ge hcon
    have h2 : (((∑ d ∈ D, (d - 1 : ℚ)⁻¹ : ℚ)) : ℝ) < 1 := by exact_mod_cast h1
    have h3 : (((∑ d ∈ D, (d - 1 : ℚ)⁻¹ : ℚ)) : ℝ) = σ := by
      dsimp [σ]
      rw [Rat.cast_sum]
      exact Finset.sum_congr rfl (fun d _ => by
        rw [Rat.cast_inv, Rat.cast_sub, Rat.cast_natCast, Rat.cast_one])
    rwa [h3] at h2
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  by_cases hD : D = ∅
  · subst hD
    have hmem := hN₀ (N₀ + 1) (Nat.le_succ N₀)
    rw [Finset.sum_empty, Set.mem_zero] at hmem
    omega
  · have hDne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD
    have hσpos : 0 < σ := by
      refine Finset.sum_pos (fun d hd => ?_) hDne
      have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hD₃ d hd
      exact inv_pos.mpr (by linarith)
    let E : ℝ := (1 + σ) / (2 * σ)
    have hE1 : 1 < E := by
      dsimp [E]
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have hEσ : E * σ < 1 := by
      have h4 : (1 + σ) / (2 * σ) * σ = (1 + σ) / 2 := by
        field_simp [hσpos.ne']
      dsimp [E]
      rw [h4]
      linarith
    obtain ⟨n, hnN₀, hn1, hwin⟩ := exists_simultaneous_power_window hD₃ hE1 N₀
    have hmem : n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0 := hN₀ n hnN₀
    obtain ⟨g, hg, hgsum⟩ := (Set.mem_finsetSum D (fun d => sumsOfDistinctPowers d 0) n).mp hmem
    have hgle : ∀ d ∈ D, g d ≤ n := by
      intro d hd
      rw [← hgsum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hd
    have hper : ∀ d ∈ D, (g d : ℝ) < E * (n : ℝ) * ((d : ℝ) - 1)⁻¹ := by
      intro d hd
      obtain ⟨k, hnk, hdk_le⟩ := hwin d hd
      have hd3 := hD₃ d hd
      have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
        linarith
      have hgd_lt : g d < d ^ k := lt_of_le_of_lt (hgle d hd) hnk
      have hb := sumsOfDistinctPowers_le_of_lt_pow (by omega : 2 ≤ d) (hg hd) hgd_lt
      calc
        (g d : ℝ) ≤ ((d : ℝ) ^ k - 1) / ((d : ℝ) - 1) := hb
        _ < (d : ℝ) ^ k / ((d : ℝ) - 1) :=
          div_lt_div_of_pos_right (by linarith) hd1_pos
        _ = ((d ^ k : ℕ) : ℝ) * ((d : ℝ) - 1)⁻¹ := by
          rw [Nat.cast_pow, div_eq_mul_inv]
        _ ≤ E * (n : ℝ) * ((d : ℝ) - 1)⁻¹ :=
          mul_le_mul_of_nonneg_right hdk_le (inv_nonneg.mpr hd1_pos.le)
    have hsum_lt : ((∑ d ∈ D, g d : ℕ) : ℝ) < ∑ d ∈ D, E * (n : ℝ) * ((d : ℝ) - 1)⁻¹ := by
      push_cast
      exact Finset.sum_lt_sum_of_nonempty hDne hper
    rw [hgsum, ← Finset.mul_sum] at hsum_lt
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hcontr : (n : ℝ) < n := by
      calc
        (n : ℝ) < E * (n : ℝ) * σ := hsum_lt
        _ = (n : ℝ) * (E * σ) := by ring
        _ < (n : ℝ) * 1 := mul_lt_mul_of_pos_left hEσ hn_pos
        _ = (n : ℝ) := mul_one _
    exact lt_irrefl _ hcontr

/-- **Pomerance's Converse for arbitrary minimum exponent `k`**:
Since `sumsOfDistinctPowers d k ⊆ sumsOfDistinctPowers d 0`, if all sufficiently large natural
numbers belong to `∑ d ∈ D, sumsOfDistinctPowers d k`, then `1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹`. -/
theorem erdos124.converse_of_k {D : Finset ℕ} {k : ℕ} (hD₃ : ∀ d ∈ D, 3 ≤ d)
    (h : ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k) :
    1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ :=
  erdos124.converse hD₃ (h.mono fun _ hn => sum_sumsOfDistinctPowers_subset_zero D k hn)

/-- **Complete Characterization of Erdős Problem 124 for `k = 0`**:
For any finite set `D` of bases `d ≥ 3`, the following are equivalent:
1. All sufficiently large natural numbers belong to `∑ d ∈ D, sumsOfDistinctPowers d 0`.
2. Every natural number belongs to `∑ d ∈ D, sumsOfDistinctPowers d 0`.
3. `1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹`. -/
theorem erdos124.eventually_iff_le_sum {D : Finset ℕ} (hD : ∀ d ∈ D, 3 ≤ d) :
    (∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0) ↔ 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ :=
  ⟨erdos124.converse hD, erdos124.zero D hD⟩

theorem erdos124.forall_iff_le_sum {D : Finset ℕ} (hD : ∀ d ∈ D, 3 ≤ d) :
    (∀ n : ℕ, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0) ↔ 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ :=
  ⟨fun h => erdos124.converse hD (Filter.Eventually.of_forall h), erdos124.zero_all D hD⟩

end Erdos124

#print axioms Erdos124.pow_dvd_of_mem_sumsOfDistinctPowers
#print axioms Erdos124.sum_sumsOfDistinctPowers_subset_zero
#print axioms Erdos124.sumsOfDistinctPowers_zero_eq
#print axioms Erdos124.subset_sum_complete
#print axioms Erdos124.erdos124.zero_all
#print axioms Erdos124.erdos124.zero
#print axioms Erdos124.exists_simultaneous_power_window
#print axioms Erdos124.erdos124.converse
#print axioms Erdos124.erdos124.converse_of_k
#print axioms Erdos124.erdos124.eventually_iff_le_sum
#print axioms Erdos124.erdos124.forall_iff_le_sum
