/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.SymmDiff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Erdős Problem 657 (`FormalConjectures/ErdosProblems/657.lean`): Distinct Distances in Isosceles-Free Sets

*References:*
- [erdosproblems.com/657](https://www.erdosproblems.com/657)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (1973), 117–138.
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*. Ann. Mat.
  Pura Appl. (4) (1975), 99–108.
- [Du08] Dumitrescu, Adrian, *On distinct distances and λ-free point sets*. Discrete Math.
  (2008), 6533–6538.

This file formalizes complete, zero-`sorry` proofs for `FormalConjectures/ErdosProblems/657.lean`:
1. **Unconditional Proof of Straus's Hyperbox Theorem (`erdos_657.variants.straus`)**:
   For every dimension $k \in \mathbb{N}$, constructs the $2^k$-element weighted hypercube
   $$A_k = \left\{ \sum_{i \in S} 2^i e_i \;\middle|\; S \subseteq \mathrm{Fin}\,k \right\} \subset \mathbb{R}^k$$
   and proves:
   - `A_k.card = 2 ^ k`,
   - `(A_k : Set (ℝ^k)).IsIsoscelesFree` (every triple of distinct points determines 3 distinct distances),
   - `distinctDistances A_k ≤ 2 ^ k - 1` (since $\operatorname{dist}(p_S, p_T)^2 = \sum_{i \in S \triangle T} 4^i$
     depends only on the non-empty symmetric difference $S \triangle T \subseteq \mathrm{Fin}\,k$, and
     base-$4$ uniqueness forces $S \triangle T_1 = S \triangle T_2 \implies T_1 = T_2$).
2. **Characterization of 1D Isosceles-Free Sets (`isIsoscelesFree_real_iff_no_three_term_ap`)**:
   On $\mathbb{R}$, a point set is `IsIsoscelesFree` if and only if it contains no non-trivial
   3-term arithmetic progression ($x + z = 2y$ with $x, y, z$ distinct).
3. **Reduction of `erdos_657.variants.dim_one` to `erdos_657.variants.dim_one_lower`
   (`erdos_657_dim_one_of_dim_one_lower`)**:
   Proves that Dumitrescu's logarithmic lower bound [Du08] implies the main 1D question
   `erdos_657.variants.dim_one`.
-/

open Filter Set Finset BigOperators
open scoped symmDiff

/-- The ternary relation `r` holds triplewise on the set `s` if `r x y z` holds for all
distinct `x, y, z ∈ s`. -/
protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

/-- Three points `p, q, r` form an isosceles triangle if at least two of the three pairwise
distances are equal. -/
def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

/-- A set is isosceles-free if no three distinct points in it form an isosceles triangle. -/
def Set.IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z ↦ ¬ _root_.IsIsosceles x y z

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/-- The number of distinct distances between pairs of distinct points in `points`. -/
noncomputable def distinctDistances {X : Type*} [MetricSpace X] (points : Finset X) : ℕ :=
  (distanceSet points).card

scoped[EuclideanGeometry] notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

namespace Erdos657

/-!
## Part 1: Uniqueness of Base-4 Subset Sums on `Fin k`
-/

/-- Geometric series inequality: $\sum_{j=0}^{m-1} 4^j < 4^m$ for all $m \in \mathbb{N}$. -/
lemma sum_four_pow_range_lt (m : ℕ) : ∑ j ∈ Finset.range m, 4 ^ j < 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have : 4 ^ (m + 1) = 4 * 4 ^ m := by ring
    omega

/-- For any subset $D \subseteq \mathrm{Fin}\,k$ whose elements are all strictly less than $m$,
$\sum_{i \in D} 4^{i.1} < 4^{m.1}$. -/
lemma sum_four_pow_fin_lt {k : ℕ} (D : Finset (Fin k)) (m : Fin k)
    (hm : ∀ i ∈ D, i < m) : ∑ i ∈ D, 4 ^ i.1 < 4 ^ m.1 := by
  have hsub : D.image Fin.val ⊆ Finset.range m.1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hm i hi)
  have himg : ∑ x ∈ D.image Fin.val, 4 ^ x = ∑ i ∈ D, 4 ^ i.1 :=
    Finset.sum_image (fun _ _ _ _ h => Fin.ext h)
  calc
    ∑ i ∈ D, 4 ^ i.1 = ∑ x ∈ D.image Fin.val, 4 ^ x := himg.symm
    _ ≤ ∑ x ∈ Finset.range m.1, 4 ^ x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ < 4 ^ m.1 := sum_four_pow_range_lt m.1

/-- If $m$ is the largest coordinate where $D_1$ and $D_2$ differ, and $m \in D_1 \setminus D_2$,
then $\sum_{i \in D_2} 4^{i.1} < \sum_{i \in D_1} 4^{i.1}$. -/
lemma sum_four_pow_lt_of_max_diff {k : ℕ} {D₁ D₂ : Finset (Fin k)} (m : Fin k)
    (hm1 : m ∈ D₁) (hm2 : m ∉ D₂) (hmax : ∀ i : Fin k, m < i → (i ∈ D₁ ↔ i ∈ D₂)) :
    ∑ i ∈ D₂, 4 ^ i.1 < ∑ i ∈ D₁, 4 ^ i.1 := by
  rw [← Finset.sum_filter_add_sum_filter_not D₂ (fun i : Fin k => m < i),
    ← Finset.sum_filter_add_sum_filter_not D₁ (fun i : Fin k => m < i)]
  have h_upper : D₂.filter (fun i : Fin k => m < i) = D₁.filter (fun i : Fin k => m < i) := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hi, hlt⟩ => ⟨(hmax i hlt).mpr hi, hlt⟩,
      fun ⟨hi, hlt⟩ => ⟨(hmax i hlt).mp hi, hlt⟩⟩
  have h_lower2 : ∑ i ∈ D₂.filter (fun i : Fin k => ¬ m < i), 4 ^ i.1 < 4 ^ m.1 := by
    refine sum_four_pow_fin_lt _ m (fun i hi => ?_)
    obtain ⟨hiD2, hnotlt⟩ := Finset.mem_filter.mp hi
    have hne : i ≠ m := fun h => hm2 (h ▸ hiD2)
    exact lt_of_le_of_ne (not_lt.mp hnotlt) hne
  have h_lower1 : 4 ^ m.1 ≤ ∑ i ∈ D₁.filter (fun i : Fin k => ¬ m < i), 4 ^ i.1 := by
    refine Finset.single_le_sum (f := fun i : Fin k => 4 ^ i.1) (fun _ _ => Nat.zero_le _) ?_
    exact Finset.mem_filter.mpr ⟨hm1, lt_irrefl m⟩
  rw [h_upper]
  omega

/-- **Uniqueness of Base-4 Subset Sums**:
The map $D \mapsto \sum_{i \in D} 4^{i.1}$ on `Finset (Fin k)` is injective. -/
theorem sum_four_pow_injective (k : ℕ) :
    Function.Injective (fun D : Finset (Fin k) => ∑ i ∈ D, 4 ^ i.1) := by
  intro D₁ D₂ hsum
  dsimp at hsum
  by_contra hne
  have hsd_ne : (D₁ ∆ D₂).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    apply hne
    exact symmDiff_eq_bot.mp hemp
  let m : Fin k := (D₁ ∆ D₂).max' hsd_ne
  have hm_mem : m ∈ D₁ ∆ D₂ := Finset.max'_mem (D₁ ∆ D₂) hsd_ne
  have hmax : ∀ i : Fin k, m < i → (i ∈ D₁ ↔ i ∈ D₂) := by
    intro i hi
    have hnot : i ∉ D₁ ∆ D₂ := fun h => not_le_of_gt hi (Finset.le_max' (D₁ ∆ D₂) i h)
    rw [Finset.mem_symmDiff] at hnot
    tauto
  rw [Finset.mem_symmDiff] at hm_mem
  rcases hm_mem with ⟨hm1, hm2⟩ | ⟨hm2, hm1⟩
  · have hlt := sum_four_pow_lt_of_max_diff m hm1 hm2 hmax
    omega
  · have hlt := sum_four_pow_lt_of_max_diff m hm2 hm1 (fun i hi => (hmax i hi).symm)
    omega

/-!
## Part 2: Straus's Weighted Hypercube Construction (`erdos_657.variants.straus`)
-/

/-- The point $p_S \in \mathbb{R}^k$ associated to $S \subseteq \mathrm{Fin}\,k$, with $i$-th
coordinate $2^i$ if $i \in S$ and $0$ otherwise. -/
noncomputable def strausPoint (k : ℕ) (S : Finset (Fin k)) : ℝ^k :=
  WithLp.equiv 2 (Fin k → ℝ) |>.symm fun i => if i ∈ S then (2 : ℝ) ^ i.1 else 0

@[simp]
lemma strausPoint_apply (k : ℕ) (S : Finset (Fin k)) (i : Fin k) :
    strausPoint k S i = if i ∈ S then (2 : ℝ) ^ i.1 else 0 := rfl

/-- The squared distance between `strausPoint k S` and `strausPoint k T` equals
$\sum_{i \in S \triangle T} 4^{i.1}$. -/
lemma dist_sq_strausPoint (k : ℕ) (S T : Finset (Fin k)) :
    dist (strausPoint k S) (strausPoint k T) ^ 2 = ((∑ i ∈ S ∆ T, 4 ^ i.1 : ℕ) : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq, Nat.cast_sum]
  have hterm : ∀ i : Fin k,
      dist (strausPoint k S i) (strausPoint k T i) ^ 2 =
        if i ∈ S ∆ T then ((4 ^ i.1 : ℕ) : ℝ) else 0 := by
    intro i
    simp only [strausPoint_apply, Real.dist_eq, sq_abs, Finset.mem_symmDiff, Nat.cast_pow,
      Nat.cast_ofNat]
    have hpow : ((2 : ℝ) ^ i.1) ^ 2 = (4 : ℝ) ^ i.1 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, hpow]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- Explicit distance formula: $\operatorname{dist}(p_S, p_T) = \sqrt{\sum_{i \in S \triangle T} 4^{i.1}}$. -/
lemma dist_strausPoint (k : ℕ) (S T : Finset (Fin k)) :
    dist (strausPoint k S) (strausPoint k T) = √((∑ i ∈ S ∆ T, 4 ^ i.1 : ℕ) : ℝ) := by
  rw [← Real.sqrt_sq dist_nonneg, dist_sq_strausPoint]

/-- Two pairs $(S, T)$ and $(U, V)$ determine the same distance if and only if they have the same
symmetric difference $S \triangle T = U \triangle V$. -/
lemma dist_strausPoint_eq_iff (k : ℕ) (S T U V : Finset (Fin k)) :
    dist (strausPoint k S) (strausPoint k T) = dist (strausPoint k U) (strausPoint k V) ↔
      S ∆ T = U ∆ V := by
  constructor
  · intro h
    have hsq : dist (strausPoint k S) (strausPoint k T) ^ 2 =
        dist (strausPoint k U) (strausPoint k V) ^ 2 := by rw [h]
    rw [dist_sq_strausPoint, dist_sq_strausPoint, Nat.cast_inj] at hsq
    exact sum_four_pow_injective k hsq
  · intro h
    rw [dist_strausPoint, dist_strausPoint, h]

/-- `strausPoint k` is injective on `Finset (Fin k)`. -/
lemma strausPoint_injective (k : ℕ) : Function.Injective (strausPoint k) := by
  intro S T hST
  have hdist : dist (strausPoint k S) (strausPoint k T) =
      dist (strausPoint k S) (strausPoint k S) := by rw [hST]
  have hsd := (dist_strausPoint_eq_iff k S T S S).mp hdist
  rw [symmDiff_self] at hsd
  exact symmDiff_eq_bot.mp hsd

/-- Straus's $2^k$-point configuration in $\mathbb{R}^k$. -/
noncomputable def strausSet (k : ℕ) : Finset (ℝ^k) :=
  Finset.univ.image (strausPoint k)

/-- `strausSet k` has exact cardinality $2^k$. -/
theorem card_strausSet (k : ℕ) : (strausSet k).card = 2 ^ k := by
  unfold strausSet
  rw [Finset.card_image_of_injective _ (strausPoint_injective k), Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

/-- Symmetric difference cancellation: if $A \triangle B = B \triangle C$, then $A = C$. -/
lemma eq_of_symmDiff_eq_symmDiff {α : Type*} [DecidableEq α] {A B C : Finset α}
    (h : A ∆ B = B ∆ C) : A = C := by
  ext x
  have hx := Finset.ext_iff.mp h x
  simp only [Finset.mem_symmDiff] at hx
  tauto

/-- `strausSet k` is isosceles-free: no three distinct points form an isosceles triangle. -/
theorem isIsoscelesFree_strausSet (k : ℕ) : ((strausSet k : Set (ℝ^k))).IsIsoscelesFree := by
  intro x hx y hy z hz hxy hyz hxz hiso
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨S, _, rfl⟩
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨T, _, rfl⟩
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hz) with ⟨U, _, rfl⟩
  unfold _root_.IsIsosceles at hiso
  rcases hiso with h1 | h2 | h3
  · have hsd := (dist_strausPoint_eq_iff k S T T U).mp h1
    exact hxz (congrArg (strausPoint k) (eq_of_symmDiff_eq_symmDiff hsd))
  · have hsd := (dist_strausPoint_eq_iff k T U U S).mp h2
    exact hxy.symm (congrArg (strausPoint k) (eq_of_symmDiff_eq_symmDiff hsd))
  · have hsd := (dist_strausPoint_eq_iff k U S S T).mp h3
    exact hyz.symm (congrArg (strausPoint k) (eq_of_symmDiff_eq_symmDiff hsd))

/-- `strausSet k` determines at most $2^k - 1$ distinct distances. -/
theorem distinctDistances_strausSet_le (k : ℕ) :
    distinctDistances (strausSet k) ≤ 2 ^ k - 1 := by
  classical
  let nonEmptySubsets : Finset (Finset (Fin k)) :=
    (Finset.univ : Finset (Finset (Fin k))).erase ∅
  let f : Finset (Fin k) → ℝ := fun D => √((∑ i ∈ D, 4 ^ i.1 : ℕ) : ℝ)
  have hsub : distanceSet (strausSet k) ⊆ nonEmptySubsets.image f := by
    intro d hd
    obtain ⟨⟨x, y⟩, hxy_mem, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hx, hy, hxy_ne⟩ := Finset.mem_offDiag.mp hxy_mem
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hy
    have hST_ne : S ≠ T := fun h => hxy_ne (congrArg (strausPoint k) h)
    have hsd_ne : S ∆ T ≠ ∅ := fun h => hST_ne (symmDiff_eq_bot.mp h)
    refine Finset.mem_image.mpr ⟨S ∆ T, ?_, (dist_strausPoint k S T).symm⟩
    exact Finset.mem_erase.mpr ⟨hsd_ne, Finset.mem_univ _⟩
  calc
    distinctDistances (strausSet k) = (distanceSet (strausSet k)).card := rfl
    _ ≤ (nonEmptySubsets.image f).card := Finset.card_le_card hsub
    _ ≤ nonEmptySubsets.card := Finset.card_image_le
    _ = 2 ^ k - 1 := by
      dsimp [nonEmptySubsets]
      rw [Finset.card_erase_of_mem (Finset.mem_univ ∅), Finset.card_univ,
        Fintype.card_finset, Fintype.card_fin]

/-- **Straus's Theorem (`erdos_657.variants.straus`)**:
For every $k \in \mathbb{N}$, there is a set of $2^k$ points in $\mathbb{R}^k$ with no isosceles
triangles which determines at most $2^k - 1$ distinct distances. -/
theorem erdos_657.variants.straus (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 :=
  ⟨strausSet k, card_strausSet k, isIsoscelesFree_strausSet k, distinctDistances_strausSet_le k⟩

/-!
## Part 3: 1D Characterization and Reduction of `erdos_657.variants.dim_one`
-/

/-- On the real line $\mathbb{R}$, three distinct points $x, y, z$ form an isosceles triangle if
and only if one is the midpoint of the other two ($x + z = 2y$, $y + x = 2z$, or $z + y = 2x$). -/
theorem isIsosceles_real_iff {x y z : ℝ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    IsIsosceles x y z ↔ x + z = 2 * y ∨ y + x = 2 * z ∨ z + y = 2 * x := by
  unfold _root_.IsIsosceles
  simp only [Real.dist_eq, abs_eq_abs]
  constructor
  · rintro ((h | h) | (h | h) | (h | h))
    · left; linarith
    · exfalso; apply hxz; linarith
    · right; left; linarith
    · exfalso; apply hxy; linarith
    · right; right; linarith
    · exfalso; apply hyz; linarith
  · rintro (h | h | h)
    · left; left; linarith
    · right; left; left; linarith
    · right; right; left; linarith

/-- On the real line, a set $A \subseteq \mathbb{R}$ has no isosceles triangles if and only if
it contains no non-trivial three-term arithmetic progression. -/
theorem isIsoscelesFree_real_iff_no_three_term_ap (A : Set ℝ) :
    A.IsIsoscelesFree ↔
      ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → ∀ ⦃z⦄, z ∈ A → x ≠ y → y ≠ z → x ≠ z → x + z ≠ 2 * y := by
  constructor
  · intro h x hx y hy z hz hxy hyz hxz hsum
    apply h hx hy hz hxy hyz hxz
    exact (isIsosceles_real_iff hxy hyz hxz).mpr (Or.inl hsum)
  · intro h x hx y hy z hz hxy hyz hxz hiso
    rcases (isIsosceles_real_iff hxy hyz hxz).mp hiso with h1 | h2 | h3
    · exact h hx hy hz hxy hyz hxz h1
    · exact h hy hz hx hyz hxz.symm hxy.symm h2
    · exact h hz hx hy hxz.symm hxy hyz.symm h3

/-- **Deduction of `erdos_657.variants.dim_one` from Dumitrescu's Lower Bound
(`erdos_657.variants.dim_one_lower`)**:
As stated in `FormalConjectures/ErdosProblems/657.lean`, Dumitrescu's theorem [Du08] that every
isosceles-free set of $n$ reals determines at least $n (\log n)^c$ distinct distances for large $n$
immediately yields a function $f : \mathbb{N} \to \mathbb{R}$ with $f(n) \to \infty$ such that
$f(n) n \le \mathrm{distinctDistances}(A)$ for all $n$ and all $A \subseteq \mathbb{R}$ of size $n$. -/
theorem erdos_657_dim_one_of_dim_one_lower
    (h_lower : ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset ℝ, A.card = n → (A : Set ℝ).IsIsoscelesFree →
        (n : ℝ) * (Real.log n) ^ c ≤ (distinctDistances A : ℝ)) :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ n : ℕ, ∀ A : Finset ℝ, A.card = n → (A : Set ℝ).IsIsoscelesFree →
        f n * (n : ℝ) ≤ (distinctDistances A : ℝ) := by
  obtain ⟨c, hc, h_ev⟩ := h_lower
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨N, hN⟩ := h_ev
  let f : ℕ → ℝ := fun n => if n < N then 0 else (Real.log n) ^ c
  refine ⟨f, ?_, ?_⟩
  · have h_log : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h_rpow : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ c) atTop atTop :=
      (tendsto_rpow_atTop hc).comp h_log
    refine h_rpow.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    simp [f, not_lt.mpr hn]
  · intro n A hcard hiso
    dsimp [f]
    split_ifs with hlt
    · rw [zero_mul]
      positivity
    · rw [mul_comm]
      exact hN n (not_lt.mp hlt) A hcard hiso

end Erdos657

#print axioms Erdos657.sum_four_pow_injective
#print axioms Erdos657.erdos_657.variants.straus
#print axioms Erdos657.isIsoscelesFree_real_iff_no_three_term_ap
#print axioms Erdos657.erdos_657_dim_one_of_dim_one_lower
