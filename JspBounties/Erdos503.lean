import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 503 (`JSP-000403` / `JSP-000404`): Isosceles Point Sets in $\mathbb{R}^n$

*References:*
- [erdosproblems.com/503](https://www.erdosproblems.com/503) (`FormalConjectures/ErdosProblems/503.lean`)
- [ErKe47] Erdős, P. and Kelly, L. M., *Elementary Problems and Solutions: Solutions: E735*.
  Amer. Math. Monthly 54 (1947), 227–229.
- [Cr62] Croft, H. T., *$9$-point and $7$-point configurations in $3$-space*.
  Proc. London Math. Soc. (3) 12 (1962), 400–424.
- [Bl84] Blokhuis, A., *Few-distance sets*. CWI Tract 7 (1984), Chapter 7.
- [Ko24c] Kovács, Z., *A note on Erdős's mysterious remark*. arXiv:2412.05190 (2024).

This file formalizes complete, zero-`sorry` proofs for `FormalConjectures/ErdosProblems/503.lean`:
1. **Exact solution in dimension $n = 0$ (`erdos_503.variants.R0`)**:
   `IsGreatest {(A.ncard) | (A : Set (ℝ^0)) (hA : A.IsIsosceles)} 1`.
2. **Exact solution in dimension $n = 1$ (`erdos_503.variants.R1`)**:
   `IsGreatest {(A.ncard) | (A : Set (ℝ^1)) (hA : A.IsIsosceles)} 3`, proving both the construction
   $\{-1, 0, 1\} \subset \mathbb{R}^1$ of size $3$ and the upper bound $|A| \le 3 = \binom{1+2}{2}$.
3. **General Two-Distance and Spherical Suspension Principles (`triplewise_isIsosceles_of_two_distances`,
   `triplewise_isIsosceles_insert_center`)**:
   Every $\le 2$-distance set is `IsIsosceles`; adjoining the center of a spherical $2$-distance
   set preserves `IsIsosceles`.
4. **Kelly's 6-Point Planar Construction (`kelly_R2_lower_bound`)**:
   The centered regular pentagon in $\mathbb{R}^2$ has cardinality $6$ and satisfies `A.IsIsosceles`
   (the constructive half of `erdos_503.variants.R2`, and `erdos_503.variants.R2` modulo the
   upper bound).
5. **Kelly's 8-Point 3D Construction (`kelly_R3_lower_bound`)**:
   The centered regular pentagonal bipyramid in $\mathbb{R}^3$ has cardinality $8$ and satisfies
   `A.IsIsosceles` (the constructive half of `erdos_503.variants.R3`).
6. **Alweiss's General $\binom{n+1}{2}$ Construction in $\mathbb{R}^n$ (`alweiss_construction`)**:
   For every $n \ge 1$, constructs an explicit regular simplex $v_0, \dots, v_n \in \mathbb{R}^n$
   and proves via a coordinatewise four-point quadratic identity that the $\binom{n+1}{2}$ pairwise
   sums $v_i + v_j$ ($0 \le i < j \le n$) form a $2$-distance (hence `IsIsosceles`) set of exact
   cardinality $\binom{n+1}{2}$, deriving `erdos_503.variants.lower_bound` from `BddAbove`.
-/

open Set Finset BigOperators

/-- The ternary relation `r` holds triplewise on the set `s` if `r x y z` holds for all
distinct `x, y, z ∈ s`. -/
protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

/-- Three points `p, q, r` form an isosceles triangle if at least two of the three pairwise
distances are equal. -/
def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

/-- A set `A` is isosceles if it is nonempty and every triple of distinct points in `A`
forms an isosceles triangle. -/
nonrec def Set.IsIsosceles {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Nonempty ∧ A.Triplewise (IsIsosceles · · ·)

scoped[EuclideanGeometry] notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
scoped[EuclideanGeometry] notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open scoped EuclideanGeometry

namespace Erdos503

/-!
## Part 1: General Combinatorial & Metric Reduction Lemmas
-/

/-- **Pigeonhole Principle for 2-Distance Sets**:
If every pair of distinct points in `A` has distance in `{d₁, d₂}`, then every triple of distinct
points in `A` is `IsIsosceles`. -/
theorem triplewise_isIsosceles_of_two_distances {α : Type*} [PseudoMetricSpace α]
    {A : Set α} {d₁ d₂ : ℝ}
    (hdist : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → x ≠ y → dist x y = d₁ ∨ dist x y = d₂) :
    A.Triplewise (IsIsosceles · · ·) := by
  intro x hx y hy z hz hxy hyz hxz
  unfold _root_.IsIsosceles
  rcases hdist hx hy hxy with h1 | h1 <;>
    rcases hdist hy hz hyz with h2 | h2 <;>
      rcases hdist hz hx hxz.symm with h3 | h3
  · left; rw [h1, h2]
  · left; rw [h1, h2]
  · right; right; rw [h3, h1]
  · right; left; rw [h2, h3]
  · right; left; rw [h2, h3]
  · right; right; rw [h3, h1]
  · left; rw [h1, h2]
  · left; rw [h1, h2]

/-- **Spherical Center Extension**:
If `S` is a 2-distance set on a sphere of radius `r` centered at `c`, then `insert c S` is
`IsIsosceles`. -/
theorem triplewise_isIsosceles_insert_center {α : Type*} [PseudoMetricSpace α]
    {S : Set α} {c : α} {r d₁ d₂ : ℝ}
    (hrad : ∀ ⦃x⦄, x ∈ S → dist c x = r)
    (hdist : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → dist x y = d₁ ∨ dist x y = d₂) :
    (insert c S).Triplewise (IsIsosceles · · ·) := by
  intro x hx y hy z hz hxy hyz hxz
  rcases hx with rfl | hxS
  · rcases hy with rfl | hyS
    · contradiction
    · rcases hz with rfl | hzS
      · contradiction
      · right; right
        rw [dist_comm z x, hrad hzS, hrad hyS]
  · rcases hy with rfl | hyS
    · rcases hz with rfl | hzS
      · contradiction
      · left
        rw [dist_comm x y, hrad hxS, hrad hzS]
    · rcases hz with rfl | hzS
      · right; left
        rw [dist_comm y z, hrad hyS, hrad hxS]
      · exact triplewise_isIsosceles_of_two_distances hdist hxS hyS hzS hxy hyz hxz

/-!
## Part 2: Exact Solutions in Dimensions $n = 0$ and $n = 1$
-/

/-- In dimension $n = 0$, the maximum size of an isosceles subset of $\mathbb{R}^0$ is $1 = \binom{2}{2}$. -/
theorem erdos_503.variants.R0 :
    IsGreatest {(A.ncard) | (A : Set (ℝ^0)) (_hA : A.IsIsosceles)} 1 := by
  refine ⟨⟨{0}, ⟨⟨0, rfl⟩, fun x _ y _ _ _ hxy _ _ => (hxy (Subsingleton.elim x y)).elim⟩,
    Set.ncard_singleton 0⟩, ?_⟩
  rintro m ⟨A, _, rfl⟩
  have hsub : A ⊆ ({0} : Set (ℝ^0)) := fun x _ => Set.mem_singleton_iff.mpr (Subsingleton.elim x 0)
  exact le_trans (Set.ncard_le_ncard hsub (Set.finite_singleton 0)) (by simp)

/-- Helper lemma on $\mathbb{R}$: four strictly ordered real numbers $a < b < c < d$ cannot have
all triples isosceles. -/
lemma not_all_triples_isosceles_four_reals {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h1 : |a - b| = |b - c| ∨ |b - c| = |c - a| ∨ |c - a| = |a - b|)
    (h2 : |b - c| = |c - d| ∨ |c - d| = |d - b| ∨ |d - b| = |b - c|)
    (h3 : |a - b| = |b - d| ∨ |b - d| = |d - a| ∨ |d - a| = |a - b|) : False := by
  have hab' : |a - b| = b - a := by rw [abs_of_neg (by linarith)]; ring
  have hbc' : |b - c| = c - b := by rw [abs_of_neg (by linarith)]; ring
  have hca' : |c - a| = c - a := abs_of_pos (by linarith)
  have hcd' : |c - d| = d - c := by rw [abs_of_neg (by linarith)]; ring
  have hdb' : |d - b| = d - b := abs_of_pos (by linarith)
  have hbd' : |b - d| = d - b := by rw [abs_of_neg (by linarith)]; ring
  have hda' : |d - a| = d - a := abs_of_pos (by linarith)
  rw [hab', hbc', hca'] at h1
  rw [hbc', hcd', hdb'] at h2
  rw [hab', hbd', hda'] at h3
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
    linarith

/-- For any two vectors $x, y \in \mathbb{R}^1$, $\operatorname{dist}(x, y) = |x_0 - y_0|$. -/
lemma dist_R1_eq_abs (x y : ℝ^1) : dist x y = |x 0 - y 0| := by
  have hsq : dist x y ^ 2 = (x 0 - y 0) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_one, Real.dist_eq, sq_abs]
  have h1 : √(dist x y ^ 2) = √((x 0 - y 0) ^ 2) := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq_eq_abs] at h1

/-- No finite `IsIsosceles` subset of $\mathbb{R}^1$ can have more than $3$ elements. -/
lemma card_le_three_of_isIsosceles_R1 {A : Set (ℝ^1)} (hA : A.IsIsosceles) (hfin : A.Finite) :
    A.ncard ≤ 3 := by
  by_contra! hgt
  have hcard4 : 4 ≤ hfin.toFinset.card := by
    have : hfin.toFinset.card = A.ncard := by
      rw [← Set.ncard_coe_finset, Finite.coe_toFinset]
    omega
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hcard4
  let s : Finset ℝ := B.image (fun x : ℝ^1 => x 0)
  have hinj : Set.InjOn (fun x : ℝ^1 => x 0) (B : Set (ℝ^1)) := by
    intro x _ y _ hxy
    ext i
    fin_cases i
    exact hxy
  have hscard : s.card = 4 := by
    rw [Finset.card_image_of_injOn hinj, hBcard]
  let e := s.orderEmbOfFin hscard
  obtain ⟨xa, hxaB, hxa⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem hscard 0)
  obtain ⟨xb, hxbB, hxb⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem hscard 1)
  obtain ⟨xc, hxcB, hxc⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem hscard 2)
  obtain ⟨xd, hxdB, hxd⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem hscard 3)
  have hxaA : xa ∈ A := (Finite.mem_toFinset hfin).mp (hBsub hxaB)
  have hxbA : xb ∈ A := (Finite.mem_toFinset hfin).mp (hBsub hxbB)
  have hxcA : xc ∈ A := (Finite.mem_toFinset hfin).mp (hBsub hxcB)
  have hxdA : xd ∈ A := (Finite.mem_toFinset hfin).mp (hBsub hxdB)
  have hab : xa 0 < xb 0 := by rw [hxa, hxb]; exact e.strictMono (by decide : (0 : Fin 4) < 1)
  have hbc : xb 0 < xc 0 := by rw [hxb, hxc]; exact e.strictMono (by decide : (1 : Fin 4) < 2)
  have hcd : xc 0 < xd 0 := by rw [hxc, hxd]; exact e.strictMono (by decide : (2 : Fin 4) < 3)
  have hne : ∀ {u v : ℝ^1}, u 0 < v 0 → u ≠ v := fun huv heq => by rw [heq] at huv; linarith
  have h1 := hA.2 hxaA hxbA hxcA (hne hab) (hne hbc) (hne (hab.trans hbc))
  have h2 := hA.2 hxbA hxcA hxdA (hne hbc) (hne hcd) (hne (hbc.trans hcd))
  have h3 := hA.2 hxaA hxbA hxdA (hne hab) (hne (hbc.trans hcd)) (hne ((hab.trans hbc).trans hcd))
  unfold _root_.IsIsosceles at h1 h2 h3
  simp only [dist_R1_eq_abs] at h1 h2 h3
  exact not_all_triples_isosceles_four_reals hab hbc hcd h1 h2 h3

/-- Upper bound of `Erdos503` for $n = 1$: every `IsIsosceles` subset of $\mathbb{R}^1$ has
`A.ncard ≤ 3 = (1 + 2).choose 2`. -/
theorem erdos_503_upper_bound_R1 :
    ∀ m ∈ {(A.ncard) | (A : Set (ℝ^1)) (_hA : A.IsIsosceles)}, m ≤ (1 + 2).choose 2 := by
  rintro m ⟨A, hA, rfl⟩
  by_cases hfin : A.Finite
  · exact card_le_three_of_isIsosceles_R1 hA hfin
  · rw [Set.Infinite.ncard hfin]
    decide

/-- **Complete Resolution of Erdős Problem 503 in Dimension $n = 1$ (`erdos_503.variants.R1`)**:
The maximum size of an isosceles subset of $\mathbb{R}^1$ is $3$ (realized by $\{-1, 0, 1\}$). -/
theorem erdos_503.variants.R1 :
    IsGreatest {(A.ncard) | (A : Set (ℝ^1)) (_hA : A.IsIsosceles)} 3 := by
  refine ⟨?_, erdos_503_upper_bound_R1⟩
  let p0 : ℝ^1 := EuclideanSpace.single 0 (-1 : ℝ)
  let p1 : ℝ^1 := 0
  let p2 : ℝ^1 := EuclideanSpace.single 0 (1 : ℝ)
  have hp0_val : p0 0 = -1 := by simp [p0]
  have hp1_val : p1 0 = 0 := by simp [p1]
  have hp2_val : p2 0 = 1 := by simp [p2]
  have hp01 : p0 ≠ p1 := fun h => by have := congrArg (fun v : ℝ^1 => v 0) h; linarith
  have hp12 : p1 ≠ p2 := fun h => by have := congrArg (fun v : ℝ^1 => v 0) h; linarith
  have hp02 : p0 ≠ p2 := fun h => by have := congrArg (fun v : ℝ^1 => v 0) h; linarith
  refine ⟨{p0, p1, p2}, ⟨⟨p0, by simp⟩, ?_⟩, ?_⟩
  · intro x hx y hy z hz hxy hyz hxz
    unfold _root_.IsIsosceles
    simp only [dist_R1_eq_abs]
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl <;>
        rcases hz with rfl | rfl | rfl <;>
          first
          | contradiction
          | (simp only [hp0_val, hp1_val, hp2_val]; norm_num)
  · rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton]
    · simp [hp12]
    · simp [hp01, hp02]

/-!
## Part 3: Kelly's 6-Point Planar Construction (`R2`) and 8-Point 3D Construction (`R3`)
-/

/-- Cosine and sine coordinates of the regular pentagon on the unit circle. -/
noncomputable def c1 : ℝ := (√5 - 1) / 4
noncomputable def c2 : ℝ := -(√5 + 1) / 4
noncomputable def s1 : ℝ := √((5 + √5) / 8)
noncomputable def s2 : ℝ := √((5 - √5) / 8)

lemma sqrt5_Bounds : 2 < √5 ∧ √5 < 3 := by
  constructor
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma s1_sq : s1 ^ 2 = (5 + √5) / 8 := by
  unfold s1
  have := sqrt5_Bounds
  exact Real.sq_sqrt (by linarith)

lemma s2_sq : s2 ^ 2 = (5 - √5) / 8 := by
  unfold s2
  have := sqrt5_Bounds
  exact Real.sq_sqrt (by linarith)

lemma s1_pos : 0 < s1 := by
  unfold s1
  have := sqrt5_Bounds
  exact Real.sqrt_pos.mpr (by linarith)

lemma s2_pos : 0 < s2 := by
  unfold s2
  have := sqrt5_Bounds
  exact Real.sqrt_pos.mpr (by linarith)

lemma s1_mul_s2 : s1 * s2 = √5 / 4 := by
  have hsq : (s1 * s2) ^ 2 = (√5 / 4) ^ 2 := by
    calc
      (s1 * s2) ^ 2 = s1 ^ 2 * s2 ^ 2 := by ring
      _ = ((5 + √5) / 8) * ((5 - √5) / 8) := by rw [s1_sq, s2_sq]
      _ = (25 - (√5) ^ 2) / 64 := by ring
      _ = (25 - 5) / 64 := by rw [Real.sq_sqrt (by norm_num)]
      _ = 5 / 16 := by ring
      _ = (√5) ^ 2 / 16 := by rw [Real.sq_sqrt (by norm_num)]
      _ = (√5 / 4) ^ 2 := by ring
  have hnonneg1 : 0 ≤ s1 * s2 := mul_nonneg s1_pos.le s2_pos.le
  have hnonneg2 : 0 ≤ √5 / 4 := by positivity
  nlinarith [sq_nonneg (s1 * s2 - √5 / 4)]

/-- The 5 vertices of the regular pentagon on the unit circle in $\mathbb{R}^2$. -/
noncomputable def pentagonVertex (i : Fin 5) : ℝ² :=
  match i with
  | ⟨0, _⟩ => !₂[1, 0]
  | ⟨1, _⟩ => !₂[c1, s1]
  | ⟨2, _⟩ => !₂[c2, s2]
  | ⟨3, _⟩ => !₂[c2, -s2]
  | ⟨4, _⟩ => !₂[c1, -s1]

/-- Every vertex of the regular pentagon lies at distance `1` from the origin `0 : ℝ²`. -/
lemma dist_zero_pentagonVertex (i : Fin 5) : dist (0 : ℝ²) (pentagonVertex i) = 1 := by
  have hsq : dist (0 : ℝ²) (pentagonVertex i) ^ 2 = 1 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
    fin_cases i <;>
      simp only [pentagonVertex, PiLp.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.dist_eq, sq_abs]
    · ring
    · unfold c1; linear_combination s1_sq + (1 / 16) * Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    · unfold c2; linear_combination s2_sq + (1 / 16) * Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    · unfold c2; linear_combination s2_sq + (1 / 16) * Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    · unfold c1; linear_combination s1_sq + (1 / 16) * Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [dist_nonneg (x := (0 : ℝ²)) (y := pentagonVertex i)]

/-- Every pair of distinct vertices of the regular pentagon has squared distance equal to
$(5 - \sqrt{5}) / 2$ (side) or $(5 + \sqrt{5}) / 2$ (diagonal). -/
lemma dist_sq_pentagonVertex (i j : Fin 5) (hij : i ≠ j) :
    dist (pentagonVertex i) (pentagonVertex j) ^ 2 = (5 - √5) / 2 ∨
    dist (pentagonVertex i) (pentagonVertex j) ^ 2 = (5 + √5) / 2 := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs1 := s1_sq
  have hs2 := s2_sq
  have hs12 := s1_mul_s2
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    simp only [pentagonVertex, Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs,
      c1, c2]
    first
    | (left; linear_combination hs1 + (1 / 16) * h5)
    | (right; linear_combination hs2 + (1 / 16) * h5)
    | (left; linear_combination hs1 + hs2 - 2 * hs12 + (4 / 16) * h5)
    | (right; linear_combination hs1 + hs2 + 2 * hs12 + (4 / 16) * h5)
    | (left; linear_combination 4 * hs2)
    | (right; linear_combination 4 * hs1)

/-- Every pair of distinct vertices of the regular pentagon has distance $\sqrt{(5 - \sqrt{5})/2}$
or $\sqrt{(5 + \sqrt{5})/2}$. -/
lemma dist_pentagonVertex (i j : Fin 5) (hij : i ≠ j) :
    dist (pentagonVertex i) (pentagonVertex j) = √((5 - √5) / 2) ∨
    dist (pentagonVertex i) (pentagonVertex j) = √((5 + √5) / 2) := by
  rcases dist_sq_pentagonVertex i j hij with h | h
  · left
    rw [← Real.sqrt_sq dist_nonneg, h]
  · right
    rw [← Real.sqrt_sq dist_nonneg, h]

/-- The 5 vertices of the regular pentagon are pairwise distinct, and none equals `0`. -/
lemma pentagonVertex_injective : Function.Injective pentagonVertex := by
  intro i j hij
  by_contra hne
  have h0 : dist (pentagonVertex i) (pentagonVertex j) ^ 2 = 0 := by rw [hij, dist_self, sq]; ring
  have hb := sqrt5_Bounds
  rcases dist_sq_pentagonVertex i j hne with h | h <;> linarith

lemma pentagonVertex_ne_zero (i : Fin 5) : pentagonVertex i ≠ 0 := by
  intro h
  have := dist_zero_pentagonVertex i
  rw [h, dist_self] at this
  linarith

/-- Kelly's 6-point planar configuration: the origin `0` plus the 5 vertices of the regular pentagon. -/
noncomputable def kellySixPoints : Set ℝ² :=
  insert 0 (Set.range pentagonVertex)

/-- **Kelly's 6-Point Planar Construction (`kelly_R2_lower_bound`)**:
`kellySixPoints ⊆ ℝ²` is an `IsIsosceles` set of cardinality `6`, establishing the constructive half
of `erdos_503.variants.R2`. -/
theorem kelly_R2_lower_bound :
    kellySixPoints.IsIsosceles ∧ kellySixPoints.ncard = 6 := by
  have hrange_fin : (Set.range pentagonVertex).Finite := Set.finite_range pentagonVertex
  have h0_not_mem : (0 : ℝ²) ∉ Set.range pentagonVertex := by
    rintro ⟨i, hi⟩
    exact pentagonVertex_ne_zero i hi
  constructor
  · refine ⟨⟨0, Set.mem_insert 0 _⟩, ?_⟩
    refine triplewise_isIsosceles_insert_center (α := ℝ²) (r := 1)
      (d₁ := √((5 - √5) / 2)) (d₂ := √((5 + √5) / 2)) ?_ ?_
    · rintro x ⟨i, rfl⟩
      exact dist_zero_pentagonVertex i
    · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hxy
      exact dist_pentagonVertex i j (fun hij => hxy (congrArg pentagonVertex hij))
  · unfold kellySixPoints
    rw [Set.ncard_insert_of_notMem h0_not_mem hrange_fin,
      Set.ncard_range_of_injective pentagonVertex_injective, Nat.card_fin]

/-- Conditional completion of `erdos_503.variants.R2` (`FormalConjectures/ErdosProblems/503.lean`)
from `kelly_R2_lower_bound` and Kelly's planar upper bound. -/
theorem erdos_503_R2_of_upper_bound
    (hupper : ∀ m ∈ {(A.ncard) | (A : Set ℝ²) (_hA : A.IsIsosceles)}, m ≤ 6) :
    IsGreatest {(A.ncard) | (A : Set ℝ²) (_hA : A.IsIsosceles)} 6 :=
  ⟨⟨kellySixPoints, kelly_R2_lower_bound.1, kelly_R2_lower_bound.2⟩, hupper⟩

/-- Isometric embedding of $\mathbb{R}^2$ into the $z = 0$ plane of $\mathbb{R}^3$. -/
noncomputable def embedR2ToR3 (p : ℝ²) : ℝ³ :=
  WithLp.equiv 2 (Fin 3 → ℝ) |>.symm fun j =>
    if j.1 = 0 then p 0 else if j.1 = 1 then p 1 else 0

@[simp]
lemma embedR2ToR3_apply (p : ℝ²) (j : Fin 3) :
    embedR2ToR3 p j = if j.1 = 0 then p 0 else if j.1 = 1 then p 1 else 0 := rfl

lemma dist_embedR2ToR3 (p q : ℝ²) : dist (embedR2ToR3 p) (embedR2ToR3 q) = dist p q := by
  have hsq : dist (embedR2ToR3 p) (embedR2ToR3 q) ^ 2 = dist p q ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
    simp [embedR2ToR3_apply, Real.dist_eq, sq_abs]
  have h1 : √(dist (embedR2ToR3 p) (embedR2ToR3 q) ^ 2) = √(dist p q ^ 2) :=
    congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq dist_nonneg] at h1

/-- The three axial points $O = (0,0,0)$, $N = (0,0,1)$, $P = (0,0,-1)$ in $\mathbb{R}^3$. -/
noncomputable def poleAxis (k : Fin 3) : ℝ³ :=
  WithLp.equiv 2 (Fin 3 → ℝ) |>.symm fun j =>
    if j.1 = 2 then (if k.1 = 0 then 0 else if k.1 = 1 then 1 else -1) else 0

@[simp]
lemma poleAxis_apply (k : Fin 3) (j : Fin 3) :
    poleAxis k j = if j.1 = 2 then (if k.1 = 0 then 0 else if k.1 = 1 then 1 else -1) else 0 := rfl

lemma dist_poleAxis_embed_pentagon (k : Fin 3) (i : Fin 5) :
    dist (poleAxis k) (embedR2ToR3 (pentagonVertex i)) = if k.1 = 0 then 1 else √2 := by
  have hp_norm : (pentagonVertex i 0) ^ 2 + (pentagonVertex i 1) ^ 2 = 1 := by
    have h0 := dist_zero_pentagonVertex i
    have hsq : dist (0 : ℝ²) (pentagonVertex i) ^ 2 = 1 := by rw [h0]; ring
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hsq
    simp only [PiLp.zero_apply, Real.dist_eq, sq_abs] at hsq
    linarith
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    have hsq : dist (poleAxis 0) (embedR2ToR3 (pentagonVertex i)) ^ 2 = 1 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
      simp only [poleAxis_apply, embedR2ToR3_apply, Fin.isValue, Fin.val_zero, Fin.val_one,
        Fin.val_two, ↓reduceIte, Real.dist_eq, sq_abs]
      norm_num
      linarith [hp_norm]
    nlinarith [dist_nonneg (x := poleAxis 0) (y := embedR2ToR3 (pentagonVertex i))]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    have hsq : dist (poleAxis 1) (embedR2ToR3 (pentagonVertex i)) ^ 2 = 2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
      simp only [poleAxis_apply, embedR2ToR3_apply, Fin.isValue, Fin.val_zero, Fin.val_one,
        Fin.val_two, ↓reduceIte, Real.dist_eq, sq_abs]
      norm_num
      linarith [hp_norm]
    rw [← Real.sqrt_sq dist_nonneg, hsq]
  · simp only [Fin.reduceFinMk, Fin.isValue, OfNat.ofNat_ne_zero, ↓reduceIte]
    have hsq : dist (poleAxis 2) (embedR2ToR3 (pentagonVertex i)) ^ 2 = 2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
      simp only [poleAxis_apply, embedR2ToR3_apply, Fin.isValue, Fin.val_zero, Fin.val_one,
        Fin.val_two, ↓reduceIte, Real.dist_eq, sq_abs]
      norm_num
      linarith [hp_norm]
    rw [← Real.sqrt_sq dist_nonneg, hsq]

lemma dist_poleAxis (a b : Fin 3) :
    dist (poleAxis a) (poleAxis b) =
      if a = b then 0 else if a.1 = 0 ∨ b.1 = 0 then 1 else 2 := by
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg hab]
    rw [← Real.sqrt_sq dist_nonneg, EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
    fin_cases a <;> fin_cases b <;> try contradiction
    all_goals
      simp only [poleAxis_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte, Real.dist_eq, sq_abs]
      norm_num
      try rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Kelly's 8-point configuration in $\mathbb{R}^3$: the 3 axial points `poleAxis` (`Fin 3`)
together with the 5 equatorial pentagon vertices (`Fin 5`). -/
noncomputable def kellyEightMap : Fin 3 ⊕ Fin 5 → ℝ³
  | Sum.inl k => poleAxis k
  | Sum.inr i => embedR2ToR3 (pentagonVertex i)

noncomputable def kellyEightPoints : Set ℝ³ :=
  Set.range kellyEightMap

lemma kellyEightMap_injective : Function.Injective kellyEightMap := by
  intro u v huv
  rcases u with a | i <;> rcases v with b | j
  · by_contra hne
    have hab : a ≠ b := fun h => hne (congrArg Sum.inl h)
    have h0 : dist (poleAxis a) (poleAxis b) = 0 := by
      change dist (kellyEightMap (Sum.inl a)) (kellyEightMap (Sum.inl b)) = 0
      rw [huv, dist_self]
    rw [dist_poleAxis a b, if_neg hab] at h0
    split_ifs at h0 <;> linarith
  · exfalso
    have h0 : dist (poleAxis a) (embedR2ToR3 (pentagonVertex j)) = 0 := by
      change dist (kellyEightMap (Sum.inl a)) (kellyEightMap (Sum.inr j)) = 0
      rw [huv, dist_self]
    rw [dist_poleAxis_embed_pentagon a j] at h0
    split_ifs at h0
    · linarith
    · have : (0 : ℝ) < √2 := by positivity
      linarith
  · exfalso
    have h0 : dist (poleAxis b) (embedR2ToR3 (pentagonVertex i)) = 0 := by
      change dist (kellyEightMap (Sum.inl b)) (kellyEightMap (Sum.inr i)) = 0
      rw [← huv, dist_self]
    rw [dist_poleAxis_embed_pentagon b i] at h0
    split_ifs at h0
    · linarith
    · have : (0 : ℝ) < √2 := by positivity
      linarith
  · congr 1
    apply pentagonVertex_injective
    have h0 : dist (embedR2ToR3 (pentagonVertex i)) (embedR2ToR3 (pentagonVertex j)) = 0 := by
      change dist (kellyEightMap (Sum.inr i)) (kellyEightMap (Sum.inr j)) = 0
      rw [huv, dist_self]
    rw [dist_embedR2ToR3] at h0
    exact dist_eq_zero.mp h0

/-- **Kelly's 8-Point 3D Construction (`kelly_R3_lower_bound`)**:
`kellyEightPoints ⊆ ℝ³` is an `IsIsosceles` set of cardinality `8`, establishing the constructive
half of `erdos_503.variants.R3`. -/
theorem kelly_R3_lower_bound :
    kellyEightPoints.IsIsosceles ∧ kellyEightPoints.ncard = 8 := by
  constructor
  · refine ⟨⟨kellyEightMap (Sum.inl 0), ⟨Sum.inl 0, rfl⟩⟩, ?_⟩
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ _ ⟨w, rfl⟩ huv hvw huw
    have huv' : u ≠ v := fun h => huv (congrArg kellyEightMap h)
    have hvw' : v ≠ w := fun h => hvw (congrArg kellyEightMap h)
    have huw' : u ≠ w := fun h => huw (congrArg kellyEightMap h)
    unfold _root_.IsIsosceles
    rcases u with a | i <;> rcases v with b | j <;> rcases w with c | k
    · -- 3 axial points `{poleAxis a, poleAxis b, poleAxis c}`
      have hab : a ≠ b := fun h => huv' (congrArg Sum.inl h)
      have hbc : b ≠ c := fun h => hvw' (congrArg Sum.inl h)
      have hac : a ≠ c := fun h => huw' (congrArg Sum.inl h)
      simp only [kellyEightMap, dist_poleAxis]
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        first | contradiction | simp
    · -- 2 axial points `a, b` and 1 pentagon vertex `k`
      have hab : a ≠ b := fun h => huv' (congrArg Sum.inl h)
      simp only [kellyEightMap, dist_poleAxis, dist_comm (embedR2ToR3 _),
        dist_poleAxis_embed_pentagon]
      fin_cases a <;> fin_cases b <;> first | contradiction | simp
    · -- 2 axial points `a, c` and 1 pentagon vertex `j`
      have hac : a ≠ c := fun h => huw' (congrArg Sum.inl h)
      simp only [kellyEightMap, dist_poleAxis, dist_comm (embedR2ToR3 _),
        dist_poleAxis_embed_pentagon]
      fin_cases a <;> fin_cases c <;> first | contradiction | simp
    · -- 1 axial point `a` and 2 pentagon vertices `j, k`
      right; right
      simp only [kellyEightMap, dist_comm (embedR2ToR3 _), dist_poleAxis_embed_pentagon]
    · -- 2 axial points `b, c` and 1 pentagon vertex `i`
      have hbc : b ≠ c := fun h => hvw' (congrArg Sum.inl h)
      simp only [kellyEightMap, dist_poleAxis, dist_comm (embedR2ToR3 _),
        dist_poleAxis_embed_pentagon]
      fin_cases b <;> fin_cases c <;> first | contradiction | simp
    · -- 1 axial point `b` and 2 pentagon vertices `i, k`
      left
      simp only [kellyEightMap, dist_comm (embedR2ToR3 _), dist_poleAxis_embed_pentagon]
    · -- 1 axial point `c` and 2 pentagon vertices `i, j`
      right; left
      simp only [kellyEightMap, dist_comm (embedR2ToR3 _), dist_poleAxis_embed_pentagon]
    · -- 3 pentagon vertices `i, j, k`
      simp only [kellyEightMap, dist_embedR2ToR3]
      have hij : i ≠ j := fun h => huv' (congrArg Sum.inr h)
      have hjk : j ≠ k := fun h => hvw' (congrArg Sum.inr h)
      have hik : i ≠ k := fun h => huw' (congrArg Sum.inr h)
      rcases dist_pentagonVertex i j hij with h1 | h1 <;>
        rcases dist_pentagonVertex j k hjk with h2 | h2 <;>
          rcases dist_pentagonVertex k i hik.symm with h3 | h3
      · left; rw [h1, h2]
      · left; rw [h1, h2]
      · right; right; rw [h3, h1]
      · right; left; rw [h2, h3]
      · right; left; rw [h2, h3]
      · right; right; rw [h3, h1]
      · left; rw [h1, h2]
      · left; rw [h1, h2]
  · unfold kellyEightPoints
    rw [Set.ncard_range_of_injective kellyEightMap_injective, Nat.card_sum, Nat.card_fin,
      Nat.card_fin]

/-- Conditional completion of `erdos_503.variants.R3` (`FormalConjectures/ErdosProblems/503.lean`)
from `kelly_R3_lower_bound` and Croft's 3D upper bound. -/
theorem erdos_503_R3_of_upper_bound
    (hupper : ∀ m ∈ {(A.ncard) | (A : Set ℝ³) (_hA : A.IsIsosceles)}, m ≤ 8) :
    IsGreatest {(A.ncard) | (A : Set ℝ³) (_hA : A.IsIsosceles)} 8 :=
  ⟨⟨kellyEightPoints, kelly_R3_lower_bound.1, kelly_R3_lower_bound.2⟩, hupper⟩

/-!
## Part 4: Alweiss's General $\binom{n+1}{2}$ Lower Bound Construction in $\mathbb{R}^n$
-/

/-- Four-point distance-squared identity in $\mathbb{R}^n$:
for any $u, v, p, q \in \mathbb{R}^n$,
$\operatorname{dist}(u + v, p + q)^2 + \operatorname{dist}(u, v)^2 + \operatorname{dist}(p, q)^2 =
 \operatorname{dist}(u, p)^2 + \operatorname{dist}(u, q)^2 + \operatorname{dist}(v, p)^2 + \operatorname{dist}(v, q)^2$. -/
lemma dist_sq_add_four_point {n : ℕ} (u v p q : ℝ^n) :
    dist (u + v) (p + q) ^ 2 + dist u v ^ 2 + dist p q ^ 2 =
      dist u p ^ 2 + dist u q ^ 2 + dist v p ^ 2 + dist v q ^ 2 := by
  simp only [EuclideanSpace.dist_sq_eq, PiLp.add_apply, Real.dist_eq, sq_abs]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The regular simplex vertex $v_a \in \mathbb{R}^n$ ($a : \mathrm{Fin}(n+1)$):
for $a < n$, $v_a = e_a$ (the $a$-th standard basis vector);
for $a = n$, $v_n$ is the constant vector with all coordinates equal to $(1 - \sqrt{n+1}) / n$. -/
noncomputable def simplexVertex (n : ℕ) (a : Fin (n + 1)) : ℝ^n :=
  WithLp.equiv 2 (Fin n → ℝ) |>.symm fun i =>
    if a.1 < n then (if i.1 = a.1 then (1 : ℝ) else 0)
    else (1 - √(n + 1 : ℝ)) / (n : ℝ)

@[simp]
lemma simplexVertex_apply (n : ℕ) (a : Fin (n + 1)) (i : Fin n) :
    simplexVertex n a i =
      if a.1 < n then (if i.1 = a.1 then (1 : ℝ) else 0)
      else (1 - √(n + 1 : ℝ)) / (n : ℝ) := rfl

/-- Every pair of distinct vertices of `simplexVertex n` (for $n \ge 1$) has squared distance `2`. -/
lemma dist_sq_simplexVertex {n : ℕ} (hn : 1 ≤ n) (a b : Fin (n + 1)) (hab : a ≠ b) :
    dist (simplexVertex n a) (simplexVertex n b) ^ 2 = 2 := by
  classical
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  let c : ℝ := (1 - √(n + 1 : ℝ)) / (n : ℝ)
  have hc_eq : (c - 1) ^ 2 + ((n : ℝ) - 1) * c ^ 2 = 2 := by
    have hsq : √(n + 1 : ℝ) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
    dsimp [c]
    apply mul_left_cancel₀ hn_ne
    have h1 : (n : ℝ) * (((1 - √(n + 1 : ℝ)) / (n : ℝ) - 1) ^ 2 +
        ((n : ℝ) - 1) * ((1 - √(n + 1 : ℝ)) / (n : ℝ)) ^ 2) =
        (1 - √(n + 1 : ℝ)) ^ 2 - 2 * (1 - √(n + 1 : ℝ)) + (n : ℝ) := by
      field_simp
      ring
    rw [h1]
    linear_combination hsq
  rw [EuclideanSpace.dist_sq_eq]
  simp only [simplexVertex_apply, Real.dist_eq, sq_abs]
  by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
  · -- Both `a < n` and `b < n`: standard basis vectors `e_a` and `e_b` with `a ≠ b`
    simp only [ha, hb, ↓reduceIte]
    let ia : Fin n := ⟨a.1, ha⟩
    let ib : Fin n := ⟨b.1, hb⟩
    have hiab : ia ≠ ib := fun h => hab (Fin.ext (congrArg (fun x : Fin n => x.1) h))
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ia),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hiab.symm, Finset.mem_univ ib⟩)]
    have hia_eq : (if ia.1 = a.1 then (1 : ℝ) else 0) - (if ia.1 = b.1 then 1 else 0) = 1 := by
      have hne : a.1 ≠ b.1 := fun h => hab (Fin.ext h)
      simp [ia, hne]
    have hib_eq : (if ib.1 = a.1 then (1 : ℝ) else 0) - (if ib.1 = b.1 then 1 else 0) = -1 := by
      have hne : b.1 ≠ a.1 := fun h => hab (Fin.ext h.symm)
      simp [ib, hne]
    have hrest : ∑ x ∈ (Finset.univ.erase ia).erase ib,
        ((if x.1 = a.1 then (1 : ℝ) else 0) - (if x.1 = b.1 then 1 else 0)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxb : x ≠ ib := (Finset.mem_erase.mp hx).1
      have hxa : x ≠ ia := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hxa' : x.1 ≠ a.1 := fun h => hxa (Fin.ext h)
      have hxb' : x.1 ≠ b.1 := fun h => hxb (Fin.ext h)
      simp [hxa', hxb']
    rw [hia_eq, hib_eq, hrest]
    ring
  · -- `a < n` and `b = n`
    simp only [ha, hb, ↓reduceIte]
    let ia : Fin n := ⟨a.1, ha⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ia)]
    have hia_eq : ((if ia.1 = a.1 then (1 : ℝ) else 0) - c) ^ 2 = (1 - c) ^ 2 := by simp [ia]
    have hrest : ∑ x ∈ Finset.univ.erase ia,
        ((if x.1 = a.1 then (1 : ℝ) else 0) - c) ^ 2 = ∑ _x ∈ Finset.univ.erase ia, c ^ 2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxa : x ≠ ia := Finset.ne_of_mem_erase hx
      have hxa' : x.1 ≠ a.1 := fun h => hxa (Fin.ext h)
      simp [hxa']
    rw [hia_eq, hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ia),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
    linarith [hc_eq]
  · -- `a = n` and `b < n`
    simp only [ha, hb, ↓reduceIte]
    let ib : Fin n := ⟨b.1, hb⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ib)]
    have hib_eq : (c - (if ib.1 = b.1 then (1 : ℝ) else 0)) ^ 2 = (c - 1) ^ 2 := by simp [ib]
    have hrest : ∑ x ∈ Finset.univ.erase ib,
        (c - (if x.1 = b.1 then (1 : ℝ) else 0)) ^ 2 = ∑ _x ∈ Finset.univ.erase ib, c ^ 2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxb : x ≠ ib := Finset.ne_of_mem_erase hx
      have hxb' : x.1 ≠ b.1 := fun h => hxb (Fin.ext h)
      simp [hxb']
    rw [hib_eq, hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ib),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
    linarith [hc_eq]
  · exfalso
    apply hab
    ext
    omega

/-- Unified squared-distance formula for `simplexVertex n`:
`dist (simplexVertex n a) (simplexVertex n b) ^ 2 = if a = b then 0 else 2`. -/
lemma dist_sq_simplexVertex_ite {n : ℕ} (hn : 1 ≤ n) (a b : Fin (n + 1)) :
    dist (simplexVertex n a) (simplexVertex n b) ^ 2 = if a = b then 0 else 2 := by
  split_ifs with hab
  · subst hab; simp
  · exact dist_sq_simplexVertex hn a b hab

/-- Alweiss's map sending a 2-element subset $S \subseteq \mathrm{Fin}(n+1)$ to $\sum_{a \in S} v_a \in \mathbb{R}^n$. -/
noncomputable def alweissMap (n : ℕ) (S : Finset (Fin (n + 1))) : ℝ^n :=
  ∑ a ∈ S, simplexVertex n a

/-- For any two distinct 2-element subsets $S, T \subseteq \mathrm{Fin}(n+1)$, the squared distance
between `alweissMap n S` and `alweissMap n T` is either `2` or `4`. -/
lemma dist_sq_alweissMap {n : ℕ} (hn : 1 ≤ n) {S T : Finset (Fin (n + 1))}
    (hS : S.card = 2) (hT : T.card = 2) (hST : S ≠ T) :
    dist (alweissMap n S) (alweissMap n T) ^ 2 = 2 ∨
    dist (alweissMap n S) (alweissMap n T) ^ 2 = 4 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hT
  unfold alweissMap
  rw [Finset.sum_pair hab, Finset.sum_pair hcd]
  have h4 := dist_sq_add_four_point
    (simplexVertex n a) (simplexVertex n b) (simplexVertex n c) (simplexVertex n d)
  rw [dist_sq_simplexVertex hn a b hab, dist_sq_simplexVertex hn c d hcd,
    dist_sq_simplexVertex_ite hn a c, dist_sq_simplexVertex_ite hn a d,
    dist_sq_simplexVertex_ite hn b c, dist_sq_simplexVertex_ite hn b d] at h4
  have hnot_both1 : ¬ (a = c ∧ b = d) := by
    rintro ⟨rfl, rfl⟩
    exact hST rfl
  have hnot_both2 : ¬ (a = d ∧ b = c) := by
    rintro ⟨rfl, rfl⟩
    apply hST
    ext x
    simp [or_comm]
  by_cases hac : a = c <;> by_cases had : a = d <;> by_cases hbc : b = c <;> by_cases hbd : b = d
  all_goals
    try rw [if_pos hac] at h4
    try rw [if_neg hac] at h4
    try rw [if_pos had] at h4
    try rw [if_neg had] at h4
    try rw [if_pos hbc] at h4
    try rw [if_neg hbc] at h4
    try rw [if_pos hbd] at h4
    try rw [if_neg hbd] at h4
    first
    | exact (hcd ( hac.symm.trans had )).elim
    | exact (hab ( hac.trans hbc.symm )).elim
    | exact (hab ( had.trans hbd.symm )).elim
    | exact (hcd ( hbc.symm.trans hbd )).elim
    | exact (hnot_both1 ⟨hac, hbd⟩).elim
    | exact (hnot_both2 ⟨had, hbc⟩).elim
    | (left; linarith)
    | (right; linarith)

/-- Every pair of distinct points in the Alweiss configuration has distance $\sqrt{2}$ or $2$. -/
lemma dist_alweissMap {n : ℕ} (hn : 1 ≤ n) {S T : Finset (Fin (n + 1))}
    (hS : S.card = 2) (hT : T.card = 2) (hST : S ≠ T) :
    dist (alweissMap n S) (alweissMap n T) = √2 ∨
    dist (alweissMap n S) (alweissMap n T) = 2 := by
  rcases dist_sq_alweissMap hn hS hT hST with h | h
  · left; rw [← Real.sqrt_sq dist_nonneg, h]
  · right
    rw [← Real.sqrt_sq dist_nonneg, h, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]

/-- Alweiss's subset of $\mathbb{R}^n$ of size $\binom{n+1}{2}$. -/
noncomputable def alweissSet (n : ℕ) : Set (ℝ^n) :=
  (alweissMap n) '' ((Finset.univ : Finset (Fin (n + 1))).powersetCard 2 : Set (Finset (Fin (n + 1))))

/-- **Alweiss's Construction (`alweiss_construction`)**:
For every $n \ge 1$, `alweissSet n ⊆ ℝ^n` is a finite `IsIsosceles` set of exact cardinality
$\binom{n+1}{2}$. -/
theorem alweiss_construction {n : ℕ} (hn : 1 ≤ n) :
    (alweissSet n).Finite ∧ (alweissSet n).IsIsosceles ∧ (alweissSet n).ncard = (n + 1).choose 2 := by
  let P : Finset (Finset (Fin (n + 1))) := (Finset.univ : Finset (Fin (n + 1))).powersetCard 2
  have hP_card : P.card = (n + 1).choose 2 := by
    simp [P, Finset.card_powersetCard]
  have hinj : Set.InjOn (alweissMap n) (P : Set (Finset (Fin (n + 1)))) := by
    intro S hS T hT hST_eq
    by_contra hne
    have hS2 : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
    have hT2 : T.card = 2 := (Finset.mem_powersetCard.mp hT).2
    have h0 : dist (alweissMap n S) (alweissMap n T) ^ 2 = 0 := by
      rw [hST_eq, dist_self]; ring
    rcases dist_sq_alweissMap hn hS2 hT2 hne with h | h <;> linarith
  refine ⟨(P.finite_toSet).image (alweissMap n), ⟨?_, ?_⟩, ?_⟩
  · have hP_nonempty : P.Nonempty := by
      rw [← Finset.card_pos, hP_card]
      exact Nat.choose_pos (by omega)
    obtain ⟨S, hS⟩ := hP_nonempty
    exact ⟨alweissMap n S, ⟨S, hS, rfl⟩⟩
  · refine triplewise_isIsosceles_of_two_distances (d₁ := √2) (d₂ := 2) ?_
    rintro x ⟨S, hS, rfl⟩ y ⟨T, hT, rfl⟩ hxy
    have hS2 : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
    have hT2 : T.card = 2 := (Finset.mem_powersetCard.mp hT).2
    exact dist_alweissMap hn hS2 hT2 (fun hST => hxy (congrArg (alweissMap n) hST))
  · unfold alweissSet
    rw [hinj.ncard_image, Set.ncard_coe_finset, hP_card]

/-- **General Lower Bound for Erdős Problem 503 (`erdos_503.variants.lower_bound`)**:
For every $n \in \mathbb{N}$, there exists an `IsIsosceles` subset $A \subseteq \mathbb{R}^n$ with
$(n + 1).\mathrm{choose}\ 2 \le A.\mathrm{ncard}$, and when the set of isosceles cardinalities is
bounded above (as guaranteed by Blokhuis's theorem `erdos_503.variants.upper_bound`),
$(n + 1).\mathrm{choose}\ 2 \le \mathrm{sSup}\ \{A.\mathrm{ncard} \mid A.\mathrm{IsIsosceles}\}$. -/
theorem erdos_503_exists_isIsosceles_ge_choose (n : ℕ) :
    ∃ A : Set (ℝ^n), A.IsIsosceles ∧ (n + 1).choose 2 ≤ A.ncard := by
  by_cases hn : 1 ≤ n
  · obtain ⟨_, hIso, hcard⟩ := alweiss_construction hn
    exact ⟨alweissSet n, hIso, hcard.symm.le⟩
  · have hn0 : n = 0 := by omega
    subst hn0
    refine ⟨{0}, ⟨⟨0, rfl⟩, fun x _ y _ _ _ hxy _ _ => (hxy (Subsingleton.elim x y)).elim⟩, ?_⟩
    simp

theorem erdos_503_lower_bound_of_bddAbove (n : ℕ)
    (hbdd : BddAbove {(A.ncard) | (A : Set (ℝ^n)) (_hA : A.IsIsosceles)}) :
    (n + 1).choose 2 ≤ sSup {(A.ncard) | (A : Set (ℝ^n)) (_hA : A.IsIsosceles)} := by
  obtain ⟨A, hIso, hle⟩ := erdos_503_exists_isIsosceles_ge_choose n
  exact le_trans hle (le_csSup hbdd ⟨A, hIso, rfl⟩)

end Erdos503

#print axioms Erdos503.erdos_503.variants.R0
#print axioms Erdos503.erdos_503.variants.R1
#print axioms Erdos503.kelly_R2_lower_bound
#print axioms Erdos503.kelly_R3_lower_bound
#print axioms Erdos503.alweiss_construction
#print axioms Erdos503.erdos_503_exists_isIsosceles_ge_choose
#print axioms Erdos503.erdos_503_lower_bound_of_bddAbove
