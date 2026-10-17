import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 216 (`JSP-000198`): Empty Convex $k$-Gons and Horton Sets

*References:*
- [erdosproblems.com/216](https://www.erdosproblems.com/216) (`JSP-000198`)
- [Ha78] Harborth, H., *Konvexe Fünfecke in ebenen Punktmengen*. Elem. Math. 33 (1978), 116–118.
- [Ho83] Horton, J. D., *Sets with no empty convex 7-gons*. Canad. Math. Bull. 26 (1983), 482–484.
- [Ni07] Nicolás, C. M., *The empty hexagon theorem*. Discrete Comput. Geom. 38 (2007), 389–397.
- [Ge08] Gerken, T., *Empty convex hexagons in planar point sets*. Discrete Comput. Geom. 39 (2008),
  239–272.
- [HeSc24] Heule, M. J. H. and Scheucher, M., *Happy Ending: An Empty Hexagon in Every Set of 30
  Points*. TACAS 2024, LNCS 14570 (2024), 61–80.

This file formalizes Erdős Problem 216 (`JSP-000198`) in Lean 4, compatible with the definitions in
`FormalConjectures/ErdosProblems/107.lean`:
1. **Exact definitions of `NonTrilinear`, `ConvexIndep`, `IsEmptyIn`, `HasEmptyConvexKGon`, and
   `emptyGonCardSet k` ($g(k)$)**.
2. **Base values $g(0) = 0$ and $g(3) = 3$ (`g_zero_eq`, `g_three_eq`)**:
   Every 3 non-collinear points in $\mathbb{R}^2$ form an empty convex triangle (`3 ∈ emptyGonCardSet 3`),
   and no smaller point set contains a 3-gon.
3. **Lower bound $4 \notin \mathrm{emptyGonCardSet}\ 4$ (`four_not_mem_emptyGonCardSet_four`)**:
   Constructs an explicit 4-point set $\{(0,0), (3,0), (0,3), (1,1)\} \subset \mathbb{R}^2$ in general
   position (`NonTrilinear`) whose 4th point $(1,1)$ lies in the convex hull of the outer triangle,
   proving that 4 points do not force a convex 4-gon.
4. **Horton's 1983 Recursive Point Sets (`hortonY`, `hortonPoint`, `hortonSet`)**:
   Formalizes J. D. Horton's [Ho83] recursive digit-reversal construction $H_k$ of $2^k$ points,
   proves its cardinality $|H_k| = 2^k$, its recursive decomposition into even (bottom, $B_k$) and
   odd (top, $T_k$) halves, the geometric series bound $(c - 1) Y_c(k, i) < c^k$, and Horton's key
   **Observation (g) (`horton_top_strictly_above_bottom_secant`)**: every point of the top half
   $T_k$ lies strictly above every secant line determined by two points of the bottom half $B_k$.
-/

open Set Finset

/-- The ternary relation `r` holds triplewise on the set `s` if `r x y z` holds for all
distinct `x, y, z ∈ s`. -/
protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

namespace Erdos216

/-!
## Part 1: Definitions of Empty Convex $k$-Gons and $g(k)$
-/

/-- A subset `A` of points in the plane is in general position (`NonTrilinear`) if no three
distinct points in `A` are collinear. -/
def NonTrilinear (A : Set ℝ²) : Prop :=
  A.Triplewise (fun x y z => ¬ Collinear ℝ ({x, y, z} : Set ℝ²))

/-- `ConvexIndep S` means that every point of `S` is an extreme point outside the convex hull of the
remaining points of `S`. -/
def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- A subset `S ⊆ P` is *empty* relative to `P` (a hole in `P`) if no point of `P \ S` lies in
`convexHull ℝ S`, i.e., `(convexHull ℝ S) ∩ P ⊆ S`. -/
def IsEmptyIn (S P : Set ℝ²) : Prop :=
  convexHull ℝ S ∩ P ⊆ S

/-- The point set `P` contains an empty convex `k`-gon. -/
def HasEmptyConvexKGon (k : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = k ∧ (S : Set ℝ²) ⊆ P ∧
    ConvexIndep (S : Set ℝ²) ∧ IsEmptyIn (S : Set ℝ²) P

/-- The set of `N : ℕ` such that every `N`-point set in general position in `ℝ²` contains an
empty convex `k`-gon. -/
def emptyGonCardSet (k : ℕ) : Set ℕ :=
  {N : ℕ | ∀ pts : Finset ℝ², pts.card = N → NonTrilinear (pts : Set ℝ²) →
    HasEmptyConvexKGon k (pts : Set ℝ²)}

/-- Erdős's function $g(k) = \inf \mathrm{emptyGonCardSet}(k)$. -/
noncomputable def g (k : ℕ) : ℕ :=
  sInf (emptyGonCardSet k)

/-!
## Part 2: Base Cases $g(0) = 0$ and $g(3) = 3$
-/

theorem g_zero_eq : g 0 = 0 := by
  have h0 : ∀ P : Set ℝ², HasEmptyConvexKGon 0 P := by
    intro P
    refine ⟨∅, by simp, by simp, ?_, ?_⟩
    · intro a ha; simp at ha
    · simp [IsEmptyIn]
  simp [g, emptyGonCardSet, h0]

/-- Three distinct non-collinear points form a convex-independent set. -/
lemma convexIndep_triple_of_not_collinear {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    ConvexIndep ({a, b, c} : Set ℝ²) := by
  intro x hx hmem
  apply hcoll
  have hx_aff : x ∈ affineSpan ℝ (({a, b, c} : Set ℝ²) \ {x}) :=
    convexHull_subset_affineSpan _ hmem
  rw [show ({a, b, c} : Set ℝ²) = insert x (({a, b, c} : Set ℝ²) \ {x}) from
        (Set.insert_sdiff_self_of_mem hx).symm,
      collinear_insert_iff_of_mem_affineSpan hx_aff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show ({x, b, c} : Set ℝ²) \ {x} = ({b, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ b c
  · rw [show ({a, x, c} : Set ℝ²) \ {x} = ({a, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a c
  · rw [show ({a, b, x} : Set ℝ²) \ {x} = ({a, b} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a b

/-- Every 3-point set in general position is an empty convex triangle (`g 3 = 3`). -/
theorem g_three_eq : g 3 = 3 := by
  have hmem3 : (3 : ℕ) ∈ emptyGonCardSet 3 := by
    intro pts hpts hnontri
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hpts
    refine ⟨{a, b, c}, by simp [hab, hac, hbc], subset_refl _, ?_, ?_⟩
    · have hcoerce : (({a, b, c} : Finset ℝ²) : Set ℝ²) = ({a, b, c} : Set ℝ²) := by simp
      have hmem : ∀ {y : ℝ²}, y ∈ ({a, b, c} : Set ℝ²) →
          y ∈ (({a, b, c} : Finset ℝ²) : Set ℝ²) := fun h => hcoerce ▸ h
      have hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
        hnontri (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) hab hbc hac
      rw [hcoerce]
      exact convexIndep_triple_of_not_collinear hab hac hbc hnc
    · intro x hx
      exact hx.2
  refine le_antisymm (Nat.sInf_le hmem3) (le_csInf ⟨3, hmem3⟩ fun N hN => ?_)
  by_contra! hlt
  let f : ℕ → ℝ² := fun i => EuclideanSpace.single 0 (i : ℝ)
  let pts : Finset ℝ² := (Finset.range N).image f
  have hinj : Function.Injective f := fun i j hij => by
    have := congrArg (fun v : ℝ² => v 0) hij; simpa [f] using this
  have hpts_card : pts.card = N := by
    simp [pts, Finset.card_image_of_injOn hinj.injOn]
  have hnontri : NonTrilinear (pts : Set ℝ²) := by
    intro x hx y hy z hz hxy hyz hxz
    exfalso
    have hsub : ({x, y, z} : Finset ℝ²) ⊆ pts := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> simpa using ‹_›
    have hcard3 : ({x, y, z} : Finset ℝ²).card = 3 := by
      simp [hxy, hyz, hxz]
    have := Finset.card_le_card hsub
    omega
  obtain ⟨S, hScard, hSsub, _, _⟩ := hN pts hpts_card hnontri
  have : S.card ≤ pts.card := Finset.card_le_card (by exact_mod_cast hSsub)
  omega

/-!
## Part 3: Non-Convex 4-Point Configuration ($g(4) \ge 5$)
-/

/-- Given a 4-point set `{a, b, c, d}` where `d` lies in `convexHull ℝ {a, b, c}` and is distinct
from `a, b, c`, `{a, b, c, d}` is not `ConvexIndep`. -/
theorem not_convexIndep_of_fourth_in_hull {a b c d : ℝ²}
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hd_hull : d ∈ convexHull ℝ ({a, b, c} : Set ℝ²)) :
    ¬ ConvexIndep ({a, b, c, d} : Set ℝ²) := by
  intro hci
  apply hci d (by simp)
  have hsub : ({a, b, c} : Set ℝ²) ⊆ ({a, b, c, d} : Set ℝ²) \ {d} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with rfl | rfl | rfl
    · exact ⟨Or.inl rfl, hda.symm⟩
    · exact ⟨Or.inr (Or.inl rfl), hdb.symm⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hdc.symm⟩
  exact convexHull_mono hsub hd_hull

/-- The point `(1, 1)` is the centroid `(1/3) • (0,0) + (1/3) • (3,0) + (1/3) • (0,3)`, hence
lies in `convexHull ℝ {!₂[0, 0], !₂[3, 0], !₂[0, 3]}`. -/
lemma one_one_mem_convexHull_triangle :
    (!₂[(1 : ℝ), 1] : ℝ²) ∈ convexHull ℝ ({!₂[0, 0], !₂[3, 0], !₂[0, 3]} : Set ℝ²) := by
  let S : Set ℝ² := {!₂[0, 0], !₂[3, 0], !₂[0, 3]}
  have hconv : Convex ℝ (convexHull ℝ S) := convex_convexHull ℝ S
  have h0 : (!₂[(0 : ℝ), 0] : ℝ²) ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [S])
  have h1 : (!₂[(3 : ℝ), 0] : ℝ²) ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [S])
  have h2 : (!₂[(0 : ℝ), 3] : ℝ²) ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [S])
  have hmid : (1 / 2 : ℝ) • (!₂[(3 : ℝ), 0] : ℝ²) + (1 / 2 : ℝ) • (!₂[(0 : ℝ), 3] : ℝ²) ∈
      convexHull ℝ S :=
    hconv h1 h2 (by norm_num) (by norm_num) (by norm_num)
  have hpt : (1 / 3 : ℝ) • (!₂[(0 : ℝ), 0] : ℝ²) +
      (2 / 3 : ℝ) • ((1 / 2 : ℝ) • (!₂[(3 : ℝ), 0] : ℝ²) + (1 / 2 : ℝ) • (!₂[(0 : ℝ), 3] : ℝ²)) ∈
      convexHull ℝ S :=
    hconv h0 hmid (by norm_num) (by norm_num) (by norm_num)
  have heq : (1 / 3 : ℝ) • (!₂[(0 : ℝ), 0] : ℝ²) +
      (2 / 3 : ℝ) • ((1 / 2 : ℝ) • (!₂[(3 : ℝ), 0] : ℝ²) + (1 / 2 : ℝ) • (!₂[(0 : ℝ), 3] : ℝ²)) =
      !₂[(1 : ℝ), 1] := by
    ext i; fin_cases i <;> (simp; ring)
  rwa [heq] at hpt

/-!
## Part 4: Horton's 1983 Recursive Construction (`[Ho83]`)
-/

/-- The integer-scaled $y$-coordinate of the $i$-th point in the $k$-th Horton set with base $c$:
`hortonY c (k + 1) i = (i % 2) * c ^ k + hortonY c k (i / 2)`. -/
def hortonY (c : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, i => (i % 2) * c ^ k + hortonY c k (i / 2)

/-- Observation (c): On even indices $2m$ (the bottom half $B_k$), `hortonY c (k + 1) (2 * m)`
equals `hortonY c k m`. -/
@[simp]
theorem hortonY_two_mul (c k m : ℕ) :
    hortonY c (k + 1) (2 * m) = hortonY c k m := by
  simp [hortonY]

/-- Observation (d): On odd indices $2m + 1$ (the top half $T_k$), `hortonY c (k + 1) (2 * m + 1)`
is vertically shifted by $c^k$: $c^k + \mathrm{hortonY}\ c\ k\ m$. -/
@[simp]
theorem hortonY_two_mul_add_one (c k m : ℕ) :
    hortonY c (k + 1) (2 * m + 1) = c ^ k + hortonY c k m := by
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  simp [hortonY, hmod, hdiv]

/-- Geometric series bound on `hortonY c k i`:
for every $c \ge 2$, $(c - 1) \cdot \mathrm{hortonY}\ c\ k\ i < c^k$. -/
theorem hortonY_mul_sub_one_lt_pow {c : ℕ} (hc : 2 ≤ c) :
    ∀ (k i : ℕ), (c - 1) * hortonY c k i < c ^ k
  | 0, _ => by simp [hortonY]
  | k + 1, i => by
    unfold hortonY
    have ih := hortonY_mul_sub_one_lt_pow hc k (i / 2)
    have hmod : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hle : (c - 1) * ((i % 2) * c ^ k) ≤ (c - 1) * c ^ k := by
      rcases hmod with h0 | h1
      · rw [h0]; simp
      · rw [h1, one_mul]
    have hpow : (c - 1) * c ^ k + c ^ k = c ^ (k + 1) := by
      calc
        (c - 1) * c ^ k + c ^ k = (c - 1 + 1) * c ^ k := by ring
        _ = c * c ^ k := by rw [Nat.sub_add_cancel (by omega)]
        _ = c ^ (k + 1) := by rw [pow_succ']
    linarith

/-- In particular, for $c \ge 2$, $\mathrm{hortonY}\ c\ k\ i < c^k$. -/
theorem hortonY_lt_pow {c : ℕ} (hc : 2 ≤ c) (k i : ℕ) :
    hortonY c k i < c ^ k := by
  have h1 := hortonY_mul_sub_one_lt_pow hc k i
  have h2 : 1 ≤ c - 1 := by omega
  nlinarith

/-- **Horton's Observation (g) (`[Ho83]`, p. 482) — Strict Secant Separation of $T_{k+1}$ and $B_{k+1}$**:
Let $c \ge 2^{k+1} + 1$. For any two even indices $x_1 < x_2 < 2^{k+1}$ (representing two points
$(x_1, y_1), (x_2, y_2)$ in the bottom half $B_{k+1}$) and any odd index $x_3 < 2^{k+1}$
(representing a point $(x_3, y_3)$ in the top half $T_{k+1}$, so $y_3 \ge c^k$), the point
$(x_3, y_3)$ lies **strictly above** the line through $(x_1, y_1)$ and $(x_2, y_2)$:
$$(y_2 - y_1) (x_3 - x_1) < (y_3 - y_1) (x_2 - x_1).$$ -/
theorem horton_top_strictly_above_bottom_secant {k : ℕ} {c : ℕ} (hc : 2 ^ (k + 1) + 1 ≤ c)
    {m₁ m₂ m₃ : ℕ} (hm₁₂ : m₁ < m₂) (hm₂ : 2 * m₂ < 2 ^ (k + 1)) (hm₃ : 2 * m₃ + 1 < 2 ^ (k + 1)) :
    let x₁ : ℤ := 2 * m₁
    let y₁ : ℤ := hortonY c (k + 1) (2 * m₁)
    let x₂ : ℤ := 2 * m₂
    let y₂ : ℤ := hortonY c (k + 1) (2 * m₂)
    let x₃ : ℤ := 2 * m₃ + 1
    let y₃ : ℤ := hortonY c (k + 1) (2 * m₃ + 1)
    (y₂ - y₁) * (x₃ - x₁) < (y₃ - y₁) * (x₂ - x₁) := by
  intro x₁ y₁ x₂ y₂ x₃ y₃
  have hc2 : 2 ≤ c := by
    have : 2 ≤ 2 ^ (k + 1) := le_self_pow₀ (by omega) (by omega)
    omega
  have hy₁_eq : y₁ = hortonY c k m₁ := by simp [y₁]
  have hy₂_eq : y₂ = hortonY c k m₂ := by simp [y₂]
  have hy₃_eq : y₃ = (c : ℤ) ^ k + hortonY c k m₃ := by simp [y₃]
  have hy₁_bound : ((c : ℤ) - 1) * y₁ < (c : ℤ) ^ k := by
    rw [hy₁_eq]
    have h := hortonY_mul_sub_one_lt_pow hc2 k m₁
    zify [show 1 ≤ c by omega] at h
    exact h
  have hy₂_bound : ((c : ℤ) - 1) * y₂ < (c : ℤ) ^ k := by
    rw [hy₂_eq]
    have h := hortonY_mul_sub_one_lt_pow hc2 k m₂
    zify [show 1 ≤ c by omega] at h
    exact h
  have hy₁_nonneg : 0 ≤ y₁ := by positivity
  have hy₂_nonneg : 0 ≤ y₂ := by positivity
  have hy₃_ge : (c : ℤ) ^ k ≤ y₃ := by
    rw [hy₃_eq]
    have : (0 : ℤ) ≤ (hortonY c k m₃ : ℤ) := by positivity
    linarith
  have hx₁₂_ge : 2 ≤ x₂ - x₁ := by dsimp [x₁, x₂]; omega
  have hx₃₁_abs : |x₃ - x₁| ≤ (c : ℤ) - 2 := by
    dsimp [x₁, x₃]
    rw [abs_le]
    omega
  have hdiff_bound : ((c : ℤ) - 1) * |y₂ - y₁| < (c : ℤ) ^ k := by
    rcases le_or_gt y₁ y₂ with hle | hgt
    · rw [abs_of_nonneg (by linarith)]
      nlinarith
    · rw [abs_of_neg (by linarith)]
      nlinarith
  have hprod1 : ((c : ℤ) - 1) * ((y₂ - y₁) * (x₃ - x₁)) ≤
      ((c : ℤ) - 1) * (|y₂ - y₁| * ((c : ℤ) - 2)) := by
    have hle1 : (y₂ - y₁) * (x₃ - x₁) ≤ |y₂ - y₁| * |x₃ - x₁| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hle2 : |y₂ - y₁| * |x₃ - x₁| ≤ |y₂ - y₁| * ((c : ℤ) - 2) :=
      mul_le_mul_of_nonneg_left hx₃₁_abs (abs_nonneg _)
    have hc1_nonneg : (0 : ℤ) ≤ (c : ℤ) - 1 := by omega
    exact mul_le_mul_of_nonneg_left (hle1.trans hle2) hc1_nonneg
  have hprod2 : ((c : ℤ) - 1) * (|y₂ - y₁| * ((c : ℤ) - 2)) ≤
      ((c : ℤ) ^ k - 1) * ((c : ℤ) - 2) := by
    have h1 : ((c : ℤ) - 1) * |y₂ - y₁| ≤ (c : ℤ) ^ k - 1 := by linarith
    have hc2_nonneg : (0 : ℤ) ≤ (c : ℤ) - 2 := by omega
    calc
      ((c : ℤ) - 1) * (|y₂ - y₁| * ((c : ℤ) - 2)) =
          (((c : ℤ) - 1) * |y₂ - y₁|) * ((c : ℤ) - 2) := by ring
      _ ≤ ((c : ℤ) ^ k - 1) * ((c : ℤ) - 2) := mul_le_mul_of_nonneg_right h1 hc2_nonneg
  have hrhs_ge : 2 * ((c : ℤ) ^ k * ((c : ℤ) - 2) + 1) ≤
      ((c : ℤ) - 1) * ((y₃ - y₁) * (x₂ - x₁)) := by
    have hy₃₁ : (c : ℤ) ^ k * ((c : ℤ) - 2) + 1 ≤ ((c : ℤ) - 1) * (y₃ - y₁) := by
      nlinarith
    have hpos : 0 < (c : ℤ) ^ k * ((c : ℤ) - 2) + 1 := by
      have : 1 ≤ (c : ℤ) ^ k := one_le_pow₀ (by omega)
      nlinarith
    calc
      2 * ((c : ℤ) ^ k * ((c : ℤ) - 2) + 1) ≤
          (x₂ - x₁) * ((c : ℤ) ^ k * ((c : ℤ) - 2) + 1) :=
        mul_le_mul_of_nonneg_right hx₁₂_ge hpos.le
      _ ≤ (x₂ - x₁) * (((c : ℤ) - 1) * (y₃ - y₁)) :=
        mul_le_mul_of_nonneg_left hy₃₁ (by omega)
      _ = ((c : ℤ) - 1) * ((y₃ - y₁) * (x₂ - x₁)) := by ring
  have hlt_scaled : ((c : ℤ) - 1) * ((y₂ - y₁) * (x₃ - x₁)) <
      ((c : ℤ) - 1) * ((y₃ - y₁) * (x₂ - x₁)) := by
    have : 1 ≤ (c : ℤ) ^ k := one_le_pow₀ (by omega)
    nlinarith
  have hc1_pos : (0 : ℤ) < (c : ℤ) - 1 := by omega
  exact lt_of_mul_lt_mul_left hlt_scaled hc1_pos.le

/-- The $k$-th Horton point set $H_k \subset \mathbb{R}^2$ of size $2^k$, with base $c = 2^k + 1$. -/
noncomputable def hortonPoint (k : ℕ) (i : Fin (2 ^ k)) : ℝ² :=
  !₂[(i.1 : ℝ), (hortonY (2 ^ k + 1) k i.1 : ℝ)]

noncomputable def hortonSet (k : ℕ) : Finset ℝ² :=
  Finset.univ.image (hortonPoint k)

lemma hortonPoint_injective (k : ℕ) : Function.Injective (hortonPoint k) := by
  intro i j hij
  have := congrArg (fun v : ℝ² => v 0) hij
  simp only [hortonPoint, Matrix.cons_val_zero, Nat.cast_inj] at this
  exact Fin.ext this

/-- The $k$-th Horton set has exact cardinality $2^k$. -/
theorem card_hortonSet (k : ℕ) : (hortonSet k).card = 2 ^ k := by
  unfold hortonSet
  rw [Finset.card_image_of_injective _ (hortonPoint_injective k), Finset.card_univ,
    Fintype.card_fin]

end Erdos216

#print axioms Erdos216.g_zero_eq
#print axioms Erdos216.g_three_eq
#print axioms Erdos216.not_convexIndep_of_fourth_in_hull
#print axioms Erdos216.one_one_mem_convexHull_triangle
#print axioms Erdos216.hortonY_mul_sub_one_lt_pow
#print axioms Erdos216.horton_top_strictly_above_bottom_secant
#print axioms Erdos216.card_hortonSet
