/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 602 (JSP-000489)

*Reference:* [erdosproblems.com/602](https://www.erdosproblems.com/602)

We formalize the solved variants and disproofs in `FormalConjectures/ErdosProblems/602.lean`:
- `erdos_602.variants.countable_index`: Every countable family of countably infinite sets has Property B (Bernstein's Lemma).
- `erdos_602.variants.disjoint`: Every pairwise-disjoint family of infinite sets has Property B.
- `erdos_602.variants.two_sets`: Every pair of infinite sets whose intersection is finite and of size $\neq 1$ has Property B.
- `erdos_602.variants.single_set`, `erdos_602.variants.empty_index`, `erdos_602.variants.unique_index`: Foundational cases.
- `disjoint_without_infinite_claim.disproof`: Dropping the infinite-set hypothesis refutes the disjoint Property B claim.
- Scope certificates and disjoint-refinement reductions below are partial results only.

The original problem (Erdős 1987, p. 227, §12) permits an arbitrary ground set
and arbitrary index set. The full statement `originalProblem` below is a proposition,
not a proved theorem. Countability of individual members does not imply countability
of their union; the contrary renaming explanation in Formal Conjectures is invalid.
-/

open Set

namespace Erdos602

universe u v

/-- A set `A ⊆ α` is **monochromatic** under a 2-colouring `f : α → Fin 2`
if all elements of `A` receive the same colour. -/
def IsMonochromatic {α : Type*} (f : α → Fin 2) (A : Set α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, f x = f y

/-- A family `(A_i)_{i ∈ I}` of subsets of `α` has **Property B** if there exists
a 2-colouring `f : α → Fin 2` such that no `A_i` is monochromatic. -/
def HasPropertyB {α : Type*} (I : Type*) (A : I → Set α) : Prop :=
  ∃ f : α → Fin 2, ∀ i, ¬IsMonochromatic f (A i)

/-- The exact original question, with neither the ground set nor the index restricted
    to be countable. This definition asserts no proof of the proposition. -/
def originalProblem : Prop :=
  ∀ {α : Type u} {I : Type v} (A : I → Set α),
    (∀ i, (A i).Countable ∧ (A i).Infinite) →
    (∀ i j, i ≠ j → (A i ∩ A j).Finite) →
    (∀ i j, i ≠ j → Set.ncard (A i ∩ A j) ≠ 1) →
    HasPropertyB I A

/--
**Pairwise disjoint families.**
If the `A_i` are pairwise disjoint and infinite, then Property B holds.
-/
theorem erdos_602.variants.disjoint :
    ∀ {α : Type*} {I : Type*} (A : I → Set α),
      (∀ i, (A i).Infinite) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
      HasPropertyB I A := by
  intro α I A hInfinite hDisjoint
  have ha_b : ∀ i, ∃ a b : α, a ∈ A i ∧ b ∈ A i ∧ a ≠ b := by
    intro i
    obtain ⟨a, ha⟩ := (hInfinite i).nonempty
    have hA2 : (A i \ {a}).Nonempty :=
      Set.Infinite.nonempty ((hInfinite i).sdiff (Set.finite_singleton a))
    obtain ⟨b, hbA, hba⟩ := hA2
    simp only [Set.mem_singleton_iff] at hba
    exact ⟨a, b, ha, hbA, fun h => hba h.symm⟩
  choose a_fn b_fn ha_mem hb_mem hab_ne using ha_b
  have key : ∀ i j, a_fn i ≠ b_fn j := by
    intro i j haj
    by_cases hij : i = j
    · subst hij; exact hab_ne i haj
    · have hdisj := hDisjoint i j hij
      rw [Set.disjoint_left] at hdisj
      have hbj : b_fn j ∈ A j := hb_mem j
      rw [← haj] at hbj
      exact hdisj (ha_mem i) hbj
  classical
  let f : α → Fin 2 := fun n => if ∃ i, n = b_fn i then 1 else 0
  refine ⟨f, fun i => ?_⟩
  intro hMono
  have hfa : f (a_fn i) = 0 := by
    simp only [f]
    rw [if_neg]
    rintro ⟨j, hj⟩
    exact key i j hj
  have hfb : f (b_fn i) = 1 := by
    simp only [f]
    rw [if_pos ⟨i, rfl⟩]
  have hne := hMono (a_fn i) (ha_mem i) (b_fn i) (hb_mem i)
  rw [hfa, hfb] at hne
  exact absurd hne (by decide)

/-! ### Countable index set case (Bernstein's Lemma) -/

/-- Recursive construction of the finite set of already-chosen witness elements
at stage `n : ℕ`. At each stage `n`, we pick two distinct elements `x_n, y_n` from
`A n \ S_n` and insert both into `S_{n+1}`. -/
private noncomputable def bernsteinStep {α : Type*} (A : ℕ → Set α) (hInf : ∀ i, (A i).Infinite) :
    ℕ → {S : Set α // S.Finite}
  | 0 => ⟨∅, Set.finite_empty⟩
  | n + 1 =>
    let S := (bernsteinStep A hInf n).1
    let hS := (bernsteinStep A hInf n).2
    let x := ((hInf n).sdiff hS).nonempty.some
    let y := (((hInf n).sdiff hS).sdiff (Set.finite_singleton x)).nonempty.some
    ⟨insert x (insert y S), (hS.insert y).insert x⟩

private noncomputable def bernsteinX {α : Type*} (A : ℕ → Set α) (hInf : ∀ i, (A i).Infinite)
    (n : ℕ) : α :=
  ((hInf n).sdiff (bernsteinStep A hInf n).2).nonempty.some

private noncomputable def bernsteinY {α : Type*} (A : ℕ → Set α) (hInf : ∀ i, (A i).Infinite)
    (n : ℕ) : α :=
  (((hInf n).sdiff (bernsteinStep A hInf n).2).sdiff
    (Set.finite_singleton (bernsteinX A hInf n))).nonempty.some

private lemma bernsteinStep_succ {α : Type*} (A : ℕ → Set α) (hInf : ∀ i, (A i).Infinite)
    (n : ℕ) :
    (bernsteinStep A hInf (n + 1)).1 =
      insert (bernsteinX A hInf n) (insert (bernsteinY A hInf n) (bernsteinStep A hInf n).1) :=
  rfl

private lemma bernsteinStep_mono {α : Type*} (A : ℕ → Set α) (hInf : ∀ i, (A i).Infinite) :
    Monotone (fun n => (bernsteinStep A hInf n).1) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [bernsteinStep_succ]
  exact (Set.subset_insert _ _).trans (Set.subset_insert _ _)

private lemma bernsteinX_mem {α : Type*} (A : ℕ → Set α) (hInf : ∀ i, (A i).Infinite) (n : ℕ) :
    bernsteinX A hInf n ∈ A n ∧ bernsteinX A hInf n ∉ (bernsteinStep A hInf n).1 :=
  ((hInf n).sdiff (bernsteinStep A hInf n).2).nonempty.some_mem

private lemma bernsteinY_mem {α : Type*} (A : ℕ → Set α) (hInf : ∀ i, (A i).Infinite) (n : ℕ) :
    bernsteinY A hInf n ∈ A n ∧
      bernsteinY A hInf n ∉ (bernsteinStep A hInf n).1 ∧
      bernsteinY A hInf n ≠ bernsteinX A hInf n := by
  have h := (((hInf n).sdiff (bernsteinStep A hInf n).2).sdiff
    (Set.finite_singleton (bernsteinX A hInf n))).nonempty.some_mem
  exact ⟨h.1.1, h.1.2, h.2⟩

private lemma bernsteinX_ne_bernsteinY {α : Type*} (A : ℕ → Set α) (hInf : ∀ i, (A i).Infinite)
    (i j : ℕ) : bernsteinX A hInf i ≠ bernsteinY A hInf j := by
  intro hxy
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hx_in : bernsteinX A hInf i ∈ (bernsteinStep A hInf (i + 1)).1 := by
      rw [bernsteinStep_succ]
      exact Set.mem_insert _ _
    have hx_in_j : bernsteinX A hInf i ∈ (bernsteinStep A hInf j).1 :=
      bernsteinStep_mono A hInf (Nat.succ_le_of_lt hij) hx_in
    rw [hxy] at hx_in_j
    exact (bernsteinY_mem A hInf j).2.1 hx_in_j
  · exact (bernsteinY_mem A hInf i).2.2 hxy.symm
  · have hy_in : bernsteinY A hInf j ∈ (bernsteinStep A hInf (j + 1)).1 := by
      rw [bernsteinStep_succ]
      exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hy_in_i : bernsteinY A hInf j ∈ (bernsteinStep A hInf i).1 :=
      bernsteinStep_mono A hInf (Nat.succ_le_of_lt hji) hy_in
    rw [← hxy] at hy_in_i
    exact (bernsteinX_mem A hInf i).2 hy_in_i

/-- **Bernstein's Lemma for countable families:** every countable family of infinite sets
has Property B, without requiring any intersection conditions. -/
theorem bernstein_countable_propertyB {α : Type*} (A : ℕ → Set α)
    (hInf : ∀ i, (A i).Infinite) : HasPropertyB ℕ A := by
  classical
  let f : α → Fin 2 := fun x => if ∃ j, x = bernsteinY A hInf j then 1 else 0
  refine ⟨f, fun i hMono => ?_⟩
  have hfx : f (bernsteinX A hInf i) = 0 := by
    simp only [f]
    rw [if_neg]
    rintro ⟨j, hj⟩
    exact bernsteinX_ne_bernsteinY A hInf i j hj
  have hfy : f (bernsteinY A hInf i) = 1 := by
    simp only [f]
    rw [if_pos ⟨i, rfl⟩]
  have hne := hMono (bernsteinX A hInf i) (bernsteinX_mem A hInf i).1
    (bernsteinY A hInf i) (bernsteinY_mem A hInf i).1
  rw [hfx, hfy] at hne
  exact absurd hne (by decide)

/--
**Countable index set case.**

If the index set is countable, the answer is yes, and the intersection
condition is unnecessary. This is Bernstein's Lemma:
every countable system of infinite sets has Property B.
-/
theorem erdos_602.variants.countable_index :
    ∀ {α : Type*} (A : ℕ → Set α),
      (∀ i, (A i).Countable ∧ (A i).Infinite) →
      (∀ i j, i ≠ j → (A i ∩ A j).Finite) →
      (∀ i j, i ≠ j → Set.ncard (A i ∩ A j) ≠ 1) →
      HasPropertyB ℕ A := by
  intro α A hCountInf _hFin _hNcard
  exact bernstein_countable_propertyB A (fun i => (hCountInf i).2)

/--
**Single infinite set.**
-/
theorem erdos_602.variants.single_set {α : Type*} (A : Set α) (hA : A.Infinite) :
    ∃ f : α → Fin 2, ¬IsMonochromatic f A := by
  classical
  obtain ⟨a, ha⟩ := hA.nonempty
  have hA2 : (A \ {a}).Nonempty :=
    Set.Infinite.nonempty (hA.sdiff (Set.finite_singleton a))
  obtain ⟨b, hbA, hba⟩ := hA2
  simp only [Set.mem_singleton_iff] at hba
  refine ⟨fun n => if n = b then 1 else 0, fun hMono => ?_⟩
  have h0 : (fun n => if n = b then (1 : Fin 2) else 0) a = 0 := by
    simp [Ne.symm hba]
  have h1 : (fun n => if n = b then (1 : Fin 2) else 0) b = 1 := by
    simp
  have := hMono a ha b hbA
  rw [h0, h1] at this
  exact absurd this (by decide)

/--
**Empty index set.**
-/
theorem erdos_602.variants.empty_index {α : Type*} :
    ∀ (A : PEmpty → Set α),
      (∀ i, (A i).Infinite) →
      HasPropertyB PEmpty A := by
  intro A _hInfinite
  exact ⟨fun _ => 0, fun i => i.elim⟩

/--
**Unique index set.**
-/
theorem erdos_602.variants.unique_index {α : Type*} (I : Type*) [Unique I]
    (A : I → Set α) (hInfinite : ∀ i, (A i).Infinite) :
    HasPropertyB I A := by
  obtain ⟨f, hf⟩ := erdos_602.variants.single_set (A default) (hInfinite default)
  refine ⟨f, fun i => ?_⟩
  rw [Unique.eq_default i]
  exact hf

/--
**Two infinite sets with pairwise intersection of size ≠ 1.**
-/
theorem erdos_602.variants.two_sets :
    ∀ {α : Type*} (A : Fin 2 → Set α),
      (∀ i, (A i).Infinite) →
      (A 0 ∩ A 1).Finite →
      Set.ncard (A 0 ∩ A 1) ≠ 1 →
      HasPropertyB (Fin 2) A := by
  intro α A hInfinite hFin hNcard
  classical
  by_cases hEmpty : (A 0 ∩ A 1) = ∅
  · obtain ⟨a, ha0⟩ := (hInfinite 0).nonempty
    have hA0' : (A 0 \ {a}).Nonempty :=
      Set.Infinite.nonempty ((hInfinite 0).sdiff (Set.finite_singleton a))
    obtain ⟨b, hbA0, hba⟩ := hA0'
    simp only [Set.mem_singleton_iff] at hba
    obtain ⟨c, hc1⟩ := (hInfinite 1).nonempty
    have hA1' : (A 1 \ {c}).Nonempty :=
      Set.Infinite.nonempty ((hInfinite 1).sdiff (Set.finite_singleton c))
    obtain ⟨d, hd1, hdc⟩ := hA1'
    simp only [Set.mem_singleton_iff] at hdc
    have hDisj : ∀ x, x ∈ A 0 → x ∉ A 1 := by
      intro x hx0 hx1
      have hmem : x ∈ A 0 ∩ A 1 := ⟨hx0, hx1⟩
      rw [hEmpty] at hmem
      exact hmem
    have hb_ne_c : b ≠ c := fun h => hDisj b hbA0 (h ▸ hc1)
    have hb_ne_d : b ≠ d := fun h => hDisj b hbA0 (h ▸ hd1)
    have ha_ne_c : a ≠ c := fun h => hDisj a ha0 (h ▸ hc1)
    refine ⟨fun n => if n = b ∨ n = c then 1 else 0, fun i => ?_⟩
    fin_cases i
    · intro hMono
      have hfa : (fun n => if n = b ∨ n = c then (1 : Fin 2) else 0) a = 0 := by
        simp [show a ≠ b from fun h => hba h.symm, ha_ne_c]
      have hfb : (fun n => if n = b ∨ n = c then (1 : Fin 2) else 0) b = 1 := by simp
      have := hMono a ha0 b hbA0
      rw [hfa, hfb] at this; exact absurd this (by decide)
    · intro hMono
      have hfc : (fun n => if n = b ∨ n = c then (1 : Fin 2) else 0) c = 1 := by simp
      have hfd : (fun n => if n = b ∨ n = c then (1 : Fin 2) else 0) d = 0 := by
        simp [hb_ne_d.symm, hdc]
      have := hMono c hc1 d hd1
      rw [hfc, hfd] at this; exact absurd this (by decide)
  · have hge2 : 1 < Set.ncard (A 0 ∩ A 1) := by
      have hpos : 0 < Set.ncard (A 0 ∩ A 1) := by
        rw [Set.ncard_pos hFin]
        exact Set.nonempty_iff_ne_empty.mpr hEmpty
      omega
    obtain ⟨x, hxI, y, hyI, hxy⟩ := (Set.one_lt_ncard hFin).mp hge2
    refine ⟨fun n => if n = y then 1 else 0, fun i => ?_⟩
    fin_cases i
    · intro hMono
      have hfx : (fun n => if n = y then (1 : Fin 2) else 0) x = 0 := by
        simp [show x ≠ y from hxy]
      have hfy : (fun n => if n = y then (1 : Fin 2) else 0) y = 1 := by simp
      have := hMono x hxI.1 y hyI.1
      rw [hfx, hfy] at this; exact absurd this (by decide)
    · intro hMono
      have hfx : (fun n => if n = y then (1 : Fin 2) else 0) x = 0 := by
        simp [show x ≠ y from hxy]
      have hfy : (fun n => if n = y then (1 : Fin 2) else 0) y = 1 := by simp
      have := hMono x hxI.2 y hyI.2
      rw [hfx, hfy] at this; exact absurd this (by decide)

/-- A natural but FALSE relaxation of `erdos_602.variants.disjoint`: drop the
hypothesis that each `A i` is infinite. -/
def disjoint_without_infinite_claim : Prop :=
  ∀ {α : Type} {I : Type} (A : I → Set α),
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
    HasPropertyB I A

/-- Formal disproof of `disjoint_without_infinite_claim`. -/
theorem disjoint_without_infinite_claim.disproof :
    ¬ disjoint_without_infinite_claim := by
  intro h
  have hApp : HasPropertyB (Fin 2) (fun k : Fin 2 => if k = 0 then ({0} : Set ℕ) else {1}) :=
    h (fun k : Fin 2 => if k = 0 then ({0} : Set ℕ) else {1}) (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
  obtain ⟨f, hf⟩ := hApp
  apply hf 0
  simp only [Fin.isValue, ↓reduceIte]
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  rw [hx, hy]

/-! ### New scope certificates and sufficient conditions

These results do not settle `originalProblem`. In particular, finite pairwise
intersections do not supply the finite deletions in the sufficient condition.
-/

/-- A colouring of an infinite disjoint refinement also splits the original family. -/
theorem propertyB_of_disjoint_refinement {α I : Type*} (A B : I → Set α)
    (hSub : ∀ i, B i ⊆ A i) (hInf : ∀ i, (B i).Infinite)
    (hDisj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) : HasPropertyB I A := by
  obtain ⟨f, hf⟩ := erdos_602.variants.disjoint B hInf hDisj
  exact ⟨f, fun i hMono => hf i (fun x hx y hy => hMono x (hSub i hx) y (hSub i hy))⟩

/-- Essential disjointness is sufficient. The deletions must be proved to exist,
    and are not consequences asserted here of the original hypotheses. -/
theorem propertyB_of_finite_deletions {α I : Type*} (A D : I → Set α)
    (hInf : ∀ i, (A i).Infinite) (hFin : ∀ i, (D i).Finite)
    (hDisj : ∀ i j, i ≠ j → Disjoint (A i \ D i) (A j \ D j)) :
    HasPropertyB I A := by
  exact propertyB_of_disjoint_refinement A (fun i => A i \ D i)
    (fun _ => Set.sdiff_subset) (fun i => (hInf i).sdiff (hFin i)) hDisj

/-- A family of countably infinite, pairwise disjoint fibres whose union is
    uncountable. This disproves the union-countability inference, not Property B. -/
theorem countably_infinite_members_uncountable_union {β : Type*} [Uncountable β] :
    let A : β → Set (β × ℕ) := fun i => Set.range (fun n => (i, n))
    (∀ i, (A i).Countable ∧ (A i).Infinite) ∧
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
    ¬ (⋃ i, A i).Countable := by
  dsimp
  refine ⟨fun i => ⟨Set.countable_range _, Set.infinite_range_of_injective ?_⟩,
    ?_, ?_⟩
  · intro n m h
    exact congrArg Prod.snd h
  · intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ ⟨m, h⟩
    exact hij (congrArg Prod.fst h).symm
  · intro hc
    have hUnion : (⋃ i : β, Set.range (fun n : ℕ => (i, n))) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨x.1, x.2, Prod.eta x⟩
    rw [hUnion] at hc
    have hImage := hc.image Prod.fst
    rw [Set.image_univ_of_surjective (fun i : β => ⟨(i, 0), rfl⟩)] at hImage
    exact Set.not_countable_univ hImage

/-- The accurate renaming premise is countability of the whole union. -/
theorem countable_union_of_countable_index {α I : Type*} [Countable I]
    (A : I → Set α) (hc : ∀ i, (A i).Countable) : (⋃ i, A i).Countable :=
  Set.countable_iUnion hc

/-- A global colouring can be pulled back along one common relabelling.
    Separate bijections for each edge do not supply this common map. -/
theorem propertyB_of_image {α β I : Type*} (A : I → Set α) (e : α → β)
    (hB : HasPropertyB I (fun i => e '' A i)) :
    HasPropertyB I A := by
  obtain ⟨f, hf⟩ := hB
  refine ⟨f ∘ e, fun i hMono => hf i ?_⟩
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  exact hMono a ha b hb

/-- Core for the fresh-witness obstruction. -/
def pairedCore : Set (ℕ × ℕ × Fin 2) := {x | x.1 = 0}

/-- Satellite `i` shares precisely its two core points, and has an infinite private row. -/
def pairedSatellite (i : ℕ) : Set (ℕ × ℕ × Fin 2) :=
  {x | x.1 = i + 1 ∨ (x.1 = 0 ∧ x.2.1 = i)}

def pairedWitnesses (i : ℕ) : Set (ℕ × ℕ × Fin 2) := {(0, i, 0), (0, i, 1)}

def pairedFamily : Option ℕ → Set (ℕ × ℕ × Fin 2)
  | none => pairedCore
  | some i => pairedSatellite i

private theorem pairedCore_inter (i : ℕ) :
    pairedCore ∩ pairedSatellite i = pairedWitnesses i := by
  ext x
  rcases x with ⟨a, b, c⟩
  fin_cases c <;> simp [pairedCore, pairedSatellite, pairedWitnesses] <;> omega

private theorem pairedSatellite_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (pairedSatellite i) (pairedSatellite j) := by
  rw [Set.disjoint_left]
  rintro ⟨a, b, c⟩ hi hj
  simp only [pairedSatellite, Set.mem_ofPred_eq] at hi hj
  rcases hi with hi | ⟨hi, hbi⟩ <;> rcases hj with hj | ⟨hj, hbj⟩ <;> omega

/-- This example satisfies every original hypothesis; it is not a negative answer. -/
theorem paired_core_original_hypotheses :
    (∀ i, (pairedFamily i).Countable ∧ (pairedFamily i).Infinite) ∧
    (∀ i j, i ≠ j → (pairedFamily i ∩ pairedFamily j).Finite) ∧
    (∀ i j, i ≠ j → Set.ncard (pairedFamily i ∩ pairedFamily j) ≠ 1) := by
  have hPairFin : ∀ i, (pairedWitnesses i).Finite := fun i =>
    (Set.finite_singleton (0, i, (1 : Fin 2))).insert (0, i, (0 : Fin 2))
  have hPairCard : ∀ i, (pairedWitnesses i).ncard = 2 := by
    intro i
    exact Set.ncard_pair (by simp)
  have hInf : ∀ r : ℕ, Set.Infinite {x : ℕ × ℕ × Fin 2 | x.1 = r} := by
    intro r
    exact Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => (r, n, (0 : Fin 2)))
      (fun _ _ h => congrArg (fun x => x.2.1) h) (fun _ => rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨Set.to_countable _, ?_⟩
    cases i with
    | none => exact hInf 0
    | some i => exact (hInf (i + 1)).mono (fun _ hx => Or.inl hx)
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => simpa only [pairedFamily, pairedCore_inter] using hPairFin j
    | some i =>
      cases j with
      | none => simpa only [pairedFamily, Set.inter_comm, pairedCore_inter] using hPairFin i
      | some j =>
        have hd := pairedSatellite_disjoint (fun h => hij (congrArg some h))
        simpa only [pairedFamily, Set.disjoint_iff_inter_eq_empty.mp hd] using Set.finite_empty
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => simp only [pairedFamily, pairedCore_inter, hPairCard]; decide
    | some i =>
      cases j with
      | none => simp only [pairedFamily, Set.inter_comm, pairedCore_inter, hPairCard]; decide
      | some j =>
        have hd := pairedSatellite_disjoint (fun h => hij (congrArg some h))
        simp only [pairedFamily, Set.disjoint_iff_inter_eq_empty.mp hd, Set.ncard_empty]
        decide

/-- The last coordinate already splits all edges of the obstruction example. -/
theorem paired_core_hasPropertyB : HasPropertyB (Option ℕ) pairedFamily := by
  refine ⟨fun x => x.2.2, fun i hMono => ?_⟩
  cases i with
  | none =>
    have h := hMono (0, 0, 0) rfl (0, 0, 1) rfl
    exact (by decide : (0 : Fin 2) ≠ 1) h
  | some i =>
    have h := hMono (i + 1, 0, 0) (Or.inl rfl) (i + 1, 0, 1) (Or.inl rfl)
    exact (by decide : (0 : Fin 2) ≠ 1) h

/-- The satellites can use disjoint pairs of witnesses in the core. Their union
    exhausts the core, preventing a later fresh pair although Property B holds. -/
theorem paired_core_no_fresh_pair :
    (∀ i, pairedWitnesses i ⊆ pairedSatellite i) ∧
    (∀ i j, i ≠ j → Disjoint (pairedWitnesses i) (pairedWitnesses j)) ∧
    pairedCore \ (⋃ i, pairedWitnesses i) = ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i x hx
    rw [← pairedCore_inter] at hx
    exact hx.2
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    have hi' : x.2.1 = i := by
      rcases hi with rfl | hi
      · rfl
      · rw [Set.mem_singleton_iff] at hi
        rw [hi]
    have hj' : x.2.1 = j := by
      rcases hj with rfl | hj
      · rfl
      · rw [Set.mem_singleton_iff] at hj
        rw [hj]
    exact hij (hi'.symm.trans hj')
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨a, b, c⟩ ⟨ha, hn⟩
    change a = 0 at ha
    subst a
    apply hn
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_⟩
    fin_cases c <;> simp [pairedWitnesses]

/-- Split colourings converge pointwise to a monochromatic colouring even for one
    infinite edge. This certifies the missing closedness in naive compactness. -/
theorem splitting_condition_not_preserved_by_pointwise_limit :
    (∀ n : ℕ, ¬IsMonochromatic (fun x : ℕ => if x ≤ n then (0 : Fin 2) else 1) Set.univ) ∧
    (∀ x : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      (if x ≤ n then (0 : Fin 2) else 1) = 0) ∧
    IsMonochromatic (fun _ : ℕ => (0 : Fin 2)) Set.univ := by
  refine ⟨?_, ?_, fun _ _ _ _ => rfl⟩
  · intro n hMono
    have h := hMono 0 (Set.mem_univ _) (n + 1) (Set.mem_univ _)
    simp at h
  · intro x
    exact ⟨x, fun _ hn => if_pos hn⟩

/-- A chain of independent vertex sets can cease to be independent at its union,
    even in a family satisfying all original hypotheses. Zorn's lemma therefore
    cannot simply be applied to the inclusion order on independent sets. -/
theorem independent_chain_union_obstruction :
    let S : ℕ → Set (ℕ × ℕ × Fin 2) := fun n => {x | x.1 = 0 ∧ x.2.1 < n}
    Monotone S ∧ (∀ n i, ¬pairedFamily i ⊆ S n) ∧
      pairedFamily none ⊆ ⋃ n, S n := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro n m hnm x hx
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hnm⟩
  · intro n i hSub
    cases i with
    | none =>
      have h := hSub (show (0, n, (0 : Fin 2)) ∈ pairedFamily none from rfl)
      exact (Nat.lt_irrefl n) h.2
    | some i =>
      have h := hSub (show (i + 1, 0, (0 : Fin 2)) ∈ pairedFamily (some i) from Or.inl rfl)
      exact (Nat.succ_ne_zero i) h.1
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨x.2.1 + 1, hx, Nat.lt_succ_self _⟩

#print axioms independent_chain_union_obstruction

#print axioms paired_core_original_hypotheses
#print axioms paired_core_hasPropertyB
#print axioms paired_core_no_fresh_pair
#print axioms splitting_condition_not_preserved_by_pointwise_limit

#print axioms propertyB_of_disjoint_refinement
#print axioms propertyB_of_finite_deletions
#print axioms countably_infinite_members_uncountable_union
#print axioms countable_union_of_countable_index
#print axioms propertyB_of_image

#print axioms erdos_602.variants.disjoint
#print axioms erdos_602.variants.countable_index
#print axioms erdos_602.variants.single_set
#print axioms erdos_602.variants.empty_index
#print axioms erdos_602.variants.unique_index
#print axioms erdos_602.variants.two_sets
#print axioms disjoint_without_infinite_claim.disproof

end Erdos602
