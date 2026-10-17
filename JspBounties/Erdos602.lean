import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 602 (JSP-000489)

*Reference:* [erdosproblems.com/602](https://www.erdosproblems.com/602)

We formalize the solved variants and disproofs in `FormalConjectures/ErdosProblems/602.lean`:
- `erdos_602.variants.disjoint`: Every pairwise-disjoint family of infinite sets has Property B.
- `erdos_602.variants.two_sets`: Every pair of infinite sets whose intersection is finite and of size $\neq 1$ has Property B.
- `disjoint_without_infinite_claim.disproof`: Dropping the infinite-set hypothesis refutes the disjoint Property B claim.
-/

open Set

namespace Erdos602

/-- A set `A ⊆ α` is **monochromatic** under a 2-colouring `f : α → Fin 2`
if all elements of `A` receive the same colour. -/
def IsMonochromatic {α : Type*} (f : α → Fin 2) (A : Set α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, f x = f y

/-- A family `(A_i)_{i ∈ I}` of subsets of `α` has **Property B** if there exists
a 2-colouring `f : α → Fin 2` such that no `A_i` is monochromatic. -/
def HasPropertyB {α : Type*} (I : Type*) (A : I → Set α) : Prop :=
  ∃ f : α → Fin 2, ∀ i, ¬IsMonochromatic f (A i)

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

#print axioms erdos_602.variants.disjoint
#print axioms erdos_602.variants.two_sets
#print axioms disjoint_without_infinite_claim.disproof

end Erdos602
