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

#print axioms erdos_602.variants.disjoint
#print axioms erdos_602.variants.countable_index
#print axioms erdos_602.variants.single_set
#print axioms erdos_602.variants.empty_index
#print axioms erdos_602.variants.unique_index
#print axioms erdos_602.variants.two_sets
#print axioms disjoint_without_infinite_claim.disproof

end Erdos602
