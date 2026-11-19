/-
Copyright 2026 Chucheng Xiang (@xccElephant).
SPDX-License-Identifier: Apache-2.0

Independent first-principles statement audit and axiom verification for `Erdos701` (`JSP-000571`).
Reconstructs hereditary set families (downsets), pairwise-intersecting subfamilies, and element
stars directly from elementary set/finset membership without referencing `IsLowerSet`,
`Set.Intersecting`, or any helper definitions from `Erdos701`, proves bidirectional semantic
equivalence bridges and standalone full-scope audit theorems across `Cardinal`, `Set.ncard`,
`Finset`, and Chvátal's `[Ch74]` vertex-in-edge hypergraph formulation, and audits transitive
axioms via `#print axioms`.
-/
import Erdos701

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace StatementAudit

open Cardinal

/-! ### 1. Independent First-Principles Definitions (Zero `IsLowerSet` or `Set.Intersecting`) -/

/-- Raw first-principles hereditary property (downward subset closure) on `Set (Set X)`:
whenever `A ∈ F` and every element of `B` belongs to `A`, we have `B ∈ F`. -/
def RawHereditarySet {X : Type*} (F : Set (Set X)) : Prop :=
  ∀ A : Set X, A ∈ F → ∀ B : Set X, (∀ z : X, z ∈ B → z ∈ A) → B ∈ F

/-- Raw first-principles pairwise-intersecting property on `Set (Set X)`:
every two members `A, B ∈ F'` share at least one common element `z : X`. -/
def RawIntersectingSet {X : Type*} (F' : Set (Set X)) : Prop :=
  ∀ A : Set X, A ∈ F' → ∀ B : Set X, B ∈ F' → ∃ z : X, z ∈ A ∧ z ∈ B

/-- Raw first-principles star of an element `x : X` inside `F : Set (Set X)`. -/
def rawStarSet {X : Type*} (F : Set (Set X)) (x : X) : Set (Set X) :=
  {A : Set X | A ∈ F ∧ x ∈ A}

/-- Raw first-principles hereditary property on `Finset (Finset X)`. -/
def RawHereditaryFinset {X : Type*} (D : Finset (Finset X)) : Prop :=
  ∀ A : Finset X, A ∈ D → ∀ B : Finset X, (∀ z : X, z ∈ B → z ∈ A) → B ∈ D

/-- Raw first-principles pairwise-intersecting property on `Finset (Finset X)`. -/
def RawIntersectingFinset {X : Type*} (I : Finset (Finset X)) : Prop :=
  ∀ A : Finset X, A ∈ I → ∀ B : Finset X, B ∈ I → ∃ z : X, z ∈ A ∧ z ∈ B

/-- Raw first-principles star of an element `x : X` inside `D : Finset (Finset X)`. -/
def rawStarFinset {X : Type*} [DecidableEq X] (D : Finset (Finset X)) (x : X) : Finset (Finset X) :=
  D.filter (fun A => x ∈ A)

/-! ### 2. Bidirectional Semantic Equivalence Bridges -/

theorem rawHereditarySet_iff_isLowerSet {X : Type*} (F : Set (Set X)) :
    RawHereditarySet F ↔ IsLowerSet F :=
  ⟨fun h A B hBA hAF => h A hAF B hBA, fun h _ hAF _ hBA => h hBA hAF⟩

theorem rawIntersectingSet_iff_intersecting {X : Type*} (F' : Set (Set X)) :
    RawIntersectingSet F' ↔ F'.Intersecting := by
  constructor
  · intro h A hA B hB
    rw [Set.not_disjoint_iff]
    exact h A hA B hB
  · intro h _ hA _ hB
    exact Set.not_disjoint_iff.mp (h hA hB)

theorem rawHereditaryFinset_iff_subset {X : Type*} (D : Finset (Finset X)) :
    RawHereditaryFinset D ↔ (∀ A ∈ D, ∀ B ⊆ A, B ∈ D) :=
  ⟨fun h A hA B hBA => h A hA B (fun _ hz => hBA hz),
   fun h A hA B hBA => h A hA B (fun z hz => hBA z hz)⟩

theorem rawIntersectingFinset_iff_nonempty {X : Type*} [DecidableEq X] (I : Finset (Finset X)) :
    RawIntersectingFinset I ↔ (∀ A ∈ I, ∀ B ∈ I, (A ∩ B).Nonempty) := by
  constructor
  · intro h A hA B hB
    rcases h A hA B hB with ⟨z, hzA, hzB⟩
    exact ⟨z, Finset.mem_inter.mpr ⟨hzA, hzB⟩⟩
  · intro h A hA B hB
    rcases h A hA B hB with ⟨z, hz⟩
    exact ⟨z, (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩

/-! ### 3. Independent First-Principles Full-Scope Audit Theorems -/

/-- First-principles `Cardinal` audit theorem for Chvátal's Conjecture (`Erdős #701` / `JSP-000571`). -/
theorem audit_erdos_701_cardinal {X : Type} [Nonempty X] [Fintype X]
    (F : Set (Set X)) (hF : RawHereditarySet F) :
    ∃ x : X, ∀ F' : Set (Set X), (∀ A, A ∈ F' → A ∈ F) →
      RawIntersectingSet F' → #F' ≤ #(rawStarSet F x) := by
  rcases Erdos701.erdos_701 F ((rawHereditarySet_iff_isLowerSet F).mp hF) with ⟨x, hx⟩
  exact ⟨x, fun F' hsub hinter =>
    hx F' hsub ((rawIntersectingSet_iff_intersecting F').mp hinter)⟩

/-- First-principles universe-polymorphic `Set.ncard` audit theorem for Chvátal's Conjecture. -/
theorem audit_erdos_701_ncard {X : Type*} [Nonempty X] [Fintype X]
    (F : Set (Set X)) (hF : RawHereditarySet F) :
    ∃ x : X, ∀ F' : Set (Set X), (∀ A, A ∈ F' → A ∈ F) →
      RawIntersectingSet F' → F'.ncard ≤ (rawStarSet F x).ncard := by
  rcases Erdos701.erdos_701_ncard F ((rawHereditarySet_iff_isLowerSet F).mp hF) with ⟨x, hx⟩
  exact ⟨x, fun F' hsub hinter =>
    hx F' hsub ((rawIntersectingSet_iff_intersecting F').mp hinter)⟩

/-- First-principles `Finset` audit theorem for Chvátal's Conjecture (`[Ch74]`). -/
theorem audit_chvatal_finset {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (D : Finset (Finset X)) (hD : RawHereditaryFinset D) :
    ∃ x : X, ∀ I : Finset (Finset X), (∀ A, A ∈ I → A ∈ D) →
      RawIntersectingFinset I → I.card ≤ (rawStarFinset D x).card := by
  rcases Erdos701.chvatal_conjecture_finset D ((rawHereditaryFinset_iff_subset D).mp hD) with ⟨x, hx⟩
  exact ⟨x, fun I hsub hinter =>
    hx I (fun A hA => hsub A hA) ((rawIntersectingFinset_iff_nonempty I).mp hinter)⟩

/-- First-principles `[Ch74]` vertex-in-edge audit theorem (requiring no `[Nonempty X]` typeclass). -/
theorem audit_chvatal_hypergraph_vertex {X : Type*} [Fintype X] [DecidableEq X]
    (D : Finset (Finset X)) (hD : RawHereditaryFinset D)
    (hne : ∃ E ∈ D, ∃ y : X, y ∈ E) :
    ∃ x : X, ({x} : Finset X) ∈ D ∧
      ∀ I : Finset (Finset X), (∀ A, A ∈ I → A ∈ D) →
        RawIntersectingFinset I → I.card ≤ (rawStarFinset D x).card := by
  rcases hne with ⟨E, hED, y, hyE⟩
  rcases Erdos701.chvatal_conjecture_hypergraph_vertex D
    ((rawHereditaryFinset_iff_subset D).mp hD) ⟨E, hED, y, hyE⟩ with ⟨x, hxD, hx⟩
  exact ⟨x, hxD, fun I hsub hinter =>
    hx I (fun A hA => hsub A hA) ((rawIntersectingFinset_iff_nonempty I).mp hinter)⟩

/-! ### 4. Signature & Transitive Axiom Verification -/

#check @Erdos701.erdos_701
#check @Erdos701.erdos_701_ncard
#check @Erdos701.chvatal_conjecture_finset
#check @Erdos701.chvatal_conjecture_hypergraph_vertex
#check @Erdos701.principal_downset_sharpness
#check @StatementAudit.audit_erdos_701_cardinal
#check @StatementAudit.audit_erdos_701_ncard
#check @StatementAudit.audit_chvatal_finset
#check @StatementAudit.audit_chvatal_hypergraph_vertex

#print axioms Erdos701.erdos_701
#print axioms Erdos701.erdos_701_ncard
#print axioms Erdos701.chvatal_conjecture_finset
#print axioms Erdos701.chvatal_conjecture_hypergraph_vertex
#print axioms Erdos701.principal_downset_sharpness
#print axioms StatementAudit.audit_erdos_701_cardinal
#print axioms StatementAudit.audit_erdos_701_ncard
#print axioms StatementAudit.audit_chvatal_finset
#print axioms StatementAudit.audit_chvatal_hypergraph_vertex

end StatementAudit
