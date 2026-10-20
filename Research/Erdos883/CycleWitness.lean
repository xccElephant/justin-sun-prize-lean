import Research.Erdos883.Compression
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Generic cycle witnesses, independent of any finite coverage theorem. -/

namespace Erdos883Research

def IsCycleWitness {k : ℕ} (A : Finset ℕ) (c : Fin k → ℕ) : Prop :=
  Function.Injective c ∧ (∀ i, c i ∈ A) ∧
    ∀ i j, (SimpleGraph.cycleGraph k).Adj i j → (c i).Coprime (c j)

instance {k : ℕ} (A : Finset ℕ) (c : Fin k → ℕ) : Decidable (IsCycleWitness A c) := by
  unfold IsCycleWitness Function.Injective
  infer_instance

theorem cycleWitness_isContained {k : ℕ} {A : Finset ℕ} {c : Fin k → ℕ}
    (hc : IsCycleWitness A c) :
    (SimpleGraph.cycleGraph k).IsContained (coprimeGraph.induce (A : Set ℕ)) := by
  let f : Fin k → {z // z ∈ A} := fun i => ⟨c i, hc.2.1 i⟩
  refine ⟨⟨{ toFun := f, map_rel' := ?_ }, ?_⟩⟩
  · intro i j hij
    apply coprimeGraph_adj.mpr
    exact ⟨fun h => hij.ne (hc.1 h), hc.2.2 i j hij⟩
  · intro i j hij
    exact hc.1 (congrArg Subtype.val hij)

theorem cycleWitness_isContained_of_subset {k : ℕ} {A B : Finset ℕ} {c : Fin k → ℕ}
    (hc : IsCycleWitness A c) (hAB : A ⊆ B) :
    (SimpleGraph.cycleGraph k).IsContained (coprimeGraph.induce (B : Set ℕ)) :=
  cycleWitness_isContained ⟨hc.1, fun i => hAB (hc.2.1 i), hc.2.2⟩

end Erdos883Research

#print axioms Erdos883Research.cycleWitness_isContained
