import Research.Erdos883.FiniteWitness
import Research.Erdos883.CompressionCounts
import Research.Erdos883.N12Clauses
import Research.Erdos883.ThirdParty.PartII

/-!
# Integration checks for the explicitly partial Erdős 883 development

No theorem in this file asserts the complete first question. The general
second-question proof is attributed third-party work.
-/

example : Erdos883Research.coprimeGraph = Erdos883.coprimeGraph := rfl

example {V : Type*} (H : SimpleGraph V) (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n)
    (hfree : ¬ H.IsContained (Erdos883.coprimeGraph.induce (A : Set ℕ))) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 n ∧ B.card = A.card ∧
      (B.filter (fun v => v % 2 = 0)).card = (A.filter (fun v => v % 2 = 0)).card ∧
      (¬ H.IsContained (Erdos883.coprimeGraph.induce (B : Set ℕ))) ∧
      (∀ x ∈ B, ∀ y ∈ Finset.Icc 1 n,
        x % 2 = y % 2 → x.primeFactors ⊂ y.primeFactors → y ∈ B) ∧
      (∀ x ∈ B, ∀ y ∈ Finset.Icc 1 n,
        y < x → y.primeFactors = x.primeFactors → y ∈ B) :=
  Erdos883Research.exists_compressed_prefix_counterexample H n A hA hfree

example (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 12) (hcard : A.card = 9)
    (heven : (A.filter (fun v => v % 2 = 0)).card = 6) :
    ∃ v, ∃ p : (Erdos883.coprimeGraph.induce (A : Set ℕ)).Walk v v,
      p.IsCycle ∧ p.length = 5 :=
  (SimpleGraph.cycleGraph_isContained_iff (by decide)).mp
    (Erdos883Research.n12_b0_has_five_cycle A hA hcard heven)

#print axioms Erdos883Research.no_copy_after_replacement
#print axioms Erdos883Research.exists_support_compressed_counterexample
#print axioms Erdos883Research.exists_compressed_prefix_counterexample
#print axioms Erdos883Research.cycleWitness_isContained
#print axioms Erdos883Research.n12_b0_has_five_cycle
#print axioms Erdos883.erdos_883_parts_ii_direct

example (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 12) (hcard : A.card = 9)
    (heven : (A.filter (fun v => v % 2 = 0)).card = 6) :
    ∃ v, ∃ p : (Erdos883.coprimeGraph.induce (A : Set ℕ)).Walk v v,
      p.IsCycle ∧ p.length = 5 :=
  (SimpleGraph.cycleGraph_isContained_iff (by decide)).mp
    (Erdos883Research.N12Certificate.n12_b0_has_five_cycle_via_lrat A hA hcard heven)

#print axioms Erdos883Research.exists_compressed_prefix_counterexample_counts
#print axioms Erdos883Research.N12Certificate.refutation
#print axioms Erdos883Research.N12Certificate.satisfies_formula
#print axioms Erdos883Research.N12Certificate.n12_b0_has_five_cycle_via_lrat
