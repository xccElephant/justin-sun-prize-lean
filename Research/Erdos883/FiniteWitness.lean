import Research.Erdos883.CycleWitness

/-!
# A direct, checked finite witness interface for Erdős 883

This module connects a finite cycle table to actual graph containment. The
first instance is n=12, all six evens selected, and a five-cycle. It is a
bounded integration test, not the all-n theorem or a prize submission.
-/

namespace Erdos883Research

/-- Every nine-element subset of [1,12] containing all six even integers. -/
def n12WitnessTable : List (Finset ℕ × (Fin 5 → ℕ)) := [
  ({1, 2, 3, 4, 5, 6, 8, 10, 12}, ![1, 2, 3, 4, 5]),
  ({1, 2, 3, 4, 6, 7, 8, 10, 12}, ![1, 2, 3, 4, 7]),
  ({1, 2, 3, 4, 6, 8, 9, 10, 12}, ![1, 2, 3, 4, 9]),
  ({1, 2, 3, 4, 6, 8, 10, 11, 12}, ![1, 2, 3, 4, 11]),
  ({1, 2, 4, 5, 6, 7, 8, 10, 12}, ![1, 2, 5, 4, 7]),
  ({1, 2, 4, 5, 6, 8, 9, 10, 12}, ![1, 2, 5, 4, 9]),
  ({1, 2, 4, 5, 6, 8, 10, 11, 12}, ![1, 2, 5, 4, 11]),
  ({1, 2, 4, 6, 7, 8, 9, 10, 12}, ![1, 2, 7, 4, 9]),
  ({1, 2, 4, 6, 7, 8, 10, 11, 12}, ![1, 2, 7, 4, 11]),
  ({1, 2, 4, 6, 8, 9, 10, 11, 12}, ![1, 2, 9, 4, 11]),
  ({2, 3, 4, 5, 6, 7, 8, 10, 12}, ![2, 3, 4, 5, 7]),
  ({2, 3, 4, 5, 6, 8, 9, 10, 12}, ![2, 3, 4, 5, 9]),
  ({2, 3, 4, 5, 6, 8, 10, 11, 12}, ![2, 3, 4, 5, 11]),
  ({2, 3, 4, 6, 7, 8, 9, 10, 12}, ![2, 3, 4, 7, 9]),
  ({2, 3, 4, 6, 7, 8, 10, 11, 12}, ![2, 3, 4, 7, 11]),
  ({2, 3, 4, 6, 8, 9, 10, 11, 12}, ![2, 3, 4, 9, 11]),
  ({2, 4, 5, 6, 7, 8, 9, 10, 12}, ![2, 5, 4, 7, 9]),
  ({2, 4, 5, 6, 7, 8, 10, 11, 12}, ![2, 5, 4, 7, 11]),
  ({2, 4, 5, 6, 8, 9, 10, 11, 12}, ![2, 5, 4, 9, 11]),
  ({2, 4, 6, 7, 8, 9, 10, 11, 12}, ![2, 7, 4, 9, 11])
]

theorem n12_table_valid :
    ∀ row ∈ n12WitnessTable, IsCycleWitness row.1 row.2 := by decide

set_option maxRecDepth 10000 in
theorem n12_table_covers :
    ∀ A ∈ (Finset.Icc 1 12).powersetCard 9,
      selectedCount (fun v => v % 2 = 0) A = 6 →
      ∃ row ∈ n12WitnessTable, row.1 = A := by decide

/-- End-to-end graph statement for one small residual parameter, independent
of SAT compression. This is not the full Erdős883 theorem. -/
theorem n12_b0_has_five_cycle (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 12) (hcard : A.card = 9)
    (heven : selectedCount (fun v => v % 2 = 0) A = 6) :
    (SimpleGraph.cycleGraph 5).IsContained (coprimeGraph.induce (A : Set ℕ)) := by
  obtain ⟨row, hrow, hsame⟩ := n12_table_covers A (Finset.mem_powersetCard.mpr ⟨hA,hcard⟩) heven
  rw [← hsame]
  exact cycleWitness_isContained (n12_table_valid row hrow)

end Erdos883Research

#print axioms Erdos883Research.n12_b0_has_five_cycle
