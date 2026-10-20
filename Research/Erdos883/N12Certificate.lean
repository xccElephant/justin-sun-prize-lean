import Research.Erdos883.CycleWitness
import Research.Erdos883.SequentialCounter
import Research.Erdos883.SatCertificate

/-!
# Graph-to-CNF bridge for Jentges's n12/b0/l2 certificate

This module uses the unmodified archived CNF/LRAT pair. Its graph theorem is
independent of `FiniteWitness.lean` and its exhaustive n12 witness table.
It is a finite feasibility result, not the complete Erdős 883 first question.
-/

namespace Erdos883Research.N12Certificate
open SequentialCounter

/-- The exact archived 321-clause formula, with Mathlib's zero-based indices. -/
def formula : Sat.Fmla := dimacs_formula
  (include_str "../../verification/2026-10-20-bounty-only/certificates/n12_b0_l2.cnf")

theorem refutation : formula.proof [] := lrat_refutation
  (include_str "../../verification/2026-10-20-bounty-only/certificates/n12_b0_l2.cnf")
  (include_str "../../verification/2026-10-20-bounty-only/certificates/n12_b0_l2.lrat")

/-- Membership followed by the size-at-most-nine and complement-at-most-three
sequential counters, exactly in the archive's allocation order. -/
def assignment (B : Finset ℕ) : Sat.Valuation := fun i =>
  if i < 12 then i + 1 ∈ B
  else if i < 120 then aux (fun k => k + 1 ∈ B) ((i - 12) / 9 + 1) ((i - 12) % 9)
  else if i < 156 then aux (fun k => k + 1 ∉ B) ((i - 120) / 3 + 1) ((i - 120) % 3)
  else False

lemma total_mem (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 12) :
    prefixTrueCount (fun k => k + 1 ∈ B) 12 = B.card := by
  have himage : ((Finset.range 12).filter (fun k => k + 1 ∈ B)).image
      (fun k => k + 1) = B := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨k, ⟨_, hk⟩, rfl⟩
      exact hk
    · intro hv
      have hb := Finset.mem_Icc.mp (hB hv)
      refine ⟨v - 1, ⟨by omega, ?_⟩, by omega⟩
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ v)] using hv
  have hc := Finset.card_image_of_injective
    ((Finset.range 12).filter (fun k => k + 1 ∈ B))
    (show Function.Injective (fun k : ℕ => k + 1) by intro a b h; exact Nat.add_right_cancel h)
  rw [himage] at hc
  exact hc.symm

lemma total_not_mem (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 12) (hcard : B.card = 9) :
    prefixTrueCount (fun k => k + 1 ∉ B) 12 = 3 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range 12) (fun k => k + 1 ∈ B)
  have hm := total_mem B hB
  simp only [Finset.card_range] at h
  change prefixTrueCount (fun k => k + 1 ∈ B) 12 +
    prefixTrueCount (fun k => k + 1 ∉ B) 12 = 12 at h
  omega

lemma all_evens (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 12)
    (heven : selectedCount (fun v => v % 2 = 0) B = 6) :
    ∀ v ∈ ({2, 4, 6, 8, 10, 12} : Finset ℕ), v ∈ B := by
  have hsub : B.filter (fun v => v % 2 = 0) ⊆ {2, 4, 6, 8, 10, 12} := by
    intro v hv
    obtain ⟨hv, he⟩ := Finset.mem_filter.mp hv
    have hb := Finset.mem_Icc.mp (hB hv)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    change ({2, 4, 6, 8, 10, 12} : Finset ℕ).card ≤ selectedCount (fun v => v % 2 = 0) B
    rw [heven]
    decide)
  intro v hv
  exact (Finset.mem_filter.mp (heq.symm ▸ hv)).1

end Erdos883Research.N12Certificate
#print axioms Erdos883Research.N12Certificate.refutation
