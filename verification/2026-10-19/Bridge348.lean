import JspBounties.Erdos348

open scoped BigOperators
namespace Independent348

def CompleteAfterDeleting (a : ℕ → ℕ) (s : Finset ℕ) : Prop :=
  ∀ᶠ k in Filter.atTop, ∃ B : Finset ℕ, k = ∑ i ∈ B, (if i ∈ s then 0 else a i)

lemma agrees (a : ℕ → ℕ) (s : Finset ℕ) :
    CompleteAfterDeleting a s ↔ IsAddCompleteNatSeq' (Function.updateFinset a s 0) := by
  simp only [CompleteAfterDeleting, IsAddCompleteNatSeq', subseqSums', Set.mem_ofPred_eq,
    Erdos348.updateFinset_zero_apply]

theorem complete_original_sequence_question (m n : ℕ) (hmn : m < n) :
    (∃ a : ℕ → ℕ, Monotone a ∧
      (∀ s : Finset ℕ, s.card = m → CompleteAfterDeleting a s) ∧
      (∀ s : Finset ℕ, s.card = n → ¬ CompleteAfterDeleting a s)) ↔ m ≤ 1 := by
  simp only [agrees]
  have h := congrArg (fun S : Set (ℕ × ℕ) => (m, n) ∈ S) Erdos348.erdos_348
  simpa [Erdos348.erdos_348.answer, hmn, and_comm, and_left_comm, and_assoc] using h

#print axioms complete_original_sequence_question
end Independent348
