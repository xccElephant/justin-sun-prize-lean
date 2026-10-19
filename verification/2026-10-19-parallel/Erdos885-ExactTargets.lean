import JspBounties.Erdos885
example (k : ℕ) : ∃ N M : ℕ, 0 < N ∧ N < M ∧
    k ≤ (Erdos885.factorDifferenceSet N ∩ Erdos885.factorDifferenceSet M).ncard :=
  Erdos885.TwoNumbers.literal_two_numbers k
example (k : ℕ) : ∃ (N M : ℕ) (D : Finset ℕ), 0 < N ∧ N < M ∧ D.card = k ∧
    ∀ d ∈ D, 0 < d ∧ d ∈ Erdos885.factorDifferenceSet N ∩
      Erdos885.factorDifferenceSet M :=
  Erdos885.TwoNumbers.literal_two_number_witnesses k
#check Erdos885.erdos_885.variants.k_eq_2
#check Erdos885.erdos_885.variants.k_eq_3
#check Erdos885.erdos_885.variants.k_eq_4
#check Erdos885.TwoNumbers.literal_two_numbers
#check Erdos885.TwoNumbers.literal_two_number_witnesses
#print axioms Erdos885.TwoNumbers.literal_two_numbers
#print axioms Erdos885.TwoNumbers.literal_two_number_witnesses
