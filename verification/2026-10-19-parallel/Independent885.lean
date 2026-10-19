import JspBounties.Erdos885
set_option autoImplicit false
namespace Independent885
def rawD (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a * b ∧
    (d : ℤ) = |(a : ℤ) - b|}

lemma rawD_eq (n : ℕ) (hn : 0 < n) :
    rawD n = Erdos885.factorDifferenceSet n := by
  ext d
  constructor
  · rintro ⟨a, b, _, _, hab, hd⟩
    exact ⟨a, b, hab, hd⟩
  · rintro ⟨a, b, hab, hd⟩
    have ha : 0 < a := by
      by_contra h
      have hz : a = 0 := by omega
      simp [hz] at hab
      omega
    have hb : 0 < b := by
      by_contra h
      have hz : b = 0 := by omega
      simp [hz] at hab
      omega
    exact ⟨a, b, ha, hb, hab, hd⟩

-- Independent bridge: unpack original definition into strictly positive factor pairs.
example (k : ℕ) :
    ∃ (N M : ℕ) (D : Finset ℕ), 0 < N ∧ N < M ∧ D.card = k ∧
      ∀ d ∈ D, 0 < d ∧
        (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a*b ∧
          (d : ℤ) = |(a : ℤ)-b|) ∧
        (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ M = a*b ∧
          (d : ℤ) = |(a : ℤ)-b|) := by
  obtain ⟨N, M, D, hN, hNM, hcard, hD⟩ :=
    Erdos885.TwoNumbers.literal_two_number_witnesses k
  refine ⟨N, M, D, hN, hNM, hcard, ?_⟩
  intro d hd
  obtain ⟨hpos, hleft, hright⟩ := hD d hd
  have hM : 0 < M := lt_trans hN hNM
  have hleft' : d ∈ rawD N := by rw [rawD_eq N hN]; exact hleft
  have hright' : d ∈ rawD M := by rw [rawD_eq M hM]; exact hright
  exact ⟨hpos, hleft', hright'⟩

-- Independently assemble the cardinality bound from witnesses and finiteness.
example (k : ℕ) :
    ∃ N M : ℕ, 0 < N ∧ N < M ∧ k ≤ (rawD N ∩ rawD M).ncard := by
  obtain ⟨N, M, D, hN, hNM, hcard, hD⟩ :=
    Erdos885.TwoNumbers.literal_two_number_witnesses k
  refine ⟨N, M, hN, hNM, ?_⟩
  rw [rawD_eq N hN, rawD_eq M (lt_trans hN hNM), ← hcard,
    ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun d hd => (hD d hd).2)
    ((Erdos885.factorDifferenceSet_finite hN).subset Set.inter_subset_left)

-- Confirm both exact public signatures.
example (k : ℕ) : ∃ N M : ℕ, 0 < N ∧ N < M ∧
    k ≤ (Erdos885.factorDifferenceSet N ∩ Erdos885.factorDifferenceSet M).ncard :=
  Erdos885.TwoNumbers.literal_two_numbers k
example (k : ℕ) : ∃ (N M : ℕ) (D : Finset ℕ), 0 < N ∧ N < M ∧ D.card = k ∧
    ∀ d ∈ D, 0 < d ∧ d ∈ Erdos885.factorDifferenceSet N ∩
      Erdos885.factorDifferenceSet M :=
  Erdos885.TwoNumbers.literal_two_number_witnesses k

-- No Point-existence assumption; seed and the total sequence are terms.
example : Nonempty Erdos885.TwoNumbers.Point := ⟨Erdos885.TwoNumbers.seed⟩
example (n : ℕ) : padicValRat 2 (Erdos885.TwoNumbers.points n).x =
    -2*((n : ℤ)+1) := Erdos885.TwoNumbers.points_valuation n
example (n : ℕ) : 2*padicValRat 2
    (Erdos885.TwoNumbers.u (Erdos885.TwoNumbers.points n)) = -2*((n : ℤ)+2) := by
  rw [Erdos885.TwoNumbers.u_val_relation, Erdos885.TwoNumbers.points_valuation]
  ring
example : Function.Injective
    (fun n => |Erdos885.TwoNumbers.u (Erdos885.TwoNumbers.points n)|) :=
  Erdos885.TwoNumbers.u_points_injective

-- Empty-index boundary: the common denominator product is 1 and D is empty.
example : (∏ ij : Fin 0 × Fin 3,
    (Erdos885.TwoNumbers.u (Erdos885.TwoNumbers.points ij.1)).den) = 1 := by simp
example : ∃ (N M : ℕ) (D : Finset ℕ), 0 < N ∧ N < M ∧ D.card = 0 ∧
    ∀ d ∈ D, 0 < d ∧ d ∈ rawD N ∩ rawD M := by
  exact ⟨6, 12, ∅, by norm_num, by norm_num, by simp, by simp⟩

#print axioms rawD_eq
#print axioms Erdos885.TwoNumbers.seed
#print axioms Erdos885.TwoNumbers.double
#print axioms Erdos885.TwoNumbers.points_valuation
#print axioms Erdos885.TwoNumbers.u_points_injective
#print axioms Erdos885.TwoNumbers.literal_two_number_witnesses
#print axioms Erdos885.TwoNumbers.literal_two_numbers
end Independent885
