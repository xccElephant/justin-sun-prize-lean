import JspBounties.Erdos365
namespace Independent365

def PowerfulPositive (n : ℕ) : Prop := 0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

theorem complete_original_question :
    ¬ ∀ n : ℕ, PowerfulPositive n → PowerfulPositive (n + 1) →
      IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  obtain ⟨ha, hb, hna, hnb⟩ := Erdos365.golomb_pair
  have a : PowerfulPositive 12167 := by
    refine ⟨by decide, ?_⟩
    intro p hp hd
    exact ha p (Nat.mem_primeFactors.mpr ⟨hp, hd, by decide⟩)
  have b : PowerfulPositive 12168 := by
    refine ⟨by decide, ?_⟩
    intro p hp hd
    exact hb p (Nat.mem_primeFactors.mpr ⟨hp, hd, by decide⟩)
  rcases h 12167 a b with hs | hs
  · exact hna hs
  · exact hnb hs

#print axioms complete_original_question
end Independent365
