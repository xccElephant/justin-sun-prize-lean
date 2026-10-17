import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem 1063 (JSP-000881)

*References:*
- [erdosproblems.com/1063](https://www.erdosproblems.com/1063)
- [ErSe83] Erdős, P. and Selfridge, J. L., *Problem 6447*. Amer. Math. Monthly (1983), 710.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory* (2004), Problem B31.
- [Mo85] Monier, Jean-Marie, *Problems and Solutions: Solutions of Advanced Problems: 6447*.
  Amer. Math. Monthly **92** (1985), 435-436.

We formalize `erdos_1063.variants.small_values` ($n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12$) from
`FormalConjectures/ErdosProblems/1063.lean`.
-/

namespace Erdos1063

/--
Let $n_k$ be the least $n \ge 2k$ such that all but one of the integers $n - i$ with
$0 \le i < k$ divide $\binom{n}{k}$.
-/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/-- The initial values satisfy $n_2 = 4$, $n_3 = 6$, $n_4 = 9$, and $n_5 = 12$ ([Gu04], Problem B31). -/
theorem erdos_1063.variants.small_values :
    n 2 = 4 ∧ n 3 = 6 ∧ n 4 = 9 ∧ n 5 = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨4, by decide⟩
      rintro b hb
      have : 2 * 2 ≤ b := hb.1
      omega
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨6, by decide⟩
      rintro b hb
      have : 2 * 3 ≤ b := hb.1
      omega
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨9, by decide⟩
      rintro b hb
      have hb8 : 8 ≤ b := by have := hb.1; omega
      by_contra! h
      interval_cases b
      · exact absurd hb (by decide)
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨12, by decide⟩
      rintro b hb
      have hb10 : 10 ≤ b := by have := hb.1; omega
      by_contra! h
      interval_cases b
      · exact absurd hb (by decide)
      · exact absurd hb (by decide)

#print axioms erdos_1063.variants.small_values

end Erdos1063
