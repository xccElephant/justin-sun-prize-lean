import Mathlib.NumberTheory.Pell
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Erdős Problem 686 (JSP-000558)

*References:*
- [erdosproblems.com/686](https://www.erdosproblems.com/686)
- [Er79d] Erdős, P., *Some unconventional problems in number theory*. Acta Math.
  Acad. Sci. Hungar. (1979), 71-80.

We prove the solved research questions in `FormalConjectures/ErdosProblems/686.lean`:
- `erdos_686.variants.four_two`: $4$ cannot be written as $(m+1)(m+2)/((n+1)(n+2))$ for $m \ge n + 2$,
- `erdos_686.variants.nine`: $9$ can be written as $\prod_{1 \le i \le k}(m+i)/\prod_{1 \le i \le k}(n+i)$ with $k \ge 2, m \ge n + k$,
- `erdos_686.variants.non_square`: every non-square integer $N \ge 2$ can be written in this form (with $k = 2$, via Pell's equation).
-/

namespace Erdos686

/--
The number $4$ cannot be written as
$$4=\frac{\prod_{1\leq i\leq 2}(m+i)}{\prod_{1\leq i\leq 2}(n+i)}$$
for $m\geq n+2$.
-/
theorem erdos_686.variants.four_two :
    ¬ ∃ᵉ (n : ℕ) (m ≥ n + 2),
      (4 : ℚ) = (∏ i ∈ Finset.Icc 1 2, (m + i)) / (∏ i ∈ Finset.Icc 1 2, (n + i)) := by
  simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self,
    Finset.prod_singleton]
  push Not
  intro n m hm
  rw [ne_eq, eq_div_iff (by positivity : (↑((n + 1) * (n + (1 + 1))) : ℚ) ≠ 0)]
  push_cast
  intro h
  have h' : 4 * ((n + 1) * (n + 2)) = (m + 1) * (m + 2) := by exact_mod_cast h
  by_cases hc : m < 2 * (n + 1) <;> nlinarith

/--
Can $9$ be written as
$$9=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\le k}(n+i)}$$
for some $k\geq 2$ and $m\geq n+k$?
Yes: witness $k = 3, n = 11, m = 25$, since $(26\cdot 27\cdot 28)/(12\cdot 13\cdot 14) = 19656/2184 = 9$.
-/
theorem erdos_686.variants.nine :
    ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (9 : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  refine ⟨3, by norm_num, 11, 25, by norm_num, ?_⟩
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/--
Every non-square $N\geq 2$ can be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k\geq 2$ and $m\geq n+k$ (in fact with $k = 2$).
-/
theorem erdos_686.variants.non_square :
    ∀ N ≥ (2 : ℕ), (¬ IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  intro N hN_ge_2 hN_not_square
  have hd : ¬ IsSquare (4 * N : ℤ) := by
    rintro ⟨s, hs⟩
    have h_even : Even s := by
      have : Even (s * s) := ⟨2 * N, by linarith⟩
      exact Int.even_mul.mp this |>.elim id id
    obtain ⟨t, rfl⟩ := h_even
    have ht : (N : ℤ) = t * t := by linarith
    have ht_nat : N = t.natAbs * t.natAbs := by
      have : (N : ℤ) = (t.natAbs : ℤ) ^ 2 := by
        rw [Int.natAbs_sq, sq, ht]
      have : N = t.natAbs ^ 2 := by exact_mod_cast this
      rwa [sq] at this
    exact hN_not_square ⟨t.natAbs, ht_nat⟩
  obtain ⟨x, y, hxy, hy_ne⟩ := Pell.exists_of_not_isSquare (by omega : 0 < (4 * N : ℤ)) hd
  set X : ℕ := x.natAbs
  set Y : ℕ := y.natAbs
  have hY_pos : 0 < Y := Int.natAbs_pos.mpr hy_ne
  have hXY_int : (X : ℤ) ^ 2 = 4 * (N : ℤ) * (Y : ℤ) ^ 2 + 1 := by
    have hx2 : (X : ℤ) ^ 2 = x ^ 2 := Int.natAbs_sq x
    have hy2 : (Y : ℤ) ^ 2 = y ^ 2 := Int.natAbs_sq y
    rw [hx2, hy2]
    linarith
  have hXY : X ^ 2 = 4 * N * Y ^ 2 + 1 := by exact_mod_cast hXY_int
  have hX_pos : 1 ≤ X := by nlinarith
  set S' : ℕ := 4 * N * Y ^ 2
  set Y' : ℕ := 2 * X * Y
  have hY'_ge_2 : 2 ≤ Y' := by
    have hXY_pos : 1 ≤ X * Y := Nat.mul_pos hX_pos hY_pos
    calc 2 = 2 * 1 := by ring
      _ ≤ 2 * (X * Y) := Nat.mul_le_mul_left 2 hXY_pos
      _ = Y' := by dsimp [Y']; ring
  have hS'_pos : 0 < S' := by positivity
  have hS'_ident : S' * (S' + 1) = N * Y' ^ 2 := by
    dsimp [S', Y']
    calc 4 * N * Y ^ 2 * (4 * N * Y ^ 2 + 1)
        = 4 * N * Y ^ 2 * X ^ 2 := by rw [← hXY]
      _ = N * (2 * X * Y) ^ 2 := by ring
  set n := Y' + S' - 1
  set m := N * Y' + S' - 1
  refine ⟨2, by norm_num, n, m, ?_, ?_⟩
  · have : 2 * Y' ≤ N * Y' := Nat.mul_le_mul_right Y' hN_ge_2
    omega
  · simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self,
      Finset.prod_singleton]
    rw [eq_div_iff (by positivity : (↑((n + 1) * (n + (1 + 1))) : ℚ) ≠ 0)]
    have h_ident : N * ((n + 1) * (n + 2)) = (m + 1) * (m + 2) := by
      have hn1 : n + 1 = Y' + S' := by omega
      have hn2 : n + 2 = Y' + S' + 1 := by omega
      have hm1 : m + 1 = N * Y' + S' := by omega
      have hm2 : m + 2 = N * Y' + S' + 1 := by omega
      rw [hn1, hn2, hm1, hm2]
      calc N * ((Y' + S') * (Y' + S' + 1))
          = N * Y' ^ 2 + N * Y' * (2 * S' + 1) + N * (S' * (S' + 1)) := by ring
        _ = S' * (S' + 1) + N * Y' * (2 * S' + 1) + N * (N * Y' ^ 2) := by rw [hS'_ident]
        _ = (N * Y' + S') * (N * Y' + S' + 1) := by ring
    exact_mod_cast h_ident

#print axioms erdos_686.variants.four_two
#print axioms erdos_686.variants.nine
#print axioms erdos_686.variants.non_square

end Erdos686
