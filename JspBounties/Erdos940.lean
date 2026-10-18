/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 940 & 941 (`JSP-000782`): Powerful Numbers and Sums of Powerful Numbers

*References:*
- [erdosproblems.com/940](https://www.erdosproblems.com/940) (`FormalConjectures/ErdosProblems/940.lean`)
- [erdosproblems.com/941](https://www.erdosproblems.com/941) (`JSP-000782`)
- [BaBr94] Baker, R. C. and Brüdern, J., *On sums of two squarefull numbers*. Math. Proc.
  Cambridge Philos. Soc. 115 (1994), 1–5.
- [He88] Heath-Brown, D. R., *Ternary quadratic forms and sums of three square-full numbers*.
  Séminaire de Théorie des Nombres, Paris 1986–87 (1988), 137–163.

This file formalizes:
1. **Algebraic closure properties of $r$-powerful numbers (`Nat.Full r n`)**:
   Closure under multiplication (`Nat.Full.mul`), powers (`Nat.Full.pow_of_le`), and monotonicity in $r$.
2. **The Classical Structure Theorem for $2$-Powerful Numbers (`two_full_iff_exists_sq_mul_cube`)**:
   A natural number $n$ is $2$-powerful (`(2).Full n`) if and only if $n = a^2 b^3$ for some
   $a, b \in \mathbb{N}$ (the foundational parameterization behind Terence Tao's and
   Baker–Brüdern's density-zero argument for `erdos_940.variants.two` and Heath-Brown's ternary
   quadratic form reduction for `erdos_940.variants.three_powerful`).
3. **Sharpness of `∀ᶠ x in atTop` in `erdos_940.variants.three_powerful` (`seven_not_sum_three_powerful`)**:
   Proves that $7$ cannot be expressed as the sum of at most three $2$-powerful numbers, showing
   that the `atTop` filter in Heath-Brown's theorem (`JSP-000782`) is strictly necessary.
-/

namespace Nat

/-- A natural number `n` is `k`-full (or `k`-powerful) if `p^k ∣ n` for every prime factor `p` of `n`. -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- `0` is `k`-full for all `k`. -/
theorem Full.zero_right (k : ℕ) : k.Full 0 := by
  simp [Nat.Full]

/-- `1` is `k`-full for all `k`. -/
theorem Full.one_right (k : ℕ) : k.Full 1 := by
  simp [Nat.Full]

/-- Monotonicity of `k`-fullness in the exponent `k`. -/
theorem Full.mono {k m n : ℕ} (hkm : k ≤ m) (h : m.Full n) : k.Full n :=
  fun p hp => pow_dvd_of_le_of_pow_dvd hkm (h p hp)

/-- Product of two `k`-full numbers is `k`-full. -/
theorem Full.mul {k a b : ℕ} (ha : k.Full a) (hb : k.Full b) : k.Full (a * b) := by
  by_cases hab : a * b = 0
  · rw [hab]
    exact Full.zero_right k
  · have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
    intro p hp
    obtain ⟨hpp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    rcases hpp.dvd_mul.mp hdvd with hda | hdb
    · exact dvd_mul_of_dvd_left (ha p (Nat.mem_primeFactors.mpr ⟨hpp, hda, ha0⟩)) b
    · exact dvd_mul_of_dvd_right (hb p (Nat.mem_primeFactors.mpr ⟨hpp, hdb, hb0⟩)) a

/-- Any $m$-th power $a^m$ with $k \le m$ is $k$-full. -/
theorem Full.pow_of_le {k m : ℕ} (hkm : k ≤ m) (a : ℕ) : k.Full (a ^ m) := by
  by_cases ha0 : a = 0
  · subst ha0
    rcases eq_or_ne m 0 with rfl | hm0
    · simp [Full.one_right]
    · rw [zero_pow hm0]
      exact Full.zero_right k
  · intro p hp
    obtain ⟨hpp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpa : p ∣ a := hpp.dvd_of_dvd_pow hdvd
    exact pow_dvd_of_le_of_pow_dvd hkm (pow_dvd_pow_of_dvd hpa m)

/-- Every number of the form $a^2 b^3$ is $2$-powerful. -/
theorem two_full_sq_mul_cube (a b : ℕ) : (2).Full (a ^ 2 * b ^ 3) :=
  Full.mul (Full.pow_of_le (le_refl 2) a) (Full.pow_of_le (by omega : 2 ≤ 3) b)

/-- **Structure Theorem for $2$-Powerful Numbers**:
Every $2$-powerful natural number $n$ can be written as $n = a^2 b^3$ for some $a, b \in \mathbb{N}$. -/
theorem exists_sq_mul_cube_of_two_full : ∀ n : ℕ, (2).Full n → ∃ a b : ℕ, n = a ^ 2 * b ^ 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn1 : n ≤ 1
    · have h01 : n = 0 ∨ n = 1 := by omega
      rcases h01 with rfl | rfl
      · exact ⟨0, 1, by ring⟩
      · exact ⟨1, 1, by ring⟩
    · have hn_gt1 : 1 < n := by omega
      obtain ⟨p, hp_def⟩ : ∃ p, p = n.minFac := ⟨n.minFac, rfl⟩
      have hpp : Nat.Prime p := hp_def ▸ Nat.minFac_prime (by omega)
      have hpn : p ∣ n := hp_def ▸ Nat.minFac_dvd n
      have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpn, by omega⟩
      have hp2 : p ^ 2 ∣ n := hn p hp_mem
      have hp_gt1 : 1 < p := hpp.one_lt
      by_cases hcase : p ^ 3 ∣ n ∧ ¬ (p ^ 4 ∣ n)
      · obtain ⟨⟨m, hnm⟩, hnp4⟩ := hcase
        have hm0 : m ≠ 0 := by rintro rfl; omega
        have hpm : ¬ (p ∣ m) := by
          rintro ⟨c, rfl⟩
          apply hnp4
          refine ⟨c, ?_⟩
          linear_combination hnm
        have hm_full : (2).Full m := by
          intro q hq
          obtain ⟨hqp, hqm, _⟩ := Nat.mem_primeFactors.mp hq
          have hq_ne_p : q ≠ p := fun heq => hpm (heq ▸ hqm)
          have hcop : Nat.Coprime (q ^ 2) (p ^ 3) :=
            ((hqp.coprime_iff_not_dvd.mpr fun h => hq_ne_p ( (Nat.prime_dvd_prime_iff_eq hqp hpp).mp h )).pow_left 2).pow_right 3
          have hq_n : q ^ 2 ∣ p ^ 3 * m := by
            rw [← hnm]
            exact hn q (Nat.mem_primeFactors.mpr ⟨hqp, hnm ▸ dvd_mul_of_dvd_right hqm (p ^ 3), by omega⟩)
          exact hcop.dvd_of_dvd_mul_left hq_n
        have hm_lt : m < n := by
          have : 1 < p ^ 3 := one_lt_pow₀ hp_gt1 (by omega)
          nlinarith [Nat.pos_of_ne_zero hm0]
        obtain ⟨a, b, rfl⟩ := ih m hm_lt hm_full
        exact ⟨a, p * b, by linear_combination hnm⟩
      · obtain ⟨m, hnm⟩ := hp2
        have hm0 : m ≠ 0 := by rintro rfl; omega
        have hm_full : (2).Full m := by
          intro q hq
          obtain ⟨hqp, hqm, _⟩ := Nat.mem_primeFactors.mp hq
          by_cases hqp_eq : q = p
          · subst q
            have hp3 : p ^ 3 ∣ n := by
              obtain ⟨c, rfl⟩ := hqm
              exact ⟨c, by linear_combination hnm⟩
            have hp4 : p ^ 4 ∣ n := by
              by_contra hnp4
              exact hcase ⟨hp3, hnp4⟩
            obtain ⟨c, hc⟩ := hp4
            have hmc : m = p ^ 2 * c := by
              have hp2_pos : 0 < p ^ 2 := pow_pos hpp.pos 2
              apply Nat.eq_of_mul_eq_mul_left hp2_pos
              calc
                p ^ 2 * m = n := hnm.symm
                _ = p ^ 4 * c := hc
                _ = p ^ 2 * (p ^ 2 * c) := by ring
            exact ⟨c, hmc⟩
          · have hcop : Nat.Coprime (q ^ 2) (p ^ 2) :=
              ((hqp.coprime_iff_not_dvd.mpr fun h => hqp_eq ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp h)).pow_left 2).pow_right 2
            have hq_n : q ^ 2 ∣ p ^ 2 * m := by
              rw [← hnm]
              exact hn q (Nat.mem_primeFactors.mpr ⟨hqp, hnm ▸ dvd_mul_of_dvd_right hqm (p ^ 2), by omega⟩)
            exact hcop.dvd_of_dvd_mul_left hq_n
        have hm_lt : m < n := by
          have : 1 < p ^ 2 := one_lt_pow₀ hp_gt1 (by omega)
          nlinarith [Nat.pos_of_ne_zero hm0]
        obtain ⟨a, b, rfl⟩ := ih m hm_lt hm_full
        exact ⟨p * a, b, by linear_combination hnm⟩

/-- Equivalence: `n` is $2$-powerful if and only if $n = a^2 b^3$ for some $a, b \in \mathbb{N}$. -/
theorem two_full_iff_exists_sq_mul_cube (n : ℕ) :
    (2).Full n ↔ ∃ a b : ℕ, n = a ^ 2 * b ^ 3 :=
  ⟨exists_sq_mul_cube_of_two_full n, fun ⟨a, b, h⟩ => h ▸ two_full_sq_mul_cube a b⟩

end Nat

namespace Erdos940

/-- Helper lemma: If `(2).Full s` and `s ≤ 7`, then `s ∈ {0, 1, 4}`. -/
lemma two_full_le_seven {s : ℕ} (hs : (2).Full s) (hle : s ≤ 7) :
    s = 0 ∨ s = 1 ∨ s = 4 := by
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; rfl
  · right; left; rfl
  · exfalso
    have := hs 2 (by norm_num [Nat.mem_primeFactors])
    omega
  · exfalso
    have := hs 3 (by norm_num [Nat.mem_primeFactors])
    omega
  · right; right; rfl
  · exfalso
    have := hs 5 (by norm_num [Nat.mem_primeFactors])
    omega
  · exfalso
    have := hs 2 (by norm_num [Nat.mem_primeFactors])
    omega
  · exfalso
    have := hs 7 (by norm_num [Nat.mem_primeFactors])
    omega

/-- **Exception to Sums of Three Powerful Numbers (`erdos_940.variants.three_powerful`)**:
The integer $7$ cannot be written as the sum of a multiset of at most $3$ $2$-powerful numbers.
This demonstrates that the `∀ᶠ x in atTop` quantifier in Heath-Brown's theorem (`JSP-000782`)
cannot be strengthened to all positive integers. -/
theorem seven_not_sum_three_powerful :
    ¬ ∃ S : Multiset ℕ, S.card ≤ 3 ∧ (∀ s ∈ S, (2).Full s) ∧ S.sum = 7 := by
  rintro ⟨S, hcard, hfull, hsum⟩
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · rw [Multiset.card_eq_zero.mp h0, Multiset.sum_zero] at hsum
    omega
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
    simp only [Multiset.sum_singleton] at hsum
    rcases two_full_le_seven (hfull a (by simp)) (by omega) with rfl | rfl | rfl <;> omega
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h2
    have hsum' : a + b = 7 := by simpa using hsum
    rcases two_full_le_seven (hfull a (by simp)) (by omega) with rfl | rfl | rfl <;>
      rcases two_full_le_seven (hfull b (by simp)) (by omega) with rfl | rfl | rfl <;> omega
  · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp h3
    have hsum' : a + (b + c) = 7 := by simpa using hsum
    rcases two_full_le_seven (hfull a (by simp)) (by omega) with rfl | rfl | rfl <;>
      rcases two_full_le_seven (hfull b (by simp)) (by omega) with rfl | rfl | rfl <;>
        rcases two_full_le_seven (hfull c (by simp)) (by omega) with rfl | rfl | rfl <;> omega

end Erdos940

#print axioms Nat.two_full_iff_exists_sq_mul_cube
#print axioms Erdos940.seven_not_sum_three_powerful
