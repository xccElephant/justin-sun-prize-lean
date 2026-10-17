import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

/-!
# Erdős Problem 366 (JSP-000302)

*Reference:* [erdosproblems.com/366](https://www.erdosproblems.com/366)

Erdős and Graham asked whether $(8, 9)$ is the only pair of consecutive integers $n, n+1$
with $n$ $3$-full and $n+1$ $2$-full. The answer is no: $12167 = 23^3$ and
$12168 = 2^3 \cdot 3^2 \cdot 13^2$ is another such pair, already known to Golomb (1970).
-/

namespace Nat

/-- A natural number $n$ is said to be $k$-full (or $k$-powerful) if for every prime factor $p$ of $n$,
the $k$-th power $p^k$ also divides $n$. -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

end Nat

namespace Erdos366

private lemma prime_eq_of_dvd_pow {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ∣ q ^ k) :
    p = q :=
  ((hq.dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow h)).symm

/-- Note that $8$ is $3$-full and $9$ is $2$-full. -/
theorem exists_three_full_then_two_full : ∃ n > 0, (3).Full n ∧ (2).Full (n + 1) := by
  refine ⟨8, by norm_num, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpow : p ∣ (2 : ℕ) ^ 3 := by norm_num at hd ⊢; exact hd
    have heq : p = 2 := prime_eq_of_dvd_pow hp (by norm_num) hpow
    subst p
    norm_num
  · intro p hp
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpow : p ∣ (3 : ℕ) ^ 2 := by norm_num at hd ⊢; exact hd
    have heq : p = 3 := prime_eq_of_dvd_pow hp (by norm_num) hpow
    subst p
    norm_num

/-- Erdős and Graham asked whether $(8, 9)$ is the only pair of consecutive integers $n, n+1$
with $n$ $3$-full and $n+1$ $2$-full. The answer is no, witnessed by $n = 12167$. -/
theorem erdos_366.variants.three_two :
    ¬ ∀ n > 0, (3).Full n ∧ (2).Full (n + 1) → n = 8 := by
  intro h
  have h12167 : (3).Full 12167 ∧ (2).Full (12167 + 1) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
      have hpow : p ∣ (23 : ℕ) ^ 3 := by norm_num at hd ⊢; exact hd
      have heq : p = 23 := prime_eq_of_dvd_pow hp (by norm_num) hpow
      subst p
      norm_num
    · intro p hp
      obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
      have hprod : p ∣ (2 : ℕ) ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num at hd ⊢; exact hd
      rcases hp.dvd_mul.mp hprod with hab | hc
      · rcases hp.dvd_mul.mp hab with ha | hb
        · have heq : p = 2 := prime_eq_of_dvd_pow hp (by norm_num) ha
          subst p
          norm_num
        · have heq : p = 3 := prime_eq_of_dvd_pow hp (by norm_num) hb
          subst p
          norm_num
      · have heq : p = 13 := prime_eq_of_dvd_pow hp (by norm_num) hc
        subst p
        norm_num
  have := h 12167 (by norm_num) h12167
  omega

#print axioms exists_three_full_then_two_full
#print axioms erdos_366.variants.three_two

end Erdos366
