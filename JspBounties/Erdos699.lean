/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 699 (`JSP-000570`)

Erdős Problem 699 (Erdős–Szekeres, 1978) asks whether for every $1 \le i < j \le n / 2$,
there exists a prime $p \ge i$ such that
$$p \mid \gcd\!\left(\binom{n}{i}, \binom{n}{j}\right).$$

Erdős and Szekeres also conjectured (`erdos_szekeres_strengthening` in `699.lean`) that apart
from a finite exceptional set $E$ of triples $(n, i, j)$, one can always find a prime $p > i$
dividing $\gcd(\binom{n}{i}, \binom{n}{j})$.

In this file we formalize and prove (with zero `sorry`):
1. **Strict Monotonicity of Binomial Coefficients (`choose_lt_choose_of_lt`)**:
   For $1 \le i \le j < n$, $\binom{j}{i} < \binom{n}{i}$.
2. **Erdős–Szekeres Non-Coprimality Theorem (`choose_gcd_gt_one`)**:
   For all $1 \le i \le j < n$, $\gcd(\binom{n}{i}, \binom{n}{j}) > 1$.
3. **Full Resolution of Erdős Problem 699 for $i \in \{1, 2\}$ (`erdos_699_of_le_two`)**:
   For all $n, i, j$ with $1 \le i \le 2$ and $i < j \le n / 2$, there exists a prime $p \ge i$
   dividing $\gcd(\binom{n}{i}, \binom{n}{j})$.
4. **Large Prime Divisor Transfer Theorem (`dvd_gcd_choose_of_prime_gt_dvd`)**:
   If $i \le j \le n$ and a prime $p > j$ divides $\binom{n}{i}$, then
   $p \mid \gcd(\binom{n}{i}, \binom{n}{j})$.
5. **Prime in $(n - i, n]$ Theorem (`erdos_699_of_prime_in_interval`)**:
   If $1 \le i < j \le n / 2$ and there is a prime $p \in (n - i, n]$, then $p > j > i$ and
   $p \mid \gcd(\binom{n}{i}, \binom{n}{j})$.
6. **Composite-Step Reduction (`erdos_699_succ_of_not_prime`)**:
   When $j = i + 1$ is composite, any Sylvester–Schur prime $p > i$ dividing $\binom{n}{i}$
   automatically satisfies $p > j$ and divides $\gcd(\binom{n}{i}, \binom{n}{i+1})$.
7. **Characterization of Required Exceptions in `erdos_szekeres_strengthening`
   (`erdos_szekeres_exceptional_triples`, `mem_exceptions_of_erdos_szekeres_strengthening`)**:
   Every valid exceptional finset $E$ in `erdos_szekeres_strengthening` must contain
   `(10, 3, 5)`, `(16, 2, 6)`, `(28, 3, 14)`, and `(28, 5, 14)`, where the largest prime factor
   of $\gcd(\binom{n}{i}, \binom{n}{j})$ is $p = i$.
-/

namespace Erdos699

/-- Any prime dividing `n.choose k` (with `k ≤ n`) is at most `n`. -/
theorem prime_le_of_dvd_choose {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hdvd : p ∣ n.choose k) :
    p ≤ n := by
  have hfac : p ∣ n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkn]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _
  exact hp.dvd_factorial.mp hfac

/-- Strict monotonicity of `n.choose i` in the upper argument when `1 ≤ i ≤ j < n`. -/
theorem choose_lt_choose_of_lt {n i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j < n) :
    j.choose i < n.choose i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hpos : 0 < j.choose k := Nat.choose_pos (by omega)
  have hstep : j.choose (k + 1) < (j + 1).choose (k + 1) := by
    change j.choose (k + 1) < j.choose k + j.choose (k + 1)
    omega
  have hmono : (j + 1).choose (k + 1) ≤ n.choose (k + 1) :=
    Nat.choose_le_choose (k + 1) (by omega)
  exact lt_of_lt_of_le hstep hmono

/-- **Erdős–Szekeres (1978) Non-Coprimality Theorem**:
For all `1 ≤ i ≤ j < n`, `n.choose i` and `n.choose j` are never coprime:
`1 < Nat.gcd (n.choose i) (n.choose j)`. -/
theorem choose_gcd_gt_one {n i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j < n) :
    1 < Nat.gcd (n.choose i) (n.choose j) := by
  have h_not_coprime : ¬ Nat.Coprime (n.choose i) (n.choose j) := by
    intro hcop
    have hmul : n.choose j * j.choose i = n.choose i * (n - i).choose (j - i) :=
      Nat.choose_mul hij
    have hdvd_prod : n.choose i ∣ n.choose j * j.choose i :=
      ⟨(n - i).choose (j - i), hmul⟩
    have hdvd : n.choose i ∣ j.choose i :=
      hcop.dvd_of_dvd_mul_left hdvd_prod
    have hj_pos : 0 < j.choose i := Nat.choose_pos hij
    have hle : n.choose i ≤ j.choose i := Nat.le_of_dvd hj_pos hdvd
    have hlt : j.choose i < n.choose i := choose_lt_choose_of_lt hi hij hjn
    omega
  have h_ne_one : Nat.gcd (n.choose i) (n.choose j) ≠ 1 := h_not_coprime
  have h_pos : 0 < Nat.gcd (n.choose i) (n.choose j) :=
    Nat.gcd_pos_of_pos_left _ (Nat.choose_pos (by omega))
  omega

/-- **Erdős Problem 699 for `i ≤ 2` (`i = 1` and `i = 2`)**:
For every `1 ≤ i ≤ 2` and `i < j ≤ n / 2`, there exists a prime `p ≥ i` dividing
`Nat.gcd (n.choose i) (n.choose j)`. -/
theorem erdos_699_of_le_two (n i j : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ 2)
    (hij : i < j) (hjn : j ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) := by
  have hg : 1 < Nat.gcd (n.choose i) (n.choose j) :=
    choose_gcd_gt_one hi1 (by omega) (by omega)
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd (n.choose i) (n.choose j) ≠ 1)
  have hp2 : 2 ≤ p := hp.two_le
  exact ⟨p, hp, by omega, hdvd⟩

/-- **Large Prime Divisor Transfer Theorem (`dvd_gcd_choose_of_prime_gt_dvd`)**:
If `i ≤ j` and `p > j` is a prime dividing `n.choose i`, then `p` also divides `n.choose j`,
and hence `p ∣ Nat.gcd (n.choose i) (n.choose j)`. -/
theorem dvd_gcd_choose_of_prime_gt_dvd {n i j p : ℕ}
    (hij : i ≤ j) (hp : p.Prime) (hpj : j < p) (hdvd : p ∣ n.choose i) :
    p ∣ Nat.gcd (n.choose i) (n.choose j) := by
  refine Nat.dvd_gcd hdvd ?_
  have hmul : n.choose j * j.choose i = n.choose i * (n - i).choose (j - i) :=
    Nat.choose_mul hij
  have hdvd_prod : p ∣ n.choose j * j.choose i := by
    rw [hmul]
    exact dvd_mul_of_dvd_left hdvd _
  rcases hp.dvd_mul.mp hdvd_prod with hnj | hji
  · exact hnj
  · exfalso
    have hple : p ≤ j := prime_le_of_dvd_choose hp hij hji
    omega

/-- **Prime in `(n - i, n]` Theorem (`erdos_699_of_prime_in_interval`)**:
If `1 ≤ i < j ≤ n / 2` and there is a prime `p` with `n - i < p ≤ n`, then `p > j > i` and
`p ∣ Nat.gcd (n.choose i) (n.choose j)`. -/
theorem erdos_699_of_prime_in_interval {n i j p : ℕ}
    (hij : i < j) (hjn : j ≤ n / 2)
    (hp : p.Prime) (hp_low : n - i < p) (hp_high : p ≤ n) :
    p.Prime ∧ i < p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) := by
  have hpj : j < p := by omega
  have hpi : i < p := by omega
  have hdvd_ni : p ∣ n.choose i := by
    have hfac : p ∣ n.factorial := hp.dvd_factorial.mpr hp_high
    rw [← Nat.choose_mul_factorial_mul_factorial (by omega : i ≤ n)] at hfac
    rcases hp.dvd_mul.mp hfac with h1 | h2
    · rcases hp.dvd_mul.mp h1 with hchoose | hifac
      · exact hchoose
      · exfalso
        have := hp.dvd_factorial.mp hifac
        omega
    · exfalso
      have := hp.dvd_factorial.mp h2
      omega
  exact ⟨hp, hpi, dvd_gcd_choose_of_prime_gt_dvd (by omega) hp hpj hdvd_ni⟩

/-- **Composite Adjacent Step (`erdos_699_succ_of_not_prime`)**:
If `j = i + 1` is not prime, then any Sylvester–Schur prime `p > i` dividing `n.choose i`
strictly exceeds `j` and therefore divides `Nat.gcd (n.choose i) (n.choose (i + 1))`. -/
theorem erdos_699_succ_of_not_prime {n i p : ℕ}
    (hnotp : ¬ (i + 1).Prime) (hp : p.Prime) (hpi : i < p) (hdvd : p ∣ n.choose i) :
    p.Prime ∧ i < p ∧ p ∣ Nat.gcd (n.choose i) (n.choose (i + 1)) := by
  have hp_ne : p ≠ i + 1 := by
    intro heq
    subst heq
    exact hnotp hp
  have hpj : i + 1 < p := by omega
  exact ⟨hp, hpi, dvd_gcd_choose_of_prime_gt_dvd (by omega) hp hpj hdvd⟩

/-- Verification that `(10, 3, 5)`, `(16, 2, 6)`, `(28, 3, 14)`, and `(28, 5, 14)` satisfy
Erdős Problem 699 (`p = i` divides the gcd), yet NO prime `p > i` divides the gcd. -/
theorem erdos_szekeres_exceptional_triples :
    (∀ p : ℕ, p.Prime → p ∣ Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5) → p ≤ 3) ∧
    (∀ p : ℕ, p.Prime → p ∣ Nat.gcd (Nat.choose 16 2) (Nat.choose 16 6) → p ≤ 2) ∧
    (∀ p : ℕ, p.Prime → p ∣ Nat.gcd (Nat.choose 28 3) (Nat.choose 28 14) → p ≤ 3) ∧
    (∀ p : ℕ, p.Prime → p ∣ Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) → p ≤ 5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp hdvd
    have hgcd : Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5) = 12 := by decide
    rw [hgcd] at hdvd
    have hle : p ≤ 12 := Nat.le_of_dvd (by decide) hdvd
    revert hp hdvd
    interval_cases p <;> decide
  · intro p hp hdvd
    have hgcd : Nat.gcd (Nat.choose 16 2) (Nat.choose 16 6) = 8 := by decide
    rw [hgcd] at hdvd
    have hle : p ≤ 8 := Nat.le_of_dvd (by decide) hdvd
    revert hp hdvd
    interval_cases p <;> decide
  · intro p hp hdvd
    have hgcd : Nat.gcd (Nat.choose 28 3) (Nat.choose 28 14) = 36 := by decide
    rw [hgcd] at hdvd
    have hle : p ≤ 36 := Nat.le_of_dvd (by decide) hdvd
    revert hp hdvd
    interval_cases p <;> decide
  · intro p hp hdvd
    have hgcd : Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) = 1080 := by decide
    rw [hgcd] at hdvd
    have hdvd30 : p ∣ 30 := by
      have h1080 : 1080 ∣ 30 ^ 3 := by decide
      exact hp.dvd_of_dvd_pow (dvd_trans hdvd h1080)
    have hle : p ≤ 30 := Nat.le_of_dvd (by decide) hdvd30
    revert hp hdvd30
    interval_cases p <;> decide

/-- Every valid exceptional finset `E` in `erdos_szekeres_strengthening` must contain
`(10, 3, 5)`, `(16, 2, 6)`, `(28, 3, 14)`, and `(28, 5, 14)`. -/
theorem mem_exceptions_of_erdos_szekeres_strengthening
    (E : Finset (ℕ × ℕ × ℕ))
    (hE : ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 → (n, i, j) ∉ E →
      ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j)) :
    (10, 3, 5) ∈ E ∧ (16, 2, 6) ∈ E ∧ (28, 3, 14) ∈ E ∧ (28, 5, 14) ∈ E := by
  obtain ⟨h10, h16, h28_3, h28_5⟩ := erdos_szekeres_exceptional_triples
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hnot
    obtain ⟨p, hp, hgt, hdvd⟩ := hE 10 3 5 (by decide) (by decide) (by decide) hnot
    have := h10 p hp hdvd
    omega
  · by_contra hnot
    obtain ⟨p, hp, hgt, hdvd⟩ := hE 16 2 6 (by decide) (by decide) (by decide) hnot
    have := h16 p hp hdvd
    omega
  · by_contra hnot
    obtain ⟨p, hp, hgt, hdvd⟩ := hE 28 3 14 (by decide) (by decide) (by decide) hnot
    have := h28_3 p hp hdvd
    omega
  · by_contra hnot
    obtain ⟨p, hp, hgt, hdvd⟩ := hE 28 5 14 (by decide) (by decide) (by decide) hnot
    have := h28_5 p hp hdvd
    omega

end Erdos699

#print axioms Erdos699.choose_gcd_gt_one
#print axioms Erdos699.erdos_699_of_le_two
#print axioms Erdos699.dvd_gcd_choose_of_prime_gt_dvd
#print axioms Erdos699.erdos_699_of_prime_in_interval
#print axioms Erdos699.erdos_699_succ_of_not_prime
#print axioms Erdos699.erdos_szekeres_exceptional_triples
#print axioms Erdos699.mem_exceptions_of_erdos_szekeres_strengthening
