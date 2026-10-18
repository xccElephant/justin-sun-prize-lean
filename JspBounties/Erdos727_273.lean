/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 727 (`JSP-000595`) & Erdős Problem 273 (`JSP-000234`)

*References:*
- [erdosproblems.com/727](https://www.erdosproblems.com/727) (`FormalConjectures/ErdosProblems/727.lean`)
- [Ba29] Balakram, H., *On the values of $n$ which make $(2n)!/(n+1)!(n+1)!$ an integer*.
  J. Indian Math. Soc. 18 (1929), 97–100.
- [EGRS75] Erdős, P., Graham, R. L., Ruzsa, I. Z., and Straus, E. G.,
  *On the prime factors of $\binom{2n}{n}$*. Math. Comp. 29 (1975), 83–92.
- [erdosproblems.com/273](https://www.erdosproblems.com/273) (`FormalConjectures/ErdosProblems/273.lean`)
- [ErGr80] Erdős, P. and Graham, R. L., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathématique 28 (1980), p. 24.

This file formalizes complete, zero-`sorry` proofs of:
1. **`erdos_727.variants.k_1` (`JSP-000595`)**:
   There are infinitely many $n \in \mathbb{N}$ such that $((n + 1)!)^2 \mid (2n)!$
   (equivalently, $(n + 1)^2 \mid \binom{2n}{n}$, i.e., $n + 1$ divides the $n$-th Catalan number
   $C_n = \frac{1}{n+1}\binom{2n}{n}$).
2. **`erdos_273.variants.three` (`JSP-000234`)**:
   There exists a strict covering system of $\mathbb{N}$ (and of $\mathbb{Z}$) all of whose moduli
   are of the form $p - 1$ for primes $p \ge 3$ (Selfridge's 12-modulus covering system using the
   prime-shifted divisors $\{2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180\}$ of $360$).
-/

open scoped Nat Pointwise
open Finset

/-!
## Part 1: Erdős Problem 727 (`JSP-000595`) — Balakram's Theorem ($k = 1$)
-/

namespace Erdos727

/-- `(n + 1)! ^ 2 ∣ (2 * n)!` is equivalent to `(n + 1) ^ 2 ∣ n.centralBinom`. -/
lemma factorial_sq_dvd_two_mul_factorial_iff (n : ℕ) :
    (n + 1)! ^ 2 ∣ (2 * n)! ↔ (n + 1) ^ 2 ∣ n.centralBinom := by
  have hchoose := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega, ← Nat.centralBinom_eq_two_mul_choose] at hchoose
  have h1 : (n + 1)! ^ 2 = (n + 1) ^ 2 * (n ! * n !) := by
    rw [Nat.factorial_succ]; ring
  have h2 : (2 * n)! = n.centralBinom * (n ! * n !) := by
    rw [← hchoose]; ring
  have hne : n ! * n ! ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero n)
  rw [h1, h2, mul_dvd_mul_iff_right hne]

/-- **Kummer's Carry Lower Bound**: If $p$ is prime and $s$ is a finite set of positive exponents
$i \ge 1$ at which doubling $n$ produces a carry modulo $p^i$ (i.e., $p^i \le 2(n \bmod p^i)$),
then $p^{\#s} \mid \binom{2n}{n}$. -/
lemma prime_pow_dvd_centralBinom_of_carries {p n : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ i ∈ s, 1 ≤ i ∧ p ^ i ≤ 2 * (n % p ^ i)) :
    p ^ s.card ∣ n.centralBinom := by
  rw [hp.pow_dvd_iff_le_factorization (Nat.centralBinom_ne_zero n)]
  have h2n : n.centralBinom = (n + n).choose n := by
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  rw [h2n, Nat.factorization_choose' hp (Nat.lt_succ_self (Nat.log p (n + n)))]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨h1, h2⟩ := hs i hi
  rw [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨h1, ?_⟩, by simpa [two_mul] using h2⟩
  have hle : p ^ i ≤ n + n := by
    have := Nat.mod_le n (p ^ i)
    omega
  exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp.one_lt hle)

/-- Two distinct carrying levels $i \ne j$ ($i, j \ge 1$) yield $p^2 \mid \binom{2n}{n}$. -/
lemma prime_sq_dvd_centralBinom_of_two_carries {p n i j : ℕ} (hp : p.Prime)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j)
    (h₁ : p ^ i ≤ 2 * (n % p ^ i)) (h₂ : p ^ j ≤ 2 * (n % p ^ j)) :
    p ^ 2 ∣ n.centralBinom := by
  have h := prime_pow_dvd_centralBinom_of_carries hp {i, j} (by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact ⟨hi, h₁⟩
    · exact ⟨hj, h₂⟩)
  rwa [Finset.card_pair hij] at h

/-- Four strictly increasing carrying levels $i_1 < i_2 < i_3 < i_4$ yield $p^4 \mid \binom{2n}{n}$. -/
lemma prime_pow_four_dvd_centralBinom_of_four_carries {p n i₁ i₂ i₃ i₄ : ℕ} (hp : p.Prime)
    (h1 : 1 ≤ i₁) (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄)
    (c₁ : p ^ i₁ ≤ 2 * (n % p ^ i₁)) (c₂ : p ^ i₂ ≤ 2 * (n % p ^ i₂))
    (c₃ : p ^ i₃ ≤ 2 * (n % p ^ i₃)) (c₄ : p ^ i₄ ≤ 2 * (n % p ^ i₄)) :
    p ^ 4 ∣ n.centralBinom := by
  let s : Finset ℕ := {i₁, i₂, i₃, i₄}
  have hcard : s.card = 4 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_pair (by omega)]
  rw [← hcard]
  apply prime_pow_dvd_centralBinom_of_carries hp s
  intro k hk
  simp only [s, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨h1, c₁⟩
  · exact ⟨by omega, c₂⟩
  · exact ⟨by omega, c₃⟩
  · exact ⟨by omega, c₄⟩

/-- **Unified Level-1 & Level-2 Carry Lemma**:
For any prime $p$ and any $m, k \in \mathbb{N}$ such that $(2k + 1) p < 2m$ and $m \le (k + 1) p$,
the integer $n = m p - 1$ has carries at levels $1$ and $2$ in base $p$, so $p^2 \mid \binom{2n}{n}$. -/
lemma prime_sq_dvd_centralBinom_of_mul_sub_one {p m k : ℕ} (hp : p.Prime)
    (hlo : (2 * k + 1) * p < 2 * m) (hhi : m ≤ (k + 1) * p) :
    p ^ 2 ∣ (m * p - 1).centralBinom := by
  have hp2 : 2 ≤ p := hp.two_le
  have hkm : k * p < m := by nlinarith only [hlo, hp2]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, m = k * (p' + 1) + r + 1 := ⟨m - 1 - k * (p' + 1), by omega⟩
  have hr_lt : r < p' + 1 := by nlinarith only [hhi, hr]
  have h2r : p' ≤ 2 * r := by nlinarith only [hlo, hr]
  have hn1 : m * (p' + 1) - 1 = p' + (k * (p' + 1) + r) * (p' + 1) := by
    rw [hr]
    have : (k * (p' + 1) + r + 1) * (p' + 1) = p' + (k * (p' + 1) + r) * (p' + 1) + 1 := by ring
    omega
  have hn2 : m * (p' + 1) - 1 = (r * (p' + 1) + p') + k * (p' + 1) ^ 2 := by
    rw [hn1]
    ring
  have hrem_lt : r * (p' + 1) + p' < (p' + 1) ^ 2 := by nlinarith only [hr_lt]
  apply prime_sq_dvd_centralBinom_of_two_carries hp le_rfl (by decide) (by decide : 1 ≠ 2)
  · rw [pow_one, hn1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hn2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem_lt]
    nlinarith only [h2r, hp2]

/-- **Balakram's First Family ($c = 1$)**:
If $p < q$ are primes with $3 < p$, $3 p < 2 q$, and $q < 2 p$, then $n = p q - 1$ satisfies
$(n + 1)^2 \mid \binom{2n}{n}$. -/
theorem balakram_case_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (_hp3 : 3 < p) (hpq : p < q) (hlo : 3 * p < 2 * q) (hhi : q < 2 * p) :
    (p * q) ^ 2 ∣ (p * q - 1).centralBinom := by
  have hq_dvd : q ^ 2 ∣ (p * q - 1).centralBinom :=
    prime_sq_dvd_centralBinom_of_mul_sub_one (k := 0) hq (by omega) (by omega)
  have hp_dvd : p ^ 2 ∣ (p * q - 1).centralBinom := by
    rw [mul_comm p q]
    exact prime_sq_dvd_centralBinom_of_mul_sub_one (k := 1) hp (by omega) (by omega)
  have hcop : Nat.Coprime (p ^ 2) (q ^ 2) :=
    ((Nat.coprime_primes hp hq).mpr (ne_of_lt hpq)).pow 2 2
  rw [mul_pow]
  exact hcop.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd

/-- If $m \ge 2$ is even and not a power of $2$, then $n = 4 m + 3$ has at least $4$ carries in
base $2$, so $2^4 \mid \binom{2n}{n}$. -/
lemma two_pow_four_dvd_centralBinom_of_even_not_pow_two {m : ℕ}
    (hm_even : 2 ∣ m) (hm_ge : 2 ≤ m) (hnot_pow : ∀ k : ℕ, m ≠ 2 ^ k) :
    2 ^ 4 ∣ (4 * m + 3).centralBinom := by
  have hm0 : m ≠ 0 := by omega
  set a := m.factorization 2
  set b := Nat.log 2 m
  have ha_ge : 1 ≤ a := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hm0).mp hm_even
  have ha_dvd : 2 ^ a ∣ m := Nat.ordProj_dvd m 2
  have hb_le : 2 ^ b ≤ m := Nat.pow_log_le_self 2 hm0
  have hb_lt : m < 2 ^ (b + 1) := Nat.lt_pow_succ_log_self (by decide) m
  have hab : a < b := by
    have hale : a ≤ b := Nat.le_log_of_pow_le (by decide) (Nat.le_of_dvd (by omega) ha_dvd)
    rcases eq_or_lt_of_le hale with heq | hlt
    · obtain ⟨u, hu⟩ := ha_dvd
      have hpow_eq : 2 ^ a = 2 ^ b := congrArg (2 ^ ·) heq
      have hu1 : u = 1 := by
        have h1 : 2 ^ a * 1 ≤ 2 ^ a * u := by omega
        have h2 : 2 ^ a * u < 2 ^ a * 2 := by
          calc 2 ^ a * u = m := hu.symm
            _ < 2 ^ (b + 1) := hb_lt
            _ = 2 ^ b * 2 := by ring
            _ = 2 ^ a * 2 := by rw [hpow_eq]
        have hpos : 0 < 2 ^ a := Nat.pow_pos (by decide)
        nlinarith only [h1, h2, hpos]
      exfalso
      exact hnot_pow a (by rw [hu, hu1, mul_one])
    · exact hlt
  set n := 4 * m + 3
  apply prime_pow_four_dvd_centralBinom_of_four_carries Nat.prime_two
    (i₁ := 1) (i₂ := 2) (i₃ := a + 3) (i₄ := b + 3)
    le_rfl (by omega) (by omega) (by omega)
  · dsimp [n]; omega
  · dsimp [n]; omega
  · set u := ordCompl[2] m
    have hmu : 2 ^ a * u = m := Nat.ordProj_mul_ordCompl_eq_self m 2
    have hu_odd : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hm0
    set q := u / 2
    have hu_div : u = 2 * q + 1 := by omega
    have hn_eq : n = (2 ^ (a + 2) + 3) + q * 2 ^ (a + 3) := by
      dsimp [n]
      rw [← hmu, hu_div]
      ring
    have hlt_a : 2 ^ (a + 2) + 3 < 2 ^ (a + 3) := by
      have h4 : 4 ≤ 2 ^ (a + 2) := by
        calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      have : 2 ^ (a + 3) = 2 ^ (a + 2) + 2 ^ (a + 2) := by ring
      omega
    rw [hn_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt_a]
    have : 2 ^ (a + 3) = 2 * 2 ^ (a + 2) := by ring
    omega
  · have hn_lt : n < 2 ^ (b + 3) := by
      dsimp [n]
      have : 2 ^ (b + 3) = 4 * 2 ^ (b + 1) := by ring
      omega
    have hn_ge : 2 ^ (b + 2) ≤ n := by
      dsimp [n]
      have : 2 ^ (b + 2) = 4 * 2 ^ b := by ring
      omega
    rw [Nat.mod_eq_of_lt hn_lt]
    have : 2 ^ (b + 3) = 2 * 2 ^ (b + 2) := by ring
    omega

/-- **Four-Times Product Family ($c = 4$)**:
If $p < q$ are primes with $3 < p$, $11 p < 8 q$, $2 q < 3 p$, and $p q - 1$ is not a power of $2$,
then $n = 4 p q - 1$ satisfies $(n + 1)^2 \mid \binom{2n}{n}$. -/
theorem balakram_case_four {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 < p) (hpq : p < q) (hlo : 11 * p < 8 * q) (hhi : 2 * q < 3 * p)
    (hnot_pow : ∀ k : ℕ, p * q - 1 ≠ 2 ^ k) :
    (4 * p * q) ^ 2 ∣ (4 * p * q - 1).centralBinom := by
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hq_odd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by omega)
  have hpq_ge : 16 ≤ p * q := by nlinarith only [hp3, hpq]
  have hm_even : 2 ∣ p * q - 1 := by
    have h1 : (p * q) % 2 = 1 := by rw [Nat.mul_mod, hp_odd, hq_odd]
    omega
  have hm_ge : 2 ≤ p * q - 1 := by omega
  have hn_eq : 4 * p * q - 1 = 4 * (p * q - 1) + 3 := by
    have : 4 * p * q = 4 * (p * q) := by ring
    omega
  have h2_dvd : 2 ^ 4 ∣ (4 * p * q - 1).centralBinom := by
    rw [hn_eq]
    exact two_pow_four_dvd_centralBinom_of_even_not_pow_two hm_even hm_ge hnot_pow
  have hp_dvd : p ^ 2 ∣ (4 * p * q - 1).centralBinom := by
    have h_eq : 4 * p * q - 1 = (4 * q) * p - 1 := by ring_nf
    rw [h_eq]
    exact prime_sq_dvd_centralBinom_of_mul_sub_one (k := 5) hp
      (by linarith only [hlo]) (by linarith only [hhi])
  have hq_dvd : q ^ 2 ∣ (4 * p * q - 1).centralBinom :=
    prime_sq_dvd_centralBinom_of_mul_sub_one (k := 2) hq
      (by linarith only [hhi]) (by linarith only [hlo])
  have hcop_pq : Nat.Coprime (p ^ 2) (q ^ 2) :=
    ((Nat.coprime_primes hp hq).mpr (ne_of_lt hpq)).pow 2 2
  have hcop_2p : Nat.Coprime (2 ^ 4) (p ^ 2) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow 4 2
  have hcop_2q : Nat.Coprime (2 ^ 4) (q ^ 2) :=
    ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow 4 2
  have hcop_2pq : Nat.Coprime (2 ^ 4) (p ^ 2 * q ^ 2) := hcop_2p.mul_right hcop_2q
  have h_eq : (4 * p * q) ^ 2 = 2 ^ 4 * (p ^ 2 * q ^ 2) := by ring
  rw [h_eq]
  exact hcop_2pq.mul_dvd_of_dvd_of_dvd h2_dvd (hcop_pq.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd)

/-- For every $t \in \mathbb{N}$, $3 \mid 2^{2t + 1} + 1$. -/
lemma two_odd_pow_add_one_mod_three (t : ℕ) : (2 ^ (2 * t + 1) + 1) % 3 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have : 2 ^ (2 * (t + 1) + 1) + 1 = 3 * 2 ^ (2 * t + 1) + (2 ^ (2 * t + 1) + 1) := by ring
    omega

/-- For primes $p, q > 3$, $(p q) \bmod 3 \ne 0$. -/
lemma prime_mul_mod_three_ne_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 < p) (hq3 : 3 < q) : (p * q) % 3 ≠ 0 := by
  intro hmod
  have hdvd : 3 ∣ p * q := Nat.dvd_of_mod_eq_zero hmod
  rcases Nat.prime_three.dvd_mul.mp hdvd with h3p | h3q
  · rcases (Nat.dvd_prime hp).mp h3p with h | h <;> omega
  · rcases (Nat.dvd_prime hq).mp h3q with h | h <;> omega

/-- If $p, q > 3$ are primes and $p q - 1 = 2^k$, then $k = 2t$ is even (and $t \ge 2$). -/
lemma even_of_prime_mul_sub_one_eq_two_pow {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 < p) (hq3 : 3 < q) (h : p * q - 1 = 2 ^ k) :
    ∃ t : ℕ, 2 ≤ t ∧ k = 2 * t := by
  have hpq : 16 ≤ p * q := by nlinarith only [hp3, hq3]
  have hk4 : 4 ≤ k := by
    by_contra! hlt
    interval_cases k <;> omega
  rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
  · exact ⟨t, by omega, rfl⟩
  · exfalso
    have heq : p * q = 2 ^ (2 * t + 1) + 1 := by omega
    have hmod := two_odd_pow_add_one_mod_three t
    rw [← heq] at hmod
    exact prime_mul_mod_three_ne_zero hp hq hp3 hq3 hmod

/-- If $p, q > 3$ are primes and $2^{2t} < p q - 1 < 2^{2t + 2}$, then $p q - 1$ is not a power of $2$. -/
lemma not_pow_two_of_between_even_pow {p q t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 < p) (hq3 : 3 < q)
    (hlo : 2 ^ (2 * t) < p * q - 1) (hhi : p * q - 1 < 2 ^ (2 * t + 2)) :
    ∀ k : ℕ, p * q - 1 ≠ 2 ^ k := by
  intro k heq
  rw [heq] at hlo hhi
  have hk_gt : 2 * t < k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlo
  have hk_lt : k < 2 * t + 2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hhi
  have hk_eq : k = 2 * t + 1 := by omega
  rw [hk_eq] at heq
  have hpq : 1 ≤ p * q := by nlinarith only [hp3, hq3]
  have hpq_eq : p * q = 2 ^ (2 * t + 1) + 1 := by omega
  have hmod := two_odd_pow_add_one_mod_three t
  rw [← hpq_eq] at hmod
  exact prime_mul_mod_three_ne_zero hp hq hp3 hq3 hmod

/-- For any prime $p \ge 3$, Bertrand's postulate gives a prime $q$ with $p < q < 2p$. -/
lemma exists_prime_gt_and_lt_two_mul {p : ℕ} (hp3 : 3 ≤ p) :
    ∃ q : ℕ, q.Prime ∧ p < q ∧ q < 2 * p := by
  obtain ⟨q, hq, hpq, hq2p⟩ := Nat.exists_prime_lt_and_le_two_mul p (by omega)
  refine ⟨q, hq, hpq, lt_of_le_of_ne hq2p ?_⟩
  rintro rfl
  rcases (Nat.dvd_prime hq).mp (dvd_mul_right 2 p) with h | h <;> omega

/-- Given any prime $p_0 \ge 5$, taking the maximum prime $p^*$ in $[p_0, 11 p_0 / 8]$ and a
Bertrand prime $s \in (p^*, 2 p^*)$ yields $p_0 \le p^*$, $8 p^* \le 11 p_0$, $p^* < s < 2 p^*$,
and $11 p_0 < 8 s$. -/
lemma exists_max_prime_in_interval_and_bertrand {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀5 : 5 ≤ p₀) :
    ∃ p s : ℕ, p.Prime ∧ s.Prime ∧ p₀ ≤ p ∧ 8 * p ≤ 11 * p₀ ∧
      p < s ∧ s < 2 * p ∧ 11 * p₀ < 8 * s := by
  let S := (Finset.Icc p₀ (11 * p₀ / 8)).filter Nat.Prime
  have hp₀_mem : p₀ ∈ S := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, by omega⟩, hp₀⟩
  let p := S.max' ⟨p₀, hp₀_mem⟩
  have hp_mem : p ∈ S := Finset.max'_mem S ⟨p₀, hp₀_mem⟩
  rw [Finset.mem_filter, Finset.mem_Icc] at hp_mem
  obtain ⟨⟨hp_ge, hp_le⟩, hp_prime⟩ := hp_mem
  have hp₀_le_p : p₀ ≤ p := Finset.le_max' S p₀ hp₀_mem
  obtain ⟨s, hs_prime, hps, hs2p⟩ := exists_prime_gt_and_lt_two_mul (p := p) (by omega)
  have hs_not_mem : s ∉ S := fun hs_mem =>
    not_lt_of_ge (Finset.le_max' S s hs_mem) hps
  rw [Finset.mem_filter, Finset.mem_Icc, not_and] at hs_not_mem
  have hs_gt : 11 * p₀ / 8 < s := by
    by_contra! hle
    exact hs_not_mem ⟨by omega, hle⟩ hs_prime
  exact ⟨p, s, hp_prime, hs_prime, hp₀_le_p, by omega, hps, hs2p, by omega⟩

/-- Corollary of `exists_max_prime_in_interval_and_bertrand`: for every prime $p_0 \ge 5$, there
exist primes $p < q$ with $p_0 \le p$, $11 p < 8 q$, and $q < 2 p$. -/
lemma exists_prime_pair_eleven_eighths {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀5 : 5 ≤ p₀) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p₀ ≤ p ∧ p < q ∧ 11 * p < 8 * q ∧ q < 2 * p := by
  obtain ⟨p, s, hp, hs, hp₀p, hp_le, hps, hs2p, hs_gt⟩ :=
    exists_max_prime_in_interval_and_bertrand hp₀ hp₀5
  rcases lt_or_ge (11 * p) (8 * s) with hlt | hge
  · exact ⟨p, s, hp, hs, hp₀p, hps, hlt, hs2p⟩
  · refine ⟨p₀, s, hp₀, hs, le_rfl, by omega, hs_gt, ?_⟩
    omega

/-- For primes $p, q > 3$, $3 p \ne 2 q$. -/
lemma three_mul_prime_ne_two_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) :
    3 * p ≠ 2 * q := by
  intro heq
  have hdvd : p ∣ 2 * q := ⟨3, by linarith only [heq]⟩
  rcases hp.dvd_mul.mp hdvd with hp2 | hpq_dvd
  · have := Nat.le_of_dvd (by decide) hp2; omega
  · rcases (Nat.dvd_prime hq).mp hpq_dvd with h | h <;> omega

/-- Any pair of primes $3 < p < q$ with $11 p < 8 q$, $q < 2p$, and $\forall k, p q - 1 \ne 2^k$
produces an integer $n \ge p q - 1$ satisfying $(n + 1)^2 \mid \binom{2n}{n}$. -/
lemma exists_good_of_valid_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 < p) (hpq : p < q) (hlo : 11 * p < 8 * q) (hhi : q < 2 * p)
    (hnot_pow : ∀ k : ℕ, p * q - 1 ≠ 2 ^ k) :
    ∃ n : ℕ, p * q - 1 ≤ n ∧ (n + 1) ^ 2 ∣ n.centralBinom := by
  have hpq1 : 1 ≤ p * q := by nlinarith only [hp3, hpq]
  have hne : 3 * p ≠ 2 * q := three_mul_prime_ne_two_mul_prime hp hq hp3
  rcases lt_or_gt_of_ne hne with hgt | hlt
  · refine ⟨p * q - 1, le_rfl, ?_⟩
    rw [Nat.sub_add_cancel hpq1]
    exact balakram_case_one hp hq hp3 hpq hgt hhi
  · have hle : p * q - 1 ≤ 4 * p * q - 1 := by
      have : p * q ≤ 4 * p * q := by nlinarith only [hpq1]
      omega
    refine ⟨4 * p * q - 1, hle, ?_⟩
    have hpq4 : 1 ≤ 4 * p * q := by nlinarith only [hpq1]
    rw [Nat.sub_add_cancel hpq4]
    exact balakram_case_four hp hq hp3 hpq hlo hlt hnot_pow

/-- **Main Unboundedness Lemma for Erdős Problem 727 ($k = 1$)**:
For every $N \in \mathbb{N}$, there exists $n \ge N$ such that $(n + 1)^2 \mid \binom{2n}{n}$. -/
theorem exists_ge_centralBinom_dvd (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (n + 1) ^ 2 ∣ n.centralBinom := by
  obtain ⟨p₀, hp₀_ge, hp₀_prime⟩ := Nat.exists_infinite_primes (max N 5)
  have hp₀N : N ≤ p₀ := le_trans (le_max_left N 5) hp₀_ge
  have hp₀5 : 5 ≤ p₀ := le_trans (le_max_right N 5) hp₀_ge
  obtain ⟨p₁, q₁, hp₁, hq₁, hp₀p₁, hp₁q₁, hlo₁, hhi₁⟩ :=
    exists_prime_pair_eleven_eighths hp₀_prime hp₀5
  have hp₁3 : 3 < p₁ := by omega
  have hq₁3 : 3 < q₁ := by omega
  have hp₁_le_pq : p₁ + 1 ≤ p₁ * q₁ := by nlinarith only [hp₁3, hp₁q₁]
  have hN_le_p₁q₁ : N ≤ p₁ * q₁ - 1 := by omega
  by_cases hpow : ∃ k : ℕ, p₁ * q₁ - 1 = 2 ^ k
  · obtain ⟨k, hk⟩ := hpow
    obtain ⟨t, ht2, rfl⟩ := even_of_prime_mul_sub_one_eq_two_pow hp₁ hq₁ hp₁3 hq₁3 hk
    have hne₁ : 3 * p₁ ≠ 2 * q₁ := three_mul_prime_ne_two_mul_prime hp₁ hq₁ hp₁3
    rcases lt_or_gt_of_ne hne₁ with hgt₁ | hlt₁
    · refine ⟨p₁ * q₁ - 1, hN_le_p₁q₁, ?_⟩
      rw [Nat.sub_add_cancel (by omega)]
      exact balakram_case_one hp₁ hq₁ hp₁3 hp₁q₁ hgt₁ hhi₁
    · obtain ⟨p₂, s, hp₂, hs, hq₁p₂, hp₂_le, hp₂s, hs2p₂, hs_gt⟩ :=
        exists_max_prime_in_interval_and_bertrand hq₁ (by omega)
      have hp₂3 : 3 < p₂ := by omega
      have hs3 : 3 < s := by omega
      have hpow_ge : 16 ≤ 2 ^ (2 * t) := by
        calc 16 = 2 ^ (2 * 2) := by norm_num
        _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp₁q₁_eq : p₁ * q₁ = 2 ^ (2 * t) + 1 := by omega
      have hs_ne : s ≠ 2 * q₁ := by
        rintro rfl
        rcases (Nat.dvd_prime hs).mp (dvd_mul_right 2 q₁) with h | h <;> omega
      rcases lt_or_gt_of_ne hs_ne with hs_lt | hs_gt_2q₁
      · -- Subcase 1: `s < 2 * q₁`. Pair `(q₁, s)` works!
        have hp₁_lt_s : p₁ < s := by omega
        have hlo_qs : 2 ^ (2 * t) < q₁ * s - 1 := by
          have h1 : p₁ * q₁ < q₁ * s := by nlinarith only [hp₁_lt_s, hq₁3]
          omega
        have hhi_qs : q₁ * s - 1 < 2 ^ (2 * t + 2) := by
          have h1 : q₁ * s < 2 * (q₁ * q₁) := by nlinarith only [hs_lt, hq₁3]
          have h2 : 2 * (q₁ * q₁) < 3 * (p₁ * q₁) := by nlinarith only [hlt₁, hq₁3]
          have h4 : 2 ^ (2 * t + 2) = 4 * 2 ^ (2 * t) := by ring
          omega
        obtain ⟨n, hn_ge, hn_dvd⟩ := exists_good_of_valid_pair hq₁ hs hq₁3
          (by omega) hs_gt hs_lt (not_pow_two_of_between_even_pow hq₁ hs hq₁3 hs3 hlo_qs hhi_qs)
        exact ⟨n, by omega, hn_dvd⟩
      · -- Now `2 * q₁ < s < 2 * p₂`, which forces `q₁ < p₂`.
        have hq₁_lt_p₂ : q₁ < p₂ := by omega
        have hp₂_ne : p₂ ≠ 2 * p₁ := by
          rintro rfl
          rcases (Nat.dvd_prime hp₂).mp (dvd_mul_right 2 p₁) with h | h <;> omega
        rcases lt_or_gt_of_ne hp₂_ne with hp₂_lt | hp₂_gt
        · -- Subcase 2: `q₁ < p₂ < 2 * p₁`. Pair `(p₁, p₂)` works!
          have hlo_pp₂ : 2 ^ (2 * t) < p₁ * p₂ - 1 := by
            have h1 : p₁ * q₁ < p₁ * p₂ := by nlinarith only [hq₁_lt_p₂, hp₁3]
            omega
          have hhi_pp₂ : p₁ * p₂ - 1 < 2 ^ (2 * t + 2) := by
            have h1 : p₁ * p₂ < 2 * (p₁ * p₁) := by nlinarith only [hp₂_lt, hp₁3]
            have h2 : p₁ * p₁ < p₁ * q₁ := by nlinarith only [hp₁q₁, hp₁3]
            have h4 : 2 ^ (2 * t + 2) = 4 * 2 ^ (2 * t) := by ring
            omega
          obtain ⟨n, hn_ge, hn_dvd⟩ := exists_good_of_valid_pair hp₁ hp₂ hp₁3
            (by omega) (by omega) hp₂_lt
            (not_pow_two_of_between_even_pow hp₁ hp₂ hp₁3 hp₂3 hlo_pp₂ hhi_pp₂)
          exact ⟨n, by omega, hn_dvd⟩
        · -- Subcase 3: `2 * p₁ < p₂` and `2 * q₁ < s`. Pair `(p₂, s)` works in `(2^(2t+2), 2^(2t+4))`!
          have hlo_p₂s : 2 ^ (2 * (t + 1)) < p₂ * s - 1 := by
            have h1 : 4 * (p₁ * q₁) < p₂ * s := by nlinarith only [hp₂_gt, hs_gt_2q₁]
            have h3 : 2 ^ (2 * (t + 1)) = 4 * 2 ^ (2 * t) := by ring
            omega
          have hhi_p₂s : p₂ * s - 1 < 2 ^ (2 * (t + 1) + 2) := by
            have h1 : p₂ < 2 * q₁ := by omega
            have h2 : s < 4 * q₁ := by omega
            have h3 : p₂ * s < 8 * (q₁ * q₁) := by nlinarith only [h1, h2, hq₁3]
            have h4 : 2 * (q₁ * q₁) < 3 * (p₁ * q₁) := by nlinarith only [hlt₁, hq₁3]
            have h6 : 2 ^ (2 * (t + 1) + 2) = 16 * 2 ^ (2 * t) := by ring
            omega
          obtain ⟨n, hn_ge, hn_dvd⟩ := exists_good_of_valid_pair hp₂ hs hp₂3
            hp₂s (by omega) hs2p₂
            (not_pow_two_of_between_even_pow hp₂ hs hp₂3 hs3 hlo_p₂s hhi_p₂s)
          have h_pq_lt : p₁ * q₁ < p₂ * s := by nlinarith only [hp₂_gt, hs_gt_2q₁, hp₁3, hq₁3]
          have hN_le : N ≤ p₂ * s - 1 := by omega
          exact ⟨n, le_trans hN_le hn_ge, hn_dvd⟩
  · push Not at hpow
    obtain ⟨n, hn_ge, hn_dvd⟩ :=
      exists_good_of_valid_pair hp₁ hq₁ hp₁3 hp₁q₁ hlo₁ hhi₁ hpow
    exact ⟨n, le_trans hN_le_p₁q₁ hn_ge, hn_dvd⟩

/-- **Erdős Problem 727 (`JSP-000595` / `erdos_727.variants.k_1`)**:
For $k = 1$, there are infinitely many $n \in \mathbb{N}$ such that $((n + k)!)^2 \mid (2n)!$. -/
theorem erdos_727.variants.k_1 :
    letI k := 1
    Set.Infinite {n : ℕ | (n + k)! ^ 2 ∣ (2 * n)!} := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  obtain ⟨n, han, hdvd⟩ := exists_ge_centralBinom_dvd (a + 1)
  refine ⟨n, ?_, by omega⟩
  change (n + 1)! ^ 2 ∣ (2 * n)!
  rwa [factorial_sq_dvd_two_mul_factorial_iff]

end Erdos727

/-!
## Part 2: Erdős Problem 273 (`JSP-000234`) — Selfridge's Covering System for $p \ge 3$

We reproduce the exact `CoveringSystem` and `StrictCoveringSystem` structures from
`FormalConjecturesForMathlib.NumberTheory.CoveringSystem` and construct Selfridge's 12-coset
strict covering system of $\mathbb{N}$ with moduli $p - 1$ for
$p \in \{3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181\}$.
-/

/-- A covering system of a commutative semiring `R` (matching
`FormalConjecturesForMathlib.NumberTheory.CoveringSystem`). -/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = @Set.univ R
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

/-- A strict covering system has distinct moduli (matching
`FormalConjecturesForMathlib.NumberTheory.CoveringSystem`). -/
structure StrictCoveringSystem (R : Type*) [CommSemiring R] extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace Erdos273

/-- The 12 primes $p \ge 3$ used in Selfridge's covering system of $\mathbb{N}$ (and $\mathbb{Z}$),
whose shifted values $p - 1$ divide $360$. -/
def selfridgePrimes : Fin 12 → ℕ
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 11
  | 4 => 13
  | 5 => 19
  | 6 => 31
  | 7 => 37
  | 8 => 41
  | 9 => 61
  | 10 => 73
  | 11 => 181

/-- The 12 moduli $m_i = p_i - 1 \in \{2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180\}$. -/
def selfridgeModuliNat (i : Fin 12) : ℕ := selfridgePrimes i - 1

/-- The 12 ideals $\langle p_i - 1 \rangle \subseteq \mathbb{N}$. -/
def selfridgeModuli (i : Fin 12) : Ideal ℕ := Ideal.span {↑(selfridgePrimes i - 1)}

/-- The 12 residues $r_i < m_i$ that cover all 360 residue classes modulo $360$. -/
def selfridgeResiduesNat : Fin 12 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 8
  | 5 => 12
  | 6 => 24
  | 7 => 24
  | 8 => 36
  | 9 => 12
  | 10 => 0
  | 11 => 0

lemma selfridgePrimes_prime (i : Fin 12) : (selfridgePrimes i).Prime := by
  fin_cases i <;> norm_num [selfridgePrimes]

lemma selfridgePrimes_ge_three (i : Fin 12) : 3 ≤ selfridgePrimes i := by
  fin_cases i <;> decide

lemma selfridgeModuliNat_ge_two (i : Fin 12) : 2 ≤ selfridgeModuliNat i := by
  fin_cases i <;> decide

lemma selfridgeModuliNat_injective : Function.Injective selfridgeModuliNat := by
  intro i j
  revert i j
  decide

lemma selfridgeModuliNat_dvd_360 (i : Fin 12) : selfridgeModuliNat i ∣ 360 := by
  fin_cases i <;> decide

/-- Explicit index selector for Selfridge's 12-modulus covering system. -/
def selfridgeIdx (n : ℕ) : Fin 12 :=
  if n % 2 = 1 then 0
  else if n % 4 = 2 then 1
  else if n % 6 = 4 then 2
  else if n % 10 = 8 then 3
  else if n % 12 = 8 then 4
  else if n % 18 = 12 then 5
  else if n % 30 = 24 then 6
  else if n % 36 = 24 then 7
  else if n % 40 = 36 then 8
  else if n % 60 = 12 then 9
  else if n % 72 = 0 then 10
  else 11

lemma selfridge_covers_grid (a : Fin 12) (b : Fin 15) :
    let m := 2 * (15 * a.1 + b.1)
    m % selfridgeModuliNat (selfridgeIdx m) =
      selfridgeResiduesNat (selfridgeIdx m) := by
  revert a b
  decide

lemma selfridge_covers_nat (n : ℕ) :
    ∃ i : Fin 12, n % selfridgeModuliNat i = selfridgeResiduesNat i := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · set q := (n % 360) / 2
    have hq_lt : q < 180 := by omega
    let a : Fin 12 := ⟨q / 15, by omega⟩
    let b : Fin 15 := ⟨q % 15, by omega⟩
    have h_ab : 2 * (15 * a.1 + b.1) = n % 360 := by
      dsimp [a, b, q]
      omega
    let i := selfridgeIdx (2 * (15 * a.1 + b.1))
    refine ⟨i, ?_⟩
    have hcov := selfridge_covers_grid a b
    dsimp only at hcov
    change (2 * (15 * a.1 + b.1)) % selfridgeModuliNat i = selfridgeResiduesNat i at hcov
    rw [h_ab, Nat.mod_mod_of_dvd n (selfridgeModuliNat_dvd_360 i)] at hcov
    exact hcov
  · exact ⟨0, h1⟩

lemma selfridgeModuli_injective : Function.Injective selfridgeModuli := by
  intro i j hij
  have h1 : selfridgeModuliNat i ∈ selfridgeModuli j := by
    rw [← hij]
    exact Ideal.subset_span (Set.mem_singleton _)
  have h2 : selfridgeModuliNat j ∈ selfridgeModuli i := by
    rw [hij]
    exact Ideal.subset_span (Set.mem_singleton _)
  unfold selfridgeModuli at h1 h2
  rw [Ideal.mem_span_singleton] at h1 h2
  exact selfridgeModuliNat_injective (Nat.dvd_antisymm h2 h1)

/-- Selfridge's strict covering system of $\mathbb{N}$ with moduli $p - 1$ ($p \ge 3$ prime). -/
def selfridgeStrictCoveringNat : StrictCoveringSystem ℕ where
  ι := Fin 12
  fintypeIndex := inferInstance
  residue := selfridgeResiduesNat
  moduli := selfridgeModuli
  unionCovers := by
    ext n
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := selfridge_covers_nat n
    refine ⟨i, Set.mem_add.mpr ⟨selfridgeResiduesNat i, rfl,
      selfridgeModuliNat i * (n / selfridgeModuliNat i), ?_, ?_⟩⟩
    · change selfridgeModuliNat i * (n / selfridgeModuliNat i) ∈ Ideal.span {selfridgeModuliNat i}
      rw [Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    · have hdiv := Nat.div_add_mod n (selfridgeModuliNat i)
      omega
  ne_bot := by
    intro i hbot
    have hmem : selfridgeModuliNat i ∈ selfridgeModuli i :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [hbot, Submodule.mem_bot] at hmem
    have := selfridgeModuliNat_ge_two i
    omega
  ne_top := by
    intro i htop
    have hmem : (1 : ℕ) ∈ (⊤ : Ideal ℕ) := trivial
    rw [← htop] at hmem
    change (1 : ℕ) ∈ Ideal.span {selfridgeModuliNat i} at hmem
    rw [Ideal.mem_span_singleton] at hmem
    have hle : selfridgeModuliNat i ≤ 1 := Nat.le_of_dvd (by decide) hmem
    have := selfridgeModuliNat_ge_two i
    omega
  injective_moduli := selfridgeModuli_injective

/-- **Erdős Problem 273 (`JSP-000234` / `erdos_273.variants.three`)**:
There exists a strict covering system of $\mathbb{N}$ all of whose moduli are of the form $p - 1$
for some primes $p \ge 3$. -/
theorem erdos_273.variants.three : ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧
    c.moduli i = Ideal.span {↑(p - 1)} :=
  ⟨selfridgeStrictCoveringNat, fun i =>
    ⟨selfridgePrimes i, selfridgePrimes_prime i, selfridgePrimes_ge_three i, rfl⟩⟩

/-- The 12 ideals $\langle p_i - 1 \rangle \subseteq \mathbb{Z}$. -/
def selfridgeModuliInt (i : Fin 12) : Ideal ℤ := Ideal.span {↑(selfridgePrimes i - 1)}

lemma selfridgeModuliInt_injective : Function.Injective selfridgeModuliInt := by
  intro i j hij
  have h1 : (selfridgeModuliNat i : ℤ) ∈ selfridgeModuliInt j := by
    rw [← hij]
    exact Ideal.subset_span (Set.mem_singleton _)
  have h2 : (selfridgeModuliNat j : ℤ) ∈ selfridgeModuliInt i := by
    rw [hij]
    exact Ideal.subset_span (Set.mem_singleton _)
  unfold selfridgeModuliInt at h1 h2
  rw [Ideal.mem_span_singleton] at h1 h2
  have hd1 : selfridgeModuliNat j ∣ selfridgeModuliNat i := Int.ofNat_dvd.mp h1
  have hd2 : selfridgeModuliNat i ∣ selfridgeModuliNat j := Int.ofNat_dvd.mp h2
  exact selfridgeModuliNat_injective (Nat.dvd_antisymm hd2 hd1)

/-- Selfridge's strict covering system of $\mathbb{Z}$ with moduli $p - 1$ ($p \ge 3$ prime). -/
def selfridgeStrictCoveringInt : StrictCoveringSystem ℤ where
  ι := Fin 12
  fintypeIndex := inferInstance
  residue := fun i => (selfridgeResiduesNat i : ℤ)
  moduli := selfridgeModuliInt
  unionCovers := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    set n : ℕ := (z % 360).toNat
    have hz_mod_nonneg : 0 ≤ z % 360 := Int.emod_nonneg z (by decide)
    have hn_eq : (n : ℤ) = z % 360 := Int.toNat_of_nonneg hz_mod_nonneg
    obtain ⟨i, hi⟩ := selfridge_covers_nat n
    refine ⟨i, Set.mem_add.mpr ⟨(selfridgeResiduesNat i : ℤ), rfl,
      z - (selfridgeResiduesNat i : ℤ), ?_, by ring⟩⟩
    change z - (selfridgeResiduesNat i : ℤ) ∈ Ideal.span {(selfridgeModuliNat i : ℤ)}
    rw [Ideal.mem_span_singleton]
    obtain ⟨k, hk⟩ := selfridgeModuliNat_dvd_360 i
    set q_n : ℕ := n / selfridgeModuliNat i
    set q_z : ℤ := z / 360
    have hdiv_n : selfridgeModuliNat i * q_n + selfridgeResiduesNat i = n := by
      dsimp [q_n]
      rw [← hi]
      exact Nat.div_add_mod n (selfridgeModuliNat i)
    have hz_div : 360 * q_z + z % 360 = z := by dsimp [q_z]; omega
    refine ⟨(q_n : ℤ) + (k : ℤ) * q_z, ?_⟩
    have hn_cast : (n : ℤ) = (selfridgeModuliNat i : ℤ) * (q_n : ℤ) +
        (selfridgeResiduesNat i : ℤ) := by exact_mod_cast hdiv_n.symm
    have hk_cast : (360 : ℤ) = (selfridgeModuliNat i : ℤ) * (k : ℤ) := by exact_mod_cast hk
    calc z - (selfridgeResiduesNat i : ℤ)
        = (360 : ℤ) * q_z + (n : ℤ) - (selfridgeResiduesNat i : ℤ) := by linarith
      _ = ((selfridgeModuliNat i : ℤ) * (k : ℤ)) * q_z +
          ((selfridgeModuliNat i : ℤ) * (q_n : ℤ) +
            (selfridgeResiduesNat i : ℤ)) - (selfridgeResiduesNat i : ℤ) := by
            rw [hk_cast, hn_cast]
      _ = (selfridgeModuliNat i : ℤ) * ((q_n : ℤ) + (k : ℤ) * q_z) := by ring
  ne_bot := by
    intro i hbot
    have hmem : (selfridgeModuliNat i : ℤ) ∈ selfridgeModuliInt i :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [hbot, Submodule.mem_bot] at hmem
    have hge := selfridgeModuliNat_ge_two i
    omega
  ne_top := by
    intro i htop
    have hmem : (1 : ℤ) ∈ (⊤ : Ideal ℤ) := trivial
    rw [← htop] at hmem
    change (1 : ℤ) ∈ Ideal.span {(selfridgeModuliNat i : ℤ)} at hmem
    rw [Ideal.mem_span_singleton] at hmem
    have hdvd : selfridgeModuliNat i ∣ 1 := Int.ofNat_dvd.mp hmem
    have hle : selfridgeModuliNat i ≤ 1 := Nat.le_of_dvd (by decide) hdvd
    have hge := selfridgeModuliNat_ge_two i
    omega
  injective_moduli := selfridgeModuliInt_injective

/-- **Integer Ring Version of `erdos_273.variants.three`**:
There exists a strict covering system of $\mathbb{Z}$ all of whose moduli are of the form $p - 1$
for some primes $p \ge 3$. -/
theorem erdos_273.variants.three_int : ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ (p : ℕ), p.Prime ∧ 3 ≤ p ∧
    c.moduli i = Ideal.span {↑(p - 1)} :=
  ⟨selfridgeStrictCoveringInt, fun i =>
    ⟨selfridgePrimes i, selfridgePrimes_prime i, selfridgePrimes_ge_three i, rfl⟩⟩

end Erdos273

#print axioms Erdos727.balakram_case_one
#print axioms Erdos727.balakram_case_four
#print axioms Erdos727.exists_ge_centralBinom_dvd
#print axioms Erdos727.erdos_727.variants.k_1
#print axioms Erdos273.erdos_273.variants.three
#print axioms Erdos273.erdos_273.variants.three_int
