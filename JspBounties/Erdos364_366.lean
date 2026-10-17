import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos364_366

/-- A natural number $n$ is $k$-full if $p^k \mid n$ for every prime factor $p$ of $n$
(matching `FormalConjecturesForMathlib.Data.Nat.Full`). -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- A natural number $n$ is powerful ($2$-full) if $p^2 \mid n$ for every prime factor $p$ of $n$. -/
abbrev Powerful : ℕ → Prop := Full 2

lemma full_of_le_full {k m n : ℕ} (hk : k ≤ m) (h : Full m n) : Full k n :=
  fun p hp => dvd_trans (Nat.pow_dvd_pow p hk) (h p hp)

/-- If $p$ is prime, $p \mid n$, and $p^{k+1} \nmid n$, then $n$ is not $(k+1)$-full. -/
lemma not_full_of_dvd_of_not_pow_dvd {n k p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ n) (hndvd : ¬ p ^ (k + 1) ∣ n) : ¬ Full (k + 1) n := by
  intro hfull
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hndvd (dvd_zero _)
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn0⟩
  exact hndvd (hfull p hmem)

/-- If $n \equiv p \pmod{p^{k+1}}$ for a prime $p$, then $n$ is not $(k+1)$-full. -/
lemma not_full_of_prime_mod_prime_sq (n k : ℕ) {p : ℕ} (hp : p.Prime)
    (h : n % p ^ (k + 1) = p) : ¬ Full (k + 1) n := by
  have hp_dvd_pow : p ∣ p ^ (k + 1) := dvd_pow_self p (by omega)
  have hdvd : p ∣ n := by
    rw [← Nat.div_add_mod n (p ^ (k + 1)), h]
    exact dvd_add (dvd_mul_of_dvd_left hp_dvd_pow _) dvd_rfl
  have hndvd : ¬ p ^ (k + 1) ∣ n := by
    intro hpow
    have hzero : n % p ^ (k + 1) = 0 := Nat.mod_eq_zero_of_dvd hpow
    have hp_gt : 1 < p := hp.one_lt
    omega
  exact not_full_of_dvd_of_not_pow_dvd hp hdvd hndvd

/-!
## Part 1: Erdős Problem 364 (`JSP-000300`) — Consecutive Powerful Numbers
-/

/-- **No Four Consecutive Powerful Numbers** (`erdos_364.variants.weak`):
Among any four consecutive integers $n, n+1, n+2, n+3$, at least one is $\equiv 2 \pmod 4$
and therefore not powerful. -/
theorem erdos_364_weak :
    ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) ∧ Powerful (n + 3) := by
  rintro ⟨n, h0, h1, h2, h3⟩
  have hmod : n % 4 = 2 ∨ (n + 1) % 4 = 2 ∨ (n + 2) % 4 = 2 ∨ (n + 3) % 4 = 2 := by omega
  rcases hmod with hm | hm | hm | hm
  · exact not_full_of_prime_mod_prime_sq n 1 Nat.prime_two hm h0
  · exact not_full_of_prime_mod_prime_sq (n + 1) 1 Nat.prime_two hm h1
  · exact not_full_of_prime_mod_prime_sq (n + 2) 1 Nat.prime_two hm h2
  · exact not_full_of_prime_mod_prime_sq (n + 3) 1 Nat.prime_two hm h3

/-- More generally, for every $k \ge 2$, there is no quadruple of consecutive $k$-full integers. -/
theorem no_four_consecutive_full {k : ℕ} (hk : 2 ≤ k) :
    ¬ ∃ (n : ℕ), Full k n ∧ Full k (n + 1) ∧ Full k (n + 2) ∧ Full k (n + 3) := by
  rintro ⟨n, h0, h1, h2, h3⟩
  exact erdos_364_weak ⟨n,
    full_of_le_full hk h0, full_of_le_full hk h1,
    full_of_le_full hk h2, full_of_le_full hk h3⟩

lemma not_powerful_of_mod_four_eq_two {m : ℕ} (h : m % 4 = 2) : ¬ Powerful m :=
  not_full_of_prime_mod_prime_sq m 1 Nat.prime_two h

lemma not_powerful_of_mod_nine_eq_three {m : ℕ} (h : m % 9 = 3) : ¬ Powerful m :=
  not_full_of_prime_mod_prime_sq m 1 Nat.prime_three h

lemma not_powerful_of_mod_nine_eq_six {m : ℕ} (h : m % 9 = 6) : ¬ Powerful m := by
  apply not_full_of_dvd_of_not_pow_dvd Nat.prime_three
  · rw [← Nat.div_add_mod m 9, h]
    exact ⟨3 * (m / 9) + 2, by ring⟩
  · intro hdvd
    have hzero : m % 9 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega

/-- **Modulo $36$ Sieve for Erdős Problem 364**:
Any triple of consecutive powerful numbers $(n, n+1, n+2)$ must satisfy $n \equiv 3 \pmod 4$
and $n \equiv 0, 7, 8 \pmod 9$, leaving only $3$ out of $36$ residue classes:
$n \equiv 7, 27, \text{ or } 35 \pmod{36}$. -/
theorem erdos_364_mod_thirtysix_barrier {n : ℕ}
    (h0 : Powerful n) (h1 : Powerful (n + 1)) (h2 : Powerful (n + 2)) :
    n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 := by
  have h4_0 : n % 4 ≠ 2 := fun h => not_powerful_of_mod_four_eq_two h h0
  have h4_1 : (n + 1) % 4 ≠ 2 := fun h => not_powerful_of_mod_four_eq_two h h1
  have h4_2 : (n + 2) % 4 ≠ 2 := fun h => not_powerful_of_mod_four_eq_two h h2
  have h9_0a : n % 9 ≠ 3 := fun h => not_powerful_of_mod_nine_eq_three h h0
  have h9_0b : n % 9 ≠ 6 := fun h => not_powerful_of_mod_nine_eq_six h h0
  have h9_1a : (n + 1) % 9 ≠ 3 := fun h => not_powerful_of_mod_nine_eq_three h h1
  have h9_1b : (n + 1) % 9 ≠ 6 := fun h => not_powerful_of_mod_nine_eq_six h h1
  have h9_2a : (n + 2) % 9 ≠ 3 := fun h => not_powerful_of_mod_nine_eq_three h h2
  have h9_2b : (n + 2) % 9 ≠ 6 := fun h => not_powerful_of_mod_nine_eq_six h h2
  omega

/-!
## Part 2: Erdős Problem 365 (`JSP-000301`) & Erdős Problem 366 (`JSP-000302`)

1. `exists_three_full_then_two_full`: $(8, 9)$ is a consecutive pair with $8$ $3$-full and $9$ $2$-full.
2. `golomb_pair`: Golomb's pair $(12167, 12168) = (23^3, 2^3 \cdot 3^2 \cdot 13^2)$ has $12167$ $3$-full
   (hence powerful), $12168$ $2$-full (powerful), and neither is a perfect square.
3. This simultaneously resolves:
   - `erdos_365.parts.i` (`JSP-000301`): Not every consecutive powerful pair contains a square.
   - `erdos_366.variants.three_two`: $(8, 9)$ is not the unique $(3\text{-full}, 2\text{-full})$ pair.
   - The `(3-full, 2-full)` reading of the ambiguous statement `JSP-000302`.
-/

lemma full_three_eight : Full 3 8 := by
  intro p hp
  obtain ⟨hp_prime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpow : p ∣ (2 : ℕ) ^ 3 := by norm_num at hdvd ⊢; exact hdvd
  have heq : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp_prime Nat.prime_two hpow
  subst p
  norm_num

lemma full_two_nine : Full 2 9 := by
  intro p hp
  obtain ⟨hp_prime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpow : p ∣ (3 : ℕ) ^ 2 := by norm_num at hdvd ⊢; exact hdvd
  have heq : p = 3 := Nat.prime_eq_prime_of_dvd_pow hp_prime Nat.prime_three hpow
  subst p
  norm_num

/-- **Existence of $(3\text{-full}, 2\text{-full})$ Consecutive Pair** (`exists_three_full_then_two_full`):
$n = 8 = 2^3$ is $3$-full and $n + 1 = 9 = 3^2$ is $2$-full. -/
theorem exists_three_full_then_two_full : ∃ n > 0, Full 3 n ∧ Full 2 (n + 1) :=
  ⟨8, by decide, full_three_eight, full_two_nine⟩

lemma full_three_12167 : Full 3 12167 := by
  intro p hp
  obtain ⟨hp_prime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpow : p ∣ (23 : ℕ) ^ 3 := by norm_num at hdvd ⊢; exact hdvd
  have heq : p = 23 := Nat.prime_eq_prime_of_dvd_pow hp_prime (by decide) hpow
  subst p
  norm_num

lemma full_two_12168 : Full 2 12168 := by
  intro p hp
  obtain ⟨hp_prime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hprod : p ∣ (2 : ℕ) ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num at hdvd ⊢; exact hdvd
  rcases hp_prime.dvd_mul.mp hprod with hab | hc
  · rcases hp_prime.dvd_mul.mp hab with ha | hb
    · have heq : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp_prime Nat.prime_two ha
      subst p; norm_num
    · have heq : p = 3 := Nat.prime_eq_prime_of_dvd_pow hp_prime Nat.prime_three hb
      subst p; norm_num
  · have heq : p = 13 := Nat.prime_eq_prime_of_dvd_pow hp_prime (by decide) hc
    subst p; norm_num

/-- **Golomb's Theorem (1970)** (`erdos_366.variants.three_two`):
$(8, 9)$ is not the only consecutive pair $(n, n+1)$ with $n$ $3$-full and $n+1$ $2$-full;
$n = 12167 = 23^3$ and $n + 1 = 12168 = 2^3 \cdot 3^2 \cdot 13^2$ is another. -/
theorem erdos_366_variants_three_two :
    ¬ ∀ n > 0, Full 3 n ∧ Full 2 (n + 1) → n = 8 := by
  intro h
  have h12167 := h 12167 (by decide) ⟨full_three_12167, full_two_12168⟩
  omega

/-- **Golomb's Non-Square Powerful Pair** (`golomb_pair` / `erdos_365.parts.i` / `JSP-000301`):
$12167$ is $3$-full (hence powerful), $12168$ is powerful, and neither is a perfect square. -/
theorem golomb_pair :
    Powerful 12167 ∧ Powerful 12168 ∧ ¬ IsSquare (12167 : ℕ) ∧ ¬ IsSquare (12168 : ℕ) := by
  have hns : ∀ n : ℕ, 12100 < n → n < 12321 → ¬ IsSquare n := by
    intro n hlo hhi ⟨r, hr⟩
    have hrlo : 110 < r := by nlinarith
    have hrhi : r < 111 := by nlinarith
    omega
  exact ⟨full_of_le_full (by decide : 2 ≤ 3) full_three_12167,
    full_two_12168,
    hns 12167 (by decide) (by decide),
    hns 12168 (by decide) (by decide)⟩

/-- Disproof of `JSP-000301` (`erdos_365.parts.i`):
Not every pair of consecutive positive powerful numbers contains a perfect square. -/
theorem erdos_365_parts_i :
    ¬ ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  obtain ⟨hA, hB, hnA, hnB⟩ := golomb_pair
  rcases h 12167 (by decide) hA hB with hs | hs
  · exact hnA hs
  · exact hnB hs

/-- **Modulo $8$ Barrier for Erdős Problem 366**:
If $n$ is $2$-full and $n+1$ is $3$-full, then $n \equiv 0, 4, \text{ or } 7 \pmod 8$. -/
theorem erdos_366_mod_eight_barrier {n : ℕ} (hn : Full 2 n) (hn1 : Full 3 (n + 1)) :
    n % 8 = 0 ∨ n % 8 = 4 ∨ n % 8 = 7 := by
  have h_not_2 : n % 4 ≠ 2 := fun h => not_powerful_of_mod_four_eq_two h hn
  have h_not_even1 : ¬ (n % 2 = 1 ∧ (n + 1) % 8 ≠ 0) := by
    rintro ⟨hodd, hmod8⟩
    have hdvd2 : 2 ∣ n + 1 := by omega
    have hndvd8 : ¬ (2 ^ 3 ∣ n + 1) := by
      intro hdvd8
      have := Nat.mod_eq_zero_of_dvd hdvd8
      omega
    exact not_full_of_dvd_of_not_pow_dvd Nat.prime_two hdvd2 hndvd8 hn1
  omega

#print axioms erdos_364_weak
#print axioms no_four_consecutive_full
#print axioms erdos_364_mod_thirtysix_barrier
#print axioms exists_three_full_then_two_full
#print axioms erdos_366_variants_three_two
#print axioms golomb_pair
#print axioms erdos_365_parts_i
#print axioms erdos_366_mod_eight_barrier

end Erdos364_366
