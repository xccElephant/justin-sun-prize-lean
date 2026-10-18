/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem 372 (`JSP-000307`): Decreasing Largest Prime Factors of Consecutive Integers

*References:*
- [erdosproblems.com/372](https://www.erdosproblems.com/372) (`FormalConjectures/ErdosProblems/372.lean`, `JSP-000307`)
- [ErPo78] Erdős, P. and Pomerance, C., *On the largest prime factors of $n$ and $n+1$*.
  Aequationes Math. 17 (1978), 311–321.
- [Ba01] Balog, A., *On triplets with descending largest prime factors*.
  Studia Sci. Math. Hungar. 38 (2001), 45–50.

This file formalizes:
1. **The exact `Nat.maxPrimeFac` function and its complete algebraic API** from
   `FormalConjecturesForMathlib/Data/Nat/MaxPrimeFac.lean` (`maxPrimeFac_dvd`, `le_maxPrimeFac`,
   `maxPrimeFac_mul`, `maxPrimeFac_pow`).
2. **Resolution of the `JSP-000307` Existence & Minimality Question (`jsp_000307_least_decreasing_triple`)**:
   Proves that $n = 13$ ($P^+(13) = 13 > P^+(14) = 7 > P^+(15) = 5$) is the **least** natural
   number satisfying $P^+(n) > P^+(n+1) > P^+(n+2)$, and exhibits a four-term strictly decreasing
   chain at $n = 317$ ($P^+(317) = 317 > P^+(318) = 53 > P^+(319) = 29 > P^+(320) = 5$).
3. **Unconditional Infinite Families for Consecutive Largest Prime Factor Comparisons**:
   - `infinite_maxPrimeFac_gt_succ`: $\{n : \mathbb{N} \mid P^+(n) > P^+(n+1)\}$ is infinite
     (via $n = 2^k - 1$ for $k \ge 2$, where $P^+(2^k - 1) \ge 3 > 2 = P^+(2^k)$).
   - `infinite_maxPrimeFac_lt_succ`: $\{n : \mathbb{N} \mid P^+(n) < P^+(n+1)\}$ is infinite
     (via $n = 2^k$ for $k \ge 1$, where $P^+(2^k) = 2 < 3 \le P^+(2^k + 1)$).
   - `infinite_maxPrimeFac_valley`: $\{n : \mathbb{N} \mid P^+(n) > P^+(n+1) \wedge P^+(n+1) < P^+(n+2)\}$
     is infinite.
-/

namespace Nat

/-- The greatest prime divisor of a natural number `n > 1` (takes `0` for `n = 0` and `1` for `n = 1`),
matching `FormalConjecturesForMathlib/Data/Nat/MaxPrimeFac.lean`. -/
def maxPrimeFac (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactorsList.getLastI

@[simp]
lemma maxPrimeFac_zero : maxPrimeFac 0 = 0 := by
  simp [maxPrimeFac, List.getLastI]

@[simp]
lemma maxPrimeFac_one : maxPrimeFac 1 = 1 := rfl

lemma prime_maxPrimeFac_of_one_lt (n : ℕ) (h : 1 < n) :
    Prime (maxPrimeFac n) := by
  have hn : n.primeFactorsList ≠ [] := (primeFactorsList_ne_nil n).2 h
  have hmem : n.primeFactorsList.getLast hn ∈ n.primeFactorsList := List.getLast_mem hn
  have hprime : Prime (n.primeFactorsList.getLast hn) := prime_of_mem_primeFactorsList hmem
  simpa [maxPrimeFac, h.ne', List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hn] using hprime

/-- The greatest prime factor of a natural number divides it. -/
lemma maxPrimeFac_dvd : ∀ {n : ℕ}, maxPrimeFac n ∣ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have hn : 1 < n + 2 := by omega
    have hlist : (n + 2).primeFactorsList ≠ [] :=
      (primeFactorsList_ne_nil (n + 2)).2 hn
    have hmem : (n + 2).primeFactorsList.getLast hlist ∈ (n + 2).primeFactorsList :=
      List.getLast_mem hlist
    have hdvd : (n + 2).primeFactorsList.getLast hlist ∣ n + 2 :=
      dvd_of_mem_primeFactorsList hmem
    simpa [maxPrimeFac, hn.ne', List.getLastI_eq_getLast?_getD,
      List.getLast?_eq_getLast_of_ne_nil hlist] using hdvd

/-- Every prime factor of a nonzero natural number is at most its greatest prime factor. -/
lemma le_maxPrimeFac {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n := by
  have hmem : p ∈ n.primeFactorsList := (mem_primeFactorsList hn).2 ⟨hp, h_dvd⟩
  have hlist : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hmem
  have hn_one : n ≠ 1 := ((primeFactorsList_ne_nil n).1 hlist).ne'
  have hp_last : p ≤ n.primeFactorsList.getLast hlist :=
    (primeFactorsList_sorted n).pairwise.rel_getLast hmem
  simpa [maxPrimeFac, hn_one, List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hlist] using hp_last

lemma maxPrimeFac_eq_of_dvd_of_le (n p : ℕ) (hn : 0 < n) (hp : p.Prime)
    (h_dvd : p ∣ n) (h_le : maxPrimeFac n ≤ p) :
    maxPrimeFac n = p :=
  le_antisymm h_le (le_maxPrimeFac hn.ne' hp h_dvd)

@[simp]
lemma Prime.maxPrimeFac_eq_self {p : ℕ} (hp : p.Prime) :
    maxPrimeFac p = p := by
  apply maxPrimeFac_eq_of_dvd_of_le p p hp.pos hp (dvd_refl p)
  exact Nat.le_of_dvd hp.pos maxPrimeFac_dvd

lemma maxPrimeFac_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    maxPrimeFac (m * n) = max (maxPrimeFac m) (maxPrimeFac n) := by
  obtain rfl | hm_lt : m = 1 ∨ 1 < m := by omega
  · have hle : 1 ≤ maxPrimeFac n := by
      obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
      · simp
      · exact (prime_maxPrimeFac_of_one_lt n hn_lt).one_lt.le
    simp [hle]
  obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
  · have hle : 1 ≤ maxPrimeFac m := (prime_maxPrimeFac_of_one_lt m hm_lt).one_lt.le
    simp [hle]
  have hmn_lt : 1 < m * n := Nat.one_lt_mul_iff.mpr
    ⟨zero_lt_of_lt hm_lt, zero_lt_of_lt hn_lt, Or.inl hm_lt⟩
  apply le_antisymm
  · have hp : Prime (maxPrimeFac (m * n)) := prime_maxPrimeFac_of_one_lt (m * n) hmn_lt
    rcases hp.dvd_mul.mp maxPrimeFac_dvd with hpm | hpn
    · exact (le_maxPrimeFac hm hp hpm).trans (le_max_left _ _)
    · exact (le_maxPrimeFac hn hp hpn).trans (le_max_right _ _)
  · apply max_le
    · have hp : Prime (maxPrimeFac m) := prime_maxPrimeFac_of_one_lt m hm_lt
      apply le_maxPrimeFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_left maxPrimeFac_dvd n
    · have hp : Prime (maxPrimeFac n) := prime_maxPrimeFac_of_one_lt n hn_lt
      apply le_maxPrimeFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_right maxPrimeFac_dvd m

@[simp]
lemma maxPrimeFac_pow {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    maxPrimeFac (n ^ k) = maxPrimeFac n :=
  match k, hk with
  | k + 1, _ => by
    by_cases hn : n = 0
    · subst n; simp
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, maxPrimeFac_mul (pow_ne_zero _ hn) hn, ih (by omega)]
      simp

end Nat

namespace Erdos372

/-- **JSP-000307 (Existence and Minimality)**:
$n = 13$ ($P^+(13) = 13 > P^+(14) = 7 > P^+(15) = 5$) is the least natural number $n$
whose three consecutive terms $n, n+1, n+2$ have strictly decreasing largest prime factors. -/
theorem jsp_000307_least_decreasing_triple :
    IsLeast {n : ℕ | Nat.maxPrimeFac n > Nat.maxPrimeFac (n + 1) ∧
      Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac (n + 2)} 13 := by
  refine ⟨by decide +kernel, fun n hn => ?_⟩
  by_contra! hlt
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hn <;> decide +kernel

/-- Four consecutive integers $317, 318, 319, 320$ have strictly decreasing largest prime factors:
$P^+(317) = 317 > P^+(318) = 53 > P^+(319) = 29 > P^+(320) = 5$. -/
theorem decreasing_quadruple_317 :
    Nat.maxPrimeFac 317 = 317 ∧ Nat.maxPrimeFac 318 = 53 ∧
    Nat.maxPrimeFac 319 = 29 ∧ Nat.maxPrimeFac 320 = 5 ∧
    Nat.maxPrimeFac 317 > Nat.maxPrimeFac 318 ∧
    Nat.maxPrimeFac 318 > Nat.maxPrimeFac 319 ∧
    Nat.maxPrimeFac 319 > Nat.maxPrimeFac 320 := by
  decide +kernel

/-- Every odd integer $m > 1$ has `3 ≤ Nat.maxPrimeFac m`. -/
lemma three_le_maxPrimeFac_of_odd {m : ℕ} (hm1 : 1 < m) (hodd : m % 2 = 1) :
    3 ≤ Nat.maxPrimeFac m := by
  have hp : Nat.Prime (Nat.maxPrimeFac m) := Nat.prime_maxPrimeFac_of_one_lt m hm1
  have hdvd : Nat.maxPrimeFac m ∣ m := Nat.maxPrimeFac_dvd
  have hne2 : Nat.maxPrimeFac m ≠ 2 := by
    intro h2
    rw [h2] at hdvd
    omega
  have hp2 : 2 ≤ Nat.maxPrimeFac m := hp.two_le
  omega

/-- For every $k \ge 2$, $n = 2^k - 1$ satisfies
$\mathrm{maxPrimeFac}(2^k - 1) \ge 3 > 2 = \mathrm{maxPrimeFac}(2^k)$ and
$\mathrm{maxPrimeFac}(2^k) = 2 < 3 \le \mathrm{maxPrimeFac}(2^k + 1)$. -/
theorem two_pow_sub_one_valley {k : ℕ} (hk : 2 ≤ k) :
    Nat.maxPrimeFac (2 ^ k - 1) > Nat.maxPrimeFac (2 ^ k) ∧
    Nat.maxPrimeFac (2 ^ k) < Nat.maxPrimeFac (2 ^ k + 1) := by
  have hpow_ge4 : 4 ≤ 2 ^ k := by
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have h2k_max : Nat.maxPrimeFac (2 ^ k) = 2 := by
    rw [Nat.maxPrimeFac_pow (by omega), Nat.Prime.maxPrimeFac_eq_self Nat.prime_two]
  have h2_dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hodd_sub : (2 ^ k - 1) % 2 = 1 := by omega
  have hodd_add : (2 ^ k + 1) % 2 = 1 := by omega
  have hsub_ge3 : 3 ≤ Nat.maxPrimeFac (2 ^ k - 1) :=
    three_le_maxPrimeFac_of_odd (by omega) hodd_sub
  have hadd_ge3 : 3 ≤ Nat.maxPrimeFac (2 ^ k + 1) :=
    three_le_maxPrimeFac_of_odd (by omega) hodd_add
  omega

/-- **Unconditional Infinitude of Valley Triples (`infinite_maxPrimeFac_valley`)**:
There are infinitely many $n \in \mathbb{N}$ such that $P^+(n) > P^+(n+1)$ and $P^+(n+1) < P^+(n+2)$. -/
theorem infinite_maxPrimeFac_valley :
    {n : ℕ | Nat.maxPrimeFac n > Nat.maxPrimeFac (n + 1) ∧
      Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac (n + 2)}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 2) - 1) ?_ ?_
  · intro a b hab
    dsimp at hab
    have ha : 1 ≤ 2 ^ (a + 2) := Nat.one_le_pow (a + 2) 2 (by omega)
    have hb : 1 ≤ 2 ^ (b + 2) := Nat.one_le_pow (b + 2) 2 (by omega)
    have heq : 2 ^ (a + 2) = 2 ^ (b + 2) := by omega
    have := Nat.pow_right_injective (by omega : 2 ≤ 2) heq
    omega
  · intro k
    have hpos : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow (k + 2) 2 (by omega)
    have h1 : 2 ^ (k + 2) - 1 + 1 = 2 ^ (k + 2) := Nat.sub_add_cancel hpos
    have h2 : 2 ^ (k + 2) - 1 + 2 = 2 ^ (k + 2) + 1 := by omega
    change Nat.maxPrimeFac (2 ^ (k + 2) - 1) > Nat.maxPrimeFac (2 ^ (k + 2) - 1 + 1) ∧
      Nat.maxPrimeFac (2 ^ (k + 2) - 1 + 1) < Nat.maxPrimeFac (2 ^ (k + 2) - 1 + 2)
    rw [h1, h2]
    exact two_pow_sub_one_valley (by omega)

/-- In particular, $\{n : \mathbb{N} \mid P^+(n) > P^+(n+1)\}$ is infinite. -/
theorem infinite_maxPrimeFac_gt_succ :
    {n : ℕ | Nat.maxPrimeFac n > Nat.maxPrimeFac (n + 1)}.Infinite :=
  infinite_maxPrimeFac_valley.mono (fun _ hn => hn.1)

/-- And $\{n : \mathbb{N} \mid P^+(n) < P^+(n+1)\}$ is infinite. -/
theorem infinite_maxPrimeFac_lt_succ :
    {n : ℕ | Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 2)) ?_ ?_
  · intro a b hab
    have := Nat.pow_right_injective (by omega : 2 ≤ 2) hab
    omega
  · intro k
    exact (two_pow_sub_one_valley (by omega)).2

end Erdos372

#print axioms Erdos372.jsp_000307_least_decreasing_triple
#print axioms Erdos372.decreasing_quadruple_317
#print axioms Erdos372.infinite_maxPrimeFac_valley
#print axioms Erdos372.infinite_maxPrimeFac_gt_succ
#print axioms Erdos372.infinite_maxPrimeFac_lt_succ
