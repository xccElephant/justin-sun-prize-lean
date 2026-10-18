/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Asymptotics Filter Finset Nat Set

/-!
# Part 1: Erdős Problem 291 — Divisibility of Harmonic Numerators and Lcm Denominators
-/

namespace Erdos291

/-- $L_n$ is the least common multiple of $\{1, \ldots, n\}$. -/
def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm (fun x ↦ x)

theorem L_eval : L 1 = 1 ∧ L 2 = 2 ∧ L 3 = 6 ∧ L 4 = 12 := by decide

/-- $a_n$ is defined by $\sum_{1 \le k \le n} \frac{1}{k} = \frac{a_n}{L_n}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

theorem a_eval : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 25 := by decide

lemma dvd_L_of_mem {n j : ℕ} (hj : j ∈ Finset.Icc 1 n) : j ∣ L n :=
  Finset.dvd_lcm hj

lemma three_dvd_L_two_mul_pow_three {k : ℕ} (hk : 1 ≤ k) : 3 ∣ L (2 * 3 ^ k) := by
  apply dvd_L_of_mem
  rw [Finset.mem_Icc]
  have hpow : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk
  omega

lemma pow_three_dvd_L_two_mul_pow_three (k : ℕ) : 3 ^ k ∣ L (2 * 3 ^ k) := by
  apply dvd_L_of_mem
  rw [Finset.mem_Icc]
  have : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  omega

lemma two_mul_pow_three_dvd_L (k : ℕ) : 2 * 3 ^ k ∣ L (2 * 3 ^ k) := by
  apply dvd_L_of_mem
  rw [Finset.mem_Icc]
  have : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  omega

lemma not_pow_three_dvd_of_mem_of_ne {k j : ℕ}
    (hj : j ∈ Finset.Icc 1 (2 * 3 ^ k)) (hne1 : j ≠ 3 ^ k) (hne2 : j ≠ 2 * 3 ^ k) :
    ¬ (3 ^ k ∣ j) := by
  rintro ⟨m, rfl⟩
  rw [Finset.mem_Icc] at hj
  have hpos : 0 < 3 ^ k := by positivity
  have hm_ge : 1 ≤ m := by
    by_contra hm0
    have : m = 0 := by omega
    subst m
    omega
  have hm_le : m ≤ 2 := by nlinarith
  have : m = 1 ∨ m = 2 := by omega
  rcases this with rfl | rfl
  · exact hne1 (by ring)
  · exact hne2 (by ring)

lemma three_dvd_div_L_of_ne {k j : ℕ}
    (hj : j ∈ Finset.Icc 1 (2 * 3 ^ k)) (hne1 : j ≠ 3 ^ k) (hne2 : j ≠ 2 * 3 ^ k) :
    3 ∣ L (2 * 3 ^ k) / j := by
  have hj_dvd : j ∣ L (2 * 3 ^ k) := dvd_L_of_mem hj
  have h3k_dvd : 3 ^ k ∣ L (2 * 3 ^ k) := pow_three_dvd_L_two_mul_pow_three k
  have hnot : ¬ (3 ^ k ∣ j) := not_pow_three_dvd_of_mem_of_ne hj hne1 hne2
  by_contra h3
  have hcop : Nat.Coprime 3 (L (2 * 3 ^ k) / j) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hcop_pow : Nat.Coprime (3 ^ k) (L (2 * 3 ^ k) / j) := hcop.pow_left k
  rw [← Nat.mul_div_cancel' hj_dvd] at h3k_dvd
  exact hnot (hcop_pow.dvd_of_dvd_mul_right h3k_dvd)

lemma three_dvd_top_two_terms (k : ℕ) :
    3 ∣ L (2 * 3 ^ k) / 3 ^ k + L (2 * 3 ^ k) / (2 * 3 ^ k) := by
  obtain ⟨q, hq⟩ := two_mul_pow_three_dvd_L k
  have hpos1 : 0 < 3 ^ k := by positivity
  have hpos2 : 0 < 2 * 3 ^ k := by positivity
  have h1 : L (2 * 3 ^ k) / 3 ^ k = 2 * q := by
    have hq' : L (2 * 3 ^ k) = 3 ^ k * (2 * q) := by linarith
    rw [hq', Nat.mul_div_right _ hpos1]
  have h2 : L (2 * 3 ^ k) / (2 * 3 ^ k) = q := by
    rw [hq, Nat.mul_div_right _ hpos2]
  rw [h1, h2]
  exact ⟨q, by ring⟩

lemma three_dvd_a_two_mul_pow_three (k : ℕ) : 3 ∣ a (2 * 3 ^ k) := by
  unfold a
  set n := 2 * 3 ^ k
  have hpos : 0 < 3 ^ k := by positivity
  have hmem1 : 3 ^ k ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    omega
  have hmem2 : n ∈ (Finset.Icc 1 n).erase (3 ^ k) := by
    rw [Finset.mem_erase, Finset.mem_Icc]
    omega
  rw [← Finset.add_sum_erase _ _ hmem1, ← Finset.add_sum_erase _ _ hmem2, ← add_assoc]
  apply dvd_add (three_dvd_top_two_terms k)
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_erase] at hj
  obtain ⟨hne2, hj'⟩ := hj
  rw [Finset.mem_erase] at hj'
  obtain ⟨hne1, hj_mem⟩ := hj'
  exact three_dvd_div_L_of_ne hj_mem hne1 hne2

/-- For every $k \ge 1$, $3 \mid \gcd(a_{2 \cdot 3^k}, L_{2 \cdot 3^k})$. -/
theorem three_dvd_gcd_two_mul_pow_three {k : ℕ} (hk : 1 ≤ k) :
    3 ∣ Nat.gcd (a (2 * 3 ^ k)) (L (2 * 3 ^ k)) :=
  Nat.dvd_gcd (three_dvd_a_two_mul_pow_three k) (three_dvd_L_two_mul_pow_three hk)

/-- For every $k \ge 1$, $\gcd(a_{2 \cdot 3^k}, L_{2 \cdot 3^k}) > 1$. -/
theorem gcd_two_mul_pow_three_gt_one {k : ℕ} (hk : 1 ≤ k) :
    Nat.gcd (a (2 * 3 ^ k)) (L (2 * 3 ^ k)) > 1 := by
  obtain ⟨m, hm⟩ := three_dvd_gcd_two_mul_pow_three hk
  have hpos : 0 < 3 ^ k := by positivity
  have hL_ne : L (2 * 3 ^ k) ≠ 0 := by
    unfold L
    rw [ ne_eq, Finset.lcm_eq_zero_iff ]
    rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_Icc] at hx
    omega
  have hgcd_ne : Nat.gcd (a (2 * 3 ^ k)) (L (2 * 3 ^ k)) ≠ 0 :=
    Nat.gcd_ne_zero_right hL_ne
  omega

/-- **Erdős Problem 291, Part (ii)** (`erdos_291.parts.ii`):
There are infinitely many $n$ such that $\gcd(a_n, L_n) > 1$. -/
theorem erdos_291.parts.ii :
    { n : ℕ | Nat.gcd (a n) (L n) > 1 }.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ 2 * 3 ^ (k + 1))
  · intro k₁ k₂ h
    dsimp at h
    have hpow : (3 : ℕ) ^ (k₁ + 1) = 3 ^ (k₂ + 1) := by omega
    have hinj := Nat.pow_right_injective (by decide : 2 ≤ 3) hpow
    omega
  · intro k
    change Nat.gcd (a (2 * 3 ^ (k + 1))) (L (2 * 3 ^ (k + 1))) > 1
    exact gcd_two_mul_pow_three_gt_one (by omega)

end Erdos291

/-!
# Part 2: Erdős Problem 367 (`JSP-000303`) — Product of $2$-Full Parts of Consecutive Integers
-/

namespace Erdos367

/-- `B r n` is the $r$-full part of $n$: the product of prime powers $p^a \parallel n$ with $a \ge r$. -/
def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

lemma B_pos (r n : ℕ) : 0 < B r n := by
  unfold B
  apply Finset.prod_pos
  intro i hi
  rw [Finset.mem_filter, Finsupp.mem_support_iff] at hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hi.1 (Nat.factorization_zero_right n)
  have : 0 < i := Nat.pos_of_ne_zero hi0
  positivity

lemma B_dvd (r n : ℕ) : B r n ∣ n := by
  by_cases hn : n = 0
  · subst n; exact dvd_zero _
  · unfold B
    refine dvd_trans ?_ (dvd_of_eq (Nat.prod_factorization_pow_eq_self hn))
    exact Finset.prod_dvd_prod_of_subset
      (n.factorization.support.filter (fun i ↦ r ≤ n.factorization i))
      n.factorization.support
      (fun i ↦ i ^ n.factorization i)
      (Finset.filter_subset _ _)

lemma B_le (r : ℕ) {n : ℕ} (hn : 0 < n) : B r n ≤ n :=
  Nat.le_of_dvd hn (B_dvd r n)

lemma pow_dvd_B_of_pow_dvd {r m n : ℕ} (hr : 1 ≤ r) (hn : n ≠ 0) (hdvd : m ^ r ∣ n) :
    m ^ r ∣ B r n := by
  have hmr_ne : m ^ r ≠ 0 := ne_zero_of_dvd_ne_zero hn hdvd
  have hprod : (∏ i ∈ (m ^ r).factorization.support, i ^ (m ^ r).factorization i) = m ^ r :=
    Nat.prod_factorization_pow_eq_self hmr_ne
  have hfac_le : (m ^ r).factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hmr_ne hn).mpr hdvd
  rw [← hprod]
  unfold B
  apply dvd_trans
  · exact Finset.prod_dvd_prod_of_dvd
      (fun i ↦ i ^ (m ^ r).factorization i)
      (fun i ↦ i ^ n.factorization i)
      (fun i _ ↦ Nat.pow_dvd_pow i (hfac_le i))
  · apply Finset.prod_dvd_prod_of_subset
      (m ^ r).factorization.support
      (n.factorization.support.filter (fun i ↦ r ≤ n.factorization i))
      (fun i ↦ i ^ n.factorization i)
    intro i hi
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    rw [Finsupp.mem_support_iff, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul] at hi
    have hmi : 1 ≤ m.factorization i := by
      by_contra h0
      have : m.factorization i = 0 := by omega
      exact hi (by simp [this])
    have hri : r ≤ n.factorization i := by
      have hle := hfac_le i
      rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hle
      nlinarith
    exact ⟨by omega, hri⟩

lemma pow_le_B_of_pow_dvd {r m n : ℕ} (hr : 1 ≤ r) (hn : n ≠ 0) (hdvd : m ^ r ∣ n) :
    m ^ r ≤ B r n :=
  Nat.le_of_dvd (B_pos r n) (pow_dvd_B_of_pow_dvd hr hn hdvd)

/-! ## Upper Bound for $k \le 2$ (`erdos_367.variants.k_le_two`) -/

lemma prod_B_Ico_le_four_mul_sq {k n : ℕ} (hk : k ≤ 2) (hn : 1 ≤ n) :
    (∏ m ∈ Finset.Ico n (n + k), B 2 m) ≤ 4 * n ^ 2 := by
  interval_cases k
  · simp
    nlinarith
  · rw [Nat.Ico_succ_right_eq_insert_Ico (by omega), Finset.Ico_self, Finset.insert_empty,
      Finset.prod_singleton]
    have hle : B 2 n ≤ n := B_le 2 (by omega)
    nlinarith
  · have h1 : n + 2 = (n + 1) + 1 := by omega
    rw [h1, Finset.prod_Ico_succ_top (by omega), Finset.prod_Ico_succ_top (by omega),
      Finset.Ico_self, Finset.prod_empty, one_mul]
    have hle0 : B 2 n ≤ n := B_le 2 (by omega)
    have hle1 : B 2 (n + 1) ≤ n + 1 := B_le 2 (by omega)
    have hmul : B 2 n * B 2 (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul hle0 hle1
    nlinarith

/-- **Erdős Problem 367, $k \le 2$** (`erdos_367.variants.k_le_two`):
For $k \le 2$, $\prod_{n \le m < n+k} B_2(m) = O(n^2)$. -/
theorem erdos_367.variants.k_le_two : ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  intro k hk
  refine Asymptotics.IsBigO.of_bound 4 ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  rw [Real.norm_natCast, Real.rpow_two, Real.norm_of_nonneg (by positivity)]
  exact_mod_cast prod_B_Ico_le_four_mul_sq hk hn

/-! ## Cubic Pell-Triple Construction for $k \ge 3$ (`erdos_367.parts.ii` & `k_ge_three_lower`) -/

/-- Companion Pell subsequence $a_s = u_{3^s}$ satisfying $a_s^2 + 1 = 2 b_s^2$. -/
def pellA : ℕ → ℕ
  | 0 => 1
  | s + 1 => pellA s * (4 * pellA s ^ 2 + 3)

@[simp] lemma pellA_zero : pellA 0 = 1 := rfl
@[simp] lemma pellA_succ (s : ℕ) : pellA (s + 1) = pellA s * (4 * pellA s ^ 2 + 3) := rfl

/-- Companion Pell subsequence $b_s = v_{3^s}$ satisfying $2 b_s^2 = a_s^2 + 1$. -/
def pellB : ℕ → ℕ
  | 0 => 1
  | s + 1 => pellB s * (3 * pellA s ^ 2 + 2 * pellB s ^ 2)

@[simp] lemma pellB_zero : pellB 0 = 1 := rfl
@[simp] lemma pellB_succ (s : ℕ) :
    pellB (s + 1) = pellB s * (3 * pellA s ^ 2 + 2 * pellB s ^ 2) := rfl

/-- Middle term $x_s = u_{2 \cdot 3^s} = 2 a_s^2 + 1$. -/
def pellX (s : ℕ) : ℕ := 2 * pellA s ^ 2 + 1

/-- Starting integer $n_s = 2 a_s^2 = x_s - 1$. -/
def pellN (s : ℕ) : ℕ := 2 * pellA s ^ 2

lemma pellA_pos (s : ℕ) : 0 < pellA s := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [pellA_succ]
    positivity

lemma pellN_pos (s : ℕ) : 0 < pellN s := by
  unfold pellN
  have := pellA_pos s
  positivity

lemma pellA_strictMono : StrictMono pellA := by
  refine strictMono_nat_of_lt_succ (fun s ↦ ?_)
  rw [pellA_succ]
  have h := pellA_pos s
  nlinarith

lemma pellN_strictMono : StrictMono pellN := by
  intro a b hab
  unfold pellN
  have hlt := pellA_strictMono hab
  have ha := pellA_pos a
  nlinarith

lemma pell_norm (s : ℕ) : 2 * pellB s ^ 2 = pellA s ^ 2 + 1 := by
  induction s with
  | zero => decide
  | succ s ih =>
    calc 2 * pellB (s + 1) ^ 2
        = (2 * pellB s ^ 2) * (3 * pellA s ^ 2 + 2 * pellB s ^ 2) ^ 2 := by
            rw [pellB_succ]; ring
      _ = (pellA s ^ 2 + 1) * (3 * pellA s ^ 2 + (pellA s ^ 2 + 1)) ^ 2 := by rw [ih]
      _ = pellA (s + 1) ^ 2 + 1 := by rw [pellA_succ]; ring

lemma pellN_add_one (s : ℕ) : pellN s + 1 = pellX s := rfl

lemma pellN_add_two (s : ℕ) : pellN s + 2 = (2 * pellB s) ^ 2 := by
  unfold pellN
  have h := pell_norm s
  linarith [show (2 * pellB s) ^ 2 = 2 * (2 * pellB s ^ 2) by ring]

lemma pow_three_dvd_pellX_int (s : ℕ) : ((3 : ℤ) ^ (s + 1)) ∣ (pellX s : ℤ) := by
  induction s with
  | zero => decide
  | succ s ih =>
    obtain ⟨k, hk⟩ := ih
    have hstep : (pellX (s + 1) : ℤ) = (pellX s : ℤ) * (4 * (pellX s : ℤ) ^ 2 - 3) := by
      simp only [pellX, pellA_succ]
      push_cast
      ring
    rw [hstep, hk]
    refine ⟨k * (4 * (3 : ℤ) ^ (2 * s + 1) * k ^ 2 - 1), ?_⟩
    ring

lemma pow_three_dvd_pellX (s : ℕ) : 3 ^ (s + 1) ∣ pellX s := by
  exact_mod_cast pow_three_dvd_pellX_int s

lemma B_two_pellN_ge (s : ℕ) : pellA s ^ 2 ≤ B 2 (pellN s) := by
  apply pow_le_B_of_pow_dvd (by decide) (by have := pellN_pos s; omega)
  exact ⟨2, by unfold pellN; ring⟩

lemma B_two_pellN_add_one_ge (j : ℕ) :
    3 ^ (2 * j + 2) ≤ B 2 (pellN (2 * j + 1) + 1) := by
  have hdvd : (3 ^ (j + 1)) ^ 2 ∣ pellN (2 * j + 1) + 1 := by
    rw [pellN_add_one, show (3 ^ (j + 1)) ^ 2 = 3 ^ (2 * j + 2) by ring]
    exact pow_three_dvd_pellX (2 * j + 1)
  have hle := pow_le_B_of_pow_dvd (by decide) (by omega) hdvd
  rwa [show (3 ^ (j + 1)) ^ 2 = 3 ^ (2 * j + 2) by ring] at hle

lemma B_two_pellN_add_two_ge (s : ℕ) : pellN s + 2 ≤ B 2 (pellN s + 2) := by
  have hdvd : (2 * pellB s) ^ 2 ∣ pellN s + 2 := by
    rw [pellN_add_two]
  have hle := pow_le_B_of_pow_dvd (by decide) (by omega) hdvd
  rwa [← pellN_add_two] at hle

lemma prod_B_Ico_three_pellN_ge (j : ℕ) :
    3 ^ (2 * j + 2) * pellN (2 * j + 1) ^ 2 ≤
      2 * ∏ m ∈ Finset.Ico (pellN (2 * j + 1)) (pellN (2 * j + 1) + 3), B 2 m := by
  have hdecomp :
      (∏ m ∈ Finset.Ico (pellN (2 * j + 1)) (pellN (2 * j + 1) + 3), B 2 m) =
        B 2 (pellN (2 * j + 1)) * B 2 (pellN (2 * j + 1) + 1) * B 2 (pellN (2 * j + 1) + 2) := by
    have h3 : pellN (2 * j + 1) + 3 = (pellN (2 * j + 1) + 2) + 1 := by omega
    have h2 : pellN (2 * j + 1) + 2 = (pellN (2 * j + 1) + 1) + 1 := by omega
    rw [h3, Finset.prod_Ico_succ_top (by omega), h2, Finset.prod_Ico_succ_top (by omega),
      Finset.prod_Ico_succ_top (by omega), Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [hdecomp]
  have h0 : pellN (2 * j + 1) ≤ 2 * B 2 (pellN (2 * j + 1)) := by
    have h := B_two_pellN_ge (2 * j + 1)
    have hdef : pellN (2 * j + 1) = 2 * pellA (2 * j + 1) ^ 2 := rfl
    linarith
  have h1 : 3 ^ (2 * j + 2) ≤ B 2 (pellN (2 * j + 1) + 1) := B_two_pellN_add_one_ge j
  have h2 : pellN (2 * j + 1) ≤ B 2 (pellN (2 * j + 1) + 2) := by
    have := B_two_pellN_add_two_ge (2 * j + 1)
    omega
  calc 3 ^ (2 * j + 2) * pellN (2 * j + 1) ^ 2
      = pellN (2 * j + 1) * 3 ^ (2 * j + 2) * pellN (2 * j + 1) := by ring
    _ ≤ (2 * B 2 (pellN (2 * j + 1))) *
          B 2 (pellN (2 * j + 1) + 1) * B 2 (pellN (2 * j + 1) + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2
    _ = 2 * (B 2 (pellN (2 * j + 1)) *
          B 2 (pellN (2 * j + 1) + 1) * B 2 (pellN (2 * j + 1) + 2)) := by ring

lemma prod_B_Ico_mono_k {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (n : ℕ) :
    (∏ m ∈ Finset.Ico n (n + k₁), B 2 m) ≤ ∏ m ∈ Finset.Ico n (n + k₂), B 2 m := by
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · exact Finset.Ico_subset_Ico_right (by omega)
  · intro m _ _
    exact B_pos 2 m

/-- For every $k \ge 3$, $\prod_{n \le m < n+k} B_2(m)$ is NOT $O(n^2)$. -/
theorem not_isBigO_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    ¬ (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  intro hBigO
  obtain ⟨c, hc⟩ := hBigO.bound
  rw [Filter.eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * max c 1 + 1)
  let j := M + N
  have h9_ge : j + 1 ≤ 3 ^ (2 * j + 2) := by
    have hlt : j + 1 < 3 ^ (j + 1) := Nat.lt_pow_self (by decide : 1 < 3)
    have hpow : 3 ^ (j + 1) ≤ 3 ^ (2 * j + 2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hn_ge_idx : 2 * j + 1 ≤ pellN (2 * j + 1) := by
    have h1 := pellN_strictMono.id_le (2 * j + 1)
    simpa using h1
  have hn_ge_N : N ≤ pellN (2 * j + 1) := by omega
  have hn_pos : (0 : ℝ) < (pellN (2 * j + 1) : ℝ) := by exact_mod_cast pellN_pos (2 * j + 1)
  have hsq_pos : (0 : ℝ) < (pellN (2 * j + 1) : ℝ) ^ 2 := by positivity
  have hbound := hN (pellN (2 * j + 1)) hn_ge_N
  rw [Real.norm_natCast, Real.rpow_two, Real.norm_of_nonneg (by positivity)] at hbound
  have hmono :
      (∏ m ∈ Finset.Ico (pellN (2 * j + 1)) (pellN (2 * j + 1) + 3), B 2 m) ≤
        ∏ m ∈ Finset.Ico (pellN (2 * j + 1)) (pellN (2 * j + 1) + k), B 2 m :=
    prod_B_Ico_mono_k hk (pellN (2 * j + 1))
  have hlow_nat := prod_B_Ico_three_pellN_ge j
  have hlow_real : (3 : ℝ) ^ (2 * j + 2) * (pellN (2 * j + 1) : ℝ) ^ 2 ≤
      2 * ((∏ m ∈ Finset.Ico (pellN (2 * j + 1)) (pellN (2 * j + 1) + k), B 2 m : ℕ) : ℝ) := by
    have h1 : (3 : ℝ) ^ (2 * j + 2) * (pellN (2 * j + 1) : ℝ) ^ 2 ≤
        2 * ((∏ m ∈ Finset.Ico (pellN (2 * j + 1)) (pellN (2 * j + 1) + 3), B 2 m : ℕ) : ℝ) := by
      exact_mod_cast hlow_nat
    have h2 : ((∏ m ∈ Finset.Ico (pellN (2 * j + 1)) (pellN (2 * j + 1) + 3), B 2 m : ℕ) : ℝ) ≤
        ((∏ m ∈ Finset.Ico (pellN (2 * j + 1)) (pellN (2 * j + 1) + k), B 2 m : ℕ) : ℝ) := by
      exact_mod_cast hmono
    linarith
  have hM_real :
      2 * (c * (pellN (2 * j + 1) : ℝ) ^ 2) + (pellN (2 * j + 1) : ℝ) ^ 2 <
        (3 : ℝ) ^ (2 * j + 2) * (pellN (2 * j + 1) : ℝ) ^ 2 := by
    rw [show 2 * (c * (pellN (2 * j + 1) : ℝ) ^ 2) + (pellN (2 * j + 1) : ℝ) ^ 2 =
      (2 * c + 1) * (pellN (2 * j + 1) : ℝ) ^ 2 by ring]
    apply mul_lt_mul_of_pos_right _ hsq_pos
    have h9_real : ((M : ℕ) : ℝ) < ((3 ^ (2 * j + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M < 3 ^ (2 * j + 2) by omega)
    push_cast at h9_real
    have hc_le : 2 * c + 1 < (M : ℝ) := by
      have : 2 * c ≤ 2 * max c 1 := by linarith [le_max_left c 1]
      linarith
    linarith
  linarith

/-- **Erdős Problem 367, Part (ii)** (`erdos_367.parts.ii`, `JSP-000303`):
It is false that for every $k \ge 1$, $\prod_{n \le m < n+k} B_2(m) = O(n^2)$. -/
theorem erdos_367.parts.ii : ¬ ∀ k : ℕ, 1 ≤ k →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  intro h
  exact not_isBigO_of_three_le (by decide : 3 ≤ 3) (h 3 (by decide))

/-! ## Quantitative Lower Bound: $\prod_{m=n}^{n+2} B_2(m) \gg n^2 \log n$ Infinitely Often -/

lemma three_mul_pellA_le (s : ℕ) : 3 * pellA s ≤ 3 ^ (3 ^ s) := by
  induction s with
  | zero => decide
  | succ s ih =>
    have hstep : 3 * pellA (s + 1) ≤ (3 * pellA s) ^ 3 := by
      rw [pellA_succ]
      have hpos := pellA_pos s
      nlinarith
    have hpow : (3 * pellA s) ^ 3 ≤ (3 ^ (3 ^ s)) ^ 3 := Nat.pow_le_pow_left ih 3
    have hexp : (3 ^ (3 ^ s)) ^ 3 = 3 ^ (3 ^ (s + 1)) := by
      rw [← pow_mul, pow_succ]
    exact le_trans hstep (hexp ▸ hpow)

lemma pellN_le_pow_three (s : ℕ) : pellN s ≤ 3 ^ (2 * 3 ^ s) := by
  have h1 : pellN s ≤ (3 * pellA s) ^ 2 := by
    unfold pellN
    nlinarith
  have h2 : (3 * pellA s) ^ 2 ≤ (3 ^ (3 ^ s)) ^ 2 :=
    Nat.pow_le_pow_left (three_mul_pellA_le s) 2
  have h3 : (3 ^ (3 ^ s)) ^ 2 = 3 ^ (2 * 3 ^ s) := by
    rw [← pow_mul, mul_comm (3 ^ s) 2]
  exact le_trans h1 (h3 ▸ h2)

lemma log_pellN_le (s : ℕ) : Real.log (pellN s : ℝ) ≤ 4 * (3 : ℝ) ^ s := by
  have hpos : (0 : ℝ) < (pellN s : ℝ) := by exact_mod_cast pellN_pos s
  rw [Real.log_le_iff_le_exp hpos]
  have hnat : (pellN s : ℝ) ≤ (3 : ℝ) ^ (2 * 3 ^ s) := by exact_mod_cast pellN_le_pow_three s
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have hsq : (2 : ℝ) * 2 ≤ Real.exp 1 * Real.exp 1 :=
      mul_le_mul hexp1 hexp1 (by positivity) (by positivity)
    rw [← Real.exp_add, show (1 : ℝ) + 1 = 2 by ring] at hsq
    linarith
  have hpow : (3 : ℝ) ^ (2 * 3 ^ s) ≤ (Real.exp 2) ^ (2 * 3 ^ s) :=
    pow_le_pow_left₀ (by positivity) hexp2 _
  have hexp_mul : (Real.exp 2) ^ (2 * 3 ^ s) = Real.exp (4 * (3 : ℝ) ^ s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  linarith

/-- **Erdős Problem 367, Quantitative $k = 3$ Lower Bound** (`erdos_367.variants.k_ge_three_lower`):
There exists $c > 0$ such that $\prod_{n \le m < n+3} B_2(m) \ge c \, n^2 \log n$ for
infinitely many $n$. -/
theorem erdos_367.variants.k_ge_three_lower :
    ∃ c > (0 : ℝ), ∃ᶠ (n : ℕ) in atTop,
      c * ((n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤
        ((∏ m ∈ .Ico n (n + 3), B 2 m : ℕ) : ℝ) := by
  refine ⟨3 / 8, by norm_num, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  have hn_ge : N ≤ pellN (2 * N + 1) := by
    have h1 : 2 * N + 1 ≤ pellN (2 * N + 1) := pellN_strictMono.id_le (2 * N + 1)
    omega
  refine ⟨pellN (2 * N + 1), hn_ge, ?_⟩
  have hlog : Real.log (pellN (2 * N + 1) : ℝ) ≤ 4 * (3 : ℝ) ^ (2 * N + 1) :=
    log_pellN_le (2 * N + 1)
  have hprod_nat := prod_B_Ico_three_pellN_ge N
  have hprod_real : (3 : ℝ) ^ (2 * N + 2) * (pellN (2 * N + 1) : ℝ) ^ 2 ≤
      2 * ((∏ m ∈ Finset.Ico (pellN (2 * N + 1)) (pellN (2 * N + 1) + 3), B 2 m : ℕ) : ℝ) := by
    exact_mod_cast hprod_nat
  have h3pow :
      (3 : ℝ) ^ (2 * N + 2) * (pellN (2 * N + 1) : ℝ) ^ 2 =
        (3 / 4 : ℝ) * ((pellN (2 * N + 1) : ℝ) ^ 2 * (4 * (3 : ℝ) ^ (2 * N + 1))) := by
    rw [show 2 * N + 2 = (2 * N + 1) + 1 by omega, pow_succ]
    ring
  have hmul :
      (pellN (2 * N + 1) : ℝ) ^ 2 * Real.log (pellN (2 * N + 1) : ℝ) ≤
        (pellN (2 * N + 1) : ℝ) ^ 2 * (4 * (3 : ℝ) ^ (2 * N + 1)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

end Erdos367

#print axioms Erdos291.L_eval
#print axioms Erdos291.a_eval
#print axioms Erdos291.three_dvd_gcd_two_mul_pow_three
#print axioms Erdos291.erdos_291.parts.ii
#print axioms Erdos367.erdos_367.variants.k_le_two
#print axioms Erdos367.not_isBigO_of_three_le
#print axioms Erdos367.erdos_367.parts.ii
#print axioms Erdos367.erdos_367.variants.k_ge_three_lower
