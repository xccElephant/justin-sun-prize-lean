/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Erdos287

/-- The maximum gap between consecutive terms of a finite sequence `s : Fin k → ℕ`,
i.e., $\max_{0 \le i < k-1} (s(i+1) - s(i))$. -/
def max_gap (k : ℕ) (s : Fin k → ℕ) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin (k - 1) =>
    s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-!
## Part 1: Best-Possible Example (`max_gap = 3`)
-/

/-- The example $1 = \frac{1}{2}+\frac{1}{3}+\frac{1}{6}$ shows that `max_gap = 3` is achieved. -/
theorem erdos_287_best_possible :
    let s : Fin 3 → ℕ := ![2, 3, 6]
    StrictMono s ∧
    1 < s 0 ∧
    ∑ i : Fin 3, 1 / (s i : ℝ) = 1 ∧
    max_gap 3 s = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := rfl
    rw [huniv]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton]
    norm_num [
      show (![2, 3, 6] : Fin 3 → ℕ) 0 = 2 from rfl,
      show (![2, 3, 6] : Fin 3 → ℕ) 1 = 3 from rfl,
      show (![2, 3, 6] : Fin 3 → ℕ) 2 = 6 from rfl]
  · rfl

/-!
## Part 2: Erdős (1932) — `max_gap k s ≥ 2` (`erdos_287.variants.gap_at_least_two`)
-/

/-- The odd part of a natural number $n$, obtained by dividing out all factors of $2$. -/
def oddPart (n : ℕ) : ℕ :=
  if _ : 0 < n ∧ n % 2 = 0 then oddPart (n / 2) else n
termination_by n
decreasing_by omega

/-- The $2$-adic valuation $v_2(n)$ of a natural number $n$. -/
def twoVal (n : ℕ) : ℕ :=
  if _ : 0 < n ∧ n % 2 = 0 then twoVal (n / 2) + 1 else 0
termination_by n
decreasing_by omega

lemma two_pow_mul_oddPart (n : ℕ) : 2 ^ twoVal n * oddPart n = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [twoVal, oddPart]
    split_ifs with h
    · have ih' := ih (n / 2) (by omega)
      rw [pow_succ, mul_right_comm, ih']
      omega
    · simp

lemma oddPart_mod_two {n : ℕ} (hn : 0 < n) : oddPart n % 2 = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [oddPart]
    split_ifs with h
    · exact ih (n / 2) (by omega) (by omega)
    · omega

lemma le_twoVal_of_two_pow_dvd {n r : ℕ} (hn : 0 < n) (hdvd : 2 ^ r ∣ n) : r ≤ twoVal n := by
  by_contra hlt
  have hlt' : twoVal n + 1 ≤ r := by omega
  have h1 : 2 ^ (twoVal n + 1) ∣ 2 ^ r := Nat.pow_dvd_pow 2 hlt'
  have h2 : 2 ^ (twoVal n + 1) ∣ 2 ^ twoVal n * oddPart n := by
    rw [two_pow_mul_oddPart]
    exact dvd_trans h1 hdvd
  rw [pow_succ] at h2
  have hpos : 0 < 2 ^ twoVal n := Nat.pos_of_ne_zero (by positivity)
  have h3 : 2 ∣ oddPart n := (Nat.mul_dvd_mul_iff_left hpos).mp h2
  have hmod := oddPart_mod_two hn
  omega

lemma step_le_max_gap {k : ℕ} (s : Fin k → ℕ) (i : Fin (k - 1)) :
    s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩ ≤ max_gap k s := by
  unfold max_gap
  exact Finset.le_sup (f := fun j : Fin (k - 1) =>
    s ⟨j.val + 1, by omega⟩ - s ⟨j.val, by omega⟩) (Finset.mem_univ i)

lemma s_eq_add_of_max_gap_lt_two {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hs : StrictMono s) (hgap : max_gap k s < 2) (j : ℕ) (hj : j < k) :
    s ⟨j, hj⟩ = s ⟨0, by omega⟩ + j := by
  induction j with
  | zero => simp
  | succ m ih =>
    have hm : m < k := by omega
    have hstep := step_le_max_gap s ⟨m, by omega⟩
    dsimp at hstep
    have hmono : s ⟨m, hm⟩ < s ⟨m + 1, hj⟩ := hs (by simp)
    have ih' := ih hm
    omega

lemma prod_odd_mod_two {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ S, f x % 2 = 1) : (∏ x ∈ S, f x) % 2 = 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.mul_mod]
    have ha1 : f a % 2 = 1 := hf a (Finset.mem_insert_self a s)
    have hs1 : (∏ x ∈ s, f x) % 2 = 1 := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    rw [ha1, hs1]

lemma clear_denominators_eq {k : ℕ} (s : Fin k → ℕ) (hs_pos : ∀ i, 0 < s i)
    (hsum : ∑ i : Fin k, 1 / (s i : ℝ) = 1) (M : ℕ) (hM : ∀ i : Fin k, s i ∣ M) :
    ∑ i : Fin k, M / s i = M := by
  have hterm : ∀ i : Fin k, ((M / s i : ℕ) : ℝ) = (M : ℝ) * (1 / (s i : ℝ)) := by
    intro i
    have hdvd := hM i
    have hmul : s i * (M / s i) = M := Nat.mul_div_cancel' hdvd
    have hsi : (s i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (hs_pos i))
    apply mul_left_cancel₀ hsi
    calc
      (s i : ℝ) * ((M / s i : ℕ) : ℝ) = ((s i * (M / s i) : ℕ) : ℝ) := by push_cast; ring
      _ = (M : ℝ) := by rw [hmul]
      _ = ((s i : ℝ) * (1 / (s i : ℝ))) * (M : ℝ) := by rw [mul_one_div_cancel hsi, one_mul]
      _ = (s i : ℝ) * ((M : ℝ) * (1 / (s i : ℝ))) := by ring
  have hreal : (∑ i : Fin k, ((M / s i : ℕ) : ℝ)) = (M : ℝ) := by
    calc
      (∑ i : Fin k, ((M / s i : ℕ) : ℝ)) = ∑ i : Fin k, (M : ℝ) * (1 / (s i : ℝ)) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (M : ℝ) * ∑ i : Fin k, 1 / (s i : ℝ) := by rw [← Finset.mul_sum]
      _ = (M : ℝ) := by rw [hsum, mul_one]
  have hcast : ((∑ i : Fin k, M / s i : ℕ) : ℝ) = (M : ℝ) := by
    simpa using hreal
  exact Nat.cast_injective hcast

/-- **Erdős (1932)** (`erdos_287.variants.gap_at_least_two`):
For any strictly increasing sequence $1 < s_0 < \dots < s_{k-1}$ of $k \ge 2$ integers whose
reciprocals sum to $1$, the maximum gap between consecutive terms is at least $2$. -/
theorem erdos_287_gap_at_least_two :
    ∀ (k : ℕ) (_ : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s → 1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
    2 ≤ max_gap k s := by
  intro k hk s hs hs0 hsum
  by_contra hgap
  have hgap' : max_gap k s < 2 := by omega
  have hs_eq : ∀ i : Fin k, s i = s ⟨0, by omega⟩ + i.val := by
    intro i
    have h := s_eq_add_of_max_gap_lt_two hk s hs hgap' i.val i.isLt
    simpa only [Fin.eta] using h
  have hs_pos : ∀ i : Fin k, 0 < s i := by
    intro i; rw [hs_eq i]; omega
  let r : ℕ := Finset.sup Finset.univ (fun i : Fin k => twoVal (s i))
  have hr_le : ∀ i : Fin k, twoVal (s i) ≤ r :=
    fun i => Finset.le_sup (f := fun j : Fin k => twoVal (s j)) (Finset.mem_univ i)
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun i : Fin k => twoVal (s i))
  have hi₀_eq : twoVal (s i₀) = r := hi₀.symm
  have hr_pos : 1 ≤ r := by
    have h01 : s ⟨0, by omega⟩ % 2 = 0 ∨ s ⟨1, by omega⟩ % 2 = 0 := by
      have h1 := hs_eq ⟨1, by omega⟩
      dsimp at h1
      omega
    rcases h01 with h0 | h1
    · have hdvd : 2 ^ 1 ∣ s ⟨0, by omega⟩ := by omega
      exact le_trans (le_twoVal_of_two_pow_dvd (hs_pos _) hdvd) (hr_le _)
    · have hdvd : 2 ^ 1 ∣ s ⟨1, by omega⟩ := by omega
      exact le_trans (le_twoVal_of_two_pow_dvd (hs_pos _) hdvd) (hr_le _)
  have hunique : ∀ i : Fin k, i ≠ i₀ → twoVal (s i) < r := by
    intro i hne_i
    have hle := hr_le i
    apply lt_of_le_of_ne hle
    intro heq
    have h_order : i.val < i₀.val ∨ i₀.val < i.val := by
      rcases lt_trichotomy i.val i₀.val with h | h | h
      · exact Or.inl h
      · exact absurd (Fin.ext h) hne_i
      · exact Or.inr h
    have h_pair : ∃ a b : Fin k, a.val < b.val ∧ twoVal (s a) = r ∧ twoVal (s b) = r := by
      rcases h_order with h | h
      · exact ⟨i, i₀, h, heq, hi₀_eq⟩
      · exact ⟨i₀, i, h, hi₀_eq, heq⟩
    rcases h_pair with ⟨a, b, hab, ha_r, hb_r⟩
    have hsa : 2 ^ r * oddPart (s a) = s a := by
      rw [← ha_r, two_pow_mul_oddPart]
    have hsb : 2 ^ r * oddPart (s b) = s b := by
      rw [← hb_r, two_pow_mul_oddPart]
    have hsab : s a < s b := hs hab
    have h_odd_lt : oddPart (s a) < oddPart (s b) := by
      nlinarith [show 0 < 2 ^ r from Nat.pos_of_ne_zero (by positivity)]
    let m := 2 ^ r * (oddPart (s a) + 1)
    have hm_gt : s a < m := by
      have : 0 < 2 ^ r := Nat.pos_of_ne_zero (by positivity)
      dsimp [m]; nlinarith
    have hm_le : m ≤ s b := by
      dsimp [m]; nlinarith
    let idx : Fin k := ⟨m - s ⟨0, by omega⟩, by
      have := hs_eq a
      have := hs_eq b
      omega⟩
    have hs_idx : s idx = m := by
      have hidx := hs_eq idx
      change s idx = s ⟨0, by omega⟩ + (m - s ⟨0, by omega⟩) at hidx
      have ha_eq := hs_eq a
      omega
    have h_odd_mod : oddPart (s a) % 2 = 1 := oddPart_mod_two (hs_pos a)
    have h_even : 2 ∣ oddPart (s a) + 1 := by omega
    rcases h_even with ⟨t, ht⟩
    have hdvd_idx : 2 ^ (r + 1) ∣ s idx := by
      use t
      rw [hs_idx, pow_succ]
      dsimp [m]
      rw [ht]
      ring
    have h_ge : r + 1 ≤ twoVal (s idx) := le_twoVal_of_two_pow_dvd (hs_pos idx) hdvd_idx
    have h_le : twoVal (s idx) ≤ r := hr_le idx
    omega
  let O := ∏ j : Fin k, oddPart (s j)
  let M := 2 ^ r * O
  let term (i : Fin k) : ℕ :=
    2 ^ (r - twoVal (s i)) * ∏ j ∈ Finset.univ.erase i, oddPart (s j)
  have h_mul_term : ∀ i : Fin k, s i * term i = M := by
    intro i
    dsimp [term, M, O]
    have h1 := two_pow_mul_oddPart (s i)
    have h2 : oddPart (s i) * ∏ j ∈ Finset.univ.erase i, oddPart (s j) =
        ∏ j : Fin k, oddPart (s j) :=
      Finset.mul_prod_erase Finset.univ (fun j => oddPart (s j)) (Finset.mem_univ i)
    have h3 : 2 ^ twoVal (s i) * 2 ^ (r - twoVal (s i)) = 2 ^ r := by
      rw [← pow_add, Nat.add_sub_of_le (hr_le i)]
    calc
      s i * (2 ^ (r - twoVal (s i)) * ∏ j ∈ Finset.univ.erase i, oddPart (s j))
        = (2 ^ twoVal (s i) * oddPart (s i)) *
            (2 ^ (r - twoVal (s i)) * ∏ j ∈ Finset.univ.erase i, oddPart (s j)) := by rw [h1]
      _ = (2 ^ twoVal (s i) * 2 ^ (r - twoVal (s i))) *
            (oddPart (s i) * ∏ j ∈ Finset.univ.erase i, oddPart (s j)) := by ring
      _ = 2 ^ r * ∏ j : Fin k, oddPart (s j) := by rw [h3, h2]
  have hM_dvd : ∀ i : Fin k, s i ∣ M := fun i => ⟨term i, (h_mul_term i).symm⟩
  have hM_div : ∀ i : Fin k, M / s i = term i := by
    intro i
    rw [← h_mul_term i, Nat.mul_div_right _ (hs_pos i)]
  have hsum_nat := clear_denominators_eq s hs_pos hsum M hM_dvd
  have hsum_term : ∑ i : Fin k, term i = M := by
    simpa [hM_div] using hsum_nat
  have hterm_i₀ : term i₀ % 2 = 1 := by
    dsimp [term]
    rw [hi₀_eq, Nat.sub_self, pow_zero, one_mul]
    exact prod_odd_mod_two _ _ (fun j _ => oddPart_mod_two (hs_pos j))
  have hterm_other : ∀ i ∈ Finset.univ.erase i₀, term i % 2 = 0 := by
    intro i hi
    have hne_i : i ≠ i₀ := Finset.ne_of_mem_erase hi
    have hlt := hunique i hne_i
    dsimp [term]
    have hpow : 2 ^ (r - twoVal (s i)) % 2 = 0 := by
      obtain ⟨d, hd⟩ : ∃ d, r - twoVal (s i) = d + 1 := ⟨r - twoVal (s i) - 1, by omega⟩
      rw [hd, pow_succ]
      omega
    rw [Nat.mul_mod, hpow, zero_mul, Nat.zero_mod]
  have h_lhs_mod : (∑ i : Fin k, term i) % 2 = 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have h_erase_zero : (∑ i ∈ Finset.univ.erase i₀, term i) % 2 = 0 := by
      rw [Finset.sum_nat_mod, Finset.sum_eq_zero hterm_other]
      rfl
    omega
  have h_rhs_mod : M % 2 = 0 := by
    dsimp [M]
    obtain ⟨d, hd⟩ : ∃ d, r = d + 1 := ⟨r - 1, by omega⟩
    have hmul2 : 2 ^ r * O = 2 * (2 ^ d * O) := by
      rw [hd, pow_succ]; ring
    omega
  omega

/-!
## Part 3: Prime Conjecture Implies Erdős 287 for Large $k$
(`erdos_287.variants.prime_conjecture_implies`)
-/

lemma s_add_le_of_strictMono {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hs : StrictMono s)
    (j : ℕ) (hj : j < k) : s ⟨0, by omega⟩ + j ≤ s ⟨j, hj⟩ := by
  induction j with
  | zero => simp
  | succ m ih =>
    have hm : m < k := by omega
    have hmono : s ⟨m, hm⟩ < s ⟨m + 1, hj⟩ := hs (by simp)
    have ih' := ih hm
    omega

lemma first_term_lt_len {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hs : StrictMono s) (hs0 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, 1 / (s i : ℝ) = 1) : s ⟨0, by omega⟩ < k := by
  have hs0_pos : (0 : ℝ) < (s ⟨0, by omega⟩ : ℝ) := by positivity
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      1 / (s i : ℝ) ≤ 1 / (s ⟨0, by omega⟩ : ℝ) := by
    intro i _
    have h1 : s ⟨0, by omega⟩ ≤ s i := by
      have h := s_add_le_of_strictMono hk s hs i.val i.isLt
      simp only [Fin.eta] at h
      omega
    exact one_div_le_one_div_of_le hs0_pos (by exact_mod_cast h1)
  have hlt : 1 / (s ⟨1, by omega⟩ : ℝ) < 1 / (s ⟨0, by omega⟩ : ℝ) := by
    have h1 : s ⟨0, by omega⟩ < s ⟨1, by omega⟩ := hs (by simp)
    exact one_div_lt_one_div_of_lt hs0_pos (by exact_mod_cast h1)
  have hsum_lt : ∑ i : Fin k, 1 / (s i : ℝ) < ∑ _i : Fin k, 1 / (s ⟨0, by omega⟩ : ℝ) :=
    Finset.sum_lt_sum hle ⟨⟨1, by omega⟩, Finset.mem_univ _, hlt⟩
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum_lt
  have hmul : (s ⟨0, by omega⟩ : ℝ) < (k : ℝ) := by
    have h2 := mul_lt_mul_of_pos_right hsum_lt hs0_pos
    have hcancel : (k : ℝ) * (1 / (s ⟨0, by omega⟩ : ℝ)) * (s ⟨0, by omega⟩ : ℝ) = (k : ℝ) := by
      calc
        (k : ℝ) * (1 / (s ⟨0, by omega⟩ : ℝ)) * (s ⟨0, by omega⟩ : ℝ)
          = (k : ℝ) * ((s ⟨0, by omega⟩ : ℝ) * (1 / (s ⟨0, by omega⟩ : ℝ))) := by ring
        _ = (k : ℝ) * 1 := by rw [mul_one_div_cancel (ne_of_gt hs0_pos)]
        _ = (k : ℝ) := mul_one _
    linarith
  exact_mod_cast hmul

lemma sum_ite_eq_le {k : ℕ} (s : Fin k → ℕ) (hs : Function.Injective s) (v w : ℕ) :
    ∑ i : Fin k, (if s i = v then w else 0) ≤ w := by
  by_cases h : ∃ i : Fin k, s i = v
  · rcases h with ⟨i₀, hi₀⟩
    rw [Finset.sum_eq_single i₀]
    · simp [hi₀]
    · intro j _ hj
      have hne : s j ≠ v := fun heq => hj (hs (heq.trans hi₀.symm))
      simp [hne]
    · intro hmem
      exact absurd (Finset.mem_univ i₀) hmem
  · push Not at h
    rw [Finset.sum_eq_zero (fun i _ => by simp [h i])]
    exact Nat.zero_le w

lemma prime_not_dvd_prod {α : Type*} [DecidableEq α] {q : ℕ} (hq : Nat.Prime q)
    (S : Finset α) (g : α → ℕ) (hg : ∀ x ∈ S, ¬ (q ∣ g x)) : ¬ (q ∣ ∏ x ∈ S, g x) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact hq.not_dvd_one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    intro hdvd
    rcases hq.dvd_mul.mp hdvd with h1 | h2
    · exact hg a (Finset.mem_insert_self a s) h1
    · exact ih (fun x hx => hg x (Finset.mem_insert_of_mem hx)) h2

/-- Any prime $q > 11$ with $4q > s_i$ for all $i$ cannot divide any denominator $s_i$
in a strictly increasing Egyptian fraction representation of $1$. -/
lemma not_dvd_of_prime_gt_eleven {k : ℕ} (s : Fin k → ℕ) (hs : StrictMono s)
    (hs_pos : ∀ i, 0 < s i) (hsum : ∑ i : Fin k, 1 / (s i : ℝ) = 1)
    {q : ℕ} (hq : Nat.Prime q) (hq11 : 11 < q) (hbound : ∀ i : Fin k, s i < 4 * q) :
    ∀ i₀ : Fin k, ¬ (q ∣ s i₀) := by
  intro i₀ hdvd₀
  let f (i : Fin k) : ℕ := if q ∣ s i then 1 else s i
  let P : ℕ := ∏ i : Fin k, f i
  have hq_not_dvd_P : ¬ (q ∣ P) := by
    apply prime_not_dvd_prod hq Finset.univ f
    intro i _
    dsimp [f]
    split_ifs with h
    · exact hq.not_dvd_one
    · exact h
  let c1 (i : Fin k) : ℕ := if s i = q then 6 else 0
  let c2 (i : Fin k) : ℕ := if s i = 2 * q then 3 else 0
  let c3 (i : Fin k) : ℕ := if s i = 3 * q then 2 else 0
  let c (i : Fin k) : ℕ := c1 i + c2 i + c3 i
  have hc_cases : ∀ i : Fin k, q ∣ s i →
      s i * c i = 6 * q ∧ 0 < c i := by
    intro i ⟨m, hm⟩
    have hpos_i := hs_pos i
    have hlt_i := hbound i
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm; omega
      · exact hpos
    have hm_lt4 : m < 4 := by
      by_contra hge
      have hge4 : 4 ≤ m := by omega
      have hmul4 : q * 4 ≤ q * m := Nat.mul_le_mul_left q hge4
      omega
    have hm_range : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    dsimp [c, c1, c2, c3]
    rcases hm_range with rfl | rfl | rfl
    · have hsi : s i = q := by omega
      rw [hsi]; split_ifs <;> omega
    · have hsi : s i = 2 * q := by omega
      rw [hsi]; split_ifs <;> omega
    · have hsi : s i = 3 * q := by omega
      rw [hsi]; split_ifs <;> omega
  have hc_zero : ∀ i : Fin k, ¬ (q ∣ s i) → c i = 0 := by
    intro i hndvd
    have h1 : s i ≠ q := fun h => hndvd (h ▸ dvd_rfl)
    have h2 : s i ≠ 2 * q := fun h => hndvd ⟨2, by linarith⟩
    have h3 : s i ≠ 3 * q := fun h => hndvd ⟨3, by linarith⟩
    dsimp [c, c1, c2, c3]
    simp [h1, h2, h3]
  let M : ℕ := 6 * q * P
  let term (i : Fin k) : ℕ :=
    if q ∣ s i then c i * P else 6 * q * ∏ j ∈ Finset.univ.erase i, f j
  have h_mul_term : ∀ i : Fin k, s i * term i = M := by
    intro i
    dsimp [term, M]
    split_ifs with hdvd
    · have hmul := (hc_cases i hdvd).1
      calc
        s i * (c i * P) = (s i * c i) * P := by ring
        _ = 6 * q * P := by rw [hmul]
    · have hf_i : f i = s i := if_neg hdvd
      have hprod : f i * ∏ j ∈ Finset.univ.erase i, f j = P :=
        Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)
      rw [hf_i] at hprod
      calc
        s i * (6 * q * ∏ j ∈ Finset.univ.erase i, f j)
          = 6 * q * (s i * ∏ j ∈ Finset.univ.erase i, f j) := by ring
        _ = 6 * q * P := by rw [hprod]
  have hM_dvd : ∀ i : Fin k, s i ∣ M := fun i => ⟨term i, (h_mul_term i).symm⟩
  have hM_div : ∀ i : Fin k, M / s i = term i := by
    intro i
    rw [← h_mul_term i, Nat.mul_div_right _ (hs_pos i)]
  have hsum_nat := clear_denominators_eq s hs_pos hsum M hM_dvd
  have hsum_term : ∑ i : Fin k, term i = M := by
    simpa [hM_div] using hsum_nat
  have hterm_mod : ∀ i : Fin k, term i % q = (c i * P) % q := by
    intro i
    dsimp [term]
    split_ifs with hdvd
    · rfl
    · rw [hc_zero i hdvd, zero_mul, Nat.zero_mod]
      have : 6 * q * ∏ j ∈ Finset.univ.erase i, f j =
          q * (6 * ∏ j ∈ Finset.univ.erase i, f j) := by ring
      rw [this, Nat.mul_mod_right]
  have h_sum_mod : (∑ i : Fin k, (c i * P)) % q = 0 := by
    rw [Finset.sum_nat_mod]
    have hcongr : ∑ i : Fin k, (c i * P) % q = ∑ i : Fin k, term i % q :=
      Finset.sum_congr rfl (fun i _ => (hterm_mod i).symm)
    rw [hcongr, ← Finset.sum_nat_mod, hsum_term]
    dsimp [M]
    have : 6 * q * P = q * (6 * P) := by ring
    rw [this, Nat.mul_mod_right]
  rw [← Finset.sum_mul] at h_sum_mod
  have hq_dvd_mul : q ∣ (∑ i : Fin k, c i) * P := Nat.dvd_of_mod_eq_zero h_sum_mod
  have hq_dvd_C : q ∣ ∑ i : Fin k, c i :=
    (hq.dvd_mul.mp hq_dvd_mul).resolve_right hq_not_dvd_P
  have hC_pos : 0 < ∑ i : Fin k, c i := by
    have hc_i₀ : 0 < c i₀ := (hc_cases i₀ hdvd₀).2
    have hle : c i₀ ≤ ∑ i : Fin k, c i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) (Finset.mem_univ i₀)
    omega
  have hC_le : ∑ i : Fin k, c i ≤ 11 := by
    have hsplit : ∑ i : Fin k, c i =
        (∑ i : Fin k, c1 i) + (∑ i : Fin k, c2 i) + (∑ i : Fin k, c3 i) := by
      simp only [c, Finset.sum_add_distrib]
    have h1 : ∑ i : Fin k, c1 i ≤ 6 := sum_ite_eq_le s hs.injective q 6
    have h2 : ∑ i : Fin k, c2 i ≤ 3 := sum_ite_eq_le s hs.injective (2 * q) 3
    have h3 : ∑ i : Fin k, c3 i ≤ 2 := sum_ite_eq_le s hs.injective (3 * q) 2
    omega
  have hq_le_C : q ≤ ∑ i : Fin k, c i := Nat.le_of_dvd hC_pos hq_dvd_C
  omega

lemma stay_below_barrier {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hgap : max_gap k s < 3) (p : ℕ) (hs0 : s ⟨0, by omega⟩ < p)
    (havoid : ∀ i : Fin k, s i ≠ p ∧ s i ≠ p + 1)
    (m : ℕ) (hm : m < k) : s ⟨m, hm⟩ < p := by
  induction m with
  | zero => exact hs0
  | succ j ih =>
    have hj : j < k := by omega
    have ih' := ih hj
    have hstep := step_le_max_gap s ⟨j, by omega⟩
    dsimp at hstep
    have hav := havoid ⟨j + 1, hm⟩
    omega

/-- **Erdős Problem 287 Conditional Reduction** (`erdos_287.variants.prime_conjecture_implies`):
If for all large $N$ there is a prime $p \in [N, 2N]$ such that $(p+1)/2$ is also prime, then
there exists $k_0$ such that every strictly increasing Egyptian fraction representation of $1$
with $k \ge k_0$ terms $> 1$ satisfies $\max_i (s_{i+1} - s_i) \ge 3$. -/
theorem erdos_287_prime_conjecture_implies :
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℕ, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2 * N ∧ Nat.Prime ((p + 1) / 2)) →
    ∃ (k₀ : ℕ), ∀ (k : ℕ) (_ : k₀ ≤ k) (_ : 2 ≤ k) (s : Fin k → ℕ),
      StrictMono s → 1 < s ⟨0, by omega⟩ →
      ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
      3 ≤ max_gap k s := by
  rintro ⟨N₀, hN₀⟩
  refine ⟨2 * N₀ + 48, ?_⟩
  intro k hk₀ hk s hs hs0 hsum
  by_contra hgap
  have hgap' : max_gap k s < 3 := by omega
  have hs_pos : ∀ i : Fin k, 0 < s i := by
    intro i
    have h := s_add_le_of_strictMono hk s hs i.val i.isLt
    simp only [Fin.eta] at h
    omega
  have hlast_ge : s ⟨0, by omega⟩ + (k - 1) ≤ s ⟨k - 1, by omega⟩ :=
    s_add_le_of_strictMono hk s hs (k - 1) (by omega)
  have hs0_lt_k : s ⟨0, by omega⟩ < k := first_term_lt_len hk s hs hs0 hsum
  let N : ℕ := s ⟨k - 1, by omega⟩ / 2
  have hN_ge_N₀ : N₀ ≤ N := by omega
  have hN_ge_24 : 24 ≤ N := by omega
  have hs0_le_N : s ⟨0, by omega⟩ ≤ N := by omega
  obtain ⟨p, hp, hNp, hp2N, hq⟩ := hN₀ N hN_ge_N₀
  let q : ℕ := (p + 1) / 2
  have hp_gt_two : 2 < p := by omega
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  have hp_lt_2N : p < 2 * N := by omega
  have hp1_le_last : p + 1 ≤ s ⟨k - 1, by omega⟩ := by omega
  have h2q : 2 * q = p + 1 := by omega
  have hq11 : 11 < q := by omega
  have hp11 : 11 < p := by omega
  have hbound_q : ∀ i : Fin k, s i < 4 * q := by
    intro i
    have hi_le : s i ≤ s ⟨k - 1, by omega⟩ := by
      rcases eq_or_lt_of_le (show i.val ≤ k - 1 by omega) with heq | hlt
      · have : i = ⟨k - 1, by omega⟩ := Fin.ext heq
        rw [this]
      · exact le_of_lt (hs hlt)
    omega
  have hbound_p : ∀ i : Fin k, s i < 4 * p := by
    intro i
    have := hbound_q i
    omega
  have hnot_dvd_p := not_dvd_of_prime_gt_eleven s hs hs_pos hsum hp hp11 hbound_p
  have hnot_dvd_q := not_dvd_of_prime_gt_eleven s hs hs_pos hsum hq hq11 hbound_q
  have havoid : ∀ i : Fin k, s i ≠ p ∧ s i ≠ p + 1 := by
    intro i
    refine ⟨?_, ?_⟩
    · intro heq
      exact hnot_dvd_p i (heq ▸ dvd_rfl)
    · intro heq
      have hdvd : q ∣ s i := ⟨2, by omega⟩
      exact hnot_dvd_q i hdvd
  have hs0_lt_p : s ⟨0, by omega⟩ < p := by
    have hne := (havoid ⟨0, by omega⟩).1
    omega
  have hlast_lt_p : s ⟨k - 1, by omega⟩ < p :=
    stay_below_barrier hk s hgap' p hs0_lt_p havoid (k - 1) (by omega)
  omega

#print axioms erdos_287_best_possible
#print axioms erdos_287_gap_at_least_two
#print axioms erdos_287_prime_conjecture_implies

end Erdos287
