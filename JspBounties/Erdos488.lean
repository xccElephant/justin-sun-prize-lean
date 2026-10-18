/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 488 (`JSP-000396`)

Let $A$ be a finite nonempty set of integers $\ge 2$, and
$$B = \{n \ge 1 : \exists a \in A, \, a \mid n\}.$$
Erdős Problem 488 asks whether for every $m > n \ge \max(A)$,
$$\frac{|B \cap [1, m]|}{m} < 2 \frac{|B \cap [1, n]|}{n}.$$

In this file we formalize and prove (with zero `sorry`):
1. Exact bridge between the set-filter formulation in `FormalConjectures/ErdosProblems/488.lean`
   and the finite counting function `B_card A x = |B_A ∩ [1, x]|`.
2. **Strengthened Singleton Theorem (`erdos_488_singleton`)**:
   For any $a \ge 1$ and $m > n \ge a$, $(n + 1) B_{\{a\}}(m) \le 2 m B_{\{a\}}(n)$, which yields
   the strict inequality $B_{\{a\}}(m)/m < 2 B_{\{a\}}(n)/n$.
3. **Sharpness of the Constant $2$ (`erdos_488_sharpness`)**:
   For $A = \{a\}$ ($a \ge 2$), $n = 2a - 1$, $m = 2a$, equality holds in the strengthened bound
   $(n + 1) B_{\{a\}}(m) = 2 m B_{\{a\}}(n)$, and the ratio is $2 - 1/a \to 2$.
4. **Full Two-Element Theorem (`erdos_488_pair`)**:
   Erdős Problem 488 holds for every two-element set $A = \{a, b\}$ with $2 \le a < b \le n < m$.
5. **Full $2 \in A$ Theorem (`erdos_488_of_two_mem`)**:
   Erdős Problem 488 holds for every finite set $A \subset \mathbb{N}_{\ge 2}$ containing $2$.
6. **High-Half Inductive Step (`erdos_488_insert_gt_half`)**:
   Adding any generator $a \in (n/2, n]$ not divisible by existing elements of $A$ preserves the
   strengthened inequality $(n + 1) B_A(m) \le 2 m B_A(n)$.
7. **Disproof of the [Er61]/[Er80] Non-Multiples Variant (`erdos_488_nonmultiples_false`)**:
   Disproves the misprinted version where $a \mid n$ is replaced by $\forall a \in A, a \nmid n$,
   using the minimal counterexample $A = \{2, 3, 5, 7\}$, $n = 9$, $m = 13$.
-/

open scoped Finset

namespace Erdos488

/-- The subset of `[1, x]` consisting of multiples of at least one element of `A`. -/
def multiplesIn (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)

/-- Counting function `B_card A x = |B_A ∩ [1, x]|`. -/
def B_card (A : Finset ℕ) (x : ℕ) : ℕ :=
  (multiplesIn A x).card

/-- Bridge lemma showing `multiplesIn A x` matches the exact filter in `488.lean`. -/
theorem filter_B_eq_multiplesIn (A : Finset ℕ) (x : ℕ) :
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    (Finset.Icc 1 x).filter (· ∈ B) = multiplesIn A x := by
  ext k
  simp only [multiplesIn, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq, ge_iff_le]
  tauto

/-- The multiples of a single integer `a` in `[1, x]`. -/
def singleMultiplesIn (a x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (a ∣ ·)

theorem multiplesIn_singleton (a x : ℕ) :
    multiplesIn {a} x = singleMultiplesIn a x := by
  ext k
  simp [multiplesIn, singleMultiplesIn]

/-- The number of multiples of `a` in `[1, x]` is `x / a`. -/
theorem card_singleMultiplesIn (a x : ℕ) :
    (singleMultiplesIn a x).card = x / a := by
  have h_eq : singleMultiplesIn a x = {k ∈ Finset.range x.succ | k ≠ 0 ∧ a ∣ k} := by
    ext k
    simp only [singleMultiplesIn, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Nat.lt_succ_iff]
    omega
  rw [h_eq, Nat.card_multiples']

theorem B_card_singleton (a x : ℕ) :
    B_card {a} x = x / a := by
  rw [B_card, multiplesIn_singleton, card_singleMultiplesIn]

/-- Fundamental arithmetic inequality for a single generator `a ≤ n`:
`n + 1 ≤ 2 * a * (n / a)`. -/
theorem succ_le_two_mul_div (a n : ℕ) (ha : 1 ≤ a) (han : a ≤ n) :
    n + 1 ≤ 2 * a * (n / a) := by
  have hq : 1 ≤ n / a := Nat.div_pos han ha
  have hmod : n % a < a := Nat.mod_lt n ha
  have hdiv : a * (n / a) + n % a = n := Nat.div_add_mod n a
  nlinarith

/-- Strengthened inequality `(n + 1) * B_card {a} m ≤ 2 * m * B_card {a} n` for `A = {a}`. -/
theorem erdos_488_singleton_strengthened (a n m : ℕ) (ha : 1 ≤ a) (han : a ≤ n) :
    (n + 1) * B_card {a} m ≤ 2 * m * B_card {a} n := by
  rw [B_card_singleton, B_card_singleton]
  have h1 : a * (m / a) ≤ m := Nat.mul_div_le m a
  have h2 : n + 1 ≤ 2 * a * (n / a) := succ_le_two_mul_div a n ha han
  have h3 : (n + 1) * (a * (m / a)) ≤ (2 * a * (n / a)) * m :=
    Nat.mul_le_mul h2 h1
  nlinarith

/-- Strict natural-number inequality for `A = {a}` when `m > n ≥ a ≥ 1`. -/
theorem erdos_488_singleton_nat (a n m : ℕ) (ha : 1 ≤ a) (han : a ≤ n) (hnm : n < m) :
    n * B_card {a} m < 2 * m * B_card {a} n := by
  have h_str := erdos_488_singleton_strengthened a n m ha han
  have hm_pos : 1 ≤ B_card {a} m := by
    rw [B_card_singleton]
    exact Nat.div_pos (by omega) ha
  nlinarith

/-- Conversion from the natural-number inequality `n * B(m) < 2 * m * B(n)` to the exact
rational inequality in `FormalConjectures/ErdosProblems/488.lean`. -/
theorem rat_div_lt_two_mul_div_of_nat_lt (A : Finset ℕ) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m)
    (h : n * B_card A m < 2 * m * B_card A n) :
    letI B := {k ≥ 1 | ∃ a ∈ A, a ∣ k}
    ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
      2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  rw [filter_B_eq_multiplesIn, filter_B_eq_multiplesIn]
  change (B_card A m : ℚ) / (m : ℚ) < 2 * (B_card A n : ℚ) / (n : ℚ)
  have hn_q : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  have hm_q : (0 : ℚ) < m := Nat.cast_pos.mpr hm
  rw [div_lt_div_iff₀ hm_q hn_q]
  have h_q : ((n * B_card A m : ℕ) : ℚ) < ((2 * m * B_card A n : ℕ) : ℚ) :=
    Nat.cast_lt.mpr h
  push_cast at h_q
  linarith

/-- **Erdős Problem 488 for Singleton Sets (`|A| = 1`)**. -/
theorem erdos_488_singleton (a n m : ℕ) (ha : 2 ≤ a) (han : a ≤ n) (hnm : n < m) :
    letI B := {k ≥ 1 | ∃ x ∈ ({a} : Finset ℕ), x ∣ k}
    ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
      2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  apply rat_div_lt_two_mul_div_of_nat_lt {a} n m (by omega) (by omega)
  exact erdos_488_singleton_nat a n m (by omega) han hnm

/-- **Sharpness of the Constant 2 (`erdos_488_sharpness`)**:
For `A = {a}` (`a ≥ 2`), `n = 2a - 1`, `m = 2a`, we have `B_card {a} n = 1`, `B_card {a} m = 2`,
and exact equality `(n + 1) * B_card {a} m = 2 * m * B_card {a} n` in the strengthened bound. -/
theorem erdos_488_sharpness (a : ℕ) (ha : 2 ≤ a) :
    B_card {a} (2 * a - 1) = 1 ∧
    B_card {a} (2 * a) = 2 ∧
    (2 * a - 1 + 1) * B_card {a} (2 * a) = 2 * (2 * a) * B_card {a} (2 * a - 1) := by
  rw [B_card_singleton, B_card_singleton]
  have h1 : (2 * a - 1) / a = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have h2 : (2 * a) / a = 2 := by
    apply Nat.div_eq_of_lt_le <;> omega
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  omega

/-- Subadditivity of `B_card` under union: `B_card {a, b} m ≤ m / a + m / b`. -/
theorem B_card_pair_le (a b m : ℕ) :
    B_card {a, b} m ≤ m / a + m / b := by
  have h_sub : multiplesIn {a, b} m ⊆ singleMultiplesIn a m ∪ singleMultiplesIn b m := by
    intro k hk
    simp only [multiplesIn, singleMultiplesIn, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hk ⊢
    rcases hk with ⟨hk1, x, rfl | rfl, hxk⟩
    · left; exact ⟨hk1, hxk⟩
    · right; exact ⟨hk1, hxk⟩
  calc B_card {a, b} m
      ≤ (singleMultiplesIn a m ∪ singleMultiplesIn b m).card := Finset.card_le_card h_sub
    _ ≤ (singleMultiplesIn a m).card + (singleMultiplesIn b m).card := Finset.card_union_le _ _
    _ = m / a + m / b := by rw [card_singleMultiplesIn, card_singleMultiplesIn]

/-- Lower bound on `B_card {a, b} n` when `¬(a ∣ b)` and `1 ≤ b ≤ n`:
`b` is an additional element in `multiplesIn {a, b} n` outside `singleMultiplesIn a n`. -/
theorem B_card_pair_ge_of_not_dvd (a b n : ℕ) (hb : 1 ≤ b) (hbn : b ≤ n) (hab : ¬(a ∣ b)) :
    n / a + 1 ≤ B_card {a, b} n := by
  have h_sub : insert b (singleMultiplesIn a n) ⊆ multiplesIn {a, b} n := by
    intro k hk
    simp only [Finset.mem_insert, singleMultiplesIn, multiplesIn, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_singleton] at hk ⊢
    rcases hk with hk_eq | ⟨hk1, hka⟩
    · subst hk_eq
      exact ⟨⟨hb, hbn⟩, k, Or.inr rfl, dvd_rfl⟩
    · exact ⟨hk1, a, Or.inl rfl, hka⟩
  have hb_not_mem : b ∉ singleMultiplesIn a n := by
    simp only [singleMultiplesIn, Finset.mem_filter, Finset.mem_Icc, not_and]
    intro _
    exact hab
  have h_card : (insert b (singleMultiplesIn a n)).card ≤ B_card {a, b} n :=
    Finset.card_le_card h_sub
  rw [Finset.card_insert_of_notMem hb_not_mem, card_singleMultiplesIn] at h_card
  exact h_card

/-- If `a ∣ b`, then `multiplesIn {a, b} x = multiplesIn {a} x`. -/
theorem multiplesIn_pair_eq_of_dvd (a b x : ℕ) (hab : a ∣ b) :
    multiplesIn {a, b} x = multiplesIn {a} x := by
  ext k
  simp only [multiplesIn, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hk, y, rfl | rfl, hyk⟩
    · exact ⟨hk, y, rfl, hyk⟩
    · exact ⟨hk, a, rfl, dvd_trans hab hyk⟩
  · rintro ⟨hk, y, rfl, hyk⟩
    exact ⟨hk, y, Or.inl rfl, hyk⟩

/-- **Erdős Problem 488 for All Two-Element Sets (`|A| = 2`)** in natural-number form:
For `2 ≤ a < b ≤ n < m`, `n * B_card {a, b} m < 2 * m * B_card {a, b} n`. -/
theorem erdos_488_pair_nat (a b n m : ℕ) (ha : 2 ≤ a) (hab : a < b) (hbn : b ≤ n) (hnm : n < m) :
    n * B_card {a, b} m < 2 * m * B_card {a, b} n := by
  by_cases hdvd : a ∣ b
  · have h_eq_n : B_card {a, b} n = B_card {a} n := by
      simp [B_card, multiplesIn_pair_eq_of_dvd a b n hdvd]
    have h_eq_m : B_card {a, b} m = B_card {a} m := by
      simp [B_card, multiplesIn_pair_eq_of_dvd a b m hdvd]
    rw [h_eq_n, h_eq_m]
    exact erdos_488_singleton_nat a n m (by omega) (by omega) hnm
  · have h_low : n / a + 1 ≤ B_card {a, b} n :=
      B_card_pair_ge_of_not_dvd a b n (by omega) hbn hdvd
    have h_high : B_card {a, b} m ≤ m / a + m / b := B_card_pair_le a b m
    have h_div_n : n + 1 ≤ a * (n / a + 1) := by
      have hmod : n % a < a := Nat.mod_lt n (by omega)
      have hdiv : a * (n / a) + n % a = n := Nat.div_add_mod n a
      nlinarith
    have h_a_bn : n + 1 ≤ a * B_card {a, b} n := by
      calc n + 1 ≤ a * (n / a + 1) := h_div_n
        _ ≤ a * B_card {a, b} n := Nat.mul_le_mul_left a h_low
    have h_mb_pos : 1 ≤ m / b := Nat.div_pos (by omega) (by omega)
    have h_ma : a * (m / a) ≤ m := Nat.mul_div_le m a
    have h_mb : b * (m / b) ≤ m := Nat.mul_div_le m b
    have h_amb : a * (m / b) < m := by nlinarith
    have h_a_bm : a * B_card {a, b} m < 2 * m := by
      have : a * B_card {a, b} m ≤ a * (m / a + m / b) := Nat.mul_le_mul_left a h_high
      nlinarith
    have h_bn_pos : 1 ≤ B_card {a, b} n := by
      have : 0 ≤ n / a := Nat.zero_le _
      omega
    nlinarith

/-- **Erdős Problem 488 for All Two-Element Sets (`|A| = 2`)** in exact rational form. -/
theorem erdos_488_pair (a b n m : ℕ) (ha : 2 ≤ a) (hab : a < b) (hbn : b ≤ n) (hnm : n < m) :
    letI B := {k ≥ 1 | ∃ x ∈ ({a, b} : Finset ℕ), x ∣ k}
    ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
      2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  apply rat_div_lt_two_mul_div_of_nat_lt {a, b} n m (by omega) (by omega)
  exact erdos_488_pair_nat a b n m ha hab hbn hnm

/-- If `1 ∉ A`, then `1 ∉ multiplesIn A m`, so `B_card A m ≤ m - 1`. -/
theorem B_card_le_pred (A : Finset ℕ) (m : ℕ) (h1 : 1 ∉ A) :
    B_card A m ≤ m - 1 := by
  have h_sub : multiplesIn A m ⊆ Finset.Icc 2 m := by
    intro k hk
    simp only [multiplesIn, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    rcases hk with ⟨⟨hk1, hkm⟩, a, haA, hak⟩
    refine ⟨?_, hkm⟩
    by_contra hlt
    have hk_eq : k = 1 := by omega
    subst hk_eq
    have ha_eq : a = 1 := Nat.eq_one_of_dvd_one hak
    subst ha_eq
    exact h1 haA
  calc B_card A m ≤ (Finset.Icc 2 m).card := Finset.card_le_card h_sub
    _ = m - 1 := by simp [Nat.card_Icc]

/-- **Erdős Problem 488 for Any Set Containing `2` (`2 ∈ A`)**:
For any finite set `A` with `0 ∉ A`, `1 ∉ A`, and `2 ∈ A`, and any `m > n ≥ max(A)`,
`n * B_card A m < 2 * m * B_card A n`. -/
theorem erdos_488_of_two_mem_nat (A : Finset ℕ) (n m : ℕ)
    (h0 : 0 ∉ A) (h1 : 1 ∉ A) (h2 : 2 ∈ A)
    (hmax : ∀ a ∈ A, a ≤ n) (hnm : n < m) :
    n * B_card A m < 2 * m * B_card A n := by
  by_cases hall : ∀ a ∈ A, 2 ∣ a
  · have h_eq : ∀ x, multiplesIn A x = multiplesIn {2} x := by
      intro x
      ext k
      simp only [multiplesIn, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨hk, a, haA, hak⟩
        exact ⟨hk, 2, rfl, dvd_trans (hall a haA) hak⟩
      · rintro ⟨hk, _, rfl, h2k⟩
        exact ⟨hk, 2, h2, h2k⟩
    have hn_eq : B_card A n = B_card {2} n := by simp [B_card, h_eq n]
    have hm_eq : B_card A m = B_card {2} m := by simp [B_card, h_eq m]
    rw [hn_eq, hm_eq]
    exact erdos_488_singleton_nat 2 n m (by omega) (hmax 2 h2) hnm
  · push Not at hall
    rcases hall with ⟨b, hbA, hb_ndvd⟩
    have hb_ge : 2 ≤ b := by
      rcases b with _ | _ | b
      · exfalso; exact h0 hbA
      · exfalso; exact h1 hbA
      · omega
    have hbn : b ≤ n := hmax b hbA
    have h_low : n / 2 + 1 ≤ B_card A n := by
      have h_sub : insert b (singleMultiplesIn 2 n) ⊆ multiplesIn A n := by
        intro k hk
        simp only [Finset.mem_insert, singleMultiplesIn, multiplesIn, Finset.mem_filter,
          Finset.mem_Icc] at hk ⊢
        rcases hk with hk_eq | ⟨hk1, h2k⟩
        · subst hk_eq
          exact ⟨⟨by omega, hbn⟩, k, hbA, dvd_rfl⟩
        · exact ⟨hk1, 2, h2, h2k⟩
      have hb_not : b ∉ singleMultiplesIn 2 n := by
        simp [singleMultiplesIn, hb_ndvd]
      have h_card : (insert b (singleMultiplesIn 2 n)).card ≤ B_card A n :=
        Finset.card_le_card h_sub
      rw [Finset.card_insert_of_notMem hb_not, card_singleMultiplesIn] at h_card
      exact h_card
    have h_high : B_card A m ≤ m - 1 := B_card_le_pred A m h1
    have h_high' : B_card A m + 1 ≤ m := by omega
    have h_n_le : n + 1 ≤ 2 * B_card A n := by omega
    nlinarith

/-- **Erdős Problem 488 for Any Set Containing `2` (`2 ∈ A`)** in exact rational form. -/
theorem erdos_488_of_two_mem (A : Finset ℕ) (n m : ℕ)
    (h0 : 0 ∉ A) (h1 : 1 ∉ A) (h2 : 2 ∈ A)
    (hmax : A.max ≤ n) (hnm : n < m) :
    letI B := {k ≥ 1 | ∃ a ∈ A, a ∣ k}
    ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
      2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  have hmax' : ∀ a ∈ A, a ≤ n := by
    intro a ha
    exact WithBot.coe_le_coe.mp (le_trans (Finset.le_max ha) hmax)
  have hn_pos : 0 < n := by
    have := hmax' 2 h2
    omega
  apply rat_div_lt_two_mul_div_of_nat_lt A n m hn_pos (by omega)
  exact erdos_488_of_two_mem_nat A n m h0 h1 h2 hmax' hnm

/-- **High-Half Inductive Step (`erdos_488_insert_gt_half`)**:
If `n / 2 < a ≤ n` and no element of `A` divides `a`, then adding `a` to `A` increases
`B_card A n` by at least `1` (in fact exactly `1`), and increases `B_card A m` by at most `m / a`.
Consequently, if `(n + 1) * B_card A m ≤ 2 * m * B_card A n`, then
`(n + 1) * B_card (insert a A) m ≤ 2 * m * B_card (insert a A) n`. -/
theorem erdos_488_insert_gt_half (A : Finset ℕ) (a n m : ℕ)
    (ha_low : n / 2 < a) (ha_high : a ≤ n)
    (h_ndvd : ∀ b ∈ A, ¬(b ∣ a))
    (h_ih : (n + 1) * B_card A m ≤ 2 * m * B_card A n) :
    (n + 1) * B_card (insert a A) m ≤ 2 * m * B_card (insert a A) n := by
  have h_bn : B_card A n + 1 ≤ B_card (insert a A) n := by
    have h_sub : insert a (multiplesIn A n) ⊆ multiplesIn (insert a A) n := by
      intro k hk
      simp only [Finset.mem_insert, multiplesIn, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      rcases hk with hk_eq | ⟨hk1, b, hbA, hbk⟩
      · subst hk_eq
        exact ⟨⟨by omega, ha_high⟩, k, Or.inl rfl, dvd_rfl⟩
      · exact ⟨hk1, b, Or.inr hbA, hbk⟩
    have ha_not : a ∉ multiplesIn A n := by
      simp only [multiplesIn, Finset.mem_filter, Finset.mem_Icc, not_and, not_exists]
      intro _ b hbA
      exact h_ndvd b hbA
    have h_card : (insert a (multiplesIn A n)).card ≤ B_card (insert a A) n :=
      Finset.card_le_card h_sub
    rw [Finset.card_insert_of_notMem ha_not] at h_card
    exact h_card
  have h_bm : B_card (insert a A) m ≤ B_card A m + m / a := by
    have h_sub : multiplesIn (insert a A) m ⊆ multiplesIn A m ∪ singleMultiplesIn a m := by
      intro k hk
      simp only [multiplesIn, singleMultiplesIn, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_insert, Finset.mem_union] at hk ⊢
      rcases hk with ⟨hk1, b, rfl | hbA, hbk⟩
      · right; exact ⟨hk1, hbk⟩
      · left; exact ⟨hk1, b, hbA, hbk⟩
    calc B_card (insert a A) m
        ≤ (multiplesIn A m ∪ singleMultiplesIn a m).card := Finset.card_le_card h_sub
      _ ≤ B_card A m + (singleMultiplesIn a m).card := Finset.card_union_le _ _
      _ = B_card A m + m / a := by rw [card_singleMultiplesIn]
  have h_step : (n + 1) * (m / a) ≤ 2 * m := by
    have h2a : n + 1 ≤ 2 * a := by omega
    have hma : a * (m / a) ≤ m := Nat.mul_div_le m a
    have : (n + 1) * (m / a) ≤ (2 * a) * (m / a) := Nat.mul_le_mul_right (m / a) h2a
    nlinarith
  nlinarith

/-- The non-multiples of `A` in `[1, x]` (from the misprinted [Er61]/[Er80] problem statement). -/
def nonMultiplesIn (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun k => ∀ a ∈ A, ¬(a ∣ k))

/-- **Disproof of the [Er61]/[Er80] Non-Multiples Formulation (`erdos_488_nonmultiples_false`)**:
In [Er61, p.236] and [Er80, p.112], `B` was misprinted as the set of integers divisible by NO
element of `A`. The minimal counterexample is `A = {2, 3, 5, 7}`, `n = 9`, `m = 13`, for which
`|B ∩ [1, 9]| = 1` (`{1}`) and `|B ∩ [1, 13]| = 3` (`{1, 11, 13}`), so `3 / 13 > 2 * (1 / 9)`. -/
theorem erdos_488_nonmultiples_false :
    ¬ (∀ (A : Finset ℕ), A.Nonempty → 0 ∉ A → 1 ∉ A →
        ∀ (n : ℕ) (m : ℕ), n < m → (∀ a ∈ A, a ≤ n) →
          (nonMultiplesIn A m).card / (m : ℚ) <
            2 * (nonMultiplesIn A n).card / n) := by
  intro h
  have hce := h {2, 3, 5, 7} (by decide) (by decide) (by decide) 9 13 (by decide) (by decide)
  have h9 : (nonMultiplesIn {2, 3, 5, 7} 9).card = 1 := by decide
  have h13 : (nonMultiplesIn {2, 3, 5, 7} 13).card = 3 := by decide
  rw [h9, h13] at hce
  norm_num at hce

end Erdos488

#print axioms Erdos488.erdos_488_singleton
#print axioms Erdos488.erdos_488_sharpness
#print axioms Erdos488.erdos_488_pair
#print axioms Erdos488.erdos_488_of_two_mem
#print axioms Erdos488.erdos_488_insert_gt_half
#print axioms Erdos488.erdos_488_nonmultiples_false
