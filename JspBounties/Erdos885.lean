/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem 885 (JSP-000736)

*References:*
- [erdosproblems.com/885](https://www.erdosproblems.com/885)
- [ErRo97] Erdős, P. and Rosenfeld, M., *The factor-difference set of integers* (1997).
- [Ji99] Jiménez-Urroz, J., *A note on a conjecture of Erdős and Rosenfeld* (1999).
- [Br19] Bremner, A., *On a problem of Erdős related to common factor differences* (2019).

For integer $n \geq 1$ we define the factor difference set of $n$ by
$D(n) = \{|a-b| : n=ab\}$.
Is it true that, for every $k \geq 1$, there exist integers $N_1 < \dots < N_k$ such that
$|\bigcap_i D(N_i)| \geq k$?

We prove the solved cases $k = 1$, $k = 2$ (`erdos_885.variants.k_eq_2`),
$k = 3$ (`erdos_885.variants.k_eq_3`), and $k = 4$ (`erdos_885.variants.k_eq_4`).

Separately, `TwoNumbers.literal_two_numbers` proves the literal JSP-000736
catalog wording: for every k there are TWO distinct positive integers with at
least k common differences. `TwoNumbers.literal_two_number_witnesses` gives
exactly k distinct strictly positive shared differences. This is a different
scope from the k-number conjecture above and does not prove that conjecture.
The new proof iterates rational doubling on y²=x³−36x, proves infinitude by
2-adic valuations, and clears finitely many denominators. No elliptic-rank
or infinitude axiom is assumed.
-/

open Nat Set Finset

namespace Erdos885

/--
For integer $n \geq 1$ we define the factor difference set of $n$ by
$D(n) = \{|a-b| : n=ab\}$.
-/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

lemma mem_factorDifferenceSet_of_eq {n d b : ℕ} (h : n = b * (b + d)) :
    d ∈ factorDifferenceSet n :=
  ⟨b, b + d, h, by push_cast; rw [show (b : ℤ) - (b + d) = -d by ring, abs_neg,
    abs_of_nonneg (by positivity)]⟩

lemma factorDifferenceSet_finite {n : ℕ} (hn : 1 ≤ n) : (factorDifferenceSet n).Finite := by
  refine ((Finset.Iic n).finite_toSet).subset ?_
  rintro d ⟨a, b, rfl, hd⟩
  rw [Finset.mem_coe, Finset.mem_Iic]
  have ha : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hb : 1 ≤ b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have h1 : (a : ℤ) ≤ a * b := by exact_mod_cast Nat.le_mul_of_pos_right a hb
  have h2 : (b : ℤ) ≤ a * b := by exact_mod_cast Nat.le_mul_of_pos_left b ha
  have : (d : ℤ) ≤ a * b := hd ▸ abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  exact_mod_cast this

/--
Erdős and Rosenfeld [ErRo97] proved this is true for $k=2$.
-/
theorem erdos_885.variants.k_eq_2 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 2 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2 := by
  refine ⟨{65984625, 508032000}, by simp, by decide, ?_⟩
  have hsub : (↑({5040, 27720} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({65984625, 508032000} : Finset ℕ),
        factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl) <;> rcases hd with rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 5985) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2205) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 20160) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 12600) (by norm_num)]
  have hfin : (⋂ n ∈ ({65984625, 508032000} : Finset ℕ),
      factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 65984625)).subset
      (Set.iInter₂_subset 65984625 (by simp))
  calc 2 = (↑({5040, 27720} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

/--
Jiménez-Urroz [Ji99] proved this for $k=3$.
-/
theorem erdos_885.variants.k_eq_3 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3 := by
  refine ⟨{65984625, 508032000, 1578963456}, by simp, by decide, ?_⟩
  have hsub : (↑({5040, 27720, 68880} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({65984625, 508032000, 1578963456} : Finset ℕ),
        factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 5985) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2205) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 945) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 20160) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 12600) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 6720) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 37296) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 28224) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 18144) (by norm_num)]
  have hfin : (⋂ n ∈ ({65984625, 508032000, 1578963456} : Finset ℕ),
      factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 65984625)).subset
      (Set.iInter₂_subset 65984625 (by simp))
  calc 3 = (↑({5040, 27720, 68880} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

/--
Bremner [Br19] proved this for $k=4$.
-/
theorem erdos_885.variants.k_eq_4 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 4 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 := by
  refine ⟨{65984625, 508032000, 1578963456, 2505664000}, by simp, by decide, ?_⟩
  have hsub : (↑({5040, 27720, 68880, 164976} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({65984625, 508032000, 1578963456, 2505664000} : Finset ℕ),
        factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 5985) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2205) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 945) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 399) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 20160) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 12600) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 6720) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 3024) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 37296) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 28224) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 18144) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 9072) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 47600) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 38080) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 26320) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 14000) (by norm_num)]
  have hfin : (⋂ n ∈ ({65984625, 508032000, 1578963456, 2505664000} : Finset ℕ),
      factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 65984625)).subset
      (Set.iInter₂_subset 65984625 (by simp))
  calc 4 = (↑({5040, 27720, 68880, 164976} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms erdos_885.variants.k_eq_2
#print axioms erdos_885.variants.k_eq_3
#print axioms erdos_885.variants.k_eq_4

end Erdos885

namespace Erdos885.TwoNumbers

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

lemma val_two : padicValRat 2 (2 : ℚ) = 1 := by
  exact padicValRat.self (by decide)
lemma val_four : padicValRat 2 (4 : ℚ) = 2 := by
  have h := padicValRat.pow (p := 2) (2 : ℚ) (k := 2)
  norm_num [val_two] at h ⊢
  exact h
lemma val_thirtysix : padicValRat 2 (36 : ℚ) = 2 := by
  decide +kernel

/-- A positive point of the congruent-number curve with negative 2-adic x valuation. -/
structure Point where
  x : ℚ
  y : ℚ
  x_gt : 6 < x
  equation : y^2 = x^3 - 36*x
  val_negative : padicValRat 2 x < 0

lemma x_ne_zero (P : Point) : P.x ≠ 0 := by linarith [P.x_gt]
lemma y_ne_zero (P : Point) : P.y ≠ 0 := by
  intro h
  have hx := P.x_gt
  have he := P.equation
  rw [h] at he
  have hxx : 0 < P.x^2-36 := by nlinarith
  have hp : 0 < P.x*(P.x^2-36) := mul_pos (by linarith) hxx
  nlinarith

noncomputable def doubleX (P : Point) : ℚ := (P.x^2+36)^2 / (4*P.y^2)
noncomputable def doubleY (P : Point) : ℚ :=
  (3*P.x^2-36)/(2*P.y) * (P.x-doubleX P) - P.y

lemma double_curve (P : Point) : (doubleY P)^2 = (doubleX P)^3 - 36*doubleX P := by
  have hy := y_ne_zero P
  have he := P.equation
  unfold doubleY doubleX
  field_simp
  ring_nf
  simp only [show P.y ^ 4 = (P.y ^ 2) ^ 2 by ring,
    show P.y ^ 6 = (P.y ^ 2) ^ 3 by ring,
    show P.y ^ 8 = (P.y ^ 2) ^ 4 by ring, he]
  ring

lemma doubleX_val (P : Point) : padicValRat 2 (doubleX P) =
    4*padicValRat 2 P.x - 2*padicValRat 2 P.y - 2 := by
  have hx := x_ne_zero P
  have hy := y_ne_zero P
  have hnum : P.x^2+36 ≠ 0 := by positivity
  have hvnum : padicValRat 2 (P.x^2+36) = 2*padicValRat 2 P.x := by
    rw [padicValRat.add_eq_of_lt hnum (pow_ne_zero _ hx) (by norm_num)]
    · simp [padicValRat.pow]
    · simp [padicValRat.pow, val_thirtysix]
      linarith [P.val_negative]
  rw [doubleX,padicValRat.div (pow_ne_zero _ hnum)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hy)),padicValRat.pow,
    padicValRat.mul (by norm_num) (pow_ne_zero _ hy),val_four,padicValRat.pow,hvnum]
  ring

lemma curve_valuation (P : Point) : 2*padicValRat 2 P.y = 3*padicValRat 2 P.x := by
  have hx := x_ne_zero P
  have hy := y_ne_zero P
  have hprod : (36 : ℚ)*P.x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hdiff : P.x^3 + -(36*P.x) ≠ 0 := by
    rw [← sub_eq_add_neg,← P.equation]
    exact pow_ne_zero _ hy
  have hval : padicValRat 2 (P.x^3 + -(36*P.x)) = 3*padicValRat 2 P.x := by
    rw [padicValRat.add_eq_of_lt hdiff (pow_ne_zero _ hx) (neg_ne_zero.mpr hprod)]
    · simp [padicValRat.pow]
    · rw [padicValRat.pow,padicValRat.neg,padicValRat.mul (by norm_num) hx,val_thirtysix]
      norm_num only [Nat.cast_ofNat] at *
      linarith [P.val_negative]
  rw [← sub_eq_add_neg,← P.equation,padicValRat.pow] at hval
  exact hval

lemma doubled_valuation (P : Point) : padicValRat 2 (doubleX P) = padicValRat 2 P.x-2 := by
  rw [doubleX_val]
  linarith [curve_valuation P]

lemma doubleX_gt (P : Point) : 6 < doubleX P := by
  have hy := y_ne_zero P
  have hden : 0 < 4*P.y^2 := by positivity
  have hsq : (P.x^2-12*P.x-36)^2 =
      (P.x^2+36)^2 - 24*P.y^2 := by rw [P.equation]; ring
  have hge : 6 ≤ doubleX P := by
    unfold doubleX
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg (P.x^2-12*P.x-36)]
  have h6 : padicValRat 2 (6 : ℚ)=1 := by decide +kernel
  have hne : doubleX P ≠ 6 := by
    intro h
    have hv := doubled_valuation P
    rw [h,h6] at hv
    linarith [P.val_negative]
  exact lt_of_le_of_ne hge hne.symm

noncomputable def double (P : Point) : Point where
  x := doubleX P
  y := doubleY P
  x_gt := doubleX_gt P
  equation := double_curve P
  val_negative := by rw [doubled_valuation]; linarith [P.val_negative]

noncomputable def seed : Point where
  x := 25/4
  y := 35/8
  x_gt := by norm_num
  equation := by norm_num
  val_negative := by decide +kernel

noncomputable def points : ℕ → Point
 | 0 => seed
 | n+1 => double (points n)

lemma points_valuation (n : ℕ) : padicValRat 2 (points n).x = -2*(n+1) := by
  induction n with
  | zero => change padicValRat 2 (25/4 : ℚ) = -2; decide +kernel
  | succ n ih =>
    change padicValRat 2 (doubleX (points n)) = _
    rw [doubled_valuation,ih]
    push_cast
    ring

noncomputable def u (P : Point) : ℚ := (P.x^2-12*P.x-36)/(2*P.y)
noncomputable def v (P : Point) : ℚ := (P.x^2+36)/(2*P.y)
noncomputable def w (P : Point) : ℚ := (P.x^2+12*P.x-36)/(2*P.y)

lemma offsets (P : Point) : (v P)^2-(u P)^2=6 ∧ (w P)^2-(u P)^2=12 := by
  have hy := y_ne_zero P
  constructor
  · unfold v u
    field_simp
    rw [P.equation]
    ring
  · unfold w u
    field_simp
    rw [P.equation]
    ring

lemma u_val_relation (P : Point) :
    2*padicValRat 2 (u P) = padicValRat 2 P.x-2 := by
  have hx := x_ne_zero P
  have hy := y_ne_zero P
  have h12 : padicValRat 2 (12 : ℚ)=2 := by decide +kernel
  have hnum1 : P.x^2+-(12*P.x) ≠ 0 := by
    intro he
    have heq : P.x=12 := by nlinarith [P.x_gt]
    have h := P.val_negative
    rw [heq,h12] at h
    omega
  have hval1 : padicValRat 2 (P.x^2+-(12*P.x))=2*padicValRat 2 P.x := by
    rw [padicValRat.add_eq_of_lt hnum1 (pow_ne_zero _ hx)
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hx))]
    · simp
    · rw [padicValRat.pow,padicValRat.neg,padicValRat.mul (by norm_num) hx,h12]
      norm_num only [Nat.cast_ofNat] at *
      linarith [P.val_negative]
  have hnum : P.x^2-12*P.x-36 ≠ 0 := by
    intro he
    have heq : P.x^2+-(12*P.x)=36 := by linarith
    rw [heq,val_thirtysix] at hval1
    linarith [P.val_negative]
  have hvnum : padicValRat 2 (P.x^2-12*P.x-36)=2*padicValRat 2 P.x := by
    rw [sub_eq_add_neg,sub_eq_add_neg]
    rw [padicValRat.add_eq_of_lt (by simpa [sub_eq_add_neg] using hnum) hnum1
      (by norm_num),hval1]
    rw [hval1,padicValRat.neg,val_thirtysix]
    linarith [P.val_negative]
  unfold u
  rw [padicValRat.div hnum (mul_ne_zero (by norm_num) hy),
    padicValRat.mul (by norm_num) hy,val_two,hvnum]
  linarith [curve_valuation P]

lemma u_points_injective : Function.Injective (fun n => |u (points n)|) := by
  intro n m h
  dsimp only at h
  have he : padicValRat 2 (u (points n))=padicValRat 2 (u (points m)) := by
    have hn : padicValRat 2 |u (points n)|=padicValRat 2 (u (points n)) := by
      rcases le_or_gt 0 (u (points n)) with H|H
      · rw [abs_of_nonneg H]
      · rw [abs_of_neg H,padicValRat.neg]
    have hm : padicValRat 2 |u (points m)|=padicValRat 2 (u (points m)) := by
      rcases le_or_gt 0 (u (points m)) with H|H
      · rw [abs_of_nonneg H]
      · rw [abs_of_neg H,padicValRat.neg]
    rw [← hn,← hm,h]
  have hn := u_val_relation (points n)
  have hm := u_val_relation (points m)
  rw [points_valuation] at hn hm
  omega

end Erdos885.TwoNumbers

namespace Erdos885.TwoNumbers

lemma scaled_abs_integer (q : ℚ) {L : ℕ} (hL : 0 < L) (hd : q.den ∣ L) :
    ∃ a : ℕ, (a : ℚ) = (L : ℚ) * |q| := by
  obtain ⟨t, ht⟩ := hd
  have hq : (q.den : ℚ) * q = q.num := by
    have hh := q.num_div_den
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    calc (q.den : ℚ) * q = q * q.den := mul_comm _ _
      _ = q.num := ((div_eq_iff hden).mp hh).symm
  have hz : ((t : ℤ) * q.num : ℚ) = (L : ℚ) * q := by
    push_cast
    rw [ht]
    push_cast
    rw [← hq]
    ring
  refine ⟨((t : ℤ) * q.num).natAbs, ?_⟩
  rw [Nat.cast_natAbs]
  have habs := congrArg abs hz
  simpa only [Int.cast_mul, Int.cast_abs, abs_mul, abs_of_nonneg (show (0 : ℚ) ≤ L by positivity)]
    using habs

lemma nat_factor_difference_of_squares {U V N : ℕ}
    (he : (V : ℚ)^2 - (U : ℚ)^2 = N) (hN : 0 < N) :
    2 * U ∈ Erdos885.factorDifferenceSet N := by
  have hUV : U ≤ V := by
    have hn : (0 : ℚ) < N := by exact_mod_cast hN
    have hU : (0 : ℚ) ≤ U := by positivity
    have hV : (0 : ℚ) ≤ V := by positivity
    have : (U : ℚ) ≤ V := by nlinarith
    exact_mod_cast this
  refine ⟨V - U, V + U, ?_, ?_⟩
  · have : (N : ℚ) = (V - U : ℕ) * (V + U : ℕ) := by
      rw [Nat.cast_sub hUV, Nat.cast_add]
      nlinarith [he]
    exact_mod_cast this
  · rw [Nat.cast_sub hUV, Nat.cast_add]
    push_cast
    rw [show (V : ℤ) - U - (V + U) = -(2 * U) by ring, abs_neg,
      abs_of_nonneg (by positivity)]

/-- The literal two-number statement. It does not assert the k-number Erdős conjecture. -/
theorem literal_two_number_witnesses (k : ℕ) :
    ∃ (N M : ℕ) (D : Finset ℕ), 0 < N ∧ N < M ∧ D.card = k ∧
      ∀ d ∈ D, 0 < d ∧ d ∈ Erdos885.factorDifferenceSet N ∩
        Erdos885.factorDifferenceSet M := by
  classical
  let q : Fin k × Fin 3 → ℚ := fun ij =>
    if ij.2 = 0 then u (points ij.1) else
    if ij.2 = 1 then v (points ij.1) else w (points ij.1)
  let L : ℕ := ∏ ij : Fin k × Fin 3, (q ij).den
  have hL : 0 < L := Finset.prod_pos (fun ij _ => Rat.den_pos (q ij))
  have hd (ij : Fin k × Fin 3) : (q ij).den ∣ L :=
    Finset.dvd_prod_of_mem (fun ij => (q ij).den) (Finset.mem_univ ij)
  have hu (i : Fin k) : ∃ a : ℕ, (a : ℚ) = (L : ℚ) * |u (points i)| := by
    simpa [q] using scaled_abs_integer (q (i, 0)) hL (hd (i, 0))
  have hv (i : Fin k) : ∃ a : ℕ, (a : ℚ) = (L : ℚ) * |v (points i)| := by
    simpa [q] using scaled_abs_integer (q (i, 1)) hL (hd (i, 1))
  have hw (i : Fin k) : ∃ a : ℕ, (a : ℚ) = (L : ℚ) * |w (points i)| := by
    simpa [q] using scaled_abs_integer (q (i, 2)) hL (hd (i, 2))
  choose U hU using hu
  choose V hV using hv
  choose W hW using hw
  have heV (i : Fin k) : (V i : ℚ)^2 - (U i : ℚ)^2 = (6 * L^2 : ℕ) := by
    rw [hV, hU]
    push_cast
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
    nlinarith [(offsets (points i)).1]
  have heW (i : Fin k) : (W i : ℚ)^2 - (U i : ℚ)^2 = (12 * L^2 : ℕ) := by
    rw [hW, hU]
    push_cast
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
    nlinarith [(offsets (points i)).2]
  have hinj : Function.Injective (fun i : Fin k => 2 * U i) := by
    intro i j hij
    dsimp only at hij
    have hui : U i = U j := by omega
    have heq : |u (points i)| = |u (points j)| := by
      apply mul_left_cancel₀ (show (L : ℚ) ≠ 0 by positivity)
      rw [← hU, ← hU, hui]
    exact Fin.ext (u_points_injective heq)
  let D : Finset ℕ := Finset.univ.image (fun i : Fin k => 2 * U i)
  have hcard : D.card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hN : 0 < 6 * L^2 := by positivity
  have hM : 0 < 12 * L^2 := by positivity
  have hsub : (D : Set ℕ) ⊆
      Erdos885.factorDifferenceSet (6 * L^2) ∩ Erdos885.factorDifferenceSet (12 * L^2) := by
    intro d hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨nat_factor_difference_of_squares (heV i) hN,
      nat_factor_difference_of_squares (heW i) hM⟩
  refine ⟨6 * L^2, 12 * L^2, D, hN, by nlinarith [sq_pos_of_pos hL], hcard, ?_⟩
  intro d hd
  refine ⟨?_, hsub hd⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  have hun : u (points i) ≠ 0 := by
    intro hz
    have hh := u_val_relation (points i)
    rw [hz, padicValRat.zero] at hh
    linarith [(points i).val_negative]
  have hp : (0 : ℚ) < U i := by
    rw [hU]
    exact mul_pos (by exact_mod_cast hL) (abs_pos.mpr hun)
  have : 0 < U i := by exact_mod_cast hp
  omega

/-- Two distinct positive integers have arbitrarily many common factor differences.
This theorem is the literal JSP736 wording, not the k-number Erdős885 conjecture. -/
theorem literal_two_numbers (k : ℕ) :
    ∃ N M : ℕ, 0 < N ∧ N < M ∧
      k ≤ (Erdos885.factorDifferenceSet N ∩ Erdos885.factorDifferenceSet M).ncard := by
  obtain ⟨N, M, D, hN, hNM, hcard, hD⟩ := literal_two_number_witnesses k
  refine ⟨N, M, hN, hNM, ?_⟩
  rw [← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun d hd => (hD d hd).2)
    ((Erdos885.factorDifferenceSet_finite hN).subset Set.inter_subset_left)

#print axioms literal_two_number_witnesses
#print axioms literal_two_numbers
end Erdos885.TwoNumbers
