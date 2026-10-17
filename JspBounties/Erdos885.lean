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
