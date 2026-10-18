/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Update
import Mathlib.Data.Nat.Fib.Basic

open scoped Classical

variable {M : Type*} [AddCommMonoid M]

/-- The set of subset sums of a sequence `ℕ → M`, where repetition is allowed. -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

variable [Preorder M]

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
(not necessarily distinct) terms of `A`. -/
def IsAddCompleteNatSeq' (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

namespace Erdos348

open Finset

def erdos_348.answer : Set (ℕ × ℕ) := {(m, n) : ℕ × ℕ | m < n ∧ m ≤ 1}

/-! ### Basic properties of `Function.updateFinset` and `subseqSums'` -/

lemma updateFinset_zero_apply (a : ℕ → ℕ) (s : Finset ℕ) (i : ℕ) :
    Function.updateFinset a s 0 i = if i ∈ s then 0 else a i := by
  simp only [Function.updateFinset]
  split_ifs <;> rfl

lemma sum_updateFinset_zero_eq_sum_sdiff (a : ℕ → ℕ) (s B : Finset ℕ) :
    ∑ i ∈ B, Function.updateFinset a s 0 i = ∑ i ∈ B \ s, a i := by
  rw [← sum_sdiff (sdiff_subset : B \ s ⊆ B)]
  have h1 : ∑ i ∈ B \ (B \ s), Function.updateFinset a s 0 i = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [mem_sdiff, mem_sdiff, not_and, Classical.not_not] at hi
    rw [updateFinset_zero_apply, if_pos (hi.2 hi.1)]
  have h2 : ∑ i ∈ B \ s, Function.updateFinset a s 0 i = ∑ i ∈ B \ s, a i := by
    apply sum_congr rfl
    intro i hi
    rw [mem_sdiff] at hi
    rw [updateFinset_zero_apply, if_neg hi.2]
  omega

lemma mem_subseqSums'_updateFinset_iff (a : ℕ → ℕ) (s : Finset ℕ) (x : ℕ) :
    x ∈ subseqSums' (Function.updateFinset a s 0) ↔
      ∃ B : Finset ℕ, Disjoint B s ∧ x = ∑ i ∈ B, a i := by
  constructor
  · rintro ⟨B, rfl⟩
    refine ⟨B \ s, disjoint_sdiff_self_left, ?_⟩
    exact sum_updateFinset_zero_eq_sum_sdiff a s B
  · rintro ⟨B, hBs, rfl⟩
    refine ⟨B, ?_⟩
    rw [sum_updateFinset_zero_eq_sum_sdiff, sdiff_eq_self_of_disjoint hBs]

lemma subseqSums'_updateFinset_mono {a : ℕ → ℕ} {s t : Finset ℕ} (hst : s ⊆ t) :
    subseqSums' (Function.updateFinset a t 0) ⊆ subseqSums' (Function.updateFinset a s 0) := by
  intro x hx
  rw [mem_subseqSums'_updateFinset_iff] at hx ⊢
  rcases hx with ⟨B, hBt, rfl⟩
  exact ⟨B, Disjoint.mono_right hst hBt, rfl⟩

lemma isAddCompleteNatSeq'_updateFinset_mono {a : ℕ → ℕ} {s t : Finset ℕ} (hst : s ⊆ t)
    (h : IsAddCompleteNatSeq' (Function.updateFinset a t 0)) :
    IsAddCompleteNatSeq' (Function.updateFinset a s 0) := by
  filter_upwards [h] with x hx
  exact subseqSums'_updateFinset_mono hst hx

lemma isAddCompleteNatSeq'_iff (A : ℕ → ℕ) :
    IsAddCompleteNatSeq' A ↔ ∃ T : ℕ, ∀ x ≥ T, x ∈ subseqSums' A := by
  simp [IsAddCompleteNatSeq', Filter.eventually_atTop]

/-! ### Section 3A: Existence for `m = 0` (Powers of Two) -/

lemma pow_two_sum_range (k : ℕ) : ∑ i ∈ range k, 2 ^ i + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ]
    omega

lemma pow_two_repr (n : ℕ) :
    ∀ x < 2 ^ n, ∃ B ⊆ range n, x = ∑ i ∈ B, 2 ^ i := by
  induction n with
  | zero =>
    intro x hx
    have : x = 0 := by omega
    subst this
    exact ⟨∅, empty_subset _, by simp⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    by_cases hlt : x < 2 ^ n
    · rcases ih x hlt with ⟨B, hB, rfl⟩
      exact ⟨B, Subset.trans hB (range_mono (Nat.le_succ n)), rfl⟩
    · have hsub : x - 2 ^ n < 2 ^ n := by omega
      rcases ih (x - 2 ^ n) hsub with ⟨B, hB, hsum⟩
      refine ⟨insert n B, ?_, ?_⟩
      · intro idx hidx
        rw [mem_range]
        rcases mem_insert.mp hidx with h_eq | hidxB
        · omega
        · have := mem_range.mp (hB hidxB)
          omega
      · have hnB : n ∉ B := fun hn => by
          have := mem_range.mp (hB hn)
          omega
        rw [sum_insert hnB, ← hsum]
        omega

lemma pow_two_complete_zero (s : Finset ℕ) (hs : s.card = 0) :
    IsAddCompleteNatSeq' (Function.updateFinset (fun i => 2 ^ i) s 0) := by
  rw [card_eq_zero.mp hs, Function.updateFinset_empty, isAddCompleteNatSeq'_iff]
  refine ⟨0, fun x _ => ?_⟩
  have hx : x < 2 ^ x := Nat.lt_two_pow_self
  rcases pow_two_repr x x hx with ⟨B, _, hsum⟩
  exact ⟨B, hsum⟩

lemma pow_two_dvd_sum_filter_gt (B : Finset ℕ) (j : ℕ) :
    ∃ k, ∑ i ∈ B.filter (fun i => j < i), 2 ^ i = 2 ^ (j + 1) * k := by
  induction B using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    rcases ih with ⟨k, hk⟩
    rw [filter_insert]
    split_ifs with hja
    · refine ⟨2 ^ (a - (j + 1)) + k, ?_⟩
      have ha_notin : a ∉ s.filter (fun i => j < i) := fun h => ha (mem_filter.mp h).1
      rw [sum_insert ha_notin, hk, Nat.mul_add, ← pow_add]
      congr 2
      omega
    · exact ⟨k, hk⟩

lemma pow_two_not_complete_of_nonempty (t : Finset ℕ) (ht : t.Nonempty) :
    ¬IsAddCompleteNatSeq' (Function.updateFinset (fun i => 2 ^ i) t 0) := by
  rcases ht with ⟨j, hj⟩
  rw [isAddCompleteNatSeq'_iff]
  rintro ⟨T, hT⟩
  let x := 2 ^ (j + 1) * T + 2 ^ j
  have hxT : T ≤ x := by
    have h1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow (j + 1) 2 (by omega)
    have h2 : 1 * T ≤ 2 ^ (j + 1) * T := Nat.mul_le_mul_right T h1
    omega
  have hx := hT x hxT
  rw [mem_subseqSums'_updateFinset_iff] at hx
  rcases hx with ⟨B, hBt, hsum⟩
  have hjB : j ∉ B := Finset.disjoint_right.mp hBt hj
  let B₁ := B.filter (fun i => i < j)
  let B₂ := B.filter (fun i => j < i)
  have hB_union : B = B₁ ∪ B₂ := by
    ext i
    simp only [B₁, B₂, mem_union, mem_filter]
    constructor
    · intro hi
      have hij : i ≠ j := fun h => hjB (h ▸ hi)
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · exact Or.inl ⟨hi, hlt⟩
      · exact Or.inr ⟨hi, hgt⟩
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  have hB_disj : Disjoint B₁ B₂ := by
    rw [disjoint_filter]
    intro i _ h1 h2
    omega
  rw [hB_union, sum_union hB_disj] at hsum
  have hB₁_sub : B₁ ⊆ range j := by
    intro i hi
    rw [mem_range]
    exact (mem_filter.mp hi).2
  have hB₁_le : ∑ i ∈ B₁, 2 ^ i < 2 ^ j := by
    have hle := sum_le_sum_of_subset (f := fun i => 2 ^ i) hB₁_sub
    have hpow := pow_two_sum_range j
    omega
  rcases pow_two_dvd_sum_filter_gt B j with ⟨k, hk⟩
  change ∑ i ∈ B₂, 2 ^ i = 2 ^ (j + 1) * k at hk
  have hpow_succ : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by
    rw [pow_succ]
    omega
  rcases le_or_gt k T with hkT | hkT
  · have hmul : 2 ^ (j + 1) * k ≤ 2 ^ (j + 1) * T := Nat.mul_le_mul_left _ hkT
    dsimp [x] at hsum
    omega
  · have hmul : 2 ^ (j + 1) * (T + 1) ≤ 2 ^ (j + 1) * k := Nat.mul_le_mul_left _ hkT
    rw [Nat.mul_add, Nat.mul_one] at hmul
    dsimp [x] at hsum
    omega

theorem exists_for_m_eq_zero {n : ℕ} (hn : 0 < n) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ s : Finset ℕ, s.card = 0 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
      (∀ t : Finset ℕ, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) := by
  refine ⟨fun i => 2 ^ i, fun i j hij => Nat.pow_le_pow_right (by omega) hij,
    pow_two_complete_zero, fun t ht => ?_⟩
  apply pow_two_not_complete_of_nonempty t
  rw [← card_pos]
  omega

/-! ### Section 3B: Existence for `m = 1` (Fibonacci Sequence) -/

def fibSeq (i : ℕ) : ℕ := Nat.fib (i + 1)

lemma fibSeq_mono : Monotone fibSeq :=
  fun i j hij => Nat.fib_mono (by omega)

lemma fibSeq_pos (i : ℕ) : 1 ≤ fibSeq i :=
  Nat.fib_pos.mpr (by omega)

lemma fibSeq_zero : fibSeq 0 = 1 := rfl
lemma fibSeq_one : fibSeq 1 = 1 := rfl

lemma fibSeq_add_two (i : ℕ) : fibSeq (i + 1 + 1) = fibSeq i + fibSeq (i + 1) := by
  dsimp [fibSeq]
  rw [Nat.fib_add_two]

lemma fibSeq_sum_range (k : ℕ) : ∑ i ∈ range k, fibSeq i + 1 = fibSeq (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sum_range_succ, fibSeq_add_two]
    omega

lemma fibSeq_ge_index (k : ℕ) : k ≤ fibSeq (k + 1) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [fibSeq_add_two]
    have := fibSeq_pos k
    omega

lemma fibSeq_one_del_step (j k : ℕ) :
    Function.updateFinset fibSeq {j} 0 k ≤
      (∑ i ∈ range k, Function.updateFinset fibSeq {j} 0 i) + 1 := by
  rw [sum_updateFinset_zero_eq_sum_sdiff, updateFinset_zero_apply]
  simp only [mem_singleton]
  by_cases hkj : k = j
  · rw [if_pos hkj]
    omega
  · rw [if_neg hkj]
    by_cases hlt : k < j
    · have hsdiff : range k \ {j} = range k := by
        rw [Finset.sdiff_eq_self_iff_disjoint, disjoint_singleton_right, mem_range]
        omega
      rw [hsdiff, fibSeq_sum_range k]
      exact fibSeq_mono (by omega)
    · have hj_lt : j < k := by omega
      have hj_mem : j ∈ range k := mem_range.mpr hj_lt
      have hsdiff : range k \ {j} = (range k).erase j := (erase_eq (range k) j).symm
      rw [hsdiff]
      have herase := add_sum_erase (range k) fibSeq hj_mem
      have hsum := fibSeq_sum_range k
      obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
      have hadd := fibSeq_add_two d
      have hle : fibSeq j ≤ fibSeq d := fibSeq_mono (by omega)
      omega

lemma fibSeq_one_del_repr (j k : ℕ) :
    ∀ x ≤ ∑ i ∈ range k, Function.updateFinset fibSeq {j} 0 i,
      ∃ B ⊆ range k, x = ∑ i ∈ B, Function.updateFinset fibSeq {j} 0 i := by
  induction k with
  | zero =>
    intro x hx
    simp only [range_zero, sum_empty, nonpos_iff_eq_zero] at hx
    subst hx
    exact ⟨∅, empty_subset _, by simp⟩
  | succ k ih =>
    intro x hx
    rw [sum_range_succ] at hx
    let S := ∑ i ∈ range k, Function.updateFinset fibSeq {j} 0 i
    let c := Function.updateFinset fibSeq {j} 0 k
    by_cases hle : x ≤ S
    · rcases ih x hle with ⟨B, hB, rfl⟩
      exact ⟨B, Subset.trans hB (range_mono (Nat.le_succ k)), rfl⟩
    · have hstep : c ≤ S + 1 := fibSeq_one_del_step j k
      have hsub : x - c ≤ S := by omega
      rcases ih (x - c) hsub with ⟨B, hB, hsum⟩
      refine ⟨insert k B, ?_, ?_⟩
      · intro idx hidx
        rw [mem_range]
        rcases mem_insert.mp hidx with h_eq | hidxB
        · omega
        · have := mem_range.mp (hB hidxB)
          omega
      · have hkB : k ∉ B := fun hk => by
          have := mem_range.mp (hB hk)
          omega
        rw [sum_insert hkB, ← hsum]
        omega

lemma fibSeq_complete_one (s : Finset ℕ) (hs : s.card = 1) :
    IsAddCompleteNatSeq' (Function.updateFinset fibSeq s 0) := by
  rcases card_eq_one.mp hs with ⟨j, rfl⟩
  rw [isAddCompleteNatSeq'_iff]
  refine ⟨0, fun x _ => ?_⟩
  let k := x + fibSeq j + j + 2
  have hjm : j < k := by omega
  have hsum_ge : x ≤ ∑ i ∈ range k, Function.updateFinset fibSeq {j} 0 i := by
    rw [sum_updateFinset_zero_eq_sum_sdiff]
    have hsdiff : range k \ {j} = (range k).erase j := (erase_eq (range k) j).symm
    rw [hsdiff]
    have herase := add_sum_erase (range k) fibSeq (mem_range.mpr hjm)
    have hsum := fibSeq_sum_range k
    have hge := fibSeq_ge_index k
    omega
  rcases fibSeq_one_del_repr j k x hsum_ge with ⟨B, _, hBsum⟩
  exact ⟨B, hBsum⟩

lemma sum_sdiff_pair {a : ℕ → ℕ} {k i j : ℕ} (hij : i < j) (hjk : j < k) :
    ∑ r ∈ range k \ {i, j}, a r + a i + a j = ∑ r ∈ range k, a r := by
  have hi : i ∈ range k := mem_range.mpr (Nat.lt_trans hij hjk)
  have hj : j ∈ (range k).erase i := mem_erase.mpr ⟨by omega, mem_range.mpr hjk⟩
  have hset : range k \ {i, j} = ((range k).erase i).erase j := by
    ext r
    simp only [mem_sdiff, mem_insert, mem_singleton, mem_erase]
    tauto
  rw [hset]
  have e1 := add_sum_erase (range k) a hi
  have e2 := add_sum_erase ((range k).erase i) a hj
  omega

lemma fibSeq_two_del_missing {i j : ℕ} (hij : i < j) (m : ℕ) :
    fibSeq (j + 2 * m + 1) - 1 ∉ subseqSums' (Function.updateFinset fibSeq {i, j} 0) := by
  induction m with
  | zero =>
    rw [Nat.mul_zero, Nat.add_zero, mem_subseqSums'_updateFinset_iff]
    rintro ⟨B, hBdisj, hsum⟩
    have hBsub : B ⊆ range (j + 1) \ {i, j} := by
      intro r hr
      rw [mem_sdiff, mem_range]
      refine ⟨?_, Finset.disjoint_left.mp hBdisj hr⟩
      by_contra hge
      have hle : fibSeq r ≤ fibSeq (j + 1) - 1 := by
        rw [hsum]
        exact single_le_sum (fun _ _ => Nat.zero_le _) hr
      have hmono : fibSeq (j + 1) ≤ fibSeq r := fibSeq_mono (by omega)
      have hpos := fibSeq_pos (j + 1)
      omega
    have hle := sum_le_sum_of_subset (f := fibSeq) hBsub
    have hpair := sum_sdiff_pair (a := fibSeq) (k := j + 1) hij (by omega : j < j + 1)
    have htot := fibSeq_sum_range (j + 1)
    have hadd := fibSeq_add_two j
    have hipos := fibSeq_pos i
    omega
  | succ m ih =>
    rw [mem_subseqSums'_updateFinset_iff]
    rintro ⟨B, hBdisj, hsum⟩
    let s := j + 2 * m + 2
    have htarget : j + 2 * (m + 1) + 1 = s + 1 := by omega
    rw [htarget] at hsum
    have hBsub : B ⊆ range (s + 1) \ {i, j} := by
      intro r hr
      rw [mem_sdiff, mem_range]
      refine ⟨?_, Finset.disjoint_left.mp hBdisj hr⟩
      by_contra hge
      have hle : fibSeq r ≤ fibSeq (s + 1) - 1 := by
        rw [hsum]
        exact single_le_sum (fun _ _ => Nat.zero_le _) hr
      have hmono : fibSeq (s + 1) ≤ fibSeq r := fibSeq_mono (by omega)
      have hpos := fibSeq_pos (s + 1)
      omega
    by_cases hsB : s ∈ B
    · apply ih
      rw [mem_subseqSums'_updateFinset_iff]
      refine ⟨B.erase s, Disjoint.mono_left (erase_subset s B) hBdisj, ?_⟩
      have herase := add_sum_erase B fibSeq hsB
      have hadd : fibSeq (s + 1) = fibSeq (j + 2 * m + 1) + fibSeq s := by
        exact fibSeq_add_two (j + 2 * m + 1)
      have hpos := fibSeq_pos (j + 2 * m + 1)
      omega
    · have hBsub' : B ⊆ range s \ {i, j} := by
        intro r hr
        have hr1 := hBsub hr
        rw [mem_sdiff, mem_range] at hr1 ⊢
        have : r ≠ s := fun h => hsB (h ▸ hr)
        exact ⟨by omega, hr1.2⟩
      have hle := sum_le_sum_of_subset (f := fibSeq) hBsub'
      have hpair := sum_sdiff_pair (a := fibSeq) hij (by omega : j < s)
      have htot := fibSeq_sum_range s
      have hipos := fibSeq_pos i
      have hjpos := fibSeq_pos j
      omega

theorem exists_for_m_eq_one {n : ℕ} (hn : 2 ≤ n) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ s : Finset ℕ, s.card = 1 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
      (∀ t : Finset ℕ, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) := by
  refine ⟨fibSeq, fibSeq_mono, fibSeq_complete_one, fun t ht hcomp => ?_⟩
  have ht2 : 1 < t.card := by omega
  rcases one_lt_card.mp ht2 with ⟨u, hu, v, hv, huv⟩
  have hpair : ∃ i ∈ t, ∃ j ∈ t, i < j := by
    rcases lt_trichotomy u v with hlt | rfl | hgt
    · exact ⟨u, hu, v, hv, hlt⟩
    · exact absurd rfl huv
    · exact ⟨v, hv, u, hu, hgt⟩
  rcases hpair with ⟨i, hi, j, hj, hij⟩
  have hsub : ({i, j} : Finset ℕ) ⊆ t := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hi
    · rw [mem_singleton.mp hr]
      exact hj
  have hcomp2 := isAddCompleteNatSeq'_updateFinset_mono hsub hcomp
  rw [isAddCompleteNatSeq'_iff] at hcomp2
  rcases hcomp2 with ⟨T, hT⟩
  have hge : T ≤ fibSeq (j + 2 * T + 1) - 1 := by
    have := fibSeq_ge_index (j + 2 * T)
    omega
  exact fibSeq_two_del_missing hij T (hT _ hge)

/-! ### Section 4: Central Intervals from Diverging Slack (`thm:central`) -/

def prefixSum (B : ℕ → ℕ) (N : ℕ) : ℕ := ∑ i ∈ range N, B i

def prefixSums (B : ℕ → ℕ) (N : ℕ) : Set ℕ :=
  {x | ∃ s ⊆ range N, x = ∑ i ∈ s, B i}

lemma prefixSum_zero (B : ℕ → ℕ) : prefixSum B 0 = 0 := sum_range_zero B

lemma prefixSum_succ (B : ℕ → ℕ) (N : ℕ) :
    prefixSum B (N + 1) = prefixSum B N + B N := sum_range_succ B N

lemma prefixSum_mono (B : ℕ → ℕ) : Monotone (prefixSum B) :=
  fun _ _ h => sum_le_sum_of_subset (range_mono h)

lemma prefixSum_add_const_block {B : ℕ → ℕ} {b l j : ℕ} (hlj : l ≤ j)
    (hconst : ∀ r, l ≤ r → r < j → B r = b) :
    prefixSum B j = prefixSum B l + (j - l) * b := by
  induction j with
  | zero =>
    have : l = 0 := by omega
    subst this
    simp
  | succ j ih =>
    rcases eq_or_lt_of_le hlj with rfl | hlt
    · simp
    · have ih' := ih (by omega) (fun r h1 h2 => hconst r h1 (by omega))
      have hbj : B j = b := hconst j (by omega) (by omega)
      rw [prefixSum_succ, ih', hbj, show j + 1 - l = (j - l) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega

lemma prefixSums_mono {B : ℕ → ℕ} {M N : ℕ} (hMN : M ≤ N) :
    prefixSums B M ⊆ prefixSums B N := by
  rintro x ⟨s, hs, rfl⟩
  exact ⟨s, Subset.trans hs (range_mono hMN), rfl⟩

lemma prefixSums_subset_subseqSums' (B : ℕ → ℕ) (N : ℕ) :
    prefixSums B N ⊆ subseqSums' B := by
  rintro x ⟨s, _, rfl⟩
  exact ⟨s, rfl⟩

lemma le_prefixSum_of_mem_prefixSums {B : ℕ → ℕ} {N x : ℕ} (hx : x ∈ prefixSums B N) :
    x ≤ prefixSum B N := by
  rcases hx with ⟨s, hs, rfl⟩
  exact sum_le_sum_of_subset hs

lemma sub_mem_prefixSums_of_mem_prefixSums {B : ℕ → ℕ} {N x : ℕ} (hx : x ∈ prefixSums B N) :
    prefixSum B N - x ∈ prefixSums B N := by
  rcases hx with ⟨s, hs, rfl⟩
  refine ⟨range N \ s, sdiff_subset, ?_⟩
  have h := sum_sdiff (f := B) hs
  dsimp [prefixSum]
  omega

lemma mem_prefixSums_of_sub_mem_prefixSums {B : ℕ → ℕ} {N x : ℕ}
    (hle : x ≤ prefixSum B N) (hsub : prefixSum B N - x ∈ prefixSums B N) :
    x ∈ prefixSums B N := by
  have h := sub_mem_prefixSums_of_mem_prefixSums hsub
  rwa [Nat.sub_sub_self hle] at h

lemma add_mem_prefixSums_of_mem_prefixSums {B : ℕ → ℕ} {j m N x : ℕ}
    (hx : x ∈ prefixSums B j) (hjm : j ≤ m) (hmN : m < N) :
    x + B m ∈ prefixSums B N := by
  rcases hx with ⟨s, hs, rfl⟩
  have hm_notin : m ∉ s := fun hm => by
    have := mem_range.mp (hs hm)
    omega
  refine ⟨insert m s, ?_, ?_⟩
  · intro r hr
    rw [mem_range]
    rcases mem_insert.mp hr with h_eq | hrs
    · omega
    · have := mem_range.mp (hs hrs)
      omega
  · rw [sum_insert hm_notin]
    omega

lemma add_const_block_mem_prefixSums {B : ℕ → ℕ} {b p j x : ℕ}
    (hx : x ∈ prefixSums B (p + 1)) (hpj : p ≤ j)
    (hconst : ∀ r, p < r → r ≤ j → B r = b) :
    x + (j - p) * b ∈ prefixSums B (j + 1) := by
  induction j with
  | zero =>
    have : p = 0 := by omega
    subst this
    simpa using hx
  | succ j ih =>
    rcases eq_or_lt_of_le hpj with rfl | hlt
    · simpa using hx
    · have ih' := ih (by omega) (fun r h1 h2 => hconst r h1 (by omega))
      have hbj : B (j + 1) = b := hconst (j + 1) (by omega) (by omega)
      have hadd := add_mem_prefixSums_of_mem_prefixSums ih' (le_refl (j + 1)) (by omega : j + 1 < j + 1 + 1)
      have h_eq : x + (j + 1 - p) * b = x + (j - p) * b + B (j + 1) := by
        rw [hbj, show j + 1 - p = (j - p) + 1 by omega, Nat.add_mul, Nat.one_mul]
        omega
      rwa [h_eq]

/-- Lemma 6 (`lem:cut`): Every integer `x ∈ [T, S_N - T]` missing from `P_N` lies at distance
`< T` below an earlier cut total `S_j` (`j < N`). -/
lemma central_cut {B : ℕ → ℕ} (hB_mono : Monotone B) {T : ℕ} (hT : 1 ≤ T)
    (hB_comp : ∀ x ≥ T, x ∈ subseqSums' B) {N x : ℕ}
    (_hxT : T ≤ x) (hxS : x + T ≤ prefixSum B N) (hx_not : x ∉ prefixSums B N) :
    ∃ j < N, ∃ u < T, prefixSum B j = x + u := by
  suffices ∀ k ≤ N, x + T ≤ prefixSum B k → ∃ j < k, ∃ u < T, prefixSum B j = x + u by
    exact this N (le_refl N) hxS
  intro k
  induction k with
  | zero =>
    intro _ h0
    rw [prefixSum_zero] at h0
    omega
  | succ k ih =>
    intro hkN hkS
    by_cases hprev : x + T ≤ prefixSum B k
    · rcases ih (by omega) hprev with ⟨j, hjk, u, huT, hsum⟩
      exact ⟨j, by omega, u, huT, hsum⟩
    · rw [prefixSum_succ] at hkS
      let y := prefixSum B (k + 1) - x
      have hyT : T ≤ y := by
        dsimp [y]
        rw [prefixSum_succ]
        omega
      have hyB : B k ≤ y := by
        by_contra hlt
        rcases hB_comp y hyT with ⟨s, hysum⟩
        have hs_sub : s ⊆ range (k + 1) := by
          intro r hr
          rw [mem_range]
          by_contra hge
          have hle : B r ≤ y := by
            rw [hysum]
            exact single_le_sum (fun _ _ => Nat.zero_le _) hr
          have hmono : B k ≤ B r := hB_mono (by omega)
          omega
        have hy_mem : y ∈ prefixSums B (k + 1) := ⟨s, hs_sub, hysum⟩
        have hx_le : x ≤ prefixSum B (k + 1) := by
          rw [prefixSum_succ]
          omega
        have hsub_mem : prefixSum B (k + 1) - x ∈ prefixSums B (k + 1) := hy_mem
        have hx_mem := mem_prefixSums_of_sub_mem_prefixSums hx_le hsub_mem
        exact hx_not (prefixSums_mono hkN hx_mem)
      dsimp [y] at hyB
      rw [prefixSum_succ] at hyB
      refine ⟨k, Nat.lt_succ_self k, prefixSum B k - x, by omega, by omega⟩

lemma exists_prefix_for_lt_T (B : ℕ → ℕ) (T : ℕ) :
    ∃ J₀ : ℕ, ∀ u < T, u ∈ subseqSums' B → u ∈ prefixSums B J₀ := by
  induction T with
  | zero =>
    exact ⟨0, fun u hu => by omega⟩
  | succ m ih =>
    rcases ih with ⟨J₀, hJ₀⟩
    by_cases hm : m ∈ subseqSums' B
    · rcases hm with ⟨s, hs⟩
      let J₁ := max J₀ (s.sup id + 1)
      refine ⟨J₁, fun u hu huB => ?_⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hu) with rfl | hlt
      · refine ⟨s, fun r hr => ?_, hs⟩
        rw [mem_range]
        have hle : r ≤ s.sup id := le_sup (f := id) hr
        dsimp [J₁]
        omega
      · exact prefixSums_mono (le_max_left J₀ _) (hJ₀ u hlt huB)
    · refine ⟨J₀, fun u hu huB => ?_⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hu) with rfl | hlt
      · exact absurd huB hm
      · exact hJ₀ u hlt huB

lemma exists_first_eq {B : ℕ → ℕ} (hB_mono : Monotone B) (l : ℕ) :
    ∃ p ≤ l, B p = B l ∧ (p = 0 ∨ B (p - 1) < B p) := by
  induction l with
  | zero => exact ⟨0, le_refl 0, rfl, Or.inl rfl⟩
  | succ l ih =>
    rcases ih with ⟨p, hpl, hp_eq, hp_min⟩
    rcases eq_or_lt_of_le (hB_mono (Nat.le_succ l)) with heq | hlt
    · exact ⟨p, by omega, hp_eq.trans heq, hp_min⟩
    · exact ⟨l + 1, le_refl (l + 1), rfl, Or.inr hlt⟩

lemma exists_first_gt {B : ℕ → ℕ} (hB_mono : Monotone B) {j M : ℕ} (h : B j < B M) :
    ∃ m ≤ M, B j < B m ∧ ∀ r < m, B r ≤ B j := by
  induction M with
  | zero =>
    exact ⟨0, le_refl 0, h, fun r hr => by omega⟩
  | succ M ih =>
    by_cases hprev : B j < B M
    · rcases ih hprev with ⟨m, hmM, hjm, hm_min⟩
      exact ⟨m, by omega, hjm, hm_min⟩
    · refine ⟨M + 1, le_refl (M + 1), h, fun r hr => ?_⟩
      have h1 : B r ≤ B M := hB_mono (by omega)
      omega

/-- Lemma 7 (`lem:close`): In any state `(j, N, E)` with `B j ≥ T`, the first term value `B m`
strictly greater than `B j` satisfies `B m - B j ≤ e` for every `e ∈ E`. -/
lemma central_close {B : ℕ → ℕ} (hB_mono : Monotone B) {T : ℕ}
    (hB_comp : ∀ x ≥ T, x ∈ subseqSums' B) {j N m : ℕ} {E : Finset ℕ}
    (hjN : j < N) (hE_sub : ∀ e ∈ E, 1 ≤ e ∧ e ∉ subseqSums' B)
    (hE_miss : ∀ e ∈ E, e ≤ prefixSum B j ∧ prefixSum B j - e ∉ prefixSums B N)
    (hjT : T ≤ B j) (hjm : B j < B m) (hm_min : ∀ r < m, B r ≤ B j) :
    ∀ e ∈ E, B m - B j ≤ e := by
  intro e he
  rcases hE_sub e he with ⟨he1, he_not⟩
  rcases hE_miss e he with ⟨heS, he_miss⟩
  by_contra hgt
  have hbm_gt : B j + e < B m := by omega
  have hae_ge_T : T ≤ B j + e := by omega
  rcases hB_comp (B j + e) hae_ge_T with ⟨s, hssum⟩
  have hs_range_j : s ⊆ range j := by
    intro r hr
    rw [mem_range]
    have hr_le_sum : B r ≤ B j + e := by
      rw [hssum]
      exact single_le_sum (fun _ _ => Nat.zero_le _) hr
    have hr_lt_m : r < m := by
      by_contra hge_m
      have : B m ≤ B r := hB_mono (by omega)
      omega
    have hr_le_bj : B r ≤ B j := hm_min r hr_lt_m
    rcases eq_or_lt_of_le hr_le_bj with heq | hlt
    · exfalso
      apply he_not
      refine ⟨s.erase r, ?_⟩
      have herase := add_sum_erase s B hr
      omega
    · by_contra hge_j
      have : B j ≤ B r := hB_mono (by omega)
      omega
  have hae_mem : B j + e ∈ prefixSums B j := ⟨s, hs_range_j, hssum⟩
  have hae_le : B j + e ≤ prefixSum B j := le_prefixSum_of_mem_prefixSums hae_mem
  have hcomp_mem : prefixSum B j - (B j + e) ∈ prefixSums B j :=
    sub_mem_prefixSums_of_mem_prefixSums hae_mem
  have hadd_mem := add_mem_prefixSums_of_mem_prefixSums hcomp_mem (le_refl j) hjN
  have htarget : prefixSum B j - (B j + e) + B j = prefixSum B j - e := by omega
  rw [htarget] at hadd_mem
  exact he_miss hadd_mem

/-- Lemma 8 (`lem:common`): Missing sums in `[max(T, S_J) + 1, S_j - T]` with spread at most `2h`
share a single cut index `l < j`. -/
lemma central_common {B : ℕ → ℕ} (hB_mono : Monotone B) (_hB_pos : ∀ i, 1 ≤ B i)
    {T : ℕ} (hT : 1 ≤ T) (hB_comp : ∀ x ≥ T, x ∈ subseqSums' B)
    {H : Finset ℕ} (hH_def : ∀ u, u ∈ H ↔ u < T ∧ u ∉ subseqSums' B)
    {h J : ℕ} (hH_ub : ∀ u ∈ H, 1 ≤ u ∧ u ≤ h)
    (hJ₀ : ∀ u < T, u ∈ subseqSums' B → u ∈ prefixSums B J)
    (hJB : 3 * h < B J)
    {j : ℕ} {R : Finset ℕ} (hR : R.Nonempty)
    (hR_miss : ∀ x ∈ R, x ∉ prefixSums B j)
    (hR_low : ∀ x ∈ R, T ≤ x ∧ prefixSum B J < x)
    (hR_high : ∀ x ∈ R, x + T ≤ prefixSum B j)
    (hR_spread : ∀ x ∈ R, ∀ y ∈ R, x ≤ y + 2 * h) :
    ∃ l < j, ∃ E' : Finset ℕ,
      E'.Nonempty ∧ E' ⊆ H ∧ E'.card = R.card ∧
      (∀ e ∈ E', e ≤ prefixSum B l ∧ prefixSum B l - e ∈ R ∧ prefixSum B l - e ∉ prefixSums B j) ∧
      (∀ x ∈ R, x ≤ prefixSum B l ∧ prefixSum B l - x ∈ E') := by
  have hcut_each : ∀ x ∈ R, ∃ l < j, ∃ u ∈ H, prefixSum B l = x + u ∧ J < l := by
    intro x hx
    rcases central_cut hB_mono hT hB_comp (hR_low x hx).1 (hR_high x hx) (hR_miss x hx) with
      ⟨l, hlj, u, huT, hsum⟩
    have hJl : J < l := by
      by_contra hle
      have h1 : prefixSum B l ≤ prefixSum B J := prefixSum_mono B (by omega)
      have h2 := (hR_low x hx).2
      omega
    have huH : u ∈ H := by
      rw [hH_def]
      refine ⟨huT, fun huB => ?_⟩
      have hu_mem : u ∈ prefixSums B l :=
        prefixSums_mono (by omega : J ≤ l) (hJ₀ u huT huB)
      have hx_le : x ≤ prefixSum B l := by omega
      have hsub : prefixSum B l - x = u := by omega
      rw [← hsub] at hu_mem
      have hx_mem := mem_prefixSums_of_sub_mem_prefixSums hx_le hu_mem
      exact hR_miss x hx (prefixSums_mono (by omega : l ≤ j) hx_mem)
    exact ⟨l, hlj, u, huH, hsum, hJl⟩
  rcases hR with ⟨x₀, hx₀⟩
  rcases hcut_each x₀ hx₀ with ⟨l, hlj, u₀, hu₀H, hsum₀, hJl⟩
  have hu₀_ub := hH_ub u₀ hu₀H
  have hall_l : ∀ x ∈ R, x ≤ prefixSum B l ∧ prefixSum B l - x ∈ H := by
    intro x hx
    rcases hcut_each x hx with ⟨lx, hlxj, ux, huxH, hsumx, hJlx⟩
    have hux_ub := hH_ub ux huxH
    have hsp1 := hR_spread x hx x₀ hx₀
    have hsp2 := hR_spread x₀ hx₀ x hx
    have hl_eq : lx = l := by
      rcases lt_trichotomy lx l with hlt | rfl | hgt
      · have h1 : prefixSum B (lx + 1) ≤ prefixSum B l := prefixSum_mono B (by omega)
        rw [prefixSum_succ] at h1
        have h2 : B J ≤ B lx := hB_mono (by omega)
        omega
      · rfl
      · have h1 : prefixSum B (l + 1) ≤ prefixSum B lx := prefixSum_mono B (by omega)
        rw [prefixSum_succ] at h1
        have h2 : B J ≤ B l := hB_mono (by omega)
        omega
    subst hl_eq
    refine ⟨by omega, ?_⟩
    have : prefixSum B lx - x = ux := by omega
    rw [this]
    exact huxH
  let E' := R.image (fun x => prefixSum B l - x)
  have hE'_card : E'.card = R.card := by
    apply card_image_of_injOn
    intro x hx y hy hxy
    dsimp at hxy
    have hx_le := (hall_l x hx).1
    have hy_le := (hall_l y hy).1
    omega
  refine ⟨l, hlj, E', Nonempty.image ⟨x₀, hx₀⟩ _, ?_, hE'_card, ?_, ?_⟩
  · intro e he
    rcases mem_image.mp he with ⟨x, hx, rfl⟩
    exact (hall_l x hx).2
  · intro e he
    rcases mem_image.mp he with ⟨x, hx, rfl⟩
    have hx_le := (hall_l x hx).1
    have hsub : prefixSum B l - (prefixSum B l - x) = x := Nat.sub_sub_self hx_le
    rw [hsub]
    exact ⟨by omega, hx, hR_miss x hx⟩
  · intro x hx
    exact ⟨(hall_l x hx).1, mem_image_of_mem _ hx⟩

/-! ### States, Normalization, and Transitions (Section 4.2 & 4.3) -/

def IsState (B : ℕ → ℕ) (H : Finset ℕ) (j N : ℕ) (E : Finset ℕ) : Prop :=
  j < N ∧ E.Nonempty ∧ E ⊆ H ∧
    ∀ e ∈ E, e ≤ prefixSum B j ∧ prefixSum B j - e ∉ prefixSums B N

def IsNormState (B : ℕ → ℕ) (H : Finset ℕ) (j N : ℕ) (E : Finset ℕ) : Prop :=
  IsState B H j N E ∧ (B j = B (N - 1) → j = 0 ∨ B (j - 1) < B j)

def statePotential (B : ℕ → ℕ) (h j N : ℕ) (E : Finset ℕ) : ℕ :=
  if hE : E.Nonempty then
    if B j = B (N - 1) then (h + 1) * E.card + E.min' hE
    else (h + 1) * (E.card + 1)
  else 0

lemma prefixSum_ge_index {B : ℕ → ℕ} (hB_pos : ∀ i, 1 ≤ B i) (k : ℕ) :
    k ≤ prefixSum B k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [prefixSum_succ]
    have := hB_pos k
    omega

lemma statePotential_ub {B : ℕ → ℕ} {H : Finset ℕ} {h j N : ℕ} {E : Finset ℕ}
    (hH_ub : ∀ u ∈ H, 1 ≤ u ∧ u ≤ h) (hst : IsState B H j N E) :
    statePotential B h j N E ≤ (h + 1) * (H.card + 1) := by
  rcases hst with ⟨_, hE, hEH, _⟩
  have hcard : E.card ≤ H.card := card_le_card hEH
  have hmin_mem : E.min' hE ∈ H := hEH (min'_mem E hE)
  have hmin_ub : E.min' hE ≤ h := (hH_ub _ hmin_mem).2
  dsimp [statePotential]
  rw [dif_pos hE]
  split_ifs
  · have hmul : (h + 1) * E.card ≤ (h + 1) * H.card := Nat.mul_le_mul_left _ hcard
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · exact Nat.mul_le_mul_left _ (by omega)

lemma statePotential_ge_card {B : ℕ → ℕ} {H : Finset ℕ} {h j N : ℕ} {E : Finset ℕ}
    (hH_ub : ∀ u ∈ H, 1 ≤ u ∧ u ≤ h) (hst : IsState B H j N E) :
    (h + 1) * E.card + 1 ≤ statePotential B h j N E := by
  rcases hst with ⟨_, hE, hEH, _⟩
  have hmin_mem : E.min' hE ∈ H := hEH (min'_mem E hE)
  have hmin_lb : 1 ≤ E.min' hE := (hH_ub _ hmin_mem).1
  dsimp [statePotential]
  rw [dif_pos hE]
  split_ifs
  · omega
  · rw [Nat.mul_add, Nat.mul_one]
    omega

lemma normalize_state {B : ℕ → ℕ} (hB_mono : Monotone B) (hB_pos : ∀ i, 1 ≤ B i)
    {H : Finset ℕ} {h l j K' : ℕ} {E' : Finset ℕ}
    (hH_ub : ∀ u ∈ H, 1 ≤ u ∧ u ≤ h)
    (hst : IsState B H l j E')
    (hBl : B (max K' h) < B l) :
    ∃ j' N', IsNormState B H j' N' E' ∧ K' ≤ j' ∧
      (B l = B (j - 1) →
        statePotential B h j' N' E' = (h + 1) * E'.card + E'.min' hst.2.1) ∧
      (B l ≠ B (j - 1) →
        statePotential B h j' N' E' = (h + 1) * (E'.card + 1)) := by
  rcases hst with ⟨hlj, hE', hE'H, hE'miss⟩
  by_cases hconst : B l = B (j - 1)
  · rcases exists_first_eq hB_mono l with ⟨p, hpl, hp_eq, hp_min⟩
    have hp_gt : max K' h < p := by
      by_contra hle
      have : B p ≤ B (max K' h) := hB_mono (by omega)
      omega
    have hpK' : K' ≤ p := by omega
    have hph : h < p := by omega
    have hpS : p ≤ prefixSum B p := prefixSum_ge_index hB_pos p
    have hblock : ∀ r, p ≤ r → r < l → B r = B l := by
      intro r hr1 hr2
      have h1 : B p ≤ B r := hB_mono hr1
      have h2 : B r ≤ B l := hB_mono (by omega)
      omega
    have hblock' : ∀ r, p < r → r ≤ l → B r = B l := by
      intro r hr1 hr2
      have h1 : B p ≤ B r := hB_mono (by omega)
      have h2 : B r ≤ B l := hB_mono hr2
      omega
    have hSl_eq : prefixSum B l = prefixSum B p + (l - p) * B l :=
      prefixSum_add_const_block hpl hblock
    have hp_state : IsState B H p (p + 1) E' := by
      refine ⟨Nat.lt_succ_self p, hE', hE'H, fun e he => ?_⟩
      have he_ub : e ≤ h := (hH_ub e (hE'H he)).2
      refine ⟨by omega, fun hmem => ?_⟩
      have hadd := add_const_block_mem_prefixSums hmem hpl hblock'
      have htarget : prefixSum B p - e + (l - p) * B l = prefixSum B l - e := by omega
      rw [htarget] at hadd
      exact (hE'miss e he).2 (prefixSums_mono (by omega : l + 1 ≤ j) hadd)
    have hp_norm : IsNormState B H p (p + 1) E' :=
      ⟨hp_state, fun _ => hp_min⟩
    refine ⟨p, p + 1, hp_norm, hpK', fun _ => ?_, fun hne => absurd hconst hne⟩
    dsimp [statePotential]
    rw [dif_pos hE', if_pos rfl]
  · have hl_gt : max K' h < l := by
      by_contra hle
      have : B l ≤ B (max K' h) := hB_mono (by omega)
      omega
    have hl_norm : IsNormState B H l j E' :=
      ⟨⟨hlj, hE', hE'H, hE'miss⟩, fun heq => absurd heq hconst⟩
    refine ⟨l, j, hl_norm, by omega, fun heq => absurd heq hconst, fun _ => ?_⟩
    dsimp [statePotential]
    rw [dif_pos hE', if_neg hconst]

lemma step_exists {B : ℕ → ℕ} (hB_mono : Monotone B) (hB_pos : ∀ i, 1 ≤ B i)
    (hB_unb : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, M ≤ B i)
    (hB_slack : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, B i + M ≤ prefixSum B i)
    {T : ℕ} (hT : 1 ≤ T) (hB_comp : ∀ x ≥ T, x ∈ subseqSums' B)
    {H : Finset ℕ} (hH : H.Nonempty)
    (hH_def : ∀ u, u ∈ H ↔ u < T ∧ u ∉ subseqSums' B)
    (K' : ℕ) :
    let h := H.max' hH
    ∃ K : ℕ, ∀ j N : ℕ, ∀ E : Finset ℕ,
      IsNormState B H j N E → K ≤ j →
      ∃ j' N' : ℕ, ∃ E' : Finset ℕ,
        IsNormState B H j' N' E' ∧ K' ≤ j' ∧
        statePotential B h j N E < statePotential B h j' N' E' := by
  intro h
  have hH_ub : ∀ u ∈ H, 1 ≤ u ∧ u ≤ h := by
    intro u hu
    refine ⟨?_, le_max' H u hu⟩
    by_contra h0
    have hu0 : u = 0 := by omega
    subst hu0
    have h0_in : 0 ∈ subseqSums' B := ⟨∅, by simp⟩
    exact (hH_def 0 |>.mp hu).2 h0_in
  rcases exists_prefix_for_lt_T B T with ⟨J₀, hJ₀⟩
  rcases hB_unb (3 * h + 1) with ⟨J₁, hJ₁⟩
  let J := max J₀ J₁
  have hJ₀' : ∀ u < T, u ∈ subseqSums' B → u ∈ prefixSums B J :=
    fun u hu huB => prefixSums_mono (le_max_left J₀ J₁) (hJ₀ u hu huB)
  have hJB : 3 * h < B J := by
    have := hJ₁ J (le_max_right J₀ J₁)
    omega
  let M₁ := max K' h
  rcases hB_unb (max T (B M₁) + 1) with ⟨L₁, hL₁⟩
  let M₂ := max T (max (prefixSum B J) (prefixSum B L₁))
  rcases hB_slack (2 * h + M₂ + 1) with ⟨K₁, hK₁⟩
  rcases hB_unb (max T h + 1) with ⟨K₂, hK₂⟩
  refine ⟨max K₁ (K₂ + 1), fun j N E hnorm hjK => ?_⟩
  rcases hnorm with ⟨⟨hjN, hE, hEH, hEmiss⟩, hnorm_cond⟩
  have hjK₁ : K₁ ≤ j := le_trans (le_max_left _ _) hjK
  have hjK₂ : K₂ + 1 ≤ j := le_trans (le_max_right _ _) hjK
  have hjslack : B j + (2 * h + M₂ + 1) ≤ prefixSum B j := hK₁ j hjK₁
  have hbj_prev : max T h < B (j - 1) := by
    have := hK₂ (j - 1) (by omega)
    omega
  have hbj_ge_prev : B (j - 1) ≤ B j := hB_mono (by omega)
  have hM₂_T : T ≤ M₂ := le_max_left _ _
  have hM₂_SJ : prefixSum B J ≤ M₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM₂_SL₁ : prefixSum B L₁ ≤ M₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hE_sub : ∀ e ∈ E, 1 ≤ e ∧ e ∉ subseqSums' B := by
    intro e he
    exact ⟨(hH_ub e (hEH he)).1, (hH_def e |>.mp (hEH he)).2⟩
  by_cases hconst : B j = B (N - 1)
  · -- Constant state transition
    have hbj_lt : B (j - 1) < B j := by
      rcases hnorm_cond hconst with hj0 | hlt
      · omega
      · exact hlt
    let R := E.image (fun e => prefixSum B j - B j - e)
    have hR_nonempty : R.Nonempty := Nonempty.image hE _
    have hR_card : R.card = E.card := by
      apply card_image_of_injOn
      intro e₁ he₁ e₂ he₂ heq
      dsimp at heq
      have h1 := (hH_ub e₁ (hEH he₁)).2
      have h2 := (hH_ub e₂ (hEH he₂)).2
      omega
    have hR_miss : ∀ x ∈ R, x ∉ prefixSums B j := by
      intro x hx hmem
      rcases mem_image.mp hx with ⟨e, he, rfl⟩
      have he_ub := (hH_ub e (hEH he)).2
      have hadd := add_mem_prefixSums_of_mem_prefixSums hmem (le_refl j) hjN
      have htarget : prefixSum B j - B j - e + B j = prefixSum B j - e := by omega
      rw [htarget] at hadd
      exact (hEmiss e he).2 hadd
    have hR_low : ∀ x ∈ R, T ≤ x ∧ prefixSum B J < x := by
      intro x hx
      rcases mem_image.mp hx with ⟨e, he, rfl⟩
      have he_ub := (hH_ub e (hEH he)).2
      omega
    have hR_high : ∀ x ∈ R, x + T ≤ prefixSum B j := by
      intro x hx
      rcases mem_image.mp hx with ⟨e, he, rfl⟩
      have he_lb := (hH_ub e (hEH he)).1
      omega
    have hR_spread : ∀ x ∈ R, ∀ y ∈ R, x ≤ y + 2 * h := by
      intro x hx y hy
      rcases mem_image.mp hx with ⟨e₁, he₁, rfl⟩
      rcases mem_image.mp hy with ⟨e₂, he₂, rfl⟩
      have h1 := (hH_ub e₁ (hEH he₁)).2
      have h2 := (hH_ub e₂ (hEH he₂)).2
      omega
    rcases central_common hB_mono hB_pos hT hB_comp hH_def hH_ub hJ₀' hJB
      hR_nonempty hR_miss hR_low hR_high hR_spread with
      ⟨l, hlj, E', hE', hE'H, hE'card, hE'props, hRprops⟩
    have hst' : IsState B H l j E' :=
      ⟨hlj, hE', hE'H, fun e he => ⟨(hE'props e he).1, (hE'props e he).2.2⟩⟩
    have hL₁_lt_l : L₁ < l := by
      rcases hE with ⟨e₀, he₀⟩
      let x₀ := prefixSum B j - B j - e₀
      have hx₀R : x₀ ∈ R := mem_image_of_mem _ he₀
      have hx₀_le : x₀ ≤ prefixSum B l := (hRprops x₀ hx₀R).1
      have he₀_ub := (hH_ub e₀ (hEH he₀)).2
      by_contra hle
      have : prefixSum B l ≤ prefixSum B L₁ := prefixSum_mono B (by omega)
      omega
    have hBl_gt : max T (B M₁) < B l := by
      have := hL₁ l (by omega)
      omega
    rcases normalize_state hB_mono hB_pos hH_ub hst' (by omega : B M₁ < B l) with
      ⟨j', N', hnorm', hj'K', hpot_const, hpot_dist⟩
    refine ⟨j', N', E', hnorm', hj'K', ?_⟩
    have hpot_old : statePotential B h j N E = (h + 1) * E.card + E.min' hE := by
      dsimp [statePotential]
      rw [dif_pos hE, if_pos hconst]
    rw [hpot_old]
    by_cases hconst' : B l = B (j - 1)
    · rw [hpot_const hconst', hE'card, hR_card]
      let b := B (j - 1)
      have hBl_eq_b : B l = b := hconst'
      have hblock : ∀ r, l ≤ r → r < j → B r = b := by
        intro r hr1 hr2
        have h1 : B l ≤ B r := hB_mono hr1
        have h2 : B r ≤ B (j - 1) := hB_mono (by omega)
        omega
      have hSj_eq : prefixSum B j = prefixSum B l + (j - l) * b :=
        prefixSum_add_const_block (by omega : l ≤ j) hblock
      have hjm_min : ∀ r < j, B r ≤ B l := by
        intro r hr
        have : B r ≤ B (j - 1) := hB_mono (by omega)
        omega
      have hclose := central_close hB_mono hB_comp hlj
        (fun e he => ⟨(hH_ub e (hE'H he)).1, (hH_def e |>.mp (hE'H he)).2⟩)
        (fun e he => ⟨(hE'props e he).1, (hE'props e he).2.2⟩)
        (by omega : T ≤ B l) (by omega : B l < B j) hjm_min
      let e_min := E.min' hE
      have he_min_mem : e_min ∈ E := min'_mem E hE
      have he_min_ub : e_min ≤ h := (hH_ub e_min (hEH he_min_mem)).2
      let x_min := prefixSum B j - B j - e_min
      have hx_min_R : x_min ∈ R := mem_image_of_mem _ he_min_mem
      have hx_min_le : x_min ≤ prefixSum B l := (hRprops x_min hx_min_R).1
      let u₀ := prefixSum B l - x_min
      have hu₀_E' : u₀ ∈ E' := (hRprops x_min hx_min_R).2
      have hu₀_close : B j - B l ≤ u₀ := hclose u₀ hu₀_E'
      have hjl_one : j - l = 1 := by
        by_contra hne
        have h2 : 2 ≤ j - l := by omega
        have hmul : 2 * b ≤ (j - l) * b := Nat.mul_le_mul_right b h2
        dsimp [u₀, x_min, b] at hu₀_close hx_min_le hSj_eq hmul
        omega
      rw [hjl_one, Nat.one_mul] at hSj_eq
      let u_min := E'.min' hE'
      have hu_min_E' : u_min ∈ E' := min'_mem E' hE'
      have hu_min_R : prefixSum B l - u_min ∈ R := (hE'props u_min hu_min_E').2.1
      have hu_min_le : u_min ≤ prefixSum B l := (hE'props u_min hu_min_E').1
      rcases mem_image.mp hu_min_R with ⟨e, he, he_eq⟩
      have he_ge : e_min ≤ e := min'_le E e he
      have he_ub : e ≤ h := (hH_ub e (hEH he)).2
      dsimp [b] at hSj_eq
      omega
    · rw [hpot_dist hconst', hE'card, hR_card, Nat.mul_add, Nat.mul_one]
      have hmin_ub : E.min' hE ≤ h := (hH_ub _ (hEH (min'_mem E hE))).2
      omega
  · -- Distinct state transition
    have hbj_lt_N : B j < B (N - 1) := by
      have : B j ≤ B (N - 1) := hB_mono (by omega)
      omega
    rcases exists_first_gt hB_mono hbj_lt_N with ⟨m, hmN, hjm_val, hm_min⟩
    have hjm_idx : j < m := by
      by_contra hle
      have : B m ≤ B j := hB_mono (by omega)
      omega
    have hm_lt_N : m < N := by omega
    have hclose := central_close hB_mono hB_comp hjN hE_sub hEmiss
      (by omega : T ≤ B j) hjm_val hm_min
    have hbm_diff_ub : B m - B j ≤ h := by
      rcases hE with ⟨e₀, he₀⟩
      have h1 := hclose e₀ he₀
      have h2 := (hH_ub e₀ (hEH he₀)).2
      omega
    let R₁ := E.image (fun e => prefixSum B j - B j - e)
    let R₂ := E.image (fun e => prefixSum B j - B m - e)
    let R := R₁ ∪ R₂
    have hR_nonempty : R.Nonempty := Nonempty.mono subset_union_left (Nonempty.image hE _)
    have hR₁_card : R₁.card = E.card := by
      apply card_image_of_injOn
      intro e₁ he₁ e₂ he₂ heq
      dsimp at heq
      have h1 := (hH_ub e₁ (hEH he₁)).2
      have h2 := (hH_ub e₂ (hEH he₂)).2
      omega
    let e_max := E.max' hE
    have he_max_mem : e_max ∈ E := max'_mem E hE
    have he_max_ub : e_max ≤ h := (hH_ub e_max (hEH he_max_mem)).2
    let y₀ := prefixSum B j - B m - e_max
    have hy₀_R₂ : y₀ ∈ R₂ := mem_image_of_mem _ he_max_mem
    have hy₀_not_R₁ : y₀ ∉ R₁ := by
      intro hy₀
      rcases mem_image.mp hy₀ with ⟨e, he, heq⟩
      have he_le : e ≤ e_max := le_max' E e he
      dsimp [y₀] at heq
      omega
    have hR_card_gt : E.card + 1 ≤ R.card := by
      have hsub : insert y₀ R₁ ⊆ R := by
        intro x hx
        rcases mem_insert.mp hx with rfl | hx₁
        · exact mem_union_right R₁ hy₀_R₂
        · exact mem_union_left R₂ hx₁
      have hle := card_le_card hsub
      rw [card_insert_of_notMem hy₀_not_R₁, hR₁_card] at hle
      exact hle
    have hR_miss : ∀ x ∈ R, x ∉ prefixSums B j := by
      intro x hx hmem
      rcases mem_union.mp hx with hx₁ | hx₂
      · rcases mem_image.mp hx₁ with ⟨e, he, rfl⟩
        have he_ub := (hH_ub e (hEH he)).2
        have hadd := add_mem_prefixSums_of_mem_prefixSums hmem (le_refl j) hjN
        have htarget : prefixSum B j - B j - e + B j = prefixSum B j - e := by omega
        rw [htarget] at hadd
        exact (hEmiss e he).2 hadd
      · rcases mem_image.mp hx₂ with ⟨e, he, rfl⟩
        have he_ub := (hH_ub e (hEH he)).2
        have hadd := add_mem_prefixSums_of_mem_prefixSums hmem (by omega : j ≤ m) hm_lt_N
        have htarget : prefixSum B j - B m - e + B m = prefixSum B j - e := by omega
        rw [htarget] at hadd
        exact (hEmiss e he).2 hadd
    have hR_bounds : ∀ x ∈ R,
        prefixSum B j - B j - 2 * h ≤ x ∧ x ≤ prefixSum B j - B j - 1 := by
      intro x hx
      rcases mem_union.mp hx with hx₁ | hx₂
      · rcases mem_image.mp hx₁ with ⟨e, he, rfl⟩
        have h1 := (hH_ub e (hEH he)).1
        have h2 := (hH_ub e (hEH he)).2
        omega
      · rcases mem_image.mp hx₂ with ⟨e, he, rfl⟩
        have h1 := (hH_ub e (hEH he)).1
        have h2 := (hH_ub e (hEH he)).2
        omega
    have hR_low : ∀ x ∈ R, T ≤ x ∧ prefixSum B J < x := by
      intro x hx
      have hb := hR_bounds x hx
      omega
    have hR_high : ∀ x ∈ R, x + T ≤ prefixSum B j := by
      intro x hx
      have hb := hR_bounds x hx
      omega
    have hR_spread : ∀ x ∈ R, ∀ y ∈ R, x ≤ y + 2 * h := by
      intro x hx y hy
      have hbx := hR_bounds x hx
      have hby := hR_bounds y hy
      omega
    rcases central_common hB_mono hB_pos hT hB_comp hH_def hH_ub hJ₀' hJB
      hR_nonempty hR_miss hR_low hR_high hR_spread with
      ⟨l, hlj, E', hE', hE'H, hE'card, hE'props, hRprops⟩
    have hst' : IsState B H l j E' :=
      ⟨hlj, hE', hE'H, fun e he => ⟨(hE'props e he).1, (hE'props e he).2.2⟩⟩
    have hL₁_lt_l : L₁ < l := by
      have hy₀_R : y₀ ∈ R := mem_union_right R₁ hy₀_R₂
      have hy₀_le : y₀ ≤ prefixSum B l := (hRprops y₀ hy₀_R).1
      have hy₀_b := hR_bounds y₀ hy₀_R
      by_contra hle
      have : prefixSum B l ≤ prefixSum B L₁ := prefixSum_mono B (by omega)
      omega
    have hBl_gt : max T (B M₁) < B l := by
      have := hL₁ l (by omega)
      omega
    rcases normalize_state hB_mono hB_pos hH_ub hst' (by omega : B M₁ < B l) with
      ⟨j', N', hnorm', hj'K', _, _⟩
    refine ⟨j', N', E', hnorm', hj'K', ?_⟩
    have hpot_old : statePotential B h j N E = (h + 1) * (E.card + 1) := by
      dsimp [statePotential]
      rw [dif_pos hE, if_neg hconst]
    have hpot_new_lb := statePotential_ge_card hH_ub hnorm'.1
    have hcard_ge : E.card + 1 ≤ E'.card := by omega
    have hmul : (h + 1) * (E.card + 1) ≤ (h + 1) * E'.card := Nat.mul_le_mul_left _ hcard_ge
    omega

/-- Theorem 2 (`thm:central`): For an unbounded nondecreasing positive integer sequence `B`
with `[T, ∞) ⊆ FS(B)` and diverging prefix slack, `[T, S_N - T] ⊆ P_N` for all large `N`. -/
theorem central_interval_thm {B : ℕ → ℕ} (hB_mono : Monotone B) (hB_pos : ∀ i, 1 ≤ B i)
    (hB_unb : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, M ≤ B i)
    (hB_slack : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, B i + M ≤ prefixSum B i)
    {T : ℕ} (hT : 1 ≤ T) (hB_comp : ∀ x ≥ T, x ∈ subseqSums' B) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℕ, T ≤ x → x + T ≤ prefixSum B N → x ∈ prefixSums B N := by
  let H : Finset ℕ := (range T).filter (fun u => u ∉ subseqSums' B)
  have hH_def : ∀ u, u ∈ H ↔ u < T ∧ u ∉ subseqSums' B := by
    intro u
    simp [H, mem_filter, mem_range]
  rcases exists_prefix_for_lt_T B T with ⟨J₀, hJ₀⟩
  by_cases hH : H.Nonempty
  · have hH_ub : ∀ u ∈ H, 1 ≤ u ∧ u ≤ H.max' hH := by
      intro u hu
      refine ⟨?_, le_max' H u hu⟩
      by_contra h0
      have hu0 : u = 0 := by omega
      subst hu0
      exact (hH_def 0 |>.mp hu).2 ⟨∅, by simp⟩
    have h_no_norm_state : ∀ k : ℕ, ∃ K : ℕ, ∀ j N : ℕ, ∀ E : Finset ℕ,
        IsNormState B H j N E →
        (H.max' hH + 1) * (H.card + 1) + 1 - statePotential B (H.max' hH) j N E ≤ k →
        j < K := by
      intro k
      induction k with
      | zero =>
        refine ⟨0, fun j N E hnorm hle => ?_⟩
        have hub := statePotential_ub hH_ub hnorm.1
        omega
      | succ k ih =>
        rcases ih with ⟨K', hK'⟩
        rcases step_exists hB_mono hB_pos hB_unb hB_slack hT hB_comp hH hH_def K' with ⟨K, hK⟩
        refine ⟨K, fun j N E hnorm hle => ?_⟩
        by_contra hge
        rcases hK j N E hnorm (by omega) with ⟨j', N', E', hnorm', hj'K', hpot_lt⟩
        have hub := statePotential_ub hH_ub hnorm.1
        have hlt := hK' j' N' E' hnorm' (by omega)
        omega
    rcases h_no_norm_state ((H.max' hH + 1) * (H.card + 1) + 1) with ⟨K_final, hK_final⟩
    let M₀ := max J₀ (max K_final (H.max' hH))
    rcases hB_unb (B M₀ + 1) with ⟨L₀, hL₀⟩
    rcases hB_unb (prefixSum B L₀ + 1) with ⟨N₀, hN₀⟩
    refine ⟨N₀, fun N hN x hxT hxS => ?_⟩
    by_contra hx_not
    rcases central_cut hB_mono hT hB_comp hxT hxS hx_not with ⟨j, hjN, u, huT, hSj⟩
    rcases hB_comp x hxT with ⟨s, hssum⟩
    have hs_ge_N : ∃ r ∈ s, N ≤ r := by
      by_contra hall
      have hs_sub : s ⊆ range N := by
        intro r hr
        rw [mem_range]
        by_contra hge
        exact hall ⟨r, hr, by omega⟩
      exact hx_not ⟨s, hs_sub, hssum⟩
    rcases hs_ge_N with ⟨r, hr, hrN⟩
    have hx_ge_BN : B N ≤ x := by
      have h1 : B N ≤ B r := hB_mono hrN
      have h2 : B r ≤ x := by
        rw [hssum]
        exact single_le_sum (fun _ _ => Nat.zero_le _) hr
      omega
    have hBN_gt : prefixSum B L₀ < B N := by
      have := hN₀ N hN
      omega
    have hL₀_lt_j : L₀ < j := by
      by_contra hle
      have : prefixSum B j ≤ prefixSum B L₀ := prefixSum_mono B (by omega)
      omega
    have hBj_gt : B M₀ < B j := by
      have := hL₀ j (by omega)
      omega
    have hM₀_lt_j : M₀ < j := by
      by_contra hle
      have : B j ≤ B M₀ := hB_mono (by omega)
      omega
    have hJ₀_le_M₀ : J₀ ≤ M₀ := le_max_left _ _
    have huH : u ∈ H := by
      rw [hH_def]
      refine ⟨huT, fun huB => ?_⟩
      have hu_mem : u ∈ prefixSums B j :=
        prefixSums_mono (by omega : J₀ ≤ j) (hJ₀ u huT huB)
      have hx_le : x ≤ prefixSum B j := by omega
      have hsub : prefixSum B j - x = u := by omega
      rw [← hsub] at hu_mem
      have hx_mem := mem_prefixSums_of_sub_mem_prefixSums hx_le hu_mem
      exact hx_not (prefixSums_mono (by omega : j ≤ N) hx_mem)
    have hst : IsState B H j N {u} := by
      refine ⟨hjN, singleton_nonempty u, singleton_subset_iff.mpr huH, fun e he => ?_⟩
      rw [mem_singleton.mp he]
      have hsub : prefixSum B j - u = x := by omega
      rw [hsub]
      exact ⟨by omega, hx_not⟩
    rcases normalize_state (K' := K_final) hB_mono hB_pos hH_ub hst (by
      have : B (max K_final (H.max' hH)) ≤ B M₀ := hB_mono (le_max_right J₀ _)
      omega) with ⟨j', N', hnorm', hj'K, _, _⟩
    have hlt := hK_final j' N' {u} hnorm' (by omega)
    omega
  · rw [not_nonempty_iff_eq_empty] at hH
    rcases hB_unb (prefixSum B J₀ + 1) with ⟨N₀, hN₀⟩
    refine ⟨N₀, fun N hN x hxT hxS => ?_⟩
    by_contra hx_not
    rcases central_cut hB_mono hT hB_comp hxT hxS hx_not with ⟨j, hjN, u, huT, hSj⟩
    rcases hB_comp x hxT with ⟨s, hssum⟩
    have hs_ge_N : ∃ r ∈ s, N ≤ r := by
      by_contra hall
      have hs_sub : s ⊆ range N := by
        intro r hr
        rw [mem_range]
        by_contra hge
        exact hall ⟨r, hr, by omega⟩
      exact hx_not ⟨s, hs_sub, hssum⟩
    rcases hs_ge_N with ⟨r, hr, hrN⟩
    have hx_ge_BN : B N ≤ x := by
      have h1 : B N ≤ B r := hB_mono hrN
      have h2 : B r ≤ x := by
        rw [hssum]
        exact single_le_sum (fun _ _ => Nat.zero_le _) hr
      omega
    have hBN_gt : prefixSum B J₀ < B N := by
      have := hN₀ N hN
      omega
    have hJ₀_lt_j : J₀ < j := by
      by_contra hle
      have : prefixSum B j ≤ prefixSum B J₀ := prefixSum_mono B (by omega)
      omega
    have huH : u ∈ H := by
      rw [hH_def]
      refine ⟨huT, fun huB => ?_⟩
      have hu_mem : u ∈ prefixSums B j :=
        prefixSums_mono (by omega : J₀ ≤ j) (hJ₀ u huT huB)
      have hx_le : x ≤ prefixSum B j := by omega
      have hsub : prefixSum B j - x = u := by omega
      rw [← hsub] at hu_mem
      have hx_mem := mem_prefixSums_of_sub_mem_prefixSums hx_le hu_mem
      exact hx_not (prefixSums_mono (by omega : j ≤ N) hx_mem)
    rw [hH] at huH
    exact notMem_empty u huH

/-! ### Section 2: The Deletion Classification (`lem:slack`, `lem:pair`, `prop:extension`) -/

def IsComplEmb (D : Finset ℕ) (emb : ℕ → ℕ) : Prop :=
  StrictMono emb ∧ (∀ i, emb i ∉ D) ∧ (∀ j, j ∉ D → ∃ i, emb i = j)

lemma exists_complEmb (D : Finset ℕ) : ∃ emb : ℕ → ℕ, IsComplEmb D emb := by
  induction D using Finset.induction_on with
  | empty =>
    exact ⟨id, fun _ _ h => h, fun _ => notMem_empty _, fun j _ => ⟨j, rfl⟩⟩
  | @insert a s ha ih =>
    rcases ih with ⟨emb, hstrict, hnot, hsurj⟩
    rcases hsurj a ha with ⟨i₀, rfl⟩
    let emb' : ℕ → ℕ := fun i => emb (if i < i₀ then i else i + 1)
    refine ⟨emb', ?_, ?_, ?_⟩
    · intro i j hij
      apply hstrict
      split_ifs <;> omega
    · intro i hi
      rcases mem_insert.mp hi with heq | hs
      · have h_inj := hstrict.injective heq
        split_ifs at h_inj <;> omega
      · exact hnot _ hs
    · intro j hj
      have hj_ne : j ≠ emb i₀ := fun h => hj (mem_insert.mpr (Or.inl h))
      have hj_not_s : j ∉ s := fun h => hj (mem_insert.mpr (Or.inr h))
      rcases hsurj j hj_not_s with ⟨m, rfl⟩
      have hm_ne : m ≠ i₀ := fun h => hj_ne (congrArg emb h)
      rcases Nat.lt_or_gt_of_ne hm_ne with hlt | hgt
      · refine ⟨m, ?_⟩
        dsimp [emb']
        rw [if_pos hlt]
      · refine ⟨m - 1, ?_⟩
        dsimp [emb']
        rw [if_neg (by omega), Nat.sub_add_cancel (by omega)]

lemma complEmb_preimage_finset {D : Finset ℕ} {emb : ℕ → ℕ} (hemb : IsComplEmb D emb)
    {t : Finset ℕ} (htD : Disjoint t D) :
    ∃ s : Finset ℕ, s.image emb = t := by
  rcases hemb with ⟨hstrict, _, hsurj⟩
  let M := t.sup id + 1
  let s := (range M).filter (fun i => emb i ∈ t)
  refine ⟨s, ?_⟩
  ext j
  simp only [s, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, ⟨_, hit⟩, rfl⟩
    exact hit
  · intro hjt
    have hjD : j ∉ D := Finset.disjoint_left.mp htD hjt
    rcases hsurj j hjD with ⟨i, rfl⟩
    have hi_le : i ≤ emb i := hstrict.id_le i
    have hemb_le : emb i ≤ t.sup id := le_sup (f := id) hjt
    exact ⟨i, ⟨by dsimp [M]; omega, hjt⟩, rfl⟩

lemma subseqSums'_complEmb_updateFinset {A : ℕ → ℕ} {D : Finset ℕ} {emb : ℕ → ℕ}
    (hemb : IsComplEmb D emb) (E : Finset ℕ) :
    subseqSums' (Function.updateFinset (fun i => A (emb i)) E 0) =
      subseqSums' (Function.updateFinset A (D ∪ E.image emb) 0) := by
  rcases hemb with ⟨hstrict, hnot, hsurj⟩
  ext x
  rw [mem_subseqSums'_updateFinset_iff, mem_subseqSums'_updateFinset_iff]
  constructor
  · rintro ⟨s, hsE, rfl⟩
    refine ⟨s.image emb, ?_, ?_⟩
    · rw [disjoint_left]
      intro y hy hDE
      rcases mem_image.mp hy with ⟨i, his, rfl⟩
      rcases mem_union.mp hDE with hD | hE
      · exact hnot i hD
      · rcases mem_image.mp hE with ⟨j, hjE, hij⟩
        have := hstrict.injective hij
        subst this
        exact Finset.disjoint_left.mp hsE his hjE
    · rw [sum_image (fun i _ j _ h => hstrict.injective h)]
  · rintro ⟨t, htDE, rfl⟩
    have htD : Disjoint t D := Disjoint.mono_right subset_union_left htDE
    rcases complEmb_preimage_finset ⟨hstrict, hnot, hsurj⟩ htD with ⟨s, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · rw [disjoint_left]
      intro i his hiE
      exact Finset.disjoint_left.mp htDE (mem_image_of_mem emb his)
        (mem_union_right D (mem_image_of_mem emb hiE))
    · rw [sum_image (fun i _ j _ h => hstrict.injective h)]

lemma prefixSum_complEmb_bound {A : ℕ → ℕ} {D : Finset ℕ} {emb : ℕ → ℕ}
    (hemb : IsComplEmb D emb) (k : ℕ) :
    prefixSum A (emb k) ≤ prefixSum (fun i => A (emb i)) k + ∑ j ∈ D, A j := by
  rcases hemb with ⟨hstrict, hnot, hsurj⟩
  have himg : (range k).image emb = range (emb k) \ D := by
    ext j
    simp only [mem_image, mem_range, mem_sdiff]
    constructor
    · rintro ⟨r, hrk, rfl⟩
      exact ⟨hstrict hrk, hnot r⟩
    · rintro ⟨hjk, hjD⟩
      rcases hsurj j hjD with ⟨r, rfl⟩
      exact ⟨r, hstrict.lt_iff_lt.mp hjk, rfl⟩
  have hsum_img : prefixSum (fun i => A (emb i)) k = ∑ j ∈ range (emb k) \ D, A j := by
    dsimp [prefixSum]
    rw [← himg, sum_image (fun i _ j _ h => hstrict.injective h)]
  have hsub : range (emb k) ⊆ (range (emb k) \ D) ∪ D := by
    intro j hj
    rw [mem_union, mem_sdiff]
    by_cases hjD : j ∈ D
    · exact Or.inr hjD
    · exact Or.inl ⟨hj, hjD⟩
  have hle1 := sum_le_sum_of_subset (f := A) hsub
  rw [sum_union disjoint_sdiff_self_left] at hle1
  rw [hsum_img]
  dsimp [prefixSum]
  omega

/-- Lemma 3 (`lem:slack`): If an unbounded nondecreasing positive integer sequence `A` remains
complete after every single-element deletion, then its prefix slack tends to infinity, and still
tends to infinity after any fixed finite deletion `D`. -/
lemma slack_diverges_of_one_del {A : ℕ → ℕ} (hA_mono : Monotone A) (hA_pos : ∀ i, 1 ≤ A i)
    (hA_unb : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, M ≤ A i)
    (hA1 : ∀ i : ℕ, IsAddCompleteNatSeq' (Function.updateFinset A {i} 0))
    {D : Finset ℕ} {emb : ℕ → ℕ} (hemb : IsComplEmb D emb) :
    ∀ M : ℕ, ∃ K : ℕ, ∀ k ≥ K, A (emb k) + M ≤ prefixSum (fun i => A (emb i)) k := by
  have hA_slack : ∀ M : ℕ, ∃ K : ℕ, ∀ k ≥ K, A k + M ≤ prefixSum A k := by
    intro M
    rcases hA_unb (M + 1) with ⟨i, hiM⟩
    have hi : M + 1 ≤ A i := hiM i (le_refl i)
    have hcomp := (isAddCompleteNatSeq'_iff _).mp (hA1 i)
    rcases hcomp with ⟨T_i, hT_i⟩
    let K := T_i + A i + i + 1
    refine ⟨K, fun k hk => ?_⟩
    have hik : i < k := by omega
    have hkS : k ≤ prefixSum A k := prefixSum_ge_index hA_pos k
    let x := prefixSum A k - A i + 1
    have hxT : T_i ≤ x := by omega
    have hx_mem := hT_i x hxT
    rw [mem_subseqSums'_updateFinset_iff] at hx_mem
    rcases hx_mem with ⟨s, hs_disj, hx_sum⟩
    have hi_notin_s : i ∉ s := Finset.disjoint_right.mp hs_disj (mem_singleton_self i)
    have hs_ge_k : ∃ r ∈ s, k ≤ r := by
      by_contra hall
      have hs_sub : s ⊆ (range k).erase i := by
        intro r hr
        rw [mem_erase, mem_range]
        refine ⟨fun h => hi_notin_s (h ▸ hr), ?_⟩
        by_contra hge
        exact hall ⟨r, hr, by omega⟩
      have hle := sum_le_sum_of_subset (f := A) hs_sub
      have herase := add_sum_erase (range k) A (mem_range.mpr hik)
      dsimp [prefixSum, x] at hx_sum herase
      omega
    rcases hs_ge_k with ⟨r, hr, hrk⟩
    have hAk_le_Ar : A k ≤ A r := hA_mono hrk
    have hAr_le_x : A r ≤ x := by
      rw [hx_sum]
      exact single_le_sum (fun _ _ => Nat.zero_le _) hr
    omega
  intro M
  let C := ∑ j ∈ D, A j
  rcases hA_slack (M + C) with ⟨K, hK⟩
  refine ⟨K, fun k hk => ?_⟩
  have hemb_k : K ≤ emb k := le_trans hk (hemb.1.id_le k)
  have h1 := hK (emb k) hemb_k
  have h2 := prefixSum_complEmb_bound (A := A) hemb k
  omega

/-- Proposition 5 (`prop:extension`): If `A` is an unbounded nondecreasing positive integer
sequence that remains complete after every two-element deletion, then any finite deletion `D`
leaving a complete sequence can be enlarged by one element while retaining completeness. -/
theorem extension_prop {A : ℕ → ℕ} (hA_mono : Monotone A) (hA_pos : ∀ i, 1 ≤ A i)
    (hA_unb : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, M ≤ A i)
    (hA2 : ∀ s : Finset ℕ, s.card = 2 → IsAddCompleteNatSeq' (Function.updateFinset A s 0))
    (D : Finset ℕ) (hD_comp : IsAddCompleteNatSeq' (Function.updateFinset A D 0)) :
    ∃ d ∉ D, IsAddCompleteNatSeq' (Function.updateFinset A (insert d D) 0) := by
  have hA1 : ∀ i : ℕ, IsAddCompleteNatSeq' (Function.updateFinset A {i} 0) := by
    intro i
    have hcard : ({i, i + 1} : Finset ℕ).card = 2 := card_pair (by omega)
    have hsub : ({i} : Finset ℕ) ⊆ {i, i + 1} := singleton_subset_iff.mpr (mem_insert_self i {i + 1})
    exact isAddCompleteNatSeq'_updateFinset_mono hsub (hA2 {i, i + 1} hcard)
  rcases exists_complEmb D with ⟨emb, hemb⟩
  let B : ℕ → ℕ := fun i => A (emb i)
  have hB_mono : Monotone B := fun i j hij => hA_mono (hemb.1.monotone hij)
  have hB_pos : ∀ i, 1 ≤ B i := fun i => hA_pos (emb i)
  have hB_unb : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, M ≤ B i := by
    intro M
    rcases hA_unb M with ⟨I, hI⟩
    exact ⟨I, fun i hi => hI (emb i) (le_trans hi (hemb.1.id_le i))⟩
  have hB_slack : ∀ M : ℕ, ∃ K : ℕ, ∀ k ≥ K, B k + M ≤ prefixSum B k :=
    slack_diverges_of_one_del hA_mono hA_pos hA_unb hA1 hemb
  have hB_sums : subseqSums' B = subseqSums' (Function.updateFinset A D 0) := by
    have h := subseqSums'_complEmb_updateFinset (A := A) hemb ∅
    rw [image_empty, union_empty, Function.updateFinset_empty] at h
    exact h
  have hB_comp_seq : IsAddCompleteNatSeq' B := by
    rw [isAddCompleteNatSeq'_iff, hB_sums, ← isAddCompleteNatSeq'_iff]
    exact hD_comp
  rcases (isAddCompleteNatSeq'_iff B).mp hB_comp_seq with ⟨T₀, hT₀⟩
  let T := max T₀ 1
  have hT : 1 ≤ T := le_max_right T₀ 1
  have hB_comp : ∀ x ≥ T, x ∈ subseqSums' B :=
    fun x hx => hT₀ x (le_trans (le_max_left T₀ 1) hx)
  by_contra h_no_ext
  have hB_min : ∀ j : ℕ, ¬IsAddCompleteNatSeq' (Function.updateFinset B {j} 0) := by
    intro j hj_comp
    apply h_no_ext
    refine ⟨emb j, hemb.2.1 j, ?_⟩
    have h := subseqSums'_complEmb_updateFinset (A := A) hemb {j}
    rw [image_singleton, union_comm, ← insert_eq] at h
    rw [isAddCompleteNatSeq'_iff, ← h, ← isAddCompleteNatSeq'_iff]
    exact hj_comp
  rcases central_interval_thm hB_mono hB_pos hB_unb hB_slack hT hB_comp with ⟨K₀, hK₀⟩
  let C := ∑ d ∈ D, A d
  rcases hB_unb (2 * T + C + 1) with ⟨I₀, hI₀⟩
  let i := I₀
  have hBi : 2 * T + C + 1 ≤ B i := hI₀ i (le_refl i)
  let k := max K₀ (max (i + 1) (2 * T))
  have hkK₀ : K₀ ≤ k := le_max_left _ _
  have hik : i < k := by
    have : i + 1 ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hk2T : 2 * T ≤ prefixSum B k := by
    have h1 : 2 * T ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have h2 : k ≤ prefixSum B k := prefixSum_ge_index hB_pos k
    omega
  have hP_central : ∀ x : ℕ, T ≤ x → x + T ≤ prefixSum B k → x ∈ prefixSums B k :=
    hK₀ k hkK₀
  let Q : Set ℕ := {q | ∃ s : Finset ℕ, (∀ r ∈ s, k < r) ∧ q = ∑ r ∈ s, B r}
  have hP_add_Q : ∀ x ∈ prefixSums B k, ∀ q ∈ Q,
      x + q ∈ subseqSums' (Function.updateFinset B {k} 0) := by
    rintro x ⟨s₁, hs₁, rfl⟩ q ⟨s₂, hs₂, rfl⟩
    rw [mem_subseqSums'_updateFinset_iff]
    have hdisj : Disjoint s₁ s₂ := by
      rw [disjoint_left]
      intro r hr₁ hr₂
      have h1 := mem_range.mp (hs₁ hr₁)
      have h2 := hs₂ r hr₂
      omega
    refine ⟨s₁ ∪ s₂, ?_, (sum_union hdisj).symm⟩
    rw [disjoint_singleton_right, mem_union]
    rintro (h1 | h2)
    · have := mem_range.mp (hs₁ h1)
      omega
    · have := hs₂ k h2
      omega
  let L := prefixSum B k - 2 * T + 1
  have hQ_gap : ∀ M : ℕ, ∃ q ∈ Q, M ≤ q ∧ ∀ q' ∈ Q, q' ≤ q ∨ q + L < q' := by
    intro M
    by_contra h_no_gap
    have h_step : ∀ q ∈ Q, M ≤ q → ∃ q' ∈ Q, q < q' ∧ q' ≤ q + L := by
      intro q hq hMq
      by_contra h_none
      apply h_no_gap
      refine ⟨q, hq, hMq, fun q' hq' => ?_⟩
      by_contra h_mid
      exact h_none ⟨q', hq', by omega, by omega⟩
    rcases hB_unb M with ⟨I₁, hI₁⟩
    let r₀ := max I₁ (k + 1)
    let q₀ := B r₀
    have hq₀_Q : q₀ ∈ Q := by
      refine ⟨{r₀}, fun r hr => ?_, by simp [q₀]⟩
      rw [mem_singleton.mp hr]
      have : k + 1 ≤ r₀ := le_max_right _ _
      omega
    have hq₀_M : M ≤ q₀ := hI₁ r₀ (le_max_left _ _)
    have h_cover : ∀ m : ℕ, ∃ q ∈ Q,
        q₀ ≤ q ∧ q + T ≤ q₀ + T + m ∧ q₀ + T + m ≤ q + (prefixSum B k - T) := by
      intro m
      induction m with
      | zero =>
        exact ⟨q₀, hq₀_Q, le_refl q₀, by omega, by omega⟩
      | succ m ih =>
        rcases ih with ⟨q, hqQ, hq_ge, hq_lo, hq_hi⟩
        by_cases h_stay : q₀ + T + (m + 1) ≤ q + (prefixSum B k - T)
        · exact ⟨q, hqQ, hq_ge, by omega, h_stay⟩
        · rcases h_step q hqQ (by omega) with ⟨q', hq'Q, hqq', hq'L⟩
          exact ⟨q', hq'Q, by omega, by dsimp [L] at hq'L; omega, by omega⟩
    apply hB_min k
    rw [isAddCompleteNatSeq'_iff]
    refine ⟨q₀ + T, fun z hz => ?_⟩
    rcases h_cover (z - (q₀ + T)) with ⟨q, hqQ, _, hq_lo, hq_hi⟩
    have hz_eq : q₀ + T + (z - (q₀ + T)) = z := by omega
    rw [hz_eq] at hq_lo hq_hi
    have hzq_mem : z - q ∈ prefixSums B k :=
      hP_central (z - q) (by omega) (by omega)
    have hsum_mem := hP_add_Q (z - q) hzq_mem q hqQ
    have htarget : z - q + q = z := by omega
    rwa [htarget] at hsum_mem
  let pair : Finset ℕ := {emb i, emb k}
  have hpair_card : pair.card = 2 := by
    apply card_pair
    intro heq
    have := hemb.1.injective heq
    omega
  rcases (isAddCompleteNatSeq'_iff _).mp (hA2 pair hpair_card) with ⟨T_p, hT_p⟩
  rcases hQ_gap T_p with ⟨q, hqQ, hqT_p, hq_gap⟩
  have hBi_le_Sk : B i ≤ prefixSum B k :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr hik)
  let x := q + prefixSum B k - B i + 1 + C
  have hx_ge : T_p ≤ x := by omega
  have hx_mem := hT_p x hx_ge
  rw [mem_subseqSums'_updateFinset_iff] at hx_mem
  rcases hx_mem with ⟨S, hS_disj, hx_sum⟩
  let S_D := S.filter (fun u => u ∈ D)
  let S_B := S.filter (fun u => u ∉ D)
  have hS_union : S = S_D ∪ S_B := by
    ext u
    simp only [S_D, S_B, mem_union, mem_filter]
    by_cases huD : u ∈ D <;> simp [huD]
  have hS_disj_DB : Disjoint S_D S_B := by
    rw [disjoint_filter]
    intro _ _ h1 h2
    exact h2 h1
  rw [hS_union, sum_union hS_disj_DB] at hx_sum
  have hSD_sub : S_D ⊆ D := fun _ hu => (mem_filter.mp hu).2
  have hd_le_C : ∑ u ∈ S_D, A u ≤ C := sum_le_sum_of_subset hSD_sub
  have hSB_disj_D : Disjoint S_B D := by
    rw [disjoint_left]
    intro _ hu
    exact (mem_filter.mp hu).2
  rcases complEmb_preimage_finset hemb hSB_disj_D with ⟨s, hs_img⟩
  have hSB_sum : ∑ u ∈ S_B, A u = ∑ r ∈ s, B r := by
    rw [← hs_img, sum_image (fun r₁ _ r₂ _ h => hemb.1.injective h)]
  have hi_notin_s : i ∉ s := by
    intro his
    have hemb_in : emb i ∈ S := by
      have : emb i ∈ S_B := hs_img ▸ mem_image_of_mem emb his
      exact (mem_filter.mp this).1
    exact Finset.disjoint_left.mp hS_disj hemb_in (mem_insert_self _ _)
  have hk_notin_s : k ∉ s := by
    intro hks
    have hemb_in : emb k ∈ S := by
      have : emb k ∈ S_B := hs_img ▸ mem_image_of_mem emb hks
      exact (mem_filter.mp this).1
    exact Finset.disjoint_left.mp hS_disj hemb_in (mem_insert_of_mem (mem_singleton_self _))
  let s₁ := s.filter (fun r => r < k)
  let s₂ := s.filter (fun r => k < r)
  have hs_union : s = s₁ ∪ s₂ := by
    ext r
    simp only [s₁, s₂, mem_union, mem_filter]
    constructor
    · intro hrs
      have hrk : r ≠ k := fun h => hk_notin_s (h ▸ hrs)
      rcases Nat.lt_or_gt_of_ne hrk with hlt | hgt
      · exact Or.inl ⟨hrs, hlt⟩
      · exact Or.inr ⟨hrs, hgt⟩
    · rintro (⟨hrs, _⟩ | ⟨hrs, _⟩) <;> exact hrs
  have hs_disj : Disjoint s₁ s₂ := by
    rw [disjoint_filter]
    intro _ _ h1 h2
    omega
  rw [hSB_sum, hs_union, sum_union hs_disj] at hx_sum
  have hs₁_sub : s₁ ⊆ (range k).erase i := by
    intro r hr
    rw [mem_erase, mem_range]
    rcases mem_filter.mp hr with ⟨hrs, hrk⟩
    exact ⟨fun h => hi_notin_s (h ▸ hrs), hrk⟩
  have hf_le : ∑ r ∈ s₁, B r + B i ≤ prefixSum B k := by
    have hle := sum_le_sum_of_subset (f := B) hs₁_sub
    have herase := add_sum_erase (range k) B (mem_range.mpr hik)
    dsimp [prefixSum]
    omega
  let q' := ∑ r ∈ s₂, B r
  have hq'_Q : q' ∈ Q := ⟨s₂, fun r hr => (mem_filter.mp hr).2, rfl⟩
  rcases hq_gap q' hq'_Q with hle_q | hgt_q
  · dsimp [x, q'] at hx_sum hle_q
    omega
  · dsimp [x, L, q'] at hx_sum hgt_q
    omega

lemma exists_complete_deletion_of_two_del {A : ℕ → ℕ} (hA_mono : Monotone A)
    (hA_pos : ∀ i, 1 ≤ A i) (hA_unb : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, M ≤ A i)
    (hA2 : ∀ s : Finset ℕ, s.card = 2 → IsAddCompleteNatSeq' (Function.updateFinset A s 0))
    (r : ℕ) :
    ∃ D : Finset ℕ, D.card = r ∧ IsAddCompleteNatSeq' (Function.updateFinset A D 0) := by
  induction r with
  | zero =>
    refine ⟨∅, card_empty, ?_⟩
    have hcard : ({0, 1} : Finset ℕ).card = 2 := card_pair (by omega)
    exact isAddCompleteNatSeq'_updateFinset_mono (empty_subset _) (hA2 {0, 1} hcard)
  | succ r ih =>
    rcases ih with ⟨D, hDcard, hDcomp⟩
    rcases extension_prop hA_mono hA_pos hA_unb hA2 D hDcomp with ⟨d, hdD, hcomp'⟩
    exact ⟨insert d D, by rw [card_insert_of_notMem hdD, hDcard], hcomp'⟩

/-! ### Exclusion of `m ≥ 2` and Main Theorem `erdos_348` -/

lemma exists_superset_card {s : Finset ℕ} {m : ℕ} (hsm : s.card ≤ m) :
    ∃ s' : Finset ℕ, s ⊆ s' ∧ s'.card = m := by
  induction m with
  | zero =>
    have : s.card = 0 := by omega
    exact ⟨s, Subset.refl s, this⟩
  | succ m ih =>
    rcases eq_or_lt_of_le hsm with heq | hlt
    · exact ⟨s, Subset.refl s, heq⟩
    · rcases ih (by omega) with ⟨s', hss', hs'card⟩
      let x := s'.sup id + 1
      have hx : x ∉ s' := by
        intro hx_in
        have := le_sup (f := id) hx_in
        dsimp [x] at this
        omega
      exact ⟨insert x s', Subset.trans hss' (subset_insert x s'),
        by rw [card_insert_of_notMem hx, hs'card]⟩

lemma eventually_const_of_monotone_bdd {a : ℕ → ℕ} (ha : Monotone a) (M : ℕ)
    (hM : ∀ i, a i ≤ M) :
    ∃ k₀ : ℕ, ∀ i ≥ k₀, a i = a k₀ := by
  suffices ∀ d : ℕ, ∀ j : ℕ, M - a j ≤ d → ∃ k₀ : ℕ, ∀ i ≥ k₀, a i = a k₀ by
    exact this (M - a 0) 0 (le_refl _)
  intro d
  induction d with
  | zero =>
    intro j hj
    refine ⟨j, fun i hi => ?_⟩
    have h1 : a j ≤ a i := ha hi
    have h2 : a i ≤ M := hM i
    omega
  | succ d ih =>
    intro j hj
    by_cases hconst : ∀ i ≥ j, a i = a j
    · exact ⟨j, hconst⟩
    · have hex : ∃ j' ≥ j, a j < a j' := by
        by_contra hall
        apply hconst
        intro i hi
        have h1 : a j ≤ a i := ha hi
        have h2 : ¬(a j < a i) := fun hlt => hall ⟨i, hi, hlt⟩
        omega
      rcases hex with ⟨j', _, hlt⟩
      exact ih j' (by omega)

lemma shift_updateFinset_subseqSums' {a : ℕ → ℕ} {k₀ : ℕ} (h0 : ∀ j < k₀, a j = 0)
    (D : Finset ℕ) :
    subseqSums' (Function.updateFinset (fun i => a (k₀ + i)) D 0) =
      subseqSums' (Function.updateFinset a (D.image (fun i => k₀ + i)) 0) := by
  ext x
  rw [mem_subseqSums'_updateFinset_iff, mem_subseqSums'_updateFinset_iff]
  constructor
  · rintro ⟨B, hBD, rfl⟩
    refine ⟨B.image (fun i => k₀ + i), ?_, ?_⟩
    · rw [disjoint_left]
      intro y hy₁ hy₂
      rcases mem_image.mp hy₁ with ⟨i₁, hi₁, rfl⟩
      rcases mem_image.mp hy₂ with ⟨i₂, hi₂, heq⟩
      have : i₁ = i₂ := by omega
      subst this
      exact Finset.disjoint_left.mp hBD hi₁ hi₂
    · rw [sum_image (fun i₁ _ i₂ _ h => by omega)]
  · rintro ⟨B, hBD, rfl⟩
    let B₂ := B.filter (fun j => k₀ ≤ j)
    have hsum_eq : ∑ j ∈ B, a j = ∑ j ∈ B₂, a j := by
      rw [← sum_filter_add_sum_filter_not B (fun j => k₀ ≤ j)]
      have hzero : ∑ j ∈ B.filter (fun j => ¬k₀ ≤ j), a j = 0 := by
        apply sum_eq_zero
        intro j hj
        rw [mem_filter] at hj
        exact h0 j (by omega)
      change ∑ j ∈ B₂, a j + ∑ j ∈ B.filter (fun j => ¬k₀ ≤ j), a j = ∑ j ∈ B₂, a j
      omega
    rw [hsum_eq]
    let B' := B₂.image (fun j => j - k₀)
    refine ⟨B', ?_, ?_⟩
    · rw [disjoint_left]
      intro i hiB' hiD
      rcases mem_image.mp hiB' with ⟨j, hjB₂, rfl⟩
      rw [mem_filter] at hjB₂
      have hj_eq : k₀ + (j - k₀) = j := by omega
      have hj_in_img : j ∈ D.image (fun i => k₀ + i) := by
        rw [← hj_eq]
        exact mem_image_of_mem _ hiD
      exact Finset.disjoint_left.mp hBD hjB₂.1 hj_in_img
    · rw [sum_image]
      · apply sum_congr rfl
        intro j hj
        rw [mem_filter] at hj
        congr 1
        omega
      · intro j₁ hj₁ j₂ hj₂ heq
        rw [mem_coe, mem_filter] at hj₁ hj₂
        dsimp at heq
        omega

theorem not_exists_for_m_ge_two {m n : ℕ} (hmn : m < n) (hm2 : 2 ≤ m)
    (a : ℕ → ℕ) (ha : Monotone a)
    (hm : ∀ s : Finset ℕ, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
    (hn : ∀ t : Finset ℕ, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) :
    False := by
  have ha_dle : ∀ s : Finset ℕ, s.card ≤ m →
      IsAddCompleteNatSeq' (Function.updateFinset a s 0) := by
    intro s hsm
    rcases exists_superset_card hsm with ⟨s', hss', hs'm⟩
    exact isAddCompleteNatSeq'_updateFinset_mono hss' (hm s' hs'm)
  have ha_unb : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, M ≤ a i := by
    intro M
    by_contra hbdd
    have h_all_lt : ∀ i, a i ≤ M := by
      intro i
      by_contra hge
      exact hbdd ⟨i, fun j hj => le_trans (by omega : M ≤ a i) (ha hj)⟩
    rcases eventually_const_of_monotone_bdd ha M h_all_lt with ⟨k₀, hk₀⟩
    let t := Ico k₀ (k₀ + n)
    have ht_card : t.card = n := by simp [t]
    apply hn t ht_card
    have ha0 : IsAddCompleteNatSeq' a := by
      simpa using ha_dle ∅ (by simp)
    filter_upwards [ha0] with x hx
    rcases hx with ⟨B, rfl⟩
    rw [mem_subseqSums'_updateFinset_iff]
    let B₁ := B.filter (fun i => i < k₀)
    let B₂ := B.filter (fun i => k₀ ≤ i)
    have hB_union : B = B₁ ∪ B₂ := by
      ext i
      simp only [B₁, B₂, mem_union, mem_filter]
      by_cases hik : i < k₀ <;> [exact ⟨fun h => Or.inl ⟨h, hik⟩, by tauto⟩;
        exact ⟨fun h => Or.inr ⟨h, by omega⟩, by tauto⟩]
    have hB_disj : Disjoint B₁ B₂ := by
      rw [disjoint_filter]
      intro _ _ h1 h2
      omega
    let B₂' := B₂.image (fun i => i + n)
    have hdisj' : Disjoint B₁ B₂' := by
      rw [disjoint_left]
      intro i hi₁ hi₂
      rcases mem_image.mp hi₂ with ⟨j, hj₂, rfl⟩
      have h1 := (mem_filter.mp hi₁).2
      have h2 := (mem_filter.mp hj₂).2
      omega
    refine ⟨B₁ ∪ B₂', ?_, ?_⟩
    · rw [disjoint_left]
      intro i hi hit
      rw [mem_Ico] at hit
      rcases mem_union.mp hi with hi₁ | hi₂
      · have := (mem_filter.mp hi₁).2
        omega
      · rcases mem_image.mp hi₂ with ⟨j, hj₂, rfl⟩
        have := (mem_filter.mp hj₂).2
        omega
    · rw [ hB_union, sum_union hB_disj, sum_union hdisj']
      congr 1
      rw [sum_image (fun i₁ _ i₂ _ h => by omega)]
      apply sum_congr rfl
      intro i hi
      have hik : k₀ ≤ i := (mem_filter.mp hi).2
      rw [hk₀ i hik, hk₀ (i + n) (by omega)]
  rcases ha_unb 1 with ⟨I₁, hI₁⟩
  have hex_first_pos : ∃ k₀ ≤ I₁, 1 ≤ a k₀ ∧ ∀ j < k₀, a j = 0 := by
    suffices ∀ m : ℕ, 1 ≤ a m → ∃ k₀ ≤ m, 1 ≤ a k₀ ∧ ∀ j < k₀, a j = 0 by
      exact this I₁ (hI₁ I₁ (le_refl I₁))
    intro m
    induction m with
    | zero =>
      intro h0
      exact ⟨0, le_refl 0, h0, fun _ hj => by omega⟩
    | succ m ih =>
      intro hm1
      by_cases hprev : 1 ≤ a m
      · rcases ih hprev with ⟨k₀, hk₀m, hk₀1, hk₀0⟩
        exact ⟨k₀, by omega, hk₀1, hk₀0⟩
      · refine ⟨m + 1, le_refl (m + 1), hm1, fun j hj => ?_⟩
        have : a j ≤ a m := ha (by omega)
        omega
  rcases hex_first_pos with ⟨k₀, _, hk₀_pos, hk₀_zero⟩
  let A : ℕ → ℕ := fun i => a (k₀ + i)
  have hA_mono : Monotone A := fun i j hij => ha (by omega)
  have hA_pos : ∀ i, 1 ≤ A i := fun i => le_trans hk₀_pos (ha (by omega))
  have hA_unb : ∀ M : ℕ, ∃ I : ℕ, ∀ i ≥ I, M ≤ A i := by
    intro M
    rcases ha_unb M with ⟨I, hI⟩
    exact ⟨I, fun i hi => hI (k₀ + i) (by omega)⟩
  have hA2 : ∀ s : Finset ℕ, s.card = 2 → IsAddCompleteNatSeq' (Function.updateFinset A s 0) := by
    intro s hs2
    rw [isAddCompleteNatSeq'_iff, shift_updateFinset_subseqSums' hk₀_zero s,
      ← isAddCompleteNatSeq'_iff]
    apply ha_dle
    rw [card_image_of_injective s (fun i₁ i₂ h => by omega), hs2]
    exact hm2
  rcases exists_complete_deletion_of_two_del hA_mono hA_pos hA_unb hA2 n with
    ⟨D, hDcard, hDcomp⟩
  let t := D.image (fun i => k₀ + i)
  have ht_card : t.card = n := by
    rw [card_image_of_injective D (fun i₁ i₂ h => by omega), hDcard]
  apply hn t ht_card
  rw [isAddCompleteNatSeq'_iff, ← shift_updateFinset_subseqSums' hk₀_zero D,
    ← isAddCompleteNatSeq'_iff]
  exact hDcomp

/--
For what values of $0 \leq m < n$ is there a complete sequence
$A = \{a_1 \leq a_2 \leq \cdots\}$ of integers such that
 1. $A$ remains complete after removing any $m$ elements, but
 2. $A$ is not complete after removing any $n$ elements.

Geneson [Ge26, Theorem 1] proved that the pairs are exactly those with $m \leq 1$.
Completeness allows finitely many exceptions, and deletions remove indexed occurrences.
-/
theorem erdos_348 :
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
        (_ : ∀ t, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) } =
    erdos_348.answer := by
  ext ⟨m, n⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, erdos_348.answer]
  constructor
  · rintro ⟨m', n', hmn, a, ha, hm, hn, rfl, rfl⟩
    refine ⟨hmn, ?_⟩
    by_contra hm_gt
    exact not_exists_for_m_ge_two hmn (by omega) a ha hm hn
  · rintro ⟨hmn, hm1⟩
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · rcases exists_for_m_eq_zero hmn with ⟨a, ha, hm, hn⟩
      exact ⟨0, n, hmn, a, ha, hm, hn, rfl, rfl⟩
    · rcases exists_for_m_eq_one hmn with ⟨a, ha, hm, hn⟩
      exact ⟨1, n, hmn, a, ha, hm, hn, rfl, rfl⟩

end Erdos348

#print axioms Erdos348.erdos_348

