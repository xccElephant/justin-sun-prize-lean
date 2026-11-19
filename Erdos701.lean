/-
Copyright 2025 The Formal Conjectures Authors (statement signature of `Erdos701.erdos_701`,
adapted from `google-deepmind/formal-conjectures` commit `b576d527b271b936f9e61c0e367c302d7386bc80`).
Copyright 2026 Chucheng Xiang (@xccElephant) (100% clean-room Lean 4 proof and auxiliary theorems).
SPDX-License-Identifier: Apache-2.0

Complete, unconditional, 100% clean-room Lean 4 (`v4.33.1`) formalization of Chvátal's Conjecture
(`Erdős Problem #701` / `JSP-000571`).

Mathematical credits (zero mathematical-solver priority claimed):
- Original conjecture: Václav Chvátal (1972/1974, `[Ch74]`, Lecture Notes in Math. 411, pp. 61–66);
  featured by Paul Erdős (`[Er81]`, Combinatorica 1 (1981), 25–42).
- Mathematical resolution (September 2026 preprints):
  1. Fan Chang, Hong Liu, and Miao Liu, *A proof of Chvátal's conjecture via a sharp correlation
     inequality*, arXiv:2609.19123 (16 September 2026).
  2. Peter Keevash, *On Kahn's flow conjecture*, arXiv:2609.23595 (20 September 2026).
  3. David Ellis, Yuval Filmus, and Ehud Friedgut, *Chvátal's conjecture: a proof from The Book*,
     arXiv:2609.28404 (23 September 2026).
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Order.UpperLower.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos701

open Cardinal
open scoped BigOperators Classical

noncomputable def boolChar {X : Type*} [DecidableEq X] (S T : Finset X) : ℝ :=
  (-1 : ℝ) ^ (S ∩ T).card

lemma boolChar_symm {X : Type*} [DecidableEq X] (S T : Finset X) :
    boolChar S T = boolChar T S := by
  simp only [boolChar, Finset.inter_comm]

lemma boolChar_empty_left {X : Type*} [DecidableEq X] (T : Finset X) :
    boolChar ∅ T = 1 := by
  simp [boolChar]

lemma boolChar_symmDiff {X : Type*} [DecidableEq X] (A B T : Finset X) :
    boolChar (symmDiff A B) T = boolChar A T * boolChar B T := by
  let U := A ∩ T
  let V := B ∩ T
  have hinter : symmDiff A B ∩ T = symmDiff U V := by
    ext x
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> by_cases hxT : x ∈ T <;>
      simp [U, V, Finset.mem_symmDiff, hxA, hxB, hxT]
  have hcard : (symmDiff U V).card + 2 * (U ∩ V).card = U.card + V.card := by
    have hdisj : Disjoint (U \ V) (V \ U) := disjoint_sdiff_sdiff
    have hsd : symmDiff U V = (U \ V) ∪ (V \ U) := rfl
    have hc1 := Finset.card_sdiff_add_card_inter U V
    have hc2 := Finset.card_sdiff_add_card_inter V U
    rw [Finset.inter_comm V U] at hc2
    rw [hsd, Finset.card_union_of_disjoint hdisj]
    omega
  simp only [boolChar, hinter]
  change (-1 : ℝ) ^ (symmDiff U V).card = (-1 : ℝ) ^ U.card * (-1 : ℝ) ^ V.card
  rw [← pow_add, ← hcard, pow_add, pow_mul]
  norm_num

lemma sum_boolChar_powerset {X : Type*} [DecidableEq X] (M B : Finset X) :
    (∑ C ∈ M.powerset, boolChar B C) = if B ∩ M = ∅ then (2 : ℝ) ^ M.card else 0 := by
  split_ifs with hempty
  · have h1 : ∀ C ∈ M.powerset, boolChar B C = 1 := by
      intro C hC
      rw [Finset.mem_powerset] at hC
      have hBC : B ∩ C = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => by
        have : x ∈ B ∩ M := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hC (Finset.mem_inter.mp hx).2⟩
        rw [hempty] at this; exact Finset.notMem_empty x this
      simp [boolChar, hBC]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_powerset]
    simp
  · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases Finset.mem_inter.mp hx₀ with ⟨hx₀B, hx₀M⟩
    let flip : Finset X → Finset X := fun C => if x₀ ∈ C then C.erase x₀ else insert x₀ C
    have hflip_mem : ∀ C ∈ M.powerset, flip C ∈ M.powerset := by
      intro C hC; rw [Finset.mem_powerset] at hC ⊢
      dsimp [flip]; split_ifs with hxC
      · exact subset_trans (Finset.erase_subset x₀ C) hC
      · exact Finset.insert_subset_iff.mpr ⟨hx₀M, hC⟩
    have hflip_inv : ∀ C : Finset X, flip (flip C) = C := by
      intro C; dsimp [flip]
      by_cases hxC : x₀ ∈ C
      · rw [if_pos hxC, if_neg (Finset.notMem_erase x₀ C), Finset.insert_erase hxC]
      · rw [if_neg hxC, if_pos (Finset.mem_insert_self x₀ C), Finset.erase_insert hxC]
    have hflip_sign : ∀ C : Finset X, boolChar B (flip C) = - boolChar B C := by
      intro C; dsimp [flip]
      by_cases hxC : x₀ ∈ C
      · rw [if_pos hxC]
        have hinter_er : B ∩ C.erase x₀ = (B ∩ C).erase x₀ := by
          ext y; simp only [Finset.mem_inter, Finset.mem_erase]; exact and_left_comm
        have hxBC : x₀ ∈ B ∩ C := Finset.mem_inter.mpr ⟨hx₀B, hxC⟩
        have hcard_er : (B ∩ C).card = ((B ∩ C).erase x₀).card + 1 :=
          (Finset.card_erase_add_one hxBC).symm
        simp only [boolChar, hinter_er, hcard_er, pow_succ]
        ring
      · rw [if_neg hxC]
        have hinter_ins : B ∩ insert x₀ C = insert x₀ (B ∩ C) := by
          ext y; simp only [Finset.mem_inter, Finset.mem_insert]
          exact ⟨fun ⟨hyB, hy⟩ => hy.elim Or.inl (fun h => Or.inr ⟨hyB, h⟩),
            fun h => h.elim (fun hy0 => ⟨hy0 ▸ hx₀B, Or.inl hy0⟩) (fun ⟨hyB, hyC⟩ => ⟨hyB, Or.inr hyC⟩)⟩
        have hxBC : x₀ ∉ B ∩ C := fun h => hxC (Finset.mem_inter.mp h).2
        simp only [boolChar, hinter_ins, Finset.card_insert_of_notMem hxBC, pow_succ]
        ring
    have hsum_eq : (∑ C ∈ M.powerset, boolChar B C) = ∑ C ∈ M.powerset, boolChar B (flip C) := by
      refine Finset.sum_bij (fun C _ => flip C) hflip_mem ?_ ?_ ?_
      · intro C₁ _ C₂ _ heq
        have := congrArg flip heq; rwa [hflip_inv, hflip_inv] at this
      · intro C hC
        exact ⟨flip C, hflip_mem C hC, hflip_inv C⟩
      · intro C _; rw [hflip_inv C]
    simp_rw [hflip_sign, Finset.sum_neg_distrib] at hsum_eq
    linarith

lemma bool_parseval {X : Type*} [Fintype X] [DecidableEq X] (h : Finset X → ℝ) :
    let N : ℝ := (2 : ℝ) ^ Fintype.card X
    let hHat : Finset X → ℝ := fun S => (∑ T : Finset X, h T * boolChar S T) / N
    ∑ S : Finset X, (hHat S) ^ 2 = (∑ T : Finset X, (h T) ^ 2) / N := by
  intro N hHat
  have hN_pos : 0 < N := by dsimp [N]; positivity
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have huniv_pow : (Finset.univ : Finset X).powerset = (Finset.univ : Finset (Finset X)) := by
    ext S; simp
  have horth : ∀ T₁ T₂ : Finset X,
      (∑ S : Finset X, boolChar S T₁ * boolChar S T₂) = if T₁ = T₂ then N else 0 := by
    intro T₁ T₂
    have h1 : ∀ S : Finset X, boolChar S T₁ * boolChar S T₂ = boolChar (symmDiff T₁ T₂) S := by
      intro S
      rw [boolChar_symm S T₁, boolChar_symm S T₂, ← boolChar_symmDiff]
    simp_rw [h1, ← huniv_pow]
    rw [sum_boolChar_powerset, Finset.inter_univ]
    have hcard_u : (Finset.univ : Finset X).card = Fintype.card X := Finset.card_univ
    rw [hcard_u]
    have hiff : symmDiff T₁ T₂ = ∅ ↔ T₁ = T₂ := symmDiff_eq_bot
    by_cases h12 : T₁ = T₂
    · rw [if_pos (hiff.mpr h12), if_pos h12]
    · rw [if_neg (mt hiff.mp h12), if_neg h12]
  have hexp : ∑ S : Finset X, (hHat S) ^ 2 =
      (1 / N ^ 2) * ∑ T₁ : Finset X, ∑ T₂ : Finset X,
        h T₁ * h T₂ * (∑ S : Finset X, boolChar S T₁ * boolChar S T₂) := by
    have hsq : ∀ S : Finset X, (hHat S) ^ 2 =
        (1 / N ^ 2) * ∑ T₁ : Finset X, ∑ T₂ : Finset X, (h T₁ * h T₂ * (boolChar S T₁ * boolChar S T₂)) := by
      intro S; dsimp [hHat]
      rw [div_pow, div_eq_mul_inv, mul_comm _ ((N ^ 2)⁻¹), one_div]
      conv_lhs => arg 2; rw [sq, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun T₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T₂ _ => by ring
    simp_rw [hsq, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T₂ _ => by rw [← Finset.mul_sum]
  rw [hexp]
  simp_rw [horth]
  have hdiag : ∀ T₁ : Finset X,
      (∑ T₂ : Finset X, h T₁ * h T₂ * (if T₁ = T₂ then N else 0)) = (h T₁) ^ 2 * N := by
    intro T₁
    have hc : ∀ T₂ ∈ (Finset.univ : Finset (Finset X)),
        h T₁ * h T₂ * (if T₁ = T₂ then N else 0) = if T₂ = T₁ then (h T₁) ^ 2 * N else 0 := by
      intro T₂ _
      by_cases h12 : T₁ = T₂
      · subst h12; simp [sq]
      · have h21 : T₂ ≠ T₁ := Ne.symm h12
        simp [h12, h21]
    rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq' Finset.univ T₁]
    simp
  simp_rw [hdiag, ← Finset.sum_mul]
  field_simp

lemma chvatal_ub_and_eigen_identities {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (D I : Finset (Finset X))
    (hD_down : ∀ A ∈ D, ∀ B : Finset X, B ⊆ A → B ∈ D)
    (hID : I ⊆ D)
    (hI_inter : ∀ A ∈ I, ∀ B ∈ I, (A ∩ B).Nonempty) :
    let N : ℝ := (2 : ℝ) ^ Fintype.card X
    let U : Finset (Finset X) := (Finset.univ : Finset (Finset X)).filter (fun T => ∃ B ∈ I, B ⊆ T)
    let h : Finset X → ℝ := fun T => if T ∈ U then 1 else if Tᶜ ∈ U then -1 else 0
    let hHat : Finset X → ℝ := fun S => (∑ T : Finset X, h T * boolChar S T) / N
    (∃ x₀ : X, ∑ A ∈ D, ∑ B ∈ D, (hHat (symmDiff A B)) ^ 2 ≤
      2 * ((D.filter (x₀ ∈ ·)).card : ℝ)) ∧
    (∀ A ∈ I, ∀ B ∈ D,
      (∑ C ∈ D, hHat (symmDiff B C) * (if C ⊆ A then (1 : ℝ) else 0)) =
        - (if B ⊆ A then (1 : ℝ) else 0)) ∧
    (∀ A ∈ I, ∀ B ∈ D,
      (∑ C ∈ D, hHat (symmDiff B C) * (boolChar Finset.univ C * (if C ⊆ A then (1 : ℝ) else 0))) =
        boolChar Finset.univ B * (if B ⊆ A then (1 : ℝ) else 0)) := by
  intro N U h hHat
  have hN_pos : 0 < N := by dsimp [N]; positivity
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hU_disj : ∀ T : Finset X, ¬ (T ∈ U ∧ Tᶜ ∈ U) := by
    rintro T ⟨h1, h2⟩
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases h1 with ⟨B₁, hB₁, hsub₁⟩
    rcases h2 with ⟨B₂, hB₂, hsub₂⟩
    obtain ⟨x, hx⟩ := hI_inter B₁ hB₁ B₂ hB₂
    rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
    exact (Finset.mem_compl.mp (hsub₂ hx2)) (hsub₁ hx1)
  have hh_anti : ∀ T : Finset X, h Tᶜ = - h T := by
    intro T; dsimp [h]
    rw [compl_compl]
    by_cases h1 : T ∈ U
    · have h2 : Tᶜ ∉ U := fun hc => hU_disj T ⟨h1, hc⟩
      simp [h1, h2]
    · by_cases h2 : Tᶜ ∈ U <;> simp [h1, h2]
  have hhHat_empty : hHat ∅ = 0 := by
    dsimp [hHat]
    simp_rw [boolChar_empty_left, mul_one]
    have hsum0 : (∑ T : Finset X, h T) = 0 := by
      have hbij : (∑ T : Finset X, h T) = ∑ T : Finset X, h Tᶜ := by
        refine Finset.sum_bij (fun T _ => Tᶜ) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ heq => compl_injective heq)
          (fun T _ => ⟨Tᶜ, Finset.mem_univ _, compl_compl T⟩)
          (fun T _ => by rw [compl_compl])
      simp_rw [hh_anti, Finset.sum_neg_distrib] at hbij
      linarith
    rw [hsum0, zero_div]
  have hhHat_l2 : ∑ S : Finset X, (hHat S) ^ 2 ≤ 1 := by
    rw [bool_parseval h]
    rw [div_le_one hN_pos]
    have hle1 : ∀ T ∈ (Finset.univ : Finset (Finset X)), (h T) ^ 2 ≤ 1 := by
      intro T _; dsimp [h]; split_ifs <;> norm_num
    have hsum_le := Finset.sum_le_sum hle1
    simpa [N, Fintype.card_finset] using hsum_le
  refine ⟨?_, ?_, ?_⟩
  · -- Proof of `(UB)`: choose `x₀ : X` maximizing `|S_x| = (D.filter (x ∈ ·)).card`
    obtain ⟨x₀, _, hx₀_max⟩ := Finset.exists_max_image (Finset.univ : Finset X)
      (fun x => (D.filter (x ∈ ·)).card) Finset.univ_nonempty
    refine ⟨x₀, ?_⟩
    set M := ((D.filter (x₀ ∈ ·)).card : ℝ)
    have hpair_count : ∀ T : Finset X, T ≠ ∅ →
        (((D ×ˢ D).filter (fun pq => symmDiff pq.1 pq.2 = T)).card : ℝ) ≤ 2 * M := by
      intro T hT_ne
      obtain ⟨i, hiT⟩ := Finset.nonempty_iff_ne_empty.mpr hT_ne
      let Si := D.filter (i ∈ ·)
      let P := (D ×ˢ D).filter (fun pq => symmDiff pq.1 pq.2 = T)
      let P1 := P.filter (fun pq => i ∈ pq.1)
      let P2 := P.filter (fun pq => i ∉ pq.1)
      have hpart : P = P1 ∪ P2 := by
        ext pq; simp only [Finset.mem_union, P1, P2, Finset.mem_filter]
        exact ⟨fun hp => if h : i ∈ pq.1 then Or.inl ⟨hp, h⟩ else Or.inr ⟨hp, h⟩,
          fun h => h.elim And.left And.left⟩
      have hdisj : Disjoint P1 P2 := by
        rw [Finset.disjoint_left]; intro pq h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hP1_le : P1.card ≤ Si.card := by
        have hinj1 : Set.InjOn Prod.fst (P1 : Set (Finset X × Finset X)) := by
          rintro ⟨A₁, B₁⟩ h1 ⟨A₂, B₂⟩ h2 hA
          dsimp at hA; subst hA
          rw [Finset.mem_coe] at h1 h2
          have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
          have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
          have hB : B₁ = symmDiff A₁ T := by rw [← e1, symmDiff_symmDiff_cancel_left]
          have hB' : B₂ = symmDiff A₁ T := by rw [← e2, symmDiff_symmDiff_cancel_left]
          exact Prod.ext rfl (hB.trans hB'.symm)
        rw [← Finset.card_image_of_injOn hinj1]
        exact Finset.card_le_card fun A hA => by
          rcases Finset.mem_image.mp hA with ⟨⟨A', B'⟩, hp, rfl⟩
          rcases Finset.mem_filter.mp hp with ⟨hpP, hiA⟩
          exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hpP).1).1, hiA⟩
      have hP2_le : P2.card ≤ Si.card := by
        have hinj2 : Set.InjOn Prod.snd (P2 : Set (Finset X × Finset X)) := by
          rintro ⟨A₁, B₁⟩ h1 ⟨A₂, B₂⟩ h2 hB
          dsimp at hB; subst hB
          rw [Finset.mem_coe] at h1 h2
          have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
          have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
          have hA1 : A₁ = symmDiff T B₁ := by rw [← e1, symmDiff_symmDiff_cancel_right]
          have hA2 : A₂ = symmDiff T B₁ := by rw [← e2, symmDiff_symmDiff_cancel_right]
          exact Prod.ext (hA1.trans hA2.symm) rfl
        rw [← Finset.card_image_of_injOn hinj2]
        exact Finset.card_le_card fun B hB => by
          rcases Finset.mem_image.mp hB with ⟨⟨A', B'⟩, hp, rfl⟩
          rcases Finset.mem_filter.mp hp with ⟨hpP, hniA⟩
          rcases Finset.mem_filter.mp hpP with ⟨hpDD, hsd⟩
          have hiB : i ∈ B' := by
            have hi_sd : i ∈ symmDiff A' B' := hsd ▸ hiT
            rw [Finset.mem_symmDiff] at hi_sd
            rcases hi_sd with ⟨hiA, _⟩ | ⟨hiB, _⟩
            · exact False.elim (hniA hiA)
            · exact hiB
          exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hpDD).2, hiB⟩
      have hSi_le : Si.card ≤ (D.filter (x₀ ∈ ·)).card := hx₀_max i (Finset.mem_univ i)
      have hP_le : P.card ≤ 2 * (D.filter (x₀ ∈ ·)).card := by
        rw [hpart, Finset.card_union_of_disjoint hdisj]; omega
      change (P.card : ℝ) ≤ 2 * M
      dsimp [M]; exact_mod_cast hP_le
    -- Fiber decomposition of `∑ A ∈ D, ∑ B ∈ D, (hHat (symmDiff A B))^2` over `T : Finset X`
    have hfiber : ∑ A ∈ D, ∑ B ∈ D, (hHat (symmDiff A B)) ^ 2 =
        ∑ T : Finset X, (((D ×ˢ D).filter (fun pq => symmDiff pq.1 pq.2 = T)).card : ℝ) *
          (hHat T) ^ 2 := by
      rw [← Finset.sum_product']
      have hsplit : ∀ pq ∈ D ×ˢ D, (hHat (symmDiff pq.1 pq.2)) ^ 2 =
          ∑ T : Finset X, if symmDiff pq.1 pq.2 = T then (hHat T) ^ 2 else 0 := by
        intro pq _
        rw [Finset.sum_ite_eq Finset.univ (symmDiff pq.1 pq.2)]
        simp
      rw [Finset.sum_congr rfl hsplit, Finset.sum_comm]
      refine Finset.sum_congr rfl fun T _ => ?_
      simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hfiber]
    have hterm_le : ∀ T ∈ (Finset.univ : Finset (Finset X)),
        (((D ×ˢ D).filter (fun pq => symmDiff pq.1 pq.2 = T)).card : ℝ) * (hHat T) ^ 2 ≤
          (2 * M) * (hHat T) ^ 2 := by
      intro T _
      by_cases hT0 : T = ∅
      · subst hT0; rw [hhHat_empty]; norm_num
      · exact mul_le_mul_of_nonneg_right (hpair_count T hT0) (sq_nonneg _)
    calc ∑ T : Finset X, (((D ×ˢ D).filter (fun pq => symmDiff pq.1 pq.2 = T)).card : ℝ) * (hHat T) ^ 2
      _ ≤ ∑ T : Finset X, (2 * M) * (hHat T) ^ 2 := Finset.sum_le_sum hterm_le
      _ = (2 * M) * ∑ T : Finset X, (hHat T) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * M) * 1 := mul_le_mul_of_nonneg_left hhHat_l2 (by dsimp [M]; positivity)
      _ = 2 * M := mul_one _
  · -- Proof of `(H p_A)(B) = - p_A(B)` in physical space
    intro A hAI B hBD
    have hpow_sub : A.powerset ⊆ D := fun C hC =>
      hD_down A (hID hAI) C (Finset.mem_powerset.mp hC)
    have hsum_D : (∑ C ∈ D, hHat (symmDiff B C) * (if C ⊆ A then (1 : ℝ) else 0)) =
        ∑ C ∈ A.powerset, hHat (symmDiff B C) := by
      have h1 : ∀ C ∈ D, hHat (symmDiff B C) * (if C ⊆ A then (1 : ℝ) else 0) =
          if C ⊆ A then hHat (symmDiff B C) else 0 := by intro C _; split_ifs <;> ring
      rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
      have hfilt : (D.filter (fun C => C ⊆ A)) = A.powerset := by
        ext C; simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨And.right, fun hCA => ⟨hD_down A (hID hAI) C hCA, hCA⟩⟩
      rw [hfilt]
    rw [hsum_D]
    have hexp : ∑ C ∈ A.powerset, hHat (symmDiff B C) =
        (1 / N) * ∑ T : Finset X, h T * boolChar B T * (∑ C ∈ A.powerset, boolChar T C) := by
      dsimp [hHat]
      have h1 : ∀ C ∈ A.powerset, (∑ T : Finset X, h T * boolChar (symmDiff B C) T) / N =
          (1 / N) * ∑ T : Finset X, h T * boolChar B T * boolChar T C := by
        intro C _; rw [div_eq_mul_inv, mul_comm, one_div]; congr 1
        refine Finset.sum_congr rfl fun T _ => by rw [boolChar_symmDiff, boolChar_symm C T]; ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun T _ => (Finset.mul_sum _ _ _).symm
    rw [hexp]
    simp_rw [sum_boolChar_powerset A]
    have hTA_iff : ∀ T : Finset X, T ∩ A = ∅ ↔ T ∈ Aᶜ.powerset := by
      intro T; rw [Finset.mem_powerset, Finset.subset_compl_iff_disjoint_right, Finset.disjoint_iff_inter_eq_empty]
    have hcoll : (∑ T : Finset X, h T * boolChar B T * (if T ∩ A = ∅ then (2 : ℝ) ^ A.card else 0)) =
        ∑ T ∈ Aᶜ.powerset, (-1 : ℝ) * boolChar B T * (2 : ℝ) ^ A.card := by
      have hite : ∀ T ∈ (Finset.univ : Finset (Finset X)),
          h T * boolChar B T * (if T ∩ A = ∅ then (2 : ℝ) ^ A.card else 0) =
            if T ∈ Aᶜ.powerset then (-1 : ℝ) * boolChar B T * (2 : ℝ) ^ A.card else 0 := by
        intro T _
        by_cases hmem : T ∈ Aᶜ.powerset
        · rw [if_pos ((hTA_iff T).mpr hmem), if_pos hmem]
          have hTcU : Tᶜ ∈ U := by
            rw [Finset.mem_powerset, Finset.subset_compl_comm] at hmem
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, A, hAI, hmem⟩
          have hTU : T ∉ U := fun h1 => hU_disj T ⟨h1, hTcU⟩
          dsimp [h]; rw [if_neg hTU, if_pos hTcU]
        · rw [if_neg (mt (hTA_iff T).mp hmem), if_neg hmem, mul_zero]
      rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
      have hf_eq : (Finset.univ.filter (· ∈ Aᶜ.powerset)) = Aᶜ.powerset := by ext T; simp
      rw [hf_eq]
    rw [hcoll]
    have hpull : (∑ T ∈ Aᶜ.powerset, (-1 : ℝ) * boolChar B T * (2 : ℝ) ^ A.card) =
        - ((2 : ℝ) ^ A.card * ∑ T ∈ Aᶜ.powerset, boolChar B T) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun T _ => by ring
    rw [hpull, sum_boolChar_powerset Aᶜ B]
    have hBAc : B ∩ Aᶜ = ∅ ↔ B ⊆ A := by
      rw [← Finset.disjoint_iff_inter_eq_empty, ← Finset.subset_compl_iff_disjoint_right, compl_compl]
    have hpow_tot : (2 : ℝ) ^ A.card * (2 : ℝ) ^ Aᶜ.card = N := by
      rw [← pow_add, Finset.card_compl, add_tsub_cancel_of_le (Finset.card_le_univ A)]
    by_cases hBA : B ⊆ A
    · rw [if_pos (hBAc.mpr hBA), if_pos hBA, hpow_tot]; field_simp
    · rw [if_neg (mt hBAc.mp hBA), if_neg hBA]; simp
  · -- Proof of `(H q_A)(B) = + q_A(B)` in physical space
    intro A hAI B hBD
    have hsum_D : (∑ C ∈ D, hHat (symmDiff B C) * (boolChar Finset.univ C * (if C ⊆ A then (1 : ℝ) else 0))) =
        ∑ C ∈ A.powerset, hHat (symmDiff B C) * boolChar Finset.univ C := by
      have h1 : ∀ C ∈ D, hHat (symmDiff B C) * (boolChar Finset.univ C * (if C ⊆ A then (1 : ℝ) else 0)) =
          if C ⊆ A then hHat (symmDiff B C) * boolChar Finset.univ C else 0 := by
        intro C _; split_ifs <;> ring
      rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
      have hfilt : (D.filter (fun C => C ⊆ A)) = A.powerset := by
        ext C; simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨And.right, fun hCA => ⟨hD_down A (hID hAI) C hCA, hCA⟩⟩
      rw [hfilt]
    rw [hsum_D]
    have hchar_compl : ∀ T C : Finset X, boolChar C T * boolChar Finset.univ C = boolChar Tᶜ C := by
      intro T C
      rw [boolChar_symm C T, ← boolChar_symmDiff T Finset.univ C]
      have hsd_u : symmDiff T Finset.univ = Tᶜ := by
        ext x; simp [Finset.mem_symmDiff]
      rw [hsd_u, boolChar_symm]
    have hexp : ∑ C ∈ A.powerset, hHat (symmDiff B C) * boolChar Finset.univ C =
        (1 / N) * ∑ T : Finset X, h T * boolChar B T * (∑ C ∈ A.powerset, boolChar Tᶜ C) := by
      dsimp [hHat]
      have h1 : ∀ C ∈ A.powerset, ((∑ T : Finset X, h T * boolChar (symmDiff B C) T) / N) * boolChar Finset.univ C =
          (1 / N) * ∑ T : Finset X, h T * boolChar B T * boolChar Tᶜ C := by
        intro C _
        have hc : ∑ T : Finset X, h T * boolChar (symmDiff B C) T * boolChar Finset.univ C =
            ∑ T : Finset X, h T * boolChar B T * boolChar Tᶜ C := by
          refine Finset.sum_congr rfl fun T _ => by rw [boolChar_symmDiff, mul_assoc, mul_assoc, hchar_compl T C]; ring
        rw [div_mul_eq_mul_div, Finset.sum_mul, hc, div_eq_mul_inv, mul_comm, one_div]
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun T _ => (Finset.mul_sum _ _ _).symm
    rw [hexp]
    simp_rw [sum_boolChar_powerset A]
    -- `Tᶜ ∩ A = ∅ ↔ A ⊆ T`, parameterized bijectively by `R ∈ Aᶜ.powerset ↦ A ∪ R`
    let liftA : Finset X → Finset X := fun R => A ∪ R
    have hlift_inj : Set.InjOn liftA (Aᶜ.powerset : Set (Finset X)) := by
      intro R₁ h1 R₂ h2 heq
      rw [Finset.mem_coe, Finset.mem_powerset, Finset.subset_compl_iff_disjoint_left] at h1 h2
      ext x
      have hx_u := Finset.ext_iff.mp heq x
      simp only [liftA, Finset.mem_union] at hx_u
      by_cases hxA : x ∈ A
      · simp [Finset.disjoint_left.mp h1 hxA, Finset.disjoint_left.mp h2 hxA]
      · simpa [hxA] using hx_u
    have himg_eq : Aᶜ.powerset.image liftA =
        (Finset.univ : Finset (Finset X)).filter (fun T => Tᶜ ∩ A = ∅) := by
      ext T; simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_filter, Finset.mem_univ, true_and, liftA]
      constructor
      · rintro ⟨R, hRAc, rfl⟩
        rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
        intro x hxTc hxA; exact (Finset.mem_compl.mp hxTc) (Finset.mem_union_left R hxA)
      · intro hempty
        have hAT : A ⊆ T := by
          intro x hxA; by_contra hxT
          have : x ∈ Tᶜ ∩ A := Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hxT, hxA⟩
          rw [hempty] at this; exact Finset.notMem_empty x this
        exact ⟨T \ A, fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2,
          Finset.union_sdiff_of_subset hAT⟩
    have hcoll : (∑ T : Finset X, h T * boolChar B T * (if Tᶜ ∩ A = ∅ then (2 : ℝ) ^ A.card else 0)) =
        ∑ R ∈ Aᶜ.powerset, boolChar B (A ∪ R) * (2 : ℝ) ^ A.card := by
      have hite : ∀ T ∈ (Finset.univ : Finset (Finset X)),
          h T * boolChar B T * (if Tᶜ ∩ A = ∅ then (2 : ℝ) ^ A.card else 0) =
            if Tᶜ ∩ A = ∅ then h T * boolChar B T * (2 : ℝ) ^ A.card else 0 := by
        intro T _; split_ifs <;> ring
      rw [Finset.sum_congr rfl hite, ← Finset.sum_filter, ← himg_eq,
        Finset.sum_image hlift_inj]
      refine Finset.sum_congr rfl fun R _ => ?_
      have hAU : A ∪ R ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, A, hAI, Finset.subset_union_left⟩
      dsimp [h, liftA]; rw [if_pos hAU, one_mul]
    rw [hcoll]
    have hsplit_AR : ∀ R ∈ Aᶜ.powerset,
        boolChar B (A ∪ R) * (2 : ℝ) ^ A.card =
          (boolChar B A * (2 : ℝ) ^ A.card) * boolChar B R := by
      intro R hR
      rw [Finset.mem_powerset, Finset.subset_compl_iff_disjoint_left] at hR
      have hu_sd : A ∪ R = symmDiff A R := by
        ext x; by_cases hxA : x ∈ A <;> by_cases hxR : x ∈ R
        · exact False.elim (Finset.disjoint_left.mp hR hxA hxR)
        · simp [Finset.mem_symmDiff, hxA, hxR]
        · simp [Finset.mem_symmDiff, hxA, hxR]
        · simp [Finset.mem_symmDiff, hxA, hxR]
      rw [hu_sd, boolChar_symm B (symmDiff A R), boolChar_symmDiff, boolChar_symm A B, boolChar_symm R B]
      ring
    rw [Finset.sum_congr rfl hsplit_AR, ← Finset.mul_sum, sum_boolChar_powerset Aᶜ B]
    have hBAc : B ∩ Aᶜ = ∅ ↔ B ⊆ A := by
      rw [← Finset.disjoint_iff_inter_eq_empty, ← Finset.subset_compl_iff_disjoint_right, compl_compl]
    have hpow_tot : (2 : ℝ) ^ A.card * (2 : ℝ) ^ Aᶜ.card = N := by
      rw [← pow_add, Finset.card_compl, add_tsub_cancel_of_le (Finset.card_le_univ A)]
    by_cases hBA : B ⊆ A
    · rw [if_pos (hBAc.mpr hBA), if_pos hBA]
      have hchar_u : boolChar B A = boolChar Finset.univ B := by
        simp only [boolChar, Finset.inter_eq_left.mpr hBA, Finset.univ_inter]
      rw [hchar_u]
      calc (1 / N) * (boolChar Finset.univ B * (2 : ℝ) ^ A.card * (2 : ℝ) ^ Aᶜ.card)
        _ = (1 / N) * (boolChar Finset.univ B * ((2 : ℝ) ^ A.card * (2 : ℝ) ^ Aᶜ.card)) := by ring
        _ = (1 / N) * (boolChar Finset.univ B * N) := by rw [hpow_tot]
        _ = boolChar Finset.univ B * 1 := by field_simp
    · rw [if_neg (mt hBAc.mp hBA), if_neg hBA]; simp

lemma orthonormal_eigenbasis_from_subsets {X : Type*} [DecidableEq X]
    (D : Finset (Finset X)) (K : Finset X → Finset X → ℝ)
    (w : Finset X → Finset X → ℝ) (sgn : ℝ)
    (hw_supp : ∀ A B : Finset X, ¬ B ⊆ A → w A B = 0) :
    ∀ (J : Finset (Finset X)), J ⊆ D →
      (∀ A ∈ J, w A A ≠ 0) →
      (∀ A ∈ J, ∀ B ∈ D, (∑ C ∈ D, K B C * w A C) = sgn * w A B) →
      ∃ e : Fin J.card → (Finset X → ℝ),
        (∀ i j : Fin J.card, (∑ B ∈ D, e i B * e j B) = if i = j then 1 else 0) ∧
        (∀ i : Fin J.card, ∀ B ∈ D, (∑ C ∈ D, K B C * e i C) = sgn * e i B) ∧
        (∀ i : Fin J.card, ∀ B : Finset X, (∀ A ∈ J, ¬ B ⊆ A) → e i B = 0) := by
  intro J
  induction hcard : J.card generalizing J with
  | zero =>
    intro _ _ _
    exact ⟨fun i => False.elim (Nat.not_lt_zero i.val i.isLt),
      fun i => False.elim (Nat.not_lt_zero i.val i.isLt),
      fun i => False.elim (Nat.not_lt_zero i.val i.isLt),
      fun i => False.elim (Nat.not_lt_zero i.val i.isLt)⟩
  | succ k ih =>
    intro hJD hw_diag hw_eig
    have hJ_ne : J.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨Aₘ, hAₘ_J, hAₘ_max⟩ := Finset.exists_max_image J Finset.card hJ_ne
    let J' := J.erase Aₘ
    have hJ'_card : J'.card = k := by
      dsimp [J']; rw [Finset.card_erase_of_mem hAₘ_J, hcard]; omega
    have hJ'_sub : J' ⊆ D := subset_trans (Finset.erase_subset Aₘ J) hJD
    obtain ⟨e', he'_orth, he'_eig, he'_supp⟩ := ih J' hJ'_card hJ'_sub
      (fun A hA => hw_diag A (Finset.mem_of_mem_erase hA))
      (fun A hA => hw_eig A (Finset.mem_of_mem_erase hA))
    have hnot_sub_J' : ∀ A ∈ J', ¬ Aₘ ⊆ A := by
      intro A hAJ' hsub
      rcases Finset.mem_erase.mp hAJ' with ⟨hne, hAJ⟩
      have hle2 : A.card ≤ Aₘ.card := hAₘ_max A hAJ
      exact hne (Finset.eq_of_subset_of_card_le hsub hle2).symm
    let proj : Fin k → ℝ := fun r => ∑ B ∈ D, w Aₘ B * e' r B
    let u : Finset X → ℝ := fun B => w Aₘ B - ∑ r : Fin k, proj r * e' r B
    have hu_at_Am : u Aₘ = w Aₘ Aₘ := by
      dsimp [u]
      have hz : ∀ r ∈ (Finset.univ : Finset (Fin k)), proj r * e' r Aₘ = 0 := by
        intro r _; rw [he'_supp r Aₘ hnot_sub_J', mul_zero]
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, sub_zero]
    have hAm_D : Aₘ ∈ D := hJD hAₘ_J
    have hu_norm_pos : 0 < ∑ B ∈ D, (u B) ^ 2 := by
      have hpos_Am : 0 < (u Aₘ) ^ 2 := by
        rw [hu_at_Am]; exact sq_pos_of_ne_zero (hw_diag Aₘ hAₘ_J)
      exact lt_of_lt_of_le hpos_Am
        (Finset.single_le_sum (fun B _ => sq_nonneg (u B)) hAm_D)
    set nrm : ℝ := Real.sqrt (∑ B ∈ D, (u B) ^ 2)
    have hnrm_pos : 0 < nrm := Real.sqrt_pos.mpr hu_norm_pos
    have hnrm_ne : nrm ≠ 0 := ne_of_gt hnrm_pos
    have hnrm_sq : nrm ^ 2 = ∑ B ∈ D, (u B) ^ 2 := Real.sq_sqrt (le_of_lt hu_norm_pos)
    let e_top : Finset X → ℝ := fun B => u B / nrm
    have hu_orth : ∀ r : Fin k, (∑ B ∈ D, u B * e' r B) = 0 := by
      intro r
      have h1 : ∀ B ∈ D, u B * e' r B = w Aₘ B * e' r B - ∑ s : Fin k, proj s * (e' s B * e' r B) := by
        intro B _; dsimp [u]; rw [sub_mul, Finset.sum_mul]
        congr 1; refine Finset.sum_congr rfl fun s _ => by ring
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_comm]
      have h2 : ∑ s : Fin k, ∑ B ∈ D, proj s * (e' s B * e' r B) = proj r := by
        simp_rw [← Finset.mul_sum, he'_orth]
        have hite : ∀ s ∈ (Finset.univ : Finset (Fin k)),
            proj s * (if s = r then (1 : ℝ) else 0) = if s = r then proj r else 0 := by
          intro s _; by_cases hsr : s = r
          · subst hsr; simp
          · simp [hsr]
        rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq' Finset.univ r]
        simp
      rw [h2]; dsimp [proj]; ring
    have he_top_norm : (∑ B ∈ D, e_top B * e_top B) = 1 := by
      dsimp [e_top]
      have h1 : ∀ B ∈ D, (u B / nrm) * (u B / nrm) = (u B) ^ 2 * (nrm ^ 2)⁻¹ :=
        fun B _ => by ring
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← hnrm_sq]
      field_simp
    have he_top_eig : ∀ B ∈ D, (∑ C ∈ D, K B C * e_top C) = sgn * e_top B := by
      intro B hBD; dsimp [e_top]
      simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
      have hu_eig : (∑ C ∈ D, K B C * u C) = sgn * u B := by
        have h1 : ∀ C ∈ D, K B C * u C = K B C * w Aₘ C - ∑ r : Fin k, proj r * (K B C * e' r C) := by
          intro C _; dsimp [u]; rw [mul_sub, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun r _ => by ring
        rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hw_eig Aₘ hAₘ_J B hBD, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        have h2 : ∑ r : Fin k, proj r * (∑ C ∈ D, K B C * e' r C) = sgn * ∑ r : Fin k, proj r * e' r B := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => by rw [he'_eig r B hBD]; ring
        rw [h2]; dsimp [u]; ring
      rw [hu_eig]
    have he_top_supp : ∀ B : Finset X, (∀ A ∈ J, ¬ B ⊆ A) → e_top B = 0 := by
      intro B hBJ; dsimp [e_top, u]
      have hw0 : w Aₘ B = 0 := hw_supp Aₘ B (hBJ Aₘ hAₘ_J)
      have he0 : ∀ r ∈ (Finset.univ : Finset (Fin k)), proj r * e' r B = 0 := by
        intro r _
        rw [he'_supp r B (fun A hAJ' => hBJ A (Finset.mem_of_mem_erase hAJ')), mul_zero]
      rw [hw0, Finset.sum_congr rfl he0, Finset.sum_const_zero, sub_zero, zero_div]
    let e_all : Fin (k + 1) → (Finset X → ℝ) := Fin.snoc e' e_top
    refine ⟨e_all, ?_, ?_, ?_⟩
    · intro i j
      refine i.lastCases ?_ (fun r => ?_) <;> refine j.lastCases ?_ (fun s => ?_)
      · simp [e_all, he_top_norm]
      · have hne_ls : Fin.last k ≠ s.castSucc := (Fin.castSucc_ne_last s).symm
        simp only [e_all, Fin.snoc_last, Fin.snoc_castSucc, if_neg hne_ls]
        dsimp [e_top]; simp_rw [div_eq_mul_inv, mul_comm _ nrm⁻¹, mul_assoc, ← Finset.mul_sum]
        rw [hu_orth s]; simp
      · simp only [e_all, Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last]
        dsimp [e_top]; simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
        have hcomm : (∑ B ∈ D, e' r B * u B) = ∑ B ∈ D, u B * e' r B :=
          Finset.sum_congr rfl fun B _ => mul_comm _ _
        rw [hcomm, hu_orth r]; simp
      · simp only [e_all, Fin.snoc_castSucc, Fin.castSucc_inj]
        exact he'_orth r s
    · intro i B hBD
      refine i.lastCases ?_ (fun r => ?_)
      · simp [e_all, he_top_eig B hBD]
      · simp [e_all, he'_eig r B hBD]
    · intro i B hBJ
      refine i.lastCases ?_ (fun r => ?_)
      · simp [e_all, he_top_supp B hBJ]
      · simp [e_all, he'_supp r B (fun A hAJ' => hBJ A (Finset.mem_of_mem_erase hAJ'))]

lemma row_bessel_inequality {α : Type*} (D : Finset α) {M : ℕ}
    (f : α → ℝ) (E : Fin M → (α → ℝ))
    (hE_orth : ∀ r s : Fin M, (∑ B ∈ D, E r B * E s B) = if r = s then 1 else 0) :
    (∑ r : Fin M, (∑ B ∈ D, f B * E r B) ^ 2) ≤ ∑ B ∈ D, (f B) ^ 2 := by
  let c : Fin M → ℝ := fun r => ∑ B ∈ D, f B * E r B
  let res : α → ℝ := fun B => f B - ∑ r : Fin M, c r * E r B
  have hnn : 0 ≤ ∑ B ∈ D, (res B) ^ 2 := Finset.sum_nonneg fun B _ => sq_nonneg _
  have hexp : ∑ B ∈ D, (res B) ^ 2 = (∑ B ∈ D, (f B) ^ 2) - ∑ r : Fin M, (c r) ^ 2 := by
    have h1 : ∀ B ∈ D, (res B) ^ 2 = (f B) ^ 2 - 2 * (∑ r : Fin M, c r * (f B * E r B)) +
        ∑ r : Fin M, ∑ s : Fin M, c r * c s * (E r B * E s B) := by
      intro B _; dsimp [res]
      have hsq_sum : (∑ r : Fin M, c r * E r B) ^ 2 =
          ∑ r : Fin M, ∑ s : Fin M, c r * c s * (E r B * E s B) := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => by ring
      have hlin_sum : f B * ∑ r : Fin M, c r * E r B = ∑ r : Fin M, c r * (f B * E r B) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring
      calc (f B - ∑ r : Fin M, c r * E r B) ^ 2
        _ = (f B) ^ 2 - 2 * (f B * ∑ r : Fin M, c r * E r B) + (∑ r : Fin M, c r * E r B) ^ 2 := by ring
        _ = _ := by rw [hlin_sum, hsq_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hmid : (∑ B ∈ D, 2 * ∑ r : Fin M, c r * (f B * E r B)) = 2 * ∑ r : Fin M, (c r) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.mul_sum]; dsimp [c]; ring
    have hquad : (∑ B ∈ D, ∑ r : Fin M, ∑ s : Fin M, c r * c s * (E r B * E s B)) =
        ∑ r : Fin M, (c r) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hE_orth]
      have hite : ∀ s ∈ (Finset.univ : Finset (Fin M)),
          c r * c s * (if r = s then (1 : ℝ) else 0) = if s = r then (c r) ^ 2 else 0 := by
        intro s _; by_cases hrs : r = s
        · subst hrs; simp [sq]
        · have hsr : s ≠ r := Ne.symm hrs; simp [hrs, hsr]
      rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq' Finset.univ r]
      simp
    rw [hmid, hquad]; ring
  linarith

/-- **Theorem 1A (`Erdős #701` Complete Finset Proof of Chvátal's Conjecture)**:
For every finite nonempty type `X` and every downset `D : Finset (Finset X)`, there exists `x₀ : X`
such that **every** intersecting subfamily `I ⊆ D` satisfies `I.card ≤ (D.filter (x₀ ∈ ·)).card`
(machine-checked adaptation of Chang–Liu–Liu 2026 & Ellis–Filmus–Friedgut 2026). -/
theorem chvatal_conjecture_finset {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (D : Finset (Finset X)) (hD_down : ∀ A ∈ D, ∀ B : Finset X, B ⊆ A → B ∈ D) :
    ∃ x₀ : X, ∀ I : Finset (Finset X), I ⊆ D →
      (∀ A ∈ I, ∀ B ∈ I, (A ∩ B).Nonempty) → I.card ≤ (D.filter (x₀ ∈ ·)).card := by
  obtain ⟨x₀, _, hx₀_max⟩ := Finset.exists_max_image (Finset.univ : Finset X)
    (fun x => (D.filter (x ∈ ·)).card) Finset.univ_nonempty
  refine ⟨x₀, fun I hID hI_inter => ?_⟩
  have hub_eig := chvatal_ub_and_eigen_identities D I hD_down hID hI_inter
  let N : ℝ := (2 : ℝ) ^ Fintype.card X
  let U : Finset (Finset X) := (Finset.univ : Finset (Finset X)).filter (fun T => ∃ B ∈ I, B ⊆ T)
  let h : Finset X → ℝ := fun T => if T ∈ U then 1 else if Tᶜ ∈ U then -1 else 0
  let hHat : Finset X → ℝ := fun S => (∑ T : Finset X, h T * boolChar S T) / N
  let K : Finset X → Finset X → ℝ := fun A B => hHat (symmDiff A B)
  have hK_symm : ∀ A B : Finset X, K A B = K B A := fun A B => by
    dsimp [K]; rw [symmDiff_comm]
  rcases hub_eig with ⟨⟨x₁, hub⟩, heig_neg, heig_pos⟩
  have hx₁_le_x₀ : (D.filter (x₁ ∈ ·)).card ≤ (D.filter (x₀ ∈ ·)).card :=
    hx₀_max x₁ (Finset.mem_univ x₁)
  have hub0 : ∑ A ∈ D, ∑ B ∈ D, (K A B) ^ 2 ≤ 2 * ((D.filter (x₀ ∈ ·)).card : ℝ) :=
    le_trans hub (by exact_mod_cast Nat.mul_le_mul_left 2 hx₁_le_x₀)
  let w_neg : Finset X → Finset X → ℝ := fun A B => if B ⊆ A then 1 else 0
  let w_pos : Finset X → Finset X → ℝ := fun A B => boolChar Finset.univ B * (if B ⊆ A then 1 else 0)
  obtain ⟨e_neg, hneg_orth, hneg_eig, _⟩ := orthonormal_eigenbasis_from_subsets D K w_neg (-1)
    (fun A B hnot => by simp [w_neg, hnot]) I hID
    (fun A _ => by simp [w_neg])
    (fun A hAI B hBD => by dsimp [K, hHat, h, U, N, w_neg]; rw [neg_one_mul]; exact heig_neg A hAI B hBD)
  obtain ⟨e_pos, hpos_orth, hpos_eig, _⟩ := orthonormal_eigenbasis_from_subsets D K w_pos 1
    (fun A B hnot => by simp [w_pos, hnot]) I hID
    (fun A _ => by
      dsimp [w_pos]; rw [if_pos (Finset.Subset.refl A), mul_one]
      exact pow_ne_zero _ (by norm_num))
    (fun A hAI B hBD => by dsimp [K, hHat, h, U, N, w_pos]; rw [one_mul]; exact heig_pos A hAI B hBD)
  -- Mutual orthogonality between `+1` and `-1` eigenfunctions of symmetric `K`!
  have hcross_orth : ∀ i j : Fin I.card, (∑ B ∈ D, e_neg i B * e_pos j B) = 0 := by
    intro i j
    have hsym_bilin : (∑ B ∈ D, (∑ C ∈ D, K B C * e_neg i C) * e_pos j B) =
        ∑ C ∈ D, e_neg i C * (∑ B ∈ D, K C B * e_pos j B) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun C _ => ?_
      refine Finset.sum_congr rfl fun B _ => by rw [hK_symm B C]; ring
    have hlhs : (∑ B ∈ D, (∑ C ∈ D, K B C * e_neg i C) * e_pos j B) =
        - ∑ B ∈ D, e_neg i B * e_pos j B := by
      have h1 : ∀ B ∈ D, (∑ C ∈ D, K B C * e_neg i C) * e_pos j B = - (e_neg i B * e_pos j B) :=
        fun B hB => by rw [hneg_eig i B hB]; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_neg_distrib]
    have hrhs : (∑ C ∈ D, e_neg i C * (∑ B ∈ D, K C B * e_pos j B)) =
        ∑ C ∈ D, e_neg i C * e_pos j C := by
      refine Finset.sum_congr rfl fun C hC => by rw [hpos_eig j C hC, one_mul]
    linarith
  -- Combine `e_neg` and `e_pos` into an orthonormal system `E : Fin (I.card + I.card) → (Finset X → ℝ)`
  let E : Fin (I.card + I.card) → (Finset X → ℝ) := Fin.addCases e_neg e_pos
  have hE_orth : ∀ r s : Fin (I.card + I.card), (∑ B ∈ D, E r B * E s B) = if r = s then 1 else 0 := by
    intro r s
    refine r.addCases (fun i => ?_) (fun i => ?_) <;> refine s.addCases (fun j => ?_) (fun j => ?_)
    · simp only [E, Fin.addCases_left, Fin.castAdd_inj]; exact hneg_orth i j
    · have hne : Fin.castAdd I.card i ≠ Fin.natAdd I.card j := by
        intro h; have hv := congrArg Fin.val h; simp at hv; omega
      simp only [E, Fin.addCases_left, Fin.addCases_right, if_neg hne]
      exact hcross_orth i j
    · have hne : Fin.natAdd I.card i ≠ Fin.castAdd I.card j := by
        intro h; have hv := congrArg Fin.val h; simp at hv; omega
      simp only [E, Fin.addCases_left, Fin.addCases_right, if_neg hne]
      have hcomm : (∑ B ∈ D, e_pos i B * e_neg j B) = ∑ B ∈ D, e_neg j B * e_pos i B :=
        Finset.sum_congr rfl fun B _ => mul_comm _ _
      rw [hcomm, hcross_orth j i]
    · simp only [E, Fin.addCases_right, Fin.natAdd_inj]; exact hpos_orth i j
  have hE_norm_sq : ∀ r : Fin (I.card + I.card), (∑ A ∈ D, (∑ B ∈ D, K A B * E r B) ^ 2) = 1 := by
    intro r
    refine r.addCases (fun i => ?_) (fun i => ?_)
    · simp only [E, Fin.addCases_left]
      have h1 : ∀ A ∈ D, (∑ B ∈ D, K A B * e_neg i B) ^ 2 = e_neg i A * e_neg i A := by
        intro A hA; rw [hneg_eig i A hA]; ring
      rw [Finset.sum_congr rfl h1, hneg_orth i i, if_pos rfl]
    · simp only [E, Fin.addCases_right]
      have h1 : ∀ A ∈ D, (∑ B ∈ D, K A B * e_pos i B) ^ 2 = e_pos i A * e_pos i A := by
        intro A hA; rw [hpos_eig i A hA]; ring
      rw [Finset.sum_congr rfl h1, hpos_orth i i, if_pos rfl]
  have hlb_rows : ∀ A ∈ D,
      (∑ r : Fin (I.card + I.card), (∑ B ∈ D, K A B * E r B) ^ 2) ≤ ∑ B ∈ D, (K A B) ^ 2 :=
    fun A _ => row_bessel_inequality D (K A) E hE_orth
  have hlb : 2 * (I.card : ℝ) ≤ ∑ A ∈ D, ∑ B ∈ D, (K A B) ^ 2 := by
    have hsum_le := Finset.sum_le_sum hlb_rows
    rw [Finset.sum_comm] at hsum_le
    simp_rw [hE_norm_sq] at hsum_le
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum_le
    have h2I : ((I.card + I.card : ℕ) : ℝ) = 2 * (I.card : ℝ) := by push_cast; ring
    linarith
  have h2_le : 2 * (I.card : ℝ) ≤ 2 * ((D.filter (x₀ ∈ ·)).card : ℝ) := le_trans hlb hub0
  exact_mod_cast (show (I.card : ℝ) ≤ ((D.filter (x₀ ∈ ·)).card : ℝ) by linarith)

/-- **Theorem 1B (`Erdős #701` Complete `Set (Set X)` Formalization of Chvátal's Conjecture)**:
Matches `FormalConjectures/ErdosProblems/701.lean` (`IsLowerSet F`, `F'.Intersecting`, and `ncard`):
for every finite nonempty type `X` and every downset `F : Set (Set X)`, there exists `x : X` such
that every intersecting subfamily `F' ⊆ F` satisfies `F'.ncard ≤ {A ∈ F | x ∈ A}.ncard`. -/
theorem erdos_701_ncard {X : Type*} [Nonempty X] [Fintype X]
    (F : Set (Set X)) (hF : IsLowerSet F) :
    ∃ x : X, ∀ F' ⊆ F, F'.Intersecting →
      F'.ncard ≤ {A : Set X | A ∈ F ∧ x ∈ A}.ncard := by
  let toFS : Finset X ↪ Set X := ⟨fun A => (A : Set X), Finset.coe_injective⟩
  let D : Finset (Finset X) := (Finset.univ : Finset (Finset X)).filter (fun A => (A : Set X) ∈ F)
  have hD_down : ∀ A ∈ D, ∀ B : Finset X, B ⊆ A → B ∈ D := by
    intro A hA B hBA
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact hF (Finset.coe_subset.mpr hBA) hA
  obtain ⟨x, hx⟩ := chvatal_conjecture_finset D hD_down
  refine ⟨x, fun F' hF'F hF'_inter => ?_⟩
  let I : Finset (Finset X) := (Finset.univ : Finset (Finset X)).filter (fun A => (A : Set X) ∈ F')
  have hID : I ⊆ D := by
    intro A hA
    simp only [I, D, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact hF'F hA
  have hI_inter : ∀ A ∈ I, ∀ B ∈ I, (A ∩ B).Nonempty := by
    intro A hA B hB
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hA hB
    have hnd := hF'_inter hA hB
    rw [Set.not_disjoint_iff] at hnd
    rcases hnd with ⟨y, hyA, hyB⟩
    exact ⟨y, Finset.mem_inter.mpr ⟨hyA, hyB⟩⟩
  have hcard_le := hx I hID hI_inter
  have hI_ncard : F'.ncard = I.card := by
    have himg : (I.map toFS : Set (Set X)) = F' := by
      ext S; simp only [Finset.mem_coe, Finset.mem_map, I, Finset.mem_filter, Finset.mem_univ,
        true_and, toFS, Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨A, hAF', hAS⟩ => hAS ▸ hAF', fun hSF' => ⟨S.toFinset, by simpa using hSF', Set.coe_toFinset S⟩⟩
    rw [← himg, Set.ncard_coe_finset, Finset.card_map]
  have hStar_ncard : {A : Set X | A ∈ F ∧ x ∈ A}.ncard = (D.filter (x ∈ ·)).card := by
    have himg : ((D.filter (x ∈ ·)).map toFS : Set (Set X)) = {A : Set X | A ∈ F ∧ x ∈ A} := by
      ext S; simp only [Finset.mem_coe, Finset.mem_map, D, Finset.mem_filter, Finset.mem_univ,
        true_and, Set.mem_ofPred, toFS, Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨A, ⟨hAF, hxA⟩, hAS⟩ => hAS ▸ ⟨hAF, hxA⟩,
        fun ⟨hSF, hxS⟩ => ⟨S.toFinset, ⟨by simpa using hSF, Set.mem_toFinset.mpr hxS⟩, Set.coe_toFinset S⟩⟩
    rw [← himg, Set.ncard_coe_finset, Finset.card_map]
  rw [hI_ncard, hStar_ncard]
  exact hcard_le


/-- **Principal Downset Sharpness (`Erdős #701`)**:
In the principal downset `S.powerset` (`S` nonempty), for every `x₀ ∈ S` the star at `x₀` is an
intersecting subfamily of cardinality `2 ^ (S.card - 1)`, and every intersecting subfamily of
`S.powerset` has cardinality at most `2 ^ (S.card - 1)`. -/
theorem principal_downset_sharpness {X : Type*} [DecidableEq X]
    (S : Finset X) (x₀ : X) (hx₀ : x₀ ∈ S) :
    ((S.powerset).filter (x₀ ∈ ·)).card = 2 ^ (S.card - 1) ∧
    (∀ A ∈ (S.powerset).filter (x₀ ∈ ·), ∀ B ∈ (S.powerset).filter (x₀ ∈ ·), (A ∩ B).Nonempty) ∧
    (∀ I : Finset (Finset X), I ⊆ S.powerset →
      (∀ A ∈ I, ∀ B ∈ I, (A ∩ B).Nonempty) → I.card ≤ 2 ^ (S.card - 1)) := by
  have hstar_card : ((S.powerset).filter (x₀ ∈ ·)).card = 2 ^ (S.card - 1) := by
    have hbij : ((S.powerset).filter (x₀ ∈ ·)) =
        (S.erase x₀).powerset.image (insert x₀) := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
      constructor
      · rintro ⟨hAS, hxA⟩
        refine ⟨A.erase x₀, ?_, Finset.insert_erase hxA⟩
        intro y hy
        rcases Finset.mem_erase.mp hy with ⟨hyx, hyA⟩
        exact Finset.mem_erase.mpr ⟨hyx, hAS hyA⟩
      · rintro ⟨B, hBS, rfl⟩
        refine ⟨?_, Finset.mem_insert_self x₀ B⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hyB
        · exact hx₀
        · exact Finset.mem_of_mem_erase (hBS hyB)
    rw [hbij, Finset.card_image_of_injOn, Finset.card_powerset, Finset.card_erase_of_mem hx₀]
    intro B₁ hB₁ B₂ hB₂ hins
    rw [Finset.mem_coe, Finset.mem_powerset] at hB₁ hB₂
    have hxB₁ : x₀ ∉ B₁ := fun h => (Finset.mem_erase.mp (hB₁ h)).1 rfl
    have hxB₂ : x₀ ∉ B₂ := fun h => (Finset.mem_erase.mp (hB₂ h)).1 rfl
    have heq := congr_arg (fun T : Finset X => T.erase x₀) hins
    simpa [Finset.erase_insert hxB₁, Finset.erase_insert hxB₂] using heq
  refine ⟨hstar_card, ?_, ?_⟩
  · intro A hA B hB
    exact ⟨x₀, Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hA).2, (Finset.mem_filter.mp hB).2⟩⟩
  · intro I hIS hI_inter
    have hpair : ∀ A ∈ I, S \ A ∉ I := by
      intro A hAI hcompI
      rcases hI_inter A hAI (S \ A) hcompI with ⟨y, hy⟩
      rcases Finset.mem_inter.mp hy with ⟨hyA, hySA⟩
      exact (Finset.mem_sdiff.mp hySA).2 hyA
    have hdisj : Disjoint I (I.image (fun A => S \ A)) := by
      rw [Finset.disjoint_left]
      intro B hBI hBimg
      rcases Finset.mem_image.mp hBimg with ⟨A, hAI, rfl⟩
      exact hpair A hAI hBI
    have hinj : Set.InjOn (fun A : Finset X => S \ A) (I : Set (Finset X)) := by
      intro A₁ hA₁ A₂ hA₂ heq
      have h₁ : A₁ ⊆ S := Finset.mem_powerset.mp (hIS hA₁)
      have h₂ : A₂ ⊆ S := Finset.mem_powerset.mp (hIS hA₂)
      have hss : S \ (S \ A₁) = S \ (S \ A₂) := congr_arg (fun T => S \ T) heq
      simpa [Finset.sdiff_sdiff_eq_self h₁, Finset.sdiff_sdiff_eq_self h₂] using hss
    have hunion_sub : I ∪ I.image (fun A => S \ A) ⊆ S.powerset := by
      intro B hB
      rcases Finset.mem_union.mp hB with hBI | hBimg
      · exact hIS hBI
      · rcases Finset.mem_image.mp hBimg with ⟨A, _, rfl⟩
        exact Finset.mem_powerset.mpr Finset.sdiff_subset
    have hle := Finset.card_le_card hunion_sub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj,
      Finset.card_powerset] at hle
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x₀, hx₀⟩
    have hpow : 2 ^ S.card = 2 * 2 ^ (S.card - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ, mul_comm]
    omega


/-- **Exact `FormalConjectures` Cardinal Formulation of Erdős Problem `#701` (`JSP-000571`)**:
Matches `Erdos701.erdos_701` in `google-deepmind/formal-conjectures`
(`FormalConjectures/ErdosProblems/701.lean`, commit `b576d527b271b936f9e61c0e367c302d7386bc80`)
character-for-character: in every hereditary family `F : Set (Set X)` (`IsLowerSet F`) on a finite
nonempty ground type `X`, there exists `x : X` whose star in `F` has cardinality `#` at least `#F'`
for every pairwise-intersecting subfamily `F' ⊆ F`. -/
theorem erdos_701 : ∀ {X : Type} [Nonempty X] [Fintype X],
    ∀ (F : Set (Set X)), IsLowerSet F →
      ∃ x : X, ∀ᵉ (F' ⊆ F),
        F'.Intersecting →
          (#F' ≤ #{ A : Set X | A ∈ F ∧ x ∈ A }) := by
  intro X _ _ F hF
  rcases erdos_701_ncard F hF with ⟨x, hx⟩
  refine ⟨x, fun F' hF'F hF'_inter => ?_⟩
  have hnc := hx F' hF'F hF'_inter
  rw [← Nat.cast_le (α := Cardinal), ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hnc
  have hc1 : ((Nat.card F' : ℕ) : Cardinal) = #F' := Nat.cast_card
  have hc2 : ((Nat.card { A : Set X | A ∈ F ∧ x ∈ A } : ℕ) : Cardinal) = #{ A : Set X | A ∈ F ∧ x ∈ A } :=
    Nat.cast_card
  rwa [hc1, hc2] at hnc

/-- **Chvátal's Hereditary Hypergraph Vertex-in-Edge Formulation (`[Ch74]`)**:
For any finite ground type `X` (without assuming `[Nonempty X]` a priori) and any hereditary set
family `D : Finset (Finset X)` containing at least one nonempty member `E ∈ D`, there exists an
element `x₀ : X` belonging to `D` as a singleton `{x₀} ∈ D` (hence lying in `⋃_{A ∈ D} A`) whose
star `D.filter (x₀ ∈ ·)` achieves the maximum cardinality over all intersecting subfamilies `I ⊆ D`. -/
theorem chvatal_conjecture_hypergraph_vertex {X : Type*} [Fintype X] [DecidableEq X]
    (D : Finset (Finset X)) (hD_down : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D)
    (hD_ne : ∃ E ∈ D, E.Nonempty) :
    ∃ x₀ : X, ({x₀} : Finset X) ∈ D ∧
      ∀ I : Finset (Finset X), I ⊆ D →
        (∀ A ∈ I, ∀ B ∈ I, (A ∩ B).Nonempty) →
        I.card ≤ (D.filter (x₀ ∈ ·)).card := by
  rcases hD_ne with ⟨E, hED, y₀, hy₀E⟩
  have : Nonempty X := ⟨y₀⟩
  rcases chvatal_conjecture_finset D hD_down with ⟨x₀, hx₀_max⟩
  have hy₀_singleton_D : ({y₀} : Finset X) ∈ D :=
    hD_down E hED {y₀} (Finset.singleton_subset_iff.mpr hy₀E)
  have hy₀_inter : ∀ A ∈ ({({y₀} : Finset X)} : Finset (Finset X)),
      ∀ B ∈ ({({y₀} : Finset X)} : Finset (Finset X)), (A ∩ B).Nonempty := by
    intro A hA B hB
    rw [Finset.mem_singleton] at hA hB
    subst hA; subst hB
    exact ⟨y₀, by simp⟩
  have hcard_ge1 : 1 ≤ (D.filter (x₀ ∈ ·)).card := by
    have := hx₀_max {{y₀}} (Finset.singleton_subset_iff.mpr hy₀_singleton_D) hy₀_inter
    simpa using this
  rcases Finset.card_pos.mp hcard_ge1 with ⟨A₀, hA₀_filt⟩
  rcases Finset.mem_filter.mp hA₀_filt with ⟨hA₀_D, hx₀_A₀⟩
  exact ⟨x₀, hD_down A₀ hA₀_D {x₀} (Finset.singleton_subset_iff.mpr hx₀_A₀), hx₀_max⟩

end Erdos701
