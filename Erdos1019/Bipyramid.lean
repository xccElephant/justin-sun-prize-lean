/-
Copyright 2026 Chucheng Xiang (@xccElephant).
SPDX-License-Identifier: Apache-2.0

Clean-room construction, edge counting, and straight-line topological planarity proofs for
bipyramid graphs `B_l = C_l ∨ 2K_1` (`l ≥ 3`) and `K_4` (`⊤ : SimpleGraph (Fin 4)`).
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Erdos1019.Planarity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos1019

open Finset
open scoped SimpleGraph

/-- Vertex type of the `l`-bipyramid `B_l = C_l ∨ 2K_1`:
`Sum.inl i` (`i : Fin l`) are the `l` cycle vertices, `Sum.inr true` is the north apex, and
`Sum.inr false` is the south apex. -/
abbrev BipyramidVert (l : ℕ) : Type := Fin l ⊕ Bool

/-- Adjacency relation of the cycle `C_l` on `Fin l`. -/
def cycleAdj {l : ℕ} (i j : Fin l) : Prop :=
  i ≠ j ∧ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 ∨ (i.1 = 0 ∧ j.1 + 1 = l) ∨ (j.1 = 0 ∧ i.1 + 1 = l))

instance instDecidableRelCycleAdj (l : ℕ) : DecidableRel (@cycleAdj l) :=
  fun i j => by unfold cycleAdj; infer_instance

theorem cycleAdj_symm {l : ℕ} {i j : Fin l} (h : cycleAdj i j) : cycleAdj j i := by
  rcases h with ⟨hne, h1 | h2 | h3 | h4⟩
  · exact ⟨hne.symm, Or.inr (Or.inl h1)⟩
  · exact ⟨hne.symm, Or.inl h2⟩
  · exact ⟨hne.symm, Or.inr (Or.inr (Or.inr h3))⟩
  · exact ⟨hne.symm, Or.inr (Or.inr (Or.inl h4))⟩

/-- Adjacency predicate of the `l`-bipyramid graph `B_l = C_l ∨ 2K_1`. -/
def bipyramidAdj (l : ℕ) : BipyramidVert l → BipyramidVert l → Prop
  | Sum.inl i, Sum.inl j => cycleAdj i j
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => False

/-- The `l`-bipyramid graph `B_l = C_l ∨ 2K_1` on `l + 2` vertices. -/
def bipyramidGraph (l : ℕ) : SimpleGraph (BipyramidVert l) where
  Adj := bipyramidAdj l
  symm := ⟨fun u v h => by
    cases u <;> cases v
    · exact cycleAdj_symm h
    · trivial
    · trivial
    · exact h⟩
  loopless := ⟨fun u h => by
    cases u with
    | inl i => exact h.1 rfl
    | inr _ => exact h⟩

instance instDecidableRelBipyramidAdj (l : ℕ) : DecidableRel (bipyramidGraph l).Adj :=
  fun u v => by
    cases u <;> cases v <;> dsimp [bipyramidGraph, bipyramidAdj] <;> infer_instance

theorem card_bipyramidVert (l : ℕ) : Fintype.card (BipyramidVert l) = l + 2 := by
  simp [BipyramidVert]

/-! ### Exact Degree and Edge Count of `bipyramidGraph l` (`l ≥ 3`) -/

private def cycleNext {l : ℕ} (hl : 3 ≤ l) (i : Fin l) : Fin l :=
  if h : i.1 + 1 < l then ⟨i.1 + 1, h⟩ else ⟨0, by omega⟩

private def cyclePrev {l : ℕ} (hl : 3 ≤ l) (i : Fin l) : Fin l :=
  if h : i.1 = 0 then ⟨l - 1, by omega⟩ else ⟨i.1 - 1, by omega⟩

private lemma cycleAdj_iff_next_or_prev {l : ℕ} (hl : 3 ≤ l) (i j : Fin l) :
    cycleAdj i j ↔ j = cycleNext hl i ∨ j = cyclePrev hl i := by
  have hi_lt : i.1 < l := i.2
  have hj_lt : j.1 < l := j.2
  have hij_ne : i ≠ j ↔ i.1 ≠ j.1 := ⟨fun h heq => h (Fin.ext heq), fun h heq => h (congrArg Fin.val heq)⟩
  unfold cycleAdj cycleNext cyclePrev
  rw [hij_ne]
  constructor
  · rintro ⟨hne, h1 | h2 | ⟨hi0, hj⟩ | ⟨hj0, hi⟩⟩
    · left
      rw [dif_pos (by omega)]
      ext; dsimp; omega
    · right
      rw [dif_neg (by omega)]
      ext; dsimp; omega
    · right
      rw [dif_pos hi0]
      ext; dsimp; omega
    · left
      rw [dif_neg (by omega)]
      ext; dsimp; omega
  · rintro (rfl | rfl)
    · split_ifs with hlt
      · refine ⟨by dsimp; omega, Or.inl rfl⟩
      · refine ⟨by dsimp; omega, Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))⟩
    · split_ifs with hi0
      · refine ⟨by dsimp; omega, Or.inr (Or.inr (Or.inl ⟨hi0, by dsimp; omega⟩))⟩
      · refine ⟨by dsimp; omega, Or.inr (Or.inl (by dsimp; omega))⟩

private lemma cycleNext_ne_cyclePrev {l : ℕ} (hl : 3 ≤ l) (i : Fin l) :
    cycleNext hl i ≠ cyclePrev hl i := by
  have hi_lt : i.1 < l := i.2
  unfold cycleNext cyclePrev
  intro heq
  have hv := congrArg Fin.val heq
  split_ifs at hv <;> dsimp at hv <;> omega

private lemma bipyramid_degree_inl {l : ℕ} (hl : 3 ≤ l) (i : Fin l) :
    (bipyramidGraph l).degree (Sum.inl i) = 4 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hset : (bipyramidGraph l).neighborFinset (Sum.inl i) =
      {Sum.inl (cycleNext hl i), Sum.inl (cyclePrev hl i), Sum.inr true, Sum.inr false} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, mem_insert, mem_singleton]
    cases v with
    | inl j =>
      simp only [bipyramidGraph, bipyramidAdj, cycleAdj_iff_next_or_prev hl i j, Sum.inl.injEq,
        reduceCtorEq, or_false]
    | inr b =>
      cases b <;> simp [bipyramidGraph, bipyramidAdj]
  rw [hset]
  have hne1 : (Sum.inl (cycleNext hl i) : BipyramidVert l) ∉
      ({Sum.inl (cyclePrev hl i), Sum.inr true, Sum.inr false} : Finset (BipyramidVert l)) := by
    simp [cycleNext_ne_cyclePrev hl i]
  have hne2 : (Sum.inl (cyclePrev hl i) : BipyramidVert l) ∉
      ({Sum.inr true, Sum.inr false} : Finset (BipyramidVert l)) := by
    simp
  have hne3 : (Sum.inr true : BipyramidVert l) ∉
      ({Sum.inr false} : Finset (BipyramidVert l)) := by
    simp
  rw [card_insert_of_notMem hne1, card_insert_of_notMem hne2, card_insert_of_notMem hne3,
    card_singleton]

private lemma bipyramid_degree_inr {l : ℕ} (b : Bool) :
    (bipyramidGraph l).degree (Sum.inr b) = l := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hset : (bipyramidGraph l).neighborFinset (Sum.inr b) =
      univ.map Function.Embedding.inl := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, mem_map, mem_univ, true_and,
      Function.Embedding.inl_apply]
    cases v <;> simp [bipyramidGraph, bipyramidAdj]
  rw [hset, card_map, card_univ, Fintype.card_fin]

theorem bipyramidGraph_card_edgeFinset {l : ℕ} (hl : 3 ≤ l) :
    #(bipyramidGraph l).edgeFinset = 3 * l := by
  have hsum := (bipyramidGraph l).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at hsum
  have h1 : ∑ x : Fin l, (bipyramidGraph l).degree (Sum.inl x) = 4 * l := by
    simp [bipyramid_degree_inl hl, mul_comm]
  have h2 : ∑ b : Bool, (bipyramidGraph l).degree (Sum.inr b) = 2 * l := by
    simp [bipyramid_degree_inr, two_mul]
  omega

theorem ncard_edgeSet_eq_card_edgeFinset {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] : H.edgeSet.ncard = #H.edgeFinset := by
  rw [← SimpleGraph.coe_edgeFinset H, Set.ncard_coe_finset]

theorem bipyramidGraph_ncard_edgeSet {l : ℕ} (hl : 3 ≤ l) :
    (bipyramidGraph l).edgeSet.ncard = 3 * Fintype.card (BipyramidVert l) - 6 := by
  rw [ncard_edgeSet_eq_card_edgeFinset, bipyramidGraph_card_edgeFinset hl, card_bipyramidVert]
  omega

/-! ### Explicit Straight-Line Embedding of `bipyramidGraph l` (`l ≥ 3`) in `ℝ × ℝ` -/

/-- Underlying coordinate map for `bipyramidGraph l`:
`P_0 = (0, 4)`, `P_k = (k, 0)` for `1 ≤ k < l`, `N = (1, 1)`, `S = (0, -1)`. -/
def bipyramidPosFun (l : ℕ) : BipyramidVert l → ℝ × ℝ
  | Sum.inl i => if i.1 = 0 then (0, 4) else ((i.1 : ℝ), 0)
  | Sum.inr true => (1, 1)
  | Sum.inr false => (0, -1)

/-- Integer-valued straight-line vertex embedding for `bipyramidGraph l` in `ℝ × ℝ`. -/
def bipyramidPos (l : ℕ) : BipyramidVert l ↪ ℝ × ℝ where
  toFun := bipyramidPosFun l
  inj' u v h := by
    cases u with
    | inl i =>
      cases v with
      | inl j =>
        dsimp [bipyramidPosFun] at h
        split_ifs at h with hi0 hj0
        · congr; exact Fin.ext (by omega)
        · have hy : (4 : ℝ) = 0 := congrArg Prod.snd h; norm_num at hy
        · have hy : (0 : ℝ) = 4 := congrArg Prod.snd h; norm_num at hy
        · have hx : (i.1 : ℝ) = (j.1 : ℝ) := congrArg Prod.fst h
          have hij : i.1 = j.1 := by exact_mod_cast hx
          congr; exact Fin.ext hij
      | inr b =>
        cases b <;> dsimp [bipyramidPosFun] at h <;> split_ifs at h
        · have hy : (4 : ℝ) = -1 := congrArg Prod.snd h; norm_num at hy
        · have hy : (0 : ℝ) = -1 := congrArg Prod.snd h; norm_num at hy
        · have hy : (4 : ℝ) = 1 := congrArg Prod.snd h; norm_num at hy
        · have hy : (0 : ℝ) = 1 := congrArg Prod.snd h; norm_num at hy
    | inr b₁ =>
      cases v with
      | inl j =>
        cases b₁ <;> dsimp [bipyramidPosFun] at h <;> split_ifs at h
        · have hy : (-1 : ℝ) = 4 := congrArg Prod.snd h; norm_num at hy
        · have hy : (-1 : ℝ) = 0 := congrArg Prod.snd h; norm_num at hy
        · have hy : (1 : ℝ) = 4 := congrArg Prod.snd h; norm_num at hy
        · have hy : (1 : ℝ) = 0 := congrArg Prod.snd h; norm_num at hy
      | inr b₂ =>
        cases b₁ <;> cases b₂ <;> dsimp [bipyramidPosFun] at h
        · rfl
        · have hy : (-1 : ℝ) = 1 := congrArg Prod.snd h; norm_num at hy
        · have hy : (1 : ℝ) = -1 := congrArg Prod.snd h; norm_num at hy
        · rfl

@[simp] theorem bipyramidPos_inl_zero {l : ℕ} {i : Fin l} (hi : i.1 = 0) :
    bipyramidPos l (Sum.inl i) = (0, 4) := by
  change bipyramidPosFun l (Sum.inl i) = (0, 4)
  simp [bipyramidPosFun, hi]

@[simp] theorem bipyramidPos_inl_ne_zero {l : ℕ} {i : Fin l} (hi : i.1 ≠ 0) :
    bipyramidPos l (Sum.inl i) = ((i.1 : ℝ), 0) := by
  change bipyramidPosFun l (Sum.inl i) = ((i.1 : ℝ), 0)
  simp [bipyramidPosFun, hi]

@[simp] theorem bipyramidPos_inr_true (l : ℕ) :
    bipyramidPos l (Sum.inr true) = (1, 1) := rfl

@[simp] theorem bipyramidPos_inr_false (l : ℕ) :
    bipyramidPos l (Sum.inr false) = (0, -1) := rfl

/-- Canonical classification of unordered edges of `bipyramidGraph l` (`l ≥ 3`). -/
private inductive BipyramidEdgeTag (l : ℕ) : Type
  | southZero : BipyramidEdgeTag l
  | southPos (k : Fin l) (hk : 1 ≤ k.1) : BipyramidEdgeTag l
  | horiz (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k + 1 < l) : BipyramidEdgeTag l
  | leftLid : BipyramidEdgeTag l
  | rightLid : BipyramidEdgeTag l
  | northZero : BipyramidEdgeTag l
  | northPos (k : Fin l) (hk : 1 ≤ k.1) : BipyramidEdgeTag l

private def edgeEndpoints {l : ℕ} (hl : 3 ≤ l) :
    BipyramidEdgeTag l → BipyramidVert l × BipyramidVert l
  | .southZero => (Sum.inr false, Sum.inl ⟨0, by omega⟩)
  | .southPos k _ => (Sum.inr false, Sum.inl k)
  | .horiz k _ hk2 => (Sum.inl ⟨k, by omega⟩, Sum.inl ⟨k + 1, hk2⟩)
  | .leftLid => (Sum.inl ⟨0, by omega⟩, Sum.inl ⟨1, by omega⟩)
  | .rightLid => (Sum.inl ⟨0, by omega⟩, Sum.inl ⟨l - 1, by omega⟩)
  | .northZero => (Sum.inr true, Sum.inl ⟨0, by omega⟩)
  | .northPos k _ => (Sum.inr true, Sum.inl k)

private lemma classify_bipyramid_edge {l : ℕ} (hl : 3 ≤ l) {u v : BipyramidVert l}
    (hadj : (bipyramidGraph l).Adj u v) :
    ∃ tag : BipyramidEdgeTag l,
      (u = (edgeEndpoints hl tag).1 ∧ v = (edgeEndpoints hl tag).2) ∨
      (u = (edgeEndpoints hl tag).2 ∧ v = (edgeEndpoints hl tag).1) := by
  cases u with
  | inl i =>
    have hi_lt : i.1 < l := i.2
    cases v with
    | inl j =>
      have hj_lt : j.1 < l := j.2
      rcases hadj with ⟨_, h1 | h2 | ⟨hi0, hj⟩ | ⟨hj0, hi⟩⟩
      · by_cases hi0 : i.1 = 0
        · refine ⟨.leftLid, Or.inl ⟨?_, ?_⟩⟩ <;> (dsimp [edgeEndpoints]; congr; exact Fin.ext (by dsimp; omega))
        · refine ⟨.horiz i.1 (by omega) (by omega), Or.inl ⟨rfl, ?_⟩⟩
          dsimp [edgeEndpoints]; congr; exact Fin.ext (by dsimp; omega)
      · by_cases hj0 : j.1 = 0
        · refine ⟨.leftLid, Or.inr ⟨?_, ?_⟩⟩ <;> (dsimp [edgeEndpoints]; congr; exact Fin.ext (by dsimp; omega))
        · refine ⟨.horiz j.1 (by omega) (by omega), Or.inr ⟨?_, rfl⟩⟩
          dsimp [edgeEndpoints]; congr; exact Fin.ext (by dsimp; omega)
      · refine ⟨.rightLid, Or.inl ⟨?_, ?_⟩⟩ <;> (dsimp [edgeEndpoints]; congr; exact Fin.ext (by dsimp; omega))
      · refine ⟨.rightLid, Or.inr ⟨?_, ?_⟩⟩ <;> (dsimp [edgeEndpoints]; congr; exact Fin.ext (by dsimp; omega))
    | inr b =>
      cases b
      · by_cases hi0 : i.1 = 0
        · refine ⟨.southZero, Or.inr ⟨?_, rfl⟩⟩
          dsimp [edgeEndpoints]; congr; exact Fin.ext (by omega)
        · exact ⟨.southPos i (by omega), Or.inr ⟨rfl, rfl⟩⟩
      · by_cases hi0 : i.1 = 0
        · refine ⟨.northZero, Or.inr ⟨?_, rfl⟩⟩
          dsimp [edgeEndpoints]; congr; exact Fin.ext (by omega)
        · exact ⟨.northPos i (by omega), Or.inr ⟨rfl, rfl⟩⟩
  | inr b =>
    cases v with
    | inl j =>
      cases b
      · by_cases hj0 : j.1 = 0
        · refine ⟨.southZero, Or.inl ⟨rfl, ?_⟩⟩
          dsimp [edgeEndpoints]; congr; exact Fin.ext (by omega)
        · exact ⟨.southPos j (by omega), Or.inl ⟨rfl, rfl⟩⟩
      · by_cases hj0 : j.1 = 0
        · refine ⟨.northZero, Or.inl ⟨rfl, ?_⟩⟩
          dsimp [edgeEndpoints]; congr; exact Fin.ext (by omega)
        · exact ⟨.northPos j (by omega), Or.inl ⟨rfl, rfl⟩⟩
    | inr _ => exact False.elim hadj

/-- Coordinates of `lineSeg` along each canonical oriented edge tag. -/
private lemma tag_seg_coords {l : ℕ} (hl : 3 ≤ l) (tag : BipyramidEdgeTag l) (s : ℝ) :
    lineSeg (bipyramidPos l (edgeEndpoints hl tag).1)
        (bipyramidPos l (edgeEndpoints hl tag).2) s =
      match tag with
      | .southZero => (0, -1 + 5 * s)
      | .southPos k _ => (s * (k.1 : ℝ), s - 1)
      | .horiz k _ _ => ((k : ℝ) + s, 0)
      | .leftLid => (s, 4 - 4 * s)
      | .rightLid => (s * ((l - 1 : ℕ) : ℝ), 4 - 4 * s)
      | .northZero => (1 - s, 1 + 3 * s)
      | .northPos k _ => (1 - s + s * (k.1 : ℝ), 1 - s) := by
  cases tag with
  | southZero =>
    dsimp [edgeEndpoints]
    rw [bipyramidPos_inl_zero rfl]
    ext <;> dsimp [lineSeg] <;> ring
  | southPos k hk =>
    have hk0 : k.1 ≠ 0 := by omega
    dsimp [edgeEndpoints]
    rw [bipyramidPos_inl_ne_zero hk0]
    ext <;> dsimp [lineSeg] <;> ring
  | horiz k hk1 hk2 =>
    have hk0 : (⟨k, by omega⟩ : Fin l).1 ≠ 0 := by dsimp; omega
    have hk10 : (⟨k + 1, hk2⟩ : Fin l).1 ≠ 0 := by dsimp; omega
    dsimp [edgeEndpoints]
    rw [bipyramidPos_inl_ne_zero hk0, bipyramidPos_inl_ne_zero hk10]
    ext <;> dsimp [lineSeg] <;> push_cast <;> ring
  | leftLid =>
    have h10 : (⟨1, by omega⟩ : Fin l).1 ≠ 0 := by dsimp; omega
    dsimp [edgeEndpoints]
    rw [bipyramidPos_inl_zero rfl, bipyramidPos_inl_ne_zero h10]
    ext <;> dsimp [lineSeg] <;> push_cast <;> ring
  | rightLid =>
    have hl0 : (⟨l - 1, by omega⟩ : Fin l).1 ≠ 0 := by dsimp; omega
    dsimp [edgeEndpoints]
    rw [bipyramidPos_inl_zero rfl, bipyramidPos_inl_ne_zero hl0]
    ext <;> dsimp [lineSeg] <;> ring
  | northZero =>
    dsimp [edgeEndpoints]
    rw [bipyramidPos_inl_zero rfl]
    ext <;> dsimp [lineSeg] <;> ring
  | northPos k hk =>
    have hk0 : k.1 ≠ 0 := by omega
    dsimp [edgeEndpoints]
    rw [bipyramidPos_inl_ne_zero hk0]
    ext <;> dsimp [lineSeg] <;> ring

private def tagRegionProp {l : ℕ} (tag : BipyramidEdgeTag l) (p : ℝ × ℝ) : Prop :=
  (-1 < p.2 ∧ p.2 < 4) ∧
  match tag with
  | .southZero => p.1 = 0
  | .southPos _ _ => 0 < p.1 ∧ p.2 < 0
  | .horiz k _ _ => 0 < p.1 ∧ p.2 = 0 ∧ (k : ℝ) < p.1 ∧ p.1 < (k : ℝ) + 1
  | .leftLid => 0 < p.1 ∧ 0 < p.2 ∧ 4 * p.1 + p.2 = 4
  | .rightLid =>
      0 < p.1 ∧ 0 < p.2 ∧ 4 < 4 * p.1 + p.2 ∧
      4 * p.1 + ((l - 1 : ℕ) : ℝ) * p.2 = 4 * ((l - 1 : ℕ) : ℝ)
  | .northZero =>
      0 < p.1 ∧ 1 < p.2 ∧ 4 < 4 * p.1 + p.2 ∧
      4 * p.1 + ((l - 1 : ℕ) : ℝ) * p.2 < 4 * ((l - 1 : ℕ) : ℝ)
  | .northPos _ _ =>
      0 < p.1 ∧ 0 < p.2 ∧ p.2 < 1 ∧ 4 < 4 * p.1 + p.2 ∧
      4 * p.1 + ((l - 1 : ℕ) : ℝ) * p.2 < 4 * ((l - 1 : ℕ) : ℝ)

/-- Region invariants separating all 7 canonical edge tags on `s ∈ (0, 1)`. -/
private lemma tag_open_props {l : ℕ} (hl : 3 ≤ l) (tag : BipyramidEdgeTag l)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    tagRegionProp tag
      (lineSeg (bipyramidPos l (edgeEndpoints hl tag).1)
        (bipyramidPos l (edgeEndpoints hl tag).2) s) := by
  rw [tag_seg_coords hl tag s]
  have hl_real : (2 : ℝ) ≤ ((l - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ l - 1 by omega)
  cases tag with
  | southZero =>
    exact ⟨⟨by linarith, by linarith⟩, rfl⟩
  | southPos k hk =>
    have hk_real : (1 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast hk
    exact ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by linarith⟩⟩
  | horiz k hk1 _ =>
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, rfl, by linarith, by linarith⟩⟩
  | leftLid =>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith, by ring⟩⟩
  | rightLid =>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by linarith, by nlinarith, by ring⟩⟩
  | northZero =>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith, by nlinarith⟩⟩
  | northPos k hk =>
    have hk_lt : k.1 < l := k.2
    have hk_real : (1 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast hk
    have hkl_real : (k.1 : ℝ) ≤ ((l - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show k.1 ≤ l - 1 by omega)
    exact ⟨⟨by linarith, by linarith⟩,
      ⟨by nlinarith, by linarith, by linarith, by nlinarith, by nlinarith⟩⟩

/-- Every bipyramid `B_l = C_l ∨ 2K_1` (`l ≥ 3`) is topologically planar in `ℝ × ℝ`. -/
theorem bipyramidGraph_isPlanar {l : ℕ} (hl : 3 ≤ l) : IsPlanar (bipyramidGraph l) := by
  have hl_real : (2 : ℝ) ≤ ((l - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ l - 1 by omega)
  apply IsPlanar.of_straightLine (bipyramidPos l)
  · -- 1. Open edge segments avoid all vertex positions
    intro u v w hadj t ht0 ht1 heq
    obtain ⟨tag, hdir⟩ := classify_bipyramid_edge hl hadj
    obtain ⟨s, hs0, hs1, hseg⟩ : ∃ s : ℝ, 0 < s ∧ s < 1 ∧
        lineSeg (bipyramidPos l u) (bipyramidPos l v) t =
          lineSeg (bipyramidPos l (edgeEndpoints hl tag).1)
            (bipyramidPos l (edgeEndpoints hl tag).2) s := by
      rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨t, ht0, ht1, rfl⟩
      · exact ⟨1 - t, by linarith, by linarith, lineSeg_symm _ _ t⟩
    rw [hseg] at heq
    have hprops := tag_open_props hl tag hs0 hs1
    rw [heq] at hprops
    rcases hprops with ⟨⟨hy_gt, hy_lt⟩, hreg⟩
    cases w with
    | inr b =>
      cases b
      · -- South apex `(0, -1)`
        rw [bipyramidPos_inr_false] at hy_gt
        dsimp at hy_gt
        linarith
      · -- North apex `(1, 1)`
        rw [bipyramidPos_inr_true] at hreg
        cases tag <;> dsimp [tagRegionProp] at hreg <;> linarith
    | inl m =>
      by_cases hm0 : m.1 = 0
      · -- `P_0 = (0, 4)`
        rw [bipyramidPos_inl_zero hm0] at hy_lt
        dsimp at hy_lt
        linarith
      · -- `P_m = (m, 0)` with `m ≥ 1`
        rw [bipyramidPos_inl_ne_zero hm0] at hreg
        cases tag with
        | southZero =>
          dsimp [tagRegionProp] at hreg
          have hm_pos : (0 : ℝ) < (m.1 : ℝ) := by exact_mod_cast (show 0 < m.1 by omega)
          linarith
        | southPos _ _ => dsimp [tagRegionProp] at hreg; linarith
        | horiz k _ _ =>
          dsimp [tagRegionProp] at hreg
          rcases hreg with ⟨_, _, hlt1, hlt2⟩
          have hmk : m.1 ≤ k ∨ k + 1 ≤ m.1 := by omega
          rcases hmk with hle | hge
          · have hle_r : (m.1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle
            linarith
          · have hge_r : (k : ℝ) + 1 ≤ (m.1 : ℝ) := by exact_mod_cast hge
            linarith
        | leftLid => dsimp [tagRegionProp] at hreg; linarith
        | rightLid => dsimp [tagRegionProp] at hreg; linarith
        | northZero => dsimp [tagRegionProp] at hreg; linarith
        | northPos _ _ => dsimp [tagRegionProp] at hreg; linarith
  · -- 2. Open edge segments of distinct unordered edges are pairwise disjoint
    intro u₁ v₁ u₂ v₂ hadj₁ hadj₂ hne t₁ t₂ ht1_0 ht1_1 ht2_0 ht2_1 heq
    obtain ⟨tag₁, hdir₁⟩ := classify_bipyramid_edge hl hadj₁
    obtain ⟨tag₂, hdir₂⟩ := classify_bipyramid_edge hl hadj₂
    obtain ⟨s₁, hs1_0, hs1_1, hseg₁, hsym₁⟩ : ∃ s₁ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧
        lineSeg (bipyramidPos l u₁) (bipyramidPos l v₁) t₁ =
          lineSeg (bipyramidPos l (edgeEndpoints hl tag₁).1)
            (bipyramidPos l (edgeEndpoints hl tag₁).2) s₁ ∧
        s(u₁, v₁) = s((edgeEndpoints hl tag₁).1, (edgeEndpoints hl tag₁).2) := by
      rcases hdir₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨t₁, ht1_0, ht1_1, rfl, rfl⟩
      · exact ⟨1 - t₁, by linarith, by linarith, lineSeg_symm _ _ t₁, Sym2.eq_swap⟩
    obtain ⟨s₂, hs2_0, hs2_1, hseg₂, hsym₂⟩ : ∃ s₂ : ℝ, 0 < s₂ ∧ s₂ < 1 ∧
        lineSeg (bipyramidPos l u₂) (bipyramidPos l v₂) t₂ =
          lineSeg (bipyramidPos l (edgeEndpoints hl tag₂).1)
            (bipyramidPos l (edgeEndpoints hl tag₂).2) s₂ ∧
        s(u₂, v₂) = s((edgeEndpoints hl tag₂).1, (edgeEndpoints hl tag₂).2) := by
      rcases hdir₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨t₂, ht2_0, ht2_1, rfl, rfl⟩
      · exact ⟨1 - t₂, by linarith, by linarith, lineSeg_symm _ _ t₂, Sym2.eq_swap⟩
    have htag_ne : tag₁ ≠ tag₂ := by
      intro hsame
      apply hne
      rw [hsym₁, hsym₂, hsame]
    have hp₁ := tag_open_props hl tag₁ hs1_0 hs1_1
    have hp₂ := tag_open_props hl tag₂ hs2_0 hs2_1
    rw [hseg₁, hseg₂] at heq
    rw [heq] at hp₁
    rcases hp₁ with ⟨_, hr₁⟩
    rcases hp₂ with ⟨_, hr₂⟩
    cases tag₁ with
    | southZero =>
      cases tag₂ with
      | southZero => exact htag_ne rfl
      | _ => dsimp at hr₁ hr₂; linarith
    | southPos k₁ hk₁ =>
      cases tag₂ with
      | southPos k₂ hk₂ =>
        rw [tag_seg_coords hl (.southPos k₁ hk₁) s₁,
            tag_seg_coords hl (.southPos k₂ hk₂) s₂] at heq
        have hy : s₁ - 1 = s₂ - 1 := congrArg Prod.snd heq
        have hs_eq : s₁ = s₂ := by linarith
        have hx : s₁ * (k₁.1 : ℝ) = s₂ * (k₂.1 : ℝ) := congrArg Prod.fst heq
        rw [hs_eq] at hx
        have hk_real : (k₁.1 : ℝ) = (k₂.1 : ℝ) := mul_left_cancel₀ (ne_of_gt hs2_0) hx
        have hk_eq : k₁ = k₂ := Fin.ext (by exact_mod_cast hk_real)
        subst hk_eq
        exact htag_ne rfl
      | _ => dsimp at hr₁ hr₂; linarith
    | horiz k₁ hk1_1 hk2_1 =>
      cases tag₂ with
      | horiz k₂ hk1_2 hk2_2 =>
        dsimp at hr₁ hr₂
        rcases hr₁ with ⟨_, _, hl1, hr1_lt⟩
        rcases hr₂ with ⟨_, _, hl2, hr2_lt⟩
        have hcmp : k₁ = k₂ ∨ k₁ + 1 ≤ k₂ ∨ k₂ + 1 ≤ k₁ := by omega
        rcases hcmp with rfl | hle | hge
        · exact htag_ne rfl
        · have hle_r : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by exact_mod_cast hle
          linarith
        · have hge_r : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by exact_mod_cast hge
          linarith
      | _ => dsimp at hr₁ hr₂; linarith
    | leftLid =>
      cases tag₂ with
      | leftLid => exact htag_ne rfl
      | _ => dsimp at hr₁ hr₂; linarith
    | rightLid =>
      cases tag₂ with
      | rightLid => exact htag_ne rfl
      | _ => dsimp at hr₁ hr₂; linarith
    | northZero =>
      cases tag₂ with
      | northZero => exact htag_ne rfl
      | _ => dsimp at hr₁ hr₂; linarith
    | northPos k₁ hk₁ =>
      cases tag₂ with
      | northPos k₂ hk₂ =>
        rw [tag_seg_coords hl (.northPos k₁ hk₁) s₁,
            tag_seg_coords hl (.northPos k₂ hk₂) s₂] at heq
        have hy : 1 - s₁ = 1 - s₂ := congrArg Prod.snd heq
        have hs_eq : s₁ = s₂ := by linarith
        have hx : 1 - s₁ + s₁ * (k₁.1 : ℝ) = 1 - s₂ + s₂ * (k₂.1 : ℝ) := congrArg Prod.fst heq
        rw [hs_eq] at hx
        have hmul : s₂ * (k₁.1 : ℝ) = s₂ * (k₂.1 : ℝ) := by linarith
        have hk_real : (k₁.1 : ℝ) = (k₂.1 : ℝ) := mul_left_cancel₀ (ne_of_gt hs2_0) hmul
        have hk_eq : k₁ = k₂ := Fin.ext (by exact_mod_cast hk_real)
        subst hk_eq
        exact htag_ne rfl
      | _ => dsimp at hr₁ hr₂; linarith

/-! ### `K_4` Planarity and Edge Count as a Copy Inside `bipyramidGraph 3` -/

/-- Injection of `K_4` (`⊤ : SimpleGraph (Fin 4)`) into `bipyramidGraph 3` (`{P_0, P_1, P_2, N}`). -/
def k4ToBipyramid3 : SimpleGraph.Copy (⊤ : SimpleGraph (Fin 4)) (bipyramidGraph 3) where
  toHom := {
    toFun := fun i =>
      if h : i.1 < 3 then Sum.inl ⟨i.1, h⟩ else Sum.inr true
    map_rel' := by
      intro i j hij
      have hne : i ≠ j := hij
      fin_cases i <;> fin_cases j <;> simp_all [bipyramidGraph, bipyramidAdj, cycleAdj]
  }
  injective' := by
    intro i j heq
    fin_cases i <;> fin_cases j <;> simp_all

theorem completeGraph_fin4_isPlanar : IsPlanar (⊤ : SimpleGraph (Fin 4)) :=
  IsPlanar.of_copy k4ToBipyramid3 (bipyramidGraph_isPlanar (by decide))

theorem completeGraph_fin4_card_edgeFinset :
    #(⊤ : SimpleGraph (Fin 4)).edgeFinset = 6 := by
  decide

theorem completeGraph_fin4_ncard_edgeSet :
    (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard = 3 * Fintype.card (Fin 4) - 6 := by
  rw [ncard_edgeSet_eq_card_edgeFinset, completeGraph_fin4_card_edgeFinset, Fintype.card_fin]

end Erdos1019
