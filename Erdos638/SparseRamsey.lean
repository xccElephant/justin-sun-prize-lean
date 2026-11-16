import Erdos638.Defs
import Erdos638.Container
import Erdos638.GridCounting
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Locally Sparse `r`-Color Triangle-Ramsey Graphs via Finite Product Counting

In this module we prove from first principles (zero probability/measure theory, zero real analysis):

**Theorem (`exists_locally_sparse_triangle_ramsey`)**:
For every number of colors `r ≥ 1` and every vertex threshold `B ≥ 4`, there exists a finite
simple graph `W : FiniteGraph` such that:
1. `ForcesMonoTriangle W.graph (Fin r)` (`W → (K₃)²_r`), and
2. For every subset `S : Finset (Fin W.verts)` with `4 ≤ S.card ≤ B`,
   `edgesInside W.graph S ≤ 2 * S.card - 3`!

Combined with `exists_dense_four_plus_subset` from `Erdos638.Defs`, this immediately yields the
**Finite Core Avoidance Theorem (`exists_ramsey_avoiding_family`)**:
Given ANY finite set `F` of finite 2-Ramsey graphs (in particular minimal 2-Ramsey cores, taking
`B` to be the maximum vertex count in `F`), there exists a finite graph `W` with `W → (K₃)²_r`
into which NO member of `F` embeds as an ordinary subgraph!
-/

namespace Erdos638

open scoped Classical BigOperators
open Erdos638.Container

/-! ## 1. Classical Multicolor Triangle Ramsey Number `R_r(3)` -/

/-- Explicit recursive upper bound for the `r`-color triangle Ramsey number on complete graphs:
`ramseyBound 0 = 1`, `ramseyBound (r + 1) = (r + 1) * ramseyBound r + 2`.
Note `ramseyBound 1 = 3`, `ramseyBound 2 = 8` (`≥ R(3,3) = 6`). -/
def ramseyBound : ℕ → ℕ
  | 0 => 1
  | r + 1 => (r + 1) * ramseyBound r + 2

lemma ramseyBound_ge_three {r : ℕ} (hr : 1 ≤ r) : 3 ≤ ramseyBound r := by
  cases r with
  | zero => omega
  | succ r =>
    simp only [ramseyBound]
    have hpos : 1 ≤ ramseyBound r := by
      induction r with
      | zero => decide
      | succ k ih => simp [ramseyBound]
    nlinarith

/-- Classical Ramsey theorem for triangles on complete graphs `⊤ : SimpleGraph (Fin (ramseyBound r))`. -/
theorem completeGraph_forcesMonoTriangle :
    ∀ (r : ℕ), 1 ≤ r →
      ∀ col : Sym2 (Fin (ramseyBound r)) → Fin r,
        HasMonoTriangle (⊤ : SimpleGraph (Fin (ramseyBound r))) col
  | 0, hr, _ => absurd hr (by decide)
  | 1, _, col => by
    let v0 : Fin (ramseyBound 1) := ⟨0, by decide⟩
    let v1 : Fin (ramseyBound 1) := ⟨1, by decide⟩
    let v2 : Fin (ramseyBound 1) := ⟨2, by decide⟩
    refine ⟨v0, v1, v2, by simp [v0, v1], by simp [v1, v2], by simp [v0, v2], ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  | r + 2, _, col => by
    let R' := ramseyBound (r + 1)
    have hR'_ge3 : 3 ≤ R' := ramseyBound_ge_three (by omega)
    let N := ramseyBound (r + 2)
    have hN_eq : N = (r + 2) * R' + 2 := rfl
    let v0 : Fin N := ⟨0, by omega⟩
    let rest : Finset (Fin N) := Finset.univ.erase v0
    have hrest_card : rest.card = (r + 2) * R' + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v0), Finset.card_univ, Fintype.card_fin]
      omega
    -- Partition `rest` into `r + 2` color fibers according to `col s(v0, u)`:
    -- since `rest.card > (r + 2) * R'`, some color `c₀ : Fin (r + 2)` has fiber of size `≥ R' + 1 ≥ R'`!
    have hex_fiber : ∃ c₀ : Fin (r + 2), R' ≤ (rest.filter (fun u => col s(v0, u) = c₀)).card := by
      by_contra! hlt
      have hsum_eq : ∑ c : Fin (r + 2), (rest.filter (fun u => col s(v0, u) = c)).card = rest.card := by
        simpa using Finset.card_eq_sum_card_fiberwise
          (f := fun u => col s(v0, u)) (s := rest) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _) |>.symm
      have hsum_le : ∑ c : Fin (r + 2), (rest.filter (fun u => col s(v0, u) = c)).card ≤
          (r + 2) * R' := by
        have h1 : ∀ c ∈ (Finset.univ : Finset (Fin (r + 2))),
            (rest.filter (fun u => col s(v0, u) = c)).card ≤ R' - 1 := by
          intro c _; have := hlt c; omega
        calc ∑ c : Fin (r + 2), (rest.filter (fun u => col s(v0, u) = c)).card
            ≤ ∑ _c : Fin (r + 2), (R' - 1) := Finset.sum_le_sum h1
          _ = (r + 2) * (R' - 1) := by simp
          _ ≤ (r + 2) * R' := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega
    obtain ⟨c₀, hc₀_card⟩ := hex_fiber
    let fib := rest.filter (fun u => col s(v0, u) = c₀)
    obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hc₀_card
    -- Check if `S` already contains an edge `s(u, w)` (`u ≠ w`) of color `c₀`:
    by_cases hex_c₀ : ∃ u ∈ S, ∃ w ∈ S, u ≠ w ∧ col s(u, w) = c₀
    · obtain ⟨u, huS, w, hwS, huw, hcol_uw⟩ := hex_c₀
      have hu_fib : u ∈ fib := hS_sub huS
      have hw_fib : w ∈ fib := hS_sub hwS
      have hv0_u : v0 ≠ u := (Finset.mem_erase.mp (Finset.mem_filter.mp hu_fib).1).1.symm
      have hv0_w : v0 ≠ w := (Finset.mem_erase.mp (Finset.mem_filter.mp hw_fib).1).1.symm
      have hcol_v0u : col s(v0, u) = c₀ := (Finset.mem_filter.mp hu_fib).2
      have hcol_v0w : col s(v0, w) = c₀ := (Finset.mem_filter.mp hw_fib).2
      exact ⟨v0, u, w, hv0_u, huw, hv0_w,
        by rw [hcol_v0u, hcol_uw], by rw [hcol_uw, hcol_v0w]⟩
    · -- Every distinct pair `u ≠ w` in `S` has `col s(u, w) ≠ c₀`!
      -- Biject `Fin R' ≃ S` and map `Fin (r + 2) \ {c₀}` to `Fin (r + 1)` via `c₀.predAbove`!
      have hex_c₀_neg : ∀ u ∈ S, ∀ w ∈ S, u ≠ w → col s(u, w) ≠ c₀ := by
        intro u hu w hw huw hcol
        exact hex_c₀ ⟨u, hu, w, hw, huw, hcol⟩
      have hcard_S : Fintype.card S = R' := by simpa using hS_card
      let embS : Fin R' ≃ S := (Fintype.equivFinOfCardEq hcard_S).symm
      let shrinkColor : Fin (r + 2) → Fin (r + 1) := fun c =>
        if hlt : c.val < c₀.val then ⟨c.val, by omega⟩
        else ⟨c.val - 1, by omega⟩
      have hshrink_inj_away : ∀ a b : Fin (r + 2), a ≠ c₀ → b ≠ c₀ →
          shrinkColor a = shrinkColor b → a = b := by
        intro a b ha hb heq
        have ha_ne : a.val ≠ c₀.val := Fin.val_ne_of_ne ha
        have hb_ne : b.val ≠ c₀.val := Fin.val_ne_of_ne hb
        have hval := congrArg Fin.val heq
        simp only [shrinkColor] at hval
        by_cases hal : a.val < c₀.val <;> by_cases hbl : b.val < c₀.val <;>
          simp [hal, hbl] at hval <;> ext <;> omega
      let col' : Sym2 (Fin R') → Fin (r + 1) :=
        Sym2.lift ⟨fun i j => shrinkColor (col s((embS i).1, (embS j).1)), by
          intro i j; simp [Sym2.eq_swap]⟩
      obtain ⟨i, j, k, hij, hjk, hik, h1, h2⟩ :=
        completeGraph_forcesMonoTriangle (r + 1) (by omega) col'
      have hij_ne : (embS i).1 ≠ (embS j).1 := fun h => hij (embS.injective (Subtype.ext h))
      have hjk_ne : (embS j).1 ≠ (embS k).1 := fun h => hjk (embS.injective (Subtype.ext h))
      have hik_ne : (embS i).1 ≠ (embS k).1 := fun h => hik (embS.injective (Subtype.ext h))
      have hc_ij : col s((embS i).1, (embS j).1) ≠ c₀ :=
        hex_c₀_neg (embS i).1 (embS i).2 (embS j).1 (embS j).2 hij_ne
      have hc_jk : col s((embS j).1, (embS k).1) ≠ c₀ :=
        hex_c₀_neg (embS j).1 (embS j).2 (embS k).1 (embS k).2 hjk_ne
      have hc_ik : col s((embS i).1, (embS k).1) ≠ c₀ :=
        hex_c₀_neg (embS i).1 (embS i).2 (embS k).1 (embS k).2 hik_ne
      refine ⟨(embS i).1, (embS j).1, (embS k).1, hij_ne, hjk_ne, hik_ne, ?_, ?_⟩
      · exact hshrink_inj_away _ _ hc_ij hc_jk h1
      · exact hshrink_inj_away _ _ hc_jk hc_ik h2

/-! ## 2. Indexing the Edges and Triangles of `K_n` on `Fin (n.choose 2)` -/

section CompleteHypergraph

/-- All non-diagonal edges of the complete graph on `Fin n` (`powersetCard 2`). -/
def completeEdges (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard 2

lemma card_completeEdges (n : ℕ) : (completeEdges n).card = n.choose 2 := by
  simp [completeEdges, Finset.card_powersetCard]

/-- Canonical equivalence `Fin (n.choose 2) ≃ completeEdges n`. -/
noncomputable def edgeIndexEquiv (n : ℕ) : Fin (n.choose 2) ≃ completeEdges n :=
  (Fintype.equivFinOfCardEq (by simp [card_completeEdges])).symm

/-- Map a 3-vertex subset `t ∈ powersetCard 3` to the 3-element `Finset (Fin (n.choose 2))`
of its three 2-element subsets! -/
noncomputable def triangleEdgeIndices (n : ℕ) (t : Finset (Fin n)) : Finset (Fin (n.choose 2)) :=
  (t.powersetCard 2).attach.image (fun e : { x // x ∈ t.powersetCard 2 } =>
    let he : e.1 ∈ completeEdges n := by
      rw [completeEdges, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp e.2).2⟩
    (edgeIndexEquiv n).symm ⟨e.1, he⟩)

lemma triangleEdgeIndices_card {n : ℕ} {t : Finset (Fin n)}
    (ht : t ∈ (Finset.univ : Finset (Fin n)).powersetCard 3) :
    (triangleEdgeIndices n t).card = 3 := by
  have ht3 : t.card = 3 := (Finset.mem_powersetCard.mp ht).2
  unfold triangleEdgeIndices
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_attach, Finset.card_powersetCard, ht3]; decide
  · intro a b hab
    have hsub := (edgeIndexEquiv n).symm.injective hab
    have hv : a.1 = b.1 := congrArg (Subtype.val : completeEdges n → Finset (Fin n)) hsub
    exact Subtype.ext hv

lemma triangleEdgeIndices_injective (n : ℕ) :
    Set.InjOn (triangleEdgeIndices n) ((Finset.univ : Finset (Fin n)).powersetCard 3) := by
  intro t₁ ht₁ t₂ ht₂ heq
  have ht₁_3 : t₁.card = 3 := (Finset.mem_powersetCard.mp ht₁).2
  have ht₂_3 : t₂.card = 3 := (Finset.mem_powersetCard.mp ht₂).2
  have hmem_iff : ∀ {t : Finset (Fin n)}, t.card = 3 → ∀ x : Fin n,
      x ∈ t ↔ ∃ i ∈ triangleEdgeIndices n t, x ∈ ((edgeIndexEquiv n) i).1 := by
    intro t htc x
    constructor
    · intro hxt
      have hrem : 1 ≤ (t.erase x).card := by
        rw [Finset.card_erase_of_mem hxt]; omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hrem
      have hy_ne : y ≠ x := (Finset.mem_erase.mp hy).1
      have hyt : y ∈ t := (Finset.mem_erase.mp hy).2
      let pair : Finset (Fin n) := {x, y}
      have hpair_mem : pair ∈ t.powersetCard 2 := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair hy_ne.symm⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hzy
        · exact hxt
        · rw [Finset.mem_singleton.mp hzy]; exact hyt
      have hpair_comp : pair ∈ completeEdges n := by
        rw [completeEdges, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, Finset.card_pair hy_ne.symm⟩
      let idx := (edgeIndexEquiv n).symm ⟨pair, hpair_comp⟩
      refine ⟨idx, ?_, ?_⟩
      · unfold triangleEdgeIndices
        exact Finset.mem_image.mpr ⟨⟨pair, hpair_mem⟩, Finset.mem_attach _ _, rfl⟩
      · simp [idx, pair]
    · rintro ⟨i, hi, hxi⟩
      unfold triangleEdgeIndices at hi
      rcases Finset.mem_image.mp hi with ⟨⟨pair, hpair⟩, _, rfl⟩
      simp only [Equiv.apply_symm_apply] at hxi
      exact (Finset.mem_powersetCard.mp hpair).1 hxi
  ext x
  rw [hmem_iff ht₁_3, hmem_iff ht₂_3, heq]

/-- The 3-uniform triangle hypergraph `T(K_n)` on `Fin (n.choose 2)`. -/
@[irreducible] noncomputable def triangleHypergraph (n : ℕ) : Finset (Finset (Fin (n.choose 2))) :=
  ((Finset.univ : Finset (Fin n)).powersetCard 3).image (triangleEdgeIndices n)

lemma card_triangleHypergraph (n : ℕ) : (triangleHypergraph n).card = n.choose 3 := by
  unfold triangleHypergraph
  rw [Finset.card_image_of_injOn (triangleEdgeIndices_injective n),
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma triangleHypergraph_uniform (n : ℕ) :
    ∀ e ∈ triangleHypergraph n, 1 ≤ e.card ∧ e.card ≤ 3 := by
  intro e he
  unfold triangleHypergraph at he
  rcases Finset.mem_image.mp he with ⟨t, ht, rfl⟩
  have hc := triangleEdgeIndices_card ht
  omega

lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    cases k with
    | zero => decide
    | succ j => simp at ih ⊢; nlinarith

/-- Crucial algebraic identity: `3 * n.choose 3 = (n - 2) * n.choose 2` for all `n`! -/
lemma three_mul_choose_three (n : ℕ) : 3 * n.choose 3 = (n - 2) * n.choose 2 := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ m =>
      induction m with
      | zero => decide
      | succ k ih =>
        have h1 : (k + 3).choose 3 = (k + 2).choose 2 + (k + 2).choose 3 :=
          Nat.choose_succ_succ (k + 2) 2
        have h2 : (k + 3).choose 2 = (k + 2) + (k + 2).choose 2 := by
          have ha : (k + 3).choose 2 = (k + 2).choose 1 + (k + 2).choose 2 :=
            Nat.choose_succ_succ (k + 2) 1
          rw [ha, Nat.choose_one_right]
        have hk2 : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := two_mul_choose_two (k + 2)
        have ih' : 3 * (k + 2).choose 3 = k * (k + 2).choose 2 := by simpa using ih
        change 3 * (k + 3).choose 3 = (k + 1) * (k + 3).choose 2
        nlinarith

theorem triangleHypergraph_isSpread (m : ℕ) (hm : 1 ≤ m) :
    (uniformInducedHypergraph (triangleHypergraph (m ^ 2 + 2))
      (Finset.univ : Finset (Fin ((m ^ 2 + 2).choose 2)))).IsSpread (1 / (m : ℚ)) 3 := by
  let n := m ^ 2 + 2
  let N₀ := n.choose 2
  let p : ℚ := 1 / (m : ℚ)
  let H_all := uniformInducedHypergraph (triangleHypergraph n) (Finset.univ : Finset (Fin N₀))
  have hn_ge3 : 3 ≤ n := by dsimp [n]; nlinarith
  have hN₀_pos : 0 < N₀ := Nat.choose_pos (by omega)
  have hM_eq : H_all.totalWeight = (n.choose 3 : ℚ) := by
    rw [uniformInducedHypergraph_totalWeight]
    have hfilt : (triangleHypergraph n).filter (fun e => e ⊆ Finset.univ) = triangleHypergraph n :=
      Finset.filter_true_of_mem (fun e _ => Finset.subset_univ e)
    rw [hfilt, card_triangleHypergraph]
  have h_abs : (3 : ℚ) * (n.choose 3 : ℚ) / (N₀ : ℚ) = (m : ℚ) ^ 2 := by
    have hid : 3 * n.choose 3 = m ^ 2 * N₀ := by
      have h := three_mul_choose_three n
      have hsub : n - 2 = m ^ 2 := by dsimp [n]; omega
      rw [hsub] at h
      exact h
    have hN₀_q : (N₀ : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hN₀_pos
    rw [div_eq_iff hN₀_q]
    exact_mod_cast hid
  intro X hX1
  have hcodeg_eq_card : H_all.codegWeight H_all.edges X =
      (((triangleHypergraph n).filter (fun e => X ⊆ e)).card : ℚ) := by
    unfold WeightedHypergraph.codegWeight
    have hfilt : H_all.edges = triangleHypergraph n :=
      Finset.filter_true_of_mem (fun e _ => Finset.subset_univ e)
    have hwt : H_all.wt = fun _ => (1 : ℚ) := rfl
    rw [hfilt, hwt, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcodeg_eq_card, hM_eq]
  have hrhs_rw : (n.choose 3 : ℚ) * 3 * p ^ (X.card - 1) / (N₀ : ℚ) =
      (m : ℚ) ^ 2 * p ^ (X.card - 1) := by
    calc (n.choose 3 : ℚ) * 3 * p ^ (X.card - 1) / (N₀ : ℚ)
        = ((3 : ℚ) * (n.choose 3 : ℚ) / (N₀ : ℚ)) * p ^ (X.card - 1) := by ring
      _ = (m : ℚ) ^ 2 * p ^ (X.card - 1) := by rw [h_abs]
  rw [hrhs_rw]
  by_cases hX4 : 4 ≤ X.card
  · -- `|X| ≥ 4`: no 3-element hyperedge can contain `X`, so count is `0`!
    have hzero : ((triangleHypergraph n).filter (fun e => X ⊆ e)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hXe
      have he3 := (triangleHypergraph_uniform n e he).2
      have := Finset.card_le_card hXe
      omega
    rw [hzero]
    simp only [Nat.cast_zero]
    positivity
  · -- `X.card ∈ {1, 2, 3}`!
    have hX_cases : X.card = 1 ∨ X.card = 2 ∨ X.card = 3 := by omega
    rcases hX_cases with h1 | h2 | h3
    · -- `X.card = 1`: `X = {i₀}`, edge `pair₀` has size 2, so any `t ∈ powersetCard 3` with
      -- `i₀ ∈ triangleEdgeIndices n t` satisfies `pair₀ ⊆ t`, giving at most `(Finset.univ \ pair₀).card = n - 2 = m^2`!
      rw [h1]
      simp only [Nat.sub_self, pow_zero, mul_one]
      obtain ⟨i₀, rfl⟩ := Finset.card_eq_one.mp h1
      let pair₀ := ((edgeIndexEquiv n) i₀).1
      have hpair₀_2 : pair₀.card = 2 :=
        (Finset.mem_powersetCard.mp ((edgeIndexEquiv n) i₀).2).2
      -- Inject `(triangleHypergraph n).filter ({i₀} ⊆ ·)` into `Finset.univ \ pair₀`!
      -- Every `e` in the filter is `triangleEdgeIndices n t` for a unique `t ∈ powersetCard 3`
      -- containing `pair₀`, hence `t \ pair₀` is a singleton `{z}` with `z ∈ univ \ pair₀`!
      have hcard_le : ((triangleHypergraph n).filter (fun e => {i₀} ⊆ e)).card ≤ m ^ 2 := by
        have hpre : ((triangleHypergraph n).filter (fun e => {i₀} ⊆ e)).card ≤
            (((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun t => pair₀ ⊆ t)).card := by
          unfold triangleHypergraph
          have hsub : (((Finset.univ : Finset (Fin n)).powersetCard 3).image (triangleEdgeIndices n)).filter
              (fun e => {i₀} ⊆ e) ⊆
              (((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun t => pair₀ ⊆ t)).image
                (triangleEdgeIndices n) := by
            intro e he
            rcases Finset.mem_filter.mp he with ⟨he_img, hi₀⟩
            rcases Finset.mem_image.mp he_img with ⟨t, ht, rfl⟩
            have hi₀_in : i₀ ∈ triangleEdgeIndices n t := hi₀ (Finset.mem_singleton_self i₀)
            unfold triangleEdgeIndices at hi₀_in
            rcases Finset.mem_image.mp hi₀_in with ⟨⟨p', hp'⟩, _, heq_i⟩
            have hp'_eq : p' = pair₀ := by
              have h := congrArg (edgeIndexEquiv n) heq_i
              simpa [pair₀] using congrArg Subtype.val h
            subst hp'_eq
            exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ht, (Finset.mem_powersetCard.mp hp').1⟩)
          calc _ ≤ _ := Finset.card_le_card hsub
            _ ≤ _ := Finset.card_image_le
        -- Map `u ∈ Finset.univ \ pair₀` to `insert u pair₀` (surjective onto `{t : card=3 ∧ pair₀ ⊆ t}`)!
        have hsurj : (((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun t => pair₀ ⊆ t)) ⊆
            ((Finset.univ : Finset (Fin n)) \ pair₀).image (fun u => insert u pair₀) := by
          intro t ht
          rcases Finset.mem_filter.mp ht with ⟨ht3, hsub0⟩
          have htc : t.card = 3 := (Finset.mem_powersetCard.mp ht3).2
          have hsdiff_c : (t \ pair₀).card = 1 := by
            have := Finset.card_sdiff_add_card_eq_card hsub0
            omega
          obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hsdiff_c
          have hu_in_sdiff : u ∈ t \ pair₀ := hu_eq ▸ Finset.mem_singleton_self u
          have hu_not : u ∉ pair₀ := (Finset.mem_sdiff.mp hu_in_sdiff).2
          refine Finset.mem_image.mpr ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu_not⟩, ?_⟩
          ext z
          simp only [Finset.mem_insert]
          constructor
          · rintro (rfl | hzp)
            · exact (Finset.mem_sdiff.mp hu_in_sdiff).1
            · exact hsub0 hzp
          · intro hzt
            by_cases hzp : z ∈ pair₀
            · exact Or.inr hzp
            · left
              have : z ∈ t \ pair₀ := Finset.mem_sdiff.mpr ⟨hzt, hzp⟩
              rw [hu_eq] at this
              exact Finset.mem_singleton.mp this
        have hrem_card : ((Finset.univ : Finset (Fin n)) \ pair₀).card = m ^ 2 := by
          have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ pair₀)
          simp only [Finset.card_univ, Fintype.card_fin, hpair₀_2] at h
          dsimp [n] at h
          omega
        calc ((triangleHypergraph n).filter (fun e => {i₀} ⊆ e)).card
            ≤ (((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun t => pair₀ ⊆ t)).card := hpre
          _ ≤ (((Finset.univ : Finset (Fin n)) \ pair₀).image (fun u => insert u pair₀)).card :=
              Finset.card_le_card hsurj
          _ ≤ ((Finset.univ : Finset (Fin n)) \ pair₀).card := Finset.card_image_le
          _ = m ^ 2 := hrem_card
      exact_mod_cast hcard_le
    · -- `X.card = 2`: two distinct edges `pair₁ ≠ pair₂` have `(pair₁ ∪ pair₂).card ≥ 3`,
      -- so AT MOST ONE 3-element set `t` can contain `pair₁ ∪ pair₂`!
      rw [h2]
      obtain ⟨i₁, i₂, hi₁₂, rfl⟩ := Finset.card_eq_two.mp h2
      let pair₁ := ((edgeIndexEquiv n) i₁).1
      let pair₂ := ((edgeIndexEquiv n) i₂).1
      have hp1_c : pair₁.card = 2 := (Finset.mem_powersetCard.mp ((edgeIndexEquiv n) i₁).2).2
      have hp2_c : pair₂.card = 2 := (Finset.mem_powersetCard.mp ((edgeIndexEquiv n) i₂).2).2
      have hp_ne : pair₁ ≠ pair₂ := fun h =>
        hi₁₂ ((edgeIndexEquiv n).injective (Subtype.ext h))
      -- Therefore `pair₁ ∪ pair₂` has `≥ 3` elements!
      have hunion_ge3 : 3 ≤ (pair₁ ∪ pair₂).card := by
        by_contra! hlt3
        have hle2 : (pair₁ ∪ pair₂).card ≤ 2 := by omega
        have heq1 : pair₁ = pair₁ ∪ pair₂ :=
          Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
        have heq2 : pair₂ = pair₁ ∪ pair₂ :=
          Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
        exact hp_ne (heq1.trans heq2.symm)
      have hcard_le1 : ((triangleHypergraph n).filter (fun e => {i₁, i₂} ⊆ e)).card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_
        intro e_a hea e_b heb
        rcases Finset.mem_filter.mp hea with ⟨hea_H, hXa⟩
        rcases Finset.mem_filter.mp heb with ⟨heb_H, hXb⟩
        unfold triangleHypergraph at hea_H heb_H
        rcases Finset.mem_image.mp hea_H with ⟨ta, hta, rfl⟩
        rcases Finset.mem_image.mp heb_H with ⟨tb, htb, rfl⟩
        congr 1
        have hsub_u : ∀ {t : Finset (Fin n)}, {i₁, i₂} ⊆ triangleEdgeIndices n t → pair₁ ∪ pair₂ ⊆ t := by
          intro t hXt
          have h1_in : i₁ ∈ triangleEdgeIndices n t := hXt (by simp)
          have h2_in : i₂ ∈ triangleEdgeIndices n t := hXt (by simp)
          unfold triangleEdgeIndices at h1_in h2_in
          rcases Finset.mem_image.mp h1_in with ⟨⟨q₁, hq₁⟩, _, heq1⟩
          rcases Finset.mem_image.mp h2_in with ⟨⟨q₂, hq₂⟩, _, heq2⟩
          have hq₁_eq : q₁ = pair₁ := by
            simpa [pair₁] using congrArg Subtype.val (congrArg (edgeIndexEquiv n) heq1)
          have hq₂_eq : q₂ = pair₂ := by
            simpa [pair₂] using congrArg Subtype.val (congrArg (edgeIndexEquiv n) heq2)
          subst hq₁_eq hq₂_eq
          exact Finset.union_subset (Finset.mem_powersetCard.mp hq₁).1 (Finset.mem_powersetCard.mp hq₂).1
        have hua := hsub_u hXa
        have hub := hsub_u hXb
        have hta3 : ta.card = 3 := (Finset.mem_powersetCard.mp hta).2
        have htb3 : tb.card = 3 := (Finset.mem_powersetCard.mp htb).2
        have eq_a : pair₁ ∪ pair₂ = ta := Finset.eq_of_subset_of_card_le hua (by omega)
        have eq_b : pair₁ ∪ pair₂ = tb := Finset.eq_of_subset_of_card_le hub (by omega)
        exact eq_a.symm.trans eq_b
      have hm_q : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
      have hm_ne : (m : ℚ) ≠ 0 := by positivity
      have hrhs : (m : ℚ) ^ 2 * p ^ (2 - 1) = (m : ℚ) := by
        dsimp [p]; field_simp [hm_ne]
      rw [hrhs]
      have hc_q : (((triangleHypergraph n).filter (fun e => {i₁, i₂} ⊆ e)).card : ℚ) ≤ 1 := by
        exact_mod_cast hcard_le1
      linarith
    · -- `X.card = 3`: every `e ∈ triangleHypergraph n` with `X ⊆ e` has `e.card ≤ 3 = X.card`, so `e = X` (`≤ 1`)!
      rw [h3]
      have hcard_le1 : ((triangleHypergraph n).filter (fun e => X ⊆ e)).card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_
        intro ea hea eb heb
        rcases Finset.mem_filter.mp hea with ⟨hea_H, hXa⟩
        rcases Finset.mem_filter.mp heb with ⟨heb_H, hXb⟩
        have hea_eq : X = ea := Finset.eq_of_subset_of_card_le hXa (by
          have := (triangleHypergraph_uniform n ea hea_H).2; omega)
        have heb_eq : X = eb := Finset.eq_of_subset_of_card_le hXb (by
          have := (triangleHypergraph_uniform n eb heb_H).2; omega)
        exact hea_eq.symm.trans heb_eq
      have hm_ne : (m : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (by omega : 0 < m)
      have hrhs : (m : ℚ) ^ 2 * p ^ (3 - 1) = 1 := by
        dsimp [p]; field_simp [hm_ne]
      rw [hrhs]
      exact_mod_cast hcard_le1

/-! ## 3. Ramsey Supersaturation via Exact Binomial Absorption -/

lemma choose_absorption {n R k : ℕ} (hR : k ≤ R) (_hn : R ≤ n) :
    R.choose k * n.choose R = n.choose k * (n - k).choose (R - k) := by
  rw [mul_comm, Nat.choose_mul hR]

lemma card_powersetCard_superset {n R : ℕ} {A : Finset (Fin n)} (hAR : A.card ≤ R) :
    (((Finset.univ : Finset (Fin n)).powersetCard R).filter (fun S => A ⊆ S)).card =
      (n - A.card).choose (R - A.card) := by
  let rest : Finset (Fin n) := Finset.univ \ A
  have hrest_card : rest.card = n - A.card := by
    have h : rest.card + A.card = (Finset.univ : Finset (Fin n)).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    simp at h; omega
  have heq : (((Finset.univ : Finset (Fin n)).powersetCard R).filter (fun S => A ⊆ S)) =
      (rest.powersetCard (R - A.card)).image (fun T => A ∪ T) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨hScard, hAS⟩
      refine ⟨S \ A, ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ S) (Finset.Subset.refl A), ?_⟩,
        Finset.union_sdiff_of_subset hAS⟩
      have h := Finset.card_sdiff_add_card_eq_card hAS
      omega
    · rintro ⟨T, ⟨hTrest, hTcard⟩, rfl⟩
      have hdisj : Disjoint A T :=
        Disjoint.mono_right hTrest Finset.sdiff_disjoint.symm
      refine ⟨?_, Finset.subset_union_left⟩
      rw [Finset.card_union_of_disjoint hdisj, hTcard]
      omega
  rw [heq, Finset.card_image_of_injOn]
  · rw [Finset.card_powersetCard, hrest_card]
  · intro T₁ hT₁ T₂ hT₂ hu
    dsimp only at hu
    have hd₁ : Disjoint A T₁ :=
      Disjoint.mono_right (Finset.mem_powersetCard.mp hT₁).1 Finset.sdiff_disjoint.symm
    have hd₂ : Disjoint A T₂ :=
      Disjoint.mono_right (Finset.mem_powersetCard.mp hT₂).1 Finset.sdiff_disjoint.symm
    have hs₁ : (A ∪ T₁) \ A = T₁ := Finset.union_sdiff_cancel_left hd₁
    have hs₂ : (A ∪ T₂) \ A = T₂ := Finset.union_sdiff_cancel_left hd₂
    rw [← hs₁, ← hs₂, hu]

private lemma card_biUnion_le_sum {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := by
  refine Finset.induction_on s (by simp) ?_
  intro x T hxT ih
  rw [Finset.biUnion_insert, Finset.sum_insert hxT]
  calc (f x ∪ T.biUnion f).card
      ≤ (f x).card + (T.biUnion f).card := Finset.card_union_le _ _
    _ ≤ (f x).card + ∑ a ∈ T, (f a).card := Nat.add_le_add_left ih _

theorem ramsey_supersaturation {r n : ℕ} (hr : 1 ≤ r)
    (hn : ramseyBound r ≤ n)
    (C : Fin r → Finset (Fin (n.choose 2)))
    (htri_small :
      (∑ c : Fin r, (((triangleHypergraph n).filter (fun e => e ⊆ C c)).card : ℚ)) ≤
        (n.choose 3 : ℚ) / (2 * ((ramseyBound r).choose 3 : ℚ))) :
    let U_uncov := (Finset.univ : Finset (Fin (n.choose 2))) \ Finset.univ.biUnion C
    (n.choose 2 : ℚ) / (2 * ((ramseyBound r).choose 2 : ℚ)) ≤ (U_uncov.card : ℚ) := by
  dsimp only
  let R := ramseyBound r
  have hR3 : 3 ≤ R := ramseyBound_ge_three hr
  set U_uncov := (Finset.univ : Finset (Fin (n.choose 2))) \ Finset.univ.biUnion C
  let allR := (Finset.univ : Finset (Fin n)).powersetCard R
  let badEdgeSets := U_uncov.biUnion (fun i => allR.filter (fun S => ((edgeIndexEquiv n) i).1 ⊆ S))
  let badTriSets := (Finset.univ : Finset (Fin r)).biUnion (fun c =>
    (((Finset.univ : Finset (Fin n)).powersetCard 3).filter
      (fun t => triangleEdgeIndices n t ⊆ C c)).biUnion
      (fun t => allR.filter (fun S => t ⊆ S)))
  -- Define a global color assignment `edgeColor : Fin (n.choose 2) → Fin r` picking a covering color when one exists!
  let c0 : Fin r := ⟨0, by omega⟩
  let edgeColor : Fin (n.choose 2) → Fin r := fun idx =>
    if hex : ∃ c : Fin r, idx ∈ C c then Classical.choose hex else c0
  have hedgeColor_spec : ∀ idx : Fin (n.choose 2), idx ∉ U_uncov → idx ∈ C (edgeColor idx) := by
    intro idx hnotU
    have hex : ∃ c : Fin r, idx ∈ C c := by
      by_contra hnone
      apply hnotU
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ idx, ?_⟩
      rw [Finset.mem_biUnion]
      rintro ⟨c, _, hc⟩
      exact hnone ⟨c, hc⟩
    simp only [edgeColor, hex, ↓reduceDIte]
    exact Classical.choose_spec hex
  have hcover : allR ⊆ badEdgeSets ∪ badTriSets := by
    intro S hS
    by_cases hunc : ∃ i ∈ U_uncov, ((edgeIndexEquiv n) i).1 ⊆ S
    · obtain ⟨i, hiU, hiS⟩ := hunc
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hiU, Finset.mem_filter.mpr ⟨hS, hiS⟩⟩)
    · apply Finset.mem_union_right
      have hS_card : Fintype.card S = R := by
        simpa using (Finset.mem_powersetCard.mp hS).2
      let emb : Fin R ≃ S := (Fintype.equivFinOfCardEq hS_card).symm
      let pairIdx : (u v : Fin R) → u ≠ v → Fin (n.choose 2) := fun u v huv =>
        have hne : (emb u).1 ≠ (emb v).1 := fun h => huv (emb.injective (Subtype.ext h))
        (edgeIndexEquiv n).symm ⟨{(emb u).1, (emb v).1}, by
          rw [completeEdges, Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, Finset.card_pair hne⟩⟩
      have hpairIdx_symm : ∀ (u v : Fin R) (huv : u ≠ v),
          pairIdx u v huv = pairIdx v u huv.symm := by
        intro u v huv
        apply (edgeIndexEquiv n).injective
        ext z
        simp [pairIdx, or_comm]
      have hpairIdx_in_C : ∀ (u v : Fin R) (huv : u ≠ v),
          pairIdx u v huv ∈ C (edgeColor (pairIdx u v huv)) := by
        intro u v huv
        apply hedgeColor_spec
        intro hmemU
        apply hunc ⟨pairIdx u v huv, hmemU, ?_⟩
        have hval : ((edgeIndexEquiv n) (pairIdx u v huv)).1 = {(emb u).1, (emb v).1} := by
          simp [pairIdx]
        rw [hval]
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hzv
        · exact (emb u).2
        · rw [Finset.mem_singleton.mp hzv]; exact (emb v).2
      let col : Sym2 (Fin R) → Fin r :=
        Sym2.lift ⟨fun u v =>
          if huv : u = v then c0
          else edgeColor (pairIdx u v huv), by
            intro u v
            by_cases huv : u = v
            · subst huv; simp
            · have hvu : v ≠ u := Ne.symm huv
              dsimp only
              rw [dif_neg huv, dif_neg hvu, hpairIdx_symm u v huv]⟩
      obtain ⟨u, v, w, huv_adj, hvw_adj, huw_adj, h1, h2⟩ :=
        completeGraph_forcesMonoTriangle r hr col
      have huv : u ≠ v := huv_adj
      have hvw : v ≠ w := hvw_adj
      have huw : u ≠ w := huw_adj
      have hcol_uv : col s(u, v) = edgeColor (pairIdx u v huv) := by simp [col, huv]
      have hcol_vw : col s(v, w) = edgeColor (pairIdx v w hvw) := by simp [col, hvw]
      have hcol_uw : col s(u, w) = edgeColor (pairIdx u w huw) := by simp [col, huw]
      let c_star : Fin r := col s(u, v)
      have hc_uv : edgeColor (pairIdx u v huv) = c_star := hcol_uv.symm
      have hc_vw : edgeColor (pairIdx v w hvw) = c_star := hcol_vw.symm.trans h1.symm
      have hc_uw : edgeColor (pairIdx u w huw) = c_star := hcol_uw.symm.trans (h1.trans h2).symm
      -- Build the 3-element subset `t = {(emb u).1, (emb v).1, (emb w).1} ⊆ S`!
      let eu := (emb u).1
      let ev := (emb v).1
      let ew := (emb w).1
      have heu_ev : eu ≠ ev := fun h => huv (emb.injective (Subtype.ext h))
      have hev_ew : ev ≠ ew := fun h => hvw (emb.injective (Subtype.ext h))
      have heu_ew : eu ≠ ew := fun h => huw (emb.injective (Subtype.ext h))
      let t : Finset (Fin n) := {eu, ev, ew}
      have ht_card : t.card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simpa using hev_ew
        · simp [heu_ev, heu_ew]
      have ht_sub_S : t ⊆ S := by
        intro z hz
        simp only [t, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact (emb u).2
        · exact (emb v).2
        · exact (emb w).2
      have ht_pow3 : t ∈ (Finset.univ : Finset (Fin n)).powersetCard 3 :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ t, ht_card⟩
      have ht_in_C : triangleEdgeIndices n t ⊆ C c_star := by
        intro idx hidx
        unfold triangleEdgeIndices at hidx
        rcases Finset.mem_image.mp hidx with ⟨⟨p, hp⟩, _, hidx_eq⟩
        have hp_val : ((edgeIndexEquiv n) idx).1 = p := by
          rw [← hidx_eq]; simp
        rcases Finset.mem_powersetCard.mp hp with ⟨hp_sub, hp_c⟩
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hp_c
        have hx_t : x ∈ t := hp_sub (by simp)
        have hy_t : y ∈ t := hp_sub (by simp)
        simp only [t, Finset.mem_insert, Finset.mem_singleton] at hx_t hy_t
        have hp_cases : ({x, y} : Finset (Fin n)) = {eu, ev} ∨
            ({x, y} : Finset (Fin n)) = {ev, ew} ∨ ({x, y} : Finset (Fin n)) = {eu, ew} := by
          rcases hx_t with rfl | rfl | rfl <;> rcases hy_t with rfl | rfl | rfl
          · exact absurd rfl hxy
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl (Finset.pair_comm ev eu)
          · exact absurd rfl hxy
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Finset.pair_comm ew eu))
          · exact Or.inr (Or.inl (Finset.pair_comm ew ev))
          · exact absurd rfl hxy
        rcases hp_cases with heq | heq | heq
        · have hid_eq : idx = pairIdx u v huv := by
            apply (edgeIndexEquiv n).injective
            apply Subtype.ext
            rw [hp_val, heq]; simp [pairIdx, eu, ev]
          rw [hid_eq, ← hc_uv]; exact hpairIdx_in_C u v huv
        · have hid_eq : idx = pairIdx v w hvw := by
            apply (edgeIndexEquiv n).injective
            apply Subtype.ext
            rw [hp_val, heq]; simp [pairIdx, ev, ew]
          rw [hid_eq, ← hc_vw]; exact hpairIdx_in_C v w hvw
        · have hid_eq : idx = pairIdx u w huw := by
            apply (edgeIndexEquiv n).injective
            apply Subtype.ext
            rw [hp_val, heq]; simp [pairIdx, eu, ew]
          rw [hid_eq, ← hc_uw]; exact hpairIdx_in_C u w huw
      exact Finset.mem_biUnion.mpr ⟨c_star, Finset.mem_univ c_star,
        Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr ⟨ht_pow3, ht_in_C⟩,
          Finset.mem_filter.mpr ⟨hS, ht_sub_S⟩⟩⟩
  -- Now count sizes of `allR`, `badEdgeSets`, and `badTriSets`!
  have hallR_card : allR.card = n.choose R := by
    simp [allR, Finset.card_powersetCard]
  have hbadE_card : badEdgeSets.card ≤ U_uncov.card * (n - 2).choose (R - 2) := by
    calc badEdgeSets.card
        ≤ ∑ i ∈ U_uncov, (allR.filter (fun S => ((edgeIndexEquiv n) i).1 ⊆ S)).card :=
          card_biUnion_le_sum _ _
      _ = ∑ _i ∈ U_uncov, (n - 2).choose (R - 2) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hc2 : ((edgeIndexEquiv n) i).1.card = 2 :=
            (Finset.mem_powersetCard.mp ((edgeIndexEquiv n) i).2).2
          have h := card_powersetCard_superset (R := R) (A := ((edgeIndexEquiv n) i).1) (by omega)
          simpa [allR, hc2] using h
      _ = U_uncov.card * (n - 2).choose (R - 2) := by simp
  have htri_img_card : ∀ c : Fin r,
      (((Finset.univ : Finset (Fin n)).powersetCard 3).filter
        (fun t => triangleEdgeIndices n t ⊆ C c)).card =
        ((triangleHypergraph n).filter (fun e => e ⊆ C c)).card := by
    intro c
    unfold triangleHypergraph
    rw [Finset.filter_image, Finset.card_image_of_injOn]
    exact (triangleEdgeIndices_injective n).mono (Finset.filter_subset _ _)
  have hbadT_card : badTriSets.card ≤
      (∑ c : Fin r, ((triangleHypergraph n).filter (fun e => e ⊆ C c)).card) *
        (n - 3).choose (R - 3) := by
    calc badTriSets.card
        ≤ ∑ c : Fin r,
            ((((Finset.univ : Finset (Fin n)).powersetCard 3).filter
              (fun t => triangleEdgeIndices n t ⊆ C c)).biUnion
              (fun t => allR.filter (fun S => t ⊆ S))).card :=
          card_biUnion_le_sum _ _
      _ ≤ ∑ c : Fin r,
            ∑ t ∈ ((Finset.univ : Finset (Fin n)).powersetCard 3).filter
              (fun t => triangleEdgeIndices n t ⊆ C c),
              (allR.filter (fun S => t ⊆ S)).card := by
          refine Finset.sum_le_sum (fun c _ => card_biUnion_le_sum _ _)
      _ = ∑ c : Fin r,
            ((triangleHypergraph n).filter (fun e => e ⊆ C c)).card * (n - 3).choose (R - 3) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          have hinner : ∀ t ∈ ((Finset.univ : Finset (Fin n)).powersetCard 3).filter
              (fun t => triangleEdgeIndices n t ⊆ C c),
              (allR.filter (fun S => t ⊆ S)).card = (n - 3).choose (R - 3) := by
            intro t ht
            have hc3 : t.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ht).1).2
            have h := card_powersetCard_superset (R := R) (A := t) (by omega)
            simpa [allR, hc3] using h
          rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, htri_img_card c]
      _ = (∑ c : Fin r, ((triangleHypergraph n).filter (fun e => e ⊆ C c)).card) *
            (n - 3).choose (R - 3) := (Finset.sum_mul _ _ _).symm
  have hnat_ineq : n.choose R ≤
      U_uncov.card * (n - 2).choose (R - 2) +
        (∑ c : Fin r, ((triangleHypergraph n).filter (fun e => e ⊆ C c)).card) *
          (n - 3).choose (R - 3) := by
    calc n.choose R = allR.card := hallR_card.symm
      _ ≤ (badEdgeSets ∪ badTriSets).card := Finset.card_le_card hcover
      _ ≤ badEdgeSets.card + badTriSets.card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add hbadE_card hbadT_card
  -- Convert `hnat_ineq` to `ℚ` using the two absorption identities!
  have habs2 : (R.choose 2 : ℚ) * (n.choose R : ℚ) =
      (n.choose 2 : ℚ) * ((n - 2).choose (R - 2) : ℚ) := by
    exact_mod_cast choose_absorption (by omega) hn
  have habs3 : (R.choose 3 : ℚ) * (n.choose R : ℚ) =
      (n.choose 3 : ℚ) * ((n - 3).choose (R - 3) : ℚ) := by
    exact_mod_cast choose_absorption hR3 hn
  have hnR_pos : (0 : ℚ) < (n.choose R : ℚ) := by exact_mod_cast Nat.choose_pos hn
  have hn2_pos : (0 : ℚ) < (n.choose 2 : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hn3_pos : (0 : ℚ) < (n.choose 3 : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hR2_pos : (0 : ℚ) < (R.choose 2 : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hR3_pos : (0 : ℚ) < (R.choose 3 : ℚ) := by exact_mod_cast Nat.choose_pos hR3
  set T_sum : ℚ := ∑ c : Fin r, (((triangleHypergraph n).filter (fun e => e ⊆ C c)).card : ℚ)
  have hq_ineq : (n.choose R : ℚ) ≤
      (U_uncov.card : ℚ) * ((n - 2).choose (R - 2) : ℚ) +
        T_sum * ((n - 3).choose (R - 3) : ℚ) := by
    have hcast : (n.choose R : ℚ) ≤
        ((U_uncov.card * (n - 2).choose (R - 2) +
          (∑ c : Fin r, ((triangleHypergraph n).filter (fun e => e ⊆ C c)).card) *
            (n - 3).choose (R - 3) : ℕ) : ℚ) := by
      exact_mod_cast hnat_ineq
    simpa [T_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_sum] using hcast
  -- Multiply both sides by `(n.choose 2 : ℚ) * (n.choose 3 : ℚ)`!
  have hmul := mul_le_mul_of_nonneg_left hq_ineq (by positivity : (0 : ℚ) ≤ (n.choose 2 : ℚ) * (n.choose 3 : ℚ))
  have hrw1 : (n.choose 2 : ℚ) * (n.choose 3 : ℚ) * ((U_uncov.card : ℚ) * ((n - 2).choose (R - 2) : ℚ)) =
      (U_uncov.card : ℚ) * (R.choose 2 : ℚ) * (n.choose 3 : ℚ) * (n.choose R : ℚ) := by
    calc (n.choose 2 : ℚ) * (n.choose 3 : ℚ) * ((U_uncov.card : ℚ) * ((n - 2).choose (R - 2) : ℚ))
        = (U_uncov.card : ℚ) * (n.choose 3 : ℚ) * ((n.choose 2 : ℚ) * ((n - 2).choose (R - 2) : ℚ)) := by ring
      _ = (U_uncov.card : ℚ) * (n.choose 3 : ℚ) * ((R.choose 2 : ℚ) * (n.choose R : ℚ)) := by rw [← habs2]
      _ = (U_uncov.card : ℚ) * (R.choose 2 : ℚ) * (n.choose 3 : ℚ) * (n.choose R : ℚ) := by ring
  have hrw2 : (n.choose 2 : ℚ) * (n.choose 3 : ℚ) * (T_sum * ((n - 3).choose (R - 3) : ℚ)) =
      T_sum * (R.choose 3 : ℚ) * (n.choose 2 : ℚ) * (n.choose R : ℚ) := by
    calc (n.choose 2 : ℚ) * (n.choose 3 : ℚ) * (T_sum * ((n - 3).choose (R - 3) : ℚ))
        = T_sum * (n.choose 2 : ℚ) * ((n.choose 3 : ℚ) * ((n - 3).choose (R - 3) : ℚ)) := by ring
      _ = T_sum * (n.choose 2 : ℚ) * ((R.choose 3 : ℚ) * (n.choose R : ℚ)) := by rw [← habs3]
      _ = T_sum * (R.choose 3 : ℚ) * (n.choose 2 : ℚ) * (n.choose R : ℚ) := by ring
  rw [mul_add, hrw1, hrw2] at hmul
  -- Cancel `(n.choose R : ℚ) > 0`!
  have hcancel_nR : (n.choose 2 : ℚ) * (n.choose 3 : ℚ) ≤
      (U_uncov.card : ℚ) * (R.choose 2 : ℚ) * (n.choose 3 : ℚ) +
        T_sum * (R.choose 3 : ℚ) * (n.choose 2 : ℚ) := by
    have hmul' : ((n.choose 2 : ℚ) * (n.choose 3 : ℚ)) * (n.choose R : ℚ) ≤
        ((U_uncov.card : ℚ) * (R.choose 2 : ℚ) * (n.choose 3 : ℚ) +
          T_sum * (R.choose 3 : ℚ) * (n.choose 2 : ℚ)) * (n.choose R : ℚ) := by linarith
    exact le_of_mul_le_mul_right hmul' hnR_pos
  -- From `htri_small : T_sum ≤ n.choose 3 / (2 * R.choose 3)`, we have `T_sum * R.choose 3 ≤ n.choose 3 / 2`!
  have hT_half : T_sum * (R.choose 3 : ℚ) ≤ (n.choose 3 : ℚ) / 2 := by
    have h1 : T_sum ≤ (n.choose 3 : ℚ) / (2 * (R.choose 3 : ℚ)) := htri_small
    rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 * (R.choose 3 : ℚ))] at h1
    linarith
  have hT_term : T_sum * (R.choose 3 : ℚ) * (n.choose 2 : ℚ) ≤
      (n.choose 2 : ℚ) * (n.choose 3 : ℚ) / 2 := by
    have h := mul_le_mul_of_nonneg_right hT_half (le_of_lt hn2_pos)
    linarith
  have hU_term : (n.choose 2 : ℚ) * (n.choose 3 : ℚ) / 2 ≤
      (U_uncov.card : ℚ) * (R.choose 2 : ℚ) * (n.choose 3 : ℚ) := by linarith
  have hcancel_n3 : (n.choose 2 : ℚ) ≤ (U_uncov.card : ℚ) * (2 * (R.choose 2 : ℚ)) := by
    have hmul2 : ((n.choose 2 : ℚ)) * (n.choose 3 : ℚ) ≤
        ((U_uncov.card : ℚ) * (2 * (R.choose 2 : ℚ))) * (n.choose 3 : ℚ) := by linarith
    exact le_of_mul_le_mul_right hmul2 hn3_pos
  rwa [div_le_iff₀ (by positivity : (0 : ℚ) < 2 * (R.choose 2 : ℚ))]

end CompleteHypergraph

/-! ## 4. Locally Sparse Triangle-Ramsey Existence via Finite Grid Alteration -/

section AlterationConstruction

open Erdos638.GridCounting

/-- Convert a set of edge indices `E ⊆ Fin (n.choose 2)` into a `SimpleGraph (Fin n)`. -/
noncomputable def graphOfEdgeIndices (n : ℕ) (E : Finset (Fin (n.choose 2))) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ i ∈ E, ((edgeIndexEquiv n) i).1 = {u, v}
  symm := by
    constructor
    intro u v h
    rcases h with ⟨huv, i, hi, heq⟩
    exact ⟨huv.symm, i, hi, heq.trans (Finset.pair_comm u v)⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

lemma graphOfEdgeIndices_adj_iff {n : ℕ} {E : Finset (Fin (n.choose 2))} {u v : Fin n}
    (huv : u ≠ v) :
    (graphOfEdgeIndices n E).Adj u v ↔
      (edgeIndexEquiv n).symm ⟨{u, v}, by
        rw [completeEdges, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, Finset.card_pair huv⟩⟩ ∈ E := by
  have hpair_comp : ({u, v} : Finset (Fin n)) ∈ completeEdges n := by
    rw [completeEdges, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, Finset.card_pair huv⟩
  unfold graphOfEdgeIndices
  dsimp only
  constructor
  · rintro ⟨_, i, hiE, heq⟩
    have hid : (edgeIndexEquiv n).symm ⟨{u, v}, hpair_comp⟩ = i := by
      apply (edgeIndexEquiv n).injective
      apply Subtype.ext
      simpa using heq.symm
    rwa [hid]
  · intro hmem
    exact ⟨huv, (edgeIndexEquiv n).symm ⟨{u, v}, hpair_comp⟩, hmem, by simp⟩

/-- Set of edge indices inside a vertex subset `S : Finset (Fin n)`. -/
noncomputable def indicesInside (n : ℕ) (S : Finset (Fin n)) : Finset (Fin (n.choose 2)) :=
  Finset.univ.filter (fun i => ((edgeIndexEquiv n) i).1 ⊆ S)

lemma card_indicesInside {n : ℕ} (S : Finset (Fin n)) :
    (indicesInside n S).card = S.card.choose 2 := by
  have heq : (indicesInside n S).image (fun i => ((edgeIndexEquiv n) i).1) = S.powersetCard 2 := by
    ext p
    simp only [indicesInside, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨i, hpS, rfl⟩
      exact ⟨hpS, (Finset.mem_powersetCard.mp ((edgeIndexEquiv n) i).2).2⟩
    · rintro ⟨hpS, hpc⟩
      have hp_comp : p ∈ completeEdges n := by
        rw [completeEdges, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hpc⟩
      exact ⟨(edgeIndexEquiv n).symm ⟨p, hp_comp⟩, by simpa using hpS, by simp⟩
  rw [← Finset.card_powersetCard 2 S, ← heq, Finset.card_image_of_injective]
  intro i j hij
  exact (edgeIndexEquiv n).injective (Subtype.ext hij)

private noncomputable def twoSetToSym2 {n : ℕ} (p : Finset (Fin n)) (hp : p.card = 2) : Sym2 (Fin n) :=
  s(Classical.choose (Finset.card_eq_two.mp hp),
    Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp hp)))

private lemma twoSetToSym2_eq_pair {n : ℕ} {p : Finset (Fin n)} (hp : p.card = 2) :
    ∃ a b : Fin n, a ≠ b ∧ p = {a, b} ∧ twoSetToSym2 p hp = s(a, b) := by
  let a := Classical.choose (Finset.card_eq_two.mp hp)
  let h2 := Classical.choose_spec (Finset.card_eq_two.mp hp)
  let b := Classical.choose h2
  let h3 := Classical.choose_spec h2
  exact ⟨a, b, h3.1, h3.2, rfl⟩

lemma edgesInside_graphOfEdgeIndices (n : ℕ) (E : Finset (Fin (n.choose 2))) (S : Finset (Fin n)) :
    edgesInside (graphOfEdgeIndices n E) S = (E ∩ indicesInside n S).card := by
  let toSym2 : Fin (n.choose 2) → Sym2 (Fin n) := fun i =>
    twoSetToSym2 ((edgeIndexEquiv n) i).1
      (Finset.mem_powersetCard.mp ((edgeIndexEquiv n) i).2).2
  have htoSym2_spec : ∀ i : Fin (n.choose 2),
      ∃ a b : Fin n, a ≠ b ∧ ((edgeIndexEquiv n) i).1 = {a, b} ∧ toSym2 i = s(a, b) :=
    fun i => twoSetToSym2_eq_pair _
  have htoSym2_mem : ∀ i : Fin (n.choose 2), ∀ x : Fin n,
      x ∈ toSym2 i ↔ x ∈ ((edgeIndexEquiv n) i).1 := by
    intro i x
    obtain ⟨a, b, _, hp_eq, hs_eq⟩ := htoSym2_spec i
    rw [hs_eq, hp_eq]
    simp
  have htoSym2_inj : Function.Injective toSym2 := by
    intro i j hij
    apply (edgeIndexEquiv n).injective
    apply Subtype.ext
    ext x
    rw [← htoSym2_mem i x, ← htoSym2_mem j x, hij]
  let target := (graphOfEdgeIndices n E).edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)
  have htarget_eq : edgesInside (graphOfEdgeIndices n E) S = target.card := by
    unfold edgesInside
    congr 1
    ext e
    simp [target]
  rw [htarget_eq]
  have himg_eq : (E ∩ indicesInside n S).image toSym2 = target := by
    ext e
    simp only [target, Finset.mem_image, Finset.mem_inter, indicesInside, Finset.mem_filter,
      Finset.mem_univ, true_and, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨i, ⟨hiE, hiS⟩, rfl⟩
      obtain ⟨a, b, hab, hp_eq, hs_eq⟩ := htoSym2_spec i
      rw [hs_eq]
      refine ⟨⟨hab, i, hiE, hp_eq⟩, ?_⟩
      intro x hx
      rw [← hs_eq] at hx
      exact hiS ((htoSym2_mem i x).mp hx)
    · induction e using Sym2.ind with
      | _ u v =>
        rintro ⟨⟨_huv, i, hiE, hp_uv⟩, hmemS⟩
        obtain ⟨a, b, hab, hp_ab, hs_ab⟩ := htoSym2_spec i
        refine ⟨i, ⟨hiE, ?_⟩, ?_⟩
        · intro x hx
          rw [hp_uv] at hx
          rcases Finset.mem_insert.mp hx with hxu | hxv
          · rw [hxu]; exact hmemS u (Sym2.mem_mk_left u v)
          · rw [Finset.mem_singleton.mp hxv]
            exact hmemS v (Sym2.mem_mk_right u v)
        · rw [hs_ab, Sym2.eq_iff]
          have hset_eq : ({a, b} : Finset (Fin n)) = {u, v} := hp_ab.symm.trans hp_uv
          have ha_mem : a ∈ ({u, v} : Finset (Fin n)) := hset_eq ▸ by simp
          have hb_mem : b ∈ ({u, v} : Finset (Fin n)) := hset_eq ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem hb_mem
          rcases ha_mem with hau | hav <;> rcases hb_mem with hbu | hbv
          · exfalso; exact hab (hau.trans hbu.symm)
          · exact Or.inl ⟨hau, hbv⟩
          · exact Or.inr ⟨hav, hbu⟩
          · exfalso; exact hab (hav.trans hbv.symm)
  rw [← himg_eq, Finset.card_image_of_injective _ htoSym2_inj]

/-- All dense `(2|S| - 2)`-edge subsets `D ⊆ Fin (n.choose 2)` coming from vertex sets `S`
with `4 ≤ S.card ≤ B`! -/
noncomputable def denseObstructions (n B : ℕ) : Finset (Finset (Fin (n.choose 2))) :=
  ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => 4 ≤ S.card ∧ S.card ≤ B)).biUnion
    (fun S => (indicesInside n S).powersetCard (2 * S.card - 2))

/-- Altered edge set: delete ALL edges belonging to ANY `D ∈ denseObstructions n B` that is
completely present in `raw` (`D ⊆ raw`)! -/
noncomputable def purgeDenseObstructions (n B : ℕ) (raw : Finset (Fin (n.choose 2))) :
    Finset (Fin (n.choose 2)) :=
  raw \ ((denseObstructions n B).filter (fun D => D ⊆ raw)).biUnion id

/-- **Deterministic Sparsity Guarantee**:
For ANY `raw`, `G = graphOfEdgeIndices n (purgeDenseObstructions n B raw)` has
`edgesInside G S ≤ 2 * S.card - 3` for EVERY `S` with `4 ≤ S.card ≤ B`! -/
lemma purgeDenseObstructions_sparse (n B : ℕ) (raw : Finset (Fin (n.choose 2)))
    (S : Finset (Fin n)) (hS4 : 4 ≤ S.card) (hSB : S.card ≤ B) :
    edgesInside (graphOfEdgeIndices n (purgeDenseObstructions n B raw)) S ≤ 2 * S.card - 3 := by
  rw [edgesInside_graphOfEdgeIndices]
  set E := purgeDenseObstructions n B raw
  by_contra! hge
  have hle_needed : 2 * S.card - 2 ≤ (E ∩ indicesInside n S).card := by omega
  obtain ⟨D, hD_sub, hD_card⟩ := Finset.exists_subset_card_eq hle_needed
  have hD_E : D ⊆ E := hD_sub.trans Finset.inter_subset_left
  have hD_indS : D ⊆ indicesInside n S := hD_sub.trans Finset.inter_subset_right
  have hD_raw : D ⊆ raw := hD_E.trans Finset.sdiff_subset
  have hD_obs : D ∈ denseObstructions n B := by
    unfold denseObstructions
    refine Finset.mem_biUnion.mpr ⟨S, ?_, Finset.mem_powersetCard.mpr ⟨hD_indS, hD_card⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), hS4, hSB⟩
  -- Since `4 ≤ S.card`, `2 * S.card - 2 ≥ 6 ≥ 1`, so `D` has an element `x₀ ∈ D`!
  have hD_pos : 0 < D.card := by omega
  obtain ⟨x₀, hx₀D⟩ := Finset.card_pos.mp hD_pos
  have hx₀E : x₀ ∈ E := hD_E hx₀D
  have hx₀_del : x₀ ∈ ((denseObstructions n B).filter (fun D' => D' ⊆ raw)).biUnion id :=
    Finset.mem_biUnion.mpr ⟨D, Finset.mem_filter.mpr ⟨hD_obs, hD_raw⟩, hx₀D⟩
  exact (Finset.mem_sdiff.mp hx₀E).2 hx₀_del

/-- Upper bound on total number of `D ∈ denseObstructions n B`:
for each `S` (`4 ≤ S.card ≤ B`), `indicesInside n S` has size `S.card.choose 2 ≤ B ^ 2`,
so `(indicesInside n S).powersetCard (2 * S.card - 2)` has size `≤ 2 ^ (B ^ 2)`.
Even simpler: we bound `∑ D ∈ denseObstructions n B, q ^ D.card`! -/
lemma sum_denseObstructions_prob {m B A : ℕ} (hm : 1 ≤ m) (_hB : 4 ≤ B) :
    let n := m ^ 2 + 2
    let q : ℚ := (A : ℚ) / (m : ℚ)
    (∑ D ∈ denseObstructions n B, q ^ D.card) ≤
      ((B + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (B * B) * ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2 := by
  let n := m ^ 2 + 2
  let q : ℚ := (A : ℚ) / (m : ℚ)
  have hm_pos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hm_ne : (m : ℚ) ≠ 0 := ne_of_gt hm_pos
  have hn_le_3m2 : (n : ℚ) ≤ 3 * (m : ℚ) ^ 2 := by
    have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    have hm2 : (1 : ℚ) ≤ (m : ℚ) ^ 2 := by nlinarith
    have hcast : (n : ℚ) = (m : ℚ) ^ 2 + 2 := by dsimp [n]; push_cast; ring
    linarith
  unfold denseObstructions
  -- Use `Finset.sum_biUnion_le` over `S` (`4 ≤ S.card ≤ B`)!
  have hbi_le : ∀ (T : Finset (Finset (Fin n))) (g : Finset (Fin n) → Finset (Finset (Fin (n.choose 2)))),
      (∑ D ∈ T.biUnion g, q ^ D.card) ≤ ∑ S ∈ T, ∑ D ∈ g S, q ^ D.card := by
    intro T g
    refine Finset.induction_on T (by simp) ?_
    intro S₀ R hS₀R ih
    rw [Finset.biUnion_insert, Finset.sum_insert hS₀R]
    have hunion : (∑ D ∈ g S₀ ∪ R.biUnion g, q ^ D.card) ≤
        (∑ D ∈ g S₀, q ^ D.card) + ∑ D ∈ R.biUnion g, q ^ D.card := by
      have h := Finset.sum_union_inter (s₁ := g S₀) (s₂ := R.biUnion g) (f := fun D => q ^ D.card)
      have hinter : 0 ≤ ∑ D ∈ g S₀ ∩ R.biUnion g, q ^ D.card :=
        Finset.sum_nonneg (fun D _ => by positivity)
      linarith
    linarith
  calc (∑ D ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => 4 ≤ S.card ∧ S.card ≤ B)).biUnion
          (fun S => (indicesInside n S).powersetCard (2 * S.card - 2)), q ^ D.card)
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => 4 ≤ S.card ∧ S.card ≤ B),
          ∑ D ∈ (indicesInside n S).powersetCard (2 * S.card - 2), q ^ D.card := hbi_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 4 B,
          (n.choose k : ℚ) * ((2 : ℚ) ^ (B * B) * q ^ (2 * k - 2)) := by
        -- Group by `k = S.card ∈ Finset.Icc 4 B`!
        rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc 4 B) (g := Finset.card)
          (fun S hS => Finset.mem_Icc.mpr (Finset.mem_filter.mp hS).2)]
        apply Finset.sum_le_sum
        intro k hk
        rcases Finset.mem_Icc.mp hk with ⟨hk4, hkB⟩
        have hfib_eq : (((Finset.univ : Finset (Fin n)).powerset.filter
            (fun S => 4 ≤ S.card ∧ S.card ≤ B)).filter (fun S => S.card = k)) =
            (Finset.univ : Finset (Fin n)).powersetCard k := by
          ext S
          simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
            Finset.mem_powersetCard]
          exact ⟨fun h => h.2, fun h => ⟨⟨by omega, by omega⟩, h⟩⟩
        rw [hfib_eq]
        have hinner : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (∑ D ∈ (indicesInside n S).powersetCard (2 * S.card - 2), q ^ D.card) ≤
              (2 : ℚ) ^ (B * B) * q ^ (2 * k - 2) := by
          intro S hS
          have hSk : S.card = k := (Finset.mem_powersetCard.mp hS).2
          have hconst : ∀ D ∈ (indicesInside n S).powersetCard (2 * S.card - 2),
              q ^ D.card = q ^ (2 * k - 2) := by
            intro D hD
            rw [(Finset.mem_powersetCard.mp hD).2, hSk]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          -- `((indicesInside n S).powersetCard (2 * S.card - 2)).card ≤ (indicesInside n S).powerset.card = 2 ^ (k.choose 2) ≤ 2 ^ (B * B)`!
          have hsub_pow : (indicesInside n S).powersetCard (2 * S.card - 2) ⊆
              (indicesInside n S).powerset :=
            fun D hD => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hD).1
          have hle_2B : ((indicesInside n S).powersetCard (2 * S.card - 2)).card ≤ 2 ^ (B * B) := by
            have hk_ch : k.choose 2 ≤ B * B := by
              have h := two_mul_choose_two k
              have hkB2 : k * (k - 1) ≤ B * B :=
                Nat.mul_le_mul hkB ((Nat.sub_le k 1).trans hkB)
              omega
            calc ((indicesInside n S).powersetCard (2 * S.card - 2)).card
                ≤ (indicesInside n S).powerset.card := Finset.card_le_card hsub_pow
              _ = 2 ^ (indicesInside n S).card := Finset.card_powerset _
              _ = 2 ^ (k.choose 2) := by rw [card_indicesInside, hSk]
              _ ≤ 2 ^ (B * B) := Nat.pow_le_pow_right (by norm_num) hk_ch
          exact_mod_cast hle_2B
        calc (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              ∑ D ∈ (indicesInside n S).powersetCard (2 * S.card - 2), q ^ D.card)
            ≤ ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
                ((2 : ℚ) ^ (B * B) * q ^ (2 * k - 2)) := Finset.sum_le_sum hinner
          _ = (n.choose k : ℚ) * ((2 : ℚ) ^ (B * B) * q ^ (2 * k - 2)) := by
              rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul]
    _ ≤ ∑ _k ∈ Finset.Icc 4 B,
          ((2 : ℚ) ^ (B * B) * ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        rcases Finset.mem_Icc.mp hk with ⟨hk4, hkB⟩
        -- Note `n.choose k ≤ n ^ k ≤ (3 * m ^ 2) ^ k = 3 ^ k * m ^ (2 * k)`!
        -- And `q ^ (2 * k - 2) = A ^ (2 * k - 2) / m ^ (2 * k - 2) ≤ (A + 1) ^ (2 * k) / m ^ (2 * k - 2)`!
        -- Multiplying cancels `m ^ (2 * k - 2)` leaving `m ^ 2`!!
        have hch_le_pow : n.choose k ≤ n ^ k := by
          -- `(n + 1) ^ k = ∑ j ∈ range (k + 1), n ^ j * 1 ^ (k - j) * k.choose j`? No:
          -- Map `powersetCard k (Fin n)` injectively? No: `k`-subsets of `Fin n`:
          -- By induction on `n`: `(n + 1).choose k = n.choose k + n.choose (k - 1)`?
          -- Even simpler: by induction on `k` using `k * n.choose k ≤ n * n.choose (k - 1)` (from `(k) * C(n, k) = n * C(n - 1, k - 1) ≤ n * C(n, k - 1)`)!!
          have haux : ∀ j : ℕ, n.choose j ≤ n ^ j := by
            intro j
            induction j with
            | zero => simp
            | succ j ih =>
              have hstep : ∀ x : ℕ, x.choose (j + 1) ≤ x * x.choose j := by
                intro x
                induction x with
                | zero => simp
                | succ x ihx =>
                  rw [Nat.choose_succ_succ]
                  have hmono : x.choose j ≤ (x + 1).choose j :=
                    Nat.choose_le_succ x j
                  calc x.choose j + x.choose (j + 1)
                      ≤ x.choose j + x * x.choose j := Nat.add_le_add_left ihx _
                    _ = (x + 1) * x.choose j := by ring
                    _ ≤ (x + 1) * (x + 1).choose j := Nat.mul_le_mul_left _ hmono
              calc n.choose (j + 1)
                  ≤ n * n.choose j := hstep n
                _ ≤ n * n ^ j := Nat.mul_le_mul_left n ih
                _ = n ^ (j + 1) := by ring
          exact haux k
        have hch_q : (n.choose k : ℚ) ≤ (3 : ℚ) ^ k * (m : ℚ) ^ (2 * k) := by
          have h1 : (n.choose k : ℚ) ≤ (n : ℚ) ^ k := by exact_mod_cast hch_le_pow
          have h2 : (n : ℚ) ^ k ≤ (3 * (m : ℚ) ^ 2) ^ k :=
            pow_le_pow_left₀ (by positivity) hn_le_3m2 k
          have h3 : (3 * (m : ℚ) ^ 2) ^ k = (3 : ℚ) ^ k * (m : ℚ) ^ (2 * k) := by
            rw [mul_pow, ← pow_mul]
          linarith
        have hq_pow : q ^ (2 * k - 2) ≤ (((A + 1 : ℕ) : ℚ) ^ 2) ^ k / (m : ℚ) ^ (2 * k - 2) := by
          dsimp [q]
          rw [div_pow]
          apply div_le_div_of_nonneg_right _ (by positivity)
          have hA_le : (A : ℚ) ≤ ((A + 1 : ℕ) : ℚ) := by push_cast; linarith
          have hle_exp : 2 * k - 2 ≤ 2 * k := Nat.sub_le _ _
          calc (A : ℚ) ^ (2 * k - 2)
              ≤ ((A + 1 : ℕ) : ℚ) ^ (2 * k - 2) := pow_le_pow_left₀ (by positivity) hA_le _
            _ ≤ ((A + 1 : ℕ) : ℚ) ^ (2 * k) :=
                pow_le_pow_right₀ (by push_cast; linarith) hle_exp
            _ = (((A + 1 : ℕ) : ℚ) ^ 2) ^ k := by rw [← pow_mul]
        have hm_split : (m : ℚ) ^ (2 * k) = (m : ℚ) ^ 2 * (m : ℚ) ^ (2 * k - 2) := by
          rw [← pow_add]
          congr 1; omega
        have hprod_k : (n.choose k : ℚ) * q ^ (2 * k - 2) ≤
            ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2 := by
          calc (n.choose k : ℚ) * q ^ (2 * k - 2)
              ≤ ((3 : ℚ) ^ k * (m : ℚ) ^ (2 * k)) *
                  ((((A + 1 : ℕ) : ℚ) ^ 2) ^ k / (m : ℚ) ^ (2 * k - 2)) :=
                mul_le_mul hch_q hq_pow (by positivity) (by positivity)
            _ = ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ k * (m : ℚ) ^ 2 := by
                rw [hm_split, mul_pow]
                have hm_p_ne : (m : ℚ) ^ (2 * k - 2) ≠ 0 := pow_ne_zero _ hm_ne
                field_simp [hm_p_ne]
            _ ≤ ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2 := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply pow_le_pow_right₀ _ hkB
                have hA1 : (1 : ℚ) ≤ ((A + 1 : ℕ) : ℚ) := by push_cast; linarith
                nlinarith
        calc (n.choose k : ℚ) * ((2 : ℚ) ^ (B * B) * q ^ (2 * k - 2))
            = (2 : ℚ) ^ (B * B) * ((n.choose k : ℚ) * q ^ (2 * k - 2)) := by ring
          _ ≤ (2 : ℚ) ^ (B * B) * (((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2) :=
              mul_le_mul_of_nonneg_left hprod_k (by positivity)
          _ = (2 : ℚ) ^ (B * B) * ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2 := by ring
    _ = ((Finset.Icc 4 B).card : ℚ) *
          ((2 : ℚ) ^ (B * B) * ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((B + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (B * B) * ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2 := by
        have hcard_le : (Finset.Icc 4 B).card ≤ B + 1 := by
          have hsub : Finset.Icc 4 B ⊆ Finset.range (B + 1) := by
            intro x hx; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hx).2)
          calc (Finset.Icc 4 B).card ≤ (Finset.range (B + 1)).card := Finset.card_le_card hsub
            _ = B + 1 := Finset.card_range _
        have hcast : ((Finset.Icc 4 B).card : ℚ) ≤ ((B + 1 : ℕ) : ℚ) := by exact_mod_cast hcard_le
        have hpos_fac : 0 ≤ (2 : ℚ) ^ (B * B) * ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2 := by
          positivity
        nlinarith

end AlterationConstruction

end Erdos638
