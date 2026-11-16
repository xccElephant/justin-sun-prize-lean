/-
Copyright 2026 Chucheng Xiang (@xccElephant).
SPDX-License-Identifier: Apache-2.0

Clean-room formalization of the Simonovits–Cambie extremal stability induction for Erdős Problem
#1019 (`JSP-000849`):
every finite simple graph `G` on `n ≥ 1` vertices with `e(G) ≥ ⌊n²/4⌋ + ⌊(n-1)/2⌋` either contains
`K_4` or a bipyramid `B_l = C_l ∨ 2K_1` (`l ≥ 3`), or else has `e(G) = ⌊n²/4⌋ + ⌊(n-1)/2⌋` and is
a balanced tree-join `T_a ∨ b K_1` (`a + b = n`, `a ≥ 1`, `0 ≤ a - b ≤ 2`).
Consequently, every graph on `n` vertices with `e(G) ≥ ⌊n²/4⌋ + ⌊(n+1)/2⌋` (or exact equality)
contains `K_4` or some `B_l` (`l ≥ 3`).
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Erdos1019.Bipyramid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos1019

open Finset
open scoped SimpleGraph

/-- Lower extremal threshold `⌊n²/4⌋ + ⌊(n-1)/2⌋` for the Simonovits stability theorem. -/
def extremalEdges (n : ℕ) : ℕ :=
  n ^ 2 / 4 + (n - 1) / 2

/-- Erdős #1019 edge threshold `⌊n²/4⌋ + ⌊(n+1)/2⌋`. -/
def saturationThreshold (n : ℕ) : ℕ :=
  n ^ 2 / 4 + (n + 1) / 2

theorem saturationThreshold_eq_succ {n : ℕ} (hn : 1 ≤ n) :
    saturationThreshold n = extremalEdges n + 1 := by
  unfold saturationThreshold extremalEdges
  omega

theorem extremalEdges_step {n : ℕ} (hn : 2 ≤ n) :
    extremalEdges n = extremalEdges (n - 1) + (n + 1) / 2 := by
  unfold extremalEdges
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k := ⟨n / 4, by omega⟩
    have hk : 1 ≤ k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hsq1 : (4 * (m + 1)) ^ 2 / 4 = 4 * (m + 1) ^ 2 := by
      have : (4 * (m + 1)) ^ 2 = 4 * (4 * (m + 1) ^ 2) := by ring
      rw [this, Nat.mul_div_right _ (by omega)]
    have hsq2 : (4 * (m + 1) - 1) ^ 2 / 4 = 4 * m ^ 2 + 6 * m + 2 := by
      have hsub : 4 * (m + 1) - 1 = 4 * m + 3 := by omega
      rw [hsub]
      have : (4 * m + 3) ^ 2 = 4 * (4 * m ^ 2 + 6 * m + 2) + 1 := by ring
      rw [this]; omega
    rw [hsq1, hsq2]
    ring_nf
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
    have hsq1 : (4 * k + 1) ^ 2 / 4 = 4 * k ^ 2 + 2 * k := by
      have : (4 * k + 1) ^ 2 = 4 * (4 * k ^ 2 + 2 * k) + 1 := by ring
      rw [this]; omega
    have hsq2 : (4 * k) ^ 2 / 4 = 4 * k ^ 2 := by
      have : (4 * k) ^ 2 = 4 * (4 * k ^ 2) := by ring
      rw [this, Nat.mul_div_right _ (by omega)]
    have hsub : 4 * k + 1 - 1 = 4 * k := by omega
    rw [hsub, hsq1, hsq2]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
    have hsq1 : (4 * k + 2) ^ 2 / 4 = 4 * k ^ 2 + 4 * k + 1 := by
      have : (4 * k + 2) ^ 2 = 4 * (4 * k ^ 2 + 4 * k + 1) := by ring
      rw [this, Nat.mul_div_right _ (by omega)]
    have hsq2 : (4 * k + 1) ^ 2 / 4 = 4 * k ^ 2 + 2 * k := by
      have : (4 * k + 1) ^ 2 = 4 * (4 * k ^ 2 + 2 * k) + 1 := by ring
      rw [this]; omega
    have hsub : 4 * k + 2 - 1 = 4 * k + 1 := by omega
    rw [hsub, hsq1, hsq2]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
    have hsq1 : (4 * k + 3) ^ 2 / 4 = 4 * k ^ 2 + 6 * k + 2 := by
      have : (4 * k + 3) ^ 2 = 4 * (4 * k ^ 2 + 6 * k + 2) + 1 := by ring
      rw [this]; omega
    have hsq2 : (4 * k + 2) ^ 2 / 4 = 4 * k ^ 2 + 4 * k + 1 := by
      have : (4 * k + 2) ^ 2 = 4 * (4 * k ^ 2 + 4 * k + 1) := by ring
      rw [this, Nat.mul_div_right _ (by omega)]
    have hsub : 4 * k + 3 - 1 = 4 * k + 2 := by omega
    rw [hsub, hsq1, hsq2]
    omega

/-- Predicate that `G` contains `K_4` or a bipyramid `B_l = C_l ∨ 2K_1` for some `l ≥ 3`. -/
def ContainsK4OrBipyramid {V : Type*} (G : SimpleGraph V) : Prop :=
  ((⊤ : SimpleGraph (Fin 4)) ⊑ G) ∨ ∃ l : ℕ, 3 ≤ l ∧ (bipyramidGraph l ⊑ G)

theorem ContainsK4OrBipyramid.of_copy {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (f : H.Copy G) (hH : ContainsK4OrBipyramid H) : ContainsK4OrBipyramid G := by
  rcases hH with hk4 | ⟨l, hl, hbip⟩
  · exact Or.inl (hk4.trans ⟨f⟩)
  · exact Or.inr ⟨l, hl, hbip.trans ⟨f⟩⟩

/-- Constructor for `K_4 ⊑ G` from 4 pairwise adjacent vertices. -/
theorem containsK4_of_clique4 {V : Type*} {G : SimpleGraph V}
    (v₀ v₁ v₂ v₃ : V)
    (h01 : G.Adj v₀ v₁) (h02 : G.Adj v₀ v₂) (h03 : G.Adj v₀ v₃)
    (h12 : G.Adj v₁ v₂) (h13 : G.Adj v₁ v₃) (h23 : G.Adj v₂ v₃) :
    (⊤ : SimpleGraph (Fin 4)) ⊑ G := by
  let f : Fin 4 → V := ![v₀, v₁, v₂, v₃]
  have hadj : ∀ i j : Fin 4, i ≠ j → G.Adj (f i) (f j) := by
    intro i j hne
    fin_cases i <;> fin_cases j <;> simp_all [f, SimpleGraph.adj_comm]
  refine ⟨{
    toHom := ⟨f, fun {i j} hij => hadj i j hij⟩
    injective' := fun i j heq => by
      by_contra hne
      have ha : G.Adj (f i) (f j) := hadj i j hne
      change f i = f j at heq
      rw [heq] at ha
      exact ha.ne rfl
  }⟩

/-- Constructor for `bipyramidGraph l ⊑ G` from a cycle `c : Fin l ↪ V` (`l ≥ 3`) and two distinct
apices `w₁ ≠ w₂` disjoint from `c` and adjacent to every vertex of `c`. -/
theorem containsBipyramid_of_cycle_and_apices {V : Type*} {G : SimpleGraph V}
    {l : ℕ} (c : Fin l ↪ V)
    (hadj_next : ∀ i : Fin l, ∀ (hi : i.1 + 1 < l), G.Adj (c i) (c ⟨i.1 + 1, hi⟩))
    (hadj_close : ∀ (hl0 : 0 < l), G.Adj (c ⟨0, hl0⟩) (c ⟨l - 1, by omega⟩))
    (w₁ w₂ : V) (hw_ne : w₁ ≠ w₂)
    (hw₁_disj : ∀ i : Fin l, c i ≠ w₁)
    (hw₂_disj : ∀ i : Fin l, c i ≠ w₂)
    (hw₁_adj : ∀ i : Fin l, G.Adj (c i) w₁)
    (hw₂_adj : ∀ i : Fin l, G.Adj (c i) w₂) :
    bipyramidGraph l ⊑ G := by
  let f : BipyramidVert l → V
    | Sum.inl i => c i
    | Sum.inr true => w₁
    | Sum.inr false => w₂
  refine ⟨{
    toHom := {
      toFun := f
      map_rel' := by
        intro u v huv
        cases u with
        | inl i =>
          have hi_lt : i.1 < l := i.2
          cases v with
          | inl j =>
            have hj_lt : j.1 < l := j.2
            rcases huv with ⟨_, h1 | h2 | ⟨hi0, hj⟩ | ⟨hj0, hi⟩⟩
            · have heq : j = ⟨i.1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
              change G.Adj (c i) (c j)
              rw [heq]; exact hadj_next i (by omega)
            · have heq : i = ⟨j.1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
              change G.Adj (c i) (c j)
              rw [heq]; exact (hadj_next j (by omega)).symm
            · have hl0 : 0 < l := by omega
              have hi_eq : i = ⟨0, hl0⟩ := Fin.ext hi0
              have hj_eq : j = ⟨l - 1, by omega⟩ := Fin.ext (by dsimp; omega)
              change G.Adj (c i) (c j)
              rw [hi_eq, hj_eq]; exact hadj_close hl0
            · have hl0 : 0 < l := by omega
              have hj_eq : j = ⟨0, hl0⟩ := Fin.ext hj0
              have hi_eq : i = ⟨l - 1, by omega⟩ := Fin.ext (by dsimp; omega)
              change G.Adj (c i) (c j)
              rw [hi_eq, hj_eq]; exact (hadj_close hl0).symm
          | inr b =>
            cases b
            · exact hw₂_adj i
            · exact hw₁_adj i
        | inr b =>
          cases v with
          | inl j =>
            cases b
            · exact (hw₂_adj j).symm
            · exact (hw₁_adj j).symm
          | inr _ => exact False.elim huv
    }
    injective' := by
      intro u v heq
      cases u with
      | inl i =>
        cases v with
        | inl j => exact congrArg Sum.inl (c.injective heq)
        | inr b =>
          cases b
          · exact False.elim (hw₂_disj i heq)
          · exact False.elim (hw₁_disj i heq)
      | inr b₁ =>
        cases v with
        | inl j =>
          cases b₁
          · exact False.elim (hw₂_disj j heq.symm)
          · exact False.elim (hw₁_disj j heq.symm)
        | inr b₂ =>
          cases b₁ <;> cases b₂
          · rfl
          · exact False.elim (hw_ne heq.symm)
          · exact False.elim (hw_ne heq)
          · rfl
  }⟩

/-! ### Balanced Tree-Independent Join Structure `T_a ∨ b K_1` -/

/-- `IsBalancedTreeJoin G` holds when `V` partitions into a nonempty `A` and `B = V \ A` such that
`0 ≤ |A| - |B| ≤ 2`, `G[A]` is a tree, `B` is an independent set, and every vertex of `A` is
adjacent to every vertex of `B`. -/
def IsBalancedTreeJoin {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ A : Finset V,
    1 ≤ #A ∧
    Fintype.card V ≤ 2 * #A ∧
    2 * #A ≤ Fintype.card V + 2 ∧
    (G.induce (A : Set V)).IsTree ∧
    (∀ b₁ ∉ A, ∀ b₂ ∉ A, ¬ G.Adj b₁ b₂) ∧
    (∀ a ∈ A, ∀ b ∉ A, G.Adj a b)

/-- Edge-counting formula for a vertex partition `(A, Aᶜ)` where `Aᶜ` is independent and complete
to `A`: `#G.edgeFinset = #(G.induce A).edgeFinset + #A * (|V| - #A)`. -/
lemma card_edgeFinset_of_indep_join {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V)
    (hB_indep : ∀ b₁ ∉ A, ∀ b₂ ∉ A, ¬ G.Adj b₁ b₂)
    (hCross : ∀ a ∈ A, ∀ b ∉ A, G.Adj a b) :
    #G.edgeFinset = #(G.induce (A : Set V)).edgeFinset + #A * (Fintype.card V - #A) := by
  have hsplit : #G.edgeFinset =
      #{e ∈ G.edgeFinset | e.toFinset ⊆ A} + #{e ∈ G.edgeFinset | ¬ e.toFinset ⊆ A} :=
    (Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (p := (·.toFinset ⊆ A))).symm
  rw [hsplit, G.card_filter_edgeFinset_toFinset_subset A]
  congr 1
  let crossSet := {e ∈ G.edgeFinset | ¬ e.toFinset ⊆ A}
  have hbij : #(A ×ˢ (univ \ A)) = #crossSet := by
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      rcases mem_product.mp hp with ⟨ha, hb⟩
      have hb_not : b ∉ A := (mem_sdiff.mp hb).2
      rw [mem_filter]
      refine ⟨G.mem_edgeFinset.mpr (hCross a ha b hb_not), ?_⟩
      intro hsub
      exact hb_not (hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right a b)))
    · rintro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ heq
      rcases mem_product.mp hp₁ with ⟨ha₁, hb₁⟩
      rcases mem_product.mp hp₂ with ⟨ha₂, hb₂⟩
      have hb₁_not : b₁ ∉ A := (mem_sdiff.mp hb₁).2
      have hb₂_not : b₂ ∉ A := (mem_sdiff.mp hb₂).2
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact False.elim (hb₂_not ha₁)
    · intro e he
      rcases mem_filter.mp he with ⟨he_edge, hnot_sub⟩
      induction e using Sym2.inductionOn with
      | hf u v =>
        have huv : G.Adj u v := G.mem_edgeFinset.mp he_edge
        by_cases hu : u ∈ A
        · by_cases hv : v ∈ A
          · exfalso
            apply hnot_sub
            intro z hz
            rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hz) with rfl | rfl <;> assumption
          · exact ⟨(u, v), mem_product.mpr ⟨hu, mem_sdiff.mpr ⟨mem_univ _, hv⟩⟩, rfl⟩
        · by_cases hv : v ∈ A
          · exact ⟨(v, u), mem_product.mpr ⟨hv, mem_sdiff.mpr ⟨mem_univ _, hu⟩⟩, Sym2.eq_swap⟩
          · exact False.elim (hB_indep u hu v hv huv)
  rw [← hbij, card_product, card_sdiff_of_subset (subset_univ A), card_univ]

/-- Every balanced tree-join on `n` vertices has exact edge count `extremalEdges n`. -/
theorem IsBalancedTreeJoin.card_edgeFinset_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : IsBalancedTreeJoin G) :
    #G.edgeFinset = extremalEdges (Fintype.card V) := by
  rcases h with ⟨A, hA1, hle1, hle2, hTree, hB_indep, hCross⟩
  classical
  have hcard_ind := card_edgeFinset_of_indep_join G A hB_indep hCross
  have hTree_edges : #(G.induce (A : Set V)).edgeFinset + 1 = #A := by
    simpa using hTree.card_edgeFinset
  have hA_le_n : #A ≤ Fintype.card V := card_le_univ A
  set n := Fintype.card V
  set a := #A
  have hcases : 2 * a = n ∨ 2 * a = n + 1 ∨ 2 * a = n + 2 := by omega
  unfold extremalEdges
  rcases hcases with heven | hodd | heven2
  · have hn : n = 2 * a := by omega
    have hsq : (2 * a) ^ 2 / 4 = a ^ 2 := by
      have : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
      rw [this, Nat.mul_div_right _ (by omega)]
    have hna : n - a = a := by omega
    rw [hcard_ind, hna, hn, hsq]
    have hmul : a * a = a ^ 2 := by ring
    omega
  · obtain ⟨m, hm⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    have hn' : n = 2 * m + 1 := by omega
    have hna : n - a = m := by omega
    have hsq : (2 * m + 1) ^ 2 / 4 = m ^ 2 + m := by
      have : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
      rw [this]; omega
    rw [hcard_ind, hna, hm, hn', hsq]
    have hmul : (m + 1) * m = m ^ 2 + m := by ring
    omega
  · obtain ⟨m, hm⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
    have hn' : n = 2 * m + 2 := by omega
    have hna : n - a = m := by omega
    have hsq : (2 * m + 2) ^ 2 / 4 = m ^ 2 + 2 * m + 1 := by
      have : (2 * m + 2) ^ 2 = 4 * (m ^ 2 + 2 * m + 1) := by ring
      rw [this, Nat.mul_div_right _ (by omega)]
    rw [hcard_ind, hna, hm, hn', hsq]
    have hmul : (m + 2) * m = m ^ 2 + 2 * m := by ring
    omega

/-! ### Helper Lemmas on Trees: Unique Path Cycle Extraction, Leaf Extension, and Star Criterion -/

/-- Adding a new vertex `x ∉ A` adjacent to a unique vertex `u ∈ A` of a tree `G[A]` yields a
tree `G[insert x A]`. -/
lemma isTree_induce_insert_leaf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (x u : V)
    (hxA : x ∉ A) (huA : u ∈ A)
    (hTree : (G.induce (A : Set V)).IsTree)
    (hAdj_u : G.Adj x u)
    (hOnly_u : ∀ a ∈ A, G.Adj x a → a = u) :
    (G.induce ((insert x A : Finset V) : Set V)).IsTree := by
  classical
  let A' : Finset V := insert x A
  let H := G.induce (A' : Set V)
  rw [SimpleGraph.isTree_iff_connected_and_card]
  have hxA' : x ∈ (A' : Set V) := Finset.mem_coe.mpr (mem_insert_self x A)
  have huA' : u ∈ (A' : Set V) := Finset.mem_coe.mpr (mem_insert_of_mem huA)
  have subA : (A : Set V) ⊆ (A' : Set V) := by
    intro z hz
    exact Finset.mem_coe.mpr (mem_insert_of_mem (Finset.mem_coe.mp hz))
  -- 1. Connectedness of `H`
  have hConn : H.Connected := by
    have : Nonempty (A' : Set V) := ⟨⟨x, hxA'⟩⟩
    refine SimpleGraph.Connected.mk ?_
    intro v₁ v₂
    have reach_from_A : ∀ z (hz : z ∈ (A : Set V)), H.Reachable ⟨u, huA'⟩ ⟨z, subA hz⟩ := by
      intro z hz
      obtain ⟨w⟩ := hTree.connected ⟨u, Finset.mem_coe.mpr huA⟩ ⟨z, hz⟩
      let hom : G.induce (A : Set V) →g H := {
        toFun := fun y => ⟨y.1, subA y.2⟩
        map_rel' := fun h => h
      }
      exact ⟨w.map hom⟩
    have reach_u : ∀ v : (A' : Set V), H.Reachable ⟨u, huA'⟩ v := by
      rintro ⟨z, hz⟩
      rcases mem_insert.mp (Finset.mem_coe.mp hz) with rfl | hzA
      · exact SimpleGraph.Adj.reachable hAdj_u.symm
      · exact reach_from_A z (Finset.mem_coe.mpr hzA)
    exact (reach_u v₁).symm.trans (reach_u v₂)
  refine ⟨hConn, ?_⟩
  -- 2. Edge count: `#H.edgeFinset + 1 = #(insert x A)`
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hV_card : Fintype.card (A' : Set V) = #(insert x A) := Fintype.card_coe A'
  have hH_card : Fintype.card H.edgeSet = #H.edgeFinset := H.card_edgeSet
  change Fintype.card H.edgeSet + 1 = Fintype.card (A' : Set V)
  rw [hH_card, hV_card, card_insert_of_notMem hxA]
  -- Delete `⟨x, hxA'⟩` from `H`: its degree in `H` is 1, and `H.induce {⟨x, hxA'⟩}ᶜ ≃g G.induce A`
  let x_sub : (A' : Set V) := ⟨x, hxA'⟩
  let u_sub : (A' : Set V) := ⟨u, huA'⟩
  have hdeg_x : H.degree x_sub = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hset : H.neighborFinset x_sub = {u_sub} := by
      ext ⟨z, hz⟩
      simp only [SimpleGraph.mem_neighborFinset, mem_singleton]
      constructor
      · intro hadj
        rcases mem_insert.mp (Finset.mem_coe.mp hz) with rfl | hzA
        · exact False.elim (hadj.ne rfl)
        · exact Subtype.ext (hOnly_u z hzA hadj)
      · intro heq
        rw [heq]
        exact hAdj_u
    rw [hset, card_singleton]
  have hdel := H.card_edgeFinset_deleteIncidenceSet x_sub
  have hind := H.card_edgeFinset_induce_compl_singleton x_sub
  -- Bijection between `(H.induce {x_sub}ᶜ).edgeFinset` and `(G.induce A).edgeFinset`
  let iso : H.induce ({x_sub}ᶜ : Set (A' : Set V)) ≃g G.induce (A : Set V) := {
    toFun := fun y => ⟨y.1.1, by
      have hy_mem : y.1.1 ∈ A' := Finset.mem_coe.mp y.1.2
      have hy_ne : y.1.1 ≠ x := fun h => y.2 (Subtype.ext h)
      rcases mem_insert.mp hy_mem with hzx | hA
      · exact False.elim (hy_ne hzx)
      · exact Finset.mem_coe.mpr hA⟩
    invFun := fun z => ⟨⟨z.1, subA z.2⟩, by
      intro hEq
      have hzx : z.1 = x := congrArg Subtype.val hEq
      have hzA : z.1 ∈ A := Finset.mem_coe.mp z.2
      rw [hzx] at hzA
      exact hxA hzA⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl
  }
  have hiso_edges : #(H.induce ({x_sub}ᶜ : Set (A' : Set V))).edgeFinset =
      #(G.induce (A : Set V)).edgeFinset := by
    rw [← SimpleGraph.card_edgeSet, ← SimpleGraph.card_edgeSet]
    exact Fintype.card_congr iso.mapEdgeSet
  have hTree_card : #(G.induce (A : Set V)).edgeFinset + 1 = #A := by
    simpa using hTree.card_edgeFinset
  have hge1 : 1 ≤ #H.edgeFinset := by
    rw [Finset.one_le_card]
    exact ⟨s(x_sub, u_sub), H.mem_edgeFinset.mpr hAdj_u⟩
  omega

/-- If `G[A]` is a tree and `u₁ ≠ u₂` are non-adjacent in `G[A]`, then `G[A]` contains a simple
path `c_0, c_1, ..., c_m` (`m ≥ 2`) from `u₁` to `u₂`; adding a vertex `x ∉ A` adjacent to `u₁`
and `u₂` produces a cycle of length `m + 2 ≥ 4` inside `A ∪ {x}`. -/
lemma exists_cycle_of_nonadj_in_tree {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (x u₁ u₂ : V)
    (hxA : x ∉ A) (hu₁ : u₁ ∈ A) (hu₂ : u₂ ∈ A) (hu_ne : u₁ ≠ u₂)
    (hnot_adj : ¬ G.Adj u₁ u₂)
    (hx_u₁ : G.Adj x u₁) (hx_u₂ : G.Adj x u₂)
    (hTree : (G.induce (A : Set V)).IsTree) :
    ∃ (l : ℕ) (hl : 3 ≤ l) (c : Fin l ↪ V),
      (∀ i : Fin l, c i ∈ insert x A) ∧
      (∀ i : Fin l, ∀ (hi : i.1 + 1 < l), G.Adj (c i) (c ⟨i.1 + 1, hi⟩)) ∧
      G.Adj (c ⟨0, by omega⟩) (c ⟨l - 1, by omega⟩) := by
  let u₁' : (A : Set V) := ⟨u₁, Finset.mem_coe.mpr hu₁⟩
  let u₂' : (A : Set V) := ⟨u₂, Finset.mem_coe.mpr hu₂⟩
  obtain ⟨p, hp⟩ := hTree.connected.exists_isPath u₁' u₂'
  -- Length `p.length ≥ 2` since `u₁ ≠ u₂` and `¬ G.Adj u₁ u₂`
  have hlen_ne0 : p.length ≠ 0 := by
    intro h0
    have heq := SimpleGraph.Walk.eq_of_length_eq_zero h0
    exact hu_ne (congrArg Subtype.val heq)
  have hlen_ne1 : p.length ≠ 1 := by
    intro h1
    have hadj0 : (G.induce (A : Set V)).Adj (p.getVert 0) (p.getVert 1) :=
      p.adj_getVert_succ (by omega)
    rw [p.getVert_zero, ← h1, p.getVert_length] at hadj0
    exact hnot_adj hadj0
  have hlen_ge2 : 2 ≤ p.length := by omega
  let l := p.length + 2
  have hl3 : 3 ≤ l := by omega
  let cFun : Fin l → V := fun i =>
    if h : i.1 ≤ p.length then (p.getVert i.1).1 else x
  have hc_inj : Function.Injective cFun := by
    intro i j heq
    have hi_lt : i.1 < l := i.2
    have hj_lt : j.1 < l := j.2
    dsimp [cFun] at heq
    split_ifs at heq with hi_le hj_le hj_le
    · have hsub_eq : p.getVert i.1 = p.getVert j.1 := Subtype.ext heq
      have hij : i.1 = j.1 := hp.getVert_injOn hi_le hj_le hsub_eq
      exact Fin.ext hij
    · exfalso
      have hmem : (p.getVert i.1).1 ∈ A := Finset.mem_coe.mp (p.getVert i.1).2
      rw [heq] at hmem
      exact hxA hmem
    · exfalso
      have hmem : (p.getVert j.1).1 ∈ A := Finset.mem_coe.mp (p.getVert j.1).2
      rw [← heq] at hmem
      exact hxA hmem
    · exact Fin.ext (by omega)
  refine ⟨l, hl3, ⟨cFun, hc_inj⟩, ?_, ?_, ?_⟩
  · -- Membership in `insert x A`
    intro i
    dsimp [cFun]
    split_ifs with hi_le
    · exact mem_insert_of_mem (Finset.mem_coe.mp (p.getVert i.1).2)
    · exact mem_insert_self x A
  · -- Consecutive adjacencies `c i ~ c (i + 1)`
    intro i hi
    dsimp [cFun]
    split_ifs with h1 h2 h2
    · exact p.adj_getVert_succ (by omega)
    · have hi_eq : i.1 = p.length := by omega
      have hvert : (p.getVert i.1).1 = u₂ := by
        rw [hi_eq, p.getVert_length]
      rw [hvert]
      exact hx_u₂.symm
    · omega
    · omega
  · -- Closing edge `c 0 ~ c (l - 1)` is `u₁ ~ x`
    dsimp [cFun]
    rw [if_neg (by omega)]
    have h0 : (p.getVert 0).1 = u₁ := by rw [p.getVert_zero]
    rw [h0]
    exact hx_u₁.symm

/-- Star characterization on trees: if `G[A]` is a tree with `u ∈ A`, and no two vertices in
`A \ {u}` are adjacent in `G`, then every vertex in `A \ {u}` is adjacent to `u`, so `A \ {u}` is
an independent set and every vertex of `A \ {u}` is joined to `u`. -/
lemma star_of_tree_compl_indep {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (u : V) (hu : u ∈ A)
    (hTree : (G.induce (A : Set V)).IsTree)
    (hIndep : ∀ y ∈ A, y ≠ u → ∀ z ∈ A, z ≠ u → ¬ G.Adj y z) :
    ∀ y ∈ A, y ≠ u → G.Adj y u := by
  intro y hy hy_ne
  let y' : (A : Set V) := ⟨y, Finset.mem_coe.mpr hy⟩
  let u' : (A : Set V) := ⟨u, Finset.mem_coe.mpr hu⟩
  obtain ⟨p, hp⟩ := hTree.connected.exists_isPath y' u'
  have hlen_pos : 0 < p.length := by
    by_contra h0
    have heq := SimpleGraph.Walk.eq_of_length_eq_zero (by omega : p.length = 0)
    exact hy_ne (congrArg Subtype.val heq)
  have hadj01 : G.Adj (p.getVert 0).1 (p.getVert 1).1 := p.adj_getVert_succ hlen_pos
  have hv0 : (p.getVert 0).1 = y := by rw [p.getVert_zero]
  rw [hv0] at hadj01
  by_cases hv1 : (p.getVert 1).1 = u
  · rwa [hv1] at hadj01
  · exfalso
    have hv1_A : (p.getVert 1).1 ∈ A := Finset.mem_coe.mp (p.getVert 1).2
    exact hIndep y hy hy_ne (p.getVert 1).1 hv1_A hv1 hadj01

/-- Broom tree lemma (Case `(b)` of Cambie's proof):
Suppose `V` partitions into `A'`, `B'`, `{x}` with `u ∈ A'`, `v ∈ B'`, such that:
* `B'` is an independent set in `G`,
* every vertex of `B'` is adjacent to `u`,
* `x` is adjacent to `v` and NOT adjacent to any other vertex of `B'`,
* `x` is NOT adjacent to `u`.
Then `S := insert x (insert u B')` induces a tree in `G`! -/
lemma isTree_broom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B' : Finset V) (u v x : V)
    (huB : u ∉ B') (hvB : v ∈ B') (hxB : x ∉ B') (hxu_ne : x ≠ u)
    (hB_indep : ∀ b₁ ∈ B', ∀ b₂ ∈ B', ¬ G.Adj b₁ b₂)
    (hu_B : ∀ b ∈ B', G.Adj u b)
    (hxv : G.Adj x v)
    (hx_only_v : ∀ b ∈ B', G.Adj x b → b = v)
    (hnot_xu : ¬ G.Adj x u) :
    (G.induce ((insert x (insert u B') : Finset V) : Set V)).IsTree := by
  -- First show `insert u B'` induces a star tree centered at `u`
  have hStar : (G.induce ((insert u B' : Finset V) : Set V)).IsTree := by
    classical
    let S₀ := insert u B'
    let H₀ := G.induce (S₀ : Set V)
    rw [SimpleGraph.isTree_iff_connected_and_card]
    have huS₀ : u ∈ (S₀ : Set V) := Finset.mem_coe.mpr (mem_insert_self u B')
    have hConn₀ : H₀.Connected := by
      have : Nonempty (S₀ : Set V) := ⟨⟨u, huS₀⟩⟩
      refine SimpleGraph.Connected.mk ?_
      rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
      have reach_u : ∀ z (hz : z ∈ (S₀ : Set V)), H₀.Reachable ⟨u, huS₀⟩ ⟨z, hz⟩ := by
        intro z hz
        rcases mem_insert.mp (Finset.mem_coe.mp hz) with rfl | hzB
        · exact SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable (hu_B z hzB)
      exact (reach_u z₁ hz₁).symm.trans (reach_u z₂ hz₂)
    refine ⟨hConn₀, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hV₀_card : Fintype.card (S₀ : Set V) = #(insert u B') := Fintype.card_coe S₀
    have hH₀_card : Fintype.card H₀.edgeSet = #H₀.edgeFinset := H₀.card_edgeSet
    change Fintype.card H₀.edgeSet + 1 = Fintype.card (S₀ : Set V)
    rw [hH₀_card, hV₀_card, card_insert_of_notMem huB]
    -- Count edges of `H₀`: every edge has `u` and some `b ∈ B'`!
    have hEdges₀ : #H₀.edgeFinset = #B' := by
      symm
      refine Finset.card_bij
        (fun b hb => s((⟨u, huS₀⟩ : (S₀ : Set V)),
          ⟨b, Finset.mem_coe.mpr (mem_insert_of_mem hb)⟩))
        ?_ ?_ ?_
      · intro b hb
        exact H₀.mem_edgeFinset.mpr (hu_B b hb)
      · intro b₁ hb₁ b₂ hb₂ heq
        rcases Sym2.eq_iff.mp heq with ⟨_, hb_eq⟩ | ⟨hub, _⟩
        · exact congrArg Subtype.val hb_eq
        · exfalso
          have hval : u = b₂ := congrArg Subtype.val hub
          rw [← hval] at hb₂
          exact huB hb₂
      · intro e he
        induction e using Sym2.inductionOn with
        | hf z₁ z₂ =>
          have hadj : G.Adj z₁.1 z₂.1 := H₀.mem_edgeFinset.mp he
          rcases mem_insert.mp (Finset.mem_coe.mp z₁.2) with hz₁_u | hz₁_B
          · rcases mem_insert.mp (Finset.mem_coe.mp z₂.2) with hz₂_u | hz₂_B
            · exfalso
              rw [hz₁_u, hz₂_u] at hadj
              exact hadj.ne rfl
            · refine ⟨z₂.1, hz₂_B, ?_⟩
              have h1 : (⟨u, huS₀⟩ : (S₀ : Set V)) = z₁ := Subtype.ext hz₁_u.symm
              rw [h1]
          · rcases mem_insert.mp (Finset.mem_coe.mp z₂.2) with hz₂_u | hz₂_B
            · refine ⟨z₁.1, hz₁_B, ?_⟩
              have h2 : (⟨u, huS₀⟩ : (S₀ : Set V)) = z₂ := Subtype.ext hz₂_u.symm
              rw [h2, Sym2.eq_swap]
            · exact False.elim (hB_indep z₁.1 hz₁_B z₂.1 hz₂_B hadj)
    omega
  -- Second, `x ∉ insert u B'` attaches only to `v ∈ insert u B'`, so `isTree_induce_insert_leaf` applies!
  have hx_not_S₀ : x ∉ insert u B' := by
    simp [hxu_ne, hxB]
  have hv_S₀ : v ∈ insert u B' := mem_insert_of_mem hvB
  refine isTree_induce_insert_leaf G (insert u B') x v hx_not_S₀ hv_S₀ hStar hxv ?_
  intro a ha hadj
  rcases mem_insert.mp ha with rfl | haB
  · exact False.elim (hnot_xu hadj)
  · exact hx_only_v a haB hadj

/-! ### Minimum-Degree Bound at the Extremal Threshold -/

lemma exists_vertex_degree_le_half_succ {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 1 ≤ Fintype.card V)
    (hedges : #G.edgeFinset ≤ extremalEdges (Fintype.card V)) :
    ∃ x : V, G.degree x ≤ (Fintype.card V + 1) / 2 := by
  by_contra hnone
  have hnone' : ∀ v : V, (Fintype.card V + 1) / 2 < G.degree v := by
    intro v
    by_contra hv
    exact hnone ⟨v, Nat.le_of_not_lt hv⟩
  set n := Fintype.card V
  have hsum_ge : n * ((n + 1) / 2 + 1) ≤ ∑ v : V, G.degree v := by
    have hle : ∑ _v : V, ((n + 1) / 2 + 1) ≤ ∑ v : V, G.degree v :=
      Finset.sum_le_sum fun v _ => hnone' v
    simpa [Finset.sum_const, Finset.card_univ] using hle
  have hsum_eq := G.sum_degrees_eq_twice_card_edges
  have htwice : n * ((n + 1) / 2 + 1) ≤ 2 * extremalEdges n := by omega
  unfold extremalEdges at htwice
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k := ⟨n / 4, by omega⟩
    have hsq : n ^ 2 / 4 = 4 * k ^ 2 := by
      rw [hk]
      have : (4 * k) ^ 2 = 4 * (4 * k ^ 2) := by ring
      rw [this, Nat.mul_div_right _ (by omega)]
    rw [hsq, hk] at htwice
    have hk1 : 1 ≤ k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1' : (4 * (m + 1) + 1) / 2 = 2 * m + 2 := by omega
    have h2' : (4 * (m + 1) - 1) / 2 = 2 * m + 1 := by omega
    rw [h1', h2'] at htwice
    nlinarith
  · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
    have hsq : n ^ 2 / 4 = 4 * k ^ 2 + 2 * k := by
      rw [hk]
      have : (4 * k + 1) ^ 2 = 4 * (4 * k ^ 2 + 2 * k) + 1 := by ring
      rw [this]; omega
    rw [hsq, hk] at htwice
    have h1' : (4 * k + 1 + 1) / 2 = 2 * k + 1 := by omega
    have h2' : (4 * k + 1 - 1) / 2 = 2 * k := by omega
    rw [h1', h2'] at htwice
    nlinarith
  · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
    have hsq : n ^ 2 / 4 = 4 * k ^ 2 + 4 * k + 1 := by
      rw [hk]
      have : (4 * k + 2) ^ 2 = 4 * (4 * k ^ 2 + 4 * k + 1) := by ring
      rw [this, Nat.mul_div_right _ (by omega)]
    rw [hsq, hk] at htwice
    have h1' : (4 * k + 2 + 1) / 2 = 2 * k + 1 := by omega
    have h2' : (4 * k + 2 - 1) / 2 = 2 * k := by omega
    rw [h1', h2'] at htwice
    nlinarith
  · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
    have hsq : n ^ 2 / 4 = 4 * k ^ 2 + 6 * k + 2 := by
      rw [hk]
      have : (4 * k + 3) ^ 2 = 4 * (4 * k ^ 2 + 6 * k + 2) + 1 := by ring
      rw [this]; omega
    rw [hsq, hk] at htwice
    have h1' : (4 * k + 3 + 1) / 2 = 2 * k + 2 := by omega
    have h2' : (4 * k + 3 - 1) / 2 = 2 * k + 1 := by omega
    rw [h1', h2'] at htwice
    nlinarith

/-! ### Simonovits–Cambie Extremal Stability Theorem and Saturation Consequences -/

/-- Adding any single edge `u₀ ~ v₀` to a balanced tree-join `G₁ ≤ G` creates either `K_4` or
a bipyramid `B_l` (`l ≥ 3`) in `G`. -/
lemma contains_of_balancedTreeJoin_and_extra_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G₁ G : SimpleGraph V} [DecidableRel G₁.Adj]
    (hle : G₁ ≤ G)
    (hBTJ : IsBalancedTreeJoin G₁)
    {u₀ v₀ : V} (h_not_adj₁ : ¬ G₁.Adj u₀ v₀) (h_adjG : G.Adj u₀ v₀) :
    ContainsK4OrBipyramid G := by
  have hu₀_ne_v₀ : u₀ ≠ v₀ := h_adjG.ne
  rcases hBTJ with ⟨A, hA1, hle1, hle2, hTree, hB_indep, hCross⟩
  have hA_le_n : #A ≤ Fintype.card V := card_le_univ A
  by_cases huA : u₀ ∈ A
  · by_cases hvA : v₀ ∈ A
    · -- Both `u₀, v₀ ∈ A`: unique path in `G₁[A]` between `u₀` and `v₀` has length `≥ 2`
      let u' : (A : Set V) := ⟨u₀, Finset.mem_coe.mpr huA⟩
      let v' : (A : Set V) := ⟨v₀, Finset.mem_coe.mpr hvA⟩
      obtain ⟨p, hp⟩ := hTree.connected.exists_isPath u' v'
      have hlen_ne0 : p.length ≠ 0 := by
        intro h0
        exact hu₀_ne_v₀ (congrArg Subtype.val (SimpleGraph.Walk.eq_of_length_eq_zero h0))
      have hlen_ne1 : p.length ≠ 1 := by
        intro h1
        have hadj0 : G₁.Adj (p.getVert 0).1 (p.getVert 1).1 := p.adj_getVert_succ (by omega)
        rw [p.getVert_zero, ← h1, p.getVert_length] at hadj0
        exact h_not_adj₁ hadj0
      have hlen_ge2 : 2 ≤ p.length := by omega
      -- Since `p` is a simple path of length `≥ 2` in `A`, `#A ≥ p.length + 1 ≥ 3`
      let l := p.length + 1
      have hl3 : 3 ≤ l := by omega
      let cFun : Fin l → V := fun i => (p.getVert i.1).1
      have hc_inj : Function.Injective cFun := by
        intro i j heq
        have hi_le : i.1 ≤ p.length := by omega
        have hj_le : j.1 ≤ p.length := by omega
        exact Fin.ext (hp.getVert_injOn hi_le hj_le (Subtype.ext heq))
      have hc_mem : ∀ i : Fin l, cFun i ∈ A :=
        fun i => Finset.mem_coe.mp (p.getVert i.1).2
      have hl_le_A : l ≤ #A := by
        have hmap_sub : univ.map ⟨cFun, hc_inj⟩ ⊆ A := by
          intro z hz
          rcases mem_map.mp hz with ⟨i, _, rfl⟩
          exact hc_mem i
        have hc := Finset.card_le_card hmap_sub
        rwa [card_map, card_univ, Fintype.card_fin] at hc
      have hA_ge3 : 3 ≤ #A := le_trans hl3 hl_le_A
      -- Check `#(univ \ A)` (`b = |V| - #A`): since `2 * #A ≤ |V| + 2` and `#A ≥ 3`, `b ≥ 1`!
      let B := univ \ A
      have hB_card : #B = Fintype.card V - #A := by
        rw [card_sdiff_of_subset (subset_univ A), card_univ]
      by_cases hB2 : 2 ≤ #B
      · -- Two apices `w₁ ≠ w₂` in `B` joined to the cycle `cFun` in `G` -> `bipyramidGraph l ⊑ G`!
        obtain ⟨w₁, hw₁, w₂, hw₂, hw_ne⟩ := Finset.one_lt_card.mp (by omega : 1 < #B)
        have hw₁_notA : w₁ ∉ A := (mem_sdiff.mp hw₁).2
        have hw₂_notA : w₂ ∉ A := (mem_sdiff.mp hw₂).2
        right
        refine ⟨l, hl3, containsBipyramid_of_cycle_and_apices ⟨cFun, hc_inj⟩ ?_ ?_
          w₁ w₂ hw_ne ?_ ?_ ?_ ?_⟩
        · intro i hi
          exact hle (p.adj_getVert_succ (by omega))
        · intro hl0
          change G.Adj (cFun ⟨0, hl0⟩) (cFun ⟨l - 1, by omega⟩)
          have h0 : cFun ⟨0, hl0⟩ = u₀ := by dsimp [cFun]; rw [p.getVert_zero]
          have hlast : cFun ⟨l - 1, by omega⟩ = v₀ := by
            dsimp [cFun]
            have hsub : l - 1 = p.length := by omega
            rw [hsub, p.getVert_length]
          rw [h0, hlast]
          exact h_adjG
        · intro i heq
          exact hw₁_notA (heq ▸ hc_mem i)
        · intro i heq
          exact hw₂_notA (heq ▸ hc_mem i)
        · intro i
          exact hle (hCross (cFun i) (hc_mem i) w₁ hw₁_notA)
        · intro i
          exact hle (hCross (cFun i) (hc_mem i) w₂ hw₂_notA)
      · -- Otherwise `#B < 2`, and since `#A ≥ 3` and `2 * #A ≤ |V| + 2`, `#A = 3` and `#B = 1`!
        have hB1 : 0 < #B := by omega
        obtain ⟨w, hw⟩ := Finset.card_pos.mp hB1
        have hw_notA : w ∉ A := (mem_sdiff.mp hw).2
        have hplen2 : p.length = 2 := by omega
        let a₀ := cFun ⟨0, by omega⟩
        let a₁ := cFun ⟨1, by omega⟩
        let a₂ := cFun ⟨2, by omega⟩
        have ha₀_eq : a₀ = u₀ := by dsimp [a₀, cFun]; rw [p.getVert_zero]
        have ha₂_eq : a₂ = v₀ := by
          dsimp [a₂, cFun]
          rw [← hplen2, p.getVert_length]
        have hadj01 : G.Adj a₀ a₁ := hle (p.adj_getVert_succ (by dsimp; omega))
        have hadj12 : G.Adj a₁ a₂ := hle (p.adj_getVert_succ (by dsimp; omega))
        have hadj02 : G.Adj a₀ a₂ := by rw [ha₀_eq, ha₂_eq]; exact h_adjG
        left
        exact containsK4_of_clique4 a₀ a₁ a₂ w
          hadj01 hadj02 (hle (hCross a₀ (hc_mem _) w hw_notA))
          hadj12 (hle (hCross a₁ (hc_mem _) w hw_notA))
          (hle (hCross a₂ (hc_mem _) w hw_notA))
    · -- `u₀ ∈ A` and `v₀ ∉ A` contradicts `hCross`!
      exact False.elim (h_not_adj₁ (hCross u₀ huA v₀ hvA))
  · by_cases hvA : v₀ ∈ A
    · -- `u₀ ∉ A` and `v₀ ∈ A` contradicts `hCross`!
      exact False.elim (h_not_adj₁ (hCross v₀ hvA u₀ huA).symm)
    · -- Both `u₀ ∉ A` and `v₀ ∉ A` (`u₀ ≠ v₀`): so `#(univ \ A) ≥ 2`, hence `#A ≥ 2`!
      let B := univ \ A
      have huB : u₀ ∈ B := mem_sdiff.mpr ⟨mem_univ _, huA⟩
      have hvB : v₀ ∈ B := mem_sdiff.mpr ⟨mem_univ _, hvA⟩
      have hB_ge2 : 2 ≤ #B := by
        have hsub : ({u₀, v₀} : Finset V) ⊆ B := by
          intro z hz
          rcases mem_insert.mp hz with rfl | hzv
          · exact huB
          · rw [mem_singleton.mp hzv]; exact hvB
        have hc := Finset.card_le_card hsub
        rw [card_pair hu₀_ne_v₀] at hc
        exact hc
      have hB_card : #B = Fintype.card V - #A := by
        rw [card_sdiff_of_subset (subset_univ A), card_univ]
      have hA_ge2 : 2 ≤ #A := by omega
      -- Since `G₁[A]` is a tree on `#A ≥ 2` vertices, `#(G₁.induce A).edgeFinset = #A - 1 ≥ 1`,
      -- so `A` contains an edge `a₁ ~ a₂` in `G₁`! Together with `u₀ ~ v₀` in `G` and cross edges,
      -- `{a₁, a₂, u₀, v₀}` is a `K_4` in `G`!
      have hTree_edges : #(G₁.induce (A : Set V)).edgeFinset + 1 = #A := by
        simpa using hTree.card_edgeFinset
      have hEdge_pos : 0 < #(G₁.induce (A : Set V)).edgeFinset := by omega
      obtain ⟨e, he⟩ := Finset.card_pos.mp hEdge_pos
      induction e using Sym2.inductionOn with
      | hf a₁ a₂ =>
        have ha12 : G₁.Adj a₁.1 a₂.1 := (G₁.induce (A : Set V)).mem_edgeFinset.mp he
        have ha₁A : a₁.1 ∈ A := Finset.mem_coe.mp a₁.2
        have ha₂A : a₂.1 ∈ A := Finset.mem_coe.mp a₂.2
        left
        exact containsK4_of_clique4 a₁.1 a₂.1 u₀ v₀
          (hle ha12)
          (hle (hCross a₁.1 ha₁A u₀ huA))
          (hle (hCross a₁.1 ha₁A v₀ hvA))
          (hle (hCross a₂.1 ha₂A u₀ huA))
          (hle (hCross a₂.1 ha₂A v₀ hvA))
          h_adjG

/-- Exact-edge Simonovits–Cambie stability theorem indexed by `n = Fintype.card V`:
every graph on `n ≥ 1` vertices with `#G.edgeFinset = extremalEdges n` either contains `K_4` or
some `B_l` (`l ≥ 3`), or is a balanced tree-join `T_a ∨ b K_1`. -/
private lemma simonovits_exact_aux :
    ∀ n : ℕ, 1 ≤ n →
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = n →
        #G.edgeFinset = extremalEdges n →
        ContainsK4OrBipyramid G ∨ IsBalancedTreeJoin G := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn V _ _ G _ hcard hedges
    by_cases hn1 : n = 1
    · -- Base case `n = 1`
      subst hn1
      right
      refine ⟨univ, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hcard]
      · simp [hcard]
      · simp [hcard]
      · rw [SimpleGraph.isTree_iff_connected_and_card]
        have : Nonempty ((univ : Finset V) : Set V) := by
          have hpos : 0 < #(univ : Finset V) := by simp [hcard]
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
          exact ⟨⟨v, Finset.mem_coe.mpr hv⟩⟩
        have hv_c : Fintype.card ((univ : Finset V) : Set V) = 1 := by
          simpa using hcard
        have hsub : Subsingleton ((univ : Finset V) : Set V) :=
          Fintype.card_le_one_iff_subsingleton.mp (by omega)
        refine ⟨SimpleGraph.Connected.mk fun u v => ?_, ?_⟩
        · rw [Subsingleton.elim u v]
        · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          have he_c : Fintype.card (G.induce ((univ : Finset V) : Set V)).edgeSet = 0 := by
            rw [SimpleGraph.card_edgeSet]
            have hle := (G.induce ((univ : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
            rw [hv_c] at hle
            have hc2 : Nat.choose 1 2 = 0 := by decide
            omega
          change Fintype.card (G.induce ((univ : Finset V) : Set V)).edgeSet + 1 =
            Fintype.card ((univ : Finset V) : Set V)
          omega
      · intro b₁ hb₁
        exact False.elim (hb₁ (mem_univ b₁))
      · intro _ _ b hb
        exact False.elim (hb (mem_univ b))
    · -- Inductive step `n ≥ 2`
      have hn2 : 2 ≤ n := by omega
      -- Choose a vertex `x` of degree `≤ (n + 1) / 2`
      obtain ⟨x, hx_deg⟩ := exists_vertex_degree_le_half_succ G (by omega) (by rw [hcard, hedges])
      rw [hcard] at hx_deg
      -- Induced subgraph `G' := G.induce {x}ᶜ` on `n - 1` vertices
      let W := ({x}ᶜ : Set V)
      let G' : SimpleGraph W := G.induce W
      have hW_card : Fintype.card W = n - 1 := by
        rw [Fintype.card_compl_set, hcard]
        have hsing : Fintype.card ({x} : Set V) = 1 := Fintype.card_ofSubsingleton ⟨x, rfl⟩
        rw [hsing]
      have hG'_edges : #G'.edgeFinset = #G.edgeFinset - G.degree x := by
        rw [G.card_edgeFinset_induce_compl_singleton x, G.card_edgeFinset_deleteIncidenceSet x]
      have hstep := extremalEdges_step hn2
      have hG'_ge : extremalEdges (n - 1) ≤ #G'.edgeFinset := by omega
      -- If `#G'.edgeFinset > extremalEdges (n - 1)`, peel edges in `G'` via `deleteEdges`!
      by_cases hG'_gt : extremalEdges (n - 1) < #G'.edgeFinset
      · obtain ⟨E₀, hE₀_sub, hE₀_card⟩ :=
          Finset.exists_subset_card_eq (s := G'.edgeFinset) (n := extremalEdges (n - 1) + 1) (by omega)
        obtain ⟨e₀, he₀⟩ := Finset.card_pos.mp (by omega : 0 < #E₀)
        let E₁ := E₀.erase e₀
        let S_del : Finset (Sym2 W) := G'.edgeFinset \ E₁
        let G₁' : SimpleGraph W := G'.deleteEdges (S_del : Set (Sym2 W))
        have hE₁_sub_G' : E₁ ⊆ G'.edgeFinset := (erase_subset e₀ E₀).trans hE₀_sub
        have hG₁'_le : G₁' ≤ G' := G'.deleteEdges_le _
        classical
        have hG₁'_finset : G₁'.edgeFinset = E₁ := by
          rw [SimpleGraph.edgeFinset_deleteEdges]
          exact Finset.sdiff_sdiff_eq_self hE₁_sub_G'
        have hG₁'_edges : #G₁'.edgeFinset = extremalEdges (n - 1) := by
          rw [hG₁'_finset, Finset.card_erase_of_mem he₀, hE₀_card]
          omega
        rcases ih (n - 1) (by omega) (by omega) G₁' hW_card hG₁'_edges with hSub | hBTJ'
        · left
          exact ContainsK4OrBipyramid.of_copy
            ((SimpleGraph.Copy.induce G W).comp (SimpleGraph.Copy.ofLE G₁' G' hG₁'_le)) hSub
        · -- `e₀ ∈ E₀ ⊆ G'.edgeFinset` is in `G'` but NOT in `G₁'`!
          induction e₀ using Sym2.inductionOn with
          | hf u₀ v₀ =>
            have hadj_G' : G'.Adj u₀ v₀ := G'.mem_edgeFinset.mp (hE₀_sub he₀)
            have hnot_G₁' : ¬ G₁'.Adj u₀ v₀ := by
              intro hadj₁
              have hmem₁ : s(u₀, v₀) ∈ G₁'.edgeFinset := G₁'.mem_edgeFinset.mpr hadj₁
              rw [hG₁'_finset] at hmem₁
              exact notMem_erase s(u₀, v₀) E₀ hmem₁
            left
            exact ContainsK4OrBipyramid.of_copy (SimpleGraph.Copy.induce G W)
              (contains_of_balancedTreeJoin_and_extra_edge hG₁'_le hBTJ' hnot_G₁' hadj_G')
      · -- `#G'.edgeFinset = extremalEdges (n - 1)` AND `G.degree x = (n + 1) / 2`!
        have hG'_eq : #G'.edgeFinset = extremalEdges (n - 1) := by omega
        have hx_eq : G.degree x = (n + 1) / 2 := by omega
        rcases ih (n - 1) (by omega) (by omega) G' hW_card hG'_eq with hSub | hBTJ'
        · left
          exact ContainsK4OrBipyramid.of_copy (SimpleGraph.Copy.induce G W) hSub
        · -- Unpack `G' = T_{a'} ∨ b' K_1` on `W = {x}ᶜ` and lift `A'` and `B'` to `Finset V`!
          rcases hBTJ' with ⟨A_W, hAW1, hW_le1, hW_le2, hTree_W, hBW_indep, hW_cross⟩
          let embW : W ↪ V := Function.Embedding.subtype _
          let A' : Finset V := A_W.map embW
          let B' : Finset V := (univ \ A_W).map embW
          have hx_not_A' : x ∉ A' := by
            intro hx
            rcases mem_map.mp hx with ⟨w, _, heq⟩
            have hwx : w.1 = x := heq
            exact w.2 hwx
          have hx_not_B' : x ∉ B' := by
            intro hx
            rcases mem_map.mp hx with ⟨w, _, heq⟩
            have hwx : w.1 = x := heq
            exact w.2 hwx
          have hdisj_AB : Disjoint A' B' := by
            rw [Finset.disjoint_left]
            intro z hzA hzB
            rcases mem_map.mp hzA with ⟨w₁, hw₁, heq₁⟩
            rcases mem_map.mp hzB with ⟨w₂, hw₂, heq₂⟩
            have hw_eq : w₁ = w₂ := embW.injective (heq₁.trans heq₂.symm)
            rw [hw_eq] at hw₁
            exact (mem_sdiff.mp hw₂).2 hw₁
          have hpart_V : insert x (A' ∪ B') = univ := by
            ext z
            simp only [mem_insert, mem_union, mem_univ, iff_true]
            by_cases hzx : z = x
            · exact Or.inl hzx
            · right
              let zw : W := ⟨z, hzx⟩
              by_cases hzw : zw ∈ A_W
              · exact Or.inl (mem_map.mpr ⟨zw, hzw, rfl⟩)
              · exact Or.inr (mem_map.mpr ⟨zw, mem_sdiff.mpr ⟨mem_univ _, hzw⟩, rfl⟩)
          have hcard_A' : #A' = #A_W := card_map _
          have hcard_B' : #B' = (n - 1) - #A_W := by
            rw [card_map, card_sdiff_of_subset (subset_univ A_W), card_univ, hW_card]
          have hTree_A' : (G.induce (A' : Set V)).IsTree := by
            let isoA : G'.induce (A_W : Set W) ≃g G.induce (A' : Set V) := {
              toFun := fun y => ⟨y.1.1, Finset.mem_coe.mpr (mem_map.mpr ⟨y.1, Finset.mem_coe.mp y.2, rfl⟩)⟩
              invFun := fun z =>
                have hzx : z.1 ≠ x := fun h => hx_not_A' (h ▸ Finset.mem_coe.mp z.2)
                ⟨⟨z.1, hzx⟩, by
                  rcases mem_map.mp (Finset.mem_coe.mp z.2) with ⟨w, hw, heq⟩
                  have hw_eq : w = ⟨z.1, hzx⟩ := Subtype.ext heq
                  exact Finset.mem_coe.mpr (hw_eq ▸ hw)⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
              map_rel_iff' := Iff.rfl
            }
            exact isoA.isTree_iff.mp hTree_W
          have hB'_indep : ∀ b₁ ∈ B', ∀ b₂ ∈ B', ¬ G.Adj b₁ b₂ := by
            intro b₁ hb₁ b₂ hb₂ hadj
            rcases mem_map.mp hb₁ with ⟨w₁, hw₁, rfl⟩
            rcases mem_map.mp hb₂ with ⟨w₂, hw₂, rfl⟩
            exact hBW_indep w₁ (mem_sdiff.mp hw₁).2 w₂ (mem_sdiff.mp hw₂).2 hadj
          have hAB'_cross : ∀ a ∈ A', ∀ b ∈ B', G.Adj a b := by
            intro a ha b hb
            rcases mem_map.mp ha with ⟨w₁, hw₁, rfl⟩
            rcases mem_map.mp hb with ⟨w₂, hw₂, rfl⟩
            exact hW_cross w₁ hw₁ w₂ (mem_sdiff.mp hw₂).2
          -- Split `G.neighborFinset x` into `NA ⊆ A'` and `NB ⊆ B'`
          let NA := A'.filter (G.Adj x ·)
          let NB := B'.filter (G.Adj x ·)
          have hNA_sub : NA ⊆ A' := filter_subset _ _
          have hNB_sub : NB ⊆ B' := filter_subset _ _
          have hdeg_split : #NA + #NB = (n + 1) / 2 := by
            have hdisj_N : Disjoint NA NB := hdisj_AB.mono hNA_sub hNB_sub
            have hunion_N : NA ∪ NB = G.neighborFinset x := by
              ext z
              simp only [NA, NB, mem_union, mem_filter, SimpleGraph.mem_neighborFinset]
              constructor
              · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
              · intro hadj
                have hzx : z ≠ x := hadj.ne'
                have hmem : z ∈ insert x (A' ∪ B') := by rw [hpart_V]; exact mem_univ z
                rcases mem_insert.mp hmem with rfl | hAB
                · exact False.elim (hzx rfl)
                · rcases mem_union.mp hAB with hzA | hzB
                  · exact Or.inl ⟨hzA, hadj⟩
                  · exact Or.inr ⟨hzB, hadj⟩
            rw [← card_union_of_disjoint hdisj_N, hunion_N,
              SimpleGraph.card_neighborFinset_eq_degree, hx_eq]
          have hp_le : #NA ≤ #A' := card_le_card hNA_sub
          have hq_le : #NB ≤ #B' := card_le_card hNB_sub
          rw [hW_card] at hW_le1 hW_le2
          -- Now run the 4 exhaustive attachment cases of Cambie–Simonovits!
          -- Note first: `#NA ≥ 1` ALWAYS holds by arithmetic!
          have hp_ge1 : 1 ≤ #NA := by omega
          by_cases hcase_a : 2 ≤ #NA ∧ 2 ≤ #NB
          · -- Case (a): `#NA ≥ 2` and `#NB ≥ 2` -> `K_4` or `bipyramidGraph l` (`l ≥ 3`)!
            left
            obtain ⟨u₁, hu₁, u₂, hu₂, hu_ne⟩ := Finset.one_lt_card.mp (by omega : 1 < #NA)
            obtain ⟨v₁, hv₁, v₂, hv₂, hv_ne⟩ := Finset.one_lt_card.mp (by omega : 1 < #NB)
            have hu₁A : u₁ ∈ A' := (mem_filter.mp hu₁).1
            have hu₂A : u₂ ∈ A' := (mem_filter.mp hu₂).1
            have hx_u₁ : G.Adj x u₁ := (mem_filter.mp hu₁).2
            have hx_u₂ : G.Adj x u₂ := (mem_filter.mp hu₂).2
            have hv₁B : v₁ ∈ B' := (mem_filter.mp hv₁).1
            have hv₂B : v₂ ∈ B' := (mem_filter.mp hv₂).1
            have hx_v₁ : G.Adj x v₁ := (mem_filter.mp hv₁).2
            have hx_v₂ : G.Adj x v₂ := (mem_filter.mp hv₂).2
            by_cases hu12_adj : G.Adj u₁ u₂
            · -- `{x, u₁, u₂, v₁}` is a `K_4`!
              exact Or.inl (containsK4_of_clique4 x u₁ u₂ v₁
                hx_u₁ hx_u₂ hx_v₁
                hu12_adj (hAB'_cross u₁ hu₁A v₁ hv₁B) (hAB'_cross u₂ hu₂A v₁ hv₁B))
            · -- `u₁` and `u₂` are non-adjacent in `T_{a'}`, so `T_{a'} + x` has a cycle `C_l` (`l ≥ 4`)
              -- inside `insert x A'`, and both `v₁, v₂ ∈ B'` are adjacent to every vertex of `insert x A'`!
              obtain ⟨l, hl3, c, hc_mem, hc_next, hc_close⟩ :=
                exists_cycle_of_nonadj_in_tree G A' x u₁ u₂
                  hx_not_A' hu₁A hu₂A hu_ne hu12_adj hx_u₁ hx_u₂ hTree_A'
              refine Or.inr ⟨l, hl3, containsBipyramid_of_cycle_and_apices c hc_next
                (fun _ => hc_close) v₁ v₂ hv_ne ?_ ?_ ?_ ?_⟩
              · intro i heq
                rcases mem_insert.mp (hc_mem i) with hcx | hcA
                · have hxv₁ : x = v₁ := hcx.symm.trans heq
                  exact hx_not_B' (hxv₁ ▸ hv₁B)
                · exact Finset.disjoint_left.mp hdisj_AB hcA (heq ▸ hv₁B)
              · intro i heq
                rcases mem_insert.mp (hc_mem i) with hcx | hcA
                · have hxv₂ : x = v₂ := hcx.symm.trans heq
                  exact hx_not_B' (hxv₂ ▸ hv₂B)
                · exact Finset.disjoint_left.mp hdisj_AB hcA (heq ▸ hv₂B)
              · intro i
                rcases mem_insert.mp (hc_mem i) with hcx | hcA
                · rw [hcx]; exact hx_v₁
                · exact hAB'_cross (c i) hcA v₁ hv₁B
              · intro i
                rcases mem_insert.mp (hc_mem i) with hcx | hcA
                · rw [hcx]; exact hx_v₂
                · exact hAB'_cross (c i) hcA v₂ hv₂B
          · -- `¬ (2 ≤ #NA ∧ 2 ≤ #NB)`: since `#NA ≥ 1`, either `#NA = 1` or `#NB ≤ 1`!
            by_cases hp1 : #NA = 1
            · -- Case (c): `#NA = 1`! By arithmetic, `#NB = #B'` AND `0 ≤ (#A' + 1) - #B' ≤ 2`!
              have hq_eq : #NB = #B' := by omega
              have hNB_eq_B' : NB = B' := Finset.eq_of_subset_of_card_le hNB_sub (by omega)
              obtain ⟨u, hu_sing⟩ := Finset.card_eq_one.mp hp1
              have hu_NA : u ∈ NA := by rw [hu_sing]; exact mem_singleton_self u
              have huA : u ∈ A' := (mem_filter.mp hu_NA).1
              have hx_u : G.Adj x u := (mem_filter.mp hu_NA).2
              have hx_only_u : ∀ a ∈ A', G.Adj x a → a = u := by
                intro a ha hadj
                have ha_NA : a ∈ NA := mem_filter.mpr ⟨ha, hadj⟩
                rw [hu_sing] at ha_NA
                exact mem_singleton.mp ha_NA
              right
              refine ⟨insert x A', ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [card_insert_of_notMem hx_not_A']; omega
              · rw [card_insert_of_notMem hx_not_A', hcard]; omega
              · rw [card_insert_of_notMem hx_not_A', hcard]; omega
              · exact isTree_induce_insert_leaf G A' x u hx_not_A' huA hTree_A' hx_u hx_only_u
              · intro b₁ hb₁ b₂ hb₂
                have hb₁_B : b₁ ∈ B' := by
                  have hm : b₁ ∈ insert x (A' ∪ B') := by rw [hpart_V]; exact mem_univ _
                  rcases mem_insert.mp hm with hbx | hAB
                  · exact False.elim (hb₁ (hbx ▸ mem_insert_self x A'))
                  · rcases mem_union.mp hAB with hA | hB
                    · exact False.elim (hb₁ (mem_insert_of_mem hA))
                    · exact hB
                have hb₂_B : b₂ ∈ B' := by
                  have hm : b₂ ∈ insert x (A' ∪ B') := by rw [hpart_V]; exact mem_univ _
                  rcases mem_insert.mp hm with hbx | hAB
                  · exact False.elim (hb₂ (hbx ▸ mem_insert_self x A'))
                  · rcases mem_union.mp hAB with hA | hB
                    · exact False.elim (hb₂ (mem_insert_of_mem hA))
                    · exact hB
                exact hB'_indep b₁ hb₁_B b₂ hb₂_B
              · intro a ha b hb
                have hb_B : b ∈ B' := by
                  have hm : b ∈ insert x (A' ∪ B') := by rw [hpart_V]; exact mem_univ _
                  rcases mem_insert.mp hm with hbx | hAB
                  · exact False.elim (hb (hbx ▸ mem_insert_self x A'))
                  · rcases mem_union.mp hAB with hA | hB
                    · exact False.elim (hb (mem_insert_of_mem hA))
                    · exact hB
                rcases mem_insert.mp ha with rfl | haA
                · have hb_NB : b ∈ NB := by rwa [hNB_eq_B']
                  exact (mem_filter.mp hb_NB).2
                · exact hAB'_cross a haA b hb_B
            · -- Here `2 ≤ #NA` and `¬ (2 ≤ #NA ∧ 2 ≤ #NB)`, so `#NB ≤ 1`!
              have hq_le1 : #NB ≤ 1 := by omega
              by_cases hq0 : #NB = 0
              · -- Case (d): `#NB = 0`! By arithmetic, `#NA = #A'` and `G = T_{a'} ∨ (b' + 1) K_1`!
                have hp_eq : #NA = #A' := by omega
                have hNA_eq_A' : NA = A' := Finset.eq_of_subset_of_card_le hNA_sub (by omega)
                have hNB_empty : NB = ∅ := Finset.card_eq_zero.mp hq0
                right
                refine ⟨A', ?_, ?_, ?_, hTree_A', ?_, ?_⟩
                · omega
                · rw [hcard]; omega
                · rw [hcard]; omega
                · intro b₁ hb₁ b₂ hb₂ hadj
                  have h1_or : b₁ = x ∨ b₁ ∈ B' := by
                    have hm : b₁ ∈ insert x (A' ∪ B') := by rw [hpart_V]; exact mem_univ _
                    rcases mem_insert.mp hm with rfl | hAB
                    · exact Or.inl rfl
                    · rcases mem_union.mp hAB with hA | hB
                      · exact False.elim (hb₁ hA)
                      · exact Or.inr hB
                  have h2_or : b₂ = x ∨ b₂ ∈ B' := by
                    have hm : b₂ ∈ insert x (A' ∪ B') := by rw [hpart_V]; exact mem_univ _
                    rcases mem_insert.mp hm with rfl | hAB
                    · exact Or.inl rfl
                    · rcases mem_union.mp hAB with hA | hB
                      · exact False.elim (hb₂ hA)
                      · exact Or.inr hB
                  rcases h1_or with rfl | hb₁B
                  · rcases h2_or with rfl | hb₂B
                    · exact hadj.ne rfl
                    · have hmem : b₂ ∈ NB := mem_filter.mpr ⟨hb₂B, hadj⟩
                      rw [hNB_empty] at hmem
                      exact notMem_empty _ hmem
                  · rcases h2_or with rfl | hb₂B
                    · have hmem : b₁ ∈ NB := mem_filter.mpr ⟨hb₁B, hadj.symm⟩
                      rw [hNB_empty] at hmem
                      exact notMem_empty _ hmem
                    · exact hB'_indep b₁ hb₁B b₂ hb₂B hadj
                · intro a ha b hb
                  have hb_or : b = x ∨ b ∈ B' := by
                    have hm : b ∈ insert x (A' ∪ B') := by rw [hpart_V]; exact mem_univ _
                    rcases mem_insert.mp hm with rfl | hAB
                    · exact Or.inl rfl
                    · rcases mem_union.mp hAB with hA | hB
                      · exact False.elim (hb hA)
                      · exact Or.inr hB
                  rcases hb_or with rfl | hbB
                  · have ha_NA : a ∈ NA := by rwa [hNA_eq_A']
                    exact (mem_filter.mp ha_NA).2.symm
                  · exact hAB'_cross a ha b hbB
              · -- Case (b): `#NB = 1` and `2 ≤ #NA`!
                have hq1 : #NB = 1 := by omega
                obtain ⟨v, hv_sing⟩ := Finset.card_eq_one.mp hq1
                have hv_NB : v ∈ NB := by rw [hv_sing]; exact mem_singleton_self v
                have hvB : v ∈ B' := (mem_filter.mp hv_NB).1
                have hxv : G.Adj x v := (mem_filter.mp hv_NB).2
                have hx_only_v : ∀ b ∈ B', G.Adj x b → b = v := by
                  intro b hb hadj
                  have hb_NB : b ∈ NB := mem_filter.mpr ⟨hb, hadj⟩
                  rw [hv_sing] at hb_NB
                  exact mem_singleton.mp hb_NB
                -- Check whether `#NA = #A'` or `#NA = #A' - 1`!
                have hp_cases : #NA = #A' ∨ #NA + 1 = #A' := by omega
                rcases hp_cases with hp_all | hp_miss1
                · -- Subcase (b1): `#NA = #A'` (`x` is adjacent to ALL of `A'` AND to `v ∈ B'`).
                  -- Since `2 ≤ #NA = #A'`, the tree `G[A']` has `#A' - 1 ≥ 1` edges, so there is
                  -- an edge `u₁ ~ u₂` in `A'`; then `{x, v, u₁, u₂}` is a `K_4`!
                  left
                  have hNA_eq_A' : NA = A' := Finset.eq_of_subset_of_card_le hNA_sub (by omega)
                  have hTree_edges : #(G.induce (A' : Set V)).edgeFinset + 1 = #A' := by
                    simpa using hTree_A'.card_edgeFinset
                  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < #(G.induce (A' : Set V)).edgeFinset)
                  induction e using Sym2.inductionOn with
                  | hf u₁ u₂ =>
                    have hu12 : G.Adj u₁.1 u₂.1 := (G.induce (A' : Set V)).mem_edgeFinset.mp he
                    have hu₁A : u₁.1 ∈ A' := Finset.mem_coe.mp u₁.2
                    have hu₂A : u₂.1 ∈ A' := Finset.mem_coe.mp u₂.2
                    have hu₁_NA : u₁.1 ∈ NA := by rwa [hNA_eq_A']
                    have hu₂_NA : u₂.1 ∈ NA := by rwa [hNA_eq_A']
                    have hxu₁ : G.Adj x u₁.1 := (mem_filter.mp hu₁_NA).2
                    have hxu₂ : G.Adj x u₂.1 := (mem_filter.mp hu₂_NA).2
                    exact Or.inl (containsK4_of_clique4 x v u₁.1 u₂.1
                      hxv hxu₁ hxu₂
                      (hAB'_cross u₁.1 hu₁A v hvB).symm (hAB'_cross u₂.1 hu₂A v hvB).symm
                      hu12)
                · -- Subcase (b2): `#NA + 1 = #A'` (`x` misses a unique vertex `u ∈ A' \ NA`)!
                  have hdiff_card : #(A' \ NA) = 1 := by
                    rw [card_sdiff_of_subset hNA_sub]; omega
                  obtain ⟨u, hu_sing⟩ := Finset.card_eq_one.mp hdiff_card
                  have hu_diff : u ∈ A' \ NA := by rw [hu_sing]; exact mem_singleton_self u
                  have huA : u ∈ A' := (mem_sdiff.mp hu_diff).1
                  have hu_not_NA : u ∉ NA := (mem_sdiff.mp hu_diff).2
                  have hnot_xu : ¬ G.Adj x u := fun h => hu_not_NA (mem_filter.mpr ⟨huA, h⟩)
                  have hx_adj_other : ∀ y ∈ A', y ≠ u → G.Adj x y := by
                    intro y hy hy_ne
                    by_contra hnot
                    have hy_diff : y ∈ A' \ NA :=
                      mem_sdiff.mpr ⟨hy, fun hmem => hnot (mem_filter.mp hmem).2⟩
                    rw [hu_sing] at hy_diff
                    exact hy_ne (mem_singleton.mp hy_diff)
                  -- If ANY two vertices `y, z ∈ A' \ {u}` are adjacent in `G`, `{x, v, y, z}` is `K_4`!
                  by_cases hEdge_in_NA : ∃ y ∈ A', y ≠ u ∧ ∃ z ∈ A', z ≠ u ∧ G.Adj y z
                  · left
                    rcases hEdge_in_NA with ⟨y, hyA, hy_ne, z, hzA, hz_ne, hyz⟩
                    exact Or.inl (containsK4_of_clique4 x v y z
                      hxv (hx_adj_other y hyA hy_ne) (hx_adj_other z hzA hz_ne)
                      (hAB'_cross y hyA v hvB).symm (hAB'_cross z hzA v hvB).symm hyz)
                  · -- Otherwise `A' \ {u}` is an independent set!
                    -- By `star_of_tree_compl_indep`, `G[A']` is a star centered at `u`!
                    -- Flip partition to `S := insert x (insert u B')` (broom tree) and `I := A' \ {u}`!
                    have hIndep_NA : ∀ y ∈ A', y ≠ u → ∀ z ∈ A', z ≠ u → ¬ G.Adj y z := by
                      intro y hy hy_ne z hz hz_ne hyz
                      exact hEdge_in_NA ⟨y, hy, hy_ne, z, hz, hz_ne, hyz⟩
                    have hStar_u : ∀ y ∈ A', y ≠ u → G.Adj y u :=
                      star_of_tree_compl_indep G A' u huA hTree_A' hIndep_NA
                    right
                    let S := insert x (insert u B')
                    have hu_not_B' : u ∉ B' := Finset.disjoint_left.mp hdisj_AB huA
                    have hxu_ne : x ≠ u := fun h => hx_not_A' (h ▸ huA)
                    have hx_not_uB : x ∉ insert u B' := by simp [hxu_ne, hx_not_B']
                    have hS_card : #S = #B' + 2 := by
                      dsimp [S]
                      rw [card_insert_of_notMem hx_not_uB, card_insert_of_notMem hu_not_B']
                    -- Helper characterizing `z ∉ S ↔ z ∈ A' ∧ z ≠ u`
                    have h_not_S_iff : ∀ z : V, z ∉ S ↔ (z ∈ A' ∧ z ≠ u) := by
                      intro z
                      constructor
                      · intro hz_not
                        have hm : z ∈ insert x (A' ∪ B') := by rw [hpart_V]; exact mem_univ z
                        rcases mem_insert.mp hm with hzx | hAB
                        · exact False.elim (hz_not (hzx ▸ mem_insert_self x _))
                        · rcases mem_union.mp hAB with hzA | hzB
                          · refine ⟨hzA, ?_⟩
                            intro hzu
                            exact hz_not (mem_insert_of_mem (hzu ▸ mem_insert_self u B'))
                          · exact False.elim (hz_not (mem_insert_of_mem (mem_insert_of_mem hzB)))
                      · rintro ⟨hzA, hzu⟩ hzS
                        rcases mem_insert.mp hzS with hzx | hz_uB
                        · exact hx_not_A' (hzx ▸ hzA)
                        · rcases mem_insert.mp hz_uB with hzu' | hzB
                          · exact hzu hzu'
                          · exact Finset.disjoint_left.mp hdisj_AB hzA hzB
                    refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · rw [hS_card]; omega
                    · rw [hS_card, hcard]; omega
                    · rw [hS_card, hcard]; omega
                    · exact isTree_broom G B' u v x hu_not_B' hvB hx_not_B' hxu_ne
                        hB'_indep (fun b hb => hAB'_cross u huA b hb) hxv hx_only_v hnot_xu
                    · intro y₁ hy₁ y₂ hy₂
                      rcases (h_not_S_iff y₁).mp hy₁ with ⟨hy₁A, hy₁u⟩
                      rcases (h_not_S_iff y₂).mp hy₂ with ⟨hy₂A, hy₂u⟩
                      exact hIndep_NA y₁ hy₁A hy₁u y₂ hy₂A hy₂u
                    · intro s hs y hy
                      rcases (h_not_S_iff y).mp hy with ⟨hyA, hyu⟩
                      rcases mem_insert.mp hs with rfl | hs_uB
                      · exact hx_adj_other y hyA hyu
                      · rcases mem_insert.mp hs_uB with rfl | hsB
                        · exact (hStar_u y hyA hyu).symm
                        · exact (hAB'_cross y hyA s hsB).symm

/-- **Simonovits–Cambie Extremal Stability Theorem**:
Every simple graph `G` on `n ≥ 1` vertices with `#G.edgeFinset ≥ ⌊n²/4⌋ + ⌊(n-1)/2⌋` either
contains `K_4` or a bipyramid `B_l = C_l ∨ 2K_1` (`l ≥ 3`), or else has exact edge count
`⌊n²/4⌋ + ⌊(n-1)/2⌋` and is a balanced tree-join `T_a ∨ b K_1`. -/
theorem simonovits_stability {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 1 ≤ Fintype.card V)
    (hedges : extremalEdges (Fintype.card V) ≤ #G.edgeFinset) :
    ContainsK4OrBipyramid G ∨
      (#G.edgeFinset = extremalEdges (Fintype.card V) ∧ IsBalancedTreeJoin G) := by
  set n := Fintype.card V
  by_cases hgt : extremalEdges n < #G.edgeFinset
  · left
    obtain ⟨E₀, hE₀_sub, hE₀_card⟩ :=
      Finset.exists_subset_card_eq (s := G.edgeFinset) (n := extremalEdges n + 1) (by omega)
    obtain ⟨e₀, he₀⟩ := Finset.card_pos.mp (by omega : 0 < #E₀)
    let E₁ := E₀.erase e₀
    let S_del : Finset (Sym2 V) := G.edgeFinset \ E₁
    let G₁ : SimpleGraph V := G.deleteEdges (S_del : Set (Sym2 V))
    have hE₁_sub_G : E₁ ⊆ G.edgeFinset := (erase_subset e₀ E₀).trans hE₀_sub
    have hG₁_le : G₁ ≤ G := G.deleteEdges_le _
    classical
    have hG₁_finset : G₁.edgeFinset = E₁ := by
      rw [SimpleGraph.edgeFinset_deleteEdges]
      exact Finset.sdiff_sdiff_eq_self hE₁_sub_G
    have hG₁_edges : #G₁.edgeFinset = extremalEdges n := by
      rw [hG₁_finset, Finset.card_erase_of_mem he₀, hE₀_card]
      omega
    rcases simonovits_exact_aux n hn G₁ rfl hG₁_edges with hSub | hBTJ
    · exact ContainsK4OrBipyramid.of_copy (SimpleGraph.Copy.ofLE G₁ G hG₁_le) hSub
    · induction e₀ using Sym2.inductionOn with
      | hf u₀ v₀ =>
        have hadj_G : G.Adj u₀ v₀ := G.mem_edgeFinset.mp (hE₀_sub he₀)
        have hnot_G₁ : ¬ G₁.Adj u₀ v₀ := by
          intro hadj₁
          have hmem₁ : s(u₀, v₀) ∈ G₁.edgeFinset := G₁.mem_edgeFinset.mpr hadj₁
          rw [hG₁_finset] at hmem₁
          exact notMem_erase s(u₀, v₀) E₀ hmem₁
        exact contains_of_balancedTreeJoin_and_extra_edge hG₁_le hBTJ hnot_G₁ hadj_G
  · have heq : #G.edgeFinset = extremalEdges n := by omega
    rcases simonovits_exact_aux n hn G rfl heq with hSub | hBTJ
    · exact Or.inl hSub
    · exact Or.inr ⟨heq, hBTJ⟩

/-- **Simonovits Structural Theorem (`≥` threshold, all `n : ℕ`)**:
For every finite vertex type `V` (no `[Nonempty V]` assumption needed!) and every `G : SimpleGraph V`
with `G.edgeSet.ncard ≥ ⌊n²/4⌋ + ⌊(n+1)/2⌋` (`n = Fintype.card V`), either `n = 0` or `G` contains
`K_4` or a bipyramid `B_l` (`l ≥ 3`); in fact, for `n = 0`, `⌊0²/4⌋ + ⌊1/2⌋ = 0`, whereas for all
`n ≥ 1` (and unconditionally whenever `4 ≤ n` or `1 ≤ G.edgeSet.ncard`), `G` contains `K_4` or
`B_l` (`l ≥ 3`). -/
theorem contains_k4_or_bipyramid_of_ge {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hn : 1 ≤ Fintype.card V)
    (hedges : saturationThreshold (Fintype.card V) ≤ G.edgeSet.ncard) :
    ContainsK4OrBipyramid G := by
  classical
  rw [ncard_edgeSet_eq_card_edgeFinset] at hedges
  have hsucc := saturationThreshold_eq_succ hn
  have hge : extremalEdges (Fintype.card V) ≤ #G.edgeFinset := by omega
  rcases simonovits_stability G hn hge with hSub | ⟨heq, _⟩
  · exact hSub
  · omega

end Erdos1019

