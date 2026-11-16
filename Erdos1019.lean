/-
Copyright 2026 Chucheng Xiang (@xccElephant).
SPDX-License-Identifier: Apache-2.0

Complete, unconditional, 100% clean-room Lean 4 formalization of **JSP-000849** (Erdős Problem
#1019, `[Er69c, p. 17]`, `[Er71, item 13, p. 102]`):

> A planar graph on `m` vertices with `3m - 6` edges is called *saturated*.
> Does every graph on `n` vertices with `⌊n²/4⌋ + ⌊(n + 1)/2⌋` edges contain a saturated planar
> subgraph on `> 3` vertices?

**Answer: Yes.** Every simple graph `G` on `n ≥ 1` vertices with at least (or, in particular,
exactly) `⌊n²/4⌋ + ⌊(n + 1)/2⌋` edges contains either `K_4` or a bipyramid `B_l = C_l ∨ 2K_1`
(`l ≥ 3`), both of which are topologically planar in `ℝ × ℝ` via continuous injective Jordan arcs
and have `m > 3` vertices and `3m - 6` edges.
-/
import Erdos1019.Planarity
import Erdos1019.Bipyramid
import Erdos1019.Extremal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos1019

open scoped SimpleGraph

/-- A finite simple graph `H` on `W` is a *saturated planar graph* (`[Er69c, p. 13]`,
`[Er71, p. 102]`) if `H` is topologically planar in `ℝ × ℝ`, has at least `3` vertices, and has
`3 * |W| - 6` edges. -/
def IsSaturatedPlanar {W : Type*} [Fintype W] (H : SimpleGraph W) : Prop :=
  IsPlanar H ∧ 3 ≤ Fintype.card W ∧ H.edgeSet.ncard = 3 * Fintype.card W - 6

/-- `K_4` (`⊤ : SimpleGraph (Fin 4)`) is a saturated planar graph on `4 > 3` vertices. -/
theorem completeGraph_fin4_isSaturatedPlanar :
    IsSaturatedPlanar (⊤ : SimpleGraph (Fin 4)) :=
  ⟨completeGraph_fin4_isPlanar, by decide, completeGraph_fin4_ncard_edgeSet⟩

/-- Every bipyramid `B_l = C_l ∨ 2K_1` (`l ≥ 3`) is a saturated planar graph on `l + 2 > 3`
vertices. -/
theorem bipyramidGraph_isSaturatedPlanar {l : ℕ} (hl : 3 ≤ l) :
    IsSaturatedPlanar (bipyramidGraph l) :=
  ⟨bipyramidGraph_isPlanar hl, by rw [card_bipyramidVert]; omega, bipyramidGraph_ncard_edgeSet hl⟩

/-- Any graph `H` isomorphic to `G'` inherits `IsSaturatedPlanar`. -/
theorem IsSaturatedPlanar.of_iso {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂} (e : H₁ ≃g H₂)
    (h₁ : IsSaturatedPlanar H₁) : IsSaturatedPlanar H₂ := by
  rcases h₁ with ⟨hplan, hcard3, hedges⟩
  have hcard_eq : Fintype.card W₁ = Fintype.card W₂ := Fintype.card_congr e.toEquiv
  have hedges_eq : H₁.edgeSet.ncard = H₂.edgeSet.ncard := by
    classical
    rw [ncard_edgeSet_eq_card_edgeFinset, ncard_edgeSet_eq_card_edgeFinset,
      ← SimpleGraph.card_edgeSet, ← SimpleGraph.card_edgeSet]
    exact Fintype.card_congr e.mapEdgeSet
  exact ⟨IsPlanar.of_copy e.symm.toCopy hplan, hcard_eq ▸ hcard3, by omega⟩

/-- Converting a contained copy `K_4 ⊑ G` or `B_l ⊑ G` (`l ≥ 3`) into a concrete `G.Subgraph`
on `> 3` vertices whose coerced simple graph is topologically planar and saturated (`3m - 6`
edges), staying in the same universe `u` as `V`! -/
theorem exists_saturated_planar_subgraph_of_contains {V : Type*} [Fintype V]
    {G : SimpleGraph V} (h : ContainsK4OrBipyramid G) :
    ∃ H : G.Subgraph, ∃ _ : Fintype H.verts,
      3 < @Fintype.card H.verts ‹_› ∧ @IsSaturatedPlanar H.verts ‹_› H.coe := by
  classical
  rcases h with hk4 | ⟨l, hl, hbip⟩
  · rcases hk4 with ⟨f⟩
    refine ⟨f.toSubgraph, inferInstance, ?_, ?_⟩
    · have hcard : Fintype.card f.toSubgraph.verts = 4 := by
        simpa using (Fintype.card_congr f.isoToSubgraph.toEquiv).symm
      omega
    · exact completeGraph_fin4_isSaturatedPlanar.of_iso f.isoToSubgraph
  · rcases hbip with ⟨f⟩
    refine ⟨f.toSubgraph, inferInstance, ?_, ?_⟩
    · have hcard : Fintype.card f.toSubgraph.verts = l + 2 := by
        have hc := (Fintype.card_congr f.isoToSubgraph.toEquiv).symm
        rwa [card_bipyramidVert] at hc
      omega
    · exact (bipyramidGraph_isSaturatedPlanar hl).of_iso f.isoToSubgraph

/-- **Erdős Problem #1019 (`≥` threshold, all `n ≥ 1`)**:
Every simple graph `G` on `n ≥ 1` vertices with at least `⌊n²/4⌋ + ⌊(n + 1)/2⌋` edges contains a
subgraph `H` on `m > 3` vertices that is topologically planar in `ℝ × ℝ` and has `3m - 6` edges. -/
theorem erdos_1019_ge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : 1 ≤ Fintype.card V)
    (hedges : (Fintype.card V) ^ 2 / 4 + (Fintype.card V + 1) / 2 ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, ∃ _ : Fintype H.verts,
      3 < @Fintype.card H.verts ‹_› ∧
      IsPlanar H.coe ∧
      H.coe.edgeSet.ncard = 3 * @Fintype.card H.verts ‹_› - 6 := by
  have hcont := contains_k4_or_bipyramid_of_ge G hn hedges
  obtain ⟨H, inst, hgt3, hplan, _, hsat⟩ := exists_saturated_planar_subgraph_of_contains hcont
  exact ⟨H, inst, hgt3, hplan, hsat⟩

/-- **Erdős Problem #1019 (`≥` threshold for `n ≥ 4`, zero extra premises)**:
For every finite vertex set `V` of size `n ≥ 4`, every graph `G` on `V` with at least
`⌊n²/4⌋ + ⌊(n + 1)/2⌋` edges contains a saturated planar subgraph on `> 3` vertices. -/
theorem erdos_1019_ge_of_four_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : 4 ≤ Fintype.card V)
    (hedges : (Fintype.card V) ^ 2 / 4 + (Fintype.card V + 1) / 2 ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, ∃ _ : Fintype H.verts,
      3 < @Fintype.card H.verts ‹_› ∧
      IsPlanar H.coe ∧
      H.coe.edgeSet.ncard = 3 * @Fintype.card H.verts ‹_› - 6 :=
  erdos_1019_ge G (by omega) hedges

/-- **Erdős Problem #1019 (exact `=` threshold, `[Er69c, p. 17]` / `[Er71, p. 102]`)**:
Every simple graph `G` on `n ≥ 1` vertices with *exactly* `⌊n²/4⌋ + ⌊(n + 1)/2⌋` edges contains a
saturated planar subgraph on `> 3` vertices (note: for `n ∈ {1, 2, 3}`, `⌊n²/4⌋ + ⌊(n+1)/2⌋ > C(n,2)`,
so `n ≥ 4` holds automatically whenever equality holds for `n ≥ 1`!). -/
theorem erdos_1019 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : 1 ≤ Fintype.card V)
    (hedges : G.edgeSet.ncard = (Fintype.card V) ^ 2 / 4 + (Fintype.card V + 1) / 2) :
    ∃ H : G.Subgraph, ∃ _ : Fintype H.verts,
      3 < @Fintype.card H.verts ‹_› ∧
      IsPlanar H.coe ∧
      H.coe.edgeSet.ncard = 3 * @Fintype.card H.verts ‹_› - 6 :=
  erdos_1019_ge G hn (le_of_eq hedges.symm)

/-- Canonical `Fin n` formulation of **Erdős Problem #1019** (`JSP-000849`) for all `n ≥ 1`
(both `≥` and `=` forms follow immediately; for `n = 0`, `⌊0²/4⌋ + ⌊1/2⌋ = 0` on `0` vertices
cannot contain `> 3` vertices, whereas for every `n ≥ 1`, every `G : SimpleGraph (Fin n)` with
`≥ ⌊n²/4⌋ + ⌊(n + 1)/2⌋` edges contains a saturated planar subgraph on `m > 3` vertices). -/
theorem erdos_1019_fin (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (hedges : n ^ 2 / 4 + (n + 1) / 2 ≤ G.edgeSet.ncard) :
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
      3 < m ∧ IsPlanar H ∧ H.edgeSet.ncard = 3 * m - 6 ∧ (H ⊑ G) := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hcont := contains_k4_or_bipyramid_of_ge G (by omega)
    (by unfold saturationThreshold; rw [hcard]; exact hedges)
  rcases hcont with hk4 | ⟨l, hl, hbip⟩
  · exact ⟨4, ⊤, by omega, completeGraph_fin4_isPlanar, completeGraph_fin4_ncard_edgeSet, hk4⟩
  · let eFin : BipyramidVert l ≃ Fin (l + 2) :=
      Fintype.equivOfCardEq (by rw [card_bipyramidVert, Fintype.card_fin])
    let H : SimpleGraph (Fin (l + 2)) := (bipyramidGraph l).map eFin.toEmbedding
    have hiso : bipyramidGraph l ≃g H := SimpleGraph.Iso.map eFin (bipyramidGraph l)
    have hsat : IsSaturatedPlanar H := (bipyramidGraph_isSaturatedPlanar hl).of_iso hiso
    rcases hsat with ⟨hplan, _, hncard⟩
    rw [Fintype.card_fin] at hncard
    exact ⟨l + 2, H, by omega, hplan, hncard, hiso.symm.isContained.trans hbip⟩

end Erdos1019
