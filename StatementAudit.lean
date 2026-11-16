/-
Copyright 2026 Chucheng Xiang (@xccElephant).
SPDX-License-Identifier: Apache-2.0

Independent first-principles statement audit and axiom verification for `Erdos1019` (`JSP-000849`).
Reconstructs graph subgraph containment, unordered edge counting, vertex cardinality `> 3`, and
Jordan-arc topological planarity in `ℝ × ℝ` directly from Mathlib primitives without referencing
any helper definitions from `Erdos1019`, proves logical equivalence and full-scope theorems for
both the exact `=` threshold (`[Er69c, p. 17]`, `[Er71, p. 102]`) and the `≥` threshold across
both `SimpleGraph V` and `SimpleGraph (Fin n)`, and audits transitive axioms via `#print axioms`.
-/
import Erdos1019

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace StatementAudit

/-! ### 1. Independent First-Principles Specification of `[Er69c]` / `[Er71, item 13]` -/

/-- Independent first-principles definition of Jordan-arc topological planarity in `ℝ × ℝ` for a
simple graph `H : SimpleGraph W`, written directly in terms of Mathlib's `SimpleGraph`, `Sym2`,
`Set.Icc (0 : ℝ) 1`, `Continuous`, and `Function.Injective` (using zero helper definitions from
`Erdos1019`). -/
def RawJordanPlanar {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ (pos : W → ℝ × ℝ),
    Function.Injective pos ∧
    ∃ (γ : ∀ e : Sym2 W, e ∈ H.edgeSet → Set.Icc (0 : ℝ) 1 → ℝ × ℝ),
      (∀ (e : Sym2 W) (he : e ∈ H.edgeSet), Continuous (γ e he)) ∧
      (∀ (e : Sym2 W) (he : e ∈ H.edgeSet), Function.Injective (γ e he)) ∧
      (∀ (u v : W) (huv : H.Adj u v),
        let he : s(u, v) ∈ H.edgeSet := H.mem_edgeSet.mpr huv
        (γ s(u, v) he ⟨0, ⟨le_rfl, zero_le_one⟩⟩ = pos u ∧
         γ s(u, v) he ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = pos v) ∨
        (γ s(u, v) he ⟨0, ⟨le_rfl, zero_le_one⟩⟩ = pos v ∧
         γ s(u, v) he ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = pos u)) ∧
      (∀ (e : Sym2 W) (he : e ∈ H.edgeSet) (t : Set.Icc (0 : ℝ) 1),
        (0 : ℝ) < t.1 → t.1 < 1 → ∀ w : W, γ e he t ≠ pos w) ∧
      (∀ (e₁ : Sym2 W) (he₁ : e₁ ∈ H.edgeSet) (e₂ : Sym2 W) (he₂ : e₂ ∈ H.edgeSet),
        e₁ ≠ e₂ → ∀ (t₁ t₂ : Set.Icc (0 : ℝ) 1),
          γ e₁ he₁ t₁ = γ e₂ he₂ t₂ →
            ((t₁.1 = 0 ∨ t₁.1 = 1) ∧ (t₂.1 = 0 ∨ t₂.1 = 1)))

/-- Independent first-principles unordered edge count on a finite vertex type `V`:
cardinality of `{e : Sym2 V | e ∈ G.edgeSet}`. -/
noncomputable def rawEdgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : Sym2 V => e ∈ G.edgeSet).card

/-- Independent first-principles subgraph containment: `H` (on `Fin m`) embeds as a subgraph of `G`
(on `V`) via an injective vertex map `φ : Fin m → V` preserving adjacency. -/
def RawContainsOnFin {V : Type*} (G : SimpleGraph V) (m : ℕ) (H : SimpleGraph (Fin m)) : Prop :=
  ∃ φ : Fin m → V, Function.Injective φ ∧ ∀ i j : Fin m, H.Adj i j → G.Adj (φ i) (φ j)

/-! ### 2. Semantic Equivalence Bridges -/

/-- Exact logical equivalence between `Erdos1019.IsPlanar` and `RawJordanPlanar` for every simple
graph `H` on any vertex type `W`. -/
theorem isPlanar_iff_rawJordanPlanar {W : Type*} (H : SimpleGraph W) :
    Erdos1019.IsPlanar H ↔ RawJordanPlanar H := by
  constructor
  · rintro ⟨D⟩
    refine ⟨D.vPos, D.vPos.injective, D.arc, D.arc_continuous, D.arc_injective, ?_, ?_,
      D.arc_inter_endpoints⟩
    · intro u v huv
      have he : s(u, v) ∈ H.edgeSet := H.mem_edgeSet.mpr huv
      have hend := D.arc_endpoints s(u, v) he
      let a₀ := D.arc s(u, v) he Erdos1019.unitZero
      let a₁ := D.arc s(u, v) he Erdos1019.unitOne
      have ha₀_ne_a₁ : a₀ ≠ a₁ := fun h =>
        Erdos1019.unitZero_ne_unitOne (D.arc_injective s(u, v) he h)
      have ha₀_mem : a₀ ∈ D.vPos '' {w : W | w ∈ s(u, v)} := by
        rw [← hend]; exact Set.mem_insert a₀ _
      have ha₁_mem : a₁ ∈ D.vPos '' {w : W | w ∈ s(u, v)} := by
        rw [← hend]; exact Set.mem_insert_of_mem a₀ (Set.mem_singleton a₁)
      rcases ha₀_mem with ⟨w₀, hw₀, hw₀_eq⟩
      rcases ha₁_mem with ⟨w₁, hw₁, hw₁_eq⟩
      rcases Sym2.mem_iff.mp hw₀ with rfl | rfl <;>
        rcases Sym2.mem_iff.mp hw₁ with rfl | rfl
      · exact False.elim (ha₀_ne_a₁ (hw₀_eq.symm.trans hw₁_eq))
      · exact Or.inl ⟨hw₀_eq.symm, hw₁_eq.symm⟩
      · exact Or.inr ⟨hw₀_eq.symm, hw₁_eq.symm⟩
      · exact False.elim (ha₀_ne_a₁ (hw₀_eq.symm.trans hw₁_eq))
    · intro e he t ht0 ht1 w hw
      exact D.arc_interior_disjoint e he t ht0 ht1 ⟨w, hw.symm⟩
  · rintro ⟨pos, hpos_inj, γ, hcont, hinj, hend, hint, hinter⟩
    refine ⟨{
      vPos := ⟨pos, hpos_inj⟩
      arc := γ
      arc_continuous := hcont
      arc_injective := hinj
      arc_endpoints := fun e he => by
        induction e using Sym2.inductionOn with
        | hf u v =>
          have huv : H.Adj u v := H.mem_edgeSet.mp he
          rcases hend u v huv with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · ext p
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff, Set.mem_image,
              Function.Embedding.coeFn_mk]
            change (p = γ s(u, v) he ⟨0, ⟨le_rfl, zero_le_one⟩⟩ ∨
              p = γ s(u, v) he ⟨1, ⟨zero_le_one, le_rfl⟩⟩) ↔ _
            rw [h0, h1]
            constructor
            · rintro (rfl | rfl)
              · exact ⟨u, Or.inl rfl, rfl⟩
              · exact ⟨v, Or.inr rfl, rfl⟩
            · rintro ⟨w, hwu | hwv, rfl⟩
              · rw [hwu]; exact Or.inl rfl
              · rw [hwv]; exact Or.inr rfl
          · ext p
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff, Set.mem_image,
              Function.Embedding.coeFn_mk]
            change (p = γ s(u, v) he ⟨0, ⟨le_rfl, zero_le_one⟩⟩ ∨
              p = γ s(u, v) he ⟨1, ⟨zero_le_one, le_rfl⟩⟩) ↔ _
            rw [h0, h1]
            constructor
            · rintro (rfl | rfl)
              · exact ⟨v, Or.inr rfl, rfl⟩
              · exact ⟨u, Or.inl rfl, rfl⟩
            · rintro ⟨w, hwu | hwv, rfl⟩
              · rw [hwu]; exact Or.inr rfl
              · rw [hwv]; exact Or.inl rfl
      arc_interior_disjoint := fun e he t ht0 ht1 hmem => by
        rcases hmem with ⟨w, hw⟩
        exact hint e he t ht0 ht1 w hw.symm
      arc_inter_endpoints := hinter
    }⟩

/-- Exact equality between `G.edgeSet.ncard` and `rawEdgeCount G`. -/
theorem ncard_edgeSet_eq_rawEdgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard = rawEdgeCount G := by
  classical
  rw [Erdos1019.ncard_edgeSet_eq_card_edgeFinset, rawEdgeCount]
  congr 1
  ext e
  simp

/-! ### 3. Audited Original-Problem Theorems (`[Er69c, p. 17]` & `[Er71, item 13, p. 102]`) -/

/-- **Audited Main Theorem (`=` threshold on arbitrary `Fintype V`, `1 ≤ |V|`)**:
Literal formalization of Erdős Problem #1019 (`[Er69c, p. 17]`, `[Er71, p. 102]`,
`erdosproblems.com/1019`, `JSP-000849`):
every simple graph `G` on `n ≥ 1` vertices with `⌊n²/4⌋ + ⌊(n + 1)/2⌋` edges contains a planar
subgraph on `m > 3` vertices with `3m - 6` edges. -/
theorem audit_erdos_1019_exact {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : 1 ≤ Fintype.card V)
    (hedges : rawEdgeCount G = (Fintype.card V) ^ 2 / 4 + (Fintype.card V + 1) / 2) :
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
      3 < m ∧
      RawJordanPlanar H ∧
      rawEdgeCount H = 3 * m - 6 ∧
      RawContainsOnFin G m H := by
  classical
  let eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let GFin : SimpleGraph (Fin (Fintype.card V)) := G.map eV.toEmbedding
  have hiso : G ≃g GFin := SimpleGraph.Iso.map eV G
  have hedges_fin : (Fintype.card V) ^ 2 / 4 + (Fintype.card V + 1) / 2 ≤ GFin.edgeSet.ncard := by
    have heq_ncard : GFin.edgeSet.ncard = G.edgeSet.ncard := by
      rw [Erdos1019.ncard_edgeSet_eq_card_edgeFinset, Erdos1019.ncard_edgeSet_eq_card_edgeFinset,
        ← SimpleGraph.card_edgeSet, ← SimpleGraph.card_edgeSet]
      exact Fintype.card_congr hiso.symm.mapEdgeSet
    rw [heq_ncard, ncard_edgeSet_eq_rawEdgeCount, hedges]
  obtain ⟨m, H, hm3, hplan, hsat, ⟨f⟩⟩ :=
    Erdos1019.erdos_1019_fin (Fintype.card V) hn GFin hedges_fin
  refine ⟨m, H, hm3, (isPlanar_iff_rawJordanPlanar H).mp hplan, ?_, ?_⟩
  · rwa [← ncard_edgeSet_eq_rawEdgeCount]
  · refine ⟨fun i => hiso.symm (f i), hiso.symm.injective.comp f.injective, ?_⟩
    intro i j hij
    exact hiso.symm.map_rel_iff.mpr (f.toHom.map_adj hij)

/-- **Audited Main Theorem (`≥` threshold on arbitrary `Fintype V`, `1 ≤ |V|`)**:
Monotone-threshold version of Erdős Problem #1019 (`erdosproblems.com/forum/thread/1019`, Part i):
every simple graph `G` on `n ≥ 1` vertices with at least `⌊n²/4⌋ + ⌊(n + 1)/2⌋` edges contains a
planar subgraph on `m > 3` vertices with `3m - 6` edges. -/
theorem audit_erdos_1019_ge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : 1 ≤ Fintype.card V)
    (hedges : (Fintype.card V) ^ 2 / 4 + (Fintype.card V + 1) / 2 ≤ rawEdgeCount G) :
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
      3 < m ∧
      RawJordanPlanar H ∧
      rawEdgeCount H = 3 * m - 6 ∧
      RawContainsOnFin G m H := by
  classical
  let eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let GFin : SimpleGraph (Fin (Fintype.card V)) := G.map eV.toEmbedding
  have hiso : G ≃g GFin := SimpleGraph.Iso.map eV G
  have hedges_fin : (Fintype.card V) ^ 2 / 4 + (Fintype.card V + 1) / 2 ≤ GFin.edgeSet.ncard := by
    have heq_ncard : GFin.edgeSet.ncard = G.edgeSet.ncard := by
      rw [Erdos1019.ncard_edgeSet_eq_card_edgeFinset, Erdos1019.ncard_edgeSet_eq_card_edgeFinset,
        ← SimpleGraph.card_edgeSet, ← SimpleGraph.card_edgeSet]
      exact Fintype.card_congr hiso.symm.mapEdgeSet
    rwa [heq_ncard, ncard_edgeSet_eq_rawEdgeCount]
  obtain ⟨m, H, hm3, hplan, hsat, ⟨f⟩⟩ :=
    Erdos1019.erdos_1019_fin (Fintype.card V) hn GFin hedges_fin
  refine ⟨m, H, hm3, (isPlanar_iff_rawJordanPlanar H).mp hplan, ?_, ?_⟩
  · rwa [← ncard_edgeSet_eq_rawEdgeCount]
  · refine ⟨fun i => hiso.symm (f i), hiso.symm.injective.comp f.injective, ?_⟩
    intro i j hij
    exact hiso.symm.map_rel_iff.mpr (f.toHom.map_adj hij)

/-- **Audited Subgraph-Object Theorem (`G.Subgraph`, `n ≥ 4`, zero extra premises)**:
Direct `G.Subgraph` formulation for all finite vertex types `V` with `4 ≤ Fintype.card V`. -/
theorem audit_erdos_1019_subgraph {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : 4 ≤ Fintype.card V)
    (hedges : (Fintype.card V) ^ 2 / 4 + (Fintype.card V + 1) / 2 ≤ rawEdgeCount G) :
    ∃ H : G.Subgraph, ∃ _ : Fintype H.verts,
      3 < @Fintype.card H.verts ‹_› ∧
      RawJordanPlanar H.coe ∧
      @rawEdgeCount H.verts ‹_› H.coe = 3 * @Fintype.card H.verts ‹_› - 6 := by
  rw [← ncard_edgeSet_eq_rawEdgeCount] at hedges
  obtain ⟨H, inst, hgt3, hplan, hsat⟩ := Erdos1019.erdos_1019_ge_of_four_le G hn hedges
  refine ⟨H, inst, hgt3, (isPlanar_iff_rawJordanPlanar H.coe).mp hplan, ?_⟩
  rwa [← @ncard_edgeSet_eq_rawEdgeCount H.verts inst H.coe]

end StatementAudit

/-! ### 4. Transitive Axiom Audit -/

#check @Erdos1019.completeGraph_fin4_isPlanar
#check @Erdos1019.bipyramidGraph_isPlanar
#check @Erdos1019.simonovits_stability
#check @Erdos1019.erdos_1019
#check @Erdos1019.erdos_1019_ge
#check @Erdos1019.erdos_1019_ge_of_four_le
#check @Erdos1019.erdos_1019_fin
#check @StatementAudit.isPlanar_iff_rawJordanPlanar
#check @StatementAudit.audit_erdos_1019_exact
#check @StatementAudit.audit_erdos_1019_ge
#check @StatementAudit.audit_erdos_1019_subgraph

#print axioms Erdos1019.completeGraph_fin4_isPlanar
#print axioms Erdos1019.bipyramidGraph_isPlanar
#print axioms Erdos1019.simonovits_stability
#print axioms Erdos1019.erdos_1019
#print axioms Erdos1019.erdos_1019_ge
#print axioms Erdos1019.erdos_1019_ge_of_four_le
#print axioms Erdos1019.erdos_1019_fin
#print axioms StatementAudit.isPlanar_iff_rawJordanPlanar
#print axioms StatementAudit.audit_erdos_1019_exact
#print axioms StatementAudit.audit_erdos_1019_ge
#print axioms StatementAudit.audit_erdos_1019_subgraph
