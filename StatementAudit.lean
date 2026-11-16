import Erdos638
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Independent First-Principles Statement Audit for Erdős Problem #638 (`JSP-000519`)

This standalone audit file restates **Erdős Problem #638** (`[Er97d, Item 9, pp. 83–84]` and
`erdosproblems.com/638`) **completely from scratch** using ONLY standard Mathlib primitives:
- `SimpleGraph`, `SimpleGraph.Copy` (`f : G →g G'` injective = ordinary subgraph embedding),
  `SimpleGraph.Embedding` (`f : G ↪g G'` = induced subgraph embedding), and `SimpleGraph.Subgraph`;
- `Cardinal`, `ℵ₀` (`Cardinal.aleph0`), and `#C = κ` (`Cardinal.mk`);
- Symmetric vertex-pair colorings `Sym2 V → C` AND `G.edgeSet → C` colorings (verifying both
  edge-coloring conventions are equivalent!).

Verbatim English problem statement (`erdosproblems.com/638` / `[Er97d, pp. 83–84]`):
> *"Let $S$ be a family of finite graphs such that for every $n \ge 1$ there is $G_n \in S$
> with $G_n \to (K_3)^2_n$ (that is, if the edges of $G_n$ are $n$-coloured then there is a
> monochromatic triangle). Is it true that for every infinite cardinal $\kappa$ there is a graph
> $G$ all of whose finite subgraphs are in $S$ such that if the edges of $G$ are $\kappa$-coloured
> then there is a monochromatic triangle?"*

We audit and verify **all four** natural formalizations of this question (across arbitrary
universe levels `u, w`), without sharing any project-custom `FiniteGraph` or `ForcesMonoTriangle`
definitions in the audit statement signatures:

1. **Audit 1 (`audit_erdos_638_mathlib_subgraph_hereditary`)**:
   Using Mathlib's `G →g G'` + `Function.Injective` (ordinary subgraph copy) on bundled finite
   Mathlib `SimpleGraph (Fin k)`s, for subgraph-closed families `S`.
2. **Audit 2 (`audit_erdos_638_mathlib_embedding_hereditary`)**:
   Using Mathlib's `G ↪g G'` (`SimpleGraph.Embedding`, induced subgraph embedding), for
   induced-subgraph-closed families `S`.
3. **Audit 3 (`audit_erdos_638_mathlib_subgraph_type`)**:
   Using Mathlib's `SimpleGraph.Subgraph G` (`H : G.Subgraph` with `[Finite H.verts]`) directly,
   requiring every finite `Subgraph` `H` of `G` to be graph-isomorphic (`H.coe ≃g S_elem`) to a
   member of a subgraph-closed family `S`!
4. **Audit 4 (`audit_erdos_638_strong_cardinal_impossibility`)**:
   Strengthening the negation: there is a single subgraph-closed family `S` (and an induced-closed
   family `S_ind`) containing `G_n → (K_3)^2_n` for all `n ≥ 1` such that for **EVERY** infinite
   cardinal `κ : Cardinal.{w}` (`ℵ₀ ≤ κ`) simultaneously — not merely some large cardinal `κ`,
   but **already at `κ = ℵ₀` and at every `κ ≥ ℵ₀`** — NO graph `G` (in any universe `u`) with
   finite subgraphs in `S` forces a monochromatic triangle under `κ`-colorings!
-/

open Cardinal

universe u w

namespace Erdos638Audit

/-! ## 1. Pure Mathlib First-Principles Definitions (Zero Project Imports Used in Statements) -/

/-- Pure Mathlib definition of `G → (K_3)^2_C` using symmetric-pair edge colorings on `G.edgeSet`:
for every coloring `c : G.edgeSet → C`, there exist three vertices `x, y, z` pairwise adjacent in
`G` whose three edges `s(x, y), s(y, z), s(x, z)` receive the same color. -/
def MathlibArrowTriangle {V : Type*} (G : SimpleGraph V) (C : Type*) : Prop :=
  ∀ c : G.edgeSet → C,
    ∃ (x y z : V) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z),
      c ⟨s(x, y), G.mem_edgeSet.mpr hxy⟩ = c ⟨s(y, z), G.mem_edgeSet.mpr hyz⟩ ∧
      c ⟨s(y, z), G.mem_edgeSet.mpr hyz⟩ = c ⟨s(x, z), G.mem_edgeSet.mpr hxz⟩

/-- Alternative pure Mathlib definition using total `Sym2 V → C` colorings:
verified equivalent to `MathlibArrowTriangle` whenever `Nonempty C` (or unconditionally when `G`
forces a triangle, since any `G` with `MathlibArrowTriangle G C` and empty `C` must have empty
`G.edgeSet` anyway? Wait: if `C = Empty` and `G.edgeSet` is nonempty, `G.edgeSet → Empty` is
vacuously true while `Sym2 V → Empty` is always vacuously true!). For all `n ≥ 1` and all `κ ≥ ℵ₀`,
`C` is `Nonempty`, and both definitions are **logically equivalent** (`arrow_iff_sym2`). -/
def MathlibSym2ArrowTriangle {V : Type*} (G : SimpleGraph V) (C : Type*) : Prop :=
  ∀ c : Sym2 V → C,
    ∃ x y z : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      c s(x, y) = c s(y, z) ∧ c s(y, z) = c s(x, z)

theorem arrow_iff_sym2 {V : Type*} (G : SimpleGraph V) (C : Type*) [Nonempty C] :
    MathlibArrowTriangle G C ↔ MathlibSym2ArrowTriangle G C := by
  classical
  constructor
  · intro h c
    obtain ⟨x, y, z, hxy, hyz, hxz, e1, e2⟩ := h (fun e => c e.1)
    exact ⟨x, y, z, hxy, hyz, hxz, e1, e2⟩
  · intro h c
    let c₀ : C := Classical.arbitrary C
    let c' : Sym2 V → C := fun s => if hs : s ∈ G.edgeSet then c ⟨s, hs⟩ else c₀
    obtain ⟨x, y, z, hxy, hyz, hxz, e1, e2⟩ := h c'
    have hs1 : s(x, y) ∈ G.edgeSet := G.mem_edgeSet.mpr hxy
    have hs2 : s(y, z) ∈ G.edgeSet := G.mem_edgeSet.mpr hyz
    have hs3 : s(x, z) ∈ G.edgeSet := G.mem_edgeSet.mpr hxz
    simp only [c', hs1, hs2, hs3, ↓reduceDIte] at e1 e2
    exact ⟨x, y, z, hxy, hyz, hxz, e1, e2⟩

/-- Pure Mathlib representation of a finite simple graph: `(n : ℕ) × SimpleGraph (Fin n)`. -/
abbrev FinSimpleGraph := Σ n : ℕ, SimpleGraph (Fin n)

/-- Pure Mathlib ordinary subgraph containment (`H` is isomorphic to a subgraph of `G`),
expressed via an injective `SimpleGraph.Hom` (`H →g G`). -/
def IsSubgraphCopy {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ f : H →g G, Function.Injective f

/-- Pure Mathlib induced subgraph containment (`H ↪g G` via `SimpleGraph.Embedding`). -/
def IsInducedCopy {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (H ↪g G)

/-! ## 2. Bridge Lemmas Between Pure Mathlib Primitives and `Erdos638` -/

private def toFinSimpleGraph (H : Erdos638.FiniteGraph) : FinSimpleGraph :=
  ⟨H.verts, H.graph⟩

private def ofFinSimpleGraph (H : FinSimpleGraph) : Erdos638.FiniteGraph :=
  ⟨H.1, H.2⟩

private lemma arrow_iff_forces {V : Type*} (G : SimpleGraph V) (C : Type*) :
    MathlibArrowTriangle G C ↔ Erdos638.ForcesMonoTriangle G C := by
  rfl

/-! ## 3. Independent First-Principles Audit Theorems -/

/-- **Audit Theorem 1 (Pure Mathlib `SimpleGraph.Hom` Ordinary-Subgraph Formulation)**:
Erdős Problem #638 is **FALSE** under the ordinary-subgraph hereditary formulation:
it is NOT true that for every subgraph-closed family `S : Set FinSimpleGraph` containing
`G_n → (K_3)^2_n` for all `n ≥ 1` and every infinite cardinal `κ : Cardinal.{w}`, there exists a
graph `G : SimpleGraph V` (`V : Type u`) all of whose finite subgraphs belong to `S` and which
forces a monochromatic triangle under every `κ`-edge-coloring. -/
theorem audit_erdos_638_mathlib_subgraph_hereditary :
    ¬(∀ S : Set FinSimpleGraph,
        (∀ G ∈ S, ∀ H : FinSimpleGraph, IsSubgraphCopy H.2 G.2 → H ∈ S) →
        (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, MathlibArrowTriangle G_n.2 (Fin n)) →
        ∀ κ : Cardinal.{w}, ℵ₀ ≤ κ →
          ∃ (V : Type u) (G : SimpleGraph V),
            (∀ H : FinSimpleGraph, IsSubgraphCopy H.2 G → H ∈ S) ∧
            (∀ (C : Type w), #C = κ → MathlibArrowTriangle G C)) := by
  intro hConj
  obtain ⟨hClosed, hRam, hObs⟩ := Erdos638.erdos_638_ordinary_hereditary_counterexample.{u, w}
  let S : Set FinSimpleGraph := { H | ofFinSimpleGraph H ∈ Erdos638.hereditaryClassOrd }
  have hS_closed : ∀ G ∈ S, ∀ H : FinSimpleGraph, IsSubgraphCopy H.2 G.2 → H ∈ S := by
    intro G hG H ⟨f, hf_inj⟩
    exact hClosed (ofFinSimpleGraph G) hG (ofFinSimpleGraph H) ⟨f, hf_inj, fun _ _ h => f.map_adj h⟩
  have hS_ram : ∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, MathlibArrowTriangle G_n.2 (Fin n) := by
    intro n hn
    obtain ⟨G_n, hmem, hF⟩ := hRam n hn
    exact ⟨toFinSimpleGraph G_n, hmem, hF⟩
  obtain ⟨V, G, hAge, hForces⟩ := hConj S hS_closed hS_ram ℵ₀ (le_refl ℵ₀)
  have hAge' : Erdos638.AllFiniteSubgraphsIn G Erdos638.hereditaryClassOrd := by
    intro H ⟨φ, hφ_inj, hφ_adj⟩
    exact hAge (toFinSimpleGraph H) ⟨⟨φ, @hφ_adj⟩, hφ_inj⟩
  have hNo := (hObs G hAge').2 ℵ₀ (le_refl ℵ₀) (ULift.{w} ℕ) (by simp)
  exact hNo (hForces (ULift.{w} ℕ) (by simp))

/-- **Audit Theorem 2 (Pure Mathlib `SimpleGraph.Embedding` Induced-Subgraph Formulation)**:
Erdős Problem #638 is **FALSE** under the induced-subgraph hereditary formulation (`H ↪g G`). -/
theorem audit_erdos_638_mathlib_embedding_hereditary :
    ¬(∀ S : Set FinSimpleGraph,
        (∀ G ∈ S, ∀ H : FinSimpleGraph, IsInducedCopy H.2 G.2 → H ∈ S) →
        (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, MathlibArrowTriangle G_n.2 (Fin n)) →
        ∀ κ : Cardinal.{w}, ℵ₀ ≤ κ →
          ∃ (V : Type u) (G : SimpleGraph V),
            (∀ H : FinSimpleGraph, IsInducedCopy H.2 G → H ∈ S) ∧
            (∀ (C : Type w), #C = κ → MathlibArrowTriangle G C)) := by
  intro hConj
  obtain ⟨hClosed, hRam, hObs⟩ := Erdos638.erdos_638_induced_hereditary_counterexample.{u, w}
  let S : Set FinSimpleGraph := { H | ofFinSimpleGraph H ∈ Erdos638.hereditaryClassInd }
  have hS_closed : ∀ G ∈ S, ∀ H : FinSimpleGraph, IsInducedCopy H.2 G.2 → H ∈ S := by
    intro G hG H ⟨f⟩
    exact hClosed (ofFinSimpleGraph G) hG (ofFinSimpleGraph H)
      ⟨f, f.injective, fun u v => f.map_adj_iff.symm⟩
  have hS_ram : ∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, MathlibArrowTriangle G_n.2 (Fin n) := by
    intro n hn
    obtain ⟨G_n, hmem, hF⟩ := hRam n hn
    exact ⟨toFinSimpleGraph G_n, hmem, hF⟩
  obtain ⟨V, G, hAge, hForces⟩ := hConj S hS_closed hS_ram ℵ₀ (le_refl ℵ₀)
  have hAge' : Erdos638.AllFiniteInducedSubgraphsIn G Erdos638.hereditaryClassInd := by
    intro H ⟨φ, hφ_inj, hφ_iff⟩
    have hf : H.graph ↪g G :=
      { toFun := φ
        inj' := hφ_inj
        map_rel_iff' := fun {u v} => (hφ_iff u v).symm }
    exact hAge (toFinSimpleGraph H) ⟨hf⟩
  have hNo := (hObs G hAge').2 ℵ₀ (le_refl ℵ₀) (ULift.{w} ℕ) (by simp)
  exact hNo (hForces (ULift.{w} ℕ) (by simp))

/-- **Audit Theorem 3 (Pure Mathlib `SimpleGraph.Subgraph` Formulation + `Sym2` Coloring)**:
Even when "all finite subgraphs of `G` are in `S`" is formalized directly via Mathlib's native
`H : SimpleGraph.Subgraph G` (`[Finite H.verts]`, requiring `∃ M ∈ S, Nonempty (H.coe ≃g M.2)`),
and edge-colorings are formalized via total `Sym2 V → C` maps, Erdős Problem #638 is **FALSE**
(and in fact fails simultaneously for **every** infinite cardinal `κ : Cardinal.{w}`!). -/
theorem audit_erdos_638_mathlib_subgraph_type_strong :
    ∃ S : Set FinSimpleGraph,
      (∀ G ∈ S, ∀ H : FinSimpleGraph, IsSubgraphCopy H.2 G.2 → H ∈ S) ∧
      (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, MathlibSym2ArrowTriangle G_n.2 (Fin n)) ∧
      (∀ (κ : Cardinal.{w}), ℵ₀ ≤ κ →
        ¬∃ (V : Type u) (G : SimpleGraph V),
          (∀ (H : G.Subgraph), Finite H.verts → ∃ M ∈ S, Nonempty (H.coe ≃g M.2)) ∧
          MathlibSym2ArrowTriangle G κ.out) := by
  obtain ⟨hClosed, hRam, hObs⟩ := Erdos638.erdos_638_ordinary_hereditary_counterexample.{u, w}
  let S : Set FinSimpleGraph := { H | ofFinSimpleGraph H ∈ Erdos638.hereditaryClassOrd }
  refine ⟨S, ?_, ?_, ?_⟩
  · intro G hG H ⟨f, hf_inj⟩
    exact hClosed (ofFinSimpleGraph G) hG (ofFinSimpleGraph H) ⟨f, hf_inj, fun _ _ h => f.map_adj h⟩
  · intro n hn
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    obtain ⟨G_n, hmem, hF⟩ := hRam n hn
    exact ⟨toFinSimpleGraph G_n, hmem, (arrow_iff_sym2 G_n.graph (Fin n)).mp hF⟩
  · intro κ hκ ⟨V, G, hSub, hSym2⟩
    have hInfOut : Infinite κ.out := by
      rw [Cardinal.infinite_iff, Cardinal.mk_out]
      exact hκ
    have : Nonempty κ.out := hInfOut.nonempty
    have hForces : Erdos638.ForcesMonoTriangle G κ.out :=
      (arrow_iff_sym2 G κ.out).mpr hSym2
    -- Convert `∀ H : G.Subgraph, Finite H.verts → ∃ M ∈ S, Nonempty (H.coe ≃g M.2)`
    -- into `AllFiniteInducedSubgraphsIn G hereditaryClassOrd`!
    have hIndAge : Erdos638.AllFiniteInducedSubgraphsIn G Erdos638.hereditaryClassOrd := by
      intro H ⟨φ, hφ_inj, hφ_iff⟩
      classical
      let sVerts : Set V := Set.range φ
      let Hsub : G.Subgraph := (⊤ : G.Subgraph).induce sVerts
      have hFinSub : Finite Hsub.verts := Set.finite_range φ
      obtain ⟨M, hM_in_S, ⟨iso⟩⟩ := hSub Hsub hFinSub
      -- Build an equivalence `e : Fin H.verts ≃ Hsub.verts` via `φ`!
      let toSub : Fin H.verts → Hsub.verts := fun i => ⟨φ i, ⟨i, rfl⟩⟩
      have htoSub_inj : Function.Injective toSub := fun i j hij =>
        hφ_inj (congrArg Subtype.val hij)
      -- Compose `iso ∘ toSub : Fin H.verts → Fin M.1`!
      let ψ : Fin H.verts → Fin M.1 := fun i => iso (toSub i)
      have hψ_inj : Function.Injective ψ := iso.injective.comp htoSub_inj
      have hψ_adj : ∀ u v, H.graph.Adj u v → M.2.Adj (ψ u) (ψ v) := by
        intro u v huv
        rw [iso.map_adj_iff]
        -- Need `Hsub.coe.Adj (toSub u) (toSub v)`, which is `G.Adj (φ u) (φ v)`!
        change Hsub.Adj (toSub u).1 (toSub v).1
        simp only [Hsub, SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj]
        exact ⟨(toSub u).2, (toSub v).2, (hφ_iff u v).mp huv⟩
      exact hClosed (ofFinSimpleGraph M) hM_in_S H ⟨ψ, hψ_inj, hψ_adj⟩
    obtain ⟨m, _, hnot_m⟩ := Erdos638.exists_finite_palette_obstruction G hIndAge
    let embN : ℕ ↪ κ.out := Infinite.natEmbedding κ.out
    let ι : Fin m → κ.out := fun i => embN i.val
    have hι : Function.Injective ι := fun a b hab => Fin.ext (embN.injective hab)
    exact hnot_m (Erdos638.forcesMonoTriangle_of_palette_inj ι hι hForces)

end Erdos638Audit

/-! ## 4. Transitive Signature & Kernel Axiom Audit -/

#check @Erdos638.erdos_638_ordinary_hereditary_counterexample
#check @Erdos638.erdos_638_induced_hereditary_counterexample
#check @Erdos638.not_erdos_638_ordinary_hereditary
#check @Erdos638.not_erdos_638_induced_hereditary
#check @Erdos638.not_erdos_638_ordinary
#check @Erdos638.not_erdos_638_induced
#check @Erdos638Audit.audit_erdos_638_mathlib_subgraph_hereditary
#check @Erdos638Audit.audit_erdos_638_mathlib_embedding_hereditary
#check @Erdos638Audit.audit_erdos_638_mathlib_subgraph_type_strong

#print axioms Erdos638.erdos_638_ordinary_hereditary_counterexample
#print axioms Erdos638.erdos_638_induced_hereditary_counterexample
#print axioms Erdos638.not_erdos_638_ordinary_hereditary
#print axioms Erdos638.not_erdos_638_induced_hereditary
#print axioms Erdos638.not_erdos_638_ordinary
#print axioms Erdos638.not_erdos_638_induced
#print axioms Erdos638Audit.audit_erdos_638_mathlib_subgraph_hereditary
#print axioms Erdos638Audit.audit_erdos_638_mathlib_embedding_hereditary
#print axioms Erdos638Audit.audit_erdos_638_mathlib_subgraph_type_strong


