import Erdos638.Compactness
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Erdős Problem #638 (`JSP-000519`): Main Theorems

We assemble the complete unconditional ZFC disproof of **Erdős Problem #638**
(`[Er97d, Item 9, pp. 83–84]`, `erdosproblems.com/638`), covering **every** standard reading
of the problem statement across arbitrary universe levels `u, w`:

1. **Ordinary-subgraph hereditary formulation** (`erdos_638_ordinary_hereditary_counterexample` /
   `not_erdos_638_ordinary_hereditary`):
   There exists a family `S = hereditaryClassOrd : Set FiniteGraph` closed under ordinary
   subgraphs (`ClosedUnderSubgraphs S`) containing an `n`-color triangle-Ramsey graph
   `G_n → (K_3)^2_n` for every `n ≥ 1`, such that for **every** graph `G : SimpleGraph V`
   (`V : Type u`) whose finite subgraphs all belong to `S`:
   - there already exists a **finite** palette size `m ≥ 2` with `¬ForcesMonoTriangle G (Fin m)`;
   - consequently, for **every** infinite cardinal `κ : Cardinal.{w}` (`ℵ₀ ≤ κ`, including
     `κ = ℵ₀`!), `¬ForcesMonoTriangle G κ.out` (and for every type `C : Type w` with `#C = κ`,
     `¬ForcesMonoTriangle G C`).

2. **Induced-subgraph hereditary formulation** (`erdos_638_induced_hereditary_counterexample` /
   `not_erdos_638_induced_hereditary`):
   There exists a family `S = hereditaryClassInd : Set FiniteGraph` closed under induced
   subgraphs (`ClosedUnderInducedSubgraphs S`) containing an `n`-color triangle-Ramsey graph
   `G_n → (K_3)^2_n` for every `n ≥ 1`, such that for **every** graph `G : SimpleGraph V`
   (`V : Type u`) whose finite induced subgraphs all belong to `S`:
   - there already exists a **finite** palette size `m ≥ 2` with `¬ForcesMonoTriangle G (Fin m)`;
   - consequently, for **every** infinite cardinal `κ : Cardinal.{w}` (`ℵ₀ ≤ κ`),
     `¬ForcesMonoTriangle G κ.out` (and for every type `C : Type w` with `#C = κ`,
     `¬ForcesMonoTriangle G C`).

3. **Literal non-hereditary formulation**:
   Dropping `ClosedUnderSubgraphs S` / `ClosedUnderInducedSubgraphs S` makes the existential
   witness `S` only easier to construct, so `hereditaryClassOrd` and `hereditaryClassInd`
   immediately disprove the non-hereditary statement as well (`not_erdos_638_ordinary`,
   `not_erdos_638_induced`).

### Mathematical Attribution
- Original problem: Paul Erdős, *Some of my new and almost new problems and results in
  combinatorial number theory* (`[Er97d, Item 9, pp. 83–84]`, 1997).
- Mathematical counterexample strategy (disjoint Ramsey-age blocks via sparse triangle-Ramsey
  graphs + compactness): Brian Saturnino (*A counterexample to a hereditary triangle Ramsey
  compactness problem*, `erdosproblems.com/forum/thread/638`, April 26, 2026); see also
  Kevin Barreto's finite-obstruction note (`erdosproblems.com/forum/thread/638`, Jan 29, 2026).
- Sparse triangle-Ramsey hypergraph container method: Rajko Nenadov and Huy Tuan Pham (2024/2025),
  after Nenadov–Steger (2016) and Rödl–Ruciński (1994). Here we give a 100% self-contained
  elementary proof over `ℚ` avoiding Nešetřil–Rödl partite amalgamation, Berge cycles, and real
  transcendental analysis via the `(2|S| - 3)`-sparsity 2-coloring theorem (`Defs.lean`),
  single-function rational containers (`Container.lean`), and exact `(m² + 2, 1/m)` grid
  alteration (`GridCounting.lean`, `SparseRamsey.lean`, `AlterationBound.lean`).
-/

open Cardinal

universe u w

namespace Erdos638

/-! ## 1. Constructive Counterexample Packages (Strongest Positive Form of the Negation) -/

/-- **Main Theorem 1 (Ordinary-Subgraph Hereditary Counterexample, Constructive Form)**:
The family `hereditaryClassOrd : Set FiniteGraph` satisfies:
1. `ClosedUnderSubgraphs hereditaryClassOrd` (closed under all ordinary finite subgraphs);
2. For every `n ≥ 1`, there exists `G_n ∈ hereditaryClassOrd` with `G_n → (K_3)^2_n`;
3. For every vertex type `V : Type u` and graph `G : SimpleGraph V` whose finite subgraphs all
   lie in `hereditaryClassOrd`:
   - there exists a finite `m ≥ 2` with `¬ForcesMonoTriangle G (Fin m)`; and
   - for every infinite cardinal `κ : Cardinal.{w}` (`ℵ₀ ≤ κ`) and every palette `C : Type w`
     with `#C = κ`, `¬ForcesMonoTriangle G C`. -/
theorem erdos_638_ordinary_hereditary_counterexample :
    ClosedUnderSubgraphs hereditaryClassOrd ∧
    (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ hereditaryClassOrd, ForcesMonoTriangle G_n.graph (Fin n)) ∧
    (∀ {V : Type u} (G : SimpleGraph V),
      AllFiniteSubgraphsIn G hereditaryClassOrd →
      (∃ m : ℕ, 2 ≤ m ∧ ¬ForcesMonoTriangle G (Fin m)) ∧
      (∀ (κ : Cardinal.{w}), ℵ₀ ≤ κ →
        ∀ (C : Type w), #C = κ → ¬ForcesMonoTriangle G C)) := by
  refine ⟨hereditaryClassOrd_closed, fun n _ => hereditaryClassOrd_contains_n_ramsey n, ?_⟩
  intro V G hAge
  have hIndAge : AllFiniteInducedSubgraphsIn G hereditaryClassOrd := by
    intro H ⟨φ, hφ_inj, hφ_iff⟩
    exact hAge H ⟨φ, hφ_inj, fun u v h => (hφ_iff u v).mp h⟩
  refine ⟨exists_finite_palette_obstruction G hIndAge, ?_⟩
  intro κ hκ C hC
  have : Infinite C := by
    rw [Cardinal.infinite_iff, hC]
    exact hκ
  exact not_forcesMonoTriangle_infinite_of_ord G hAge C

/-- **Main Theorem 2 (Induced-Subgraph Hereditary Counterexample, Constructive Form)**:
The family `hereditaryClassInd : Set FiniteGraph` satisfies:
1. `ClosedUnderInducedSubgraphs hereditaryClassInd` (closed under all finite induced subgraphs);
2. For every `n ≥ 1`, there exists `G_n ∈ hereditaryClassInd` with `G_n → (K_3)^2_n`;
3. For every vertex type `V : Type u` and graph `G : SimpleGraph V` whose finite induced subgraphs
   all lie in `hereditaryClassInd`:
   - there exists a finite `m ≥ 2` with `¬ForcesMonoTriangle G (Fin m)`; and
   - for every infinite cardinal `κ : Cardinal.{w}` (`ℵ₀ ≤ κ`) and every palette `C : Type w`
     with `#C = κ`, `¬ForcesMonoTriangle G C`. -/
theorem erdos_638_induced_hereditary_counterexample :
    ClosedUnderInducedSubgraphs hereditaryClassInd ∧
    (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ hereditaryClassInd, ForcesMonoTriangle G_n.graph (Fin n)) ∧
    (∀ {V : Type u} (G : SimpleGraph V),
      AllFiniteInducedSubgraphsIn G hereditaryClassInd →
      (∃ m : ℕ, 2 ≤ m ∧ ¬ForcesMonoTriangle G (Fin m)) ∧
      (∀ (κ : Cardinal.{w}), ℵ₀ ≤ κ →
        ∀ (C : Type w), #C = κ → ¬ForcesMonoTriangle G C)) := by
  refine ⟨hereditaryClassInd_closed, fun n _ => hereditaryClassInd_contains_n_ramsey n, ?_⟩
  intro V G hAge
  have hIndOrd : AllFiniteInducedSubgraphsIn G hereditaryClassOrd := by
    intro H hH
    exact hereditaryClassInd_subset_ord (hAge H hH)
  refine ⟨exists_finite_palette_obstruction G hIndOrd, ?_⟩
  intro κ hκ C hC
  have : Infinite C := by
    rw [Cardinal.infinite_iff, hC]
    exact hκ
  exact not_forcesMonoTriangle_infinite_of_ind G hAge C

/-! ## 2. Direct Negations of the Yes/No Problem Statements (`[Er97d]` & `erdosproblems.com/638`) -/

/-- Exact statement of Erdős Problem #638 under the ordinary-subgraph hereditary reading:
*"For every subgraph-closed family `S` of finite graphs containing `G_n → (K_3)^2_n` for all
`n ≥ 1`, and for every infinite cardinal `κ`, there exists a graph `G` (on `V : Type u`) all of
whose finite subgraphs are in `S` such that `G → (K_3)^2_κ`."* -/
def Erdos638OrdinaryHereditaryProp : Prop :=
  ∀ S : Set FiniteGraph,
    ClosedUnderSubgraphs S →
    (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, ForcesMonoTriangle G_n.graph (Fin n)) →
    ∀ κ : Cardinal.{w}, ℵ₀ ≤ κ →
      ∃ (V : Type u) (G : SimpleGraph V),
        AllFiniteSubgraphsIn G S ∧ ForcesMonoTriangle G κ.out

/-- Exact statement of Erdős Problem #638 under the induced-subgraph hereditary reading:
*"For every induced-subgraph-closed family `S` of finite graphs containing `G_n → (K_3)^2_n` for all
`n ≥ 1`, and for every infinite cardinal `κ`, there exists a graph `G` (on `V : Type u`) all of
whose finite induced subgraphs are in `S` such that `G → (K_3)^2_κ`."* -/
def Erdos638InducedHereditaryProp : Prop :=
  ∀ S : Set FiniteGraph,
    ClosedUnderInducedSubgraphs S →
    (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, ForcesMonoTriangle G_n.graph (Fin n)) →
    ∀ κ : Cardinal.{w}, ℵ₀ ≤ κ →
      ∃ (V : Type u) (G : SimpleGraph V),
        AllFiniteInducedSubgraphsIn G S ∧ ForcesMonoTriangle G κ.out

/-- Literal non-hereditary statement of Erdős Problem #638 (ordinary subgraphs, no closure assumed on `S`). -/
def Erdos638OrdinaryProp : Prop :=
  ∀ S : Set FiniteGraph,
    (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, ForcesMonoTriangle G_n.graph (Fin n)) →
    ∀ κ : Cardinal.{w}, ℵ₀ ≤ κ →
      ∃ (V : Type u) (G : SimpleGraph V),
        AllFiniteSubgraphsIn G S ∧ ForcesMonoTriangle G κ.out

/-- Literal non-hereditary statement of Erdős Problem #638 (induced subgraphs, no closure assumed on `S`). -/
def Erdos638InducedProp : Prop :=
  ∀ S : Set FiniteGraph,
    (∀ n : ℕ, 1 ≤ n → ∃ G_n ∈ S, ForcesMonoTriangle G_n.graph (Fin n)) →
    ∀ κ : Cardinal.{w}, ℵ₀ ≤ κ →
      ∃ (V : Type u) (G : SimpleGraph V),
        AllFiniteInducedSubgraphsIn G S ∧ ForcesMonoTriangle G κ.out

/-- **Disproof of Erdős Problem #638 (Ordinary-Subgraph Hereditary Reading)** across all
universe levels `u, w` (already failing at `κ = ULift.{w} ℕ`, i.e., `κ = ℵ₀`!). -/
theorem not_erdos_638_ordinary_hereditary : ¬Erdos638OrdinaryHereditaryProp.{u, w} := by
  intro hProp
  obtain ⟨hClosed, hRam, hObs⟩ := erdos_638_ordinary_hereditary_counterexample.{u, w}
  obtain ⟨V, G, hAge, hForces⟩ := hProp hereditaryClassOrd hClosed hRam ℵ₀ (le_refl ℵ₀)
  exact (hObs G hAge).2 ℵ₀ (le_refl ℵ₀) (ℵ₀ : Cardinal.{w}).out (Cardinal.mk_out ℵ₀) hForces

/-- **Disproof of Erdős Problem #638 (Induced-Subgraph Hereditary Reading)** across all
universe levels `u, w` (already failing at `κ = ℵ₀`!). -/
theorem not_erdos_638_induced_hereditary : ¬Erdos638InducedHereditaryProp.{u, w} := by
  intro hProp
  obtain ⟨hClosed, hRam, hObs⟩ := erdos_638_induced_hereditary_counterexample.{u, w}
  obtain ⟨V, G, hAge, hForces⟩ := hProp hereditaryClassInd hClosed hRam ℵ₀ (le_refl ℵ₀)
  exact (hObs G hAge).2 ℵ₀ (le_refl ℵ₀) (ℵ₀ : Cardinal.{w}).out (Cardinal.mk_out ℵ₀) hForces

/-- **Disproof of Erdős Problem #638 (Literal Non-Hereditary Ordinary Reading)**. -/
theorem not_erdos_638_ordinary : ¬Erdos638OrdinaryProp.{u, w} := by
  intro hProp
  apply not_erdos_638_ordinary_hereditary.{u, w}
  intro S _ hRam κ hκ
  exact hProp S hRam κ hκ

/-- **Disproof of Erdős Problem #638 (Literal Non-Hereditary Induced Reading)**. -/
theorem not_erdos_638_induced : ¬Erdos638InducedProp.{u, w} := by
  intro hProp
  apply not_erdos_638_induced_hereditary.{u, w}
  intro S _ hRam κ hκ
  exact hProp S hRam κ hκ

end Erdos638
