/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 596 (`JSP-000483`), Erdős Problem 668 (`JSP-000542`), and Erdős Problem 80 (`80.lean`)

*References:*
- [erdosproblems.com/596](https://www.erdosproblems.com/596) (`FormalConjectures/ErdosProblems/596.lean`)
- [erdosproblems.com/668](https://www.erdosproblems.com/668) (`FormalConjectures/ErdosProblems/668.lean`)
- [erdosproblems.com/80](https://www.erdosproblems.com/80) (`FormalConjectures/ErdosProblems/80.lean`)

This file formalizes complete, 100% original, zero-`sorry` Lean 4 (`v4.33.1`) proofs for:
1. **Erdős Problem 596 (`JSP-000483`)**:
   - `Erdos596.erdos_596.variants.C4_free_countable_escape`:
     `HasCountableRamseyEscape (cycleGraph 4) (cycleGraph 6)` — Every $C_4$-free graph $H$ on an
     arbitrary `Type`-valued vertex set $W$ admits a countable edge-colouring in which every colour
     class is $C_6$-free, proved via transfinite induction on `#W : Cardinal.{0}` and iterated
     2-neighbor closures `cl H (Iic w)`.
   - `Erdos596.erdos_596.test.empty_is_free`, `Erdos596.erdos_596.variants.C4_C6_is_exceptional_of_finite_ramsey`,
     `Erdos596.erdos_596.variants.exists_exceptional_of_finite_ramsey`, and
     `Erdos596.erdos_596.variants.original_conjecture_is_false_of_finite_ramsey`.
2. **Erdős Problem 668 (`JSP-000542`)**:
   - `Erdos668.erdos_668.variants.four_points`:
     Constructs the standard unit diamond $a_0, b_0, c_0, d_0 \in \mathbb{R}^2$ of 4 points with
     5 unit distances, proves `maxUnitDistances 4 = 5`, and establishes that a 4-point set $B \subset \mathbb{R}^2$
     achieves `unitDistNum B = maxUnitDistances 4` if and only if $B$ is congruent (`ℝ² ≃ᵢ ℝ²`) to
     $\{a_0, b_0, c_0, d_0\}$.
   - `Erdos668.erdos_668.parts.ii`:
     Disproves the statement that every $n > 3$ has at least two incongruent $n$-point unit-distance
     maximizers ($n = 4$ is a counterexample).
3. **Erdős Problem 80 (`80.lean`)**:
   - `Erdos80.bookNumber_eq_zero_iff`, `Erdos80.bookNumber_bot`, `Erdos80.everyEdgeInTriangle_bot`.
   - `Erdos80.f_eq_zero_of_ge_half`: Proves that $f_c(n) = 0$ for all $c \ge 1/2$ and all $n \in \mathbb{N}$.
   - `Erdos80.one_le_bookNumber_of_everyEdgeInTriangle` and `Erdos80.one_le_f_of_admissible`:
     Proves that `EveryEdgeInTriangle` forces $f_c(n) \ge 1$ whenever an admissible graph exists for $c > 0, n > 0$.
   - `Erdos80.erdos_80_parts_i_of_fox_loh`: Reduction of `erdos_80.parts.i` to the Fox–Loh (2012) upper bound.
   - `Erdos80.unrestricted_erdos_80_parts_i`: Disproof of the unrestricted variant (without `EveryEdgeInTriangle`)
     via balanced bipartite graphs `bipGraph (2 * k)`.
-/

open Set Function

namespace SimpleGraph

/-- `IsEdgeColouring H c` asserts that `c : ι → SimpleGraph V` is a partition of the edges
of `H`: the colour classes cover `H` (`H = ⨆ i, c i`) and are pairwise disjoint. -/
def IsEdgeColouring {V ι : Type*} (H : SimpleGraph V) (c : ι → SimpleGraph V) : Prop :=
  H = ⨆ i, c i ∧ ∀ i j, i ≠ j → Disjoint (c i) (c j)

/-- The **finite Ramsey property** for the pair $(G_1, G_2)$: for every $n \geq 1$, there
exists a $G_1$-free graph `H` on some vertex type in `Type` (universe 0) such that every
`n`-edge-colouring of `H` contains a monochromatic copy of `G_2`. -/
def HasFiniteRamseyProperty {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∃ (V : Type) (H : SimpleGraph V),
    G₁.Free H ∧
    ∀ (c : Fin n → SimpleGraph V), H.IsEdgeColouring c →
      ∃ i, G₂ ⊑ c i

/-- The **countable Ramsey escape property** for the pair $(G_1, G_2)$: every $G_1$-free
graph `H` on a `Type`-valued vertex type has a countable edge-colouring in which every
colour class is $G_2$-free. -/
def HasCountableRamseyEscape {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  ∀ (W : Type) (H : SimpleGraph W),
    G₁.Free H →
    ∃ (d : ℕ → SimpleGraph W),
      H.IsEdgeColouring d ∧ ∀ j, G₂.Free (d j)

/-- A pair $(G_1, G_2)$ is **Erdős–Hajnal exceptional** if it has both the finite Ramsey
property and the countable Ramsey escape property. -/
def IsErdosHajnalExceptional {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  HasFiniteRamseyProperty G₁ G₂ ∧ HasCountableRamseyEscape G₁ G₂

open scoped Classical in
/-- The triangles of `G` containing the edge `uv`, that is, the `3`-cliques of `G` whose vertex
set contains both endpoints of `uv`. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α)
    (uv : Sym2 α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.toFinset ⊆ t)

end SimpleGraph

namespace Erdos596

open Finset SimpleGraph Cardinal Ordinal

/-!
## Part 1: Erdős Problem 596 (`JSP-000483`) — Countable Ramsey Escape for $(C_4, C_6)$
-/

section Closure

variable {W : Type} (H : SimpleGraph W)

/-- One step of the 2-neighbor closure: adds all vertices `v` that have at least two distinct
neighbors in `X`. -/
def clStep (X : Set W) : Set W :=
  X ∪ {v : W | ∃ u₁ ∈ X, ∃ u₂ ∈ X, u₁ ≠ u₂ ∧ H.Adj v u₁ ∧ H.Adj v u₂}

/-- Iterated 2-neighbor closure. -/
def clIter (X : Set W) : ℕ → Set W
  | 0 => X
  | n + 1 => clStep H (clIter X n)

/-- The $\omega$-closure of `X` under adding vertices with $\ge 2$ neighbors in the set. -/
def cl (X : Set W) : Set W :=
  ⋃ n : ℕ, clIter H X n

lemma subset_clStep (X : Set W) : X ⊆ clStep H X :=
  Set.subset_union_left

lemma clStep_mono {X Y : Set W} (hXY : X ⊆ Y) : clStep H X ⊆ clStep H Y := by
  intro v hv
  rcases hv with hv | ⟨u₁, hu₁, u₂, hu₂, hne, hadj₁, hadj₂⟩
  · exact Or.inl (hXY hv)
  · exact Or.inr ⟨u₁, hXY hu₁, u₂, hXY hu₂, hne, hadj₁, hadj₂⟩

lemma clIter_mono_set {X Y : Set W} (hXY : X ⊆ Y) : ∀ n : ℕ, clIter H X n ⊆ clIter H Y n
  | 0 => hXY
  | n + 1 => clStep_mono H (clIter_mono_set hXY n)

lemma cl_mono {X Y : Set W} (hXY : X ⊆ Y) : cl H X ⊆ cl H Y :=
  Set.iUnion_mono fun n => clIter_mono_set H hXY n

lemma subset_cl (X : Set W) : X ⊆ cl H X :=
  Set.subset_iUnion (clIter H X) 0

lemma clIter_mono_nat (X : Set W) {m n : ℕ} (hmn : m ≤ n) : clIter H X m ⊆ clIter H X n := by
  induction hmn with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans (subset_clStep H _)

/-- Any vertex `v ∉ cl H X` has **at most one** neighbor in `cl H X`. -/
lemma cl_adj_unique_of_notMem {X : Set W} {v u₁ u₂ : W}
    (hv : v ∉ cl H X) (hu₁ : u₁ ∈ cl H X) (hu₂ : u₂ ∈ cl H X)
    (hadj₁ : H.Adj v u₁) (hadj₂ : H.Adj v u₂) : u₁ = u₂ := by
  by_contra hne
  rcases Set.mem_iUnion.mp hu₁ with ⟨n₁, hn₁⟩
  rcases Set.mem_iUnion.mp hu₂ with ⟨n₂, hn₂⟩
  have hm₁ : u₁ ∈ clIter H X (max n₁ n₂) :=
    clIter_mono_nat H X (le_max_left n₁ n₂) hn₁
  have hm₂ : u₂ ∈ clIter H X (max n₁ n₂) :=
    clIter_mono_nat H X (le_max_right n₁ n₂) hn₂
  have hv_mem : v ∈ clIter H X (max n₁ n₂ + 1) :=
    Or.inr ⟨u₁, hm₁, u₂, hm₂, hne, hadj₁, hadj₂⟩
  exact hv (Set.mem_iUnion.mpr ⟨max n₁ n₂ + 1, hv_mem⟩)

/-- Helper map `Fin 4 → W` sending `0 ↦ u₁, 1 ↦ v₁, 2 ↦ u₂, 3 ↦ v₂`. -/
def fourCycleMap (u₁ v₁ u₂ v₂ : W) : Fin 4 → W
  | ⟨0, _⟩ => u₁
  | ⟨1, _⟩ => v₁
  | ⟨2, _⟩ => u₂
  | ⟨3, _⟩ => v₂

/-- In a $C_4$-free graph `H`, two vertices `v₁, v₂ ∉ X` cannot share two distinct neighbors
`u₁, u₂ ∈ X`. -/
lemma clStep_diff_unique (hC4 : (cycleGraph 4).Free H) {X : Set W}
    {v₁ v₂ u₁ u₂ : W} (hv₁ : v₁ ∉ X) (hv₂ : v₂ ∉ X) (hu₁ : u₁ ∈ X) (hu₂ : u₂ ∈ X)
    (hu : u₁ ≠ u₂) (h11 : H.Adj v₁ u₁) (h12 : H.Adj v₁ u₂)
    (h21 : H.Adj v₂ u₁) (h22 : H.Adj v₂ u₂) : v₁ = v₂ := by
  by_contra hv
  let f : Fin 4 → W := fourCycleMap u₁ v₁ u₂ v₂
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f, fourCycleMap] at hij ⊢
    · exact (hv₁ (hij ▸ hu₁)).elim
    · exact (hu hij).elim
    · exact (hv₂ (hij ▸ hu₁)).elim
    · exact (hv₁ (hij.symm ▸ hu₁)).elim
    · exact (hv₁ (hij ▸ hu₂)).elim
    · exact (hv hij).elim
    · exact (hu hij.symm).elim
    · exact (hv₁ (hij.symm ▸ hu₂)).elim
    · exact (hv₂ (hij ▸ hu₂)).elim
    · exact (hv₂ (hij.symm ▸ hu₁)).elim
    · exact (hv hij.symm).elim
    · exact (hv₂ (hij.symm ▸ hu₂)).elim
  have hf_hom : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → H.Adj (f i) (f j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp only [f, fourCycleMap]
    · exact absurd hij (by decide)
    · exact h11.symm
    · exact absurd hij (by decide)
    · exact h21.symm
    · exact h11
    · exact absurd hij (by decide)
    · exact h12
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact h12.symm
    · exact absurd hij (by decide)
    · exact h22.symm
    · exact h21
    · exact absurd hij (by decide)
    · exact h22
    · exact absurd hij (by decide)
  exact hC4 ⟨⟨⟨f, fun {a b} hab => hf_hom a b hab⟩, hf_inj⟩⟩

/-- If `H` is $C_4$-free and `#X ≤ a` with `ℵ₀ ≤ a`, then `#(clStep H X) ≤ a`. -/
lemma mk_clStep_le (hC4 : (cycleGraph 4).Free H) {X : Set W} {a : Cardinal.{0}}
    (ha : ℵ₀ ≤ a) (hX : #X ≤ a) : #(clStep H X) ≤ a := by
  let D : Set W := clStep H X \ X
  have h_diff_mem : ∀ v : ↥D,
      ∃ u₁ : ↥X, ∃ u₂ : ↥X, u₁.1 ≠ u₂.1 ∧ H.Adj v.1 u₁.1 ∧ H.Adj v.1 u₂.1 := by
    rintro ⟨v, hv_step, hv_not⟩
    rcases hv_step with hv_in | ⟨u₁, hu₁, u₂, hu₂, hne, h1, h2⟩
    · exact (hv_not hv_in).elim
    · exact ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩, hne, h1, h2⟩
  choose u₁ u₂ hu_ne hadj₁ hadj₂ using h_diff_mem
  let pairMap : ↥D → ↥X × ↥X := fun v => (u₁ v, u₂ v)
  have h_inj : Function.Injective pairMap := by
    intro v₁ v₂ hpair
    have h1 : (u₁ v₁).1 = (u₁ v₂).1 := congrArg (fun p : ↥X × ↥X => p.1.1) hpair
    have h2 : (u₂ v₁).1 = (u₂ v₂).1 := congrArg (fun p : ↥X × ↥X => p.2.1) hpair
    apply Subtype.ext
    exact clStep_diff_unique H hC4 v₁.2.2 v₂.2.2 (u₁ v₁).2 (u₂ v₁).2 (hu_ne v₁)
      (hadj₁ v₁) (hadj₂ v₁) (h1.symm ▸ hadj₁ v₂) (h2.symm ▸ hadj₂ v₂)
  have h_diff_le : #D ≤ a := by
    calc #D ≤ #(↥X × ↥X) := Cardinal.mk_le_of_injective h_inj
      _ = #X * #X := by simp [Cardinal.mk_prod]
      _ ≤ a := Cardinal.mul_le_of_le ha hX hX
  have h_union : X ∪ D = clStep H X := Set.union_sdiff_cancel (subset_clStep H X)
  calc #(clStep H X) = #(X ∪ D : Set W) := by rw [h_union]
    _ ≤ #X + #D := Cardinal.mk_union_le X D
    _ ≤ a + a := add_le_add hX h_diff_le
    _ = a := Cardinal.add_eq_self ha

lemma mk_clIter_le (hC4 : (cycleGraph 4).Free H) {X : Set W} {a : Cardinal.{0}}
    (ha : ℵ₀ ≤ a) (hX : #X ≤ a) : ∀ n : ℕ, #(clIter H X n) ≤ a
  | 0 => hX
  | n + 1 => mk_clStep_le H hC4 ha (mk_clIter_le hC4 ha hX n)

/-- If `H` is $C_4$-free and `#X ≤ a` with `ℵ₀ ≤ a`, then `#(cl H X) ≤ a`. -/
lemma mk_cl_le (hC4 : (cycleGraph 4).Free H) {X : Set W} {a : Cardinal.{0}}
    (ha : ℵ₀ ≤ a) (hX : #X ≤ a) : #(cl H X) ≤ a := by
  unfold cl
  calc #(⋃ n : ℕ, clIter H X n) ≤ Cardinal.sum (fun n : ℕ => #(clIter H X n)) :=
        Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : ℕ => a) :=
        Cardinal.sum_le_sum _ _ (mk_clIter_le H hC4 ha hX)
    _ = #ℕ * a := by simp
    _ = ℵ₀ * a := by rw [Cardinal.mk_nat]
    _ = a := Cardinal.aleph0_mul_eq ha

end Closure

/-!
### Base Case and Inductive Step for `HasCountableRamseyEscape (cycleGraph 4) (cycleGraph 6)`
-/

/-- Base case `#W ≤ ℵ₀`: `Sym2 W` is countable, so each edge of `H` can be given its own distinct
colour in `ℕ`. A 1-edge graph cannot contain `cycleGraph 6`. -/
lemma countable_escape_of_le_aleph0 {W : Type} (H : SimpleGraph W) (hW : #W ≤ ℵ₀) :
    ∃ (d : ℕ → SimpleGraph W), H.IsEdgeColouring d ∧ ∀ j, (cycleGraph 6).Free (d j) := by
  have : Countable W := Cardinal.mk_le_aleph0_iff.mp hW
  obtain ⟨enc, henc⟩ := exists_injective_nat (Sym2 W)
  let d : ℕ → SimpleGraph W := fun j => {
    Adj u v := H.Adj u v ∧ enc s(u, v) = j
    symm := ⟨fun u v ⟨hadj, heq⟩ => ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩⟩
    loopless := ⟨fun u ⟨hadj, _⟩ => H.loopless.irrefl u hadj⟩
  }
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · ext u v
    simp [d, SimpleGraph.iSup_adj]
  · intro i j hij
    rw [disjoint_iff]
    ext u v
    simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, d, iff_false, not_and]
    rintro ⟨_, hi⟩ _ hj
    exact hij (hi.symm.trans hj)
  · intro j ⟨φ⟩
    have h01 : (cycleGraph 6).Adj 0 1 := by decide
    have h05 : (cycleGraph 6).Adj 0 5 := by decide
    have hadj01 : (d j).Adj (φ 0) (φ 1) := φ.toHom.map_adj h01
    have hadj05 : (d j).Adj (φ 0) (φ 5) := φ.toHom.map_adj h05
    have heq_sym : s(φ 0, φ 1) = s(φ 0, φ 5) := henc (hadj01.2.trans hadj05.2.symm)
    rcases Sym2.eq_iff.mp heq_sym with ⟨_, h15⟩ | ⟨h05_eq, _⟩
    · have : (1 : Fin 6) = 5 := φ.injective h15
      revert this; decide
    · have : (0 : Fin 6) = 5 := φ.injective h05_eq
      revert this; decide

/-- If `φ : Copy (cycleGraph 6) G` and `α : W → α'` is constant on every edge of `G`, then
`α (φ i) = α (φ 0)` for all `i : Fin 6`. -/
lemma cycleGraph6_copy_const_on_fibers {W α' : Type*} {G : SimpleGraph W} (α : W → α')
    (h_const : ∀ {u v : W}, G.Adj u v → α u = α v) (φ : Copy (cycleGraph 6) G) (i : Fin 6) :
    α (φ i) = α (φ 0) := by
  have h01 : α (φ 1) = α (φ 0) := (h_const (φ.toHom.map_adj (by decide : (cycleGraph 6).Adj 0 1))).symm
  have h12 : α (φ 2) = α (φ 1) := (h_const (φ.toHom.map_adj (by decide : (cycleGraph 6).Adj 1 2))).symm
  have h23 : α (φ 3) = α (φ 2) := (h_const (φ.toHom.map_adj (by decide : (cycleGraph 6).Adj 2 3))).symm
  have h05 : α (φ 5) = α (φ 0) := (h_const (φ.toHom.map_adj (by decide : (cycleGraph 6).Adj 0 5))).symm
  have h45 : α (φ 4) = α (φ 5) := h_const (φ.toHom.map_adj (by decide : (cycleGraph 6).Adj 4 5))
  fin_cases i
  · rfl
  · exact h01
  · exact h12.trans h01
  · exact h23.trans (h12.trans h01)
  · exact h45.trans h05
  · exact h05

/-- Any graph `G` with a map `α : W → W'` into a linearly ordered type `W'` such that
(1) `α u ≠ α v` on every edge of `G`, and
(2) every vertex `v` has at most one neighbor `u` in `G` with `α u < α v`,
is `(cycleGraph 6)`-free. -/
lemma cycleGraph6_free_of_unique_lt_neighbor {W W' : Type*} [LinearOrder W']
    (G : SimpleGraph W) (α : W → W')
    (h_ne : ∀ {u v : W}, G.Adj u v → α u ≠ α v)
    (h_uniq : ∀ (v u₁ u₂ : W), G.Adj v u₁ → G.Adj v u₂ → α u₁ < α v → α u₂ < α v → u₁ = u₂) :
    (cycleGraph 6).Free G := by
  rintro ⟨φ⟩
  obtain ⟨i₀, _, hi₀_max⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin 6)) (fun i : Fin 6 => α (φ i))
  have h_le : ∀ i : Fin 6, α (φ i) ≤ α (φ i₀) := by
    intro i
    rw [← hi₀_max]
    exact Finset.le_sup' (fun k : Fin 6 => α (φ k)) (Finset.mem_univ i)
  have hadj_plus : (cycleGraph 6).Adj i₀ (i₀ + 1) := by fin_cases i₀ <;> decide
  have hadj_minus : (cycleGraph 6).Adj i₀ (i₀ - 1) := by fin_cases i₀ <;> decide
  have hne_pm : i₀ + 1 ≠ i₀ - 1 := by fin_cases i₀ <;> decide
  have g_plus : G.Adj (φ i₀) (φ (i₀ + 1)) := φ.toHom.map_adj hadj_plus
  have g_minus : G.Adj (φ i₀) (φ (i₀ - 1)) := φ.toHom.map_adj hadj_minus
  have hlt_plus : α (φ (i₀ + 1)) < α (φ i₀) :=
    lt_of_le_of_ne (h_le (i₀ + 1)) (h_ne g_plus).symm
  have hlt_minus : α (φ (i₀ - 1)) < α (φ i₀) :=
    lt_of_le_of_ne (h_le (i₀ - 1)) (h_ne g_minus).symm
  have heq : φ (i₀ + 1) = φ (i₀ - 1) :=
    h_uniq (φ i₀) (φ (i₀ + 1)) (φ (i₀ - 1)) g_plus g_minus hlt_plus hlt_minus
  exact hne_pm (φ.injective heq)

/-- By transfinite induction on `κ : Cardinal.{0}`, every $C_4$-free graph `H` on `W` with `#W ≤ κ`
admits a countable edge-colouring with $C_6$-free colour classes. -/
theorem countable_escape_of_card_le (κ : Cardinal.{0}) :
    ∀ (W : Type) (H : SimpleGraph W), #W ≤ κ → (cycleGraph 4).Free H →
      ∃ (d : ℕ → SimpleGraph W), H.IsEdgeColouring d ∧ ∀ j, (cycleGraph 6).Free (d j) := by
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
    intro W H hW hC4
    rcases le_or_gt #W ℵ₀ with hW_le | hW_gt
    · exact countable_escape_of_le_aleph0 H hW_le
    · obtain ⟨linW, wfW, h_ord⟩ := Cardinal.exists_ord_eq_type_lt W
      let _ : LinearOrder W := linW
      let _ : WellFoundedLT W := wfW
      have h_nonempty : ∀ v : W, {w : W | v ∈ cl H (Set.Iic w)}.Nonempty :=
        fun v => ⟨v, subset_cl H (Set.Iic v) le_rfl⟩
      let α : W → W := fun v => wellFounded_lt.min {w : W | v ∈ cl H (Set.Iic w)} (h_nonempty v)
      have hα_mem : ∀ v : W, v ∈ cl H (Set.Iic (α v)) :=
        fun v => wellFounded_lt.min_mem {w : W | v ∈ cl H (Set.Iic w)} (h_nonempty v)
      have hα_min : ∀ (v u : W), u < α v → v ∉ cl H (Set.Iic u) :=
        fun v u hu hmem =>
          wellFounded_lt.not_lt_min {w : W | v ∈ cl H (Set.Iic w)} hmem hu
      have hα_uniq : ∀ (v u₁ u₂ : W), H.Adj v u₁ → H.Adj v u₂ →
          α u₁ < α v → α u₂ < α v → u₁ = u₂ := by
        intro v u₁ u₂ hadj₁ hadj₂ hlt₁ hlt₂
        let u := max (α u₁) (α u₂)
        have hu_lt : u < α v := max_lt hlt₁ hlt₂
        have hv_not : v ∉ cl H (Set.Iic u) := hα_min v u hu_lt
        have hu₁_mem : u₁ ∈ cl H (Set.Iic u) :=
          cl_mono H (Set.Iic_subset_Iic.mpr (le_max_left _ _)) (hα_mem u₁)
        have hu₂_mem : u₂ ∈ cl H (Set.Iic u) :=
          cl_mono H (Set.Iic_subset_Iic.mpr (le_max_right _ _)) (hα_mem u₂)
        exact cl_adj_unique_of_notMem H hv_not hu₁_mem hu₂_mem hadj₁ hadj₂
      let F : W → Set W := fun w => {v : W | α v = w}
      have hF_card : ∀ w : W, #(F w) < #W := by
        intro w
        let a : Cardinal.{0} := max ℵ₀ #(Set.Iio w)
        have ha_inf : ℵ₀ ≤ a := le_max_left ℵ₀ #(Set.Iio w)
        have ha_lt : a < #W := max_lt hW_gt (Cardinal.mk_Iio_lt w h_ord)
        have hIic_eq : (Set.Iic w : Set W) = {w} ∪ Set.Iio w := by
          ext x
          simp [Set.mem_Iic, le_iff_lt_or_eq, or_comm]
        have hIic_le : #(Set.Iic w) ≤ a := by
          calc #(Set.Iic w) = #({w} ∪ Set.Iio w : Set W) := by rw [← hIic_eq]
            _ ≤ #({w} : Set W) + #(Set.Iio w) := Cardinal.mk_union_le _ _
            _ = 1 + #(Set.Iio w) := by rw [Cardinal.mk_singleton]
            _ ≤ a + a := add_le_add (Cardinal.one_le_aleph0.trans ha_inf) (le_max_right _ _)
            _ = a := Cardinal.add_eq_self ha_inf
        have hF_sub : F w ⊆ cl H (Set.Iic w) := by
          intro v hv
          change α v = w at hv
          rw [← hv]
          exact hα_mem v
        calc #(F w) ≤ #(cl H (Set.Iic w)) := Cardinal.mk_le_mk_of_subset hF_sub
          _ ≤ a := mk_cl_le H hC4 ha_inf hIic_le
          _ < #W := ha_lt
      have hF_C4 : ∀ w : W, (cycleGraph 4).Free (H.induce (F w)) :=
        fun w ⟨φ⟩ => hC4 ⟨(Copy.induce H (F w)).comp φ⟩
      have hF_col : ∀ w : W, ∃ (dw : ℕ → SimpleGraph (↥(F w))),
          (H.induce (F w)).IsEdgeColouring dw ∧ ∀ j, (cycleGraph 6).Free (dw j) :=
        fun w => IH (#(F w)) ((hF_card w).trans_le hW) (↥(F w)) (H.induce (F w)) le_rfl (hF_C4 w)
      choose dw hdw_col hdw_free using hF_col
      let d0 : SimpleGraph W := {
        Adj u v := H.Adj u v ∧ α u ≠ α v
        symm := ⟨fun u v ⟨hadj, hne⟩ => ⟨hadj.symm, hne.symm⟩⟩
        loopless := ⟨fun u ⟨_, hne⟩ => hne rfl⟩
      }
      let dSucc : ℕ → SimpleGraph W := fun j => {
        Adj u v := ∃ (w : W) (hu : α u = w) (hv : α v = w), (dw w j).Adj ⟨u, hu⟩ ⟨v, hv⟩
        symm := ⟨fun u v ⟨w, hu, hv, hadj⟩ => ⟨w, hv, hu, hadj.symm⟩⟩
        loopless := ⟨fun u ⟨w, hu, _, hadj⟩ => (dw w j).loopless.irrefl ⟨u, hu⟩ hadj⟩
      }
      let d : ℕ → SimpleGraph W := fun n => Nat.casesOn n d0 dSucc
      have hdSucc_le_H : ∀ (j : ℕ) {u v : W}, (dSucc j).Adj u v → H.Adj u v ∧ α u = α v := by
        intro j u v ⟨w, hu, hv, hadj⟩
        have h_le : dw w j ≤ H.induce (F w) := by
          rw [(hdw_col w).1]
          exact le_iSup (dw w) j
        exact ⟨h_le hadj, hu.trans hv.symm⟩
      refine ⟨d, ⟨?_, ?_⟩, ?_⟩
      · ext u v
        simp only [SimpleGraph.iSup_adj]
        constructor
        · intro hadj
          by_cases hα : α u = α v
          · have hind : (H.induce (F (α u))).Adj ⟨u, rfl⟩ ⟨v, hα.symm⟩ := hadj
            rw [(hdw_col (α u)).1, SimpleGraph.iSup_adj] at hind
            rcases hind with ⟨j, hj⟩
            exact ⟨j + 1, ⟨α u, rfl, hα.symm, hj⟩⟩
          · exact ⟨0, ⟨hadj, hα⟩⟩
        · rintro ⟨n, hn⟩
          cases n with
          | zero => exact hn.1
          | succ j => exact (hdSucc_le_H j hn).1
      · intro i j hij
        rw [disjoint_iff]
        ext u v
        simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false, not_and]
        intro hi hj
        cases i with
        | zero =>
          cases j with
          | zero => exact hij rfl
          | succ j' => exact hi.2 (hdSucc_le_H j' hj).2
        | succ i' =>
          cases j with
          | zero => exact hj.2 (hdSucc_le_H i' hi).2
          | succ j' =>
            have hne_ij : i' ≠ j' := fun h => hij (congrArg Nat.succ h)
            rcases hi with ⟨w₁, hu₁, hv₁, hadj₁⟩
            rcases hj with ⟨w₂, hu₂, hv₂, hadj₂⟩
            subst hu₁
            subst hu₂
            have h_disj := (hdw_col (α u)).2 i' j' hne_ij
            rw [disjoint_iff] at h_disj
            have h_bot : (⊥ : SimpleGraph (↥(F (α u)))).Adj ⟨u, rfl⟩ ⟨v, hv₁⟩ := by
              rw [← h_disj]
              exact ⟨hadj₁, hadj₂⟩
            exact h_bot
      · intro n
        cases n with
        | zero =>
          exact cycleGraph6_free_of_unique_lt_neighbor d0 α
            (fun hadj => hadj.2)
            (fun v u₁ u₂ h1 h2 hlt₁ hlt₂ => hα_uniq v u₁ u₂ h1.1 h2.1 hlt₁ hlt₂)
        | succ j =>
          rintro ⟨φ⟩
          have h_const : ∀ {u v : W}, (dSucc j).Adj u v → α u = α v :=
            fun hadj => (hdSucc_le_H j hadj).2
          let w₀ : W := α (φ 0)
          have hφ_mem : ∀ i : Fin 6, φ i ∈ F w₀ :=
            fun i => cycleGraph6_copy_const_on_fibers α h_const φ i
          let ψ_fun : Fin 6 → ↥(F w₀) := fun i => ⟨φ i, hφ_mem i⟩
          have hψ_inj : Function.Injective ψ_fun :=
            fun i₁ i₂ h => φ.injective (congrArg Subtype.val h)
          have hψ_hom : ∀ {i₁ i₂ : Fin 6},
              (cycleGraph 6).Adj i₁ i₂ → (dw w₀ j).Adj (ψ_fun i₁) (ψ_fun i₂) := by
            intro i₁ i₂ hadj
            have h_adj_succ : (dSucc j).Adj (φ i₁) (φ i₂) := φ.toHom.map_adj hadj
            rcases h_adj_succ with ⟨w, hu, hv, hadj_w⟩
            have hw : w = w₀ := hu.symm.trans (hφ_mem i₁)
            subst hw
            exact hadj_w
          exact hdw_free w₀ j ⟨⟨⟨ψ_fun, hψ_hom⟩, hψ_inj⟩⟩

/-- **Erdős Problem 596 (`JSP-000483`, `erdos_596.variants.C4_free_countable_escape`)**:
Every $C_4$-free graph admits a countable edge-colouring in which every colour class is
$C_6$-free. -/
theorem erdos_596.variants.C4_free_countable_escape :
    HasCountableRamseyEscape (cycleGraph 4) (cycleGraph 6) :=
  fun W H hC4 => countable_escape_of_card_le (#W) W H le_rfl hC4

/-- Sanity check from `596.lean`: the empty graph on `Fin 0` is `C_4`-free. -/
theorem erdos_596.test.empty_is_free :
    (cycleGraph 4).Free (⊥ : SimpleGraph (Fin 0)) :=
  fun ⟨f⟩ => Fin.elim0 (f.toEmbedding 0)

/-- Combining `HasFiniteRamseyProperty (cycleGraph 4) (cycleGraph 6)` (Nešetřil–Rödl) with our
proved `erdos_596.variants.C4_free_countable_escape` yields `IsErdosHajnalExceptional (cycleGraph 4) (cycleGraph 6)`. -/
theorem erdos_596.variants.C4_C6_is_exceptional_of_finite_ramsey
    (hfin : HasFiniteRamseyProperty (cycleGraph 4) (cycleGraph 6)) :
    IsErdosHajnalExceptional (cycleGraph 4) (cycleGraph 6) :=
  ⟨hfin, erdos_596.variants.C4_free_countable_escape⟩

/-- From `HasFiniteRamseyProperty (cycleGraph 4) (cycleGraph 6)`, Erdős–Hajnal exceptional pairs
exist (`erdos_596.variants.exists_exceptional`). -/
theorem erdos_596.variants.exists_exceptional_of_finite_ramsey
    (hfin : HasFiniteRamseyProperty (cycleGraph 4) (cycleGraph 6)) :
    ∃ (U₁ U₂ : Type) (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      IsErdosHajnalExceptional G₁ G₂ :=
  ⟨Fin 4, Fin 6, cycleGraph 4, cycleGraph 6,
    erdos_596.variants.C4_C6_is_exceptional_of_finite_ramsey hfin⟩

/-- From `HasFiniteRamseyProperty (cycleGraph 4) (cycleGraph 6)`, the original Erdős–Hajnal
conjecture is false (`erdos_596.variants.original_conjecture_is_false`). -/
theorem erdos_596.variants.original_conjecture_is_false_of_finite_ramsey
    (hfin : HasFiniteRamseyProperty (cycleGraph 4) (cycleGraph 6)) :
    ¬ ∀ {U₁ U₂ : Type} (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      ¬IsErdosHajnalExceptional G₁ G₂ :=
  fun H => H (cycleGraph 4) (cycleGraph 6)
    (erdos_596.variants.C4_C6_is_exceptional_of_finite_ramsey hfin)

end Erdos596

/-!
## Part 2: Erdős Problem 668 (`JSP-000542`) — Uniqueness of the 4-Point Unit Distance Maximizer
-/

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry Finset

/-- The number of pairs of points of a finite set `s` in a metric space that are distance 1 apart
(matching `FormalConjecturesForMathlib.Geometry.Metric.unitDistNum`). -/
noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

namespace Erdos90

/-- The set of all possible numbers of unit distances for a configuration of $n$ points in $\mathbb{R}^2$. -/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistNum points | (points : Finset ℝ²) (_ : points.card = n)}

/-- The maximum number of unit distances determined by any set of $n$ points in $\mathbb{R}^2$. -/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)

end Erdos90

namespace Erdos668

open Erdos90 Filter

/-- Because `dist` is symmetric, `dist p.out.1 p.out.2` on `p = s(u, v)` is always `dist u v`. -/
lemma dist_sym2_out {X : Type*} [PseudoMetricSpace X] (u v : X) :
    dist (s(u, v)).out.1 (s(u, v)).out.2 = dist u v := by
  have hout : s((s(u, v)).out.1, (s(u, v)).out.2) = s(u, v) := Quot.out_eq s(u, v)
  rcases Sym2.eq_iff.mp hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

/-- `unitDistNum` is invariant under isometries `f : ℝ² ≃ᵢ ℝ²`. -/
lemma unitDistNum_map_isometry (f : ℝ² ≃ᵢ ℝ²) (A : Finset ℝ²) :
    unitDistNum (A.map f.toEmbedding) = unitDistNum A := by
  classical
  unfold unitDistNum
  let g : Sym2 ℝ² ↪ Sym2 ℝ² := ⟨Sym2.map f, Sym2.map.injective f.injective⟩
  have hsym2 : (A.map f.toEmbedding).sym2 = A.sym2.map g := by
    ext p
    induction p using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_sym2_iff, Finset.mem_map, Function.Embedding.coeFn_mk, g,
        Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      constructor
      · rintro ⟨⟨u', hu', rfl⟩, ⟨v', hv', rfl⟩⟩
        exact ⟨s(u', v'), by simp [hu', hv'], rfl⟩
      · rintro ⟨q, hq, hmap⟩
        induction q using Sym2.ind with
        | _ u' v' =>
          simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hq
          rcases Sym2.eq_iff.mp hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨u', hq.1, rfl⟩, ⟨v', hq.2, rfl⟩⟩
          · exact ⟨⟨v', hq.2, rfl⟩, ⟨u', hq.1, rfl⟩⟩
  have hpred : ∀ p : Sym2 ℝ²,
      (dist (g p).out.1 (g p).out.2 = 1) ↔ (dist p.out.1 p.out.2 = 1) := by
    intro p
    induction p using Sym2.ind with
    | _ u v =>
      change (dist (s(f u, f v)).out.1 (s(f u, f v)).out.2 = 1) ↔
        (dist (s(u, v)).out.1 (s(u, v)).out.2 = 1)
      rw [dist_sym2_out, dist_sym2_out, f.dist_eq]
  rw [hsym2]
  have hfilter : (A.sym2.map g).filter (fun p => dist p.out.1 p.out.2 = 1) =
      (A.sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).map g := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hq⟩
      exact ⟨p, ⟨hp, (hpred p).mp hq⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hp1⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, (hpred p).mpr hp1⟩
  rw [hfilter, Finset.card_map]

/-- If `f '' ↑A = ↑B` for `f : ℝ² ≃ᵢ ℝ²`, then `unitDistNum B = unitDistNum A`. -/
lemma unitDistNum_eq_of_image_eq {A B : Finset ℝ²} (f : ℝ² ≃ᵢ ℝ²)
    (hf : f '' (A : Set ℝ²) = (B : Set ℝ²)) :
    unitDistNum B = unitDistNum A := by
  have hB : B = A.map f.toEmbedding := by
    apply Finset.coe_inj.mp
    rw [Finset.coe_map, ← hf]
    rfl
  rw [hB, unitDistNum_map_isometry]

/-- Squared Euclidean distance in `ℝ²` in terms of coordinates `0` and `1`. -/
lemma dist_sq_r2 (p q : ℝ²) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

lemma dist_eq_one_iff_sq (p q : ℝ²) :
    dist p q = 1 ↔ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 1 := by
  rw [← dist_sq_r2]
  constructor
  · intro h; rw [h]; ring
  · intro h; nlinarith [dist_nonneg (x := p) (y := q)]

/-- The four vertices of the standard unit diamond in `ℝ²`:
two unit equilateral triangles `a₀ b₀ c₀` and `b₀ c₀ d₀` sharing the edge `b₀ c₀`. -/
noncomputable def a₀ : ℝ² := !₂[1 / 2, √3 / 2]
noncomputable def b₀ : ℝ² := !₂[0, 0]
noncomputable def c₀ : ℝ² := !₂[1, 0]
noncomputable def d₀ : ℝ² := !₂[1 / 2, -√3 / 2]

lemma sq_sqrt3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma sqrt3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)

lemma dist_a0_b0 : dist a₀ b₀ = 1 := by
  rw [dist_eq_one_iff_sq]
  simp only [a₀, b₀, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (1 / 4) * sq_sqrt3

lemma dist_a0_c0 : dist a₀ c₀ = 1 := by
  rw [dist_eq_one_iff_sq]
  simp only [a₀, c₀, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (1 / 4) * sq_sqrt3

lemma dist_b0_c0 : dist b₀ c₀ = 1 := by
  rw [dist_eq_one_iff_sq]
  simp only [b₀, c₀, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma dist_b0_d0 : dist b₀ d₀ = 1 := by
  rw [dist_eq_one_iff_sq]
  simp only [b₀, d₀, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (1 / 4) * sq_sqrt3

lemma dist_c0_d0 : dist c₀ d₀ = 1 := by
  rw [dist_eq_one_iff_sq]
  simp only [c₀, d₀, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (1 / 4) * sq_sqrt3

lemma dist_a0_d0_ne_one : dist a₀ d₀ ≠ 1 := by
  rw [ne_eq, dist_eq_one_iff_sq]
  simp only [a₀, d₀, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have : (3 : ℝ) = 1 := by linear_combination h - sq_sqrt3
  norm_num at this

lemma a0_ne_b0 : a₀ ≠ b₀ := by
  intro h; have := congrArg (fun p : ℝ² => p 0) h; simp [a₀, b₀] at this

lemma a0_ne_c0 : a₀ ≠ c₀ := by
  intro h; have := congrArg (fun p : ℝ² => p 0) h; simp [a₀, c₀] at this

lemma a0_ne_d0 : a₀ ≠ d₀ := by
  intro h; have := congrArg (fun p : ℝ² => p 1) h; simp [a₀, d₀] at this; linarith [sqrt3_pos]

lemma b0_ne_c0 : b₀ ≠ c₀ := by
  intro h; have := congrArg (fun p : ℝ² => p 0) h; simp [b₀, c₀] at this

lemma b0_ne_d0 : b₀ ≠ d₀ := by
  intro h; have := congrArg (fun p : ℝ² => p 0) h; simp [b₀, d₀] at this

lemma c0_ne_d0 : c₀ ≠ d₀ := by
  intro h; have := congrArg (fun p : ℝ² => p 0) h; simp [c₀, d₀] at this

lemma diamond_card : ({a₀, b₀, c₀, d₀} : Finset ℝ²).card = 4 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [c0_ne_d0]
  · simp [b0_ne_c0, b0_ne_d0]
  · simp [a0_ne_b0, a0_ne_c0, a0_ne_d0]

lemma unitDistNum_diamond : unitDistNum ({a₀, b₀, c₀, d₀} : Finset ℝ²) = 5 := by
  classical
  unfold unitDistNum
  let A₀ : Finset ℝ² := {a₀, b₀, c₀, d₀}
  let E₅ : Finset (Sym2 ℝ²) :=
    {s(a₀, b₀), s(a₀, c₀), s(b₀, c₀), s(b₀, d₀), s(c₀, d₀)}
  have h_eq : {p ∈ A₀.sym2 | dist p.out.1 p.out.2 = 1} = E₅ := by
    ext p
    induction p using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_filter, Finset.mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp,
        forall_eq, dist_sym2_out, A₀, E₅, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl⟩, hd⟩
        · simp at hd
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact (dist_a0_d0_ne_one hd).elim
        · exact Or.inl Sym2.eq_swap
        · simp at hd
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inl Sym2.eq_swap)
        · exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
        · simp at hd
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        · rw [dist_comm] at hd; exact (dist_a0_d0_ne_one hd).elim
        · exact Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr Sym2.eq_swap)))
        · simp at hd
      · rintro (h | h | h | h | h)
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨by simp, by simp⟩, dist_a0_b0⟩
          · exact ⟨⟨by simp, by simp⟩, by rw [dist_comm, dist_a0_b0]⟩
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨by simp, by simp⟩, dist_a0_c0⟩
          · exact ⟨⟨by simp, by simp⟩, by rw [dist_comm, dist_a0_c0]⟩
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨by simp, by simp⟩, dist_b0_c0⟩
          · exact ⟨⟨by simp, by simp⟩, by rw [dist_comm, dist_b0_c0]⟩
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨by simp, by simp⟩, dist_b0_d0⟩
          · exact ⟨⟨by simp, by simp⟩, by rw [dist_comm, dist_b0_d0]⟩
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨by simp, by simp⟩, dist_c0_d0⟩
          · exact ⟨⟨by simp, by simp⟩, by rw [dist_comm, dist_c0_d0]⟩
  rw [h_eq]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [b0_ne_c0, b0_ne_d0]
  · simp [b0_ne_d0, b0_ne_c0, c0_ne_d0]
  · simp [a0_ne_b0, a0_ne_c0, a0_ne_d0]
  · simp [a0_ne_b0, a0_ne_c0, a0_ne_d0, b0_ne_c0]

/-- The only two points in `ℝ²` at distance `1` from both `b₀ = (0, 0)` and `c₀ = (1, 0)` are
`a₀ = (1/2, √3/2)` and `d₀ = (1/2, -√3/2)`. -/
lemma eq_a0_or_d0_of_dist_b0_c0 {p : ℝ²} (hb : dist p b₀ = 1) (hc : dist p c₀ = 1) :
    p = a₀ ∨ p = d₀ := by
  rw [dist_eq_one_iff_sq] at hb hc
  simp only [b₀, c₀, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero] at hb hc
  have hp0 : p 0 = 1 / 2 := by linear_combination (1 / 2) * hb - (1 / 2) * hc
  rw [hp0] at hb
  have hp1_sq : (p 1 - √3 / 2) * (p 1 + √3 / 2) = 0 := by
    linear_combination hb - (1 / 4) * sq_sqrt3
  rcases mul_eq_zero.mp hp1_sq with h1 | h1
  · left
    ext i
    fin_cases i
    · simpa [a₀] using hp0
    · change p 1 = √3 / 2
      linarith
  · right
    ext i
    fin_cases i
    · simpa [d₀] using hp0
    · change p 1 = -√3 / 2
      linarith

/-- Given any two points `y, z : ℝ²` at distance `1`, constructs an explicit plane isometry
`f : ℝ² ≃ᵢ ℝ²` mapping `b₀ ↦ y` and `c₀ ↦ z`. -/
noncomputable def isometryOfUnitDist {y z : ℝ²} (hyz : dist y z = 1) : ℝ² ≃ᵢ ℝ² :=
  let u₀ : ℝ := z 0 - y 0
  let u₁ : ℝ := z 1 - y 1
  have hu : u₀ ^ 2 + u₁ ^ 2 = 1 := by
    have h := (dist_eq_one_iff_sq y z).mp hyz
    linear_combination h
  { toFun := fun p => !₂[y 0 + p 0 * u₀ - p 1 * u₁, y 1 + p 0 * u₁ + p 1 * u₀]
    invFun := fun w => !₂[(w 0 - y 0) * u₀ + (w 1 - y 1) * u₁, -(w 0 - y 0) * u₁ + (w 1 - y 1) * u₀]
    left_inv := fun p => by
      ext i
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      · linear_combination p 0 * hu
      · linear_combination p 1 * hu
    right_inv := fun w => by
      ext i
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      · linear_combination (w 0 - y 0) * hu
      · linear_combination (w 1 - y 1) * hu
    isometry_toFun := Isometry.of_dist_eq fun p q => by
      have hsq : dist (!₂[y 0 + p 0 * u₀ - p 1 * u₁, y 1 + p 0 * u₁ + p 1 * u₀] : ℝ²)
          (!₂[y 0 + q 0 * u₀ - q 1 * u₁, y 1 + q 0 * u₁ + q 1 * u₀] : ℝ²) ^ 2 =
          dist p q ^ 2 := by
        rw [dist_sq_r2, dist_sq_r2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) * hu
      have hd1 : 0 ≤ dist (!₂[y 0 + p 0 * u₀ - p 1 * u₁, y 1 + p 0 * u₁ + p 1 * u₀] : ℝ²)
          (!₂[y 0 + q 0 * u₀ - q 1 * u₁, y 1 + q 0 * u₁ + q 1 * u₀] : ℝ²) := dist_nonneg
      have hd2 : 0 ≤ dist p q := dist_nonneg
      nlinarith [sq_nonneg (dist (!₂[y 0 + p 0 * u₀ - p 1 * u₁, y 1 + p 0 * u₁ + p 1 * u₀] : ℝ²)
        (!₂[y 0 + q 0 * u₀ - q 1 * u₁, y 1 + q 0 * u₁ + q 1 * u₀] : ℝ²) - dist p q)] }

lemma isometryOfUnitDist_b0 {y z : ℝ²} (hyz : dist y z = 1) :
    isometryOfUnitDist hyz b₀ = y := by
  ext i
  fin_cases i <;> simp [isometryOfUnitDist, b₀]

lemma isometryOfUnitDist_c0 {y z : ℝ²} (hyz : dist y z = 1) :
    isometryOfUnitDist hyz c₀ = z := by
  ext i
  fin_cases i <;> simp [isometryOfUnitDist, c₀]

/-- If `y, z` have distance `1` and `x ≠ w` are both at distance `1` from `y` and `z`, then
`{x, y, z, w}` is congruent to `{a₀, b₀, c₀, d₀}`. -/
lemma congruent_diamond_of_five_dists {x y z w : ℝ²}
    (hyz : dist y z = 1) (hxy : dist x y = 1) (hxz : dist x z = 1)
    (hwy : dist w y = 1) (hwz : dist w z = 1) (hxw : x ≠ w) :
    ∃ f : ℝ² ≃ᵢ ℝ², f '' ({a₀, b₀, c₀, d₀} : Set ℝ²) = ({x, y, z, w} : Set ℝ²) := by
  let f := isometryOfUnitDist hyz
  have hfb : f b₀ = y := isometryOfUnitDist_b0 hyz
  have hfc : f c₀ = z := isometryOfUnitDist_c0 hyz
  let x' := f.symm x
  let w' := f.symm w
  have hx'b : dist x' b₀ = 1 := by
    rw [← f.dist_eq x' b₀, f.apply_symm_apply, hfb, hxy]
  have hx'c : dist x' c₀ = 1 := by
    rw [← f.dist_eq x' c₀, f.apply_symm_apply, hfc, hxz]
  have hw'b : dist w' b₀ = 1 := by
    rw [← f.dist_eq w' b₀, f.apply_symm_apply, hfb, hwy]
  have hw'c : dist w' c₀ = 1 := by
    rw [← f.dist_eq w' c₀, f.apply_symm_apply, hfc, hwz]
  have hx'w' : x' ≠ w' := fun h => hxw (f.symm.injective h)
  have hfx' : f x' = x := f.apply_symm_apply x
  have hfw' : f w' = w := f.apply_symm_apply w
  rcases eq_a0_or_d0_of_dist_b0_c0 hx'b hx'c with hx' | hx' <;>
    rcases eq_a0_or_d0_of_dist_b0_c0 hw'b hw'c with hw' | hw'
  · exact (hx'w' (hx'.trans hw'.symm)).elim
  · refine ⟨f, ?_⟩
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rw [← hx', ← hw', hfx', hfb, hfc, hfw']
  · refine ⟨f, ?_⟩
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rw [← hw', ← hx', hfw', hfb, hfc, hfx']
    ext p; simp [or_left_comm, or_comm]
  · exact (hx'w' (hx'.trans hw'.symm)).elim

/-- General indicator bound for a finset `S` contained in `{e₁, e₂, e₃, e₄, e₅, e₆}` where every
element of `S` satisfies `Q`. -/
lemma card_le_sum_ite_six {α : Type*} [DecidableEq α] (S : Finset α) (Q : α → Prop)
    [DecidablePred Q] (e₁ e₂ e₃ e₄ e₅ e₆ : α)
    (hS : ∀ p ∈ S, Q p ∧ (p = e₁ ∨ p = e₂ ∨ p = e₃ ∨ p = e₄ ∨ p = e₅ ∨ p = e₆)) :
    S.card ≤ (if Q e₁ then 1 else 0) + (if Q e₂ then 1 else 0) + (if Q e₃ then 1 else 0) +
      (if Q e₄ then 1 else 0) + (if Q e₅ then 1 else 0) + (if Q e₆ then 1 else 0) := by
  let F : α → Finset α := fun e => if Q e then {e} else ∅
  have hF : ∀ e : α, (F e).card = if Q e then 1 else 0 := fun e => by
    dsimp [F]; split_ifs <;> simp
  have hsub : S ⊆ F e₁ ∪ F e₂ ∪ F e₃ ∪ F e₄ ∪ F e₅ ∪ F e₆ := by
    intro p hp
    rcases hS p hp with ⟨hq, rfl | rfl | rfl | rfl | rfl | rfl⟩ <;>
      simp [F, hq]
  calc S.card ≤ (F e₁ ∪ F e₂ ∪ F e₃ ∪ F e₄ ∪ F e₅ ∪ F e₆).card := Finset.card_le_card hsub
    _ ≤ (F e₁ ∪ F e₂ ∪ F e₃ ∪ F e₄ ∪ F e₅).card + (F e₆).card := Finset.card_union_le _ _
    _ ≤ (F e₁ ∪ F e₂ ∪ F e₃ ∪ F e₄).card + (F e₅).card + (F e₆).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (F e₁ ∪ F e₂ ∪ F e₃).card + (F e₄).card + (F e₅).card + (F e₆).card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ (F e₁ ∪ F e₂).card + (F e₃).card + (F e₄).card + (F e₅).card + (F e₆).card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _
    _ ≤ (F e₁).card + (F e₂).card + (F e₃).card + (F e₄).card + (F e₅).card + (F e₆).card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) _
    _ = _ := by rw [hF, hF, hF, hF, hF, hF]

/-- Every 4-element set `B ⊆ ℝ²` with `5 ≤ unitDistNum B` is congruent to the unit diamond
`{a₀, b₀, c₀, d₀}`. -/
lemma exists_isometry_of_card_four_of_five_le_unitDistNum {B : Finset ℝ²}
    (hB : B.card = 4) (h5 : 5 ≤ unitDistNum B) :
    ∃ f : ℝ² ≃ᵢ ℝ², f '' ({a₀, b₀, c₀, d₀} : Set ℝ²) = (B : Set ℝ²) := by
  classical
  obtain ⟨x₀, T₁, hx₀, rfl, hT₁⟩ := Finset.card_eq_succ.mp hB
  obtain ⟨x₁, T₂, hx₁, rfl, hT₂⟩ := Finset.card_eq_succ.mp hT₁
  obtain ⟨x₂, T₃, hx₂, rfl, hT₃⟩ := Finset.card_eq_succ.mp hT₂
  obtain ⟨x₃, rfl⟩ := Finset.card_eq_one.mp hT₃
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx₀ hx₁ hx₂
  rcases hx₀ with ⟨hx01, hx02, hx03⟩
  rcases hx₁ with ⟨hx12, hx13⟩
  have hx23 : x₂ ≠ x₃ := hx₂
  let S := ({x₀, x₁, x₂, x₃} : Finset ℝ²).sym2.filter (fun p => dist p.out.1 p.out.2 = 1)
  let Q : Sym2 ℝ² → Prop := fun p => dist p.out.1 p.out.2 = 1
  have hS_sub : ∀ p ∈ S, Q p ∧
      (p = s(x₀, x₁) ∨ p = s(x₀, x₂) ∨ p = s(x₀, x₃) ∨
       p = s(x₁, x₂) ∨ p = s(x₁, x₃) ∨ p = s(x₂, x₃)) := by
    intro p hp
    induction p using Sym2.ind with
    | _ u v =>
      simp only [S, Finset.mem_filter, Finset.mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp,
        forall_eq, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with ⟨⟨rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl⟩, hd⟩
      · rw [dist_sym2_out] at hd; simp at hd
      · exact ⟨hd, Or.inl rfl⟩
      · exact ⟨hd, Or.inr (Or.inl rfl)⟩
      · exact ⟨hd, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨hd, Or.inl Sym2.eq_swap⟩
      · rw [dist_sym2_out] at hd; simp at hd
      · exact ⟨hd, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨hd, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
      · exact ⟨hd, Or.inr (Or.inl Sym2.eq_swap)⟩
      · exact ⟨hd, Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))⟩
      · rw [dist_sym2_out] at hd; simp at hd
      · exact ⟨hd, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
      · exact ⟨hd, Or.inr (Or.inr (Or.inl Sym2.eq_swap))⟩
      · exact ⟨hd, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap))))⟩
      · exact ⟨hd, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr Sym2.eq_swap))))⟩
      · rw [dist_sym2_out] at hd; simp at hd
  have h_sum := card_le_sum_ite_six S Q s(x₀, x₁) s(x₀, x₂) s(x₀, x₃) s(x₁, x₂) s(x₁, x₃) s(x₂, x₃) hS_sub
  change unitDistNum {x₀, x₁, x₂, x₃} ≤ _ at h_sum
  simp only [Q, dist_sym2_out] at h_sum
  have h_cases :
      (dist x₀ x₁ = 1 ∧ dist x₀ x₂ = 1 ∧ dist x₁ x₂ = 1 ∧ dist x₀ x₃ = 1 ∧ dist x₁ x₃ = 1) ∨
      (dist x₀ x₂ = 1 ∧ dist x₀ x₁ = 1 ∧ dist x₁ x₂ = 1 ∧ dist x₀ x₃ = 1 ∧ dist x₂ x₃ = 1) ∨
      (dist x₀ x₃ = 1 ∧ dist x₀ x₁ = 1 ∧ dist x₁ x₃ = 1 ∧ dist x₀ x₂ = 1 ∧ dist x₂ x₃ = 1) ∨
      (dist x₁ x₂ = 1 ∧ dist x₀ x₁ = 1 ∧ dist x₀ x₂ = 1 ∧ dist x₁ x₃ = 1 ∧ dist x₂ x₃ = 1) ∨
      (dist x₁ x₃ = 1 ∧ dist x₀ x₁ = 1 ∧ dist x₀ x₃ = 1 ∧ dist x₁ x₂ = 1 ∧ dist x₂ x₃ = 1) ∨
      (dist x₂ x₃ = 1 ∧ dist x₀ x₂ = 1 ∧ dist x₀ x₃ = 1 ∧ dist x₁ x₂ = 1 ∧ dist x₁ x₃ = 1) := by
    by_cases h01 : dist x₀ x₁ = 1 <;>
      by_cases h02 : dist x₀ x₂ = 1 <;>
        by_cases h03 : dist x₀ x₃ = 1 <;>
          by_cases h12 : dist x₁ x₂ = 1 <;>
            by_cases h13 : dist x₁ x₃ = 1 <;>
              by_cases h23 : dist x₂ x₃ = 1 <;>
              simp_all <;> omega
  have h_perm : ∀ {x y z w : ℝ²},
      ({x, y, z, w} : Set ℝ²) = ({x₀, x₁, x₂, x₃} : Set ℝ²) →
      dist y z = 1 → dist x y = 1 → dist x z = 1 → dist w y = 1 → dist w z = 1 → x ≠ w →
      ∃ f : ℝ² ≃ᵢ ℝ², f '' ({a₀, b₀, c₀, d₀} : Set ℝ²) = (({x₀, x₁, x₂, x₃} : Finset ℝ²) : Set ℝ²) := by
    intro x y z w hset hyz hxy hxz hwy hwz hxw
    obtain ⟨f, hf⟩ := congruent_diamond_of_five_dists hyz hxy hxz hwy hwz hxw
    refine ⟨f, ?_⟩
    simpa [Finset.coe_insert, Finset.coe_singleton, hset] using hf
  rcases h_cases with ⟨h1, h2, h3, h4, h5'⟩ | ⟨h1, h2, h3, h4, h5'⟩ | ⟨h1, h2, h3, h4, h5'⟩ |
      ⟨h1, h2, h3, h4, h5'⟩ | ⟨h1, h2, h3, h4, h5'⟩ | ⟨h1, h2, h3, h4, h5'⟩
  · refine h_perm (x := x₂) (y := x₀) (z := x₁) (w := x₃) ?_ h1
      (by rw [dist_comm]; exact h2) (by rw [dist_comm]; exact h3)
      (by rw [dist_comm]; exact h4) (by rw [dist_comm]; exact h5') hx23
    ext p; simp [or_left_comm]
  · refine h_perm (x := x₁) (y := x₀) (z := x₂) (w := x₃) ?_ h1
      (by rw [dist_comm]; exact h2) h3
      (by rw [dist_comm]; exact h4) (by rw [dist_comm]; exact h5') hx13
    ext p; simp [or_left_comm]
  · refine h_perm (x := x₁) (y := x₀) (z := x₃) (w := x₂) ?_ h1
      (by rw [dist_comm]; exact h2) h3
      (by rw [dist_comm]; exact h4) h5' hx12
    ext p; simp [or_left_comm, or_comm]
  · refine h_perm (x := x₀) (y := x₁) (z := x₂) (w := x₃) ?_ h1
      h2 h3
      (by rw [dist_comm]; exact h4) (by rw [dist_comm]; exact h5') hx03
    ext p; simp
  · refine h_perm (x := x₀) (y := x₁) (z := x₃) (w := x₂) ?_ h1
      h2 h3
      (by rw [dist_comm]; exact h4) h5' hx02
    ext p; simp [or_comm]
  · refine h_perm (x := x₀) (y := x₂) (z := x₃) (w := x₁) ?_ h1
      h2 h3 h4 h5' hx01
    ext p; simp [or_left_comm, or_comm]

/-- No 4-point set in `ℝ²` can have more than 5 unit distances. -/
lemma unitDistNum_le_five_of_card_four {B : Finset ℝ²} (hB : B.card = 4) :
    unitDistNum B ≤ 5 := by
  by_contra hgt
  have h5 : 5 ≤ unitDistNum B := by omega
  obtain ⟨f, hf⟩ := exists_isometry_of_card_four_of_five_le_unitDistNum hB h5
  have hf_coe : f '' (({a₀, b₀, c₀, d₀} : Finset ℝ²) : Set ℝ²) = (B : Set ℝ²) := by
    simpa [Finset.coe_insert, Finset.coe_singleton] using hf
  have heq : unitDistNum B = 5 := by
    rw [unitDistNum_eq_of_image_eq f hf_coe, unitDistNum_diamond]
  omega

/-- The maximum number of unit distances among 4 points in `ℝ²` is `5`. -/
lemma maxUnitDistances_four : maxUnitDistances 4 = 5 := by
  unfold maxUnitDistances
  apply le_antisymm
  · apply csSup_le
    · exact ⟨5, {a₀, b₀, c₀, d₀}, diamond_card, unitDistNum_diamond⟩
    · rintro m ⟨B, hB, rfl⟩
      exact unitDistNum_le_five_of_card_four hB
  · apply le_csSup
    · refine ⟨5, ?_⟩
      rintro m ⟨B, hB, rfl⟩
      exact unitDistNum_le_five_of_card_four hB
    · exact ⟨{a₀, b₀, c₀, d₀}, diamond_card, unitDistNum_diamond⟩

/-- **Erdős Problem 668 (`JSP-000542`, `erdos_668.variants.four_points`)**:
For $n=4$ there is, up to congruence, exactly one set of points in $\mathbb{R}^2$ which maximises
the number of unit distances: two unit equilateral triangles $abc$ and $bcd$ joined by the edge
$bc$, with $a \neq d$. -/
theorem erdos_668.variants.four_points :
    ∃ a b c d : ℝ², dist a b = 1 ∧ dist a c = 1 ∧ dist b c = 1 ∧ dist b d = 1 ∧ dist c d = 1 ∧
      ({a, b, c, d} : Finset ℝ²).card = 4 ∧
      ∀ B : Finset ℝ², B.card = 4 →
        (unitDistNum B = maxUnitDistances 4 ↔ ∃ f : ℝ² ≃ᵢ ℝ², f '' {a, b, c, d} = B) := by
  refine ⟨a₀, b₀, c₀, d₀, dist_a0_b0, dist_a0_c0, dist_b0_c0, dist_b0_d0, dist_c0_d0,
    diamond_card, ?_⟩
  intro B hB
  rw [maxUnitDistances_four]
  constructor
  · intro h5
    exact exists_isometry_of_card_four_of_five_le_unitDistNum hB (by omega)
  · rintro ⟨f, hf⟩
    have hf_coe : f '' (({a₀, b₀, c₀, d₀} : Finset ℝ²) : Set ℝ²) = (B : Set ℝ²) := by
      simpa [Finset.coe_insert, Finset.coe_singleton] using hf
    rw [unitDistNum_eq_of_image_eq f hf_coe, unitDistNum_diamond]

/-- **Erdős Problem 668 (`JSP-000542`, `erdos_668.parts.ii`)**:
It is false that for every $n > 3$ there are at least two incongruent $n$-point sets in
$\mathbb{R}^2$ maximising `unitDistNum` ($n = 4$ is a counterexample). -/
theorem erdos_668.parts.ii :
    ¬ ∀ n : ℕ, 3 < n → ∃ A B : Finset ℝ², A.card = n ∧ B.card = n ∧
      unitDistNum A = maxUnitDistances n ∧ unitDistNum B = maxUnitDistances n ∧
      ¬ ∃ f : ℝ² ≃ᵢ ℝ², f '' A = B := by
  obtain ⟨a, b, c, d, -, -, -, -, -, -, h⟩ := erdos_668.variants.four_points
  intro H
  obtain ⟨A, B, hA, hB, hAm, hBm, hAB⟩ := H 4 (by norm_num)
  obtain ⟨f, hf⟩ := (h A hA).1 hAm
  obtain ⟨g, hg⟩ := (h B hB).1 hBm
  exact hAB ⟨f.symm.trans g, by rw [← hf, ← hg, Set.image_image]; simp⟩

end Erdos668

/-!
## Part 3: Erdős Problem 80 (`80.lean`) — Book Numbers and Triangle-Rich Graphs
-/

namespace Erdos80

open Filter Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The size of the largest *book* in `G`: the greatest number of triangles sharing a single
edge. -/
noncomputable def bookNumber : ℕ :=
  G.edgeFinset.sup fun e => #(G.trianglesContaining e)

/-- Every edge of `G` lies in at least one triangle. -/
def EveryEdgeInTriangle : Prop :=
  ∀ e ∈ G.edgeFinset, (G.trianglesContaining e).Nonempty

/-- The graphs the problem quantifies over: `n` vertices, at least $cn^2$ edges, and every
edge in a triangle. -/
def Admissible (c : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  c * (n : ℝ) ^ 2 ≤ #G.edgeFinset ∧ EveryEdgeInTriangle G

open Classical in
/-- $f_c(n)$, the largest book size forced on every admissible graph, which is the least book
number among them. -/
noncomputable def f (c : ℝ) (n : ℕ) : ℕ :=
  sInf {m | ∃ G : SimpleGraph (Fin n), Admissible c G ∧ bookNumber G = m}

omit [DecidableEq α] in
/-- A book is counted by triangles, so `bookNumber` is `0` exactly when no edge lies in one. -/
theorem bookNumber_eq_zero_iff :
    bookNumber G = 0 ↔ ∀ e ∈ G.edgeFinset, G.trianglesContaining e = ∅ := by
  simp [bookNumber, Finset.card_eq_zero]

/-- On a graph with no edges there is no book. -/
theorem bookNumber_bot {n : ℕ} : bookNumber (⊥ : SimpleGraph (Fin n)) = 0 := by
  simp [bookNumber]

/-- `EveryEdgeInTriangle` holds vacuously on a graph with no edges. -/
theorem everyEdgeInTriangle_bot {n : ℕ} :
    EveryEdgeInTriangle (⊥ : SimpleGraph (Fin n)) := by
  simp [EveryEdgeInTriangle]

/-- For $c \ge 1 / 2$ and every $n : \mathbb{N}$, $f_c(n) = 0$ (as noted in `80.lean`: a simple
graph on $n \ge 1$ vertices has at most $n(n-1)/2 < n^2/2$ edges, so the admissible set is empty
for $n \ge 1$, while for $n = 0$ every graph has $0$ edges and `bookNumber = 0`). -/
theorem f_eq_zero_of_ge_half {c : ℝ} (hc : 1 / 2 ≤ c) (n : ℕ) : f c n = 0 := by
  classical
  unfold f
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · apply Nat.eq_zero_of_le_zero
    apply Nat.sInf_le
    refine ⟨⊥, ⟨?_, everyEdgeInTriangle_bot⟩, bookNumber_bot⟩
    simp
  · have h_empty : {m | ∃ G : SimpleGraph (Fin n), Admissible c G ∧ bookNumber G = m} = ∅ := by
      ext m
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨G, ⟨h_edges, _⟩, _⟩
      have h_le_choose : #G.edgeFinset ≤ n.choose 2 := by
        simpa [Fintype.card_fin] using G.card_edgeFinset_le_card_choose_two
      have h_mul : 2 * #G.edgeFinset < n * n := by
        have h1 : 2 * n.choose 2 ≤ n * (n - 1) := by
          rw [Nat.choose_two_right, mul_comm 2]
          exact Nat.div_mul_le_self (n * (n - 1)) 2
        have h2 : n * (n - 1) < n * n := by
          rcases n with _ | k
          · omega
          · simp
        omega
      have h_real : (2 : ℝ) * (#G.edgeFinset : ℝ) < (n : ℝ) ^ 2 := by
        have := Nat.cast_lt (α := ℝ).mpr h_mul
        push_cast at this
        linarith
      nlinarith [sq_nonneg (n : ℝ)]
    rw [h_empty, Nat.sInf_empty]

omit [DecidableEq α] in
/-- If `EveryEdgeInTriangle G` holds and `G` has at least one edge, then `1 ≤ bookNumber G`. -/
theorem one_le_bookNumber_of_everyEdgeInTriangle
    (h_tri : EveryEdgeInTriangle G) (h_ne : G.edgeFinset.Nonempty) :
    1 ≤ bookNumber G := by
  obtain ⟨e, he⟩ := h_ne
  have h_pos : 1 ≤ #(G.trianglesContaining e) := Finset.Nonempty.card_pos (h_tri e he)
  exact h_pos.trans (Finset.le_sup (f := fun e => #(G.trianglesContaining e)) he)

/-- Whenever `0 < c`, `0 < n`, and an admissible graph exists, `1 ≤ f c n` (showing that
`EveryEdgeInTriangle` excludes triangle-free graphs from achieving `bookNumber G = 0`). -/
theorem one_le_f_of_admissible {c : ℝ} {n : ℕ} (hc : 0 < c) (hn : 0 < n)
    (h_adm : ∃ G : SimpleGraph (Fin n), by classical exact Admissible c G) :
    1 ≤ f c n := by
  classical
  obtain ⟨G₀, hG₀⟩ := h_adm
  apply le_csInf
  · exact ⟨bookNumber G₀, G₀, hG₀, rfl⟩
  · rintro m ⟨G, ⟨h_edges, h_tri⟩, rfl⟩
    have h_pos_real : (0 : ℝ) < (#G.edgeFinset : ℝ) := by
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      linarith [ show (0 : ℝ) < c * (n : ℝ) ^ 2 by positivity ]
    have h_pos : 0 < #G.edgeFinset := Nat.cast_pos.mp h_pos_real
    exact one_le_bookNumber_of_everyEdgeInTriangle G h_tri (Finset.card_pos.mp h_pos)

/-- Reduction of `erdos_80.parts.i` to the Fox–Loh (2012) upper bound: if for some
$c \in (0, 1/2)$ and every $\varepsilon > 0$ we have $f_c(n) \le n^\varepsilon$ infinitely often,
then `erdos_80.parts.i` holds. -/
theorem erdos_80_parts_i_of_fox_loh
    (h_fl : ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      ∀ ε > (0 : ℝ), ∃ᶠ n : ℕ in atTop, (f c n : ℝ) ≤ (n : ℝ) ^ ε) :
    ¬ ∀ c : ℝ, 0 < c → c < 1 / 2 →
      ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ε < f c n := by
  rcases h_fl with ⟨c, hc0, hc2, h_freq⟩
  intro H
  rcases H c hc0 hc2 with ⟨ε, hε, h_ev⟩
  exact (h_freq ε hε).and_eventually h_ev |>.exists |> fun ⟨n, hle, hlt⟩ => by linarith

/-!
### Unrestricted Book Number Variant (Without `EveryEdgeInTriangle`)
-/

open Classical in
/-- The unrestricted book number function dropping `EveryEdgeInTriangle G`:
minimum `bookNumber G` over all graphs on `Fin n` with at least $cn^2$ edges. -/
noncomputable def fUnrestricted (c : ℝ) (n : ℕ) : ℕ :=
  sInf {m | ∃ G : SimpleGraph (Fin n), c * (n : ℝ) ^ 2 ≤ #G.edgeFinset ∧ bookNumber G = m}

/-- Balanced bipartite graph on `Fin n` with parts `{i | i.val < n / 2}` and `{i | n / 2 ≤ i.val}`. -/
def bipGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (u.val < n / 2) ≠ (v.val < n / 2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

/-- `bipGraph n` is triangle-free (`CliqueFree 3`). -/
lemma bipGraph_cliqueFree (n : ℕ) : (bipGraph n).CliqueFree 3 := by
  intro t ht
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp ht.2
  have h1 : (bipGraph n).Adj u v := ht.1 (by simp) (by simp) huv
  have h2 : (bipGraph n).Adj u w := ht.1 (by simp) (by simp) huw
  have h3 : (bipGraph n).Adj v w := ht.1 (by simp) (by simp) hvw
  change (u.val < n / 2) ≠ (v.val < n / 2) at h1
  change (u.val < n / 2) ≠ (w.val < n / 2) at h2
  change (v.val < n / 2) ≠ (w.val < n / 2) at h3
  by_cases hu : u.val < n / 2 <;>
    by_cases hv : v.val < n / 2 <;>
      by_cases hw : w.val < n / 2 <;>
      simp_all

open Classical in
/-- Because `bipGraph n` has no triangles, its `bookNumber` is `0`. -/
lemma bookNumber_bipGraph (n : ℕ) :
    bookNumber (bipGraph n) = 0 := by
  rw [bookNumber_eq_zero_iff]
  intro e _
  ext t
  simp only [SimpleGraph.trianglesContaining, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff,
    Finset.notMem_empty, iff_false, not_and]
  intro ht _
  exact (bipGraph_cliqueFree n t ht).elim

open Classical in
/-- For any `k : ℕ`, `bipGraph (2 * k)` has at least `k * k` edges. -/
lemma card_edgeFinset_bipGraph_two_mul (k : ℕ) :
    k * k ≤ #(bipGraph (2 * k)).edgeFinset := by
  let φ : Fin k × Fin k → Sym2 (Fin (2 * k)) :=
    fun p => s(⟨p.1.val, by omega⟩, ⟨k + p.2.val, by omega⟩)
  have h_maps : ∀ p ∈ (Finset.univ : Finset (Fin k × Fin k)),
      φ p ∈ (bipGraph (2 * k)).edgeFinset := by
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ _
    rw [SimpleGraph.mem_edgeFinset]
    change (i < (2 * k) / 2) ≠ (k + j < (2 * k) / 2)
    have h1 : i < (2 * k) / 2 := by omega
    have h2 : ¬ (k + j < (2 * k) / 2) := by omega
    intro h_eq
    exact h2 (h_eq ▸ h1)
  have h_inj : Set.InjOn φ ((Finset.univ : Finset (Fin k × Fin k)) : Set (Fin k × Fin k)) := by
    rintro ⟨⟨i₁, hi₁⟩, ⟨j₁, hj₁⟩⟩ _ ⟨⟨i₂, hi₂⟩, ⟨j₂, hj₂⟩⟩ _ h_eq
    rcases Sym2.eq_iff.mp h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Fin.mk.injEq] at h1 h2
      ext <;> simp <;> omega
    · simp only [Fin.mk.injEq] at h1 h2
      omega
  have h_card := Finset.card_le_card_of_injOn φ h_maps h_inj
  simpa [Fintype.card_prod, Fintype.card_fin] using h_card

open Classical in
/-- For `c ≤ 1 / 4` and any `k : ℕ`, `fUnrestricted c (2 * k) = 0` witnessed by `bipGraph (2 * k)`. -/
lemma fUnrestricted_two_mul_eq_zero {c : ℝ} (hc : c ≤ 1 / 4) (k : ℕ) :
    fUnrestricted c (2 * k) = 0 := by
  unfold fUnrestricted
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  refine ⟨bipGraph (2 * k), ?_, bookNumber_bipGraph (2 * k)⟩
  have h_edges : ((k * k : ℕ) : ℝ) ≤ (#(bipGraph (2 * k)).edgeFinset : ℝ) :=
    Nat.cast_le.mpr (card_edgeFinset_bipGraph_two_mul k)
  push_cast at h_edges ⊢
  nlinarith [sq_nonneg (k : ℝ)]

/-- Disproof of the unrestricted version of `erdos_80.parts.i` (without `EveryEdgeInTriangle`),
using $c = 1 / 8 < 1 / 4$ and balanced bipartite graphs. -/
theorem unrestricted_erdos_80_parts_i :
    ¬ ∀ c : ℝ, 0 < c → c < 1 / 2 →
      ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ε < fUnrestricted c n := by
  intro H
  obtain ⟨ε, hε, h_ev⟩ := H (1 / 8) (by norm_num) (by norm_num)
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨N, hN⟩ := h_ev
  have h_lt := hN (2 * (N + 1)) (by omega)
  rw [fUnrestricted_two_mul_eq_zero (by norm_num) (N + 1)] at h_lt
  simp only [Nat.cast_zero] at h_lt
  have h_pos : (0 : ℝ) < ((2 * (N + 1) : ℕ) : ℝ) ^ ε := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast (show 0 < 2 * (N + 1) by omega)
  linarith

end Erdos80

#print axioms Erdos596.erdos_596.variants.C4_free_countable_escape
#print axioms Erdos668.erdos_668.variants.four_points
#print axioms Erdos668.erdos_668.parts.ii
#print axioms Erdos80.f_eq_zero_of_ge_half
#print axioms Erdos80.one_le_f_of_admissible
#print axioms Erdos80.unrestricted_erdos_80_parts_i
