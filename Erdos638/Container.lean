import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Self-Contained Rational Hypergraph Container Theorem (Nenadov–Pham 2024)

We formalize the short greedy container algorithm of Nenadov and Pham (*Combin. Probab. Comput.*
34 (2025), 621–624, `arXiv:2408.08514`) purely over `ℚ` on `Fin N₀`, using the single-function
sandwich invariance design (`containerStep ... F̂ = (F, C)` for every `F ⊆ F̂ ⊆ I`).
-/

namespace Erdos638.Container

open scoped Classical BigOperators

/-- A weighted hypergraph on `Fin N₀` is represented by its finite support `edges : Finset (Finset (Fin N₀))`
together with a rational weight function `wt : Finset (Fin N₀) → ℚ`. -/
structure WeightedHypergraph (N₀ : ℕ) where
  edges : Finset (Finset (Fin N₀))
  wt : Finset (Fin N₀) → ℚ

namespace WeightedHypergraph

variable {N₀ : ℕ}

/-- Total weight of a collection of edges `E`. -/
def weightOf (H : WeightedHypergraph N₀) (E : Finset (Finset (Fin N₀))) : ℚ :=
  ∑ e ∈ E, H.wt e

/-- Total weight of `H`. -/
def totalWeight (H : WeightedHypergraph N₀) : ℚ :=
  H.weightOf H.edges

/-- Codegree weight of a subset `X : Finset (Fin N₀)` inside an edge collection `E`:
sum of `H.wt e` over `e ∈ E` with `X ⊆ e`. -/
def codegWeight (H : WeightedHypergraph N₀) (E : Finset (Finset (Fin N₀))) (X : Finset (Fin N₀)) : ℚ :=
  ∑ e ∈ E.filter (fun e => X ⊆ e), H.wt e

/-- Vertex degree weight of `v : Fin N₀` inside an edge collection `E`. -/
def degWeight (H : WeightedHypergraph N₀) (E : Finset (Finset (Fin N₀))) (v : Fin N₀) : ℚ :=
  H.codegWeight E {v}

/-- `H` is valid of rank `≤ ℓ` on vertex domain `U` if all `e ∈ H.edges` satisfy
`e ⊆ U`, `1 ≤ e.card ≤ ℓ`, and `0 < H.wt e` (with non-negative weights everywhere). -/
structure IsValidOn (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀)) : Prop where
  sub_domain : ∀ e ∈ H.edges, e ⊆ U
  nonempty_edge : ∀ e ∈ H.edges, 1 ≤ e.card
  card_le : ∀ e ∈ H.edges, e.card ≤ ℓ
  wt_pos : ∀ e ∈ H.edges, 0 < H.wt e
  wt_nonneg : ∀ e, 0 ≤ H.wt e
  total_pos : 0 < H.totalWeight

/-- `(p, K)`-uniformly-spread condition at global scale `N₀`. -/
def IsSpread (H : WeightedHypergraph N₀) (p K : ℚ) : Prop :=
  ∀ X : Finset (Fin N₀), 1 ≤ X.card →
    H.codegWeight H.edges X ≤ H.totalWeight * K * p ^ (X.card - 1) / (N₀ : ℚ)

/-- `I` is an independent set of `H` if no `e ∈ H.edges` satisfies `e ⊆ I`. -/
def IsIndep (H : WeightedHypergraph N₀) (I : Finset (Fin N₀)) : Prop :=
  ∀ e ∈ H.edges, ¬(e ⊆ I)

lemma weightOf_nonneg {H : WeightedHypergraph N₀} (hnn : ∀ e, 0 ≤ H.wt e)
    (E : Finset (Finset (Fin N₀))) : 0 ≤ H.weightOf E :=
  Finset.sum_nonneg (fun e _ => hnn e)

lemma weightOf_mono {H : WeightedHypergraph N₀} (hnn : ∀ e, 0 ≤ H.wt e)
    {E₁ E₂ : Finset (Finset (Fin N₀))} (h : E₁ ⊆ E₂) :
    H.weightOf E₁ ≤ H.weightOf E₂ :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun e _ _ => hnn e)

lemma weightOf_union_le {H : WeightedHypergraph N₀} (hnn : ∀ e, 0 ≤ H.wt e)
    (E₁ E₂ : Finset (Finset (Fin N₀))) :
    H.weightOf (E₁ ∪ E₂) ≤ H.weightOf E₁ + H.weightOf E₂ := by
  unfold weightOf
  have h := Finset.sum_union_inter (s₁ := E₁) (s₂ := E₂) (f := H.wt)
  have hinter : 0 ≤ ∑ e ∈ E₁ ∩ E₂, H.wt e := Finset.sum_nonneg (fun e _ => hnn e)
  linarith

lemma codegWeight_mono {H : WeightedHypergraph N₀} (hnn : ∀ e, 0 ≤ H.wt e)
    {E₁ E₂ : Finset (Finset (Fin N₀))} (h : E₁ ⊆ E₂) (X : Finset (Fin N₀)) :
    H.codegWeight E₁ X ≤ H.codegWeight E₂ X := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨h he.1, he.2⟩
  · intro e _ _
    exact hnn e

lemma codegWeight_union_disjoint {H : WeightedHypergraph N₀}
    {E₁ E₂ : Finset (Finset (Fin N₀))} (hd : Disjoint E₁ E₂) (X : Finset (Fin N₀)) :
    H.codegWeight (E₁ ∪ E₂) X = H.codegWeight E₁ X + H.codegWeight E₂ X := by
  unfold codegWeight
  rw [Finset.filter_union, Finset.sum_union]
  exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd

lemma degWeight_mono {H : WeightedHypergraph N₀} (hnn : ∀ e, 0 ≤ H.wt e)
    {E₁ E₂ : Finset (Finset (Fin N₀))} (h : E₁ ⊆ E₂) (v : Fin N₀) :
    H.degWeight E₁ v ≤ H.degWeight E₂ v :=
  codegWeight_mono hnn h {v}

end WeightedHypergraph

/-! ## Canonical Degree-Maximizing Choice with Lexicographic Tie-Breaking -/

section GreedyChoice

variable {N₀ : ℕ}

/-- Compare two vertices `u, v : Fin N₀` under score `score : Fin N₀ → ℚ`:
`betterVertex score u v` holds if `score v < score u`, or `score u = score v` and `u ≤ v`
(preferring larger degree, then smaller vertex index). -/
def betterVertex (score : Fin N₀ → ℚ) (u v : Fin N₀) : Prop :=
  score v < score u ∨ (score u = score v ∧ u ≤ v)

lemma betterVertex_refl (score : Fin N₀ → ℚ) (u : Fin N₀) : betterVertex score u u :=
  Or.inr ⟨rfl, le_rfl⟩

lemma betterVertex_trans {score : Fin N₀ → ℚ} {a b c : Fin N₀}
    (hab : betterVertex score a b) (hbc : betterVertex score b c) :
    betterVertex score a c := by
  rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
  · exact Or.inl (lt_trans h2 h1)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨h1.trans h2, le_trans h1' h2'⟩

lemma betterVertex_total (score : Fin N₀ → ℚ) (u v : Fin N₀) :
    betterVertex score u v ∨ betterVertex score v u := by
  rcases lt_trichotomy (score u) (score v) with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · rcases le_total u v with huv | hvu
    · exact Or.inl (Or.inr ⟨heq, huv⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hvu⟩)
  · exact Or.inl (Or.inl hgt)

lemma betterVertex_antisymm {score : Fin N₀ → ℚ} {u v : Fin N₀}
    (h1 : betterVertex score u v) (h2 : betterVertex score v u) : u = v := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨_, h2'⟩
  · exfalso; exact lt_asymm h1 h2
  · exfalso; linarith
  · exfalso; linarith
  · exact le_antisymm h1' h2'

/-- Every nonempty `S : Finset (Fin N₀)` has a unique `betterVertex`-best element. -/
lemma exists_best_vertex (score : Fin N₀ → ℚ) {S : Finset (Fin N₀)} (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, betterVertex score v u := by
  revert hS
  refine Finset.induction_on S (fun h => absurd rfl h.ne_empty) ?_
  intro x T hxT ih _
  by_cases hT : T.Nonempty
  · obtain ⟨b, hbT, hb⟩ := ih hT
    rcases betterVertex_total score x b with hab | hba
    · refine ⟨x, Finset.mem_insert_self x T, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with hux | huT
      · rw [hux]; exact betterVertex_refl score x
      · exact betterVertex_trans hab (hb u huT)
    · refine ⟨b, Finset.mem_insert_of_mem hbT, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with hux | huT
      · rw [hux]; exact hba
      · exact hb u huT
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    rw [hT]
    exact ⟨x, Finset.mem_singleton_self x, fun u hu => by
      rw [Finset.mem_singleton.mp hu]; exact betterVertex_refl score x⟩

/-- Pick the unique `betterVertex`-best element of a nonempty `Finset (Fin N₀)`. -/
noncomputable def pickBestVertex (score : Fin N₀ → ℚ) (S : Finset (Fin N₀))
    (hS : S.Nonempty) : Fin N₀ :=
  Classical.choose (exists_best_vertex score hS)

lemma pickBestVertex_mem (score : Fin N₀ → ℚ) {S : Finset (Fin N₀)} (hS : S.Nonempty) :
    pickBestVertex score S hS ∈ S :=
  (Classical.choose_spec (exists_best_vertex score hS)).1

lemma pickBestVertex_best (score : Fin N₀ → ℚ) {S : Finset (Fin N₀)} (hS : S.Nonempty) :
    ∀ u ∈ S, betterVertex score (pickBestVertex score S hS) u :=
  (Classical.choose_spec (exists_best_vertex score hS)).2

lemma pickBestVertex_deg_ge (score : Fin N₀ → ℚ) {S : Finset (Fin N₀)} (hS : S.Nonempty)
    {u : Fin N₀} (hu : u ∈ S) :
    score u ≤ score (pickBestVertex score S hS) := by
  rcases pickBestVertex_best score hS u hu with hlt | ⟨heq, _⟩
  · exact le_of_lt hlt
  · exact le_of_eq heq.symm

/-- **Sandwich Invariance of `pickBestVertex`**:
If `v = pickBestVertex score I hI` belongs to a subset `F̂ ⊆ I`, then `pickBestVertex score F̂ hF̂ = v`! -/
lemma pickBestVertex_sandwich (score : Fin N₀ → ℚ)
    {F_hat I : Finset (Fin N₀)} (hF_hat : F_hat.Nonempty) (hI : I.Nonempty)
    (hsub : F_hat ⊆ I) (hmem : pickBestVertex score I hI ∈ F_hat) :
    pickBestVertex score F_hat hF_hat = pickBestVertex score I hI := by
  apply betterVertex_antisymm
  · exact pickBestVertex_best score hF_hat _ hmem
  · exact pickBestVertex_best score hI _ (hsub (pickBestVertex_mem score hF_hat))

end GreedyChoice

/-! ## Inner Greedy State and Round Transition (Nenadov–Pham Lemma 2.1) -/

section GreedyProcess

variable {N₀ : ℕ}

/-- State during the `s`-round greedy loop of Nenadov–Pham Lemma 2.1. -/
structure GreedyState (N₀ : ℕ) where
  F : Finset (Fin N₀)
  Hp : Finset (Finset (Fin N₀))
  L : Finset (Finset (Fin N₀))
  D : Finset (Finset (Fin N₀))

/-- Active residual hyperedges `R = H[U \ F] \ D`: edges of `H` disjoint from `F` and not in `D`. -/
def GreedyState.R (H : WeightedHypergraph N₀) (st : GreedyState N₀) :
    Finset (Finset (Fin N₀)) :=
  (H.edges.filter (fun e => Disjoint e st.F)) \ st.D

/-- Candidate nonempty subsets `X ⊆ U` of size `1 ≤ |X| ≤ ℓ - 1`. -/
def smallSubsets (ℓ : ℕ) (U : Finset (Fin N₀)) : Finset (Finset (Fin N₀)) :=
  U.powerset.filter (fun X => 1 ≤ X.card ∧ X.card ≤ ℓ - 1)

/-- Single transition step of the greedy loop upon adding a chosen vertex `v`.
Notice this depends ONLY on `(H, ℓ, U, p, K, st, v)` and NOT on `S`! -/
def greedyAdvance (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (st : GreedyState N₀) (v : Fin N₀) : GreedyState N₀ :=
  let R := st.R H
  let newly := R.filter (fun e => v ∈ e)
  let R_rem := R.filter (fun e => v ∉ e)
  let Hp' := st.Hp ∪ newly
  let newL := (smallSubsets ℓ U \ st.L).filter (fun X =>
    H.totalWeight * K * p ^ X.card / (N₀ : ℚ) < H.codegWeight Hp' X)
  let L' := st.L ∪ newL
  let newD := newL.biUnion (fun X => R_rem.filter (fun e => X ⊆ e))
  let D' := st.D ∪ newD
  { F := insert v st.F, Hp := Hp', L := L', D := D' }

/-- Run `k` greedy rounds starting from `st`, picking vertices from `S \ st.F`. -/
noncomputable def runGreedyRounds (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (S : Finset (Fin N₀)) : ℕ → GreedyState N₀ → GreedyState N₀
  | 0, st => st
  | k + 1, st =>
    if hne : (S \ st.F).Nonempty then
      let v := pickBestVertex (H.degWeight (st.R H)) (S \ st.F) hne
      runGreedyRounds H ℓ U p K S k (greedyAdvance H ℓ U p K st v)
    else
      st

/-- Initial empty greedy state. -/
def initGreedyState : GreedyState N₀ :=
  { F := ∅, Hp := ∅, L := ∅, D := ∅ }

/-- Invariants maintained throughout the `s`-round greedy process. -/
structure GreedyInvariant (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (st : GreedyState N₀) : Prop where
  Hp_sub : st.Hp ⊆ H.edges
  D_sub : st.D ⊆ H.edges
  Hp_disjoint_D : Disjoint st.Hp st.D
  Hp_hits_F : ∀ e ∈ st.Hp, ¬Disjoint e st.F
  L_sub : st.L ⊆ smallSubsets ℓ U
  D_covered_by_L : ∀ e ∈ st.D, ∃ X ∈ st.L, X ⊆ e
  L_heavy : ∀ X ∈ st.L, H.totalWeight * K * p ^ X.card / (N₀ : ℚ) < H.codegWeight st.Hp X
  L_kills_R : ∀ X ∈ st.L, ∀ e ∈ st.R H, ¬(X ⊆ e)
  nonL_light : ∀ X ∈ smallSubsets ℓ U \ st.L,
    H.codegWeight st.Hp X ≤ H.totalWeight * K * p ^ X.card / (N₀ : ℚ)
  L_capped_disjoint : ∀ X ∈ smallSubsets ℓ U, Disjoint X st.F →
    H.codegWeight st.Hp X ≤ 2 * H.totalWeight * K * p ^ X.card / (N₀ : ℚ)
  partition_edges : H.edges ⊆ st.R H ∪ st.Hp ∪ st.D

lemma greedyInvariant_init (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (hH : H.IsValidOn ℓ U) (hp : 0 < p) (hK : 0 < K) (hN₀ : 0 < N₀) :
    GreedyInvariant H ℓ U p K initGreedyState := by
  have hW : 0 ≤ H.totalWeight := le_of_lt hH.total_pos
  refine
    { Hp_sub := Finset.empty_subset _
      D_sub := Finset.empty_subset _
      Hp_disjoint_D := Finset.disjoint_empty_left _
      Hp_hits_F := fun _ he => absurd he (Finset.notMem_empty _)
      L_sub := Finset.empty_subset _
      D_covered_by_L := fun _ he => absurd he (Finset.notMem_empty _)
      L_heavy := fun _ hX => absurd hX (Finset.notMem_empty _)
      L_kills_R := fun _ hX => absurd hX (Finset.notMem_empty _)
      nonL_light := ?_
      L_capped_disjoint := ?_
      partition_edges := ?_ }
  · intro X _
    simp only [initGreedyState, WeightedHypergraph.codegWeight, Finset.filter_empty, Finset.sum_empty]
    positivity
  · intro X _ _
    simp only [initGreedyState, WeightedHypergraph.codegWeight, Finset.filter_empty, Finset.sum_empty]
    positivity
  · intro e he
    simp [initGreedyState, GreedyState.R, he]

lemma greedyAdvance_R_subset (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (st : GreedyState N₀) (v : Fin N₀) :
    (greedyAdvance H ℓ U p K st v).R H ⊆ st.R H := by
  intro e he
  simp only [greedyAdvance, GreedyState.R, Finset.mem_sdiff, Finset.mem_filter,
    Finset.disjoint_insert_right, Finset.mem_union] at he ⊢
  exact ⟨⟨he.1.1, he.1.2.2⟩, fun hd => he.2 (Or.inl hd)⟩

lemma greedyAdvance_F (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (st : GreedyState N₀) (v : Fin N₀) :
    (greedyAdvance H ℓ U p K st v).F = insert v st.F := rfl

lemma greedyAdvance_Hp_disjoint_union (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (st : GreedyState N₀) (v : Fin N₀) (hinv : GreedyInvariant H ℓ U p K st) :
    Disjoint st.Hp ((st.R H).filter (fun e => v ∈ e)) := by
  rw [Finset.disjoint_left]
  intro e heHp heNew
  have hdisj : Disjoint e st.F := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp heNew).1).1).2
  exact hinv.Hp_hits_F e heHp hdisj

lemma greedyAdvance_weightOf_Hp (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (st : GreedyState N₀) (v : Fin N₀) (hinv : GreedyInvariant H ℓ U p K st) :
    H.weightOf (greedyAdvance H ℓ U p K st v).Hp =
      H.weightOf st.Hp + H.degWeight (st.R H) v := by
  have hd := greedyAdvance_Hp_disjoint_union H ℓ U p K st v hinv
  change ∑ e ∈ st.Hp ∪ (st.R H).filter (fun e => v ∈ e), H.wt e =
    (∑ e ∈ st.Hp, H.wt e) + ∑ e ∈ (st.R H).filter (fun e => {v} ⊆ e), H.wt e
  rw [Finset.sum_union hd]
  congr 1
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext e
  simp

lemma greedyAdvance_preserves (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (st : GreedyState N₀) (v : Fin N₀)
    (hH : H.IsValidOn ℓ U) (hsp : H.IsSpread p K)
    (hinv : GreedyInvariant H ℓ U p K st) :
    GreedyInvariant H ℓ U p K (greedyAdvance H ℓ U p K st v) := by
  set R := st.R H
  set newly := R.filter (fun e => v ∈ e)
  set R_rem := R.filter (fun e => v ∉ e)
  set Hp' := st.Hp ∪ newly
  set newL := (smallSubsets ℓ U \ st.L).filter (fun X =>
    H.totalWeight * K * p ^ X.card / (N₀ : ℚ) < H.codegWeight Hp' X)
  set L' := st.L ∪ newL
  set newD := newL.biUnion (fun X => R_rem.filter (fun e => X ⊆ e))
  set D' := st.D ∪ newD
  have hR_sub_edges : R ⊆ H.edges := fun e he =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).1
  have hR_disj_F : ∀ e ∈ R, Disjoint e st.F := fun e he =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).2
  have hR_not_D : ∀ e ∈ R, e ∉ st.D := fun e he => (Finset.mem_sdiff.mp he).2
  have hnewly_disj_Hp : Disjoint st.Hp newly :=
    greedyAdvance_Hp_disjoint_union H ℓ U p K st v hinv
  have hnewly_sub_edges : newly ⊆ H.edges :=
    (Finset.filter_subset _ _).trans hR_sub_edges
  have hnewD_sub_R_rem : newD ⊆ R_rem := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨X, _, heX⟩
    exact (Finset.mem_filter.mp heX).1
  have hnewD_sub_edges : newD ⊆ H.edges :=
    hnewD_sub_R_rem.trans ((Finset.filter_subset _ _).trans hR_sub_edges)
  refine
    { Hp_sub := Finset.union_subset hinv.Hp_sub hnewly_sub_edges
      D_sub := Finset.union_subset hinv.D_sub hnewD_sub_edges
      Hp_disjoint_D := ?_
      Hp_hits_F := ?_
      L_sub := ?_
      D_covered_by_L := ?_
      L_heavy := ?_
      L_kills_R := ?_
      nonL_light := ?_
      L_capped_disjoint := ?_
      partition_edges := ?_ }
  · -- `Disjoint Hp' D'`
    rw [Finset.disjoint_left]
    intro e heHp' heD'
    rcases Finset.mem_union.mp heHp' with heHp | heNew <;>
      rcases Finset.mem_union.mp heD' with heD | heNewD
    · exact Finset.disjoint_left.mp hinv.Hp_disjoint_D heHp heD
    · have heR : e ∈ R := (Finset.mem_filter.mp (hnewD_sub_R_rem heNewD)).1
      exact hinv.Hp_hits_F e heHp (hR_disj_F e heR)
    · exact hR_not_D e (Finset.mem_filter.mp heNew).1 heD
    · have hv_in : v ∈ e := (Finset.mem_filter.mp heNew).2
      have hv_not : v ∉ e := (Finset.mem_filter.mp (hnewD_sub_R_rem heNewD)).2
      exact hv_not hv_in
  · -- `Hp_hits_F`
    intro e heHp' hdisj'
    rw [greedyAdvance_F, Finset.disjoint_insert_right] at hdisj'
    rcases Finset.mem_union.mp heHp' with heHp | heNew
    · exact hinv.Hp_hits_F e heHp hdisj'.2
    · exact hdisj'.1 (Finset.mem_filter.mp heNew).2
  · -- `L_sub`
    refine Finset.union_subset hinv.L_sub ?_
    exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
  · -- `D_covered_by_L`
    intro e heD'
    rcases Finset.mem_union.mp heD' with heD | heNewD
    · obtain ⟨X, hXL, hXe⟩ := hinv.D_covered_by_L e heD
      exact ⟨X, Finset.mem_union_left _ hXL, hXe⟩
    · rcases Finset.mem_biUnion.mp heNewD with ⟨X, hXnewL, heX⟩
      exact ⟨X, Finset.mem_union_right _ hXnewL, (Finset.mem_filter.mp heX).2⟩
  · -- `L_heavy`
    intro X hXL'
    rcases Finset.mem_union.mp hXL' with hXL | hXnewL
    · exact lt_of_lt_of_le (hinv.L_heavy X hXL)
        (H.codegWeight_mono hH.wt_nonneg Finset.subset_union_left X)
    · exact (Finset.mem_filter.mp hXnewL).2
  · -- `L_kills_R`
    intro X hXL' e heR' hXe
    have heR : e ∈ R := greedyAdvance_R_subset H ℓ U p K st v heR'
    rcases Finset.mem_union.mp hXL' with hXL | hXnewL
    · exact hinv.L_kills_R X hXL e heR hXe
    · simp only [greedyAdvance, GreedyState.R, Finset.mem_sdiff, Finset.mem_filter,
        Finset.disjoint_insert_right, Finset.mem_union] at heR'
      have heR_rem : e ∈ R_rem := Finset.mem_filter.mpr ⟨heR, heR'.1.2.1⟩
      have heNewD : e ∈ newD := Finset.mem_biUnion.mpr ⟨X, hXnewL, Finset.mem_filter.mpr ⟨heR_rem, hXe⟩⟩
      exact heR'.2 (Or.inr heNewD)
  · -- `nonL_light`
    intro X hXnon
    have hXs : X ∈ smallSubsets ℓ U := (Finset.mem_sdiff.mp hXnon).1
    have hXnotL' : X ∉ L' := (Finset.mem_sdiff.mp hXnon).2
    have hXnotL : X ∉ st.L := fun h => hXnotL' (Finset.mem_union_left _ h)
    have hXnotNew : X ∉ newL := fun h => hXnotL' (Finset.mem_union_right _ h)
    by_contra! hgt
    exact hXnotNew (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hXs, hXnotL⟩, hgt⟩)
  · -- `L_capped_disjoint`: key Nenadov–Pham observation!
    intro X hXs hXdisj
    rw [greedyAdvance_F, Finset.disjoint_insert_right] at hXdisj
    rcases hXdisj with ⟨hvX, hXdisjF⟩
    have hHp_eq : (greedyAdvance H ℓ U p K st v).Hp = st.Hp ∪ newly := rfl
    rw [hHp_eq]
    by_cases hXL : X ∈ st.L
    · have hzero : H.codegWeight newly X = 0 := by
        unfold WeightedHypergraph.codegWeight
        apply Finset.sum_eq_zero
        intro e he
        rcases Finset.mem_filter.mp he with ⟨heNew, hXe⟩
        exfalso
        exact hinv.L_kills_R X hXL e (Finset.mem_filter.mp heNew).1 hXe
      rw [H.codegWeight_union_disjoint hnewly_disj_Hp, hzero, add_zero]
      exact hinv.L_capped_disjoint X hXs hXdisjF
    · have hold := hinv.nonL_light X (Finset.mem_sdiff.mpr ⟨hXs, hXL⟩)
      have hXcard : 1 ≤ X.card := (Finset.mem_filter.mp hXs).2.1
      have hsub_ins : newly.filter (fun e => X ⊆ e) ⊆ H.edges.filter (fun e => insert v X ⊆ e) := by
        intro e he
        rcases Finset.mem_filter.mp he with ⟨heNew, hXe⟩
        rcases Finset.mem_filter.mp heNew with ⟨heR, hve⟩
        exact Finset.mem_filter.mpr ⟨hR_sub_edges heR, Finset.insert_subset_iff.mpr ⟨hve, hXe⟩⟩
      have hcard_ins : (insert v X).card = X.card + 1 := Finset.card_insert_of_notMem hvX
      have hdelta : H.codegWeight newly X ≤ H.totalWeight * K * p ^ X.card / (N₀ : ℚ) := by
        calc H.codegWeight newly X
            ≤ H.codegWeight H.edges (insert v X) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_ins (fun _ _ _ => hH.wt_nonneg _)
          _ ≤ H.totalWeight * K * p ^ ((insert v X).card - 1) / (N₀ : ℚ) :=
              hsp (insert v X) (by omega)
          _ = H.totalWeight * K * p ^ X.card / (N₀ : ℚ) := by rw [hcard_ins]; simp
      rw [H.codegWeight_union_disjoint hnewly_disj_Hp]
      have htwo : 2 * H.totalWeight * K * p ^ X.card / (N₀ : ℚ) =
          H.totalWeight * K * p ^ X.card / (N₀ : ℚ) + H.totalWeight * K * p ^ X.card / (N₀ : ℚ) := by ring
      linarith
  · -- `partition_edges`
    intro e he
    rcases Finset.mem_union.mp (hinv.partition_edges he) with heR_Hp | heD
    · rcases Finset.mem_union.mp heR_Hp with heR | heHp
      · by_cases hve : v ∈ e
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨heR, hve⟩)))
        · by_cases heNewD : e ∈ newD
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ heNewD)
          · apply Finset.mem_union_left _ (Finset.mem_union_left _ _)
            simp only [greedyAdvance, GreedyState.R, Finset.mem_sdiff, Finset.mem_filter,
              Finset.disjoint_insert_right, Finset.mem_union]
            refine ⟨⟨he, hve, hR_disj_F e heR⟩, ?_⟩
            rintro (heD | heND)
            · exact hR_not_D e heR heD
            · exact heNewD heND
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _ heHp))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ heD)

/-- Properties of `runGreedyRounds` after `k` rounds when `(I \ st.F).card ≥ k`. -/
lemma runGreedyRounds_spec (H : WeightedHypergraph N₀) (ℓ : ℕ) (U : Finset (Fin N₀))
    (p K : ℚ) (I : Finset (Fin N₀)) (hH : H.IsValidOn ℓ U) (hsp : H.IsSpread p K) :
    ∀ (k : ℕ) (st : GreedyState N₀),
      GreedyInvariant H ℓ U p K st →
      st.F ⊆ I →
      k ≤ (I \ st.F).card →
      let st' := runGreedyRounds H ℓ U p K I k st
      GreedyInvariant H ℓ U p K st' ∧
      st.F ⊆ st'.F ∧
      st'.F ⊆ I ∧
      st'.F.card = st.F.card + k ∧
      st'.R H ⊆ st.R H ∧
      (∀ u ∈ I \ st'.F, H.weightOf st.Hp + (k : ℚ) * H.degWeight (st'.R H) u ≤ H.weightOf st'.Hp) ∧
      (∀ F_hat : Finset (Fin N₀), st'.F ⊆ F_hat → F_hat ⊆ I →
        runGreedyRounds H ℓ U p K F_hat k st = st')
  | 0, st, hinv, hFI, _ => by
    simp only [runGreedyRounds]
    refine ⟨hinv, Finset.Subset.refl _, hFI, by omega, Finset.Subset.refl _, ?_, ?_⟩
    · intro u _; simp
    · intro _ _ _; trivial
  | k + 1, st, hinv, hFI, hk => by
    have hne : (I \ st.F).Nonempty := Finset.card_pos.mp (by omega)
    let v := pickBestVertex (H.degWeight (st.R H)) (I \ st.F) hne
    have hv_mem : v ∈ I \ st.F := pickBestVertex_mem (H.degWeight (st.R H)) hne
    have hv_I : v ∈ I := (Finset.mem_sdiff.mp hv_mem).1
    have hv_notF : v ∉ st.F := (Finset.mem_sdiff.mp hv_mem).2
    let st₁ := greedyAdvance H ℓ U p K st v
    have hrun_eq : runGreedyRounds H ℓ U p K I (k + 1) st = runGreedyRounds H ℓ U p K I k st₁ := by
      simp [runGreedyRounds, hne, v, st₁]
    have hinv₁ : GreedyInvariant H ℓ U p K st₁ := greedyAdvance_preserves H ℓ U p K st v hH hsp hinv
    have hF₁_sub : st₁.F ⊆ I := Finset.insert_subset_iff.mpr ⟨hv_I, hFI⟩
    have hsdiff_card : (I \ st₁.F).card + 1 = (I \ st.F).card := by
      have heq : insert v (I \ insert v st.F) = I \ st.F := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_sdiff, not_or]
        constructor
        · rintro (rfl | ⟨hxI, _, hxF⟩)
          · exact ⟨hv_I, hv_notF⟩
          · exact ⟨hxI, hxF⟩
        · rintro ⟨hxI, hxF⟩
          by_cases hxv : x = v
          · exact Or.inl hxv
          · exact Or.inr ⟨hxI, hxv, hxF⟩
      have hv_not_sdiff : v ∉ I \ insert v st.F := by simp
      have hcard := Finset.card_insert_of_notMem hv_not_sdiff
      rw [heq] at hcard
      simpa [st₁, greedyAdvance_F] using hcard.symm
    obtain ⟨hinv', hsub₁', hF'_I, hcard', hR'_sub₁, hdeg_ih, hsand_ih⟩ :=
      runGreedyRounds_spec H ℓ U p K I hH hsp k st₁ hinv₁ hF₁_sub (by omega)
    rw [hrun_eq]
    set st' := runGreedyRounds H ℓ U p K I k st₁
    have hF_sub' : st.F ⊆ st'.F := (Finset.subset_insert v st.F).trans hsub₁'
    have hR'_sub : st'.R H ⊆ st.R H := hR'_sub₁.trans (greedyAdvance_R_subset H ℓ U p K st v)
    refine ⟨hinv', hF_sub', hF'_I, ?_, hR'_sub, ?_, ?_⟩
    · have hF₁_card : st₁.F.card = st.F.card + 1 := Finset.card_insert_of_notMem hv_notF
      omega
    · -- Equation (4) of Nenadov–Pham: `w(Hp') ≥ w(Hp) + (k + 1) * deg_{R'}(u)`
      intro u hu
      have hu_I : u ∈ I := (Finset.mem_sdiff.mp hu).1
      have hu_notF' : u ∉ st'.F := (Finset.mem_sdiff.mp hu).2
      have hu_notF : u ∉ st.F := fun h => hu_notF' (hF_sub' h)
      have hu_sdiff : u ∈ I \ st.F := Finset.mem_sdiff.mpr ⟨hu_I, hu_notF⟩
      have hdeg_le_v : H.degWeight (st'.R H) u ≤ H.degWeight (st.R H) v := by
        calc H.degWeight (st'.R H) u
            ≤ H.degWeight (st.R H) u := H.degWeight_mono hH.wt_nonneg hR'_sub u
          _ ≤ H.degWeight (st.R H) v := pickBestVertex_deg_ge _ hne hu_sdiff
      have hwt₁ : H.weightOf st₁.Hp = H.weightOf st.Hp + H.degWeight (st.R H) v :=
        greedyAdvance_weightOf_Hp H ℓ U p K st v hinv
      have hih_u := hdeg_ih u hu
      push_cast
      linarith
    · -- Sandwich invariance: `runGreedyRounds ... F_hat (k + 1) st = st'`!
      intro F_hat hst'_Fhat hFhat_I
      have hv_in_st' : v ∈ st'.F := hsub₁' (Finset.mem_insert_self v st.F)
      have hv_in_Fhat : v ∈ F_hat \ st.F :=
        Finset.mem_sdiff.mpr ⟨hst'_Fhat hv_in_st', hv_notF⟩
      have hne_hat : (F_hat \ st.F).Nonempty := ⟨v, hv_in_Fhat⟩
      have hsub_sdiff : F_hat \ st.F ⊆ I \ st.F := Finset.sdiff_subset_sdiff hFhat_I (Finset.Subset.refl _)
      have hpick_eq : pickBestVertex (H.degWeight (st.R H)) (F_hat \ st.F) hne_hat = v :=
        pickBestVertex_sandwich _ hne_hat hne hsub_sdiff hv_in_Fhat
      simp only [runGreedyRounds, hne_hat, dif_pos, hpick_eq]
      exact hsand_ih F_hat hst'_Fhat hFhat_I

/-- Equation (3) of Nenadov–Pham: `2 ^ ℓ * H.weightOf st.Hp ≥ p * H.weightOf st.D`! -/
lemma weightOf_D_bound {H : WeightedHypergraph N₀} {ℓ : ℕ} {U : Finset (Fin N₀)}
    {p K : ℚ} {st : GreedyState N₀}
    (hH : H.IsValidOn ℓ U) (hsp : H.IsSpread p K)
    (hp : 0 < p) (hinv : GreedyInvariant H ℓ U p K st) :
    p * H.weightOf st.D ≤ (2 : ℚ) ^ ℓ * H.weightOf st.Hp := by
  -- Step 1: `H.weightOf st.D ≤ ∑_{X ∈ st.L} H.codegWeight H.edges X`
  have hD_le_sumL : H.weightOf st.D ≤ ∑ X ∈ st.L, H.codegWeight H.edges X := by
    have hbi_le : ∀ T : Finset (Finset (Fin N₀)),
        H.weightOf (T.biUnion (fun X => H.edges.filter (fun e => X ⊆ e))) ≤
          ∑ X ∈ T, H.codegWeight H.edges X := by
      intro T
      refine Finset.induction_on T (by simp [WeightedHypergraph.weightOf]) ?_
      intro a B haB ih
      rw [Finset.biUnion_insert, Finset.sum_insert haB]
      calc H.weightOf (H.edges.filter (fun e => a ⊆ e) ∪
              B.biUnion (fun X => H.edges.filter (fun e => X ⊆ e)))
          ≤ H.weightOf (H.edges.filter (fun e => a ⊆ e)) +
              H.weightOf (B.biUnion (fun X => H.edges.filter (fun e => X ⊆ e))) :=
            H.weightOf_union_le hH.wt_nonneg _ _
        _ ≤ H.codegWeight H.edges a + ∑ X ∈ B, H.codegWeight H.edges X :=
            add_le_add le_rfl ih
    have hD_sub_bi : st.D ⊆ st.L.biUnion (fun X => H.edges.filter (fun e => X ⊆ e)) := by
      intro e heD
      obtain ⟨X, hXL, hXe⟩ := hinv.D_covered_by_L e heD
      exact Finset.mem_biUnion.mpr ⟨X, hXL, Finset.mem_filter.mpr ⟨hinv.D_sub heD, hXe⟩⟩
    exact (H.weightOf_mono hH.wt_nonneg hD_sub_bi).trans (hbi_le st.L)
  -- Step 2: For each `X ∈ st.L`, `p * H.codegWeight H.edges X ≤ H.codegWeight st.Hp X`
  have hp_sumL : p * ∑ X ∈ st.L, H.codegWeight H.edges X ≤ ∑ X ∈ st.L, H.codegWeight st.Hp X := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro X hXL
    have hXs : X ∈ smallSubsets ℓ U := hinv.L_sub hXL
    have hXcard : 1 ≤ X.card := (Finset.mem_filter.mp hXs).2.1
    have hspX := hsp X hXcard
    have hheavyX := hinv.L_heavy X hXL
    have hp_pow : p * (H.totalWeight * K * p ^ (X.card - 1) / (N₀ : ℚ)) =
        H.totalWeight * K * p ^ X.card / (N₀ : ℚ) := by
      have hpow : p * p ^ (X.card - 1) = p ^ X.card := by
        cases hxc : X.card with
        | zero => omega
        | succ m => simp [pow_succ']
      calc p * (H.totalWeight * K * p ^ (X.card - 1) / (N₀ : ℚ))
          = H.totalWeight * K * (p * p ^ (X.card - 1)) / (N₀ : ℚ) := by ring
        _ = H.totalWeight * K * p ^ X.card / (N₀ : ℚ) := by rw [hpow]
    have hmul : p * H.codegWeight H.edges X ≤ p * (H.totalWeight * K * p ^ (X.card - 1) / (N₀ : ℚ)) :=
      mul_le_mul_of_nonneg_left hspX (le_of_lt hp)
    linarith
  -- Step 3: Double-count `(X, e)` with `X ∈ st.L`, `e ∈ st.Hp`, `X ⊆ e`: each `e ∈ st.Hp` has `e.card ≤ ℓ`,
  -- so `e.powerset.card = 2 ^ e.card ≤ 2 ^ ℓ`!
  have hsumL_le_Hp : ∑ X ∈ st.L, H.codegWeight st.Hp X ≤ (2 : ℚ) ^ ℓ * H.weightOf st.Hp := by
    unfold WeightedHypergraph.codegWeight WeightedHypergraph.weightOf
    have hswap : ∑ X ∈ st.L, ∑ e ∈ st.Hp.filter (fun e => X ⊆ e), H.wt e =
        ∑ e ∈ st.Hp, ((st.L.filter (fun X => X ⊆ e)).card : ℚ) * H.wt e := by
      calc ∑ X ∈ st.L, ∑ e ∈ st.Hp.filter (fun e => X ⊆ e), H.wt e
          = ∑ X ∈ st.L, ∑ e ∈ st.Hp, (if X ⊆ e then H.wt e else 0) := by
              refine Finset.sum_congr rfl (fun X _ => ?_)
              rw [Finset.sum_filter]
        _ = ∑ e ∈ st.Hp, ∑ X ∈ st.L, (if X ⊆ e then H.wt e else 0) := Finset.sum_comm
        _ = ∑ e ∈ st.Hp, ((st.L.filter (fun X => X ⊆ e)).card : ℚ) * H.wt e := by
              refine Finset.sum_congr rfl (fun e _ => ?_)
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hswap, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e heHp
    have he_card : e.card ≤ ℓ := hH.card_le e (hinv.Hp_sub heHp)
    have hsub_pow : st.L.filter (fun X => X ⊆ e) ⊆ e.powerset := by
      intro X hX
      exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hX).2
    have hcard_pow : (st.L.filter (fun X => X ⊆ e)).card ≤ 2 ^ ℓ := by
      calc (st.L.filter (fun X => X ⊆ e)).card
          ≤ e.powerset.card := Finset.card_le_card hsub_pow
        _ = 2 ^ e.card := Finset.card_powerset e
        _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) he_card
    have hcard_q : ((st.L.filter (fun X => X ⊆ e)).card : ℚ) ≤ (2 : ℚ) ^ ℓ := by
      exact_mod_cast hcard_pow
    exact mul_le_mul_of_nonneg_right hcard_q (hH.wt_nonneg e)
  have hpD : p * H.weightOf st.D ≤ p * ∑ X ∈ st.L, H.codegWeight H.edges X :=
    mul_le_mul_of_nonneg_left hD_le_sumL (le_of_lt hp)
  linarith

/-! ## Lower-Uniformity Projection (Case 1) and Single-Step Container Lemma 2.1 -/

/-- Project `Hp` onto `U \ F` by mapping each `e ∈ Hp` with `(e \ F).Nonempty` to `e \ F`
and summing weights across preimages. -/
def projectHypergraph (H : WeightedHypergraph N₀) (Hp : Finset (Finset (Fin N₀)))
    (F : Finset (Fin N₀)) : WeightedHypergraph N₀ where
  edges := (Hp.filter (fun e => (e \ F).Nonempty)).image (fun e => e \ F)
  wt := fun Y =>
    if Y.Nonempty ∧ Disjoint Y F then
      ∑ e ∈ Hp.filter (fun e => e \ F = Y), H.wt e
    else 0

lemma projectHypergraph_totalWeight {H : WeightedHypergraph N₀} {ℓ : ℕ} {U I : Finset (Fin N₀)}
    {p K : ℚ} {st : GreedyState N₀}
    (_hH : H.IsValidOn ℓ U) (hinv : GreedyInvariant H ℓ U p K st)
    (hF_sub : st.F ⊆ I) (hIndep : H.IsIndep I) :
    (projectHypergraph H st.Hp st.F).totalWeight = H.weightOf st.Hp := by
  -- Because `st.F ⊆ I` and `I` is independent in `H`, NO edge `e ∈ st.Hp ⊆ H.edges` satisfies `e ⊆ st.F`!
  -- Hence `(e \ st.F).Nonempty` holds for ALL `e ∈ st.Hp`!
  have hall_ne : ∀ e ∈ st.Hp, (e \ st.F).Nonempty := by
    intro e heHp
    rw [Finset.sdiff_nonempty]
    intro hsubF
    exact hIndep e (hinv.Hp_sub heHp) (hsubF.trans hF_sub)
  have hfilt_eq : st.Hp.filter (fun e => (e \ st.F).Nonempty) = st.Hp :=
    Finset.filter_true_of_mem hall_ne
  unfold WeightedHypergraph.totalWeight WeightedHypergraph.weightOf projectHypergraph
  dsimp only
  rw [hfilt_eq]
  rw [← Finset.sum_fiberwise_of_maps_to (s := st.Hp) (t := st.Hp.image (fun e => e \ st.F))
    (g := fun e => e \ st.F) (f := H.wt) (fun e he => Finset.mem_image_of_mem _ he)]
  apply Finset.sum_congr rfl
  intro Y hY
  rcases Finset.mem_image.mp hY with ⟨e₀, he₀, rfl⟩
  have hne₀ : (e₀ \ st.F).Nonempty := hall_ne e₀ he₀
  have hdisj₀ : Disjoint (e₀ \ st.F) st.F := Finset.sdiff_disjoint
  simp [hne₀, hdisj₀]

lemma projectHypergraph_valid_and_spread {H : WeightedHypergraph N₀} {ℓ : ℕ} {U I : Finset (Fin N₀)}
    {p K α : ℚ} {st : GreedyState N₀}
    (hℓ : 2 ≤ ℓ) (hH : H.IsValidOn ℓ U) (_hsp : H.IsSpread p K)
    (hp : 0 < p) (hK : 0 < K) (hα : 0 < α) (hN₀ : 0 < N₀)
    (hinv : GreedyInvariant H ℓ U p K st)
    (hF_sub : st.F ⊆ I) (hIndep : H.IsIndep I)
    (hheavy : α * p * H.totalWeight ≤ H.weightOf st.Hp) :
    let H₂ := projectHypergraph H st.Hp st.F
    H₂.IsValidOn (ℓ - 1) (U \ st.F) ∧
    H₂.IsSpread p (2 * K / α) ∧
    H₂.IsIndep (I \ st.F) := by
  set H₂ := projectHypergraph H st.Hp st.F
  have hall_ne : ∀ e ∈ st.Hp, (e \ st.F).Nonempty := by
    intro e heHp
    rw [Finset.sdiff_nonempty]
    intro hsubF
    exact hIndep e (hinv.Hp_sub heHp) (hsubF.trans hF_sub)
  have htot_eq : H₂.totalWeight = H.weightOf st.Hp :=
    projectHypergraph_totalWeight hH hinv hF_sub hIndep
  have htot_pos : 0 < H₂.totalWeight := by
    have hW : 0 < H.totalWeight := hH.total_pos
    have : 0 < α * p * H.totalWeight := by positivity
    linarith
  have hvalid : H₂.IsValidOn (ℓ - 1) (U \ st.F) := by
    refine
      { sub_domain := ?_
        nonempty_edge := ?_
        card_le := ?_
        wt_pos := ?_
        wt_nonneg := ?_
        total_pos := htot_pos }
    · intro Y hY
      rcases Finset.mem_image.mp hY with ⟨e, he, rfl⟩
      have heH : e ∈ H.edges := hinv.Hp_sub (Finset.mem_filter.mp he).1
      exact Finset.sdiff_subset_sdiff (hH.sub_domain e heH) (Finset.Subset.refl _)
    · intro Y hY
      rcases Finset.mem_image.mp hY with ⟨e, he, rfl⟩
      exact Finset.card_pos.mpr (Finset.mem_filter.mp he).2
    · intro Y hY
      rcases Finset.mem_image.mp hY with ⟨e, he, rfl⟩
      have heHp : e ∈ st.Hp := (Finset.mem_filter.mp he).1
      have he_le : e.card ≤ ℓ := hH.card_le e (hinv.Hp_sub heHp)
      -- Since `¬Disjoint e st.F`, `e` contains some `x ∈ st.F`, so `(e \ st.F).card < e.card ≤ ℓ`!
      have hnot_disj := hinv.Hp_hits_F e heHp
      rw [Finset.not_disjoint_iff] at hnot_disj
      obtain ⟨x, hxe, hxF⟩ := hnot_disj
      have hssub : e \ st.F ⊂ e := by
        refine Finset.ssubset_iff_of_subset Finset.sdiff_subset |>.mpr ?_
        exact ⟨x, hxe, by simp [hxF]⟩
      have hlt : (e \ st.F).card < e.card := Finset.card_lt_card hssub
      omega
    · intro Y hY
      rcases Finset.mem_image.mp hY with ⟨e, he, rfl⟩
      have heHp : e ∈ st.Hp := (Finset.mem_filter.mp he).1
      have hne : (e \ st.F).Nonempty := (Finset.mem_filter.mp he).2
      have hdisj : Disjoint (e \ st.F) st.F := Finset.sdiff_disjoint
      simp only [H₂, projectHypergraph, hne, hdisj, and_self, ↓reduceIte]
      have he_in : e ∈ st.Hp.filter (fun e' => e' \ st.F = e \ st.F) :=
        Finset.mem_filter.mpr ⟨heHp, rfl⟩
      calc 0 < H.wt e := hH.wt_pos e (hinv.Hp_sub heHp)
        _ ≤ ∑ e' ∈ st.Hp.filter (fun e' => e' \ st.F = e \ st.F), H.wt e' :=
            Finset.single_le_sum (fun e' _ => hH.wt_nonneg e') he_in
    · intro Y
      simp only [H₂, projectHypergraph]
      split_ifs
      · exact Finset.sum_nonneg (fun e _ => hH.wt_nonneg e)
      · exact le_rfl
  refine ⟨hvalid, ?_, ?_⟩
  · -- `(p, 2 * K / α)`-spread of `H₂`
    intro X hXcard
    by_cases hXsub : X ⊆ U \ st.F
    · by_cases hXle : X.card ≤ ℓ - 1
      · have hXdisj : Disjoint X st.F :=
          Disjoint.mono_left hXsub Finset.sdiff_disjoint
        have hXsmall : X ∈ smallSubsets ℓ U := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hXcard, hXle⟩
          exact hXsub.trans Finset.sdiff_subset
        -- Show `H₂.codegWeight H₂.edges X = H.codegWeight st.Hp X`!
        have hcodeg_eq : H₂.codegWeight H₂.edges X = H.codegWeight st.Hp X := by
          unfold WeightedHypergraph.codegWeight
          have hfilt_Hp : st.Hp.filter (fun e => (e \ st.F).Nonempty) = st.Hp :=
            Finset.filter_true_of_mem hall_ne
          -- Fiberwise sum of `st.Hp.filter (X ⊆ ·)` under `e ↦ e \ st.F`
          have hmaps : ∀ e ∈ st.Hp.filter (fun e => X ⊆ e),
              e \ st.F ∈ H₂.edges.filter (fun Y => X ⊆ Y) := by
            intro e he
            rcases Finset.mem_filter.mp he with ⟨heHp, hXe⟩
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · simp only [H₂, projectHypergraph, hfilt_Hp]
              exact Finset.mem_image_of_mem _ heHp
            · exact Finset.subset_sdiff.mpr ⟨hXe, hXdisj⟩
          rw [← Finset.sum_fiberwise_of_maps_to hmaps]
          apply Finset.sum_congr rfl
          intro Y hY
          rcases Finset.mem_filter.mp hY with ⟨hYedges, hXY⟩
          rcases Finset.mem_image.mp hYedges with ⟨e₀, he₀, rfl⟩
          have hne₀ : (e₀ \ st.F).Nonempty := (Finset.mem_filter.mp he₀).2
          have hdisj₀ : Disjoint (e₀ \ st.F) st.F := Finset.sdiff_disjoint
          simp only [H₂, projectHypergraph, hne₀, hdisj₀, and_self, ↓reduceIte]
          apply Finset.sum_congr ?_ (fun _ _ => rfl)
          ext e
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨heHp, hfib⟩
            refine ⟨⟨heHp, ?_⟩, hfib⟩
            exact hXY.trans (hfib ▸ Finset.sdiff_subset)
          · rintro ⟨⟨heHp, _⟩, hfib⟩
            exact ⟨heHp, hfib⟩
        rw [hcodeg_eq]
        have hcap := hinv.L_capped_disjoint X hXsmall hXdisj
        -- Bound `2 * W * K * p ^ |X| / N₀ ≤ H₂.totalWeight * (2 * K / α) * p ^ (|X| - 1) / N₀`!
        have hp_pow : p ^ X.card = p * p ^ (X.card - 1) := by
          cases hxc : X.card with
          | zero => omega
          | succ m => simp [pow_succ']
        have hW_le : p * H.totalWeight ≤ H₂.totalWeight / α := by
          rw [htot_eq, le_div_iff₀ hα]
          linarith
        have hmul_nonneg : 0 ≤ 2 * K * p ^ (X.card - 1) / (N₀ : ℚ) := by positivity
        calc H.codegWeight st.Hp X
            ≤ 2 * H.totalWeight * K * p ^ X.card / (N₀ : ℚ) := hcap
          _ = (p * H.totalWeight) * (2 * K * p ^ (X.card - 1) / (N₀ : ℚ)) := by
              rw [hp_pow]; ring
          _ ≤ (H₂.totalWeight / α) * (2 * K * p ^ (X.card - 1) / (N₀ : ℚ)) :=
              mul_le_mul_of_nonneg_right hW_le hmul_nonneg
          _ = H₂.totalWeight * (2 * K / α) * p ^ (X.card - 1) / (N₀ : ℚ) := by ring
      · -- `X.card > ℓ - 1`: no edge of `H₂` has size `≥ X.card`, so `codegWeight = 0`!
        have hzero : H₂.codegWeight H₂.edges X = 0 := by
          unfold WeightedHypergraph.codegWeight
          apply Finset.sum_eq_zero
          intro Y hY
          rcases Finset.mem_filter.mp hY with ⟨hYe, hXY⟩
          have hYle := hvalid.card_le Y hYe
          have hXleY := Finset.card_le_card hXY
          omega
        rw [hzero]
        have : 0 ≤ H₂.totalWeight := le_of_lt htot_pos
        positivity
    · -- `¬(X ⊆ U \ st.F)`: no edge of `H₂` (all `⊆ U \ st.F`) contains `X`, so `codegWeight = 0`!
      have hzero : H₂.codegWeight H₂.edges X = 0 := by
        unfold WeightedHypergraph.codegWeight
        apply Finset.sum_eq_zero
        intro Y hY
        rcases Finset.mem_filter.mp hY with ⟨hYe, hXY⟩
        exfalso
        exact hXsub (hXY.trans (hvalid.sub_domain Y hYe))
      rw [hzero]
      have : 0 ≤ H₂.totalWeight := le_of_lt htot_pos
      positivity
  · -- `H₂.IsIndep (I \ st.F)`
    intro Y hY hYI
    rcases Finset.mem_image.mp hY with ⟨e, he, rfl⟩
    have heHp : e ∈ st.Hp := (Finset.mem_filter.mp he).1
    have heI : e ⊆ I := by
      intro x hxe
      by_cases hxF : x ∈ st.F
      · exact hF_sub hxF
      · exact (Finset.mem_sdiff.mp (hYI (Finset.mem_sdiff.mpr ⟨hxe, hxF⟩))).1
    exact hIndep e (hinv.Hp_sub heHp) heI

/-! ## Modular Helper Lemmas and Single-Step Container Lemma 2.1 -/

/-- For any edge subset `E ⊆ H.edges` whose edges all lie inside `W : Finset (Fin N₀)`,
`H.weightOf E ≤ ∑ v ∈ W, H.degWeight E v`. -/
lemma weightOf_le_sum_degWeight {H : WeightedHypergraph N₀} {ℓ : ℕ} {U W : Finset (Fin N₀)}
    (hH : H.IsValidOn ℓ U) {E : Finset (Finset (Fin N₀))}
    (hE_sub : E ⊆ H.edges) (hE_W : ∀ e ∈ E, e ⊆ W) :
    H.weightOf E ≤ ∑ v ∈ W, H.degWeight E v := by
  unfold WeightedHypergraph.weightOf WeightedHypergraph.degWeight WeightedHypergraph.codegWeight
  have hswap : ∑ v ∈ W, ∑ e ∈ E.filter (fun e => {v} ⊆ e), H.wt e =
      ∑ e ∈ E, ((W.filter (fun v => v ∈ e)).card : ℚ) * H.wt e := by
    calc ∑ v ∈ W, ∑ e ∈ E.filter (fun e => {v} ⊆ e), H.wt e
        = ∑ v ∈ W, ∑ e ∈ E, (if v ∈ e then H.wt e else 0) := by
            refine Finset.sum_congr rfl (fun v _ => ?_)
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl (fun e _ => ?_)
            simp
      _ = ∑ e ∈ E, ∑ v ∈ W, (if v ∈ e then H.wt e else 0) := Finset.sum_comm
      _ = ∑ e ∈ E, ((W.filter (fun v => v ∈ e)).card : ℚ) * H.wt e := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hswap]
  apply Finset.sum_le_sum
  intro e heE
  have heH : e ∈ H.edges := hE_sub heE
  have heW : W.filter (fun v => v ∈ e) = e := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun hv => ⟨hE_W e heE hv, hv⟩⟩
  rw [heW]
  have h1 : (1 : ℚ) ≤ (e.card : ℚ) := by exact_mod_cast hH.nonempty_edge e heH
  calc H.wt e = 1 * H.wt e := (one_mul _).symm
    _ ≤ (e.card : ℚ) * H.wt e := mul_le_mul_of_nonneg_right h1 (hH.wt_nonneg e)

lemma degWeight_le_of_spread {H : WeightedHypergraph N₀} {p K : ℚ}
    (hsp : H.IsSpread p K) (v : Fin N₀) :
    H.degWeight H.edges v ≤ H.totalWeight * K / (N₀ : ℚ) := by
  have h := hsp {v} (by simp)
  simpa [WeightedHypergraph.degWeight] using h

/-- Any valid `(p, K)`-spread hypergraph on `U` satisfies `(N₀ : ℚ) / K ≤ U.card`. -/
lemma domain_card_ge_of_valid_spread {H : WeightedHypergraph N₀} {ℓ : ℕ} {U : Finset (Fin N₀)}
    {p K : ℚ} (hN₀ : 0 < N₀) (hK : 0 < K) (hH : H.IsValidOn ℓ U) (hsp : H.IsSpread p K) :
    (N₀ : ℚ) / K ≤ (U.card : ℚ) := by
  have h1 : H.totalWeight ≤ ∑ v ∈ U, H.degWeight H.edges v :=
    weightOf_le_sum_degWeight hH (Finset.Subset.refl _) hH.sub_domain
  have h2 : ∑ v ∈ U, H.degWeight H.edges v ≤ (U.card : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := by
    calc ∑ v ∈ U, H.degWeight H.edges v
        ≤ ∑ _v ∈ U, (H.totalWeight * K / (N₀ : ℚ)) :=
          Finset.sum_le_sum (fun v _ => degWeight_le_of_spread hsp v)
      _ = (U.card : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hW_pos : 0 < H.totalWeight := hH.total_pos
  have hN₀_q : (0 : ℚ) < (N₀ : ℚ) := by exact_mod_cast hN₀
  have hineq : H.totalWeight ≤ (U.card : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := le_trans h1 h2
  have hmul : (N₀ : ℚ) * H.totalWeight ≤ ((U.card : ℚ) * K) * H.totalWeight := by
    have h := mul_le_mul_of_nonneg_left hineq (le_of_lt hN₀_q)
    have hrhs : (N₀ : ℚ) * ((U.card : ℚ) * (H.totalWeight * K / (N₀ : ℚ))) =
        ((U.card : ℚ) * K) * H.totalWeight := by
      field_simp [ne_of_gt hN₀_q]
    linarith
  have hNK : (N₀ : ℚ) ≤ (U.card : ℚ) * K := le_of_mul_le_mul_right hmul hW_pos
  rwa [div_le_iff₀ hK]

/-- Nenadov–Pham single-shrinkage algorithm (Lemma 2.1) for `ℓ = j + 1`. -/
noncomputable def containerStep :
    (j : ℕ) → (U : Finset (Fin N₀)) → (H : WeightedHypergraph N₀) →
    (p K : ℚ) → (S : Finset (Fin N₀)) → Finset (Fin N₀) × Finset (Fin N₀)
  | 0, U, H, _p, _K, _S =>
    (∅, U.filter (fun v => H.degWeight H.edges v = 0))
  | j + 1, U, H, p, K, S =>
    let ℓ := j + 2
    let s : ℕ := ⌈(N₀ : ℚ) * p⌉₊
    if S.card < s then
      (S, ∅)
    else
      let st := runGreedyRounds H ℓ U p K S s initGreedyState
      let α : ℚ := 1 / (2 : ℚ) ^ (ℓ + 2)
      if α * p * H.totalWeight ≤ H.weightOf st.Hp then
        let H₂ := projectHypergraph H st.Hp st.F
        let res := containerStep j (U \ st.F) H₂ p (2 * K / α) (S \ st.F)
        (st.F ∪ res.1, res.2)
      else
        let C := (U \ st.F).filter (fun v => H.degWeight (st.R H) v ≤ α * H.totalWeight / (N₀ : ℚ))
        (st.F, C)

/-- Shrinkage constant `δ_j(K) > 0` guaranteed by `containerStep j` (`ℓ = j + 1`). -/
def shrinkDelta : ℕ → ℚ → ℚ
  | 0, K => 1 / K
  | j + 1, K =>
    let α : ℚ := 1 / (2 : ℚ) ^ (j + 4)
    min (1 / (4 * K)) (shrinkDelta j (2 * K / α))

lemma shrinkDelta_pos : ∀ (j : ℕ) {K : ℚ}, 0 < K → 0 < shrinkDelta j K
  | 0, _K, hK => by simp [shrinkDelta]; positivity
  | j + 1, _K, hK => by
    simp only [shrinkDelta, lt_min_iff]
    exact ⟨by positivity, shrinkDelta_pos j (by positivity)⟩

/-- Base case `j = 0` (`ℓ = 1`) of `containerStep_spec`. -/
private lemma containerStep_zero_spec (U : Finset (Fin N₀)) (H : WeightedHypergraph N₀)
    (p K : ℚ) (I : Finset (Fin N₀))
    (hN₀ : 0 < N₀) (hK : 0 < K) (hH : H.IsValidOn 1 U) (hsp : H.IsSpread p K)
    (hIU : I ⊆ U) (hIndep : H.IsIndep I) :
    let FC := containerStep 0 U H p K I
    FC.1 ⊆ I ∧
    FC.2 ⊆ U \ FC.1 ∧
    I ⊆ FC.2 ∪ FC.1 ∧
    FC.1.card ≤ 1 * ⌈(N₀ : ℚ) * p⌉₊ ∧
    (FC.2.card : ℚ) + shrinkDelta 0 K * (N₀ : ℚ) ≤ (U.card : ℚ) ∧
    (∀ F_hat : Finset (Fin N₀), FC.1 ⊆ F_hat → F_hat ⊆ I →
      containerStep 0 U H p K F_hat = FC) := by
  dsimp only [containerStep, shrinkDelta]
  set C := U.filter (fun v => H.degWeight H.edges v = 0)
  refine ⟨Finset.empty_subset _, ?_, ?_, Nat.zero_le _, ?_, ?_⟩
  · simp [C, Finset.filter_subset]
  · intro v hvI
    rw [Finset.union_empty]
    refine Finset.mem_filter.mpr ⟨hIU hvI, ?_⟩
    unfold WeightedHypergraph.degWeight WeightedHypergraph.codegWeight
    apply Finset.sum_eq_zero
    intro e he
    rcases Finset.mem_filter.mp he with ⟨heH, hve⟩
    exfalso
    have hcard1 : e.card = 1 := le_antisymm (hH.card_le e heH) (hH.nonempty_edge e heH)
    obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hcard1
    have hvw : v = w := Finset.mem_singleton.mp (hve (Finset.mem_singleton_self v))
    subst hvw
    exact hIndep {v} heH (Finset.singleton_subset_iff.mpr hvI)
  · have hCU : C ⊆ U := Finset.filter_subset _ U
    have h1 : H.totalWeight ≤ ∑ v ∈ U, H.degWeight H.edges v :=
      weightOf_le_sum_degWeight hH (Finset.Subset.refl _) hH.sub_domain
    have hsplit : ∑ v ∈ U, H.degWeight H.edges v = ∑ v ∈ U \ C, H.degWeight H.edges v := by
      rw [← Finset.sum_sdiff hCU]
      have h0 : ∑ v ∈ C, H.degWeight H.edges v = 0 :=
        Finset.sum_eq_zero (fun v hv => (Finset.mem_filter.mp hv).2)
      linarith
    have h2 : ∑ v ∈ U \ C, H.degWeight H.edges v ≤
        ((U \ C).card : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := by
      calc ∑ v ∈ U \ C, H.degWeight H.edges v
          ≤ ∑ _v ∈ U \ C, (H.totalWeight * K / (N₀ : ℚ)) :=
            Finset.sum_le_sum (fun v _ => degWeight_le_of_spread hsp v)
        _ = ((U \ C).card : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hW_pos : 0 < H.totalWeight := hH.total_pos
    have hN₀_q : (0 : ℚ) < (N₀ : ℚ) := by exact_mod_cast hN₀
    have hineq : H.totalWeight ≤ ((U \ C).card : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := by linarith
    have hmul : (N₀ : ℚ) * H.totalWeight ≤ (((U \ C).card : ℚ) * K) * H.totalWeight := by
      have h := mul_le_mul_of_nonneg_left hineq (le_of_lt hN₀_q)
      have hrhs : (N₀ : ℚ) * (((U \ C).card : ℚ) * (H.totalWeight * K / (N₀ : ℚ))) =
          (((U \ C).card : ℚ) * K) * H.totalWeight := by
        field_simp [ne_of_gt hN₀_q]
      linarith
    have hNK : (N₀ : ℚ) ≤ ((U \ C).card : ℚ) * K := le_of_mul_le_mul_right hmul hW_pos
    have hdiv : 1 / K * (N₀ : ℚ) ≤ ((U \ C).card : ℚ) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK]
      exact hNK
    have hcard_add : (U \ C).card + C.card = U.card := Finset.card_sdiff_add_card_eq_card hCU
    have hcard_q : ((U \ C).card : ℚ) + (C.card : ℚ) = (U.card : ℚ) := by exact_mod_cast hcard_add
    linarith
  · intro _ _ _; rfl

/-- Case 2 shrinkage calculation extracted into its own fast lemma. -/
private lemma case2_shrink_bound {H : WeightedHypergraph N₀} {j : ℕ} {U : Finset (Fin N₀)}
    {p K : ℚ} {st : GreedyState N₀}
    (hN₀ : 0 < N₀) (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 < K)
    (hH : H.IsValidOn (j + 2) U) (hsp : H.IsSpread p K)
    (hinv : GreedyInvariant H (j + 2) U p K st)
    (hlt_Hp : H.weightOf st.Hp < (1 / (2 : ℚ) ^ (j + 4)) * p * H.totalWeight) :
    let α : ℚ := 1 / (2 : ℚ) ^ (j + 4)
    let C := (U \ st.F).filter (fun v => H.degWeight (st.R H) v ≤ α * H.totalWeight / (N₀ : ℚ))
    (C.card : ℚ) + shrinkDelta (j + 1) K * (N₀ : ℚ) ≤ (U.card : ℚ) := by
  let α : ℚ := 1 / (2 : ℚ) ^ (j + 4)
  set C := (U \ st.F).filter (fun v => H.degWeight (st.R H) v ≤ α * H.totalWeight / (N₀ : ℚ))
  have hα_pos : 0 < α := by positivity
  have hα_le_16 : α ≤ 1 / 16 := by
    dsimp only [α]
    have hpow : (16 : ℚ) ≤ (2 : ℚ) ^ (j + 4) := by
      calc (16 : ℚ) = (2 : ℚ) ^ 4 := by norm_num
        _ ≤ (2 : ℚ) ^ (j + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact one_div_le_one_div_of_le (by norm_num) hpow
  have hW_pos : 0 < H.totalWeight := hH.total_pos
  have hHp_quarter : H.weightOf st.Hp < H.totalWeight / 4 := by
    have hpW : α * p * H.totalWeight ≤ α * H.totalWeight := by
      have h1 : p * (α * H.totalWeight) ≤ 1 * (α * H.totalWeight) :=
        mul_le_mul_of_nonneg_right hp1 (by positivity)
      linarith
    have hαW : α * H.totalWeight ≤ (1 / 16) * H.totalWeight :=
      mul_le_mul_of_nonneg_right hα_le_16 (le_of_lt hW_pos)
    linarith
  have hD_quarter : H.weightOf st.D < H.totalWeight / 4 := by
    have hD_bd := weightOf_D_bound hH hsp hp hinv
    have hpow_α : (2 : ℚ) ^ (j + 2) * α = 1 / 4 := by
      dsimp only [α]
      have hexp : j + 4 = (j + 2) + 2 := by omega
      rw [hexp, pow_add]
      have h2l : (2 : ℚ) ^ (j + 2) ≠ 0 := by positivity
      field_simp [h2l]
      ring
    have hmul : (2 : ℚ) ^ (j + 2) * H.weightOf st.Hp < (2 : ℚ) ^ (j + 2) * (α * p * H.totalWeight) :=
      mul_lt_mul_of_pos_left hlt_Hp (by positivity)
    have hrhs : (2 : ℚ) ^ (j + 2) * (α * p * H.totalWeight) = p * (H.totalWeight / 4) := by
      calc (2 : ℚ) ^ (j + 2) * (α * p * H.totalWeight)
          = ((2 : ℚ) ^ (j + 2) * α) * (p * H.totalWeight) := by ring
        _ = (1 / 4) * (p * H.totalWeight) := by rw [hpow_α]
        _ = p * (H.totalWeight / 4) := by ring
    have hp_lt : p * H.weightOf st.D < p * (H.totalWeight / 4) := by linarith
    exact lt_of_mul_lt_mul_left hp_lt (le_of_lt hp)
  have hR_half : H.totalWeight / 2 < H.weightOf (st.R H) := by
    let wR := H.weightOf (st.R H)
    let wHp := H.weightOf st.Hp
    let wD := H.weightOf st.D
    have hcov : H.totalWeight ≤ wR + wHp + wD := by
      have hu1 : H.totalWeight ≤ H.weightOf (st.R H ∪ st.Hp ∪ st.D) :=
        H.weightOf_mono hH.wt_nonneg hinv.partition_edges
      have hu2 : H.weightOf (st.R H ∪ st.Hp ∪ st.D) ≤ H.weightOf (st.R H ∪ st.Hp) + wD :=
        H.weightOf_union_le hH.wt_nonneg (st.R H ∪ st.Hp) st.D
      have hu3 : H.weightOf (st.R H ∪ st.Hp) ≤ wR + wHp :=
        H.weightOf_union_le hH.wt_nonneg (st.R H) st.Hp
      linarith
    have h1 : wHp < H.totalWeight / 4 := hHp_quarter
    have h2 : wD < H.totalWeight / 4 := hD_quarter
    linarith
  have hR_sub_H : st.R H ⊆ H.edges := fun e he =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).1
  have hR_UF : ∀ e ∈ st.R H, e ⊆ U \ st.F := by
    intro e heR
    have heH : e ∈ H.edges := hR_sub_H heR
    have heDisj : Disjoint e st.F := (Finset.mem_filter.mp (Finset.mem_sdiff.mp heR).1).2
    exact Finset.subset_sdiff.mpr ⟨hH.sub_domain e heH, heDisj⟩
  have hR_le_sum : H.weightOf (st.R H) ≤ ∑ v ∈ U \ st.F, H.degWeight (st.R H) v :=
    weightOf_le_sum_degWeight hH hR_sub_H hR_UF
  have hC_sub_UF : C ⊆ U \ st.F := Finset.filter_subset _ _
  have hsplit : ∑ v ∈ U \ st.F, H.degWeight (st.R H) v =
      (∑ v ∈ C, H.degWeight (st.R H) v) + ∑ v ∈ (U \ st.F) \ C, H.degWeight (st.R H) v := by
    rw [add_comm, Finset.sum_sdiff hC_sub_UF]
  have hN₀_q : (0 : ℚ) < (N₀ : ℚ) := by exact_mod_cast hN₀
  have hsum_C : ∑ v ∈ C, H.degWeight (st.R H) v ≤ α * H.totalWeight := by
    have hC_card_le : (C.card : ℚ) ≤ (N₀ : ℚ) := by
      have hle : C.card ≤ Fintype.card (Fin N₀) := Finset.card_le_univ C
      simpa using hle
    calc ∑ v ∈ C, H.degWeight (st.R H) v
        ≤ ∑ _v ∈ C, (α * H.totalWeight / (N₀ : ℚ)) :=
          Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = (C.card : ℚ) * (α * H.totalWeight / (N₀ : ℚ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N₀ : ℚ) * (α * H.totalWeight / (N₀ : ℚ)) :=
          mul_le_mul_of_nonneg_right hC_card_le (by positivity)
      _ = α * H.totalWeight := by field_simp [ne_of_gt hN₀_q]
  have hCU : C ⊆ U := hC_sub_UF.trans Finset.sdiff_subset
  have hsum_rem : ∑ v ∈ (U \ st.F) \ C, H.degWeight (st.R H) v ≤
      ((U.card - C.card : ℕ) : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := by
    have hrem_sub : (U \ st.F) \ C ⊆ U \ C :=
      Finset.sdiff_subset_sdiff Finset.sdiff_subset (Finset.Subset.refl _)
    have hrem_card : ((U \ st.F) \ C).card ≤ U.card - C.card := by
      have hadd := Finset.card_sdiff_add_card_eq_card hCU
      have hle := Finset.card_le_card hrem_sub
      omega
    calc ∑ v ∈ (U \ st.F) \ C, H.degWeight (st.R H) v
        ≤ ∑ v ∈ (U \ st.F) \ C, H.degWeight H.edges v :=
          Finset.sum_le_sum (fun v _ => H.degWeight_mono hH.wt_nonneg hR_sub_H v)
      _ ≤ ∑ _v ∈ (U \ st.F) \ C, (H.totalWeight * K / (N₀ : ℚ)) :=
          Finset.sum_le_sum (fun v _ => degWeight_le_of_spread hsp v)
      _ = (((U \ st.F) \ C).card : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((U.card - C.card : ℕ) : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hrem_card) (by positivity)
  have hαW : α * H.totalWeight ≤ (1 / 16) * H.totalWeight :=
    mul_le_mul_of_nonneg_right hα_le_16 (le_of_lt hW_pos)
  have hquarter_le : H.totalWeight / 4 ≤
      ((U.card - C.card : ℕ) : ℚ) * (H.totalWeight * K / (N₀ : ℚ)) := by linarith
  have hmul4 : (N₀ : ℚ) * H.totalWeight ≤
      (4 * K * ((U.card - C.card : ℕ) : ℚ)) * H.totalWeight := by
    have h := mul_le_mul_of_nonneg_left hquarter_le (by positivity : (0 : ℚ) ≤ 4 * (N₀ : ℚ))
    have hlhs : 4 * (N₀ : ℚ) * (H.totalWeight / 4) = (N₀ : ℚ) * H.totalWeight := by ring
    have hrhs : 4 * (N₀ : ℚ) * (((U.card - C.card : ℕ) : ℚ) * (H.totalWeight * K / (N₀ : ℚ))) =
        (4 * K * ((U.card - C.card : ℕ) : ℚ)) * H.totalWeight := by
      field_simp [ne_of_gt hN₀_q]
    linarith
  have hNK4 : (N₀ : ℚ) ≤ 4 * K * ((U.card - C.card : ℕ) : ℚ) :=
    le_of_mul_le_mul_right hmul4 hW_pos
  have hdiv4 : 1 / (4 * K) * (N₀ : ℚ) ≤ ((U.card - C.card : ℕ) : ℚ) := by
    have h4Kpos : 0 < 4 * K := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h4Kpos]
    linarith
  have hCleU : C.card ≤ U.card := Finset.card_le_card hCU
  have hsub_cast : (C.card : ℚ) + ((U.card - C.card : ℕ) : ℚ) = (U.card : ℚ) := by
    exact_mod_cast Nat.add_sub_of_le hCleU
  have hdel_le : shrinkDelta (j + 1) K ≤ 1 / (4 * K) := min_le_left _ _
  have hdel_mul : shrinkDelta (j + 1) K * (N₀ : ℚ) ≤ 1 / (4 * K) * (N₀ : ℚ) :=
    mul_le_mul_of_nonneg_right hdel_le (le_of_lt hN₀_q)
  linarith

/-- Full specification of `containerStep` (Nenadov–Pham Lemma 2.1 + Sandwich Invariance)! -/
theorem containerStep_spec :
    ∀ (j : ℕ) (U : Finset (Fin N₀)) (H : WeightedHypergraph N₀) (p K : ℚ) (I : Finset (Fin N₀)),
      0 < N₀ → 0 < p → p ≤ 1 → 0 < K →
      H.IsValidOn (j + 1) U →
      H.IsSpread p K →
      I ⊆ U →
      H.IsIndep I →
      let FC := containerStep j U H p K I
      FC.1 ⊆ I ∧
      FC.2 ⊆ U \ FC.1 ∧
      I ⊆ FC.2 ∪ FC.1 ∧
      FC.1.card ≤ (j + 1) * ⌈(N₀ : ℚ) * p⌉₊ ∧
      (FC.2.card : ℚ) + shrinkDelta j K * (N₀ : ℚ) ≤ (U.card : ℚ) ∧
      (∀ F_hat : Finset (Fin N₀), FC.1 ⊆ F_hat → F_hat ⊆ I →
        containerStep j U H p K F_hat = FC)
  | 0, U, H, p, K, I, hN₀, _hp, _hp1, hK, hH, hsp, hIU, hIndep =>
    containerStep_zero_spec U H p K I hN₀ hK hH hsp hIU hIndep
  | j + 1, U, H, p, K, I, hN₀, hp, hp1, hK, hH, hsp, hIU, hIndep => by
    let s : ℕ := ⌈(N₀ : ℚ) * p⌉₊
    by_cases hsmall : I.card < s
    · have hstep_eq : containerStep (j + 1) U H p K I = (I, ∅) := by
        unfold containerStep
        exact if_pos hsmall
      rw [hstep_eq]
      have hU_ge := domain_card_ge_of_valid_spread hN₀ hK hH hsp
      have hdel_le : shrinkDelta (j + 1) K ≤ 1 / (4 * K) := min_le_left _ _
      have hN₀_nonneg : (0 : ℚ) ≤ (N₀ : ℚ) := by positivity
      have h4K : 1 / (4 * K) * (N₀ : ℚ) ≤ (N₀ : ℚ) / K := by
        have hdiff : (N₀ : ℚ) / K - 1 / (4 * K) * (N₀ : ℚ) = 3 * (N₀ : ℚ) / (4 * K) := by
          field_simp [ne_of_gt hK]; ring
        have hnn : 0 ≤ 3 * (N₀ : ℚ) / (4 * K) := by positivity
        linarith
      refine ⟨Finset.Subset.refl _, Finset.empty_subset _, by simp, ?_, ?_, ?_⟩
      · calc I.card ≤ s := le_of_lt hsmall
          _ = 1 * s := (one_mul s).symm
          _ ≤ (j + 2) * s := Nat.mul_le_mul_right s (by omega)
      · have h1 : shrinkDelta (j + 1) K * (N₀ : ℚ) ≤ 1 / (4 * K) * (N₀ : ℚ) :=
          mul_le_mul_of_nonneg_right hdel_le hN₀_nonneg
        simp only [Finset.card_empty, Nat.cast_zero, zero_add]
        linarith
      · intro F_hat hI_Fhat hFhat_I
        have hFhat_eq : F_hat = I := Finset.Subset.antisymm hFhat_I hI_Fhat
        subst hFhat_eq
        exact hstep_eq
    · have hs_le : s ≤ I.card := le_of_not_gt hsmall
      have hinv₀ : GreedyInvariant H (j + 2) U p K initGreedyState :=
        greedyInvariant_init H (j + 2) U p K hH hp hK hN₀
      have hs_sdiff : s ≤ (I \ (initGreedyState : GreedyState N₀).F).card := by
        simpa [initGreedyState] using hs_le
      obtain ⟨hinv, _, hF_I, hF_card, _, hdeg_max, hsand_rounds⟩ :=
        runGreedyRounds_spec H (j + 2) U p K I hH hsp s initGreedyState hinv₀ (Finset.empty_subset _) hs_sdiff
      set st := runGreedyRounds H (j + 2) U p K I s initGreedyState
      have hF_card_eq : st.F.card = s := by simpa [initGreedyState] using hF_card
      let α : ℚ := 1 / (2 : ℚ) ^ (j + 4)
      have hα_pos : 0 < α := by positivity
      by_cases hcase1 : α * p * H.totalWeight ≤ H.weightOf st.Hp
      · obtain ⟨hH₂_valid, hH₂_sp, hH₂_indep⟩ :=
          projectHypergraph_valid_and_spread (by omega) hH hsp hp hK hα_pos hN₀ hinv hF_I hIndep hcase1
        set H₂ := projectHypergraph H st.Hp st.F
        have hK₂_pos : 0 < 2 * K / α := by positivity
        have hI₂_sub : I \ st.F ⊆ U \ st.F := Finset.sdiff_subset_sdiff hIU (Finset.Subset.refl _)
        obtain ⟨hF'_sub, hC_sub, hI₂_cov, hF'_card, hC_shrink, hsand_rec⟩ :=
          containerStep_spec j (U \ st.F) H₂ p (2 * K / α) (I \ st.F)
            hN₀ hp hp1 hK₂_pos hH₂_valid hH₂_sp hI₂_sub hH₂_indep
        set res := containerStep j (U \ st.F) H₂ p (2 * K / α) (I \ st.F)
        have hstep_eq : containerStep (j + 1) U H p K I = (st.F ∪ res.1, res.2) := by
          unfold containerStep
          rw [if_neg hsmall]
          exact if_pos hcase1
        rw [hstep_eq]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact Finset.union_subset hF_I (hF'_sub.trans Finset.sdiff_subset)
        · intro x hx
          have hx' := hC_sub hx
          rw [Finset.mem_sdiff, Finset.mem_sdiff] at hx'
          rw [Finset.mem_sdiff, Finset.mem_union]
          exact ⟨hx'.1.1, fun h => h.elim hx'.1.2 hx'.2⟩
        · intro x hxI
          by_cases hxF : x ∈ st.F
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxF)
          · rcases Finset.mem_union.mp (hI₂_cov (Finset.mem_sdiff.mpr ⟨hxI, hxF⟩)) with hxC | hxF'
            · exact Finset.mem_union_left _ hxC
            · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxF')
        · have hF'_s : res.1.card ≤ (j + 1) * s := hF'_card
          calc (st.F ∪ res.1).card
              ≤ st.F.card + res.1.card := Finset.card_union_le _ _
            _ ≤ s + (j + 1) * s := by omega
            _ = (j + 2) * s := by ring
        · have hdel_le : shrinkDelta (j + 1) K ≤ shrinkDelta j (2 * K / α) := min_le_right _ _
          have h1 : shrinkDelta (j + 1) K * (N₀ : ℚ) ≤ shrinkDelta j (2 * K / α) * (N₀ : ℚ) :=
            mul_le_mul_of_nonneg_right hdel_le (by positivity)
          have hUF_le : ((U \ st.F).card : ℚ) ≤ (U.card : ℚ) := by
            exact_mod_cast Finset.card_le_card Finset.sdiff_subset
          linarith
        · intro F_hat hFC_Fhat hFhat_I
          have hF_Fhat : st.F ⊆ F_hat := Finset.subset_union_left.trans hFC_Fhat
          have hnot_small_hat : ¬(F_hat.card < s) := by
            have := Finset.card_le_card hF_Fhat; omega
          have hst_hat : runGreedyRounds H (j + 2) U p K F_hat s initGreedyState = st :=
            hsand_rounds F_hat hF_Fhat hFhat_I
          have hres1_Fhat : res.1 ⊆ F_hat \ st.F := by
            intro x hx
            have hx_notF : x ∉ st.F := (Finset.mem_sdiff.mp (hF'_sub hx)).2
            exact Finset.mem_sdiff.mpr ⟨hFC_Fhat (Finset.mem_union_right _ hx), hx_notF⟩
          have hFhat_sdiff_I : F_hat \ st.F ⊆ I \ st.F :=
            Finset.sdiff_subset_sdiff hFhat_I (Finset.Subset.refl _)
          have hrec_hat : containerStep j (U \ st.F) H₂ p (2 * K / α) (F_hat \ st.F) = res :=
            hsand_rec (F_hat \ st.F) hres1_Fhat hFhat_sdiff_I
          conv_lhs => unfold containerStep
          rw [if_neg hnot_small_hat]
          change (let st_h := runGreedyRounds H (j + 2) U p K F_hat s initGreedyState;
            if α * p * H.totalWeight ≤ H.weightOf st_h.Hp then
              (st_h.F ∪ (containerStep j (U \ st_h.F) (projectHypergraph H st_h.Hp st_h.F)
                p (2 * K / α) (F_hat \ st_h.F)).1,
               (containerStep j (U \ st_h.F) (projectHypergraph H st_h.Hp st_h.F)
                p (2 * K / α) (F_hat \ st_h.F)).2)
            else _) = _
          rw [hst_hat, if_pos hcase1, hrec_hat]
      · have hlt_Hp : H.weightOf st.Hp < α * p * H.totalWeight := lt_of_not_ge hcase1
        set C := (U \ st.F).filter (fun v => H.degWeight (st.R H) v ≤ α * H.totalWeight / (N₀ : ℚ))
        have hstep_eq : containerStep (j + 1) U H p K I = (st.F, C) := by
          unfold containerStep
          rw [if_neg hsmall]
          exact if_neg hcase1
        rw [hstep_eq]
        refine ⟨hF_I, Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
        · intro u huI
          by_cases huF : u ∈ st.F
          · exact Finset.mem_union_right _ huF
          · apply Finset.mem_union_left
            refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hIU huI, huF⟩, ?_⟩
            have hu_sdiff : u ∈ I \ st.F := Finset.mem_sdiff.mpr ⟨huI, huF⟩
            have hdeg := hdeg_max u hu_sdiff
            have hinit0 : H.weightOf (initGreedyState : GreedyState N₀).Hp = 0 := by
              simp [initGreedyState, WeightedHypergraph.weightOf]
            rw [hinit0, zero_add] at hdeg
            have hs_ge_Np : (N₀ : ℚ) * p ≤ (s : ℚ) := Nat.le_ceil _
            have hdeg_nonneg : 0 ≤ H.degWeight (st.R H) u :=
              Finset.sum_nonneg (fun e _ => hH.wt_nonneg e)
            have hNp_deg : (N₀ : ℚ) * p * H.degWeight (st.R H) u < α * p * H.totalWeight := by
              calc (N₀ : ℚ) * p * H.degWeight (st.R H) u
                  ≤ (s : ℚ) * H.degWeight (st.R H) u :=
                    mul_le_mul_of_nonneg_right hs_ge_Np hdeg_nonneg
                _ ≤ H.weightOf st.Hp := hdeg
                _ < α * p * H.totalWeight := hlt_Hp
            have hN₀_q : (0 : ℚ) < (N₀ : ℚ) := by exact_mod_cast hN₀
            have hcancel_p : (N₀ : ℚ) * H.degWeight (st.R H) u < α * H.totalWeight := by
              have h1 : p * ((N₀ : ℚ) * H.degWeight (st.R H) u) < p * (α * H.totalWeight) := by linarith
              exact lt_of_mul_lt_mul_left h1 (le_of_lt hp)
            rw [le_div_iff₀ hN₀_q]
            linarith [mul_comm (N₀ : ℚ) (H.degWeight (st.R H) u)]
        · calc st.F.card = 1 * s := by rw [one_mul, hF_card_eq]
            _ ≤ (j + 2) * s := Nat.mul_le_mul_right s (by omega)
        · exact case2_shrink_bound hN₀ hp hp1 hK hH hsp hinv hlt_Hp
        · intro F_hat hF_Fhat hFhat_I
          have hF_sub' : st.F ⊆ F_hat := hF_Fhat
          have hnot_small_hat : ¬(F_hat.card < s) := by
            have := Finset.card_le_card hF_sub'; omega
          have hst_hat : runGreedyRounds H (j + 2) U p K F_hat s initGreedyState = st :=
            hsand_rounds F_hat hF_sub' hFhat_I
          conv_lhs => unfold containerStep
          rw [if_neg hnot_small_hat]
          change (let st_h := runGreedyRounds H (j + 2) U p K F_hat s initGreedyState;
            if α * p * H.totalWeight ≤ H.weightOf st_h.Hp then _
            else (st_h.F, (U \ st_h.F).filter (fun v =>
              H.degWeight (st_h.R H) v ≤ α * H.totalWeight / (N₀ : ℚ)))) = _
          rw [hst_hat, if_neg hcase1]

/-! ## Outer Iterated Container Theorem (Nenadov–Pham Theorem 1.1 for 3-Uniform Hypergraphs) -/

/-- Restrict a 3-uniform unweighted hypergraph `H₃ : Finset (Finset (Fin N₀))` to edges inside `U`
with unit weight `1`. -/
def uniformInducedHypergraph (H₃ : Finset (Finset (Fin N₀))) (U : Finset (Fin N₀)) :
    WeightedHypergraph N₀ where
  edges := H₃.filter (fun e => e ⊆ U)
  wt := fun _ => 1

lemma uniformInducedHypergraph_totalWeight (H₃ : Finset (Finset (Fin N₀))) (U : Finset (Fin N₀)) :
    (uniformInducedHypergraph H₃ U).totalWeight = ((H₃.filter (fun e => e ⊆ U)).card : ℚ) := by
  simp [uniformInducedHypergraph, WeightedHypergraph.totalWeight, WeightedHypergraph.weightOf]

/-- Outer container loop running up to `t` iterations while `|(H₃)[U]| ≥ ε * |H₃|`. -/
noncomputable def buildContainer3 (H₃ : Finset (Finset (Fin N₀))) (p K ε : ℚ) :
    (t : ℕ) → (U : Finset (Fin N₀)) → (S : Finset (Fin N₀)) →
    Finset (Fin N₀) × Finset (Fin N₀)
  | 0, U, _S => (∅, U)
  | t + 1, U, S =>
    if ((H₃.filter (fun e => e ⊆ U)).card : ℚ) < ε * (H₃.card : ℚ) then
      (∅, U)
    else
      let H_U := uniformInducedHypergraph H₃ U
      let FC₁ := containerStep 2 U H_U p (K / ε) (S ∩ U)
      let FC₂ := buildContainer3 H₃ p K ε t FC₁.2 (S ∩ FC₁.2)
      (FC₁.1 ∪ FC₂.1, FC₂.2)

lemma uniformInduced_valid_spread {H₃ : Finset (Finset (Fin N₀))} {U : Finset (Fin N₀)}
    {p K ε : ℚ}
    (hH₃_card : ∀ e ∈ H₃, 1 ≤ e.card ∧ e.card ≤ 3)
    (hH₃_pos : 0 < H₃.card)
    (hsp₀ : (uniformInducedHypergraph H₃ (Finset.univ : Finset (Fin N₀))).IsSpread p K)
    (_hp : 0 < p) (_hK : 0 < K) (hε : 0 < ε) (_hN₀ : 0 < N₀)
    (hdense : ε * (H₃.card : ℚ) ≤ ((H₃.filter (fun e => e ⊆ U)).card : ℚ)) :
    let H_U := uniformInducedHypergraph H₃ U
    H_U.IsValidOn 3 U ∧ H_U.IsSpread p (K / ε) := by
  set H_U := uniformInducedHypergraph H₃ U
  have htot_eq : H_U.totalWeight = ((H₃.filter (fun e => e ⊆ U)).card : ℚ) :=
    uniformInducedHypergraph_totalWeight H₃ U
  have hM_pos : (0 : ℚ) < (H₃.card : ℚ) := by exact_mod_cast hH₃_pos
  have htot_pos : 0 < H_U.totalWeight := by
    rw [htot_eq]
    have : 0 < ε * (H₃.card : ℚ) := by positivity
    linarith
  refine ⟨?_, ?_⟩
  · refine
      { sub_domain := fun e he => (Finset.mem_filter.mp he).2
        nonempty_edge := fun e he => (hH₃_card e (Finset.mem_filter.mp he).1).1
        card_le := fun e he => (hH₃_card e (Finset.mem_filter.mp he).1).2
        wt_pos := fun _ _ => by norm_num [H_U, uniformInducedHypergraph]
        wt_nonneg := fun _ => by norm_num [H_U, uniformInducedHypergraph]
        total_pos := htot_pos }
  · intro X hXcard
    let H_all := uniformInducedHypergraph H₃ (Finset.univ : Finset (Fin N₀))
    have hsub_edges : H_U.edges.filter (fun e => X ⊆ e) ⊆ H_all.edges.filter (fun e => X ⊆ e) := by
      intro e he
      rcases Finset.mem_filter.mp he with ⟨heU, hXe⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heU).1,
        Finset.subset_univ e⟩, hXe⟩
    have hcodeg_le : H_U.codegWeight H_U.edges X ≤ H_all.codegWeight H_all.edges X := by
      unfold WeightedHypergraph.codegWeight
      have h1 : H_U.wt = H_all.wt := rfl
      rw [h1]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub_edges (fun _ _ _ => by
        simp [H_all, uniformInducedHypergraph])
    have hall_tot : H_all.totalWeight = (H₃.card : ℚ) := by
      rw [uniformInducedHypergraph_totalWeight]
      have hfilt : H₃.filter (fun e => e ⊆ (Finset.univ : Finset (Fin N₀))) = H₃ :=
        Finset.filter_true_of_mem (fun e _ => Finset.subset_univ e)
      rw [hfilt]
    have hspX := hsp₀ X hXcard
    rw [hall_tot] at hspX
    have hM_le : (H₃.card : ℚ) ≤ H_U.totalWeight / ε := by
      rw [htot_eq, le_div_iff₀ hε]
      linarith
    have hmul_nn : 0 ≤ K * p ^ (X.card - 1) / (N₀ : ℚ) := by positivity
    calc H_U.codegWeight H_U.edges X
        ≤ H_all.codegWeight H_all.edges X := hcodeg_le
      _ ≤ (H₃.card : ℚ) * K * p ^ (X.card - 1) / (N₀ : ℚ) := hspX
      _ = (H₃.card : ℚ) * (K * p ^ (X.card - 1) / (N₀ : ℚ)) := by ring
      _ ≤ (H_U.totalWeight / ε) * (K * p ^ (X.card - 1) / (N₀ : ℚ)) :=
          mul_le_mul_of_nonneg_right hM_le hmul_nn
      _ = H_U.totalWeight * (K / ε) * p ^ (X.card - 1) / (N₀ : ℚ) := by ring

/-- Specification of `buildContainer3` by induction on fuel `t`:
every active iteration shrinks `U.card` by at least `shrinkDelta 2 (K / ε) * N₀`, so once
`t * shrinkDelta 2 (K / ε) > 1`, the process MUST halt with `< ε * H₃.card` edges in `C`,
AND satisfies exact idempotence `(buildContainer3 ... F_tot).2 = C`! -/
theorem buildContainer3_spec {H₃ : Finset (Finset (Fin N₀))} {p K ε : ℚ}
    (hN₀ : 0 < N₀) (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 < K) (hε : 0 < ε)
    (hH₃_card : ∀ e ∈ H₃, 1 ≤ e.card ∧ e.card ≤ 3)
    (hH₃_pos : 0 < H₃.card)
    (hsp₀ : (uniformInducedHypergraph H₃ (Finset.univ : Finset (Fin N₀))).IsSpread p K) :
    ∀ (t : ℕ) (U I : Finset (Fin N₀)),
      (∀ e ∈ H₃, ¬(e ⊆ I)) →
      let FC := buildContainer3 H₃ p K ε t U I
      FC.1 ⊆ I ∩ U ∧
      FC.2 ⊆ U \ FC.1 ∧
      I ∩ U ⊆ FC.2 ∪ FC.1 ∧
      FC.1.card ≤ 3 * t * ⌈(N₀ : ℚ) * p⌉₊ ∧
      (((H₃.filter (fun e => e ⊆ FC.2)).card : ℚ) < ε * (H₃.card : ℚ) ∨
        (FC.2.card : ℚ) + (t : ℚ) * (shrinkDelta 2 (K / ε) * (N₀ : ℚ)) ≤ (U.card : ℚ)) ∧
      (∀ F_hat : Finset (Fin N₀), FC.1 ⊆ F_hat → F_hat ⊆ I →
        buildContainer3 H₃ p K ε t U F_hat = FC)
  | 0, U, _I, _hIndep => by
    dsimp only [buildContainer3]
    refine ⟨Finset.empty_subset _, ?_, ?_, Nat.zero_le _, Or.inr (by simp), fun _ _ _ => rfl⟩
    · simp
    · intro x hx
      exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).2
  | t + 1, U, I, hIndep => by
    by_cases hsparse : ((H₃.filter (fun e => e ⊆ U)).card : ℚ) < ε * (H₃.card : ℚ)
    · have heq : buildContainer3 H₃ p K ε (t + 1) U I = (∅, U) := by
        unfold buildContainer3
        exact if_pos hsparse
      rw [heq]
      refine ⟨Finset.empty_subset _, ?_, ?_, Nat.zero_le _, Or.inl hsparse, ?_⟩
      · simp
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).2
      · intro F_hat _ _
        unfold buildContainer3
        exact if_pos hsparse
    · have hdense : ε * (H₃.card : ℚ) ≤ ((H₃.filter (fun e => e ⊆ U)).card : ℚ) :=
        le_of_not_gt hsparse
      obtain ⟨hHU_valid, hHU_sp⟩ :=
        uniformInduced_valid_spread hH₃_card hH₃_pos hsp₀ hp hK hε hN₀ hdense
      set H_U := uniformInducedHypergraph H₃ U
      have hKe_pos : 0 < K / ε := by positivity
      have hIU_indep : H_U.IsIndep (I ∩ U) := by
        intro e he hsub
        exact hIndep e (Finset.mem_filter.mp he).1 (hsub.trans Finset.inter_subset_left)
      obtain ⟨hF₁_sub, hC₁_sub, hIU_cov, hF₁_card, hC₁_shrink, hsand₁⟩ :=
        containerStep_spec 2 U H_U p (K / ε) (I ∩ U)
          hN₀ hp hp1 hKe_pos hHU_valid hHU_sp Finset.inter_subset_right hIU_indep
      set FC₁ := containerStep 2 U H_U p (K / ε) (I ∩ U)
      have hIndep_IC₁ : ∀ e ∈ H₃, ¬(e ⊆ I ∩ FC₁.2) := by
        intro e he hsub
        exact hIndep e he (hsub.trans Finset.inter_subset_left)
      obtain ⟨hF₂_sub, hC₂_sub, hIC₁_cov, hF₂_card, hC₂_or, hsand₂⟩ :=
        buildContainer3_spec hN₀ hp hp1 hK hε hH₃_card hH₃_pos hsp₀ t FC₁.2 (I ∩ FC₁.2) hIndep_IC₁
      set FC₂ := buildContainer3 H₃ p K ε t FC₁.2 (I ∩ FC₁.2)
      have hstep_eq : buildContainer3 H₃ p K ε (t + 1) U I = (FC₁.1 ∪ FC₂.1, FC₂.2) := by
        unfold buildContainer3
        exact if_neg hsparse
      rw [hstep_eq]
      have hFC₁_2_U : FC₁.2 ⊆ U := hC₁_sub.trans Finset.sdiff_subset
      have hF₂_IU : FC₂.1 ⊆ I ∩ U := by
        intro x hx
        have hx' := hF₂_sub hx
        rw [Finset.mem_inter, Finset.mem_inter] at hx'
        exact Finset.mem_inter.mpr ⟨hx'.1.1, hFC₁_2_U hx'.2⟩
      refine ⟨Finset.union_subset hF₁_sub hF₂_IU, ?_, ?_, ?_, ?_, ?_⟩
      · -- `FC₂.2 ⊆ U \ (FC₁.1 ∪ FC₂.1)`
        intro x hx
        have hx₂ := hC₂_sub hx
        rw [Finset.mem_sdiff] at hx₂
        have hx₁ := hC₁_sub hx₂.1
        rw [Finset.mem_sdiff] at hx₁
        rw [Finset.mem_sdiff, Finset.mem_union]
        exact ⟨hx₁.1, fun h => h.elim hx₁.2 hx₂.2⟩
      · -- `I ∩ U ⊆ FC₂.2 ∪ (FC₁.1 ∪ FC₂.1)`
        intro x hxIU
        rcases Finset.mem_union.mp (hIU_cov hxIU) with hxC₁ | hxF₁
        · have hxI : x ∈ I := (Finset.mem_inter.mp hxIU).1
          have hxIC₁ : x ∈ (I ∩ FC₁.2) ∩ FC₁.2 :=
            Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxI, hxC₁⟩, hxC₁⟩
          rcases Finset.mem_union.mp (hIC₁_cov hxIC₁) with hxC₂ | hxF₂
          · exact Finset.mem_union_left _ hxC₂
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxF₂)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxF₁)
      · -- `(FC₁.1 ∪ FC₂.1).card ≤ 3 * (t + 1) * s`
        calc (FC₁.1 ∪ FC₂.1).card
            ≤ FC₁.1.card + FC₂.1.card := Finset.card_union_le _ _
          _ ≤ 3 * ⌈(N₀ : ℚ) * p⌉₊ + 3 * t * ⌈(N₀ : ℚ) * p⌉₊ := add_le_add hF₁_card hF₂_card
          _ = 3 * (t + 1) * ⌈(N₀ : ℚ) * p⌉₊ := by ring
      · -- Either `< ε * |H₃|` or cumulative shrinkage by `(t + 1) * shrinkDelta`!
        rcases hC₂_or with hlt | hshr₂
        · exact Or.inl hlt
        · right
          push_cast
          linarith
      · -- Sandwich invariance for `buildContainer3`!
        intro F_hat hFC_Fhat hFhat_I
        have hF₁_FhatU : FC₁.1 ⊆ F_hat ∩ U :=
          Finset.subset_inter (Finset.subset_union_left.trans hFC_Fhat)
            (hF₁_sub.trans Finset.inter_subset_right)
        have hFhatU_IU : F_hat ∩ U ⊆ I ∩ U :=
          Finset.inter_subset_inter_right hFhat_I
        have h1_eq : containerStep 2 U H_U p (K / ε) (F_hat ∩ U) = FC₁ :=
          hsand₁ (F_hat ∩ U) hF₁_FhatU hFhatU_IU
        have hF₂_FhatC₁ : FC₂.1 ⊆ F_hat ∩ FC₁.2 :=
          Finset.subset_inter (Finset.subset_union_right.trans hFC_Fhat)
            (hF₂_sub.trans Finset.inter_subset_right)
        have hFhatC₁_IC₁ : F_hat ∩ FC₁.2 ⊆ I ∩ FC₁.2 :=
          Finset.inter_subset_inter_right hFhat_I
        have h2_eq : buildContainer3 H₃ p K ε t FC₁.2 (F_hat ∩ FC₁.2) = FC₂ :=
          hsand₂ (F_hat ∩ FC₁.2) hF₂_FhatC₁ hFhatC₁_IC₁
        conv_lhs => unfold buildContainer3
        rw [if_neg hsparse]
        dsimp only
        rw [h1_eq, h2_eq]

/-- **Theorem 1.1 of Nenadov–Pham (Specialized to 3-Uniform Hypergraphs with Canonical Container Map)**:
Irreducible canonical container map so downstream proofs never unfold the internal greedy recursion! -/
@[irreducible] noncomputable def canonicalContainer (H₃ : Finset (Finset (Fin N₀))) (p K ε : ℚ)
    (F : Finset (Fin N₀)) : Finset (Fin N₀) :=
  let t_max : ℕ := ⌈1 / shrinkDelta 2 (K / ε)⌉₊ + 1
  (buildContainer3 H₃ p K ε t_max Finset.univ F).2

theorem exists_fingerprint_for_indep {H₃ : Finset (Finset (Fin N₀))} {p K ε : ℚ}
    (hN₀ : 0 < N₀) (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 < K) (hε : 0 < ε)
    (hH₃_card : ∀ e ∈ H₃, 1 ≤ e.card ∧ e.card ≤ 3)
    (hH₃_pos : 0 < H₃.card)
    (hsp₀ : (uniformInducedHypergraph H₃ (Finset.univ : Finset (Fin N₀))).IsSpread p K)
    (I : Finset (Fin N₀)) (hIndep : ∀ e ∈ H₃, ¬(e ⊆ I)) :
    let t_max : ℕ := ⌈1 / shrinkDelta 2 (K / ε)⌉₊ + 1
    ∃ F : Finset (Fin N₀),
      F ⊆ I ∧
      F.card ≤ 3 * t_max * ⌈(N₀ : ℚ) * p⌉₊ ∧
      I ⊆ canonicalContainer H₃ p K ε F ∪ F ∧
      ((H₃.filter (fun e => e ⊆ canonicalContainer H₃ p K ε F)).card : ℚ) < ε * (H₃.card : ℚ) := by
  let δ := shrinkDelta 2 (K / ε)
  have hδ_pos : 0 < δ := shrinkDelta_pos 2 (by positivity)
  let t_max : ℕ := ⌈1 / δ⌉₊ + 1
  obtain ⟨hF_sub, _, hI_cov, hF_card, h_or, hsand⟩ :=
    buildContainer3_spec hN₀ hp hp1 hK hε hH₃_card hH₃_pos hsp₀ t_max Finset.univ I hIndep
  set FC := buildContainer3 H₃ p K ε t_max Finset.univ I
  have hF_I : FC.1 ⊆ I := by simpa using hF_sub
  have hcanon_eq : canonicalContainer H₃ p K ε FC.1 = FC.2 := by
    unfold canonicalContainer
    exact congrArg Prod.snd (hsand FC.1 (Finset.Subset.refl _) hF_I)
  refine ⟨FC.1, hF_I, hF_card, ?_, ?_⟩
  · rw [hcanon_eq]
    intro x hxI
    exact hI_cov (Finset.mem_inter.mpr ⟨hxI, Finset.mem_univ x⟩)
  · rw [hcanon_eq]
    rcases h_or with hlt | hshr
    · exact hlt
    · -- Impossible! `(t_max : ℚ) * δ > 1`, so `t_max * (δ * N₀) > N₀ = univ.card`!
      exfalso
      have ht_gt : 1 / δ < (t_max : ℚ) := by
        have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℚ) := Nat.le_ceil _
        dsimp only [t_max]
        push_cast
        linarith
      have htδ_gt : 1 < (t_max : ℚ) * δ := by
        rwa [div_lt_iff₀ hδ_pos] at ht_gt
      have hN₀_q : (0 : ℚ) < (N₀ : ℚ) := by exact_mod_cast hN₀
      have hprod_gt : (N₀ : ℚ) < (t_max : ℚ) * (δ * (N₀ : ℚ)) := by
        calc (N₀ : ℚ) = 1 * (N₀ : ℚ) := (one_mul _).symm
          _ < ((t_max : ℚ) * δ) * (N₀ : ℚ) := mul_lt_mul_of_pos_right htδ_gt hN₀_q
          _ = (t_max : ℚ) * (δ * (N₀ : ℚ)) := by ring
      have huniv_card : ((Finset.univ : Finset (Fin N₀)).card : ℚ) = (N₀ : ℚ) := by simp
      have hC_nn : (0 : ℚ) ≤ (FC.2.card : ℚ) := by positivity
      linarith

end GreedyProcess

end Erdos638.Container
