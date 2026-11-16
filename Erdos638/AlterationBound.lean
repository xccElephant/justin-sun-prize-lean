import Erdos638.Defs
import Erdos638.Container
import Erdos638.GridCounting
import Erdos638.SparseRamsey

/-!
# Finite Grid Probabilistic Union Bound & Core Avoidance Theorem

Combining `Erdos638.Container`, `Erdos638.GridCounting`, and `Erdos638.SparseRamsey`, we prove:

1. **`exists_locally_sparse_triangle_ramsey`**:
   For every `r ≥ 1` and `B ≥ 4`, there exists a finite simple graph `W : FiniteGraph` such that:
   - `ForcesMonoTriangle W.graph (Fin r)` (`W → (K₃)²_r`), and
   - `∀ S : Finset (Fin W.verts), 4 ≤ S.card → S.card ≤ B → edgesInside W.graph S ≤ 2 * S.card - 3`.

2. **`exists_ramsey_avoiding_family`**:
   For every `r ≥ 1` and every finite family `ℱ : Finset FiniteGraph` of finite 2-Ramsey graphs
   (`∀ M ∈ ℱ, ForcesMonoTriangle M.graph (Fin 2)`), there exists `W : FiniteGraph` with
   `ForcesMonoTriangle W.graph (Fin r)` such that `∀ M ∈ ℱ, ¬EmbedsInto M W`!
-/

namespace Erdos638

open scoped Classical BigOperators
open Erdos638.Container Erdos638.GridCounting

/-! ## Helper Lemmas Connecting Container Expansion & Markov Obstruction Bound -/

/-- Adding a set `F` of size `|F| ≤ L` to a container `C₀ ⊆ Fin (n.choose 2)` creates at most
`L * n` additional triangles in `triangleHypergraph n`!
Why? Every new triangle `e ∈ triangleHypergraph n` with `e ⊆ C₀ ∪ F` and `¬(e ⊆ C₀)` must
contain some element `i ∈ F` (`¬Disjoint e F`); and by the `|X| = 1` bound in `SparseRamsey`,
each `i ∈ F` lies in at most `n` triangles of `K_n` (in fact `n - 2`)! -/
lemma triangleHypergraph_union_add_le {m : ℕ} (hm : 1 ≤ m)
    (C₀ F : Finset (Fin ((m ^ 2 + 2).choose 2))) :
    let n := m ^ 2 + 2
    (((triangleHypergraph n).filter (fun e => e ⊆ C₀ ∪ F)).card : ℚ) ≤
      (((triangleHypergraph n).filter (fun e => e ⊆ C₀)).card : ℚ) +
        (F.card : ℚ) * (m : ℚ) ^ 2 := by
  let n := m ^ 2 + 2
  have hsub : (triangleHypergraph n).filter (fun e => e ⊆ C₀ ∪ F) ⊆
      (triangleHypergraph n).filter (fun e => e ⊆ C₀) ∪
        F.biUnion (fun i => (triangleHypergraph n).filter (fun e => {i} ⊆ e)) := by
    intro e he
    rcases Finset.mem_filter.mp he with ⟨heH, heCF⟩
    by_cases heC₀ : e ⊆ C₀
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heH, heC₀⟩)
    · apply Finset.mem_union_right
      -- Since `e ⊆ C₀ ∪ F` and `¬(e ⊆ C₀)`, some `i ∈ e` belongs to `F`!
      have hex : ∃ i ∈ e, i ∈ F := by
        by_contra! hall
        apply heC₀
        intro x hxe
        rcases Finset.mem_union.mp (heCF hxe) with hxC | hxF
        · exact hxC
        · exfalso; exact hall x hxe hxF
      obtain ⟨i, hie, hiF⟩ := hex
      exact Finset.mem_biUnion.mpr ⟨i, hiF,
        Finset.mem_filter.mpr ⟨heH, Finset.singleton_subset_iff.mpr hie⟩⟩
  -- For each `i`, `(triangleHypergraph n).filter ({i} ⊆ ·)` has card `≤ m ^ 2` by `triangleHypergraph_isSpread`!
  have hdeg_m2 : ∀ i : Fin (n.choose 2),
      (((triangleHypergraph n).filter (fun e => {i} ⊆ e)).card : ℚ) ≤ (m : ℚ) ^ 2 := by
    intro i
    have hsp := triangleHypergraph_isSpread m hm {i} (by simp)
    let H_all := uniformInducedHypergraph (triangleHypergraph n) (Finset.univ : Finset (Fin (n.choose 2)))
    have hcodeg : H_all.codegWeight H_all.edges {i} =
        (((triangleHypergraph n).filter (fun e => {i} ⊆ e)).card : ℚ) := by
      unfold WeightedHypergraph.codegWeight
      have hfilt : H_all.edges = triangleHypergraph n :=
        Finset.filter_true_of_mem (fun e _ => Finset.subset_univ e)
      have hwt : H_all.wt = fun _ => (1 : ℚ) := rfl
      rw [hfilt, hwt, Finset.sum_const, nsmul_eq_mul, mul_one]
    have htot : H_all.totalWeight = (n.choose 3 : ℚ) := by
      rw [uniformInducedHypergraph_totalWeight]
      have hfilt : (triangleHypergraph n).filter (fun e => e ⊆ Finset.univ) = triangleHypergraph n :=
        Finset.filter_true_of_mem (fun e _ => Finset.subset_univ e)
      rw [hfilt, card_triangleHypergraph]
    have habs : (n.choose 3 : ℚ) * 3 * (1 / (m : ℚ)) ^ (({i} : Finset _).card - 1) / (n.choose 2 : ℚ) =
        (m : ℚ) ^ 2 := by
      simp only [Finset.card_singleton, Nat.sub_self, pow_zero, mul_one]
      have hid : 3 * n.choose 3 = m ^ 2 * n.choose 2 := by
        have h := three_mul_choose_three n
        have hs : n - 2 = m ^ 2 := by dsimp [n]; omega
        rwa [hs] at h
      have hN_pos : 0 < n.choose 2 := Nat.choose_pos (by dsimp [n]; nlinarith)
      have hN_q : (n.choose 2 : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hN_pos
      rw [mul_comm (n.choose 3 : ℚ) 3, div_eq_iff hN_q]
      exact_mod_cast hid
    change H_all.codegWeight H_all.edges {i} ≤
      H_all.totalWeight * 3 * (1 / (m : ℚ)) ^ (({i} : Finset _).card - 1) / (n.choose 2 : ℚ) at hsp
    rw [hcodeg, htot, habs] at hsp
    exact hsp
  have hbi_card : (F.biUnion (fun i => (triangleHypergraph n).filter (fun e => {i} ⊆ e))).card ≤
      ∑ i ∈ F, ((triangleHypergraph n).filter (fun e => {i} ⊆ e)).card := by
    refine Finset.induction_on F (by simp) ?_
    intro x T hxT ih
    rw [Finset.biUnion_insert, Finset.sum_insert hxT]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)
  have hnat : ((triangleHypergraph n).filter (fun e => e ⊆ C₀ ∪ F)).card ≤
      ((triangleHypergraph n).filter (fun e => e ⊆ C₀)).card +
        ∑ i ∈ F, ((triangleHypergraph n).filter (fun e => {i} ⊆ e)).card := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left hbi_card _
  have hq : (((triangleHypergraph n).filter (fun e => e ⊆ C₀ ∪ F)).card : ℚ) ≤
      (((triangleHypergraph n).filter (fun e => e ⊆ C₀)).card : ℚ) +
        ∑ i ∈ F, (((triangleHypergraph n).filter (fun e => {i} ⊆ e)).card : ℚ) := by
    exact_mod_cast hnat
  have hsum_F : (∑ i ∈ F, (((triangleHypergraph n).filter (fun e => {i} ⊆ e)).card : ℚ)) ≤
      (F.card : ℚ) * (m : ℚ) ^ 2 := by
    calc _ ≤ ∑ _i ∈ F, (m : ℚ) ^ 2 := Finset.sum_le_sum (fun i _ => hdeg_m2 i)
      _ = (F.card : ℚ) * (m : ℚ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Markov's inequality on `Ω = Fin N₀ → Fin m` for `denseObstructions n B`:
At most `(1 / 2) * m ^ N₀` configurations `ω` have more than `2 * C_obs * m ^ 2` dense obstructions
`D ⊆ rawEdges A ω`, and when `ω` has `≤ 2 * C_obs * m ^ 2` such obstructions,
`(rawEdges A ω \ purgeDenseObstructions n B (rawEdges A ω)).card ≤ 2 * B * (2 * C_obs * m ^ 2)`! -/
lemma card_many_obstructions_lt_half {m B A : ℕ} (hm : 1 ≤ m) (hB : 4 ≤ B) (hAm : A ≤ m) :
    let n := m ^ 2 + 2
    let N₀ := n.choose 2
    let C_obs : ℕ := ⌈((B + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (B * B) *
      ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B⌉₊ + 1
    let badObs : Finset (Fin N₀ → Fin m) :=
      Finset.univ.filter (fun ω =>
        2 * C_obs * m ^ 2 < ((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card)
    (badObs.card : ℚ) < (1 / 2 : ℚ) * (m : ℚ) ^ N₀ ∧
    ∀ ω : Fin N₀ → Fin m, ω ∉ badObs →
      (rawEdges A ω \ purgeDenseObstructions n B (rawEdges A ω)).card ≤
        4 * B * C_obs * m ^ 2 := by
  let n := m ^ 2 + 2
  let N₀ := n.choose 2
  let C_obs : ℕ := ⌈((B + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (B * B) *
    ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B⌉₊ + 1
  let badObs : Finset (Fin N₀ → Fin m) :=
    Finset.univ.filter (fun ω =>
      2 * C_obs * m ^ 2 < ((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card)
  refine ⟨?_, ?_⟩
  · -- Double-count pairs `(ω, D)` with `D ∈ denseObstructions n B` and `D ⊆ rawEdges A ω`!
    have hsum_ω : (∑ ω : Fin N₀ → Fin m,
        (((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card : ℚ)) =
        ∑ D ∈ denseObstructions n B,
          (((Finset.univ : Finset (Fin N₀ → Fin m)).filter (fun ω => D ⊆ rawEdges A ω)).card : ℚ) := by
      calc (∑ ω : Fin N₀ → Fin m,
              (((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card : ℚ))
          = ∑ ω : Fin N₀ → Fin m, ∑ D ∈ denseObstructions n B,
              (if D ⊆ rawEdges A ω then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl (fun ω _ => ?_)
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ∑ D ∈ denseObstructions n B, ∑ ω : Fin N₀ → Fin m,
              (if D ⊆ rawEdges A ω then (1 : ℚ) else 0) := Finset.sum_comm
        _ = ∑ D ∈ denseObstructions n B,
              (((Finset.univ : Finset (Fin N₀ → Fin m)).filter (fun ω => D ⊆ rawEdges A ω)).card : ℚ) := by
              refine Finset.sum_congr rfl (fun D _ => ?_)
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    -- Each term on the RHS equals `m ^ N₀ * (A / m) ^ D.card` by `card_grid_cylinder` with `Z = ∅`!
    have hrhs_eq : (∑ D ∈ denseObstructions n B,
        (((Finset.univ : Finset (Fin N₀ → Fin m)).filter (fun ω => D ⊆ rawEdges A ω)).card : ℚ)) =
        (m : ℚ) ^ N₀ * ∑ D ∈ denseObstructions n B, ((A : ℚ) / (m : ℚ)) ^ D.card := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun D _ => ?_)
      have hcyl := card_grid_cylinder (N₀ := N₀) (m := m) hAm (by omega) D ∅
        (Finset.disjoint_empty_right D)
      simpa using hcyl
    have hexp_bd := sum_denseObstructions_prob (m := m) (B := B) (A := A) hm hB
    have hC_obs_gt : ((B + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (B * B) *
        ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B < (C_obs : ℚ) := by
      let X_rat : ℚ := ((B + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (B * B) *
        ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B
      have h1 : X_rat ≤ (⌈X_rat⌉₊ : ℚ) := Nat.le_ceil X_rat
      have hcast : (C_obs : ℚ) = (⌈X_rat⌉₊ : ℚ) + 1 := by
        change ((⌈X_rat⌉₊ + 1 : ℕ) : ℚ) = (⌈X_rat⌉₊ : ℚ) + 1
        exact Nat.cast_add_one _
      change X_rat < (C_obs : ℚ)
      linarith
    have hm2_pos : (0 : ℚ) < (m : ℚ) ^ 2 := by positivity
    have hmN_pos : (0 : ℚ) < (m : ℚ) ^ N₀ := by positivity
    have htot_lt : (∑ ω : Fin N₀ → Fin m,
        (((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card : ℚ)) <
        (m : ℚ) ^ N₀ * ((C_obs : ℚ) * (m : ℚ) ^ 2) := by
      rw [hsum_ω, hrhs_eq]
      apply mul_lt_mul_of_pos_left _ hmN_pos
      have hstrict : ((B + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (B * B) *
          ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B * (m : ℚ) ^ 2 <
          (C_obs : ℚ) * (m : ℚ) ^ 2 := mul_lt_mul_of_pos_right hC_obs_gt hm2_pos
      linarith
    -- On the other hand, summing over `ω ∈ badObs` gives `≥ badObs.card * (2 * C_obs * m ^ 2)`!
    have hbad_le_sum : (badObs.card : ℚ) * (2 * (C_obs : ℚ) * (m : ℚ) ^ 2) ≤
        ∑ ω : Fin N₀ → Fin m,
          (((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card : ℚ) := by
      calc (badObs.card : ℚ) * (2 * (C_obs : ℚ) * (m : ℚ) ^ 2)
          = ∑ _ω ∈ badObs, (2 * (C_obs : ℚ) * (m : ℚ) ^ 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ ω ∈ badObs,
              (((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card : ℚ) := by
              refine Finset.sum_le_sum (fun ω hω => ?_)
              have hlt_nat : 2 * C_obs * m ^ 2 ≤
                  ((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card :=
                le_of_lt (Finset.mem_filter.mp hω).2
              have hcast : ((2 * C_obs * m ^ 2 : ℕ) : ℚ) ≤
                  (((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card : ℚ) := by
                exact_mod_cast hlt_nat
              simpa [Nat.cast_mul, Nat.cast_pow] using hcast
        _ ≤ ∑ ω : Fin N₀ → Fin m,
              (((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card : ℚ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => by positivity)
    have hC_pos : (0 : ℚ) < (C_obs : ℚ) * (m : ℚ) ^ 2 := by
      have : 0 < C_obs := by dsimp [C_obs]; omega
      positivity
    have hcomb : (badObs.card : ℚ) * (2 * ((C_obs : ℚ) * (m : ℚ) ^ 2)) <
        ((1 / 2 : ℚ) * (m : ℚ) ^ N₀) * (2 * ((C_obs : ℚ) * (m : ℚ) ^ 2)) := by
      linarith
    exact lt_of_mul_lt_mul_right hcomb (by positivity)
  · -- When `ω ∉ badObs`, at most `2 * C_obs * m ^ 2` sets `D` are deleted, and each `D` has `≤ 2 * B` edges!
    intro ω hnotBad
    have hle_cnt : ((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card ≤
        2 * C_obs * m ^ 2 := by
      by_contra! hgt
      exact hnotBad (Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hgt⟩)
    have hsub_del : rawEdges A ω \ purgeDenseObstructions n B (rawEdges A ω) ⊆
        ((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).biUnion id := by
      intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxRaw, hxNotPurge⟩
      unfold purgeDenseObstructions at hxNotPurge
      by_contra hxNotBi
      exact hxNotPurge (Finset.mem_sdiff.mpr ⟨hxRaw, hxNotBi⟩)
    have hD_card_le : ∀ D ∈ denseObstructions n B, D.card ≤ 2 * B := by
      intro D hD
      unfold denseObstructions at hD
      rcases Finset.mem_biUnion.mp hD with ⟨S, hS, hD_pow⟩
      have hSB : S.card ≤ B := (Finset.mem_filter.mp hS).2.2
      have hDc : D.card = 2 * S.card - 2 := (Finset.mem_powersetCard.mp hD_pow).2
      omega
    have hbi_le : ∀ T : Finset (Finset (Fin N₀)),
        (T.biUnion id).card ≤ ∑ D ∈ T, D.card := by
      intro T
      refine Finset.induction_on T (by simp) ?_
      intro D₀ R hD₀R ih
      rw [Finset.biUnion_insert, Finset.sum_insert hD₀R]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)
    calc (rawEdges A ω \ purgeDenseObstructions n B (rawEdges A ω)).card
        ≤ (((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).biUnion id).card :=
          Finset.card_le_card hsub_del
      _ ≤ ∑ D ∈ (denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω), D.card := hbi_le _
      _ ≤ ∑ _D ∈ (denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω), (2 * B) :=
          Finset.sum_le_sum (fun D hD => hD_card_le D (Finset.mem_filter.mp hD).1)
      _ = ((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card * (2 * B) := by simp
      _ ≤ (2 * C_obs * m ^ 2) * (2 * B) := Nat.mul_le_mul_right _ hle_cnt
      _ = 4 * B * C_obs * m ^ 2 := by ring

/-! ## Container Union Bound & Main Sparse Triangle-Ramsey Theorem -/

/-- If `graphOfEdgeIndices n E` fails `ForcesMonoTriangle _ (Fin r)` (`r ≥ 1`), then `E` can be
partitioned into `r` pairwise disjoint subsets `I : Fin r → Finset (Fin (n.choose 2))` such that
`E = Finset.univ.biUnion I` and each `I c` is an independent set of `triangleHypergraph n`! -/
lemma partition_into_triangle_free_color_classes {r n : ℕ} (hr : 1 ≤ r)
    {E : Finset (Fin (n.choose 2))}
    (hnot : ¬ForcesMonoTriangle (graphOfEdgeIndices n E) (Fin r)) :
    ∃ I : Fin r → Finset (Fin (n.choose 2)),
      (∀ c₁ c₂, c₁ ≠ c₂ → Disjoint (I c₁) (I c₂)) ∧
      E = Finset.univ.biUnion I ∧
      (∀ c : Fin r, ∀ e ∈ triangleHypergraph n, ¬(e ⊆ I c)) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [forcesMonoTriangle_iff_sym2] at hnot
  have hex_col : ∃ col : Sym2 (Fin n) → Fin r, ¬HasMonoTriangle (graphOfEdgeIndices n E) col := by
    by_contra! hall
    exact hnot hall
  obtain ⟨col, hcol⟩ := hex_col
  -- Map each edge index `i : Fin (n.choose 2)` to its `Sym2 (Fin n)` unordered pair!
  let edgeSym2 : Fin (n.choose 2) → Sym2 (Fin n) := fun i =>
    let p := ((edgeIndexEquiv n) i).1
    have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp ((edgeIndexEquiv n) i).2).2
    s(Classical.choose (Finset.card_eq_two.mp hp2),
      Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp hp2)))
  have hedgeSym2_eq : ∀ (u v : Fin n) (huv : u ≠ v),
      edgeSym2 ((edgeIndexEquiv n).symm ⟨{u, v}, by
        rw [completeEdges, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, Finset.card_pair huv⟩⟩) = s(u, v) := by
    intro u v huv
    let idx := (edgeIndexEquiv n).symm ⟨{u, v}, by
      rw [completeEdges, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair huv⟩⟩
    have hp_uv : ((edgeIndexEquiv n) idx).1 = {u, v} := by simp [idx]
    let p := ((edgeIndexEquiv n) idx).1
    have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp ((edgeIndexEquiv n) idx).2).2
    let a := Classical.choose (Finset.card_eq_two.mp hp2)
    let h2 := Classical.choose_spec (Finset.card_eq_two.mp hp2)
    let b := Classical.choose h2
    let h3 := Classical.choose_spec h2
    change s(a, b) = s(u, v)
    rw [Sym2.eq_iff]
    have hset_eq : ({a, b} : Finset (Fin n)) = {u, v} := h3.2.symm.trans hp_uv
    have ha : a ∈ ({u, v} : Finset (Fin n)) := hset_eq ▸ by simp
    have hb : b ∈ ({u, v} : Finset (Fin n)) := hset_eq ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with hau | hav <;> rcases hb with hbu | hbv
    · exfalso; exact h3.1 (hau.trans hbu.symm)
    · exact Or.inl ⟨hau, hbv⟩
    · exact Or.inr ⟨hav, hbu⟩
    · exfalso; exact h3.1 (hav.trans hbv.symm)
  let I : Fin r → Finset (Fin (n.choose 2)) := fun c => E.filter (fun i => col (edgeSym2 i) = c)
  refine ⟨I, ?_, ?_, ?_⟩
  · intro c₁ c₂ hne
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    have h1 := (Finset.mem_filter.mp hi₁).2
    have h2 := (Finset.mem_filter.mp hi₂).2
    exact hne (h1.symm.trans h2)
  · ext i
    simp only [I, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun hi => ⟨col (edgeSym2 i), hi, rfl⟩, fun ⟨_, hi, _⟩ => hi⟩
  · intro c e he hsub
    unfold triangleHypergraph at he
    rcases Finset.mem_image.mp he with ⟨t, ht, rfl⟩
    have ht3 : t.card = 3 := (Finset.mem_powersetCard.mp ht).2
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht3
    have mem_idx : ∀ (u v : Fin n) (huv : u ≠ v),
        ({u, v} : Finset (Fin n)) ⊆ {x, y, z} →
        (edgeIndexEquiv n).symm ⟨{u, v}, by
          rw [completeEdges, Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, Finset.card_pair huv⟩⟩ ∈
          triangleEdgeIndices n {x, y, z} := by
      intro u v huv huv_sub
      unfold triangleEdgeIndices
      have hp_t : ({u, v} : Finset (Fin n)) ∈ ({x, y, z} : Finset (Fin n)).powersetCard 2 :=
        Finset.mem_powersetCard.mpr ⟨huv_sub, Finset.card_pair huv⟩
      exact Finset.mem_image.mpr ⟨⟨{u, v}, hp_t⟩, Finset.mem_attach _ _, rfl⟩
    have hxy_sub : ({x, y} : Finset (Fin n)) ⊆ {x, y, z} := by intro w hw; simp at hw ⊢; tauto
    have hyz_sub : ({y, z} : Finset (Fin n)) ⊆ {x, y, z} := by intro w hw; simp at hw ⊢; tauto
    have hxz_sub : ({x, z} : Finset (Fin n)) ⊆ {x, y, z} := by intro w hw; simp at hw ⊢; tauto
    have hxy_I := hsub (mem_idx x y hxy hxy_sub)
    have hyz_I := hsub (mem_idx y z hyz hyz_sub)
    have hxz_I := hsub (mem_idx x z hxz hxz_sub)
    rcases Finset.mem_filter.mp hxy_I with ⟨hxy_E, hxy_col⟩
    rcases Finset.mem_filter.mp hyz_I with ⟨hyz_E, hyz_col⟩
    rcases Finset.mem_filter.mp hxz_I with ⟨hxz_E, hxz_col⟩
    rw [hedgeSym2_eq x y hxy] at hxy_col
    rw [hedgeSym2_eq y z hyz] at hyz_col
    rw [hedgeSym2_eq x z hxz] at hxz_col
    apply hcol
    refine ⟨x, y, z,
      (graphOfEdgeIndices_adj_iff hxy).mpr hxy_E,
      (graphOfEdgeIndices_adj_iff hyz).mpr hyz_E,
      (graphOfEdgeIndices_adj_iff hxz).mpr hxz_E,
      hxy_col.trans hyz_col.symm,
      hyz_col.trans hxz_col.symm⟩

/-- Sum of `∏ c : Fin r, g (F c)` over all tuples `F : Fin r → α` (`F ∈ (Fin r → s)`) equals
`(∑ x ∈ s, g x) ^ r`! -/
private lemma sum_pi_pow_eq {α : Type*} [DecidableEq α] (r : ℕ) (s : Finset α) (g : α → ℚ) :
    (∑ F ∈ Fintype.piFinset (fun _ : Fin r => s), ∏ c : Fin r, g (F c)) =
      (∑ x ∈ s, g x) ^ r := by
  rw [← Finset.prod_univ_sum]
  simp

/-- General 2-level indicator covering bound (free of any specific `Finset` terms):
if every `x ∈ S` belongs to `C a b` for some `a ∈ A` and `b ∈ B a`, then
`(S.card : ℚ) ≤ ∑ a ∈ A, ∑ b ∈ B a, ((C a b).card : ℚ)`! -/
private lemma card_le_double_sum_of_witness {Ω α β : Type*} [Fintype Ω]
    (S : Finset Ω) (A : Finset α) (B : α → Finset β) (C : α → β → Finset Ω)
    (hwit : ∀ x ∈ S, ∃ a ∈ A, ∃ b ∈ B a, x ∈ C a b) :
    (S.card : ℚ) ≤ ∑ a ∈ A, ∑ b ∈ B a, ((C a b).card : ℚ) := by
  let indS : Ω → ℚ := fun x => if x ∈ S then 1 else 0
  let indC : α → β → Ω → ℚ := fun a b x => if x ∈ C a b then 1 else 0
  have hindC_nn : ∀ a b x, 0 ≤ indC a b x := by
    intro a b x; dsimp [indC]; split_ifs <;> norm_num
  have hpt : ∀ x : Ω, indS x ≤ ∑ a ∈ A, ∑ b ∈ B a, indC a b x := by
    intro x
    dsimp [indS]
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      obtain ⟨a₀, ha₀, b₀, hb₀, hx₀⟩ := hwit x hx
      have h1 : (1 : ℚ) = indC a₀ b₀ x := by dsimp [indC]; rw [if_pos hx₀]
      calc (1 : ℚ)
          = indC a₀ b₀ x := h1
        _ ≤ ∑ b ∈ B a₀, indC a₀ b x :=
            Finset.single_le_sum (fun b _ => hindC_nn a₀ b x) hb₀
        _ ≤ ∑ a ∈ A, ∑ b ∈ B a, indC a b x :=
            Finset.single_le_sum
              (fun a _ => Finset.sum_nonneg (fun b _ => hindC_nn a b x)) ha₀
    · rw [if_neg hx]
      exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hindC_nn a b x))
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Ω)) (fun x _ => hpt x)
  have hlhs : (∑ x : Ω, indS x) = (S.card : ℚ) := by
    dsimp [indS]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hfilt : (Finset.univ : Finset Ω).filter (· ∈ S) = S := by ext x; simp
    rw [hfilt]
  have hrhs : (∑ x : Ω, ∑ a ∈ A, ∑ b ∈ B a, indC a b x) =
      ∑ a ∈ A, ∑ b ∈ B a, ((C a b).card : ℚ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    dsimp [indC]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hfilt : (Finset.univ : Finset Ω).filter (· ∈ C a b) = C a b := by ext x; simp
    rw [hfilt]
  linarith

private lemma rat_prod_nonneg {ι : Type*} (s : Finset ι) (g : ι → ℚ)
    (hg : ∀ i ∈ s, 0 ≤ g i) : 0 ≤ ∏ i ∈ s, g i := by
  revert hg
  refine Finset.induction_on s (by simp) ?_
  intro x T hxT ih hg
  rw [Finset.prod_insert hxT]
  exact mul_nonneg (hg x (Finset.mem_insert_self x T))
    (ih (fun y hy => hg y (Finset.mem_insert_of_mem hy)))

private lemma nat_le_du_ceil_div (N₀ D_U : ℕ) (hDU : 1 ≤ D_U) :
    N₀ ≤ D_U * ⌈(N₀ : ℚ) / (D_U : ℚ)⌉₊ := by
  have hDU_q : (0 : ℚ) < (D_U : ℚ) := by exact_mod_cast (by omega : 0 < D_U)
  have h1 : (N₀ : ℚ) / (D_U : ℚ) ≤ (⌈(N₀ : ℚ) / (D_U : ℚ)⌉₊ : ℚ) := Nat.le_ceil _
  rw [div_le_iff₀ hDU_q] at h1
  have h2 : (N₀ : ℚ) ≤ ((D_U * ⌈(N₀ : ℚ) / (D_U : ℚ)⌉₊ : ℕ) : ℚ) := by
    rw [Nat.cast_mul]; linarith
  exact Nat.cast_le.mp h2

/-- Pure rational exponential-combination inequality (zero `Finset` terms in context!): -/
private lemma combine_prob_factors
    {r D_U N₀ U_min B_del L K_m A T : ℕ}
    (hr : 1 ≤ r) (hDU : 1 ≤ D_U) (hA : 1 ≤ A) (hKm : 1 ≤ K_m)
    (hN₀_le_DU : N₀ ≤ D_U * U_min)
    (hN₀_ge : (8 * A * K_m) ^ 4 ≤ 2 * N₀)
    (hL_le : L ≤ 3 * T * (8 * A * K_m) ^ 3)
    (hBdel_le : B_del ≤ (8 * A * K_m) ^ 3)
    (hA_ge : 128 * D_U * (3 * r * T * (8 * r * D_U) + 2) ≤ A) :
    let m := 8 * A * K_m
    let q : ℚ := (A : ℚ) / (m : ℚ)
    let lam_nat := 8 * r * D_U
    let lam : ℚ := (lam_nat : ℚ)
    (2 : ℚ) ^ B_del * lam ^ (r * L) *
      ((1 + q / lam) ^ (r * N₀) * (1 - q / 2) ^ U_min) ≤ 1 / 2 := by
  let m := 8 * A * K_m
  have hm1 : 1 ≤ m := by
    calc 1 ≤ 8 * 1 * 1 := by decide
      _ ≤ 8 * A * K_m := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hA) hKm
  let q : ℚ := (A : ℚ) / (m : ℚ)
  let lam_nat := 8 * r * D_U
  have hlam_ge1 : 1 ≤ lam_nat := by dsimp [lam_nat]; nlinarith
  let lam : ℚ := (lam_nat : ℚ)
  have hlam1 : (1 : ℚ) ≤ lam := by
    change ((1 : ℕ) : ℚ) ≤ (lam_nat : ℚ)
    exact Nat.cast_le.mpr hlam_ge1
  have hq_pos : 0 < q := by positivity
  have hq_le_eighth : q ≤ 1 / 8 := by
    dsimp [q]
    rw [div_le_iff₀ (by positivity : (0 : ℚ) < (m : ℚ))]
    have hm_eq : (m : ℚ) = 8 * (A : ℚ) * (K_m : ℚ) := by dsimp [m]; push_cast; ring
    have hK1 : (1 : ℚ) ≤ (K_m : ℚ) := by exact_mod_cast hKm
    have hA0 : (0 : ℚ) ≤ (A : ℚ) := by positivity
    nlinarith
  have hcomb_exp : (1 + q / lam) ^ (r * N₀) * (1 - q / 2) ^ U_min ≤ (1 - q / 4) ^ U_min := by
    have h1_qlam : (1 : ℚ) ≤ 1 + q / lam := by
      have : 0 ≤ q / lam := by positivity
      linarith
    have hpow_up : (1 + q / lam) ^ (r * N₀) ≤ ((1 + q / lam) ^ (r * D_U)) ^ U_min := by
      rw [← pow_mul]
      apply pow_le_pow_right₀ h1_qlam
      calc r * N₀ ≤ r * (D_U * U_min) := Nat.mul_le_mul_left r hN₀_le_DU
        _ = r * D_U * U_min := (Nat.mul_assoc r D_U U_min).symm
    have hlin : (1 + q / lam) ^ (r * D_U) ≤ 1 + q / 4 := by
      have hlam_eq : lam = 8 * (r : ℚ) * (D_U : ℚ) := by dsimp [lam, lam_nat]; push_cast; ring
      have hrDU_ne : (r : ℚ) * (D_U : ℚ) ≠ 0 := by positivity
      have h2kz : 2 * ((r * D_U : ℕ) : ℚ) * (q / lam) = q / 4 := by
        rw [hlam_eq]; push_cast; field_simp [hrDU_ne]; ring
      have hle1 : 2 * ((r * D_U : ℕ) : ℚ) * (q / lam) ≤ 1 := by rw [h2kz]; linarith
      have h := one_add_pow_le_linear (r * D_U) (by positivity) hle1
      rwa [h2kz] at h
    have hstep_base : (1 + q / lam) ^ (r * D_U) * (1 - q / 2) ≤ 1 - q / 4 := by
      have hmul : (1 + q / lam) ^ (r * D_U) * (1 - q / 2) ≤ (1 + q / 4) * (1 - q / 2) :=
        mul_le_mul_of_nonneg_right hlin (by linarith)
      have hsq : 0 ≤ q ^ 2 / 8 := by positivity
      have hid : (1 + q / 4) * (1 - q / 2) = 1 - q / 4 - q ^ 2 / 8 := by ring
      linarith
    have hbase_nn : 0 ≤ (1 + q / lam) ^ (r * D_U) * (1 - q / 2) :=
      mul_nonneg (by positivity) (by linarith)
    calc (1 + q / lam) ^ (r * N₀) * (1 - q / 2) ^ U_min
        ≤ ((1 + q / lam) ^ (r * D_U)) ^ U_min * (1 - q / 2) ^ U_min :=
          mul_le_mul_of_nonneg_right hpow_up (pow_nonneg (by linarith) _)
      _ = ((1 + q / lam) ^ (r * D_U) * (1 - q / 2)) ^ U_min := (mul_pow _ _ _).symm
      _ ≤ (1 - q / 4) ^ U_min := pow_le_pow_left₀ hbase_nn hstep_base U_min
  let E_pos : ℕ := (3 * r * T * lam_nat + 1) * m ^ 3
  have hpos_pow2 : (2 : ℚ) ^ B_del * lam ^ (r * L) ≤ (2 : ℚ) ^ E_pos := by
    have hlam_2 : lam ≤ (2 : ℚ) ^ lam_nat := by
      have hle_pow : ∀ k : ℕ, k ≤ 2 ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ j ih =>
          have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
          rw [pow_succ]; omega
      have hcast : (lam_nat : ℚ) ≤ ((2 ^ lam_nat : ℕ) : ℚ) := Nat.cast_le.mpr (hle_pow lam_nat)
      simpa [lam, Nat.cast_pow] using hcast
    have hlam_rL : lam ^ (r * L) ≤ (2 : ℚ) ^ (lam_nat * (r * L)) := by
      calc lam ^ (r * L) ≤ ((2 : ℚ) ^ lam_nat) ^ (r * L) :=
            pow_le_pow_left₀ (by positivity) hlam_2 _
        _ = (2 : ℚ) ^ (lam_nat * (r * L)) := (pow_mul _ _ _).symm
    have hexp_le : B_del + lam_nat * (r * L) ≤ E_pos := by
      have h1 : lam_nat * (r * L) ≤ lam_nat * (r * (3 * T * m ^ 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL_le)
      have hbdel : B_del ≤ m ^ 3 := hBdel_le
      dsimp [E_pos]
      nlinarith
    calc (2 : ℚ) ^ B_del * lam ^ (r * L)
        ≤ (2 : ℚ) ^ B_del * (2 : ℚ) ^ (lam_nat * (r * L)) :=
          mul_le_mul_of_nonneg_left hlam_rL (by positivity)
      _ = (2 : ℚ) ^ (B_del + lam_nat * (r * L)) := (pow_add _ _ _).symm
      _ ≤ (2 : ℚ) ^ E_pos := pow_le_pow_right₀ (by norm_num) hexp_le
  let b : ℕ := 64 * K_m
  have hb_block : (1 - q / 4) ^ b ≤ 1 / 2 := by
    apply one_sub_pow_block_le_half (by linarith) (by linarith)
    have h2eq : (b : ℚ) * (q / 4) = 2 := by
      dsimp [b, q, m]
      have hA_ne : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (by omega : 0 < A)
      have hKm_ne : (K_m : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (by omega : 0 < K_m)
      push_cast
      field_simp [hA_ne, hKm_ne]
      ring
    linarith
  let C_exp : ℕ := 3 * r * T * lam_nat + 2
  have hb_blocks_fit : b * (E_pos + 1) ≤ U_min := by
    have hE1_le : E_pos + 1 ≤ C_exp * m ^ 3 := by
      dsimp [E_pos, C_exp]
      have hm3_ge1 : 1 ≤ m ^ 3 := Nat.one_le_pow 3 m hm1
      nlinarith
    have h_m4 : 2 * D_U * (b * (E_pos + 1)) ≤ m ^ 4 := by
      have hAK_le : A * K_m ≤ 8 * A * K_m := by nlinarith
      calc 2 * D_U * (b * (E_pos + 1))
          ≤ 2 * D_U * (b * (C_exp * m ^ 3)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hE1_le)
        _ = (128 * D_U * C_exp) * K_m * m ^ 3 := by dsimp [b]; ring
        _ ≤ A * K_m * m ^ 3 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA_ge)
        _ ≤ (8 * A * K_m) * m ^ 3 :=
            Nat.mul_le_mul_right _ hAK_le
        _ = m ^ 4 := by dsimp [m]; ring
    have h_2DU : m ^ 4 ≤ 2 * D_U * U_min := by
      calc m ^ 4 ≤ 2 * N₀ := hN₀_ge
        _ ≤ 2 * (D_U * U_min) := Nat.mul_le_mul_left 2 hN₀_le_DU
        _ = 2 * D_U * U_min := by ring
    exact Nat.le_of_mul_le_mul_left (h_m4.trans h_2DU) (by omega)
  have hneg_pow2 : (1 - q / 4) ^ U_min ≤ (1 / 2 : ℚ) ^ (E_pos + 1) := by
    calc (1 - q / 4) ^ U_min
        ≤ (1 - q / 4) ^ (b * (E_pos + 1)) :=
          pow_le_pow_of_le_one (by linarith) (by linarith) hb_blocks_fit
      _ = ((1 - q / 4) ^ b) ^ (E_pos + 1) := pow_mul _ _ _
      _ ≤ (1 / 2 : ℚ) ^ (E_pos + 1) :=
          pow_le_pow_left₀ (pow_nonneg (by linarith) _) hb_block _
  have hnn_comb : 0 ≤ (1 + q / lam) ^ (r * N₀) * (1 - q / 2) ^ U_min :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  calc (2 : ℚ) ^ B_del * lam ^ (r * L) * ((1 + q / lam) ^ (r * N₀) * (1 - q / 2) ^ U_min)
      ≤ (2 : ℚ) ^ E_pos * (1 - q / 4) ^ U_min :=
        mul_le_mul hpos_pow2 hcomb_exp hnn_comb (by positivity)
    _ ≤ (2 : ℚ) ^ E_pos * (1 / 2 : ℚ) ^ (E_pos + 1) :=
        mul_le_mul_of_nonneg_left hneg_pow2 (by positivity)
    _ = 1 / 2 := by
        rw [pow_succ, ← mul_assoc, ← mul_pow]
        norm_num

/-- Elementary inequality `n ≤ 2 ^ n` for all `n : ℕ`. -/
private lemma le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    rw [pow_succ]
    omega


/-! ## Parameterized Container Union Bound Lemma -/

private lemma disjoint_biUnion_card_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (F : α → Finset β)
    (hdisj : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (F a) (F b)) :
    (s.biUnion F).card = ∑ a ∈ s, (F a).card := by
  revert hdisj
  refine Finset.induction_on s (by simp) ?_
  intro x T hxT ih hdisj
  have hT_disj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint (F a) (F b) :=
    fun a ha b hb hab => hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
  have hx_disj : Disjoint (F x) (T.biUnion F) := by
    rw [Finset.disjoint_biUnion_right]
    intro y hyT
    exact hdisj x (Finset.mem_insert_self x T) y (Finset.mem_insert_of_mem hyT)
      (fun h => hxT (h ▸ hyT))
  rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hx_disj, Finset.sum_insert hxT,
      ih hT_disj]

/-- Parameterized core union-bound lemma on `Ω = Fin N₀ → Fin m`:
Given ANY parameters `(r, B, A, K_m, C_obs, T)` satisfying the polynomial bounds, the set of
configurations `ω` with `≤ B_del` deleted edges whose purged graph fails `r`-color triangle-Ramsey
has cardinality `≤ (1 / 2) * m ^ N₀`! -/
private lemma card_badRamsey_le_half
    {r B A K_m B_del T : ℕ}
    (hr : 1 ≤ r)
    (hA_pos : 1 ≤ A)
    (hKm_pos : 1 ≤ K_m)
    (hT_ge : 3 * (⌈1 / shrinkDelta 2 (3 / (1 / ((4 * r * (ramseyBound r).choose 3 : ℕ) : ℚ)))⌉₊ + 1) ≤ T)
    (hA_ge : 128 * (2 * (ramseyBound r).choose 2) *
      (3 * r * T * (8 * r * (2 * (ramseyBound r).choose 2)) + 2) ≤ A)
    (hR_le_m : ramseyBound r ≤ 8 * A * K_m)
    (h18_le_m : 18 * T * (4 * r * (ramseyBound r).choose 3) ≤ 8 * A * K_m)
    (hm_ge2 : 2 ≤ 8 * A * K_m)
    (hBdel_le_m3 : B_del ≤ (8 * A * K_m) ^ 3) :
    let m := 8 * A * K_m
    let n := m ^ 2 + 2
    let N₀ := n.choose 2
    let badRamsey : Finset (Fin N₀ → Fin m) :=
      Finset.univ.filter (fun ω =>
        (rawEdges A ω \ purgeDenseObstructions n B (rawEdges A ω)).card ≤ B_del ∧
        ¬ForcesMonoTriangle
          (graphOfEdgeIndices n (purgeDenseObstructions n B (rawEdges A ω))) (Fin r))
    (badRamsey.card : ℚ) ≤ (1 / 2 : ℚ) * (m : ℚ) ^ N₀ := by
  let R := ramseyBound r
  have hR3 : 3 ≤ R := ramseyBound_ge_three hr
  let D_U : ℕ := 2 * R.choose 2
  have hDU_pos : 1 ≤ D_U := by
    have : 1 ≤ R.choose 2 := Nat.choose_pos (by omega)
    dsimp [D_U]; omega
  let D_tri : ℕ := 4 * r * R.choose 3
  have hDtri_pos : 1 ≤ D_tri := by
    have : 1 ≤ R.choose 3 := Nat.choose_pos hR3
    dsimp [D_tri]; nlinarith
  let ε : ℚ := 1 / (D_tri : ℚ)
  have hε_pos : 0 < ε := by positivity
  let lam_nat : ℕ := 8 * r * D_U
  have hlam_ge1 : 1 ≤ lam_nat := by dsimp [lam_nat]; nlinarith
  let C_exp : ℕ := 3 * r * T * lam_nat + 2

  let m : ℕ := 8 * A * K_m
  have hm1 : 1 ≤ m := by omega
  have hAm : A ≤ m := by
    dsimp [m]
    calc A = A * 1 := (mul_one A).symm
      _ ≤ A * (8 * K_m) := Nat.mul_le_mul_left A (by omega)
      _ = 8 * A * K_m := by ring
  let n : ℕ := m ^ 2 + 2
  have hn_ge_R : R ≤ n := by
    have hm_le_n : m ≤ n := by dsimp [n]; nlinarith
    omega
  let N₀ : ℕ := n.choose 2
  have hN₀_pos : 0 < N₀ := Nat.choose_pos (by dsimp [n]; nlinarith)
  let p : ℚ := 1 / (m : ℚ)
  let q : ℚ := (A : ℚ) / (m : ℚ)
  have hp_pos : 0 < p := by positivity
  have hp_le1 : p ≤ 1 := by
    dsimp [p]; rw [div_le_one (by positivity)]; exact_mod_cast hm1
  have hq_pos : 0 < q := by positivity
  have hq_le_eighth : q ≤ 1 / 8 := by
    dsimp [q]
    rw [div_le_iff₀ (by positivity : (0 : ℚ) < (m : ℚ))]
    have hm_eq : (m : ℚ) = 8 * (A : ℚ) * (K_m : ℚ) := by dsimp [m]; push_cast; ring
    have hK1 : (1 : ℚ) ≤ (K_m : ℚ) := by exact_mod_cast hKm_pos
    have hA0 : (0 : ℚ) ≤ (A : ℚ) := by positivity
    nlinarith
  have hq_le1 : q ≤ 1 := by linarith

  set badRamsey : Finset (Fin N₀ → Fin m) :=
    Finset.univ.filter (fun ω =>
      (rawEdges A ω \ purgeDenseObstructions n B (rawEdges A ω)).card ≤ B_del ∧
      ¬ForcesMonoTriangle
        (graphOfEdgeIndices n (purgeDenseObstructions n B (rawEdges A ω))) (Fin r))

  let L : ℕ := T * ⌈(N₀ : ℚ) * p⌉₊
  let smallSets : Finset (Finset (Fin N₀)) :=
    (Finset.univ : Finset (Fin N₀)).powerset.filter (fun F => F.card ≤ L)
  let tupleSpace : Finset (Fin r → Finset (Fin N₀)) :=
    Fintype.piFinset (fun _ : Fin r => smallSets)
  let H₃ := triangleHypergraph n
  let contOf : Finset (Fin N₀) → Finset (Fin N₀) := fun F =>
    canonicalContainer H₃ p 3 ε F ∪ F
  let uncovOf : (Fin r → Finset (Fin N₀)) → Finset (Fin N₀) := fun F =>
    Finset.univ \ Finset.univ.biUnion (fun c => contOf (F c))

  have h2N₀_eq : 2 * N₀ = n * (n - 1) := two_mul_choose_two n
  have hN₀_ge : m ^ 4 ≤ 2 * N₀ := by
    have hn1 : m ^ 2 ≤ n - 1 := by dsimp [n]; omega
    have hn0 : m ^ 2 ≤ n := by dsimp [n]; omega
    have hmul := Nat.mul_le_mul hn0 hn1
    have hm4 : m ^ 2 * m ^ 2 = m ^ 4 := by ring
    omega
  have hN₀_le : N₀ ≤ 2 * m ^ 4 := by
    have hm_ge2' : 2 ≤ m := hm_ge2
    have hm2 : 2 ≤ m ^ 2 := by nlinarith
    have hprod : n * (n - 1) ≤ 4 * m ^ 4 := by
      dsimp [n]
      calc (m ^ 2 + 2) * (m ^ 2 + 2 - 1)
          = (m ^ 2 + 2) * (m ^ 2 + 1) := by congr 1
        _ ≤ (2 * m ^ 2) * (2 * m ^ 2) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4 * m ^ 4 := by ring
    omega
  have hceil_Np_le : ⌈(N₀ : ℚ) * p⌉₊ ≤ 3 * m ^ 3 := by
    rw [Nat.ceil_le]
    dsimp [p]
    rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℚ) < (m : ℚ))]
    have hcast : (N₀ : ℚ) ≤ 2 * (m : ℚ) ^ 4 := by exact_mod_cast hN₀_le
    have hm4_pos : (0 : ℚ) ≤ (m : ℚ) ^ 4 := by positivity
    push_cast
    nlinarith
  have hL_le : L ≤ 3 * T * m ^ 3 := by
    dsimp [L]
    calc T * ⌈(N₀ : ℚ) * p⌉₊ ≤ T * (3 * m ^ 3) := Nat.mul_le_mul_left T hceil_Np_le
      _ = 3 * T * m ^ 3 := by ring

  let U_min : ℕ := ⌈(N₀ : ℚ) / (D_U : ℚ)⌉₊
  let validTuples : Finset (Fin r → Finset (Fin N₀)) :=
    tupleSpace.filter (fun F =>
      (∀ c₁ c₂, c₁ ≠ c₂ → Disjoint (F c₁) (F c₂)) ∧ U_min ≤ (uncovOf F).card)

  have hbadRamsey_witness : ∀ ω ∈ badRamsey,
      ∃ F ∈ validTuples,
        ∃ E ∈ (uncovOf F).powerset.filter (fun E => E.card ≤ B_del),
          (Finset.univ.biUnion F ∪ E) ⊆ rawEdges A ω ∧
            Disjoint (uncovOf F \ E) (rawEdges A ω) := by
    intro ω hω
    rcases Finset.mem_filter.mp hω with ⟨_, hdel_ω, hnot_ram⟩
    set E_purged := purgeDenseObstructions n B (rawEdges A ω)
    obtain ⟨I, hI_disj, hE_eq_biI, hI_indep⟩ :=
      partition_into_triangle_free_color_classes hr hnot_ram
    have hH₃_pos : 0 < H₃.card := by
      rw [card_triangleHypergraph]
      exact Nat.choose_pos (by dsimp [n]; nlinarith)
    have hsp₀ := triangleHypergraph_isSpread m hm1
    have hex_F : ∀ c : Fin r, ∃ Fc : Finset (Fin N₀),
        Fc ⊆ I c ∧
        Fc.card ≤ L ∧
        I c ⊆ contOf Fc ∧
        ((H₃.filter (fun e => e ⊆ canonicalContainer H₃ p 3 ε Fc)).card : ℚ) < ε * (H₃.card : ℚ) := by
      intro c
      obtain ⟨Fc, hFc_sub, hFc_card, hIc_cov, htri_lt⟩ :=
        exists_fingerprint_for_indep hN₀_pos hp_pos hp_le1 (by norm_num) hε_pos
          (triangleHypergraph_uniform n) hH₃_pos hsp₀ (I c) (hI_indep c)
      refine ⟨Fc, hFc_sub, ?_, hIc_cov, htri_lt⟩
      exact hFc_card.trans (Nat.mul_le_mul_right _ hT_ge)
    let F : Fin r → Finset (Fin N₀) := fun c => Classical.choose (hex_F c)
    have hF_spec := fun c => Classical.choose_spec (hex_F c)
    have hF_in_tuple : F ∈ tupleSpace := by
      rw [Fintype.mem_piFinset]
      intro c
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), (hF_spec c).2.1⟩
    have hF_disj : ∀ c₁ c₂, c₁ ≠ c₂ → Disjoint (F c₁) (F c₂) :=
      fun c₁ c₂ hne => Disjoint.mono (hF_spec c₁).1 (hF_spec c₂).1 (hI_disj c₁ c₂ hne)
    have hU_ge : U_min ≤ (uncovOf F).card := by
      have hLm2_le : (L : ℚ) * (m : ℚ) ^ 2 ≤ ε * (n.choose 3 : ℚ) := by
        have h6M : (m : ℚ) ^ 6 ≤ 6 * (n.choose 3 : ℚ) := by
          have hid : 6 * n.choose 3 = m ^ 2 * (2 * N₀) := by
            have h := three_mul_choose_three n
            have hs : n - 2 = m ^ 2 := Nat.add_sub_cancel _ _
            rw [hs] at h
            dsimp [N₀]
            linarith
          have hm6_nat : m ^ 6 ≤ 6 * n.choose 3 := by
            calc m ^ 6 = m ^ 2 * m ^ 4 := by ring
              _ ≤ m ^ 2 * (2 * N₀) := Nat.mul_le_mul_left _ hN₀_ge
              _ = 6 * n.choose 3 := hid.symm
          exact_mod_cast hm6_nat
        have hL_q : (L : ℚ) ≤ 3 * (T : ℚ) * (m : ℚ) ^ 3 := by exact_mod_cast hL_le
        have hm_big : 18 * (T : ℚ) * (D_tri : ℚ) ≤ (m : ℚ) := by exact_mod_cast h18_le_m
        have h1 : (L : ℚ) * (m : ℚ) ^ 2 * (D_tri : ℚ) ≤ (n.choose 3 : ℚ) := by
          calc (L : ℚ) * (m : ℚ) ^ 2 * (D_tri : ℚ)
              ≤ (3 * (T : ℚ) * (m : ℚ) ^ 3) * (m : ℚ) ^ 2 * (D_tri : ℚ) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_right hL_q (by positivity)
            _ = (18 * (T : ℚ) * (D_tri : ℚ)) * ((m : ℚ) ^ 5 / 6) := by ring
            _ ≤ (m : ℚ) * ((m : ℚ) ^ 5 / 6) :=
                mul_le_mul_of_nonneg_right hm_big (by positivity)
            _ = (m : ℚ) ^ 6 / 6 := by ring
            _ ≤ (n.choose 3 : ℚ) := by linarith
        dsimp [ε]
        rw [one_div_mul_eq_div, le_div_iff₀ (by positivity : (0 : ℚ) < (D_tri : ℚ))]
        exact h1
      have htri_each : ∀ c : Fin r,
          (((H₃.filter (fun e => e ⊆ contOf (F c))).card : ℚ)) ≤ 2 * ε * (n.choose 3 : ℚ) := by
        intro c
        let canon_c := canonicalContainer H₃ p 3 ε (F c)
        have hexp_add := triangleHypergraph_union_add_le hm1 canon_c (F c)
        have hcanon_lt : (((H₃.filter (fun e => e ⊆ canon_c)).card : ℚ)) < ε * (n.choose 3 : ℚ) := by
          have h : (((H₃.filter (fun e => e ⊆ canon_c)).card : ℚ)) < ε * (H₃.card : ℚ) :=
            (hF_spec c).2.2.2
          have hcardH : (H₃.card : ℚ) = (n.choose 3 : ℚ) := by
            exact_mod_cast card_triangleHypergraph n
          rwa [hcardH] at h
        have hFc_m2 : ((F c).card : ℚ) * (m : ℚ) ^ 2 ≤ (L : ℚ) * (m : ℚ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (hF_spec c).2.1) (by positivity)
        have heq_cont : H₃.filter (fun e => e ⊆ contOf (F c)) =
            (triangleHypergraph (m ^ 2 + 2)).filter (fun e => e ⊆ canon_c ∪ F c) := by
          ext e; simp [H₃, n, contOf, canon_c]
        have hexp_add' : (((H₃.filter (fun e => e ⊆ contOf (F c))).card : ℚ)) ≤
            (((H₃.filter (fun e => e ⊆ canon_c)).card : ℚ)) + ((F c).card : ℚ) * (m : ℚ) ^ 2 := by
          have h0 : (((triangleHypergraph (m ^ 2 + 2)).filter (fun e => e ⊆ canon_c ∪ F c)).card : ℚ) ≤
              (((triangleHypergraph (m ^ 2 + 2)).filter (fun e => e ⊆ canon_c)).card : ℚ) +
                ((F c).card : ℚ) * (m : ℚ) ^ 2 := hexp_add
          have heq_can : H₃.filter (fun e => e ⊆ canon_c) =
              (triangleHypergraph (m ^ 2 + 2)).filter (fun e => e ⊆ canon_c) := by
            ext e; simp [H₃, n]
          rw [heq_cont, heq_can]
          exact h0
        linarith
      have htri_sum : (∑ c : Fin r, (((H₃.filter (fun e => e ⊆ contOf (F c))).card : ℚ))) ≤
          (n.choose 3 : ℚ) / (2 * (R.choose 3 : ℚ)) := by
        calc (∑ c : Fin r, (((H₃.filter (fun e => e ⊆ contOf (F c))).card : ℚ)))
            ≤ ∑ _c : Fin r, (2 * ε * (n.choose 3 : ℚ)) := Finset.sum_le_sum (fun c _ => htri_each c)
          _ = (r : ℚ) * (2 * ε * (n.choose 3 : ℚ)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = (n.choose 3 : ℚ) / (2 * (R.choose 3 : ℚ)) := by
              dsimp [ε, D_tri]
              have hr_ne : (r : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (by omega : 0 < r)
              have hR3_ne : (R.choose 3 : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.choose_pos hR3)
              push_cast
              field_simp [hr_ne, hR3_ne]
              ring
      have hsup := ramsey_supersaturation hr hn_ge_R (fun c => contOf (F c)) htri_sum
      dsimp only at hsup
      have hDU_eq : (2 * (R.choose 2 : ℚ)) = (D_U : ℚ) := by dsimp [D_U]; push_cast; ring
      rw [hDU_eq] at hsup
      exact Nat.ceil_le.mpr hsup
    have hF_valid : F ∈ validTuples :=
      Finset.mem_filter.mpr ⟨hF_in_tuple, hF_disj, hU_ge⟩
    let E_bad : Finset (Fin N₀) := rawEdges A ω ∩ uncovOf F
    have hE_bad_sub_U : E_bad ⊆ uncovOf F := Finset.inter_subset_right
    have hE_bad_sub_del : E_bad ⊆ rawEdges A ω \ E_purged := by
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxRaw, hxUnc⟩
      refine Finset.mem_sdiff.mpr ⟨hxRaw, ?_⟩
      intro hxPurged
      rw [hE_eq_biI, Finset.mem_biUnion] at hxPurged
      rcases hxPurged with ⟨c, _, hxIc⟩
      have hxCont : x ∈ contOf (F c) := (hF_spec c).2.2.1 hxIc
      have hxInBi : x ∈ Finset.univ.biUnion (fun c' => contOf (F c')) :=
        Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hxCont⟩
      exact (Finset.mem_sdiff.mp hxUnc).2 hxInBi
    have hE_bad_card : E_bad.card ≤ B_del :=
      (Finset.card_le_card hE_bad_sub_del).trans hdel_ω
    have hF_raw : Finset.univ.biUnion F ∪ E_bad ⊆ rawEdges A ω := by
      refine Finset.union_subset ?_ Finset.inter_subset_left
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨c, _, hxFc⟩
      have hxIc : x ∈ I c := (hF_spec c).1 hxFc
      have hxPurged : x ∈ E_purged := by
        rw [hE_eq_biI]; exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hxIc⟩
      exact Finset.sdiff_subset hxPurged
    have hZ_disj : Disjoint (uncovOf F \ E_bad) (rawEdges A ω) := by
      rw [Finset.disjoint_left]
      intro x hxZ hxRaw
      rcases Finset.mem_sdiff.mp hxZ with ⟨hxUnc, hxNotBad⟩
      exact hxNotBad (Finset.mem_inter.mpr ⟨hxRaw, hxUnc⟩)
    exact ⟨F, hF_valid, E_bad,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hE_bad_sub_U, hE_bad_card⟩,
      hF_raw, hZ_disj⟩

  let cylSet : (Fin r → Finset (Fin N₀)) → Finset (Fin N₀) → Finset (Fin N₀ → Fin m) := fun F E =>
    Finset.univ.filter (fun ω =>
      (Finset.univ.biUnion F ∪ E) ⊆ rawEdges A ω ∧
        Disjoint (uncovOf F \ E) (rawEdges A ω))

  have hstep1 : (badRamsey.card : ℚ) ≤
      ∑ F ∈ validTuples,
        ∑ E ∈ (uncovOf F).powerset.filter (fun E => E.card ≤ B_del),
          ((cylSet F E).card : ℚ) := by
    apply card_le_double_sum_of_witness badRamsey validTuples
      (fun F => (uncovOf F).powerset.filter (fun E => E.card ≤ B_del)) cylSet
    intro ω hω
    obtain ⟨F, hF, E, hE, h1, h2⟩ := hbadRamsey_witness ω hω
    exact ⟨F, hF, E, hE, Finset.mem_filter.mpr ⟨Finset.mem_univ ω, h1, h2⟩⟩

  -- Evaluate each cylinder size via `card_grid_cylinder` and bound the inner sum over `E` via `sum_tail_subsets_le`!
  have hinner_F : ∀ F ∈ validTuples,
      (∑ E ∈ (uncovOf F).powerset.filter (fun E => E.card ≤ B_del),
        (((Finset.univ : Finset (Fin N₀ → Fin m)).filter (fun ω =>
          (Finset.univ.biUnion F ∪ E) ⊆ rawEdges A ω ∧
            Disjoint (uncovOf F \ E) (rawEdges A ω))).card : ℚ)) ≤
      (m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min) * ∏ c : Fin r, q ^ (F c).card := by
    intro F hF
    rcases (Finset.mem_filter.mp hF).2 with ⟨hF_disj, hU_ge⟩
    have hbiF_disj_U : Disjoint (Finset.univ.biUnion F) (uncovOf F) := by
      rw [Finset.disjoint_left]
      intro x hxBiF hxUnc
      rcases Finset.mem_biUnion.mp hxBiF with ⟨c, _, hxFc⟩
      have hxCont : x ∈ contOf (F c) := Finset.mem_union_right _ hxFc
      have hxBiCont : x ∈ Finset.univ.biUnion (fun c' => contOf (F c')) :=
        Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hxCont⟩
      exact (Finset.mem_sdiff.mp hxUnc).2 hxBiCont
    have hbiF_card : (Finset.univ.biUnion F).card = ∑ c : Fin r, (F c).card :=
      disjoint_biUnion_card_eq Finset.univ F (fun c₁ _ c₂ _ hne => hF_disj c₁ c₂ hne)
    have hq_prod : q ^ (Finset.univ.biUnion F).card = ∏ c : Fin r, q ^ (F c).card := by
      rw [hbiF_card, Finset.prod_pow_eq_pow_sum]
    have hcyl_sum :
        (∑ E ∈ (uncovOf F).powerset.filter (fun E => E.card ≤ B_del),
          (((Finset.univ : Finset (Fin N₀ → Fin m)).filter (fun ω =>
            (Finset.univ.biUnion F ∪ E) ⊆ rawEdges A ω ∧
              Disjoint (uncovOf F \ E) (rawEdges A ω))).card : ℚ)) =
        ((m : ℚ) ^ N₀ * ∏ c : Fin r, q ^ (F c).card) *
          ∑ E ∈ (uncovOf F).powerset.filter (fun E => E.card ≤ B_del),
            q ^ E.card * (1 - q) ^ (uncovOf F \ E).card := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun E hE => ?_)
      have hEU : E ⊆ uncovOf F := Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1
      have hd_FE : Disjoint (Finset.univ.biUnion F) E :=
        Disjoint.mono_right hEU hbiF_disj_U
      have hd_PZ : Disjoint (Finset.univ.biUnion F ∪ E) (uncovOf F \ E) := by
        rw [Finset.disjoint_union_left]
        exact ⟨Disjoint.mono_right Finset.sdiff_subset hbiF_disj_U, Finset.sdiff_disjoint.symm⟩
      have hcyl := card_grid_cylinder (N₀ := N₀) (m := m) hAm (by omega)
        (Finset.univ.biUnion F ∪ E) (uncovOf F \ E) hd_PZ
      rw [hcyl, Finset.card_union_of_disjoint hd_FE, pow_add]
      change (m : ℚ) ^ N₀ * (q ^ (Finset.univ.biUnion F).card * q ^ E.card) *
          (1 - q) ^ (uncovOf F \ E).card = _
      rw [hq_prod]
      ring
    rw [hcyl_sum]
    have htail := sum_tail_subsets_le (uncovOf F) B_del (le_of_lt hq_pos) hq_le1
    have h1q2_nn : 0 ≤ 1 - q / 2 := by linarith
    have hpow_mono : (1 - q / 2) ^ (uncovOf F).card ≤ (1 - q / 2) ^ U_min :=
      pow_le_pow_of_le_one h1q2_nn (by linarith) hU_ge
    have htail' : (∑ E ∈ (uncovOf F).powerset.filter (fun E => E.card ≤ B_del),
        q ^ E.card * (1 - q) ^ (uncovOf F \ E).card) ≤
        (2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min :=
      htail.trans (mul_le_mul_of_nonneg_left hpow_mono (by positivity))
    have hprod_F_nn : 0 ≤ ∏ c : Fin r, q ^ (F c).card :=
      rat_prod_nonneg Finset.univ _ (fun _ _ => pow_nonneg (le_of_lt hq_pos) _)
    calc ((m : ℚ) ^ N₀ * ∏ c : Fin r, q ^ (F c).card) *
          (∑ E ∈ (uncovOf F).powerset.filter (fun E => E.card ≤ B_del),
            q ^ E.card * (1 - q) ^ (uncovOf F \ E).card)
        ≤ ((m : ℚ) ^ N₀ * ∏ c : Fin r, q ^ (F c).card) *
            ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min) :=
          mul_le_mul_of_nonneg_left htail' (mul_nonneg (by positivity) hprod_F_nn)
      _ = (m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min) * ∏ c : Fin r, q ^ (F c).card := by ring

  -- Sum over `F ∈ validTuples ⊆ tupleSpace`, factor out `(∑_{Fc ∈ smallSets} q^|Fc|)^r`, and apply Bernstein + block decay!
  let lam : ℚ := (lam_nat : ℚ)
  have hlam1 : (1 : ℚ) ≤ lam := by
    change ((1 : ℕ) : ℚ) ≤ (lam_nat : ℚ)
    exact Nat.cast_le.mpr hlam_ge1
  have hsum_tuples : (∑ F ∈ validTuples, ∏ c : Fin r, q ^ (F c).card) ≤
      lam ^ (r * L) * (1 + q / lam) ^ (r * N₀) := by
    calc (∑ F ∈ validTuples, ∏ c : Fin r, q ^ (F c).card)
        ≤ ∑ F ∈ tupleSpace, ∏ c : Fin r, q ^ (F c).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => rat_prod_nonneg Finset.univ _ (fun _ _ => pow_nonneg (le_of_lt hq_pos) _))
      _ = (∑ Fc ∈ smallSets, q ^ Fc.card) ^ r := sum_pi_pow_eq r smallSets (fun Fc => q ^ Fc.card)
      _ ≤ (lam ^ L * (1 + q / lam) ^ N₀) ^ r :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity))
            (sum_pow_card_le_bernstein N₀ L (le_of_lt hq_pos) hlam1) r
      _ = lam ^ (r * L) * (1 + q / lam) ^ (r * N₀) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm L r, mul_comm N₀ r]

  have h1q2_pow_nn : 0 ≤ (1 - q / 2) ^ U_min := pow_nonneg (by linarith) _
  have hcoef_nn : 0 ≤ (m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) h1q2_pow_nn)
  have htot_bound1 : (badRamsey.card : ℚ) ≤
      (m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * lam ^ (r * L) *
        ((1 + q / lam) ^ (r * N₀) * (1 - q / 2) ^ U_min)) := by
    have ha : (badRamsey.card : ℚ) ≤
        ∑ F ∈ validTuples,
          (m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min) * ∏ c : Fin r, q ^ (F c).card :=
      hstep1.trans (Finset.sum_le_sum hinner_F)
    have hb : (∑ F ∈ validTuples,
        (m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min) * ∏ c : Fin r, q ^ (F c).card) =
        ((m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min)) *
          ∑ F ∈ validTuples, ∏ c : Fin r, q ^ (F c).card :=
      (Finset.mul_sum _ _ _).symm
    have hc : ((m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min)) *
        (∑ F ∈ validTuples, ∏ c : Fin r, q ^ (F c).card) ≤
        ((m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * (1 - q / 2) ^ U_min)) *
          (lam ^ (r * L) * (1 + q / lam) ^ (r * N₀)) :=
      mul_le_mul_of_nonneg_left hsum_tuples hcoef_nn
    let X1 := (m : ℚ) ^ N₀
    let X2 := (2 : ℚ) ^ B_del
    let X3 := (1 - q / 2) ^ U_min
    let X4 := lam ^ (r * L)
    let X5 := (1 + q / lam) ^ (r * N₀)
    have hd : (X1 * (X2 * X3)) * (X4 * X5) = X1 * (X2 * X4 * (X5 * X3)) := by ring
    exact ha.trans (hb.trans_le (hc.trans_eq hd))

  have hN₀_le_DU_Umin : N₀ ≤ D_U * U_min := nat_le_du_ceil_div N₀ D_U hDU_pos
  have hprod_half : (2 : ℚ) ^ B_del * lam ^ (r * L) *
      ((1 + q / lam) ^ (r * N₀) * (1 - q / 2) ^ U_min) ≤ 1 / 2 :=
    combine_prob_factors hr hDU_pos hA_pos hKm_pos hN₀_le_DU_Umin hN₀_ge hL_le hBdel_le_m3 hA_ge

  calc (badRamsey.card : ℚ)
      ≤ (m : ℚ) ^ N₀ * ((2 : ℚ) ^ B_del * lam ^ (r * L) *
          ((1 + q / lam) ^ (r * N₀) * (1 - q / 2) ^ U_min)) := htot_bound1
    _ ≤ (m : ℚ) ^ N₀ * (1 / 2 : ℚ) := mul_le_mul_of_nonneg_left hprod_half (by positivity)
    _ = (1 / 2 : ℚ) * (m : ℚ) ^ N₀ := by ring

/-- **Main Finite Sparse Triangle-Ramsey Theorem**:
For every `r ≥ 1` and `B ≥ 4`, there exists a finite simple graph `W : FiniteGraph` such that:
1. `ForcesMonoTriangle W.graph (Fin r)` (`W → (K₃)²_r`), and
2. `∀ S : Finset (Fin W.verts), 4 ≤ S.card → S.card ≤ B → edgesInside W.graph S ≤ 2 * S.card - 3`! -/
theorem exists_locally_sparse_triangle_ramsey (r B : ℕ) (hr : 1 ≤ r) (hB : 4 ≤ B) :
    ∃ W : FiniteGraph,
      ForcesMonoTriangle W.graph (Fin r) ∧
      ∀ S : Finset (Fin W.verts), 4 ≤ S.card → S.card ≤ B →
        edgesInside W.graph S ≤ 2 * S.card - 3 := by
  let R := ramseyBound r
  have hR3 : 3 ≤ R := ramseyBound_ge_three hr
  let D_U : ℕ := 2 * R.choose 2
  have hDU_pos : 1 ≤ D_U := by
    have : 1 ≤ R.choose 2 := Nat.choose_pos (by omega)
    dsimp [D_U]; omega
  let D_tri : ℕ := 4 * r * R.choose 3
  let T : ℕ := 3 * (⌈1 / shrinkDelta 2 (3 / (1 / (D_tri : ℚ)))⌉₊ + 1)
  let lam_nat : ℕ := 8 * r * D_U
  let A : ℕ := 128 * D_U * (3 * r * T * lam_nat + 2)
  have hA_pos : 1 ≤ A := by
    have : 1 ≤ 3 * r * T * lam_nat + 2 := by omega
    dsimp [A]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  let C_obs : ℕ := ⌈((B + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (B * B) *
    ((3 : ℚ) * ((A + 1 : ℕ) : ℚ) ^ 2) ^ B⌉₊ + 1
  let K_m : ℕ := R + 4 * B * C_obs + 18 * T * D_tri + 2
  have hKm_pos : 1 ≤ K_m := by dsimp [K_m]; omega
  let m : ℕ := 8 * A * K_m
  have hm1 : 1 ≤ m := by
    calc 1 ≤ 8 * 1 * 1 := by decide
      _ ≤ 8 * A * K_m := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hA_pos) hKm_pos
  have hAm : A ≤ m := by
    calc A = A * 1 := (mul_one A).symm
      _ ≤ A * (8 * K_m) := Nat.mul_le_mul_left A (by omega)
      _ = 8 * A * K_m := by ring
  let n : ℕ := m ^ 2 + 2
  let N₀ : ℕ := n.choose 2
  have hMarkov := card_many_obstructions_lt_half (m := m) (B := B) (A := A) hm1 hB hAm
  let badObs : Finset (Fin N₀ → Fin m) :=
    Finset.univ.filter (fun ω =>
      2 * C_obs * m ^ 2 < ((denseObstructions n B).filter (fun D => D ⊆ rawEdges A ω)).card)
  let B_del : ℕ := 4 * B * C_obs * m ^ 2
  let badRamsey : Finset (Fin N₀ → Fin m) :=
    Finset.univ.filter (fun ω =>
      (rawEdges A ω \ purgeDenseObstructions n B (rawEdges A ω)).card ≤ B_del ∧
      ¬ForcesMonoTriangle
        (graphOfEdgeIndices n (purgeDenseObstructions n B (rawEdges A ω))) (Fin r))
  have h8A_ge1 : 1 ≤ 8 * A := by omega
  have hR_le_m : R ≤ 8 * A * K_m := by
    calc R ≤ K_m := by dsimp [K_m]; omega
      _ = 1 * K_m := (one_mul K_m).symm
      _ ≤ (8 * A) * K_m := Nat.mul_le_mul_right K_m h8A_ge1
  have h18_le_m : 18 * T * D_tri ≤ 8 * A * K_m := by
    calc 18 * T * D_tri ≤ K_m := by dsimp [K_m]; omega
      _ = 1 * K_m := (one_mul K_m).symm
      _ ≤ (8 * A) * K_m := Nat.mul_le_mul_right K_m h8A_ge1
  have hm_ge2 : 2 ≤ 8 * A * K_m := by
    calc 2 ≤ K_m := by dsimp [K_m]; omega
      _ = 1 * K_m := (one_mul K_m).symm
      _ ≤ (8 * A) * K_m := Nat.mul_le_mul_right K_m h8A_ge1
  have hBdel_le_m3 : B_del ≤ m ^ 3 := by
    have h4BC_le_m : 4 * B * C_obs ≤ m := by
      calc 4 * B * C_obs ≤ K_m := by dsimp [K_m]; omega
        _ = 1 * K_m := (one_mul K_m).symm
        _ ≤ (8 * A) * K_m := Nat.mul_le_mul_right K_m h8A_ge1
    calc B_del = (4 * B * C_obs) * m ^ 2 := rfl
      _ ≤ m * m ^ 2 := Nat.mul_le_mul_right (m ^ 2) h4BC_le_m
      _ = m ^ 3 := by ring
  have hbadRam_le := card_badRamsey_le_half (B := B) hr hA_pos hKm_pos
    (le_refl T) (le_refl A) hR_le_m h18_le_m hm_ge2 hBdel_le_m3
  have hbadObs_lt : (badObs.card : ℚ) < (1 / 2 : ℚ) * (m : ℚ) ^ N₀ := hMarkov.1
  have hunion_lt : ((badObs ∪ badRamsey).card : ℚ) < (m : ℚ) ^ N₀ := by
    have hu_nat : (badObs ∪ badRamsey).card ≤ badObs.card + badRamsey.card :=
      Finset.card_union_le _ _
    have hu_q : ((badObs ∪ badRamsey).card : ℚ) ≤ (badObs.card : ℚ) + (badRamsey.card : ℚ) := by
      exact_mod_cast hu_nat
    dsimp only at hbadRam_le
    linarith
  have huniv_card : ((Finset.univ : Finset (Fin N₀ → Fin m)).card : ℚ) = (m : ℚ) ^ N₀ := by
    simp [Fintype.card_pi]
  have hstrict_card : (badObs ∪ badRamsey).card < (Finset.univ : Finset (Fin N₀ → Fin m)).card := by
    rw [← @Nat.cast_lt ℚ, huniv_card]
    exact hunion_lt
  have hex_good : ∃ ω₀ ∈ (Finset.univ : Finset (Fin N₀ → Fin m)), ω₀ ∉ badObs ∪ badRamsey := by
    by_contra! hall
    exact not_le_of_gt hstrict_card (Finset.card_le_card hall)
  obtain ⟨ω₀, _, hnot_bad⟩ := hex_good
  rw [Finset.mem_union, not_or] at hnot_bad
  rcases hnot_bad with ⟨hnot_obs, hnot_ram⟩
  have hdel_ω₀ : (rawEdges A ω₀ \ purgeDenseObstructions n B (rawEdges A ω₀)).card ≤ B_del :=
    hMarkov.2 ω₀ hnot_obs
  have hram : ForcesMonoTriangle
      (graphOfEdgeIndices n (purgeDenseObstructions n B (rawEdges A ω₀))) (Fin r) := by
    by_contra hfail
    exact hnot_ram (Finset.mem_filter.mpr ⟨Finset.mem_univ ω₀, hdel_ω₀, hfail⟩)
  refine ⟨⟨n, graphOfEdgeIndices n (purgeDenseObstructions n B (rawEdges A ω₀))⟩, hram, ?_⟩
  intro S hS4 hSB
  exact purgeDenseObstructions_sparse n B (rawEdges A ω₀) S hS4 hSB

/-- **Finite Core Avoidance Theorem**:
For every `r ≥ 1` and every finite family `ℱ : Finset FiniteGraph` of finite 2-Ramsey graphs
(`∀ M ∈ ℱ, ForcesMonoTriangle M.graph (Fin 2)`), there exists `W : FiniteGraph` such that:
1. `ForcesMonoTriangle W.graph (Fin r)` (`W → (K₃)²_r`), and
2. `∀ M ∈ ℱ, ¬EmbedsInto M W`! -/
theorem exists_ramsey_avoiding_family (r : ℕ) (hr : 1 ≤ r) (ℱ : Finset FiniteGraph)
    (hℱ : ∀ M ∈ ℱ, ForcesMonoTriangle M.graph (Fin 2)) :
    ∃ W : FiniteGraph,
      ForcesMonoTriangle W.graph (Fin r) ∧
      ∀ M ∈ ℱ, ¬EmbedsInto M W := by
  -- Set `B := 4 + ∑ M ∈ ℱ, M.verts` so `4 ≤ B` and `M.verts ≤ B` for every `M ∈ ℱ`!
  let B : ℕ := 4 + ∑ M ∈ ℱ, M.verts
  obtain ⟨W, hW_ramsey, hW_sparse⟩ := exists_locally_sparse_triangle_ramsey r B hr (by omega)
  refine ⟨W, hW_ramsey, ?_⟩
  intro M hM_mem ⟨φ, hφ_inj, hφ_adj⟩
  -- By `exists_dense_four_plus_subset`, `M` contains a subset `S ⊆ Fin M.verts` with `4 ≤ S.card`
  -- and `2 * S.card - 2 ≤ edgesInside M.graph S`!
  obtain ⟨S, hS4, hS_dense⟩ := exists_dense_four_plus_subset (hℱ M hM_mem)
  -- Push `S` forward along `φ` into `Fin W.verts` via order-independent `Finset.map`!
  let φ_emb : Fin M.verts ↪ Fin W.verts := ⟨φ, hφ_inj⟩
  have himg_eq_map : @Finset.image _ _ (Classical.decEq _) φ S = S.map φ_emb := by
    ext x; simp [φ_emb]
  have hedges_push : edgesInside M.graph S ≤ edgesInside W.graph (S.map φ_emb) := by
    rw [← himg_eq_map]
    exact edgesInside_le_of_emb φ hφ_inj hφ_adj S
  have hS'_card : (S.map φ_emb).card = S.card := Finset.card_map φ_emb
  have hM_le_B : M.verts ≤ B := by
    have hle_sum : M.verts ≤ ∑ M' ∈ ℱ, M'.verts :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hM_mem
    dsimp [B]; omega
  have hS_le_M : S.card ≤ M.verts := by
    have h := Finset.card_le_univ S; simpa using h
  have hW_S' := hW_sparse (S.map φ_emb) (by omega) (by omega)
  omega

end Erdos638
