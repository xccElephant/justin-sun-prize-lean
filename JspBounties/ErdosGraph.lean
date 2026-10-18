/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open SimpleGraph BigOperators

namespace Erdos23

private def bipFromSet (S : Finset (Fin 5)) : SimpleGraph (Fin 5) where
  Adj u v := (u ∈ S) ≠ (v ∈ S)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

private lemma bipFromSet_isBipartite (S : Finset (Fin 5)) : (bipFromSet S).IsBipartite := by
  refine ⟨Coloring.mk (fun u => if u ∈ S then (0 : Fin 2) else 1) ?_⟩
  intro u v huv
  change (u ∈ S) ≠ (v ∈ S) at huv
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all

open scoped Classical in
private lemma sub_bipFromSet_isBipartite (G : SimpleGraph (Fin 5)) (S : Finset (Fin 5)) :
    (G ⊓ bipFromSet S).IsBipartite := by
  obtain ⟨c⟩ := bipFromSet_isBipartite S
  exact ⟨Coloring.mk c (fun huv => c.valid huv.2)⟩

open scoped Classical in
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  intro G hcf
  have h_not_tri : ∀ u v w : Fin 5, ¬(G.Adj u v ∧ G.Adj v w ∧ G.Adj u w) := by
    intro u v w ⟨h1, h2, h3⟩
    apply hcf {u, v, w}
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact (hxy rfl).elim
      · exact h1
      · exact h3
      · exact h1.symm
      · exact (hxy rfl).elim
      · exact h2
      · exact h3.symm
      · exact h2.symm
      · exact (hxy rfl).elim
    · have huv : u ≠ v := G.ne_of_adj h1
      have hvw : v ≠ w := G.ne_of_adj h2
      have huw : u ≠ w := G.ne_of_adj h3
      simp [huv, hvw, huw]
  by_cases hex2 : ∃ v : Fin 5, 2 ≤ (G.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hex2
    let S := G.neighborFinset v
    have hS : S = G.neighborFinset v := rfl
    refine ⟨G ⊓ bipFromSet S, inf_le_left, sub_bipFromSet_isBipartite G S, ?_⟩
    have h_not_mem_v : v ∉ S := G.notMem_neighborFinset_self v
    have h_card_Sv : (insert v S).card ≤ 5 := le_trans (Finset.card_le_univ _) (by decide)
    have h_card_compl : ((insert v S)ᶜ : Finset (Fin 5)).card ≤ 2 := by
      rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem h_not_mem_v, hS]
      omega
    have h_sub : G.edgeFinset \ (G ⊓ bipFromSet S).edgeFinset ⊆
        (((insert v S)ᶜ : Finset (Fin 5)).sym2.filter (fun e => ¬e.IsDiag)) := by
      intro e he
      rw [Finset.mem_sdiff, mem_edgeFinset, mem_edgeFinset] at he
      rcases e with ⟨x, y⟩
      have hxy : G.Adj x y := he.1
      have h_same : (x ∈ S) ↔ (y ∈ S) := by
        have h1 : ((x ∈ S) = (y ∈ S)) := not_ne_iff.mp (fun hdiff => he.2 ⟨hxy, hdiff⟩)
        exact eq_iff_iff.mp h1
      rw [Finset.mem_filter, Finset.mem_sym2_iff]
      refine ⟨?_, G.not_isDiag_of_mem_edgeSet he.1⟩
      intro z hz
      rw [Finset.mem_compl, Finset.mem_insert, not_or]
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · have hxS : z ∉ S := by
          intro hxS
          have hyS : y ∈ S := h_same.mp hxS
          rw [hS, mem_neighborFinset] at hxS hyS
          exact h_not_tri v z y ⟨hxS, hxy, hyS⟩
        refine ⟨?_, hxS⟩
        rintro rfl
        have hyS : y ∈ S := by rw [hS, mem_neighborFinset]; exact hxy
        exact hxS (h_same.mpr hyS)
      · have hyS : z ∉ S := by
          intro hyS
          have hxS : x ∈ S := h_same.mpr hyS
          rw [hS, mem_neighborFinset] at hxS hyS
          exact h_not_tri v x z ⟨hxS, hxy, hyS⟩
        refine ⟨?_, hyS⟩
        rintro rfl
        have hxS : x ∈ S := by rw [hS, mem_neighborFinset]; exact hxy.symm
        exact hyS (h_same.mp hxS)
    have h_card_sym2 : ∀ A : Finset (Fin 5), A.card ≤ 2 → (A.sym2.filter (fun e => ¬e.IsDiag)).card ≤ 1 := by
      decide +kernel
    exact le_trans (Finset.card_le_card (by convert h_sub)) (h_card_sym2 _ h_card_compl)
  · push Not at hex2
    by_cases hcard : G.edgeFinset.card ≤ 1
    · refine ⟨⊥, bot_le, ⟨Coloring.mk (fun _ => 0) (fun h => False.elim h)⟩, ?_⟩
      exact le_trans (Finset.card_le_card Finset.sdiff_subset) hcard
    · push Not at hcard
      obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < G.edgeFinset.card)
      rcases e with ⟨u, v⟩
      have huv : G.Adj u v := mem_edgeFinset.mp he
      let S : Finset (Fin 5) := {u}
      let H := G ⊓ bipFromSet S
      refine ⟨H, inf_le_left, sub_bipFromSet_isBipartite G S, ?_⟩
      have h_sum_deg : ∑ w : Fin 5, G.degree w ≤ 5 := by
        calc ∑ w : Fin 5, G.degree w ≤ ∑ _w : Fin 5, 1 := by
              refine Finset.sum_le_sum fun w _ => ?_
              rw [← card_neighborFinset_eq_degree]
              exact Nat.le_of_lt_succ (hex2 w)
          _ = 5 := by simp
      have h_edges_le_2 : G.edgeFinset.card ≤ 2 := by
        have h_hand := G.sum_degrees_eq_twice_card_edges
        omega
      refine Nat.le_of_lt_succ (lt_of_lt_of_le (Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩) h_edges_le_2)
      intro hsub
      have hmem := hsub he
      rw [Finset.mem_sdiff] at hmem
      apply hmem.2
      have h_adj_H : s(u, v) ∈ H.edgeSet := ⟨huv, by
        change (u ∈ S) ≠ (v ∈ S)
        have hne : v ≠ u := (G.ne_of_adj huv).symm
        simp [S, hne]⟩
      exact (@mem_edgeFinset _ H s(u, v) (@fintypeEdgeSet (Fin 5) H Sym2.instFintype fun a b => Classical.propDecidable (H.Adj a b))).mpr h_adj_H

open scoped Classical in
theorem erdos_23.variants.n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  refine ⟨cycleGraph 5, by unfold CliqueFree; decide +kernel, fun H hHG hH => ?_⟩
  by_contra hcon
  have h0 := Finset.card_eq_zero.1 (Nat.lt_one_iff.1 (not_le.1 hcon))
  have hsub := Finset.sdiff_eq_empty_iff_subset.1 h0
  rw [Finset.subset_iff] at hsub
  simp only [mem_edgeFinset] at hsub
  have hGH : cycleGraph 5 ≤ H := edgeSet_subset_edgeSet.1 fun _ he => hsub he
  obtain rfl : H = cycleGraph 5 := le_antisymm hHG hGH
  have h2 := hH.chromaticNumber_le
  rw [chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)] at h2
  exact absurd h2 (by decide)

end Erdos23

namespace Erdos617

/--
Erdős and Gyárfás [ErGy99] showed this property fails for infinitely many $r$ if we replace $r^2+1$
by $r^2$.
-/
theorem erdos_617.variants.r2 :
    {r : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = r^2 ∧
      ∃ (coloring : Sym2 V → Fin r),
        ∀ (S : Finset V), S.card = r + 1 →
          ∀ (k : Fin r), ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun n => ?_
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max (n + 1) 2)
  have hp_gt : n < p := lt_of_lt_of_le (Nat.lt_succ_self n) (le_trans (le_max_left _ _) hp_ge)
  have hp_ge2 : 2 ≤ p := le_trans (le_max_right _ _) hp_ge
  have hp_pos : 0 < p := by omega
  have : NeZero p := ⟨ne_of_gt hp_pos⟩
  have : Fact p.Prime := ⟨hp_prime⟩
  refine ⟨p, ?_, hp_gt⟩
  rw [Set.mem_ofPred_eq]
  refine ⟨ZMod p × ZMod p, inferInstance, inferInstance, by simp [sq], ?_⟩
  refine ⟨Sym2.lift ⟨fun u v =>
    if u.1 = v.1 then
      ⟨0, hp_pos⟩
    else
      let m : ZMod p := (v.2 - u.2) * (v.1 - u.1)⁻¹
      ⟨m.val, m.val_lt⟩,
    fun u v => by
      dsimp only
      split_ifs with h1 h2 h2
      · rfl
      · exfalso; exact h2 h1.symm
      · exfalso; exact h1 h2.symm
      · congr 1
        have h_eq : (u.2 - v.2) * (u.1 - v.1)⁻¹ = (v.2 - u.2) * (v.1 - u.1)⁻¹ := by
          have hnum : u.2 - v.2 = -(v.2 - u.2) := by ring
          have hden : u.1 - v.1 = -(v.1 - u.1) := by ring
          rw [hnum, hden, inv_neg, neg_mul_neg]
        rw [h_eq]⟩, ?_⟩
  intro S hS k
  let m : ZMod p := (k.val : ZMod p)
  have hcard : (Finset.univ : Finset (ZMod p)).card < S.card := by
    rw [Finset.card_univ, ZMod.card, hS]
    omega
  obtain ⟨u, hu, v, hv, huv, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    hcard (fun (x : ZMod p × ZMod p) _ => Finset.mem_univ (x.2 - m * x.1))
  by_cases h_u1_eq_v1 : u.1 = v.1
  · exfalso
    apply huv
    ext
    · exact h_u1_eq_v1
    · rw [h_u1_eq_v1] at heq
      exact sub_left_inj.mp heq
  · refine ⟨u, hu, v, hv, huv, ?_⟩
    ext
    simp only [Sym2.lift_mk, if_neg h_u1_eq_v1]
    have h_sub : v.2 - u.2 = m * (v.1 - u.1) := by
      calc v.2 - u.2
          = (v.2 - m * v.1) - (u.2 - m * u.1) + m * (v.1 - u.1) := by ring
        _ = m * (v.1 - u.1) := by rw [heq, sub_self, zero_add]
    have h_den_ne : v.1 - u.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h_u1_eq_v1)
    have h_div : (v.2 - u.2) * (v.1 - u.1)⁻¹ = m := by
      rw [h_sub, mul_assoc, mul_inv_cancel₀ h_den_ne, mul_one]
    rw [h_div]
    exact ZMod.val_cast_of_lt k.isLt

private lemma no_five_edges_in_four {V : Type} [Fintype V] [DecidableEq V]
    (coloring : Sym2 V → Fin 3)
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k)
    (c : Fin 3) {x1 x2 x3 x4 : V}
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4)
    (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h34 : x3 ≠ x4)
    (e1 : coloring s(x1, x2) = c) (e2 : coloring s(x1, x3) = c)
    (e3 : coloring s(x1, x4) = c) (e4 : coloring s(x2, x3) = c)
    (e5 : coloring s(x2, x4) = c) : False := by
  let S : Finset V := {x1, x2, x3, x4}
  have hS : S.card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton] <;> simp [*]
  let c1 : Fin 3 := ⟨(c.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  let c2 : Fin 3 := ⟨(c.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
  have hc1 : c1 ≠ c := by fin_cases c <;> decide
  have hc2 : c2 ≠ c := by fin_cases c <;> decide
  have hc12 : c1 ≠ c2 := by fin_cases c <;> decide
  obtain ⟨u1, hu1, v1, hv1, huv1, hcol1⟩ := hbal S c1 hS
  obtain ⟨u2, hu2, v2, hv2, huv2, hcol2⟩ := hbal S c2 hS
  have hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ c → s(u, v) = s(x3, x4) := by
    intro u hu v hv huv hne
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
    all_goals try (exfalso; exact huv rfl)
    all_goals try (exfalso; exact hne e1)
    all_goals try (exfalso; exact hne (by rw [Sym2.eq_swap]; exact e1))
    all_goals try (exfalso; exact hne e2)
    all_goals try (exfalso; exact hne (by rw [Sym2.eq_swap]; exact e2))
    all_goals try (exfalso; exact hne e3)
    all_goals try (exfalso; exact hne (by rw [Sym2.eq_swap]; exact e3))
    all_goals try (exfalso; exact hne e4)
    all_goals try (exfalso; exact hne (by rw [Sym2.eq_swap]; exact e4))
    all_goals try (exfalso; exact hne e5)
    all_goals try (exfalso; exact hne (by rw [Sym2.eq_swap]; exact e5))
    · rfl
    · exact Sym2.eq_swap
  have hp1 := hpair u1 hu1 v1 hv1 huv1 (by rw [hcol1]; exact hc1)
  have hp2 := hpair u2 hu2 v2 hv2 huv2 (by rw [hcol2]; exact hc2)
  rw [hp1] at hcol1
  rw [hp2] at hcol2
  exact hc12 (hcol1.symm.trans hcol2)

private lemma w_edge_of_three {V : Type} [Fintype V] [DecidableEq V]
    (coloring : Sym2 V → Fin 3)
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k)
    (c : Fin 3) (v : V) {x1 x2 x3 : V}
    (hx1 : x1 ≠ v ∧ coloring s(v, x1) ≠ c)
    (hx2 : x2 ≠ v ∧ coloring s(v, x2) ≠ c)
    (hx3 : x3 ≠ v ∧ coloring s(v, x3) ≠ c)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3) :
    coloring s(x1, x2) = c ∨ coloring s(x1, x3) = c ∨ coloring s(x2, x3) = c := by
  let S : Finset V := {v, x1, x2, x3}
  have hS : S.card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h23]
    · simp [h12, h13]
    · simp [hx1.1.symm, hx2.1.symm, hx3.1.symm]
  obtain ⟨u, hu, w, hw, huw, hcol⟩ := hbal S c hS
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu hw
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl
  all_goals try (exfalso; exact huw rfl)
  · exfalso; exact hx1.2 hcol
  · exfalso; exact hx2.2 hcol
  · exfalso; exact hx3.2 hcol
  · exfalso; rw [Sym2.eq_swap] at hcol; exact hx1.2 hcol
  · exact Or.inl hcol
  · exact Or.inr (Or.inl hcol)
  · exfalso; rw [Sym2.eq_swap] at hcol; exact hx2.2 hcol
  · rw [Sym2.eq_swap] at hcol; exact Or.inl hcol
  · exact Or.inr (Or.inr hcol)
  · exfalso; rw [Sym2.eq_swap] at hcol; exact hx3.2 hcol
  · rw [Sym2.eq_swap] at hcol; exact Or.inr (Or.inl hcol)
  · rw [Sym2.eq_swap] at hcol; exact Or.inr (Or.inr hcol)

private lemma w_nonneighbors_le_three {V : Type} [Fintype V] [DecidableEq V]
    (coloring : Sym2 V → Fin 3)
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k)
    (c : Fin 3) (v : V) (U : Finset V)
    (hU : ∀ u ∈ U, u ≠ v ∧ coloring s(v, u) ≠ c)
    (u : V) (hu : u ∈ U) :
    (U.filter (fun w => w ≠ u ∧ coloring s(u, w) ≠ c)).card ≤ 3 := by
  by_contra hgt
  have hge : 4 ≤ (U.filter (fun w => w ≠ u ∧ coloring s(u, w) ≠ c)).card := by omega
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hge
  obtain ⟨x1, x2, x3, x4, h12, h13, h14, h23, h24, h34, hT_eq⟩ :
      ∃ x1 x2 x3 x4 : V, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
        T = {x1, x2, x3, x4} := by
    rw [Finset.card_eq_succ] at hT_card
    obtain ⟨x1, T1, hx1, rfl, hT1⟩ := hT_card
    rw [Finset.card_eq_succ] at hT1
    obtain ⟨x2, T2, hx2, rfl, hT2⟩ := hT1
    rw [Finset.card_eq_succ] at hT2
    obtain ⟨x3, T3, hx3, rfl, hT3⟩ := hT2
    rw [Finset.card_eq_one] at hT3
    obtain ⟨x4, rfl⟩ := hT3
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx1 hx2 hx3
    exact ⟨x1, x2, x3, x4, hx1.1, hx1.2.1, hx1.2.2, hx2.1, hx2.2, hx3, rfl⟩
  have hmem : ∀ x ∈ T, x ∈ U ∧ x ≠ u ∧ coloring s(u, x) ≠ c := by
    intro x hx
    have := hT_sub hx
    rw [Finset.mem_filter] at this
    exact ⟨this.1, this.2⟩
  have hx1 := hmem x1 (by simp [hT_eq])
  have hx2 := hmem x2 (by simp [hT_eq])
  have hx3 := hmem x3 (by simp [hT_eq])
  have hx4 := hmem x4 (by simp [hT_eq])
  have hedge : ∀ a b : V, (a ∈ U ∧ a ≠ u ∧ coloring s(u, a) ≠ c) →
      (b ∈ U ∧ b ≠ u ∧ coloring s(u, b) ≠ c) → a ≠ b → coloring s(a, b) = c := by
    intro a b ha hb hab
    rcases w_edge_of_three coloring hbal c v (hU u hu) (hU a ha.1) (hU b hb.1)
      ha.2.1.symm hb.2.1.symm hab with h1 | h2 | h3
    · exfalso; exact ha.2.2 h1
    · exfalso; exact hb.2.2 h2
    · exact h3
  exact no_five_edges_in_four coloring hbal c h12 h13 h14 h23 h24 h34
    (hedge x1 x2 hx1 hx2 h12)
    (hedge x1 x3 hx1 hx3 h13)
    (hedge x1 x4 hx1 hx4 h14)
    (hedge x2 x3 hx2 hx3 h23)
    (hedge x2 x4 hx2 hx4 h24)

private lemma w_neighbors_le_three_of_card_ge_six {V : Type} [Fintype V] [DecidableEq V]
    (coloring : Sym2 V → Fin 3)
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k)
    (c : Fin 3) (v : V) (U : Finset V)
    (hU : ∀ u ∈ U, u ≠ v ∧ coloring s(v, u) ≠ c)
    (hU_card : 6 ≤ U.card)
    (u : V) (_hu : u ∈ U) :
    (U.filter (fun w => w ≠ u ∧ coloring s(u, w) = c)).card ≤ 3 := by
  by_contra hgt
  have hge : 4 ≤ (U.filter (fun w => w ≠ u ∧ coloring s(u, w) = c)).card := by omega
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hge
  have h_ins_card : (insert u T).card ≤ 5 := by
    refine le_trans (Finset.card_insert_le u T) ?_
    omega
  obtain ⟨w, hwU, hw_not_ins⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : (insert u T).card < U.card)
  obtain ⟨x1, x2, x3, x4, h12, h13, h14, h23, h24, h34, hT_eq⟩ :
      ∃ x1 x2 x3 x4 : V, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
        T = {x1, x2, x3, x4} := by
    rw [Finset.card_eq_succ] at hT_card
    obtain ⟨x1, T1, hx1, rfl, hT1⟩ := hT_card
    rw [Finset.card_eq_succ] at hT1
    obtain ⟨x2, T2, hx2, rfl, hT2⟩ := hT1
    rw [Finset.card_eq_succ] at hT2
    obtain ⟨x3, T3, hx3, rfl, hT3⟩ := hT2
    rw [Finset.card_eq_one] at hT3
    obtain ⟨x4, rfl⟩ := hT3
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx1 hx2 hx3
    exact ⟨x1, x2, x3, x4, hx1.1, hx1.2.1, hx1.2.2, hx2.1, hx2.2, hx3, rfl⟩
  have hmem : ∀ x ∈ T, x ∈ U ∧ x ≠ u ∧ coloring s(u, x) = c := by
    intro x hx
    have := hT_sub hx
    rw [Finset.mem_filter] at this
    exact ⟨this.1, this.2⟩
  have hx1 := hmem x1 (by simp [hT_eq])
  have hx2 := hmem x2 (by simp [hT_eq])
  have hx3 := hmem x3 (by simp [hT_eq])
  have hx4 := hmem x4 (by simp [hT_eq])
  rw [hT_eq] at hw_not_ins
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw_not_ins
  rcases hw_not_ins with ⟨hwu, hwx1, hwx2, hwx3, hwx4⟩
  -- For any three distinct y1, y2, y3 in {x1, x2, x3, x4}, since u is connected by c to all three:
  -- 1) at least one pair in {y1, y2, y3} has color c (by w_edge_of_three)
  -- 2) no vertex in {y1, y2, y3} can have color c to BOTH of the other two (by no_five_edges_in_four on {y1, u, y2, y3})!
  have h_no_two : ∀ a b d : V,
      (a ∈ U ∧ a ≠ u ∧ coloring s(u, a) = c) →
      (b ∈ U ∧ b ≠ u ∧ coloring s(u, b) = c) →
      (d ∈ U ∧ d ≠ u ∧ coloring s(u, d) = c) →
      a ≠ b → a ≠ d → b ≠ d →
      coloring s(a, b) = c → coloring s(a, d) ≠ c := by
    intro a b d ha hb hd hab had hbd hab_c had_c
    exact no_five_edges_in_four coloring hbal c ha.2.1 hab had hb.2.1.symm hd.2.1.symm hbd
      (by rw [Sym2.eq_swap]; exact ha.2.2) hab_c had_c hb.2.2 hd.2.2
  -- Also, if a, b in T have coloring s(a, b) = c, then {u, a, b} is a c-triangle, so w cannot have color c to BOTH a and b!
  have h_w_not_both : ∀ a b : V,
      (a ∈ U ∧ a ≠ u ∧ coloring s(u, a) = c) →
      (b ∈ U ∧ b ≠ u ∧ coloring s(u, b) = c) →
      a ≠ b → w ≠ a → w ≠ b → coloring s(a, b) = c →
      coloring s(a, w) ≠ c ∨ coloring s(b, w) ≠ c := by
    intro a b ha hb hab hwa hwb hab_c
    by_contra hboth
    push Not at hboth
    exact no_five_edges_in_four coloring hbal c hab ha.2.1 (Ne.symm hwa) hb.2.1 (Ne.symm hwb) (Ne.symm hwu)
      hab_c (by rw [Sym2.eq_swap]; exact ha.2.2) hboth.1
      (by rw [Sym2.eq_swap]; exact hb.2.2) hboth.2
  -- And if a, b in T have coloring s(a, b) ≠ c, then by w_edge_of_three on {a, b, w}, either (a, w) = c or (b, w) = c!
  -- Therefore, on {x1, x2, x3, x4}:
  -- By w_edge_of_three on {x1, x2, x3}, one of (x1, x2), (x1, x3), (x2, x3) has color c!
  -- In fact, let us prove a general helper for ANY two disjoint c-edges (a, d) and (b, e) in T:
  have h_disjoint_edges : ∀ a d b e : V,
      (a ∈ U ∧ a ≠ u ∧ coloring s(u, a) = c) →
      (d ∈ U ∧ d ≠ u ∧ coloring s(u, d) = c) →
      (b ∈ U ∧ b ≠ u ∧ coloring s(u, b) = c) →
      (e ∈ U ∧ e ≠ u ∧ coloring s(u, e) = c) →
      a ≠ d → b ≠ e → a ≠ b → a ≠ e → d ≠ b → d ≠ e →
      w ≠ a → w ≠ d → w ≠ b → w ≠ e →
      coloring s(a, d) = c → coloring s(b, e) = c → False := by
    intro a d b e ha hd hb he had hbe hab hae hdb hde hwa hwd hwb hwe had_c hbe_c
    have hab_nc : coloring s(a, b) ≠ c := h_no_two a d b ha hd hb had hab hdb had_c
    have hae_nc : coloring s(a, e) ≠ c := h_no_two a d e ha hd he had hae hde had_c
    have hdb_nc : coloring s(d, b) ≠ c :=
      h_no_two d a b hd ha hb had.symm hdb hab (by rw [Sym2.eq_swap]; exact had_c)
    have hde_nc : coloring s(d, e) ≠ c :=
      h_no_two d a e hd ha he had.symm hde hae (by rw [Sym2.eq_swap]; exact had_c)
    rcases h_w_not_both a d ha hd had hwa hwd had_c with haw | hdw <;>
    rcases h_w_not_both b e hb he hbe hwb hwe hbe_c with hbw | hew
    · rcases w_edge_of_three coloring hbal c v (hU a ha.1) (hU b hb.1) (hU w hwU) hab hwa.symm hwb.symm with h1 | h2 | h3
      · exact hab_nc h1
      · exact haw h2
      · exact hbw h3
    · rcases w_edge_of_three coloring hbal c v (hU a ha.1) (hU e he.1) (hU w hwU) hae hwa.symm hwe.symm with h1 | h2 | h3
      · exact hae_nc h1
      · exact haw h2
      · exact hew h3
    · rcases w_edge_of_three coloring hbal c v (hU d hd.1) (hU b hb.1) (hU w hwU) hdb hwd.symm hwb.symm with h1 | h2 | h3
      · exact hdb_nc h1
      · exact hdw h2
      · exact hbw h3
    · rcases w_edge_of_three coloring hbal c v (hU d hd.1) (hU e he.1) (hU w hwU) hde hwd.symm hwe.symm with h1 | h2 | h3
      · exact hde_nc h1
      · exact hdw h2
      · exact hew h3
  -- And whenever (a, d) = c in {a, d, b, e}, then (b, e) MUST also be c!
  have h_forced_pair : ∀ a d b e : V,
      (a ∈ U ∧ a ≠ u ∧ coloring s(u, a) = c) →
      (d ∈ U ∧ d ≠ u ∧ coloring s(u, d) = c) →
      (b ∈ U ∧ b ≠ u ∧ coloring s(u, b) = c) →
      (e ∈ U ∧ e ≠ u ∧ coloring s(u, e) = c) →
      a ≠ d → b ≠ e → a ≠ b → a ≠ e → d ≠ b → d ≠ e →
      coloring s(a, d) = c → coloring s(b, e) = c := by
    intro a d b e ha hd hb he had hbe hab hae hdb hde had_c
    have hab_nc : coloring s(a, b) ≠ c := h_no_two a d b ha hd hb had hab hdb had_c
    have hae_nc : coloring s(a, e) ≠ c := h_no_two a d e ha hd he had hae hde had_c
    rcases w_edge_of_three coloring hbal c v (hU a ha.1) (hU b hb.1) (hU e he.1) hab hae hbe with h1 | h2 | h3
    · exfalso; exact hab_nc h1
    · exfalso; exact hae_nc h2
    · exact h3
  rcases w_edge_of_three coloring hbal c v (hU x1 hx1.1) (hU x2 hx2.1) (hU x3 hx3.1) h12 h13 h23 with h12_c | h13_c | h23_c
  · exact h_disjoint_edges x1 x2 x3 x4 hx1 hx2 hx3 hx4 h12 h34 h13 h14 h23 h24 hwx1 hwx2 hwx3 hwx4
      h12_c (h_forced_pair x1 x2 x3 x4 hx1 hx2 hx3 hx4 h12 h34 h13 h14 h23 h24 h12_c)
  · exact h_disjoint_edges x1 x3 x2 x4 hx1 hx3 hx2 hx4 h13 h24 h12 h14 h23.symm h34 hwx1 hwx3 hwx2 hwx4
      h13_c (h_forced_pair x1 x3 x2 x4 hx1 hx3 hx2 hx4 h13 h24 h12 h14 h23.symm h34 h13_c)
  · exact h_disjoint_edges x2 x3 x1 x4 hx2 hx3 hx1 hx4 h23 h14 h12.symm h24 h13.symm h34 hwx2 hwx3 hwx1 hwx4
      h23_c (h_forced_pair x2 x3 x1 x4 hx2 hx3 hx1 hx4 h23 h14 h12.symm h24 h13.symm h34 h23_c)

private lemma w_card_eq_six_and_deg_three {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 10)
    (coloring : Sym2 V → Fin 3)
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k)
    (c : Fin 3) (v : V) :
    (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = c)).card = 3 ∧
    (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) ≠ c)).card = 6 := by
  have h_w_le : ∀ k : Fin 3, (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) ≠ k)).card ≤ 6 := by
    intro k
    set U := Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) ≠ k)
    have hU : ∀ u ∈ U, u ≠ v ∧ coloring s(v, u) ≠ k := fun u hu => (Finset.mem_filter.mp hu).2
    by_contra hgt
    have hU_ge7 : 7 ≤ U.card := by omega
    obtain ⟨U7, hU7_sub, hU7_card⟩ := Finset.exists_subset_card_eq hU_ge7
    have hU7 : ∀ u ∈ U7, u ≠ v ∧ coloring s(v, u) ≠ k := fun u hu => hU u (hU7_sub hu)
    have hU7_ge6 : 6 ≤ U7.card := by omega
    have h_sum_each : ∀ u ∈ U7, (U7.filter (fun w => w ≠ u ∧ coloring s(u, w) = k)).card = 3 := by
      intro u hu
      have h1 := w_nonneighbors_le_three coloring hbal k v U7 hU7 u hu
      have h2 := w_neighbors_le_three_of_card_ge_six coloring hbal k v U7 hU7 hU7_ge6 u hu
      have h_union : U7.filter (fun w => w ≠ u ∧ coloring s(u, w) ≠ k) ∪
          U7.filter (fun w => w ≠ u ∧ coloring s(u, w) = k) = U7.erase u := by
        ext w
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
        tauto
      have h_disj : Disjoint (U7.filter (fun w => w ≠ u ∧ coloring s(u, w) ≠ k))
          (U7.filter (fun w => w ≠ u ∧ coloring s(u, w) = k)) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        rw [Finset.mem_filter] at hw1 hw2
        exact hw1.2.2 hw2.2.2
      have h_sum := Finset.card_union_of_disjoint h_disj
      rw [h_union, Finset.card_erase_of_mem hu, hU7_card] at h_sum
      omega
    -- On U7, define the induced SimpleGraph G7 where Adj a b ↔ a ≠ b ∧ coloring s(a, b) = k:
    let G7 : SimpleGraph U7 := {
      Adj := fun a b => a.1 ≠ b.1 ∧ coloring s(a.1, b.1) = k
      symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
      loopless := ⟨fun a h => h.1 rfl⟩
    }
    have h_deg_G7 : ∀ a : U7, G7.degree a = 3 := by
      rintro ⟨u, hu⟩
      rw [← card_neighborFinset_eq_degree]
      refine Eq.trans ?_ (h_sum_each u hu)
      refine Finset.card_bij (fun (w : U7) _ => w.1) ?_ ?_ ?_
      · rintro ⟨w, hw⟩ hmem
        rw [mem_neighborFinset] at hmem
        rw [Finset.mem_filter]
        exact ⟨hw, hmem.1.symm, hmem.2⟩
      · rintro ⟨w1, _⟩ _ ⟨w2, _⟩ _ h
        exact Subtype.ext h
      · intro w hw
        rw [Finset.mem_filter] at hw
        refine ⟨⟨w, hw.1⟩, ?_, rfl⟩
        rw [mem_neighborFinset]
        exact ⟨hw.2.1.symm, hw.2.2⟩
    have h_hand := G7.sum_degrees_eq_twice_card_edges
    have h_sum21 : ∑ a : U7, G7.degree a = 21 := by
      simp [h_deg_G7, hU7_card]
    omega
  -- Now from h_w_le : ∀ k, (W_k(v)).card ≤ 6, deduce N_c(v).card = 3 and W_c(v).card = 6!
  have hNW : ∀ k : Fin 3,
      (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = k)).card +
      (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) ≠ k)).card = 9 := by
    intro k
    have h_union : Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = k) ∪
        Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) ≠ k) = Finset.univ.erase v := by
      ext u
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      tauto
    have h_disj : Disjoint (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = k))
        (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) ≠ k)) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rw [Finset.mem_filter] at hu1 hu2
      exact hu2.2.2 hu1.2.2
    have h_sum := Finset.card_union_of_disjoint h_disj
    rw [h_union, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV] at h_sum
    omega
  have hN_ge3 : ∀ k : Fin 3, 3 ≤ (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = k)).card := by
    intro k
    have h1 := h_w_le k
    have h2 := hNW k
    omega
  have hN_sum :
      (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 0)).card +
      (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 1)).card +
      (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 2)).card = 9 := by
    have h_u012 :
        Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 0) ∪
        Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 1) ∪
        Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 2) = Finset.univ.erase v := by
      ext u
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro huv
        generalize coloring s(v, u) = k
        fin_cases k <;> simp [huv]
    have hd01 : Disjoint (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 0))
        (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 1)) := by
      rw [Finset.disjoint_left]; intro u h0 h1
      rw [Finset.mem_filter] at h0 h1
      have := h0.2.2.symm.trans h1.2.2; revert this; decide
    have hd01_2 : Disjoint
        (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 0) ∪
         Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 1))
        (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 2)) := by
      rw [Finset.disjoint_left]; intro u h01 h2
      simp only [Finset.mem_union, Finset.mem_filter] at h01 h2
      rcases h01 with h0 | h1
      · have := h0.2.2.symm.trans h2.2.2; revert this; decide
      · have := h1.2.2.symm.trans h2.2.2; revert this; decide
    rw [← Finset.card_union_of_disjoint hd01, ← Finset.card_union_of_disjoint hd01_2,
        h_u012, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV]
  have h0 := hN_ge3 0
  have h1 := hN_ge3 1
  have h2 := hN_ge3 2
  have hNc : (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = c)).card = 3 := by
    fin_cases c
    · change (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 0)).card = 3; omega
    · change (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 1)).card = 3; omega
    · change (Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) = 2)).card = 3; omega
  have hWc := hNW c
  exact ⟨hNc, by omega⟩

private lemma exists_triangle_of_bal {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 10)
    (coloring : Sym2 V → Fin 3)
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k) :
    ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      coloring s(x, y) = 0 ∧ coloring s(x, z) = 0 ∧ coloring s(y, z) = 0 := by
  have hne : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by rw [Finset.card_univ, hV]; decide)
  obtain ⟨v, _⟩ := hne
  let U := Finset.univ.filter (fun u => u ≠ v ∧ coloring s(v, u) ≠ 0)
  have hU : ∀ u ∈ U, u ≠ v ∧ coloring s(v, u) ≠ 0 := fun u hu => (Finset.mem_filter.mp hu).2
  have hU_card : U.card = 6 := (w_card_eq_six_and_deg_three hV coloring hbal 0 v).2
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  let N_u := U.filter (fun w => w ≠ u ∧ coloring s(u, w) = 0)
  let M_u := U.filter (fun w => w ≠ u ∧ coloring s(u, w) ≠ 0)
  have h_union : N_u ∪ M_u = U.erase u := by
    ext w; simp only [N_u, M_u, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]; tauto
  have h_disj : Disjoint N_u M_u := by
    rw [Finset.disjoint_left]; intro w hw1 hw2
    simp only [N_u, M_u, Finset.mem_filter] at hw1 hw2
    exact hw2.2.2 hw1.2.2
  have h_sum : N_u.card + M_u.card = 5 := by
    have := Finset.card_union_of_disjoint h_disj
    rw [h_union, Finset.card_erase_of_mem hu, hU_card] at this
    omega
  by_cases hN3 : 3 ≤ N_u.card
  · obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hN3
    rw [Finset.card_eq_three] at hT_card
    obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := hT_card
    have ha := Finset.mem_filter.mp (hT_sub (by simp : a ∈ ({a, b, d} : Finset V)))
    have hb := Finset.mem_filter.mp (hT_sub (by simp : b ∈ ({a, b, d} : Finset V)))
    have hd := Finset.mem_filter.mp (hT_sub (by simp : d ∈ ({a, b, d} : Finset V)))
    rcases w_edge_of_three coloring hbal 0 v (hU a ha.1) (hU b hb.1) (hU d hd.1) hab had hbd with h1 | h2 | h3
    · exact ⟨u, a, b, ha.2.1.symm, hb.2.1.symm, hab, ha.2.2, hb.2.2, h1⟩
    · exact ⟨u, a, d, ha.2.1.symm, hd.2.1.symm, had, ha.2.2, hd.2.2, h2⟩
    · exact ⟨u, b, d, hb.2.1.symm, hd.2.1.symm, hbd, hb.2.2, hd.2.2, h3⟩
  · have hM3 : 3 ≤ M_u.card := by omega
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hM3
    rw [Finset.card_eq_three] at hT_card
    obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := hT_card
    have ha := Finset.mem_filter.mp (hT_sub (by simp : a ∈ ({a, b, d} : Finset V)))
    have hb := Finset.mem_filter.mp (hT_sub (by simp : b ∈ ({a, b, d} : Finset V)))
    have hd := Finset.mem_filter.mp (hT_sub (by simp : d ∈ ({a, b, d} : Finset V)))
    have h_edge : ∀ p q : V, (p ∈ U ∧ (p ≠ u ∧ coloring s(u, p) ≠ 0)) →
        (q ∈ U ∧ (q ≠ u ∧ coloring s(u, q) ≠ 0)) → p ≠ q → coloring s(p, q) = 0 := by
      intro p q hp hq hpq
      rcases w_edge_of_three coloring hbal 0 v (hU u hu) (hU p hp.1) (hU q hq.1)
        hp.2.1.symm hq.2.1.symm hpq with h1 | h2 | h3
      · exfalso; exact hp.2.2 h1
      · exfalso; exact hq.2.2 h2
      · exact h3
    exact ⟨a, b, d, hab, had, hbd, h_edge a b ha hb hab, h_edge a d ha hd had, h_edge b d hb hd hbd⟩

theorem erdos_617.variants.r_eq_3 (r : ℕ) (_hr : r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 3^2 + 1) (coloring : Sym2 V → Fin 3) :
    ∃ (S : Finset V) (k : Fin 3),
      S.card = 3 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  by_contra hcon
  push Not at hcon
  have hV10 : Fintype.card V = 10 := hV
  obtain ⟨x, y, z, hxy, hxz, hyz, exy, exz, eyz⟩ := exists_triangle_of_bal hV10 coloring hcon
  -- Helper: for any vertex p of a 0-triangle {p, q, s}, there is a unique 3rd neighbor a of p in color 0,
  -- and a is NOT adjacent in color 0 to q or s!
  have h_third_nb : ∀ p q t : V, p ≠ q → p ≠ t → q ≠ t →
      coloring s(p, q) = 0 → coloring s(p, t) = 0 → coloring s(q, t) = 0 →
      ∃ a : V, a ≠ p ∧ a ≠ q ∧ a ≠ t ∧ coloring s(p, a) = 0 ∧
        coloring s(q, a) ≠ 0 ∧ coloring s(t, a) ≠ 0 ∧
        Finset.univ.filter (fun u => u ≠ p ∧ coloring s(p, u) = 0) = {q, t, a} := by
    intro p q t hpq hpt hqt epq ept eqt
    let Np := Finset.univ.filter (fun u => u ≠ p ∧ coloring s(p, u) = 0)
    have hNp_card : Np.card = 3 := (w_card_eq_six_and_deg_three hV10 coloring hcon 0 p).1
    have hq_in : q ∈ Np := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hpq.symm, epq⟩
    have ht_in : t ∈ Np := Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt.symm, ept⟩
    have hqt_sub : ({q, t} : Finset V) ⊆ Np := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    have h_sdiff_card : (Np \ {q, t}).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hqt_sub, hNp_card,
          Finset.card_pair hqt]
    obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp h_sdiff_card
    have ha_mem : a ∈ Np \ {q, t} := ha_eq ▸ Finset.mem_singleton_self a
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, not_or] at ha_mem
    have hqa_ne0 : coloring s(q, a) ≠ 0 := by
      intro hqa0
      exact no_five_edges_in_four coloring hcon 0 hpq hpt ha_mem.1.2.1.symm
        hqt (Ne.symm ha_mem.2.1) (Ne.symm ha_mem.2.2) epq ept ha_mem.1.2.2 eqt hqa0
    have hta_ne0 : coloring s(t, a) ≠ 0 := by
      intro hta0
      exact no_five_edges_in_four coloring hcon 0 hpt hpq ha_mem.1.2.1.symm
        hqt.symm (Ne.symm ha_mem.2.2) (Ne.symm ha_mem.2.1) ept epq ha_mem.1.2.2
        (by rw [Sym2.eq_swap]; exact eqt) hta0
    refine ⟨a, ha_mem.1.2.1, ha_mem.2.1, ha_mem.2.2, ha_mem.1.2.2, hqa_ne0, hta_ne0, ?_⟩
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hu
      by_cases hu_qt : u ∈ ({q, t} : Finset V)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hu_qt
        rcases hu_qt with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have hu_sdiff : u ∈ Np \ {q, t} := Finset.mem_sdiff.mpr ⟨hu, hu_qt⟩
        rw [ha_eq, Finset.mem_singleton] at hu_sdiff
        exact Or.inr (Or.inr hu_sdiff)
    · rintro (rfl | rfl | rfl)
      · exact hq_in
      · exact ht_in
      · exact Finset.mem_filter.mpr ha_mem.1
  obtain ⟨a, hax, hay, haz, exa, eya, eza, hNx⟩ := h_third_nb x y z hxy hxz hyz exy exz eyz
  obtain ⟨b, hby, hbx, hbz, eyb, exb, ezb, hNy⟩ :=
    h_third_nb y x z hxy.symm hyz hxz (by rw [Sym2.eq_swap]; exact exy) eyz exz
  obtain ⟨c, hcz, hcx, hcy, ezc, exc, eyc, hNz⟩ :=
    h_third_nb z x y hxz.symm hyz.symm hxy (by rw [Sym2.eq_swap]; exact exz) (by rw [Sym2.eq_swap]; exact eyz) exy
  have hab : a ≠ b := by intro h; subst h; exact eya eyb
  have hac : a ≠ c := by intro h; subst h; exact eza ezc
  have hbc : b ≠ c := by intro h; subst h; exact ezb ezc
  have h_nb_sub_W : ∀ q p q_nb : V,
      p ≠ q → coloring s(q, p) ≠ 0 →
      q_nb ≠ p → coloring s(p, q_nb) = 0 →
      (q_nb = q ∨ coloring s(q, q_nb) = 0) →
      ∀ w : V, w ≠ p → w ≠ q_nb → coloring s(p, w) = 0 → (w ≠ q ∧ coloring s(q, w) ≠ 0) := by
    intro q p q_nb hpq eqp hqnb ep_qnb hqnb_not_W w hwp hw_qnb epw
    set Wq := Finset.univ.filter (fun u => u ≠ q ∧ coloring s(q, u) ≠ 0)
    have hWq : ∀ u ∈ Wq, u ≠ q ∧ coloring s(q, u) ≠ 0 := fun u hu => (Finset.mem_filter.mp hu).2
    have hWq_card : Wq.card = 6 := (w_card_eq_six_and_deg_three hV10 coloring hcon 0 q).2
    have hp_Wq : p ∈ Wq := Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpq, eqp⟩
    have h_non_le3 := w_nonneighbors_le_three coloring hcon 0 q Wq hWq p hp_Wq
    set Np_W := Wq.filter (fun u => u ≠ p ∧ coloring s(p, u) = 0)
    set Mp_W := Wq.filter (fun u => u ≠ p ∧ coloring s(p, u) ≠ 0)
    have h_u : Np_W ∪ Mp_W = Wq.erase p := by
      ext u; simp only [Np_W, Mp_W, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]; tauto
    have h_d : Disjoint Np_W Mp_W := by
      rw [Finset.disjoint_left]; intro u h1 h2
      simp only [Np_W, Mp_W, Finset.mem_filter] at h1 h2; exact h2.2.2 h1.2.2
    have h_Np_W_ge2 : 2 ≤ Np_W.card := by
      have := Finset.card_union_of_disjoint h_d
      rw [h_u, Finset.card_erase_of_mem hp_Wq, hWq_card] at this
      omega
    set Np := Finset.univ.filter (fun u => u ≠ p ∧ coloring s(p, u) = 0)
    have hNp_card : Np.card = 3 := (w_card_eq_six_and_deg_three hV10 coloring hcon 0 p).1
    have h_sub : insert q_nb Np_W ⊆ Np := by
      intro u hu
      rw [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hqnb, ep_qnb⟩
      · rw [Finset.mem_filter] at hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu.2⟩
    have hqnb_not_in : q_nb ∉ Np_W := by
      intro hmem
      have h1 := (Finset.mem_filter.mp hmem).1
      rw [Finset.mem_filter] at h1
      rcases hqnb_not_W with rfl | h0
      · exact h1.2.1 rfl
      · exact h1.2.2 h0
    have h_eq : insert q_nb Np_W = Np := by
      refine Finset.eq_of_subset_of_card_le h_sub ?_
      rw [Finset.card_insert_of_notMem hqnb_not_in, hNp_card]
      omega
    have hw_Np : w ∈ Np := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwp, epw⟩
    rw [← h_eq, Finset.mem_insert] at hw_Np
    rcases hw_Np with rfl | hw_W
    · exfalso; exact hw_qnb rfl
    · exact hWq w (Finset.mem_filter.mp hw_W).1
  have eba_ne0 : coloring s(b, a) ≠ 0 := by
    intro h0
    have := h_nb_sub_W x b y hbx exb hby.symm (by rw [Sym2.eq_swap]; exact eyb) (Or.inr exy) a hab hay h0
    exact this.2 exa
  have ebc_ne0 : coloring s(b, c) ≠ 0 := by
    intro h0
    have := h_nb_sub_W z b y hbz ezb hby.symm (by rw [Sym2.eq_swap]; exact eyb) (Or.inr (by rw [Sym2.eq_swap]; exact eyz)) c hbc.symm hcy h0
    exact this.2 ezc
  have eac_ne0 : coloring s(a, c) ≠ 0 := by
    intro h0
    have := h_nb_sub_W z a x haz eza hax.symm (by rw [Sym2.eq_swap]; exact exa) (Or.inr (by rw [Sym2.eq_swap]; exact exz)) c hac.symm hcx h0
    exact this.2 ezc
  set S6 : Finset V := {x, y, z, a, b, c}
  have hS6_card : S6.card = 6 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hbc]
    · simp [hab, hac]
    · simp [haz.symm, hbz.symm, hcz.symm]
    · simp [hyz, hay.symm, hby.symm, hcy.symm]
    · simp [hxy, hxz, hax.symm, hbx.symm, hcx.symm]
  set R : Finset V := Finset.univ \ S6
  have hR_card : R.card = 4 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ S6),
        Finset.card_univ, hV10, hS6_card]
  have hR_mem : ∀ r ∈ R, r ≠ x ∧ r ≠ y ∧ r ≠ z ∧ r ≠ a ∧ r ≠ b ∧ r ≠ c ∧
      coloring s(x, r) ≠ 0 ∧ coloring s(y, r) ≠ 0 ∧ coloring s(z, r) ≠ 0 := by
    intro r hr
    rw [Finset.mem_sdiff] at hr
    have hnot : r ∉ ({x, y, z, a, b, c} : Finset V) := hr.2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    rcases hnot with ⟨hrx, hry, hrz, hra, hrb, hrc⟩
    have hxr0 : coloring s(x, r) ≠ 0 := by
      intro h0
      have h_in : r ∈ Finset.univ.filter (fun u => u ≠ x ∧ coloring s(x, u) = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ r, hrx, h0⟩
      rw [hNx, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h_in
      rcases h_in with rfl | rfl | rfl
      · exact hry rfl
      · exact hrz rfl
      · exact hra rfl
    have hyr0 : coloring s(y, r) ≠ 0 := by
      intro h0
      have h_in : r ∈ Finset.univ.filter (fun u => u ≠ y ∧ coloring s(y, u) = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ r, hry, h0⟩
      rw [hNy, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h_in
      rcases h_in with rfl | rfl | rfl
      · exact hrx rfl
      · exact hrz rfl
      · exact hrb rfl
    have hzr0 : coloring s(z, r) ≠ 0 := by
      intro h0
      have h_in : r ∈ Finset.univ.filter (fun u => u ≠ z ∧ coloring s(z, u) = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ r, hrz, h0⟩
      rw [hNz, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h_in
      rcases h_in with rfl | rfl | rfl
      · exact hrx rfl
      · exact hry rfl
      · exact hrc rfl
    exact ⟨hrx, hry, hrz, hra, hrb, hrc, hxr0, hyr0, hzr0⟩
  -- Define A, B, C ⊆ R:
  set A := R.filter (fun r => coloring s(a, r) = 0)
  set B := R.filter (fun r => coloring s(b, r) = 0)
  set C := R.filter (fun r => coloring s(c, r) = 0)
  have h_card_le2 : ∀ p p_nb : V, p_nb ≠ p → coloring s(p, p_nb) = 0 →
      p_nb ∉ R → (∀ r ∈ R, r ≠ p) → (R.filter (fun r => coloring s(p, r) = 0)).card ≤ 2 := by
    intro p p_nb hpnb ep_pnb hpnb_not_R hR_ne_p
    let Np := Finset.univ.filter (fun u => u ≠ p ∧ coloring s(p, u) = 0)
    have hNp_card : Np.card = 3 := (w_card_eq_six_and_deg_three hV10 coloring hcon 0 p).1
    have h_sub : insert p_nb (R.filter (fun r => coloring s(p, r) = 0)) ⊆ Np := by
      intro u hu
      rw [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hpnb, ep_pnb⟩
      · rw [Finset.mem_filter] at hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hR_ne_p u hu.1, hu.2⟩
    have hpnb_not_in : p_nb ∉ R.filter (fun r => coloring s(p, r) = 0) := by
      intro hmem
      exact hpnb_not_R (Finset.mem_filter.mp hmem).1
    have hle := Finset.card_le_card h_sub
    rw [Finset.card_insert_of_notMem hpnb_not_in, hNp_card] at hle
    omega
  have hA_le2 : A.card ≤ 2 := h_card_le2 a x hax.symm (by rw [Sym2.eq_swap]; exact exa)
    (fun h => (hR_mem x h).1 rfl) (fun r hr => (hR_mem r hr).2.2.2.1)
  have hB_le2 : B.card ≤ 2 := h_card_le2 b y hby.symm (by rw [Sym2.eq_swap]; exact eyb)
    (fun h => (hR_mem y h).2.1 rfl) (fun r hr => (hR_mem r hr).2.2.2.2.1)
  have hC_le2 : C.card ≤ 2 := h_card_le2 c z hcz.symm (by rw [Sym2.eq_swap]; exact ezc)
    (fun h => (hR_mem z h).2.2.1 rfl) (fun r hr => (hR_mem r hr).2.2.2.2.2.1)
  -- R \ B ⊆ A (by w_edge_of_three on {b, a, r} in W_0(z))!
  have hRB_sub_A : R \ B ⊆ A := by
    intro r hr
    rw [Finset.mem_sdiff, Finset.mem_filter, not_and] at hr
    have hrm := hR_mem r hr.1
    have hbr_ne0 : coloring s(b, r) ≠ 0 := hr.2 hr.1
    rcases w_edge_of_three coloring hcon 0 z ⟨hbz, ezb⟩ ⟨haz, eza⟩ ⟨hrm.2.2.1, hrm.2.2.2.2.2.2.2.2⟩
      hab.symm (Ne.symm hrm.2.2.2.2.1) (Ne.symm hrm.2.2.2.1) with h1 | h2 | h3
    · exfalso; exact eba_ne0 h1
    · exfalso; exact hbr_ne0 h2
    · exact Finset.mem_filter.mpr ⟨hr.1, h3⟩
  -- R \ B ⊆ C (by w_edge_of_three on {b, c, r} in W_0(x))!
  have hRB_sub_C : R \ B ⊆ C := by
    intro r hr
    rw [Finset.mem_sdiff, Finset.mem_filter, not_and] at hr
    have hrm := hR_mem r hr.1
    have hbr_ne0 : coloring s(b, r) ≠ 0 := hr.2 hr.1
    rcases w_edge_of_three coloring hcon 0 x ⟨hbx, exb⟩ ⟨hcx, exc⟩ ⟨hrm.1, hrm.2.2.2.2.2.2.1⟩
      hbc (Ne.symm hrm.2.2.2.2.1) (Ne.symm hrm.2.2.2.2.2.1) with h1 | h2 | h3
    · exfalso; exact ebc_ne0 h1
    · exfalso; exact hbr_ne0 h2
    · exact Finset.mem_filter.mpr ⟨hr.1, h3⟩
  -- R \ A ⊆ C (by w_edge_of_three on {a, c, r} in W_0(y))!
  have hRA_sub_C : R \ A ⊆ C := by
    intro r hr
    rw [Finset.mem_sdiff, Finset.mem_filter, not_and] at hr
    have hrm := hR_mem r hr.1
    have har_ne0 : coloring s(a, r) ≠ 0 := hr.2 hr.1
    rcases w_edge_of_three coloring hcon 0 y ⟨hay, eya⟩ ⟨hcy, eyc⟩ ⟨hrm.2.1, hrm.2.2.2.2.2.2.2.1⟩
      hac (Ne.symm hrm.2.2.2.1) (Ne.symm hrm.2.2.2.2.2.1) with h1 | h2 | h3
    · exfalso; exact eac_ne0 h1
    · exfalso; exact har_ne0 h2
    · exact Finset.mem_filter.mpr ⟨hr.1, h3⟩
  -- Since B ⊆ R and B.card ≤ 2 and R.card = 4, (R \ B).card ≥ 2.
  -- Since R \ B ⊆ A and A.card ≤ 2, we have R \ B = A!
  have hRB_eq_A : R \ B = A := by
    refine Finset.eq_of_subset_of_card_le hRB_sub_A ?_
    have h_sdiff : (R \ B).card + B.card = R.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun r => coloring s(b, r) = 0) R)
    omega
  -- Therefore R ⊆ C!
  have hR_sub_C : R ⊆ C := by
    intro r hr
    by_cases hrB : r ∈ B
    · have hr_not_RB : r ∉ R \ B := fun h => (Finset.mem_sdiff.mp h).2 hrB
      rw [hRB_eq_A] at hr_not_RB
      exact hRA_sub_C (Finset.mem_sdiff.mpr ⟨hr, hr_not_RB⟩)
    · exact hRB_sub_C (Finset.mem_sdiff.mpr ⟨hr, hrB⟩)
  have hR_le_C := Finset.card_le_card hR_sub_C
  omega

end Erdos617

namespace Erdos628

open SimpleGraph

private lemma not_colorable_two_iff_odd_loop {V : Type*} {G : SimpleGraph V} :
    ¬G.Colorable 2 ↔ ∃ (u : V) (w : G.Walk u u), Odd w.length := by
  rw [two_colorable_iff_forall_loop_even]
  push Not
  simp only [Nat.not_even_iff_odd]

private lemma three_le_chromaticNumber_iff_not_colorable_two {V : Type*} {G : SimpleGraph V} :
    (3 : ℕ∞) ≤ G.chromaticNumber ↔ ¬G.Colorable 2 := by
  constructor
  · intro h3 hcol
    have h2 : G.chromaticNumber ≤ 2 := hcol.chromaticNumber_le
    exact absurd (le_trans h3 h2) (by decide)
  · intro hnot
    by_contra hlt
    push Not at hlt
    have hle : G.chromaticNumber ≤ 2 := Order.le_of_lt_add_one hlt
    exact hnot (chromaticNumber_le_iff_colorable.mp hle)

/-- A cyclic sequence of `n` vertices in `G` where consecutive vertices (modulo `n`) are adjacent. -/
private def IsCyclicWalk {V : Type*} (G : SimpleGraph V) (n : ℕ) (f : ℕ → V) : Prop :=
  (∀ i : ℕ, f (i + n) = f i) ∧ ∀ i : ℕ, G.Adj (f i) (f (i + 1))

private lemma exists_odd_cyclicWalk_of_not_colorable_two {V : Type*} {G : SimpleGraph V}
    (hnot : ¬G.Colorable 2) :
    ∃ m : ℕ, ∃ f : ℕ → V, IsCyclicWalk G (2 * m + 1) f := by
  rw [not_colorable_two_iff_odd_loop] at hnot
  obtain ⟨u, w, m, hm⟩ := hnot
  have hlen : 0 < 2 * m + 1 := by omega
  refine ⟨m, fun i => w.getVert (i % (2 * m + 1)), ?_, ?_⟩
  · intro i
    dsimp only
    rw [Nat.add_mod_right]
  · intro i
    dsimp only
    have hlt : i % (2 * m + 1) < 2 * m + 1 := Nat.mod_lt i hlen
    by_cases hlast : i % (2 * m + 1) + 1 = 2 * m + 1
    · have hmod : (i + 1) % (2 * m + 1) = 0 := by
        rw [← Nat.mod_add_div i (2 * m + 1)]
        have : i % (2 * m + 1) + (2 * m + 1) * (i / (2 * m + 1)) + 1 =
            (2 * m + 1) * (i / (2 * m + 1) + 1) := by linarith
        rw [this, Nat.mul_mod_right]
      have h_adj := w.adj_getVert_succ (i := i % (2 * m + 1)) (by omega)
      have h_end : w.getVert (i % (2 * m + 1) + 1) = u := by
        rw [hlast, ← hm, Walk.getVert_length w]
      rw [h_end] at h_adj
      rw [hmod, Walk.getVert_zero]
      exact h_adj
    · have hmod : (i + 1) % (2 * m + 1) = i % (2 * m + 1) + 1 := by
        have h1 : (i + 1) % (2 * m + 1) = (i % (2 * m + 1) + 1) % (2 * m + 1) := by
          conv_lhs => rw [← Nat.mod_add_div i (2 * m + 1)]
          have : i % (2 * m + 1) + (2 * m + 1) * (i / (2 * m + 1)) + 1 =
              (i % (2 * m + 1) + 1) + (2 * m + 1) * (i / (2 * m + 1)) := by ring
          rw [this, Nat.add_mul_mod_self_left]
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact w.adj_getVert_succ (by omega)

private lemma not_colorable_two_induce_of_odd_cyclicWalk {V : Type*} {G : SimpleGraph V}
    {m : ℕ} {f : ℕ → V} (hf : IsCyclicWalk G (2 * m + 1) f)
    {s : Set V} (hs : ∀ i : ℕ, f i ∈ s) :
    ¬(G.induce s).Colorable 2 := by
  rintro ⟨c⟩
  have h_step : ∀ i : ℕ, (c ⟨f (i + 1), hs (i + 1)⟩).val = 1 - (c ⟨f i, hs i⟩).val := by
    intro i
    have hne : c ⟨f i, hs i⟩ ≠ c ⟨f (i + 1), hs (i + 1)⟩ := c.valid (hf.2 i)
    have h1 := (c ⟨f i, hs i⟩).isLt
    have h2 := (c ⟨f (i + 1), hs (i + 1)⟩).isLt
    have hne_val : (c ⟨f i, hs i⟩).val ≠ (c ⟨f (i + 1), hs (i + 1)⟩).val :=
      fun h => hne (Fin.ext h)
    omega
  have h_parity : ∀ k : ℕ, (c ⟨f k, hs k⟩).val % 2 = ((c ⟨f 0, hs 0⟩).val + k) % 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs_k := h_step k
      have hlt := (c ⟨f k, hs k⟩).isLt
      omega
  have h_end := h_parity (2 * m + 1)
  have h_eq : (⟨f (2 * m + 1), hs (2 * m + 1)⟩ : s) = ⟨f 0, hs 0⟩ := by
    ext
    simpa using hf.1 0
  rw [h_eq] at h_end
  omega

private lemma isCyclicWalk_shift {V : Type*} {G : SimpleGraph V} {n : ℕ} {f : ℕ → V}
    (hf : IsCyclicWalk G n f) (a : ℕ) : IsCyclicWalk G n (fun t => f (a + t)) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · dsimp only
    rw [← add_assoc, hf.1 (a + t)]
  · dsimp only
    rw [← add_assoc]
    exact hf.2 (a + t)

private lemma isCyclicWalk_periodic_mul {V : Type*} {G : SimpleGraph V} {n : ℕ} {f : ℕ → V}
    (hf : IsCyclicWalk G n f) (i q : ℕ) : f (i + n * q) = f i := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : i + n * (q + 1) = (i + n * q) + n := by ring
    rw [this, hf.1, ih]

private lemma isCyclicWalk_eq_mod {V : Type*} {G : SimpleGraph V} {n : ℕ} {f : ℕ → V}
    (hf : IsCyclicWalk G n f) (i : ℕ) : f (i % n) = f i := by
  have h := isCyclicWalk_periodic_mul hf (i % n) (i / n)
  rw [Nat.mod_add_div] at h
  exact h.symm

private lemma isCyclicWalk_shortcut_of_eq {V : Type*} {G : SimpleGraph V} {n : ℕ} {f : ℕ → V}
    (hf : IsCyclicWalk G n f) {d : ℕ} (hd : 0 < d) (heq : f d = f 0) :
    IsCyclicWalk G d (fun t => f (t % d)) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · dsimp only
    rw [Nat.add_mod_right]
  · dsimp only
    have hlt : t % d < d := Nat.mod_lt t hd
    by_cases hlast : t % d + 1 = d
    · have hmod : (t + 1) % d = 0 := by
        rw [← Nat.mod_add_div t d]
        have : t % d + d * (t / d) + 1 = d * (t / d + 1) := by linarith
        rw [this, Nat.mul_mod_right]
      have hadj := hf.2 (t % d)
      rw [hlast, heq] at hadj
      rw [hmod]
      exact hadj
    · have hmod : (t + 1) % d = t % d + 1 := by
        have h1 : (t + 1) % d = (t % d + 1) % d := by
          conv_lhs => rw [← Nat.mod_add_div t d]
          have : t % d + d * (t / d) + 1 = (t % d + 1) + d * (t / d) := by ring
          rw [this, Nat.add_mul_mod_self_left]
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact hf.2 (t % d)

private lemma isCyclicWalk_shortcut_of_adj {V : Type*} {G : SimpleGraph V} {n : ℕ} {f : ℕ → V}
    (hf : IsCyclicWalk G n f) {d : ℕ} (hadj : G.Adj (f d) (f 0)) :
    IsCyclicWalk G (d + 1) (fun t => f (t % (d + 1))) := by
  have hd1 : 0 < d + 1 := by omega
  refine ⟨fun t => ?_, fun t => ?_⟩
  · dsimp only
    rw [Nat.add_mod_right]
  · dsimp only
    have hlt : t % (d + 1) < d + 1 := Nat.mod_lt t hd1
    by_cases hlast : t % (d + 1) = d
    · have hmod : (t + 1) % (d + 1) = 0 := by
        rw [← Nat.mod_add_div t (d + 1)]
        have : t % (d + 1) + (d + 1) * (t / (d + 1)) + 1 = (d + 1) * (t / (d + 1) + 1) := by linarith
        rw [this, Nat.mul_mod_right]
      rw [hmod, hlast]
      exact hadj
    · have hmod : (t + 1) % (d + 1) = t % (d + 1) + 1 := by
        have h1 : (t + 1) % (d + 1) = (t % (d + 1) + 1) % (d + 1) := by
          conv_lhs => rw [← Nat.mod_add_div t (d + 1)]
          have : t % (d + 1) + (d + 1) * (t / (d + 1)) + 1 = (t % (d + 1) + 1) + (d + 1) * (t / (d + 1)) := by ring
          rw [this, Nat.add_mul_mod_self_left]
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact hf.2 (t % (d + 1))

open scoped Classical in
private lemma exists_min_odd_cyclicWalk {V : Type*} {G : SimpleGraph V}
    (hnot : ¬G.Colorable 2) :
    ∃ m : ℕ, ∃ f : ℕ → V, IsCyclicWalk G (2 * m + 1) f ∧
      ∀ m' < m, ∀ g : ℕ → V, ¬IsCyclicWalk G (2 * m' + 1) g := by
  have hex := exists_odd_cyclicWalk_of_not_colorable_two hnot
  let m := Nat.find hex
  obtain ⟨f, hf⟩ := Nat.find_spec hex
  refine ⟨m, f, hf, fun m' hm' g hg => ?_⟩
  exact Nat.find_min hex hm' ⟨g, hg⟩

private lemma min_odd_cyclicWalk_inj {V : Type*} {G : SimpleGraph V}
    {m : ℕ} {f : ℕ → V} (hf : IsCyclicWalk G (2 * m + 1) f)
    (hmin : ∀ m' < m, ∀ g : ℕ → V, ¬IsCyclicWalk G (2 * m' + 1) g)
    {i j : ℕ} (_hi : i < 2 * m + 1) (hj : j < 2 * m + 1) (hij : i < j) :
    f i ≠ f j := by
  intro heq
  let d := j - i
  have hd_pos : 0 < d := by omega
  have hd_lt : d < 2 * m + 1 := by omega
  by_cases hd_odd : d % 2 = 1
  · let m' := d / 2
    have hm'_eq : 2 * m' + 1 = d := by omega
    have hm'_lt : m' < m := by omega
    have hshift := isCyclicWalk_shift hf i
    have heq1 : (fun t => f (i + t)) (2 * m' + 1) = (fun t => f (i + t)) 0 := by
      dsimp only
      rw [hm'_eq, add_zero, show i + d = j by omega, heq]
    exact hmin m' hm'_lt _ (isCyclicWalk_shortcut_of_eq hshift (by omega) heq1)
  · let d2 := (2 * m + 1) - d
    let m' := d2 / 2
    have hm'_eq : 2 * m' + 1 = d2 := by omega
    have hm'_lt : m' < m := by omega
    have hshift := isCyclicWalk_shift hf j
    have heq2 : (fun t => f (j + t)) (2 * m' + 1) = (fun t => f (j + t)) 0 := by
      dsimp only
      have hjd2 : j + (2 * m' + 1) = i + (2 * m + 1) := by omega
      rw [hjd2, hf.1 i, add_zero, heq]
    exact hmin m' hm'_lt _ (isCyclicWalk_shortcut_of_eq hshift (by omega) heq2)

private lemma min_odd_cyclicWalk_adj_iff {V : Type*} {G : SimpleGraph V}
    {m : ℕ} {f : ℕ → V} (hf : IsCyclicWalk G (2 * m + 1) f)
    (hmin : ∀ m' < m, ∀ g : ℕ → V, ¬IsCyclicWalk G (2 * m' + 1) g)
    {i j : ℕ} (_hi : i < 2 * m + 1) (hj : j < 2 * m + 1) (hij : i < j)
    (hadj : G.Adj (f i) (f j)) :
    j = i + 1 ∨ (i = 0 ∧ j = 2 * m) := by
  by_contra hnot
  let d := j - i
  have hd_ge2 : 2 ≤ d := by omega
  have hd_lt : d < 2 * m := by omega
  by_cases hd_even : d % 2 = 0
  · let m' := d / 2
    have hm'_eq : 2 * m' = d := by omega
    have hm'_lt : m' < m := by omega
    have hshift := isCyclicWalk_shift hf i
    have hadj1 : G.Adj ((fun t => f (i + t)) (2 * m')) ((fun t => f (i + t)) 0) := by
      dsimp only
      rw [hm'_eq, add_zero, show i + d = j by omega]
      exact hadj.symm
    exact hmin m' hm'_lt _ (isCyclicWalk_shortcut_of_adj hshift hadj1)
  · let d2 := (2 * m + 1) - d
    let m' := d2 / 2
    have hm'_eq : 2 * m' = d2 := by omega
    have hm'_lt : m' < m := by omega
    have hshift := isCyclicWalk_shift hf j
    have hadj2 : G.Adj ((fun t => f (j + t)) (2 * m')) ((fun t => f (j + t)) 0) := by
      dsimp only
      have hjd2 : j + 2 * m' = i + (2 * m + 1) := by omega
      rw [hjd2, hf.1 i, add_zero]
      exact hadj
    exact hmin m' hm'_lt _ (isCyclicWalk_shortcut_of_adj hshift hadj2)

private lemma isCyclicWalk_shortcut_via_external {V : Type*} {G : SimpleGraph V} {n : ℕ} {f : ℕ → V}
    (hf : IsCyclicWalk G n f) (v : V) {d : ℕ} (hd : 0 < d)
    (h0 : G.Adj v (f 0)) (hd_adj : G.Adj (f d) v) :
    IsCyclicWalk G (d + 2) (fun t => if t % (d + 2) = 0 then v else f (t % (d + 2) - 1)) := by
  have hd2 : 0 < d + 2 := by omega
  refine ⟨fun t => ?_, fun t => ?_⟩
  · dsimp only
    rw [Nat.add_mod_right]
  · dsimp only
    have hlt : t % (d + 2) < d + 2 := Nat.mod_lt t hd2
    by_cases hlast : t % (d + 2) = d + 1
    · have hmod : (t + 1) % (d + 2) = 0 := by
        rw [← Nat.mod_add_div t (d + 2)]
        have : t % (d + 2) + (d + 2) * (t / (d + 2)) + 1 = (d + 2) * (t / (d + 2) + 1) := by linarith
        rw [this, Nat.mul_mod_right]
      rw [hlast, if_neg (by omega), hmod, if_pos rfl, show d + 1 - 1 = d by omega]
      exact hd_adj
    · have hmod : (t + 1) % (d + 2) = t % (d + 2) + 1 := by
        have h1 : (t + 1) % (d + 2) = (t % (d + 2) + 1) % (d + 2) := by
          conv_lhs => rw [← Nat.mod_add_div t (d + 2)]
          have : t % (d + 2) + (d + 2) * (t / (d + 2)) + 1 = (t % (d + 2) + 1) + (d + 2) * (t / (d + 2)) := by ring
          rw [this, Nat.add_mul_mod_self_left]
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      by_cases ht0 : t % (d + 2) = 0
      · rw [ht0]
        simp [h0]
      · rw [if_neg ht0, if_neg (by omega), show t % (d + 2) + 1 - 1 = (t % (d + 2) - 1) + 1 by omega]
        exact hf.2 (t % (d + 2) - 1)

private lemma min_odd_cyclicWalk_external_le_two {V : Type*} {G : SimpleGraph V}
    {m : ℕ} {f : ℕ → V} (hf : IsCyclicWalk G (2 * m + 1) f)
    (hmin : ∀ m' < m, ∀ g : ℕ → V, ¬IsCyclicWalk G (2 * m' + 1) g)
    (hm_ge2 : 2 ≤ m)
    {v : V} {i j k : ℕ} (_hi : i < 2 * m + 1) (_hj : j < 2 * m + 1) (hk : k < 2 * m + 1)
    (hij : i < j) (hjk : j < k)
    (hvi : G.Adj v (f i)) (hvj : G.Adj v (f j)) (hvk : G.Adj v (f k)) : False := by
  let d1 := j - i
  let d2 := k - j
  let d3 := (2 * m + 1) + i - k
  have hsum : d1 + d2 + d3 = 2 * m + 1 := by omega
  have hd1_ge1 : 1 ≤ d1 := by omega
  have hd2_ge1 : 1 ≤ d2 := by omega
  have hd3_ge1 : 1 ≤ d3 := by omega
  -- Cannot have d1 = 1 ∧ d2 = 1 ∧ d3 = 1 since 2*m + 1 ≥ 5!
  -- Wait: Can d1 = 1 and d2 is odd?
  -- Notice that for ANY s ∈ {d1, d2, d3}:
  -- If s is ODD AND s ≤ 2 * m - 3, then s + 2 = 2 * m' + 1 with m' < m, giving a shorter odd cyclic walk via v!
  -- Wait: Since d1 + d2 + d3 = 2 * m + 1 (odd), either:
  -- Case 1: Only ONE of d1, d2, d3 is odd (and the other two are even, hence ≥ 2, so the odd one is ≤ (2*m + 1) - 4 = 2*m - 3)!!
  -- Case 2: ALL THREE of d1, d2, d3 are odd!
  --   Since 2*m + 1 ≥ 5 and d1 + d2 + d3 = 2*m + 1, can any of d1, d2, d3 be ≥ 2*m - 1?
  --   Only if the other two are both 1, i.e., two of d1, d2, d3 are equal to 1 (which is odd AND 1 ≤ 2*m - 3 since m ≥ 2)!!
  -- STOP!! FREEZE!! DO NOT MOVE A MUSCLE!!
  -- READ THOSE 4 LINES AGAIN!!
  -- "Since d1 + d2 + d3 = 2*m + 1 ≥ 5 and d1, d2, d3 ≥ 1:
  --  At least one of d1, d2, d3 is BOTH ODD AND ≤ 2*m - 3!!"
  have h_one_odd_small :
      (d1 % 2 = 1 ∧ d1 ≤ 2 * m - 3) ∨
      (d2 % 2 = 1 ∧ d2 ≤ 2 * m - 3) ∨
      (d3 % 2 = 1 ∧ d3 ≤ 2 * m - 3) := by omega
  rcases h_one_odd_small with ⟨h1_odd, h1_le⟩ | ⟨h2_odd, h2_le⟩ | ⟨h3_odd, h3_le⟩
  · let m' := (d1 + 1) / 2
    have hm'_eq : d1 + 2 = 2 * m' + 1 := by omega
    have hm'_lt : m' < m := by omega
    have hshift := isCyclicWalk_shift hf i
    have h0 : G.Adj v ((fun t => f (i + t)) 0) := by dsimp only; rw [add_zero]; exact hvi
    have hd : G.Adj ((fun t => f (i + t)) d1) v := by
      dsimp only; rw [show i + d1 = j by omega]; exact hvj.symm
    have hwalk := isCyclicWalk_shortcut_via_external hshift v hd1_ge1 h0 hd
    rw [hm'_eq] at hwalk
    exact hmin m' hm'_lt _ hwalk
  · let m' := (d2 + 1) / 2
    have hm'_eq : d2 + 2 = 2 * m' + 1 := by omega
    have hm'_lt : m' < m := by omega
    have hshift := isCyclicWalk_shift hf j
    have h0 : G.Adj v ((fun t => f (j + t)) 0) := by dsimp only; rw [add_zero]; exact hvj
    have hd : G.Adj ((fun t => f (j + t)) d2) v := by
      dsimp only; rw [show j + d2 = k by omega]; exact hvk.symm
    have hwalk := isCyclicWalk_shortcut_via_external hshift v hd2_ge1 h0 hd
    rw [hm'_eq] at hwalk
    exact hmin m' hm'_lt _ hwalk
  · let m' := (d3 + 1) / 2
    have hm'_eq : d3 + 2 = 2 * m' + 1 := by omega
    have hm'_lt : m' < m := by omega
    have hshift := isCyclicWalk_shift hf k
    have h0 : G.Adj v ((fun t => f (k + t)) 0) := by dsimp only; rw [add_zero]; exact hvk
    have hd : G.Adj ((fun t => f (k + t)) d3) v := by
      dsimp only; rw [show k + d3 = i + (2 * m + 1) by omega, hf.1 i]; exact hvi.symm
    have hwalk := isCyclicWalk_shortcut_via_external hshift v hd3_ge1 h0 hd
    rw [hm'_eq] at hwalk
    exact hmin m' hm'_lt _ hwalk

open scoped Classical in
private lemma colorable_four_of_min_odd_cyclicWalk {V : Type*} {G : SimpleGraph V}
    {m : ℕ} {f : ℕ → V} (hf : IsCyclicWalk G (2 * m + 1) f)
    (hmin : ∀ m' < m, ∀ g : ℕ → V, ¬IsCyclicWalk G (2 * m' + 1) g)
    (hm_ge2 : 2 ≤ m)
    (h_compl : (G.induce (Set.range f)ᶜ).Colorable 2) :
    G.Colorable 4 := by
  obtain ⟨c_bar⟩ := h_compl
  -- For any x ∈ Set.range f, choose i_x < 2 * m + 1 such that f i_x = x!
  have h_idx : ∀ x ∈ Set.range f, ∃ i < 2 * m + 1, f i = x := by
    rintro x ⟨k, rfl⟩
    exact ⟨k % (2 * m + 1), Nat.mod_lt k (by omega), isCyclicWalk_eq_mod hf k⟩
  let idx (x : V) (hx : x ∈ Set.range f) : ℕ := Classical.choose (h_idx x hx)
  have h_idx_lt (x : V) (hx : x ∈ Set.range f) : idx x hx < 2 * m + 1 :=
    (Classical.choose_spec (h_idx x hx)).1
  have h_idx_eq (x : V) (hx : x ∈ Set.range f) : f (idx x hx) = x :=
    (Classical.choose_spec (h_idx x hx)).2
  let c_C (x : V) (hx : x ∈ Set.range f) : Fin 3 :=
    ⟨if idx x hx = 2 * m then 2 else (idx x hx) % 2, by split_ifs <;> omega⟩
  have hc_C_valid : ∀ x hx y hy, G.Adj x y → c_C x hx ≠ c_C y hy := by
    intro x hx y hy hadj heq
    set i := idx x hx
    set j := idx y hy
    have hi : i < 2 * m + 1 := h_idx_lt x hx
    have hj : j < 2 * m + 1 := h_idx_lt y hy
    have hij_ne : i ≠ j := by
      intro h_eq
      have : x = y := by rw [← h_idx_eq x hx, ← h_idx_eq y hy]; exact congrArg f h_eq
      exact G.ne_of_adj hadj this
    have hadj_ij : G.Adj (f i) (f j) := by
      rw [h_idx_eq x hx, h_idx_eq y hy]; exact hadj
    have h_step : (j = i + 1 ∨ (i = 0 ∧ j = 2 * m)) ∨ (i = j + 1 ∨ (j = 0 ∧ i = 2 * m)) := by
      rcases lt_or_gt_of_ne hij_ne with hlt | hgt
      · exact Or.inl (min_odd_cyclicWalk_adj_iff hf hmin hi hj hlt hadj_ij)
      · exact Or.inr (min_odd_cyclicWalk_adj_iff hf hmin hj hi hgt hadj_ij.symm)
    have h_val : (if i = 2 * m then 2 else i % 2) = (if j = 2 * m then 2 else j % 2) :=
      congrArg Fin.val heq
    split_ifs at h_val <;> omega
  have h_ext_col : ∀ v : V, v ∉ Set.range f →
      ∃ col_v : Fin 3, ∀ x (hx : x ∈ Set.range f), G.Adj v x → c_C x hx ≠ col_v := by
    intro v _hv
    by_contra h_all
    push Not at h_all
    obtain ⟨x0, hx0, hadj0, hcol0⟩ := h_all 0
    obtain ⟨x1, hx1, hadj1, hcol1⟩ := h_all 1
    obtain ⟨x2, hx2, hadj2, hcol2⟩ := h_all 2
    set i0 := idx x0 hx0
    set i1 := idx x1 hx1
    set i2 := idx x2 hx2
    have hi0 : i0 < 2 * m + 1 := h_idx_lt x0 hx0
    have hi1 : i1 < 2 * m + 1 := h_idx_lt x1 hx1
    have hi2 : i2 < 2 * m + 1 := h_idx_lt x2 hx2
    have h_ne01 : i0 ≠ i1 := by
      intro h; have : x0 = x1 := by rw [← h_idx_eq x0 hx0, ← h_idx_eq x1 hx1]; exact congrArg f h
      subst this; have := hcol0.symm.trans hcol1; revert this; decide
    have h_ne02 : i0 ≠ i2 := by
      intro h; have : x0 = x2 := by rw [← h_idx_eq x0 hx0, ← h_idx_eq x2 hx2]; exact congrArg f h
      subst this; have := hcol0.symm.trans hcol2; revert this; decide
    have h_ne12 : i1 ≠ i2 := by
      intro h; have : x1 = x2 := by rw [← h_idx_eq x1 hx1, ← h_idx_eq x2 hx2]; exact congrArg f h
      subst this; have := hcol1.symm.trans hcol2; revert this; decide
    have hv0 : G.Adj v (f i0) := by rw [h_idx_eq x0 hx0]; exact hadj0
    have hv1 : G.Adj v (f i1) := by rw [h_idx_eq x1 hx1]; exact hadj1
    have hv2 : G.Adj v (f i2) := by rw [h_idx_eq x2 hx2]; exact hadj2
    have h_order : (i0 < i1 ∧ i1 < i2) ∨ (i0 < i2 ∧ i2 < i1) ∨
        (i1 < i0 ∧ i0 < i2) ∨ (i1 < i2 ∧ i2 < i0) ∨
        (i2 < i0 ∧ i0 < i1) ∨ (i2 < i1 ∧ i1 < i0) := by omega
    rcases h_order with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact min_odd_cyclicWalk_external_le_two hf hmin hm_ge2 hi0 hi1 hi2 h1 h2 hv0 hv1 hv2
    · exact min_odd_cyclicWalk_external_le_two hf hmin hm_ge2 hi0 hi2 hi1 h1 h2 hv0 hv2 hv1
    · exact min_odd_cyclicWalk_external_le_two hf hmin hm_ge2 hi1 hi0 hi2 h1 h2 hv1 hv0 hv2
    · exact min_odd_cyclicWalk_external_le_two hf hmin hm_ge2 hi1 hi2 hi0 h1 h2 hv1 hv2 hv0
    · exact min_odd_cyclicWalk_external_le_two hf hmin hm_ge2 hi2 hi0 hi1 h1 h2 hv2 hv0 hv1
    · exact min_odd_cyclicWalk_external_le_two hf hmin hm_ge2 hi2 hi1 hi0 h1 h2 hv2 hv1 hv0
  let col4 (u : V) : Fin 4 :=
    ⟨if hu : u ∈ Set.range f then
      (c_C u hu).val
    else if (c_bar ⟨u, hu⟩).val = 0 then
      (Classical.choose (h_ext_col u hu)).val
    else
      3, by
      split_ifs with hu hb
      · have := (c_C u hu).isLt; omega
      · have := (Classical.choose (h_ext_col u hu)).isLt; omega
      · omega⟩
  refine ⟨Coloring.mk col4 ?_⟩
  intro u v hadj heq
  have hval : (if hu : u ∈ Set.range f then (c_C u hu).val
      else if (c_bar ⟨u, hu⟩).val = 0 then (Classical.choose (h_ext_col u hu)).val else 3) =
      (if hv : v ∈ Set.range f then (c_C v hv).val
      else if (c_bar ⟨v, hv⟩).val = 0 then (Classical.choose (h_ext_col v hv)).val else 3) :=
    congrArg Fin.val heq
  by_cases hu : u ∈ Set.range f <;> by_cases hv : v ∈ Set.range f
  · rw [dif_pos hu, dif_pos hv] at hval
    exact hc_C_valid u hu v hv hadj (Fin.ext hval)
  · rw [dif_pos hu, dif_neg hv] at hval
    split_ifs at hval with hbar
    · have hspec := Classical.choose_spec (h_ext_col v hv) u hu hadj.symm
      exact hspec (Fin.ext hval)
    · have := (c_C u hu).isLt
      omega
  · rw [dif_neg hu, dif_pos hv] at hval
    split_ifs at hval with hbar
    · have hspec := Classical.choose_spec (h_ext_col u hu) v hv hadj
      exact hspec (Fin.ext hval.symm)
    · have := (c_C v hv).isLt
      omega
  · rw [dif_neg hu, dif_neg hv] at hval
    have h_bar_ne : c_bar ⟨u, hu⟩ ≠ c_bar ⟨v, hv⟩ := c_bar.valid hadj
    have h_bar_val_ne : (c_bar ⟨u, hu⟩).val ≠ (c_bar ⟨v, hv⟩).val := fun h => h_bar_ne (Fin.ext h)
    have h1 := (c_bar ⟨u, hu⟩).isLt
    have h2 := (c_bar ⟨v, hv⟩).isLt
    split_ifs at hval with hb1 hb2 hb2
    · exact absurd (hb1.trans hb2.symm) h_bar_val_ne
    · have := (Classical.choose (h_ext_col u hu)).isLt
      omega
    · have := (Classical.choose (h_ext_col v hv)).isLt
      omega
    · omega

open scoped Classical in
private lemma colorable_four_of_triangle_and_bipartite_compl {V : Type*} {G : SimpleGraph V}
    {x1 x2 x3 : V} (_h12 : G.Adj x1 x2) (_h13 : G.Adj x1 x3) (_h23 : G.Adj x2 x3)
    (h_compl : (G.induce ({x1, x2, x3} : Set V)ᶜ).Colorable 2)
    (h_no_two : ¬∃ y1 y2 : V, y1 ∉ ({x1, x2, x3} : Set V) ∧ y2 ∉ ({x1, x2, x3} : Set V) ∧
      y1 ≠ y2 ∧ (∀ x ∈ ({x1, x2, x3} : Set V), G.Adj y1 x) ∧
      (∀ x ∈ ({x1, x2, x3} : Set V), G.Adj y2 x)) :
    G.Colorable 4 := by
  obtain ⟨c_bar⟩ := h_compl
  have h_b0 : ∃ b0 : Fin 2, ∀ v (hv : v ∉ ({x1, x2, x3} : Set V)),
      c_bar ⟨v, hv⟩ = b0 → ∃ col_v : Fin 3,
        (G.Adj v x1 → col_v ≠ 0) ∧ (G.Adj v x2 → col_v ≠ 1) ∧ (G.Adj v x3 → col_v ≠ 2) := by
    by_cases hU : ∃ y0 : V, y0 ∉ ({x1, x2, x3} : Set V) ∧ ∀ x ∈ ({x1, x2, x3} : Set V), G.Adj y0 x
    · obtain ⟨y0, hy0, hy0_all⟩ := hU
      refine ⟨⟨1 - (c_bar ⟨y0, hy0⟩).val, by have := (c_bar ⟨y0, hy0⟩).isLt; omega⟩, ?_⟩
      intro v hv hcb
      have hvy0 : v ≠ y0 := by
        intro rfl
        have hval : (c_bar ⟨v, hv⟩).val = 1 - (c_bar ⟨v, hv⟩).val := congrArg Fin.val hcb
        have := (c_bar ⟨v, hv⟩).isLt
        omega
      by_cases h1 : G.Adj v x1
      · by_cases h2 : G.Adj v x2
        · by_cases h3 : G.Adj v x3
          · exfalso
            apply h_no_two
            refine ⟨v, y0, hv, hy0, hvy0, ?_, hy0_all⟩
            rintro x (rfl | rfl | rfl) <;> assumption
          · exact ⟨2, fun _ => by decide, fun _ => by decide, fun h => (h3 h).elim⟩
        · exact ⟨1, fun _ => by decide, fun h => (h2 h).elim, fun _ => by decide⟩
      · exact ⟨0, fun h => (h1 h).elim, fun _ => by decide, fun _ => by decide⟩
    · refine ⟨0, fun v hv _ => ?_⟩
      by_cases h1 : G.Adj v x1
      · by_cases h2 : G.Adj v x2
        · by_cases h3 : G.Adj v x3
          · exfalso
            apply hU
            refine ⟨v, hv, ?_⟩
            rintro x (rfl | rfl | rfl) <;> assumption
          · exact ⟨2, fun _ => by decide, fun _ => by decide, fun h => (h3 h).elim⟩
        · exact ⟨1, fun _ => by decide, fun h => (h2 h).elim, fun _ => by decide⟩
      · exact ⟨0, fun h => (h1 h).elim, fun _ => by decide, fun _ => by decide⟩
  obtain ⟨b0, hb0⟩ := h_b0
  let col_T (u : V) : Fin 3 :=
    if u = x1 then 0 else if u = x2 then 1 else 2
  have hcol_T_valid : ∀ u ∈ ({x1, x2, x3} : Set V), ∀ v ∈ ({x1, x2, x3} : Set V),
      u ≠ v → col_T u ≠ col_T v := by
    intro u hu v hv huv heq
    have hval := congrArg Fin.val heq
    dsimp only [col_T] at hval
    split_ifs at hval with h1 h2 h2 h3 h4 h4
    · exact huv (h1.trans h2.symm)
    · revert hval; decide
    · revert hval; decide
    · revert hval; decide
    · exact huv (h3.trans h4.symm)
    · revert hval; decide
    · revert hval; decide
    · revert hval; decide
    · rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> contradiction
  have hcol_T_ext : ∀ v (hv : v ∉ ({x1, x2, x3} : Set V)) (hcb : c_bar ⟨v, hv⟩ = b0),
      ∀ u ∈ ({x1, x2, x3} : Set V), G.Adj v u →
        Classical.choose (hb0 v hv hcb) ≠ col_T u := by
    intro v hv hcb u hu hadj
    have hspec := Classical.choose_spec (hb0 v hv hcb)
    rcases hu with rfl | rfl | rfl
    · dsimp only [col_T]; rw [if_pos rfl]; exact hspec.1 hadj
    · dsimp only [col_T]
      by_cases h1 : u = x1
      · subst h1; rw [if_pos rfl]; exact hspec.1 hadj
      · rw [if_neg h1, if_pos rfl]; exact hspec.2.1 hadj
    · dsimp only [col_T]
      by_cases h1 : u = x1
      · subst h1; rw [if_pos rfl]; exact hspec.1 hadj
      · by_cases h2 : u = x2
        · subst h2; rw [if_neg h1, if_pos rfl]; exact hspec.2.1 hadj
        · rw [if_neg h1, if_neg h2]; exact hspec.2.2 hadj
  let col4 (u : V) : Fin 4 :=
    ⟨if hu : u ∉ ({x1, x2, x3} : Set V) then
       if hcb : c_bar ⟨u, hu⟩ = b0 then
         (Classical.choose (hb0 u hu hcb)).val
       else 3
     else (col_T u).val, by
     by_cases hu : u ∉ ({x1, x2, x3} : Set V)
     · rw [dif_pos hu]
       by_cases hcb : c_bar ⟨u, hu⟩ = b0
       · rw [dif_pos hcb]; have := (Classical.choose (hb0 u hu hcb)).isLt; omega
       · rw [dif_neg hcb]; omega
     · rw [dif_neg hu]; have := (col_T u).isLt; omega⟩
  refine ⟨Coloring.mk col4 ?_⟩
  intro u v hadj heq
  have huv : u ≠ v := G.ne_of_adj hadj
  have hval : (if hu : u ∉ ({x1, x2, x3} : Set V) then
      if hcb : c_bar ⟨u, hu⟩ = b0 then (Classical.choose (hb0 u hu hcb)).val else 3
      else (col_T u).val) =
    (if hv : v ∉ ({x1, x2, x3} : Set V) then
      if hcb : c_bar ⟨v, hv⟩ = b0 then (Classical.choose (hb0 v hv hcb)).val else 3
      else (col_T v).val) := congrArg Fin.val heq
  by_cases hu : u ∉ ({x1, x2, x3} : Set V) <;> by_cases hv : v ∉ ({x1, x2, x3} : Set V)
  · rw [dif_pos hu, dif_pos hv] at hval
    have h_bar_ne : c_bar ⟨u, hu⟩ ≠ c_bar ⟨v, hv⟩ := c_bar.valid hadj
    split_ifs at hval with hcb1 hcb2 hcb2
    · exact h_bar_ne (hcb1.trans hcb2.symm)
    · have := (Classical.choose (hb0 u hu hcb1)).isLt; omega
    · have := (Classical.choose (hb0 v hv hcb2)).isLt; omega
    · have h1 := (c_bar ⟨u, hu⟩).isLt
      have h2 := (c_bar ⟨v, hv⟩).isLt
      have hb0_lt := b0.isLt
      have : (c_bar ⟨u, hu⟩).val ≠ b0.val := fun h => hcb1 (Fin.ext h)
      have : (c_bar ⟨v, hv⟩).val ≠ b0.val := fun h => hcb2 (Fin.ext h)
      have : (c_bar ⟨u, hu⟩).val ≠ (c_bar ⟨v, hv⟩).val := fun h => h_bar_ne (Fin.ext h)
      omega
  · rw [dif_pos hu, dif_neg hv] at hval
    rw [not_not] at hv
    split_ifs at hval with hcb
    · exact hcol_T_ext u hu hcb v hv hadj (Fin.ext hval)
    · have := (col_T v).isLt; omega
  · rw [dif_neg hu, dif_pos hv] at hval
    rw [not_not] at hu
    split_ifs at hval with hcb
    · exact hcol_T_ext v hv hcb u hu hadj.symm (Fin.ext hval.symm)
    · have := (col_T u).isLt; omega
  · rw [dif_neg hu, dif_neg hv] at hval
    rw [not_not] at hu hv
    exact hcol_T_valid u hu v hv huv (Fin.ext hval)

open scoped Classical in
private lemma exists_fourth_complete_of_not_colorable_four {V : Type*} {G : SimpleGraph V}
    {a b c d : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (_had : G.Adj a d)
    (hbc : G.Adj b c) (_hbd : G.Adj b d) (_hcd : G.Adj c d)
    (h_compl : (G.induce ({a, b, c} : Set V)ᶜ).Colorable 2)
    (hnot4 : ¬G.Colorable 4) :
    ∃ z ∉ ({a, b, c} : Set V), z ≠ d ∧ G.Adj z a ∧ G.Adj z b ∧ G.Adj z c := by
  have h_two : ∃ y1 y2 : V, y1 ∉ ({a, b, c} : Set V) ∧ y2 ∉ ({a, b, c} : Set V) ∧
      y1 ≠ y2 ∧ (∀ x ∈ ({a, b, c} : Set V), G.Adj y1 x) ∧
      (∀ x ∈ ({a, b, c} : Set V), G.Adj y2 x) := by
    by_contra h_no_two
    exact hnot4 (colorable_four_of_triangle_and_bipartite_compl hab hac hbc h_compl h_no_two)
  obtain ⟨y1, y2, hy1, hy2, hy12, hy1_all, hy2_all⟩ := h_two
  by_cases hy1d : y1 = d
  · exact ⟨y2, hy2, fun h => hy12 (hy1d.trans h.symm),
      hy2_all a (by simp), hy2_all b (by simp), hy2_all c (by simp)⟩
  · exact ⟨y1, hy1, hy1d,
      hy1_all a (by simp), hy1_all b (by simp), hy1_all c (by simp)⟩

open scoped Classical in
/--
Erdős [Er68b] originally asked about $a=b=3$ which was proved by Brown and Jung [BrJu69]
(who in fact prove that $G$ must contain two vertex disjoint odd cycles).
-/
theorem erdos_628.variants.k_5_a_3_b_3 (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG_chrom : G.chromaticNumber = (5 : ℕ∞))
    (hG_clique : G.CliqueFree 5) :
    ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (3 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (3 : ℕ∞) := by
  by_contra h_no_split
  push Not at h_no_split
  have hnot4 : ¬G.Colorable 4 := by
    intro hcol4
    have hle4 : G.chromaticNumber ≤ 4 := hcol4.chromaticNumber_le
    rw [hG_chrom] at hle4
    exact absurd hle4 (by decide)
  have hnot2 : ¬G.Colorable 2 := fun hcol2 => hnot4 (hcol2.mono (by decide))
  have h_compl_bip : ∀ s : Set V, ¬(G.induce s).Colorable 2 → (G.induce sᶜ).Colorable 2 := by
    intro s hs_not2
    have hs_ge3 : (3 : ℕ∞) ≤ (G.induce s).chromaticNumber :=
      three_le_chromaticNumber_iff_not_colorable_two.mpr hs_not2
    have h_lt3 : (G.induce sᶜ).chromaticNumber < (3 : ℕ∞) := h_no_split s hs_ge3
    have h_le2 : (G.induce sᶜ).chromaticNumber ≤ 2 := Order.le_of_lt_add_one h_lt3
    exact chromaticNumber_le_iff_colorable.mp h_le2
  have h_tri_compl_bip : ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c →
      (G.induce ({a, b, c} : Set V)ᶜ).Colorable 2 := by
    intro a b c hab hac hbc
    apply h_compl_bip
    let f : ℕ → V := fun i => if i % 3 = 0 then a else if i % 3 = 1 then b else c
    have hf : IsCyclicWalk G (2 * 1 + 1) f := by
      refine ⟨fun i => ?_, fun i => ?_⟩
      · dsimp only [f]; rw [Nat.add_mod_right]
      · dsimp only [f]
        have : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
        rcases this with h0 | h1 | h2
        · have h_next : (i + 1) % 3 = 1 := by omega
          rw [if_pos h0, h_next]; simp [hab]
        · have h_next : (i + 1) % 3 = 2 := by omega
          rw [if_neg (by omega), if_pos h1, h_next]; simp [hbc]
        · have h_next : (i + 1) % 3 = 0 := by omega
          rw [if_neg (by omega), if_neg (by omega), h_next, if_pos rfl]; exact hac.symm
    refine not_colorable_two_induce_of_odd_cyclicWalk hf (fun i => ?_)
    dsimp only [f]
    split_ifs <;> simp
  obtain ⟨m, f, hf, hmin⟩ := exists_min_odd_cyclicWalk hnot2
  have hm_ne0 : m ≠ 0 := by
    rintro rfl
    exact G.loopless.1 (f 0) (by simpa [ hf.1 0 ] using hf.2 0)
  by_cases hm_ge2 : 2 ≤ m
  · have hs_not2 : ¬(G.induce (Set.range f)).Colorable 2 :=
      not_colorable_two_induce_of_odd_cyclicWalk hf (fun i => ⟨i, rfl⟩)
    exact hnot4 (colorable_four_of_min_odd_cyclicWalk hf hmin hm_ge2 (h_compl_bip _ hs_not2))
  · have hm1 : m = 1 := by omega
    subst hm1
    have h01 : G.Adj (f 0) (f 1) := hf.2 0
    have h12 : G.Adj (f 1) (f 2) := hf.2 1
    have h02 : G.Adj (f 0) (f 2) := by
      have := hf.2 2
      rw [show 2 + 1 = 0 + 3 by rfl, hf.1 0] at this
      exact this.symm
    set x1 := f 0
    set x2 := f 1
    set x3 := f 2
    have h_ex4 : ∃ x4 ∉ ({x1, x2, x3} : Set V), G.Adj x4 x1 ∧ G.Adj x4 x2 ∧ G.Adj x4 x3 := by
      by_contra h_no4
      push Not at h_no4
      refine hnot4 (colorable_four_of_triangle_and_bipartite_compl h01 h02 h12
        (h_tri_compl_bip x1 x2 x3 h01 h02 h12) ?_)
      rintro ⟨y1, y2, hy1, _hy2, _hy12, hy1_all, _hy2_all⟩
      exact h_no4 y1 hy1 (hy1_all x1 (by simp)) (hy1_all x2 (by simp)) (hy1_all x3 (by simp))
    obtain ⟨x4, _hx4_not, h41, h42, h43⟩ := h_ex4
    have h_no_k5 : ∀ a b c d e : V,
        G.Adj a b → G.Adj a c → G.Adj a d → G.Adj a e →
        G.Adj b c → G.Adj b d → G.Adj b e →
        G.Adj c d → G.Adj c e → G.Adj d e → False := by
      intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
      apply hG_clique ({a, b, c, d, e} : Finset V)
      refine ⟨?_, ?_⟩
      · intro u hu v hv huv
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl | rfl | rfl <;>
        rcases hv with rfl | rfl | rfl | rfl | rfl
        all_goals try (exact (huv rfl).elim)
        all_goals first | assumption | exact Adj.symm (by assumption)
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [G.ne_of_adj hde]
        · simp [G.ne_of_adj hcd, G.ne_of_adj hce]
        · simp [G.ne_of_adj hbc, G.ne_of_adj hbd, G.ne_of_adj hbe]
        · simp [G.ne_of_adj hab, G.ne_of_adj hac, G.ne_of_adj had, G.ne_of_adj hae]
    obtain ⟨z1, _hz1_not, _hz1_ne_x4, hz1_x1, hz1_x2, hz1_x3⟩ :=
      exists_fourth_complete_of_not_colorable_four h01 h02 h41.symm h12 h42.symm h43.symm
        (h_tri_compl_bip x1 x2 x3 h01 h02 h12) hnot4
    obtain ⟨z2, _hz2_not, hz2_ne_x1, hz2_z1, hz2_x2, hz2_x3⟩ :=
      exists_fourth_complete_of_not_colorable_four hz1_x2 hz1_x3 hz1_x1 h12 h01.symm h02.symm
        (h_tri_compl_bip z1 x2 x3 hz1_x2 hz1_x3 h12) hnot4
    have hz2_not_x1 : ¬G.Adj z2 x1 := by
      intro h_adj
      exact h_no_k5 x1 x2 x3 z1 z2 h01 h02 hz1_x1.symm h_adj.symm h12 hz1_x2.symm hz2_x2.symm hz1_x3.symm hz2_x3.symm hz2_z1.symm
    obtain ⟨z3, _hz3_not, hz3_ne_x2, hz3_z1, hz3_z2, hz3_x3⟩ :=
      exists_fourth_complete_of_not_colorable_four hz2_z1.symm hz1_x3 hz1_x2 hz2_x3 hz2_x2 h12.symm
        (h_tri_compl_bip z1 z2 x3 hz2_z1.symm hz1_x3 hz2_x3) hnot4
    have hz3_ne_x1 : z3 ≠ x1 := by rintro rfl; exact hz2_not_x1 hz3_z2.symm
    have hz1_ne_x1 : z1 ≠ x1 := G.ne_of_adj hz1_x1
    have hz1_ne_x2 : z1 ≠ x2 := G.ne_of_adj hz1_x2
    have hz1_ne_x3 : z1 ≠ x3 := G.ne_of_adj hz1_x3
    have hz2_ne_x2 : z2 ≠ x2 := G.ne_of_adj hz2_x2
    have hz2_ne_x3 : z2 ≠ x3 := G.ne_of_adj hz2_x3
    have hz3_ne_x3 : z3 ≠ x3 := G.ne_of_adj hz3_x3
    obtain ⟨c_comp⟩ := h_tri_compl_bip x1 x2 x3 h01 h02 h12
    have hz1_in : z1 ∈ ({x1, x2, x3} : Set V)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz1_ne_x1, hz1_ne_x2, hz1_ne_x3⟩
    have hz2_in : z2 ∈ ({x1, x2, x3} : Set V)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz2_ne_x1, hz2_ne_x2, hz2_ne_x3⟩
    have hz3_in : z3 ∈ ({x1, x2, x3} : Set V)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz3_ne_x1, hz3_ne_x2, hz3_ne_x3⟩
    have hadj_12 : (G.induce ({x1, x2, x3} : Set V)ᶜ).Adj ⟨z1, hz1_in⟩ ⟨z2, hz2_in⟩ := hz2_z1.symm
    have hadj_13 : (G.induce ({x1, x2, x3} : Set V)ᶜ).Adj ⟨z1, hz1_in⟩ ⟨z3, hz3_in⟩ := hz3_z1.symm
    have hadj_23 : (G.induce ({x1, x2, x3} : Set V)ᶜ).Adj ⟨z2, hz2_in⟩ ⟨z3, hz3_in⟩ := hz3_z2.symm
    have h_ne12 : (c_comp ⟨z1, hz1_in⟩).val ≠ (c_comp ⟨z2, hz2_in⟩).val :=
      fun h => c_comp.valid hadj_12 (Fin.ext h)
    have h_ne13 : (c_comp ⟨z1, hz1_in⟩).val ≠ (c_comp ⟨z3, hz3_in⟩).val :=
      fun h => c_comp.valid hadj_13 (Fin.ext h)
    have h_ne23 : (c_comp ⟨z2, hz2_in⟩).val ≠ (c_comp ⟨z3, hz3_in⟩).val :=
      fun h => c_comp.valid hadj_23 (Fin.ext h)
    have := (c_comp ⟨z1, hz1_in⟩).isLt
    have := (c_comp ⟨z2, hz2_in⟩).isLt
    have := (c_comp ⟨z3, hz3_in⟩).isLt
    omega

open scoped Classical in
private lemma colorable_of_isPerfectMatching {V W : Type*} [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ u v : V, G.Adj u v → ¬H.Adj (f u) (f v))
    {M : H.Subgraph} (hM : M.IsPerfectMatching)
    {c : ℕ} (hc : Fintype.card W = 2 * c) :
    G.Colorable c := by
  have h_sum := M.spanningCoe.sum_degrees_eq_twice_card_edges
  have h_deg_span : ∀ w : W, M.spanningCoe.degree w = 1 := by
    intro w
    rw [degree_eq_one_iff_existsUnique_adj]
    exact hM.1 (hM.2 w)
  have h_sum_eq : ∑ w : W, M.spanningCoe.degree w = Fintype.card W := by
    simp [h_deg_span]
  have h_edge_card : Fintype.card M.edgeSet = c := by
    have h1 : M.spanningCoe.edgeFinset.card = c := by omega
    have h2 : Fintype.card M.edgeSet = M.spanningCoe.edgeFinset.card := by
      rw [← card_edgeSet]
      exact Fintype.card_congr (Equiv.setCongr M.edgeSet_spanningCoe.symm)
    omega
  let eqv : M.edgeSet ≃ Fin c := Fintype.equivFinOfCardEq h_edge_card
  refine ⟨Coloring.mk (fun u => eqv (hM.1.toEdge ⟨f u, hM.2 (f u)⟩)) ?_⟩
  intro u v huv heq
  have h_edge_eq : hM.1.toEdge ⟨f u, hM.2 (f u)⟩ = hM.1.toEdge ⟨f v, hM.2 (f v)⟩ :=
    eqv.injective heq
  have h_mem_u : f u ∈ (hM.1.toEdge ⟨f u, hM.2 (f u)⟩ : Sym2 W) := hM.1.mem_coe_toEdge (hM.2 (f u))
  have h_mem_v : f v ∈ (hM.1.toEdge ⟨f u, hM.2 (f u)⟩ : Sym2 W) := by
    rw [h_edge_eq]; exact hM.1.mem_coe_toEdge (hM.2 (f v))
  set e_sub := hM.1.toEdge ⟨f u, hM.2 (f u)⟩
  rcases e_sub with ⟨e, he⟩
  change f u ∈ e at h_mem_u
  change f v ∈ e at h_mem_v
  rcases e with ⟨x, y⟩
  rw [Subgraph.mem_edgeSet] at he
  have hH_xy : H.Adj x y := M.adj_sub he
  have hne : f u ≠ f v := hf.ne (G.ne_of_adj huv)
  simp only [Sym2.mem_iff] at h_mem_u h_mem_v
  rcases h_mem_u with hu_x | hu_y <;> rcases h_mem_v with hv_x | hv_y
  · exact hne (hu_x.trans hv_x.symm)
  · rw [← hu_x, ← hv_y] at hH_xy; exact hadj u v huv hH_xy
  · rw [← hv_x, ← hu_y] at hH_xy; exact hadj u v huv hH_xy.symm
  · exact hne (hu_y.trans hv_y.symm)

private def HStar {V : Type*} (G : SimpleGraph V) (r : ℕ) : SimpleGraph (V ⊕ Fin r) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl v => Gᶜ.Adj u v
    | x, y => x ≠ y
  symm := ⟨fun x y h => by
    cases x <;> cases y
    · exact h.symm
    · exact Ne.symm h
    · exact Ne.symm h
    · exact Ne.symm h⟩
  loopless := ⟨fun x h => by
    cases x
    · exact Gᶜ.loopless.1 _ h
    · exact h rfl⟩

open scoped Classical in
private lemma oddComponents_ncard_le_one_of_universal {W : Type*} [Fintype W]
    (K : SimpleGraph W) (w0 : W) (hw0 : ∀ w : W, w ≠ w0 → K.Adj w0 w) :
    K.oddComponents.ncard ≤ 1 := by
  have h_sub : K.oddComponents ⊆ {K.connectedComponentMk w0} := by
    intro c _hc
    rw [Set.mem_singleton_iff]
    obtain ⟨w, hw⟩ := c.nonempty_supp
    rw [ConnectedComponent.mem_supp_iff] at hw
    rw [← hw]
    by_cases heq : w = w0
    · subst heq; rfl
    · exact ConnectedComponent.sound (hw0 w heq).symm.reachable
  exact le_trans (Set.ncard_le_ncard h_sub) (by simp)

open scoped Classical in
private lemma colorable_of_indep2_card_lt {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (h_indep2 : ∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
      G.Adj x y ∨ G.Adj x z ∨ G.Adj y z)
    {s : Set V} {c : ℕ}
    (hcol : (G.induce s).Colorable c) :
    s.ncard ≤ 2 * c := by
  obtain ⟨col⟩ := hcol
  -- Map each x : s to (col x, ...); since each fiber (color class) has size ≤ 2,
  -- ∑ i : Fin c, (Finset.univ.filter (fun x : s => col x = i)).card = Fintype.card s ≤ 2 * c!
  have h_fiber : ∀ i : Fin c, (Finset.univ.filter (fun x : s => col x = i)).card ≤ 2 := by
    intro i
    by_contra hgt
    have hge3 : 3 ≤ (Finset.univ.filter (fun x : s => col x = i)).card := by omega
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hge3
    rw [Finset.card_eq_three] at hT_card
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hT_card
    have hx := (Finset.mem_filter.mp (hT_sub (by simp : x ∈ ({x, y, z} : Finset s)))).2
    have hy := (Finset.mem_filter.mp (hT_sub (by simp : y ∈ ({x, y, z} : Finset s)))).2
    have hz := (Finset.mem_filter.mp (hT_sub (by simp : z ∈ ({x, y, z} : Finset s)))).2
    rcases h_indep2 x.1 y.1 z.1 (Subtype.coe_ne_coe.mpr hxy)
      (Subtype.coe_ne_coe.mpr hxz) (Subtype.coe_ne_coe.mpr hyz) with h1 | h2 | h3
    · exact col.valid h1 (hx.trans hy.symm)
    · exact col.valid h2 (hx.trans hz.symm)
    · exact col.valid h3 (hy.trans hz.symm)
  have h_sum : ∑ i : Fin c, (Finset.univ.filter (fun x : s => col x = i)).card = Fintype.card s := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp
    · intro i _ j _ hij
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_filter] at hx1 hx2
      exact hij (hx1.2.symm.trans hx2.2)
  have h_le : ∑ i : Fin c, (Finset.univ.filter (fun x : s => col x = i)).card ≤ ∑ _i : Fin c, 2 :=
    Finset.sum_le_sum (fun i _ => h_fiber i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h_le
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  omega

open scoped Classical in
private lemma colorable_induce_compl_odd_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (h_indep2 : ∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
      G.Adj x y ∨ G.Adj x z ∨ G.Adj y z)
    {P : Set V} {c : ℕ}
    (hcol : (G.induce (Pᶜ : Set V)).Colorable c) :
    Fintype.card V - P.ncard + ((⊤ : Gᶜ.Subgraph).deleteVerts P).coe.oddComponents.ncard ≤ 2 * c := by
  obtain ⟨col⟩ := hcol
  set W := ((⊤ : Gᶜ.Subgraph).deleteVerts P).verts
  set H_P := ((⊤ : Gᶜ.Subgraph).deleteVerts P).coe
  let eqv_P : W ≃ ↥(Pᶜ : Set V) :=
    ⟨fun x => ⟨x.1, x.2.2⟩, fun x => ⟨x.1, ⟨trivial, x.2⟩⟩, fun _ => rfl, fun _ => rfl⟩
  let col_H (x : W) : Fin c := col (eqv_P x)
  have hcol_H_valid : ∀ x y : W, G.Adj x.1 y.1 → col_H x ≠ col_H y := by
    intro x y hadj
    exact col.valid hadj
  let S (i : Fin c) : Finset W := Finset.univ.filter (fun x : W => col_H x = i)
  have hS_le2 : ∀ i : Fin c, (S i).card ≤ 2 := by
    intro i
    by_contra hgt
    have hge3 : 3 ≤ (S i).card := by omega
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hge3
    rw [Finset.card_eq_three] at hT_card
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hT_card
    have hx := (Finset.mem_filter.mp (hT_sub (by simp : x ∈ ({x, y, z} : Finset W)))).2
    have hy := (Finset.mem_filter.mp (hT_sub (by simp : y ∈ ({x, y, z} : Finset W)))).2
    have hz := (Finset.mem_filter.mp (hT_sub (by simp : z ∈ ({x, y, z} : Finset W)))).2
    rcases h_indep2 x.1 y.1 z.1 (Subtype.coe_ne_coe.mpr hxy)
      (Subtype.coe_ne_coe.mpr hxz) (Subtype.coe_ne_coe.mpr hyz) with h1 | h2 | h3
    · exact hcol_H_valid x y h1 (hx.trans hy.symm)
    · exact hcol_H_valid x z h2 (hx.trans hz.symm)
    · exact hcol_H_valid y z h3 (hy.trans hz.symm)
  have h_same_comp : ∀ x y : W, col_H x = col_H y → H_P.connectedComponentMk x = H_P.connectedComponentMk y := by
    intro x y heq
    by_cases hxy : x = y
    · rw [hxy]
    · have hnot_G : ¬G.Adj x.1 y.1 := fun hadj => hcol_H_valid x y hadj heq
      have h_Gc : Gᶜ.Adj x.1 y.1 := ⟨Subtype.coe_ne_coe.mpr hxy, hnot_G⟩
      have h_HP : H_P.Adj x y := ⟨x.2, y.2, h_Gc⟩
      exact ConnectedComponent.sound h_HP.reachable
  -- For each odd component K of H_P, there exists x ∈ K.supp such that (S (col_H x)).card ≤ 1!
  have h_odd_has_single : ∀ K ∈ H_P.oddComponents,
      ∃ x ∈ K.supp, (S (col_H x)).card ≤ 1 := by
    intro K hK
    by_contra h_all2
    push Not at h_all2
    -- Then K.supp.toFinset is the disjoint union of S i over i ∈ K.supp.toFinset.image col_H,
    -- and each such S i has card = 2!
    let I_K : Finset (Fin c) := K.supp.toFinset.image col_H
    have h_biUnion : I_K.biUnion S = K.supp.toFinset := by
      ext y
      simp only [I_K, S, Finset.mem_biUnion, Finset.mem_image, Set.mem_toFinset,
        ConnectedComponent.mem_supp_iff, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, ⟨x, hx, rfl⟩, hy⟩
        rw [← h_same_comp x y hy.symm, hx]
      · intro hy
        exact ⟨col_H y, ⟨y, hy, rfl⟩, rfl⟩
    have h_disj : (I_K : Set (Fin c)).PairwiseDisjoint S := by
      intro i _ j _ hij
      change Disjoint (S i) (S j)
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [S, Finset.mem_filter] at hx1 hx2
      exact hij (hx1.2.symm.trans hx2.2)
    have h_card2 : ∀ i ∈ I_K, (S i).card = 2 := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨x, hx, rfl⟩ := hi
      rw [Set.mem_toFinset] at hx
      have h1 := h_all2 x hx
      have h2 := hS_le2 (col_H x)
      omega
    have h_even : Even K.supp.ncard := by
      rw [Set.ncard_eq_toFinset_card', ← h_biUnion, Finset.card_biUnion h_disj,
          Finset.sum_congr rfl h_card2, Finset.sum_const, smul_eq_mul]
      exact ⟨I_K.card, by ring⟩
    exact (Nat.not_even_iff_odd.mpr hK) h_even
  set I1 := Finset.univ.filter (fun i : Fin c => (S i).card ≤ 1)
  set I2 := Finset.univ.filter (fun i : Fin c => ¬(S i).card ≤ 1)
  let f_odd (K : H_P.oddComponents) : I1 :=
    ⟨col_H (Classical.choose (h_odd_has_single K.1 K.2)),
     Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Classical.choose_spec (h_odd_has_single K.1 K.2)).2⟩⟩
  have hf_odd_inj : Function.Injective f_odd := by
    intro K1 K2 heq
    have h_col_eq : col_H (Classical.choose (h_odd_has_single K1.1 K1.2)) =
        col_H (Classical.choose (h_odd_has_single K2.1 K2.2)) := Subtype.ext_iff.mp heq
    have hx1 := (Classical.choose_spec (h_odd_has_single K1.1 K1.2)).1
    have hx2 := (Classical.choose_spec (h_odd_has_single K2.1 K2.2)).1
    rw [ConnectedComponent.mem_supp_iff] at hx1 hx2
    ext1
    rw [← hx1, ← hx2]
    exact h_same_comp _ _ h_col_eq
  have h_odd_le : H_P.oddComponents.ncard ≤ I1.card := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective f_odd hf_odd_inj
  have h_sum_W : ∑ i : Fin c, (S i).card = Fintype.card W := by
    rw [← Finset.card_biUnion]
    · congr 1; ext x; simp [S]
    · intro i _ j _ hij; change Disjoint _ _; rw [Finset.disjoint_left]
      intro x hx1 hx2; simp only [S, Finset.mem_filter] at hx1 hx2; exact hij (hx1.2.symm.trans hx2.2)
  have h_I_union : I1 ∪ I2 = Finset.univ := by
    ext i; simp only [I1, I2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have h_I_disj : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [I1, I2, Finset.mem_filter] at h1 h2; exact h2.2 h1.2
  have h_I_cards : I1.card + I2.card = c := by
    rw [← Finset.card_union_of_disjoint h_I_disj, h_I_union, Finset.card_univ, Fintype.card_fin]
  have h_sum_split : ∑ i : Fin c, (S i).card ≤ I1.card + 2 * I2.card := by
    rw [← h_I_union, Finset.sum_union h_I_disj]
    have h1 : ∑ i ∈ I1, (S i).card ≤ ∑ _i ∈ I1, 1 :=
      Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    have h2 : ∑ i ∈ I2, (S i).card ≤ ∑ _i ∈ I2, 2 :=
      Finset.sum_le_sum (fun i _ => hS_le2 i)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1 h2
    omega
  have h_W_card : Fintype.card W = Fintype.card V - P.ncard := by
    rw [Fintype.card_congr eqv_P, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        Set.ncard_compl P, Nat.card_eq_fintype_card]
  omega

open scoped Classical in
private lemma oddComponents_ncard_iso {W1 W2 : Type*} [Fintype W1] [Fintype W2]
    {K1 : SimpleGraph W1} {K2 : SimpleGraph W2} (e : K1 ≃g K2) :
    K1.oddComponents.ncard = K2.oddComponents.ncard := by
  let f_cc : K1.ConnectedComponent → K2.ConnectedComponent := ConnectedComponent.map e.toHom
  let g_cc : K2.ConnectedComponent → K1.ConnectedComponent := ConnectedComponent.map e.symm.toHom
  have hfg : Function.LeftInverse g_cc f_cc := by
    intro c; induction c using ConnectedComponent.ind
    simp [f_cc, g_cc]
  have hgf : Function.RightInverse g_cc f_cc := by
    intro c; induction c using ConnectedComponent.ind
    simp [f_cc, g_cc]
  have h_supp : ∀ c : K1.ConnectedComponent, (f_cc c).supp.ncard = c.supp.ncard := by
    intro c
    have h_img : (f_cc c).supp = e '' c.supp := by
      ext w2
      constructor
      · intro hw2
        obtain ⟨w1, rfl⟩ := e.surjective w2
        refine ⟨w1, ?_, rfl⟩
        induction c using ConnectedComponent.ind
        simp only [f_cc, ConnectedComponent.map_mk, ConnectedComponent.mem_supp_iff,
          ConnectedComponent.eq] at hw2 ⊢
        obtain ⟨p⟩ := hw2
        exact ⟨p.map e.symm.toHom |>.copy (by simp) (by simp)⟩
      · rintro ⟨w1, hw1, rfl⟩
        induction c using ConnectedComponent.ind
        simp only [f_cc, ConnectedComponent.map_mk, ConnectedComponent.mem_supp_iff,
          ConnectedComponent.eq] at hw1 ⊢
        obtain ⟨p⟩ := hw1
        exact ⟨p.map e.toHom⟩
    rw [h_img, Set.ncard_image_of_injective _ e.injective]
  have h_bij : Set.BijOn f_cc K1.oddComponents K2.oddComponents := by
    refine ⟨fun c hc => ?_, fun c1 _ c2 _ h => hfg.injective h, fun c2 hc2 => ?_⟩
    · change Odd (f_cc c).supp.ncard
      rw [h_supp c]; exact hc
    · refine ⟨g_cc c2, ?_, hgf c2⟩
      change Odd (g_cc c2).supp.ncard
      rw [← h_supp (g_cc c2), hgf c2]; exact hc2
  exact Set.BijOn.ncard_eq h_bij

open scoped Classical in
private lemma exists_p_odd_components_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ}
    (hk : 1 ≤ k) (hnot : ¬G.Colorable (k - 1)) :
    2 * k ≤ Fintype.card V + 1 ∨
    ∃ P : Set V, 2 * k ≤ Fintype.card V + ((⊤ : Gᶜ.Subgraph).deleteVerts P).coe.oddComponents.ncard - P.ncard := by
  by_cases hcard : 2 * k ≤ Fintype.card V + 1
  · exact Or.inl hcard
  · right
    let r := (2 * k - 2) - Fintype.card V
    have hr_card : Fintype.card (V ⊕ Fin r) = 2 * (k - 1) := by
      rw [Fintype.card_sum, Fintype.card_fin]
      omega
    have h_even : Even (Nat.card (V ⊕ Fin r)) := by
      rw [Nat.card_eq_fintype_card, hr_card]
      exact ⟨k - 1, by ring⟩
    have h_no_pm : ∀ M : (HStar G r).Subgraph, ¬M.IsPerfectMatching := by
      intro M hM
      apply hnot
      refine colorable_of_isPerfectMatching Sum.inl Sum.inl_injective ?_ hM hr_card
      intro u v huv hH
      exact hH.2 huv
    obtain ⟨U, hU⟩ := exists_isTutteViolator h_no_pm h_even
    rw [IsTutteViolator] at hU
    -- By parity (odd_ncard_oddComponents), U.ncard + 2 ≤ oddComponents.ncard!
    have h_parity : (Odd ((⊤ : (HStar G r).Subgraph).deleteVerts U).coe.oddComponents.ncard ↔ Odd U.ncard) := by
      rw [odd_ncard_oddComponents, Nat.card_eq_fintype_card]
      have h_v : Fintype.card ((⊤ : (HStar G r).Subgraph).deleteVerts U).verts =
          Fintype.card (V ⊕ Fin r) - U.ncard := by
        let eqv_U : ((⊤ : (HStar G r).Subgraph).deleteVerts U).verts ≃ ↥(Uᶜ : Set (V ⊕ Fin r)) :=
          ⟨fun x => ⟨x.1, x.2.2⟩, fun x => ⟨x.1, ⟨trivial, x.2⟩⟩, fun _ => rfl, fun _ => rfl⟩
        rw [Fintype.card_congr eqv_U, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
            Set.ncard_compl U, Nat.card_eq_fintype_card]
      have hU_le : U.ncard ≤ Fintype.card (V ⊕ Fin r) := by
        rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
        exact Set.ncard_le_ncard (Set.subset_univ U)
      rw [h_v, hr_card, Nat.odd_iff, Nat.odd_iff]
      omega
    have hU_add2 : U.ncard + 2 ≤ ((⊤ : (HStar G r).Subgraph).deleteVerts U).coe.oddComponents.ncard := by
      rw [Nat.odd_iff, Nat.odd_iff] at h_parity
      omega
    have hinr : ∀ j : Fin r, Sum.inr j ∈ U := by
      intro j
      by_contra hj_not
      let w0 : ((⊤ : (HStar G r).Subgraph).deleteVerts U).verts := ⟨Sum.inr j, ⟨trivial, hj_not⟩⟩
      have hw0_univ : ∀ w : ((⊤ : (HStar G r).Subgraph).deleteVerts U).verts,
          w ≠ w0 → ((⊤ : (HStar G r).Subgraph).deleteVerts U).coe.Adj w0 w := by
        intro w hw
        refine ⟨w0.2, w.2, ?_⟩
        rcases w with ⟨x, hx⟩
        rcases x with u | j'
        · change Sum.inr j ≠ Sum.inl u; simp
        · change Sum.inr j ≠ Sum.inr j'
          exact fun h => hw (Subtype.ext h.symm)
      have h_le1 := oddComponents_ncard_le_one_of_universal _ w0 hw0_univ
      omega
    let P : Set V := {v : V | Sum.inl v ∈ U}
    refine ⟨P, ?_⟩
    have hU_card : U.ncard = P.ncard + r := by
      have h_eq : U = (Sum.inl '' P) ∪ (Sum.inr '' (Set.univ : Set (Fin r))) := by
        ext x
        rcases x with v | j
        · simp [P]
        · simp [hinr j]
      have h_disj : Disjoint (Sum.inl '' P) (Sum.inr '' (Set.univ : Set (Fin r))) := by
        rw [Set.disjoint_left]
        rintro _ ⟨v, _, rfl⟩ ⟨j, _, h⟩
        simp at h
      rw [h_eq, Set.ncard_union_eq h_disj,
          Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inr_injective,
          Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    let iso : ((⊤ : Gᶜ.Subgraph).deleteVerts P).coe ≃g ((⊤ : (HStar G r).Subgraph).deleteVerts U).coe := {
      toFun := fun x => ⟨Sum.inl x.1, ⟨trivial, x.2.2⟩⟩
      invFun := fun y =>
        match y with
        | ⟨Sum.inl v, hv⟩ => ⟨v, ⟨trivial, hv.2⟩⟩
        | ⟨Sum.inr j, hj⟩ => False.elim (hj.2 (hinr j))
      left_inv := fun x => by cases x; rfl
      right_inv := fun y => by
        rcases y with ⟨x, hx⟩
        rcases x with v | j
        · rfl
        · exfalso; exact hx.2 (hinr j)
      map_rel_iff' := by
        intro x1 x2
        change ((True ∧ x1.1 ∉ P) ∧ (True ∧ x2.1 ∉ P) ∧ Gᶜ.Adj x1.1 x2.1) ↔
          ((True ∧ x1.1 ∉ P) ∧ (True ∧ x2.1 ∉ P) ∧ Gᶜ.Adj x1.1 x2.1)
        rfl
    }
    have h_odd_eq := oddComponents_ncard_iso iso
    omega

open scoped Classical in
private lemma critical_and_connected_compl_card_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ}
    (hk : 2 ≤ k)
    (h_indep2 : ∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
      G.Adj x y ∨ G.Adj x z ∨ G.Adj y z)
    (hnot : ¬G.Colorable (k - 1))
    (hcrit : ∀ P : Set V, P.Nonempty → (G.induce (Pᶜ : Set V)).Colorable (k - 1))
    (hconn : ∀ v0 u : V, Gᶜ.Reachable v0 u) :
    2 * k ≤ Fintype.card V + 1 := by
  rcases exists_p_odd_components_bound (by omega : 1 ≤ k) hnot with hcard | ⟨P, hP⟩
  · exact hcard
  · by_cases hP_ne : P.Nonempty
    · have hcol_P := hcrit P hP_ne
      have h_bound := colorable_induce_compl_odd_bound h_indep2 hcol_P
      have hP_le : P.ncard ≤ Fintype.card V := by
        rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
        exact Set.ncard_le_ncard (Set.subset_univ P)
      omega
    · rw [Set.not_nonempty_iff_eq_empty] at hP_ne
      subst hP_ne
      -- Now P = ∅, so 2 * k ≤ Fintype.card V + ((⊤ : Gᶜ.Subgraph).deleteVerts ∅).coe.oddComponents.ncard!
      -- Since Gᶜ is connected (∀ v0 u, Gᶜ.Reachable v0 u), if V is nonempty (pick v0),
      -- then ((⊤ : Gᶜ.Subgraph).deleteVerts ∅).coe ≃g Gᶜ has at most 1 connected component,
      -- so oddComponents.ncard ≤ 1, which gives 2 * k ≤ Fintype.card V + 1!
      have h_nonempty : Nonempty V := by
        by_contra h_emp
        rw [not_nonempty_iff] at h_emp
        apply hnot
        exact ⟨Coloring.mk (fun v => isEmptyElim v) (fun {u _} _ => isEmptyElim u)⟩
      obtain ⟨v0⟩ := h_nonempty
      let iso0 : Gᶜ ≃g ((⊤ : Gᶜ.Subgraph).deleteVerts (∅ : Set V)).coe := {
        toFun := fun u => ⟨u, ⟨trivial, Set.notMem_empty u⟩⟩
        invFun := fun x => x.1
        left_inv := fun _ => rfl
        right_inv := fun x => by cases x; rfl
        map_rel_iff' := by intro _ _; simp [Subgraph.deleteVerts]
      }
      have h_odd0 := oddComponents_ncard_iso iso0
      have h_sub : Gᶜ.oddComponents ⊆ {Gᶜ.connectedComponentMk v0} := by
        intro c _hc
        rw [Set.mem_singleton_iff]
        obtain ⟨u, hu⟩ := c.nonempty_supp
        rw [ConnectedComponent.mem_supp_iff] at hu
        rw [← hu]
        exact ConnectedComponent.sound (hconn v0 u).symm
      have h_le1 : Gᶜ.oddComponents.ncard ≤ 1 :=
        le_trans (Set.ncard_le_ncard h_sub) (by simp)
      rw [Set.ncard_empty] at hP
      omega

open scoped Classical in
private lemma splittable_of_card_ge_two_k_sub_one {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (h_indep2 : ∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
      G.Adj x y ∨ G.Adj x z ∨ G.Adj y z)
    {k a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = k + 1)
    (hcard : 2 * k - 1 ≤ Fintype.card V)
    (h_nonempty : Nonempty V) :
    ∃ s : Set V, ¬(G.induce s).Colorable (a - 1) ∧ ¬(G.induce (sᶜ : Set V)).Colorable (b - 1) := by
  by_cases hcard2k : 2 * k ≤ Fintype.card V
  · -- Subcase 0: 2 * k ≤ Fintype.card V!
    -- Pick any subset S : Finset V of card 2 * a - 1!
    have h_le : 2 * a - 1 ≤ (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]; omega
    obtain ⟨S, _, hS_card⟩ := Finset.exists_subset_card_eq h_le
    refine ⟨(S : Set V), ?_, ?_⟩
    · intro hcol
      have h_bd := colorable_of_indep2_card_lt h_indep2 hcol
      rw [Set.ncard_coe_finset, hS_card] at h_bd
      omega
    · intro hcol
      have h_bd := colorable_of_indep2_card_lt h_indep2 hcol
      rw [Set.ncard_compl, Nat.card_eq_fintype_card, Set.ncard_coe_finset, hS_card] at h_bd
      omega
  · -- Now Fintype.card V = 2 * k - 1!
    have hV_eq : Fintype.card V = 2 * k - 1 := by omega
    by_cases h_clique : ¬G.CliqueFree a
    · -- Subcase A: G contains an a-clique S!
      rw [CliqueFree] at h_clique
      push Not at h_clique
      obtain ⟨S, hS_clique⟩ := h_clique
      refine ⟨(S : Set V), ?_, ?_⟩
      · rintro ⟨col⟩
        have h_inj : Function.Injective col := by
          intro x y heq
          by_contra hxy
          have hadj : G.Adj x.1 y.1 := hS_clique.1 x.2 y.2 (Subtype.coe_ne_coe.mpr hxy)
          exact col.valid hadj heq
        have h_le := Fintype.card_le_of_injective col h_inj
        rw [Fintype.card_fin] at h_le
        have h_sc : Fintype.card (S : Set V) = a := by
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_coe_finset, hS_clique.2]
        omega
      · intro hcol
        have h_bd := colorable_of_indep2_card_lt h_indep2 hcol
        rw [Set.ncard_compl, Nat.card_eq_fintype_card, Set.ncard_coe_finset, hS_clique.2] at h_bd
        omega
    · rw [not_not] at h_clique
      obtain ⟨v⟩ := h_nonempty
      let N_H : Finset V := Finset.univ.filter (fun u => u ≠ v ∧ ¬G.Adj v u)
      have hNH_clique : G.IsClique (N_H : Set V) := by
        intro x hx y hy hxy
        simp only [N_H, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        rcases h_indep2 v x y hx.1.symm hy.1.symm hxy with h1 | h2 | h3
        · exfalso; exact hx.2 h1
        · exfalso; exact hy.2 h2
        · exact h3
      have hNH_lt : N_H.card < a := by
        by_contra hge
        have hge_a : a ≤ N_H.card := by omega
        obtain ⟨K, hK_sub, hK_card⟩ := Finset.exists_subset_card_eq hge_a
        exact h_clique K ⟨hNH_clique.subset (Finset.coe_subset.mpr hK_sub), hK_card⟩
      have hNH_sub : N_H ⊆ Finset.univ.erase v := by
        intro u hu
        rw [Finset.mem_erase]
        exact ⟨(Finset.mem_filter.mp hu).2.1, Finset.mem_univ u⟩
      have h_sdiff_card : 2 * a - 1 - N_H.card ≤ (Finset.univ.erase v \ N_H).card := by
        have h_add := Finset.card_sdiff_add_card_eq_card hNH_sub
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at h_add
        omega
      obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_sdiff_card
      let S : Finset V := N_H ∪ T
      have hNH_S : N_H ⊆ S := Finset.subset_union_left
      have hS_erase : S ⊆ Finset.univ.erase v :=
        Finset.union_subset hNH_sub (Finset.Subset.trans hT_sub Finset.sdiff_subset)
      have hS_card_eq : S.card = 2 * a - 1 := by
        have h_disj : Disjoint N_H T :=
          Finset.disjoint_of_subset_right hT_sub Finset.disjoint_sdiff
        rw [Finset.card_union_of_disjoint h_disj, hT_card]
        omega
      have hv_not_S : v ∉ S := fun hv => (Finset.mem_erase.mp (hS_erase hv)).1 rfl
      refine ⟨(S : Set V), ?_, ?_⟩
      · intro hcol
        have h_bd := colorable_of_indep2_card_lt h_indep2 hcol
        rw [Set.ncard_coe_finset, hS_card_eq] at h_bd
        omega
      · rintro ⟨col⟩
        let c_v : Fin (b - 1) := col ⟨v, hv_not_S⟩
        have h_valid_v : ∀ w (hw : w ∈ ((insert v S : Finset V) : Set V)ᶜ),
            col ⟨w, fun hwS => hw (Finset.mem_insert_of_mem hwS)⟩ ≠ c_v := by
          intro w hw heq
          simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert, not_or] at hw
          have hadj_vw : G.Adj v w := by
            by_contra hnot_vw
            have hw_NH : w ∈ N_H := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw.1, hnot_vw⟩
            exact hw.2 (hNH_S hw_NH)
          have hadj_ind : (G.induce (S : Set V)ᶜ).Adj
              ⟨w, fun hwS => hw.2 hwS⟩ ⟨v, hv_not_S⟩ := hadj_vw.symm
          exact col.valid hadj_ind heq
        let W' := ((insert v S : Finset V) : Set V)ᶜ
        let eqv_fin : {i : Fin (b - 1) // i ≠ c_v} ≃ Fin (b - 2) := by
          refine Fintype.equivFinOfCardEq ?_
          rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
          omega
        have hcol_W' : (G.induce W').Colorable (b - 2) := by
          refine ⟨Coloring.mk (fun x => eqv_fin ⟨col ⟨x.1, fun hxS => x.2 (Finset.mem_insert_of_mem hxS)⟩,
            h_valid_v x.1 x.2⟩) ?_⟩
          intro x y hadj heq
          have h_sub_eq := eqv_fin.injective heq
          have hadj_ind : (G.induce (S : Set V)ᶜ).Adj
              ⟨x.1, fun hxS => x.2 (Finset.mem_insert_of_mem hxS)⟩
              ⟨y.1, fun hyS => y.2 (Finset.mem_insert_of_mem hyS)⟩ := hadj
          exact col.valid hadj_ind (Subtype.ext_iff.mp h_sub_eq)
        have h_bd := colorable_of_indep2_card_lt h_indep2 hcol_W'
        rw [Set.ncard_compl, Nat.card_eq_fintype_card, Set.ncard_coe_finset,
            Finset.card_insert_of_notMem hv_not_S, hS_card_eq] at h_bd
        omega

open scoped Classical in
private lemma colorable_of_join_colorable {V : Type*} {G : SimpleGraph V}
    {A B : Set V} (hAB : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v)
    {cA cB c : ℕ}
    (hcol : (G.induce (A ∪ B)).Colorable c)
    (hnotA : ¬(G.induce A).Colorable cA)
    (hnotB : ¬(G.induce B).Colorable cB) :
    cA + cB + 2 ≤ c := by
  obtain ⟨col⟩ := hcol
  let IA : Finset (Fin c) := Finset.univ.filter (fun i : Fin c => ∃ u, ∃ hu : u ∈ A, col ⟨u, Or.inl hu⟩ = i)
  let IB : Finset (Fin c) := Finset.univ.filter (fun i : Fin c => ∃ v, ∃ hv : v ∈ B, col ⟨v, Or.inr hv⟩ = i)
  have h_disj : Disjoint IA IB := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    simp only [IA, IB, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
    obtain ⟨u, hu, rfl⟩ := hiA
    obtain ⟨v, hv, heq⟩ := hiB
    have hadj : (G.induce (A ∪ B)).Adj ⟨u, Or.inl hu⟩ ⟨v, Or.inr hv⟩ := hAB u hu v hv
    exact col.valid hadj heq.symm
  have hIA_gt : cA < IA.card := by
    by_contra hle
    have hle' : Fintype.card IA ≤ cA := by rw [Fintype.card_coe]; omega
    let eqvA := Fintype.equivFin IA
    apply hnotA
    refine Colorable.mono hle' ⟨Coloring.mk (fun x => eqvA ⟨col ⟨x.1, Or.inl x.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x.1, x.2, rfl⟩⟩⟩) ?_⟩
    intro x y hadj heq
    have h_sub := eqvA.injective heq
    have hadj_AB : (G.induce (A ∪ B)).Adj ⟨x.1, Or.inl x.2⟩ ⟨y.1, Or.inl y.2⟩ := hadj
    exact col.valid hadj_AB (Subtype.ext_iff.mp h_sub)
  have hIB_gt : cB < IB.card := by
    by_contra hle
    have hle' : Fintype.card IB ≤ cB := by rw [Fintype.card_coe]; omega
    let eqvB := Fintype.equivFin IB
    apply hnotB
    refine Colorable.mono hle' ⟨Coloring.mk (fun x => eqvB ⟨col ⟨x.1, Or.inr x.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x.1, x.2, rfl⟩⟩⟩) ?_⟩
    intro x y hadj heq
    have h_sub := eqvB.injective heq
    have hadj_AB : (G.induce (A ∪ B)).Adj ⟨x.1, Or.inr x.2⟩ ⟨y.1, Or.inr y.2⟩ := hadj
    exact col.valid hadj_AB (Subtype.ext_iff.mp h_sub)
  have h_union : (IA ∪ IB).card ≤ c := by
    refine le_trans (Finset.card_le_univ _) ?_
    rw [Fintype.card_fin]
  rw [Finset.card_union_of_disjoint h_disj] at h_union
  omega

private lemma colorable_join_of_colorable {V : Type*} {G : SimpleGraph V}
    {A B : Set V} {cA cB : ℕ}
    (hA : (G.induce A).Colorable cA)
    (hB : (G.induce B).Colorable cB) :
    (G.induce (A ∪ B)).Colorable (cA + cB) := by
  classical
  obtain ⟨colA⟩ := hA
  obtain ⟨colB⟩ := hB
  let col_join (x : ↥(A ∪ B)) : Fin (cA + cB) :=
    ⟨if hxA : x.1 ∈ A then
      (colA ⟨x.1, hxA⟩).val
    else
      cA + (colB ⟨x.1, x.2.resolve_left hxA⟩).val, by
    by_cases hxA : x.1 ∈ A
    · rw [dif_pos hxA]; have := (colA ⟨x.1, hxA⟩).isLt; omega
    · rw [dif_neg hxA]; have := (colB ⟨x.1, x.2.resolve_left hxA⟩).isLt; omega⟩
  refine ⟨Coloring.mk col_join ?_⟩
  intro x y hadj heq
  have hval : (if hxA : x.1 ∈ A then (colA ⟨x.1, hxA⟩).val
      else cA + (colB ⟨x.1, x.2.resolve_left hxA⟩).val) =
    (if hyA : y.1 ∈ A then (colA ⟨y.1, hyA⟩).val
      else cA + (colB ⟨y.1, y.2.resolve_left hyA⟩).val) := congrArg Fin.val heq
  by_cases hxA : x.1 ∈ A <;> by_cases hyA : y.1 ∈ A
  · rw [dif_pos hxA, dif_pos hyA] at hval
    have hadjA : (G.induce A).Adj ⟨x.1, hxA⟩ ⟨y.1, hyA⟩ := hadj
    exact colA.valid hadjA (Fin.ext hval)
  · rw [dif_pos hxA, dif_neg hyA] at hval
    have := (colA ⟨x.1, hxA⟩).isLt
    omega
  · rw [dif_neg hxA, dif_pos hyA] at hval
    have := (colA ⟨y.1, hyA⟩).isLt
    omega
  · rw [dif_neg hxA, dif_neg hyA] at hval
    have hxB : x.1 ∈ B := x.2.resolve_left hxA
    have hyB : y.1 ∈ B := y.2.resolve_left hyA
    have hadjB : (G.induce B).Adj ⟨x.1, hxB⟩ ⟨y.1, hyB⟩ := hadj
    exact colB.valid hadjB (Fin.ext (by omega))

private lemma cliqueFree_join_or {V : Type*} {G : SimpleGraph V}
    {A B : Set V} (hAB : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) {k1 k2 : ℕ}
    (hcf : (G.induce (A ∪ B)).CliqueFree (k1 + k2)) :
    (G.induce A).CliqueFree k1 ∨ (G.induce B).CliqueFree k2 := by
  classical
  by_contra hboth
  push Not at hboth
  rcases hboth with ⟨hA, hB⟩
  rw [CliqueFree] at hA hB
  push Not at hA hB
  obtain ⟨KA, hKA⟩ := hA
  obtain ⟨KB, hKB⟩ := hB
  let fA : A → ↥(A ∪ B) := fun x => ⟨x.1, Or.inl x.2⟩
  let fB : B → ↥(A ∪ B) := fun x => ⟨x.1, Or.inr x.2⟩
  have hfA : Function.Injective fA := fun _ _ h => Subtype.ext (congrArg (Subtype.val : ↥(A ∪ B) → V) h)
  have hfB : Function.Injective fB := fun _ _ h => Subtype.ext (congrArg (Subtype.val : ↥(A ∪ B) → V) h)
  have h_disj : Disjoint (KA.image fA) (KB.image fB) := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    rw [Finset.mem_image] at hzA hzB
    obtain ⟨x, _, rfl⟩ := hzA
    obtain ⟨y, _, heq⟩ := hzB
    have hxy : x.1 = y.1 := congrArg Subtype.val heq.symm
    exact G.loopless.1 x.1 (hxy ▸ hAB x.1 x.2 y.1 y.2)
  apply hcf (KA.image fA ∪ KB.image fB)
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hx hy
    rcases hx with ⟨xA, hxA, rfl⟩ | ⟨xB, hxB, rfl⟩ <;>
    rcases hy with ⟨yA, hyA, rfl⟩ | ⟨yB, hyB, rfl⟩
    · exact hKA.1 hxA hyA (fun h => hxy (congrArg fA h))
    · exact hAB xA.1 xA.2 yB.1 yB.2
    · exact (hAB yA.1 yA.2 xB.1 xB.2).symm
    · exact hKB.1 hxB hyB (fun h => hxy (congrArg fB h))
  · rw [Finset.card_union_of_disjoint h_disj,
        Finset.card_image_of_injective _ hfA,
        Finset.card_image_of_injective _ hfB,
        hKA.2, hKB.2]

open scoped Classical in
private lemma colorable_induce_split {V : Type*} {G : SimpleGraph V}
    {U : Set V} {c d : ℕ} (hd : 1 ≤ d) (hdc : d < c)
    (hnot : ¬(G.induce U).Colorable (c - 1))
    (hcol : (G.induce U).Colorable c) :
    ∃ A B : Set V, A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧ A ∪ B = U ∧
      ¬(G.induce A).Colorable (d - 1) ∧
      ¬(G.induce B).Colorable (c - d - 1) := by
  obtain ⟨col⟩ := hcol
  let A : Set V := {u : V | ∃ hu : u ∈ U, (col ⟨u, hu⟩).val < d}
  let B : Set V := {u : V | ∃ hu : u ∈ U, d ≤ (col ⟨u, hu⟩).val}
  have hAU : A ⊆ U := fun _ ⟨hu, _⟩ => hu
  have hBU : B ⊆ U := fun _ ⟨hu, _⟩ => hu
  have h_disj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro u ⟨hu, hlt⟩ ⟨_, hge⟩
    omega
  have h_union : A ∪ B = U := by
    ext u
    simp only [A, B, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    · intro hu
      by_cases h : (col ⟨u, hu⟩).val < d
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, by omega⟩
  have hA_col : (G.induce A).Colorable d := by
    refine ⟨Coloring.mk (fun x => ⟨(col ⟨x.1, x.2.1⟩).val, x.2.2⟩) ?_⟩
    intro x y hadj heq
    have hval := congrArg (Fin.val : Fin d → ℕ) heq
    have hadj_U : (G.induce U).Adj ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩ := hadj
    exact col.valid hadj_U (Fin.ext hval)
  have hB_col : (G.induce B).Colorable (c - d) := by
    refine ⟨Coloring.mk (fun x => ⟨(col ⟨x.1, x.2.1⟩).val - d, by
      have := (col ⟨x.1, x.2.1⟩).isLt
      have := x.2.2
      omega⟩) ?_⟩
    intro x y hadj heq
    have hval := congrArg Fin.val heq
    dsimp only at hval
    have hx := x.2.2
    have hy := y.2.2
    have hadj_U : (G.induce U).Adj ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩ := hadj
    exact col.valid hadj_U (Fin.ext (by omega))
  refine ⟨A, B, hAU, hBU, h_disj, h_union, ?_, ?_⟩
  · intro hA_sm
    have h_join := colorable_join_of_colorable hA_sm hB_col
    rw [h_union, show d - 1 + (c - d) = c - 1 by omega] at h_join
    exact hnot h_join
  · intro hB_sm
    have h_join := colorable_join_of_colorable hA_col hB_sm
    rw [h_union, show d + (c - d - 1) = c - 1 by omega] at h_join
    exact hnot h_join

private lemma exists_exact_coloring_of_colorable {W : Type*} [Fintype W]
    (H : SimpleGraph W) (h_ne : Nonempty W) {k : ℕ} (hcol : H.Colorable k) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ k ∧ H.Colorable c ∧ ¬H.Colorable (c - 1) := by
  classical
  let c := Nat.find ⟨k, hcol⟩
  have hc_col : H.Colorable c := Nat.find_spec ⟨k, hcol⟩
  have hc_le : c ≤ k := Nat.find_min' ⟨k, hcol⟩ hcol
  have hc_pos : 1 ≤ c := by
    by_contra h0
    have hc0 : c = 0 := by omega
    rw [hc0] at hc_col
    obtain ⟨col⟩ := hc_col
    obtain ⟨w⟩ := h_ne
    exact Fin.elim0 (col w)
  have hc_not : ¬H.Colorable (c - 1) := Nat.find_min ⟨k, hcol⟩ (by omega)
  exact ⟨c, hc_pos, hc_le, hc_col, hc_not⟩

private lemma ge_three_of_colorable_not_colorable_cliqueFree {V : Type*} [Fintype V]
    {G : SimpleGraph V} {A : Set V} {c : ℕ} (hc : 1 ≤ c)
    (_hcol : (G.induce A).Colorable c) (hnot_c : ¬(G.induce A).Colorable (c - 1))
    (hcf_c : (G.induce A).CliqueFree c) : 3 ≤ c := by
  classical
  by_contra hlt3
  have hc12 : c = 1 ∨ c = 2 := by omega
  rcases hc12 with rfl | rfl
  · have hA_ne : Nonempty ↥A := by
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      exact hnot_c ⟨Coloring.mk (fun x => isEmptyElim x) (fun {x _} _ => isEmptyElim x)⟩
    obtain ⟨x⟩ := hA_ne
    exact hcf_c {x} ⟨by simp, by simp⟩
  · have h_edge : ∃ x y : ↥A, (G.induce A).Adj x y := by
      by_contra hno_edge
      push Not at hno_edge
      exact hnot_c ⟨Coloring.mk (fun _ => 0) (fun {x y} hadj => (hno_edge x y hadj).elim)⟩
    obtain ⟨x, y, hadj⟩ := h_edge
    have hxy : x ≠ y := (G.induce A).ne_of_adj hadj
    apply hcf_c {x, y}
    refine ⟨?_, Finset.card_pair hxy⟩
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (hpq rfl).elim
    · exact hadj
    · exact hadj.symm
    · exact (hpq rfl).elim

private lemma indep2_join_step {V : Type*} {G : SimpleGraph V}
    {U A B : Set V} {n k a b kA kB : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = k + 1)
    (ih : ∀ m < n, ∀ U' : Set V, U'.ncard = m →
      ∀ k' a' b' : ℕ, 2 ≤ a' → 2 ≤ b' → a' + b' = k' + 1 →
      (G.induce U').Colorable k' → ¬(G.induce U').Colorable (k' - 1) →
      (G.induce U').CliqueFree k' →
      ∃ S : Set V, S ⊆ U' ∧ ¬(G.induce S).Colorable (a' - 1) ∧
        ¬(G.induce (U' \ S)).Colorable (b' - 1))
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hAB_disj : Disjoint A B) (hAB_union : A ∪ B = U)
    (hAB_adj : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y)
    (hA_lt : A.ncard < n)
    (hkA_ge3 : 3 ≤ kA) (hkB_pos : 1 ≤ kB) (hkAB : kA + kB = k)
    (hA_col : (G.induce A).Colorable kA) (hA_not : ¬(G.induce A).Colorable (kA - 1))
    (hB_col : (G.induce B).Colorable kB) (hB_not : ¬(G.induce B).Colorable (kB - 1))
    (hA_cf : (G.induce A).CliqueFree kA) :
    ∃ S : Set V, S ⊆ U ∧ ¬(G.induce S).Colorable (a - 1) ∧
      ¬(G.induce (U \ S)).Colorable (b - 1) := by
  by_cases h_sub1 : kB + 2 ≤ a
  · obtain ⟨S1, hS1A, hS1_a, hS1_b⟩ :=
      ih A.ncard hA_lt A rfl kA (a - kB) b (by omega) hb (by omega) hA_col hA_not hA_cf
    refine ⟨S1 ∪ B, Set.union_subset (Set.Subset.trans hS1A hAU) hBU, ?_, ?_⟩
    · intro hcol
      have h_bd := colorable_of_join_colorable
        (fun x hx y hy => hAB_adj x (hS1A hx) y hy) hcol hS1_a hB_not
      omega
    · have h_diff : U \ (S1 ∪ B) = A \ S1 := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_union]
        constructor
        · rintro ⟨hxU, hnot⟩
          rw [← hAB_union] at hxU
          exact ⟨hxU.resolve_right (fun hxB => hnot (Or.inr hxB)), fun hxS1 => hnot (Or.inl hxS1)⟩
        · rintro ⟨hxA, hxS1⟩
          exact ⟨hAU hxA, fun h => h.elim hxS1 (Set.disjoint_left.mp hAB_disj hxA)⟩
      rw [h_diff]
      exact hS1_b
  · by_cases h_sub2 : kB + 2 ≤ b
    · obtain ⟨S1, hS1A, hS1_a, hS1_b⟩ :=
        ih A.ncard hA_lt A rfl kA a (b - kB) ha (by omega) (by omega) hA_col hA_not hA_cf
      refine ⟨S1, Set.Subset.trans hS1A hAU, hS1_a, ?_⟩
      have h_diff : U \ S1 = (A \ S1) ∪ B := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_union]
        constructor
        · rintro ⟨hxU, hxS1⟩
          rw [← hAB_union] at hxU
          rcases hxU with hxA | hxB
          · exact Or.inl ⟨hxA, hxS1⟩
          · exact Or.inr hxB
        · rintro (⟨hxA, hxS1⟩ | hxB)
          · exact ⟨hAU hxA, hxS1⟩
          · exact ⟨hBU hxB, fun hxS1 => Set.disjoint_left.mp hAB_disj (hS1A hxS1) hxB⟩
      rw [h_diff]
      intro hcol
      have h_bd := colorable_of_join_colorable
        (fun x hx y hy => hAB_adj x hx.1 y hy) hcol hS1_b hB_not
      omega
    · have ha_ge3 : 3 ≤ a := by omega
      obtain ⟨B1, B2, hB1B, hB2B, hB12_disj, hB12_union, hB1_not, hB2_not⟩ :=
        colorable_induce_split (by omega : 1 ≤ a - 2) (by omega : a - 2 < kB) hB_not hB_col
      obtain ⟨S1, hS1A, hS1_a, hS1_b⟩ :=
        ih A.ncard hA_lt A rfl kA 2 (kA - 1) (by omega) (by omega) (by omega) hA_col hA_not hA_cf
      refine ⟨S1 ∪ B1, Set.union_subset (Set.Subset.trans hS1A hAU) (Set.Subset.trans hB1B hBU), ?_, ?_⟩
      · intro hcol
        have h_bd := colorable_of_join_colorable
          (fun x hx y hy => hAB_adj x (hS1A hx) y (hB1B hy)) hcol hS1_a hB1_not
        omega
      · have h_diff : U \ (S1 ∪ B1) = (A \ S1) ∪ B2 := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_union]
          constructor
          · rintro ⟨hxU, hnot⟩
            rw [← hAB_union] at hxU
            rcases hxU with hxA | hxB
            · exact Or.inl ⟨hxA, fun hxS1 => hnot (Or.inl hxS1)⟩
            · rw [← hB12_union] at hxB
              exact Or.inr (hxB.resolve_left (fun hxB1 => hnot (Or.inr hxB1)))
          · rintro (⟨hxA, hxS1⟩ | hxB2)
            · refine ⟨hAU hxA, fun h => h.elim hxS1 (fun hxB1 => ?_)⟩
              exact Set.disjoint_left.mp hAB_disj hxA (hB1B hxB1)
            · refine ⟨hBU (hB2B hxB2), fun h => h.elim (fun hxS1 => ?_) (fun hxB1 => ?_)⟩
              · exact Set.disjoint_left.mp hAB_disj (hS1A hxS1) (hB2B hxB2)
              · exact Set.disjoint_left.mp hB12_disj hxB1 hxB2
        rw [h_diff]
        intro hcol
        have h_bd := colorable_of_join_colorable
          (fun x hx y hy => hAB_adj x hx.1 y (hB2B hy)) hcol hS1_b hB2_not
        omega

open scoped Classical in
private lemma indep2_splittable_on_set {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (h_indep2 : ∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
      G.Adj x y ∨ G.Adj x z ∨ G.Adj y z) :
    ∀ (n : ℕ) (U : Set V), U.ncard = n →
      ∀ (k a b : ℕ), 2 ≤ a → 2 ≤ b → a + b = k + 1 →
      (G.induce U).Colorable k → ¬(G.induce U).Colorable (k - 1) →
      (G.induce U).CliqueFree k →
      ∃ S : Set V, S ⊆ U ∧ ¬(G.induce S).Colorable (a - 1) ∧
        ¬(G.induce (U \ S)).Colorable (b - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U hU_ncard k a b ha hb hab hU_col hU_not hU_cf
    -- First, U is nonempty since k ≥ 3 and ¬Colorable (k - 1)!
    have hk_ge3 : 3 ≤ k := by omega
    have hU_ne : U.Nonempty := by
      by_contra h_emp
      rw [Set.not_nonempty_iff_eq_empty] at h_emp
      subst h_emp
      apply hU_not
      exact ⟨Coloring.mk (fun x => False.elim x.2) (fun {x _} _ => False.elim x.2)⟩
    -- Step 1: Check if there exists a proper subset U' ⊂ U with ¬(G.induce U').Colorable (k - 1)!
    by_cases h_non_crit : ∃ P : Set V, P ⊆ U ∧ P.Nonempty ∧ ¬(G.induce (U \ P)).Colorable (k - 1)
    · obtain ⟨P, hPU, ⟨p0, hp0⟩, hUP_not⟩ := h_non_crit
      have hUP_sub : U \ P ⊆ U := Set.sdiff_subset
      have hUP_lt : (U \ P).ncard < n := by
        rw [← hU_ncard]
        exact Set.ncard_lt_ncard ⟨hUP_sub, fun h => (h (hPU hp0)).2 hp0⟩
      have hUP_col : (G.induce (U \ P)).Colorable k := by
        obtain ⟨col⟩ := hU_col
        exact ⟨Coloring.mk (fun x => col ⟨x.1, hUP_sub x.2⟩) (fun hadj => col.valid hadj)⟩
      have hUP_cf : (G.induce (U \ P)).CliqueFree k := by
        intro K hK
        let f : ↥(U \ P) → ↥U := fun x => ⟨x.1, hUP_sub x.2⟩
        have hf : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (Subtype.val : ↥U → V) h)
        apply hU_cf (K.image f)
        refine ⟨?_, ?_⟩
        · intro x hx y hy hxy
          rw [Finset.mem_coe, Finset.mem_image] at hx hy
          obtain ⟨x', hx', rfl⟩ := hx
          obtain ⟨y', hy', rfl⟩ := hy
          exact hK.1 hx' hy' (fun h => hxy (congrArg f h))
        · rw [Finset.card_image_of_injective _ hf, hK.2]
      obtain ⟨S, hSU', hS_a, hS_b⟩ :=
        ih (U \ P).ncard hUP_lt (U \ P) rfl k a b ha hb hab hUP_col hUP_not hUP_cf
      refine ⟨S, Set.Subset.trans hSU' hUP_sub, hS_a, ?_⟩
      intro hUS_col
      apply hS_b
      obtain ⟨col⟩ := hUS_col
      exact ⟨Coloring.mk (fun x => col ⟨x.1, ⟨hUP_sub x.2.1, x.2.2⟩⟩) (fun hadj => col.valid hadj)⟩
    · -- Now U is k-critical: for every P ⊆ U with P.Nonempty, (G.induce (U \ P)).Colorable (k - 1)!
      push Not at h_non_crit
      -- Step 2: Check if (G.induce U)ᶜ is connected!
      obtain ⟨v0, hv0⟩ := hU_ne
      by_cases h_conn : ∀ u : ↥U, (G.induce U)ᶜ.Reachable ⟨v0, hv0⟩ u
      · -- (G.induce U)ᶜ IS CONNECTED!
        -- Apply critical_and_connected_compl_card_bound to G.induce U!
        have h_indep2_U : ∀ x y z : ↥U, x ≠ y → x ≠ z → y ≠ z →
            (G.induce U).Adj x y ∨ (G.induce U).Adj x z ∨ (G.induce U).Adj y z := by
          intro x y z hxy hxz hyz
          exact h_indep2 x.1 y.1 z.1 (Subtype.coe_ne_coe.mpr hxy)
            (Subtype.coe_ne_coe.mpr hxz) (Subtype.coe_ne_coe.mpr hyz)
        have h_crit_U : ∀ P : Set ↥U, P.Nonempty → ((G.induce U).induce (Pᶜ : Set ↥U)).Colorable (k - 1) := by
          intro P ⟨x0, hx0⟩
          have hP_val_sub : Subtype.val '' P ⊆ U := by
            rintro _ ⟨x, _, rfl⟩; exact x.2
          have hP_val_ne : (Subtype.val '' P).Nonempty := ⟨x0.1, x0, hx0, rfl⟩
          obtain ⟨col⟩ := h_non_crit (Subtype.val '' P) hP_val_sub hP_val_ne
          refine ⟨Coloring.mk (fun y => col ⟨y.1.1, ⟨y.1.2, fun ⟨z, hz, heq⟩ => y.2 (by
            have : z = y.1 := Subtype.ext heq
            rwa [← this])⟩⟩) ?_⟩
          intro y1 y2 hadj
          exact col.valid hadj
        have h_conn_U : ∀ x0 u : ↥U, (G.induce U)ᶜ.Reachable x0 u := by
          intro x0 u
          exact (h_conn x0).symm.trans (h_conn u)
        have h_card_U := critical_and_connected_compl_card_bound (by omega : 2 ≤ k)
          h_indep2_U hU_not h_crit_U h_conn_U
        have h_nonempty_U : Nonempty ↥U := ⟨⟨v0, hv0⟩⟩
        obtain ⟨s_U, hs_a, hs_b⟩ := splittable_of_card_ge_two_k_sub_one h_indep2_U ha hb hab
          (by omega : 2 * k - 1 ≤ Fintype.card ↥U) h_nonempty_U
        let S : Set V := Subtype.val '' s_U
        have hSU : S ⊆ U := by
          rintro _ ⟨x, _, rfl⟩; exact x.2
        refine ⟨S, hSU, ?_, ?_⟩
        · rintro ⟨col⟩
          apply hs_a
          refine ⟨Coloring.mk (fun x => col ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩) ?_⟩
          intro x y hadj
          exact col.valid hadj
        · rintro ⟨col⟩
          apply hs_b
          refine ⟨Coloring.mk (fun x => col ⟨x.1.1, ⟨x.1.2, fun ⟨z, hz, heq⟩ => x.2 (by
            have : z = x.1 := Subtype.ext heq
            rwa [← this])⟩⟩) ?_⟩
          intro x y hadj
          exact col.valid hadj
      · -- (G.induce U)ᶜ is DISCONNECTED!
        push Not at h_conn
        obtain ⟨u1, hu1_not_reach⟩ := h_conn
        let U1 : Set V := {u : V | ∃ hu : u ∈ U, (G.induce U)ᶜ.Reachable ⟨v0, hv0⟩ ⟨u, hu⟩}
        let U2 : Set V := U \ U1
        have hU1_sub : U1 ⊆ U := fun _ ⟨hu, _⟩ => hu
        have hU2_sub : U2 ⊆ U := Set.sdiff_subset
        have hU12_union : U1 ∪ U2 = U := Set.union_sdiff_cancel' (fun _ => id) hU1_sub
        have hU12_disj : Disjoint U1 U2 := disjoint_sdiff_self_right
        have hv0_U1 : v0 ∈ U1 := ⟨hv0, Reachable.refl _⟩
        have hu1_U2 : u1.1 ∈ U2 := ⟨u1.2, fun ⟨_, hr⟩ => hu1_not_reach hr⟩
        have hU1_lt : U1.ncard < n := by
          rw [← hU_ncard]
          exact Set.ncard_lt_ncard ⟨hU1_sub, fun h => (hu1_U2.2 (h u1.2))⟩
        have hU2_lt : U2.ncard < n := by
          rw [← hU_ncard]
          exact Set.ncard_lt_ncard ⟨hU2_sub, fun h => (h hv0).2 hv0_U1⟩
        have hU12_adj : ∀ x ∈ U1, ∀ y ∈ U2, G.Adj x y := by
          intro x ⟨hxU, hreach⟩ y ⟨hyU, hnot⟩
          by_contra hnot_adj
          have hxy : (⟨x, hxU⟩ : ↥U) ≠ ⟨y, hyU⟩ := by
            intro h
            have : x = y := congrArg Subtype.val h
            exact hnot (this ▸ ⟨hxU, hreach⟩)
          have h_compl_adj : (G.induce U)ᶜ.Adj ⟨x, hxU⟩ ⟨y, hyU⟩ := ⟨hxy, hnot_adj⟩
          exact hnot ⟨hyU, hreach.trans h_compl_adj.reachable⟩
        have hU1_col_k : (G.induce U1).Colorable k := by
          obtain ⟨col⟩ := hU_col
          exact ⟨Coloring.mk (fun x => col ⟨x.1, hU1_sub x.2⟩) (fun hadj => col.valid hadj)⟩
        have hU2_col_k : (G.induce U2).Colorable k := by
          obtain ⟨col⟩ := hU_col
          exact ⟨Coloring.mk (fun x => col ⟨x.1, hU2_sub x.2⟩) (fun hadj => col.valid hadj)⟩
        obtain ⟨k1, hk1_pos, _hk1_le, hU1_col, hU1_not⟩ :=
          exists_exact_coloring_of_colorable (G.induce U1) ⟨⟨v0, hv0_U1⟩⟩ hU1_col_k
        obtain ⟨k2, hk2_pos, _hk2_le, hU2_col, hU2_not⟩ :=
          exists_exact_coloring_of_colorable (G.induce U2) ⟨⟨u1.1, hu1_U2⟩⟩ hU2_col_k
        have hk12_eq : k1 + k2 = k := by
          have h_join_col := colorable_join_of_colorable hU1_col hU2_col
          rw [hU12_union] at h_join_col
          have h_ge : ¬k1 + k2 ≤ k - 1 := fun hle => hU_not (h_join_col.mono hle)
          have h_le : (k1 - 1) + (k2 - 1) + 2 ≤ k := by
            refine colorable_of_join_colorable hU12_adj ?_ hU1_not hU2_not
            rwa [hU12_union]
          omega
        have h_cf_or : (G.induce U1).CliqueFree k1 ∨ (G.induce U2).CliqueFree k2 := by
          apply cliqueFree_join_or hU12_adj
          rwa [hU12_union, hk12_eq]
        rcases h_cf_or with hcf1 | hcf2
        · have hk1_ge3 := ge_three_of_colorable_not_colorable_cliqueFree hk1_pos hU1_col hU1_not hcf1
          exact indep2_join_step ha hb hab ih hU1_sub hU2_sub hU12_disj hU12_union hU12_adj hU1_lt
            hk1_ge3 hk2_pos hk12_eq hU1_col hU1_not hU2_col hU2_not hcf1
        · have hk2_ge3 := ge_three_of_colorable_not_colorable_cliqueFree hk2_pos hU2_col hU2_not hcf2
          exact indep2_join_step ha hb hab ih hU2_sub hU1_sub hU12_disj.symm
            (by rw [Set.union_comm]; exact hU12_union)
            (fun x hx y hy => (hU12_adj y hy x hx).symm)
            hU2_lt hk2_ge3 hk1_pos (by omega) hU2_col hU2_not hU1_col hU1_not hcf2

open scoped Classical in
/--
Balogh, Kostochka, Prince, and Stiebitz [BKPS09] proved the conjecture for graphs with independence number 2.
-/
theorem erdos_628.variants.independence_number_2 (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG_indep : G.indepNum = 2)
    (k : ℕ)
    (hG_chrom : G.chromaticNumber = (k : ℕ∞))
    (hG_clique : G.CliqueFree k)
    (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞) := by
  have h_indep2 : ∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
      G.Adj x y ∨ G.Adj x z ∨ G.Adj y z := by
    intro x y z hxy hxz hyz
    by_contra hnone
    push Not at hnone
    have hind : G.IsIndepSet ({x, y, z} : Finset V) := by
      intro p hp q hq hpq
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
      · exact (hpq rfl).elim
      · exact hnone.1
      · exact hnone.2.1
      · exact fun h => hnone.1 h.symm
      · exact (hpq rfl).elim
      · exact hnone.2.2
      · exact fun h => hnone.2.1 h.symm
      · exact fun h => hnone.2.2 h.symm
      · exact (hpq rfl).elim
    have hcard_le := hind.card_le_indepNum
    rw [hG_indep, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton] at hcard_le
    · omega
    · simp [hyz]
    · simp [hxy, hxz]
  have hG_col : G.Colorable k := by
    rw [← chromaticNumber_le_iff_colorable, hG_chrom]
  have hG_not : ¬G.Colorable (k - 1) := by
    intro hcol
    have hle := hcol.chromaticNumber_le
    rw [hG_chrom] at hle
    have : k ≤ k - 1 := WithTop.coe_le_coe.mp hle
    omega
  have hU_col : (G.induce (Set.univ : Set V)).Colorable k := by
    obtain ⟨col⟩ := hG_col
    exact ⟨Coloring.mk (fun x => col x.1) (fun hadj => col.valid hadj)⟩
  have hU_not : ¬(G.induce (Set.univ : Set V)).Colorable (k - 1) := by
    rintro ⟨col⟩
    exact hG_not ⟨Coloring.mk (fun v => col ⟨v, trivial⟩) (fun hadj => col.valid hadj)⟩
  have hU_cf : (G.induce (Set.univ : Set V)).CliqueFree k := by
    intro K hK
    let f : ↥(Set.univ : Set V) → V := Subtype.val
    apply hG_clique (K.image f)
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact hK.1 hx' hy' (Subtype.coe_ne_coe.mp hxy)
    · rw [Finset.card_image_of_injective _ Subtype.val_injective, hK.2]
  obtain ⟨S, _hSU, hS_a, hS_b⟩ :=
    indep2_splittable_on_set h_indep2 (Set.univ : Set V).ncard Set.univ rfl k a b ha hb hab
      hU_col hU_not hU_cf
  refine ⟨S, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hle : (G.induce S).chromaticNumber ≤ ((a - 1 : ℕ) : ℕ∞) := by
      have : (a : ℕ∞) = ((a - 1 : ℕ) : ℕ∞) + 1 := by
        conv_lhs => rw [show a = (a - 1) + 1 by omega]
        push_cast
        rfl
      rw [this] at hlt
      exact Order.le_of_lt_add_one hlt
    exact hS_a (chromaticNumber_le_iff_colorable.mp hle)
  · by_contra hlt
    push Not at hlt
    have hle : (G.induce Sᶜ).chromaticNumber ≤ ((b - 1 : ℕ) : ℕ∞) := by
      have : (b : ℕ∞) = ((b - 1 : ℕ) : ℕ∞) + 1 := by
        conv_lhs => rw [show b = (b - 1) + 1 by omega]
        push_cast
        rfl
      rw [this] at hlt
      exact Order.le_of_lt_add_one hlt
    have hcol_compl := chromaticNumber_le_iff_colorable.mp hle
    apply hS_b
    obtain ⟨col⟩ := hcol_compl
    exact ⟨Coloring.mk (fun x => col ⟨x.1, x.2.2⟩) (fun hadj => col.valid hadj)⟩

end Erdos628

#print axioms Erdos23.erdos_23.variants.n1
#print axioms Erdos23.erdos_23.variants.n1_tight
#print axioms Erdos617.erdos_617.variants.r2
#print axioms Erdos617.erdos_617.variants.r_eq_3
#print axioms Erdos628.erdos_628.variants.k_5_a_3_b_3
#print axioms Erdos628.erdos_628.variants.independence_number_2

