import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
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

end Erdos617

#print axioms Erdos23.erdos_23.variants.n1
#print axioms Erdos23.erdos_23.variants.n1_tight
#print axioms Erdos617.erdos_617.variants.r2

