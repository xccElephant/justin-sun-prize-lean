import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Tauto

open Finset SimpleGraph
open scoped Nat

/-!
# Erdős Problem 835 and the Ma–Tang Theorem

This file is a self-contained formalization of Erdős Problem 835 and the results of
Jie Ma and Quanyu Tang, *A note on Erdős Problem #835* (2025/2026):
- Equivalence between Erdős's subset-coloring property `Property k` and
  `J(2 * k, k).chromaticNumber = k + 1` (`property_iff_chromaticNumber`).
- Johnson's upper bound on the independence number `α(J(n, k)) ≤ johnsonBound n 4 k`
  (`indepNum_johnson_le_johnsonBound`) and the resulting chromatic number lower bound
  (`div_johnsonBound_le_chromaticNum_johnson`).
- Monotonicity of Johnson graphs via graph homomorphisms `J(n₁, k₁) →g J(n₂, k₂)` whenever
  `k₁ ≤ k₂` and `n₁ - k₁ ≤ n₂ - k₂` (`johnsonHomOfLe`, `chromaticNumber_johnson_mono`).
- Proposition 2.1 of Ma–Tang (`ma_tang_prop_2_1`): if `J(2 * k, k)` is `(k + 1)`-colorable
  (or `χ(J(2 * k, k)) = k + 1`), then `t ∣ (k + t).choose (t - 1)` for all `1 ≤ t ≤ k`.
- Theorem 2.2 of Ma–Tang (`johnson_chromaticNumber_composite`): for all `k > 2` with `k + 1`
  composite, `k + 1 < J(2 * k, k).chromaticNumber` (and hence `¬ Property k`).
- Corollary for all odd `k > 2` (`johnson_chromaticNumber_odd`) and `k = 9`
  (`johnsonGraph_18_9_chromaticNumber`).
- Lemma 2.3 of Ma–Tang (`ma_tang_lemma_2_3`): when `k + 1` is prime, the divisibility condition
  `t ∣ (k + t).choose (t - 1)` holds for all `1 ≤ t ≤ k`.
-/

/-- A natural number `n` is composite if `1 < n` and `n` is not prime. -/
abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

namespace Finset
variable {α : Type*} {s t : Finset α}

lemma card_lt_card_iff_of_subset (hst : s ⊆ t) : #s < #t ↔ s ≠ t := by
  rw [← not_le, eq_iff_card_le_of_subset hst]

end Finset

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {n k : ℕ}

@[inherit_doc] scoped notation "α(" G ")" => indepNum G
@[inherit_doc] scoped notation "χ(" G ")" => chromaticNumber G

@[simp] lemma indepNum_of_isEmpty [IsEmpty V] : α(G) = 0 := by
  simp [indepNum, isNIndepSet_iff, Subsingleton.elim _ ∅]

@[simp] lemma indepNum_pos [Finite V] [Nonempty V] : 0 < α(G) := by
  cases nonempty_fintype V
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← Nat.add_one_le_iff]
  exact le_csSup ⟨Nat.card V, by simp [mem_upperBounds, isNIndepSet_iff, Finset.card_le_univ]⟩
    ⟨{v}, by simp [isNIndepSet_iff]⟩

/--
The Johnson graph $J(n, k)$ has as vertices the $k$-subsets of an $n$-set.
Two vertices are adjacent if their intersection has size $k - 1$.
-/
@[simps -isSimp]
def johnson (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // #s = k} where
  Adj s t := #(s.val ∩ t.val) + 1 = k
  symm.symm s t h := by simpa [inter_comm]
  loopless.irrefl := by simp +contextual

scoped notation "J(" n ", " k ")" => johnson n k

instance : DecidableRel J(n, k).Adj :=
  fun s t ↦ inferInstanceAs (Decidable (#(s.val ∩ t.val) + 1 = k))

lemma johnson_adj_iff_ge {s t : {s : Finset (Fin n) // #s = k}} :
    J(n, k).Adj s t ↔ s ≠ t ∧ k ≤ #(s.val ∩ t.val) + 1 := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  simp only [johnson_adj, le_antisymm_iff (α := ℕ), ne_eq, Subtype.mk.injEq, and_congr_left_iff]
  rintro h
  constructor
  · rintro hst rfl
    simp at hst
    omega
  · rintro hst
    rw [Nat.add_one_le_iff, ← hs, card_lt_card_iff_of_subset inter_subset_left]
    simp only [ne_eq, inter_eq_left]
    contrapose! hst
    exact eq_of_subset_of_card_le hst (by simp [*])

lemma not_johnson_adj_iff_lt {s t : {s : Finset (Fin n) // #s = k}} :
    ¬ J(n, k).Adj s t ↔ s = t ∨ #(s.val ∩ t.val) + 1 < k := by
  simp [johnson_adj_iff_ge]
  tauto

lemma lt_chromaticNumber_iff_not_colorable : n < G.chromaticNumber ↔ ¬ G.Colorable n := by
  rw [← chromaticNumber_le_iff_colorable, not_le]

lemma le_chromaticNumber_iff_not_colorable (hn : n ≠ 0) :
    n ≤ G.chromaticNumber ↔ ¬ G.Colorable (n - 1) := by
  let n + 1 := n; simp [ENat.add_one_le_iff, lt_chromaticNumber_iff_not_colorable]

lemma card_div_indepNum_le_chromaticNumber : ⌈(Nat.card V / α(G) : ℚ≥0)⌉₊ ≤ G.chromaticNumber := by
  cases finite_or_infinite V
  swap; · simp
  cases nonempty_fintype V
  simp only [Nat.card_eq_fintype_card, le_chromaticNumber_iff_coloring, Nat.ceil_le]
  refine fun m c ↦ div_le_of_le_mul₀ (by simp) (by simp) ?_
  norm_cast
  rw [← mul_one (Fintype.card V), ← Fintype.card_fin m]
  refine Finset.card_mul_le_card_mul (c · = ·)
    (by simp [Finset.bipartiteAbove, Finset.filter_nonempty_iff])
    fun b _ ↦ IsIndepSet.card_le_indepNum ?_
  simpa [IsIndepSet, Set.Pairwise, Coloring.colorClass] using
    fun x hx y hy _ ↦ c.not_adj_of_mem_colorClass hx hy

end SimpleGraph

namespace Erdos835

variable {n k : ℕ}

/--
The property that for a given $k$, the $k$-subsets of a $2k$-set can be colored with $k+1$ colors
such that any $(k+1)$-subset contains all colors.
-/
def Property (k : ℕ) : Prop :=
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  ∃ c : K → Fin (k + 1),
    ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
      (image c {s : K | s.val ⊂ A}) = (univ : Finset (Fin (k + 1)))

private lemma card_filter_ssubset_eq (k : ℕ) {A : Finset (Fin (2 * k))} (hA : #A = k + 1) :
    #({s : {s : Finset (Fin (2 * k)) // #s = k} | s.val ⊂ A}) = k + 1 := by
  let K := {s : Finset (Fin (2 * k)) // #s = k}
  let S : Finset K := {s : K | s.val ⊂ A}
  let emb : K ↪ Finset (Fin (2 * k)) := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : S.map emb = A.powersetCard k := by
    ext u
    simp only [S, mem_map, mem_filter, mem_univ, true_and, emb, Function.Embedding.coeFn_mk,
      mem_powersetCard, Finset.ssubset_iff_subset_ne]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨hu, _⟩, rfl⟩
      exact ⟨hu, ha⟩
    · rintro ⟨huA, huk⟩
      refine ⟨⟨u, huk⟩, ⟨huA, ?_⟩, rfl⟩
      intro h_eq
      rw [← h_eq] at hA
      change #u = k + 1 at hA
      omega
  have hcard := congr_arg Finset.card hmap
  rw [card_map, card_powersetCard, hA, Nat.choose_succ_self_right] at hcard
  exact hcard

private lemma adj_of_ssubset_of_ne {k : ℕ} {A : Finset (Fin (2 * k))} (hA : #A = k + 1)
    {s t : {s : Finset (Fin (2 * k)) // #s = k}} (hs : s.val ⊂ A) (ht : t.val ⊂ A) (hne : s ≠ t) :
    J(2 * k, k).Adj s t := by
  rw [johnson_adj_iff_ge]
  refine ⟨hne, ?_⟩
  have hu : #(s.val ∪ t.val) ≤ k + 1 := by
    rw [← hA]
    exact card_le_card (union_subset hs.subset ht.subset)
  have h_inter := card_union_add_card_inter s.val t.val
  rw [s.prop, t.prop] at h_inter
  omega

/--
Problem 1.1 is equivalent to Problem 1.3: `J(2 * k, k).chromaticNumber = k + 1` iff `Property k`.
-/
theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    (J(2 * k, k).chromaticNumber = k + 1) ↔
    Property k := by
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  have h_lower : (k + 1 : ℕ∞) ≤ J(2 * k, k).chromaticNumber := by
    have hne : ((univ : Finset (Fin (2 * k))).powersetCard (k + 1)).Nonempty := by
      rw [powersetCard_nonempty]
      simp only [card_univ, Fintype.card_fin]
      omega
    obtain ⟨A, hA⟩ := hne
    rw [mem_powersetCard] at hA
    let S : Finset K := {s : K | s.val ⊂ A}
    have hclique : J(2 * k, k).IsClique (S : Set K) := by
      intro s hs t ht hne
      simp only [coe_filter, mem_univ, true_and, S] at hs ht
      exact adj_of_ssubset_of_ne hA.2 hs ht hne
    have hle := hclique.card_le_chromaticNumber
    rw [card_filter_ssubset_eq k hA.2] at hle
    exact_mod_cast hle
  have h_col_iff : (J(2 * k, k).chromaticNumber = k + 1) ↔ J(2 * k, k).Colorable (k + 1) := by
    rw [show (k : ℕ∞) + 1 = ((k + 1 : ℕ) : ℕ∞) by push_cast; rfl,
      ← chromaticNumber_le_iff_colorable, le_antisymm_iff]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h_lower⟩⟩
  rw [h_col_iff]
  constructor
  · rintro ⟨c⟩
    refine ⟨c, fun A hA ↦ ?_⟩
    let S : Finset K := {s : K | s.val ⊂ A}
    have hinj : Set.InjOn c (S : Set K) := by
      intro s hs t ht h_eq
      by_contra hne
      simp only [coe_filter, mem_univ, true_and, S] at hs ht
      exact c.valid (adj_of_ssubset_of_ne hA hs ht hne) h_eq
    refine eq_of_subset_of_card_le (subset_univ _) ?_
    rw [card_image_of_injOn hinj, card_filter_ssubset_eq k hA, card_univ, Fintype.card_fin]
  · rintro ⟨c, hc⟩
    refine ⟨Coloring.mk c fun {s t} hadj ↦ ?_⟩
    have hne : s ≠ t := hadj.ne
    rw [johnson_adj] at hadj
    let A : Finset (Fin (2 * k)) := s.val ∪ t.val
    have hA : #A = k + 1 := by
      have h_inter := card_union_add_card_inter s.val t.val
      rw [s.prop, t.prop] at h_inter
      change #(s.val ∪ t.val) = k + 1
      omega
    have hsA : s.val ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, by
      intro h; have := congr_arg Finset.card h; rw [s.prop, hA] at this; omega⟩
    have htA : t.val ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_right, by
      intro h; have := congr_arg Finset.card h; rw [t.prop, hA] at this; omega⟩
    let S : Finset K := {u : K | u.val ⊂ A}
    have h_img : #(image c S) = #S := by
      rw [hc A hA, card_univ, Fintype.card_fin, card_filter_ssubset_eq k hA]
    have hinj : Set.InjOn c (S : Set K) := card_image_iff.mp h_img
    intro heq
    apply hne
    exact hinj (mem_filter.mpr ⟨mem_univ _, hsA⟩) (mem_filter.mpr ⟨mem_univ _, htA⟩) heq

/-- Johnson's upper bound on the maximum size `A(n, d, w)` of an `n`-dimensional binary code of
distance `d` and weight `w`:
* If `d > 2 * w`, then `A(n, d, w) = 1`.
* If `d ≤ 2 * w`, then `A(n, d, w) ≤ ⌊n / w * A(n - 1, d, w - 1)⌋`. -/
def johnsonBound : ℕ → ℕ → ℕ → ℕ
  | 0, _d, _w => 1
  | _n, _d, 0 => 1
  | n + 1, d, w + 1 => if 2 * (w + 1) < d then 1 else (n + 1) * johnsonBound n d w / (w + 1)

private lemma map_succAboveEmb_filter {n : ℕ} (x : Fin (n + 1)) (s : Finset (Fin (n + 1))) :
    (univ.filter (fun i : Fin n ↦ x.succAbove i ∈ s)).map x.succAboveEmb =
      s.erase x := by
  ext y
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.succAboveEmb_apply, mem_erase]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Fin.succAbove_ne x i, hi⟩
  · rintro ⟨hyx, hys⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hyx
    exact ⟨i, hys, rfl⟩

private lemma card_indepSet_johnson_le_johnsonBound :
    ∀ (n k : ℕ) (F : Finset {s : Finset (Fin n) // #s = k}),
      J(n, k).IsIndepSet (F : Set {s : Finset (Fin n) // #s = k}) → #F ≤ johnsonBound n 4 k
  | 0, k, F, _ => by
    have : Subsingleton {s : Finset (Fin 0) // #s = k} :=
      ⟨fun a b ↦ Subtype.ext (Subsingleton.elim a.val b.val)⟩
    simpa [johnsonBound] using Finset.card_le_one_of_subsingleton F
  | n + 1, 0, F, _ => by
    have : Subsingleton {s : Finset (Fin (n + 1)) // #s = 0} :=
      ⟨fun a b ↦ Subtype.ext (by rw [card_eq_zero.mp a.prop, card_eq_zero.mp b.prop])⟩
    simpa [johnsonBound] using Finset.card_le_one_of_subsingleton F
  | n + 1, 1, F, hF => by
    simp only [johnsonBound, show 2 * (0 + 1) < 4 by omega, ↓reduceIte]
    rw [Finset.card_le_one_iff]
    intro s t hs ht
    by_contra hne
    have hadj : J(n + 1, 1).Adj s t := by
      rw [johnson_adj_iff_ge]
      exact ⟨hne, by omega⟩
    exact hF hs ht hne hadj
  | n + 1, w + 2, F, hF => by
    simp only [johnsonBound, show ¬(2 * (w + 1 + 1) < 4) by omega, ↓reduceIte]
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h_dc := Finset.card_mul_le_card_mul
      (r := fun (s : {s : Finset (Fin (n + 1)) // #s = w + 2}) (x : Fin (n + 1)) ↦ x ∈ s.val)
      (s := F) (t := (univ : Finset (Fin (n + 1))))
      (m := w + 2) (n := johnsonBound n 4 (w + 1))
      (fun s _ ↦ by
        simp only [bipartiteAbove]
        have h_eq : univ.filter (fun x : Fin (n + 1) ↦ x ∈ s.val) = s.val := by
          ext x; simp
        rw [h_eq, s.prop])
      (fun x _ ↦ by
        simp only [bipartiteBelow]
        let Fx := F.filter (fun s ↦ x ∈ s.val)
        let φ : {s // s ∈ Fx} → {u : Finset (Fin n) // #u = w + 1} := fun ⟨s, hs⟩ ↦
          ⟨univ.filter (fun i : Fin n ↦ x.succAbove i ∈ s.val), by
            have hm := congr_arg Finset.card (map_succAboveEmb_filter x s.val)
            rw [card_map, card_erase_of_mem (mem_filter.mp hs).2, s.prop] at hm
            exact hm⟩
        have hφ_inj : Set.InjOn φ (Fx.attach : Set {s // s ∈ Fx}) := by
          rintro ⟨s, hs⟩ _ ⟨t, ht⟩ _ h_eq
          apply Subtype.ext
          apply Subtype.ext
          have hm := congr_arg (fun u : Finset (Fin n) ↦ u.map x.succAboveEmb)
            (Subtype.mk.inj h_eq)
          rw [map_succAboveEmb_filter, map_succAboveEmb_filter] at hm
          rw [← insert_erase (mem_filter.mp hs).2, hm, insert_erase (mem_filter.mp ht).2]
        let F' := Fx.attach.image φ
        have hF'_indep : J(n, w + 1).IsIndepSet (F' : Set {u : Finset (Fin n) // #u = w + 1}) := by
          intro u hu v hv hne hadj
          simp only [F', coe_image, coe_attach, Set.image_univ, Set.mem_range] at hu hv
          rcases hu with ⟨⟨s, hs⟩, rfl⟩
          rcases hv with ⟨⟨t, ht⟩, rfl⟩
          have hst_ne : s ≠ t := by
            rintro rfl
            exact hne rfl
          rw [johnson_adj] at hadj
          have h_inter_eq :
              (φ ⟨s, hs⟩).val ∩ (φ ⟨t, ht⟩).val =
                univ.filter (fun i : Fin n ↦ x.succAbove i ∈ s.val ∩ t.val) := by
            ext i; simp [φ]
          have h_inter_map :
              ((φ ⟨s, hs⟩).val ∩ (φ ⟨t, ht⟩).val).map x.succAboveEmb =
                (s.val ∩ t.val).erase x := by
            rw [h_inter_eq, map_succAboveEmb_filter]
          have h_card := congr_arg Finset.card h_inter_map
          rw [card_map, card_erase_of_mem (mem_inter.mpr ⟨(mem_filter.mp hs).2,
            (mem_filter.mp ht).2⟩)] at h_card
          have hadj' : J(n + 1, w + 2).Adj s t := by
            rw [johnson_adj_iff_ge]
            refine ⟨hst_ne, ?_⟩
            have h_sub : 1 ≤ #(s.val ∩ t.val) :=
              Finset.card_pos.mpr ⟨x, mem_inter.mpr ⟨(mem_filter.mp hs).2, (mem_filter.mp ht).2⟩⟩
            omega
          exact hF (mem_filter.mp hs).1 (mem_filter.mp ht).1 hst_ne hadj'
        have h_le := card_indepSet_johnson_le_johnsonBound n (w + 1) F' hF'_indep
        rw [card_image_of_injOn hφ_inj, card_attach] at h_le
        exact h_le)
    simpa [card_univ, Fintype.card_fin] using h_dc

/-- Johnson's bound for the independence number of the Johnson graph. -/
lemma indepNum_johnson_le_johnsonBound : α(J(n, k)) ≤ johnsonBound n 4 k := by
  obtain ⟨F, hF⟩ := J(n, k).exists_isNIndepSet_indepNum
  rw [← hF.card_eq]
  exact card_indepSet_johnson_le_johnsonBound n k F hF.isIndepSet

/-- Johnson's bound for the chromatic number of the Johnson graph. -/
lemma div_johnsonBound_le_chromaticNum_johnson :
    ⌈(n.choose k / johnsonBound n 4 k : ℚ≥0)⌉₊ ≤ χ(J(n, k)) := by
  obtain hnk | hkn := lt_or_ge n k
  · simp [Nat.choose_eq_zero_of_lt, *]
  have : Nonempty {s : Finset (Fin n) // #s = k} := by
    simpa [Finset.Nonempty] using Finset.powersetCard_nonempty (s := .univ).2 <| by simpa
  grw [← card_div_indepNum_le_chromaticNumber, indepNum_johnson_le_johnsonBound] <;> simp

/-- Graph homomorphism `J(n₁, k₁) →g J(n₂, k₂)` whenever `k₁ ≤ k₂` and `n₁ + (k₂ - k₁) ≤ n₂`,
obtained by embedding `Fin n₁` into the first `n₁` elements of `Fin n₂` and padding with `k₂ - k₁`
fixed elements from `{n₁, ..., n₁ + (k₂ - k₁) - 1}`. -/
def johnsonHomOfLe {n₁ k₁ n₂ k₂ : ℕ} (hk : k₁ ≤ k₂) (hn : n₁ + (k₂ - k₁) ≤ n₂) :
    J(n₁, k₁) →g J(n₂, k₂) where
  toFun s :=
    let embL : Fin n₁ ↪ Fin n₂ := Fin.castLEEmb (by omega : n₁ ≤ n₂)
    let embR : Fin (k₂ - k₁) ↪ Fin n₂ :=
      ⟨fun i ↦ ⟨n₁ + i.1, by omega⟩, fun i j hij ↦ by ext; simpa [Fin.ext_iff] using hij⟩
    ⟨s.val.map embL ∪ univ.map embR, by
      have hdisj : Disjoint (s.val.map embL) (univ.map embR) := by
        rw [Finset.disjoint_left]
        rintro x hxL hxR
        rw [mem_map] at hxL hxR
        rcases hxL with ⟨a, _, rfl⟩
        rcases hxR with ⟨b, _, h_eq⟩
        have : n₁ + b.1 = a.1 := congr_arg Fin.val h_eq
        omega
      rw [card_union_of_disjoint hdisj, card_map, card_map, card_univ, Fintype.card_fin, s.prop]
      omega⟩
  map_rel' {s t} hadj := by
    let embL : Fin n₁ ↪ Fin n₂ := Fin.castLEEmb (by omega : n₁ ≤ n₂)
    let embR : Fin (k₂ - k₁) ↪ Fin n₂ :=
      ⟨fun i ↦ ⟨n₁ + i.1, by omega⟩, fun i j hij ↦ by ext; simpa [Fin.ext_iff] using hij⟩
    rw [johnson_adj] at hadj ⊢
    change #((s.val.map embL ∪ univ.map embR) ∩ (t.val.map embL ∪ univ.map embR)) + 1 = k₂
    rw [← inter_union_distrib_right, ← Finset.map_inter]
    have hdisj : Disjoint ((s.val ∩ t.val).map embL) (univ.map embR) := by
      rw [Finset.disjoint_left]
      rintro x hxL hxR
      rw [mem_map] at hxL hxR
      rcases hxL with ⟨a, _, rfl⟩
      rcases hxR with ⟨b, _, h_eq⟩
      have : n₁ + b.1 = a.1 := congr_arg Fin.val h_eq
      omega
    rw [card_union_of_disjoint hdisj, card_map, card_map, card_univ, Fintype.card_fin]
    omega

/-- Monotonicity of the chromatic number of Johnson graphs: if `k₁ ≤ k₂` and `n₁ + (k₂ - k₁) ≤ n₂`,
then `χ(J(n₁, k₁)) ≤ χ(J(n₂, k₂))`. -/
lemma chromaticNumber_johnson_mono {n₁ k₁ n₂ k₂ : ℕ} (hk : k₁ ≤ k₂) (hn : n₁ + (k₂ - k₁) ≤ n₂) :
    J(n₁, k₁).chromaticNumber ≤ J(n₂, k₂).chromaticNumber :=
  chromaticNumber_mono_of_hom (johnsonHomOfLe hk hn)

/-- Hypergraph packing upper bound (Claims 1 and 2 of Ma–Tang): for any independent set `F` in
`J(n, t)` with `1 ≤ t`, we have `#F * t ≤ n.choose (t - 1)`. -/
lemma card_indepSet_mul_le_choose_pred {n t : ℕ} (ht : 1 ≤ t)
    (F : Finset {s : Finset (Fin n) // #s = t})
    (hF : J(n, t).IsIndepSet (F : Set {s : Finset (Fin n) // #s = t})) :
    #F * t ≤ n.choose (t - 1) := by
  have h_dc := Finset.card_mul_le_card_mul
    (r := fun (s : {s : Finset (Fin n) // #s = t}) (R : Finset (Fin n)) ↦ R ⊆ s.val)
    (s := F) (t := (univ : Finset (Fin n)).powersetCard (t - 1))
    (m := t) (n := 1)
    (fun s _ ↦ by
      simp only [bipartiteAbove]
      have h_eq : ((univ : Finset (Fin n)).powersetCard (t - 1)).filter (fun R ↦ R ⊆ s.val) =
          s.val.powersetCard (t - 1) := by
        ext R
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
        tauto
      rw [h_eq, card_powersetCard, s.prop]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht
      simp [Nat.add_comm 1 m, Nat.choose_succ_self_right])
    (fun R hR ↦ by
      simp only [bipartiteBelow]
      rw [mem_powersetCard] at hR
      rw [Finset.card_le_one_iff]
      intro s₁ s₂ hs₁ hs₂
      rw [mem_filter] at hs₁ hs₂
      by_contra hne
      have hsub : R ⊆ s₁.val ∩ s₂.val := subset_inter hs₁.2 hs₂.2
      have hcard := card_le_card hsub
      rw [hR.2] at hcard
      have hadj : J(n, t).Adj s₁ s₂ := by
        rw [johnson_adj_iff_ge]
        exact ⟨hne, by omega⟩
      exact hF hs₁.1 hs₂.1 hne hadj)
  simpa [card_powersetCard, card_univ, Fintype.card_fin] using h_dc

/-- Hypergraph packing upper bound on the independence number of `J(n, t)` (Claims 1 and 2 of
Ma–Tang): for `1 ≤ t`, `α(J(n, t)) ≤ n.choose (t - 1) / t`. -/
lemma indepNum_johnson_le_choose_pred_div {n t : ℕ} (ht : 1 ≤ t) :
    α(J(n, t)) ≤ n.choose (t - 1) / t := by
  obtain ⟨F, hF⟩ := J(n, t).exists_isNIndepSet_indepNum
  rw [← hF.card_eq, Nat.le_div_iff_mul_le ht]
  exact card_indepSet_mul_le_choose_pred ht F hF.isIndepSet

/-- Divisibility condition for `J(k + t, t)`: if `J(k + t, t)` is `(k + 1)`-colorable and `1 ≤ t`,
then `t ∣ (k + t).choose (t - 1)`. -/
theorem dvd_choose_of_colorable_johnson_add {k t : ℕ} (ht : 1 ≤ t)
    (hc : J(k + t, t).Colorable (k + 1)) :
    t ∣ (k + t).choose (t - 1) := by
  rcases hc with ⟨c⟩
  have h_dc := Finset.card_mul_le_card_mul
    (r := fun (v : {s : Finset (Fin (k + t)) // #s = t}) (i : Fin (k + 1)) ↦ c v = i)
    (s := univ) (t := univ)
    (m := 1) (n := (k + t).choose (t - 1) / t)
    (fun v _ ↦ by
      simp only [bipartiteAbove, Nat.add_one_le_iff, Finset.card_pos]
      exact ⟨c v, by simp⟩)
    (fun i _ ↦ by
      simp only [bipartiteBelow]
      let Fi := univ.filter (fun v : {s : Finset (Fin (k + t)) // #s = t} ↦ c v = i)
      have hFi : J(k + t, t).IsIndepSet (Fi : Set {s : Finset (Fin (k + t)) // #s = t}) := by
        intro u hu v hv _ hadj
        simp only [Fi, coe_filter, mem_univ, true_and] at hu hv
        exact c.valid hadj (hu.trans hv.symm)
      rw [Nat.le_div_iff_mul_le ht]
      exact card_indepSet_mul_le_choose_pred ht Fi hFi)
  have h_card_univ : #(univ : Finset {s : Finset (Fin (k + t)) // #s = t}) = (k + t).choose t := by
    simp only [card_univ, Fintype.card_subtype]
    have h_pc : ({x : Finset (Fin (k + t)) | #x = t} : Finset _) = univ.powersetCard t := by
      ext x; simp
    rw [h_pc, card_powersetCard, card_univ, Fintype.card_fin]
  rw [h_card_univ, card_univ, Fintype.card_fin, mul_one] at h_dc
  have h_mul := Nat.mul_le_mul_right t h_dc
  have h_id := Nat.choose_succ_right_eq (k + t) (t - 1)
  have h_t1 : t - 1 + 1 = t := by omega
  have h_kt : k + t - (t - 1) = k + 1 := by omega
  rw [h_t1, h_kt] at h_id
  have h_div_le : (k + t).choose (t - 1) / t * t ≤ (k + t).choose (t - 1) :=
    Nat.div_mul_le_self _ _
  have h_eq : (k + t).choose (t - 1) / t * t = (k + t).choose (t - 1) := by
    nlinarith
  exact ⟨(k + t).choose (t - 1) / t, by linarith⟩

/-- **Proposition 2.1 of Ma–Tang (2025/2026)**:
If `J(2 * k, k)` is `(k + 1)`-colorable (or `χ(J(2 * k, k)) = k + 1`), then for every integer `t`
with `1 ≤ t ≤ k`, we have `t ∣ (k + t).choose (t - 1)`. -/
theorem ma_tang_prop_2_1 {k t : ℕ} (ht₁ : 1 ≤ t) (ht₂ : t ≤ k)
    (hc : J(2 * k, k).Colorable (k + 1)) :
    t ∣ (k + t).choose (t - 1) := by
  rcases hc with ⟨c⟩
  have hc' : J(k + t, t).Colorable (k + 1) :=
    ⟨c.comp (johnsonHomOfLe ht₂ (by omega))⟩
  exact dvd_choose_of_colorable_johnson_add ht₁ hc'

/-- Variant of Proposition 2.1 stated with `J(2 * k, k).chromaticNumber = k + 1`. -/
theorem ma_tang_prop_2_1_of_chromaticNumber {k t : ℕ} (ht₁ : 1 ≤ t) (ht₂ : t ≤ k)
    (hχ : J(2 * k, k).chromaticNumber = k + 1) :
    t ∣ (k + t).choose (t - 1) := by
  apply ma_tang_prop_2_1 ht₁ ht₂
  rw [← chromaticNumber_le_iff_colorable, hχ]
  norm_cast

/-- **Theorem 2.2 of Ma–Tang (2025/2026)**:
If `k > 2` and `k + 1` is composite (not prime), then `k + 1 < J(2 * k, k).chromaticNumber`. -/
theorem johnson_chromaticNumber_composite (k : ℕ) (hk : 2 < k) (h : (k + 1).Composite) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  rw [show (k : ℕ∞) + 1 = ((k + 1 : ℕ) : ℕ∞) by push_cast; rfl,
    lt_chromaticNumber_iff_not_colorable]
  intro hc
  let p := (k + 1).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ k + 1 := Nat.minFac_dvd (k + 1)
  have hp_le : p ≤ k + 1 := Nat.minFac_le (by omega)
  have hp_ne : p ≠ k + 1 := by
    intro h_eq
    exact h.2 (h_eq ▸ hp)
  have hp_lt : p < k + 1 := lt_of_le_of_ne hp_le hp_ne
  have hp_two : 2 ≤ p := hp.two_le
  have h_prop := ma_tang_prop_2_1 (by omega : 1 ≤ p) (by omega : p ≤ k) hc
  have : Fact p.Prime := ⟨hp⟩
  have h_lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := k + p) (k := p - 1) (p := p)
  obtain ⟨q, hq⟩ := hp_dvd
  have hq_pos : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq_pos
    · omega
    · exact hq_pos
  have h_kp_mod : (k + p) % p = p - 1 := by
    have h_eq : k + p = p - 1 + p * q := by omega
    rw [h_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have h_p1_mod : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have h_p1_div : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h_kp_mod, h_p1_mod, h_p1_div, Nat.choose_self, Nat.choose_zero_right, mul_one] at h_lucas
  have h_mod_zero : (k + p).choose (p - 1) % p = 0 := Nat.mod_eq_zero_of_dvd h_prop
  rw [Nat.ModEq, h_mod_zero, Nat.mod_eq_of_lt (by omega : 1 < p)] at h_lucas
  omega

/-- Corollary of Ma–Tang Theorem 2.2: `¬ Property k` for all `k > 2` with `k + 1` composite. -/
theorem not_property_of_composite (k : ℕ) (hk : 2 < k) (h : (k + 1).Composite) :
    ¬ Property k := by
  rw [← property_iff_chromaticNumber k (by omega)]
  exact (johnson_chromaticNumber_composite k hk h).ne'

/-- Ma and Tang's result implies the cases for odd `k > 2`. -/
theorem johnsonGraph_chromaticNumber_odd_of_johnson_chromaticNumber_composite :
    (∀ k : ℕ, 2 < k → (k + 1).Composite → k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ k : ℕ, 2 < k → Odd k → k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h k hk h_odd
  refine h k hk ⟨by omega, ?_⟩
  rw [Nat.not_prime_iff_exists_dvd_lt (by omega)]
  refine ⟨2, even_iff_two_dvd.mp (Odd.add_one h_odd), by omega⟩

/-- The chromatic number of `J(2 * k, k)` is `> k + 1` for all odd `k > 2`. -/
theorem johnson_chromaticNumber_odd (k : ℕ) (hk : 2 < k) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber :=
  johnsonGraph_chromaticNumber_odd_of_johnson_chromaticNumber_composite
    johnson_chromaticNumber_composite k hk h

/-- For `3 ≤ k ≤ 300` odd, the chromatic number of `J(2 * k, k)` is greater than `k + 1`. -/
theorem chromaticNumber_johnson_2k_k_lower_bound_odd (hk : 3 ≤ k) (_hk' : k ≤ 300)
    (hk_odd : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber :=
  johnson_chromaticNumber_odd k (by omega) hk_odd

/-- The chromatic number of `J(18, 9)` is strictly greater than `9 + 1 = 10`. -/
theorem johnsonGraph_18_9_chromaticNumber : J(18, 9).chromaticNumber > 9 + 1 :=
  johnson_chromaticNumber_odd 9 (by omega) ⟨4, by ring⟩

/-- **Lemma 2.3 of Ma–Tang (2025/2026)**:
If `k ≥ 2` and `k + 1` is prime, then for every `1 ≤ t ≤ k`, `t ∣ (k + t).choose (t - 1)`. -/
theorem ma_tang_lemma_2_3 (k t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ k) (hp : (k + 1).Prime) :
    t ∣ (k + t).choose (t - 1) := by
  have h_id := Nat.choose_succ_right_eq (k + t) (t - 1)
  have h_t1 : t - 1 + 1 = t := by omega
  have h_kt : k + t - (t - 1) = k + 1 := by omega
  rw [h_t1, h_kt] at h_id
  have h_dvd_mul : t ∣ (k + t).choose (t - 1) * (k + 1) :=
    ⟨(k + t).choose t, by linarith⟩
  have h_coprime : Nat.Coprime t (k + 1) :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ht₁ (by omega))).symm
  exact h_coprime.dvd_of_dvd_mul_right h_dvd_mul

private def recolor5 (c0 c1 c2 c3 x : Fin 5) : Fin 5 :=
  if x = c0 then 0
  else if x = c1 then 1
  else if x = c2 then 2
  else if x = c3 then 3
  else 4

set_option synthInstance.maxSize 500 in
private lemma recolor5_ne :
    ∀ c0 : Fin 5,
    ∀ c1 : Fin 5, (_ : c1 ≠ c0) →
    ∀ c2 : Fin 5, (_ : c2 ≠ c0) → (_ : c2 ≠ c1) →
    ∀ c3 : Fin 5, (_ : c3 ≠ c0) → (_ : c3 ≠ c1) → (_ : c3 ≠ c2) →
    ∀ x y : Fin 5, (_ : x ≠ y) →
    recolor5 c0 c1 c2 c3 x ≠ recolor5 c0 c1 c2 c3 y := by
  decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Finite 5-colorability refutation on the 16-vertex subgraph of `J(6, 3)` consisting of all
3-subsets of `Fin 6` that contain `0` or `1`, after symmetry breaking on the 4-clique
`v0, v1, v2, v3`. -/
private lemma j63_no_5_coloring_aux :
    ∀ c4 : Fin 5, (_ : c4 ≠ 0) → (_ : c4 ≠ 1) →
    ∀ c5 : Fin 5, (_ : c5 ≠ 0) → (_ : c5 ≠ 2) → (_ : c5 ≠ c4) →
    ∀ c6 : Fin 5, (_ : c6 ≠ 0) → (_ : c6 ≠ 3) → (_ : c6 ≠ c4) → (_ : c6 ≠ c5) →
    ∀ c7 : Fin 5, (_ : c7 ≠ 1) → (_ : c7 ≠ 2) → (_ : c7 ≠ c4) → (_ : c7 ≠ c5) →
    ∀ c8 : Fin 5, (_ : c8 ≠ 1) → (_ : c8 ≠ 3) → (_ : c8 ≠ c4) → (_ : c8 ≠ c6) → (_ : c8 ≠ c7) →
    ∀ c9 : Fin 5, (_ : c9 ≠ 2) → (_ : c9 ≠ 3) → (_ : c9 ≠ c5) → (_ : c9 ≠ c6) →
      (_ : c9 ≠ c7) → (_ : c9 ≠ c8) →
    ∀ c10 : Fin 5, (_ : c10 ≠ 0) → (_ : c10 ≠ 1) → (_ : c10 ≠ c4) →
    ∀ c11 : Fin 5, (_ : c11 ≠ 0) → (_ : c11 ≠ 2) → (_ : c11 ≠ c5) → (_ : c11 ≠ c10) →
    ∀ c12 : Fin 5, (_ : c12 ≠ 0) → (_ : c12 ≠ 3) → (_ : c12 ≠ c6) → (_ : c12 ≠ c10) →
      (_ : c12 ≠ c11) →
    ∀ c13 : Fin 5, (_ : c13 ≠ 1) → (_ : c13 ≠ 2) → (_ : c13 ≠ c7) → (_ : c13 ≠ c10) →
      (_ : c13 ≠ c11) →
    ∀ c14 : Fin 5, (_ : c14 ≠ 1) → (_ : c14 ≠ 3) → (_ : c14 ≠ c8) → (_ : c14 ≠ c10) →
      (_ : c14 ≠ c12) → (_ : c14 ≠ c13) →
    ∀ c15 : Fin 5, (_ : c15 ≠ 2) → (_ : c15 ≠ 3) → (_ : c15 ≠ c9) → (_ : c15 ≠ c11) →
      (_ : c15 ≠ c12) → (_ : c15 ≠ c13) → (_ : c15 ≠ c14) →
    False := by
  decide +kernel

/-- The Johnson graph `J(6, 3)` is not 5-colorable (`χ(J(6, 3)) = 6`). -/
theorem not_colorable_five_johnson_6_3 : ¬ J(6, 3).Colorable 5 := by
  rintro ⟨c₀⟩
  let v0 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 1, 2}, by decide⟩
  let v1 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 1, 3}, by decide⟩
  let v2 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 1, 4}, by decide⟩
  let v3 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 1, 5}, by decide⟩
  let v4 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 2, 3}, by decide⟩
  let v5 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 2, 4}, by decide⟩
  let v6 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 2, 5}, by decide⟩
  let v7 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 3, 4}, by decide⟩
  let v8 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 3, 5}, by decide⟩
  let v9 : {s : Finset (Fin 6) // #s = 3} := ⟨{0, 4, 5}, by decide⟩
  let v10 : {s : Finset (Fin 6) // #s = 3} := ⟨{1, 2, 3}, by decide⟩
  let v11 : {s : Finset (Fin 6) // #s = 3} := ⟨{1, 2, 4}, by decide⟩
  let v12 : {s : Finset (Fin 6) // #s = 3} := ⟨{1, 2, 5}, by decide⟩
  let v13 : {s : Finset (Fin 6) // #s = 3} := ⟨{1, 3, 4}, by decide⟩
  let v14 : {s : Finset (Fin 6) // #s = 3} := ⟨{1, 3, 5}, by decide⟩
  let v15 : {s : Finset (Fin 6) // #s = 3} := ⟨{1, 4, 5}, by decide⟩
  have h10 : c₀ v1 ≠ c₀ v0 := c₀.valid (by decide : J(6, 3).Adj v1 v0)
  have h20 : c₀ v2 ≠ c₀ v0 := c₀.valid (by decide : J(6, 3).Adj v2 v0)
  have h21 : c₀ v2 ≠ c₀ v1 := c₀.valid (by decide : J(6, 3).Adj v2 v1)
  have h30 : c₀ v3 ≠ c₀ v0 := c₀.valid (by decide : J(6, 3).Adj v3 v0)
  have h31 : c₀ v3 ≠ c₀ v1 := c₀.valid (by decide : J(6, 3).Adj v3 v1)
  have h32 : c₀ v3 ≠ c₀ v2 := c₀.valid (by decide : J(6, 3).Adj v3 v2)
  let c : J(6, 3).Coloring (Fin 5) :=
    Coloring.mk (fun v ↦ recolor5 (c₀ v0) (c₀ v1) (c₀ v2) (c₀ v3) (c₀ v))
      (fun {u v} hadj ↦ recolor5_ne (c₀ v0) (c₀ v1) h10 (c₀ v2) h20 h21 (c₀ v3) h30 h31 h32
        (c₀ u) (c₀ v) (c₀.valid hadj))
  have hc0 : c v0 = 0 := by
    change recolor5 (c₀ v0) (c₀ v1) (c₀ v2) (c₀ v3) (c₀ v0) = 0
    simp [recolor5]
  have hc1 : c v1 = 1 := by
    change recolor5 (c₀ v0) (c₀ v1) (c₀ v2) (c₀ v3) (c₀ v1) = 1
    simp [recolor5, h10]
  have hc2 : c v2 = 2 := by
    change recolor5 (c₀ v0) (c₀ v1) (c₀ v2) (c₀ v3) (c₀ v2) = 2
    simp [recolor5, h20, h21]
  have hc3 : c v3 = 3 := by
    change recolor5 (c₀ v0) (c₀ v1) (c₀ v2) (c₀ v3) (c₀ v3) = 3
    simp [recolor5, h30, h31, h32]
  exact j63_no_5_coloring_aux
    (c v4) (hc0 ▸ c.valid (by decide : J(6, 3).Adj v4 v0))
      (hc1 ▸ c.valid (by decide : J(6, 3).Adj v4 v1))
    (c v5) (hc0 ▸ c.valid (by decide : J(6, 3).Adj v5 v0))
      (hc2 ▸ c.valid (by decide : J(6, 3).Adj v5 v2)) (c.valid (by decide : J(6, 3).Adj v5 v4))
    (c v6) (hc0 ▸ c.valid (by decide : J(6, 3).Adj v6 v0))
      (hc3 ▸ c.valid (by decide : J(6, 3).Adj v6 v3))
      (c.valid (by decide : J(6, 3).Adj v6 v4)) (c.valid (by decide : J(6, 3).Adj v6 v5))
    (c v7) (hc1 ▸ c.valid (by decide : J(6, 3).Adj v7 v1))
      (hc2 ▸ c.valid (by decide : J(6, 3).Adj v7 v2))
      (c.valid (by decide : J(6, 3).Adj v7 v4)) (c.valid (by decide : J(6, 3).Adj v7 v5))
    (c v8) (hc1 ▸ c.valid (by decide : J(6, 3).Adj v8 v1))
      (hc3 ▸ c.valid (by decide : J(6, 3).Adj v8 v3))
      (c.valid (by decide : J(6, 3).Adj v8 v4)) (c.valid (by decide : J(6, 3).Adj v8 v6))
      (c.valid (by decide : J(6, 3).Adj v8 v7))
    (c v9) (hc2 ▸ c.valid (by decide : J(6, 3).Adj v9 v2))
      (hc3 ▸ c.valid (by decide : J(6, 3).Adj v9 v3))
      (c.valid (by decide : J(6, 3).Adj v9 v5)) (c.valid (by decide : J(6, 3).Adj v9 v6))
      (c.valid (by decide : J(6, 3).Adj v9 v7)) (c.valid (by decide : J(6, 3).Adj v9 v8))
    (c v10) (hc0 ▸ c.valid (by decide : J(6, 3).Adj v10 v0))
      (hc1 ▸ c.valid (by decide : J(6, 3).Adj v10 v1))
      (c.valid (by decide : J(6, 3).Adj v10 v4))
    (c v11) (hc0 ▸ c.valid (by decide : J(6, 3).Adj v11 v0))
      (hc2 ▸ c.valid (by decide : J(6, 3).Adj v11 v2))
      (c.valid (by decide : J(6, 3).Adj v11 v5)) (c.valid (by decide : J(6, 3).Adj v11 v10))
    (c v12) (hc0 ▸ c.valid (by decide : J(6, 3).Adj v12 v0))
      (hc3 ▸ c.valid (by decide : J(6, 3).Adj v12 v3))
      (c.valid (by decide : J(6, 3).Adj v12 v6)) (c.valid (by decide : J(6, 3).Adj v12 v10))
      (c.valid (by decide : J(6, 3).Adj v12 v11))
    (c v13) (hc1 ▸ c.valid (by decide : J(6, 3).Adj v13 v1))
      (hc2 ▸ c.valid (by decide : J(6, 3).Adj v13 v2))
      (c.valid (by decide : J(6, 3).Adj v13 v7)) (c.valid (by decide : J(6, 3).Adj v13 v10))
      (c.valid (by decide : J(6, 3).Adj v13 v11))
    (c v14) (hc1 ▸ c.valid (by decide : J(6, 3).Adj v14 v1))
      (hc3 ▸ c.valid (by decide : J(6, 3).Adj v14 v3))
      (c.valid (by decide : J(6, 3).Adj v14 v8)) (c.valid (by decide : J(6, 3).Adj v14 v10))
      (c.valid (by decide : J(6, 3).Adj v14 v12)) (c.valid (by decide : J(6, 3).Adj v14 v13))
    (c v15) (hc2 ▸ c.valid (by decide : J(6, 3).Adj v15 v2))
      (hc3 ▸ c.valid (by decide : J(6, 3).Adj v15 v3))
      (c.valid (by decide : J(6, 3).Adj v15 v9)) (c.valid (by decide : J(6, 3).Adj v15 v11))
      (c.valid (by decide : J(6, 3).Adj v15 v12)) (c.valid (by decide : J(6, 3).Adj v15 v13))
      (c.valid (by decide : J(6, 3).Adj v15 v14))

/-- Resolution of the first prime `k + 1 = p` case (`k = 4, p = 5`):
`4 + 1 < J(2 * 4, 4).chromaticNumber`, proved via the embedding `J(6, 3) →g J(8, 4)`
and `¬ J(6, 3).Colorable 5`. -/
theorem johnson_chromaticNumber_four : 4 + 1 < J(2 * 4, 4).chromaticNumber := by
  have h_mono : J(6, 3).chromaticNumber ≤ J(2 * 4, 4).chromaticNumber :=
    chromaticNumber_johnson_mono (by omega) (by omega)
  have h_gt : (5 : ℕ∞) < J(6, 3).chromaticNumber := by
    rw [show (5 : ℕ∞) = ((5 : ℕ) : ℕ∞) by rfl, lt_chromaticNumber_iff_not_colorable]
    exact not_colorable_five_johnson_6_3
  exact lt_of_lt_of_le h_gt h_mono

/-- Corollary for `k = 4`: `¬ Property 4`. -/
theorem not_property_four : ¬ Property 4 := by
  rw [← property_iff_chromaticNumber 4 (by omega)]
  exact johnson_chromaticNumber_four.ne'

end Erdos835

#print axioms Erdos835.property_iff_chromaticNumber
#print axioms Erdos835.indepNum_johnson_le_johnsonBound
#print axioms Erdos835.div_johnsonBound_le_chromaticNum_johnson
#print axioms Erdos835.ma_tang_prop_2_1
#print axioms Erdos835.johnson_chromaticNumber_composite
#print axioms Erdos835.not_property_of_composite
#print axioms Erdos835.johnson_chromaticNumber_odd
#print axioms Erdos835.johnsonGraph_18_9_chromaticNumber
#print axioms Erdos835.ma_tang_lemma_2_3
#print axioms Erdos835.johnson_chromaticNumber_four
#print axioms Erdos835.not_property_four
