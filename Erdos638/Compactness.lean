import Erdos638.Defs
import Erdos638.AlterationBound
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Clean-Room Ultrafilter Triangle-Coloring Compactness & Block-Disjointness Obstruction

In pure ZFC, we construct a sequence of finite graphs `blockGraph : ℕ → FiniteGraph` and prove:

1. **Ultrafilter Triangle-Coloring Compactness (`exists_finite_induced_two_ramsey`)**:
   If `G : SimpleGraph V` (on an arbitrary type `V`) satisfies `ForcesMonoTriangle G (Fin 2)`,
   then some finite subset `S : Finset V` already induces a finite graph `H` satisfying
   `ForcesMonoTriangle H.graph (Fin 2)`.
   *Proof*: Otherwise, for every `S : Finset V` we may choose a triangle-free 2-coloring `c_S` of `G[S]`.
   Extend `Filter.atTop : Filter (Finset V)` to an ultrafilter `𝒰 : Ultrafilter (Finset V)` and set
   `col e = 1` iff `{S | c_S e = 1} ∈ 𝒰`. On any triangle `{x, y, z}` of `G`, intersecting `{S | {x,y,z} ⊆ S} ∈ 𝒰`
   with the three ultrafilter color sets produces a single finite set `S ⊇ {x, y, z}` on which `c_S`
   makes `{x, y, z}` monochromatic — contradiction!

2. **Recursive Disjoint-Core Block Sequence (`blockGraph : ℕ → FiniteGraph`)**:
   Using `exists_ramsey_avoiding_family`, we recursively select `blockGraph k` (`k : ℕ`) so that:
   - `ForcesMonoTriangle (blockGraph k).graph (Fin (k + 2))` (`W_k → (K₃)²_{k+2}`), and
   - `blockGraph (k + 1)` avoids ALL minimal 2-Ramsey cores that embed into `blockGraph 0, ..., blockGraph k`!

3. **Age Obstruction Theorem (`finite_color_obstruction_ordinary` & `finite_color_obstruction_induced`)**:
   Let `𝒮_ord` (resp. `𝒮_ind`) be the set of all finite graphs embedding as ordinary (resp. induced)
   subgraphs into some `blockGraph k`. For ANY host graph `G : SimpleGraph V` (finite or infinite,
   in ANY universe) with `AllFiniteSubgraphsIn G 𝒮_ord` (or `AllFiniteInducedSubgraphsIn G 𝒮_ind`),
   there exists a FINITE number `m : ℕ` (`1 ≤ m`) such that `¬ForcesMonoTriangle G (Fin m)`!
   Consequently, for **every infinite cardinal `κ`** (and every infinite palette `C`),
   `¬ForcesMonoTriangle G C`!
-/

namespace Erdos638

open scoped Classical BigOperators
open Filter

/-! ## 1. Induced `FiniteGraph` on a `Finset V` & Ultrafilter Compactness -/

/-- Canonical `FiniteGraph` induced by `G : SimpleGraph V` on a finite vertex subset `S : Finset V`. -/
noncomputable def inducedFiniteGraph {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    Σ' (H : FiniteGraph), ∃ φ : Fin H.verts → V,
      Function.Injective φ ∧
      (∀ i, φ i ∈ S) ∧
      (∀ w ∈ S, ∃ i, φ i = w) ∧
      (∀ i j, H.graph.Adj i j ↔ G.Adj (φ i) (φ j)) := by
  let eqv : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let φ : Fin S.card → V := fun i => (eqv i).1
  have hφ_inj : Function.Injective φ := Subtype.val_injective.comp eqv.injective
  let H : FiniteGraph := ⟨S.card, SimpleGraph.comap φ G⟩
  refine ⟨H, φ, hφ_inj, fun i => (eqv i).2, ?_, fun i j => ?_⟩
  · intro w hw
    exact ⟨eqv.symm ⟨w, hw⟩, by simp [φ]⟩
  · simp [H]

/-- **Ultrafilter Compactness for 2-Color Triangle Forcing**:
If `ForcesMonoTriangle G (Fin 2)` holds on `G : SimpleGraph V`, then some finite induced subgraph
`H : FiniteGraph` of `G` already satisfies `ForcesMonoTriangle H.graph (Fin 2)`! -/
theorem exists_finite_induced_two_ramsey {V : Type*} {G : SimpleGraph V}
    (hG : ForcesMonoTriangle G (Fin 2)) :
    ∃ (H : FiniteGraph) (φ : Fin H.verts → V),
      Function.Injective φ ∧
      (∀ i j, H.graph.Adj i j ↔ G.Adj (φ i) (φ j)) ∧
      ForcesMonoTriangle H.graph (Fin 2) := by
  by_contra! hnone
  -- For every `S : Finset V`, its induced finite graph `H_S` does NOT force a monochromatic triangle under 2 colors!
  have hex_local : ∀ S : Finset V,
      ∃ c : Sym2 V → Fin 2, ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
        G.Adj x y → G.Adj y z → G.Adj x z →
          ¬(c s(x, y) = c s(y, z) ∧ c s(y, z) = c s(x, z)) := by
    intro S
    let pack := inducedFiniteGraph G S
    let H := pack.1
    obtain ⟨φ, hφ_inj, hφ_inS, hφ_surjS, hφ_adj⟩ := pack.2
    have hnotH : ¬ForcesMonoTriangle H.graph (Fin 2) :=
      fun hF => hnone H φ hφ_inj hφ_adj hF
    rw [forcesMonoTriangle_iff_sym2] at hnotH
    have hex_cH : ∃ cH : Sym2 (Fin H.verts) → Fin 2, ¬HasMonoTriangle H.graph cH := by
      by_contra! hall
      exact hnotH hall
    obtain ⟨cH, hcH⟩ := hex_cH
    -- Extend `cH` to `Sym2 V → Fin 2` using `hφ_surjS` on `S`!
    let invS : (w : V) → w ∈ S → Fin H.verts := fun w hw => Classical.choose (hφ_surjS w hw)
    have hinvS_eq : ∀ w (hw : w ∈ S), φ (invS w hw) = w :=
      fun w hw => Classical.choose_spec (hφ_surjS w hw)
    let c : Sym2 V → Fin 2 :=
      Sym2.lift ⟨fun x y =>
        if hx : x ∈ S then
          if hy : y ∈ S then cH s(invS x hx, invS y hy) else 0
        else 0, by
          intro x y
          by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy, Sym2.eq_swap]⟩
    refine ⟨c, ?_⟩
    intro x hx y hy z hz hab hbc hac ⟨h1, h2⟩
    let ix := invS x hx
    let iy := invS y hy
    let iz := invS z hz
    have hix : φ ix = x := hinvS_eq x hx
    have hiy : φ iy = y := hinvS_eq y hy
    have hiz : φ iz = z := hinvS_eq z hz
    have hc_xy : c s(x, y) = cH s(ix, iy) := by simp [c, hx, hy, ix, iy]
    have hc_yz : c s(y, z) = cH s(iy, iz) := by simp [c, hy, hz, iy, iz]
    have hc_xz : c s(x, z) = cH s(ix, iz) := by simp [c, hx, hz, ix, iz]
    apply hcH
    refine ⟨ix, iy, iz,
      (hφ_adj ix iy).mpr (by rwa [hix, hiy]),
      (hφ_adj iy iz).mpr (by rwa [hiy, hiz]),
      (hφ_adj ix iz).mpr (by rwa [hix, hiz]),
      by rw [← hc_xy, ← hc_yz]; exact h1,
      by rw [← hc_yz, ← hc_xz]; exact h2⟩
  let locCol : Finset V → Sym2 V → Fin 2 := fun S => Classical.choose (hex_local S)
  have hloc_spec := fun S => Classical.choose_spec (hex_local S)
  -- Extend `Filter.atTop : Filter (Finset V)` (which is `NeBot` since `Finset V` is directed/semilatticeSup!)
  -- to an ultrafilter `𝒰 : Ultrafilter (Finset V)`!
  let 𝒰 : Ultrafilter (Finset V) := Ultrafilter.of (Filter.atTop : Filter (Finset V))
  have h𝒰_le : (𝒰 : Filter (Finset V)) ≤ Filter.atTop := Ultrafilter.of_le Filter.atTop
  -- Define global coloring `col : Sym2 V → Fin 2` along `𝒰`!
  let col : Sym2 V → Fin 2 := fun e =>
    if {S : Finset V | locCol S e = 1} ∈ 𝒰 then 1 else 0
  have hcol_ev : ∀ e : Sym2 V, {S : Finset V | locCol S e = col e} ∈ (𝒰 : Filter (Finset V)) := by
    intro e
    dsimp only [col]
    by_cases h1 : {S : Finset V | locCol S e = 1} ∈ 𝒰
    · rw [if_pos h1]; exact h1
    · rw [if_neg h1]
      -- Since `𝒰` is an ultrafilter and `Fin 2` has only `0` and `1`, `{S | locCol S e ≠ 1} ∈ 𝒰`!
      have hcompl : {S : Finset V | locCol S e = 1}ᶜ ∈ 𝒰 :=
        Ultrafilter.compl_mem_iff_notMem.mpr h1
      apply Filter.mem_of_superset hcompl
      intro S hS
      have hne1 : locCol S e ≠ 1 := hS
      have hv := (locCol S e).isLt
      have hval_ne : (locCol S e).val ≠ 1 := fun h => hne1 (Fin.ext h)
      ext; simp; omega
  rw [forcesMonoTriangle_iff_sym2] at hG
  obtain ⟨x, y, z, hab, hbc, hac, hm1, hm2⟩ := hG col
  have hxyz_atTop : {S : Finset V | ({x, y, z} : Finset V) ⊆ S} ∈ (Filter.atTop : Filter (Finset V)) :=
    Filter.mem_atTop ({x, y, z} : Finset V)
  have hxyz_𝒰 : {S : Finset V | ({x, y, z} : Finset V) ⊆ S} ∈ (𝒰 : Filter (Finset V)) :=
    h𝒰_le hxyz_atTop
  have hinter : ({S : Finset V | ({x, y, z} : Finset V) ⊆ S} ∩
      ({S : Finset V | locCol S s(x, y) = col s(x, y)} ∩
        ({S : Finset V | locCol S s(y, z) = col s(y, z)} ∩
          {S : Finset V | locCol S s(x, z) = col s(x, z)}))) ∈ (𝒰 : Filter (Finset V)) :=
    Filter.inter_mem hxyz_𝒰 (Filter.inter_mem (hcol_ev s(x, y))
      (Filter.inter_mem (hcol_ev s(y, z)) (hcol_ev s(x, z))))
  obtain ⟨S₀, hS₀_sub, hc_ab, hc_bc, hc_ac⟩ := Filter.nonempty_of_mem hinter
  have hxS₀ : x ∈ S₀ := hS₀_sub (by simp)
  have hyS₀ : y ∈ S₀ := hS₀_sub (by simp)
  have hzS₀ : z ∈ S₀ := hS₀_sub (by simp)
  have heq_ab : locCol S₀ s(x, y) = col s(x, y) := hc_ab
  have heq_bc : locCol S₀ s(y, z) = col s(y, z) := hc_bc
  have heq_ac : locCol S₀ s(x, z) = col s(x, z) := hc_ac
  have hspec₀ : ¬(locCol S₀ s(x, y) = locCol S₀ s(y, z) ∧ locCol S₀ s(y, z) = locCol S₀ s(x, z)) :=
    hloc_spec S₀ x hxS₀ y hyS₀ z hzS₀ hab hbc hac
  exact hspec₀ ⟨by rw [heq_ab, heq_bc, hm1], by rw [heq_bc, heq_ac, hm2]⟩

/-! ## 2. Enumeration of All `FiniteGraph`s up to Vertex Bound `N` & Block Sequence -/

/-- Finite `Finset` of ALL canonical `FiniteGraph`s `⟨v, G⟩` with `v ≤ N` and `G → (K₃)²_2`!
Notice that for fixed `v : ℕ`, `SimpleGraph (Fin v)` is a `Fintype`! -/
noncomputable def twoRamseyGraphsUpTo (N : ℕ) : Finset FiniteGraph :=
  (Finset.range (N + 1)).biUnion (fun v =>
    ((Finset.univ : Finset (SimpleGraph (Fin v))).filter
      (fun G => ForcesMonoTriangle G (Fin 2))).image (fun G => ⟨v, G⟩))

lemma mem_twoRamseyGraphsUpTo {N : ℕ} {M : FiniteGraph} :
    M ∈ twoRamseyGraphsUpTo N ↔ M.verts ≤ N ∧ ForcesMonoTriangle M.graph (Fin 2) := by
  rcases M with ⟨v, G⟩
  unfold twoRamseyGraphsUpTo
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, G', hG', heq⟩
    cases heq
    exact ⟨by omega, hG'⟩
  · rintro ⟨hv, hG⟩
    exact ⟨v, by omega, G, hG, rfl⟩

/-- Recursive construction of the block prefix `blockPrefix k : Fin (k + 1) → FiniteGraph`?
Even simpler: define `blockList : ℕ → List FiniteGraph` by recursion on `k`:
at step `k`, collect `ℱ_k := twoRamseyGraphsUpTo (max_{W ∈ blockList k} W.verts)` — wait:
ANY 2-Ramsey graph `M` that embeds into some earlier block `W ∈ blockList k` MUST satisfy
`M.verts ≤ W.verts ≤ maxVerts`!!
WAIT A SECOND!! STOP AND ADMIRE THAT SIMPLICITY!!
We don't even need to filter by "minimal 2-Ramsey cores of earlier blocks" during recursion —
if `blockGraph (k + 1)` avoids **EVERY** 2-Ramsey graph `M` of order `M.verts ≤ max_{i ≤ k} (blockGraph i).verts`,
then in particular NO minimal 2-Ramsey core `M` embedding into ANY `blockGraph i` (`i ≤ k`) can
EVER embed into `blockGraph (k + 1)`!! -/
noncomputable def blockList : ℕ → List FiniteGraph
  | 0 => []
  | k + 1 =>
    let prev := blockList k
    let maxV : ℕ := (prev.map FiniteGraph.verts).foldr max 0
    let ℱ : Finset FiniteGraph := twoRamseyGraphsUpTo maxV
    have hℱ : ∀ M ∈ ℱ, ForcesMonoTriangle M.graph (Fin 2) :=
      fun _ hM => (mem_twoRamseyGraphsUpTo.mp hM).2
    let W := Classical.choose (exists_ramsey_avoiding_family (k + 2) (by omega) ℱ hℱ)
    W :: prev

lemma blockList_length (k : ℕ) : (blockList k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [blockList, ih]

/-- `blockGraph k` (`k : ℕ`) is the `k`-th sparse triangle-Ramsey block (`W_k → (K₃)²_{k + 2}`). -/
noncomputable def blockGraph (k : ℕ) : FiniteGraph :=
  match blockList (k + 1) with
  | W :: _ => W
  | [] => ⟨0, ⊥⟩

lemma blockList_mem_iff : ∀ (n : ℕ) (G : FiniteGraph),
    G ∈ blockList n ↔ ∃ k < n, blockGraph k = G
  | 0, G => by simp [blockList]
  | n + 1, G => by
    have hcons : blockList (n + 1) = blockGraph n :: blockList n := rfl
    rw [hcons, List.mem_cons, blockList_mem_iff n G]
    constructor
    · rintro (rfl | ⟨k, hkn, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · exact ⟨k, Nat.lt_succ_of_lt hkn, rfl⟩
    · rintro ⟨k, hkn1, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hkn1 with hlt | rfl
      · exact Or.inr ⟨k, hlt, rfl⟩
      · exact Or.inl rfl

lemma blockGraph_ramsey (k : ℕ) : ForcesMonoTriangle (blockGraph k).graph (Fin (k + 2)) := by
  let prev := blockList k
  let maxV : ℕ := (prev.map FiniteGraph.verts).foldr max 0
  let ℱ : Finset FiniteGraph := twoRamseyGraphsUpTo maxV
  have hℱ : ∀ M ∈ ℱ, ForcesMonoTriangle M.graph (Fin 2) :=
    fun _ hM => (mem_twoRamseyGraphsUpTo.mp hM).2
  have hspec := Classical.choose_spec (exists_ramsey_avoiding_family (k + 2) (by omega) ℱ hℱ)
  have heq : blockGraph k = Classical.choose (exists_ramsey_avoiding_family (k + 2) (by omega) ℱ hℱ) := by
    unfold blockGraph blockList
    rfl
  rw [heq]
  exact hspec.1

/-- **Unique Block Property**:
If `M` is ANY finite 2-Ramsey graph (`ForcesMonoTriangle M.graph (Fin 2)`), `M` embeds into
AT MOST ONE block `blockGraph k` (`i ≠ j → EmbedsInto M (blockGraph i) → ¬EmbedsInto M (blockGraph j)`)! -/
lemma blockGraph_disjoint_two_ramsey {M : FiniteGraph}
    (hM : ForcesMonoTriangle M.graph (Fin 2)) {i j : ℕ} (hij : i ≠ j)
    (hi : EmbedsInto M (blockGraph i)) : ¬EmbedsInto M (blockGraph j) := by
  -- WLOG assume `i < j` (otherwise swap `i` and `j`)!
  suffices hlt_case : ∀ {a b : ℕ}, a < b → EmbedsInto M (blockGraph a) → ¬EmbedsInto M (blockGraph b) by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hlt_case hlt hi
    · intro hj
      exact hlt_case hgt hj hi
  intro a b hab ha
  cases b with
  | zero => omega
  | succ k =>
    let prev := blockList k
    let maxV : ℕ := (prev.map FiniteGraph.verts).foldr max 0
    let ℱ : Finset FiniteGraph := twoRamseyGraphsUpTo maxV
    have hℱ : ∀ M' ∈ ℱ, ForcesMonoTriangle M'.graph (Fin 2) :=
      fun _ hM' => (mem_twoRamseyGraphsUpTo.mp hM').2
    have hspec := Classical.choose_spec (exists_ramsey_avoiding_family (k + 2) (by omega) ℱ hℱ)
    have heq : blockGraph k = Classical.choose (exists_ramsey_avoiding_family (k + 2) (by omega) ℱ hℱ) := by
      unfold blockGraph blockList; rfl
    --Wait: `b = k + 1`, so `blockGraph b = blockGraph (k + 1)` uses `prev' = blockList (k + 1)`!
    let prev' := blockList (k + 1)
    let maxV' : ℕ := (prev'.map FiniteGraph.verts).foldr max 0
    let ℱ' : Finset FiniteGraph := twoRamseyGraphsUpTo maxV'
    have hℱ' : ∀ M' ∈ ℱ', ForcesMonoTriangle M'.graph (Fin 2) :=
      fun _ hM' => (mem_twoRamseyGraphsUpTo.mp hM').2
    have hspec' := Classical.choose_spec (exists_ramsey_avoiding_family (k + 3) (by omega) ℱ' hℱ')
    have heq' : blockGraph (k + 1) =
        Classical.choose (exists_ramsey_avoiding_family (k + 3) (by omega) ℱ' hℱ') := by
      unfold blockGraph blockList; rfl
    rw [heq']
    apply hspec'.2 M
    rw [mem_twoRamseyGraphsUpTo]
    refine ⟨?_, hM⟩
    -- Since `a < k + 1`, `blockGraph a ∈ prev' = blockList (k + 1)`, so `M.verts ≤ (blockGraph a).verts ≤ maxV'`!
    have hmem_prev' : blockGraph a ∈ prev' :=
      (blockList_mem_iff (k + 1) (blockGraph a)).mpr ⟨a, hab, rfl⟩
    have hle_maxV' : ∀ L : List FiniteGraph, ∀ X ∈ L,
        X.verts ≤ (L.map FiniteGraph.verts).foldr max 0 := by
      intro L
      induction L with
      | nil => simp
      | cons head tail ih =>
        intro X hX
        simp only [List.map_cons, List.foldr_cons]
        rcases List.mem_cons.mp hX with rfl | htail
        · exact le_max_left _ _
        · exact (ih X htail).trans (le_max_right _ _)
    exact ha.verts_le.trans (hle_maxV' prev' (blockGraph a) hmem_prev')

/-! ## 3. Hereditary Classes `hereditaryClassOrd` and `hereditaryClassInd` & Age Obstruction -/

/-- The ordinary-subgraph hereditary counterexample class `𝒮_ord`:
all `FiniteGraph`s that embed as ordinary subgraphs into some `blockGraph k` (`k : ℕ`). -/
def hereditaryClassOrd : Set FiniteGraph :=
  { H | ∃ k : ℕ, EmbedsInto H (blockGraph k) }

/-- The induced-subgraph hereditary counterexample class `𝒮_ind`:
all `FiniteGraph`s that embed as induced subgraphs into some `blockGraph k` (`k : ℕ`). -/
def hereditaryClassInd : Set FiniteGraph :=
  { H | ∃ k : ℕ, InducesInto H (blockGraph k) }

lemma hereditaryClassOrd_closed : ClosedUnderSubgraphs hereditaryClassOrd := by
  intro G ⟨k, hk⟩ H hHG
  exact ⟨k, hHG.trans hk⟩

lemma hereditaryClassInd_closed : ClosedUnderInducedSubgraphs hereditaryClassInd := by
  intro G ⟨k, hk⟩ H hHG
  exact ⟨k, hHG.trans hk⟩

lemma hereditaryClassInd_subset_ord : hereditaryClassInd ⊆ hereditaryClassOrd := by
  intro H ⟨k, hk⟩
  exact ⟨k, hk.toEmbeds⟩

/-- Both `hereditaryClassOrd` and `hereditaryClassInd` contain `blockGraph (n - 1)` (or `blockGraph 0`
for `n = 0, 1`), hence for EVERY `n : ℕ` (`n ≥ 1`, and even `n = 0`?! Wait: for `n = 0`, `Fin 0` is
empty, so `G.edgeSet → Fin 0` only exists when `G.edgeSet` is empty! For `n ≥ 1`, `blockGraph n`
satisfies `ForcesMonoTriangle (blockGraph n).graph (Fin (n + 2))`, hence `ForcesMonoTriangle _ (Fin n)`!). -/
lemma hereditaryClassInd_contains_n_ramsey (n : ℕ) :
    ∃ G ∈ hereditaryClassInd, ForcesMonoTriangle G.graph (Fin n) := by
  refine ⟨blockGraph n, ⟨n, InducesInto.refl (blockGraph n)⟩, ?_⟩
  have hram := blockGraph_ramsey n
  let ι : Fin n → Fin (n + 2) := fun c => ⟨c.val, by omega⟩
  have hι : Function.Injective ι := fun a b hab => by
    have hv : (ι a).val = (ι b).val := congrArg Fin.val hab
    exact Fin.ext hv
  exact forcesMonoTriangle_of_palette_inj ι hι hram

lemma hereditaryClassOrd_contains_n_ramsey (n : ℕ) :
    ∃ G ∈ hereditaryClassOrd, ForcesMonoTriangle G.graph (Fin n) := by
  obtain ⟨G, hG_ind, hG_ram⟩ := hereditaryClassInd_contains_n_ramsey n
  exact ⟨G, hereditaryClassInd_subset_ord hG_ind, hG_ram⟩

/-- **Core Age-Obstruction Theorem (Unified for Both Ordinary and Induced Ages)**:
Suppose `G : SimpleGraph V` (on ANY vertex type `V : Type*`, in ANY universe!) has the property
that every finite **induced** subgraph of `G` belongs to `hereditaryClassOrd`
(`AllFiniteInducedSubgraphsIn G hereditaryClassOrd` — note that both `AllFiniteSubgraphsIn G hereditaryClassOrd`
AND `AllFiniteInducedSubgraphsIn G hereditaryClassInd` immediately imply this!).
Then there exists a **finite positive integer `m ≥ 2`** such that `¬ForcesMonoTriangle G (Fin m)`! -/
theorem exists_finite_palette_obstruction {V : Type*} (G : SimpleGraph V)
    (hAge : AllFiniteInducedSubgraphsIn G hereditaryClassOrd) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ForcesMonoTriangle G (Fin m) := by
  by_cases h2 : ForcesMonoTriangle G (Fin 2)
  · -- `G` forces a monochromatic triangle under 2 colors!
    -- By Ultrafilter Compactness (`exists_finite_induced_two_ramsey`), some finite induced subgraph
    -- `H₀` of `G` (embedding via `φ₀ : Fin H₀.verts → V`) ALREADY satisfies `ForcesMonoTriangle H₀.graph (Fin 2)`!
    obtain ⟨H₀, φ₀, hφ₀_inj, hφ₀_adj, hH₀_2⟩ := exists_finite_induced_two_ramsey h2
    -- Since `H₀` is a finite induced subgraph of `G`, `H₀ ∈ hereditaryClassOrd`, so `EmbedsInto H₀ (blockGraph k₀)` for some `k₀`!
    obtain ⟨k₀, hk₀⟩ := hAge H₀ ⟨φ₀, hφ₀_inj, hφ₀_adj⟩
    -- NOW SHOW `V` HAS AT MOST `(blockGraph k₀).verts` ELEMENTS!!
    let B₀ : ℕ := (blockGraph k₀).verts
    have hfin_bound : ∀ S : Finset V, (Finset.univ.image φ₀ ⊆ S) → S.card ≤ B₀ := by
      intro S hS_sup
      let pack := inducedFiniteGraph G S
      let H_S := pack.1
      obtain ⟨ψ, hψ_inj, hψ_inS, hψ_surjS, hψ_adj⟩ := pack.2
      -- 1. `H₀` embeds into `H_S` because `range φ₀ ⊆ S`!
      have hH₀_in_HS : EmbedsInto H₀ H_S := by
        have hex_idx : ∀ i : Fin H₀.verts, ∃ j : Fin H_S.verts, ψ j = φ₀ i := by
          intro i
          exact hψ_surjS (φ₀ i) (hS_sup (Finset.mem_image_of_mem φ₀ (Finset.mem_univ i)))
        let g : Fin H₀.verts → Fin H_S.verts := fun i => Classical.choose (hex_idx i)
        have hg_eq : ∀ i, ψ (g i) = φ₀ i := fun i => Classical.choose_spec (hex_idx i)
        have hg_inj : Function.Injective g := by
          intro i₁ i₂ heq
          apply hφ₀_inj
          rw [← hg_eq i₁, ← hg_eq i₂, heq]
        refine ⟨g, hg_inj, ?_⟩
        intro i₁ i₂ hadj
        rw [hψ_adj, hg_eq, hg_eq, ← hφ₀_adj]
        exact hadj
      -- 2. Since `H_S` is a finite induced subgraph of `G`, `H_S ∈ hereditaryClassOrd`,
      --    so `EmbedsInto H_S (blockGraph k₁)` for some `k₁`!
      obtain ⟨k₁, hk₁⟩ := hAge H_S ⟨ψ, hψ_inj, hψ_adj⟩
      -- 3. By transitivity, `EmbedsInto H₀ (blockGraph k₁)`!
      have hH₀_k₁ : EmbedsInto H₀ (blockGraph k₁) := hH₀_in_HS.trans hk₁
      -- 4. Since `H₀` is 2-Ramsey (`hH₀_2`), `blockGraph_disjoint_two_ramsey` forces `k₁ = k₀`!
      have hk_eq : k₁ = k₀ := by
        by_contra hne
        exact blockGraph_disjoint_two_ramsey hH₀_2 hne hH₀_k₁ hk₀
      subst hk_eq
      -- 5. Hence `S.card = H_S.verts ≤ (blockGraph k₁).verts = B₀`!
      exact hk₁.verts_le
    -- Deduce `Finite V`! If `Infinite V`, we could choose `B₀ + 1` elements of `V`, union with `univ.image φ₀`,
    -- and get a `Finset V` of size `≥ B₀ + 1 > B₀` containing `univ.image φ₀`!
    have hFiniteV : Finite V := by
      by_contra hInf
      rw [not_finite_iff_infinite] at hInf
      let embN : ℕ ↪ V := Infinite.natEmbedding V
      let T : Finset V := (Finset.range (B₀ + 1)).map embN
      have hT_card : T.card = B₀ + 1 := by simp [T]
      let S_big : Finset V := Finset.univ.image φ₀ ∪ T
      have hle_B₀ := hfin_bound S_big Finset.subset_union_left
      have hge_T : B₀ + 1 ≤ S_big.card := by
        rw [← hT_card]
        exact Finset.card_le_card Finset.subset_union_right
      omega
    let _ : Fintype V := Fintype.ofFinite V
    -- Any finite graph `G` on `Fintype V` has finitely many edges `e = G.edgeFinset.card`,
    -- so with `m = max 2 (e + 1)`, `¬ForcesMonoTriangle G (Fin m)`!
    let e_cnt := G.edgeFinset.card
    let m := max 2 (e_cnt + 1)
    refine ⟨m, le_max_left _ _, ?_⟩
    intro hFm
    have hFe : ForcesMonoTriangle G (Fin (e_cnt + 1)) := by
      have hm_ge : e_cnt + 1 ≤ m := le_max_right _ _
      let ι : Fin (e_cnt + 1) → Fin m := fun c => ⟨c.val, by omega⟩
      have hι : Function.Injective ι := fun a b hab => by
        have hv : (ι a).val = (ι b).val := congrArg Fin.val hab
        exact Fin.ext hv
      exact forcesMonoTriangle_of_palette_inj ι hι hFm
    exact not_forcesMonoTriangle_of_card_edges_lt G (le_refl e_cnt) hFe
  · exact ⟨2, le_rfl, h2⟩

/-- Corollary: Under EITHER `AllFiniteSubgraphsIn G hereditaryClassOrd` OR
`AllFiniteInducedSubgraphsIn G hereditaryClassInd`, `G` cannot force a monochromatic triangle
under ANY infinite color palette `C` (`[Infinite C]`)! -/
theorem not_forcesMonoTriangle_infinite_of_ord {V : Type*} (G : SimpleGraph V)
    (hAge : AllFiniteSubgraphsIn G hereditaryClassOrd)
    (C : Type*) [Infinite C] :
    ¬ForcesMonoTriangle G C := by
  have hIndAge : AllFiniteInducedSubgraphsIn G hereditaryClassOrd := by
    intro H ⟨φ, hφ_inj, hφ_iff⟩
    exact hAge H ⟨φ, hφ_inj, fun u v h => (hφ_iff u v).mp h⟩
  obtain ⟨m, _, hnot_m⟩ := exists_finite_palette_obstruction G hIndAge
  intro hFC
  let embN : ℕ ↪ C := Infinite.natEmbedding C
  let ι : Fin m → C := fun i => embN i.val
  have hι : Function.Injective ι := fun a b hab => Fin.ext (embN.injective hab)
  exact hnot_m (forcesMonoTriangle_of_palette_inj ι hι hFC)

theorem not_forcesMonoTriangle_infinite_of_ind {V : Type*} (G : SimpleGraph V)
    (hAge : AllFiniteInducedSubgraphsIn G hereditaryClassInd)
    (C : Type*) [Infinite C] :
    ¬ForcesMonoTriangle G C := by
  have hIndOrd : AllFiniteInducedSubgraphsIn G hereditaryClassOrd := by
    intro H hH
    exact hereditaryClassInd_subset_ord (hAge H hH)
  obtain ⟨m, _, hnot_m⟩ := exists_finite_palette_obstruction G hIndOrd
  intro hFC
  let embN : ℕ ↪ C := Infinite.natEmbedding C
  let ι : Fin m → C := fun i => embN i.val
  have hι : Function.Injective ι := fun a b hab => Fin.ext (embN.injective hab)
  exact hnot_m (forcesMonoTriangle_of_palette_inj ι hι hFC)

end Erdos638
