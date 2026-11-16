import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Clean-Room Graph & Sparsity Foundations for Erdős Problem #638 (`JSP-000519`)

This module develops from first principles:
1. Monochromatic triangle forcing (`ForcesMonoTriangle`) for arbitrary finite or infinite
   color palettes `C`, together with monotonicity in the graph and palette;
2. Finite graph models (`FiniteGraph`), subgraph homomorphisms (`EmbedsInto`), induced
   embeddings (`InducesInto`), downward-closed hereditary families, and finite subgraph
   realizations inside arbitrary host graphs `G : SimpleGraph V`;
3. **The `(2|S| - 3)`-Sparsity 2-Coloring Theorem (`two_colorable_of_sparse_subsets`)**:
   Every finite simple graph `G` in which every subset `S` of `≥ 4` vertices spans at most
   `2|S| - 3` edges admits a 2-edge-coloring with no monochromatic triangle!
   Consequently (`exists_dense_four_plus_subset`), every finite graph forcing a monochromatic
   triangle under 2 colors contains a vertex set `S` (`4 ≤ |S|`) spanning `≥ 2|S| - 2` edges.
-/

namespace Erdos638

open scoped Classical BigOperators
universe u v

/-! ## 1. Monochromatic Triangle Forcing -/

/-- `HasMonoTriangle G col` asserts that edge-coloring `col : Sym2 V → C` admits three
mutually adjacent vertices `x, y, z : V` in `G` whose three edges receive the same color. -/
def HasMonoTriangle {V : Type*} (G : SimpleGraph V) {C : Type*} (col : Sym2 V → C) : Prop :=
  ∃ x y z : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
    col s(x, y) = col s(y, z) ∧ col s(y, z) = col s(x, z)

/-- `ForcesMonoTriangle G C` (`G → (K₃)²_C`) asserts that every coloring of the edges of `G`
by palette `C` yields a monochromatic triangle in `G`. -/
def ForcesMonoTriangle {V : Type*} (G : SimpleGraph V) (C : Type*) : Prop :=
  ∀ col : G.edgeSet → C, ∃ (x y z : V) (hab : G.Adj x y) (hbc : G.Adj y z) (hac : G.Adj x z),
    col ⟨s(x, y), hab⟩ = col ⟨s(y, z), hbc⟩ ∧
    col ⟨s(y, z), hbc⟩ = col ⟨s(x, z), hac⟩

lemma forcesMonoTriangle_iff_sym2 {V : Type*} (G : SimpleGraph V) (C : Type*) [Nonempty C] :
    ForcesMonoTriangle G C ↔ ∀ col : Sym2 V → C, HasMonoTriangle G col := by
  constructor
  · intro h col
    obtain ⟨x, y, z, hab, hbc, hac, h1, h2⟩ := h (fun e => col e.1)
    exact ⟨x, y, z, hab, hbc, hac, h1, h2⟩
  · intro h col
    let c₀ : C := Classical.arbitrary C
    let col' : Sym2 V → C := fun e => if he : e ∈ G.edgeSet then col ⟨e, he⟩ else c₀
    obtain ⟨x, y, z, hab, hbc, hac, h1, h2⟩ := h col'
    have mem_ab : s(x, y) ∈ G.edgeSet := hab
    have mem_bc : s(y, z) ∈ G.edgeSet := hbc
    have mem_ac : s(x, z) ∈ G.edgeSet := hac
    refine ⟨x, y, z, hab, hbc, hac, ?_, ?_⟩
    · simpa [col', mem_ab, mem_bc] using h1
    · simpa [col', mem_bc, mem_ac] using h2

lemma forcesMonoTriangle_of_palette_inj {V : Type*} {G : SimpleGraph V} {C₁ C₂ : Type*}
    (ι : C₁ → C₂) (hι : Function.Injective ι) (hG : ForcesMonoTriangle G C₂) :
    ForcesMonoTriangle G C₁ := by
  intro col
  obtain ⟨x, y, z, hab, hbc, hac, h1, h2⟩ := hG (fun e => ι (col e))
  exact ⟨x, y, z, hab, hbc, hac, hι h1, hι h2⟩

lemma forcesMonoTriangle_of_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {C : Type*} (φ : V → W) (hφ : ∀ u w, G.Adj u w → H.Adj (φ u) (φ w))
    (hG : ForcesMonoTriangle G C) : ForcesMonoTriangle H C := by
  intro col
  let colG : G.edgeSet → C := fun e =>
    col ⟨Sym2.map φ e.1, by
      rcases e with ⟨p, hp⟩
      induction p using Sym2.ind with
      | _ u w => exact hφ u w hp⟩
  obtain ⟨x, y, z, hab, hbc, hac, h1, h2⟩ := hG colG
  exact ⟨φ x, φ y, φ z, hφ x y hab, hφ y z hbc, hφ x z hac, h1, h2⟩

lemma not_forcesMonoTriangle_of_card_edges_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    {k : ℕ} (hk : G.edgeFinset.card ≤ k) :
    ¬ForcesMonoTriangle G (Fin (k + 1)) := by
  intro hF
  -- Inject `G.edgeSet` into `Fin G.edgeFinset.card`, hence into `Fin (k + 1)`!
  have hcard : Fintype.card G.edgeSet = G.edgeFinset.card := by
    simp [SimpleGraph.edgeFinset]
  let eqv : G.edgeSet ≃ Fin (Fintype.card G.edgeSet) := Fintype.equivFin G.edgeSet
  let col : G.edgeSet → Fin (k + 1) := fun e =>
    ⟨(eqv e).val, by omega⟩
  obtain ⟨x, y, z, hab, hbc, hac, h1, h2⟩ := hF col
  have hinj : Function.Injective col := by
    intro e₁ e₂ heq
    apply eqv.injective
    ext
    simpa [col] using congrArg Fin.val heq
  have heq_edges : (⟨s(x, y), hab⟩ : G.edgeSet) = ⟨s(y, z), hbc⟩ := hinj h1
  have hsym_eq : s(x, y) = s(y, z) := congrArg Subtype.val heq_edges
  rw [Sym2.eq_iff] at hsym_eq
  rcases hsym_eq with ⟨hxy, _⟩ | ⟨hxz, _⟩
  · exact G.ne_of_adj hab hxy
  · exact G.ne_of_adj hac hxz

/-! ## 2. Canonical Finite Graph Models and Subgraph Families -/

/-- A canonical finite simple graph: vertex count `verts : ℕ` with graph `graph : SimpleGraph (Fin verts)`. -/
structure FiniteGraph where
  verts : ℕ
  graph : SimpleGraph (Fin verts)

/-- Injective adjacency-preserving embedding (ordinary subgraph copy) between `FiniteGraph`s. -/
def EmbedsInto (H G : FiniteGraph) : Prop :=
  ∃ φ : Fin H.verts → Fin G.verts, Function.Injective φ ∧
    ∀ u v, H.graph.Adj u v → G.graph.Adj (φ u) (φ v)

/-- Injective adjacency-reflecting embedding (induced subgraph copy) between `FiniteGraph`s. -/
def InducesInto (H G : FiniteGraph) : Prop :=
  ∃ φ : Fin H.verts → Fin G.verts, Function.Injective φ ∧
    ∀ u v, H.graph.Adj u v ↔ G.graph.Adj (φ u) (φ v)

lemma EmbedsInto.refl (G : FiniteGraph) : EmbedsInto G G :=
  ⟨id, Function.injective_id, fun _ _ h => h⟩

lemma InducesInto.refl (G : FiniteGraph) : InducesInto G G :=
  ⟨id, Function.injective_id, fun _ _ => Iff.rfl⟩

lemma EmbedsInto.trans {A B C : FiniteGraph} (h1 : EmbedsInto A B) (h2 : EmbedsInto B C) :
    EmbedsInto A C := by
  rcases h1 with ⟨f, hf, hadjf⟩
  rcases h2 with ⟨g, hg, hadjg⟩
  exact ⟨g ∘ f, hg.comp hf, fun u v h => hadjg _ _ (hadjf u v h)⟩

lemma InducesInto.trans {A B C : FiniteGraph} (h1 : InducesInto A B) (h2 : InducesInto B C) :
    InducesInto A C := by
  rcases h1 with ⟨f, hf, hadjf⟩
  rcases h2 with ⟨g, hg, hadjg⟩
  exact ⟨g ∘ f, hg.comp hf, fun u v => (hadjf u v).trans (hadjg _ _)⟩

lemma InducesInto.toEmbeds {H G : FiniteGraph} (h : InducesInto H G) : EmbedsInto H G := by
  rcases h with ⟨f, hf, hadj⟩
  exact ⟨f, hf, fun u v huv => (hadj u v).mp huv⟩

lemma EmbedsInto.verts_le {H G : FiniteGraph} (h : EmbedsInto H G) : H.verts ≤ G.verts := by
  rcases h with ⟨f, hf, -⟩
  simpa using Fintype.card_le_of_injective f hf

lemma EmbedsInto.edges_le {H G : FiniteGraph} (h : EmbedsInto H G) :
    H.graph.edgeFinset.card ≤ G.graph.edgeFinset.card := by
  rcases h with ⟨f, hf, hadj⟩
  have hinj : Function.Injective (Sym2.map f) := Sym2.map.injective hf
  have hsub : H.graph.edgeFinset.image (Sym2.map f) ⊆ G.graph.edgeFinset := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at he' ⊢
    induction e' using Sym2.ind with
    | _ u v => exact hadj u v he'
  calc H.graph.edgeFinset.card
      = (H.graph.edgeFinset.image (Sym2.map f)).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ G.graph.edgeFinset.card := Finset.card_le_card hsub

/-- `ClosedUnderSubgraphs S` means `S` is closed under isomorphism and taking ordinary subgraphs. -/
def ClosedUnderSubgraphs (S : Set FiniteGraph) : Prop :=
  ∀ G ∈ S, ∀ H : FiniteGraph, EmbedsInto H G → H ∈ S

/-- `ClosedUnderInducedSubgraphs S` means `S` is closed under isomorphism and taking induced subgraphs. -/
def ClosedUnderInducedSubgraphs (S : Set FiniteGraph) : Prop :=
  ∀ G ∈ S, ∀ H : FiniteGraph, InducesInto H G → H ∈ S

/-- `AllFiniteSubgraphsIn G S`: every finite ordinary subgraph of `G : SimpleGraph V` belongs to `S`. -/
def AllFiniteSubgraphsIn {V : Type*} (G : SimpleGraph V) (S : Set FiniteGraph) : Prop :=
  ∀ H : FiniteGraph,
    (∃ φ : Fin H.verts → V, Function.Injective φ ∧ ∀ u v, H.graph.Adj u v → G.Adj (φ u) (φ v)) →
    H ∈ S

/-- `AllFiniteInducedSubgraphsIn G S`: every finite induced subgraph of `G : SimpleGraph V` belongs to `S`. -/
def AllFiniteInducedSubgraphsIn {V : Type*} (G : SimpleGraph V) (S : Set FiniteGraph) : Prop :=
  ∀ H : FiniteGraph,
    (∃ φ : Fin H.verts → V, Function.Injective φ ∧ ∀ u v, H.graph.Adj u v ↔ G.Adj (φ u) (φ v)) →
    H ∈ S

/-! ## 3. The `(2|S| - 3)`-Sparsity 2-Colorability Theorem -/

/-- Number of edges of `G` whose endpoints both lie in `S : Finset V`. -/
noncomputable def edgesInside {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)).card

/-- `SparseFourSubsets G` holds when every subset `S` of `≥ 4` vertices spans at most `2|S| - 3` edges. -/
def SparseFourSubsets {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, 4 ≤ S.card → edgesInside G S ≤ 2 * S.card - 3

lemma edgesInside_univ {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgesInside G Finset.univ = G.edgeFinset.card := by
  simp [edgesInside]

lemma edgesInside_le_of_emb {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ u v, G.Adj u v → H.Adj (f u) (f v)) (S : Finset V) :
    edgesInside G S ≤ edgesInside H (S.image f) := by
  unfold edgesInside
  have hinj : Function.Injective (Sym2.map f) := Sym2.map.injective hf
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_le_card
  intro e he
  rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he' ⊢
  rcases he' with ⟨hadj', hmem'⟩
  induction e' using Sym2.ind with
  | _ u v =>
    refine ⟨hadj u v hadj', ?_⟩
    intro x hx
    simp only [Sym2.map_mk, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_image_of_mem f (hmem' u (Sym2.mem_mk_left u v))
    · exact Finset.mem_image_of_mem f (hmem' v (Sym2.mem_mk_right u v))

lemma sparseFourSubsets_of_emb {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ u v, G.Adj u v → H.Adj (f u) (f v))
    (hH : SparseFourSubsets H) : SparseFourSubsets G := by
  intro S hS
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S hf
  calc edgesInside G S
      ≤ edgesInside H (S.image f) := edgesInside_le_of_emb f hf hadj S
    _ ≤ 2 * (S.image f).card - 3 := hH (S.image f) (by omega)
    _ = 2 * S.card - 3 := by rw [hcard]

private def swapBit (c : Fin 2) : Fin 2 := 1 - c

private lemma swapBit_ne (c : Fin 2) : swapBit c ≠ c := by
  fin_cases c <;> decide

/-- Local star-extension lemma: if `v` has neighbor set `N` of size `≤ 3` and `N` does not induce `K₃`,
any 2-coloring `col0` of the remaining edges extends to incident edges `(v, x)` without creating
a monochromatic triangle at `v`. -/
private lemma extend_star_two_coloring {V : Type*} (G : SimpleGraph V) (v : V)
    (N : Finset V) (hN_card : N.card ≤ 3) (hN_adj : ∀ x, G.Adj v x → x ∈ N)
    (hN_not_k3 : ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N,
      a ≠ b → b ≠ c → a ≠ c → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c))
    (col0 : Sym2 V → Fin 2) :
    ∃ ext : V → Fin 2, ∀ x y : V,
      G.Adj v x → G.Adj v y → G.Adj x y →
        ¬(ext x = ext y ∧ ext y = col0 s(x, y)) := by
  by_cases hex : ∃ a ∈ N, ∃ b ∈ N, G.Adj a b
  · obtain ⟨a, haN, b, hbN, hab⟩ := hex
    have hab_ne : a ≠ b := G.ne_of_adj hab
    have h_third_uniq : ∀ u ∈ N, ∀ w ∈ N, u ≠ a → u ≠ b → w ≠ a → w ≠ b → u = w := by
      intro u hu w hw hua hub hwa hwb
      by_contra huw
      have hsub : ({a, b, u, w} : Finset V) ⊆ N := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> assumption
      have h4 : ({a, b, u, w} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton]
        · simpa using huw
        · simp [hub.symm, hwb.symm]
        · simp [hab_ne, hua.symm, hwa.symm]
      have := Finset.card_le_card hsub
      omega
    by_cases hca : ∃ c ∈ N, c ≠ a ∧ c ≠ b ∧ G.Adj a c
    · obtain ⟨c, hcN, hca_ne, hcb_ne, hac⟩ := hca
      have hnbc : ¬G.Adj b c := fun hbc =>
        hN_not_k3 a haN b hbN c hcN hab_ne hcb_ne.symm hca_ne.symm ⟨hab, hbc, hac⟩
      refine ⟨fun z =>
        if z = a then col0 s(a, b)
        else if z = b then swapBit (col0 s(a, b))
        else swapBit (col0 s(a, c)), ?_⟩
      intro x y hvx hvy hxy ⟨h1, h2⟩
      have hxN : x ∈ N := hN_adj x hvx
      have hyN : y ∈ N := hN_adj y hvy
      have hxy_ne : x ≠ y := G.ne_of_adj hxy
      by_cases hxa : x = a
      · subst hxa
        by_cases hyb : y = b
        · subst hyb
          simp [hab_ne.symm] at h1
          exact swapBit_ne (col0 s(x, y)) h1.symm
        · have hyc : y = c := h_third_uniq y hyN c hcN hxy_ne.symm hyb hca_ne hcb_ne
          subst hyc
          have hya : y ≠ x := hxy_ne.symm
          simp [hya, hyb] at h1 h2
          exact swapBit_ne (col0 s(x, y)) h2
      · by_cases hxb : x = b
        · subst hxb
          by_cases hya : y = a
          · subst hya
            have hba : x ≠ y := hxy_ne
            have hsym : s(x, y) = s(y, x) := Sym2.eq_swap
            simp [hba] at h1 h2
            rw [hsym] at h2
            exact swapBit_ne (col0 s(y, x)) h1
          · have hyc : y = c := h_third_uniq y hyN c hcN hya hxy_ne.symm hca_ne hcb_ne
            subst hyc
            exact hnbc hxy
        · have hxc : x = c := h_third_uniq x hxN c hcN hxa hxb hca_ne hcb_ne
          subst hxc
          by_cases hya : y = a
          · subst hya
            have hsym : s(x, y) = s(y, x) := Sym2.eq_swap
            simp [hxa, hxb] at h1 h2
            rw [hsym] at h2
            exact swapBit_ne (col0 s(y, x)) (h1.trans h2)
          · by_cases hyb : y = b
            · subst hyb
              exact hnbc (G.adj_symm hxy)
            · exact hxy_ne (h_third_uniq x hxN y hyN hxa hxb hya hyb)
    · refine ⟨fun z =>
        if z = b then col0 s(a, b)
        else if z = a then swapBit (col0 s(a, b))
        else swapBit (col0 s(b, z)), ?_⟩
      intro x y hvx hvy hxy ⟨h1, h2⟩
      have hxN : x ∈ N := hN_adj x hvx
      have hyN : y ∈ N := hN_adj y hvy
      have hxy_ne : x ≠ y := G.ne_of_adj hxy
      by_cases hxb : x = b
      · subst hxb
        by_cases hya : y = a
        · subst hya
          simp [hab_ne] at h1 h2
          exact swapBit_ne (col0 s(y, x)) h1.symm
        · simp [hya, hxy_ne.symm] at h1 h2
          exact swapBit_ne (col0 s(x, y)) h2
      · by_cases hxa : x = a
        · subst hxa
          by_cases hyb : y = b
          · subst hyb
            simp [hab_ne] at h1 h2
            exact swapBit_ne (col0 s(x, y)) h1
          · exfalso
            exact hca ⟨y, hyN, hxy_ne.symm, hyb, hxy⟩
        · by_cases hyb : y = b
          · subst hyb
            have hsym : s(x, y) = s(y, x) := Sym2.eq_swap
            simp [hxb, hxa] at h1 h2
            rw [hsym] at h2
            exact swapBit_ne (col0 s(y, x)) (h1.trans h2)
          · by_cases hya : y = a
            · subst hya
              exfalso
              exact hca ⟨x, hxN, hxa, hxb, G.adj_symm hxy⟩
            · exact hxy_ne (h_third_uniq x hxN y hyN hxa hxb hya hyb)
  · refine ⟨fun _ => 0, ?_⟩
    intro x y hvx hvy hxy
    exfalso
    exact hex ⟨x, hN_adj x hvx, y, hN_adj y hvy, hxy⟩

private lemma neighbor_not_k3_of_sparse {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : SparseFourSubsets G) (v a b c : V)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab_ne : a ≠ b) (hbc_ne : b ≠ c) (hac_ne : a ≠ c) :
    ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) := by
  rintro ⟨hab, hbc, hac⟩
  have hv_ne_a : v ≠ a := G.ne_of_adj hva
  have hv_ne_b : v ≠ b := G.ne_of_adj hvb
  have hv_ne_c : v ≠ c := G.ne_of_adj hvc
  let S : Finset V := {v, a, b, c}
  have hS_card : S.card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hbc_ne
    · simp [hab_ne, hac_ne]
    · simp [hv_ne_a, hv_ne_b, hv_ne_c]
  let E₆ : Finset (Sym2 V) := {s(v, a), s(v, b), s(v, c), s(a, b), s(b, c), s(a, c)}
  have hE₆_sub : E₆ ⊆ G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S) := by
    intro e he
    simp only [E₆, Finset.mem_insert, Finset.mem_singleton] at he
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hva, fun x hx => by simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> simp [S]⟩
    · exact ⟨hvb, fun x hx => by simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> simp [S]⟩
    · exact ⟨hvc, fun x hx => by simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> simp [S]⟩
    · exact ⟨hab, fun x hx => by simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> simp [S]⟩
    · exact ⟨hbc, fun x hx => by simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> simp [S]⟩
    · exact ⟨hac, fun x hx => by simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> simp [S]⟩
  have hE₆_card : E₆.card = 6 := by
    let g : Fin 4 → V := fun i => match i.val with
      | 0 => v
      | 1 => a
      | 2 => b
      | _ => c
    have hg_inj : Function.Injective g := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [g] at hij ⊢
      all_goals first
        | exact absurd hij hv_ne_a
        | exact absurd hij hv_ne_b
        | exact absurd hij hv_ne_c
        | exact absurd hij.symm hv_ne_a
        | exact absurd hij.symm hv_ne_b
        | exact absurd hij.symm hv_ne_c
        | exact absurd hij hab_ne
        | exact absurd hij hac_ne
        | exact absurd hij.symm hab_ne
        | exact absurd hij hbc_ne
        | exact absurd hij.symm hac_ne
        | exact absurd hij.symm hbc_ne
    let E₀ : Finset (Sym2 (Fin 4)) := {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(2, 3), s(1, 3)}
    have hE₀_card : E₀.card = 6 := by decide
    have hE₆_eq : E₀.image (Sym2.map g) = E₆ := by
      ext e
      simp [E₀, E₆, g]
    rw [← hE₆_eq, Finset.card_image_of_injective _ (Sym2.map.injective hg_inj), hE₀_card]
  have h6 : 6 ≤ edgesInside G S := by
    unfold edgesInside
    calc 6 = E₆.card := hE₆_card.symm
      _ ≤ _ := Finset.card_le_card hE₆_sub
  have h5 : edgesInside G S ≤ 2 * S.card - 3 := hG S (by omega)
  omega

private lemma exists_deg_le_three_of_sparse {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : SparseFourSubsets G) :
    ∃ v : Fin n, G.degree v ≤ 3 := by
  by_cases hn4 : n < 4
  · refine ⟨⟨0, by omega⟩, ?_⟩
    have := G.degree_lt_card_verts ⟨0, by omega⟩
    simp at this
    omega
  · by_contra! hdeg
    have hsum_ge : 4 * n ≤ ∑ v : Fin n, G.degree v := by
      calc 4 * n = ∑ _v : Fin n, 4 := by simp [Nat.mul_comm]
        _ ≤ ∑ v : Fin n, G.degree v := Finset.sum_le_sum (fun v _ => hdeg v)
    have hshake : ∑ v : Fin n, G.degree v = 2 * G.edgeFinset.card :=
      G.sum_degrees_eq_twice_card_edges
    have huniv : G.edgeFinset.card ≤ 2 * n - 3 := by
      have h := hG Finset.univ (by simp; omega)
      simpa [edgesInside_univ] using h
    omega

/-- **The `(2|S| - 3)`-Sparsity 2-Coloring Theorem**:
Every finite graph `G` with `SparseFourSubsets G` admits a 2-coloring `Sym2 (Fin n) → Fin 2`
without monochromatic triangles. -/
theorem two_colorable_of_sparse_subsets :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), SparseFourSubsets G →
      ∃ col : Sym2 (Fin n) → Fin 2, ¬HasMonoTriangle G col
  | 0, _G, _ => ⟨fun _ => 0, by rintro ⟨x, -⟩; exact Fin.elim0 x⟩
  | n + 1, G, hG => by
    obtain ⟨v, hv_deg⟩ := exists_deg_le_three_of_sparse (Nat.succ_pos n) G hG
    let emb : Fin n → Fin (n + 1) := v.succAbove
    have hemb_inj : Function.Injective emb := Fin.succAbove_right_injective
    let G' : SimpleGraph (Fin n) := SimpleGraph.comap emb G
    have hadj' : ∀ i j, G'.Adj i j → G.Adj (emb i) (emb j) := fun _ _ h => h
    have hG'_sparse : SparseFourSubsets G' := sparseFourSubsets_of_emb emb hemb_inj hadj' hG
    obtain ⟨col', hcol'⟩ := two_colorable_of_sparse_subsets n G' hG'_sparse
    have hex_pre : ∀ x : Fin (n + 1), x ≠ v → ∃ i : Fin n, emb i = x :=
      fun _ hxv => Fin.exists_succAbove_eq hxv
    let invEmb : (x : Fin (n + 1)) → x ≠ v → Fin n := fun x hxv => Classical.choose (hex_pre x hxv)
    have hinv_eq : ∀ x (hxv : x ≠ v), emb (invEmb x hxv) = x :=
      fun x hxv => Classical.choose_spec (hex_pre x hxv)
    let col0 : Sym2 (Fin (n + 1)) → Fin 2 :=
      Sym2.lift ⟨fun x y =>
        if hxv : x = v then 0
        else if hyv : y = v then 0
        else col' s(invEmb x hxv, invEmb y hyv), by
          intro x y
          by_cases hxv : x = v <;> by_cases hyv : y = v <;> simp [hxv, hyv, Sym2.eq_swap]⟩
    have hcol0_away : ∀ (x y : Fin (n + 1)) (hx : x ≠ v) (hy : y ≠ v),
        col0 s(x, y) = col' s(invEmb x hx, invEmb y hy) := by
      intro x y hx hy
      simp [col0, hx, hy]
    let N : Finset (Fin (n + 1)) := G.neighborFinset v
    have hN_card : N.card ≤ 3 := by simpa [N, SimpleGraph.card_neighborFinset_eq_degree] using hv_deg
    have hN_adj : ∀ x, G.Adj v x → x ∈ N := fun x hx => (G.mem_neighborFinset v x).mpr hx
    have hN_not_k3 : ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N,
        a ≠ b → b ≠ c → a ≠ c → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) := by
      intro a ha b hb c hc hab hbc hac
      exact neighbor_not_k3_of_sparse hG v a b c
        ((G.mem_neighborFinset v a).mp ha)
        ((G.mem_neighborFinset v b).mp hb)
        ((G.mem_neighborFinset v c).mp hc) hab hbc hac
    obtain ⟨ext, hext⟩ := extend_star_two_coloring G v N hN_card hN_adj hN_not_k3 col0
    let col : Sym2 (Fin (n + 1)) → Fin 2 :=
      Sym2.lift ⟨fun x y =>
        if x = v then ext y
        else if y = v then ext x
        else col0 s(x, y), by
          intro x y
          by_cases hxv : x = v
          · subst hxv
            by_cases hyv : y = x
            · subst hyv; simp
            · simp [hyv]
          · by_cases hyv : y = v
            · subst hyv; simp [hxv]
            · simp [hxv, hyv, Sym2.eq_swap]⟩
    refine ⟨col, ?_⟩
    rintro ⟨x, y, z, hab, hbc, hac, h1, h2⟩
    by_cases hxv : x = v
    · subst hxv
      have hyv : y ≠ x := (G.ne_of_adj hab).symm
      have hzv : z ≠ x := (G.ne_of_adj hac).symm
      have hab_c : col s(x, y) = ext y := by simp [col]
      have hac_c : col s(x, z) = ext z := by simp [col]
      have hbc_c : col s(y, z) = col0 s(y, z) := by simp [col, hyv, hzv]
      apply hext y z hab hac hbc
      exact ⟨by rw [← hab_c, ← hac_c]; exact h1.trans h2, by rw [← hac_c, ← hbc_c]; exact h2.symm⟩
    · by_cases hyv : y = v
      · subst hyv
        have hxv' : x ≠ y := G.ne_of_adj hab
        have hzv : z ≠ y := (G.ne_of_adj hbc).symm
        have hab_c : col s(x, y) = ext x := by simp [col, hxv']
        have hbc_c : col s(y, z) = ext z := by simp [col]
        have hac_c : col s(x, z) = col0 s(x, z) := by simp [col, hxv', hzv]
        apply hext x z (G.adj_symm hab) hbc hac
        exact ⟨by rw [← hab_c, ← hbc_c]; exact h1, by rw [← hbc_c, ← hac_c]; exact h2⟩
      · by_cases hzv : z = v
        · subst hzv
          have hxv' : x ≠ z := G.ne_of_adj hac
          have hyv' : y ≠ z := G.ne_of_adj hbc
          have hac_c : col s(x, z) = ext x := by simp [col, hxv']
          have hbc_c : col s(y, z) = ext y := by simp [col, hyv']
          have hab_c : col s(x, y) = col0 s(x, y) := by simp [col, hxv', hyv']
          apply hext x y (G.adj_symm hac) (G.adj_symm hbc) hab
          exact ⟨by rw [← hac_c, ← hbc_c]; exact h2.symm, by rw [← hbc_c, ← hab_c]; exact h1.symm⟩
        · let ix := invEmb x hxv
          let iy := invEmb y hyv
          let iz := invEmb z hzv
          have hix : emb ix = x := hinv_eq x hxv
          have hiy : emb iy = y := hinv_eq y hyv
          have hiz : emb iz = z := hinv_eq z hzv
          have hab_c : col s(x, y) = col' s(ix, iy) := by simp [col, hxv, hyv, hcol0_away, ix, iy]
          have hbc_c : col s(y, z) = col' s(iy, iz) := by simp [col, hyv, hzv, hcol0_away, iy, iz]
          have hac_c : col s(x, z) = col' s(ix, iz) := by simp [col, hxv, hzv, hcol0_away, ix, iz]
          apply hcol'
          refine ⟨ix, iy, iz,
            by simpa [G', hix, hiy] using hab,
            by simpa [G', hiy, hiz] using hbc,
            by simpa [G', hix, hiz] using hac,
            by rw [← hab_c, ← hbc_c]; exact h1,
            by rw [← hbc_c, ← hac_c]; exact h2⟩

theorem not_forcesMonoTriangle_two_of_sparse {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : SparseFourSubsets G) : ¬ForcesMonoTriangle G (Fin 2) := by
  intro hF
  rw [forcesMonoTriangle_iff_sym2] at hF
  obtain ⟨col, hcol⟩ := two_colorable_of_sparse_subsets n G hG
  exact hcol (hF col)

/-- **Dense Subgraph Certificate**:
Every finite graph `G` with `ForcesMonoTriangle G (Fin 2)` contains a vertex subset `S`
of size `4 ≤ S.card` spanning at least `2 * S.card - 2` edges! -/
theorem exists_dense_four_plus_subset {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ForcesMonoTriangle G (Fin 2)) :
    ∃ S : Finset (Fin n), 4 ≤ S.card ∧ 2 * S.card - 2 ≤ edgesInside G S := by
  by_contra! hsparse
  have hS : SparseFourSubsets G := by
    intro S hS4
    have hlt := hsparse S hS4
    omega
  exact not_forcesMonoTriangle_two_of_sparse hS hG

/-! ## 4. Minimal 2-Color Triangle-Forcing Cores (Clean-Room Formulation) -/

/-- `IsMinimalTwoRamsey M` means `M → (K₃)²_2` and no graph of strictly smaller `(verts, edges)`
embeds into `M` while still forcing a monochromatic triangle under 2 colors. -/
def IsMinimalTwoRamsey (M : FiniteGraph) : Prop :=
  ForcesMonoTriangle M.graph (Fin 2) ∧
  ∀ H : FiniteGraph, EmbedsInto H M → ForcesMonoTriangle H.graph (Fin 2) → EmbedsInto M H

/-- Every finite graph forcing a monochromatic triangle under 2 colors contains a minimal such core. -/
lemma exists_minimal_two_ramsey (G : FiniteGraph) (hG : ForcesMonoTriangle G.graph (Fin 2)) :
    ∃ M : FiniteGraph, IsMinimalTwoRamsey M ∧ EmbedsInto M G := by
  let W : ℕ := G.verts * G.verts + 1
  let P : ℕ → Prop := fun m =>
    ∃ H : FiniteGraph, EmbedsInto H G ∧ ForcesMonoTriangle H.graph (Fin 2) ∧
      H.verts * W + H.graph.edgeFinset.card = m
  have hP : ∃ m, P m := ⟨G.verts * W + G.graph.edgeFinset.card, G, EmbedsInto.refl G, hG, rfl⟩
  let m₀ := Nat.find hP
  obtain ⟨M, hMG, hM2, hm₀⟩ := Nat.find_spec hP
  refine ⟨M, ⟨hM2, ?_⟩, hMG⟩
  intro H hHM hH2
  have hHG : EmbedsInto H G := hHM.trans hMG
  have hmin : m₀ ≤ H.verts * W + H.graph.edgeFinset.card :=
    Nat.find_min' hP ⟨H, hHG, hH2, rfl⟩
  have hle_v : H.verts ≤ M.verts := hHM.verts_le
  have hle_e : H.graph.edgeFinset.card ≤ M.graph.edgeFinset.card := hHM.edges_le
  have heq_v : H.verts = M.verts := by
    by_contra hne
    have hlt_v : H.verts + 1 ≤ M.verts := Nat.succ_le_of_lt (lt_of_le_of_ne hle_v hne)
    have he_lt : H.graph.edgeFinset.card < W := by
      have h1 : H.graph.edgeFinset.card ≤ Fintype.card (Sym2 (Fin H.verts)) := Finset.card_le_univ _
      have h2 : Fintype.card (Sym2 (Fin H.verts)) ≤ G.verts * G.verts := by
        calc Fintype.card (Sym2 (Fin H.verts))
            ≤ Fintype.card (Fin H.verts × Fin H.verts) :=
              Fintype.card_le_of_surjective _ Sym2.mk_surjective
          _ = H.verts * H.verts := by simp
          _ ≤ G.verts * G.verts := Nat.mul_le_mul hHG.verts_le hHG.verts_le
      omega
    have hlt_tot : H.verts * W + H.graph.edgeFinset.card < M.verts * W + M.graph.edgeFinset.card := by
      calc H.verts * W + H.graph.edgeFinset.card
          < H.verts * W + W := by omega
        _ = (H.verts + 1) * W := by ring
        _ ≤ M.verts * W := Nat.mul_le_mul_right W hlt_v
        _ ≤ M.verts * W + M.graph.edgeFinset.card := Nat.le_add_right _ _
    have hm_eq : m₀ = M.verts * W + M.graph.edgeFinset.card := hm₀.symm
    omega
  have hm_eq : m₀ = M.verts * W + M.graph.edgeFinset.card := hm₀.symm
  have hprod_eq : H.verts * W = M.verts * W := by rw [heq_v]
  have heq_e : H.graph.edgeFinset.card = M.graph.edgeFinset.card := by omega
  rcases hHM with ⟨f, hf, hadj⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf, by simp [heq_v]⟩
  let invf := Function.surjInv hbij.2
  have hfinv : ∀ x, f (invf x) = x := Function.surjInv_eq hbij.2
  have hinvf : ∀ y, invf (f y) = y := fun y => hf (hfinv (f y))
  have hinj_inv : Function.Injective invf := Function.RightInverse.injective hfinv
  have himg : H.graph.edgeFinset.image (Sym2.map f) = M.graph.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
      rw [SimpleGraph.mem_edgeFinset] at he' ⊢
      induction e' using Sym2.ind with
      | _ u v => exact hadj u v he'
    · rw [Finset.card_image_of_injective _ (Sym2.map.injective hf), heq_e]
  refine ⟨invf, hinj_inv, ?_⟩
  intro x y hxy
  have hmem : s(x, y) ∈ M.graph.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hxy
  rw [← himg] at hmem
  rcases Finset.mem_image.mp hmem with ⟨e', he', heq⟩
  rw [SimpleGraph.mem_edgeFinset] at he'
  induction e' using Sym2.ind with
  | _ u v =>
    simp only [Sym2.map_mk, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [hinvf] using he'
    · simpa [hinvf] using H.graph.adj_symm he'

end Erdos638
