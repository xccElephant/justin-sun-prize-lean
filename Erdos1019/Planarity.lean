/-
Copyright 2026 Chucheng Xiang (@xccElephant).
SPDX-License-Identifier: Apache-2.0

Clean-room topological definition of graph planarity in `ℝ × ℝ` via continuous injective Jordan
arcs on `[0, 1]`, pullback monotonicity along injective graph homomorphisms (`SimpleGraph.Copy`),
and a straight-line Fáry-segment constructor (`IsPlanar.of_straightLine`).
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos1019

open scoped SimpleGraph

/-- Standard parameter `0 ∈ [0, 1]` on the unit interval `Set.Icc (0 : ℝ) 1`. -/
def unitZero : Set.Icc (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_le_one⟩⟩

/-- Standard parameter `1 ∈ [0, 1]` on the unit interval `Set.Icc (0 : ℝ) 1`. -/
def unitOne : Set.Icc (0 : ℝ) 1 := ⟨1, ⟨zero_le_one, le_rfl⟩⟩

@[simp] theorem coe_unitZero : (unitZero : ℝ) = 0 := rfl
@[simp] theorem coe_unitOne : (unitOne : ℝ) = 1 := rfl

theorem unitZero_ne_unitOne : unitZero ≠ unitOne := by
  intro h
  have hval : (0 : ℝ) = 1 := congrArg Subtype.val h
  norm_num at hval

/-- A topological plane drawing of a simple graph `G : SimpleGraph W` in `ℝ × ℝ`:
an injective vertex placement `vPos : W ↪ ℝ × ℝ` together with, for each unordered edge
`e ∈ G.edgeSet`, a continuous injective curve `arc e he : Set.Icc (0 : ℝ) 1 → ℝ × ℝ` whose
unordered endpoints `{arc 0, arc 1}` equal the image of the endpoints of `e`, whose open interior
`(0, 1)` avoids all vertex positions `Set.range vPos`, and such that arcs of distinct edges meet
at most at shared endpoints (`t₁ ∈ {0, 1}` and `t₂ ∈ {0, 1}`). -/
structure PlaneDrawing {W : Type*} (G : SimpleGraph W) where
  vPos : W ↪ ℝ × ℝ
  arc : ∀ e : Sym2 W, e ∈ G.edgeSet → Set.Icc (0 : ℝ) 1 → ℝ × ℝ
  arc_continuous : ∀ (e : Sym2 W) (he : e ∈ G.edgeSet), Continuous (arc e he)
  arc_injective : ∀ (e : Sym2 W) (he : e ∈ G.edgeSet), Function.Injective (arc e he)
  arc_endpoints : ∀ (e : Sym2 W) (he : e ∈ G.edgeSet),
    ({arc e he unitZero, arc e he unitOne} : Set (ℝ × ℝ)) = vPos '' {w : W | w ∈ e}
  arc_interior_disjoint : ∀ (e : Sym2 W) (he : e ∈ G.edgeSet) (t : Set.Icc (0 : ℝ) 1),
    (0 : ℝ) < t.1 → t.1 < 1 → arc e he t ∉ Set.range vPos
  arc_inter_endpoints :
    ∀ (e₁ : Sym2 W) (he₁ : e₁ ∈ G.edgeSet) (e₂ : Sym2 W) (he₂ : e₂ ∈ G.edgeSet),
      e₁ ≠ e₂ → ∀ (t₁ t₂ : Set.Icc (0 : ℝ) 1),
        arc e₁ he₁ t₁ = arc e₂ he₂ t₂ →
          ((t₁.1 = 0 ∨ t₁.1 = 1) ∧ (t₂.1 = 0 ∨ t₂.1 = 1))

/-- A simple graph `G` is planar if it admits a topological `PlaneDrawing` in `ℝ × ℝ`. -/
def IsPlanar {W : Type*} (G : SimpleGraph W) : Prop :=
  Nonempty (PlaneDrawing G)

/-- Pulling back a `PlaneDrawing` along an injective graph homomorphism `f : H.Copy G`. -/
def PlaneDrawing.pullback {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    (D : PlaneDrawing G) (f : H.Copy G) : PlaneDrawing H where
  vPos := f.toEmbedding.trans D.vPos
  arc e he := D.arc (e.map f) (f.toHom.map_mem_edgeSet he)
  arc_continuous e he := D.arc_continuous (e.map f) (f.toHom.map_mem_edgeSet he)
  arc_injective e he := D.arc_injective (e.map f) (f.toHom.map_mem_edgeSet he)
  arc_endpoints e he := by
    rw [D.arc_endpoints (e.map f) (f.toHom.map_mem_edgeSet he)]
    induction e using Sym2.inductionOn with
    | hf u v =>
      ext p
      simp only [Sym2.map_mk, Sym2.mem_iff, Set.mem_image,
        Function.Embedding.trans_apply, SimpleGraph.Copy.toEmbedding]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with hxu | hxv
        · rw [hxu]; exact ⟨u, Or.inl rfl, rfl⟩
        · rw [hxv]; exact ⟨v, Or.inr rfl, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rcases hw with hwu | hwv
        · rw [hwu]; exact ⟨f u, Or.inl rfl, rfl⟩
        · rw [hwv]; exact ⟨f v, Or.inr rfl, rfl⟩
  arc_interior_disjoint e he t ht0 ht1 hmem := by
    rcases hmem with ⟨w, hw⟩
    refine D.arc_interior_disjoint (e.map f) (f.toHom.map_mem_edgeSet he) t ht0 ht1 ?_
    exact ⟨f w, hw⟩
  arc_inter_endpoints e₁ he₁ e₂ he₂ hne t₁ t₂ heq := by
    refine D.arc_inter_endpoints (e₁.map f) (f.toHom.map_mem_edgeSet he₁)
      (e₂.map f) (f.toHom.map_mem_edgeSet he₂) ?_ t₁ t₂ heq
    intro hmap
    exact hne (Sym2.map.injective f.injective hmap)

theorem IsPlanar.of_copy {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    (f : H.Copy G) (hG : IsPlanar G) : IsPlanar H := by
  rcases hG with ⟨D⟩
  exact ⟨D.pullback f⟩

theorem IsPlanar.of_isContained {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    (hsub : H ⊑ G) (hG : IsPlanar G) : IsPlanar H := by
  rcases hsub with ⟨f⟩
  exact IsPlanar.of_copy f hG

theorem IsPlanar.of_le {W : Type*} {H G : SimpleGraph W}
    (hle : H ≤ G) (hG : IsPlanar G) : IsPlanar H :=
  IsPlanar.of_copy (SimpleGraph.Copy.ofLE H G hle) hG

/-- Affine straight-line parameterization `(1 - t) • p + t • q` in `ℝ × ℝ`. -/
def lineSeg (p q : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)

@[simp] theorem lineSeg_zero (p q : ℝ × ℝ) : lineSeg p q 0 = p := by
  ext <;> simp [lineSeg]

@[simp] theorem lineSeg_one (p q : ℝ × ℝ) : lineSeg p q 1 = q := by
  ext <;> simp [lineSeg]

theorem lineSeg_symm (p q : ℝ × ℝ) (t : ℝ) : lineSeg p q t = lineSeg q p (1 - t) := by
  ext <;> simp [lineSeg] <;> ring

theorem lineSeg_continuous (p q : ℝ × ℝ) :
    Continuous (fun t : Set.Icc (0 : ℝ) 1 => lineSeg p q t.1) := by
  unfold lineSeg
  fun_prop

theorem lineSeg_injective {p q : ℝ × ℝ} (hpq : p ≠ q) :
    Function.Injective (fun t : Set.Icc (0 : ℝ) 1 => lineSeg p q t.1) := by
  intro t₁ t₂ h
  ext
  have h1 : (1 - t₁.1) * p.1 + t₁.1 * q.1 = (1 - t₂.1) * p.1 + t₂.1 * q.1 :=
    congrArg Prod.fst h
  have h2 : (1 - t₁.1) * p.2 + t₁.1 * q.2 = (1 - t₂.1) * p.2 + t₂.1 * q.2 :=
    congrArg Prod.snd h
  have hd1 : (t₁.1 - t₂.1) * (q.1 - p.1) = 0 := by linarith
  have hd2 : (t₁.1 - t₂.1) * (q.2 - p.2) = 0 := by linarith
  rcases mul_eq_zero.mp hd1 with ht | hx
  · linarith
  · rcases mul_eq_zero.mp hd2 with ht | hy
    · linarith
    · exfalso
      apply hpq
      ext <;> linarith

private lemma exists_endpoints_of_mem_edgeSet {W : Type*} {G : SimpleGraph W}
    {e : Sym2 W} (he : e ∈ G.edgeSet) :
    ∃ p : W × W, e = s(p.1, p.2) ∧ G.Adj p.1 p.2 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    exact ⟨(u, v), rfl, G.mem_edgeSet.mp he⟩

/-- Any injective vertex placement `vPos : W ↪ ℝ × ℝ` whose open straight-line edge segments avoid
all vertex positions and are pairwise disjoint for distinct edges induces a genuine topological
`PlaneDrawing`. -/
theorem IsPlanar.of_straightLine {W : Type*} {G : SimpleGraph W}
    (vPos : W ↪ ℝ × ℝ)
    (hAvoidVerts : ∀ (u v w : W), G.Adj u v → ∀ t : ℝ, 0 < t → t < 1 →
      lineSeg (vPos u) (vPos v) t ≠ vPos w)
    (hDisjointOpen : ∀ (u₁ v₁ u₂ v₂ : W), G.Adj u₁ v₁ → G.Adj u₂ v₂ →
      s(u₁, v₁) ≠ s(u₂, v₂) → ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < 1 → 0 < t₂ → t₂ < 1 →
        lineSeg (vPos u₁) (vPos v₁) t₁ ≠ lineSeg (vPos u₂) (vPos v₂) t₂) :
    IsPlanar G := by
  classical
  let chosenPair : ∀ e : Sym2 W, e ∈ G.edgeSet → W × W :=
    fun e he => Classical.choose (exists_endpoints_of_mem_edgeSet he)
  have hPair_eq : ∀ (e : Sym2 W) (he : e ∈ G.edgeSet),
      e = s((chosenPair e he).1, (chosenPair e he).2) :=
    fun e he => (Classical.choose_spec (exists_endpoints_of_mem_edgeSet he)).1
  have hPair_adj : ∀ (e : Sym2 W) (he : e ∈ G.edgeSet),
      G.Adj (chosenPair e he).1 (chosenPair e he).2 :=
    fun e he => (Classical.choose_spec (exists_endpoints_of_mem_edgeSet he)).2
  refine ⟨{
    vPos := vPos
    arc := fun e he t => lineSeg (vPos (chosenPair e he).1) (vPos (chosenPair e he).2) t.1
    arc_continuous := fun e he => lineSeg_continuous _ _
    arc_injective := fun e he => by
      apply lineSeg_injective
      intro heq
      exact (hPair_adj e he).ne (vPos.injective heq)
    arc_endpoints := fun e he => by
      let uv := chosenPair e he
      have he_eq : e = s(uv.1, uv.2) := hPair_eq e he
      change ({lineSeg (vPos uv.1) (vPos uv.2) 0, lineSeg (vPos uv.1) (vPos uv.2) 1} : Set (ℝ × ℝ)) =
        vPos '' {w : W | w ∈ e}
      rw [lineSeg_zero, lineSeg_one, he_eq]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff, Set.mem_image]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨uv.1, Or.inl rfl, rfl⟩
        · exact ⟨uv.2, Or.inr rfl, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rcases hw with h1 | h2
        · rw [h1]; exact Or.inl rfl
        · rw [h2]; exact Or.inr rfl
    arc_interior_disjoint := fun e he t ht0 ht1 hmem => by
      rcases hmem with ⟨w, hw⟩
      exact hAvoidVerts (chosenPair e he).1 (chosenPair e he).2 w (hPair_adj e he)
        t.1 ht0 ht1 hw.symm
    arc_inter_endpoints := fun e₁ he₁ e₂ he₂ hne t₁ t₂ heq => by
      have hadj₁ := hPair_adj e₁ he₁
      have hadj₂ := hPair_adj e₂ he₂
      have hsym_ne : s((chosenPair e₁ he₁).1, (chosenPair e₁ he₁).2) ≠
          s((chosenPair e₂ he₂).1, (chosenPair e₂ he₂).2) := by
        rwa [← hPair_eq e₁ he₁, ← hPair_eq e₂ he₂]
      have endpoint_or_interior : ∀ t : Set.Icc (0 : ℝ) 1,
          (t.1 = 0 ∨ t.1 = 1) ∨ (0 < t.1 ∧ t.1 < 1) := by
        intro t
        rcases lt_or_eq_of_le t.2.1 with hgt | heq0
        · rcases lt_or_eq_of_le t.2.2 with hlt | heq1
          · exact Or.inr ⟨hgt, hlt⟩
          · exact Or.inl (Or.inr heq1)
        · exact Or.inl (Or.inl heq0.symm)
      rcases endpoint_or_interior t₁ with h1_end | ⟨h1_gt, h1_lt⟩
      · rcases endpoint_or_interior t₂ with h2_end | ⟨h2_gt, h2_lt⟩
        · exact ⟨h1_end, h2_end⟩
        · exfalso
          rcases h1_end with ht1_0 | ht1_1
          · change lineSeg (vPos (chosenPair e₁ he₁).1) (vPos (chosenPair e₁ he₁).2) t₁.1 = _ at heq
            rw [ht1_0, lineSeg_zero] at heq
            exact hAvoidVerts _ _ _ hadj₂ t₂.1 h2_gt h2_lt heq.symm
          · change lineSeg (vPos (chosenPair e₁ he₁).1) (vPos (chosenPair e₁ he₁).2) t₁.1 = _ at heq
            rw [ht1_1, lineSeg_one] at heq
            exact hAvoidVerts _ _ _ hadj₂ t₂.1 h2_gt h2_lt heq.symm
      · exfalso
        rcases endpoint_or_interior t₂ with h2_end | ⟨h2_gt, h2_lt⟩
        · rcases h2_end with ht2_0 | ht2_1
          · change _ = lineSeg (vPos (chosenPair e₂ he₂).1) (vPos (chosenPair e₂ he₂).2) t₂.1 at heq
            rw [ht2_0, lineSeg_zero] at heq
            exact hAvoidVerts _ _ _ hadj₁ t₁.1 h1_gt h1_lt heq
          · change _ = lineSeg (vPos (chosenPair e₂ he₂).1) (vPos (chosenPair e₂ he₂).2) t₂.1 at heq
            rw [ht2_1, lineSeg_one] at heq
            exact hAvoidVerts _ _ _ hadj₁ t₁.1 h1_gt h1_lt heq
        · exact hDisjointOpen _ _ _ _ hadj₁ hadj₂ hsym_ne
            t₁.1 t₂.1 h1_gt h1_lt h2_gt h2_lt heq
  }⟩

end Erdos1019
