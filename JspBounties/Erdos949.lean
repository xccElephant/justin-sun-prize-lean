import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Real.Pointwise
import Mathlib.Order.Zorn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem 949 (JSP-000789)

*Reference:* [erdosproblems.com/949](https://www.erdosproblems.com/949)

Let $S \subseteq \mathbb{R}$ be a Sidon set. Must there be a set $A \subseteq \mathbb{R} \setminus S$
of cardinality continuum such that $A + A \subseteq \mathbb{R} \setminus S$?

We formalize the complete proof of `erdos_949.variants.sidon` from `FormalConjectures/ErdosProblems/949.lean`.
-/

open Cardinal Filter
open scoped Pointwise

namespace Cardinal
variable {α : Type*} {s t : Set α}

@[simp] lemma aleph0_le_mk_set : ℵ₀ ≤ #s ↔ s.Infinite := by
  rw [aleph0_le_mk_iff, Set.infinite_coe_iff]

@[simp]
lemma mk_sdiff_eq_left' (hs : s.Infinite) (hst : #↑(s ∩ t) < #s) : #↑(s \ t) = #s := by
  refine (mk_le_mk_of_subset Set.sdiff_subset).eq_of_not_lt
    fun h ↦ (add_lt_of_lt (by simpa) hst h).not_ge ?_
  grw [← mk_union_le .., Set.inter_union_sdiff]

@[simp]
lemma mk_sdiff_eq_left_of_finite' (hs : s.Infinite) (hst : (s ∩ t).Finite) : #↑(s \ t) = #s :=
  mk_sdiff_eq_left' hs <| (aleph0_le_mk_set.2 hs).trans_lt' <| by simpa

end Cardinal

/-- A subset `S` of an additive commutative monoid is a Sidon set if all pairwise sums of
elements in `S` are distinct up to reordering the pair. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Erdos949

/-- Let $S\subseteq \mathbb{R}$ be a Sidon set. Must there be a set $A\subseteq \mathbb{R}\setminus S$ of cardinality
continuum such that $A + A \subseteq \mathbb{R}\setminus S$?
Yes, proved unconditionally using Zorn's lemma (when `#S < 𝔠`) and a shifted difference construction (when `#S = 𝔠`). -/
theorem erdos_949.variants.sidon :
    ∀ S : Set ℝ, IsSidon S → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  simp only [Set.add_subset_iff]
  rintro S hS
  obtain hS𝔠 | hS𝔠 : #S < 𝔠 ∨ #S = 𝔠 := lt_or_eq_of_le <| by simpa [Cardinal.mk_real] using mk_set_le S
  · obtain ⟨A, ⟨hAS, hAAS⟩, hAmax⟩ := by
      refine zorn_subset {A ⊆ Sᶜ | ∀ x ∈ A, ∀ y ∈ A, x + y ∉ S} ?_
      simp only [Set.ofPred_and, Set.subset_inter_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, and_imp,
        and_assoc]
      refine fun C hCS hSC hC ↦ ⟨_, Set.iUnion₂_subset hCS, ?_, Set.subset_iUnion₂⟩
      simp only [Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
      rintro x A hA hx y B hB hy
      obtain ⟨D, hD, hAD, hBD⟩ := hC.directedOn _ hA _ hB
      exact hSC hD _ (hAD hx) _ (hBD hy)
    refine ⟨A, hAS, ?_, hAAS⟩
    replace hAmax : Sᶜ ∩ ((· / 2) '' S)ᶜ ⊆ A ∪ ⋃ a ∈ A, (· - a) '' S := by
      simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_image, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_eq_iff, mul_two,
      Set.mem_union, Set.mem_iUnion, sub_eq_iff_eq_add, exists_eq_right, exists_prop,
      or_iff_not_imp_left, and_imp]
      rintro x hxS hxxS hxA
      by_contra! hxAS
      refine hxA <| hAmax ?_ (Set.subset_insert ..) (Set.mem_insert ..)
      simpa [Set.insert_subset_iff, forall_and, add_comm _ x, *] using ⟨hxAS, hAAS⟩
    have hS𝔠' : #↑(Sᶜ ∩ ((· / 2) '' S)ᶜ) = 𝔠 := by
      rw [← Set.compl_union, mk_compl_of_infinite, mk_real]
      grw [mk_union_le, Cardinal.mk_real]
      refine add_lt_of_lt aleph0_le_continuum hS𝔠 ?_
      grw [mk_image_le]
      exact hS𝔠
    refine (mk_real ▸ mk_set_le _).eq_of_not_lt fun hA𝔠 ↦ lt_irrefl 𝔠 ?_
    calc
      𝔠 = #↑(Sᶜ ∩ ((· / 2) '' S)ᶜ) := by rw [hS𝔠']
      _ ≤ #↑(A ∪ ⋃ a ∈ A, (· - a) '' S) := mk_subtype_mono hAmax
      _ ≤ #A + #A * #S := by
        obtain rfl | hA := A.eq_empty_or_nonempty
        · simp
        have : Nonempty A := hA.coe_sort
        grw [mk_union_le, mk_biUnion_le, ciSup_le fun _ ↦ mk_image_le]
      _ < 𝔠 := add_lt_of_lt aleph0_le_continuum hA𝔠 <| mul_lt_of_lt aleph0_le_continuum hA𝔠 hS𝔠
  have hSinf : S.Infinite := by simpa using aleph0_le_continuum.trans_eq hS𝔠.symm
  obtain ⟨a, ha, ha₀⟩ : ∃ a ∈ S, a ≠ 0 := (hSinf.sdiff <| Set.finite_singleton 0).nonempty
  refine ⟨(· - a / 2) '' (S \ {a}) \ S, Set.sdiff_subset_compl .., ?_, ?_⟩
  · rw [mk_sdiff_eq_left_of_finite' ((hSinf.sdiff <| Set.finite_singleton _).image
      sub_left_injective.injOn)]
    · simp [Cardinal.mk_image_eq sub_left_injective, *]
    · refine Set.Subsingleton.finite ?_
      rintro _ ⟨⟨x, ⟨hx, -⟩, rfl⟩, hxa⟩ _ ⟨⟨y, ⟨hy, -⟩, rfl⟩, hya⟩
      obtain rfl : x = y := by
        simpa [ha₀, eq_comm (b := x - _)] using hS _ hya _ hxa _ hx _ hy (by ring)
      rfl
  · rintro _ ⟨⟨x, ⟨hx, hxa⟩, rfl⟩, -⟩ _ ⟨⟨y, ⟨hy, hya⟩, rfl⟩, -⟩ hxy
    have := hS _ hx _ ha _ hy _ hxy (by ring)
    simp_all

#print axioms erdos_949.variants.sidon

end Erdos949
