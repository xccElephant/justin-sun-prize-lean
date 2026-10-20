import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Counterexample-preserving support compression for Erdős 883

This is one semantic step toward checking the finite certificates in Cecil
Jentges's 2026 ordered-weight argument. It is not a proof of the original problem.
The proof below was written independently; no external Lean proof was copied.
-/

namespace Erdos883Research

open scoped BigOperators

/-- The original simple coprime graph, also used by Formal Conjectures. -/
def coprimeGraph : SimpleGraph ℕ := SimpleGraph.fromRel Nat.Coprime

lemma coprimeGraph_adj {a b : ℕ} :
    coprimeGraph.Adj a b ↔ a ≠ b ∧ a.Coprime b := by
  simp [coprimeGraph, SimpleGraph.fromRel, Nat.coprime_comm]

/-- If every prime factor of `x` divides `y`, coprimality with `y` implies
coprimality with `x`. No positivity or squarefree assumption is needed. -/
theorem coprime_of_prime_support_subset {x y z : ℕ}
    (hs : ∀ p : ℕ, p.Prime → p ∣ x → p ∣ y)
    (hy : y.Coprime z) : x.Coprime z := by
  by_contra hx
  obtain ⟨p, hp, hpx, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp hx
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hs p hp hpx, hpz⟩) hy

/-- Replace `x` by `y` in a finite set. -/
def replace (A : Finset ℕ) (x y : ℕ) : Finset ℕ := insert y (A.erase x)

theorem replace_card {A : Finset ℕ} {x y : ℕ}
    (hx : x ∈ A) (hy : y ∉ A) : (replace A x y).card = A.card := by
  rw [replace, Finset.card_insert_of_notMem (by simp [hy]),
    Finset.card_erase_of_mem hx]
  exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨x, hx⟩)

/-- Map the replacement vertex back to the removed vertex. -/
def restore (x y z : ℕ) : ℕ := if z = y then x else z

lemma restore_mem {A : Finset ℕ} {x y z : ℕ}
    (hx : x ∈ A) (hz : z ∈ replace A x y) : restore x y z ∈ A := by
  rcases Finset.mem_insert.mp hz with rfl | hz
  · simp [restore, hx]
  · by_cases hzy : z = y
    · simp [restore, hzy, hx]
    · simpa [restore, hzy] using (Finset.mem_erase.mp hz).2

lemma restore_injOn {A : Finset ℕ} {x y : ℕ}
    (_hx : x ∈ A) (_hy : y ∉ A) :
    Set.InjOn (restore x y) (replace A x y : Set ℕ) := by
  intro a ha b hb hab
  by_cases hay : a = y <;> by_cases hby : b = y
  · exact hay.trans hby.symm
  · subst a
    have hbne : b ≠ x := (Finset.mem_erase.mp ((Finset.mem_insert.mp hb).resolve_left hby)).1
    simp [restore, hby] at hab
    exact (hbne hab.symm).elim
  · subst b
    have hane : a ≠ x := (Finset.mem_erase.mp ((Finset.mem_insert.mp ha).resolve_left hay)).1
    simp [restore, hay] at hab
    exact (hane hab).elim
  · simpa [restore, hay, hby] using hab

/-- Every graph in the compressed set embeds in the original set. Thus an
absent cycle cannot be created by this support-increasing replacement. -/
theorem replacement_graph_isContained {A : Finset ℕ} {x y : ℕ}
    (hx : x ∈ A) (hy : y ∉ A)
    (hs : ∀ p : ℕ, p.Prime → p ∣ x → p ∣ y) :
    (coprimeGraph.induce (replace A x y : Set ℕ)).IsContained
      (coprimeGraph.induce (A : Set ℕ)) := by
  let f : {z // z ∈ replace A x y} → {z // z ∈ A} :=
    fun z => ⟨restore x y z, restore_mem hx z.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact restore_injOn hx hy a.property b.property (congrArg Subtype.val hab)
  refine ⟨⟨{ toFun := f, map_rel' := ?_ }, hf⟩⟩
  intro a b hab
  have h : a.val ≠ b.val ∧ a.val.Coprime b.val := coprimeGraph_adj.mp hab
  apply coprimeGraph_adj.mpr
  refine ⟨?_, ?_⟩
  · intro heq
    exact h.1 (restore_injOn hx hy a.property b.property heq)
  · change (restore x y a.val).Coprime (restore x y b.val)
    by_cases hay : a.val = y <;> by_cases hby : b.val = y
    · exact (h.1 (hay.trans hby.symm)).elim
    · simp only [restore, hay, if_true, hby, if_false]
      exact coprime_of_prime_support_subset hs (by simpa only [hay] using h.2)
    · simp only [restore, hay, if_false, hby, if_true]
      exact (coprime_of_prime_support_subset hs (by simpa only [hby] using h.2.symm)).symm
    · simpa [restore, hay, hby] using h.2

theorem no_copy_after_replacement {V : Type*} (H : SimpleGraph V)
    {A : Finset ℕ} {x y : ℕ} (hx : x ∈ A) (hy : y ∉ A)
    (hs : ∀ p : ℕ, p.Prime → p ∣ x → p ∣ y)
    (hfree : ¬ H.IsContained (coprimeGraph.induce (A : Set ℕ))) :
    ¬ H.IsContained (coprimeGraph.induce (replace A x y : Set ℕ)) := by
  intro h
  exact hfree (h.trans (replacement_graph_isContained hx hy hs))

theorem replace_subset {A U : Finset ℕ} {x y : ℕ}
    (hA : A ⊆ U) (hy : y ∈ U) : replace A x y ⊆ U := by
  exact Finset.insert_subset hy (Finset.erase_subset _ _ |>.trans hA)

/-- The number of selected elements satisfying a predicate. -/
def selectedCount (P : ℕ → Prop) [DecidablePred P] (A : Finset ℕ) : ℕ :=
  (A.filter P).card

theorem selectedCount_replace (P : ℕ → Prop) [DecidablePred P]
    {A : Finset ℕ} {x y : ℕ} (hx : x ∈ A) (hy : y ∉ A)
    (hP : P x ↔ P y) : selectedCount P (replace A x y) = selectedCount P A := by
  by_cases hpx : P x
  · have hpy := hP.mp hpx
    have hxfilter : x ∈ A.filter P := Finset.mem_filter.mpr ⟨hx, hpx⟩
    have hyfilter : y ∉ (A.filter P).erase x := by
      intro h
      exact hy (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).1
    unfold selectedCount replace
    rw [Finset.filter_insert, if_pos hpy, Finset.filter_erase,
      Finset.card_insert_of_notMem hyfilter, Finset.card_erase_of_mem hxfilter]
    exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨x, hxfilter⟩)
  · have hpy : ¬ P y := fun h => hpx (hP.mpr h)
    simp [selectedCount, replace, Finset.filter_insert, Finset.filter_erase, hpx, hpy]

/-- A finite potential which strictly increases under support enlargement. -/
def supportWeight (A : Finset ℕ) : ℕ := ∑ v ∈ A, v.primeFactors.card

theorem supportWeight_replace {A : Finset ℕ} {x y : ℕ}
    (hx : x ∈ A) (hy : y ∉ A) :
    supportWeight (replace A x y) + x.primeFactors.card =
      supportWeight A + y.primeFactors.card := by
  have hsum := Finset.sum_erase_add A (fun v : ℕ => v.primeFactors.card) hx
  have hyerase : y ∉ A.erase x := by
    intro h
    exact hy (Finset.mem_erase.mp h).2
  unfold supportWeight replace
  rw [Finset.sum_insert hyerase]
  omega

/-- Every hypothetical counterexample has a same-size, same-parity-count
counterexample admitting no further support-enlarging replacement. This is the
first canonicalization required by the finite SAT encoding. -/
theorem exists_support_compressed_counterexample {V : Type*} (H : SimpleGraph V)
    (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hfree : ¬ H.IsContained (coprimeGraph.induce (A : Set ℕ))) :
    ∃ B : Finset ℕ,
      B ⊆ Finset.Icc 1 n ∧ B.card = A.card ∧
      selectedCount (fun v => v % 2 = 0) B = selectedCount (fun v => v % 2 = 0) A ∧
      (¬ H.IsContained (coprimeGraph.induce (B : Set ℕ))) ∧
      ∀ x ∈ B, ∀ y ∈ Finset.Icc 1 n,
        x % 2 = y % 2 → x.primeFactors ⊂ y.primeFactors → y ∈ B := by
  classical
  let candidates := (Finset.Icc 1 n).powerset.filter fun B =>
    B.card = A.card ∧
      selectedCount (fun v => v % 2 = 0) B = selectedCount (fun v => v % 2 = 0) A ∧
      ¬ H.IsContained (coprimeGraph.induce (B : Set ℕ))
  have hmem : A ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, rfl, rfl, hfree⟩
  obtain ⟨B, hB, hmax⟩ := candidates.exists_max_image supportWeight ⟨A, hmem⟩
  have hBdata := Finset.mem_filter.mp hB
  have hBsub : B ⊆ Finset.Icc 1 n := Finset.mem_powerset.mp hBdata.1
  refine ⟨B, hBsub, hBdata.2.1, hBdata.2.2.1, hBdata.2.2.2, ?_⟩
  intro x hx y hy hpar hs
  by_contra hynot
  have hx0 : x ≠ 0 := by have := (Finset.mem_Icc.mp (hBsub hx)).1; omega
  have hsupport : ∀ p : ℕ, p.Prime → p ∣ x → p ∣ y := by
    intro p hp hpx
    exact Nat.dvd_of_mem_primeFactors (hs.subset (hp.mem_primeFactors hpx hx0))
  have hrep : replace B x y ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (replace_subset hBsub hy), ?_, ?_, ?_⟩
    · rw [replace_card hx hynot, hBdata.2.1]
    · rw [selectedCount_replace _ hx hynot (by rw [hpar]), hBdata.2.2.1]
    · exact no_copy_after_replacement H hx hynot hsupport hBdata.2.2.2
  have hle := hmax _ hrep
  have heq := supportWeight_replace hx hynot
  have hlt := Finset.card_lt_card hs
  omega

/-- Secondary potential preferring smaller representatives of equal prime support. -/
def prefixWeight (n : ℕ) (A : Finset ℕ) : ℕ := ∑ v ∈ A, 2 ^ (n - v)

theorem prefixWeight_replace {A : Finset ℕ} {x y : ℕ}
    (n : ℕ) (hx : x ∈ A) (hy : y ∉ A) :
    prefixWeight n (replace A x y) + 2 ^ (n - x) =
      prefixWeight n A + 2 ^ (n - y) := by
  have hsum := Finset.sum_erase_add A (fun v : ℕ => 2 ^ (n - v)) hx
  have hyerase : y ∉ A.erase x := fun h => hy (Finset.mem_erase.mp h).2
  unfold prefixWeight replace
  rw [Finset.sum_insert hyerase]
  omega

/-- Counterexamples can be simultaneously support-compressed and prefix-ordered
within each prime-support class. The second maximization preserves the first
potential, so the two normalizations are not assumed to commute. -/
theorem exists_compressed_prefix_counterexample {V : Type*} (H : SimpleGraph V)
    (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hfree : ¬ H.IsContained (coprimeGraph.induce (A : Set ℕ))) :
    ∃ B : Finset ℕ,
      B ⊆ Finset.Icc 1 n ∧ B.card = A.card ∧
      selectedCount (fun v => v % 2 = 0) B = selectedCount (fun v => v % 2 = 0) A ∧
      (¬ H.IsContained (coprimeGraph.induce (B : Set ℕ))) ∧
      (∀ x ∈ B, ∀ y ∈ Finset.Icc 1 n,
        x % 2 = y % 2 → x.primeFactors ⊂ y.primeFactors → y ∈ B) ∧
      (∀ x ∈ B, ∀ y ∈ Finset.Icc 1 n,
        y < x → y.primeFactors = x.primeFactors → y ∈ B) := by
  classical
  let candidates := (Finset.Icc 1 n).powerset.filter fun B =>
    B.card = A.card ∧
      selectedCount (fun v => v % 2 = 0) B = selectedCount (fun v => v % 2 = 0) A ∧
      ¬ H.IsContained (coprimeGraph.induce (B : Set ℕ))
  have hmem : A ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, rfl, rfl, hfree⟩
  obtain ⟨C, hC, hmax⟩ := candidates.exists_max_image supportWeight ⟨A, hmem⟩
  let optimal := candidates.filter fun B => supportWeight B = supportWeight C
  have hCopt : C ∈ optimal := Finset.mem_filter.mpr ⟨hC, rfl⟩
  obtain ⟨B, hBopt, hprefix⟩ := optimal.exists_max_image (prefixWeight n) ⟨C, hCopt⟩
  have hB := (Finset.mem_filter.mp hBopt).1
  have hBweight := (Finset.mem_filter.mp hBopt).2
  have hBdata := Finset.mem_filter.mp hB
  have hBsub : B ⊆ Finset.Icc 1 n := Finset.mem_powerset.mp hBdata.1
  have hreplacement : ∀ x ∈ B, ∀ y ∈ Finset.Icc 1 n, y ∉ B →
      (x % 2 = y % 2) → x.primeFactors ⊆ y.primeFactors →
      replace B x y ∈ candidates := by
    intro x hx y hy hynot hpar hs
    have hx0 : x ≠ 0 := by have := (Finset.mem_Icc.mp (hBsub hx)).1; omega
    have hsupport : ∀ p : ℕ, p.Prime → p ∣ x → p ∣ y := by
      intro p hp hpx
      exact Nat.dvd_of_mem_primeFactors (hs (hp.mem_primeFactors hpx hx0))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (replace_subset hBsub hy), ?_, ?_, ?_⟩
    · rw [replace_card hx hynot, hBdata.2.1]
    · rw [selectedCount_replace _ hx hynot (by rw [hpar]), hBdata.2.2.1]
    · exact no_copy_after_replacement H hx hynot hsupport hBdata.2.2.2
  refine ⟨B, hBsub, hBdata.2.1, hBdata.2.2.1, hBdata.2.2.2, ?_, ?_⟩
  · intro x hx y hy hpar hs
    by_contra hynot
    have hle := hmax _ (hreplacement x hx y hy hynot hpar hs.subset)
    have heq := supportWeight_replace hx hynot
    have hlt := Finset.card_lt_card hs
    omega
  · intro x hx y hy hyx hs
    by_contra hynot
    have hx0 : x ≠ 0 := by have := (Finset.mem_Icc.mp (hBsub hx)).1; omega
    have hy0 : y ≠ 0 := by have := (Finset.mem_Icc.mp hy).1; omega
    have hpar : x % 2 = y % 2 := by
      have heven : 2 ∣ x ↔ 2 ∣ y := by
        have hmem := Finset.ext_iff.mp hs 2
        constructor
        · intro hd
          exact Nat.dvd_of_mem_primeFactors (hmem.mpr (Nat.prime_two.mem_primeFactors hd hx0))
        · intro hd
          exact Nat.dvd_of_mem_primeFactors (hmem.mp (Nat.prime_two.mem_primeFactors hd hy0))
      omega
    have hrep := hreplacement x hx y hy hynot hpar (Finset.Subset.trans
      (by rw [hs]) (Finset.Subset.refl _))
    have hweight : supportWeight (replace B x y) = supportWeight C := by
      have heq := supportWeight_replace hx hynot
      rw [hs] at heq
      omega
    have hrepopt : replace B x y ∈ optimal := Finset.mem_filter.mpr ⟨hrep, hweight⟩
    have hle := hprefix _ hrepopt
    have heq := prefixWeight_replace n hx hynot
    have hexp : n - x < n - y := by
      have := (Finset.mem_Icc.mp (hBsub hx)).2
      omega
    have hlt : 2 ^ (n - x) < 2 ^ (n - y) := Nat.pow_lt_pow_right (by decide) hexp
    omega

end Erdos883Research

#print axioms Erdos883Research.no_copy_after_replacement
#print axioms Erdos883Research.exists_support_compressed_counterexample
#print axioms Erdos883Research.exists_compressed_prefix_counterexample
