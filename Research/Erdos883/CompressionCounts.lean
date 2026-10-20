import Research.Erdos883.Compression

/-!
# Count-preserving simultaneous compression for Erdős 883

Support enlargement with fixed parity cannot remove a selected odd multiple of
three without adding another. We retain this count lower bound among the finite
candidates, maximize support weight, then maximize prefix weight among support
maximizers. Neither canonical property is assumed in the candidate predicate.

This is a normalization lemma for hypothetical counterexamples, not a proof of
the original Erdős 883 conjecture or its finite certificates.
-/

namespace Erdos883Research

/-- Replacing a vertex in `A` by a vertex outside `A` cannot decrease a
predicate count when `P x → P y`. Unlike `selectedCount_replace`, only a forward
implication is required, so support enlargement may increase the count. -/
theorem selectedCount_le_replace (P : ℕ → Prop) [DecidablePred P]
    {A : Finset ℕ} {x y : ℕ} (hx : x ∈ A) (hy : y ∉ A)
    (hP : P x → P y) : selectedCount P A ≤ selectedCount P (replace A x y) := by
  by_cases hpx : P x
  · exact le_of_eq (selectedCount_replace P hx hy
      ⟨hP, fun _ => hpx⟩).symm
  · apply Finset.card_le_card
    intro z hz
    obtain ⟨hzA, hzP⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨by intro hzx; subst z; exact hpx hzP, hzA⟩), hzP⟩

/-- Every hypothetical counterexample admits simultaneous support and prefix
normalization, preserving cardinality and the number of even vertices, while
weakly increasing the number of selected odd multiples of three. Only interval
membership and absence of the graph `H` are assumed of the input set. -/
theorem exists_compressed_prefix_counterexample_counts {V : Type*} (H : SimpleGraph V)
    (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hfree : ¬ H.IsContained (coprimeGraph.induce (A : Set ℕ))) :
    ∃ B : Finset ℕ,
      B ⊆ Finset.Icc 1 n ∧ B.card = A.card ∧
      selectedCount (fun v => v % 2 = 0) B = selectedCount (fun v => v % 2 = 0) A ∧
      selectedCount (fun v => v % 2 = 1 ∧ 3 ∣ v) A ≤
        selectedCount (fun v => v % 2 = 1 ∧ 3 ∣ v) B ∧
      (¬ H.IsContained (coprimeGraph.induce (B : Set ℕ))) ∧
      (∀ x ∈ B, ∀ y ∈ Finset.Icc 1 n,
        x % 2 = y % 2 → x.primeFactors ⊂ y.primeFactors → y ∈ B) ∧
      (∀ x ∈ B, ∀ y ∈ Finset.Icc 1 n,
        y < x → y.primeFactors = x.primeFactors → y ∈ B) := by
  classical
  let candidates := (Finset.Icc 1 n).powerset.filter fun B =>
    B.card = A.card ∧
      selectedCount (fun v => v % 2 = 0) B = selectedCount (fun v => v % 2 = 0) A ∧
      selectedCount (fun v => v % 2 = 1 ∧ 3 ∣ v) A ≤
        selectedCount (fun v => v % 2 = 1 ∧ 3 ∣ v) B ∧
      ¬ H.IsContained (coprimeGraph.induce (B : Set ℕ))
  have hmem : A ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, rfl, rfl, le_rfl, hfree⟩
  -- The input itself witnesses nonemptiness; no normalization is assumed.
  obtain ⟨C, hC, hmax⟩ := candidates.exists_max_image supportWeight ⟨A, hmem⟩
  -- Maximize the prefix potential only among support-weight maximizers.
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
    refine ⟨Finset.mem_powerset.mpr (replace_subset hBsub hy), ?_, ?_, ?_, ?_⟩
    · rw [replace_card hx hynot, hBdata.2.1]
    · rw [selectedCount_replace _ hx hynot (by rw [hpar]), hBdata.2.2.1]
    · exact hBdata.2.2.2.1.trans (selectedCount_le_replace _ hx hynot (by
        intro hpx
        exact ⟨by omega, hsupport 3 Nat.prime_three hpx.2⟩))
    · exact no_copy_after_replacement H hx hynot hsupport hBdata.2.2.2.2
  refine ⟨B, hBsub, hBdata.2.1, hBdata.2.2.1, hBdata.2.2.2.1, hBdata.2.2.2.2, ?_, ?_⟩
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
