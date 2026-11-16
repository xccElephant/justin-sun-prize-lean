import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Product Grid Counting (`Fin N₀ → Fin m`) & Elementary Rational Power Bounds

Every probabilistic step of the `G(n, q)` + deletion + container argument is formalized here as
exact integer/rational cardinality counting on the finite function space `Ω := Fin N₀ → Fin m`
(with threshold `A < m` representing edge probability `q = A / m`), completely free of measure
theory, real logarithms, or Stirling's formula.
-/

namespace Erdos638.GridCounting

open scoped Classical BigOperators

section GridIdentities

variable {N₀ m : ℕ}

/-- The edge set `rawEdges A ω ⊆ Finset.univ` selected by a configuration `ω : Fin N₀ → Fin m`
at threshold `A`: index `i` is included iff `(ω i).val < A`. -/
def rawEdges (A : ℕ) (ω : Fin N₀ → Fin m) : Finset (Fin N₀) :=
  Finset.univ.filter (fun i => (ω i).val < A)

lemma mem_rawEdges {A : ℕ} {ω : Fin N₀ → Fin m} {i : Fin N₀} :
    i ∈ rawEdges A ω ↔ (ω i).val < A := by
  simp [rawEdges]

/-- Exact product-card identity on `Fin N₀ → Fin m`:
given disjoint sets `P, Z : Finset (Fin N₀)` ("present" and "absent" coordinates) and `A ≤ m`,
the number of `ω : Fin N₀ → Fin m` satisfying `P ⊆ rawEdges A ω` and `Disjoint Z (rawEdges A ω)` is:
`A ^ P.card * (m - A) ^ Z.card * m ^ (N₀ - P.card - Z.card)`
(and hence in `ℚ`, dividing by `m ^ N₀`, equals `(A / m) ^ P.card * (1 - A / m) ^ Z.card`!). -/
lemma card_grid_cylinder {A : ℕ} (hAm : A ≤ m) (hm : 0 < m)
    (P Z : Finset (Fin N₀)) (hdisj : Disjoint P Z) :
    (((Finset.univ : Finset (Fin N₀ → Fin m)).filter
      (fun ω => P ⊆ rawEdges A ω ∧ Disjoint Z (rawEdges A ω))).card : ℚ) =
      (m : ℚ) ^ N₀ * ((A : ℚ) / (m : ℚ)) ^ P.card * (1 - (A : ℚ) / (m : ℚ)) ^ Z.card := by
  -- Express the indicator of the filter as a product over `i : Fin N₀`, then swap `∑_{ω}` and `∏_{i}`
  -- via `Fintype.prod_sum` (`∏ i, ∑ x : Fin m, f i x = ∑ ω : Fin N₀ → Fin m, ∏ i, f i (ω i)`)!!
  let f : Fin N₀ → Fin m → ℚ := fun i x =>
    if i ∈ P then (if x.val < A then 1 else 0)
    else if i ∈ Z then (if A ≤ x.val then 1 else 0)
    else 1
  have hprod_ind : ∀ ω : Fin N₀ → Fin m,
      (∏ i : Fin N₀, f i (ω i)) =
        if P ⊆ rawEdges A ω ∧ Disjoint Z (rawEdges A ω) then 1 else 0 := by
    intro ω
    by_cases hok : P ⊆ rawEdges A ω ∧ Disjoint Z (rawEdges A ω)
    · rw [if_pos hok]
      apply Finset.prod_eq_one
      intro i _
      dsimp only [f]
      by_cases hiP : i ∈ P
      · have hlt : (ω i).val < A := mem_rawEdges.mp (hok.1 hiP)
        simp [hiP, hlt]
      · by_cases hiZ : i ∈ Z
        · have hnot : i ∉ rawEdges A ω := Finset.disjoint_left.mp hok.2 hiZ
          have hge : A ≤ (ω i).val := le_of_not_gt (mem_rawEdges.not.mp hnot)
          simp [hiP, hiZ, hge]
        · simp [hiP, hiZ]
    · rw [if_neg hok]
      -- Some coordinate `i₀` fails its condition, making `f i₀ (ω i₀) = 0`!
      have hex_zero : ∃ i₀ ∈ (Finset.univ : Finset (Fin N₀)), f i₀ (ω i₀) = 0 := by
        by_contra! hall_ne
        apply hok
        refine ⟨?_, ?_⟩
        · intro i hiP
          have hfi := hall_ne i (Finset.mem_univ i)
          dsimp only [f] at hfi
          rw [if_pos hiP] at hfi
          by_contra hnot
          have hlt_not : ¬((ω i).val < A) := mem_rawEdges.not.mp hnot
          simp [hlt_not] at hfi
        · rw [Finset.disjoint_left]
          intro i hiZ hiRaw
          have hi_notP : i ∉ P := Finset.disjoint_right.mp hdisj hiZ
          have hfi := hall_ne i (Finset.mem_univ i)
          dsimp only [f] at hfi
          rw [if_neg hi_notP, if_pos hiZ] at hfi
          have hlt : (ω i).val < A := mem_rawEdges.mp hiRaw
          have hnot_ge : ¬(A ≤ (ω i).val) := not_le_of_gt hlt
          simp [hnot_ge] at hfi
      obtain ⟨i₀, hi₀, hz⟩ := hex_zero
      exact Finset.prod_eq_zero hi₀ hz
  have hcard_as_sum :
      (((Finset.univ : Finset (Fin N₀ → Fin m)).filter
        (fun ω => P ⊆ rawEdges A ω ∧ Disjoint Z (rawEdges A ω))).card : ℚ) =
        ∑ ω : Fin N₀ → Fin m, ∏ i : Fin N₀, f i (ω i) := by
    simp only [hprod_ind, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard_as_sum, ← Fintype.prod_sum]
  -- Evaluate `∑ x : Fin m, f i x` for each `i : Fin N₀`:
  have hsum_P : (∑ x : Fin m, (if x.val < A then (1 : ℚ) else 0)) = (A : ℚ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    -- `{x : Fin m | x.val < A}` has card `A` because `A ≤ m`!
    have heq : (Finset.univ : Finset (Fin m)).filter (fun x => x.val < A) =
        (Finset.range A).attach.image (fun k => ⟨k.1, lt_of_lt_of_le (Finset.mem_range.mp k.2) hAm⟩) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach,
        true_and, Subtype.exists]
      constructor
      · intro hx; exact ⟨x.val, Finset.mem_range.mpr hx, Fin.ext rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact Finset.mem_range.mp hk
    rw [heq, Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have hv : a.1 = b.1 := congrArg Fin.val hab
      exact Subtype.ext hv
  have hsum_Z : (∑ x : Fin m, (if A ≤ x.val then (1 : ℚ) else 0)) = (m : ℚ) - (A : ℚ) := by
    have htot : (∑ x : Fin m, ((if x.val < A then (1 : ℚ) else 0) + (if A ≤ x.val then 1 else 0))) =
        (m : ℚ) := by
      have h1 : ∀ x : Fin m, (if x.val < A then (1 : ℚ) else 0) + (if A ≤ x.val then 1 else 0) = 1 := by
        intro x
        by_cases h : x.val < A
        · simp [h, not_le_of_gt h]
        · simp [h, le_of_not_gt h]
      simp [h1]
    rw [Finset.sum_add_distrib, hsum_P] at htot
    linarith
  have hfactor : ∀ i : Fin N₀,
      (∑ x : Fin m, f i x) =
        if i ∈ P then (A : ℚ) else if i ∈ Z then (m : ℚ) - (A : ℚ) else (m : ℚ) := by
    intro i
    dsimp only [f]
    by_cases hiP : i ∈ P
    · simp [hiP, hsum_P]
    · by_cases hiZ : i ∈ Z
      · simp [hiP, hiZ, hsum_Z]
      · simp [hiP, hiZ]
  have hm_q : (m : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hfactor_norm : ∀ i : Fin N₀,
      (∑ x : Fin m, f i x) =
        (m : ℚ) * (if i ∈ P then (A : ℚ) / (m : ℚ) else 1) *
          (if i ∈ Z then 1 - (A : ℚ) / (m : ℚ) else 1) := by
    intro i
    rw [hfactor i]
    by_cases hiP : i ∈ P
    · have hi_notZ : i ∉ Z := Finset.disjoint_left.mp hdisj hiP
      simp [hiP, hi_notZ]; field_simp [hm_q]
    · by_cases hiZ : i ∈ Z
      · simp [hiP, hiZ]; field_simp [hm_q]
      · simp [hiP, hiZ]
  simp only [hfactor_norm]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hp1 : (∏ _i : Fin N₀, (m : ℚ)) = (m : ℚ) ^ N₀ := by simp
  have hp2 : (∏ i : Fin N₀, (if i ∈ P then (A : ℚ) / (m : ℚ) else 1)) =
      ((A : ℚ) / (m : ℚ)) ^ P.card := by
    rw [← Finset.prod_filter]
    have hfP : (Finset.univ : Finset (Fin N₀)).filter (· ∈ P) = P := by ext x; simp
    rw [hfP, Finset.prod_const]
  have hp3 : (∏ i : Fin N₀, (if i ∈ Z then 1 - (A : ℚ) / (m : ℚ) else 1)) =
      (1 - (A : ℚ) / (m : ℚ)) ^ Z.card := by
    rw [← Finset.prod_filter]
    have hfZ : (Finset.univ : Finset (Fin N₀)).filter (· ∈ Z) = Z := by ext x; simp
    rw [hfZ, Finset.prod_const]
  rw [hp1, hp2, hp3]

end GridIdentities

/-! ## Elementary Rational Bernstein & Exponential Decay Inequalities -/

section RationalBounds

/-- **Bernstein Sum Bound over Small Subsets**:
For `0 ≤ q` and `1 ≤ lam`,
`∑_{F ⊆ Fin N₀ : F.card ≤ L} q ^ F.card ≤ lam ^ L * (1 + q / lam) ^ N₀`!
Proved in 10 lines directly from the binomial theorem `(q / lam + 1) ^ N₀`! -/
lemma sum_pow_card_le_bernstein (N₀ L : ℕ) {q lam : ℚ} (hq : 0 ≤ q) (hlam : 1 ≤ lam) :
    (∑ F ∈ (Finset.univ : Finset (Fin N₀)).powerset.filter (fun F => F.card ≤ L),
      q ^ F.card) ≤ lam ^ L * (1 + q / lam) ^ N₀ := by
  have hlam_pos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  -- Multiply each term `F` (`F.card ≤ L`) by `1 ≤ lam ^ (L - F.card)`!
  have hterm : ∀ F ∈ (Finset.univ : Finset (Fin N₀)).powerset.filter (fun F => F.card ≤ L),
      q ^ F.card ≤ lam ^ L * (q / lam) ^ F.card := by
    intro F hF
    have hFc : F.card ≤ L := (Finset.mem_filter.mp hF).2
    have hpow_ge1 : (1 : ℚ) ≤ lam ^ (L - F.card) := one_le_pow₀ hlam
    have hsplit : lam ^ L = lam ^ (L - F.card) * lam ^ F.card := by
      rw [← pow_add, Nat.sub_add_cancel hFc]
    have hcancel : lam ^ F.card * (q / lam) ^ F.card = q ^ F.card := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ (ne_of_gt hlam_pos))]
    calc q ^ F.card = 1 * q ^ F.card := (one_mul _).symm
      _ ≤ lam ^ (L - F.card) * q ^ F.card :=
          mul_le_mul_of_nonneg_right hpow_ge1 (pow_nonneg hq _)
      _ = lam ^ (L - F.card) * (lam ^ F.card * (q / lam) ^ F.card) := by rw [hcancel]
      _ = lam ^ L * (q / lam) ^ F.card := by rw [← mul_assoc, ← hsplit]
  calc (∑ F ∈ (Finset.univ : Finset (Fin N₀)).powerset.filter (fun F => F.card ≤ L), q ^ F.card)
      ≤ ∑ F ∈ (Finset.univ : Finset (Fin N₀)).powerset.filter (fun F => F.card ≤ L),
          lam ^ L * (q / lam) ^ F.card := Finset.sum_le_sum hterm
    _ ≤ ∑ F ∈ (Finset.univ : Finset (Fin N₀)).powerset,
          lam ^ L * (q / lam) ^ F.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun F _ _ => by positivity)
    _ = lam ^ L * ∑ F ∈ (Finset.univ : Finset (Fin N₀)).powerset, (q / lam) ^ F.card :=
        (Finset.mul_sum _ _ _).symm
    _ = lam ^ L * (1 + q / lam) ^ N₀ := by
        congr 1
        -- Group `powerset` by `F.card ∈ range (N₀ + 1)` and apply `add_pow`!
        rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (N₀ + 1)) (g := Finset.card)
          (fun F hF => Finset.mem_range.mpr (Nat.lt_succ_of_le (by
            have := Finset.card_le_univ F; simpa using this)))]
        have hbinom := add_pow (q / lam) 1 N₀
        rw [add_comm 1 (q / lam), hbinom]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have hfib : ((Finset.univ : Finset (Fin N₀)).powerset.filter (fun F => F.card = k)) =
            (Finset.univ : Finset (Fin N₀)).powersetCard k := by
          ext F; simp [Finset.mem_powersetCard]
        rw [hfib]
        have hconst : ∀ F ∈ (Finset.univ : Finset (Fin N₀)).powersetCard k,
            (q / lam) ^ F.card = (q / lam) ^ k :=
          fun F hF => by rw [(Finset.mem_powersetCard.mp hF).2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow, mul_one, mul_comm]

/-- **Bernstein Lower-Tail Bound on `U : Finset (Fin N₀)`**:
For `0 ≤ q ≤ 1` and `B_del : ℕ`, the sum over all `E_bad ⊆ U` with `E_bad.card ≤ B_del` of
`q ^ E_bad.card * (1 - q) ^ (U \ E_bad).card` is at most `2 ^ B_del * (1 - q / 2) ^ U.card`! -/
lemma sum_tail_subsets_le {N₀ : ℕ} (U : Finset (Fin N₀)) (B_del : ℕ) {q : ℚ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ E ∈ U.powerset.filter (fun E => E.card ≤ B_del),
      q ^ E.card * (1 - q) ^ (U \ E).card) ≤
      (2 : ℚ) ^ B_del * (1 - q / 2) ^ U.card := by
  have h1q : 0 ≤ 1 - q := by linarith
  have hterm : ∀ E ∈ U.powerset.filter (fun E => E.card ≤ B_del),
      q ^ E.card * (1 - q) ^ (U \ E).card ≤
        (2 : ℚ) ^ B_del * ((q / 2) ^ E.card * (1 - q) ^ (U.card - E.card)) := by
    intro E hE
    rcases Finset.mem_filter.mp hE with ⟨hEU_pow, hEc⟩
    have hEU : E ⊆ U := Finset.mem_powerset.mp hEU_pow
    have hsdiff : (U \ E).card = U.card - E.card := by
      have h := Finset.card_sdiff_add_card_eq_card hEU; omega
    rw [hsdiff]
    have hpow2 : (1 : ℚ) ≤ (2 : ℚ) ^ (B_del - E.card) := one_le_pow₀ (by norm_num)
    have hsplit : (2 : ℚ) ^ B_del = (2 : ℚ) ^ (B_del - E.card) * (2 : ℚ) ^ E.card := by
      rw [← pow_add, Nat.sub_add_cancel hEc]
    have hcancel : (2 : ℚ) ^ E.card * (q / 2) ^ E.card = q ^ E.card := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num))]
    calc q ^ E.card * (1 - q) ^ (U.card - E.card)
        = 1 * (q ^ E.card * (1 - q) ^ (U.card - E.card)) := (one_mul _).symm
      _ ≤ (2 : ℚ) ^ (B_del - E.card) * (q ^ E.card * (1 - q) ^ (U.card - E.card)) :=
          mul_le_mul_of_nonneg_right hpow2 (by positivity)
      _ = (2 : ℚ) ^ (B_del - E.card) * ((2 : ℚ) ^ E.card * (q / 2) ^ E.card * (1 - q) ^ (U.card - E.card)) := by
          rw [hcancel]
      _ = (2 : ℚ) ^ B_del * ((q / 2) ^ E.card * (1 - q) ^ (U.card - E.card)) := by
          rw [hsplit]; ring
  calc (∑ E ∈ U.powerset.filter (fun E => E.card ≤ B_del), q ^ E.card * (1 - q) ^ (U \ E).card)
      ≤ ∑ E ∈ U.powerset.filter (fun E => E.card ≤ B_del),
          (2 : ℚ) ^ B_del * ((q / 2) ^ E.card * (1 - q) ^ (U.card - E.card)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ E ∈ U.powerset,
          (2 : ℚ) ^ B_del * ((q / 2) ^ E.card * (1 - q) ^ (U.card - E.card)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ = (2 : ℚ) ^ B_del * ∑ E ∈ U.powerset, (q / 2) ^ E.card * (1 - q) ^ (U.card - E.card) :=
        (Finset.mul_sum _ _ _).symm
    _ = (2 : ℚ) ^ B_del * (1 - q / 2) ^ U.card := by
        congr 1
        rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (U.card + 1)) (g := Finset.card)
          (fun E hE => Finset.mem_range.mpr (Nat.lt_succ_of_le
            (Finset.card_le_card (Finset.mem_powerset.mp hE))))]
        have hbinom := add_pow (q / 2) (1 - q) U.card
        have hbase : q / 2 + (1 - q) = 1 - q / 2 := by ring
        rw [hbase] at hbinom
        rw [hbinom]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have hfib : (U.powerset.filter (fun E => E.card = k)) = U.powersetCard k := by
          ext E; simp [Finset.mem_powersetCard]
        rw [hfib]
        have hconst : ∀ E ∈ U.powersetCard k,
            (q / 2) ^ E.card * (1 - q) ^ (U.card - E.card) =
              (q / 2) ^ k * (1 - q) ^ (U.card - k) :=
          fun E hE => by rw [(Finset.mem_powersetCard.mp hE).2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
            nsmul_eq_mul, mul_comm]

/-- Elementary 3-line rational convexity lemma:
For all `k : ℕ` and `0 ≤ z` with `2 * k * z ≤ 1`, `(1 + z) ^ k ≤ 1 + 2 * k * z`! -/
lemma one_add_pow_le_linear (k : ℕ) {z : ℚ} (hz : 0 ≤ z) (hkz : 2 * (k : ℚ) * z ≤ 1) :
    (1 + z) ^ k ≤ 1 + 2 * (k : ℚ) * z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkz' : 2 * (k : ℚ) * z ≤ 1 := by push_cast at hkz; linarith
    have hstep := ih hkz'
    rw [pow_succ]
    have hmul : (1 + z) ^ k * (1 + z) ≤ (1 + 2 * (k : ℚ) * z) * (1 + z) :=
      mul_le_mul_of_nonneg_right hstep (by linarith)
    have hexpand : (1 + 2 * (k : ℚ) * z) * (1 + z) =
        1 + (2 * (k : ℚ) + 1) * z + (2 * (k : ℚ) * z) * z := by ring
    have hsq : (2 * (k : ℚ) * z) * z ≤ 1 * z := mul_le_mul_of_nonneg_right hkz' hz
    push_cast
    linarith

/-- Elementary rational Bernoulli lower bound: `1 + k * y ≤ (1 + y) ^ k` for `0 ≤ y`. -/
lemma one_add_mul_le_pow (k : ℕ) {y : ℚ} (hy : 0 ≤ y) :
    1 + (k : ℚ) * y ≤ (1 + y) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hmul : (1 + (k : ℚ) * y) * (1 + y) ≤ (1 + y) ^ k * (1 + y) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hexp : (1 + (k : ℚ) * y) * (1 + y) = 1 + ((k : ℚ) + 1) * y + (k : ℚ) * y ^ 2 := by ring
    have hnn : 0 ≤ (k : ℚ) * y ^ 2 := by positivity
    push_cast
    linarith

/-- Block decay bound: if `0 < y < 1` and `b : ℕ` satisfies `2 ≤ b * y`, then `(1 - y) ^ b ≤ 1 / 2`! -/
lemma one_sub_pow_block_le_half {b : ℕ} {y : ℚ} (hy0 : 0 < y) (hy1 : y < 1)
    (hby : 2 ≤ (b : ℚ) * y) :
    (1 - y) ^ b ≤ 1 / 2 := by
  have h1y_pos : 0 < 1 + y := by linarith
  have hsub_le_inv : 1 - y ≤ 1 / (1 + y) := by
    rw [le_div_iff₀ h1y_pos]
    have : (1 - y) * (1 + y) = 1 - y ^ 2 := by ring
    have : 0 ≤ y ^ 2 := sq_nonneg y
    linarith
  have hpow : (1 - y) ^ b ≤ (1 / (1 + y)) ^ b :=
    pow_le_pow_left₀ (by linarith) hsub_le_inv b
  have hbern : (3 : ℚ) ≤ (1 + y) ^ b := by
    have h := one_add_mul_le_pow b (le_of_lt hy0)
    linarith
  calc (1 - y) ^ b
      ≤ (1 / (1 + y)) ^ b := hpow
    _ = 1 / (1 + y) ^ b := one_div_pow _ _
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hbern
    _ ≤ 1 / 2 := by norm_num

end RationalBounds

end Erdos638.GridCounting
