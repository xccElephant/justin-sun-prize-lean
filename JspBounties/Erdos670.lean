/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 670 (JSP-000544)

*References:*
- [erdosproblems.com/670](https://www.erdosproblems.com/670)
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.

We prove the two positive results in `FormalConjectures/ErdosProblems/670.lean`:
- `erdos_670.variants.choose_two`: For any $d \ge 0$ and any finite set $A \subseteq \mathbb{R}^d$
  of $n \neq 2$ points whose pairwise distances differ by at least $1$, the diameter of $A$ is at
  least $\binom{n}{2}$.
- `erdos_670.variants.dim_one` (Erdős, 1997): In dimension $d = 1$, for every $\varepsilon > 0$ and
  all sufficiently large $n$, any $n$-point set $A \subseteq \mathbb{R}^1$ whose pairwise distances
  differ by at least $1$ has diameter at least $(1 - \varepsilon) n^2$.
-/

open Filter

namespace Erdos670

/-- A finite set $A$ of points has *separated distances* if all its pairwise distances differ
by at least $1$: for any two different unordered pairs $\{a, b\} \neq \{c, e\}$ of distinct
points of $A$, we have $\lvert d(a, b) - d(c, e)\rvert \geq 1$. -/
def HasSeparatedDistances {X : Type*} [MetricSpace X] (A : Finset X) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A, a ≠ b → c ≠ e → s(a, b) ≠ s(c, e) →
    1 ≤ |dist a b - dist c e|

/-! ### General $1$-separated real-valued families on finite sets -/

/-- If $m > 0$ real values on a finite set $P$ are bounded below by $c$, bounded above by $M$,
and pairwise differ by at least $1$, then $c + m - 1 \le M$. -/
private lemma sep_max_ge {α : Type*} [DecidableEq α] :
    ∀ (m : ℕ) (P : Finset α) (f : α → ℝ) (c M : ℝ),
      P.card = m →
      0 < m →
      (∀ x ∈ P, c ≤ f x) →
      (∀ x ∈ P, f x ≤ M) →
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ |f x - f y|) →
      c + (m : ℝ) - 1 ≤ M
  | 0, _, _, _, _, _, hm, _, _, _ => absurd hm (lt_irrefl 0)
  | m + 1, P, f, c, M, hcard, _, hlow, hhigh, hsep => by
    have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxP, hxmax⟩ := Finset.exists_max_image P f hne
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hcx := hlow x hxP
      have hxM := hhigh x hxP
      push_cast
      linarith
    · let P' := P.erase x
      have hcard' : P'.card = m := by
        rw [Finset.card_erase_of_mem hxP, hcard]
        omega
      have hhigh' : ∀ y ∈ P', f y ≤ M - 1 := by
        intro y hy
        have hyP : y ∈ P := Finset.mem_of_mem_erase hy
        have hyx : y ≠ x := Finset.ne_of_mem_erase hy
        have hle : f y ≤ f x := hxmax y hyP
        have h1 : 1 ≤ |f y - f x| := hsep y hyP x hxP hyx
        rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h1
        have hxM : f x ≤ M := hhigh x hxP
        linarith
      have ih := sep_max_ge m P' f c (M - 1) hcard' hm
        (fun y hy => hlow y (Finset.mem_of_mem_erase hy))
        hhigh'
        (fun y hy z hz => hsep y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz))
      push_cast
      linarith

/-- If $m$ nonnegative real values on a finite set $P$ pairwise differ by at least $1$,
their sum is at least $m(m-1)/2$. -/
private lemma sep_sum_ge {α : Type*} [DecidableEq α] :
    ∀ (m : ℕ) (P : Finset α) (f : α → ℝ),
      P.card = m →
      (∀ x ∈ P, 0 ≤ f x) →
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ |f x - f y|) →
      (m : ℝ) * ((m : ℝ) - 1) / 2 ≤ ∑ x ∈ P, f x
  | 0, P, f, hcard, _, _ => by
    rw [Finset.card_eq_zero.mp hcard]
    simp
  | m + 1, P, f, hcard, hnonneg, hsep => by
    have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxP, hxmax⟩ := Finset.exists_max_image P f hne
    have hfx : 0 + ((m + 1 : ℕ) : ℝ) - 1 ≤ f x :=
      sep_max_ge (m + 1) P f 0 (f x) hcard (Nat.succ_pos m) hnonneg hxmax hsep
    have hcard' : (P.erase x).card = m := by
      rw [Finset.card_erase_of_mem hxP, hcard]
      omega
    have hsum' := sep_sum_ge m (P.erase x) f hcard'
      (fun y hy => hnonneg y (Finset.mem_of_mem_erase hy))
      (fun y hy z hz => hsep y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz))
    rw [← Finset.sum_erase_add P f hxP]
    push_cast at hfx ⊢
    linarith

/-! ### Indexing pairs of elements by step size -/

/-- The finite set of pairs $\langle r, i \rangle$ with $0 \le r < k$ and $0 \le i < n - (r + 1)$,
representing ordered index pairs $(i, i + r + 1)$ of step size $r + 1 \in \{1, \dots, k\}$. -/
private def stepPairs (n k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range k).sigma (fun r => Finset.range (n - (r + 1)))

private lemma mem_stepPairs {n k : ℕ} {p : Σ _ : ℕ, ℕ} :
    p ∈ stepPairs n k ↔ p.1 < k ∧ p.2 < n - (p.1 + 1) := by
  simp [stepPairs]

private lemma card_stepPairs (n k : ℕ) (hkn : k ≤ n) :
    ((stepPairs n k).card : ℝ) = (k : ℝ) * (n : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  rw [stepPairs, Finset.card_sigma]
  simp only [Finset.card_range]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_add, ih (Nat.le_of_succ_le hkn), Nat.cast_sub hkn]
    push_cast
    ring

private lemma choose_two_cast_real (n : ℕ) :
    (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, ih]
    push_cast
    ring

private lemma card_stepPairs_self (n : ℕ) :
    ((stepPairs n n).card : ℝ) = (n.choose 2 : ℝ) := by
  rw [card_stepPairs n n le_rfl, choose_two_cast_real]
  ring

/-- Any injection $g : \{0, \dots, n - 1\} \to A$ sends distinct pairs in `stepPairs n k`
to $1$-separated distances when `HasSeparatedDistances A` holds. -/
private lemma stepPairs_sep {X : Type*} [MetricSpace X] {A : Finset X}
    (hA : HasSeparatedDistances A) {n k : ℕ} {g : ℕ → X}
    (hg_mem : ∀ i, g i ∈ A)
    (hg_inj : ∀ i < n, ∀ j < n, g i = g j → i = j)
    {p₁ p₂ : Σ _ : ℕ, ℕ} (hp₁ : p₁ ∈ stepPairs n k) (hp₂ : p₂ ∈ stepPairs n k)
    (hne : p₁ ≠ p₂) :
    1 ≤ |dist (g p₁.2) (g (p₁.2 + p₁.1 + 1)) - dist (g p₂.2) (g (p₂.2 + p₂.1 + 1))| := by
  rw [mem_stepPairs] at hp₁ hp₂
  have hi₁ : p₁.2 < n := by omega
  have hj₁ : p₁.2 + p₁.1 + 1 < n := by omega
  have hi₂ : p₂.2 < n := by omega
  have hj₂ : p₂.2 + p₂.1 + 1 < n := by omega
  apply hA (g p₁.2) (hg_mem _) (g (p₁.2 + p₁.1 + 1)) (hg_mem _)
    (g p₂.2) (hg_mem _) (g (p₂.2 + p₂.1 + 1)) (hg_mem _)
  · intro h
    have := hg_inj _ hi₁ _ hj₁ h
    omega
  · intro h
    have := hg_inj _ hi₂ _ hj₂ h
    omega
  · intro hsym
    rw [Sym2.eq_iff] at hsym
    rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := hg_inj _ hi₁ _ hi₂ h1
      have e2 := hg_inj _ hj₁ _ hj₂ h2
      rcases p₁ with ⟨r₁, i₁⟩
      rcases p₂ with ⟨r₂, i₂⟩
      dsimp at e1 e2
      have er : r₁ = r₂ := by omega
      subst e1 er
      exact hne rfl
    · have e1 := hg_inj _ hi₁ _ hj₂ h1
      have e2 := hg_inj _ hj₁ _ hi₂ h2
      omega

/-! ### Proof of `erdos_670.variants.choose_two` -/

/-- In a set $A$ of at least $3$ points with separated distances, every distance between
distinct points of $A$ is at least $1$. -/
private lemma one_le_dist_of_card_ge_three {X : Type*} [MetricSpace X] [DecidableEq X]
    {A : Finset X} (hA : HasSeparatedDistances A) (hcard : 3 ≤ A.card)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    1 ≤ dist x y := by
  have hcard1 : 2 ≤ (A.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  have hy' : y ∈ A.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hcard2 : 0 < ((A.erase x).erase y).card := by
    rw [Finset.card_erase_of_mem hy']
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard2
  have hz1 : z ∈ A.erase x := Finset.mem_of_mem_erase hz
  have hzy : z ≠ y := Finset.ne_of_mem_erase hz
  have hzA : z ∈ A := Finset.mem_of_mem_erase hz1
  have hzx : z ≠ x := Finset.ne_of_mem_erase hz1
  have hsym : s(x, z) ≠ s(y, z) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hxy h1
    · exact hzx h1.symm
  have hsep : 1 ≤ |dist x z - dist y z| :=
    hA x hx z hzA y hy z hzA hzx.symm hzy.symm hsym
  exact hsep.trans (abs_dist_sub_le x y z)

/--
The trivial lower bound: if $A\subseteq \mathbb{R}^d$ is a set of $n \neq 2$ points such that all
pairwise distances differ by at least $1$, then the diameter of $A$ is at least $\binom{n}{2}$.
-/
theorem erdos_670.variants.choose_two (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (hA : HasSeparatedDistances A) (hn : A.card ≠ 2) :
    (A.card.choose 2 : ℝ) ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  set n := A.card with hn_def
  by_cases hn2 : n ≤ 1
  · have hchoose : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose, Nat.cast_zero]
    exact Metric.diam_nonneg
  · have hn3 : 3 ≤ n := by omega
    have hn_pos : 0 < n := by omega
    let e : Fin n ≃ A := (A.equivFinOfCardEq hn_def.symm).symm
    let g : ℕ → EuclideanSpace ℝ (Fin d) :=
      fun i => if h : i < n then (e ⟨i, h⟩ : EuclideanSpace ℝ (Fin d)) else (e ⟨0, hn_pos⟩ : _)
    have hg_mem : ∀ i, g i ∈ A := by
      intro i
      dsimp [g]
      split_ifs with h
      · exact (e ⟨i, h⟩).2
      · exact (e ⟨0, hn_pos⟩).2
    have hg_inj : ∀ i < n, ∀ j < n, g i = g j → i = j := by
      intro i hi j hj hij
      dsimp [g] at hij
      rw [dif_pos hi, dif_pos hj] at hij
      have heq : (⟨i, hi⟩ : Fin n) = ⟨j, hj⟩ := e.injective (Subtype.ext hij)
      exact Fin.mk.inj_iff.mp heq
    let P := stepPairs n n
    let f : (Σ _ : ℕ, ℕ) → ℝ := fun p => dist (g p.2) (g (p.2 + p.1 + 1))
    have hP_pos : 0 < P.card := by
      have hcard_nat : P.card = n.choose 2 := Nat.cast_injective (R := ℝ) (card_stepPairs_self n)
      rw [hcard_nat]
      exact Nat.choose_pos (by omega)
    have hlow : ∀ p ∈ P, 1 ≤ f p := by
      intro p hp
      rw [mem_stepPairs] at hp
      have hi : p.2 < n := by omega
      have hj : p.2 + p.1 + 1 < n := by omega
      have hne : g p.2 ≠ g (p.2 + p.1 + 1) := by
        intro h
        have := hg_inj _ hi _ hj h
        omega
      exact one_le_dist_of_card_ge_three hA hn3 (hg_mem _) (hg_mem _) hne
    have hhigh : ∀ p ∈ P, f p ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
      intro p _
      exact Metric.dist_le_diam_of_mem A.finite_toSet.isBounded (hg_mem _) (hg_mem _)
    have hsep : ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ → 1 ≤ |f p₁ - f p₂| :=
      fun p₁ hp₁ p₂ hp₂ hne => stepPairs_sep hA hg_mem hg_inj hp₁ hp₂ hne
    have hbound := sep_max_ge P.card P f 1 (Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))))
      rfl hP_pos hlow hhigh hsep
    rw [card_stepPairs_self n] at hbound
    linarith

/-! ### Proof of `erdos_670.variants.dim_one` -/

private lemma euclidean_fin1_dist (x y : EuclideanSpace ℝ (Fin 1)) :
    dist x y = |x 0 - y 0| := by
  rw [PiLp.dist_eq_of_L2, Fin.sum_univ_one, Real.sqrt_sq dist_nonneg, Real.dist_eq]

private lemma euclidean_fin1_eval_injective :
    Function.Injective (fun x : EuclideanSpace ℝ (Fin 1) => x 0) := by
  intro x y h
  ext i
  fin_cases i
  exact h

/-- Telescoping identity for sums of differences of step size $m \le n$. -/
private lemma sum_range_sub_shift_eq (a : ℕ → ℝ) {n m : ℕ} (hm : m ≤ n) :
    ∑ i ∈ Finset.range (n - m), (a (i + m) - a i) =
      ∑ i ∈ Finset.range m, (a (n - m + i) - a i) := by
  have h1 := Finset.sum_range_add a m (n - m)
  have h2 := Finset.sum_range_add a (n - m) m
  rw [Nat.add_sub_of_le hm] at h1
  rw [Nat.sub_add_cancel hm] at h2
  have h3 : ∑ i ∈ Finset.range (n - m), a (m + i) = ∑ i ∈ Finset.range (n - m), a (i + m) :=
    Finset.sum_congr rfl (fun i _ => by rw [add_comm])
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← h3]
  linarith

private lemma sum_range_add_one_mul (k : ℕ) (D : ℝ) :
    ∑ r ∈ Finset.range k, ((r : ℝ) + 1) * D = (k : ℝ) * ((k : ℝ) + 1) / 2 * D := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/--
Erdős [Er97f] proved the claim when $d = 1$: if $A\subseteq \mathbb{R}$ is a set of $n$ points
such that all pairwise distances differ by at least $1$, then the diameter of $A$ is at least
$(1+o(1))n^2$.
-/
theorem erdos_670.variants.dim_one :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset (EuclideanSpace ℝ (Fin 1)), A.card = n → HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 1))) := by
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_ge (2 / ε)
  let k : ℕ := m + 1
  have hk_pos : 1 ≤ k := by omega
  have hk_eps : 2 ≤ ε * ((k : ℝ) + 1) := by
    have h1 : 2 ≤ ε * (m : ℝ) := (div_le_iff₀' hε).mp hm
    have h2 : (m : ℝ) ≤ (k : ℝ) + 1 := by
      dsimp [k]
      push_cast
      linarith
    nlinarith
  rw [ Filter.eventually_atTop ]
  refine ⟨k ^ 2 + k + 1, fun n hn A hcard hA => ?_⟩
  have hkn : k ≤ n := by nlinarith
  have hn_pos : 0 < n := by omega
  -- Project A to ℝ and sort in increasing order
  let S : Finset ℝ := A.image (fun x => x 0)
  have hScard : S.card = n := by
    rw [Finset.card_image_of_injective A euclidean_fin1_eval_injective, hcard]
  let emb : Fin n ↪o ℝ := S.orderEmbOfFin hScard
  let ψ : ℝ → EuclideanSpace ℝ (Fin 1) := fun u => WithLp.toLp 2 (fun _ => u)
  have hψ_mem : ∀ u ∈ S, ψ u ∈ A := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨x, hxA, rfl⟩
    have hx : ψ (x 0) = x := by
      ext i
      fin_cases i
      rfl
    rwa [hx]
  let a : ℕ → ℝ := fun i => if h : i < n then emb ⟨i, h⟩ else emb ⟨0, hn_pos⟩
  let g : ℕ → EuclideanSpace ℝ (Fin 1) := fun i => ψ (a i)
  have ha_mem : ∀ i, a i ∈ S := by
    intro i
    dsimp [a]
    split_ifs with h
    · exact S.orderEmbOfFin_mem hScard ⟨i, h⟩
    · exact S.orderEmbOfFin_mem hScard ⟨0, hn_pos⟩
  have hg_mem : ∀ i, g i ∈ A := fun i => hψ_mem (a i) (ha_mem i)
  have ha_lt : ∀ {i j : ℕ} (hi : i < n) (hj : j < n), i < j → a i < a j := by
    intro i j hi hj hij
    dsimp [a]
    rw [dif_pos hi, dif_pos hj]
    exact emb.strictMono hij
  have hg_inj : ∀ i < n, ∀ j < n, g i = g j → i = j := by
    intro i hi j hj hij
    have haij : a i = a j := congr_arg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) hij
    dsimp [a] at haij
    rw [dif_pos hi, dif_pos hj] at haij
    exact Fin.mk.inj_iff.mp (emb.injective haij)
  have hg_dist : ∀ i j, dist (g i) (g j) = |a i - a j| := by
    intro i j
    exact euclidean_fin1_dist (g i) (g j)
  set D := Metric.diam (A : Set (EuclideanSpace ℝ (Fin 1)))
  have ha_sub_le_D : ∀ i j, a j - a i ≤ D := by
    intro i j
    have hle : a j - a i ≤ |a j - a i| := le_abs_self _
    have hdist : |a j - a i| = dist (g j) (g i) := (hg_dist j i).symm
    have hdiam : dist (g j) (g i) ≤ D :=
      Metric.dist_le_diam_of_mem A.finite_toSet.isBounded (hg_mem j) (hg_mem i)
    linarith
  let P := stepPairs n k
  let f : (Σ _ : ℕ, ℕ) → ℝ := fun p => dist (g p.2) (g (p.2 + p.1 + 1))
  have hf_eq : ∀ p ∈ P, f p = a (p.2 + p.1 + 1) - a p.2 := by
    intro p hp
    rw [mem_stepPairs] at hp
    have hi : p.2 < n := by omega
    have hj : p.2 + p.1 + 1 < n := by omega
    have hlt : a p.2 < a (p.2 + p.1 + 1) := ha_lt hi hj (by omega)
    dsimp [f]
    rw [hg_dist, abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)]
  have hnonneg : ∀ p ∈ P, 0 ≤ f p := fun p _ => dist_nonneg
  have hsep : ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ → 1 ≤ |f p₁ - f p₂| :=
    fun p₁ hp₁ p₂ hp₂ hne => stepPairs_sep hA hg_mem hg_inj hp₁ hp₂ hne
  -- Lower bound on ∑ p ∈ P, f p
  have hsum_low : (P.card : ℝ) * ((P.card : ℝ) - 1) / 2 ≤ ∑ p ∈ P, f p :=
    sep_sum_ge P.card P f rfl hnonneg hsep
  -- Upper bound on ∑ p ∈ P, f p via telescoping
  have hsum_eq : ∑ p ∈ P, f p =
      ∑ r ∈ Finset.range k, ∑ i ∈ Finset.range (n - (r + 1)), (a (i + (r + 1)) - a i) := by
    rw [ Finset.sum_congr rfl hf_eq ]
    dsimp [P, stepPairs]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
    rw [add_assoc]
  have hsum_high : ∑ p ∈ P, f p ≤ (k : ℝ) * ((k : ℝ) + 1) / 2 * D := by
    rw [hsum_eq, ← sum_range_add_one_mul k D]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrk : r + 1 ≤ n := by
      have := Finset.mem_range.mp hr
      omega
    rw [sum_range_sub_shift_eq a hrk]
    calc
      ∑ i ∈ Finset.range (r + 1), (a (n - (r + 1) + i) - a i) ≤
          ∑ _i ∈ Finset.range (r + 1), D :=
        Finset.sum_le_sum fun i _ => ha_sub_le_D i (n - (r + 1) + i)
      _ = ((r : ℝ) + 1) * D := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  -- Combine lower and upper bounds
  set N : ℝ := (k : ℝ) * (n : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
  have hN : (P.card : ℝ) = N := card_stepPairs n k hkn
  rw [hN] at hsum_low
  have hND : N * (N - 1) ≤ (k : ℝ) * ((k : ℝ) + 1) * D := by linarith
  have hid : N * (N - 1) - (k : ℝ) * ((k : ℝ) + 1) * ((1 - ε) * (n : ℝ) ^ 2) =
      (k : ℝ) * (ε * ((k : ℝ) + 1) - 2) * (n : ℝ) ^ 2 +
      (k : ℝ) * (n : ℝ) * ((n : ℝ) - ((k : ℝ) ^ 2 + (k : ℝ) + 1)) +
      (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) ^ 2 + (k : ℝ) + 2) / 4 := by
    dsimp [N]
    ring
  have hterm1 : 0 ≤ (k : ℝ) * (ε * ((k : ℝ) + 1) - 2) * (n : ℝ) ^ 2 := by
    have : 0 ≤ ε * ((k : ℝ) + 1) - 2 := by linarith
    positivity
  have hterm2 : 0 ≤ (k : ℝ) * (n : ℝ) * ((n : ℝ) - ((k : ℝ) ^ 2 + (k : ℝ) + 1)) := by
    have hn_real : (k : ℝ) ^ 2 + (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have : 0 ≤ (n : ℝ) - ((k : ℝ) ^ 2 + (k : ℝ) + 1) := by linarith
    positivity
  have hterm3 : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) ^ 2 + (k : ℝ) + 2) / 4 := by positivity
  have hN_low : (k : ℝ) * ((k : ℝ) + 1) * ((1 - ε) * (n : ℝ) ^ 2) ≤ N * (N - 1) := by linarith
  have hk_mul_pos : 0 < (k : ℝ) * ((k : ℝ) + 1) := by positivity
  exact le_of_mul_le_mul_left (hN_low.trans hND) hk_mul_pos

/--
The version of the problem where the $o(1)$ term must be uniform in the dimension $d$ has a
negative answer, conditional on Ho's construction (`erdos_670.variants.ho`, Ho [Ho26]).
-/
theorem erdos_670.variants.uniform_in_dim_of_ho
    (hHo : ∀ ε > (0 : ℝ), ∃ᶠ n : ℕ in atTop,
      ∃ A : Finset (EuclideanSpace ℝ (Fin (n ^ 2 - n))), A.card = n ∧
        HasSeparatedDistances A ∧
        Metric.diam (A : Set (EuclideanSpace ℝ (Fin (n ^ 2 - n)))) ≤
          (1 - 1 / Real.pi ^ 2 + ε) * (n : ℝ) ^ 2) :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n → HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  intro hUnif
  have hpi : 0 < 1 / Real.pi ^ 2 := by positivity
  let ε : ℝ := (1 / Real.pi ^ 2) / 3
  have hε : 0 < ε := by positivity
  have hFreq := hHo ε hε
  have hEv1 := hUnif ε hε
  have hEv2 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
  obtain ⟨n, ⟨A, hcard, hA, hdiam_le⟩, hdiam_ge, hn1⟩ :=
    (hFreq.and_eventually (hEv1.and hEv2)).exists
  have hlow := hdiam_ge (n ^ 2 - n) A hcard hA
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    positivity
  have hdiff : (1 - 1 / Real.pi ^ 2 + ε) * (n : ℝ) ^ 2 < (1 - ε) * (n : ℝ) ^ 2 := by
    have : 1 - 1 / Real.pi ^ 2 + ε < 1 - ε := by
      dsimp [ε]
      linarith
    exact mul_lt_mul_of_pos_right this hn_pos
  linarith

#print axioms erdos_670.variants.choose_two
#print axioms erdos_670.variants.dim_one
#print axioms erdos_670.variants.uniform_in_dim_of_ho

end Erdos670
