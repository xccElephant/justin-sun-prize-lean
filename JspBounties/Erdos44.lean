/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Erdős Problem 44 (`FormalConjectures/ErdosProblems/44.lean`): Extending and Constructing Sidon Sets

*References:*
- [erdosproblems.com/44](https://www.erdosproblems.com/44)
- [Si38] Singer, James, *A theorem in finite projective geometry and some applications to number
  theory*. Trans. Amer. Math. Soc. 43 (1938), 377–385.
- [ErTu41] Erdős, P. and Turán, P., *On a problem of Sidon in additive number theory, and on some
  related problems*. J. London Math. Soc. 16 (1941), 212–215.
- [arXiv:2103.15850](https://arxiv.org/abs/2103.15850)

This file formalizes complete, zero-`sorry` proofs for `FormalConjectures/ErdosProblems/44.lean`:
1. **Upper bound `maxSidonSubsetCard_icc_bound`**:
   Every Sidon subset of $\{1, \ldots, N\}$ has cardinality at most $2 \sqrt{N}$.
2. **Verified Sidon Example (`example_sidon_set`)**:
   $\{1, 2, 4, 8, 13\} \subseteq \{1, \ldots, 13\}$ is a Sidon set.
3. **Unconditional Proof of the Greedy Sidon Construction (`greedy_sidon_construction`)**:
   For every $N \ge 1$, there exists a Sidon set $A \subseteq \{1, \ldots, N\}$ with $N \le |A|^3$,
   proved via a single cubic covering map $F : A \times A \times A \to \mathbb{N}$ defined by
   $F(a, b, c) = (a + c)/2$ if $a = b \ne c$ and $b + c - a$ otherwise.
4. **Erdős–Turán's Prime Parabola Construction (`erdos_turan_parabola_sidon`) and Unconditional
   $\sqrt{N}/3$ Lower Bound (`sidon_set_lower_bound_sqrt_div_three`)**:
   For every odd prime $p$, constructs the parabola Sidon set
   $A_p = \{2px + (x^2 \bmod p) + 1 \mid x \in \mathrm{Fin}\,p\} \subseteq \{1, \ldots, 2p^2\}$
   of cardinality $p$, and combines it with Bertrand's Postulate (`Nat.exists_prime_lt_and_le_two_mul`)
   to prove unconditionally that every $\{1, \ldots, N\}$ ($N \ge 1$) contains a Sidon set of size
   $\ge \sqrt{N}/3$.
5. **Deduction of `sidon_set_lower_bound` and `erdos_44.variants.empty_start` from Singer's
   Construction (`sidon_set_lower_bound_of_singer`, `erdos_44_empty_start_of_singer`)**:
   Proves that Singer's projective-plane construction [Si38] together with Bertrand's Postulate
   yields `sidon_set_lower_bound` ($\ge \sqrt{N}/2$), and together with asymptotic prime density
   yields `erdos_44.variants.empty_start` ($\ge (1 - \varepsilon)\sqrt{M}$).
-/

open Function Set Finset Filter

/-- A Sidon set is a set such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Set

theorem IsSidon.insert {α : Type*} [AddCommMonoid α] {A : Set α} {m : α}
    [IsRightCancelAdd α] [IsLeftCancelAdd α] (hA : IsSidon A) :
    IsSidon (A ∪ {m}) ↔ (m ∈ A ∨ ∀ᵉ (a ∈ A) (b ∈ A), m + m ≠ a + b ∧ ∀ c ∈ A, m + a ≠ b + c) := by
  by_cases h_mem : m ∈ A
  · exact ⟨fun _ ↦ .inl h_mem, fun _ ↦ by rwa [union_singleton, insert_eq_of_mem h_mem]⟩
  refine ⟨fun h ↦ .inr fun a ha b hb ↦ ⟨fun hc ↦ ?_, fun c hc h_contr ↦ ?_⟩, fun hm ↦ ?_⟩
  · exact h m (by simp) a (by simp [ha]) m (by simp) b (by simp [hb]) hc
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · exact h m (by simp) b (by simp [hb]) a (by simp [ha]) c (by simp [hc]) h_contr
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · intro i₁ hi₁
    rcases hi₁ with (hi₁ | hi₁)
    · intro j₁ hj₁
      rcases hj₁ with (hj₁ | hj₁)
      · intro i₂ hi₂
        rcases hi₂ with (hi₂ | hi₂)
        · intro j₂ hj₂
          rcases hj₂ with (hj₂ | hj₂)
          · exact fun h ↦ hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
          · simp_all
            exact fun h ↦ by cases (hm j₁ hj₁ i₁ hi₁).2 i₂ hi₂ (add_comm j₁ m ▸ h.symm)
        · simp_all
          exact fun a ha h ↦ by cases (hm i₁ hi₁ j₁ hj₁).2 a ha (add_comm i₁ m ▸ h)
      · simp_all
        refine ⟨fun b hb h ↦ .inr <| by simp_all [add_comm], fun b hb ↦ ⟨fun h ↦ ?_, ?_⟩⟩
        · cases (hm i₁ hi₁ b hb).1 h.symm
        · exact fun c hc h ↦ by cases ((hm c hc i₁ hi₁).2 b hb) h.symm
    · simp_all
      exact fun _ _ _ _ _ ↦ by simp_all [add_comm]

end Set

namespace Finset

instance {α : Type*} [AddCommMonoid α] (A : Finset α) [DecidableEq α] :
    Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- The maximum size of a Sidon set in the supplied `Finset`. -/
def maxSidonSubsetCard {α : Type*} [AddCommMonoid α] (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

end Finset

namespace Erdos44

/-!
## Part 1: Upper Bound and Textbook Examples (`44.lean`)
-/

/-- The maximum size of a Sidon set in `{1, ..., N}` is less than or equal to `2 * √N`. -/
theorem maxSidonSubsetCard_icc_bound (N : ℕ) (hN : 1 ≤ N) :
    maxSidonSubsetCard (Icc 1 N) ≤ 2 * Real.sqrt N := by
  have key : maxSidonSubsetCard (Finset.Icc 1 N) ^ 2 ≤ 4 * N := by
    obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup
      ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ))
      ⟨∅, by simp [IsSidon]⟩ Finset.card
    rw [maxSidonSubsetCard, hBeq]
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB
    obtain ⟨hsub, hsid⟩ := hB
    have hcard : B.offDiag.card ≤ (Finset.Icc (-(N : ℤ)) N).card := by
      refine Finset.card_le_card_of_injOn (fun p ↦ (p.1 : ℤ) - p.2) ?_ ?_
      · rintro ⟨a, b⟩ hab
        rw [Finset.mem_coe, Finset.mem_offDiag] at hab
        have ha' := Finset.mem_Icc.mp (hsub hab.1)
        have hb' := Finset.mem_Icc.mp (hsub hab.2.1)
        simp only [Finset.mem_coe, Finset.mem_Icc]
        omega
      · rintro ⟨a, b⟩ ha ⟨c, d⟩ hc hac
        rw [Finset.mem_coe, Finset.mem_offDiag] at ha hc
        simp only at hac
        have hsum : a + d = c + b := by omega
        rcases hsid a ha.1 c hc.1 d hc.2.1 b ha.2.1 hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1, h2]
        · exact absurd h1 ha.2.2
    have hIcc : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    rw [Finset.offDiag_card, hIcc] at hcard
    have hle : B.card ≤ N := by simpa using Finset.card_le_card hsub
    rcases Nat.eq_zero_or_pos B.card with h0 | hpos
    · simp [h0]
    have hkk : B.card ≤ B.card * B.card := Nat.le_mul_of_pos_left _ hpos
    calc B.card ^ 2 = B.card * B.card := sq B.card
      _ ≤ 2 * N + 1 + B.card := by omega
      _ ≤ 4 * N := by omega
  have h1 : ((maxSidonSubsetCard (Finset.Icc 1 N) : ℝ)) ^ 2 ≤ 4 * N := by exact_mod_cast key
  have h2 : (2 : ℝ) * Real.sqrt N = Real.sqrt (4 * N) := by
    rw [show (4 : ℝ) * N = 2 ^ 2 * N by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [h2, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (maxSidonSubsetCard (Finset.Icc 1 N) : ℝ))]
  exact Real.sqrt_le_sqrt h1

/-- The set `{1, 2, 4, 8, 13}` is a Sidon set in `{1, ..., 13}`. -/
theorem example_sidon_set : IsSidon ({1, 2, 4, 8, 13} : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hi₂ hj₂
  rcases hi₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hi₂ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj₂ with rfl | rfl | rfl | rfl | rfl <;>
  simp_all

/-!
## Part 2: Unconditional Proof of `greedy_sidon_construction` (`44.lean`)
-/

/-- **Greedy Sidon Lower Bound (`greedy_sidon_construction`)**:
For every $N \ge 1$, there exists a Sidon set $A \subseteq \{1, \ldots, N\}$ such that
$N \le |A|^3$. -/
theorem greedy_sidon_construction (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3 := by
  classical
  -- Pick a Sidon subset `A ⊆ Icc 1 N` of maximum cardinality.
  let S := (Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)
  have h1_mem : ({1} : Finset ℕ) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff,
      Finset.mem_Icc]
    refine ⟨⟨le_rfl, hN⟩, ?_⟩
    intro a ha b hb c hc d hd _
    simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb hc hd
    subst ha hb hc hd
    left; exact ⟨rfl, rfl⟩
  obtain ⟨A, hA_mem, hA_sup⟩ := Finset.exists_mem_eq_sup S ⟨{1}, h1_mem⟩ Finset.card
  simp only [S, Finset.mem_filter, Finset.mem_powerset] at hA_mem
  obtain ⟨hA_sub, hA_sidon⟩ := hA_mem
  refine ⟨A, hA_sub, hA_sidon, ?_⟩
  -- Define the cubic covering map `F : ℕ × ℕ × ℕ → ℕ`.
  let F : ℕ × ℕ × ℕ → ℕ := fun p =>
    if p.1 = p.2.1 ∧ p.1 ≠ p.2.2 then (p.1 + p.2.2) / 2 else p.2.1 + p.2.2 - p.1
  have hcov : Finset.Icc 1 N ⊆ (A ×ˢ (A ×ˢ A)).image F := by
    intro x hx
    by_cases hxA : x ∈ A
    · refine Finset.mem_image.mpr ⟨(x, x, x), by simp [hxA], ?_⟩
      dsimp [F]
      rw [if_neg (by tauto)]
      omega
    · -- Since `A` has maximum cardinality in `S`, `insert x A` is not Sidon.
      have hnot_sidon : ¬ IsSidon ((A : Set ℕ) ∪ {x}) := by
        intro hsid'
        have hins_mem : A ∪ {x} ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.union_subset hA_sub (Finset.singleton_subset_iff.mpr hx), ?_⟩
          simpa [Finset.coe_union] using hsid'
        have hle : (A ∪ {x}).card ≤ A.card := by
          rw [← hA_sup]
          exact Finset.le_sup (f := Finset.card) hins_mem
        have hcard_eq : (A ∪ {x}).card = A.card + 1 := by
          rw [Finset.union_comm, ← Finset.insert_eq, Finset.card_insert_of_notMem hxA]
        omega
      have hiff := (Set.IsSidon.insert hA_sidon (m := x)).mp
      -- Unpack `¬ (x ∈ A ∨ ∀ a ∈ A, ∀ b ∈ A, x + x ≠ a + b ∧ ∀ c ∈ A, x + a ≠ b + c)`.
      have hobst : ∃ a ∈ A, ∃ b ∈ A, x + x = a + b ∨ ∃ c ∈ A, x + a = b + c := by
        by_contra! hall
        apply hnot_sidon
        refine (Set.IsSidon.insert hA_sidon).mpr (Or.inr fun a ha b hb => ?_)
        exact ⟨(hall a ha b hb).1, (hall a ha b hb).2⟩
      obtain ⟨a, ha, b, hb, h2x | ⟨c, hc, hxabc⟩⟩ := hobst
      · by_cases hab : a = b
        · subst hab
          have : x = a := by omega
          exact (hxA (this ▸ ha)).elim
        · refine Finset.mem_image.mpr ⟨(a, a, b), by simp [ha, hb], ?_⟩
          dsimp [F]
          rw [if_pos ⟨rfl, hab⟩]
          omega
      · by_cases hab : a = b
        · subst hab
          have : x = c := by omega
          exact (hxA (this ▸ hc)).elim
        · refine Finset.mem_image.mpr ⟨(a, b, c), by simp [ha, hb, hc], ?_⟩
          dsimp [F]
          rw [if_neg (by tauto)]
          omega
  calc
    N = (Finset.Icc 1 N).card := by simp
    _ ≤ ((A ×ˢ (A ×ˢ A)).image F).card := Finset.card_le_card hcov
    _ ≤ (A ×ˢ (A ×ˢ A)).card := Finset.card_image_le
    _ = A.card ^ 3 := by
      rw [Finset.card_product, Finset.card_product]
      ring

/-!
## Part 3: Erdős–Turán's Prime Parabola Sidon Construction (`[ErTu41]`)
-/

/-- The Erdős–Turán parabola map $g_p(x) = 2px + (x^2 \bmod p) + 1$ for $x \in \mathrm{Fin}\,p$. -/
def parabolaMap (p : ℕ) (x : Fin p) : ℕ :=
  2 * p * x.1 + (x.1 ^ 2) % p + 1

/-- The Erdős–Turán parabola Sidon set $A_p \subseteq \{1, \ldots, 2p^2\}$ of size $p$. -/
def parabolaSidonSet (p : ℕ) : Finset ℕ :=
  Finset.univ.image (parabolaMap p)

lemma parabolaMap_mem_Icc {p : ℕ} (hp : p.Prime) (x : Fin p) :
    parabolaMap p x ∈ Finset.Icc 1 (2 * p ^ 2) := by
  have hp_pos : 0 < p := hp.pos
  have hmod : (x.1 ^ 2) % p < p := Nat.mod_lt _ hp_pos
  have hx : x.1 ≤ p - 1 := Nat.le_sub_one_of_lt x.2
  rw [Finset.mem_Icc]
  refine ⟨by unfold parabolaMap; omega, ?_⟩
  unfold parabolaMap
  calc
    2 * p * x.1 + (x.1 ^ 2) % p + 1 ≤ 2 * p * (p - 1) + (p - 1) + 1 := by
      have : 2 * p * x.1 ≤ 2 * p * (p - 1) := Nat.mul_le_mul_left (2 * p) hx
      omega
    _ = 2 * p * (p - 1) + p := by omega
    _ ≤ 2 * p * (p - 1) + 2 * p := by omega
    _ = 2 * p * (p - 1 + 1) := by ring
    _ = 2 * p ^ 2 := by
      rw [Nat.sub_add_cancel hp.one_lt.le]
      ring

lemma eq_of_two_mul_add_eq {p a b r₁ r₂ : ℕ} (hr₁ : r₁ < 2 * p) (hr₂ : r₂ < 2 * p)
    (h : 2 * p * a + r₁ = 2 * p * b + r₂) : a = b ∧ r₁ = r₂ := by
  have hdiv : (2 * p * a + r₁) / (2 * p) = (2 * p * b + r₂) / (2 * p) := by rw [h]
  have hp : 0 < 2 * p := by omega
  rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hr₁, add_zero,
      Nat.mul_add_div hp, Nat.div_eq_of_lt hr₂, add_zero] at hdiv
  refine ⟨hdiv, ?_⟩
  rw [hdiv] at h
  omega

lemma parabolaMap_injective {p : ℕ} (hp : p.Prime) :
    Function.Injective (parabolaMap p) := by
  intro x y hxy
  unfold parabolaMap at hxy
  have hp_pos : 0 < p := hp.pos
  have hmodx : (x.1 ^ 2) % p < p := Nat.mod_lt _ hp_pos
  have hmody : (y.1 ^ 2) % p < p := Nat.mod_lt _ hp_pos
  have heq : 2 * p * x.1 + (x.1 ^ 2) % p = 2 * p * y.1 + (y.1 ^ 2) % p := by omega
  exact Fin.ext (eq_of_two_mul_add_eq (by omega) (by omega) heq).1

/-- Ring identity used in the Erdős–Turán parabola Sidon proof:
$2(x_1 - y_1)(x_1 - y_2) = (x_1^2 + x_2^2 - (y_1^2 + y_2^2)) + (x_1 + x_2 - (y_1 + y_2))(x_1 - x_2 - y_1 - y_2)$. -/
lemma parabola_quad_identity {R : Type*} [CommRing R] (x₁ x₂ y₁ y₂ : R)
    (hsum : x₁ + x₂ = y₁ + y₂) (hsq : x₁ ^ 2 + x₂ ^ 2 = y₁ ^ 2 + y₂ ^ 2) :
    2 * (x₁ - y₁) * (x₁ - y₂) = 0 := by
  calc
    2 * (x₁ - y₁) * (x₁ - y₂) =
        (x₁ ^ 2 + x₂ ^ 2 - (y₁ ^ 2 + y₂ ^ 2)) +
          (x₁ + x₂ - (y₁ + y₂)) * (x₁ - x₂ - y₁ - y₂) := by ring
    _ = 0 := by rw [hsum, hsq]; ring

/-- **Erdős–Turán's Prime Parabola Theorem (`erdos_turan_parabola_sidon`)**:
For every odd prime $p$, `parabolaSidonSet p` is a Sidon subset of $\{1, \ldots, 2p^2\}$ of
exact cardinality $p$. -/
theorem erdos_turan_parabola_sidon {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    parabolaSidonSet p ⊆ Finset.Icc 1 (2 * p ^ 2) ∧
      IsSidon (parabolaSidonSet p : Set ℕ) ∧
      (parabolaSidonSet p).card = p := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact parabolaMap_mem_Icc hp x
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    obtain ⟨x₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hi₁)
    obtain ⟨y₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hj₁)
    obtain ⟨x₂, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hi₂)
    obtain ⟨y₂, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hj₂)
    have hp_pos : 0 < p := hp.pos
    have hmx₁ : (x₁.1 ^ 2) % p < p := Nat.mod_lt _ hp_pos
    have hmx₂ : (x₂.1 ^ 2) % p < p := Nat.mod_lt _ hp_pos
    have hmy₁ : (y₁.1 ^ 2) % p < p := Nat.mod_lt _ hp_pos
    have hmy₂ : (y₂.1 ^ 2) % p < p := Nat.mod_lt _ hp_pos
    have hsum_unfold :
        2 * p * (x₁.1 + x₂.1) + ((x₁.1 ^ 2) % p + (x₂.1 ^ 2) % p) =
          2 * p * (y₁.1 + y₂.1) + ((y₁.1 ^ 2) % p + (y₂.1 ^ 2) % p) := by
      unfold parabolaMap at hsum
      linarith
    obtain ⟨hquot, hrem⟩ := eq_of_two_mul_add_eq (by omega) (by omega) hsum_unfold
    -- Pass to `ZMod p`.
    have hz_sum : (x₁.1 : ZMod p) + (x₂.1 : ZMod p) = (y₁.1 : ZMod p) + (y₂.1 : ZMod p) := by
      have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hquot
      simpa [Nat.cast_add] using hcast
    have hz_sq : (x₁.1 : ZMod p) ^ 2 + (x₂.1 : ZMod p) ^ 2 =
        (y₁.1 : ZMod p) ^ 2 + (y₂.1 : ZMod p) ^ 2 := by
      have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hrem
      simpa [Nat.cast_add, ZMod.natCast_mod, Nat.cast_pow] using hcast
    have hprod := parabola_quad_identity
      (x₁.1 : ZMod p) (x₂.1 : ZMod p) (y₁.1 : ZMod p) (y₂.1 : ZMod p) hz_sum hz_sq
    have htwo_ne : (2 : ZMod p) ≠ 0 := by
      intro h20
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hge : 2 ≤ p := hp.two_le
      omega
    rw [mul_assoc] at hprod
    have hfac : ((x₁.1 : ZMod p) - (y₁.1 : ZMod p)) * ((x₁.1 : ZMod p) - (y₂.1 : ZMod p)) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left htwo_ne
    rcases mul_eq_zero.mp hfac with h1 | h2
    · left
      have hx1y1_z : (x₁.1 : ZMod p) = (y₁.1 : ZMod p) := sub_eq_zero.mp h1
      have hx1y1 : x₁.1 = y₁.1 := by
        have := congrArg ZMod.val hx1y1_z
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt x₁.2,
          Nat.mod_eq_of_lt y₁.2] at this
      have hx2y2 : x₂.1 = y₂.1 := by omega
      exact ⟨congrArg (parabolaMap p) (Fin.ext hx1y1),
        congrArg (parabolaMap p) (Fin.ext hx2y2)⟩
    · right
      have hx1y2_z : (x₁.1 : ZMod p) = (y₂.1 : ZMod p) := sub_eq_zero.mp h2
      have hx1y2 : x₁.1 = y₂.1 := by
        have := congrArg ZMod.val hx1y2_z
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt x₁.2,
          Nat.mod_eq_of_lt y₂.2] at this
      have hx2y1 : x₂.1 = y₁.1 := by omega
      exact ⟨congrArg (parabolaMap p) (Fin.ext hx1y2),
        congrArg (parabolaMap p) (Fin.ext hx2y1)⟩
  · unfold parabolaSidonSet
    rw [Finset.card_image_of_injective _ (parabolaMap_injective hp), Finset.card_univ,
      Fintype.card_fin]

/-- **Unconditional $\sqrt{N}/3$ Sidon Lower Bound (`sidon_set_lower_bound_sqrt_div_three`)**:
Combining `erdos_turan_parabola_sidon`, `example_sidon_set`, and Bertrand's Postulate
(`Nat.exists_prime_lt_and_le_two_mul`), every interval $\{1, \ldots, N\}$ ($N \ge 1$) contains
a Sidon set $A$ of cardinality at least $\sqrt{N} / 3$. -/
theorem sidon_set_lower_bound_sqrt_div_three (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ Real.sqrt N / 3 ≤ A.card := by
  by_cases hN9 : N ≤ 9
  · refine ⟨{1}, Finset.singleton_subset_iff.mpr (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩), ?_, ?_⟩
    · intro a ha b hb c hc d hd _
      simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb hc hd
      subst ha hb hc hd; left; exact ⟨rfl, rfl⟩
    · simp only [Finset.card_singleton, Nat.cast_one]
      have hsq : Real.sqrt N ≤ 3 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ 3 ^ 2))
      linarith
  · by_cases hN12 : N ≤ 12
    · refine ⟨{1, 2}, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_Icc]
        rcases hx with rfl | rfl <;> omega
      · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
        rcases hi₁ with rfl | rfl <;> rcases hj₁ with rfl | rfl <;>
          rcases hi₂ with rfl | rfl <;> rcases hj₂ with rfl | rfl <;> simp_all
      · rw [Finset.card_pair (by decide)]
        push_cast
        have hsq : Real.sqrt N ≤ 6 := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]
          exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ 6 ^ 2))
        linarith
    · by_cases hN71 : N < 72
      · refine ⟨{1, 2, 4, 8, 13}, ?_, ?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_Icc]
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
        · simpa using example_sidon_set
        · have hcard : ({1, 2, 4, 8, 13} : Finset ℕ).card = 5 := by decide
          rw [hcard]
          push_cast
          have hsq : Real.sqrt N ≤ 9 := by
            rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 9)]
            exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ 9 ^ 2))
          linarith
      · -- For `N ≥ 72`, apply Bertrand's postulate to `m = Nat.sqrt (N / 8) ≥ 3`.
        have hN72 : 72 ≤ N := not_lt.mp hN71
        let m := Nat.sqrt (N / 8)
        have hm3 : 3 ≤ m := by
          dsimp [m]
          rw [Nat.le_sqrt]
          omega
        obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
        have hp2 : p ≠ 2 := by omega
        obtain ⟨hsub, hsid, hcard⟩ := erdos_turan_parabola_sidon hp hp2
        have h2p2_le : 2 * p ^ 2 ≤ N := by
          have hm_sq : m * m ≤ N / 8 := Nat.sqrt_le (N / 8)
          have hp_sq : p ^ 2 ≤ 4 * (m * m) := by nlinarith
          omega
        refine ⟨parabolaSidonSet p, hsub.trans (Finset.Icc_subset_Icc_right h2p2_le), hsid, ?_⟩
        rw [hcard]
        have hlt_sq : N / 8 < (m + 1) * (m + 1) := Nat.lt_succ_sqrt (N / 8)
        have hN_le : N ≤ 9 * p ^ 2 := by
          have : m + 1 ≤ p := hmp
          have : (m + 1) * (m + 1) ≤ p ^ 2 := by nlinarith
          omega
        have hN_le_real : (N : ℝ) ≤ (3 * (p : ℝ)) ^ 2 := by
          calc
            (N : ℝ) ≤ (9 * p ^ 2 : ℕ) := by exact_mod_cast hN_le
            _ = (3 * (p : ℝ)) ^ 2 := by push_cast; ring
        have hsqrt_le : Real.sqrt N ≤ 3 * (p : ℝ) := by
          rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3 * (p : ℝ))]
          exact Real.sqrt_le_sqrt hN_le_real
        linarith

/-!
## Part 4: Deductions of `sidon_set_lower_bound` and `erdos_44.variants.empty_start` from Singer (`[Si38]`)
-/

/-- Singer's 1938 theorem [Si38]: for every prime $q$, there exists a Sidon subset
$A \subseteq \{1, \ldots, q^2 + q + 1\}$ of cardinality $q + 1$. -/
def SingerSidonProperty : Prop :=
  ∀ q : ℕ, q.Prime →
    ∃ᵉ (A ⊆ Finset.Icc 1 (q ^ 2 + q + 1)), IsSidon (A : Set ℕ) ∧ A.card = q + 1

/-- **Deduction of `sidon_set_lower_bound` (`44.lean`) from Singer's Theorem and Bertrand's Postulate**:
For every $N \ge 1$, there exists a Sidon subset $A \subseteq \{1, \ldots, N\}$ with
$\sqrt{N} / 2 \le |A|$. -/
theorem sidon_set_lower_bound_of_singer (hsinger : SingerSidonProperty) (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ Real.sqrt N / 2 ≤ A.card := by
  by_cases hN1 : N = 1
  · subst hN1
    refine ⟨{1}, by simp, ?_, ?_⟩
    · intro a ha b hb c hc d hd _
      simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb hc hd
      subst ha hb hc hd; left; exact ⟨rfl, rfl⟩
    · simp only [Nat.cast_one, Real.sqrt_one, Finset.card_singleton]
      norm_num
  · by_cases hN8 : N < 9
    · refine ⟨{1, 2}, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_Icc]
        rcases hx with rfl | rfl <;> omega
      · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
        rcases hi₁ with rfl | rfl <;> rcases hj₁ with rfl | rfl <;>
          rcases hi₂ with rfl | rfl <;> rcases hj₂ with rfl | rfl <;> simp_all
      · rw [Finset.card_pair (by decide)]
        push_cast
        have hsq : Real.sqrt N ≤ 4 := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ 4 ^ 2))
        linarith
    · have hN9 : 9 ≤ N := not_lt.mp hN8
      let s := Nat.sqrt N
      have hs3 : 3 ≤ s := by
        dsimp [s]
        rw [Nat.le_sqrt]
        omega
      let m := (s - 1) / 2
      have hm1 : m ≠ 0 := by omega
      obtain ⟨q, hq_prime, hmq, hq2m⟩ := Nat.exists_prime_lt_and_le_two_mul m hm1
      obtain ⟨A, hA_sub, hA_sidon, hA_card⟩ := hsinger q hq_prime
      have hq_upper : q ^ 2 + q + 1 ≤ N := by
        have hq_le_s1 : q + 1 ≤ s := by omega
        have hs_sq : s * s ≤ N := Nat.sqrt_le N
        calc
          q ^ 2 + q + 1 ≤ (q + 1) * (q + 1) := by nlinarith
          _ ≤ s * s := Nat.mul_le_mul hq_le_s1 hq_le_s1
          _ ≤ N := hs_sq
      refine ⟨A, hA_sub.trans (Finset.Icc_subset_Icc_right hq_upper), hA_sidon, ?_⟩
      rw [hA_card]
      have hs_succ : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
      have h2q : s + 1 ≤ 2 * (q + 1) := by omega
      have hN_le_real : (N : ℝ) ≤ (2 * ((q + 1 : ℕ) : ℝ)) ^ 2 := by
        have hnat : N ≤ (2 * (q + 1)) ^ 2 := by nlinarith
        calc
          (N : ℝ) ≤ ((2 * (q + 1)) ^ 2 : ℕ) := by exact_mod_cast hnat
          _ = (2 * ((q + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; ring
      have hsqrt_le : Real.sqrt N ≤ 2 * ((q + 1 : ℕ) : ℝ) := by
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * ((q + 1 : ℕ) : ℝ))]
        exact Real.sqrt_le_sqrt hN_le_real
      linarith

/-- **Deduction of `erdos_44.variants.empty_start` (`44.lean`) from Singer's Theorem and Dense Primes**:
As explained in the docstring of `erdos_44.variants.empty_start`, if Singer's construction holds and
every interval $[(1 - \varepsilon)\sqrt{M} - 1, \sqrt{M} - 1]$ for sufficiently large $M$ contains a
prime $q$, then for every $\varepsilon > 0$ and all sufficiently large $M$, $\{1, \ldots, M\}$
contains a Sidon set of size at least $(1 - \varepsilon)\sqrt{M}$. -/
theorem erdos_44_empty_start_of_singer
    (hsinger : SingerSidonProperty)
    (hdense_primes : ∀ ε > (0 : ℝ), ∀ᶠ M : ℕ in Filter.atTop,
      ∃ q : ℕ, q.Prime ∧ (1 - ε) * Real.sqrt M ≤ (q + 1 : ℕ) ∧ q ^ 2 + q + 1 ≤ M) :
    ∀ᵉ (ε > (0 : ℝ)), ∀ᶠ (M : ℕ) in Filter.atTop,
      ∃ᵉ (A ⊆ Finset.Icc 1 M), IsSidon (A : Set ℕ) ∧ (1 - ε) * Real.sqrt M ≤ A.card := by
  intro ε hε
  filter_upwards [hdense_primes ε hε] with M ⟨q, hq_prime, hq_lb, hq_ub⟩
  obtain ⟨A, hA_sub, hA_sidon, hA_card⟩ := hsinger q hq_prime
  refine ⟨A, hA_sub.trans (Finset.Icc_subset_Icc_right hq_ub), hA_sidon, ?_⟩
  rwa [hA_card]

end Erdos44

#print axioms Erdos44.maxSidonSubsetCard_icc_bound
#print axioms Erdos44.example_sidon_set
#print axioms Erdos44.greedy_sidon_construction
#print axioms Erdos44.erdos_turan_parabola_sidon
#print axioms Erdos44.sidon_set_lower_bound_sqrt_div_three
#print axioms Erdos44.sidon_set_lower_bound_of_singer
#print axioms Erdos44.erdos_44_empty_start_of_singer
