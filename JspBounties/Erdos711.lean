/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 711 (`FormalConjectures/ErdosProblems/711.lean`): Distinct Multiples in Short Intervals

*References:*
- [erdosproblems.com/711](https://www.erdosproblems.com/711)
- [ErPo80] Erdős, P. and Pomerance, C., *Matching the natural numbers up to $n$ with distinct
  multiples in another interval*. Indag. Math. 83 (1980), 147–161.
- [vD26] van Doorn, W., *On the length of an interval that contains distinct multiples of the
  first $n$ positive integers*. [arXiv:2601.16972](https://arxiv.org/abs/2601.16972), Integers 26 (2026), #A7.

This file formalizes complete, zero-`sorry` results for `FormalConjectures/ErdosProblems/711.lean`:
1. **Universal Existence and Uniqueness of Minimal Interval Length $f(n, m)$
   (`exists_isMinimalIntervalLength`, `isMinimalIntervalLength_unique`)**:
   For every $n, m \in \mathbb{N}$, proves via an explicit strictly increasing multiple construction
   $a_i = (m + i + 1)(i + 1)$ and well-ordering (`Nat.find`) that there exists a unique $L$
   satisfying `IsMinimalIntervalLength n m L`.
2. **Exact Evaluation at $m = 0$ (`isMinimalIntervalLength_zero`) and General Lower Bound
   (`n_add_one_le_of_isMinimalIntervalLength`)**:
   Proves by pigeonhole injection into `Finset.Ioo m (m + L)` that $f(n, m) \ge n + 1$ for all
   $n \ge 1$ and all $m$, with equality $f(n, 0) = n + 1$ at $m = 0$.
3. **Common-Multiple Periodicity of $f(n, m)$ (`isMinimalIntervalLength_add_of_common_multiple`)**:
   If $M$ is divisible by every $k \in \{1, \ldots, n\}$, then shifting the interval by $M$
   preserves valid tuples (`HasDivisibleDistinctTuple n (m + M) L ↔ HasDivisibleDistinctTuple n m L`)
   and hence $f(n, m + M) = f(n, m)$.
4. **Deduction of `erdos_711.parts.ii` from van Doorn's [vD26] Quantitative Theorem
   (`erdos_711_parts_ii_of_van_doorn`)**:
   Combines `exists_isMinimalIntervalLength` with van Doorn's lower bound to prove `erdos_711.parts.ii`.
-/

open Filter Finset

namespace Erdos711

/-- There are distinct $a_1,\ldots,a_n$ in the open interval $(m,m+L)$ such that
$i \mid a_i$ for every $1 \leq i \leq n$. -/
def HasDivisibleDistinctTuple (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ,
    Function.Injective a ∧
      ∀ i : Fin n, m < a i ∧ a i < m + L ∧ (i.val + 1) ∣ a i

/-- $L$ is the minimal interval length for the parameters $(n,m)$. -/
def IsMinimalIntervalLength (n m L : ℕ) : Prop :=
  HasDivisibleDistinctTuple n m L ∧
    ∀ L', HasDivisibleDistinctTuple n m L' → L ≤ L'

/-!
## Part 1: Existence and Uniqueness of the Minimal Interval Length $f(n, m)$
-/

/-- Explicit upper bound witness: for every $n, m \in \mathbb{N}$, setting
$a_i = (m + i + 1)(i + 1)$ gives a valid tuple in $(m, m + L)$ for $L = (m + n + 1)(n + 1) + 1$. -/
lemma exists_hasDivisibleDistinctTuple (n m : ℕ) :
    ∃ L : ℕ, HasDivisibleDistinctTuple n m L := by
  refine ⟨(m + n + 1) * (n + 1) + 1, fun i : Fin n => (m + i.1 + 1) * (i.1 + 1), ?_, ?_⟩
  · intro i j hij
    dsimp at hij
    ext
    nlinarith
  · intro i
    have hi : i.1 < n := i.2
    refine ⟨by nlinarith, ?_, dvd_mul_left (i.1 + 1) (m + i.1 + 1)⟩
    calc
      (m + i.1 + 1) * (i.1 + 1) ≤ (m + n + 1) * (n + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ < m + ((m + n + 1) * (n + 1) + 1) := by omega

/-- **Existence of Minimal Interval Length (`exists_isMinimalIntervalLength`)**:
For every $n, m \in \mathbb{N}$, there exists $L \in \mathbb{N}$ satisfying
`IsMinimalIntervalLength n m L`. -/
theorem exists_isMinimalIntervalLength (n m : ℕ) :
    ∃ L : ℕ, IsMinimalIntervalLength n m L := by
  classical
  have hex := exists_hasDivisibleDistinctTuple n m
  exact ⟨Nat.find hex, Nat.find_spec hex, fun L' hL' => Nat.find_min' hex hL'⟩

/-- **Uniqueness of Minimal Interval Length (`isMinimalIntervalLength_unique`)**:
If $L_1$ and $L_2$ both satisfy `IsMinimalIntervalLength n m`, then $L_1 = L_2$. -/
theorem isMinimalIntervalLength_unique {n m L₁ L₂ : ℕ}
    (h₁ : IsMinimalIntervalLength n m L₁) (h₂ : IsMinimalIntervalLength n m L₂) :
    L₁ = L₂ :=
  le_antisymm (h₁.2 L₂ h₂.1) (h₂.2 L₁ h₁.1)

/-!
## Part 2: General Lower Bound $f(n, m) \ge n + 1$ and Exact Evaluation $f(n, 0) = n + 1$
-/

/-- **General Pigeonhole Lower Bound (`n_add_one_le_of_hasDivisibleDistinctTuple`)**:
For any $n \ge 1$ and any $m, L \in \mathbb{N}$, if `HasDivisibleDistinctTuple n m L` holds, then
$n + 1 \le L$. -/
theorem n_add_one_le_of_hasDivisibleDistinctTuple {n m L : ℕ} (hn : 1 ≤ n)
    (h : HasDivisibleDistinctTuple n m L) : n + 1 ≤ L := by
  obtain ⟨a, hinj, ha⟩ := h
  have hsub : Finset.univ.image a ⊆ Finset.Ioo m (m + L) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ioo.mpr ⟨(ha i).1, (ha i).2.1⟩
  have hcard : n ≤ L - 1 := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ = (Finset.univ.image a).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.Ioo m (m + L)).card := Finset.card_le_card hsub
      _ = L - 1 := by simp
  have hL_pos : 1 ≤ L := by
    have i0 : Fin n := ⟨0, hn⟩
    have := (ha i0).1
    have := (ha i0).2.1
    omega
  omega

/-- **Exact Value at $m = 0$ (`isMinimalIntervalLength_zero`)**:
For every $n \ge 1$, the minimal interval length for $(n, 0)$ is $n + 1$. -/
theorem isMinimalIntervalLength_zero {n : ℕ} (hn : 1 ≤ n) :
    IsMinimalIntervalLength n 0 (n + 1) := by
  refine ⟨⟨fun i : Fin n => i.1 + 1, ?_, ?_⟩, fun L' hL' =>
    n_add_one_le_of_hasDivisibleDistinctTuple hn hL'⟩
  · intro i j hij
    dsimp at hij
    ext
    omega
  · intro i
    have hi : i.1 < n := i.2
    dsimp
    exact ⟨by omega, by omega, dvd_refl (i.1 + 1)⟩

/-!
## Part 3: Common-Multiple Periodicity of $f(n, m)$
-/

/-- Shifting $m$ by a common multiple $M$ of $1, \ldots, n$ preserves `HasDivisibleDistinctTuple`. -/
theorem hasDivisibleDistinctTuple_add_iff_of_dvd {n m M L : ℕ}
    (hM : ∀ i : Fin n, (i.1 + 1) ∣ M) :
    HasDivisibleDistinctTuple n (m + M) L ↔ HasDivisibleDistinctTuple n m L := by
  constructor
  · rintro ⟨a, hinj, ha⟩
    refine ⟨fun i => a i - M, ?_, ?_⟩
    · intro i j hij
      dsimp at hij
      have hi : M < a i := by have := (ha i).1; omega
      have hj : M < a j := by have := (ha j).1; omega
      exact hinj (by omega)
    · intro i
      obtain ⟨h1, h2, hdvd⟩ := ha i
      dsimp
      refine ⟨by omega, by omega, ?_⟩
      exact Nat.dvd_sub hdvd (hM i)
  · rintro ⟨a, hinj, ha⟩
    refine ⟨fun i => a i + M, ?_, ?_⟩
    · intro i j hij
      dsimp at hij
      exact hinj (by omega)
    · intro i
      obtain ⟨h1, h2, hdvd⟩ := ha i
      dsimp
      exact ⟨by omega, by omega, Nat.dvd_add hdvd (hM i)⟩

/-- Shifting $m$ by a common multiple $M$ of $1, \ldots, n$ preserves `IsMinimalIntervalLength`. -/
theorem isMinimalIntervalLength_add_iff_of_dvd {n m M L : ℕ}
    (hM : ∀ i : Fin n, (i.1 + 1) ∣ M) :
    IsMinimalIntervalLength n (m + M) L ↔ IsMinimalIntervalLength n m L := by
  simp only [IsMinimalIntervalLength, hasDivisibleDistinctTuple_add_iff_of_dvd hM]

/-!
## Part 4: Deduction of `erdos_711.parts.ii` from van Doorn's Lower Bound (`[vD26]`)
-/

/-- **Deduction of `erdos_711.parts.ii` from van Doorn's Lower Bound (`[vD26]`)**:
Combining `exists_isMinimalIntervalLength` with van Doorn's theorem [vD26] that for every $B$ and
all sufficiently large $n$, there exists $m$ whose minimal interval length exceeds $f(n, n)$ by at
least $B$, yields the exact statement of `erdos_711.parts.ii`. -/
theorem erdos_711_parts_ii_of_van_doorn
    (hvd : ∀ B : ℕ, ∀ᶠ n in atTop, ∃ m : ℕ,
      ∀ Lm Ln : ℕ, HasDivisibleDistinctTuple n m Lm →
        IsMinimalIntervalLength n n Ln → B ≤ Lm - Ln) :
    ∀ B : ℕ, ∀ᶠ n in atTop,
      ∃ m Lm Ln : ℕ, IsMinimalIntervalLength n m Lm ∧
        IsMinimalIntervalLength n n Ln ∧ B ≤ Lm - Ln := by
  intro B
  filter_upwards [hvd B] with n ⟨m, hm⟩
  obtain ⟨Lm, hLm⟩ := exists_isMinimalIntervalLength n m
  obtain ⟨Ln, hLn⟩ := exists_isMinimalIntervalLength n n
  exact ⟨m, Lm, Ln, hLm, hLn, hm Lm Ln hLm.1 hLn⟩

end Erdos711

#print axioms Erdos711.exists_isMinimalIntervalLength
#print axioms Erdos711.isMinimalIntervalLength_unique
#print axioms Erdos711.n_add_one_le_of_hasDivisibleDistinctTuple
#print axioms Erdos711.isMinimalIntervalLength_zero
#print axioms Erdos711.isMinimalIntervalLength_add_iff_of_dvd
#print axioms Erdos711.erdos_711_parts_ii_of_van_doorn
