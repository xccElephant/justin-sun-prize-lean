/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)

Complete, self-contained, zero-sorry Lean 4 formalization of the resolved
case of Erdős Problem #273 (`JSP-000234`), matching the definitions and
theorem statements in Google DeepMind's `FormalConjectures/ErdosProblems/273.lean`.
-/

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

set_option maxRecDepth 200000

open Pointwise

/--
A covering system of a semiring `R` is a finite set of cosets of non-zero proper ideals whose union
covers the whole semiring. (Exact definition from `FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean`.)
-/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = @Set.univ R
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

/--
A covering system is strict if all congruence relations are taken modulo distinct ideals.
(Exact definition from `FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean`.)
-/
structure StrictCoveringSystem (R : Type*) [CommSemiring R] extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace Erdos273

/-- The 12 residue-modulus-prime triples `(r_i, m_i, p_i)` with `m_i = p_i - 1 ∣ 360` and `p_i ≥ 3` prime. -/
def resVal : Fin 12 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | 7 => 11
  | 8 => 3
  | 9 => 47
  | 10 => 71
  | 11 => 179

def modVal : Fin 12 → ℕ
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 10
  | 4 => 12
  | 5 => 18
  | 6 => 30
  | 7 => 36
  | 8 => 40
  | 9 => 60
  | 10 => 72
  | 11 => 180

def primeVal : Fin 12 → ℕ
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 11
  | 4 => 13
  | 5 => 19
  | 6 => 31
  | 7 => 37
  | 8 => 41
  | 9 => 61
  | 10 => 73
  | 11 => 181

lemma primeVal_prime : ∀ i : Fin 12, (primeVal i).Prime := by
  intro i
  fin_cases i <;> norm_num [primeVal]

lemma three_le_primeVal : ∀ i : Fin 12, 3 ≤ primeVal i := by decide

lemma modVal_eq_primeVal_sub_one : ∀ i : Fin 12, modVal i = primeVal i - 1 := by decide

lemma two_le_modVal : ∀ i : Fin 12, 2 ≤ modVal i := by decide

lemma modVal_dvd_360 : ∀ i : Fin 12, modVal i ∣ 360 := by decide

lemma modVal_injective : Function.Injective modVal := by decide

lemma cover_mod_360 : ∀ r : Fin 360, ∃ i : Fin 12, r.val % modVal i = resVal i := by decide

lemma nat_covered (n : ℕ) : ∃ i : Fin 12, n ∈ ({resVal i} : Set ℕ) + (Ideal.span {modVal i} : Set ℕ) := by
  have hlt : n % 360 < 360 := Nat.mod_lt n (by decide)
  obtain ⟨i, hi⟩ := cover_mod_360 ⟨n % 360, hlt⟩
  refine ⟨i, resVal i, rfl, (n / modVal i) * modVal i, ?_, ?_⟩
  · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    exact dvd_mul_left (modVal i) (n / modVal i)
  · change resVal i + n / modVal i * modVal i = n
    have hmod : (n % 360) % modVal i = n % modVal i :=
      Nat.mod_mod_of_dvd n (modVal_dvd_360 i)
    have hrem : n % modVal i = resVal i := hmod.symm.trans hi
    have hdiv := Nat.div_add_mod n (modVal i)
    have hmul : modVal i * (n / modVal i) = n / modVal i * modVal i := Nat.mul_comm _ _
    omega

lemma span_modVal_ne_bot (i : Fin 12) : Ideal.span ({modVal i} : Set ℕ) ≠ ⊥ := by
  intro h
  have hmem : modVal i ∈ Ideal.span ({modVal i} : Set ℕ) := Ideal.subset_span rfl
  rw [h, Submodule.mem_bot] at hmem
  have := two_le_modVal i
  omega

lemma span_modVal_ne_top (i : Fin 12) : Ideal.span ({modVal i} : Set ℕ) ≠ ⊤ := by
  intro h
  have hmem : (1 : ℕ) ∈ Ideal.span ({modVal i} : Set ℕ) := by rw [h]; trivial
  rw [Ideal.mem_span_singleton] at hmem
  have hle : modVal i ≤ 1 := Nat.le_of_dvd (by decide) hmem
  have := two_le_modVal i
  omega

lemma span_modVal_injective :
    Function.Injective (fun i : Fin 12 => Ideal.span ({modVal i} : Set ℕ)) := by
  intro i j hij
  dsimp at hij
  have hi : modVal i ∈ Ideal.span ({modVal j} : Set ℕ) := by
    rw [← hij]; exact Ideal.subset_span rfl
  have hj : modVal j ∈ Ideal.span ({modVal i} : Set ℕ) := by
    rw [hij]; exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton] at hi hj
  exact modVal_injective (Nat.dvd_antisymm hj hi)

/--
Explicit strict covering system of `ℕ` whose 12 moduli are `2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180`,
all of the form `p - 1` for primes `p ∈ {3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181}`.
-/
def witnessCoveringSystem : StrictCoveringSystem ℕ where
  ι := Fin 12
  fintypeIndex := inferInstance
  residue := resVal
  moduli := fun i => Ideal.span {modVal i}
  unionCovers := by
    ext n
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact nat_covered n
  ne_bot := span_modVal_ne_bot
  ne_top := span_modVal_ne_top
  injective_moduli := span_modVal_injective

/--
**Erdős Problem 273 (`erdos_273.variants.three`)**:
There exists a strict covering system of `ℕ` all of whose moduli are of the form `p - 1`
for some primes `p ≥ 3`.
-/
theorem erdos_273.variants.three : ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧
    c.moduli i = Ideal.span {↑(p - 1)} := by
  refine ⟨witnessCoveringSystem, fun i => ⟨primeVal i, primeVal_prime i, three_le_primeVal i, ?_⟩⟩
  change Ideal.span {modVal i} = Ideal.span {primeVal i - 1}
  rw [modVal_eq_primeVal_sub_one i]

#print axioms Erdos273.erdos_273.variants.three

end Erdos273
