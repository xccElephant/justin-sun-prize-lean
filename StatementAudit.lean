/-
Copyright 2026 Chucheng Xiang (@xccElephant).
SPDX-License-Identifier: Apache-2.0

Independent first-principles statement audit and axiom verification for `Erdos983` (`JSP-000816`).
Rebuilds the original definitions of Erdős and Straus [Er70b, pp. 138, 140] directly from
`Nat.Prime`, divisibility `(· ∣ ·)`, `Finset.Icc 1 n`, and injective `r`-tuples of primes,
proves equivalence to the `FormalConjectures/ErdosProblems/983.lean` formulation, and checks
transitive axiom dependencies of all target theorems.
-/
import Erdos983

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace StatementAudit

open Finset

/-! ### 1. First-Principles Reconstruction of `[Er70b]` Definitions -/

/-- Prime-counting function $\pi(n) = |\{p \in \{1, \dots, n\} : p \text{ prime}\}|$ built directly
from `Finset.Icc 1 n` and `Nat.Prime`. -/
def rawPi (n : ℕ) : ℕ :=
  ((Icc 1 n).filter Nat.Prime).card

/-- Literal predicate from `[Er70b, p. 138]`: "$a$ is only divisible by primes from $S$". -/
def OnlyDivisibleByPrimesIn (a : ℕ) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ a → p ∈ S

/-- Count of elements in $A$ whose prime divisors all belong to $S$. -/
noncomputable def rawSmoothCount (A S : Finset ℕ) : ℕ := by
  classical
  exact (A.filter fun a => OnlyDivisibleByPrimesIn a S).card

/-- First-principles definition of $f(k, n)$ using finite sets of $r$ primes. -/
noncomputable def rawF (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, A ⊆ Icc 1 n → A.card = k →
    ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < rawSmoothCount A S}

/-- Literal indexed-tuple definition of $f(k, n)$ matching `[Er70b]`: "there exist (distinct)
primes $p_1, \dots, p_r$ such that $> r$ many $a \in A$ are only divisible by primes from
$\{p_1, \dots, p_r\}$". -/
noncomputable def indexedF (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, A ⊆ Icc 1 n → A.card = k →
    ∃ p : Fin r ↪ ℕ, (∀ i : Fin r, (p i).Prime) ∧
      r < rawSmoothCount A (univ.map p)}

/-! ### 2. Semantic Equivalence Bridges -/

theorem rawPi_eq_primeCounting (n : ℕ) : rawPi n = Nat.primeCounting n := by
  rw [rawPi, ← Nat.primesLE_eq_filter_Icc_one, Nat.primesLE_card_eq_primeCounting]

theorem rawSmoothCount_eq_numSmooth {n : ℕ} {A S : Finset ℕ} (hA : A ⊆ Icc 1 n) :
    rawSmoothCount A S = Erdos983.numSmooth A S := by
  classical
  unfold rawSmoothCount Erdos983.numSmooth OnlyDivisibleByPrimesIn
  congr 1
  refine filter_congr fun a ha => ?_
  have ha1 : 1 ≤ a := (mem_Icc.mp (hA ha)).1
  have hne : a ≠ 0 := by omega
  constructor
  · intro h p hp
    obtain ⟨hp_prime, hp_dvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact h p hp_prime hp_dvd
  · intro h p hp_prime hp_dvd
    exact h p (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hne⟩)

theorem rawF_eq_f (k n : ℕ) : rawF k n = Erdos983.f k n := by
  unfold rawF Erdos983.f
  congr 1
  ext r
  constructor
  · intro hr A hA hAk
    obtain ⟨S, hSc, hSp, hlt⟩ := hr A hA hAk
    rw [rawSmoothCount_eq_numSmooth hA] at hlt
    exact ⟨S, hSc, hSp, hlt⟩
  · intro hr A hA hAk
    obtain ⟨S, hSc, hSp, hlt⟩ := hr A hA hAk
    rw [← rawSmoothCount_eq_numSmooth hA] at hlt
    exact ⟨S, hSc, hSp, hlt⟩

theorem indexedF_eq_rawF (k n : ℕ) : indexedF k n = rawF k n := by
  unfold indexedF rawF
  congr 1
  ext r
  constructor
  · intro hr A hA hAk
    obtain ⟨p, hp, hlt⟩ := hr A hA hAk
    refine ⟨univ.map p, ?_, ?_, hlt⟩
    · simp
    · intro q hq
      obtain ⟨i, _, rfl⟩ := mem_map.mp hq
      exact hp i
  · intro hr A hA hAk
    obtain ⟨S, hSc, hSp, hlt⟩ := hr A hA hAk
    have heq : Fintype.card S = Fintype.card (Fin r) := by
      simp [hSc]
    let e : Fin r ≃ S := (Fintype.equivOfCardEq heq).symm
    let p : Fin r ↪ ℕ := e.toEmbedding.trans (Function.Embedding.subtype _)
    have hmap : univ.map p = S := by
      ext q
      simp only [p, mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).2
      · intro hqS
        exact ⟨e.symm ⟨q, hqS⟩, by simp⟩
    refine ⟨p, fun i => hSp (p i) (by rw [← hmap]; exact mem_map_of_mem p (mem_univ i)), ?_⟩
    rwa [hmap]

/-! ### 3. Audited Original-Problem Theorems -/

/-- Audited Erdős–Straus upper bound in raw definitions:
$\forall n,\; f(\pi(n) + 1, n) \le 2\pi(\lfloor\sqrt{n}\rfloor) + 1$. -/
theorem audit_upper_bound (n : ℕ) :
    rawF (rawPi n + 1) n ≤ 2 * rawPi (Nat.sqrt n) + 1 := by
  rw [rawF_eq_f, rawPi_eq_primeCounting, rawPi_eq_primeCounting]
  exact Erdos983.erdos_983.variants.upper_bound n

/-- Audited sharpness theorem in raw definitions: for every cutoff $N_0$, there exists $n \ge N_0$
with $n \ge 2$ and $f(\pi(n) + 1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1$ (equivalently for
`indexedF`). -/
theorem audit_unbounded_exact_equality :
    ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ 2 ≤ n ∧
      rawF (rawPi n + 1) n = 2 * rawPi (Nat.sqrt n) + 1 ∧
      indexedF (rawPi n + 1) n = 2 * rawPi (Nat.sqrt n) + 1 := by
  intro N₀
  obtain ⟨n, ⟨hn2, heq⟩, hgt⟩ := Erdos983.erdos_983.variants.infinite_exact_equality.exists_gt (N₀ + 1)
  refine ⟨n, by omega, hn2, ?_, ?_⟩
  · rwa [rawF_eq_f, rawPi_eq_primeCounting, rawPi_eq_primeCounting]
  · rwa [indexedF_eq_rawF, rawF_eq_f, rawPi_eq_primeCounting, rawPi_eq_primeCounting]

/-- Audited `Filter`-free disproof of the Erdős–Straus conjecture (`JSP-000816` / `[Er70b]` Part i):
it is false that for every $M \in \mathbb{Z}$ there exists $N_0 \in \mathbb{N}$ such that all
$n \ge N_0$ satisfy $2\pi(\lfloor\sqrt{n}\rfloor) - f(\pi(n) + 1, n) \ge M$. -/
theorem audit_erdos_983_part_i_raw :
    ¬ (∀ M : ℤ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      M ≤ 2 * (rawPi (Nat.sqrt n) : ℤ) - (rawF (rawPi n + 1) n : ℤ)) := by
  intro hall
  obtain ⟨N₀, hN₀⟩ := hall 0
  obtain ⟨n, hn_ge, _, heq, _⟩ := audit_unbounded_exact_equality N₀
  have hge := hN₀ n hn_ge
  rw [heq] at hge
  push_cast at hge
  omega

/-- Exact type-level match to `FormalConjectures/ErdosProblems/983.lean` (`erdos_983.parts.i`). -/
theorem audit_fc_erdos_983_part_i :
    ¬ Filter.Tendsto (fun n : ℕ ↦
      2 * (Nat.primeCounting (Nat.sqrt n) : ℤ) - (Erdos983.f (Nat.primeCounting n + 1) n : ℤ))
      Filter.atTop Filter.atTop :=
  Erdos983.erdos_983.parts.i

/-- Exact type-level match to `FormalConjectures/ErdosProblems/983.lean`
(`erdos_983.variants.upper_bound`). -/
theorem audit_fc_upper_bound :
    ∀ n : ℕ, Erdos983.f (Nat.primeCounting n + 1) n ≤
      2 * Nat.primeCounting (Nat.sqrt n) + 1 :=
  Erdos983.erdos_983.variants.upper_bound

end StatementAudit

/-! ### 4. Transitive Axiom Audit -/

#check @Erdos983.erdos_983.variants.le_primeCounting
#check @Erdos983.erdos_983.variants.upper_bound
#check @Erdos983.exists_pomerance_prime_index
#check @Erdos983.exact_equality_at_pomerance_index
#check @Erdos983.erdos_983.variants.upper_bound_attained_frequently
#check @Erdos983.erdos_983.variants.infinite_exact_equality
#check @Erdos983.erdos_983.parts.i
#check @StatementAudit.audit_upper_bound
#check @StatementAudit.audit_unbounded_exact_equality
#check @StatementAudit.audit_erdos_983_part_i_raw
#check @StatementAudit.audit_fc_erdos_983_part_i

#print axioms Erdos983.erdos_983.variants.le_primeCounting
#print axioms Erdos983.erdos_983.variants.upper_bound
#print axioms Erdos983.exists_pomerance_prime_index
#print axioms Erdos983.exact_equality_at_pomerance_index
#print axioms Erdos983.erdos_983.variants.upper_bound_attained_frequently
#print axioms Erdos983.erdos_983.variants.infinite_exact_equality
#print axioms Erdos983.erdos_983.parts.i
#print axioms StatementAudit.audit_upper_bound
#print axioms StatementAudit.audit_unbounded_exact_equality
#print axioms StatementAudit.audit_erdos_983_part_i_raw
#print axioms StatementAudit.audit_fc_erdos_983_part_i
