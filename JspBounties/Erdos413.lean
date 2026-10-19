/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Erdős Problem 413 (`FormalConjectures/ErdosProblems/413.lean`): Barriers for $\omega$, $\Omega$, and `expProd`

*References:*
- [erdosproblems.com/413](https://www.erdosproblems.com/413)
- [Er79d] Erdős, P., *Some unconventional problems in number theory*. Acta Math. Acad. Sci.
  Hungar. 33 (1979), 71–80.
- [ErGr80] Erdős, P. and Graham, R. L., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathématique 28 (1980), p. 81.
- [La26] Lau, C. F., *On the Number of Prime Factors of Consecutive Integers*.
  [arXiv:2604.15042](https://arxiv.org/abs/2604.15042) (2026).

This file formalizes the following zero-`sorry` partial results related to `FormalConjectures/ErdosProblems/413.lean`:
1. **Shifted-Difference Characterization of $\varepsilon$-Barriers (`isBarrier_mul_iff`)**:
   For any $\varepsilon > 0$ and $f : \mathbb{N} \to \mathbb{R}$ with $f(0) \le 0$, $n$ is an
   $\varepsilon$-barrier for $f$ (`IsBarrier (fun m => ε * f m) n`) if and only if
   $f(n - k) \le k / \varepsilon$ for all $1 \le k \le n$.
2. **Equivalence of `erdos_413.parts.ii` with Linear Shifted-$\omega$ Bounds
   (`erdos_413_parts_ii_iff_linear_omega`) and Deduction from Lau's Theorem (`erdos_413_parts_ii_of_lau`)**:
   Proves that `erdos_413.parts.ii` is equivalent to the existence of $C > 0$ and infinitely many $n$
   satisfying $\omega(n - k) \le C k$ for all $1 \le k \le n$, and follows from Lau's [La26] bound
   $\omega(n - k) \le C(\log k + 1)$.
3. **Erdős–Graham's Trajectory Trapping & Coalescence Theorem (`barrier_traps_iterates`,
   `barrier_coalesces_trajectories`)**:
   Proves the foundational dynamical property noted in [ErGr80, p. 81]: if $n$ is an integer barrier
   for $g : \mathbb{N} \to \mathbb{N}$, then for every starting value $m \le n$, the iterated sequence
   $T(x) = x + g(x)$ cannot jump strictly across $n$; any two trajectories starting at $m_1, m_2 \le n$
   that eventually reach $\ge n$ must pass through $n$ itself and coalesce thereafter.
4. **Infinite Family of Non-Barriers for $\omega$ (`infinite_not_isBarrier_omega`) and Squarefree
   Property of `expProd` (`expProd_eq_one_of_squarefree`, `le_succ_expProd_of_squarefree`)**:
   Proves that $6k + 7$ is never a barrier for $\omega$ (since $\omega(6(k+1)) \ge 2$), and that
   `expProd m = 1` for every squarefree integer $m$ (the key input in Erdős's [Er79d] proof of
   `erdos_413.variants.hasPosDensity_barrier_expProd`).
-/

open ArithmeticFunction Set
open scoped omega Omega

namespace Erdos413

/-- `IsBarrier f n` means `n` is a barrier for the real-valued function `f`,
i.e. `(m : ℝ) + f m ≤ (n : ℝ)` for all `m < n`. -/
def IsBarrier (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ m < n, (m : ℝ) + f m ≤ n

/-- `expProd n` is `∏ kᵢ` when `n = ∏ pᵢ ^ kᵢ`, i.e. the product of the prime exponents of `n`. -/
def expProd (n : ℕ) : ℕ :=
  n.factorization.prod fun _ e => e

/-!
## Part 1: Shifted-Difference Characterization and Reduction of `erdos_413.parts.ii`
-/

/-- Monotonicity of barriers with respect to pointwise smaller functions: if $f \le g$ on $[0, n)$
and $n$ is a barrier for $g$, then $n$ is a barrier for $f$. -/
lemma IsBarrier.mono {f g : ℕ → ℝ} {n : ℕ} (hfg : ∀ m < n, f m ≤ g m) (hg : IsBarrier g n) :
    IsBarrier f n := by
  intro m hm
  linarith [hg m hm, hfg m hm]

/-- **Shifted-Difference Characterization of $\varepsilon$-Barriers (`isBarrier_mul_iff`)**:
For any $\varepsilon > 0$ and $f : \mathbb{N} \to \mathbb{R}$, $n$ is an $\varepsilon$-barrier for $f$
if and only if $f(n - k) \le k / \varepsilon$ for every $k \in \{1, \ldots, n\}$. -/
theorem isBarrier_mul_iff {f : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    IsBarrier (fun m => ε * f m) n ↔ ∀ k ∈ Set.Icc 1 n, f (n - k) ≤ (k : ℝ) / ε := by
  constructor
  · intro h k ⟨hk1, hkn⟩
    have hlt : n - k < n := by omega
    have hbar := h (n - k) hlt
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkn
    rw [hcast] at hbar
    have hle : ε * f (n - k) ≤ (k : ℝ) := by linarith
    exact (le_div_iff₀' hε).mpr hle
  · intro h m hm
    let k := n - m
    have hk_mem : k ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
    have hnk : n - k = m := by omega
    have hdiv := h k hk_mem
    rw [hnk, le_div_iff₀' hε] at hdiv
    have hcast : (k : ℝ) = (n : ℝ) - (m : ℝ) := by
      dsimp [k]
      exact Nat.cast_sub hm.le
    linarith

/-- **Equivalence of `erdos_413.parts.ii` with Linear Shifted-$\omega$ Bounds**:
There exists $\varepsilon > 0$ with infinitely many $\varepsilon$-barriers for $\omega$ if and only if
there exists $C > 0$ and infinitely many $n$ such that $\omega(n - k) \le C k$ for all $1 \le k \le n$. -/
theorem erdos_413_parts_ii_iff_linear_omega :
    (∃ ε > (0 : ℝ), { n | IsBarrier (fun m => ε * (ω m : ℝ)) n }.Infinite) ↔
      ∃ C > (0 : ℝ), { n : ℕ | ∀ k ∈ Set.Icc 1 n, (ω (n - k) : ℝ) ≤ C * k }.Infinite := by
  constructor
  · rintro ⟨ε, hε, hinf⟩
    refine ⟨1 / ε, by positivity, ?_⟩
    refine hinf.mono fun n hn k hk => ?_
    have h1 := (isBarrier_mul_iff hε n).mp hn k hk
    linarith [show (k : ℝ) / ε = 1 / ε * (k : ℝ) by ring]
  · rintro ⟨C, hC, hinf⟩
    refine ⟨1 / C, by positivity, ?_⟩
    refine hinf.mono fun n hn => (isBarrier_mul_iff (by positivity) n).mpr fun k hk => ?_
    have h1 := hn k hk
    have h2 : C * (k : ℝ) = (k : ℝ) / (1 / C) := by
      have : C ≠ 0 := hC.ne'
      field_simp
    linarith

/-- **Deduction of `erdos_413.parts.ii` from Lau's [La26] Logarithmic Shifted-$\omega$ Theorem**:
The premise below is a strengthened endpoint-inclusive input; it is not the literal
statement of Lau v3, Theorem 1.3, which covers only `1 < k < n`. This theorem remains
conditional. The endpoint-correct deduction from the literal theorem is
`erdos_413_parts_ii_of_lau_v3` below. Since $\log k + 1 \le k$ for all $k \ge 1$,
the stated premise yields the epsilon-barrier conclusion. -/
theorem erdos_413_parts_ii_of_lau
    (hlau : ∃ C > (0 : ℝ),
      { n : ℕ | ∀ k ∈ Set.Icc 1 n, (ω (n - k) : ℝ) ≤ C * (Real.log k + 1) }.Infinite) :
    ∃ ε > (0 : ℝ), { n | IsBarrier (fun m => ε * (ω m : ℝ)) n }.Infinite := by
  rw [erdos_413_parts_ii_iff_linear_omega]
  obtain ⟨C, hC, hinf⟩ := hlau
  refine ⟨C, hC, hinf.mono fun n hn k hk => ?_⟩
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hlog_le : Real.log (k : ℝ) + 1 ≤ (k : ℝ) := by
    have := Real.log_le_sub_one_of_pos hk_pos
    linarith
  exact (hn k hk).trans (mul_le_mul_of_nonneg_left hlog_le hC.le)

/-- Endpoint-correct deduction from Lau v3, Theorem 1.3.
The analytic theorem remains an explicit hypothesis. Translate n to n-2,
so that the first required shift uses Lau's bound at k=3. -/
theorem erdos_413_parts_ii_of_lau_v3
    (hlau : ∃ C > (0 : ℝ),
      {n : ℕ | ∀ k : ℕ, 1 < k → k < n →
        (ω (n - k) : ℝ) ≤ C * Real.log k}.Infinite) :
    ∃ ε > (0 : ℝ), {n | IsBarrier (fun m => ε * (ω m : ℝ)) n}.Infinite := by
  obtain ⟨C, hC, hinf⟩ := hlau
  let S : Set ℕ := {n | ∀ k : ℕ, 1 < k → k < n →
    (ω (n - k) : ℝ) ≤ C * Real.log k} \ {0, 1, 2}
  have hS : S.Infinite := hinf.sdiff (by simp)
  have hlarge {n : ℕ} (hn : n ∈ S) : 2 < n := by
    have hn' : n ∉ ({0, 1, 2} : Set ℕ) := hn.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn'
    omega
  have hinj : Set.InjOn (fun n : ℕ => n - 2) S := by
    intro a ha b hb he
    change a - 2 = b - 2 at he
    have := hlarge ha
    have := hlarge hb
    omega
  rw [erdos_413_parts_ii_iff_linear_omega]
  refine ⟨2 * C, by positivity, (hS.image hinj).mono ?_⟩
  rintro N ⟨n, hn, rfl⟩ k ⟨hk, hkn⟩
  change k ≤ n - 2 at hkn
  by_cases he : k = n - 2
  · simp [he]
    positivity
  · have hklt : k + 2 < n := by
      have := hlarge hn
      omega
    have hb := hn.1 (k + 2) (by omega) hklt
    have hsub : n - (k + 2) = n - 2 - k := by omega
    rw [hsub] at hb
    have hpos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hpos
    push_cast at hlog
    have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlog' : Real.log (k + 2 : ℕ) ≤ 2 * (k : ℝ) := by
      push_cast
      linarith
    calc
      (ω (n - 2 - k) : ℝ) ≤ C * Real.log (k + 2 : ℕ) := hb
      _ ≤ C * (2 * (k : ℝ)) := mul_le_mul_of_nonneg_left hlog' hC.le
      _ = (2 * C) * k := by ring

/-!
## Part 2: Erdős–Graham's Trajectory Trapping & Coalescence Theorem (`[ErGr80, p. 81]`)
-/

/-- The one-step map $T_g(m) = m + g(m)$ studied by Erdős and Graham [ErGr80]. -/
def stepMap (g : ℕ → ℕ) (m : ℕ) : ℕ :=
  m + g m

/-- **Erdős–Graham Trajectory Trapping Theorem (`barrier_traps_iterates`)**:
If $n$ is a barrier for an integer-valued function $g : \mathbb{N} \to \mathbb{N}$
(`IsBarrier (fun m => (g m : ℝ)) n`), then for every starting value $m \le n$ and every iteration
count $k \in \mathbb{N}$, either $(T_g)^{[k]}(m) < n$, or the trajectory hits $n$ exactly at some
step $j \le k$ (`(stepMap g)^[j] m = n`). In particular, no trajectory starting below $n$ can jump
over $n$. -/
theorem barrier_traps_iterates {g : ℕ → ℕ} {n : ℕ}
    (hbar : IsBarrier (fun m => (g m : ℝ)) n) {m : ℕ} (hm : m ≤ n) :
    ∀ k : ℕ, (stepMap g)^[k] m < n ∨ ∃ j ≤ k, (stepMap g)^[j] m = n := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    rcases lt_or_eq_of_le hm with hlt | rfl
    · exact Or.inl hlt
    · exact Or.inr ⟨0, le_rfl, rfl⟩
  | succ k ih =>
    rcases ih with hlt | ⟨j, hjk, hj_eq⟩
    · have hle_real := hbar ((stepMap g)^[k] m) hlt
      dsimp at hle_real
      have hle_nat : (stepMap g)^[k] m + g ((stepMap g)^[k] m) ≤ n := by
        exact_mod_cast hle_real
      have hsucc : (stepMap g)^[k + 1] m = (stepMap g)^[k] m + g ((stepMap g)^[k] m) := by
        rw [Function.iterate_succ_apply']
        rfl
      rcases lt_or_eq_of_le hle_nat with hlt' | heq'
      · exact Or.inl (hsucc.symm ▸ hlt')
      · exact Or.inr ⟨k + 1, le_rfl, hsucc.symm ▸ heq'⟩
    · exact Or.inr ⟨j, Nat.le_succ_of_le hjk, hj_eq⟩

/-- **Trajectory Coalescence at a Barrier (`barrier_coalesces_trajectories`)**:
If $n$ is a barrier for $g : \mathbb{N} \to \mathbb{N}$ and a trajectory starting at $m \le n$
reaches $\ge n$ at step $k$, then it must pass through $n$ at some step $j \le k$. -/
theorem barrier_coalesces_trajectories {g : ℕ → ℕ} {n m k : ℕ}
    (hbar : IsBarrier (fun x => (g x : ℝ)) n) (hm : m ≤ n)
    (hge : n ≤ (stepMap g)^[k] m) :
    ∃ j ≤ k, (stepMap g)^[j] m = n := by
  rcases barrier_traps_iterates hbar hm k with hlt | hhit
  · omega
  · exact hhit

/-!
## Part 3: Infinite Family of Non-Barriers for $\omega$ and Squarefree Property of `expProd`
-/

/-- For every $k \in \mathbb{N}$, $6(k + 1)$ has at least two distinct prime factors ($2$ and $3$). -/
lemma two_le_omega_six_mul_succ (k : ℕ) : 2 ≤ ω (6 * (k + 1)) := by
  have hne : 6 * (k + 1) ≠ 0 := by omega
  have hsub : ({2, 3} : Finset ℕ) ⊆ (6 * (k + 1)).primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Nat.mem_primeFactors]
    rcases hp with rfl | rfl
    · exact ⟨Nat.prime_two, ⟨3 * (k + 1), by ring⟩, hne⟩
    · exact ⟨Nat.prime_three, ⟨2 * (k + 1), by ring⟩, hne⟩
  have hcard : ({2, 3} : Finset ℕ).card ≤ (6 * (k + 1)).primeFactors.card :=
    Finset.card_le_card hsub
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]
  simpa using hcard

/-- For every $k \in \mathbb{N}$, $n = 6(k + 1) + 1$ is NOT a barrier for $\omega$, because
$m = 6(k + 1) < n$ satisfies $m + \omega(m) \ge 6(k + 1) + 2 > n$. -/
theorem not_isBarrier_omega_six_mul_succ_add_one (k : ℕ) :
    ¬ IsBarrier (fun m => (ω m : ℝ)) (6 * (k + 1) + 1) := by
  intro hbar
  have hlt : 6 * (k + 1) < 6 * (k + 1) + 1 := by omega
  have hle := hbar (6 * (k + 1)) hlt
  have homega : (2 : ℝ) ≤ (ω (6 * (k + 1)) : ℝ) := by
    exact_mod_cast two_le_omega_six_mul_succ k
  push_cast at hle
  linarith

/-- There are infinitely many positive integers $n$ that are NOT barriers for $\omega$. -/
theorem infinite_not_isBarrier_omega :
    { n : ℕ | ¬ IsBarrier (fun m => (ω m : ℝ)) n }.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 6 * (k + 1) + 1) ?_ ?_
  · intro a b hab
    dsimp at hab
    omega
  · intro k
    exact not_isBarrier_omega_six_mul_succ_add_one k

/-- **Squarefree Property of `expProd` (`expProd_eq_one_of_squarefree`)**:
For every squarefree natural number $m$, `expProd m = 1`, so $m + \mathrm{expProd}(m) = m + 1 \le n$
holds automatically for all squarefree $m < n$ (the key structural property in Erdős's 1979 proof
[Er79d] that `expProd` has a positive density of barriers). -/
theorem expProd_eq_one_of_squarefree {m : ℕ} (hm : Squarefree m) : expProd m = 1 := by
  unfold expProd
  rw [Finsupp.prod]
  refine Finset.prod_eq_one fun p hp => ?_
  have hne0 : m.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hm_ne : m ≠ 0 := by
    intro h0
    subst h0
    simp at hne0
  have hle : m.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hm_ne).mp hm p
  omega

/-- Consequently, every squarefree $m < n$ satisfies the barrier inequality
$(m : \mathbb{R}) + \mathrm{expProd}(m) \le n$. -/
theorem barrier_ineq_expProd_of_squarefree {m n : ℕ} (hm : Squarefree m) (hmn : m < n) :
    (m : ℝ) + (expProd m : ℝ) ≤ (n : ℝ) := by
  rw [expProd_eq_one_of_squarefree hm]
  have : m + 1 ≤ n := hmn
  exact_mod_cast this

end Erdos413

#print axioms Erdos413.isBarrier_mul_iff
#print axioms Erdos413.erdos_413_parts_ii_iff_linear_omega
#print axioms Erdos413.erdos_413_parts_ii_of_lau
#print axioms Erdos413.barrier_traps_iterates
#print axioms Erdos413.barrier_coalesces_trajectories
#print axioms Erdos413.infinite_not_isBarrier_omega
#print axioms Erdos413.expProd_eq_one_of_squarefree
#print axioms Erdos413.barrier_ineq_expProd_of_squarefree

#print axioms Erdos413.erdos_413_parts_ii_of_lau_v3
