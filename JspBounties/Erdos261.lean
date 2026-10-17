import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Erdős Problem 261 (JSP-000226)

*References:*
- [erdosproblems.com/261](https://www.erdosproblems.com/261)
- [BoLo90] Borwein, Peter and Loring, Terry A., *Some questions of Erdős and Graham on numbers
  of the form $\sum g_n/2^{g_n}$*. Math. Comp. (1990), 377-394.
- [Er88c] Erdős, P., *On the irrationality of certain series: problems and results*. New advances
  in transcendence theory (Durham, 1986) (1988), 102-109.

We prove `erdos_261.parts.i`: there are infinitely many positive integers $n$ such that there
exist $t \ge 2$ and distinct integers $a_1, \ldots, a_t \ge 1$ satisfying
$$\frac{n}{2^n} = \sum_{1 \le k \le t} \frac{a_k}{2^{a_k}},$$
as well as Borwein and Loring's identity and family construction (`erdos_261.variants.borwein_loring`
and `erdos_261.variants.borwein_loring_property`).
-/

namespace Erdos261

/-- A natural number $n$ is said to have property `Erdos261Prop` if there exist $t \ge 2$
pairwise distinct positive integers $a_1, \ldots, a_t$ such that
$n / 2^n = \sum_{1 \le k \le t} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- Telescoping identity: for all $n, m \in \mathbb{N}$,
$$\sum_{i=0}^{m-1} \frac{n + 1 + i}{2^{n + 1 + i}} = \frac{n + 2}{2^n} - \frac{n + m + 2}{2^{n + m}}.$$ -/
lemma sum_range_dyadic (n m : ℕ) :
    ∑ i ∈ Finset.range m, ((n + 1 + i : ℕ) : ℚ) / (2 ^ (n + 1 + i) : ℚ) =
      ((n + 2 : ℕ) : ℚ) / (2 ^ n : ℚ) - ((n + m + 2 : ℕ) : ℚ) / (2 ^ (n + m) : ℚ) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow1 : (2 : ℚ) ^ (n + 1 + m) = (2 : ℚ) ^ (n + m) * 2 := by
      rw [show n + 1 + m = n + m + 1 by omega, pow_succ]
    have hpow2 : (2 : ℚ) ^ (n + (m + 1)) = (2 : ℚ) ^ (n + m) * 2 := by
      rw [show n + (m + 1) = n + m + 1 by omega, pow_succ]
    rw [hpow1, hpow2]
    push_cast
    have hne1 : (2 : ℚ) ^ n ≠ 0 := by positivity
    have hne2 : (2 : ℚ) ^ (n + m) ≠ 0 := by positivity
    field_simp
    ring

/-- Sum over `Finset.Ioc n (n + m)` matches `Finset.range m`. -/
lemma sum_Ioc_dyadic (n m : ℕ) :
    ∑ k ∈ Finset.Ioc n (n + m), (k : ℚ) / (2 ^ k : ℚ) =
      ∑ i ∈ Finset.range m, ((n + 1 + i : ℕ) : ℚ) / (2 ^ (n + 1 + i) : ℚ) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [show n + (m + 1) = n + m + 1 by omega,
      Finset.sum_Ioc_succ_top (by omega : n ≤ n + m), ih, Finset.sum_range_succ]
    congr 1
    have : n + m + 1 = n + 1 + m := by omega
    rw [this]

/-- Helper inequality: $m + 2 \le 2^{m + 1}$ for all $m \ge 1$. -/
lemma add_two_le_two_pow_succ (m : ℕ) (hm : 0 < m) : m + 2 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk
    · norm_num
    · have hk' := ih (Nat.pos_of_ne_zero hk)
      calc k + 1 + 2 = (k + 2) + 1 := by omega
        _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := Nat.add_le_add hk' (Nat.one_le_two_pow)
        _ = 2 ^ (k + 1 + 1) := by ring

/-- For every positive integer $m$, if $n = 2^{m+1} - m - 2$, then
$$\frac{n}{2^n} = \sum_{n < k \le n + m} \frac{k}{2^k}.$$
This construction is due to Borwein and Loring [BoLo90]. -/
theorem erdos_261.variants.borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
  intro n
  rw [sum_Ioc_dyadic, sum_range_dyadic]
  have hle : m + 2 ≤ 2 ^ (m + 1) := add_two_le_two_pow_succ m hm
  have hn_eq : (n : ℚ) + m + 2 = (2 : ℚ) ^ (m + 1) := by
    have : n + m + 2 = 2 ^ (m + 1) := by omega
    exact_mod_cast this
  have hpow : (2 : ℚ) ^ (n + m) = (2 : ℚ) ^ n * (2 : ℚ) ^ m := by
    rw [pow_add]
  have hpow_m1 : (2 : ℚ) ^ (m + 1) = 2 * (2 : ℚ) ^ m := by
    rw [pow_succ']
  have hne_n : (2 : ℚ) ^ n ≠ 0 := by positivity
  have hne_m : (2 : ℚ) ^ m ≠ 0 := by positivity
  push_cast
  rw [hn_eq, hpow, hpow_m1]
  field_simp
  ring

/-- The Borwein--Loring construction gives the required property when $m \ge 2$. -/
theorem erdos_261.variants.borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  set n := 2 ^ (m + 1) - m - 2
  refine ⟨m, hm, fun i : Fin m => n + 1 + i.val, ?_, ?_, ?_⟩
  · intro i j hij
    ext
    dsimp at hij
    omega
  · intro i
    dsimp
    omega
  · have hbl := erdos_261.variants.borwein_loring m (by omega)
    dsimp only at hbl
    rw [hbl, sum_Ioc_dyadic, ← Fin.sum_univ_eq_sum_range]

/-- Strict monotonicity of the Borwein--Loring sequence $m \mapsto 2^{m+1} - m - 2$ for $m \ge 2$. -/
lemma borwein_loring_strictMonoOn :
    StrictMonoOn (fun m : ℕ => 2 ^ (m + 1) - m - 2) (Set.Ici 2) := by
  intro a ha b hb hab
  rw [Set.mem_Ici] at ha hb
  have hstep : ∀ k ≥ 2, 2 ^ (k + 1) - k - 2 < 2 ^ (k + 2) - (k + 1) - 2 := by
    intro k hk
    have hle := add_two_le_two_pow_succ k (by omega)
    have hpow : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    omega
  induction hab with
  | refl => exact hstep a ha
  | @step k hkb ih =>
    have hk2 : 2 ≤ k := le_trans ha (Nat.le_of_lt hkb)
    exact lt_trans (ih (by omega)) (hstep k hk2)

/-- Are there infinitely many positive integers $n$ such that there exist some $t \ge 2$ and
distinct integers $a_1, \ldots, a_t \ge 1$ satisfying
$$\frac{n}{2^n} = \sum_{1 \le k \le t} \frac{a_k}{2^{a_k}}?$$
Yes, proved unconditionally via the Borwein--Loring family. -/
theorem erdos_261.parts.i : {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite := by
  let f : ℕ → ℕ := fun k => 2 ^ (k + 2 + 1) - (k + 2) - 2
  apply Set.infinite_of_injective_forall_mem (f := f)
  · intro x y hxy
    have hmono : StrictMono f := by
      intro a b hab
      exact borwein_loring_strictMonoOn (by simp) (by simp) (by omega)
    exact hmono.injective hxy
  · intro k
    simp only [Set.mem_ofPred_eq, f]
    refine ⟨?_, erdos_261.variants.borwein_loring_property (k + 2) (by omega)⟩
    have h0 : 2 ^ (0 + 2 + 1) - (0 + 2) - 2 = 4 := by norm_num
    rcases eq_or_ne k 0 with rfl | hk
    · omega
    · have hlt : 2 ^ (0 + 2 + 1) - (0 + 2) - 2 < 2 ^ (k + 2 + 1) - (k + 2) - 2 :=
        borwein_loring_strictMonoOn (by simp) (by simp) (by omega)
      omega

#print axioms erdos_261.variants.borwein_loring
#print axioms erdos_261.variants.borwein_loring_property
#print axioms erdos_261.parts.i

end Erdos261
