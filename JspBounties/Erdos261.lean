/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Rat
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem 261 (JSP-000226)

*References:*
- [erdosproblems.com/261](https://www.erdosproblems.com/261)
- [BoLo90] Borwein, Peter and Loring, Terry A., *Some questions of Erdős and Graham on numbers
  of the form $\sum g_n/2^{g_n}$*. Math. Comp. (1990), 377-394.
- [Er88c] Erdős, P., *On the irrationality of certain series: problems and results*. New advances
  in transcendence theory (Durham, 1986) (1988), 102-109.

We prove:
1. `erdos_261.parts.i`: there are infinitely many positive integers $n$ such that there
   exist $t \ge 2$ and distinct integers $a_1, \ldots, a_t \ge 1$ satisfying
   $$\frac{n}{2^n} = \sum_{1 \le k \le t} \frac{a_k}{2^{a_k}},$$
   as well as Borwein and Loring's identity and family construction (`erdos_261.variants.borwein_loring`
   and `erdos_261.variants.borwein_loring_property`).
2. `erdos_261.variants.arbitrarily_many_representations`: for every finite `r`, some rational
   number has at least `2^r` canonical infinite representations. This does not settle the
   continuum-many representations required by part iii.
3. `erdos_261.variants.two_representations`: there exists a rational number $x$ with at least two
   distinct representations $x = \sum_{k=1}^\infty a_k / 2^{a_k}$ by strictly increasing positive
   integers $a_k$.
-/

open scoped Cardinal

namespace Erdos261

/-- A natural number $n$ is said to have property `Erdos261Prop` if there exist $t \ge 2$
pairwise distinct positive integers $a_1, \ldots, a_t$ such that
$n / 2^n = \sum_{1 \le k \le t} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- A canonical infinite representation of a rational number $x$ by positive integers. The
denominators are strictly increasing so that reorderings are not counted as different
representations. -/
def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

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

/-- Exponential growth bound: $(k + 1)(k + 2) \le 2^{k + 2}$ for all $k \in \mathbb{N}$. -/
lemma mul_succ_succ_le_two_pow (k : ℕ) : (k + 1) * (k + 2) ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk
    · norm_num
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
      calc
        (k + 2) * (k + 3) = (k + 1) * (k + 2) + 2 * (k + 2) := by ring
        _ ≤ (k + 1) * (k + 2) + (k + 1) * (k + 2) := by nlinarith
        _ ≤ 2 ^ (k + 2) + 2 ^ (k + 2) := Nat.add_le_add ih ih
        _ = 2 ^ (k + 3) := by ring

/-- Rational tail bound: $(n + m + 2) / 2^{n + m} \le 4 / (m + 1)$ for all $n, m \in \mathbb{N}$. -/
lemma dyadic_tail_remainder_le (n m : ℕ) :
    ((n + m + 2 : ℕ) : ℚ) / (2 ^ (n + m) : ℚ) ≤ 4 / ((m + 1 : ℕ) : ℚ) := by
  have hnat : (m + 1) * (n + m + 2) ≤ 4 * 2 ^ (n + m) := by
    calc
      (m + 1) * (n + m + 2) ≤ (n + m + 1) * (n + m + 2) :=
        Nat.mul_le_mul_right (n + m + 2) (by omega)
      _ ≤ 2 ^ (n + m + 2) := mul_succ_succ_le_two_pow (n + m)
      _ = 4 * 2 ^ (n + m) := by ring
  have hrat : ((m + 1 : ℕ) : ℚ) * ((n + m + 2 : ℕ) : ℚ) ≤ 4 * (2 : ℚ) ^ (n + m) := by
    exact_mod_cast hnat
  have hm_pos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
  have hpow_pos : (0 : ℚ) < (2 : ℚ) ^ (n + m) := by positivity
  rw [div_le_div_iff₀ hpow_pos hm_pos]
  linarith

/-- Infinite dyadic tail series in $\mathbb{Q}$:
$$\sum_{i=0}^\infty \frac{n + 1 + i}{2^{n + 1 + i}} = \frac{n + 2}{2^n}.$$ -/
lemma hasSum_dyadic_tail (n : ℕ) :
    HasSum (fun i : ℕ => ((n + 1 + i : ℕ) : ℚ) / (2 ^ (n + 1 + i) : ℚ))
      (((n + 2 : ℕ) : ℚ) / (2 ^ n : ℚ)) := by
  let f : ℕ → ℚ := fun i => ((n + 1 + i : ℕ) : ℚ) / (2 ^ (n + 1 + i) : ℚ)
  have hf_nonneg : ∀ i, 0 ≤ f i := fun i => by dsimp [f]; positivity
  apply hasSum_of_isLUB_of_nonneg _ hf_nonneg
  constructor
  · rintro _ ⟨s, rfl⟩
    let M := s.sup id + 1
    have hsub : s ⊆ Finset.range M := by
      intro i hi
      rw [Finset.mem_range]
      have : i ≤ s.sup id := Finset.le_sup (f := id) hi
      omega
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf_nonneg i)
    have hrem : (0 : ℚ) ≤ ((n + M + 2 : ℕ) : ℚ) / (2 ^ (n + M) : ℚ) := by positivity
    dsimp [f] at hle ⊢
    rw [sum_range_dyadic n M] at hle
    linarith
  · intro y hy
    by_contra! hlt
    set ε : ℚ := ((n + 2 : ℕ) : ℚ) / (2 ^ n : ℚ) - y
    have hε : 0 < ε := sub_pos.mpr hlt
    obtain ⟨m, hm⟩ := exists_nat_gt (4 / ε)
    have hsum_le : ∑ i ∈ Finset.range m, f i ≤ y := hy ⟨Finset.range m, rfl⟩
    dsimp [f] at hsum_le
    rw [sum_range_dyadic n m] at hsum_le
    have hrem_ge : ε ≤ ((n + m + 2 : ℕ) : ℚ) / (2 ^ (n + m) : ℚ) := by linarith
    have hrem_le := dyadic_tail_remainder_le n m
    have hm1_gt : 4 / ε < ((m + 1 : ℕ) : ℚ) := by
      push_cast
      linarith
    have hm1_pos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
    have hlt_eps : 4 / ((m + 1 : ℕ) : ℚ) < ε := (div_lt_iff₀ hm1_pos).mpr
      ((div_lt_iff₀ hε).mp hm1_gt |>.trans_eq (mul_comm _ _))
    linarith

/-- First representation sequence for $x = 3/8$: $a_0(k) = k + 5$ ($5, 6, 7, 8, \ldots$). -/
def repSeq0 (k : ℕ) : ℕ := k + 5

/-- Second representation sequence for $x = 3/8$: $a_1(0) = 4$ and $a_1(k) = k + 6$ for $k \ge 1$
($4, 7, 8, 9, \ldots$). -/
def repSeq1 (k : ℕ) : ℕ := if k = 0 then 4 else k + 6

lemma repSeq0_representation : Erdos261InfiniteRepresentation (3 / 8 : ℚ) repSeq0 := by
  have hhas : HasSum (fun k : ℕ => (repSeq0 k : ℚ) / (2 ^ (repSeq0 k) : ℚ)) (3 / 8 : ℚ) := by
    have h4 := hasSum_dyadic_tail 4
    have heq : (fun i : ℕ => ((4 + 1 + i : ℕ) : ℚ) / (2 ^ (4 + 1 + i) : ℚ)) =
        (fun k : ℕ => (repSeq0 k : ℚ) / (2 ^ (repSeq0 k) : ℚ)) := by
      ext k
      simp [repSeq0, add_comm]
    have hval : (((4 + 2 : ℕ) : ℚ) / (2 ^ 4 : ℚ)) = (3 / 8 : ℚ) := by norm_num
    rwa [heq, hval] at h4
  refine ⟨?_, ?_, hhas.summable, hhas.tsum_eq.symm⟩
  · intro i j hij; dsimp [repSeq0]; omega
  · intro k; dsimp [repSeq0]; omega

lemma repSeq1_representation : Erdos261InfiniteRepresentation (3 / 8 : ℚ) repSeq1 := by
  let g : ℕ → ℚ := fun k => (repSeq1 k : ℚ) / (2 ^ (repSeq1 k) : ℚ)
  have hhas : HasSum g (3 / 8 : ℚ) := by
    have h6 := hasSum_dyadic_tail 6
    have heq : (fun i : ℕ => ((6 + 1 + i : ℕ) : ℚ) / (2 ^ (6 + 1 + i) : ℚ)) =
        (fun k : ℕ => g (k + 1)) := by
      ext k
      dsimp [g, repSeq1]
      have hk : 7 + k = k + 1 + 6 := by omega
      rw [hk]
    rw [heq] at h6
    have h0 : HasSum g (g 0 + (((6 + 2 : ℕ) : ℚ) / (2 ^ 6 : ℚ))) := HasSum.zero_add h6
    have hval : g 0 + (((6 + 2 : ℕ) : ℚ) / (2 ^ 6 : ℚ)) = (3 / 8 : ℚ) := by
      dsimp [g, repSeq1]
      norm_num
    rwa [hval] at h0
  refine ⟨?_, ?_, hhas.summable, hhas.tsum_eq.symm⟩
  · intro i j hij
    dsimp [repSeq1]
    split_ifs <;> omega
  · intro k
    dsimp [repSeq1]
    split_ifs <;> omega

/-- There exists a rational $x$ with at least two representations
$$x = \sum_{k=1}^{\infty} \frac{a_k}{2^{a_k}}$$
by pairwise distinct positive integers $a_k$. -/
theorem erdos_261.variants.two_representations : ∃ x : ℚ,
    2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  refine ⟨3 / 8, ?_⟩
  have hne : repSeq0 ≠ repSeq1 := by
    intro h
    have := congrFun h 0
    simp [repSeq0, repSeq1] at this
  have hsub : ({repSeq0, repSeq1} : Set (ℕ → ℕ)) ⊆
      {a : ℕ → ℕ | Erdos261InfiniteRepresentation (3 / 8) a} := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact repSeq0_representation
    · exact repSeq1_representation
  have hcard : #({repSeq0, repSeq1} : Set (ℕ → ℕ)) = 2 := by
    rw [Cardinal.mk_insert (by simpa using hne), Cardinal.mk_singleton]
    norm_num
  exact hcard ▸ Cardinal.mk_le_mk_of_subset hsub

def dyadicWeight (n : ℕ) : ℚ := n / (2 ^ n : ℚ)

lemma hasSum_dyadicWeight : HasSum dyadicWeight 2 := by
  have h := hasSum_dyadic_tail 0
  have hshift : HasSum (fun n => dyadicWeight (n + 1)) 2 := by
    simpa [dyadicWeight, Nat.add_comm] using h
  have hfull := (hasSum_nat_add_iff 1).mp hshift
  simpa [dyadicWeight] using hfull

noncomputable def canonicalEnumeration (s : Set ℕ) (hs : s.Infinite) : ℕ → ℕ :=
  let := hs.to_subtype
  fun n => (Nat.Subtype.orderIsoOfNat s n).val

lemma canonicalEnumeration_range (s : Set ℕ) (hs : s.Infinite) :
    Set.range (canonicalEnumeration s hs) = s := by
  let := hs.to_subtype
  ext n
  constructor
  · rintro ⟨k, rfl⟩
    exact (Nat.Subtype.orderIsoOfNat s k).property
  · intro hn
    obtain ⟨k, hk⟩ := (Nat.Subtype.orderIsoOfNat s).surjective ⟨n, hn⟩
    exact ⟨k, congrArg Subtype.val hk⟩

lemma canonicalEnumeration_representation (s : Set ℕ) (hs : s.Infinite)
    (hp : ∀ n ∈ s, 1 ≤ n) {x : ℚ}
    (hx : HasSum (fun n : s => dyadicWeight n.val) x) :
    Erdos261InfiniteRepresentation x (canonicalEnumeration s hs) := by
  let := hs.to_subtype
  have hsum : HasSum (fun n => dyadicWeight (canonicalEnumeration s hs n)) x :=
    (Nat.Subtype.orderIsoOfNat s).toEquiv.hasSum_iff.mpr hx
  refine ⟨?_, ?_, hsum.summable, hsum.tsum_eq.symm⟩
  · intro i j hij
    exact (Nat.Subtype.orderIsoOfNat s).strictMono hij
  · intro n
    exact hp _ (Nat.Subtype.orderIsoOfNat s n).property

lemma hasSum_finite_indicator (s : Finset ℕ) :
    HasSum (fun n => if n ∈ s then dyadicWeight n else 0)
      (∑ n ∈ s, dyadicWeight n) := by
  classical
  have h : HasSum ((s : Set ℕ).indicator dyadicWeight) (∑ n ∈ s, dyadicWeight n) :=
    hasSum_subtype_iff_indicator.mp (s.hasSum dyadicWeight)
  exact h.congr_fun (fun n => by simp [Set.indicator_apply])

/-- Removing finitely many positive denominators leaves a canonical infinite representation
of the rational total minus their weights. -/
theorem finite_deletion_representation (s : Finset ℕ) :
    ∃ a : ℕ → ℕ,
      Erdos261InfiniteRepresentation (2 - ∑ n ∈ s, dyadicWeight n) a ∧
        Set.range a = {n : ℕ | 0 < n ∧ n ∉ s} := by
  classical
  let S : Set ℕ := {n | 0 < n ∧ n ∉ s}
  have hpos : ({n : ℕ | 0 < n} : Set ℕ).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun n => n + 1)
      (by intro a b hab; dsimp at hab; omega) (by intro n; simp)
  have hS : S.Infinite := hpos.sdiff s.finite_toSet
  have hsub := hasSum_dyadicWeight.sub (hasSum_finite_indicator s)
  have hind : HasSum (S.indicator dyadicWeight) (2 - ∑ n ∈ s, dyadicWeight n) := by
    apply hsub.congr_fun
    intro n
    by_cases hn : n = 0
    · subst n
      simp [S, Set.indicator, dyadicWeight]
    · by_cases hm : n ∈ s <;> simp [S, Set.indicator, hm, Nat.pos_of_ne_zero hn]
  refine ⟨canonicalEnumeration S hS, ?_, canonicalEnumeration_range S hS⟩
  apply canonicalEnumeration_representation S hS
  · intro n hn; exact hn.1
  · exact hasSum_subtype_iff_indicator.mpr hind

/-- Starting points of disjoint Borwein--Loring replacement blocks. -/
def blockStart (i : ℕ) : ℕ := 2 ^ (i + 3) - (i + 2) - 2

def replacementBlock (i : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ioc (blockStart i) (blockStart i + (i + 2))
  else {blockStart i}

lemma blockStart_pos (i : ℕ) : 0 < blockStart i := by
  have hmono := borwein_loring_strictMonoOn (a := 2) (b := i + 2)
  by_cases hi : i = 0
  · subst i; norm_num [blockStart]
  · have hh := hmono (by simp) (by simp) (by omega)
    norm_num at hh
    simpa [blockStart, show i + 2 + 1 = i + 3 by omega] using (lt_trans (by norm_num : 0 < 4) hh)

lemma block_separated {i j : ℕ} (hij : i < j) :
    blockStart i + (i + 2) < blockStart j := by
  have hi := add_two_le_two_pow_succ (i + 2) (by omega)
  have hstep : blockStart i + (i + 2) < blockStart (i + 1) := by
    have hh := add_two_le_two_pow_succ (i + 3) (by omega)
    have hg : i + 3 ≤ 2 ^ (i + 2) := by
      simpa [show i + 1 + 1 = i + 2 by omega] using add_two_le_two_pow_succ (i + 1) (by omega)
    have hprev : 2 ^ (i + 3) = 2 * 2 ^ (i + 2) := by ring
    have hlarge : 2 * (i + 3) ≤ 2 ^ (i + 3) := by omega
    have hp : 2 ^ (i + 4) = 2 * 2 ^ (i + 3) := by ring
    dsimp [blockStart]
    rw [show i + 1 + 3 = i + 4 by omega, hp]
    omega
  by_cases he : j = i + 1
  · simpa [he] using hstep
  · have hh := borwein_loring_strictMonoOn
        (a := i + 1 + 2) (b := j + 2) (by simp) (by simp) (by omega)
    have hj : blockStart (i + 1) < blockStart j := by
      simpa [blockStart, show i + 1 + 2 + 1 = i + 1 + 3 by omega,
        show j + 2 + 1 = j + 3 by omega] using hh
    exact hstep.trans hj

lemma replacementBlock_bounds (i : ℕ) (b : Bool) {n : ℕ}
    (hn : n ∈ replacementBlock i b) :
    blockStart i ≤ n ∧ n ≤ blockStart i + (i + 2) := by
  cases b <;> simp [replacementBlock] at hn <;> omega

lemma replacementBlock_disjoint {i j : ℕ} (hij : i ≠ j) (b c : Bool) :
    Disjoint (replacementBlock i b) (replacementBlock j c) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  have hi := replacementBlock_bounds i b hn
  have hj := replacementBlock_bounds j c hm
  rcases lt_or_gt_of_ne hij with h | h
  · have := block_separated h; omega
  · have := block_separated h; omega

lemma replacementBlock_sum (i : ℕ) (b : Bool) :
    ∑ n ∈ replacementBlock i b, dyadicWeight n = dyadicWeight (blockStart i) := by
  cases b
  · simp [replacementBlock]
  · have h := erdos_261.variants.borwein_loring (i + 2) (by omega)
    simpa [replacementBlock, blockStart, dyadicWeight,
      show i + 2 + 1 = i + 3 by omega] using h.symm

lemma replacementBlock_marker (i : ℕ) (b : Bool) :
    blockStart i ∈ replacementBlock i b ↔ b = false := by
  cases b <;> simp [replacementBlock]

noncomputable def deletedBlocks (r : ℕ) (bits : Fin r → Bool) : Finset ℕ :=
  Finset.univ.biUnion (fun i => replacementBlock i.val (bits i))

lemma deletedBlocks_sum (r : ℕ) (bits : Fin r → Bool) :
    ∑ n ∈ deletedBlocks r bits, dyadicWeight n =
      ∑ i : Fin r, dyadicWeight (blockStart i.val) := by
  classical
  rw [deletedBlocks, Finset.sum_biUnion]
  · exact Finset.sum_congr rfl (fun i _ => replacementBlock_sum i.val (bits i))
  · intro i _ j _ hij
    exact replacementBlock_disjoint (fun h => hij (Fin.ext h)) _ _

lemma deletedBlocks_marker (r : ℕ) (bits : Fin r → Bool) (i : Fin r) :
    blockStart i.val ∈ deletedBlocks r bits ↔ bits i = false := by
  classical
  simp only [deletedBlocks, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst j; exact (replacementBlock_marker _ _).mp hj
    · have hnot := replacementBlock_disjoint (i := j.val) (j := i.val)
        (fun h => hji (Fin.ext h)) (bits j) false
      have hi : blockStart i.val ∈ replacementBlock i.val false := by simp [replacementBlock]
      exact False.elim (Finset.disjoint_left.mp hnot hj hi)
  · intro hb
    exact ⟨i, (replacementBlock_marker _ _).mpr hb⟩

/-- For every finite number of independent binary choices, one rational number has
at least that many canonical infinite representations. The equal-mass blocks are
Borwein--Loring's; only finitely many are removed, preserving rationality. -/
theorem erdos_261.variants.arbitrarily_many_representations (r : ℕ) :
    ∃ x : ℚ, (2 : Cardinal) ^ (r : Cardinal) ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  classical
  let x : ℚ := 2 - ∑ i : Fin r, dyadicWeight (blockStart i.val)
  have hex : ∀ bits : Fin r → Bool, ∃ a : ℕ → ℕ,
      Erdos261InfiniteRepresentation x a ∧
      Set.range a = {n : ℕ | 0 < n ∧ n ∉ deletedBlocks r bits} := by
    intro bits
    simpa only [deletedBlocks_sum, x] using finite_deletion_representation (deletedBlocks r bits)
  choose seq hrep hrange using hex
  let f : (Fin r → Bool) → {a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} :=
    fun bits => ⟨seq bits, hrep bits⟩
  have hf : Function.Injective f := by
    intro b c hbc
    have heq : seq b = seq c := congrArg Subtype.val hbc
    have hr : Set.range (seq b) = Set.range (seq c) := congrArg Set.range heq
    rw [hrange b, hrange c] at hr
    funext i
    have hi := Set.ext_iff.mp hr (blockStart i.val)
    simp only [Set.mem_ofPred_eq, blockStart_pos, true_and, deletedBlocks_marker] at hi
    cases hb : b i <;> cases hc : c i <;> simp_all
  refine ⟨x, ?_⟩
  have hc := Cardinal.mk_le_of_injective hf
  simpa only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_fin, Cardinal.lift_natCast,
    Cardinal.lift_ofNat] using hc

/-- An integer scaled remainder is kept strictly between the two tail boundaries. -/
def interiorRemainder (n r : ℕ) : Prop := 0 < r ∧ r < n + 2

/-- Every interior remainder has an interior successor, so finite searches cannot
prove that an interior path eventually dies. This does not assert repeated branching. -/
lemma interiorRemainder_successor {n r : ℕ} (hr : interiorRemainder n r) :
    (interiorRemainder (n + 1) (2 * r)) ∨
    (n + 1 ≤ 2 * r ∧ interiorRemainder (n + 1) (2 * r - (n + 1))) := by
  dsimp [interiorRemainder] at *
  by_cases h : 2 * r < n + 3
  · exact Or.inl ⟨by omega, h⟩
  · exact Or.inr ⟨by omega, by omega, by omega⟩

/-- Both next digits preserve a strictly interior remainder exactly at the
central state. Their successor remainders are `1` and `n+2`. -/
lemma interiorRemainder_branch_iff {n r : ℕ} :
    (interiorRemainder (n + 1) (2 * r) ∧
      n + 1 ≤ 2 * r ∧ interiorRemainder (n + 1) (2 * r - (n + 1))) ↔
      2 * r = n + 2 := by
  dsimp [interiorRemainder]
  omega

lemma interiorRemainder_branch_values {n r : ℕ} (h : 2 * r = n + 2) :
    2 * r - (n + 1) = 1 ∧ 2 * r = n + 2 := by omega

/-- Complementing every digit complements the scaled remainder inside the tail capacity.
This identifies the two central branches but does not prove another central return. -/
lemma interiorRemainder_complement {n r : ℕ} (hr : interiorRemainder n r) :
    interiorRemainder n (n + 2 - r) := by
  dsimp [interiorRemainder] at *
  omega

lemma interiorRemainder_complement_step {n r : ℕ}
    (hr : interiorRemainder n r) (hnext : interiorRemainder (n + 1) (2 * r)) :
    2 * (n + 2 - r) - (n + 1) = n + 3 - 2 * r := by
  dsimp [interiorRemainder] at *
  omega

/-- Canonical representations are determined by their denominator sets, so their
cardinality can never exceed the continuum. -/
theorem erdos_261.variants.representations_le_continuum (x : ℚ) :
    #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} ≤ 𝔠 := by
  let f : {a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} → Set ℕ :=
    fun a => Set.range a.val
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact (a.property.1.range_inj b.property.1).mp hab
  have hc := Cardinal.mk_le_of_injective hf
  simpa only [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0] using hc

#print axioms finite_deletion_representation
#print axioms erdos_261.variants.arbitrarily_many_representations
#print axioms interiorRemainder_successor
#print axioms interiorRemainder_complement
#print axioms interiorRemainder_complement_step
#print axioms interiorRemainder_branch_iff
#print axioms erdos_261.variants.representations_le_continuum

#print axioms erdos_261.variants.borwein_loring
#print axioms erdos_261.variants.borwein_loring_property
#print axioms erdos_261.parts.i
#print axioms erdos_261.variants.two_representations

end Erdos261
