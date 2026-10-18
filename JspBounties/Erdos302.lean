/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem 302 (JSP-000253)

*References:*
- [erdosproblems.com/302](https://www.erdosproblems.com/302)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).

Let $f(N)$ be the size of the largest $A\subseteq \{1,\ldots,N\}$ such that there are no
solutions to $\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with distinct $a,b,c\in A$.
In particular, is $f(N) = (\tfrac{1}{2} + o(1))N$?

We prove `erdos_302.variants.lower_half`, construct an explicit triple-free subset of $\{1, \dots, N\}$
of density $17/32 > 1/2$ (all odd integers in $[1, N]$ together with all integers $\equiv 4 \pmod{16}$
in $[N/2 + 1, N]$), and deduce `erdos_302.parts.ii`: $f(N)/N$ does NOT tend to $1/2$.
-/

open Filter Finset
open scoped Topology

namespace Erdos302

/--
A finite set $A$ of positive integers admits no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with $a, b, c$ distinct elements of $A$.
-/
def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

/--
$f N$ is the size of the largest $A \subseteq \{1, \dots, N\}$ containing no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with distinct $a, b, c \in A$.
-/
def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} m

/--
One can take $A$ to be all odd integers in $[1,N]$ to show $f(N)\geq (1/2+o(1))N$.
-/
theorem erdos_302.variants.lower_half (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((1 : ℝ) / 2 - ε) * N ≤ f N := by
  refine Filter.Eventually.of_forall fun N => ?_
  set A : Finset ℕ := (Finset.range ((N + 1) / 2)).image (fun x => 2 * x + 1) with hA
  have hsub : A ⊆ Finset.Icc 1 N := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Icc]
    omega
  have hno : NoUnitFractionTriple A := by
    intro a ha b hb c hc _ _ _ h
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hc
    have hx : ((2 * x + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hy : ((2 * y + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hz : ((2 * z + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp at h
    have h' : (2 * y + 1) * (2 * z + 1) = (2 * x + 1) * (2 * z + 1 + (2 * y + 1)) := by
      exact_mod_cast h
    have := congrArg (· % 2) h'
    simp [Nat.mul_mod, Nat.add_mod] at this
  have hcard : A.card = (N + 1) / 2 := by
    rw [hA, Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy),
      Finset.card_range]
  have hle : (N + 1) / 2 ≤ f N := by
    rw [← hcard]
    exact (hf N).2 ⟨A, hsub, hno, rfl⟩
  have h1 : (N : ℝ) ≤ 2 * ((N + 1) / 2 : ℕ) := by
    exact_mod_cast (by omega : N ≤ 2 * ((N + 1) / 2))
  have h2 : (((N + 1) / 2 : ℕ) : ℝ) ≤ f N := by exact_mod_cast hle
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- Construction of density $17/32$: all $x \in [1, N]$ with $x \equiv 1 \pmod 2$, or
$x \in [N/2 + 1, N]$ with $x \equiv 4 \pmod{16}$. -/
def seventeenThirtySecondsSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => x % 2 = 1 ∨ (N / 2 + 1 ≤ x ∧ x % 16 = 4))

lemma seventeenThirtySecondsSet_subset (N : ℕ) :
    seventeenThirtySecondsSet N ⊆ Finset.Icc 1 N :=
  Finset.filter_subset _ _

lemma seventeenThirtySecondsSet_noUnitFractionTriple (N : ℕ) :
    NoUnitFractionTriple (seventeenThirtySecondsSet N) := by
  intro a ha b hb c hc _ _ _ heq
  simp only [seventeenThirtySecondsSet, Finset.mem_filter, Finset.mem_Icc] at ha hb hc
  obtain ⟨⟨ha1, haN⟩, ha_mod⟩ := ha
  obtain ⟨⟨hb1, hbN⟩, hb_mod⟩ := hb
  obtain ⟨⟨hc1, hcN⟩, hc_mod⟩ := hc
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hmul : (b : ℚ) * c = a * (b + c) := by
    have h1 := heq
    field_simp at h1
    linarith
  have hnat : b * c = a * (b + c) := by exact_mod_cast hmul
  rcases ha_mod with ha_odd | ⟨ha_half, ha16⟩
  · -- Case 1: a is odd
    rcases hb_mod with hb_odd | ⟨_, hb16⟩ <;>
    rcases hc_mod with hc_odd | ⟨_, hc16⟩
    · have := congrArg (· % 2) hnat
      simp [Nat.mul_mod, Nat.add_mod, ha_odd, hb_odd, hc_odd] at this
    · have := congrArg (· % 2) hnat
      have hc2 : c % 2 = 0 := by omega
      simp [Nat.mul_mod, Nat.add_mod, ha_odd, hb_odd, hc2] at this
    · have := congrArg (· % 2) hnat
      have hb2 : b % 2 = 0 := by omega
      simp [Nat.mul_mod, Nat.add_mod, ha_odd, hb2, hc_odd] at this
    · have hmod16 : ((b % 16) * (c % 16)) % 16 = ((a % 16) * ((b % 16 + c % 16) % 16)) % 16 := by
        rw [← Nat.mul_mod, ← Nat.add_mod, ← Nat.mul_mod, hnat]
      rw [hb16, hc16] at hmod16
      omega
  · -- Case 2: a ≥ N / 2 + 1
    have hab_lt : a < b := by nlinarith
    have hac_lt : a < c := by nlinarith
    have h_ident : (b - a) * (c - a) = a * a := by
      zify [le_of_lt hab_lt, le_of_lt hac_lt]
      linarith
    have hba : b - a < a := by
      have h2 : N < (N / 2 + 1) + (N / 2 + 1) := by omega
      have h3 : (N / 2 + 1) + (N / 2 + 1) ≤ a + a := Nat.add_le_add ha_half ha_half
      exact Nat.sub_lt_left_of_lt_add (le_of_lt hab_lt) (lt_of_le_of_lt hbN (lt_of_lt_of_le h2 h3))
    have hca : c - a < a := by
      have h2 : N < (N / 2 + 1) + (N / 2 + 1) := by omega
      have h3 : (N / 2 + 1) + (N / 2 + 1) ≤ a + a := Nat.add_le_add ha_half ha_half
      exact Nat.sub_lt_left_of_lt_add (le_of_lt hac_lt) (lt_of_le_of_lt hcN (lt_of_lt_of_le h2 h3))
    have hlt_sq : (b - a) * (c - a) < a * a := Nat.mul_lt_mul'' hba hca
    omega

lemma seventeenThirtySecondsSet_card_ge (N : ℕ) (hN : 32 ≤ N) :
    17 * (N / 32) - 1 ≤ (seventeenThirtySecondsSet N).card := by
  let Sodd := (Finset.range (16 * (N / 32))).image (fun k => 2 * k + 1)
  let Seven := (Finset.range (N / 32 - 1)).image (fun k => 16 * (N / 32 + 1 + k) + 4)
  have hdisj : Disjoint Sodd Seven := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨k1, _, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨k2, _, h2⟩ := Finset.mem_image.1 hx2
    omega
  have hsub : Sodd ∪ Seven ⊆ seventeenThirtySecondsSet N := by
    intro x hx
    rw [Finset.mem_union] at hx
    simp only [seventeenThirtySecondsSet, Finset.mem_filter, Finset.mem_Icc]
    rcases hx with hx | hx
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_range] at hk
      omega
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_range] at hk
      refine ⟨⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  have hcard : (Sodd ∪ Seven).card = 17 * (N / 32) - 1 := by
    rw [Finset.card_union_of_disjoint hdisj]
    have h1 : Sodd.card = 16 * (N / 32) := by
      rw [Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy),
        Finset.card_range]
    have h2 : Seven.card = N / 32 - 1 := by
      rw [Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy),
        Finset.card_range]
    omega
  rw [← hcard]
  exact Finset.card_le_card hsub

/--
Lower bound $f(N) \ge (17/32 - \varepsilon) N$ for all sufficiently large $N$.
-/
theorem erdos_302.variants.lower_seventeen_thirtyseconds (f : ℕ → ℕ)
    (hf : ∀ N, IsMaxNoTripleCard N (f N)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((17 : ℝ) / 32 - ε) * N ≤ f N := by
  rw [Filter.eventually_atTop]
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (18 / ε)
  refine ⟨max N₀ 32, fun N hN => ?_⟩
  have hle : (seventeenThirtySecondsSet N).card ≤ f N :=
    (hf N).2 ⟨seventeenThirtySecondsSet N, seventeenThirtySecondsSet_subset N,
      seventeenThirtySecondsSet_noUnitFractionTriple N, rfl⟩
  have hcard := seventeenThirtySecondsSet_card_ge N (le_of_max_le_right hN)
  have hbound_nat : 17 * N ≤ 32 * f N + 576 := by omega
  have hbound_real : (17 : ℝ) * N ≤ 32 * (f N : ℝ) + 576 := by exact_mod_cast hbound_nat
  have hN_gt : 18 / ε < (N : ℝ) := by
    have h1 : N₀ ≤ N := le_of_max_le_left hN
    exact lt_of_lt_of_le hN₀ (by exact_mod_cast h1)
  have hεN : 18 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN_gt
  linarith

/--
In particular, is $f(N)=(\tfrac{1}{2}+o(1))N$?
This is false: since $f(N) \ge (17/32 - o(1))N$ and $17/32 > 1/2$, $f(N)/N$ cannot tend to $1/2$.
-/
theorem erdos_302.parts.ii (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    ¬ Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2)) := by
  intro h
  have h_up : ∀ᶠ N : ℕ in atTop, (f N : ℝ) / N < 33 / 64 :=
    h.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 33 / 64))
  have h_low := erdos_302.variants.lower_seventeen_thirtyseconds f hf (1 / 128) (by norm_num)
  obtain ⟨N, hN1, h1, h2⟩ := ((eventually_ge_atTop 1).and (h_up.and h_low)).exists
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN1
  have h1' : (f N : ℝ) < (33 / 64) * N := (div_lt_iff₀ hN_pos).mp h1
  linarith

#print axioms erdos_302.variants.lower_half
#print axioms erdos_302.variants.lower_seventeen_thirtyseconds
#print axioms erdos_302.parts.ii

end Erdos302
