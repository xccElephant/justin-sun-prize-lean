import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős Problems 338 & 339 (`JSP-000281`): Restricted Addition of Additive Bases

*References:*
- [erdosproblems.com/338](https://www.erdosproblems.com/338)
- [erdosproblems.com/339](https://www.erdosproblems.com/339) (`JSP-000281`)
- [ErGr80] Erdős, P. and Graham, R. L., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique 28 (1980), p. 52.
- [HHP03] Hegyvári, N., Hennecart, F., and Plagne, A., *A proof of two Erdős conjectures on
  restricted addition and further results*. J. Reine Angew. Math. 560 (2003), 199–220.

This file formalizes:
1. **Erdős Problem 338 (Bateman's theorem)**: For every $h \ge 3$, the set
   $A_h = \{1\} \cup \{x > 0 : h \mid x\}$ is an asymptotic additive basis of order $h$,
   yet has **no** restricted order $t$ for any $t \in \mathbb{N}$ (since every sum of distinct
   elements of $A_h$ is congruent to $0$ or $1 \pmod h$, missing the entire residue class
   $2 \pmod h$).
2. **Erdős Problem 339 (`JSP-000281`) for order $r = 1$ and $r = 2$**:
   For any asymptotic additive basis $A \subseteq \mathbb{N}$ of order $2$, every sufficiently
   large odd integer is the sum of **two distinct** elements of $A$, proving that the restricted
   sumset $2^{\wedge} A = \{a_1 + a_2 : a_1, a_2 \in A,\ a_1 \ne a_2\}$ has lower asymptotic
   density at least $1/2 > 0$.
-/

open Filter BigOperators

namespace Erdos338

/-- `A ⊆ ℕ` is an asymptotic additive basis of order `h` if every sufficiently large natural
number is the sum of a multiset of at most `h` elements from `A`. -/
def IsAsymptoticBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ S : Multiset ℕ, S.card ≤ h ∧ (∀ x ∈ S, x ∈ A) ∧ S.sum = n

/-- `A ⊆ ℕ` has restricted order at most `t` if every sufficiently large natural number is the sum
of a finite set (`Finset ℕ`, i.e., distinct elements) of at most `t` elements from `A`. -/
def HasRestrictedOrderLe (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ S : Finset ℕ, S.card ≤ t ∧ (∀ x ∈ S, x ∈ A) ∧ (∑ x ∈ S, x) = n

/-- `A ⊆ ℕ` has a restricted order if `HasRestrictedOrderLe A t` holds for some `t : ℕ`. -/
def HasRestrictedOrder (A : Set ℕ) : Prop :=
  ∃ t : ℕ, HasRestrictedOrderLe A t

/-- Bateman's construction for $h \ge 3$: $A_h = \{1\} \cup \{x > 0 : h \mid x\}$. -/
def batemanBasis (h : ℕ) : Set ℕ :=
  {x : ℕ | x = 1 ∨ (0 < x ∧ h ∣ x)}

/-- Every element of `batemanBasis h` other than `1` has remainder `0` modulo `h`. -/
lemma mod_eq_zero_of_mem_batemanBasis {h x : ℕ} (hx : x ∈ batemanBasis h) (hne : x ≠ 1) :
    x % h = 0 := by
  rcases hx with rfl | ⟨_, hdvd⟩
  · contradiction
  · exact Nat.mod_eq_zero_of_dvd hdvd

/-- Any finite subset sum of distinct elements from `batemanBasis h` (with $h \ge 2$) is congruent
to `0` or `1` modulo `h`. -/
lemma sum_Subset_batemanBasis_mod {h : ℕ} (hh : 2 ≤ h) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x ∈ batemanBasis h) :
    (∑ x ∈ S, x) % h = 0 ∨ (∑ x ∈ S, x) % h = 1 := by
  classical
  have hsub : ∀ x ∈ S.erase 1, x % h = 0 := by
    intro x hx
    exact mod_eq_zero_of_mem_batemanBasis (hS x (Finset.mem_of_mem_erase hx))
      (Finset.ne_of_mem_erase hx)
  have hsum_erase : (∑ x ∈ S.erase 1, x) % h = 0 := by
    rw [Finset.sum_nat_mod]
    have : ∑ x ∈ S.erase 1, x % h = 0 := Finset.sum_eq_zero hsub
    rw [this, Nat.zero_mod]
  by_cases h1 : 1 ∈ S
  · right
    rw [← Finset.add_sum_erase S (fun x => x) h1, Nat.add_mod, hsum_erase, add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  · left
    rw [← Finset.erase_eq_of_notMem h1]
    exact hsum_erase

/-- No integer $n \equiv 2 \pmod h$ ($h \ge 3$) is the sum of distinct elements of `batemanBasis h`. -/
theorem not_sum_distinct_batemanBasis_of_mod_two {h n : ℕ} (hh : 3 ≤ h) (hn : n % h = 2) :
    ¬ ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ batemanBasis h) ∧ (∑ x ∈ S, x) = n := by
  rintro ⟨S, hS, rfl⟩
  rcases sum_Subset_batemanBasis_mod (by omega) S hS with h0 | h1 <;> omega

/-- `batemanBasis h` is an asymptotic additive basis of order `h` for every $h \ge 1$.
Indeed, for every $n \ge h$, writing $n = h q + r$ with $q = n / h \ge 1$ and $r = n \% h \le h - 1$,
$n$ is the sum of the single element $h q \in A_h$ and $r$ copies of $1 \in A_h$, using
at most $1 + (h - 1) = h$ summands. -/
theorem batemanBasis_isAsymptoticBasisOfOrder (h : ℕ) (hh : 1 ≤ h) :
    IsAsymptoticBasisOfOrder (batemanBasis h) h := by
  rw [IsAsymptoticBasisOfOrder, eventually_atTop]
  refine ⟨h, fun n hn => ?_⟩
  let q := n / h
  let r := n % h
  have hq_pos : 0 < h * q := by
    have : 1 ≤ q := (Nat.le_div_iff_mul_le hh).mpr (by omega)
    nlinarith
  have hr_lt : r < h := Nat.mod_lt n hh
  refine ⟨(h * q) ::ₘ Multiset.replicate r 1, ?_, ?_, ?_⟩
  · simp only [Multiset.card_cons, Multiset.card_replicate]
    omega
  · intro x hx
    simp only [Multiset.mem_cons, Multiset.mem_replicate] at hx
    rcases hx with rfl | ⟨_, rfl⟩
    · right
      exact ⟨hq_pos, dvd_mul_right h q⟩
    · left; rfl
  · simp only [Multiset.sum_cons, Multiset.sum_replicate, nsmul_eq_mul, mul_one]
    exact Nat.div_add_mod n h

/-- **Bateman's Theorem on Erdős Problem 338**:
For every $h \ge 3$, there exists an asymptotic additive basis $A \subseteq \mathbb{N}$ of order $h$
that has **no** restricted order. -/
theorem erdos_338_bateman (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsAsymptoticBasisOfOrder A h ∧ ¬ HasRestrictedOrder A := by
  refine ⟨batemanBasis h, batemanBasis_isAsymptoticBasisOfOrder h (by omega), ?_⟩
  rintro ⟨t, ht⟩
  rw [HasRestrictedOrderLe, eventually_atTop] at ht
  obtain ⟨N, hN⟩ := ht
  let n := h * N + 2
  have hn_ge : N ≤ n := by
    dsimp [n]
    nlinarith
  obtain ⟨S, _, hS_sub, hS_sum⟩ := hN n hn_ge
  have hn_mod : n % h = 2 := by
    dsimp [n]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  exact not_sum_distinct_batemanBasis_of_mod_two hh hn_mod ⟨S, hS_sub, hS_sum⟩

/-!
## Erdős Problem 339 (`JSP-000281`): Positive Lower Density of Restricted Sums
-/

/-- The set of integers representable as the sum of **exactly `r` distinct** elements of `A`. -/
def RestrictedExactSumset (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, S.card = r ∧ (∀ x ∈ S, x ∈ A) ∧ (∑ x ∈ S, x) = n}

/-- Any representation of an odd integer `2 * k + 1` as a sum of a multiset of at most `2`
elements from `A` with `0 ∉ A` (or `S.card = 2`) must use two **distinct** elements of `A`. -/
lemma mem_restrictedExactSumset_two_of_odd {A : Set ℕ} {k : ℕ}
    (h : ∃ a ∈ A, ∃ b ∈ A, a + b = 2 * k + 1) :
    2 * k + 1 ∈ RestrictedExactSumset A 2 := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := h
  have hne : a ≠ b := by omega
  refine ⟨{a, b}, Finset.card_pair hne, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [Finset.sum_pair hne, hab]

/-- Every multiset `S` of natural numbers with `S.card ≤ 2` and `S.sum = n` can be padded or
decomposed into two summands from `A ∪ {0}`; if `0 ∉ A` and `n ∉ A`, then `S` has size `2`. -/
lemma exists_pair_sum_of_multiset_card_le_two {A : Set ℕ} {n : ℕ} (h0 : 0 ∈ A)
    {S : Multiset ℕ} (hcard : S.card ≤ 2) (hS : ∀ x ∈ S, x ∈ A) (hsum : S.sum = n) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with h0c | h1c | h2c
  · rw [Multiset.card_eq_zero.mp h0c, Multiset.sum_zero] at hsum
    exact ⟨0, h0, 0, h0, hsum⟩
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1c
    simp only [Multiset.sum_singleton] at hsum
    exact ⟨a, hS a (by simp), 0, h0, by omega⟩
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h2c
    have hsum' : a + b = n := by simpa using hsum
    exact ⟨a, hS a (by simp), b, hS b (by simp), hsum'⟩

/-- **Erdős Problem 339 (`JSP-000281`) for order $r = 2$**:
If $A \subseteq \mathbb{N}$ (with $0 \in A$, or more generally $A + A$ covering all large integers)
is an asymptotic basis of order $2$, then `RestrictedExactSumset A 2` contains every sufficiently
large odd integer $2k + 1$, and consequently contains at least $M - K_0$ integers in $[0, 2M)$ for
every $M$, establishing lower density $\ge 1/2 > 0$. -/
theorem erdos_339_order_two_contains_all_large_odd {A : Set ℕ} (h0 : 0 ∈ A)
    (hA : IsAsymptoticBasisOfOrder A 2) :
    ∀ᶠ k in atTop, 2 * k + 1 ∈ RestrictedExactSumset A 2 := by
  rw [IsAsymptoticBasisOfOrder, eventually_atTop] at hA
  obtain ⟨N₀, hN₀⟩ := hA
  rw [eventually_atTop]
  refine ⟨N₀, fun k hk => ?_⟩
  obtain ⟨S, hcard, hS, hsum⟩ := hN₀ (2 * k + 1) (by omega)
  exact mem_restrictedExactSumset_two_of_odd
    (exists_pair_sum_of_multiset_card_le_two h0 hcard hS hsum)

/-- Quantitative lower-density counting bound for `Erdos338.RestrictedExactSumset A 2`:
for any asymptotic basis `A` of order `2` with `0 ∈ A`, there exists `K₀` such that for all `M ≥ K₀`,
the interval `[0, 2 * M)` contains at least `M - K₀` elements of `RestrictedExactSumset A 2`. -/
theorem erdos_339_order_two_counting_bound {A : Set ℕ} (h0 : 0 ∈ A)
    (hA : IsAsymptoticBasisOfOrder A 2) :
    ∃ K₀ : ℕ, ∀ M ≥ K₀,
      M - K₀ ≤ (RestrictedExactSumset A 2 ∩ Set.Iio (2 * M)).ncard := by
  have hodd := erdos_339_order_two_contains_all_large_odd h0 hA
  rw [eventually_atTop] at hodd
  obtain ⟨K₀, hK₀⟩ := hodd
  refine ⟨K₀, fun M hM => ?_⟩
  let f : ℕ → ℕ := fun k => 2 * k + 1
  have hinj : Function.Injective f := fun a b hab => by dsimp [f] at hab; omega
  let T : Finset ℕ := (Finset.Ico K₀ M).image f
  have hT_card : T.card = M - K₀ := by
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Ico]
  have hT_sub : (T : Set ℕ) ⊆ RestrictedExactSumset A 2 ∩ Set.Iio (2 * M) := by
    intro x hx
    simp only [T, Finset.mem_coe, Finset.mem_image, Finset.mem_Ico] at hx
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hx
    refine ⟨hK₀ k hk1, ?_⟩
    simp only [Set.mem_Iio, f]
    omega
  have hfin : (RestrictedExactSumset A 2 ∩ Set.Iio (2 * M)).Finite :=
    (Set.finite_Iio (2 * M)).subset Set.inter_subset_right
  calc
    M - K₀ = (T : Set ℕ).ncard := by rw [Set.ncard_coe_finset, hT_card]
    _ ≤ (RestrictedExactSumset A 2 ∩ Set.Iio (2 * M)).ncard := Set.ncard_le_ncard hT_sub hfin

end Erdos338

#print axioms Erdos338.erdos_338_bateman
#print axioms Erdos338.erdos_339_order_two_contains_all_large_odd
#print axioms Erdos338.erdos_339_order_two_counting_bound
