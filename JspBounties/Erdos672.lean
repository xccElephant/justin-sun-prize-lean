import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Erdos672

/-- Predicate asserting that `s : Set α` is the arithmetic progression of length `l`
with first term `a` and common difference `d` (matching `FormalConjectures`). -/
def Set.IsAPOfLengthWith {α : Type*} [AddCommMonoid α] (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- `Erdos672With k l` asserts that the product of `k` terms in an arithmetic progression
$n, n+d, \dots, n+(k-1)d$ with $n > 0, d > 0, \gcd(n, d) = 1$ is never an $l$-th power $q^l$. -/
def Erdos672With (k l : ℕ) : Prop :=
  ∀ (s : Finset ℕ), s.card = k → ∀ (n : ℕ), n > 0 → ∀ (d : ℕ), d > 0 → n.gcd d = 1 →
    Set.IsAPOfLengthWith (s : Set ℕ) k n d → ∀ q, ∏ i ∈ s, i ≠ q ^ l

/-!
## Part 1: Sharpness of the Parameters $k \ge 4$ and $l \ge 3$ (for $k = 3$)

1. For $k = 2$ and every $l \ge 1$, `Erdos672With 2 l` is **false**, witnessed by
   $\{1, 2^l\}$ ($n = 1, d = 2^l - 1, \gcd(1, d) = 1$) whose product is $2^l$.
2. For $k = 3$ and $l = 2$, `Erdos672With 3 2` is **false**:
   - $(n, d) = (1, 24)$ with $\gcd(1, 24) = 1$ gives $1 \cdot 25 \cdot 49 = 1225 = 35^2$.
   - $(n, d) = (18, 7)$ with $\gcd(18, 7) = 1$ gives $18 \cdot 25 \cdot 32 = 14400 = 120^2$.
   This explains both why `erdos_672` requires $k \ge 4$ and why Obláth's theorem
   (`erdos_672.variants.oblath`) for $k = 3$ starts at $l = 3$ ($l \in \{3, 4, 5\}$).
-/

lemma isAPOfLengthWith_two (n d : ℕ) (hd : 0 < d) :
    let s : Finset ℕ := {n, n + d}
    s.card = 2 ∧
    Set.IsAPOfLengthWith (s : Set ℕ) 2 n d ∧
    ∏ i ∈ s, i = n * (n + d) := by
  intro s
  have hmem0 : n ∉ ({n + d} : Finset ℕ) := by simp; omega
  have hcard : s.card = 2 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem hmem0, Finset.card_singleton]
  have hprod : ∏ i ∈ s, i = n * (n + d) := by
    dsimp [s]
    rw [Finset.prod_insert hmem0, Finset.prod_singleton]
  refine ⟨hcard, ⟨?_, ?_⟩, hprod⟩
  · simp [hcard]
  · ext x
    simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_ofPred_eq, nsmul_eq_mul]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, by ring⟩
      · exact ⟨1, by decide, by ring⟩
    · rintro ⟨m, hm, rfl⟩
      have hm' : m < 2 := by exact_mod_cast hm
      rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
      · left; ring
      · right; ring

/-- For every exponent $l \ge 1$, `Erdos672With 2 l` is false: $\{1, 2^l\}$ has product $2^l$. -/
theorem not_erdos672With_two (l : ℕ) (hl : 1 ≤ l) : ¬ Erdos672With 2 l := by
  intro h
  have h2l : 2 ≤ 2 ^ l := by
    calc 2 = 2 ^ 1 := by ring
    _ ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) hl
  have hd : 0 < 2 ^ l - 1 := by omega
  obtain ⟨hcard, hap, hprod⟩ := isAPOfLengthWith_two 1 (2 ^ l - 1) hd
  have hne := h {1, 1 + (2 ^ l - 1)} hcard 1 (by decide) (2 ^ l - 1) hd (Nat.gcd_one_left _) hap 2
  have hprod' : ∏ i ∈ ({1, 1 + (2 ^ l - 1)} : Finset ℕ), i = 2 ^ l := by
    rw [hprod]; omega
  exact hne hprod'

lemma isAPOfLengthWith_three (n d : ℕ) (hd : 0 < d) :
    let s : Finset ℕ := {n, n + d, n + 2 * d}
    s.card = 3 ∧
    Set.IsAPOfLengthWith (s : Set ℕ) 3 n d ∧
    ∏ i ∈ s, i = n * (n + d) * (n + 2 * d) := by
  intro s
  have hmem0 : n ∉ ({n + d, n + 2 * d} : Finset ℕ) := by simp; omega
  have hmem1 : n + d ∉ ({n + 2 * d} : Finset ℕ) := by simp; omega
  have hcard : s.card = 3 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem hmem0, Finset.card_insert_of_notMem hmem1,
      Finset.card_singleton]
  have hprod : ∏ i ∈ s, i = n * (n + d) * (n + 2 * d) := by
    dsimp [s]
    rw [Finset.prod_insert hmem0, Finset.prod_insert hmem1, Finset.prod_singleton]
    ring
  refine ⟨hcard, ⟨?_, ?_⟩, hprod⟩
  · simp [hcard]
  · ext x
    simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_ofPred_eq, nsmul_eq_mul]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by decide, by ring⟩
      · exact ⟨1, by decide, by ring⟩
      · exact ⟨2, by decide, by ring⟩
    · rintro ⟨m, hm, rfl⟩
      have hm' : m < 3 := by exact_mod_cast hm
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
      · left; ring
      · right; left; ring
      · right; right; ring

/-- `Erdos672With 3 2` is false: the $3$-term coprime AP $\{1, 25, 49\}$ ($n=1, d=24$)
has product $1 \cdot 25 \cdot 49 = 35^2$. -/
theorem not_erdos672With_three_two : ¬ Erdos672With 3 2 := by
  intro h
  obtain ⟨hcard, hap, hprod⟩ := isAPOfLengthWith_three 1 24 (by decide)
  have hne := h {1, 1 + 24, 1 + 2 * 24} hcard 1 (by decide) 24 (by decide) (by decide) hap 35
  have hprod' : ∏ i ∈ ({1, 1 + 24, 1 + 2 * 24} : Finset ℕ), i = 35 ^ 2 := by
    rw [hprod]
    decide
  exact hne hprod'

/-- Second counterexample with $n > 1$: $\{18, 25, 32\}$ ($n=18, d=7, \gcd(18,7)=1$)
has product $18 \cdot 25 \cdot 32 = 14400 = 120^2$. -/
theorem three_term_ap_counterexample_two :
    let s : Finset ℕ := {18, 18 + 7, 18 + 2 * 7}
    s.card = 3 ∧ Nat.gcd 18 7 = 1 ∧
    Set.IsAPOfLengthWith (s : Set ℕ) 3 18 7 ∧
    ∏ i ∈ s, i = 120 ^ 2 := by
  obtain ⟨hcard, hap, hprod⟩ := isAPOfLengthWith_three 18 7 (by decide)
  refine ⟨hcard, by decide, hap, ?_⟩
  omega

/-!
## Part 2: Euler's Identity and Impossibility Theorems for $k = 4, l = 2$

Euler observed the identity
$$n(n+d)(n+2d)(n+3d) + d^4 = (n^2 + 3nd + d^2)^2.$$
-/

/-- **Euler's Four-Term AP Identity**:
$n(n+d)(n+2d)(n+3d) + d^4 = (n^2 + 3nd + d^2)^2$. -/
theorem euler_four_ap_identity (n d : ℕ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) + d ^ 4 = (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 := by
  ring

/-- Characterization of a $4$-term arithmetic progression in `Finset ℕ`. -/
lemma prod_eq_of_isAPOfLengthWith_four {s : Finset ℕ} {n d : ℕ} (hd : 0 < d)
    (hap : Set.IsAPOfLengthWith (s : Set ℕ) 4 n d) :
    ∏ i ∈ s, i = n * (n + d) * (n + 2 * d) * (n + 3 * d) := by
  have hs_eq : s = {n, n + d, n + 2 * d, n + 3 * d} := by
    ext x
    have hset := Set.ext_iff.mp hap.2 x
    simp only [Finset.mem_coe, Set.mem_ofPred_eq, nsmul_eq_mul, Finset.mem_insert,
      Finset.mem_singleton] at hset ⊢
    rw [hset]
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm' : m < 4 := by exact_mod_cast hm
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with rfl | rfl | rfl | rfl
      · left; ring
      · right; left; ring
      · right; right; left; ring
      · right; right; right; ring
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by decide, by ring⟩
      · exact ⟨1, by decide, by ring⟩
      · exact ⟨2, by decide, by ring⟩
      · exact ⟨3, by decide, by ring⟩
  rw [hs_eq]
  have hm0 : n ∉ ({n + d, n + 2 * d, n + 3 * d} : Finset ℕ) := by simp; omega
  have hm1 : n + d ∉ ({n + 2 * d, n + 3 * d} : Finset ℕ) := by simp; omega
  have hm2 : n + 2 * d ∉ ({n + 3 * d} : Finset ℕ) := by simp; omega
  rw [Finset.prod_insert hm0, Finset.prod_insert hm1, Finset.prod_insert hm2,
    Finset.prod_singleton]
  ring

/-- **Euler Barrier for $k = 4, l = 2$**:
Whenever $d^4 + 1 < 2(n^2 + 3nd + d^2)$ and $d > 0$, the product $n(n+d)(n+2d)(n+3d)$ is strictly
sandwiched between $(n^2 + 3nd + d^2 - 1)^2$ and $(n^2 + 3nd + d^2)^2$, hence is never a square. -/
theorem erdos_672_four_two_of_d_pow_four_lt {n d : ℕ} (_ : 0 < n) (hd : 0 < d)
    (hbound : d ^ 4 + 1 < 2 * (n ^ 2 + 3 * n * d + d ^ 2)) (q : ℕ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  intro hsq
  let Z := n ^ 2 + 3 * n * d + d ^ 2
  change d ^ 4 + 1 < 2 * Z at hbound
  have hident : q ^ 2 + d ^ 4 = Z ^ 2 := by
    dsimp [Z]
    rw [← hsq]
    exact euler_four_ap_identity n d
  have hd4_pos : 0 < d ^ 4 := by positivity
  have hq_lt_Z : q < Z := by nlinarith
  have hq_le : q ≤ Z - 1 := by omega
  have hsq_le : q ^ 2 ≤ (Z - 1) ^ 2 := Nat.pow_le_pow_left hq_le 2
  have hZ_eq : Z = (Z - 1) + 1 := by omega
  have hZ_sq : Z ^ 2 = (Z - 1) ^ 2 + 2 * (Z - 1) + 1 := by
    calc Z ^ 2 = ((Z - 1) + 1) ^ 2 := by rw [← hZ_eq]
    _ = (Z - 1) ^ 2 + 2 * (Z - 1) + 1 := by ring
  omega

/-- **Corollary ($n \ge d^2$)**: For any $d > 0$ and $n \ge d^2$,
$n(n+d)(n+2d)(n+3d)$ is never a square. -/
theorem erdos_672_four_two_of_sq_le {n d : ℕ} (hd : 0 < d) (hnd : d ^ 2 ≤ n) (q : ℕ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  have hn : 0 < n := by
    have : 0 < d ^ 2 := by positivity
    omega
  apply erdos_672_four_two_of_d_pow_four_lt hn hd
  have hd4 : d ^ 4 = (d ^ 2) ^ 2 := by ring
  have hle : (d ^ 2) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hnd 2
  have hpos : 0 < 3 * n * d + d ^ 2 := by positivity
  omega

/-- **Four Consecutive Positive Integers Are Never a Square** ($k = 4, l = 2, d = 1$):
For every $n > 0$ and $q \in \mathbb{N}$, $n(n+1)(n+2)(n+3) \ne q^2$. -/
theorem four_consecutive_ne_sq {n : ℕ} (hn : 0 < n) (q : ℕ) :
    n * (n + 1) * (n + 2) * (n + 3) ≠ q ^ 2 := by
  have h := erdos_672_four_two_of_sq_le (n := n) (d := 1) (by decide) (by omega) q
  simpa using h

/-- `Erdos672With 4 2` specialized to $d = 1$: no $4$-term AP with difference $1$
has a square product. -/
theorem erdos_672_four_two_d_eq_one (s : Finset ℕ) (_ : s.card = 4) (n : ℕ) (hn : 0 < n)
    (hap : Set.IsAPOfLengthWith (s : Set ℕ) 4 n 1) (q : ℕ) :
    ∏ i ∈ s, i ≠ q ^ 2 := by
  rw [prod_eq_of_isAPOfLengthWith_four (by decide) hap]
  simpa using four_consecutive_ne_sq hn q

/-- The middle two terms $n+d$ and $n+2d$ of a coprime AP are always coprime. -/
theorem coprime_middle_terms {n d : ℕ} (hcop : n.gcd d = 1) :
    (n + d).gcd (n + 2 * d) = 1 := by
  have hc : Nat.Coprime n d := hcop
  have h1 : Nat.Coprime (n + d) d := Nat.coprime_add_self_left.mpr hc
  have h2 : Nat.Coprime (n + d) (d + (n + d)) := Nat.coprime_add_self_right.mpr h1
  have heq : d + (n + d) = n + 2 * d := by ring
  rw [heq] at h2
  exact h2

/-- Any hypothetical counterexample to `Erdos672With 4 2` produces a primitive Pythagorean triple
$(q, d^2, n^2 + 3nd + d^2)$ with $\gcd(q, d) = 1$. -/
theorem erdos_672_four_two_primitive_pythagorean {n d q : ℕ}
    (hcop : n.gcd d = 1)
    (hsq : n * (n + d) * (n + 2 * d) * (n + 3 * d) = q ^ 2) :
    q ^ 2 + (d ^ 2) ^ 2 = (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 ∧ q.gcd d = 1 := by
  refine ⟨?_, ?_⟩
  · calc
      q ^ 2 + (d ^ 2) ^ 2 = n * (n + d) * (n + 2 * d) * (n + 3 * d) + d ^ 4 := by
        rw [hsq]; ring
      _ = (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 := euler_four_ap_identity n d
  · have hc : Nat.Coprime n d := hcop
    have hc1 : Nat.Coprime (n + d) d := Nat.coprime_add_self_left.mpr hc
    have hc2 : Nat.Coprime (n + 2 * d) d := (Nat.coprime_add_mul_right_left n d 2).mpr hc
    have hc3 : Nat.Coprime (n + 3 * d) d := (Nat.coprime_add_mul_right_left n d 3).mpr hc
    have hcop_prod : Nat.Coprime (n * (n + d) * (n + 2 * d) * (n + 3 * d)) d :=
      Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left hc hc1) hc2) hc3
    rw [hsq] at hcop_prod
    exact (Nat.coprime_pow_left_iff (by decide : 0 < 2) q d).mp hcop_prod

#print axioms not_erdos672With_two
#print axioms not_erdos672With_three_two
#print axioms three_term_ap_counterexample_two
#print axioms euler_four_ap_identity
#print axioms erdos_672_four_two_of_d_pow_four_lt
#print axioms erdos_672_four_two_of_sq_le
#print axioms four_consecutive_ne_sq
#print axioms erdos_672_four_two_d_eq_one
#print axioms coprime_middle_terms
#print axioms erdos_672_four_two_primitive_pythagorean

end Erdos672
