/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

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

/-!
## Complete four-term square-product repair

Mathematical source: Tamás Erdélyi, “On the equation
`a(a+d)(a+2d)(a+3d)=x²`”, pp. 3–4,
https://people.tamu.edu/~terdelyi/prog_sub.pdf.
The Lean code below was written independently from the paper's mathematical argument;
no external Lean proof was copied. Both descent branches, normalization, and the global well-founded closure prove
`Erdos672With 4 2` below.
The original problem for arbitrary `k ≥ 4` and perfect powers remains broader still.
-/

lemma case2_mod_three (x y z : ZMod 3)
    (h : (2*x^2+y^2)*(x^2+2*y^2)=z^2) (hc : x ≠ 0 ∨ y ≠ 0) :
    x^2=y^2 ∧ z=0 := by
  have H : ∀ x y z : ZMod 3,
      (2*x^2+y^2)*(x^2+2*y^2)=z^2 → (x ≠ 0 ∨ y ≠ 0) → x^2=y^2 ∧ z=0 := by
    decide
  exact H x y z h hc

lemma case2_divisibility {x y z : ℤ} (hc : Int.gcd x y = 1)
    (h : (2*x^2+y^2)*(x^2+2*y^2)=z^2) :
    3 ∣ x^2-y^2 ∧ 3 ∣ z := by
  have hc' : (x : ZMod 3) ≠ 0 ∨ (y : ZMod 3) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hx := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hh.1
    have hy := (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hh.2
    have hg := Int.dvd_coe_gcd hx hy
    rw [hc] at hg
    norm_num at hg
  have hz : (2*(x : ZMod 3)^2+(y : ZMod 3)^2)*
      ((x : ZMod 3)^2+2*(y : ZMod 3)^2) = (z : ZMod 3)^2 := by
    have hh := congrArg (fun z : ℤ => (z : ZMod 3)) h
    push_cast at hh
    exact hh
  obtain ⟨he, hz⟩ := case2_mod_three _ _ _ hz hc'
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    push_cast
    rw [he, sub_self]
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hz

lemma case2_coprime_factors {u v : ℤ} (hc : Int.gcd u v = 1)
    (hp : u % 2 = 0 ∧ v % 2 = 1 ∨ u % 2 = 1 ∧ v % 2 = 0) :
    Int.gcd (u+v) (u-v) = 1 := by
  let g := Int.gcd (u+v) (u-v)
  have hg1 : (g : ℤ) ∣ u+v := Int.gcd_dvd_left _ _
  have hg2 : (g : ℤ) ∣ u-v := Int.gcd_dvd_right _ _
  have hgu : (g : ℤ) ∣ 2*u := by
    have he : (u+v)+(u-v) = 2*u := by ring
    rw [← he]
    exact dvd_add hg1 hg2
  have hgv : (g : ℤ) ∣ 2*v := by
    have he : (u+v)-(u-v) = 2*v := by ring
    rw [← he]
    exact dvd_sub hg1 hg2
  have hg : (g : ℤ) ∣ 2 := by
    have h := Int.dvd_coe_gcd hgu hgv
    rw [Int.gcd_mul_left, hc] at h
    norm_num at h
    exact h
  have hgNat : g ∣ 2 := by exact_mod_cast hg
  have hcases : g = 1 ∨ g = 2 := (Nat.dvd_prime Nat.prime_two).mp hgNat
  rcases hcases with hg | hg
  · exact hg
  · have hh : 2 ∣ u+v := by simpa [hg] using hg1
    have hh' := Int.emod_eq_zero_of_dvd hh
    rw [Int.add_emod] at hh'
    rcases hp with ⟨hu,hv⟩ | ⟨hu,hv⟩ <;> simp [hu,hv] at hh'
-- The odd-leg descent in Erdélyi's proof. All arithmetic here is integral.
theorem odd_leg_descent_algebra {a d u v x y : ℤ}
    (ha : 0 < a) (hd : 0 < d) (hv : 0 < v)
    (hz : a ^ 2 + 3 * a * d + d ^ 2 = u ^ 2 + v ^ 2)
    (hd2 : d ^ 2 = u ^ 2 - v ^ 2)
    (hx : u + v = x ^ 2) (hy : u - v = y ^ 2)
    (hdiv : 3 ∣ x^2-y^2) (hQdiv : 3 ∣ 2*a+3*d) :
    ∃ A D Q : ℤ, 0 < A ∧ 0 < D ∧
      A * (A + D) * (A + 2 * D) * (A + 3 * D) = Q ^ 2 ∧
      (A + D) * (A + 2 * D) < (a + d) * (a + 2 * d) := by
  have hxy : x ^ 2 * y ^ 2 = d ^ 2 := by
    rw [← hx, ← hy]
    nlinarith only [hd2]
  have hypos : 0 < y ^ 2 := by
    have hdp : 0 < d ^ 2 := sq_pos_of_pos hd
    nlinarith only [hxy, hdp, sq_nonneg y, sq_nonneg x]
  have hdisc : (2*x^2+y^2)*(x^2+2*y^2) = (2*a+3*d)^2 := by
    rw [← hx, ← hy]
    linear_combination -4*hz - 5*hd2
  let D := (x^2-y^2)/3
  have hD : 3 * D = x^2-y^2 := Int.mul_ediv_cancel' hdiv
  have hDpos : 0 < D := by linarith only [hx, hy, hD, hv]

  have hQ : 3 * ((2*a+3*d)/3) = 2*a+3*d := Int.mul_ediv_cancel' hQdiv
  have hB : 3*(y^2+D) = x^2+2*y^2 := by linarith
  have hC : 3*(y^2+2*D) = 2*x^2+y^2 := by linarith
  have hE : y^2+3*D = x^2 := by linarith
  have hmid : (y^2+D)*(y^2+2*D) = ((2*a+3*d)/3)^2 := by
    apply (mul_left_inj' (by norm_num : (9 : ℤ) ≠ 0)).mp
    linear_combination hdisc - ((2*a+3*d)+3*((2*a+3*d)/3))*hQ +
      (2*x^2+y^2)*hB + 3*(y^2+D)*hC
  have hless : (y^2+D)*(y^2+2*D) < (a+d)*(a+2*d) := by
    rw [hmid]
    have hQs : 9*((2*a+3*d)/3)^2 = (2*a+3*d)^2 := by
      linear_combination (3*((2*a+3*d)/3)+(2*a+3*d))*hQ
    have had : 0 < a*d := mul_pos ha hd
    nlinarith only [hQs, sq_pos_of_pos ha, sq_pos_of_pos hd, had]
  refine ⟨y^2,D,x*y*((2*a+3*d)/3),hypos,hDpos,?_,hless⟩
  rw [hE]
  calc
    y^2*(y^2+D)*(y^2+2*D)*x^2 =
        x^2*y^2*((y^2+D)*(y^2+2*D)) := by ring
    _ = (x*y*((2*a+3*d)/3))^2 := by rw [hmid]; ring


/-- Erdélyi Case 2: primitive odd-leg parameters produce a smaller positive AP
with square product. No size bound on the original AP is used. -/
theorem erdos_672_four_two_case2_descent {a d u v : ℤ}
    (ha : 0 < a) (hd : 0 < d) (hu0 : 0 ≤ u) (hv : 0 < v)
    (hz : a^2+3*a*d+d^2=u^2+v^2) (hd2 : d^2=u^2-v^2)
    (hc : Int.gcd u v = 1)
    (hp : u % 2 = 0 ∧ v % 2 = 1 ∨ u % 2 = 1 ∧ v % 2 = 0) :
    ∃ A D Q : ℤ, 0 < A ∧ 0 < D ∧
      A*(A+D)*(A+2*D)*(A+3*D)=Q^2 ∧
      (A+D)*(A+2*D)<(a+d)*(a+2*d) := by
  have hcf := case2_coprime_factors hc hp
  have hprod : (u+v)*(u-v)=d^2 := by nlinarith only [hd2]
  have hu : 0 < u+v := by
    linarith only [hu0,hv]
  have huv : 0 < u-v := by
    nlinarith only [hprod,hu,sq_pos_of_pos hd]
  obtain ⟨x,hx⟩ := Int.sq_of_gcd_eq_one hcf hprod
  have hx' : u+v=x^2 := by
    rcases hx with hx | hx
    · exact hx
    · nlinarith only [hx,hu,sq_nonneg x]
  obtain ⟨y,hy⟩ := Int.sq_of_gcd_eq_one (by rwa [Int.gcd_comm]) (by rwa [mul_comm] at hprod)
  have hy' : u-v=y^2 := by
    rcases hy with hy | hy
    · exact hy
    · nlinarith only [hy,huv,sq_nonneg y]
  have hcxy : Int.gcd x y = 1 := by
    have hcp : IsCoprime (x^2) (y^2) := by
      rw [← hx',← hy']
      exact Int.isCoprime_iff_gcd_eq_one.mpr hcf
    exact Int.isCoprime_iff_gcd_eq_one.mp
      ((IsCoprime.pow_left_iff (by decide : 0 < 2)).mp
        ((IsCoprime.pow_right_iff (by decide : 0 < 2)).mp hcp))
  have hdisc : (2*x^2+y^2)*(x^2+2*y^2)=(2*a+3*d)^2 := by
    rw [← hx',← hy']
    linear_combination -4*hz-5*hd2
  obtain ⟨hdiv,hQdiv⟩ := case2_divisibility hcxy hdisc
  exact odd_leg_descent_algebra ha hd hv hz hd2 hx' hy' hdiv hQdiv

/-- Reverse the four positive terms when the conic parameters give negative difference. -/
lemma positive_ap_orientation {a b Q : ℤ} (_ha : 0 < a) (_hb : 0 < b)
    (hL : 0 < 2*a-b) (hR : 0 < 2*b-a) (hne : a ≠ b)
    (hprod : (2*a-b)*a*b*(2*b-a)=Q^2) :
    ∃ A D : ℤ, 0 < A ∧ 0 < D ∧
      A*(A+D)*(A+2*D)*(A+3*D)=Q^2 ∧ (A+D)*(A+2*D)=a*b := by
  rcases lt_or_gt_of_ne hne with hab | hab
  · refine ⟨2*a-b,b-a,hL,by omega,?_,?_⟩
    · convert hprod using 1
      ring
    · ring
  · refine ⟨2*b-a,a-b,hR,by omega,?_,?_⟩
    · calc
        _ = (2*a-b)*a*b*(2*b-a) := by ring
        _ = Q^2 := hprod
    · ring

/-- The two quadratic numerators in the Eisenstein conic parametrization
have no common factor other than a divisor of 3. -/
lemma eisenstein_numerators_gcd {a b : ℤ} (hc : Int.gcd a b = 1) :
    (Int.gcd (b*(2*a-b)) (a*(2*b-a)) : ℤ) ∣ 3 := by
  let g := Int.gcd (b*(2*a-b)) (a*(2*b-a))
  have hF : (g : ℤ) ∣ b*(2*a-b) := Int.gcd_dvd_left _ _
  have hG : (g : ℤ) ∣ a*(2*b-a) := Int.gcd_dvd_right _ _
  have hcp : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hc
  have hfa : IsCoprime (b*(2*a-b)) a := by
    have hh : IsCoprime (-b^2+2*b*a) a := hcp.symm.pow_left.neg_left.add_mul_right_left (2*b)
    convert hh using 1
    ring
  have hgbb : IsCoprime (a*(2*b-a)) b := by
    have hh : IsCoprime (-a^2+2*a*b) b := hcp.pow_left.neg_left.add_mul_right_left (2*a)
    convert hh using 1
    ring
  have hga : IsCoprime (g : ℤ) a := hfa.of_isCoprime_of_dvd_left hF
  have hgb : IsCoprime (g : ℤ) b := hgbb.of_isCoprime_of_dvd_left hG
  have hL : (g : ℤ) ∣ 2*a-b := hgb.dvd_of_dvd_mul_left hF
  have hR : (g : ℤ) ∣ 2*b-a := hga.dvd_of_dvd_mul_left hG
  have h3a : (g : ℤ) ∣ 3*a := by
    have he : 2*(2*a-b)+(2*b-a)=3*a := by ring
    rw [← he]
    exact dvd_add (dvd_mul_of_dvd_right hL 2) hR
  exact hga.dvd_of_dvd_mul_right h3a


/-- A positive integral parametrization with scale bounded by 3.
The scale bound is the arithmetic input needed for strict descent. -/
theorem eisenstein_conic_parameterization {x y z : ℤ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hc : Int.gcd x y = 1) (he : x^2+y^2-x*y=z^2) :
    ∃ a b k : ℤ, 0 < a ∧ 0 < b ∧ 0 < k ∧ k ≤ 3 ∧
      b*(2*a-b)=k*x ∧ a*(2*b-a)=k*y ∧ Int.gcd a b = 1 := by
  have hg : 0 < Int.gcd (x+z) (y+z) := by
    apply Nat.pos_of_ne_zero
    intro hh
    obtain ⟨hh1,hh2⟩ := Int.gcd_eq_zero_iff.mp hh
    linarith
  obtain ⟨g,a,b,hgpos,hab,hxa,hyb⟩ := Int.exists_gcd_one' hg
  have hgI : 0 < (g : ℤ) := by exact_mod_cast hgpos
  have ha : 0 < a := by nlinarith only [hxa,hx,hz,hgI]
  have hb : 0 < b := by nlinarith only [hyb,hy,hz,hgI]
  have hL : a*(y+z)=b*(x+z) := by rw [hxa,hyb]; ring
  have hE : x*(a*(2*b-a))=y*(b*(2*a-b)) := by
    apply (mul_left_inj' (sq_pos_of_pos (show 0 < y+z by linarith)).ne').mp
    linear_combination
      -b^2*(x-y)*he +
      (-x*(a*(y+z)+b*(x+z))+2*b*(x-y)*(y+z))*hL
  have hcp : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hc
  have hxF : x ∣ b*(2*a-b) := hcp.dvd_of_dvd_mul_left (by rw [← hE]; exact dvd_mul_right _ _)
  obtain ⟨k,hk⟩ := hxF
  have hG : a*(2*b-a)=k*y := by
    apply (mul_left_inj' hx.ne').mp
    linear_combination hE + y*hk
  have hsum : b*(2*a-b)+a*(2*b-a)=4*a*b-a^2-b^2 := by ring
  have hlow : 0 < 4*a*b-a^2-b^2 := by
    have hN : (g:ℤ)^2*(4*a*b-a^2-b^2)=3*x*y+2*z*(x+y)+z^2 := by
      linear_combination
        -(4*b*(g:ℤ)-a*(g:ℤ)-(x+z))*hxa -
        (4*(x+z)-b*(g:ℤ)-(y+z))*hyb - he
    have hxy : 0 < x*y := mul_pos hx hy
    have hzxy : 0 < z*(x+y) := mul_pos hz (by linarith)
    have hg2 : 0 < (g:ℤ)^2 := sq_pos_of_pos hgI
    nlinarith only [hN,hxy,hzxy,hg2,sq_nonneg z]
  have hkpos : 0 < k := by nlinarith only [hsum,hlow,hk,hG,hx,hy]
  have hkg : (Int.gcd (b*(2*a-b)) (a*(2*b-a)) : ℤ) = k := by
    rw [hk,hG,mul_comm x k,Int.gcd_mul_left,hc]
    simp only [mul_one]
    exact Int.natCast_natAbs k |>.trans (abs_of_pos hkpos)
  have hk3 : k ∣ 3 := by rw [← hkg]; exact eisenstein_numerators_gcd hab
  refine ⟨a,b,k,ha,hb,hkpos,?_,?_,hG,hab⟩
  · exact Int.le_of_dvd (by norm_num) hk3
  · rw [hk]; ring


theorem case1_conic_descent {n d r s e w : ℤ}
    (hn : 0 < n) (hd : 0 < d) (hr : 0 < r) (hs : 0 < s)
    (hc : Int.gcd r s = 1) (hne : r^2 ≠ s^2)
    (he : (r^2)^2+(s^2)^2-r^2*s^2=e^2) (hepos : 0 < e)
    (hw : r*s=w) (hbound : 4*w^2 ≤ d^2) :
    ∃ A D Q : ℤ, 0 < A ∧ 0 < D ∧
      A*(A+D)*(A+2*D)*(A+3*D)=Q^2 ∧
      (A+D)*(A+2*D)<(n+d)*(n+2*d) := by
  have hc2 : Int.gcd (r^2) (s^2) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_iff_gcd_eq_one.mpr hc).pow
  obtain ⟨a,b,k,ha,hb,hk,hk3,hF,hG,hab⟩ :=
    eisenstein_conic_parameterization (sq_pos_of_pos hr) (sq_pos_of_pos hs) hepos hc2 he
  have hL : 0 < 2*a-b := by
    have : 0 < k*r^2 := mul_pos hk (sq_pos_of_pos hr)
    nlinarith only [hF,this,hb]
  have hR : 0 < 2*b-a := by
    have : 0 < k*s^2 := mul_pos hk (sq_pos_of_pos hs)
    nlinarith only [hG,this,ha]
  have habne : a ≠ b := by
    intro hh
    have hkk := hk.ne'
    apply hne
    apply (mul_left_inj' hkk).mp
    linear_combination -hF+hG+(a+b)*hh
  have hprod : (2*a-b)*a*b*(2*b-a)=(k*r*s)^2 := by
    calc
      _ = (b*(2*a-b))*(a*(2*b-a)) := by ring
      _ = _ := by rw [hF,hG]; ring
  obtain ⟨A,D,hA,hD,hAP,hmid⟩ := positive_ap_orientation ha hb hL hR habne hprod
  refine ⟨A,D,k*r*s,hA,hD,hAP,?_⟩
  rw [hmid]
  have hends : 3 ≤ (2*a-b)*(2*b-a) := by
    by_contra hh
    have hLL : 1 ≤ 2*a-b := by omega
    have hRR : 1 ≤ 2*b-a := by omega
    have hLle : 2*a-b ≤ 2 := by nlinarith only [hh,hLL,hRR]
    have hRle : 2*b-a ≤ 2 := by nlinarith only [hh,hLL,hRR]
    have hLc : 2*a-b=1 ∨ 2*a-b=2 := by omega
    have hRc : 2*b-a=1 ∨ 2*b-a=2 := by omega
    rcases hLc with hLc | hLc <;> rcases hRc with hRc | hRc <;> omega
  have hsmall : 3*(a*b) ≤ (k*r*s)^2 := by
    have heq : (a*b)*((2*a-b)*(2*b-a))=(k*r*s)^2 := by
      calc _ = (2*a-b)*a*b*(2*b-a) := by ring
           _ = _ := hprod
    nlinarith only [heq,hends,mul_pos ha hb]
  have hscale4 : 4*(k*r*s)^2 ≤ 9*d^2 := by
    have hkSq : k^2 ≤ 9 := by nlinarith only [hk,hk3]
    have heq : 4*(k*r*s)^2 = k^2*(4*w^2) := by rw [← hw]; ring
    calc
      4*(k*r*s)^2 = k^2*(4*w^2) := heq
      _ ≤ 9*(4*w^2) := mul_le_mul_of_nonneg_right hkSq (by positivity)
      _ ≤ 9*d^2 := by linarith only [hbound]
  have hnd : 0 < n*d := mul_pos hn hd
  nlinarith only [hsmall,hscale4,sq_pos_of_pos hd,sq_pos_of_pos hn,hnd]

lemma positive_square_factor {a b c : ℤ} (ha : 0 < a)
    (hc : Int.gcd a b = 1) (he : a*b=c^2) : ∃ r : ℤ, 0 < r ∧ a=r^2 := by
  obtain ⟨r,hr⟩ := Int.sq_of_gcd_eq_one hc he
  have hr' : a=r^2 := by
    rcases hr with hr | hr
    · exact hr
    · nlinarith only [hr,ha,sq_nonneg r]
  refine ⟨|r|,?_,?_⟩
  · have : r ≠ 0 := by intro hh; simp [hh] at hr'; omega
    exact abs_pos.mpr this
  · simpa using hr'

lemma squares_three_mod (a b : ZMod 3) (h : a^2+b^2=0) : a=0 ∧ b=0 := by
  have hh : ∀ a b : ZMod 3, a^2+b^2=0 → a=0 ∧ b=0 := by decide
  exact hh a b h

lemma case1_coprime_sums {r s : ℤ} (hc : Int.gcd r s = 1) :
    Int.gcd (r^2+s^2) (4*r^2+s^2) = 1 := by
  let g := Int.gcd (r^2+s^2) (4*r^2+s^2)
  have h1 : (g : ℤ) ∣ r^2+s^2 := Int.gcd_dvd_left _ _
  have h2 : (g : ℤ) ∣ 4*r^2+s^2 := Int.gcd_dvd_right _ _
  have hgr : IsCoprime (g : ℤ) (r^2) := by
    have hh := Int.isCoprime_of_sq_sum (Int.isCoprime_iff_gcd_eq_one.mpr hc).symm
    exact (hh.pow_right).of_isCoprime_of_dvd_left h1
  have h3r : (g : ℤ) ∣ 3*r^2 := by
    have he : (4*r^2+s^2)-(r^2+s^2)=3*r^2 := by ring
    rw [← he]
    exact dvd_sub h2 h1
  have hg3 : (g : ℤ) ∣ 3 := hgr.dvd_of_dvd_mul_right h3r
  have hgN : g ∣ 3 := by exact_mod_cast hg3
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hgN with hg | hg
  · exact hg
  · have hsum : (r : ZMod 3)^2+(s : ZMod 3)^2=0 := by
      have hdiv : (3:ℤ) ∣ r^2+s^2 := by simpa [hg] using h1
      have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdiv
      push_cast at hh
      exact hh
    obtain ⟨hr,hs⟩ := squares_three_mod _ _ hsum
    have hrd := (ZMod.intCast_zmod_eq_zero_iff_dvd r 3).mp hr
    have hsd := (ZMod.intCast_zmod_eq_zero_iff_dvd s 3).mp hs
    have hgd := Int.dvd_coe_gcd hrd hsd
    rw [hc] at hgd
    norm_num at hgd


lemma primitive_even_square_leg_ordered {u v d : ℤ} (hu : 0 < u) (hv : 0 < v)
    (hc : Int.gcd u v = 1) (hd : d^2=2*u*v) (hue : u % 2 = 0) (hvo : v % 2 = 1) :
    ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ Int.gcd r s = 1 ∧ s % 2 = 1 ∧
      u=2*r^2 ∧ v=s^2 ∧ d^2=4*r^2*s^2 := by
  obtain ⟨U,hU⟩ := Int.dvd_of_emod_eq_zero hue
  have hUpos : 0 < U := by omega
  have hD : (2:ℤ) ∣ d := by
    apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
    rw [hd, mul_assoc]
    exact dvd_mul_right (2 : ℤ) (u*v)
  obtain ⟨D,hD⟩ := hD
  have hUD : U*v=D^2 := by
    rw [hU,hD] at hd
    nlinarith only [hd]
  have hcp : IsCoprime U v := by
    apply (Int.isCoprime_iff_gcd_eq_one.mpr hc).of_isCoprime_of_dvd_left
    exact ⟨2,by linarith⟩
  obtain ⟨r,hr,hrEq⟩ := positive_square_factor hUpos (Int.isCoprime_iff_gcd_eq_one.mp hcp) hUD
  obtain ⟨s,hs,hsEq⟩ := positive_square_factor hv (Int.isCoprime_iff_gcd_eq_one.mp hcp.symm) (by rwa [mul_comm])
  have hroots : Int.gcd r s = 1 := by
    rw [hrEq,hsEq] at hcp
    exact Int.isCoprime_iff_gcd_eq_one.mp
      ((IsCoprime.pow_left_iff (by decide : 0 < 2)).mp
        ((IsCoprime.pow_right_iff (by decide : 0 < 2)).mp hcp))
  have hso : s % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one s with hh | hh
    · rw [hsEq,sq,Int.mul_emod,hh] at hvo
      norm_num at hvo
    · exact hh
  refine ⟨r,s,hr,hs,hroots,hso,?_,hsEq,?_⟩
  · rw [hU,hrEq]
  · rw [hd,hU,hrEq,hsEq]; ring

lemma primitive_even_square_leg {u v d : ℤ} (hu : 0 < u) (hv : 0 < v)
    (hc : Int.gcd u v = 1) (hd : d^2=2*u*v)
    (hp : u % 2 = 0 ∧ v % 2 = 1 ∨ u % 2 = 1 ∧ v % 2 = 0) :
    ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ Int.gcd r s = 1 ∧ s % 2 = 1 ∧
      (u=2*r^2 ∧ v=s^2 ∨ v=2*r^2 ∧ u=s^2) ∧ d^2=4*r^2*s^2 := by
  rcases hp with ⟨hue,hvo⟩ | ⟨huo,hve⟩
  · obtain ⟨r,s,hr,hs,hc,ho,hu,hv,hd⟩ := primitive_even_square_leg_ordered hu hv hc hd hue hvo
    exact ⟨r,s,hr,hs,hc,ho,Or.inl ⟨hu,hv⟩,hd⟩
  · obtain ⟨r,s,hr,hs,hc,ho,hv,hu,hd⟩ :=
      primitive_even_square_leg_ordered hv hu (by rwa [Int.gcd_comm]) (by nlinarith only [hd]) hve huo
    exact ⟨r,s,hr,hs,hc,ho,Or.inr ⟨hv,hu⟩,hd⟩

lemma double_triangle_conic {n d r s E F : ℤ}
    (_hn : 0 < n) (_hd : 0 < d) (hr : 0 < r) (hs : 0 < s)
    (hc : Int.gcd r s = 1) (hso : s % 2 = 1)
    (hE : r^2+s^2=E^2) (hEp : 0 < E)
    (hF : (2*r)^2+s^2=F^2) (hFp : 0 < F)
    (hd2 : d^2=4*r^2*s^2) :
    ∃ R S Z W : ℤ, 0 < R ∧ 0 < S ∧ Int.gcd R S = 1 ∧
      R^2 ≠ S^2 ∧ (R^2)^2+(S^2)^2-R^2*S^2=Z^2 ∧ 0 < Z ∧
      R*S=W ∧ 4*W^2 ≤ d^2 := by
  have hpE : PythagoreanTriple s r E := by
    unfold PythagoreanTriple
    nlinarith only [hE]
  have hcE : Int.gcd s r = 1 := by rwa [Int.gcd_comm]
  obtain ⟨m,l,hsm,hrm,hEm,hcml,hpar,hmp⟩ := hpE.coprime_classification' hcE hso hEp
  have hmpos : 0 < m := by
    by_contra hh
    have hm0 : m=0 := by omega
    rw [hm0] at hrm
    norm_num at hrm
    omega
  have hlpos : 0 < l := by nlinarith only [hrm,hr,hmpos]
  have hcs2r : Int.gcd s (2*r) = 1 := by
    have hcp : IsCoprime s r := Int.isCoprime_iff_gcd_eq_one.mpr hcE
    have hs2 : IsCoprime s (2:ℤ) := by
      have h : Int.gcd s 2 = 1 := by
        have hg2 : Int.gcd s 2 ∣ 2 := by
          have hh := Int.gcd_dvd_right s 2
          exact_mod_cast hh
        rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with hh | hh
        · exact hh
        · have hsD : (2:ℤ) ∣ s := by
            have h := Int.gcd_dvd_left s 2
            simpa [hh] using h
          have hsZ := Int.emod_eq_zero_of_dvd hsD
          omega
      exact Int.isCoprime_iff_gcd_eq_one.mpr h
    exact Int.isCoprime_iff_gcd_eq_one.mp (hs2.mul_right hcp)
  have hpF : PythagoreanTriple s (2*r) F := by
    unfold PythagoreanTriple
    nlinarith only [hF]
  obtain ⟨R,S,hsR,hrR,hFR,hcRS,hparRS,hRp⟩ := hpF.coprime_classification' hcs2r hso hFp
  have hRpos : 0 < R := by
    by_contra hh
    have hR0 : R=0 := by omega
    rw [hR0] at hrR
    norm_num at hrR
    omega
  have hSpos : 0 < S := by nlinarith only [hrR,hr,hRpos]
  refine ⟨R,S,m^2+l^2,r,hRpos,hSpos,hcRS,?_,?_,?_,?_,?_⟩
  · intro hh
    rw [hh] at hsR
    omega
  · have hRS : R*S=r := by nlinarith only [hrR]
    have hml : 2*m*l=r := by linarith only [hrm]
    have hsquares : R^2-S^2=m^2-l^2 := by linarith only [hsR,hsm]
    have hRSsq : (R*S)^2=r^2 := by rw [hRS]
    have hmlsq : (2*m*l)^2=r^2 := by rw [hml]
    nlinarith only [hsquares,hRSsq,hmlsq]
  · positivity
  · nlinarith only [hrR]
  · have hs1 : 1 ≤ s^2 := by nlinarith only [sq_pos_of_pos hs]
    nlinarith only [hd2,hs1,sq_nonneg r]

lemma even_leg_discriminant {n d u v r s : ℤ}
    (hz : n^2+3*n*d+d^2=u^2+v^2) (_hd2 : d^2=2*u*v)
    (huv : u=2*r^2 ∧ v=s^2 ∨ v=2*r^2 ∧ u=s^2)
    (hd4 : d^2=4*r^2*s^2) :
    ∃ c : ℤ, (r^2+s^2)*(4*r^2+s^2)=c^2 := by
  have hdEven : (2:ℤ) ∣ d := by
    apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
    rw [hd4]
    exact ⟨2*r^2*s^2,by ring⟩
  obtain ⟨D,hD⟩ := hdEven
  refine ⟨n+3*D,?_⟩
  rcases huv with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;>
    rw [hu,hv,hD] at hz <;> rw [hD] at hd4 <;>
    nlinarith only [hz,hd4]

/-- The complete even-leg branch of Erdélyi's descent. -/
theorem erdos_672_four_two_case1_descent {n d u v : ℤ}
    (hn : 0 < n) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v)
    (hc : Int.gcd u v = 1)
    (hp : u % 2 = 0 ∧ v % 2 = 1 ∨ u % 2 = 1 ∧ v % 2 = 0)
    (hz : n^2+3*n*d+d^2=u^2+v^2) (hd2 : d^2=2*u*v) :
    ∃ A D Q : ℤ, 0 < A ∧ 0 < D ∧
      A*(A+D)*(A+2*D)*(A+3*D)=Q^2 ∧
      (A+D)*(A+2*D)<(n+d)*(n+2*d) := by
  obtain ⟨r,s,hr,hs,hcrs,hso,huv,hd4⟩ := primitive_even_square_leg hu hv hc hd2 hp
  obtain ⟨c,hcprod⟩ := even_leg_discriminant hz hd2 huv hd4
  have hcg := case1_coprime_sums hcrs
  obtain ⟨E,hEp,hE⟩ := positive_square_factor (by positivity) hcg hcprod
  obtain ⟨F,hFp,hF⟩ := positive_square_factor (a := 4*r^2+s^2) (b := r^2+s^2) (c := c)
    (by positivity) (by rwa [Int.gcd_comm]) (by rwa [mul_comm])
  have hF' : (2*r)^2+s^2=F^2 := by nlinarith only [hF]
  obtain ⟨R,S,Z,W,hR,hS,hcRS,hne,hconic,hZ,hW,hbound⟩ :=
    double_triangle_conic hn hd hr hs hcrs hso hE hEp hF' hFp hd4
  exact case1_conic_descent hn hd hR hS hcRS hne hconic hZ hW hbound

/-- Every primitive square-product counterexample yields a smaller positive
square-product AP, without a coprimality requirement on the output. -/
theorem primitive_four_ap_descent {a d q : ℤ}
    (ha : 0 < a) (hd : 0 < d) (hc : Int.gcd a d = 1)
    (hsq : a*(a+d)*(a+2*d)*(a+3*d)=q^2) :
    ∃ A D Q : ℤ, 0 < A ∧ 0 < D ∧
      A*(A+D)*(A+2*D)*(A+3*D)=Q^2 ∧
      (A+D)*(A+2*D)<(a+d)*(a+2*d) := by
  have hcp : IsCoprime a d := Int.isCoprime_iff_gcd_eq_one.mpr hc
  have hcp1 : IsCoprime (a+d) d := by
    simpa using hcp.add_mul_right_left 1
  have hcp2 : IsCoprime (a+2*d) d := hcp.add_mul_right_left 2
  have hcp3 : IsCoprime (a+3*d) d := hcp.add_mul_right_left 3
  have hprod := ((hcp.mul_left hcp1).mul_left hcp2).mul_left hcp3
  rw [hsq] at hprod
  have hqd : IsCoprime q d := (IsCoprime.pow_left_iff (by decide : 0 < 2)).mp hprod
  have hqd2 : Int.gcd q (d^2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hqd.pow_right
  have hZ : 0 < a^2+3*a*d+d^2 := by positivity
  have hpy : PythagoreanTriple q (d^2) (a^2+3*a*d+d^2) := by
    unfold PythagoreanTriple
    linear_combination -hsq
  obtain ⟨u,v,hlegs,hyp,hcuv,hpar⟩ :=
    PythagoreanTriple.coprime_classification.mp ⟨hpy,hqd2⟩
  have hyp' : a^2+3*a*d+d^2=u^2+v^2 := by
    rcases hyp with hyp | hyp
    · exact hyp
    · nlinarith only [hyp,hZ,sq_nonneg u,sq_nonneg v]
  let U := |u|
  let V := |v|
  have hUsq : U^2=u^2 := sq_abs u
  have hVsq : V^2=v^2 := sq_abs v
  have hcUV : Int.gcd U V = 1 := by simpa [U,V,Int.gcd_eq_natAbs,Int.natAbs_abs] using hcuv
  have hpUV : U % 2 = 0 ∧ V % 2 = 1 ∨ U % 2 = 1 ∧ V % 2 = 0 := by
    have hmod : ∀ t : ℤ, |t| % 2 = t % 2 := by
      intro t
      by_cases ht : 0 ≤ t
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg (by omega),Int.neg_emod_two]
    simpa [U,V,hmod] using hpar
  rcases hlegs with ⟨hq,hdiff⟩ | ⟨hq,heven⟩
  · have hEV : d^2=2*U*V := by
      change d^2 = 2 * |u| * |v|
      have hh := congrArg abs hdiff
      simpa [abs_mul,abs_of_nonneg (sq_nonneg d)] using hh
    have hUp : 0 < U := by
      have hUn : 0 ≤ U := abs_nonneg u
      have hVn : 0 ≤ V := abs_nonneg v
      nlinarith only [hEV,sq_pos_of_pos hd,hUn,hVn]
    have hVp : 0 < V := by
      have hUn : 0 ≤ U := abs_nonneg u
      have hVn : 0 ≤ V := abs_nonneg v
      nlinarith only [hEV,sq_pos_of_pos hd,hUn,hVn]
    exact erdos_672_four_two_case1_descent ha hd hUp hVp hcUV hpUV
      (by nlinarith only [hyp',hUsq,hVsq]) hEV
  · have hD : d^2=U^2-V^2 := by nlinarith only [heven,hUsq,hVsq]
    have hVp : 0 < V := by
      have hq0 : q ≠ 0 := by
        intro hh
        rw [hh] at hsq
        have hpositive : 0 < a*(a+d)*(a+2*d)*(a+3*d) := by positivity
        nlinarith only [hsq,hpositive]
      have hv0 : v ≠ 0 := by intro hh; rw [hh] at hq; simp at hq; exact hq0 hq
      exact abs_pos.mpr hv0
    exact erdos_672_four_two_case2_descent ha hd (abs_nonneg u) hVp
      (by nlinarith only [hyp',hUsq,hVsq]) hD hcUV hpUV

def product4 (a d : ℕ) : ℕ := a * (a+d) * (a+2*d) * (a+3*d)
def middle (a d : ℕ) : ℕ := (a+d)*(a+2*d)

theorem normalize {a d q : ℕ} (ha : 0 < a) (hd : 0 < d)
    (h : product4 a d = q^2) :
    ∃ A D Q : ℕ, 0 < A ∧ 0 < D ∧ Nat.gcd A D = 1 ∧
      product4 A D = Q^2 ∧ middle A D ≤ middle a d := by
  let g := Nat.gcd a d
  let A := a / g
  let D := d / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d ha
  have hga : g ∣ a := Nat.gcd_dvd_left a d
  have hgd : g ∣ d := Nat.gcd_dvd_right a d
  have hA : g*A = a := Nat.mul_div_cancel' hga
  have hD : g*D = d := Nat.mul_div_cancel' hgd
  have hAp : 0 < A := by nlinarith
  have hDp : 0 < D := by nlinarith
  have hfactor : g^4 * product4 A D = product4 a d := by
    rw [← hA, ← hD]
    unfold product4
    ring
  have hgq : g^2 ∣ q := by
    apply (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    rw [← h]
    refine ⟨product4 A D, ?_⟩
    rw [← hfactor]
    ring
  obtain ⟨Q, hQ⟩ := hgq
  have heq : product4 A D = Q^2 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hg 4)
    calc
      g^4 * product4 A D = q^2 := hfactor.trans h
      _ = g^4 * Q^2 := by rw [hQ]; ring
  have hAle : A ≤ a := Nat.div_le_self _ _
  have hDle : D ≤ d := Nat.div_le_self _ _
  refine ⟨A,D,Q,hAp,hDp,?_,heq,?_⟩
  · exact Nat.coprime_div_gcd_div_gcd hg
  · unfold middle
    exact Nat.mul_le_mul (by omega) (by omega)

/-- Well-founded closure of a primitive strict descent. The premise is supplied
by the separately proved descent construction, not assumed by a final theorem. -/
theorem no_square_of_primitive_descent
    (step : ∀ a d q : ℕ, 0 < a → 0 < d → Nat.gcd a d = 1 →
      product4 a d = q^2 → ∃ A D Q : ℕ,
        0 < A ∧ 0 < D ∧ product4 A D = Q^2 ∧ middle A D < middle a d) :
    ∀ a d q : ℕ, 0 < a → 0 < d → product4 a d ≠ q^2 := by
  have induction_statement : ∀ m : ℕ, ∀ a d q : ℕ,
      middle a d = m → 0 < a → 0 < d → product4 a d ≠ q^2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a d q hm ha hd heq
      obtain ⟨A,D,Q,hA,hD,hcop,hsq,hle⟩ := normalize ha hd heq
      obtain ⟨A',D',Q',hA',hD',hsq',hlt⟩ := step A D Q hA hD hcop hsq
      have hsm : middle A' D' < m := by omega
      exact ih (middle A' D') hsm A' D' Q' rfl hA' hD' hsq'
  intro a d q ha hd
  exact induction_statement (middle a d) a d q rfl ha hd


/-- Natural-number bridge for the independently proved primitive descent. -/
theorem primitive_four_ap_descent_nat (a d q : ℕ)
    (ha : 0 < a) (hd : 0 < d) (hc : Nat.gcd a d = 1)
    (hsq : product4 a d = q^2) :
    ∃ A D Q : ℕ, 0 < A ∧ 0 < D ∧ product4 A D = Q^2 ∧ middle A D < middle a d := by
  have hcZ : Int.gcd (a : ℤ) (d : ℤ) = 1 := by simpa using hc
  have hsqZ : (a : ℤ)*(a+d)*(a+2*d)*(a+3*d)=(q : ℤ)^2 := by
    unfold product4 at hsq
    exact_mod_cast hsq
  obtain ⟨A,D,Q,hA,hD,hprod,hmid⟩ := primitive_four_ap_descent
    (by exact_mod_cast ha) (by exact_mod_cast hd) hcZ hsqZ
  have hAc : (A.toNat : ℤ)=A := Int.toNat_of_nonneg (le_of_lt hA)
  have hDc : (D.toNat : ℤ)=D := Int.toNat_of_nonneg (le_of_lt hD)
  refine ⟨A.toNat,D.toNat,Q.natAbs,?_,?_,?_,?_⟩
  · have hh : (0:ℤ) < (A.toNat : ℤ) := by rwa [hAc]
    exact_mod_cast hh
  · have hh : (0:ℤ) < (D.toNat : ℤ) := by rwa [hDc]
    exact_mod_cast hh
  · unfold product4
    apply Int.natCast_inj.mp
    push_cast
    rw [hAc,hDc,sq_abs]
    exact hprod
  · unfold middle
    have hh : ((A.toNat : ℤ)+D.toNat)*((A.toNat : ℤ)+2*D.toNat)<
        ((a : ℤ)+d)*((a : ℤ)+2*d) := by rw [hAc,hDc]; exact hmid
    exact_mod_cast hh

/-- The product of four positive integer terms in a nonconstant AP is never
square. Coprimality is unnecessary after normalization. -/
theorem four_ap_ne_sq {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (q : ℕ) :
    n*(n+d)*(n+2*d)*(n+3*d) ≠ q^2 :=
  no_square_of_primitive_descent primitive_four_ap_descent_nat n d q hn hd

/-- Complete Euler four-term square-product theorem in the original interface.
This proves only `k=4, l=2`, not the general perfect-power problem. -/
theorem erdos_672_four_two : Erdos672With 4 2 := by
  intro s _ n hn d hd _ hap q
  rw [prod_eq_of_isAPOfLengthWith_four hd hap]
  exact four_ap_ne_sq hn hd q

#print axioms normalize
#print axioms no_square_of_primitive_descent
#print axioms primitive_four_ap_descent_nat
#print axioms four_ap_ne_sq
#print axioms erdos_672_four_two
#print axioms primitive_four_ap_descent
#print axioms erdos_672_four_two_case1_descent
#print axioms primitive_even_square_leg
#print axioms double_triangle_conic
#print axioms eisenstein_conic_parameterization
#print axioms case1_conic_descent
#print axioms erdos_672_four_two_case2_descent
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
