/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Erdős Problem 939 (`JSP-000780` & `JSP-000781`): Sums of Coprime $r$-Powerful Numbers

*References:*
- [erdosproblems.com/939](https://www.erdosproblems.com/939) (`FormalConjectures/ErdosProblems/939.lean`)
- [Ni95] Nitaj, A., *On a conjecture of Erdős on 3-powerful numbers*. Bull. London Math. Soc.
  27 (1995), 317–318.
- [Co98] Cohn, J. H. E., *A conjecture of Erdős on 3-powerful numbers*. Math. Comp. 67 (1998),
  439–440.
- [Wa24] Walsh, P., *A question of Erdős on 3-powerful numbers and an elliptic curve analogue
  of the Ankeny-Artin-Chowla conjecture*. arXiv:2404.03970 (2024).
- [LaPa67] Lander, L. J. and Parkin, T. R., *A counterexample to Euler's sum of powers
  conjecture*. Math. Comp. 21 (1967), 101–103.

This file formalizes complete, zero-`sorry` proofs of the solved questions and variants of
Erdős Problem 939:
1. **`erdos_939.variants.triples` (`JSP-000780`)**:
   There are infinitely many triples $(a, b, c)$ of coprime positive $3$-powerful numbers
   satisfying $a + b = c$. We formalize a self-contained algebraic recurrence inspired by
   Cohn (1998) starting from Nitaj's seed $271^3 + 2^3 \cdot 3^5 \cdot 73^3 = 919^3$, proving
   that the invariant $3 \mid a b c$ completely eliminates the potential common factor of $3$
   at every step.
2. **`erdos_939.variants.finite` (`JSP-000781`)**:
   Disproves the finiteness question `∀ r ≥ 4, (Erdos939Sums r).Finite` by constructing infinite
   parametric families of coprime $r$-powerful sums in `Erdos939Sums r` for every $r ≥ 6$.
3. **`erdos_939.variants.examples`, `erdos_939.variants.seven`, `erdos_939.variants.eight`,
   and `erdos_939.variants.euler`**:
   Complete proofs of all solved existence variants for $r = 5, 6, 7, 8$ and the Lander–Parkin
   counterexample to Euler's sum of powers conjecture.
-/

open scoped BigOperators

namespace Nat

/-- A natural number `n` is `k`-full (or `k`-powerful) if `p^k ∣ n` for every prime factor `p` of `n`. -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- `0` is always `k`-full. -/
theorem Full.zero_right (k : ℕ) : k.Full 0 := by
  simp [Nat.Full]

/-- `1` is always `k`-full. -/
theorem Full.one_right (k : ℕ) : k.Full 1 := by
  simp [Nat.Full]

/-- Product of two `k`-full numbers is `k`-full. -/
theorem Full.mul {k a b : ℕ} (ha : k.Full a) (hb : k.Full b) : k.Full (a * b) := by
  by_cases hab : a * b = 0
  · rw [hab]
    exact Full.zero_right k
  · have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
    intro p hp
    obtain ⟨hpp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    rcases hpp.dvd_mul.mp hdvd with hda | hdb
    · exact dvd_mul_of_dvd_left (ha p (Nat.mem_primeFactors.mpr ⟨hpp, hda, ha0⟩)) b
    · exact dvd_mul_of_dvd_right (hb p (Nat.mem_primeFactors.mpr ⟨hpp, hdb, hb0⟩)) a

/-- Any $m$-th power $a^m$ with $k \le m$ is $k$-full. -/
theorem Full.pow_of_le {k m : ℕ} (hkm : k ≤ m) (a : ℕ) : k.Full (a ^ m) := by
  by_cases ha0 : a = 0
  · subst ha0
    rcases eq_or_ne m 0 with rfl | hm0
    · simp [Full.one_right]
    · rw [zero_pow hm0]
      exact Full.zero_right k
  · intro p hp
    obtain ⟨hpp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpa : p ∣ a := hpp.dvd_of_dvd_pow hdvd
    exact pow_dvd_of_le_of_pow_dvd hkm (pow_dvd_pow_of_dvd hpa m)

/-- If `c ∣ B`, then `c * B ^ r` is `r`-full for every `r`. -/
theorem Full.mul_pow_of_dvd {r c B : ℕ} (hcB : c ∣ B) : r.Full (c * B ^ r) := by
  intro p hp
  obtain ⟨hpp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpB : p ∣ B := by
    rcases hpp.dvd_mul.mp hdvd with hpc | hpBr
    · exact dvd_trans hpc hcB
    · exact hpp.dvd_of_dvd_pow hpBr
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpB r) c

end Nat

/-- A `Finset` of natural numbers is coprime (setwise relatively prime) if its `gcd` is `1`. -/
@[reducible] def Finset.Coprime (S : Finset ℕ) : Prop := S.gcd id = 1

namespace Erdos939

open Nat

/-- Any `Finset ℕ` containing two coprime elements is setwise coprime. -/
lemma finset_coprime_of_mem_coprime {S : Finset ℕ} {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : Nat.Coprime x y) : S.Coprime :=
  Nat.eq_one_of_dvd_one (hxy ▸ Nat.dvd_gcd (Finset.gcd_dvd hx) (Finset.gcd_dvd hy))

/-!
## Part 1: Infinitely Many Coprime $3$-Powerful Triples $a + b = c$ (`erdos_939.variants.triples`)
-/

/-- A valid state for the Cohn–Nitaj cubic recurrence: coprime $3$-powerful triples $(a, b, c)$
with $1 < a, 1 < b$, $a + b = c$, and at least one of $a, b, c$ divisible by $3$. -/
structure ValidTriple (t : ℕ × ℕ × ℕ) : Prop where
  one_lt_a : 1 < t.1
  one_lt_b : 1 < t.2.1
  coprime : Nat.Coprime t.1 t.2.1
  dvd_three : 3 ∣ t.1 ∨ 3 ∣ t.2.1 ∨ 3 ∣ t.2.2
  full_a : (3).Full t.1
  full_b : (3).Full t.2.1
  full_c : (3).Full t.2.2
  add_eq : t.1 + t.2.1 = t.2.2

/-- Key coprimality lemma for Cohn's cubic map: if $a + b = c$, $\gcd(a, b) = 1$, and $3$ divides
one of $a, b, c$, then $\gcd(b + c, a + c) = 1$. -/
lemma coprime_add_of_valid {a b c : ℕ} (hab : Nat.Coprime a b)
    (h3 : 3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c) (hsum : a + b = c) :
    Nat.Coprime (b + c) (a + c) := by
  rw [Nat.Coprime]
  set g := Nat.gcd (b + c) (a + c)
  have hg_bc : g ∣ b + c := Nat.gcd_dvd_left (b + c) (a + c)
  have hg_ac : g ∣ a + c := Nat.gcd_dvd_right (b + c) (a + c)
  have hg_3c : g ∣ 3 * c := by
    have heq : (b + c) + (a + c) = 3 * c := by omega
    rw [← heq]
    exact dvd_add hg_bc hg_ac
  have hg_3b : g ∣ 3 * b := by
    have heq : 3 * b + 3 * c = 3 * (b + c) := by ring
    exact (Nat.dvd_add_left hg_3c).mp (heq ▸ dvd_mul_of_dvd_right hg_bc 3)
  have hg_3a : g ∣ 3 * a := by
    have heq : 3 * a + 3 * b = 3 * c := by omega
    exact (Nat.dvd_add_left hg_3b).mp (heq ▸ hg_3c)
  have hg_3 : g ∣ 3 := by
    have h1 : g ∣ Nat.gcd (3 * a) (3 * b) := Nat.dvd_gcd hg_3a hg_3b
    rwa [Nat.gcd_mul_left, hab.gcd_eq_one, mul_one] at h1
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hg_3 with hg1 | hg3_eq
  · exact hg1
  · exfalso
    have h3bc : 3 ∣ b + c := hg3_eq ▸ hg_bc
    have h3ac : 3 ∣ a + c := hg3_eq ▸ hg_ac
    have h3ab : 3 ∣ a ∧ 3 ∣ b := by omega
    have h31 : 3 ∣ Nat.gcd a b := Nat.dvd_gcd h3ab.1 h3ab.2
    rw [hab.gcd_eq_one] at h31
    omega

/-- Core step when $a < b$: $(a(b+c)^3, c(b-a)^3, b(a+c)^3)$ is a valid triple with strictly larger sum. -/
lemma step_lt {a b c : ℕ} (ha : 1 < a) (hab_lt : a < b) (hab : Nat.Coprime a b)
    (h3 : 3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c) (hfa : (3).Full a) (hfb : (3).Full b) (hfc : (3).Full c)
    (hsum : a + b = c) :
    ValidTriple (a * (b + c) ^ 3, c * (b - a) ^ 3, b * (a + c) ^ 3) ∧
      c < b * (a + c) ^ 3 := by
  have hle : a ≤ b := le_of_lt hab_lt
  have hsum' : a * (b + c) ^ 3 + c * (b - a) ^ 3 = b * (a + c) ^ 3 := by
    subst hsum
    zify [hle]
    ring
  have hac : Nat.Coprime a c := by
    rw [← hsum]
    exact Nat.coprime_self_add_right.mpr hab
  have hbc : Nat.Coprime b c := by
    rw [← hsum]
    exact Nat.coprime_add_self_right.mpr hab.symm
  have h_a_ac : Nat.Coprime a (a + c) := Nat.coprime_self_add_right.mpr hac
  have h_bc_b : Nat.Coprime (b + c) b := by
    rw [add_comm]
    exact Nat.coprime_add_self_left.mpr hbc.symm
  have h_bc_ac : Nat.Coprime (b + c) (a + c) := coprime_add_of_valid hab h3 hsum
  have hcop_a'_c' : Nat.Coprime (a * (b + c) ^ 3) (b * (a + c) ^ 3) :=
    (hab.mul_right (h_a_ac.pow_right 3)).mul_left ((h_bc_b.pow_left 3).mul_right (h_bc_ac.pow 3 3))
  have hcop_a'_b' : Nat.Coprime (a * (b + c) ^ 3) (c * (b - a) ^ 3) := by
    rw [← hsum'] at hcop_a'_c'
    exact Nat.coprime_self_add_right.mp hcop_a'_c'
  have h3' : 3 ∣ a * (b + c) ^ 3 ∨ 3 ∣ c * (b - a) ^ 3 ∨ 3 ∣ b * (a + c) ^ 3 := by
    rcases h3 with h3a | h3b | h3c
    · exact Or.inl (dvd_mul_of_dvd_left h3a _)
    · exact Or.inr (Or.inr (dvd_mul_of_dvd_left h3b _))
    · exact Or.inr (Or.inl (dvd_mul_of_dvd_left h3c _))
  have hba_pos : 1 ≤ b - a := by omega
  have hbc_pos : 1 ≤ b + c := by omega
  have hac_pos : 2 ≤ a + c := by omega
  refine ⟨⟨?_, ?_, hcop_a'_b', h3',
    hfa.mul (Full.pow_of_le (le_refl 3) _),
    hfc.mul (Full.pow_of_le (le_refl 3) _),
    hfb.mul (Full.pow_of_le (le_refl 3) _),
    hsum'⟩, ?_⟩
  · have : 1 ≤ (b + c) ^ 3 := one_le_pow₀ hbc_pos
    nlinarith
  · have : 1 ≤ (b - a) ^ 3 := one_le_pow₀ hba_pos
    nlinarith
  · have : c < (a + c) ^ 3 := by
      calc c < a + c := by omega
        _ = (a + c) ^ 1 := (pow_one _).symm
        _ ≤ (a + c) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith

/-- Next triple map on $\mathbb{N}^3$. -/
def nextTriple (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let a := t.1
  let b := t.2.1
  let c := t.2.2
  if a ≤ b then
    (a * (b + c) ^ 3, c * (b - a) ^ 3, b * (a + c) ^ 3)
  else
    (b * (a + c) ^ 3, c * (a - b) ^ 3, a * (b + c) ^ 3)

lemma nextTriple_spec {t : ℕ × ℕ × ℕ} (ht : ValidTriple t) :
    ValidTriple (nextTriple t) ∧ t.2.2 < (nextTriple t).2.2 := by
  rcases t with ⟨a, b, c⟩
  have hne : a ≠ b := by
    rintro rfl
    have h1 : a = 1 := by
      have := ht.coprime.gcd_eq_one
      rwa [Nat.gcd_self] at this
    linarith [ht.one_lt_a]
  unfold nextTriple
  dsimp only
  split_ifs with hle
  · exact step_lt ht.one_lt_a (lt_of_le_of_ne hle hne) ht.coprime ht.dvd_three
      ht.full_a ht.full_b ht.full_c ht.add_eq
  · have hba : b < a := by omega
    have h3_swap : 3 ∣ b ∨ 3 ∣ a ∨ 3 ∣ c := by
      rcases ht.dvd_three with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    exact step_lt ht.one_lt_b hba ht.coprime.symm h3_swap
      ht.full_b ht.full_a ht.full_c (by linarith [ht.add_eq])

/-- Nitaj's seed triple $(271^3, 2^3 \cdot 3^5 \cdot 73^3, 919^3)$. -/
def seedTriple : ℕ × ℕ × ℕ := (271 ^ 3, 2 ^ 3 * 3 ^ 5 * 73 ^ 3, 919 ^ 3)

lemma seedTriple_valid : ValidTriple seedTriple := by
  refine ⟨by norm_num [seedTriple], by norm_num [seedTriple], by decide,
    Or.inr (Or.inl (by decide)), ?_, ?_, ?_, by norm_num [seedTriple]⟩
  · exact Full.pow_of_le (le_refl 3) 271
  · exact ((Full.pow_of_le (le_refl 3) 2).mul (Full.pow_of_le (by omega : 3 ≤ 5) 3)).mul
      (Full.pow_of_le (le_refl 3) 73)
  · exact Full.pow_of_le (le_refl 3) 919

/-- Sequence of coprime $3$-powerful triples generated by iterating `nextTriple`. -/
def tripleSeq : ℕ → ℕ × ℕ × ℕ
  | 0 => seedTriple
  | n + 1 => nextTriple (tripleSeq n)

lemma tripleSeq_valid (n : ℕ) : ValidTriple (tripleSeq n) := by
  induction n with
  | zero => exact seedTriple_valid
  | succ n ih => exact (nextTriple_spec ih).1

lemma tripleSeq_strictMono : StrictMono (fun n => (tripleSeq n).2.2) :=
  strictMono_nat_of_lt_succ fun n => (nextTriple_spec (tripleSeq_valid n)).2

/-- **Erdős Problem 939, Triples Variant (`JSP-000780`)**:
There are infinitely many triples $(a, b, c)$ of coprime positive $3$-powerful numbers such that
$a + b = c$. -/
theorem erdos_939.variants.triples :
    {(a, b, c) | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      a + b = c}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := tripleSeq)
  · intro m₁ m₂ heq
    apply tripleSeq_strictMono.injective
    exact congrArg (fun t => t.2.2) heq
  · intro n
    have hv := tripleSeq_valid n
    rcases h : tripleSeq n with ⟨a, b, c⟩
    rw [h] at hv
    have hcop : ({a, b, c} : Finset ℕ).Coprime :=
      finset_coprime_of_mem_coprime (by simp) (by simp) hv.coprime
    exact ⟨hcop, by linarith [hv.one_lt_a], by linarith [hv.one_lt_b],
      hv.full_a, hv.full_b, hv.full_c, hv.add_eq⟩

/-!
## Part 2: Sums of $r - 2$ Coprime $r$-Powerful Numbers (`Erdos939Sums r`)
-/

/-- A set `S` belongs to `Erdos939Sums r` if it has size `r - 2`, is setwise coprime, consists of
positive `r`-powerful numbers, and has an `r`-powerful sum. -/
def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧
      ∀ s ∈ S, 0 < s ∧ r.Full s}

/-- Helper lemma: a family `f : ℕ → Finset ℕ` with strictly increasing sums proves infinitude. -/
lemma infinite_of_strictMono_sum {P : Finset ℕ → Prop} (f : ℕ → Finset ℕ) (g : ℕ → ℕ)
    (hmem : ∀ m, P (f m)) (hsum : ∀ m, ∑ s ∈ f m, s = g m) (hmono : StrictMono g) :
    {S : Finset ℕ | P S}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := f) ?_ hmem
  intro m₁ m₂ heq
  apply hmono.injective
  rw [← hsum m₁, ← hsum m₂, heq]

/-- Every monomial term `c * (M ^ r) ^ a * (B ^ r) ^ b` with `c ∣ B` and `1 ≤ b` is `r`-powerful. -/
lemma full_monomial_term {r M B c a b : ℕ} (hcB : c ∣ B) (hb : 1 ≤ b) :
    r.Full (c * (M ^ r) ^ a * (B ^ r) ^ b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have heq : c * (M ^ r) ^ a * (B ^ r) ^ (k + 1) = (c * B ^ r) * (M ^ a) ^ r * (B ^ k) ^ r := by
    ring
  rw [heq]
  exact ((Full.mul_pow_of_dvd hcB).mul (Full.pow_of_le (le_refl r) _)).mul
    (Full.pow_of_le (le_refl r) _)

/-- Coprimality between `(X - Y)^r` and `c * X^a * Y^b` when `M = B * k + 1`, `X = M^r`, `Y = B^r`,
and `c ∣ B`. -/
lemma coprime_sub_pow_monomial {r B k c a b : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (hcB : c ∣ B) :
    let M := B * k + 1
    let X := M ^ r
    let Y := B ^ r
    Nat.Coprime ((X - Y) ^ r) (c * X ^ a * Y ^ b) := by
  intro M X Y
  have hMB : Nat.Coprime M B := by
    rw [Nat.Coprime]
    have hd1 : Nat.gcd (B * k + 1) B ∣ B * k + 1 := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd (B * k + 1) B ∣ B := Nat.gcd_dvd_right _ _
    have hd_Bk : Nat.gcd (B * k + 1) B ∣ B * k := dvd_mul_of_dvd_left hd2 k
    exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right hd_Bk).mp hd1)
  have hXY : Nat.Coprime X Y := hMB.pow r r
  have hBM : B ≤ M := by
    change B ≤ B * k + 1
    nlinarith
  have hYX_le : Y ≤ X := Nat.pow_le_pow_left hBM r
  have hX_eq : (X - Y) + Y = X := Nat.sub_add_cancel hYX_le
  have h_sub_Y : Nat.Coprime (X - Y) Y := by
    rw [Nat.Coprime]
    have hd1 : Nat.gcd (X - Y) Y ∣ X - Y := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd (X - Y) Y ∣ Y := Nat.gcd_dvd_right _ _
    have hdX : Nat.gcd (X - Y) Y ∣ (X - Y) + Y := dvd_add hd1 hd2
    rw [hX_eq] at hdX
    have hd_gcd : Nat.gcd (X - Y) Y ∣ Nat.gcd X Y := Nat.dvd_gcd hdX hd2
    rw [hXY.gcd_eq_one] at hd_gcd
    exact Nat.eq_one_of_dvd_one hd_gcd
  have h_sub_X : Nat.Coprime (X - Y) X := by
    rw [Nat.Coprime]
    have hd1 : Nat.gcd (X - Y) X ∣ X - Y := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd (X - Y) X ∣ X := Nat.gcd_dvd_right _ _
    have hd2' : Nat.gcd (X - Y) X ∣ (X - Y) + Y := by
      simpa only [hX_eq] using hd2
    have hdY : Nat.gcd (X - Y) X ∣ Y := (Nat.dvd_add_right hd1).mp hd2'
    have hd_gcd : Nat.gcd (X - Y) X ∣ Nat.gcd (X - Y) Y := Nat.dvd_gcd hd1 hdY
    rw [h_sub_Y.gcd_eq_one] at hd_gcd
    exact Nat.eq_one_of_dvd_one hd_gcd
  have hcY : c ∣ Y := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    change c ∣ B ^ (t + 1)
    rw [_root_.pow_succ']
    exact dvd_mul_of_dvd_left hcB (B ^ t)
  have h_sub_c : Nat.Coprime (X - Y) c := h_sub_Y.coprime_dvd_right hcY
  exact ((h_sub_c.mul_right (h_sub_X.pow_right a)).mul_right (h_sub_Y.pow_right b)).pow_left r

/-- Monomial comparison helper: avoids unfolding large powers of concrete numerals. -/
lemma monomial_lt_step2 {c₁ c₂ X Y a b : ℕ} (hX : 0 < X) (hY : 0 < Y)
    (hc : c₁ * Y ^ 2 < c₂ * X ^ 2) :
    c₁ * X ^ a * Y ^ (b + 2) < c₂ * X ^ (a + 2) * Y ^ b := by
  have hpos : 0 < X ^ a * Y ^ b := mul_pos (pow_pos hX a) (pow_pos hY b)
  calc c₁ * X ^ a * Y ^ (b + 2) = (c₁ * Y ^ 2) * (X ^ a * Y ^ b) := by ring
    _ < (c₂ * X ^ 2) * (X ^ a * Y ^ b) := Nat.mul_lt_mul_of_pos_right hc hpos
    _ = c₂ * X ^ (a + 2) * Y ^ b := by ring

lemma card_and_sum_three {a₁ a₂ a₃ : ℕ} (h12 : a₁ < a₂) (h23 : a₂ < a₃) :
    ({a₁, a₂, a₃} : Finset ℕ).card = 3 ∧
      ∑ s ∈ ({a₁, a₂, a₃} : Finset ℕ), s = a₁ + a₂ + a₃ := by
  have h1 : a₁ ∉ ({a₂, a₃} : Finset ℕ) := by simp; omega
  have h2 : a₂ ∉ ({a₃} : Finset ℕ) := by simp; omega
  constructor
  · simp [h1, h2]
  · simp [h1, h2, add_assoc]

lemma card_and_sum_four {a₁ a₂ a₃ a₄ : ℕ} (h12 : a₁ < a₂) (h23 : a₂ < a₃) (h34 : a₃ < a₄) :
    ({a₁, a₂, a₃, a₄} : Finset ℕ).card = 4 ∧
      ∑ s ∈ ({a₁, a₂, a₃, a₄} : Finset ℕ), s = a₁ + a₂ + a₃ + a₄ := by
  have h1 : a₁ ∉ ({a₂, a₃, a₄} : Finset ℕ) := by simp; omega
  have h2 : a₂ ∉ ({a₃, a₄} : Finset ℕ) := by simp; omega
  have h3 : a₃ ∉ ({a₄} : Finset ℕ) := by simp; omega
  constructor
  · simp [h1, h2, h3]
  · simp [h1, h2, h3, add_assoc]

lemma card_and_sum_five {a₁ a₂ a₃ a₄ a₅ : ℕ} (h12 : a₁ < a₂) (h23 : a₂ < a₃) (h34 : a₃ < a₄)
    (h45 : a₄ < a₅) :
    ({a₁, a₂, a₃, a₄, a₅} : Finset ℕ).card = 5 ∧
      ∑ s ∈ ({a₁, a₂, a₃, a₄, a₅} : Finset ℕ), s = a₁ + a₂ + a₃ + a₄ + a₅ := by
  have h0 : a₁ ∉ ({a₂, a₃, a₄, a₅} : Finset ℕ) := by simp; omega
  obtain ⟨hc, hs⟩ := card_and_sum_four h23 h34 h45
  constructor
  · simp [h0, hc]
  · simp [h0, hs, add_assoc]

lemma card_and_sum_six {a₁ a₂ a₃ a₄ a₅ a₆ : ℕ} (h12 : a₁ < a₂) (h23 : a₂ < a₃) (h34 : a₃ < a₄)
    (h45 : a₄ < a₅) (h56 : a₅ < a₆) :
    ({a₁, a₂, a₃, a₄, a₅, a₆} : Finset ℕ).card = 6 ∧
      ∑ s ∈ ({a₁, a₂, a₃, a₄, a₅, a₆} : Finset ℕ), s = a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := by
  have h0 : a₁ ∉ ({a₂, a₃, a₄, a₅, a₆} : Finset ℕ) := by simp; omega
  obtain ⟨hc, hs⟩ := card_and_sum_five h23 h34 h45 h56
  constructor
  · simp [h0, hc]
  · simp [h0, hs, add_assoc]

/-!
### Infinite Family for $r = 6$ and Disproof of `erdos_939.variants.finite` (`JSP-000781`)
-/

/-- The $4$-element set for $r = 6$ parametrized by general $(X, Y)$. -/
def rawSetSix (X Y : ℕ) : Finset ℕ :=
  {12 * X ^ 1 * Y ^ 5, 40 * X ^ 3 * Y ^ 3, 12 * X ^ 5 * Y ^ 1, (X - Y) ^ 6}

lemma rawSetSix_card_and_sum {X Y : ℕ} (hY : 0 < Y) (hXY : 4096 * Y ≤ X) :
    (rawSetSix X Y).card = 4 ∧ ∑ s ∈ rawSetSix X Y, s = (X + Y) ^ 6 := by
  have hX : 0 < X := by omega
  set Z := X - Y
  have hXZ : X = Z + Y := (Nat.sub_add_cancel (by omega : Y ≤ X)).symm
  have hZY : 4095 * Y ≤ Z := by omega
  have h12 : 12 * X ^ 1 * Y ^ 5 < 40 * X ^ 3 * Y ^ 3 :=
    monomial_lt_step2 hX hY (by nlinarith)
  have h23 : 40 * X ^ 3 * Y ^ 3 < 12 * X ^ 5 * Y ^ 1 :=
    monomial_lt_step2 hX hY (by nlinarith)
  have h34 : 12 * X ^ 5 * Y ^ 1 < (X - Y) ^ 6 := by
    change 12 * X ^ 5 * Y ^ 1 < Z ^ 6
    have hX_le : X ≤ 2 * Z := by omega
    have hX5 : X ^ 5 ≤ (2 * Z) ^ 5 := Nat.pow_le_pow_left hX_le 5
    have hZ5_pos : 0 < Z ^ 5 := pow_pos (by omega : 0 < Z) 5
    calc 12 * X ^ 5 * Y ^ 1 ≤ 12 * (2 * Z) ^ 5 * Y := by nlinarith
      _ = 384 * Y * Z ^ 5 := by ring
      _ < Z * Z ^ 5 := by nlinarith
      _ = Z ^ 6 := by ring
  obtain ⟨hcard, hsum⟩ := card_and_sum_four h12 h23 h34
  refine ⟨hcard, ?_⟩
  unfold rawSetSix
  rw [hsum]
  have hle : Y ≤ X := by omega
  zify [hle]
  ring

lemma rawSetSix_mem {B k : ℕ} (hB : 0 < B) (hk : 4 ≤ k) (h12 : 12 ∣ B) (h40 : 40 ∣ B) :
    let M := B * k + 1
    let X := M ^ 6
    let Y := B ^ 6
    rawSetSix X Y ∈ Erdos939Sums 6 ∧ ∑ s ∈ rawSetSix X Y, s = (X + Y) ^ 6 := by
  intro M X Y
  have hY_pos : 0 < Y := pow_pos hB 6
  have h4B : 4 * B ≤ M := by
    change 4 * B ≤ B * k + 1
    nlinarith
  have hXY_bound : 4096 * Y ≤ X := by
    calc 4096 * Y = (4 * B) ^ 6 := by ring
      _ ≤ M ^ 6 := Nat.pow_le_pow_left h4B 6
  obtain ⟨hcard, hsum_eq⟩ := rawSetSix_card_and_sum hY_pos hXY_bound
  refine ⟨⟨hcard, ?_, ?_, ?_⟩, hsum_eq⟩
  · apply finset_coprime_of_mem_coprime (x := (X - Y) ^ 6) (y := 12 * X ^ 1 * Y ^ 5)
    · simp [rawSetSix]
    · simp [rawSetSix]
    · exact coprime_sub_pow_monomial (by omega) (by omega) h12
  · rw [hsum_eq]
    exact Full.pow_of_le (le_refl 6) (X + Y)
  · intro s hs
    simp only [rawSetSix, Finset.mem_insert, Finset.mem_singleton] at hs
    have hX_pos : 0 < X := by omega
    have hZ_pos : 0 < X - Y := by omega
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨by positivity, full_monomial_term h12 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h40 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h12 (by omega)⟩
    · exact ⟨pow_pos hZ_pos 6, Full.pow_of_le (le_refl 6) (X - Y)⟩

/-- Parametric family of $4$-element sets in `Erdos939Sums 6`. -/
def sumSetSix (m : ℕ) : Finset ℕ :=
  rawSetSix ((120 * (m + 4) + 1) ^ 6) (120 ^ 6)

lemma sumSetSix_spec (m : ℕ) :
    sumSetSix m ∈ Erdos939Sums 6 ∧
      ∑ s ∈ sumSetSix m, s = ((120 * (m + 4) + 1) ^ 6 + 120 ^ 6) ^ 6 :=
  rawSetSix_mem (B := 120) (k := m + 4) (by decide) (by omega) (by decide) (by decide)

/-- `Erdos939Sums 6` is infinite. -/
theorem erdos_939_six_infinite : (Erdos939Sums 6).Infinite := by
  apply infinite_of_strictMono_sum sumSetSix (fun m => ((120 * (m + 4) + 1) ^ 6 + 120 ^ 6) ^ 6)
  · exact fun m => (sumSetSix_spec m).1
  · exact fun m => (sumSetSix_spec m).2
  · intro a b hab
    apply Nat.pow_lt_pow_left _ (by omega : 6 ≠ 0)
    apply Nat.add_lt_add_right
    apply Nat.pow_lt_pow_left (by omega) (by omega : 6 ≠ 0)

/-- **Erdős Problem 939, Finiteness Question (`JSP-000781`)**:
It is NOT true that for every $r \ge 4$ there are at most finitely many sums of $r - 2$ coprime
$r$-powerful numbers that are themselves $r$-powerful. -/
theorem erdos_939.variants.finite : ¬ ∀ r ≥ 4, (Erdos939Sums r).Finite := by
  intro h
  exact erdos_939_six_infinite (h 6 (by omega))

/-!
### Infinite Families and Existence for $r = 7$ and $r = 8$ (`seven`, `eight`, `examples`, `euler`)
-/

/-- The $5$-element set for $r = 7$ parametrized by general $(X, Y)$. -/
def rawSetSeven (X Y : ℕ) : Finset ℕ :=
  {2 * X ^ 0 * Y ^ 7, 42 * X ^ 2 * Y ^ 5, 70 * X ^ 4 * Y ^ 3, 14 * X ^ 6 * Y ^ 1, (X - Y) ^ 7}

lemma rawSetSeven_card_and_sum {X Y : ℕ} (hY : 0 < Y) (hXY : 16384 * Y ≤ X) :
    (rawSetSeven X Y).card = 5 ∧ ∑ s ∈ rawSetSeven X Y, s = (X + Y) ^ 7 := by
  have hX : 0 < X := by omega
  set Z := X - Y
  have hXZ : X = Z + Y := (Nat.sub_add_cancel (by omega : Y ≤ X)).symm
  have hZY : 16383 * Y ≤ Z := by omega
  have h12 : 2 * X ^ 0 * Y ^ 7 < 42 * X ^ 2 * Y ^ 5 :=
    monomial_lt_step2 hX hY (by nlinarith)
  have h23 : 42 * X ^ 2 * Y ^ 5 < 70 * X ^ 4 * Y ^ 3 :=
    monomial_lt_step2 hX hY (by nlinarith)
  have h34 : 70 * X ^ 4 * Y ^ 3 < 14 * X ^ 6 * Y ^ 1 :=
    monomial_lt_step2 hX hY (by nlinarith)
  have h45 : 14 * X ^ 6 * Y ^ 1 < (X - Y) ^ 7 := by
    change 14 * X ^ 6 * Y ^ 1 < Z ^ 7
    have hX_le : X ≤ 2 * Z := by omega
    have hX6 : X ^ 6 ≤ (2 * Z) ^ 6 := Nat.pow_le_pow_left hX_le 6
    have hZ6_pos : 0 < Z ^ 6 := pow_pos (by omega : 0 < Z) 6
    calc 14 * X ^ 6 * Y ^ 1 ≤ 14 * (2 * Z) ^ 6 * Y := by nlinarith
      _ = 896 * Y * Z ^ 6 := by ring
      _ < Z * Z ^ 6 := by nlinarith
      _ = Z ^ 7 := by ring
  obtain ⟨hcard, hsum⟩ := card_and_sum_five h12 h23 h34 h45
  refine ⟨hcard, ?_⟩
  unfold rawSetSeven
  rw [hsum]
  have hle : Y ≤ X := by omega
  zify [hle]
  ring

lemma rawSetSeven_mem {B k : ℕ} (hB : 0 < B) (hk : 4 ≤ k)
    (h2 : 2 ∣ B) (h14 : 14 ∣ B) (h42 : 42 ∣ B) (h70 : 70 ∣ B) :
    let M := B * k + 1
    let X := M ^ 7
    let Y := B ^ 7
    rawSetSeven X Y ∈ Erdos939Sums 7 ∧ ∑ s ∈ rawSetSeven X Y, s = (X + Y) ^ 7 := by
  intro M X Y
  have hY_pos : 0 < Y := pow_pos hB 7
  have h4B : 4 * B ≤ M := by
    change 4 * B ≤ B * k + 1
    nlinarith
  have hXY_bound : 16384 * Y ≤ X := by
    calc 16384 * Y = (4 * B) ^ 7 := by ring
      _ ≤ M ^ 7 := Nat.pow_le_pow_left h4B 7
  obtain ⟨hcard, hsum_eq⟩ := rawSetSeven_card_and_sum hY_pos hXY_bound
  refine ⟨⟨hcard, ?_, ?_, ?_⟩, hsum_eq⟩
  · apply finset_coprime_of_mem_coprime (x := (X - Y) ^ 7) (y := 2 * X ^ 0 * Y ^ 7)
    · simp [rawSetSeven]
    · simp [rawSetSeven]
    · exact coprime_sub_pow_monomial (by omega) (by omega) h2
  · rw [hsum_eq]
    exact Full.pow_of_le (le_refl 7) (X + Y)
  · intro s hs
    simp only [rawSetSeven, Finset.mem_insert, Finset.mem_singleton] at hs
    have hX_pos : 0 < X := by omega
    have hZ_pos : 0 < X - Y := by omega
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by positivity, full_monomial_term h2 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h42 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h70 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h14 (by omega)⟩
    · exact ⟨pow_pos hZ_pos 7, Full.pow_of_le (le_refl 7) (X - Y)⟩

/-- Parametric family of $5$-element sets in `Erdos939Sums 7`. -/
def sumSetSeven (m : ℕ) : Finset ℕ :=
  rawSetSeven ((210 * (m + 4) + 1) ^ 7) (210 ^ 7)

lemma sumSetSeven_spec (m : ℕ) :
    sumSetSeven m ∈ Erdos939Sums 7 ∧
      ∑ s ∈ sumSetSeven m, s = ((210 * (m + 4) + 1) ^ 7 + 210 ^ 7) ^ 7 :=
  rawSetSeven_mem (B := 210) (k := m + 4)
    (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)

/-- `Erdos939Sums 7` is infinite. -/
theorem erdos_939_seven_infinite : (Erdos939Sums 7).Infinite := by
  apply infinite_of_strictMono_sum sumSetSeven (fun m => ((210 * (m + 4) + 1) ^ 7 + 210 ^ 7) ^ 7)
  · exact fun m => (sumSetSeven_spec m).1
  · exact fun m => (sumSetSeven_spec m).2
  · intro a b hab
    apply Nat.pow_lt_pow_left _ (by omega : 7 ≠ 0)
    apply Nat.add_lt_add_right
    apply Nat.pow_lt_pow_left (by omega) (by omega : 7 ≠ 0)

/-- **Erdős Problem 939, Variant `r = 7` (`erdos_939.variants.seven`)**:
`Erdos939Sums 7` is nonempty. -/
theorem erdos_939.variants.seven : (Erdos939Sums 7).Nonempty :=
  erdos_939_seven_infinite.nonempty

/-- The $6$-element set for $r = 8$ parametrized by general $(X, Y)$. -/
def rawSetEight (X Y : ℕ) : Finset ℕ :=
  {16 * X ^ 1 * Y ^ 7, 112 * X ^ 3 * Y ^ 5, 32 * X ^ 5 * Y ^ 3,
   80 * X ^ 5 * Y ^ 3, 16 * X ^ 7 * Y ^ 1, (X - Y) ^ 8}

lemma rawSetEight_card_and_sum {X Y : ℕ} (hY : 0 < Y) (hXY : 65536 * Y ≤ X) :
    (rawSetEight X Y).card = 6 ∧ ∑ s ∈ rawSetEight X Y, s = (X + Y) ^ 8 := by
  have hX : 0 < X := by omega
  set Z := X - Y
  have hXZ : X = Z + Y := (Nat.sub_add_cancel (by omega : Y ≤ X)).symm
  have hZY : 65535 * Y ≤ Z := by omega
  have h12 : 16 * X ^ 1 * Y ^ 7 < 112 * X ^ 3 * Y ^ 5 :=
    monomial_lt_step2 hX hY (by nlinarith)
  have h23 : 112 * X ^ 3 * Y ^ 5 < 32 * X ^ 5 * Y ^ 3 :=
    monomial_lt_step2 hX hY (by nlinarith)
  have h34 : 32 * X ^ 5 * Y ^ 3 < 80 * X ^ 5 * Y ^ 3 := by
    have hpos : 0 < X ^ 5 * Y ^ 3 := mul_pos (pow_pos hX 5) (pow_pos hY 3)
    calc 32 * X ^ 5 * Y ^ 3 = 32 * (X ^ 5 * Y ^ 3) := by ring
      _ < 80 * (X ^ 5 * Y ^ 3) := Nat.mul_lt_mul_of_pos_right (by omega) hpos
      _ = 80 * X ^ 5 * Y ^ 3 := by ring
  have h45 : 80 * X ^ 5 * Y ^ 3 < 16 * X ^ 7 * Y ^ 1 :=
    monomial_lt_step2 hX hY (by nlinarith)
  have h56 : 16 * X ^ 7 * Y ^ 1 < (X - Y) ^ 8 := by
    change 16 * X ^ 7 * Y ^ 1 < Z ^ 8
    have hX_le : X ≤ 2 * Z := by omega
    have hX7 : X ^ 7 ≤ (2 * Z) ^ 7 := Nat.pow_le_pow_left hX_le 7
    have hZ7_pos : 0 < Z ^ 7 := pow_pos (by omega : 0 < Z) 7
    calc 16 * X ^ 7 * Y ^ 1 ≤ 16 * (2 * Z) ^ 7 * Y := by nlinarith
      _ = 2048 * Y * Z ^ 7 := by ring
      _ < Z * Z ^ 7 := by nlinarith
      _ = Z ^ 8 := by ring
  obtain ⟨hcard, hsum⟩ := card_and_sum_six h12 h23 h34 h45 h56
  refine ⟨hcard, ?_⟩
  unfold rawSetEight
  rw [hsum]
  have hle : Y ≤ X := by omega
  zify [hle]
  ring

lemma rawSetEight_mem {B k : ℕ} (hB : 0 < B) (hk : 4 ≤ k)
    (h16 : 16 ∣ B) (h32 : 32 ∣ B) (h80 : 80 ∣ B) (h112 : 112 ∣ B) :
    let M := B * k + 1
    let X := M ^ 8
    let Y := B ^ 8
    rawSetEight X Y ∈ Erdos939Sums 8 ∧ ∑ s ∈ rawSetEight X Y, s = (X + Y) ^ 8 := by
  intro M X Y
  have hY_pos : 0 < Y := pow_pos hB 8
  have h4B : 4 * B ≤ M := by
    change 4 * B ≤ B * k + 1
    nlinarith
  have hXY_bound : 65536 * Y ≤ X := by
    calc 65536 * Y = (4 * B) ^ 8 := by ring
      _ ≤ M ^ 8 := Nat.pow_le_pow_left h4B 8
  obtain ⟨hcard, hsum_eq⟩ := rawSetEight_card_and_sum hY_pos hXY_bound
  refine ⟨⟨hcard, ?_, ?_, ?_⟩, hsum_eq⟩
  · apply finset_coprime_of_mem_coprime (x := (X - Y) ^ 8) (y := 16 * X ^ 1 * Y ^ 7)
    · simp [rawSetEight]
    · simp [rawSetEight]
    · exact coprime_sub_pow_monomial (by omega) (by omega) h16
  · rw [hsum_eq]
    exact Full.pow_of_le (le_refl 8) (X + Y)
  · intro s hs
    simp only [rawSetEight, Finset.mem_insert, Finset.mem_singleton] at hs
    have hX_pos : 0 < X := by omega
    have hZ_pos : 0 < X - Y := by omega
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by positivity, full_monomial_term h16 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h112 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h32 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h80 (by omega)⟩
    · exact ⟨by positivity, full_monomial_term h16 (by omega)⟩
    · exact ⟨pow_pos hZ_pos 8, Full.pow_of_le (le_refl 8) (X - Y)⟩

/-- Parametric family of $6$-element sets in `Erdos939Sums 8`. -/
def sumSetEight (m : ℕ) : Finset ℕ :=
  rawSetEight ((1120 * (m + 4) + 1) ^ 8) (1120 ^ 8)

lemma sumSetEight_spec (m : ℕ) :
    sumSetEight m ∈ Erdos939Sums 8 ∧
      ∑ s ∈ sumSetEight m, s = ((1120 * (m + 4) + 1) ^ 8 + 1120 ^ 8) ^ 8 :=
  rawSetEight_mem (B := 1120) (k := m + 4)
    (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)

/-- `Erdos939Sums 8` is infinite. -/
theorem erdos_939_eight_infinite : (Erdos939Sums 8).Infinite := by
  apply infinite_of_strictMono_sum sumSetEight (fun m => ((1120 * (m + 4) + 1) ^ 8 + 1120 ^ 8) ^ 8)
  · exact fun m => (sumSetEight_spec m).1
  · exact fun m => (sumSetEight_spec m).2
  · intro a b hab
    apply Nat.pow_lt_pow_left _ (by omega : 8 ≠ 0)
    apply Nat.add_lt_add_right
    apply Nat.pow_lt_pow_left (by omega) (by omega : 8 ≠ 0)

/-- **Erdős Problem 939, Variant `r = 8` (`erdos_939.variants.eight`)**:
`Erdos939Sums 8` is nonempty. -/
theorem erdos_939.variants.eight : (Erdos939Sums 8).Nonempty :=
  erdos_939_eight_infinite.nonempty

/-!
### Infinite families for every `r ≥ 6`

Mathematical construction: GPT-5.5 Pro prompted by Liam Price, posted on 24 May 2026,
https://www.erdosproblems.com/forum/thread/939#post-6640. This is a newly written
Finset formalization using labels `(exponent, coefficient)`; no code from the linked
Aristotle autoformalization is included (its reuse license was not established).
The original `Erdos939Sums` definition is unchanged. The construction does not resolve
positive existence at `r = 4` or infinitude at `r = 4, 5`.
-/

namespace General

/-- Odd powers of `Y` in the binomial expansion. -/
def oddTerms (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun j => Odd j)

def pieces (r : ℕ) : ℕ := r / 2 - 2

def smallCoefficients (r : ℕ) : Finset ℕ :=
  (Finset.range (pieces r - 1)).image Nat.succ

def remainder (r : ℕ) : ℕ := 2 * r.choose 3 - ∑ c ∈ smallCoefficients r, c

def coefficients (r : ℕ) : Finset ℕ := insert (remainder r) (smallCoefficients r)

lemma cubic_room (r : ℕ) (hr : 6 ≤ r) : r * r < 2 * r.choose 3 := by
  have quadratic_room : ∀ n ≥ 4, n + 1 ≤ n.choose 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num [Nat.choose]
    | succ n hn ih =>
      rw [show (n + 1).choose 2 = n.choose 1 + n.choose 2 by
        exact Nat.choose_succ_succ n 1, Nat.choose_one_right]
      omega
  induction r, hr using Nat.le_induction with
  | base => norm_num [Nat.choose]
  | succ r hr ih =>
    rw [Nat.choose_succ_succ]
    have h := quadratic_room r (by omega)
    nlinarith

lemma pieces_bounds (r : ℕ) (hr : 6 ≤ r) : 1 ≤ pieces r ∧ pieces r ≤ r := by
  unfold pieces
  omega

lemma small_mem {r c : ℕ} : c ∈ smallCoefficients r ↔ 1 ≤ c ∧ c < pieces r := by
  simp only [smallCoefficients, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨hc, ht⟩
    exact ⟨c - 1, by omega, by omega⟩

lemma coefficient_spec (r : ℕ) (hr : 6 ≤ r) :
    (coefficients r).card = pieces r ∧
    (∑ c ∈ coefficients r, c) = 2 * r.choose 3 ∧
    ∀ c ∈ coefficients r, 0 < c := by
  have ht := pieces_bounds r hr
  have hcard : (smallCoefficients r).card = pieces r - 1 := by
    rw [smallCoefficients, Finset.card_image_of_injective _ Nat.succ_injective]
    simp
  have hbound : (∑ c ∈ smallCoefficients r, c) + pieces r ≤ r * r := by
    have hsum : (∑ c ∈ smallCoefficients r, c) ≤ (pieces r - 1) * pieces r := by
      calc
        _ ≤ ∑ _c ∈ smallCoefficients r, pieces r :=
          Finset.sum_le_sum (fun c hc => (small_mem.mp hc).2.le)
        _ = (pieces r - 1) * pieces r := by simp [hcard]
    have hcancel : (pieces r - 1) + 1 = pieces r := by omega
    calc
      _ ≤ (pieces r - 1) * pieces r + pieces r := Nat.add_le_add_right hsum _
      _ = pieces r * pieces r := by nlinarith
      _ ≤ r * r := Nat.mul_le_mul ht.2 ht.2
  have hlarge : pieces r < remainder r := by
    unfold remainder
    have h := lt_of_le_of_lt hbound (cubic_room r hr)
    omega
  have hnot : remainder r ∉ smallCoefficients r := by
    intro hc
    have := (small_mem.mp hc).2
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp [coefficients, hnot, hcard]
    omega
  · rw [coefficients, Finset.sum_insert hnot]
    unfold remainder
    have hroom := cubic_room r hr
    omega
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · omega
    · exact (small_mem.mp hc).1

lemma odd_card (r : ℕ) : (oddTerms r).card = (r + 1) / 2 := by
  have heq : oddTerms r = (Finset.range ((r + 1) / 2)).image (fun i => 2 * i + 1) := by
    ext j
    simp only [oddTerms, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, ⟨i, rfl⟩⟩
      exact ⟨i, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, ⟨i, by ring⟩⟩
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro i j h
    change 2 * i + 1 = 2 * j + 1 at h
    omega

/-- A label records the exponent of `Y` and its positive coefficient. -/
def labels (r : ℕ) : Finset (ℕ × ℕ) :=
  ((oddTerms r).erase 3).image (fun j => (j, 2 * r.choose j)) ∪
    (coefficients r).image (fun c => (3, c))

lemma labels_disjoint (r : ℕ) :
    Disjoint (((oddTerms r).erase 3).image (fun j => (j, 2 * r.choose j)))
      ((coefficients r).image (fun c => (3, c))) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hz'
  have := congrArg Prod.fst heq
  exact (Finset.mem_erase.mp hj).1 this.symm

lemma labels_card (r : ℕ) (hr : 6 ≤ r) : (labels r).card + 1 = r - 2 := by
  have hthree : 3 ∈ oddTerms r := by
    simp only [oddTerms, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by decide⟩
  rw [labels, Finset.card_union_of_disjoint (labels_disjoint r)]
  rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h)]
  rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.snd h)]
  rw [Finset.card_erase_of_mem hthree, odd_card, (coefficient_spec r hr).1]
  unfold pieces
  omega

lemma label_bounds (r : ℕ) (hr : 6 ≤ r) {z : ℕ × ℕ} (hz : z ∈ labels r) :
    1 ≤ z.1 ∧ z.1 ≤ r ∧ 0 < z.2 := by
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have ho := Finset.mem_filter.mp (Finset.mem_erase.mp hj).2
    have hj : j < r + 1 := Finset.mem_range.mp ho.1
    exact ⟨Odd.pos ho.2, by omega, mul_pos two_pos (Nat.choose_pos (by omega))⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨by omega, by omega, (coefficient_spec r hr).2.2 c hc⟩

lemma binomial_difference (r X Y : ℕ) (hYX : Y ≤ X) :
    (X + Y) ^ r = (X - Y) ^ r +
      ∑ j ∈ oddTerms r, 2 * r.choose j * X ^ (r - j) * Y ^ j := by
  have hi : ((X : ℤ) + Y) ^ r - ((X : ℤ) - Y) ^ r =
      ∑ j ∈ oddTerms r, 2 * (r.choose j : ℤ) * X ^ (r - j) * Y ^ j := by
    rw [sub_eq_add_neg (a := (X : ℤ)) (b := (Y : ℤ)), add_comm (X : ℤ) (Y : ℤ),
      add_pow, add_comm (X : ℤ) (-(Y : ℤ)), add_pow, ← Finset.sum_sub_distrib]
    rw [oddTerms, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases ho : Odd j
    · simp [ho, ho.neg_pow]
      ring
    · have he := (Nat.even_or_odd j).resolve_right ho
      simp [ho, he.neg_pow]
  have hi' : ((X : ℤ) + Y) ^ r = ((X : ℤ) - Y) ^ r +
      ∑ j ∈ oddTerms r, 2 * (r.choose j : ℤ) * X ^ (r - j) * Y ^ j := by
    linarith
  exact_mod_cast hi'

lemma labels_sum (r X Y : ℕ) (hr : 6 ≤ r) :
    (∑ z ∈ labels r, z.2 * X ^ (r - z.1) * Y ^ z.1) =
      ∑ j ∈ oddTerms r, 2 * r.choose j * X ^ (r - j) * Y ^ j := by
  have hthree : 3 ∈ oddTerms r := by
    simp only [oddTerms, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by decide⟩
  rw [labels, Finset.sum_union (labels_disjoint r)]
  rw [Finset.sum_image (by intro a ha b hb h; exact congrArg Prod.fst h),
    Finset.sum_image (by intro a ha b hb h; exact congrArg Prod.snd h)]
  simp only [Prod.fst, Prod.snd]
  rw [← Finset.sum_mul, ← Finset.sum_mul, (coefficient_spec r hr).2.1]
  exact Finset.sum_erase_add _ _ hthree


/-- A multiple of every coefficient, including a factor `2` to keep it above `1`. -/
def base (r : ℕ) : ℕ := 2 * ∏ z ∈ labels r, z.2

lemma base_positive (r : ℕ) (hr : 6 ≤ r) : 0 < base r := by
  exact mul_pos two_pos (Finset.prod_pos (fun z hz => (label_bounds r hr hz).2.2))

lemma coefficient_dvd_base {r : ℕ} {z : ℕ × ℕ} (hz : z ∈ labels r) : z.2 ∣ base r :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem Prod.snd hz) 2

lemma base_gt_one (r : ℕ) (hr : 6 ≤ r) : 1 < base r := by
  have h := Finset.prod_pos (fun z hz => (label_bounds r hr hz).2.2)
  unfold base
  omega

def term (r q : ℕ) (z : ℕ × ℕ) : ℕ :=
  z.2 * (q ^ r) ^ (r - z.1) * (base r ^ r) ^ z.1

def sumFamily (r q : ℕ) : Finset ℕ :=
  insert ((q ^ r - base r ^ r) ^ r) ((labels r).image (term r q))

lemma term_positive {r q : ℕ} (hr : 6 ≤ r) (hq : 0 < q)
    {z : ℕ × ℕ} (hz : z ∈ labels r) : 0 < term r q z := by
  have hB := base_positive r hr
  have hc := (label_bounds r hr hz).2.2
  unfold term
  positivity

lemma term_full {r q : ℕ} (hr : 6 ≤ r) {z : ℕ × ℕ} (hz : z ∈ labels r) :
    r.Full (term r q z) :=
  Erdos939.full_monomial_term (coefficient_dvd_base hz) (label_bounds r hr hz).1

lemma term_valuation {r q : ℕ} (hr : 6 ≤ r) (hq : q.Prime) (hBq : base r < q)
    {z : ℕ × ℕ} (hz : z ∈ labels r) :
    (term r q z).factorization q = r * (r - z.1) := by
  have hB := base_positive r hr
  have hc := (label_bounds r hr hz).2.2
  have hcq : ¬q ∣ z.2 := Nat.not_dvd_of_pos_of_lt hc
    ((Nat.le_of_dvd hB (coefficient_dvd_base hz)).trans_lt hBq)
  have hqB : ¬q ∣ base r := Nat.not_dvd_of_pos_of_lt hB hBq
  have hc0 : z.2 ≠ 0 := ne_of_gt hc
  have hB0 : base r ≠ 0 := ne_of_gt hB
  unfold term
  rw [Nat.factorization_mul (mul_ne_zero hc0 (pow_ne_zero _ (pow_ne_zero _ hq.ne_zero)))
      (pow_ne_zero _ (pow_ne_zero _ hB0)),
    Nat.factorization_mul hc0 (pow_ne_zero _ (pow_ne_zero _ hq.ne_zero))]
  have hcf : z.2.factorization q = 0 :=
    by rw [Nat.factorization_eq_zero_iff]; exact Or.inr (Or.inl hcq)
  have hBf : (base r).factorization q = 0 :=
    by rw [Nat.factorization_eq_zero_iff]; exact Or.inr (Or.inl hqB)
  simp [Nat.factorization_pow, hcf, hBf, hq.factorization_self, mul_comm]

lemma term_injective {r q : ℕ} (hr : 6 ≤ r) (hq : q.Prime) (hBq : base r < q) :
    Set.InjOn (term r q) (labels r) := by
  intro z hz w hw heq
  have hf := congrArg (fun n => n.factorization q) heq
  rw [term_valuation hr hq hBq hz, term_valuation hr hq hBq hw] at hf
  have hj : z.1 = w.1 := by
    have hs := Nat.mul_left_cancel (by omega : 0 < r) hf
    have hzle := (label_bounds r hr hz).2.1
    have hwle := (label_bounds r hr hw).2.1
    omega
  have hp : 0 < (q ^ r) ^ (r - z.1) * (base r ^ r) ^ z.1 := by
    have hB := base_positive r hr
    have hqpos := hq.pos
    positivity
  have hc : z.2 = w.2 := by
    apply Nat.mul_right_cancel hp
    simpa only [term, ← hj, mul_assoc] using heq
  exact Prod.ext hj hc

lemma first_coprime_base {r q : ℕ} (hr : 6 ≤ r) (hq : q.Prime) (hBq : base r < q) :
    Nat.Coprime ((q ^ r - base r ^ r) ^ r) (base r ^ r) := by
  have hcop : Nat.Coprime q (base r) :=
    hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (base_positive r hr) hBq)
  exact ((Nat.coprime_sub_self_left (Nat.pow_le_pow_left hBq.le r)).mpr
    (hcop.pow r r)).pow_left r

lemma first_not_mem {r q : ℕ} (hr : 6 ≤ r) (hq : q.Prime) (hBq : base r < q) :
    (q ^ r - base r ^ r) ^ r ∉ (labels r).image (term r q) := by
  intro hmem
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hmem
  have hd : base r ^ r ∣ (q ^ r - base r ^ r) ^ r := by
    rw [← heq]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (by
      have := (label_bounds r hr hz).1
      omega)) _
  have hone := Nat.eq_one_of_dvd_coprimes (first_coprime_base hr hq hBq) hd dvd_rfl
  have hlarge := (base_gt_one r hr).trans_le (Nat.le_self_pow (by omega : r ≠ 0) _)
  omega

lemma family_coprime {r q : ℕ} (hr : 6 ≤ r) (hq : q.Prime) (hBq : base r < q) :
    (sumFamily r q).Coprime := by
  have hcop : Nat.Coprime q (base r) :=
    hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (base_positive r hr) hBq)
  have hXY := hcop.pow r r
  have hle := Nat.pow_le_pow_left hBq.le r
  have hsubB := (Nat.coprime_sub_self_left hle).mpr hXY
  have hsubX : Nat.Coprime (q ^ r - base r ^ r) (q ^ r) := by
    exact ((Nat.coprime_self_sub_right hle).mpr hXY).symm
  have hone : (1, 2 * r.choose 1) ∈ labels r := by
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨1, ?_, rfl⟩
    simp [oddTerms]
    omega
  have hc := coefficient_dvd_base hone
  have hcY : 2 * r.choose 1 ∣ base r ^ r :=
    dvd_trans hc (dvd_pow_self _ (by omega : r ≠ 0))
  apply Erdos939.finset_coprime_of_mem_coprime
    (x := (q ^ r - base r ^ r) ^ r) (y := term r q (1, 2 * r.choose 1))
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, hone, rfl⟩)
  · exact (((hsubB.coprime_dvd_right hcY).mul_right (hsubX.pow_right (r - 1))).mul_right
      (hsubB.pow_right 1)).pow_left r

lemma family_spec {r q : ℕ} (hr : 6 ≤ r) (hq : q.Prime) (hBq : base r < q) :
    sumFamily r q ∈ Erdos939.Erdos939Sums r ∧
      (∑ s ∈ sumFamily r q, s) = (q ^ r + base r ^ r) ^ r := by
  have hnot := first_not_mem hr hq hBq
  have hsum : (∑ s ∈ sumFamily r q, s) = (q ^ r + base r ^ r) ^ r := by
    rw [sumFamily, Finset.sum_insert hnot, Finset.sum_image (term_injective hr hq hBq)]
    simp only [term]
    rw [labels_sum r (q ^ r) (base r ^ r) hr]
    exact (binomial_difference r (q ^ r) (base r ^ r) (Nat.pow_le_pow_left hBq.le r)).symm
  refine ⟨⟨?_, family_coprime hr hq hBq, ?_, ?_⟩, hsum⟩
  · rw [sumFamily, Finset.card_insert_of_notMem hnot,
      Finset.card_image_of_injOn (term_injective hr hq hBq)]
    exact labels_card r hr
  · rw [hsum]
    exact Nat.Full.pow_of_le le_rfl _
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact ⟨pow_pos (Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hBq (by omega))) _,
        Nat.Full.pow_of_le le_rfl _⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨term_positive hr hq.pos hz, term_full hr hz⟩

/-- Distinct prime parameters give distinct sums, hence distinct finite sets. -/
lemma family_injective (r : ℕ) (hr : 6 ≤ r) :
    Set.InjOn (sumFamily r) {q : ℕ | q.Prime ∧ base r < q} := by
  intro q hq p hp heq
  have hs := congrArg (fun S : Finset ℕ => ∑ s ∈ S, s) heq
  rw [(family_spec hr hq.1 hq.2).2, (family_spec hr hp.1 hp.2).2] at hs
  have hpow : Function.Injective (fun n : ℕ => n ^ r) := by
    apply StrictMono.injective
    intro a b hab
    exact Nat.pow_lt_pow_left hab (by omega)
  exact hpow (Nat.add_right_cancel (hpow hs))

lemma large_primes_infinite (B : ℕ) : {q : ℕ | q.Prime ∧ B < q}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro M
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (max (B + 1) (M + 1))
  refine ⟨q, ⟨hp, ?_⟩, ?_⟩
  · have := (Nat.le_max_left (B + 1) (M + 1)).trans hq
    omega
  · have := (Nat.le_max_right (B + 1) (M + 1)).trans hq
    omega

end General

/-- The source-compatible infinitude variant, for every exponent at least six. -/
theorem erdos_939.variants.infinite_of_six_le : ∀ r ≥ 6, (Erdos939Sums r).Infinite := by
  intro r hr
  have h := (General.large_primes_infinite (General.base r)).image
    (General.family_injective r hr)
  apply h.mono
  rintro S ⟨q, hq, rfl⟩
  exact (General.family_spec hr hq.1 hq.2).1


/-- **Erdős Problem 939, Variant `r = 5` (`erdos_939_five_nonempty`)**:
`Erdos939Sums 5` is nonempty, witnessed by
$2^5 \cdot 17^6 + 7^{11} + 2^5 \cdot 3^6 \cdot 7^8 = 3^7 \cdot 13^7$. -/
theorem erdos_939_five_nonempty : (Erdos939Sums 5).Nonempty := by
  let a₁ := 2 ^ 5 * 17 ^ 6
  let a₂ := 7 ^ 11
  let a₃ := 2 ^ 5 * 3 ^ 6 * 7 ^ 8
  refine ⟨{a₁, a₂, a₃}, ?_⟩
  obtain ⟨hcard, hsum⟩ := card_and_sum_three (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
    (by norm_num [a₁, a₂]) (by norm_num [a₂, a₃])
  have hsum_eq : ∑ s ∈ ({a₁, a₂, a₃} : Finset ℕ), s = 3 ^ 7 * 13 ^ 7 := by
    rw [hsum]
    norm_num [a₁, a₂, a₃]
  refine ⟨hcard, ?_, ?_, ?_⟩
  · exact finset_coprime_of_mem_coprime (x := a₁) (y := a₂) (by simp) (by simp) (by decide)
  · rw [hsum_eq]
    exact (Full.pow_of_le (by omega : 5 ≤ 7) 3).mul (Full.pow_of_le (by omega : 5 ≤ 7) 13)
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨by norm_num [a₁],
        (Full.pow_of_le (le_refl 5) 2).mul (Full.pow_of_le (by omega : 5 ≤ 6) 17)⟩
    · exact ⟨by norm_num [a₂], Full.pow_of_le (by omega : 5 ≤ 11) 7⟩
    · exact ⟨by norm_num [a₃],
        ((Full.pow_of_le (le_refl 5) 2).mul (Full.pow_of_le (by omega : 5 ≤ 6) 3)).mul
          (Full.pow_of_le (by omega : 5 ≤ 8) 7)⟩

/-- **Erdős Problem 939, Existence Examples (`erdos_939.variants.examples`)**:
There exists $r \ge 4$ such that `Erdos939Sums r` is nonempty. -/
theorem erdos_939.variants.examples : (∃ r ≥ 4, (Erdos939Sums r).Nonempty) :=
  ⟨5, by omega, erdos_939_five_nonempty⟩

/-- **Lander–Parkin Counterexample to Euler's Conjecture (`erdos_939.variants.euler`)**:
$27^5 + 84^5 + 110^5 + 133^5 = 144^5$. -/
theorem erdos_939.variants.euler : ¬ (∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
    (∀ s ∈ S, 0 < s) → ¬ (∃ q, ∑ s ∈ S, s ^ k = q ^ k)) := by
  push Not
  refine ⟨5, by omega, {27, 84, 110, 133}, by decide, by decide, 144, by norm_num⟩

end Erdos939

#print axioms Erdos939.erdos_939.variants.triples
#print axioms Erdos939.erdos_939.variants.finite
#print axioms Erdos939.erdos_939_five_nonempty
#print axioms Erdos939.erdos_939_six_infinite
#print axioms Erdos939.erdos_939_seven_infinite
#print axioms Erdos939.erdos_939_eight_infinite
#print axioms Erdos939.erdos_939.variants.seven
#print axioms Erdos939.erdos_939.variants.eight
#print axioms Erdos939.erdos_939.variants.examples
#print axioms Erdos939.erdos_939.variants.euler
#print axioms Erdos939.erdos_939.variants.infinite_of_six_le
