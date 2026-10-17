import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 365 (JSP-000301): Consecutive Powerful Numbers

*Problem Statement (JSP-000301 / Erdős Problem 365, Part i):*
If two consecutive positive integers $n$ and $n+1$ are powerful, must at least one of them be a
perfect square?

*Resolution:*
No.
1. **Golomb (1970)** gave the first counterexample:
   $$12167 = 23^3 \quad \text{and} \quad 12168 = 2^3 \cdot 3^2 \cdot 13^2 = 2^3 \cdot 39^2$$
   are consecutive powerful numbers, and neither is a perfect square.
2. **Walker (1976)** proved that there are **infinitely many** pairs $(n, n+1)$ of consecutive
   powerful numbers such that neither $n$ nor $n+1$ is a perfect square. Specifically, for any
   primes $p, q$ and any positive integer solution $(x, y)$ to the Diophantine equation
   $$p^3 x^2 - q^3 y^2 = 1,$$
   the pair $(n, n+1) = (q^3 y^2, p^3 x^2)$ consists of consecutive powerful numbers, neither of
   which is a square. Moreover, given one solution $(x, y)$, the cubic Pell-type map
   $$(x', y') = (p^3 x^3 + 3 q^3 x y^2,\; 3 p^3 x^2 y + q^3 y^3)$$
   satisfies
   $$p^3 (x')^2 - q^3 (y')^2 = (p^3 x^2 - q^3 y^2)^3 = 1$$
   and produces a strictly increasing infinite sequence of solutions.
   - Starting from Golomb's base solution $(p, q, x_0, y_0) = (2, 23, 39, 1)$ to
     $2^3 x^2 - 23^3 y^2 = 1$, this generates an infinite family of non-square consecutive powerful
     pairs beginning with $(12167, 12168)$.
   - Starting from Walker's base solution $(p, q, x_0, y_0) = (7, 3, 376766, 1342879)$ to
     $7^3 x^2 - 3^3 y^2 = 1$, this generates Walker's (1976) infinite family beginning with
     $(48689748233307, 48689748233308)$.

*References:*
- [Go70] Golomb, S. W., *Powerful numbers*. Amer. Math. Monthly 77 (1970), 848–855.
- [Wa76] Walker, D. T., *Consecutive integer pairs of powerful numbers and related Diophantine
  equations*. Fibonacci Quart. 14 (1976), 111–116.
- [Gu04] Guy, R. K., *Unsolved problems in number theory* (2004), Problem B16.
-/

namespace Nat

/-- A natural number $n$ is $k$-full if $p^k \mid n$ for every prime factor $p$ of $n$. -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- A natural number $n$ is *powerful* (or $2$-full / squareful) if $p^2 \mid n$ for every prime
factor $p$ of $n$. -/
abbrev Powerful : ℕ → Prop := (2).Full

end Nat

namespace Erdos365

/-! ## General Properties of Powerful Numbers and Non-Squares -/

/-- Every square $m^2$ is powerful. -/
theorem powerful_sq (m : ℕ) : Nat.Powerful (m ^ 2) := by
  intro p hp
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  exact pow_dvd_pow_of_dvd (hprime.dvd_of_dvd_pow hdvd) 2

/-- Every cube $m^3$ is powerful. -/
theorem powerful_cube (m : ℕ) : Nat.Powerful (m ^ 3) := by
  intro p hp
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hp_m : p ∣ m := hprime.dvd_of_dvd_pow hdvd
  exact dvd_trans (pow_dvd_pow p (by decide : 2 ≤ 3)) (pow_dvd_pow_of_dvd hp_m 3)

/-- The product of two powerful numbers is powerful. -/
theorem powerful_mul {a b : ℕ} (ha : Nat.Powerful a) (hb : Nat.Powerful b) :
    Nat.Powerful (a * b) := by
  intro p hp
  obtain ⟨hprime, hdvd, hab⟩ := Nat.mem_primeFactors.mp hp
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
  rcases hprime.dvd_mul.mp hdvd with hpa | hpb
  · exact dvd_mul_of_dvd_left (ha p (Nat.mem_primeFactors.mpr ⟨hprime, hpa, ha0⟩)) b
  · exact dvd_mul_of_dvd_right (hb p (Nat.mem_primeFactors.mpr ⟨hprime, hpb, hb0⟩)) a

/-- Any number of the form $a^3 b^2$ is powerful. -/
theorem powerful_cube_mul_sq (a b : ℕ) : Nat.Powerful (a ^ 3 * b ^ 2) :=
  powerful_mul (powerful_cube a) (powerful_sq b)

/-- For any prime $p$ and any positive integer $u$, $p u^2$ is never a perfect square. -/
theorem prime_mul_sq_ne_sq {p : ℕ} (hp : p.Prime) :
    ∀ u : ℕ, 0 < u → ∀ r : ℕ, p * u ^ 2 ≠ r ^ 2 := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu r hEq
    have hp_dvd_r2 : p ∣ r ^ 2 := ⟨u ^ 2, by linarith⟩
    have hp_dvd_r : p ∣ r := hp.dvd_of_dvd_pow hp_dvd_r2
    obtain ⟨s, rfl⟩ := hp_dvd_r
    have hu2 : u ^ 2 = p * s ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc
        p * u ^ 2 = (p * s) ^ 2 := hEq
        _ = p * (p * s ^ 2) := by ring
    have hp_dvd_u2 : p ∣ u ^ 2 := ⟨s ^ 2, hu2⟩
    have hp_dvd_u : p ∣ u := hp.dvd_of_dvd_pow hp_dvd_u2
    obtain ⟨v, rfl⟩ := hp_dvd_u
    have hv_pos : 0 < v := Nat.pos_of_mul_pos_left hu
    have hv_lt : v < p * v := by
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith
    have hv_eq : p * v ^ 2 = s ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc
        p * (p * v ^ 2) = (p * v) ^ 2 := by ring
        _ = p * s ^ 2 := hu2
    exact ih v hv_lt hv_pos s hv_eq

/-- For any prime $p$ and positive integer $y$, $p^3 y^2$ is not a perfect square. -/
theorem not_isSquare_prime_cube_mul_sq {p y : ℕ} (hp : p.Prime) (hy : 0 < y) :
    ¬ IsSquare (p ^ 3 * y ^ 2) := by
  rintro ⟨r, hr⟩
  have hpy : 0 < p * y := Nat.mul_pos hp.pos hy
  have hEq : p * (p * y) ^ 2 = r ^ 2 := by
    calc
      p * (p * y) ^ 2 = p ^ 3 * y ^ 2 := by ring
      _ = r * r := hr
      _ = r ^ 2 := by ring
  exact prime_mul_sq_ne_sq hp (p * y) hpy r hEq

/-! ## Golomb's Counterexample (1970) and Erdős Problem 365 Part (i) -/

/-- Golomb's consecutive powerful pair $12167 = 23^3$ and $12168 = 2^3 \cdot 39^2 = 2^3 \cdot 3^2 \cdot 13^2$.
Neither number is a perfect square [Go70]. -/
theorem golomb_pair :
    Nat.Powerful 12167 ∧ Nat.Powerful 12168 ∧
      ¬ IsSquare (12167 : ℕ) ∧ ¬ IsSquare (12168 : ℕ) := by
  have h12167 : (12167 : ℕ) = 23 ^ 3 * 1 ^ 2 := by norm_num
  have h12168 : (12168 : ℕ) = 2 ^ 3 * 39 ^ 2 := by norm_num
  have hp23 : Nat.Prime 23 := by decide
  have hp2 : Nat.Prime 2 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h12167]; exact powerful_cube_mul_sq 23 1
  · rw [h12168]; exact powerful_cube_mul_sq 2 39
  · rw [h12167]; exact not_isSquare_prime_cube_mul_sq hp23 (by norm_num)
  · rw [h12168]; exact not_isSquare_prime_cube_mul_sq hp2 (by norm_num)

/-- **Erdős Problem 365, Part (i) (JSP-000301)**:
It is false that for every pair of consecutive positive powerful numbers $n$ and $n+1$, at least
one of $n$ or $n+1$ must be a perfect square. -/
theorem erdos_365.parts.i :
    ¬ ∀ n : ℕ, 0 < n → Nat.Powerful n → Nat.Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  obtain ⟨hA, hB, hnA, hnB⟩ := golomb_pair
  rcases h 12167 (by norm_num) hA hB with hs | hs
  · exact hnA hs
  · exact hnB hs

/-! ## Walker's (1976) Infinite Family of Non-Square Consecutive Powerful Pairs -/

/-- Cubic Pell-type step for the Diophantine equation $A x^2 - B y^2 = 1$:
$(x, y) \mapsto (A x^3 + 3 B x y^2,\; 3 A x^2 y + B y^3)$. -/
def pellCubeStep (A B : ℕ) (xy : ℕ × ℕ) : ℕ × ℕ :=
  (A * xy.1 ^ 3 + 3 * B * xy.1 * xy.2 ^ 2, 3 * A * xy.1 ^ 2 * xy.2 + B * xy.2 ^ 3)

/-- Iterated cubic Pell-type solutions starting from $(x_0, y_0)$. -/
def pellCubeSeq (A B x₀ y₀ : ℕ) : ℕ → ℕ × ℕ
  | 0 => (x₀, y₀)
  | k + 1 => pellCubeStep A B (pellCubeSeq A B x₀ y₀ k)

/-- Polynomial identity in $\mathbb{Z}$:
$A (A x^3 + 3 B x y^2)^2 - B (3 A x^2 y + B y^3)^2 = (A x^2 - B y^2)^3$. -/
theorem pellCubeStep_zmod_identity (A B x y : ℤ) :
    A * (A * x ^ 3 + 3 * B * x * y ^ 2) ^ 2 -
      B * (3 * A * x ^ 2 * y + B * y ^ 3) ^ 2 =
      (A * x ^ 2 - B * y ^ 2) ^ 3 := by
  ring

/-- If $A x^2 = B y^2 + 1$ in $\mathbb{N}$, then `pellCubeStep A B (x, y)` also satisfies
$A (x')^2 = B (y')^2 + 1$. -/
theorem pellCubeStep_preserves_eq {A B : ℕ} {xy : ℕ × ℕ}
    (h : A * xy.1 ^ 2 = B * xy.2 ^ 2 + 1) :
    A * (pellCubeStep A B xy).1 ^ 2 = B * (pellCubeStep A B xy).2 ^ 2 + 1 := by
  have hcast : (A : ℤ) * (xy.1 : ℤ) ^ 2 = (B : ℤ) * (xy.2 : ℤ) ^ 2 + 1 := by
    exact_mod_cast h
  have hz : (A : ℤ) * (xy.1 : ℤ) ^ 2 - (B : ℤ) * (xy.2 : ℤ) ^ 2 = 1 := by
    linarith
  have hstep := pellCubeStep_zmod_identity (A : ℤ) (B : ℤ) (xy.1 : ℤ) (xy.2 : ℤ)
  rw [hz, one_pow] at hstep
  have hstep' :
      (A : ℤ) * ((pellCubeStep A B xy).1 : ℤ) ^ 2 =
        (B : ℤ) * ((pellCubeStep A B xy).2 : ℤ) ^ 2 + 1 := by
    dsimp [pellCubeStep]
    linarith
  exact_mod_cast hstep'

/-- Every term in `pellCubeSeq A B x₀ y₀` satisfies $A x_k^2 = B y_k^2 + 1$ whenever $(x_0, y_0)$
does. -/
theorem pellCubeSeq_eq {A B x₀ y₀ : ℕ} (h₀ : A * x₀ ^ 2 = B * y₀ ^ 2 + 1) (k : ℕ) :
    A * (pellCubeSeq A B x₀ y₀ k).1 ^ 2 = B * (pellCubeSeq A B x₀ y₀ k).2 ^ 2 + 1 := by
  induction k with
  | zero => exact h₀
  | succ k ih => exact pellCubeStep_preserves_eq ih

/-- Positivity of `pellCubeSeq` coordinates when $A, B, x_0, y_0 > 0$. -/
theorem pellCubeSeq_pos {A B x₀ y₀ : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) (k : ℕ) :
    0 < (pellCubeSeq A B x₀ y₀ k).1 ∧ 0 < (pellCubeSeq A B x₀ y₀ k).2 := by
  induction k with
  | zero => exact ⟨hx₀, hy₀⟩
  | succ k ih =>
    rcases ih with ⟨hx, hy⟩
    dsimp [pellCubeSeq, pellCubeStep]
    constructor <;> positivity

/-- The second coordinate of `pellCubeSeq` is strictly increasing when $A, B, x_0, y_0 > 0$. -/
theorem pellCubeSeq_snd_strictMono {A B x₀ y₀ : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    StrictMono (fun k => (pellCubeSeq A B x₀ y₀ k).2) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  obtain ⟨hx, hy⟩ := pellCubeSeq_pos hA hB hx₀ hy₀ k
  dsimp [pellCubeSeq, pellCubeStep]
  have h1 : 0 < 3 * A * (pellCubeSeq A B x₀ y₀ k).1 ^ 2 * (pellCubeSeq A B x₀ y₀ k).2 := by
    positivity
  have hB2 : 0 < B * (pellCubeSeq A B x₀ y₀ k).2 ^ 2 := by
    positivity
  have h2 : (pellCubeSeq A B x₀ y₀ k).2 ≤ B * (pellCubeSeq A B x₀ y₀ k).2 ^ 3 := by
    nlinarith
  omega

/-- General parametric theorem: if $p, q$ are primes and $p^3 x_0^2 = q^3 y_0^2 + 1$ with
$x_0, y_0 > 0$, then $n_k = q^3 y_k^2$ gives a strictly increasing sequence of positive integers
such that $n_k$ and $n_k + 1$ are both powerful and neither is a perfect square. -/
theorem parametric_nonSquare_powerful_family {p q x₀ y₀ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (h₀ : p ^ 3 * x₀ ^ 2 = q ^ 3 * y₀ ^ 2 + 1) :
    let n : ℕ → ℕ := fun k => q ^ 3 * (pellCubeSeq (p ^ 3) (q ^ 3) x₀ y₀ k).2 ^ 2
    StrictMono n ∧
      ∀ k : ℕ, 0 < n k ∧ Nat.Powerful (n k) ∧ Nat.Powerful (n k + 1) ∧
        ¬ IsSquare (n k) ∧ ¬ IsSquare (n k + 1) := by
  intro n
  have hp3 : 0 < p ^ 3 := pow_pos hp.pos 3
  have hq3 : 0 < q ^ 3 := pow_pos hq.pos 3
  refine ⟨?_, fun k => ?_⟩
  · intro i j hij
    have hy_lt := pellCubeSeq_snd_strictMono hp3 hq3 hx₀ hy₀ hij
    have hy_pos := (pellCubeSeq_pos hp3 hq3 hx₀ hy₀ i).2
    dsimp [n]
    have hsq_lt :
        (pellCubeSeq (p ^ 3) (q ^ 3) x₀ y₀ i).2 ^ 2 <
          (pellCubeSeq (p ^ 3) (q ^ 3) x₀ y₀ j).2 ^ 2 := by
      nlinarith
    exact Nat.mul_lt_mul_of_pos_left hsq_lt hq3
  · obtain ⟨hx, hy⟩ := pellCubeSeq_pos hp3 hq3 hx₀ hy₀ k
    have hEq := pellCubeSeq_eq h₀ k
    have hn1 : n k + 1 = p ^ 3 * (pellCubeSeq (p ^ 3) (q ^ 3) x₀ y₀ k).1 ^ 2 := by
      dsimp [n]
      omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp [n]; positivity
    · dsimp [n]; exact powerful_cube_mul_sq q _
    · rw [hn1]; exact powerful_cube_mul_sq p _
    · dsimp [n]; exact not_isSquare_prime_cube_mul_sq hq hy
    · rw [hn1]; exact not_isSquare_prime_cube_mul_sq hp hx

/-- **Walker's (1976) base example**:
$48689748233307 = 3^3 \cdot 1342879^2$ and $48689748233308 = 7^3 \cdot 376766^2$ are consecutive
powerful numbers, neither of which is a perfect square. -/
theorem walker_base_pair :
    Nat.Powerful 48689748233307 ∧ Nat.Powerful 48689748233308 ∧
      ¬ IsSquare (48689748233307 : ℕ) ∧ ¬ IsSquare (48689748233308 : ℕ) := by
  have hA : (48689748233307 : ℕ) = 3 ^ 3 * 1342879 ^ 2 := by norm_num
  have hB : (48689748233308 : ℕ) = 7 ^ 3 * 376766 ^ 2 := by norm_num
  have hp3 : Nat.Prime 3 := by decide
  have hp7 : Nat.Prime 7 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA]; exact powerful_cube_mul_sq 3 1342879
  · rw [hB]; exact powerful_cube_mul_sq 7 376766
  · rw [hA]; exact not_isSquare_prime_cube_mul_sq hp3 (by norm_num)
  · rw [hB]; exact not_isSquare_prime_cube_mul_sq hp7 (by norm_num)

/-- **Walker's (1976) Theorem on $7^3 x^2 - 3^3 y^2 = 1$**:
The equation $7^3 x^2 = 3^3 y^2 + 1$ generates a strictly increasing infinite sequence of
non-square consecutive powerful pairs $n_k = 3^3 y_k^2$. -/
def walkerSeq (k : ℕ) : ℕ :=
  3 ^ 3 * (pellCubeSeq (7 ^ 3) (3 ^ 3) 376766 1342879 k).2 ^ 2

theorem walkerSeq_properties :
    StrictMono walkerSeq ∧
      ∀ k : ℕ, 0 < walkerSeq k ∧ Nat.Powerful (walkerSeq k) ∧ Nat.Powerful (walkerSeq k + 1) ∧
        ¬ IsSquare (walkerSeq k) ∧ ¬ IsSquare (walkerSeq k + 1) := by
  exact parametric_nonSquare_powerful_family
    (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 3)
    (by norm_num : 0 < 376766)
    (by norm_num : 0 < 1342879)
    (by norm_num : 7 ^ 3 * 376766 ^ 2 = 3 ^ 3 * 1342879 ^ 2 + 1)

/-- **Golomb–Walker Infinite Family on $2^3 x^2 - 23^3 y^2 = 1$**:
Starting from Golomb's pair $(12167, 12168)$, the equation $2^3 x^2 = 23^3 y^2 + 1$ also generates
a strictly increasing infinite sequence of non-square consecutive powerful pairs. -/
def golombWalkerSeq (k : ℕ) : ℕ :=
  23 ^ 3 * (pellCubeSeq (2 ^ 3) (23 ^ 3) 39 1 k).2 ^ 2

theorem golombWalkerSeq_properties :
    StrictMono golombWalkerSeq ∧
      ∀ k : ℕ, 0 < golombWalkerSeq k ∧ Nat.Powerful (golombWalkerSeq k) ∧
        Nat.Powerful (golombWalkerSeq k + 1) ∧
        ¬ IsSquare (golombWalkerSeq k) ∧ ¬ IsSquare (golombWalkerSeq k + 1) := by
  exact parametric_nonSquare_powerful_family
    (by decide : Nat.Prime 2)
    (by decide : Nat.Prime 23)
    (by norm_num : 0 < 39)
    (by norm_num : 0 < 1)
    (by norm_num : 2 ^ 3 * 39 ^ 2 = 23 ^ 3 * 1 ^ 2 + 1)

/-- **Infinitely Many Counterexamples to Erdős Problem 365 Part (i)**:
The set of positive integers $n$ such that both $n$ and $n+1$ are powerful and neither is a perfect
square is infinite. -/
theorem infinite_nonSquare_consecutive_powerful :
    {n : ℕ | 0 < n ∧ Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1)}.Infinite := by
  obtain ⟨hMono, hProps⟩ := walkerSeq_properties
  exact Set.infinite_of_injective_forall_mem hMono.injective hProps

#print axioms golomb_pair
#print axioms erdos_365.parts.i
#print axioms walker_base_pair
#print axioms walkerSeq_properties
#print axioms golombWalkerSeq_properties
#print axioms infinite_nonSquare_consecutive_powerful

end Erdos365
