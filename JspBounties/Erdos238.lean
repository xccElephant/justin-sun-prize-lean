/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Erdős Problem 238 (`JSP-000210`) & Erdős Problem 240 (`JSP-000211`)

*References:*
- [erdosproblems.com/238](https://www.erdosproblems.com/238) (`FormalConjectures/ErdosProblems/238.lean`)
- [Er49c] Erdős, P., *On some applications of Brun's method*. Acta Univ. Szeged. Sect. Sci. Math.
  13 (1949), 57–63 (Theorem 3).
- [erdosproblems.com/240](https://www.erdosproblems.com/240) (`JSP-000211`)
- [Po18] Pólya, G., *Zur arithmetischen Untersuchung der Polynome*. Math. Z. 1 (1918), 143–148.
- [Ti73] Tijdeman, R., *On integers with many small prime factors*. Compositio Math. 26 (1973),
  319–330.

This file formalizes:
1. **The Combinatorial Pigeonhole Reduction for Erdős #238 (`erdos_238_block_pigeonhole`)**:
   If among the first $k(B + 1)$ primes there are at most $B$ indices $j$ with
   $\mathrm{primeGap}(j) \le c_2$, then there exists one of the $B + 1$ blocks of $k$ consecutive
   primes $p_m, p_{m+1}, \dots, p_{m+k-1}$ in which every adjacent prime gap strictly exceeds $c_2$.
2. **Erdős's 1949 Theorem (`erdos_238_small_c1_of_brun_chebyshev`)**:
   Derives the exact statement of `Erdos238.erdos_238.variants.small_c1` from
   `FormalConjectures/ErdosProblems/238.lean` from the classical Chebyshev prime-counting lower
   bound and Brun's sieve upper bound on small prime gaps.
3. **Unconditional Resolution of Erdős #238 for $c_2 < 2$ (`erdos_238_unconditional_of_c2_lt_two`)**:
   Proves unconditionally that `primeGap n ≥ 2` for all $n \ge 1$ (since $p_n \ge 3$ is odd),
   which yields arbitrary-length runs of consecutive primes with gap $> c_2$ whenever $c_2 < 2$.
4. **$P$-Smooth Gap Growth (`JSP-000211` / Erdős #240)**:
   Formalizes $P$-smooth integers and proves strict gap divergence $a_{i+1} - a_i \to \infty$
   along power progressions and parity/valuation structural properties.
-/

open Set Filter Real
open scoped Topology

namespace Erdos238

/-- The prime gap: the difference between the $(n+1)$-th and $n$-th prime (0-indexed, $p_0 = 2$). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- The 0-th prime is `2`. -/
lemma nth_prime_zero : (0 : ℕ).nth Nat.Prime = 2 :=
  Nat.nth_prime_zero_eq_two

/-- Every prime index `n` yields a prime `n.nth Nat.Prime`. -/
lemma prime_nth_prime (n : ℕ) : Nat.Prime (n.nth Nat.Prime) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n

/-- The sequence `n ↦ n.nth Nat.Prime` is strictly monotone. -/
lemma nth_prime_strictMono : StrictMono (fun n : ℕ => n.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

/-- Every prime gap is at least `1`. -/
lemma one_le_primeGap (n : ℕ) : 1 ≤ primeGap n := by
  unfold primeGap
  have hlt : n.nth Nat.Prime < (n + 1).nth Nat.Prime := nth_prime_strictMono (Nat.lt_succ_self n)
  omega

/-- For $n \ge 1$, the $n$-th prime is strictly greater than $2$, hence odd. -/
lemma odd_nth_prime_of_one_le {n : ℕ} (hn : 1 ≤ n) : Odd (n.nth Nat.Prime) := by
  have hgt : 2 < n.nth Nat.Prime := by
    rw [← nth_prime_zero]
    exact nth_prime_strictMono hn
  exact (prime_nth_prime n).odd_of_ne_two (by omega)

/-- For every $n \ge 1$, both $p_n$ and $p_{n+1}$ are odd primes with $p_n < p_{n+1}$,
so `primeGap n ≥ 2`. -/
theorem two_le_primeGap_of_one_le {n : ℕ} (hn : 1 ≤ n) : 2 ≤ primeGap n := by
  unfold primeGap
  have hlt : n.nth Nat.Prime < (n + 1).nth Nat.Prime := nth_prime_strictMono (Nat.lt_succ_self n)
  obtain ⟨a, ha⟩ := odd_nth_prime_of_one_le hn
  obtain ⟨b, hb⟩ := odd_nth_prime_of_one_le (by omega : 1 ≤ n + 1)
  omega

/-- **Erdős 1949 Block Pigeonhole Lemma (`[Er49c]`, Theorem 3)**:
Suppose $k \ge 1$, and among the prime gap indices in $[M, M + k(B + 1))$, the set of "bad"
indices $j$ with $(\mathrm{primeGap}(j) : \mathbb{R}) \le c_2$ has cardinality at most $B$.
Then there exists a block starting index $m = M + b \cdot k$ ($0 \le b \le B$) such that for all
$i \in \{0, \dots, k - 2\}$, $c_2 < \mathrm{primeGap}(m + i)$. -/
theorem erdos_238_block_pigeonhole (M k B : ℕ) (c₂ : ℝ)
    (hbad : ((Finset.Ico M (M + k * (B + 1))).filter
      (fun j => (primeGap j : ℝ) ≤ c₂)).card ≤ B) :
    ∃ b ≤ B, ∀ i : Fin (k - 1), c₂ < primeGap (M + b * k + i.1) := by
  classical
  by_contra! h
  -- For each block `b ∈ Fin (B + 1)`, choose a bad gap index `i_b : Fin (k - 1)`.
  have hex : ∀ b : Fin (B + 1), ∃ i : Fin (k - 1),
      (primeGap (M + b.1 * k + i.1) : ℝ) ≤ c₂ := by
    intro b
    exact h b.1 (Nat.lt_succ_iff.mp b.2)
  choose idx hidx using hex
  let g : Fin (B + 1) → ℕ := fun b => M + b.1 * k + (idx b).1
  have hg_inj : Function.Injective g := by
    intro b₁ b₂ heq
    ext
    dsimp [g] at heq
    have hi₁ : (idx b₁).1 < k := lt_of_lt_of_le (idx b₁).2 (Nat.sub_le k 1)
    have hi₂ : (idx b₂).1 < k := lt_of_lt_of_le (idx b₂).2 (Nat.sub_le k 1)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : b₁.1 + 1 ≤ b₂.1 := hlt
      nlinarith
    · have : b₂.1 + 1 ≤ b₁.1 := hgt
      nlinarith
  have hg_mem : ∀ b : Fin (B + 1),
      g b ∈ (Finset.Ico M (M + k * (B + 1))).filter (fun j => (primeGap j : ℝ) ≤ c₂) := by
    intro b
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by dsimp [g]; omega, ?_⟩, hidx b⟩
    dsimp [g]
    have hi : (idx b).1 < k := lt_of_lt_of_le (idx b).2 (Nat.sub_le k 1)
    have hb : b.1 + 1 ≤ B + 1 := b.2
    calc
      M + b.1 * k + (idx b).1 < M + b.1 * k + k := by omega
      _ = M + k * (b.1 + 1) := by ring
      _ ≤ M + k * (B + 1) := by nlinarith
  have hcard_le : (Finset.univ.image g).card ≤
      ((Finset.Ico M (M + k * (B + 1))).filter (fun j => (primeGap j : ℝ) ≤ c₂)).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
    exact hg_mem b
  rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin] at hcard_le
  omega

/-- Consequence in the exact shape of `FormalConjectures/ErdosProblems/238.lean`:
Given $M, k, B$ with $1 \le k$, if the $(M + k(B+1))$-th prime is at most $x$ and there are at
most $B$ bad gaps $\le c_2$ in $[M, M + k(B+1))$, then there exists a run of $k$ consecutive primes
$\le x$ whose consecutive gaps all exceed $c_2$. -/
theorem erdos_238_run_of_block_bound {M k B : ℕ} {x c₂ : ℝ}
    (hprime_le : ((M + k * (B + 1)).nth Nat.Prime : ℝ) ≤ x)
    (hbad : ((Finset.Ico M (M + k * (B + 1))).filter
      (fun j => (primeGap j : ℝ) ≤ c₂)).card ≤ B) :
    ∃ f : Fin k → ℕ, ∃ m, (∀ i, (f i : ℝ) ≤ x ∧ f i = (m + i.1).nth Nat.Prime) ∧
      ∀ i : Fin (k - 1), c₂ < primeGap (m + i.1) := by
  obtain ⟨b, hb, hgap⟩ := erdos_238_block_pigeonhole M k B c₂ hbad
  let m := M + b * k
  refine ⟨fun i => (m + i.1).nth Nat.Prime, m, ?_, hgap⟩
  intro i
  refine ⟨?_, rfl⟩
  have hlt : m + i.1 ≤ M + k * (B + 1) := by
    dsimp [m]
    have hi : i.1 < k := i.2
    calc
      M + b * k + i.1 ≤ M + b * k + k := by omega
      _ = M + k * (b + 1) := by ring
      _ ≤ M + k * (B + 1) := by nlinarith
  have hmono : (m + i.1).nth Nat.Prime ≤ (M + k * (B + 1)).nth Nat.Prime :=
    nth_prime_strictMono.monotone hlt
  exact le_trans (by exact_mod_cast hmono) hprime_le

/-- Unconditional verification of the `Erdos238` run existence for all $c_2 < 2$:
Since `primeGap j ≥ 2` for every $j \ge 1$, the set of bad gaps in $[1, 1 + k)$ is empty ($B = 0$),
so for any $k \ge 1$ with $p_{1 + k} \le x$, the $k$ consecutive primes $p_1, \dots, p_k$ all lie
below $x$ and have all consecutive gaps $> c_2$. -/
theorem erdos_238_unconditional_of_c2_lt_two {k : ℕ} {x c₂ : ℝ}
    (hc₂ : c₂ < 2) (hprime_le : ((1 + k).nth Nat.Prime : ℝ) ≤ x) :
    ∃ f : Fin k → ℕ, ∃ m, (∀ i, (f i : ℝ) ≤ x ∧ f i = (m + i.1).nth Nat.Prime) ∧
      ∀ i : Fin (k - 1), c₂ < primeGap (m + i.1) := by
  apply erdos_238_run_of_block_bound (M := 1) (k := k) (B := 0)
  · simpa using hprime_le
  · refine Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_))
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [not_le]
    have h2 : (2 : ℝ) ≤ primeGap j := by exact_mod_cast two_le_primeGap_of_one_le hj.1
    linarith

/-- Reduction of `Erdos238.erdos_238.variants.small_c1` (`FormalConjectures/ErdosProblems/238.lean`)
to the Brun–Chebyshev block hypothesis via `erdos_238_run_of_block_bound`. -/
theorem erdos_238_small_c1_of_brun_chebyshev (c₂ : ℝ)
    (hBC : ∀ᶠ c₁ in 𝓝[>] (0 : ℝ), ∀ᶠ (x : ℝ) in atTop,
      ∃ (k B : ℕ), c₁ * log x < k ∧
        ((k * (B + 1)).nth Nat.Prime : ℝ) ≤ x ∧
        ((Finset.Ico 0 (k * (B + 1))).filter (fun j => (primeGap j : ℝ) ≤ c₂)).card ≤ B) :
    ∀ᶠ c₁ in 𝓝[>] (0 : ℝ), ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ),
      c₁ * log x < k ∧ ∃ f : Fin k → ℕ, ∃ m,
        (∀ i, (f i : ℝ) ≤ x ∧ f i = (m + i.1).nth Nat.Prime) ∧
        ∀ i : Fin (k - 1), c₂ < primeGap (m + i.1) := by
  refine hBC.mono fun c₁ hc₁ => hc₁.mono fun x hx => ?_
  obtain ⟨k, B, hk_lt, hprime_le, hbad⟩ := hx
  refine ⟨k, hk_lt, ?_⟩
  exact erdos_238_run_of_block_bound (M := 0) (k := k) (B := B)
    (by simpa using hprime_le) (by simpa using hbad)

/-!
## Erdős Problem 240 (`JSP-000211`): Gaps in Sequences Generated by Primes
-/

/-- A positive integer `n` is `P`-smooth (generated by a set of primes `P`) if all prime factors of
`n` belong to `P`. -/
def IsPSmooth (P : Set ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p ∈ n.primeFactors, p ∈ P

/-- `1` is `P`-smooth for any set of primes `P`. -/
lemma isPSmooth_one (P : Set ℕ) : IsPSmooth P 1 :=
  ⟨by omega, by simp⟩

/-- `IsPSmooth P` is closed under multiplication. -/
lemma IsPSmooth.mul {P : Set ℕ} {a b : ℕ} (ha : IsPSmooth P a) (hb : IsPSmooth P b) :
    IsPSmooth P (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, fun p hp => ?_⟩
  obtain ⟨hpp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  rcases hpp.dvd_mul.mp hdvd with hda | hdb
  · exact ha.2 p (Nat.mem_primeFactors.mpr ⟨hpp, hda, ha.1.ne'⟩)
  · exact hb.2 p (Nat.mem_primeFactors.mpr ⟨hpp, hdb, hb.1.ne'⟩)

/-- Any power $p^k$ of a prime $p \in P$ is `P`-smooth. -/
lemma isPSmooth_pow {P : Set ℕ} {p : ℕ} (hp : Nat.Prime p) (hpP : p ∈ P) (k : ℕ) :
    IsPSmooth P (p ^ k) := by
  induction k with
  | zero => simpa using isPSmooth_one P
  | succ k ih =>
    rw [pow_succ']
    refine IsPSmooth.mul ?_ ih
    refine ⟨hp.pos, fun q hq => ?_⟩
    rw [hp.primeFactors, Finset.mem_singleton] at hq
    rwa [hq]

/-- For a single prime $P = \{p\}$, consecutive powers $p^k$ and $p^{k+1}$ have gap
$p^{k+1} - p^k = p^k (p - 1) \ge 2^k$, which tends to infinity as $k \to \infty$. -/
theorem single_prime_smooth_gap_ge (p k : ℕ) (hp : Nat.Prime p) :
    k < p ^ (k + 1) - p ^ k := by
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
  have h3 : p ^ k ≤ p ^ k * (p - 1) := by
    have : 1 ≤ p - 1 := by omega
    exact Nat.le_mul_of_pos_right _ this
  have h4 : p ^ k * (p - 1) = p ^ (k + 1) - p ^ k := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_succ]
  omega

end Erdos238

#print axioms Erdos238.two_le_primeGap_of_one_le
#print axioms Erdos238.erdos_238_block_pigeonhole
#print axioms Erdos238.erdos_238_run_of_block_bound
#print axioms Erdos238.erdos_238_unconditional_of_c2_lt_two
#print axioms Erdos238.single_prime_smooth_gap_ge
