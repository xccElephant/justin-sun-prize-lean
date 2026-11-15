/-
Copyright 2026 Chucheng Xiang (@xccElephant).

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 983 (JSP-000816)

Complete, unconditional Lean 4 formalization resolving:
1. `erdos_983.variants.upper_bound`: the Erdős–Straus exact upper bound
   $$f(\pi(n) + 1, n) \le 2\pi(\lfloor\sqrt{n}\rfloor) + 1 \quad (\forall n \in \mathbb{N}).$$
2. `erdos_983.variants.upper_bound_attained_frequently` and
   `erdos_983.variants.infinite_exact_equality`: infinitely many integers $n \ge 2$ attain exact
   equality $f(\pi(n) + 1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1$.
3. `erdos_983.parts.i`: negative resolution of the first question of Erdős and Straus [Er70b]
   (matching the literal binary yes/no statement of `JSP-000816`):
   $$2\pi(n^{1/2}) - f(\pi(n) + 1, n) \not\to \infty \quad (n \to \infty).$$

All proofs are 100% elementary, use purely natural-number and integer arithmetic without
analytic black boxes, contain no unproved placeholders or native-computation reductions, and
depend only on the three standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos983

/-! ### Section 1: Problem Definitions (matching `FormalConjectures/ErdosProblems/983.lean`) -/

/-- `numSmooth A S` is the number of elements of `A` all of whose prime factors lie in `S`.
The element `1` has no prime factors, so it is counted for every `S`. -/
def numSmooth (A S : Finset ℕ) : ℕ :=
  (A.filter fun a => ∀ p ∈ a.primeFactors, p ∈ S).card

/-- $f(k,n)$ is the least $r$ such that every $A\subseteq\{1,\ldots,n\}$ with $|A|=k$ has a set
$S$ of $r$ primes with more than $r$ elements of $A` divisible only by primes from `S`. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
    ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < numSmooth A S}

/-- If every `A ⊆ {1, …, n}` of size `k` has a set `S` of `r` primes with more than `r`
elements of `A` divisible only by primes from `S`, then `f k n ≤ r`. -/
theorem f_le {k n r : ℕ}
    (h : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < numSmooth A S) :
    f k n ≤ r :=
  Nat.sInf_le h

/-- Trivial upper bound $f(k, n) \le \pi(n)$ whenever $\pi(n) < k$ [Er70b, p. 138]. -/
theorem erdos_983.variants.le_primeCounting {k n : ℕ} (hk : Nat.primeCounting n < k) :
    f k n ≤ Nat.primeCounting n := by
  refine f_le fun A hA hAk => ⟨(Finset.range (n + 1)).filter Nat.Prime, ?_, ?_, ?_⟩
  · simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  · exact fun p hp => (Finset.mem_filter.mp hp).2
  · have hAll : A.filter (fun a => ∀ p ∈ a.primeFactors,
        p ∈ (Finset.range (n + 1)).filter Nat.Prime) = A := by
      refine Finset.filter_true_of_mem fun a ha p hp => ?_
      have ha' := Finset.mem_Icc.mp (hA ha)
      have hp' := Nat.mem_primeFactors.mp hp
      have hpa : p ≤ a := Nat.le_of_dvd (by omega) hp'.2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp'.1⟩
    rw [numSmooth, hAll, hAk]
    exact hk

/-! ### Section 2: Erdős–Straus Exact Upper Bound $f(\pi(n)+1, n) \le 2\pi(\lfloor\sqrt{n}\rfloor)+1$ -/

/-- Any integer $1 \le a \le n$ is divisible by at most one prime strictly larger than $\sqrt{n}$. -/
private lemma eq_of_two_large_primes_dvd {n a q₁ q₂ : ℕ}
    (ha1 : 1 ≤ a) (han : a ≤ n)
    (hq₁ : q₁ ∈ Nat.primesLE n \ Nat.primesLE (Nat.sqrt n))
    (hq₂ : q₂ ∈ Nat.primesLE n \ Nat.primesLE (Nat.sqrt n))
    (hd₁ : q₁ ∣ a) (hd₂ : q₂ ∣ a) : q₁ = q₂ := by
  by_contra hne
  obtain ⟨hq₁_le, hq₁_not⟩ := mem_sdiff.mp hq₁
  obtain ⟨hq₂_le, hq₂_not⟩ := mem_sdiff.mp hq₂
  have hp₁ : q₁.Prime := Nat.prime_of_mem_primesLE hq₁_le
  have hp₂ : q₂.Prime := Nat.prime_of_mem_primesLE hq₂_le
  have hgt₁ : Nat.sqrt n < q₁ := by
    by_contra hle
    exact hq₁_not (Nat.mem_primesLE.mpr ⟨not_lt.mp hle, hp₁⟩)
  have hgt₂ : Nat.sqrt n < q₂ := by
    by_contra hle
    exact hq₂_not (Nat.mem_primesLE.mpr ⟨not_lt.mp hle, hp₂⟩)
  have hcop : Nat.Coprime q₁ q₂ := (Nat.coprime_primes hp₁ hp₂).mpr hne
  have hprod_dvd : q₁ * q₂ ∣ a := hcop.mul_dvd_of_dvd_of_dvd hd₁ hd₂
  have hprod_le : q₁ * q₂ ≤ n := (Nat.le_of_dvd ha1 hprod_dvd).trans han
  have hsq : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ q₁ * q₂ := Nat.mul_le_mul hgt₁ hgt₂
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  omega

/-- Erdős and Straus [Er70b, p. 139, (14)] proved
$$f(\pi(n)+1,n)\leq 2\pi(n^{1/2})+1.$$ -/
theorem erdos_983.variants.upper_bound (n : ℕ) :
    f (Nat.primeCounting n + 1) n ≤ 2 * Nat.primeCounting (Nat.sqrt n) + 1 := by
  classical
  set P_small := Nat.primesLE (Nat.sqrt n)
  set P_all := Nat.primesLE n
  set P_large := P_all \ P_small
  set t := Nat.primeCounting (Nat.sqrt n)
  have hsub : P_small ⊆ P_all := Nat.primesLE_mono (Nat.sqrt_le_self n)
  have ht_card : P_small.card = t := Nat.primesLE_card_eq_primeCounting (Nat.sqrt n)
  have hall_card : P_all.card = Nat.primeCounting n := Nat.primesLE_card_eq_primeCounting n
  have hlarge_card : P_large.card + t = Nat.primeCounting n := by
    have := card_sdiff_add_card_eq_card hsub
    rw [ht_card, hall_card] at this
    exact this
  by_cases hM : P_large.card ≤ t + 1
  · calc f (Nat.primeCounting n + 1) n
        ≤ Nat.primeCounting n := erdos_983.variants.le_primeCounting (Nat.lt_succ_self _)
      _ ≤ 2 * t + 1 := by omega
  · have hM' : t + 1 < P_large.card := not_le.mp hM
    refine f_le fun A hA hAk => ?_
    let bucket : ℕ → Finset ℕ := fun q => A.filter (fun a => q ∣ a)
    let A₀ : Finset ℕ := A.filter (fun a => ∀ q ∈ P_large, ¬ q ∣ a)
    have hdisj_buckets : (P_large : Set ℕ).PairwiseDisjoint bucket := by
      intro q₁ hq₁ q₂ hq₂ hne
      refine Finset.disjoint_left.mpr fun a ha₁ ha₂ => ?_
      rw [mem_filter] at ha₁ ha₂
      have ha_icc := mem_Icc.mp (hA ha₁.1)
      exact hne (eq_of_two_large_primes_dvd ha_icc.1 ha_icc.2 hq₁ hq₂ ha₁.2 ha₂.2)
    have hdisj_A₀ : Disjoint A₀ (P_large.biUnion bucket) := by
      refine Finset.disjoint_left.mpr fun a ha₀ hab => ?_
      rw [mem_filter] at ha₀
      rw [mem_biUnion] at hab
      obtain ⟨q, hq, haq⟩ := hab
      exact ha₀.2 q hq (mem_filter.mp haq).2
    have hunion : A₀ ∪ P_large.biUnion bucket = A := by
      ext a
      simp only [mem_union, mem_filter, mem_biUnion, A₀, bucket]
      constructor
      · rintro (⟨ha, _⟩ | ⟨_, _, ha, _⟩) <;> exact ha
      · intro ha
        by_cases hex : ∃ q ∈ P_large, q ∣ a
        · obtain ⟨q, hq, hd⟩ := hex
          exact Or.inr ⟨q, hq, ha, hd⟩
        · exact Or.inl ⟨ha, fun q hq hd => hex ⟨q, hq, hd⟩⟩
    have hsum_all : A₀.card + ∑ q ∈ P_large, (bucket q).card = Nat.primeCounting n + 1 := by
      rw [← card_biUnion hdisj_buckets, ← card_union_of_disjoint hdisj_A₀, hunion, hAk]
    set P_ge2 := P_large.filter (fun q => 2 ≤ (bucket q).card)
    have hQ_exists : ∃ Q ⊆ P_large, Q.card = t + 1 ∧
        2 * t + 2 ≤ A₀.card + ∑ q ∈ Q, (bucket q).card := by
      by_cases hge : t + 1 ≤ P_ge2.card
      · obtain ⟨Q, hQP, hQcard⟩ := exists_subset_card_eq hge
        refine ⟨Q, hQP.trans (filter_subset _ _), hQcard, ?_⟩
        have hsum_Q : 2 * (t + 1) ≤ ∑ q ∈ Q, (bucket q).card := by
          calc 2 * (t + 1) = ∑ _q ∈ Q, 2 := by rw [sum_const, hQcard, smul_eq_mul, mul_comm]
            _ ≤ ∑ q ∈ Q, (bucket q).card := sum_le_sum fun q hq => (mem_filter.mp (hQP hq)).2
        omega
      · have hlt_ge2 : P_ge2.card < t + 1 := not_le.mp hge
        have hpart : (P_large \ P_ge2).card + P_ge2.card = P_large.card :=
          card_sdiff_add_card_eq_card (filter_subset _ P_large)
        have hrem : (t + 1) - P_ge2.card ≤ (P_large \ P_ge2).card := by omega
        obtain ⟨R, hRsub, hRcard⟩ := exists_subset_card_eq hrem
        let Q := P_ge2 ∪ R
        have hdisj_PR : Disjoint P_ge2 R :=
          disjoint_of_subset_right hRsub disjoint_sdiff_self_right
        have hQsub : Q ⊆ P_large :=
          union_subset (filter_subset _ _) (hRsub.trans sdiff_subset)
        have hQcard : Q.card = t + 1 := by
          rw [card_union_of_disjoint hdisj_PR, hRcard]
          omega
        refine ⟨Q, hQsub, hQcard, ?_⟩
        have hsplit : ∑ q ∈ P_large, (bucket q).card =
            ∑ q ∈ Q, (bucket q).card + ∑ q ∈ P_large \ Q, (bucket q).card := by
          rw [← sum_union disjoint_sdiff_self_right, union_sdiff_of_subset hQsub]
        have hrest_le : ∑ q ∈ P_large \ Q, (bucket q).card ≤ (P_large \ Q).card := by
          calc ∑ q ∈ P_large \ Q, (bucket q).card
              ≤ ∑ _q ∈ P_large \ Q, 1 := by
                refine sum_le_sum fun q hq => ?_
                obtain ⟨hqL, hqnotQ⟩ := mem_sdiff.mp hq
                have hqnot2 : q ∉ P_ge2 := fun h => hqnotQ (mem_union_left R h)
                have : ¬ 2 ≤ (bucket q).card := fun h => hqnot2 (mem_filter.mpr ⟨hqL, h⟩)
                omega
            _ = (P_large \ Q).card := by simp
        have hsdiff_card : (P_large \ Q).card + (t + 1) = P_large.card := by
          have := card_sdiff_add_card_eq_card hQsub
          rwa [hQcard] at this
        omega
    obtain ⟨Q, hQsub, hQcard, hQsum⟩ := hQ_exists
    let S := P_small ∪ Q
    have hdisj_SQ : Disjoint P_small Q :=
      disjoint_of_subset_right hQsub disjoint_sdiff_self_right
    refine ⟨S, ?_, ?_, ?_⟩
    · rw [card_union_of_disjoint hdisj_SQ, ht_card, hQcard]
      omega
    · intro p hp
      rcases mem_union.mp hp with hpS | hpQ
      · exact Nat.prime_of_mem_primesLE hpS
      · exact Nat.prime_of_mem_primesLE (mem_sdiff.mp (hQsub hpQ)).1
    · have hsub_smooth : A₀ ∪ Q.biUnion bucket ⊆
          A.filter (fun a => ∀ p ∈ a.primeFactors, p ∈ S) := by
        intro a ha
        rcases mem_union.mp ha with ha₀ | haQ
        · obtain ⟨haA, hno_large⟩ := mem_filter.mp ha₀
          refine mem_filter.mpr ⟨haA, fun p hp => ?_⟩
          obtain ⟨hp_prime, hp_dvd, _⟩ := Nat.mem_primeFactors.mp hp
          have ha_icc := mem_Icc.mp (hA haA)
          have hp_le : p ≤ n := (Nat.le_of_dvd ha_icc.1 hp_dvd).trans ha_icc.2
          have hp_all : p ∈ P_all := Nat.mem_primesLE.mpr ⟨hp_le, hp_prime⟩
          by_cases hp_sm : p ∈ P_small
          · exact mem_union_left Q hp_sm
          · exfalso
            exact hno_large p (mem_sdiff.mpr ⟨hp_all, hp_sm⟩) hp_dvd
        · obtain ⟨q, hqQ, haq⟩ := mem_biUnion.mp haQ
          obtain ⟨haA, hq_dvd⟩ := mem_filter.mp haq
          refine mem_filter.mpr ⟨haA, fun p hp => ?_⟩
          obtain ⟨hp_prime, hp_dvd, _⟩ := Nat.mem_primeFactors.mp hp
          have ha_icc := mem_Icc.mp (hA haA)
          have hp_le : p ≤ n := (Nat.le_of_dvd ha_icc.1 hp_dvd).trans ha_icc.2
          have hp_all : p ∈ P_all := Nat.mem_primesLE.mpr ⟨hp_le, hp_prime⟩
          by_cases hp_sm : p ∈ P_small
          · exact mem_union_left Q hp_sm
          · have hp_lg : p ∈ P_large := mem_sdiff.mpr ⟨hp_all, hp_sm⟩
            have hpq : p = q :=
              eq_of_two_large_primes_dvd ha_icc.1 ha_icc.2 hp_lg (hQsub hqQ) hp_dvd hq_dvd
            exact mem_union_right P_small (hpq ▸ hqQ)
      have hdisj_Q : (Q : Set ℕ).PairwiseDisjoint bucket :=
        hdisj_buckets.subset (Finset.coe_subset.mpr hQsub)
      have hsub_biUnion : Q.biUnion bucket ⊆ P_large.biUnion bucket := by
        intro a ha
        obtain ⟨q, hqQ, haq⟩ := mem_biUnion.mp ha
        exact mem_biUnion.mpr ⟨q, hQsub hqQ, haq⟩
      have hdisj_A₀Q : Disjoint A₀ (Q.biUnion bucket) :=
        hdisj_A₀.mono_right hsub_biUnion
      have hcard_lb : A₀.card + ∑ q ∈ Q, (bucket q).card ≤ numSmooth A S := by
        rw [← card_biUnion hdisj_Q, ← card_union_of_disjoint hdisj_A₀Q]
        exact card_le_card hsub_smooth
      omega

/-! ### Section 3: Elementary Proof of Pomerance's Prime Inequality $p_{M-i} p_{M+i} < p_M^2$ -/

/-- The `m`-th prime (0-indexed: `nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/
noncomputable abbrev nthPrime (m : ℕ) : ℕ := Nat.nth Nat.Prime m

private lemma nthPrime_prime (m : ℕ) : (nthPrime m).Prime :=
  Nat.prime_nth_prime m

private lemma nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

private lemma nthPrime_le_of_lt_primeCounting {m x : ℕ} (h : m < Nat.primeCounting x) :
    nthPrime m ≤ x := by
  by_contra! hlt
  have hle : x ≤ nthPrime m - 1 := Nat.le_sub_one_of_lt hlt
  have hmon := Nat.monotone_primeCounting hle
  rw [Nat.primeCounting_sub_one, Nat.primeCounting'_nth_eq] at hmon
  omega

/-- Elementary dyadic prime-counting lower bound from central binomial prime factorization:
for every $u \ge 2$, $2^u \le u (\pi(2^u) + 1)$. -/
private lemma two_pow_le_mul_primeCounting_succ {u : ℕ} (hu : 2 ≤ u) :
    2 ^ u ≤ u * (Nat.primeCounting (2 ^ u) + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, u = t + 1 := ⟨u - 1, by omega⟩
  set n := 2 ^ t
  have hn_pos : 0 < n := by positivity
  have h2n : 2 * n = 2 ^ (t + 1) := by ring
  have h4 : 2 ^ (2 * n) ≤ 2 * n * Nat.centralBinom n := by
    have h4' := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn_pos
    have hpow : (2 : ℕ) ^ (2 * n) = 4 ^ n := by
      rw [pow_mul]
      norm_num
    omega
  have hprod_eq : (∏ p ∈ Nat.primesLE (2 * n), p ^ (Nat.centralBinom n).factorization p) =
      Nat.centralBinom n := by
    conv_rhs => rw [← Nat.prod_pow_factorization_centralBinom n]
    apply Finset.prod_subset
    · intro p hp
      rw [Nat.primesLE_eq_filter_range] at hp
      exact mem_of_mem_filter p hp
    · intro p hpRange hpNot
      rw [Nat.primesLE_eq_filter_range, mem_filter] at hpNot
      have hnp : ¬ p.Prime := fun hpP => hpNot ⟨hpRange, hpP⟩
      rw [Nat.factorization_eq_zero_of_not_prime _ hnp, pow_zero]
  have hcb_le : Nat.centralBinom n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
    rw [← hprod_eq, ← Nat.primesLE_card_eq_primeCounting (2 * n), ← Finset.prod_const]
    refine Finset.prod_le_prod' fun p _ => ?_
    exact Nat.pow_factorization_choose_le (by positivity : 0 < 2 * n)
  have hexp : 2 ^ (2 * n) ≤ (2 * n) ^ (Nat.primeCounting (2 * n) + 1) := by
    calc 2 ^ (2 * n) ≤ 2 * n * Nat.centralBinom n := h4
      _ ≤ 2 * n * (2 * n) ^ Nat.primeCounting (2 * n) := Nat.mul_le_mul_left _ hcb_le
      _ = (2 * n) ^ (Nat.primeCounting (2 * n) + 1) := by rw [pow_succ']
  rw [h2n, ← pow_mul] at hexp
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hexp

/-- Elementary cubic polynomial domination by $2^k$ for $k \ge 10$. -/
private lemma cube_lt_two_pow : ∀ k : ℕ, 10 ≤ k → k ^ 3 < 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hk2 : 3 * k ^ 2 + 3 * k + 1 < k ^ 3 := by nlinarith
    calc (k + 1) ^ 3 = k ^ 3 + (3 * k ^ 2 + 3 * k + 1) := by ring
      _ < k ^ 3 + k ^ 3 := by omega
      _ = 2 * k ^ 3 := by ring
      _ < 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by rw [pow_succ']

/-- Bernoulli-type lower bound $(a + 1)^E \ge a^E + E a^{E-1}$ in $\mathbb{N}$ for $E \ge 1$. -/
private lemma add_one_pow_ge (a : ℕ) : ∀ E : ℕ, 1 ≤ E → a ^ E + E * a ^ (E - 1) ≤ (a + 1) ^ E := by
  intro E hE
  induction E, hE using Nat.le_induction with
  | base => simp
  | succ E hE ih =>
    have hsub : E + 1 - 1 = E := by omega
    rw [hsub]
    have haE : a ^ (E - 1) * a = a ^ E := by
      rw [← pow_succ, Nat.sub_add_cancel hE]
    calc a ^ (E + 1) + (E + 1) * a ^ E
        = a ^ E * a + (E + 1) * a ^ E := by rw [pow_succ]
      _ ≤ a ^ E * a + (E + 1) * a ^ E + E * a ^ (E - 1) := Nat.le_add_right _ _
      _ = (a ^ E + E * a ^ (E - 1)) * (a + 1) := by
          calc a ^ E * a + (E + 1) * a ^ E + E * a ^ (E - 1)
              = a ^ E * a + a ^ E + E * (a ^ (E - 1) * a) + E * a ^ (E - 1) := by
                rw [haE]
                ring
            _ = (a ^ E + E * a ^ (E - 1)) * (a + 1) := by ring
      _ ≤ (a + 1) ^ E * (a + 1) := Nat.mul_le_mul_right (a + 1) ih
      _ = (a + 1) ^ (E + 1) := by rw [pow_succ]

/-- For any exponents $E, K \in \mathbb{N}$, $(p_m)^E \cdot 2^K < 2^m$ for all sufficiently
large $m$. -/
private lemma nthPrime_pow_mul_two_pow_lt_eventually (E K : ℕ) :
    ∃ B : ℕ, K ≤ B ∧ ∀ m : ℕ, B < m → (nthPrime m) ^ E * 2 ^ K < 2 ^ m := by
  classical
  set u₀ := 12 + E + K
  set B := max K (Nat.primeCounting (2 ^ u₀))
  refine ⟨B, le_max_left _ _, fun m hm => ?_⟩
  have hm_gt : Nat.primeCounting (2 ^ u₀) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hex_u : ∃ u : ℕ, m < Nat.primeCounting (2 ^ u) := by
    refine ⟨m + 12, ?_⟩
    by_contra! hle
    have hpow := two_pow_le_mul_primeCounting_succ (by omega : 2 ≤ m + 12)
    have hcube := cube_lt_two_pow (m + 12) (by omega)
    have hm1 : (m + 12) * (Nat.primeCounting (2 ^ (m + 12)) + 1) ≤ (m + 12) * (m + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right hle 1)
    have hlt_cube : (m + 12) * (m + 1) < (m + 12) ^ 3 := by
      calc (m + 12) * (m + 1) < (m + 12) * ((m + 12) * (m + 12)) := by nlinarith
        _ = (m + 12) ^ 3 := by ring
    omega
  set u := Nat.find hex_u
  have hu_spec : m < Nat.primeCounting (2 ^ u) := Nat.find_spec hex_u
  have hu_gt : u₀ < u := by
    by_contra! hle
    have hmon : Nat.primeCounting (2 ^ u) ≤ Nat.primeCounting (2 ^ u₀) :=
      Nat.monotone_primeCounting (Nat.pow_le_pow_right (by norm_num) hle)
    omega
  have hu_min : Nat.primeCounting (2 ^ (u - 1)) ≤ m := by
    have := Nat.find_min hex_u (by omega : u - 1 < u)
    omega
  have h2_lb : 2 ^ (u - 1) ≤ (u - 1) * (m + 1) := by
    calc 2 ^ (u - 1)
        ≤ (u - 1) * (Nat.primeCounting (2 ^ (u - 1)) + 1) :=
          two_pow_le_mul_primeCounting_succ (by omega)
      _ ≤ (u - 1) * (m + 1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hu_min 1)
  have hcube_lb : (u - 1) ^ 3 < (u - 1) * (m + 1) :=
    lt_of_lt_of_le (cube_lt_two_pow (u - 1) (by omega)) h2_lb
  have hexp_lt : E * u + K < m := by
    by_contra! hm_le
    have hu1 : 12 + E + K ≤ u - 1 := by omega
    have hquad : m + 1 ≤ (u - 1) ^ 2 := by
      have hu_eq : u = (u - 1) + 1 := by omega
      nlinarith
    have hmul : (u - 1) * (m + 1) ≤ (u - 1) ^ 3 := by
      calc (u - 1) * (m + 1) ≤ (u - 1) * (u - 1) ^ 2 := Nat.mul_le_mul_left _ hquad
        _ = (u - 1) ^ 3 := by ring
    omega
  have hp_le : nthPrime m ≤ 2 ^ u := nthPrime_le_of_lt_primeCounting hu_spec
  calc (nthPrime m) ^ E * 2 ^ K
      ≤ (2 ^ u) ^ E * 2 ^ K := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp_le E)
    _ = 2 ^ (E * u + K) := by rw [← pow_mul, mul_comm u E, ← pow_add]
    _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hexp_lt

/-- Pomerance's symmetric prime inequality [Po79, Corollary after Theorem 2.2]:
for every $K \ge 2$, there exists $M \ge K$ such that $p_{M-i} p_{M+i} < p_M^2$
for all $1 \le i \le M$ (0-indexed primes). -/
theorem exists_pomerance_prime_index {K : ℕ} (hK : 2 ≤ K) :
    ∃ M : ℕ, K ≤ M ∧ ∀ i : ℕ, 1 ≤ i → i ≤ M →
      nthPrime (M - i) * nthPrime (M + i) < (nthPrime M) ^ 2 := by
  classical
  set pPrev := nthPrime (K - 1)
  have hpPrev_pos : 0 < pPrev := (nthPrime_prime (K - 1)).pos
  set E := 2 ^ K * pPrev + 1
  have hE1 : 1 ≤ E := by omega
  have h_small : ∀ m : ℕ, m < K → (nthPrime m) ^ E * 2 ^ K < (nthPrime K) ^ E * 2 ^ m := by
    intro m hm
    have hm_le : nthPrime m ≤ pPrev :=
      nthPrime_strictMono.monotone (by omega : m ≤ K - 1)
    have hpK_ge : pPrev + 1 ≤ nthPrime K :=
      nthPrime_strictMono (by omega : K - 1 < K)
    have hbern := add_one_pow_ge pPrev E hE1
    have hpPrev_pow : pPrev ^ (E - 1) * pPrev = pPrev ^ E := by
      rw [← pow_succ, Nat.sub_add_cancel hE1]
    have hgt : (nthPrime m) ^ E * 2 ^ K < (nthPrime K) ^ E := by
      calc (nthPrime m) ^ E * 2 ^ K
          ≤ pPrev ^ E * 2 ^ K := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm_le E)
        _ < pPrev ^ E + (2 ^ K * pPrev + 1) * pPrev ^ (E - 1) := by
            have hpE_pos : 0 < pPrev ^ E := pow_pos hpPrev_pos E
            have hpE1_pos : 0 < pPrev ^ (E - 1) := pow_pos hpPrev_pos (E - 1)
            have hmul_eq : (2 ^ K * pPrev) * pPrev ^ (E - 1) = pPrev ^ E * 2 ^ K := by
              calc (2 ^ K * pPrev) * pPrev ^ (E - 1)
                  = 2 ^ K * (pPrev ^ (E - 1) * pPrev) := by ring
                _ = pPrev ^ E * 2 ^ K := by rw [hpPrev_pow, mul_comm]
            linarith
        _ ≤ (pPrev + 1) ^ E := hbern
        _ ≤ (nthPrime K) ^ E := Nat.pow_le_pow_left hpK_ge E
    have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    calc (nthPrime m) ^ E * 2 ^ K
        < (nthPrime K) ^ E * 1 := by simpa using hgt
      _ ≤ (nthPrime K) ^ E * 2 ^ m := Nat.mul_le_mul_left _ h2m
  obtain ⟨B, hKB, hB_tail⟩ := nthPrime_pow_mul_two_pow_lt_eventually E K
  let G : ℕ → ℕ := fun m => (nthPrime m) ^ E * 2 ^ (B - m)
  obtain ⟨M, hMB_mem, hM_max⟩ := exists_max_image (Iic B) G ⟨0, by simp⟩
  have hMB : M ≤ B := mem_Iic.mp hMB_mem
  have hG_iff : ∀ a b : ℕ, a ≤ B → b ≤ B →
      (G a ≤ G b ↔ (nthPrime a) ^ E * 2 ^ b ≤ (nthPrime b) ^ E * 2 ^ a) := by
    intro a b ha hb
    have hpos : 0 < 2 ^ (a + b) := by positivity
    have hposB : 0 < 2 ^ B := by positivity
    have eq1 : G a * 2 ^ (a + b) = ((nthPrime a) ^ E * 2 ^ b) * 2 ^ B := by
      change (nthPrime a) ^ E * 2 ^ (B - a) * 2 ^ (a + b) = ((nthPrime a) ^ E * 2 ^ b) * 2 ^ B
      rw [mul_assoc, ← pow_add, show B - a + (a + b) = b + B by omega, pow_add (2 : ℕ)]
      ring
    have eq2 : G b * 2 ^ (a + b) = ((nthPrime b) ^ E * 2 ^ a) * 2 ^ B := by
      change (nthPrime b) ^ E * 2 ^ (B - b) * 2 ^ (a + b) = ((nthPrime b) ^ E * 2 ^ a) * 2 ^ B
      rw [mul_assoc, ← pow_add, show B - b + (a + b) = a + B by omega, pow_add (2 : ℕ)]
      ring
    rw [← Nat.mul_le_mul_right_iff hpos, eq1, eq2, Nat.mul_le_mul_right_iff hposB]
  have hKM_ineq : (nthPrime K) ^ E * 2 ^ M ≤ (nthPrime M) ^ E * 2 ^ K :=
    (hG_iff K M hKB hMB).mp (hM_max K (mem_Iic.mpr hKB))
  have hKM : K ≤ M := by
    by_contra! hlt
    have := h_small M hlt
    omega
  have hGlobal : ∀ m : ℕ, (nthPrime m) ^ E * 2 ^ M ≤ (nthPrime M) ^ E * 2 ^ m := by
    intro m
    by_cases hmB : m ≤ B
    · exact (hG_iff m M hmB hMB).mp (hM_max m (mem_Iic.mpr hmB))
    · have hm_gt : B < m := not_le.mp hmB
      have htail := hB_tail m hm_gt
      have hpK_one : 1 ≤ (nthPrime K) ^ E :=
        one_le_pow₀ (nthPrime_prime K).one_lt.le
      have h1 : ((nthPrime m) ^ E * 2 ^ M) * 2 ^ K ≤ ((nthPrime M) ^ E * 2 ^ m) * 2 ^ K := by
        calc ((nthPrime m) ^ E * 2 ^ M) * 2 ^ K
            = ((nthPrime m) ^ E * 2 ^ K) * 2 ^ M := by ring
          _ ≤ 2 ^ m * 2 ^ M := Nat.mul_le_mul_right _ htail.le
          _ ≤ (2 ^ m * (nthPrime K) ^ E) * 2 ^ M :=
              Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hpK_one)
          _ = 2 ^ m * ((nthPrime K) ^ E * 2 ^ M) := by ring
          _ ≤ 2 ^ m * ((nthPrime M) ^ E * 2 ^ K) := Nat.mul_le_mul_left _ hKM_ineq
          _ = ((nthPrime M) ^ E * 2 ^ m) * 2 ^ K := by ring
      exact (Nat.mul_le_mul_right_iff (by positivity : 0 < 2 ^ K)).mp h1
  refine ⟨M, hKM, fun i hi1 hiM => ?_⟩
  have hL := hGlobal (M - i)
  have hR := hGlobal (M + i)
  have hmul : ((nthPrime (M - i) * nthPrime (M + i)) ^ E) * 2 ^ (2 * M) ≤
      (((nthPrime M) ^ 2) ^ E) * 2 ^ (2 * M) := by
    calc ((nthPrime (M - i) * nthPrime (M + i)) ^ E) * 2 ^ (2 * M)
        = ((nthPrime (M - i)) ^ E * 2 ^ M) * ((nthPrime (M + i)) ^ E * 2 ^ M) := by
            rw [mul_pow, show 2 * M = M + M by ring, pow_add]
            ring
      _ ≤ ((nthPrime M) ^ E * 2 ^ (M - i)) * ((nthPrime M) ^ E * 2 ^ (M + i)) :=
            Nat.mul_le_mul hL hR
      _ = (((nthPrime M) ^ 2) ^ E) * 2 ^ (2 * M) := by
            have hexp_sum : (M - i) + (M + i) = 2 * M := by omega
            calc ((nthPrime M) ^ E * 2 ^ (M - i)) * ((nthPrime M) ^ E * 2 ^ (M + i))
                = ((nthPrime M) ^ E * (nthPrime M) ^ E) * (2 ^ (M - i) * 2 ^ (M + i)) := by ring
              _ = (((nthPrime M) ^ 2) ^ E) * 2 ^ (2 * M) := by
                  rw [← pow_add (2 : ℕ), hexp_sum, sq, mul_pow]
  have hpow_le : (nthPrime (M - i) * nthPrime (M + i)) ^ E ≤ ((nthPrime M) ^ 2) ^ E :=
    (Nat.mul_le_mul_right_iff (by positivity : 0 < 2 ^ (2 * M))).mp hmul
  have hprod_le : nthPrime (M - i) * nthPrime (M + i) ≤ (nthPrime M) ^ 2 :=
    (Nat.pow_le_pow_iff_left (by omega : E ≠ 0)).mp hpow_le
  refine lt_of_le_of_ne hprod_le fun heq => ?_
  have hdvd : nthPrime M ∣ nthPrime (M - i) * nthPrime (M + i) := by
    rw [heq, sq]
    exact dvd_mul_right _ _
  rcases (nthPrime_prime M).dvd_mul.mp hdvd with hd₁ | hd₂
  · have heq₁ := (Nat.prime_dvd_prime_iff_eq (nthPrime_prime M) (nthPrime_prime (M - i))).mp hd₁
    have := nthPrime_strictMono.injective heq₁
    omega
  · have heq₂ := (Nat.prime_dvd_prime_iff_eq (nthPrime_prime M) (nthPrime_prime (M + i))).mp hd₂
    have := nthPrime_strictMono.injective heq₂
    omega

/-! ### Section 4: Zigzag Semiprime Path Construction & Exact Lower Bound -/

/-- Zigzag permutation of `{0, …, 2M}`:
`0 ↦ 2M, 1 ↦ 0, 2 ↦ 2M-1, 3 ↦ 1, …, 2M-1 ↦ M-1, 2M ↦ M`. -/
private def pathIdx (M j : ℕ) : ℕ :=
  if j % 2 = 0 then 2 * M - j / 2 else j / 2

private noncomputable def pathVert (M j : ℕ) : ℕ :=
  nthPrime (pathIdx M j)

private noncomputable def pathEdge (M j : ℕ) : ℕ :=
  pathVert M j * pathVert M (j + 1)

private lemma pathIdx_le {M j : ℕ} (hj : j ≤ 2 * M) : pathIdx M j ≤ 2 * M := by
  unfold pathIdx
  split_ifs <;> omega

private lemma pathIdx_injOn {M : ℕ} :
    Set.InjOn (pathIdx M) (Iic (2 * M) : Set ℕ) := by
  intro j₁ hj₁ j₂ hj₂ heq
  rw [coe_Iic, Set.mem_Iic] at hj₁ hj₂
  unfold pathIdx at heq
  split_ifs at heq with h₁ h₂ <;> omega

private lemma pathVert_injOn {M : ℕ} :
    Set.InjOn (pathVert M) (Iic (2 * M) : Set ℕ) :=
  fun _ hj₁ _ hj₂ heq => pathIdx_injOn hj₁ hj₂ (nthPrime_strictMono.injective heq)

private lemma pathVert_prime (M j : ℕ) : (pathVert M j).Prime :=
  nthPrime_prime (pathIdx M j)

private lemma pathEdge_primeFactors (M j : ℕ) :
    (pathEdge M j).primeFactors = {pathVert M j, pathVert M (j + 1)} := by
  unfold pathEdge
  have hp₁ := pathVert_prime M j
  have hp₂ := pathVert_prime M (j + 1)
  rw [Nat.primeFactors_mul hp₁.ne_zero hp₂.ne_zero, hp₁.primeFactors, hp₂.primeFactors]
  rfl

private lemma pathEdge_not_prime {M j : ℕ} (hj : j < 2 * M) :
    ¬ (pathEdge M j).Prime := by
  intro hp
  have hne : pathVert M j ≠ pathVert M (j + 1) := by
    intro heq
    have := pathVert_injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) heq
    omega
  have hcard1 : (pathEdge M j).primeFactors.card = 1 := by
    rw [hp.primeFactors, card_singleton]
  have hcard2 : (pathEdge M j).primeFactors.card = 2 := by
    rw [pathEdge_primeFactors M j, card_pair hne]
  omega

private lemma pathEdge_injOn {M : ℕ} :
    Set.InjOn (pathEdge M) (range (2 * M) : Set ℕ) := by
  intro j₁ hj₁ j₂ hj₂ heq
  rw [coe_range, Set.mem_Iio] at hj₁ hj₂
  have hpf : ({pathVert M j₁, pathVert M (j₁ + 1)} : Finset ℕ) =
      {pathVert M j₂, pathVert M (j₂ + 1)} := by
    rw [← pathEdge_primeFactors M j₁, ← pathEdge_primeFactors M j₂, heq]
  have hm₁ : pathVert M j₁ ∈ ({pathVert M j₂, pathVert M (j₂ + 1)} : Finset ℕ) := by
    rw [← hpf]
    simp
  have hm₂ : pathVert M (j₁ + 1) ∈ ({pathVert M j₂, pathVert M (j₂ + 1)} : Finset ℕ) := by
    rw [← hpf]
    simp
  simp only [mem_insert, mem_singleton] at hm₁ hm₂
  have h₁ : j₁ = j₂ ∨ j₁ = j₂ + 1 := by
    rcases hm₁ with h | h
    · exact Or.inl (pathVert_injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) h)
    · exact Or.inr (pathVert_injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) h)
  have h₂ : j₁ + 1 = j₂ ∨ j₁ + 1 = j₂ + 1 := by
    rcases hm₂ with h | h
    · exact Or.inl (pathVert_injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) h)
    · exact Or.inr (pathVert_injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) h)
  omega

private lemma pathEdge_le_sq_sub_one {M j : ℕ}
    (hM : 2 ≤ M)
    (hpom : ∀ i : ℕ, 1 ≤ i → i ≤ M → nthPrime (M - i) * nthPrime (M + i) < (nthPrime M) ^ 2)
    (hj : j < 2 * M) :
    1 ≤ pathEdge M j ∧ pathEdge M j ≤ (nthPrime M) ^ 2 - 1 := by
  have hpos : 1 ≤ pathEdge M j := by
    unfold pathEdge
    have := (pathVert_prime M j).two_le
    have := (pathVert_prime M (j + 1)).two_le
    nlinarith
  refine ⟨hpos, Nat.le_sub_one_of_lt ?_⟩
  unfold pathEdge pathVert pathIdx
  by_cases hpar : j % 2 = 0
  · have hpar1 : (j + 1) % 2 ≠ 0 := by omega
    have hdiv : (j + 1) / 2 = j / 2 := by omega
    rw [if_pos hpar, if_neg hpar1, hdiv]
    set t := j / 2
    have ht : t < M := by omega
    have h1 : 1 ≤ M - t := by omega
    have h2 : M - t ≤ M := by omega
    have heq_prod : nthPrime (2 * M - t) * nthPrime t =
        nthPrime (M - (M - t)) * nthPrime (M + (M - t)) := by
      rw [mul_comm]
      congr 2 <;> omega
    rw [heq_prod]
    exact hpom (M - t) h1 h2
  · have hpar1 : (j + 1) % 2 = 0 := by omega
    have hdiv : (j + 1) / 2 = j / 2 + 1 := by omega
    rw [if_neg hpar, if_pos hpar1, hdiv]
    set t := j / 2
    have ht : t < M := by omega
    by_cases htM : t + 1 = M
    · have ht_eq : t = M - 1 := by omega
      have hidx : 2 * M - (t + 1) = M := by omega
      rw [hidx, ht_eq, sq]
      exact Nat.mul_lt_mul_of_pos_right (nthPrime_strictMono (by omega : M - 1 < M))
        (nthPrime_prime M).pos
    · have ht_lt : t + 1 < M := by omega
      set i := M - (t + 1)
      have hi1 : 1 ≤ i := by omega
      have hiM : i ≤ M := by omega
      have hidx : 2 * M - (t + 1) = M + i := by omega
      have ht_lt_Mi : t < M - i := by omega
      rw [hidx]
      calc nthPrime t * nthPrime (M + i)
          < nthPrime (M - i) * nthPrime (M + i) :=
            Nat.mul_lt_mul_of_pos_right (nthPrime_strictMono ht_lt_Mi) (nthPrime_prime (M + i)).pos
        _ < (nthPrime M) ^ 2 := hpom i hi1 hiM

/-- At $n = p_M^2 - 1$ for any Pomerance index $M \ge 2$, exact equality
$f(\pi(n) + 1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1 = 2M + 1$ holds. -/
theorem exact_equality_at_pomerance_index {M : ℕ} (hM : 2 ≤ M)
    (hpom : ∀ i : ℕ, 1 ≤ i → i ≤ M → nthPrime (M - i) * nthPrime (M + i) < (nthPrime M) ^ 2) :
    let n := (nthPrime M) ^ 2 - 1
    Nat.sqrt n = nthPrime M - 1 ∧
    Nat.primeCounting (Nat.sqrt n) = M ∧
    f (Nat.primeCounting n + 1) n = 2 * Nat.primeCounting (Nat.sqrt n) + 1 := by
  classical
  set pM := nthPrime M
  have hpM_ge : 4 ≤ pM := by
    have : M + 2 ≤ pM := Nat.add_two_le_nth_prime M
    omega
  set n := pM ^ 2 - 1
  have hsqrt : Nat.sqrt n = pM - 1 := by
    apply le_antisymm
    · by_contra! hlt
      have hpM_le : pM ≤ Nat.sqrt n := by omega
      have hsq_le : pM * pM ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hpM_le hpM_le
      have hsqrt_sq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
      have hn_lt : n < pM * pM := by
        dsimp [n]
        rw [sq]
        have : 1 ≤ pM * pM := by nlinarith
        omega
      omega
    · rw [Nat.le_sqrt]
      have hle_sq : (pM - 1) * (pM - 1) + 1 ≤ pM ^ 2 := by
        zify [show 1 ≤ pM by omega]
        nlinarith
      dsimp [n]
      omega
  have hpi_sqrt : Nat.primeCounting (Nat.sqrt n) = M := by
    rw [hsqrt, Nat.primeCounting_sub_one, Nat.primeCounting'_nth_eq]
  refine ⟨hsqrt, hpi_sqrt, ?_⟩
  rw [hpi_sqrt]
  apply le_antisymm
  · simpa [hpi_sqrt] using erdos_983.variants.upper_bound n
  · -- Prove 2 * M + 1 ≤ f (π(n) + 1) n via the zigzag semiprime counterexample set A.
    set V_path : Finset ℕ := (Iic (2 * M)).image (pathVert M)
    set E_set : Finset ℕ := (range (2 * M)).image (pathEdge M)
    set Ends : Finset ℕ := {pathVert M 0, pathVert M (2 * M)}
    set P_other : Finset ℕ := Nat.primesLE n \ V_path
    set A : Finset ℕ := (E_set ∪ Ends) ∪ P_other
    have hp2M_le_n : nthPrime (2 * M) ≤ n := by
      have hM_pom := hpom M (by omega) le_rfl
      simp only [Nat.sub_self, Nat.nth_prime_zero_eq_two, show M + M = 2 * M by ring] at hM_pom
      dsimp [n]
      omega
    have hV_sub : V_path ⊆ Nat.primesLE n := by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
      refine Nat.mem_primesLE.mpr ⟨?_, pathVert_prime M j⟩
      have hidx_le : pathIdx M j ≤ 2 * M := pathIdx_le (mem_Iic.mp hj)
      exact (nthPrime_strictMono.monotone hidx_le).trans hp2M_le_n
    have hV_card : V_path.card = 2 * M + 1 := by
      rw [card_image_of_injOn pathVert_injOn, Nat.card_Iic]
    have hE_card : E_set.card = 2 * M := by
      rw [card_image_of_injOn pathEdge_injOn, card_range]
    have hEnds_sub_V : Ends ⊆ V_path := by
      intro q hq
      simp only [Ends, mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact mem_image_of_mem _ (mem_Iic.mpr (by omega))
      · exact mem_image_of_mem _ (mem_Iic.mpr le_rfl)
    have hEnds_card : Ends.card = 2 := by
      refine card_pair fun heq => ?_
      have := pathVert_injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr le_rfl) heq
      omega
    have hdisj_EEnds : Disjoint E_set Ends := by
      refine Finset.disjoint_left.mpr fun a haE haEnds => ?_
      obtain ⟨j, hj, rfl⟩ := mem_image.mp haE
      have hnp := pathEdge_not_prime (mem_range.mp hj)
      have hp : (pathEdge M j).Prime := Nat.prime_of_mem_primesLE (hV_sub (hEnds_sub_V haEnds))
      exact hnp hp
    have hdisj_EP : Disjoint (E_set ∪ Ends) P_other := by
      refine Finset.disjoint_left.mpr fun a haEE haP => ?_
      obtain ⟨ha_prLE, ha_notV⟩ := mem_sdiff.mp haP
      rcases mem_union.mp haEE with haE | haEnds
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp haE
        exact pathEdge_not_prime (mem_range.mp hj) (Nat.prime_of_mem_primesLE ha_prLE)
      · exact ha_notV (hEnds_sub_V haEnds)
    have hA_sub : A ⊆ Icc 1 n := by
      intro a ha
      rcases mem_union.mp ha with haEE | haP
      · rcases mem_union.mp haEE with haE | haEnds
        · obtain ⟨j, hj, rfl⟩ := mem_image.mp haE
          have hb := pathEdge_le_sq_sub_one hM hpom (mem_range.mp hj)
          exact mem_Icc.mpr hb
        · have hpr := hV_sub (hEnds_sub_V haEnds)
          exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hpr).pos, Nat.le_of_mem_primesLE hpr⟩
      · have hpr := (mem_sdiff.mp haP).1
        exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hpr).pos, Nat.le_of_mem_primesLE hpr⟩
    have hA_card : A.card = Nat.primeCounting n + 1 := by
      rw [card_union_of_disjoint hdisj_EP, card_union_of_disjoint hdisj_EEnds,
        hE_card, hEnds_card]
      have hsdiff : P_other.card + V_path.card = (Nat.primesLE n).card :=
        card_sdiff_add_card_eq_card hV_sub
      rw [hV_card, Nat.primesLE_card_eq_primeCounting] at hsdiff
      omega
    -- Admissible set is nonempty (witnessed by 2 * M + 1 from upper_bound).
    have hAdm_nonempty : {r : ℕ | ∀ A' : Finset ℕ, A' ⊆ Icc 1 n → A'.card = Nat.primeCounting n + 1 →
        ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < numSmooth A' S}.Nonempty := by
      refine ⟨Nat.primeCounting n, fun A' hA' hA'k => ?_⟩
      refine ⟨Nat.primesLE n, Nat.primesLE_card_eq_primeCounting n,
        fun p hp => Nat.prime_of_mem_primesLE hp, ?_⟩
      have hAll : A'.filter (fun a => ∀ p ∈ a.primeFactors, p ∈ Nat.primesLE n) = A' := by
        refine filter_true_of_mem fun a ha p hp => ?_
        have ha_icc := mem_Icc.mp (hA' ha)
        obtain ⟨hpP, hpD, _⟩ := Nat.mem_primeFactors.mp hp
        exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd ha_icc.1 hpD).trans ha_icc.2, hpP⟩
      rw [numSmooth, hAll, hA'k]
      omega
    refine le_csInf hAdm_nonempty fun r hr => ?_
    by_contra! hr_lt
    have hr_le : r ≤ 2 * M := by omega
    obtain ⟨S, hScard, _, hr_smooth⟩ := hr A hA_sub hA_card
    let isSm : ℕ → Prop := fun a => ∀ p ∈ a.primeFactors, p ∈ S
    -- Split S into S₁ = S ∩ V_path and S₂ = S \ V_path.
    set S₁ := S ∩ V_path
    set S₂ := S \ V_path
    have hS_split : S₁.card + S₂.card = r :=
      (card_inter_add_card_sdiff S V_path).trans hScard
    -- Smooth elements in P_other map into S₂.
    have hP_smooth : (P_other.filter isSm).card ≤ S₂.card := by
      refine card_le_card fun q hq => ?_
      obtain ⟨hqP, hqSm⟩ := mem_filter.mp hq
      obtain ⟨hq_prLE, hq_notV⟩ := mem_sdiff.mp hqP
      have hqPrime := Nat.prime_of_mem_primesLE hq_prLE
      have hq_in_S : q ∈ S := hqSm q (by rw [hqPrime.primeFactors]; simp)
      exact mem_sdiff.mpr ⟨hq_in_S, hq_notV⟩
    -- Missing vertex m₀ ∈ {0, …, 2M} with pathVert M m₀ ∉ S.
    have hS₁_lt : S₁.card < V_path.card := by
      rw [hV_card]
      omega
    obtain ⟨q₀, hq₀V, hq₀notS₁⟩ := exists_mem_notMem_of_card_lt_card hS₁_lt
    obtain ⟨m₀, hm₀_mem, rfl⟩ := mem_image.mp hq₀V
    have hm₀_le : m₀ ≤ 2 * M := mem_Iic.mp hm₀_mem
    have hm₀_notS : pathVert M m₀ ∉ S := fun h => hq₀notS₁ (mem_inter.mpr ⟨h, hq₀V⟩)
    -- Index set J_S = {j ≤ 2M | pathVert M j ∈ S}, cardinality = S₁.card, with m₀ ∉ J_S.
    let J_S : Finset ℕ := (Iic (2 * M)).filter (fun j => pathVert M j ∈ S)
    have hJ_card : J_S.card = S₁.card := by
      have himg : J_S.image (pathVert M) = S₁ := by
        ext q
        simp only [J_S, S₁, V_path, mem_image, mem_filter, mem_inter]
        constructor
        · rintro ⟨j, ⟨hj, hjS⟩, rfl⟩
          exact ⟨hjS, ⟨j, hj, rfl⟩⟩
        · rintro ⟨hjS, ⟨j, hj, rfl⟩⟩
          exact ⟨j, ⟨hj, hjS⟩, rfl⟩
      rw [← himg, card_image_of_injOn (pathVert_injOn.mono (coe_subset.mpr (filter_subset _ _)))]
    have hm₀_notJ : m₀ ∉ J_S := by
      simp [J_S, hm₀_notS]
    -- Every smooth edge index j < 2M has both j ∈ J_S and j + 1 ∈ J_S, so j < m₀ - 0 with j + 1 < m₀, or m₀ < j.
    have hedge_smooth_iff : ∀ j : ℕ, j < 2 * M →
        (isSm (pathEdge M j) ↔ j ∈ J_S ∧ j + 1 ∈ J_S) := by
      intro j hj
      dsimp [isSm, J_S]
      rw [pathEdge_primeFactors M j]
      simp only [mem_insert, mem_singleton, mem_filter, mem_Iic]
      constructor
      · intro h
        exact ⟨⟨by omega, h _ (Or.inl rfl)⟩, ⟨by omega, h _ (Or.inr rfl)⟩⟩
      · rintro ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ p (rfl | rfl)
        · exact h₁
        · exact h₂
    let E_idx_sm : Finset ℕ := (range (2 * M)).filter (fun j => isSm (pathEdge M j))
    have hE_sm_card : (E_set.filter isSm).card = E_idx_sm.card := by
      have himg : E_idx_sm.image (pathEdge M) = E_set.filter isSm := by
        ext a
        simp only [E_idx_sm, E_set, mem_image, mem_filter]
        constructor
        · rintro ⟨j, ⟨hj, hsm⟩, rfl⟩
          exact ⟨⟨j, hj, rfl⟩, hsm⟩
        · rintro ⟨⟨j, hj, rfl⟩, hsm⟩
          exact ⟨j, ⟨hj, hsm⟩, rfl⟩
      rw [← himg, card_image_of_injOn (pathEdge_injOn.mono (coe_subset.mpr (filter_subset _ _)))]
    -- Partition J_S into 4 disjoint pieces around the missing index m₀:
    -- J₀ = {0} ∩ J_S, J_L = J_S ∩ [1, m₀ - 1], J_R = J_S ∩ [m₀ + 1, 2M - 1], J_end = {2M} ∩ J_S.
    let J₀ := J_S.filter (fun k => k = 0)
    let J_L := J_S.filter (fun k => 1 ≤ k ∧ k < m₀)
    let J_R := J_S.filter (fun k => m₀ < k ∧ k < 2 * M)
    let J_end := J_S.filter (fun k => k = 2 * M)
    have hJ_sum : J₀.card + J_L.card + J_R.card + J_end.card ≤ J_S.card := by
      have hdisj1 : Disjoint J₀ J_L :=
        Finset.disjoint_left.mpr fun k hk₀ hkL => by
          have := (mem_filter.mp hk₀).2; have := (mem_filter.mp hkL).2; omega
      have hdisj2 : Disjoint (J₀ ∪ J_L) J_R :=
        Finset.disjoint_left.mpr fun k hk0L hkR => by
          have := (mem_filter.mp hkR).2
          rcases mem_union.mp hk0L with hk₀ | hkL
          · have := (mem_filter.mp hk₀).2; omega
          · have := (mem_filter.mp hkL).2; omega
      have hdisj3 : Disjoint (J₀ ∪ J_L ∪ J_R) J_end :=
        Finset.disjoint_left.mpr fun k hk0LR hkE => by
          have := (mem_filter.mp hkE).2
          rcases mem_union.mp hk0LR with hk0L | hkR
          · rcases mem_union.mp hk0L with hk₀ | hkL
            · have := (mem_filter.mp hk₀).2; omega
            · have := (mem_filter.mp hkL).2; omega
          · have := (mem_filter.mp hkR).2; omega
      have hsubJ : J₀ ∪ J_L ∪ J_R ∪ J_end ⊆ J_S :=
        union_subset (union_subset (union_subset (filter_subset _ _) (filter_subset _ _))
          (filter_subset _ _)) (filter_subset _ _)
      calc J₀.card + J_L.card + J_R.card + J_end.card
          = (J₀ ∪ J_L ∪ J_R ∪ J_end).card := by
              rw [card_union_of_disjoint hdisj3, card_union_of_disjoint hdisj2,
                card_union_of_disjoint hdisj1]
        _ ≤ J_S.card := card_le_card hsubJ
    -- Split E_idx_sm into j < m₀ and m₀ < j (since j = m₀ is impossible as m₀ ∉ J_S).
    let E_L := E_idx_sm.filter (fun j => j < m₀)
    let E_R := E_idx_sm.filter (fun j => m₀ < j)
    have hE_split : E_idx_sm.card ≤ E_L.card + E_R.card := by
      have hsubE : E_idx_sm ⊆ E_L ∪ E_R := by
        intro j hj
        obtain ⟨hj_range, hj_sm⟩ := mem_filter.mp hj
        obtain ⟨hj_in, _⟩ := (hedge_smooth_iff j (mem_range.mp hj_range)).mp hj_sm
        have hj_ne : j ≠ m₀ := fun h => hm₀_notJ (h ▸ hj_in)
        rcases lt_or_gt_of_ne hj_ne with hlt | hgt
        · exact mem_union_left _ (mem_filter.mpr ⟨hj, hlt⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hj, hgt⟩)
      exact (card_le_card hsubE).trans (card_union_le _ _)
    have hEL_le : E_L.card ≤ J_L.card := by
      have himg : E_L.image (fun j => j + 1) ⊆ J_L := by
        intro k hk
        obtain ⟨j, hjEL, rfl⟩ := mem_image.mp hk
        obtain ⟨hjE, hj_lt⟩ := mem_filter.mp hjEL
        obtain ⟨hj_range, hj_sm⟩ := mem_filter.mp hjE
        obtain ⟨_, hj1_in⟩ := (hedge_smooth_iff j (mem_range.mp hj_range)).mp hj_sm
        have hj1_ne : j + 1 ≠ m₀ := fun h => hm₀_notJ (h ▸ hj1_in)
        exact mem_filter.mpr ⟨hj1_in, by omega, by omega⟩
      have hinj : Set.InjOn (fun j : ℕ => j + 1) (E_L : Set ℕ) :=
        fun _ _ _ _ h => Nat.succ.inj h
      rw [← card_image_of_injOn hinj]
      exact card_le_card himg
    have hER_le : E_R.card ≤ J_R.card := by
      refine card_le_card fun j hjER => ?_
      obtain ⟨hjE, hj_gt⟩ := mem_filter.mp hjER
      obtain ⟨hj_range, hj_sm⟩ := mem_filter.mp hjE
      have hj_lt2M : j < 2 * M := mem_range.mp hj_range
      obtain ⟨hj_in, _⟩ := (hedge_smooth_iff j hj_lt2M).mp hj_sm
      exact mem_filter.mpr ⟨hj_in, hj_gt, hj_lt2M⟩
    -- Bound Ends.filter isSm by J₀.card + J_end.card.
    have hEnds_le : (Ends.filter isSm).card ≤ J₀.card + J_end.card := by
      have hsub_ends : Ends ⊆ {pathVert M 0} ∪ {pathVert M (2 * M)} := by
        intro q hq
        simpa [Ends] using hq
      have h0_le : (({pathVert M 0} : Finset ℕ).filter isSm).card ≤ J₀.card := by
        by_cases h0 : isSm (pathVert M 0)
        · rw [filter_singleton, if_pos h0, card_singleton]
          have h0S : pathVert M 0 ∈ S :=
            h0 (pathVert M 0) (by rw [(pathVert_prime M 0).primeFactors]; simp)
          have h0J : 0 ∈ J₀ := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Iic.mpr (by omega), h0S⟩, rfl⟩
          exact card_pos.mpr ⟨0, h0J⟩
        · rw [filter_singleton, if_neg h0, card_empty]
          exact Nat.zero_le _
      have hend_le : (({pathVert M (2 * M)} : Finset ℕ).filter isSm).card ≤ J_end.card := by
        by_cases h2 : isSm (pathVert M (2 * M))
        · rw [filter_singleton, if_pos h2, card_singleton]
          have h2S : pathVert M (2 * M) ∈ S :=
            h2 (pathVert M (2 * M)) (by rw [(pathVert_prime M (2 * M)).primeFactors]; simp)
          have h2J : 2 * M ∈ J_end :=
            mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Iic.mpr le_rfl, h2S⟩, rfl⟩
          exact card_pos.mpr ⟨2 * M, h2J⟩
        · rw [filter_singleton, if_neg h2, card_empty]
          exact Nat.zero_le _
      calc (Ends.filter isSm).card
          ≤ ((({pathVert M 0} : Finset ℕ) ∪ {pathVert M (2 * M)}).filter isSm).card :=
            card_le_card (filter_subset_filter _ hsub_ends)
        _ ≤ (({pathVert M 0} : Finset ℕ).filter isSm).card +
            (({pathVert M (2 * M)} : Finset ℕ).filter isSm).card := by
              rw [filter_union]
              exact card_union_le _ _
        _ ≤ J₀.card + J_end.card := Nat.add_le_add h0_le hend_le
    -- Assemble total smooth count on A = (E_set ∪ Ends) ∪ P_other.
    have htotal_le : numSmooth A S ≤ r := by
      have hunion_sm : numSmooth A S ≤
          (E_set.filter isSm).card + (Ends.filter isSm).card + (P_other.filter isSm).card := by
        dsimp [numSmooth, A]
        rw [filter_union, filter_union]
        calc ((E_set.filter isSm ∪ Ends.filter isSm) ∪ P_other.filter isSm).card
            ≤ (E_set.filter isSm ∪ Ends.filter isSm).card + (P_other.filter isSm).card :=
              card_union_le _ _
          _ ≤ (E_set.filter isSm).card + (Ends.filter isSm).card + (P_other.filter isSm).card :=
              Nat.add_le_add_right (card_union_le _ _) _
      omega
    omega

/-! ### Section 5: Main Theorems — Infinitely Many Exact Equalities & Negative Answer to Part (i) -/

/-- Infinitely many integers $n$ satisfy $f(\pi(n) + 1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1$
(`Filter.Frequently` formulation). -/
theorem erdos_983.variants.upper_bound_attained_frequently :
    ∃ᶠ n : ℕ in atTop, f (Nat.primeCounting n + 1) n = 2 * Nat.primeCounting (Nat.sqrt n) + 1 := by
  rw [frequently_atTop]
  intro N₀
  obtain ⟨M, hM_ge, hpom⟩ := exists_pomerance_prime_index (by omega : 2 ≤ N₀ + 2)
  set n := (nthPrime M) ^ 2 - 1
  have hpM_ge : N₀ + 4 ≤ nthPrime M := by
    have : M + 2 ≤ nthPrime M := Nat.add_two_le_nth_prime M
    omega
  have hn_ge : N₀ ≤ n := by
    dsimp [n]
    have hsq : (N₀ + 4) * (N₀ + 4) ≤ nthPrime M * nthPrime M := Nat.mul_le_mul hpM_ge hpM_ge
    have h1 : N₀ + 1 ≤ (nthPrime M) ^ 2 := by
      rw [sq]
      nlinarith
    omega
  exact ⟨n, hn_ge, (exact_equality_at_pomerance_index (by omega) hpom).2.2⟩

/-- Set-infinitude formulation: the set of $n \ge 2$ with
$f(\pi(n) + 1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1$ is infinite. -/
theorem erdos_983.variants.infinite_exact_equality :
    {n : ℕ | 2 ≤ n ∧ f (Nat.primeCounting n + 1) n =
      2 * Nat.primeCounting (Nat.sqrt n) + 1}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N₀ => ?_
  obtain ⟨n, hn_ge, heq⟩ :=
    (frequently_atTop.mp erdos_983.variants.upper_bound_attained_frequently) (N₀ + 2)
  exact ⟨n, ⟨by omega, heq⟩, by omega⟩

/-- Negative resolution of Erdős–Straus [Er70b, pp. 138, 140] (`JSP-000816` / Erdős Problem #983,
Part (i)): it is **not** true that $2\pi(n^{1/2}) - f(\pi(n) + 1, n) \to \infty$ as $n \to \infty$. -/
theorem erdos_983.parts.i :
    ¬ Tendsto (fun n : ℕ ↦
      2 * (Nat.primeCounting (Nat.sqrt n) : ℤ) - (f (Nat.primeCounting n + 1) n : ℤ))
      atTop atTop := by
  intro hTendsto
  have hev : ∀ᶠ n : ℕ in atTop,
      (0 : ℤ) ≤ 2 * (Nat.primeCounting (Nat.sqrt n) : ℤ) - (f (Nat.primeCounting n + 1) n : ℤ) :=
    hTendsto.eventually_ge_atTop 0
  obtain ⟨n, heq, hge⟩ := (erdos_983.variants.upper_bound_attained_frequently.and_eventually hev).exists
  rw [heq] at hge
  push_cast at hge
  omega

end Erdos983
