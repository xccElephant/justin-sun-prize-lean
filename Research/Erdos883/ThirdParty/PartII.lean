/-
Third-party proof: baobingzhang/jsp-000734-erdos883-lean, Erdos883.lean.
Source pin: f87d2d526a9f736818133baed805fff4a1e94d10
Source URL:
https://github.com/baobingzhang/jsp-000734-erdos883-lean/blob/f87d2d526a9f736818133baed805fff4a1e94d10/Erdos883.lean
Source SHA256: c7cf722baa0d9e7a0ef770d0a36896caec066d9544731009d1df06d39756fe9e
Attribution: upstream author baobingzhang; formal-conjectures definitions and
statement attribution is retained in the original documentation below.

SPDX-License-Identifier: Apache-2.0
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

LOCAL COMPATIBILITY DERIVATIVE (2026-10-20): minimally ported from the supplied
Lean 4.34 / Mathlib 5ed296.. source to Lean 4.33.1 / Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. Only proof API compatibility is changed;
mathematical definitions and statements are preserved. This is reuse and
independent verification of a third-party dependency, not our mathematical
proof or a newly solved prize. See reports/bounty-only-2026-10-20/883/partii-port.
-/

import Mathlib

/-!
# Erdős Problem 883 (ii): `K(1, ℓ, ℓ)` in the coprime graph of a dense set

For `A ⊆ {1, …, n}` let `G(A)` be the coprime graph on `A`. Part (ii) of Erdős Problem 883 asks
whether, for every `ℓ ≥ 1` and all sufficiently large `n`, every `A ⊆ {1, …, n}` with
`|A| > ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋` contains a complete tripartite graph `K(1, ℓ, ℓ)` in `G(A)`.
Sárközy [Sa99] answered this affirmatively, even with `ℓ ≫ log n / log log log n`.

This file proves the statement for every fixed `ℓ`, which is the form used in formal-conjectures:
`Erdos883.erdos_883.parts.ii` (with `answer(True)` written as `True`) and the same statement
without `True ↔`, `Erdos883.erdos_883_parts_ii_direct`. The definition `coprimeGraph` and the
statement are copied verbatim from Google DeepMind's formal-conjectures project
(`FormalConjectures/ErdosProblems/883.lean`, Apache-2.0). `IsContained` is Mathlib's subgraph
containment (an injective graph homomorphism, not necessarily induced), and `coprimeGraph` has no
loops.

## Proof

Write `S` for the multiples of `2` or `3` in `[1, n]` (so `|S| = ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋`,
`card_Sset`), `B` for the elements of `A` coprime to `6` and `b = |B|`. Since `|A| > |S|`, at most
`b - 1` elements of `S` are missing from `A` (`setup`). The argument below is an elementary one for
fixed `ℓ`. It follows Sárközy's split into a sparse and a dense case, but replaces the analytic
lemmas of [Sa99] by the tools listed first. Put `ρ(k) = ∏_{p ∣ k, p ≥ 5} (1 - 1/p)` and let `ω(k)`
be the number of primes `p ≥ 5` dividing `k`.

* **Tools.** The sieve bound
  `|#{k ≤ N : k ≡ a (mod 6), p ∤ k for p ∈ T} - (N/6) ∏_{p ∈ T} (1 - 1/p)| ≤ 2^{|T|+1}`
  for a set `T` of primes `≥ 5` (`sieve`, by induction on `T`); the moment bound
  `∑_{k ≤ N} ρ(k)^{-4} ≤ 55 N` (`sum_rho_inv_pow_le`, from `ρ(k)^{-4} ≤ ∏_{p ∣ k} (1 + 15/p)` expanded
  over sets of primes); `ρ(k) ≥ 4/(ω(k) + 4)` (`rho_ge`); and `(2^{ω(k)})^4 ≤ k` once
  `ω(k) ≥ 512` (`two_pow_card_pf5_le`).
* **Sparse case `b ≤ n / 2^{2ℓ+22}`** (`case_i`). By the moment bound some `x ∈ B` has
  `b ≤ 220 n ρ(x)^4`. The chains `{2u, 4u, …, 2^ℓ u}` with `u ≤ n/2^ℓ` coprime to `6x` are pairwise
  disjoint subsets of `S`, so fewer than `b` of them contain a number outside `A`. The sieve and the
  moment bound then give an intact chain with `ρ(u) ≥ ρ(x)/6`. Finally the sieve gives at least
  `b + ℓ` odd multiples of `3` in `[1, n]` coprime to `xu`, so `ℓ` of them lie in `A`. The number `x`,
  the chain and these `ℓ` numbers form `K(1, ℓ, ℓ)`.
* **Dense case `b > n / 2^{2ℓ+22}`** (`case_ii`). Put `r = (64ℓ + 16) 2^{4ℓ+46} + 7`, `P = r!` and
  `β = 2^{-(2ℓ+23)}`. Choose `c ∈ {1, 5}` with `|A ∩ (c mod 6)| ≥ b/2` and group the residues modulo
  `P` into `P/6` blocks of seven consecutive residues, overlapping in the residues `≡ c (mod 6)`
  (`block_total`). The block sums add up to `|A| + |A ∩ (c mod 6)| ≥ 2n/3 + βn`, so some block has at
  least five classes containing `≥ βn/P` elements of `A`. Among any five of the seven offsets there
  are three whose classes share no prime `≤ r` (`pattern`, a finite check by `decide`, and
  `no_small_common`). Pairs from two such classes with a common prime `p > r` number at most
  `∑_{p > r} (n/(pP) + 1)^2 ≤ 2 (n/P)^2 / r + 2n` (`bad_pairs_le`). Averaging gives a centre `x` in the
  first class with few non-coprime partners in the other two, and a Markov-type greedy argument
  (`greedy`) finds `K(ℓ, ℓ)` among the elements of the other two classes that are coprime to `x`.

## What remains open

Part (i) of Erdős Problem 883 (all odd cycles of length `≤ n/3 + 1`) is open and not treated here.
Sárközy's quantitative result, with `ℓ` growing like `log n / log log log n`, is not formalized;
the thresholds for `n` in this file are very large and not optimized.

## References

* [Sa99] Sárközy, G. N., _Complete tripartite subgraphs in the coprime graph of integers_.
  Discrete Math. 202 (1999), 227–238.
* [ErSa97] Erdős, P. and Sárközy, G. N., _On cycles in the coprime graph of integers_.
  Electron. J. Combin. 4 (1997), Research Paper 8.
* [erdosproblems.com/883](https://www.erdosproblems.com/883)
-/

open Finset Filter

namespace Erdos883

-- Copied verbatim from formal-conjectures, `FormalConjectures/ErdosProblems/883.lean`.
/--
The coprime graph on $\mathbb{N}$: two integers are joined by an edge if they are coprime.
-/
def coprimeGraph : SimpleGraph ℕ :=
  SimpleGraph.fromRel Nat.Coprime

/-- The primes `p ≥ 5` dividing `k`. -/
def pf5 (k : ℕ) : Finset ℕ := k.primeFactors.filter (fun p => 5 ≤ p)

/-- `∏_{p ∈ T} (1 - 1/p)`. -/
noncomputable def rhoS (T : Finset ℕ) : ℝ := ∏ p ∈ T, (1 - 1 / (p : ℝ))

/-- `ρ(k) = ∏_{p ∣ k, p ≥ 5} (1 - 1/p)`. -/
noncomputable def rho (k : ℕ) : ℝ := rhoS (pf5 k)

/-- `#{k ∈ [1, N] : k ≡ a (mod 6), p ∤ k for all p ∈ T}`. -/
def cnt (N a : ℕ) (T : Finset ℕ) : ℕ :=
  ((Icc 1 N).filter (fun k => k % 6 = a ∧ ∀ p ∈ T, ¬ p ∣ k)).card

lemma mem_pf5 {k p : ℕ} : p ∈ pf5 k ↔ p.Prime ∧ p ∣ k ∧ k ≠ 0 ∧ 5 ≤ p := by
  simp [pf5, Nat.mem_primeFactors, and_assoc]

lemma rhoS_nonneg {T : Finset ℕ} (hT : ∀ p ∈ T, 1 ≤ p) : 0 ≤ rhoS T := by
  refine prod_nonneg fun p hp => ?_
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hT p hp
  rw [sub_nonneg]
  exact div_le_one_of_le₀ h1 (by linarith)

lemma rhoS_pos {T : Finset ℕ} (hT : ∀ p ∈ T, 2 ≤ p) : 0 < rhoS T := by
  refine prod_pos fun p hp => ?_
  have h1 : (2 : ℝ) ≤ p := by exact_mod_cast hT p hp
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

lemma rhoS_le_one {T : Finset ℕ} (hT : ∀ p ∈ T, 1 ≤ p) : rhoS T ≤ 1 := by
  refine Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)
  · have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hT p hp
    rw [sub_nonneg]
    exact div_le_one_of_le₀ h1 (by linarith)
  · have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hT p hp
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith

lemma rho_pos (k : ℕ) : 0 < rho k :=
  rhoS_pos fun p hp => by have := (mem_pf5.1 hp); omega

lemma rho_le_one (k : ℕ) : rho k ≤ 1 :=
  rhoS_le_one fun p hp => by have := (mem_pf5.1 hp); omega

/-- A set of naturals `≤ N` which are pairwise congruent modulo `m` has at most `N/m + 1`
elements. -/
lemma card_le_of_modEq {S : Finset ℕ} {m N : ℕ} (hS : ∀ k ∈ S, k ≤ N)
    (hmod : ∀ k ∈ S, ∀ k' ∈ S, k % m = k' % m) : S.card ≤ N / m + 1 := by
  have : S.card ≤ (range (N / m + 1)).card := by
    refine card_le_card_of_injOn (fun k => k / m) (fun k hk => ?_) (fun k hk k' hk' h => ?_)
    · simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (hS k hk))
    · have h1 := Nat.div_add_mod k m
      have h2 := Nat.div_add_mod k' m
      have h3 := hmod k hk k' hk'
      simp only at h
      rw [← h1, ← h2, h, h3]
  simpa using this

lemma prime_mod_six {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : p % 2 = 1 := by
    rcases Nat.even_or_odd p with h | h
    · exfalso
      have := (Nat.Prime.even_iff hp).1 h
      omega
    · exact Nat.odd_iff.1 h
  have h3 : p % 3 ≠ 0 := by
    intro h
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  omega

lemma mod6_mul {p k a : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) (ha : a < 6) :
    (p * k) % 6 = a ↔ k % 6 = (a * p) % 6 := by
  rw [Nat.mul_mod, Nat.mul_mod a]
  have hk : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases hp with hp | hp <;> rw [hp] <;> interval_cases hk' : k % 6 <;> interval_cases a <;>
    simp

lemma cnt_insert (N a p : ℕ) (T : Finset ℕ) (ha : a < 6) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpT : p ∉ T) (hT : ∀ q ∈ T, q.Prime) :
    cnt N a T = cnt N a (insert p T) + cnt (N / p) ((a * p) % 6) T := by
  unfold cnt
  rw [← card_filter_add_card_filter_not (fun k => ¬ p ∣ k)]
  have hp6 := prime_mod_six hp hp5
  have hp0 : 0 < p := hp.pos
  congr 1
  · congr 1
    ext k
    simp only [mem_filter, mem_Icc, mem_insert, forall_eq_or_imp]
    tauto
  · refine card_bij' (fun k _ => k / p) (fun k' _ => p * k') ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_filter, mem_Icc, not_not] at hk ⊢
      obtain ⟨⟨⟨hk1, hkN⟩, hka, hkT⟩, hpk⟩ := hk
      obtain ⟨c, rfl⟩ := hpk
      rw [Nat.mul_div_cancel_left c hp0]
      refine ⟨⟨?_, ?_⟩, (mod6_mul hp6 ha).1 hka, fun q hq hqc => hkT q hq (dvd_mul_of_dvd_right hqc p)⟩
      · rcases Nat.eq_zero_or_pos c with h | h
        · simp [h] at hk1
        · exact h
      · exact (Nat.le_div_iff_mul_le hp0).2 (by linarith [Nat.mul_comm c p])
    · intro k' hk'
      simp only [mem_filter, mem_Icc, not_not] at hk' ⊢
      obtain ⟨⟨hk1, hkN⟩, hka, hkT⟩ := hk'
      refine ⟨⟨⟨?_, ?_⟩, (mod6_mul hp6 ha).2 hka, fun q hq hqd => ?_⟩, dvd_mul_right p k'⟩
      · nlinarith
      · have := (Nat.le_div_iff_mul_le hp0).1 hkN
        linarith [Nat.mul_comm k' p]
      · rcases (Nat.Prime.dvd_mul (hT q hq)).1 hqd with h | h
        · have := (Nat.prime_dvd_prime_iff_eq (hT q hq) hp).1 h
          exact hpT (this ▸ hq)
        · exact hkT q hq h
    · intro k hk
      simp only [mem_filter, not_not] at hk
      exact Nat.mul_div_cancel' hk.2
    · intro k' _
      exact Nat.mul_div_cancel_left k' hp0

lemma cnt_empty_bound (N a : ℕ) (ha : a < 6) :
    |(cnt N a ∅ : ℝ) - N / 6 * rhoS ∅| ≤ 1 := by
  simp only [rhoS, prod_empty, mul_one]
  set S := (Icc 1 N).filter (fun k => k % 6 = a ∧ ∀ p ∈ (∅ : Finset ℕ), ¬ p ∣ k) with hS
  have hup : S.card ≤ N / 6 + 1 := by
    refine card_le_of_modEq (fun k hk => ?_) (fun k hk k' hk' => ?_)
    · simp only [hS, mem_filter, mem_Icc] at hk
      exact hk.1.2
    · simp only [hS, mem_filter] at hk hk'
      rw [hk.2.1, hk'.2.1]
  have hlow : N / 6 ≤ S.card := by
    have : (range (N / 6)).card ≤ S.card := by
      refine card_le_card_of_injOn (fun q => 6 * q + (if a = 0 then 6 else a))
        (fun q hq => ?_) (fun q _ q' _ h => ?_)
      · simp only [coe_range, Set.mem_Iio] at hq
        simp only [hS, coe_filter, mem_Icc, Set.mem_ofPred_eq, notMem_empty, IsEmpty.forall_iff,
          implies_true, and_true]
        have hq' : 6 * q + 6 ≤ N := by omega
        split_ifs with h0 <;> refine ⟨⟨by omega, by omega⟩, by omega⟩
      · simp only at h
        split_ifs at h <;> omega
    simpa using this
  have h1 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := Nat.cast_div_le
  have h2 : (N : ℝ) / 6 < ((N / 6 : ℕ) : ℝ) + 1 := by
    have := Nat.div_add_mod N 6
    have hm : N % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have : (N : ℝ) = 6 * ((N / 6 : ℕ) : ℝ) + ((N % 6 : ℕ) : ℝ) := by exact_mod_cast this.symm
    have hm' : ((N % 6 : ℕ) : ℝ) < 6 := by exact_mod_cast hm
    rw [this]
    linarith
  have hup' : (S.card : ℝ) ≤ ((N / 6 : ℕ) : ℝ) + 1 := by exact_mod_cast hup
  have hlow' : ((N / 6 : ℕ) : ℝ) ≤ S.card := by exact_mod_cast hlow
  change |(S.card : ℝ) - N / 6| ≤ 1
  rw [abs_le]
  constructor <;> linarith

/-- The sieve estimate
`|#{k ≤ N : k ≡ a (6), p ∤ k ∀ p ∈ T} - (N/6) ∏_{p ∈ T} (1 - 1/p)| ≤ 2^{|T|+1} - 1`
for a finite set `T` of primes `≥ 5`. -/
theorem sieve (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ 5 ≤ p) :
    ∀ N a, a < 6 → |(cnt N a T : ℝ) - N / 6 * rhoS T| ≤ 2 ^ (T.card + 1) - 1 := by
  induction T using Finset.induction_on with
  | empty =>
    intro N a ha
    have := cnt_empty_bound N a ha
    norm_num at this ⊢
    exact this
  | insert p T hpT ih =>
    intro N a ha
    have hp := hT p (mem_insert_self p T)
    have hT' : ∀ q ∈ T, q.Prime ∧ 5 ≤ q := fun q hq => hT q (mem_insert_of_mem hq)
    have hid := cnt_insert N a p T ha hp.1 hp.2 hpT (fun q hq => (hT' q hq).1)
    have hc : ((cnt N a (insert p T) : ℕ) : ℝ) =
        (cnt N a T : ℝ) - (cnt (N / p) ((a * p) % 6) T : ℝ) := by
      rw [hid]; push_cast; ring
    have hρ : rhoS (insert p T) = (1 - 1 / (p : ℝ)) * rhoS T := by
      unfold rhoS; rw [prod_insert hpT]
    have hcard : (insert p T).card = T.card + 1 := card_insert_of_notMem hpT
    have ih1 := ih hT' N a ha
    have ih2 := ih hT' (N / p) ((a * p) % 6) (Nat.mod_lt _ (by norm_num))
    have hρ0 : 0 ≤ rhoS T := rhoS_nonneg fun q hq => by have := hT' q hq; omega
    have hρ1 : rhoS T ≤ 1 := rhoS_le_one fun q hq => by have := hT' q hq; omega
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
    have hfl1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    have hfl2 : (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 := by
      have e := Nat.div_add_mod N p
      have hm : N % p < p := Nat.mod_lt _ hp.1.pos
      have : (N : ℝ) = p * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) := by exact_mod_cast e.symm
      have hm' : ((N % p : ℕ) : ℝ) ≤ p := by exact_mod_cast hm.le
      rw [div_le_iff₀ hp0, this]
      nlinarith
    rw [hc, hρ, hcard]
    have key : (cnt N a T : ℝ) - (cnt (N / p) ((a * p) % 6) T : ℝ) -
        N / 6 * ((1 - 1 / (p : ℝ)) * rhoS T) =
        ((cnt N a T : ℝ) - N / 6 * rhoS T) -
        ((cnt (N / p) ((a * p) % 6) T : ℝ) - ((N / p : ℕ) : ℝ) / 6 * rhoS T)
        + ((N : ℝ) / p - ((N / p : ℕ) : ℝ)) * rhoS T / 6 := by
      field_simp
      ring
    rw [key]
    have hpow : (2 : ℝ) ^ (T.card + 1 + 1) = 2 * 2 ^ (T.card + 1) := by ring
    rw [hpow]
    have hx : 0 ≤ ((N : ℝ) / p - ((N / p : ℕ) : ℝ)) * rhoS T / 6 := by
      have : 0 ≤ (N : ℝ) / p - ((N / p : ℕ) : ℝ) := by linarith
      positivity
    have hy : ((N : ℝ) / p - ((N / p : ℕ) : ℝ)) * rhoS T / 6 ≤ 1 / 6 := by
      have h1 : (N : ℝ) / p - ((N / p : ℕ) : ℝ) ≤ 1 := by linarith
      have h0 : 0 ≤ (N : ℝ) / p - ((N / p : ℕ) : ℝ) := by linarith
      have : ((N : ℝ) / p - ((N / p : ℕ) : ℝ)) * rhoS T ≤ 1 := by nlinarith
      linarith
    rw [abs_le] at ih1 ih2 ⊢
    constructor <;> nlinarith [ih1.1, ih1.2, ih2.1, ih2.2]

/-- `∑_{a < j ≤ M} 1/j² ≤ 1/a - 1/M`. -/
lemma sum_Ioc_inv_sq_le (a : ℕ) (ha : 1 ≤ a) :
    ∀ M, a ≤ M → ∑ j ∈ Ioc a M, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 1 / a - 1 / M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans ha hM
    have key : (1 : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / M - 1 / ((M + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

lemma sum_Ioc_inv_sq_le' (a : ℕ) (ha : 1 ≤ a) (M : ℕ) :
    ∑ j ∈ Ioc a M, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 1 / a := by
  rcases le_or_gt a M with h | h
  · have := sum_Ioc_inv_sq_le a ha M h
    have : (0 : ℝ) ≤ 1 / M := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [sum_empty]
    positivity

lemma inv_pow_four_le {p : ℝ} (hp : 5 ≤ p) : ((1 - 1 / p)⁻¹) ^ 4 ≤ 1 + 15 / p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have h1 : ((1 - 1 / p)⁻¹) ^ 4 = p ^ 4 / (p - 1) ^ 4 := by
    field_simp
  have h2 : 1 + 15 / p = (p + 15) / p := by field_simp
  rw [h1, h2, div_le_div_iff₀ (by positivity) hp0]
  have h3 : 0 ≤ 11 * p ^ 4 - 54 * p ^ 3 + 86 * p ^ 2 - 59 * p + 15 := by
    nlinarith [sq_nonneg (p - 5), mul_nonneg (mul_nonneg hp0.le hp0.le) (sub_nonneg.2 hp),
      mul_nonneg (mul_nonneg (mul_nonneg hp0.le hp0.le) hp0.le) (sub_nonneg.2 hp),
      mul_nonneg hp0.le (sub_nonneg.2 hp)]
  nlinarith [h3]

lemma prod_dvd_of_primes {U : Finset ℕ} {k : ℕ} (hU : ∀ p ∈ U, p.Prime ∧ p ∣ k) :
    ∏ p ∈ U, p ∣ k := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert p U hpU ih =>
    rw [prod_insert hpU]
    have hp := hU p (mem_insert_self p U)
    have ih' := ih fun q hq => hU q (mem_insert_of_mem hq)
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ hp.2 ih'
    refine Nat.Coprime.prod_right fun q hq => ?_
    have hq' := hU q (mem_insert_of_mem hq)
    exact (Nat.coprime_primes hp.1 hq'.1).2 (fun h => hpU (h ▸ hq))

lemma rho_inv_pow_le (k : ℕ) : (rho k)⁻¹ ^ 4 ≤ ∏ p ∈ pf5 k, (1 + 15 / (p : ℝ)) := by
  unfold rho rhoS
  rw [← prod_inv_distrib, ← prod_pow]
  refine Finset.prod_le_prod (fun p hp => by positivity) (fun p hp => ?_)
  have := (mem_pf5.1 hp).2.2.2
  exact inv_pow_four_le (by exact_mod_cast this)

lemma exp_fifteen_quarter_le : Real.exp (15 / 4) ≤ 55 := by
  have h1 : Real.exp (15 / 4) ≤ Real.exp 4 := Real.exp_le_exp.2 (by norm_num)
  have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 := Real.exp_one_lt_d9
  have h4 : 0 < Real.exp 1 := Real.exp_pos 1
  have h5 : Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
  have h6 : (2.7182818286 : ℝ) ^ 4 ≤ 55 := by norm_num
  linarith

/-- The fourth moment bound `∑_{k ≤ N} ρ(k)^{-4} ≤ 55 N`. -/
theorem sum_rho_inv_pow_le (N : ℕ) : ∑ k ∈ Icc 1 N, (rho k)⁻¹ ^ 4 ≤ 55 * N := by
  set P5 := (Icc 5 N).filter Nat.Prime with hP5
  have step1 : ∑ k ∈ Icc 1 N, (rho k)⁻¹ ^ 4 ≤
      ∑ k ∈ Icc 1 N, ∑ U ∈ (pf5 k).powerset, ∏ p ∈ U, (15 / (p : ℝ)) := by
    refine sum_le_sum fun k hk => ?_
    rw [← prod_one_add]
    exact rho_inv_pow_le k
  have step2 : ∑ k ∈ Icc 1 N, ∑ U ∈ (pf5 k).powerset, ∏ p ∈ U, (15 / (p : ℝ)) =
      ∑ U ∈ P5.powerset, ∑ k ∈ (Icc 1 N).filter (fun k => U ⊆ pf5 k),
        ∏ p ∈ U, (15 / (p : ℝ)) := by
    refine sum_comm' fun k U => ?_
    simp only [mem_powerset, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hk, hU⟩
      refine ⟨⟨hk, hU⟩, fun p hp => ?_⟩
      have := mem_pf5.1 (hU hp)
      simp only [hP5, mem_filter, mem_Icc]
      exact ⟨⟨this.2.2.2, le_trans (Nat.le_of_dvd (by omega) this.2.1) hk.2⟩, this.1⟩
    · rintro ⟨⟨hk, hU⟩, _⟩
      exact ⟨hk, hU⟩
  have step3 : ∀ U ∈ P5.powerset, ∑ k ∈ (Icc 1 N).filter (fun k => U ⊆ pf5 k),
      ∏ p ∈ U, (15 / (p : ℝ)) ≤ N * ∏ p ∈ U, (15 / (p : ℝ) ^ 2) := by
    intro U hU
    rw [sum_const, nsmul_eq_mul]
    have hUp : ∀ p ∈ U, p.Prime := by
      intro p hp
      have := (mem_powerset.1 hU) hp
      simp only [hP5, mem_filter] at this
      exact this.2
    have hpos : 0 < ∏ p ∈ U, p := prod_pos fun p hp => (hUp p hp).pos
    have hcard : ((Icc 1 N).filter (fun k => U ⊆ pf5 k)).card ≤ N / ∏ p ∈ U, p := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div]
      refine card_le_card fun k hk => ?_
      simp only [mem_filter, mem_Icc, mem_Ioc] at hk ⊢
      refine ⟨by omega, prod_dvd_of_primes fun p hp => ?_⟩
      have := mem_pf5.1 (hk.2 hp)
      exact ⟨this.1, this.2.1⟩
    have hcard' : (((Icc 1 N).filter (fun k => U ⊆ pf5 k)).card : ℝ) ≤
        (N : ℝ) / ((∏ p ∈ U, p : ℕ) : ℝ) :=
      le_trans (by exact_mod_cast hcard) Nat.cast_div_le
    have hnn : 0 ≤ ∏ p ∈ U, (15 / (p : ℝ)) := prod_nonneg fun p _ => by positivity
    calc (((Icc 1 N).filter (fun k => U ⊆ pf5 k)).card : ℝ) * ∏ p ∈ U, (15 / (p : ℝ))
        ≤ (N : ℝ) / ((∏ p ∈ U, p : ℕ) : ℝ) * ∏ p ∈ U, (15 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard' hnn
      _ = N * ∏ p ∈ U, (15 / (p : ℝ) ^ 2) := by
          push_cast
          rw [div_eq_mul_inv, mul_assoc, ← prod_inv_distrib, ← prod_mul_distrib]
          congr 1
          refine prod_congr rfl fun p hp => ?_
          have : (p : ℝ) ≠ 0 := by exact_mod_cast (hUp p hp).ne_zero
          field_simp
  have step4 : ∑ U ∈ P5.powerset, (N : ℝ) * ∏ p ∈ U, (15 / (p : ℝ) ^ 2) =
      N * ∏ p ∈ P5, (1 + 15 / (p : ℝ) ^ 2) := by
    rw [← mul_sum, prod_one_add]
  have step5 : ∏ p ∈ P5, (1 + 15 / (p : ℝ) ^ 2) ≤ 55 := by
    have h1 : ∏ p ∈ P5, (1 + 15 / (p : ℝ) ^ 2) ≤ ∏ p ∈ P5, Real.exp (15 / (p : ℝ) ^ 2) :=
      Finset.prod_le_prod (fun p _ => by positivity) fun p _ => by
        have := Real.add_one_le_exp (15 / (p : ℝ) ^ 2); linarith
    rw [← Real.exp_sum] at h1
    have h2 : ∑ p ∈ P5, 15 / (p : ℝ) ^ 2 ≤ 15 / 4 := by
      have h3 : P5 ⊆ Ioc 4 N := by
        intro p hp
        simp only [hP5, mem_filter, mem_Icc] at hp
        simp only [mem_Ioc]; omega
      have h4 := sum_le_sum_of_subset_of_nonneg h3 (f := fun j : ℕ => 1 / (j : ℝ) ^ 2)
        (fun _ _ _ => by positivity)
      have h5 := sum_Ioc_inv_sq_le' 4 (by norm_num) N
      have : ∑ p ∈ P5, 15 / (p : ℝ) ^ 2 = 15 * ∑ p ∈ P5, 1 / (p : ℝ) ^ 2 := by
        rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
      rw [this]
      push_cast at h5
      linarith
    exact le_trans h1 (le_trans (Real.exp_le_exp.2 h2) exp_fifteen_quarter_le)
  calc ∑ k ∈ Icc 1 N, (rho k)⁻¹ ^ 4 ≤ _ := step1
    _ = _ := step2
    _ ≤ ∑ U ∈ P5.powerset, (N : ℝ) * ∏ p ∈ U, (15 / (p : ℝ) ^ 2) := sum_le_sum step3
    _ = _ := step4
    _ ≤ N * 55 := mul_le_mul_of_nonneg_left step5 (by positivity)
    _ = 55 * N := by ring

/-- `∏_{p ∈ T} (1 - 1/p) ≥ 4/(|T| + 4)` for a set `T` of integers `≥ 5`. -/
lemma rhoS_ge (T : Finset ℕ) (hT : ∀ p ∈ T, 5 ≤ p) : 4 / ((T.card : ℝ) + 4) ≤ rhoS T := by
  induction T using Finset.induction_on_max with
  | empty => simp [rhoS]
  | insert a s has ih =>
    have ha5 : 5 ≤ a := hT a (mem_insert_self a s)
    have hs5 : ∀ p ∈ s, 5 ≤ p := fun p hp => hT p (mem_insert_of_mem hp)
    have ih' := ih hs5
    have has' : a ∉ s := fun h => lt_irrefl a (has a h)
    have hcard_s : s.card ≤ a - 5 := by
      have : s ⊆ Ico 5 a := fun p hp => mem_Ico.2 ⟨hs5 p hp, has p hp⟩
      simpa using card_le_card this
    rw [card_insert_of_notMem has']
    unfold rhoS at ih' ⊢
    rw [prod_insert has']
    have hc : (s.card : ℝ) + 5 ≤ a := by
      have : s.card + 5 ≤ a := by omega
      exact_mod_cast this
    have ha0 : (0 : ℝ) < a := by linarith [show (0 : ℝ) ≤ s.card from by positivity]
    have hfac : ((s.card : ℝ) + 4) / ((s.card : ℝ) + 5) ≤ 1 - 1 / (a : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 / (a : ℝ) ≤ 1 / ((s.card : ℝ) + 5) := one_div_le_one_div_of_le (by positivity) hc
      have h2 : (1 / ((s.card : ℝ) + 5)) * ((s.card : ℝ) + 5) = 1 := by field_simp
      nlinarith
    have hpos : 0 ≤ 4 / ((s.card : ℝ) + 4) := by positivity
    calc 4 / (((s.card + 1 : ℕ) : ℝ) + 4)
        = ((s.card : ℝ) + 4) / ((s.card : ℝ) + 5) * (4 / ((s.card : ℝ) + 4)) := by
          push_cast; field_simp; ring
      _ ≤ (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
          mul_le_mul hfac ih' hpos (by have : (0:ℝ) < 1 / a := by positivity
                                       have : 1 / (a : ℝ) ≤ 1 / 5 := by
                                         rw [div_le_div_iff₀ ha0 (by norm_num)]
                                         have : (5 : ℝ) ≤ a := by exact_mod_cast ha5
                                         linarith
                                       linarith)

lemma rho_ge (k : ℕ) : 4 / (((pf5 k).card : ℝ) + 4) ≤ rho k :=
  rhoS_ge _ fun _ hp => (mem_pf5.1 hp).2.2.2

lemma prod_pf5_le (k : ℕ) (hk : k ≠ 0) : ∏ p ∈ pf5 k, p ≤ k :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hk)
    (prod_dvd_of_primes fun _ hp => ⟨(mem_pf5.1 hp).1, (mem_pf5.1 hp).2.1⟩)

/-- If `k` has at least `512` prime factors `≥ 5`, then `(2^ω)^4 ≤ k`. -/
lemma two_pow_card_pf5_le (k : ℕ) (hk : k ≠ 0) (h : 512 ≤ (pf5 k).card) :
    (2 ^ (pf5 k).card) ^ 4 ≤ k := by
  have hsmall : ((pf5 k).filter (fun p => ¬ 256 ≤ p)).card ≤ 256 := by
    have : (pf5 k).filter (fun p => ¬ 256 ≤ p) ⊆ range 256 := fun p hp => by
      simp only [mem_filter, not_le] at hp; simpa using hp.2
    simpa using card_le_card this
  have hsplit := card_filter_add_card_filter_not (s := pf5 k) (fun p => 256 ≤ p)
  have hT' : (pf5 k).card ≤ ((pf5 k).filter (fun p => 256 ≤ p)).card + 256 := by omega
  have h1 : 256 ^ ((pf5 k).filter (fun p => 256 ≤ p)).card ≤
      ∏ p ∈ (pf5 k).filter (fun p => 256 ≤ p), p := by
    rw [← prod_const]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => (mem_filter.1 hp).2
  have h2 : ∏ p ∈ (pf5 k).filter (fun p => 256 ≤ p), p ≤ ∏ p ∈ pf5 k, p :=
    Finset.prod_le_prod_of_subset_of_one_le (filter_subset _ _)
      (fun _ _ => Nat.zero_le _) fun p hp _ => by
      have := (mem_pf5.1 hp).2.2.2; omega
  have h3 := prod_pf5_le k hk
  have h4 : (2 ^ (pf5 k).card) ^ 4 ≤ 256 ^ ((pf5 k).filter (fun p => 256 ≤ p)).card := by
    generalize ((pf5 k).filter (fun p => 256 ≤ p)).card = t at hT' ⊢
    have e1 : (256 : ℕ) ^ t = 2 ^ (8 * t) := by rw [pow_mul]; norm_num
    rw [← pow_mul, e1]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact le_trans h4 (le_trans h1 (le_trans h2 h3))

lemma sq_add_four_le (m : ℕ) : ((m : ℝ) + 4) ^ 2 ≤ 36 * 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    push_cast
    have : ((m : ℝ) + 1 + 4) ^ 2 ≤ 2 * ((m : ℝ) + 4) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ m from by positivity]
    have h2 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [h2]
    linarith

/-- The multiples of `2` or `3` in `[1, n]`. -/
def Sset (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun k => k % 2 = 0 ∨ k % 3 = 0)

/-- The elements of `A` coprime to `6`. -/
def Bset (A : Finset ℕ) : Finset ℕ := A.filter (fun k => k % 6 = 1 ∨ k % 6 = 5)

/-- `A` contains a vertex `x` and two disjoint `l`-sets `Y`, `Z` with all cross pairs coprime. -/
def Good (A : Finset ℕ) (l : ℕ) : Prop :=
  ∃ x ∈ A, ∃ Y Z : Finset ℕ, Y ⊆ A ∧ Z ⊆ A ∧ Y.card = l ∧ Z.card = l ∧ x ∉ Y ∧ x ∉ Z ∧
    Disjoint Y Z ∧ (∀ y ∈ Y, Nat.Coprime x y) ∧ (∀ z ∈ Z, Nat.Coprime x z) ∧
    (∀ y ∈ Y, ∀ z ∈ Z, Nat.Coprime y z)

lemma card_filter_dvd_Icc (n d : ℕ) :
    ((Icc 1 n).filter (fun k => d ∣ k)).card = n / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1

lemma card_Sset (n : ℕ) : (Sset n).card = n / 2 + n / 3 - n / 6 := by
  have h2 : ((Icc 1 n).filter (fun k => k % 2 = 0)).card = n / 2 := by
    rw [← card_filter_dvd_Icc]; congr 1; ext k; simp [Nat.dvd_iff_mod_eq_zero]
  have h3 : ((Icc 1 n).filter (fun k => k % 3 = 0)).card = n / 3 := by
    rw [← card_filter_dvd_Icc]; congr 1; ext k; simp [Nat.dvd_iff_mod_eq_zero]
  have h6 : ((Icc 1 n).filter (fun k => k % 2 = 0 ∧ k % 3 = 0)).card = n / 6 := by
    rw [← card_filter_dvd_Icc]; congr 1; ext k; simp [Nat.dvd_iff_mod_eq_zero]; omega
  have hu := card_union_add_card_inter ((Icc 1 n).filter (fun k => k % 2 = 0))
    ((Icc 1 n).filter (fun k => k % 3 = 0))
  rw [← filter_or, ← filter_and, h2, h3, h6] at hu
  unfold Sset
  omega

/-- The basic counting consequence of `|A| > |S|`: every `T ⊆ S` satisfies
`|T| + 1 ≤ |T ∩ A| + |B|`. -/
lemma setup {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n) (hcard : n / 2 + n / 3 - n / 6 < A.card)
    (T : Finset ℕ) (hT : T ⊆ Sset n) :
    T.card + 1 ≤ (T.filter (· ∈ A)).card + (Bset A).card := by
  have hAsplit := card_filter_add_card_filter_not (s := A) (fun k => k % 6 = 1 ∨ k % 6 = 5)
  have hAS : (A.filter (fun k => ¬ (k % 6 = 1 ∨ k % 6 = 5))) ⊆ (Sset n).filter (· ∈ A) := by
    intro k hk
    simp only [mem_filter] at hk
    simp only [Sset, mem_filter]
    exact ⟨⟨hA hk.1, by omega⟩, hk.1⟩
  have h1 := card_le_card hAS
  have hSsplit := card_filter_add_card_filter_not (s := Sset n) (· ∈ A)
  have hTsplit := card_filter_add_card_filter_not (s := T) (· ∈ A)
  have hTS : T.filter (· ∉ A) ⊆ (Sset n).filter (· ∉ A) := by
    intro k hk
    simp only [mem_filter] at hk ⊢
    exact ⟨hT hk.1, hk.2⟩
  have h2 := card_le_card hTS
  have hS := card_Sset n
  unfold Bset
  omega

lemma coprime_of_no_common {m k : ℕ} (h2 : ¬(2 ∣ m ∧ 2 ∣ k)) (h3 : ¬(3 ∣ m ∧ 3 ∣ k))
    (h5 : ∀ p, p.Prime → 5 ≤ p → p ∣ m → p ∣ k → False) : Nat.Coprime m k := by
  refine Nat.coprime_of_dvd fun p hp hm hk => ?_
  by_cases h : 5 ≤ p
  · exact h5 p hp h hm hk
  · have h2' := hp.two_le
    interval_cases p
    · exact h2 ⟨hm, hk⟩
    · exact h3 ⟨hm, hk⟩
    · norm_num at hp

lemma rhoS_union_ge (W W2 : Finset ℕ) (hW : ∀ p ∈ W, 1 ≤ p) (hW2 : ∀ p ∈ W2, 1 ≤ p) :
    rhoS W * rhoS W2 ≤ rhoS (W ∪ W2) := by
  have e1 : W ∪ W2 = W ∪ (W2 \ W) := by rw [union_sdiff_self_eq_union]
  have hdisj : Disjoint W (W2 \ W) := disjoint_sdiff_self_right
  have e2 : rhoS (W ∪ W2) = rhoS W * rhoS (W2 \ W) := by
    unfold rhoS; rw [e1, prod_union hdisj]
  have e3 : rhoS (W2 \ W) * rhoS (W2 ∩ W) = rhoS W2 := by
    unfold rhoS
    have := prod_sdiff (f := fun p : ℕ => (1 - 1 / (p : ℝ))) (inter_subset_left (s₁ := W2) (s₂ := W))
    rwa [sdiff_inter_self_left] at this
  have h0 : 0 ≤ rhoS (W2 \ W) :=
    rhoS_nonneg fun p hp => hW2 p (mem_sdiff.1 hp).1
  have h1 : rhoS (W2 ∩ W) ≤ 1 := rhoS_le_one fun p hp => hW2 p (mem_inter.1 hp).1
  have h2 : rhoS W2 ≤ rhoS (W2 \ W) := by rw [← e3]; nlinarith
  have h3 : 0 ≤ rhoS W := rhoS_nonneg hW
  rw [e2]
  exact mul_le_mul_of_nonneg_left h2 h3

lemma odd_part_inj {a b u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 1) (h : 2 ^ a * u = 2 ^ b * v) :
    u = v := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    have : 2 ∣ u := h' ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (by norm_num) v) _
    omega
  · exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    have : 2 ∣ v := h' ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (by norm_num) u) _
    omega

/-- The real inequalities needed in the sparse case. -/
lemma numeric_i (l : ℕ) (n q R b E1 E2 : ℝ) (hq : q ^ 4 = n) (hq325 : 325 ≤ q)
    (hql : 162 * (l : ℝ) ≤ q ^ 2) (hq2 : 9 * 2 ^ (l + 3) ≤ q ^ 2) (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hb1 : b ≤ n / 2 ^ (2 * l + 22)) (hb2 : b ≤ 220 * n * R ^ 4) (hE1 : E1 ≤ q) (hE2 : E2 ≤ q)
    (hE20 : 0 ≤ E2) (hRE : 16 ≤ R ^ 2 * (36 * E1)) :
    0 < n * R / 2 ^ (l + 2) - 1 / 4 - 4 * E1 - b + 1 ∧
      (l : ℝ) ≤ n * R ^ 2 / 36 - 2 * E1 * E2 - (b - 1) := by
  set T : ℝ := 2 ^ l with hT
  have hT1 : 1 ≤ T := one_le_pow₀ (by norm_num)
  have e2 : (2 : ℝ) ^ (l + 2) = 4 * T := by rw [hT, pow_add]; ring
  have e3 : (2 : ℝ) ^ (l + 3) = 8 * T := by rw [hT, pow_add]; ring
  have e22 : (2 : ℝ) ^ (2 * l + 22) = T ^ 2 * 4194304 := by
    rw [hT, pow_add, mul_comm 2 l, pow_mul]; norm_num
  rw [e3] at hq2
  rw [e22] at hb1
  rw [e2]
  have hq0 : 0 ≤ q := by linarith
  have hn0 : 0 < n := by rw [← hq]; positivity
  -- b ≤ n / 2^22
  have hb1' : b ≤ n / 4194304 := by
    refine le_trans hb1 (div_le_div_of_nonneg_left hn0.le (by norm_num) ?_)
    nlinarith
  have hbA : b ≤ n * R ^ 2 / 72 := by
    by_cases h : 15840 * R ^ 2 ≤ 1
    · have h' := mul_nonneg (mul_nonneg hn0.le (sq_nonneg R)) (sub_nonneg.2 h)
      nlinarith
    · replace h := not_le.1 h
      have : n / 4194304 ≤ n * R ^ 2 / 72 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith
      linarith
  have hbB : b ≤ n * R / (8 * T) := by
    by_cases h : 1760 * T * R ^ 3 ≤ 1
    · rw [le_div_iff₀ (by positivity)]
      have h' := mul_nonneg (mul_nonneg hn0.le hR0.le) (sub_nonneg.2 h)
      have hb2' : b * (8 * T) ≤ 220 * n * R ^ 4 * (8 * T) :=
        mul_le_mul_of_nonneg_right hb2 (by positivity)
      nlinarith
    · replace h := not_le.1 h
      have hR3 : R ^ 3 ≤ R := by
        have : R ^ 2 ≤ 1 := by nlinarith
        nlinarith
      have h2 : 1 < 1760 * T * R := by nlinarith
      have : n / (T ^ 2 * 4194304) ≤ n * R / (8 * T) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : n * (8 * T) * 1 ≤ n * (8 * T) * (1760 * T * R) := by
          apply mul_le_mul_of_nonneg_left h2.le; positivity
        nlinarith
      linarith
  have hRq : 16 ≤ R ^ 2 * (36 * q) := by nlinarith
  have hnR2 : 4 * q ^ 3 ≤ 9 * (n * R ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hRq (pow_nonneg hq0 3)
    have h2 : q ^ 3 * (R ^ 2 * (36 * q)) = 36 * (q ^ 4 * R ^ 2) := by ring
    rw [← hq]
    linarith
  have hnR : n * R ^ 2 ≤ n * R := by
    have : R ^ 2 ≤ R := by nlinarith
    exact mul_le_mul_of_nonneg_left this hn0.le
  constructor
  · have hkey : 4 * q ≤ n * R / (8 * T) := by
      rw [le_div_iff₀ (by positivity)]
      have h1 : 4 * q * (8 * T) * 9 ≤ 4 * q ^ 3 := by
        have := mul_le_mul_of_nonneg_left hq2 (by positivity : (0:ℝ) ≤ 4 * q)
        have e : 4 * q * q ^ 2 = 4 * q ^ 3 := by ring
        linarith
      linarith
    have e4 : n * R / (4 * T) = 2 * (n * R / (8 * T)) := by field_simp; ring
    rw [e4]
    linarith
  · have hE12 : E1 * E2 ≤ q ^ 2 := by
      have := mul_le_mul hE1 hE2 hE20 hq0
      nlinarith
    have hq3 : 325 * q ^ 2 ≤ q ^ 3 := by
      have := mul_le_mul_of_nonneg_left hq325 (sq_nonneg q)
      nlinarith
    linarith

lemma two_dvd_two_pow_mul {a u : ℕ} (ha : 1 ≤ a) : 2 ∣ 2 ^ a * u :=
  dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) u

lemma prime_dvd_two_pow_mul {p a u : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 2 ^ a * u) :
    p ∣ u := by
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h1); omega
  · exact h1

/-- `(2^ω(k))^4 ≤ n` for `1 ≤ k ≤ n` and `n ≥ 2^2044`. -/
lemma two_pow_pf5_le_real {n k : ℕ} (hn : 2 ^ 2044 ≤ n) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((2 : ℝ) ^ (pf5 k).card) ^ 4 ≤ n := by
  have : (2 ^ (pf5 k).card) ^ 4 ≤ n := by
    by_cases h : 512 ≤ (pf5 k).card
    · exact le_trans (two_pow_card_pf5_le k (by omega) h) hkn
    · have h0 : (pf5 k).card * 4 ≤ 2044 := by omega
      have h1 : (2 ^ (pf5 k).card) ^ 4 ≤ 2 ^ 2044 := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) h0
      exact le_trans h1 hn
  exact_mod_cast this

/-- The threshold for the sparse case. -/
def N0 (l : ℕ) : ℕ := 2 ^ 2044 + (162 * l) ^ 2 + (9 * 2 ^ (l + 3)) ^ 2 + 325 ^ 4

lemma q_facts (l n : ℕ) (hn : N0 l ≤ n) : ∃ q : ℝ, 0 ≤ q ∧ q ^ 4 = n ∧ 325 ≤ q ∧
    162 * (l : ℝ) ≤ q ^ 2 ∧ 9 * 2 ^ (l + 3) ≤ q ^ 2 ∧ 2 ^ 2044 ≤ n ∧
    ∀ k, 1 ≤ k → k ≤ n → (2 : ℝ) ^ (pf5 k).card ≤ q := by
  unfold N0 at hn
  set q : ℝ := Real.sqrt (Real.sqrt n) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = Real.sqrt n := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hq4 : q ^ 4 = n := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq2, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hn2044 : 2 ^ 2044 ≤ n :=
    le_trans (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
      (Nat.le_add_right _ _))) hn
  have hnl : (162 * l) ^ 2 ≤ n :=
    le_trans (le_trans (Nat.le_add_left _ _) (le_trans (Nat.le_add_right _ _)
      (Nat.le_add_right _ _))) hn
  have hnl3 : (9 * 2 ^ (l + 3)) ^ 2 ≤ n :=
    le_trans (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)) hn
  have hn325 : 325 ^ 4 ≤ n := le_trans (Nat.le_add_left _ _) hn
  have hnl' : (162 * (l : ℝ)) ^ 2 ≤ n := by exact_mod_cast hnl
  have hnl3' : (9 * (2 : ℝ) ^ (l + 3)) ^ 2 ≤ n := by exact_mod_cast hnl3
  have hn325' : (325 : ℝ) ^ 4 ≤ n := by exact_mod_cast hn325
  refine ⟨q, hq0, hq4, ?_, ?_, ?_, hn2044, ?_⟩
  · by_contra h
    have h' : q ^ 4 < 325 ^ 4 := pow_lt_pow_left₀ (not_le.1 h) hq0 (by norm_num)
    rw [hq4] at h'
    linarith
  · by_contra h
    have h' : (q ^ 2) ^ 2 < (162 * (l : ℝ)) ^ 2 :=
      pow_lt_pow_left₀ (not_le.1 h) (sq_nonneg q) (by norm_num)
    have : (q ^ 2) ^ 2 = q ^ 4 := by ring
    rw [this, hq4] at h'
    linarith
  · by_contra h
    have h' : (q ^ 2) ^ 2 < (9 * (2 : ℝ) ^ (l + 3)) ^ 2 :=
      pow_lt_pow_left₀ (not_le.1 h) (sq_nonneg q) (by norm_num)
    have : (q ^ 2) ^ 2 = q ^ 4 := by ring
    rw [this, hq4] at h'
    linarith
  · intro k hk1 hkn
    have h := two_pow_pf5_le_real hn2044 hk1 hkn
    rw [← hq4] at h
    exact (pow_le_pow_iff_left₀ (by positivity) hq0 (by norm_num)).1 h

/-- A centre `x ∈ B` with `|B| ≤ 220 n ρ(x)^4`. -/
lemma exists_center (n : ℕ) (hn : 0 < n) (B : Finset ℕ) (hB : B ⊆ Icc 1 n) (hB1 : 1 ≤ B.card) :
    ∃ x ∈ B, (B.card : ℝ) ≤ 220 * n * rho x ^ 4 := by
  by_contra hcon
  push Not at hcon
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ x ∈ B, (rho x)⁻¹ ^ 4 ≤ 55 * n :=
    le_trans (sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => by positivity))
      (sum_rho_inv_pow_le n)
  have hne : B.Nonempty := card_pos.1 (by omega)
  have hb0 : (0 : ℝ) < B.card := by exact_mod_cast (by omega : 0 < B.card)
  have : (B.card : ℝ) < B.card / 4 := by
    calc (B.card : ℝ) = ∑ x ∈ B, (1 : ℝ) := by simp
      _ < ∑ x ∈ B, (B.card / (220 * n)) * (rho x)⁻¹ ^ 4 := by
        refine sum_lt_sum_of_nonempty hne fun x hx => ?_
        have hρ := rho_pos x
        have e : (B.card / (220 * n)) * (rho x)⁻¹ ^ 4 = B.card / (220 * n * rho x ^ 4) := by
          field_simp
        rw [e, one_lt_div (by positivity)]
        exact hcon x hx
      _ = (B.card / (220 * n)) * ∑ x ∈ B, (rho x)⁻¹ ^ 4 := by rw [mul_sum]
      _ ≤ (B.card / (220 * n)) * (55 * n) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = B.card / 4 := by field_simp; ring
  linarith

lemma rho_E (x : ℕ) : 16 ≤ rho x ^ 2 * (36 * (2 : ℝ) ^ (pf5 x).card) := by
  have h1 := rho_ge x
  have h2 := sq_add_four_le (pf5 x).card
  have hR := rho_pos x
  have h3 : (4 : ℝ) ≤ rho x * (((pf5 x).card : ℝ) + 4) := by
    rw [div_le_iff₀ (by positivity)] at h1; linarith
  nlinarith [sq_nonneg (rho x * (((pf5 x).card : ℝ) + 4))]

/-- The candidate chain indices `u ≤ N`, `u` coprime to `6` and to all `p ∈ W`. -/
def Vset (N : ℕ) (W : Finset ℕ) : Finset ℕ :=
  ((Icc 1 N).filter (fun k => k % 6 = 1 ∧ ∀ p ∈ W, ¬ p ∣ k)) ∪
    ((Icc 1 N).filter (fun k => k % 6 = 5 ∧ ∀ p ∈ W, ¬ p ∣ k))

lemma mem_Vset {N : ℕ} {W : Finset ℕ} {u : ℕ} :
    u ∈ Vset N W ↔ (1 ≤ u ∧ u ≤ N) ∧ (u % 6 = 1 ∨ u % 6 = 5) ∧ ∀ p ∈ W, ¬ p ∣ u := by
  simp only [Vset, mem_union, mem_filter, mem_Icc]
  tauto

lemma Vset_card_ge (N : ℕ) (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime ∧ 5 ≤ p) :
    N * rhoS W / 3 - 4 * (2 : ℝ) ^ W.card + 2 ≤ (Vset N W).card := by
  have hVcard : ((Vset N W).card : ℝ) = cnt N 1 W + cnt N 5 W := by
    rw [Vset, card_union_of_disjoint]
    · push_cast; rfl
    · exact disjoint_filter.2 fun k _ h1 h2 => by omega
  have hsv1 := sieve W hW N 1 (by norm_num)
  have hsv5 := sieve W hW N 5 (by norm_num)
  have hpow : (2 : ℝ) ^ (W.card + 1) = 2 * 2 ^ W.card := by ring
  rw [hpow, abs_le] at hsv1 hsv5
  rw [hVcard]
  linarith [hsv1.1, hsv5.1]

lemma bad_card_le (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N) (R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ((S.filter (fun u => rho u < R / 6)).card : ℝ) ≤ N * R / 12 := by
  set Vbad := S.filter (fun u => rho u < R / 6)
  have hs : ∑ u ∈ Vbad, (rho u)⁻¹ ^ 4 ≤ 55 * N :=
    le_trans (sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans hS)
      (fun _ _ _ => by positivity)) (sum_rho_inv_pow_le N)
  calc (Vbad.card : ℝ) = ∑ u ∈ Vbad, (1 : ℝ) := by simp
    _ ≤ ∑ u ∈ Vbad, (R / 6) ^ 4 * (rho u)⁻¹ ^ 4 := by
      refine sum_le_sum fun u hu => ?_
      have hu' := (mem_filter.1 hu).2
      have hρ := rho_pos u
      have e : (R / 6) ^ 4 * (rho u)⁻¹ ^ 4 = ((R / 6) / rho u) ^ 4 := by
        field_simp
      rw [e]
      exact one_le_pow₀ ((one_le_div hρ).2 hu'.le)
    _ = (R / 6) ^ 4 * ∑ u ∈ Vbad, (rho u)⁻¹ ^ 4 := by rw [mul_sum]
    _ ≤ (R / 6) ^ 4 * (55 * N) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ N * R / 12 := by
      have hR3 : R ^ 3 ≤ 1 := pow_le_one₀ hR0.le hR1
      have : (R / 6) ^ 4 * (55 * N) = N * R * (55 * R ^ 3 / 1296) := by ring
      rw [this]
      have h2 : 55 * R ^ 3 / 1296 ≤ 1 / 12 := by linarith
      have : N * R * (55 * R ^ 3 / 1296) ≤ N * R * (1 / 12) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith

/-- Dead chains inject into the missing multiples of `2` or `3`. -/
lemma dead_card_le (l n : ℕ) (A W : Finset ℕ) :
    ((Vset (n / 2 ^ l) W).filter (fun u => ¬ ∀ a ∈ Icc 1 l, 2 ^ a * u ∈ A)).card ≤
      ((Sset n).filter (· ∉ A)).card := by
  classical
  set Dead := (Vset (n / 2 ^ l) W).filter (fun u => ¬ ∀ a ∈ Icc 1 l, 2 ^ a * u ∈ A)
  let g : ℕ → ℕ := fun u =>
    if h : ∃ a ∈ Icc 1 l, 2 ^ a * u ∉ A then 2 ^ (Classical.choose h) * u else 0
  have hex_of : ∀ u ∈ Dead, ∃ a ∈ Icc 1 l, 2 ^ a * u ∉ A := by
    intro u hu
    have := (mem_filter.1 hu).2; push Not at this; exact this
  have hodd : ∀ v ∈ Dead, v % 2 = 1 := by
    intro v hv
    have := (mem_Vset.1 (mem_filter.1 hv).1).2.1
    omega
  refine card_le_card_of_injOn g (fun u hu => ?_) (fun u hu u' hu' hgu => ?_)
  · have hex := hex_of u hu
    have hspec := Classical.choose_spec hex
    have hg : g u = 2 ^ (Classical.choose hex) * u := dif_pos hex
    have hu1 := (mem_Vset.1 (mem_filter.1 hu).1).1
    simp only [coe_filter, Set.mem_ofPred_eq, Sset, mem_filter, mem_Icc]
    rw [hg]
    obtain ⟨ha, hnotA⟩ := hspec
    have ha' := mem_Icc.1 ha
    refine ⟨⟨⟨?_, ?_⟩, Or.inl ?_⟩, hnotA⟩
    · have : 1 ≤ 2 ^ Classical.choose hex := Nat.one_le_two_pow
      nlinarith
    · have h1 : 2 ^ Classical.choose hex ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) ha'.2
      have h2 : u * 2 ^ l ≤ n := (Nat.le_div_iff_mul_le (by positivity)).1 hu1.2
      calc 2 ^ Classical.choose hex * u ≤ 2 ^ l * u := Nat.mul_le_mul_right u h1
        _ = u * 2 ^ l := mul_comm _ _
        _ ≤ n := h2
    · exact Nat.mod_eq_zero_of_dvd (two_dvd_two_pow_mul ha'.1)
  · have hex := hex_of u hu
    have hex' := hex_of u' hu'
    have hg1 : g u = 2 ^ (Classical.choose hex) * u := dif_pos hex
    have hg2 : g u' = 2 ^ (Classical.choose hex') * u' := dif_pos hex'
    exact odd_part_inj (hodd u hu) (hodd u' hu') (hg1 ▸ hg2 ▸ hgu)

/-- An alive chain whose index `u` has `ρ(u) ≥ ρ(x)/6`. -/
lemma exists_chain (l n : ℕ) (A W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime ∧ 5 ≤ p) (R b : ℝ)
    (hR0 : 0 < R) (hR1 : R ≤ 1) (hRW : R = rhoS W)
    (hdead : ((Sset n).filter (· ∉ A)).card + 1 ≤ b)
    (hnum : 0 < n * R / 2 ^ (l + 2) - 1 / 4 - 4 * (2 : ℝ) ^ W.card - b + 1) :
    ∃ u, u ∈ Vset (n / 2 ^ l) W ∧ R / 6 ≤ rho u ∧ ∀ a ∈ Icc 1 l, 2 ^ a * u ∈ A := by
  set N1 := n / 2 ^ l with hN1
  have hN1real : (n : ℝ) / 2 ^ l - 1 ≤ N1 := by
    have e := Nat.div_add_mod n (2 ^ l)
    have hm : n % 2 ^ l < 2 ^ l := Nat.mod_lt _ (by positivity)
    have e' : (n : ℝ) = 2 ^ l * (N1 : ℝ) + ((n % 2 ^ l : ℕ) : ℝ) := by exact_mod_cast e.symm
    have hm' : ((n % 2 ^ l : ℕ) : ℝ) < 2 ^ l := by exact_mod_cast hm
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity), e']
    nlinarith
  set V := Vset N1 W
  have hVsub : V ⊆ Icc 1 N1 := fun k hk => mem_Icc.2 (mem_Vset.1 hk).1
  have hVlow := Vset_card_ge N1 W hW
  rw [← hRW] at hVlow
  have hVbad := bad_card_le N1 V hVsub R hR0 hR1
  have hDead := dead_card_le l n A W
  set Vbad := V.filter (fun u => rho u < R / 6)
  set Dead := V.filter (fun u => ¬ ∀ a ∈ Icc 1 l, 2 ^ a * u ∈ A)
  have hlt : (Vbad ∪ Dead).card < V.card := by
    have h1 := card_union_le Vbad Dead
    have h2 : ((Vbad ∪ Dead).card : ℝ) ≤ Vbad.card + Dead.card := by exact_mod_cast h1
    have h3 : (Dead.card : ℝ) + 1 ≤ b := by
      have : (Dead.card : ℝ) ≤ ((Sset n).filter (· ∉ A)).card := by exact_mod_cast hDead
      linarith
    have h5 : ((n : ℝ) / 2 ^ l - 1) * R ≤ N1 * R := mul_le_mul_of_nonneg_right hN1real hR0.le
    rw [sub_mul, one_mul] at h5
    have h6 : (n : ℝ) * R / 2 ^ (l + 2) = (n / 2 ^ l) * R / 4 := by rw [pow_add]; ring
    rw [h6] at hnum
    have h7 : ((Vbad ∪ Dead).card : ℝ) < V.card := by linarith
    exact_mod_cast h7
  obtain ⟨u, huV, hunot⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨u, huV, ?_, ?_⟩
  · by_contra h
    exact hunot (mem_union_left _ (mem_filter.2 ⟨huV, not_le.1 h⟩))
  · by_contra h
    exact hunot (mem_union_right _ (mem_filter.2 ⟨huV, h⟩))

/-- The candidates for the third class. -/
def Zset (n : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun k => k % 6 = 3 ∧ ∀ p ∈ W, ¬ p ∣ k)

lemma Zset_card_ge (n : ℕ) (x u : ℕ) (hu : rho x / 6 ≤ rho u) :
    (n : ℝ) * rho x ^ 2 / 36 - 2 * ((2 : ℝ) ^ (pf5 x).card * 2 ^ (pf5 u).card) + 1 ≤
      (Zset n (pf5 x ∪ pf5 u)).card := by
  set W' := pf5 x ∪ pf5 u
  have hW'p : ∀ p ∈ W', p.Prime ∧ 5 ≤ p := by
    intro p hp
    rcases mem_union.1 hp with h | h
    · exact ⟨(mem_pf5.1 h).1, (mem_pf5.1 h).2.2.2⟩
    · exact ⟨(mem_pf5.1 h).1, (mem_pf5.1 h).2.2.2⟩
  have hsvZ := sieve W' hW'p n 3 (by norm_num)
  have hR0 := rho_pos x
  have hrhoW' : rho x * (rho x / 6) ≤ rhoS W' := by
    have h1 : rho x * rho u ≤ rhoS W' := rhoS_union_ge (pf5 x) (pf5 u)
      (fun p hp => by have := (mem_pf5.1 hp).2.2.2; omega)
      (fun p hp => by have := (mem_pf5.1 hp).2.2.2; omega)
    have h2 : rho x * (rho x / 6) ≤ rho x * rho u := mul_le_mul_of_nonneg_left hu hR0.le
    linarith
  have hcardW' : (2 : ℝ) ^ (W'.card + 1) ≤ 2 * (2 ^ (pf5 x).card * 2 ^ (pf5 u).card) := by
    have h := card_union_le (pf5 x) (pf5 u)
    rw [← pow_add, pow_succ]
    have : (2 : ℝ) ^ W'.card ≤ 2 ^ ((pf5 x).card + (pf5 u).card) :=
      pow_le_pow_right₀ (by norm_num) h
    linarith
  have hZcnt : (Zset n W').card = cnt n 3 W' := rfl
  rw [← hZcnt, abs_le] at hsvZ
  have h1 := hsvZ.1
  have h2 : (n : ℝ) / 6 * (rho x * (rho x / 6)) ≤ n / 6 * rhoS W' :=
    mul_le_mul_of_nonneg_left hrhoW' (by positivity)
  have e : (n : ℝ) / 6 * (rho x * (rho x / 6)) = n * rho x ^ 2 / 36 := by ring
  rw [e] at h2
  linarith

/-- Assembling the configuration from the centre, the chain and the third class. -/
lemma good_of_parts (l : ℕ) (A : Finset ℕ) (x u : ℕ) (hxA : x ∈ A) (hx1 : 1 ≤ x)
    (hx6 : x % 6 = 1 ∨ x % 6 = 5) (hu1 : 1 ≤ u) (hu6 : u % 6 = 1 ∨ u % 6 = 5)
    (huW : ∀ p ∈ pf5 x, ¬ p ∣ u) (hualive : ∀ a ∈ Icc 1 l, 2 ^ a * u ∈ A) (n : ℕ)
    (hZ : l ≤ ((Zset n (pf5 x ∪ pf5 u)).filter (· ∈ A)).card) : Good A l := by
  obtain ⟨Z, hZsub, hZcard⟩ := exists_subset_card_eq hZ
  set Y := (Icc 1 l).image (fun a => 2 ^ a * u) with hY
  have hYcard : Y.card = l := by
    rw [hY, card_image_of_injective]
    · simp
    · intro a a' h
      simp only at h
      exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right hu1 h)
  have hZmem : ∀ z ∈ Z, z ∈ A ∧ z % 6 = 3 ∧ ∀ p ∈ pf5 x ∪ pf5 u, ¬ p ∣ z := by
    intro z hz
    have := hZsub hz
    simp only [mem_filter, Zset] at this
    exact ⟨this.2, this.1.2.1, this.1.2.2⟩
  have hYmem : ∀ y ∈ Y, ∃ a ∈ Icc 1 l, y = 2 ^ a * u := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
    exact ⟨a, ha, rfl⟩
  refine ⟨x, hxA, Y, Z, ?_, fun z hz => (hZmem z hz).1, hYcard, hZcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hYmem y hy
    exact hualive a ha
  · intro hx
    obtain ⟨a, ha, hxa⟩ := hYmem x hx
    have := two_dvd_two_pow_mul (u := u) (mem_Icc.1 ha).1
    rw [← hxa] at this
    omega
  · intro hx
    have := (hZmem x hx).2.1
    omega
  · rw [disjoint_left]
    intro y hy hyZ
    obtain ⟨a, ha, rfl⟩ := hYmem y hy
    have h1 := two_dvd_two_pow_mul (u := u) (mem_Icc.1 ha).1
    have h2 := (hZmem _ hyZ).2.1
    omega
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hYmem y hy
    refine coprime_of_no_common ?_ ?_ ?_
    · rintro ⟨h1, _⟩; omega
    · rintro ⟨h1, _⟩; omega
    · intro p hp hp5 hpx hpy
      have hpW : p ∈ pf5 x := mem_pf5.2 ⟨hp, hpx, by omega, hp5⟩
      exact huW p hpW (prime_dvd_two_pow_mul hp hp5 hpy)
  · intro z hz
    have hz' := hZmem z hz
    refine coprime_of_no_common ?_ ?_ ?_
    · rintro ⟨h1, _⟩; omega
    · rintro ⟨h1, _⟩; omega
    · intro p hp hp5 hpx hpz
      exact hz'.2.2 p (mem_union_left _ (mem_pf5.2 ⟨hp, hpx, by omega, hp5⟩)) hpz
  · intro y hy z hz
    obtain ⟨a, ha, rfl⟩ := hYmem y hy
    have hz' := hZmem z hz
    refine coprime_of_no_common ?_ ?_ ?_
    · rintro ⟨_, h2⟩; omega
    · rintro ⟨h1, _⟩
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h | h
      · have h3 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · omega
    · intro p hp hp5 hpy hpz
      have hpu := prime_dvd_two_pow_mul hp hp5 hpy
      exact hz'.2.2 p (mem_union_right _ (mem_pf5.2 ⟨hp, hpu, by omega, hp5⟩)) hpz

/-- **Sparse case.** If `|B| ≤ n / 2^(2l+22)`, the configuration exists for `n ≥ N0 l`. -/
theorem case_i (l : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 n →
    n / 2 + n / 3 - n / 6 < A.card →
    ((Bset A).card : ℝ) ≤ (n : ℝ) / 2 ^ (2 * l + 22) → Good A l := by
  filter_upwards [eventually_ge_atTop (N0 l)] with n hn A hA hcard hb
  obtain ⟨q, hq0, hq4, hq325, hql, hq2', hn2044, hE⟩ := q_facts l n hn
  have hsetup := setup hA hcard
  have hB1 : 1 ≤ (Bset A).card := by
    have := hsetup ∅ (empty_subset _); simpa using this
  have hBsub : Bset A ⊆ Icc 1 n := fun k hk => hA (mem_filter.1 hk).1
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn2044
  obtain ⟨x, hxB, hxb⟩ := exists_center n hn0 (Bset A) hBsub hB1
  have hxA : x ∈ A := (mem_filter.1 hxB).1
  have hx6 : x % 6 = 1 ∨ x % 6 = 5 := (mem_filter.1 hxB).2
  have hx1n := mem_Icc.1 (hA hxA)
  have hW : ∀ p ∈ pf5 x, p.Prime ∧ 5 ≤ p :=
    fun p hp => ⟨(mem_pf5.1 hp).1, (mem_pf5.1 hp).2.2.2⟩
  have hE1 := hE x hx1n.1 hx1n.2
  have hC := numeric_i l n q (rho x) ((Bset A).card) (2 ^ (pf5 x).card) (2 ^ (pf5 x).card) hq4
    hq325 hql hq2' (rho_pos x) (rho_le_one x) hb hxb hE1 hE1 (by positivity)
    (rho_E x)
  have hdead : (((Sset n).filter (· ∉ A)).card : ℝ) + 1 ≤ (Bset A).card := by
    have hS := hsetup (Sset n) subset_rfl
    have hsplit := card_filter_add_card_filter_not (s := Sset n) (· ∈ A)
    have : ((Sset n).filter (· ∉ A)).card + 1 ≤ (Bset A).card := by omega
    exact_mod_cast this
  obtain ⟨u, huV, hurho, hualive⟩ := exists_chain l n A (pf5 x) hW (rho x) ((Bset A).card)
    (rho_pos x) (rho_le_one x) rfl hdead hC.1
  have hu := mem_Vset.1 huV
  have hun : u ≤ n := le_trans hu.1.2 (Nat.div_le_self _ _)
  have hE2 := hE u hu.1.1 hun
  have hC2 := (numeric_i l n q (rho x) ((Bset A).card) (2 ^ (pf5 x).card) (2 ^ (pf5 u).card) hq4
    hq325 hql hq2' (rho_pos x) (rho_le_one x) hb hxb hE1 hE2 (by positivity)
    (rho_E x)).2
  have hZs := Zset_card_ge n x u hurho
  have hZsS : Zset n (pf5 x ∪ pf5 u) ⊆ Sset n := by
    intro k hk
    simp only [Zset, mem_filter] at hk
    simp only [Sset, mem_filter]
    exact ⟨hk.1, Or.inr (by omega)⟩
  have hZA := hsetup _ hZsS
  have hZAl : l ≤ ((Zset n (pf5 x ∪ pf5 u)).filter (· ∈ A)).card := by
    have h1 : (((Zset n (pf5 x ∪ pf5 u)).card + 1 : ℕ) : ℝ) ≤
        (((Zset n (pf5 x ∪ pf5 u)).filter (· ∈ A)).card + (Bset A).card : ℕ) := by
      exact_mod_cast hZA
    push_cast at h1
    have : (l : ℝ) < ((Zset n (pf5 x ∪ pf5 u)).filter (· ∈ A)).card := by linarith
    exact_mod_cast this.le
  exact good_of_parts l A x u hxA hx1n.1 hx6 hu.1.1 hu.2.1 hu.2.2 hualive n hZAl

/-- A residue class `{k ∈ [1, n] : (k + e) mod P = τ}`. -/
def cls (n P e τ : ℕ) : Finset ℕ := (Icc 1 n).filter (fun k => (k + e) % P = τ)

lemma modEq_of_mem_cls {n P e τ k k' : ℕ} (hk : k ∈ cls n P e τ) (hk' : k' ∈ cls n P e τ) :
    k % P = k' % P := by
  simp only [cls, mem_filter] at hk hk'
  have h : Nat.ModEq P (k + e) (k' + e) := by
    unfold Nat.ModEq; rw [hk.2, hk'.2]
  exact Nat.ModEq.add_right_cancel' e h

lemma card_cls_le (n P e τ : ℕ) : (cls n P e τ).card ≤ n / P + 1 :=
  card_le_of_modEq (fun _ hk => (mem_Icc.1 (mem_filter.1 hk).1).2)
    (fun _ hk _ hk' => modEq_of_mem_cls hk hk')

lemma card_cls_dvd_le (n P e τ d : ℕ) (hdP : Nat.Coprime d P) :
    ((cls n P e τ).filter (d ∣ ·)).card ≤ n / (d * P) + 1 := by
  set S := (cls n P e τ).filter (d ∣ ·)
  have hinj : Set.InjOn (fun k => k / d) S := by
    intro k hk k' hk' h
    simp only [S, coe_filter, Set.mem_ofPred_eq] at hk hk'
    simp only at h
    rw [← Nat.mul_div_cancel' hk.2, ← Nat.mul_div_cancel' hk'.2, h]
  rw [← card_image_of_injOn hinj]
  rw [← Nat.div_div_eq_div_mul]
  refine card_le_of_modEq (fun k hk => ?_) (fun k hk k' hk' => ?_)
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 hk
    have := (mem_Icc.1 (mem_filter.1 (mem_filter.1 hj).1).1).2
    exact Nat.div_le_div_right this
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 hk
    obtain ⟨j', hj', rfl⟩ := mem_image.1 hk'
    have h1 := modEq_of_mem_cls (mem_filter.1 hj).1 (mem_filter.1 hj').1
    have hd1 := (mem_filter.1 hj).2
    have hd2 := (mem_filter.1 hj').2
    have h2 : Nat.ModEq P (d * (j / d)) (d * (j' / d)) := by
      rw [Nat.mul_div_cancel' hd1, Nat.mul_div_cancel' hd2]; exact h1
    exact Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hdP) h2

lemma coprime_of_prime_gt {p r : ℕ} (hp : p.Prime) (hpr : r < p) : Nat.Coprime p r.factorial :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
    have := (Nat.Prime.dvd_factorial hp).1 h; omega

/-- The weighted count of non-coprime pairs between two classes that share no prime `≤ r`. -/
lemma bad_pairs_le (n r e τ1 τ2 : ℕ) (hr : 1 ≤ r) (S1 S2 : Finset ℕ)
    (h1 : S1 ⊆ cls n r.factorial e τ1) (h2 : S2 ⊆ cls n r.factorial e τ2)
    (hsmall : ∀ k1 ∈ S1, ∀ k2 ∈ S2, ∀ p, p.Prime → p ≤ r → p ∣ k1 → p ∣ k2 → False) :
    (∑ x ∈ S1, ((S2.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ)) ≤
      2 * ((n : ℝ) / r.factorial) ^ 2 / r + 2 * n := by
  set P := r.factorial with hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast Nat.factorial_pos r
  set Pr := (Ioc r n).filter Nat.Prime with hPr
  -- union bound over the primes dividing `x`
  have step1 : ∀ x ∈ S1, ((S2.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ) ≤
      ∑ p ∈ Pr.filter (· ∣ x), ((S2.filter (p ∣ ·)).card : ℝ) := by
    intro x hx
    have hsub : S2.filter (fun y => ¬ Nat.Coprime x y) ⊆
        (Pr.filter (· ∣ x)).biUnion (fun p => S2.filter (p ∣ ·)) := by
      intro y hy
      obtain ⟨hyS, hyc⟩ := mem_filter.1 hy
      obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.1 hyc
      have hxn := (mem_Icc.1 (mem_filter.1 (h1 hx)).1)
      refine mem_biUnion.2 ⟨p, ?_, mem_filter.2 ⟨hyS, hpy⟩⟩
      refine mem_filter.2 ⟨mem_filter.2 ⟨mem_Ioc.2 ⟨?_, ?_⟩, hp⟩, hpx⟩
      · by_contra hle
        exact hsmall x hx y hyS p hp (not_lt.1 hle) hpx hpy
      · exact le_trans (Nat.le_of_dvd (by omega) hpx) hxn.2
    have := le_trans (card_le_card hsub) card_biUnion_le
    exact_mod_cast this
  have step2 : ∑ x ∈ S1, ∑ p ∈ Pr.filter (· ∣ x), ((S2.filter (p ∣ ·)).card : ℝ) =
      ∑ p ∈ Pr, ∑ x ∈ S1.filter (p ∣ ·), ((S2.filter (p ∣ ·)).card : ℝ) := by
    refine sum_comm' fun x p => ?_
    simp only [mem_filter]
    tauto
  have step3 : ∀ p ∈ Pr, ∑ x ∈ S1.filter (p ∣ ·), ((S2.filter (p ∣ ·)).card : ℝ) ≤
      2 * ((n : ℝ) / P) ^ 2 / (p : ℝ) ^ 2 + 2 := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.1 hp
    have hrp := (mem_Ioc.1 hpI).1
    have hcop := coprime_of_prime_gt hpp hrp
    rw [sum_const, nsmul_eq_mul]
    have hb1 : (S1.filter (p ∣ ·)).card ≤ n / (p * P) + 1 :=
      le_trans (card_le_card (filter_subset_filter _ h1)) (card_cls_dvd_le n P e τ1 p hcop)
    have hb2 : (S2.filter (p ∣ ·)).card ≤ n / (p * P) + 1 :=
      le_trans (card_le_card (filter_subset_filter _ h2)) (card_cls_dvd_le n P e τ2 p hcop)
    have hreal : ((n / (p * P) + 1 : ℕ) : ℝ) ≤ (n : ℝ) / P / p + 1 := by
      push_cast
      have : ((n / (p * P) : ℕ) : ℝ) ≤ (n : ℝ) / ((p * P : ℕ) : ℝ) := Nat.cast_div_le
      push_cast at this
      rw [div_div, mul_comm (P : ℝ)]
      linarith
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hb1' : ((S1.filter (p ∣ ·)).card : ℝ) ≤ (n : ℝ) / P / p + 1 :=
      le_trans (by exact_mod_cast hb1) hreal
    have hb2' : ((S2.filter (p ∣ ·)).card : ℝ) ≤ (n : ℝ) / P / p + 1 :=
      le_trans (by exact_mod_cast hb2) hreal
    have hnn : (0 : ℝ) ≤ (n : ℝ) / P / p := by positivity
    calc ((S1.filter (p ∣ ·)).card : ℝ) * ((S2.filter (p ∣ ·)).card : ℝ)
        ≤ ((n : ℝ) / P / p + 1) * ((n : ℝ) / P / p + 1) :=
          mul_le_mul hb1' hb2' (by positivity) (by positivity)
      _ ≤ 2 * ((n : ℝ) / P / p) ^ 2 + 2 := by nlinarith [sq_nonneg ((n : ℝ) / P / p - 1)]
      _ = 2 * ((n : ℝ) / P) ^ 2 / (p : ℝ) ^ 2 + 2 := by field_simp
  have step4 : ∑ p ∈ Pr, (2 * ((n : ℝ) / P) ^ 2 / (p : ℝ) ^ 2 + 2) ≤
      ∑ d ∈ Ioc r n, (2 * ((n : ℝ) / P) ^ 2 / (d : ℝ) ^ 2 + 2) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have step5 : ∑ d ∈ Ioc r n, (2 * ((n : ℝ) / P) ^ 2 / (d : ℝ) ^ 2 + 2) ≤
      2 * ((n : ℝ) / P) ^ 2 / r + 2 * n := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    have h1 : ∑ d ∈ Ioc r n, 2 * ((n : ℝ) / P) ^ 2 / (d : ℝ) ^ 2 =
        2 * ((n : ℝ) / P) ^ 2 * ∑ d ∈ Ioc r n, 1 / (d : ℝ) ^ 2 := by
      rw [mul_sum]; refine sum_congr rfl fun d _ => by ring
    have h2 := sum_Ioc_inv_sq_le' r hr n
    have h3 : ((Ioc r n).card : ℝ) ≤ n := by
      have : (Ioc r n).card ≤ n := by simp
      exact_mod_cast this
    rw [h1]
    have h4 : 2 * ((n : ℝ) / P) ^ 2 * ∑ d ∈ Ioc r n, 1 / (d : ℝ) ^ 2 ≤
        2 * ((n : ℝ) / P) ^ 2 * (1 / r) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : 2 * ((n : ℝ) / P) ^ 2 * (1 / (r : ℝ)) = 2 * ((n : ℝ) / P) ^ 2 / r := by ring
    linarith
  calc (∑ x ∈ S1, ((S2.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ))
      ≤ ∑ x ∈ S1, ∑ p ∈ Pr.filter (· ∣ x), ((S2.filter (p ∣ ·)).card : ℝ) := sum_le_sum step1
    _ = _ := step2
    _ ≤ ∑ p ∈ Pr, (2 * ((n : ℝ) / P) ^ 2 / (p : ℝ) ^ 2 + 2) := sum_le_sum step3
    _ ≤ _ := step4
    _ ≤ _ := step5

/-- Greedy extraction of `K_{l,l}` from a bipartite relation with few missing pairs. -/
lemma greedy (l : ℕ) (hl : 1 ≤ l) (Y0 Z0 : Finset ℕ) (rel : ℕ → ℕ → Prop) [DecidableRel rel]
    (hY : 2 * l ≤ Y0.card) (hZ : 2 * l ≤ Z0.card)
    (hbad : 4 * l * ∑ y ∈ Y0, (Z0.filter (fun z => ¬ rel y z)).card ≤ Y0.card * Z0.card) :
    ∃ Y ⊆ Y0, ∃ Z ⊆ Z0, Y.card = l ∧ Z.card = l ∧ ∀ y ∈ Y, ∀ z ∈ Z, rel y z := by
  set deg := fun y => (Z0.filter (fun z => ¬ rel y z)).card with hdeg
  set G := Y0.filter (fun y => 2 * l * deg y ≤ Z0.card) with hG
  have hZpos : 0 < Z0.card := by omega
  have hbadG : (Y0.filter (fun y => ¬ (2 * l * deg y ≤ Z0.card))).card * Z0.card ≤
      2 * l * ∑ y ∈ Y0, deg y := by
    calc (Y0.filter (fun y => ¬ (2 * l * deg y ≤ Z0.card))).card * Z0.card
        = ∑ y ∈ Y0.filter (fun y => ¬ (2 * l * deg y ≤ Z0.card)), Z0.card := by
          rw [sum_const, smul_eq_mul]
      _ ≤ ∑ y ∈ Y0.filter (fun y => ¬ (2 * l * deg y ≤ Z0.card)), 2 * l * deg y :=
          sum_le_sum fun y hy => le_of_lt (not_le.1 (mem_filter.1 hy).2)
      _ ≤ ∑ y ∈ Y0, 2 * l * deg y :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      _ = 2 * l * ∑ y ∈ Y0, deg y := by rw [mul_sum]
  have hsplit := card_filter_add_card_filter_not (s := Y0) (fun y => 2 * l * deg y ≤ Z0.card)
  have hGcard : l ≤ G.card := by
    have h1 : 2 * (Y0.filter (fun y => ¬ (2 * l * deg y ≤ Z0.card))).card * Z0.card ≤
        Y0.card * Z0.card := by
      have := Nat.mul_le_mul_left 2 hbadG
      calc 2 * (Y0.filter (fun y => ¬ (2 * l * deg y ≤ Z0.card))).card * Z0.card
          = 2 * ((Y0.filter (fun y => ¬ (2 * l * deg y ≤ Z0.card))).card * Z0.card) := by ring
        _ ≤ 2 * (2 * l * ∑ y ∈ Y0, deg y) := this
        _ = 4 * l * ∑ y ∈ Y0, deg y := by ring
        _ ≤ _ := hbad
    have h2 : 2 * (Y0.filter (fun y => ¬ (2 * l * deg y ≤ Z0.card))).card ≤ Y0.card :=
      Nat.le_of_mul_le_mul_right h1 hZpos
    rw [hG]
    omega
  obtain ⟨Y, hYG, hYcard⟩ := exists_subset_card_eq hGcard
  set N := Y.biUnion (fun y => Z0.filter (fun z => ¬ rel y z)) with hN
  have hNcard : 2 * N.card ≤ Z0.card := by
    have h1 : N.card ≤ ∑ y ∈ Y, deg y := card_biUnion_le
    have h2 : ∑ y ∈ Y, 2 * l * deg y ≤ ∑ y ∈ Y, Z0.card :=
      sum_le_sum fun y hy => (mem_filter.1 (hYG hy)).2
    rw [sum_const, smul_eq_mul, hYcard, ← mul_sum] at h2
    have h3 : 2 * l * N.card ≤ l * Z0.card := by
      calc 2 * l * N.card ≤ 2 * l * ∑ y ∈ Y, deg y := Nat.mul_le_mul_left _ h1
        _ ≤ l * Z0.card := h2
    have h4 : l * (2 * N.card) ≤ l * Z0.card := by
      calc l * (2 * N.card) = 2 * l * N.card := by ring
        _ ≤ _ := h3
    exact Nat.le_of_mul_le_mul_left h4 (by omega)
  have hZN : l ≤ (Z0 \ N).card := by
    have : N.card ≤ Z0.card := by omega
    have h := card_sdiff_add_card_inter Z0 N
    have h' : (Z0 ∩ N).card ≤ N.card := card_le_card inter_subset_right
    omega
  obtain ⟨Z, hZsub, hZcard⟩ := exists_subset_card_eq hZN
  refine ⟨Y, fun y hy => (mem_filter.1 (hYG hy)).1, Z, fun z hz => (mem_sdiff.1 (hZsub hz)).1,
    hYcard, hZcard, fun y hy z hz => ?_⟩
  by_contra h
  have hz := mem_sdiff.1 (hZsub hz)
  exact hz.2 (mem_biUnion.2 ⟨y, hy, mem_filter.2 ⟨hz.1, h⟩⟩)

lemma sum_range_six_mul (f : ℕ → ℕ) (m : ℕ) :
    ∑ τ ∈ range (6 * m), f τ = ∑ i ∈ range m, ∑ u ∈ range 6, f (6 * i + u) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 6 * (m + 1) = 6 * m + 6 by ring, sum_range_add, ih,
      sum_range_succ (fun i => ∑ u ∈ range 6, f (6 * i + u)) m]

/-- The sum over all blocks of the seven class counts is `|A| + |A ∩ (c mod 6)|`. -/
lemma block_total (A : Finset ℕ) (P e c : ℕ) (hP6 : 6 ∣ P) (hP0 : 0 < P) (hec : (e + c) % 6 = 0)
    (hc : c < 6) :
    ∑ i ∈ range (P / 6), ∑ u ∈ range 7, (A.filter (fun k => (k + e) % P = (6 * i + u) % P)).card
      = A.card + (A.filter (fun k => k % 6 = c)).card := by
  set f : ℕ → ℕ := fun τ => (A.filter (fun k => (k + e) % P = τ)).card with hf
  set m := P / 6 with hm
  have hPm : P = 6 * m := by rw [hm]; exact (Nat.mul_div_cancel' hP6).symm
  have hsplit : ∀ i ∈ range m, ∑ u ∈ range 7, f ((6 * i + u) % P) =
      ∑ u ∈ range 6, f (6 * i + u) + f ((6 * i + 6) % P) := by
    intro i hi
    rw [sum_range_succ]
    congr 1
    refine sum_congr rfl fun u hu => ?_
    have hi' := mem_range.1 hi
    have hu' := mem_range.1 hu
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [sum_congr rfl hsplit, sum_add_distrib]
  congr 1
  · -- the first six classes of each block partition `A`
    rw [← sum_range_six_mul f m, ← hPm]
    exact (card_eq_sum_card_fiberwise (f := fun k => (k + e) % P) (t := range P)
      (fun k _ => by simp only [coe_range, Set.mem_Iio]; exact Nat.mod_lt _ hP0)).symm
  · -- the seventh classes are the residues `≡ 0 (mod 6)`, i.e. `k ≡ c (mod 6)`
    set g : ℕ → ℕ := fun i => f ((6 * i) % P) with hg
    have hshift : ∑ i ∈ range m, f ((6 * i + 6) % P) = ∑ i ∈ range m, g i := by
      have h1 := sum_range_succ' g m
      have h2 := sum_range_succ g m
      have hgm : g m = g 0 := by simp only [hg]; rw [← hPm, Nat.mod_self]; simp
      have h3 : ∑ i ∈ range m, g (i + 1) = ∑ i ∈ range m, f ((6 * i + 6) % P) :=
        sum_congr rfl fun i _ => by simp only [hg]; ring_nf
      omega
    rw [hshift]
    have hgi : ∀ i ∈ range m, g i = f (6 * i) := by
      intro i hi
      simp only [hg]
      rw [Nat.mod_eq_of_lt (by have := mem_range.1 hi; omega)]
    rw [sum_congr rfl hgi]
    set Ac := A.filter (fun k => k % 6 = c)
    have hmaps : (Ac : Set ℕ).MapsTo (fun k => (k + e) % P / 6) (range m) := by
      intro k _
      simp only [coe_range, Set.mem_Iio]
      have := Nat.mod_lt (k + e) hP0
      omega
    rw [card_eq_sum_card_fiberwise hmaps]
    refine sum_congr rfl fun i hi => ?_
    simp only [hf, Ac]
    congr 1
    ext k
    simp only [mem_filter]
    have hmod : (k + e) % P % 6 = (k + e) % 6 := Nat.mod_mod_of_dvd _ hP6
    constructor
    · rintro ⟨hk, hkc⟩
      refine ⟨⟨hk, ?_⟩, ?_⟩
      · rw [hkc] at hmod; omega
      · rw [hkc]; omega
    · rintro ⟨⟨hk, hkc⟩, hki⟩
      refine ⟨hk, ?_⟩
      omega

/-- Bool form of the pattern lemma, for `c = 5` (offsets `u`, `k ≡ u + 5 (mod 6)`). -/
lemma pat5 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    5 ≤ b0.toNat + b1.toNat + b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat →
    (b0 && b1 && b2) = true ∨ (b0 && b3 && b4) = true ∨ (b0 && b3 && b6) = true ∨
      (b2 && b3 && b4) = true ∨ (b2 && b3 && b6) = true ∨ (b4 && b5 && b6) = true := by
  decide

/-- Bool form of the pattern lemma, for `c = 1`. -/
lemma pat1 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    5 ≤ b0.toNat + b1.toNat + b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat →
    (b0 && b1 && b2) = true ∨ (b0 && b1 && b4) = true ∨ (b0 && b3 && b6) = true ∨
      (b2 && b3 && b4) = true ∨ (b2 && b3 && b6) = true ∨ (b4 && b5 && b6) = true := by
  decide

/-- `u < v` are offsets whose classes can share no prime: `v - u ≠ 5`, and the corresponding
residues `u + c`, `v + c` mod 6 are not both even and not both divisible by 3. -/
def good6 (c u v : ℕ) : Prop :=
  u < v ∧ v < 7 ∧ v - u ≠ 5 ∧ ¬((c + u) % 2 = 0 ∧ (c + v) % 2 = 0) ∧
    ¬((c + u) % 3 = 0 ∧ (c + v) % 3 = 0)

instance (c u v : ℕ) : Decidable (good6 c u v) := by unfold good6; infer_instance

lemma pattern (c : ℕ) (hc : c = 1 ∨ c = 5) (hi : ℕ → Prop) [DecidablePred hi]
    (hcount : 5 ≤ ((range 7).filter hi).card) :
    ∃ u v w, hi u ∧ hi v ∧ hi w ∧ good6 c u v ∧ good6 c u w ∧ good6 c v w := by
  have hsum : ((range 7).filter hi).card = (decide (hi 0)).toNat + (decide (hi 1)).toNat +
      (decide (hi 2)).toNat + (decide (hi 3)).toNat + (decide (hi 4)).toNat +
      (decide (hi 5)).toNat + (decide (hi 6)).toNat := by
    simp only [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp [Bool.toNat, Bool.cond_decide]
  rw [hsum] at hcount
  rcases hc with rfl | rfl
  · rcases pat1 _ _ _ _ _ _ _ hcount with h | h | h | h | h | h <;>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    · exact ⟨0, 1, 2, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, 4, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨0, 3, 6, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 4, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 6, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨4, 5, 6, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
  · rcases pat5 _ _ _ _ _ _ _ hcount with h | h | h | h | h | h <;>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    · exact ⟨0, 1, 2, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨0, 3, 4, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨0, 3, 6, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 4, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 6, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩
    · exact ⟨4, 5, 6, h.1.1, h.1.2, h.2, by decide, by decide, by decide⟩

/-- Elements of the classes of two `good6` offsets of one block share no prime `≤ r`. -/
lemma no_small_common (r e c i u v k1 k2 p : ℕ) (hr : 6 ≤ r) (hec : (e + c) % 6 = 0)
    (h1 : (k1 + e) % r.factorial = (6 * i + u) % r.factorial)
    (h2 : (k2 + e) % r.factorial = (6 * i + v) % r.factorial)
    (hg : good6 c u v) (hp : p.Prime) (hpr : p ≤ r) (hpk1 : p ∣ k1) (hpk2 : p ∣ k2) : False := by
  obtain ⟨huv, hv7, hv5, h2g, h3g⟩ := hg
  set P := r.factorial
  have hP6 : 6 ∣ P := Nat.dvd_factorial (by norm_num) hr
  have hpP : p ∣ P := Nat.dvd_factorial hp.pos hpr
  -- residues mod 6
  have hk1_6 : (k1 + e) % 6 = (6 * i + u) % 6 := by
    have := congrArg (· % 6) h1
    simpa [Nat.mod_mod_of_dvd _ hP6] using this
  have hk2_6 : (k2 + e) % 6 = (6 * i + v) % 6 := by
    have := congrArg (· % 6) h2
    simpa [Nat.mod_mod_of_dvd _ hP6] using this
  -- `k1 + v ≡ k2 + u (mod p)`
  have hmodP : Nat.ModEq P (k1 + v + (e + 6 * i)) (k2 + u + (e + 6 * i)) := by
    have e1 : Nat.ModEq P (k1 + e) (6 * i + u) := h1
    have e2 : Nat.ModEq P (k2 + e) (6 * i + v) := h2
    have := Nat.ModEq.add e1 e2.symm
    unfold Nat.ModEq at this ⊢
    rw [show k1 + v + (e + 6 * i) = k1 + e + (6 * i + v) by ring,
      show k2 + u + (e + 6 * i) = 6 * i + u + (k2 + e) by ring]
    exact this
  have hmodp : Nat.ModEq p (k1 + v) (k2 + u) :=
    Nat.ModEq.of_dvd hpP (Nat.ModEq.add_right_cancel' _ hmodP)
  have hv : Nat.ModEq p v u := by
    have a1 : Nat.ModEq p k1 0 := (Nat.modEq_zero_iff_dvd).2 hpk1
    have a2 : Nat.ModEq p k2 0 := (Nat.modEq_zero_iff_dvd).2 hpk2
    have := (a1.add_right v).symm.trans (hmodp.trans (a2.add_right u))
    simpa using this
  have hdvd : p ∣ v - u := (Nat.modEq_iff_dvd' huv.le).1 hv.symm
  have hple : p ≤ v - u := Nat.le_of_dvd (by omega) hdvd
  have hp2 := hp.two_le
  have hp6 : p ≤ 6 := by omega
  interval_cases p
  · have : k1 % 2 = 0 := Nat.mod_eq_zero_of_dvd hpk1
    have : k2 % 2 = 0 := Nat.mod_eq_zero_of_dvd hpk2
    omega
  · have : k1 % 3 = 0 := Nat.mod_eq_zero_of_dvd hpk1
    have : k2 % 3 = 0 := Nat.mod_eq_zero_of_dvd hpk2
    omega
  · norm_num at hp
  · omega
  · norm_num at hp

lemma sq_div_le_of_mul_le {T r c : ℝ} (hc : 0 < c) (hT : 0 < T) (hr : c * T ^ 2 ≤ r) :
    T ^ 2 / r ≤ 1 / c := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  rw [div_le_div_iff₀ hr0 hc]
  linarith

lemma numeric_ii_b (l n r T M : ℝ) (hl : 1 ≤ l) (hT : 1 ≤ T) (hn : 0 ≤ n)
    (hr : (64 * l + 16) * T ^ 2 ≤ r) (hM : 64 * (l + 1) ≤ M) :
    2 * (2 * (n * M * T ^ 2) / r + 2 * n) ≤ n * M / 2 := by
  have h1 : T ^ 2 / r ≤ 1 / (64 * l + 16) :=
    sq_div_le_of_mul_le (by positivity) (by linarith) hr
  have h2 : 1 / (64 * l + 16) ≤ (1 : ℝ) / 16 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hnM : 0 ≤ n * M := mul_nonneg hn (by linarith)
  have e : 2 * (2 * (n * M * T ^ 2) / r + 2 * n) = 4 * (n * M) * (T ^ 2 / r) + 4 * n := by ring
  rw [e]
  have h3 : 4 * (n * M) * (T ^ 2 / r) ≤ 4 * (n * M) * (1 / 16) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
  have h4 : 16 * n ≤ n * M := by nlinarith
  linarith

lemma numeric_ii_d (l n r T M : ℝ) (hl : 1 ≤ l) (hT : 1 ≤ T) (hn : 0 ≤ n)
    (hr : (64 * l + 16) * T ^ 2 ≤ r) (hM : 64 * (l + 1) ≤ M) :
    4 * l * (2 * (n * M * T ^ 2) / r + 2 * n) ≤ n * M / 4 := by
  have hr' : (64 * l) * T ^ 2 ≤ r := by nlinarith [sq_nonneg T]
  have h1 : T ^ 2 / r ≤ 1 / (64 * l) := sq_div_le_of_mul_le (by positivity) (by linarith) hr'
  have hnM : 0 ≤ n * M := mul_nonneg hn (by linarith)
  have e : 4 * l * (2 * (n * M * T ^ 2) / r + 2 * n) =
      8 * l * (n * M) * (T ^ 2 / r) + 8 * l * n := by ring
  rw [e]
  have h3 : 8 * l * (n * M) * (T ^ 2 / r) ≤ 8 * l * (n * M) * (1 / (64 * l)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 8 * l * (n * M) * (1 / (64 * l)) = n * M / 8 := by
    field_simp; ring
  have h5 : 8 * l * n * 8 ≤ n * M := by nlinarith
  linarith

/-- The real inequalities needed in the dense case. -/
lemma numeric_ii (l n P r : ℕ) (hl : 1 ≤ l) (hP : 1 ≤ P)
    (hr : (64 * l + 16) * 2 ^ (4 * l + 46) ≤ r)
    (hn : 64 * (l + 1) * P ^ 2 * 2 ^ (4 * l + 46) ≤ n) :
    4 * ((n : ℝ) / P + 1) + 3 * (1 / 2 ^ (2 * l + 23)) * ((n : ℝ) / P) <
        4 * ((n : ℝ) / P) + 6 * (1 / 2 ^ (2 * l + 23)) * ((n : ℝ) / P) ∧
      2 * (2 * ((n : ℝ) / P) ^ 2 / r + 2 * n) ≤
        ((1 / 2 ^ (2 * l + 23)) * ((n : ℝ) / P)) ^ 2 / 2 ∧
      (2 * l : ℝ) ≤ (1 / 2 ^ (2 * l + 23)) * ((n : ℝ) / P) / 2 ∧
      4 * l * (2 * ((n : ℝ) / P) ^ 2 / r + 2 * n) ≤
        ((1 / 2 ^ (2 * l + 23)) * ((n : ℝ) / P) / 2) ^ 2 := by
  set T : ℝ := 2 ^ (2 * l + 23) with hT
  have hT1 : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hK : (2 : ℝ) ^ (4 * l + 46) = T ^ 2 := by
    rw [hT, ← pow_mul]; ring_nf
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hr' : ((64 * l + 16 : ℕ) : ℝ) * T ^ 2 ≤ r := by
    rw [← hK]; exact_mod_cast hr
  push_cast at hr'
  have hn' : 64 * ((l : ℝ) + 1) * (P : ℝ) ^ 2 * T ^ 2 ≤ n := by
    rw [← hK]; exact_mod_cast hn
  have hP0 : (0 : ℝ) < P := by linarith
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) < 64 * ((l : ℝ) + 1) * (P : ℝ) ^ 2 * T ^ 2 := by positivity
    linarith
  set M : ℝ := n / ((P : ℝ) ^ 2 * T ^ 2) with hM
  have hM64 : 64 * ((l : ℝ) + 1) ≤ M := by
    rw [hM, le_div_iff₀ (by positivity)]; linarith
  have hbN : (1 / T) * ((n : ℝ) / P) = M * P * T := by
    rw [hM]; field_simp
  have hbN2 : ((1 / T) * ((n : ℝ) / P)) ^ 2 = n * M := by
    rw [hM]; field_simp
  have hN2 : ((n : ℝ) / P) ^ 2 = n * M * T ^ 2 := by
    rw [hM]; field_simp
  have hMPT : M ≤ M * P * T := by
    have h1 : 1 ≤ (P : ℝ) * T := by nlinarith
    have hM0 : 0 ≤ M := by linarith
    have := mul_le_mul_of_nonneg_left h1 hM0
    linarith [mul_assoc M (P : ℝ) T]
  have hβN : 4 * (l : ℝ) ≤ (1 / T) * ((n : ℝ) / P) := by rw [hbN]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : 4 * ((n : ℝ) / P + 1) + 3 * (1 / T) * ((n : ℝ) / P) =
        4 * ((n : ℝ) / P) + 4 + 3 * ((1 / T) * ((n : ℝ) / P)) := by ring
    have e2 : 4 * ((n : ℝ) / P) + 6 * (1 / T) * ((n : ℝ) / P) =
        4 * ((n : ℝ) / P) + 6 * ((1 / T) * ((n : ℝ) / P)) := by ring
    rw [e, e2]
    linarith
  · rw [hN2, hbN2]
    exact numeric_ii_b l n r T M hl' hT1 hn0.le hr' hM64
  · linarith
  · rw [hN2, div_pow, hbN2]
    have := numeric_ii_d l n r T M hl' hT1 hn0.le hr' hM64
    linarith

lemma tau_ne {P i u v : ℕ} (hP : 7 ≤ P) (huv : u < v) (hv : v < 7) :
    (6 * i + u) % P ≠ (6 * i + v) % P := by
  intro h
  have h1 : Nat.ModEq P (6 * i + u) (6 * i + v) := h
  have h2 : Nat.ModEq P u v := Nat.ModEq.add_left_cancel' (6 * i) h1
  unfold Nat.ModEq at h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  omega

/-- The dense case, once three suitable classes of one block have been found. -/
lemma good_of_classes (l n r e c i u v w : ℕ) (A : Finset ℕ) (hl : 1 ≤ l) (hr : 7 ≤ r)
    (hA : A ⊆ Icc 1 n) (hec : (e + c) % 6 = 0)
    (huv : good6 c u v) (huw : good6 c u w) (hvw : good6 c v w) (β : ℝ)
    (hKu : β * ((n : ℝ) / r.factorial) ≤
      (A.filter (fun k => (k + e) % r.factorial = (6 * i + u) % r.factorial)).card)
    (hKv : β * ((n : ℝ) / r.factorial) ≤
      (A.filter (fun k => (k + e) % r.factorial = (6 * i + v) % r.factorial)).card)
    (hKw : β * ((n : ℝ) / r.factorial) ≤
      (A.filter (fun k => (k + e) % r.factorial = (6 * i + w) % r.factorial)).card)
    (hb : 2 * (2 * ((n : ℝ) / r.factorial) ^ 2 / r + 2 * n) ≤ (β * ((n : ℝ) / r.factorial)) ^ 2 / 2)
    (hc : (2 * l : ℝ) ≤ β * ((n : ℝ) / r.factorial) / 2)
    (hd : 4 * l * (2 * ((n : ℝ) / r.factorial) ^ 2 / r + 2 * n) ≤
      (β * ((n : ℝ) / r.factorial) / 2) ^ 2) :
    Good A l := by
  set P := r.factorial with hP
  have hP7 : 7 ≤ P := le_trans hr (Nat.self_le_factorial r)
  set X : ℝ := β * ((n : ℝ) / P) with hX
  set Bd : ℝ := 2 * ((n : ℝ) / P) ^ 2 / r + 2 * n with hBd
  have hr1 : 1 ≤ r := by omega
  have hX4 : 4 ≤ X := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  set Ku := A.filter (fun k => (k + e) % P = (6 * i + u) % P) with hKu_def
  set Kv := A.filter (fun k => (k + e) % P = (6 * i + v) % P) with hKv_def
  set Kw := A.filter (fun k => (k + e) % P = (6 * i + w) % P) with hKw_def
  set Cu := cls n P e ((6 * i + u) % P)
  set Cv := cls n P e ((6 * i + v) % P)
  set Cw := cls n P e ((6 * i + w) % P)
  have hsub : ∀ τ, A.filter (fun k => (k + e) % P = τ) ⊆ cls n P e τ := by
    intro τ k hk
    simp only [mem_filter] at hk
    simp only [cls, mem_filter]
    exact ⟨hA hk.1, hk.2⟩
  have hsmall : ∀ a b, good6 c a b → ∀ k1 ∈ cls n P e ((6 * i + a) % P),
      ∀ k2 ∈ cls n P e ((6 * i + b) % P), ∀ p, p.Prime → p ≤ r → p ∣ k1 → p ∣ k2 → False := by
    intro a b hab k1 hk1 k2 hk2 p hp hpr h1 h2
    exact no_small_common r e c i a b k1 k2 p (by omega) hec (mem_filter.1 hk1).2
      (mem_filter.1 hk2).2 hab hp hpr h1 h2
  -- choose the centre `x`
  have hbad_uv := bad_pairs_le n r e _ _ hr1 Ku Cv (hsub _) subset_rfl
    (fun k1 hk1 k2 hk2 => hsmall u v huv k1 (hsub _ hk1) k2 hk2)
  have hbad_uw := bad_pairs_le n r e _ _ hr1 Ku Cw (hsub _) subset_rfl
    (fun k1 hk1 k2 hk2 => hsmall u w huw k1 (hsub _ hk1) k2 hk2)
  have hKu_pos : (0 : ℝ) < Ku.card := by linarith
  have hKu_ne : Ku.Nonempty := card_pos.1 (by exact_mod_cast hKu_pos)
  obtain ⟨x, hxK, hxD⟩ : ∃ x ∈ Ku, (((Cv.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ) +
      (Cw.filter (fun y => ¬ Nat.Coprime x y)).card) * Ku.card ≤ 2 * Bd := by
    by_contra hcon
    push Not at hcon
    have h1 : ∑ x ∈ Ku, (2 * Bd) < ∑ x ∈ Ku, (((Cv.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ) +
        (Cw.filter (fun y => ¬ Nat.Coprime x y)).card) * Ku.card :=
      sum_lt_sum_of_nonempty hKu_ne hcon
    rw [sum_const, nsmul_eq_mul, ← sum_mul, sum_add_distrib] at h1
    have h2 : (∑ x ∈ Ku, ((Cv.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ) +
        ∑ x ∈ Ku, ((Cw.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ)) * Ku.card ≤
        (2 * Bd) * Ku.card := mul_le_mul_of_nonneg_right (by linarith) hKu_pos.le
    linarith
  have hxA : x ∈ A := (mem_filter.1 hxK).1
  set dv := ((Cv.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ)
  set dw := ((Cw.filter (fun y => ¬ Nat.Coprime x y)).card : ℝ)
  have hdamage : dv + dw ≤ X / 2 := by
    have h1 : (dv + dw) * X ≤ (dv + dw) * Ku.card :=
      mul_le_mul_of_nonneg_left hKu (by positivity)
    have h2 : (dv + dw) * X ≤ X ^ 2 / 2 := by linarith
    have h3 : (dv + dw) * X ≤ (X / 2) * X := by nlinarith
    exact le_of_mul_le_mul_right h3 (by linarith)
  -- the two other classes, restricted to numbers coprime to `x`
  set Y0 := Kv.filter (fun y => Nat.Coprime x y) with hY0
  set Z0 := Kw.filter (fun z => Nat.Coprime x z) with hZ0
  have hY0card : X / 2 ≤ Y0.card := by
    have h1 := card_filter_add_card_filter_not (s := Kv) (fun y => Nat.Coprime x y)
    have h2 : (Kv.filter (fun y => ¬ Nat.Coprime x y)).card ≤
        (Cv.filter (fun y => ¬ Nat.Coprime x y)).card :=
      card_le_card (filter_subset_filter _ (hsub _))
    have h1' : ((Y0.card : ℕ) : ℝ) + ((Kv.filter (fun y => ¬ Nat.Coprime x y)).card : ℕ) =
        Kv.card := by exact_mod_cast h1
    have h2' : (((Kv.filter (fun y => ¬ Nat.Coprime x y)).card : ℕ) : ℝ) ≤ dv :=
      Nat.cast_le.2 h2
    have hdw : 0 ≤ dw := by positivity
    linarith
  have hZ0card : X / 2 ≤ Z0.card := by
    have h1 := card_filter_add_card_filter_not (s := Kw) (fun z => Nat.Coprime x z)
    have h2 : (Kw.filter (fun z => ¬ Nat.Coprime x z)).card ≤
        (Cw.filter (fun z => ¬ Nat.Coprime x z)).card :=
      card_le_card (filter_subset_filter _ (hsub _))
    have h1' : ((Z0.card : ℕ) : ℝ) + ((Kw.filter (fun z => ¬ Nat.Coprime x z)).card : ℕ) =
        Kw.card := by exact_mod_cast h1
    have h2' : (((Kw.filter (fun z => ¬ Nat.Coprime x z)).card : ℕ) : ℝ) ≤ dw :=
      Nat.cast_le.2 h2
    have hdv : 0 ≤ dv := by positivity
    linarith
  -- few bad pairs between `Y0` and `Z0`
  have hY0C : Y0 ⊆ Cv := (filter_subset _ _).trans (hsub _)
  have hbad_vw := bad_pairs_le n r e _ _ hr1 Y0 Cw hY0C subset_rfl
    (fun k1 hk1 k2 hk2 => hsmall v w hvw k1 (hY0C hk1) k2 hk2)
  have hsumZ : ∑ y ∈ Y0, (Z0.filter (fun z => ¬ Nat.Coprime y z)).card ≤
      ∑ y ∈ Y0, (Cw.filter (fun z => ¬ Nat.Coprime y z)).card :=
    sum_le_sum fun y _ => card_le_card
      (filter_subset_filter _ ((filter_subset _ _).trans (hsub _)))
  have hgreedy : 4 * l * ∑ y ∈ Y0, (Z0.filter (fun z => ¬ Nat.Coprime y z)).card ≤
      Y0.card * Z0.card := by
    have h1 : ((∑ y ∈ Y0, (Z0.filter (fun z => ¬ Nat.Coprime y z)).card : ℕ) : ℝ) ≤ Bd := by
      have : ((∑ y ∈ Y0, (Z0.filter (fun z => ¬ Nat.Coprime y z)).card : ℕ) : ℝ) ≤
          ∑ y ∈ Y0, ((Cw.filter (fun z => ¬ Nat.Coprime y z)).card : ℝ) := by
        exact_mod_cast hsumZ
      linarith
    have h2 : ((4 * l * ∑ y ∈ Y0, (Z0.filter (fun z => ¬ Nat.Coprime y z)).card : ℕ) : ℝ) ≤
        (Y0.card : ℝ) * Z0.card := by
      push_cast
      have hl0 : (0 : ℝ) ≤ 4 * l := by positivity
      have h3 : 4 * (l : ℝ) * ((∑ y ∈ Y0, (Z0.filter (fun z => ¬ Nat.Coprime y z)).card : ℕ) : ℝ)
          ≤ 4 * l * Bd := mul_le_mul_of_nonneg_left h1 hl0
      have h4 : (X / 2) * (X / 2) ≤ (Y0.card : ℝ) * Z0.card :=
        mul_le_mul hY0card hZ0card (by linarith) (by positivity)
      push_cast at h3
      nlinarith
    exact_mod_cast h2
  have hY2 : 2 * l ≤ Y0.card := by
    have : (2 * l : ℝ) ≤ Y0.card := by linarith
    exact_mod_cast this
  have hZ2 : 2 * l ≤ Z0.card := by
    have : (2 * l : ℝ) ≤ Z0.card := by linarith
    exact_mod_cast this
  obtain ⟨Y, hYsub, Z, hZsub, hYcard, hZcard, hYZ⟩ :=
    greedy l hl Y0 Z0 (fun y z => Nat.Coprime y z) hY2 hZ2 hgreedy
  have hYK : ∀ y ∈ Y, y ∈ A ∧ (y + e) % P = (6 * i + v) % P ∧ Nat.Coprime x y := by
    intro y hy
    have h := hYsub hy
    simp only [hY0, hKv_def, mem_filter] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hZK : ∀ z ∈ Z, z ∈ A ∧ (z + e) % P = (6 * i + w) % P ∧ Nat.Coprime x z := by
    intro z hz
    have h := hZsub hz
    simp only [hZ0, hKw_def, mem_filter] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hxe : (x + e) % P = (6 * i + u) % P := (mem_filter.1 hxK).2
  refine ⟨x, hxA, Y, Z, fun y hy => (hYK y hy).1, fun z hz => (hZK z hz).1, hYcard, hZcard,
    ?_, ?_, ?_, fun y hy => (hYK y hy).2.2, fun z hz => (hZK z hz).2.2, hYZ⟩
  · intro hx
    exact tau_ne hP7 huv.1 huv.2.1 (hxe.symm.trans (hYK x hx).2.1)
  · intro hx
    exact tau_ne hP7 huw.1 huw.2.1 (hxe.symm.trans (hZK x hx).2.1)
  · rw [disjoint_left]
    intro y hy hyZ
    exact tau_ne hP7 hvw.1 hvw.2.1 ((hYK y hy).2.1.symm.trans (hZK y hyZ).2.1)

lemma exists_block (A : Finset ℕ) (P e c : ℕ) (hP6 : 6 ∣ P) (hP0 : 0 < P)
    (hec : (e + c) % 6 = 0) (hc : c < 6) :
    ∃ i ∈ range (P / 6), A.card + (A.filter (fun k => k % 6 = c)).card ≤
      (P / 6) * ∑ u ∈ range 7, (A.filter (fun k => (k + e) % P = (6 * i + u) % P)).card := by
  have htot := block_total A P e c hP6 hP0 hec hc
  have hm : 0 < P / 6 := Nat.div_pos (Nat.le_of_dvd hP0 hP6) (by norm_num)
  by_contra hcon
  push Not at hcon
  have hne : (range (P / 6)).Nonempty := nonempty_range_iff.2 (by omega)
  have h1 := sum_lt_sum_of_nonempty hne hcon
  rw [← mul_sum, htot, sum_const, card_range, smul_eq_mul] at h1
  exact lt_irrefl _ h1

lemma sum_le_of_few_high (a : ℕ → ℝ) (X Y : ℝ) (hXY : Y ≤ X) (ha : ∀ u, a u ≤ X)
    (hi : ℕ → Prop) [DecidablePred hi] (hlow : ∀ u, ¬ hi u → a u ≤ Y)
    (hcnt : ((range 7).filter hi).card ≤ 4) :
    ∑ u ∈ range 7, a u ≤ 4 * X + 3 * Y := by
  rw [← sum_filter_add_sum_filter_not (range 7) hi]
  have h1 : ∑ u ∈ (range 7).filter hi, a u ≤ ((range 7).filter hi).card * X := by
    rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun u _ => ha u
  have h2 : ∑ u ∈ (range 7).filter (fun u => ¬ hi u), a u ≤
      ((range 7).filter (fun u => ¬ hi u)).card * Y := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun u hu => hlow u (mem_filter.1 hu).2
  have h3 := card_filter_add_card_filter_not (s := range 7) hi
  rw [card_range] at h3
  have h3' : (((range 7).filter hi).card : ℝ) + ((range 7).filter (fun u => ¬ hi u)).card = 7 := by
    exact_mod_cast h3
  have h4 : (((range 7).filter hi).card : ℝ) ≤ 4 := by exact_mod_cast hcnt
  set F := (((range 7).filter hi).card : ℝ)
  set G := (((range 7).filter (fun u => ¬ hi u)).card : ℝ)
  have h5 : F * (X - Y) ≤ 4 * (X - Y) := mul_le_mul_of_nonneg_right h4 (sub_nonneg.2 hXY)
  have h6 : G * Y = 7 * Y - F * Y := by rw [show G = 7 - F by linarith]; ring
  have h7 : F * (X - Y) = F * X - F * Y := by ring
  linarith

/-- The parameter `r` of the dense case. -/
def rII (l : ℕ) : ℕ := (64 * l + 16) * 2 ^ (4 * l + 46) + 7

lemma case_ii_core (l n r : ℕ) (A : Finset ℕ) (c e : ℕ) (hl : 1 ≤ l) (hA : A ⊆ Icc 1 n)
    (hA3 : 2 * n ≤ 3 * A.card) (hb : (n : ℝ) / 2 ^ (2 * l + 22) < (Bset A).card)
    (hsc : (Bset A).card ≤ 2 * (A.filter (fun k => k % 6 = c)).card)
    (hec : (e + c) % 6 = 0) (hc : c = 1 ∨ c = 5) (hr7 : 7 ≤ r)
    (hr : (64 * l + 16) * 2 ^ (4 * l + 46) ≤ r)
    (hn : 64 * (l + 1) * r.factorial ^ 2 * 2 ^ (4 * l + 46) ≤ n) : Good A l := by
  set P := r.factorial with hP
  have hP6 : 6 ∣ P := Nat.dvd_factorial (by norm_num) (by omega)
  have hP0 : 0 < P := Nat.factorial_pos r
  obtain ⟨na, nb, nc, nd⟩ := numeric_ii l n P r hl hP0 hr hn
  set β : ℝ := 1 / 2 ^ (2 * l + 23) with hβ
  set N' : ℝ := (n : ℝ) / P with hN'
  obtain ⟨i, _, hblock⟩ := exists_block A P e c hP6 hP0 hec (by omega)
  set a : ℕ → ℕ := fun u => (A.filter (fun k => (k + e) % P = (6 * i + u) % P)).card with ha
  -- the block sum is large
  have hblock_real : 4 * N' + 6 * β * N' ≤ ∑ u ∈ range 7, (a u : ℝ) := by
    have hm : ((P / 6 : ℕ) : ℝ) = (P : ℝ) / 6 := by
      have := Nat.div_mul_cancel hP6
      have h' : ((P / 6 : ℕ) : ℝ) * 6 = (P : ℝ) := by exact_mod_cast this
      linarith
    have h1 : ((A.card + (A.filter (fun k => k % 6 = c)).card : ℕ) : ℝ) ≤
        ((P / 6 : ℕ) : ℝ) * ((∑ u ∈ range 7, a u : ℕ) : ℝ) := by exact_mod_cast hblock
    rw [hm] at h1
    push_cast at h1
    have hA3' : (2 : ℝ) * n ≤ 3 * A.card := by exact_mod_cast hA3
    have hsc' : ((Bset A).card : ℝ) ≤ 2 * (A.filter (fun k => k % 6 = c)).card := by
      exact_mod_cast hsc
    have hβn : β * n < ((A.filter (fun k => k % 6 = c)).card : ℝ) := by
      have e2 : (2 : ℝ) ^ (2 * l + 23) = 2 * 2 ^ (2 * l + 22) := by ring
      have : β * n = (n : ℝ) / 2 ^ (2 * l + 22) / 2 := by
        rw [hβ, e2]; field_simp
      rw [this]; linarith
    have hP0' : (0 : ℝ) < P := by exact_mod_cast hP0
    rw [hN']
    have key : (4 * ((n : ℝ) / P) + 6 * β * ((n : ℝ) / P)) * ((P : ℝ) / 6) =
        (2 * n / 3 + β * n) := by field_simp; ring
    have h2 : (2 * (n : ℝ) / 3 + β * n) ≤ (P : ℝ) / 6 * ∑ u ∈ range 7, (a u : ℝ) := by
      linarith
    have h3 : (4 * ((n : ℝ) / P) + 6 * β * ((n : ℝ) / P)) * ((P : ℝ) / 6) ≤
        (∑ u ∈ range 7, (a u : ℝ)) * ((P : ℝ) / 6) := by
      rw [key]; linarith
    exact le_of_mul_le_mul_right h3 (by positivity)
  -- each class is small
  have ha_le : ∀ u, (a u : ℝ) ≤ N' + 1 := by
    intro u
    have h1 : a u ≤ n / P + 1 := by
      refine le_trans (card_le_card fun k hk => ?_) (card_cls_le n P e ((6 * i + u) % P))
      simp only [mem_filter] at hk
      simp only [cls, mem_filter]
      exact ⟨hA hk.1, hk.2⟩
    have h2 : ((n / P : ℕ) : ℝ) ≤ (n : ℝ) / P := Nat.cast_div_le
    have h3 : ((a u : ℕ) : ℝ) ≤ ((n / P + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  classical
  set hi : ℕ → Prop := fun u => β * N' ≤ (a u : ℝ) with hhi
  have hβ1 : β ≤ 1 := by
    rw [hβ]; exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
  have hN0 : 0 ≤ N' := by positivity
  have hcount : 5 ≤ ((range 7).filter hi).card := by
    by_contra hcon
    have hle := sum_le_of_few_high (fun u => (a u : ℝ)) (N' + 1) (β * N')
      (by nlinarith) ha_le hi (fun u hu => le_of_lt (not_le.1 hu)) (by omega)
    have : 4 * (N' + 1) + 3 * (β * N') < 4 * N' + 6 * β * N' := by
      have := na
      linarith
    linarith
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ := pattern c hc hi hcount
  exact good_of_classes l n r e c i u v w A hl hr7 hA hec huv huw hvw β hu hv hw nb nc nd

/-- **Dense case.** If `|B| > n / 2^(2l+22)`, the configuration exists for large `n`. -/
theorem case_ii (l : ℕ) (hl : 1 ≤ l) : ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 n →
    n / 2 + n / 3 - n / 6 < A.card →
    (n : ℝ) / 2 ^ (2 * l + 22) < (Bset A).card → Good A l := by
  filter_upwards [eventually_ge_atTop (64 * (l + 1) * (rII l).factorial ^ 2 * 2 ^ (4 * l + 46))]
    with n hn A hA hcard hb
  have hr7 : 7 ≤ rII l := Nat.le_add_left _ _
  have hr : (64 * l + 16) * 2 ^ (4 * l + 46) ≤ rII l := Nat.le_add_right _ _
  have hA3 : 2 * n ≤ 3 * A.card := by omega
  have hB : (Bset A).card = (A.filter (fun k => k % 6 = 1)).card +
      (A.filter (fun k => k % 6 = 5)).card := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun k _ h1 h2 => by omega)]
    congr 1
    ext k
    simp [Bset, mem_filter, mem_union, and_or_left]
  by_cases h5 : (Bset A).card ≤ 2 * (A.filter (fun k => k % 6 = 5)).card
  · exact case_ii_core l n (rII l) A 5 1 hl hA hA3 hb h5 (by norm_num) (Or.inr rfl) hr7 hr hn
  · have h1 : (Bset A).card ≤ 2 * (A.filter (fun k => k % 6 = 1)).card := by omega
    have hP6 : 6 ∣ (rII l).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hP0 := Nat.factorial_pos (rII l)
    refine case_ii_core l n (rII l) A 1 ((rII l).factorial - 1) hl hA hA3 hb h1 ?_ (Or.inl rfl)
      hr7 hr hn
    have : (rII l).factorial - 1 + 1 = (rII l).factorial := Nat.sub_add_cancel hP0
    rw [this]
    exact Nat.mod_eq_zero_of_dvd hP6

/-- The vertex map of the copy of `K(1, l, l)`. -/
def vmap (l x : ℕ) (fY fZ : Fin l → ℕ) : (Σ i : Fin 3, Fin (![1, l, l] i)) → ℕ
  | ⟨⟨0, _⟩, _⟩ => x
  | ⟨⟨1, _⟩, j⟩ => fY j
  | ⟨⟨2, _⟩, j⟩ => fZ j
  | ⟨⟨k + 3, h⟩, _⟩ => absurd h (by omega)

lemma isContained_of_good {A : Finset ℕ} {l : ℕ} (h : Good A l) :
    (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
      (coprimeGraph.induce (A : Set ℕ)) := by
  obtain ⟨x, hxA, Y, Z, hYA, hZA, hYc, hZc, hxY, hxZ, hYZ, hxy, hxz, hyz⟩ := h
  set fY : Fin l → ℕ := fun j => Y.orderEmbOfFin hYc j with hfY
  set fZ : Fin l → ℕ := fun j => Z.orderEmbOfFin hZc j with hfZ
  have hfYm : ∀ j, fY j ∈ Y := fun j => orderEmbOfFin_mem Y hYc j
  have hfZm : ∀ j, fZ j ∈ Z := fun j => orderEmbOfFin_mem Z hZc j
  have hfYi : Function.Injective fY := (Y.orderEmbOfFin hYc).injective
  have hfZi : Function.Injective fZ := (Z.orderEmbOfFin hZc).injective
  set g := vmap l x fY fZ with hg
  -- the three parts
  have hpart : ∀ v : (Σ i : Fin 3, Fin (![1, l, l] i)),
      (v.1 = 0 ∧ g v = x) ∨ (v.1 = 1 ∧ ∃ j, g v = fY j) ∨ (v.1 = 2 ∧ ∃ j, g v = fZ j) := by
    rintro ⟨⟨k, hk⟩, j⟩
    match k, hk, j with
    | 0, _, _ => exact Or.inl ⟨rfl, rfl⟩
    | 1, _, j => exact Or.inr (Or.inl ⟨rfl, j, rfl⟩)
    | 2, _, j => exact Or.inr (Or.inr ⟨rfl, j, rfl⟩)
    | k + 3, hk, _ => omega
  have hmemA : ∀ v, g v ∈ A := by
    intro v
    rcases hpart v with ⟨_, hv⟩ | ⟨_, j, hv⟩ | ⟨_, j, hv⟩ <;> rw [hv]
    · exact hxA
    · exact hYA (hfYm j)
    · exact hZA (hfZm j)
  let f : (Σ i : Fin 3, Fin (![1, l, l] i)) → (A : Set ℕ) := fun v => ⟨g v, hmemA v⟩
  have hadj : ∀ u v : (Σ i : Fin 3, Fin (![1, l, l] i)), u.1 ≠ v.1 →
      g u ≠ g v ∧ Nat.Coprime (g u) (g v) := by
    intro u v huv
    have hY : ∀ j, x ≠ fY j := fun j h => hxY (h ▸ hfYm j)
    have hZ : ∀ j, x ≠ fZ j := fun j h => hxZ (h ▸ hfZm j)
    have hYZ' : ∀ j j', fY j ≠ fZ j' := fun j j' h =>
      (disjoint_left.1 hYZ) (hfYm j) (h ▸ hfZm j')
    rcases hpart u with ⟨hu, hgu⟩ | ⟨hu, ju, hgu⟩ | ⟨hu, ju, hgu⟩ <;>
      rcases hpart v with ⟨hv, hgv⟩ | ⟨hv, jv, hgv⟩ | ⟨hv, jv, hgv⟩ <;>
      rw [hgu, hgv] <;> first
        | exact absurd (hu.trans hv.symm) huv
        | exact ⟨hY jv, hxy _ (hfYm jv)⟩
        | exact ⟨hZ jv, hxz _ (hfZm jv)⟩
        | exact ⟨(hY ju).symm, (hxy _ (hfYm ju)).symm⟩
        | exact ⟨hYZ' ju jv, hyz _ (hfYm ju) _ (hfZm jv)⟩
        | exact ⟨(hZ ju).symm, (hxz _ (hfZm ju)).symm⟩
        | exact ⟨(hYZ' jv ju).symm, (hyz _ (hfYm jv) _ (hfZm ju)).symm⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, b⟩ huv
    have hg' : g ⟨⟨k, hk⟩, a⟩ = g ⟨⟨k', hk'⟩, b⟩ := congrArg Subtype.val huv
    by_cases hkk : k = k'
    · subst hkk
      simp only [Sigma.mk.injEq]
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      · have ha : a.1 < 1 := a.2
        have hb : b.1 < 1 := b.2
        refine ⟨trivial, heq_of_eq (Fin.ext (by omega))⟩
      · exact ⟨trivial, heq_of_eq (hfYi hg')⟩
      · exact ⟨trivial, heq_of_eq (hfZi hg')⟩
    · exact absurd hg' (hadj _ _ (fun h => hkk (congrArg Fin.val h))).1
  refine ⟨⟨⟨f, fun {u v} huv => ?_⟩, hinj⟩⟩
  have huv' : u.1 ≠ v.1 := by simpa [SimpleGraph.completeMultipartiteGraph] using huv
  rw [SimpleGraph.induce_adj]
  simp only [coprimeGraph, SimpleGraph.fromRel_adj]
  exact ⟨(hadj u v huv').1, Or.inl (hadj u v huv').2⟩

/-- For every `l ≥ 1`, if `n` is sufficiently large and `|A| > ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋`, then the
coprime graph on `A ⊆ {1, …, n}` contains `K(1, l, l)`. -/
theorem erdos_883_parts_ii_direct :
    ∀ l : ℕ, 1 ≤ l → ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
        (coprimeGraph.induce (A : Set ℕ)) := by
  intro l hl
  filter_upwards [case_i l, case_ii l hl] with n h1 h2 A hA hcard
  rcases le_or_gt ((Bset A).card : ℝ) ((n : ℝ) / 2 ^ (2 * l + 22)) with hb | hb
  · exact isContained_of_good (h1 A hA hcard hb)
  · exact isContained_of_good (h2 A hA hcard hb)

open scoped Classical in
/--
Is it true that, for every $\ell\geq 1$, if $n$ is sufficiently large and
$$|A| > \lfloor n/2\rfloor + \lfloor n/3\rfloor - \lfloor n/6\rfloor$$
then $G(A)$ must contain a complete $(1,\ell,\ell)$ tripartite graph on $2\ell+1$ vertices?

The second question was solved by Sárközy [Sa99], who proved this with
$\ell \gg \log n/\log\log n$.

The statement is copied from formal-conjectures, with `answer(True)` written as `True`.
-/
theorem erdos_883.parts.ii : True ↔
    ∀ l : ℕ, 1 ≤ l → ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
        (coprimeGraph.induce (A : Set ℕ)) :=
  iff_of_true trivial erdos_883_parts_ii_direct

end Erdos883

-- Verification of the actual upstream final targets on the local toolchain.
#print axioms Erdos883.erdos_883_parts_ii_direct
#print axioms Erdos883.erdos_883.parts.ii
