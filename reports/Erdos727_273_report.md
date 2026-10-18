# Erdős Problems 727 & 273 Formalization Report

## Overview

We provide 100% original, zero-`sorry`, zero-custom-axiom Lean 4 (`v4.33.1`) proofs for **Erdős Problem 727 (`JSP-000595`)** and **Erdős Problem 273 (`JSP-000234`)** in `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos727_273.lean`:

- **`Erdos727.erdos_727.variants.k_1`** (`@[category research solved, question]` in `FormalConjectures/ErdosProblems/727.lean`):
  $$\operatorname{Set.Infinite} \left\{n : \mathbb{N} \;\middle|\; ((n + 1)!)^2 \mid (2n)!\right\}.$$
  Equivalently, $(n + 1)^2 \mid \binom{2n}{n}$ (so $n + 1$ divides the $n$-th Catalan number $C_n = \frac{1}{n+1}\binom{2n}{n}$) for infinitely many $n \in \mathbb{N}$.
- **`Erdos273.erdos_273.variants.three`** (`@[category research solved, question]` in `FormalConjectures/ErdosProblems/273.lean`) and **`Erdos273.erdos_273.variants.three_int`**:
  $$\exists c : \operatorname{StrictCoveringSystem} \mathbb{N},\ \forall i,\ \exists p,\ p.\operatorname{Prime} \wedge 3 \le p \wedge c.\operatorname{moduli} i = \operatorname{Ideal.span} \{\uparrow(p - 1)\},$$
  together with the corresponding theorem for $\operatorname{StrictCoveringSystem} \mathbb{Z}$.

---

## Mathematical Proof Summaries

### 1. Erdős Problem 727 (`Erdos727.erdos_727.variants.k_1`)

- **Reduction to Central Binomial Coefficient (`factorial_sq_dvd_two_mul_factorial_iff`)**:
  Using $(2n)! = \binom{2n}{n} (n!)^2$ and $((n + 1)!)^2 = (n + 1)^2 (n!)^2$, cancelling $(n!)^2 \ne 0$ shows $((n + 1)!)^2 \mid (2n)! \iff (n + 1)^2 \mid \binom{2n}{n}$.
- **Kummer Carry Lower Bound (`prime_pow_dvd_centralBinom_of_carries` & `prime_sq_dvd_centralBinom_of_mul_sub_one`)**:
  By Kummer's theorem (`Nat.factorization_choose'`), for any prime $p$, $v_p\big(\binom{2n}{n}\big)$ is the number of exponents $i \ge 1$ such that $p^i \le 2(n \bmod p^i)$.
  When $n = m p - 1$ with $(2k + 1) p < 2m$ and $m \le (k + 1) p$, writing $m - 1 = k p + r$ gives $n \bmod p = p - 1$ (carry at level $1$) and $n \bmod p^2 = r p + (p - 1)$ with $p \le 2r + 1$, so $p^2 \le 2(n \bmod p^2)$ (carry at level $2$). Hence $p^2 \mid \binom{2n}{n}$.
- **Two Complementary Prime-Pair Families (`balakram_case_one` and `balakram_case_four`)**:
  1. **Family 1 ($c = 1$, $n = p q - 1$)**: For primes $3 < p < q$ with $\frac{3}{2} p < q < 2p$, applying the unified carry lemma with $(m, k) = (p, 0)$ for $q$ and $(m, k) = (q, 1)$ for $p$ gives $q^2 \mid \binom{2n}{n}$ and $p^2 \mid \binom{2n}{n}$, hence $(p q)^2 \mid \binom{2n}{n}$.
  2. **Family 2 ($c = 4$, $n = 4 p q - 1$)**: For primes $3 < p < q$ with $\frac{11}{8} p < q < \frac{3}{2} p$ such that $p q - 1$ is not a power of $2$, applying the unified carry lemma with $(m, k) = (4q, 5)$ for $p$ and $(m, k) = (4p, 2)$ for $q$ gives $p^2 \mid \binom{2n}{n}$ and $q^2 \mid \binom{2n}{n}$. Moreover, since $m = p q - 1$ is even and not a power of $2$, its $2$-adic valuation $a = v_2(m) \ge 1$ is strictly smaller than $b = \lfloor \log_2 m \rfloor$, yielding four strictly increasing binary carry levels $1 < 2 < a + 3 < b + 3$ for $n = 4m + 3$, so $2^4 \mid \binom{2n}{n}$ (`two_pow_four_dvd_centralBinom_of_even_not_pow_two`). By pairwise coprimality, $(4 p q)^2 \mid \binom{2n}{n}$.
- **Finding Valid Prime Pairs from Bertrand's Postulate (`exists_prime_pair_eleven_eighths` and `exists_ge_centralBinom_dvd`)**:
  Since $\left(\frac{11}{8}\right)^2 = \frac{121}{64} < 2$, taking the maximum prime $p$ in $[p_0, \lfloor \frac{11}{8} p_0 \rfloor]$ and a Bertrand prime $s \in (p, 2p)$ via `Nat.exists_prime_lt_and_le_two_mul` guarantees that either $(p, s)$ or $(p_0, s)$ has ratio in $(\frac{11}{8}, 2)$.
  Finally, if $p_1 q_1 - 1 = 2^k$ for a pair in $(\frac{11}{8}, \frac{3}{2})$, modulo-$3$ arithmetic (`two_odd_pow_add_one_mod_three`) forces $k = 2t$ to be even, and a second application of the maximal-prime Bertrand step from $q_1$ produces a pair in $(\frac{11}{8}, 2)$ whose product minus $1$ is strictly trapped between consecutive even powers of $2$ — either in $(2^{2t}, 2^{2t+2})$ or in $(2^{2t+2}, 2^{2t+4})$ — and hence cannot be a power of $2$.

### 2. Erdős Problem 273 (`Erdos273.erdos_273.variants.three`)

- **Selfridge's 12-Modulus Covering System (`selfridgeStrictCoveringNat` and `selfridgeStrictCoveringInt`)**:
  We use the 12 primes $p_i \in \{3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181\}$, whose shifted values $m_i = p_i - 1 \in \{2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180\}$ are distinct divisors of $360$, with residues $r_i \in \{1, 2, 4, 8, 8, 12, 24, 24, 36, 12, 0, 0\}$.
  All odd integers satisfy $n \equiv 1 \pmod 2$ ($i = 0$), and the $180$ even residue classes modulo $360$ are verified via a $12 \times 15$ grid factorization (`selfridge_covers_grid`) with an explicit index selector `selfridgeIdx`.

---

## Verification & Axiom Audit

Verified with `/Users/xcc/Project/justin-sun-prize-lean/check_lean.sh /Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos727_273.lean` (exit code `0`):

```text
'Erdos727.balakram_case_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos727.balakram_case_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos727.exists_ge_centralBinom_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos727.erdos_727.variants.k_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos273.erdos_273.variants.three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos273.erdos_273.variants.three_int' depends on axioms: [propext, Classical.choice, Quot.sound]
```
