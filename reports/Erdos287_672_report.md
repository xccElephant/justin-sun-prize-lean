# Erdős Problems 287, 672, and 364/365/366 — Computation & Lean 4 Formalization Report

## Overview

| Catalog ID | Erdős Problem | Lean 4 File | Status of Main Conjecture | Formalized Theorems (`0 sorry`, `0 axiom`) |
| :--- | :--- | :--- | :--- | :--- |
| **`JSP-000244`** | Erdős #287 | `JspBounties/Erdos287.lean` | Open in full generality | `erdos_287_best_possible`, `erdos_287_gap_at_least_two` (Erdős 1932), `not_dvd_of_prime_gt_eleven`, `erdos_287_prime_conjecture_implies` |
| **`JSP-000546`** | Erdős #672 | `JspBounties/Erdos672.lean` | Open for general $(k, l)$ | `not_erdos672With_two`, `not_erdos672With_three_two`, `three_term_ap_counterexample_two`, `euler_four_ap_identity`, `erdos_672_four_two_of_d_pow_four_lt`, `erdos_672_four_two_of_sq_le`, `four_consecutive_ne_sq`, `erdos_672_four_two_d_eq_one`, `coprime_middle_terms`, `erdos_672_four_two_primitive_pythagorean` |
| **`JSP-000300` / `0301` / `0302`** | Erdős #364 / #365 / #366 | `JspBounties/Erdos364_366.lean` | #364 Open; #365(i) Solved; #366(3,2) Solved, #366(2,3) Open | `erdos_364_weak`, `no_four_consecutive_full`, `erdos_364_mod_thirtysix_barrier`, `exists_three_full_then_two_full`, `erdos_366_variants_three_two`, `golomb_pair`, `erdos_365_parts_i`, `erdos_366_mod_eight_barrier` |

---

## 1. `JSP-000244` (Erdős Problem 287): Maximum Gap in Unit Fraction Representations of $1$

### 1.1 Mathematical Analysis & Lean 4 Formalization (`JspBounties/Erdos287.lean`)

For any strictly increasing sequence of integers $1 < s_0 < s_1 < \dots < s_{k-1}$ ($k \ge 2$) with $\sum_{i=0}^{k-1} \frac{1}{s_i} = 1$, Erdős Problem 287 asks whether $\max_{0 \le i < k-1} (s_{i+1} - s_i) \ge 3$.

We formalized all three solved/structural results from `FormalConjectures/ErdosProblems/287.lean` completely from first principles:

1. **Tightness (`erdos_287_best_possible`)**:
   $(s_0, s_1, s_2) = (2, 3, 6)$ satisfies $\frac{1}{2} + \frac{1}{3} + \frac{1}{6} = 1$ with $\max_i (s_{i+1} - s_i) = 3$.
2. **Erdős (1932) Lower Bound (`erdos_287_gap_at_least_two`)**:
   $$\max_{0 \le i < k-1} (s_{i+1} - s_i) \ge 2.$$
   *Proof method*: If $\max_i (s_{i+1} - s_i) < 2$, then $s_i = s_0 + i$ is a block of $k \ge 2$ consecutive integers. Defining the $2$-adic valuation `twoVal` and odd part `oddPart` recursively on $\mathbb{N}$, let $r = \max_i v_2(s_i) \ge 1$. If two distinct terms $s_a < s_b$ both had $v_2(s_a) = v_2(s_b) = r$, then $m = 2^r(\text{oddPart}(s_a) + 1)$ would lie in $(s_a, s_b]$ and therefore appear in the consecutive block $s$, but $\text{oddPart}(s_a) + 1$ is even so $v_2(m) \ge r + 1$, a contradiction. Clearing denominators with $M = 2^r \prod_j \text{oddPart}(s_j)$ yields a sum of $(k-1)$ even integers and $1$ odd integer equal to the even integer $M$, a contradiction.
3. **Conditional Reduction to Safe-like Primes (`erdos_287_prime_conjecture_implies`)**:
   If for all $N \ge N_0$ there exists a prime $p \in [N, 2N]$ such that $q = \frac{p+1}{2}$ is also prime, then for all $k \ge 2N_0 + 48$, every unit fraction representation of $1$ satisfies $\max_i (s_{i+1} - s_i) \ge 3$.
   *Proof method*:
   - First we prove the general $q$-adic barrier lemma `not_dvd_of_prime_gt_eleven`: if $q > 11$ is prime and $s_i < 4q$ for all $i$, then $q \nmid s_i$ for all $i$. Indeed, any multiple of $q$ in $s$ must belong to $\{q, 2q, 3q\}$; multiplying $\sum_i \frac{1}{s_i} = 1$ by $6q \prod_{q \nmid s_j} s_j$ and reducing modulo $q$ forces $q \mid C$ where $C = \sum_{q \mid s_i} \frac{6q}{s_i} \in [1, 6+3+2] = [1, 11]$, impossible for $q > 11$.
   - Next we show $s_0 < k$ (from $1 = \sum_i \frac{1}{s_i} < \frac{k}{s_0}$) and $s_0 + (k-1) \le s_{k-1}$, which implies $s_0 \le \lfloor s_{k-1}/2 \rfloor =: N$.
   - Applying the prime hypothesis to $N = \lfloor s_{k-1}/2 \rfloor$ produces primes $p \in [N, 2N - 1]$ and $q = (p+1)/2 > 11$ with $s_{k-1} < 4q < 4p$. By `not_dvd_of_prime_gt_eleven`, neither $p$ nor $p + 1 = 2q$ can appear in $s$. Since $s_0 < p < p+1 \le s_{k-1}$, skipping the two consecutive integers $p, p+1$ forces a gap of at least $(p+2) - (p-1) = 3$.

### 1.2 Computational Verification (`max_gap = 2` Search up to $N = 100,000$)

Using the prime-multiple barrier (`M = \lfloor N/q \rfloor = 1` for any prime $q$, `M = 2` for $q \ge 5$, and `M = 3` for $q = 7$ or $q \ge 13$), any integer $m \le N$ divisible by such a prime $q$ is forbidden from appearing in any sequence $s$ with $\max s_i = N$ and $\sum \frac{1}{s_i} = 1$. Whenever two consecutive integers $(a, a+1)$ are both forbidden, no sequence with $\max(s_{i+1} - s_i) \le 2$ can cross below $a$.
- Across all $N \in [2, 100000]$, **only $6$ values of $N$** ($N \in \{6, 8, 9, 33, 35, 36\}$) have allowed reciprocals above the highest double-barrier summing to $\ge 1$.
- Exact DFS backtracking over all $N \le 40$ confirms **zero solutions** with $\max(s_{i+1} - s_i) \le 2$. Hence Erdős Problem 287 holds unconditionally for all sequences with $s_{k-1} \le 100,000$.

---

## 2. `JSP-000546` (Erdős Problem 672): Products of Arithmetic Progressions as Perfect Powers

### 2.1 Mathematical Analysis & Lean 4 Formalization (`JspBounties/Erdos672.lean`)

1. **Sharpness of $k \ge 4$ (`not_erdos672With_two`, `not_erdos672With_three_two`, `three_term_ap_counterexample_two`)**:
   - For $k = 2$ and every $l \ge 1$, the coprime AP $\{1, 2^l\}$ ($n = 1, d = 2^l - 1$) has product $2^l$, so `¬ Erdos672With 2 l`.
   - For $k = 3$ and $l = 2$, the coprime APs $\{1, 25, 49\}$ ($n = 1, d = 24$) and $\{18, 25, 32\}$ ($n = 18, d = 7$) have products $1 \cdot 25 \cdot 49 = 35^2$ and $18 \cdot 25 \cdot 32 = 120^2$, proving `¬ Erdos672With 3 2`. This explains why `erdos_672` requires $k \ge 4$ and why Obláth's $k = 3$ theorem (`erdos_672.variants.oblath`) only holds for $l \in \{3, 4, 5\}$.
2. **Euler's Identity and $k = 4, l = 2$ Barriers (`euler_four_ap_identity`, `erdos_672_four_two_of_d_pow_four_lt`, `erdos_672_four_two_of_sq_le`, `four_consecutive_ne_sq`, `erdos_672_four_two_d_eq_one`, `erdos_672_four_two_primitive_pythagorean`)**:
   - From $n(n+d)(n+2d)(n+3d) + d^4 = (n^2 + 3nd + d^2)^2$, any square solution $q^2$ satisfies $(n^2+3nd+d^2-1)^2 \ge q^2 = (n^2+3nd+d^2)^2 - d^4$, which is impossible whenever $d^4 + 1 < 2(n^2 + 3nd + d^2)$ (in particular for all $n \ge d^2$, and unconditionally for $d = 1$).
   - Moreover, when $\gcd(n, d) = 1$, any hypothetical solution to $n(n+d)(n+2d)(n+3d) = q^2$ satisfies $\gcd(q, d) = 1$ and $\gcd(n+d, n+2d) = 1$, yielding a primitive Pythagorean triple $(q, d^2, n^2+3nd+d^2)$.

---

## 3. `JSP-000300`, `JSP-000301`, `JSP-000302` (Erdős Problems 364, 365, 366): Consecutive Powerful and $k$-Full Numbers

### 3.1 Mathematical Analysis & Lean 4 Formalization (`JspBounties/Erdos364_366.lean`)

1. **Erdős Problem 364 (`JSP-000300`)**:
   - `erdos_364_weak` & `no_four_consecutive_full`: For any $k \ge 2$, no four consecutive integers can all be $k$-full, because one of any four consecutive integers is $\equiv 2 \pmod 4$.
   - `erdos_364_mod_thirtysix_barrier`: Any triple of consecutive powerful integers $(n, n+1, n+2)$ must avoid $2 \pmod 4$ and $3, 6 \pmod 9$, restricting $n \bmod 36$ to $\{7, 27, 35\}$.
2. **Erdős Problem 365 (`JSP-000301`) & Erdős Problem 366 (`JSP-000302`)**:
   - `exists_three_full_then_two_full`: $(8, 9) = (2^3, 3^2)$ is a consecutive pair where $n$ is $3$-full and $n+1$ is $2$-full.
   - `golomb_pair`, `erdos_366_variants_three_two`, & `erdos_365_parts_i`: Golomb's pair $12167 = 23^3$ ($3$-full, hence $2$-full) and $12168 = 2^3 \cdot 3^2 \cdot 13^2$ ($2$-full) satisfies $110^2 < 12167 < 12168 < 111^2$, so neither is a square. This simultaneously disproves `JSP-000301` (`erdos_365.parts.i`), proves `erdos_366.variants.three_two` ($n = 8$ is not unique), and resolves the $(3\text{-full}, 2\text{-full})$ reading of the ambiguous catalog problem `JSP-000302`.
   - `erdos_366_mod_eight_barrier`: For the open $(2\text{-full}, 3\text{-full})$ direction (`erdos_366`), any solution must satisfy $n \equiv 0, 4, \text{ or } 7 \pmod 8$.
