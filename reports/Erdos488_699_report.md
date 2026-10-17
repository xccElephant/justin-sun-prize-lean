# Erdős Problems 488 (`JSP-000396`) & 699 (`JSP-000570`) Analysis and Lean 4 Formalization Report

## 1. Executive Summary

| Catalog ID | Problem | Status of Conjecture | Counterexamples Found? | Lean 4 Formalization |
| :--- | :--- | :--- | :--- | :--- |
| **`JSP-000396`** | **Erdős Problem 488** | **Open (True in all tested regimes)** | **0** for multiples ($a \mid n$); disproved for the [Er61]/[Er80] non-multiples typo ($a \nmid n$) at $A=\{2,3,5,7\}, n=9, m=13$ | `JspBounties/Erdos488.lean` (0 `sorry`) |
| **`JSP-000570`** | **Erdős Problem 699** | **Open (True up to $n = 10^7$)** | **0** for $p \ge i$; 9 known finite exceptions for the strict $p > i$ strengthening | `JspBounties/Erdos699.lean` (0 `sorry`) |

---

## 2. `JSP-000396`: Erdős Problem 488

### 2.1 Problem Statement and Exact $D$-Scaling Equivalence

For a finite nonempty set $A \subset \mathbb{Z}_{\ge 2}$, let
$$B_A = \{k \ge 1 : \exists a \in A, \, a \mid k\}, \qquad B_A(x) = |B_A \cap [1, x]|.$$
Erdős Problem 488 asks whether for all $m > n \ge \max(A)$,
$$\frac{B_A(m)}{m} < 2 \frac{B_A(n)}{n}.$$

By scaling any finite base set $A_0 \subset \mathbb{Z}_{\ge 1}$ by a large integer $D \ge 2$ ($A = D \cdot A_0$) and taking $n = D(k+1) - 1$ ($k \ge \max(A_0)$) and $m = D y$ ($y \ge k + 1$), we obtain $B_A(n) = B_{A_0}(k)$ and $B_A(m) = B_{A_0}(y)$, so
$$\lim_{D \to \infty} \frac{B_A(m)/m}{B_A(n)/n} = \frac{(k + 1) \, B_{A_0}(y)}{y \, B_{A_0}(k)}.$$
Consequently, Erdős Problem 488 holds for all $(A, n, m)$ if and only if the **strengthened discrete inequality**
$$(n + 1) \, B_A(m) \le 2 m \, B_A(n)$$
holds for all finite nonempty $A \subset \mathbb{Z}_{\ge 2}$ and all $m > n \ge \max(A)$.

### 2.2 Computational Search Findings

- Exhaustive search over all antichains $A \subset \{2, \dots, 17\}$ of size $1 \le |A| \le 4$ and 5,000+ randomized sets $A \subset \{2, \dots, 80\}$ of size up to $15$ found **zero violations** of the strengthened inequality $(n + 1) B_A(m) \le 2 m B_A(n)$.
- The supremum $\frac{(n + 1) B_A(m)}{m B_A(n)} = 2$ is attained at singletons $A = \{a\}$ with $n = 2a - 1$ and $m = 2a$, where $\frac{B_A(m)/m}{B_A(n)/n} = 2 - \frac{1}{a}$.
- For two-element sets $A = \{a, a+1\}$ with $n = 2a - 1, m = 2a + 2$, the ratio reaches $\frac{2a - 1}{a + 1} = 2 - \frac{3}{a + 1}$ (e.g., $A = \{40, 41\}, n = 79, m = 82$ gives $\frac{(n+1) B_A(m)}{m B_A(n)} = \frac{80}{41} \approx 1.9512$).
- **One-step quotient-sieve reduction**: For $a = \max(A)$ with $k = \lfloor n / a \rfloor$, let $Q_a = \{b / \gcd(a, b) : b \in A \setminus \{a\}\}$ and let $U_Q(x)$ be the count of integers in $[1, x]$ coprime to all $q \in Q_a$. Removing $a$ from $A$ subtracts $U_{Q_a}(k)$ from $B_A(n)$ and subtracts $U_{Q_a}(\lfloor m/a \rfloor)$ from $B_A(m)$. For $k \in \{1, 2, 3, 5\}$, the standalone inequality $(k+1) U_Q(Y) \le 2 Y U_Q(k)$ holds for all $Q \subset \{2, \dots, k\}$ and all $Y > k$; for $k = 4$ and $k \ge 6$, oscillation of the unsieved set $U_Q$ can exceed $\frac{2}{k+1}$, explaining why the general case $|A| \ge 3$ with $\max(A) \le n/4$ cannot be proved by greedy single-element stripping alone.

### 2.3 Theorems Formalized in `JspBounties/Erdos488.lean`

All theorems compile with zero `sorry` and depend only on standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. `Erdos488.filter_B_eq_multiplesIn`: Exact equivalence between the `FormalConjectures` filter definition and `multiplesIn A x`.
2. `Erdos488.erdos_488_singleton_strengthened` & `Erdos488.erdos_488_singleton`: Full proof of $(n + 1) B_{\{a\}}(m) \le 2 m B_{\{a\}}(n)$ and the strict rational inequality for all singletons $A = \{a\}$.
3. `Erdos488.erdos_488_sharpness`: Proof that $A = \{a\}, n = 2a - 1, m = 2a$ achieves exact equality $(n + 1) B_{\{a\}}(m) = 2 m B_{\{a\}}(n)$.
4. `Erdos488.erdos_488_pair_nat` & `Erdos488.erdos_488_pair`: Complete proof of Erdős Problem 488 for all two-element sets $A = \{a, b\}$ ($2 \le a < b \le n < m$).
5. `Erdos488.erdos_488_of_two_mem_nat` & `Erdos488.erdos_488_of_two_mem`: Complete proof of Erdős Problem 488 for any finite set $A \subset \mathbb{N}_{\ge 2}$ with $2 \in A$.
6. `Erdos488.erdos_488_insert_gt_half`: Inductive reduction step showing that inserting any $a \in (n/2, n]$ not divisible by elements of $A$ preserves $(n + 1) B_A(m) \le 2 m B_A(n)$.
7. `Erdos488.erdos_488_nonmultiples_false`: Formal disproof of the misprinted [Er61]/[Er80] non-multiples version via $A = \{2, 3, 5, 7\}, n = 9, m = 13$.

---

## 3. `JSP-000570`: Erdős Problem 699

### 3.1 Mathematical Analysis and Kummer Structure of Exceptional Triples

Erdős Problem 699 asks whether for every $1 \le i < j \le n / 2$, there exists a prime $p \ge i$ dividing $\gcd\big(\binom{n}{i}, \binom{n}{j}\big)$. The key algebraic identity is
$$\binom{n}{i} \binom{n - i}{j - i} = \binom{n}{j} \binom{j}{i}.$$

1. **Non-coprimality and $i \in \{1, 2\}$**: If $\gcd\big(\binom{n}{i}, \binom{n}{j}\big) = 1$, the identity forces $\binom{n}{i} \mid \binom{j}{i}$, so $\binom{n}{i} \le \binom{j}{i}$, contradicting strict monotonicity $\binom{j}{i} < \binom{n}{i}$ for $1 \le i \le j < n$. Thus $\gcd\big(\binom{n}{i}, \binom{n}{j}\big) > 1$ always has at least one prime factor $p \ge 2$, which immediately settles Erdős Problem 699 for all $i \in \{1, 2\}$.
2. **Structure of Exceptions to the Strict Inequality ($p > i$)**:
   - **$i = 2, n = 2^k$**: $\binom{2^k}{2} = 2^{k-1}(2^k - 1)$. When $2^k - 1 = p q$ has few prime factors, an integer $j \le 2^{k-1}$ can have base-$p$ and base-$q$ digits bounded by those of $2^k$, yielding $\gcd\big(\binom{2^k}{2}, \binom{2^k}{j}\big) = 2^{k-1}$ at $(16, 2, 6)$, $(512, 2, 147)$, and $(2048, 2, 713)$.
   - **$i = 3, n = 3^k + 1, j = (3^k + 1)/2$**: $\binom{n}{3} = 3^{k-1} \frac{3^{2k} - 1}{2}$. When every prime factor $p > 3$ of $3^{2k} - 1$ gives $n = 3^k + 1$ only even digits in base $p$ (which occurs for $k \in \{2, 3, 5, 7, 13\}$, e.g., when $\frac{3^k + 1}{4}$ and $\frac{3^k - 1}{2}$ are prime or prime powers with even base-$p$ digits), Kummer's theorem prevents $p$ from dividing $\binom{n}{n/2}$, so $\gcd\big(\binom{n}{3}, \binom{n}{n/2}\big) = 4 \cdot 3^{k-1}$, whose largest prime factor is $3 = i$.
   - **$i \ge 4$**: The unique known exception is $(n, i, j) = (28, 5, 14)$, where $\gcd\big(\binom{28}{5}, \binom{28}{14}\big) = 1080 = 2^3 \cdot 3^3 \cdot 5$.

### 3.2 Theorems Formalized in `JspBounties/Erdos699.lean`

All theorems compile with zero `sorry` and depend only on standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. `Erdos699.prime_le_of_dvd_choose`: Any prime dividing $\binom{n}{k}$ ($k \le n$) satisfies $p \le n$.
2. `Erdos699.choose_lt_choose_of_lt`: Strict upper-argument monotonicity $\binom{j}{i} < \binom{n}{i}$ for $1 \le i \le j < n$.
3. `Erdos699.choose_gcd_gt_one`: Erdős–Szekeres (1978) theorem that $\gcd\big(\binom{n}{i}, \binom{n}{j}\big) > 1$ for all $1 \le i \le j < n$.
4. `Erdos699.erdos_699_of_le_two`: Full resolution of Erdős Problem 699 for $i \in \{1, 2\}$ and all $i < j \le n / 2$.
5. `Erdos699.dvd_gcd_choose_of_prime_gt_dvd`: Any prime $p > j$ dividing $\binom{n}{i}$ ($i \le j$) divides $\gcd\big(\binom{n}{i}, \binom{n}{j}\big)$.
6. `Erdos699.erdos_699_of_prime_in_interval`: Any prime $p \in (n - i, n]$ satisfies $p > j > i$ and $p \mid \gcd\big(\binom{n}{i}, \binom{n}{j}\big)$.
7. `Erdos699.erdos_699_succ_of_not_prime`: When $j = i + 1$ is composite, any Sylvester–Schur prime $p > i$ dividing $\binom{n}{i}$ divides $\gcd\big(\binom{n}{i}, \binom{n}{i+1}\big)$.
8. `Erdos699.erdos_szekeres_exceptional_triples` & `Erdos699.mem_exceptions_of_erdos_szekeres_strengthening`: Formal proof that every valid exceptional finset $E$ in `erdos_szekeres_strengthening` must contain $(10, 3, 5)$, $(16, 2, 6)$, $(28, 3, 14)$, and $(28, 5, 14)$.
