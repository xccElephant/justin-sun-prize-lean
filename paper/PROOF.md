# Complete Elementary Proof of Erdős Problem #983 (`JSP-000816`)

- **Problem**: Erdős Problem #983 (`JSP-000816`, Erdős–Straus 1970 `[Er70b, pp. 138, 140]`)
- **Lean 4 Formalization Author**: Chucheng Xiang (`@xccElephant`)
- **Mathematical Credits**: Erdős–Straus (1970, exact upper bound), Pomerance (1979, symmetric prime inequality), Liam Price & Nat Sothanaphan (2026, semiprime path disproof of Part i)

---

## 1. Problem Statement

For integers $n \ge 2$ and $\pi(n) < k \le n$, let $f(k, n)$ denote the least integer $r$ such that for every subset $A \subseteq \{1, \dots, n\}$ of cardinality $|A| = k$, there exists a set $S$ of $r$ primes such that strictly more than $r$ elements of $A$ have all their prime divisors in $S$ (with $1$ vacuously smooth with respect to every $S$).

In `[Er70b, p. 139, (14)]`, Erdős and Straus proved the universal upper bound
$$f(\pi(n) + 1, n) \le 2\pi(\lfloor\sqrt{n}\rfloor) + 1,$$
and asked (`[Er70b, pp. 138, 140]`; `JSP-000816` / `erdos_983.parts.i`):
> **Question.** Is it true that $2\pi(n^{1/2}) - f(\pi(n) + 1, n) \to \infty$ as $n \to \infty$?

We give a 100% elementary, self-contained proof (using only natural-number and integer arithmetic, with zero real logarithms or analytic number theory) of:
1. **Theorem 1 (`erdos_983.variants.upper_bound`)**: For all $n \in \mathbb{N}$, $f(\pi(n) + 1, n) \le 2\pi(\lfloor\sqrt{n}\rfloor) + 1$.
2. **Theorem 2 (`erdos_983.variants.infinite_exact_equality`)**: There exist infinitely many $n \ge 2$ for which
   $$f(\pi(n) + 1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1.$$
3. **Corollary 3 (`erdos_983.parts.i`)**: $2\pi(n^{1/2}) - f(\pi(n) + 1, n) \not\to \infty$ as $n \to \infty$ (in fact the difference equals $-1$ infinitely often).

---

## 2. Proof of Theorem 1 (Erdős–Straus Upper Bound)

Let $P_{\le} = \{p \le \lfloor\sqrt{n}\rfloor : p \text{ prime}\}$ with $t = |P_{\le}| = \pi(\lfloor\sqrt{n}\rfloor)$, and let $P_{>} = \{q \text{ prime} : \lfloor\sqrt{n}\rfloor < q \le n\}$ with $M = |P_{>}| = \pi(n) - t$.

- **Case 1 ($M \le t + 1$)**: Then $\pi(n) = t + M \le 2t + 1$. Taking $S = P_{\le} \cup P_{>}$ of size $\pi(n)$, every $a \in A \subseteq \{1, \dots, n\}$ is $S$-smooth, giving $|A| = \pi(n) + 1 > \pi(n)$ smooth elements. Hence $f(\pi(n) + 1, n) \le \pi(n) \le 2t + 1$.
- **Case 2 ($M > t + 1$)**: Let $A \subseteq \{1, \dots, n\}$ have $|A| = \pi(n) + 1 = t + M + 1$.
  - **Unique large prime factor**: If $q_1 \ne q_2$ in $P_{>}$ both divide $a \in A$, coprimality gives $q_1 q_2 \mid a$, so $(\lfloor\sqrt{n}\rfloor + 1)^2 \le q_1 q_2 \le a \le n$, impossible.
  - Thus the buckets $B_q = \{a \in A : q \mid a\}$ ($q \in P_{>}$) are pairwise disjoint, and setting $A_0 = \{a \in A : \forall q \in P_{>},\ q \nmid a\}$ partitions $A = A_0 \sqcup \bigsqcup_{q \in P_{>}} B_q$, so
    $$|A_0| + \sum_{q \in P_{>}} |B_q| = t + M + 1.$$
  - Let $P_{\ge 2} = \{q \in P_{>} : |B_q| \ge 2\}$.
    - If $|P_{\ge 2}| \ge t + 1$, choose any $Q \subseteq P_{\ge 2}$ with $|Q| = t + 1$; then $|A_0| + \sum_{q \in Q} |B_q| \ge 2(t + 1) = 2t + 2$.
    - If $|P_{\ge 2}| < t + 1$, extend $P_{\ge 2}$ to a subset $Q \subseteq P_{>}$ of size $|Q| = t + 1$. Every $q \in P_{>} \setminus Q$ has $|B_q| \le 1$, so $\sum_{q \in P_{>} \setminus Q} |B_q| \le M - (t + 1)$, whence $|A_0| + \sum_{q \in Q} |B_q| \ge (t + M + 1) - (M - t - 1) = 2t + 2$.
  - Set $S = P_{\le} \cup Q$. Then $|S| = t + (t + 1) = 2t + 1$, and every $a \in A_0 \sqcup \bigsqcup_{q \in Q} B_q$ has all prime factors in $S$, yielding at least $2t + 2 > 2t + 1$ smooth elements. $\blacksquare$

---

## 3. Pure-$\mathbb{N}$ Proof of Pomerance's Symmetric Prime Inequality

Write $p_0 < p_1 < p_2 < \dots$ for the $0$-indexed primes ($p_0 = 2, p_1 = 3, p_2 = 5, \dots$).

**Lemma 3.1 (Dyadic prime count via central binomials).** *For every integer $u \ge 2$, $2^u \le u(\pi(2^u) + 1)$.*

*Proof.* Put $u = t + 1$ ($t \ge 1$) and $N = 2^t$, so $2N = 2^u$. From Erdős's elementary bound $4^N \le 2N \binom{2N}{N}$ and Kummer's prime-power bound $p^{v_p(\binom{2N}{N})} \le 2N$ for each prime $p \le 2N$, we have
$$2^{2N} = 4^N \le 2N \prod_{p \le 2N} p^{v_p(\binom{2N}{N})} \le 2N \cdot (2N)^{\pi(2N)} = (2N)^{\pi(2N) + 1}.$$
Substituting $2N = 2^u$ gives $2^{2^u} \le 2^{u(\pi(2^u) + 1)}$, so $2^u \le u(\pi(2^u) + 1)$. $\blacksquare$

**Lemma 3.2 (Subexponential growth of $p_m$).** *For any $E, K \in \mathbb{N}$, there exists $B \ge K$ such that $(p_m)^E \cdot 2^K < 2^m$ for all $m > B$.*

*Proof.* Set $u_0 = 12 + E + K$ and $B = \max(K, \pi(2^{u_0}))$. Given $m > B$, let $u$ be the least integer with $m < \pi(2^u)$. Then $u > u_0$ (so $u - 1 \ge 12 + E + K$), $p_m \le 2^u$, and $\pi(2^{u-1}) \le m$. By Lemma 3.1 and $(u-1)^3 < 2^{u-1}$ (valid for all $u - 1 \ge 10$),
$$(u - 1)^3 < 2^{u - 1} \le (u - 1)(\pi(2^{u - 1}) + 1) \le (u - 1)(m + 1) \implies (u - 1)^2 < m + 1.$$
Since $u - 1 \ge 12 + E + K$, we have $E u + K + 1 \le (u - 1)^2 < m + 1$, so $E u + K < m$ and $(p_m)^E \cdot 2^K \le 2^{E u + K} < 2^m$. $\blacksquare$

**Proposition 3.3 (Pomerance, 1979).** *For every $K \ge 2$, there exists $M \ge K$ such that $p_{M - i} p_{M + i} < p_M^2$ for all $1 \le i \le M$.*

*Proof.* Set $E = 2^K p_{K - 1} + 1$. By Bernoulli's inequality $(p_{K-1} + 1)^E \ge p_{K-1}^E + E p_{K-1}^{E-1} > 2^K p_{K-1}^E$, every $m < K$ satisfies $p_m^E \cdot 2^K < p_K^E \cdot 2^m$. Choose $B \ge K$ by Lemma 3.2, and pick $M \in \{0, \dots, B\}$ maximizing the integer quantity $G(m) := p_m^E \cdot 2^{B - m}$. Since $G(a) \le G(b) \iff p_a^E \cdot 2^b \le p_b^E \cdot 2^a$ for $a, b \le B$:
1. $G(m) < G(K) \le G(M)$ for all $m < K$, forcing $M \ge K$;
2. For all $m \in \mathbb{N}$ (both $m \le B$ and $m > B$ via Lemma 3.2), $p_m^E \cdot 2^M \le p_M^E \cdot 2^m$.

Multiplying this inequality at $m = M - i$ and $m = M + i$ ($1 \le i \le M$) yields
$$(p_{M - i} p_{M + i})^E \cdot 2^{2M} \le (p_M^2)^E \cdot 2^{(M - i) + (M + i)} = (p_M^2)^E \cdot 2^{2M},$$
so $p_{M - i} p_{M + i} \le p_M^2$. Equality cannot hold by unique prime factorization since $p_{M - i} < p_M < p_{M + i}$. $\blacksquare$

---

## 4. Proof of Theorem 2 & Corollary 3 (Zigzag Semiprime Path & Bidirectional Injection)

Let $M \ge 2$ satisfy Proposition 3.3, and set $n = p_M^2 - 1$. Then $\lfloor\sqrt{n}\rfloor = p_M - 1$, $\pi(\lfloor\sqrt{n}\rfloor) = M$, and $2\pi(\lfloor\sqrt{n}\rfloor) + 1 = 2M + 1$. Note $2 p_{2M} = p_0 p_{2M} < p_M^2 \implies p_{2M} \le n$.

Order the $2M + 1$ primes $V_{\text{path}} = \{p_0, \dots, p_{2M}\}$ along the zigzag sequence $(v_0, \dots, v_{2M})$ defined by
$$v_{2t} = p_{2M - t} \quad (0 \le t \le M), \qquad v_{2t + 1} = p_t \quad (0 \le t < M).$$
Define the $2M$ adjacent semiprimes $e_j = v_j v_{j + 1}$ ($0 \le j < 2M$).
- For $j = 2t$, $e_j = p_{2M - t} p_t = p_{M - (M - t)} p_{M + (M - t)} < p_M^2$, so $e_j \le n$.
- For $j = 2t + 1$: if $t + 1 = M$, $e_j = p_{M - 1} p_M < p_M^2$; if $t + 1 < M$, $e_j = p_t p_{M + (M - t - 1)} < p_{M - (M - t - 1)} p_{M + (M - t - 1)} < p_M^2$, so $e_j \le n$.
- Since $j \mapsto v_j$ is injective and $\operatorname{primeFactors}(e_j) = \{v_j, v_{j+1}\}$, the $2M$ composite numbers $e_0, \dots, e_{2M - 1}$ are pairwise distinct.

Set
$$A = \{e_0, \dots, e_{2M - 1}\} \sqcup \{v_0, v_{2M}\} \sqcup \big(\{q \le n \text{ prime}\} \setminus V_{\text{path}}\big) \subseteq \{1, \dots, n\}.$$
Then $|A| = 2M + 2 + (\pi(n) - (2M + 1)) = \pi(n) + 1$.

Now let $S$ be any set of $r \le 2M$ primes, and write $S_1 = S \cap V_{\text{path}}$, $S_2 = S \setminus V_{\text{path}}$.
- Every $S$-smooth prime outside $V_{\text{path}}$ lies in $S_2$, contributing at most $|S_2|$ elements.
- Since $|S_1| \le r \le 2M < 2M + 1 = |V_{\text{path}}|$, there exists a missing vertex index $m_0 \in \{0, \dots, 2M\}$ with $v_{m_0} \notin S$. Let $J_S = \{j \in \{0, \dots, 2M\} : v_j \in S\}$, so $|J_S| = |S_1|$ and $m_0 \notin J_S$.
- Every $S$-smooth edge $e_j$ satisfies $j \in J_S$ and $j + 1 \in J_S$; since $m_0 \notin J_S$, either $j < m_0$ (with $1 \le j + 1 < m_0$ and $j + 1 \in J_S$) or $m_0 < j < 2M$ (with $j \in J_S$).
- Partitioning $J_S$ into the four pairwise disjoint sets $J_S \cap \{0\}$, $J_S \cap [1, m_0 - 1]$, $J_S \cap [m_0 + 1, 2M - 1]$, and $J_S \cap \{2M\}$ (note $0 < 2M$) injects:
  - $v_0$ (if smooth) into $J_S \cap \{0\}$;
  - smooth $e_j$ ($j < m_0$) via $j \mapsto j + 1$ into $J_S \cap [1, m_0 - 1]$;
  - smooth $e_j$ ($j > m_0$) via $j \mapsto j$ into $J_S \cap [m_0 + 1, 2M - 1]$;
  - $v_{2M}$ (if smooth) into $J_S \cap \{2M\}$.

Hence at most $|J_S| + |S_2| = |S_1| + |S_2| = r$ elements of $A$ are $S$-smooth. Therefore $f(\pi(n) + 1, n) \ge 2M + 1 = 2\pi(\lfloor\sqrt{n}\rfloor) + 1$. Combined with Theorem 1, equality holds at $n = p_M^2 - 1$ for arbitrarily large $M$, so $2\pi(\lfloor\sqrt{n}\rfloor) - f(\pi(n) + 1, n) = -1$ infinitely often and cannot tend to $+\infty$. $\blacksquare$
