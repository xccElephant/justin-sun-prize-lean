# Erdős Problems 670 & 602 Formalization Report

## Overview

We provide 100% original, zero-`sorry`, zero-custom-axiom Lean 4 (`v4.33.1`) proofs for **Erdős Problem 670 (`JSP-000544`)** and **Erdős Problem 602 (`JSP-000489`)**.

- **`JspBounties/Erdos670.lean`**:
  - `Erdos670.erdos_670.variants.choose_two` (`@[category textbook]`): For any dimension $d \ge 0$ and any finite set $A \subseteq \mathbb{R}^d$ of $n \neq 2$ points with $1$-separated pairwise distances (`HasSeparatedDistances A`), $\binom{n}{2} \le \operatorname{diam}(A)$.
  - `Erdos670.erdos_670.variants.dim_one` (`@[category research solved, question]`): Erdős's 1997 theorem in dimension $d = 1$: for every $\varepsilon > 0$ and all sufficiently large $n$, any $n$-point set $A \subseteq \mathbb{R}^1$ with $1$-separated pairwise distances satisfies $(1 - \varepsilon)n^2 \le \operatorname{diam}(A)$.
  - `Erdos670.erdos_670.variants.uniform_in_dim_of_ho`: Conditional deduction refuting the dimension-uniform version from Ho's upper-bound construction.

- **`JspBounties/Erdos602.lean`**:
  - `Erdos602.erdos_602.variants.countable_index` (`@[category research solved, question]`): Bernstein's Lemma for countable families of infinite sets (`HasPropertyB ℕ A`), which was previously `sorry` in `FormalConjectures/ErdosProblems/602.lean`.
  - Also includes `bernstein_countable_propertyB`, `erdos_602.variants.disjoint`, `erdos_602.variants.single_set`, `erdos_602.variants.empty_index`, `erdos_602.variants.unique_index`, `erdos_602.variants.two_sets`, and `disjoint_without_infinite_claim.disproof`.

---

## Mathematical Proof Summaries

### 1. Erdős Problem 670 (`JspBounties/Erdos670.lean`)

- **Unified $1$-Separated Family Bounds (`sep_max_ge` and `sep_sum_ge`)**:
  - By induction on $m = |P|$ (erasing the maximizer $x_{\max} \in P$ via `Finset.exists_max_image`), if $f : P \to \mathbb{R}$ satisfies $c \le f(x) \le M$ and $|f(x) - f(y)| \ge 1$ for distinct $x, y \in P$, then $c + m - 1 \le M$.
  - Applying `sep_max_ge` with $c = 0$ and $M = f(x_{\max})$ gives $f(x_{\max}) \ge m - 1$, and inducting over `P.erase x_max` yields $\sum_{x \in P} f(x) \ge \frac{m(m-1)}{2}$ whenever $f \ge 0$.

- **`erdos_670.variants.choose_two`**:
  - For $|A| \le 1$, $\binom{|A|}{2} = 0 \le \operatorname{diam}(A)$.
  - For $n = |A| \ge 3$, every pair of distinct points $x, y \in A$ has a third point $z \in (A \setminus \{x\}) \setminus \{y\}$, giving $1 \le |\operatorname{dist}(x, z) - \operatorname{dist}(y, z)| \le \operatorname{dist}(x, y)$.
  - Indexing the $\binom{n}{2}$ pairs via `stepPairs n n` and applying `sep_max_ge` with $c = 1$ and $M = \operatorname{diam}(A)$ yields $\binom{n}{2} \le \operatorname{diam}(A)$.

- **`erdos_670.variants.dim_one`**:
  - Given $\varepsilon > 0$, choose $k \ge 1$ such that $\varepsilon(k+1) \ge 2$, and take $n \ge k^2 + k + 1$.
  - Project $A \subseteq \mathbb{R}^1$ into $\mathbb{R}$ and sort its elements in strictly increasing order $a_0 < a_1 < \dots < a_{n-1}$ via `Finset.orderEmbOfFin`.
  - Consider the $N = kn - \frac{k(k+1)}{2}$ pairs in `P = stepPairs n k` corresponding to $(i, i + r + 1)$ with $0 \le r < k$ and $0 \le i < n - (r + 1)$.
  - By `sep_sum_ge`, $\sum_{p \in P} f(p) \ge \frac{N(N-1)}{2}$.
  - By the telescoping identity `sum_range_sub_shift_eq`, for each step size $m = r + 1$, $\sum_{i < n - m} (a_{i+m} - a_i) = \sum_{i < m} (a_{n-m+i} - a_i) \le m \operatorname{diam}(A)$, so $\sum_{p \in P} f(p) \le \frac{k(k+1)}{2} \operatorname{diam}(A)$.
  - Combining the two inequalities with the algebraic identity
    $$N(N - 1) - k(k + 1)(1 - \varepsilon)n^2 = k(\varepsilon(k + 1) - 2)n^2 + kn(n - (k^2 + k + 1)) + \frac{k(k+1)(k^2+k+2)}{4} \ge 0$$
    yields $(1 - \varepsilon)n^2 \le \operatorname{diam}(A)$.

### 2. Erdős Problem 602 (`JspBounties/Erdos602.lean`)

- **`erdos_602.variants.countable_index` (Bernstein's Lemma)**:
  - Given any sequence $A : \mathbb{N} \to \operatorname{Set} \alpha$ of infinite sets, we recursively construct a monotone sequence of finite sets $S_n \subseteq \alpha$ (`bernsteinStep`) together with elements $x_n, y_n \in A_n \setminus S_n$ (`bernsteinX`, `bernsteinY`) such that $x_n \neq y_n$ and $S_{n+1} = S_n \cup \{x_n, y_n\}$.
  - By trichotomy on $(i, j)$ and monotonicity of $S_n$, $x_i \neq y_j$ for all $i, j \in \mathbb{N}$.
  - Defining $f(x) = 1$ if $\exists j,\, x = y_j$ and $0$ otherwise ensures $f(x_i) = 0 \neq 1 = f(y_i)$ for every $i \in \mathbb{N}$, so no $A_i$ is monochromatic.

---

## Verification & Axiom Audit

Both files were verified with `./check_lean.sh`:

```text
'Erdos670.erdos_670.variants.choose_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos670.erdos_670.variants.dim_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos670.erdos_670.variants.uniform_in_dim_of_ho' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos602.erdos_602.variants.disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos602.erdos_602.variants.countable_index' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos602.erdos_602.variants.single_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos602.erdos_602.variants.empty_index' depends on axioms: [propext]
'Erdos602.erdos_602.variants.unique_index' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos602.erdos_602.variants.two_sets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos602.disjoint_without_infinite_claim.disproof' depends on axioms: [propext, Classical.choice, Quot.sound]
```
