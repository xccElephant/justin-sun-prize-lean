# Formalization Report: `JSP-000137` (Erdős Problem 131) & `JSP-000301` (Erdős Problem 365)

## Overview

| Catalog ID | Erdős Problem | Title / Question | Status | Lean 4 File | `sorry` Count |
| :--- | :--- | :--- | :--- | :--- | :---: |
| **`JSP-000137`** | **Erdős 131** | Non-dividing subsets of $\{1, \dots, N\}$ and $F(N) > N^{1/2 - o(1)}$ | Open (exact exponent) / Disproved ($N^{1/2-o(1)}$ question) | `JspBounties/Erdos131.lean` | **0** |
| **`JSP-000301`** | **Erdős 365 (Part i)** | If two consecutive positive integers are powerful, must at least one be a perfect square? | Solved (Disproved: Golomb 1970, Walker 1976) | `JspBounties/Erdos365.lean` | **0** |

Both files compile cleanly under Lean `v4.33.1` via `./check_lean.sh` with targeted Mathlib imports (no umbrella `import Mathlib`) and depend only on the standard foundational axioms `[propext, Classical.choice, Quot.sound]`.

---

## 1. `JSP-000137` — Erdős Problem 131 (`JspBounties/Erdos131.lean`)

### Mathematical Summary
A finite set $A \subseteq \mathbb{N}$ is called **non-dividing** (Property Q in Erdős–Lev–Rauzy–Sándor–Sárközy [ELRSS99]) if no $a \in A$ divides the sum of the elements of any nonempty subset $S \subseteq A \setminus \{a\}$:
$$\forall a \in A,\; \forall \emptyset \neq S \subseteq A \setminus \{a\},\quad a \nmid \sum_{x \in S} x.$$
Let $F(N)$ denote the maximum cardinality of a non-dividing subset $A \subseteq \{1, \dots, N\}$.

- **Erdős, Lev, Rauzy, Sándor, and Sárközy (1999)** proved $N^{1/5} \ll F(N) \le P(N) < 3\sqrt{N} + 1$, where $P(N)$ is the maximum size of a subset of $\{1, \dots, N\}$ satisfying *Property P* (no $a \in A$ divides a nonempty sum of elements of $A$ strictly greater than $a$), and asked whether $F(N) > N^{1/2 - o(1)}$.
- Every non-dividing set is **non-averaging**: if $a \in A$ were the arithmetic mean of a nonempty $S \subseteq A \setminus \{a\}$, then $\sum_{x \in S} x = |S| \cdot a$, so $a \mid \sum_{x \in S} x$.
- **Pham and Zakharov (2024)** proved that any non-averaging subset of $\{1, \dots, N\}$ has cardinality at most $N^{1/4 + o(1)}$, which implies $F(N) \le N^{1/4 + o(1)}$ and refutes $F(N) > N^{1/2 - o(1)}$. Because the exact asymptotic growth rate of $F(N)$ between $\Omega(N^{1/5})$ and $N^{1/4 + o(1)}$ remains open, `JSP-000137` is marked Open in the catalog.

### Formalized Theorems in `JspBounties/Erdos131.lean`
1. **Core Definitions & Extremal API**:
   - `NonDividing`, decidability instance, and `F (N : ℕ) : ℕ`.
   - `exists_card_eq_F`, `card_le_F`, `NonDividing.mono`, `F_le`, `F_mono`, `one_le_F`.
   - `F_small_values`: exact verification of $F(0)=0, F(1)=1, F(2)=1, F(3)=2, F(4)=2, F(5)=2, F(6)=2, F(7)=3$.
2. **Primitivity & Reduction to Non-Averaging Sets**:
   - `NonDividing.not_dvd_of_ne`: every non-dividing set is primitive ($a \nmid b$ for distinct $a, b \in A$).
   - `NonDividing.nonAveraging`: every non-dividing set is non-averaging (`NonAveraging A`).
   - `F_le_H_nonavg`: $F(N) \le H_{\text{nonavg}}(N)$ for all $N \in \mathbb{N}$.
3. **Unconditional Zero-Sum-Free Pigeonhole Bound**:
   - `exists_nested_chain_of_le_card` & `chain_subset_of_le`: constructs a strictly nested chain of subsets $T_0 \subset T_1 \subset \dots \subset T_m \subseteq B$ with $|T_i| = i$.
   - `card_le_of_mem_nonDividing`: for every non-dividing set $A$ and every positive element $a \in A$, $|A| \le a$ (proved via prefix sums modulo $a$ and `Fintype.exists_ne_map_eq_of_card_lt`).
   - `two_mul_F_le` & `F_le_half`: unconditional bound $2 F(N) \le N + 1$, i.e., $F(N) \le (N + 1)/2$ for all $N \ge 1$.
4. **ELRSS Property P & Lower Bound Construction**:
   - `PropertyP`, `P (N : ℕ)`, `NonDividing.propertyP`, and `F_le_P : F N ≤ P N`.
   - `propertyP_Icc_top` & `le_P_of_mul_pred_lt`: proves that whenever $1 \le k \le N$ and $k(k-1) < N$, the top interval $\{N - k + 1, \dots, N\}$ satisfies Property P, yielding $k \le P(N)$.
5. **Asymptotic Refutation of $F(N) > N^{1/2 - o(1)}$**:
   - `erdos_131_of_subSqrtBound`: proves that any sub-square-root bound $F(N) \le N^{\alpha + o(1)}$ with $\alpha < 1/2$ refutes $F(N) > N^{1/2 - o(1)}$.
   - `erdos_131_of_pham_zakharov`: specializes to the Pham–Zakharov exponent $\alpha = 1/4$.

---

## 2. `JSP-000301` — Erdős Problem 365 (`JspBounties/Erdos365.lean`)

### Mathematical Summary
A natural number $n$ is **powerful** (`Nat.Powerful`, or $2$-full) if $p^2 \mid n$ for every prime factor $p \mid n$. Erdős Problem 365 (Part i) / `JSP-000301` asks:
> *If two consecutive positive integers $n$ and $n+1$ are powerful, must at least one of them be a perfect square?*

- **Golomb (1970)** disproved this by exhibiting the consecutive powerful pair:
  $$12167 = 23^3, \qquad 12168 = 2^3 \cdot 3^2 \cdot 13^2 = 2^3 \cdot 39^2,$$
  neither of which is a perfect square.
- **Walker (1976)** proved that there are **infinitely many** consecutive powerful pairs $(n, n+1)$ with neither member a square, obtained from positive integer solutions to $7^3 x^2 - 3^3 y^2 = 1$ (with least solution $x_0 = 376766, y_0 = 1342879$, giving $n_0 = 48689748233307$).
- More generally, for any primes $p, q$ and any solution $(x, y)$ to $p^3 x^2 - q^3 y^2 = 1$, the cubic Pell-type endomorphism
  $$(x', y') = (p^3 x^3 + 3 q^3 x y^2,\; 3 p^3 x^2 y + q^3 y^3)$$
  satisfies the polynomial identity
  $$p^3 (x')^2 - q^3 (y')^2 = (p^3 x^2 - q^3 y^2)^3 = 1,$$
  generating a strictly increasing infinite sequence of solutions and thus infinitely many non-square consecutive powerful pairs $(q^3 y_k^2, p^3 x_k^2)$.

### Formalized Theorems in `JspBounties/Erdos365.lean`
1. **Structural Lemmas for Powerful Numbers and Non-Squares**:
   - `powerful_sq`, `powerful_cube`, `powerful_mul`, and `powerful_cube_mul_sq`: proves that $a^3 b^2$ is powerful for all $a, b \in \mathbb{N}$.
   - `prime_mul_sq_ne_sq` & `not_isSquare_prime_cube_mul_sq`: proves by strong induction (infinite descent) that for any prime $p$ and any $y > 0$, $p^3 y^2$ is never a perfect square.
2. **Golomb's Counterexample & Disproof of `erdos_365.parts.i` (`JSP-000301`)**:
   - `golomb_pair`: proves `Nat.Powerful 12167 ∧ Nat.Powerful 12168 ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare 12168`.
   - `erdos_365.parts.i`: proves `¬ ∀ n : ℕ, 0 < n → Nat.Powerful n → Nat.Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)`.
3. **Walker's (1976) Infinite Family & Parametric Cubic Pell Recurrence**:
   - `pellCubeStep`, `pellCubeSeq`, `pellCubeStep_zmod_identity`, `pellCubeStep_preserves_eq`, `pellCubeSeq_eq`, `pellCubeSeq_pos`, `pellCubeSeq_snd_strictMono`.
   - `parametric_nonSquare_powerful_family`: general theorem producing a strictly increasing infinite sequence of non-square consecutive powerful pairs from any prime pair $(p, q)$ and base solution $p^3 x_0^2 = q^3 y_0^2 + 1$.
   - `walker_base_pair` & `walkerSeq_properties`: Walker's (1976) family $7^3 x^2 - 3^3 y^2 = 1$ starting at $(48689748233307, 48689748233308)$.
   - `golombWalkerSeq_properties`: infinite family $2^3 x^2 - 23^3 y^2 = 1$ starting at Golomb's pair $(12167, 12168)$.
   - `infinite_nonSquare_consecutive_powerful`: proves that `{n : ℕ | 0 < n ∧ Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1)}.Infinite`.
