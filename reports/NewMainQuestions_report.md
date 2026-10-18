# New Main Questions & Solved Variants Formalization Report

## 1. Executive Summary

We inspected the seven candidate files in `reference/formal-conjectures/FormalConjectures/ErdosProblems/` (`44.lean`, `261.lean`, `319.lean`, `413.lean`, `657.lean`, `711.lean`, `1106.lean`) and produced **6 self-contained, zero-`sorry`, zero-`admit`, zero-custom-`axiom` Lean 4 (`v4.33.1`) modules** in `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/`:

| Lean File | Source File | Main Verified Theorems (Zero `sorry`) | `#print axioms` |
| :--- | :--- | :--- | :--- |
| `JspBounties/Erdos261.lean` | `FormalConjectures/ErdosProblems/261.lean` | `erdos_261.variants.borwein_loring`<br>`erdos_261.variants.borwein_loring_property`<br>`erdos_261.parts.i`<br>`hasSum_dyadic_tail`<br>**`erdos_261.variants.two_representations`** | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos657.lean` | `FormalConjectures/ErdosProblems/657.lean` | `sum_four_pow_injective`<br>**`erdos_657.variants.straus`**<br>`isIsoscelesFree_real_iff_no_three_term_ap`<br>`erdos_657_dim_one_of_dim_one_lower` | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos44.lean` | `FormalConjectures/ErdosProblems/44.lean` | `maxSidonSubsetCard_icc_bound`<br>`example_sidon_set`<br>**`greedy_sidon_construction`**<br>`erdos_turan_parabola_sidon`<br>`sidon_set_lower_bound_sqrt_div_three`<br>`sidon_set_lower_bound_of_singer`<br>`erdos_44_empty_start_of_singer` | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos319.lean` | `FormalConjectures/ErdosProblems/319.lean` | `erdos_319_isBigO`<br>`adenwalla_irreducible_of_unit_fraction_sum`<br>`four_mem_erdos319Set`, `five_mem_erdos319Set`<br>`erdos_319_lb_of_croot`<br>`erdos_319_isTheta_of_lb` | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos413.lean` | `FormalConjectures/ErdosProblems/413.lean` | `isBarrier_mul_iff`<br>`erdos_413_parts_ii_iff_linear_omega`<br>`erdos_413_parts_ii_of_lau`<br>`barrier_traps_iterates`<br>`barrier_coalesces_trajectories`<br>`infinite_not_isBarrier_omega`<br>`expProd_eq_one_of_squarefree` | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos711.lean` | `FormalConjectures/ErdosProblems/711.lean` | `exists_isMinimalIntervalLength`<br>`isMinimalIntervalLength_unique`<br>`n_add_one_le_of_hasDivisibleDistinctTuple`<br>`isMinimalIntervalLength_zero`<br>`isMinimalIntervalLength_add_iff_of_dvd`<br>`erdos_711_parts_ii_of_van_doorn` | `[propext, Classical.choice, Quot.sound]` |

---

## 2. Detailed Problem-by-Problem Breakdown

### 2.1 `JspBounties/Erdos261.lean` — Two Distinct Infinite Representations (`erdos_261.variants.two_representations`)
- **Theorem Statement**:
  ```lean
  theorem erdos_261.variants.two_representations : ∃ x : ℚ,
      2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}
  ```
- **Mathematical Proof**:
  - Using the finite telescoping identity $\sum_{i=0}^{m-1} \frac{n + 1 + i}{2^{n + 1 + i}} = \frac{n + 2}{2^n} - \frac{n + m + 2}{2^{n + m}}$ (`sum_range_dyadic`) and the exponential remainder estimate $\frac{n + m + 2}{2^{n + m}} \le \frac{4}{m + 1}$ (`dyadic_tail_remainder_le`), we prove via `hasSum_of_isLUB_of_nonneg` in the order topology of $\mathbb{Q}$ that for every $n \in \mathbb{N}$,
    $$\sum_{i=0}^\infty \frac{n + 1 + i}{2^{n + 1 + i}} = \frac{n + 2}{2^n} \in \mathbb{Q} \quad (\text{`hasSum_dyadic_tail`}).$$
  - Specializing to $n = 4$ and $n = 6$ (combined with $\frac{4}{2^4} = \frac{5}{2^5} + \frac{6}{2^6} = \frac{1}{4}$ and `HasSum.zero_add`), we prove that both strictly increasing sequences
    $$a_0(k) = k + 5 \quad (5, 6, 7, 8, \dots) \qquad \text{and} \qquad a_1(k) = \begin{cases} 4 & k = 0, \\ k + 6 & k \ge 1 \end{cases} \quad (4, 7, 8, 9, \dots)$$
    satisfy `Erdos261InfiniteRepresentation (3 / 8) a`, establishing `2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation (3 / 8) a}`.

### 2.2 `JspBounties/Erdos657.lean` — Straus's Hypercube Construction (`erdos_657.variants.straus`)
- **Theorem Statement**:
  ```lean
  theorem erdos_657.variants.straus (k : ℕ) :
      ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
        distinctDistances A ≤ 2 ^ k - 1
  ```
- **Mathematical Proof**:
  - For each subset $S \subseteq \mathrm{Fin}\,k$, define `strausPoint k S : ℝ^k` with $i$-th coordinate $2^i$ if $i \in S$ and $0$ otherwise.
  - For any $S, T \subseteq \mathrm{Fin}\,k$, $\operatorname{dist}(p_S, p_T)^2 = \sum_{i \in S \triangle T} 4^i$ (`dist_sq_strausPoint`).
  - By comparing the maximum element $m = \max(D_1 \triangle D_2)$ and using $\sum_{j < m} 4^j < 4^m$ (`sum_four_pow_fin_lt`), we prove that the base-$4$ subset-sum map $D \mapsto \sum_{i \in D} 4^i$ is injective on `Finset (Fin k)` (`sum_four_pow_injective`).
  - Consequently, $\operatorname{dist}(p_S, p_T) = \operatorname{dist}(p_U, p_V) \iff S \triangle T = U \triangle V$ (`dist_strausPoint_eq_iff`).
  - This single equivalence immediately gives:
    1. `card_strausSet`: `strausPoint k` is injective, so $|A_k| = 2^k$.
    2. `isIsoscelesFree_strausSet`: if $\operatorname{dist}(p_S, p_T) = \operatorname{dist}(p_T, p_U)$, then $S \triangle T = T \triangle U \implies S = U$, so no three distinct points form an isosceles triangle.
    3. `distinctDistances_strausSet_le`: every off-diagonal distance is determined by the non-empty subset $S \triangle T \in \mathcal{P}(\mathrm{Fin}\,k) \setminus \{\emptyset\}$, so $\mathrm{distinctDistances}(A_k) \le 2^k - 1$.
  - We also prove `isIsoscelesFree_real_iff_no_three_term_ap` (1D isosceles-free sets are precisely 3-AP-free sets) and `erdos_657_dim_one_of_dim_one_lower` (reducing `erdos_657.variants.dim_one` to Dumitrescu's theorem `erdos_657.variants.dim_one_lower`).

### 2.3 `JspBounties/Erdos44.lean` — Greedy & Parabola Sidon Constructions (`greedy_sidon_construction`)
- **Theorem Statements**:
  - `greedy_sidon_construction`: `∀ N ≥ 1, ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3`
  - `erdos_turan_parabola_sidon`: for every odd prime $p$, $A_p = \{2px + (x^2 \bmod p) + 1 \mid x \in \mathrm{Fin}\,p\} \subseteq \{1, \ldots, 2p^2\}$ is a Sidon set of cardinality $p$.
  - `sidon_set_lower_bound_sqrt_div_three`: `∀ N ≥ 1, ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ Real.sqrt N / 3 ≤ A.card`
  - `sidon_set_lower_bound_of_singer` & `erdos_44_empty_start_of_singer`: complete deductions of `sidon_set_lower_bound` and `erdos_44.variants.empty_start` from Singer's projective-plane theorem.
- **Mathematical Proof of `greedy_sidon_construction`**:
  - Let $A \subseteq \{1, \ldots, N\}$ be a Sidon subset of maximum cardinality. By maximality and `Set.IsSidon.insert`, every $x \in \{1, \ldots, N\}$ satisfies either $x \in A$, $2x = a + b$ for some $a \ne b \in A$, or $x + a = b + c$ for some $a \ne b$ and $c \in A$.
  - Defining the single covering map $F : \mathbb{N} \times \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ by
    $$F(a, b, c) = \begin{cases} (a + c) / 2 & \text{if } a = b \text{ and } a \ne c, \\ b + c - a & \text{otherwise}, \end{cases}$$
    every $x \in \{1, \ldots, N\}$ lies in the image of $A \times A \times A$ under $F$ ($F(x,x,x) = x$, $F(a,a,b) = (a+b)/2$, and $F(a,b,c) = b+c-a$), giving $N \le |A \times A \times A| = |A|^3$.

### 2.4 `JspBounties/Erdos319.lean` — Irreducible Signed Unit-Fraction Zero-Sums (`erdos_319.variants.isTheta`)
- **What we proved**:
  1. `erdos_319_isBigO`: unconditional proof that $0 \le c(N) \le N$ and `c =O[atTop] erdos_319.variants.isTheta.answer`.
  2. `adenwalla_irreducible_of_unit_fraction_sum`: for any $B \subseteq \{2, \ldots, N\}$ with $\sum_{n \in B} \frac{1}{n} = 1$, $A = \{1\} \cup B$ with $\delta(1) = -1$ and $\delta(n) = +1$ ($n \ge 2$) is an irreducible signed unit-fraction zero-sum of size $|B| + 1$ (since every non-empty proper subset $A' \subsetneq A$ has strictly positive sum if $1 \notin A'$ and strictly negative sum if $1 \in A'$).
  3. `four_mem_erdos319Set` and `five_mem_erdos319Set`: unconditional lower bounds $c(N) \ge 4$ for $N \ge 6$ (via $\{1, 2, 3, 6\}$) and $c(N) \ge 5$ for $N \ge 42$ (via $\{1, 2, 3, 7, 42\}$).
  4. `erdos_319_lb_of_croot` and `erdos_319_isTheta_of_lb`: complete proof of `erdos_319.variants.isTheta` (`c =Θ[atTop] erdos_319.variants.isTheta.answer`) from `erdos_319.variants.lb` and deduction of `erdos_319.variants.lb` from Croot's [Cr01] unit-fraction theorem.

### 2.5 `JspBounties/Erdos413.lean` & `JspBounties/Erdos711.lean`
- **`JspBounties/Erdos413.lean`**:
  - Proves `isBarrier_mul_iff`, `erdos_413_parts_ii_iff_linear_omega` (equivalence of `erdos_413.parts.ii` with $\omega(n - k) \le C k$), and `erdos_413_parts_ii_of_lau` (deduction from Lau's [La26] bound $\omega(n - k) \le C(\log k + 1)$).
  - Proves Erdős and Graham's [ErGr80, p. 81] trajectory-trapping theorem `barrier_traps_iterates` and `barrier_coalesces_trajectories`.
  - Proves `infinite_not_isBarrier_omega` and `expProd_eq_one_of_squarefree`.
- **`JspBounties/Erdos711.lean`**:
  - Proves `exists_isMinimalIntervalLength`, `isMinimalIntervalLength_unique`, `n_add_one_le_of_hasDivisibleDistinctTuple`, `isMinimalIntervalLength_zero` ($f(n, 0) = n + 1$), `isMinimalIntervalLength_add_iff_of_dvd` (periodicity modulo $\mathrm{lcm}(1, \ldots, n)$), and `erdos_711_parts_ii_of_van_doorn`.
