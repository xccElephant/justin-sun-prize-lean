# Systematic Bounty Hunter Report

## Executive Summary

We executed a systematic Python-driven scan across all `.lean` files in `reference/formal-conjectures/FormalConjectures/ErdosProblems/` that are **not** present in `reference/lean-proofs/src/latest/ErdosProblems/` (429 Erdős problems total, of which 379–381 correspond to Justin Sun Prize catalog entries currently marked `Current status: Open` and `Lean proof: No`, plus solved entries with `Lean proof: No`).

Following the two bounty-hunting strategies—**Type 1** (recent 2025/2026 elementary solutions and solved parts/variants lacking standalone Lean proofs in `lean-proofs/src/latest/ErdosProblems/`) and **Type 2** (universal statements `∀ ...` refuted by explicit counterexamples or existential statements `∃ ...` proved by explicit witnesses)—we produced and kernel-verified **9 self-contained, zero-`sorry`, zero-`admit`, zero-custom-`axiom` Lean 4 files** in `JspBounties/`:

| # | Erdős Problem | JSP ID | JSP Catalog Status | Lean Proof in Catalog | Bounty Type | File | Main Verified Theorems |
|---|---|---|---|---|---|---|---|
| 1 | **Erdős #131** | `JSP-000137` | `Open` | `No` | Type 1 & 2 | `JspBounties/Erdos131.lean` | `exists_card_eq_F`, `card_le_F`, `F_le`, `F_mono`, `one_le_F`, `F_small_values`, `erdos_131_of_pham_zakharov` |
| 2 | **Erdős #261** | `JSP-000226` | `Open` | `No` | Type 1 & 2 | `JspBounties/Erdos261.lean` | `erdos_261.variants.borwein_loring`, `erdos_261.variants.borwein_loring_property`, `erdos_261.parts.i` |
| 3 | **Erdős #302** | `JSP-000253` | `Open` | `No` | Type 1 & 2 | `JspBounties/Erdos302.lean` | `erdos_302.variants.lower_half`, `erdos_302.variants.lower_seventeen_thirtyseconds`, `erdos_302.parts.ii` |
| 4 | **Erdős #365** | `JSP-000301` | `Solved` | `No` | Type 2 (Counterexample) | `JspBounties/Erdos365.lean` | `golomb_pair`, `erdos_365.parts.i` |
| 5 | **Erdős #366** | `JSP-000302` | `Open` | `No` | Type 2 (Counterexample & Witness) | `JspBounties/Erdos366.lean` | `exists_three_full_then_two_full`, `erdos_366.variants.three_two` |
| 6 | **Erdős #602** | `JSP-000489` | `Open` | `No` | Type 1 & 2 | `JspBounties/Erdos602.lean` | `erdos_602.variants.disjoint`, `erdos_602.variants.two_sets`, `disjoint_without_infinite_claim.disproof` |
| 7 | **Erdős #686** | `JSP-000558` | `Open` | `No` | Type 1 & 2 | `JspBounties/Erdos686.lean` | `erdos_686.variants.four_two`, `erdos_686.variants.nine`, `erdos_686.variants.non_square` |
| 8 | **Erdős #885** | `JSP-000736` | `Open` | `No` | Type 2 (Finite Witnesses) | `JspBounties/Erdos885.lean` | `erdos_885.variants.k_eq_2`, `erdos_885.variants.k_eq_3`, `erdos_885.variants.k_eq_4` |
| 9 | **Erdős #949** | `JSP-000789` | `Open` | `No` | Type 1 & 2 | `JspBounties/Erdos949.lean` | `erdos_949.variants.sidon` |
| 10 | **Erdős #1063** | `JSP-000881` | `Open` | `No` | Type 2 (Exact Thresholds) | `JspBounties/Erdos1063.lean` | `erdos_1063.variants.small_values` |
| 11 | **Erdős #1209** | `JSP-001014` | `Open` | `No` | Type 1 & 2 (Counterexample Sequences) | `JspBounties/Erdos1209.lean` | `erdos_1209.parts.i`, `erdos_1209.parts.ii` |

*(Note: All 10 files above—9 primary targets plus `Erdos1063.lean`—compile cleanly with `./check_lean.sh` using targeted `Mathlib.*` imports, zero `sorry`/`admit`, and depend only on standard Lean axioms `[propext, Classical.choice, Quot.sound]`.)*

---

## Detailed Problem-by-Problem Breakdown

### 1. Erdős Problem #261 (`JSP-000226`) — `JspBounties/Erdos261.lean`
- **Catalog Entry**: `JSP-000226` (*Determine how binary-weighted terms can be decomposed as finite or infinite sums of distinct terms of the same form*, `Current status: Open`, `Lean proof: No`).
- **Mathematical Content**:
  - **Part (i)** (`erdos_261.parts.i`) asks whether there exist infinitely many positive integers $n$ such that
    $$\frac{n}{2^n} = \sum_{k=1}^t \frac{a_k}{2^{a_k}}$$
    for some $t \ge 2$ and pairwise distinct positive integers $a_1, \dots, a_t$.
  - Using the explicit telescoping identity
    $$\sum_{i=0}^{m-1} \frac{n + 1 + i}{2^{n + 1 + i}} = \frac{n + 2}{2^n} - \frac{n + m + 2}{2^{n + m}},$$
    we prove Borwein and Loring's theorem (`erdos_261.variants.borwein_loring` and `erdos_261.variants.borwein_loring_property`): for every $m \ge 2$, setting $n_m = 2^{m+1} - m - 2$ yields
    $$\frac{n_m}{2^{n_m}} = \sum_{k = n_m + 1}^{n_m + m} \frac{k}{2^k}.$$
  - Since $m \mapsto 2^{m+1} - m - 2$ is strictly increasing on $[2, \infty)$, this provides an infinite family of positive integers satisfying `Erdos261Prop`, proving `erdos_261.parts.i` unconditionally.
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 2. Erdős Problem #302 (`JSP-000253`) — `JspBounties/Erdos302.lean`
- **Catalog Entry**: `JSP-000253` (*How large can a subset of an integer interval be if no element's reciprocal is the sum of two other distinct reciprocals?*, `Current status: Open`, `Lean proof: No`).
- **Mathematical Content**:
  - Let $f(N)$ be the maximum cardinality of a subset $A \subseteq \{1, \dots, N\}$ with no distinct $a, b, c \in A$ satisfying $\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$.
  - **Part (ii)** (`erdos_302.parts.ii`) asks whether $f(N) = (\frac{1}{2} + o(1))N$, i.e., whether $f(N)/N \to 1/2$.
  - We first prove the $(1/2 - o(1))N$ lower bound (`erdos_302.variants.lower_half`) using odd integers in $[1, N]$.
  - We then construct an explicit triple-free subset `seventeenThirtySecondsSet N` consisting of all odd integers in $[1, N]$ together with all integers $x \in [N/2 + 1, N]$ satisfying $x \equiv 4 \pmod{16}$:
    - If $a$ is odd, then in $bc = a(b+c)$, modulo $2$ and modulo $16$ arithmetic rules out all combinations of odd and $\equiv 4 \pmod{16}$ elements for $b, c$ (`(4 * 4) % 16 = 0` while `(a * (4 + 4)) % 16 = 8`).
    - If $a \in [N/2 + 1, N]$, then $b, c \le N < 2a$, so $(b - a)(c - a) < a^2$, contradicting $bc = a(b+c) \iff (b-a)(c-a) = a^2$.
  - This proves $f(N) \ge (\frac{17}{32} - \varepsilon)N$ for all large $N$ (`erdos_302.variants.lower_seventeen_thirtyseconds`), which strictly exceeds $\frac{1}{2}N$ and unconditionally refutes $\lim_{N\to\infty} f(N)/N = 1/2$ (`erdos_302.parts.ii`).
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 3. Erdős Problem #365 (`JSP-000301`) — `JspBounties/Erdos365.lean`
- **Catalog Entry**: `JSP-000301` (*If two consecutive positive integers are powerful, must one be a square, and how many such pairs occur up to x?*, `Current status: Solved`, `Lean proof: No`).
- **Mathematical Content**:
  - **Part (i)** (`erdos_365.parts.i`) asks whether every pair of consecutive positive powerful numbers $n, n+1$ has at least one square.
  - We prove Golomb's counterexample (`golomb_pair`): $12167 = 23^3$ and $12168 = 2^3 \cdot 3^2 \cdot 13^2$ are both powerful ($2$-full), and since $110^2 = 12100 < 12167 < 12168 < 12321 = 111^2$, neither is a square. This proves `erdos_365.parts.i`.
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 4. Erdős Problem #366 (`JSP-000302`) — `JspBounties/Erdos366.lean`
- **Catalog Entry**: `JSP-000302` (*ambiguous statement* [consecutive $2$-full and $3$-full integers], `Current status: Open`, `Lean proof: No`).
- **Mathematical Content**:
  - We prove `exists_three_full_then_two_full` (witnessed by $n = 8$, where $8 = 2^3$ is $3$-full and $9 = 3^2$ is $2$-full) and refute Erdős and Graham's uniqueness question `erdos_366.variants.three_two` ($\neg \forall n > 0, \text{Full } 3\, n \land \text{Full } 2\, (n+1) \to n = 8$) using $n = 12167 = 23^3$.
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 5. Erdős Problem #602 (`JSP-000489`) — `JspBounties/Erdos602.lean`
- **Catalog Entry**: `JSP-000489` (*Property B*, `Current status: Open`, `Lean proof: No`).
- **Mathematical Content**:
  - We prove `erdos_602.variants.disjoint` (every pairwise disjoint family of infinite sets has Property B), `erdos_602.variants.two_sets` (every pair of infinite sets with finite intersection of size $\neq 1$ has Property B), and `disjoint_without_infinite_claim.disproof` (counterexample with singletons showing the infinite-set hypothesis is essential).
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 6. Erdős Problem #686 (`JSP-000558`) — `JspBounties/Erdos686.lean`
- **Catalog Entry**: `JSP-000558` (*Can every integer at least two be a ratio of products of two disjoint equal-length blocks of consecutive integers?*, `Current status: Open`, `Lean proof: No`).
- **Mathematical Content**:
  - We prove `erdos_686.variants.four_two` ($4$ cannot be represented with block length $k = 2$), `erdos_686.variants.nine` ($9$ is represented with $k = 3, n = 11, m = 25$), and the general theorem `erdos_686.variants.non_square`: every non-square integer $N \ge 2$ can be written as
    $$N = \frac{\prod_{i=1}^k (m+i)}{\prod_{i=1}^k (n+i)}$$
    with $k = 2$ and $m \ge n + 2$.
  - Our proof of `erdos_686.variants.non_square` uses `Pell.exists_of_not_isSquare` for $d = 4N$: given a nontrivial solution $X^2 - 4NY^2 = 1$ with $X, Y \ge 1$, passing to the doubled Pell solution $Y' = 2XY \ge 2$ and $S' = 4NY^2 \ge 1$ gives $S'(S'+1) = 4NY^2(4NY^2+1) = 4NY^2 X^2 = N(Y')^2$, so $n = Y' + S' - 1$ and $m = NY' + S' - 1$ satisfy $m \ge n + 2$ and $N(n+1)(n+2) = (m+1)(m+2)$.
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 7. Erdős Problem #885 (`JSP-000736`) — `JspBounties/Erdos885.lean`
- **Catalog Entry**: `JSP-000736` (*Can arbitrarily many integers share at least that many common factor differences?*, `Current status: Open`, `Lean proof: No`).
- **Mathematical Content**:
  - For $n \ge 1$, $D(n) = \{|a - b| : n = ab\}$ is the factor-difference set of $n$.
  - We prove the solved existential cases $k = 2$ (`erdos_885.variants.k_eq_2`, Erdős–Rosenfeld 1997), $k = 3$ (`erdos_885.variants.k_eq_3`, Jiménez-Urroz 1999), and $k = 4$ (`erdos_885.variants.k_eq_4`, Bremner 2019), exhibiting explicit finite sets $Ns \subset \mathbb{N}$ of size $k$ whose factor-difference sets share at least $k$ common differences $\{5040, 27720, 68880, 164976\}$.
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 8. Erdős Problem #949 (`JSP-000789`) — `JspBounties/Erdos949.lean`
- **Catalog Entry**: `JSP-000789` (*If a real set is sum-free, does its complement contain a continuum-sized subset whose pairwise sums also avoid the set?*, `Current status: Open`, `Lean proof: No`).
- **Mathematical Content**:
  - We prove the Sidon-set variant `erdos_949.variants.sidon`: for every Sidon set $S \subseteq \mathbb{R}$, there exists $A \subseteq \mathbb{R} \setminus S$ of cardinality `#A = 𝔠` such that $A + A \subseteq \mathbb{R} \setminus S$.
  - The proof splits into `#S < 𝔠` (handled via Zorn's lemma on subsets $A \subseteq S^c$ with $A + A \subseteq S^c$ and cardinal arithmetic) and `#S = 𝔠` (handled by taking $a \in S \setminus \{0\}$ and $A = ((S \setminus \{a\}) - a/2) \setminus S$).
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 9. Erdős Problem #1209 (`JSP-001014`) — `JspBounties/Erdos1209.lean`
- **Catalog Entry**: `JSP-001014` (*Can a rapidly growing integer sequence admit infinitely many shifts making all shifted terms prime, or squarefree?*, `Current status: Open`, `Lean proof: No`).
- **Mathematical Content**:
  - **Part (i)** (`erdos_1209.parts.i`): Disproves that for sufficiently fast-growing $a_k$, the existence of $n$ with all $n + a_k$ prime forces infinitely many such $n$. For any growth function $f : \mathbb{N} \to \mathbb{N}$, we use Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`) to construct a strictly increasing sequence of primes $a_k \ge f(k)$ such that $k + a_k$ is composite for every $k \ge 1$. Then $n = 0$ makes all $0 + a_k = a_k$ prime, whereas no $n \ge 1$ works.
  - **Part (ii)** (`erdos_1209.parts.ii`): Disproves the analogous statement for squarefree shifts $n + a_k$, choosing primes $a_k \equiv -k \pmod{q_k^2}$ so that $q_k^2 \mid k + a_k$ for all $k \ge 1$ while $0 + a_k = a_k$ is prime (hence squarefree).
- **Axioms**: `[propext, Classical.choice, Quot.sound]`.

### 10. Erdős Problem #131 (`JSP-000137`) & Erdős Problem #1063 (`JSP-000881`)
- **`JspBounties/Erdos131.lean` (`JSP-000137`)**: Formalizes the non-dividing set function $F(N)$, proves attainment (`exists_card_eq_F`), monotonicity (`F_mono`), bounds (`card_le_F`, `F_le`, `one_le_F`), exact small values $F(1)=1, F(2)=1, F(3)=2, F(4)=2, F(5)=2$ (`F_small_values`), and the reduction of the negative answer `erdos_131` to the Pham–Zakharov bound (`erdos_131_of_pham_zakharov`).
- **`JspBounties/Erdos1063.lean` (`JSP-000881`)**: Formalizes the Erdős–Selfridge binomial divisibility threshold $n_k$ and proves `erdos_1063.variants.small_values`: $n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12$.
