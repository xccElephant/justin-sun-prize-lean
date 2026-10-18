# Erdős Problem 124 (`JSP-000131`) — Lean 4 Formalization Report

## 1. Executive Summary

- **Problem:** Erdős Problem 124 (`JSP-000131`, posed by Burr, Erdős, Graham, and Li [BEGL96] and Erdős [Er97]) studies the set
  $$\mathrm{sumsOfDistinctPowers}(d, k) = \left\{ \sum_{i \in s} d^i \;\middle|\; s \subset \mathbb{N}\text{ finite},\ \forall i \in s,\, i \ge k \right\}$$
  of integers whose base-$d$ representation uses only digits in $\{0, 1\}$ and is divisible by $d^k$.
  - **`erdos124.zero` (`@[category research solved, question]`):** If $D$ is a finite set of integers $d \ge 3$ satisfying $\sum_{d \in D} \frac{1}{d - 1} \ge 1$, do all sufficiently large integers belong to $\sum_{d \in D} \mathrm{sumsOfDistinctPowers}(d, 0)$?
  - **`erdos124.converse` (`@[category research solved]`):** Conversely (Pomerance's observation in [BEGL96]), if all sufficiently large integers belong to $\sum_{d \in D} \mathrm{sumsOfDistinctPowers}(d, 0)$, must $\sum_{d \in D} \frac{1}{d - 1} \ge 1$?
- **Formalization Status:** **100% Complete & Kernel-Verified.**
  - File: `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos124.lean`
  - Compiler verification: `/Users/xcc/Project/justin-sun-prize-lean/check_lean.sh /Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos124.lean` exits with code `0` in ~10 seconds.
  - Axiom verification (`#print axioms`):
    ```
    'Erdos124.pow_dvd_of_mem_sumsOfDistinctPowers' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.sum_sumsOfDistinctPowers_subset_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.sumsOfDistinctPowers_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.subset_sum_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.erdos124.zero_all' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.erdos124.zero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.exists_simultaneous_power_window' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.erdos124.converse' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.erdos124.converse_of_k' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.erdos124.eventually_iff_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos124.erdos124.forall_iff_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
    ```
  - Zero `sorry`, zero `admit`, zero custom `axiom` declarations.

---

## 2. Exact Statements Verified (Matching `FormalConjectures/ErdosProblems/124.lean`)

The definition `sumsOfDistinctPowers` and theorems `Erdos124.erdos124.zero` and `Erdos124.erdos124.converse` match `FormalConjectures/ErdosProblems/124.lean` verbatim:

```lean
namespace Erdos124

def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

theorem erdos124.zero :
    ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ →
      ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0

theorem erdos124.converse {D : Finset ℕ} (hD₃ : ∀ d ∈ D, 3 ≤ d)
    (h : ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0) :
    1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹
```

In addition, we prove the stronger universal form `erdos124.zero_all` (that **every** $n \in \mathbb{N}$ belongs to the sumset), the $k$-generalized converse `erdos124.converse_of_k`, and the full equivalences `erdos124.eventually_iff_le_sum` and `erdos124.forall_iff_le_sum`.

---

## 3. Architecture of the Lean 4 Proof (`JspBounties/Erdos124.lean`)

### Part 1: Core Definitions and Structural Lemmas
- `zero_mem_sumsOfDistinctPowers`, `pow_mem_sumsOfDistinctPowers`, `sumsOfDistinctPowers_anti`, `zero_mem_sum_sumsOfDistinctPowers`.
- `pow_dvd_of_mem_sumsOfDistinctPowers`: Every $x \in \mathrm{sumsOfDistinctPowers}(d, k)$ satisfies $d^k \mid x$.
- `sum_sumsOfDistinctPowers_subset_zero`: Pointwise sumset monotonicity $\sum_{d \in D} \mathrm{sumsOfDistinctPowers}(d, k) \subseteq \sum_{d \in D} \mathrm{sumsOfDistinctPowers}(d, 0)$.
- `sumsOfDistinctPowers_zero_eq`: Decomposes $\mathrm{sumsOfDistinctPowers}(d, 0) = \{0, 1\} + \mathrm{sumsOfDistinctPowers}(d, 1)$ according to whether $0 \in s$.

### Part 2: Brown's Completeness Criterion for Finite Weight Systems (`subset_sum_complete`)
- Instead of sorting the infinite multiset $\{d^i \mid d \in D, i \ge 0\}$ and breaking ties, we formulate and prove a tie-free Finset induction lemma:
  - Given any finite set $I : \mathrm{Finset}\ \alpha$ and weight function $w : \alpha \to \mathbb{N}$ such that
    $$\forall a \in I,\quad w(a) \le 1 + \sum_{x \in I,\ w(x) < w(a)} w(x),$$
    every integer $0 \le n \le \sum_{x \in I} w(x)$ is the weight sum of some subset $J \subseteq I$.
  - **Proof:** By induction on $|I|$, peeling off a maximum-weight element $a \in I$ (`I.exists_max_image w`). Because $w(b) \le w(a)$ for all $b \in I' = I \setminus \{a\}$, the strict sub-level sets $\{x \in I' \mid w(x) < w(b)\}$ and $\{x \in I \mid w(x) < w(b)\}$ coincide even when there are ties $w(b) = w(a)$.

### Part 3: Strong Solution of `erdos124.zero` (`pred_le_sum_powers_lt`, `erdos124.zero_all`, `erdos124.zero`)
- For a target $n \in \mathbb{N}$, we work on the finite set $I = \{(d, i) \in D \times \{0, \dots, n\} \mid d^i \le n\}$ with weight $w(d, i) = d^i$.
- For any $q \ge 1$ with $q - 1 \le n$ and each $d \in D$, let $k_d$ be the least exponent such that $q \le d^{k_d}$ (`Nat.find`). Then every $i < k_d$ satisfies $d^i < q \le n + 1$ and $i < d^i \le n$, so $(d, i) \in I$ with $w(d, i) < q$.
- Summing the geometric series over $d \in D$ in $\mathbb{Q}$ yields
  $$\sum_{d \in D} \sum_{i < k_d} d^i = \sum_{d \in D} \frac{d^{k_d} - 1}{d - 1} \ge (q - 1) \sum_{d \in D} \frac{1}{d - 1} \ge q - 1.$$
- Applying this bound both at $q = w(a)$ (verifying Brown's hypothesis) and at $q = n + 1$ (verifying $n \le \sum_{x \in I} w(x)$) immediately gives `erdos124.zero_all` and `erdos124.zero`.

### Part 4: Pomerance's Converse (`exists_simultaneous_power_window`, `erdos124.converse`)
- To prove `erdos124.converse` without auxiliary irrationality case-splits or multi-file scaffolding, we prove a single-pass **Simultaneous Power Window Lemma** (`exists_simultaneous_power_window`):
  - Given $\forall d \in D, 3 \le d$, $E > 1$, and $N_0 \in \mathbb{N}$, define $B = 1 + \sum_{d \in D} \ln d$, $E_1 = (E + 1)/2$, choose $N$ with $\exp(2B/N) \le E_1$, choose $M > \max(N_0, E_1/(E - E_1)) + 1$, and set $S = \ln M + B$ and $\alpha_d = S / \ln d$.
  - By the pigeonhole principle on $\mathrm{Fin}(N^{|D|} + 1) \to (D \to \mathrm{Fin}\ N)$ via $j \mapsto \lfloor \operatorname{fract}(j \alpha_d) N \rfloor_+$, there exist $j_1 < j_2$ such that $m = j_2 - j_1 \ge 1$ and $k_d = \lfloor j_2 \alpha_d \rfloor - \lfloor j_1 \alpha_d \rfloor \ge 0$ satisfy $|m \alpha_d - k_d| < 1/N$.
  - Multiplying by $\ln d$ (using $\alpha_d \ln d = S$) gives $|m S - k_d \ln d| < B / N$ for all $d \in D$.
  - Setting $Y = m S - B / N \ge \ln M$ and $n = \lfloor e^Y \rfloor_+ \ge M \ge N_0$ immediately places every power $d^{k_d} = \exp(k_d \ln d)$ in the window $n \le e^Y < d^{k_d} < e^{Y + 2B/N} \le (n + 1) E_1 \le E n$.
- Combining `exists_simultaneous_power_window` (with $E = (1 + \sigma)/(2\sigma) > 1$ when $\sigma = \sum_{d \in D} (d - 1)^{-1} < 1$) with the geometric series bound `sumsOfDistinctPowers_le_of_lt_pow` yields $n = \sum_{d \in D} g_d < E n \sigma < n$, completing the proof of `erdos124.converse`.
