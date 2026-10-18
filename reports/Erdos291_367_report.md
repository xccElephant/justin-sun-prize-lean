# Formalization Report: Erdős Problem 291 (`291.lean`) & `JSP-000303` (Erdős Problem 367, `367.lean`)

## Overview

| Catalog ID | Erdős Problem | Title / Question | Status | Lean 4 File | `sorry` Count |
| :--- | :--- | :--- | :--- | :--- | :---: |
| — | **Erdős 291 (Part ii)** | Does $\gcd(a_n, L_n) > 1$ occur for infinitely many $n$, where $\sum_{k=1}^n \frac{1}{k} = \frac{a_n}{L_n}$ and $L_n = \operatorname{lcm}(1, \dots, n)$? | Solved (Steinerberger) | `JspBounties/Erdos291_367.lean` | **0** |
| **`JSP-000303`** | **Erdős 367** | How large can the product $\prod_{n \le m < n+k} B_2(m)$ of the $2$-full parts of consecutive integers be? | Solved ($k \le 2$ upper bound, $k \ge 3$ refutation of $O(n^2)$, and $\Omega(n^2 \log n)$ lower bound) | `JspBounties/Erdos291_367.lean` | **0** |

The file `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos291_367.lean` compiles cleanly under Lean `v4.33.1` via `./check_lean.sh` with targeted Mathlib imports (no umbrella `import Mathlib`) and depends only on the standard foundational axioms `[propext, Classical.choice, Quot.sound]`.

---

## 1. Erdős Problem 291 (`Erdos291` in `JspBounties/Erdos291_367.lean`)

### Mathematical Summary
For $n \ge 1$, let $L_n = \operatorname{lcm}\{1, 2, \dots, n\}$ and define
$$a_n = \sum_{j=1}^n \frac{L_n}{j}, \qquad \text{so that} \qquad \sum_{j=1}^n \frac{1}{j} = \frac{a_n}{L_n}.$$
Erdős Problem 291 asks whether $\gcd(a_n, L_n) = 1$ infinitely often (Part i, open) and whether $\gcd(a_n, L_n) > 1$ infinitely often (Part ii, solved).

For $n_k = 2 \cdot 3^k$ ($k \ge 1$):
1. Since $3 \in \{1, \dots, 2 \cdot 3^k\}$, we immediately have $3 \mid L_{2 \cdot 3^k}$.
2. Since $2 \cdot 3^k \in \{1, \dots, 2 \cdot 3^k\}$, we can write $L_{2 \cdot 3^k} = 2 \cdot 3^k \cdot q$ for some $q \in \mathbb{N}$. Then the two terms $j = 3^k$ and $j = 2 \cdot 3^k$ in $a_{2 \cdot 3^k}$ sum to
   $$\frac{L_{2 \cdot 3^k}}{3^k} + \frac{L_{2 \cdot 3^k}}{2 \cdot 3^k} = 2q + q = 3q,$$
   which is divisible by $3$ **without** needing an upper bound on $\nu_3(L_{2 \cdot 3^k})$.
3. For every other $j \in \{1, \dots, 2 \cdot 3^k\} \setminus \{3^k, 2 \cdot 3^k\}$, we have $3^k \nmid j$. Since $3^k \mid L_{2 \cdot 3^k} = j \cdot (L_{2 \cdot 3^k} / j)$, Euclid's lemma implies $3 \mid (L_{2 \cdot 3^k} / j)$.
4. Summing over all $j \in \{1, \dots, 2 \cdot 3^k\}$ yields $3 \mid a_{2 \cdot 3^k}$, hence $3 \mid \gcd(a_{2 \cdot 3^k}, L_{2 \cdot 3^k})$ and $\gcd(a_{2 \cdot 3^k}, L_{2 \cdot 3^k}) \ge 3 > 1$.

### Formalized Theorems in `Erdos291`
- `L_eval` & `a_eval`: exact verification for $n \in \{1, 2, 3, 4\}$.
- `three_dvd_L_two_mul_pow_three`: $3 \mid L_{2 \cdot 3^k}$ for all $k \ge 1$.
- `three_dvd_div_L_of_ne`: $3 \mid (L_{2 \cdot 3^k} / j)$ for all $j \in [1, 2 \cdot 3^k] \setminus \{3^k, 2 \cdot 3^k\}$.
- `three_dvd_top_two_terms`: $3 \mid \left(L_{2 \cdot 3^k} / 3^k + L_{2 \cdot 3^k} / (2 \cdot 3^k)\right)$.
- `three_dvd_a_two_mul_pow_three` & `three_dvd_gcd_two_mul_pow_three`: $3 \mid \gcd(a_{2 \cdot 3^k}, L_{2 \cdot 3^k})$ for all $k \ge 1$.
- `erdos_291.parts.ii`: `{ n : ℕ | Nat.gcd (a n) (L n) > 1 }.Infinite`.

---

## 2. `JSP-000303` — Erdős Problem 367 (`Erdos367` in `JspBounties/Erdos291_367.lean`)

### Mathematical Summary
Let $B_r(n) = \prod_{p^a \parallel n,\, a \ge r} p^a$ denote the $r$-full part of $n$, and $B_2(n)$ its $2$-full (powerful) part. Erdős and Graham (1980) asked whether $\prod_{n \le m < n+k} B_2(m) = O_k(n^2)$ for every fixed $k \ge 1$.

1. **Upper bound for $k \le 2$ (`erdos_367.variants.k_le_two`)**:
   Since $B_r(m) \mid m$, we have $B_2(m) \le m$ for all $m \ge 1$. Thus for $k \le 2$ and $n \ge 1$,
   $$\prod_{n \le m < n+k} B_2(m) \le n(n+1) \le 4n^2 = O(n^2).$$
2. **Cubic Pell-Triple Construction for $k \ge 3$ (`not_isBigO_of_three_le`, `erdos_367.parts.ii`, and `erdos_367.variants.k_ge_three_lower`)**:
   Define $(a_s, b_s)$ by $(a_0, b_0) = (1, 1)$ and the cubic companion-Pell recurrence
   $$a_{s+1} = a_s(4a_s^2 + 3), \qquad b_{s+1} = b_s(3a_s^2 + 2b_s^2),$$
   corresponding to $(a_s + b_s\sqrt{2}) = (1 + \sqrt{2})^{3^s}$.
   - **Norm invariant**: $2b_s^2 = a_s^2 + 1$ for all $s \ge 0$.
   - **Consecutive triple**: Setting $n_s = 2a_s^2$ and $x_s = 2a_s^2 + 1$, the three consecutive integers are
     $$n_s = 2a_s^2, \qquad n_s + 1 = x_s, \qquad n_s + 2 = (2b_s)^2.$$
   - **3-adic valuation of the middle term**: $x_0 = 3$ and $x_{s+1} = x_s(4x_s^2 - 3)$, so by induction $3^{s+1} \mid x_s$ for all $s \ge 0$.
   - For odd indices $s = 2j + 1$, the square $(3^{j+1})^2 = 3^{2j+2}$ divides $n_s + 1$, the square $a_s^2 = n_s / 2$ divides $n_s$, and $(2b_s)^2 = n_s + 2$ is itself a square. Since $m^2 \mid N \implies m^2 \le B_2(N)$, we obtain
     $$\prod_{m=n_s}^{n_s+2} B_2(m) \ge \frac{n_s}{2} \cdot 3^{2j+2} \cdot (n_s + 2) > \frac{3^{2j+2}}{2} n_s^2.$$
   - Moreover, $3a_s \le 3^{3^s}$, so $n_s = 2a_s^2 \le 3^{2 \cdot 3^s} \le e^{4 \cdot 3^s}$, giving $\log n_s \le 4 \cdot 3^s$ and hence
     $$\prod_{m=n_{2j+1}}^{n_{2j+1}+2} B_2(m) \ge \frac{3}{8} n_{2j+1}^2 \log n_{2j+1}$$
     for all $j \ge 0$.

### Formalized Theorems in `Erdos367`
- `B_pos`, `B_dvd`, `B_le`: $B_r(n) > 0$, $B_r(n) \mid n$, and $B_r(n) \le n$ for $n \ge 1$.
- `pow_dvd_B_of_pow_dvd` & `pow_le_B_of_pow_dvd`: if $r \ge 1$, $n \ne 0$, and $m^r \mid n$, then $m^r \mid B_r(n)$ and $m^r \le B_r(n)$.
- `erdos_367.variants.k_le_two`: for all $k \le 2$, $\prod_{n \le m < n+k} B_2(m) = O(n^2)$.
- `not_isBigO_of_three_le`: for all $k \ge 3$, $\prod_{n \le m < n+k} B_2(m) \ne O(n^2)$.
- `erdos_367.parts.ii`: refutation of $\forall k \ge 1,\; \prod_{n \le m < n+k} B_2(m) = O(n^2)$.
- `erdos_367.variants.k_ge_three_lower`: $\exists c > 0$ such that $\prod_{n \le m < n+3} B_2(m) \ge c \, n^2 \log n$ infinitely often (proved with $c = 3/8$).
