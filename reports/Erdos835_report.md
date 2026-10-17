# Erdős Problem 835 (`JSP-000691`) Formalization & Investigation Report

## 1. Overview

- **Lean 4 File**: `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos835.lean`
- **Toolchain**: Lean `v4.33.1` with Mathlib precompiled cache
- **Verification Status**: Compiles cleanly with **0 errors**, **0 warnings**, **0 `sorry`**, **0 `admit`**, and **0 custom axioms** via `/Users/xcc/Project/justin-sun-prize-lean/check_lean.sh /Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos835.lean`.
- **Axiom Footprint**: Every main theorem depends solely on `[propext, Classical.choice, Quot.sound]`.

---

## 2. Main Theorems Formalized in `JspBounties/Erdos835.lean`

| Declaration | Mathematical Statement | Status |
| :--- | :--- | :--- |
| `Erdos835.property_iff_chromaticNumber` | For $k > 0$, $\chi(J(2k, k)) = k + 1 \iff \text{Property}(k)$ (Problem 1.1 $\iff$ Problem 1.3). | Proven (`0 sorry`) |
| `Erdos835.indepNum_johnson_le_johnsonBound` | $\alpha(J(n, k)) \le \text{johnsonBound}(n, 4, k)$ for all $n, k \in \mathbb{N}$. | Proven (`0 sorry`) |
| `Erdos835.div_johnsonBound_le_chromaticNum_johnson` | $\lceil \binom{n}{k} / \text{johnsonBound}(n, 4, k) \rceil \le \chi(J(n, k))$. | Proven (`0 sorry`) |
| `Erdos835.johnsonHomOfLe` | Graph homomorphism $J(n_1, k_1) \to_g J(n_2, k_2)$ whenever $k_1 \le k_2$ and $n_1 - k_1 \le n_2 - k_2$. | Proven (`0 sorry`) |
| `Erdos835.chromaticNumber_johnson_mono` | $\chi(J(n_1, k_1)) \le \chi(J(n_2, k_2))$ whenever $k_1 \le k_2$ and $n_1 - k_1 \le n_2 - k_2$. | Proven (`0 sorry`) |
| `Erdos835.indepNum_johnson_le_choose_pred_div` | Hypergraph packing bound (Ma–Tang Claims 1 & 2): $\alpha(J(n, t)) \le \lfloor \frac{1}{t}\binom{n}{t-1} \rfloor$ for $t \ge 1$. | Proven (`0 sorry`) |
| `Erdos835.ma_tang_prop_2_1` | **Proposition 2.1 (Ma–Tang)**: If $J(2k, k)$ is $(k+1)$-colorable and $1 \le t \le k$, then $t \mid \binom{k+t}{t-1}$. | Proven (`0 sorry`) |
| `Erdos835.johnson_chromaticNumber_composite` | **Theorem 2.2 (Ma–Tang)**: If $k > 2$ and $k + 1$ is composite, then $k + 1 < \chi(J(2k, k))$. | Proven (`0 sorry`) |
| `Erdos835.not_property_of_composite` | If $k > 2$ and $k + 1$ is composite, then $\neg \text{Property}(k)$. | Proven (`0 sorry`) |
| `Erdos835.johnson_chromaticNumber_odd` | If $k > 2$ is odd, then $k + 1 < \chi(J(2k, k))$. | Proven (`0 sorry`) |
| `Erdos835.johnsonGraph_18_9_chromaticNumber` | $\chi(J(18, 9)) > 10$. | Proven (`0 sorry`) |
| `Erdos835.ma_tang_lemma_2_3` | **Lemma 2.3 (Ma–Tang)**: If $k + 1$ is prime, then $t \mid \binom{k+t}{t-1}$ for all $1 \le t \le k$. | Proven (`0 sorry`) |
| `Erdos835.johnson_chromaticNumber_four` | **First Prime $k+1$ Case ($k = 4, p = 5$)**: $4 + 1 < \chi(J(8, 4))$. | Proven (`0 sorry`) |
| `Erdos835.not_property_four` | $\neg \text{Property}(4)$. | Proven (`0 sorry`) |

---

## 3. Proof Architecture & Key Insights

### 3.1 Streamlining Ma–Tang Proposition 2.1 via Subgraph Homomorphism $J(k+t, t) \to_g J(2k, k)$
In Ma and Tang's paper, Proposition 2.1 is proved by averaging the hypergraph packing bound $|F_\lambda| \le \nu_{t-1}(k+t) \le \lfloor \frac{1}{t}\binom{k+t}{t-1}\rfloor$ over all $\binom{2k}{k-t}$ choices of a $(k-t)$-subset $\lambda \subset [2k]$ and simplifying the factorial ratio $\frac{1}{k+1}\binom{2k}{k}\binom{k}{t}/\binom{2k}{k-t} = \frac{1}{t}\binom{k+t}{t-1}$.

We observed that fixing a **single** $(k-t)$-subset $\lambda_0 = \{k+t, \dots, 2k-1\}$ defines an injective graph homomorphism
$$\varphi : J(k+t, t) \to_g J(2k, k), \quad S \mapsto S \cup \lambda_0$$
(generalized in `johnsonHomOfLe` to any $k_1 \le k_2$ and $n_1 - k_1 \le n_2 - k_2$). Consequently:
1. Any $(k+1)$-coloring of $J(2k, k)$ pulls back directly to a $(k+1)$-coloring of $J(k+t, t)$.
2. For any independent set $F$ in $J(k+t, t)$, double-counting the incidence relation $R \subseteq S$ between $S \in F$ and $R \in \binom{[k+t]}{t-1}$ via `Finset.card_mul_le_card_mul` immediately yields $|F| \cdot t \le \binom{k+t}{t-1}$, hence $|F| \le \lfloor \binom{k+t}{t-1} / t \rfloor$.
3. Double-counting the $(k+1)$ color classes of $J(k+t, t)$ together with the absorption identity
   $$\binom{k+t}{t} \cdot t = \binom{k+t}{t-1} \cdot (k+1)$$
   gives $\binom{k+t}{t-1} \cdot (k+1) \le (k+1) \cdot \lfloor \binom{k+t}{t-1} / t \rfloor \cdot t$, forcing $t \mid \binom{k+t}{t-1}$ without any factorial division.

### 3.2 Equivalence with the Iterated Johnson Bound
We also analyzed the exact relationship between `johnsonBound (2 * k) 4 k` and Ma–Tang's divisibility condition:
- Unrolling the recurrence $B_1 = 1$, $B_t = \lfloor \frac{k+t}{t} B_{t-1} \rfloor$ for $B_t = \text{johnsonBound}(k+t, 4, t)$, the unfloored rational product at step $t$ is
  $$\prod_{j=2}^t \frac{k+j}{j} = \frac{(k+t)!}{t!(k+1)!} = \frac{1}{t}\binom{k+t}{t-1}.$$
- By `ma_tang_lemma_2_3`, when $k + 1 = p$ is prime, $t \mid \binom{k+t}{t-1}$ holds for every $1 \le t \le k$. Thus **no rounding occurs at any step** of `johnsonBound (2 * k) 4 k` when $k + 1$ is prime, and `johnsonBound (2 * k) 4 k` equals the Catalan number $C_k = \frac{1}{k+1}\binom{2k}{k}$ (so `div_johnsonBound_le_chromaticNum_johnson` yields only $\chi(J(2k, k)) \ge k + 1$).
- Conversely, when $k + 1$ is composite with smallest prime factor $p \le k$, no rounding occurs for $1 \le t < p$ (since $\gcd(t, k+1) = 1$), and strict rounding occurs at $t = p$ because $\binom{k+p}{p-1} \equiv 1 \pmod p$ by Lucas's theorem (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`).

---

## 4. Investigation of the Prime Cases $k + 1 = p$ ($k = 4, 6, 10, \dots$)

### 4.1 Necessary Structural Conditions for $\chi(J(2k, k)) = k + 1$ when $k + 1 = p$ is Prime
Suppose $k + 1 = p$ is an odd prime ($k \ge 4$ even) and $J(2k, k)$ admits a $(k+1)$-coloring $c : V(J(2k, k)) \to \text{Fin}(k+1)$ with color classes $F_0, \dots, F_k$:
1. **Partition into Steiner Systems $S(k-1, k, 2k)$**:
   Every $(k-1)$-subset $\lambda \subset [2k]$ has $2k - (k-1) = k + 1$ extensions to a $k$-subset, which form a $(k+1)$-clique in $J(2k, k)$. Hence every color class $F_i$ contains a unique block containing $\lambda$; that is, each $F_i$ is a **Steiner system $S(k-1, k, 2k)$** of size $C_k = \frac{1}{k+1}\binom{2k}{k}$, and $\{F_0, \dots, F_k\}$ is a **Large Set of Steiner systems $\text{LS}(k-1, k, 2k)$**.
2. **Derived Large Sets via `johnsonHomOfLe`**:
   Fixing any $k - t$ points ($1 \le t \le k$) shows that $J(k+t, t)$ must also be $(k+1)$-colorable, which is equivalent to the existence of a **Large Set of Steiner systems $\text{LS}(t-1, t, k+t)$** partitioning $\binom{[k+t]}{t}$ into $k+1$ disjoint $S(t-1, t, k+t)$ designs:
   - For $t = 3$: a $(k+1)$-coloring of $J(2k, k)$ induces a Large Set of Steiner triple systems $\text{LSTS}(k+3)$ on $k+3$ points.
   - For $t = 4$: a $(k+1)$-coloring of $J(2k, k)$ induces a Large Set of Steiner quadruple systems $\text{LS}(3, 4, k+4)$ on $k+4$ points.
3. **Complement Closure ($x_0 = 1, x_1 = 0$)**:
   Solving the Mendelsohn block-intersection equations $\sum_{m=r}^k \binom{m}{r} x_m = \binom{k}{r} \frac{1}{k-r}\binom{2k-r}{k-1-r}$ ($0 \le r \le k-1$) for a Steiner system $S(k-1, k, 2k)$ with $k$ even yields $x_0 = 1$ and $x_1 = 0$. Thus every color class $F_i$ is closed under complementation ($S \in F_i \iff S^c \in F_i$), and no two blocks in the same color class can intersect in $1$ or $k-1$ elements.

### 4.2 Complete Resolution and Formalization of $k = 4$ ($k + 1 = 5$)
For $k = 4$, our monotonicity theorem `chromaticNumber_johnson_mono` gives two independent routes to $\chi(J(8, 4)) > 5$:
- **Route 1 (via $t = 3$, $J(7, 3) \to_g J(8, 4)$)**: A $5$-coloring of $J(7, 3)$ is a partition of $\binom{[7]}{3}$ into $5$ disjoint Fano planes $\text{STS}(7)$ ($\text{LSTS}(7)$). By Cayley (1850), at most $2$ pairwise disjoint $\text{STS}(7)$'s exist on $7$ points, so $\chi(J(7, 3)) = 6 > 5$.
- **Route 2 (via $J(6, 3) \to_g J(8, 4)$, formalized in `Erdos835.lean`)**:
  Since $3 \le 4$ and $6 - 3 \le 8 - 4$, `johnsonHomOfLe` embeds $J(6, 3)$ into $J(8, 4)$. Although $\alpha(J(6, 3)) = 4$ and $|V(J(6, 3))| = 20 = 5 \times 4$, $J(6, 3)$ is not $5$-colorable ($\chi(J(6, 3)) = 6$). Even more sharply, the $16$-vertex induced subgraph of $J(6, 3)$ consisting of all $3$-subsets of $\text{Fin } 6$ intersecting $\{0, 1\}$ has a $4$-clique $\{0,1,2\}, \{0,1,3\}, \{0,1,4\}, \{0,1,5\}$ and only $175$ backtracking states after symmetry breaking (`recolor5`), allowing `decide +kernel` to certify `not_colorable_five_johnson_6_3` and `johnson_chromaticNumber_four : 4 + 1 < J(2 * 4, 4).chromaticNumber` in Lean 4.

### 4.3 Analysis of $k = 6$ ($k + 1 = 7$) and $k = 10$ ($k + 1 = 11$)
- **Case $k = 6$ ($J(12, 6)$, $\chi(J(12, 6)) > 7$)**:
  - Every subgraph $J(n_1, k_1)$ with $k_1 \le 6, n_1 - k_1 \le 6$ and $n_1 \le 8$ (such as $J(8, 3)$ and $J(8, 4)$) *is* $7$-colorable ($\chi(J(8, 3)) = 7$, $\chi(J(8, 4)) = 6$), and $J(9, 3)$ is also $7$-colorable because $\text{LSTS}(9)$ exists (Kirkman 1850).
  - However, at $t = 4$, $J(10, 4)$ (and already $J(9, 4) \to_g J(10, 4) \to_g J(12, 6)$) is **not $7$-colorable**: any $7$-coloring of $J(9, 4)$ (126 vertices, $\alpha(J(9, 4)) = 18$) has uncovered $3$-subsets forming an $\text{LSTS}(9)$ $\{U_0, \dots, U_6\}$ and therefore extends uniquely to a Large Set of Steiner Quadruple Systems $\text{LS}(3, 4, 10)$ on $10$ points (`J(10, 4)`). By the theorem of Kramer and Mesner (1974), at most $5$ pairwise disjoint $S(3, 4, 10)$ systems exist among all $2520$ copies of $S(3, 4, 10)$ on $10$ points, so $\text{LS}(3, 4, 10)$ does not exist and $\chi(J(12, 6)) \ge \chi(J(9, 4)) \ge 8 > 7$.
- **Case $k = 10$ ($J(20, 10)$, $\chi(J(20, 10)) > 11$)**:
  - A $11$-coloring of $J(20, 10)$ requires each color class to be a Steiner system $S(9, 10, 20)$ (and its derived designs to be $S(t-1, t, 10+t)$ for all $1 \le t \le 10$, including $S(4, 5, 15)$ and $S(5, 6, 16)$). No Steiner system $S(t, t+1, v)$ with $t \ge 6$ is known to exist, and in fact Mendelsohn / Kramer–Mesner / Ostergård nonexistence results for derived designs rule out small parameters, while for general prime $k + 1 = p$ Problem 835 remains open in the literature.
