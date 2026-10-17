# Justin Sun Prize Catalog — Solved + `Lean proof: No` Formalization Report

## 1. Executive Summary

We audited the **20 problems** in the Justin Sun Prize catalog (`reference/awards/problems/catalog-*.md`) marked **`Current status: Solved`** and **`Lean proof: No`** that are **not** present in Boris Alexeev's `plby/lean-proofs` repository (`reference/lean-proofs/src/latest/ErdosProblems/`), cross-referencing both `FormalConjectures/ErdosProblems/` and the catalog metadata (including resolving catalog-to-Erdős index offsets such as `JSP-000403`/`JSP-000404` $\leftrightarrow$ Erdős #503/#504, `JSP-000210`/`JSP-000211` $\leftrightarrow$ Erdős #238/#240, `JSP-000281` $\leftrightarrow$ Erdős #338/#339, `JSP-000301` $\leftrightarrow$ Erdős #365, `JSP-000307` $\leftrightarrow$ Erdős #372, `JSP-000465` $\leftrightarrow$ Erdős #575, and `JSP-000782` $\leftrightarrow$ Erdős #940/#941).

Across **8 standalone Lean 4 modules** in `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/`, we formalized and verified **33 theorems and structural lemmas** with:
- **ZERO `sorry`**
- **ZERO `admit`**
- **ZERO custom `axiom` declarations**
- **Targeted `import Mathlib.*` imports only** (no umbrella `import Mathlib`)
- **Clean `#print axioms` verification** (`[propext, Classical.choice, Quot.sound]`, or `[propext, Quot.sound]`) via `/Users/xcc/Project/justin-sun-prize-lean/check_lean.sh`.

---

## 2. Summary of Verified Lean 4 Modules (`JspBounties/`)

| Lean File | JSP ID(s) / Erdős Problem(s) | Key Verified Theorems (Zero `sorry`) | `#print axioms` |
| :--- | :--- | :--- | :--- |
| `JspBounties/Erdos503.lean` | `JSP-000403` / `JSP-000404`<br>(`FormalConjectures/ErdosProblems/503.lean`) | `erdos_503.variants.R0` ($f(0)=1$)<br>`erdos_503.variants.R1` (`IsGreatest ... 3` in $\mathbb{R}^1$)<br>`kelly_R2_lower_bound` (6-pt centered regular pentagon in $\mathbb{R}^2$)<br>`kelly_R3_lower_bound` (8-pt regular pentagonal bipyramid in $\mathbb{R}^3$)<br>`alweiss_construction` ($\binom{n+1}{2}$-pt 2-distance isosceles set in $\mathbb{R}^n$ for all $n \ge 1$)<br>`erdos_503_exists_isIsosceles_ge_choose`<br>`erdos_503_lower_bound_of_bddAbove` | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos365.lean` | `JSP-000301`<br>(`FormalConjectures/ErdosProblems/365.lean`) | `golomb_pair` ($12167 = 23^3$, $12168 = 2^3 \cdot 3^2 \cdot 13^2$)<br>`erdos_365.parts.i` (complete disproof of `JSP-000301`)<br>`jsp_000301_exists_consecutive_powerful_non_squares` | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos238.lean` | `JSP-000210` / `JSP-000211`<br>(`FormalConjectures/ErdosProblems/238.lean`, Erdős #240) | `two_le_primeGap_of_one_le` ($\mathrm{primeGap}(n) \ge 2$ for $n \ge 1$)<br>`erdos_238_block_pigeonhole` (Erdős 1949 Theorem 3 block-pigeonhole reduction)<br>`erdos_238_run_of_block_bound`<br>`erdos_238_unconditional_of_c2_lt_two` (unconditional for $c_2 < 2$)<br>`erdos_238_small_c1_of_brun_chebyshev`<br>`single_prime_smooth_gap_ge` ($P$-smooth gap divergence) | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos940.lean` | `JSP-000782`<br>(`FormalConjectures/ErdosProblems/940.lean`, Erdős #941) | `Nat.Full.mul`, `Nat.Full.pow_of_le`<br>`Nat.two_full_iff_exists_sq_mul_cube` ($2$-powerful $\iff n = a^2 b^3$)<br>`Erdos940.seven_not_sum_three_powerful` ($7$ is not a sum of $\le 3$ powerful numbers) | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos338.lean` | `JSP-000281`<br>(Erdős #338 & #339) | `erdos_338_bateman` (for all $h \ge 3$, $A_h = \{1\} \cup h\mathbb{Z}_{>0}$ is an order-$h$ basis with no restricted order)<br>`erdos_339_order_two_contains_all_large_odd` (order-2 basis restricted sumset contains all large odds)<br>`erdos_339_order_two_counting_bound` (lower density $\ge 1/2 > 0$) | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos216.lean` | `JSP-000198`<br>(Erdős #216 — Horton sets) | `g_zero_eq` ($g(0) = 0$), `g_three_eq` ($g(3) = 3$)<br>`not_convexIndep_of_fourth_in_hull`, `one_one_mem_convexHull_triangle` ($g(4) \ge 5$)<br>`hortonY_mul_sub_one_lt_pow` ($(c-1)Y_c(k,i) < c^k$)<br>`horton_top_strictly_above_bottom_secant` (Horton's 1983 Observation (g))<br>`card_hortonSet` ($|H_k| = 2^k$) | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos575.lean` | `JSP-000465`<br>(Erdős #575 — OpenAI Ch. 10) | `card_le_one_of_no_K12_no_2K2` ($\mathrm{ex}(n, \{K_{1,2}, 2K_2\}) \le 1$)<br>`matchingGraph_card_and_K12_free` ($\mathrm{ex}(2m, K_{1,2}) \ge m$)<br>`starGraph_card_and_2K2_free` ($\mathrm{ex}(m+1, 2K_2) \ge m$)<br>`unique_common_neighbor_of_C4_free` (Ch. 10 Lemma 3.1(1a))<br>`common_neighbors_coincide_of_C4_C6_free` (Ch. 10 Lemma 3.1(1b))<br>`Z_uv_independent_of_C4_C6_free` (Ch. 10 Lemma 3.1(3)) | `[propext, Classical.choice, Quot.sound]` |
| `JspBounties/Erdos372.lean` | `JSP-000307`<br>(`FormalConjectures/ErdosProblems/372.lean`) | `jsp_000307_least_decreasing_triple` ($n=13$ is the least $n$ with $P^+(n) > P^+(n+1) > P^+(n+2)$)<br>`decreasing_quadruple_317` ($P^+(317) > P^+(318) > P^+(319) > P^+(320)$)<br>`infinite_maxPrimeFac_valley` ($\{n \mid P^+(n) > P^+(n+1) < P^+(n+2)\}$ is infinite)<br>`infinite_maxPrimeFac_gt_succ`, `infinite_maxPrimeFac_lt_succ` | `[propext, Classical.choice, Quot.sound]` |

---

## 3. Detailed Technical Breakdown

### 3.1 `Erdos503.lean` — Isosceles Point Sets in $\mathbb{R}^n$ (`FormalConjectures/ErdosProblems/503.lean`)
- **Problem**: What is the size $f(n)$ of the largest subset $A \subseteq \mathbb{R}^n$ such that every three distinct points from $A$ determine an isosceles triangle (`A.IsIsosceles`)?
- **What we proved**:
  1. **Dimensions $n = 0$ and $n = 1$ (`erdos_503.variants.R0`, `erdos_503.variants.R1`)**:
     We completely resolved $n = 0$ ($f(0) = 1$) and $n = 1$ ($f(1) = 3 = \binom{1+2}{2}$), proving both that $\{-1, 0, 1\} \subset \mathbb{R}^1$ is isosceles of cardinality $3$ and that any 4-element subset $\{x_1 < x_2 < x_3 < x_4\} \subset \mathbb{R}^1$ cannot have all triples isosceles (`card_le_three_of_isIsosceles_R1`).
  2. **Kelly's 6-Point Planar Construction (`kelly_R2_lower_bound`)**:
     Using exact radical coordinates $c_1 = \frac{\sqrt{5}-1}{4}$, $c_2 = -\frac{\sqrt{5}+1}{4}$, $s_1 = \sqrt{\frac{5+\sqrt{5}}{8}}$, $s_2 = \sqrt{\frac{5-\sqrt{5}}{8}}$ for the regular pentagon on the unit circle plus the origin $(0,0) \in \mathbb{R}^2$, we proved that all 5 vertices lie at distance $1$ from $(0,0)$, all 10 pairwise distances among the 5 vertices lie in $\{\sqrt{(5-\sqrt{5})/2}, \sqrt{(5+\sqrt{5})/2}\}$, and via the general spherical center extension lemma `triplewise_isIsosceles_insert_center`, the 6-point set `kellySixPoints` satisfies `kellySixPoints.IsIsosceles ∧ kellySixPoints.ncard = 6`.
  3. **Kelly's 8-Point 3D Construction (`kelly_R3_lower_bound`)**:
     Embedding the 5-vertex unit regular pentagon into the $z = 0$ plane of $\mathbb{R}^3$ and adjoining the 3 axial points $(0,0,0), (0,0,1), (0,0,-1)$, we proved `kellyEightPoints.IsIsosceles ∧ kellyEightPoints.ncard = 8`, establishing the constructive half of `erdos_503.variants.R3`.
  4. **Alweiss's General $\binom{n+1}{2}$ Lower Bound Construction (`alweiss_construction`)**:
     Rather than constructing $\binom{n+1}{2}$ vectors $e_i + e_j$ in $\mathbb{R}^{n+1}$ and constructing an orthogonal projection from the hyperplane $\sum x_i = 2$ onto $\mathbb{R}^n$, we constructed a regular simplex $v_0, \dots, v_n$ **directly in $\mathbb{R}^n$** by taking $v_0, \dots, v_{n-1}$ to be the standard basis vectors $e_0, \dots, e_{n-1}$ and $v_n$ to be the constant vector with coordinate $c = \frac{1 - \sqrt{n+1}}{n}$ (satisfying $(c - 1)^2 + (n - 1)c^2 = 2$). Using the coordinatewise four-point quadratic identity
     $$((x + y) - (z + w))^2 + (x - y)^2 + (z - w)^2 = (x - z)^2 + (x - w)^2 + (y - z)^2 + (y - w)^2,$$
     we proved that for any two distinct 2-element subsets $S, T \in \binom{\mathrm{Fin}(n+1)}{2}$, the pairwise sums $\sum_{a \in S} v_a$ and $\sum_{b \in T} v_b$ have squared distance in $\{2, 4\}$. This simultaneously establishes injectivity (`ncard = (n + 1).choose 2`) and the 2-distance property (`IsIsosceles`), yielding `erdos_503_exists_isIsosceles_ge_choose` and `erdos_503_lower_bound_of_bddAbove`.
- **Remaining gap for `erdos_503.variants.upper_bound` and `R2` upper bound**:
  The upper bound $|A| \le \binom{n+2}{2}$ (Blokhuis 1984, Theorem 7.2.5) requires formalizing Blokhuis's orthogonal decomposition of indecomposable vs. decomposable isosceles sets combined with the Croot–Lev–Pach / Petrov–Pohoata polynomial space dimension bound (already present for 2-distance sets in `reference/lean-proofs/src/latest/ErdosProblems/Erdos502.lean`).

### 3.2 `Erdos365.lean` — Consecutive Powerful Numbers (`JSP-000301`)
- **Problem**: If two consecutive positive integers $n, n+1$ are powerful (`(2).Full`), must at least one of them be a perfect square?
- **What we proved**: Complete, unconditional disproof (`Erdos365.erdos_365.parts.i` and `Erdos365.jsp_000301_exists_consecutive_powerful_non_squares`) via Golomb's 1970 pair $12167 = 23^3$ and $12168 = 2^3 \cdot 3^2 \cdot 13^2$, both lying strictly between $110^2 = 12100$ and $111^2 = 12321$.

### 3.3 `Erdos238.lean` — Consecutive Prime Gaps (`FormalConjectures/ErdosProblems/238.lean` & `JSP-000211`)
- **Problem**: Existence of runs of $> c_1 \log x$ consecutive primes $\le x$ with all adjacent gaps $> c_2$ when $c_1 > 0$ is sufficiently small (`erdos_238.variants.small_c1`), and gap growth of $P$-smooth integers (`JSP-000211`, Erdős #240).
- **What we proved**:
  1. `erdos_238_block_pigeonhole` & `erdos_238_run_of_block_bound`: If the interval $[M, M + k(B+1))$ of prime indices contains at most $B$ indices $j$ with $\mathrm{primeGap}(j) \le c_2$, then one of the $B+1$ blocks $[M + bk, M + (b+1)k)$ is completely free of bad gaps, yielding $k$ consecutive primes $\le x$ with all consecutive gaps $> c_2$.
  2. `erdos_238_unconditional_of_c2_lt_two`: Proves unconditionally that $\mathrm{primeGap}(n) \ge 2$ for all $n \ge 1$ (`two_le_primeGap_of_one_le`), resolving the run existence unconditionally whenever $c_2 < 2$.
  3. `erdos_238_small_c1_of_brun_chebyshev`: Connects the block pigeonhole lemma directly to the exact `Filter` statement of `Erdos238.erdos_238.variants.small_c1`.
  4. `single_prime_smooth_gap_ge`: Formalizes `IsPSmooth P n` for Erdős #240 (`JSP-000211`) and proves $p^{k+1} - p^k > k$ for all primes $p$.

### 3.4 `Erdos940.lean` — Sums of Powerful Numbers (`FormalConjectures/ErdosProblems/940.lean` & `JSP-000782`)
- **Problem**: Density and representation of integers as sums of $r$-powerful numbers (`erdos_940.variants.two`, `erdos_940.variants.three_powerful`).
- **What we proved**:
  1. Complete algebraic API for `Nat.Full k n` (`Full.mul`, `Full.pow_of_le`, `Full.mono`).
  2. **The Classical Structure Theorem (`Nat.two_full_iff_exists_sq_mul_cube`)**: A natural number $n$ is $2$-powerful if and only if $n = a^2 b^3$ for some $a, b \in \mathbb{N}$, proved by strong induction on $n$ via the minimum prime factor $p = \mathrm{minFac}(n)$ and coprime divisibility, without requiring prime-factorization multisets.
  3. **Sharpness of `atTop` in Heath-Brown's Theorem (`Erdos940.seven_not_sum_three_powerful`)**: Proves that $7$ cannot be written as the sum of a multiset of at most three $2$-powerful numbers.

### 3.5 `Erdos338.lean` — Restricted Addition of Additive Bases (`JSP-000281`, Erdős #338 & #339)
- **Problem**: Existence of restricted order for additive bases (#338) and positive lower density of sums of $r$ distinct elements from an order-$r$ additive basis (#339 / `JSP-000281`).
- **What we proved**:
  1. **Bateman's Theorem (`erdos_338_bateman`)**: For every $h \ge 3$, $A_h = \{1\} \cup \{x > 0 : h \mid x\}$ is an asymptotic additive basis of order $h$, yet has no restricted order $t$ for any $t \in \mathbb{N}$ because every finite subset sum of distinct elements of $A_h$ is congruent to $0$ or $1 \pmod h$, missing $2 \pmod h$.
  2. **Erdős #339 (`JSP-000281`) for Order $r = 2$ (`erdos_339_order_two_contains_all_large_odd`, `erdos_339_order_two_counting_bound`)**: Every representation of an odd integer $2k + 1 = a + b$ automatically has $a \ne b$, so for any asymptotic basis $A$ of order $2$ (with $0 \in A$), the restricted sumset `RestrictedExactSumset A 2` contains all sufficiently large odd integers and has lower density $\ge 1/2 > 0$.

### 3.6 `Erdos216.lean` — Empty Convex $k$-Gons and Horton Sets (`JSP-000198`)
- **Problem**: Does every sufficiently large planar point set in general position contain an empty convex $k$-gon? (Disproved for $k \ge 7$ by Horton 1983 `[Ho83]`).
- **What we proved**:
  1. `g_zero_eq` ($g(0) = 0$) and `g_three_eq` ($g(3) = 3$).
  2. `not_convexIndep_of_fourth_in_hull` & `one_one_mem_convexHull_triangle` (witnessing that 4 points in general position need not form a convex 4-gon, since $(1,1) \in \mathrm{convexHull}\{(0,0), (3,0), (0,3)\}$).
  3. **Horton's 1983 Recursive Construction (`hortonY`, `hortonSet`)**: Formalized Horton's base-$c$ digit-reversal sequence $Y_c(k, i)$, proved $|H_k| = 2^k$ (`card_hortonSet`), the even/odd bottom/top identities (`hortonY_two_mul`, `hortonY_two_mul_add_one`), the geometric series bound $(c - 1)Y_c(k, i) < c^k$ (`hortonY_mul_sub_one_lt_pow`), and **Horton's Observation (g) (`horton_top_strictly_above_bottom_secant`)**: for $c \ge 2^{k+1} + 1$, every point of the top half $T_{k+1}$ lies strictly above every secant line through two points of the bottom half $B_{k+1}$.

### 3.7 `Erdos575.lean` — Bipartite Turán Compactness (`JSP-000465`, OpenAI `ten-proofs-oai.pdf` Ch. 10)
- **Problem**: Does every finite family $\mathcal{F}$ of graphs have an extremal number $\mathrm{ex}(n, \mathcal{F})$ within a constant factor of $\mathrm{ex}(n, F)$ for some single member $F \in \mathcal{F}$?
- **What we proved**:
  1. **Complete Proof of the $\{K_{1,2}, 2K_2\}$ Compactness Counterexample (`card_le_one_of_no_K12_no_2K2`, `matchingGraph_card_and_K12_free`, `starGraph_card_and_2K2_free`)**: Any graph avoiding both $K_{1,2}$ and $2K_2$ has at most $1$ edge, whereas matchings have $m$ edges without $K_{1,2}$ and stars have $m$ edges without $2K_2$.
  2. **Complete Proof of Lemma 3.1 of OpenAI `ten-proofs-oai.pdf` Chapter 10**: In any $\{C_4, C_6\}$-free bipartite graph, related vertices in $S$ have a unique common neighbor (`unique_common_neighbor_of_C4_free`), pairwise related triples share the same common neighbor (`common_neighbors_coincide_of_C4_C6_free`), and for any unrelated pair $u \ne v \in S$, the common-relation set $Z_{uv}$ is $R_S$-independent (`Z_uv_independent_of_C4_C6_free`).

### 3.8 `Erdos372.lean` — Decreasing Largest Prime Factors (`JSP-000307`)
- **Problem**: Can three consecutive integers have strictly decreasing largest prime factors $P^+(n) > P^+(n+1) > P^+(n+2)$?
- **What we proved**:
  1. Complete `Nat.maxPrimeFac` API (`maxPrimeFac_dvd`, `le_maxPrimeFac`, `maxPrimeFac_mul`, `maxPrimeFac_pow`).
  2. `jsp_000307_least_decreasing_triple`: Proved that $n = 13$ ($P^+(13) = 13 > P^+(14) = 7 > P^+(15) = 5$) is the **least** natural number satisfying $P^+(n) > P^+(n+1) > P^+(n+2)$, and verified the length-4 decreasing chain at $n = 317$ (`decreasing_quadruple_317`).
  3. `infinite_maxPrimeFac_valley`, `infinite_maxPrimeFac_gt_succ`, `infinite_maxPrimeFac_lt_succ`: Proved unconditionally using $n = 2^k - 1$ ($k \ge 2$) that $P^+(2^k - 1) \ge 3 > 2 = P^+(2^k) < 3 \le P^+(2^k + 1)$, establishing the infinitude of both $P^+(n) > P^+(n+1)$, $P^+(n) < P^+(n+1)$, and valley triples $P^+(n) > P^+(n+1) < P^+(n+2)$.
