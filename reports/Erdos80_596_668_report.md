# Formalization Report: Erdős Problems 596 (`JSP-000483`), 668 (`JSP-000542`), and 80 (`80.lean`)

- **File**: `JspBounties/Erdos80_596_668.lean`
- **Toolchain**: `leanprover/lean4:v4.33.1`
- **Mathlib**: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`)
- **Verification**: `./check_lean.sh JspBounties/Erdos80_596_668.lean` (Exit code `0`, zero warnings, zero `sorry`)

---

## 1. Erdős Problem 596 (`JSP-000483`, 0 Competing Real PRs)

### Target Theorem (`FormalConjectures/ErdosProblems/596.lean`)
- `Erdos596.erdos_596.variants.C4_free_countable_escape`:
  ```lean
  theorem erdos_596.variants.C4_free_countable_escape :
      HasCountableRamseyEscape (cycleGraph 4) (cycleGraph 6)
  ```
- **Mathematical Proof**:
  We prove by well-founded transfinite induction on `κ : Cardinal.{0}` (`countable_escape_of_card_le`) that every $C_4$-free graph $H$ on an arbitrary `Type`-valued vertex set $W$ with `#W ≤ κ` admits a countable edge-colouring `d : ℕ → SimpleGraph W` (`H.IsEdgeColouring d`) in which every colour class `d j` is $C_6$-free:
  1. **Base case (`#W ≤ ℵ₀`, `countable_escape_of_le_aleph0`)**:
     When $W$ is countable, `Sym2 W` is countable (`exists_injective_nat (Sym2 W)`), so each unordered pair receives its own distinct colour in `ℕ`. Each colour class `d j` contains at most one edge, and hence cannot contain `cycleGraph 6` (where vertex `0` is incident to two distinct edges `{0, 1}` and `{0, 5}`).
  2. **2-Neighbor Closure (`cl H X`) and Cardinality Preservation (`mk_cl_le`)**:
     For any subset $X \subseteq W$, define `clStep H X` by adjoining all vertices $v \in W$ that have at least two distinct neighbors in $X$, and let `cl H X = ⋃ n : ℕ, clIter H X n`.
     - Any vertex $v \notin \text{cl } H\, X$ has **at most one** neighbor in $\text{cl } H\, X$ (`cl_adj_unique_of_notMem`).
     - Because $H$ is $C_4$-free, two distinct vertices $v_1, v_2 \notin X$ cannot share two distinct neighbors $u_1, u_2 \in X$ (`clStep_diff_unique`). Thus `↥(clStep H X \ X)` injects into `↥X × ↥X`, giving `#(cl H X) ≤ a` whenever `ℵ₀ ≤ a` and `#X ≤ a` (`mk_cl_le`).
  3. **Transfinite Slice Decomposition (`#W > ℵ₀`)**:
     Equip $W$ with a minimal well-order (`Cardinal.exists_ord_eq_type_lt W`) of order type `(#W).ord`, so every initial segment `Iio w` has `#(Iio w) < #W` (`Cardinal.mk_Iio_lt`). For each $v \in W$, define $\alpha(v) = \min \{w \in W \mid v \in \text{cl } H\, (\text{Iic } w)\}$.
     - Every vertex $v \in W$ has **at most one** neighbor $u$ in $H$ with $\alpha(u) < \alpha(v)$ (`hα_uniq`), so the inter-fiber subgraph `d0` (edges with $\alpha(u) \ne \alpha(v)$) is $C_6$-free (`cycleGraph6_free_of_unique_lt_neighbor`: the vertex of any copy of $C_6$ maximizing $\alpha$ would have two distinct neighbors with strictly smaller $\alpha$).
     - Each fiber $F_w = \{v \in W \mid \alpha(v) = w\} \subseteq \text{cl } H\, (\text{Iic } w)$ has cardinality `#(F w) ≤ max ℵ₀ #(Iio w) < #W`. Applying the inductive hypothesis to each induced subgraph `H.induce (F w)` and combining their colourings in colours `j + 1` completes the partition (since $C_6$ is connected, any copy of $C_6$ in `d (j + 1)` lies inside a single fiber `F_{w₀}`).

---

## 2. Erdős Problem 668 (`JSP-000542`, 0 Competing Real PRs)

### Target Theorems (`FormalConjectures/ErdosProblems/668.lean`)
- `Erdos668.erdos_668.variants.four_points`:
  ```lean
  theorem erdos_668.variants.four_points :
      ∃ a b c d : ℝ², dist a b = 1 ∧ dist a c = 1 ∧ dist b c = 1 ∧ dist b d = 1 ∧ dist c d = 1 ∧
        ({a, b, c, d} : Finset ℝ²).card = 4 ∧
        ∀ B : Finset ℝ², B.card = 4 →
          (unitDistNum B = maxUnitDistances 4 ↔ ∃ f : ℝ² ≃ᵢ ℝ², f '' {a, b, c, d} = B)
  ```
- `Erdos668.erdos_668.parts.ii`:
  ```lean
  theorem erdos_668.parts.ii :
      ¬ ∀ n : ℕ, 3 < n → ∃ A B : Finset ℝ², A.card = n ∧ B.card = n ∧
        unitDistNum A = maxUnitDistances n ∧ unitDistNum B = maxUnitDistances n ∧
        ¬ ∃ f : ℝ² ≃ᵢ ℝ², f '' A = B
  ```
- **Mathematical Proof**:
  1. **Standard Unit Diamond**: We construct $a_0 = (1/2, \sqrt{3}/2)$, $b_0 = (0, 0)$, $c_0 = (1, 0)$, $d_0 = (1/2, -\sqrt{3}/2) \in \mathbb{R}^2$, prove `#({a₀, b₀, c₀, d₀}) = 4` (`diamond_card`) and `unitDistNum {a₀, b₀, c₀, d₀} = 5` (`unitDistNum_diamond`), and prove that $a_0$ and $d_0$ are the **only** two points in $\mathbb{R}^2$ at unit distance from both $b_0$ and $c_0$ (`eq_a0_or_d0_of_dist_b0_c0`).
  2. **Explicit Plane Isometries (`isometryOfUnitDist`)**: For any $y, z \in \mathbb{R}^2$ with $\text{dist}(y, z) = 1$, we construct an explicit plane isometry `f : ℝ² ≃ᵢ ℝ²` sending $b_0 \mapsto y$ and $c_0 \mapsto z$.
  3. **Uniqueness & Exact Maximum (`exists_isometry_of_card_four_of_five_le_unitDistNum`, `maxUnitDistances_four`)**: Any 4-element point set $B = \{x_0, x_1, x_2, x_3\} \subset \mathbb{R}^2$ with $\text{unitDistNum } B \ge 5$ has at least 5 of the 6 pairwise distances equal to $1$ (`card_le_sum_ite_six`), so it consists of a unit-distance base pair $\{y, z\}$ and two distinct points $x \ne w$ both at distance $1$ from $y$ and $z$. Pulling back via `isometryOfUnitDist` forces $\{f^{-1}(x), f^{-1}(w)\} = \{a_0, d_0\}$, proving both $f '' \{a_0, b_0, c_0, d_0\} = B$ and $\text{unitDistNum } B = 5$ (whence `maxUnitDistances 4 = 5`).

---

## 3. Erdős Problem 80 (`80.lean`)

### Inspection & Proved Theorems
- In `FormalConjectures/ErdosProblems/80.lean`, `Admissible c G` is defined as `c * (n : ℝ) ^ 2 ≤ #G.edgeFinset ∧ EveryEdgeInTriangle G`, where `EveryEdgeInTriangle G` requires **every** edge of $G$ to lie in at least one triangle.
- We prove in `namespace Erdos80`:
  - `bookNumber_eq_zero_iff`, `bookNumber_bot`, `everyEdgeInTriangle_bot` (the API/test theorems in `80.lean`).
  - `f_eq_zero_of_ge_half`: Proves that $f_c(n) = 0$ for all $c \ge 1/2$ and all $n \in \mathbb{N}$.
  - `one_le_bookNumber_of_everyEdgeInTriangle` and `one_le_f_of_admissible`: Shows why `EveryEdgeInTriangle` forces $f_c(n) \ge 1$ whenever an admissible graph exists for $c > 0, n > 0$ (and why disproving `erdos_80.parts.i` for `Admissible` graphs requires the Fox–Loh 2012 tripartite construction, captured in `erdos_80_parts_i_of_fox_loh`).
  - `unrestricted_erdos_80_parts_i`: Proves that if `EveryEdgeInTriangle` is omitted (`fUnrestricted`), the balanced bipartite graph `bipGraph (2 * k)` has $\ge k^2 \ge \frac{1}{8}(2k)^2$ edges and `bookNumber = 0`, giving `fUnrestricted (1/8) (2*k) = 0` and disproving the unrestricted polynomial lower bound.

---

## 4. Axiom Audit (`#print axioms`)

```
'Erdos596.erdos_596.variants.C4_free_countable_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos668.erdos_668.variants.four_points' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos668.erdos_668.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos80.f_eq_zero_of_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos80.one_le_f_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos80.unrestricted_erdos_80_parts_i' depends on axioms: [propext, Classical.choice, Quot.sound]
```
