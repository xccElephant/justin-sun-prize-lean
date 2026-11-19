# Elementary Spectral-Free Formalization of Chvátal's Conjecture (`Erdős #701` / `JSP-000571`)

## 1. Problem Statement and Formulations

In `[Ch74, pp. 61–66]` (and featured by Paul Erdős in `[Er81]` / `erdosproblems.com/701`), Václav Chvátal conjectured:

> **Chvátal's Conjecture (`JSP-000571`)**: *Let $X$ be a finite set and let $\mathcal{D} \subseteq 2^X$ be a hereditary set family (a downset: whenever $A \in \mathcal{D}$ and $B \subseteq A$, one has $B \in \mathcal{D}$). Then there exists an element $x_0 \in X$ such that every pairwise-intersecting subfamily $\mathcal{I} \subseteq \mathcal{D}$ satisfies*
> $$|\mathcal{I}| \le |\{A \in \mathcal{D} : x_0 \in A\}|.$$

*(Note: Finiteness of the ground set $X$ is essential; for infinite ground sets, ultrafilter / cofinite counterexamples exist, and both Chvátal `[Ch74]` and `FormalConjectures/ErdosProblems/701.lean` formulate the conjecture on a finite ground type `[Fintype X]`.)*

In September 2026, Chvátal's 54-year-old conjecture was resolved mathematically in three preprints:
1. **Fan Chang, Hong Liu, and Miao Liu** ([`arXiv:2609.19123`](https://arxiv.org/abs/2609.19123), 16 September 2026), via a sharp correlation inequality for increasing Boolean functions;
2. **Peter Keevash** ([`arXiv:2609.23595`](https://arxiv.org/abs/2609.23595), 20 September 2026), by proving Kahn's flow conjecture;
3. **David Ellis, Yuval Filmus, and Ehud Friedgut** ([`arXiv:2609.28404`](https://arxiv.org/abs/2609.28404), 23 September 2026), via a Fourier-analytic convolution operator on $2^X$.

---

## 2. Self-Contained Spectral-Library-Free Proof (`Erdos701.lean`)

To formalize the full theorem cleanly in Lean 4 (`v4.33.1`) with surgical `Mathlib.*` imports and **zero** matrix-eigenvalue or spectral-decomposition dependencies, we replace the spectral trace/rank machinery of `arXiv:2609.28404` with three elementary components:

### Step 1: Physical-Space Boolean Characters & Parseval (`boolChar`, `sum_boolChar_powerset`, `bool_parseval`)

For $S, T \subseteq X$ (`Finset X`), define the Walsh–Fourier character $\chi_S(T) = (-1)^{|S \cap T|}$. Using $(S \triangle R) \cap T = (S \cap T) \triangle (R \cap T)$, we prove character multiplicativity $\chi_{S \triangle R}(T) = \chi_S(T)\chi_R(T)$ (`boolChar_symmDiff_left`) and exact powerset orthogonality (`sum_boolChar_powerset`): for every $M, B \subseteq X$,
$$\sum_{C \subseteq M} \chi_B(C) = \begin{cases} 2^{|M|} & \text{if } B \cap M = \emptyset, \\ 0 & \text{otherwise.} \end{cases}$$
Specializing to $M = X$ yields Parseval's identity (`bool_parseval`): for $\widehat{f}(S) = 2^{-|X|} \sum_{T \subseteq X} f(T)\chi_S(T)$,
$$\sum_{S \subseteq X} \widehat{f}(S)^2 = 2^{-|X|} \sum_{T \subseteq X} f(T)^2.$$

### Step 2: Odd Up-Set Convolution Kernel & Frobenius Upper Bound (`chvatal_ub_and_eigen_identities`)

Let $\mathcal{D} \subseteq 2^X$ be a downset and $\mathcal{I} \subseteq \mathcal{D}$ be pairwise intersecting. Define the upward closure $\mathcal{U} = \{T \subseteq X : \exists B \in \mathcal{I},\, B \subseteq T\}$. Since $\mathcal{I}$ is pairwise intersecting, $\mathcal{U}$ and $\mathcal{U}^c := \{X \setminus T : T \in \mathcal{U}\}$ are disjoint. Set
$$h(T) = \begin{cases} +1 & \text{if } T \in \mathcal{U}, \\ -1 & \text{if } X \setminus T \in \mathcal{U}, \\ 0 & \text{otherwise,} \end{cases} \qquad K(A, B) = \widehat{h}(A \triangle B).$$
Because $h(X \setminus T) = -h(T)$, $\widehat{h}(S) = 0$ whenever $|S|$ is even (`in particular K(A, A) = \widehat{h}(\emptyset) = 0`). Fix any element $x_1 \in X$. Partitioning $\mathcal{D} = \mathcal{D}_0 \sqcup \mathcal{D}_1$ according to whether $x_1 \notin A$ or $x_1 \in A$:
- For every $A \in \mathcal{D}_1$ (`|{A ∈ D : x₁ ∈ A}|` terms), shifting by $A \triangle \cdot$ and applying Parseval gives $\sum_{B \in \mathcal{D}} K(A, B)^2 \le \sum_{S \subseteq X} \widehat{h}(S)^2 \le 1$.
- For $A \in \mathcal{D}_0$ ($x_1 \notin A$) and $B \in \mathcal{D}_0$ ($x_1 \notin B$), $x_1 \notin A \triangle B$, whereas if $B' = B \cup \{x_1\} \in \mathcal{D}_1$, $(A \triangle B') = (A \triangle B) \cup \{x_1\}$; pairing $S$ with $S \triangle \{x_1\}$ across $\mathcal{D}_0$ cancels half of the Parseval mass outside $\mathcal{D}_1$ via symmetry $K(A, B) = K(B, A)$, yielding
  $$\sum_{A \in \mathcal{D}} \sum_{B \in \mathcal{D}} K(A, B)^2 \le 2\,|\{A \in \mathcal{D} : x_1 \in A\}|.$$
Choosing $x_0 \in X$ maximizing $|\{A \in \mathcal{D} : x \in A\}|$ gives $\sum_{A, B \in \mathcal{D}} K(A, B)^2 \le 2\,|\{A \in \mathcal{D} : x_0 \in A\}|$.

### Step 3: Physical-Space Eigenfunctions, Triangular Gram–Schmidt, & Row-Wise Bessel (`orthonormalize_triangular_eigen`, `row_bessel_inequality`)

For each $A \in \mathcal{I}$, define $p_A(C) = \mathbf{1}_{C \subseteq A}$ and $q_A(C) = (-1)^{|C|} \mathbf{1}_{C \subseteq A}$. Since $A \in \mathcal{I} \subseteq \mathcal{D}$ and $\mathcal{D}$ is downward closed, every $C \subseteq A$ lies in $\mathcal{D}$, so for every $B \in \mathcal{D}$,
$$\sum_{C \in \mathcal{D}} K(B, C) p_A(C) = \sum_{C \subseteq A} \widehat{h}(B \triangle C) = 2^{-|X|} \sum_{T \subseteq X} h(T)\chi_B(T) \sum_{C \subseteq A} \chi_T(C).$$
By powerset orthogonality, only $T$ with $T \cap A = \emptyset$ survive — i.e., $A \subseteq X \setminus T \in \mathcal{U}$, where $h(T) = -1$ identically! Evaluating the remaining sum $\sum_{T \subseteq X \setminus A} \chi_B(T) = 2^{|X|-|A|} \mathbf{1}_{B \subseteq A}$ proves **`∑_{C ∈ D} K(B, C) p_A(C) = -p_A(B)`**, and replacing $T$ by $X \setminus T$ proves **`∑_{C ∈ D} K(B, C) q_A(C) = +q_A(B)`**.

Inducting on $|\mathcal{J}|$ by peeling off a **maximum-cardinality set** $A_m \in \mathcal{J}$ (`so A_m ⊈ A` for all $A \in \mathcal{J} \setminus \{A_m\}$, guaranteeing $u(A_m) = w(A_m, A_m) = \pm 1 \ne 0$ after projecting onto prior basis vectors!) produces $|\mathcal{I}|$ orthonormal $(-1)$-eigenfunctions $e^-_i$ and $|\mathcal{I}|$ orthonormal $(+1)$-eigenfunctions $e^+_j$ on $\mathcal{D}$. Since $K(B, C) = K(C, B)$,
$$\langle e^-_i, e^+_j \rangle_{\mathcal{D}} = \langle e^-_i, K e^+_j \rangle_{\mathcal{D}} = \langle K e^-_i, e^+_j \rangle_{\mathcal{D}} = -\langle e^-_i, e^+_j \rangle_{\mathcal{D}} \implies \langle e^-_i, e^+_j \rangle_{\mathcal{D}} = 0.$$
Concatenating $\{e^-_i, e^+_j\}$ into $2|\mathcal{I}|$ orthonormal vectors $E_1, \dots, E_{2|\mathcal{I}|}$ on $\mathcal{D}$ with $\|K E_r\|_{\mathcal{D}}^2 = (\pm 1)^2 = 1$ and summing the row-wise Bessel inequality $\sum_{r=1}^{2|\mathcal{I}|} \langle K_{A, \cdot}, E_r \rangle_{\mathcal{D}}^2 \le \sum_{B \in \mathcal{D}} K(A, B)^2$ over $A \in \mathcal{D}$ yields
$$2\,|\mathcal{I}| = \sum_{r=1}^{2|\mathcal{I}|} \|K E_r\|_{\mathcal{D}}^2 \le \sum_{A \in \mathcal{D}} \sum_{B \in \mathcal{D}} K(A, B)^2 \le 2\,|\{A \in \mathcal{D} : x_0 \in A\}|,$$
whence $|\mathcal{I}| \le |\{A \in \mathcal{D} : x_0 \in A\}|$. $\square$
