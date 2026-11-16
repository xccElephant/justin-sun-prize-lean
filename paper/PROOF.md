# Unconditional ZFC Disproof of Erdős Problem #638 (`JSP-000519`)

## 1. Problem Statement and Quantifier Audit

In `[Er97d, Item 9, pp. 83–84]` (and [`erdosproblems.com/638`](https://www.erdosproblems.com/638)), Paul Erdős asked:

> *"Let $S$ be a family of finite graphs such that for every $n \ge 1$ there is $G_n \in S$ with $G_n \to (K_3)^2_n$ (that is, if the edges of $G_n$ are $n$-coloured then there is a monochromatic triangle). Is it true that for every infinite cardinal $\kappa$ there is a graph $G$ all of whose finite subgraphs are in $S$ such that if the edges of $G$ are $\kappa$-coloured then there is a monochromatic triangle?"*

As discussed on `erdosproblems.com/forum/thread/638` (Kevin Barreto, Jan 29, 2026; Brian Saturnino, Apr 26, 2026):
1. **Literal (non-hereditary) reading**: Without assuming $S$ is closed under subgraphs (e.g., $S = \{K_{R_n(3)} : n \ge 1\}$), no graph with $\ge 2$ edges can have all ordinary finite subgraphs in $S$ (since $K_2 \notin S$), and taking sparse complete graphs $S = \{K_{3^n + 1} : n \ge 1\}$ similarly obstructs induced subgraphs of size $5$.
2. **Intended hereditary readings (both ordinary and induced)**: Even when $S$ is required to be **hereditary** — either closed under all ordinary finite subgraphs (`ClosedUnderSubgraphs S`) or closed under all finite induced subgraphs (`ClosedUnderInducedSubgraphs S`) — the answer is **NO**. More strongly, there exist hereditary families $\mathcal{S}_{\mathrm{ord}}$ and $\mathcal{S}_{\mathrm{ind}}$ containing $G_n \to (K_3)^2_n$ for every $n \ge 1$ such that for **every** graph $G$ (finite or infinite, in any universe) whose finite ordinary (resp. induced) subgraphs belong to $\mathcal{S}_{\mathrm{ord}}$ (resp. $\mathcal{S}_{\mathrm{ind}}$), there already exists a **finite integer $m \ge 2$** such that $G \not\to (K_3)^2_m$. Injecting $\mathrm{Fin}\,m$ into any infinite color palette of cardinality $\kappa \ge \aleph_0$ immediately yields $G \not\to (K_3)^2_\kappa$ simultaneously for **every infinite cardinal $\kappa$** (including $\kappa = \aleph_0$).

---

## 2. Self-Contained Elementary Proof

Our Lean 4 formalization eliminates Nešetřil–Rödl partite amalgamation, Berge-cycle hypergraph theory, and real transcendental analysis via four elementary steps:

### Step 1: The $(2|S|-3)$-Sparsity 2-Coloring Theorem (`Erdos638/Defs.lean`)

**Theorem (`two_colorable_of_sparse_subsets`).** *Let $H = (V, E)$ be a finite simple graph such that every vertex subset $S \subseteq V$ with $|S| \ge 4$ spans at most $2|S| - 3$ edges. Then $H \not\to (K_3)^2_2$.*

*Proof.* By strong induction on $|V|$. For $|V| \le 3$ there is at most one triangle, which can be bicolored if $|E| = 3$. For $|V| = 4$, $|E| \le 2(4) - 3 = 5 < 6$, so $H$ is a subgraph of $K_4 - e$; coloring the shared edge of the two potential triangles color $0$ and the remaining $\le 4$ edges color $1$ avoids monochromatic triangles.

For $|V| \ge 5$, applying the hypothesis to $S = V$ gives $|E| \le 2|V| - 3$, so $\sum_{v \in V} \deg(v) = 2|E| \le 4|V| - 6 < 4|V|$. Hence some vertex $v \in V$ has $\deg(v) \le 3$. By the induction hypothesis on $H - v$, there is a monochromatic-$K_3$-free $2$-coloring $c$ of $H - v$. Crucially, the neighborhood $N(v)$ ($|N(v)| \le 3$) **cannot induce $K_3$**, else $S = \{v\} \cup N(v)$ would have $4$ vertices and $3 + 3 = 6 > 5$ edges! Thus $N(v)$ spans at most $2$ edges in $H - v$:
- If $N(v)$ spans $0$ edges, no triangle contains $v$.
- If $N(v)$ spans $1$ edge $u_1 u_2$, setting $c(v u_1) = 0$ and $c(v u_2) = 1$ bicolors the unique triangle $\{v, u_1, u_2\}$ through $v$.
- If $N(v) = \{u_1, u_2, u_3\}$ spans $2$ edges $u_1 u_2$ and $u_2 u_3$ sharing center $u_2$ (with $u_1 u_3 \notin E$), setting $c(v u_2) = 0$ and $c(v u_1) = c(v u_3) = 1$ bicolors both $\{v, u_1, u_2\}$ and $\{v, u_2, u_3\}$, regardless of $c(u_1 u_2)$ and $c(u_2 u_3)$! $\square$

**Corollary (`exists_dense_four_plus_subset`).** *Every finite graph $M$ satisfying $M \to (K_3)^2_2$ contains a subset $S \subseteq V(M)$ with $4 \le |S| \le |V(M)|$ spanning at least $2|S| - 2$ edges.*

---

### Step 2: Single-Function Rational Hypergraph Containers (`Erdos638/Container.lean`)

Following Nenadov–Pham (2024/2025), for any $3$-uniform hypergraph $\mathcal{H} \subseteq \binom{[N_0]}{3}$ satisfying $(p, \lambda)$-spreadness over $\mathbb{Q}$, we construct an explicit deterministic degree-peeling procedure (`containerStep` / `buildContainer3`) and package its self-application `canonicalContainer(S) := buildContainer3(S)` (`@[irreducible]`). Using a sandwich invariant ($S \subseteq I \subseteq C$), we prove purely over $\mathbb{Q}$ (`exists_fingerprint_for_indep`) that every independent set $I$ of $\mathcal{H}$ admits a fingerprint $S \subseteq I$ of small size ($|S| \le O(\lambda p N_0)$) such that $I \subseteq \mathrm{canonicalContainer}(S)$ and $\mathcal{H}[\mathrm{canonicalContainer}(S)]$ spans strictly fewer than $(1 - c_\lambda)|E(\mathcal{H})|$ hyperedges.

---

### Step 3: Exact Scale $n = m^2 + 2$ and Finite-Grid Alteration (`GridCounting.lean`, `SparseRamsey.lean`, `AlterationBound.lean`)

Setting $n := m^2 + 2$ and $N_0 := \binom{n}{2}$ eliminates all irrational square roots via the exact identity $3\binom{n}{3} = (n - 2)\binom{n}{2} = m^2 N_0$, making $\mathcal{H}_{\triangle}(K_n)$ $(1/m, 3)$-spread (`triangleHypergraph_isSpread`). On the finite product grid $\Omega = (\mathrm{Fin}\,N_0 \to \mathrm{Fin}\,m)$ with active-edge threshold $A$ (`rawEdges A ω`):
1. **Deterministic $(2|S|-3)$-sparsity via purging (`purgeDenseObstructions_sparse`, `card_many_obstructions_lt_half`)**: Deleting every $(k, 2k-2)$-dense subset ($4 \le k \le B$) from `rawEdges A ω` deterministically enforces $\le 2|S| - 3$ edges on all $S$ with $4 \le |S| \le B$, while Markov's inequality on $\Omega$ guarantees that strictly fewer than $|\Omega|/2$ grids delete more than $4 B C_{\mathrm{obs}} m^2 = O_{r, B}(m^2)$ edges.
2. **Ramsey supersaturation + container union bound (`exists_locally_sparse_triangle_ramsey`)**: Whenever the purged graph $G'(\omega)$ fails $G'(\omega) \to (K_3)^2_r$ while deleting $\le L := 4 B C_{\mathrm{obs}} m^2$ edges, partitioning $E(G'(\omega)) = I_1 \sqcup \dots \sqcup I_r$ into $r$ triangle-free color classes yields fingerprints $(S_1, \dots, S_r)$ inside `rawEdges A ω` and containers $C_c = \mathrm{canonicalContainer}(S_c)$, plus a leftover deleted set $F \subseteq \mathrm{rawEdges}\,A\,\omega$ of size $|F| \le L$ covering all remaining edges of `rawEdges A ω`. By `triangleHypergraph_union_add_le`, adding $F$ to $C_1$ creates at most $L m^2 = O_{r, B}(m^4) \ll m^6$ triangles, so Ramsey supersaturation (`ramsey_supersaturation`) forces at least $D_U = \Omega_r(N_0)$ edges of $K_n$ to lie outside $F \cup \bigcup_{c=1}^r C_c$ (hence outside `rawEdges A ω`). Summing cylinder counts (`card_grid_cylinder`) over all $(S_1, \dots, S_r)$ and $F$ via rational Bernstein bounds (`GridCounting.lean`) bounds the non-Ramsey grids by $< |\Omega|/2$.

Hence some $\omega \in \Omega$ yields a finite graph $W = G'(\omega)$ with $W \to (K_3)^2_r$ in which every subset $S$ ($4 \le |S| \le B$) spans $\le 2|S| - 3$ edges — and by Step 1, **no $2$-Ramsey graph on $\le B$ vertices embeds into $W$** (`exists_ramsey_avoiding_family`)!

---

### Step 4: Disjoint-Age Block Sequence and Ultrafilter Compactness (`Compactness.lean`, `Main.lean`)

1. **Ultrafilter Compactness (`exists_finite_induced_two_ramsey`)**: Using an ultrafilter extending `Filter.atTop` on `Finset V`, every graph $G = (V, E)$ with $G \to (K_3)^2_2$ contains a finite induced subgraph $H_0$ with $H_0 \to (K_3)^2_2$.
2. **Recursive Block Sequence (`blockGraph`)**: Define $W_k := \mathrm{blockGraph}(k)$ recursively so that $W_k \to (K_3)^2_{k+2}$ while $W_k$ avoids all $2$-Ramsey subgraphs on $\le \max_{j < k} |V(W_j)|$ vertices. Then no finite $2$-Ramsey graph can embed into two distinct blocks $W_a, W_b$ ($a \ne b$) (`blockGraph_disjoint_two_ramsey`).
3. **Unified Finite-Palette Obstruction (`exists_finite_palette_obstruction`)**: Define the subgraph-closed class $\mathcal{S}_{\mathrm{ord}} := \{H : \exists k,\, H \hookrightarrow_{\mathrm{sub}} W_k\}$ and induced-closed subclass $\mathcal{S}_{\mathrm{ind}} := \{H : \exists k,\, H \hookrightarrow_{\mathrm{ind}} W_k\} \subseteq \mathcal{S}_{\mathrm{ord}}$. For **any** graph $G = (V, E)$ whose finite induced subgraphs belong to $\mathcal{S}_{\mathrm{ord}}$ (which holds under **both** $\mathrm{Age}_{\mathrm{ord}}(G) \subseteq \mathcal{S}_{\mathrm{ord}}$ and $\mathrm{Age}_{\mathrm{ind}}(G) \subseteq \mathcal{S}_{\mathrm{ind}}$):
   - Either $G \not\to (K_3)^2_2$ ($m = 2$);
   - Or $G \to (K_3)^2_2$, so $G$ contains a finite induced $2$-Ramsey subgraph $H_0 = G[F_0]$ embedding into a **unique** block $W_{k_0}$. Every finite superset $S \supseteq F_0$ in $V$ induces $G[S] \in \mathcal{S}_{\mathrm{ord}}$, which embeds into some $W_{k_1}$; since $H_0 \hookrightarrow_{\mathrm{sub}} G[S] \hookrightarrow_{\mathrm{sub}} W_{k_1}$, uniqueness forces $k_1 = k_0$ and $|S| \le |V(W_{k_0})|$. Thus $V$ is finite ($|V| \le |V(W_{k_0})|$), so $G$ has finitely many edges $e = |E(G)|$ and fails $G \to (K_3)^2_{\max(2, e+1)}$!
   - Injecting $\mathrm{Fin}\,m \hookrightarrow C$ into any infinite palette $C$ ($|C| = \kappa \ge \aleph_0$) yields $G \not\to (K_3)^2_C$ for every infinite cardinal $\kappa$. $\blacksquare$
