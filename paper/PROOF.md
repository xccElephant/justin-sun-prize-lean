# Complete Proof and Topological Embedding Exposition for Erdős Problem #1019 (`JSP-000849`)

- **Problem**: Erdős Problem #1019 (`JSP-000849`, Erdős `[Er69c, pp. 16–17]`, `[Er71, item 13, p. 102]`)
- **Lean 4 Formalization Author**: Chucheng Xiang (`@xccElephant`, 100% clean-room formalization)
- **Mathematical Credits**: Miklós Simonovits (1970, PhD thesis, Chapter 9) and Stijn Cambie (2025, public proof exposition)

---

## 1. Problem Statement and Definitions

A finite simple graph $H = (W, E(H))$ on $m = |W| \ge 3$ vertices is called **planar** if there exist an injective vertex placement $\phi : W \hookrightarrow \mathbb{R}^2$ and, for each unordered edge $e = \{u, v\} \in E(H)$, a continuous injective Jordan arc $\gamma_e : [0, 1] \to \mathbb{R}^2$ such that:
1. $\{\gamma_e(0), \gamma_e(1)\} = \{\phi(u), \phi(v)\}$;
2. $\gamma_e((0, 1)) \cap \phi(W) = \emptyset$; and
3. for any two distinct edges $e_1 \ne e_2$, $\gamma_{e_1}(t_1) = \gamma_{e_2}(t_2)$ implies $t_1 \in \{0, 1\}$ and $t_2 \in \{0, 1\}$.

Following Erdős `[Er69c, p. 13]` and `[Er71, p. 102]`, a planar graph $H$ on $m$ vertices with $3m - 6$ edges is called **saturated**. In `[Er69c, p. 17]` and `[Er71, p. 102]`, Erdős asked:

> **Question (`JSP-000849` / Erdős #1019).** Does every simple graph $G$ on $n$ vertices with $\lfloor n^2 / 4 \rfloor + \lfloor (n + 1) / 2 \rfloor$ edges contain a saturated planar subgraph on $m > 3$ vertices?

Note that for $n \in \{1, 2, 3\}$, $\lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor \in \{1, 2, 4\}$ strictly exceeds $\binom{n}{2} \in \{0, 1, 3\}$, so the implication holds vacuously for $1 \le n \le 3$ and substantively for all $n \ge 4$.

Define the extremal edge count
$$f(n) := \left\lfloor \frac{n^2}{4} \right\rfloor + \left\lfloor \frac{n - 1}{2} \right\rfloor, \qquad f(n) + 1 = \left\lfloor \frac{n^2}{4} \right\rfloor + \left\lfloor \frac{n + 1}{2} \right\rfloor \quad (n \ge 1).$$
For $\ell \ge 3$, let $B_\ell := C_\ell \vee 2K_1$ denote the $\ell$-bipyramid on $\ell + 2$ vertices with $3\ell = 3(\ell + 2) - 6$ edges. A graph $G$ on $n \ge 1$ vertices is called a **balanced tree-join** if $V(G) = A \sqcup B$ with $a = |A| \ge 1$, $b = |B| = n - a$, $0 \le a - b \le 2$ (equivalently $n \le 2a \le n + 2$), $G[A]$ is a tree, $B$ is an independent set, and every vertex in $A$ is adjacent to every vertex in $B$. Every balanced tree-join has $(a - 1) + ab = f(n)$ edges.

---

## 2. Simonovits–Cambie Extremal Stability Theorem

**Theorem 2.1 (`simonovits_stability`).** *Every simple graph $G$ on $n \ge 1$ vertices with $e(G) \ge f(n)$ either contains $K_4$ or some $B_\ell$ ($\ell \ge 3$), or else has $e(G) = f(n)$ and is a balanced tree-join.*

**Lemma 2.2 (`contains_of_balancedTreeJoin_and_extra_edge`).** *If $G_1 \subseteq G$ is a spanning balanced tree-join on $n \ge 1$ vertices and $G$ contains at least one edge $u_0 v_0 \notin E(G_1)$, then $G$ contains $K_4$ or some $B_\ell$ ($\ell \ge 3$).*

*Proof of Lemma 2.2.* Let $(A, B)$ be the balanced tree-join partition of $G_1$. Since all cross pairs between $A$ and $B$ are already edges of $G_1$, either $u_0, v_0 \in A$ or $u_0, v_0 \in B$.
- **Case 1 ($u_0, v_0 \in A$)**: Let $P = (w_0, w_1, \dots, w_k)$ ($w_0 = u_0, w_k = v_0$) be the unique path between $u_0$ and $v_0$ in the tree $G_1[A]$. Because $u_0 \ne v_0$ and $u_0 v_0 \notin E(G_1)$, we have $k \ge 2$, so $P \cup \{u_0 v_0\}$ is a cycle of length $\ell = k + 1 \ge 3$ in $G[A]$, and $a = |A| \ge \ell \ge 3$. Since $2a \le n + 2 = a + b + 2$, we have $b \ge a - 2 \ge 1$.
  - If $b \ge 2$, choosing any two distinct vertices $x_1, x_2 \in B$ yields $B_\ell \subseteq G$.
  - If $b = 1$, then $a \le b + 2 = 3$, forcing $a = 3$, $k = 2$, and $B = \{x_1\}$; then $\{w_0, w_1, w_2, x_1\}$ spans $K_4 \subseteq G$.
- **Case 2 ($u_0, v_0 \in B$)**: Here $b = |B| \ge 2$, so $a \ge b \ge 2$. Thus the tree $G_1[A]$ has $a - 1 \ge 1$ edges. Picking any edge $a_1 a_2 \in E(G_1[A])$, the four vertices $\{a_1, a_2, u_0, v_0\}$ span $K_4 \subseteq G$. $\blacksquare$

*Proof of Theorem 2.1.* By Lemma 2.2 (applied after deleting excess edges down to $f(n) + 1$ and removing one further edge), it suffices to prove the exact-edge case $e(G) = f(n)$ by strong induction on $n \ge 1$.

For $n = 1$, $f(1) = 0$ and $V(G) = A \sqcup \emptyset$ is a $1$-vertex tree-join.

Now let $n \ge 2$ and assume $e(G) = f(n)$. Direct parity verification mod $4$ gives $f(n) - f(n - 1) = \lfloor (n + 1)/2 \rfloor$ and $2 f(n) < n(\lfloor (n + 1)/2 \rfloor + 1)$. By the handshaking lemma $\sum_{v \in V} \deg(v) = 2 f(n)$, some vertex $x \in V(G)$ has $\deg_G(x) \le \lfloor (n + 1)/2 \rfloor$. Set $G' = G - x$ on $n - 1 \ge 1$ vertices, so $e(G') = f(n) - \deg_G(x) \ge f(n - 1)$.
- If $e(G') > f(n - 1)$, the induction hypothesis together with Lemma 2.2 gives $K_4$ or $B_\ell$ in $G' \subseteq G$.
- Otherwise $e(G') = f(n - 1)$ and $\deg_G(x) = \lfloor (n + 1)/2 \rfloor$. Assuming $G'$ avoids $K_4$ and all $B_\ell$, the induction hypothesis gives $V(G') = A' \sqcup B'$ with $a' = |A'| \ge 1$, $b' = |B'| = n - 1 - a'$, $n - 1 \le 2a' \le n + 1$, $G'[A']$ a tree, $B'$ independent, and all cross edges $A' \times B'$ present.

Let $N_A = N_G(x) \cap A'$ ($p = |N_A| \le a'$) and $N_B = N_G(x) \cap B'$ ($q = |N_B| \le b'$), so $p + q = \lfloor (n + 1)/2 \rfloor$. Since $b' \le \lfloor (n - 1)/2 \rfloor < \lfloor (n + 1)/2 \rfloor$, we always have $p \ge 1$. Four cases exhaust all possibilities:
1. **$p \ge 2$ and $q \ge 2$**: Pick $u_1 \ne u_2$ in $N_A$ and $v_1 \ne v_2$ in $N_B$. If $u_1 u_2 \in E(G)$, $\{x, u_1, u_2, v_1\}$ induces $K_4$. If $u_1 u_2 \notin E(G)$, the unique $u_1$–$u_2$ path in the tree $G'[A']$ has length $k \ge 2$ and forms with $x$ a cycle of length $\ell = k + 2 \ge 4$ inside $A' \cup \{x\}$, every vertex of which is adjacent to both $v_1$ and $v_2$, yielding $B_\ell \subseteq G$.
2. **$p = 1$**: Since $1 + q = \lfloor (n + 1)/2 \rfloor$ and $q \le b' \le \lfloor (n - 1)/2 \rfloor$, equality holds throughout: $n$ is odd or $4 \mid n - 2$ with $b' = q = \lfloor (n - 1)/2 \rfloor$ (so $N_B = B'$) and $n \le 2(a' + 1) \le n + 2$. Writing $N_A = \{u\}$, $x$ attaches as a leaf to $u$ in $G'[A']$, so $G[A' \cup \{x\}]$ is a tree and $(A' \cup \{x\}, B')$ exhibits $G$ as a balanced tree-join.
3. **$p \ge 2$ and $q = 0$**: Then $p = \lfloor (n + 1)/2 \rfloor \le a'$ forces $a' = p = \lfloor (n + 1)/2 \rfloor$ (so $N_A = A'$) and $n \le 2a' \le n + 2$. Thus $x$ is non-adjacent to $B'$ and adjacent to all of $A'$, so $(A', B' \cup \{x\})$ exhibits $G$ as a balanced tree-join.
4. **$p \ge 2$ and $q = 1$**: Let $N_B = \{v\}$. Since $p + 1 = \lfloor (n + 1)/2 \rfloor$ and $a' - b' \in \{0, 1, 2\}$, we have $p \in \{a', a' - 1\}$.
   - If $p = a'$ ($N_A = A'$), since $a' = p \ge 2$, the tree $G'[A']$ contains at least one edge $u_1 u_2$, and $\{x, v, u_1, u_2\}$ spans $K_4$.
   - If $p = a' - 1$, let $A' \setminus N_A = \{u\}$. Notice $(b' + 2) + (a' - 1) = n$ and $n \le 2(b' + 2) \le n + 2$. If any two vertices $y, z \in A' \setminus \{u\} = N_A$ are adjacent, $\{x, v, y, z\}$ spans $K_4$. Otherwise $A' \setminus \{u\}$ is independent; since $G'[A']$ is connected, every $y \in A' \setminus \{u\}$ must be adjacent to $u$ (making $G'[A']$ a star centered at $u$). Then $S := B' \cup \{u, x\}$ induces a broom tree ($B'$ is a star on center $u$, and $x$ attaches solely to $v \in B'$), $I := A' \setminus \{u\}$ is independent, and every vertex of $I$ is adjacent to $x$, $u$, and every vertex of $B'$. Hence $(S, I)$ exhibits $G$ as a balanced tree-join. $\blacksquare$

---

## 3. Explicit Non-Crossing Straight-Line Embeddings of $B_\ell$ and $K_4$

For $\ell \ge 3$, embed the $\ell + 2$ vertices of $B_\ell = C_\ell \vee 2K_1$ at the integer points in $\mathbb{R}^2$:
$$P_0 = (0, 4), \quad P_k = (k, 0) \;\; (1 \le k < \ell), \quad N = (1, 1), \quad S = (0, -1),$$
with affine straight-line segments $\gamma_{uv}(t) = (1 - t)\phi(u) + t\phi(v)$ for $t \in [0, 1]$.

For $s \in (0, 1)$, every open edge segment lies in $-1 < y < 4$ and falls into one of seven pairwise-disjoint affine regions:
1. $S P_0$: $x = 0$, $-1 < y < 4$;
2. $S P_k$ ($1 \le k < \ell$): $(s k, s - 1)$ with $x > 0$ and $-1 < y < 0$ (distinct $k$ give distinct $x = k(y + 1)$);
3. $P_k P_{k+1}$ ($1 \le k < \ell - 1$): $(k + s, 0)$ with $y = 0$ and $k < x < k + 1$;
4. $P_0 P_1$: $(s, 4 - 4s)$ with $x > 0$, $y > 0$, and $4x + y = 4$;
5. $P_0 P_{\ell - 1}$: $(s(\ell - 1), 4 - 4s)$ with $x > 0$, $y > 0$, $4x + y > 4$, and $4x + (\ell - 1)y = 4(\ell - 1)$;
6. $N P_0$: $(1 - s, 1 + 3s)$ with $x > 0$, $1 < y < 4$, $4x + y > 4$, and $4x + (\ell - 1)y < 4(\ell - 1)$ (since $\ell - 1 \ge 2$);
7. $N P_k$ ($1 \le k < \ell$): $(1 - s + sk, 1 - s)$ with $x > 0$, $0 < y < 1$, $4x + y > 4$, and $4x + (\ell - 1)y < 4(\ell - 1)$ (distinct $k$ determine $s = 1 - y > 0$ and hence $k$).

No vertex lies in any open edge segment ($S$ has $y = -1$, $P_0$ has $y = 4$, $N = (1, 1)$ violates $y \ne 1$ or $4x + (\ell - 1)y = 4(\ell - 1)$ since $4 + \ell - 1 < 4\ell - 4$ for $\ell \ge 3$, and $P_m = (m, 0)$ has integer $x \ge 1$ on $y = 0$). Thus $B_\ell$ is topologically planar for every $\ell \ge 3$, and $K_4$ embeds as the subgraph $\{P_0, P_1, P_2, N\} \subseteq B_3$, so $K_4$ is topologically planar as well. Combining this with Theorem 2.1 settles Erdős Problem #1019 (`JSP-000849`) in the affirmative. $\blacksquare$
