# JSP-000519 · Erdős Problem #638 — Complete Lean 4 Formalization

Complete, unconditional, zero-custom-axiom Lean 4 formalization resolving **JSP-000519** (Erdős Problem #638, `[Er97d, Item 9, pp. 83–84]`, [`erdosproblems.com/638`](https://www.erdosproblems.com/638)):

> **JSP-000519**: *Can the property of forcing a monochromatic triangle under every finite edge coloring be extended to infinite cardinal sizes?*
>
> **Erdős `[Er97d, pp. 83–84]`**: *Let $S$ be a family of finite graphs such that for every $n \ge 1$ there is $G_n \in S$ with $G_n \to (K_3)^2_n$ (that is, if the edges of $G_n$ are $n$-coloured then there is a monochromatic triangle). Is it true that for every infinite cardinal $\kappa$ there is a graph $G$ all of whose finite subgraphs are in $S$ such that if the edges of $G$ are $\kappa$-coloured then there is a monochromatic triangle?*

**Answer: No** — across **every** standard reading of the problem (ordinary-subgraph hereditary families, induced-subgraph hereditary families, native Mathlib `SimpleGraph.Subgraph` containment, and literal non-hereditary families), and **simultaneously for every infinite cardinal $\kappa \ge \aleph_0$** across arbitrary Lean universe levels `u, w`. More strongly, for our hereditary counterexample families $\mathcal{S}_{\mathrm{ord}}$ and $\mathcal{S}_{\mathrm{ind}}$, every graph $G$ whose finite ordinary (resp. induced) subgraphs belong to $\mathcal{S}_{\mathrm{ord}}$ (resp. $\mathcal{S}_{\mathrm{ind}}$) already fails $G \to (K_3)^2_m$ for some **finite** palette size $m \ge 2$, and hence fails $G \to (K_3)^2_\kappa$ at $\kappa = \aleph_0$ and at every infinite cardinal $\kappa \ge \aleph_0$.

---

## Verified Formal Targets

| Module | Declaration | Mathematical Content |
| :--- | :--- | :--- |
| `Erdos638.Defs` | `Erdos638.two_colorable_of_sparse_subsets` | Every finite graph in which every subset $S$ with $\|S\| \ge 4$ spans $\le 2\|S\|-3$ edges satisfies $H \not\to (K_3)^2_2$ |
| `Erdos638.Container` | `Erdos638.Container.exists_fingerprint_for_indep` | Single-function idempotent rational hypergraph container theorem over `ℚ` for $(p, 3)$-spread $3$-graphs |
| `Erdos638.AlterationBound` | `Erdos638.exists_ramsey_avoiding_family` | For every $r \ge 1$ and finite family $\mathcal{F}$ of $2$-Ramsey graphs, $\exists W \to (K_3)^2_r$ avoiding every $M \in \mathcal{F}$ |
| `Erdos638.Compactness` | `Erdos638.exists_finite_palette_obstruction` | $\mathrm{Age}_{\mathrm{ind}}(G) \subseteq \mathcal{S}_{\mathrm{ord}} \implies \exists m \ge 2,\; G \not\to (K_3)^2_m$ (via ultrafilter compactness + disjoint blocks) |
| `Erdos638.Main` | `Erdos638.erdos_638_ordinary_hereditary_counterexample` | Subgraph-closed counterexample $\mathcal{S}_{\mathrm{ord}}$ obstructing $G \to (K_3)^2_C$ for every $\kappa \ge \aleph_0$ and $\#C = \kappa$ |
| `Erdos638.Main` | `Erdos638.erdos_638_induced_hereditary_counterexample` | Induced-subgraph-closed counterexample $\mathcal{S}_{\mathrm{ind}}$ obstructing $G \to (K_3)^2_C$ for every $\kappa \ge \aleph_0$ and $\#C = \kappa$ |
| `Erdos638.Main` | `Erdos638.not_erdos_638_ordinary_hereditary` | Direct negation of Erdős #638 (ordinary-subgraph hereditary formulation, universe-polymorphic in `u, w`) |
| `Erdos638.Main` | `Erdos638.not_erdos_638_induced_hereditary` | Direct negation of Erdős #638 (induced-subgraph hereditary formulation, universe-polymorphic in `u, w`) |
| `Erdos638.Main` | `Erdos638.not_erdos_638_ordinary` / `not_erdos_638_induced` | Direct negations of the literal non-hereditary formulations |
| `StatementAudit` | `Erdos638Audit.audit_erdos_638_mathlib_subgraph_hereditary` | Standalone pure-Mathlib disproof using injective `SimpleGraph.Hom` (`H →g G`) and `Cardinal` |
| `StatementAudit` | `Erdos638Audit.audit_erdos_638_mathlib_embedding_hereditary` | Standalone pure-Mathlib disproof using `SimpleGraph.Embedding` (`H ↪g G`) and `Cardinal` |
| `StatementAudit` | `Erdos638Audit.audit_erdos_638_mathlib_subgraph_type_strong` | Standalone pure-Mathlib disproof using native `H : G.Subgraph` (`Finite H.verts`) and `Sym2 V → C` |

### Trust & Completeness Summary

- **`sorry` / `admit` count**: `0`
- **`native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`**: `0`
- **Transitive axioms (`#print axioms`)**: strictly `[propext, Classical.choice, Quot.sound]`
- **Fine-grained imports only**: zero monolithic `import Mathlib` (`1,309` transitive build jobs)
- **Kernel replay**: verified via `lake env leanchecker -v Erdos638 StatementAudit`, `lake env leanchecker --fresh Erdos638`, and `lake env leanchecker --fresh StatementAudit`

---

## Pinned Toolchain & Reproduction

- **Repository**: [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean) (standalone orphan branch `jsp-000519-lean`)
- **Lean Toolchain**: `leanprover/lean4:v4.33.1` ([`lean-toolchain`](lean-toolchain))
- **Mathlib Revision**: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`, pinned in [`lake-manifest.json`](lake-manifest.json))

```bash
git clone --single-branch --branch jsp-000519-lean https://github.com/xccElephant/justin-sun-prize-lean.git
cd justin-sun-prize-lean
lake exe cache get
timeout 300s lake --wfail build
timeout 180s lake env lean StatementAudit.lean
timeout 300s lake env leanchecker -v Erdos638 StatementAudit
timeout 600s lake env leanchecker --fresh Erdos638
timeout 600s lake env leanchecker --fresh StatementAudit
```

---

## Architecture & Exposition

| Path | Lines | Description |
| :--- | ---: | :--- |
| [`Erdos638/Defs.lean`](Erdos638/Defs.lean) | 636 | Arrow relations, hereditary graph ages, and the $(2\|S\|-3)$-sparsity $2$-coloring theorem |
| [`Erdos638/Container.lean`](Erdos638/Container.lean) | 1,569 | Single-function idempotent rational hypergraph container theorem over `ℚ` |
| [`Erdos638/GridCounting.lean`](Erdos638/GridCounting.lean) | 346 | Product-grid cylinder identities and rational Bernstein/binomial bounds |
| [`Erdos638/SparseRamsey.lean`](Erdos638/SparseRamsey.lean) | 1,141 | Multicolor Ramsey upper bound, $(1/m, 3)$-spreadness at $n = m^2+2$, Ramsey supersaturation, dense-subset purging |
| [`Erdos638/AlterationBound.lean`](Erdos638/AlterationBound.lean) | 1,121 | Markov obstruction bound and $r$-color container union bound on $\Omega = \mathrm{Fin}\,N_0 \to \mathrm{Fin}\,m$ |
| [`Erdos638/Compactness.lean`](Erdos638/Compactness.lean) | 451 | Ultrafilter $2$-Ramsey compactness, recursive disjoint-age `blockGraph` sequence, finite-palette obstruction |
| [`Erdos638/Main.lean`](Erdos638/Main.lean) | 192 | Universe-polymorphic constructive counterexample theorems and direct disproofs of Erdős #638 |
| [`StatementAudit.lean`](StatementAudit.lean) | 264 | Independent first-principles Mathlib statement reconstruction and `#print axioms` audit |
| [`paper/PROOF.md`](paper/PROOF.md) / [`paper/erdos638.tex`](paper/erdos638.tex) | — | Self-contained mathematical exposition (Markdown and AMS-LaTeX) |
| [`AUTHORS.md`](AUTHORS.md) | — | Authorship (`Chucheng Xiang` / `@xccElephant`), prior mathematical credits, clean-room & AI disclosures |
