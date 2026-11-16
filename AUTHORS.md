# Authorship, Provenance, and Attribution

## Lean 4 Formalization Author

- **Name**: Chucheng Xiang
- **GitHub Account**: [`@xccElephant`](https://github.com/xccElephant)
- **Repository & Branch**: [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean), standalone orphan branch `jsp-000519-lean`
- **Claimed Contribution Role**: **Lean 4 Formalization Author** (first complete, unconditional, zero-`sorry`, zero-custom-axiom Lean 4 formalization resolving Erdős Problem #638 / `JSP-000519` across all subgraph, induced-subgraph, hereditary, and non-hereditary formulations and across all infinite cardinals $\kappa \ge \aleph_0$).
- **Toolchain & Dependencies**:
  - Lean 4: `leanprover/lean4:v4.33.1`
  - Mathlib4: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`)

## Mathematical Attribution (Prior Informal Results)

No mathematical-solver priority is claimed over the prior informal mathematical results credited below:

1. **Original Problem (`[Er97d]`)**:
   - **Author**: Paul Erdős (1997).
   - **Source**: P. Erdős, *Some of my new and almost new problems and results in combinatorial number theory*, Number Theory (Eger, 1996), Walter de Gruyter, Berlin, 1998, Item 9, pp. 83–84 ([`erdosproblems.com/638`](https://www.erdosproblems.com/638); `JSP-000519` in `TheJustinSunPrize/awards`).
2. **Finite-Obstruction & Hereditary Disjoint-Age Counterexample Strategy**:
   - **Contributors**: Kevin Barreto (January 29, 2026) and Brian Saturnino (April 26, 2026).
   - **Source**: Public discussion on `erdosproblems.com` Problem #638 ([`erdosproblems.com/forum/thread/638`](https://www.erdosproblems.com/forum/thread/638)), including B. Saturnino's note *A counterexample to a hereditary triangle Ramsey compactness problem*, which shows via compactness that an infinite sequence of $r$-color triangle-Ramsey blocks with pairwise disjoint $2$-Ramsey finite subgraphs refutes hereditary triangle-Ramsey compactness already at $\aleph_0$ (and hence for every infinite cardinal $\kappa$).
3. **Sparse Triangle-Ramsey Hypergraph Container Framework**:
   - **Authors**: Rajko Nenadov and Huy Tuan Pham (2024/2025), building on Rajko Nenadov and Angelika Steger (2016), David Saxton and Andrew Thomason (2015), József Balogh, Robert Morris, and Wojciech Samotij (2015), and Vojtěch Rödl and Andrzej Ruciński (1994).

## Clean-Room Formalization & Prior Lean Sketch Disclosure

- **Prior Incomplete Lean Sketch**: Brian Saturnino's companion GitHub repository (`woeowiegj/Erdos638`, April 27, 2026) formalized the high-level compactness shell for his hereditary variant while leaving `2` `sorry`s (`avoidance_principle` and `exists_block_sequence`) for the Nešetřil–Rödl sparse Ramsey and Berge-cycle avoidance machinery.
- **100% Clean-Room Elementary Proof Closing All Gaps**: Zero code was copied or adapted from `woeowiegj/Erdos638`. Instead of Nešetřil–Rödl partite amalgamation, Berge-cycle hypergraphs, or real transcendental analysis, this repository develops from scratch in Lean 4:
  1. An elementary **$(2|S|-3)$-Sparsity $2$-Coloring Theorem** (`Erdos638/Defs.lean`: `two_colorable_of_sparse_subsets`), replacing Berge-cycle girth obstructions;
  2. A **Single-Function Idempotent Rational Hypergraph Container Theorem** purely over `ℚ` (`Erdos638/Container.lean`: `canonicalContainer`, `exists_fingerprint_for_indep`);
  3. **Exact Scale Choice $n = m^2 + 2$, $p = 1/m$ & Finite Product-Grid Alteration** (`Erdos638/GridCounting.lean`, `Erdos638/SparseRamsey.lean`, `Erdos638/AlterationBound.lean`: `exists_locally_sparse_triangle_ramsey`, `exists_ramsey_avoiding_family`);
  4. **Ultrafilter $2$-Ramsey Compactness & Full `[Er97d]` Cardinal Scope** (`Erdos638/Compactness.lean`, `Erdos638/Main.lean`, `StatementAudit.lean`), covering ordinary subgraphs, induced subgraphs, native Mathlib `SimpleGraph.Subgraph`, both hereditary and non-hereditary families, and all infinite cardinals $\kappa \ge \aleph_0$ across arbitrary universe levels `u, w`.

## AI Disclosure

AI coding and formal-verification assistance was used in drafting proof scripts, documentation, and verification checks. All Lean proofs are machine-checked end-to-end by the Lean 4.33.1 kernel and `leanchecker --fresh` with zero `sorry`, zero `admit`, zero `native_decide`, and only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
