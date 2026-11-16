# Authorship, Provenance, and Attribution

## Lean 4 Formalization Author

- **Name**: Chucheng Xiang
- **GitHub Account**: [`@xccElephant`](https://github.com/xccElephant)
- **Repository & Branch**: [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean), standalone orphan branch `jsp-000849-lean`
- **Claimed Contribution Role**: **Lean 4 Formalization Author** (first complete, 100% clean-room, unconditional Lean 4 formalization of Erdős Problem #1019 / `JSP-000849` with genuine Jordan-arc topological planarity in $\mathbb{R}^2$, eligible for the 30% formalization role under the pre-2026 mathematical solution rule).
- **Toolchain & Dependencies**:
  - Lean 4: `leanprover/lean4:v4.33.1`
  - Mathlib4: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`)

## Mathematical Attribution (Prior Informal Results)

No mathematical-solver priority is claimed over the prior informal mathematical results credited below:

1. **Affirmative Resolution & Extremal Stability Theorem**:
   - **Author**: Miklós Simonovits (1970, PhD dissertation, Chapter 9; cited by Paul Erdős in `[Er71, item 13, p. 102]`).
   - **Original Problem Sources**:
     - P. Erdős, *Über die in Graphen enthaltenen saturierten planaren Graphen*, Math. Nachr. 40 (1969), 13–17 (`[Er69c, pp. 16–17]`).
     - P. Erdős, *Some unsolved problems in graph theory and combinatorial analysis*, Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969), Academic Press, London (1971), 97–109 (`[Er71, item 13, p. 102]`).
2. **Public Combinatorial Proof Exposition**:
   - **Author**: Stijn Cambie (21 November 2025, following correspondence with Miklós Simonovits).
   - **Source**: Public proof summary on `erdosproblems.com` Problem #1019 ([discussion thread #1019](https://www.erdosproblems.com/forum/thread/1019)).

## Clean-Room Provenance & Statement Fidelity

- **100% Clean-Room Authorship**: Every file in this repository (`Erdos1019/Planarity.lean`, `Erdos1019/Bipyramid.lean`, `Erdos1019/Extremal.lean`, `Erdos1019.lean`, and `StatementAudit.lean`) was authored completely from scratch against Mathlib `v4.33.1`, without reading, copying, vendoring, or adapting any third-party formalization code.
- **Topological Planarity Fidelity**: Unlike proxy models that replace planarity with a finite isomorphism disjunction (`K_4` or `bipyramidGraph l`), `Erdos1019.IsPlanar` defines genuine topological planarity in `ℝ × ℝ` via an injective vertex placement `W ↪ ℝ × ℝ` and continuous injective Jordan arcs `Set.Icc (0 : ℝ) 1 → ℝ × ℝ` whose open interiors avoid all vertices and which intersect other arcs at most at shared endpoints (independently cross-checked in `StatementAudit.isPlanar_iff_rawJordanPlanar`).
- **Complete Scope Coverage**: Covers both the literal exact-edge formulation $e(G) = \lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ (`Erdos1019.erdos_1019`, `StatementAudit.audit_erdos_1019_exact`) and the monotone inequality formulation $e(G) \ge \lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ (`Erdos1019.erdos_1019_ge`, `Erdos1019.erdos_1019_fin`, `StatementAudit.audit_erdos_1019_ge`), together with the full Simonovits stability theorem at $\lfloor n^2/4 \rfloor + \lfloor (n-1)/2 \rfloor$ (`Erdos1019.simonovits_stability`).

## AI Disclosure

AI coding and formal-verification assistance was used in authoring the clean-room Lean 4 proof scripts, documentation, and verification checks. All Lean proofs are machine-checked end-to-end by the Lean 4.33.1 kernel and `leanchecker --fresh` with zero `sorry`, zero `admit`, zero `native_decide`, and only the three standard classical axioms `propext`, `Classical.choice`, and `Quot.sound`.
