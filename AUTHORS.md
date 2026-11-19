# Authorship, Provenance, and Attribution

## Lean 4 Formalization Author

- **Name**: Chucheng Xiang
- **GitHub Account**: [`@xccElephant`](https://github.com/xccElephant)
- **Repository & Branch**: [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean), standalone orphan branch `jsp-000571-lean`
- **Contribution Role**: **Lean 4 Formalization Author** (independent, 100% clean-room, unconditional Lean 4 formalization of Chvátal's Conjecture — Erdős Problem #701 / `JSP-000571` — via physical-space Boolean characters, maximum-cardinality-peeling triangular Gram–Schmidt orthonormalization, and row-wise Bessel inequality).
- **Toolchain & Dependencies**:
  - Lean 4: `leanprover/lean4:v4.33.1`
  - Mathlib4: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`)

## Mathematical Attribution (Prior Informal Results)

No mathematical-solver priority is claimed over the informal mathematical results credited below:

1. **Original Conjecture & Problem Sources**:
   - Václav Chvátal, *Intersecting families of edges in hypergraphs having the hereditary property*, in *Hypergraph Seminar* (Ohio State University, Columbus, 1972), Lecture Notes in Mathematics, vol. 411, Springer, Berlin (1974), pp. 61–66 (`[Ch74]`).
   - Paul Erdős, *On the combinatorial problems which I would most like to see solved*, Combinatorica 1 (1981), 25–42 (`[Er81]`).
   - Related early and partial results: François Sterboul (`[St74]`, Lecture Notes in Math. 411, 1974, pp. 152–164); Daniel J. Kleitman and Thomas L. Magnanti (J. Combin. Theory Ser. A 16, 1974, 215–220); Peter Borg (`[Bo11]`, Eur. J. Combin. 32, 2011, 140–145); Leon Eifler, Ambros Gleixner, and Jonad Pulaj (2018/2019); Peter Frankl and Andrey Kupavskii (`[FrKu23]`, Adv. Math. 426, 2023).
2. **Affirmative Mathematical Resolution of Chvátal's Conjecture (September 2026 Preprints)**:
   - **Fan Chang, Hong Liu, and Miao Liu**, *A proof of Chvátal's conjecture via a sharp correlation inequality*, [`arXiv:2609.19123`](https://arxiv.org/abs/2609.19123) (16 September 2026).
   - **Peter Keevash**, *On Kahn's flow conjecture*, [`arXiv:2609.23595`](https://arxiv.org/abs/2609.23595) (20 September 2026), proving Kahn's flow conjecture and deducing Kleitman's and Chvátal's conjectures.
   - **David Ellis, Yuval Filmus, and Ehud Friedgut**, *Chvátal's conjecture: a proof from The Book*, [`arXiv:2609.28404`](https://arxiv.org/abs/2609.28404) (23 September 2026), giving a short Fourier-spectral proof building on Chang–Liu–Liu.

## Clean-Room Provenance & Statement Fidelity

- **100% Clean-Room Authorship**: Every proof line in [`Erdos701.lean`](Erdos701.lean) and [`StatementAudit.lean`](StatementAudit.lean) was authored completely from scratch against Mathlib `v4.33.1`, without reading, copying, vendoring, or adapting any third-party Lean proof code.
- **Formal Statement Attribution**: The statement signature of `Erdos701.erdos_701` (`∀ {X : Type} [Nonempty X] [Fintype X] (F : Set (Set X)), IsLowerSet F → ∃ x : X, ∀ᵉ (F' ⊆ F), F'.Intersecting → (#F' ≤ #{ A : Set X | A ∈ F ∧ x ∈ A })`) matches [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/b576d527b271b936f9e61c0e367c302d7386bc80/FormalConjectures/ErdosProblems/701.lean) (`FormalConjectures/ErdosProblems/701.lean`, commit `b576d527b271b936f9e61c0e367c302d7386bc80`, Apache-2.0, Copyright 2025 The Formal Conjectures Authors).
- **Spectral-Library-Free Design & Multi-Formulation Coverage**: Adapting the Fourier-convolution operator $K(A, B) = \widehat{h}(A \triangle B)$ of Ellis–Filmus–Friedgut (`arXiv:2609.28404`), our formalization replaces matrix eigenvalue theory with an elementary physical-space eigenfunction identity, maximum-cardinality-peeling triangular Gram–Schmidt orthonormalization, and a row-wise Bessel inequality. Alongside `Erdos701.erdos_701`, we prove the universe-polymorphic `Set.ncard` theorem (`Erdos701.erdos_701_ncard`), the `Finset` downset theorem (`Erdos701.chvatal_conjecture_finset`), Chvátal's `[Ch74]` vertex-in-edge hypergraph formulation (`Erdos701.chvatal_conjecture_hypergraph_vertex`), and principal-downset sharpness (`Erdos701.principal_downset_sharpness`), all cross-checked from raw membership primitives in [`StatementAudit.lean`](StatementAudit.lean).

## AI Disclosure

AI coding and formal-verification assistance was used in authoring the clean-room Lean 4 proof scripts, documentation, and verification checks. All Lean proofs are machine-checked end-to-end by the Lean 4.33.1 kernel and `leanchecker --fresh` with zero `sorry`, zero `admit`, zero `native_decide`, and only the three standard classical axioms `propext`, `Classical.choice`, and `Quot.sound`.
