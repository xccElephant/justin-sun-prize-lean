# JSP-000571 · Erdős Problem #701 (Chvátal's Conjecture) — Clean-Room Lean 4 Formalization

Complete, unconditional, 100% clean-room, zero-custom-axiom Lean 4 (`v4.33.1`) formalization of **Chvátal's Conjecture** (**JSP-000571**, Erdős Problem #701, Chvátal 1972/1974 `[Ch74, pp. 61–66]`, Erdős 1981 `[Er81]`):

> **JSP-000571**: *In a hereditary set family, is a largest pairwise-intersecting subfamily always obtainable by taking all members containing one fixed element?*
>
> **Chvátal `[Ch74]` / Erdős `#701`**: *Let $\mathcal{F}$ be a finite family of finite sets closed under taking subsets (if $B \subseteq A \in \mathcal{F}$ then $B \in \mathcal{F}$). Then there exists an element $x$ such that for every pairwise-intersecting subfamily $\mathcal{F}' \subseteq \mathcal{F}$,*
> $$|\mathcal{F}'| \le |\{A \in \mathcal{F} : x \in A\}|.$$

**Answer: Yes.** Mathematically resolved in September 2026 by Fan Chang, Hong Liu, and Miao Liu ([`arXiv:2609.19123`](https://arxiv.org/abs/2609.19123)), Peter Keevash ([`arXiv:2609.23595`](https://arxiv.org/abs/2609.23595)), and David Ellis, Yuval Filmus, and Ehud Friedgut ([`arXiv:2609.28404`](https://arxiv.org/abs/2609.28404)). This repository provides an independent, self-contained, 100% clean-room Lean 4 (`v4.33.1`) formalization by Chucheng Xiang (`@xccElephant`), adapting the Boolean Fourier convolution construction via physical-space eigenfunctions, triangular Gram–Schmidt orthonormalization, and a row-wise Bessel inequality without requiring spectral-theorem library imports.

---

## Verified Formal Targets

| Module | Declaration | Mathematical Content |
| :--- | :--- | :--- |
| `Erdos701` | `Erdos701.erdos_701` | Exact `Cardinal` signature of [`FormalConjectures/ErdosProblems/701.lean`](https://github.com/google-deepmind/formal-conjectures/blob/b576d527b271b936f9e61c0e367c302d7386bc80/FormalConjectures/ErdosProblems/701.lean): `#F' ≤ #{ A : Set X | A ∈ F ∧ x ∈ A }` for every `IsLowerSet F` and `F'.Intersecting` |
| `Erdos701` | `Erdos701.erdos_701_ncard` | Universe-polymorphic `Set.ncard` downset star bound `F'.ncard ≤ {A | A ∈ F ∧ x ∈ A}.ncard` |
| `Erdos701` | `Erdos701.chvatal_conjecture_finset` | Finite `Finset (Finset X)` hereditary family theorem `I.card ≤ (D.filter (x₀ ∈ ·)).card` |
| `Erdos701` | `Erdos701.chvatal_conjecture_hypergraph_vertex` | Chvátal's `[Ch74]` hereditary hypergraph theorem guaranteeing `{x₀} ∈ D` whenever `∃ E ∈ D, E.Nonempty` (with no `[Nonempty X]` typeclass assumption) |
| `Erdos701` | `Erdos701.principal_downset_sharpness` | Exact star size `2 ^ (S.card - 1)` and complement-pairing optimality on principal downsets `S.powerset` |
| `StatementAudit` | `StatementAudit.audit_erdos_701_cardinal` / `audit_erdos_701_ncard` / `audit_chvatal_finset` / `audit_chvatal_hypergraph_vertex` | Independent first-principles theorems reconstructed from raw membership (`RawHereditarySet`, `RawIntersectingSet`, `RawHereditaryFinset`, `RawIntersectingFinset`) with zero `IsLowerSet` or `Set.Intersecting` dependencies |

### Trust & Completeness Summary

- **`sorry` / `admit` count**: `0`
- **`native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`**: `0`
- **Umbrella `Mathlib` / `Mathlib.Tactic` imports**: `0` (surgical `Mathlib.*` imports only)
- **Transitive axioms (`#print axioms`)**: strictly `[propext, Classical.choice, Quot.sound]`
- **Kernel replay**: verified via both `lake env leanchecker -v Erdos701 StatementAudit` and fresh empty-environment replay `lake env leanchecker --fresh Erdos701`

---

## Pinned Toolchain & Reproduction

- **Repository**: [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean) (standalone orphan branch `jsp-000571-lean`)
- **Lean Toolchain**: `leanprover/lean4:v4.33.1` ([`lean-toolchain`](lean-toolchain))
- **Mathlib Revision**: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`, pinned in [`lake-manifest.json`](lake-manifest.json))

```bash
git clone --branch jsp-000571-lean --single-branch https://github.com/xccElephant/justin-sun-prize-lean.git jsp-000571-lean
cd jsp-000571-lean
lake exe cache get
timeout 180s lake --wfail build
timeout 120s lake env lean StatementAudit.lean
timeout 180s lake env leanchecker -v Erdos701 StatementAudit
timeout 300s lake env leanchecker --fresh Erdos701
```

---

## Exposition & Attribution

- Mathematical proof walkthrough: [`paper/PROOF.md`](paper/PROOF.md) and [`paper/erdos701.tex`](paper/erdos701.tex)
- Authorship, prior-work credits, and AI disclosure: [`AUTHORS.md`](AUTHORS.md)
