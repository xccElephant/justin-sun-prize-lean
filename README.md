# JSP-000849 · Erdős Problem #1019 — Complete Lean 4 Formalization

Complete, unconditional, 100% clean-room, zero-custom-axiom Lean 4 formalization resolving **JSP-000849** (Erdős Problem #1019, Erdős 1969/1971 `[Er69c, pp. 16–17]`, `[Er71, item 13, p. 102]`):

> **JSP-000849**: *Must every dense graph contain a nontrivial maximal planar subgraph?*
>
> **Erdős `[Er69c, p. 17]` / `[Er71, p. 102]`**: *A planar graph on $m$ vertices with $3m - 6$ edges is called saturated. Does every graph on $n$ vertices with $\lfloor n^2 / 4 \rfloor + \lfloor (n + 1) / 2 \rfloor$ edges contain a saturated planar graph with $> 3$ vertices?*

**Answer: Yes.** Every finite simple graph $G$ on $n \ge 1$ vertices with at least (or, in particular, exactly) $\lfloor n^2/4 \rfloor + \lfloor (n + 1)/2 \rfloor$ edges contains either $K_4$ or a bipyramid $B_\ell = C_\ell \vee 2K_1$ ($\ell \ge 3$). Both $K_4$ and $B_\ell$ ($\ell \ge 3$) admit explicit non-crossing topological Jordan-arc plane drawings in $\mathbb{R}^2$ and have $m > 3$ vertices and $3m - 6$ edges.

---

## Verified Formal Targets

Every line of this package—including the Jordan-arc topological `PlaneDrawing` definition in $\mathbb{R}^2$, straight-line Fáry-segment embeddings of $K_4$ and $B_\ell$, and the Simonovits–Cambie extremal stability induction—is written 100% from scratch, with an independent first-principles semantic bridge in [`StatementAudit.lean`](StatementAudit.lean):

| Module | Declaration | Mathematical Content |
| :--- | :--- | :--- |
| `Erdos1019.Planarity` | `Erdos1019.PlaneDrawing` / `Erdos1019.IsPlanar` | Genuine topological plane drawing in `ℝ × ℝ`: injective vertex placement `W ↪ ℝ × ℝ` and continuous injective Jordan arcs `Set.Icc (0 : ℝ) 1 → ℝ × ℝ` meeting at most at shared endpoints |
| `Erdos1019.Bipyramid` | `Erdos1019.completeGraph_fin4_isPlanar` | $K_4$ (`⊤ : SimpleGraph (Fin 4)`) is topologically planar in `ℝ × ℝ` with $6 = 3(4) - 6$ edges |
| `Erdos1019.Bipyramid` | `Erdos1019.bipyramidGraph_isPlanar` | Every bipyramid $B_\ell = C_\ell \vee 2K_1$ ($\ell \ge 3$) is topologically planar in `ℝ × ℝ` with $3\ell = 3(\ell+2) - 6$ edges |
| `Erdos1019.Extremal` | `Erdos1019.simonovits_stability` | Every $n$-vertex graph ($n \ge 1$) with $e(G) \ge \lfloor n^2/4 \rfloor + \lfloor (n-1)/2 \rfloor$ contains $K_4$ or $B_\ell$ ($\ell \ge 3$), or else has $e(G) = \lfloor n^2/4 \rfloor + \lfloor (n-1)/2 \rfloor$ and is a balanced tree-join $T_a \vee \overline{K_b}$ |
| `Erdos1019` | `Erdos1019.erdos_1019` | Exact `=` threshold (`[Er69c]`, `[Er71]`): every graph $G$ on $n \ge 1$ vertices with $e(G) = \lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ contains a planar subgraph $H$ on $m > 3$ vertices with $3m - 6$ edges |
| `Erdos1019` | `Erdos1019.erdos_1019_ge` / `erdos_1019_fin` | Monotone `≥` threshold for all $n \ge 1$ (and `erdos_1019_ge_of_four_le` for $n \ge 4$) |
| `StatementAudit` | `StatementAudit.audit_erdos_1019_exact` / `audit_erdos_1019_ge` | Independent first-principles theorems reconstructed directly from Mathlib primitives (`RawJordanPlanar`, `rawEdgeCount`, `RawContainsOnFin`), with `isPlanar_iff_rawJordanPlanar` equivalence |

### Trust & Completeness Summary

- **`sorry` / `admit` count**: `0`
- **`native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`**: `0`
- **Transitive axioms (`#print axioms`)**: strictly `[propext, Classical.choice, Quot.sound]`
- **Kernel replay**: verified via both `lake env leanchecker -v Erdos1019 StatementAudit` and fresh empty-environment replay `lake env leanchecker --fresh Erdos1019`

---

## Pinned Toolchain & Reproduction

- **Repository**: [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean) (standalone orphan branch `jsp-000849-lean`)
- **Lean Toolchain**: `leanprover/lean4:v4.33.1` ([`lean-toolchain`](lean-toolchain))
- **Mathlib Revision**: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`, pinned in [`lake-manifest.json`](lake-manifest.json))

```bash
git clone --branch jsp-000849-lean --single-branch https://github.com/xccElephant/justin-sun-prize-lean.git jsp-000849-lean
cd jsp-000849-lean
lake exe cache get
timeout 180s lake --wfail build
timeout 120s lake env lean StatementAudit.lean
timeout 180s lake env leanchecker -v Erdos1019 StatementAudit
timeout 300s lake env leanchecker --fresh Erdos1019
```

---

## Exposition & Attribution

- **Mathematical Exposition**: [`paper/PROOF.md`](paper/PROOF.md) and [`paper/erdos1019.tex`](paper/erdos1019.tex)
- **Authorship, Prior Credits & Clean-Room Disclosure**: [`AUTHORS.md`](AUTHORS.md)
  - 100% clean-room Lean 4 formalization by **Chucheng Xiang (`@xccElephant`)**.
  - Mathematical solution credits: **Miklós Simonovits** (1970 PhD thesis, Chapter 9; cited in `[Er71, p. 102]`) and **Stijn Cambie** (November 2025 public proof exposition on `erdosproblems.com/1019`).
