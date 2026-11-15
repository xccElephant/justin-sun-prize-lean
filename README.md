# JSP-000816 · Erdős Problem #983 — Complete Lean 4 Formalization

Complete, unconditional, zero-custom-axiom Lean 4 formalization resolving **JSP-000816** (Erdős Problem #983, Part (i), Erdős–Straus 1970 `[Er70b, pp. 138, 140]`):

> **JSP-000816**: *If an integer set is larger than the prime count in its range, must some collection of its elements be supported on relatively few small primes?*
>
> **Erdős–Straus `[Er70b]` (Part i)**: *Let $n \ge 2$ and $\pi(n) < k \le n$. Let $f(k, n)$ be the smallest integer $r$ such that in any $A \subseteq \{1, \dots, n\}$ of size $|A| = k$ there exist primes $p_1, \dots, p_r$ such that $> r$ many $a \in A$ are only divisible by primes from $\{p_1, \dots, p_r\}$. Is it true that $2\pi(n^{1/2}) - f(\pi(n) + 1, n) \to \infty$ as $n \to \infty$?*

**Answer: No.** While $f(\pi(n) + 1, n) \le 2\pi(\lfloor\sqrt{n}\rfloor) + 1$ holds for every $n \in \mathbb{N}$, equality $f(\pi(n) + 1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1$ holds for infinitely many $n \ge 2$, so $2\pi(\lfloor\sqrt{n}\rfloor) - f(\pi(n) + 1, n) = -1$ infinitely often and does not tend to $+\infty$.

---

## Verified Formal Targets

All core definitions (`Erdos983.numSmooth`, `Erdos983.f`) and main theorem signatures match [`FormalConjectures/ErdosProblems/983.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/983.lean) character-for-character, with an independent first-principles semantic bridge in [`StatementAudit.lean`](StatementAudit.lean):

| Module | Declaration | Mathematical Content |
| :--- | :--- | :--- |
| `Erdos983` | `Erdos983.erdos_983.variants.upper_bound` | $\forall n \in \mathbb{N},\; f(\pi(n)+1, n) \le 2\pi(\lfloor\sqrt{n}\rfloor) + 1$ (Erdős–Straus `[Er70b, (14)]`) |
| `Erdos983` | `Erdos983.exists_pomerance_prime_index` | $\forall K \ge 2,\; \exists M \ge K,\; \forall 1 \le i \le M,\; p_{M-i}p_{M+i} < p_M^2$ (Pomerance `[Po79]`) |
| `Erdos983` | `Erdos983.exact_equality_at_pomerance_index` | At $n = p_M^2 - 1$, $f(\pi(n)+1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1 = 2M + 1$ |
| `Erdos983` | `Erdos983.erdos_983.variants.upper_bound_attained_frequently` | $\exists^\infty n \in \mathbb{N},\; f(\pi(n)+1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1$ (`Filter.Frequently`) |
| `Erdos983` | `Erdos983.erdos_983.variants.infinite_exact_equality` | $\{n \ge 2 \mid f(\pi(n)+1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1\}$ is infinite |
| `Erdos983` | `Erdos983.erdos_983.parts.i` | $\neg\,\mathrm{Tendsto}\big(n \mapsto 2\pi(\lfloor\sqrt{n}\rfloor) - f(\pi(n)+1, n),\; \mathrm{atTop},\; \mathrm{atTop}\big)$ |
| `StatementAudit` | `StatementAudit.audit_erdos_983_part_i_raw` | `Filter`-free, `primeFactors`-free disproof reconstructed directly from `Nat.Prime` and `(· ∣ ·)` |

### Trust & Completeness Summary

- **`sorry` / `admit` count**: `0`
- **`native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`**: `0`
- **Transitive axioms (`#print axioms`)**: strictly `[propext, Classical.choice, Quot.sound]`
- **Kernel replay**: verified via both `lake env leanchecker -v Erdos983 StatementAudit` and fresh empty-environment replay `lake env leanchecker --fresh Erdos983`

---

## Pinned Toolchain & Reproduction

- **Repository**: [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean) (standalone orphan branch `jsp-000816-lean`)
- **Lean Toolchain**: `leanprover/lean4:v4.33.1` ([`lean-toolchain`](lean-toolchain))
- **Mathlib Revision**: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`, pinned in [`lake-manifest.json`](lake-manifest.json))

```bash
git clone --branch jsp-000816-lean --single-branch https://github.com/xccElephant/justin-sun-prize-lean.git jsp-000816-lean
cd jsp-000816-lean
lake exe cache get
timeout 180s lake --wfail build
timeout 120s lake env lean StatementAudit.lean
timeout 180s lake env leanchecker -v Erdos983 StatementAudit
```

---

## Exposition & Attribution

- **Mathematical Exposition**: [`paper/PROOF.md`](paper/PROOF.md) and [`paper/erdos983.tex`](paper/erdos983.tex)
- **Authorship, Prior Credits & Scope Disclosure**: [`AUTHORS.md`](AUTHORS.md)
  - Lean 4 formalization by **Chucheng Xiang (`@xccElephant`)**.
  - Mathematical solution credits: Paul Erdős & Ernst G. Straus (1970), Carl Pomerance (1979), Liam Price & Nat Sothanaphan (2026).
  - Covers the complete literal binary yes/no statement of `JSP-000816` (`erdos_983.parts.i` and `erdos_983.variants.upper_bound`); the separate open-ended asymptotic question for general $\pi(n)+1 < k = o(n)$ (`erdos_983.parts.ii` in `[Er70b]`, omitted from the `JSP-000816` catalog entry) remains open and is not claimed.
