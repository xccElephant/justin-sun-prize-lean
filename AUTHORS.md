# Authorship, Provenance, and Attribution

## Lean 4 Formalization Author

- **Name**: Chucheng Xiang
- **GitHub Account**: [`@xccElephant`](https://github.com/xccElephant)
- **Repository & Branch**: [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean), standalone orphan branch `jsp-000816-lean`
- **Claimed Contribution Role**: **Lean 4 Formalization Author** (first complete, unconditional, zero-custom-axiom Lean 4 formalization of Erdős Problem #983, Part (i) and the Erdős–Straus exact upper bound, corresponding to the literal binary statement of `JSP-000816`).
- **Toolchain & Dependencies**:
  - Lean 4: `leanprover/lean4:v4.33.1`
  - Mathlib4: `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`)

## Mathematical Attribution (Prior Informal Results)

No mathematical-solver priority is claimed over the prior informal mathematical results credited below:

1. **Exact Upper Bound (`erdos_983.variants.upper_bound`)**:
   - **Authors**: Paul Erdős and Ernst G. Straus (1970).
   - **Source**: P. Erdős, *Some applications of graph theory to number theory*, Proc. Second Chapel Hill Conf. on Combinatorial Mathematics and its Applications (Univ. North Carolina, Chapel Hill, N.C., 1970), pp. 136–145, inequality (14) on p. 139.
2. **Symmetric Prime Product Inequality (`exists_pomerance_prime_index`)**:
   - **Author**: Carl Pomerance (1979).
   - **Source**: C. Pomerance, *The prime number graph*, Math. Comp. 33 (1979), pp. 399–408, Corollary after Theorem 2.2 (proved in `Erdos983.lean` via a self-contained pure-$\mathbb{N}$ global-maximizer and central-binomial factorization argument, avoiding real logarithms and concave-hull recursion).
3. **Negative Resolution of Part (i) via Zigzag Semiprime Path (`erdos_983.parts.i`)**:
   - **Contributors**: Liam Price (assisted by GPT-5.5 Pro) and Nat Sothanaphan (April 2026).
   - **Source**: Public discussion on `erdosproblems.com` Problem #983 ([post #6104](https://www.erdosproblems.com/forum/thread/983#post-6104) and [post #6525](https://www.erdosproblems.com/forum/thread/983#post-6525)).

## Statement Provenance and Scope Disclosure

- **Canonical Lean Statement Reference**: The definitions `Erdos983.numSmooth` and `Erdos983.f`, as well as the theorem signatures `Erdos983.erdos_983.parts.i`, `Erdos983.erdos_983.variants.upper_bound`, and `Erdos983.erdos_983.variants.le_primeCounting`, match [`FormalConjectures/ErdosProblems/983.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/983.lean) (Apache-2.0, The Formal Conjectures Authors).
- **Exact Scope Coverage**:
  - `JSP-000816` in `TheJustinSunPrize/awards` (`problems/catalog-0801-0900.md#JSP-000816`) states the single binary yes/no question:
    > *"If an integer set is larger than the prime count in its range, must some collection of its elements be supported on relatively few small primes?"*
  - This repository proves unconditionally in Lean 4 both the sharp Erdős–Straus upper bound $f(\pi(n)+1, n) \le 2\pi(\lfloor\sqrt{n}\rfloor) + 1$ for all $n \in \mathbb{N}$ and that equality $f(\pi(n)+1, n) = 2\pi(\lfloor\sqrt{n}\rfloor) + 1$ holds for infinitely many $n \ge 2$, thereby completely resolving the binary question (`erdos_983.parts.i`: $2\pi(n^{1/2}) - f(\pi(n)+1, n) \not\to \infty$) in the negative.
  - Historical note: `[Er70b, p. 140]` and `erdosproblems.com/983` also mention a separate open-ended asymptotic estimation sentence (*"In general, estimate $f(k,n)$, particularly when $\pi(n)+1 < k = o(n)$"*, recorded as `erdos_983.parts.ii` in `FormalConjectures`), which is omitted from the `JSP-000816` catalog description and is not addressed here.

## AI Disclosure

AI coding and formal-verification assistance was used in drafting proof scripts, documentation, and verification checks. All Lean proofs are machine-checked end-to-end by the Lean 4.33.1 kernel and `leanchecker` with zero `sorry`, zero `admit`, zero `native_decide`, and only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
