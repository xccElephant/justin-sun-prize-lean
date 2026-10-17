# Erdős Problem 348 (`JSP-000290`) — Lean 4 Formalization Report

## 1. Executive Summary

- **Problem:** Erdős Problem 348 (`JSP-000290`, posed by Graham (1971) and Erdős–Graham (1980, p. 57)) asks:
  > For what values of $0 \le m < n$ is there a complete nondecreasing sequence $A = (a_i)$ of integers such that:
  > 1. $A$ remains complete after removing any $m$ elements, but
  > 2. $A$ is not complete after removing any $n$ elements?
- **Mathematical Resolution:** Jesse Geneson (*Deletion thresholds and exponential examples for complete sequences*, `arXiv:2609.25107`, September 2026, Theorem 1) proved that the admissible pairs $(m, n)$ with $0 \le m < n$ are **exactly those with $m \le 1$**.
- **Formalization Status:** **100% Complete & Kernel-Verified.**
  - File: `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos348.lean`
  - Compiler verification: `/Users/xcc/Project/justin-sun-prize-lean/check_lean.sh /Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos348.lean` exits with code `0` in ~14 seconds.
  - Axiom verification (`#print axioms Erdos348.erdos_348`):
    ```
    'Erdos348.erdos_348' depends on axioms: [propext, Classical.choice, Quot.sound]
    ```
  - Zero `sorry`, zero `admit`, zero custom `axiom` declarations.

---

## 2. Exact Statement Verified (Matching `FormalConjectures/ErdosProblems/348.lean`)

The definitions `subseqSums'`, `IsAddCompleteNatSeq'`, `Erdos348.erdos_348.answer`, and theorem `Erdos348.erdos_348` match the Google DeepMind `FormalConjectures` specification verbatim:

```lean
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

def IsAddCompleteNatSeq' (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

namespace Erdos348

def erdos_348.answer : Set (ℕ × ℕ) := {(m, n) : ℕ × ℕ | m < n ∧ m ≤ 1}

theorem erdos_348 :
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
        (_ : ∀ t, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) } =
    erdos_348.answer
```

---

## 3. Architecture of the Lean 4 Proof (`JspBounties/Erdos348.lean`)

The formalization is self-contained on top of 7 targeted Mathlib modules (`Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Algebra.Order.BigOperators.Group.Finset`, `Mathlib.Order.Filter.AtTopBot.Basic`, `Mathlib.Order.Interval.Finset.Nat`, `Mathlib.Data.Finset.Max`, `Mathlib.Data.Finset.Update`, `Mathlib.Data.Nat.Fib.Basic`) and is structured into four main sections:

### Section 1: Subset-Sum & Deletion Infrastructure
- `sum_updateFinset_zero_eq_sum_sdiff` and `mem_subseqSums'_updateFinset_iff`: Characterizes subset sums of `Function.updateFinset a s 0` as subset sums `∑ i ∈ B, a i` over finite index sets `B` disjoint from the deleted index set `s`.
- `isAddCompleteNatSeq'_updateFinset_mono`: Deleting fewer indices preserves completeness (`s ⊆ t` implies `subseqSums' (updateFinset a t 0) ⊆ subseqSums' (updateFinset a s 0)`).

### Section 2: The Two Existence Constructions ($m = 0$ and $m = 1$)
- **Case $m = 0, n \ge 1$ (`exists_for_m_eq_zero`):**
  - Uses $a_i = 2^i$.
  - `pow_two_repr` and `pow_two_complete_zero`: Binary expansion represents every natural number $x < 2^n$ using indices in `range n`.
  - `pow_two_not_complete_of_nonempty`: If $j \in t$, any subset sum avoiding index $j$ decomposes into a prefix sum $< 2^j$ and a tail sum divisible by $2^{j+1}$, so $2^{j+1} T + 2^j$ is never represented.
- **Case $m = 1, n \ge 2$ (`exists_for_m_eq_one`):**
  - Uses `fibSeq i = Nat.fib (i + 1)` ($1, 1, 2, 3, 5, \dots$).
  - `fibSeq_one_del_step`, `fibSeq_one_del_repr`, and `fibSeq_complete_one`: Formalizes Brown's interval criterion after deleting any single occurrence `{j}`, showing that every integer up to the retained prefix sum is represented.
  - `fibSeq_two_del_missing`: For any two deleted indices $i < j$ and all $m \ge 0$, proves by induction on $m$ that $F_{j+2m+2} - 1 = \text{fibSeq}(j + 2m + 1) - 1$ is missing from the subset sums of `Function.updateFinset fibSeq {i, j} 0`.

### Section 3: Geneson's Central-Interval Theorem (`central_interval_thm`, Theorem 2)
For any unbounded nondecreasing positive integer sequence $B : \mathbb{N} \to \mathbb{N}$ with completeness threshold $T \ge 1$ and diverging prefix slack $\delta_j = S_j - B_j \to \infty$:
- **Cut Lemma (`central_cut`, Lemma 6):** Every $x \in [T, S_N - T]$ missing from $P_N$ satisfies $S_j = x + u$ for some cut index $j < N$ and $0 \le u < T$.
- **Close-Value Lemma (`central_close`, Lemma 7):** In any state $(j, N, E)$ with $B_j \ge T$, the first value $B_m > B_j$ satisfies $B_m - B_j \le e$ for every label $e \in E$.
- **Common-Cut Lemma (`central_common`, Lemma 8):** Any nonempty finite set $R$ of sums missing from $P_j$ with $\min R > \max(T, S_J)$, $\max R \le S_j - T$, and spread $\le 2h$ shares a single earlier cut index $l < j$, producing a new state $(l, j, E')$ with $|E'| = |R|$.
- **Potential & Quantitative Transition (`normalize_state`, `step_exists`):** Defines the state potential
  $$\Phi(j, N, E) = \begin{cases} (h+1)|E| + \min E & \text{if } B_j = B_{N-1} \text{ (constant state)}, \\ (h+1)(|E|+1) & \text{if } B_j < B_{N-1} \text{ (distinct state)}, \end{cases}$$
  bounded above by $(h+1)(|H|+1)$, and proves that for every target threshold $K'$, any normalized state with sufficiently large cut $j \ge K$ transitions to a normalized state with cut $j' \ge K'$ and strictly larger potential $\Phi$. A finite induction on $(h+1)(|H|+1) + 1 - \Phi$ then rules out normalized states at large cut indices.

### Section 4: Slack Divergence, Deletion Extension & Exclusion of $m \ge 2$
- **Order-Embedding of $\mathbb{N} \setminus D$ (`exists_complEmb`, `subseqSums'_complEmb_updateFinset`):** Re-indexes the surviving terms of $A \setminus D$ as a positive monotone sequence $B_i = A_{\text{emb}(i)}$ while preserving subset-sum sets under further deletions.
- **Divergent Prefix Slack (`slack_diverges_of_one_del`, Lemma 3):** Deduces $\delta_k(A \setminus D) \to \infty$ from completeness of $A$ after every single-element deletion.
- **Single-Element Enlargement (`extension_prop`, Proposition 5 & Lemma 4):** If $A$ tolerates every 2-element deletion and $A \setminus D$ is complete, then $D$ can be enlarged by one element $d \notin D$ while retaining completeness.
- **Exclusion of $m \ge 2$ (`not_exists_for_m_ge_two`):** Rules out bounded sequences (which are eventually constant and thus remain complete after deleting $n$ late occurrences) and shifts past any initial zeros of $a$ to apply `exists_complete_deletion_of_two_del` $n$ times, contradicting universal incompleteness at $n$ deletions.

---

## 4. Note on Erdős Problem 349 (`JSP-000291`)

We also inspected Section 5 of Geneson (2026) regarding the counterexample to Graham's conjecture on Erdős Problem 349 (`complete_for_alpha_in_Ioo_one_to_goldenRatio` in `349.lean`). Geneson's disproof relies on an external theorem of Dubickas (2006, *Glasgow Math. J.* 48, Theorem 6) — which in turn depends on Zaïmi (2006) — asserting that for a Salem number $\gamma$ with minimal polynomial $P(x) = x^{18} - x^{12} - x^{11} - x^{10} - x^9 - x^8 - x^7 - x^6 + 1$ ($P(1) = -5$) and any $\epsilon > 0$, there exists $\xi \in \mathbb{Q}(\gamma)$ whose fractional parts $\{\xi \gamma^n\}$ all lie within $\epsilon$ of $1/5$. Because Dubickas's theorem on Salem numbers is not in Mathlib and custom `axiom` declarations are forbidden by Justin Sun Prize rules, Erdős Problem 348 (`JSP-000290`) is the self-contained, 100% axiom-clean prize target from `arXiv:2609.25107`.
