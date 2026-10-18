# Independent review: Erdős 727 carry increments

Reviewed 2026-10-19 by an agent who did not implement these five lemmas. `JspBounties/Erdos727_273.lean` was read only. Scope: actual new diff at lines483–592, exact factorial factor, Kummer/log bounds, and whether the reductions assume the missing existence theorem. No new problem was researched.

## Verdict

No blocking issue found in the five added lemma statements or proofs. The rising-factorial factor has no off-by-one error, and the carry-count interval includes exactly the required positive levels through floor(log_p(2n)). Empty-interval and zero-parameter cases are handled by natural-number arithmetic without adding a hidden premise. The missing mixed infinitude theorem remains missing; these increments must be described as arithmetic reductions/construction steps, not its resolution.

## Exact factorial factor

Reviewed `mixed_factorial_dvd_iff` at line532 against installed Mathlib `Nat.ascFactorial_eq_prod_range` and `Nat.factorial_mul_ascFactorial`.

Mathlib defines `(n+1).ascFactorial k = ∏ i<k, (n+1+i)`, so it contains exactly k factors, from n+1 through n+k. In particular,

`(n+k)! = n! * (n+1).ascFactorial k`,

`(n+1)! = n! * (n+1)`.

Their product therefore equals `Q*(n!*n!)` with `Q=(n+1)*(n+1).ascFactorial k`. The central-binomial identity gives `(2n)! = centralBinom(n)*(n!*n!)`. The proof cancels the same nonzero factorial-square factor in divisibility; it does not use truncated natural division to approximate a quotient.

Boundary checks:

- k=0: ascending factorial is 1, so Q=n+1. The left side is n!*(n+1)!, not the squared-factorial expression.
- k=1: Q=(n+1)^2, exactly the existing squared `(n+1)!` criterion.
- k=2: Q=(n+1)^2*(n+2), with no additional n+3 factor and no missing n+2 factor.
- For k≥1 the general formula is `(n+1)^2 * ∏_{j=2}^k (n+j)`; this rewritten product formula should not be applied at k=0.
- n=0: centralBinom(0)=1. Both sides are true for k=0,1 and false for k≥2, as the exact factor dictates.

## Carry-count/log boundary

Reviewed `mixed_factorial_dvd_iff_carry_count` at line548, the existing lower-bound helper at line66, and installed Mathlib `Nat.factorization_choose'` in `Data/Nat/Choose/Factorization.lean:114`.

The library theorem counts carries in `Ico 1 b` provided `log p (n+k) < b`. Applying it to choose(n+n,n) with `b=log p(n+n)+1` satisfies that strict bound directly. `Ico 1 (log+1)` means **1≤i≤log**, so the highest relevant level is included. Starting at 1 is correct: level0 has modulus1 and cannot carry. The comparison uses `p^i ≤ 2*(n mod p^i)`, including equality, as required by the carry criterion.

No larger level can contribute: if there is a carry, `p^i ≤ 2*(n mod p^i) ≤ 2n`, so i≤log_p(2n). Equivalently, above the log bound p^i>2n and n mod p^i=n, making a carry impossible. This is also the explicit argument used by the existing lower-bound helper to place arbitrary carrying levels inside the bounded set.

At n=0 the logarithm is the Nat.log convention at zero, and the interval is empty; the valuation of centralBinom(0)=1 is zero. For prime p>2n the interval is likewise empty. At a top-bound equality p^i=2n, the corresponding level is included and the ≤ carry predicate does not discard it.

The criterion quantifies only over primeFactors(Q), a legitimate reduction because Q>0 for every n,k. Primality is obtained from membership, so Nat.log bases0/1 are never used as primes. In the reverse implication, factorization at every index outside the support is zero; the proof explicitly fills those cases before applying `factorization_le_iff_dvd`. It does not confuse a condition on some prime factors with a condition on all factors.

## Offset and interval lemmas

`carry_of_dvd_offset`: premises 0<j and 2j≤m imply m>0 and j<m. Since m divides n+j, the positive sum `(n mod m)+j` lies below2m and is a multiple of m; it must equal m. Hence the remainder is m−j≥m/2, giving the desired carry. The equality boundary 2j=m is valid. Positivity of j rules out the zero-multiple case.

`prime_pow_dvd_centralBinom_of_offset`: for every level 1≤i≤e, p^i divides n+j and p^i≥p≥2j, so the arithmetic lemma supplies that level's carry. The Finset Icc1e has cardinality e, with no duplicate levels. At e=0 it is empty and the conclusion is merely 1 divides centralBinom(n). This is a sufficient condition, not a converse.

`prime_pow_dvd_centralBinom_of_offset_interval`: levels are exactly t≤i≤L. The premise t≥1 makes them valid positive carrying levels; 2A≤p^t propagates to each level, and p^L|n+A propagates downwards. The number of levels is `L+1−t` in truncated Nat subtraction. If L<t this is0 and the conclusion is1 divisibility; if L=t there is exactly one level. No L≥t hypothesis is missing. Equality2A=p^t is allowed. Although t,L can be arbitrary, the lemma does not produce the congruence hcong or prime parameters: those remain premises of this arithmetic step.

None of these five lemmas assumes the target factorial divisibility or central-binomial divisibility to prove it. The only equivalences reduce an arbitrary fixed n,k to its exact arithmetic criterion. The construction needed to realize enough congruences in infinitely many suitable prime pairs is absent, as the source comments state.

## Evidence reviewed and independent regressions

Read `erdos727/exact-checks.lean`, `exact-checks.log`, `RESULT.json`, `STATUS.md`, `source.sha256`, and `kernel-replay.exit`. No file literally named RESULT0 was found; the available RESULT.json records source_compile_exit, exact_checks_exit, all_theorem_audit_exit and kernel_replay_exit all equal0, and the explicit kernel-replay.exit is0.

The source SHA-256 is `92f584dcea5e785793ec7a0ce56befd027c6bdc873e6757a37fc61c135bc3f79`, matching source.sha256. The exact-checks file begins with the identical current source and adds the universal iff type check and p=7,n=47,j=2,e=2 regression. Its log shows the five new theorem axiom closures contain only propext, Classical.choice and Quot.sound (the elementary offset lemma does not require choice). RESULT.json records170 audited theorem declarations and no nonstandard axioms. These are existing kernel/build records read by this reviewer; no redundant large-file Lean build was started.

Independent exact-integer regressions additionally passed:

- 1,053 factorial/Q and prime-factor carry-criterion comparisons for 0≤n≤80 and 0≤k≤12.
- 3,321 direct central-binomial valuation/carry-count equalities for primes below180.
- 24,636 applicable offset cases, including e=0 and equality boundaries.
- 106,855 applicable interval cases, including L<t, L=t and equality2A=p^t.

Parameters j,A ran1–8; e,L ran0–4; t ran1–4. Results are saved in `erdos727/independent-review-regressions.json`. The checks supplement the universal kernel proofs; they do not establish infinitude.

## Batch scope

Safe description: five exact carry/factorial reduction lemmas added; existing k=1 proof and covering-system code unchanged by this increment. Unsafe description: “mixed theorem proved for every k” or “squared-factorial conjecture proved for k≥2.” RESULT.json explicitly marks both broader targets NOT PROVED and k_1_2 undeclared, consistent with the actual diff.
