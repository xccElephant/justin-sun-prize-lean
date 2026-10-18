# Erdos727 mixed factorial repair — incomplete main theorem

The requested `Erdos727.erdos_727.variants.k_1_2` is NOT proved or declared.
The squared-factorial conjecture for k≥2 is NOT proved or declared.
No definition or existing theorem has been weakened.

## Proved increments

- `carry_of_dvd_offset`: if 0<j, 2j≤m and m divides n+j, doubling n carries modulo m.
- `prime_pow_dvd_centralBinom_of_offset`: if p is prime, 0<j, 2j≤p and p^e divides n+j, then p^e divides centralBinom n.
- `mixed_factorial_dvd_iff`: the mixed quotient is equivalent to
  `(n+1)*(n+1).ascFactorial k | centralBinom n`.
- `mixed_factorial_dvd_iff_carry_count`: an exact iff using the finite Kummer carry set,
  with levels in Ico 1 (log_p(2n)+1). All inputs and outputs are explicit; no target divisibility is assumed.
- `prime_pow_dvd_centralBinom_of_offset_interval`: from p^L | n+A, 2A≤p^t and t≥1, the L+1−t distinct carry levels give p^(L+1−t) | centralBinom n.

These are necessary construction/reduction steps, not a completion of mixed infinitude.
The arbitrary certificate wrapper explored in mixed-test.lean was not added to the project file.

## Primary literature actually read

Erdős, Graham, Ruzsa, Straus, On the prime factors of binomial(2n,n),
Math. Comp. 29 (1975), 83–92.
Author-hosted scan: https://mathweb.ucsd.edu/~ronspubs/75_03_prime_factors.pdf
Saved as egrs.pdf. Page 90 is egrs-08.png, with OCR in egrs-08.txt.
Its final paragraphs contain an unnumbered assertion that for every k infinitely
many n satisfy (n+k)!(n+1)! | (2n)!, even for k<c log n, attributing the method to Balakran.
It does not state a construction lemma or provide the proof of the generalization.

H. Balakran, On the values of n which make (2n)!/(n+1)!(n+1)! an integer,
J. Indian Math. Soc. 18 (1929), 97–100: cited in EGRS75 page 92 (egrs-10.txt).
The original Balakran article has NOT been obtained or read. The repository's
existing heading uses the spelling Balakram; the primary EGRS75 scan uses Balakran.
No outside Lean code has been copied. Existing k1 code is reused with its existing authorship.
FC-727.lean preserves the upstream copyright/license and exact requested statement.

## Mathematical route and precise missing construction

Write B=centralBinom n. The required factor is
Q=(n+1)^2 * product(j=2..k)(n+j), hence
v_r(Q)=2v_r(n+1)+sum(j=2..k)v_r(n+j).
For r>2k, at most one term in this short block is divisible by r.
The offset carry lemma supplies all valuation levels for j≥2.
For n+1, the existing Balakran primepair families n=pq−1 and n=4pq−1 supply the double valuation when their ratio conditions hold.

For small primes r≤2k, put A=k! (k≥2) and prescribe n≡−A modulo r^L.
Then for i with r^i≥2A and i≤L, n mod r^i=r^i−A gives a carry.
Taking L large would produce arbitrarily many carries. If r^L exceeds the
relevant valuations of A−j, the valuations of n+j are fixed (A−j is nonzero:
A>k for k≥3). The exceptional k=2,A=2,j=2 must use A>k instead, e.g. A=(k+1)!.
Thus A=(k+1)! is the safe uniform choice for this proposed route.

The unresolved step is realizing all prescribed small-prime congruences inside
infinitely many valid primepair families while retaining their relative gaps.
Ordinary Bertrand gives gaps but no residue conditions; the local Dirichlet
prime-in-AP theorem gives residues but not relative gaps between the two required
residue classes. A quantified AP prime-gap theorem or a different Balakran
construction is still needed. We have not proved this simultaneous construction.
It is not legitimate to treat carry certificates as an existence hypothesis and
then claim the requested infinite theorem.

## Verification

Original missing target red.log fails with unknownIdentifier k_1_2.
New carrying targets: carry-red.log and exact-red.log fail before implementation.
Actual project build and new olean: green.log.
Public exact types and a concrete p=7,n=47,j=2,e=2 regression: exact-checks.log.
All theorem axiom audit: audit.log. New olean kernel replay: kernel-replay.log.
No Git commits, pushes or external PRs. Only this directory and Erdos727_273.lean are written.

Final checks: project compilation, exact regressions, and all-theorem audit exited 0.
Kernel replay of the new olean exited 0. Audit: 170 theorem declarations, only
propext, Classical.choice, Quot.sound. Pre-existing bodies unchanged byte-for-byte.
