# Erdős 711 parts.ii repair — 2026-10-19

Scope: JspBounties/Erdos711.lean and this directory. No Git commit or external PR.

The unconditional theorem is Erdos711.erdos_711_parts_ii, with the FC-compatible name
Erdos711.erdos_711.parts.ii. The old conditional wrapper remains unchanged.
Both minimal lengths refer to the same n and the original open intervals.

## Proof

Let F(n) denote the project's minimal open interval length at (n,n).
A finite Hall certificate at N=5000 has 416 indices and 414 neighbors in
(5000,15000]. All certificate checks use decide +kernel, not native_decide.
Thus F(5000) >= 10002.

Restriction to indices q,2q,...,Nq, followed by division by q, proves
q*(N+F(N)-1) < n+F(n) whenever q>0 and q*N<=n.
Writing n=5000*q+r, 0<=r<5000, gives F(n)-2*n-1 >= q-3*r.

Restriction to even indices gives F(2*n)>=2*F(n)-1.
Van Doorn's splice gives F(2*n)<=2*n+L(n,4*n).
Therefore L(n,4*n)-F(n)>=F(n)-2*n-1.
For B, n>=5000*(B+15001) suffices. The witness is m=4*n.

## Attribution and primary sources

Wouter van Doorn, arXiv:2601.16972v1, Lemma 2:
https://arxiv.org/html/2601.16972v1
The splice idea is attributed in source; its Lean implementation is independent.
The original quantitative proof also invokes Erdős–Pomerance asymptotic bounds.
Those bounds are not assumed or needed in this finite-certificate proof.

Paul Erdős and Carl Pomerance, Matching the natural numbers up to n with distinct
multiples in another interval (1980), author-hosted original:
https://math.dartmouth.edu/~carlp/PDF/matching.pdf
The restriction/scaling idea is also present in their proof of Theorem 2.
No external Lean code was copied. The certificate search script is original here.

## Verification artifacts

red.log: the original unconditional target fails against the conditional wrapper.
build.log/build.exit: artifact build and all selected theorem axioms.
target.log/target.exit: imported unconditional FC-compatible target.
axioms-types.log/audit.exit: all module theorem types and axioms.
kernel.log/kernel.exit: independent leanchecker replay.
certificate.json and search_certificate.py: reproducible finite obstruction.

Independent review requested by the user is assigned to agent 261 by the parent
agent; no callable multi-agent tools are available in this session.
