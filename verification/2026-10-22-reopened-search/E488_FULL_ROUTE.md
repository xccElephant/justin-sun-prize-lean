# Erdős488 / JSP-000395 / PR5096: complete prior refutation found

Checked October22,2026. This is a newly located route in our investigation,
not a newly discovered theorem or a new first-formalization contribution.
The previous repair queue's lack-of-route assessment is superseded here.
The existing submitted JspBounties/Erdos488.lean remains partial and unchanged.

## Exact mathematical target and solution

Let M_A(x) count positive integers j≤x divisible by at least one member of a
finite nonempty A, excluding generators0 and1. The original asks whether,
for all m>n≥max A, M_A(m)/m < 2 M_A(n)/n.

Declan Gessel's fixed public construction proves the strict reverse at two
finite endpoints. It uses all primes P<257 and S=P\{2}, Q=product(S), φ=φ(Q).
Let H(k) count S-smooth positive d≤256^k. Prime exponent encoding gives
H(k)≤(8k+1)^53. Since H(0)=1 and 2^4096*32769^53<3^4096, some k<4096 satisfies
2H(k+1)≤3H(k). Put T=256^k, h=H(k), A={P-smooth a:T<a≤256T}, n=256T, m=2TQ.

Every multiple j≤n of an a∈A is again in A: j/a<257, so it has no prime factor
outside P. Writing a=2^e*d injects A into S-smooth d≤256T paired with e mod8.
Thus M_A(n)=|A|≤8H(k+1)≤12h.

For each S-smooth d≤T, choose c_d=2^e*d minimally above T, hence T<c_d≤2T.
The map (d,r)↦c_d*r for0≤r<Q, gcd(r,Q)=1 is injective: odd smooth factors
cannot be absorbed by 2 or by r, so equality forces d=d' and then r=r'.
All images are covered and ≤m, yielding M_A(m)≥hφ. The exact finite prime
product comparison3Q<16φ and Q>128 give m>n and
2mM_A(n)≤48TQh<256Tφh≤nM_A(m).
This refutes the multiples statement itself, not the nonmultiples misprint.

The coordinator read this entire construction and corresponding end-of-proof
inequalities; the fixed source then supplies machine checking. No new
mathematical step or authorship is claimed for this description.

## Verified source and provenance

Original repository: WoshuaJolk/jig-verifier.
Commit: ccf4a26cb8a8c49f476d44304070a2b677da4d7e.
Path: Submissions/ErdosMultiplesSmoothRefuted/Counterexample.lean.
SHA256:37d2f3b46b3979d676ad50802fa9e2c08eaaf1cd859dee85271ad3e5ca639fe2.
Targets: Submissions.ErdosMultiplesSmoothRefuted.Counterexample.finite_counterexample
and Submissions.ErdosMultiplesSmoothRefuted.Counterexample.proof.

The actual commit metadata identifies submission by declangessel at
2026-09-05T20:26:51Z. GitHub Actions run33990129375 was created two seconds
later and completed successfully at20:29:02Z on the same commit. In Asia/Shanghai
this is **September6,2026,04:26–04:29**, not a new October22 result.
The Actions result is independently fetched public history; its inner server
checks are reported by that service, not recreated here.

Local independent validation on October22:
1. The downloaded unmodified standalone file compiled with exit0 on
   Lean4.33.1 / Mathlib0df444a360eaa60ab8c11dca51a86af692955474.
2. Its actual printed final axiom list is only propext, Classical.choice,
   Quot.sound. Linter/large-exponent warnings were emitted; there were no errors.
3. Our appended statement audit derived1∉A from the counterexample itself:
   if1∈A, both counts are full interval lengths and strict reversal is impossible.
   It proves positive endpoints, the exact Finset.max condition, and the
   rational-density formulation with both excluded generators. Both audit
   endpoints compiled exit0 and have only the same three standard axioms.
4. The actual literal-negation theorem is
   OriginalScopeCheck488.original_statement_false. It has no unproved hypothesis.
   The audit suffix is preserved in OriginalScope488.lean.txt; raw unmodified
   source, concatenated audit file and fetched public history are in the raw
   evidence folder. No additional separate kernel replay was performed.

An existing exact FormalConjectures adapter was also located at gist revision
9bbb516e782229c8ee2fe08dfe3bd53acac8b258, Erdos488.lean, theorem
Erdos488ExactAdapter.refutation. Its body and scope were read, but that separate
gist version was not the file independently compiled in the local check above.

## Consequence for our work

This supplies a concrete route to complete mathematical coverage of E488.
Our restricted affirmative results remain valid; the general statement is
refuted by a different finite smooth-band construction. It is inaccurate to
say we must prove that general inequality or have no full route available.

However, the complete mathematics and Lean source are prior work. A credited
reuse, compatibility port or new wrapper would not establish our first-proof
or first-Lean priority. No prize entitlement, contributor-share agreement,
independent innovation or permission to claim someone else's result exists.
Accordingly, this round records and validates the route without promoting
PR5096 to Ready or copying the proof into our submitted package.

To reproduce the exact local check, fetch the pinned source URL in
SOURCE_MANIFEST.json, verify its hash, append OriginalScope488.lean.txt to a
new temporary file, and run lake env lean on that file in this workspace.
The proof source and submission are attributed to Declan Gessel; the independent
scope audit and local checks are the only new work here.
