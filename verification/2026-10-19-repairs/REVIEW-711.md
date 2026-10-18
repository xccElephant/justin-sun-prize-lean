# Independent review of Erdos711 unconditional parts ii

Reviewed 2026-10-19. **Final verdict: review passed. No remaining mathematical defect found in the Hall/restriction/splice/asymptotic route; fresh-artifact independent import checks of both exact unconditional targets and all critical axiom dependencies passed (exit 0).**

Reviewed current source SHA-256: `01112dfa4b8c13fefbe3503a9f85ab8924aa9f076fedd05e99514faa1600cce2` (final compiled source, including the repaired gap case split, Boolean certificate, exact `erdos_711.parts.ii` alias, and updated source header).
Only review markdown was written; Erdos711 and its verification sources were not edited.

## Immediate feedback and resolution

An earlier version of `gap_from_diagonal` contained `have hh : Ln ≤ Lm := by omega`. The preceding arithmetic did not entail this: n=10, Ln=15, intermediate A=29, Lm=9 satisfies `2*(n+Ln-1)<2*n+A`, `A≤2*n+Lm`, `n+1≤Ln` but not `Ln≤Lm`. This was reported immediately. The current version removes this unsupported assertion, explicitly rewrites the splice bound as `A≤2*n+Lm`, and splits on `Ln≤2*n+1`. The intended truncated gap inequality does follow from those bounds and passed a separate small Lean arithmetic check. The example was a counterexample to the inference from those arithmetic facts, not to the final theorem with all its minimality hypotheses.

## Hall certificate covers the actual full neighbor set

Parsed the S and T literals directly from the source and independently regenerated

```
neighbors = ⋃ i∈S {i*t | 5000 < i*t ≤ 15000}.
```

S has 416 entries, 416 distinct elements, is strictly increasing, and lies in [520,5000]. T has 414 entries, 414 distinct elements, is strictly increasing, and equals this **entire** neighbor set: no missing neighbors and no extras.

The open interval `(5000,5000+10001)` is exactly the integer interval 5001..15000. The source `closure` considers every multiplier in `range (15000/i+1)`, not a chosen subset of neighbors. A tuple value divisible by i and at most 15000 has multiplier t≤floor(15000/i), so it is in that range. The `5000<i*t` test imposes the lower open endpoint. Including the endpoint 15000 is correct; excluding it would be unsound here.

In `obstruction`, every i∈S gives a valid index i−1∈Fin 5000. The map uses the corresponding actual tuple entry. Tuple divisibility supplies i∣a(i−1), `closure` puts that value in T, and original tuple injectivity plus i,j>0 proves injection S→T. This contradicts 416>414. It does not assume independent neighbor choices or injectivity of arbitrary multiplication maps. List chain proofs establish genuine Finset nodup, so cardinality is not inflated by duplicates.

`finite_diagonal_lower` transfers any minimal witness with A≤10001 into the forbidden interval, hence A≥10002. It makes no assumption that this finite certificate is the original published numerical certificate.

## Restriction, scale and open intervals

For q>0, N≥0, q*N≤n, restriction uses source divisor q*(i+1) at index q*(i+1)−1. This index is positive-before-subtraction and less than n; multiplication by q is injective. The tuple entry is divisible by q, so division is exact, not floor division of an arbitrary entry.

Its scaled value satisfies:

- `a/q > N`, because a>n≥q*N and a=q*(a/q).
- `a/q ≤ floor((n+L−1)/q)`, because a<n+L is an integer strict inequality.
- `(i+1)∣a/q`, by canceling the positive q from the original divisibility witness.

The target open interval has length `floor((n+L−1)/q)−N+1`. For each existing entry, the first bound ensures the subtraction is not truncated and its upper endpoint is floor((n+L−1)/q)+1, so the weak upper bound is precisely sufficient for a strict upper endpoint. N=0 is harmless because the tuple is empty.

For N>0, minimality at scale N gives
`N+A−1 ≤ floor((n+L−1)/q)`. Multiplying and using the floor bound yields the strict inequality

```
q*(N+A−1) < n+L.
```

The proof supplies the needed positivity/nontruncation via an actual restricted tuple and its cardinal lower bound. It does not rely on q*N=n or on n being a multiple of N.

## Splice and k=2 starting at 4n

The splice begins with n assignments in `(k²*n,k²*n+L)`. To build k*n assignments above k*n, it retains those n entries and assigns each new divisor i+1 (n<i+1≤k*n) the value k*(i+1). The new entries are strictly above k*n and at most k²*n, whereas the retained entries are strictly above k²*n. This proves cross-block distinctness, including the boundary value k²*n. New entries are distinct because k≥1. The new upper endpoint is k²*n+L; L>0 follows whenever a new index exists.

Thus for k=2 the correct source offset is **4n**, target is `(2n,4n+Lm)`, and minimality gives

```
A = f(2n,2n) ≤ 2n+Lm.
```

Restriction to even divisors of a minimal diagonal 2n-tuple gives

```
2*(n+Ln−1) < 2n+A.
```

Consequently `Lm ≥ 2Ln−2n−1`. If Ln≤2n+1 then the desired natural-number quantity `Ln−2n−1` is zero. Otherwise this inequality forces Lm≥Ln and yields

```
Ln−2n−1 ≤ Lm−Ln.
```

The current case split implements this valid reasoning. It is not a splice from 2n or an incorrect substitution of k*n for k²*n.

## All large n, with the remainder included

Set q=floor(n/5000), t=n mod 5000. Then n=5000q+t with 0≤t≤4999. The certificate gives A≥10002 and hence `5000+A−1≥15001`. Scale gives

```
15001*q < n+Ln,
Ln ≥ 10001*q−t+1,
Ln−2n−1 ≥ q−3t
```

whenever the last lower bound is positive (as it is at the final threshold). The chosen threshold `n≥5000*(B+15001)` ensures q≥B+15001, so
`q−3t≥B+15001−14997=B+4`. Thus the claimed B bound is safe, with spare room for strict endpoints. This step handles every residue t, not merely multiples of 5000 or an infinite subsequence.

The final statement quantifies `∀ B, ∀ᶠ n in atTop`. The code selects the explicit eventual threshold and chooses m=4n for every n above it, together with the actual minimal Lm and Ln. It does not use the old conditional van Doorn theorem as a hypothesis. Original tuple and minimality definitions were compared with HEAD and are unchanged.

## Verification status

- Independent exact Python reconstruction of the complete Hall neighborhood passed (416 vs 414, exact equality of T and actual neighbors).
- A separate small Lean check passed for the repaired arithmetic gap and for the full q/t threshold implication, importing only `Mathlib.Tactic.NormNum`. An initial attempt to import `Mathlib.Tactic.Omega` failed because that standalone olean is absent locally; rerunning with the project's available tactic import passed.
- `git diff --check` passed.
- The initial independent full-source stdin elaboration was cancelled at coordinator request to avoid duplicating the author's expensive certificate work on the shared machine. It produced no completed verification claim.
- Final author build exit is 0. The installed Erdos711.olean is newer than the final source. The independent import check described below also exited 0, and every checked certificate/helper/final target depends only on `[propext, Classical.choice, Quot.sound]`. Earlier failed-revision `sorryAx` output is superseded by these successful final checks.
- Existing `erdos711/Target.lean` still assigns the old conditional `_of_van_doorn` theorem to an unconditional type. That stale test must be pointed at `erdos_711_parts_ii` when doing final target validation. It is an obsolete verification artifact, not a flaw in the new mathematical proof.

The final source header now describes the unconditional finite-Hall/scaling/splice proof with witness m=4n, retains the conditional wrapper only for API compatibility, and explicitly says part i is not proved.

## Historical compile blocker — resolved

A newer source revision switched the certificate to Boolean list computations. Its observed SHA-256 was `9116dea580876dfd000aebbb61ce5e7f56c5dc0f9fc96522d6a9c18ee809ec3f`. The author's build log reported a type mismatch at source line 320: `ih` expected `increasing xs = true` but received `increasing (b :: xs) = true`. This was immediately communicated. The log consequently printed `sorryAx` for the certificate cards/bounds/closure, obstruction, finite diagonal bound, and final unconditional theorem. This is a compile blocker in that revision, not a discovered mathematical counterexample. Splice, restriction, scale_lower and repaired gap_from_diagonal printed only standard axioms. No fresh olean/import success was claimed from that failing revision. The final revision uses ordinary list induction, compiling the proof of `increasing (b :: xs)` with the matching induction hypothesis. Final artifact checks below supersede this historical failure.

## Final independent fresh-artifact check

Ran only `lake env lean --stdin` containing `import JspBounties.Erdos711`, two exact target examples, `#check`, and `#print axioms`. No certificate or source was re-elaborated. Exit code **0**.

Both `Erdos711.erdos_711_parts_ii` and the exact alias `Erdos711.erdos_711.parts.ii` independently inhabited this full, unconditional type:

```lean
∀ B : ℕ, ∀ᶠ n in atTop,
  ∃ m Lm Ln : ℕ, Erdos711.IsMinimalIntervalLength n m Lm ∧
    Erdos711.IsMinimalIntervalLength n n Ln ∧ B ≤ Lm - Ln
```

The alias `#check` displayed `(B : ℕ) : ∀ᶠ n in atTop, ...` with exactly the minimality predicates and gap above; no van Doorn hypothesis is required.

Printed axioms for all of:

- `FiniteObstruction.cards`, `.bounds`, `.closure`, `.obstruction`
- `hasDivisibleDistinctTuple_splice`, `hasDivisibleDistinctTuple_restrict`
- `scale_lower`, `finite_diagonal_lower`, `gap_from_diagonal`
- `erdos_711_parts_ii`, `erdos_711.parts.ii`

Every result printed `[propext, Classical.choice, Quot.sound]`. None uses `sorryAx` or an added theorem-specific axiom. A preceding independent import check also instantiated restriction, the k=2 splice with explicitly simplified natural subtraction, the finite obstruction and A≥10002; it exited 0. The final certificate literals were rechecked independently and still give the exact full neighborhood with 416 left vertices and 414 right vertices.

Only this markdown report was updated. The source header and alias were read and verified, not edited by the reviewer.

## Sidecar completion — final pass confirmed

Confirmed on disk: final reviewed source SHA-256 is `01112dfa4b8c13fefbe3503a9f85ab8924aa9f076fedd05e99514faa1600cce2`; fresh olean exists; author `build.exit`, `target.exit`, `audit.exit`, and `kernel.exit` are all **0**. The independent import exact-target/alias/axiom check above also exited **0**. Historical failed-revision notes are resolved history and do not describe the final artifact. **This sidecar is complete: PASS.** No source recompilation or edits were performed during this final confirmation.
