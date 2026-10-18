# Final review: Euler four-term AP square-product theorem

Date: 2026-10-19, Asia/Shanghai.
Scope: complete algorithm and proof graph for `Erdos672With 4 2` only.
Verdict: **PASS — no blocking mathematical or proof-graph issue found.**
The previously pending primitive dispatch, normalization, natural-number
transport, and well-founded closure are now implemented and verified.
The previous partial reports record earlier versions and are superseded by
this final report for the fixed version below.

## Fixed reviewed version and artifacts

Source: `JspBounties/Erdos672.lean`.
SHA256: `6669c1d7eab74ec05536e90d16a8f7e2ee674f23a0aba1c98ffaaeead611e62b`.
Reviewed compiled artifact:
`verification/repair-2026-10-19/erdos672/compiled/JspBounties/Erdos672.olean`.
Artifact SHA256:
`0cb15b8a44aa5b2747af7a53fc4942e000ec21d36cbd96d521db8e91a6422778`.

The author's `compile-olean.log`, `target.log`, and `all-theorems.log` record
successful artifact/target checks and standard axioms; the all-theorem audit
contains 82 entries. `kernel-replay.log` says `replaying JspBounties.Erdos672`,
and `kernel-exit.txt` is 0. These existing checks were inspected, not rerun.

The reviewer independently ran `ReviewFinalImport.lean` against that exact new
artifact using the saved `verification-env.json` LEAN_PATH. This avoids the
older olean still present in the default `.lake/build` directory.
`review-final-import-exit.txt` is 0. The independent check verifies both the
explicit arithmetic theorem and the fully expanded original-interface type,
prints the two final proof bodies, and prints axioms for all six core stages.
No source-module recompilation or additional kernel replay was performed by
the reviewer. No source was edited.

## Exact final conclusions

The unrestricted arithmetic conclusion is:

```lean
∀ (n d q : ℕ), 0 < n → 0 < d →
  n * (n+d) * (n+2*d) * (n+3*d) ≠ q^2
```

It has no coprimality, size-bound, descent-step, or parametrization premise.
The original-interface theorem is:

```lean
Erdos672.erdos_672_four_two : Erdos672.Erdos672With 4 2
```

The independent import also checks its exact unfolded type:

```lean
∀ (s : Finset ℕ), s.card = 4 → ∀ (n : ℕ), 0 < n →
  ∀ (d : ℕ), 0 < d → Nat.gcd n d = 1 →
  Erdos672.Set.IsAPOfLengthWith (s : Set ℕ) 4 n d →
  ∀ q : ℕ, ∏ i ∈ s, i ≠ q^2
```

The predicate retains its genuine four-term AP definition. The wrapper uses
`prod_eq_of_isAPOfLengthWith_four` to identify the finite-set product with the
four arithmetic factors and then applies `four_ap_ne_sq`. The unused original
coprimality premise is legitimate because the arithmetic result is stronger.
This verifies the complete `k=4,l=2` subproblem; it does not establish the
broader assertion for arbitrary `k≥4,l>1`.

## Proof graph and absence of circularity

The reviewed dependency order is:

1. Integral algebra, gcd/square extraction, finite modulo-3 checks, and
   installed mathlib primitive Pythagorean classification.
2. Case2 odd-leg descent; Param and the double-triangle construction for
   Case1; complete Case1 even-leg descent.
3. `primitive_four_ap_descent`: derives all branch premises from a hypothetical
   primitive positive square-product AP and dispatches to Case1 or Case2.
4. `primitive_four_ap_descent_nat`: transports its positive integral outputs
   and strict middle-product inequality to natural numbers.
5. `normalize`: independently reduces any positive natural square-product AP
   to a primitive one without increasing its middle product.
6. `no_square_of_primitive_descent`: a generic strong-induction theorem using
   normalization and a supplied primitive strict-descent function.
7. `four_ap_ne_sq`: explicitly supplies the already proved
   `primitive_four_ap_descent_nat` to that generic theorem.
8. `erdos_672_four_two`: translates the original AP interface to the
   unrestricted arithmetic result.

The printed body of `four_ap_ne_sq` is precisely an application of
`no_square_of_primitive_descent primitive_four_ap_descent_nat`.
The generic helper's `step` argument is therefore discharged, not carried
into the final theorem. Neither primitive descent, either case branch, Param,
normalization, nor the natural-number bridge calls `four_ap_ne_sq`, the final
interface theorem, or the generic no-square theorem. There is no reverse edge
from the descent construction to the result it is used to prove.
The only recursive use is the induction hypothesis at a strictly smaller
natural middle product, justified locally before that call.

## Core hypotheses are derived

### Primitive dispatch

From gcd(a,d)=1, the proof derives coprimality of each of the four AP factors
with d, hence gcd(q,d²)=1 from the hypothetical square-product equality.
Euler's polynomial identity supplies the primitive Pythagorean equation.
The installed classification supplies opposite-parity coprime parameters and
the two leg orderings. The positive hypotenuse excludes its negative option.
Taking U=abs(u), V=abs(v) preserves squares, gcd, and residues modulo 2.

In the even-leg ordering, d²=2UV>0 forces U,V>0. In the odd-leg ordering,
the positive AP product proves q!=0; q=2uv then excludes v=0 and gives V>0.
Together with d²=U²-V²>0 this also ensures U>V>0. No sign, parity, primitive
parameter, or nonzero-root assumption is added at dispatch.

### Case2

Coprime opposite-parity U,V imply gcd(U+V,U−V)=1. Positivity allows both
factors of d² to be extracted as positive squares x²,y². Coprimality descends
to x,y. The discriminant identity and modulo-3 check derive the exact
integral divisions used in D=(x²−y²)/3 and t=(2a+3d)/3.
The new AP starts at A=y²>0, and 3D=2V>0 gives D>0.
Its square product is (x*y*t)². Its middle product is t², and

`9*((a+d)*(a+2d)−t²)=5a²+15ad+9d²>0`.

Thus the actual positive AP has a strictly smaller middle product without
an assumed size bound or descent inequality.

### Case1 and Param

The primitive even square leg is factored into 2r² and s² with r,s>0,
gcd(r,s)=1, and s odd. The discriminant and coprime positive factors give
two genuine Pythagorean triangles. Their classifications derive positive,
coprime R,S, R²!=S², the Eisenstein conic equation with positive root,
and W=R*S=r with 4W²<=d².

Param constructs primitive a,b from the exact gcd factorization of x+z,y+z.
Its positive identity proves k>0, while the numerator gcd divides 3 and
primitive x,y give k|3. Thus k<=3 is derived. The two numerator identities
force 2a−b>0 and 2b−a>0. Nondegeneracy excludes a=b, so either orientation
produces A>0,D>0 and the same square product, with middle product a*b.
The endpoint product is at least 3. Hence

`3ab <= (kRS)²` and `4(kRS)² <= 9d²`, so `ab <= 3d²/4`.

The source middle product n²+3nd+2d² is strictly greater than 2d² for n,d>0.
This closes strict descent even at k=3. No conic parameter or scale-bound
hypothesis is left unproved at the Case1 caller.

## Normalization, casts, and well-founded closure

`normalize` uses g=gcd(a,d)>0 and exact divisibility to write a=gA,d=gD.
It proves A,D>0 and gcd(A,D)=1. The product scales by g⁴, so from
q²=g⁴*product4(A,D) it proves g²|q and normalizes the square root by g²,
not by g. Cancellation by the positive g⁴ then preserves the square-product
identity. A<=a and D<=d prove non-increase of the middle product.

`primitive_four_ap_descent_nat` proves A,D positive before calling toNat,
uses exact cast-back identities, and chooses Q.natAbs because only Q² is
required. The product identity and strict middle inequality are transported
by integer casts; negative values are not truncated into spurious witnesses.

The well-founded argument strongly inducts on m=middle(a,d), for arbitrary
positive APs rather than only primitive ones. It first normalizes to middle
M<=m, then applies the proved primitive step to get M'<M. Thus M'<m,
and the induction hypothesis applies to the generated positive AP regardless
of its gcd. There is no need to assume output primitivity or preserve the
original square root. At m=0 the same strictly-smaller-measure argument is
impossible; no omitted special base-case assumption is needed.

## Closed previous findings and final checks

- The former redundant `convert …; ring` failure in hcp1 is fixed with simpa.
- Primitive U,V positivity and parity are derived in both leg orderings.
- Case1 is implemented through Param and its derived scale bound.
- Output normalization, square-root normalization by gcd², and the ℤ-to-ℕ
  bridge are implemented.
- The generic descent assumption is instantiated in the final arithmetic
  theorem; it is absent from both final types.
- The final original interface is exact and restricted to four terms/squares.
- Independent imported axioms for normalize, primitive descent, natural
  descent, generic strong induction, four_ap_ne_sq, and erdos_672_four_two
  are exactly `[propext, Classical.choice, Quot.sound]`.
- The fixed source and inspected successful logs contain no sorryAx or
  Lean.ofReduceBool dependency for those final proofs.

No blocking findings remain for this fixed four-term square-product proof.
The report does not authorize or perform a commit, and does not claim proof
of the general Erdős 672 perfect-power problem.
