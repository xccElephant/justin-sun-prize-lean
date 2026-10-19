# Two integers with arbitrarily many common factor differences

Date: 2026-10-19. Submitted account: `xccElephant` (Ethan Xiang).
This proof and its Lean formalization were developed with AI assistance in this
repository. No claim of first discovery, priority or award entitlement is made.

## Statement and scope

For a positive integer n, write

    D(n) = { |a-b| : a,b are nonnegative integers and ab=n }.

For every natural number k there are positive integers N<M and exactly k distinct
positive integers belonging to both D(N) and D(M).

This answers the literal two-integer wording of JSP-000736 in the publisher's
catalog at `fd8fa66abb4e21df828fdebc25298e9ad75521bd`. It does **not** answer the
stronger Erdős #885 conjecture asking for k distinct integers with at least k
common factor differences. The number of integers in this construction is always
two. Whether this narrower catalog wording is the intended award scope requires
maintainer review; the catalog's original status and eligibility are retained.

Primary scope references:

- [Publisher catalog](https://github.com/TheJustinSunPrize/awards/blob/fd8fa66abb4e21df828fdebc25298e9ad75521bd/problems/catalog-0701-0800.md#JSP-000736).
- [Erdős #885](https://www.erdosproblems.com/885).
- [Publisher submission requirements](https://github.com/TheJustinSunPrize/awards/blob/fd8fa66abb4e21df828fdebc25298e9ad75521bd/CONTRIBUTING.md).

## 1. An infinite sequence of rational points

Let v₂ be the usual 2-adic valuation of a nonzero rational, with v₂(2)=1.
Start with (x₀,y₀)=(25/4,35/8), which satisfies

    y² = x³ - 36x,   x>6,   v₂(x)=-2.

For a rational point with x>6 and v₂(x)<0, y is nonzero because
y²=x(x²-36)>0. Define

    x' = (x²+36)² / (4y²),
    y' = ((3x²-36)/(2y))(x-x') - y.

Substitution in these formulas, clearing the nonzero denominator and using
y²=x³-36x, gives y'²=x'³-36x'. This polynomial identity is explicitly checked in
`double_curve`; no elliptic-curve group theorem or rank result is assumed.

Put s=v₂(x)<0. The terms x³ and -36x have valuations 3s and 2+s. These are
different, with 3s<2+s, so

    2v₂(y)=3s.

Likewise v₂(x²+36)=2s, because 2s<2. Consequently

    v₂(x')=4s-2-2v₂(y)=s-2.

The identity

    (x²-12x-36)² = (x²+36)² - 24y²

implies x'≥6. Equality is impossible: v₂(6)=1, whereas v₂(x')=s-2<0.
Thus x'>6, the curve equation and the negative valuation are all preserved.
Iteration is therefore defined for every n, with

    v₂(xₙ)=-2(n+1).

## 2. Rational triples with two fixed square differences

At each point define

    u = (x²-12x-36)/(2y),
    v = (x²+36)/(2y),
    w = (x²+12x-36)/(2y).

Direct algebra on the curve gives

    v²-u²=6,   w²-u²=12.

For the numerator of u, the valuations of x², -12x and -36 are 2s, 2+s
and 2. The first is strictly smallest. Hence the numerator is nonzero, and

    2v₂(u)=2(2s-1-v₂(y))=s-2.

For the nth point this gives v₂(uₙ)=-n-2. Therefore uₙ is nonzero, and the
numbers |uₙ| are pairwise distinct: taking absolute values preserves valuation.
There is no assumption that uₙ or yₙ has a fixed sign.

## 3. Clear finitely many denominators

Fix k. Take any positive integer L divisible by the denominators of
uᵢ,vᵢ,wᵢ for 0≤i<k. In Lean, L is the product of all these positive
denominators; for k=0 the empty product is 1. Set

    Uᵢ=L|uᵢ|,   Vᵢ=L|vᵢ|,   Wᵢ=L|wᵢ|.

These are nonnegative integers, Uᵢ>0, and

    Vᵢ²-Uᵢ²=6L²,   Wᵢ²-Uᵢ²=12L².

In particular Vᵢ>Uᵢ and Wᵢ>Uᵢ. Let N=6L² and M=12L². Then 0<N<M and

    N=(Vᵢ-Uᵢ)(Vᵢ+Uᵢ),
    M=(Wᵢ-Uᵢ)(Wᵢ+Uᵢ).

Both pairs consist of positive integer factors and both factor differences are
2Uᵢ. The k numbers 2Uᵢ are positive and pairwise distinct, since L>0 and the
|uᵢ| are pairwise distinct. They form the required subset of D(N)∩D(M).

## Formal targets and verification boundaries

Source: `JspBounties/Erdos885.lean`.

- `Erdos885.TwoNumbers.literal_two_number_witnesses`: the exact k-element
  finite set of positive common differences, together with 0<N<M.
- `Erdos885.TwoNumbers.literal_two_numbers`: the intersection cardinality is
  at least k. Finiteness follows from N>0 and the finite factor-difference set.

Both targets have no mathematical premises beyond the natural parameter k.
Their reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Compilation, an independent exact-signature/definition check, and bundled Lean
kernel replay are recorded alongside this document. Replay uses Lean's own
kernel and pinned imported dependency caches, not an independently implemented
external kernel or a from-scratch rebuild of Mathlib.

The previous explicit k=2,3,4 cases of the stronger family statement remain in
the source, with their historical references. They do not supply a proof for
arbitrary k. This note supplies a self-contained mathematical argument for the
new two-number theorem, not an attribution claim about the stronger conjecture.
