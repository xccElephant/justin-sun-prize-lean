# Sendov Lemma 4.1: exact obstruction to the cyclic two-band route

**Result:** no general geometric capacity proof obtained. The proposed abstract
condition “every union of two adjacent sector-color graphs is bipartite” does
**not** imply the strict-half capacity. An explicit finite obstruction already
occurs for m = 2. This is not a counterexample to the final geometric bound.

Read the local BLUMENTHAL.md, Sendov printed pp.33–40, and the two existing
weighted/missing-band Lean interfaces as evidence; no source code copied.
Offline bounded sidecar; no random configuration search performed.

## The obstruction

Take vertices Z/5Z and color each unordered edge {i,j} by i+j modulo 5.
The five cyclic color classes are:

| Color | Edges |
|---|---|
| 0 | 14, 23 |
| 1 | 01, 24 |
| 2 | 02, 34 |
| 3 | 03, 12 |
| 4 | 04, 13 |

Every class is a matching: for a fixed vertex i and color c its only possible
neighbor is c-i. The union of **any** two distinct classes is bipartite,
because every cycle alternates between their two matching colors and therefore
has even length. In particular, the five adjacent unions are the paths

    (0,1): 0–1–4–2–3
    (1,2): 1–0–2–4–3
    (2,3): 1–2–0–3–4
    (3,4): 2–1–3–0–4
    (4,0): 0–4–1–3–2

Thus K5 satisfies even the stronger all-pairs condition. Assigning abstract
local weights 2^0 to all five vertices gives total 5 > 2^2. The unweighted
special case alone refutes a capacity theorem based only on this graph
condition. The edge table and the five paths were checked by exhaustive
enumeration of the ten edges, not by numerical geometric search.

## Why the angle hypothesis supplies this condition but cannot be recovered from it

Write h = π/t and partition the projective direction circle into 2m+1 equal
half-open sectors, each of width w = π/(2m+1). If δ < 1/2 then h > 2w.
Two adjacent sectors form a double sector of width 2w < h (also across the
projective seam). An odd cycle with all edge lines in that double sector must
have a vertex whose two cycle rays point into opposite components: otherwise
orienting its edges by the component gives alternating incoming/outgoing
vertices, impossible on an odd cycle. The angle at the nonalternating vertex
is greater than π-2w and hence greater than π-h. This contradicts the angle
cap. Therefore each adjacent-color union is bipartite.

The converse inference is the failed step: the abstract bipartiteness
condition does not retain h > 2w, the actual edge directions, or their
compatibility with center positions. Our K5 obstruction does not assert a
realization satisfying the strict cap.

The equality geometry explains the loss of information. Five regular pentagon
vertices have maximum triple angle 3π/5 = π(1-1/(5/2)). Their ten projective
edge directions form five equally spaced directions, so a rotated five-sector
partition assigns one matching to each sector. Labeling the vertices cyclically,
the direction color is i+j modulo 5, up to a common shift: subtracting the two
complex roots of unity gives line angle π(i+j)/5 + π/2 modulo π. At every
vertex the four distinct projective directions have normalized circular gaps
1/5, 1/5, 1/5, 2/5. At t = 5/2 their products with t are 1/2, 1/2, 1/2, 1,
so k_i = 0. The total is 5, exactly the allowed δ = 1/2 capacity 4+1.
This is an equality example, not a strict-half counterexample.

## Consequence for weighted codes

The existing weighted Boolean-subcube argument requires a common used
coordinate separating each pair of vertices. Five nonempty disjoint subcubes
cannot fit in a two-coordinate Boolean cube: each contains at least one word,
and that cube has four words. Hence the adjacent-union hypothesis cannot by
itself supply the required m-coordinate separating code, even before asking
for k_i free coordinates. Merely strengthening “adjacent” to “any two” does
not repair this route, since the same example satisfies that strengthening.

A viable continuation must use additional geometric or quantitative angular
constraints; the strict slack h-2w has to enter before the information is
reduced to bipartiteness. No such strengthening or general proof is supplied
here. In particular, the known four-center weight total 10 at t = 15/4
remains consistent with the final bound 10; its disagreement with the printed
four-center profile is not being counted as a disproof of Lemma 4.1.
