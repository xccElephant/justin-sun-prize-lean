# Remaining original-submission repair queue

The user requested completion of all existing submissions before new problems. All 32 records remain in this queue; none is abandoned. A proved subproblem does not close a broader original record. As of this batch, two clearly scoped original proofs await external review, PR5080 awaits scope review of its complete finite-existence proof, and29 records remain drafts with scope or mathematical requirements.

This is an obligation ledger, not a claim that all open mathematical requirements are currently solvable. Known-proof formalization, new mathematical research, scope clarification, and external acceptance are separate activities.

## PR5076 — JSP-000290 / Erdős348

Status: `proof_complete_pending_review`. Abandoned: no.

Existing proved scope: For every pair of natural numbers 0 <= m < n, a nondecreasing sequence a : N -> N exists such that deleting any m indexed occurrences leaves every sufficiently large natural number representable as a finite sum of remaining indexed occurrences, while deleting any n indexed occurrences destroys this property, if and only if m <= 1. The proof covers m = 0 by powers of two, m = 1 by the Fibonacci sequence 1,1,2,3,..., and impossibility for m >= 2. Deletion is Function.updateFinset a s 0; repeated values retain separate indices.

Outstanding original-problem obligation: No mathematical scope gap for JSP-000290. Use the actual set-equality target Erdos348.erdos_348 and the nondecreasing, indexed-deletion formulation.

## PR5077 — JSP-000254 / Erdős302

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Constructs reciprocal-sum-free subsets of {1,...,N} with asymptotic density at least 17/32 and proves that the extremal density does not tend to 1/2 (parts.ii). The audited finite inequality uses additive constant 576, not 64.

Outstanding original-problem obligation: The optimal asymptotic density and existence of its limit (parts.i) are not proved. The 5/8 lower bound and 9/10 upper bound are not established here.

## PR5078 — JSP-000691 / Erdős835

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves necessary divisibility t | choose(k+t,t-1) for (k+1)-colorability of J(2k,k), exclusions for k>2 when k+1 is composite or k is odd, the k=4 exclusion, and chromaticNumber(J(18,9)) > 10.

Outstanding original-problem obligation: Neither existence for some k > 2 nor nonexistence for all such k is proved. The general remaining prime-(k+1) cases remain uncovered. The coloring question concerns k-subsets of a 2k-set and all k+1 colors on each (k+1)-subset.

## PR5079 — JSP-000301 / Erdős365

Status: `proof_complete_pending_review`. Abandoned: no.

Existing proved scope: Fully disproves the scoped question: if two consecutive positive integers are powerful, must at least one be a perfect square? The counterexample is 12167 = 23^3 and 12168 = 2^3 * 39^2; both are powerful and neither is a square. The parts.i target directly proves the negation of the universal claim. Also proves infinitely many positive consecutive powerful pairs with neither member square.

Outstanding original-problem obligation: No scope gap for JSP-000301, whose review notes explicitly exclude the separate counting question. The polylogarithmic counting upper bound in Erdos 365 parts.ii is not proved; the infinite family does not imply it.

## PR5080 — JSP-000307 / Erdős372

Status: `submitted_for_scope_review`. Abandoned: no.

Existing proved scope: Proves the least decreasing triple begins at n=13 and gives a decreasing quadruple at n=317. Also proves infinitely many valleys P(n)>P(n+1)<P(n+2), and infinitely many individual adjacent increases and decreases.

Latest checked repair: Literal existence theorem stated entirely using prime divisibility and domination of every prime divisor; witness 13,14,15.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: Infinitely many decreasing triples are not proved; catalog scope remains unresolved.

Review-state clarification: PR5080 is ready for scope review, not claimed to prove infinitude or qualify for a prize. See REVIEW_STATUS.md.

## PR5081 — JSP-000509 / Erdős628

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the Tihany partition variants k=5, a=b=3 and independence number exactly 2.

Outstanding original-problem obligation: The conjecture for arbitrary graphs and arbitrary k,a,b is not proved. The independence-number hypothesis is a substantive restriction; the quasi-line variant is not established here.

## PR5082 — JSP-000500 / Erdős617

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the r=3 statement for edge colorings of K10. The target variants.r2 proves infinitely many parameters r admit an r-coloring on r^2 vertices in which every (r+1)-vertex subset contains every color; this is a counterexample family at r^2 vertices.

Outstanding original-problem obligation: The general r>=3 statement on r^2+1 vertices, including the r=4 variant, is not proved. The name r2 refers to r^2 counterexamples, not an affirmative r=2 case.

## PR5083 — JSP-000403 / Erdős503

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves exact maxima 1 in dimension 0 and 3 in dimension 1, six-point and eight-point constructions in dimensions 2 and 3, and a choose(n+1,2)-point isosceles construction in general dimension.

Outstanding original-problem obligation: The upper bounds proving optimality in dimensions 2 and 3 and the general upper bound are not proved. Other optimality wrappers assume hupper; the supremum lower-bound wrapper assumes BddAbove.

## PR5084 — JSP-000247 / Erdős291

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves infinitely many n have gcd(a_n,L_n)>1, where L_n=lcm(1,...,n) and a_n=sum_{j=1}^n L_n/j, using n=2*3^(k+1). This completes parts.ii.

Outstanding original-problem obligation: The infinitely-many coprime case (parts.i), the prime-digit equivalence, and counting or density results are not proved.

## PR5085 — JSP-000303 / Erdős367

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the O(n^2) bound for k<=2, disproves the universal O(n^2) claim in parts.ii, and proves an infinitely-often positive-constant n^2 log n lower bound for three consecutive B_2 factors.

Outstanding original-problem obligation: The n^(2+o(1)) question in parts.i remains unproved and undisproved; n^2 log n is compatible with that bound. Higher-full variants for r>=3 are not proved.

## PR5086 — JSP-000489 / Erdős602

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves property B for countably indexed families of infinite sets, and the two-set and pairwise-disjoint variants.

Outstanding original-problem obligation: The original permits an arbitrary index set. Countability of each member does not imply countability of the family; the general almost-disjoint, forbidden-singleton-intersection case is not proved.

## PR5087 — JSP-000544 / Erdős670

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the fixed one-dimensional asymptotic statement and the choose(n,2) diameter lower bound in every dimension. Derives failure of a bound uniform in dimension only under the complete Ho-construction hypothesis hHo.

Outstanding original-problem obligation: The fixed-dimension statement for d>=2 is not proved. The choose(n,2) bound has asymptotic constant 1/2. The Ho construction is assumed, and dimensions varying with n do not refute a fixed-dimension claim.

## PR5088 — JSP-000131 / Erdős124

Status: `scope_clarification_active`. Abandoned: no.

Existing proved scope: Proves the k=0 digit-representation statement, including representation of every natural number under the reciprocal-sum condition, its converse, and the k=0 eventual-representation equivalence.

Latest checked repair: Necessary gcd obstruction and explicit distinct-exponent representatives for every residue.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: Positive-cutoff sufficiency, {3,4,7} completeness, and Melfi construction remain unproved.

## PR5089 — JSP-000780 / Erdős939

Status: `scope_clarification_active`. Abandoned: no.

Existing proved scope: Proves infinitely many triples of positive 3-powerful integers a,b,c with a+b=c and {a,b,c}.Coprime, using a proved seed and a growing recurrence.

Latest checked repair: For every r>=6, infinitely many finite sets of exactly r-2 positive r-powerful terms, setwise gcd1 and r-powerful sum.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: The triples theorem is complete but its exact JSP scope remains unresolved. The new general r>=6 construction is a separate sum-family result; it does not resolve the scope or r=4/5 gaps.

## PR5090 — JSP-000781 / Erdős939

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves infinite higher-powerful sum families for r=6,7,8, examples, and the negation of the assertion that every r>=4 has only finitely many solutions.

Latest checked repair: For every r>=6, infinitely many finite sets of exactly r-2 positive r-powerful terms, setwise gcd1 and r-powerful sum.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: r=4 existence, r=4/5 infinitude, full catalog counting/density questions and scope approval remain unresolved.

## PR5091 — JSP-000058 / Erdős23

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the five-vertex case (k=1) of the triangle-free bipartite edge-deletion problem and its C5 sharpness: at least one edge must be deleted.

Outstanding original-problem obligation: The bound for all k>1, the n5 variants, and general C5-blowup tightness are not proved here.

## PR5092 — JSP-000244 / Erdős287

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves a maximum adjacent denominator gap of at least 2 and the sharpness witness (2,3,6) with reciprocal sum 1 and maximum gap 3. Derives the gap>=3 conclusion for sufficiently large lengths only under an additional prime-distribution conjecture.

Outstanding original-problem obligation: The original unconditional gap>=3 statement for all lengths is not proved. The prime-distribution premise and the remaining small lengths are unresolved by this file.

## PR5093 — JSP-000280 / Erdős338

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the Bateman counterexample: for each h>=3, a set is an ordinary asymptotic basis of order at most h but has no restricted order. Separately proves large-odd coverage and a counting bound for order-two bases containing 0, which concern Erdos 339.

Outstanding original-problem obligation: The Erdos 338 classification, quantitative restricted-order bounds, equality conditions, and finite-deletion cases are not proved. Exact minimal ordinary order h is not independently established; the Erdos 339 results do not fill those gaps.

## PR5094 — JSP-000569 / Erdős699

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the requested common prime-factor bound for i<=2 and the weaker general gcd>1 result. Proves conditional prime-factor transfer steps, explicit exceptions to the strict p>i strengthening, and necessary membership of those exceptions in any valid exception set.

Outstanding original-problem obligation: The general common-prime bound p>=i is not proved. A gcd>1 conclusion only ensures a common prime >=2; transfer results retain additional prime-existence or divisibility hypotheses. Necessary exceptions are not a full classification.

## PR5095 — JSP-000736 / Erdős885

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the k=2,3,4 complementary-factor-difference variants. For k=4 the numbers are 65984625,508032000,1578963456,2505664000, with common differences 5040,27720,68880,164976.

Outstanding original-problem obligation: The assertion for every k is not proved. The original asks for k distinct positive integers with at least k common complementary-factor differences; it is not restricted to two integers.

## PR5096 — JSP-000395 / Erdős488

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the union-of-multiples inequality for singleton and two-element sets and sets containing 2. Proves a conditional high-half insertion step and a counterexample to the nonmultiples misprint.

Outstanding original-problem obligation: The general finite-set inequality is not proved. The insertion step assumes n/2<a<=n, nondivisibility by old elements, and the stronger bound (n+1)B(m)<=2mB(n). The nonmultiples counterexample does not refute the original multiples question.

## PR5097 — JSP-000546 / Erdős672

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves k=2 and k=3 counterexamples outside the original k>=4 range. Proves the identity n(n+d)(n+2d)(n+3d)+d^4=(n^2+3nd+d^2)^2. Excludes square products when d^4+1<2(n^2+3nd+d^2), in particular for d>0 and n>=d^2, and for n>0,d=1. Derives a necessary primitive-Pythagorean condition for a hypothetical coprime four-term square-product counterexample.

Latest checked repair: Complete unconditional four-term square-product exclusion, with normalization and both infinite-descent branches.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: The original assertion for arbitrary progression length and perfect-power exponent remains unproved.

## PR5098 — JSP-000234 / Erdős273

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves a finite distinct-modulus covering of N with moduli p-1 for primes p>=3, using twelve moduli including 2 and period 360.

Outstanding original-problem obligation: The original requires p>=5 and a covering of Z. The construction uses p=3; removing modulus 2 loses coverage of 2. The later integer-domain bridge still permits p=3 and does not resolve the prime-bound gap.

## PR5099 — JSP-000226 / Erdős261

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the infinitely-many-n finite-representation question (parts.i), the Borwein-Loring construction and property, and two distinct infinite representations of 3/8, via (5,6,7,...) and (4,7,8,...).

Latest checked repair: For every finite r, a rational x_r has at least 2^r canonical infinite representations; each fiber has cardinality at most continuum.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: A single rational with continuum many representations and finite decomposition for every positive n remain unproved; quantifiers cannot be exchanged.

## PR5100 — JSP-000483 / Erdős596

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves that every C4-free graph, on an arbitrary vertex type, has a countable decomposition into C6-free edge-color classes.

Outstanding original-problem obligation: The finite-color Ramsey premise hfin is not proved; exceptional-pair and related existence conclusions depend on it. Classification of all graph pairs remains unproved. The audited escape result promises C6-free classes, not trees.

## PR5101 — JSP-000542 / Erdős668

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the negation of the every-n>3 multiplicity claim (parts.ii): at n=4 the maximum unit-distance count is 5 and every maximizer is equivalent under a plane isometry to a unit rhombus.

Outstanding original-problem obligation: The first question, whether the number of maximizing configurations tends to infinity, is not proved. The unit-distance maximum 5 is distinct from the number of configurations up to isometry.

## PR5102 — JSP-000533 / Erdős657

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves the Straus construction of 2^k isosceles-free points in R^k with at most 2^k-1 distinct distances, and the equivalence between one-dimensional isosceles triples and three-term arithmetic progressions.

Outstanding original-problem obligation: The fixed-plane asymptotic distance bound is not proved. Growing dimension with n does not answer it. The one-dimensional asymptotic reduction assumes the core Dumitrescu lower bound; the submitted targets do not prove that bound.

## PR5103 — JSP-000210 / Erdős238

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves block-pigeonhole and finite-run lemmas. For c2<2, supplies a run of prescribed length k when the (1+k)-th indexed prime is <=x. Derives the small-c1 logarithmic-run conclusion only under the explicit eventual block-count and sparse-bad-gap premise hBC.

Latest checked repair: Every positive c1 and every c2<2: all sufficiently large real x have more than c1 log x consecutive primes with every adjacent gap above c2.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: Arbitrary c2>=2 and the unrestricted original question remain unproved.

## PR5104 — JSP-000340 / Erdős413

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves trajectory trapping and coalescence conditional on a barrier, infinitely many nonbarriers, and an equivalence and a conditional reduction for parts.ii using the Lau hypothesis.

Outstanding original-problem obligation: Infinitely many omega-barriers are not proved. The second question asks for some epsilon>0 with infinitely many epsilon-barriers, not every fixed epsilon; the core Lau hypothesis and the infinitude on the equivalence right-hand side are unproved. Infinite nonbarriers do not rule out infinite barriers.

## PR5105 — JSP-000072 / Erdős44

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves greedy and parabola Sidon constructions and an unconditional sqrt(N)/3 lower bound. Derives a near-optimal empty-start result only assuming Singer and the required prime-density input.

Outstanding original-problem obligation: Extending an arbitrary prescribed Sidon set A while preserving A and proving A union B is Sidon is not established. The constant 1/3 does not give (1-epsilon)sqrt(M) for every epsilon>0; the Singer construction is assumed in the conditional results.

## PR5106 — JSP-000579 / Erdős711

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves existence and uniqueness of the minimum interval length, the lower bound n+1, the value at m=0, and periodicity under a common multiple. Derives parts.ii only under the van Doorn hypothesis hvd.

Latest checked repair: Unconditional parts.ii, all sufficiently large n and explicit offset m=4n; no external gap hypothesis.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: Parts.i uniform n^(1+o(1)) upper bound remains unproved.

## PR5107 — JSP-000595 / Erdős727

Status: `proof_repair_active`. Abandoned: no.

Existing proved scope: Proves infinitely many n satisfy ((n+1)!)^2 | (2n)!, the k=1 variant.

Latest checked repair: Exact factorial/carry-count equivalence and offset carrying lemmas.

Selected repair commit: `de6cac2e9dcfd904988edf7e2603a87bc1c6f3fe`.

Outstanding original-problem obligation: Neither mixed-factorial infinitude nor the squared-factorial conjecture for k>=2 is proved.
