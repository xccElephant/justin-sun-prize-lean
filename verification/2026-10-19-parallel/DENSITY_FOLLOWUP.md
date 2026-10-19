# Bounded mathematical followup — 2026-10-19

Publication note: this is the original local followup report. Its `sources/` and finite-check paths refer to local research evidence under `reports/parallel-campaign-2026-10-19/nt-density-products-followup/`, not bundled public files. Raw third-party papers are not republished. The conclusions are mathematical route analysis only, not new accepted Lean proofs.

Completed one focused route per original PR: 5077/E302, 5084/E291, 5085/E367. All three remain **full=false / unresolved**. This pass supplies new mathematical analysis, not a new Lean proof or a full repair. Only this followup directory was written. No git, source edits, PR changes, messages, subagents, or Lean compiler processes were used. coding and web-access were read; the work is mathematical/documentary, so no manufactured failing implementation tests were appropriate. Exact finite calculation was used only to check an actual proposed mathematical inequality.

## Source verification and scope

The current original problem pages were retrieved on 2026-10-19 using public curl under web-access's static-source route, and retained as `sources/erdos{302,291,367}.html` and derived `.txt`. The original Erdős–Graham book was retrieved from `https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf` as `sources/ErGr80-original.pdf`. It matches the retained book byte-for-byte (see manifest). The book is an image scan: OCR is navigation evidence, not authoritative mathematical transcription. Rendered printed pages 34, 37 and 69 were visually inspected. Printed pp. 36–37 locate E302's reciprocal question; p. 34 contains both E291 infinitude questions; pp. 68–69 define the powerful-part product and ask the exponent-2-plus-epsilon bound. Thus previous bare references to p. 36 for E302 or p. 71 for E367 need location clarification. The original book uses product offsets 1 through k, which are asymptotically equivalent to the current offsets 0 through k−1 by shifting n.

Current page URLs:
- https://www.erdosproblems.com/302
- https://www.erdosproblems.com/291
- https://www.erdosproblems.com/367

These are statement/status context, not substitutes for a proof. E302's page records the known 5/8 constructive lower bound and 9/10 upper bound. The upper bound is attributed to an author's linked note; this bounded pass did not independently audit that note and does not claim its proof. E291's page explicitly distinguishes a heuristic x/log x count from a theorem. E367 retains the n^(2+o(1)) question after the stronger O(n²) claim fails. No new general literature search or current awards/PR-status retrieval was undertaken. Local PR payloads and the prior group REPORT/RESULT are historical scope evidence only.

Read-only local sources: `JspBounties/Erdos302.lean`, `JspBounties/Erdos291_367.lean`, previous `nt-density-products/REPORT.md`, `RESULT.json`, `ACCEPTANCE_TYPES.md`, and retained original PR payloads `reports/audit-2026-10-18/evidence/pr-{5077,5084,5085}.json`. Source hashes before and after are retained and agree.

## PR5077 / E302 — scaling and Fekete-type density limit

**Exact missing full statement.** For the extremal cardinality f(N) of subsets of [1,N] without distinct a,b,c satisfying bc=a(b+c), determine its sharp asymptotic behavior, with an identified optimal density δ and matching bounds if an asymptotic density exists. The sufficient target is f(N)=δN+o(N), with δ identified and proved optimal. Existence of an unspecified δ would itself be useful progress but would not determine the optimum. Existing Lean establishes only the 17/32 lower bound and nonconvergence to 1/2.

**One route tested.** Use homogeneity to transport extremizers, then seek subadditivity or superadditivity strong enough for Fekete's lemma to establish the density limit.

What is valid:
1. f(N) exists because the finite feasible family is nonempty. Restriction and addition of at most one new point give f(N)≤f(N+1)≤f(N)+1.
2. A→qA preserves the reciprocal equation for integer q≥1, so f(qN)≥f(N). It does **not** multiply cardinality by q.
3. Independent placement in translated blocks fails. The triple-free set {1,2,10} translated by 2 becomes {3,4,12}, which contains 1/3=1/4+1/12. For the original set the only possible smallest reciprocal denominator is 1, and 1/2+1/10≠1. Thus ordinary interval restriction cannot be identified with an extremal problem on a translated prefix.

The desired uncorrected inequalities are actually false, not merely unproved:
- Superadditivity: f(5)=5 and f(10)=9, so f(5+5)<f(5)+f(5). The only distinct unordered denominator triple through 10 is {2,3,6}; omit 2 to achieve 9.
- Subadditivity: f(6)=5, f(12)=10 and f(18)=16, so f(6+12)>f(6)+f(12). Through 12 the triples are {2,3,6}, {3,4,12}, {4,6,12}; no single vertex meets all three, and deleting 3,6 suffices. Through 18 the additional triples are {6,9,18}, {6,10,15}. The disjoint triples {3,4,12} and {6,10,15} force at least two deletions, and deleting 3,6 meets all five.

Enumeration is exact: choose a<b<c; clearing denominators forces c=ab/(b−a), so divisibility and c≤N generate every triple. A finite minimum hitting-set calculation through N=30 independently checked these values; its output is `finite-E302-check.json`. The above small witnesses and covers are the proof, not an extrapolation from the finite list.

**Outcome/core failure.** Homogeneity and the one-step Lipschitz bound survive, but neither ordinary Fekete hypothesis survives. This excludes this naive route to a limit; it does not exclude corrected inequalities, a different scaling decomposition, a density limit, or a full solution. The exact missing ingredient for this route is a justified composition/comparison theorem with asymptotically negligible error strong enough to force liminf f(N)/N=limsup f(N)/N. Even that would leave identification and sharpness of δ. No new asymptotic bound or density-limit theorem is claimed.

## PR5084 / E291 — simultaneous p-adic leading-digit avoidance

**Exact missing full statement.** With L_n=lcm(1,...,n) and a_n=Σ_{j≤n}L_n/j, prove that {n≥1:gcd(a_n,L_n)=1} is infinite, and retain the already established infinitude with gcd>1. Equivalently, for every N there is n≥max(N,1) avoiding every common prime divisor simultaneously.

**One route tested.** Derive the exact local criterion, then use simultaneous logarithmic recurrence to enforce admissible leading digits for a growing set of primes.

For a prime p≤n put e=floor(log_p n), d=floor(n/p^e)∈{1,...,p−1}, and U=L_n/p^e. By the lcm valuation formula v_p(L_n)=e, U is a p-adic unit. All j not divisible by p^e contribute 0 modulo p to a_n. The remaining j are j=tp^e, 1≤t≤d, and contribute U/t in F_p. Therefore

    a_n ≡ U H_d (mod p),       H_d=Σ_{t=1}^d t^(−1) in F_p.

In particular p divides gcd(a_n,L_n) iff H_d=0 in F_p. The unit U must be retained; the page's informal congruence with H_d is an equivalence of vanishing, not generally literal equality. This proof is unconditional. Define Z_p={d∈[1,p−1]:H_d=0 in F_p}. Then coprimality is exactly d_p(n)∉Z_p for **every** prime p≤n. H_1=1 ensures leading digit 1 is always safe. For odd p, H_{p−1}=0 by pairing t with p−t; p=2 is an exception (its sole leading digit 1 is safe).

A real simultaneous result follows for every fixed finite set S of primes: there are unbounded integers n whose leading digit is 1 in each base p∈S. Here is a proof rather than an independence assumption. Fix t0=log(3/2). Then {t0/log p} lies strictly inside (0,log_p 2) for each p∈S. There exist unbounded positive integers q_j with q_j/log p tending to 0 modulo 1 for all p∈S simultaneously. The elementary simultaneous Dirichlet pigeonhole argument gives, for each Q, an integer 1≤q≤Q^|S| with all distances to integers ≤1/Q. If such q are unbounded, take a subsequence. If they stay bounded along an infinite subsequence, one fixed q is an exact common period, and its multiples give unbounded returns. Thus no rational independence of 1/log p is required for recurrence to the identity. For n_j=floor(exp(t0+q_j)), log n_j−(t0+q_j)→0. The fractional parts remain inside the safe open intervals, proving the claim.

**Outcome/core failure.** This proves finite-prime avoidance at arbitrarily large n, not coprimality. The quantifiers are ∀ finite S ∃ unbounded n avoiding S, whereas the goal requires avoidance of {p:p≤n} at the same n. The recurrence proof gives no bound forcing its returned n below the prime cutoff chosen in advance. A diagonal sequence avoiding larger initial prime sets can still acquire a bad new prime above each cutoff. Primes p>n/2 are automatically safe (d=1), but the uncontrolled range from the fixed cutoff through n/2 remains. Choosing powers of 2 alone also does not solve the problem: n=8 has leading digit 2 in base 3, so 3 divides the gcd.

The exact missing lemma is a quantitative simultaneous avoidance theorem with a cutoff covering all relevant primes of its own witness, or another construction proving ∀N∃n≥N∀p≤n,H_{d_p(n)}≠0. Neither the finite-prime recurrence nor the heuristic x/log x estimate supplies it. This is useful unconditional local and finite-simultaneous analysis, not a proof of coprime infinitude.

## PR5085 / E367 — repeated square divisors and gcd/CRT control

**Exact missing full statement.** For every fixed k≥1 and ε>0, eventually

    P_k(n):=∏_{i=0}^{k−1} B_2(n+i) ≤ n^(2+ε).

Allowing a constant C_{k,ε} is equivalent after using ε/2 and enlarging the threshold. A disproof needs one fixed k and ε>0 with unbounded witnesses violating such an eventual bound, equivalently polynomial excess above exponent 2. The existing n² log n lower bound does not do this. The analogous r≥3 questions remain outside this three-gap main target.

**One route tested.** Decompose repeated prime powers into square divisors; combine the fixed-length gcd restriction with CRT to seek an upper bound independent of k in its exponent.

Write m_i=n+i and

    d_i=∏_p p^floor(v_p(m_i)/2),    m_i=s_i d_i²,

where s_i is squarefree. Then d_i² divides m_i, and d_i²≤B_2(m_i)≤d_i³ because a≤3 floor(a/2) for every a≥2. Consequently if Q=∏d_i, then Q²≤P_k(n)≤Q³. Also, for i≠j,

    gcd(d_i,d_j)² divides |i−j|,

and gcd(B_2(m_i),B_2(m_j)) divides |i−j|. In particular a prime ≥k cannot divide two different m_i. Small primes can nevertheless have arbitrarily high valuation in one m_i; their total powerful contribution cannot be discarded as a k-dependent constant.

Let D=lcm(d_0,...,d_{k−1}). The repeated exponent loss is bounded uniformly for fixed k. Prime by prime, sum of valuations minus their maximum is at most the sum of all pairwise minima; the latter are valuations of pairwise gcds. Thus

    Q/D divides ∏_{i<j}gcd(d_i,d_j),
    Q ≤ C_k D,   C_k:=∏_{i<j}floor(sqrt(j−i)).

The empty product is 1. Since D² divides ∏m_i, this yields only the weak P_k(n)≤C_k³(∏m_i)^(3/2); the direct P_k(n)≤∏m_i≤(n+k)^k is better. Neither gives exponent 2+ε for k≥3. Bounded overlaps address repeated primes, not the size of the distinct square factors.

CRT imposes the compatible congruences n≡−i (mod d_i²), with common modulus D²≥Q²/C_k². A large modulus does **not** force its least positive solution to be large. This proposed obstruction already fails for arbitrarily large two-term examples: Pell solutions x²−8y²=1 give n=8y², n+1=x²; choosing d_0=2y and d_1=x makes the moduli 4y² and x² coprime, with product 4y²x² asymptotic to n²/2, yet the simultaneous solution is n. The chosen divisors need not be maximal d_i for this counterexample to the modulus-to-size inference. Thus even genuinely simultaneous large square divisors can occur far below the CRT modulus.

**Outcome/core failure.** Exact gcd, square-divisor, and CRT facts survive; they produce no desired uniform exponent bound. A sufficient additional bound for this particular decomposition would be Q≤n^(2/3+ε/3) eventually for every ε>0, but that condition is too strong even for k=2 square-rich Pell pairs. A viable completion must instead control P_k(n) itself, or use more precise square/cube exponent information and a nontrivial Diophantine size estimate across the whole fixed block. No such estimate is proved here. The Pell family does not refute the original exponent-2 question; it refutes only the proposed CRT size shortcut. This route failure is not an impossibility claim.

## Ledger handoff

For all three originals keep full=false, ready=false, can_submit_full_solution=false. New work is the explicitly proved route analysis above, with an actual obstruction or quantifier gap for each. Existing partial Lean targets were read, not recompiled; no new formal theorem or axiom audit was generated. The focused pass is complete, while the underlying three full mathematical repairs remain unresolved. The final source integration validation mentioned by the user is external context and is not represented as a new check performed in this sidecar.
