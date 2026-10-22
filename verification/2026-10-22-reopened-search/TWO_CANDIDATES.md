# Two-candidate reopened audit — 2026-10-22

Scope: exactly JSP-000391 and JSP-000930. Read-only source/PR inspection; this report is the only authored artifact. No commits, messages, PR edits, new candidates, or builds. This is a bounded statement/dependency audit, not a fresh kernel or independent human certification.

## Verdict

| Candidate | Actual original problem | Complete mathematical route | Actual prior Lean endpoint / remaining contribution |
| --- | --- | --- | --- |
| JSP-000391 | Erdős **482**, not 391 | Stoll's explicit arbitrary-base alternating floor construction for every positive real, hence every positive algebraic real | Faithful prior full endpoint exists: `JSP000391.stoll_general_base` and `JSP000391.jsp000391` at **14e5155e68554de4e053e4aacd77095a93e96dd4**. No missing final original-problem contribution identified. |
| JSP-000930 | Erdős **1119**, not 930 | Positive ZFC case `m⁺ < c`, plus opposite consistency models at `m=aleph₁`, `c=aleph₂` | Fixed plby endpoint proves only the positive case; separate prior Wetzel biconditional covers countable values. Full general-cardinal independence endpoint is absent from inspected roots. Genuine large scope gap, not a small final lemma. |

The second row is a source-bounded gap finding, not a worldwide nonexistence or bounty entitlement claim. Neither candidate supplies an identified inexpensive new complete bounty proof.

## Fixed evidence and ledger

Local checkout pins obtained with `git rev-parse HEAD`:

- `reference/awards`: **87402fe6cbbff6844f7e324f30a4348477b196a4**. Read actual rows `problems/catalog-0301-0400.md` (JSP-000391, line 1572) and `problems/catalog-0901-1000.md` (JSP-000930, line 500). Both record Solved / Lean proof No / Eligible No. JSP-000930 explicitly records independence, rather than a ZFC proof of the affirmative statement.
- Local discovery ledger `reports/discovery-2026-10-19/pool.json`: read both full records, including references and review notes. `reports/strategy-2026-10-19/catalog-screen.json` agrees. Neither appears in the narrower `reports/parallel-campaign-2026-10-19/acceptance-ledger.json`; no invented acceptance-ledger record.
- `reference/formal-conjectures`: **e754a78c74a3f2bbc38e4f2063b5f6eed51bde39**; actual `FormalConjectures/ErdosProblems/482.lean` and `1119.lean` read. These are specification roots with `sorry`, not completed proofs.
- `reference/lean-proofs`: **8822f7ddef30fadbd92e1c6ab4ed897af356af5e**; read actual `src/latest/ErdosProblems/Erdos482.lean` and `Erdos1119.lean`, plus companion markdown. Each imports Mathlib directly, and the relevant proof bodies are present rather than assumptions.
- `reference/erdosproblems`: **6f63fe53e757f2976fd8559c1e02f0726074c38f**. Its #1119 record explicitly distinguishes Collin Yuanjie Ren's countable-values CH biconditional from general-cardinal independence.
- Local Mathlib **0df444a360eaa60ab8c11dca51a86af692955474**, workspace Lean **v4.33.1**: used only for immediate-library source inspection. This is not the external proof's toolchain and no cross-version compile is claimed.

Live original pages were successfully read in the browser on 2026-10-22: https://www.erdosproblems.com/482 and https://www.erdosproblems.com/1119. Direct HTTP requests to those pages were denied, but browser text exposed the original formulas and scope. The #482 page cites Erdős–Graham 1980 p.96 and explicitly asks for similar results for sqrt(m) and other algebraic numbers. The #1119 page identifies Hayman Problem 2.46, requires **aleph₀ < m < c**, and describes opposite models at c=aleph₂. The bibliography match and mathematics establish the mapping, independently of numeric filenames or PR titles.

Minimal live public corroboration: read PR https://github.com/TheJustinSunPrize/awards/pull/293 and https://github.com/TheJustinSunPrize/awards/pull/4140; both displayed Open. Read fixed-source links from PR https://github.com/TheJustinSunPrize/awards/pull/179. GitHub API requests were rate-limited (403), so no exhaustive current PR or review-status claim is made. PR prose, checklists, or file titles were not treated as scope proof.

## JSP-000391 / Erdős 482

The original is open-ended generalization, not a demand that the unchanged sqrt(2) multiplier compute every algebraic target or every radix. The catalogue's prescribed-base phrasing warrants checking arbitrary g, not stopping at the existing binary theorem.

### Actual complete endpoint

Read both fixed raw files in full:

- https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/14e5155e68554de4e053e4aacd77095a93e96dd4/projects/jsp-000391/JSP000391Main.lean
- Its sole project import: https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/14e5155e68554de4e053e4aacd77095a93e96dd4/projects/jsp-000391/JSP000391.lean (imports Mathlib).

`stoll_general_base (g) (w e) (2 ≤ g) (0 < w) (-1/g ≤ e) (e < (g+1)(g-2)/g)` proves all extracted digits equal the standard floor-difference digits of `t=w/g^floor(log_g w)`, proves every digit lies in `[0,g)`, and proves decoded prefixes converge to t. `admissible_shift` shows the interval is nonempty for every g; `jsp000391` uses e=-1/g and has **no extra mathematical premise**. Note g=2 has interval [-1/2,0), so zero would be an invalid uniform witness; the actual proof uses the valid endpoint -1/g.

The actual recurrence is recursive, with initial value 1, coefficients `a=g/((g-1)(t+g))`, `b=(g-1)(t+g)` and alternating shifts e and 1/(g-1). It is not defined by its desired closed form. `multipliers` proves b=g/a. Integers, rather than natural truncating subtraction, are used for extracted differences. Sequence index zero is paper index one; digit index zero is the leading significant digit. For radix rationals, floors select the terminating expansion. Recovery of w follows from the stated normalization and its known power of g, rather than asserting the mantissa is w.

Proof chain actually read: `geometric_relation`; `initial_floor`; `expanding_floor`; `contracting_floor`; `sequence_closed_forms`; `expanded_prefix`; `recurrence_extracts_digits`; `digit_bounds`; `normalized_bounds`; `accumulated_eq_prefix`; `reconstruction_error`; `index_lt_radix_pow`; `reconstruction_converges`; `stoll_general_base`; `admissible_shift`; `jsp000391`. No sorry/admit/added axiom appeared in these two source files. `normalized_bounds` invokes Mathlib's `Real.floor_logb_natCast`, `Int.zpow_log_le_self`, and `Int.lt_zpow_succ_log_self`; reconstruction uses ordinary floor bounds and an Archimedean estimate.

Hardest local step is contracting_floor, and it has an actual proof. Write D=(g-1)(t+g), X=(t+g)g^n, q=floor(X), S=(g^(n+1)-1)/(g-1). The needed floor equality is floor(g(q+e)/D)=S. Since DS=gX-(t+g), its lower bound follows from q>X-1 and ge≥-1, giving g(q+e)-DS>t-1≥0. Its upper bound follows from q≤X and ge<(g+1)(g-2): g(q+e)-DS<D, using (g-2)(t-1)≥0. This proves S≤g(q+e)/D<S+1. Induction gives the two interlaced forms; integer powers cancel in successive gaps, leaving the actual radix digit.

Toolchain and direct dependency lock were read at that same commit: Lean **v4.34.0**, Mathlib **5ed2965256430c3649e86755f9576b54eca72435**. PR293's build/kernel/NaNoda receipts are contributor claims; this audit did not replay them.

Independent additional fixed endpoint read: gotrevor/lean-gallery **a834bbad2f36eedcc16066b2bc4da49f98ab5b85**, `LeanGallery/NumberTheory/Erdos482/Statement.lean` alias `statement_erdos482_resolution` and its actual target `General/Erdos482General.lean`, theorem `erdos482_resolution`. It existentially supplies a,b,e with ab=g and gives every normalized base-g digit as `Real.digits`. Its body uses `mantissa_mem` and `thm13_digits`, choosing e=-1/g. This corroborates the canonical Mathlib digit presentation; no giant import closure was audited, because the smaller full two-file endpoint already suffices.

Local plby **8822f7...** theorem `stollBinary_resolution` proves the normalized arbitrary-real **binary** construction and reconstruction; `erdos_482` includes the original sqrt(2) recurrence. Its immediate hard floor lemmas `alpha_floor_step` and `beta_floor_step` and `stollBinary_closed_forms` were read. Binary scope alone would not justify closing the prescribed-base question; the fixed arbitrary-base endpoint above does.

Math source corroboration: Stoll's primary JIS page https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.html was read; its abstract states arbitrary positive real targets and every integer g≥2, and links the paper. The full PDF and all Stoll 2006 refinements were not reconstructed. Costs: duplication is moderate elementary Lean floor arithmetic plus normalization; rebuilding dependencies could be large but creates no identified missing original endpoint. No new contribution recommended on this evidence.

## JSP-000930 / Erdős 1119

### What the existing actual roots prove

At plby **8822f7ddef30fadbd92e1c6ab4ed897af356af5e**, actual root `src/latest/ErdosProblems/Erdos1119.lean`:

1. `coincidenceSet_countable`: two different entire functions coincide at countably many points.
2. `entireFamily_cardinality_le_continuum`: encode continuous functions on a fixed countable dense sequence; entire families have size ≤c.
3. `exists_separating_point_of_mk_lt_continuum`: for a family smaller than c, remove the union of pairwise coincidence sets.
4. `cardinality_le_of_succ_lt_continuum`: if aleph₀≤m and m⁺<c, extract a subfamily of size m⁺ and obtain contradiction by evaluation injectivity into ≤m values.
5. Public `erdos_1119.variants.easy_case`: the actual general-cardinal positive range, with essential hypothesis **succ m < c**.
6. Public `erdos_1119`, aliased `erdos_1119.variants.erdos_wetzel`: pointwise-countable families are countable when aleph₁<c.

The headline name `erdos_1119` therefore does not have the original #1119 quantifiers. No uncountable-boundary countermodel, positive consistency theorem, or general independence endpoint occurs in this file. PR4140's prose asserting complete original correspondence is broader than the actual type.

Immediate hard dependencies were read: `Complex.analyticOnNhd_univ_iff_differentiable` in CauchyIntegral, `AnalyticOnNhd.preimage_zero_mem_codiscrete` in Analytic/Order (its immediate proof reduces to the identity-theorem alternative), and `IsLindelof.countable_of_isDiscrete` in Topology/Compactness/Lindelof. Thus f-g nonzero somewhere has discrete zero set, which is countable in C. This is a valid proof of the local analytic dependency, not an assumption that distinct functions differ everywhere.

Read the fixed separate root at CollinYuanjieRen/awards **49d433ee833f3d8d52b2fd839237c9c7639d6a07**, `submissions/jsp-000930-cyr/Erdos1119Wetzel/Main.lean`: `exists_uncountable_wetzelFamily_iff_continuum_eq_aleph_one` proves the exact countable-values/CH biconditional. Main imports Countable and Recursion; Recursion was read at declaration level (exists_step, transfinite fam, fam_spec, fam_injective, exists_uncountable_wetzelFamily_of_continuum_eq), and itself imports RationalLattice, Interpolation, IndexType. Their full proofs were not audited. The root's scope is plainly **m=aleph₀**, excluded by the original strict aleph₀<m hypothesis, so more closure inspection cannot turn it into the general-cardinal endpoint.

### Complete mathematical route and missing theorem contract

Let P mean: for every aleph₀<m<c, every set F of entire functions with ≤m pointwise values has |F|≤m. Since m<c implies m⁺≤c, the existing strict case reduces the unresolved case to m⁺=c. The original page and fixed specification record Kumar–Shelah (2017) positive and Schilhan–Weinert (2024) negative models, both c=aleph₂. Since the only cardinal strictly between aleph₀ and aleph₂ is aleph₁, these models settle P and its negation. This is a complete *published mathematics route*, not a proof of P in Lean's ambient cardinal model.

A full Lean independence contribution needs all of these obligations, with model-internal reals, analytic functions and cardinals, not ambient constants accidentally substituted:

1. Define/formalize ZFC syntax, satisfaction and the sentence P with faithful encodings of complex numbers and entire functions; prove agreement of the encoding with the intended analytic/cardinal statement.
2. Establish a usable forcing/model or syntactic relative-consistency framework, including forcing theorem/truth lemma and preservation infrastructure for each selected construction. A model approach must state its actual ground-model assumptions; a countable-transitive-model hypothesis must not silently be presented as merely Con(ZFC).
3. Transfer/formalize the existing coincidence-countability, continuum bound and strict-case theorem inside the models; prove reduction to m⁺=c and, when c=aleph₂, m=aleph₁.
4. Formalize the Kumar–Shelah positive construction: its posets/iteration and required preservation lemmas, c=aleph₂, and **every** pointwise-aleph₁ entire family has size ≤aleph₁ in the resulting model.
5. Formalize the Schilhan–Weinert negative construction: its posets/iteration and preservation lemmas, c=aleph₂, existence of aleph₂ **distinct** entire functions with ≤aleph₁ values at **every** complex point. Include analyticity of constructed functions and persistence of the pointwise restriction through the construction.
6. Derive appropriately stated `Con(ZFC) → Con(ZFC + P)` and `Con(ZFC) → Con(ZFC + ¬P)` (or explicitly qualified model-existence counterparts), then the nonprovability/nonrefutability conclusions via soundness. Do not insert either consistency claim as an axiom.

Hardest missing dependency: items 4–5, especially the universal positive model and the negative family's global pointwise restriction after forcing. They are **not proved by this audit**: the underlying papers/forcing proofs were not read in full within the bound, so no honest specific-poset lemma list or hardest-forcing-dependency proof is available. This is a material evidence limit: the theorem contract above is complete at the endpoint level, not a validated implementation blueprint. The fixed specifications' prose that independence is not directly a theorem about Lean's fixed model does not prohibit formalizing metatheory inside Lean; it requires changing the endpoint to consistency/satisfaction rather than filling the affirmative ambient `sorry`.

The strongest elementary dependency we can prove completely here is the strict-range argument already implemented. Given |F|>m, choose G⊂F of cardinal κ=m⁺. There are κ²=κ distinct pairs and ≤aleph₀ coincidence points per pair, so the collision union has size ≤κ·aleph₀=κ. If κ<c, select z outside it. Evaluation at z injects G into the ≤m permitted values, giving κ≤m, contradiction. If κ=c, the estimate becomes ≤c and the union may be all of C; the separating-point step disappears. This identifies the exact failure, with no reliance on the title or an unproved density heuristic.

Qualitative cost: the completed positive lemma is elementary cardinal arithmetic on existing analytic infrastructure; reproducing it or CH Wetzel work would duplicate existing scope. Full boundary independence needs substantial set-theoretic metatheory, analytic coding and two specialized forcing developments. Expect a major research formalization project, not hours/days of final Lean glue. The local Mathlib SetTheory/ZFC files exist; this audit did not establish a ready-to-use forcing implementation, and their existence alone is not evidence that items 4–5 are available.

## Limits and next decision

No fresh compile, kernel replay, NaNoda check, broad candidate scan, priority adjudication, organizer acceptance check, or payment assessment. Original pages and fixed main types were actually read. Source-only completeness for #482 is strong enough to reject a *missing-final-endpoint* opportunity without giant builds. For #1119 the gap is supported by exact types, but full forcing proofs remain unverified and an exhaustive search for other independent implementations was not performed. Preserve that distinction: a genuine gap in reviewed sources is not a ready complete bounty route.

Parent steering about an unrelated previously completed endpoint was treated only as a instruction to stop broadening; no third candidate was audited.
