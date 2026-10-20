# Final bounded finite-graph audit — 2026-10-20

**Result: neither candidate exposes a genuine remaining mathematical endpoint to take on.** Audited exactly JSP-000139 and JSP-000760. This is bounded source evidence, not a build certification.

## Pins and corroboration

Local repositories read first: `reference/awards` **87402fe6cbbff6844f7e324f30a4348477b196a4**; `reference/formal-conjectures` **e754a78c74a3f2bbc38e4f2063b5f6eed51bde39**; `reference/lean-proofs` **8822f7ddef30fadbd92e1c6ab4ed897af356af5e**. Relevant proof files have no working-tree modifications. All proof paths below are relative to `reference/lean-proofs/src/latest/` at that exact pin (headers specify Lean/Mathlib v4.33.0).

Minimal live reads: Erdős original pages `/133` and `/916` (HTML and extracted text saved in `graphs-evidence/`), GitHub commit lookup via `gh api`, and pinned raw `Erdos133.lean`, `Erdos916.lean`, and `Erdos916/AHTSourceTheorem66.lean`. All three raw files compare byte-identically with local sources. No PR-state claim is needed or made; no external writes occurred.

## JSP-000139 → Erdős 133

**Mapping evidence:** awards `problems/catalog-0101-0200.md:666` asks the triangle-free diameter-two maximum-degree growth question and cites Er97b, HaSe84, FuSe94, HaLe18. The original `/133` asks the growth of the minimum possible maximum degree and whether its quotient by √n diverges; it names the same constructions and references. `FormalConjectures/ErdosProblems/133.lean:43–75` defines `f` and explicitly links the pinned actual proof. The mapping is by statement and bibliography, not the number 139.

**Exact endpoint:** `Erdos133.lean:597`, `Erdos133.erdos_133`, proves for every n≥64:

- √n−1 ≤ `erdos133Function n` ≤ 4√n;
- `Asymptotics.IsTheta atTop` with √n;
- the quotient does **not** tend to `atTop`.

**Complete route inspected:** `HasDiameterTwo` (:41) requires each distinct pair to be adjacent or share a neighbour. `Model` carries a genuine finite graph, cardinality, triangle-freeness, this diameter condition and a degree bound; `erdos133Function` (:57) is the infimum over available models. `moore_bound` (:64) counts the radius-two neighbourhood to get n≤d²+1. The explicit base graph on `(Bool × Fin k)²` (:160–204) flips one coordinate and changes the other; the proof excludes triangles, constructs common neighbours for nonedges (:239), and bounds degrees by 4k (:295). Injectively indexed vertex duplication (:326–419) preserves triangle-freeness and diameter and increases degree by at most a factor two. With k=⌊⌊√n⌋/2⌋, q=(2k)², the parameter proof (:427) establishes q≤n≤2q, permitting exactly n−q duplicates. `exists_upper_model` (:464) supplies every n≥64; the infimum attainment, Moore bound, and real square-root estimates then yield the final result (:507–608). No conjectural existence input remains.

**Scope:** formal-conjectures uses graphs on `Fin n` with metric diameter exactly 2; the actual proof uses arbitrary finite types of cardinality n and the explicit distance-at-most-two predicate. For n≥3, a triangle-free graph satisfying that predicate cannot have diameter ≤1, because that would make it complete; hence its diameter is exactly 2. Relabelling by `Fintype.equivFin` identifies the extremal functions eventually. This equivalence is a mathematical scope check, **not an independently compiled Lean bridge to the formal-conjectures declaration**. The final source resolves the original growth/divergence question; it does not prove the sharper √2 or 2/√3 constants, nor the still-open asymptotic constant 1. Those are separate stronger questions, not a missing final step here.

**Disposition:** already has a same-scope source solution. No new candidate.

## JSP-000760 → Erdős 916

**Mapping evidence:** awards `problems/catalog-0701-0800.md:1015` asks for a linear edge bound forcing a cycle and an external vertex with three rim neighbours, citing Dirac Di60 and Thomassen Th74. Original `/916` specifies **2n−2 edges**, describes the special K₄-subdivision strengthening of Dirac, and attributes the affirmative result to Thomassen. There is no `FormalConjectures/ErdosProblems/916.lean` at the local pin. Numerical Erdős 760 is instead a cochromatic-number problem; its source was inspected only to reject the erroneous numeric mapping.

**Exact endpoint:** `Erdos916.lean:26`, `Erdos916.erdos_916` (alias `erdos916` :34), for any finite simple graph in any universe, with n≥4 and exactly 2n−2 edges, proves `HasWheelWitness`. Its definition in `Erdos916/Core.lean:35` is a genuine `Walk.IsCycle`, a vertex outside the walk support, and cardinality ≥3 of the intersection of its neighbours with the support finset. Thus the rim vertices are distinct; it is not merely a K₄ minor or unrestricted subdivision.

**Complete route and direct load-bearing bodies inspected:** `CoreClassification.lean:258` extracts a minimal dense induced vertex set and retains a spanning (2,3)-circuit. Circuit sparsity gives minimum degree three. The AHT theorem supplies degree-three false twins in a wheel-free graph. `BlockPathDecomposition.lean:977` deletes the twins and applies the three-common-neighbour path/three-block alternative; either branch forces a wheel in the circuit, which then lifts to the ambient graph. `Assembly.lean:75` assembles the dense result conditional on the false-twin principle; **the public endpoint actually discharges that principle**, rather than leaving it assumed.

Specifically, `AHTSourceTheorem66.lean:3212`, `aht_theorem66`, has a real strong-induction body. It chooses a degree-three noncentre, deletes it, invokes `AHTWatkinsMesnerSplitter.lean:16812` (`exists_watkinsMesnerSplitter`, whose final constructive body was read), and applies `twoPairs_of_splitter_below` (:3118). The latter consumes strictly smaller fragment recursions and the completed terminal/mixed-side/final three-by-three cases. Section 7's `AHTSection7TwoSeparation.lean:5743` proves the pointed reduction by strong induction, including boundary-adjacent and high-boundary branches. `AHTConnectivity.lean:442` handles connected components; `AHTUniverse.lean:34` transports the finite Type-zero theorem along `Fin (card V)`. `AHTFinalAssembly.lean:21,52` composes these results and the public theorem passes **`aht_theorem66` itself**. Old comments describing remaining work are superseded by these final bodies.

**Scope:** n≥4 is necessary for the standard statement: the literal webpage wording includes the isolated n=1,m=0 counterexample; n=2,3 cannot attain 2n−2 edges in a simple graph. This is a small-order correction, not an actionable new theorem. The public declaration uses equality, exactly as the original; ≥2n−2 follows mathematically by selecting that many edges and witness monotonicity (`Core.lean:51`). That extension was not separately compiled. The practical hard dependency is the extensive AHT/Watkins–Mesner structural machinery; its source already exists, so this is not a short unfinished exercise.

**Disposition:** already has a same-scope source solution for the meaningful original range. No new candidate.

## Evidence limits

`graphs-evidence/source-closure.json` records hashes and a static recursive scan of all local non-Mathlib imports reachable from both endpoints: **74 existing source files**, no missing project imports, and no `sorry`, `admit`, or `axiom` tokens outside comments. One `Lean.Elab.Tactic.Omega` import belongs to the Lean standard library and is excluded from project-missing counts. This scan is not a kernel axiom report, does not recursively inspect Mathlib/Lean, and does not establish correctness of every dependency body. Human reading focused on definitions, endpoint bodies, the complete construction for 133, and the direct structural/final-assembly inputs for 916. **No Lean build, replay, or `#print axioms` execution was performed.** The file's `#print axioms` command is source text only. No commits, PRs, messages, or unrelated candidate expansion.
