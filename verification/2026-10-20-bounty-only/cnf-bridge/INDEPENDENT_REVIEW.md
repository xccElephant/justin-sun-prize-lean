# Independent n12 CNF bridge review — October 20, 2026

Verdict: no substantive findings in the reviewed current source or independently checked certificate data. The source implements the requested implication from an arbitrary no-C5 subset of [1,12] with cardinality 9 and even count 6, through normalization and an explicit assignment satisfying the exact archived CNF, to contradiction from the archived LRAT. This is a source and data review; compilation and final emitted axiom lists remain the parent's responsibility. No exit-0 compilation is claimed here.

Scope: CompressionCounts.lean, SequentialCounter.lean, CycleWitness.lean, SatCertificate.lean, N12Certificate.lean, N12Clauses.lean, and Research/Erdos883/scripts/generate_n12_bridge.py. The generator resides under Research/Erdos883/scripts, rather than a repository-root scripts directory. I also read the directly relevant existing Compression.lean dependency and the local Mathlib SAT reconstruction and cycleGraph definitions. No network, rebuild, source edits, commits, or broader candidate investigation was performed. The only filesystem write by this reviewer is this report.

## Arbitrary set to normalized counterexample

N12Clauses.lean:2678 defines n12_b0_has_five_cycle_via_lrat with only interval inclusion, cardinality 9, and selected even count 6 as input assumptions. Its proof assumes no contained cycleGraph 5 by contradiction and applies exists_compressed_prefix_counterexample from Compression.lean. The resulting B preserves interval inclusion, cardinality, even count, and absence of C5, and has both required normalization properties. Thus satisfies_formula's normalization and no-cycle hypotheses are discharged rather than added to the final statement.

The direction of compression is correct: replacement enlarges prime support, so any coprime edge involving the replacement vertex pulls back to an edge involving the removed vertex. The restore map is injective on the replacement set because the removed vertex is erased and the inserted vertex was not originally present. Hence a graph copy in the replacement set yields a copy in the original; absence in the original implies absence after replacement. This does not require the converse.

Candidates contain A itself and impose no normalization condition. Support weight is maximized first, then prefix weight among support maximizers. A missing strict support enlargement contradicts support maximality; a missing smaller equal-support representative preserves support weight and contradicts prefix maximality. Positivity comes from interval inclusion when extracting prime divisibility and parity. There is no assumption that the two normalization procedures commute, and no finite coverage theorem is used to establish existence of B.

The total_mem lemma identifies B with the injective image k ↦ k+1 of selected indices in range 12. total_not_mem then gives exactly three absent inputs. all_evens derives membership of all six even vertices from interval inclusion and the even count, rather than assuming these unit clauses independently.

## Assignment, literal conventions, and counters

Mathlib's Literal.ofInt maps DIMACS ±d to Sat literals on d-1. Valuation.neg means literal falsification: positive d supplies ¬v(d-1), negative d supplies v(d-1). The generated implication-shaped satisfaction proofs respect both conventions, including positive membership literals arising from negated complement inputs.

Allocation matches the archive exactly:

- DIMACS 1..12 → Sat 0..11: membership of vertices 1..12.
- DIMACS 13..120 → Sat 12..119: 12 rows of nine membership-counter columns.
- DIMACS 121..156 → Sat 120..155: 12 rows of three complement-counter columns.

The assignment row is the number of processed inputs, starting at 1; column j means at least j+1 selected inputs in that prefix. Initial higher columns are false. Increment and propagation clauses use the previous prefix i and the new prefix i+1. Overflow at input index i prohibits previous column k-1, whose actual threshold is k, not k+1. It is justified by total ≤ k and a true next input. The final input i=11 is covered; the extra final auxiliary row i+1=12 is allocated and satisfies its implications. There is no counter off-by-one or index-156 alias.

Independent Python constructed the two counter blocks separately and compared their clauses and order to the archive: membership at-most-nine is clauses 11..228; complement at-most-three is clauses 229..308. For all 4,096 membership bit masks, the explicit prefix-count assignment satisfies each counter block exactly when its corresponding total is at most its bound. The membership block accepted 4,017 masks; the complement block accepted 299. These checks concern counter semantics and are not a graph finite-coverage proof.

## Formula identity and generated proof structure

formula and refutation both include the same archive path, verification/2026-10-20-bounty-only/certificates/n12_b0_l2.cnf. dimacs_formula and Mathlib.fromLRATAux both parse it with the same Mathlib parser and buildConj construction. The generator's recursive split matches buildConj's balanced split. Each satisfies_one leaf has the expected archived clause before its change tactic; leaf labels run consecutively 1..321.

Independent reconstruction of the header and all clauses equals the complete archived bytes, including order, spaces, terminal zeros, and final newline: 3,363 bytes, header p cnf 156 321, maximum variable 156. SHA-256:

    0de600b326666f3c8edee110b4a53a40e16eb3c5d22cc122e1336f7bac8b40eb

I executed the current generator with Path.write_text intercepted in memory, preventing source writes. Its output is byte-identical to the current N12Clauses.lean. Its generated clauses reconstruct the archive byte-for-byte. This was repeated after the support_facts update.

The local Mathlib DIMACS parser reads the declared number of clauses without an explicit end-of-input check. That is not a finding for this pinned file: independent checking found precisely 321 terminated clauses and no trailing payload. The source does not embed a hash pin; byte identity here refers to the presently archived file, whose bytes are recorded above.

## Seven blocking clauses and current prime-factor repair

Clauses 315..321 use the following concrete witnesses, in order:

- [5,2,7,4,11]
- [3,2,5,4,7]
- [3,2,9,4,5]
- [7,2,3,4,9]
- [3,2,11,4,5]
- [3,2,9,4,11]
- [3,2,11,4,7]

I independently checked injectivity and coprimality for every edge of cycleGraph 5, including the wraparound edge. Membership missing from a blocking literal is supplied by the proven prefix implications 4 → 2 and 9 → 3. CycleWitness.lean defines IsCycleWitness using injectivity, vertex membership, and preservation of every cycleGraph adjacency; its conversion builds an injective graph homomorphism into the induced coprime graph. The blocks therefore assert actual graph copies, not merely five selected vertices or four path edges. Extra coprime chords do not matter for IsContained.

The current generated file has private pf4, pf8, pf9, pf6, pf12, pf10 lemmas at lines 16..43, deriving prime-factor sets using Nat.primeFactors_prime_pow and Nat.primeFactors_mul. Their nonzero and primality premises agree with the local Mathlib signatures and the concrete arithmetic. support_facts at lines 45..50 rewrites those facts and prime/one facts, then uses <;> decide. The generated support equalities and strict inclusions now use this tactic at the ten normalization clauses and all missing-vertex derivations. The repair introduces no graph assumption, custom axiom, native_decide, or certificate change. Using <;> decide permits simp to close equality goals without an ensuing no-goals error. Actual successful elaboration remains to be confirmed by the parent.

## LRAT reconstruction and dependencies

Independent Python replayed all additions with their ordered RUP hints and deletions, requiring each referenced clause to be unit or conflicting under falsification of the proposed clause. It validated additions 324 (four literals, 12 hints), 325 (three literals, nine hints), 326 (one literal, 23 hints), and 328 (empty clause, 17 hints), with 307 clause deletions. No RAT hints were needed. LRAT SHA-256:

    30d1955972369d52913c2da60416fef266b412a88fd0cf3022cf9ec36bc161f9

SatCertificate delegates to the existing Mathlib proof reconstruction and returns its proof of formula.proof []. This means every valuation satisfying formula satisfies the empty clause, hence False. The final theorem applies this proof to assignment B and its proven formula satisfaction. Unsafe string evaluation is elaborator machinery; it is not itself a proof axiom. Reconstructed declarations and the returned proof must still pass Lean checking. The generator is likewise outside the proof trust boundary because its leaf proofs are checked against the separately parsed formula.

The transitive local import closure is Compression, CompressionCounts, CycleWitness, SequentialCounter, SatCertificate, N12Certificate, N12Clauses. There is no import or theorem reference to FiniteWitness, Check, or ThirdParty.PartII on the bridge's dependency path, and no cycle back to the new graph theorem. Source scans found no sorry, admit, native_decide, or axiom declarations in this closure. The existing direct finite theorem and Check adapter are outside this bridge. Printed axiom directives alone are not proof of a clean successful build; the parent reports that the prior run emitted clean main-theorem axiom sets, but its final exit-0 rerun remains unverified by this reviewer.

## Separate count/cmax monotonicity generalization

CompressionCounts.lean:20 proves selectedCount_le_replace for arbitrary decidable P from P x → P y. If P x holds, both removed and added elements satisfy P and the count is equal. If P x does not hold, no P-selected element is erased, so the filtered original embeds in the filtered replacement. The inequality direction is correct.

CompressionCounts.lean:36 adds the lower bound on selected odd multiples of three to candidates. A witnesses nonemptiness. Same-parity support enlargement preserves the forward predicate implication: oddness is retained and the prime factor 3 of x divides y. Consequently every permitted replacement preserves the candidate lower bound. Equal-support prefix replacement also preserves parity, keeps support weight fixed, and stays among support maximizers. The simultaneous normalization argument remains valid for arbitrary n and H; n=0 is harmless because the closure conditions are vacuous.

This proves count(A) ≤ count(B), with size and even count equal. It is sound for preserving a count lower bound, including one used in a cmax argument. It does not prove equality of that count or preservation of an upper bound on it. No theorem named cmax is defined in these files, so no downstream extremal conclusion is certified here. The n12 bridge uses the original normalization lemma and does not depend on this generalization.

## Limits and reviewed snapshot

No substantive concern was found. This review does not claim a successful Lean build, validate the complete Erdős 883 conjecture, or establish integration of the LRAT theorem into the existing Check adapter. All kernel acceptance and emitted axiom-list conclusions require the parent's completed compilation. The independent data checks supplement, rather than replace, kernel checking.

Reviewed source SHA-256 values (to distinguish concurrent parent edits):

- Research/Erdos883/CompressionCounts.lean: `165d0c4377dfccb7fa08bce5f00ed13785713353ac72d86b5f0e5b68eec31896`
- Research/Erdos883/SequentialCounter.lean: `a35524d68ed95439b160da472a295986db7515491a9de5d281a9a72cd79e743a`
- Research/Erdos883/CycleWitness.lean: `e1850035f9a36cc1e00872b309fac6ed9f3835a7d25f7fb3cee0e33635f5f158`
- Research/Erdos883/SatCertificate.lean: `c9b2d4cd5fa4c6d088d6e4157c1713cd2117b208aaab00ed3a7af62a68bd2ea0`
- Research/Erdos883/N12Certificate.lean: `32ff674af5f612c6d291482162d3c60aca3f475257af289f9d3c017d41efef65`
- Research/Erdos883/N12Clauses.lean: `00f18b5854c7258a5ae4dffbc72d5b5ac4fc0dee79cc640cf556e0fb4d5bbc0c`
- Research/Erdos883/scripts/generate_n12_bridge.py: `dbf9b4f513e50ea9e96f2113fca3b096fb0894893838e2464f46ae3b2ad0b796`
- Research/Erdos883/Compression.lean: `e64011c81f45c064bc1f4e340c265e0c7b351868e860c7e4a0702b537b95b2a7`
