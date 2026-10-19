# Bounded assessment: JSP000641 and JSP001018

**Decision: stop both; no concrete missing full-problem route found.** Existing fixed source covers the complete original questions, with stronger extensions. No competitor builds, Lean scratch, PR mutations, or new proof work were performed. Retrieved competitor files are evidence only, with attribution retained; they are not new contributions.

Catalog checked at `fd8fa66abb4e21df828fdebc25298e9ad75521bd` in `reference/awards`, using the requested census/candidate/PR metadata. Online retrieval crossed local midnight into 2026-10-20; this directory retains the assigned 2026-10-19 name. Evidence and hashes are in `evidence/`.

## JSP000641 = Erdős 781

**Scope verified:** least interval length f(k) forcing a monochromatic strictly increasing k-term sequence with nonincreasing ordinary gaps under every two-coloring; estimate f(k), and decide the proposed identity f(k)=k²−k+1. Reflection of positions and values transfers ascending to descending waves. Fin n represents a translated n-element positive interval; midpoint inequalities are invariant under translation.

**Primary proof obtained and read:** Alon–Spencer, *Ascending Waves*, JCTA 52 (1989), 275–287, author-hosted `https://web.math.princeton.edu/~nalon/PDFS/Publications1/Ascending%20waves.pdf`, saved completely (604557 bytes) as `evidence/alon-spencer.pdf` with extracted text. Theorem 1.1; complete cubic lower proof Section 1, pp.276–282, including Lemma 1.7 floor-profile count. This is a genuine cubic lower argument, not merely the intermediate cubic/log² bound of Remark 1.6. Also obtained LeSaulnier–Robertson arXiv:math/0506351v1 full HTML: Theorem 1, Lemma 1.1, Corollary 1.2 supply the stronger constructive upper route.

**Complete earlier endpoint:** `plby/lean-proofs` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, `src/latest/ErdosProblems/Erdos781.lean`, `Erdos781.erdos_781` (line 3201). It proves

```
(∀ k, 2^50 ≤ k → k^3 ≤ 2^48 * waveRamsey k ∧ waveRamsey k ≤ 8*k^3+1)
∧ ¬ (∀ k, waveRamsey k = k^2-k+1).
```

`waveRamsey` is genuinely the infimum of forcing interval lengths, with attainment/minimality proved. `IsDescendingWave` requires strict increase and the actual midpoint inequality; `Monochromatic` requires one common color. The cubic lower is proved through finite seed/profile counting and progression control, not assumed. Imports are Mathlib; no custom axioms or sorry/admit/native_decide occurred in the inspected file. Mathematics credited to Alon/Spencer; formalization credited to Codex/GPT-5.6 Sol.

**Strongest inspected same-scope endpoint:** PR1193, current awards head `be70ff8b1d2398c2e8eeac4a3cbfcabdd0d5ffd1`; external `KunHcz/jsp-nonpinnacle-proofs` at `2f3b421d2ec67f783e3372d3107a9b468b2b22e9`, package `submissions/jsp-000641-cubic`, `JSP641/Main.lean:75`, theorem `JSP641.jsp_000641`:

```
(∀ k, 2^50 ≤ k → k^3 ≤ 2^48 * Erdos781.waveRamsey k
  ∧ 6*Erdos781.waveRamsey k ≤ k^3+5*k)
∧ ¬ (∀ k, 2 ≤ k → Erdos781.waveRamsey k = k^2-k+1).
```

This retains the attributed prior lower proof and adds the stronger all-color constructive upper formula. `boolean_forcing_iff`, `ramsey_eq_original`, and `positive_descending_interval` explicitly bridge palette, minimum, and positive interval models. Contributor-published fixed verification records report seven clean modules, 55 axiom closures using standard axioms, and Nanoda closure checks. Those records were retrieved, not rerun or treated as independent human approval.

PR54's finite [1,133], k=12 certificate is supplemental; it is not the complete cubic estimate. Its proposed finite work is already public. PR4053 instead mistakenly cites Erdős641/Erdos641.lean; that numbering mismatch does not invalidate the correctly mapped complete source above and does not create a vacancy.

## JSP001018 = Erdős 1213

**Scope verified:** for each positive initial integer a and positive upper gap K, choose F(a,K) before the finite sequence; every nonempty strictly increasing sequence starting at a, with adjacent gaps ≤K and last value >F, has two distinct nonempty consecutive index intervals with equal actual sums. Overlap is allowed; the intervals need not be adjacent to one another or have equal lengths. No quantitative optimality or polynomial-in-K theorem is required by the catalog.

**Mathematical proof evidence:** Erdős1213 page matches the catalog. Hegyvári, *On consecutive sums in sequences*, Acta Math. Hungar. 48 (1986), 193–200, DOI `10.1007/BF01949064`, is the primary historical solution. PR4661's fixed SOURCES record locates the original question/Theorem 3 at printed p.197, complete proof pp.197–198 (archive PDF pages 203–204). The 138MB archive retrieval timed out after 555024 bytes; saved as `hegyvari-volume-INCOMPLETE.part`, explicitly not a full article. Publisher returned HTML, not a PDF. Thus **historical proof text was not independently obtained/read in this sidecar**. This retrieval limitation is not a Lean vacancy.

A complete author-published finite counting exposition was obtained at `sweetsky123/erdos-problem-1213`, commit `d787b3cb7010713201aa32b0873f3461278904b5`, README Theorem 1 and six lemmas, saved as `hegyvari-writeup.md`. It supplies F=4^K*a+2K*16^K without relying on the inaccessible historical article. Sliding windows of length r change by ≤Kr; each legal length/bin slot obtains an actual window. More than W=K*(4^K)^2 slots lie in W integer values, and bins of any fixed length are disjoint. Hence equal-value distinct slots give different actual intervals. The displayed Lemma 3 proof omits writing the final addition of W, but its preceding bound X≤Ma+KM² directly yields X+W≤Ma+2KM²; no missing mathematical lemma is needed.

**Complete earlier endpoint:** `plby/lean-proofs` at the same `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, `src/latest/ErdosProblems/Erdos1213.lean:495`, `Erdos1213.erdos_1213`. Full natural-valued finite-prefix theorem with positive initial value, strict increase, bounded gaps, uniform threshold, actual `Finset.Ico` sums, both nonempty intervals inside the prefix and unequal endpoint pairs. The explicit threshold is proved, not supplied as a premise. The file was read through its window-crossing, slot cardinality, injectivity and pigeonhole assembly. Naturals cover the positive original integer prefix; signed bridges already exist separately. Mathematics credited to Hegyvári; formalization to Codex/GPT-5.6 Sol.

**Strongest inspected scope extension:** PR1205, awards head `2064e09ae7b85af31e73e970c61c52ab73634d28`; `KunHcz/jsp-nonpinnacle-proofs` at `9b51e774eafde79c53a67f77224f857d2d55d31d`, package `submissions/jsp-001018-multiplicity`. All six local modules were fetched/read for endpoint/dependency correspondence, without compiling. `JSP1018/Integer.lean:98`, `JSP1018.jsp_001018` has the literal signed type:

```
∀ (a K : ℤ), 1≤a → 1≤K → ∃ F : ℤ,
  ∀ s (B : ℕ → ℤ), 0<s → B 0=a → StrictMonoOn B (Set.Iio s) →
  (∀ i, i+1<s → B (i+1)-B i≤K) → F<B (s-1) →
  ∃ u v x y, u<v ∧ v≤s ∧ x<y ∧ y≤s ∧ (u,v)≠(x,y) ∧
    (∑ i∈Ico u v, B i)=(∑ i∈Ico x y, B i).
```

`JSP1018.uniform_multiplicity` additionally handles every requested positive q with ≥q distinct equal-sum intervals of pairwise different lengths. The crucial finite criterion `sum_{r=1}^L floor(W/(Kr)) > (q−1)W`, endpoint-map injectivity, actual slot windows, and multiplicity pigeonhole are proved. Uniform harmonic cutoff and Nat/Int value/sum/gap transport are also proved. No custom axioms or placeholders were found in these six files. Elementary window lemmas are explicitly attributed to the prior Erdos1213 source. Contributor records report six clean modules and 36 standard-axiom closures; no independent rerun claimed.

PR1622 also supplies a smaller explicit two-interval threshold `a*4^K + K*(4^K)^2 + K*4^K + K`, at `firesh/erdos1213-lean`, commit `0cf7d32f6a7cf4e71f6884fce02cc5f098c1138d`, `Erdos1213/Main.lean`, `exists_equal_blocks`/`erdos_1213`. “Strongest” therefore depends on quantitative bound versus multiplicity; neither leaves the original question missing. PR3015 mistakenly cites Erdős1018/Erdos1018.lean and is not usable scope evidence.

## Action

Keep both out of the new full-problem implementation queue. A new finite certificate, signed wrapper, harmonic proof or multiplicity extension would repeat inspected public work. Improving the K-dependence or proving optimal wave constants would ask for new mathematics beyond the assigned full-problem route; no such route established here. No census files or strategy files were changed, and no global absence/priority/award verdict is asserted.
