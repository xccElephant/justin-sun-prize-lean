# Complete-proof opportunity screening — 19 October 2026

> Historical first-round report. The cumulative ledger was subsequently updated by
> [round2](../2026-10-19-discovery-round2/README.md): the corrected pool has294 entries,
> with31 documented checks and263 without substantive review. The original291 pool
> count below used an exact-field filter and missed3 entries labelled `No — ...`.

The first execution of the revised strategy found **no new candidate approved for
implementation**. No new award PR was opened, and the existing 32 PR heads and
draft states were read back unchanged: four ready and 28 drafts. This is a bounded
discovery result, not a claim that all opportunities have been exhausted.

## What was actually checked

The official main was freshly read as
`fd8fa66abb4e21df828fdebc25298e9ad75521bd`. Its 1,072 catalogue entries contain
291 entries marked Solved with a literal Lean proof value of No. These are raw
metadata candidates only.

All **4,509 official pull requests**, across open/closed/merged states, were
enumerated in 46 GraphQL pages. PR numbers were checked for uniqueness and the
final page reported no next page. Every one of the 291 pool records had at least
one JSP-number match in a PR title (between three and 63 matches). A title match
does not establish correct mapping, full scope, valid proof, authorship, priority
or acceptance. Closed does not imply invalid, and open does not imply complete.

Fourteen pool records have a documented source, mathematical, or claim-level
review in this pass; **277 remain unreviewed beyond metadata**. The reviewed
records have different evidence levels, expressly recorded in
[CANDIDATE_LEDGER.json](CANDIDATE_LEDGER.json). The ledger retains all 291 records;
unreviewed entries are not silently excluded. Three additional Open catalogue
entries (E65/E80/E883) were checked only to prevent a solved subproblem from being
substituted for a whole catalogue record.

[Machine-readable result](RESULT.json) records the counts and disposition.
The complete raw sources and API pages remain local under
`reports/discovery-2026-10-19/`; third-party proof code and papers are not
republished as this account's work.

## Decisions supported by concrete evidence

- **JSP000264 / E318:** The ordinary plby entry lacks the squares-greater-than-one
  component, but a different public source in closed PR105 supplies exactly that
  endpoint. `Erdos318.erdos_318.parts.ii` and
  `ReciprocalSquares.square_partition` were read at fixed commit
  `8c4f1b2b4b9d1e7fb872340b7ae88dde5e862097`. The signed-definition bridge and the
  top-level construction contain proof bodies, not an assumed conclusion. The
  complete imported proof closure was not independently rebuilt. Larsen's
  mathematical Theorem 6 uses the substantial weighted Egyptian-fraction/circle
  method Theorem 4. This is neither an established vacant Lean opportunity nor a
  low-cost elementary implementation.
- **JSP000925 / E1114:** Original Bálint 1960 pp.33–40 acquired. The polynomial
  has degree N+1 and N+1 equally spaced roots; the problem website's degree-n
  wording is an indexing error. A fixed plby `erdos_1114` endpoint covers
  arbitrary start, positive spacing, actual roots/degree, derivative-root listing,
  nondecreasing outward gaps and reflection symmetry. Its core analytic and
  polynomial steps have proof bodies. Strict strengthenings and Lorch's wider
  generalizations were not claimed. This is concrete same-scope competition. The coordinator independently compiled the unchanged 1,620-line fixed source with Lean4.33.1 and pinned Mathlib, exit0; the main target printed only `propext`, `Classical.choice`, `Quot.sound`. See [compile record](E1114-independent-compile.json) and [output](E1114-independent-compile.log). The source header names Lean4.33.0; no separate kernel replay or from-scratch dependency build was run.
- **JSP000907 / E1091:** The short 2026 negative construction is real, but plby's
  fixed source includes both that family and the original affirmative question.
  Actual endpoints and a closed 38-module import tree were inspected; no
  independent build of that tree. Issue1019 is public evidence of a later
  claimant withdrawing because of the broader prior proof, not an official
  priority judgment.
- **JSP000183 / E193:** The author already supplies a fixed Lean endpoint for the
  infinite three-dimensional walk with finite step set and no collinear triple.
  The proof paper and actual endpoint were read; no new implementation warranted.
- **JSP000393 / E485:** The fixed final limit theorem and actual Schinzel
  reduction were inspected. Its 22-module source tree is substantial; a short
  polynomial identity would not supply the full result.
- **JSP000399 / E494:** A simple finite counterexample is not the general
  eventual-uniqueness theorem. The original GFS1962 proof invokes Ridout's
  theorem; no complete elementary replacement or verified reusable dependency
  was found in this pass. Held for dependency/competition review, not declared
  impossible or globally unformalized.
- **JSP000385/E473, JSP000598/E730, JSP000288/E346 and JSP000673/E816:** Concrete
  existing exact endpoints or fixed formal-proof records were located; details
  and the distinction between read source and linked source are in the ledger.
- **JSP000334/E407:** The actual fixed `erdos_407` proves a uniform bound on
  ordered exponent quadruples, supplying its specialised Subspace-Theorem input.
  PR1677 identifies the correct E407 mapping. PR2731 maps the same JSP to E334,
  which is unrelated; that bad record does not invalidate the correct source.
- **JSP000643/E783:** A fixed assembly theorem supplies the asymptotic resolution
  from named lower-bound and achievability proofs. Only this assembly was
  inspected; it is not a full dependency audit or a verified award decision.
- **JSP000404/E504:** A public scoped-component submission reports a suspected
  gap in the published general lower bound. That claim has not been independently
  verified here. This record remains scope/mathematics unresolved and is not
  approved for implementation.
- **JSP000838/E1006:** Initial mapping was unclear; a later local source read
  found an actual finite orientation counterexample endpoint. It is retained as
  a limited source-level lead, without independent build or priority certification.

## Primary references

- [Official catalogue and submission rules](https://github.com/TheJustinSunPrize/awards/tree/fd8fa66abb4e21df828fdebc25298e9ad75521bd).
- [E318 PR105](https://github.com/TheJustinSunPrize/awards/pull/105),
  [fixed square endpoint](https://github.com/CollinYuanjieRen/awards/blob/8c4f1b2b4b9d1e7fb872340b7ae88dde5e862097/submissions/jsp-000264-cyr/MerLeanExperiment/Erdos318Solution.lean),
  [Larsen's mathematical paper](https://github.com/Larsen-Daniel/Erdos-318/blob/main/318.pdf).
- [E1114 fixed source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1114.lean),
  [Bálint original volume](https://real-j.mtak.hu/9390/1/MTA_MatematikaiLapok_1960.pdf).
- [E1091 fixed source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1091.lean),
  [APSSV manuscript](https://arxiv.org/html/2604.06609v1),
  [public correction record](https://github.com/TheJustinSunPrize/awards/issues/1019).
- [E193 mathematical paper](https://arxiv.org/html/2609.01766v1),
  [author's fixed endpoint](https://github.com/ekalvi/erdos-193/blob/fca4e1bd2b423c000a6bef18cf2f3bc0f4bd363e/formal/Hilbert193/Hilbert193/Continuity.lean).
- [GFS1962 original paper](https://msp.org/pjm/1962/12-1/pjm-v12-n1-p17-s.pdf).

## What follows

Continue the same strategy, using the ledger to avoid repeated discovery. Search
the remaining records for a **specific missing full endpoint**, verify the whole
mathematical argument and any reusable dependency/license, then compare all
known same-scope sources. A PR title, unmerged proof, old catalogue flag, failed
search or absent local filename is not enough to enter implementation.

At most one implementation starts after those conditions pass. No code is copied
and submitted as this account's contribution, no original question is narrowed
to make a submission, and no award amount or payout probability is fabricated.
The next discovery pass may still yield no qualifying candidate; it must report
that rather than weaken the requirements. The user's prize-maximization
objective remains ongoing and no reward has been established by this screening.
