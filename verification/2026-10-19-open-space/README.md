# Remaining problem space: catalogue census

Checked **2026-10-19 21:22 China time**. The live official main remained
`fd8fa66abb4e21df828fdebc25298e9ad75521bd` (committed 2026-10-14).
The census reads all 11 catalogue volumes and the index at that exact commit,
checks that all 1,072 identifiers are unique and consecutive, and checks the
index/detail mathematical statuses agree.

## Counts and their meaning

- **677 Open**: the official catalogue has not recorded a complete solution of
  the stated scope. This does not establish that every problem is still
  mathematically open worldwide or that nobody has submitted a proof.
- **395 Solved**: a complete resolution is recorded or claimed in the catalogue.
  Of these, 41 explicitly retain independent-mathematical-review-pending wording.
- **100 Solved + Lean Yes**: the catalogue records formalization evidence.
  This census does not independently certify those proofs.
- **295 Solved + no recorded complete Lean**: the discovery pool, using the
  index's normalized Lean field. This is not a count of verified prize vacancies.
- **37** pool records already have substantive review records of varying depth;
  **258** do not. Reading a publisher's scope flag is not counted as a proof audit.
- **0** new implementation candidates in this pool have passed our full scope,
  proof, competition and award-route checks. The true number that could pass
  remains unknown; zero approved is not proof of zero opportunities.

## Correction to the previous pool

The previous detail-field filter `Lean proof.startswith("No")` found 294 rows
but missed **JSP-000448**, whose detail field begins **Reported; standalone Lean
source not located**. The official index normalizes it to **No — reported;
standalone source not located**. It belongs in the same discovery pool.

The corrected count is **295**, and the not-substantively-reviewed remainder is
**258**, not 257. This is a metadata correction, not a newly proved problem or
an established easy gap. Four PR titles already mention JSP-000448: 574, 3748,
4224 and 4546; their validity is not assessed here.

## Competition coverage

The complete earlier index of 4,509 PRs was refreshed with the 100 most recently
updated PRs. That page reaches back to 2026-10-14, overlapping the baseline;
the resulting 4,510 unique PR numbers equal the live GraphQL total. This includes
Open, Closed and Merged states. The added PR is 5111.

- Among 677 Open catalogue problems, **670** have a JSP-ID title match and **7**
  do not. Of those 677, 425 have an Open PR title match.
- Among 295 Solved/no-complete-Lean pool problems, **294** have a title match and
  **1** does not; 293 have an Open PR title match.
- The sole pool entry without a title match is JSP-001059, Hilbert's sixteenth
  problem. Its published broader mathematical claim is marked review pending,
  and the linked limited Lean target does not cover the full statement. Lack of
  a title hit is no reason to treat it as a straightforward implementation.

Matching uses only JSP IDs in titles. A title hit can be a partial result,
incorrect proof, registration, or correction. No hit can miss title variants,
body-only mentions and external code. Neither result establishes priority or
the presence/absence of a valid same-scope proof.

## What this means for the prize objective

There is still a substantial **unassessed pool**, but its viable size is unknown.
Prioritize the 258 not-yet-substantively-reviewed solved/formalization records,
plus explicit source gaps from previous reviews. For Open records, seek a
recent complete proof missed by the catalogue or a concrete tractable proof
route before investing in implementation. Do not infer ease from status or
absence of a PR title.

The shared legacy `Eligible to claim: No` field means the current prerequisites
are not yet satisfied; it is not a permanent ban on a new complete formalization.
Conversely, the raw pool count is not a promise of eligibility, priority or money.
No proof source, award PR, or Ready/Draft state was changed in this census.

## Evidence and reproduction

Raw evidence and complete lists: `reports/open-space-2026-10-19/`:
`COUNTS.json`, `CATALOG.json`, `CATALOG.csv`, `OPEN.json`,
`LEAN_CANDIDATES.json`, `PR_METADATA.json`, the exact official index and process,
live main response, PR update page and live PR total.

Primary sources at the pinned commit:

- `TheJustinSunPrize/awards:problems/README.md` (definitions and complete index).
- `TheJustinSunPrize/awards:problems/catalog-0401-0500.md` (JSP-000448).
- `TheJustinSunPrize/awards:docs/award-process.md` (eligibility and independent
  mathematical/formalization review).

```sh
python3 scripts/census_open_space.py \
  --head reports/open-space-2026-10-19/official-head.json \
  --delta reports/open-space-2026-10-19/pr-delta.json \
  --total reports/open-space-2026-10-19/pr-live-total.json \
  --output reports/open-space-2026-10-19
```

The timestamp updates on reproduction. The output is a fixed-commit census,
not a new global proof search.
