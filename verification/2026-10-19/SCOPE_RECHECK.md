# Scope clarification — 19 October 2026

The 30 draft records remain open. Draft status was an applicant-side review decision, not a rejection by the prize committee. Their proofs were retained and all source modules passed checking. Most deficiencies concern coverage, not an invalid proof of the stated theorem.

## Correction to the classification of PR5080 / JSP-000307

The catalog at fd8fa66abb4e21df828fdebc25298e9ad75521bd literally asks whether three consecutive integers can have strictly decreasing largest prime factors. The checked theorem `Erdos372.jsp_000307_least_decreasing_triple` proves that the least example begins at13, so it completely answers that finite-existence question. The cited original research problem and FC statement require infinitely many such triples, which this file does not prove.

Accordingly, this record is **scope unresolved**, rather than conclusively incomplete for every interpretation of the catalog. It should be reconsidered alongside #124 and #939. The current triage is two clearly complete scoped records, 27 records with identified broader-scope gaps, and three scope-clarification candidates. This is triage, not a committee decision.

The quantitative Balog lower bound is a stronger known result, not an automatic obligation for the infinitude question. Similarly, not every theorem or variant in a FormalConjectures file or problem webpage must be proved: obligations come from the precise selected prize problem. Once a universal conjecture is refuted by a valid counterexample satisfying its hypotheses, that universal question is complete; unrelated variants cannot be added as new acceptance conditions.

## Repair types

- Incorrect names, copied signatures, bibliography and build configuration are ordinary repairable submission defects; the previously identified active errors were corrected and109 target checks passed.
- A complete subquestion with an ambiguous catalog mapping needs a scope decision, not an invented stronger proof obligation.
- A special case of an arbitrary-parameter question needs a general proof or a valid counterexample to the actual question. An extra theorem premise containing the hard result must be discharged; it cannot be removed by editing prose.
- Completing known mathematics may be feasible but needs a concrete dependency plan. Filling a still-open mathematical case is new research and cannot be promised as a quick repair.

Sources: official catalog-0301-0400.md JSP-000307; `JspBounties/Erdos372.lean` lines143–151; FC ErdosProblems/372.lean lines33–41; retained PR target-check log. Competitor priority is a separate question and was not the reason for converting these30 records to drafts.
