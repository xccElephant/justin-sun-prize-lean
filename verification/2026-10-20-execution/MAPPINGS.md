# Source-verified mapping corrections

These nine pairs were checked against the actual catalogue descriptions at
`fd8fa66abb4e21df828fdebc25298e9ad75521bd` and the original problem text or
matching source theorem. They are not inferred from a numeric offset.

- JSP211 → E240: an **infinite prime set** with diverging gaps between all its
  positive smooth integers. `Erdos240.lean` definitions 36–58 and final
  `erdos_240`; E238 instead concerns long runs of prime gaps.
- JSP281 → E339: positive lower density of distinct-summand sums of an additive
  basis. `Erdos339.lean`, `restrictedSums` and final `erdos_339`; PR681 also
  explicitly identifies E339. E338 is a different restricted-basis question.
- JSP585 → E717: chromatic number versus largest complete-graph subdivision,
  with the FLS13 source. `Erdos717.lean:573`; E716 is the (6,3) hypergraph theorem.
- JSP782 → E941: all sufficiently large integers are sums of at most three
  positive **2-powerful** numbers. Original E941 page fetched; `Erdos941.lean:32`.
  E940 instead asks density-zero questions for r-powerful numbers.
- JSP854 → E1027: many subsets meeting every hyperedge without containing one.
  FC `1027.lean:63`, `Erdos1027.lean:209`; E1026 concerns monotone subsequences.
- JSP857 → E1031: an induced nontrivial regular graph in a graph with no
  homogeneous set of order at least `10 log n`. Original E1031 page fetched;
  `Erdos1031.lean:1776`. E1034 is a different triangle-neighborhood question.
- JSP1010 → E1205: maximize minimum covering multiplicity by choosing one residue
  for every modulus up to x. PR919 and `Erdos1205.lean`, `coveringNumber`, final
  asymptotic `erdos_1205` identify the same problem.
- JSP1018 → E1213: bounded-gap sequences have distinct equal-sum consecutive
  blocks. Original E1213 page, Hegyvári reference and fixed author proof read by
  the combinatorics sidecar; exact `erdos_1213` at line495.
- JSP1019 → E1214: equality of all prime supports of x^n−1 and y^n−1 implies x=y.
  FC `1214.lean` and `Erdos1214.lean:948` have the same quantified statement.

plby source throughout is `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`;
the local FC source is `e754a78c74a3f2bbc38e4f2063b5f6eed51bde39`.
The larger legacy mapping remains a discovery aid, not an audited bijection.

An additional consistency pass repaired ten stale entries already established
by the independent submission/repair audit in
`verification/2026-10-19-repairs/REPAIR_QUEUE.md`: JSP500→617,403→503,247→291,
780→939,58→23,280→338,569→699,395→488,210→238,579→711. The corresponding ten
subtests all failed before the repair. These updates synchronize previously
known meanings; they are not ten new candidate proof reviews.

Validation: the nine subtests failed against the old mapping (six wrong values,
three missing values), and the ten repair-queue pairs also failed. After the
corrections, the complete five-test mapping/loader/selector suite passed.
No Lean proof or award record was changed.
