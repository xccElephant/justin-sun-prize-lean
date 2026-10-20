import Mathlib.Tactic.Sat.FromLRAT

/- Certificate by Cecil Jentges, fixed source b5738d8944340f0ac9434f70f689316b18497026.
   This replays the CNF only; no graph-to-CNF correctness theorem is asserted. -/
lrat_proof n12_replayed
  (include_str "n12_b0_l2.cnf")
  (include_str "n12_b0_l2.lrat")

#print axioms n12_replayed
