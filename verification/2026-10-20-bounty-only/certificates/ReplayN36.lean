import Mathlib.Tactic.Sat.FromLRAT

/- Jentges certificate; propositional replay only, not a graph theorem. -/
lrat_proof n36_replayed
  (include_str "n36_b3_l6.cnf")
  (include_str "n36_b3_l6.lrat")

#print axioms n36_replayed
