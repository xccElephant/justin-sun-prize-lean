import Mathlib.Tactic.Sat.FromLRAT

/-!
# Kernel proof interface to archived DIMACS/LRAT certificates

These elaborators use Mathlib's existing parser and proof reconstruction.
`dimacs_formula` exposes the exact parsed formula; `lrat_refutation` exposes its
semantic empty-clause proof without the large propositional reification.
Neither elaborator adds an axiom or executes a native decision procedure.
-/

open Lean Elab Term

elab "dimacs_formula " cnf:term:max : term => do
  let cnf ← unsafe evalTerm String (mkConst ``String) cnf
  let .success _ (_, arr) :=
      Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  return Mathlib.Tactic.Sat.buildConj arr 0 arr.size

elab "lrat_refutation " cnf:term:max ppSpace lrat:term:max : term => do
  let cnf ← unsafe evalTerm String (mkConst ``String) cnf
  let lrat ← unsafe evalTerm String (mkConst ``String) lrat
  let name ← mkAuxName `lratRefutation
  let (_, _, _, proof) ← Mathlib.Tactic.Sat.fromLRATAux cnf lrat name
  return proof
