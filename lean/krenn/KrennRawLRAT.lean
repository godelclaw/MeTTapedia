import Mathlib.Tactic.Sat.FromLRAT

/-!
Expose an LRAT refutation at Mathlib's small `Sat.Fmla.proof` boundary.

Unlike `lrat_proof`, this command deliberately does not expand the result into
a large propositional disjunction.  A consumer supplies a valuation satisfying
the concrete CNF and obtains the empty-clause contradiction directly.
-/

open Lean Elab Term

namespace Krenn.RawLRAT

elab "raw_lrat_proof " n:ident ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    let (_, formula, _, proof) ← Mathlib.Tactic.Sat.fromLRATAux cnf lrat name
    let emptyClause := Lean.mkConst ``Sat.Clause.nil
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) formula emptyClause
      value := proof
    }
    addTermInfo' n (← mkConstWithLevelParams name) (isBinder := true) |>.run'

/-- As above, while also requiring the parsed CNF to be definitionally equal
to a caller-supplied structured formula.  This is the binding gate between an
external DIMACS file and the semantic Lean data consumed downstream. -/
elab "raw_lrat_proof_for " n:ident ppSpace expected:term:max ppSpace
    cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let expected ← elabTermEnsuringType expected (Lean.mkConst ``Sat.Fmla)
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (Lean.mkConst ``String) lrat
    let (_, formula, _, proof) ← Mathlib.Tactic.Sat.fromLRATAux cnf lrat name
    unless ← Lean.Meta.isDefEq expected formula do
      throwError "structured formula does not match the LRAT CNF"
    let emptyClause := Lean.mkConst ``Sat.Clause.nil
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) expected emptyClause
      value := proof
    }
    addTermInfo' n (← mkConstWithLevelParams name) (isBinder := true) |>.run'

end Krenn.RawLRAT
