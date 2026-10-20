import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Probes
import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# Bridge to the executable HE evaluator

The core calculus under `reevaluate` is meant to be the existing executable HE
evaluator `HE.eval` restricted to its fragment. `Program.toSpace` writes a
program as an HE space: one `(= lhs rhs)` atom per equation, in order, and
one `(: head (-> T₁ … Tₙ R))` per declaration, with `Atom` for the `atom`
mode and `%Undefined%` for the others.

On every equation-only probe — the alias chain, `twice` and `twicem` on
`coin` and on `(fr a)`, `pairit`, `quote`/`unquote`, the `Atom`-result macro
`ga` used through the equation `(= (usem $m) (pair $m))`, and the stuck call
`(fr (h))` whose argument reduces, alone and under aliases — the observation
of the core under `reevaluate` is exactly the list of atoms `HE.eval`
returns, in the same order (`bridge_*`). The primitives `collapse`,
`superpose`, `unique`, `let` and `car-atom` belong to HE's standard library,
which `HE.eval` does not load (`heAnswers_car_atom_stuck`), so those probes
have no counterpart here.

A general simulation theorem between `HE.eval` and the core on the whole
fragment is not proved here. Its obligations: `HE.eval` threads binding sets
through every argument and returns them with each result, and renames
equation variables apart from the live call scope before unifying, where the
core matches one way without renaming; its typed path (`getAtomTypes`,
`checkIfFunctionTypeIsApplicable`, `typeCast`) must be shown to reduce to the
parameter and result modes on declared and undeclared heads; and its fuel is
consumed per mutual function and exhaustion yields fewer results rather than
an explicit failure, so the statement needs a stabilization lemma for
`HE.eval` in its fuel.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- The HE type of a parameter mode. -/
def ParamMode.toType : ParamMode → Atom
  | .value => Atom.undefinedType
  | .atom => Atom.atomType

/-- The HE type of a result mode. -/
def ResultMode.toType : ResultMode → Atom
  | .evaluate => Atom.undefinedType
  | .atom => Atom.atomType

/-- The type declaration `(: head (-> T₁ … Tₙ R))`. -/
def Decl.toAtom (d : Decl) : Atom :=
  .expression [.symbol ":", .symbol d.head,
    .expression (.symbol "->" :: d.params.map ParamMode.toType ++ [d.result.toType])]

/-- A program as an HE space: equations in order, then declarations. -/
def Program.toSpace (P : Program) : Mettapedia.Languages.MeTTa.HE.Space :=
  Mettapedia.Languages.MeTTa.HE.Space.ofList
    (P.equations.map (fun eq => .expression [.symbol "=", eq.1, eq.2]) ++ P.decls.map Decl.toAtom)

/-- The executable HE evaluator's answers, without their bindings. -/
def heAnswers (P : Program) (a : Atom) (fuel : ℕ) : List Atom :=
  (Mettapedia.Languages.MeTTa.HE.eval P.toSpace a fuel).map Prod.fst

open Probe

theorem bridge_fr : observe .reevaluate program fra = some (heAnswers program fra 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_wrap :
    observe .reevaluate program (E [S "wrap", fra]) =
      some (heAnswers program (E [S "wrap", fra]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_alias :
    observe .reevaluate program (E [S "g", fra]) = some (heAnswers program (E [S "g", fra]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_alias2 :
    observe .reevaluate program (E [S "g1", fra]) =
      some (heAnswers program (E [S "g1", fra]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_twice_coin :
    observe .reevaluate program (E [S "twice", E [S "coin"]]) =
      some (heAnswers program (E [S "twice", E [S "coin"]]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_twicem_coin :
    observe .reevaluate program (E [S "twicem", E [S "coin"]]) =
      some (heAnswers program (E [S "twicem", E [S "coin"]]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_twice_fr :
    observe .reevaluate program (E [S "twice", fra]) =
      some (heAnswers program (E [S "twice", fra]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_pairit :
    observe .reevaluate program (E [S "pairit", fra]) =
      some (heAnswers program (E [S "pairit", fra]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_unquote :
    observe .reevaluate program (E [S "unquote", E [S "quote", fra]]) =
      some (heAnswers program (E [S "unquote", E [S "quote", fra]]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_ga :
    observe .reevaluate program (E [S "ga", fra]) = some (heAnswers program (E [S "ga", fra]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_usem_ga :
    observe .reevaluate program (E [S "usem", E [S "ga", fra]]) =
      some (heAnswers program (E [S "usem", E [S "ga", fra]]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_fr_h :
    observe .reevaluate program frh = some (heAnswers program frh 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_wrap_fr_h :
    observe .reevaluate program (E [S "wrap", frh]) =
      some (heAnswers program (E [S "wrap", frh]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_alias_fr_h :
    observe .reevaluate program (E [S "g", frh]) = some (heAnswers program (E [S "g", frh]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

theorem bridge_alias2_fr_h :
    observe .reevaluate program (E [S "g1", frh]) =
      some (heAnswers program (E [S "g1", frh]) 24) :=
  observe_of_evalFuel (n := 24) (by decide +kernel)

/-- Without the standard library, `HE.eval` leaves `car-atom` as a stuck
call. -/
theorem heAnswers_car_atom_stuck :
    heAnswers program (E [S "car-atom", E [fra, S "b"]]) 24 =
      List.replicate 2 (E [S "car-atom", E [fra, S "b"]]) := by
  decide +kernel

/-- The HE evaluator's answer counts on the alias chain are the old rule's:
2, 4, 8, where the repaired rule gives 2, 2, 2. -/
theorem heAnswers_alias_counts :
    (heAnswers program fra 24).length = 2 ∧
      (heAnswers program (E [S "g", fra]) 24).length = 4 ∧
      (heAnswers program (E [S "g1", fra]) 24).length = 8 := by
  decide +kernel

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues
