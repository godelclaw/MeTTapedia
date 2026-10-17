/-
Writes `tests/petta/emitted/ambient.metta`, upstream MeTTaIL's ambient calculus as one emitted
complete module, and prints `tests/petta/gslt_ambient_controls.metta`: for each of upstream's 29
test inputs, the states that `ambient:explore` reaches in `work` rounds, as the Lean model
predicts them. Run from `lean/mettapedia`:
`lake env lean ../../metta/gslt/tools/generate_ambient_controls.lean`.
-/
import Mettapedia.OSLF.MeTTaIL.Upstream.AmbientTests
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.OSLF.MeTTaIL.Complete.Settled

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL CompleteEmission
open Mettapedia.OSLF.MeTTaIL.Upstream

def render (term : Term) : String := Term.render term

/-- The module: the conformance language over every test's free names, root steps modulo its
equations, states of sort `Proc`. -/
def spec : Spec :=
  ⟨GeneralExecutionAdmission.compile ⟨AmbientTests.conformanceLanguage, AmbientTests.free,
      { signatures := [], rows := [] }⟩
    { sites := .rootOnly, includeDerivedEquations := false }, [], .base "Proc"⟩

def work : Nat := 400

/-- The states of `work` rounds, computed by stopping once settled
(`Complete.Settled.roundsUntilSettled_states`). -/
def predicted (source : Pattern) : List Pattern :=
  let search := Complete.Normalized.search spec.plan spec.bound spec.expected
  (Complete.Settled.roundsUntilSettled search work
    (Complete.Explore.begin search (Complete.Normalized.standard spec.plan source))).nodes.map (·.state)

def ambientControl (row : String × List (String × TypeExpr) × Pattern) : String :=
  "!(let $s (ambient:explore " ++ render (encodePattern row.2.2) ++ " " ++ toString work ++ ")\n" ++
  "  (println! (AmbientControl " ++ reprStr row.1 ++ " (== $s (quote " ++
    render (CettaWire.encodeList encodePattern (predicted row.2.2)) ++ ")))))"

def main : IO Unit := do
  match emitText? spec "ambient" with
  | .ok text => IO.FS.writeFile "../../metta/gslt/tests/petta/emitted/ambient.metta" text
  | .error _ => throw (IO.userError "the ambient module is refused")
  IO.println "; Upstream MeTTaIL's ambient-calculus tests, run through the emitted module. Every"
  IO.println "; expected state list is the Lean model's (`Complete.Explore` over `Complete.Normalized`)."
  for row in AmbientTests.tests do
    IO.println (ambientControl row)

#eval main
