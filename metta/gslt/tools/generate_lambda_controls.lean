/-
Writes `tests/petta/emitted/upstream_lambda.metta`, upstream MeTTaIL's lambda calculus as one
emitted complete module, and prints `tests/petta/gslt_upstream_lambda_controls.metta`: for each
test input, the states that `ulambda:explore` reaches in `work` rounds, as the Lean model predicts
them. Also writes `out/lambda-inputs.txt` (the inputs in upstream's syntax) and
`out/lambda-predicted.txt` (the predicted states with binders as indices), for comparison with
upstream's own runs. Run from `lean/mettapedia`:
`lake env lean ../../metta/gslt/tools/generate_lambda_controls.lean`.
-/
import Mettapedia.OSLF.MeTTaIL.Upstream.Lambda
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.OSLF.MeTTaIL.Complete.Settled

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL CompleteEmission
open Mettapedia.OSLF.MeTTaIL.Upstream

def render (term : Term) : String := Term.render term

/-- The module: upstream's lambda calculus over every test's free names, root steps (its
congruences are authored), states of sort `Term`. -/
def spec : Spec :=
  ⟨GeneralExecutionAdmission.compile ⟨Lambda.reduced, Lambda.free, { signatures := [], rows := [] }⟩
    { sites := .rootOnly, includeDerivedEquations := false }, [], .base "Term"⟩

def work : Nat := 5000

/-- The states of `work` rounds, computed by stopping once settled
(`Complete.Settled.roundsUntilSettled_states`). -/
def predicted (source : Pattern) : List Pattern :=
  let search := Complete.Normalized.search spec.plan spec.bound spec.expected
  (Complete.Settled.roundsUntilSettled search work
    (Complete.Explore.begin search (Complete.Normalized.standard spec.plan source))).nodes.map (·.state)

/-- Whether exploration settles within `work` rounds. -/
def settles (source : Pattern) : Bool :=
  let search := Complete.Normalized.search spec.plan spec.bound spec.expected
  Complete.Settled.settled search (Complete.Settled.roundsUntilSettled search work
    (Complete.Explore.begin search (Complete.Normalized.standard spec.plan source)))

/-- A state with binders as indices: `(lam body)`, `(app f a)`, `#i`, free names. -/
def indexed : Pattern → String
  | .bvar index => s!"#{index}"
  | .fvar name => name
  | .apply "Lam" [.lambda _ body] => s!"(lam {indexed body})"
  | .apply "App" [function, argument] => s!"(app {indexed function} {indexed argument})"
  | other => s!"?{reprStr other}"

def lambdaControl (row : String × List (String × TypeExpr) × Pattern) : String :=
  "!(let $s (ulambda:explore " ++ render (encodePattern row.2.2) ++ " " ++ toString work ++ ")\n" ++
  "  (println! (LambdaControl " ++ reprStr row.1 ++ " (== $s (quote " ++
    render (CettaWire.encodeList encodePattern (predicted row.2.2)) ++ ")))))"

def main : IO Unit := do
  match emitText? spec "ulambda" with
  | .ok text => IO.FS.writeFile "../../metta/gslt/tests/petta/emitted/upstream_lambda.metta" text
  | .error _ => throw (IO.userError "the lambda module is refused")
  IO.FS.writeFile "../../metta/gslt/tools/out/lambda-inputs.txt"
    ("\n".intercalate (Lambda.sources.map (·.2.render)) ++ "\n")
  IO.FS.writeFile "../../metta/gslt/tools/out/lambda-predicted.txt"
    ("\n".intercalate (Lambda.tests.map fun row =>
      "TEST " ++ row.1 ++ (if settles row.2.2 then "" else " UNSETTLED") ++ "\n" ++
        "\n".intercalate ((predicted row.2.2).map indexed |>.mergeSort)) ++ "\n")
  IO.println "; Upstream MeTTaIL's lambda calculus, run through the emitted module. Every expected"
  IO.println "; state list is the Lean model's (`Complete.Explore` over `Complete.Normalized`)."
  for row in Lambda.tests do
    IO.println (lambdaControl row)

#eval main
