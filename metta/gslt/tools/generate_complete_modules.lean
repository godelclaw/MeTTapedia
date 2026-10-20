/-
Writes `tests/petta/emitted/complete_*.metta` with `CompleteEmission.emitText?` and prints
`tests/petta/gslt_complete_module_controls.metta`. Every expected readout is the Lean complete
machine's (`OSLF/MeTTaIL/Complete`).
Run from `lean/mettapedia`: `lake env lean ../../metta/gslt/tools/generate_complete_modules.lean`.
-/
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire (planTerm)
open Mettapedia.Machines.ResumableSearchRunner (Machine Phase)

def render (term : Term) : String := Term.render term
def pat (p : Pattern) : String := render (encodePattern p)

def search (spec : Spec) := Complete.Normalized.search spec.plan spec.bound spec.expected

def phaseTerm : Phase → Term
  | .running => .symbol "ClassRunning"
  | .done => .symbol "ClassDone"
  | .blocked => .symbol "ClassBlocked"

def traceText (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  let machine := Machine.advance (search spec) ticks quantum
    (Machine.begin (search spec) (Complete.Normalized.standard spec.plan source))
  render (.application "RunTrace" [phaseTerm machine.phase, CettaWire.encodeList encodePattern machine.states.reverse])

def statesText (spec : Spec) (source : Pattern) (work : Nat) : String :=
  render (CettaWire.encodeList encodePattern ((Complete.Explore.explore (search spec)
    (Complete.Normalized.standard spec.plan source) work).nodes.map (·.state)))

def runControl (label name : String) (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let $t (" ++ name ++ ":run " ++ pat source ++ " " ++ toString ticks ++ " " ++ toString quantum ++ ")\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $t (quote " ++ traceText spec source ticks quantum ++ ")))))"

def beginControl (label name : String) (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let* (($m (" ++ name ++ ":begin " ++ pat source ++ "))\n" ++
  "        ($a (gslt:runner:advance " ++ render (planTerm spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected) ++
    " " ++ render (StandardWire.standardTerm spec.plan) ++ " " ++ toString ticks ++ " " ++ toString quantum ++ " $m))\n" ++
  "        ($t (gslt:runner:trace $a)))\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $t (quote " ++ traceText spec source ticks quantum ++ ")))))"

def exploreControl (label name : String) (spec : Spec) (source : Pattern) (work : Nat) : String :=
  "!(let $s (" ++ name ++ ":explore " ++ pat source ++ " " ++ toString work ++ ")\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $s (quote " ++ statesText spec source work ++ ")))))"

def emitTo (spec : Spec) (name : String) (path : String) : IO Unit := do
  match emitText? spec name with
  | .ok text => IO.FS.writeFile path text
  | .error _ => throw (IO.userError s!"refused: {name}")

def lambdaSpec : Spec := ⟨Complete.Controls.lambdaPlan, [], .base "Term", .standard⟩
def guardedSpec : Spec := ⟨GeneralGuardedBinderExecution.plan [.permit], [], .proc, .standard⟩
def sealedSpec : Spec := ⟨GeneralGuardedBinderExecution.plan [], [], .proc, .standard⟩
def branchingSpec : Spec := ⟨Complete.ClassesControls.branchingPlan, [], .base "T", .standard⟩
/-- λ compiled without the structural-descent refinement: its only obligation is stratification. -/
def unstratifiedSpec : Spec :=
  ⟨GeneralExecutionAdmission.compile ⟨Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language, [],
    {signatures := [], rows := []}⟩ StructuralDescent.Controls.rootPermissions, [], .base "Term", .standard⟩

def refusal (name : String) : String :=
  match emitText? lambdaSpec name with
  | .error (.nameCollision _) => "refused-name-collision"
  | _ => "NOT-REFUSED"

def main : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/emitted/"
  emitTo lambdaSpec "lambda" (dir ++ "complete_lambda.metta")
  emitTo guardedSpec "guarded" (dir ++ "complete_guarded.metta")
  emitTo sealedSpec "sealed" (dir ++ "complete_sealed.metta")
  emitTo branchingSpec "branching" (dir ++ "complete_branching.metta")
  emitTo unstratifiedSpec "unstratified" (dir ++ "complete_unstratified.metta")
  IO.println "; Controls for complete-machine modules. Each module was written by"
  IO.println "; CompleteEmission.emitText?; every expected readout is the Lean complete machine's."
  let source := GeneralGuardedBinderFrontierControls.source
  IO.println (runControl "lambda-nested-run" "lambda" lambdaSpec StructuralDescent.Controls.nestedRedex 40 50)
  IO.println (runControl "lambda-two-steps-run" "lambda" lambdaSpec Complete.Controls.twoSteps 60 50)
  IO.println (beginControl "lambda-begin-then-pages" "lambda" lambdaSpec Complete.Controls.twoSteps 60 50)
  IO.println (runControl "guarded-run" "guarded" guardedSpec source 10 40)
  IO.println (exploreControl "guarded-explore" "guarded" guardedSpec source 200)
  IO.println (runControl "sealed-run" "sealed" sealedSpec source 10 40)
  IO.println (runControl "branching-run" "branching" branchingSpec (.apply "A" []) 20 5)
  IO.println (exploreControl "branching-explore" "branching" branchingSpec (.apply "A" []) 12)
  IO.println (runControl "unstratified-lambda-run" "unstratified" unstratifiedSpec Complete.Controls.twoSteps 60 50)
  IO.println ("; name collision with the runtime: " ++ refusal "gslt:runner" ++ ", " ++ refusal "gslt:explore")
  IO.println ("; unstratified plan's obligations: " ++ reprStr (repr unstratifiedSpec.plan.obligations).pretty ++
    ", pending after the complete machine: " ++ toString (pending unstratifiedSpec.plan).length)

#eval main
