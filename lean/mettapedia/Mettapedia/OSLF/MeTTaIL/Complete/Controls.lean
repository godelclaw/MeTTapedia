import Mettapedia.OSLF.MeTTaIL.Complete.Run
import Mettapedia.OSLF.MeTTaIL.StructuralDescentControls

/-!
# Controls: the complete step search on recursive authored languages

The authored lambda calculus (beta with three congruence rules), the sorted let/case language
(congruence premises) and the partial-recursive machine, each compiled to a plan with root
sites only, so that every inner step comes from a recursive premise. Expected targets are the
existing exhaustive structural-descent readouts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Controls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open StructuralDescent
open Mettapedia.Machines

private def term : TypeExpr := .base "Term"

/-- A plan for an authored language: no free variables, no provider, root sites only. -/
def rootPlan (language : LanguageDef) : Plan :=
  StructuralDescent.Plan.compile ⟨language, [], {signatures := [], rows := []}⟩ Controls.rootPermissions

/-- The logged targets and whether the search is complete, after some rounds. -/
def readout (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (work : Nat) :
    List Pattern × Bool :=
  let state := Step.rounds plan bound expected work (Step.begin plan bound expected source)
  (state.log.map (·.target), Step.status plan state == .complete)

def lambdaPlan : Plan := rootPlan Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language

/-! ## Lambda: beta under two binders, through two congruence premises -/

#guard readout lambdaPlan [] term Controls.nestedRedex 200 == (Controls.nestedTargets, false)
#guard readout lambdaPlan [] term Controls.nestedRedex 4000 == (Controls.nestedTargets, true)
/- Certified once a drained level saw no depth cut, well before the depth reaches the term's size. -/
#guard !(readout lambdaPlan [] term Controls.nestedRedex 500).2 && (readout lambdaPlan [] term Controls.nestedRedex 550).2

/-- Two beta steps in sequence: `(λx.x) ((λy.y) (λz.z))`. -/
def identity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def twoSteps : Pattern := .apply "App" [identity, .apply "App" [identity, identity]]

/-- The targets of the independent exhaustive structural-descent readout. -/
def exhaustiveTargets (environment : GeneralPremise.Environment) (type : TypeExpr) (source : Pattern) :
    List Pattern :=
  (StructuralDescent.Execution.exhaustive environment [] type source).map (·.target)

#guard (readout lambdaPlan [] term twoSteps 3000).1.isPerm (exhaustiveTargets Controls.lambdaEnvironment term twoSteps)
#guard (readout lambdaPlan [] term twoSteps 3000) == ([.apply "App" [identity, identity], .apply "App" [identity, identity]], true)

/-! ## Let/case: congruence premises at computation positions -/

open Mettapedia.OSLF.NativeTypes.Instances.LetCase in
def letCasePlan : Plan := rootPlan Mettapedia.OSLF.NativeTypes.Instances.LetCase.language

open Mettapedia.OSLF.NativeTypes.Instances.LetCase in
#guard (readout letCasePlan [] computation Controls.LetCaseControls.nested 3000).1.isPerm
  (Controls.LetCaseControls.targets Controls.LetCaseControls.nested)
open Mettapedia.OSLF.NativeTypes.Instances.LetCase in
#guard (readout letCasePlan [] computation Controls.LetCaseControls.nested 3000).2

/-! ## The partial-recursive machine -/

#guard readout Controls.partrecPlan [] (.base "Cfg") Controls.partrecStart 3000 == (Controls.partrecTargets, true)

/-! ## A language that fails admission: beta with a self-cycling rule -/

def cyclicPlan : Plan := rootPlan
  {Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language with
    rewrites := [Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule, Controls.cyclicRule]}

#guard !StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment cyclicPlan)

/- Beta is found; every deeper cycle derivation of the same step is another receipt; the search is
never certified. -/
#guard let (targets, complete) := readout cyclicPlan [] term (.apply "App" [identity, identity]) 3000
  2 ≤ targets.length && targets.all (· == identity) && !complete

/-! ## A whole run: `(λx.x) ((λy.y) (λz.z))` to its normal form -/

def runReadout (ticks quantum : Nat) : List Pattern × String :=
  let machine := Run.advance lambdaPlan [] term ticks quantum (Run.begin lambdaPlan [] term twoSteps)
  (machine.states.reverse, match machine.phase with
    | .running => "running" | .done => "done" | .blocked => "blocked")

#guard runReadout 4 3000 == ([twoSteps, .apply "App" [identity, identity], identity], "done")

end Mettapedia.OSLF.MeTTaIL.Complete.Controls
