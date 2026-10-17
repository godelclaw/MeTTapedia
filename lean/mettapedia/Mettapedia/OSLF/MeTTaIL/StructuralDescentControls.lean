import Mettapedia.OSLF.MeTTaIL.StructuralDescentPlan
import Mettapedia.OSLF.Syntax.LambdaAuthoredFullRuleProfile
import Mettapedia.Languages.PartrecMachine.LanguageDef
import Mettapedia.OSLF.NativeTypes.Instances.LetCase.Language

/-!
# Controls on original authored recursive and first-order languages

The lambda source is the original four-rule scoped profile, including Beta,
LamCong and both AppCong declarations. The same generic interpreter executes
recursive congruence under arbitrarily repeated binders; no intrinsic-lambda
runtime adapter is used. The partial-recursive-machine source is its original
authored declaration snapshot and is elaborated by ordinary binding inference.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding GeneralPremise
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

private def term : TypeExpr := .base "Term"

/-- Generic extraction of explicit authored occurrence specifications. -/
def authoredEnvironment (language : LanguageDef) : Environment where
  language := language
  free := fun _ => none
  provider := {signatures := [], rows := []}
  specifications := language.rewrites.zipIdx.filterMap fun (rule, index) =>
    rule.bindings.map fun spec => (index, spec)

def lambdaEnvironment : Environment := authoredEnvironment LambdaAuthoredFullRuleProfile.language

theorem original_lambda_source :
    lambdaEnvironment.language = LambdaAuthoredFullRuleProfile.language := rfl

theorem lambda_structural_admission : checkEnvironment lambdaEnvironment = true := by
  simp [checkEnvironment, lambdaEnvironment, authoredEnvironment,
    LambdaAuthoredFullRuleProfile.language, language, betaRule, lamCongRule,
    LambdaAuthoredFullRuleProfile.appCongLRule, LambdaAuthoredFullRuleProfile.appCongRRule,
    LambdaAuthoredFullRuleProfile.appCongLSpec, LambdaAuthoredFullRuleProfile.appCongRSpec,
    LambdaAuthoredFullRuleProfile.appCongLStep, LambdaAuthoredFullRuleProfile.appCongRStep,
    specification?, StructuralDescent.checkRule, checkPremises, checkPremise, checkSource,
    checkDescent, fvarCount, fvarCountList, GeneralEquationAdmission.restCount, GeneralEquationAdmission.restCountList, GeneralEquationMeasures.constantContribution,
    GeneralEquationMeasures.evaluate, GeneralEquationMeasures.evaluateList,
    Pattern.freeFvarNames, GeneralEquationAdmission.checkSide,
    GeneralEquationAdmission.checkArguments]
  decide +kernel

theorem lambda_complete (bound : List TypeExpr) (source : Pattern)
    (answer : Execution.RootAnswer lambdaEnvironment bound term source) :
    answer ∈ Execution.exhaustive lambdaEnvironment bound term source :=
  Execution.exhaustive_complete lambdaEnvironment lambda_structural_admission bound term source answer

def nestedRedex : Pattern :=
  .apply "Lam" [.lambda none
    (.apply "Lam" [.lambda none
      (.apply "App" [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0])])]

def nestedTarget : Pattern :=
  .apply "Lam" [.lambda none (.apply "Lam" [.lambda none (.bvar 0)])]

def nestedTargets : List Pattern :=
  (Execution.exhaustive lambdaEnvironment [] term nestedRedex).map (·.target)

#guard nestedTargets == [nestedTarget]

/- The same declaration recurs below each lambda. This is precisely the call
that declaration-index stratification rejects, and structural descent admits. -/
mutual
def childIndices : Event → List Nat
  | .child _ _ index _ _ _ _ _ _ _ history =>
      index :: childIndicesList history
  | .quantified _ _ _ elements => elementChildIndices elements
  | _ => []
termination_by event => sizeOf event

def childIndicesList : List Event → List Nat
  | [] => []
  | event :: events => childIndices event ++ childIndicesList events
termination_by events => sizeOf events

def elementChildIndices : List (Nat × Pattern × List Event) → List Nat
  | [] => []
  | (_, _, events) :: elements => childIndicesList events ++ elementChildIndices elements
termination_by elements => sizeOf elements
end

#guard ((Execution.exhaustive lambdaEnvironment [] term nestedRedex).map fun answer =>
  (answer.index, answer.history.flatMap childIndices)) == [(1, [1, 0])]

def illScoped : Pattern := .apply "App" [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0]

#guard (Execution.exhaustive lambdaEnvironment [] term illScoped).isEmpty
#guard !(Execution.exhaustive lambdaEnvironment [term] term illScoped).isEmpty
#guard (Execution.roots lambdaEnvironment 1 [] term nestedRedex).isEmpty
#guard !(Execution.roots lambdaEnvironment 3 [] term nestedRedex).isEmpty

def cyclicRule : RewriteRule := {
  «name» := "Cycle", typeContext := [("X", term), ("Y", term)],
  premises := [.congruence (.fvar "X") (.fvar "Y")],
  left := .fvar "X", right := .fvar "Y",
  bindings := some { dependencies := [("X", []), ("Y", [])], occurrences := [] } }

theorem self_cycle_rejected :
    checkEnvironment (authoredEnvironment {LambdaAuthoredFullRuleProfile.language with rewrites := [cyclicRule]}) =
      false := by
  decide +kernel

def partrecSnapshot : GeneralExecutionAdmission.Snapshot where
  language := Mettapedia.Languages.PartrecMachine.partrecMachine
  freeTypes := []
  provider := {signatures := [], rows := []}

def rootPermissions : GeneralExecutionAdmission.Permissions where
  sites := .rootOnly
  equationIndices := some []
  includeDerivedEquations := false

def partrecPlan : GeneralExecutionAdmission.Plan := Plan.compile partrecSnapshot rootPermissions

def partrecEnvironment : Environment := GeneralPlanEnvironment.environment partrecPlan

#guard checkEnvironment partrecEnvironment
#guard partrecPlan.rules.length == 19

def partrecStart : Pattern :=
  .apply "Normal" [.apply "ZeroCode" [], .apply "HaltCont" [], .apply "Nil" []]

def partrecTargets : List Pattern :=
  (Execution.exhaustive partrecEnvironment [] (.base "Cfg") partrecStart).map (·.target)

#eval partrecTargets

#guard partrecTargets ==
  [.apply "Ret" [.apply "HaltCont" [], .apply "Cons" [.apply "Zero" [], .apply "Nil" []]]]

namespace LetCaseControls

open Mettapedia.OSLF.NativeTypes.Instances.LetCase

def environment : Environment := authoredEnvironment Mettapedia.OSLF.NativeTypes.Instances.LetCase.language

#guard checkEnvironment environment

theorem structurally_admitted : checkEnvironment environment = true := by
  simp [checkEnvironment, environment, authoredEnvironment, Mettapedia.OSLF.NativeTypes.Instances.LetCase.language,
    letRule, caseRule, letInitialCongruence, letBodyCongruence, caseBodyCongruence,
    letTerm, returnValue, caseTerm, pair, specification?, StructuralDescent.checkRule,
    checkPremises, checkPremise, checkSource, checkDescent, fvarCount, fvarCountList, GeneralEquationAdmission.restCount, GeneralEquationAdmission.restCountList,
    GeneralEquationMeasures.constantContribution, GeneralEquationMeasures.evaluate,
    GeneralEquationMeasures.evaluateList, Pattern.freeFvarNames,
    GeneralEquationAdmission.checkSide, GeneralEquationAdmission.checkArguments]
  decide +kernel

theorem complete (bound : List TypeExpr) (source : Pattern)
    (answer : Execution.RootAnswer environment bound computation source) :
    answer ∈ Execution.exhaustive environment bound computation source :=
  Execution.exhaustive_complete environment structurally_admitted bound computation source answer

def unit : Pattern := .apply "Unit" []
def inner : Pattern := letTerm (returnValue unit) (returnValue (.bvar 0))
def nested : Pattern := caseTerm (pair unit unit) inner

def targets (source : Pattern) : List Pattern :=
  (Execution.exhaustive environment [] computation source).map (·.target)

#guard targets inner == [returnValue unit]
#guard (targets nested).contains (caseTerm (pair unit unit) (returnValue unit))
#guard (Execution.exhaustive environment [] computation nested).any (fun answer =>
  answer.index == 4 && answer.history.flatMap childIndices == [0])
#guard (Execution.exhaustive environment [] value inner).isEmpty
#guard (Execution.exhaustive environment [] computation
  (letTerm (returnValue unit) (returnValue (.bvar 1)))).isEmpty

#print axioms structurally_admitted
#print axioms complete

end LetCaseControls

#print axioms lambda_structural_admission
#print axioms lambda_complete
#print axioms self_cycle_rejected

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Controls
