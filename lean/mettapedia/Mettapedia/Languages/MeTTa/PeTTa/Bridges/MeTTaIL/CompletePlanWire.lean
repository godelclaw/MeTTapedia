import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RulePlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution.Core
import Mettapedia.OSLF.MeTTaIL.StructuralDescentAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralEquationMeasures

/-!
# The complete machine's plan as MeTTa data

`(CompletePlan environment permissions bound expected rules equations admitted)`, read by
`gslt_complete.metta`. Shared by the emitter and the controls generators.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax

/-- `Admitted` when the structural admission check holds, so a rule's deepening is certified at
the focus size; `Unadmitted` otherwise. Symbols, since `True` would read back as a boolean. -/
def admittedTerm (value : Bool) : Term := .symbol (if value then "Admitted" else "Unadmitted")

/-- How deep an equation's premises go: `(EquationDepth constant names)` when the plan's rules and
the equation's premises descend, so every premise derivation at a capture fits in `constant` plus
the sizes of the captured values of `names` (`EquationJob.premisesBound`); `EquationUnbounded`
otherwise. -/
def equationDepthTerm (plan : GeneralExecutionAdmission.Plan) (equation : GeneralExecutionAdmission.EquationPlan) : Term :=
  if StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) &&
      StructuralDescent.checkPremises equation.rule equation.binding.spec 0 equation.rule.premises then
    .application "EquationDepth" [.natural (GeneralEquationMeasures.constantContribution equation.rule.left),
      CettaWire.encodeList Term.string equation.rule.left.freeFvarNames]
  else .symbol "EquationUnbounded"

/-- An equation of the plan with its position: `(EquationJobDeclaration position rule spec depth)`. -/
def equationDeclarationTerm (plan : GeneralExecutionAdmission.Plan)
    (pair : GeneralExecutionAdmission.EquationPlan × Nat) : Term :=
  .application "EquationJobDeclaration" [.natural pair.2, InferenceCettaWire.AuthoredRule.rewriteTerm pair.1.rule,
    InferenceCettaWire.AuthoredRule.bindingSpecTerm pair.1.binding.spec, equationDepthTerm plan pair.1]

/-- `(CompletePlan environment permissions bound expected rules equations admitted)`, with `table`
as the environment's free types. -/
def planTerm (plan : GeneralExecutionAdmission.Plan) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) : Term :=
  .application "CompletePlan"
    [PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan) table,
     InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites,
     CettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm bound,
     InferenceCettaWire.AuthoredRule.typeTerm expected,
     CettaWire.encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules,
     CettaWire.encodeList (equationDeclarationTerm plan) plan.equations.zipIdx,
     admittedTerm (StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan))]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire.admittedTerm

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire.equationDepthTerm

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire.equationDeclarationTerm

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire.planTerm
