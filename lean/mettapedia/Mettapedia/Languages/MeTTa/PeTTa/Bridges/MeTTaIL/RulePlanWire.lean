import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! Rule-plan data shared by emitters and execution proofs. The original
constructor vocabulary, declaration positions and binding origins are retained.
Encoding a plan does not require importing its runtime realization proofs. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleJobReadoutExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission

def originTerm : GeneralRuleBindingInference.Origin → Term
  | .authored => .symbol "BindingAuthored"
  | .inferredRootInputs => .symbol "BindingInferredRootInputs"
  | .inferredGrammar implicitTypes => .application "BindingInferredGrammar"
      [encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm implicitTypes]

def decodeOrigin? : Term → Option GeneralRuleBindingInference.Origin
  | .symbol "BindingAuthored" => some .authored
  | .symbol "BindingInferredRootInputs" => some .inferredRootInputs
  | .application "BindingInferredGrammar" [implicitTypes] =>
      GeneralRuleBindingInference.Origin.inferredGrammar <$>
        decodeList InferenceCettaWire.AuthoredRule.decodeTypeBinding? implicitTypes
  | _ => none

@[simp] theorem decodeOrigin?_originTerm (origin : GeneralRuleBindingInference.Origin) :
    decodeOrigin? (originTerm origin) = some origin := by
  cases origin <;> simp [originTerm, decodeOrigin?, decodeList_encodeList]

def bindingPlanTerm (plan : GeneralRuleBindingInference.BindingPlan) : Term :=
  .application "RuleBindingPlan" [InferenceCettaWire.AuthoredRule.bindingSpecTerm plan.spec, originTerm plan.origin]

def decodeBindingPlan? : Term → Option GeneralRuleBindingInference.BindingPlan
  | .application "RuleBindingPlan" [spec, origin] => do
      pure ⟨← InferenceCettaWire.AuthoredRule.decodeBindingSpec? spec, ← decodeOrigin? origin⟩
  | _ => none

@[simp] theorem decodeBindingPlan?_bindingPlanTerm (plan : GeneralRuleBindingInference.BindingPlan) :
    decodeBindingPlan? (bindingPlanTerm plan) = some plan := by
  cases plan
  simp [bindingPlanTerm, decodeBindingPlan?]

def rulePlanTerm (plan : RulePlan) : Term :=
  .application "RuleJobDeclaration" [.natural plan.declarationIndex, InferenceCettaWire.AuthoredRule.rewriteTerm plan.authored,
    bindingPlanTerm plan.binding]

def decodeRulePlan? : Term → Option RulePlan
  | .application "RuleJobDeclaration" [.natural index, authored, binding] => do
      pure ⟨index, ← InferenceCettaWire.AuthoredRule.decodeRewrite? authored, ← decodeBindingPlan? binding⟩
  | _ => none

@[simp] theorem decodeRulePlan?_rulePlanTerm (plan : RulePlan) :
    decodeRulePlan? (rulePlanTerm plan) = some plan := by
  cases plan
  simp [rulePlanTerm, decodeRulePlan?]

#print axioms decodeOrigin?_originTerm
#print axioms decodeBindingPlan?_bindingPlanTerm
#print axioms decodeRulePlan?_rulePlanTerm

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleJobReadoutExecution
