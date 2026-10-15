import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledReadout
import Mettapedia.OSLF.MeTTaIL.StructuralDescentPlan

/-!
# Original declaration origins of generic scoped execution

The execution ordinal and original authored declaration position remain
separate. This comparison applies to every emitted receipt of every admitted
plan; equal rule names or equal targets never identify declaration origins.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.AuthoredOrigins

open Syntax GeneralPremise GeneralExecutionAdmission

def declarationOrigin? (plan : GeneralExecutionAdmission.Plan) (ordinal : Nat) : Option Nat :=
  plan.rules[ordinal]?.map RulePlan.declarationIndex

/-- Every semantic receipt names a real selected declaration. Its original
source position, source schemas and premise list are retained by elaboration. -/
theorem root_original_declaration (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (answer : Execution.RootAnswer
      (GeneralPlanEnvironment.environment (Plan.compile snapshot permissions)) bound type source) :
    ∃ declaration : RulePlan,
      (Plan.compile snapshot permissions).rules[answer.index]? = some declaration ∧
      snapshot.language.rewrites[declaration.declarationIndex]? = some declaration.authored ∧
      selected permissions.ruleIndices declaration.declarationIndex = true ∧
      declaration.rule.name = declaration.authored.name ∧
      declaration.rule.left = declaration.authored.left ∧
      declaration.rule.right = declaration.authored.right ∧
      declaration.rule.premises = declaration.authored.premises := by
  cases answer.valid with
  | @fire _ _ _ _ _ rule _ _ _ _ _ declared _ _ _ _ _ _ _ _ =>
      have read : ((Plan.compile snapshot permissions).rules.map RulePlan.rule)[answer.index]? = some rule :=
        declared
      rw [List.getElem?_map] at read
      obtain ⟨declaration, position, _⟩ := Option.map_eq_some_iff.mp read
      have present : declaration ∈ (Plan.compile snapshot permissions).rules := List.mem_of_getElem? position
      have original : declaration ∈ (GeneralExecutionAdmission.compile snapshot permissions).rules := by
        simpa only [Plan.compile, Plan.rules_preserved] using present
      obtain ⟨authored, index, entry, enabled, compiled⟩ := compiled_rule_origin original
      have info := rulePlan_readout compiled
      have authoredAt := List.mk_mem_zipIdx_iff_getElem?.mp entry
      refine ⟨declaration, position, ?_, ?_, ?_⟩
      · simpa only [info.1, info.2.1] using authoredAt
      · simpa only [info.1] using enabled
      · exact GeneralRuleBindingInference.elaborate_source declaration.binding declaration.authored

/-- The computed origin readout reports the original index of the actual
receipt's selected declaration, even when selected ordinals are renumbered. -/
theorem receipt_origin (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (answer : Execution.RootAnswer
      (GeneralPlanEnvironment.environment (Plan.compile snapshot permissions)) bound type source) :
    ∃ index authored,
      declarationOrigin? (Plan.compile snapshot permissions) answer.index = some index ∧
      snapshot.language.rewrites[index]? = some authored ∧
      selected permissions.ruleIndices index = true := by
  obtain ⟨declaration, position, original, enabled, _⟩ :=
    root_original_declaration snapshot permissions bound type source answer
  exact ⟨declaration.declarationIndex, declaration.authored,
    by simp only [declarationOrigin?, position, Option.map_some], original, enabled⟩

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.AuthoredOrigins
