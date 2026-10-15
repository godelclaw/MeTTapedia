import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingMatchInstantiation
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaCaptures

/-!
# Whole-context source reconstruction from original firing receipts

Every original scoped firing of an ordinary tree declaration reconstructs
its actual source modulo binder display metadata, even after ordered
premises extend the assignment. The proof reads original matching evidence
and does not assume source reconstruction as a receipt field.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaSource

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage
open NativeBindingSchemaCaptures NativeBindingMatchInstantiation

variable {plan : Plan} (schema : Rules.Schema plan)

theorem reconstructed {ambient : List String} {sort : String} (point : Selected schema ambient sort)
    (shape : treeSchema schema.declaration.rule.left = true) :
    (instantiateAt? schema.declaration.rule schema.declaration.binding.spec ambient.length
      .left [] 0 point.val.receipt.completed schema.declaration.rule.left).map Pattern.eraseBinderMetadata =
        some (toPattern point.val.source) := by
  have selectedRule := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  have selectedSpec := GeneralPlanEnvironment.selected_specification plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  rw [← point.property] at selectedRule selectedSpec
  cases point.val.receipt.valid with
  | fire ruleLookup specLookup _ _ matching _ premises _ _ =>
      cases Option.some.inj (ruleLookup.symm.trans selectedRule)
      cases Option.some.inj (specLookup.symm.trans selectedSpec)
      obtain ⟨instantiated, actual, erased⟩ := matching_reconstructs
        (operation := Substitution.instantiateBVar) matching.matching shape premises.extension
      have actual' : instantiateWith? Substitution.instantiateBVar schema.declaration.rule
          schema.declaration.binding.spec ambient.length .left [] 0 point.val.receipt.completed
          schema.declaration.rule.left = some instantiated := by
        simpa only [NativeBindingEventAction.bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext,
          List.length_map] using actual
      change (instantiateWith? Substitution.instantiateBVar schema.declaration.rule
        schema.declaration.binding.spec ambient.length .left [] 0 point.val.receipt.completed
        schema.declaration.rule.left).map Pattern.eraseBinderMetadata = some (toPattern point.val.source)
      rw [actual']
      apply congrArg some
      exact erased.trans (Pattern.eraseBinderMetadata_eq_self_of_canonical (toPattern_canonical point.val.source))

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaSource
