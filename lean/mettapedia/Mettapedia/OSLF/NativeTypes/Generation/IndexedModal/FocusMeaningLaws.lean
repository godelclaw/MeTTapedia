import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning

/-! # Variance, fixed ambient captures and specified reducts -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning

open Mettapedia.OSLF.MeTTaIL Syntax ScopedRuleMatching GeneralPremise
open Mettapedia.OSLF.NativeTypes.Modal
open NativeReceiptRechecking

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}

/-- Ambient matched variables can be fixed by the semantic environment;
they are not additional universally varied rely slots. -/
def Arguments.atAnchor (arguments : Arguments installed index ambient) (anchor : ScopedRuleMatching.Assignment) :
    Arguments installed index ambient :=
  {arguments with target := fun values assignment target =>
    (∀ name ∈ (installed.indexed.schema index).matchedNames,
      lookup assignment name = lookup anchor name) ∧ arguments.target values assignment target}

theorem anchored_response_captures {arguments : Arguments installed index ambient}
    {anchor : ScopedRuleMatching.Assignment} {focus : Pattern} {values : RelyValues installed index ambient}
    (response : Response (arguments.atAnchor anchor) focus values) :
    ∀ name ∈ (installed.indexed.schema index).matchedNames,
      lookup response.receipt.firing.answer.completed name = lookup anchor name :=
  response.target.1

/-- Restricting admitted requests and weakening the postcondition preserves
the entire response family. Index values must remain unchanged. -/
theorem variance (first second : Arguments installed index ambient) (focus : Pattern)
    (indices : ∀ position, (first.indices position).value = (second.indices position).value)
    (requests : ∀ values, Requested second values → Requested first values)
    (targets : ∀ values assignment target, first.target values assignment target →
      second.target values assignment target) :
    Inhabits first focus → Inhabits second focus := by
  rintro ⟨family⟩
  refine ⟨⟨family.admitted, fun values requested => ?_⟩⟩
  let response := family.respond values (requests values requested)
  refine ⟨response.source, response.receipt, response.focus_eq, ?_, response.relies,
    targets _ _ _ response.target⟩
  intro position
  exact (response.indices position).trans (congrArg (fun value => some value.val) (indices position))

theorem SourceResponse.specified_rhs {arguments : Arguments installed index ambient}
    {focus source : Pattern} {values : RelyValues installed index ambient} {payload : Payload}
    (response : SourceResponse arguments focus values source payload) :
    reductWith? (ScopedReflectiveExecution.binderOperation installed.indexed.operational.Environment.reflection
      (installed.indexed.schema index).declaration.rule)
      (installed.indexed.schema index).declaration.rule (installed.indexed.schema index).declaration.binding.spec
      ambient.length payload.completed = some payload.target := by
  have firing := response.1
  have selected := response.2.1
  have declared := GeneralPlanEnvironment.selected_rule (BindingPipeline.plan installed.indexed.operational.generated)
    (List.mk_mem_zipIdx_iff_getElem?.mp (installed.indexed.schema index).declared)
  have specified := GeneralPlanEnvironment.selected_specification (BindingPipeline.plan installed.indexed.operational.generated)
    (List.mk_mem_zipIdx_iff_getElem?.mp (installed.indexed.schema index).declared)
  cases firing with
  | fire actualRule actualSpec _ _ _ _ _ reduct _ =>
      rw [selected] at actualRule actualSpec
      cases Option.some.inj (actualRule.symm.trans declared)
      cases Option.some.inj (actualSpec.symm.trans specified)
      simpa only [NativeBindingEventAction.bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext,
        List.length_map] using reduct

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning
