import Mettapedia.OSLF.NativeTypes.Modal.NativeEventDeclarations
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTypedFocusCoverage

/-!
# Actual typing descents retained by every generated modal schema

The finite schema catalogue is derived from authored rules and the checked
typed occurrence generator. This comparison recovers its independent typing
descent, exact local binder prefix and original address for every entry.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingGeneratedSchemaTyping

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.OSLF.NativeTypes.Generation
open TypedOccurrences

theorem generated_licensed {plan : Plan} (index : NativeEventDeclarations.Index plan) :
    ∃ site : SiteData,
      Licensed plan.snapshot.language
        (Occurrences.ruleFree (NativeEventDeclarations.schema plan index).declaration.rule)
        .all [] (NativeEventDeclarations.schema plan index).programCarrier
        (NativeEventDeclarations.schema plan index).declaration.rule.left site ∧
      (NativeEventDeclarations.schema plan index).position = site.address ∧
      (NativeEventDeclarations.schema plan index).focusBound = site.focusBound ∧
      (NativeEventDeclarations.schema plan index).focusCarrier = site.focusType := by
  have member : NativeEventDeclarations.schema plan index ∈ schemas plan :=
    List.getElem_mem index.isLt
  unfold schemas at member
  obtain ⟨entry, _, carriers⟩ := List.mem_flatMap.mp member
  obtain ⟨carrier, _, occurrences⟩ := List.mem_flatMap.mp carriers
  obtain ⟨site, siteMember, same⟩ := List.mem_map.mp occurrences
  refine ⟨site, ?_, ?_, ?_, ?_⟩
  · rw [← same]
    exact generate_sound _ _ _ _ _ _ _ siteMember
  · rw [← same]
  · rw [← same]
  · rw [← same]

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingGeneratedSchemaTyping
