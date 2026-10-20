import Mettapedia.OSLF.NativeTypes.Instances.Natural.Provider
import Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCallControls
import Mettapedia.GSLT.LanguageDef.IntegerRepresentationRetainedCallControls
import Mettapedia.TypeTheory.NaturalRepresentations

/-! Joined controls: the backend observation is used to justify a natural
request and its authored transition, including negative and resource cases. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.Provider.Controls

open Mettapedia.GSLT.LanguageDef
open IntegerRepresentationExternalCall
open IntegerRepresentationExternalCall.Controls
open Mettapedia.TypeTheory.NaturalRepresentations

theorem natural_fast_result_without_available_fallback :
    ExactArithmetic.Evaluation .add 2 3 5 :=
  returned_natural_sound signedFastPath decimalEncode decimalDecode decimal_roundtrip
    resourceFailure resourceFailure_sound .add (Or.inl rfl) 2 3 5 (by decide)

theorem invented_natural_zero_refused :
    run signedFastPath decimalEncode decimalDecode decimalReference ⟨.sub, 2, 3⟩ ≠
      .ok (.val 0) := by
  intro returned
  have evaluated := returned_natural_sound signedFastPath decimalEncode decimalDecode
    decimal_roundtrip decimalReference decimalReference_sound .sub
    (Or.inr (Or.inl rfl)) 2 3 0 returned
  have computed := ExactArithmetic.evaluate?_of_evaluation evaluated
  contradiction

theorem valid_natural_request_can_lack_resources :
    ExactArithmetic.Evaluation .sub 7 3 4 ∧
      run signedFastPath decimalEncode decimalDecode resourceFailure ⟨.sub, 7, 3⟩ =
        .error "resource-fault" :=
  ⟨.sub 7 3 (by decide), fallback_resource_failure_is_retained⟩

theorem authored_successor_from_backend
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base Examples.NativeNaturalCounter.language
      (Examples.NativeNaturalCounter.counter 9) (Examples.NativeNaturalCounter.counter 10) := by
  apply (Provider.authored_target_iff signedFastPath decimalEncode decimalDecode
    decimal_roundtrip decimalReference decimalReference_sound decimalReference_available base 9 _).mpr
  exact ⟨10, by decide, rfl⟩

/-- The actual fallback result is interpreted in material naturals, without
executing a material-to-integer inverse or losing the selected decimal carrier. -/
theorem material_meaning_of_overflow_result :
    ExactArithmetic.representedAdd materialRepresentation
      (materialRepresentation.encode 9223372036854775807) (materialRepresentation.encode 1) =
      materialRepresentation.encode
        (resultInteger decimalDecode (.inr "9223372036854775808")).toNat :=
  retained_add_interpretation signedFastPath decimalEncode decimalDecode decimal_roundtrip
    decimalReference decimalReference_sound materialRepresentation 9223372036854775807 1
    (.inr "9223372036854775808") positive_overflow_uses_exact_fallback

/-- The source successor is obtained from an already stored large value;
the provider result retains the input's generation rather than re-encoding it. -/
theorem authored_successor_from_retained_backend
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base Examples.NativeNaturalCounter.language
      (Examples.NativeNaturalCounter.counter (2^128)) (Examples.NativeNaturalCounter.counter (2^128 + 1)) := by
  apply (Provider.retained_counter_target_iff Retained.Controls.encode Retained.Controls.decode
    Retained.Controls.roundtrip Retained.Controls.provider Retained.Controls.provider_sound
    base (2^128) (.inr ⟨2^128, 7⟩) rfl ?_ _).mpr
  · refine ⟨.inr ⟨2^128 + 1, 8⟩, by decide +kernel, ?_⟩
    apply congrArg Examples.NativeNaturalCounter.counter
    decide +kernel
  · intro _
    exact ⟨⟨2^128 + 1, 8⟩, rfl⟩

theorem retained_resource_failure_is_not_a_counter_refutation
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base Examples.NativeNaturalCounter.language
      (Examples.NativeNaturalCounter.counter 7) (Examples.NativeNaturalCounter.counter 8) ∧
    Retained.add Retained.Controls.encode Retained.Controls.limited (.inr ⟨7, 4⟩) (.inl 1) =
      .error "resource-exhausted" := by
  constructor
  · exact (Examples.NativeNaturalCounter.counter_step_target_iff base 7 _).mpr rfl
  · decide +kernel

end Mettapedia.OSLF.NativeTypes.Instances.Natural.Provider.Controls
