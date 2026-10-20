import Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall
import Mettapedia.GSLT.LanguageDef.IntegerRepresentationExtension

/-!
# Controls for represented providers and signed dispatch

The decimal instance reuses the existing source-integer codec. Its provider
is a mathematical reference for checking the composition, not a GMP model.
Negative controls distinguish a corrupt signed decoder, unchecked overflow,
resource failure, and a source zero-divisor decline.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Controls

open ArithmeticExternalCallPilot

def decimalEncode (value : Int) : String :=
  IntegerRepresentationExtension.decimalRealization.compile () value

def decimalDecode (wire : String) : Int :=
  (IntegerRepresentationExtension.decimalRealization.observeArtifact () wire).getD 0

theorem decimal_roundtrip : Function.LeftInverse decimalDecode decimalEncode := by
  intro value
  change (IntegerRepresentationExtension.decimalRealization.observeArtifact ()
    (IntegerRepresentationExtension.decimalRealization.compile () value)).getD 0 = value
  rw [IntegerRepresentationExtension.decimalRealization.adequate]
  rfl

/-- The error labels here are test observations, not a replacement ABI enum. -/
def decimalReference : Provider String String := fun operation left right =>
  if operation.undefinedAt (decimalDecode right) then .error "engine-fault"
  else .ok (decimalEncode (operation.fn (decimalDecode left) (decimalDecode right)))

theorem decimalReference_sound : SuccessfulSound decimalDecode decimalReference := by
  intro operation left right result defined returned
  simp only [decimalReference, if_neg defined, Except.ok.injEq] at returned
  subst result
  exact decimal_roundtrip _

theorem decimalReference_available :
    FallbackAvailable signedFastPath decimalEncode decimalReference := by
  intro request defined _
  refine ⟨decimalEncode request.meaning, ?_⟩
  simp only [decimalReference, decimal_roundtrip request.left,
    decimal_roundtrip request.right, if_neg defined, Request.meaning]

theorem decimalReference_adequate : ExternalCallAdequacy
    (successfulExternal signedFastPath decimalEncode decimalDecode decimalReference) :=
  externalCallAdequacy signedFastPath decimalEncode decimalDecode decimal_roundtrip
    decimalReference decimalReference_sound decimalReference_available

theorem decimal_fallback (request : Request) (defined : request.Defined)
    (refused : signedFastPath.attempt request = none) :
    dispatch signedFastPath decimalEncode decimalReference request =
      .ok (.inr (decimalEncode request.meaning)) := by
  simp only [dispatch, refused, decimalReference, decimal_roundtrip request.left,
    decimal_roundtrip request.right, if_neg defined, Except.map, Request.meaning]

theorem all_operations_exact (operation : ArithmeticExtension.ExactInteger.CoreOp)
    (left right : Int) :
    run signedFastPath decimalEncode decimalDecode decimalReference
      ⟨compileSyntax operation, left, right⟩ =
      .ok (ArithmeticExtension.ExactInteger.coreSem operation left right) :=
  run_compiled_eq_core signedFastPath decimalEncode decimalDecode decimal_roundtrip
    decimalReference decimalReference_sound decimalReference_available operation left right

theorem negative_word_decodes_signed :
    (Int64.ofInt (-1)).toInt = -1 := by decide

theorem negative_word_unsigned_decode_is_wrong :
    ((Int64.ofInt (-1)).toUInt64.toNat : Int) ≠ -1 := by decide

theorem unsigned_decode_not_roundtrip :
    ¬ Function.LeftInverse (fun word : Int64 => (word.toUInt64.toNat : Int)) Int64.ofInt := by
  intro roundtrip
  exact negative_word_unsigned_decode_is_wrong (roundtrip (-1))

theorem last_safe_add_uses_word :
    dispatch signedFastPath decimalEncode decimalReference ⟨.add, 9223372036854775806, 1⟩ =
      .ok (.inl (Int64.ofInt 9223372036854775807)) := by decide

theorem signed_add_negative :
    dispatch signedFastPath decimalEncode decimalReference ⟨.add, -7, 3⟩ =
      .ok (.inl (Int64.ofInt (-4))) := by decide

theorem positive_overflow_uses_exact_fallback :
    dispatch signedFastPath decimalEncode decimalReference ⟨.add, 9223372036854775807, 1⟩ =
      .ok (.inr "9223372036854775808") := by
  rw [decimal_fallback _ (by decide) (by decide)]
  decide

theorem negative_overflow_uses_exact_fallback :
    dispatch signedFastPath decimalEncode decimalReference ⟨.add, -9223372036854775808, -1⟩ =
      .ok (.inr "-9223372036854775809") := by
  rw [decimal_fallback _ (by decide) (by decide)]
  decide

theorem large_input_uses_exact_fallback :
    dispatch signedFastPath decimalEncode decimalReference ⟨.add, 18446744073709551616, 3⟩ =
      .ok (.inr "18446744073709551619") := by
  rw [decimal_fallback _ (by decide) (by decide)]
  decide

theorem unchecked_signed_add_wraps :
    (Int64.ofInt 9223372036854775807 + 1).toInt = -9223372036854775808 := by decide

theorem unchecked_signed_add_not_exact :
    (Int64.ofInt 9223372036854775807 + 1).toInt ≠ (9223372036854775807 : Int) + 1 := by decide

theorem truncating_and_flooring_differ :
    run signedFastPath decimalEncode decimalDecode decimalReference ⟨.tquot, -7, 3⟩ =
      .ok (.val (-2)) ∧
    run signedFastPath decimalEncode decimalDecode decimalReference ⟨.fquot, -7, 3⟩ =
      .ok (.val (-3)) := by
  constructor
  · exact all_operations_exact .tquot (-7) 3
  · exact all_operations_exact .fquot (-7) 3

theorem signed_remainders_differ :
    run signedFastPath decimalEncode decimalDecode decimalReference ⟨.trem, -7, 3⟩ =
      .ok (.val (-1)) ∧
    run signedFastPath decimalEncode decimalDecode decimalReference ⟨.frem, -7, 3⟩ =
      .ok (.val 2) := by
  constructor
  · exact all_operations_exact .trem (-7) 3
  · exact all_operations_exact .frem (-7) 3

theorem direct_zero_divisor_is_provider_fault :
    decimalReference .tquot "7" "0" = .error "engine-fault" := by
  change decimalReference .tquot (decimalEncode 7) (decimalEncode 0) = _
  simp [decimalReference, decimal_roundtrip 0, CompiledOp.undefinedAt, CompiledOp.guard]

theorem guarded_zero_divisor_is_source_decline :
    run signedFastPath decimalEncode decimalDecode decimalReference ⟨.tquot, 7, 0⟩ =
      .ok .declined := by decide

def resourceFailure : Provider String String := fun _ _ _ => .error "resource-fault"

/-- No returned value is wrong. This deliberately says nothing about a
successful value ever being returned. -/
theorem resourceFailure_sound : SuccessfulSound decimalDecode resourceFailure := by
  intro _ _ _ _ _ returned
  cases returned

theorem resourceFailure_not_available :
    ¬ FallbackAvailable signedFastPath decimalEncode resourceFailure := by
  intro available
  obtain ⟨result, returned⟩ := available ⟨.sub, 7, 3⟩ (by decide) rfl
  cases returned

theorem resourceFailure_not_adequate : ¬ ExternalCallAdequacy
    (successfulExternal signedFastPath decimalEncode decimalDecode resourceFailure) := by
  intro adequate
  obtain ⟨_, result, returned, _⟩ := adequate.complete .sub 7 3 (by decide)
  simp [dispatch, signedFastPath, signedFastAttempt, resourceFailure, Except.map] at returned

theorem fast_success_does_not_need_provider_resources :
    run signedFastPath decimalEncode decimalDecode resourceFailure ⟨.add, -7, 3⟩ =
      .ok (.val (-4)) := by decide

theorem fallback_resource_failure_is_retained :
    run signedFastPath decimalEncode decimalDecode resourceFailure ⟨.sub, 7, 3⟩ =
      .error "resource-fault" := by decide

theorem resource_failure_is_not_decline :
    run signedFastPath decimalEncode decimalDecode resourceFailure ⟨.sub, 7, 3⟩ ≠
      .ok .declined := by decide

/-- The zero guard precedes dispatch even when the provider is unavailable. -/
theorem zero_guard_does_not_need_provider_resources :
    run signedFastPath decimalEncode decimalDecode resourceFailure ⟨.frem, 7, 0⟩ =
      .ok .declined := by decide

theorem unavailable_fallback_can_still_validate_fast_result :
    ArithmeticExtension.ExactInteger.coreSem .add (-7) 3 = .val (-4) :=
  run_compiled_value_sound signedFastPath decimalEncode decimalDecode decimal_roundtrip
    resourceFailure resourceFailure_sound .add (-7) 3 (-4) (by decide)

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Controls
