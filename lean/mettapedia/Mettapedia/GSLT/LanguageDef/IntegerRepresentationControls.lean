import Mettapedia.GSLT.LanguageDef.IntegerRepresentationArithmetic

/-!
# Integer authoring, representation and arithmetic boundary controls

These controls concern structured declarations, exact source-provider
expressions and the represented numeric step. Small precisions exercise the
general finite-format laws; they do not assert C character arithmetic before
integer promotion. No textual `.module` parser or native implementation is
used as proof evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationControls

open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger
open Mettapedia.GSLT.LanguageDef.IntegerRepresentationExtension
open Mettapedia.GSLT.LanguageDef.IntegerRepresentationArithmetic
open Mettapedia.Languages.C11

def unsigned8 : IntegerFormat := .unsigned 8 (by decide)
def twos8 : IntegerFormat := .signed 7 (by decide) (.twosComplement true)
def minimumTrap8 : IntegerFormat := .signed 7 (by decide) (.twosComplement false)
def signMagnitude8 : IntegerFormat := .signed 7 (by decide) .signMagnitude
def ones8 : IntegerFormat := .signed 7 (by decide) .onesComplement

def representations : Registry :=
  ⟨[⟨"exact", .exact⟩,
    ⟨"unsigned-8", .bounded unsigned8 .normal⟩,
    ⟨"twos-8", .bounded twos8 .normal⟩,
    ⟨"minimum-trap-8", .bounded minimumTrap8 .normal⟩,
    ⟨"sign-magnitude-8", .bounded signMagnitude8 .normal⟩,
    ⟨"ones-8", .bounded ones8 .normal⟩], by decide⟩

theorem checked_authoring_roundtrip :
    representationLayer.elaborate standardTheory
        (representationLayer.quote standardTheory representations) = some representations :=
  representationLayer.elaborate_quote standardTheory representations

theorem authored_reader_is_constructed :
    readAuthored? (quoteRegistry representations) "twos-8"
      (encodeValue (.bounded twos8 .normal) ⟨-7, by decide⟩) =
      some (.value (-7) false) :=
  readAuthored?_quote representations "twos-8" (.bounded twos8 .normal) (by decide) _

theorem missing_representation_identity_refused :
    readAuthored? (quoteRegistry representations) "missing" (.integer 128) = none := by
  cbv

theorem rejected_authoring_cannot_read :
    readAuthored? (.bundle [
      .declaration (.representation "same" .exact),
      .declaration (.representation "same" (.bounded (.unsigned 8) .normal))])
      "same" (.integer 1) = none := by cbv

theorem nested_authoring_retains_order :
    elaborate? (.bundle [
      .declaration (.representation "exact" .exact),
      .bundle [.declaration (.representation "twos-8" (.bounded
        (.signed 7 (.twosComplement true)) .normal))]]) =
      some ⟨[⟨"exact", .exact⟩, ⟨"twos-8", .bounded twos8 .normal⟩], by decide⟩ := by
  cbv

theorem duplicate_identity_refused :
    elaborate? (.bundle [
      .declaration (.representation "same" .exact),
      .declaration (.representation "same" (.bounded (.unsigned 8) .normal))]) = none := by
  cbv

theorem empty_identity_refused :
    elaborate? (.declaration (.representation "" .exact)) = none := by cbv

theorem zero_precision_refused :
    decodeProfile? (.bounded (.signed 0 .signMagnitude) .normal) = none ∧
      decodeProfile? (.bounded (.unsigned 0) .normal) = none := by cbv

theorem exact_module_integer_retained :
    readValue? .exact (encodeValue .exact (-4294967296)) =
      some (.value (-4294967296) false) := readValue?_encode .exact _

theorem decimal_exact_retained :
    decimalRealization.observeArtifact ()
        (decimalRealization.compile () (-4294967296)) = some (-4294967296) :=
  decimalRealization.adequate () _

theorem non_integer_module_carrier_refused :
    readValue? .exact (.string "42") = none := rfl

theorem signed_negative_encoding_constructed :
    encodeValue (.bounded twos8 .normal) ⟨-7, by decide⟩ = .integer 249 ∧
      readValue? (.bounded twos8 .normal) (.integer 249) = some (.value (-7) false) := by
  cbv; decide

theorem signed_representations_really_differ :
    encodeValue (.bounded signMagnitude8 .normal) ⟨-7, by decide⟩ = .integer 135 ∧
      encodeValue (.bounded ones8 .normal) ⟨-7, by decide⟩ = .integer 248 ∧
      encodeValue (.bounded twos8 .normal) ⟨-7, by decide⟩ = .integer 249 := by cbv; decide

theorem positive_and_negative_zero_retained :
    readValue? (.bounded signMagnitude8 .normal) (.integer 0) = some (.value 0 false) ∧
      readValue? (.bounded signMagnitude8 .normal) (.integer 128) = some (.value 0 true) := by
  cbv; decide

theorem negative_zero_trap_retained :
    readValue? (.bounded signMagnitude8 .trap) (.integer 128) = some (.trap .negativeZero) := by
  cbv

theorem minimum_trap_distinguished :
    readValue? (.bounded twos8 .normal) (.integer 128) = some (.value (-128) false) ∧
      readValue? (.bounded minimumTrap8 .normal) (.integer 128) = some (.trap .minimum) := by
  cbv; decide

theorem invalid_word_is_not_a_trap :
    readValue? (.bounded twos8 .normal) (.integer 256) = none ∧
      readValue? (.bounded unsigned8 .normal) (.integer (-1)) = none := by cbv

theorem canonical_store_selects_positive_zero :
    encodeValue (.bounded signMagnitude8 .normal) ⟨0, by decide⟩ = .integer 0 ∧
      encodeValue (.bounded ones8 .normal) ⟨0, by decide⟩ = .integer 0 := by cbv; decide

theorem same_input_encoding_does_not_fix_arithmetic :
    encodeValue .exact 127 = encodeValue (.bounded twos8 .normal) ⟨127, by decide⟩ ∧
      coreSem .add 127 1 = .val 128 ∧
      evaluateIntegerBinary twos8 .add ⟨127, by decide⟩ ⟨1, by decide⟩ =
        .undefined .overflow := by cbv; decide

theorem unsigned_wrap_differs_from_exact :
    coreSem .add 255 1 = .val 256 ∧
      evaluateIntegerBinary unsigned8 .add ⟨255, by decide⟩ ⟨1, by decide⟩ = .value 0 := by cbv

theorem overflow_excludes_common_domain :
    ¬ CommonDomain twos8 .add ⟨127, by decide⟩ ⟨1, by decide⟩ ∧
      ¬ CommonDomain unsigned8 .add ⟨255, by decide⟩ ⟨1, by decide⟩ := by decide

theorem quotient_convention_is_separate :
    coreSem .tquot (-7) 2 = .val (-3) ∧ coreSem .fquot (-7) 2 = .val (-4) ∧
      coreSem .trem (-7) 2 = .val (-1) ∧ coreSem .frem (-7) 2 = .val 1 := by decide

theorem remainder_requires_quotient_to_fit :
    coreSem .trem (-128) (-1) = .val 0 ∧
      evaluateIntegerBinary twos8 .remainder ⟨-128, by decide⟩ ⟨-1, by decide⟩ =
        .undefined .overflow ∧
      ¬ CommonDomain twos8 .remainder ⟨-128, by decide⟩ ⟨-1, by decide⟩ := by decide

theorem conversion_policy_is_separate :
    convertInteger intervalReductionPolicy 255 (.integer twos8) = .value (-1) ∧
      convertInteger (signalingPolicy 9) 255 (.integer twos8) = .signal 9 ∧
      evaluateIntegerBinary twos8 .add ⟨127, by decide⟩ ⟨1, by decide⟩ =
        .undefined .overflow := by decide

theorem common_sum_constructs_independent_evaluation :
    IntegerBinaryEvaluation unsigned8 ⟨200, by decide⟩ ⟨55, by decide⟩ .add (.value 255) :=
  binary_within unsigned8 .add _ _ (by decide)

theorem represented_common_sum_steps :
    IntegerStep.stepData intervalReductionPolicy
      (compile unsigned8 .add ⟨200, by decide⟩ ⟨55, by decide⟩) =
      some (.completed (.binary (.value 255))) :=
  compiled_step intervalReductionPolicy unsigned8 .add _ _ (by decide)

theorem representation_step_observes_common_quotient :
    observeStep? intervalReductionPolicy
        (compile twos8 .divide ⟨-7, by decide⟩ ⟨2, by decide⟩) =
      some (.inl (.val (-3))) :=
  observeStep?_compiled intervalReductionPolicy twos8 .divide _ _ (by decide)

theorem represented_fault_remains_a_fault :
    observeStep? intervalReductionPolicy
        (compile twos8 .divide ⟨7, by decide⟩ ⟨0, by decide⟩) =
      some (.inr .divisionByZero) ∧
      coreSem .tquot 7 0 = .declined := by cbv

theorem malformed_operand_is_not_a_language_fault :
    observeStep? intervalReductionPolicy
      (.pending (.binary (.unsigned 8) .add 256 1)) = none := by cbv

theorem one_numeric_reduction_two_driver_actions :
    (IntegerStep.machine intervalReductionPolicy).run 2
        (.pending (.binary unsigned8 .add ⟨200, by decide⟩ ⟨55, by decide⟩)) =
      ([⟨.binary unsigned8 .add ⟨200, by decide⟩ ⟨55, by decide⟩,
        .binary (.value 255)⟩], .finished (.binary (.value 255))) ∧
      (IntegerStep.machine intervalReductionPolicy).spent IntegerStep.price 2
        (.pending (.binary unsigned8 .add ⟨200, by decide⟩ ⟨55, by decide⟩)) = 1 := by
  constructor
  · have exactRun := IntegerStep.run_two_finishes_with_one_occurrence intervalReductionPolicy
      (.binary unsigned8 .add ⟨200, by decide⟩ ⟨55, by decide⟩)
    simpa [IntegerStep.execute, evaluateIntegerBinary_within unsigned8 .add
      ⟨200, by decide⟩ ⟨55, by decide⟩ (by decide), mathematical,
      exactOperation, CoreOp.fn] using exactRun
  · exact IntegerStep.run_two_has_one_reduction_charge intervalReductionPolicy _

theorem extra_result_is_not_authorized : ¬ ExactEvaluation .add 17 25 (.val 0) := by
  intro extra
  have computed := coreSem_complete .add 17 25 (.val 0) extra
  simp [coreSem, undefinedAt, CoreOp.isPartial, CoreOp.fn] at computed

theorem nested_source_provider_consumes_exact_sum :
    Mettapedia.GSLT.Parsing.SourceIntegerProvider.IntegerEval
      [("?x", 17), ("?y", 25), ("?z", -3)]
      (.list [.atom "+", .list [.atom "+", .atom "?x", .atom "?y"], .atom "?z"]) 39 := by
  apply Mettapedia.GSLT.Parsing.SourceIntegerProvider.IntegerEval.add
    (first := 42) (second := -3)
  · apply Mettapedia.GSLT.Parsing.SourceIntegerProvider.IntegerEval.add
      (first := 17) (second := 25)
    · exact .sourceVar (by simp [Mettapedia.GSLT.Parsing.SourceIntegerProvider.sourceVariableToken]) (by simp [Mettapedia.GSLT.Parsing.SourceIntegerProvider.lookup?])
    · exact .sourceVar (by simp [Mettapedia.GSLT.Parsing.SourceIntegerProvider.sourceVariableToken]) (by simp [Mettapedia.GSLT.Parsing.SourceIntegerProvider.lookup?])
  · exact .sourceVar (by simp [Mettapedia.GSLT.Parsing.SourceIntegerProvider.sourceVariableToken]) (by simp [Mettapedia.GSLT.Parsing.SourceIntegerProvider.lookup?])

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationControls
