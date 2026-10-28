import Mettapedia.Computability.KolmogorovComplexity.FeatureSchemePrefix
import Mettapedia.Examples.Compression.FeatureCompressionRatioControls

/-!
# Complete feature-scheme controls

Wire round trips retain order and duplicate frames. Two noncommuting helpers
make a reversed application order observable. Truncated count/frame packets
are refused, and a missing helper computation cannot fabricate an output.
Canonical universal-machine controls include arbitrarily large sources whose
ideal schemes must actually take a compression step.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureSchemeControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open scoped Classical

def prefixer : ConditionalAlgorithm := fun program input =>
  if program = [false] then Part.some (false :: input)
  else if program = [true] then Part.some (true :: input)
  else Part.none

theorem frame_order_round_trip :
    decodeSchemeDescription (schemeDescription [[false], [true]] [true]) =
      some ([[true], [false]], [true]) := by
  simpa using decodeSchemeDescription_encode [[false], [true]] [true]

theorem duplicate_frames_survive :
    decodeSchemeDescription (schemeDescription [[false], [false]] [true]) =
      some ([[false], [false]], [true]) := by
  simpa using decodeSchemeDescription_encode [[false], [false]] [true]

theorem empty_packet_refused : decodeSchemeDescription [] = none := by decide

theorem missing_first_frame_refused :
    decodeSchemeDescription (pairCondition [false] []) = none := by decide

theorem missing_second_frame_refused :
    decodeSchemeDescription (pairCondition [false, false] (packFeatureFrames [[false]] [])) = none := by decide

theorem complete_empty_feature_cost : (schemeDescription [[]] []).length = 4 := by
  norm_num [schemeDescription_length]

theorem original_application_order :
    [false, true] ∈ schemeInterpreter prefixer (schemeDescription [[false], [true]] []) [] := by
  rw [schemeInterpreter_encode_iff]
  apply runStoredFeatures_cons (middle := [true])
  · simp [prefixer]
  · apply runStoredFeatures_cons (middle := [false, true])
    · simp [prefixer]
    · exact runStoredFeatures_nil prefixer _

theorem reversed_application_order :
    [true, false] ∈ schemeInterpreter prefixer (schemeDescription [[true], [false]] []) [] := by
  rw [schemeInterpreter_encode_iff]
  apply runStoredFeatures_cons (middle := [false])
  · simp [prefixer]
  · apply runStoredFeatures_cons (middle := [true, false])
    · simp [prefixer]
    · exact runStoredFeatures_nil prefixer _

theorem reordering_is_observable :
    ¬ [false, true] ∈ schemeInterpreter prefixer (schemeDescription [[true], [false]] []) [] := by
  intro wrong
  have impossible := Part.mem_unique wrong reversed_application_order
  simp at impossible

theorem divergent_helper_has_no_output (residual output : BinString) :
    ¬ output ∈ schemeInterpreter prefixer (schemeDescription [[]] residual) [] := by
  rw [schemeInterpreter_encode_iff]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [runStoredFeatures_cons_iff]
  simp [prefixer]

theorem prefix_packet_executes :
    IsProgram (selfDelimitingConditionalMachine (schemeInterpreter prefixer))
      (prefixSchemeDescription [[false], [true]] []) [] [false, true] :=
  selfDelimitingConditionalMachine_isProgram (schemeInterpreter prefixer) original_application_order

theorem prefix_packet_extension_refused :
    (selfDelimitingConditionalMachine (schemeInterpreter prefixer)).compute
      (prefixSchemeDescription [[false], [true]] [] ++ [false]) [] = none :=
  prefix_scheme_rejects_extension prefixer [[false], [true]] [] [false] [] (by decide)

theorem prefix_header_is_charged : (prefixSchemeDescription [[]] []).length = 11 := by decide

theorem raw_packet_has_different_prefix_payload :
    exactE2Payload (schemeDescription [] []) = some [] := by decide

theorem raw_packet_cannot_skip_prefix_framing :
    exactE2Payload (schemeDescription [] []) ≠ some (schemeDescription [] []) := by decide

theorem empty_chain_log_bound :
    (0 : ℝ) ≤ Real.log (1 : ℝ) / Real.log (3 / 2 : ℝ) + 1 := by norm_num

theorem canonical_nonempty_schemes :
    ∀ cutoff size : Nat, ∃ source features final,
      size < source.length ∧
      RationalScheme universalConditionalAlgorithm 3 2 cutoff source features final ∧
      features ≠ [] ∧ source ∈ schemeInterpreter universalConditionalAlgorithm (schemeDescription features final) [] := by
  intro cutoff size
  obtain ⟨source, large, compressed, _⟩ :=
    FeatureCompressionRatioControls.arbitrary_nonintegral_ratio_sources (cutoff + size)
  obtain ⟨features, final, scheme⟩ := exists_rational_scheme universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal 3 2 cutoff (by decide) (by decide) source
  have nonempty := scheme.nonempty_of_can_step (by omega) compressed
  exact ⟨source, features, final, by omega, scheme, nonempty, scheme.toBChain.scheme_reconstructs⟩

theorem canonical_description_bounds :
    ∃ fixedFeature : BinString, ∃ cutoff lowerOverhead : Nat, ∃ slope intercept : ℝ,
      0 ≤ slope ∧ 0 ≤ intercept ∧
      (∀ source, ∃ features final,
        RationalScheme universalConditionalAlgorithm 3 2 cutoff source features final) ∧
      ∀ source features final,
        RationalScheme universalConditionalAlgorithm 3 2 cutoff source features final →
        decodeSchemeDescription (schemeDescription features final) = some (features.reverse, final) ∧
        source ∈ schemeInterpreter universalConditionalAlgorithm (schemeDescription features final) [] ∧
        plainConditionalComplexity universalConditionalAlgorithm source [] ≤
          (schemeDescription features final).length + lowerOverhead ∧
        ((schemeDescription features final).length : ℝ) ≤
          (3 / 2 : ℝ) * plainConditionalComplexity universalConditionalAlgorithm source [] +
            slope * Real.log ((source.length : ℝ) + 1) + intercept ∧
        (∀ feature ∈ features, feature.length ≤ fixedFeature.length) ∧
        (features.length : ℝ) ≤ Real.log ((source.length : ℝ) + 1) / Real.log (3 / 2 : ℝ) + 1 := by
  exact rational_scheme_description_bounds universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec 3 2 (by decide) (by decide)

theorem canonical_prefix_description_bounds :
    ∃ cutoff lowerOverhead : Nat, ∃ slope intercept : ℝ, 0 ≤ slope ∧ 0 ≤ intercept ∧
      ∀ source features final,
        RationalScheme universalConditionalAlgorithm 3 2 cutoff source features final →
        conditionalComplexity trimmedIndexedHost source [] ≤
          (prefixSchemeDescription features final).length + lowerOverhead ∧
        ((prefixSchemeDescription features final).length : ℝ) ≤
          (3 / 2 : ℝ) * conditionalComplexity trimmedIndexedHost source [] +
            slope * Real.log ((source.length : ℝ) + 1) + intercept := by
  obtain ⟨_, cutoff, lowerOverhead, slope, intercept, slopeNonnegative, interceptNonnegative, _, bounds⟩ :=
    rational_scheme_prefix_bounds universalConditionalAlgorithm trimmedIndexedHost
      universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
      isReferenceMachine_trimmedIndexedHost 3 2 (by decide) (by decide)
  refine ⟨cutoff, lowerOverhead, slope, intercept, slopeNonnegative, interceptNonnegative,
    fun source features final scheme => ?_⟩
  have qualified := bounds source features final scheme
  exact ⟨qualified.2.1, qualified.2.2.1⟩

theorem no_premature_zero_step {U : ConditionalAlgorithm} {numerator denominator cutoff : Nat}
    {source final : BinString} (large : cutoff < source.length)
    (compressible : rationalFactor numerator denominator * plainConditionalComplexity U source [] ≤ source.length) :
    ¬ RationalScheme U numerator denominator cutoff source [] final := by
  intro scheme
  exact scheme.nonempty_of_can_step large compressible rfl

#print axioms frame_order_round_trip
#print axioms duplicate_frames_survive
#print axioms empty_packet_refused
#print axioms missing_first_frame_refused
#print axioms missing_second_frame_refused
#print axioms complete_empty_feature_cost
#print axioms original_application_order
#print axioms reversed_application_order
#print axioms reordering_is_observable
#print axioms divergent_helper_has_no_output
#print axioms prefix_packet_executes
#print axioms prefix_packet_extension_refused
#print axioms prefix_header_is_charged
#print axioms raw_packet_has_different_prefix_payload
#print axioms raw_packet_cannot_skip_prefix_framing
#print axioms empty_chain_log_bound
#print axioms canonical_nonempty_schemes
#print axioms canonical_description_bounds
#print axioms canonical_prefix_description_bounds
#print axioms no_premature_zero_step

end Mettapedia.Examples.Compression.FeatureSchemeControls
