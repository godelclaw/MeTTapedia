import Mettapedia.Computability.KolmogorovComplexity.FeatureCompressionRatio
import Mettapedia.Examples.Compression.FeatureInformationControls

/-!
# Compression-ratio controls

The finite example separates shortest b-features from unrestricted shortest
features. The canonical interpreter has arbitrarily large sources compressible
by the nonintegral factor 3/2, witnessing the real-factor theorem's domain.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureCompressionRatioControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open scoped Classical

def source : BinString := List.replicate 8 true
def residual : BinString := List.replicate 4 true

def machine : ConditionalAlgorithm := fun program condition =>
  if program = [false] ∧ condition = residual then Part.some source
  else if program = [false, false] ∧ condition = [] then Part.some source
  else if program = [true] ∧ condition = source then Part.some residual
  else if program = [true, true] ∧ condition = source then Part.some []
  else Part.none

theorem unrestricted_short_feature : Feature machine [false] source := by
  refine ⟨[true], residual, ?_, ?_, ?_⟩ <;> simp [machine, source, residual]

theorem restricted_longer_feature : ShortestBFeature machine 3 [false, false] source := by
  refine ⟨⟨[true, true], [], ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [machine, source, residual]
  · simp [machine, source, residual]
  · simp [source]
  · norm_num [source]
  · intro other present
    obtain ⟨descriptive, rest, _, reconstructs, _, ratio⟩ := present
    unfold machine at reconstructs
    split_ifs at reconstructs with first second third fourth
    · obtain ⟨rfl, rfl⟩ := first
      norm_num [source, residual] at ratio
    · obtain ⟨rfl, rfl⟩ := second
      rfl
    · simp [source, residual] at reconstructs
    · simp [source] at reconstructs
    · simp at reconstructs

theorem restricted_minimum_is_not_unrestricted : ¬ ShortestFeature machine [false, false] source := by
  intro minimum
  have impossible := minimum.2 [false] unrestricted_short_feature
  simp at impossible

theorem restricted_shortest_descriptive :
    ShortestBDescriptiveMap machine 3 [false, false] [true, true] source := by
  refine ⟨⟨[], ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [machine, source, residual]
  · simp [machine, source, residual]
  · simp [source]
  · norm_num [source]
  · intro other present
    obtain ⟨rest, extracts, reconstructs, _, _⟩ := present
    have restEmpty : rest = [] := by
      by_contra different
      simp [machine, different] at reconstructs
    subst rest
    unfold machine at extracts
    split_ifs at extracts with first second third fourth
    · simp [source, residual] at first
    · simp [source] at second
    · simp [residual] at extracts
    · rw [fourth.1]
    · simp at extracts

theorem restricted_conditional_minimum :
    [false, false].length = plainConditionalComplexity machine source [] :=
  shortest_b_feature_conditional restricted_longer_feature
    (descriptive := [true, true]) (by simp [machine, source, residual])
    (by simp [machine, source, residual]) (by simp [source]) (by norm_num [source])

theorem restricted_maps_have_complexity_witness :
    ∃ descriptive rest, rest ∈ machine descriptive source ∧ source ∈ machine [false, false] rest ∧
      (3 : ℝ) * rest.length ≤ source.length ∧
      [false, false].length = plainConditionalComplexity machine source rest ∧
      descriptive.length = plainConditionalComplexity machine rest source := by
  obtain ⟨rest, extracts, reconstructs, ratio, featureLength, mapLength⟩ :=
    shortest_b_maps_conditional restricted_longer_feature restricted_shortest_descriptive
  exact ⟨[true, true], rest, extracts, reconstructs, ratio, featureLength, mapLength⟩

theorem arbitrary_nonintegral_ratio_sources :
    ∀ bound : Nat, ∃ source,
      bound < source.length ∧ (3 / 2 : ℝ) * plainConditionalComplexity universalConditionalAlgorithm source [] ≤ source.length ∧
      ∃ feature, ShortestBFeature universalConditionalAlgorithm (3 / 2) feature source := by
  obtain ⟨compiler, compiles⟩ := universalConditionalAlgorithm_isUniversal
    FeatureInformationControls.duplicate FeatureInformationControls.duplicate_effective
  intro bound
  let payload : BinString := List.replicate (bound + 3 * compiler.length + 1) false
  let source := payload ++ payload
  have computes : source ∈ universalConditionalAlgorithm (compiler ++ payload) [] :=
    compiles payload [] source (by simp [FeatureInformationControls.duplicate, source])
  have length := plainConditionalComplexity_le_of_program universalConditionalAlgorithm [] source _ computes
  have comp : plainConditionalComplexity universalConditionalAlgorithm source [] < source.length := by
    simp only [List.length_append, List.length_replicate, payload, source] at length ⊢
    omega
  have scaled : 3 * plainConditionalComplexity universalConditionalAlgorithm source [] ≤ 2 * source.length := by
    simp only [List.length_append, List.length_replicate, payload, source] at length ⊢
    omega
  obtain ⟨single, admitted, _⟩ := singleton_b_feature universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal (3 / 2) source comp
  obtain ⟨feature, minimum⟩ := exists_shortest_b_feature universalConditionalAlgorithm (3 / 2) source ⟨single, admitted⟩
  refine ⟨source, ?_, ?_, feature, minimum⟩
  · simp only [source, payload, List.length_append, List.length_replicate]
    omega
  · have realScaled : (3 : ℝ) * plainConditionalComplexity universalConditionalAlgorithm source [] ≤ 2 * source.length := by
      exact_mod_cast scaled
    linarith

theorem canonical_ratio_bounds :
    ∃ universalFeature : BinString, ∀ (factor : ℝ), 1 < factor → ∀ input,
      factor * plainConditionalComplexity universalConditionalAlgorithm input [] ≤ input.length →
      (((universalFeature.length : ℝ) * factor < (factor - 1) * input.length) →
        BFeature universalConditionalAlgorithm factor universalFeature input) ∧
      (∀ feature, ShortestFeature universalConditionalAlgorithm feature input →
        (feature.length : ℝ) ≤ max (universalFeature.length : ℝ) (universalFeature.length / (factor - 1))) ∧
      (∀ feature, ShortestBFeature universalConditionalAlgorithm factor feature input →
        (feature.length : ℝ) ≤ max (universalFeature.length : ℝ) (universalFeature.length / (factor - 1))) :=
  b_compressible_feature_bound universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec

#print axioms restricted_longer_feature
#print axioms restricted_minimum_is_not_unrestricted
#print axioms arbitrary_nonintegral_ratio_sources
#print axioms canonical_ratio_bounds

end Mettapedia.Examples.Compression.FeatureCompressionRatioControls
