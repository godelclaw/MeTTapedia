import Mettapedia.Computability.KolmogorovComplexity.FeatureShortMaps
import Mettapedia.Examples.Compression.FeatureInformationControls

/-! Actual universal-machine instances of the short-map theorem. A fixed
feature works for arbitrarily long sources, so the constant bound is not a
finite-source or empty-instance statement. -/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureShortMapsControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open scoped Classical

theorem canonical_linear_map_bound :
    ∃ overhead : Nat, ∀ feature descriptive source,
      ShortestDescriptiveMap universalConditionalAlgorithm feature descriptive source →
      descriptive.length ≤ feature.length + overhead :=
  shortest_descriptive_linear_in_feature universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec

theorem canonical_b_compressible_maps :
    ∀ factor : ℝ, 1 < factor → ∃ featureBudget mapBudget : Nat, ∀ feature descriptive source residual,
      factor * plainConditionalComplexity universalConditionalAlgorithm source [] ≤ source.length →
      (ShortestFeature universalConditionalAlgorithm feature source ∨
        ShortestBFeature universalConditionalAlgorithm factor feature source) →
      ShortestDescriptiveMap universalConditionalAlgorithm feature descriptive source →
      residual ∈ universalConditionalAlgorithm descriptive source →
      feature.length ≤ featureBudget ∧ descriptive.length ≤ mapBudget ∧
        descriptive.length = plainConditionalComplexity universalConditionalAlgorithm residual source :=
  b_compressible_shortest_maps_constant universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec

theorem fixed_feature_arbitrarily_large_sources :
    ∃ feature : BinString, ∃ mapBudget : Nat, ∀ size : Nat,
      ∃ source descriptive residual,
        size < source.length ∧ ShortestDescriptiveMap universalConditionalAlgorithm feature descriptive source ∧
        residual ∈ universalConditionalAlgorithm descriptive source ∧
        source ∈ universalConditionalAlgorithm feature residual ∧
        feature.length + residual.length < source.length ∧ descriptive.length ≤ mapBudget := by
  obtain ⟨feature, works⟩ := exists_universal_feature universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
  obtain ⟨compiler, compiles⟩ := universalConditionalAlgorithm_isUniversal
    FeatureInformationControls.duplicate FeatureInformationControls.duplicate_effective
  obtain ⟨overhead, bounds⟩ := canonical_linear_map_bound
  refine ⟨feature, feature.length + overhead, fun size => ?_⟩
  let payload : BinString := List.replicate (size + compiler.length + feature.length + 2) false
  let source := payload ++ payload
  have computes : source ∈ universalConditionalAlgorithm (compiler ++ payload) [] :=
    compiles payload [] source (by simp [FeatureInformationControls.duplicate, source])
  have complexity := plainConditionalComplexity_le_of_program universalConditionalAlgorithm [] source _ computes
  have payloadLength : payload.length = size + compiler.length + feature.length + 2 := by simp [payload]
  have margin : plainConditionalComplexity universalConditionalAlgorithm source [] + feature.length < source.length := by
    simp only [source, List.length_append] at complexity ⊢
    omega
  obtain ⟨step, same, _⟩ := works source margin
  have present : Feature universalConditionalAlgorithm feature source := by
    simpa only [same] using step_feature step
  obtain ⟨descriptive, minimum⟩ := exists_shortest_descriptive universalConditionalAlgorithm feature source present
  obtain ⟨residual, extracts, reconstructs, smaller⟩ := minimum.1
  refine ⟨source, descriptive, residual, ?_, minimum, extracts, reconstructs, smaller,
    bounds feature descriptive source minimum⟩
  simp only [source, List.length_append]
  omega

#print axioms canonical_linear_map_bound
#print axioms canonical_b_compressible_maps
#print axioms fixed_feature_arbitrarily_large_sources

end Mettapedia.Examples.Compression.FeatureShortMapsControls
