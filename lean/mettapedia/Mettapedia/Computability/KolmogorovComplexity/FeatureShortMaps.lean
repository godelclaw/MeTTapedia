import Mettapedia.Computability.KolmogorovComplexity.FeatureDecompositionInformation
import Mettapedia.Computability.KolmogorovComplexity.FeatureCompressionRatio

/-!
# Short descriptive maps from bounded features

Franz, Antonenko and Soletskyi, "A theory of incremental compression",
Information Sciences 547 (2021), Theorem 3.8,
https://doi.org/10.1016/j.ins.2020.08.035 (arXiv:1908.03781).

Compile the existing effective residual search with the feature as its program
payload. The compiler is fixed before every feature, source and length budget.
This gives a plain descriptive-map bound linear in feature length, and hence a
source-independent constant when the feature length is bounded. The selected
residual is not an arbitrarily prescribed reconstruction witness.

These are unrestricted descriptive maps. A ratio-restricted map must retain
its extra residual condition; minimum b-features do not erase that distinction.
Plain and prefix complexities are kept separate throughout.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

/-- One compiled search supplies a descriptive map for every feature. Its
complete program is the fixed compiler prefix followed by that feature. -/
theorem residual_search_descriptive_compiler (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ compiler : BinString, ∀ feature source, Feature U feature source →
      DescriptiveMap U feature (compiler ++ feature) source := by
  obtain ⟨code, codeSpec⟩ := exists_conditional_algorithm_code effective
  obtain ⟨compiler, compiles⟩ := universal (residualSearch code) (residualSearch_partrec code)
  refine ⟨compiler, fun feature source present => ?_⟩
  obtain ⟨descriptive, residual, _, reconstructs, smaller⟩ := present
  obtain ⟨selected, finds⟩ := residualSearch_complete codeSpec reconstructs smaller
  have sound := residualSearch_sound codeSpec finds
  exact ⟨selected, compiles feature source selected finds, sound.1, sound.2⟩

theorem shortest_descriptive_linear_in_feature (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ feature descriptive source,
      ShortestDescriptiveMap U feature descriptive source →
      descriptive.length ≤ feature.length + overhead := by
  obtain ⟨compiler, compiles⟩ := residual_search_descriptive_compiler U universal effective
  refine ⟨compiler.length, fun feature descriptive source minimum => ?_⟩
  have competitor := compiles feature source ⟨descriptive, minimum.1⟩
  have bound := minimum.2 (compiler ++ feature) competitor
  simpa only [List.length_append, Nat.add_comm] using bound

/-- Determinacy of the partial algorithm identifies the actual selected
residual with the witness in the descriptive-map declaration. -/
theorem shortest_descriptive_actual_output {U : ConditionalAlgorithm}
    {feature descriptive source residual : BinString}
    (minimum : ShortestDescriptiveMap U feature descriptive source)
    (selected : residual ∈ U descriptive source) :
    source ∈ U feature residual ∧ feature.length + residual.length < source.length ∧
      descriptive.length = plainConditionalComplexity U residual source := by
  obtain ⟨witness, extracts, reconstructs, smaller⟩ := minimum.1
  have same : witness = residual := Part.mem_unique extracts selected
  subst witness
  exact ⟨reconstructs, smaller, shortest_descriptive_conditional minimum selected reconstructs smaller⟩

/-- IC Theorem 3.8: a genuine compiled competing map and the minimum map
both have a source-independent bound for every fixed feature-length budget. -/
theorem short_feature_descriptive_bounds (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ budget feature source,
      Feature U feature source → feature.length ≤ budget →
      (∃ descriptive residual, DescriptiveMap U feature descriptive source ∧
        residual ∈ U descriptive source ∧ source ∈ U feature residual ∧
        feature.length + residual.length < source.length ∧
        plainConditionalComplexity U residual source ≤ descriptive.length ∧
        descriptive.length ≤ budget + overhead) ∧
      (∀ descriptive residual, ShortestDescriptiveMap U feature descriptive source →
        residual ∈ U descriptive source →
        descriptive.length = plainConditionalComplexity U residual source ∧
        descriptive.length ≤ budget + overhead) := by
  obtain ⟨compiler, compiles⟩ := residual_search_descriptive_compiler U universal effective
  refine ⟨compiler.length, fun budget feature source present bounded => ?_⟩
  have admitted := compiles feature source present
  obtain ⟨residual, extracts, reconstructs, smaller⟩ := admitted
  constructor
  · refine ⟨compiler ++ feature, residual, ⟨residual, extracts, reconstructs, smaller⟩,
      extracts, reconstructs, smaller, plainConditionalComplexity_le_of_program U source residual _ extracts, ?_⟩
    simp only [List.length_append]
    omega
  · intro descriptive actual minimum selected
    have correct := shortest_descriptive_actual_output minimum selected
    have least := minimum.2 (compiler ++ feature) ⟨residual, extracts, reconstructs, smaller⟩
    simp only [List.length_append] at least
    exact ⟨correct.2.2, by omega⟩

theorem short_feature_prefix_residual (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ mapOverhead prefixOverhead : Nat, ∀ budget feature descriptive source residual,
      feature.length ≤ budget → ShortestDescriptiveMap U feature descriptive source →
      residual ∈ U descriptive source →
      conditionalComplexity V residual source ≤ budget + mapOverhead +
        2 * Nat.log 2 (budget + mapOverhead + 1) + prefixOverhead := by
  obtain ⟨mapOverhead, maps⟩ := shortest_descriptive_linear_in_feature U universal effective
  obtain ⟨prefixOverhead, description⟩ := reference_program_description U V effective reference
  refine ⟨mapOverhead, prefixOverhead, fun budget feature descriptive source residual bounded minimum selected => ?_⟩
  have length := maps feature descriptive source minimum
  have logarithm := Nat.log_mono_right (b := 2)
    (show descriptive.length + 1 ≤ budget + mapOverhead + 1 by omega)
  have prefixBound := description descriptive source residual selected
  omega

/-- Fixing b fixes a natural feature-length budget, uniformly over sources.
The corresponding maps below are still unrestricted minimum descriptive maps. -/
theorem b_compressible_shortest_maps_constant (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∀ factor : ℝ, 1 < factor → ∃ featureBudget mapBudget : Nat, ∀ feature descriptive source residual,
      factor * plainConditionalComplexity U source [] ≤ source.length →
      (ShortestFeature U feature source ∨ ShortestBFeature U factor feature source) →
      ShortestDescriptiveMap U feature descriptive source → residual ∈ U descriptive source →
      feature.length ≤ featureBudget ∧ descriptive.length ≤ mapBudget ∧
        descriptive.length = plainConditionalComplexity U residual source := by
  obtain ⟨fixed, featureBounds⟩ := b_compressible_feature_bound U universal effective
  obtain ⟨overhead, mapBounds⟩ := shortest_descriptive_linear_in_feature U universal effective
  intro factor greater
  let budget : Nat := ⌈max (fixed.length : ℝ) (fixed.length / (factor - 1))⌉₊
  refine ⟨budget, budget + overhead, fun feature descriptive source residual compression shortest minimum selected => ?_⟩
  have bounds := featureBounds factor greater source compression
  have lengthReal : (feature.length : ℝ) ≤ max (fixed.length : ℝ) (fixed.length / (factor - 1)) :=
    shortest.elim (bounds.2.1 feature) (bounds.2.2 feature)
  have ceiling : (feature.length : ℝ) ≤ budget := lengthReal.trans (Nat.le_ceil _)
  have length : feature.length ≤ budget := by exact_mod_cast ceiling
  have maps := mapBounds feature descriptive source minimum
  have correct := shortest_descriptive_actual_output minimum selected
  exact ⟨length, by omega, correct.2.2⟩

#print axioms residual_search_descriptive_compiler
#print axioms shortest_descriptive_linear_in_feature
#print axioms shortest_descriptive_actual_output
#print axioms short_feature_descriptive_bounds
#print axioms short_feature_prefix_residual
#print axioms b_compressible_shortest_maps_constant

end KolmogorovComplexity.FeatureTheory
