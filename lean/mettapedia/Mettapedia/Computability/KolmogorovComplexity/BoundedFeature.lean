import Mettapedia.Computability.KolmogorovComplexity.FeatureCompressionRatio
import Mettapedia.Computability.KolmogorovComplexity.FeaturePrefixInformation
import Mettapedia.Computability.KolmogorovComplexity.FeatureIncompressibility

/-!
# Bounded-feature information and machine correspondences

All definitions of residual-bounded features come from FeatureCompressionRatio.
This module connects their minimum programs to prefix observations and retains
the residual bound when comparing competing reconstruction programs.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

theorem shortest_b_maps_prefix (U : ConditionalPrefixFreeMachine) (factor : ℝ)
    {feature descriptive source : BinString}
    (shortestFeature : ShortestBFeature (prefixAlgorithm U) factor feature source)
    (shortestDescriptive : ShortestBDescriptiveMap (prefixAlgorithm U) factor feature descriptive source) :
    ∃ residual, IsProgram U descriptive source residual ∧ IsProgram U feature residual source ∧
      factor * residual.length ≤ source.length ∧
      feature.length = conditionalComplexity U source residual ∧
      descriptive.length = conditionalComplexity U residual source := by
  obtain ⟨residual,extracts,reconstructs,smaller,bounded⟩ := shortestDescriptive.1
  exact ⟨residual,(prefixAlgorithm_runs ..).mp extracts,(prefixAlgorithm_runs ..).mp reconstructs,bounded,
    (shortest_b_feature_conditional shortestFeature extracts reconstructs smaller bounded).trans
      (prefix_complexity_agrees ..),
    (shortest_b_descriptive_conditional shortestDescriptive extracts reconstructs smaller bounded).trans
      (prefix_complexity_agrees ..)⟩

theorem shortest_b_feature_plain_lower (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (computable : Partrec₂ U) :
    ∃ overhead : Nat, ∀ factor feature source,
      ShortestBFeature U factor feature source →
        feature.length ≤ plainConditionalComplexity U feature [] + overhead := by
  obtain ⟨compiler,compiles⟩ := universal _ (decodeFeatureThenRun_partrec U computable)
  refine ⟨compiler.length,fun factor feature source shortest => ?_⟩
  obtain ⟨descriptive,residual,extracts,reconstructs,smaller,bounded⟩ := shortest.1
  obtain ⟨program,decodes,minimal⟩ := exists_program_of_plainConditionalComplexity U [] feature
    (universalConditional_hasProgram U universal [] feature)
  have compiled := compiles program residual source (Part.mem_bind decodes reconstructs)
  by_cases short : (compiler ++ program).length ≤ feature.length
  · have competitor : BFeature U factor (compiler ++ program) source :=
      ⟨descriptive,residual,extracts,compiled,by omega,bounded⟩
    have least := shortest.2 (compiler ++ program) competitor
    simpa only [List.length_append,minimal,Nat.add_comm] using least
  · simp only [List.length_append,minimal] at short
    omega


/-- This is the exact arithmetic bridge to the natural-factor residual
condition used by the independent development. No machine identification is
implied by an arithmetic correspondence. -/
theorem natural_factor_residual_iff (factor : Nat) (positive : 0 < factor)
    (residual source : BinString) :
    (factor : ℝ) * residual.length ≤ source.length ↔
      residual.length ≤ source.length / factor := by
  rw [Nat.le_div_iff_mul_le positive]
  constructor
  · intro bounded
    have product : factor * residual.length ≤ source.length := by exact_mod_cast bounded
    simpa [Nat.mul_comm] using product
  · intro bounded
    have product : factor * residual.length ≤ source.length := by simpa [Nat.mul_comm] using bounded
    exact_mod_cast product

/-- Each genuinely compressing competing b-feature supplies the same bounded
residual when its program is replaced by the minimum reconstruction program. -/
theorem shortest_b_le_residual_complexity {U : ConditionalAlgorithm} {factor : ℝ}
    {shortest feature descriptive source residual : BinString}
    (minimal : ShortestBFeature U factor shortest source)
    (extracts : residual ∈ U descriptive source) (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length)
    (bounded : factor * residual.length ≤ source.length) :
    shortest.length ≤ plainConditionalComplexity U source residual := by
  obtain ⟨program,runs,length⟩ := exists_program_of_plainConditionalComplexity U residual source ⟨feature,reconstructs⟩
  have upper := plainConditionalComplexity_le_of_program U residual source feature reconstructs
  have competitor : BFeature U factor program source :=
    ⟨descriptive,residual,extracts,runs,by omega,bounded⟩
  simpa only [length] using minimal.2 program competitor

/-- The information bound applies to shortest b-features without assuming
that they are unrestricted shortest features. All constants precede b and the
source, feature, map and residual. -/
theorem reference_b_feature_information (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ factor shortest feature descriptive source residual,
      ShortestBFeature U factor shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      factor * residual.length ≤ source.length →
      conditionalComplexity V feature [] ≤
        (feature.length - shortest.length) + conditionalComplexity V feature residual +
          2 * Nat.log 2 (feature.length + 1) + overhead := by
  obtain ⟨evaluation,evalBound⟩ := uniform_prefix_evaluation U V universal effective reference
  obtain ⟨literal,literalBound⟩ := reference_literal_bound U V universal effective reference
  refine ⟨evaluation + literal,fun factor shortest feature descriptive source residual minimal extracts reconstructs smaller bounded => ?_⟩
  have residualBound := shortest_b_le_residual_complexity minimal extracts reconstructs smaller bounded
  have minimumBound := minimal.2 feature ⟨descriptive,residual,extracts,reconstructs,smaller,bounded⟩
  have evaluated := evalBound feature residual source reconstructs
  have literal := literalBound feature []
  omega

end KolmogorovComplexity.FeatureTheory
