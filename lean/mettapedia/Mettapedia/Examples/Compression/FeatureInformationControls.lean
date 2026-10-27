import Mettapedia.Computability.KolmogorovComplexity.FeatureJointInformation

/-!
# Uniform feature-information controls

The canonical source interpreter and prefix reference host satisfy the actual
machine premises. A fixed duplication program gives arbitrarily large
compressible sources, so the shortest-feature family is not empty. Negative
controls retain the shortest-feature and uniform-constant boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureInformationControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open scoped Classical

/-- A single real compressor for arbitrarily long repeated blocks. -/
def duplicate : ConditionalAlgorithm := fun program _ => Part.some (program ++ program)

theorem duplicate_effective : Partrec₂ duplicate :=
  (Primrec.list_append.comp Primrec.fst Primrec.fst).to_comp.partrec

theorem arbitrarily_large_shortest_sources :
    ∀ bound : Nat, ∃ source feature,
      bound < source.length ∧ ShortestFeature universalConditionalAlgorithm feature source := by
  obtain ⟨compiler, compiles⟩ := universalConditionalAlgorithm_isUniversal duplicate duplicate_effective
  intro bound
  let payload : BinString := List.replicate (bound + compiler.length + 1) false
  let source := payload ++ payload
  have computes : source ∈ universalConditionalAlgorithm (compiler ++ payload) [] :=
    compiles payload [] source (by simp [duplicate, source])
  have length := plainConditionalComplexity_le_of_program universalConditionalAlgorithm [] source _ computes
  have compressible : plainConditionalComplexity universalConditionalAlgorithm source [] < source.length := by
    simp only [List.length_append, List.length_replicate, payload, source] at length ⊢
    omega
  obtain ⟨step, _, _⟩ := singleton_of_compressible universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal source compressible
  obtain ⟨feature, shortest⟩ := exists_shortest_feature universalConditionalAlgorithm source ⟨_, step_feature step⟩
  refine ⟨source, feature, ?_, shortest⟩
  simp only [source, payload, List.length_append, List.length_replicate]
  omega

theorem canonical_feature_incompressibility :
    ∃ lower upper : Nat, ∀ source feature,
      ShortestFeature universalConditionalAlgorithm feature source →
        feature.length ≤ conditionalComplexity trimmedIndexedHost feature [] + lower ∧
        conditionalComplexity trimmedIndexedHost feature [] ≤
          feature.length + 2 * Nat.log 2 (feature.length + 1) + upper :=
  reference_feature_incompressibility universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost

theorem canonical_feature_information :
    ∃ overhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature universalConditionalAlgorithm shortest source →
      residual ∈ universalConditionalAlgorithm descriptive source →
      source ∈ universalConditionalAlgorithm feature residual →
      feature.length + residual.length < source.length →
      conditionalComplexity trimmedIndexedHost feature [] ≤
        (feature.length - shortest.length) + conditionalComplexity trimmedIndexedHost feature residual +
          2 * Nat.log 2 (feature.length + 1) + overhead :=
  reference_feature_information universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost

theorem canonical_shortest_independence :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature universalConditionalAlgorithm feature source →
      residual ∈ universalConditionalAlgorithm descriptive source →
      source ∈ universalConditionalAlgorithm feature residual →
      feature.length + residual.length < source.length →
      |((conditionalComplexity trimmedIndexedHost feature [] : Int) - conditionalComplexity trimmedIndexedHost feature residual)| ≤
        (2 * Nat.log 2 (feature.length + 1) + overhead : Nat) :=
  reference_shortest_independence universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost

theorem canonical_joint_information :
    ∃ overhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature universalConditionalAlgorithm shortest source →
      residual ∈ universalConditionalAlgorithm descriptive source →
      source ∈ universalConditionalAlgorithm feature residual →
      feature.length + residual.length < source.length →
      conditionalComplexity trimmedIndexedHost residual [] + conditionalComplexity trimmedIndexedHost feature [] ≤
        conditionalComplexity trimmedIndexedHost (pairCondition residual feature) [] + (feature.length - shortest.length) +
          2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead :=
  reference_feature_joint_information universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_paper_joint_information :
    ∃ overhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature universalConditionalAlgorithm shortest source →
      residual ∈ universalConditionalAlgorithm descriptive source →
      source ∈ universalConditionalAlgorithm feature residual →
      feature.length + residual.length < source.length →
      conditionalComplexity trimmedIndexedHost feature [] + conditionalComplexity trimmedIndexedHost residual [] ≤
        conditionalComplexity trimmedIndexedHost (pairCondition feature residual) [] + (feature.length - shortest.length) +
          2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead :=
  reference_feature_first_joint_information universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_residual_independence :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature universalConditionalAlgorithm feature source →
      residual ∈ universalConditionalAlgorithm descriptive source →
      source ∈ universalConditionalAlgorithm feature residual →
      feature.length + residual.length < source.length →
      |((conditionalComplexity trimmedIndexedHost residual [] : Int) - conditionalComplexity trimmedIndexedHost residual feature)| ≤
        (2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead : Nat) :=
  reference_residual_independence universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_joint_independence :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature universalConditionalAlgorithm feature source →
      residual ∈ universalConditionalAlgorithm descriptive source →
      source ∈ universalConditionalAlgorithm feature residual →
      feature.length + residual.length < source.length →
      |((conditionalComplexity trimmedIndexedHost (pairCondition feature residual) [] : Int) -
          (conditionalComplexity trimmedIndexedHost feature [] + conditionalComplexity trimmedIndexedHost residual []))| ≤
        (2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead : Nat) :=
  reference_feature_first_joint_independence universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

/-- The completed machine premises and an inhabited family hold together. -/
theorem nonvacuous_canonical_bounds : ∃ lower upper : Nat,
    (∀ source feature, ShortestFeature universalConditionalAlgorithm feature source →
      feature.length ≤ conditionalComplexity trimmedIndexedHost feature [] + lower ∧
      conditionalComplexity trimmedIndexedHost feature [] ≤ feature.length + 2 * Nat.log 2 (feature.length + 1) + upper) ∧
    (∀ bound : Nat, ∃ source feature,
      bound < source.length ∧ ShortestFeature universalConditionalAlgorithm feature source) := by
  obtain ⟨lower, upper, bounds⟩ := canonical_feature_incompressibility
  exact ⟨lower, upper, bounds, arbitrarily_large_shortest_sources⟩

theorem strict_acceptance_does_not_supply_minimality :
    ∃ (U : ConditionalAlgorithm) (source : BinString) (step : CompressionStep U source),
      ¬ ShortestFeature U step.featureProgram source := strict_step_not_necessarily_shortest

theorem pointwise_constants_do_not_supply_uniformity :
    (∀ i : Nat, ∃ multiplier constant : Nat,
      i ≤ 0 + multiplier * Nat.log 2 (0 + 1) + constant) ∧
    ¬ UniformLogarithmicUpperBound (fun i : Nat => i) (fun _ => 0) (fun _ => 0) :=
  pointwiseLogarithmicBounds_do_not_imply_uniform

theorem no_prefix_reference_from_singleton_output : ¬ IsReferenceMachine fixedEmptyMachine := by
  intro reference
  obtain ⟨program, runs⟩ := reference.hasProgram [] [true]
  simp [IsProgram, fixedEmptyMachine] at runs

#print axioms arbitrarily_large_shortest_sources
#print axioms canonical_feature_incompressibility
#print axioms canonical_feature_information
#print axioms canonical_shortest_independence
#print axioms canonical_joint_information
#print axioms canonical_paper_joint_information
#print axioms canonical_residual_independence
#print axioms canonical_joint_independence
#print axioms nonvacuous_canonical_bounds
#print axioms strict_acceptance_does_not_supply_minimality
#print axioms pointwise_constants_do_not_supply_uniformity

end Mettapedia.Examples.Compression.FeatureInformationControls
