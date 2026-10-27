import Mettapedia.Computability.KolmogorovComplexity.FeatureSourceInformation
import Mettapedia.Examples.Compression.FeatureInformationControls

/-!
# Source-conditional feature bounds on actual reference machines

The positive controls discharge every interpreter and chain-rule premise.
The negative control shows why missing outputs, whose minimum functional
defaults to zero, cannot be counted as zero-bit descriptions.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureSourceInformationControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open scoped Classical

theorem canonical_source_bound :
    ∃ overhead : Nat, ∀ source feature, ShortestFeature universalConditionalAlgorithm feature source →
      conditionalComplexity trimmedIndexedHost feature source ≤
        6 * Nat.log 2 (source.length + 1) + overhead :=
  reference_shortest_feature_source_bound universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_polynomial_count :
    ∃ coefficient : Nat, ∀ source (features : Finset BinString),
      (∀ feature ∈ features, ShortestFeature universalConditionalAlgorithm feature source) →
      features.card < coefficient * (source.length + 1) ^ 6 :=
  shortest_feature_polynomial_count universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem nonvacuous_source_bound :
    ∃ overhead : Nat, ∀ size : Nat, ∃ source feature,
      size < source.length ∧ ShortestFeature universalConditionalAlgorithm feature source ∧
      conditionalComplexity trimmedIndexedHost feature source ≤
        6 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨overhead, bound⟩ := canonical_source_bound
  refine ⟨overhead, fun size => ?_⟩
  obtain ⟨source, feature, large, shortest⟩ :=
    FeatureInformationControls.arbitrarily_large_shortest_sources size
  exact ⟨source, feature, large, shortest, bound source feature shortest⟩

theorem missing_outputs_break_counting :
    (∀ output ∈ ({[false], [true]} : Finset BinString),
      conditionalComplexity fixedEmptyMachine output [] = 0) ∧
    ¬ ({[false], [true]} : Finset BinString).card < 2 ^ (0 + 1) := by
  constructor
  · intro output member
    apply conditionalComplexity_eq_zero_of_not_hasProgram
    rintro ⟨program, runs⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> simp [IsProgram, fixedEmptyMachine] at runs
  · decide

#print axioms canonical_source_bound
#print axioms canonical_polynomial_count
#print axioms nonvacuous_source_bound
#print axioms missing_outputs_break_counting

end Mettapedia.Examples.Compression.FeatureSourceInformationControls
