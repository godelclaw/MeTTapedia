import Mettapedia.Computability.KolmogorovComplexity.FeatureOrthogonality
import Mettapedia.Computability.KolmogorovComplexity.DirectionalInformation
import Mettapedia.Computability.KolmogorovComplexity.LogarithmicBounds
import Mettapedia.Examples.Compression.FeatureIncrementalControls

/-!
# Orthogonality controls on the shared machines and chain representation

Canonical-machine corollaries discharge reference-machine and compiler
premises. A genuine finite two-stage shortest chain tests positional splitting;
it is not substituted for a universal interpreter in the information theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureOrthogonalityControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open ConditionalInformationTransport
open FeatureCompressionChainControls

theorem canonical_data_processing :
    ∃ overhead : Nat, ∀ source intermediate target,
      directedAlgorithmicInformation trimmedIndexedHost source target ≤
        directedAlgorithmicInformation trimmedIndexedHost source intermediate +
          conditionalComplexity trimmedIndexedHost target intermediate +
          (2 * Nat.log 2 (target.length + 1) + overhead : Nat) :=
  information_data_processing trimmedIndexedHost isReferenceMachine_trimmedIndexedHost
    KraftChaitin.trimmedIndexedHostStrongConditionalChainRule trimmedReferenceMachineSimulations

theorem canonical_orthogonality :
    ∃ overhead : Nat, ∀ source features final, ShortestChain universalConditionalAlgorithm source features final →
      ∀ i j (hi : i < features.length) (hj : j < features.length), i ≠ j →
        |directedAlgorithmicInformation trimmedIndexedHost features[i] features[j]| ≤
          (Nat.dist i j * (20 * Nat.log 2 (source.length + 1) + overhead) : Nat) :=
  shortest_chain_orthogonality universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem finite_two_stage_split :
    ∃ residual, ShortestChain twoStage eight [[false]] residual ∧
      ShortestChain twoStage residual [[false]] [] :=
  ShortestChain.split FeatureIncrementalControls.concrete_shortest_chain

theorem finite_later_feature_length : ([false] : BinString).length ≤ eight.length :=
  ShortestChain.feature_length_le (pre := [[false]]) (suffix := [])
    FeatureIncrementalControls.concrete_shortest_chain

theorem adjacent_distance_is_one : Nat.dist 0 1 = 1 := by decide

theorem reversing_positions_preserves_distance (i j : Nat) : Nat.dist i j = Nat.dist j i :=
  Nat.dist_comm i j

/-- The nonreference canary distinguishes directions exactly; the uniform
reference theorem pays its symmetry budget instead of identifying them. -/
theorem directional_information_is_not_definitionally_symmetric :
    directedAlgorithmicInformation DirectionalInformationCanary.machine
      DirectionalInformationCanary.model DirectionalInformationCanary.parameter = 0 ∧
    directedAlgorithmicInformation DirectionalInformationCanary.machine
      DirectionalInformationCanary.parameter DirectionalInformationCanary.model = 1 :=
  ⟨DirectionalInformationCanary.model_about_parameter_zero,
    DirectionalInformationCanary.parameter_about_model_one⟩

#print axioms FeatureTheory.remove_complexity_index
#print axioms FeatureTheory.swapPairMachine_effective
#print axioms FeatureTheory.reference_pair_swap
#print axioms joint_chain_upper
#print axioms conditional_triangle
#print axioms complexity_header_bound
#print axioms joint_chain_lower
#print axioms ordered_information_bound
#print axioms information_symmetry_uniform
#print axioms information_data_processing
#print axioms ShortestChain.split
#print axioms ShortestChain.feature_length_le
#print axioms later_feature_description
#print axioms shortest_chain_pairwise_information
#print axioms shortest_chain_orthogonality
#print axioms canonical_data_processing
#print axioms canonical_orthogonality
#print axioms finite_two_stage_split
#print axioms finite_later_feature_length
#print axioms adjacent_distance_is_one
#print axioms reversing_positions_preserves_distance
#print axioms directional_information_is_not_definitionally_symmetric
#print axioms pointwiseLogarithmicBounds_do_not_imply_uniform

end Mettapedia.Examples.Compression.FeatureOrthogonalityControls
