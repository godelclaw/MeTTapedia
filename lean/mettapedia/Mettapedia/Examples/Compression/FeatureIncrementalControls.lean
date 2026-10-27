import Mettapedia.Computability.KolmogorovComplexity.FeatureIncrementalInformation
import Mettapedia.Examples.Compression.FeatureDecompositionControls
import Mettapedia.Examples.Compression.FeatureCompressionChainControls

/-!
# Incremental shortest-feature controls

A concrete two-step chain retains minimum programs at both steps and
reconstructs its original source. Canonical-machine controls instantiate the
uniform information theorem on an unbounded nonempty family of sources.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureIncrementalControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open FeatureCompressionChainControls
open scoped Classical

theorem one_bit_feature_minimum {input : BinString}
    (present : Feature twoStage [false] input) : ShortestFeature twoStage [false] input := by
  refine ⟨present, fun other admitted => ?_⟩
  cases other with
  | nil =>
      obtain ⟨descriptive, residual, _, reconstructs, _⟩ := admitted
      simp [twoStage] at reconstructs
  | cons bit rest => simp

theorem one_bit_map_minimum {input feature : BinString}
    (present : DescriptiveMap twoStage feature [true] input) :
    ShortestDescriptiveMap twoStage feature [true] input := by
  refine ⟨present, fun other admitted => ?_⟩
  cases other with
  | nil =>
      obtain ⟨residual, extracts, _, _⟩ := admitted
      simp [twoStage] at extracts
  | cons bit rest => simp

theorem first_map : DescriptiveMap twoStage [false] [true] eight := by
  exact ⟨fourTrue, by simp [twoStage, eight, fourTrue], by simp [twoStage, eight, fourTrue], by simp [eight, fourTrue]⟩

theorem second_map : DescriptiveMap twoStage [false] [true] fourTrue := by
  exact ⟨[], by simp [twoStage, eight, fourTrue], by simp [twoStage], by simp [fourTrue]⟩

theorem concrete_shortest_chain : ShortestChain twoStage eight [[false], [false]] [] := by
  apply ShortestChain.cons (descriptive := [true]) (residual := fourTrue)
    (one_bit_feature_minimum ⟨[true], first_map⟩) (one_bit_map_minimum first_map)
  · simp [twoStage, eight, fourTrue]
  · simp [twoStage, eight, fourTrue]
  · simp [eight, fourTrue]
  · apply ShortestChain.cons (descriptive := [true]) (residual := [])
      (one_bit_feature_minimum ⟨[true], second_map⟩) (one_bit_map_minimum second_map)
    · simp [twoStage, eight, fourTrue]
    · simp [twoStage]
    · simp [fourTrue]
    · exact .nil []

theorem concrete_reconstruction : eight ∈ restoreFeatures twoStage [[false], [false]] [] :=
  concrete_shortest_chain.reconstruct

theorem invalid_feature_refused : ¬ ShortestChain twoStage eight [[]] [] := by
  intro alleged
  cases alleged with
  | cons minimal _ _ _ _ _ =>
      obtain ⟨descriptive, residual, _, reconstructs, _⟩ := minimal.1
      simp [twoStage] at reconstructs

theorem canonical_incremental_bound :
    ∃ overhead : Nat, ∀ source features final, ShortestChain universalConditionalAlgorithm source features final →
      |((conditionalComplexity trimmedIndexedHost source [] : Int) -
        ((features.map List.length).sum + conditionalComplexity trimmedIndexedHost final []))| ≤
          (features.length * (20 * Nat.log 2 (source.length + 1) + overhead) : Nat) :=
  incremental_information_bound universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem unbounded_nonempty_chains :
    ∃ overhead : Nat, ∀ size : Nat, ∃ source feature residual,
      size < source.length ∧ ShortestChain universalConditionalAlgorithm source [feature] residual ∧
      |((conditionalComplexity trimmedIndexedHost source [] : Int) -
        (feature.length + conditionalComplexity trimmedIndexedHost residual []))| ≤
          (20 * Nat.log 2 (source.length + 1) + overhead : Nat) := by
  obtain ⟨overhead, bound⟩ := canonical_incremental_bound
  refine ⟨overhead, fun size => ?_⟩
  obtain ⟨source, feature, large, minimal⟩ := FeatureInformationControls.arbitrarily_large_shortest_sources size
  obtain ⟨descriptive, minimalMap⟩ := exists_shortest_descriptive universalConditionalAlgorithm feature source minimal.1
  obtain ⟨residual, extracts, reconstructs, smaller⟩ := minimalMap.1
  have chain : ShortestChain universalConditionalAlgorithm source [feature] residual :=
    .cons minimal minimalMap extracts reconstructs smaller (.nil residual)
  exact ⟨source, feature, residual, large, chain, by simpa using bound source [feature] residual chain⟩

#print axioms concrete_shortest_chain
#print axioms concrete_reconstruction
#print axioms invalid_feature_refused
#print axioms canonical_incremental_bound
#print axioms unbounded_nonempty_chains

end Mettapedia.Examples.Compression.FeatureIncrementalControls
