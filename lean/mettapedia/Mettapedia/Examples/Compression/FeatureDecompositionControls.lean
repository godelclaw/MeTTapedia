import Mettapedia.Computability.KolmogorovComplexity.FeatureDecompositionInformation
import Mettapedia.Examples.Compression.FeatureSourceInformationControls

/-!
# Selected-residual and information-partition controls

An actual partial algorithm diverges on the empty residual but succeeds on
nonempty residuals. Rank search reaches a later successful computation. The
canonical universal interpreters instantiate the uniform information bounds.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureDecompositionControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open scoped Classical

def source : BinString := List.replicate 8 true

def waitingAlgorithm : ConditionalAlgorithm :=
  fun _ residual => if residual = [] then Part.none else Part.some source

theorem waitingAlgorithm_partrec : Partrec₂ waitingAlgorithm := by
  have empty : Computable fun input : BinString × BinString => decide (input.2 = []) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const [])).decide.to_comp
  exact (Partrec.cond empty Partrec.none (Partrec.const' (Part.some source))).of_eq fun input => by
    by_cases h : input.2 = [] <;> simp [waitingAlgorithm, h]

noncomputable def waitingCode : Nat.Partrec.Code :=
  Classical.choose (exists_conditional_algorithm_code waitingAlgorithm_partrec)

theorem waitingCode_spec : Nat.Partrec.Code.eval waitingCode = encodedConditionalAlgorithm waitingAlgorithm :=
  Classical.choose_spec (exists_conditional_algorithm_code waitingAlgorithm_partrec)

theorem empty_candidate_diverges : waitingAlgorithm [] [] = Part.none := by
  simp [waitingAlgorithm]

theorem search_reaches_later_success :
    ∃ residual, residual ∈ residualSearch waitingCode [] source ∧ residual ≠ [] ∧ residual.length < source.length := by
  obtain ⟨residual, selected⟩ := residualSearch_complete waitingCode_spec
    (feature := []) (residual := [false]) (source := source) (by simp [waitingAlgorithm]) (by simp [source])
  have correct := residualSearch_sound waitingCode_spec selected
  refine ⟨residual, selected, ?_, by simpa using correct.2⟩
  intro empty
  simp [waitingAlgorithm, empty] at correct

theorem no_fabricated_saving : ¬ ∃ residual, residual ∈ residualSearch waitingCode source source := by
  rintro ⟨residual, selected⟩
  have correct := residualSearch_sound waitingCode_spec selected
  omega

theorem canonical_descriptive_bound :
    ∃ overhead : Nat, ∀ feature descriptive input,
      ShortestFeature universalConditionalAlgorithm feature input →
      ShortestDescriptiveMap universalConditionalAlgorithm feature descriptive input →
      descriptive.length ≤ 6 * Nat.log 2 (input.length + 1) + overhead :=
  shortest_descriptive_logarithmic universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_no_superfluous_information :
    ∃ overhead : Nat, ∀ feature descriptive input residual,
      ShortestFeature universalConditionalAlgorithm feature input →
      ShortestDescriptiveMap universalConditionalAlgorithm feature descriptive input →
      residual ∈ universalConditionalAlgorithm descriptive input →
      conditionalComplexity trimmedIndexedHost (pairCondition feature residual) input ≤
        14 * Nat.log 2 (input.length + 1) + overhead :=
  shortest_maps_no_superfluous_information universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_information_partition :
    ∃ overhead : Nat, ∀ feature descriptive input residual,
      ShortestFeature universalConditionalAlgorithm feature input →
      ShortestDescriptiveMap universalConditionalAlgorithm feature descriptive input →
      residual ∈ universalConditionalAlgorithm descriptive input → input ∈ universalConditionalAlgorithm feature residual →
      feature.length + residual.length < input.length →
      |((conditionalComplexity trimmedIndexedHost input [] : Int) -
        (conditionalComplexity trimmedIndexedHost feature [] + conditionalComplexity trimmedIndexedHost residual []))| ≤
          (18 * Nat.log 2 (input.length + 1) + overhead : Nat) :=
  shortest_maps_information_partition universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem unbounded_selected_decompositions :
    ∃ overhead : Nat, ∀ size : Nat, ∃ input feature descriptive residual,
      size < input.length ∧ ShortestFeature universalConditionalAlgorithm feature input ∧
      ShortestDescriptiveMap universalConditionalAlgorithm feature descriptive input ∧
      residual ∈ universalConditionalAlgorithm descriptive input ∧ input ∈ universalConditionalAlgorithm feature residual ∧
      feature.length + residual.length < input.length ∧
      conditionalComplexity trimmedIndexedHost (pairCondition feature residual) input ≤
        14 * Nat.log 2 (input.length + 1) + overhead := by
  obtain ⟨overhead, bound⟩ := canonical_no_superfluous_information
  refine ⟨overhead, fun size => ?_⟩
  obtain ⟨input, feature, large, shortest⟩ := FeatureInformationControls.arbitrarily_large_shortest_sources size
  obtain ⟨descriptive, shortestMap⟩ := exists_shortest_descriptive universalConditionalAlgorithm feature input shortest.1
  obtain ⟨residual, extracts, reconstructs, smaller⟩ := shortestMap.1
  exact ⟨input, feature, descriptive, residual, large, shortest, shortestMap, extracts, reconstructs, smaller,
    bound feature descriptive input residual shortest shortestMap extracts⟩

#print axioms search_reaches_later_success
#print axioms no_fabricated_saving
#print axioms canonical_descriptive_bound
#print axioms canonical_no_superfluous_information
#print axioms canonical_information_partition
#print axioms unbounded_selected_decompositions

end Mettapedia.Examples.Compression.FeatureDecompositionControls
