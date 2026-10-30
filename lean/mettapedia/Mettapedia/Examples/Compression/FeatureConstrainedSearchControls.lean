import Mettapedia.Computability.KolmogorovComplexity.FeatureConstrainedSearch
import Mettapedia.Examples.Compression.FeatureDecompositionControls
import Mettapedia.Examples.Compression.FeatureCompressionRatioControls

/-!
# Constraint-preserving residual controls

A shorter unrestricted map can violate a ratio that a longer map meets.
An actual partial-recursive search reaches a ratio-admitted residual even
though an earlier reconstruction computation does not terminate. Rational
factors include the nonintegral 3/2 case on the canonical universal machine.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureConstrainedSearchControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open scoped Classical

def source : BinString := List.replicate 8 true
def longResidual : BinString := List.replicate 4 true

def machine : ConditionalAlgorithm := fun program condition =>
  if program = [false] ∧ (condition = longResidual ∨ condition = []) then Part.some source
  else if program = [true] ∧ condition = source then Part.some longResidual
  else if program = [true, true] ∧ condition = source then Part.some []
  else Part.none

theorem unrestricted_map_minimum : ShortestDescriptiveMap machine [false] [true] source := by
  refine ⟨⟨longResidual, ?_, ?_, ?_⟩, ?_⟩
  · simp [machine, source, longResidual]
  · simp [machine, source, longResidual]
  · simp [source, longResidual]
  · intro other present
    obtain ⟨residual, extracts, _, _⟩ := present
    cases other with
    | nil => simp [machine] at extracts
    | cons head tail => simp

theorem unrestricted_map_violates_ratio : ¬ BDescriptiveMap machine 3 [false] [true] source := by
  rintro ⟨residual, extracts, _, _, ratio⟩
  have same : residual = longResidual := by simpa [machine, source, longResidual] using extracts
  subst residual
  norm_num [source, longResidual] at ratio

theorem constrained_map_minimum : ShortestBDescriptiveMap machine 3 [false] [true, true] source := by
  refine ⟨⟨[], ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [machine, source, longResidual]
  · simp [machine, source, longResidual]
  · simp [source]
  · norm_num [source]
  · intro other present
    obtain ⟨residual, extracts, _, _, ratio⟩ := present
    unfold machine at extracts
    split_ifs at extracts with first second third
    · simp [source, longResidual] at first
    · have same : residual = longResidual := by simpa using extracts
      subst residual
      norm_num [source, longResidual] at ratio
    · rw [third.1]
    · simp at extracts

theorem constrained_minimum_not_unrestricted :
    ¬ ShortestDescriptiveMap machine [false] [true, true] source := by
  intro minimum
  have impossible := minimum.2 [true] unrestricted_map_minimum.1
  simp at impossible

def twoCandidates (rank : Nat) : Option BinString :=
  if rank = 0 then some longResidual else if rank = 1 then some [] else none

theorem unconstrained_search_selects_first : longResidual ∈ Nat.rfindOpt twoCandidates := by
  have first : 0 ∈ Nat.rfind (fun rank => (twoCandidates rank).isSome) := by
    apply (Nat.mem_rfind (p := fun rank => Part.some (twoCandidates rank).isSome)).mpr
    exact ⟨by simp [twoCandidates], fun {earlier} impossible => by omega⟩
  exact Part.mem_bind first (by simp [twoCandidates])

/-- Rejecting the result of an already completed search throws away the
later ratio-admitted candidate, even for a finite two-answer region. -/
theorem filtering_after_selection_loses_answer :
    ((Nat.rfindOpt twoCandidates).bind fun residual => Part.ofOption
      (guardResidualCandidate (rationalResidualGuard 3 1) ([false], source) (some residual))) =
      Part.none := by
  apply Part.eq_none_iff.mpr
  intro residual possible
  obtain ⟨selected, chosen, accepted⟩ := Part.mem_bind_iff.mp possible
  have same : selected = longResidual := Part.mem_unique chosen unconstrained_search_selects_first
  subst selected
  simp [guardResidualCandidate, rationalResidualGuard, source, longResidual] at accepted

theorem filtering_candidates_reaches_second :
    ([] : BinString) ∈ Nat.rfindOpt (fun rank =>
      guardResidualCandidate (rationalResidualGuard 3 1) ([false], source) (twoCandidates rank)) := by
  have first : 1 ∈ Nat.rfind (fun rank =>
      (guardResidualCandidate (rationalResidualGuard 3 1) ([false], source) (twoCandidates rank)).isSome) := by
    apply (Nat.mem_rfind (p := fun rank => Part.some
      (guardResidualCandidate (rationalResidualGuard 3 1) ([false], source) (twoCandidates rank)).isSome)).mpr
    constructor
    · simp [twoCandidates, guardResidualCandidate, rationalResidualGuard, source]
    · intro earlier before
      have zero : earlier = 0 := by omega
      subst earlier
      simp [twoCandidates, guardResidualCandidate, rationalResidualGuard, source, longResidual]
  exact Part.mem_bind first (by simp [twoCandidates, guardResidualCandidate, rationalResidualGuard, source])

theorem rational_search_reaches_admitted_residual :
    ∃ residual, residual ∈ guardedResidualSearch FeatureDecompositionControls.waitingCode
        (rationalResidualGuard 3 2) [] FeatureDecompositionControls.source ∧
      residual ≠ [] ∧ 3 * residual.length ≤ 2 * FeatureDecompositionControls.source.length := by
  obtain ⟨residual, selected⟩ := guardedResidualSearch_complete FeatureDecompositionControls.waitingCode_spec
    (guard := rationalResidualGuard 3 2) (feature := []) (residual := [false])
    (source := FeatureDecompositionControls.source)
    (by simp [FeatureDecompositionControls.waitingAlgorithm])
    (by simp [FeatureDecompositionControls.source])
    (by decide)
  have correct := guardedResidualSearch_sound FeatureDecompositionControls.waitingCode_spec selected
  refine ⟨residual, selected, ?_, ?_⟩
  · intro empty
    simp [FeatureDecompositionControls.waitingAlgorithm, empty] at correct
  · simpa only [rationalResidualGuard, decide_eq_true_eq] using correct.2.2

theorem no_ratio_result_without_saving :
    ¬ ∃ residual, residual ∈ guardedResidualSearch FeatureDecompositionControls.waitingCode
      (rationalResidualGuard 3 2) FeatureDecompositionControls.source FeatureDecompositionControls.source := by
  rintro ⟨residual, selected⟩
  have correct := guardedResidualSearch_sound FeatureDecompositionControls.waitingCode_spec selected
  omega

theorem canonical_rational_minimum_bound :
    ∃ overhead : Nat, ∀ feature descriptive input,
      ShortestBDescriptiveMap universalConditionalAlgorithm (3 / 2) feature descriptive input →
      descriptive.length ≤ feature.length + overhead := by
  simpa using shortest_rational_descriptive_linear universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec 3 2 (by decide)

theorem canonical_rational_constant_bounds :
    ∃ featureBudget mapBudget : Nat, ∀ feature descriptive input residual,
      (3 / 2 : ℝ) * plainConditionalComplexity universalConditionalAlgorithm input [] ≤ input.length →
      ShortestBFeature universalConditionalAlgorithm (3 / 2) feature input →
      ShortestBDescriptiveMap universalConditionalAlgorithm (3 / 2) feature descriptive input →
      residual ∈ universalConditionalAlgorithm descriptive input →
      feature.length ≤ featureBudget ∧ descriptive.length ≤ mapBudget ∧
        descriptive.length = plainConditionalComplexity universalConditionalAlgorithm residual input ∧
        (3 / 2 : ℝ) * residual.length ≤ input.length := by
  simpa using b_compressible_shortest_rational_maps_constant universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec 3 2 (by decide) (by decide)

theorem arbitrarily_large_rational_instances :
    ∀ size : Nat, ∃ input feature descriptive,
      size < input.length ∧
      ShortestBFeature universalConditionalAlgorithm (3 / 2) feature input ∧
      ShortestBDescriptiveMap universalConditionalAlgorithm (3 / 2) feature descriptive input := by
  intro size
  obtain ⟨input, large, _, feature, minimum⟩ :=
    FeatureCompressionRatioControls.arbitrary_nonintegral_ratio_sources size
  obtain ⟨descriptive, shortest⟩ := exists_shortest_b_descriptive
    universalConditionalAlgorithm (3 / 2) feature input minimum.1
  exact ⟨input, feature, descriptive, large, minimum, shortest⟩

#print axioms unrestricted_map_minimum
#print axioms unrestricted_map_violates_ratio
#print axioms constrained_map_minimum
#print axioms constrained_minimum_not_unrestricted
#print axioms unconstrained_search_selects_first
#print axioms filtering_after_selection_loses_answer
#print axioms filtering_candidates_reaches_second
#print axioms rational_search_reaches_admitted_residual
#print axioms no_ratio_result_without_saving
#print axioms canonical_rational_minimum_bound
#print axioms canonical_rational_constant_bounds
#print axioms arbitrarily_large_rational_instances

end Mettapedia.Examples.Compression.FeatureConstrainedSearchControls
