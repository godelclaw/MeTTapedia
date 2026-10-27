import Mettapedia.Computability.KolmogorovComplexity.FeatureDecompositionInformation

/-!
# Uniform information bounds for incremental shortest-feature chains

Each step retains a shortest feature and a shortest descriptive map, plus the
actual extraction, reconstruction and strict-saving witnesses. The information
bound telescopes over these steps. It concerns ideal program lengths, not the
physical size of an executable archive with its separate framing and metadata.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

theorem shortest_maps_length_partition (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → ShortestDescriptiveMap U feature descriptive source →
      residual ∈ U descriptive source → source ∈ U feature residual →
      feature.length + residual.length < source.length →
      |((conditionalComplexity V source [] : Int) -
        (feature.length + conditionalComplexity V residual []))| ≤
          (20 * Nat.log 2 (source.length + 1) + overhead : Nat) := by
  obtain ⟨partitionCost, partition⟩ := shortest_maps_information_partition U V universal effective reference chain simulations
  obtain ⟨lowerCost, upperCost, incompressibility⟩ := reference_feature_incompressibility U V universal effective reference
  refine ⟨partitionCost + max lowerCost upperCost,
    fun feature descriptive source residual minimalFeature minimalMap extracts reconstructs smaller => ?_⟩
  have split := partition feature descriptive source residual minimalFeature minimalMap extracts reconstructs smaller
  have featureBounds := incompressibility source feature minimalFeature
  have logarithm := Nat.log_mono_right (b := 2) (show feature.length + 1 ≤ source.length + 1 by omega)
  rw [abs_le] at split ⊢
  constructor <;> omega

inductive ShortestChain (U : ConditionalAlgorithm) : BinString → List BinString → BinString → Prop
  | nil (source) : ShortestChain U source [] source
  | cons {source residual final feature descriptive features}
      (minimalFeature : ShortestFeature U feature source)
      (minimalMap : ShortestDescriptiveMap U feature descriptive source)
      (extracts : residual ∈ U descriptive source)
      (reconstructs : source ∈ U feature residual)
      (smaller : feature.length + residual.length < source.length)
      (rest : ShortestChain U residual features final) :
      ShortestChain U source (feature :: features) final

def restoreFeatures (U : ConditionalAlgorithm) (features : List BinString) (final : BinString) : Part BinString :=
  features.foldr (fun feature residual => residual.bind (U feature)) (Part.some final)

theorem ShortestChain.reconstruct {U : ConditionalAlgorithm} {source final : BinString} {features : List BinString}
    (chain : ShortestChain U source features final) : source ∈ restoreFeatures U features final := by
  induction chain with
  | nil source => simp [restoreFeatures]
  | cons _ _ _ reconstructs _ _ ih => exact Part.mem_bind ih reconstructs

theorem ShortestChain.residual_le {U : ConditionalAlgorithm} {source final : BinString} {features : List BinString}
    (chain : ShortestChain U source features final) : final.length ≤ source.length := by
  induction chain with
  | nil source => rfl
  | cons _ _ _ _ smaller _ ih => omega

/-- Every successful step spends at least one bit of strict saving. This
termination measure does not bound the search needed to discover a step. -/
theorem ShortestChain.length_bound {U : ConditionalAlgorithm} {source final : BinString} {features : List BinString}
    (chain : ShortestChain U source features final) : features.length + final.length ≤ source.length := by
  induction chain with
  | nil source => simp
  | cons _ _ _ _ smaller _ ih => simp only [List.length_cons]; omega

/-- IC Theorem 3.6 with one uniform constant and an explicit per-step
logarithmic coefficient. No minimality is inferred from a practical run. -/
theorem incremental_information_bound (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ source features final, ShortestChain U source features final →
      |((conditionalComplexity V source [] : Int) -
        ((features.map List.length).sum + conditionalComplexity V final []))| ≤
          (features.length * (20 * Nat.log 2 (source.length + 1) + overhead) : Nat) := by
  obtain ⟨overhead, oneStep⟩ := shortest_maps_length_partition U V universal effective reference chainRule simulations
  refine ⟨overhead, fun source features final chain => ?_⟩
  induction chain with
  | nil source => simp
  | @cons source residual final feature descriptive features minimalFeature minimalMap extracts reconstructs smaller rest ih =>
      have stepBound := oneStep feature descriptive source residual minimalFeature minimalMap extracts reconstructs smaller
      have logarithm := Nat.log_mono_right (b := 2) (show residual.length + 1 ≤ source.length + 1 by omega)
      have larger : features.length * (20 * Nat.log 2 (residual.length + 1) + overhead) ≤
          features.length * (20 * Nat.log 2 (source.length + 1) + overhead) :=
        Nat.mul_le_mul_left _ (by omega)
      have largerInt : (features.length * (20 * Nat.log 2 (residual.length + 1) + overhead) : Int) ≤
          (features.length * (20 * Nat.log 2 (source.length + 1) + overhead) : Int) := by exact_mod_cast larger
      have triangle := abs_add_le
        ((conditionalComplexity V source [] : Int) - (feature.length + conditionalComplexity V residual []))
        ((conditionalComplexity V residual [] : Int) - ((features.map List.length).sum + conditionalComplexity V final []))
      have composed := triangle.trans (add_le_add stepBound (ih.trans largerInt))
      have telescope : ((conditionalComplexity V source [] : Int) - (feature.length + conditionalComplexity V residual [])) +
          ((conditionalComplexity V residual [] : Int) - ((features.map List.length).sum + conditionalComplexity V final [])) =
          (conditionalComplexity V source [] : Int) -
            (feature.length + ((features.map List.length).sum + conditionalComplexity V final [])) := by ring
      rw [telescope] at composed
      simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_mul,
        Nat.cast_one, Nat.cast_ofNat, add_mul, one_mul, add_assoc, add_comm, add_left_comm] using composed

#print axioms shortest_maps_length_partition
#print axioms ShortestChain.reconstruct
#print axioms ShortestChain.length_bound
#print axioms incremental_information_bound

end KolmogorovComplexity.FeatureTheory
