import Mettapedia.Computability.KolmogorovComplexity.FeaturePrefixInformation
import Mettapedia.Computability.KolmogorovComplexity.EffectiveContainmentRepair

/-!
# Joint feature and residual information with uniform costs

The joint bound uses the existing strong conditional chain rule and actual
reference-machine simulations. The complexity index is encoded by the
existing self-delimiting header, with its full logarithmic cost. All constants
precede the feature/source quantifiers.

The pair is encoded in the explicit order `(residual, feature)`. No silent
exchange of the two information directions or pair components is used.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

/-- Removing the complexity index from the condition costs its actual
self-delimiting representation and one fixed interpreter prefix. -/
theorem remove_complexity_index {V : ConditionalPrefixFreeMachine}
    (reference : IsReferenceMachine V) (simulations : ReferenceMachineSimulations V)
    (feature residual : BinString) :
    conditionalComplexity V feature residual ≤
      conditionalComplexity V feature (chainCondition [] residual (conditionalComplexity V residual [])) +
        (e1encode (binaryBits (conditionalComplexity V residual []))).length +
        simulations.indexedCondition.compilerPrefix.length := by
  obtain ⟨program, runs, minimal⟩ := exists_program_of_conditionalComplexity V
    (chainCondition [] residual (conditionalComplexity V residual [])) feature
    (reference.hasProgram _ _)
  have indexed : IsProgram (indexedConditionMachine V)
      (e1encode (binaryBits (conditionalComplexity V residual [])) ++ program) residual feature := by
    simpa only [IsProgram, indexedConditionMachine, e1decode_e1encode_append, chainCondition] using runs
  have bound := conditionalComplexity_le_simulated_program simulations.indexedCondition indexed
  simpa only [List.length_append, minimal, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using bound

theorem reference_feature_joint_information (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature U shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      conditionalComplexity V residual [] + conditionalComplexity V feature [] ≤
        conditionalComplexity V (pairCondition residual feature) [] + (feature.length - shortest.length) +
          2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead := by
  obtain ⟨information, infoBound⟩ := reference_feature_information U V universal effective reference
  let headerConstant := 2 * Nat.log 2 (simulations.literal.compilerPrefix.length + 2) + 5
  refine ⟨information + chain.constant + simulations.indexedCondition.compilerPrefix.length + headerConstant + 2,
    fun shortest feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have featureBound := infoBound shortest feature descriptive source residual minimal extracts reconstructs smaller
  have indexed := remove_complexity_index reference simulations feature residual
  have joint := chain.lower [] residual feature (reference.hasProgram _ _) (reference.hasProgram _ _)
  have header := complexityIndexHeader_le_log simulations.literal
    (show residual.length < residual.length + 1 by omega)
  have shift := log_add_constant_le residual.length 1
  dsimp only [headerConstant]
  omega

/-- The upper chain inequality and the condition-ignoring compiler bound
the paired description by the two separate descriptions, uniformly. -/
theorem reference_joint_upper {V : ConditionalPrefixFreeMachine}
    (reference : IsReferenceMachine V) (chain : StrongConditionalChainRule V) :
    ∃ overhead : Nat, ∀ residual feature,
      conditionalComplexity V (pairCondition residual feature) [] ≤
        conditionalComplexity V residual [] + conditionalComplexity V feature [] + overhead := by
  obtain ⟨ignore, ignoreBound⟩ := reference_ignore_condition V reference
  refine ⟨chain.constant + ignore, fun residual feature => ?_⟩
  have joint := chain.upper [] residual feature (reference.hasProgram _ _) (reference.hasProgram _ _)
  have ignored := ignoreBound feature (chainCondition [] residual (conditionalComplexity V residual []))
  omega

/-- IC's shortest-feature joint independence shape, with the pair order
explicit and all overheads uniform over sources and decomposition lengths. -/
theorem reference_shortest_joint_independence (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      |((conditionalComplexity V (pairCondition residual feature) [] : Int) -
          (conditionalComplexity V residual [] + conditionalComplexity V feature []))| ≤
        (2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead : Nat) := by
  obtain ⟨lower, lowerBound⟩ := reference_feature_joint_information U V universal effective reference chain simulations
  obtain ⟨upper, upperBound⟩ := reference_joint_upper reference chain
  refine ⟨max lower upper, fun feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have below := lowerBound feature feature descriptive source residual minimal extracts reconstructs smaller
  have above := upperBound residual feature
  rw [abs_le]
  constructor <;> omega

/-- The existing pair-swap interpreter is effective; exchanging the two
fields is an actual program transformation, not a definitional equality. -/
theorem swapPairMachine_effective (V : ConditionalPrefixFreeMachine) (effective : Effective V) :
    Effective (swapPairMachine V) := by
  let swapOutput : BinString → Option BinString := fun output =>
    (unpairCondition output).map fun fields => pairCondition fields.2 fields.1
  have swapComputable : Primrec swapOutput :=
    Primrec.option_map KraftChaitin.unpairCondition_primrec
      (pairCondition_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.right) (Primrec.fst.comp₂ Primrec₂.right))
  have tail : Partrec₂ fun (_input : BinString × BinString) output => Part.ofOption (swapOutput output) :=
    (Computable.ofOption (swapComputable.to_comp.comp Computable.snd)).to₂
  exact (Partrec.bind effective tail).of_eq fun input => by
    cases evaluated : V.compute input.1 input.2 with
    | none => simp [swapPairMachine, evaluated, Part.ofOption]
    | some output =>
        cases decoded : unpairCondition output <;>
          simp [swapOutput, swapPairMachine, evaluated, decoded, Part.ofOption, Part.bind_some]

theorem reference_pair_swap (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ first second condition,
      conditionalComplexity V (pairCondition first second) condition ≤
        conditionalComplexity V (pairCondition second first) condition + overhead := by
  obtain ⟨compiler⟩ := reference.2 (swapPairMachine V) (swapPairMachine_effective V reference.1)
  refine ⟨compiler.compilerPrefix.length, fun first second condition => ?_⟩
  obtain ⟨program, runs, minimal⟩ := exists_program_of_conditionalComplexity V condition
    (pairCondition second first) (reference.hasProgram _ _)
  have swapped : IsProgram (swapPairMachine V) program condition (pairCondition first second) := by
    change V.compute program condition = some (pairCondition second first) at runs
    simp only [IsProgram, swapPairMachine, runs, unpairCondition_pairCondition]
  have bound := conditionalComplexity_le_simulated_program compiler swapped
  simpa only [minimal] using bound

/-- The general joint deficit in `(feature, residual)` order, including
the excess length of a feature that is not shortest. -/
theorem reference_feature_first_joint_information (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature U shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      conditionalComplexity V feature [] + conditionalComplexity V residual [] ≤
        conditionalComplexity V (pairCondition feature residual) [] + (feature.length - shortest.length) +
          2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead := by
  obtain ⟨jointCost, jointBound⟩ := reference_feature_joint_information U V universal effective reference chain simulations
  obtain ⟨swapCost, swapBound⟩ := reference_pair_swap V reference
  refine ⟨jointCost + swapCost, fun shortest feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have joint := jointBound shortest feature descriptive source residual minimal extracts reconstructs smaller
  have swap := swapBound residual feature []
  omega

/-- IC Corollary 3.1(23), including the reverse direction that cannot be
obtained by simply interchanging the information arguments. -/
theorem reference_residual_independence (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      |((conditionalComplexity V residual [] : Int) - conditionalComplexity V residual feature)| ≤
        (2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead : Nat) := by
  obtain ⟨jointCost, jointBound⟩ := reference_feature_joint_information U V universal effective reference chain simulations
  obtain ⟨swapCost, swapBound⟩ := reference_pair_swap V reference
  obtain ⟨ignoreCost, ignoreBound⟩ := reference_ignore_condition V reference
  refine ⟨max (jointCost + swapCost + chain.constant + simulations.headCondition.compilerPrefix.length) ignoreCost,
    fun feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have lower := jointBound feature feature descriptive source residual minimal extracts reconstructs smaller
  have swap := swapBound residual feature []
  have upper := chain.upper [] feature residual (reference.hasProgram _ _) (reference.hasProgram _ _)
  obtain ⟨program, runs, shortest⟩ := exists_program_of_conditionalComplexity V feature residual (reference.hasProgram _ _)
  have indexed : IsProgram (headConditionMachine V) program
      (chainCondition [] feature (conditionalComplexity V feature [])) residual :=
    headConditionMachine_program runs
  have indexBound := conditionalComplexity_le_simulated_program simulations.headCondition indexed
  rw [shortest] at indexBound
  have ignored := ignoreBound residual feature
  rw [abs_le]
  constructor <;> omega

/-- The joint independence equation in the paper's `(feature, residual)`
order, after explicitly accounting for the pair-swap compiler. -/
theorem reference_feature_first_joint_independence (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      |((conditionalComplexity V (pairCondition feature residual) [] : Int) -
          (conditionalComplexity V feature [] + conditionalComplexity V residual []))| ≤
        (2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead : Nat) := by
  obtain ⟨jointCost, jointBound⟩ := reference_feature_joint_information U V universal effective reference chain simulations
  obtain ⟨swapCost, swapBound⟩ := reference_pair_swap V reference
  obtain ⟨upperCost, upperBound⟩ := reference_joint_upper reference chain
  refine ⟨max (jointCost + swapCost) upperCost,
    fun feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have lower := jointBound feature feature descriptive source residual minimal extracts reconstructs smaller
  have swap := swapBound residual feature []
  have upper := upperBound feature residual
  rw [abs_le]
  constructor <;> omega

#print axioms remove_complexity_index
#print axioms reference_feature_joint_information
#print axioms reference_feature_first_joint_information
#print axioms reference_shortest_joint_independence
#print axioms reference_residual_independence
#print axioms reference_feature_first_joint_independence

end KolmogorovComplexity.FeatureTheory
