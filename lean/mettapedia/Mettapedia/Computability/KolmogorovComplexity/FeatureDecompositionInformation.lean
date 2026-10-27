import Mettapedia.Computability.KolmogorovComplexity.FeatureResidualSearch

/-!
# Information in a shortest feature and its selected residual

The residual is produced by a shortest descriptive map. An effective search
supplies a short competing map; an arbitrary residual witness is insufficient
for this conclusion. All logarithmic bounds below have uniform constants.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

def rightCondition (condition : BinString) : BinString :=
  ((unpairCondition condition).getD ([], [])).2

theorem rightCondition_computable : Computable rightCondition :=
  Computable.snd.comp (Computable.option_getD KraftChaitin.unpairCondition_primrec.to_comp (Computable.const ([], [])))

def reindexedMachine (V : ConditionalPrefixFreeMachine) (translate : BinString → BinString) : ConditionalPrefixFreeMachine where
  compute := fun program condition => V.compute program (translate condition)
  prefix_free := fun condition => V.prefix_free (translate condition)

theorem reference_reindex (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (translate : BinString → BinString) (effective : Computable translate) :
    ∃ overhead : Nat, ∀ condition output,
      conditionalComplexity V output condition ≤ conditionalComplexity V output (translate condition) + overhead := by
  have compiled : Effective (reindexedMachine V translate) :=
    (reference.1.comp Computable.fst (effective.comp Computable.snd)).to₂
  obtain ⟨compiler⟩ := reference.2 (reindexedMachine V translate) compiled
  refine ⟨compiler.compilerPrefix.length, fun condition output => ?_⟩
  obtain ⟨program, runs, length⟩ := exists_program_of_conditionalComplexity V (translate condition) output
    (reference.hasProgram _ _)
  have translated : IsProgram (reindexedMachine V translate) program condition output := runs
  have bound := conditionalComplexity_le_simulated_program compiler translated
  simpa only [length] using bound

theorem reference_conditional_pair_upper (V : ConditionalPrefixFreeMachine)
    (reference : IsReferenceMachine V) (chain : StrongConditionalChainRule V) :
    ∃ overhead : Nat, ∀ first second condition,
      conditionalComplexity V (pairCondition first second) condition ≤
        conditionalComplexity V first condition + conditionalComplexity V second condition + overhead := by
  obtain ⟨baseCost, baseBound⟩ := reference_reindex V reference (fun condition => rightCondition (rightCondition condition))
    (rightCondition_computable.comp rightCondition_computable)
  refine ⟨chain.constant + baseCost, fun first second condition => ?_⟩
  have upper := chain.upper condition first second (reference.hasProgram _ _) (reference.hasProgram _ _)
  have tail := baseBound (chainCondition condition first (conditionalComplexity V first condition)) second
  have base : rightCondition (rightCondition (chainCondition condition first (conditionalComplexity V first condition))) = condition := by
    simp only [chainCondition, rightCondition, unpairCondition_pairCondition, Option.getD_some]
  rw [base] at tail
  omega

theorem reference_program_description (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ program condition output, output ∈ U program condition →
      conditionalComplexity V output condition ≤ program.length + 2 * Nat.log 2 (program.length + 1) + overhead := by
  obtain ⟨overhead, bound⟩ := reference_residual_description (residualApplication U) V (residualApplication_partrec effective) reference
  exact ⟨overhead, fun program condition output runs => bound condition program output runs⟩

theorem log_of_six_log_bound {length size overhead : Nat}
    (bounded : length ≤ 6 * Nat.log 2 (size + 1) + overhead) :
    Nat.log 2 (length + 1) ≤ Nat.log 2 (size + 1) + overhead + 3 := by
  have first := Nat.log_mono_right (b := 2) (Nat.add_le_add_right bounded 1)
  have shift := log_add_constant_le (6 * Nat.log 2 (size + 1)) overhead
  have small := Nat.log_le_self 2 (size + 1)
  have scaled := Nat.log_mono_right (b := 2)
    (show 6 * Nat.log 2 (size + 1) + 1 ≤ (size + 1) * 2 * 2 * 2 by omega)
  have double := Nat.log_mul_base (b := 2) (by decide) (Nat.succ_ne_zero size)
  have quadruple := Nat.log_mul_base (b := 2) (by decide) (show (size + 1) * 2 ≠ 0 by omega)
  have octuple := Nat.log_mul_base (b := 2) (by decide) (show (size + 1) * 2 * 2 ≠ 0 by omega)
  simp only [Nat.succ_eq_add_one] at double
  omega

/-- The selected residual has a short prefix description conditioned on
the source, because its shortest extractor is short. -/
theorem shortest_map_residual_information (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → ShortestDescriptiveMap U feature descriptive source →
      residual ∈ U descriptive source →
      conditionalComplexity V residual source ≤ 8 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨mapCost, mapBound⟩ := shortest_descriptive_logarithmic U V universal effective reference chain simulations
  obtain ⟨programCost, programBound⟩ := reference_program_description U V effective reference
  refine ⟨3 * mapCost + programCost + 6, fun feature descriptive source residual minimalFeature minimalMap extracts => ?_⟩
  have length := mapBound feature descriptive source minimalFeature minimalMap
  have logarithm := log_of_six_log_bound length
  have bound := programBound descriptive source residual extracts
  omega

/-- IC Theorem 3.4(26), with the residual selected by a shortest descriptive
map. Pair order is the paper's `(feature, residual)`. -/
theorem shortest_maps_no_superfluous_information (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → ShortestDescriptiveMap U feature descriptive source →
      residual ∈ U descriptive source →
      conditionalComplexity V (pairCondition feature residual) source ≤
        14 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨featureCost, featureBound⟩ := reference_shortest_feature_source_bound U V universal effective reference chain simulations
  obtain ⟨residualCost, residualBound⟩ := shortest_map_residual_information U V universal effective reference chain simulations
  obtain ⟨pairCost, pairBound⟩ := reference_conditional_pair_upper V reference chain
  refine ⟨featureCost + residualCost + pairCost, fun feature descriptive source residual minimalFeature minimalMap extracts => ?_⟩
  have featureInformation := featureBound source feature minimalFeature
  have rest := residualBound feature descriptive source residual minimalFeature minimalMap extracts
  have pair := pairBound feature residual source
  omega

/-- Apply a partial-recursive transformation to a prefix machine's output.
The accepted domain remains a subset of the producer's prefix-free domain. -/
noncomputable def postprocessedMachine (V : ConditionalPrefixFreeMachine) (transform : BinString →. BinString) : ConditionalPrefixFreeMachine where
  compute := fun program condition => ((Part.ofOption (V.compute program condition)).bind transform).toOption
  prefix_free := by
    intro condition program extension pref different halts
    have producerHalts : V.compute program condition ≠ none := by
      intro absent
      simp [absent] at halts
      exact halts.1
    simp [V.prefix_free condition program extension pref different producerHalts]
    intro impossible
    exact impossible.1

theorem postprocessedMachine_effective {V : ConditionalPrefixFreeMachine} {transform : BinString →. BinString}
    (producer : Effective V) (transformation : Partrec transform) : Effective (postprocessedMachine V transform) := by
  have composed : Partrec₂ fun program condition => (Part.ofOption (V.compute program condition)).bind transform :=
    Partrec.bind producer (transformation.comp Computable.snd).to₂
  exact composed.of_eq fun input => by simp [postprocessedMachine]

theorem reference_postprocess (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (transform : BinString →. BinString) (effective : Partrec transform) :
    ∃ overhead : Nat, ∀ input output condition, output ∈ transform input →
      conditionalComplexity V output condition ≤ conditionalComplexity V input condition + overhead := by
  obtain ⟨compiler⟩ := reference.2 (postprocessedMachine V transform) (postprocessedMachine_effective reference.1 effective)
  refine ⟨compiler.compilerPrefix.length, fun input output condition transforms => ?_⟩
  obtain ⟨program, runs, length⟩ := exists_program_of_conditionalComplexity V condition input (reference.hasProgram _ _)
  have produced : input ∈ Part.ofOption (V.compute program condition) := by simpa [IsProgram] using runs
  have result : IsProgram (postprocessedMachine V transform) program condition output :=
    Part.toOption_eq_some_iff.mpr (Part.mem_bind produced transforms)
  have bound := conditionalComplexity_le_simulated_program compiler result
  simpa only [length] using bound

def reconstructFeaturePair (U : ConditionalAlgorithm) (pair : BinString) : Part BinString :=
  (Part.ofOption (unpairCondition pair)).bind fun fields => U fields.1 fields.2

theorem reconstructFeaturePair_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec (reconstructFeaturePair U) :=
  Partrec.bind (Computable.ofOption KraftChaitin.unpairCondition_primrec.to_comp)
    (effective.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)).to₂

/-- Source and pair information differ by a uniform logarithmic bound
when both programs in the decomposition are shortest. -/
theorem shortest_maps_information_partition (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → ShortestDescriptiveMap U feature descriptive source →
      residual ∈ U descriptive source → source ∈ U feature residual →
      feature.length + residual.length < source.length →
      |((conditionalComplexity V source [] : Int) -
        (conditionalComplexity V feature [] + conditionalComplexity V residual []))| ≤
          (18 * Nat.log 2 (source.length + 1) + overhead : Nat) := by
  obtain ⟨pairCost, pairBound⟩ := shortest_maps_no_superfluous_information U V universal effective reference chain simulations
  obtain ⟨jointCost, jointBound⟩ := reference_feature_first_joint_information U V universal effective reference chain simulations
  obtain ⟨upperCost, upperBound⟩ := reference_joint_upper reference chain
  obtain ⟨reconstructionCost, reconstructionBound⟩ := reference_postprocess V reference
    (reconstructFeaturePair U) (reconstructFeaturePair_partrec effective)
  obtain ⟨projection⟩ := reference.2 (secondOutputMachine V) (secondOutputMachine_effective V reference.1)
  refine ⟨max (upperCost + reconstructionCost)
    (pairCost + jointCost + chain.constant + simulations.headCondition.compilerPrefix.length + projection.compilerPrefix.length),
    fun feature descriptive source residual minimalFeature minimalMap extracts reconstructs smaller => ?_⟩
  have actualReconstruction : source ∈ reconstructFeaturePair U (pairCondition feature residual) := by
    simpa [reconstructFeaturePair, unpairCondition_pairCondition] using reconstructs
  have sourceUpper := reconstructionBound _ source [] actualReconstruction
  have jointUpper := upperBound feature residual
  have independent := jointBound feature feature descriptive source residual minimalFeature extracts reconstructs smaller
  have conditionalPair := pairBound feature descriptive source residual minimalFeature minimalMap extracts
  let pair := pairCondition feature residual
  have chainUpper := chain.upper [] source pair (reference.hasProgram _ _) (reference.hasProgram _ _)
  obtain ⟨program, runs, length⟩ := exists_program_of_conditionalComplexity V source pair (reference.hasProgram _ _)
  have lifted := headConditionMachine_program (condition := pairCondition (binaryBits (conditionalComplexity V source [])) []) runs
  have liftBound := conditionalComplexity_le_simulated_program simulations.headCondition lifted
  rw [length] at liftBound
  obtain ⟨jointProgram, jointRuns, jointLength⟩ := exists_program_of_conditionalComplexity V [] (pairCondition source pair)
    (reference.hasProgram _ _)
  have projected := conditionalComplexity_le_simulated_program projection (secondOutputMachine_program jointRuns)
  rw [jointLength] at projected
  have featureLog := Nat.log_mono_right (b := 2) (show feature.length + 1 ≤ source.length + 1 by omega)
  have residualLog := Nat.log_mono_right (b := 2) (show residual.length + 1 ≤ source.length + 1 by omega)
  dsimp only [pair] at chainUpper liftBound projected
  change conditionalComplexity V (pairCondition feature residual) (chainCondition [] source (conditionalComplexity V source [])) ≤ _ at liftBound
  rw [abs_le]
  constructor <;> omega

#print axioms shortest_map_residual_information
#print axioms shortest_maps_no_superfluous_information
#print axioms shortest_maps_information_partition

end KolmogorovComplexity.FeatureTheory
