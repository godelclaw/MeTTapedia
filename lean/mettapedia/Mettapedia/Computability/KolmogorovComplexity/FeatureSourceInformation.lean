import Mettapedia.Computability.KolmogorovComplexity.FeatureJointInformation
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPrefixBridge

/-!
# Shortest features conditional on their source

The high-compression case admits a fixed universal feature, bounding every
shortest feature by its constant length. In the complementary case, the source
already contains almost its full length of information. The conditional chain
rule then bounds the information needed to identify its shortest feature.

Every compiler constant precedes the source quantifier. Source-program and
prefix-reference complexities are connected by the existing proved simulations.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

/-- Execute the condition as a feature on the program supplied as residual. -/
def residualApplication (U : ConditionalAlgorithm) : ConditionalAlgorithm :=
  fun residual feature => U feature residual

theorem residualApplication_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec₂ (residualApplication U) :=
  (effective.comp Computable.snd Computable.fst).to₂

/-- Given the feature, an E2-framed residual reconstructs the source. -/
theorem reference_residual_description (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ feature residual source,
      source ∈ U feature residual →
      conditionalComplexity V source feature ≤
        residual.length + 2 * Nat.log 2 (residual.length + 1) + overhead := by
  obtain ⟨compiler⟩ := reference.2 (selfDelimitingConditionalMachine (residualApplication U))
    (selfDelimitingConditionalMachine_effective _ (residualApplication_partrec effective))
  refine ⟨3 + compiler.compilerPrefix.length, fun feature residual source reconstructs => ?_⟩
  have framed := selfDelimitingConditionalMachine_isProgram (residualApplication U) reconstructs
  have bound := conditionalComplexity_le_simulated_program compiler framed
  have length := e2encode_length_le_log residual
  omega

/-- Exchange the order of the conditional chain rule, charging the actual
complexity-index header and pair-swap interpreter. -/
theorem reference_conditional_exchange (V : ConditionalPrefixFreeMachine)
    (reference : IsReferenceMachine V) (chain : StrongConditionalChainRule V)
    (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ first second,
      conditionalComplexity V first [] + conditionalComplexity V second first ≤
        conditionalComplexity V second [] + conditionalComplexity V first second +
          2 * Nat.log 2 (first.length + 1) + overhead := by
  obtain ⟨swapCost, swapBound⟩ := reference_pair_swap V reference
  let headerCost := 2 * Nat.log 2 (simulations.literal.compilerPrefix.length + 2) + 5
  refine ⟨2 * chain.constant + simulations.indexedCondition.compilerPrefix.length +
    simulations.headCondition.compilerPrefix.length + swapCost + headerCost + 2,
    fun first second => ?_⟩
  have indexed := remove_complexity_index reference simulations second first
  have lower := chain.lower [] first second (reference.hasProgram _ _) (reference.hasProgram _ _)
  have swap := swapBound first second []
  have upper := chain.upper [] second first (reference.hasProgram _ _) (reference.hasProgram _ _)
  obtain ⟨program, runs, minimal⟩ := exists_program_of_conditionalComplexity V second first
    (reference.hasProgram _ _)
  have lifted : IsProgram (headConditionMachine V) program
      (chainCondition [] second (conditionalComplexity V second [])) first :=
    headConditionMachine_program runs
  have liftBound := conditionalComplexity_le_simulated_program simulations.headCondition lifted
  rw [minimal] at liftBound
  have header := complexityIndexHeader_le_log simulations.literal
    (show first.length < first.length + 1 by omega)
  have shift := log_add_constant_le first.length 1
  dsimp only [headerCost]
  omega

/-- Uniform logarithmic form of IC Theorem 3.2's conditional feature bound.
The statement quantifies over all shortest features, not only the first one
found by a search procedure. -/
theorem reference_shortest_feature_source_bound (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ source feature, ShortestFeature U feature source →
      conditionalComplexity V feature source ≤ 6 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨fixed, works⟩ := universal_feature_with_length_constant U universal effective
  obtain ⟨literalCost, literalBound⟩ := reference_literal_bound U V universal effective reference
  obtain ⟨residualCost, residualBound⟩ := reference_residual_description U V effective reference
  obtain ⟨exchangeCost, exchangeBound⟩ := reference_conditional_exchange V reference chain simulations
  obtain ⟨plainCost, plainBound⟩ := plain_le_reference U V universal reference
  refine ⟨max (fixed.length + 2 * Nat.log 2 (fixed.length + 1) + literalCost)
    (fixed.length + plainCost + literalCost + residualCost + exchangeCost),
    fun source feature minimal => ?_⟩
  by_cases margin : plainConditionalComplexity U source [] + fixed.length < source.length
  · have length := shortest_feature_constant_bound minimal works margin
    have bound := literalBound feature source
    have logarithm := Nat.log_mono_right (b := 2) (Nat.add_le_add_right length 1)
    omega

  · obtain ⟨descriptive, residual, _, reconstructs, smaller⟩ := minimal.1
    have literal := literalBound feature []
    have rest := residualBound feature residual source reconstructs
    have exchange := exchangeBound source feature
    have sourceBound := plainBound source []
    have featureLog := Nat.log_mono_right (b := 2)
      (show feature.length + 1 ≤ source.length + 1 by omega)
    have residualLog := Nat.log_mono_right (b := 2)
      (show residual.length + 1 ≤ source.length + 1 by omega)
    omega

/-- Distinct outputs require distinct descriptions. This finite counting
bound does not identify program length with prefix mass. -/
theorem conditional_output_card_lt (V : ConditionalPrefixFreeMachine)
    (reference : IsReferenceMachine V) (condition : BinString) (outputs : Finset BinString)
    (limit : Nat) (bounded : ∀ output ∈ outputs, conditionalComplexity V output condition ≤ limit) :
    outputs.card < 2 ^ (limit + 1) := by
  classical
  let Programs := Σ length : Fin (limit + 1), List.Vector Bool length.val
  let encodeOutput : (output : BinString) → output ∈ outputs → Programs := fun output member =>
    let program := shortestConditionalProgram V reference condition output
    have length := (shortestConditionalProgram_spec V reference condition output).2
    ⟨⟨program.length, by dsimp only [program]; rw [length]; exact Nat.lt_succ_of_le (bounded output member)⟩,
      ⟨program, rfl⟩⟩
  let encoding : ↥outputs → Programs := fun output => encodeOutput output.val output.property
  have injective : Function.Injective encoding := by
    intro first second equal
    have programEqual : shortestConditionalProgram V reference condition first.val =
        shortestConditionalProgram V reference condition second.val :=
      congrArg (fun program : Programs => program.2.val) equal
    have firstRun := (shortestConditionalProgram_spec V reference condition first.val).1
    have secondRun := (shortestConditionalProgram_spec V reference condition second.val).1
    change V.compute _ condition = some first.val at firstRun
    change V.compute _ condition = some second.val at secondRun
    rw [programEqual] at firstRun
    exact Subtype.ext (Option.some.inj (firstRun.symm.trans secondRun))
  have cardinality := Fintype.card_le_of_injective encoding injective
  have programCount : Fintype.card Programs < 2 ^ (limit + 1) := by
    have sumBound : (∑ length ∈ Finset.range (limit + 1), (2 : Nat) ^ length) < 2 ^ (limit + 1) := by
      exact Nat.geomSum_lt (by decide) (fun length member => Finset.mem_range.mp member)
    simpa [Programs, Fintype.card_sigma, card_vector, Fin.sum_univ_eq_sum_range] using sumBound
  simpa using cardinality.trans_lt programCount

/-- IC Theorem 3.2's polynomial counting conclusion, with a single
coefficient for all sources and finite sets of their shortest features. -/
theorem shortest_feature_polynomial_count (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ coefficient : Nat, ∀ source (features : Finset BinString),
      (∀ feature ∈ features, ShortestFeature U feature source) →
      features.card < coefficient * (source.length + 1) ^ 6 := by
  obtain ⟨overhead, bound⟩ := reference_shortest_feature_source_bound U V universal effective reference chain simulations
  refine ⟨2 ^ (overhead + 1), fun source features minimal => ?_⟩
  have counted := conditional_output_card_lt V reference source features
    (6 * Nat.log 2 (source.length + 1) + overhead) (fun feature member => bound source feature (minimal feature member))
  have logBound := Nat.pow_log_le_self 2 (Nat.succ_ne_zero source.length)
  have powered := Nat.pow_le_pow_left logBound 6
  have scale : 2 ^ (6 * Nat.log 2 (source.length + 1) + overhead + 1) ≤
      2 ^ (overhead + 1) * (source.length + 1) ^ 6 := by
    rw [Nat.add_assoc, Nat.pow_add, Nat.mul_comm 6, Nat.pow_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ powered
  exact counted.trans_le scale

#print axioms residualApplication_partrec
#print axioms reference_residual_description
#print axioms reference_conditional_exchange
#print axioms reference_shortest_feature_source_bound
#print axioms conditional_output_card_lt
#print axioms shortest_feature_polynomial_count

end KolmogorovComplexity.FeatureTheory
