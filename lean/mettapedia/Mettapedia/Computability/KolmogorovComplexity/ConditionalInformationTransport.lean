import Mettapedia.Computability.KolmogorovComplexity.EffectiveContainmentRepair
import Mettapedia.Computability.KolmogorovComplexity.ReferenceMachine

/-!
# Uniform conditional information transport

Conditional composition uses the actual prefix-pairing, condition-selection
and output-projection compilers. Pair order is changed by a separately proved
effective machine, not by identifying directional information definitionally.
All constants are fixed before the data strings are quantified.

The data-processing result corresponds to Lemma 3.4 of Arthur Franz,
Oleksandr Antonenko and Roman Soletskyi, "A theory of incremental
compression" (2020), doi:10.1016/j.ins.2020.08.035.

The pair-swap and index-removal utilities retain their existing qualified
names while acquiring one general, feature-independent source owner here.
-/

set_option autoImplicit false

namespace KolmogorovComplexity

open scoped Classical

namespace FeatureTheory

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

end FeatureTheory

namespace ConditionalInformationTransport

theorem joint_chain_upper (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V)
    (first second condition : BinString) :
    conditionalComplexity V (pairCondition first second) condition ≤
      conditionalComplexity V first condition + conditionalComplexity V second first +
        chain.constant + simulations.headCondition.compilerPrefix.length := by
  obtain ⟨program, runs, minimal⟩ := exists_program_of_conditionalComplexity V first second
    (reference.hasProgram _ _)
  have selected := conditionalComplexity_le_simulated_program simulations.headCondition
    (headConditionMachine_program
      (condition := pairCondition (binaryBits (conditionalComplexity V first condition)) condition) runs)
  rw [minimal] at selected
  have upper := chain.upper condition first second (reference.hasProgram _ _) (reference.hasProgram _ _)
  change conditionalComplexity V second (chainCondition condition first (conditionalComplexity V first condition)) ≤ _ at selected
  omega

/-- The prefix-free pairing compiler requires no additional length header
for the first program. Its projection gives a uniform conditional triangle. -/
theorem conditional_triangle (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V)
    (source intermediate target : BinString) :
    conditionalComplexity V target source ≤
      conditionalComplexity V intermediate source + conditionalComplexity V target intermediate +
        chain.constant + simulations.headCondition.compilerPrefix.length +
        simulations.secondOutput.compilerPrefix.length := by
  obtain ⟨program, runs, minimal⟩ := exists_program_of_conditionalComplexity V source
    (pairCondition intermediate target) (reference.hasProgram _ _)
  have projected := conditionalComplexity_le_simulated_program simulations.secondOutput
    (secondOutputMachine_program runs)
  rw [minimal] at projected
  have upper := joint_chain_upper V reference chain simulations intermediate target source
  omega

theorem complexity_header_bound (V : ConditionalPrefixFreeMachine)
    (simulations : ReferenceMachineSimulations V) (value : BinString) :
    (e1encode (binaryBits (conditionalComplexity V value []))).length ≤
      2 * Nat.log 2 (value.length + 1) +
        (2 * Nat.log 2 (simulations.literal.compilerPrefix.length + 2) + 7) := by
  have header := complexityIndexHeader_le_log simulations.literal
    (show value.length < value.length + 1 by omega)
  have monotone := Nat.log_mono_right (b := 2)
    (show value.length + 1 + 1 ≤ (value.length + 1) * 2 by omega)
  have doubled := Nat.log_mul_base (b := 2) (by decide) (Nat.succ_ne_zero value.length)
  simp only [Nat.succ_eq_add_one] at doubled
  omega

theorem joint_chain_lower (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V)
    (first second : BinString) :
    conditionalComplexity V first [] + conditionalComplexity V second first ≤
      conditionalComplexity V (pairCondition first second) [] +
        2 * Nat.log 2 (first.length + 1) + chain.constant +
        simulations.indexedCondition.compilerPrefix.length +
        (2 * Nat.log 2 (simulations.literal.compilerPrefix.length + 2) + 7) := by
  have removed := FeatureTheory.remove_complexity_index reference simulations second first
  have lower := chain.lower [] first second (reference.hasProgram _ _) (reference.hasProgram _ _)
  have header := complexity_header_bound V simulations first
  omega

/-- The ordered sums differ only by the explicit index header and one
uniform pair-swap/compiler cost. -/
theorem ordered_information_bound (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ first second,
      conditionalComplexity V first [] + conditionalComplexity V second first ≤
        conditionalComplexity V second [] + conditionalComplexity V first second +
          2 * Nat.log 2 (first.length + 1) + overhead := by
  obtain ⟨swapCost, swapBound⟩ := FeatureTheory.reference_pair_swap V reference
  refine ⟨2 * chain.constant + simulations.indexedCondition.compilerPrefix.length +
    simulations.headCondition.compilerPrefix.length +
    (2 * Nat.log 2 (simulations.literal.compilerPrefix.length + 2) + 7) + swapCost,
    fun first second => ?_⟩
  have lower := joint_chain_lower V reference chain simulations first second
  have swapped := swapBound first second []
  have upper := joint_chain_upper V reference chain simulations second first []
  omega

theorem information_symmetry_uniform (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ first second,
      |directedAlgorithmicInformation V first second - directedAlgorithmicInformation V second first| ≤
        (2 * Nat.log 2 (first.length + 1) + 2 * Nat.log 2 (second.length + 1) + overhead : Nat) := by
  obtain ⟨overhead, bound⟩ := ordered_information_bound V reference chain simulations
  refine ⟨overhead, fun first second => ?_⟩
  have forward := bound first second
  have backward := bound second first
  rw [abs_le]
  simp only [directedAlgorithmicInformation, inducedPrefixComplexity]
  constructor <;> omega

/-- IC Lemma 3.4, with one overhead chosen before all three strings. The
error is logarithmic in the target length, not a per-instance constant. -/
theorem information_data_processing (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ source intermediate target,
      directedAlgorithmicInformation V source target ≤
        directedAlgorithmicInformation V source intermediate + conditionalComplexity V target intermediate +
          (2 * Nat.log 2 (target.length + 1) + overhead : Nat) := by
  obtain ⟨orderCost, ordered⟩ := ordered_information_bound V reference chain simulations
  refine ⟨orderCost + chain.constant + simulations.headCondition.compilerPrefix.length +
    simulations.secondOutput.compilerPrefix.length, fun source intermediate target => ?_⟩
  have first := ordered target intermediate
  have second := conditional_triangle V reference chain simulations source target intermediate
  simp only [directedAlgorithmicInformation, inducedPrefixComplexity]
  omega

end ConditionalInformationTransport
end KolmogorovComplexity
