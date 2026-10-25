import Mettapedia.Computability.KolmogorovComplexity.PrefixComplexity

/-!
# Conditional slices and effective reference-machine bounds

Fixing a condition preserves programs, outputs and shortest lengths. Represented
outputs have pointwise mass bounds; effective reference machines give the global
Kraft bounds uniformly in the condition, without simulating arbitrary machines.
-/

namespace KolmogorovComplexity

open scoped Classical BigOperators

/-- Conditional prefix complexity equals ordinary complexity of the slice. -/
theorem conditionalComplexity_eq_prefixComplexity_slice
    (U : ConditionalPrefixFreeMachine) (condition output : BinString) :
    Kc[U](output | condition) = Kpf[conditionalSlice U condition](output) :=
  conditionalComplexity_eq_kolmogorovComplexity_slice U condition output

/-- A represented conditional output has at least its shortest-description weight. -/
theorem conditionalComplexityWeight_le_outputMass (U : ConditionalPrefixFreeMachine)
    (condition output : BinString) (represented : HasProgram U condition output) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(Kc[U](output | condition) : Int))) ≤
      prefixOutputMass (U.compute · condition) output := by
  rw [conditionalComplexity_eq_prefixComplexity_slice]
  exact prefixComplexityWeight_le_outputMass (conditionalSlice U condition) output represented

/-- A shortest program at any condition of an effective reference machine. -/
noncomputable def shortestConditionalProgram
    (U : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine U)
    (condition output : BinString) : BinString :=
  Classical.choose
    (exists_program_of_conditionalComplexity U condition output
      (reference.hasProgram condition output))

theorem shortestConditionalProgram_spec
    (U : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine U)
    (condition output : BinString) :
    IsProgram U (shortestConditionalProgram U reference condition output) condition output ∧
      (shortestConditionalProgram U reference condition output).length =
        Kc[U](output | condition) :=
  Classical.choose_spec
    (exists_program_of_conditionalComplexity U condition output
      (reference.hasProgram condition output))

/-- Finite conditional Kraft bound inherited from the fixed-condition slice. -/
theorem sum_weightByConditionalComplexity_le_one
    (U : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine U)
    (condition : BinString) (outputs : Finset BinString) :
    (∑ output ∈ outputs,
      (2 : ENNReal) ^ (-(Kc[U](output | condition) : Int))) ≤ 1 := by
  simpa only [← ofReal_two_zpow_neg_nat, conditionalComplexity_eq_prefixComplexity_slice] using
    sum_weightByKpf_le_one_on (conditionalSlice U condition) outputs
      (fun output _ => reference.hasProgram condition output)

/-- Countable conditional Kraft bound inherited from the fixed-condition slice. -/
theorem tsum_weightByConditionalComplexity_le_one
    (U : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine U)
    (condition : BinString) :
    (∑' output : BinString,
      (2 : ENNReal) ^ (-(Kc[U](output | condition) : Int))) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (sum_weightByConditionalComplexity_le_one U reference condition)

/-- Freezing a condition does not add missing outputs. -/
theorem fixedEmptySlice_not_outputComplete :
    ¬ OutputComplete (conditionalSlice fixedEmptyMachine []) := by
  intro complete
  obtain ⟨program, computes⟩ := complete.has_program [true]
  simp [conditionalSlice, fixedEmptyMachine] at computes

/-- The singleton-output machine cannot be an effective reference machine. -/
theorem fixedEmptyMachine_not_reference : ¬ IsReferenceMachine fixedEmptyMachine := by
  intro reference
  obtain ⟨program, computes⟩ := reference.hasProgram [] [true]
  simp [IsProgram, fixedEmptyMachine] at computes

end KolmogorovComplexity
