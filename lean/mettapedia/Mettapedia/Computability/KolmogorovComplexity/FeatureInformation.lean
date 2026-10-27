import Mettapedia.Computability.KolmogorovComplexity.FeatureTheory
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainPrefix

/-!
# Uniform incompressibility and directional information of features

The interpreter constants are chosen before any feature, residual or source.
Composition is an actual partial-recursive program: first compute a feature
from its description, then execute that feature on the same residual.

The first results concern plain conditional complexity. The explicit E2
machine supplies separate prefix-free bounds; it is not silently identified
with an arbitrary optimal prefix machine. These give the incompressibility
and one-direction independence arguments underlying IC Theorems 3.1 and
3.3(16). Joint-information symmetry and the other independence directions
require their own chain-rule connections.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

/-- Execute a described program on the original auxiliary input. -/
def evaluateDescription (U : ConditionalAlgorithm) : ConditionalAlgorithm :=
  fun description condition => (U description condition).bind fun program => U program condition

theorem evaluateDescription_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec₂ (evaluateDescription U) := by
  apply Partrec.bind effective
  exact (effective.comp Computable.snd (Computable.snd.comp Computable.fst)).to₂

theorem evaluateDescription_runs {U : ConditionalAlgorithm} {description condition program output : BinString}
    (describes : program ∈ U description condition) (runs : output ∈ U program condition) :
    output ∈ evaluateDescription U description condition := by
  exact Part.mem_bind_iff.mpr ⟨program, describes, runs⟩

/-- One fixed literal compiler works for every output and every condition. -/
theorem uniform_literal_bound (U : ConditionalAlgorithm) (universal : IsUniversalConditional U) :
    ∃ overhead : Nat, ∀ output condition,
      plainConditionalComplexity U output condition ≤ output.length + overhead := by
  have effective : Partrec₂ (fun (program _condition : BinString) => Part.some program) :=
    Computable.fst.partrec
  obtain ⟨compiler, compiles⟩ := universal _ effective
  refine ⟨compiler.length, fun output condition => ?_⟩
  have runs := compiles output condition output (by simp)
  have bound := plainConditionalComplexity_le_of_program U condition output _ runs
  simpa only [List.length_append, Nat.add_comm] using bound

/-- A uniform compiler simulates execution of a described feature. -/
theorem uniform_evaluation_bound (U : ConditionalAlgorithm) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ feature residual source,
      source ∈ U feature residual →
      plainConditionalComplexity U source residual ≤
        plainConditionalComplexity U feature residual + overhead := by
  obtain ⟨compiler, compiles⟩ := universal (evaluateDescription U) (evaluateDescription_partrec effective)
  refine ⟨compiler.length, fun feature residual source executes => ?_⟩
  obtain ⟨description, describes, shortest⟩ := exists_program_of_plainConditionalComplexity U residual feature
    (universalConditional_hasProgram U universal residual feature)
  have runs := compiles description residual source (evaluateDescription_runs describes executes)
  have bound := plainConditionalComplexity_le_of_program U residual source _ runs
  simpa only [List.length_append, shortest, Nat.add_comm] using bound

/-- Ignoring auxiliary input also has one source-independent compiler. -/
theorem uniform_ignore_condition (U : ConditionalAlgorithm) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ output condition,
      plainConditionalComplexity U output condition ≤ plainConditionalComplexity U output [] + overhead := by
  have ignores : Partrec₂ (fun (program _condition : BinString) => U program []) :=
    (effective.comp Computable.fst (Computable.const [])).to₂
  obtain ⟨compiler, compiles⟩ := universal _ ignores
  refine ⟨compiler.length, fun output condition => ?_⟩
  obtain ⟨description, runs, shortest⟩ := exists_program_of_plainConditionalComplexity U [] output
    (universalConditional_hasProgram U universal [] output)
  have bound := plainConditionalComplexity_le_of_program U condition output _
    (compiles description condition output runs)
  simpa only [List.length_append, shortest, Nat.add_comm] using bound

/-- Any reconstruction program using this residual competes with the
globally shortest feature, since the same descriptive map remains usable. -/
theorem shortest_feature_le_residual_complexity {U : ConditionalAlgorithm}
    {shortest feature descriptive source residual : BinString}
    (minimal : ShortestFeature U shortest source)
    (extracts : residual ∈ U descriptive source) (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length) :
    shortest.length ≤ plainConditionalComplexity U source residual := by
  obtain ⟨program, runs, length⟩ := exists_program_of_plainConditionalComplexity U residual source ⟨feature, reconstructs⟩
  have bound := plainConditionalComplexity_le_of_program U residual source feature reconstructs
  have competitor : Feature U program source :=
    ⟨descriptive, residual, extracts, runs, by omega⟩
  simpa only [length] using minimal.2 program competitor

/-- Shortest features cannot be compressed by more than one fixed constant
in the unconditional plain machine. Both constants precede the sources. -/
theorem shortest_feature_incompressibility (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ lowerOverhead upperOverhead : Nat, ∀ source feature,
      ShortestFeature U feature source →
        feature.length ≤ plainConditionalComplexity U feature [] + lowerOverhead ∧
        plainConditionalComplexity U feature [] ≤ feature.length + upperOverhead := by
  obtain ⟨evaluation, evalBound⟩ := uniform_evaluation_bound U universal effective
  obtain ⟨ignore, ignoreBound⟩ := uniform_ignore_condition U universal effective
  obtain ⟨literal, literalBound⟩ := uniform_literal_bound U universal
  refine ⟨evaluation + ignore, literal, fun source feature minimal => ?_⟩
  obtain ⟨descriptive, residual, extracts, reconstructs, smaller⟩ := minimal.1
  have length := shortest_feature_conditional minimal extracts reconstructs smaller
  have first := evalBound feature residual source reconstructs
  have second := ignoreBound feature residual
  exact ⟨by omega, literalBound feature []⟩

/-- The excess feature length bounds its directional plain information
about the residual, with a constant uniform over the entire feature family. -/
theorem feature_information_bound (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature U shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      plainConditionalComplexity U feature [] ≤
        (feature.length - shortest.length) + plainConditionalComplexity U feature residual + overhead := by
  obtain ⟨evaluation, evalBound⟩ := uniform_evaluation_bound U universal effective
  obtain ⟨literal, literalBound⟩ := uniform_literal_bound U universal
  refine ⟨evaluation + literal, fun shortest feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have shortLength := shortest_feature_le_residual_complexity minimal extracts reconstructs smaller
  have order := minimal.2 feature ⟨descriptive, residual, extracts, reconstructs, smaller⟩
  have evaluationBound := evalBound feature residual source reconstructs
  have literalUpper := literalBound feature []
  omega

/-- The explicit prefix-free E2 machine receives the same lower bound and
a measured logarithmic header bound. No prefix universality is inferred. -/
theorem shortest_feature_prefix_bounds (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ lowerOverhead literalOverhead : Nat, ∀ source feature,
      ShortestFeature U feature source →
        feature.length ≤ conditionalComplexity (selfDelimitingConditionalMachine U) feature [] + lowerOverhead ∧
        conditionalComplexity (selfDelimitingConditionalMachine U) feature [] ≤
          feature.length + literalOverhead + 2 * Nat.log 2 (feature.length + literalOverhead + 1) + 3 := by
  obtain ⟨lower, literal, bounds⟩ := shortest_feature_incompressibility U universal effective
  refine ⟨lower, literal, fun source feature minimal => ?_⟩
  have pair := bounds source feature minimal
  have framed := plain_selfDelimiting_complexity_bounds U [] feature
    (universalConditional_hasProgram U universal [] feature)
  have logBound := Nat.log_mono_right (b := 2) (Nat.add_le_add_right pair.2 1)
  constructor <;> omega

/-- Prefix directional independence for the explicitly framed machine.
Every constant is selected before the source and feature quantifiers. -/
theorem feature_prefix_information_bound (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead literalOverhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature U shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      conditionalComplexity (selfDelimitingConditionalMachine U) feature [] ≤
        (feature.length - shortest.length) + conditionalComplexity (selfDelimitingConditionalMachine U) feature residual +
          2 * Nat.log 2 (feature.length + literalOverhead + 1) + overhead := by
  obtain ⟨overhead, bound⟩ := feature_information_bound U universal effective
  obtain ⟨literal, literalBound⟩ := uniform_literal_bound U universal
  refine ⟨overhead + 3, literal, fun shortest feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have information := bound shortest feature descriptive source residual minimal extracts reconstructs smaller
  have upper := selfDelimitingConditionalComplexity_le_plain_plus_log U [] feature
    (universalConditional_hasProgram U universal [] feature)
  have lower := plainConditionalComplexity_le_selfDelimiting U residual feature
    (universalConditional_hasProgram U universal residual feature)
  have logBound := Nat.log_mono_right (b := 2) (Nat.add_le_add_right (literalBound feature []) 1)
  omega

/-- A fixed shift in the logarithm is absorbed by a fixed additive bound. -/
theorem log_add_constant_le (n offset : Nat) :
    Nat.log 2 (n + offset + 1) ≤ Nat.log 2 (n + 1) + offset := by
  induction offset with
  | zero => simp
  | succ offset ih =>
      have step := Nat.log_mono_right (b := 2)
        (show n + (offset + 1) + 1 ≤ (n + offset + 1) * 2 by omega)
      rw [Nat.log_mul_base (by decide) (by omega)] at step
      omega

/-- IC's incompressibility shape for the explicitly framed machine, with
one lower constant and one upper constant for all shortest features. -/
theorem shortest_feature_prefix_uniform (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ lowerOverhead upperOverhead : Nat, ∀ source feature,
      ShortestFeature U feature source →
        feature.length ≤ conditionalComplexity (selfDelimitingConditionalMachine U) feature [] + lowerOverhead ∧
        conditionalComplexity (selfDelimitingConditionalMachine U) feature [] ≤
          feature.length + 2 * Nat.log 2 (feature.length + 1) + upperOverhead := by
  obtain ⟨lower, literal, bound⟩ := shortest_feature_prefix_bounds U universal effective
  refine ⟨lower, 3 * literal + 3, fun source feature minimal => ?_⟩
  have pair := bound source feature minimal
  have logarithm := log_add_constant_le feature.length literal
  constructor <;> omega

/-- Directional independence in the paper's logarithmic form. The actual
bound is uniform; it is not a pointwise existential big-O statement. -/
theorem feature_prefix_information_uniform (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature U shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      conditionalComplexity (selfDelimitingConditionalMachine U) feature [] ≤
        (feature.length - shortest.length) + conditionalComplexity (selfDelimitingConditionalMachine U) feature residual +
          2 * Nat.log 2 (feature.length + 1) + overhead := by
  obtain ⟨overhead, literal, bound⟩ := feature_prefix_information_bound U universal effective
  refine ⟨overhead + 2 * literal, fun shortest feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have information := bound shortest feature descriptive source residual minimal extracts reconstructs smaller
  have logarithm := log_add_constant_le feature.length literal
  omega

theorem prefix_conditioning_uniform (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ feature residual,
      conditionalComplexity (selfDelimitingConditionalMachine U) feature residual ≤
        conditionalComplexity (selfDelimitingConditionalMachine U) feature [] +
          2 * Nat.log 2 (feature.length + 1) + overhead := by
  obtain ⟨ignore, ignoreBound⟩ := uniform_ignore_condition U universal effective
  obtain ⟨literal, literalBound⟩ := uniform_literal_bound U universal
  refine ⟨ignore + 2 * (literal + ignore) + 3, fun feature residual => ?_⟩
  have ignored := ignoreBound feature residual
  have literalUpper := literalBound feature []
  have lower := plainConditionalComplexity_le_selfDelimiting U [] feature
    (universalConditional_hasProgram U universal [] feature)
  have upper := selfDelimitingConditionalComplexity_le_plain_plus_log U residual feature
    (universalConditional_hasProgram U universal residual feature)
  have logBound := Nat.log_mono_right (b := 2)
    (show plainConditionalComplexity U feature residual + 1 ≤ feature.length + (literal + ignore) + 1 by omega)
  have shift := log_add_constant_le feature.length (literal + ignore)
  omega

/-- Shortest features have only logarithmically bounded directional
information with their residual. Integer subtraction retains both signs. -/
theorem shortest_feature_prefix_independence (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      |((conditionalComplexity (selfDelimitingConditionalMachine U) feature [] : Int) -
          conditionalComplexity (selfDelimitingConditionalMachine U) feature residual)| ≤
        (2 * Nat.log 2 (feature.length + 1) + overhead : Nat) := by
  obtain ⟨forward, forwardBound⟩ := feature_prefix_information_uniform U universal effective
  obtain ⟨backward, backwardBound⟩ := prefix_conditioning_uniform U universal effective
  refine ⟨max forward backward, fun feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have first := forwardBound feature feature descriptive source residual minimal extracts reconstructs smaller
  have second := backwardBound feature residual
  rw [abs_le]
  constructor <;> omega

#print axioms evaluateDescription_partrec
#print axioms shortest_feature_incompressibility
#print axioms feature_information_bound
#print axioms shortest_feature_prefix_bounds
#print axioms feature_prefix_information_bound
#print axioms shortest_feature_prefix_uniform
#print axioms feature_prefix_information_uniform
#print axioms shortest_feature_prefix_independence

end KolmogorovComplexity.FeatureTheory
