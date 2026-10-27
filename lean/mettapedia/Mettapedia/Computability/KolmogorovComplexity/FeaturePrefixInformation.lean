import Mettapedia.Computability.KolmogorovComplexity.FeatureInformation
import Mettapedia.Computability.KolmogorovComplexity.ReferenceMachine

/-!
# Uniform feature information in an effective prefix reference machine

Feature minimization uses the stated conditional source interpreter `U`.
Information is measured by an independently named effective prefix reference
machine `V`. Actual compiler simulations connect them. Constants depend on
these machines, never on the source, feature or residual.

This supplies the logarithmic incompressibility bound (IC Theorem 3.1), the
general directional bound (Theorem 3.3, equation 16), and its shortest-feature
specialization (Corollary 3.1, equation 22). It makes no joint-information or
reverse-direction claim from these alone.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

def evaluatePrefixDescription (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine) : ConditionalAlgorithm :=
  fun description condition => (Part.ofOption (V.compute description condition)).bind fun feature => U feature condition

theorem evaluatePrefixDescription_partrec {U : ConditionalAlgorithm} {V : ConditionalPrefixFreeMachine}
    (effectiveU : Partrec₂ U) (effectiveV : Effective V) : Partrec₂ (evaluatePrefixDescription U V) := by
  apply Partrec.bind effectiveV
  exact (effectiveU.comp Computable.snd (Computable.snd.comp Computable.fst)).to₂

theorem uniform_prefix_evaluation (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ feature residual source,
      source ∈ U feature residual →
        plainConditionalComplexity U source residual ≤ conditionalComplexity V feature residual + overhead := by
  obtain ⟨compiler, compiles⟩ := universal (evaluatePrefixDescription U V)
    (evaluatePrefixDescription_partrec effective reference.1)
  refine ⟨compiler.length, fun feature residual source reconstructs => ?_⟩
  obtain ⟨description, describes, minimal⟩ :=
    exists_program_of_conditionalComplexity V residual feature (reference.hasProgram residual feature)
  have run : feature ∈ Part.ofOption (V.compute description residual) := by
    simpa [IsProgram, describes]
  have output : source ∈ evaluatePrefixDescription U V description residual :=
    Part.mem_bind run reconstructs
  have bound := plainConditionalComplexity_le_of_program U residual source _
    (compiles description residual source output)
  simpa only [List.length_append, minimal, Nat.add_comm] using bound

theorem reference_literal_bound (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ output condition,
      conditionalComplexity V output condition ≤ output.length + 2 * Nat.log 2 (output.length + 1) + overhead := by
  obtain ⟨literal, literalBound⟩ := uniform_literal_bound U universal
  obtain ⟨compiler⟩ := reference.2 (selfDelimitingConditionalMachine U)
    (selfDelimitingConditionalMachine_effective U effective)
  refine ⟨3 * literal + 3 + compiler.compilerPrefix.length, fun output condition => ?_⟩
  obtain ⟨program, runs⟩ := universalConditional_hasProgram U universal condition output
  have translated := compiler.conditionalComplexity_le
    ⟨e2encode program, selfDelimitingConditionalMachine_isProgram U runs⟩
  have header := selfDelimitingConditionalComplexity_le_plain_plus_log U condition output ⟨program, runs⟩
  have plain := literalBound output condition
  have logarithm := Nat.log_mono_right (b := 2) (Nat.add_le_add_right plain 1)
  have shift := log_add_constant_le output.length literal
  omega

theorem plain_le_reference (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ output condition,
      plainConditionalComplexity U output condition ≤ conditionalComplexity V output condition + overhead := by
  obtain ⟨overhead, bound⟩ := universal_plainConditionalComplexity_le U (prefixAlgorithm V) universal reference.1
  refine ⟨overhead, fun output condition => ?_⟩
  obtain ⟨program, runs⟩ := reference.hasProgram condition output
  have result := bound condition output ⟨program, (prefixAlgorithm_runs V _ _ _).mpr runs⟩
  simpa only [prefix_complexity_agrees] using result

/-- The lower overhead is constant; the upper bound charges the actual
self-delimiting header and a uniform compiler constant. -/
theorem reference_feature_incompressibility (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ lowerOverhead upperOverhead : Nat, ∀ source feature,
      ShortestFeature U feature source →
        feature.length ≤ conditionalComplexity V feature [] + lowerOverhead ∧
        conditionalComplexity V feature [] ≤ feature.length + 2 * Nat.log 2 (feature.length + 1) + upperOverhead := by
  obtain ⟨lower, _, plain⟩ := shortest_feature_incompressibility U universal effective
  obtain ⟨translation, translate⟩ := plain_le_reference U V universal reference
  obtain ⟨upper, literal⟩ := reference_literal_bound U V universal effective reference
  refine ⟨lower + translation, upper, fun source feature shortest => ?_⟩
  have first := (plain source feature shortest).1
  have second := translate feature []
  exact ⟨by omega, literal feature []⟩

/-- IC Theorem 3.3(16) with uniform constants and explicitly related source
and information machines. A non-shortest feature pays its full length gap. -/
theorem reference_feature_information (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ shortest feature descriptive source residual,
      ShortestFeature U shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      conditionalComplexity V feature [] ≤
        (feature.length - shortest.length) + conditionalComplexity V feature residual +
          2 * Nat.log 2 (feature.length + 1) + overhead := by
  obtain ⟨evaluation, evalBound⟩ := uniform_prefix_evaluation U V universal effective reference
  obtain ⟨literal, literalBound⟩ := reference_literal_bound U V universal effective reference
  refine ⟨evaluation + literal, fun shortest feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have short := shortest_feature_le_residual_complexity minimal extracts reconstructs smaller
  have order := minimal.2 feature ⟨descriptive, residual, extracts, reconstructs, smaller⟩
  have evaluates := evalBound feature residual source reconstructs
  have upper := literalBound feature []
  omega

/-- Ignoring a condition in an effective prefix reference machine costs
only a uniform constant, with no additional logarithmic term. -/
theorem reference_ignore_condition (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ output condition,
      conditionalComplexity V output condition ≤ conditionalComplexity V output [] + overhead := by
  let blind := conditionBlindLift (conditionalSlice V [])
  have effective : Effective blind :=
    (reference.1.comp Computable.fst (Computable.const [])).to₂
  obtain ⟨compiler⟩ := reference.2 blind effective
  refine ⟨compiler.compilerPrefix.length, fun output condition => ?_⟩
  obtain ⟨program, runs, minimal⟩ :=
    exists_program_of_conditionalComplexity V [] output (reference.hasProgram [] output)
  have copy : IsProgram blind program condition output := runs
  have bound := conditionalComplexity_le_program_length V condition output _ (compiler.program copy)
  simpa only [List.length_append, minimal, Nat.add_comm] using bound

/-- IC Corollary 3.1(22): conditional and unconditional feature information
agree to a uniform logarithmic bound for a shortest feature. -/
theorem reference_shortest_independence (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ feature descriptive source residual,
      ShortestFeature U feature source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      |((conditionalComplexity V feature [] : Int) - conditionalComplexity V feature residual)| ≤
        (2 * Nat.log 2 (feature.length + 1) + overhead : Nat) := by
  obtain ⟨forward, forwardBound⟩ := reference_feature_information U V universal effective reference
  obtain ⟨backward, backwardBound⟩ := reference_ignore_condition V reference
  refine ⟨max forward backward, fun feature descriptive source residual minimal extracts reconstructs smaller => ?_⟩
  have first := forwardBound feature feature descriptive source residual minimal extracts reconstructs smaller
  have second := backwardBound feature residual
  rw [abs_le]
  constructor <;> omega

#print axioms evaluatePrefixDescription_partrec
#print axioms reference_feature_incompressibility
#print axioms reference_feature_information
#print axioms reference_shortest_independence

end KolmogorovComplexity.FeatureTheory
