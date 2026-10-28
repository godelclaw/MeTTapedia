import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainComplexity
import Mettapedia.Computability.KolmogorovComplexity.ConditionalLowerChainRule

/-!
# Uniform postcomposition of plain descriptions

First run a producer program on the auxiliary condition, then run the supplied
transformation on that output. The transformation is length-delimited once;
the producer occupies the remaining plain payload. Its length is not doubled.
One compiler overhead is fixed before the transformation, condition or source.
-/

set_option autoImplicit false

namespace KolmogorovComplexity

open scoped Classical

def interpretPlainPair (U : ConditionalAlgorithm) (fields : BinString × BinString)
    (condition : BinString) : Part BinString :=
  (U fields.2 condition).bind (U fields.1)

theorem interpretPlainPair_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec₂ (interpretPlainPair U) := by
  apply Partrec.bind (effective.comp (Computable.snd.comp Computable.fst) Computable.snd)
  exact (effective.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd).to₂

def postcomposePlainDescription (U : ConditionalAlgorithm) : ConditionalAlgorithm :=
  fun program condition => (Part.ofOption (unpairCondition program)).bind fun fields =>
    interpretPlainPair U fields condition

theorem postcomposePlainDescription_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec₂ (postcomposePlainDescription U) := by
  apply Partrec.bind (KraftChaitin.unpairCondition_primrec.to_comp.comp Computable.fst).ofOption
  exact ((interpretPlainPair_partrec effective).comp Computable.snd
    (Computable.snd.comp Computable.fst)).to₂

theorem postcomposePlainDescription_runs {U : ConditionalAlgorithm}
    {transformation producer condition source output : BinString}
    (produces : source ∈ U producer condition) (transforms : output ∈ U transformation source) :
    output ∈ postcomposePlainDescription U (pairCondition transformation producer) condition := by
  have decoded : (transformation, producer) ∈
      Part.ofOption (unpairCondition (pairCondition transformation producer)) := by
    simp [unpairCondition_pairCondition]
  have runs : output ∈ interpretPlainPair U (transformation, producer) condition :=
    Part.mem_bind produces transforms
  exact Part.mem_bind decoded runs

theorem uniform_plain_postcomposition (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ transformation condition source output,
      output ∈ U transformation source →
      plainConditionalComplexity U output condition ≤
        plainConditionalComplexity U source condition + 2 * transformation.length + 1 + overhead := by
  obtain ⟨compiler, compiles⟩ := universal (postcomposePlainDescription U)
    (postcomposePlainDescription_partrec effective)
  refine ⟨compiler.length, fun transformation condition source output transforms => ?_⟩
  obtain ⟨producer, produces, length⟩ := exists_program_of_plainConditionalComplexity U condition source
    (universalConditional_hasProgram U universal condition source)
  have runs := compiles (pairCondition transformation producer) condition output
    (postcomposePlainDescription_runs produces transforms)
  have bound := plainConditionalComplexity_le_of_program U condition output _ runs
  simp only [List.length_append, pairCondition_length, machinePrefix_length, length] at bound
  omega

theorem uniform_plain_bounded_postcomposition (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ budget transformation condition source output,
      transformation.length ≤ budget → output ∈ U transformation source →
      plainConditionalComplexity U output condition ≤
        plainConditionalComplexity U source condition + (2 * budget + 1 + overhead) := by
  obtain ⟨overhead, bounds⟩ := uniform_plain_postcomposition U universal effective
  refine ⟨overhead, fun budget transformation condition source output bounded transforms => ?_⟩
  have bound := bounds transformation condition source output transforms
  omega

#print axioms interpretPlainPair_partrec
#print axioms postcomposePlainDescription_partrec
#print axioms postcomposePlainDescription_runs
#print axioms uniform_plain_postcomposition
#print axioms uniform_plain_bounded_postcomposition

end KolmogorovComplexity
