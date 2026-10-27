import Mettapedia.Computability.KolmogorovComplexity.FeatureInformation

/-!
# Uniform incompressibility bounds for shortest features

This direct compiler decodes a feature description at the empty condition
and then applies the feature to the supplied residual. Its single compiler
constant precedes the feature and source. General information and prefix
comparisons retain their existing owner in FeatureInformation.
-/

namespace KolmogorovComplexity.FeatureTheory

set_option autoImplicit false

def decodeFeatureThenRun (U : ConditionalAlgorithm) : ConditionalAlgorithm :=
  fun program condition => (U program []).bind fun feature => U feature condition

theorem decodeFeatureThenRun_partrec (U : ConditionalAlgorithm) (computable : Partrec₂ U) :
    Partrec₂ (decodeFeatureThenRun U) := by
  have decoded : Partrec (fun input : BinString × BinString => U input.1 []) :=
    computable.comp Computable.fst (Computable.const [])
  have applied : Partrec₂ (fun (input : BinString × BinString) feature => U feature input.2) :=
    (computable.comp Computable.snd (Computable.snd.comp Computable.fst)).to₂
  exact (decoded.bind applied).to₂

/-- A single compiler overhead bounds every shortest feature's saving under
an unconditional description of that feature. -/
theorem shortest_feature_plain_lower (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (computable : Partrec₂ U) :
    ∃ overhead : Nat, ∀ feature source,
      ShortestFeature U feature source →
        feature.length ≤ plainConditionalComplexity U feature [] + overhead := by
  obtain ⟨compiler, compiles⟩ := universal _ (decodeFeatureThenRun_partrec U computable)
  refine ⟨compiler.length, ?_⟩
  intro feature source shortest
  obtain ⟨descriptive,residual,extracts,reconstructs,smaller⟩ := shortest.1
  obtain ⟨program,decodes,minimal⟩ := exists_program_of_plainConditionalComplexity U [] feature
    (universalConditional_hasProgram U universal [] feature)
  have runs : source ∈ decodeFeatureThenRun U program residual :=
    Part.mem_bind decodes reconstructs
  have compiled := compiles program residual source runs
  by_cases short : (compiler ++ program).length ≤ feature.length
  · have competitor : Feature U (compiler ++ program) source :=
      ⟨descriptive,residual,extracts,compiled,by omega⟩
    have least := shortest.2 (compiler ++ program) competitor
    simpa only [List.length_append,minimal,Nat.add_comm] using least
  · simp only [List.length_append,minimal] at short
    omega

/-- The canonical interpreter discharges the effectivity and universality
premises of the direct compiler bound. -/
theorem canonical_shortest_feature_plain_lower :
    ∃ overhead : Nat, ∀ feature source,
      ShortestFeature universalConditionalAlgorithm feature source →
        feature.length ≤ plainConditionalComplexity universalConditionalAlgorithm feature [] + overhead :=
  shortest_feature_plain_lower universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec

end KolmogorovComplexity.FeatureTheory
