import Mettapedia.Computability.KolmogorovComplexity.FeatureSourceInformation

/-!
# Effective selection of a reconstructing residual

A search rank pairs a residual code with an evaluator budget. Every rank is a
total finite check. Searching ranks therefore reaches a reconstructing residual
whenever one exists, even if earlier candidate computations do not terminate.
The search selects a residual; it does not recover an arbitrarily prescribed
residual or decide that none exists.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

def encodedConditionalAlgorithm (U : ConditionalAlgorithm) : Nat →. Nat :=
  fun input => (Part.ofOption (Encodable.decode (α := BinString × BinString) input)).bind
    fun fields => (U fields.1 fields.2).map Encodable.encode

theorem exists_conditional_algorithm_code {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    ∃ code : Nat.Partrec.Code, Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U :=
  Nat.Partrec.Code.exists_code.mp effective

abbrev ResidualSearchInput := (BinString × BinString) × Nat

def residualSearchStep (code : Nat.Partrec.Code) (input : ResidualSearchInput) : Option BinString :=
  (Encodable.decode (α := BinString) input.2.unpair.1).bind fun residual =>
    if input.1.1.length + residual.length < input.1.2.length ∧
        Nat.Partrec.Code.evaln input.2.unpair.2 code (Encodable.encode (input.1.1, residual)) =
          some (Encodable.encode input.1.2)
    then some residual else none

theorem residualSearchStep_primrec (code : Nat.Partrec.Code) : Primrec (residualSearchStep code) := by
  have decoded : Primrec fun input : ResidualSearchInput => Encodable.decode (α := BinString) input.2.unpair.1 :=
    Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have feature : Primrec fun context : ResidualSearchInput × BinString => context.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have source : Primrec fun context : ResidualSearchInput × BinString => context.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have stage : Primrec fun context : ResidualSearchInput × BinString => context.1.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))
  have evaluation := Nat.Partrec.Code.primrec_evaln.comp
    ((stage.pair (Primrec.const code)).pair (Primrec.encode.comp (feature.pair Primrec.snd)))
  have fits : PrimrecPred fun context : ResidualSearchInput × BinString =>
      context.1.1.1.length + context.2.length < context.1.1.2.length :=
    Primrec.nat_lt.comp (Primrec.nat_add.comp (Primrec.list_length.comp feature)
      (Primrec.list_length.comp Primrec.snd)) (Primrec.list_length.comp source)
  have computes : PrimrecPred fun context : ResidualSearchInput × BinString =>
      Nat.Partrec.Code.evaln context.1.2.unpair.2 code (Encodable.encode (context.1.1.1, context.2)) =
        some (Encodable.encode context.1.1.2) :=
    Primrec.eq.comp evaluation (Primrec.option_some.comp (Primrec.encode.comp source))
  exact Primrec.option_bind decoded
    (Primrec.ite (fits.and computes) (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂

def residualSearch (code : Nat.Partrec.Code) : ConditionalAlgorithm :=
  fun feature source => Nat.rfindOpt fun rank => residualSearchStep code ((feature, source), rank)

theorem residualSearch_partrec (code : Nat.Partrec.Code) : Partrec₂ (residualSearch code) :=
  Partrec.rfindOpt (residualSearchStep_primrec code).to_comp

theorem residualSearchStep_sound {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {feature source residual : BinString} {rank : Nat}
    (found : residualSearchStep code ((feature, source), rank) = some residual) :
    source ∈ U feature residual ∧ feature.length + residual.length < source.length := by
  unfold residualSearchStep at found
  cases decoded : Encodable.decode (α := BinString) rank.unpair.1 with
  | none => simp [decoded] at found
  | some candidate =>
      simp only [decoded, Option.bind_some] at found
      split_ifs at found with accepts
      · have same := Option.some.inj found
        subst candidate
        have evaluated := Nat.Partrec.Code.evaln_sound (show Encodable.encode source ∈
          Nat.Partrec.Code.evaln rank.unpair.2 code (Encodable.encode (feature, residual)) from
            by simpa only [Option.mem_def] using accepts.2)
        rw [codeSpec] at evaluated
        have runs : source ∈ U feature residual := by
          simpa [encodedConditionalAlgorithm] using evaluated
        exact ⟨runs, accepts.1⟩

theorem residualSearchStep_complete {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {feature source residual : BinString} (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length) :
    ∃ rank, residualSearchStep code ((feature, source), rank) = some residual := by
  have evaluated : Encodable.encode source ∈
      Nat.Partrec.Code.eval code (Encodable.encode (feature, residual)) := by
    rw [codeSpec]
    simpa [encodedConditionalAlgorithm] using Part.mem_map Encodable.encode reconstructs
  obtain ⟨stage, computes⟩ := Nat.Partrec.Code.evaln_complete.mp evaluated
  refine ⟨Nat.pair (Encodable.encode residual) stage, ?_⟩
  simp [residualSearchStep, smaller]
  exact Option.mem_def.mp computes

theorem residualSearch_sound {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {feature source residual : BinString} (selected : residual ∈ residualSearch code feature source) :
    source ∈ U feature residual ∧ feature.length + residual.length < source.length := by
  obtain ⟨rank, found⟩ := Nat.rfindOpt_spec selected
  exact residualSearchStep_sound codeSpec (Option.mem_def.mp found)

theorem residualSearch_complete {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {feature source residual : BinString} (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length) :
    ∃ selected, selected ∈ residualSearch code feature source := by
  obtain ⟨rank, candidate⟩ := residualSearchStep_complete codeSpec reconstructs smaller
  exact Part.dom_iff_mem.mp (Nat.rfindOpt_dom.mpr
    ⟨rank, residual, by simpa only [Option.mem_def] using candidate⟩)

/-- First decode a feature from its prefix description conditioned on the
source, then search for a reconstructing residual. -/
def describedResidualSearch (V : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code) : ConditionalAlgorithm :=
  fun program source => (Part.ofOption (V.compute program source)).bind fun feature =>
    residualSearch code feature source

theorem describedResidualSearch_partrec {V : ConditionalPrefixFreeMachine}
    (effective : Effective V) (code : Nat.Partrec.Code) : Partrec₂ (describedResidualSearch V code) := by
  apply Partrec.bind effective
  exact ((residualSearch_partrec code).comp Computable.snd (Computable.snd.comp Computable.fst)).to₂

/-- A genuine uniformly compiled extractor witnesses the descriptive-map
bound. The selected residual may differ from an initially supplied witness. -/
theorem descriptive_map_from_feature_description (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ feature source, Feature U feature source →
      ∃ descriptive, DescriptiveMap U feature descriptive source ∧
        descriptive.length ≤ conditionalComplexity V feature source + overhead := by
  obtain ⟨code, codeSpec⟩ := exists_conditional_algorithm_code effective
  obtain ⟨compiler, compiles⟩ := universal (describedResidualSearch V code)
    (describedResidualSearch_partrec reference.1 code)
  refine ⟨compiler.length, fun feature source present => ?_⟩
  obtain ⟨oldMap, residual, _, reconstructs, smaller⟩ := present
  obtain ⟨program, decodes, length⟩ := exists_program_of_conditionalComplexity V source feature
    (reference.hasProgram _ _)
  obtain ⟨selected, finds⟩ := residualSearch_complete codeSpec reconstructs smaller
  have decoded : feature ∈ Part.ofOption (V.compute program source) := by simpa [IsProgram] using decodes
  have output : selected ∈ describedResidualSearch V code program source := Part.mem_bind decoded finds
  have correct := residualSearch_sound codeSpec finds
  refine ⟨compiler ++ program, ⟨selected, compiles program source selected output, correct.1, correct.2⟩, ?_⟩
  simp [List.length_append, length, Nat.add_comm]

/-- Uniform logarithmic form of IC Theorem 3.4(27), with an actual
terminating residual search supplying the competing descriptive map. -/
theorem shortest_descriptive_logarithmic (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ feature descriptive source,
      ShortestFeature U feature source → ShortestDescriptiveMap U feature descriptive source →
      descriptive.length ≤ 6 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨featureCost, featureBound⟩ := reference_shortest_feature_source_bound U V universal effective reference chain simulations
  obtain ⟨extractorCost, extractorBound⟩ := descriptive_map_from_feature_description U V universal effective reference
  refine ⟨featureCost + extractorCost, fun feature descriptive source minimalFeature minimalMap => ?_⟩
  obtain ⟨competitor, admitted, bounded⟩ := extractorBound feature source minimalFeature.1
  have minimal := minimalMap.2 competitor admitted
  have featureInformation := featureBound source feature minimalFeature
  omega

#print axioms residualSearch_partrec
#print axioms residualSearchStep_sound
#print axioms residualSearchStep_complete
#print axioms residualSearch_sound
#print axioms residualSearch_complete
#print axioms descriptive_map_from_feature_description
#print axioms shortest_descriptive_logarithmic

end KolmogorovComplexity.FeatureTheory
