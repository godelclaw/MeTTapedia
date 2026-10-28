import Mettapedia.Computability.KolmogorovComplexity.FeatureCompressionChain
import Mettapedia.Computability.KolmogorovComplexity.FeatureIncrementalInformation

/-!
# An executable plain description of a feature chain

Franz, Antonenko and Soletskyi, "A theory of incremental compression",
Information Sciences 547 (2021), Section 3.5 and Theorem 3.9,
https://doi.org/10.1016/j.ins.2020.08.035 (arXiv:1908.03781).

This mathematical description uses the shared length-delimited condition code:
a step-count field, the feature frames in execution order, then the raw final
residual. Every header is charged. The count costs linear space in the number
of steps, and bounded features cost constant space per step. The residual is
not doubled or silently assumed self-delimiting. The packet is a complete
plain program, not a prefix-free stream of concatenated packets.

This is not a replacement for the learner's portable artifact format and does
not assert that its bounded search discovers ideal shortest features.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

def packFeatureFrames : List BinString → BinString → BinString
  | [], residual => residual
  | feature :: rest, residual => pairCondition feature (packFeatureFrames rest residual)

abbrev FeatureFrameState := List BinString × BinString

def nextFeatureFrame (state : FeatureFrameState) : Option FeatureFrameState :=
  (unpairCondition state.2).map fun fields => (fields.1 :: state.1, fields.2)

def featureFrameStep (state : Option FeatureFrameState) : Option FeatureFrameState :=
  state.bind nextFeatureFrame

def readFeatureFrames (count : Nat) (input : BinString) : Option FeatureFrameState :=
  ((featureFrameStep^[count]) (some ([], input))).map fun state => (state.1.reverse, state.2)

theorem nextFeatureFrame_primrec : Primrec nextFeatureFrame := by
  exact Primrec.option_map (KraftChaitin.unpairCondition_primrec.comp Primrec.snd)
    ((Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.snd)).to₂

theorem featureFrameStep_primrec : Primrec featureFrameStep :=
  Primrec.option_bind Primrec.id (nextFeatureFrame_primrec.comp Primrec.snd).to₂

theorem readFeatureFrames_primrec : Primrec₂ readFeatureFrames := by
  have loop : Primrec fun input : Nat × BinString =>
      (featureFrameStep^[input.1]) (some ([], input.2)) :=
    Primrec.nat_iterate Primrec.fst
      (Primrec.option_some.comp ((Primrec.const []).pair Primrec.snd))
      (featureFrameStep_primrec.comp Primrec.snd).to₂
  exact Primrec.option_map loop
    ((Primrec.list_reverse.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)).to₂

theorem featureFrameLoop_pack (features accumulator : List BinString) (residual : BinString) :
    (featureFrameStep^[features.length]) (some (accumulator, packFeatureFrames features residual)) =
      some (features.reverse ++ accumulator, residual) := by
  induction features generalizing accumulator with
  | nil => simp [packFeatureFrames]
  | cons feature rest ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, featureFrameStep, Option.bind_some,
        packFeatureFrames, nextFeatureFrame, unpairCondition_pairCondition, Option.map_some]
      rw [ih]
      simp

theorem readFeatureFrames_pack (features : List BinString) (residual : BinString) :
    readFeatureFrames features.length (packFeatureFrames features residual) = some (features, residual) := by
  simp [readFeatureFrames, featureFrameLoop_pack]

def schemeDescription (features : List BinString) (residual : BinString) : BinString :=
  pairCondition (List.replicate features.length false) (packFeatureFrames features.reverse residual)

def decodeSchemeDescription (input : BinString) : Option FeatureFrameState :=
  (unpairCondition input).bind fun fields => readFeatureFrames fields.1.length fields.2

theorem decodeSchemeDescription_primrec : Primrec decodeSchemeDescription := by
  exact Primrec.option_bind KraftChaitin.unpairCondition_primrec
    (readFeatureFrames_primrec.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem decodeSchemeDescription_encode (features : List BinString) (residual : BinString) :
    decodeSchemeDescription (schemeDescription features residual) = some (features.reverse, residual) := by
  simp only [decodeSchemeDescription, schemeDescription, unpairCondition_pairCondition, Option.bind_some,
    List.length_replicate]
  simpa using readFeatureFrames_pack features.reverse residual

theorem schemeDescription_injective : Function.Injective (Function.uncurry schemeDescription) := by
  rintro ⟨features, residual⟩ ⟨otherFeatures, otherResidual⟩ same
  change schemeDescription features residual = schemeDescription otherFeatures otherResidual at same
  have decoded := congrArg decodeSchemeDescription same
  simp only [decodeSchemeDescription_encode, Option.some.injEq, Prod.mk.injEq] at decoded
  exact Prod.ext (List.reverse_injective decoded.1) decoded.2

theorem packFeatureFrames_length (features : List BinString) (residual : BinString) :
    (packFeatureFrames features residual).length =
      residual.length + 2 * (features.map List.length).sum + features.length := by
  induction features with
  | nil => simp [packFeatureFrames]
  | cons feature rest ih =>
      simp only [packFeatureFrames, pairCondition_length, machinePrefix_length, ih,
        List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem schemeDescription_length (features : List BinString) (residual : BinString) :
    (schemeDescription features residual).length =
      residual.length + 2 * (features.map List.length).sum + 3 * features.length + 1 := by
  simp only [schemeDescription, pairCondition_length, machinePrefix_length, List.length_replicate,
    packFeatureFrames_length, List.length_reverse, List.map_reverse, List.sum_reverse]
  omega

theorem schemeDescription_length_le {features : List BinString} (residual : BinString) {budget : Nat}
    (bounded : ∀ feature ∈ features, feature.length ≤ budget) :
    (schemeDescription features residual).length ≤ residual.length + features.length * (2 * budget + 3) + 1 := by
  have sumBound : (features.map List.length).sum ≤ features.length * budget := by
    induction features with
    | nil => simp
    | cons feature rest ih =>
        have first := bounded feature (by simp)
        have later := ih (fun other member => bounded other (by simp [member]))
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
  rw [schemeDescription_length]
  nlinarith

def storedFeatureStep (U : ConditionalAlgorithm) (state : FeatureFrameState) :
    Part (BinString ⊕ FeatureFrameState) :=
  if state.1 = [] then Part.some (Sum.inl state.2)
  else (U (state.1.head?.getD []) state.2).map fun output => Sum.inr (state.1.tail, output)

def runStoredFeatures (U : ConditionalAlgorithm) : FeatureFrameState →. BinString :=
  PFun.fix (storedFeatureStep U)

theorem storedFeatureStep_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec (storedFeatureStep U) := by
  have empty : Computable fun state : FeatureFrameState => decide (state.1 = []) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const [])).decide.to_comp
  have head : Computable fun state : FeatureFrameState => state.1.head?.getD [] :=
    Computable.option_getD (Primrec.list_head?.to_comp.comp Computable.fst) (Computable.const [])
  have runs : Partrec fun state : FeatureFrameState => U (state.1.head?.getD []) state.2 :=
    effective.comp head Computable.snd
  have tag : Computable fun context : FeatureFrameState × BinString =>
      (Sum.inr (context.1.1.tail, context.2) : BinString ⊕ FeatureFrameState) :=
    Computable.sumInr.comp
      ((Primrec.list_tail.to_comp.comp (Computable.fst.comp Computable.fst)).pair Computable.snd)
  have next : Partrec fun state : FeatureFrameState =>
      (U (state.1.head?.getD []) state.2).map fun output =>
        (Sum.inr (state.1.tail, output) : BinString ⊕ FeatureFrameState) :=
    runs.map tag.to₂
  have halt : Computable fun state : FeatureFrameState =>
      (Sum.inl state.2 : BinString ⊕ FeatureFrameState) :=
    Computable.sumInl.comp Computable.snd
  exact (Partrec.cond empty halt.partrec next).of_eq fun state => by
    by_cases h : state.1 = [] <;> simp [storedFeatureStep, h]

theorem runStoredFeatures_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec (runStoredFeatures U) := Partrec.fix (storedFeatureStep_partrec effective)

theorem runStoredFeatures_nil (U : ConditionalAlgorithm) (residual : BinString) :
    residual ∈ runStoredFeatures U ([], residual) := by
  apply PFun.mem_fix_iff.mpr
  exact Or.inl (by simp [storedFeatureStep])

theorem runStoredFeatures_cons {U : ConditionalAlgorithm} {feature initial middle output : BinString}
    {rest : List BinString} (first : middle ∈ U feature initial)
    (later : output ∈ runStoredFeatures U (rest, middle)) :
    output ∈ runStoredFeatures U (feature :: rest, initial) := by
  apply PFun.mem_fix_iff.mpr
  refine Or.inr ⟨(rest, middle), ?_, later⟩
  simpa [storedFeatureStep] using
    Part.mem_map (fun value => (Sum.inr (rest, value) : BinString ⊕ FeatureFrameState)) first

theorem runStoredFeatures_nil_iff (U : ConditionalAlgorithm) (initial output : BinString) :
    output ∈ runStoredFeatures U ([], initial) ↔ output = initial := by
  constructor
  · intro runs
    exact Part.mem_unique runs (runStoredFeatures_nil U initial)
  · rintro rfl
    exact runStoredFeatures_nil U _

theorem runStoredFeatures_cons_iff (U : ConditionalAlgorithm) (feature : BinString)
    (rest : List BinString) (initial output : BinString) :
    output ∈ runStoredFeatures U (feature :: rest, initial) ↔
      ∃ middle, middle ∈ U feature initial ∧ output ∈ runStoredFeatures U (rest, middle) := by
  constructor
  · intro before
    obtain done | ⟨state, transition, later⟩ := PFun.mem_fix_iff.mp before
    · simp [storedFeatureStep] at done
    · have step : Sum.inr state ∈ (U feature initial).map
          (fun value => (Sum.inr (rest, value) : BinString ⊕ FeatureFrameState)) := by
        simpa [storedFeatureStep] using transition
      obtain ⟨middle, computes, same⟩ :=
        (Part.mem_map_iff (fun value => (Sum.inr (rest, value) : BinString ⊕ FeatureFrameState))).mp step
      have stateEq : (rest, middle) = state := Sum.inr.inj same
      subst state
      exact ⟨middle, computes, later⟩
  · rintro ⟨middle, first, later⟩
    exact runStoredFeatures_cons first later

theorem runStoredFeatures_append {U : ConditionalAlgorithm} {first second : List BinString}
    {initial middle output : BinString} (before : middle ∈ runStoredFeatures U (first, initial))
    (after : output ∈ runStoredFeatures U (second, middle)) :
    output ∈ runStoredFeatures U (first ++ second, initial) := by
  induction first generalizing initial with
  | nil =>
      have same := (runStoredFeatures_nil_iff U initial middle).mp before
      simpa [same] using after
  | cons feature rest ih =>
      obtain ⟨next, computes, later⟩ := (runStoredFeatures_cons_iff U feature rest initial middle).mp before
      exact runStoredFeatures_cons computes (ih later)

theorem BChain.stored_reconstructs {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString} (chain : BChain U factor source features final) :
    source ∈ runStoredFeatures U (features.reverse, final) := by
  induction chain with
  | nil source => exact runStoredFeatures_nil U source
  | @cons source residual final feature descriptive features _ reconstructs _ _ _ ih =>
      have last := runStoredFeatures_cons reconstructs (runStoredFeatures_nil U source)
      simpa only [List.reverse_cons] using runStoredFeatures_append ih last

def schemeInterpreter (U : ConditionalAlgorithm) : ConditionalAlgorithm :=
  fun program _condition => (Part.ofOption (decodeSchemeDescription program)).bind (runStoredFeatures U)

theorem schemeInterpreter_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec₂ (schemeInterpreter U) := by
  apply Partrec.bind (decodeSchemeDescription_primrec.to_comp.comp Computable.fst).ofOption
  exact ((runStoredFeatures_partrec effective).comp Computable.snd).to₂

theorem schemeInterpreter_encode_iff (U : ConditionalAlgorithm)
    (features : List BinString) (residual condition output : BinString) :
    output ∈ schemeInterpreter U (schemeDescription features residual) condition ↔
      output ∈ runStoredFeatures U (features.reverse, residual) := by
  change output ∈ (Part.ofOption (decodeSchemeDescription (schemeDescription features residual))).bind
    (runStoredFeatures U) ↔ _
  rw [decodeSchemeDescription_encode]
  constructor
  · intro runs
    obtain ⟨state, selected, result⟩ := Part.mem_bind_iff.mp runs
    have same : state = (features.reverse, residual) := by simpa using selected
    simpa only [same] using result
  · intro result
    exact Part.mem_bind (by simp) result

theorem BChain.scheme_reconstructs {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString} (chain : BChain U factor source features final) :
    source ∈ schemeInterpreter U (schemeDescription features final) [] := by
  exact Part.mem_bind (by simp [decodeSchemeDescription_encode]) chain.stored_reconstructs

theorem scheme_description_complexity_lower (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ overhead : Nat, ∀ factor source final features, BChain U factor source features final →
      plainConditionalComplexity U source [] ≤ (schemeDescription features final).length + overhead := by
  obtain ⟨compiler, compiles⟩ := universal (schemeInterpreter U) (schemeInterpreter_partrec effective)
  refine ⟨compiler.length, fun factor source final features chain => ?_⟩
  have runs := compiles (schemeDescription features final) [] source chain.scheme_reconstructs
  have bound := plainConditionalComplexity_le_of_program U [] source _ runs
  simpa only [List.length_append, Nat.add_comm] using bound

#print axioms readFeatureFrames_primrec
#print axioms nextFeatureFrame_primrec
#print axioms featureFrameStep_primrec
#print axioms featureFrameLoop_pack
#print axioms readFeatureFrames_pack
#print axioms decodeSchemeDescription_primrec
#print axioms decodeSchemeDescription_encode
#print axioms schemeDescription_injective
#print axioms packFeatureFrames_length
#print axioms schemeDescription_length
#print axioms schemeDescription_length_le
#print axioms storedFeatureStep_partrec
#print axioms runStoredFeatures_partrec
#print axioms runStoredFeatures_nil
#print axioms runStoredFeatures_cons
#print axioms runStoredFeatures_nil_iff
#print axioms runStoredFeatures_cons_iff
#print axioms runStoredFeatures_append
#print axioms BChain.stored_reconstructs
#print axioms schemeInterpreter_partrec
#print axioms schemeInterpreter_encode_iff
#print axioms BChain.scheme_reconstructs
#print axioms scheme_description_complexity_lower

end KolmogorovComplexity.FeatureTheory
