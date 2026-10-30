import Mettapedia.Computability.KolmogorovComplexity.FeatureSchemeCodec
import Mettapedia.Computability.KolmogorovComplexity.FeatureResidualSearch
import Mettapedia.Algorithms.Compression.FairSearch

/-!
# Global effective search over competing autoencoder compositions

Franz, Antonenko and Soletskyi, "A theory of incremental compression",
Information Sciences 547 (2021), Section 4, doi:10.1016/j.ins.2020.08.035.

Every residual retains an enumerator of all descriptive/feature program pairs.
Trials use the shared effective conditional interpreter, retain an extracted
residual while testing reconstruction, and spawn another enumerator only after
both computations and strict shortening have succeeded. Failed and indefinitely
running trials coexist with later trials and deeper searches.

The operational scheduler is the proved eight-turn cost/age queue. This module
does not identify that policy with the paper's dyadic phases. In particular,
`Code.evaln` is a bounded evaluator stage, not a count of Turing-machine steps;
no paper running-time bound follows from the stage count below.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory.GlobalSearch

open Mettapedia.Algorithms.Compression

def evaluate (code : Nat.Partrec.Code) (program condition : BinString) (stage : Nat) : Option BinString :=
  (Nat.Partrec.Code.evaln stage code (Encodable.encode (program, condition))).bind Encodable.decode

theorem evaluate_mono (code : Nat.Partrec.Code) (program condition : BinString)
    {first second : Nat} (later : first ≤ second) {output : BinString}
    (found : evaluate code program condition first = some output) :
    evaluate code program condition second = some output := by
  unfold evaluate at found ⊢
  obtain ⟨raw, computed, decoded⟩ := Option.bind_eq_some_iff.mp found
  have persists := Nat.Partrec.Code.evaln_mono later (show raw ∈
    Nat.Partrec.Code.evaln first code (Encodable.encode (program, condition)) from computed)
  rw [show Nat.Partrec.Code.evaln second code (Encodable.encode (program, condition)) = some raw from persists]
  exact decoded

theorem evaluate_sound {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {program condition output : BinString} {stage : Nat}
    (found : evaluate code program condition stage = some output) : output ∈ U program condition := by
  unfold evaluate at found
  obtain ⟨raw, computed, decoded⟩ := Option.bind_eq_some_iff.mp found
  have runs := Nat.Partrec.Code.evaln_sound (show raw ∈
    Nat.Partrec.Code.evaln stage code (Encodable.encode (program, condition)) from computed)
  rw [codeSpec] at runs
  have mapped : raw ∈ (U program condition).map Encodable.encode := by
    simpa [encodedConditionalAlgorithm] using runs
  obtain ⟨value, computes, same⟩ := (Part.mem_map_iff Encodable.encode).mp mapped
  have equal : value = output := by
    simpa only [← same, Encodable.encodek, Option.some.injEq] using decoded
  simpa only [equal] using computes

theorem evaluate_complete {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {program condition output : BinString} (runs : output ∈ U program condition) :
    ∃ stage, evaluate code program condition stage = some output := by
  have computed : Encodable.encode output ∈ Nat.Partrec.Code.eval code (Encodable.encode (program, condition)) := by
    rw [codeSpec]
    simpa [encodedConditionalAlgorithm] using Part.mem_map Encodable.encode runs
  obtain ⟨stage, bounded⟩ := Nat.Partrec.Code.evaln_complete.mp computed
  refine ⟨stage, ?_⟩
  simp only [evaluate, show Nat.Partrec.Code.evaln stage code (Encodable.encode (program, condition)) =
    some (Encodable.encode output) from bounded, Option.bind_some, Encodable.encodek]

structure Frame where
  residual : BinString
  features : List BinString
  deriving DecidableEq, Repr

def Frame.root (source : BinString) : Frame := ⟨source, []⟩

def Frame.extend (frame : Frame) (feature residual : BinString) : Frame :=
  ⟨residual, frame.features ++ [feature]⟩

def Frame.description (frame : Frame) : BinString := schemeDescription frame.features frame.residual

def Frame.Valid (U : ConditionalAlgorithm) (source : BinString) (frame : Frame) : Prop :=
  source ∈ runStoredFeatures U (frame.features.reverse, frame.residual)

theorem root_valid (U : ConditionalAlgorithm) (source : BinString) : (Frame.root source).Valid U source :=
  runStoredFeatures_nil U source

theorem extend_valid {U : ConditionalAlgorithm} {source : BinString} {frame : Frame}
    (valid : frame.Valid U source) {feature residual : BinString}
    (reconstructs : frame.residual ∈ U feature residual) : (frame.extend feature residual).Valid U source := by
  simpa [Frame.Valid, Frame.extend] using runStoredFeatures_cons reconstructs valid

theorem valid_description {U : ConditionalAlgorithm} {source : BinString} {frame : Frame}
    (valid : frame.Valid U source) : source ∈ schemeInterpreter U frame.description [] :=
  (schemeInterpreter_encode_iff U frame.features frame.residual [] source).mpr valid

inductive Node where
  | enumerate (frame : Frame) (rank : Nat)
  | extract (frame : Frame) (descriptive feature : BinString) (stage : Nat)
  | rebuild (frame : Frame) (descriptive feature residual : BinString) (stage : Nat)
  | found (frame : Frame) (descriptive feature residual : BinString)
  deriving DecidableEq, Repr

def successors (code : Nat.Partrec.Code) : Node → List Node
  | .enumerate frame rank =>
      .enumerate frame (rank + 1) ::
        ((Encodable.decode (α := BinString × BinString) rank).map
          fun pair => Node.extract frame pair.1 pair.2 0).toList
  | .extract frame descriptive feature stage =>
      match evaluate code descriptive frame.residual stage with
      | none => [.extract frame descriptive feature (stage + 1)]
      | some residual =>
          if feature.length + residual.length < frame.residual.length then
            [.rebuild frame descriptive feature residual 0] else []
  | .rebuild frame descriptive feature residual stage =>
      match evaluate code feature residual stage with
      | none => [.rebuild frame descriptive feature residual (stage + 1)]
      | some output => if output = frame.residual then [.found frame descriptive feature residual] else []
  | .found frame _descriptive feature residual => [.enumerate (frame.extend feature residual) 0]

def emit : Node → Option Frame
  | .found frame _descriptive feature residual => some (frame.extend feature residual)
  | _ => none

def priority : Node → Nat
  | .enumerate frame rank => frame.features.length + rank
  | .extract frame descriptive feature _stage
  | .rebuild frame descriptive feature _residual _stage
  | .found frame descriptive feature _residual =>
      frame.features.length + descriptive.length + feature.length

def Legal (U : ConditionalAlgorithm) (source : BinString) : Node → Prop
  | .enumerate frame _rank | .extract frame _descriptive _feature _stage => frame.Valid U source
  | .rebuild frame descriptive feature residual _stage =>
      frame.Valid U source ∧ residual ∈ U descriptive frame.residual ∧
        feature.length + residual.length < frame.residual.length
  | .found frame descriptive feature residual =>
      frame.Valid U source ∧ residual ∈ U descriptive frame.residual ∧
        frame.residual ∈ U feature residual ∧ feature.length + residual.length < frame.residual.length

theorem successor_legal {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {source : BinString} {node next : Node} (legal : Legal U source node)
    (member : next ∈ successors code node) : Legal U source next := by
  cases node with
  | enumerate frame rank =>
      cases decoded : Encodable.decode (α := BinString × BinString) rank with
      | none =>
          simp [successors, decoded] at member
          subst next
          exact legal
      | some pair =>
          simp [successors, decoded] at member
          rcases member with rfl | rfl <;> exact legal
  | extract frame descriptive feature stage =>
      cases result : evaluate code descriptive frame.residual stage with
      | none => simp only [successors, result, List.mem_singleton] at member; subst next; exact legal
      | some residual =>
          by_cases shorter : feature.length + residual.length < frame.residual.length
          · simp only [successors, result, if_pos shorter, List.mem_singleton] at member
            subst next
            exact ⟨legal, evaluate_sound codeSpec result, shorter⟩
          · simp [successors, result, shorter] at member
  | rebuild frame descriptive feature residual stage =>
      cases result : evaluate code feature residual stage with
      | none => simp only [successors, result, List.mem_singleton] at member; subst next; exact legal
      | some output =>
          by_cases same : output = frame.residual
          · simp only [successors, result, if_pos same, List.mem_singleton] at member
            subst next
            exact ⟨legal.1, legal.2.1, same ▸ evaluate_sound codeSpec result, legal.2.2⟩
          · simp [successors, result, same] at member
  | found frame descriptive feature residual =>
      simp only [successors, List.mem_singleton] at member
      subst next
      exact extend_valid legal.1 legal.2.2.1

abbrev Reaches (code : Nat.Partrec.Code) :=
  Relation.ReflTransGen (fun node next => next ∈ successors code node)

theorem reaches_legal {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {source : BinString} {node next : Node} (legal : Legal U source node)
    (path : Reaches code node next) : Legal U source next := by
  induction path with
  | refl => exact legal
  | tail _ member ih => exact successor_legal codeSpec ih member

theorem emitted_description_sound {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (source : BinString) {node : Node} (path : Reaches code (.enumerate (.root source) 0) node)
    {frame : Frame} (emitted : emit node = some frame) :
    source ∈ schemeInterpreter U frame.description [] := by
  have rootLegal : Legal U source (.enumerate (.root source) 0) := root_valid U source
  have legal := reaches_legal codeSpec rootLegal path
  cases node <;> simp only [emit] at emitted
  case found previous descriptive feature residual =>
    cases Option.some.inj emitted
    exact valid_description (extend_valid legal.1 legal.2.2.1)

theorem enumerate_reaches (code : Nat.Partrec.Code) (frame : Frame) (rank : Nat) :
    Reaches code (.enumerate frame 0) (.enumerate frame rank) := by
  induction rank with
  | zero => exact .refl
  | succ rank ih => exact ih.tail (by simp [successors])

theorem enumerate_reaches_pair (code : Nat.Partrec.Code) (frame : Frame)
    (descriptive feature : BinString) :
    Reaches code (.enumerate frame 0) (.extract frame descriptive feature 0) := by
  exact (enumerate_reaches code frame (Encodable.encode (descriptive, feature))).tail
    (by simp [successors])

theorem extract_reaches_result (code : Nat.Partrec.Code) (frame : Frame)
    (descriptive feature residual : BinString) (stage extra : Nat)
    (found : evaluate code descriptive frame.residual (stage + extra) = some residual)
    (shorter : feature.length + residual.length < frame.residual.length) :
    Reaches code (.extract frame descriptive feature stage) (.rebuild frame descriptive feature residual 0) := by
  induction extra generalizing stage with
  | zero => exact .single (by simpa [successors, found, shorter] using shorter)
  | succ extra ih =>
      cases current : evaluate code descriptive frame.residual stage with
      | none =>
          have first : Reaches code (.extract frame descriptive feature stage)
              (.extract frame descriptive feature (stage + 1)) := .single (by simp [successors, current])
          exact first.trans (ih (stage + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found))
      | some earlier =>
          have persists := evaluate_mono code descriptive frame.residual (Nat.le_add_right stage (extra + 1)) current
          have equal := Option.some.inj (persists.symm.trans found)
          subst earlier
          exact .single (by simp [successors, current, shorter])

theorem rebuild_reaches_result (code : Nat.Partrec.Code) (frame : Frame)
    (descriptive feature residual : BinString) (stage extra : Nat)
    (found : evaluate code feature residual (stage + extra) = some frame.residual) :
    Reaches code (.rebuild frame descriptive feature residual stage) (.found frame descriptive feature residual) := by
  induction extra generalizing stage with
  | zero => exact .single (by simpa [successors, found])
  | succ extra ih =>
      cases current : evaluate code feature residual stage with
      | none =>
          have first : Reaches code (.rebuild frame descriptive feature residual stage)
              (.rebuild frame descriptive feature residual (stage + 1)) := .single (by simp [successors, current])
          exact first.trans (ih (stage + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found))
      | some earlier =>
          have persists := evaluate_mono code feature residual (Nat.le_add_right stage (extra + 1)) current
          have equal := Option.some.inj (persists.symm.trans found)
          subst earlier
          exact .single (by simp [successors, current])

theorem step_reaches_emission {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (frame : Frame) (step : CompressionStep U frame.residual) :
    Reaches code (.enumerate frame 0)
      (.found frame step.descriptiveProgram step.featureProgram step.residual) := by
  obtain ⟨mapStage, mapFound⟩ := evaluate_complete codeSpec step.extracts
  obtain ⟨featureStage, featureFound⟩ := evaluate_complete codeSpec step.reconstructs
  exact (enumerate_reaches_pair code frame step.descriptiveProgram step.featureProgram).trans
    ((extract_reaches_result code frame step.descriptiveProgram step.featureProgram step.residual
      0 mapStage mapFound step.compresses).trans
        (rebuild_reaches_result code frame step.descriptiveProgram step.featureProgram step.residual
          0 featureStage featureFound))

theorem step_reaches_child {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (frame : Frame) (step : CompressionStep U frame.residual) :
    Reaches code (.enumerate frame 0) (.enumerate (frame.extend step.featureProgram step.residual) 0) :=
  (step_reaches_emission codeSpec frame step).tail (by simp [successors])

theorem bChain_reaches_child {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {factor : ℝ} {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (prefix : List BinString) :
    Reaches code (.enumerate ⟨source, prefix⟩ 0) (.enumerate ⟨final, prefix ++ features⟩ 0) := by
  induction chain generalizing prefix with
  | nil source => simpa using (Relation.ReflTransGen.refl (a := Node.enumerate ⟨source, prefix⟩ 0))
  | @cons source residual final feature descriptive features extracts reconstructs smaller _ _ ih =>
      let step : CompressionStep U source := ⟨feature, descriptive, residual, extracts, reconstructs, smaller⟩
      have first := step_reaches_child codeSpec ⟨source, prefix⟩ step
      have later := ih (prefix ++ [feature])
      simpa [step, Frame.extend, List.append_assoc] using first.trans later

theorem bChain_reaches_emission {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {factor : ℝ} {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (nonempty : features ≠ []) (prefix : List BinString) :
    ∃ node, Reaches code (.enumerate ⟨source, prefix⟩ 0) node ∧
      emit node = some ⟨final, prefix ++ features⟩ := by
  induction chain generalizing prefix with
  | nil source => exact (nonempty rfl).elim
  | @cons source residual final feature descriptive features extracts reconstructs smaller _ later ih =>
      let step : CompressionStep U source := ⟨feature, descriptive, residual, extracts, reconstructs, smaller⟩
      cases features with
      | nil =>
          cases later
          exact ⟨_, step_reaches_emission codeSpec ⟨source, prefix⟩ step, rfl⟩
      | cons next rest =>
          obtain ⟨node, reached, emitted⟩ := ih (by simp) (prefix ++ [feature])
          refine ⟨node, (step_reaches_child codeSpec ⟨source, prefix⟩ step).trans reached, ?_⟩
          simpa [List.append_assoc] using emitted

end KolmogorovComplexity.FeatureTheory.GlobalSearch
