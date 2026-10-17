import Mettapedia.Computability.FramedWordSuffixRemoval
import Mettapedia.Computability.FramedFieldSelection
import Mettapedia.Computability.RetainedWordExecution
import Mettapedia.OSLF.Syntax.BindingWireBinary

/-!
# Physical append of original binary list words

The original list codec has a two-symbol nil terminator. The existing framed
suffix machine checks and removes that terminator from the earlier list.
The later list word remains unchanged. Physical retention and indexed copying
join both words, preserving all original element payloads and occurrences.
A retained actual suffix-check status controls success versus refusal. The
contract concerns original codec images; validating arbitrary list bodies is
an admission operation outside this append stage.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Computability.BinaryListAppend
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
abbrev Alphabet := Binary.Alphabet
abbrev SuffixCell := FramedWordSuffixRemoval.Output (Γ:=Alphabet)
variable {α : Type}

def stem (codec : Codec α) : List α → List Alphabet
  | [] => []
  | value::rest => 4 :: (encodeWith codec value ++ stem codec rest)

theorem encode_cons (codec : Codec α) (value : α) (rest : List α) :
    encodeWith (Codec.list codec) (value::rest) = 4::(encodeWith codec value++encodeWith (Codec.list codec) rest) := by
  simp [encodeWith,Codec.list,Codec.putList,encodeData_pair]

theorem original_suffix (codec : Codec α) (values : List α) :
    encodeWith (Codec.list codec) values = stem codec values ++ [3,2] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    rw [encode_cons,ih]
    simp [stem,List.append_assoc]

theorem original_append (codec : Codec α) (earlier later : List α) :
    stem codec earlier ++ encodeWith (Codec.list codec) later = encodeWith (Codec.list codec) (earlier++later) := by
  induction earlier with
  | nil => rfl
  | cons value rest ih =>
    simp only [stem,List.cons_append,encode_cons]
    simpa only [List.cons_append,List.append_assoc] using congrArg (fun word => 4::(encodeWith codec value++word)) ih

def fields (codec : Codec α) (earlier later : List α) : Fin 2 → List Alphabet :=
  ![encodeWith (Codec.list codec) earlier,encodeWith (Codec.list codec) later]
def inputWire (codec : Codec α) (earlier later : List α) := Indexed.argumentWire (fields codec earlier later)
def stemWire (codec : Codec α) (earlier : List α) := Indexed.frame [stem codec earlier]

theorem input_length (codec : Codec α) (earlier later : List α) :
    (inputWire codec earlier later).length = (stem codec earlier).length+2+
      (encodeWith (Codec.list codec) later).length+2 := by
  simp [inputWire,fields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,original_suffix,Nat.add_assoc]
  omega

def firstSelector : List (Fin 2) := [0]
local instance : Fintype ((FramedFieldSelection.machine (Γ:=Alphabet) firstSelector).Γ
    (FramedFieldSelection.machine (Γ:=Alphabet) firstSelector).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ:=Alphabet) firstSelector).Γ
    (FramedFieldSelection.machine (Γ:=Alphabet) firstSelector).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def checkedSuffixMachine := StackMachineComposition.machine (FramedFieldSelection.machine (Γ:=Alphabet) firstSelector)
  (FramedWordSuffixRemoval.machine (3 : Alphabet) 2) (Equiv.refl (Option Alphabet))
local instance : Fintype (checkedSuffixMachine.Γ checkedSuffixMachine.k₁) := inferInstanceAs (Fintype SuffixCell)
local instance : Inhabited SuffixCell := ⟨.inr false⟩
local instance : Inhabited (checkedSuffixMachine.Γ checkedSuffixMachine.k₁) := inferInstanceAs (Inhabited SuffixCell)

def checkedSuffixClock (codec : Codec α) (earlier later : List α) :=
  20*((inputWire codec earlier later).length+1)+4*((stem codec earlier).length+3)+5

noncomputable def checkedSuffixOutputs (codec : Codec α) (earlier later : List α) :
    TM2OutputsInTime checkedSuffixMachine (inputWire codec earlier later)
      (some (.inr true :: (stemWire codec earlier).map Sum.inl)) (checkedSuffixClock codec earlier later) := by
  have selected := FramedFieldSelection.outputs (Γ:=Alphabet) firstSelector (fields codec earlier later)
  have selectedWord : Indexed.frame (firstSelector.map (fields codec earlier later)) =
      FramedWordSuffixRemoval.source (3 : Alphabet) 2 [stem codec earlier] := by
    simp [firstSelector,fields,FramedWordSuffixRemoval.source,original_suffix]
  rw [selectedWord] at selected
  have stripped := FramedWordSuffixRemoval.outputs (3 : Alphabet) 2 [stem codec earlier]
  have joined := StackMachineComposition.outputs (FramedFieldSelection.machine (Γ:=Alphabet) firstSelector)
    (FramedWordSuffixRemoval.machine (3 : Alphabet) 2) (Equiv.refl (Option Alphabet))
    (inputWire codec earlier later) (FramedWordSuffixRemoval.source (3 : Alphabet) 2 [stem codec earlier])
    (.inr true :: (stemWire codec earlier).map Sum.inl) _ _ selected (by
      change TM2OutputsInTime (FramedWordSuffixRemoval.machine (3 : Alphabet) 2)
        ((FramedWordSuffixRemoval.source (3 : Alphabet) 2 [stem codec earlier]).map id) _ _
      simpa only [List.map_id,stemWire,FramedWordSuffixRemoval.copied] using stripped)
  convert joined using 1
  · rfl
  · simp only [checkedSuffixClock,firstSelector,FramedWordSuffixRemoval.source,Indexed.frame,List.map_cons,List.map_nil,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,List.length_map,List.length_cons,List.length_nil]
    change _ = 20*((inputWire codec earlier later).length+1)+2*((stem codec earlier).length+3)+2+(2*((stem codec earlier).length+3)+3)
    omega

def statusImage : SuffixCell → List Alphabet
  | .inl (some symbol) => [symbol]
  | .inl none => []
  | .inr accepted => [if accepted then 1 else 0]

theorem status_image_exact (word : List Alphabet) :
    (.inr true :: ((word.map some ++ [none]).map Sum.inl)).flatMap statusImage = 1::word := by
  simp only [List.flatMap_cons,List.flatMap_append,List.flatMap_map,statusImage,List.flatMap_nil]
  induction word <;> simp_all

def statusMachine := StackMachineComposition.machine checkedSuffixMachine (WordHomomorphismMachine.machine statusImage)
  (Equiv.refl SuffixCell)

noncomputable def statusOutputs (codec : Codec α) (earlier later : List α) :
    TM2OutputsInTime statusMachine (inputWire codec earlier later) (some ((1 : Alphabet)::stem codec earlier))
      (64*((inputWire codec earlier later).length+1)) := by
  have copied := WordHomomorphismMachine.outputs statusImage (.inr true :: (stemWire codec earlier).map Sum.inl)
  have word : (.inr true :: (stemWire codec earlier).map Sum.inl).flatMap statusImage = (1 : Alphabet)::stem codec earlier := by
    simpa only [stemWire,Indexed.frame,List.flatMap_cons,List.flatMap_nil,List.append_nil] using status_image_exact (stem codec earlier)
  rw [word] at copied
  have joined := StackMachineComposition.outputs checkedSuffixMachine (WordHomomorphismMachine.machine statusImage)
    (Equiv.refl SuffixCell) (inputWire codec earlier later) (.inr true :: (stemWire codec earlier).map Sum.inl)
    ((1 : Alphabet)::stem codec earlier) _ _ (checkedSuffixOutputs codec earlier later) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine statusImage)
        ((.inr true :: (stemWire codec earlier).map Sum.inl).map id) _ _
      simpa only [List.map_id] using copied)
  apply WordEqualityMachine.within joined
  have length := input_length codec earlier later
  simp only [checkedSuffixClock,List.length_cons,List.length_map,stemWire,Indexed.frame,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.length_append,List.length_nil]
  omega

local instance : Fintype (statusMachine.Γ statusMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (statusMachine.Γ statusMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (statusMachine.Γ statusMachine.k₁) := inferInstanceAs (Inhabited Alphabet)

def identityMachine := WordHomomorphismMachine.machine (fun symbol : Alphabet => [symbol])
def acceptStatus (symbol : Alphabet) := decide (symbol=1)
def stripMachine := StackMachineComposition.Dispatch.machine identityMachine acceptStatus []
def rawStemMachine := StackMachineComposition.machine statusMachine stripMachine (Equiv.refl Alphabet)
local instance : Fintype (rawStemMachine.Γ rawStemMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (rawStemMachine.Γ rawStemMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (rawStemMachine.Γ rawStemMachine.k₁) := inferInstanceAs (Inhabited Alphabet)

noncomputable def rawStemOutputs (codec : Codec α) (earlier later : List α) :
    TM2OutputsInTime rawStemMachine (inputWire codec earlier later) (some (stem codec earlier))
      (80*((inputWire codec earlier later).length+1)) := by
  have identity := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol]) (stem codec earlier)
  simp only [List.flatMap_singleton'] at identity
  have stripped := StackMachineComposition.Dispatch.outputs_success identityMachine acceptStatus [] (1 : Alphabet)
    (stem codec earlier) (stem codec earlier) _ (by decide) identity
  have joined := StackMachineComposition.outputs statusMachine stripMachine (Equiv.refl Alphabet)
    (inputWire codec earlier later) ((1 : Alphabet)::stem codec earlier) (stem codec earlier) _ _
    (statusOutputs codec earlier later) (by
      change TM2OutputsInTime stripMachine (((1 : Alphabet)::stem codec earlier).map id) _ _
      simpa only [List.map_id, stripMachine] using stripped)
  apply WordEqualityMachine.within joined
  have length := input_length codec earlier later
  simp only [List.length_cons]
  omega

def retainedMachine := RetainedWordExecution.WithOutput.Framed.machine rawStemMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
local instance : Fintype (retainedMachine.Γ retainedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (retainedMachine.Γ retainedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def retainedFields (codec : Codec α) (earlier later : List α) : Fin 3 → List Alphabet :=
  ![encodeWith (Codec.list codec) earlier,encodeWith (Codec.list codec) later,stem codec earlier]

theorem retained_frame (codec : Codec α) (earlier later : List α) :
    RetainedWordExecution.WithOutput.Framed.outputWord rawStemMachine (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
      (inputWire codec earlier later) (stem codec earlier) = Indexed.argumentWire (retainedFields codec earlier later) := by
  simp [RetainedWordExecution.WithOutput.Framed.outputWord,inputWire,fields,retainedFields,
    Indexed.argumentWire,Indexed.frame,List.finRange_succ,List.append_assoc,
    Function.comp_def]
  rfl

theorem retained_length (codec : Codec α) (earlier later : List α) :
    (Indexed.argumentWire (retainedFields codec earlier later)).length =
      (inputWire codec earlier later).length+(stem codec earlier).length+1 := by
  rw [← retained_frame]
  simp [RetainedWordExecution.WithOutput.Framed.outputWord]
  omega

noncomputable def retainedOutputs (codec : Codec α) (earlier later : List α) :
    TM2OutputsInTime retainedMachine (inputWire codec earlier later)
      (some (Indexed.argumentWire (retainedFields codec earlier later)))
      (128*((inputWire codec earlier later).length+1)) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs rawStemMachine (Equiv.refl (Option Alphabet))
    (Equiv.refl Alphabet) (inputWire codec earlier later) (stem codec earlier) _ (rawStemOutputs codec earlier later)
  rw [retained_frame] at retained
  apply WordEqualityMachine.within retained
  have length := input_length codec earlier later
  omega

def appendPlan : Indexed.Template Alphabet 3 := [.inl 1,.inr 2,.inr 1]
def resultWire (codec : Codec α) (values : List α) : List Alphabet := 1::encodeWith (Codec.list codec) values

theorem appendPlan_exact (codec : Codec α) (earlier later : List α) :
    Indexed.instantiate appendPlan (retainedFields codec earlier later) = resultWire codec (earlier++later) := by
  change (1 : Alphabet) ::
      (stem codec earlier ++ (encodeWith (Codec.list codec) later ++ [])) =
    resultWire codec (earlier ++ later)
  rw [List.append_nil, original_append]
  rfl

def payloadMachine := StackMachineComposition.machine retainedMachine (Indexed.machine appendPlan) (Equiv.refl (Option Alphabet))
local instance : Fintype (payloadMachine.Γ payloadMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (payloadMachine.Γ payloadMachine.k₁) := inferInstanceAs (Inhabited Alphabet)

noncomputable def payloadOutputs (codec : Codec α) (earlier later : List α) :
    TM2OutputsInTime payloadMachine (inputWire codec earlier later) (some (resultWire codec (earlier++later)))
      (192*((inputWire codec earlier later).length+1)) := by
  have copied := Indexed.outputs appendPlan (retainedFields codec earlier later)
  rw [appendPlan_exact] at copied
  have joined := StackMachineComposition.outputs retainedMachine (Indexed.machine appendPlan) (Equiv.refl (Option Alphabet))
    (inputWire codec earlier later) (Indexed.argumentWire (retainedFields codec earlier later))
    (resultWire codec (earlier++later)) _ _ (retainedOutputs codec earlier later) (by
      change TM2OutputsInTime (Indexed.machine appendPlan) ((Indexed.argumentWire (retainedFields codec earlier later)).map id) _ _
      simpa only [List.map_id] using copied)
  apply WordEqualityMachine.within joined
  have length := input_length codec earlier later
  rw [retained_length]
  simp only [appendPlan,List.length_cons,List.length_nil]
  omega

abbrev GuardCell := Sum (Option Alphabet) Bool
def guardMachine := RetainedWordExecution.machine statusMachine acceptStatus
local instance : Fintype (guardMachine.Γ guardMachine.k₁) := inferInstanceAs (Fintype GuardCell)
local instance : Inhabited GuardCell := ⟨.inr false⟩
local instance : Inhabited (guardMachine.Γ guardMachine.k₁) := inferInstanceAs (Inhabited GuardCell)

def restoreImage : GuardCell → List (Option Alphabet)
  | .inl symbol => [symbol]
  | .inr _ => []
-- Supply the dependent alphabet projections expected by composition.
local instance : Fintype ((WordHomomorphismMachine.machine restoreImage).Γ
    (WordHomomorphismMachine.machine restoreImage).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((WordHomomorphismMachine.machine restoreImage).Γ
    (WordHomomorphismMachine.machine restoreImage).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def restoredBody := StackMachineComposition.machine (WordHomomorphismMachine.machine restoreImage)
  payloadMachine (Equiv.refl (Option Alphabet))
local instance : Fintype (restoredBody.Γ restoredBody.k₀) :=
  inferInstanceAs (Fintype GuardCell)
local instance : Fintype (restoredBody.Γ restoredBody.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (restoredBody.Γ restoredBody.k₀) :=
  inferInstanceAs (Inhabited GuardCell)
local instance : Inhabited (restoredBody.Γ restoredBody.k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def acceptGuard : GuardCell → Bool
  | .inr accepted => accepted
  | .inl _ => false
def dispatchMachine := StackMachineComposition.Dispatch.machine restoredBody acceptGuard [(0 : Alphabet)]
def machine := StackMachineComposition.machine guardMachine dispatchMachine (Equiv.refl GuardCell)

theorem restored_word (word : List (Option Alphabet)) : (word.map (Sum.inl : Option Alphabet → GuardCell)).flatMap restoreImage = word := by
  induction word <;> simp_all [restoreImage]

noncomputable def restoredBodyOutputs (codec : Codec α) (earlier later : List α) :
    TM2OutputsInTime restoredBody ((inputWire codec earlier later).map (Sum.inl : Option Alphabet → GuardCell))
      (some (resultWire codec (earlier++later))) (200*((inputWire codec earlier later).length+1)) := by
  have restored := WordHomomorphismMachine.outputs restoreImage ((inputWire codec earlier later).map (Sum.inl : Option Alphabet → GuardCell))
  rw [restored_word] at restored
  have joined := StackMachineComposition.outputs (WordHomomorphismMachine.machine restoreImage) payloadMachine
    (Equiv.refl (Option Alphabet)) ((inputWire codec earlier later).map (Sum.inl : Option Alphabet → GuardCell))
    (inputWire codec earlier later) (resultWire codec (earlier++later)) _ _ restored (by
      change TM2OutputsInTime payloadMachine ((inputWire codec earlier later).map id) _ _
      simpa only [List.map_id] using payloadOutputs codec earlier later)
  apply WordEqualityMachine.within joined
  simp only [List.length_map]
  omega

noncomputable def guardedOutputs (codec : Codec α) (earlier later : List α) :
    TM2OutputsInTime guardMachine (inputWire codec earlier later)
      (some (.inr true :: (inputWire codec earlier later).map (Sum.inl : Option Alphabet → GuardCell)))
      (72*((inputWire codec earlier later).length+1)) := by
  have guarded := RetainedWordExecution.outputs statusMachine acceptStatus (inputWire codec earlier later)
    (1 : Alphabet) (stem codec earlier) _ (statusOutputs codec earlier later)
  have accepted : acceptStatus 1 = true := by decide
  rw [accepted] at guarded
  apply WordEqualityMachine.within guarded
  have length := input_length codec earlier later
  omega

/-- Complete original list append, with a physically earned guard rather
than a caller-supplied correctness flag. -/
noncomputable def outputs (codec : Codec α) (earlier later : List α) :
    TM2OutputsInTime machine (inputWire codec earlier later) (some (resultWire codec (earlier++later)))
      (288*((inputWire codec earlier later).length+1)) := by
  have dispatched := StackMachineComposition.Dispatch.outputs_success restoredBody acceptGuard [(0 : Alphabet)]
    (.inr true : GuardCell) ((inputWire codec earlier later).map (Sum.inl : Option Alphabet → GuardCell))
    (resultWire codec (earlier++later)) _ rfl (restoredBodyOutputs codec earlier later)
  have joined := StackMachineComposition.outputs guardMachine dispatchMachine (Equiv.refl GuardCell)
    (inputWire codec earlier later) (.inr true :: (inputWire codec earlier later).map (Sum.inl : Option Alphabet → GuardCell))
    (resultWire codec (earlier++later)) _ _ (guardedOutputs codec earlier later) (by
      change TM2OutputsInTime dispatchMachine ((.inr true :: (inputWire codec earlier later).map (Sum.inl : Option Alphabet → GuardCell)).map id) _ _
      simpa only [List.map_id, dispatchMachine] using dispatched)
  apply WordEqualityMachine.within joined
  simp only [List.length_cons,List.length_map]
  omega

def readResult (codec : Codec α) : List Alphabet → Option (List α)
  | 1::body => decodeWith (Codec.list codec) body
  | _ => none

theorem result_readout (codec : Codec α) (values : List α) : readResult codec (resultWire codec values) = some values :=
  decodeWith_encodeWith _ _

theorem run_decodes (codec : Codec α) (earlier later : List α) {word : List Alphabet}
    (finished : TM2Outputs machine (inputWire codec earlier later) (some word)) :
    readResult codec word = some (earlier++later) := by
  have same := StackMachineComposition.outputs_unique finished (outputs codec earlier later).toEvalsTo
  rw [same,result_readout]

noncomputable def realization (codec : Codec α) : TM2ComputableInPolyTime
    (fun pair : List α × List α => inputWire codec pair.1 pair.2) (resultWire codec) (fun pair => pair.1++pair.2) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C 288*(Polynomial.X+Polynomial.C 1)
  outputsFun pair := by
    change TM2OutputsInTime machine ((inputWire codec pair.1 pair.2).map id)
      (some ((resultWire codec (pair.1++pair.2)).map id)) _
    simp only [List.map_id,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X]
    exact outputs codec pair.1 pair.2

/-- This is the actual dispatch cleanup path, not list-body admission. -/
def dispatch_refused (input : List GuardCell) :
    TM2OutputsInTime dispatchMachine (.inr false :: input)
      (some [(0 : Alphabet)]) (input.length + 2) := by
  simpa only [dispatchMachine] using
    StackMachineComposition.Dispatch.outputs_refused restoredBody acceptGuard
      [(0 : Alphabet)] (.inr false) input rfl

/-- A payload symbol cannot impersonate an earned success status. -/
def dispatch_payload_refused (cell : Option Alphabet) (input : List GuardCell) :
    TM2OutputsInTime dispatchMachine (.inl cell :: input)
      (some [(0 : Alphabet)]) (input.length + 2) := by
  simpa only [dispatchMachine] using
    StackMachineComposition.Dispatch.outputs_refused restoredBody acceptGuard
      [(0 : Alphabet)] (.inl cell) input rfl

def dispatch_missing_status :
    TM2OutputsInTime dispatchMachine [] (some [(0 : Alphabet)]) 2 := by
  simpa only [dispatchMachine] using
    StackMachineComposition.Dispatch.outputs_empty restoredBody acceptGuard
      [(0 : Alphabet)]

namespace Controls
theorem repeated_ordered_elements : readResult Codec.nat (resultWire Codec.nat ([7,7,1]++[2,7])) = some [7,7,1,2,7] :=
  result_readout _ _
theorem empty_success_distinct : readResult Codec.nat (resultWire Codec.nat []) = some [] ∧
    readResult Codec.nat [0] = none := ⟨result_readout _ _,rfl⟩
theorem changed_element_rejected : readResult Codec.nat (resultWire Codec.nat [7,7,1,2,7]) ≠ some [7,7,1,3,7] := by
  rw [result_readout]; decide +kernel
end Controls
end Mettapedia.Computability.BinaryListAppend
