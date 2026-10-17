import Mettapedia.Computability.FramedWordPairing
import Mettapedia.Computability.FramedWordMapping
import Mettapedia.Computability.WordHomomorphismMachine
import Mettapedia.GSLT.LanguageDef.CertificateProofTraversal

/-!
# Ordered original source judgments and submitted child proofs

The original binary codecs supply the premise list and the child-proof list.
Both lists execute the original authored-arity framer, and the physical pairing
machine turns their complete fields into ordered child jobs. Either arity
mismatch refuses, including nonempty children for a nullary rule. This stage
prepares jobs; it does not establish the validity of a submitted child proof.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.OriginalChildJobs
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
abbrev Alphabet := Binary.Alphabet
abbrev PairCell := FramedWordPairing.Cell (Γ := Alphabet)
abbrev Field := List Pattern ⊕ List RawOpenProof
local instance : Inhabited PairCell := ⟨.inr false⟩
attribute [local implicit_reducible] FramedWordMapping.machine FramedWordMapping.statement
  CertificateArgumentFraming.Execution.machine WordHomomorphismMachine.machine
  StackMachineComposition.machine FramedWordPairing.machine

def encodeField : Field → List Alphabet
  | .inl goals => encodeWith (Codec.list CertificateDataEncoding.patternCodec) goals
  | .inr children => encodeWith (Codec.list CertificateDataEncoding.proofCodec) children

def fieldWords (arity : Nat) : Field → Option (List (List Alphabet))
  | .inl goals => if goals.length = arity then some (goals.map (encodeWith CertificateDataEncoding.patternCodec)) else none
  | .inr children => if children.length = arity then some (children.map (encodeWith CertificateDataEncoding.proofCodec)) else none

def status (result : Option (List (List Alphabet))) := CertificateArgumentFraming.statusWire (result.map Indexed.frame)
def emitField (arity : Nat) (field : Field) := status (fieldWords arity field)
def fieldClock (field : Field) := 7 * (encodeField field).length + 8

def inputWire (goals : List Pattern) (children : List RawOpenProof) :=
  Indexed.frame [encodeField (.inl goals),encodeField (.inr children)]
def framedWire (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) :=
  Indexed.frame [emitField arity (.inl goals),emitField arity (.inr children)]
def preparedWire (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) :=
  (framedWire arity goals children).map (Sum.inl (β := Bool))
def outputWire (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) :=
  FramedWordPairing.output (fieldWords arity (.inl goals)) (fieldWords arity (.inr children))

local instance (arity : Nat) : Fintype ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₀) := inferInstanceAs (Inhabited Alphabet)
local instance (arity : Nat) : Inhabited ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def framingMachine (arity : Nat) := FramedWordMapping.machine (CertificateArgumentFraming.Execution.machine arity)
attribute [local implicit_reducible] framingMachine
def liftCell (cell : Option (Option Alphabet)) : List PairCell := [.inl cell]
abbrev liftMachine := WordHomomorphismMachine.machine liftCell
local instance (arity : Nat) : Fintype ((framingMachine arity).Γ (framingMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance (arity : Nat) : Inhabited ((framingMachine arity).Γ (framingMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option (Option Alphabet)))
local instance : Fintype (liftMachine.Γ liftMachine.k₁) := inferInstanceAs (Fintype PairCell)
local instance : Inhabited (liftMachine.Γ liftMachine.k₁) := inferInstanceAs (Inhabited PairCell)

def preparedMachine (arity : Nat) := StackMachineComposition.machine (framingMachine arity) liftMachine
  (Equiv.refl (Option (Option Alphabet)))
attribute [local implicit_reducible] preparedMachine
local instance (arity : Nat) : Fintype ((preparedMachine arity).Γ (preparedMachine arity).k₁) := inferInstanceAs (Fintype PairCell)
local instance (arity : Nat) : Inhabited ((preparedMachine arity).Γ (preparedMachine arity).k₁) := inferInstanceAs (Inhabited PairCell)
def machine (arity : Nat) := StackMachineComposition.machine (preparedMachine arity)
  (FramedWordPairing.machine (1 : Alphabet)) (Equiv.refl PairCell)

noncomputable def fieldOutputs (arity : Nat) (field : Field) :
    TM2OutputsInTime (CertificateArgumentFraming.Execution.machine arity) (encodeField field)
      (some (emitField arity field)) (fieldClock field) := by
  cases field with
  | inl goals =>
    simpa [encodeField,emitField,status,fieldWords,CertificateArgumentFraming.Execution.frameAtArity,
      CertificateArgumentFraming.framedArguments,CertificateArgumentFraming.argumentWords,fieldClock] using
      CertificateArgumentFraming.Execution.outputsAtArity CertificateDataEncoding.patternCodec arity goals
  | inr children =>
    simpa [encodeField,emitField,status,fieldWords,CertificateArgumentFraming.Execution.frameAtArity,
      CertificateArgumentFraming.framedArguments,CertificateArgumentFraming.argumentWords,fieldClock] using
      CertificateArgumentFraming.Execution.outputsAtArity CertificateDataEncoding.proofCodec arity children

theorem field_length (arity : Nat) (field : Field) : (emitField arity field).length ≤ (encodeField field).length := by
  cases field with
  | inl goals =>
    simpa [encodeField,emitField,status,fieldWords,CertificateArgumentFraming.Execution.frameAtArity,
      CertificateArgumentFraming.framedArguments,CertificateArgumentFraming.argumentWords] using
      CertificateArgumentFraming.Execution.result_length_le CertificateDataEncoding.patternCodec arity goals
  | inr children =>
    simpa [encodeField,emitField,status,fieldWords,CertificateArgumentFraming.Execution.frameAtArity,
      CertificateArgumentFraming.framedArguments,CertificateArgumentFraming.argumentWords] using
      CertificateArgumentFraming.Execution.result_length_le CertificateDataEncoding.proofCodec arity children

theorem input_length (goals : List Pattern) (children : List RawOpenProof) :
    (inputWire goals children).length = (encodeField (.inl goals)).length + (encodeField (.inr children)).length + 2 := by
  simp [inputWire,Indexed.frame]
  omega

theorem framed_length (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) :
    (framedWire arity goals children).length ≤ (inputWire goals children).length := by
  have left := field_length arity (.inl goals)
  have right := field_length arity (.inr children)
  simp only [framedWire,Indexed.frame,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.length_append,List.length_map,List.length_cons,List.length_nil]
  rw [input_length]
  omega

noncomputable def framingOutputs (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (framingMachine arity) (inputWire goals children)
      (some (framedWire arity goals children)) (11 * (inputWire goals children).length + 10) := by
  have ran := FramedWordMapping.outputs (CertificateArgumentFraming.Execution.machine arity)
    encodeField (emitField arity) fieldClock (fieldOutputs arity) [.inl goals,.inr children]
  change TM2OutputsInTime (framingMachine arity) (inputWire goals children)
    (some (framedWire arity goals children)) _ at ran
  apply WordEqualityMachine.within ran
  rw [FramedWordMapping.totalClock_eq]
  have left := field_length arity (.inl goals)
  have right := field_length arity (.inr children)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,fieldClock]
  rw [input_length]
  omega

noncomputable def preparedOutputs (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (preparedMachine arity) (inputWire goals children)
      (some (preparedWire arity goals children)) (17 * (inputWire goals children).length + 14) := by
  have lifted := WordHomomorphismMachine.outputs liftCell (framedWire arity goals children)
  have same : (framedWire arity goals children).flatMap liftCell = preparedWire arity goals children := by
    unfold preparedWire
    induction framedWire arity goals children <;> simp_all [liftCell]
  rw [same] at lifted
  have ran := StackMachineComposition.outputs (framingMachine arity) liftMachine (Equiv.refl (Option (Option Alphabet)))
    (inputWire goals children) (framedWire arity goals children) (preparedWire arity goals children) _ _
    (framingOutputs arity goals children) (by
      change TM2OutputsInTime liftMachine ((framedWire arity goals children).map id) _ _
      simpa only [List.map_id] using lifted)
  apply WordEqualityMachine.within ran
  have size := framed_length arity goals children
  simp only [preparedWire,List.length_map]
  omega

noncomputable def outputs (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (machine arity) (inputWire goals children) (some (outputWire arity goals children))
      (31 * (inputWire goals children).length + 46) := by
  have paired := FramedWordPairing.outputs (1 : Alphabet) 0 (by decide)
    (fieldWords arity (.inl goals)) (fieldWords arity (.inr children))
  have same : FramedWordPairing.input (1 : Alphabet) 0
      (fieldWords arity (.inl goals)) (fieldWords arity (.inr children)) = preparedWire arity goals children := by
    simp only [FramedWordPairing.input,preparedWire,framedWire,emitField,status,CertificateArgumentFraming.statusWire]
    cases fieldWords arity (.inl goals) <;> cases fieldWords arity (.inr children) <;> rfl
  rw [same] at paired
  have ran := StackMachineComposition.outputs (preparedMachine arity) (FramedWordPairing.machine (1 : Alphabet))
    (Equiv.refl PairCell) (inputWire goals children) (preparedWire arity goals children) (outputWire arity goals children)
    _ _ (preparedOutputs arity goals children) (by
      change TM2OutputsInTime (FramedWordPairing.machine (1 : Alphabet)) ((preparedWire arity goals children).map id) _ _
      simpa only [List.map_id,outputWire] using paired)
  apply WordEqualityMachine.within ran
  have size := framed_length arity goals children
  simp only [preparedWire,List.length_map]
  omega

def readPairs : List (List Alphabet × List Alphabet) → Option (List (Pattern × RawOpenProof))
  | [] => some []
  | pair :: pairs => do
      let decoded ← decodeWith (Codec.prod CertificateDataEncoding.patternCodec CertificateDataEncoding.proofCodec)
        (4 :: pair.1 ++ pair.2)
      let rest ← readPairs pairs
      pure (decoded :: rest)

def readOutput (word : List PairCell) : Option (List (Pattern × RawOpenProof)) := do
  let pairs ← FramedWordPairing.readOutput word
  readPairs pairs

theorem pair_codec (goal : Pattern) (proof : RawOpenProof) :
    decodeWith (Codec.prod CertificateDataEncoding.patternCodec CertificateDataEncoding.proofCodec)
      (4 :: (encodeWith CertificateDataEncoding.patternCodec goal ++ encodeWith CertificateDataEncoding.proofCodec proof)) =
      some (goal,proof) := by
  have encoded : encodeWith (Codec.prod CertificateDataEncoding.patternCodec CertificateDataEncoding.proofCodec) (goal,proof) =
      4 :: (encodeWith CertificateDataEncoding.patternCodec goal ++ encodeWith CertificateDataEncoding.proofCodec proof) := by
    simp [encodeWith,Codec.prod,encodeData_pair]
  rw [← encoded]
  exact decodeWith_encodeWith _ _

theorem readPairs_exact (goals : List Pattern) (children : List RawOpenProof) :
    readPairs ((goals.map (encodeWith CertificateDataEncoding.patternCodec)).zip
      (children.map (encodeWith CertificateDataEncoding.proofCodec))) = some (goals.zip children) := by
  induction goals generalizing children with
  | nil => rfl
  | cons goal goals ih =>
    cases children with
    | nil => rfl
    | cons child children => simp [readPairs,pair_codec,ih]

theorem readOutput_exact (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) :
    readOutput (outputWire arity goals children) =
      if goals.length = arity ∧ children.length = arity then some (goals.zip children) else none := by
  by_cases left : goals.length = arity <;> by_cases right : children.length = arity
  · have same : (goals.map (encodeWith CertificateDataEncoding.patternCodec)).length =
        (children.map (encodeWith CertificateDataEncoding.proofCodec)).length := by simp only [List.length_map]; omega
    simp only [outputWire,fieldWords,if_pos left,if_pos right,FramedWordPairing.output,if_pos same,
      readOutput,FramedWordPairing.readOutput_positive,bind,Option.bind,readPairs_exact]
    simp [left,right]
  · simp [outputWire,fieldWords,left,right,FramedWordPairing.output,readOutput,FramedWordPairing.readOutput_refused]
  · simp [outputWire,fieldWords,left,right,FramedWordPairing.output,readOutput,FramedWordPairing.readOutput_refused]
  · simp [outputWire,fieldWords,left,right,FramedWordPairing.output,readOutput,FramedWordPairing.readOutput_refused]

theorem run_readout (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) {word : List PairCell}
    (finished : TM2Outputs (machine arity) (inputWire goals children) (some word)) :
    word = outputWire arity goals children :=
  StackMachineComposition.outputs_unique finished (outputs arity goals children).toEvalsTo

theorem run_jobs (arity : Nat) (goals : List Pattern) (children : List RawOpenProof) {word : List PairCell}
    (finished : TM2Outputs (machine arity) (inputWire goals children) (some word)) :
    readOutput word = if goals.length = arity ∧ children.length = arity then some (goals.zip children) else none := by
  rw [run_readout arity goals children finished]
  exact readOutput_exact arity goals children

abbrev Input := List Pattern × List RawOpenProof
def result (arity : Nat) (value : Input) := outputWire arity value.1 value.2
noncomputable def realization (arity : Nat) :
    TM2ComputableInPolyTime (fun value : Input => inputWire value.1 value.2) id (result arity) where
  tm := machine arity
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl PairCell
  time := C 31 * X + C 46
  outputsFun value := by
    change TM2OutputsInTime (machine arity) ((inputWire value.1 value.2).map id)
      (some ((outputWire arity value.1 value.2).map id)) _
    simp only [List.map_id,eval_add,eval_mul,eval_C,eval_X]
    exact outputs arity value.1 value.2

namespace Controls
def p : Pattern := .apply "p" []
def q : Pattern := .apply "q" []
theorem ordered_jobs : readOutput (outputWire 2 [p,q] [.premise 1,.premise 0]) =
    some [(p,.premise 1),(q,.premise 0)] := by rw [readOutput_exact]; rfl

theorem repeated_jobs : readOutput (outputWire 2 [p,p] [.premise 1,.premise 1]) =
    some [(p,.premise 1),(p,.premise 1)] := by rw [readOutput_exact]; rfl

theorem nullary_jobs : readOutput (outputWire 0 [] []) = some [] := by rw [readOutput_exact]; rfl

theorem missing_child_refused : readOutput (outputWire 2 [p,q] [.premise 1]) = none := by rw [readOutput_exact]; rfl

theorem extra_nullary_child_refused : readOutput (outputWire 0 [] [.premise 1]) = none := by rw [readOutput_exact]; rfl

end Controls
end Mettapedia.Languages.HOLLight.OriginalChildJobs
