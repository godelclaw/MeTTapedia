import Mettapedia.Languages.HOLLight.ArgumentVectorRendering
import Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming

/-!
# Original argument lists admitted and rendered by one machine

The input is the original binary `Codec.list patternCodec` word. The original
framer checks the authored arity before the existing vector machine admits
and renders each field. An explicit final status distinguishes wrong arity
from a successful empty vector; individual argument refusals keep their
positions. Every copy, dispatch, status emission and cleanup is charged.
The qualified domain includes every original encoded Pattern list, including
wrong arities and invalid scope. Arbitrary malformed source bytes require
their separate codec admission theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.HOLLight.ArgumentListRendering
open Turing Polynomial StateTransition
open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
open ArgumentRenderingMachine

open Mettapedia.GSLT.LanguageDef

local instance : Fintype (ArgumentVectorRendering.machine.Γ ArgumentVectorRendering.machine.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (ArgumentVectorRendering.machine.Γ ArgumentVectorRendering.machine.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity : Nat) : Fintype ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def input (patterns : List Pattern) : List Alphabet :=
  encodeWith (Codec.list patternCodec) patterns

def statusTemplate : WordTemplateMachine.Template (Option Alphabet) := [some (some 1), none]

def successMachine : FinTM2 := StackMachineComposition.machine ArgumentVectorRendering.machine
  (WordTemplateMachine.machine statusTemplate) (Equiv.refl (Option Alphabet))

def accept (tag : Option Alphabet) : Bool := decide (tag = some 1)

def dispatched : FinTM2 := StackMachineComposition.Dispatch.machine successMachine accept [some 0]

def machine (arity : Nat) : FinTM2 := StackMachineComposition.machine
  (CertificateArgumentFraming.Execution.machine arity) dispatched (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] ArgumentVectorRendering.machine successMachine dispatched
  WordTemplateMachine.machine CertificateArgumentFraming.Execution.machine
  StackMachineComposition.machine StackMachineComposition.Dispatch.machine FramedWordMapping.machine

def middle (arity : Nat) (patterns : List Pattern) : List (Option Alphabet) :=
  CertificateArgumentFraming.statusWire (CertificateArgumentFraming.Execution.frameAtArity patternCodec arity patterns)

def output (arity : Nat) (patterns : List Pattern) : List (Option Alphabet) :=
  CertificateArgumentFraming.statusWire (if patterns.length = arity then some (ArgumentVectorRendering.output patterns) else none)

def successClock (patterns : List Pattern) : Nat :=
  ArgumentVectorRendering.clock patterns + 14 * (ArgumentVectorRendering.output patterns).length + 14

def laterClock (arity : Nat) (patterns : List Pattern) : Nat :=
  if patterns.length = arity then successClock patterns + 1 else 2

def clock (arity : Nat) (patterns : List Pattern) : Nat :=
  7 * (input patterns).length + 8 + 2 * (middle arity patterns).length + 2 + laterClock arity patterns

theorem frame_eq (patterns : List Pattern) :
    CertificateArgumentFraming.framedArguments patternCodec patterns = ArgumentVectorRendering.input patterns := rfl

noncomputable def successOutputs (patterns : List Pattern) :
    TM2OutputsInTime successMachine (ArgumentVectorRendering.input patterns)
      (some (some 1 :: ArgumentVectorRendering.output patterns)) (successClock patterns) := by
  have tagged := WordTemplateMachine.outputs statusTemplate (ArgumentVectorRendering.output patterns)
  simp only [statusTemplate, List.length_cons, List.length_nil,
    WordTemplateMachine.instantiate_literal, WordTemplateMachine.instantiate_hole,
    WordTemplateMachine.instantiate_nil, List.append_nil] at tagged
  have joined := StackMachineComposition.outputs ArgumentVectorRendering.machine
    (WordTemplateMachine.machine statusTemplate) (Equiv.refl (Option Alphabet)) (ArgumentVectorRendering.input patterns)
    (ArgumentVectorRendering.output patterns) (some 1 :: ArgumentVectorRendering.output patterns) (ArgumentVectorRendering.clock patterns)
    (12 * ((ArgumentVectorRendering.output patterns).length + 1)) (ArgumentVectorRendering.outputs patterns)
    (by
      change TM2OutputsInTime (WordTemplateMachine.machine statusTemplate)
        ((ArgumentVectorRendering.output patterns).map id)
        (some (some 1 :: ArgumentVectorRendering.output patterns)) _
      simpa only [List.map_id, statusTemplate] using tagged)
  change EvalsToInTime _ _ _ _
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by unfold successClock; omega)⟩

noncomputable def laterOutputs (arity : Nat) (patterns : List Pattern) :
    TM2OutputsInTime dispatched (middle arity patterns)
      (some (output arity patterns)) (laterClock arity patterns) := by
  by_cases admitted : patterns.length = arity
  · simpa only [dispatched, middle, output, laterClock, CertificateArgumentFraming.Execution.frameAtArity,
      if_pos admitted, CertificateArgumentFraming.statusWire, frame_eq] using
      StackMachineComposition.Dispatch.outputs_success successMachine accept [some 0]
        (some (1 : Alphabet)) (ArgumentVectorRendering.input patterns)
        (some (1 : Alphabet) :: ArgumentVectorRendering.output patterns)
        (successClock patterns) (by decide) (successOutputs patterns)
  · simpa only [dispatched, middle, output, laterClock, CertificateArgumentFraming.Execution.frameAtArity,
      if_neg admitted, CertificateArgumentFraming.statusWire, List.length_nil, Nat.zero_add] using
      StackMachineComposition.Dispatch.outputs_refused successMachine accept [some 0]
        (some (0 : Alphabet)) [] (by decide)

/-- The original serialized list, its arity check and every argument share
one physical execution. Both arity-refusal and field-refusal paths halt. -/
noncomputable def outputs (arity : Nat) (patterns : List Pattern) :
    TM2OutputsInTime (machine arity) (input patterns)
      (some (output arity patterns)) (clock arity patterns) :=
  StackMachineComposition.outputs (CertificateArgumentFraming.Execution.machine arity) dispatched
    (Equiv.refl (Option Alphabet)) (input patterns) (middle arity patterns) (output arity patterns)
    (7 * (input patterns).length + 8) (laterClock arity patterns)
    (CertificateArgumentFraming.Execution.outputsAtArity patternCodec arity patterns)
    (by
      change TM2OutputsInTime dispatched ((middle arity patterns).map id)
        (some (output arity patterns)) _
      simpa only [List.map_id] using laterOutputs arity patterns)

theorem vector_input_length (patterns : List Pattern) :
    (ArgumentVectorRendering.input patterns).length + 2 = (input patterns).length :=
  CertificateArgumentFraming.framedArguments_length patternCodec patterns

theorem vector_output_length (patterns : List Pattern) :
    (ArgumentVectorRendering.output patterns).length ≤ 7401 * (ArgumentVectorRendering.input patterns).length := by
  induction patterns with
  | nil => simp [ArgumentVectorRendering.input, ArgumentVectorRendering.output, WordTemplateMachine.Indexed.frame]
  | cons pattern rest ih =>
      have field := ArgumentVectorRendering.field_length pattern
      have inLength : (ArgumentVectorRendering.input (pattern :: rest)).length =
          (patternWire pattern).length + 1 + (ArgumentVectorRendering.input rest).length := by
        simp [ArgumentVectorRendering.input, WordTemplateMachine.Indexed.frame, List.length_append]
        omega
      have outLength : (ArgumentVectorRendering.output (pattern :: rest)).length =
          (AdmittedArgumentRendering.output pattern).length + 1 + (ArgumentVectorRendering.output rest).length := by
        simp [ArgumentVectorRendering.output, WordTemplateMachine.Indexed.frame, List.length_append]
        omega
      rw [inLength, outLength]
      omega

theorem clock_polynomial (arity : Nat) (patterns : List Pattern) :
    clock arity patterns ≤ 3000200000 * ((input patterns).length + 1)^3 := by
  have middleBound := CertificateArgumentFraming.Execution.result_length_le patternCodec arity patterns
  change (middle arity patterns).length ≤ (input patterns).length at middleBound
  have inLength := vector_input_length patterns
  have outLength := vector_output_length patterns
  have vectorTime := ArgumentVectorRendering.clock_polynomial patterns
  have monotone : ((ArgumentVectorRendering.input patterns).length + 1)^3 ≤ ((input patterns).length + 1)^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have linear : (input patterns).length + 1 ≤ ((input patterns).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  unfold clock laterClock successClock
  split <;> nlinarith

noncomputable def realization (arity : Nat) :
    TM2ComputableInPolyTime input (output arity) (id : List Pattern → List Pattern) where
  tm := machine arity
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl (Option Alphabet)
  time := C 3000200000 * (X + C 1)^3
  outputsFun patterns := by
    change TM2OutputsInTime (machine arity) ((input patterns).map id)
      (some ((output arity patterns).map id)) _
    simp only [List.map_id_fun]
    have executed := outputs arity patterns
    refine ⟨executed.toEvalsTo, ?_⟩
    simpa only [eval_mul, eval_pow, eval_add, eval_X, eval_C] using
      executed.steps_le_m.trans (clock_polynomial arity patterns)

theorem run_output_eq {arity : Nat} {patterns : List Pattern} {word : List (Option Alphabet)}
    (run : TM2Outputs (machine arity) (input patterns) (some word)) :
    word = output arity patterns :=
  StackMachineComposition.outputs_unique run (outputs arity patterns).toTM2Outputs

/-- The outer option rejects malformed output. The middle option records
arity refusal, and inner options retain individual argument refusals. -/
def decodeOutput (word : List (Option Alphabet)) : Option (Option (List (Option CanonicalTerm))) :=
  match CertificateArgumentFraming.readStatus word with
  | none => none
  | some none => some none
  | some (some fields) => (ArgumentVectorRendering.decodeOutput fields).map some

theorem decode_output (arity : Nat) (patterns : List Pattern) :
    decodeOutput (output arity patterns) = some (if patterns.length = arity then
      some (patterns.map fun pattern => if argumentValidAt 0 pattern then
        some (renderedArgument pattern) else none) else none) := by
  by_cases admitted : patterns.length = arity
  · simp only [output, if_pos admitted, decodeOutput,
      CertificateArgumentFraming.readStatus_statusWire,
      ArgumentVectorRendering.decode_output, Option.map_some]
  · simp only [output, if_neg admitted, decodeOutput,
      CertificateArgumentFraming.readStatus_statusWire]

theorem run_decodes {arity : Nat} {patterns : List Pattern} {word : List (Option Alphabet)}
    (run : TM2Outputs (machine arity) (input patterns) (some word)) :
    decodeOutput word = some (if patterns.length = arity then
      some (patterns.map fun pattern => if argumentValidAt 0 pattern then
        some (renderedArgument pattern) else none) else none) := by
  rw [run_output_eq run, decode_output]

theorem finiteAlphabet (arity : Nat) (key : (machine arity).K) :
    Finite ((machine arity).Γ key) := by
  have later : ∀ key, Finite (dispatched.Γ key) := by
    intro key
    cases key with
    | none => exact inferInstanceAs (Finite (Option Alphabet))
    | some key => cases key with
      | inl key => exact ArgumentVectorRendering.finiteAlphabet key
      | inr key => exact inferInstanceAs (Finite (Option Alphabet))
  cases key with
  | none => exact inferInstanceAs (Finite (Option Alphabet))
  | some key => cases key with
    | inl key => exact inferInstanceAs (Finite (CertificateArgumentFraming.Execution.Cells key))
    | inr key => exact later key

namespace Controls

theorem empty_success : output 0 [] = [some 1] := rfl
theorem empty_wrong_arity : output 1 [] = [some 0] := rfl
theorem missing_argument : decodeOutput (output 2 [.apply "Z" []]) = some none := by
  rw [decode_output]; rfl
theorem excess_argument : decodeOutput (output 0 [.apply "Z" []]) = some none := by
  rw [decode_output]; rfl
theorem bad_scope_retains_position :
    decodeOutput (output 3 [.apply "Z" [], .bvar 0, .apply "Z" []]) =
      some (some [some (renderedArgument (.apply "Z" [])), none,
        some (renderedArgument (.apply "Z" []))]) := by
  rw [decode_output]; rfl
theorem bad_scope_is_not_arity_refusal : output 1 [.bvar 0] = [some 1, none] := by decide
theorem malformed_status_refused : decodeOutput [none] = none := rfl
theorem malformed_field_refused : decodeOutput [some 1, some 4] = none := rfl
theorem empty_success_decodes : decodeOutput [some 1] = some (some []) := rfl
theorem arity_refusal_decodes : decodeOutput [some 0] = some none := rfl

end Controls
end Mettapedia.Languages.HOLLight.ArgumentListRendering
