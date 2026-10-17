import Mettapedia.Computability.FramedWordMapping
import Mettapedia.Computability.FramedWordDecoding
import Mettapedia.Languages.HOLLight.AdmittedArgumentProgram

/-!
# One executed renderer for complete argument vectors

Every original field is admitted and rendered by the existing scalar machine.
The caller preserves order, duplicate occurrences and empty refusal fields,
charging all copies and transfers. A refused field remains an undecodable
field at its original position; it is never silently removed. Inputs here are
vectors of original Pattern encodings, not arbitrary byte streams.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.HOLLight.ArgumentVectorRendering
open Turing Polynomial
open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open ArgumentRenderingMachine
open Mettapedia.GSLT.LanguageDef.InferenceChecker

local instance : Fintype (AdmittedArgumentRendering.machine.Γ AdmittedArgumentRendering.machine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (AdmittedArgumentRendering.machine.Γ AdmittedArgumentRendering.machine.k₀) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (AdmittedArgumentRendering.machine.Γ AdmittedArgumentRendering.machine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def machine : FinTM2 := FramedWordMapping.machine AdmittedArgumentRendering.machine

def input (patterns : List Pattern) : List (Option Alphabet) :=
  WordTemplateMachine.Indexed.frame (patterns.map patternWire)

def output (patterns : List Pattern) : List (Option Alphabet) :=
  WordTemplateMachine.Indexed.frame (patterns.map AdmittedArgumentRendering.output)

def clock (patterns : List Pattern) : Nat :=
  FramedWordMapping.totalClock AdmittedArgumentRendering.machine patternWire
    AdmittedArgumentRendering.output AdmittedArgumentRendering.clock patterns

noncomputable def outputs (patterns : List Pattern) :
    TM2OutputsInTime machine (input patterns) (some (output patterns)) (clock patterns) :=
  FramedWordMapping.outputs AdmittedArgumentRendering.machine patternWire
    AdmittedArgumentRendering.output AdmittedArgumentRendering.clock
    AdmittedArgumentRendering.outputs patterns

/-- Every completed original run returns the qualified framed result. -/
theorem run_output_eq {patterns : List Pattern} {word : List (Option Alphabet)}
    (run : TM2Outputs machine (input patterns) (some word)) : word = output patterns :=
  StackMachineComposition.outputs_unique run (outputs patterns).toTM2Outputs

/-- Refusal of all fields preserves their number and positions. -/
theorem all_refused_output (patterns : List Pattern)
    (refused : ∀ pattern ∈ patterns, argumentValidAt 0 pattern = false) :
    output patterns = List.replicate patterns.length none := by
  induction patterns with
  | nil => rfl
  | cons pattern rest ih =>
      have head := refused pattern (by simp)
      have tail := ih (fun value member => refused value (by simp [member]))
      simpa [output, WordTemplateMachine.Indexed.frame, AdmittedArgumentRendering.output,
        List.replicate_succ, head] using congrArg (List.cons none) tail

theorem argument_length (pattern : Pattern) :
    (argumentWire pattern).length ≤ 7400 * ((patternWire pattern).length + 1) := by
  have source := (Execution.patternWire_length_bounds pattern).1
  have data := Execution.dataWord_length pattern
  have framed := Execution.rootTemplate_exact pattern
  simp only [Execution.rootTemplate, WordTemplateMachine.instantiate_append,
    WordTemplateMachine.instantiate_literals, WordTemplateMachine.instantiate_literal,
    WordTemplateMachine.instantiate_hole, WordTemplateMachine.instantiate_nil,
    List.append_nil] at framed
  have overhead : (encodeData (putTy InferenceHosting.dataType)).length + 1 ≤ 1000 := by decide
  have length := congrArg List.length framed
  simp only [List.length_cons, List.length_append] at length
  omega

theorem field_length (pattern : Pattern) :
    (AdmittedArgumentRendering.output pattern).length ≤ 7400 * ((patternWire pattern).length + 1) := by
  unfold AdmittedArgumentRendering.output
  split
  · exact argument_length pattern
  · simp

private theorem field_clock (pattern : Pattern) :
    AdmittedArgumentRendering.clock pattern + 2 * (patternWire pattern).length +
      2 * (AdmittedArgumentRendering.output pattern).length + 4 ≤
        3000050000 * ((patternWire pattern).length + 1)^3 := by
  have time := AdmittedArgumentRendering.clock_polynomial pattern
  have storage := field_length pattern
  have linear : (patternWire pattern).length + 1 ≤ ((patternWire pattern).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  nlinarith

private theorem summed_clock (patterns : List Pattern) :
    (patterns.map (fun pattern => AdmittedArgumentRendering.clock pattern +
      2 * (patternWire pattern).length + 2 * (AdmittedArgumentRendering.output pattern).length + 4)).sum ≤
        3000050000 * (input patterns).length^3 := by
  induction patterns with
  | nil => simp [input, WordTemplateMachine.Indexed.frame]
  | cons pattern rest ih =>
    have field := field_clock pattern
    have layout : (input (pattern :: rest)).length =
        (patternWire pattern).length + 1 + (input rest).length := by
      simp [input, WordTemplateMachine.Indexed.frame, List.length_append]
      omega
    simp only [List.map_cons, List.sum_cons]
    rw [layout]
    nlinarith [Nat.zero_le ((patternWire pattern).length + 1), Nat.zero_le (input rest).length,
      Nat.zero_le (((patternWire pattern).length + 1)^2 * (input rest).length),
      Nat.zero_le (((patternWire pattern).length + 1) * (input rest).length^2)]

theorem clock_polynomial (patterns : List Pattern) :
    clock patterns ≤ 3000050002 * ((input patterns).length + 1)^3 := by
  have bound := summed_clock patterns
  unfold clock
  rw [FramedWordMapping.totalClock_eq]
  have monotone : (input patterns).length^3 ≤ ((input patterns).length + 1)^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have positive : 0 < ((input patterns).length + 1)^3 := by positivity
  omega

noncomputable def realization : TM2ComputableInPolyTime input output (id : List Pattern → List Pattern) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl (Option Alphabet)
  time := C 3000050002 * (X + C 1)^3
  outputsFun patterns := by
    change TM2OutputsInTime machine ((input patterns).map id) (some ((output patterns).map id)) _
    simp only [List.map_id_fun]
    have executed := outputs patterns
    refine ⟨executed.toEvalsTo, ?_⟩
    simpa only [eval_mul, eval_pow, eval_add, eval_X, eval_C] using
      executed.steps_le_m.trans (clock_polynomial patterns)

theorem finiteAlphabet (key : machine.K) : Finite (machine.Γ key) :=
  FramedWordMapping.finiteAlphabet AdmittedArgumentRendering.machine
    AdmittedArgumentRendering.finiteAlphabet key

/-- Independent decoding retains success or refusal at each original index. -/
theorem fields_decode (patterns : List Pattern) :
    patterns.map (fun pattern => decodeWith canonicalCodec (AdmittedArgumentRendering.output pattern)) =
      patterns.map (fun pattern => if argumentValidAt 0 pattern then some (renderedArgument pattern) else none) := by
  simp only [AdmittedArgumentRendering.output_decodes]

/-- Decode the returned physical word independently of its source patterns.
Outer failure is malformed framing; an inner failure is a refused argument. -/
def decodeOutput (word : List (Option Alphabet)) : Option (List (Option CanonicalTerm)) :=
  (WordTemplateMachine.Indexed.decodeFrames word).map
    (List.map (decodeWith canonicalCodec))

theorem decode_output (patterns : List Pattern) :
    decodeOutput (output patterns) = some (patterns.map (fun pattern =>
      if argumentValidAt 0 pattern then some (renderedArgument pattern) else none)) := by
  simp only [decodeOutput, output, WordTemplateMachine.Indexed.decodeFrames_frame,
    Option.map_some, List.map_map, Function.comp_def]
  rw [fields_decode]

theorem run_decodes {patterns : List Pattern} {word : List (Option Alphabet)}
    (run : TM2Outputs machine (input patterns) (some word)) :
    decodeOutput word = some (patterns.map (fun pattern =>
      if argumentValidAt 0 pattern then some (renderedArgument pattern) else none)) := by
  rw [run_output_eq run, decode_output]

namespace Controls

theorem empty_vector : output [] = [] := rfl

theorem refusal_is_a_field : output [.bvar 0] = [none] := by decide

theorem refusal_is_not_empty_vector : output [.bvar 0] ≠ output [] := by decide

theorem refused_field_decodes : decodeOutput [none] = some [none] := rfl

theorem unterminated_output_refused : decodeOutput [some 4] = none := rfl

theorem duplicates_preserved (pattern : Pattern) :
    output [pattern, pattern] = output [pattern] ++ output [pattern] := by
  simp [output, WordTemplateMachine.Indexed.frame]

theorem mixed_fields_decode :
    [.apply "Z" [], .bvar 0, .apply "Z" []].map
      (fun pattern => decodeWith canonicalCodec (AdmittedArgumentRendering.output pattern)) =
        [some (renderedArgument (.apply "Z" [])), none, some (renderedArgument (.apply "Z" []))] := by
  rw [fields_decode]
  rfl

end Controls
end Mettapedia.Languages.HOLLight.ArgumentVectorRendering
