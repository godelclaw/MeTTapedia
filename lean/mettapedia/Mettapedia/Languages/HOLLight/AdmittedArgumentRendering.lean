import Mettapedia.Languages.HOLLight.ArgumentRenderingMachine
import Mettapedia.GSLT.LanguageDef.PatternScopeExecution
import Mettapedia.Computability.RetainedWordExecution
import Mettapedia.Computability.WordEqualityMachine

/-!
# Source admission followed by complete HOL argument rendering

One original finite machine checks scope and canonical binder metadata,
retains the complete source word, and dispatches to the complete argument
renderer only on success. Refusal drains the retained input and returns the
empty word. Every copy, tag conversion, handoff and cleanup has an executed
clock. The domain includes every original Pattern encoding, including invalid
arguments. Arbitrary malformed bytes need their separate codec admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedArgumentRendering

open Mettapedia.Computability Turing Polynomial
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open ArgumentRenderingMachine
open Mettapedia.Languages.OpenTheory.SyntaxEncoding

abbrev scopeMachine := Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.machine

local instance : Fintype (scopeMachine.Γ scopeMachine.k₁) :=
  inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (scopeMachine.Γ scopeMachine.k₀) :=
  inferInstanceAs (Inhabited Alphabet)

def readResult (result : Option Bool) : Bool := result.getD false

def savedMachine : FinTM2 := RetainedWordExecution.machine scopeMachine readResult

local instance : Fintype (savedMachine.Γ savedMachine.k₁) :=
  inferInstanceAs (Fintype (Alphabet ⊕ Bool))
local instance : Inhabited (savedMachine.Γ savedMachine.k₁) :=
  inferInstanceAs (Inhabited (Alphabet ⊕ Bool))

def tagged (pattern : Pattern) : List (Alphabet ⊕ Bool) :=
  .inr (argumentValidAt 0 pattern) :: (patternWire pattern).map Sum.inl

def savedClock (pattern : Pattern) : Nat :=
  20000 * ((patternWire pattern).length + 1)^2 + 3 * (patternWire pattern).length + 5

noncomputable def savedOutputs (pattern : Pattern) :
    TM2OutputsInTime savedMachine (patternWire pattern) (some (tagged pattern)) (savedClock pattern) := by
  simpa only [savedMachine, tagged, savedClock, patternWire, readResult, Option.getD_some,
    List.length_nil, Nat.add_zero] using
    RetainedWordExecution.outputs scopeMachine readResult (patternWire pattern)
      (some (argumentValidAt 0 pattern)) [] _ (Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.outputs pattern)

def status (accepted : Bool) : Alphabet := if accepted then 1 else 0

def project : Alphabet ⊕ Bool → List Alphabet
  | .inl symbol => [symbol]
  | .inr accepted => [status accepted]

theorem projected (pattern : Pattern) :
    (tagged pattern).flatMap project = status (argumentValidAt 0 pattern) :: patternWire pattern := by
  simp only [tagged, List.flatMap_cons, project, List.singleton_append, List.flatMap_map]
  congr 1
  induction patternWire pattern with
  | nil => rfl
  | cons symbol rest ih => simp [ih]

def admittedMachine : FinTM2 := StackMachineComposition.machine savedMachine
  (WordHomomorphismMachine.machine project) (Equiv.refl _)

local instance : Fintype (admittedMachine.Γ admittedMachine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (admittedMachine.Γ admittedMachine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def accept (symbol : Alphabet) : Bool := decide (symbol = 1)

def renderingMachine : FinTM2 := StackMachineComposition.Dispatch.machine Full.machine accept []

def machine : FinTM2 := StackMachineComposition.machine admittedMachine renderingMachine (Equiv.refl _)

def output (pattern : Pattern) : List Alphabet :=
  if argumentValidAt 0 pattern then argumentWire pattern else []

def clock (pattern : Pattern) : Nat :=
  20000 * ((patternWire pattern).length + 1)^2 + 12 * (patternWire pattern).length + 21 + Full.clock pattern

noncomputable def admittedOutputs (pattern : Pattern) :
    TM2OutputsInTime admittedMachine (patternWire pattern)
      (some (status (argumentValidAt 0 pattern) :: patternWire pattern))
      (20000 * ((patternWire pattern).length + 1)^2 + 9 * (patternWire pattern).length + 15) := by
  have mapped := WordHomomorphismMachine.outputs project (tagged pattern)
  rw [projected] at mapped
  have joined := StackMachineComposition.outputs savedMachine
    (WordHomomorphismMachine.machine project) (Equiv.refl _)
    (patternWire pattern) (tagged pattern) (status (argumentValidAt 0 pattern) :: patternWire pattern)
    _ _ (savedOutputs pattern) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine project) ((tagged pattern).map id) _ _
      simpa only [List.map_id_fun, id_eq] using mapped)
  apply WordEqualityMachine.within joined
  simp only [tagged, savedClock, List.length_cons, List.length_map]
  omega

/-- Both branches are actual runs of the same dispatch machine. -/
noncomputable def renderingOutputs (pattern : Pattern) :
    TM2OutputsInTime renderingMachine (status (argumentValidAt 0 pattern) :: patternWire pattern)
      (some (output pattern)) (Full.clock pattern + (patternWire pattern).length + 2) := by
  cases admitted : argumentValidAt 0 pattern with
  | false =>
      have refused := StackMachineComposition.Dispatch.outputs_refused Full.machine accept []
        (status false) (patternWire pattern) (by decide)
      have result : TM2OutputsInTime renderingMachine
          (status false :: patternWire pattern)
          (some (output pattern)) ((patternWire pattern).length + 2) := by
        simpa [renderingMachine, output, admitted] using refused
      apply WordEqualityMachine.within result
      omega
  | true =>
      let rendered := Classical.choice (Full.outputs pattern admitted)
      have accepted := StackMachineComposition.Dispatch.outputs_success Full.machine accept []
        (status true) (patternWire pattern) (argumentWire pattern) _ (by decide) rendered
      have result : TM2OutputsInTime renderingMachine
          (status true :: patternWire pattern)
          (some (output pattern)) (Full.clock pattern + 1) := by
        simpa [renderingMachine, output, admitted] using accepted
      apply WordEqualityMachine.within result
      omega

noncomputable def outputs (pattern : Pattern) :
    TM2OutputsInTime machine (patternWire pattern) (some (output pattern)) (clock pattern) := by
  have joined := StackMachineComposition.outputs admittedMachine renderingMachine (Equiv.refl _)
    (patternWire pattern) (status (argumentValidAt 0 pattern) :: patternWire pattern)
    (output pattern) _ _ (admittedOutputs pattern)
    (by
      change TM2OutputsInTime renderingMachine
        ((status (argumentValidAt 0 pattern) :: patternWire pattern).map id) _ _
      simpa only [List.map_id_fun, id_eq] using renderingOutputs pattern)
  apply WordEqualityMachine.within joined
  simp only [clock, List.length_cons]
  omega

theorem clock_polynomial (pattern : Pattern) :
    clock pattern ≤ 3000030000 * ((patternWire pattern).length + 1)^3 := by
  have rendered := Full.clock_polynomial pattern
  have square : ((patternWire pattern).length + 1)^2 ≤ ((patternWire pattern).length + 1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have linear : (patternWire pattern).length + 1 ≤ ((patternWire pattern).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  unfold clock
  nlinarith

noncomputable def realization : TM2ComputableInPolyTime patternWire output (id : Pattern → Pattern) where
  tm := machine
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C 3000030000 * (X + C 1)^3
  outputsFun pattern := by
    change TM2OutputsInTime machine ((patternWire pattern).map id)
      (some ((output pattern).map id)) _
    simp only [List.map_id_fun]
    have executed := outputs pattern
    refine ⟨executed.toEvalsTo, ?_⟩
    simpa only [List.map_id, Equiv.coe_refl, id_eq, eval_mul, eval_pow, eval_add, eval_X, eval_C]
      using executed.steps_le_m.trans (clock_polynomial pattern)

/-- Successful decoding recovers the original typed source-to-HOL argument.
The refusal word is not a HOL term encoding. -/
theorem output_decodes (pattern : Pattern) :
    decodeWith canonicalCodec (output pattern) =
      if argumentValidAt 0 pattern then some (renderedArgument pattern) else none := by
  cases admitted : argumentValidAt 0 pattern with
  | false => simp only [output, admitted, Bool.false_eq_true, if_false]; rfl
  | true =>
      simpa only [output, admitted, if_true, argumentWire] using
        decodeWith_encodeWith canonicalCodec (renderedArgument pattern)

/-- Every halting run of the joined machine has the specified output. -/
theorem run_output_eq {pattern : Pattern} {word : List Alphabet}
    (run : TM2Outputs machine (patternWire pattern) (some word)) :
    word = output pattern :=
  StackMachineComposition.outputs_unique run (outputs pattern).toTM2Outputs

theorem run_decodes {pattern : Pattern} {word : List Alphabet}
    (run : TM2Outputs machine (patternWire pattern) (some word)) :
    decodeWith canonicalCodec word =
      if argumentValidAt 0 pattern then some (renderedArgument pattern) else none := by
  rw [run_output_eq run, output_decodes]

/-- Scope or metadata failure cannot produce a decodable canonical HOL term. -/
theorem refused_not_decodable {pattern : Pattern} (refused : argumentValidAt 0 pattern = false)
    {word : List Alphabet} (run : TM2Outputs machine (patternWire pattern) (some word)) :
    decodeWith canonicalCodec word = none := by
  simpa only [refused, Bool.false_eq_true, if_false] using run_decodes run

private theorem composition_finite (first second : FinTM2)
    (firstFinite : ∀ key, Finite (first.Γ key))
    (secondFinite : ∀ key, Finite (second.Γ key))
    (key : StackMachineComposition.Key first second) :
    Finite (StackMachineComposition.Alphabet first second key) := by
  cases key with
  | none => exact firstFinite _
  | some key => cases key with
    | inl key => exact firstFinite key
    | inr key => exact secondFinite key

/-- All dynamic storage cells come from finite alphabets, including scratch
stacks; arbitrary terms are never hidden inside a unit-cost cell. -/
theorem finiteAlphabet (key : machine.K) : Finite (machine.Γ key) := by
  have homomorphic {A B : Type} [Fintype A] [Fintype B] [Inhabited B]
      (f : A → List B) (key : (WordHomomorphismMachine.machine f).K) :
      Finite ((WordHomomorphismMachine.machine f).Γ key) := by
    change Finite (WordHomomorphismMachine.Alphabet (A := A) (B := B) key)
    cases key <;> infer_instance
  have scope : ∀ key, Finite (scopeMachine.Γ key) := by
    apply composition_finite
    · apply composition_finite
      · intro key
        change Finite (Mettapedia.GSLT.LanguageDef.PatternScopeExecution.VisitorAdapter.Cells key)
        cases key with
        | none => exact inferInstanceAs (Finite Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Event)
        | some key => cases key <;> infer_instance
      · exact homomorphic _
    · intro key
      exact inferInstanceAs (Finite (Mettapedia.GSLT.LanguageDef.PatternScopeExecution.Binary.Cells key))
  have saved : ∀ key, Finite (savedMachine.Γ key) := by
    intro key
    cases key with
    | none => exact inferInstanceAs (Finite (Alphabet ⊕ Bool))
    | some key => cases key with
      | none => exact inferInstanceAs (Finite Alphabet)
      | some key => cases key with
        | none => exact inferInstanceAs (Finite Alphabet)
        | some key => exact scope key
  have admitted : ∀ key, Finite (admittedMachine.Γ key) :=
    composition_finite _ _ saved (homomorphic _)
  have rendered : ∀ key, Finite (renderingMachine.Γ key) := by
    apply composition_finite
    · apply composition_finite
      · intro key
        exact inferInstanceAs (Finite (Routing.Traversal.Cells key))
      · intro key
        change Finite (Routing.Cells key)
        cases key <;> infer_instance
    · intro key
      exact inferInstanceAs (Finite (Execution.Cells key))
  exact composition_finite _ _ admitted rendered key

namespace Controls

theorem nullary_accepted : argumentValidAt 0 (.apply "Z" []) = true := by decide
theorem nested_accepted :
    argumentValidAt 0 (.apply "S" [.apply "Z" [], .lambda none (.bvar 0)]) = true := by decide
theorem escaping_index_refused : argumentValidAt 0 (.bvar 0) = false := by decide
theorem noncanonical_binder_refused :
    argumentValidAt 0 (.lambda (some "display-name") (.bvar 0)) = false := by decide

theorem nested_decodes :
    decodeWith canonicalCodec (output (.apply "S" [.apply "Z" [], .lambda none (.bvar 0)])) =
      some (renderedArgument (.apply "S" [.apply "Z" [], .lambda none (.bvar 0)])) := by
  rw [output_decodes, nested_accepted]; rfl

theorem escaping_run_refused {word : List Alphabet}
    (run : TM2Outputs machine (patternWire (.bvar 0)) (some word)) :
    decodeWith canonicalCodec word = none := refused_not_decodable escaping_index_refused run

end Controls

end Mettapedia.Languages.HOLLight.AdmittedArgumentRendering
