import Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission
import Mettapedia.Languages.HOLLight.ArgumentListRendering

/-!
# Original rule admission and HOL argument rendering on one clock

For each fixed authored calculus, the original serialized rule instance is
looked up in its rule table. The bound measures the complete instance bytes;
compiling the authored table is a separate uniformity obligation.
The selected arity and every original zero-depth argument judgment are checked
before the complete argument vector is rendered. The original admission body,
status projection, renderer and refusal drain are physically composed. Unknown
rules, wrong arities and invalid arguments all halt with an explicit refusal.
The domain is the image of the original instance codec. Premise judgments and
rule side conditions remain separate obligations of the full proof checker.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.HOLLight.RuleArgumentRendering
open Turing Polynomial StateTransition
open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open InferenceChecker InferenceExtension
open CertificateRuleAdmission.ScopedApplication
open Mettapedia.Languages.OpenTheory
open ArgumentRenderingMachine

def input (ruleInstance : RuleInstance) : List Alphabet :=
  encodeWith CertificateDataEncoding.instanceCodec ruleInstance

def project : Option Alphabet ⊕ Bool → List (Option Alphabet)
  | .inl symbol => [symbol]
  | .inr accepted => [some (if accepted then 1 else 0)]

def tail (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : List (Option Alphabet) :=
  (frameResult definition ruleInstance).getD []

def projected (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : List (Option Alphabet) :=
  some (if scopeResult definition ruleInstance then 1 else 0) :: tail definition ruleInstance

theorem project_output (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (scopeOutput definition ruleInstance).flatMap project = projected definition ruleInstance := by
  cases found : frameResult definition ruleInstance <;>
    simp [scopeOutput, scopeTail, projected, tail, found, project, List.flatMap_map]

theorem projected_length (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (projected definition ruleInstance).length = (scopeOutput definition ruleInstance).length := by
  cases found : frameResult definition ruleInstance <;>
    simp [projected, tail, scopeOutput, scopeTail, found]

theorem tail_length_le (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (tail definition ruleInstance).length ≤ (input ruleInstance).length := by
  cases found : frameResult definition ruleInstance with
  | none => simp only [tail, found, Option.getD_none, List.length_nil, Nat.zero_le]
  | some framing =>
    simpa only [tail, found, Option.getD_some, frameResult_some found, input] using
      vector_length_le ruleInstance

theorem admitted_tail {definition : CalculusLanguageDef} {ruleInstance : RuleInstance}
    (admitted : scopeResult definition ruleInstance = true) :
    tail definition ruleInstance = ArgumentVectorRendering.input ruleInstance.arguments := by
  have both : (frameResult definition ruleInstance).isSome = true ∧
      ruleInstance.arguments.all (argumentValidAt 0) = true := by
    simpa only [scopeResult, Bool.and_eq_true] using admitted
  have framed := both.1
  obtain ⟨word, found⟩ := Option.isSome_iff_exists.mp framed
  rw [tail, found, Option.getD_some]
  exact (frameResult_some found).trans (ArgumentListRendering.frame_eq ruleInstance.arguments)

local instance (definition : CalculusLanguageDef) : Fintype
    ((scopeMachine definition).Γ (scopeMachine definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (definition : CalculusLanguageDef) : Inhabited
    ((scopeMachine definition).Γ (scopeMachine definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))

def projectedMachine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (scopeMachine definition)
    (WordHomomorphismMachine.machine project) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype
    ((projectedMachine definition).Γ (projectedMachine definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited
    ((projectedMachine definition).Γ (projectedMachine definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def machine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (projectedMachine definition)
    ArgumentListRendering.dispatched (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] projectedMachine machine scopeMachine scopeDispatcher
  WordHomomorphismMachine.machine StackMachineComposition.machine
  ArgumentListRendering.dispatched StackMachineComposition.Dispatch.machine

def output (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : List (Option Alphabet) :=
  if scopeResult definition ruleInstance then some 1 :: ArgumentVectorRendering.output ruleInstance.arguments
  else [some 0]

def projectionClock (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : Nat :=
  20100 * ((input ruleInstance).length + 1)^2 + 6 * (scopeOutput definition ruleInstance).length + 4

def laterClock (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : Nat :=
  if scopeResult definition ruleInstance then ArgumentListRendering.successClock ruleInstance.arguments + 1
  else (tail definition ruleInstance).length + 2

def clock (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : Nat :=
  projectionClock definition ruleInstance + 2 * (projected definition ruleInstance).length + 2 +
    laterClock definition ruleInstance

noncomputable def projectionOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (projectedMachine definition) (input ruleInstance)
      (some (projected definition ruleInstance)) (projectionClock definition ruleInstance) := by
  have projectedRun := WordHomomorphismMachine.outputs project (scopeOutput definition ruleInstance)
  rw [project_output] at projectedRun
  have joined := StackMachineComposition.outputs (scopeMachine definition)
    (WordHomomorphismMachine.machine project) (Equiv.refl _) (input ruleInstance)
    (scopeOutput definition ruleInstance) (projected definition ruleInstance)
    (20100 * ((input ruleInstance).length + 1)^2)
    (2 * (scopeOutput definition ruleInstance).length + 2 * (projected definition ruleInstance).length + 2)
    (scopeOutputs definition ruleInstance) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine project)
        ((scopeOutput definition ruleInstance).map id) _ _
      simpa only [List.map_id] using projectedRun)
  apply WordEqualityMachine.within joined
  rw [projected_length]
  unfold projectionClock
  omega

noncomputable def laterOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime ArgumentListRendering.dispatched (projected definition ruleInstance)
      (some (output definition ruleInstance)) (laterClock definition ruleInstance) := by
  cases admitted : scopeResult definition ruleInstance with
  | false =>
    simpa only [ArgumentListRendering.dispatched, projected, admitted,
      Bool.false_eq_true, if_false, output, laterClock] using
      StackMachineComposition.Dispatch.outputs_refused ArgumentListRendering.successMachine
        ArgumentListRendering.accept [some 0] (some (0 : Alphabet))
        (tail definition ruleInstance) (by decide)
  | true =>
    simpa only [ArgumentListRendering.dispatched, projected, admitted, if_true,
      output, laterClock, admitted_tail admitted] using
      StackMachineComposition.Dispatch.outputs_success ArgumentListRendering.successMachine
        ArgumentListRendering.accept [some 0] (some (1 : Alphabet))
        (ArgumentVectorRendering.input ruleInstance.arguments)
        (some 1 :: ArgumentVectorRendering.output ruleInstance.arguments)
        (ArgumentListRendering.successClock ruleInstance.arguments) (by decide)
        (ArgumentListRendering.successOutputs ruleInstance.arguments)

/-- All component runs, physical handoffs and refusal cleanup use one machine. -/
noncomputable def outputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (machine definition) (input ruleInstance)
      (some (output definition ruleInstance)) (clock definition ruleInstance) :=
  StackMachineComposition.outputs (projectedMachine definition) ArgumentListRendering.dispatched
    (Equiv.refl _) (input ruleInstance) (projected definition ruleInstance) (output definition ruleInstance)
    (projectionClock definition ruleInstance) (laterClock definition ruleInstance)
    (projectionOutputs definition ruleInstance) (by
      change TM2OutputsInTime ArgumentListRendering.dispatched
        ((projected definition ruleInstance).map id) _ _
      simpa only [List.map_id] using laterOutputs definition ruleInstance)

theorem clock_polynomial (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    clock definition ruleInstance ≤ 3000300000 * ((input ruleInstance).length + 1)^3 := by
  have vectorBound := CertificateRuleAdmission.ScopedApplication.vector_length_le ruleInstance
  change (ArgumentVectorRendering.input ruleInstance.arguments).length ≤ (input ruleInstance).length at vectorBound
  have tailBound := tail_length_le definition ruleInstance
  have outBound := ArgumentListRendering.vector_output_length ruleInstance.arguments
  have renderBound := ArgumentVectorRendering.clock_polynomial ruleInstance.arguments
  have monotone : ((ArgumentVectorRendering.input ruleInstance.arguments).length + 1)^3 ≤
      ((input ruleInstance).length + 1)^3 := Nat.pow_le_pow_left (by omega) 3
  have linear : (input ruleInstance).length + 1 ≤ ((input ruleInstance).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  have quadratic : ((input ruleInstance).length + 1)^2 ≤ ((input ruleInstance).length + 1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  unfold clock projectionClock laterClock ArgumentListRendering.successClock
  rw [← projected_length]
  simp only [projected, List.length_cons]
  split <;> nlinarith

noncomputable def realization (definition : CalculusLanguageDef) :
    TM2ComputableInPolyTime input (output definition) (id : RuleInstance → RuleInstance) where
  tm := machine definition
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl (Option Alphabet)
  time := C 3000300000 * (X + C 1)^3
  outputsFun ruleInstance := by
    change TM2OutputsInTime (machine definition) ((input ruleInstance).map id)
      (some ((output definition ruleInstance).map id)) _
    simp only [List.map_id_fun]
    have executed := outputs definition ruleInstance
    refine ⟨executed.toEvalsTo, ?_⟩
    simpa only [eval_mul, eval_pow, eval_add, eval_X, eval_C] using
      executed.steps_le_m.trans (clock_polynomial definition ruleInstance)

theorem run_output_eq {definition : CalculusLanguageDef} {ruleInstance : RuleInstance}
    {word : List (Option Alphabet)}
    (run : TM2Outputs (machine definition) (input ruleInstance) (some word)) :
    word = output definition ruleInstance :=
  StackMachineComposition.outputs_unique run (outputs definition ruleInstance).toTM2Outputs

/-- A successful admission guarantees that every rendered field is valid;
the independent decoder returns the original ordered argument images. -/
theorem decode_output (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    ArgumentListRendering.decodeOutput (output definition ruleInstance) =
      some (if scopeResult definition ruleInstance then
        some (ruleInstance.arguments.map fun pattern => some (renderedArgument pattern)) else none) := by
  cases admitted : scopeResult definition ruleInstance with
  | false => simp only [output, admitted, Bool.false_eq_true, if_false]; rfl
  | true =>
    have valid : ruleInstance.arguments.all (argumentValidAt 0) = true := by
      have both : (frameResult definition ruleInstance).isSome = true ∧
          ruleInstance.arguments.all (argumentValidAt 0) = true := by
        simpa only [scopeResult, Bool.and_eq_true] using admitted
      exact both.2
    have decoded := ArgumentListRendering.decode_output ruleInstance.arguments.length ruleInstance.arguments
    simp only [ArgumentListRendering.output, ite_true, CertificateArgumentFraming.statusWire] at decoded
    simp only [output, admitted, if_true]
    rw [decoded]
    congr 2
    apply List.map_congr_left
    intro pattern member
    rw [List.all_eq_true.mp valid pattern member]
    rfl

theorem run_decodes {definition : CalculusLanguageDef} {ruleInstance : RuleInstance}
    {word : List (Option Alphabet)}
    (run : TM2Outputs (machine definition) (input ruleInstance) (some word)) :
    ArgumentListRendering.decodeOutput word =
      some (if scopeResult definition ruleInstance then
        some (ruleInstance.arguments.map fun pattern => some (renderedArgument pattern)) else none) := by
  rw [run_output_eq run, decode_output]

theorem decoded_success_iff (definition : CalculusLanguageDef)
    (zeroDepth : ∀ index : Fin definition.rules.length,
      ∀ formal ∈ (CertificateRuleAdmission.row definition index).metavariables, formal.2 = 0)
    (ruleInstance : RuleInstance) :
    ArgumentListRendering.decodeOutput (output definition ruleInstance) =
      some (some (ruleInstance.arguments.map fun pattern => some (renderedArgument pattern))) ↔
      ∃ rule, definition.lookupRule? ruleInstance.ruleId = some rule ∧
        argumentsValidAt rule.metavariables ruleInstance.arguments = true := by
  rw [decode_output, ← scopeResult_iff definition zeroDepth ruleInstance]
  cases scopeResult definition ruleInstance <;> simp

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

private theorem homomorphism_finite {A B : Type} [Fintype A] [Fintype B] [Inhabited B]
    (f : A → List B) (key : (WordHomomorphismMachine.machine f).K) :
    Finite ((WordHomomorphismMachine.machine f).Γ key) := by
  change Finite (WordHomomorphismMachine.Alphabet (A := A) (B := B) key)
  cases key <;> infer_instance

private theorem patternScope_finite (key : PatternScopeExecution.OriginalAdmission.machine.K) :
    Finite (PatternScopeExecution.OriginalAdmission.machine.Γ key) := by
  apply composition_finite
  · apply composition_finite
    · intro key
      change Finite (PatternScopeExecution.VisitorAdapter.Cells key)
      cases key with
      | none => exact inferInstanceAs (Finite PatternSpanExecution.Event)
      | some key => cases key <;> infer_instance
    · exact homomorphism_finite _
  · intro key
    exact inferInstanceAs (Finite (PatternScopeExecution.Binary.Cells key))

attribute [local implicit_reducible] CertificateRuleAdmission.admissionMachine
  CertificateRuleAdmission.machine CertificateRuleAdmission.nameMachine
  CertificateRuleAdmission.classifier CertificateRuleAdmission.dictionary
  CertificateRuleAdmission.argumentMachine CertificateRuleAdmission.UniformArity.machine
  CertificateRuleAdmission.ArgumentScope.machine FramedWordValidation.machine
  FramedWordValidation.retainedMachine RetainedWordExecution.machine
  CommonArenaDispatch.machine CertificateDataTraversal.ProductField.machine
  FiniteWordClassifier.machine CertificateArgumentFraming.Execution.machine

private theorem product_finite (second : Bool) (key : (CertificateDataTraversal.ProductField.machine second).K) :
    Finite ((CertificateDataTraversal.ProductField.machine second).Γ key) := by
  cases key <;> exact inferInstanceAs (Finite Alphabet)

private theorem argument_finite (arity : Nat) (key : (CertificateRuleAdmission.argumentMachine arity).K) :
    Finite ((CertificateRuleAdmission.argumentMachine arity).Γ key) := by
  apply composition_finite
  · exact product_finite true
  · intro key
    exact inferInstanceAs (Finite (CertificateArgumentFraming.Execution.Cells key))

private theorem admission_finite (definition : CalculusLanguageDef)
    (key : (CertificateRuleAdmission.admissionMachine definition).K) :
    Finite ((CertificateRuleAdmission.admissionMachine definition).Γ key) := by
  have nameFinite : ∀ key, Finite ((CertificateRuleAdmission.nameMachine definition).Γ key) := by
    apply composition_finite
    · exact product_finite false
    · intro key
      change Finite (FiniteWordClassifier.Alphabet Alphabet definition.rules.length key)
      cases key <;> infer_instance
  have retained : ∀ key, Finite ((CertificateRuleAdmission.machine definition).Γ key) := by
    intro key
    cases key with
    | none => exact inferInstanceAs (Finite (Alphabet ⊕ Option (Fin definition.rules.length)))
    | some key => cases key with
      | none => exact inferInstanceAs (Finite Alphabet)
      | some key => cases key with
        | none => exact inferInstanceAs (Finite Alphabet)
        | some key => exact nameFinite key
  apply composition_finite _ _ retained
  intro key
  cases key with
  | none => exact inferInstanceAs (Finite (Alphabet ⊕ Option (Fin definition.rules.length)))
  | some key => cases key with
    | none => exact inferInstanceAs (Finite Alphabet)
    | some key => exact argument_finite 0 key

private theorem scope_finite (definition : CalculusLanguageDef)
    (key : (scopeMachine definition).K) : Finite ((scopeMachine definition).Γ key) := by
  have validation : ∀ key, Finite ((CertificateRuleAdmission.ArgumentScope.machine).Γ key) := by
    intro key
    cases key with
    | none => exact inferInstanceAs (Finite (Option Alphabet ⊕ Bool))
    | some key => cases key with
      | none => exact inferInstanceAs (Finite (Option Alphabet))
      | some key => cases key with
        | none => exact inferInstanceAs (Finite (Option Alphabet))
        | some key => cases key with
          | none => exact inferInstanceAs (Finite (Option Alphabet))
          | some key => cases key with
            | none => exact inferInstanceAs (Finite Alphabet)
            | some key => cases key with
              | none => exact inferInstanceAs (Finite (Option Bool))
              | some key => exact patternScope_finite key
  exact composition_finite _ _ (admission_finite definition) validation key

/-- Every arena, including all original admission and parser scratch stacks,
stores finite symbols. No decoded syntax tree is a unit-cost machine cell. -/
theorem finiteAlphabet (definition : CalculusLanguageDef) (key : (machine definition).K) :
    Finite ((machine definition).Γ key) := by
  have projectedFinite : ∀ key, Finite ((projectedMachine definition).Γ key) :=
    composition_finite _ _ (scope_finite definition) (homomorphism_finite project)
  have rendered : ∀ key, Finite (ArgumentListRendering.dispatched.Γ key) := by
    intro key
    cases key with
    | none => exact inferInstanceAs (Finite (Option Alphabet))
    | some key => cases key with
      | inl key => exact ArgumentVectorRendering.finiteAlphabet key
      | inr key => exact inferInstanceAs (Finite (Option Alphabet))
  exact composition_finite _ _ projectedFinite rendered key

local instance (definition : CalculusLanguageDef) : Fintype ((machine definition).Γ (machine definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited ((machine definition).Γ (machine definition).k₀) :=
  inferInstanceAs (Inhabited Alphabet)
local instance (definition : CalculusLanguageDef) : Inhabited ((machine definition).Γ (machine definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

/-- The driver may retain the complete source instance, including its rule
identity, beside the rendered result. All physical copies are charged. -/
def retainedMachine (definition : CalculusLanguageDef) : FinTM2 :=
  RetainedWordExecution.WithOutput.machine (machine definition)

def retainedOutput (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    List (Alphabet ⊕ Option Alphabet) :=
  (input ruleInstance).map Sum.inl ++ (output definition ruleInstance).map Sum.inr

def retainedClock (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : Nat :=
  clock definition ruleInstance + 3 * (input ruleInstance).length +
    2 * (output definition ruleInstance).length + 5

noncomputable def retainedOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (retainedMachine definition) (input ruleInstance)
      (some (retainedOutput definition ruleInstance)) (retainedClock definition ruleInstance) :=
  RetainedWordExecution.WithOutput.outputs (machine definition) (input ruleInstance)
    (output definition ruleInstance) (clock definition ruleInstance) (outputs definition ruleInstance)

theorem output_length_le (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (output definition ruleInstance).length ≤ 7401 * (input ruleInstance).length + 1 := by
  have vectorBound := CertificateRuleAdmission.ScopedApplication.vector_length_le ruleInstance
  change (ArgumentVectorRendering.input ruleInstance.arguments).length ≤ (input ruleInstance).length at vectorBound
  have bound := ArgumentListRendering.vector_output_length ruleInstance.arguments
  unfold output
  split <;> simp only [List.length_cons, List.length_nil] <;> omega

theorem retainedClock_polynomial (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    retainedClock definition ruleInstance ≤ 3000500000 * ((input ruleInstance).length + 1)^3 := by
  have run := clock_polynomial definition ruleInstance
  have length := output_length_le definition ruleInstance
  have linear : (input ruleInstance).length + 1 ≤ ((input ruleInstance).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  unfold retainedClock
  nlinarith

noncomputable def retainedRealization (definition : CalculusLanguageDef) :
    TM2ComputableInPolyTime input (retainedOutput definition) (id : RuleInstance → RuleInstance) where
  tm := retainedMachine definition
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl (Alphabet ⊕ Option Alphabet)
  time := C 3000500000 * (X + C 1)^3
  outputsFun ruleInstance := by
    change TM2OutputsInTime (retainedMachine definition) ((input ruleInstance).map id)
      (some ((retainedOutput definition ruleInstance).map id)) _
    simp only [List.map_id_fun]
    have executed := retainedOutputs definition ruleInstance
    refine ⟨executed.toEvalsTo, ?_⟩
    simpa only [eval_mul, eval_pow, eval_add, eval_X, eval_C] using
      executed.steps_le_m.trans (retainedClock_polynomial definition ruleInstance)

theorem retained_finiteAlphabet (definition : CalculusLanguageDef) (key : (retainedMachine definition).K) :
    Finite ((retainedMachine definition).Γ key) := by
  cases key with
  | none => exact inferInstanceAs (Finite (Alphabet ⊕ Option Alphabet))
  | some key => cases key with
    | none => exact inferInstanceAs (Finite (Option Alphabet))
    | some key => cases key with
      | none => exact inferInstanceAs (Finite Alphabet)
      | some key => cases key with
        | none => exact inferInstanceAs (Finite Alphabet)
        | some key => exact finiteAlphabet definition key

def readSource : List (Alphabet ⊕ Option Alphabet) → List Alphabet :=
  List.filterMap fun cell => match cell with
    | .inl symbol => some symbol
    | .inr _ => none

def readRendered : List (Alphabet ⊕ Option Alphabet) → List (Option Alphabet) :=
  List.filterMap fun cell => match cell with
    | .inl _ => none
    | .inr symbol => some symbol

theorem retained_source (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    readSource (retainedOutput definition ruleInstance) = input ruleInstance := by
  simp [readSource, retainedOutput, List.filterMap_map]

theorem retained_rendered (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    readRendered (retainedOutput definition ruleInstance) = output definition ruleInstance := by
  simp [readRendered, retainedOutput, List.filterMap_map]

theorem retained_run_source {definition : CalculusLanguageDef} {ruleInstance : RuleInstance}
    {word : List (Alphabet ⊕ Option Alphabet)}
    (run : TM2Outputs (retainedMachine definition) (input ruleInstance) (some word)) :
    decodeWith CertificateDataEncoding.instanceCodec (readSource word) = some ruleInstance := by
  rw [StackMachineComposition.outputs_unique run (retainedOutputs definition ruleInstance).toTM2Outputs,
    retained_source, input, decodeWith_encodeWith]

theorem retained_run_decodes {definition : CalculusLanguageDef} {ruleInstance : RuleInstance}
    {word : List (Alphabet ⊕ Option Alphabet)}
    (run : TM2Outputs (retainedMachine definition) (input ruleInstance) (some word)) :
    ArgumentListRendering.decodeOutput (readRendered word) =
      some (if scopeResult definition ruleInstance then
        some (ruleInstance.arguments.map fun pattern => some (renderedArgument pattern)) else none) := by
  rw [StackMachineComposition.outputs_unique run (retainedOutputs definition ruleInstance).toTM2Outputs,
    retained_rendered, decode_output]

namespace Controls

def rule (name : String) (formals : List (String × Nat)) : RuleSchema :=
  { id := ⟨name⟩, metavariables := formals, premises := [], conclusion := .apply "claim" [] }

def calculus : CalculusLanguageDef :=
  { name := "argument rendering", types := [], terms := [], equations := [], rewrites := [],
    rules := [rule "zero" [], rule "two" [("x", 0), ("y", 0)],
      rule "dup" [], rule "dup" [("x", 0)], rule "规则λ🙂" [("x", 0)]] }

theorem zero_depth : ∀ index : Fin calculus.rules.length,
    ∀ formal ∈ (CertificateRuleAdmission.row calculus index).metavariables, formal.2 = 0 := by
  intro index
  fin_cases index <;> simp [CertificateRuleAdmission.row, calculus, rule]

theorem empty_success : output calculus ⟨⟨"zero"⟩, []⟩ = [some 1] := by decide
theorem missing_rule : output calculus ⟨⟨"missing"⟩, []⟩ = [some 0] := by decide
theorem wrong_arity : output calculus ⟨⟨"two"⟩, [.apply "Z" []]⟩ = [some 0] := by decide
theorem first_duplicate_wins : output calculus ⟨⟨"dup"⟩, [.apply "Z" []]⟩ = [some 0] := by decide
theorem unused_invalid_argument :
    output calculus ⟨⟨"two"⟩, [.apply "Z" [], .bvar 0]⟩ = [some 0] := by decide
theorem named_binder_refused :
    output calculus ⟨⟨"规则λ🙂"⟩, [.lambda (some "display") (.bvar 0)]⟩ = [some 0] := by decide
theorem repeated_closed_binders :
    ArgumentListRendering.decodeOutput (output calculus
      ⟨⟨"two"⟩, [.lambda none (.bvar 0), .lambda none (.bvar 0)]⟩) =
      some (some [some (renderedArgument (.lambda none (.bvar 0))),
        some (renderedArgument (.lambda none (.bvar 0)))]) := by
  rw [decode_output]; rfl
theorem unicode_rule :
    ArgumentListRendering.decodeOutput (output calculus ⟨⟨"规则λ🙂"⟩, [.apply "α" []]⟩) =
      some (some [some (renderedArgument (.apply "α" []))]) := by
  rw [decode_output]; rfl

end Controls

end Mettapedia.Languages.HOLLight.RuleArgumentRendering
