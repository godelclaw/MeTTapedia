import Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
import Mettapedia.GSLT.LanguageDef.PatternSpanExecution
import Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming
import Mettapedia.Computability.FramedWordSuffixRemoval

/-!
# Executing authored first-order inference schemas

Fixed schema constructors become literal original token fields. Declared
metavariables become positional holes in the existing indexed word copier.
Arguments retain their original token storage, including opaque binder and
collection values. Complete emitted claims use the original Pattern codec;
the source checker remains the authority for argument and rule admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.Binding.WireCodec Binary
open InferenceChecker InferenceInstantiationBridge
open Mettapedia.Computability
open Turing StateTransition Polynomial

abbrev fields := PatternSpanExecution.Execution.fields

def argumentBody (pattern : Pattern) : List Alphabet := fields (PatternTokens.encode pattern)

def patternWire (pattern : Pattern) : List Alphabet :=
  encodeWith CertificateDataEncoding.patternCodec pattern

theorem patternWire_body (pattern : Pattern) :
    patternWire pattern = argumentBody pattern ++ [3, 2] := by
  exact PatternSpanExecution.Execution.tokenWire_eq (PatternTokens.encode pattern)

theorem fields_append (first second : List String) :
    fields (first ++ second) = fields first ++ fields second := by
  simp [fields, PatternSpanExecution.Execution.fields]

theorem write_split (pattern : Pattern) (tail : List String) :
    PatternTokens.write pattern tail = PatternTokens.encode pattern ++ tail := by
  simpa only [PatternTokens.encode, List.nil_append] using
    PatternTokens.write_append pattern [] tail

def literals {arity : Nat} (tokens : List String) : WordTemplateMachine.Indexed.Template Alphabet arity :=
  (fields tokens).map Sum.inl

mutual
  /-- This compiler refuses undeclared holes and schema constructors outside
  the original first-order instantiation fragment. -/
  def compile (names : List String) : Pattern →
      Option (WordTemplateMachine.Indexed.Template Alphabet names.length)
    | .bvar index => some (literals (PatternTokens.encode (.bvar index)))
    | .fvar name => if member : name ∈ names then
        some [.inr ⟨names.idxOf name, List.idxOf_lt_length_iff.mpr member⟩] else none
    | .apply name arguments => do
        let children ← compileList names arguments
        pure (literals ["a", name] ++ children)
    | .collection kind elements none => do
        let children ← compileList names elements
        pure (literals ["c", PatternTokens.collection kind, "n"] ++ children)
    | _ => none
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec
  def compileList (names : List String) : List Pattern →
      Option (WordTemplateMachine.Indexed.Template Alphabet names.length)
    | [] => some (literals ["z"])
    | pattern :: patterns => do
        let head ← compile names pattern
        let tail ← compileList names patterns
        pure (literals ["h"] ++ head ++ tail)
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

def argumentValues (names : List String) (arguments : List Pattern)
    (arity : arguments.length = names.length) : Fin names.length → Pattern :=
  fun index => arguments[index.val]'(by rw [arity]; exact index.isLt)

def argumentBodies (names : List String) (arguments : List Pattern)
    (arity : arguments.length = names.length) : Fin names.length → List Alphabet :=
  fun index => argumentBody (argumentValues names arguments arity index)

mutual
  /-- The machine's literal/hole plan agrees with original source substitution,
  including repeated holes, authored child order and fixed collections. -/
  theorem compile_exact {names : List String} {pattern : Pattern}
      (fragment : BindingSchemaFragment (names.map fun name => (name, 0)) pattern)
      (distinct : names.Nodup) (arguments : List Pattern)
      (arity : arguments.length = names.length) :
      ∃ template, compile names pattern = some template ∧
        WordTemplateMachine.Indexed.instantiate template (argumentBodies names arguments arity) =
          argumentBody (applyBindings (names.zip arguments) pattern) := by
    cases fragment with
    | bvar index =>
        refine ⟨literals (PatternTokens.encode (.bvar index)), ?_, ?_⟩
        · simp only [compile]
        · simp [literals, argumentBody, applyBindings]
    | @fvar name declared =>
        have member : name ∈ names := by
          obtain ⟨value, included, equal⟩ := List.mem_map.mp declared
          cases equal
          exact included
        have bound : names.idxOf name < arguments.length := by
          rw [arity]
          exact List.idxOf_lt_length_iff.mpr member
        have found := SortedFirstOrderRules.find?_zip distinct (List.getElem?_idxOf member)
          (List.getElem?_eq_getElem bound)
        refine ⟨[.inr ⟨names.idxOf name, List.idxOf_lt_length_iff.mpr member⟩], ?_, ?_⟩
        · simp only [compile, dif_pos member]
        · simp [WordTemplateMachine.Indexed.instantiate, argumentBodies,
            argumentValues, applyBindings, found]
    | @apply constructor patterns items =>
        obtain ⟨children, compiled, exactChildren⟩ := compileList_exact items distinct arguments arity
        refine ⟨literals ["a", constructor] ++ children, ?_, ?_⟩
        · simp only [compile, compiled]; rfl
        · simp only [WordTemplateMachine.Indexed.instantiate_append, literals,
            WordTemplateMachine.Indexed.instantiate_literals, exactChildren,
            argumentBody, applyBindings, PatternTokens.encode, PatternTokens.write,
            fields, PatternSpanExecution.Execution.fields,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | @collection kind patterns items =>
        obtain ⟨children, compiled, exactChildren⟩ := compileList_exact items distinct arguments arity
        refine ⟨literals ["c", PatternTokens.collection kind, "n"] ++ children, ?_, ?_⟩
        · simp only [compile, compiled]; rfl
        · simp only [WordTemplateMachine.Indexed.instantiate_append, literals,
            WordTemplateMachine.Indexed.instantiate_literals, exactChildren,
            argumentBody, applyBindings, List.append_nil, PatternTokens.encode,
            PatternTokens.write, PatternTokens.option, fields,
            PatternSpanExecution.Execution.fields, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.append_assoc]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec
  theorem compileList_exact {names : List String} {patterns : List Pattern}
      (fragment : BindingSchemasFragment (names.map fun name => (name, 0)) patterns)
      (distinct : names.Nodup) (arguments : List Pattern)
      (arity : arguments.length = names.length) :
      ∃ template, compileList names patterns = some template ∧
        WordTemplateMachine.Indexed.instantiate template (argumentBodies names arguments arity) =
          fields (PatternTokens.writeList (patterns.map (applyBindings (names.zip arguments))) []) := by
    cases fragment with
    | nil =>
        refine ⟨literals ["z"], ?_, ?_⟩
        · simp only [compileList]
        · simp [literals, PatternTokens.writeList]
    | @cons pattern patterns head tail =>
        obtain ⟨headTemplate, headCompiled, headExact⟩ := compile_exact head distinct arguments arity
        obtain ⟨tailTemplate, tailCompiled, tailExact⟩ := compileList_exact tail distinct arguments arity
        refine ⟨literals ["h"] ++ headTemplate ++ tailTemplate, ?_, ?_⟩
        · simp only [compileList, headCompiled, tailCompiled]; rfl
        · simp only [WordTemplateMachine.Indexed.instantiate_append, literals,
            headExact, tailExact,
            List.map_cons, PatternTokens.writeList, write_split,
            argumentBody, fields, PatternSpanExecution.Execution.fields,
            List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.append_nil, List.append_assoc]
          simp only [WordTemplateMachine.Indexed.instantiate_literal,
            WordTemplateMachine.Indexed.instantiate_literals]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

def compilePattern (names : List String) (pattern : Pattern) :
    Option (WordTemplateMachine.Indexed.Template Alphabet names.length) :=
  (compile names pattern).map fun body => body ++ ([3, 2] : List Alphabet).map Sum.inl

theorem compilePattern_exact {names : List String} {pattern : Pattern}
    (fragment : BindingSchemaFragment (names.map fun name => (name, 0)) pattern)
    (distinct : names.Nodup) (arguments : List Pattern)
    (arity : arguments.length = names.length) :
    ∃ template, compilePattern names pattern = some template ∧
      WordTemplateMachine.Indexed.instantiate template (argumentBodies names arguments arity) =
        patternWire (applyBindings (names.zip arguments) pattern) := by
  obtain ⟨body, compiled, exactBody⟩ := compile_exact fragment distinct arguments arity
  refine ⟨body ++ ([3, 2] : List Alphabet).map Sum.inl, ?_, ?_⟩
  · simp only [compilePattern, compiled, Option.map_some]
  · rw [WordTemplateMachine.Indexed.instantiate_append,
      WordTemplateMachine.Indexed.instantiate_literals, exactBody, patternWire_body]

def bodyVector (arguments : List Pattern) : List (Option Alphabet) :=
  WordTemplateMachine.Indexed.frame (arguments.map argumentBody)

theorem instantiateVector {names : List String} (template : WordTemplateMachine.Indexed.Template Alphabet names.length)
    (arguments : List Pattern) (arity : arguments.length = names.length) :
    WordTemplateMachine.Indexed.instantiateWire template (bodyVector arguments) =
      WordTemplateMachine.Indexed.instantiate template (argumentBodies names arguments arity) := by
  unfold WordTemplateMachine.Indexed.instantiateWire
  congr 1
  funext index
  have bound : index.val < (arguments.map argumentBody).length := by simp only [List.length_map]; omega
  have selected := WordTemplateMachine.Indexed.select_frame index ⟨0, by omega⟩
    (arguments.map argumentBody) (by simp only [List.length_map]; omega)
  simpa only [bodyVector, Fin.val_zero, Nat.zero_le, if_true, Nat.sub_zero,
    List.getElem?_eq_getElem bound, Option.getD_some, List.getElem_map,
    argumentBodies, argumentValues] using selected

def originalVector (arguments : List Pattern) : List (Option Alphabet) :=
  CertificateArgumentFraming.framedArguments CertificateDataEncoding.patternCodec arguments

theorem originalVector_source (arguments : List Pattern) :
    originalVector arguments = FramedWordSuffixRemoval.source (3 : Alphabet) 2
      (arguments.map argumentBody) := by
  unfold originalVector CertificateArgumentFraming.framedArguments
    CertificateArgumentFraming.argumentWords FramedWordSuffixRemoval.source
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro argument _
  exact patternWire_body argument

theorem bodyVector_length_le (arguments : List Pattern) :
    (bodyVector arguments).length ≤ (originalVector arguments).length := by
  have copied := FramedWordSuffixRemoval.copied_length_le (3 : Alphabet) 2 (arguments.map argumentBody)
  simpa only [FramedWordSuffixRemoval.copied, List.length_map, ← originalVector_source,
    bodyVector] using copied

def stripMachine : FinTM2 := FramedWordSuffixRemoval.machine (3 : Alphabet) 2

def strippedOutput (arguments : List Pattern) : List (Option Alphabet ⊕ Bool) :=
  .inr true :: (bodyVector arguments).map Sum.inl

def stripOutputs (arguments : List Pattern) :
    TM2OutputsInTime stripMachine (originalVector arguments) (some (strippedOutput arguments))
      (2 * (originalVector arguments).length + 3) := by
  rw [originalVector_source]
  exact FramedWordSuffixRemoval.outputs (3 : Alphabet) 2 (arguments.map argumentBody)

def normalize : Option Alphabet ⊕ Bool → List (Option Alphabet)
  | .inl symbol => [symbol]
  | .inr admitted => [some (if admitted then 1 else 0)]

theorem normalize_stripped (arguments : List Pattern) :
    (strippedOutput arguments).flatMap normalize = some (1 : Alphabet) :: bodyVector arguments := by
  simp only [strippedOutput, List.flatMap_cons, normalize, if_true,
    List.singleton_append, List.flatMap_map]
  congr 1
  induction bodyVector arguments with
  | nil => rfl
  | cons value values ih => simp only [List.flatMap_cons, List.singleton_append, ih]

theorem normalize_length (word : List (Option Alphabet ⊕ Bool)) :
    (word.flatMap normalize).length = word.length := by
  induction word with
  | nil => rfl
  | cons value values ih =>
      cases value <;> simp only [List.flatMap_cons, normalize, List.length_append,
        List.length_cons, List.length_nil, ih] <;> omega

attribute [local implicit_reducible] stripMachine FramedWordSuffixRemoval.machine

local instance : Fintype (stripMachine.Γ stripMachine.k₁) := by
  change Fintype (Option Alphabet ⊕ Bool); infer_instance
local instance : Inhabited (stripMachine.Γ stripMachine.k₀) := by
  change Inhabited (Option Alphabet); infer_instance

def accepted : Option Alphabet → Bool := fun symbol => symbol == some 1

def stripDispatcher : FinTM2 :=
  StackMachineComposition.Dispatch.machine stripMachine accepted [.inr false]

attribute [local implicit_reducible] stripDispatcher CertificateArgumentFraming.Execution.machine

local instance (arity : Nat) : Fintype
    ((CertificateArgumentFraming.Execution.machine arity).Γ (CertificateArgumentFraming.Execution.machine arity).k₁) := by
  change Fintype (Option Alphabet); infer_instance
local instance (arity : Nat) : Inhabited
    ((CertificateArgumentFraming.Execution.machine arity).Γ (CertificateArgumentFraming.Execution.machine arity).k₁) := by
  change Inhabited (Option Alphabet); infer_instance
local instance : Inhabited (stripDispatcher.Γ stripDispatcher.k₀) := by
  change Inhabited (Option Alphabet); infer_instance

def stripAtArityMachine (arity : Nat) : FinTM2 :=
  StackMachineComposition.machine (CertificateArgumentFraming.Execution.machine arity) stripDispatcher (Equiv.refl _)

def stripAtArityResult (arity : Nat) (arguments : List Pattern) : List (Option Alphabet ⊕ Bool) :=
  if arguments.length = arity then strippedOutput arguments else [.inr false]

def inputWire (arguments : List Pattern) : List Alphabet :=
  encodeWith (Codec.list CertificateDataEncoding.patternCodec) arguments

theorem vector_length_le (arguments : List Pattern) :
    (originalVector arguments).length + 2 = (inputWire arguments).length :=
  CertificateArgumentFraming.framedArguments_length CertificateDataEncoding.patternCodec arguments

noncomputable def stripDispatchOutputs (arity : Nat) (arguments : List Pattern) :
    TM2OutputsInTime stripDispatcher
      (CertificateArgumentFraming.statusWire
        (CertificateArgumentFraming.Execution.frameAtArity CertificateDataEncoding.patternCodec arity arguments))
      (some (stripAtArityResult arity arguments)) (2 * (inputWire arguments).length + 4) := by
  by_cases admitted : arguments.length = arity
  · have execution := StackMachineComposition.Dispatch.outputs_success stripMachine accepted [.inr false]
      (some (1 : Alphabet)) (originalVector arguments) (strippedOutput arguments)
      (2 * (originalVector arguments).length + 3) (by rfl) (stripOutputs arguments)
    apply WordEqualityMachine.within (by
      simpa only [stripDispatcher, CertificateArgumentFraming.Execution.frameAtArity, admitted,
        if_true, CertificateArgumentFraming.statusWire, stripAtArityResult, originalVector,
        TM2OutputsInTime] using execution)
    have size := vector_length_le arguments
    simp only [originalVector] at size
    omega
  · have execution := StackMachineComposition.Dispatch.outputs_refused stripMachine accepted [.inr false]
      (some (0 : Alphabet)) [] (by rfl)
    apply WordEqualityMachine.within (by
      simpa only [stripDispatcher, CertificateArgumentFraming.Execution.frameAtArity, admitted,
        if_false, CertificateArgumentFraming.statusWire, stripAtArityResult, TM2OutputsInTime] using execution)
    simp only [List.length_nil]
    omega

noncomputable def stripAtArityOutputs (arity : Nat) (arguments : List Pattern) :
    TM2OutputsInTime (stripAtArityMachine arity) (inputWire arguments)
      (some (stripAtArityResult arity arguments)) (12 * (inputWire arguments).length + 15) := by
  have first := CertificateArgumentFraming.Execution.outputsAtArity
    CertificateDataEncoding.patternCodec arity arguments
  have second := stripDispatchOutputs arity arguments
  have execution := StackMachineComposition.outputs (CertificateArgumentFraming.Execution.machine arity)
    stripDispatcher (Equiv.refl _) (inputWire arguments)
    (CertificateArgumentFraming.statusWire
      (CertificateArgumentFraming.Execution.frameAtArity CertificateDataEncoding.patternCodec arity arguments))
    (stripAtArityResult arity arguments) (7 * (inputWire arguments).length + 8)
    (2 * (inputWire arguments).length + 4) first (by
      change TM2OutputsInTime stripDispatcher
        ((CertificateArgumentFraming.statusWire
          (CertificateArgumentFraming.Execution.frameAtArity CertificateDataEncoding.patternCodec arity arguments)).map id)
        (some (stripAtArityResult arity arguments)) _
      simpa only [List.map_id_fun, id_eq] using second)
  apply WordEqualityMachine.within execution
  have size : (CertificateArgumentFraming.statusWire
      (CertificateArgumentFraming.Execution.frameAtArity CertificateDataEncoding.patternCodec arity arguments)).length ≤
      (inputWire arguments).length := by
    by_cases admitted : arguments.length = arity
    · simpa only [CertificateArgumentFraming.Execution.frameAtArity, admitted, if_true, inputWire] using
        CertificateArgumentFraming.status_length_le CertificateDataEncoding.patternCodec arguments
    · have size := vector_length_le arguments
      simp only [CertificateArgumentFraming.Execution.frameAtArity, admitted, if_false,
        CertificateArgumentFraming.statusWire, List.length_cons, List.length_nil]
      omega
  omega

theorem stripResult_length_le (arity : Nat) (arguments : List Pattern) :
    (stripAtArityResult arity arguments).length ≤ (inputWire arguments).length := by
  have original := vector_length_le arguments
  have copied := bodyVector_length_le arguments
  unfold stripAtArityResult
  split
  · simp only [strippedOutput, List.length_cons, List.length_map]; omega
  · simp only [List.length_cons, List.length_nil]; omega

attribute [local implicit_reducible] stripAtArityMachine

local instance (arity : Nat) : Fintype ((stripAtArityMachine arity).Γ (stripAtArityMachine arity).k₁) := by
  change Fintype (Option Alphabet ⊕ Bool); infer_instance
local instance (arity : Nat) : Inhabited ((stripAtArityMachine arity).Γ (stripAtArityMachine arity).k₁) := by
  change Inhabited (Option Alphabet ⊕ Bool); infer_instance

def normalizedMachine (arity : Nat) : FinTM2 :=
  StackMachineComposition.machine (stripAtArityMachine arity) (WordHomomorphismMachine.machine normalize) (Equiv.refl _)

def normalizedResult (arity : Nat) (arguments : List Pattern) : List (Option Alphabet) :=
  if arguments.length = arity then some 1 :: bodyVector arguments else [some 0]

theorem normalizedResult_eq (arity : Nat) (arguments : List Pattern) :
    normalizedResult arity arguments = (stripAtArityResult arity arguments).flatMap normalize := by
  by_cases admitted : arguments.length = arity
  · simp only [normalizedResult, stripAtArityResult, admitted, if_true, normalize_stripped]
  · simp [normalizedResult, stripAtArityResult, admitted, normalize]

theorem normalizedResult_length_le (arity : Nat) (arguments : List Pattern) :
    (normalizedResult arity arguments).length ≤ (inputWire arguments).length := by
  rw [normalizedResult_eq, normalize_length]
  exact stripResult_length_le arity arguments

noncomputable def normalizedOutputs (arity : Nat) (arguments : List Pattern) :
    TM2OutputsInTime (normalizedMachine arity) (inputWire arguments)
      (some (normalizedResult arity arguments)) (20 * ((inputWire arguments).length + 1)) := by
  have first := stripAtArityOutputs arity arguments
  have second := WordHomomorphismMachine.outputs normalize (stripAtArityResult arity arguments)
  have execution := StackMachineComposition.outputs (stripAtArityMachine arity)
    (WordHomomorphismMachine.machine normalize) (Equiv.refl _) (inputWire arguments)
    (stripAtArityResult arity arguments) (normalizedResult arity arguments)
    (12 * (inputWire arguments).length + 15)
    (2 * (stripAtArityResult arity arguments).length +
      2 * ((stripAtArityResult arity arguments).flatMap normalize).length + 2) first (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine normalize)
        ((stripAtArityResult arity arguments).map id) _ _
      simpa only [List.map_id_fun, id_eq, normalizedResult_eq] using second)
  apply WordEqualityMachine.within execution
  have size := stripResult_length_le arity arguments
  rw [normalize_length]
  omega

attribute [local implicit_reducible] WordTemplateMachine.Indexed.machine WordTemplateMachine.Indexed.Alphabet normalizedMachine

def copier {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) : FinTM2 :=
  WordTemplateMachine.Indexed.machine (.inl (1 : Alphabet) :: template)

attribute [local implicit_reducible] copier

local instance {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :
    Fintype ((copier template).Γ (copier template).k₁) := by
  change Fintype Alphabet; infer_instance
local instance {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :
    Inhabited ((copier template).Γ (copier template).k₀) := by
  change Inhabited (Option Alphabet); infer_instance

def copyDispatcher {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) : FinTM2 :=
  StackMachineComposition.Dispatch.machine (copier template) accepted [(0 : Alphabet)]

attribute [local implicit_reducible] copyDispatcher

def result {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity)
    (arguments : List Pattern) : Option (List Alphabet) :=
  if arguments.length = arity then
    some (WordTemplateMachine.Indexed.instantiateWire template (bodyVector arguments)) else none

noncomputable def copyDispatchOutputs {arity : Nat}
    (template : WordTemplateMachine.Indexed.Template Alphabet arity) (arguments : List Pattern) :
    TM2OutputsInTime (copyDispatcher template) (normalizedResult arity arguments)
      (some (CertificateArgumentFraming.Execution.resultWire (result template arguments)))
      (4 * (template.length + 2) * ((inputWire arguments).length + 1) + 1) := by
  by_cases admitted : arguments.length = arity
  · have copied := WordTemplateMachine.Indexed.outputsWire (.inl (1 : Alphabet) :: template) (bodyVector arguments)
    have execution := StackMachineComposition.Dispatch.outputs_success (copier template) accepted [(0 : Alphabet)]
      (some (1 : Alphabet)) (bodyVector arguments)
      ((1 : Alphabet) :: WordTemplateMachine.Indexed.instantiateWire template (bodyVector arguments))
      (4 * ((.inl (1 : Alphabet) :: template).length + 1) * ((bodyVector arguments).length + 1))
      (by rfl) (by simpa only [copier, WordTemplateMachine.Indexed.instantiateWire_literal] using copied)
    apply WordEqualityMachine.within (by
      simpa only [copyDispatcher, normalizedResult, result, admitted, if_true,
        CertificateArgumentFraming.Execution.resultWire, TM2OutputsInTime] using execution)
    have original := vector_length_le arguments
    have size := bodyVector_length_le arguments
    simp only [List.length_cons]
    nlinarith
  · have execution := StackMachineComposition.Dispatch.outputs_refused (copier template) accepted [(0 : Alphabet)]
      (some (0 : Alphabet)) [] (by rfl)
    apply WordEqualityMachine.within (by
      simpa only [copyDispatcher, normalizedResult, result, admitted, if_false,
        CertificateArgumentFraming.Execution.resultWire, TM2OutputsInTime] using execution)
    simp only [List.length_nil]
    nlinarith

local instance (arity : Nat) : Fintype ((normalizedMachine arity).Γ (normalizedMachine arity).k₁) := by
  change Fintype (Option Alphabet); infer_instance
local instance (arity : Nat) : Inhabited ((normalizedMachine arity).Γ (normalizedMachine arity).k₁) := by
  change Inhabited (Option Alphabet); infer_instance
local instance {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :
    Inhabited ((copyDispatcher template).Γ (copyDispatcher template).k₀) := by
  change Inhabited (Option Alphabet); infer_instance

/-- The complete phase uses the original list parser, physical terminator
removal, status conversions and indexed copying. Arity refusal clears scratch
and emits the same distinct original result-wire refusal. -/
def machine {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) : FinTM2 :=
  StackMachineComposition.machine (normalizedMachine arity) (copyDispatcher template) (Equiv.refl _)

noncomputable def outputs {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity)
    (arguments : List Pattern) : TM2OutputsInTime (machine template) (inputWire arguments)
      (some (CertificateArgumentFraming.Execution.resultWire (result template arguments)))
      (30 * (template.length + 2) * ((inputWire arguments).length + 1)) := by
  have first := normalizedOutputs arity arguments
  have second := copyDispatchOutputs template arguments
  have execution := StackMachineComposition.outputs (normalizedMachine arity) (copyDispatcher template)
    (Equiv.refl _) (inputWire arguments) (normalizedResult arity arguments)
    (CertificateArgumentFraming.Execution.resultWire (result template arguments))
    (20 * ((inputWire arguments).length + 1))
    (4 * (template.length + 2) * ((inputWire arguments).length + 1) + 1) first (by
      change TM2OutputsInTime (copyDispatcher template) ((normalizedResult arity arguments).map id) _ _
      simpa only [List.map_id_fun, id_eq] using second)
  apply WordEqualityMachine.within execution
  have size := normalizedResult_length_le arity arguments
  nlinarith

/-- Original instantiated claims, obtained by executing the compiled plan on
complete original argument-list bytes, rather than by a field-output oracle. -/
noncomputable def schemaOutputs {names : List String} {pattern : Pattern}
    (fragment : BindingSchemaFragment (names.map fun name => (name, 0)) pattern)
    (distinct : names.Nodup) {template : WordTemplateMachine.Indexed.Template Alphabet names.length}
    (compiled : compilePattern names pattern = some template) (arguments : List Pattern)
    (arity : arguments.length = names.length) :
    TM2OutputsInTime (machine template) (inputWire arguments)
      (some (CertificateArgumentFraming.Execution.resultWire
        (some (patternWire (applyBindings (names.zip arguments) pattern)))))
      (30 * (template.length + 2) * ((inputWire arguments).length + 1)) := by
  have exactPlan : WordTemplateMachine.Indexed.instantiate template
      (argumentBodies names arguments arity) = patternWire (applyBindings (names.zip arguments) pattern) := by
    obtain ⟨actual, same, exactPlan⟩ := compilePattern_exact fragment distinct arguments arity
    have equal : actual = template := Option.some.inj (same.symm.trans compiled)
    subst actual
    exact exactPlan
  have execution := outputs template arguments
  simpa only [result, arity, if_true, instantiateVector template arguments arity, exactPlan] using execution

/-- The premise vector uses its original list-of-patterns codec, distinct from
the structural child-list tokens occurring inside a pattern. -/
def compilePremiseFields (names : List String) : List Pattern →
    Option (WordTemplateMachine.Indexed.Template Alphabet names.length)
  | [] => some (([3, 2] : List Alphabet).map Sum.inl)
  | premise :: premises => do
      let head ← compilePattern names premise
      let tail ← compilePremiseFields names premises
      pure (.inl 4 :: head ++ tail)

def fieldsCodec : Codec (List Pattern × Pattern) :=
  Codec.prod (Codec.list CertificateDataEncoding.patternCodec) CertificateDataEncoding.patternCodec

def compileJudgments (names : List String) (premises : List Pattern) (conclusion : Pattern) :
    Option (WordTemplateMachine.Indexed.Template Alphabet names.length) := do
  let heads ← compilePremiseFields names premises
  let final ← compilePattern names conclusion
  pure (.inl 4 :: heads ++ final)

theorem patternList_cons (pattern : Pattern) (patterns : List Pattern) :
    encodeWith (Codec.list CertificateDataEncoding.patternCodec) (pattern :: patterns) =
      4 :: patternWire pattern ++ encodeWith (Codec.list CertificateDataEncoding.patternCodec) patterns := by
  simp only [encodeWith_list, patternWire, List.flatMap_cons, List.append_assoc]

theorem compilePremiseFields_exact {names : List String} {premises : List Pattern}
    (fragment : BindingSchemasFragment (names.map fun name => (name, 0)) premises)
    (distinct : names.Nodup) (arguments : List Pattern) (arity : arguments.length = names.length) :
    ∃ template, compilePremiseFields names premises = some template ∧
      WordTemplateMachine.Indexed.instantiate template (argumentBodies names arguments arity) =
        encodeWith (Codec.list CertificateDataEncoding.patternCodec)
          (premises.map (applyBindings (names.zip arguments))) := by
  cases fragment with
  | nil =>
      refine ⟨([3, 2] : List Alphabet).map Sum.inl, rfl, ?_⟩
      rw [WordTemplateMachine.Indexed.instantiate_literals]
      rfl
  | @cons premise premises head tail =>
      obtain ⟨headTemplate, headCompiled, headExact⟩ := compilePattern_exact head distinct arguments arity
      obtain ⟨tailTemplate, tailCompiled, tailExact⟩ := compilePremiseFields_exact tail distinct arguments arity
      refine ⟨.inl 4 :: headTemplate ++ tailTemplate, ?_, ?_⟩
      · simp only [compilePremiseFields, headCompiled, tailCompiled]; rfl
      · simp only [WordTemplateMachine.Indexed.instantiate_literal,
          WordTemplateMachine.Indexed.instantiate_append, headExact, tailExact,
          List.map_cons, patternList_cons]
  termination_by premises.length

theorem compileJudgments_exact {names : List String} {premises : List Pattern} {conclusion : Pattern}
    (premiseFragment : BindingSchemasFragment (names.map fun name => (name, 0)) premises)
    (conclusionFragment : BindingSchemaFragment (names.map fun name => (name, 0)) conclusion)
    (distinct : names.Nodup) (arguments : List Pattern) (arity : arguments.length = names.length) :
    ∃ template, compileJudgments names premises conclusion = some template ∧
      WordTemplateMachine.Indexed.instantiate template (argumentBodies names arguments arity) =
        encodeWith fieldsCodec (premises.map (applyBindings (names.zip arguments)),
          applyBindings (names.zip arguments) conclusion) := by
  obtain ⟨heads, headCompiled, headExact⟩ := compilePremiseFields_exact premiseFragment distinct arguments arity
  obtain ⟨final, finalCompiled, finalExact⟩ := compilePattern_exact conclusionFragment distinct arguments arity
  refine ⟨.inl 4 :: heads ++ final, ?_, ?_⟩
  · simp only [compileJudgments, headCompiled, finalCompiled]; rfl
  · simp only [WordTemplateMachine.Indexed.instantiate_literal,
      WordTemplateMachine.Indexed.instantiate_append, headExact, finalExact,
      fieldsCodec, encodeWith, Codec.prod, encodeData_pair, patternWire, List.cons_append]

/-- All instantiated premises and the conclusion are emitted together in the
original field encoding. Repeated premises remain separate physical fields. -/
noncomputable def judgmentsOutputs {names : List String} {premises : List Pattern} {conclusion : Pattern}
    (premiseFragment : BindingSchemasFragment (names.map fun name => (name, 0)) premises)
    (conclusionFragment : BindingSchemaFragment (names.map fun name => (name, 0)) conclusion)
    (distinct : names.Nodup) {template : WordTemplateMachine.Indexed.Template Alphabet names.length}
    (compiled : compileJudgments names premises conclusion = some template) (arguments : List Pattern)
    (arity : arguments.length = names.length) :
    TM2OutputsInTime (machine template) (inputWire arguments)
      (some (CertificateArgumentFraming.Execution.resultWire
        (some (encodeWith fieldsCodec (premises.map (applyBindings (names.zip arguments)),
          applyBindings (names.zip arguments) conclusion)))))
      (30 * (template.length + 2) * ((inputWire arguments).length + 1)) := by
  have exactPlan : WordTemplateMachine.Indexed.instantiate template (argumentBodies names arguments arity) =
      encodeWith fieldsCodec (premises.map (applyBindings (names.zip arguments)),
        applyBindings (names.zip arguments) conclusion) := by
    obtain ⟨actual, same, exactPlan⟩ := compileJudgments_exact premiseFragment conclusionFragment distinct arguments arity
    have equal : actual = template := Option.some.inj (same.symm.trans compiled)
    subst actual
    exact exactPlan
  have execution := outputs template arguments
  simpa only [result, arity, if_true, instantiateVector template arguments arity, exactPlan] using execution

theorem sourceSchema_exact {names : List String} {pattern : Pattern}
    (fragment : BindingSchemaFragment (names.map fun name => (name, 0)) pattern)
    (distinct : names.Nodup) (arguments : List Pattern) (arity : arguments.length = names.length) :
    instantiateSchema? (names.map fun name => (name, 0)) arguments pattern =
      some (applyBindings (names.zip arguments) pattern) := by
  apply instantiateSchema?_eq_applyBindings fragment
  apply argumentsOfBindings?_of_bindingsOfArguments
  · rw [List.map_map]
    change (names.map id).Nodup
    simpa only [List.map_id] using distinct
  · intro formal member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl
  · exact FirstOrderRules.bindingsOfArguments?_formals names arguments arity

theorem sourcePremises_exact {names : List String} {premises : List Pattern}
    (fragment : BindingSchemasFragment (names.map fun name => (name, 0)) premises)
    (distinct : names.Nodup) (arguments : List Pattern) (arity : arguments.length = names.length) :
    instantiateSchemas? (names.map fun name => (name, 0)) arguments premises =
      some (premises.map (applyBindings (names.zip arguments))) := by
  change instantiateSchemasAt? (names.map fun name => (name, 0)) arguments 0 premises = _
  apply instantiateSchemasAt?_eq_applyBindings fragment
  apply argumentsOfBindings?_of_bindingsOfArguments
  · rw [List.map_map]
    change (names.map id).Nodup
    simpa only [List.map_id] using distinct
  · intro formal member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl
  · exact FirstOrderRules.bindingsOfArguments?_formals names arguments arity

/-- The existing source admission and field instantiator agree for an authored
row in the all-zero first-order schema fragment. -/
theorem sourceRule_exact {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {rule : RuleSchema} {names : List String}
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some rule)
    (formals : rule.metavariables = names.map fun name => (name, 0))
    (premiseFragment : BindingSchemasFragment (names.map fun name => (name, 0)) rule.premises)
    (conclusionFragment : BindingSchemaFragment (names.map fun name => (name, 0)) rule.conclusion)
    (distinct : names.Nodup)
    (admitted : argumentsValidAt rule.metavariables ruleInstance.arguments = true)
    (conditions : RuleSchema.sideConditionsHold rule ruleInstance.arguments = true) :
    instantiateRule? definition ruleInstance = some
      (rule.premises.map (applyBindings (names.zip ruleInstance.arguments)),
        applyBindings (names.zip ruleInstance.arguments) rule.conclusion) := by
  have arity : ruleInstance.arguments.length = names.length := by
    have same := (argumentsValidAt_length admitted).symm
    simpa only [formals, List.length_map] using same
  have admittedMapped : argumentsValidAt (names.map fun name => (name, 0)) ruleInstance.arguments = true := by
    simpa only [formals] using admitted
  simp only [instantiateRule?, lookup, conditions, if_true,
    formals, admittedMapped, sourcePremises_exact premiseFragment distinct ruleInstance.arguments arity,
    sourceSchema_exact conclusionFragment distinct ruleInstance.arguments arity]
  rfl

/-- Once the original row and its independent admission checks are established,
the physically emitted fields are exactly the original instantiation result. -/
noncomputable def ruleOutputs {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {rule : RuleSchema} {names : List String}
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some rule)
    (formals : rule.metavariables = names.map fun name => (name, 0))
    (premiseFragment : BindingSchemasFragment (names.map fun name => (name, 0)) rule.premises)
    (conclusionFragment : BindingSchemaFragment (names.map fun name => (name, 0)) rule.conclusion)
    (distinct : names.Nodup)
    (admitted : argumentsValidAt rule.metavariables ruleInstance.arguments = true)
    (conditions : RuleSchema.sideConditionsHold rule ruleInstance.arguments = true)
    {template : WordTemplateMachine.Indexed.Template Alphabet names.length}
    (compiled : compileJudgments names rule.premises rule.conclusion = some template) :
    TM2OutputsInTime (machine template) (inputWire ruleInstance.arguments)
      (some (CertificateArgumentFraming.Execution.resultWire
        ((instantiateRule? definition ruleInstance).map (encodeWith fieldsCodec))))
      (30 * (template.length + 2) * ((inputWire ruleInstance.arguments).length + 1)) := by
  rw [sourceRule_exact lookup formals premiseFragment conclusionFragment distinct admitted conditions]
  have arity : ruleInstance.arguments.length = names.length := by
    have same := (argumentsValidAt_length admitted).symm
    simpa only [formals, List.length_map] using same
  exact judgmentsOutputs premiseFragment conclusionFragment distinct compiled ruleInstance.arguments arity

/-- Complete equality remains the shared original-codec comparison, including
all opaque metadata. Constructor-head agreement alone is not enough. -/
def compareOutputs (expected supplied : Pattern) :
    TM2OutputsInTime (WordEqualityMachine.machine Alphabet)
      (Binary.Equality.packet CertificateDataEncoding.patternCodec expected supplied)
      (some [decide (expected = supplied)])
      (3 * (Binary.Equality.packet CertificateDataEncoding.patternCodec expected supplied).length + 1) := by
  apply WordEqualityMachine.within (Binary.Equality.outputs CertificateDataEncoding.patternCodec expected supplied)
  rw [Binary.Equality.packet_length]
  omega


namespace Authored

open InferenceExtension

/-- The compiled plan and refusal flag depend only on the authored row. -/
def compiled (rule : RuleSchema) :=
  compileJudgments (rule.metavariables.map Prod.fst) rule.premises rule.conclusion

def plan (rule : RuleSchema) :
    WordTemplateMachine.Indexed.Template Alphabet (rule.metavariables.map Prod.fst).length :=
  (compiled rule).getD []

def accepts (enabled : Bool) (symbol : Alphabet) : Bool :=
  enabled && symbol == 1

attribute [local implicit_reducible] CertificateSchemaInstantiation.machine
  CertificateDataTraversal.ProductField.machine StackMachineComposition.Dispatch.machine
  StackMachineComposition.machine

local instance {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :
    Fintype ((CertificateSchemaInstantiation.machine template).Γ
      (CertificateSchemaInstantiation.machine template).k₁) := by
  change Fintype Alphabet; infer_instance
local instance {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :
    Inhabited ((CertificateSchemaInstantiation.machine template).Γ
      (CertificateSchemaInstantiation.machine template).k₀) := by
  change Inhabited Alphabet; infer_instance
local instance : Fintype ((CertificateDataTraversal.ProductField.machine true).Γ
    (CertificateDataTraversal.ProductField.machine true).k₁) := by
  change Fintype Alphabet; infer_instance
local instance : Inhabited ((CertificateDataTraversal.ProductField.machine true).Γ
    (CertificateDataTraversal.ProductField.machine true).k₁) := by
  change Inhabited Alphabet; infer_instance

/-- Both original instance fields are physically read before the selected
row executes its original argument-list and indexed-substitution program. -/
def localMachine {arity : Nat}
    (template : WordTemplateMachine.Indexed.Template Alphabet arity) (enabled : Bool) : FinTM2 :=
  StackMachineComposition.machine (CertificateDataTraversal.ProductField.machine true)
    (StackMachineComposition.Dispatch.machine
      (CertificateSchemaInstantiation.machine template) (accepts enabled) [(0 : Alphabet)])
    (Equiv.refl Alphabet)

attribute [local implicit_reducible] localMachine

def localResult {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity)
    (enabled : Bool) (ruleInstance : RuleInstance) : List Alphabet :=
  if enabled then CertificateArgumentFraming.Execution.resultWire
    (CertificateSchemaInstantiation.result template ruleInstance.arguments) else [(0 : Alphabet)]

/-- The bound includes complete product extraction, the status read,
argument arity parsing, terminator removal, substitution and both handoffs. -/
noncomputable def localOutputs {arity : Nat}
    (template : WordTemplateMachine.Indexed.Template Alphabet arity) (enabled : Bool)
    (ruleInstance : RuleInstance) :
    TM2OutputsInTime (localMachine template enabled)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (localResult template enabled ruleInstance))
      (50 * (template.length + 2) *
        ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)) := by
  let input := encodeWith CertificateDataEncoding.instanceCodec ruleInstance
  let arguments := inputWire ruleInstance.arguments
  have extracted := CertificateRuleAdmission.argumentFieldOutputs ruleInstance
  have size : arguments.length ≤ input.length := CertificateRuleAdmission.arguments_length_le ruleInstance
  cases enabled with
  | true =>
    have source := CertificateSchemaInstantiation.outputs template ruleInstance.arguments
    have second := StackMachineComposition.Dispatch.outputs_success
      (CertificateSchemaInstantiation.machine template) (accepts true) [(0 : Alphabet)] (1 : Alphabet)
      arguments (CertificateArgumentFraming.Execution.resultWire
        (CertificateSchemaInstantiation.result template ruleInstance.arguments))
      (30 * (template.length + 2) * (arguments.length + 1)) (by rfl) source
    have joined := StackMachineComposition.outputs (CertificateDataTraversal.ProductField.machine true)
      (StackMachineComposition.Dispatch.machine
        (CertificateSchemaInstantiation.machine template) (accepts true) [(0 : Alphabet)])
      (Equiv.refl Alphabet) input ((1 : Alphabet) :: arguments)
      (localResult template true ruleInstance) (4 * input.length + 3)
      (30 * (template.length + 2) * (arguments.length + 1) + 1) extracted (by
        change TM2OutputsInTime (StackMachineComposition.Dispatch.machine
          (CertificateSchemaInstantiation.machine template) (accepts true) [(0 : Alphabet)])
          (((1 : Alphabet) :: arguments).map id) _ _
        simpa only [List.map_id_fun, id_eq, localResult, Bool.true_eq, if_true] using second)
    apply WordEqualityMachine.within joined
    simp only [List.length_cons]
    nlinarith
  | false =>
    have second := StackMachineComposition.Dispatch.outputs_refused
      (CertificateSchemaInstantiation.machine template) (accepts false) [(0 : Alphabet)] (1 : Alphabet)
      arguments (by rfl)
    have joined := StackMachineComposition.outputs (CertificateDataTraversal.ProductField.machine true)
      (StackMachineComposition.Dispatch.machine
        (CertificateSchemaInstantiation.machine template) (accepts false) [(0 : Alphabet)])
      (Equiv.refl Alphabet) input ((1 : Alphabet) :: arguments)
      (localResult template false ruleInstance) (4 * input.length + 3)
      (arguments.length + 2) extracted (by
        change TM2OutputsInTime (StackMachineComposition.Dispatch.machine
          (CertificateSchemaInstantiation.machine template) (accepts false) [(0 : Alphabet)])
          (((1 : Alphabet) :: arguments).map id) _ _
        simpa only [List.map_id_fun, id_eq, localResult, Bool.false_eq_true, if_false] using second)
    apply WordEqualityMachine.within joined
    simp only [List.length_cons]
    nlinarith

/-- All schema rows use one physical stack/state family. Their authored
arity, template and finite continuation labels may differ. -/
abbrev Base := localMachine ([] : WordTemplateMachine.Indexed.Template Alphabet 0) true

variable (definition : CalculusLanguageDef)
abbrev Row := Fin definition.rules.length

theorem cellTypes (index : Row definition) (key : Base.K) :
    (localMachine (plan (CertificateRuleAdmission.row definition index))
      (compiled (CertificateRuleAdmission.row definition index)).isSome).Γ key = Base.Γ key := by
  rfl

def family : CommonArenaDispatch.Family Base (Row definition) where
  alphabet index := (localMachine (plan (CertificateRuleAdmission.row definition index))
    (compiled (CertificateRuleAdmission.row definition index)).isSome).Γ
  cellTypes := cellTypes definition
  Label index := (localMachine (plan (CertificateRuleAdmission.row definition index))
    (compiled (CertificateRuleAdmission.row definition index)).isSome).Λ
  labelFinite index := (localMachine (plan (CertificateRuleAdmission.row definition index))
    (compiled (CertificateRuleAdmission.row definition index)).isSome).ΛFin
  main index := (localMachine (plan (CertificateRuleAdmission.row definition index))
    (compiled (CertificateRuleAdmission.row definition index)).isSome).main
  body index := (localMachine (plan (CertificateRuleAdmission.row definition index))
    (compiled (CertificateRuleAdmission.row definition index)).isSome).m

/-- One fixed authored table determines every row program before inputs arrive. -/
def dispatcher : FinTM2 :=
  CommonArenaDispatch.machine Base (family definition) (0 : Alphabet) (0 : Alphabet)

attribute [local implicit_reducible] dispatcher

def rowResult (choice : Option (Row definition)) (ruleInstance : RuleInstance) : List Alphabet :=
  match choice with
  | none => [0]
  | some index => localResult (plan (CertificateRuleAdmission.row definition index))
      (compiled (CertificateRuleAdmission.row definition index)).isSome ruleInstance

/-- The finite authored table contributes a fixed coefficient, independent
of dynamic argument values and their physical encoded lengths. -/
def planBudget : Nat :=
  (definition.rules.map (fun rule => (plan rule).length + 2)).sum + 2

theorem row_plan_le (index : Row definition) :
    (plan (CertificateRuleAdmission.row definition index)).length + 2 ≤ planBudget definition := by
  have member : CertificateRuleAdmission.row definition index ∈ definition.rules :=
    List.get_mem definition.rules index
  have mapped : (plan (CertificateRuleAdmission.row definition index)).length + 2 ∈
      definition.rules.map (fun rule => (plan rule).length + 2) :=
    List.mem_map.mpr ⟨_, member, rfl⟩
  have bounded := List.single_le_sum (fun (_ : Nat) _ => Nat.zero_le _) _ mapped
  unfold planBudget
  omega

noncomputable def dispatchOutputs (choice : Option (Row definition)) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (dispatcher definition)
      (.inr choice :: (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map Sum.inl)
      (some (rowResult definition choice ruleInstance))
      ((55 * planBudget definition + 6) *
        ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)) := by
  let input := encodeWith CertificateDataEncoding.instanceCodec ruleInstance
  cases choice with
  | none =>
    have refused := CommonArenaDispatch.outputs_absent Base (family definition)
      (0 : Alphabet) (0 : Alphabet) input
    apply WordEqualityMachine.within refused
    dsimp only [input]
    have budget : 2 ≤ planBudget definition := by unfold planBudget; omega
    nlinarith
  | some index =>
    let rule := CertificateRuleAdmission.row definition index
    have source := localOutputs (plan rule) (compiled rule).isSome ruleInstance
    have selected : TM2OutputsInTime ((family definition).toMachine index)
        (input.map (CommonArenaDispatch.cellTypes Base (family definition) index Base.k₀).mpr)
        (some ((localResult (plan rule) (compiled rule).isSome ruleInstance).map
          (CommonArenaDispatch.cellTypes Base (family definition) index Base.k₁).mpr))
        (50 * ((plan rule).length + 2) * (input.length + 1)) := by
      change TM2OutputsInTime (localMachine (plan rule) (compiled rule).isSome)
        (input.map id) (some ((localResult (plan rule) (compiled rule).isSome ruleInstance).map id)) _
      simpa only [List.map_id_fun, id_eq] using source
    have executed := CommonArenaDispatch.outputs_selected Base (family definition)
      (0 : Alphabet) (0 : Alphabet) index input
      (localResult (plan rule) (compiled rule).isSome ruleInstance)
      (50 * ((plan rule).length + 2) * (input.length + 1)) selected
    apply WordEqualityMachine.within executed
    have budget := row_plan_le definition index
    change (plan rule).length + 2 ≤ planBudget definition at budget
    nlinarith

local instance : Fintype (Base.Γ Base.k₀) := by change Fintype Alphabet; infer_instance
local instance (definition : CalculusLanguageDef) : Fintype
    ((CertificateRuleAdmission.machine definition).Γ (CertificateRuleAdmission.machine definition).k₁) := by
  change Fintype (Alphabet ⊕ Option (Row definition)); infer_instance
local instance (definition : CalculusLanguageDef) : Inhabited
    ((CertificateRuleAdmission.machine definition).Γ (CertificateRuleAdmission.machine definition).k₁) := by
  change Inhabited (Alphabet ⊕ Option (Row definition)); infer_instance

/-- Executed first-row lookup feeds the common finite schema dispatcher. -/
def machine : FinTM2 := StackMachineComposition.machine
  (CertificateRuleAdmission.machine definition) (dispatcher definition) (Equiv.refl _)

attribute [local implicit_reducible] machine

def output (ruleInstance : RuleInstance) : List Alphabet :=
  rowResult definition (CertificateRuleAdmission.selected definition ruleInstance) ruleInstance

/-- The complete instance image drives actual lookup, full input retention,
argument extraction and schema emission. Unknown rows, unsupported schemas
and wrong argument counts return explicit refusal. -/
noncomputable def outputs (ruleInstance : RuleInstance) :
    TM2OutputsInTime (machine definition)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (output definition ruleInstance))
      ((55 * planBudget definition + 40) *
        ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)) := by
  have first := CertificateRuleAdmission.outputs definition ruleInstance
  have second := dispatchOutputs definition
    (CertificateRuleAdmission.selected definition ruleInstance) ruleInstance
  have joined := StackMachineComposition.outputs (CertificateRuleAdmission.machine definition)
    (dispatcher definition) (Equiv.refl _)
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
    (CertificateRuleAdmission.output definition ruleInstance) (output definition ruleInstance)
    (12 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 15)
    ((55 * planBudget definition + 6) *
      ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)) first (by
      change TM2OutputsInTime (dispatcher definition)
        ((CertificateRuleAdmission.output definition ruleInstance).map id) _ _
      simpa only [List.map_id_fun, id_eq, CertificateRuleAdmission.output, output] using second)
  apply WordEqualityMachine.within joined
  simp only [CertificateRuleAdmission.output, List.length_cons, List.length_map]
  nlinarith

/-- The emitted fields agree with original rule instantiation once its
original scope and side-condition obligations hold. This phase does not
replace those judgments or the later child-claim comparisons. -/
theorem output_of_rule {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {rule : RuleSchema}
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some rule)
    (formals : rule.metavariables =
      (rule.metavariables.map Prod.fst).map (fun name => (name, 0)))
    (premiseFragment : BindingSchemasFragment rule.metavariables rule.premises)
    (conclusionFragment : BindingSchemaFragment rule.metavariables rule.conclusion)
    (distinct : (rule.metavariables.map Prod.fst).Nodup)
    (admitted : argumentsValidAt rule.metavariables ruleInstance.arguments = true)
    (conditions : RuleSchema.sideConditionsHold rule ruleInstance.arguments = true) :
    output definition.1 ruleInstance = CertificateArgumentFraming.Execution.resultWire
      ((instantiateRule? definition ruleInstance).map (encodeWith fieldsCodec)) := by
  let names := rule.metavariables.map Prod.fst
  have arity : ruleInstance.arguments.length = names.length := by
    have lengths := (argumentsValidAt_length admitted).symm
    simpa only [names, List.length_map] using lengths
  have premises : BindingSchemasFragment (names.map fun name => (name, 0)) rule.premises := by
    dsimp only [names]
    rw [← formals]
    exact premiseFragment
  have conclusion : BindingSchemaFragment (names.map fun name => (name, 0)) rule.conclusion := by
    dsimp only [names]
    rw [← formals]
    exact conclusionFragment
  obtain ⟨template, compilation, exactFields⟩ :=
    compileJudgments_exact premises conclusion distinct ruleInstance.arguments arity
  have compileSame : compiled rule = some template := compilation
  have planSame : plan rule = template := by simp only [plan, compileSame, Option.getD_some]
  obtain ⟨index, selected, rowSame⟩ : ∃ index : Fin definition.1.rules.length,
      CertificateRuleAdmission.selected definition.1 ruleInstance = some index ∧
      CertificateRuleAdmission.row definition.1 index = rule := by
    have same := CertificateRuleAdmission.selected_lookup definition.1 ruleInstance
    cases found : CertificateRuleAdmission.selected definition.1 ruleInstance with
    | none => simp only [found, Option.map_none, lookup] at same; cases same
    | some index =>
      refine ⟨index, rfl, ?_⟩
      simpa only [found, Option.map_some, lookup, Option.some.injEq] using same
  have source := sourceRule_exact lookup formals premises conclusion distinct admitted conditions
  rw [output, selected]
  change localResult (plan (CertificateRuleAdmission.row definition.1 index))
    (compiled (CertificateRuleAdmission.row definition.1 index)).isSome ruleInstance = _
  rw [congrArg (fun row => localResult (plan row) (compiled row).isSome ruleInstance) rowSame]
  simp only [localResult, compileSame, Option.isSome_some, if_true, planSame,
    CertificateSchemaInstantiation.result]
  have arityExact : ruleInstance.arguments.length = (rule.metavariables.map Prod.fst).length := arity
  rw [if_pos arityExact, instantiateVector template ruleInstance.arguments arity, exactFields, source]
  rfl


/-- This is one fixed authored-table machine, independent of the input instance. -/
noncomputable def ruleOutputs {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {rule : RuleSchema}
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some rule)
    (formals : rule.metavariables =
      (rule.metavariables.map Prod.fst).map (fun name => (name, 0)))
    (premiseFragment : BindingSchemasFragment rule.metavariables rule.premises)
    (conclusionFragment : BindingSchemaFragment rule.metavariables rule.conclusion)
    (distinct : (rule.metavariables.map Prod.fst).Nodup)
    (admitted : argumentsValidAt rule.metavariables ruleInstance.arguments = true)
    (conditions : RuleSchema.sideConditionsHold rule ruleInstance.arguments = true) :
    TM2OutputsInTime (machine definition.1)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (CertificateArgumentFraming.Execution.resultWire
        ((instantiateRule? definition ruleInstance).map (encodeWith fieldsCodec))))
      ((55 * planBudget definition.1 + 40) *
        ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)) := by
  rw [← output_of_rule lookup formals premiseFragment conclusionFragment distinct admitted conditions]
  exact outputs definition.1 ruleInstance

end Authored

namespace Controls

def repeated : Pattern := .apply "Pair" [.fvar "x", .fvar "x"]
def closedBinder : Pattern := .lambda none (.bvar 0)

theorem repeated_fragment : BindingSchemaFragment [("x", 0)] repeated := by
  exact .apply (.cons (.fvar (by simp)) (.cons (.fvar (by simp)) .nil))

theorem repeated_binder_instance :
    instantiateSchema? [("x", 0)] [closedBinder] repeated =
      some (.apply "Pair" [closedBinder, closedBinder]) := by
  simp [instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?, lookupArgumentAt?, repeated]

theorem ordered_repeated_premises :
    instantiateSchemas? [("x", 0)] [closedBinder]
      [.fvar "x", .apply "P" [.fvar "x"], .fvar "x"] =
      some [closedBinder, .apply "P" [closedBinder], closedBinder] := by
  simp [instantiateSchemas?, instantiateSchemaAt?, instantiateSchemasAt?, lookupArgumentAt?]

theorem fixed_collections (kind : CollType) :
    instantiateSchema? [("x", 0)] [closedBinder]
      (.collection kind [.fvar "x", .fvar "x"] none) =
      some (.collection kind [closedBinder, closedBinder] none) := by
  simp [instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?, lookupArgumentAt?]

theorem declared_hole_compiles :
    (compilePattern ["x"] repeated).isSome = true := by
  simp [compilePattern, compile, compileList, repeated]

theorem undeclared_hole_refused : compilePattern ["x"] (.fvar "y") = none := by
  simp [compilePattern, compile]

theorem schema_binder_refused :
    compilePattern [] closedBinder = none := by
  simp [compilePattern, compile, closedBinder]

theorem schema_substitution_refused :
    compilePattern ["x"] (.subst (.fvar "x") (.fvar "x")) = none := by
  simp [compilePattern, compile]

theorem schema_rest_refused :
    compilePattern ["x"] (.collection .hashBag [.fvar "x"] (some "x")) = none := by
  simp [compilePattern, compile]

theorem arity_missing {arity : Nat}
    (template : WordTemplateMachine.Indexed.Template Alphabet (arity + 1)) :
    result template [] = none := by
  simp [result]

theorem arity_excess (template : WordTemplateMachine.Indexed.Template Alphabet 0)
    (argument : Pattern) :
    result template [argument] = none := by
  simp [result]

/-- Byte substitution transports opaque values; original semantic argument
admission is still required before those fields authorize a rule job. -/
theorem unscoped_argument_refused : argumentValidAt 0 (.bvar 0) = false := rfl

end Controls

end Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation
