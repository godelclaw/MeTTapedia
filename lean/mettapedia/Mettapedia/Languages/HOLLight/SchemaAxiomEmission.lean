import Mettapedia.Languages.HOLLight.InferenceCompiler
import Mettapedia.Computability.CommonArenaDispatch
import Mettapedia.Computability.FiniteWordClassifier
import Mettapedia.Computability.WordTemplateMachine
import Mettapedia.Computability.FramedWordMapping
import Mettapedia.Computability.FramedWordDecoding
import Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming

/-!
# Executed generation of the fixed authored HOL axiom prefix

The input supplies a complete original source rule schema and its physical
row index. A finite classifier checks all schema bytes against the fixed
compiled calculus, then dispatches the corresponding original receipt emitter.
Duplicate authored rows retain separate physical origins. Every unrecognized
word is drained and refused; accepted outputs decode to the original compiler
receipt and are admitted by its original axiom policy. The ordered-prefix
wrapper first checks the complete original authored packet, physically frames
its rows, executes every row, and collects the independent receipt readout
into the original checked chronological axiom graph.

This stage specializes one fixed calculus. Its finite program contains the
complete authored and generated payloads. It does not establish a compiler
which interprets arbitrary calculus specifications supplied at run time.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SchemaAxiomEmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef InferenceChecker CertificateDataEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability Turing Polynomial
open Mettapedia.Languages.OpenTheory
open InferenceRuleExpansion

/-- Every original side-condition constructor retains all its numeric fields. -/
def conditionCodec : Codec RuleSideCondition where
  put
    | .explicitSubstitution depth body replacement result =>
        .pair (.atom 0) (.pair (.atom depth) (.pair (.atom body) (.pair (.atom replacement) (.atom result))))
    | .unusedBinderElimination depth body result =>
        .pair (.atom 1) (.pair (.atom depth) (.pair (.atom body) (.atom result)))
  get
    | .pair (.atom 0) (.pair (.atom depth) (.pair (.atom body) (.pair (.atom replacement) (.atom result)))) =>
        some (.explicitSubstitution depth body replacement result)
    | .pair (.atom 1) (.pair (.atom depth) (.pair (.atom body) (.atom result))) =>
        some (.unusedBinderElimination depth body result)
    | _ => none
  get_put condition := by cases condition <;> rfl

/-- Storage of the original schema, retaining depths, ordered premises,
conclusion and all guards. Patterns reuse the original certificate codec. -/
def schemaCodec : Codec RuleSchema :=
  (Codec.prod Codec.string
    (Codec.prod (Codec.list (Codec.prod Codec.string Codec.nat))
      (Codec.prod (Codec.list patternCodec) (Codec.prod patternCodec (Codec.list conditionCodec))))).mapped
    (fun rule => (rule.id.value, (rule.metavariables, (rule.premises, (rule.conclusion, rule.sideConditions)))))
    (fun fields => some ⟨⟨fields.1⟩, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2⟩)
    (fun rule => by cases rule; rfl)

/-- The original physical row index distinguishes repeated authored schemas. -/
def rowCodec : Codec (Nat × RuleSchema) := Codec.prod Codec.nat schemaCodec

abbrev Row (definition : CalculusLanguageDef) := Fin definition.rules.length

def row (definition : CalculusLanguageDef) (index : Row definition) : RuleSchema :=
  definition.rules.get index

def sourceRow (definition : CalculusLanguageDef) (index : Row definition) : Nat × RuleSchema :=
  (index.val, row definition index)

def axiomIndex (definition : CalculusLanguageDef) (index : Row definition) :
    Fin (InferenceCompiler.compileAxioms definition).length :=
  ⟨index.val, by rw [InferenceCompiler.compileAxioms_length]; exact index.isLt⟩

def receipt (definition : CalculusLanguageDef) (index : Row definition) : ProofExecution.Receipt :=
  InferenceCompiler.axiomReceipt definition (axiomIndex definition index)

theorem compileAxioms_rules (definition : CalculusLanguageDef) :
    InferenceCompiler.compileAxioms definition = definition.rules.map ruleSequent := by
  simp only [InferenceCompiler.compileAxioms, Mettapedia.Logic.HOL.Embedding.InferenceRules.axioms,
    Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation.inferenceRules, List.map_map, Function.comp_def]
  rfl

theorem receipt_original (definition : CalculusLanguageDef) (index : Row definition) :
    receipt definition index = Emission.axiomNode (row definition index) ("rule",index.val) := by
  unfold receipt InferenceCompiler.axiomReceipt
  have sequent : (InferenceCompiler.compileAxioms definition).get (axiomIndex definition index) =
      ruleSequent (row definition index) := by
    simp [compileAxioms_rules, row, axiomIndex]
  simp only [sequent, Emission.axiomNode, ruleTheorem]
  rfl

def words (definition : CalculusLanguageDef) : Row definition → List Alphabet :=
  Dictionary.words rowCodec (sourceRow definition)

def selected (definition : CalculusLanguageDef) (source : Nat × RuleSchema) : Option (Row definition) :=
  Dictionary.result rowCodec (sourceRow definition) source

theorem selected_fields {definition : CalculusLanguageDef} {source : Nat × RuleSchema} {index : Row definition}
    (found : selected definition source = some index) : source = sourceRow definition index := by
  let _ := rowCodec.decEq
  have matched := List.find?_some (p := fun candidate => decide (source = sourceRow definition candidate)) found
  exact of_decide_eq_true matched

theorem sourceRow_injective (definition : CalculusLanguageDef) : Function.Injective (sourceRow definition) := by
  intro first second same
  exact Fin.ext (congrArg Prod.fst same)

theorem selected_row (definition : CalculusLanguageDef) (index : Row definition) :
    selected definition (sourceRow definition index) = some index := by
  let _ := rowCodec.decEq
  change (List.finRange definition.rules.length).find?
    (fun candidate => decide (sourceRow definition index = sourceRow definition candidate)) = some index
  have predicate : (fun candidate => decide (sourceRow definition index = sourceRow definition candidate)) =
      (fun candidate => decide (index = candidate)) := by
    funext candidate
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (sourceRow_injective definition).eq_iff
  rw [predicate, List.find?_eq_some_iff_getElem]
  refine ⟨by simp, index.val, by simp, by simp, ?_⟩
  intro earlier before
  simp [Fin.ext_iff, show index.val ≠ earlier by omega]

def targetWord (definition : CalculusLanguageDef) (index : Row definition) : List Alphabet :=
  1 :: encodeWith ProofDataEncoding.receiptCodec (receipt definition index)

def template (definition : CalculusLanguageDef) (index : Row definition) : WordTemplateMachine.Template Alphabet :=
  (targetWord definition index).map some

/-- Fixed-C program storage includes every complete generated receipt byte. -/
def payloadBudget (definition : CalculusLanguageDef) : Nat :=
  ∑ index : Row definition, (targetWord definition index).length

theorem template_length_le (definition : CalculusLanguageDef) (index : Row definition) :
    (template definition index).length ≤ payloadBudget definition := by
  simp only [template,List.length_map]
  exact Finset.single_le_sum (fun candidate _ => Nat.zero_le ((targetWord definition candidate).length))
    (Finset.mem_univ index)

abbrev Base := WordTemplateMachine.machine ([] : WordTemplateMachine.Template Alphabet)

def family (definition : CalculusLanguageDef) : CommonArenaDispatch.Family Base (Row definition) where
  alphabet _ _ := Alphabet
  cellTypes _ _ := rfl
  Label index := WordTemplateMachine.Phase (template definition index).length
  labelFinite _ := inferInstance
  main _ := .emit ⟨0,by omega⟩
  body index := WordTemplateMachine.program (template definition index)

def dispatcher (definition : CalculusLanguageDef) : FinTM2 :=
  CommonArenaDispatch.machine Base (family definition) (0 : Alphabet) (0 : Alphabet)

def choiceWord (definition : CalculusLanguageDef) : Option (Row definition) → List Alphabet
  | none => [0]
  | some index => targetWord definition index

attribute [local implicit_reducible] dispatcher

noncomputable def dispatchOutputs (definition : CalculusLanguageDef) (choice : Option (Row definition))
    (input : List Alphabet) :
    TM2OutputsInTime (dispatcher definition) (.inr choice :: input.map Sum.inl)
      (some (choiceWord definition choice))
      (2*input.length + 4*(payloadBudget definition+1)*(input.length+1)+4) := by
  cases choice with
  | none =>
      have executed := CommonArenaDispatch.outputs_absent Base (family definition) (0 : Alphabet) (0 : Alphabet) input
      apply WordEqualityMachine.within executed
      omega
  | some index =>
      have source := WordTemplateMachine.outputs (template definition index) input
      simp only [template, WordTemplateMachine.instantiate_literals] at source
      have selectedRun : TM2OutputsInTime ((family definition).toMachine index)
          (input.map (CommonArenaDispatch.cellTypes Base (family definition) index Base.k₀).mpr)
          (some ((targetWord definition index).map
            (CommonArenaDispatch.cellTypes Base (family definition) index Base.k₁).mpr))
          (4*((template definition index).length+1)*(input.length+1)) := by
        change TM2OutputsInTime (WordTemplateMachine.machine (template definition index))
          (input.map id) (some ((targetWord definition index).map id)) _
        simpa only [List.map_id_fun,id_eq,template] using source
      have executed := CommonArenaDispatch.outputs_selected Base (family definition) (0 : Alphabet) (0 : Alphabet)
        index input (targetWord definition index) (4*((template definition index).length+1)*(input.length+1)) selectedRun
      apply WordEqualityMachine.within executed
      have lengthBound := template_length_le definition index
      nlinarith

local instance (definition : CalculusLanguageDef) :
    Fintype ((FiniteWordClassifier.machine (words definition)).Γ (FiniteWordClassifier.machine (words definition)).k₁) := by
  change Fintype (Sum Alphabet (Option (Row definition)))
  infer_instance
local instance (definition : CalculusLanguageDef) :
    Inhabited ((FiniteWordClassifier.machine (words definition)).Γ (FiniteWordClassifier.machine (words definition)).k₁) := by
  change Inhabited (Sum Alphabet (Option (Row definition)))
  infer_instance

def machine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (FiniteWordClassifier.machine (words definition)) (dispatcher definition)
    (Equiv.refl (Sum Alphabet (Option (Row definition))))

attribute [local implicit_reducible] machine

def rawOutput (definition : CalculusLanguageDef) (input : List Alphabet) : List Alphabet :=
  choiceWord definition (FiniteWordClassifier.classify (words definition) input)

/-- Every input symbol is scanned, restored, transferred, and either drained
after refusal or used by the selected original receipt template. -/
noncomputable def rawOutputs (definition : CalculusLanguageDef) (input : List Alphabet) :
    TM2OutputsInTime (machine definition) input (some (rawOutput definition input))
      (6*input.length + 4*(payloadBudget definition+1)*(input.length+1)+10) := by
  have classified := FiniteWordClassifier.outputs (words definition) input
  have emitted := dispatchOutputs definition (FiniteWordClassifier.classify (words definition) input) input
  have joined := StackMachineComposition.outputs (FiniteWordClassifier.machine (words definition)) (dispatcher definition)
    (Equiv.refl (Sum Alphabet (Option (Row definition)))) input
    (.inr (FiniteWordClassifier.classify (words definition) input) :: input.map Sum.inl)
    (rawOutput definition input) (2*input.length+2)
    (2*input.length+4*(payloadBudget definition+1)*(input.length+1)+4) classified (by
      change TM2OutputsInTime (dispatcher definition)
        ((.inr (FiniteWordClassifier.classify (words definition) input) :: input.map Sum.inl).map id) _ _
      simpa only [List.map_id_fun,id_eq,rawOutput] using emitted)
  convert joined using 1
  all_goals first | rfl | (simp only [List.length_cons,List.length_map]; ring)

theorem output_source (definition : CalculusLanguageDef) (source : Nat × RuleSchema) :
    rawOutput definition (encodeWith rowCodec source) = choiceWord definition (selected definition source) := by
  exact congrArg (choiceWord definition) (Dictionary.classify_original rowCodec (sourceRow definition) source)

theorem output_row (definition : CalculusLanguageDef) (index : Row definition) :
    rawOutput definition (encodeWith rowCodec (sourceRow definition index)) = targetWord definition index := by
  rw [output_source,selected_row]
  rfl

theorem output_decodes (definition : CalculusLanguageDef) (index : Row definition) :
    decodeWith ProofDataEncoding.receiptCodec
      (rawOutput definition (encodeWith rowCodec (sourceRow definition index))).tail =
      some (InferenceCompiler.axiomReceipt definition (axiomIndex definition index)) := by
  rw [output_row]
  exact decodeWith_encodeWith ProofDataEncoding.receiptCodec _

theorem output_checked (definition : CalculusLanguageDef) (index : Row definition) :
    (receipt definition index).witness.check (InferenceHosting.policy
      (Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation.inferenceRules definition)) =
      some (receipt definition index).conclusion :=
  InferenceCompiler.axiomReceipt_checked definition (axiomIndex definition index)

theorem output_refused (definition : CalculusLanguageDef) (input : List Alphabet)
    (unknown : ∀ index, input ≠ words definition index) : rawOutput definition input = [0] := by
  unfold rawOutput
  rw [(FiniteWordClassifier.classify_none_iff (words definition) input).mpr unknown]
  rfl


/-- Byte storage of the complete fixed authored rows, including Unicode names,
large numeric depths and every side condition. -/
def authoredBytes (definition : CalculusLanguageDef) : Nat :=
  ∑ index : Row definition, (words definition index).length

/-- This is descriptor payload size, not an enumeration of all control states. -/
def fixedPayloadBytes (definition : CalculusLanguageDef) : Nat :=
  authoredBytes definition + payloadBudget definition

noncomputable def realization (definition : CalculusLanguageDef) :
    TM2ComputableInPolyTime (fun word : List Alphabet => word) (fun word : List Alphabet => word)
      (rawOutput definition) where
  tm := machine definition
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C (4*(fixedPayloadBytes definition+1)+6)*X + C (4*(fixedPayloadBytes definition+1)+10)
  outputsFun input := by
    change TM2OutputsInTime (machine definition) (input.map id)
      (some ((rawOutput definition input).map id)) _
    simp only [List.map_id_fun,id_eq]
    apply WordEqualityMachine.within (rawOutputs definition input)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    unfold fixedPayloadBytes
    nlinarith

theorem receipt_origin (definition : CalculusLanguageDef) (index : Row definition) :
    (receipt definition index).origin = ("rule",index.val) := rfl

theorem targetWord_injective (definition : CalculusLanguageDef) : Function.Injective (targetWord definition) := by
  intro first second same
  have encoded : encodeWith ProofDataEncoding.receiptCodec (receipt definition first) =
      encodeWith ProofDataEncoding.receiptCodec (receipt definition second) := (List.cons.inj same).2
  have receipts := (encodeWith_injective ProofDataEncoding.receiptCodec) encoded
  have origins := congrArg (fun receipt : ProofExecution.Receipt => receipt.origin.2) receipts
  exact Fin.ext origins

/-- A successful original receipt decode comes only from a complete original
fixed row. No raw suffix, altered guard or different row index is admitted. -/
theorem decoded_source {definition : CalculusLanguageDef} {input : List Alphabet} {out : ProofExecution.Receipt}
    (decoded : decodeWith ProofDataEncoding.receiptCodec (rawOutput definition input).tail = some out) :
    ∃ index : Row definition, input = words definition index ∧ out = receipt definition index := by
  cases found : FiniteWordClassifier.classify (words definition) input with
  | none =>
      have empty : decodeWith ProofDataEncoding.receiptCodec ([] : List Alphabet) = none := rfl
      simp only [rawOutput,found,choiceWord,List.tail_cons] at decoded
      rw [empty] at decoded
      cases decoded
  | some index =>
      refine ⟨index,FiniteWordClassifier.classify_sound (words definition) input index found,?_⟩
      have same : some (receipt definition index) = some out := by
        simpa only [rawOutput,found,choiceWord,targetWord,List.tail_cons,decodeWith_encodeWith] using decoded
      exact (Option.some.inj same).symm

theorem decoded_checked {definition : CalculusLanguageDef} {input : List Alphabet} {out : ProofExecution.Receipt}
    (decoded : decodeWith ProofDataEncoding.receiptCodec (rawOutput definition input).tail = some out) :
    out.witness.check (InferenceHosting.policy (FirstOrder.InferenceTranslation.inferenceRules definition)) =
      some out.conclusion := by
  obtain ⟨index,_,rfl⟩ := decoded_source decoded
  exact output_checked definition index

/-- Fixed alphabet and complete original bodies; evaluating this interface
need not construct the machine's bundled finite-enumeration witnesses. -/
def program (definition : CalculusLanguageDef) :=
  StackMachineComposition.Programs.body FiniteWordClassifier.Stack.result
    (CommonArenaDispatch.inputKey Base) CommonArenaDispatch.Phase.read
    (default : Sum Alphabet (Option (Row definition))) id
    (FiniteWordClassifier.program (words definition))
    (CommonArenaDispatch.program Base (family definition) (0 : Alphabet) (0 : Alphabet))

theorem program_eq (definition : CalculusLanguageDef) : program definition = (machine definition).m := by
  exact StackMachineComposition.body_eq (FiniteWordClassifier.machine (words definition)) (dispatcher definition)
    (Equiv.refl (Sum Alphabet (Option (Row definition))))

theorem decoded_admitted {definition : CalculusLanguageDef} {input : List Alphabet} {out : ProofExecution.Receipt}
    (decoded : decodeWith ProofDataEncoding.receiptCodec (rawOutput definition input).tail = some out) :
    InferenceHosting.policy (FirstOrder.InferenceTranslation.inferenceRules definition) out.conclusion.sequent := by
  obtain ⟨index,_,rfl⟩ := decoded_source decoded
  rw [receipt_original]
  exact ruleSequent_admitted (List.getElem_mem index.isLt)

end Mettapedia.Languages.HOLLight.SchemaAxiomEmission

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.SchemaAxiomEmission.Prefix
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability Turing Polynomial
open WordTemplateMachine WordTemplateMachine.Indexed

variable (definition : CalculusLanguageDef)

attribute [local implicit_reducible] SchemaAxiomEmission.machine SchemaAxiomEmission.dispatcher
  WordTemplateMachine.machine StackMachineComposition.machine CommonArenaDispatch.machine
  FramedWordMapping.machine CertificateArgumentFraming.Execution.machine CommonArenaDispatch.Family.toMachine
  StackMachineComposition.Dispatch.machine

def sourceRows : List (Nat × RuleSchema) := List.ofFn (sourceRow definition)
def receiptRows : List ProofExecution.Receipt := List.ofFn (receipt definition)

theorem receiptRows_original : receiptRows definition = InferenceCompiler.axiomGraph definition := by
  apply List.ext_getElem
  · simp [receiptRows,InferenceCompiler.axiomGraph,InferenceCompiler.compileAxioms_length]
  · intro index before after
    simp only [receiptRows,InferenceCompiler.axiomGraph,List.getElem_ofFn,receipt,axiomIndex]

def encodeRow (source : Nat × RuleSchema) : List Alphabet := encodeWith rowCodec source
def emitRow (source : Nat × RuleSchema) : List Alphabet := rawOutput definition (encodeRow source)
def rowClock (source : Nat × RuleSchema) : Nat :=
  6*(encodeRow source).length+4*(payloadBudget definition+1)*((encodeRow source).length+1)+10

local instance : Fintype ((SchemaAxiomEmission.machine definition).Γ (SchemaAxiomEmission.machine definition).k₁) := by
  change Fintype Alphabet; infer_instance
local instance : Inhabited ((SchemaAxiomEmission.machine definition).Γ (SchemaAxiomEmission.machine definition).k₀) := by
  change Inhabited Alphabet; infer_instance
local instance : Inhabited ((SchemaAxiomEmission.machine definition).Γ (SchemaAxiomEmission.machine definition).k₁) := by
  change Inhabited Alphabet; infer_instance

def mappingMachine := FramedWordMapping.machine (SchemaAxiomEmission.machine definition)
attribute [local implicit_reducible] mappingMachine
def mappedWords (sources : List (Nat × RuleSchema)) : List (Option Alphabet) := frame (sources.map (emitRow definition))
def mappingClock (sources : List (Nat × RuleSchema)) : Nat :=
  FramedWordMapping.totalClock (SchemaAxiomEmission.machine definition) encodeRow (emitRow definition)
    (rowClock definition) sources

noncomputable def mappingOutputs (sources : List (Nat × RuleSchema)) :
    TM2OutputsInTime (mappingMachine definition) (frame (sources.map encodeRow))
      (some (mappedWords definition sources)) (mappingClock definition sources) := by
  exact FramedWordMapping.outputs (SchemaAxiomEmission.machine definition) encodeRow (emitRow definition)
    (rowClock definition) (fun source => rawOutputs definition (encodeRow source)) sources

def readReceipt : List Alphabet → Option ProofExecution.Receipt
  | 1 :: body => decodeWith ProofDataEncoding.receiptCodec body
  | _ => none

def decodePrefix (word : List (Option Alphabet)) : Option (List ProofExecution.Receipt) := do
  let words ← Indexed.decodeFrames word
  words.mapM readReceipt

theorem readReceipt_targetWord (index : Row definition) :
    readReceipt (targetWord definition index) = some (receipt definition index) := by
  exact decodeWith_encodeWith ProofDataEncoding.receiptCodec _

theorem decodePrefix_receipts (receipts : List ProofExecution.Receipt) :
    decodePrefix (frame (receipts.map fun node => (1 : Alphabet)::encodeWith ProofDataEncoding.receiptCodec node)) =
      some receipts := by
  have mapDecoded : (receipts.map fun node => (1 : Alphabet)::encodeWith ProofDataEncoding.receiptCodec node).mapM readReceipt = some receipts := by
    induction receipts with
    | nil => rfl
    | cons node rest ih => simp [List.mapM_cons,readReceipt,decodeWith_encodeWith,ih]
  simpa only [decodePrefix,Indexed.decodeFrames_frame,Option.bind_eq_bind,Option.bind_some] using mapDecoded

theorem mapped_authored :
    mappedWords definition (sourceRows definition) =
      frame ((receiptRows definition).map fun node => (1 : Alphabet)::encodeWith ProofDataEncoding.receiptCodec node) := by
  unfold mappedWords sourceRows receiptRows
  rw [List.map_ofFn,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext index
  exact output_row definition index

theorem decode_authored : decodePrefix (mappedWords definition (sourceRows definition)) =
    some (InferenceCompiler.axiomGraph definition) := by
  rw [mapped_authored,decodePrefix_receipts,receiptRows_original]

/-- The emitted chronological graph earns the existing checker judgment. -/
theorem authored_checked :
    ∃ graph cache, decodePrefix (mappedWords definition (sourceRows definition)) = some graph ∧
      Mettapedia.Logic.DerivationGraph.replay (ruleWitness
        (InferenceHosting.policy (FirstOrder.InferenceTranslation.inferenceRules definition))) graph = some cache ∧
      cache.toList = graph.map (fun node => node.conclusion) := by
  obtain ⟨cache,checked,values⟩ := InferenceCompiler.axiomGraph_checked definition
  exact ⟨InferenceCompiler.axiomGraph definition,cache,decode_authored definition,checked,values⟩

local instance : Fintype ((mappingMachine definition).Γ (mappingMachine definition).k₁) := by
  change Fintype (Option Alphabet); infer_instance
local instance : Inhabited ((mappingMachine definition).Γ (mappingMachine definition).k₀) := by
  change Inhabited (Option Alphabet); infer_instance
local instance : Inhabited ((mappingMachine definition).Γ (mappingMachine definition).k₁) := by
  change Inhabited (Option Alphabet); infer_instance

def acceptTag (tag : Option Alphabet) : Bool := tag == some 1

def taggedMapping := StackMachineComposition.Dispatch.machine (mappingMachine definition) acceptTag [some (0 : Alphabet)]

attribute [local implicit_reducible] taggedMapping
local instance : Fintype ((CertificateArgumentFraming.Execution.machine definition.rules.length).Γ
    (CertificateArgumentFraming.Execution.machine definition.rules.length).k₁) := by
  change Fintype (Option Alphabet); infer_instance
local instance : Inhabited ((CertificateArgumentFraming.Execution.machine definition.rules.length).Γ
    (CertificateArgumentFraming.Execution.machine definition.rules.length).k₁) := by
  change Inhabited (Option Alphabet); infer_instance

def listMachine := StackMachineComposition.machine
  (CertificateArgumentFraming.Execution.machine definition.rules.length) (taggedMapping definition)
  (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] listMachine

def listOutput (sources : List (Nat × RuleSchema)) : List (Option Alphabet) :=
  if sources.length = definition.rules.length then mappedWords definition sources else [some (0 : Alphabet)]

def listClock (sources : List (Nat × RuleSchema)) : Nat :=
  9*(encodeWith (Codec.list rowCodec) sources).length+mappingClock definition sources+12

noncomputable def listOutputs (sources : List (Nat × RuleSchema)) :
    TM2OutputsInTime (listMachine definition) (encodeWith (Codec.list rowCodec) sources)
      (some (listOutput definition sources)) (listClock definition sources) := by
  have framed := CertificateArgumentFraming.Execution.outputsAtArity rowCodec definition.rules.length sources
  let middle := CertificateArgumentFraming.statusWire
    (CertificateArgumentFraming.Execution.frameAtArity rowCodec definition.rules.length sources)
  have mapped : TM2OutputsInTime (taggedMapping definition) middle
      (some (listOutput definition sources)) (mappingClock definition sources+2) := by
    by_cases admitted : sources.length = definition.rules.length
    · simp only [middle,CertificateArgumentFraming.Execution.frameAtArity,if_pos admitted,
        CertificateArgumentFraming.statusWire,listOutput]
      exact WordEqualityMachine.within
        (StackMachineComposition.Dispatch.outputs_success (mappingMachine definition) acceptTag [some (0 : Alphabet)]
          (some (1 : Alphabet)) (frame (sources.map encodeRow)) (mappedWords definition sources)
          (mappingClock definition sources) (by rfl) (mappingOutputs definition sources)) (by omega)
    · simp only [middle,CertificateArgumentFraming.Execution.frameAtArity,if_neg admitted,
        CertificateArgumentFraming.statusWire,listOutput]
      exact WordEqualityMachine.within
        (StackMachineComposition.Dispatch.outputs_refused (mappingMachine definition) acceptTag [some (0 : Alphabet)]
          (some (0 : Alphabet)) [] (by rfl)) (by simp)
  have joined := StackMachineComposition.outputs
    (CertificateArgumentFraming.Execution.machine definition.rules.length) (taggedMapping definition)
    (Equiv.refl (Option Alphabet)) (encodeWith (Codec.list rowCodec) sources) middle
    (listOutput definition sources) (7*(encodeWith (Codec.list rowCodec) sources).length+8)
    (mappingClock definition sources+2) framed (by
      change TM2OutputsInTime (taggedMapping definition) (middle.map id) (some (listOutput definition sources)) (mappingClock definition sources+2)
      simpa only [List.map_id] using mapped)
  apply WordEqualityMachine.within joined
  have bound := CertificateArgumentFraming.Execution.result_length_le rowCodec definition.rules.length sources
  dsimp only [listClock,middle] at *
  omega

theorem sourceRows_length : (sourceRows definition).length = definition.rules.length := by
  simp [sourceRows]

def packet : List Alphabet := encodeWith (Codec.list rowCodec) (sourceRows definition)
def packetWords : Fin 1 → List Alphabet := fun _ => packet definition

def guardedFamily : CommonArenaDispatch.Family (listMachine definition) (Fin 1) where
  alphabet _ := (listMachine definition).Γ
  cellTypes _ _ := rfl
  Label _ := (listMachine definition).Λ
  labelFinite _ := (listMachine definition).ΛFin
  main _ := (listMachine definition).main
  body _ := (listMachine definition).m

local instance : Fintype ((listMachine definition).Γ (listMachine definition).k₀) := by
  change Fintype Alphabet; infer_instance

attribute [local implicit_reducible] guardedFamily

def guardedDispatcher : FinTM2 := CommonArenaDispatch.machine (listMachine definition) (guardedFamily definition)
  (0 : Alphabet) (some (0 : Alphabet))
attribute [local implicit_reducible] guardedDispatcher

local instance : Fintype ((FiniteWordClassifier.machine (packetWords definition)).Γ
    (FiniteWordClassifier.machine (packetWords definition)).k₁) := by
  change Fintype (Sum Alphabet (Option (Fin 1))); infer_instance
local instance : Inhabited ((FiniteWordClassifier.machine (packetWords definition)).Γ
    (FiniteWordClassifier.machine (packetWords definition)).k₁) := by
  change Inhabited (Sum Alphabet (Option (Fin 1))); infer_instance

def machine := StackMachineComposition.machine (FiniteWordClassifier.machine (packetWords definition))
  (guardedDispatcher definition) (Equiv.refl (Sum Alphabet (Option (Fin 1))))
attribute [local implicit_reducible] machine

def rawOutput (input : List Alphabet) : List (Option Alphabet) :=
  if input = packet definition then mappedWords definition (sourceRows definition) else [some (0 : Alphabet)]

def fixedClock : Nat := listClock definition (sourceRows definition)

noncomputable def guardedOutputs (input : List Alphabet) :
    TM2OutputsInTime (guardedDispatcher definition)
      (.inr (FiniteWordClassifier.classify (packetWords definition) input)::input.map Sum.inl)
      (some (rawOutput definition input)) (2*input.length+fixedClock definition+4) := by
  cases classified : FiniteWordClassifier.classify (packetWords definition) input with
  | none =>
    have wrong : input ≠ packet definition :=
      (FiniteWordClassifier.classify_none_iff (packetWords definition) input).mp classified 0
    simp only [rawOutput,if_neg wrong]
    exact WordEqualityMachine.within
      (CommonArenaDispatch.outputs_absent (listMachine definition) (guardedFamily definition)
        (0 : Alphabet) (some (0 : Alphabet)) input) (by omega)
  | some index =>
    have exactInput := FiniteWordClassifier.classify_sound (packetWords definition) input index classified
    change input = packet definition at exactInput
    subst input
    simp only [rawOutput,ite_true]
    have localRun := listOutputs definition (sourceRows definition)
    simp only [listOutput,if_pos (sourceRows_length definition)] at localRun
    have rowRun : TM2OutputsInTime ((guardedFamily definition).toMachine index)
        ((packet definition).map (CommonArenaDispatch.cellTypes (listMachine definition)
          (guardedFamily definition) index (listMachine definition).k₀).mpr)
        (some ((mappedWords definition (sourceRows definition)).map
          (CommonArenaDispatch.cellTypes (listMachine definition) (guardedFamily definition)
            index (listMachine definition).k₁).mpr)) (fixedClock definition) := by
      change TM2OutputsInTime (listMachine definition) ((packet definition).map id)
        (some ((mappedWords definition (sourceRows definition)).map id)) (fixedClock definition)
      simpa only [List.map_id,packet,fixedClock] using localRun
    exact CommonArenaDispatch.outputs_selected (listMachine definition) (guardedFamily definition)
      (0 : Alphabet) (some (0 : Alphabet)) index (packet definition)
      (mappedWords definition (sourceRows definition)) (fixedClock definition) rowRun

/-- The whole original source packet is checked before the ordered mapper runs. -/
noncomputable def rawOutputs (input : List Alphabet) :
    TM2OutputsInTime (machine definition) input (some (rawOutput definition input))
      (6*input.length+fixedClock definition+10) := by
  have classified := FiniteWordClassifier.outputs (packetWords definition) input
  have emitted := guardedOutputs definition input
  have joined := StackMachineComposition.outputs (FiniteWordClassifier.machine (packetWords definition))
    (guardedDispatcher definition) (Equiv.refl (Sum Alphabet (Option (Fin 1)))) input
    (.inr (FiniteWordClassifier.classify (packetWords definition) input)::input.map Sum.inl)
    (rawOutput definition input) (2*input.length+2) (2*input.length+fixedClock definition+4)
    classified (by
      change TM2OutputsInTime (guardedDispatcher definition)
        ((.inr (FiniteWordClassifier.classify (packetWords definition) input)::input.map Sum.inl).map id)
        (some (rawOutput definition input)) (2*input.length+fixedClock definition+4)
      simpa only [List.map_id] using emitted)
  convert joined using 1
  all_goals first | rfl | (simp only [List.length_cons,List.length_map]; ring)

theorem output_authored : rawOutput definition (packet definition) =
    mappedWords definition (sourceRows definition) := by simp [rawOutput]

theorem output_refused (input : List Alphabet) (wrong : input ≠ packet definition) :
    rawOutput definition input = [some (0 : Alphabet)] := by simp only [rawOutput,if_neg wrong]

theorem raw_decodes : decodePrefix (rawOutput definition (packet definition)) =
    some (InferenceCompiler.axiomGraph definition) := by rw [output_authored,decode_authored]

noncomputable def realization : TM2ComputableInPolyTime id id (rawOutput definition) where
  tm := machine definition
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 6*X+C (fixedClock definition+10)
  outputsFun input := by
    change TM2OutputsInTime (machine definition) (input.map id)
      (some ((rawOutput definition input).map id)) _
    simpa only [List.map_id,id_eq,eval_add,eval_mul,eval_C,eval_X,Nat.add_assoc] using rawOutputs definition input

/-- The clock's fixed part charges complete original packets and generated fields. -/
theorem fixedClock_eq : fixedClock definition =
    9*(packet definition).length+
      ((sourceRows definition).map (fun source => rowClock definition source+
        2*(encodeRow source).length+2*(emitRow definition source).length+4)).sum+14 := by
  simp only [fixedClock,listClock,mappingClock,FramedWordMapping.totalClock_eq,packet]
  omega

/-- Literal program payload retained by this fixed-calculus specialization. -/
def fixedDescriptorBytes : Nat := (packet definition).length+fixedPayloadBytes definition

theorem decode_refusal : decodePrefix [some (0 : Alphabet)] = none := rfl

/-- Successful full readout reflects the complete original authored packet. -/
theorem decoded_exact (input : List Alphabet) (graph : List ProofExecution.Receipt) :
    decodePrefix (rawOutput definition input) = some graph ↔
      input = packet definition ∧ graph = InferenceCompiler.axiomGraph definition := by
  by_cases accepted : input = packet definition
  · subst input
    rw [raw_decodes]
    simp only [Option.some.injEq,true_and,eq_comm]
  · rw [output_refused definition input accepted,decode_refusal]
    simp [accepted]

theorem decoded_source_rows (sources : List (Nat × RuleSchema)) (graph : List ProofExecution.Receipt) :
    decodePrefix (rawOutput definition (encodeWith (Codec.list rowCodec) sources)) = some graph ↔
      sources = sourceRows definition ∧ graph = InferenceCompiler.axiomGraph definition := by
  rw [decoded_exact]
  exact and_congr (encodeWith_injective (Codec.list rowCodec)).eq_iff Iff.rfl

/-- Any successful emitted prefix has the original chronological axiom authority. -/
theorem decoded_checked {input : List Alphabet} {graph : List ProofExecution.Receipt}
    (decoded : decodePrefix (rawOutput definition input) = some graph) :
    ∃ cache, Mettapedia.Logic.DerivationGraph.replay (ruleWitness
      (InferenceHosting.policy (FirstOrder.InferenceTranslation.inferenceRules definition))) graph = some cache ∧
      cache.toList = graph.map (fun node => node.conclusion) := by
  have same := ((decoded_exact definition input graph).mp decoded).2
  subst graph
  exact InferenceCompiler.axiomGraph_checked definition

theorem source_rows_refused (sources : List (Nat × RuleSchema)) (wrong : sources ≠ sourceRows definition) :
    rawOutput definition (encodeWith (Codec.list rowCodec) sources) = [some (0 : Alphabet)] := by
  apply output_refused
  intro same
  apply wrong
  exact (encodeWith_injective (Codec.list rowCodec)) same

theorem trailing_refused : rawOutput definition (packet definition++[0]) = [some (0 : Alphabet)] := by
  apply output_refused
  intro same
  have sizes := congrArg List.length same
  simp only [List.length_append,List.length_singleton] at sizes
  omega

end Mettapedia.Languages.HOLLight.SchemaAxiomEmission.Prefix
