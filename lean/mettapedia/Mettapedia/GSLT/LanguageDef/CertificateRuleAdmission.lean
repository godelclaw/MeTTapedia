import Mettapedia.Computability.CommonArenaDispatch
import Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming
import Mettapedia.Computability.RetainedWordExecution
import Mettapedia.Computability.FramedWordValidation
import Mettapedia.GSLT.LanguageDef.PatternScopeExecution

/-!
# Executed lookup of authored certificate rules

The original instance codec supplies the rule name and complete arguments.
An actual prefix selector and finite dictionary classifier choose the first
matching authored row. A retained-input caller restores the complete original
instance bytes. One finite row dispatcher runs each selected row's existing
argument framer at its authored arity, with explicit refusal for absent rows or
incorrect argument counts. A separate scope-vector operation executes the
original zero-depth argument judgment on every complete Pattern image and
retains the bytes. Side conditions and child judgments remain obligations of
the original source checker; deeper formals retain their declared depths.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax InferenceChecker InferenceExtension
open Mettapedia.Computability Turing Polynomial

def row (definition : CalculusLanguageDef) (index : Fin definition.rules.length) : RuleSchema :=
  definition.rules.get index

def names (definition : CalculusLanguageDef) (index : Fin definition.rules.length) : String :=
  (row definition index).id.value

def selected (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    Option (Fin definition.rules.length) :=
  Dictionary.result Codec.string (names definition) ruleInstance.ruleId.value

theorem selected_lookup (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (selected definition ruleInstance).map (row definition) = definition.lookupRule? ruleInstance.ruleId := by
  have enumeration : (List.finRange definition.rules.length).map (row definition) = definition.rules :=
    List.map_get_finRange definition.rules
  rw [CalculusLanguageDef.lookupRule?]
  conv_rhs => rw [← enumeration, List.find?_map]
  unfold selected Dictionary.result
  apply congrArg (fun predicate => ((List.finRange definition.rules.length).find? predicate).map (row definition))
  funext index
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def, decide_eq_true_eq, names]
  constructor
  · intro same
    exact congrArg RuleId.mk same.symm
  · intro same
    exact (congrArg RuleId.value same).symm


def dictionary (definition : CalculusLanguageDef) : FinTM2 :=
  FiniteWordClassifier.machine (Dictionary.words Codec.string (names definition))

attribute [local implicit_reducible] dictionary FiniteWordClassifier.machine
  CertificateDataTraversal.ProductField.machine StackMachineComposition.Dispatch.machine
  StackMachineComposition.machine FinTM2.Cfg FinTM2.Stmt

def statusAccepted (symbol : Alphabet) : Bool := symbol == 1

def classifier (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.Dispatch.machine (dictionary definition) statusAccepted [.inr none]

local instance (takeSecond : Bool) : Fintype ((CertificateDataTraversal.ProductField.machine takeSecond).Γ
    (CertificateDataTraversal.ProductField.machine takeSecond).k₁) := by
  change Fintype Alphabet
  infer_instance

local instance (takeSecond : Bool) : Inhabited ((CertificateDataTraversal.ProductField.machine takeSecond).Γ
    (CertificateDataTraversal.ProductField.machine takeSecond).k₁) := by
  change Inhabited Alphabet
  infer_instance

def nameMachine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (CertificateDataTraversal.ProductField.machine false)
    (classifier definition) (Equiv.refl Alphabet)

attribute [local implicit_reducible] classifier nameMachine

def nameOutput (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    List (Sum Alphabet (Option (Fin definition.rules.length))) :=
  .inr (selected definition ruleInstance) :: (encodeWith Codec.string ruleInstance.ruleId.value).map Sum.inl

theorem name_length_le (ruleInstance : RuleInstance) :
    (encodeWith Codec.string ruleInstance.ruleId.value).length ≤
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length := by
  exact CertificateDataTraversal.ProductField.selected_length_le false
    (Codec.string.put ruleInstance.ruleId.value) ((Codec.list CertificateDataEncoding.patternCodec).put ruleInstance.arguments)

/-- Every original instance physically selects its name, consumes the success
status, and runs the original complete-word classifier. Unknown names return
its explicit absent-row tag. -/
noncomputable def nameOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (nameMachine definition) (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (nameOutput definition ruleInstance))
      (8 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 10) := by
  have selectedName := (CertificateDataTraversal.ProductField.selectFirstCodec Codec.string
    (Codec.list CertificateDataEncoding.patternCodec)).outputsFun (ruleInstance.ruleId.value, ruleInstance.arguments)
  change TM2OutputsInTime (CertificateDataTraversal.ProductField.machine false)
    ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map id)
    (some (((1 : Alphabet) :: encodeWith Codec.string ruleInstance.ruleId.value).map id)) _ at selectedName
  have timeEq : (CertificateDataTraversal.ProductField.selectFirstCodec Codec.string
      (Codec.list CertificateDataEncoding.patternCodec)).time = C 4 * X + C 3 := rfl
  rw [timeEq] at selectedName
  simp only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at selectedName
  have classified := Dictionary.outputs Codec.string (names definition) ruleInstance.ruleId.value
  have dispatched := StackMachineComposition.Dispatch.outputs_success (dictionary definition)
    statusAccepted [.inr none] (1 : Alphabet)
    (encodeWith Codec.string ruleInstance.ruleId.value)
    (nameOutput definition ruleInstance)
    (2 * (encodeWith Codec.string ruleInstance.ruleId.value).length + 2)
    (by rfl) classified
  have joined := StackMachineComposition.outputs (CertificateDataTraversal.ProductField.machine false)
    (classifier definition) (Equiv.refl Alphabet)
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
    ((1 : Alphabet) :: encodeWith Codec.string ruleInstance.ruleId.value)
    (nameOutput definition ruleInstance)
    (4 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 3)
    (2 * (encodeWith Codec.string ruleInstance.ruleId.value).length + 2 + 1)
    selectedName (by
      change TM2OutputsInTime (classifier definition)
        (((1 : Alphabet) :: encodeWith Codec.string ruleInstance.ruleId.value).map id) _ _
      simpa only [classifier, List.map_id_fun, id_eq] using dispatched)
  apply WordEqualityMachine.within joined
  have bounded := name_length_le ruleInstance
  simp only [List.length_cons]
  omega

instance (definition : CalculusLanguageDef) : Fintype ((nameMachine definition).Γ (nameMachine definition).k₁) := by
  change Fintype (Sum Alphabet (Option (Fin definition.rules.length)))
  infer_instance

instance (definition : CalculusLanguageDef) : Inhabited ((nameMachine definition).Γ (nameMachine definition).k₀) := by
  change Inhabited Alphabet
  infer_instance

def readRow (definition : CalculusLanguageDef) (symbol : (nameMachine definition).Γ (nameMachine definition).k₁) :
    Option (Fin definition.rules.length) := match symbol with
  | .inr index => index
  | .inl _ => none

def machine (definition : CalculusLanguageDef) : FinTM2 :=
  RetainedWordExecution.machine (nameMachine definition) (readRow definition)

attribute [local implicit_reducible] machine RetainedWordExecution.machine

def output (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    List (Sum Alphabet (Option (Fin definition.rules.length))) :=
  .inr (selected definition ruleInstance) :: (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map Sum.inl

/-- Lookup retains the complete original input, including unused arguments.
The whole bound includes selecting, scanning, copying and restoring bytes. -/
noncomputable def outputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (machine definition) (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (output definition ruleInstance))
      (12 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 15) := by
  have executed := RetainedWordExecution.outputs (nameMachine definition) (readRow definition)
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance) (.inr (selected definition ruleInstance))
    ((encodeWith Codec.string ruleInstance.ruleId.value).map Sum.inl)
    (8 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 10)
    (nameOutputs definition ruleInstance)
  apply WordEqualityMachine.within executed
  have bounded := name_length_le ruleInstance
  simp only [List.length_map]
  omega

noncomputable def realization (definition : CalculusLanguageDef) :
    TM2ComputableInPolyTime (encodeWith CertificateDataEncoding.instanceCodec)
      (output definition) (fun ruleInstance : RuleInstance => ruleInstance) where
  tm := machine definition
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl _
  time := C 12 * X + C 15
  outputsFun ruleInstance := by
    change TM2OutputsInTime (machine definition)
      ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map id)
      (some ((output definition ruleInstance).map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputs definition ruleInstance

/-- An authored row determines the existing list framer's finite arity.
Scope, metadata and side conditions remain separate source obligations. -/
def authoredArity (rule : RuleSchema) : Nat := rule.metavariables.length

attribute [local implicit_reducible] CertificateArgumentFraming.Execution.machine

def argumentMachine (arity : Nat) : FinTM2 :=
  StackMachineComposition.machine (CertificateDataTraversal.ProductField.machine true)
    (StackMachineComposition.Dispatch.machine
      (CertificateArgumentFraming.Execution.machine arity) statusAccepted [some 0])
    (Equiv.refl Alphabet)

def argumentOutput (arity : Nat) (ruleInstance : RuleInstance) : List (Option Alphabet) :=
  CertificateArgumentFraming.statusWire
    (CertificateArgumentFraming.Execution.frameAtArity CertificateDataEncoding.patternCodec
      arity ruleInstance.arguments)

attribute [local implicit_reducible] argumentMachine

theorem arguments_length_le (ruleInstance : RuleInstance) :
    (encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments).length ≤
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length :=
  CertificateDataTraversal.ProductField.selected_length_le true
    (Codec.string.put ruleInstance.ruleId.value) ((Codec.list CertificateDataEncoding.patternCodec).put ruleInstance.arguments)

/-- Execute the original product selector on a complete original rule instance.
Both fields are parsed; the argument field retains its exact ordered bytes. -/
noncomputable def argumentFieldOutputs (ruleInstance : RuleInstance) :
    TM2OutputsInTime (CertificateDataTraversal.ProductField.machine true)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some ((1 : Alphabet) :: encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments))
      (4 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 3) := by
  have selectedArguments := (CertificateDataTraversal.ProductField.selectSecondCodec Codec.string
    (Codec.list CertificateDataEncoding.patternCodec)).outputsFun (ruleInstance.ruleId.value, ruleInstance.arguments)
  change TM2OutputsInTime (CertificateDataTraversal.ProductField.machine true)
    ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map id)
    (some (((1 : Alphabet) :: encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments).map id)) _ at selectedArguments
  have timeEq : (CertificateDataTraversal.ProductField.selectSecondCodec Codec.string
      (Codec.list CertificateDataEncoding.patternCodec)).time = C 4 * X + C 3 := rfl
  rw [timeEq] at selectedArguments
  simp only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at selectedArguments
  exact selectedArguments

/-- Both original instance fields are physically parsed; the complete ordered
argument list then runs the original arity machine, including refusal paths. -/
noncomputable def argumentOutputs (arity : Nat) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (argumentMachine arity) (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (argumentOutput arity ruleInstance))
      (13 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 16) := by
  have selectedArguments := argumentFieldOutputs ruleInstance
  have framed := CertificateArgumentFraming.Execution.outputsAtArity
    CertificateDataEncoding.patternCodec arity ruleInstance.arguments
  have dispatched := StackMachineComposition.Dispatch.outputs_success
    (CertificateArgumentFraming.Execution.machine arity) statusAccepted [some 0] (1 : Alphabet)
    (encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments)
    (argumentOutput arity ruleInstance)
    (7 * (encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments).length + 8)
    (by rfl) framed
  have joined := StackMachineComposition.outputs (CertificateDataTraversal.ProductField.machine true)
    (StackMachineComposition.Dispatch.machine
      (CertificateArgumentFraming.Execution.machine arity) statusAccepted [some 0])
    (Equiv.refl Alphabet)
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
    ((1 : Alphabet) :: encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments)
    (argumentOutput arity ruleInstance)
    (4 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 3)
    (7 * (encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments).length + 8 + 1)
    selectedArguments (by
      change TM2OutputsInTime (StackMachineComposition.Dispatch.machine
          (CertificateArgumentFraming.Execution.machine arity) statusAccepted [some 0])
        (((1 : Alphabet) :: encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments).map id) _ _
      simpa only [List.map_id_fun, id_eq] using dispatched)
  apply WordEqualityMachine.within joined
  have bounded := arguments_length_le ruleInstance
  simp only [List.length_cons]
  omega

theorem lookup_selected (definition : CalculusLanguageDef) (ruleInstance : RuleInstance)
    (index : Fin definition.rules.length) (found : selected definition ruleInstance = some index) :
    definition.lookupRule? ruleInstance.ruleId = some (row definition index) := by
  rw [← selected_lookup, found]
  rfl

theorem argument_success_iff (arity : Nat) (ruleInstance : RuleInstance) :
    argumentOutput arity ruleInstance = CertificateArgumentFraming.statusWire
      (some (CertificateArgumentFraming.framedArguments CertificateDataEncoding.patternCodec ruleInstance.arguments)) ↔
      ruleInstance.arguments.length = arity := by
  unfold argumentOutput
  rw [CertificateArgumentFraming.statusWire_injective.eq_iff]
  unfold CertificateArgumentFraming.Execution.frameAtArity
  by_cases admitted : ruleInstance.arguments.length = arity <;> simp [admitted]

/-- A successful original rule application supplies the exact selected row
and its arity; the executed framing stage admits that complete argument list. -/
theorem application_selected_arity {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (accepted : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    ∃ index : Fin definition.1.rules.length,
      selected definition.1 ruleInstance = some index ∧
      argumentOutput (authoredArity (row definition.1 index)) ruleInstance =
        CertificateArgumentFraming.statusWire
          (some (CertificateArgumentFraming.framedArguments CertificateDataEncoding.patternCodec ruleInstance.arguments)) := by
  obtain ⟨rule, lookup, arguments, sides, premiseSchemas, conclusionSchema⟩ :=
    instantiateRule?_eq_some_iff_application.mp accepted
  have same := selected_lookup definition.1 ruleInstance
  cases found : selected definition.1 ruleInstance with
  | none => simp only [found, Option.map_none, lookup] at same; cases same
  | some index =>
      have rowEq : row definition.1 index = rule := by
        simpa only [found, Option.map_some, lookup, Option.some.injEq] using same
      refine ⟨index, rfl, (argument_success_iff _ _).mpr ?_⟩
      rw [authoredArity, rowEq]
      exact (argumentsValidAt_length arguments).symm


namespace UniformArity
open Mettapedia.Computability.StackMachineRegisters Turing.TM2.Stmt

variable (definition : CalculusLanguageDef)
abbrev Row := Fin definition.rules.length
abbrev Base := argumentMachine 0
local instance : DecidableEq Base.K := Base.kDecidableEq

/-- Each authored row shares the existing physical alphabet family, even
though its finite framing control contains that row's own arity. -/
theorem cellTypes (index : Row definition) (key : Base.K) :
    (argumentMachine (authoredArity (row definition index))).Γ key = Base.Γ key := by
  cases key with
  | none => rfl
  | some key => cases key with
    | inl key => cases key with
      | none => rfl
      | some key => cases key <;> rfl
    | inr key => cases key with
      | none => rfl
      | some key => cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key <;> rfl

/-- The arity-specific controls are a finite family over the existing arena. -/
def family : CommonArenaDispatch.Family Base (Row definition) where
  alphabet index := (argumentMachine (authoredArity (row definition index))).Γ
  cellTypes := cellTypes definition
  Label index := (argumentMachine (authoredArity (row definition index))).Λ
  labelFinite index := (argumentMachine (authoredArity (row definition index))).ΛFin
  main index := (argumentMachine (authoredArity (row definition index))).main
  body index := (argumentMachine (authoredArity (row definition index))).m

abbrev InputCell := Sum Alphabet (Option (Row definition))
abbrev Key := CommonArenaDispatch.Key Base
abbrev Cells := CommonArenaDispatch.Cells Base (family definition)
abbrev Extra := CommonArenaDispatch.Extra Base (family definition)
abbrev State := CommonArenaDispatch.State Base (family definition)
abbrev Phase := CommonArenaDispatch.Phase Base (family definition)
abbrev inputKey : Key := CommonArenaDispatch.inputKey Base
abbrev transferKey : Key := CommonArenaDispatch.transferKey Base
abbrev baseKey (key : Base.K) : Key := CommonArenaDispatch.baseKey Base key

def body := CommonArenaDispatch.body Base (family definition)
def readByte := CommonArenaDispatch.readByte Base (family definition)
def program := CommonArenaDispatch.program Base (family definition) (0 : Alphabet) (some (0 : Alphabet))
def machine := CommonArenaDispatch.machine Base (family definition) (0 : Alphabet) (some (0 : Alphabet))
attribute [local implicit_reducible] machine program

theorem machine_body (phase : Phase definition) :
    (machine definition).m phase = program definition phase := rfl

def config := CommonArenaDispatch.config Base (family definition) (0 : Alphabet) (some (0 : Alphabet))
def originalContents := CommonArenaDispatch.originalContents Base (family definition)
def embeddedContents := CommonArenaDispatch.embeddedContents Base (family definition) (0 : Alphabet) (some (0 : Alphabet))
def runConfig := CommonArenaDispatch.runConfig Base (family definition) (0 : Alphabet) (some (0 : Alphabet))

theorem run_step (index : Row definition) (input : List (InputCell definition)) (transfer : List Alphabet)
    (before after : (argumentMachine (authoredArity (row definition index))).Cfg)
    (computed : (argumentMachine (authoredArity (row definition index))).step before = some after) :
    (machine definition).step (runConfig definition index input transfer before) =
      some (runConfig definition index input transfer after) := by
  exact CommonArenaDispatch.run_step Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) index input transfer before after computed
theorem read_selected (index : Row definition) (state : State definition)
    (input : List (InputCell definition)) (contents : ∀ key, List (Base.Γ key)) :
    (machine definition).step (config definition (some .read) state (.inr (some index) :: input) [] contents) =
      some (config definition (some (.copy index)) (state.1, some (.inr (some index)), state.2.2)
        input [] contents) := by
  exact CommonArenaDispatch.read_selected Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) index state input contents
theorem copy_cons (index : Row definition) (state : State definition) (head : Alphabet)
    (tail : List Alphabet) (transfer : List Alphabet) (contents : ∀ key, List (Base.Γ key)) :
    (machine definition).step (config definition (some (.copy index)) state
      ((head :: tail).map Sum.inl) transfer contents) =
      some (config definition (some (.copy index)) (state.1, some (.inl head), some head)
        (tail.map Sum.inl) (head :: transfer) contents) := by
  exact CommonArenaDispatch.copy_cons Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) index state head tail transfer contents
theorem copy_nil (index : Row definition) (state : State definition) (transfer : List Alphabet)
    (contents : ∀ key, List (Base.Γ key)) :
    (machine definition).step (config definition (some (.copy index)) state [] transfer contents) =
      some (config definition (some (.restore index)) (state.1, none, none) [] transfer contents) := by
  exact CommonArenaDispatch.copy_nil Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) index state transfer contents
theorem restore_cons (index : Row definition) (state : State definition) (head : Alphabet)
    (tail : List Alphabet) (contents : ∀ key, List (Base.Γ key)) :
    (machine definition).step (config definition (some (.restore index)) state [] (head :: tail) contents) =
      some (config definition (some (.restore index)) (state.1, state.2.1, some head) [] tail
        (Function.update contents Base.k₀ (head :: contents Base.k₀))) := by
  exact CommonArenaDispatch.restore_cons Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) index state head tail contents
theorem restore_nil (index : Row definition) (state : State definition)
    (contents : ∀ key, List (Base.Γ key)) :
    (machine definition).step (config definition (some (.restore index)) state [] [] contents) =
      some (config definition (some (.run index (argumentMachine (authoredArity (row definition index))).main))
        (Base.initialState, none, none) [] [] contents) := by
  exact CommonArenaDispatch.restore_nil Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) index state contents
theorem finish_step (state : State definition) (contents : ∀ key, List (Base.Γ key)) :
    (machine definition).step (config definition (some .finish) state [] [] contents) =
      some (config definition none (Base.initialState, none, none) [] [] contents) := by
  exact CommonArenaDispatch.finish_step Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) state contents
theorem init_eq (input : List (InputCell definition)) :
    initList (machine definition) input =
      config definition (some .read) (Base.initialState, none, none) input [] (fun _ => []) := by
  exact CommonArenaDispatch.init_eq Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) input
theorem halt_eq (word : List (Option Alphabet)) :
    haltList (machine definition) word =
      config definition none (Base.initialState, none, none) [] []
        (RetainedWordExecution.wordContents Base Base.k₁ word) := by
  exact CommonArenaDispatch.halt_eq Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) word
theorem read_absent (state : State definition) (input : List (InputCell definition)) :
    (machine definition).step (config definition (some .read) state (.inr none :: input) [] (fun _ => [])) =
      some (config definition (some .rejectInput) (state.1, some (.inr none), state.2.2)
        input [] (fun _ => [])) := by
  exact CommonArenaDispatch.read_absent Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) state input
theorem reject_cons (state : State definition) (head : InputCell definition)
    (tail : List (InputCell definition)) :
    (machine definition).step (config definition (some .rejectInput) state (head :: tail) [] (fun _ => [])) =
      some (config definition (some .rejectInput) (state.1, some head, state.2.2) tail [] (fun _ => [])) := by
  exact CommonArenaDispatch.reject_cons Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) state head tail
theorem reject_nil (state : State definition) :
    (machine definition).step (config definition (some .rejectInput) state [] [] (fun _ => [])) =
      some (config definition (some .rejectTransfer) (state.1, none, state.2.2) [] [] (fun _ => [])) := by
  exact CommonArenaDispatch.reject_nil Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) state
theorem refuse_step (state : State definition) :
    (machine definition).step (config definition (some .rejectTransfer) state [] [] (fun _ => [])) =
      some (config definition none (Base.initialState, none, none) [] []
        (RetainedWordExecution.wordContents Base Base.k₁ [some 0])) := by
  exact CommonArenaDispatch.refuse_step Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) state
noncomputable def copyRun := CommonArenaDispatch.copyRun Base (family definition) (0 : Alphabet) (some (0 : Alphabet))
noncomputable def restoreRun := CommonArenaDispatch.restoreRun Base (family definition) (0 : Alphabet) (some (0 : Alphabet))
noncomputable def runExecution := CommonArenaDispatch.runExecution Base (family definition) (0 : Alphabet) (some (0 : Alphabet))
noncomputable def rejectRun := CommonArenaDispatch.rejectRun Base (family definition) (0 : Alphabet) (some (0 : Alphabet))

def result (choice : Option (Row definition)) (ruleInstance : RuleInstance) : List (Option Alphabet) :=
  match choice with
  | none => [some 0]
  | some index => argumentOutput (authoredArity (row definition index)) ruleInstance

/-- One finite authored-row machine handles every rule instance. The chosen
row executes its existing framing subroutine; absent rows and wrong lengths
produce explicit refusal and clear all caller and subroutine scratch. -/
noncomputable def outputs (choice : Option (Row definition)) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (machine definition)
      (.inr choice :: (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map Sum.inl)
      (some (result definition choice ruleInstance))
      (15 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 20) := by
  let word := encodeWith CertificateDataEncoding.instanceCodec ruleInstance
  cases choice with
  | none =>
    have refused := CommonArenaDispatch.outputs_absent Base (family definition) (0 : Alphabet) (some (0 : Alphabet)) word
    apply WordEqualityMachine.within refused
    dsimp only [word]
    omega
  | some index =>
    have source := argumentOutputs (authoredArity (row definition index)) ruleInstance
    have selected : TM2OutputsInTime ((family definition).toMachine index)
        (word.map (CommonArenaDispatch.cellTypes Base (family definition) index Base.k₀).mpr)
        (some ((argumentOutput (authoredArity (row definition index)) ruleInstance).map
          (CommonArenaDispatch.cellTypes Base (family definition) index Base.k₁).mpr))
        (13 * word.length + 16) := by
      change TM2OutputsInTime (argumentMachine (authoredArity (row definition index)))
        (word.map id) (some ((argumentOutput (authoredArity (row definition index)) ruleInstance).map id)) _
      simpa only [List.map_id_fun, id_eq] using source
    have executed := CommonArenaDispatch.outputs_selected Base (family definition) (0 : Alphabet) (some (0 : Alphabet))
      index word (argumentOutput (authoredArity (row definition index)) ruleInstance)
      (13 * word.length + 16) selected
    apply WordEqualityMachine.within executed
    dsimp only [word]
    omega

end UniformArity

instance (definition : CalculusLanguageDef) : Fintype ((machine definition).Γ (machine definition).k₁) := by
  change Fintype (UniformArity.InputCell definition)
  infer_instance

instance (definition : CalculusLanguageDef) : Inhabited ((machine definition).Γ (machine definition).k₁) := by
  change Inhabited (UniformArity.InputCell definition)
  infer_instance

/-- The complete lookup and authored-arity dispatch use one fixed finite
control graph for the original authored rule table. -/
def admissionMachine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (machine definition) (UniformArity.machine definition)
    (Equiv.refl (UniformArity.InputCell definition))

attribute [local implicit_reducible] admissionMachine

def admissionOutput (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : List (Option Alphabet) :=
  UniformArity.result definition (selected definition ruleInstance) ruleInstance

/-- Original instance bytes are retained across rule lookup and then
physically copied into the selected row's existing argument framer. Unknown
names and incorrect authored arity have distinct refusal from successful
framing; all scratch and finite registers are reset at halt. -/
noncomputable def admissionOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (admissionMachine definition)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (admissionOutput definition ruleInstance))
      (29 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 39) := by
  have joined := StackMachineComposition.outputs (machine definition) (UniformArity.machine definition)
    (Equiv.refl (UniformArity.InputCell definition))
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance) (output definition ruleInstance)
    (admissionOutput definition ruleInstance)
    (12 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 15)
    (15 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 20)
    (outputs definition ruleInstance) (by
      change TM2OutputsInTime (UniformArity.machine definition) ((output definition ruleInstance).map id) _ _
      simpa only [List.map_id_fun, id_eq, output, admissionOutput] using
        UniformArity.outputs definition (selected definition ruleInstance) ruleInstance)
  convert joined using 1
  all_goals first
    | rfl
    | (simp only [output, List.length_cons, List.length_map]; omega)

noncomputable def admissionRealization (definition : CalculusLanguageDef) :
    TM2ComputableInPolyTime (encodeWith CertificateDataEncoding.instanceCodec)
      (admissionOutput definition) (fun ruleInstance : RuleInstance => ruleInstance) where
  tm := admissionMachine definition
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl _
  time := C 29 * X + C 39
  outputsFun ruleInstance := by
    change TM2OutputsInTime (admissionMachine definition)
      ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map id)
      (some ((admissionOutput definition ruleInstance).map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using admissionOutputs definition ruleInstance

/-- Successful framing is exactly authored name lookup and authored argument
arity. It does not discharge scope, side conditions or premise semantics. -/
theorem admission_success_iff (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    admissionOutput definition ruleInstance = CertificateArgumentFraming.statusWire
      (some (CertificateArgumentFraming.framedArguments CertificateDataEncoding.patternCodec ruleInstance.arguments)) ↔
    ∃ rule, definition.lookupRule? ruleInstance.ruleId = some rule ∧
      ruleInstance.arguments.length = authoredArity rule := by
  cases found : selected definition ruleInstance with
  | none =>
    have missing : definition.lookupRule? ruleInstance.ruleId = none := by
      rw [← selected_lookup, found]; rfl
    simp [admissionOutput, found, UniformArity.result, CertificateArgumentFraming.statusWire, missing]
  | some index =>
    have lookup := lookup_selected definition ruleInstance index found
    simpa [admissionOutput, found, UniformArity.result, lookup] using argument_success_iff (authoredArity (row definition index)) ruleInstance

/-- An accepted original application always reaches successful framing in the
complete lookup-and-dispatch machine. The original checker remains the semantic
authority for the remaining rule obligations. -/
theorem application_admission {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (accepted : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    admissionOutput definition.1 ruleInstance = CertificateArgumentFraming.statusWire
      (some (CertificateArgumentFraming.framedArguments CertificateDataEncoding.patternCodec ruleInstance.arguments)) := by
  obtain ⟨index, selectedRow, framed⟩ := application_selected_arity accepted
  simpa only [admissionOutput, selectedRow, UniformArity.result] using framed


namespace ArgumentScope

local instance : Fintype (PatternScopeExecution.OriginalAdmission.machine.Γ
    PatternScopeExecution.OriginalAdmission.machine.k₁) := by
  change Fintype (Option Bool)
  infer_instance

local instance : Inhabited (PatternScopeExecution.OriginalAdmission.machine.Γ
    PatternScopeExecution.OriginalAdmission.machine.k₀) := by
  change Inhabited Alphabet
  infer_instance

/-- Scope checks use the original argument judgment on every original Pattern
image. The complete framed argument vector is retained for subsequent rendering. -/
def machine : FinTM2 := FramedWordValidation.retainedMachine
  PatternScopeExecution.OriginalAdmission.machine FramedWordValidation.readBoolean

def vector (arguments : List Pattern) : List (Option Alphabet) :=
  CertificateArgumentFraming.framedArguments CertificateDataEncoding.patternCodec arguments

def output (arguments : List Pattern) : List (Option Alphabet ⊕ Bool) :=
  .inr (arguments.all (argumentValidAt 0)) :: (vector arguments).map Sum.inl

def clock (pattern : Pattern) : Nat :=
  20000 * ((encodeWith CertificateDataEncoding.patternCodec pattern).length + 1)^2

theorem responses_eq (arguments : List Pattern) :
    FramedWordValidation.responses PatternScopeExecution.OriginalAdmission.machine
      FramedWordValidation.readBoolean (fun pattern => some (argumentValidAt 0 pattern)) arguments =
      arguments.all (argumentValidAt 0) := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
    simp only [FramedWordValidation.responses, FramedWordValidation.readBoolean,
      Option.getD_some, List.all_cons, ih]

noncomputable def outputsExact (arguments : List Pattern) :
    TM2OutputsInTime machine (vector arguments) (some (output arguments))
      (FramedWordValidation.totalClock PatternScopeExecution.OriginalAdmission.machine
        (encodeWith CertificateDataEncoding.patternCodec) clock arguments +
        3 * (vector arguments).length + 5) := by
  have runs := FramedWordValidation.retainedOutputs PatternScopeExecution.OriginalAdmission.machine
    FramedWordValidation.readBoolean (encodeWith CertificateDataEncoding.patternCodec)
    (fun pattern => some (argumentValidAt 0 pattern)) clock
    PatternScopeExecution.OriginalAdmission.outputs arguments
  simpa only [machine, vector, output, responses_eq, FramedWordValidation.frameWords,
    CertificateArgumentFraming.framedArguments, CertificateArgumentFraming.argumentWords] using runs

theorem vector_cons_length (argument : Pattern) (rest : List Pattern) :
    (vector (argument :: rest)).length =
      (encodeWith CertificateDataEncoding.patternCodec argument).length + 1 + (vector rest).length := by
  simp only [vector, CertificateArgumentFraming.framedArguments_cons,
    List.length_append, List.length_map, List.length_cons]
  omega

theorem fields_clock_le (arguments : List Pattern) :
    (arguments.map (fun pattern => clock pattern +
      2 * (encodeWith CertificateDataEncoding.patternCodec pattern).length + 4)).sum ≤
      20004 * (vector arguments).length^2 := by
  induction arguments with
  | nil => simp [vector, CertificateArgumentFraming.framedArguments,
      CertificateArgumentFraming.argumentWords, WordTemplateMachine.Indexed.frame]
  | cons argument rest ih =>
    let size := (encodeWith CertificateDataEncoding.patternCodec argument).length
    have field : clock argument + 2 * size + 4 ≤ 20004 * (size + 1)^2 := by
      dsimp [clock, size]
      nlinarith
    have squares : (size + 1)^2 + (vector rest).length^2 ≤
        (size + 1 + (vector rest).length)^2 := by
      nlinarith [Nat.zero_le ((size + 1) * (vector rest).length)]
    calc
      _ = (clock argument + 2 * size + 4) +
        (rest.map (fun pattern => clock pattern +
          2 * (encodeWith CertificateDataEncoding.patternCodec pattern).length + 4)).sum := rfl
      _ ≤ 20004 * (size + 1)^2 + 20004 * (vector rest).length^2 :=
        Nat.add_le_add field ih
      _ = 20004 * ((size + 1)^2 + (vector rest).length^2) := by ring
      _ ≤ 20004 * (size + 1 + (vector rest).length)^2 := Nat.mul_le_mul_left _ squares
      _ = _ := by rw [vector_cons_length]

/-- The clock charges all original codec symbols, delimiters, scope executions
and the physical restoration of the complete vector. False scope results do
not skip later fields. -/
noncomputable def outputs (arguments : List Pattern) :
    TM2OutputsInTime machine (vector arguments) (some (output arguments))
      (20020 * ((vector arguments).length + 1)^2) := by
  have exactRun := outputsExact arguments
  refine ⟨exactRun.toEvalsTo, exactRun.steps_le_m.trans ?_⟩
  have fields := fields_clock_le arguments
  change (arguments.map (fun pattern => clock pattern +
    2 * (encodeWith CertificateDataEncoding.patternCodec pattern).length + 4)).sum + 2 +
    3 * (vector arguments).length + 5 ≤ _
  nlinarith

noncomputable def realization :
    TM2ComputableInPolyTime vector output (fun arguments : List Pattern => arguments) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 20020 * (X + C 1)^2
  outputsFun arguments := by
    change TM2OutputsInTime machine ((vector arguments).map id)
      (some ((output arguments).map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using outputs arguments

/-- For zero-depth formals, the original positional judgment is exactly
authored arity together with the vector scope result. -/
theorem argumentsValidAt_iff (formals : List (String × Nat))
    (zeroDepth : ∀ formal ∈ formals, formal.2 = 0) (arguments : List Pattern) :
    argumentsValidAt formals arguments = true ↔
      arguments.length = formals.length ∧ arguments.all (argumentValidAt 0) = true := by
  induction formals generalizing arguments with
  | nil => cases arguments <;> simp [argumentsValidAt]
  | cons formal formals ih =>
    have head := zeroDepth formal (by simp)
    have tail : ∀ inner ∈ formals, inner.2 = 0 := fun inner member =>
      zeroDepth inner (List.mem_cons_of_mem formal member)
    cases arguments with
    | nil => simp [argumentsValidAt]
    | cons argument rest =>
      obtain ⟨name, depth⟩ := formal
      change depth = 0 at head
      subst depth
      simp only [argumentsValidAt, Bool.and_eq_true, List.length_cons,
        Nat.succ.injEq, List.all_cons, ih tail]
      tauto

theorem success_iff (arguments : List Pattern) :
    output arguments = .inr true :: (vector arguments).map Sum.inl ↔
      arguments.all (argumentValidAt 0) = true := by
  simp [output]

theorem invalid_member_refused {arguments : List Pattern} {argument : Pattern}
    (member : argument ∈ arguments) (invalid : argumentValidAt 0 argument = false) :
    output arguments = .inr false :: (vector arguments).map Sum.inl := by
  have rejected : arguments.all (argumentValidAt 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro admitted
    have individual := List.all_eq_true.mp admitted argument member
    rw [invalid] at individual
    contradiction
  simp only [output, rejected]

theorem invalid_unused_argument :
    output [.apply "a" [], .bvar 0] =
      .inr false :: (vector [.apply "a" [], .bvar 0]).map Sum.inl := by
  apply invalid_member_refused (argument := .bvar 0) (by simp)
  rfl

theorem duplicate_closed_arguments :
    output [.lambda none (.bvar 0), .lambda none (.bvar 0)] =
      .inr true :: (vector [.lambda none (.bvar 0), .lambda none (.bvar 0)]).map Sum.inl := rfl

theorem zero_depth_is_not_open_formal :
    argumentValidAt 1 (.bvar 0) = true ∧ argumentValidAt 0 (.bvar 0) = false := by
  decide

end ArgumentScope

namespace ScopedApplication

/-- The existing authored row framer determines the argument body. This is
the original framing operation, not a separate admission authority. -/
def frameResult (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    Option (List (Option Alphabet)) :=
  match selected definition ruleInstance with
  | none => none
  | some index => CertificateArgumentFraming.Execution.frameAtArity
      CertificateDataEncoding.patternCodec (authoredArity (row definition index)) ruleInstance.arguments

theorem admissionOutput_eq (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    admissionOutput definition ruleInstance = CertificateArgumentFraming.statusWire
      (frameResult definition ruleInstance) := by
  cases found : selected definition ruleInstance <;>
    simp only [admissionOutput, found, UniformArity.result, frameResult,
      argumentOutput, CertificateArgumentFraming.statusWire]

theorem frameResult_some {definition : CalculusLanguageDef} {ruleInstance : RuleInstance}
    {framing : List (Option Alphabet)} (found : frameResult definition ruleInstance = some framing) :
    framing = ArgumentScope.vector ruleInstance.arguments := by
  unfold frameResult at found
  cases selectedRow : selected definition ruleInstance with
  | none => simp only [selectedRow] at found; cases found
  | some index =>
    simp only [selectedRow, CertificateArgumentFraming.Execution.frameAtArity] at found
    split at found
    · exact Option.some.inj found.symm
    · cases found

theorem vector_length_le (ruleInstance : RuleInstance) :
    (ArgumentScope.vector ruleInstance.arguments).length ≤
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length := by
  have framed := CertificateArgumentFraming.framedArguments_length
    CertificateDataEncoding.patternCodec ruleInstance.arguments
  change _ ≤ (encodeData (.pair (Codec.string.put ruleInstance.ruleId.value)
    ((Codec.list CertificateDataEncoding.patternCodec).put ruleInstance.arguments))).length
  rw [encodeData_pair]
  simp only [List.length_cons, List.length_append]
  change _ ≤ (encodeWith Codec.string ruleInstance.ruleId.value).length +
    (encodeWith (Codec.list CertificateDataEncoding.patternCodec) ruleInstance.arguments).length + 1
  change (ArgumentScope.vector ruleInstance.arguments).length + 2 = _ at framed
  omega

def scopeResult (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : Bool :=
  (frameResult definition ruleInstance).isSome && ruleInstance.arguments.all (argumentValidAt 0)

def scopeTail (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : List (Option Alphabet ⊕ Bool) :=
  ((frameResult definition ruleInstance).map (List.map Sum.inl)).getD []

def scopeOutput (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : List (Option Alphabet ⊕ Bool) :=
  .inr (scopeResult definition ruleInstance) :: scopeTail definition ruleInstance

def scopeAccepted : Option Alphabet → Bool
  | some symbol => symbol == 1
  | none => false

attribute [local implicit_reducible] ArgumentScope.machine FramedWordValidation.retainedMachine
  FramedWordValidation.machine

local instance : Fintype (ArgumentScope.machine.Γ ArgumentScope.machine.k₁) := by
  change Fintype (Option Alphabet ⊕ Bool); infer_instance
local instance : Inhabited (ArgumentScope.machine.Γ ArgumentScope.machine.k₀) := by
  change Inhabited (Option Alphabet); infer_instance

def scopeDispatcher : FinTM2 :=
  StackMachineComposition.Dispatch.machine ArgumentScope.machine scopeAccepted [.inr false]

attribute [local implicit_reducible] scopeDispatcher

noncomputable def dispatchOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime scopeDispatcher (admissionOutput definition ruleInstance)
      (some (scopeOutput definition ruleInstance))
      (20020 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2 + 2) := by
  cases found : frameResult definition ruleInstance with
  | none =>
    have refused := StackMachineComposition.Dispatch.outputs_refused ArgumentScope.machine
      scopeAccepted [.inr false] (some (0 : Alphabet)) [] (by rfl)
    apply WordEqualityMachine.within (by
      simpa only [scopeDispatcher, admissionOutput_eq, found, CertificateArgumentFraming.statusWire,
        scopeOutput, scopeResult, scopeTail, Option.isSome_none, Bool.false_and,
        Option.map_none, Option.getD_none, TM2OutputsInTime] using refused)
    simp only [List.length_nil]; omega
  | some framing =>
    have same := frameResult_some found
    subst framing
    have admitted := StackMachineComposition.Dispatch.outputs_success ArgumentScope.machine
      scopeAccepted [.inr false] (some (1 : Alphabet)) (ArgumentScope.vector ruleInstance.arguments)
      (ArgumentScope.output ruleInstance.arguments)
      (20020 * ((ArgumentScope.vector ruleInstance.arguments).length + 1)^2)
      (by rfl) (ArgumentScope.outputs ruleInstance.arguments)
    apply WordEqualityMachine.within (by
      simpa only [scopeDispatcher, admissionOutput_eq, found, CertificateArgumentFraming.statusWire,
        scopeOutput, scopeResult, scopeTail, Option.isSome_some, Bool.true_and,
        Option.map_some, Option.getD_some, ArgumentScope.output, TM2OutputsInTime] using admitted)
    have size := vector_length_le ruleInstance
    nlinarith

local instance (definition : CalculusLanguageDef) : Fintype
    ((admissionMachine definition).Γ (admissionMachine definition).k₁) := by
  change Fintype (Option Alphabet); infer_instance
local instance (definition : CalculusLanguageDef) : Inhabited
    ((admissionMachine definition).Γ (admissionMachine definition).k₁) := by
  change Inhabited (Option Alphabet); infer_instance
local instance : Inhabited (scopeDispatcher.Γ scopeDispatcher.k₀) := by
  change Inhabited (Option Alphabet); infer_instance

def scopeMachine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (admissionMachine definition) scopeDispatcher (Equiv.refl _)

attribute [local implicit_reducible] scopeMachine

theorem framing_length_le (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (admissionOutput definition ruleInstance).length ≤
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1 := by
  rw [admissionOutput_eq]
  cases found : frameResult definition ruleInstance with
  | none => simp only [CertificateArgumentFraming.statusWire, List.length_cons, List.length_nil]; omega
  | some framing =>
    rw [frameResult_some found]
    simpa only [CertificateArgumentFraming.statusWire, List.length_cons] using
      Nat.add_le_add_right (vector_length_le ruleInstance) 1

theorem scopeTail_length_le (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (scopeTail definition ruleInstance).length ≤
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length := by
  cases found : frameResult definition ruleInstance with
  | none => simp only [scopeTail, found, Option.map_none, Option.getD_none, List.length_nil]; omega
  | some framing =>
    simpa only [scopeTail, found, Option.map_some, Option.getD_some, List.length_map,
      frameResult_some found] using vector_length_le ruleInstance

noncomputable def scopeOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (scopeMachine definition)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (scopeOutput definition ruleInstance))
      (20100 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2) := by
  have joined := StackMachineComposition.outputs (admissionMachine definition) scopeDispatcher
    (Equiv.refl _) (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
    (admissionOutput definition ruleInstance) (scopeOutput definition ruleInstance)
    (29 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 39)
    (20020 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2 + 2)
    (admissionOutputs definition ruleInstance) (by
      change TM2OutputsInTime scopeDispatcher ((admissionOutput definition ruleInstance).map id) _ _
      simpa only [List.map_id_fun, id_eq] using dispatchOutputs definition ruleInstance)
  apply WordEqualityMachine.within joined
  have size := framing_length_le definition ruleInstance
  nlinarith

def readScope : Option Alphabet ⊕ Bool → Bool
  | .inr value => value
  | .inl _ => false

local instance (definition : CalculusLanguageDef) : Fintype
    ((scopeMachine definition).Γ (scopeMachine definition).k₁) := by
  change Fintype (Option Alphabet ⊕ Bool); infer_instance
local instance (definition : CalculusLanguageDef) : Inhabited
    ((scopeMachine definition).Γ (scopeMachine definition).k₀) := by
  change Inhabited Alphabet; infer_instance

def savedMachine (definition : CalculusLanguageDef) : FinTM2 :=
  RetainedWordExecution.machine (scopeMachine definition) readScope

attribute [local implicit_reducible] savedMachine

def savedOutput (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) : List (Alphabet ⊕ Bool) :=
  .inr (scopeResult definition ruleInstance) ::
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map Sum.inl

noncomputable def savedOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (savedMachine definition)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (savedOutput definition ruleInstance))
      (20120 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2) := by
  have saved := RetainedWordExecution.outputs (scopeMachine definition) readScope
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance) (.inr (scopeResult definition ruleInstance))
    (scopeTail definition ruleInstance)
    (20100 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2)
    (scopeOutputs definition ruleInstance)
  apply WordEqualityMachine.within (by
    simpa only [savedMachine, savedOutput, readScope, TM2OutputsInTime] using saved)
  have size := scopeTail_length_le definition ruleInstance
  nlinarith

/-- The Boolean prefix is removed from a working copy by an actual word
homomorphism. The retaining caller still owns the complete tagged input. -/
def dropScope : Alphabet ⊕ Bool → List Alphabet
  | .inl symbol => [symbol]
  | .inr _ => []

theorem dropScope_savedOutput (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (savedOutput definition ruleInstance).flatMap dropScope =
      encodeWith CertificateDataEncoding.instanceCodec ruleInstance := by
  simp [savedOutput, dropScope, List.flatMap_map]

local instance (definition : CalculusLanguageDef) : Inhabited
    ((CertificateRuleAdmission.machine definition).Γ (CertificateRuleAdmission.machine definition).k₀) := by
  change Inhabited Alphabet; infer_instance

local instance : Fintype ((WordHomomorphismMachine.machine dropScope).Γ
    (WordHomomorphismMachine.machine dropScope).k₁) := by
  change Fintype Alphabet; infer_instance
local instance : Inhabited ((WordHomomorphismMachine.machine dropScope).Γ
    (WordHomomorphismMachine.machine dropScope).k₁) := by
  change Inhabited Alphabet; infer_instance

/-- Reclassification executes the original first-row lookup on the exact
retained instance bytes. Its physical projection and second lookup are counted. -/
def relookupMachine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (WordHomomorphismMachine.machine dropScope)
    (CertificateRuleAdmission.machine definition) (Equiv.refl _)

attribute [local implicit_reducible] relookupMachine

noncomputable def relookupOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (relookupMachine definition) (savedOutput definition ruleInstance)
      (some (CertificateRuleAdmission.output definition ruleInstance))
      (18 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 21) := by
  have projected := WordHomomorphismMachine.outputs dropScope (savedOutput definition ruleInstance)
  rw [dropScope_savedOutput] at projected
  have joined := StackMachineComposition.outputs (WordHomomorphismMachine.machine dropScope)
    (CertificateRuleAdmission.machine definition) (Equiv.refl _) (savedOutput definition ruleInstance)
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
    (CertificateRuleAdmission.output definition ruleInstance)
    (2 * (savedOutput definition ruleInstance).length +
      2 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 2)
    (12 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 15)
    projected (by
      change TM2OutputsInTime (CertificateRuleAdmission.machine definition)
        ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map id) _ _
      simpa only [List.map_id_fun, id_eq] using CertificateRuleAdmission.outputs definition ruleInstance)
  convert joined using 1
  all_goals first
    | rfl
    | (simp only [savedOutput, List.length_cons, List.length_map]; omega)

def readSelected (definition : CalculusLanguageDef) : Alphabet ⊕ Option (Fin definition.rules.length) →
    Option (Fin definition.rules.length)
  | .inr value => value
  | .inl _ => none

local instance (definition : CalculusLanguageDef) : Fintype
    ((relookupMachine definition).Γ (relookupMachine definition).k₁) := by
  change Fintype (Alphabet ⊕ Option (Fin definition.rules.length)); infer_instance
local instance (definition : CalculusLanguageDef) : Inhabited
    ((relookupMachine definition).Γ (relookupMachine definition).k₀) := by
  change Inhabited (Alphabet ⊕ Bool); infer_instance

def selectedMachine (definition : CalculusLanguageDef) : FinTM2 :=
  RetainedWordExecution.machine (relookupMachine definition) (readSelected definition)

attribute [local implicit_reducible] selectedMachine

/-- The row and admission result are two physical finite tags, followed by
every byte of the original instance, including unused arguments. -/
def output (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    List ((Alphabet ⊕ Bool) ⊕ Option (Fin definition.rules.length)) :=
  .inr (selected definition ruleInstance) ::
    .inl (.inr (scopeResult definition ruleInstance)) ::
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map (fun symbol => .inl (.inl symbol))

noncomputable def selectedOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (selectedMachine definition) (savedOutput definition ruleInstance)
      (some (output definition ruleInstance))
      (22 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 29) := by
  have retained := RetainedWordExecution.outputs (relookupMachine definition) (readSelected definition)
    (savedOutput definition ruleInstance) (.inr (selected definition ruleInstance))
    ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map Sum.inl)
    (18 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 21)
    (relookupOutputs definition ruleInstance)
  convert retained using 1
  all_goals first
    | rfl
    | (simp only [output, savedOutput, readSelected, List.map_cons, List.map_map, Function.comp_def]; done)
    | (simp only [savedOutput, List.length_cons, List.length_map]; omega)

local instance (definition : CalculusLanguageDef) : Fintype
    ((savedMachine definition).Γ (savedMachine definition).k₁) := by
  change Fintype (Alphabet ⊕ Bool); infer_instance
local instance (definition : CalculusLanguageDef) : Inhabited
    ((savedMachine definition).Γ (savedMachine definition).k₁) := by
  change Inhabited (Alphabet ⊕ Bool); infer_instance

def machine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (savedMachine definition) (selectedMachine definition) (Equiv.refl _)

attribute [local implicit_reducible] machine

/-- Actual first-order instance admission on the original codec image. This
joins both authored lookups, authored arity, every original scope check,
complete byte retention and physical status handoffs. Child judgments and
side conditions remain original source-checker obligations. -/
noncomputable def outputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (machine definition) (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some (output definition ruleInstance))
      (20200 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2) := by
  have joined := StackMachineComposition.outputs (savedMachine definition) (selectedMachine definition)
    (Equiv.refl _) (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
    (savedOutput definition ruleInstance) (output definition ruleInstance)
    (20120 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2)
    (22 * (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 29)
    (savedOutputs definition ruleInstance) (by
      change TM2OutputsInTime (selectedMachine definition) ((savedOutput definition ruleInstance).map id) _ _
      simpa only [List.map_id_fun, id_eq] using selectedOutputs definition ruleInstance)
  apply WordEqualityMachine.within joined
  simp only [savedOutput, List.length_cons, List.length_map]
  nlinarith

noncomputable def realization (definition : CalculusLanguageDef) :
    TM2ComputableInPolyTime (encodeWith CertificateDataEncoding.instanceCodec)
      (output definition) (fun ruleInstance : RuleInstance => ruleInstance) where
  tm := machine definition
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 20200 * (X + C 1)^2
  outputsFun ruleInstance := by
    change TM2OutputsInTime (machine definition)
      ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).map id)
      (some ((output definition ruleInstance).map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using outputs definition ruleInstance

/-- All-zero formals are precisely the first-order admission profile. The
physical Boolean tag agrees with the original positional argument judgment,
including arguments that no premise or conclusion happens to use. -/
theorem scopeResult_iff (definition : CalculusLanguageDef)
    (zeroDepth : ∀ index : Fin definition.rules.length,
      ∀ formal ∈ (row definition index).metavariables, formal.2 = 0) (ruleInstance : RuleInstance) :
    scopeResult definition ruleInstance = true ↔
      ∃ rule, definition.lookupRule? ruleInstance.ruleId = some rule ∧
        argumentsValidAt rule.metavariables ruleInstance.arguments = true := by
  cases found : selected definition ruleInstance with
  | none =>
    have missing : definition.lookupRule? ruleInstance.ruleId = none := by
      rw [← selected_lookup, found]; rfl
    simp [scopeResult, frameResult, found, missing]
  | some index =>
    have lookup := lookup_selected definition ruleInstance index found
    simp only [lookup, Option.some.injEq]
    have sourceEquivalent :
        (∃ rule, row definition index = rule ∧
          argumentsValidAt rule.metavariables ruleInstance.arguments = true) ↔
        argumentsValidAt (row definition index).metavariables ruleInstance.arguments = true := by
      constructor
      · rintro ⟨rule, same, admitted⟩
        subst rule
        exact admitted
      · intro admitted
        exact ⟨row definition index, rfl, admitted⟩
    rw [sourceEquivalent, ArgumentScope.argumentsValidAt_iff _ (zeroDepth index)]
    by_cases arity : ruleInstance.arguments.length = (row definition index).metavariables.length <;>
      simp [scopeResult, frameResult, found, CertificateArgumentFraming.Execution.frameAtArity,
        authoredArity, arity]

theorem scopeResult_of_application {definition : ValidatedCalculusLanguageDef}
    (zeroDepth : ∀ index : Fin definition.1.rules.length,
      ∀ formal ∈ (row definition.1 index).metavariables, formal.2 = 0)
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (accepted : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    scopeResult definition.1 ruleInstance = true := by
  obtain ⟨rule, lookup, arguments, _, _, _⟩ := instantiateRule?_eq_some_iff_application.mp accepted
  exact (scopeResult_iff definition.1 zeroDepth ruleInstance).mpr ⟨rule, lookup, arguments⟩

end ScopedApplication

end Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission
