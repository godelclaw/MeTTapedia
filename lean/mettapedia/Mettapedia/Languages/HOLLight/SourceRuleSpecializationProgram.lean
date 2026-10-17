import Mettapedia.Languages.HOLLight.SourceRuleSpecialization
import Mettapedia.Languages.HOLLight.ArgumentListProgram
import Mettapedia.Computability.RetainedWordProgram

/-!
# Original source-specialization table without finite-register enumeration

The original physical instruction table is assembled from component tables,
keys and initial registers. Each presentation is proved equal to the original
machine table. Source admission, rendering, naming, retention and refusal are
unchanged. The fixed original SPEC instruction array implements the same
indexed copier as the authored descriptor.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SourceRuleSpecialization.Program
open Turing Turing.TM2.Stmt
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open ArgumentRenderingMachine
local instance : Fintype ((SourceQuantifierEmission.firstField).Γ (SourceQuantifierEmission.firstField).k₁) := inferInstanceAs (Fintype (Alphabet))
local instance : Inhabited ((SourceQuantifierEmission.firstField).Γ (SourceQuantifierEmission.firstField).k₁) := inferInstanceAs (Inhabited (Alphabet))
local instance : Fintype ((Indexed.machine sourceSelector).Γ (Indexed.machine sourceSelector).k₁) := inferInstanceAs (Fintype (Alphabet))
local instance : Inhabited ((Indexed.machine sourceSelector).Γ (Indexed.machine sourceSelector).k₁) := inferInstanceAs (Inhabited (Alphabet))
local instance : Fintype ((WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Alphabet))).Γ (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Alphabet))).k₁) := inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance : Inhabited ((WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Alphabet))).Γ (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Alphabet))).k₁) := inferInstanceAs (Inhabited (Option (Option Alphabet)))
local instance (arity : Nat) : Fintype ((ArgumentListRendering.machine arity).Γ (ArgumentListRendering.machine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((ArgumentListRendering.machine arity).Γ (ArgumentListRendering.machine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity : Nat) : Fintype ((retainedRawMachine arity).Γ (retainedRawMachine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Option Alphabet))
local instance (arity : Nat) : Inhabited ((retainedRawMachine arity).Γ (retainedRawMachine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Option Alphabet))
local instance (arity : Nat) : Fintype ((retainedNamingMachine arity).Γ (retainedNamingMachine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Option Alphabet))
local instance (arity : Nat) : Inhabited ((retainedNamingMachine arity).Γ (retainedNamingMachine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Option Alphabet))
local instance (arity : Nat) : Fintype ((rawMachine arity).Γ (rawMachine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((rawMachine arity).Γ (rawMachine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity : Nat) : Fintype ((preparedMachine arity).Γ (preparedMachine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((preparedMachine arity).Γ (preparedMachine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance {arity : Nat} (indices : List (Fin arity)) : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) indices).Γ (FramedFieldSelection.machine (Γ := Alphabet) indices).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance {arity : Nat} (indices : List (Fin arity)) : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) indices).Γ (FramedFieldSelection.machine (Γ := Alphabet) indices).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

attribute [local implicit_reducible] SourceQuantifierEmission.rawMachine SourceQuantifierEmission.stripStatus
  SourceQuantifierEmission.rawIdentity StackMachineComposition.machine StackMachineComposition.Dispatch.machine
  WordHomomorphismMachine.machine Indexed.machine FramedWordMapping.machine FramedFieldSelection.machine
  ArgumentNamingMachine.machine CertificateDataTraversal.ProductField.machine
  CertificateDataTraversal.PrefixField.machine
  rawVectorMachine namedVectorMachine renderedRawMachine selectedRawMachine retainedRawMachine rawMachine
  selectedNamingMachine retainedNamingMachine namingMachine preparedMachine sourceTupleMachine tupleMachine
  RetainedWordExecution.WithOutput.machine
  PatternScopeExecution.OriginalAdmission.machine PatternScopeExecution.OriginalAdmission.projectedMachine
  PatternScopeExecution.VisitorAdapter.machine PatternScopeExecution.Binary.machine
  FramedWordValidation.machine FramedWordValidation.retainedMachine CertificateRuleAdmission.ArgumentScope.machine
  RetainedWordExecution.machine scopeDispatch listAdmissionMachine selectedAdmissionMachine
  retainedAdmissionMachine admissionMachine
  successMachine guardedMachine machine

local instance : Fintype (SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.k₀) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Fintype (ArgumentNamingMachine.machine.Γ ArgumentNamingMachine.machine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (ArgumentNamingMachine.machine.Γ ArgumentNamingMachine.machine.k₀) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (ArgumentNamingMachine.machine.Γ ArgumentNamingMachine.machine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)

private def selector (arity : Nat) (plan : Indexed.Template Alphabet arity) :
    (Indexed.machine plan).Λ → TM2.Stmt (Indexed.machine plan).Γ (Indexed.machine plan).Λ (Indexed.machine plan).σ :=
  Indexed.arrayProgram plan.length plan.toArray
private theorem selector_eq (arity : Nat) (plan : Indexed.Template Alphabet arity) :
    selector arity plan = (Indexed.machine plan).m := Indexed.arrayProgram_eq_program plan

abbrev sourceSelectInput : (Indexed.machine sourceSelector).K := .input
abbrev sourceSelectResult : (Indexed.machine sourceSelector).K := .result
def sourceSelect : (Indexed.machine sourceSelector).Λ →
    TM2.Stmt (Indexed.machine sourceSelector).Γ (Indexed.machine sourceSelector).Λ (Indexed.machine sourceSelector).σ :=
  selector 2 sourceSelector

abbrev rawInput : SourceQuantifierEmission.rawMachine.K := some (.inl (some .input))
abbrev rawResult : SourceQuantifierEmission.rawMachine.K := some (.inr .result)
def rawInitial : SourceQuantifierEmission.rawMachine.σ := ((none,false),((none,none),none),none)
def rawStrip : SourceQuantifierEmission.stripStatus.Λ →
    TM2.Stmt SourceQuantifierEmission.stripStatus.Γ SourceQuantifierEmission.stripStatus.Λ SourceQuantifierEmission.stripStatus.σ :=
  StackMachineComposition.Dispatch.Programs.body WordHomomorphismMachine.Stack.input WordHomomorphismMachine.Stack.result
    (none,none) .read
    AdmittedArgumentRendering.accept [] (WordHomomorphismMachine.program (fun symbol : Alphabet => [symbol]))
theorem rawStrip_eq : rawStrip = SourceQuantifierEmission.stripStatus.m := by
  exact (StackMachineComposition.Dispatch.Programs.body_eq SourceQuantifierEmission.rawIdentity
    AdmittedArgumentRendering.accept []).symm

def raw : SourceQuantifierEmission.rawMachine.Λ →
    TM2.Stmt SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.Λ SourceQuantifierEmission.rawMachine.σ :=
  StackMachineComposition.Programs.body (some CertificateDataTraversal.Stack.input) WordHomomorphismMachine.Stack.input
    StackMachineComposition.Dispatch.Phase.read (0 : Alphabet) id
    (CertificateDataTraversal.ProductField.machine false).m rawStrip
theorem raw_eq : raw = SourceQuantifierEmission.rawMachine.m := by
  unfold raw
  rw [rawStrip_eq]
  exact StackMachineComposition.body_eq SourceQuantifierEmission.firstField SourceQuantifierEmission.stripStatus (Equiv.refl Alphabet)

def rawMap : rawVectorMachine.Λ → TM2.Stmt rawVectorMachine.Γ rawVectorMachine.Λ rawVectorMachine.σ :=
  FramedWordMapping.Programs.body rawInput rawResult rawInitial (.inl .start) (0 : Alphabet) (0 : Alphabet) raw
theorem rawMap_eq : rawMap = rawVectorMachine.m := by
  unfold rawMap
  rw [raw_eq]
  exact FramedWordMapping.Programs.body_eq SourceQuantifierEmission.rawMachine
def rawMapInitial : rawVectorMachine.σ := (rawInitial,none,none,none,none)
abbrev rawMapInput : rawVectorMachine.K := none
abbrev rawMapResult : rawVectorMachine.K := some (some (some none))
def rawDispatch : (StackMachineComposition.Dispatch.machine rawVectorMachine scopeAccepted []).Λ →
    TM2.Stmt rawVectorMachine.Γ (StackMachineComposition.Dispatch.machine rawVectorMachine scopeAccepted []).Λ
      (StackMachineComposition.Dispatch.machine rawVectorMachine scopeAccepted []).σ :=
  StackMachineComposition.Dispatch.Programs.body rawMapInput rawMapResult rawMapInitial .scan scopeAccepted [] rawMap
theorem rawDispatch_eq : rawDispatch = (StackMachineComposition.Dispatch.machine rawVectorMachine scopeAccepted []).m := by
  unfold rawDispatch
  rw [rawMap_eq]
  exact (StackMachineComposition.Dispatch.Programs.body_eq rawVectorMachine scopeAccepted []).symm

def renderedRaw (arity : Nat) : (renderedRawMachine arity).Λ →
    TM2.Stmt (renderedRawMachine arity).Γ (renderedRawMachine arity).Λ (renderedRawMachine arity).σ :=
  StackMachineComposition.Programs.body (ArgumentListRendering.Program.resultKey arity) rawMapInput .read
    (none : Option Alphabet) id (ArgumentListRendering.Program.body arity) rawDispatch
theorem renderedRaw_eq (arity : Nat) : renderedRaw arity = (renderedRawMachine arity).m := by
  unfold renderedRaw
  rw [← ArgumentListRendering.Program.body_eq,rawDispatch_eq]
  exact StackMachineComposition.body_eq (ArgumentListRendering.machine arity)
    (StackMachineComposition.Dispatch.machine rawVectorMachine scopeAccepted []) (Equiv.refl (Option Alphabet))
def renderedRawInitial (arity : Nat) : (renderedRawMachine arity).σ :=
  ((ArgumentListRendering.Program.initial arity []).var,(rawMapInitial,none),none)
abbrev renderedRawInput (arity : Nat) : (renderedRawMachine arity).K := some (.inl (ArgumentListRendering.Program.inputKey arity))
abbrev renderedRawResult (arity : Nat) : (renderedRawMachine arity).K := some (.inr rawMapResult)
def selectedRaw (arity : Nat) : (selectedRawMachine arity).Λ →
    TM2.Stmt (selectedRawMachine arity).Γ (selectedRawMachine arity).Λ (selectedRawMachine arity).σ :=
  StackMachineComposition.Programs.body sourceSelectResult (renderedRawInput arity) (.inl (.inl (.spine ⟨0,Nat.zero_lt_succ _⟩)))
    (0 : Alphabet) id sourceSelect (renderedRaw arity)
theorem selectedRaw_eq (arity : Nat) : selectedRaw arity = (selectedRawMachine arity).m := by
  unfold selectedRaw sourceSelect
  rw [selector_eq,renderedRaw_eq]
  exact StackMachineComposition.body_eq (Indexed.machine sourceSelector) (renderedRawMachine arity) (Equiv.refl Alphabet)
def selectedRawInitial (arity : Nat) : (selectedRawMachine arity).σ := (none,renderedRawInitial arity,none)
abbrev selectedRawInput (arity : Nat) : (selectedRawMachine arity).K := some (.inl .input)
abbrev selectedRawResult (arity : Nat) : (selectedRawMachine arity).K := some (.inr (renderedRawResult arity))

def retainedRaw (arity : Nat) : (retainedRawMachine arity).Λ →
    TM2.Stmt (retainedRawMachine arity).Γ (retainedRawMachine arity).Λ (retainedRawMachine arity).σ :=
  RetainedWordExecution.WithOutput.Programs.statement (selectedRawInput arity) (selectedRawResult arity)
    (none : Option Alphabet) (none : Option Alphabet) (selectedRawInitial arity) (.inl (.emit ⟨0,by decide⟩))
    (selectedRaw arity)
theorem retainedRaw_eq (arity : Nat) : retainedRaw arity = (retainedRawMachine arity).m := by
  unfold retainedRaw
  rw [selectedRaw_eq]
  rfl
def rawPacketProgram (arity : Nat) : (rawMachine arity).Λ →
    TM2.Stmt (rawMachine arity).Γ (rawMachine arity).Λ (rawMachine arity).σ :=
  StackMachineComposition.Programs.body (FirstAlphabet := (retainedRawMachine arity).Γ)
    none WordHomomorphismMachine.Stack.input .read (default : Option Alphabet ⊕ Option Alphabet) id
    (retainedRaw arity) (WordHomomorphismMachine.program collapse)
theorem rawPacketProgram_eq (arity : Nat) : rawPacketProgram arity = (rawMachine arity).m := by
  unfold rawPacketProgram
  rw [retainedRaw_eq]
  exact StackMachineComposition.body_eq (retainedRawMachine arity) (WordHomomorphismMachine.machine collapse) (Equiv.refl _)
def rawPacketInitial (arity : Nat) : (rawMachine arity).σ :=
  ((selectedRawInitial arity,none,none),(none,none),none)
abbrev rawPacketInput (arity : Nat) : (rawMachine arity).K :=
  some (.inl (some (some (some (some (selectedRawInput arity))))))
abbrev rawPacketResult (arity : Nat) : (rawMachine arity).K := some (.inr .result)

def nameMap : namedVectorMachine.Λ → TM2.Stmt namedVectorMachine.Γ namedVectorMachine.Λ namedVectorMachine.σ :=
  FramedWordMapping.Programs.body ArgumentNamingMachine.Stack.input ArgumentNamingMachine.Stack.result
    (none : Option Alphabet) .start (0 : Alphabet) (0 : Alphabet) ArgumentNamingMachine.program
theorem nameMap_eq : nameMap = namedVectorMachine.m :=
  FramedWordMapping.Programs.body_eq ArgumentNamingMachine.machine
def nameMapInitial : namedVectorMachine.σ := (none,none,none,none,none)
abbrev nameMapInput : namedVectorMachine.K := none
abbrev nameMapResult : namedVectorMachine.K := some (some (some none))

def fieldSelection {arity : Nat} (indices : List (Fin arity)) :
    (FramedFieldSelection.machine (Γ := Alphabet) indices).Λ →
    TM2.Stmt (FramedFieldSelection.machine (Γ := Alphabet) indices).Γ
      (FramedFieldSelection.machine (Γ := Alphabet) indices).Λ (FramedFieldSelection.machine (Γ := Alphabet) indices).σ :=
  StackMachineComposition.Programs.body WordHomomorphismMachine.Stack.result Indexed.Stack.input (.emit ⟨0,by omega⟩)
    (none : Option (Option Alphabet)) id (WordHomomorphismMachine.program FramedFieldSelection.liftSymbol)
    (Indexed.arrayProgram (FramedFieldSelection.template indices).length (FramedFieldSelection.template indices).toArray)
theorem fieldSelection_eq {arity : Nat} (indices : List (Fin arity)) :
    fieldSelection indices = (FramedFieldSelection.machine (Γ := Alphabet) indices).m := by
  unfold fieldSelection
  rw [Indexed.arrayProgram_eq_program]
  exact StackMachineComposition.body_eq (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Alphabet)))
    (Indexed.machine (FramedFieldSelection.template indices)) (Equiv.refl _)
def fieldSelectionInitial {arity : Nat} (_indices : List (Fin arity)) :
    (FramedFieldSelection.machine (Γ := Alphabet) _indices).σ := ((none,none),none,none)
abbrev fieldInput {arity : Nat} (_indices : List (Fin arity)) : (FramedFieldSelection.machine (Γ := Alphabet) _indices).K :=
  some (.inl .input)
abbrev fieldResult {arity : Nat} (_indices : List (Fin arity)) : (FramedFieldSelection.machine (Γ := Alphabet) _indices).K :=
  some (.inr .result)
def selectedName (arity : Nat) : (selectedNamingMachine arity).Λ →
    TM2.Stmt (selectedNamingMachine arity).Γ (selectedNamingMachine arity).Λ (selectedNamingMachine arity).σ :=
  StackMachineComposition.Programs.body (fieldResult (rawIndices arity)) nameMapInput .scan (none : Option Alphabet) id
    (fieldSelection (rawIndices arity)) nameMap
theorem selectedName_eq (arity : Nat) : selectedName arity = (selectedNamingMachine arity).m := by
  unfold selectedName
  rw [fieldSelection_eq,nameMap_eq]
  exact StackMachineComposition.body_eq (FramedFieldSelection.machine (Γ := Alphabet) (rawIndices arity)) namedVectorMachine (Equiv.refl _)
def selectedNameInitial (arity : Nat) : (selectedNamingMachine arity).σ :=
  (fieldSelectionInitial (rawIndices arity),nameMapInitial,none)
abbrev selectedNameInput (arity : Nat) : (selectedNamingMachine arity).K := some (.inl (fieldInput (rawIndices arity)))
abbrev selectedNameResult (arity : Nat) : (selectedNamingMachine arity).K := some (.inr nameMapResult)
def retainedName (arity : Nat) : (retainedNamingMachine arity).Λ →
    TM2.Stmt (retainedNamingMachine arity).Γ (retainedNamingMachine arity).Λ (retainedNamingMachine arity).σ :=
  RetainedWordExecution.WithOutput.Programs.statement (selectedNameInput arity) (selectedNameResult arity)
    (none : Option Alphabet) (none : Option Alphabet) (selectedNameInitial arity) (.inl (.inl .read)) (selectedName arity)
theorem retainedName_eq (arity : Nat) : retainedName arity = (retainedNamingMachine arity).m := by
  unfold retainedName
  rw [selectedName_eq]
  rfl
def namingPacketProgram (arity : Nat) : (namingMachine arity).Λ →
    TM2.Stmt (namingMachine arity).Γ (namingMachine arity).Λ (namingMachine arity).σ :=
  StackMachineComposition.Programs.body (FirstAlphabet := (retainedNamingMachine arity).Γ)
    none WordHomomorphismMachine.Stack.input .read (default : Option Alphabet ⊕ Option Alphabet) id
    (retainedName arity) (WordHomomorphismMachine.program collapse)
theorem namingPacketProgram_eq (arity : Nat) : namingPacketProgram arity = (namingMachine arity).m := by
  unfold namingPacketProgram
  rw [retainedName_eq]
  exact StackMachineComposition.body_eq (retainedNamingMachine arity) (WordHomomorphismMachine.machine collapse) (Equiv.refl _)
def namingPacketInitial (arity : Nat) : (namingMachine arity).σ :=
  ((selectedNameInitial arity,none,none),(none,none),none)
abbrev namingPacketInput (arity : Nat) : (namingMachine arity).K :=
  some (.inl (some (some (some (some (selectedNameInput arity))))))
abbrev namingPacketResult (arity : Nat) : (namingMachine arity).K := some (.inr .result)

def prepared (arity : Nat) : (preparedMachine arity).Λ →
    TM2.Stmt (preparedMachine arity).Γ (preparedMachine arity).Λ (preparedMachine arity).σ :=
  StackMachineComposition.Programs.body (rawPacketResult arity) (namingPacketInput arity) (.inl .scan)
    (none : Option Alphabet) id (rawPacketProgram arity) (namingPacketProgram arity)
theorem prepared_eq (arity : Nat) : prepared arity = (preparedMachine arity).m := by
  unfold prepared
  rw [rawPacketProgram_eq,namingPacketProgram_eq]
  exact StackMachineComposition.body_eq (rawMachine arity) (namingMachine arity) (Equiv.refl _)
def preparedInitial (arity : Nat) : (preparedMachine arity).σ := (rawPacketInitial arity,namingPacketInitial arity,none)
abbrev preparedInput (arity : Nat) : (preparedMachine arity).K := some (.inl (rawPacketInput arity))
abbrev preparedResult (arity : Nat) : (preparedMachine arity).K := some (.inr (namingPacketResult arity))
def sourceTuple (arity prior : Nat) (within : prior < arity) : (sourceTupleMachine arity prior within).Λ →
    TM2.Stmt (sourceTupleMachine arity prior within).Γ (sourceTupleMachine arity prior within).Λ (sourceTupleMachine arity prior within).σ :=
  StackMachineComposition.Programs.body (preparedResult arity) (fieldInput (tupleIndices arity prior within)) (.inl .read)
    (none : Option Alphabet) id (prepared arity) (fieldSelection (tupleIndices arity prior within))
theorem sourceTuple_eq (arity prior : Nat) (within : prior < arity) :
    sourceTuple arity prior within = (sourceTupleMachine arity prior within).m := by
  unfold sourceTuple
  rw [prepared_eq,fieldSelection_eq]
  exact StackMachineComposition.body_eq (preparedMachine arity) (tupleMachine arity prior within) (Equiv.refl _)

abbrev sourceScope := PatternScopeExecution.OriginalAdmission.machine
abbrev scopeInput : sourceScope.K := some (.inl (some (.inl (some .input))))
abbrev scopeResult : sourceScope.K := some (.inr .result)
def scopeInitial : sourceScope.σ := (PatternScopeExecution.OriginalAdmission.initialConfig []).var
local instance : Fintype (sourceScope.Γ sourceScope.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (sourceScope.Γ sourceScope.k₀) := inferInstanceAs (Inhabited Alphabet)
abbrev validator := FramedWordValidation.machine sourceScope FramedWordValidation.readBoolean
def validatorInitial : validator.σ := (scopeInitial,none,none,none,true)
abbrev validatorInput : validator.K := none
abbrev validatorResult : validator.K := some (some none)

def validate : validator.Λ → TM2.Stmt validator.Γ validator.Λ validator.σ
  | .scan => pop validatorInput (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .finish)
        (branch (fun state => (state.2.1.getD none).isSome)
          (push (some none) (fun state => (state.2.1.getD none).getD (0 : Alphabet)) (goto fun _ => .copy))
          (goto fun _ => .restore)))
  | .copy => pop validatorInput (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .rejectTemporary)
        (branch (fun state => (state.2.1.getD none).isSome)
          (push (some none) (fun state => (state.2.1.getD none).getD (0 : Alphabet)) (goto fun _ => .copy))
          (goto fun _ => .restore)))
  | .restore => pop (some none) (fun state cell => (state.1,state.2.1,cell,state.2.2.2))
      (branch (fun state => state.2.2.1.isSome)
        (push (some (some (some scopeInput))) (fun state => state.2.2.1.getD (0 : Alphabet)) (goto fun _ => .restore))
        (load (fun state => (scopeInitial,none,none,none,state.2.2.2.2))
          (goto fun _ => .run (.inl (.inl (.visit .start))))))
  | .run label => StackMachineRegisters.withStack (Cell := Option Alphabet) id
      (StackMachineRegisters.withStack (Cell := Alphabet) id
        (StackMachineRegisters.withStack (Cell := Option Bool) id
          (StackMachineRegisters.returning (Extra := Option (Option Alphabet) × Option Alphabet × Option (Option Bool) × Bool)
            FramedWordValidation.Phase.run (fun _ => .read) (PatternScopeExecution.OriginalAdmission.program label))))
  | .read => pop (some (some (some scopeResult)))
      (fun state cell => (state.1,state.2.1,state.2.2.1,cell,state.2.2.2.2))
      (load (fun state => (state.1,state.2.1,state.2.2.1,state.2.2.2.1,
        state.2.2.2.2 && state.2.2.2.1.elim false FramedWordValidation.readBoolean)) (goto fun _ => .drain))
  | .drain => pop (some (some (some scopeResult)))
      (fun state cell => (state.1,state.2.1,state.2.2.1,cell,state.2.2.2.2))
      (branch (fun state => state.2.2.2.1.isSome) (goto fun _ => .drain)
        (load (fun state => (scopeInitial,none,none,none,state.2.2.2.2)) (goto fun _ => .scan)))
  | .finish => push validatorResult (fun state => some state.2.2.2.2)
      (load (fun _ => validatorInitial) halt)
  | .rejectTemporary => pop (some none) (fun state cell => (state.1,state.2.1,cell,state.2.2.2))
      (branch (fun state => state.2.2.1.isSome) (goto fun _ => .rejectTemporary)
        (push validatorResult (fun _ => some false) (load (fun _ => validatorInitial) halt)))

theorem validate_eq : validate = validator.m := by
  funext phase
  cases phase with
  | run label =>
    simp only [validate,PatternScopeExecution.OriginalAdmission.program_eq]
    rfl
  | _ => rfl

local instance : Fintype (validator.Γ validator.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (validator.Γ validator.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
def scope : scopeProgram.Λ → TM2.Stmt scopeProgram.Γ scopeProgram.Λ scopeProgram.σ :=
  RetainedWordExecution.Programs.body validatorInput validatorResult validatorInitial .scan
    (none : Option Alphabet) false FramedWordValidation.readBoolean validate
theorem scope_eq : scope = scopeProgram.m := by
  unfold scope
  rw [validate_eq]
  exact RetainedWordExecution.Programs.body_eq validator FramedWordValidation.readBoolean
def scopeRetainedInitial : scopeProgram.σ := (validatorInitial,none,none,false)
abbrev scopeRetainedInput : scopeProgram.K := some (some (some validatorInput))
abbrev scopeRetainedResult : scopeProgram.K := none
def scopeDispatched : scopeDispatch.Λ → TM2.Stmt scopeDispatch.Γ scopeDispatch.Λ scopeDispatch.σ :=
  StackMachineComposition.Dispatch.Programs.body scopeRetainedInput scopeRetainedResult scopeRetainedInitial
    .scan scopeAccepted [.inr false] scope
theorem scopeDispatched_eq : scopeDispatched = scopeDispatch.m := by
  unfold scopeDispatched
  rw [scope_eq]
  exact (StackMachineComposition.Dispatch.Programs.body_eq scopeProgram scopeAccepted [.inr false]).symm
local instance (arity : Nat) : Fintype ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def listAdmission (arity : Nat) : (listAdmissionMachine arity).Λ →
    TM2.Stmt (listAdmissionMachine arity).Γ (listAdmissionMachine arity).Λ (listAdmissionMachine arity).σ :=
  StackMachineComposition.Programs.body CertificateArgumentFraming.Execution.resultKey scopeRetainedInput .read
    (none : Option Alphabet) id (CertificateArgumentFraming.Execution.machine arity).m scopeDispatched
theorem listAdmission_eq (arity : Nat) : listAdmission arity = (listAdmissionMachine arity).m := by
  unfold listAdmission
  rw [scopeDispatched_eq]
  exact StackMachineComposition.body_eq (CertificateArgumentFraming.Execution.machine arity) scopeDispatch (Equiv.refl _)
def listAdmissionInitial (arity : Nat) : (listAdmissionMachine arity).σ := ((none,none),(scopeRetainedInitial,none),none)
abbrev listAdmissionInput (arity : Nat) : (listAdmissionMachine arity).K := some (.inl CertificateArgumentFraming.Execution.inputKey)
abbrev listAdmissionResult (arity : Nat) : (listAdmissionMachine arity).K := some (.inr scopeRetainedResult)
def selectedAdmission (arity : Nat) : (selectedAdmissionMachine arity).Λ →
    TM2.Stmt (selectedAdmissionMachine arity).Γ (selectedAdmissionMachine arity).Λ (selectedAdmissionMachine arity).σ :=
  StackMachineComposition.Programs.body sourceSelectResult (listAdmissionInput arity) (.inl (.spine ⟨0,Nat.zero_lt_succ _⟩))
    (0 : Alphabet) id sourceSelect (listAdmission arity)
theorem selectedAdmission_eq (arity : Nat) : selectedAdmission arity = (selectedAdmissionMachine arity).m := by
  unfold selectedAdmission sourceSelect
  rw [selector_eq,listAdmission_eq]
  exact StackMachineComposition.body_eq (Indexed.machine sourceSelector) (listAdmissionMachine arity) (Equiv.refl Alphabet)
def selectedAdmissionInitial (arity : Nat) : (selectedAdmissionMachine arity).σ := (none,listAdmissionInitial arity,none)
abbrev selectedAdmissionInput (arity : Nat) : (selectedAdmissionMachine arity).K := some (.inl .input)
abbrev selectedAdmissionResult (arity : Nat) : (selectedAdmissionMachine arity).K := some (.inr (listAdmissionResult arity))
local instance (arity : Nat) : Fintype ((selectedAdmissionMachine arity).Γ (selectedAdmissionMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (arity : Nat) : Inhabited ((selectedAdmissionMachine arity).Γ (selectedAdmissionMachine arity).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def retainedAdmission (arity : Nat) : (retainedAdmissionMachine arity).Λ →
    TM2.Stmt (retainedAdmissionMachine arity).Γ (retainedAdmissionMachine arity).Λ (retainedAdmissionMachine arity).σ :=
  RetainedWordExecution.Programs.body (selectedAdmissionInput arity) (selectedAdmissionResult arity)
    (selectedAdmissionInitial arity) (.inl (.emit ⟨0,by decide⟩))
    (none : Option Alphabet) false CertificateRuleAdmission.ScopedApplication.readScope (selectedAdmission arity)
theorem retainedAdmission_eq (arity : Nat) : retainedAdmission arity = (retainedAdmissionMachine arity).m := by
  unfold retainedAdmission
  rw [selectedAdmission_eq]
  exact RetainedWordExecution.Programs.body_eq (selectedAdmissionMachine arity) CertificateRuleAdmission.ScopedApplication.readScope
local instance (arity : Nat) : Fintype ((retainedAdmissionMachine arity).Γ (retainedAdmissionMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (arity : Nat) : Inhabited ((retainedAdmissionMachine arity).Γ (retainedAdmissionMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))
def admission (arity : Nat) : (admissionMachine arity).Λ →
    TM2.Stmt (admissionMachine arity).Γ (admissionMachine arity).Λ (admissionMachine arity).σ :=
  StackMachineComposition.Programs.body (FirstAlphabet := (retainedAdmissionMachine arity).Γ)
    none WordHomomorphismMachine.Stack.input .read (default : Option Alphabet ⊕ Bool) id
    (retainedAdmission arity) (WordHomomorphismMachine.program project)
theorem admission_eq (arity : Nat) : admission arity = (admissionMachine arity).m := by
  unfold admission
  rw [retainedAdmission_eq]
  exact StackMachineComposition.body_eq (retainedAdmissionMachine arity) (WordHomomorphismMachine.machine project) (Equiv.refl _)
def admissionInitial (arity : Nat) : (admissionMachine arity).σ :=
  ((selectedAdmissionInitial arity,none,none,false),(none,none),none)
abbrev admissionInput (arity : Nat) : (admissionMachine arity).K :=
  some (.inl (some (some (some (selectedAdmissionInput arity)))))
abbrev admissionResult (arity : Nat) : (admissionMachine arity).K := some (.inr .result)

def sourceTupleInitial (arity prior : Nat) (within : prior < arity) : (sourceTupleMachine arity prior within).σ :=
  (preparedInitial arity,fieldSelectionInitial (tupleIndices arity prior within),none)
abbrev sourceTupleInput (arity prior : Nat) (within : prior < arity) : (sourceTupleMachine arity prior within).K :=
  some (.inl (preparedInput arity))
abbrev sourceTupleResult (arity prior : Nat) (within : prior < arity) : (sourceTupleMachine arity prior within).K :=
  some (.inr (fieldResult (tupleIndices arity prior within)))
open Mettapedia.OSLF.MeTTaIL.Syntax
local instance (arity prior : Nat) (within : prior < arity) : Fintype
    ((sourceTupleMachine arity prior within).Γ (sourceTupleMachine arity prior within).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity prior : Nat) (within : prior < arity) : Inhabited
    ((sourceTupleMachine arity prior within).Γ (sourceTupleMachine arity prior within).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def successWithArray (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (instructions : Array (Alphabet ⊕ Fin (ScopedBetaEmission.FieldCount prior))) :
    (successMachine rule prior within).Λ →
    TM2.Stmt (successMachine rule prior within).Γ (successMachine rule prior within).Λ (successMachine rule prior within).σ :=
  StackMachineComposition.Programs.body (sourceTupleResult (ScopedRuleSpecialization.rowArity rule) prior within)
    Indexed.Stack.input (.emit ⟨0,by omega⟩) (none : Option Alphabet) id
    (sourceTuple (ScopedRuleSpecialization.rowArity rule) prior within)
    (Indexed.arrayProgram (ScopedRuleSpecialization.template rule prior within).length instructions)
theorem successWithArray_eq (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    successWithArray rule prior within (ScopedRuleSpecialization.template rule prior within).toArray =
      (successMachine rule prior within).m := by
  unfold successWithArray
  rw [sourceTuple_eq,Indexed.arrayProgram_eq_program]
  exact StackMachineComposition.body_eq (sourceTupleMachine (ScopedRuleSpecialization.rowArity rule) prior within)
    (Indexed.machine (ScopedRuleSpecialization.template rule prior within)) (Equiv.refl _)
def successInitial (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    (successMachine rule prior within).σ :=
  (sourceTupleInitial (ScopedRuleSpecialization.rowArity rule) prior within,none,none)
abbrev successInput (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    (successMachine rule prior within).K := some (.inl (sourceTupleInput (ScopedRuleSpecialization.rowArity rule) prior within))
abbrev successResult (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    (successMachine rule prior within).K := some (.inr .result)
def guardedWithArray (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (instructions : Array (Alphabet ⊕ Fin (ScopedBetaEmission.FieldCount prior))) :
    (guardedMachine rule prior within).Λ →
    TM2.Stmt (guardedMachine rule prior within).Γ (guardedMachine rule prior within).Λ (guardedMachine rule prior within).σ :=
  StackMachineComposition.Dispatch.Programs.body (successInput rule prior within) (successResult rule prior within)
    (successInitial rule prior within) (.inl (.inl (.inl (.inl .scan)))) scopeAccepted [] (successWithArray rule prior within instructions)
theorem guardedWithArray_eq (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    guardedWithArray rule prior within (ScopedRuleSpecialization.template rule prior within).toArray =
      (guardedMachine rule prior within).m := by
  unfold guardedWithArray
  rw [successWithArray_eq]
  exact (StackMachineComposition.Dispatch.Programs.body_eq (successMachine rule prior within) scopeAccepted []).symm
local instance (arity : Nat) : Fintype ((admissionMachine arity).Γ (admissionMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((admissionMachine arity).Γ (admissionMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

/-- The full original table accepts one eagerly materialized fixed descriptor. -/
def bodyWithArray (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (instructions : Array (Alphabet ⊕ Fin (ScopedBetaEmission.FieldCount prior))) :
    (machine rule prior within).Λ →
    TM2.Stmt (machine rule prior within).Γ (machine rule prior within).Λ (machine rule prior within).σ :=
  StackMachineComposition.Programs.body (admissionResult (ScopedRuleSpecialization.rowArity rule))
    (successInput rule prior within) .read (none : Option Alphabet) id
    (admission (ScopedRuleSpecialization.rowArity rule)) (guardedWithArray rule prior within instructions)
def body (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    (machine rule prior within).Λ →
    TM2.Stmt (machine rule prior within).Γ (machine rule prior within).Λ (machine rule prior within).σ :=
  bodyWithArray rule prior within (ScopedRuleSpecialization.template rule prior within).toArray
theorem body_eq (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    body rule prior within = (machine rule prior within).m := by
  unfold body bodyWithArray
  rw [admission_eq,guardedWithArray_eq]
  exact StackMachineComposition.body_eq (admissionMachine (ScopedRuleSpecialization.rowArity rule))
    (guardedMachine rule prior within) (Equiv.refl _)

def added {A : Type} (keys : List A) : List (Option A) := none :: keys.map some
def joined {A B : Type} (left : List A) (right : List B) : List (Option (A ⊕ B)) :=
  none :: (left.map (some ∘ Sum.inl) ++ right.map (some ∘ Sum.inr))
theorem added_complete {A : Type} (keys : List A) (complete : ∀ key, key ∈ keys) :
    ∀ key, key ∈ added keys := by
  intro key
  cases key <;> simp [added,complete]
theorem joined_complete {A B : Type} (left : List A) (right : List B)
    (allLeft : ∀ key, key ∈ left) (allRight : ∀ key, key ∈ right) : ∀ key, key ∈ joined left right := by
  intro key
  rcases key with _ | (key | key) <;> simp [joined,allLeft,allRight]

def mapKeys : List WordHomomorphismMachine.Stack := [.input,.output,.result]
def indexedKeys : List Indexed.Stack := [.input,.temporary,.output,.result]
def spanKeys : List PatternSpanExecution.Execution.Stack := [.input,.frames,.scratch,.span,.tasks,.events,.result]
def sourceScopeKeys : List sourceScope.K := joined (joined (added spanKeys) mapKeys)
  (show List PatternScopeExecution.Binary.Stack from [.input,.number,.depth,.scratch,.saved,.result])
def scalarKeys : List AdmittedArgumentRendering.machine.K := joined
  (joined (added (added (added sourceScopeKeys))) mapKeys)
  (joined (joined (added (added spanKeys)) (show List Routing.Key from [.input,.output,.result,.depth]))
    (Execution.Key.result :: Execution.clearKeys))
def framerKeys : List CertificateArgumentFraming.Execution.Key :=
  [none,some none,some (some none),some (some (some .input)),some (some (some .frames)),some (some (some .output))]
def renderingKeys (arity : Nat) : List (ArgumentListRendering.machine arity).K := joined framerKeys
  (joined (added (added (added (added scalarKeys)))) (show List WordTemplateMachine.Stack from [.input,.temporary,.output]))
def rawKeys : List SourceQuantifierEmission.rawMachine.K :=
  joined (show List SourceQuantifierEmission.firstField.K from [none,some .input,some .frames,some .output]) mapKeys
def selectedRawKeys (arity : Nat) : List (selectedRawMachine arity).K :=
  joined indexedKeys (joined (renderingKeys arity) (added (added (added (added rawKeys)))))
def rawPacketKeys (arity : Nat) : List (rawMachine arity).K :=
  joined (added (added (added (added (selectedRawKeys arity))))) mapKeys
def fieldKeys : List (FramedFieldSelection.machine (Γ := Alphabet) ([] : List (Fin 0))).K := joined mapKeys indexedKeys
def namingKeys (arity : Nat) : List (namingMachine arity).K := joined
  (added (added (added (added (joined fieldKeys
    (added (added (added (added (show List ArgumentNamingMachine.Stack from [.input,.pending,.output,.result])))))))))) mapKeys
def preparedKeys (arity : Nat) : List (preparedMachine arity).K := joined (rawPacketKeys arity) (namingKeys arity)
def sourceTupleKeys (arity prior : Nat) (within : prior < arity) : List (sourceTupleMachine arity prior within).K :=
  joined (preparedKeys arity) fieldKeys
def scopeRetainedKeys : List scopeProgram.K := added (added (added (added (added (added sourceScopeKeys)))))
def listAdmissionKeys (arity : Nat) : List (listAdmissionMachine arity).K := joined framerKeys scopeRetainedKeys
def selectedAdmissionKeys (arity : Nat) : List (selectedAdmissionMachine arity).K := joined indexedKeys (listAdmissionKeys arity)
def admissionKeys (arity : Nat) : List (admissionMachine arity).K :=
  joined (added (added (added (selectedAdmissionKeys arity)))) mapKeys
def keys (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    List (machine rule prior within).K :=
  joined (admissionKeys (ScopedRuleSpecialization.rowArity rule))
    (joined (sourceTupleKeys (ScopedRuleSpecialization.rowArity rule) prior within) indexedKeys)

private theorem mapKeys_complete : ∀ key, key ∈ mapKeys := by intro key; cases key <;> simp [mapKeys]
private theorem indexedKeys_complete : ∀ key, key ∈ indexedKeys := by intro key; cases key <;> simp [indexedKeys]
private theorem spanKeys_complete : ∀ key, key ∈ spanKeys := by intro key; cases key <;> simp [spanKeys]
private theorem sourceScopeKeys_complete : ∀ key, key ∈ sourceScopeKeys := by
  apply joined_complete
  · exact joined_complete _ _ (added_complete _ spanKeys_complete) mapKeys_complete
  · intro key; cases key <;> simp
private theorem scalarKeys_complete : ∀ key, key ∈ scalarKeys := by
  apply joined_complete
  · apply joined_complete
    · exact added_complete _ (added_complete _ (added_complete _ sourceScopeKeys_complete))
    · exact mapKeys_complete
  · apply joined_complete
    · apply joined_complete
      · exact added_complete _ (added_complete _ spanKeys_complete)
      · intro key; cases key <;> simp
    · intro key
      cases key with
      | body key =>
        cases key with
        | head key => cases key <;> simp [Execution.clearKeys,Execution.localClearKeys,Execution.headKeys]
        | saved key =>
          cases key with
          | «local» key => cases key <;> simp [Execution.clearKeys,Execution.localClearKeys,Execution.headKeys]
          | frames key => cases key <;> simp [Execution.clearKeys,Execution.localClearKeys,Execution.headKeys]
        | children => simp [Execution.clearKeys,Execution.localClearKeys]
      | input | result | returnWord | returnScratch => simp [Execution.clearKeys,Execution.localClearKeys]
private theorem framerKeys_complete : ∀ key, key ∈ framerKeys := by
  intro key
  rcases key with _ | (_ | (_ | key)) <;> simp [framerKeys]
  cases key <;> simp
private theorem renderingKeys_complete (arity : Nat) : ∀ key, key ∈ renderingKeys arity := by
  apply joined_complete _ _ framerKeys_complete
  apply joined_complete
  · exact added_complete _ (added_complete _ (added_complete _ (added_complete _ scalarKeys_complete)))
  · intro key; cases key <;> simp
private theorem rawKeys_complete : ∀ key, key ∈ rawKeys := by
  apply joined_complete
  · intro key; rcases key with _ | key <;> simp
    cases key <;> simp
  · exact mapKeys_complete
private theorem selectedRawKeys_complete (arity : Nat) : ∀ key, key ∈ selectedRawKeys arity := by
  apply joined_complete _ _ indexedKeys_complete
  exact joined_complete _ _ (renderingKeys_complete arity)
    (added_complete _ (added_complete _ (added_complete _ (added_complete _ rawKeys_complete))))
private theorem rawPacketKeys_complete (arity : Nat) : ∀ key, key ∈ rawPacketKeys arity :=
  joined_complete _ _ (added_complete _ (added_complete _ (added_complete _ (added_complete _ (selectedRawKeys_complete arity))))) mapKeys_complete
private theorem fieldKeys_complete : ∀ key, key ∈ fieldKeys := joined_complete _ _ mapKeys_complete indexedKeys_complete
private theorem namingKeys_complete (arity : Nat) : ∀ key, key ∈ namingKeys arity := by
  apply joined_complete
  · apply added_complete
    apply added_complete
    apply added_complete
    apply added_complete
    apply joined_complete _ _ fieldKeys_complete
    apply added_complete
    apply added_complete
    apply added_complete
    apply added_complete
    intro key; cases key <;> simp
  · exact mapKeys_complete
private theorem preparedKeys_complete (arity : Nat) : ∀ key, key ∈ preparedKeys arity :=
  joined_complete _ _ (rawPacketKeys_complete arity) (namingKeys_complete arity)
private theorem sourceTupleKeys_complete (arity prior : Nat) (within : prior < arity) : ∀ key, key ∈ sourceTupleKeys arity prior within :=
  joined_complete _ _ (preparedKeys_complete arity) fieldKeys_complete
private theorem admissionKeys_complete (arity : Nat) : ∀ key, key ∈ admissionKeys arity := by
  apply joined_complete
  · apply added_complete
    apply added_complete
    apply added_complete
    apply joined_complete _ _ indexedKeys_complete
    apply joined_complete _ _ framerKeys_complete
    apply added_complete
    apply added_complete
    apply added_complete
    apply added_complete
    apply added_complete
    exact added_complete _ sourceScopeKeys_complete
  · exact mapKeys_complete
theorem all_keys (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    ∀ key, key ∈ keys rule prior within :=
  joined_complete _ _ (admissionKeys_complete _) (joined_complete _ _ (sourceTupleKeys_complete _ prior within) indexedKeys_complete)

private def addedEquality {A : Type} (equality : DecidableEq A) : DecidableEq (Option A) := by
  letI := equality
  infer_instance
private def joinedEquality {A B : Type} (left : DecidableEq A) (right : DecidableEq B) : DecidableEq (Option (A ⊕ B)) := by
  letI := left
  letI := right
  infer_instance
def rawKeyEquality : DecidableEq SourceQuantifierEmission.rawMachine.K :=
  inferInstanceAs (DecidableEq (Option (Option CertificateDataTraversal.Stack ⊕ WordHomomorphismMachine.Stack)))
def selectedRawKeyEquality (arity : Nat) : DecidableEq (selectedRawMachine arity).K :=
  joinedEquality (inferInstanceAs (DecidableEq Indexed.Stack))
    (joinedEquality (ArgumentListRendering.Program.keyEquality arity)
      (addedEquality (addedEquality (addedEquality (addedEquality rawKeyEquality)))))
def rawPacketKeyEquality (arity : Nat) : DecidableEq (rawMachine arity).K :=
  joinedEquality (addedEquality (addedEquality (addedEquality (addedEquality (selectedRawKeyEquality arity)))))
    (inferInstanceAs (DecidableEq WordHomomorphismMachine.Stack))
def fieldKeyEquality : DecidableEq (FramedFieldSelection.machine (Γ := Alphabet) ([] : List (Fin 0))).K :=
  inferInstanceAs (DecidableEq (Option (WordHomomorphismMachine.Stack ⊕ Indexed.Stack)))
def namingKeyEquality (arity : Nat) : DecidableEq (namingMachine arity).K :=
  joinedEquality (addedEquality (addedEquality (addedEquality (addedEquality
    (joinedEquality fieldKeyEquality (addedEquality (addedEquality (addedEquality
      (addedEquality (inferInstanceAs (DecidableEq ArgumentNamingMachine.Stack)))))))))))
    (inferInstanceAs (DecidableEq WordHomomorphismMachine.Stack))
def preparedKeyEquality (arity : Nat) : DecidableEq (preparedMachine arity).K :=
  joinedEquality (rawPacketKeyEquality arity) (namingKeyEquality arity)
def sourceTupleKeyEquality (arity prior : Nat) (within : prior < arity) : DecidableEq (sourceTupleMachine arity prior within).K :=
  joinedEquality (preparedKeyEquality arity) fieldKeyEquality
def admissionKeyEquality (arity : Nat) : DecidableEq (admissionMachine arity).K :=
  joinedEquality (addedEquality (addedEquality (addedEquality
    (joinedEquality (inferInstanceAs (DecidableEq Indexed.Stack))
      (joinedEquality (inferInstanceAs (DecidableEq CertificateArgumentFraming.Execution.Key))
        (addedEquality (addedEquality (addedEquality (addedEquality (addedEquality
          (addedEquality PatternScopeExecution.OriginalAdmission.keyEquality)))))))))))
    (inferInstanceAs (DecidableEq WordHomomorphismMachine.Stack))
def keyEquality (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    DecidableEq (machine rule prior within).K :=
  joinedEquality (admissionKeyEquality (ScopedRuleSpecialization.rowArity rule))
    (joinedEquality (sourceTupleKeyEquality (ScopedRuleSpecialization.rowArity rule) prior within)
      (inferInstanceAs (DecidableEq Indexed.Stack)))

abbrev inputKey (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    (machine rule prior within).K := some (.inl (admissionInput (ScopedRuleSpecialization.rowArity rule)))
abbrev resultKey (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    (machine rule prior within).K := some (.inr (successResult rule prior within))
def initialRegisters (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    (machine rule prior within).σ :=
  (admissionInitial (ScopedRuleSpecialization.rowArity rule),(successInitial rule prior within,none),none)
theorem initialRegisters_eq (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    initialRegisters rule prior within = (machine rule prior within).initialState := rfl
def initial (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (word : List (Option Alphabet)) : (machine rule prior within).Cfg where
  l := some (.inl (.inl .scan))
  var := initialRegisters rule prior within
  stk key := @dite (List ((machine rule prior within).Γ key)) (key = inputKey rule prior within)
    (keyEquality rule prior within key (inputKey rule prior within)) (fun same => same.symm ▸ word) (fun _ => [])
theorem initial_eq (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (word : List (Option Alphabet)) : initial rule prior within word = initList (machine rule prior within) word := by
  have equality : keyEquality rule prior within = (machine rule prior within).kDecidableEq := Subsingleton.elim _ _
  unfold initial
  rw [equality,initialRegisters_eq]
  unfold initList
  congr 1
  funext key
  by_cases same : key = inputKey rule prior within
  · subst key
    simp [show inputKey rule prior within = (machine rule prior within).k₀ from rfl]
  · have different : key ≠ (machine rule prior within).k₀ := same
    simp only [dif_neg same,dif_neg different]
def stepWithArray (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (instructions : Array (Alphabet ⊕ Fin (ScopedBetaEmission.FieldCount prior))) :
    (machine rule prior within).Cfg → Option (machine rule prior within).Cfg :=
  @TM2.step (machine rule prior within).K (machine rule prior within).Γ (machine rule prior within).Λ
    (machine rule prior within).σ (keyEquality rule prior within) (bodyWithArray rule prior within instructions)
def step (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    (machine rule prior within).Cfg → Option (machine rule prior within).Cfg :=
  stepWithArray rule prior within (ScopedRuleSpecialization.template rule prior within).toArray
theorem step_eq (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) :
    step rule prior within = (machine rule prior within).step := by
  unfold step stepWithArray
  rw [show keyEquality rule prior within = (machine rule prior within).kDecidableEq from Subsingleton.elim _ _]
  change TM2.step (body rule prior within) = _
  rw [body_eq]
  rfl

end Mettapedia.Languages.HOLLight.SourceRuleSpecialization.Program
