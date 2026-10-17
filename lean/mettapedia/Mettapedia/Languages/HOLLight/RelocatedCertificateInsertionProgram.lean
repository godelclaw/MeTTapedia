import Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion
import Mettapedia.Languages.HOLLight.EmittedCertificateInsertionProgram
import Mettapedia.Languages.HOLLight.GraphRelocationEmissionProgram
/-!
# Original relocation, certificate parsing and chronological insertion instructions

The computed program retains the original packet, emits the relocated graph,
parses the actual certificate and physically appends its receipt list. Its
instruction table, initial state, complete stack coverage and counted execution
agree with the original composed machine. The prepared factory captures the
compiled relocation array and label dimensions while preserving every original
instruction and clock. Replay and input admission retain their original scope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion.Program
open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion
attribute [local reducible] RelocatedCertificateInsertion.machine routedMachine retainedMachine selectedMachine
  StackMachineComposition.machine StackMachineComposition.leftKey StackMachineComposition.rightKey
  RetainedWordExecution.WithOutput.machine RetainedWordExecution.WithOutput.Framed.machine
  RetainedWordExecution.WithOutput.Framed.taggedMachine RetainedWordExecution.WithOutput.Framed.untag
  WordHomomorphismMachine.machine WordTemplateMachine.machine Indexed.machine FramedFieldSelection.machine
  GraphRelocationEmission.machine GraphRelocationEmission.preparedMachine GraphRelocationEmission.retainedMachine
  GraphRelocationEmission.selectedAddressMachine GraphAddressSequence.machine GraphAddressSequence.mappedMachine

attribute [local reducible] EmittedCertificateInsertion.machine EmittedCertificateInsertion.routedMachine EmittedCertificateInsertion.parsedPacketMachine
  EmittedCertificateInsertion.firstMachine EmittedCertificateInsertion.secondMachine EmittedCertificateInsertion.componentMachine EmittedCertificateInsertion.parsedMachine EmittedCertificateInsertion.componentPlan
  ChronologicalInsertion.machine ChronologicalInsertion.retainedMachine ChronologicalInsertion.rawMachine ChronologicalInsertion.appendedMachine
  StackMachineComposition.machine StackMachineComposition.leftKey StackMachineComposition.rightKey
  WordHomomorphismMachine.machine WordTemplateMachine.machine Indexed.machine
  RetainedWordExecution.machine RetainedWordExecution.WithOutput.machine RetainedWordExecution.WithOutput.Framed.machine
  RetainedWordExecution.WithOutput.Framed.taggedMachine RetainedWordExecution.WithOutput.Framed.untag
  CertificateDataTraversal.ProductField.machine CertificateDataTraversal.PrefixField.machine
  BinaryListAppend.machine BinaryListAppend.checkedSuffixMachine BinaryListAppend.statusMachine
  BinaryListAppend.identityMachine BinaryListAppend.stripMachine BinaryListAppend.rawStemMachine
  BinaryListAppend.retainedMachine BinaryListAppend.payloadMachine BinaryListAppend.guardMachine
  BinaryListAppend.restoredBody BinaryListAppend.dispatchMachine
  FramedFieldSelection.machine FramedWordSuffixRemoval.machine StackMachineComposition.Dispatch.machine

attribute [local reducible] GraphAddressSequence.preparedMachine GraphAddressSequence.liftMachine
  GraphAddressAddition.machine GraphAddressAddition.projectedMachine GraphAddressAddition.digitMachine
  GraphAddressAddition.addedMachine GraphAddressAddition.preparedMachine GraphAddressAddition.mappedMachine
  GraphAddressAddition.bitMachine FramedWordMapping.machine FramedWordMapping.initial BinaryWordAddition.machine

variable {arity : Nat} (premiseCount internalCount : Nat) (block : GraphRelocationEmission.Block arity)
  (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
abbrev selected:=selectedMachine premiseCount internalCount block safe
local instance : Fintype ((selected premiseCount internalCount block safe).Γ (selected premiseCount internalCount block safe).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((selected premiseCount internalCount block safe).Γ (selected premiseCount internalCount block safe).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited ((selected premiseCount internalCount block safe).Γ (selected premiseCount internalCount block safe).k₁) := inferInstanceAs (Inhabited Alphabet)

abbrev core:=RetainedWordExecution.WithOutput.machine (selected premiseCount internalCount block safe)
abbrev tagged:=RetainedWordExecution.WithOutput.Framed.taggedMachine (selected premiseCount internalCount block safe)
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
abbrev retained:=retainedMachine premiseCount internalCount block safe
abbrev routed:=routedMachine premiseCount internalCount block safe
abbrev target:=RelocatedCertificateInsertion.machine premiseCount internalCount block safe

local instance : Fintype ((core premiseCount internalCount block safe).Γ (core premiseCount internalCount block safe).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))
local instance : Inhabited ((core premiseCount internalCount block safe).Γ (core premiseCount internalCount block safe).k₁) := ⟨(.inr (0 : Alphabet) : Option Alphabet ⊕ Alphabet)⟩
local instance : Fintype ((tagged premiseCount internalCount block safe).Γ (tagged premiseCount internalCount block safe).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((tagged premiseCount internalCount block safe).Γ (tagged premiseCount internalCount block safe).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype ((retained premiseCount internalCount block safe).Γ (retained premiseCount internalCount block safe).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((retained premiseCount internalCount block safe).Γ (retained premiseCount internalCount block safe).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype ((routed premiseCount internalCount block safe).Γ (routed premiseCount internalCount block safe).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((routed premiseCount internalCount block safe).Γ (routed premiseCount internalCount block safe).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

-- Selection tables retain their fixed compiled index order.
def selectionTable (width premises : Nat) :
    {instructions : (FramedFieldSelection.machine (Γ:=Alphabet) (selector width premises)).Λ →
      (FramedFieldSelection.machine (Γ:=Alphabet) (selector width premises)).Stmt //
      instructions=(FramedFieldSelection.machine (Γ:=Alphabet) (selector width premises)).m} := by
  extract_rule_program (FramedFieldSelection.machine (Γ:=Alphabet) (selector width premises)).m
def routeTable (width premises : Nat) :
    {instructions : (FramedFieldSelection.machine (Γ:=Alphabet) (route width premises)).Λ →
      (FramedFieldSelection.machine (Γ:=Alphabet) (route width premises)).Stmt //
      instructions=(FramedFieldSelection.machine (Γ:=Alphabet) (route width premises)).m} := by
  extract_rule_program (FramedFieldSelection.machine (Γ:=Alphabet) (route width premises)).m

def selectedBody (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt) : (selected premiseCount internalCount block safe).Λ → (selected premiseCount internalCount block safe).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FramedFieldSelection.machine (Γ:=Alphabet) (selector arity premiseCount)).k₁
    (GraphRelocationEmission.Program.inputKey premiseCount internalCount block safe)
    (GraphRelocationEmission.Program.mainLabel premiseCount internalCount block safe)
    (none : Option Alphabet) id (selectionTable arity premiseCount).val
    relocationCode)
theorem selectedBody_eq (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt)
    (relocationSame : relocationCode=(GraphRelocationEmission.machine premiseCount internalCount block safe).m) : selectedBody premiseCount internalCount block safe relocationCode=(selected premiseCount internalCount block safe).m := by
  unfold selectedBody
  rw [(selectionTable arity premiseCount).property,relocationSame]
  exact StackMachineComposition.body_eq (FramedFieldSelection.machine (Γ:=Alphabet) (selector arity premiseCount))
    (GraphRelocationEmission.machine premiseCount internalCount block safe) (Equiv.refl _)

def coreBody (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt) : (core premiseCount internalCount block safe).Λ → (core premiseCount internalCount block safe).Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (selected premiseCount internalCount block safe).k₀ (selected premiseCount internalCount block safe).k₁
    (none : Option Alphabet) (0 : Alphabet) (selected premiseCount internalCount block safe).initialState
    (selected premiseCount internalCount block safe).main (selectedBody premiseCount internalCount block safe relocationCode))
theorem coreBody_eq (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt)
    (relocationSame : relocationCode=(GraphRelocationEmission.machine premiseCount internalCount block safe).m) : coreBody premiseCount internalCount block safe relocationCode=(core premiseCount internalCount block safe).m := by
  unfold coreBody
  rw [selectedBody_eq premiseCount internalCount block safe relocationCode relocationSame]
  rfl
def untag : Option Alphabet ⊕ Alphabet → List (Option Alphabet) :=
  fun symbol => RetainedWordExecution.WithOutput.Framed.untag
    (selected premiseCount internalCount block safe) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) symbol
def taggedBody (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt) : (tagged premiseCount internalCount block safe).Λ → (tagged premiseCount internalCount block safe).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FirstAlphabet:=(core premiseCount internalCount block safe).Γ) none WordHomomorphismMachine.Stack.input .read
    (.inr (0 : Alphabet) : Option Alphabet ⊕ Alphabet) id (coreBody premiseCount internalCount block safe relocationCode)
    (WordHomomorphismMachine.program (untag premiseCount internalCount block safe)))
theorem taggedBody_eq (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt)
    (relocationSame : relocationCode=(GraphRelocationEmission.machine premiseCount internalCount block safe).m) : taggedBody premiseCount internalCount block safe relocationCode=(tagged premiseCount internalCount block safe).m := by
  unfold taggedBody
  rw [coreBody_eq premiseCount internalCount block safe relocationCode relocationSame]
  exact StackMachineComposition.body_eq (core premiseCount internalCount block safe)
    (WordHomomorphismMachine.machine (untag premiseCount internalCount block safe)) (Equiv.refl _)
def retainedBody (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt) : (retained premiseCount internalCount block safe).Λ → (retained premiseCount internalCount block safe).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FirstAlphabet:=(tagged premiseCount internalCount block safe).Γ) (tagged premiseCount internalCount block safe).k₁
    WordTemplateMachine.Stack.input (.emit ⟨0,by decide⟩) (none : Option Alphabet) id
    (taggedBody premiseCount internalCount block safe relocationCode)
    (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet))))
theorem retainedBody_eq (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt)
    (relocationSame : relocationCode=(GraphRelocationEmission.machine premiseCount internalCount block safe).m) : retainedBody premiseCount internalCount block safe relocationCode=(retained premiseCount internalCount block safe).m := by
  unfold retainedBody
  rw [taggedBody_eq premiseCount internalCount block safe relocationCode relocationSame]
  exact StackMachineComposition.body_eq (tagged premiseCount internalCount block safe)
    (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet))) (Equiv.refl _)
def routedBody (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt) : (routed premiseCount internalCount block safe).Λ → (routed premiseCount internalCount block safe).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (retained premiseCount internalCount block safe).k₁ (FramedFieldSelection.machine (Γ:=Alphabet) (route arity premiseCount)).k₀
    (FramedFieldSelection.machine (Γ:=Alphabet) (route arity premiseCount)).main
    (none : Option Alphabet) id (retainedBody premiseCount internalCount block safe relocationCode) (routeTable arity premiseCount).val)
theorem routedBody_eq (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt)
    (relocationSame : relocationCode=(GraphRelocationEmission.machine premiseCount internalCount block safe).m) : routedBody premiseCount internalCount block safe relocationCode=(routed premiseCount internalCount block safe).m := by
  unfold routedBody
  rw [retainedBody_eq premiseCount internalCount block safe relocationCode relocationSame,(routeTable arity premiseCount).property]
  exact StackMachineComposition.body_eq (retained premiseCount internalCount block safe)
    (FramedFieldSelection.machine (Γ:=Alphabet) (route arity premiseCount)) (Equiv.refl _)
def body (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt) : (target premiseCount internalCount block safe).Λ → (target premiseCount internalCount block safe).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body (routed premiseCount internalCount block safe).k₁
    EmittedCertificateInsertion.Program.inputKey EmittedCertificateInsertion.Program.mainLabel
    (none : Option Alphabet) id (routedBody premiseCount internalCount block safe relocationCode) EmittedCertificateInsertion.Program.body)
theorem body_eq (relocationCode : (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt)
    (relocationSame : relocationCode=(GraphRelocationEmission.machine premiseCount internalCount block safe).m) : body premiseCount internalCount block safe relocationCode=(target premiseCount internalCount block safe).m := by
  unfold body
  rw [routedBody_eq premiseCount internalCount block safe relocationCode relocationSame,EmittedCertificateInsertion.Program.body_eq]
  exact StackMachineComposition.body_eq (routed premiseCount internalCount block safe) EmittedCertificateInsertion.machine (Equiv.refl _)
def keyEquality : DecidableEq (target premiseCount internalCount block safe).K := by append_literal_equality
local instance : DecidableEq (target premiseCount internalCount block safe).K:=keyEquality premiseCount internalCount block safe
def registerEquality : DecidableEq (target premiseCount internalCount block safe).σ := by append_literal_equality
open Lean Elab Tactic Meta in
private partial def structuralLabelEquality (type : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf type)
  match type.getAppFn.constName?,type.getAppArgs.toList with
  | some ``Option,[inner] => mkAppOptM ``Option.instDecidableEq #[some inner,some (← structuralLabelEquality inner)]
  | some ``Sum,[left,right] => mkAppOptM ``instDecidableEqSum #[some left,some right,
      some (← structuralLabelEquality left),some (← structuralLabelEquality right)]
  | some ``Prod,[left,right] => mkAppOptM `instDecidableEqProd #[some left,some right,
      some (← structuralLabelEquality left),some (← structuralLabelEquality right)]
  | some ``RetainedWordExecution.WithOutput.Phase,[inner] =>
    mkAppOptM ``RetainedWordExecution.WithOutput.instDecidableEqPhase #[some inner,some (← structuralLabelEquality inner)]
  | some ``RetainedWordExecution.Phase,[inner] =>
    mkAppOptM ``RetainedWordExecution.instDecidableEqPhase #[some inner,some (← structuralLabelEquality inner)]
  | some ``StackMachineComposition.Dispatch.Phase,[inner] =>
    mkAppOptM ``StackMachineComposition.Dispatch.instDecidableEqPhase #[some inner,some (← structuralLabelEquality inner)]
  | some ``FramedWordMapping.Phase,[inner] =>
    mkAppOptM ``FramedWordMapping.instDecidableEqPhase #[some inner,some (← structuralLabelEquality inner)]
  | some ``WordHomomorphismMachine.Phase,[capacity] =>
    let capacity ← withTransparency .all (reduce capacity false false true)
    mkAppOptM ``WordHomomorphismMachine.instDecidableEqPhase #[some capacity]
  | _,_ => synthInstance (← mkAppM ``DecidableEq #[type])
open Lean Elab Tactic Meta in
elab "insertion_label_equality" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    goal.assign (← structuralLabelEquality (← goal.getType).getAppArgs.back!)
  replaceMainGoal []
def labelEquality : DecidableEq (target premiseCount internalCount block safe).Λ := by insertion_label_equality

def inputKey : (target premiseCount internalCount block safe).K := by normalize_rule_program (target premiseCount internalCount block safe).k₀
def outputKey : (target premiseCount internalCount block safe).K := by normalize_rule_program (target premiseCount internalCount block safe).k₁
def registers : (target premiseCount internalCount block safe).σ := by normalize_rule_program (target premiseCount internalCount block safe).initialState
def mainLabel : (target premiseCount internalCount block safe).Λ := by normalize_rule_program (target premiseCount internalCount block safe).main
abbrev Key : Type := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let expression ← Lean.Elab.Term.elabTerm (← `(term| (target premiseCount internalCount block safe).K)) (some (← goal.getType))
    goal.assign (← Lean.Meta.withTransparency .all (Lean.Meta.reduce expression false false true))
def fixedKeys : List Key := by claim_program_keys
open Lean Elab Tactic Meta in
private partial def structuralKeyFiniteness (type : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf type)
  match type.getAppFn.constName?,type.getAppArgs.toList with
  | some ``Option,[inner] => mkAppOptM ``instFintypeOption #[some inner,some (← structuralKeyFiniteness inner)]
  | some ``Sum,[left,right] => mkAppOptM ``instFintypeSum #[some left,some right,
      some (← structuralKeyFiniteness left),some (← structuralKeyFiniteness right)]
  | _,_ => synthInstance (← mkAppM ``Fintype #[type])
@[instance_reducible] noncomputable def keyFinite : Fintype Key := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← structuralKeyFiniteness (← goal.getType).getAppArgs.back!)

def keys : List (target premiseCount internalCount block safe).K := fixedKeys
local instance : BEq (target premiseCount internalCount block safe).K:=⟨fun a b=>decide (a=b)⟩
local instance : LawfulBEq (target premiseCount internalCount block safe).K where
  eq_of_beq h:=of_decide_eq_true h
  rfl:=by intro a; exact decide_eq_true rfl
noncomputable local instance : Fintype (target premiseCount internalCount block safe).K:=(target premiseCount internalCount block safe).kFin
local instance : DecidableEq Key:=by append_literal_equality
noncomputable local instance : Fintype Key:=keyFinite
theorem all_keys : ∀ key : (target premiseCount internalCount block safe).K,key∈keys premiseCount internalCount block safe := by
  change ∀ key : Key,key∈fixedKeys
  decide +kernel

def relocationBody (length : Nat)
    (same : length=(GraphRelocationEmission.template premiseCount internalCount block safe).length)
    (instructions : Array (Alphabet ⊕ Fin ((arity+premiseCount+1)+internalCount))) :
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Λ →
    (GraphRelocationEmission.machine premiseCount internalCount block safe).Stmt :=
  cast (by rw [same]; rfl)
    (StackMachineComposition.Programs.body (GraphRelocationEmission.Program.preparedResult arity premiseCount internalCount)
      Indexed.Stack.input (.emit ⟨0,by omega⟩) (none : Option Alphabet) id
      (GraphRelocationEmission.Program.prepared arity premiseCount internalCount)
      (Indexed.arrayProgram length instructions))
theorem relocationBody_eq (length : Nat)
    (same : length=(GraphRelocationEmission.template premiseCount internalCount block safe).length) :
    relocationBody premiseCount internalCount block safe length same
      (GraphRelocationEmission.template premiseCount internalCount block safe).toArray =
      (GraphRelocationEmission.machine premiseCount internalCount block safe).m := by
  subst length
  exact GraphRelocationEmission.Program.body_eq premiseCount internalCount block safe

abbrev SelectionLabels (width length : Nat) :=
  WordHomomorphismMachine.Phase 6 ⊕ Bool ⊕ Indexed.Phase width length
abbrev SequenceLabels (sequenceLength : Nat) :=
  (GraphAddressSequence.liftMachine.Λ ⊕ Bool ⊕ WordTemplateMachine.Phase sequenceLength) ⊕
    Bool ⊕ GraphAddressSequence.mappedMachine.Λ
abbrev GraphLabels (width premises internal length sequenceLength : Nat) :=
  ((RetainedWordExecution.WithOutput.Phase
    (Indexed.Phase (width+premises+1) 1 ⊕ Bool ⊕ SequenceLabels sequenceLength) ⊕
      Bool ⊕ WordHomomorphismMachine.Phase 12) ⊕
    Bool ⊕ Indexed.Phase ((width+premises+1)+internal) length)
abbrev SelectedLabels (width premises internal length sequenceLength : Nat) :=
  SelectionLabels ((width+premises+1)+1) (2*(width+premises+1)) ⊕ Bool ⊕
    GraphLabels width premises internal length sequenceLength
abbrev RetainedLabels (width premises internal length sequenceLength : Nat) :=
  (RetainedWordExecution.WithOutput.Phase (SelectedLabels width premises internal length sequenceLength) ⊕
    Bool ⊕ WordHomomorphismMachine.Phase 11) ⊕ Bool ⊕
      WordTemplateMachine.Phase (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet)).length
abbrev WholeLabels (width premises internal length sequenceLength : Nat) :=
  (RetainedLabels width premises internal length sequenceLength ⊕ Bool ⊕
    SelectionLabels (((width+premises+1)+1)+1) 4) ⊕ Bool ⊕ EmittedCertificateInsertion.Program.target.Λ

def cachedLabelEquality (length sequenceLength : Nat)
    (same : length=(GraphRelocationEmission.template premiseCount internalCount block safe).length)
    (sequenceSame : sequenceLength=(GraphAddressSequence.plan (GraphRelocationEmission.offsets internalCount)).length) :
    DecidableEq (target premiseCount internalCount block safe).Λ := by
  have selectorLength : (FramedFieldSelection.template (Γ:=Alphabet) (selector arity premiseCount)).length=2*(arity+premiseCount+1) := by
    rw [FramedFieldSelection.template_length]
    simp [selector]
  have routeLength : (FramedFieldSelection.template (Γ:=Alphabet) (route arity premiseCount)).length=4 := by
    rw [FramedFieldSelection.template_length]
    rfl
  have labels : WholeLabels arity premiseCount internalCount length sequenceLength=
      (target premiseCount internalCount block safe).Λ := by
    rw [same,sequenceSame]
    simp only [WholeLabels,RetainedLabels,SelectedLabels,GraphLabels,SelectionLabels,SequenceLabels]
    rw [← selectorLength,← routeLength]
    rfl
  exact cast (congrArg DecidableEq labels)
    (show DecidableEq (WholeLabels arity premiseCount internalCount length sequenceLength) from by insertion_label_equality)

def program : PhysicalInstructionAdapter.Program (target premiseCount internalCount block safe) where
  body:=body premiseCount internalCount block safe (GraphRelocationEmission.Program.body premiseCount internalCount block safe)
  body_eq:=body_eq premiseCount internalCount block safe _ (GraphRelocationEmission.Program.body_eq premiseCount internalCount block safe)
  keyEquality:=keyEquality premiseCount internalCount block safe
  labelEquality:=labelEquality premiseCount internalCount block safe
  registerEquality:=registerEquality premiseCount internalCount block safe
  inputKey:=inputKey premiseCount internalCount block safe
  input_eq:=by rfl
  outputKey:=outputKey premiseCount internalCount block safe
  output_eq:=by rfl
  registers:=registers premiseCount internalCount block safe
  registers_eq:=by rfl
  mainLabel:=mainLabel premiseCount internalCount block safe
  main_eq:=by rfl
  keys:=keys premiseCount internalCount block safe
  all_keys:=all_keys premiseCount internalCount block safe

def preparedProgram : PhysicalInstructionAdapter.Program (target premiseCount internalCount block safe) :=
  let instructions:=(GraphRelocationEmission.template premiseCount internalCount block safe).toArray
  let length:=instructions.size
  let same : length=(GraphRelocationEmission.template premiseCount internalCount block safe).length := List.size_toArray
  let sequenceLength:=(GraphAddressSequence.plan (GraphRelocationEmission.offsets internalCount)).length
  { program premiseCount internalCount block safe with
    body:=body premiseCount internalCount block safe
      (relocationBody premiseCount internalCount block safe length same instructions)
    body_eq:=body_eq premiseCount internalCount block safe _
      (relocationBody_eq premiseCount internalCount block safe length same)
    labelEquality:=cachedLabelEquality premiseCount internalCount block safe length sequenceLength same rfl }

theorem completed_exact (receipts : List Mettapedia.Languages.HOLLight.ProofExecution.Receipt)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat)
    (earlier : List Mettapedia.Languages.HOLLight.ProofExecution.Receipt) (aligned : Aligned block receipts payload)
    (period fuel : Nat) {count : Nat} {after : (target premiseCount internalCount block safe).Cfg}
    (completed : PhysicalInstructionAdapter.counted (program premiseCount internalCount block safe) period fuel 0 none
      (PhysicalInstructionAdapter.initial (program premiseCount internalCount block safe)
        (inputWire payload roots base earlier))=some (count,after)) :
    after=haltList (target premiseCount internalCount block safe)
      (Mettapedia.Languages.HOLLight.ProofDataEncoding.encodeCertificate
        (earlier++(GraphExpansion.expandBlock (List.ofFn roots) base (receipts,block.2)).1,
          (GraphExpansion.expandBlock (List.ofFn roots) base (receipts,block.2)).2)) ∧
      count≤coefficient premiseCount internalCount block safe*((inputWire payload roots base earlier).length+1) :=
  PhysicalInstructionAdapter.completed_original (program premiseCount internalCount block safe) _ _ _
    (RelocatedCertificateInsertion.outputs internalCount block safe receipts payload roots base earlier aligned)
    period fuel completed
theorem prepared_completed_exact (receipts : List Mettapedia.Languages.HOLLight.ProofExecution.Receipt)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat)
    (earlier : List Mettapedia.Languages.HOLLight.ProofExecution.Receipt) (aligned : Aligned block receipts payload)
    (period fuel : Nat) {count : Nat} {after : (target premiseCount internalCount block safe).Cfg}
    (completed : PhysicalInstructionAdapter.counted (preparedProgram premiseCount internalCount block safe) period fuel 0 none
      (PhysicalInstructionAdapter.initial (preparedProgram premiseCount internalCount block safe)
        (inputWire payload roots base earlier))=some (count,after)) :
    after=haltList (target premiseCount internalCount block safe)
      (Mettapedia.Languages.HOLLight.ProofDataEncoding.encodeCertificate
        (earlier++(GraphExpansion.expandBlock (List.ofFn roots) base (receipts,block.2)).1,
          (GraphExpansion.expandBlock (List.ofFn roots) base (receipts,block.2)).2)) ∧
      count≤coefficient premiseCount internalCount block safe*((inputWire payload roots base earlier).length+1) :=
  PhysicalInstructionAdapter.completed_original (preparedProgram premiseCount internalCount block safe) _ _ _
    (RelocatedCertificateInsertion.outputs internalCount block safe receipts payload roots base earlier aligned)
    period fuel completed
end Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion.Program
