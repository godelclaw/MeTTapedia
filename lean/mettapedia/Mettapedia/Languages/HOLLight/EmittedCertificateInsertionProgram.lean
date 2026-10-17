import Mettapedia.Languages.HOLLight.EmittedCertificateInsertion
import Mettapedia.Languages.HOLLight.ChronologicalInsertionProgram
/-!
# Original certificate parsing through physical instructions

The physical table projects the original receipt list and selected root, then runs the original chronological insertion table. Exact completion includes the original halted configuration and clock.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.EmittedCertificateInsertion.Program
open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
open Mettapedia.Languages.HOLLight.EmittedCertificateInsertion
open Mettapedia.GSLT.LanguageDef
attribute [local reducible] EmittedCertificateInsertion.machine routedMachine parsedPacketMachine
  firstMachine secondMachine componentMachine parsedMachine componentPlan
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

def fieldBody (second : Bool) : (CertificateDataTraversal.ProductField.machine second).Λ →
    (CertificateDataTraversal.ProductField.machine second).Stmt :=
  if second then ClaimCheckingProgram.secondFieldBody else ClaimCheckingProgram.firstFieldBody

theorem fieldBody_eq (second : Bool) : fieldBody second=(CertificateDataTraversal.ProductField.machine second).m := by
  cases second
  · exact ClaimCheckingProgram.firstFieldBody_exact
  · exact ClaimCheckingProgram.secondFieldBody_exact

local instance {arity : Nat} (index : Fin arity) : Fintype ((Indexed.machine (componentPlan index)).Γ (Indexed.machine (componentPlan index)).k₁) := inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) : Inhabited ((Indexed.machine (componentPlan index)).Γ (Indexed.machine (componentPlan index)).k₁) := inferInstanceAs (Inhabited Alphabet)
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Fintype ((parsedMachine index second).Γ (parsedMachine index second).k₁) := inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Inhabited ((parsedMachine index second).Γ (parsedMachine index second).k₁) := inferInstanceAs (Inhabited Alphabet)
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Fintype ((componentMachine index second).Γ (componentMachine index second).k₁) := inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Inhabited ((componentMachine index second).Γ (componentMachine index second).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Inhabited ((componentMachine index second).Γ (componentMachine index second).k₁) := inferInstanceAs (Inhabited Alphabet)

def parsedBody {arity : Nat} (index : Fin arity) (second : Bool) : (parsedMachine index second).Λ → (parsedMachine index second).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body Indexed.Stack.result
    (CertificateDataTraversal.ProductField.machine second).k₀ (CertificateDataTraversal.ProductField.machine second).main
    (0 : Alphabet) id (Indexed.arrayProgram (componentPlan index).length (componentPlan index).toArray) (fieldBody second))

theorem parsedBody_eq {arity : Nat} (index : Fin arity) (second : Bool) : parsedBody index second=(parsedMachine index second).m := by
  unfold parsedBody
  rw [Indexed.arrayProgram_eq_program,fieldBody_eq]
  exact StackMachineComposition.body_eq (Indexed.machine (componentPlan index)) (CertificateDataTraversal.ProductField.machine second) (Equiv.refl _)

def componentBody {arity : Nat} (index : Fin arity) (second : Bool) : (componentMachine index second).Λ → (componentMachine index second).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body (parsedMachine index second).k₁
    BinaryListAppend.stripMachine.k₀ BinaryListAppend.stripMachine.main (0 : Alphabet) id (parsedBody index second) BinaryListAppend.Program.stripBody)

theorem componentBody_eq {arity : Nat} (index : Fin arity) (second : Bool) : componentBody index second=(componentMachine index second).m := by
  unfold componentBody
  rw [parsedBody_eq,BinaryListAppend.Program.stripBody_eq]
  exact StackMachineComposition.body_eq (parsedMachine index second) BinaryListAppend.stripMachine (Equiv.refl _)

abbrev core {arity : Nat} (index : Fin arity) (second : Bool) := RetainedWordExecution.WithOutput.machine (componentMachine index second)
abbrev tagged {arity : Nat} (index : Fin arity) (second : Bool) := RetainedWordExecution.WithOutput.Framed.taggedMachine (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Fintype ((core index second).Γ (core index second).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Inhabited ((core index second).Γ (core index second).k₁) := ⟨.inr 0⟩
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Fintype ((tagged index second).Γ (tagged index second).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Inhabited ((tagged index second).Γ (tagged index second).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def coreBody {arity : Nat} (index : Fin arity) (second : Bool) : (core index second).Λ → (core index second).Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement (componentMachine index second).k₀
    (componentMachine index second).k₁ (none : Option Alphabet) (0 : Alphabet)
    (componentMachine index second).initialState (componentMachine index second).main (componentBody index second))
theorem coreBody_eq {arity : Nat} (index : Fin arity) (second : Bool) : coreBody index second=(core index second).m := by
  unfold coreBody
  rw [componentBody_eq]
  rfl

abbrev untag {arity : Nat} (index : Fin arity) (second : Bool) := RetainedWordExecution.WithOutput.Framed.untag (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
def taggedBody {arity : Nat} (index : Fin arity) (second : Bool) : (tagged index second).Λ → (tagged index second).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body (FirstAlphabet:=(core index second).Γ)
    none WordHomomorphismMachine.Stack.input .read (.inr (0 : Alphabet) : Option Alphabet ⊕ Alphabet) id
    (coreBody index second) (WordHomomorphismMachine.program (untag index second)))
theorem taggedBody_eq {arity : Nat} (index : Fin arity) (second : Bool) : taggedBody index second=(tagged index second).m := by
  unfold taggedBody
  rw [coreBody_eq]
  exact StackMachineComposition.body_eq (core index second) (WordHomomorphismMachine.machine (untag index second)) (Equiv.refl _)

local instance {arity : Nat} (index : Fin arity) (second : Bool) : Fintype ((RetainedWordExecution.WithOutput.Framed.machine (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.machine (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) (second : Bool) : Inhabited ((RetainedWordExecution.WithOutput.Framed.machine (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.machine (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def framedBody {arity : Nat} (index : Fin arity) (second : Bool) :
    (RetainedWordExecution.WithOutput.Framed.machine (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Λ →
    (RetainedWordExecution.WithOutput.Framed.machine (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body (FirstAlphabet:=(tagged index second).Γ)
    (tagged index second).k₁ WordTemplateMachine.Stack.input (.emit ⟨0,by decide⟩) (none : Option Alphabet) id
    (taggedBody index second) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet))))
theorem framedBody_eq {arity : Nat} (index : Fin arity) (second : Bool) : framedBody index second=
    (RetainedWordExecution.WithOutput.Framed.machine (componentMachine index second) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).m := by
  unfold framedBody
  rw [taggedBody_eq]
  exact StackMachineComposition.body_eq (tagged index second)
    (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet))) (Equiv.refl _)

local instance : Fintype (firstMachine.Γ firstMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (firstMachine.Γ firstMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (secondMachine.Γ secondMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (secondMachine.Γ secondMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (parsedPacketMachine.Γ parsedPacketMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (parsedPacketMachine.Γ parsedPacketMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (routedMachine.Γ routedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (routedMachine.Γ routedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def packetBody : parsedPacketMachine.Λ → parsedPacketMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body firstMachine.k₁ secondMachine.k₀ secondMachine.main
    (none : Option Alphabet) id (framedBody (1 : Fin 2) false) (framedBody (1 : Fin 3) true))
theorem packetBody_eq : packetBody=parsedPacketMachine.m := by
  unfold packetBody
  rw [framedBody_eq,framedBody_eq]
  exact StackMachineComposition.body_eq firstMachine secondMachine (Equiv.refl _)

def selectedTable : {instructions : (FramedFieldSelection.machine (Γ:=Alphabet) route).Λ → (FramedFieldSelection.machine (Γ:=Alphabet) route).Stmt // instructions=(FramedFieldSelection.machine (Γ:=Alphabet) route).m} := by
  extract_rule_program (FramedFieldSelection.machine (Γ:=Alphabet) route).m
def selectedBody:=selectedTable.val

def routedBody : routedMachine.Λ → routedMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body parsedPacketMachine.k₁
    (FramedFieldSelection.machine (Γ:=Alphabet) route).k₀ (FramedFieldSelection.machine (Γ:=Alphabet) route).main
    (none : Option Alphabet) id packetBody selectedBody)
theorem routedBody_eq : routedBody=routedMachine.m := by
  unfold routedBody
  rw [packetBody_eq,show selectedBody=(FramedFieldSelection.machine (Γ:=Alphabet) route).m from selectedTable.property]
  exact StackMachineComposition.body_eq parsedPacketMachine (FramedFieldSelection.machine (Γ:=Alphabet) route) (Equiv.refl _)

abbrev target:=EmittedCertificateInsertion.machine
def body : target.Λ → target.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body routedMachine.k₁ ChronologicalInsertion.Program.inputKey
    ChronologicalInsertion.Program.mainLabel (none : Option Alphabet) id routedBody ChronologicalInsertion.Program.body)
theorem body_eq : body=target.m := by
  unfold body
  rw [routedBody_eq,ChronologicalInsertion.Program.body_eq]
  exact StackMachineComposition.body_eq routedMachine ChronologicalInsertion.machine (Equiv.refl _)

def keyEquality : DecidableEq target.K := by append_literal_equality
local instance : DecidableEq target.K:=keyEquality
def registerEquality : DecidableEq target.σ := by append_literal_equality
def labelEquality : DecidableEq target.Λ := by append_literal_equality
def inputKey : target.K := by normalize_rule_program target.k₀
def outputKey : target.K := by normalize_rule_program target.k₁
def registers : target.σ := by normalize_rule_program target.initialState
def mainLabel : target.Λ := by normalize_rule_program target.main
def keys : List target.K := by claim_program_keys
local instance : BEq target.K:=⟨fun a b=>decide (a=b)⟩
local instance : LawfulBEq target.K where
  eq_of_beq h:=of_decide_eq_true h
  rfl:=by intro a; exact decide_eq_true rfl
noncomputable local instance : Fintype target.K:=target.kFin
theorem all_keys : ∀ key : target.K,key∈keys := by decide +kernel

def program : PhysicalInstructionAdapter.Program target where
  body:=body
  body_eq:=body_eq
  keyEquality:=keyEquality
  labelEquality:=labelEquality
  registerEquality:=registerEquality
  inputKey:=inputKey
  input_eq:=by rfl
  outputKey:=outputKey
  output_eq:=by rfl
  registers:=registers
  registers_eq:=by rfl
  mainLabel:=mainLabel
  main_eq:=by rfl
  keys:=keys
  all_keys:=all_keys

theorem completed_exact (earlier : List ProofExecution.Receipt) (block : ProofSystem.Certificate) (period fuel : Nat)
    {count : Nat} {after : target.Cfg}
    (completed : PhysicalInstructionAdapter.counted program period fuel 0 none
      (PhysicalInstructionAdapter.initial program (inputWire earlier block))=some (count,after)) :
    after=haltList target (ProofDataEncoding.encodeCertificate (earlier++block.1,block.2)) ∧
      count≤850*((inputWire earlier block).length+1) :=
  PhysicalInstructionAdapter.completed_original program _ _ _ (EmittedCertificateInsertion.outputs earlier block)
    period fuel completed
end Mettapedia.Languages.HOLLight.EmittedCertificateInsertion.Program
