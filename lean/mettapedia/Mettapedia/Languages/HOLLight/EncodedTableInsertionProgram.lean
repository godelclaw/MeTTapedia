import Mettapedia.Languages.HOLLight.EncodedTableInsertion
import Mettapedia.Languages.HOLLight.ChronologicalInsertionProgram
/-!
# Physical original-codec cache insertion instructions

The table executes the original index projection and triple encoding of every value byte, then runs the original resolver-table append. The completion theorem earns the exact canonical halted state.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.EncodedTableInsertion.Program
open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open Mettapedia.Languages.HOLLight.EncodedTableInsertion
attribute [local reducible] EncodedTableInsertion.machine routed projections retainedValue valueProjection
  SavedRootInsertion.retainedProjection SavedRootInsertion.projection SavedRootInsertion.bitProjection SavedRootInsertion.selectTemplate
  GraphAddressAddition.bitMachine GraphAddressAddition.digitMachine
  StackMachineComposition.machine StackMachineComposition.leftKey StackMachineComposition.rightKey
  WordHomomorphismMachine.machine WordTemplateMachine.machine Indexed.machine FramedFieldSelection.machine
  RetainedWordExecution.WithOutput.machine RetainedWordExecution.WithOutput.Framed.machine
  RetainedWordExecution.WithOutput.Framed.taggedMachine RetainedWordExecution.WithOutput.Framed.untag
  TableAppend.machine
abbrev target:=EncodedTableInsertion.machine
def table : {instructions : target.Λ → target.Stmt // instructions=target.m} := by
  extract_rule_program target.m
def body:=table.val
theorem body_eq : body=target.m := table.property

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

theorem completed_exact {A : Type} (codec : Mettapedia.OSLF.Binding.WireCodec.Codec A)
    (values : Array A) (next : A) (period fuel : Nat)
    {count : Nat} {after : target.Cfg}
    (completed : PhysicalInstructionAdapter.counted program period fuel 0 none
      (PhysicalInstructionAdapter.initial program (inputWire codec values next))=some (count,after)) :
    after=haltList target (Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.table (EncodedTable.rows codec (values.push next))) ∧
      count≤768*((inputWire codec values next).length+1) :=
  PhysicalInstructionAdapter.completed_original program _ _ _ (EncodedTableInsertion.outputs codec values next)
    period fuel completed
end Mettapedia.Languages.HOLLight.EncodedTableInsertion.Program
