import Mettapedia.Machines.CMemory.ProductiveBlocks
import Mettapedia.Machines.CMemory.Values

/-!
# Primitive memory trace, resumption and allocator-request controls

A write/read/free program pauses with its changed memory and precise
continuation. Its resumed trace omits the established write. Resetting the
saved memory instead faults at the read. A refused allocator identity asks
for another choice without a memory effect, whereas a repeated free stops
with the complete fault state.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ProductiveBlocks.Controls

open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage

def address : Ptr := ⟨3, 0⟩
def initialStorage : Storage CVal := [(3, ⟨true, [none]⟩)]
def written : Storage CVal := put initialStorage 3 ⟨true, [some (.u32 9)]⟩
def retired : Storage CVal := put written 3 ⟨false, [some (.u32 9)]⟩

def afterWrite : CProg CVal CVal := do
  let value ← CProg.load address
  CProg.free (some address)
  pure value

def program : CProg CVal CVal := do
  CProg.store address (.u32 9)
  afterWrite

def initial : State CVal CVal := ⟨program, initialStorage, []⟩
def saved : State CVal CVal := ⟨afterWrite, written, []⟩
def final : Finished CVal CVal := ⟨.u32 9, retired, []⟩

def writeReceipt : Receipt CVal := ⟨.store address (.u32 9), (), initialStorage, written⟩
def readReceipt : Receipt CVal := ⟨.load address, .u32 9, written, written⟩
def freeReceipt : Receipt CVal := ⟨.free (some address), (), written, retired⟩

theorem pause_retains_changed_memory :
    machine.run 1 initial = ([writeReceipt], .exhausted saved) := rfl

theorem complete_trace :
    machine.run 4 initial =
      ([writeReceipt, readReceipt, freeReceipt], .finished (.returned final)) := rfl

theorem resumed_trace_does_not_repeat_write :
    (machine.run 3 saved).1 = [readReceipt, freeReceipt] := rfl

theorem prefix_resumption_keeps_all_endpoints :
    machine.run 4 initial =
      ([writeReceipt] ++ (machine.run 3 saved).1, (machine.run 3 saved).2) :=
  resume_after_prefix 1 3 initial saved [writeReceipt] pause_retains_changed_memory

theorem source_program_has_the_same_result_and_heap :
    program.Runs (act (L := Mettapedia.GSLT.SeparationAlgebra.Excl (Option CVal)))
      (heap initialStorage) (.u32 9) (heap retired) :=
  returned_sound 4 initial final (congrArg Prod.snd complete_trace)

theorem each_receipt_has_memory_authority :
    ∀ receipt ∈ (machine.run 4 initial).1, ValidReceipt receipt :=
  run_receipts_valid 4 initial

theorem three_memory_operations_have_three_charges :
    machine.spent price 4 initial = 3 := rfl

theorem reset_saved_memory_faults_at_the_pending_read :
    (machine.run 3 (State.mk afterWrite initialStorage [])).2 =
      .finished (.fault ⟨afterWrite, initialStorage, []⟩) := rfl

theorem restarting_delivers_the_write_again :
    (machine.run 1 initial).1 = [writeReceipt] ∧ (machine.run 1 saved).1 = [readReceipt] := by
  constructor <;> rfl

def allocationProgram : CProg CVal (Option Ptr) := CProg.malloc 1
def refusedAllocation : State CVal (Option Ptr) :=
  ⟨allocationProgram, initialStorage, [.fresh 3, .fresh 4]⟩
def retryAllocation : State CVal (Option Ptr) :=
  ⟨allocationProgram, initialStorage, [.fresh 4]⟩

theorem occupied_identity_is_a_request_not_a_memory_effect :
    machine.run 1 refusedAllocation =
      ([], .suspended ⟨.malloc 1, .fresh 3⟩ retryAllocation) := rfl

theorem valid_allocator_reply_continues_the_saved_program :
    machine.run 2 retryAllocation =
      ([⟨.malloc 1, some ⟨4, 0⟩, initialStorage,
        put initialStorage 4 ⟨true, [none]⟩⟩],
        .finished (.returned ⟨some ⟨4, 0⟩,
          put initialStorage 4 ⟨true, [none]⟩, []⟩)) := rfl

def doubleFree : CProg CVal Unit := do
  CProg.free (some address)
  CProg.free (some address)

theorem repeated_free_keeps_the_fault_state :
    (machine.run 2 (State.mk doubleFree initialStorage [])).2 =
      .finished (.fault
        ⟨CProg.free (some address), put initialStorage 3 ⟨false, [none]⟩, []⟩) := rfl

end Mettapedia.Machines.CMemory.ProductiveBlocks.Controls
