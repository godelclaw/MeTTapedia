import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT

/-!
# A fault keeps what happened before it

PeTTa and CeTTa abort a run at its first fault. Output printed before the fault
has already reached the terminal, and cells changed before it stay changed. The
model's fault outcome therefore keeps the configuration in which the fault
occurred. This is the failure semantics of this profile: abort, keeping every
effect performed so far. A profile that restores its store on a fault, as an
RSpace checkpoint does on an injection error, has a different failure semantics
and would declare it.

`fault_keeps_effects` states the law for every run: the faulted configuration's
output extends the starting output, and the starting input extends what remains.

The controls run one program that prints, changes a cell and then reads a
missing cell, and another that only reads the missing cell. Both fault for the
same reason. The first keeps the printed atom and the changed cell, the second
keeps neither, so the two outcomes differ.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.FaultObservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval
open SpaceSemantics (Program)

/-- Along a run that faults, output only grows and input is consumed in order. -/
theorem fault_keeps_effects (program : Program) (fuel : Nat) (source : Configuration)
    (reason : Effects.Fault) (faulted : Configuration)
    (computed : run program fuel source = .fault reason faulted) :
    (∃ added, faulted.output = source.output ++ added) ∧
      (∃ consumed, source.input = consumed ++ faulted.input) := by
  induction fuel generalizing source with
  | zero =>
    unfold run at computed
    split at computed
    · cases computed
    · cases computed
      exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
    · cases computed
  | succ fuel ih =>
    unfold run at computed
    split at computed
    · cases computed
    · cases computed
      exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
    · cases stepped : step program source with
      | none => simp [stepped] at computed
      | some next =>
        simp only [stepped] at computed
        obtain ⟨⟨added, output⟩, ⟨consumed, input⟩⟩ := ih next computed
        obtain ⟨first, firstOutput⟩ :=
          OperationalGSLT.output_extends program source next stepped
        obtain ⟨firstConsumed, firstInput⟩ :=
          OperationalGSLT.input_is_consumed_in_order program source next stepped
        exact ⟨⟨first ++ added, by rw [output, firstOutput, List.append_assoc]⟩,
          ⟨firstConsumed ++ consumed, by rw [firstInput, input, List.append_assoc]⟩⟩

/-! ## Controls -/

def program : Program := { equations := [], declarations := [] }

private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

/-- Reading a cell that was never set faults. -/
def failing : Atom := call "get-state" [.symbol "missing"]

/-- Prints, changes a cell, then faults on the missing cell. -/
def effectful : Atom := call "superpose" [.expression [
  call "println!" [.symbol "message"],
  call "change-state!" [.symbol "changed", .symbol "value"], failing]]

/-- The output kept by a fault, and nothing otherwise. -/
def faultOutput : Outcome → List Atom
  | .fault _ faulted => faulted.output
  | _ => []

/-- The cell `changed` in the store kept by a fault. -/
def faultCell : Outcome → Option Atom
  | .fault _ faulted => faulted.state.cells "changed"
  | _ => none

def faultReason : Outcome → Option Effects.Fault
  | .fault reason _ => some reason
  | _ => none

theorem effectful_fault_reason :
    faultReason (run program 100 (start Effects.empty effectful)) =
      some (.missingCell "missing") := by
  rfl

theorem failing_fault_reason :
    faultReason (run program 100 (start Effects.empty failing)) =
      some (.missingCell "missing") := by
  rfl

/-- Positive control: the effectful fault keeps the printed atom. -/
theorem effectful_fault_keeps_output :
    faultOutput (run program 100 (start Effects.empty effectful)) = [.symbol "message"] := by
  rfl

/-- Positive control: the effectful fault keeps the changed cell. -/
theorem effectful_fault_keeps_cell :
    faultCell (run program 100 (start Effects.empty effectful)) = some (.symbol "value") := by
  rfl

/-- The immediate fault has printed nothing. -/
theorem failing_fault_output :
    faultOutput (run program 100 (start Effects.empty failing)) = [] := by
  rfl

/-- Negative control: two faults with the same reason are different outcomes when
different effects preceded them. -/
theorem effectful_fault_differs :
    run program 100 (start Effects.empty effectful) ≠
      run program 100 (start Effects.empty failing) := by
  intro same
  have outputs := congrArg faultOutput same
  rw [effectful_fault_keeps_output, failing_fault_output] at outputs
  exact List.cons_ne_nil _ _ outputs

end Mettapedia.Languages.MeTTa.PeTTa.FaultObservation
