import Mettapedia.GSLT.LanguageDef.OperationCostProtocol

/-! Executable positive and negative controls for the native-invoice cursor.
These use state changes, failures, suspension and unbounded zero-work stepping;
none treat a finite inspection allowance as a termination proof. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OperationCostProtocolControls

open Mettapedia.GSLT.LanguageDef.OperationCostProtocol
open Mettapedia.GSLT.LanguageDef.OperationContracts
open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)

def sampleRecord (progress replay : String) (bound : Atom) (kinds : List Atom) : Atom :=
  .list [.symbol "cesta-operation-protocol/1", .symbol "sample",
    .list (.symbol "ChargeKinds" :: kinds),
    .list [.symbol "Progress", .text progress, .list [.symbol "Bound", bound]],
    .list [.symbol "Replay", .text replay]]

theorem source_record_admitted : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "single" "refused" (.symbol "1") []) = true := by decide

theorem single_bound_cannot_be_unknown : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "single" "refused" (.text "unknown") []) = false := by decide

theorem source_labels_must_match : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "single" "refused" (.symbol "1")
      [.list [.symbol "not-declared", .symbol "analysisStep"]]) = false := by decide

theorem source_progress_must_match : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "steps" "refused" (.text "unknown") []) = false := by decide

theorem source_replay_must_match : admitted
    (exampleOperation "sample" "sample" (footprintAtom [] []) "yes" "no")
    (sampleRecord "single" "transparent" (.symbol "1") []) = false := by decide

def metered : Profile :=
  ⟨"sample", [("step", some .analysisStep)], .steps, none, .transparent⟩

def receipt (identity units : Nat) : Event :=
  (identity, ⟨0, identity, .analysisStep, units⟩)

def invoice (_ : Bool) (world : Nat) : List Event := [receipt world 2]

def tick (_ : Bool) (world : Nat) : Reply Nat String String × Nat := (.paid, world + 1)

def fail (_ : Bool) (world : Nat) : Reply Nat String String × Nat :=
  (.terminal (.fault "allocation"), world + 1)

def wait (_ : Bool) (world : Nat) : Reply Nat String String × Nat :=
  (.terminal (.suspended "worker-7"), world + 1)

def finish (_ : Bool) (world : Nat) : Reply Nat String String × Nat :=
  (.terminal (.done 42), world + 1)

/-- Reading an existing cursor outcome keeps scheduler suspension separate
from its four tagged terminal cases. -/
def snapshot {p : Profile} {bill : Bool → Nat → List Event}
    {action : Bool → Nat → Reply Nat String String × Nat} :
    Outcome p bill action →
      (Control Nat String String ⊕ Terminal Nat String String) × Nat × Account
  | .paused ⟨_, control, state⟩ => (.inl control, state)
  | .done ⟨_, result, state⟩ => (.inr result, state)

theorem insufficient_budget_no_action :
    let answer := run metered invoice tick 2
      ⟨PUnit.unit, .running false, 0, initial metered 1⟩
    answer.1 = 0 ∧ snapshot answer.2 =
      (.inr (.refused .budget), 0, initial metered 1) := by decide

theorem paid_failure_retains_cost_and_mutation :
    let answer := run metered invoice fail 2
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inr (.fault "allocation"), 1, ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem paid_suspension_retains_cost_and_mutation :
    let answer := run metered invoice wait 2
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inr (.suspended "worker-7"), 1, ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem successful_completion_is_a_distinct_result :
    let answer := run metered invoice finish 2
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inr (.done 42), 1, ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem scheduler_pause_can_hold_a_terminal_reply :
    let answer := run metered invoice wait 1
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inl (.terminal (.suspended "worker-7")), 1,
        ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem licensed_replay_is_still_paid :
    let answer := run metered invoice tick 2
      ⟨PUnit.unit, .running true, 0, initial metered 5⟩
    answer.1 = 4 ∧ snapshot answer.2 =
      (.inl (.running true), 2, ⟨1, none, 2, [receipt 0 2, receipt 1 2]⟩) := by decide

theorem reusing_a_physical_event_is_refused :
    let answer := run metered (fun _ _ => [receipt 0 2]) tick 3
      ⟨PUnit.unit, .running true, 0, initial metered 5⟩
    answer.1 = 2 ∧ snapshot answer.2 =
      (.inr (.refused .repeatedIdentity), 1, ⟨3, none, 1, [receipt 0 2]⟩) := by decide

theorem unknown_kinds_are_not_free :
    let p : Profile := { metered with kinds := [("step", none)] }
    let answer := run p invoice tick 2 ⟨PUnit.unit, .running false, 0, initial p 5⟩
    answer.1 = 0 ∧ snapshot answer.2 =
      (.inr (.refused .unknownCharge), 0, initial p 5) := by decide

theorem undeclared_kind_is_refused :
    let answer := run metered (fun _ n => [(n, ⟨0, n, .heapLookup, 2⟩)]) tick 2
      ⟨PUnit.unit, .running false, 0, initial metered 5⟩
    answer.1 = 0 ∧ snapshot answer.2 =
      (.inr (.refused .undeclaredKind), 0, initial metered 5) := by decide

def unbounded : Profile := ⟨"zero-work", [], .unknown, none, .refused⟩

def noInvoice (_ : Bool) (_ : Nat) : List Event := []

/-- No finite amount of scheduler fuel can finish this zero-cost handler.
This is why a receipt budget alone proves neither termination nor progress. -/
theorem zero_work_can_continue_forever (fuel world calls budget : Nat) :
    run unbounded noInvoice tick fuel
      ⟨PUnit.unit, .running false, world, ⟨budget, none, calls, []⟩⟩ =
      (0, .paused ⟨PUnit.unit, .running false,
        world + fuel, ⟨budget, none, calls + fuel, []⟩⟩) := by
  induction fuel generalizing world calls with
  | zero => rfl
  | succ fuel ih =>
      change
        (0 + (run unbounded noInvoice tick fuel
          ⟨PUnit.unit, .running false, world + 1, ⟨budget, none, calls + 1, []⟩⟩).1,
          (run unbounded noInvoice tick fuel
            ⟨PUnit.unit, .running false, world + 1, ⟨budget, none, calls + 1, []⟩⟩).2) = _
      rw [ih]
      simp only [Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 fuel]

theorem finite_allowance_stops_zero_work_calls :
    let p : Profile := { unbounded with progress := .bounded, bound := some 2 }
    let answer := run p noInvoice tick 4
      ⟨PUnit.unit, .running false, 0, initial p 0⟩
    answer.1 = 0 ∧ snapshot answer.2 =
      (.inr (.refused .inspectionLimit), 2, ⟨0, some 0, 2, []⟩) := by decide

def countdown (_ : Bool) (world : Nat) : Reply Nat String String × Nat :=
  if world = 0 then (.terminal (.done 0), world) else (.paid, world - 1)

theorem countdown_decreases (replay : Bool) (world : Nat)
    (continues : (countdown replay world).1 = .paid) :
    (countdown replay world).2 < world := by
  by_cases hz : world = 0
  · simp [countdown, hz] at continues
  · simp only [countdown, if_neg hz]
    omega

/-- This actual handler supplies the additional local rank proof that a
progress declaration alone cannot provide. Refusal remains a possible tag. -/
theorem countdown_finite_inspection (world budget : Nat) :
    ∃ (spent : Nat) (result : Finished metered invoice countdown),
      run metered invoice countdown (world + 2)
        ⟨PUnit.unit, .running false, world, initial metered budget⟩ =
          (spent, .done result) := by
  apply ranked_inspection_finishes metered invoice countdown id countdown_decreases
  change world + 1 < world + 2
  omega

theorem countdown_delivers_with_sufficient_budget :
    let answer := run metered invoice countdown 4
      ⟨PUnit.unit, .running false, 2, initial metered 6⟩
    answer.1 = 6 ∧ snapshot answer.2 =
      (.inr (.done 0), 0, ⟨0, none, 3, [receipt 2 2, receipt 1 2, receipt 0 2]⟩) := by decide

end Mettapedia.GSLT.LanguageDef.OperationCostProtocolControls
