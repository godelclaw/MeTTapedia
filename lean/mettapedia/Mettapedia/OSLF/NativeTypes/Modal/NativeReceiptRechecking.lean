import Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalAdmission
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledReadout
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseEventEquality

/-!
# Exact finite rechecking of complete authored occurrence receipts

The checker consumes the actual declaration index, matching trace, both
scoped assignments, complete ordered premise history and specified target.
It searches the certified executor's actual receipt list, rather than
accepting endpoint equality as complete evidence. Any accepted payload
reconstructs the independent firing judgment. Exhaustive rejection is earned
only under the original declaration-derived descent admission.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking

open Mettapedia.OSLF.MeTTaIL Syntax ScopedRuleMatching GeneralPremise StructuralDescent

structure Payload where
  index : Nat
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : Assignment
  completed : Assignment
  history : List Event
  target : Pattern
  deriving DecidableEq, Repr

def read {environment : Environment} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (answer : Execution.RootAnswer environment bound type source) : Payload :=
  ⟨answer.index, answer.trace, answer.captured, answer.completed, answer.history, answer.target⟩

def Valid (environment : Environment) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (payload : Payload) : Prop :=
  RootFiring environment bound type source payload.index payload.trace payload.captured
    payload.completed payload.history payload.target

def fromSnapshot {environment : Environment} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (snapshot : Scheduled.Snapshot environment bound type source) (payload : Payload) :
    Option (Execution.RootAnswer environment bound type source) :=
  (Scheduled.receipts snapshot).find? fun answer => decide (read answer = payload)

def recheck (environment : Environment) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (payload : Payload) : Option (Execution.RootAnswer environment bound type source) :=
  fromSnapshot (Scheduled.finishSource environment bound type source) payload

theorem fromSnapshot_read {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {snapshot : Scheduled.Snapshot environment bound type source}
    {payload : Payload} {answer : Execution.RootAnswer environment bound type source}
    (accepted : fromSnapshot snapshot payload = some answer) : read answer = payload := by
  have checked : decide (read answer = payload) = true :=
    List.find?_some (p := fun candidate => decide (read candidate = payload)) accepted
  exact of_decide_eq_true checked

theorem fromSnapshot_sound {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {snapshot : Scheduled.Snapshot environment bound type source}
    {payload : Payload} {answer : Execution.RootAnswer environment bound type source}
    (accepted : fromSnapshot snapshot payload = some answer) : Valid environment bound type source payload := by
  rw [← fromSnapshot_read accepted]
  exact answer.valid

theorem recheck_sound {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {payload : Payload} {answer : Execution.RootAnswer environment bound type source}
    (accepted : recheck environment bound type source payload = some answer) :
    Valid environment bound type source payload := fromSnapshot_sound accepted

theorem recheck_complete {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {payload : Payload}
    (admitted : checkEnvironment environment = true)
    (valid : Valid environment bound type source payload) :
    ∃ answer, recheck environment bound type source payload = some answer ∧ read answer = payload := by
  let wanted : Execution.RootAnswer environment bound type source :=
    ⟨payload.index, payload.trace, payload.captured, payload.completed, payload.history, payload.target, valid⟩
  have member := Scheduled.finishSource_receipts_complete environment admitted bound type source wanted
  cases found : recheck environment bound type source payload with
  | none =>
      have missing := List.find?_eq_none.mp found wanted member
      exact False.elim (missing (by simp [wanted, read]))
  | some answer => exact ⟨answer, rfl, fromSnapshot_read found⟩

theorem recheck_exact {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {payload : Payload} (admitted : checkEnvironment environment = true) :
    (recheck environment bound type source payload).isSome = true ↔
      Valid environment bound type source payload := by
  constructor
  · intro found
    cases accepted : recheck environment bound type source payload with
    | none => rw [accepted] at found; cases found
    | some answer => exact recheck_sound accepted
  · intro valid
    obtain ⟨answer, accepted, _⟩ := recheck_complete admitted valid
    rw [accepted]
    rfl

theorem exhaustive_rejection_exact {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {payload : Payload}
    (admitted : checkEnvironment environment = true) :
    recheck environment bound type source payload = none ↔ ¬ Valid environment bound type source payload := by
  constructor
  · intro absent valid
    obtain ⟨answer, accepted, _⟩ := recheck_complete admitted valid
    rw [absent] at accepted
    cases accepted
  · intro invalid
    cases selected : recheck environment bound type source payload with
    | none => rfl
    | some answer => exact False.elim (invalid (recheck_sound selected))

/-- A pause retains its exact receipt witness when additional work is run.
No equality of endpoints is used to identify two origins. -/
theorem accepted_persists {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {snapshot : Scheduled.Snapshot environment bound type source}
    {payload : Payload} {answer : Execution.RootAnswer environment bound type source}
    (accepted : fromSnapshot snapshot payload = some answer) (fuel : Nat) :
    ∃ later, fromSnapshot (Scheduled.resume environment bound type source fuel snapshot) payload = some later ∧
      read later = payload := by
  have member := List.mem_of_find?_eq_some accepted
  obtain ⟨suffix, ordered⟩ := Scheduled.receipts_preserved environment bound type source fuel snapshot
  have laterMember : answer ∈ Scheduled.receipts (Scheduled.resume environment bound type source fuel snapshot) := by
    rw [ordered]
    exact List.mem_append_left _ member
  cases found : fromSnapshot (Scheduled.resume environment bound type source fuel snapshot) payload with
  | none =>
      have missing := List.find?_eq_none.mp found answer laterMember
      exact False.elim (missing (by simp only [fromSnapshot_read accepted, decide_true]))
  | some later => exact ⟨later, rfl, fromSnapshot_read found⟩

theorem pause_resume_exact (environment : Environment) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (snapshot : Scheduled.Snapshot environment bound type source)
    (payload : Payload) (first second : Nat) :
    fromSnapshot (Scheduled.resume environment bound type source (first + second) snapshot) payload =
      fromSnapshot (Scheduled.resume environment bound type source second
        (Scheduled.resume environment bound type source first snapshot)) payload := by
  rw [Scheduled.resume_add]

end Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking
