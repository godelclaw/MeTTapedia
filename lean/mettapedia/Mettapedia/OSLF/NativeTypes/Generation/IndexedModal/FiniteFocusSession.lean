import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking

/-!
# Retained verification of finite-rely membership certificates

A unit of work checks one rely request against the supplied certificate.
The immutable certificate retains complete firing origins. A rejected
certificate is distinct from a refutation of the semantic type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking

open Mettapedia.OSLF.MeTTaIL.Syntax
open FocusMeaning

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}

inductive Verdict where
  | unknown
  | proved
  | certificateRejected
  deriving DecidableEq, Repr

structure State (installed : Joined.Installed) (index : installed.Index) (ambient : List String) where
  pending : List (RelyValues installed index ambient)
  accepted : Bool

variable (parameters : Parameters installed index ambient) (focus : Pattern) (certificate : List Witness)

def start : State installed index ambient :=
  ⟨requests parameters, checkFocus installed index ambient focus⟩

def tick (state : State installed index ambient) : State installed index ambient :=
  match state.pending with
  | [] => state
  | values :: remaining =>
      ⟨remaining, state.accepted && certificate.any (accepts parameters focus values)⟩

def run : Nat → State installed index ambient → State installed index ambient
  | 0, state => state
  | fuel + 1, state => run fuel (tick parameters focus certificate state)

theorem run_add (first extra : Nat) (state : State installed index ambient) :
    run parameters focus certificate (first + extra) state =
      run parameters focus certificate extra (run parameters focus certificate first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (tick parameters focus certificate state)

def residual (state : State installed index ambient) : Bool :=
  state.accepted && state.pending.all (fun values => certificate.any (accepts parameters focus values))

theorem residual_tick (state : State installed index ambient) :
    residual parameters focus certificate (tick parameters focus certificate state) =
      residual parameters focus certificate state := by
  cases state with
  | mk pending accepted =>
      cases pending with
      | nil => rfl
      | cons values rest => simp only [tick, residual, List.all_cons, Bool.and_assoc]

theorem residual_run (fuel : Nat) (state : State installed index ambient) :
    residual parameters focus certificate (run parameters focus certificate fuel state) =
      residual parameters focus certificate state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => exact (ih _).trans (residual_tick parameters focus certificate state)

def readout (state : State installed index ambient) : Verdict :=
  if !state.accepted then .certificateRejected
  else if state.pending.isEmpty then .proved else .unknown

structure Session where
  spent : Nat
  state : State installed index ambient
  replay : state = run parameters focus certificate spent (start parameters focus)

def begin : Session parameters focus certificate := ⟨0, start parameters focus, rfl⟩

namespace Session

variable {parameters focus certificate}

theorem ext (first second : Session parameters focus certificate)
    (spent : first.spent = second.spent) (states : first.state = second.state) : first = second := by
  cases first
  cases second
  cases spent
  cases states
  rfl

def resume (session : Session parameters focus certificate) (fuel : Nat) : Session parameters focus certificate where
  spent := session.spent + fuel
  state := run parameters focus certificate fuel session.state
  replay := by rw [session.replay, ← run_add]

theorem resume_add (session : Session parameters focus certificate) (first extra : Nat) :
    session.resume (first + extra) = (session.resume first).resume extra := by
  apply ext
  · exact (Nat.add_assoc _ _ _).symm
  · exact run_add parameters focus certificate first extra session.state

def verdict (session : Session parameters focus certificate) : Verdict := readout session.state

theorem proved (session : Session parameters focus certificate) (read : session.verdict = .proved) :
    Inhabits parameters.meaning focus := by
  have accepted : session.state.accepted = true := by
    cases value : session.state.accepted <;> simp_all [verdict, readout]
  have empty : session.state.pending = [] := by
    simp only [verdict, readout, accepted, Bool.not_true, Bool.false_eq_true, if_false] at read
    split at read
    · rename_i empty
      exact List.isEmpty_iff.mp empty
    · cases read
  have earned : residual parameters focus certificate session.state = check parameters focus certificate := by
    rw [session.replay, residual_run]
    rfl
  apply check_sound parameters focus certificate
  rw [← earned]
  simp only [residual, empty, accepted, List.all_nil, Bool.and_true]

theorem rejected (session : Session parameters focus certificate) (read : session.verdict = .certificateRejected) :
    check parameters focus certificate = false := by
  have declined : session.state.accepted = false := by
    cases value : session.state.accepted with
    | false => rfl
    | true =>
        simp only [verdict, readout, value, Bool.not_true, Bool.false_eq_true, if_false] at read
        split at read <;> cases read
  have earned : residual parameters focus certificate session.state = check parameters focus certificate := by
    rw [session.replay, residual_run]
    rfl
  rw [← earned]
  simp only [residual, declined, Bool.false_and]

end Session

theorem run_pending (fuel : Nat) (state : State installed index ambient) :
    (run parameters focus certificate fuel state).pending = state.pending.drop fuel := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rw [run, ih]
      cases state with
      | mk pending accepted => cases pending <;> simp only [tick, List.drop_succ_cons, List.drop_nil]

/-- The computable bound counts every required rely request. -/
theorem check_decided (fuel : Nat) (enough : (requests parameters).length ≤ fuel) :
    ((begin parameters focus certificate).resume fuel).verdict =
      if check parameters focus certificate then .proved else .certificateRejected := by
  let session := (begin parameters focus certificate).resume fuel
  have empty : session.state.pending = [] := by
    change (run parameters focus certificate fuel (start parameters focus)).pending = []
    rw [run_pending]
    exact List.drop_eq_nil_of_le enough
  have earned : residual parameters focus certificate session.state = check parameters focus certificate := by
    change residual parameters focus certificate (run parameters focus certificate fuel _) = _
    rw [residual_run]
    rfl
  have accepted : session.state.accepted = check parameters focus certificate := by
    simpa only [residual, empty, List.all_nil, Bool.and_true] using earned
  change readout session.state = _
  simp only [readout, accepted, empty, List.isEmpty_nil, if_true]
  cases check parameters focus certificate <;> rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking
