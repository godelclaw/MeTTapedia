import Mettapedia.Machines.ContextualCBPV
import Mettapedia.Machines.DemandedResultAdmission

/-!
# Result receivers at contextual call entry

A call carries its result receiver independently of its argument. A closed
total primitive may return a value before its inert receiver is matched.
The two executions below have different call/continuation transitions, but
agree on the complete terminal state, including logical context and faults.

The recursive constructor control is different: its argument is closed and
its body has no effects, yet erasing a mismatching receiver prevents completion.
An invariant proves that every finite value-first slice remains in recursive
call entry without publishing. This instantiates the common CBPV kernel rather
than defining a second execution loop.

The C result-policy and prepared-bind admission use this distinction. Native
groundness, the finite-node classifier and complete source elaboration remain
separate correspondence obligations. These bounds count kernel transitions,
not C activations or source-level fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.InvocationResultDemand

open NativeCallReturn

inductive Datum where
  | number (value : Nat)
  | left (value : Datum)
  | right (value : Datum)
  deriving DecidableEq, Repr

inductive Receiver where
  | fresh
  | left
  | right
  deriving DecidableEq, Repr

inductive Call where
  | primitive (argument : Nat) (receiver : Receiver)
  | recursive (argument : Nat) (receiver : Receiver)
  | matchResult (receiver : Receiver) (value : Datum)

abbrev Code := ContextualCBPV.Code Datum Call Nat Nat Unit Nat
abbrev Cursor := NativeCallReturn.Cursor Datum Nat Unit Nat
abbrev State := ContextualCBPV.State Datum Call Nat Nat Unit Nat Nat Nat Cursor
abbrev Semantics := ContextualCBPV.Semantics Datum Call Nat Nat Unit Nat Nat Nat Cursor

/-- The logical context records successful constructor-field bindings. The
closed producer does not read this context, which is the mode premise here. -/
def meet (context : Nat) (receiver : Receiver) (value : Datum) : Option Nat :=
  match receiver, value with
  | .fresh, _ => some context
  | .left, .left _ | .right, .right _ => some (context + 1)
  | _, _ => none

def matched (context : Nat) (receiver : Receiver) (value : Datum) : Nat × Code :=
  match meet context receiver value with
  | none => (context, .failure)
  | some next => (next, .returned value)

def wrapRight : Packet Datum Nat Unit → Code
  | .value _ value | .conditional value _ => .returned (.right value)
  | .raised fault => .raised fault

def recursiveBody (argument : Nat) : Code :=
  .sequence (.invoke (.recursive (argument + 1) .fresh)) wrapRight

def semantics (produce : Nat → Except Nat (Option Datum)) : Semantics where
  enter := fun _ context call => match call with
    | .primitive input receiver => match produce input with
        | .error fault => (context, .raised fault)
        | .ok none => (context, .failure)
        | .ok (some value) => matched context receiver value
    | .matchResult receiver value => matched context receiver value
    | .recursive input receiver => match receiver with
        | .left => (context, .failure)
        | .fresh => (context, recursiveBody input)
        | .right => (context + 1, recursiveBody input)
  suspend := fun context reference => .number (context + reference)
  force := fun context value => (context, .returned value)
  native := fun context world effect =>
    (world + effect + 1, ⟨.one (.value .completed (.number world)), context, 0⟩)
  pull := fun world cursor => (world, NativeCallReturn.read cursor)
  resume := fun _ current => current

def matchReturned (receiver : Receiver) : Packet Datum Nat Unit → Code
  | .value _ value | .conditional value _ => .invoke (.matchResult receiver value)
  | .raised fault => .raised fault

def byDestination (argument : Nat) (receiver : Receiver) : Code :=
  .invoke (.primitive argument receiver)

def atReturn (argument : Nat) (receiver : Receiver) : Code :=
  .sequence (.invoke (.primitive argument .fresh)) (matchReturned receiver)

def run (produce : Nat → Except Nat (Option Datum)) (allowance context : Nat)
    (code : Code) : State :=
  ((ContextualCBPV.core (semantics produce) 0 context).runSlice allowance (ContextualCBPV.initial 0 context code)).1

/-- A closed, total producer and inert receiver may use value-first entry.
Logical failure, raised control and the context established by matching all
agree; this is stronger than equality only for successful values. -/
theorem finite_result_protocol (produce : Nat → Except Nat (Option Datum))
    (argument context : Nat) (receiver : Receiver) :
    run produce 12 context (byDestination argument receiver) =
      run produce 12 context (atReturn argument receiver) := by
  cases result : produce argument with
  | error fault =>
      simp [run, byDestination, atReturn, ContextualCBPV.core, MachineCore.runSlice,
        ContextualCBPV.step, ContextualCBPV.advance, ContextualCBPV.initial, ContextualCBPV.debit, ContextualCBPV.origin, semantics, result]
  | ok value =>
      cases value with
      | none =>
          simp [run, byDestination, atReturn, ContextualCBPV.core, MachineCore.runSlice,
            ContextualCBPV.step, ContextualCBPV.advance, ContextualCBPV.initial, ContextualCBPV.debit, ContextualCBPV.origin, semantics, result]
      | some value =>
          cases receiver <;> cases value <;>
            simp [run, byDestination, atReturn, ContextualCBPV.core, MachineCore.runSlice,
              ContextualCBPV.step, ContextualCBPV.advance, ContextualCBPV.initial, ContextualCBPV.debit, ContextualCBPV.origin, semantics, result,
              matched, meet, matchReturned]

inductive Looping : ContextualCBPV.Control Datum Call Nat Nat Unit Nat Nat Cursor → Prop where
  | call (context argument : Nat) :
      Looping (.compute context (.invoke (.recursive argument .fresh)))
  | sequence (context argument : Nat) (body : Packet Datum Nat Unit → Code) :
      Looping (.compute context (.sequence (.invoke (.recursive argument .fresh)) body))

theorem recursive_step (produce : Nat → Except Nat (Option Datum))
    (state : State) (looping : Looping state.focus.control) :
    ∃ next, ContextualCBPV.step (semantics produce) state = some next ∧
      Looping next.focus.control ∧ next.published = state.published := by
  rcases state with ⟨world, ⟨control, frames⟩, alternatives, published, entries, spent, trace⟩
  cases looping with
  | call context argument =>
      let next : State := ⟨world,
        ⟨.compute context (recursiveBody argument), .restore context :: frames⟩,
        alternatives, published, entries, spent, trace⟩
      refine ⟨next, ?_, Looping.sequence context (argument + 1) wrapRight, rfl⟩
      simp [next, ContextualCBPV.step, ContextualCBPV.advance, ContextualCBPV.debit, ContextualCBPV.origin, semantics, recursiveBody]
  | sequence context argument body =>
      let next : State := ⟨world,
        ⟨.compute context (.invoke (.recursive argument .fresh)),
          .sequence context body :: frames⟩,
        alternatives, published, entries, spent, trace⟩
      refine ⟨next, ?_, Looping.call context argument, rfl⟩
      simp [next, ContextualCBPV.step, ContextualCBPV.advance, ContextualCBPV.debit, ContextualCBPV.origin]

theorem recursive_slice (produce : Nat → Except Nat (Option Datum))
    (allowance context : Nat) (state : State) (looping : Looping state.focus.control) :
    Looping (((ContextualCBPV.core (semantics produce) 0 context).runSlice allowance state).1).focus.control ∧
      ((ContextualCBPV.core (semantics produce) 0 context).runSlice allowance state).1.published =
        state.published := by
  induction allowance generalizing state with
  | zero => exact ⟨looping, rfl⟩
  | succ allowance ih =>
      obtain ⟨next, advanced, invariant, same⟩ := recursive_step produce state looping
      obtain ⟨last, unchanged⟩ := ih next invariant
      simpa [MachineCore.runSlice, ContextualCBPV.core, advanced] using
        And.intro last (unchanged.trans same)

/-- Closed arguments and absence of effects do not license erasing a result
receiver. Every finite slice keeps pending recursive work and emits nothing. -/
theorem erased_receiver_never_publishes (produce : Nat → Except Nat (Option Datum))
    (argument context allowance : Nat) :
    (run produce allowance context (.invoke (.recursive argument .fresh))).published = [] := by
  exact (recursive_slice produce allowance context
    (ContextualCBPV.initial 0 context (.invoke (.recursive argument .fresh)))
    (Looping.call context argument)).2

theorem erased_receiver_is_nonterminal (produce : Nat → Except Nat (Option Datum))
    (argument context allowance : Nat) :
    ∃ next, ContextualCBPV.step (semantics produce)
      (run produce allowance context (.invoke (.recursive argument .fresh))) = some next := by
  have invariant := (recursive_slice produce allowance context
    (ContextualCBPV.initial 0 context (.invoke (.recursive argument .fresh)))
    (Looping.call context argument)).1
  obtain ⟨next, advanced, _, _⟩ := recursive_step produce _ invariant
  exact ⟨next, advanced⟩

theorem mismatching_receiver_completes (produce : Nat → Except Nat (Option Datum))
    (argument context : Nat) :
    (run produce 4 context (.invoke (.recursive argument .left))).focus.control =
      .stopped .complete ∧
    (run produce 4 context (.invoke (.recursive argument .left))).published = [] := by
  simp [run, ContextualCBPV.core, MachineCore.runSlice, ContextualCBPV.step, ContextualCBPV.advance,
    ContextualCBPV.initial, ContextualCBPV.debit, ContextualCBPV.origin, semantics]

/-- A callee's alternatives must be retained before executing a selected body.
Refuting its first constructor resumes the next occurrence in that callee. -/
theorem failed_candidate_retains_alternatives
    (produce : Nat → Except Nat (Option Datum)) (context : Nat) :
    (run produce 12 context (.choice
      (.invoke (.recursive 0 .left)) (.returned (.number 7)))).published =
        [(context, .value .completed (.number 7))] := by
  rfl

/-- Treating the first candidate's failure as the whole call's failure loses
the next answer. Both computations terminate; their observations differ. -/
theorem discarding_candidate_changes_observation
    (produce : Nat → Except Nat (Option Datum)) (context : Nat) :
    (run produce 12 context (.choice
      (.invoke (.recursive 0 .left)) (.returned (.number 7)))).published ≠
      (run produce 12 context (.invoke (.recursive 0 .left))).published := by
  rw [failed_candidate_retains_alternatives]
  simp [run, ContextualCBPV.core, MachineCore.runSlice, ContextualCBPV.step,
    ContextualCBPV.advance, ContextualCBPV.initial, ContextualCBPV.debit,
    ContextualCBPV.origin, semantics]

end Mettapedia.Machines.InvocationResultDemand

#print axioms Mettapedia.Machines.InvocationResultDemand.finite_result_protocol
#print axioms Mettapedia.Machines.InvocationResultDemand.recursive_step
#print axioms Mettapedia.Machines.InvocationResultDemand.recursive_slice
#print axioms Mettapedia.Machines.InvocationResultDemand.erased_receiver_never_publishes
#print axioms Mettapedia.Machines.InvocationResultDemand.erased_receiver_is_nonterminal
#print axioms Mettapedia.Machines.InvocationResultDemand.mismatching_receiver_completes
#print axioms Mettapedia.Machines.InvocationResultDemand.failed_candidate_retains_alternatives
#print axioms Mettapedia.Machines.InvocationResultDemand.discarding_candidate_changes_observation
