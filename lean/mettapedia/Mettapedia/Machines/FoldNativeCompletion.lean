import Mettapedia.Machines.NativeCallReturn

/-!
# Fold completion before dialect projection

The reference constructs its success delimiter at the end of the fold.
The producer instead retains a typed success or callback fault and projects
only at the invocation boundary. Both definitions execute each callback in
the current world and stop after a fault. Error terms remain expression
packets, as required by this operation's existing dialect policy.

Native callback evaluation, argument preflight, single-answer admission and
scratch-arena ownership remain separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FoldNativeCompletion

variable {Value Item World : Type}

abbrev Step (Value Item World : Type) :=
  World → Value → Item → World × Except Value Value

def produce (step : Step Value Item World) :
    List Item → World → Value → World × Except Value Value
  | [], world, accumulator => (world, .ok accumulator)
  | item :: rest, world, accumulator =>
      let next := step world accumulator item
      match next.2 with
      | .error fault => (next.1, .error fault)
      | .ok value => produce step rest next.1 value

def reference (step : Step Value Item World) (finish : Value → Value) :
    List Item → World → Value → World × Value
  | [], world, accumulator => (world, finish accumulator)
  | item :: rest, world, accumulator =>
      let next := step world accumulator item
      match next.2 with
      | .error fault => (next.1, fault)
      | .ok value => reference step finish rest next.1 value

def project (finish : Value → Value) (result : World × Except Value Value) : World × Value :=
  (result.1, match result.2 with | .error fault => fault | .ok value => finish value)

theorem projection_refines (step : Step Value Item World) (finish : Value → Value)
    (items : List Item) (world : World) (accumulator : Value) :
    project finish (produce step items world accumulator) =
      reference step finish items world accumulator := by
  induction items generalizing world accumulator with
  | nil => rfl
  | cons item rest ih =>
      rcases progressed : step world accumulator item with ⟨after, reply⟩
      cases reply with
      | error fault => simp [produce, reference, project, progressed]
      | ok value => simpa [produce, reference, progressed] using ih after value

def continueWith (step : Step Value Item World) (items : List Item)
    (result : World × Except Value Value) : World × Except Value Value :=
  match result.2 with
  | .error fault => (result.1, .error fault)
  | .ok value => produce step items result.1 value

/-- Composing a completed prefix retains its actual world and accumulator.
A failed prefix keeps the fault and never runs the suffix. -/
theorem produce_append (step : Step Value Item World) (first later : List Item)
    (world : World) (accumulator : Value) :
    produce step (first ++ later) world accumulator =
      continueWith step later (produce step first world accumulator) := by
  induction first generalizing world accumulator with
  | nil => rfl
  | cons item rest ih =>
      rcases progressed : step world accumulator item with ⟨after, reply⟩
      cases reply with
      | error fault => simp [produce, continueWith, progressed]
      | ok value => simpa [produce, progressed] using ih after value

theorem callback_fault_stops_suffix (step : Step Value Item World)
    (item : Item) (later : List Item) (world after : World) (accumulator fault : Value)
    (failed : step world accumulator item = (after, .error fault)) :
    produce step (item :: later) world accumulator = (after, .error fault) := by
  simp [produce, failed]

def petta (result : Except Value Value) : NativeCallReturn.Packet Value Unit Unit :=
  match result with
  | .error fault => .value .expression fault
  | .ok value => .value .completed value

namespace Controls

def effectStep : Step (List Nat) Nat (List Nat) := fun world accumulator item =>
  (world ++ [item], if item == 0 then .error [9] else .ok accumulator)

theorem fault_keeps_prior_effects_only :
    produce effectStep [1, 0, 2] [] [7] = ([1, 0], .error [9]) := by
  decide +kernel

theorem equal_occurrences_both_run :
    produce effectStep [1, 1] [] [7] = ([1, 1], .ok [7]) := by
  decide +kernel

/-- The same marker-shaped payload receives different treatment solely from
the producer's tag; an expression packet cannot certify its own completion. -/
theorem marker_shape_does_not_choose_completion :
    petta (.ok ([0, 7] : List Nat)) ≠ petta (.error [0, 7]) ∧
    project (0 :: ·) ((), .ok ([0, 7] : List Nat)) = ((), [0, 0, 7]) ∧
    project (0 :: ·) ((), .error ([0, 7] : List Nat)) = ((), [0, 7]) := by
  decide +kernel

end Controls
end Mettapedia.Machines.FoldNativeCompletion

#print axioms Mettapedia.Machines.FoldNativeCompletion.projection_refines
#print axioms Mettapedia.Machines.FoldNativeCompletion.produce_append
#print axioms Mettapedia.Machines.FoldNativeCompletion.callback_fault_stops_suffix
#print axioms Mettapedia.Machines.FoldNativeCompletion.Controls.fault_keeps_prior_effects_only
#print axioms Mettapedia.Machines.FoldNativeCompletion.Controls.equal_occurrences_both_run
#print axioms Mettapedia.Machines.FoldNativeCompletion.Controls.marker_shape_does_not_choose_completion
