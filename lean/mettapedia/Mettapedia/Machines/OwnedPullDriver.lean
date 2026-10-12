import Mathlib.Data.List.Basic

/-!
# Explicit frames for owned child computations

`Runs` gives the recursive meaning of a child computation and its caller.
`transition` instead moves one explicit frame at a time, and `advance` runs a
bounded number of those transitions.  The refinement theorem preserves the
entire ordered event trace, including duplicate events.  `advance_add` proves
that a paused driver resumes from its residual without replaying earlier work.

The model does not license memoization, reorder effects, or establish the
native runtime's ownership invariants.  Events may record effects and charges;
child entry and return add no events of their own.  Native correspondence and
cleanup remain separate obligations.
-/

namespace Mettapedia.Machines.OwnedPullDriver

universe u v

inductive Program (Value : Type u) (Event : Type v) where
  | done (value : Value)
  | emit (event : Event) (next : Program Value Event)
  | child (work : Program Value Event) (resume : Value → Program Value Event)

variable {Value : Type u} {Event : Type v}

inductive Runs : Program Value Event → List Event → Value → Prop where
  | done : Runs (.done value) [] value
  | emit (tail : Runs next events value) : Runs (.emit event next) (event :: events) value
  | child (inner : Runs work first value) (outer : Runs (resume value) rest result) :
      Runs (.child work resume) (first ++ rest) result

structure State (Value : Type u) (Event : Type v) where
  work : Program Value Event
  frames : List (Value → Program Value Event)

def transition (state : State Value Event) : Option (List Event × State Value Event) :=
  match state.work, state.frames with
  | .done _, [] => none
  | .done value, resume :: rest => some ([], ⟨resume value, rest⟩)
  | .emit event next, frames => some ([event], ⟨next, frames⟩)
  | .child work resume, frames => some ([], ⟨work, resume :: frames⟩)

def advance : Nat → State Value Event → List Event × State Value Event
  | 0, state => ([], state)
  | fuel + 1, state =>
      match transition state with
      | none => ([], state)
      | some (events, next) =>
          let result := advance fuel next
          (events ++ result.1, result.2)

inductive Step : State Value Event → List Event → State Value Event → Prop where
  | emit : Step ⟨.emit event next, frames⟩ [event] ⟨next, frames⟩
  | child : Step ⟨.child work resume, frames⟩ [] ⟨work, resume :: frames⟩
  | resume : Step ⟨.done value, resume :: rest⟩ [] ⟨resume value, rest⟩

theorem transition_of_step (step : Step source events target) :
    transition source = some (events, target) := by
  cases step <;> rfl

theorem step_of_transition {source : State Value Event}
    (observed : transition source = some (events, target)) : Step source events target := by
  rcases source with ⟨work, frames⟩
  cases work with
  | done value =>
      cases frames with
      | nil => simp [transition] at observed
      | cons resume rest =>
          simp [transition] at observed
          rcases observed with ⟨rfl, rfl⟩
          exact Step.resume
  | emit event next =>
      simp [transition] at observed
      rcases observed with ⟨rfl, rfl⟩
      exact Step.emit
  | child inner resume =>
      simp [transition] at observed
      rcases observed with ⟨rfl, rfl⟩
      exact Step.child

inductive Path : State Value Event → List Event → Nat → State Value Event → Prop where
  | refl : Path state [] 0 state
  | next (step : Step source first middle) (tail : Path middle rest count target) :
      Path source (first ++ rest) (count + 1) target

theorem Path.append (first : Path source earlier m middle)
    (rest : Path middle suffix n target) : Path source (earlier ++ suffix) (m + n) target := by
  induction first generalizing suffix n target with
  | refl => simpa using rest
  | next step tail ih =>
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Path.next step (ih rest)

theorem advance_of_path (path : Path source events count target) :
    advance count source = (events, target) := by
  induction path with
  | refl => rfl
  | next step tail ih => simp [advance, transition_of_step step, ih]

theorem runs_path (run : Runs work events value)
    (frames : List (Value → Program Value Event)) :
    ∃ count, Path ⟨work, frames⟩ events count ⟨.done value, frames⟩ := by
  induction run generalizing frames with
  | done => exact ⟨0, Path.refl⟩
  | emit tail ih =>
      obtain ⟨count, path⟩ := ih frames
      exact ⟨count + 1, by simpa using Path.next Step.emit path⟩
  | @child work first value resume rest result inner outer innerIH outerIH =>
      obtain ⟨m, innerPath⟩ := innerIH (resume :: frames)
      obtain ⟨n, outerPath⟩ := outerIH frames
      have begin := Path.next Step.child innerPath
      have finish := Path.next Step.resume outerPath
      exact ⟨(m + 1) + (n + 1), by simpa using begin.append finish⟩

inductive Continues : List (Value → Program Value Event) → Value → List Event → Value → Prop where
  | done : Continues [] value [] value
  | frame (work : Runs (resume value) first next)
      (rest : Continues frames next suffix result) :
      Continues (resume :: frames) value (first ++ suffix) result

def Denotes (state : State Value Event) (events : List Event) (result : Value) : Prop :=
  ∃ first value rest, Runs state.work first value ∧
    Continues state.frames value rest result ∧ events = first ++ rest

theorem denotes_before_step (step : Step source earlier target)
    (after : Denotes target suffix result) : Denotes source (earlier ++ suffix) result := by
  obtain ⟨first, value, rest, work, frames, trace⟩ := after
  cases step with
  | emit =>
      exact ⟨_ :: first, value, rest, Runs.emit work, frames, by simp [trace]⟩
  | child =>
      cases frames with
      | frame outer remaining =>
          exact ⟨_, _, _, Runs.child work outer, remaining,
            by simp [trace, List.append_assoc]⟩
  | resume =>
      exact ⟨[], _, first ++ rest, Runs.done, Continues.frame work frames, by simp [trace]⟩

theorem denotes_before_path (path : Path source earlier count target)
    (after : Denotes target suffix result) : Denotes source (earlier ++ suffix) result := by
  induction path with
  | refl => simpa using after
  | next step tail ih =>
      simpa [List.append_assoc] using denotes_before_step step (ih after)

theorem runs_of_path {work : Program Value Event}
    (path : Path ⟨work, []⟩ events count ⟨.done value, []⟩) :
    Runs work events value := by
  have final : Denotes (Value := Value) (Event := Event) ⟨.done value, []⟩ [] value :=
    ⟨[], value, [], Runs.done, Continues.done, rfl⟩
  obtain ⟨first, middle, rest, run, remaining, trace⟩ := denotes_before_path path final
  cases remaining
  have same : events = first := by simpa using trace
  exact same.symm ▸ run

/-- Recursive child semantics and explicit frames have identical finite traces. -/
theorem runs_iff_path : Runs work events value ↔
    ∃ count, Path ⟨work, []⟩ events count ⟨.done value, []⟩ :=
  ⟨fun run => runs_path run [], fun ⟨_, path⟩ => runs_of_path path⟩

/-- The executable driver realizes every finite recursive derivation. -/
theorem advance_refines_runs (run : Runs work events value) :
    ∃ fuel, advance fuel ⟨work, []⟩ = (events, ⟨.done value, []⟩) := by
  obtain ⟨fuel, path⟩ := runs_path run []
  exact ⟨fuel, advance_of_path path⟩

theorem denotes_before_advance (fuel : Nat) (state : State Value Event)
    (after : Denotes (advance fuel state).2 suffix result) :
    Denotes state ((advance fuel state).1 ++ suffix) result := by
  induction fuel generalizing state with
  | zero => simpa [advance] using after
  | succ fuel ih =>
      cases observed : transition state with
      | none => simpa [advance, observed] using after
      | some next =>
          rcases next with ⟨events, target⟩
          have tail : Denotes (advance fuel target).2 suffix result := by
            simpa [advance, observed] using after
          simpa [advance, observed, List.append_assoc] using
            denotes_before_step (step_of_transition observed) (ih target tail)

theorem runs_of_advance {work : Program Value Event}
    (finished : advance fuel ⟨work, []⟩ = (events, ⟨.done value, []⟩)) :
    Runs work events value := by
  have final : Denotes (advance fuel ⟨work, []⟩).2 [] value := by
    rw [finished]
    exact ⟨[], value, [], Runs.done, Continues.done, rfl⟩
  obtain ⟨first, middle, rest, run, remaining, trace⟩ :=
    denotes_before_advance fuel ⟨work, []⟩ final
  cases remaining
  have same : events = first := by simpa [finished] using trace
  exact same.symm ▸ run

theorem runs_iff_advance {work : Program Value Event} : Runs work events value ↔
    ∃ fuel, advance fuel ⟨work, []⟩ = (events, ⟨.done value, []⟩) :=
  ⟨advance_refines_runs, fun ⟨_, finished⟩ => runs_of_advance finished⟩

/-- Resuming a residual concatenates traces; already observed events are not replayed. -/
theorem advance_add (first rest : Nat) (state : State Value Event) :
    advance (first + rest) state =
      let earlier := advance first state
      let suffix := advance rest earlier.2
      (earlier.1 ++ suffix.1, suffix.2) := by
  induction first generalizing state with
  | zero => simp [advance]
  | succ first ih =>
      cases observed : transition state with
      | none =>
          have stopped : ∀ n, advance n state = ([], state) := by
            intro n
            cases n <;> simp [advance, observed]
          simp [stopped]
      | some next =>
          rcases next with ⟨events, target⟩
          simp [Nat.succ_add, advance, observed, ih, List.append_assoc]

def nested : Nat → Program Nat Nat
  | 0 => .done 0
  | n + 1 => .child (nested n) (fun value => .done (value + 1))

theorem nested_runs (depth : Nat) : Runs (nested depth) [] depth := by
  induction depth with
  | zero => exact Runs.done
  | succ depth ih => simpa [nested] using Runs.child ih (Runs.done (value := depth + 1))

theorem arbitrary_depth (depth : Nat) :
    ∃ fuel, advance fuel ⟨nested depth, []⟩ = ([], ⟨.done depth, []⟩) :=
  advance_refines_runs (nested_runs depth)

def exampleProgram : Program Nat Nat :=
  .child (.emit 1 (.done 2)) (fun value => .emit 1 (.emit 3 (.done (value + 4))))

example : (advance 10 ⟨exampleProgram, []⟩).1 = [1, 1, 3] := rfl
example : (advance 10 ⟨exampleProgram, []⟩).2.work = .done 6 := rfl
example : (advance 10 ⟨exampleProgram, []⟩).1 ≠ [1, 3] := by decide
example : (advance 10 ⟨exampleProgram, []⟩).1 ≠ [3, 1, 1] := by decide

end Mettapedia.Machines.OwnedPullDriver
