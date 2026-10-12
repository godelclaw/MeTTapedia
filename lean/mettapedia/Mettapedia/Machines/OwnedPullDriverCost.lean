import Mettapedia.Machines.OwnedPullDriver
import Mettapedia.Machines.ResumableRegion
import Mettapedia.Machines.SnapshotBatch

/-!
# Transition and frame bounds for the owned pull driver

The recursive semantics counts child invocations and maximum active child
nesting independently of the driver. Each invocation contributes one push
and one return; each event contributes one transition. Every intermediate
driver state is bounded by its initial frames plus the semantic nesting depth.

These are unit-cost transition and frame-count bounds. They do not bound
the work performed by a callback, the size of an event or captured values,
the storage of the returned trace, or native allocation and representation.

The same driver also inhabits `MachineCore`. Its ordinary bounded execution
keeps the complete work and frame state without retaining a trace. The
comparison with `advance` recovers the exact residual, and the semantic
derivation supplies the number of transitions actually taken. Reaching a
child's return with pending frames is not completion of the whole computation.
-/

namespace Mettapedia.Machines.OwnedPullDriver

universe u v

variable {Value : Type u} {Event : Type v}

/-- Recursive execution with the number of calls and peak active nesting. -/
inductive CostedRuns : Program Value Event → List Event → Value → Nat → Nat → Prop where
  | done : CostedRuns (.done value) [] value 0 0
  | emit (tail : CostedRuns next events value calls depth) :
      CostedRuns (.emit event next) (event :: events) value calls depth
  | child (inner : CostedRuns work first value innerCalls innerDepth)
      (outer : CostedRuns (resume value) rest result outerCalls outerDepth) :
      CostedRuns (.child work resume) (first ++ rest) result
        (innerCalls + outerCalls + 1) (max (innerDepth + 1) outerDepth)

theorem CostedRuns.erase (run : CostedRuns work events value calls depth) :
    Runs work events value := by
  induction run with
  | done => exact Runs.done
  | emit _ ih => exact Runs.emit ih
  | child _ _ innerIH outerIH => exact Runs.child innerIH outerIH

/-- Every finite semantic derivation admits these cost annotations. -/
theorem Runs.costed (run : Runs work events value) :
    ∃ calls depth, CostedRuns work events value calls depth := by
  induction run with
  | done => exact ⟨0, 0, CostedRuns.done⟩
  | emit _ ih =>
      obtain ⟨calls, depth, tail⟩ := ih
      exact ⟨calls, depth, CostedRuns.emit tail⟩
  | child _ _ innerIH outerIH =>
      obtain ⟨innerCalls, innerDepth, inner⟩ := innerIH
      obtain ⟨outerCalls, outerDepth, outer⟩ := outerIH
      exact ⟨_, _, CostedRuns.child inner outer⟩

/-- An actual driver path whose every visited state obeys a frame bound. -/
inductive PathWithin (bound : Nat) :
    State Value Event → List Event → Nat → State Value Event → Prop where
  | refl (fits : state.frames.length ≤ bound) : PathWithin bound state [] 0 state
  | next (fits : source.frames.length ≤ bound)
      (step : Step source first middle)
      (tail : PathWithin bound middle rest count target) :
      PathWithin bound source (first ++ rest) (count + 1) target

theorem PathWithin.erase (path : PathWithin bound source events count target) :
    Path source events count target := by
  induction path with
  | refl => exact Path.refl
  | next _ step _ ih => exact Path.next step ih

theorem PathWithin.weaken (path : PathWithin bound source events count target)
    (larger : bound ≤ other) : PathWithin other source events count target := by
  induction path with
  | refl fits => exact PathWithin.refl (Nat.le_trans fits larger)
  | next fits step _ ih => exact PathWithin.next (Nat.le_trans fits larger) step ih

theorem PathWithin.append (first : PathWithin bound source earlier m middle)
    (rest : PathWithin bound middle suffix n target) :
    PathWithin bound source (earlier ++ suffix) (m + n) target := by
  induction first generalizing suffix n target with
  | refl => simpa using rest
  | next fits step _ ih =>
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        PathWithin.next fits step (ih rest)

/-- Two administrative transitions per child, one per event, at bounded depth. -/
theorem CostedRuns.driver (run : CostedRuns work events value calls depth)
    (frames : List (Value → Program Value Event)) :
    PathWithin (frames.length + depth) ⟨work, frames⟩ events
      (events.length + 2 * calls) ⟨.done value, frames⟩ := by
  induction run generalizing frames with
  | done =>
      simpa using PathWithin.refl (state := ⟨.done _, frames⟩) (Nat.le_refl frames.length)
  | emit tail ih =>
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        PathWithin.next (Nat.le_add_right frames.length _) Step.emit (ih frames)
  | @child work first value innerCalls innerDepth resume rest result outerCalls outerDepth
      inner outer innerIH outerIH =>
      let bound := frames.length + max (innerDepth + 1) outerDepth
      have innerBound : (resume :: frames).length + innerDepth ≤ bound := by
        dsimp [bound]
        omega
      have outerBound : frames.length + outerDepth ≤ bound := by
        dsimp [bound]
        omega
      have entryBound : frames.length ≤ bound := by
        dsimp [bound]
        omega
      have returnBound : (resume :: frames).length ≤ bound := by
        dsimp [bound]
        omega
      have innerPath := (innerIH (resume :: frames)).weaken innerBound
      have outerPath := (outerIH frames).weaken outerBound
      have firstPath := PathWithin.next entryBound Step.child innerPath
      have restPath := PathWithin.next returnBound Step.resume outerPath
      have cost : (first.length + 2 * innerCalls + 1) +
          (rest.length + 2 * outerCalls + 1) =
          (first ++ rest).length + 2 * (innerCalls + outerCalls + 1) := by
        simp only [List.length_append]
        omega
      simpa only [cost, List.nil_append] using firstPath.append restPath

theorem CostedRuns.executes (run : CostedRuns work events value calls depth)
    (frames : List (Value → Program Value Event)) :
    advance (events.length + 2 * calls) ⟨work, frames⟩ =
      (events, ⟨.done value, frames⟩) :=
  advance_of_path (run.driver frames).erase

/-- Control steps are at most twice the number of events and child invocations. -/
theorem CostedRuns.linear_steps (run : CostedRuns work events value calls depth)
    (frames : List (Value → Program Value Event)) :
    ∃ count, count ≤ 2 * (events.length + calls) ∧
      PathWithin (frames.length + depth) ⟨work, frames⟩ events count
        ⟨.done value, frames⟩ := by
  exact ⟨events.length + 2 * calls, by omega, run.driver frames⟩

theorem nested_costed (depth : Nat) :
    CostedRuns (nested depth) [] depth depth depth := by
  induction depth with
  | zero => exact CostedRuns.done
  | succ depth ih =>
      simpa [nested] using CostedRuns.child
        (resume := fun value => .done (value + 1)) ih
        (CostedRuns.done (value := depth + 1))

theorem nested_exact_steps (depth : Nat) :
    advance (2 * depth) ⟨nested depth, []⟩ = ([], ⟨.done depth, []⟩) := by
  simpa using (nested_costed depth).executes []

/-- Splitting at any event or administrative boundary retains the exact result. -/
theorem CostedRuns.split_execution (run : CostedRuns work events value calls depth)
    (frames : List (Value → Program Value Event)) (first rest : Nat)
    (split : first + rest = events.length + 2 * calls) :
    let earlier := advance first ⟨work, frames⟩
    let suffix := advance rest earlier.2
    (earlier.1 ++ suffix.1, suffix.2) = (events, ⟨.done value, frames⟩) := by
  have combined := advance_add first rest (State.mk work frames)
  rw [split] at combined
  exact combined.symm.trans (run.executes frames)

/-! ## The common bounded-run interface -/

/-- The unrecorded driver does not construct an event list. The work and
every pending continuation remain in the machine state. -/
def machineCore (Value Event : Type) : MachineCore (Program Value Event) where
  State := State Value Event
  load work := ⟨work, []⟩
  step state :=
    match state.work, state.frames with
    | .done _, [] => none
    | .done value, resume :: rest => some ⟨resume value, rest⟩
    | .emit _ next, frames => some ⟨next, frames⟩
    | .child work resume, frames => some ⟨work, resume :: frames⟩

/-- The unrecorded transition has exactly the traced driver's next state. -/
theorem machineCore_step {Value Event : Type} (state : State Value Event) :
    (machineCore Value Event).step state = (transition state).map Prod.snd := by
  rcases state with ⟨work, frames⟩
  cases work <;> cases frames <;> rfl

/-- An internal return remains live until its caller's frames are discharged. -/
theorem machineCore_final_iff {Value Event : Type} (state : State Value Event) :
    (machineCore Value Event).step state = none ↔
      ∃ value, state.work = .done value ∧ state.frames = [] := by
  rcases state with ⟨work, frames⟩
  cases work <;> cases frames <;> simp [machineCore]

/-- Trace-free execution and the independently defined traced driver keep
exactly the same residual, including after a partial child computation. -/
theorem runSlice_state_eq_advance {Value Event : Type} (fuel : Nat)
    (state : State Value Event) :
    (MachineCore.runSlice (machineCore Value Event) fuel state).1 =
      (advance fuel state).2 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases observed : transition state with
      | none =>
          simp only [MachineCore.runSlice, machineCore_step, advance, observed,
            Option.map_none]
          rfl
      | some next =>
          rcases next with ⟨events, next⟩
          simpa [MachineCore.runSlice, machineCore_step, advance, observed] using ih next

/-- A source path charges each actual transition once through the common
runner. Event count alone would omit child entry and return transitions. -/
theorem Path.runSlice {Value Event : Type} {source target : State Value Event}
    {events : List Event} {count : Nat} (path : Path source events count target) :
    MachineCore.runSlice (machineCore Value Event) count source = (target, count) := by
  induction path with
  | refl => rfl
  | next step tail ih =>
      simp only [MachineCore.runSlice, machineCore_step, transition_of_step step,
        Option.map_some]
      exact congrArg (fun result : State Value Event × Nat => (result.1, result.2 + 1)) ih

/-- The semantic cost derivation gives the exact debit and full endpoint of
the ordinary runner; no event recording is needed to execute this instance. -/
theorem CostedRuns.runSlice {Value Event : Type} {work : Program Value Event}
    {events : List Event} {value : Value} {calls depth : Nat}
    (run : CostedRuns work events value calls depth)
    (frames : List (Value → Program Value Event)) :
    MachineCore.runSlice (machineCore Value Event) (events.length + 2 * calls)
      ⟨work, frames⟩ = (⟨.done value, frames⟩, events.length + 2 * calls) :=
  (run.driver frames).erase.runSlice

/-- Unused allowance after root completion is not charged. -/
theorem CostedRuns.runSlice_after_completion {Value Event : Type}
    {work : Program Value Event} {events : List Event} {value : Value}
    {calls depth : Nat} (run : CostedRuns work events value calls depth) (extra : Nat) :
    MachineCore.runSlice (machineCore Value Event) (events.length + 2 * calls + extra)
      ⟨work, []⟩ = (⟨.done value, []⟩, events.length + 2 * calls) := by
  have combined := MachineCore.runSlice_add (machineCore Value Event)
    (events.length + 2 * calls) extra ⟨work, []⟩
  rw [run.runSlice []] at combined
  have final : (machineCore Value Event).step ⟨.done value, []⟩ = none := rfl
  simpa only [MachineCore.runSlice_of_final _ _ final, Nat.add_zero] using combined

/-- A producer's value may already exist while its observer is still pending.
One tick resumes that observer rather than declaring the whole run final. -/
theorem runSlice_pending_return {Value Event : Type} (value : Value)
    (resume : Value → Program Value Event) (frames : List (Value → Program Value Event)) :
    MachineCore.runSlice (machineCore Value Event) 1 ⟨.done value, resume :: frames⟩ =
      (⟨resume value, frames⟩, 1) := rfl

theorem pending_return_not_final {Value Event : Type} (value : Value)
    (resume : Value → Program Value Event) (frames : List (Value → Program Value Event)) :
    (machineCore Value Event).step ⟨.done value, resume :: frames⟩ ≠ none := by
  simp [machineCore]

/-! ## Independently owned child quanta

The existing private-write kernel can schedule this driver directly. Its
private value contains the whole pending program, caller frames and cumulative
transition debit. Programs and their captured environments belong to that
invocation; this construction does not license aliased mutable native programs
or access to a shared producer. No trace is allocated by these quanta.
-/

/-- Resume a paid invocation without restarting it or charging unused fuel. -/
def paidSlice {Value Event : Type} (fuel : Nat) (packet : Nat × State Value Event) :
    Nat × State Value Event :=
  let result := MachineCore.runSlice (machineCore Value Event) fuel packet.2
  (packet.1 + result.2, result.1)

@[simp] theorem paidSlice_zero {Value Event : Type} (packet : Nat × State Value Event) :
    paidSlice 0 packet = packet := by
  simp [paidSlice, MachineCore.runSlice]

/-- Full residual and cumulative charge compose, including internal returns. -/
theorem paidSlice_add {Value Event : Type} (first second : Nat)
    (packet : Nat × State Value Event) :
    paidSlice (first + second) packet = paidSlice second (paidSlice first packet) := by
  have combined := MachineCore.runSlice_add (machineCore Value Event) first second packet.2
  have paid := congrArg (fun result : State Value Event × Nat =>
    (packet.1 + result.2, result.1)) combined
  simpa only [paidSlice, Nat.add_assoc] using paid

theorem paidSlice_debit_bounds {Value Event : Type} (fuel : Nat)
    (packet : Nat × State Value Event) :
    packet.1 ≤ (paidSlice fuel packet).1 ∧
      (paidSlice fuel packet).1 ≤ packet.1 + fuel := by
  have bounded := MachineCore.runSlice_used_le (machineCore Value Event) fuel packet.2
  dsimp only [paidSlice]
  omega

/-- A return is publishable only after this invocation's caller frames are empty. -/
def completedValue {Value Event : Type} (state : State Value Event) : Option Value :=
  match state.work, state.frames with
  | .done value, [] => some value
  | _, _ => none

theorem completedValue_iff {Value Event : Type} (state : State Value Event) (value : Value) :
    completedValue state = some value ↔ state = ⟨.done value, []⟩ := by
  rcases state with ⟨work, frames⟩
  cases work <;> cases frames <;> simp [completedValue]

/-- The child program has its own cost derivation; the parent's number of
ready instructions supplies no bound on these internal transitions. -/
theorem CostedRuns.paidSlice {Value Event : Type} {work : Program Value Event}
    {events : List Event} {value : Value} {calls depth : Nat}
    (run : CostedRuns work events value calls depth) (spent extra : Nat) :
    paidSlice (events.length + 2 * calls + extra) (spent, ⟨work, []⟩) =
      (spent + events.length + 2 * calls, ⟨.done value, []⟩) := by
  unfold OwnedPullDriver.paidSlice
  rw [run.runSlice_after_completion extra]
  simp only [Nat.add_assoc]

/-- An item addresses one invocation and supplies its next quantum. The
snapshot and seed are unused because each packet already holds its program. -/
def paidKernel (Id Value Event : Type) :
    SnapshotBatch.Kernel Unit (Id × Nat) Unit Id (Nat × State Value Event) :=
  SnapshotBatch.Kernel.fromOwnerAction (fun _ fuel packet => paidSlice fuel packet)

/-- Any interleaving preserving each owner's command sequence keeps the
complete paid pool. This includes unfinished recursive children. -/
theorem paidKernel_interleaving {Id Value Event : Type} [DecidableEq Id]
    (pool : Id → Nat × State Value Event) (first second : List (Id × Nat))
    (same : ∀ owner, first.filter (fun item => decide (item.1 = owner)) =
      second.filter (fun item => decide (item.1 = owner))) :
    (paidKernel Id Value Event).run () (fun _ => ()) pool first =
      (paidKernel Id Value Event).run () (fun _ => ()) pool second :=
  SnapshotBatch.Kernel.run_eq_of_owner_sequences _ _ _ _ _ _ same

/-- Disjoint private preparation and arbitrary worker partition preserve
exactly the sequential paid states. Installation does not step a child. -/
theorem paidKernel_partitioned {Id Value Event : Type} [DecidableEq Id]
    (pool : Id → Nat × State Value Event) (parts : List (List (Id × Nat)))
    (schedule : List (Id × Nat)) (coverage : parts.flatten.Perm schedule)
    (distinct : (schedule.map Prod.fst).Nodup) :
    (paidKernel Id Value Event).partitioned () (fun _ => ()) pool parts =
      (paidKernel Id Value Event).run () (fun _ => ()) pool schedule :=
  SnapshotBatch.Kernel.partitioned_eq_run _ _ _ _ _ _ coverage distinct


/-- Fixed private-machine grants may be fused. The equality retains cumulative
charge and every unfinished child/caller frame; emitted history is a separate
observer. It does not apply to stateful callback acceptance allowances. -/
theorem paidSlice_foldl {Value Event : Type} (grants : List Nat)
    (packet : Nat × State Value Event) :
    grants.foldl (fun current grant => paidSlice grant current) packet =
      paidSlice grants.sum packet := by
  induction grants generalizing packet with
  | nil => simp
  | cons first rest ih =>
      rw [List.foldl_cons, ih, List.sum_cons]
      exact (paidSlice_add first rest.sum packet).symm

/-- Per-owner scheduler grants act on the original complete private packet.
Equal total allocation preserves its actual debit and residual at this fixed
machine boundary, independently of other owners' interleaving. -/
theorem paidKernel_run_at_owner {Id Value Event : Type} [DecidableEq Id]
    (pool : Id → Nat × State Value Event) (schedule : List (Id × Nat)) (owner : Id) :
    (paidKernel Id Value Event).run () (fun _ => ()) pool schedule owner =
      paidSlice ((schedule.filter (fun item => decide (item.1 = owner))).map Prod.snd).sum
        (pool owner) := by
  rw [SnapshotBatch.Kernel.run_at_location]
  change (schedule.filter (fun item : Id × Nat => decide (item.1 = owner))).foldl
    (fun current item => paidSlice item.2 current) (pool owner) = _
  have fused := paidSlice_foldl (Value := Value) (Event := Event)
    ((schedule.filter (fun item => decide (item.1 = owner))).map Prod.snd) (pool owner)
  rw [List.foldl_map] at fused
  exact fused

theorem paidKernel_owner_debit_bounds {Id Value Event : Type} [DecidableEq Id]
    (pool : Id → Nat × State Value Event) (schedule : List (Id × Nat)) (owner : Id) :
    (pool owner).1 ≤ ((paidKernel Id Value Event).run () (fun _ => ()) pool schedule owner).1 ∧
      ((paidKernel Id Value Event).run () (fun _ => ()) pool schedule owner).1 ≤
        (pool owner).1 + ((schedule.filter (fun item => decide (item.1 = owner))).map Prod.snd).sum := by
  rw [paidKernel_run_at_owner]
  exact paidSlice_debit_bounds _ _

/-- Ordered local grant chunks use the same private kernel and whole-store
partition law. A chunk's commands must address its stated owner; equal payload
values do not establish ownership. -/
theorem paidKernel_grouped {Id Value Event : Type} [DecidableEq Id]
    (pool : Id → Nat × State Value Event)
    (parts : List (List (Id × List (Id × Nat)))) (chunks : List (Id × List (Id × Nat)))
    (coverage : parts.flatten.Perm chunks) (distinct : (chunks.map Prod.fst).Nodup)
    (owned : ∀ chunk ∈ chunks, ∀ item ∈ chunk.2, item.1 = chunk.1) :
    ((paidKernel Id Value Event).grouped () (fun _ => ())).partitioned () (fun _ => ()) pool parts =
      (paidKernel Id Value Event).run () (fun _ => ()) pool (chunks.flatMap Prod.snd) :=
  SnapshotBatch.Kernel.grouped_partitioned _ _ _ _ _ _ coverage distinct owned

namespace GrantControls
private def pool : Nat → Nat × State Nat Nat := fun owner => (owner,⟨exampleProgram,[]⟩)

theorem grouped_grants_preserve_child_work_and_unused_allowance :
    let result := ((paidKernel Nat Nat Nat).grouped () (fun _ => ())).partitioned
      () (fun _ => ()) pool [[(0,[(0,1),(0,1),(0,3)])],[(1,[(1,2),(1,0),(1,4)])]]
    result 0 = ⟨5,⟨.done 6,[]⟩⟩ ∧ result 1 = ⟨6,⟨.done 6,[]⟩⟩ := by
  constructor <;> rfl
end GrantControls

theorem exampleProgram_costed : CostedRuns exampleProgram [1, 1, 3] 6 1 1 :=
  CostedRuns.child
    (resume := fun value => .emit 1 (.emit 3 (.done (value + 4))))
    (CostedRuns.emit (CostedRuns.done (value := 2)))
    (CostedRuns.emit (CostedRuns.emit CostedRuns.done))

example : (advance 1 ⟨exampleProgram, []⟩).1 = [] := rfl
example : (advance 2 ⟨exampleProgram, []⟩).1 = [1] := rfl
example : (advance 2 (advance 2 ⟨exampleProgram, []⟩).2).1 = [1] := rfl
example : (advance 2 ⟨nested 2, []⟩).2.frames.length = 2 := rfl
example : ¬ (advance 2 ⟨nested 2, []⟩).2.frames.length ≤ 1 := by decide

-- A large allowance charges three emissions plus child entry and return.
example : MachineCore.runSlice (machineCore Nat Nat) 25 ⟨exampleProgram, []⟩ =
    (⟨.done 6, []⟩, 5) := by
  simpa using exampleProgram_costed.runSlice_after_completion 20

-- The child has returned after two ticks, but its caller still has work.
example : (MachineCore.runSlice (machineCore Nat Nat) 2 ⟨exampleProgram, []⟩).1.work =
    .done 2 := rfl

example : (machineCore Nat Nat).step
    (MachineCore.runSlice (machineCore Nat Nat) 2 ⟨exampleProgram, []⟩).1 ≠ none := by
  simp [MachineCore.runSlice, machineCore, exampleProgram]

-- A pause at that return resumes the observer and keeps the total debit.
example :
    let earlier := MachineCore.runSlice (machineCore Nat Nat) 2 ⟨exampleProgram, []⟩
    let later := MachineCore.runSlice (machineCore Nat Nat) 3 earlier.1
    (later.1, earlier.2 + later.2) = (⟨.done 6, []⟩, 5) := rfl

-- Forgetting events is allowed for this runner, but is not faithful replay.
theorem erased_account_cannot_recover_event_trace :
    MachineCore.runSlice (machineCore Nat Nat) 1 ⟨.emit 1 (.done 6), []⟩ =
      MachineCore.runSlice (machineCore Nat Nat) 1 ⟨.emit 2 (.done 6), []⟩ ∧
    (advance 1 (⟨.emit 1 (.done 6), []⟩ : State Nat Nat)).1 ≠
      (advance 1 (⟨.emit 2 (.done 6), []⟩ : State Nat Nat)).1 := by
  exact ⟨rfl, by decide⟩


#print axioms paidSlice_foldl
#print axioms paidKernel_run_at_owner
#print axioms paidKernel_owner_debit_bounds
#print axioms paidKernel_grouped
#print axioms GrantControls.grouped_grants_preserve_child_work_and_unused_allowance
#print axioms erased_account_cannot_recover_event_trace

end Mettapedia.Machines.OwnedPullDriver
