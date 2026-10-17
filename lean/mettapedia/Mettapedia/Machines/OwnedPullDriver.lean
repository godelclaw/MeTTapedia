import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mettapedia.Coalgebra.CoherentPrefixTower

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

`Session` retains the driver residual, an interpreted world and the complete
committed trace. Continuation interprets only newly emitted events;
cancellation drops pending work while retaining its committed history. These
are sequential semantic laws for a supplied effect handler.

`Owned.Host` adds exclusive authority for any retained computation whose
committed effects grow by prefix. Requests carry an epoch ticket; only the
current ticket is served, and serving it moves the epoch. In every reachable
host, under arbitrary interleavings of current, stale and copied tickets, the
delivered history is the retained state's committed history and the world
interprets it exactly once (`Owned.Host.Reached.accounts`). A used ticket and
all its copies are refused (`used_ticket_refused`, `copies_act_once`), the
holder's cancellation retires the continuation and keeps the world
(`cancelled_refuses`), and consecutive tickets slice a runner's budget exactly
(`submit_add`). Copying retained data stays a private fork; new authority over
old data is a restart and repeats effects (the controls). Durable storage and
crash recovery remain host obligations.

Independence of owners is a condition on effects, not on traces: when every
effect of one owner commutes with every effect of another, any interleaving of
their delivered histories reaches the same shared world (`interpret_interleaving`,
`Owned.Host.shared_world`), while each owner keeps its own order. Without the
condition the interleaving is observable (the controls).
-/

namespace Mettapedia.Machines.OwnedPullDriver

universe u v w

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

/-- A settled driver executes no further transition at any budget. -/
theorem advance_stopped (state : State Value Event)
    (stopped : transition state = none) (fuel : Nat) :
    advance fuel state = ([], state) := by
  cases fuel <;> simp [advance, stopped]

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
          simp [advance_stopped state observed]
      | some next =>
          rcases next with ⟨events, target⟩
          simp [Nat.succ_add, advance, observed, ih, List.append_assoc]

/-! ## Interpreting fresh effects and retaining cancelled sessions -/

variable {World : Type w}

/-- Interpret the ordered event list, retaining every occurrence. -/
def interpret (action : Event → World → World) (events : List Event) (world : World) :
    World :=
  events.foldl (fun current event => action event current) world

@[simp] theorem interpret_nil (action : Event → World → World) (world : World) :
    interpret action [] world = world := rfl

@[simp] theorem interpret_cons (action : Event → World → World)
    (event : Event) (events : List Event) (world : World) :
    interpret action (event :: events) world = interpret action events (action event world) :=
  rfl

theorem interpret_append (action : Event → World → World)
    (first rest : List Event) (world : World) :
    interpret action (first ++ rest) world = interpret action rest (interpret action first world) :=
  List.foldl_append

/-- Each event appends one occurrence of the same item. The item is not
concatenated with itself inside that occurrence. -/
theorem interpret_repeat_item {Event Item : Type*} (item : Item)
    (events : List Event) (origin : List Item) :
    interpret (fun _event world => world ++ [item]) events origin =
      origin ++ events.map (fun _ => item) := by
  induction events generalizing origin with
  | nil => simp [interpret_nil]
  | cons _event rest ih =>
      simp only [interpret_cons, List.map_cons, ih, List.append_assoc,
        List.singleton_append]

/-- A product world keeps its first component and appends one observation per
event. The two components are not identified by this equation. -/
theorem interpret_pair_appends {Event Custody Observation : Type*}
    (item : Observation) (events : List Event)
    (origin : Custody × List Observation) :
    interpret (fun _event world => (world.1, world.2 ++ [item])) events origin =
      (origin.1, origin.2 ++ events.map (fun _ => item)) := by
  induction events generalizing origin with
  | nil => simp only [interpret_nil, List.map_nil, List.append_nil]
  | cons _event rest ih =>
      simp only [interpret_cons, ih, List.map_cons, List.append_assoc,
        List.singleton_append]

/-- Independence concerns the interpreted world, not equality of ordered traces. -/
theorem interpret_independent_swap (action : Event → World → World)
    (first second : Event)
    (independent : ∀ world, action second (action first world) =
      action first (action second world))
    (before after : List Event) (world : World) :
    interpret action (before ++ first :: second :: after) world =
      interpret action (before ++ second :: first :: after) world := by
  simp only [interpret_append, interpret_cons]
  rw [independent]

/-- Commuting world actions permit a world-level permutation quotient. The
session still records the original event order and multiplicity. -/
theorem interpret_perm (action : Event → World → World)
    (independent : ∀ first second world, action second (action first world) =
      action first (action second world))
    {first second : List Event} (permutation : first.Perm second) (world : World) :
    interpret action first world = interpret action second world := by
  let : RightCommutative (fun current event => action event current) :=
    ⟨fun current first second => independent first second current⟩
  change first.foldl (fun current event => action event current) world =
    second.foldl (fun current event => action event current) world
  exact permutation.foldl_eq world

/-- An action of one owner commutes past a whole history of the other. -/
theorem interpret_commute_past {Left Right : Type*} (actLeft : Left → World → World)
    (actRight : Right → World → World)
    (cross : ∀ left right world, actLeft left (actRight right world) = actRight right (actLeft left world))
    (right : Right) (lefts : List Left) (world : World) :
    interpret actLeft lefts (actRight right world) = actRight right (interpret actLeft lefts world) := by
  induction lefts generalizing world with
  | nil => rfl
  | cons left rest ih =>
      simp only [interpret_cons]
      rw [cross, ih]

/-- **Independence of two owners.** When every effect of one owner commutes
with every effect of the other, a world receiving any interleaving of their
ordered histories is the world receiving the first owner's history and then
the second's. Each owner's own order is kept: effects of one owner need not
commute with each other. -/
theorem interpret_interleaving {Left Right : Type*} (actLeft : Left → World → World)
    (actRight : Right → World → World)
    (cross : ∀ left right world, actLeft left (actRight right world) = actRight right (actLeft left world))
    (events : List (Left ⊕ Right)) (world : World) :
    interpret (Sum.elim actLeft actRight) events world =
      interpret actRight (events.filterMap Sum.getRight?)
        (interpret actLeft (events.filterMap Sum.getLeft?) world) := by
  induction events generalizing world with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | inl left =>
          simp only [interpret_cons, Sum.elim_inl, List.filterMap_cons, Sum.getLeft?_inl,
            Sum.getRight?_inl]
          exact ih (actLeft left world)
      | inr right =>
          simp only [interpret_cons, Sum.elim_inr, List.filterMap_cons, Sum.getLeft?_inr,
            Sum.getRight?_inr]
          rw [ih, interpret_commute_past actLeft actRight cross]

/-- Pending work is separate from committed state. A cancelled session has no
residual; a normally completed session retains its final driver state. -/
structure Session (Value : Type u) (Event : Type v) (World : Type w) where
  residual : Option (State Value Event)
  world : World
  committed : List Event

namespace Session

/-- Start a driver without interpreting or pre-committing any event. -/
def begin (work : Program Value Event) (world : World) : Session Value Event World :=
  ⟨some ⟨work, []⟩, world, []⟩

/-- Continue the existing residual and interpret only its fresh event suffix. -/
def resume (action : Event → World → World) (fuel : Nat)
    (session : Session Value Event World) : Session Value Event World :=
  match session.residual with
  | none => session
  | some state =>
      let advanced := advance fuel state
      ⟨some advanced.2, interpret action advanced.1 session.world,
        session.committed ++ advanced.1⟩

@[simp] theorem resume_zero (action : Event → World → World)
    (session : Session Value Event World) : resume action 0 session = session := by
  cases session with
  | mk residual world committed =>
      cases residual <;> simp [resume, advance, interpret]

/-- Slicing the budget preserves the complete residual, world and committed
history, including effects that are not idempotent. -/
theorem resume_add (action : Event → World → World) (first extra : Nat)
    (session : Session Value Event World) :
    resume action (first + extra) session =
      resume action extra (resume action first session) := by
  cases session with
  | mk residual world committed =>
      cases residual <;> simp [resume, advance_add, interpret_append, List.append_assoc]

theorem resume_committed_prefix (action : Event → World → World) (fuel : Nat)
    (session : Session Value Event World) :
    session.committed.IsPrefix (resume action fuel session).committed := by
  cases session with
  | mk residual world committed =>
      cases residual with
      | none => exact ⟨[], by simp [resume]⟩
      | some state => exact ⟨(advance fuel state).1, rfl⟩

/-- The history remains a complete account of the interpreted world when it
was a complete account before continuation. -/
theorem resume_world_history (action : Event → World → World) (fuel : Nat)
    (session : Session Value Event World) (origin : World)
    (accounted : session.world = interpret action session.committed origin) :
    (resume action fuel session).world =
      interpret action (resume action fuel session).committed origin := by
  cases session with
  | mk residual world committed =>
      cases residual <;> simp_all [resume, interpret_append]

/-- Cancellation executes no pending work and does not undo committed effects. -/
def cancel (session : Session Value Event World) : Session Value Event World :=
  { session with residual := none }

@[simp] theorem cancel_residual (session : Session Value Event World) :
    session.cancel.residual = none := rfl

@[simp] theorem cancel_world (session : Session Value Event World) :
    session.cancel.world = session.world := rfl

@[simp] theorem cancel_committed (session : Session Value Event World) :
    session.cancel.committed = session.committed := rfl

@[simp] theorem cancel_idempotent (session : Session Value Event World) :
    session.cancel.cancel = session.cancel := rfl

@[simp] theorem resume_cancelled (action : Event → World → World) (fuel : Nat)
    (session : Session Value Event World) :
    resume action fuel session.cancel = session.cancel := rfl

theorem resume_settled (action : Event → World → World) (fuel : Nat)
    (session : Session Value Event World) (state : State Value Event)
    (retained : session.residual = some state) (stopped : transition state = none) :
    resume action fuel session = session := by
  cases session with
  | mk residual world committed =>
      simp only at retained
      subst residual
      simp [resume, advance_stopped state stopped]

/-- The independent recursive semantics supplies the complete event trace
interpreted by a finishing session. -/
theorem refines_runs (action : Event → World → World) (world : World)
    {work : Program Value Event} {events : List Event} {value : Value}
    (run : Runs work events value) :
    ∃ fuel, resume action fuel (begin work world) =
      ⟨some ⟨.done value, []⟩, interpret action events world, events⟩ := by
  obtain ⟨fuel, finished⟩ := advance_refines_runs run
  exact ⟨fuel, by simp [resume, begin, finished]⟩

/-- This is the shared continuation interface applied to the actual driver. -/
def trajectory (action : Event → World → World) (session : Session Value Event World) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory (resume action) session :=
  Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory.canonical
    (resume action) session (resume_zero action) (resume_add action)

theorem trajectory_committed_prefix (action : Event → World → World)
    (session : Session Value Event World) (first extra : Nat) :
    ((trajectory action session).observation first).committed.IsPrefix
      ((trajectory action session).observation (first + extra)).committed :=
  (trajectory action session).observer_prefix_after_resume
    Session.committed (resume_committed_prefix action) first extra

/-- A cancelled trajectory retains its committed world and history at all budgets. -/
theorem trajectory_cancelled (action : Event → World → World)
    (session : Session Value Event World) (fuel : Nat) :
    (trajectory action session.cancel).observation fuel = session.cancel :=
  resume_cancelled action fuel session

end Session

/-! ## Exclusive authority over a retained continuation

A retained state is data: it can be copied, and a copy is a fork that may be
run on its own. Authority to commit effects to the world is a different thing.
`Owned.Host` keeps the authoritative retained state, the interpreted world, the
complete delivered history and an epoch. A request presents an epoch ticket.
Only the current epoch is accepted, and acceptance moves the epoch, so a ticket
acts at most once and every copy of a used ticket is refused. An accepted
operation delivers exactly the newly committed suffix of the retained state.
Cancellation by the ticket holder retires the continuation and keeps the world.

The theorems hold for every interleaving of requests, with arbitrary tickets
and operations. Durable storage, crash recovery and distributed agreement on
the epoch are host obligations outside this sequential model.
-/

namespace Owned

universe uState uOp uEffect

/-- Operations on retained states whose committed effects grow by prefix.
The effect list is the occurrence history: equal effects stay separate. -/
structure Retained (State : Type uState) (Op : Type uOp) (Effect : Type uEffect) where
  apply : Op → State → State
  committed : State → List Effect
  grows : ∀ op state, (committed state).IsPrefix (committed (apply op state))

/-- The holder of a retained continuation's authority. `retained = none` once
the continuation is retired. -/
structure Host (State : Type uState) (Effect : Type uEffect) (World : Type w) where
  epoch : Nat
  retained : Option State
  world : World
  delivered : List Effect

variable {State : Type uState} {Op : Type uOp} {Effect : Type uEffect}

namespace Host

/-- Take authority over a retained state, delivering its committed history. -/
def begin (system : Retained State Op Effect) (act : Effect → World → World)
    (state : State) (origin : World) : Host State Effect World :=
  ⟨0, some state, interpret act (system.committed state) origin, system.committed state⟩

/-- Serve one request. A current ticket applies the operation to the retained
state, interprets only the fresh committed suffix and moves the epoch. Any
other ticket, and any request to a retired host, changes nothing. -/
def submit (system : Retained State Op Effect) (act : Effect → World → World)
    (ticket : Nat) (op : Op) (host : Host State Effect World) : Host State Effect World :=
  match host.retained with
  | some state =>
      if ticket = host.epoch then
        let fresh := (system.committed (system.apply op state)).drop (system.committed state).length
        ⟨host.epoch + 1, some (system.apply op state), interpret act fresh host.world,
          host.delivered ++ fresh⟩
      else host
  | none => host

/-- The ticket holder retires the continuation. Pending work is dropped
explicitly; committed effects stay. Other tickets change nothing. -/
def cancel (ticket : Nat) (host : Host State Effect World) : Host State Effect World :=
  match host.retained with
  | some _ => if ticket = host.epoch then { host with epoch := host.epoch + 1, retained := none } else host
  | none => host

/-- Reading the retained state is shared and changes nothing. -/
def snapshot (host : Host State Effect World) : Option State := host.retained

/-- The delivered history is the committed history of the retained state, and
the world is the origin with exactly that history interpreted once. -/
structure Accounts (system : Retained State Op Effect) (act : Effect → World → World)
    (origin : World) (host : Host State Effect World) : Prop where
  delivered : ∀ state, host.retained = some state → host.delivered = system.committed state
  world : host.world = interpret act host.delivered origin

theorem begin_accounts (system : Retained State Op Effect) (act : Effect → World → World)
    (state : State) (origin : World) : Accounts system act origin (begin system act state origin) :=
  ⟨fun _ retained => by cases retained; rfl, rfl⟩

theorem submit_stale (system : Retained State Op Effect) (act : Effect → World → World)
    {ticket : Nat} (op : Op) {host : Host State Effect World} (stale : ticket ≠ host.epoch) :
    submit system act ticket op host = host := by
  unfold submit
  cases host.retained <;> simp [stale]

theorem submit_retired (system : Retained State Op Effect) (act : Effect → World → World)
    (ticket : Nat) (op : Op) {host : Host State Effect World} (retired : host.retained = none) :
    submit system act ticket op host = host := by
  simp [submit, retired]

theorem submit_current (system : Retained State Op Effect) (act : Effect → World → World)
    (op : Op) {host : Host State Effect World} {state : State} (retained : host.retained = some state) :
    submit system act host.epoch op host =
      ⟨host.epoch + 1, some (system.apply op state),
        interpret act ((system.committed (system.apply op state)).drop
          (system.committed state).length) host.world,
        host.delivered ++ (system.committed (system.apply op state)).drop
          (system.committed state).length⟩ := by
  simp [submit, retained]

theorem cancel_stale {ticket : Nat} {host : Host State Effect World} (stale : ticket ≠ host.epoch) :
    cancel ticket host = host := by
  unfold cancel
  cases host.retained <;> simp [stale]

theorem cancel_retired (ticket : Nat) {host : Host State Effect World}
    (retired : host.retained = none) : cancel ticket host = host := by
  simp [cancel, retired]

theorem cancel_current {host : Host State Effect World} {state : State}
    (retained : host.retained = some state) :
    cancel host.epoch host = { host with epoch := host.epoch + 1, retained := none } := by
  simp [cancel, retained]

theorem submit_accounts (system : Retained State Op Effect) (act : Effect → World → World)
    {origin : World} (ticket : Nat) (op : Op) {host : Host State Effect World}
    (accounts : Accounts system act origin host) :
    Accounts system act origin (submit system act ticket op host) := by
  by_cases current : ticket = host.epoch
  · cases retained : host.retained with
    | none => rwa [submit_retired system act ticket op retained]
    | some state =>
        subst current
        rw [submit_current system act op retained]
        have previous := accounts.delivered state retained
        refine ⟨?_, ?_⟩
        · intro next same
          cases same
          rw [previous]
          obtain ⟨fresh, grown⟩ := system.grows op state
          rw [← grown]
          simp
        · change interpret act _ host.world = interpret act (host.delivered ++ _) origin
          rw [interpret_append, ← accounts.world]
  · rwa [submit_stale system act op current]

theorem cancel_accounts {system : Retained State Op Effect} {act : Effect → World → World}
    {origin : World} (ticket : Nat) {host : Host State Effect World}
    (accounts : Accounts system act origin host) : Accounts system act origin (cancel ticket host) := by
  by_cases current : ticket = host.epoch
  · cases retained : host.retained with
    | none => simpa [cancel, retained] using accounts
    | some state =>
        subst current
        rw [cancel_current retained]
        exact ⟨fun _ absent => (Option.some_ne_none _ absent.symm).elim, accounts.world⟩
  · rwa [cancel_stale current]

/-- The hosts reachable, after authority was taken over `start`, by arbitrary
requests from any holders of any tickets. -/
inductive Reached (system : Retained State Op Effect) (act : Effect → World → World)
    (origin : World) (start : State) : Host State Effect World → Prop where
  | begin : Reached system act origin start (begin system act start origin)
  | submit {host : Host State Effect World} (ticket : Nat) (op : Op) :
      Reached system act origin start host →
        Reached system act origin start (submit system act ticket op host)
  | cancel {host : Host State Effect World} (ticket : Nat) :
      Reached system act origin start host → Reached system act origin start (cancel ticket host)

/-- **Committed effects are delivered exactly once.** In every reachable host
the delivered history is the committed history of the retained state, and the
world is the origin with that history interpreted once, in order. Stale or
copied tickets, refused requests and cancellations never repeat an effect. -/
theorem Reached.accounts {system : Retained State Op Effect} {act : Effect → World → World}
    {origin : World} {start : State} {host : Host State Effect World}
    (reached : Reached system act origin start host) : Accounts system act origin host := by
  induction reached with
  | begin => exact begin_accounts system act start origin
  | submit ticket op _ ih => exact submit_accounts system act ticket op ih
  | cancel ticket _ ih => exact cancel_accounts ticket ih

/-- States obtained from a start by finitely many operations. -/
abbrev Derived (system : Retained State Op Effect) (start : State) : State → Prop :=
  Relation.ReflTransGen (fun before after => ∃ op, after = system.apply op before) start

/-- The retained state of a reachable host was derived from the start by the
operations its accepted requests carried; nothing else changes it. -/
theorem Reached.retained {system : Retained State Op Effect} {act : Effect → World → World}
    {origin : World} {start : State} {host : Host State Effect World}
    (reached : Reached system act origin start host) :
    ∀ state, host.retained = some state → Derived system start state := by
  induction reached with
  | begin => intro state retained; cases retained; exact .refl
  | @submit host ticket op _ ih =>
      intro state retained
      by_cases current : ticket = host.epoch
      · cases previous : host.retained with
        | none => rw [submit_retired system act ticket op previous, previous] at retained; cases retained
        | some before =>
            subst current
            rw [submit_current system act op previous] at retained
            cases retained
            exact (ih before previous).tail ⟨op, rfl⟩
      · rw [submit_stale system act op current] at retained
        exact ih state retained
  | @cancel host ticket _ ih =>
      intro state retained
      by_cases current : ticket = host.epoch
      · cases previous : host.retained with
        | none => rw [cancel_retired ticket previous, previous] at retained; cases retained
        | some before =>
            subst current
            rw [cancel_current previous] at retained
            cases retained
      · rw [cancel_stale current] at retained
        exact ih state retained

/-- The epoch counts accepted requests; refused requests leave it unchanged. -/
theorem submit_epoch (system : Retained State Op Effect) (act : Effect → World → World)
    (ticket : Nat) (op : Op) (host : Host State Effect World) :
    (submit system act ticket op host).epoch = host.epoch ∨
      ((submit system act ticket op host).epoch = host.epoch + 1 ∧ ticket = host.epoch) := by
  by_cases current : ticket = host.epoch
  · cases retained : host.retained with
    | none => exact .inl (by rw [submit_retired system act ticket op retained])
    | some state =>
        subst current
        exact .inr ⟨by rw [submit_current system act op retained], rfl⟩
  · exact .inl (by rw [submit_stale system act op current])

/-- **One-shot authority.** After a ticket is accepted, the same ticket, held
by anyone, is refused: it changes nothing. -/
theorem used_ticket_refused (system : Retained State Op Effect) (act : Effect → World → World)
    {host : Host State Effect World} {state : State} (retained : host.retained = some state)
    (first second : Op) :
    let after := submit system act host.epoch first host
    submit system act host.epoch second after = after ∧ cancel host.epoch after = after := by
  intro after
  have moved : after.epoch = host.epoch + 1 := by
    simp only [after, submit_current system act first retained]
  have stale : host.epoch ≠ after.epoch := by omega
  exact ⟨submit_stale system act second stale, cancel_stale stale⟩

/-- Two holders of copies of one ticket: whichever request is served first is
the only one that acts. -/
theorem copies_act_once (system : Retained State Op Effect) (act : Effect → World → World)
    {host : Host State Effect World} {state : State} (retained : host.retained = some state)
    (first second : Op) :
    submit system act host.epoch second (submit system act host.epoch first host) =
      submit system act host.epoch first host :=
  (used_ticket_refused system act retained first second).1

/-- After cancellation every request is refused and the world and delivered
history stay as they were. -/
theorem cancelled_refuses (system : Retained State Op Effect) (act : Effect → World → World)
    {host : Host State Effect World} {state : State} (retained : host.retained = some state)
    (ticket : Nat) (op : Op) :
    let after := cancel host.epoch host
    submit system act ticket op after = after ∧ after.world = host.world ∧
      after.delivered = host.delivered ∧ after.retained = none := by
  intro after
  have retired : after.retained = none := by simp only [after, cancel_current retained]
  exact ⟨submit_retired system act ticket op retired,
    by simp only [after, cancel_current retained], by simp only [after, cancel_current retained], retired⟩

/-- Reading never changes the host, and a copied state can be advanced
privately without touching the world. -/
theorem private_fork (system : Retained State Op Effect) (host : Host State Effect World)
    {state : State} (retained : host.snapshot = some state) (op : Op) :
    host.retained = some state ∧
      (system.committed state).IsPrefix (system.committed (system.apply op state)) :=
  ⟨retained, system.grows op state⟩

/-- **Budget slicing for a retained runner.** When the operation is a budget
of a runner with exact resumption, two accepted requests with consecutive
tickets equal one request with the summed budget, in retained state, world and
delivered history. -/
theorem submit_add (system : Retained State Nat Effect) (act : Effect → World → World)
    (additive : ∀ first extra state, system.apply (first + extra) state =
      system.apply extra (system.apply first state))
    {host : Host State Effect World} {state : State} (retained : host.retained = some state)
    (first extra : Nat) :
    let sliced := submit system act (host.epoch + 1) extra (submit system act host.epoch first host)
    let whole := submit system act host.epoch (first + extra) host
    sliced.retained = whole.retained ∧ sliced.world = whole.world ∧
      sliced.delivered = whole.delivered ∧ sliced.epoch = whole.epoch + 1 := by
  intro sliced whole
  have middle := submit_current system act first retained
  have middleEpoch : (submit system act host.epoch first host).epoch = host.epoch + 1 := by
    rw [middle]
  have middleRetained : (submit system act host.epoch first host).retained =
      some (system.apply first state) := by
    rw [middle]
  have slicedEq : sliced = submit system act (submit system act host.epoch first host).epoch extra
      (submit system act host.epoch first host) := by
    simp only [sliced, middleEpoch]
  rw [slicedEq, submit_current system act extra middleRetained]
  simp only [whole, submit_current system act (first + extra) retained, middle, additive]
  have firstGrows := system.grows first state
  have extraGrows := system.grows extra (system.apply first state)
  obtain ⟨firstFresh, firstEq⟩ := firstGrows
  obtain ⟨extraFresh, extraEq⟩ := extraGrows
  have dropFirst : (system.committed (system.apply first state)).drop
      (system.committed state).length = firstFresh := by
    rw [← firstEq]
    simp
  have dropExtra : (system.committed (system.apply extra (system.apply first state))).drop
      (system.committed (system.apply first state)).length = extraFresh := by
    rw [← extraEq]
    simp
  have dropWhole : (system.committed (system.apply extra (system.apply first state))).drop
      (system.committed state).length = firstFresh ++ extraFresh := by
    rw [← extraEq, ← firstEq]
    simp
  simp only [dropFirst, dropExtra, dropWhole, interpret_append, List.append_assoc, and_self]


/-- **Two owners, one world.** Each host delivers its committed history once.
When every effect of one owner commutes with every effect of the other, a
shared world receiving any interleaving of the two delivered histories is the
first host's world followed by the second host's history. -/
theorem shared_world {StateL OpL EffL StateR OpR EffR : Type*}
    {systemL : Retained StateL OpL EffL} {systemR : Retained StateR OpR EffR}
    {actL : EffL → World → World} {actR : EffR → World → World} {origin : World}
    {startL : StateL} {startR : StateR}
    {hostL : Host StateL EffL World} {hostR : Host StateR EffR World}
    (reachedL : Reached systemL actL origin startL hostL)
    (_reachedR : Reached systemR actR origin startR hostR)
    (cross : ∀ left right world, actL left (actR right world) = actR right (actL left world))
    (log : List (EffL ⊕ EffR)) (left : log.filterMap Sum.getLeft? = hostL.delivered)
    (right : log.filterMap Sum.getRight? = hostR.delivered) :
    interpret (Sum.elim actL actR) log origin = interpret actR hostR.delivered hostL.world := by
  rw [interpret_interleaving actL actR cross, left, right, reachedL.accounts.world]

end Host

end Owned

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

namespace SessionControls

def addEvent (event world : Nat) : Nat := world + event

def childSession : Session Nat Nat Nat := Session.begin exampleProgram 0

example : (Session.resume addEvent 1 childSession).world = 0 := rfl
example : (Session.resume addEvent 2 childSession).committed = [1] := rfl
example : (Session.resume addEvent 2 childSession).world = 1 := rfl

example : Session.resume addEvent 8 (Session.resume addEvent 2 childSession) =
    Session.resume addEvent 10 childSession :=
  (Session.resume_add addEvent 2 8 childSession).symm

example : (Session.resume addEvent 10 childSession).world = 5 := rfl
example : (Session.resume addEvent 10 childSession).committed = [1, 1, 3] := rfl

example : (Session.resume addEvent 10 (Session.resume addEvent 2 childSession).cancel).world =
    1 := rfl
example :
    (Session.resume addEvent 10 (Session.resume addEvent 2 childSession).cancel).committed =
      [1] := rfl
example :
    (Session.resume addEvent 10 (Session.resume addEvent 2 childSession).cancel).residual =
      none := rfl

def increment (_event : Unit) (world : Nat) : Nat := world + 1

def onceProgram : Program Unit Unit := .emit () (.done ())
def onceSession : Session Unit Unit Nat := Session.begin onceProgram 0

example : (Session.resume increment 1 onceSession).world = 1 := rfl
theorem continuation_does_not_repeat :
    (Session.resume increment 1 (Session.resume increment 1 onceSession)).world =
    1 := rfl

/-- Reinstalling the original work repeats its non-idempotent effect. Pure
session data does not itself prevent that deliberate restart. -/
def restarted : Session Unit Unit Nat :=
  { Session.resume increment 1 onceSession with residual := onceSession.residual }

theorem restart_repeats : (Session.resume increment 1 restarted).world = 2 := rfl
theorem restart_retains_both_occurrences :
    (Session.resume increment 1 restarted).committed = [(), ()] := rfl
theorem restart_differs_from_continuation : (Session.resume increment 1 restarted).world ≠
    (Session.resume increment 1 (Session.resume increment 1 onceSession)).world := by decide

def noncommuting (event : Bool) (world : Nat) : Nat :=
  if event then world + 1 else world * 2

example : interpret noncommuting [true, false] 2 = 6 := rfl
example : interpret noncommuting [false, true] 2 = 5 := rfl
theorem noncommuting_swap_changes_world : interpret noncommuting [true, false] 2 ≠
    interpret noncommuting [false, true] 2 := by decide

example : interpret addEvent [1, 2] 7 = interpret addEvent [2, 1] 7 := rfl
example : ([1, 2] : List Nat) ≠ [2, 1] := by decide

end SessionControls

namespace OwnedControls

open SessionControls Owned

/-- The pull driver with its emitted event log: the operation is a budget. -/
def driver (Value Event : Type) : Owned.Retained (State Value Event × List Event) Nat Event where
  apply fuel retained := ((advance fuel retained.1).2, retained.2 ++ (advance fuel retained.1).1)
  committed retained := retained.2
  grows _ _ := List.prefix_append _ _

theorem driver_additive (Value Event : Type) (first extra : Nat)
    (retained : State Value Event × List Event) :
    (driver Value Event).apply (first + extra) retained =
      (driver Value Event).apply extra ((driver Value Event).apply first retained) := by
  simp [driver, advance_add, List.append_assoc]

def onceHost : Host (State Unit Unit × List Unit) Unit Nat :=
  Host.begin (driver Unit Unit) increment (⟨onceProgram, []⟩, []) 0

def served : Host (State Unit Unit × List Unit) Unit Nat :=
  Host.submit (driver Unit Unit) increment 0 1 onceHost

example : served.world = 1 := rfl
example : served.delivered = [()] := rfl

/-- A copy of the used ticket is refused: the effect is not repeated. -/
theorem copied_ticket_does_not_repeat :
    (Host.submit (driver Unit Unit) increment 0 1 served).world = 1 ∧
      Host.submit (driver Unit Unit) increment 0 1 served = served := ⟨rfl, rfl⟩

/-- The current ticket continues the retained state without repeating. -/
theorem current_ticket_continues :
    (Host.submit (driver Unit Unit) increment 1 1 served).world = 1 ∧
      (Host.submit (driver Unit Unit) increment 1 1 served).delivered = [()] := ⟨rfl, rfl⟩

/-- New authority over the original state is a deliberate restart: it repeats
the effect. Exactly-once delivery is a law of one host, not of copied data. -/
theorem fresh_authority_repeats :
    (Host.submit (driver Unit Unit) increment 0 1
      (Host.begin (driver Unit Unit) increment (⟨onceProgram, []⟩, []) served.world)).world = 2 :=
  rfl

/-- A stale cancellation is refused; the holder's cancellation retires the
continuation and keeps the world. -/
theorem stale_cancel_refused_current_cancel_retires :
    (Host.cancel 0 served).retained.isSome = true ∧
      (Host.cancel 1 served).retained = none ∧ (Host.cancel 1 served).world = 1 ∧
      (Host.submit (driver Unit Unit) increment 2 1 (Host.cancel 1 served)).world = 1 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Sliced budgets under consecutive tickets equal the whole budget. -/
theorem sliced_tickets_equal_whole_budget :
    let host := Host.begin (driver Nat Nat) addEvent (⟨exampleProgram, []⟩, []) 0
    (Host.submit (driver Nat Nat) addEvent 1 8 (Host.submit (driver Nat Nat) addEvent 0 2 host)).world =
        (Host.submit (driver Nat Nat) addEvent 0 10 host).world ∧
      (Host.submit (driver Nat Nat) addEvent 1 8 (Host.submit (driver Nat Nat) addEvent 0 2 host)).delivered =
        [1, 1, 3] := ⟨rfl, rfl⟩

example : (Host.submit (driver Nat Nat) addEvent 0 10
    (Host.begin (driver Nat Nat) addEvent (⟨exampleProgram, []⟩, []) 0)).world = 5 := rfl

/-- Every reachable host accounts for its world exactly once. -/
theorem driver_hosts_account (act : Nat → Nat → Nat) (origin : Nat)
    (start : State Nat Nat × List Nat) {host : Host (State Nat Nat × List Nat) Nat Nat}
    (reached : Host.Reached (driver Nat Nat) act origin start host) :
    host.world = interpret act host.delivered origin :=
  reached.accounts.world


/-- Commuting owners: two interleavings of the same delivered histories agree. -/
theorem commuting_owners_interleave :
    interpret (Sum.elim addEvent addEvent) [.inl 1, .inr 2, .inl 3] 0 =
      interpret (Sum.elim addEvent addEvent) [.inr 2, .inl 1, .inl 3] 0 := rfl

/-- Without the cross-owner condition the interleaving is observable: one owner
increments, the other doubles. -/
theorem noncommuting_owners_observe_interleaving :
    interpret (Sum.elim noncommuting noncommuting) [.inl true, .inr false] 2 ≠
      interpret (Sum.elim noncommuting noncommuting) [.inr false, .inl true] 2 := by decide

/-- Within one owner order is kept even when the owners commute with each other. -/
theorem owner_order_is_kept :
    interpret (Sum.elim noncommuting (fun (_ : Unit) (world : Nat) => world))
        [.inl true, .inr (), .inl false] 2 = 6 ∧
      interpret (Sum.elim noncommuting (fun (_ : Unit) (world : Nat) => world))
        [.inl false, .inr (), .inl true] 2 = 5 := ⟨rfl, rfl⟩

end OwnedControls

end Mettapedia.Machines.OwnedPullDriver
