import Mettapedia.Machines.Cursor.Scheduling
import Mettapedia.Machines.Cursor.Fold
import Mettapedia.Machines.CooperativeQueue
import Mettapedia.Machines.ReadyQueue
import Mettapedia.Machines.ResumableRegion
import Mettapedia.Machines.BindingPublication
import Mettapedia.Machines.EventPump
import Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor
import Mettapedia.GSLT.Core.SearchStreamProductivity
import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis

/-!
# Fair scheduling of finite observations of ongoing cursors

The provider and client are the existing indexed cursor protocol. A fair
schedule gives each retained work item unbounded inspection allocation. If
one observation can finish after finitely many inspections, that observation
eventually finishes under the fair schedule, with exactly the same receipt,
result, and provider residual. The provider itself need not terminate.

This is allocation fairness for independent retained packets. Each provider
transition must itself return; a blocking native call cannot acquire a wall
clock fairness guarantee from these laws. Reordering shared effects requires
a separate commuting-effects argument.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.FairObservation

open Mettapedia.TypeTheory
open Scheduling

universe u v
variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable (M : Provider P) (C : Client (P := P) (Return := Return))
variable (charge : Charge M)
variable {Id : Type v} [DecidableEq Id] {base : Base}

/-- The chronological finite prefix of an indefinitely authored schedule. -/
def schedulePrefix (schedule : Nat → Command Id) : Nat → List (Command Id)
  | 0 => []
  | length + 1 => schedulePrefix schedule length ++ [schedule length]

theorem allocation_append (id : Id) (first second : List (Command Id)) :
    allocation id (first ++ second) = allocation id first + allocation id second := by
  induction first with
  | nil => simp [allocation]
  | cons command rest ih => simp only [List.cons_append, allocation, ih, Nat.add_assoc]

theorem allocation_prefix_mono (schedule : Nat → Command Id) (id : Id)
    {earlier later : Nat} (ordered : earlier ≤ later) :
    allocation id (schedulePrefix schedule earlier) ≤
      allocation id (schedulePrefix schedule later) := by
  induction later, ordered using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ later _ ih =>
      rw [schedulePrefix, allocation_append]
      exact ih.trans (Nat.le_add_right _ _)

/-- Every retained identity receives any requested finite inspection budget.
No queue representation, answer order, or finite global work set is assumed. -/
def FairAllocation (schedule : Nat → Command Id) : Prop :=
  ∀ id demand, ∃ horizon,
    demand ≤ allocation id (schedulePrefix schedule horizon)

/-- Once a client finishes, a larger allocation neither polls its provider
again nor changes its receipt or terminal residual. -/
theorem resume_done_of_le (cell : Cell M C base) (needed available spent : Nat)
    (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed cell = (spent, .done result))
    (enough : needed ≤ available) :
    resume M C charge available cell = (spent, .done result) := by
  have decomposition : available = needed + (available - needed) := by omega
  rw [decomposition, resume_add, finished, resume_done]

/-- Local progress plus allocation fairness gives eventual, permanent
completion of this observation. An infinite producer may satisfy the local
progress premise for each bounded demand separately. -/
theorem fair_eventually_done (schedule : Nat → Command Id)
    (fair : FairAllocation schedule) (pool : Pool M C Id base) (id : Id)
    (needed spent : Nat) (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed (pool id) = (spent, .done result)) :
    ∃ horizon, ∀ extra,
      execute M C charge (schedulePrefix schedule (horizon + extra)) pool id =
        (spent, .done result) := by
  obtain ⟨horizon, enough⟩ := fair id needed
  refine ⟨horizon, fun extra => ?_⟩
  rw [execute_at]
  exact resume_done_of_le M C charge (pool id) needed _ spent result finished
    (enough.trans (allocation_prefix_mono schedule id (Nat.le_add_right _ _)))

/-- Fair scheduling is exact about what it can accomplish: completion is
equivalent to some finite local allocation, not to fairness alone. -/
theorem eventually_done_iff (schedule : Nat → Command Id)
    (fair : FairAllocation schedule) (pool : Pool M C Id base) (id : Id)
    (spent : Nat) (result : Finished M (Return := Return) base) :
    (∃ horizon,
      execute M C charge (schedulePrefix schedule horizon) pool id =
        (spent, .done result)) ↔
    (∃ needed, resume M C charge needed (pool id) = (spent, .done result)) := by
  constructor
  · rintro ⟨horizon, completed⟩
    exact ⟨allocation id (schedulePrefix schedule horizon),
      (execute_at M C charge _ pool id).symm.trans completed⟩
  · rintro ⟨needed, completed⟩
    obtain ⟨horizon, stable⟩ :=
      fair_eventually_done M C charge schedule fair pool id needed spent result completed
    exact ⟨horizon, by simpa using stable 0⟩

/-! ## Concrete queue service, including continuing arrivals -/

/-- The same queue used by the event pump schedules actual retained packets.
An empty scheduling slot performs no cursor inspection. -/
def cooperativeSchedule (quantum slots : Nat) (arrivals : Nat → List Id)
    (queue : List Id) : List (Command Id) :=
  (CooperativeQueue.services slots arrivals queue).map (fun id => (id, quantum))

theorem cooperative_allocation (quantum slots : Nat) (arrivals : Nat → List Id)
    (queue : List Id) (id : Id) :
    allocation id (cooperativeSchedule quantum slots arrivals queue) =
      (CooperativeQueue.services slots arrivals queue).count id * quantum :=
  allocation_uniform id quantum _

/-- Arbitrary continuing finite arrivals cannot prevent any finite inspection
demand of a continuously queued owner, provided each service grants work. -/
theorem cooperative_allocation_unbounded (quantum : Nat) (positive : 0 < quantum)
    (arrivals : Nat → List Id) (queue : List Id) (id : Id) (member : id ∈ queue)
    (demand : Nat) :
    ∃ slots, demand ≤ allocation id (cooperativeSchedule quantum slots arrivals queue) := by
  obtain ⟨slots, enough⟩ := CooperativeQueue.unbounded_service demand arrivals queue id member
  refine ⟨slots, ?_⟩
  rw [cooperative_allocation]
  have one : 1 ≤ quantum := positive
  have scaling := Nat.mul_le_mul_left
    ((CooperativeQueue.services slots arrivals queue).count id) one
  exact enough.trans (by simpa using scaling)

/-- Once sufficient service has occurred, the completed observation remains
exact under every longer queue run: answer, charge and full residual agree.
This requires local finite completion, not termination of the whole producer. -/
theorem cooperative_eventually_done (quantum : Nat) (positive : 0 < quantum)
    (arrivals : Nat → List Id) (queue : List Id) (id : Id) (member : id ∈ queue)
    (pool : Pool M C Id base) (needed spent : Nat)
    (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed (pool id) = (spent, .done result)) :
    ∃ slots, ∀ extra,
      execute M C charge (cooperativeSchedule quantum (slots + extra) arrivals queue) pool id =
        (spent, .done result) := by
  obtain ⟨slots, enough⟩ :=
    cooperative_allocation_unbounded quantum positive arrivals queue id member needed
  refine ⟨slots, fun extra => ?_⟩
  rw [execute_at]
  apply resume_done_of_le M C charge (pool id) needed _ spent result finished
  apply enough.trans
  simp only [cooperativeSchedule, CooperativeQueue.services_add, List.map_append,
    allocation_append]
  exact Nat.le_add_right _ _

/-- Recording infinitely many scheduling turns would still do no computation
if their inspection quantum were zero. Service and progress are separate. -/
theorem zero_quantum_preserves_pool (slots : Nat) (arrivals : Nat → List Id)
    (queue : List Id) (pool : Pool M C Id base) :
    execute M C charge (cooperativeSchedule 0 slots arrivals queue) pool = pool := by
  funext id
  rw [execute_at, cooperative_allocation]
  simp only [Nat.mul_zero, resume_zero]

/-- An accepted event supplies queue membership; the existing cursor protocol
then supplies exact resumable work. The driver must actually perform both the
durable admission and this queue policy. A transient wake alone is insufficient. -/
theorem accepted_eventually_done (inbox : EventPump.Inbox) (event : EventPump.Event)
    (accepted : event.owner = inbox.owner ∧ inbox.phase event.serial = none)
    (quantum : Nat) (positive : 0 < quantum)
    (arrivals : Nat → List EventPump.Key) (queue : List EventPump.Key)
    (pool : Pool M C EventPump.Key base) (needed spent : Nat)
    (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed (pool inbox.owner) = (spent, .done result)) :
    ∃ slots, ∀ extra,
      execute M C charge
        (cooperativeSchedule quantum (slots + extra) arrivals
          (EventPump.wakeReady queue (EventPump.record inbox event))) pool inbox.owner =
        (spent, .done result) := by
  have queued := EventPump.accepted_event_is_queued inbox event accepted
  have pending : event ∈ EventPump.pending (EventPump.record inbox event) :=
    List.mem_filter.mpr ⟨queued.1, by simp [queued.2]⟩
  have nonempty : EventPump.pending (EventPump.record inbox event) ≠ [] := by
    intro empty
    simp [empty] at pending
  have member := EventPump.ready_owner_is_queued queue (EventPump.record inbox event) nonempty
  have owner : (EventPump.record inbox event).owner = inbox.owner :=
    EventPump.step_preserves_owner inbox (.arrival event)
  rw [owner] at member
  exact cooperative_eventually_done M C charge quantum positive arrivals _ inbox.owner
    member pool needed spent result finished

/-- The capacity-bounded ready queue gives a retained packet enough inspection
allocation after the stated number of completed service slots. -/
theorem ready_allocation_lower_bound (visits quantum : Nat)
    (state : ReadyQueue.State) (target : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (valid : ReadyQueue.invariant state)
    (member : target ∈ state.tasks)
    (retained : ∀ n,
      (ReadyQueue.serviceRun n keep offered state).2.tasks.head? = some target →
      keep n = true) :
    visits * quantum ≤ allocation target
      ((ReadyQueue.serviceRun (visits * state.capacity) keep offered state).1.map
        (fun task => (task, quantum))) := by
  rw [allocation_uniform]
  exact Nat.mul_le_mul_right quantum
    (ReadyQueue.retained_task_gets_repeated_service visits state target keep offered
      valid member retained)

/-- State-dependent budgets preserve the capacity bound when each target
visit grants at least the stated number of inspections. The task may retire
on its final required visit; other owners need no positive budget. This bounds
completed service slots, not elapsed time or opaque provider-call duration. -/
theorem ready_variable_observation_before_retirement (visits minimum extra : Nat)
    (state : ReadyQueue.State) (target : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (valid : ReadyQueue.invariant state)
    (member : target ∈ state.tasks)
    (retained : ∀ n,
      (ReadyQueue.serviceRun (n + 1) keep offered state).1.count target < visits →
      (ReadyQueue.serviceRun n keep offered state).2.tasks.head? = some target →
      keep n = true)
    (commands : List (Command Nat))
    (aligned : List.Forall₂ (fun task command =>
      command.1 = task ∧ (task = target → minimum ≤ command.2))
      (ReadyQueue.serviceRun (visits * state.capacity + extra) keep offered state).1
      commands)
    (pool : Pool M C Nat base) (needed spent : Nat)
    (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed (pool target) = (spent, .done result))
    (enough : needed ≤ visits * minimum) :
    execute M C charge commands pool target = (spent, .done result) := by
  rw [execute_at]
  apply resume_done_of_le M C charge (pool target) needed _ spent result finished
  apply enough.trans
  apply (Nat.mul_le_mul_right minimum
    ((ReadyQueue.requested_task_gets_bounded_service visits state target keep offered
      valid member retained).trans
      (ReadyQueue.serviceRun_count_mono (Nat.le_add_right _ _) state target keep offered))).trans
  exact allocation_lower_bound target minimum aligned

/-- A finite observation survives retirement after its requested service.
No retention is required after the final requested visit. Longer executions
preserve its exact answer, paid charge and complete provider residual. -/
theorem ready_observation_before_retirement (visits quantum extra : Nat)
    (state : ReadyQueue.State) (target : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (valid : ReadyQueue.invariant state)
    (member : target ∈ state.tasks)
    (retained : ∀ n,
      (ReadyQueue.serviceRun (n + 1) keep offered state).1.count target < visits →
      (ReadyQueue.serviceRun n keep offered state).2.tasks.head? = some target →
      keep n = true)
    (pool : Pool M C Nat base) (needed spent : Nat)
    (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed (pool target) = (spent, .done result))
    (enough : needed ≤ visits * quantum) :
    execute M C charge
      ((ReadyQueue.serviceRun (visits * state.capacity + extra) keep offered state).1.map
        (fun task => (task, quantum))) pool target = (spent, .done result) := by
  apply ready_variable_observation_before_retirement M C charge visits quantum extra
    state target keep offered valid member retained _ _ pool needed spent result finished enough
  generalize (ReadyQueue.serviceRun (visits * state.capacity + extra) keep offered state).1 = trace
  induction trace with
  | nil => exact .nil
  | cons task rest ih => exact .cons ⟨rfl, fun _ => Nat.le_refl _⟩ ih

/-- Local finite completion transfers to the actual bounded ready queue.
Every longer execution preserves the exact answer, paid charge and provider
residual. The host must execute each slot and its provider calls must return. -/
theorem ready_observation_within_capacity_bound (visits quantum extra : Nat)
    (state : ReadyQueue.State) (target : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (valid : ReadyQueue.invariant state)
    (member : target ∈ state.tasks)
    (retained : ∀ n,
      (ReadyQueue.serviceRun n keep offered state).2.tasks.head? = some target →
      keep n = true)
    (pool : Pool M C Nat base) (needed spent : Nat)
    (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed (pool target) = (spent, .done result))
    (enough : needed ≤ visits * quantum) :
    execute M C charge
      ((ReadyQueue.serviceRun (visits * state.capacity + extra) keep offered state).1.map
        (fun task => (task, quantum))) pool target = (spent, .done result) := by
  exact ready_observation_before_retirement M C charge visits quantum extra state target
    keep offered valid member (fun n _ atHead => retained n atHead)
    pool needed spent result finished enough

/-! ## A fair policy and an unfair policy -/

def roundRobin (step : Nat) : Command Bool := (decide (step % 2 = 1), 1)

theorem roundRobin_allocation (id : Bool) (rounds : Nat) :
    allocation id (schedulePrefix roundRobin (2 * rounds)) = rounds := by
  induction rounds with
  | zero => simp [schedulePrefix, allocation]
  | succ rounds ih =>
      have twice : 2 * (rounds + 1) = (2 * rounds + 1) + 1 := by omega
      rw [twice, schedulePrefix, allocation_append, schedulePrefix, allocation_append, ih]
      cases id <;> simp [allocation, roundRobin, Nat.add_mod]

theorem roundRobin_fair : FairAllocation roundRobin := by
  intro id demand
  exact ⟨2 * demand, by rw [roundRobin_allocation]⟩

/-- A depth-first policy that never switches away from the first ongoing
item is not allocation-fair to the other item. -/
def neverSwitch (_ : Nat) : Command Bool := (false, 1)

theorem neverSwitch_starves (horizon : Nat) :
    allocation true (schedulePrefix neverSwitch horizon) = 0 := by
  induction horizon with
  | zero => rfl
  | succ horizon ih => simp [schedulePrefix, allocation_append, ih, allocation, neverSwitch]

theorem neverSwitch_not_fair : ¬ FairAllocation neverSwitch := by
  intro fair
  obtain ⟨horizon, enough⟩ := fair true 1
  rw [neverSwitch_starves] at enough
  omega

section OngoingProducer

open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull)
open NativeControlEffectCursor (provider)
open NativeControlBoundedCursor (client packet collectBounded)
open Mettapedia.GSLT.Core.SearchStreamProductivity (streamPrefix)

variable {Answer World : Type}

/-- A genuine ongoing producer: every poll emits another authored occurrence.
The answer type may contain closures, witnesses, or repeated values. -/
def streamPull (expected : Nat → Answer) (index : Nat) (world : World) :
    World × Pull Nat Answer := (world, .yield (expected index) (index + 1))

theorem streamPrefix_succ (expected : Nat → Answer) (demand : Nat) :
    streamPrefix expected (demand + 1) =
      expected 0 :: streamPrefix (fun index => expected (index + 1)) demand := by
  simp only [streamPrefix, List.ofFn_succ]
  rfl

/-- Every requested finite prefix is obtained after exactly that many polls,
without inspecting the next occurrence or asserting global exhaustion. -/
theorem stream_collect_exact (expected : Nat → Answer) (demand index : Nat)
    (world : World) :
    collectBounded (streamPull expected) demand demand index world =
      (demand, ⟨index + demand, world,
        streamPrefix (fun offset => expected (index + offset)) demand, 0, .limit⟩) := by
  induction demand generalizing index with
  | zero => simp [collectBounded, streamPrefix]
  | succ demand ih =>
      simp only [collectBounded, streamPull, ih,
        NativeControlBoundedCursor.Snapshot.prefix, List.singleton_append]
      rw [streamPrefix_succ]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- The independent collector's finite-prefix law transfers to the actual
protocol client. The extra inspection publishes, without another pull. -/
theorem stream_client_exact (expected : Nat → Answer) (demand index : Nat)
    (world : World) :
    advance (provider (streamPull expected)) (client Answer) (fun _ _ => 1)
      (demand + 1) (packet (streamPull expected) demand index world []) =
      (demand, .done ⟨(), ⟨0, .limit,
        streamPrefix (fun offset => expected (index + offset)) demand⟩,
        (index + demand, world)⟩) := by
  simpa using NativeControlBoundedCursor.completed_exact (streamPull expected)
    demand demand index world [] demand 0 (index + demand) world
    (streamPrefix (fun offset => expected (index + offset)) demand) .limit
    (stream_collect_exact expected demand index world)

/-- `once` observes one occurrence of an ongoing producer and leaves its
second occurrence unpolled. This does not require producer termination. -/
theorem stream_once (expected : Nat → Answer) (index : Nat) (world : World) :
    collectBounded (streamPull expected) 1 1 index world =
      (1, ⟨index + 1, world, [expected index], 0, .limit⟩) := rfl

/-- A whole pool may contain ongoing sources. Every requested finite prefix
is nevertheless delivered under fair scheduling of the retained clients. -/
theorem fair_stream_observation (expected : Nat → Answer)
    (demands starts : Id → Nat) (worlds : Id → World)
    (schedule : Nat → Command Id) (fair : FairAllocation schedule) (id : Id) :
    let pool : Pool (provider (streamPull expected)) (client Answer) Id () :=
      fun item => (0, .paused (packet (streamPull expected)
        (demands item) (starts item) (worlds item) []))
    ∃ horizon, ∀ extra,
      execute (provider (streamPull expected)) (client Answer) (fun _ _ => 1)
        (schedulePrefix schedule (horizon + extra)) pool id =
      (demands id, .done ⟨(), ⟨0, .limit,
        streamPrefix (fun offset => expected (starts id + offset)) (demands id)⟩,
        (starts id + demands id, worlds id)⟩) := by
  dsimp only
  apply fair_eventually_done _ _ _ schedule fair _ id (demands id + 1)
  simpa only [resume, Nat.zero_add] using
    stream_client_exact expected (demands id) (starts id) (worlds id)

end OngoingProducer

/-! ## Ready service of actual owned callback calls

The ready cache contains stable task identities; the pool retains each complete
owned call even after its ready membership retires. A visit performs one existing
callback call. Its actual terminal record determines retirement. In particular,
finishing a bounded callback invocation is not producer exhaustion.
-/

namespace OwnedService

open Fold.OwnedSequence.CallbackBoundary

variable {Item Terminal : Type}
variable (M : Provider (protocol Item Terminal)) (charge : Charge M)

abbrev Call := Nat × (Result Item Terminal × M.State () ())

structure State where
  ready : ReadyQueue.State
  pool : Nat → Call M

variable (terminalAfter : Item → Option Terminal := fun _ => none)

/-- The complete post-call record, not a prediction of future source answers. -/
def selected (allowance : Nat) (state : State M) : Option (Nat × Call M) :=
  state.ready.tasks.head?.map fun owner =>
    (owner, resumeCall M charge allowance (state.pool owner) terminalAfter)

def keep (allowance : Nat) (state : State M) : Bool :=
  match selected M charge terminalAfter allowance state with
  | none => true
  | some (_, later) => later.2.1.terminal.isNone

/-- One ready visit uses the existing owned boundary. A refused acceptance may
change callback context; its returned state and held loan are installed whole.
The allowance counts accepted returns, not scheduler ticks or source firings. -/
def service (allowance : Nat) (offered : List Nat) (state : State M) : State M :=
  let chosen := selected M charge terminalAfter allowance state
  ⟨ReadyQueue.service state.ready (match chosen with
      | none => true
      | some (_, later) => later.2.1.terminal.isNone) offered,
    match chosen with
    | none => state.pool
    | some (owner, later) => Function.update state.pool owner later⟩

def run : Nat → (Nat → Nat) → (Nat → List Nat) → State M → State M
  | 0, _, _, state => state
  | slots + 1, grants, offered, state =>
      run slots (fun i => grants (i + 1)) (fun i => offered (i + 1))
        (service M charge terminalAfter (grants 0) (offered 0) state)

/-- Proof observation of actual dispatches. This is not stored by `service`
or `run` and is not a required runtime journal. Idle visits add no command. -/
def commands : Nat → (Nat → Nat) → (Nat → List Nat) → State M → List (Nat × Nat)
  | 0, _, _, _ => []
  | slots + 1, grants, offered, state =>
      state.ready.tasks.head?.toList.map (fun owner => (owner, grants 0)) ++
        commands slots (fun i => grants (i + 1)) (fun i => offered (i + 1))
          (service M charge terminalAfter (grants 0) (offered 0) state)

/-- Actual terminal decisions supplied to the existing queue theorem. -/
def keeps (grants : Nat → Nat) (offered : Nat → List Nat) (state : State M) : Nat → Bool
  | 0 => keep M charge terminalAfter (grants 0) state
  | slot + 1 => keeps (fun i => grants (i + 1)) (fun i => offered (i + 1))
      (service M charge terminalAfter (grants 0) (offered 0) state) slot

theorem service_selected (allowance : Nat) (offered : List Nat) (state : State M)
    (owner : Nat) (head : state.ready.tasks.head? = some owner) :
    (service M charge terminalAfter allowance offered state).pool owner =
      resumeCall M charge allowance (state.pool owner) terminalAfter := by
  simp [service, selected, head]

theorem service_other (allowance : Nat) (offered : List Nat) (state : State M)
    (owner other : Nat) (head : state.ready.tasks.head? = some owner) (different : other ≠ owner) :
    (service M charge terminalAfter allowance offered state).pool other = state.pool other := by
  simp [service, selected, head, different]

/-- Zero acceptance allowance retains every paid account, provider state and
pending loan. The independent ready policy still visits and admits arrivals. -/
theorem zero_preserves_pool (offered : List Nat) (state : State M) :
    (service M charge terminalAfter 0 offered state).pool = state.pool := by
  funext owner
  cases head : state.ready.tasks.head? with
  | none => simp [service, selected, head]
  | some selectedOwner =>
      simp [service, selected, head, resumeCall_zero]

/-- Terminal membership retirement does not dispose the retained owner. -/
theorem terminal_keeps_call (allowance : Nat) (offered : List Nat) (state : State M)
    (owner : Nat) (head : state.ready.tasks.head? = some owner)
    (reason : Terminal) (finished : (state.pool owner).2.1.terminal = some reason) :
    keep M charge terminalAfter allowance state = false ∧
      (service M charge terminalAfter allowance offered state).pool owner = state.pool owner := by
  simp [keep, selected, head, resumeCall, finished, service_selected M charge terminalAfter _ _ _ _ head]

/-- A refused held loan causes no producer request. The entire callback
post-state is retained, even when refusal changes private context. -/
theorem pending_refusal (allowance paid accepted : Nat) (offered : List Nat) (state : State M)
    (owner : Nat) (item : Item) (before after : M.State () ())
    (head : state.ready.tasks.head? = some owner)
    (held : state.pool owner = (paid, ⟨none, some item, accepted⟩, before))
    (refused : M.step before (.accept item) = ⟨false, after⟩) :
    (service M charge terminalAfter (allowance + 1) offered state).pool owner =
      (paid + charge before (.accept item), ⟨none, some item, accepted⟩, after) := by
  rw [service_selected M charge terminalAfter _ _ _ _ head, held]
  simp only [resumeCall, fromCallbacks, refused]

/-- One accepted-return grant retries a held item without pulling the next
item. The producer-certified terminal marker is preserved exactly. -/
theorem pending_acceptance (paid accepted : Nat) (offered : List Nat) (state : State M)
    (owner : Nat) (item : Item) (before after : M.State () ())
    (head : state.ready.tasks.head? = some owner)
    (held : state.pool owner = (paid, ⟨none, some item, accepted⟩, before))
    (acknowledged : M.step before (.accept item) = ⟨true, after⟩) :
    (service M charge terminalAfter 1 offered state).pool owner =
      (paid + charge before (.accept item), ⟨terminalAfter item, none, accepted + 1⟩, after) := by
  rw [service_selected M charge terminalAfter _ _ _ _ head, held]
  cases marker : terminalAfter item <;> simp [resumeCall, fromCallbacks, acknowledged, marker]

/-- Cancelling membership neither runs a provider nor releases another owner. -/
def cancel (owner : Nat) (state : State M) : State M :=
  ⟨(ReadyQueue.step state.ready (.remove owner)).2, state.pool⟩

theorem cancel_preserves_pool (owner : Nat) (state : State M) :
    (cancel M owner state).pool = state.pool := rfl

/-- Full-pool comparison with the pre-existing independently defined owned
callback kernel. The derived word preserves each stateful refusal/retry; it
is not replaced by the sum of its acceptance allowances. -/
theorem run_is_kernel (slots : Nat) (grants : Nat → Nat) (offered : Nat → List Nat)
    (state : State M) :
    (run M charge terminalAfter slots grants offered state).pool =
      (kernel M charge Nat terminalAfter).run () (fun _ => ()) state.pool
        (commands M charge terminalAfter slots grants offered state) := by
  induction slots generalizing grants offered state with
  | zero => rfl
  | succ slots ih =>
      simp only [run, commands, ih]
      cases head : state.ready.tasks.head? with
      | none =>
          simp only [Option.toList_none, List.map_nil, List.nil_append]
          simp only [service, selected, head, Option.map_none]
      | some owner =>
          simp only [Option.toList_some, List.map_cons, List.map_nil,
            List.singleton_append, SnapshotBatch.Kernel.run_cons]
          simp only [service, selected, head, Option.map_some]
          rfl

/-- Exact residual queue and actual visited identities agree with the old
ready service. Retirement decisions are now obtained from real task results. -/
theorem run_ready (slots : Nat) (grants : Nat → Nat) (offered : Nat → List Nat)
    (state : State M) :
    ((commands M charge terminalAfter slots grants offered state).map Prod.fst,
      (run M charge terminalAfter slots grants offered state).ready) =
      ReadyQueue.serviceRun slots (keeps M charge terminalAfter grants offered state)
        offered state.ready := by
  induction slots generalizing grants offered state with
  | zero => rfl
  | succ slots ih =>
      simp only [commands, run, List.map_append, List.map_map,
        ReadyQueue.serviceRun]
      have rest := ih (fun i => grants (i + 1)) (fun i => offered (i + 1))
        (service M charge terminalAfter (grants 0) (offered 0) state)
      change (_, _) = _ at rest
      change (_, _) =
        (state.ready.tasks.head?.toList ++ _, _)
      have lifted := congrArg (fun result : List Nat × ReadyQueue.State =>
        (state.ready.tasks.head?.toList ++ result.1, result.2)) rest
      simpa [keeps, service, keep, Function.comp_def] using lifted

theorem run_preserves_ready (slots : Nat) (grants : Nat → Nat) (offered : Nat → List Nat)
    (state : State M) (valid : ReadyQueue.invariant state.ready) :
    ReadyQueue.invariant (run M charge terminalAfter slots grants offered state).ready := by
  have same := congrArg Prod.snd (run_ready M charge terminalAfter slots grants offered state)
  change (run M charge terminalAfter slots grants offered state).ready = _ at same
  rw [same]
  exact ReadyQueue.serviceRun_preserves_invariant _ _ _ _ valid

/-- Continuing arrivals and completed predecessors cannot overtake an already
queued task. This bounds visits, not successful acceptance or CPU latency. -/
theorem queued_task_gets_visit (grants : Nat → Nat) (offered : Nat → List Nat)
    (state : State M) (owner : Nat) (valid : ReadyQueue.invariant state.ready)
    (member : owner ∈ state.ready.tasks) :
    ∃ slots ≤ state.ready.tasks.length,
      owner ∈ (commands M charge terminalAfter slots grants offered state).map Prod.fst := by
  obtain ⟨slots, bound, served⟩ := ReadyQueue.queued_task_gets_bounded_service state.ready owner
    (keeps M charge terminalAfter grants offered state) offered valid member
  exact ⟨slots, bound, by
    simpa only [← run_ready M charge terminalAfter slots grants offered state] using served⟩

/-- Splitting physical service slots shifts both grants and later offers and
retains the complete pool and ready order. It does not fuse callback grants. -/
theorem run_add (first second : Nat) (grants : Nat → Nat) (offered : Nat → List Nat)
    (state : State M) :
    run M charge terminalAfter (first + second) grants offered state =
      run M charge terminalAfter second (fun i => grants (i + first))
        (fun i => offered (i + first)) (run M charge terminalAfter first grants offered state) := by
  induction first generalizing grants offered state with
  | zero => simp [run]
  | succ first ih =>
      simp only [Nat.succ_add, run, ih]
      simp only [Nat.add_assoc, Nat.add_comm first 1]

theorem commands_add (first second : Nat) (grants : Nat → Nat) (offered : Nat → List Nat)
    (state : State M) :
    commands M charge terminalAfter (first + second) grants offered state =
      commands M charge terminalAfter first grants offered state ++
        commands M charge terminalAfter second (fun i => grants (i + first))
          (fun i => offered (i + first)) (run M charge terminalAfter first grants offered state) := by
  induction first generalizing grants offered state with
  | zero => simp [commands, run]
  | succ first ih =>
      simp only [Nat.succ_add, commands, run, ih, List.append_assoc]
      simp only [Nat.add_assoc, Nat.add_comm first 1]

#print axioms run_is_kernel
#print axioms run_ready
#print axioms queued_task_gets_visit
#print axioms run_add
#print axioms zero_preserves_pool
#print axioms terminal_keeps_call
#print axioms pending_refusal
#print axioms pending_acceptance
#print axioms commands_add

/-! ### One-return native service admission

The native host adds compatibility checks and a read-only current-final
validator to the existing owned callback boundary. The provider below is an
adapter for that same boundary, with one acceptance grant. Its counters are
proof observations, not an execution journal required by ordinary service.
They count calls only; callback work, arrivals, cleanup and other host work
require separate cost contracts.
-/

namespace Visit

variable (sourceCharge : Charge M)

inductive Kind where
  | compatibility | producer | consumer | finalCurrent | rotations | retirements
  deriving DecidableEq, Repr

abbrev Account := Kind → Nat

def empty : Account := fun _ => 0

def bump (account : Account) (kind : Kind) : Account :=
  fun other => account other + if other = kind then 1 else 0

/-- A selected visit makes at most these calls. An empty queue probe is not
a rotation of a selected task and contributes no call to this subaccount. -/
def limit : Account
  | .compatibility => 2
  | _ => 1

def pollLimit : Account
  | .rotations => 0
  | kind => limit kind

/-- Compatibility may change private retry configuration without polling the
producer. The final marker includes the producer's completion condition; its
optional current validator runs only after successful acceptance and is
read-only. Source-view preservation by compatibility is a local adapter law. -/
structure Hooks where
  compatible : M.State () () → Bool × M.State () ()
  finalMarker : Item → Option Terminal
  finalCurrent : Option (M.State () () → Bool) := none

structure Frame where
  provider : M.State () ()
  account : Account := empty
  finalized : Option Terminal := none

variable (hooks : Hooks M)

def finish (item : Item) (state : Frame M) : Frame M :=
  match hooks.finalMarker item with
  | none => state
  | some reason => match hooks.finalCurrent with
      | none => { state with finalized := some reason }
      | some current => { state with
          account := bump state.account .finalCurrent
          finalized := if current state.provider then some reason else none }

/-- Only the delivery wrapper is new: its producer and consumer operations
are precisely the supplied owned provider's operations. Refusal retains the
complete callback post-state. The final check cannot produce another item. -/
def guarded : Provider (protocol Item Terminal) where
  State _ _ := Frame M
  step := fun state request => match request with
    | .next =>
        let reply := M.step state.provider .next
        ⟨reply.1, { state with
          provider := reply.2
          account := bump state.account .producer }⟩
    | .accept item =>
        let checked := hooks.compatible state.provider
        let checkedState : Frame M := { state with
          provider := checked.2
          account := bump state.account .compatibility }
        if checked.1 then
          let reply := M.step checked.2 (.accept item)
          let consumed : Frame M := { checkedState with
            provider := reply.2
            account := bump checkedState.account .consumer }
          ⟨reply.1, if reply.1 then finish M hooks item consumed else consumed⟩
        else ⟨false, checkedState⟩

def guardedCharge : Charge (guarded M hooks) := fun state request =>
  match request with
  | .next => sourceCharge state.provider .next
  | .accept item =>
      let checked := hooks.compatible state.provider
      if checked.1 then sourceCharge checked.2 (.accept item) else 0

private theorem guarded_next (state : Frame M) :
    (guarded M hooks).step (base := ()) (index := ()) state .next =
      ⟨(M.step state.provider .next).1, { state with
        provider := (M.step state.provider .next).2
        account := bump state.account .producer }⟩ := rfl

/-- The finite callback core is the maintained owned sequencer. A dynamic
final check is performed by the delivery adapter; the result is installed
after this one-return call, without polling or reaccepting anything. -/
def core (paid accepted : Nat) (pending : Option Item) (state : Frame M) :
    Call (guarded M hooks) :=
  resumeCall (guarded M hooks) (guardedCharge M sourceCharge hooks) 1
    (paid, ⟨none, pending, accepted⟩, state)

def install (later : Call (guarded M hooks)) : Call M :=
  (later.1, { later.2.1 with
    terminal := later.2.1.terminal.orElse (fun _ => later.2.2.finalized) }, later.2.2.provider)

def retire (queued : Bool) (later : Call M) (account : Account) : Account :=
  if queued && later.2.1.terminal.isSome then bump account .retirements else account

/-- The enclosing host can poll a selected but unqueued owner. It neither
admits nor rotates membership. An already terminal owner may retire; a false
poll does no callbacks. Fresh producer work has a precheck; a held loan goes
directly to delivery's compatibility check. -/
def poll (enabled queued : Bool) (previous : Call M) : Call M × Account :=
  if previous.2.1.terminal.isSome || !enabled then
    (previous, retire M queued previous empty)
  else
    let checked := match previous.2.1.pending with
      | some _ => (true, (⟨previous.2.2, empty, none⟩ : Frame M))
      | none =>
          let decision := hooks.compatible previous.2.2
          (decision.1, ⟨decision.2, bump empty .compatibility, none⟩)
    if checked.1 then
      let later := core M sourceCharge hooks previous.1 previous.2.1.accepted
        previous.2.1.pending checked.2
      let call := install M hooks later
      (call, retire M queued call later.2.2.account)
    else ((previous.1, previous.2.1, checked.2.provider), checked.2.account)

def visit (enabled : Bool) (previous : Option (Call M)) : Option (Call M) × Account :=
  match previous with
  | none => (none, empty)
  | some call =>
      let later := poll M sourceCharge hooks enabled true call
      (some later.1, bump later.2 .rotations)

/-- Independent cursor interpretation of the core, including its actual
provider state, paid account and pending loan. This is an instance of the
existing correspondence, not validation by defining one side as the other. -/
theorem core_uses_common_cursor (paid accepted : Nat) (pending : Option Item)
    (state : Frame M) :
    Mettapedia.Machines.Cursor.advance (guarded M hooks)
        (client Item Terminal) (guardedCharge M sourceCharge hooks) 3
        (packet (guarded M hooks) 1 pending accepted state) =
      let later := core M sourceCharge hooks paid accepted pending state
      (later.1 - paid, .done ⟨(), later.2.1, later.2.2⟩) := by
  have same := callback_call_instantiates_common_cursor (guarded M hooks)
    (guardedCharge M sourceCharge hooks) 1 0 accepted pending state
  simpa only [core, resumeCall, Nat.add_sub_cancel_left] using same

def permissive : Hooks M := ⟨fun state => (true, state), fun _ => none, none⟩

/-- Unconditional compatibility and no final shortcut leave the owned
provider unchanged, through the maintained local provider-refinement law. -/
def forget : Hom (guarded M (permissive M)) M where
  map := fun {base index} state => by
    cases base; cases index; exact state.provider
  step := by
    intro base index state request
    cases base; cases index
    cases request with
    | next =>
        cases reply : M.step state.provider .next
        simp [guarded, permissive, protocol, reply]
    | accept item =>
        cases reply : M.step state.provider (.accept item) with
        | mk allowed after => cases allowed <;> simp [guarded, permissive, finish, protocol, reply]

theorem permissive_core_refines_owned (paid accepted : Nat) (pending : Option Item)
    (state : Frame M) :
    mapCall (guarded M (permissive M)) (forget M)
        (core M sourceCharge (permissive M) paid accepted pending state) =
      resumeCall M sourceCharge 1 (paid, ⟨none, pending, accepted⟩, state.provider) := by
  apply resumeCall_account_transport
  intro base index frame request
  cases base; cases index; cases request <;> rfl

private theorem finish_account (item : Item) (state : Frame M) (kind : Kind) :
    (finish M hooks item state).account kind ≤
      state.account kind + if kind = .finalCurrent then 1 else 0 := by
  cases marker : hooks.finalMarker item <;> simp only [finish, marker]
  · omega
  · cases hooks.finalCurrent <;> simp [bump]

private theorem acceptance_account (item : Item) (state : Frame M) (kind : Kind) :
    ((guarded M hooks).step (base := ()) (index := ()) state (.accept item)).2.account kind ≤
      state.account kind + (if kind = .compatibility then 1 else 0) +
        (if kind = .consumer then 1 else 0) + (if kind = .finalCurrent then 1 else 0) := by
  dsimp only [guarded]
  split
  · split
    · have bound := finish_account M hooks item
        (⟨(M.step (hooks.compatible state.provider).2 (.accept item)).2,
          bump (bump state.account .compatibility) .consumer, state.finalized⟩ : Frame M) kind
      simpa [bump, Nat.add_assoc] using bound
    · simp [bump]
  · simp [bump]; omega

private theorem core_account (paid accepted : Nat) (pending : Option Item)
    (state : Frame M) (kind : Kind) :
    (core M sourceCharge hooks paid accepted pending state).2.2.account kind ≤
      state.account kind + (if kind = .compatibility then 1 else 0) +
        (if kind = .producer ∧ pending.isNone then 1 else 0) +
        (if kind = .consumer then 1 else 0) + (if kind = .finalCurrent then 1 else 0) := by
  cases pending with
  | some item =>
      have bound := acceptance_account M hooks item state kind
      cases decision : (guarded M hooks).step (base := ()) (index := ()) state (.accept item) with
      | mk allowed after =>
          cases allowed <;> simpa [core, resumeCall, fromCallbacks, decision] using bound
  | none =>
      cases response : M.step state.provider .next with
      | mk reply after =>
          cases reply with
          | paused => simp [core, resumeCall, fromCallbacks, guarded, response, bump]; omega
          | terminal reason => simp [core, resumeCall, fromCallbacks, guarded, response, bump]; omega
          | returned item =>
              let next : Frame M := { state with
                provider := after
                account := bump state.account .producer }
              have bound := acceptance_account M hooks item next kind
              cases decision : (guarded M hooks).step (base := ()) (index := ()) next
                  (.accept item) with
              | mk allowed final =>
                  dsimp only [next] at decision bound
                  cases allowed <;>
                    simpa [core, resumeCall, fromCallbacks, guarded_next, response,
                      decision, bump, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

private theorem retire_account (queued : Bool) (later : Call M) (account : Account)
    (kind : Kind) :
    retire M queued later account kind ≤
      account kind + if kind = .retirements then 1 else 0 := by
  unfold retire
  split <;> simp [bump]

/-- All six bounds are derived from the actual finite branch structure. The
retirement counter is membership removal, not owner cleanup or disposal. -/
theorem poll_account_le (enabled queued : Bool) (previous : Call M) (kind : Kind) :
    (poll M sourceCharge hooks enabled queued previous).2 kind ≤ pollLimit kind := by
  rcases previous with ⟨paid, ⟨terminal, pending, accepted⟩, state⟩
  cases terminal with
  | some reason =>
      cases queued <;> cases kind <;> simp [poll, retire, empty, bump, limit, pollLimit]
  | none =>
      cases enabled with
      | false => cases kind <;> simp [poll, retire, empty, limit, pollLimit]
      | true =>
          cases pending with
          | some item =>
              have bound := core_account M sourceCharge hooks paid accepted (some item)
                ⟨state, empty, none⟩ kind
              have retired := retire_account M queued
                (install M hooks (core M sourceCharge hooks paid accepted (some item) ⟨state, empty, none⟩))
                (core M sourceCharge hooks paid accepted (some item) ⟨state, empty, none⟩).2.2.account kind
              change retire M queued _ _ kind ≤ _
              cases kind <;> simp [empty, limit, pollLimit] at bound retired ⊢ <;> omega
          | none =>
              cases checked : hooks.compatible state with
              | mk allowed after =>
                  cases allowed with
                  | false => cases kind <;> simp [poll, checked, bump, empty, limit, pollLimit]
                  | true =>
                      have bound := core_account M sourceCharge hooks paid accepted none
                        ⟨after, bump empty .compatibility, none⟩ kind
                      have retired := retire_account M queued
                        (install M hooks (core M sourceCharge hooks paid accepted none
                          ⟨after, bump empty .compatibility, none⟩))
                        (core M sourceCharge hooks paid accepted none
                          ⟨after, bump empty .compatibility, none⟩).2.2.account kind
                      simp only [poll, checked, Option.isSome_none, Bool.false_or,
                        Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                      cases kind <;> simp [empty, bump, limit, pollLimit] at bound retired ⊢ <;> omega

theorem poll_has_no_rotation (enabled queued : Bool) (previous : Call M) :
    (poll M sourceCharge hooks enabled queued previous).2 .rotations = 0 := by
  exact Nat.eq_zero_of_le_zero (poll_account_le M sourceCharge hooks enabled queued previous .rotations)

theorem visit_account_le (enabled : Bool) (previous : Option (Call M)) (kind : Kind) :
    (visit M sourceCharge hooks enabled previous).2 kind ≤ limit kind := by
  cases previous with
  | none => cases kind <;> simp [visit, empty, limit]
  | some call =>
      cases kind with
      | rotations => simp [visit, bump, poll_has_no_rotation, limit]
      | _ => simpa [visit, bump, pollLimit] using poll_account_le M sourceCharge hooks enabled true call _

/-- A fresh-call refusal changes only the compatibility callback's private
post-state. The paid prefix, loan and acceptance record remain unchanged. -/
theorem precheck_refusal (paid accepted : Nat) (before after : M.State () ())
    (queued : Bool) (denied : hooks.compatible before = (false, after)) :
    poll M sourceCharge hooks true queued (paid, ⟨none, none, accepted⟩, before) =
      ((paid, ⟨none, none, accepted⟩, after), bump empty .compatibility) := by
  simp [poll, denied]

/-- Not calling the producer is distinct from compatibility preserving its
source. This local adapter law proves both, while permitting retry-context
updates and preserving the original paid and acceptance records. -/
theorem precheck_refusal_preserves_source {SourceView : Type*}
    (view : M.State () () → SourceView)
    (stable : ∀ state, view (hooks.compatible state).2 = view state)
    (paid accepted : Nat) (before after : M.State () ()) (queued : Bool)
    (denied : hooks.compatible before = (false, after)) :
    let later := poll M sourceCharge hooks true queued (paid, ⟨none, none, accepted⟩, before)
    later.1.1 = paid ∧ later.1.2.1 = ⟨none, none, accepted⟩ ∧
      view later.1.2.2 = view before ∧ later.2 .producer = 0 := by
  dsimp only
  rw [precheck_refusal M sourceCharge hooks paid accepted before after queued denied]
  have unchanged := stable before
  rw [denied] at unchanged
  exact ⟨rfl, rfl, unchanged, rfl⟩

/-- Pausing without an item still incurs one real producer call. -/
theorem producer_pause (paid accepted : Nat) (before prepared after : M.State () ())
    (queued : Bool) (precheck : hooks.compatible before = (true, prepared))
    (paused : M.step prepared .next = ⟨.paused, after⟩) :
    let later := poll M sourceCharge hooks true queued (paid, ⟨none, none, accepted⟩, before)
    later.1 = (paid + sourceCharge prepared .next, ⟨none, none, accepted⟩, after) ∧
      later.2 .compatibility = 1 ∧ later.2 .producer = 1 ∧
      later.2 .consumer = 0 ∧ later.2 .finalCurrent = 0 ∧ later.2 .retirements = 0 := by
  simp [poll, precheck, core, resumeCall, fromCallbacks, guarded, paused, install,
    retire, guardedCharge, bump, empty]

/-- A producer terminal reply is distinct from a pause and retires only its
queued membership; no consumer or final-certificate callback is called. -/
theorem producer_terminal (paid accepted : Nat) (before prepared after : M.State () ())
    (reason : Terminal) (queued : Bool)
    (precheck : hooks.compatible before = (true, prepared))
    (finished : M.step prepared .next = ⟨.terminal reason, after⟩) :
    let later := poll M sourceCharge hooks true queued (paid, ⟨none, none, accepted⟩, before)
    later.1 = (paid + sourceCharge prepared .next, ⟨some reason, none, accepted⟩, after) ∧
      later.2 .compatibility = 1 ∧ later.2 .producer = 1 ∧
      later.2 .consumer = 0 ∧ later.2 .finalCurrent = 0 ∧
      later.2 .retirements = if queued then 1 else 0 := by
  cases queued <;> simp [poll, precheck, core, resumeCall, fromCallbacks, guarded,
    finished, install, retire, guardedCharge, bump, empty]

/-- A delivery refusal after a producer return retains that same return and
the paid producer prefix. It does not invoke the actual consumer. -/
theorem postcheck_refusal (paid accepted : Nat) (before prepared pulled after : M.State () ())
    (item : Item) (queued : Bool)
    (precheck : hooks.compatible before = (true, prepared))
    (produced : M.step prepared .next = ⟨.returned item, pulled⟩)
    (denied : hooks.compatible pulled = (false, after)) :
    let later := poll M sourceCharge hooks true queued (paid, ⟨none, none, accepted⟩, before)
    later.1 = (paid + sourceCharge prepared .next, ⟨none, some item, accepted⟩, after) ∧
      later.2 .compatibility = 2 ∧ later.2 .producer = 1 ∧
      later.2 .consumer = 0 ∧ later.2 .finalCurrent = 0 := by
  simp [poll, precheck, core, resumeCall, fromCallbacks, guarded, produced, denied,
    install, retire, guardedCharge, bump, empty]

/-- An actual consumer refusal may change private context. The complete
post-state and paid producer work are retained with the unchanged loan. -/
theorem consumer_refusal (paid accepted : Nat)
    (before prepared pulled compatible after : M.State () ()) (item : Item) (queued : Bool)
    (precheck : hooks.compatible before = (true, prepared))
    (produced : M.step prepared .next = ⟨.returned item, pulled⟩)
    (postcheck : hooks.compatible pulled = (true, compatible))
    (refused : M.step compatible (.accept item) = ⟨false, after⟩) :
    let later := poll M sourceCharge hooks true queued (paid, ⟨none, none, accepted⟩, before)
    later.1 = (paid + (sourceCharge prepared .next + sourceCharge compatible (.accept item)),
      ⟨none, some item, accepted⟩, after) ∧
      later.2 .compatibility = 2 ∧ later.2 .producer = 1 ∧
      later.2 .consumer = 1 ∧ later.2 .finalCurrent = 0 := by
  simp [poll, precheck, core, resumeCall, fromCallbacks, guarded, produced, postcheck,
    refused, install, retire, guardedCharge, bump, empty]

theorem held_loan_no_producer (paid accepted : Nat) (item : Item)
    (state : M.State () ()) (queued : Bool) :
    (poll M sourceCharge hooks true queued (paid, ⟨none, some item, accepted⟩, state)).2 .producer = 0 := by
  have bound := core_account M sourceCharge hooks paid accepted (some item)
    ⟨state, empty, none⟩ .producer
  have retired := retire_account M queued
    (install M hooks (core M sourceCharge hooks paid accepted (some item) ⟨state, empty, none⟩))
    (core M sourceCharge hooks paid accepted (some item) ⟨state, empty, none⟩).2.2.account .producer
  change retire M queued
    (install M hooks (core M sourceCharge hooks paid accepted (some item) ⟨state, empty, none⟩))
    (core M sourceCharge hooks paid accepted (some item) ⟨state, empty, none⟩).2.2.account .producer = 0
  simp [empty] at bound retired
  omega

theorem terminal_has_no_callbacks (enabled queued : Bool) (paid accepted : Nat)
    (pending : Option Item) (reason : Terminal) (state : M.State () ()) :
    let later := poll M sourceCharge hooks enabled queued (paid, ⟨some reason, pending, accepted⟩, state)
    later.1 = (paid, ⟨some reason, pending, accepted⟩, state) ∧
      later.2 .compatibility = 0 ∧ later.2 .producer = 0 ∧ later.2 .consumer = 0 ∧
      later.2 .finalCurrent = 0 ∧ later.2 .retirements = if queued then 1 else 0 := by
  cases queued <;> simp [poll, retire, bump, empty]

theorem disabled_has_no_callbacks (queued : Bool) (previous : Call M) :
    let later := poll M sourceCharge hooks false queued previous
    later.1 = previous ∧ later.2 .compatibility = 0 ∧ later.2 .producer = 0 ∧
      later.2 .consumer = 0 ∧ later.2 .finalCurrent = 0 := by
  simp only [poll, Bool.not_false, Bool.or_true, ↓reduceIte]
  unfold retire
  split <;> simp [bump, empty]

/-! The cost join uses the old complete-slot meter. A component measurement
is bounded by its actual number of callback invocations times the declared
bound for one invocation. Cleanup is outside the six-call subaccount. The
existing slot still accounts for all arrivals and remaining bookkeeping.
-/

section Costs

variable {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost] [IsOrderedAddMonoid Cost]

def total (costs : Kind → Cost) : Cost :=
  costs .compatibility + costs .producer + costs .consumer + costs .finalCurrent +
    costs .rotations + costs .retirements

def allowance (prices : Kind → Cost) : Cost := total (fun kind => limit kind • prices kind)

private theorem total_mono (first second : Kind → Cost)
    (ordered : ∀ kind, first kind ≤ second kind) : total first ≤ total second :=
  add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (ordered .compatibility) (ordered .producer)) (ordered .consumer))
      (ordered .finalCurrent)) (ordered .rotations)) (ordered .retirements)

/-- Component measurements and local callback bounds imply a genuine
per-visit bound. No callback's instructions are bounded by its call count. -/
theorem measured_visit_cost_le (enabled : Bool) (previous : Option (Call M))
    (measured prices : Kind → Cost) (nonnegative : ∀ kind, 0 ≤ prices kind)
    (localBound : ∀ kind, measured kind ≤
      (visit M sourceCharge hooks enabled previous).2 kind • prices kind) :
    total measured ≤ allowance prices := by
  apply total_mono
  intro kind
  exact (localBound kind).trans (nsmul_le_nsmul_left (nonnegative kind)
    (visit_account_le M sourceCharge hooks enabled previous kind))

variable (meter : ReadyQueue.ServiceMeter Cost) (prices : Kind → Cost)
    (cleanupBound arrivalBound bookkeepingBound : Cost)
    (slots : Nat) (keep : Nat → Bool) (offered : Nat → List Nat) (state : ReadyQueue.State)
    (enabled : Nat → Bool) (calls : Nat → Option (Call M))
    (measured : Nat → Kind → Cost) (cleanup : Nat → Cost)
    (nonnegative : ∀ kind, 0 ≤ prices kind)
    (localBound : ∀ n, n < slots → ∀ kind, measured n kind ≤
      (visit M sourceCharge hooks (enabled n) (calls n)).2 kind • prices kind)
    (handling : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered state).2 (keep n) (offered n)).handling =
        total (measured n) + cleanup n)
    (cleanupCosts : ∀ n, n < slots → cleanup n ≤ cleanupBound)
    (arrivals : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered state).2 (keep n) (offered n)).arrivals ≤ arrivalBound)
    (bookkeeping : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered state).2 (keep n) (offered n)).bookkeeping ≤
        bookkeepingBound)

include sourceCharge hooks enabled calls measured cleanup nonnegative localBound
  handling cleanupCosts arrivals bookkeeping

/-- The callback and queue counts discharge the handling part of the maintained
whole-slot admission theorem. The host supplies actual component measurements
and their local cost contracts, including cleanup, arrivals and bookkeeping. -/
theorem serviceCostBound_of_visits :
    ReadyQueue.ServiceCostBound meter
      (allowance prices + cleanupBound + arrivalBound + bookkeepingBound)
      slots keep offered state := by
  apply ReadyQueue.ServiceCostBound.of_components meter
    (allowance prices + cleanupBound) arrivalBound bookkeepingBound slots keep offered state
  · intro n before
    rw [handling n before]
    exact add_le_add
      (measured_visit_cost_le M sourceCharge hooks (enabled n) (calls n) (measured n) prices
        nonnegative (localBound n before)) (cleanupCosts n before)
  · exact arrivals
  · exact bookkeeping

/-- Actual ready service accumulates the whole-slot bound obtained from the
finite native visit protocol. It includes empty and retired service slots. -/
theorem service_cost_le :
    (ReadyQueue.costedServiceRun meter slots keep offered state).2 ≤
      slots • (allowance prices + cleanupBound + arrivalBound + bookkeepingBound) :=
  ReadyQueue.costedServiceRun_cost_le meter _ slots keep offered state
    (serviceCostBound_of_visits M sourceCharge hooks meter prices cleanupBound arrivalBound
      bookkeepingBound slots keep offered state enabled calls measured cleanup nonnegative
      localBound handling cleanupCosts arrivals bookkeeping)

/-- Repeated requested opportunities and cumulative cost concern the same
executed service slice. Successful acceptance still requires the consumer's
own progress contract. -/
theorem requested_service_cost_le (demand target : Nat)
    (horizon : slots = demand * state.capacity)
    (valid : ReadyQueue.invariant state) (member : target ∈ state.tasks)
    (retained : ∀ n, (ReadyQueue.serviceRun (n + 1) keep offered state).1.count target < demand →
      (ReadyQueue.serviceRun n keep offered state).2.tasks.head? = some target → keep n = true) :
    demand ≤ (ReadyQueue.costedServiceRun meter slots keep offered state).1.1.count target ∧
      (ReadyQueue.costedServiceRun meter slots keep offered state).2 ≤
        slots • (allowance prices + cleanupBound + arrivalBound + bookkeepingBound) := by
  refine ⟨?_, service_cost_le M sourceCharge hooks meter prices cleanupBound arrivalBound
    bookkeepingBound slots keep offered state enabled calls measured cleanup nonnegative
    localBound handling cleanupCosts arrivals bookkeeping⟩
  simpa only [ReadyQueue.costedServiceRun_erases, horizon] using
    ReadyQueue.requested_task_gets_bounded_service demand state target keep offered
      valid member retained

theorem retained_service_cost_le (demand target : Nat)
    (horizon : slots = demand * state.capacity)
    (valid : ReadyQueue.invariant state) (member : target ∈ state.tasks)
    (retained : ∀ n, (ReadyQueue.serviceRun n keep offered state).2.tasks.head? = some target →
      keep n = true) :
    demand ≤ (ReadyQueue.costedServiceRun meter slots keep offered state).1.1.count target ∧
      (ReadyQueue.costedServiceRun meter slots keep offered state).2 ≤
        slots • (allowance prices + cleanupBound + arrivalBound + bookkeepingBound) :=
  requested_service_cost_le M sourceCharge hooks meter prices cleanupBound arrivalBound
    bookkeepingBound slots keep offered state enabled calls measured cleanup nonnegative
    localBound handling cleanupCosts arrivals bookkeeping demand target horizon valid member
    (fun n _ atHead => retained n atHead)

end Costs

/-! A producer callback can itself be a retained finite primitive slice. The
source primitive's price is not the callback's invocation count: its bound is
derived from the actual transition account and the selected work quantum.
The final source probe and callback adaptation have their own price.
-/

namespace Primitive

variable {Input : Type} (kernel : MachineCore Input) (quantum : Nat)

/-- A finite slice retains the actual source state. A terminal state is
returned as a terminal observation, which need not be a successful answer.
No payload consumer is used by this operation adapter. -/
abbrev producer : Provider (protocol Empty kernel.State) where
  State _ _ := kernel.State
  step := fun state request => match request with
    | .next =>
        if quantum = 0 then ⟨.paused, state⟩ else
          let later := MachineCore.runSlice kernel quantum state
          match kernel.step later.1 with
          | none => ⟨.terminal later.1, later.1⟩
          | some _ => ⟨.paused, later.1⟩
    | .accept impossible => nomatch impossible

def debit : Charge (producer kernel quantum) := fun state request => match request with
  | .next => (MachineCore.runSlice kernel quantum state).2
  | .accept impossible => nomatch impossible

theorem next_retains_slice (state : kernel.State) :
    ((producer kernel quantum).step (base := ()) (index := ()) state .next).2 =
      (MachineCore.runSlice kernel quantum state).1 := by
  cases quantum with
  | zero => rfl
  | succ quantum =>
      cases final : kernel.step (MachineCore.runSlice kernel (quantum + 1) state).1 <;>
        simp [producer, final]

/-- The service callback installs the actual machine endpoint and adds only
the primitive transitions taken in that slice to the retained paid prefix. -/
theorem poll_live_paid_slice (paid accepted : Nat) (state : kernel.State) (queued : Bool) :
    let later := poll (producer kernel quantum) (debit kernel quantum)
      (permissive (producer kernel quantum)) true queued
      (paid, ⟨none, none, accepted⟩, state)
    (later.1.1, later.1.2.2) = MachineCore.paidSlice kernel quantum (paid, state) := by
  cases quantum with
  | zero =>
      simp [poll, permissive, core, resumeCall, fromCallbacks, guarded, producer,
        install, guardedCharge, debit, MachineCore.paidSlice, MachineCore.runSlice]
  | succ quantum =>
      cases final : kernel.step (MachineCore.runSlice kernel (quantum + 1) state).1 <;>
        simp [poll, permissive, core, resumeCall, fromCallbacks, guarded, producer, final,
          install, guardedCharge, debit, MachineCore.paidSlice]

theorem producer_calls (enabled : Bool) (previous : Option (Call (producer kernel quantum))) :
    (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 .producer =
      match previous with
      | none => 0
      | some call => if call.2.1.terminal.isSome || !enabled then 0 else 1 := by
  cases previous with
  | none => rfl
  | some previous =>
      rcases previous with ⟨paid, ⟨terminal, pending, accepted⟩, state⟩
      cases terminal with
      | some reason => simp [visit, poll, retire, bump, empty]
      | none =>
          cases enabled with
          | false => simp [visit, poll, retire, bump, empty]
          | true =>
              cases pending with
              | some impossible => exact impossible.elim
              | none =>
                  cases quantum with
                  | zero => simp [visit, poll, permissive, core, resumeCall, fromCallbacks, guarded,
                      producer, install, retire, bump, empty]
                  | succ quantum =>
                      cases final : kernel.step (MachineCore.runSlice kernel (quantum + 1) state).1 <;>
                        simp [visit, poll, permissive, core, resumeCall, fromCallbacks, guarded,
                          producer, final, install, retire, bump, empty]

/-- A positive producer invocation also inspects the reached source state.
This last inspection does not install a possible successor. The observation
is optional mathematical evidence, not a required journal. -/
def nextTrace (state : kernel.State) : List (kernel.State × Option kernel.State) :=
  if quantum = 0 then [] else
    MachineCore.Attempts.trace kernel quantum state ++
      [((MachineCore.runSlice kernel quantum state).1,
        kernel.step (MachineCore.runSlice kernel quantum state).1)]

def callAllowance (quantum : Nat) : Nat := if quantum = 0 then 0 else quantum + 1

theorem nextTrace_length (state : kernel.State) :
    (nextTrace kernel quantum state).length =
      if quantum = 0 then 0 else
        (MachineCore.runSlice kernel quantum state).2 +
          (if (MachineCore.runSlice kernel quantum state).2 < quantum then 1 else 0) + 1 := by
  by_cases zero : quantum = 0
  · simp [nextTrace, zero]
  · simp [nextTrace, zero, MachineCore.Attempts.trace_length_exact]

theorem nextTrace_length_le (state : kernel.State) :
    (nextTrace kernel quantum state).length ≤ callAllowance quantum := by
  by_cases zero : quantum = 0
  · simp [nextTrace, callAllowance, zero]
  · have bounded := MachineCore.runSlice_used_le (MachineCore.Attempts.observer kernel)
      quantum (false, state)
    simpa [nextTrace, callAllowance, zero, MachineCore.Attempts.trace_length] using
      Nat.add_le_add_right bounded 1

theorem zero_inert (state : kernel.State) :
    (producer kernel 0).step (base := ()) (index := ()) state .next = ⟨.paused, state⟩ ∧
      debit kernel 0 (base := ()) (index := ()) state .next = 0 ∧ nextTrace kernel 0 state = [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- No source call at zero allowance changes the retained owner, its paid
prefix, acceptance count or terminal marker, even if its source is final. -/
theorem poll_zero_inert (paid accepted : Nat) (state : kernel.State) (queued : Bool) :
    (poll (producer kernel 0) (debit kernel 0) (permissive (producer kernel 0)) true queued
      (paid, ⟨none, none, accepted⟩, state)).1 = (paid, ⟨none, none, accepted⟩, state) := by
  simp [poll, permissive, core, resumeCall, fromCallbacks, guarded, producer,
    install, guardedCharge, debit, MachineCore.runSlice]

section PrimitiveCosts

variable {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost] [IsOrderedAddMonoid Cost]

/-- Every actual source call, including early stopping and the producer's
final inspection. Zero allowance performs neither kind of source call. -/
def nextCost (price : kernel.State → Cost) (state : kernel.State) : Cost :=
  if quantum = 0 then 0 else
    MachineCore.Attempts.cost kernel price quantum state +
      price (MachineCore.runSlice kernel quantum state).1

omit [Preorder Cost] [IsOrderedAddMonoid Cost] in
theorem nextCost_const (price : Cost) (state : kernel.State) :
    nextCost kernel quantum (fun _ => price) state = (nextTrace kernel quantum state).length • price := by
  by_cases zero : quantum = 0
  · simp [nextCost, nextTrace, zero]
  · simp [nextCost, nextTrace, zero, MachineCore.Attempts.cost_const, add_nsmul]

omit [Preorder Cost] [IsOrderedAddMonoid Cost] in
/-- Splitting a positive invocation adds its intermediate reached-state
inspection. If the first slice already stopped early, restarting also repeats
its stopping probe. Neither call contributes a source transition debit. -/
theorem nextCost_split (price : kernel.State → Cost) (first second : Nat) (state : kernel.State) :
    nextCost kernel first price state +
        nextCost kernel second price (MachineCore.runSlice kernel first state).1 =
      nextCost kernel (first + second) price state +
        (if 0 < first ∧ 0 < second then price (MachineCore.runSlice kernel first state).1 else 0) +
        (if (MachineCore.runSlice kernel first state).2 < first ∧ 0 < second then
          price (MachineCore.runSlice kernel first state).1 else 0) := by
  by_cases firstZero : first = 0
  · subst first
    simp [nextCost, MachineCore.runSlice]
  · by_cases secondZero : second = 0
    · subst second
      simp [nextCost]
    · have firstPositive : 0 < first := by omega
      have secondPositive : 0 < second := by omega
      have combinedNonzero : first + second ≠ 0 := by omega
      have endpoint := congrArg Prod.fst (MachineCore.runSlice_add kernel first second state)
      have combined := MachineCore.Attempts.cost_split kernel price first second state
      simp only [secondPositive, and_true] at combined
      simp only [nextCost, if_neg firstZero, if_neg secondZero, if_neg combinedNonzero,
        firstPositive, secondPositive, and_self, and_true, ↓reduceIte]
      rw [endpoint]
      calc
        _ = (MachineCore.Attempts.cost kernel price first state +
            MachineCore.Attempts.cost kernel price second
              (MachineCore.runSlice kernel first state).1) +
            price (MachineCore.runSlice kernel second (MachineCore.runSlice kernel first state).1).1 +
            price (MachineCore.runSlice kernel first state).1 := by ac_rfl
        _ = _ := by rw [combined]; ac_rfl

theorem nextCost_le (price : kernel.State → Cost) (bound : Cost) (nonnegative : 0 ≤ bound)
    (localBound : ∀ state, price state ≤ bound) (state : kernel.State) :
    nextCost kernel quantum price state ≤ callAllowance quantum • bound := by
  by_cases zero : quantum = 0
  · simp [nextCost, callAllowance, zero]
  · simpa only [nextCost, callAllowance, if_neg zero, add_nsmul, one_nsmul] using
      add_le_add (MachineCore.Attempts.cost_le kernel price bound nonnegative localBound quantum state)
        (localBound (MachineCore.runSlice kernel quantum state).1)

/-- This is source-call work plus separately priced callback adaptation.
The adaptation is not assumed free when the source allowance is zero. -/
def fullProducerCost (price adaptation : kernel.State → Cost) (enabled : Bool)
    (previous : Option (Call (producer kernel quantum))) : Cost :=
  match previous with
  | none => 0
  | some call => if call.2.1.terminal.isSome || !enabled then 0 else
      nextCost kernel quantum price call.2.2 + adaptation call.2.2

theorem full_producer_cost_le (price adaptation : kernel.State → Cost)
    (primitiveBound adaptationBound : Cost) (nonnegative : 0 ≤ primitiveBound)
    (primitivePrices : ∀ state, price state ≤ primitiveBound)
    (adaptationPrices : ∀ state, adaptation state ≤ adaptationBound)
    (enabled : Bool) (previous : Option (Call (producer kernel quantum))) :
    fullProducerCost kernel quantum price adaptation enabled previous ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 .producer •
          (callAllowance quantum • primitiveBound + adaptationBound) := by
  rw [producer_calls]
  cases previous with
  | none => simp [fullProducerCost]
  | some call =>
      change (if call.2.1.terminal.isSome || !enabled then 0 else
        nextCost kernel quantum price call.2.2 + adaptation call.2.2) ≤
          (if call.2.1.terminal.isSome || !enabled then 0 else 1) •
            (callAllowance quantum • primitiveBound + adaptationBound)
      split_ifs
      · simp
      · simpa only [one_nsmul] using add_le_add
          (nextCost_le kernel quantum price primitiveBound nonnegative primitivePrices call.2.2)
          (adaptationPrices call.2.2)

theorem full_callback_bounds (price adaptation : kernel.State → Cost)
    (primitiveBound adaptationBound : Cost) (nonnegative : 0 ≤ primitiveBound)
    (primitivePrices : ∀ state, price state ≤ primitiveBound)
    (adaptationPrices : ∀ state, adaptation state ≤ adaptationBound)
    (enabled : Bool) (previous : Option (Call (producer kernel quantum)))
    (measured prices : Kind → Cost)
    (otherCosts : ∀ kind, kind ≠ .producer → measured kind ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 kind • prices kind) :
    ∀ kind, (Function.update measured .producer
        (fullProducerCost kernel quantum price adaptation enabled previous)) kind ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 kind •
          (Function.update prices .producer
            (callAllowance quantum • primitiveBound + adaptationBound)) kind := by
  intro kind
  by_cases same : kind = .producer
  · subst kind
    simpa only [Function.update_self] using full_producer_cost_le kernel quantum price adaptation
      primitiveBound adaptationBound nonnegative primitivePrices adaptationPrices enabled previous
  · simpa only [Function.update_of_ne same] using otherCosts kind same

theorem full_visit_cost_le (price adaptation : kernel.State → Cost)
    (primitiveBound adaptationBound : Cost) (nonnegative : 0 ≤ primitiveBound)
    (adaptationNonnegative : 0 ≤ adaptationBound)
    (primitivePrices : ∀ state, price state ≤ primitiveBound)
    (adaptationPrices : ∀ state, adaptation state ≤ adaptationBound)
    (enabled : Bool) (previous : Option (Call (producer kernel quantum)))
    (measured prices : Kind → Cost) (priceNonnegative : ∀ kind, 0 ≤ prices kind)
    (otherCosts : ∀ kind, kind ≠ .producer → measured kind ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 kind • prices kind) :
    total (Function.update measured .producer
      (fullProducerCost kernel quantum price adaptation enabled previous)) ≤
        allowance (Function.update prices .producer
          (callAllowance quantum • primitiveBound + adaptationBound)) := by
  apply measured_visit_cost_le (producer kernel quantum) (debit kernel quantum)
    (permissive (producer kernel quantum)) enabled previous
  · intro kind
    by_cases same : kind = .producer
    · subst kind
      simpa only [Function.update_self] using
        add_nonneg (nsmul_nonneg nonnegative (callAllowance quantum)) adaptationNonnegative
    · simpa only [Function.update_of_ne same] using priceNonnegative kind
  · exact full_callback_bounds kernel quantum price adaptation primitiveBound adaptationBound
      nonnegative primitivePrices adaptationPrices enabled previous measured prices otherCosts

/-- Derived source-call prices fill the producer component of the existing
whole-slot contract. Host cleanup, intake and bookkeeping remain explicit. -/
theorem full_serviceCostBound_of_visits (price adaptation : kernel.State → Cost)
    (primitiveBound adaptationBound : Cost) (nonnegative : 0 ≤ primitiveBound)
    (adaptationNonnegative : 0 ≤ adaptationBound)
    (primitivePrices : ∀ state, price state ≤ primitiveBound)
    (adaptationPrices : ∀ state, adaptation state ≤ adaptationBound)
    (meter : ReadyQueue.ServiceMeter Cost) (prices : Kind → Cost)
    (cleanupBound arrivalBound bookkeepingBound : Cost)
    (slots : Nat) (keep : Nat → Bool) (offered : Nat → List Nat) (state : ReadyQueue.State)
    (enabled : Nat → Bool) (calls : Nat → Option (Call (producer kernel quantum)))
    (measured : Nat → Kind → Cost) (cleanup : Nat → Cost)
    (priceNonnegative : ∀ kind, 0 ≤ prices kind)
    (otherCosts : ∀ n, n < slots → ∀ kind, kind ≠ .producer → measured n kind ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) (enabled n) (calls n)).2 kind • prices kind)
    (handling : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered state).2 (keep n) (offered n)).handling =
        total (Function.update (measured n) .producer
          (fullProducerCost kernel quantum price adaptation (enabled n) (calls n))) + cleanup n)
    (cleanupCosts : ∀ n, n < slots → cleanup n ≤ cleanupBound)
    (arrivals : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered state).2 (keep n) (offered n)).arrivals ≤ arrivalBound)
    (bookkeeping : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered state).2 (keep n) (offered n)).bookkeeping ≤
        bookkeepingBound) :
    ReadyQueue.ServiceCostBound meter
      (allowance (Function.update prices .producer
        (callAllowance quantum • primitiveBound + adaptationBound)) +
          cleanupBound + arrivalBound + bookkeepingBound) slots keep offered state := by
  apply serviceCostBound_of_visits (producer kernel quantum) (debit kernel quantum)
    (permissive (producer kernel quantum)) meter
    (Function.update prices .producer (callAllowance quantum • primitiveBound + adaptationBound))
    cleanupBound arrivalBound bookkeepingBound slots keep offered state enabled calls
    (fun n => Function.update (measured n) .producer
      (fullProducerCost kernel quantum price adaptation (enabled n) (calls n))) cleanup
  · intro kind
    by_cases same : kind = .producer
    · subst kind
      simpa only [Function.update_self] using
        add_nonneg (nsmul_nonneg nonnegative (callAllowance quantum)) adaptationNonnegative
    · simpa only [Function.update_of_ne same] using priceNonnegative kind
  · intro n before
    exact full_callback_bounds kernel quantum price adaptation primitiveBound adaptationBound
      nonnegative primitivePrices adaptationPrices (enabled n) (calls n) (measured n) prices
      (otherCosts n before)
  · exact handling
  · exact cleanupCosts
  · exact arrivals
  · exact bookkeeping

namespace GraphAudit

open Mettapedia.Algorithms.WellFoundedServices
open Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph

/-- The actual retained DFS supplies the producer's primitive-price premise.
The fixed component still owes native memory, indexing and allocation prices;
the prefix-scan component is derived from the service's real charged work. -/
theorem full_producer_cost_le (graph : Graph) (maximum width quantum : Nat)
    (rowWidth : ∀ node, (graph.rows node).length ≤ width) (fixed scan : Cost)
    (fixedNonnegative : 0 ≤ fixed) (scanNonnegative : 0 ≤ scan)
    (adaptation : OccurrenceGraph.State → Cost) (adaptationBound : Cost)
    (adaptationPrices : ∀ state, adaptation state ≤ adaptationBound)
    (enabled : Bool)
    (previous : Option (Call (producer (sliceMachine graph maximum) quantum))) :
    fullProducerCost (sliceMachine graph maximum) quantum
      (callPrice graph maximum fixed scan) adaptation enabled previous ≤
      (visit (producer (sliceMachine graph maximum) quantum)
        (debit (sliceMachine graph maximum) quantum)
        (permissive (producer (sliceMachine graph maximum) quantum)) enabled previous).2 .producer •
          (callAllowance quantum • (fixed + width • scan) + adaptationBound) :=
  Primitive.full_producer_cost_le (sliceMachine graph maximum) quantum
    (callPrice graph maximum fixed scan) adaptation (fixed + width • scan) adaptationBound
    (add_nonneg fixedNonnegative (nsmul_nonneg scanNonnegative width))
    (callPrice_le graph maximum width rowWidth fixed scan scanNonnegative)
    adaptationPrices enabled previous

/-- Scan-aware graph admission fills the existing whole-slot service
contract. Compatibility, consumption, final-certificate validation, rotation,
retirement, cleanup, arrivals and bookkeeping retain their own obligations. -/
theorem serviceCostBound_of_visits (graph : Graph) (maximum width quantum : Nat)
    (rowWidth : ∀ node, (graph.rows node).length ≤ width) (fixed scan : Cost)
    (fixedNonnegative : 0 ≤ fixed) (scanNonnegative : 0 ≤ scan)
    (adaptation : OccurrenceGraph.State → Cost) (adaptationBound : Cost)
    (adaptationNonnegative : 0 ≤ adaptationBound)
    (adaptationPrices : ∀ state, adaptation state ≤ adaptationBound)
    (meter : ReadyQueue.ServiceMeter Cost) (prices : Kind → Cost)
    (cleanupBound arrivalBound bookkeepingBound : Cost)
    (slots : Nat) (keep : Nat → Bool) (offered : Nat → List Nat) (queue : ReadyQueue.State)
    (enabled : Nat → Bool)
    (calls : Nat → Option (Call (producer (sliceMachine graph maximum) quantum)))
    (measured : Nat → Kind → Cost) (cleanup : Nat → Cost)
    (priceNonnegative : ∀ kind, 0 ≤ prices kind)
    (otherCosts : ∀ n, n < slots → ∀ kind, kind ≠ .producer → measured n kind ≤
      (visit (producer (sliceMachine graph maximum) quantum) (debit (sliceMachine graph maximum) quantum)
        (permissive (producer (sliceMachine graph maximum) quantum)) (enabled n) (calls n)).2 kind •
          prices kind)
    (handling : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered queue).2 (keep n) (offered n)).handling =
        total (Function.update (measured n) .producer
          (fullProducerCost (sliceMachine graph maximum) quantum
            (callPrice graph maximum fixed scan) adaptation (enabled n) (calls n))) + cleanup n)
    (cleanupCosts : ∀ n, n < slots → cleanup n ≤ cleanupBound)
    (arrivals : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered queue).2 (keep n) (offered n)).arrivals ≤ arrivalBound)
    (bookkeeping : ∀ n, n < slots →
      (meter (ReadyQueue.serviceRun n keep offered queue).2 (keep n) (offered n)).bookkeeping ≤
        bookkeepingBound) :
    ReadyQueue.ServiceCostBound meter
      (allowance (Function.update prices .producer
        (callAllowance quantum • (fixed + width • scan) + adaptationBound)) +
          cleanupBound + arrivalBound + bookkeepingBound) slots keep offered queue :=
  Primitive.full_serviceCostBound_of_visits (sliceMachine graph maximum) quantum
    (callPrice graph maximum fixed scan) adaptation (fixed + width • scan) adaptationBound
    (add_nonneg fixedNonnegative (nsmul_nonneg scanNonnegative width)) adaptationNonnegative
    (callPrice_le graph maximum width rowWidth fixed scan scanNonnegative) adaptationPrices
    meter prices cleanupBound arrivalBound bookkeepingBound slots keep offered queue enabled calls
    measured cleanup priceNonnegative otherCosts handling cleanupCosts arrivals bookkeeping

/-- Structural progress makes this abstract DFS producer eventually return
its terminal state. The state records success or an explicit refusal;
terminal return alone does not assert a successful finite observation. -/
theorem terminal_after_structural_allowance (graph : Graph) (maximum : Nat)
    (state : OccurrenceGraph.State) (valid : Valid graph maximum state) :
    (producer (sliceMachine graph maximum) (structuralRank graph state + 1)).step
      (base := ()) (index := ()) state .next =
        ⟨.terminal (OccurrenceGraph.run graph maximum (structuralRank graph state + 1) state),
          OccurrenceGraph.run graph maximum (structuralRank graph state + 1) state⟩ := by
  have final := sliceMachine_final_with_structural_allowance graph maximum state valid
  rw [sliceMachine_run] at final
  simp only [sliceMachine] at final
  have positive : structuralRank graph state + 1 ≠ 0 := by omega
  simp only [producer, if_neg positive, sliceMachine_run, final]

/-- The producer's final inspection may scan the unfinished row without
installing it. Its physical comparison price must therefore be retained
separately from the source cursor's already paid prefix. -/
theorem reached_state_inspection_prices_uninstalled_scan :
    ((producer (sliceMachine depthFanGraph 100) 7).step (base := ()) (index := ())
      depthFanInitial .next).2.indexVisits = 6 ∧
    debit (sliceMachine depthFanGraph 100) 7 (base := ()) (index := ()) depthFanInitial .next = 7 ∧
    nextCost (sliceMachine depthFanGraph 100) 7
      (callPrice depthFanGraph 100 (0 : Nat) 1) depthFanInitial = 10 := by
  refine ⟨?_, by decide, ?_⟩
  · rw [next_retains_slice, sliceMachine_run]
    decide
  · have price : callPrice depthFanGraph 100 (0 : Nat) 1 = scanWork depthFanGraph 100 := by
      funext state
      simp [callPrice]
    rw [price]
    have charged := attempted_scan_account_exact depthFanGraph 100 7 depthFanInitial
    have paidPrefix : (OccurrenceGraph.run depthFanGraph 100 7 depthFanInitial).indexVisits = 6 := by decide
    have inspection : scanWork depthFanGraph 100
        (MachineCore.runSlice (sliceMachine depthFanGraph 100) 7 depthFanInitial).1 = 4 := by
      rw [sliceMachine_run]
      decide
    simp only [show depthFanInitial.indexVisits = 0 from rfl, Nat.zero_add, paidPrefix] at charged
    simp only [nextCost, show (7 : Nat) = 0 ↔ False by decide, ↓reduceIte, charged, inspection]

end GraphAudit

/-- Successful-transition subaccount with separately supplied aggregate host
overhead. `fullProducerCost` instead derives the stopping and reached-state
probe costs. An idle or already terminal owner makes no producer call. -/
def producerCost (price overhead : kernel.State → Cost) (enabled : Bool)
    (previous : Option (Call (producer kernel quantum))) : Cost :=
  match previous with
  | none => 0
  | some call => if call.2.1.terminal.isSome || !enabled then 0 else
      MachineCore.sliceCost kernel price quantum call.2.2 + overhead call.2.2

/-- The producer component of callback admission follows from local primitive
prices and exact bounded execution, rather than assuming a whole callback bound. -/
theorem producer_cost_le (price overhead : kernel.State → Cost) (primitiveBound probeBound : Cost)
    (nonnegative : 0 ≤ primitiveBound) (primitivePrices : ∀ state, price state ≤ primitiveBound)
    (probePrices : ∀ state, overhead state ≤ probeBound)
    (enabled : Bool) (previous : Option (Call (producer kernel quantum))) :
    producerCost kernel quantum price overhead enabled previous ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 .producer •
          (quantum • primitiveBound + probeBound) := by
  rw [producer_calls]
  cases previous with
  | none => simp [producerCost]
  | some call =>
      change (if call.2.1.terminal.isSome || !enabled then 0 else
        MachineCore.sliceCost kernel price quantum call.2.2 + overhead call.2.2) ≤
          (if call.2.1.terminal.isSome || !enabled then 0 else 1) •
            (quantum • primitiveBound + probeBound)
      split_ifs
      · simp
      · simpa only [one_nsmul] using add_le_add
          (MachineCore.sliceCost_le_budget kernel price primitiveBound nonnegative
            primitivePrices quantum call.2.2) (probePrices call.2.2)

/-- This fills the producer entry of the existing six-component admission
contract. All other callback prices remain the enclosing host's obligations. -/
theorem callback_bounds (price overhead : kernel.State → Cost) (primitiveBound probeBound : Cost)
    (nonnegative : 0 ≤ primitiveBound) (primitivePrices : ∀ state, price state ≤ primitiveBound)
    (probePrices : ∀ state, overhead state ≤ probeBound)
    (enabled : Bool) (previous : Option (Call (producer kernel quantum)))
    (measured prices : Kind → Cost)
    (otherCosts : ∀ kind, kind ≠ .producer → measured kind ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 kind • prices kind) :
    ∀ kind, (Function.update measured .producer
        (producerCost kernel quantum price overhead enabled previous)) kind ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 kind •
          (Function.update prices .producer (quantum • primitiveBound + probeBound)) kind := by
  intro kind
  by_cases same : kind = .producer
  · subst kind
    simpa only [Function.update_self] using producer_cost_le kernel quantum price overhead
      primitiveBound probeBound nonnegative primitivePrices probePrices enabled previous
  · simpa only [Function.update_of_ne same] using otherCosts kind same

theorem visit_cost_le (price overhead : kernel.State → Cost) (primitiveBound probeBound : Cost)
    (nonnegative : 0 ≤ primitiveBound) (probeNonnegative : 0 ≤ probeBound)
    (primitivePrices : ∀ state, price state ≤ primitiveBound)
    (probePrices : ∀ state, overhead state ≤ probeBound)
    (enabled : Bool) (previous : Option (Call (producer kernel quantum)))
    (measured prices : Kind → Cost) (priceNonnegative : ∀ kind, 0 ≤ prices kind)
    (otherCosts : ∀ kind, kind ≠ .producer → measured kind ≤
      (visit (producer kernel quantum) (debit kernel quantum)
        (permissive (producer kernel quantum)) enabled previous).2 kind • prices kind) :
    total (Function.update measured .producer
      (producerCost kernel quantum price overhead enabled previous)) ≤
        allowance (Function.update prices .producer (quantum • primitiveBound + probeBound)) := by
  apply measured_visit_cost_le (producer kernel quantum) (debit kernel quantum)
    (permissive (producer kernel quantum)) enabled previous
  · intro kind
    by_cases same : kind = .producer
    · subst kind
      simpa only [Function.update_self] using
        add_nonneg (nsmul_nonneg nonnegative quantum) probeNonnegative
    · simpa only [Function.update_of_ne same] using priceNonnegative kind
  · exact callback_bounds kernel quantum price overhead primitiveBound probeBound nonnegative
      primitivePrices probePrices enabled previous measured prices otherCosts

end PrimitiveCosts

#print axioms poll_live_paid_slice
#print axioms zero_inert
#print axioms poll_zero_inert
#print axioms nextTrace_length_le
#print axioms nextCost_const
#print axioms nextCost_split
#print axioms nextCost_le
#print axioms full_producer_cost_le
#print axioms full_callback_bounds
#print axioms full_visit_cost_le
#print axioms full_serviceCostBound_of_visits
#print axioms GraphAudit.full_producer_cost_le
#print axioms GraphAudit.serviceCostBound_of_visits
#print axioms GraphAudit.terminal_after_structural_allowance
#print axioms GraphAudit.reached_state_inspection_prices_uninstalled_scan
#print axioms producer_cost_le
#print axioms callback_bounds
#print axioms visit_cost_le

end Primitive

namespace Controls

open CallbackControls

private def currentHooks : Hooks finalWarming where
  compatible state := (true, state)
  finalMarker := terminalMarker
  finalCurrent := some fun state => state.remaining.isEmpty

/-- The first consumer refusal pays for one producer call. The next visit
retries its held final item and retires only after one real acceptance. -/
theorem refusal_retry_exact_calls :
    let first := visit finalWarming (fun _ _ => 1) currentHooks true
      (some (11, ⟨none, none, 4⟩, ⟨[7], [], 0, false⟩))
    let second := visit finalWarming (fun _ _ => 1) currentHooks true first.1
    first.1 = some (13, ⟨none, some (7, true), 4⟩, ⟨[], [], 1, true⟩) ∧
      first.2 .compatibility = 2 ∧ first.2 .producer = 1 ∧ first.2 .consumer = 1 ∧
      first.2 .finalCurrent = 0 ∧ first.2 .rotations = 1 ∧ first.2 .retirements = 0 ∧
      second.1 = some (14, ⟨some "complete", none, 5⟩, ⟨[], [7], 1, true⟩) ∧
      second.2 .compatibility = 1 ∧ second.2 .producer = 0 ∧ second.2 .consumer = 1 ∧
      second.2 .finalCurrent = 1 ∧ second.2 .rotations = 1 ∧ second.2 .retirements = 1 := by
  dsimp only
  repeat' apply And.intro
  all_goals rfl

private def preparingHooks : Hooks finalWarming where
  compatible state := if state.warmed then (true, state)
    else (false, { state with warmed := true })
  finalMarker := terminalMarker

theorem preparing_preserves_source (state : Cache) :
    ((preparingHooks.compatible state).2.remaining, (preparingHooks.compatible state).2.requested) =
      (state.remaining, state.requested) := by
  dsimp only [preparingHooks]
  split <;> rfl

/-- A denied precheck may prepare private context, but has neither produced
nor charged a loan. A later visit sees that retained configuration. -/
theorem precheck_preparation_does_not_poll :
    let first := visit finalWarming (fun _ _ => 1) preparingHooks true
      (some (11, ⟨none, none, 4⟩, ⟨[7], [], 0, false⟩))
    let second := visit finalWarming (fun _ _ => 1) preparingHooks true first.1
    first.1 = some (11, ⟨none, none, 4⟩, ⟨[7], [], 0, true⟩) ∧
      first.2 .producer = 0 ∧ first.2 .consumer = 0 ∧
      second.1 = some (13, ⟨some "complete", none, 5⟩, ⟨[], [7], 1, true⟩) := by
  decide

/-- The consumer changes the source after its last-item marker was issued.
The current check must see this post-consumer state. -/
private abbrev changedSource : Provider (protocol (Nat × Bool) String) where
  State _ _ := Cache
  step := fun state request => match request with
    | .next => finalWarming.step (base := ()) (index := ()) state .next
    | .accept item =>
        let reply := finalWarming.step (base := ()) (index := ()) state (.accept item)
        ⟨reply.1, if reply.1 then { reply.2 with remaining := [9] } else reply.2⟩

private def changedHooks (check : Bool) : Hooks changedSource where
  compatible state := (true, state)
  finalMarker := terminalMarker
  finalCurrent := if check then some fun state => state.remaining.isEmpty else none

theorem stale_final_marker_keeps_continuation :
    let initial : Option (Call changedSource) :=
      some (0, ⟨none, none, 0⟩, ⟨[7], [], 0, true⟩)
    let checked := visit changedSource (fun _ _ => 1) (changedHooks true) true initial
    let unchecked := visit changedSource (fun _ _ => 1) (changedHooks false) true initial
    checked.1 = some (2, ⟨none, none, 1⟩, ⟨[9], [7], 1, true⟩) ∧
      checked.2 .finalCurrent = 1 ∧ checked.2 .retirements = 0 ∧
      unchecked.1 = some (2, ⟨some "complete", none, 1⟩, ⟨[9], [7], 1, true⟩) ∧
      unchecked.2 .finalCurrent = 0 ∧ unchecked.2 .retirements = 1 := by
  decide

theorem empty_probe_has_no_selected_calls (enabled : Bool) (kind : Kind) :
    (visit finalWarming (fun _ _ => 1) currentHooks enabled none).2 kind = 0 := rfl

theorem retired_owner_is_not_disposed :
    let previous : Call finalWarming :=
      (14, ⟨some "complete", none, 5⟩, ⟨[], [7], 1, true⟩)
    let later := visit finalWarming (fun _ _ => 1) currentHooks true (some previous)
    later.1 = some previous ∧ later.2 .rotations = 1 ∧ later.2 .retirements = 1 ∧
      later.2 .compatibility = 0 ∧ later.2 .producer = 0 ∧ later.2 .consumer = 0 ∧
      later.2 .finalCurrent = 0 := by
  decide

/-! This primitive instance reuses the binding-publication owner's resolver.
Each transition follows at most one alias edge. The original alias allowance
is retained separately from each service quantum. Constructors remain terms;
this is not a structural matcher or a native memory model. -/

namespace AliasSlices

open BindingPublication.Examples

inductive State where
  | running (allowance : Nat) (value : Term)
  | complete (result : Except Error Term)
  deriving DecidableEq, Repr

def step (environment : Env) : State → Option State
  | .complete _ => none
  | .running _ (.atom name) => some (.complete (.ok (.atom name)))
  | .running _ (.pair left right) => some (.complete (.ok (.pair left right)))
  | .running allowance (.var key) => match environment.get key with
      | none => some (.complete (.ok (.var key)))
      | some cell => match allowance with
          | 0 => some (.complete (.error .fuelExhausted))
          | remaining + 1 => some (.running remaining cell.value)

abbrev machine (environment : Env) : MachineCore (Nat × Term) where
  State := State
  load input := .running input.1 input.2
  step := step environment

def meaning (environment : Env) : State → Except Error Term
  | .running allowance value => resolve allowance environment value
  | .complete result => result

theorem step_meaning (environment : Env) (before after : State)
    (advanced : (machine environment).step before = some after) :
    meaning environment after = meaning environment before := by
  cases before with
  | complete result => simp [machine, step] at advanced
  | running allowance value =>
      cases value with
      | atom name =>
          simp only [machine, step, Option.some.injEq] at advanced
          subst after
          simp [meaning, resolve]
      | pair left right =>
          simp only [machine, step, Option.some.injEq] at advanced
          subst after
          simp [meaning, resolve]
      | var key =>
          cases found : environment.get key with
          | none =>
              simp only [machine, step, found, Option.some.injEq] at advanced
              subst after
              simp [meaning, resolve, found]
          | some cell =>
              cases allowance <;>
                simp only [machine, step, found, Option.some.injEq] at advanced <;>
                subst after <;> simp [meaning, resolve, found]

/-- Finite service slices preserve the independent resolver's meaning,
including a live budget endpoint and terminal allowance exhaustion. -/
theorem slice_meaning (environment : Env) (fuel : Nat) (state : State) :
    meaning environment (MachineCore.runSlice (machine environment) fuel state).1 =
      meaning environment state :=
  MachineCore.runSlice_preserves (machine environment) (meaning environment)
    (step_meaning environment) fuel state

def chain (maximum : Nat) : Env :=
  ⟨fun key => if key ≤ maximum then some ⟨none, match key with
      | 0 => .atom 7
      | next + 1 => .var next⟩ else none, BindingPublication.Examples.empty.metadata⟩

/-- Arbitrarily long finite chains take an exact number of primitives,
rather than one opaque pair-sized dispatch. -/
theorem chain_complete (maximum key : Nat) (member : key ≤ maximum) :
    MachineCore.runSlice (machine (chain maximum)) (key + 2)
      (.running (key + 1) (.var key)) = (.complete (.ok (.atom 7)), key + 2) := by
  induction key with
  | zero => simp [MachineCore.runSlice, machine, step, chain]
  | succ key ih =>
      have lower : key ≤ maximum := by omega
      have first : step (chain maximum) (.running (key + 1 + 1) (.var (key + 1))) =
          some (.running (key + 1) (.var key)) := by
        simp [step, chain, member]
      rw [MachineCore.runSlice.eq_def]
      dsimp only
      rw [first]
      change ((MachineCore.runSlice (machine (chain maximum)) (key + 2)
          (.running (key + 1) (.var key))).1,
        (MachineCore.runSlice (machine (chain maximum)) (key + 2)
          (.running (key + 1) (.var key))).2 + 1) = _
      rw [ih lower]

/-- A pair-entry debit paid before the inner walk stays paid once. Its
separate operational account charges every actual primitive transition. -/
theorem chain_keeps_pair_debit (maximum key paid : Nat) (member : key ≤ maximum) :
    MachineCore.accountedPaidSlice (machine (chain maximum)) (fun _ => ((0, 1) : Nat × Nat))
      (key + 2) ((paid, .running (key + 1) (.var key)), (1, 0)) =
        ((paid + (key + 2), .complete (.ok (.atom 7))), (1, key + 2)) := by
  dsimp only [MachineCore.accountedPaidSlice]
  rw [MachineCore.sliceCost_const]
  simp [MachineCore.paidSlice, chain_complete maximum key member]

theorem chain_split_exact (maximum key paid first second : Nat) (member : key ≤ maximum)
    (split : first + second = key + 2) :
    MachineCore.accountedPaidSlice (machine (chain maximum)) (fun _ => ((0, 1) : Nat × Nat)) second
      (MachineCore.accountedPaidSlice (machine (chain maximum)) (fun _ => ((0, 1) : Nat × Nat))
        first ((paid, .running (key + 1) (.var key)), (1, 0))) =
      ((paid + (key + 2), .complete (.ok (.atom 7))), (1, key + 2)) := by
  rw [← MachineCore.accountedPaidSlice_add, split]
  exact chain_keeps_pair_debit maximum key paid member

def cycle : Env :=
  ⟨fun key => match key with
    | 0 => some ⟨none, .var 1⟩
    | 1 => some ⟨none, .var 0⟩
    | _ => none, BindingPublication.Examples.empty.metadata⟩

private def resetAllowance : State → State
  | .running _ value => .running 2 value
  | .complete result => .complete result

/-- Resetting the original allowance at each yield loses cycle control.
The retained execution instead reports incomplete checking. The same
allowance exhaustion can occur on a long acyclic chain. -/
theorem resetting_limit_loses_cycle_control :
    let first := MachineCore.paidSlice (machine cycle) 1 (0, .running 2 (.var 0))
    let second := MachineCore.paidSlice (machine cycle) 1 first
    let proper := MachineCore.paidSlice (machine cycle) 1 second
    let wrongSecond := MachineCore.paidSlice (machine cycle) 1 (first.1, resetAllowance first.2)
    let wrong := MachineCore.paidSlice (machine cycle) 1 (wrongSecond.1, resetAllowance wrongSecond.2)
    first = (1, .running 1 (.var 1)) ∧ second = (2, .running 0 (.var 0)) ∧
      proper = (3, .complete (.error .fuelExhausted)) ∧ wrong = (3, .running 1 (.var 1)) := by
  decide

theorem slice_budget_is_not_alias_allowance :
    MachineCore.runSlice (machine (chain 3)) 1 (.running 4 (.var 3)) =
      (.running 3 (.var 2), 1) ∧
      meaning (chain 3) (.running 3 (.var 2)) = .ok (.atom 7) ∧
      resolve 1 (chain 3) (.var 3) = .error .fuelExhausted ∧
      resolve 0 cycle (.var 0) = .error .fuelExhausted := by
  decide

/-- Actual owned visits use the mid-pair residual, without restarting the
chain or replaying the incoming paid prefix. -/
theorem owned_visits_resume_mid_pair :
    let kernel := machine (chain 3)
    let owned := Primitive.producer kernel 1
    let first := visit owned (Primitive.debit kernel 1) (permissive owned) true
      (some (17, ⟨none, none, 0⟩, .running 4 (.var 3)))
    let second := visit owned (Primitive.debit kernel 1) (permissive owned) true first.1
    first.1 = some (18, ⟨none, none, 0⟩, .running 3 (.var 2)) ∧ first.2 .producer = 1 ∧
      second.1 = some (19, ⟨none, none, 0⟩, .running 2 (.var 1)) ∧ second.2 .producer = 1 := by
  dsimp only
  repeat' apply And.intro
  all_goals rfl

theorem primitive_visit_has_derived_producer_cost :
    Primitive.producerCost (machine (chain 3)) 1 (fun _ => (1 : Nat)) (fun _ => 2) true
      (some (17, ⟨none, none, 0⟩, .running 4 (.var 3))) = 3 := by
  simp [Primitive.producerCost, MachineCore.sliceCost_const, MachineCore.runSlice,
    machine, step, chain]

/-- Early terminal discovery and the producer's reached-state inspection
are both paid source calls, although neither adds a semantic transition. -/
theorem early_terminal_probes_are_paid :
    let kernel := machine (chain 0)
    let state := State.running 1 (.var 0)
    (MachineCore.runSlice kernel 4 state).2 = 2 ∧
      (MachineCore.Attempts.trace kernel 4 state).length = 3 ∧
      (Primitive.nextTrace kernel 4 state).length = 4 ∧
      Primitive.nextCost kernel 4 (fun _ => (1 : Nat)) state = 4 := by
  dsimp only
  simp [Primitive.nextCost_const, Primitive.nextTrace, MachineCore.Attempts.trace,
    MachineCore.runSlice, machine, step, chain]

theorem spare_budget_can_add_a_terminal_probe :
    let kernel := machine (chain 0)
    let state := State.running 1 (.var 0)
    MachineCore.runSlice kernel 2 state = MachineCore.runSlice kernel 4 state ∧
      (Primitive.nextTrace kernel 2 state).length = 3 ∧
      (Primitive.nextTrace kernel 4 state).length = 4 := by
  decide

theorem inspection_does_not_install_successor :
    let kernel := machine (chain 3)
    let state := State.running 4 (.var 3)
    (Primitive.producer kernel 1).step (base := ()) (index := ()) state .next =
        ⟨.paused, .running 3 (.var 2)⟩ ∧
      Primitive.nextTrace kernel 1 state =
        [(state, some (.running 3 (.var 2))),
          (.running 3 (.var 2), some (.running 2 (.var 1)))] ∧
      Primitive.debit kernel 1 (base := ()) (index := ()) state .next = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Resetting an invocation after a terminal check repeats that check.
Successful-transition accounts remain zero, so their additivity is intact. -/
theorem terminal_probe_cost_is_not_additive :
    let kernel := machine (chain 0)
    let state := State.complete (.ok (.atom 7))
    MachineCore.Attempts.cost kernel (fun _ => (1 : Nat)) 1 state +
        MachineCore.Attempts.cost kernel (fun _ => (1 : Nat)) 1 state = 2 ∧
      MachineCore.Attempts.cost kernel (fun _ => (1 : Nat)) 2 state = 1 ∧
      MachineCore.sliceCost kernel (fun _ => (1 : Nat)) 2 state = 0 := by
  dsimp only
  simp [MachineCore.Attempts.cost_const, MachineCore.Attempts.trace,
    MachineCore.sliceCost_const, MachineCore.runSlice, machine, step]

/-- Zero allowance leaves even a final source uninspected and unretired.
The callback's separately priced adaptation can still have a nonzero cost. -/
theorem zero_budget_keeps_final_source_live :
    let kernel := machine (chain 0)
    let state := State.complete (.ok (.atom 7))
    let previous := some (17, ⟨none, none, 0⟩, state)
    let later := visit (Primitive.producer kernel 0) (Primitive.debit kernel 0)
      (permissive (Primitive.producer kernel 0)) true previous
    later.1 = previous ∧ later.2 .producer = 1 ∧ later.2 .retirements = 0 ∧
      Primitive.nextTrace kernel 0 state = [] ∧
      Primitive.nextCost kernel 0 (fun _ => (1 : Nat)) state = 0 ∧
      Primitive.fullProducerCost kernel 0 (fun _ => (1 : Nat)) (fun _ => 2) true previous = 2 := by
  dsimp only
  repeat' apply And.intro
  all_goals rfl

#print axioms slice_meaning
#print axioms chain_complete
#print axioms chain_keeps_pair_debit
#print axioms chain_split_exact
#print axioms resetting_limit_loses_cycle_control
#print axioms slice_budget_is_not_alias_allowance
#print axioms owned_visits_resume_mid_pair
#print axioms primitive_visit_has_derived_producer_cost
#print axioms early_terminal_probes_are_paid
#print axioms spare_budget_can_add_a_terminal_probe
#print axioms inspection_does_not_install_successor
#print axioms terminal_probe_cost_is_not_additive
#print axioms zero_budget_keeps_final_source_live

end AliasSlices

end Controls

#print axioms core_uses_common_cursor
#print axioms permissive_core_refines_owned
#print axioms visit_account_le
#print axioms precheck_refusal
#print axioms precheck_refusal_preserves_source
#print axioms producer_pause
#print axioms producer_terminal
#print axioms postcheck_refusal
#print axioms consumer_refusal
#print axioms held_loan_no_producer
#print axioms terminal_has_no_callbacks
#print axioms disabled_has_no_callbacks
#print axioms measured_visit_cost_le
#print axioms serviceCostBound_of_visits
#print axioms service_cost_le
#print axioms requested_service_cost_le
#print axioms retained_service_cost_le
#print axioms Controls.refusal_retry_exact_calls
#print axioms Controls.precheck_preparation_does_not_poll
#print axioms Controls.preparing_preserves_source
#print axioms Controls.stale_final_marker_keeps_continuation
#print axioms Controls.empty_probe_has_no_selected_calls
#print axioms Controls.retired_owner_is_not_disposed

end Visit

end OwnedService

#print axioms fair_eventually_done
#print axioms eventually_done_iff
#print axioms stream_collect_exact
#print axioms stream_client_exact
#print axioms roundRobin_fair
#print axioms fair_stream_observation

end Mettapedia.Machines.Cursor.FairObservation
