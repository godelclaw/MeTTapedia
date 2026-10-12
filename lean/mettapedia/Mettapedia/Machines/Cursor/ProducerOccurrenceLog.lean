import Mettapedia.Machines.OwnedPullDriverCost
import Mettapedia.Machines.Cursor.SharedOccurrenceOwnership
import Mettapedia.Machines.Cursor.SharedFactorMachine

/-!
# One selected producer feeding an owned occurrence log

The composition stages an actual producer return together with its complete
post-transition residual. Capture and log admission occur before another
producer transition. A full log, a refused capture or refused admission retains
the pending return and the complete residual. Administrative progress, yields,
effect requests, handoffs, interruption and genuine completion stay distinct.
Repeated barrier notices inspect the same retained request; they execute no
host action and do not add answer occurrences.

No active consumer means no producer demand; this leaves execution and log
open rather than certifying exhaustion. Known terminal or retained request
barriers are inspected before row fullness because they execute no producer.

The scheduler below counts composition microsteps, including staging and
admission. This is different from an allowance counting admitted returns and
does not bound callback work or latency. For the owned-driver instance, the
notice projection also recovers the exact number of driver transitions and the
complete residual of the unrecorded common runner. Admission and refusal do not
execute the producer again. Capturing a borrowed return is supplied
as a primitive; its observation law is separate from native root discovery,
copy allocation and cleanup. Compatibility is checked at every producer and
buffered-delivery boundary, but the supplied check is not a proof of source
dependency validity or a transport between contexts.
The check is pure and fixed within one microstep. Revalidation after a native
callback changes its current context is an additional implementation obligation.

An already buffered delivery commutes with each producer microstep and with
any finite producer slice, preserving notices and the complete owned state.
A waiting read does not commute with admission of its next occurrence.
This atomic-operation law does not prove native concurrent memory access.

This construction selects one producer. It grants no equivalence with two
independently chosen computations, effectful broadcast, late subscription,
native parallel execution, or compiled-code verification.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ProducerOccurrenceLog

open Mettapedia.Machines

variable {Producer Borrowed Stored Context Output Effect Handoff Observation : Type}
  {clients : Nat}

inductive ProducerOutcome (Producer Borrowed Effect Handoff : Type) where
  | progress (next : Producer)
  | returned (value : Borrowed) (next : Producer)
  | yielded (next : Producer)
  | effect (request : Effect) (next : Producer)
  | handoff (request : Handoff) (next : Producer)
  | interrupted (next : Producer)
  | completed (next : Producer)

inductive Mode (Effect Handoff : Type) where
  | active
  | effect (request : Effect)
  | handoff (request : Handoff)
  | interrupted
  deriving DecidableEq

structure Execution (Producer Borrowed Effect Handoff : Type) where
  producer : Producer
  pending : Option Borrowed
  accepted : Nat
  mode : Mode Effect Handoff

structure Configuration (Producer Borrowed Stored Context Output Effect Handoff : Type)
    (clients : Nat) where
  execution : Option (Execution Producer Borrowed Effect Handoff)
  context : Context
  delivery : SharedOccurrenceOwnership.Configuration Stored Output clients

inductive Notice (Borrowed Stored Effect Handoff : Type) where
  | progress
  | returned (value : Borrowed)
  | admitted (position : Nat) (value : Stored)
  | captureRefused
  | admissionRefused
  | noConsumers
  | backpressure
  | contextRefused
  | yielded
  | effect (request : Effect)
  | handoff (request : Handoff)
  | interrupted
  | completed
  | detached
  deriving DecidableEq

def initial (producer : Producer) (context : Context) (limit : Nat) :
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  ⟨some ⟨producer, none, 0, .active⟩, context, ⟨SharedOccurrenceLog.initial limit, ∅⟩⟩

def pending (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Option Borrowed := state.execution.bind (fun execution => execution.pending)

private def stage
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    Notice Borrowed Stored Effect Handoff ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  match outcome with
  | .progress next =>
      (.progress, {state with execution := some {execution with producer := next}})
  | .returned value next =>
      (.returned value,
        {state with execution := some {execution with producer := next, pending := some value}})
  | .yielded next =>
      (.yielded, {state with execution := some {execution with producer := next}})
  | .effect request next =>
      (.effect request,
        {state with execution := some {execution with producer := next, mode := .effect request}})
  | .handoff request next =>
      (.handoff request,
        {state with execution := some {execution with producer := next, mode := .handoff request}})
  | .interrupted next =>
      (.interrupted,
        {state with execution := some {execution with producer := next, mode := .interrupted}})
  | .completed next =>
      (.completed,
        {state with
          execution := some {execution with producer := next}
          delivery := {state.delivery with log := SharedOccurrenceLog.complete state.delivery.log}})

/-- Capture refusal and allocation refusal retain the original borrowed return.
The attempted independent copy, if any, remains the capture service's cleanup
responsibility. Only successful append clears the pending return. -/
private def admit (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    Notice Borrowed Stored Effect Handoff ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  match capture value with
  | none => (.captureRefused, state)
  | some stored =>
      if capacity stored then
        match SharedOccurrenceLog.append state.delivery.log stored with
        | (.accepted, log) =>
            (.admitted (SharedOccurrenceLog.pastEnd state.delivery.log) stored,
              {state with
                execution := some {execution with
                  pending := none
                  accepted := execution.accepted + 1}
                delivery := {state.delivery with log := log}})
        | (.backpressure, _) => (.backpressure, state)
        | (.completed, _) => (.completed, state)
      else (.admissionRefused, state)

def hasConsumers (state : SharedOccurrenceLog.State Stored clients) : Bool :=
  (List.finRange clients).any (fun client => (state.positions client).isSome)

/-- One composition microstep. The log-capacity guard precedes every producer
transition and every attempted capture. A pending return excludes a producer
transition; unresolved effect and handoff requests are inert barriers. -/
def pump (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Notice Borrowed Stored Effect Handoff ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  match state.execution with
  | none => (.detached, state)
  | some execution =>
      if !compatible state.context then (.contextRefused, state)
      else if state.delivery.log.completed then (.completed, state)
      else
        match execution.mode with
        | .active =>
            if !hasConsumers state.delivery.log then (.noConsumers, state)
            else if state.delivery.log.rows.length < state.delivery.log.limit then
              match execution.pending with
              | some value => admit capture capacity state execution value
              | none => stage state execution (step execution.producer)
            else (.backpressure, state)
        | .effect request => (.effect request, state)
        | .handoff request => (.handoff request, state)
        | .interrupted => (.interrupted, state)

def run (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) : Nat →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    List (Notice Borrowed Stored Effect Handoff) ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients
  | 0, state => ([], state)
  | ticks + 1, state =>
      let first := pump step capture capacity compatible state
      let rest := run step capture capacity compatible ticks first.2
      (first.1 :: rest.1, rest.2)

/-- Moving the complete execution does not discard buffered occurrences or
caller publications. The log retains its captured source context. -/
def detach (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Option (Execution Producer Borrowed Effect Handoff) ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  (state.execution, {state with execution := none})

inductive DeliveryReply (Stored : Type) where
  | observed (reply : SharedOccurrenceLog.Reply Stored)
  | contextRefused
  deriving DecidableEq

/-- Buffered delivery uses the existing preparation-before-acknowledgment
operation, after independently checking the captured source context. -/
def deliver [DecidableEq Stored] [DecidableEq Output] (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) : DeliveryReply Stored ×
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  if compatible state.context then
    let observed := SharedOccurrenceOwnership.advance state.delivery client output
    (.observed observed.1, {state with delivery := observed.2})
  else (.contextRefused, state)

def returned (notice : Notice Borrowed Stored Effect Handoff) : List Borrowed :=
  match notice with
  | .returned value => [value]
  | _ => []

def admitted (notice : Notice Borrowed Stored Effect Handoff) : List Stored :=
  match notice with
  | .admitted _ value => [value]
  | _ => []

/-- The transition debit for `driverStep`: emissions and administrative driver
progress each cost one; admission, refusal and completion inspection cost zero.
This projection does not assign a cost to arbitrary producer callbacks. -/
def driverTicks (notice : Notice Borrowed Stored Effect Handoff) : Nat :=
  match notice with
  | .progress | .returned _ => 1
  | _ => 0

theorem driverTicks_le_one (notice : Notice Borrowed Stored Effect Handoff) :
    driverTicks notice ≤ 1 := by
  cases notice <;> simp [driverTicks]

def acceptedCount
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) : Nat :=
  (state.execution.map (fun execution => execution.accepted)).getD 0

theorem run_split
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    run step capture capacity compatible (first + second) state =
      (let earlier := run step capture capacity compatible first state
       let later := run step capture capacity compatible second earlier.2
       (earlier.1 ++ later.1, later.2)) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih => simp [Nat.succ_add, run, ih]

theorem full_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (active : execution.mode = .active) (demanded : hasConsumers state.delivery.log = true)
    (full : state.delivery.log.limit ≤ state.delivery.log.rows.length) :
    pump step capture capacity compatible state = (.backpressure, state) := by
  simp [pump, attached, allowed, openLog, active, demanded, Nat.not_lt.mpr full]

theorem no_demand_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (active : execution.mode = .active) (undemanded : hasConsumers state.delivery.log = false) :
    pump step capture capacity compatible state = (.noConsumers, state) := by
  simp [pump, attached, allowed, openLog, active, undemanded]

theorem context_refusal_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) (refused : compatible state.context = false) :
    pump step capture capacity compatible state = (.contextRefused, state) := by
  simp [pump, attached, refused]

theorem capture_refusal_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (room : state.delivery.log.rows.length < state.delivery.log.limit)
    (demanded : hasConsumers state.delivery.log = true)
    (active : execution.mode = .active) (staged : execution.pending = some value)
    (refused : capture value = none) :
    pump step capture capacity compatible state = (.captureRefused, state) := by
  simp [pump, attached, allowed, openLog, room, demanded, active, staged, admit, refused]

theorem admission_refusal_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) (stored : Stored)
    (attached : state.execution = some execution) (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (room : state.delivery.log.rows.length < state.delivery.log.limit)
    (demanded : hasConsumers state.delivery.log = true)
    (active : execution.mode = .active) (staged : execution.pending = some value)
    (captured : capture value = some stored) (refused : capacity stored = false) :
    pump step capture capacity compatible state = (.admissionRefused, state) := by
  simp [pump, attached, allowed, openLog, room, demanded, active, staged, admit, captured, refused]

theorem pending_excludes_producer_step
    (left right : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) (staged : execution.pending = some value) :
    pump left capture capacity compatible state = pump right capture capacity compatible state := by
  simp only [pump, attached]
  split <;> try rfl
  split <;> try rfl
  cases execution.mode <;> simp [staged]

theorem buffered_context_refusal_preserves_complete_residual [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (refused : compatible state.context = false) :
    deliver compatible state client output = (.contextRefused, state) := by
  simp [deliver, refused]

theorem delivery_preserves_complete_execution [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) :
    (deliver compatible state client output).2.execution = state.execution := by
  unfold deliver
  split <;> rfl

theorem delivery_preserves_other_consumer [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients) (output : Output) (distinct : other ≠ client) :
    SharedOccurrenceLog.peek (deliver compatible state client output).2.delivery.log other =
      SharedOccurrenceLog.peek state.delivery.log other := by
  unfold deliver
  split
  · exact SharedOccurrenceLog.pull_preserves_other state.delivery.log client other distinct
  · rfl

/-- Distinct consumers preserve both replies, every caller root, the captured
context and the complete producer residual when their deliveries are swapped.
The producer is not stepped. Native publication still needs synchronization. -/
theorem deliver_commute [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (left right : Fin clients) (leftOutput rightOutput : Output) (distinct : left ≠ right) :
    (let first := deliver compatible state left leftOutput
     let second := deliver compatible first.2 right rightOutput
     (first.1, second.1, second.2)) =
      (let second := deliver compatible state right rightOutput
       let first := deliver compatible second.2 left leftOutput
       (first.1, second.1, first.2)) := by
  by_cases allowed : compatible state.context = true
  · simp only [deliver, allowed, ↓reduceIte]
    exact congrArg
      (fun result : SharedOccurrenceLog.Reply Stored × SharedOccurrenceLog.Reply Stored ×
          SharedOccurrenceOwnership.Configuration Stored Output clients =>
        (DeliveryReply.observed result.1, DeliveryReply.observed result.2.1,
          {state with delivery := result.2.2}))
      (SharedOccurrenceOwnership.advance_commute state.delivery left right
        leftOutput rightOutput distinct)
  · simp [deliver, allowed]

theorem detach_preserves_delivery
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (detach state).1 = state.execution ∧ (detach state).2.delivery = state.delivery ∧
      (detach state).2.context = state.context := ⟨rfl, rfl, rfl⟩

theorem detached_excludes_producer_step
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    pump step capture capacity compatible (detach state).2 = (.detached, (detach state).2) := rfl

private theorem stage_rows
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    (stage state execution outcome).2.delivery.log.rows =
      state.delivery.log.rows ++ admitted (stage state execution outcome).1 := by
  cases outcome <;> simp [stage, admitted, SharedOccurrenceLog.complete]

private theorem admit_rows (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    (admit capture capacity state execution value).2.delivery.log.rows =
      state.delivery.log.rows ++ admitted (admit capture capacity state execution value).1 := by
  unfold admit
  cases captured : capture value with
  | none => simp [admitted]
  | some stored =>
      simp only
      split
      · by_cases closed : state.delivery.log.completed = true
        · simp [SharedOccurrenceLog.append, closed, admitted]
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [SharedOccurrenceLog.append, closed, room, admitted]
      · simp [admitted]

/-- Every stored row is introduced by one successful actual log append. -/
theorem pump_rows
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pump step capture capacity compatible state).2.delivery.log.rows =
      state.delivery.log.rows ++ admitted (pump step capture capacity compatible state).1 := by
  unfold pump
  cases state.execution with
  | none => simp [admitted]
  | some execution =>
      simp only
      split
      · simp [admitted]
      · split
        · simp [admitted]
        · cases execution.mode with
          | active =>
              simp only
              split
              · simp [admitted]
              · split
                · cases execution.pending with
                  | none => exact stage_rows state execution (step execution.producer)
                  | some value => exact admit_rows capture capacity state execution value
                · simp [admitted]
          | effect request => simp [admitted]
          | handoff request => simp [admitted]
          | interrupted => simp [admitted]

theorem run_rows
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (run step capture capacity compatible ticks state).2.delivery.log.rows =
      state.delivery.log.rows ++
        (run step capture capacity compatible ticks state).1.flatMap admitted := by
  induction ticks generalizing state with
  | zero => simp [run]
  | succ ticks ih =>
      simp only [run]
      rw [ih, pump_rows]
      simp [List.append_assoc]

private theorem stage_conservation (borrowedView : Borrowed → Observation)
    (storedView : Stored → Observation)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) (empty : execution.pending = none) :
    (pending state).toList.map borrowedView ++
        (returned (stage state execution outcome).1).map borrowedView =
      (admitted (stage state execution outcome).1).map storedView ++
        (pending (stage state execution outcome).2).toList.map borrowedView := by
  cases outcome <;> simp [stage, returned, admitted, pending, attached, empty]

private theorem admit_conservation (borrowedView : Borrowed → Observation)
    (storedView : Stored → Observation)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (captureSound : ∀ value stored, capture value = some stored →
      storedView stored = borrowedView value)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) (staged : execution.pending = some value) :
    (pending state).toList.map borrowedView ++
        (returned (admit capture capacity state execution value).1).map borrowedView =
      (admitted (admit capture capacity state execution value).1).map storedView ++
        (pending (admit capture capacity state execution value).2).toList.map borrowedView := by
  unfold admit
  cases captured : capture value with
  | none => simp [returned, admitted, pending, attached, staged]
  | some stored =>
      have same := captureSound value stored captured
      simp only
      split
      · by_cases closed : state.delivery.log.completed = true
        · simp [SharedOccurrenceLog.append, closed, returned, admitted]
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [SharedOccurrenceLog.append, closed, room, returned, admitted, pending,
              attached, staged, same]
      · simp [returned, admitted, pending, attached, staged]

/-- A primitive capture observation law licenses a real conservation equation:
new producer returns are either admitted, in order, or retained as pending. -/
theorem pump_conservation (borrowedView : Borrowed → Observation)
    (storedView : Stored → Observation)
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (captureSound : ∀ value stored, capture value = some stored →
      storedView stored = borrowedView value)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pending state).toList.map borrowedView ++
        (returned (pump step capture capacity compatible state).1).map borrowedView =
      (admitted (pump step capture capacity compatible state).1).map storedView ++
        (pending (pump step capture capacity compatible state).2).toList.map borrowedView := by
  unfold pump
  cases attached : state.execution with
  | none => simp [returned, admitted]
  | some execution =>
      simp only
      split
      · simp [returned, admitted]
      · split
        · simp [returned, admitted]
        · cases execution.mode with
          | active =>
              simp only
              split
              · simp [returned, admitted]
              · split
                · cases staged : execution.pending with
                  | none =>
                      exact stage_conservation borrowedView storedView state execution
                        (step execution.producer) attached staged
                  | some value =>
                      exact admit_conservation borrowedView storedView capture capacity
                        captureSound state execution value attached staged
                · simp [returned, admitted]
          | effect request => simp [returned, admitted]
          | handoff request => simp [returned, admitted]
          | interrupted => simp [returned, admitted]

/-- Complete ordered conservation across any finite sequence of retries,
administrative steps, pauses and barriers. Equal observations keep multiplicity. -/
theorem run_conservation (borrowedView : Borrowed → Observation)
    (storedView : Stored → Observation)
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (captureSound : ∀ value stored, capture value = some stored →
      storedView stored = borrowedView value)
    (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pending state).toList.map borrowedView ++
        ((run step capture capacity compatible ticks state).1.flatMap returned).map borrowedView =
      ((run step capture capacity compatible ticks state).1.flatMap admitted).map storedView ++
        (pending (run step capture capacity compatible ticks state).2).toList.map borrowedView := by
  induction ticks generalizing state with
  | zero => simp [run]
  | succ ticks ih =>
      simp only [run, List.flatMap_cons, List.map_append]
      rw [← List.append_assoc, pump_conservation borrowedView storedView step capture capacity
        compatible captureSound state, List.append_assoc, ih]
      simp [List.append_assoc]

def ProducerOutcome.next : ProducerOutcome Producer Borrowed Effect Handoff → Producer
  | .progress next | .returned _ next | .yielded next | .effect _ next
      | .handoff _ next | .interrupted next | .completed next => next

def ProducerOutcome.returns : ProducerOutcome Producer Borrowed Effect Handoff → List Borrowed
  | .returned value _ => [value]
  | _ => []

/-- The source trace follows actual producer transitions, independently of
capture, row storage, cursor delivery or scheduler microstep accounting. -/
inductive ProducerPath (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff) :
    Producer → List Borrowed → Producer → Prop where
  | refl (state : Producer) : ProducerPath step state [] state
  | next {source : Producer} {outcome : ProducerOutcome Producer Borrowed Effect Handoff}
      {rest : List Borrowed} {target : Producer}
      (transition : step source = outcome)
      (tail : ProducerPath step outcome.next rest target) :
      ProducerPath step source (outcome.returns ++ rest) target

theorem ProducerPath.append
    {step : Producer → ProducerOutcome Producer Borrowed Effect Handoff}
    {source middle target : Producer} {earlier later : List Borrowed}
    (first : ProducerPath step source earlier middle)
    (second : ProducerPath step middle later target) :
    ProducerPath step source (earlier ++ later) target := by
  induction first with
  | refl => simpa using second
  | next transition tail ih =>
      simpa [List.append_assoc] using ProducerPath.next transition (ih second)

private theorem stage_producer_path
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) :
    ∃ next, (stage state execution (step execution.producer)).2.execution = some next ∧
      ProducerPath step execution.producer
        (returned (stage state execution (step execution.producer)).1) next.producer := by
  cases transition : step execution.producer <;>
    refine ⟨_, rfl, ?_⟩ <;>
    simpa [stage, returned, ProducerOutcome.returns, ProducerOutcome.next] using
      ProducerPath.next transition (ProducerPath.refl _)

private theorem admit_retains_producer
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) :
    ∃ next, (admit capture capacity state execution value).2.execution = some next ∧
      next.producer = execution.producer ∧
      returned (admit capture capacity state execution value).1 = [] ∧
      driverTicks (admit capture capacity state execution value).1 = 0 := by
  unfold admit
  cases capture value with
  | none => exact ⟨execution, attached, rfl, rfl, rfl⟩
  | some stored =>
      simp only
      split
      · by_cases closed : state.delivery.log.completed = true
        · simp only [SharedOccurrenceLog.append, closed, if_pos]
          exact ⟨execution, attached, rfl, rfl, rfl⟩
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit
          · simp only [SharedOccurrenceLog.append, closed, room, if_pos]
            exact ⟨_, rfl, rfl, rfl, rfl⟩
          · simp only [SharedOccurrenceLog.append, closed, room]
            exact ⟨execution, attached, rfl, rfl, rfl⟩
      · exact ⟨execution, attached, rfl, rfl, rfl⟩

private theorem admit_producer_path
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) :
    ∃ next, (admit capture capacity state execution value).2.execution = some next ∧
      ProducerPath step execution.producer
        (returned (admit capture capacity state execution value).1) next.producer := by
  obtain ⟨next, nextAttached, producer, events, _⟩ :=
    admit_retains_producer capture capacity state execution value attached
  exact ⟨next, nextAttached, by rw [producer, events]; exact ProducerPath.refl _⟩

theorem pump_producer_path
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) :
    ∃ next, (pump step capture capacity compatible state).2.execution = some next ∧
      ProducerPath step execution.producer
        (returned (pump step capture capacity compatible state).1) next.producer := by
  unfold pump
  rw [attached]
  simp only
  split
  · exact ⟨execution, attached, ProducerPath.refl _⟩
  · split
    · exact ⟨execution, attached, ProducerPath.refl _⟩
    · cases execution.mode with
      | active =>
          simp only
          split
          · exact ⟨execution, attached, ProducerPath.refl _⟩
          · split
            · cases execution.pending with
              | none => exact stage_producer_path step state execution
              | some value => exact admit_producer_path step capture capacity state execution value attached
            · exact ⟨execution, attached, ProducerPath.refl _⟩
      | effect request => exact ⟨execution, attached, ProducerPath.refl _⟩
      | handoff request => exact ⟨execution, attached, ProducerPath.refl _⟩
      | interrupted => exact ⟨execution, attached, ProducerPath.refl _⟩

/-- Every staged return comes from an actual producer transition, and the
entire final producer residual is the endpoint of that ordered source path. -/
theorem run_producer_path
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) :
    ∃ next, (run step capture capacity compatible ticks state).2.execution = some next ∧
      ProducerPath step execution.producer
        ((run step capture capacity compatible ticks state).1.flatMap returned) next.producer := by
  induction ticks generalizing state execution with
  | zero => exact ⟨execution, attached, ProducerPath.refl _⟩
  | succ ticks ih =>
      obtain ⟨middle, middleAttached, first⟩ :=
        pump_producer_path step capture capacity compatible state execution attached
      obtain ⟨next, nextAttached, rest⟩ := ih _ middle middleAttached
      exact ⟨next, nextAttached, by simpa only [run, List.flatMap_cons] using first.append rest⟩

/-- Adapts actual explicit-frame transitions to the selected event stream.
This observer treats events as return occurrences; it grants no effectful
sharing license for a native evaluator. The final value remains in the residual. -/
def driverStep {Value Event : Type} (state : OwnedPullDriver.State Value Event) :
    ProducerOutcome (OwnedPullDriver.State Value Event) Event Empty Empty :=
  match OwnedPullDriver.transition state with
  | none => .completed state
  | some ([], next) => .progress next
  | some (event :: _, next) => .returned event next

theorem driver_step_path {Value Event : Type} (state : OwnedPullDriver.State Value Event) :
    ∃ count, OwnedPullDriver.Path state (driverStep state).returns count (driverStep state).next := by
  rcases state with ⟨work, frames⟩
  cases work with
  | done value =>
      cases frames with
      | nil => exact ⟨0, OwnedPullDriver.Path.refl⟩
      | cons resume rest =>
          exact ⟨1, by simpa [driverStep, OwnedPullDriver.transition,
            ProducerOutcome.returns, ProducerOutcome.next] using
              OwnedPullDriver.Path.next (OwnedPullDriver.Step.resume
                (value := value) (resume := resume) (rest := rest)) OwnedPullDriver.Path.refl⟩
  | emit event next =>
      exact ⟨1, by simpa [driverStep, OwnedPullDriver.transition,
        ProducerOutcome.returns, ProducerOutcome.next] using
          OwnedPullDriver.Path.next (OwnedPullDriver.Step.emit
            (event := event) (next := next) (frames := frames)) OwnedPullDriver.Path.refl⟩
  | child work resume =>
      exact ⟨1, by simpa [driverStep, OwnedPullDriver.transition,
        ProducerOutcome.returns, ProducerOutcome.next] using
          OwnedPullDriver.Path.next (OwnedPullDriver.Step.child
            (work := work) (resume := resume) (frames := frames)) OwnedPullDriver.Path.refl⟩

/-- The producer trace of the composition is an actual path of the existing
owned driver, retaining its complete continuation stack and final work. -/
theorem driver_producer_path {Value Event : Type}
    {source target : OwnedPullDriver.State Value Event} {events : List Event}
    (path : ProducerPath driverStep source events target) :
    ∃ count, OwnedPullDriver.Path source events count target := by
  induction path with
  | refl => exact ⟨0, OwnedPullDriver.Path.refl⟩
  | @next source outcome rest target transition tail ih =>
      obtain ⟨firstCount, first⟩ := driver_step_path source
      rw [transition] at first
      obtain ⟨restCount, rest⟩ := ih
      exact ⟨firstCount + restCount, first.append rest⟩

theorem completed_driver_preserves_recursive_meaning {Value Event : Type}
    {work : OwnedPullDriver.Program Value Event} {events : List Event} {value : Value}
    (path : ProducerPath driverStep ⟨work, []⟩ events ⟨.done value, []⟩) :
    OwnedPullDriver.Runs work events value := by
  obtain ⟨count, actual⟩ := driver_producer_path path
  exact OwnedPullDriver.runs_of_path actual

private theorem stage_driver_path {Value Event : Type}
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients)
    (execution : Execution (OwnedPullDriver.State Value Event) Event Empty Empty) :
    ∃ next, (stage state execution (driverStep execution.producer)).2.execution = some next ∧
      OwnedPullDriver.Path execution.producer
        (returned (stage state execution (driverStep execution.producer)).1)
        (driverTicks (stage state execution (driverStep execution.producer)).1) next.producer := by
  rcases execution with ⟨⟨work, frames⟩, pending, accepted, mode⟩
  cases work with
  | done value =>
      cases frames with
      | nil => exact ⟨_, rfl, OwnedPullDriver.Path.refl⟩
      | cons resume rest =>
          refine ⟨_, rfl, ?_⟩
          simpa [stage, driverStep, OwnedPullDriver.transition, returned, driverTicks] using
            OwnedPullDriver.Path.next (OwnedPullDriver.Step.resume
              (value := value) (resume := resume) (rest := rest)) OwnedPullDriver.Path.refl
  | emit event next =>
      refine ⟨_, rfl, ?_⟩
      simpa [stage, driverStep, OwnedPullDriver.transition, returned, driverTicks] using
        OwnedPullDriver.Path.next (OwnedPullDriver.Step.emit
          (event := event) (next := next) (frames := frames)) OwnedPullDriver.Path.refl
  | child work resume =>
      refine ⟨_, rfl, ?_⟩
      simpa [stage, driverStep, OwnedPullDriver.transition, returned, driverTicks] using
        OwnedPullDriver.Path.next (OwnedPullDriver.Step.child
          (work := work) (resume := resume) (frames := frames)) OwnedPullDriver.Path.refl

/-- A composition step either performs exactly one owned-driver transition or
retains the entire producer. Successful admission is also a zero-driver step. -/
theorem pump_driver_path {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients)
    (execution : Execution (OwnedPullDriver.State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next, (pump driverStep capture capacity compatible state).2.execution = some next ∧
      OwnedPullDriver.Path execution.producer
        (returned (pump driverStep capture capacity compatible state).1)
        (driverTicks (pump driverStep capture capacity compatible state).1) next.producer := by
  unfold pump
  rw [attached]
  simp only
  split
  · exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
  · split
    · exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
    · cases execution.mode with
      | active =>
          simp only
          split
          · exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
          · split
            · cases execution.pending with
              | none => exact stage_driver_path state execution
              | some value =>
                  obtain ⟨next, nextAttached, producer, events, ticks⟩ :=
                    admit_retains_producer capture capacity state execution value attached
                  exact ⟨next, nextAttached, by
                    rw [producer, events, ticks]
                    exact OwnedPullDriver.Path.refl⟩
            · exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
      | effect request => exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
      | handoff request => exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
      | interrupted => exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩

/-- The recorded debit counts the actual producer path, retaining duplicate
events and all caller frames across admission and retry boundaries. -/
theorem run_driver_path {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients)
    (execution : Execution (OwnedPullDriver.State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next, (run driverStep capture capacity compatible ticks state).2.execution = some next ∧
      OwnedPullDriver.Path execution.producer
        ((run driverStep capture capacity compatible ticks state).1.flatMap returned)
        ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum
        next.producer := by
  induction ticks generalizing state execution with
  | zero => exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
  | succ ticks ih =>
      obtain ⟨middle, middleAttached, first⟩ :=
        pump_driver_path capture capacity compatible state execution attached
      obtain ⟨next, nextAttached, rest⟩ := ih _ middle middleAttached
      exact ⟨next, nextAttached, by
        simpa only [run, List.flatMap_cons, List.map_cons, List.sum_cons] using first.append rest⟩

/-- The independently defined unrecorded runner reaches exactly the retained
producer with this debit. Composition microsteps and accepted-return counts
are separate metrics; this law does not bound capture or scheduler work. -/
theorem run_driver_debit {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients)
    (execution : Execution (OwnedPullDriver.State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next, (run driverStep capture capacity compatible ticks state).2.execution = some next ∧
      let debit := ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum
      MachineCore.runSlice (OwnedPullDriver.machineCore Value Event) debit execution.producer =
        (next.producer, debit) := by
  obtain ⟨next, nextAttached, path⟩ :=
    run_driver_path capture capacity compatible ticks state execution attached
  exact ⟨next, nextAttached, path.runSlice⟩

theorem run_driver_ticks_le {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients) :
    ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum ≤ ticks := by
  induction ticks generalizing state with
  | zero => simp [run]
  | succ ticks ih =>
      simp only [run, List.map_cons, List.sum_cons]
      have first := driverTicks_le_one (pump driverStep capture capacity compatible state).1
      have rest := ih (pump driverStep capture capacity compatible state).2
      omega

theorem run_driver_ticks_split {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (first second : Nat)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients) :
    ((run driverStep capture capacity compatible (first + second) state).1.map driverTicks).sum =
      ((run driverStep capture capacity compatible first state).1.map driverTicks).sum +
        ((run driverStep capture capacity compatible second
          (run driverStep capture capacity compatible first state).2).1.map driverTicks).sum := by
  rw [run_split]
  simp only [List.map_append, List.sum_append]

private theorem stage_metadata
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    (stage state execution outcome).2.context = state.context ∧
      (stage state execution outcome).2.delivery.log.base = state.delivery.log.base ∧
      (stage state execution outcome).2.delivery.log.positions = state.delivery.log.positions ∧
      (stage state execution outcome).2.delivery.published = state.delivery.published := by
  cases outcome <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem admit_metadata (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    (admit capture capacity state execution value).2.context = state.context ∧
      (admit capture capacity state execution value).2.delivery.log.base = state.delivery.log.base ∧
      (admit capture capacity state execution value).2.delivery.log.positions = state.delivery.log.positions ∧
      (admit capture capacity state execution value).2.delivery.published = state.delivery.published := by
  unfold admit
  cases capture value with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some stored =>
      simp only
      split
      · by_cases closed : state.delivery.log.completed = true
        · simp only [SharedOccurrenceLog.append, closed, if_pos]
          simp
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [SharedOccurrenceLog.append, closed, room]
      · exact ⟨rfl, rfl, rfl, rfl⟩

theorem pump_preserves_context_cursors_publications
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pump step capture capacity compatible state).2.context = state.context ∧
      (pump step capture capacity compatible state).2.delivery.log.base = state.delivery.log.base ∧
      (pump step capture capacity compatible state).2.delivery.log.positions = state.delivery.log.positions ∧
      (pump step capture capacity compatible state).2.delivery.published = state.delivery.published := by
  unfold pump
  cases state.execution with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some execution =>
      simp only
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · cases execution.mode with
          | active =>
              simp only
              split
              · exact ⟨rfl, rfl, rfl, rfl⟩
              · split
                · cases execution.pending with
                  | none => exact stage_metadata state execution (step execution.producer)
                  | some value => exact admit_metadata capture capacity state execution value
                · exact ⟨rfl, rfl, rfl, rfl⟩
          | effect request => exact ⟨rfl, rfl, rfl, rfl⟩
          | handoff request => exact ⟨rfl, rfl, rfl, rfl⟩
          | interrupted => exact ⟨rfl, rfl, rfl, rfl⟩

theorem run_preserves_context_cursors_publications
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (run step capture capacity compatible ticks state).2.context = state.context ∧
      (run step capture capacity compatible ticks state).2.delivery.log.base = state.delivery.log.base ∧
      (run step capture capacity compatible ticks state).2.delivery.log.positions = state.delivery.log.positions ∧
      (run step capture capacity compatible ticks state).2.delivery.published = state.delivery.published := by
  induction ticks generalizing state with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ ticks ih =>
      have rest := ih (pump step capture capacity compatible state).2
      have first := pump_preserves_context_cursors_publications step capture capacity compatible state
      exact ⟨rest.1.trans first.1, rest.2.1.trans first.2.1,
        rest.2.2.1.trans first.2.2.1, rest.2.2.2.trans first.2.2.2⟩

/-- Producer progress retains every already buffered occurrence. An empty
buffer is different: appending a row may wake a waiting consumer. -/
theorem pump_preserves_buffered_answer
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (position : Nat) (value : Stored)
    (answer : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    SharedOccurrenceLog.peek (pump step capture capacity compatible state).2.delivery.log client =
      .answer position value := by
  have metadata := pump_preserves_context_cursors_publications step capture capacity compatible state
  exact SharedOccurrenceLog.extension_preserves_prior_answer _ _ client _ position value
    metadata.2.1 (congrFun metadata.2.2.1 client)
    (pump_rows step capture capacity compatible state) answer

private def bufferedUpdate [DecidableEq Stored] [DecidableEq Output]
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored) :
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  {state with delivery :=
    ⟨SharedOccurrenceLog.setPosition state.delivery.log client (some (position + 1)),
      OwnedLifecycle.publish state.delivery.published output [value]⟩}

private theorem active_consumer_has_demand (log : SharedOccurrenceLog.State Stored clients)
    (client : Fin clients) (position : Nat) (active : log.positions client = some position) :
    hasConsumers log = true := by
  apply List.any_eq_true.mpr
  exact ⟨client, List.mem_finRange client, by simp [active]⟩

private theorem stage_bufferedUpdate [DecidableEq Stored] [DecidableEq Output]
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored) :
    stage (bufferedUpdate state client output position value) execution outcome =
      ((stage state execution outcome).1,
        bufferedUpdate (stage state execution outcome).2 client output position value) := by
  cases outcome <;> rfl

private theorem admit_bufferedUpdate [DecidableEq Stored] [DecidableEq Output]
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (pendingValue : Borrowed)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored) :
    admit capture capacity (bufferedUpdate state client output position value) execution pendingValue =
      ((admit capture capacity state execution pendingValue).1,
        bufferedUpdate (admit capture capacity state execution pendingValue).2
          client output position value) := by
  unfold admit
  cases captured : capture pendingValue with
  | none => rfl
  | some stored =>
      simp only
      split
      · by_cases completed : state.delivery.log.completed = true
        · simp [bufferedUpdate, SharedOccurrenceLog.append, SharedOccurrenceLog.setPosition,
            completed]
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [bufferedUpdate, SharedOccurrenceLog.append, SharedOccurrenceLog.setPosition,
              SharedOccurrenceLog.pastEnd, completed, room]
      · rfl

private theorem pump_bufferedUpdate [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (active : state.delivery.log.positions client = some position) :
    pump step capture capacity compatible (bufferedUpdate state client output position value) =
      ((pump step capture capacity compatible state).1,
        bufferedUpdate (pump step capture capacity compatible state).2
          client output position value) := by
  have before := active_consumer_has_demand state.delivery.log client position active
  have after : hasConsumers
      (bufferedUpdate state client output position value).delivery.log = true :=
    active_consumer_has_demand _ client (position + 1) (by simp [bufferedUpdate])
  unfold pump
  simp only [show (bufferedUpdate state client output position value).execution =
      state.execution from rfl,
    show (bufferedUpdate state client output position value).context = state.context from rfl,
    show (bufferedUpdate state client output position value).delivery.log.completed =
      state.delivery.log.completed from rfl,
    show (bufferedUpdate state client output position value).delivery.log.rows =
      state.delivery.log.rows from rfl,
    show (bufferedUpdate state client output position value).delivery.log.limit =
      state.delivery.log.limit from rfl,
    before, after, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases execution : state.execution with
  | none => rfl
  | some producer =>
      simp only
      by_cases current : (!compatible state.context) = true
      · simp only [current, ↓reduceIte]
      · simp only [current, Bool.false_eq_true, ↓reduceIte]
        by_cases completed : state.delivery.log.completed = true
        · simp only [completed, ↓reduceIte]
        · simp only [completed, Bool.false_eq_true, ↓reduceIte]
          cases mode : producer.mode with
          | active =>
              simp only
              by_cases room : state.delivery.log.rows.length < state.delivery.log.limit
              · simp only [room, ↓reduceIte]
                cases pending : producer.pending with
                | none =>
                    exact stage_bufferedUpdate state producer (step producer.producer)
                      client output position value
                | some pendingValue =>
                    exact admit_bufferedUpdate capture capacity state producer
                      pendingValue client output position value
              · simp only [room, ↓reduceIte]
          | effect request => rfl
          | handoff request => rfl
          | interrupted => rfl

/-- A producer microstep commutes with delivery of an existing buffered
occurrence. Both replies, the exact producer residual and every published
caller root agree. This is an atomic-operation law; native interleaved memory
access, concurrent capture and source revalidation remain obligations. -/
theorem pump_deliver_buffered_commute [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (answer : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    (let produced := pump step capture capacity compatible state
     let consumed := deliver compatible produced.2 client output
     (produced.1, consumed.1, consumed.2)) =
      (let consumed := deliver compatible state client output
       let produced := pump step capture capacity compatible consumed.2
       (produced.1, consumed.1, produced.2)) := by
  have metadata := pump_preserves_context_cursors_publications step capture capacity compatible state
  by_cases current : compatible state.context = true
  · have buffered := pump_preserves_buffered_answer step capture capacity compatible
      state client position value answer
    have active := (SharedOccurrenceLog.answer_within state.delivery.log client position value answer).1
    have commute := pump_bufferedUpdate step capture capacity compatible state
      client output position value active
    simp only [deliver, metadata.1, current, ↓reduceIte,
      SharedOccurrenceOwnership.advance_answer _ client output position value buffered,
      SharedOccurrenceOwnership.advance_answer _ client output position value answer]
    change _ = ((pump step capture capacity compatible
      (bufferedUpdate state client output position value)).1,
      DeliveryReply.observed (.answer position value),
      (pump step capture capacity compatible (bufferedUpdate state client output position value)).2)
    rw [commute]
    simp only [bufferedUpdate, metadata.1]
  · simp [deliver, metadata.1, current]

/-- Any finite producer slice can overlap one already available delivery.
Ordered producer notices and the complete owned state agree, so every debit
derived from those notices agrees as well. No waiting read is reordered. -/
theorem run_deliver_buffered_commute [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (answer : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    (let produced := run step capture capacity compatible ticks state
     let consumed := deliver compatible produced.2 client output
     (produced.1, consumed.1, consumed.2)) =
      (let consumed := deliver compatible state client output
       let produced := run step capture capacity compatible ticks consumed.2
       (produced.1, consumed.1, produced.2)) := by
  induction ticks generalizing state with
  | zero => rfl
  | succ ticks ih =>
      have nextAnswer := pump_preserves_buffered_answer step capture capacity compatible
        state client position value answer
      have first := pump_deliver_buffered_commute step capture capacity compatible
        state client output position value answer
      have rest := ih (pump step capture capacity compatible state).2 nextAnswer
      have notice := congrArg Prod.fst first
      have delivery := congrArg (fun result => result.2.1) first
      have residual := congrArg (fun result => result.2.2) first
      simp only [run]
      change _ = _
      simp only at notice delivery residual rest
      rw [← notice, ← residual]
      have extended := congrArg
        (fun result : List (Notice Borrowed Stored Effect Handoff) ×
            DeliveryReply Stored ×
            Configuration Producer Borrowed Stored Context Output Effect Handoff clients =>
          ((pump step capture capacity compatible state).1 :: result.1, result.2)) rest
      simpa only [delivery] using extended

/-- Each consumer of a fresh cohort sees the same admitted occurrence sequence
at its own position. The producer path and capture conservation qualify that
sequence separately; cursor sharing is not substituted for independent choice. -/
theorem fresh_consumer_observes_admitted_order [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks budget : Nat) (producer : Producer)
    (context : Context) (limit : Nat) (client : Fin clients) (output : Output) :
    let start := initial (Borrowed := Borrowed) (Stored := Stored) (Output := Output)
      (Effect := Effect) (Handoff := Handoff) (clients := clients) producer context limit
    let result := run step capture capacity compatible ticks start
    (SharedOccurrenceOwnership.observe budget result.2.delivery client output).1 =
      (SharedOccurrenceLog.numberFrom 0 (result.1.flatMap admitted)).take budget := by
  dsimp only
  let start := initial (Borrowed := Borrowed) (Stored := Stored) (Output := Output)
    (Effect := Effect) (Handoff := Handoff) (clients := clients) producer context limit
  let result := run step capture capacity compatible ticks start
  have same := run_preserves_context_cursors_publications step capture capacity compatible ticks start
  have cursor : result.2.delivery.log.positions client = some 0 := by
    rw [same.2.2.1]
    rfl
  have base : result.2.delivery.log.base = 0 := same.2.1
  have rows : result.2.delivery.log.rows = result.1.flatMap admitted := by
    simpa only [start, result, initial, SharedOccurrenceLog.initial, List.nil_append] using
      run_rows step capture capacity compatible ticks start
  rw [(SharedOccurrenceOwnership.observe_log budget result.2.delivery client output).1]
  rw [(SharedOccurrenceLog.drain_spec budget result.2.delivery.log client 0 cursor (by omega)).1]
  simp [base, rows, result, start]

private theorem stage_log_valid
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (stage state execution outcome).2.delivery.log := by
  cases outcome <;> exact valid

private theorem admit_log_valid (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (admit capture capacity state execution value).2.delivery.log := by
  unfold admit
  cases capture value with
  | none => exact valid
  | some stored =>
      simp only
      split
      · cases appended : SharedOccurrenceLog.append state.delivery.log stored with
        | mk admission log =>
            have nextValid := SharedOccurrenceLog.append_valid state.delivery.log stored valid
            rw [appended] at nextValid
            cases admission with
            | accepted => exact nextValid
            | backpressure => exact valid
            | completed => exact valid
      · exact valid

theorem pump_log_valid
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (pump step capture capacity compatible state).2.delivery.log := by
  unfold pump
  cases state.execution with
  | none => exact valid
  | some execution =>
      simp only
      split
      · exact valid
      · split
        · exact valid
        · cases execution.mode with
          | active =>
              simp only
              split
              · exact valid
              · split
                · cases execution.pending with
                  | none => exact stage_log_valid state execution (step execution.producer) valid
                  | some value => exact admit_log_valid capture capacity state execution value valid
                · exact valid
          | effect request => exact valid
          | handoff request => exact valid
          | interrupted => exact valid

theorem run_log_valid
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (run step capture capacity compatible ticks state).2.delivery.log := by
  induction ticks generalizing state with
  | zero => exact valid
  | succ ticks ih =>
      exact ih _ (pump_log_valid step capture capacity compatible state valid)

theorem guarded_delivery_wellFormed [DecidableEq Stored] [DecidableEq Output]
    {Value : Type} (heap : ResourceOwnership.Heap Stored Value) (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output)
    (valid : SharedOccurrenceOwnership.WellFormed heap state.delivery) :
    SharedOccurrenceOwnership.WellFormed heap (deliver compatible state client output).2.delivery := by
  unfold deliver
  split
  · exact SharedOccurrenceOwnership.advance_wellFormed heap state.delivery client output valid
  · exact valid

/-- Successful log admission advances the accepted-return counter exactly
once. Capture retries and all refusal/barrier cases leave it unchanged. -/
theorem pump_accepted_count
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    acceptedCount (pump step capture capacity compatible state).2 = acceptedCount state +
      (admitted (pump step capture capacity compatible state).1).length := by
  unfold pump
  cases attached : state.execution with
  | none => simp [admitted]
  | some execution =>
      simp only
      split
      · simp [admitted]
      · split
        · simp [admitted]
        · cases execution.mode with
          | active =>
              simp only
              split
              · simp [admitted]
              · split
                · cases execution.pending with
                  | none =>
                      cases step execution.producer <;>
                        simp [stage, admitted, acceptedCount, attached]
                  | some value =>
                      unfold admit
                      cases captured : capture value with
                      | none => simp [captured, admitted]
                      | some stored =>
                          simp only [captured]
                          split
                          · by_cases closed : state.delivery.log.completed = true
                            · simp [SharedOccurrenceLog.append, closed, admitted]
                            · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
                                simp [SharedOccurrenceLog.append, closed, room, admitted, acceptedCount, attached]
                          · simp [admitted]
                · simp [admitted]
          | effect request => simp [admitted]
          | handoff request => simp [admitted]
          | interrupted => simp [admitted]

theorem run_accepted_count
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    acceptedCount (run step capture capacity compatible ticks state).2 = acceptedCount state +
      ((run step capture capacity compatible ticks state).1.flatMap admitted).length := by
  induction ticks generalizing state with
  | zero => simp [run]
  | succ ticks ih =>
      simp only [run]
      rw [ih, pump_accepted_count]
      simp [Nat.add_assoc]

section ProducerTransport

variable {OtherProducer : Type}

/-- Change only the suspended producer representation. Return occurrences and
retained requests keep their original carriers. -/
def ProducerOutcome.mapProducer (f : Producer → OtherProducer) :
    ProducerOutcome Producer Borrowed Effect Handoff →
      ProducerOutcome OtherProducer Borrowed Effect Handoff
  | .progress next => .progress (f next)
  | .returned value next => .returned value (f next)
  | .yielded next => .yielded (f next)
  | .effect request next => .effect request (f next)
  | .handoff request next => .handoff request (f next)
  | .interrupted next => .interrupted (f next)
  | .completed next => .completed (f next)

def Execution.mapProducer (f : Producer → OtherProducer)
    (execution : Execution Producer Borrowed Effect Handoff) :
    Execution OtherProducer Borrowed Effect Handoff :=
  ⟨f execution.producer, execution.pending, execution.accepted, execution.mode⟩

/-- Pending capture, public cursor positions and published roots are outside
the producer representation. A transport does not reset or re-create them. -/
def mapProducer (f : Producer → OtherProducer)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Configuration OtherProducer Borrowed Stored Context Output Effect Handoff clients :=
  ⟨state.execution.map (Execution.mapProducer f), state.context, state.delivery⟩

private theorem stage_mapProducer (f : Producer → OtherProducer)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    stage (mapProducer f state) (execution.mapProducer f) (outcome.mapProducer f) =
      ((stage state execution outcome).1, mapProducer f (stage state execution outcome).2) := by
  cases outcome <;> simp [stage, mapProducer, Execution.mapProducer, ProducerOutcome.mapProducer]

private theorem admit_mapProducer (f : Producer → OtherProducer)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    admit capture capacity (mapProducer f state) (execution.mapProducer f) value =
      ((admit capture capacity state execution value).1,
        mapProducer f (admit capture capacity state execution value).2) := by
  unfold admit
  cases captured : capture value with
  | none => rfl
  | some stored =>
      simp only [mapProducer]
      split
      · cases SharedOccurrenceLog.append state.delivery.log stored with
        | mk notice log => cases notice <;> rfl
      · rfl

/-- A concrete producer step square lifts to the entire pending/publication
composition. Capture and capacity are checked on the same retained row. -/
theorem pump_mapProducer (f : Producer → OtherProducer)
    (sourceStep : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (targetStep : OtherProducer → ProducerOutcome OtherProducer Borrowed Effect Handoff)
    (stepSquare : ∀ producer, targetStep (f producer) = (sourceStep producer).mapProducer f)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    pump targetStep capture capacity compatible (mapProducer f state) =
      ((pump sourceStep capture capacity compatible state).1,
        mapProducer f (pump sourceStep capture capacity compatible state).2) := by
  rcases state with ⟨attached, context, delivery⟩
  cases attached with
  | none => rfl
  | some execution =>
      rcases execution with ⟨producer, staged, accepted, mode⟩
      simp only [pump, mapProducer, Option.map_some, Execution.mapProducer]
      by_cases denied : (!compatible context) = true
      · simp [denied, Execution.mapProducer]
      · simp only [denied]
        by_cases closed : delivery.log.completed = true
        · simp [closed, Execution.mapProducer]
        · simp only [closed]
          cases mode with
          | active =>
              simp only
              by_cases absent : (!hasConsumers delivery.log) = true
              · simp [absent, Execution.mapProducer]
              · simp only [absent]
                by_cases room : delivery.log.rows.length < delivery.log.limit
                · simp only [room, if_true]
                  cases staged with
                  | none =>
                      simp only
                      rw [stepSquare]
                      exact stage_mapProducer f ⟨some ⟨producer, none, accepted, .active⟩,
                        context, delivery⟩ ⟨producer, none, accepted, .active⟩ (sourceStep producer)
                  | some value =>
                      exact admit_mapProducer f capture capacity
                        ⟨some ⟨producer, some value, accepted, .active⟩, context, delivery⟩
                        ⟨producer, some value, accepted, .active⟩ value
                · simp [room, Execution.mapProducer]
          | effect request => rfl
          | handoff request => rfl
          | interrupted => rfl

/-- Ordered notices, the pending return, accepted cursor, source context,
consumer positions and published roots survive finite run/resume transport. -/
theorem run_mapProducer (f : Producer → OtherProducer)
    (sourceStep : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (targetStep : OtherProducer → ProducerOutcome OtherProducer Borrowed Effect Handoff)
    (stepSquare : ∀ producer, targetStep (f producer) = (sourceStep producer).mapProducer f)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    run targetStep capture capacity compatible ticks (mapProducer f state) =
      ((run sourceStep capture capacity compatible ticks state).1,
        mapProducer f (run sourceStep capture capacity compatible ticks state).2) := by
  induction ticks generalizing state with
  | zero => rfl
  | succ ticks ih =>
      simp only [run, pump_mapProducer f sourceStep targetStep stepSquare]
      rw [ih]

theorem deliver_mapProducer [DecidableEq Stored] [DecidableEq Output]
    (f : Producer → OtherProducer) (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) :
    deliver compatible (mapProducer f state) client output =
      ((deliver compatible state client output).1,
        mapProducer f (deliver compatible state client output).2) := by
  unfold deliver
  simp only [mapProducer]
  split <;> simp_all

end ProducerTransport

/-! ## Shared factors as actual owned producers

The indexed producer and flat producer take different lookup paths. The
existing producer transport carries their proved step square through pending
returns, capture/admission refusal, independent consumers and publication.
-/

namespace FactorTransport

open SharedFactorMachine

variable {Input Value : Type}

def indexedStep : Checked Input Value 1 →
    ProducerOutcome (Checked Input Value 1) (Input × Value) Empty Empty := fun state =>
  match SharedFactor.peek state.val 0 with
  | .answer position value => .returned value (reposition state 0 (some (position + 1)))
  | .paused => .yielded state
  | .completed => .completed state
  | .cancelled | .invalid => .interrupted state

def flatStep : SharedOccurrenceLog.State (Input × Value) 1 →
    ProducerOutcome (SharedOccurrenceLog.State (Input × Value) 1) (Input × Value) Empty Empty :=
  fun state => match SharedOccurrenceLog.peek state 0 with
  | .answer position value =>
      .returned value (SharedOccurrenceLog.setPosition state 0 (some (position + 1)))
  | .paused => .yielded state
  | .completed => .completed state
  | .cancelled | .invalid => .interrupted state

def readback (state : Checked Input Value 1) : SharedOccurrenceLog.State (Input × Value) 1 :=
  SharedFactor.decode state.val

theorem step_readback (state : Checked Input Value 1) :
    flatStep (readback state) = (indexedStep state).mapProducer readback := by
  have same := SharedFactor.peek_decode state.val 0 state.property
  unfold flatStep indexedStep readback
  rw [← same]
  cases SharedFactor.peek state.val 0 <;> rfl

/-- Exact ownership-protocol correspondence, including the pending return
and complete producer residual. No assumption of a step square is exposed:
it is proved from the two actual reader operations above. -/
theorem run_readback {Context Output : Type} {readers : Nat}
    (capture : (Input × Value) → Option (Input × Value))
    (capacity : (Input × Value) → Bool) (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (Checked Input Value 1) (Input × Value) (Input × Value)
      Context Output Empty Empty readers) :
    run flatStep capture capacity compatible ticks (mapProducer readback state) =
      ((run indexedStep capture capacity compatible ticks state).1,
        mapProducer readback (run indexedStep capture capacity compatible ticks state).2) :=
  run_mapProducer readback indexedStep flatStep step_readback capture capacity compatible ticks state

private def sample : Checked Nat Nat 1 :=
  ⟨⟨#[7, 7], ⟨41, 0, 2, true⟩, fun _ => some 0⟩, by constructor <;> decide⟩

private def staged : Configuration (Checked Nat Nat 1) (Nat × Nat) (Nat × Nat)
    Nat Nat Empty Empty 2 :=
  (pump indexedStep some (fun _ => true) (fun _ => true) (initial sample 0 2)).2

theorem refusal_keeps_advanced_reader_and_pending_occurrence :
    staged.execution.map (fun execution => execution.producer.val.positions 0) = some (some 1) ∧
      pending staged = some (41, 7) ∧
      pump indexedStep some (fun _ => false) (fun _ => true) staged =
        (.admissionRefused, staged) := ⟨rfl, rfl, rfl⟩

theorem repeated_refusal_does_not_read_the_suffix_again :
    (run indexedStep some (fun _ => false) (fun _ => true) 20 staged).2 = staged := rfl

end FactorTransport

namespace Controls

abbrev Driver := OwnedPullDriver.State Nat Nat
abbrev Packet := Configuration Driver Nat Nat Nat Nat Empty Empty 2

def captureEvent (value : Nat) : Option Nat := some (value + 100)
def decodeEvent (value : Nat) : Nat := value - 100

theorem captureEvent_preserves_observation (value stored : Nat)
    (captured : captureEvent value = some stored) : decodeEvent stored = value := by
  simp only [captureEvent, Option.some.injEq] at captured
  subst stored
  simp [decodeEvent]

def start (limit : Nat) : Packet := initial ⟨OwnedPullDriver.exampleProgram, []⟩ 0 limit

def feed (ticks limit : Nat) : List (Notice Nat Nat Empty Empty) × Packet :=
  run driverStep captureEvent (fun _ => true) (fun _ => true) ticks (start limit)

theorem staged_occurrences_are_actual_driver_events : (feed 10 4).1.flatMap returned = [1, 1, 3] := rfl

theorem admitted_occurrences_keep_order_and_duplicates :
    (feed 10 4).1.flatMap admitted = [101, 101, 103] ∧
      (feed 10 4).2.delivery.log.rows = [101, 101, 103] := ⟨rfl, rfl⟩

theorem completed_execution_retains_actual_final_value :
    (feed 10 4).2.execution = some ⟨⟨.done 6, []⟩, none, 3, .active⟩ ∧
      (feed 10 4).2.delivery.log.completed = true := ⟨rfl, rfl⟩

theorem driver_transitions_and_returns_have_distinct_debits :
    (feed 10 4).1.length = 10 ∧ ((feed 10 4).1.map driverTicks).sum = 5 ∧
      acceptedCount (feed 10 4).2 = 3 := ⟨rfl, rfl, rfl⟩

theorem charging_each_notice_overcharges_the_driver :
    (feed 10 4).1.length ≠ ((feed 10 4).1.map driverTicks).sum := by decide

theorem zero_limit_does_not_step_the_driver :
    (feed 20 0).2 = start 0 := rfl

theorem backpressure_does_not_charge_unexecuted_work :
    ((feed 20 0).1.map driverTicks).sum = 0 ∧
      ((feed 20 2).1.map driverTicks).sum = 4 := ⟨rfl, rfl⟩

theorem full_log_retains_unexecuted_suffix :
    (feed 20 2).2.execution = some ⟨⟨.emit 3 (.done 6), []⟩, none, 2, .active⟩ ∧
      (feed 20 2).2.delivery.log.rows = [101, 101] ∧
      (feed 20 2).2.delivery.log.completed = false := ⟨rfl, rfl, rfl⟩

def staged : Packet := (feed 2 4).2

theorem staged_return_keeps_its_caller_frame :
    staged.execution = some
      ⟨⟨.done 2, [fun value => .emit 1 (.emit 3 (.done (value + 4)))]⟩, some 1, 0, .active⟩ := rfl

theorem capture_refusal_keeps_pending_return_and_frame :
    pump driverStep (fun _ => none) (fun _ => true) (fun _ => true) staged =
      (.captureRefused, staged) := rfl

theorem capacity_refusal_keeps_pending_return_and_frame :
    pump driverStep captureEvent (fun _ => false) (fun _ => true) staged =
      (.admissionRefused, staged) := rfl

theorem repeated_refusal_does_not_reexecute_the_pending_return :
    (run driverStep captureEvent (fun _ => false) (fun _ => true) 20 staged).2 = staged := rfl

theorem refusal_and_successful_admission_do_not_recharge_the_producer :
    ((run driverStep captureEvent (fun _ => false) (fun _ => true) 20 staged).1.map driverTicks).sum = 0 ∧
      driverTicks (pump driverStep captureEvent (fun _ => true) (fun _ => true) staged).1 = 0 :=
  ⟨rfl, rfl⟩

def retried : Packet := (pump driverStep captureEvent (fun _ => true) (fun _ => true) staged).2

theorem retry_admits_once_and_preserves_the_complete_driver_residual :
    retried.delivery.log.rows = [101] ∧
      retried.execution = some
        ⟨⟨.done 2, [fun value => .emit 1 (.emit 3 (.done (value + 4)))]⟩, none, 1, .active⟩ := ⟨rfl, rfl⟩

/-- A faulty boundary dropping its pending value skips an admitted occurrence. -/
def droppedPending : Packet :=
  {staged with execution := staged.execution.map (fun execution => {execution with pending := none})}

theorem dropping_pending_loses_the_first_occurrence :
    admitted (pump driverStep captureEvent (fun _ => true) (fun _ => true) droppedPending).1 ≠ [101] := by
  decide

theorem malformed_capture_changes_the_observation :
    (admitted (pump driverStep (fun _ => some 999) (fun _ => true) (fun _ => true) staged).1).map
        decodeEvent ≠ (pending staged).toList := by decide

theorem refusal_is_not_completion :
    (pump driverStep (fun _ => none) (fun _ => true) (fun _ => true) staged).2.delivery.log.completed ≠ true := by
  decide

def deliveredA : Packet := (deliver (fun _ => true) (feed 10 4).2 0 7).2

theorem consumers_have_independent_duplicate_occurrences :
    (deliver (fun _ => true) (feed 10 4).2 0 7).1 = .observed (.answer 0 101) ∧
      (deliver (fun _ => true) deliveredA 0 7).1 = .observed (.answer 1 101) ∧
      (deliver (fun _ => true) deliveredA 1 8).1 = .observed (.answer 0 101) := ⟨rfl, rfl, rfl⟩

/-- The first occurrence is buffered while its producer retains two more
emissions and nested return work. This is not a completed log snapshot. -/
def buffered : Packet := (feed 3 4).2

theorem recursive_slice_overlaps_buffered_delivery (ticks : Nat) :
    (let produced := run driverStep captureEvent (fun _ => true) (fun _ => true) ticks buffered
     let consumed := deliver (fun _ => true) produced.2 0 7
     (produced.1, consumed.1, consumed.2)) =
      (let consumed := deliver (fun _ => true) buffered 0 7
       let produced := run driverStep captureEvent (fun _ => true) (fun _ => true) ticks consumed.2
       (produced.1, consumed.1, produced.2)) :=
  run_deliver_buffered_commute _ _ _ _ ticks buffered 0 7 0 101 rfl

theorem interleaved_delivery_retains_occurrences_cursors_and_caller :
    let consumed := deliver (fun _ => true) buffered 0 7
    let finished := run driverStep captureEvent (fun _ => true) (fun _ => true) 7 consumed.2
    finished.2.delivery.log.rows = [101, 101, 103] ∧
      finished.2.delivery.log.completed = true ∧
      finished.2.delivery.log.positions 0 = some 1 ∧
      finished.2.delivery.log.positions 1 = some 0 ∧
      (7, 101) ∈ finished.2.delivery.published := by decide

/-- An unserved consumer observes the new occurrence only after admission.
Moving that read earlier leaves it paused at its old position. -/
theorem waiting_delivery_cannot_commute_with_admission :
    (deliver (fun _ => true) staged 0 7).1 = .observed .paused ∧
      (deliver (fun _ => true) retried 0 7).1 = .observed (.answer 0 101) ∧
      (pump driverStep captureEvent (fun _ => true) (fun _ => true)
        (deliver (fun _ => true) staged 0 7).2).2.delivery.log.positions 0 = some 0 ∧
      (deliver (fun _ => true) retried 0 7).2.delivery.log.positions 0 = some 1 := by decide

theorem stale_context_cannot_deliver_a_buffered_answer :
    deliver (fun context => context == 1) (feed 10 4).2 0 7 =
      (.contextRefused, (feed 10 4).2) := rfl

theorem arbitrary_split_preserves_the_entire_configuration (first second : Nat) :
    feed (first + second) 4 =
      (let earlier := feed first 4
       let later := run driverStep captureEvent (fun _ => true) (fun _ => true) second earlier.2
       (earlier.1 ++ later.1, later.2)) := run_split _ _ _ _ first second (start 4)

abbrev SignalPacket := Configuration Nat Nat Nat Nat Nat Nat Nat 1

def signalStart : SignalPacket := initial 0 0 2

def paused : SignalPacket :=
  (pump (fun state => .yielded (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

def finished : SignalPacket :=
  (pump (fun state => .completed (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

theorem yield_and_completion_have_distinct_residuals :
    paused.execution = some ⟨1, none, 0, .active⟩ ∧
      paused.delivery.log.completed = false ∧ finished.delivery.log.completed = true := ⟨rfl, rfl, rfl⟩

def awaiting : SignalPacket :=
  (pump (fun state => .effect 7 (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

def handedOff : SignalPacket :=
  (pump (fun state => .handoff 8 (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

def interrupted : SignalPacket :=
  (pump (fun state => .interrupted (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

theorem effect_request_is_an_inert_barrier :
    pump (fun state => .returned 99 (state + 1)) captureEvent (fun _ => true) (fun _ => true) awaiting =
      (.effect 7, awaiting) ∧ awaiting.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem handoff_is_an_inert_barrier :
    pump (fun state => .returned 99 (state + 1)) captureEvent (fun _ => true) (fun _ => true) handedOff =
      (.handoff 8, handedOff) ∧ handedOff.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem handoff_does_not_certify_exhaustion : handedOff.delivery.log.completed ≠ true := by decide

theorem interruption_keeps_an_open_inert_residual :
    pump (fun state => .returned 99 (state + 1)) captureEvent (fun _ => true) (fun _ => true) interrupted =
      (.interrupted, interrupted) ∧ interrupted.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem detach_moves_pending_and_retains_buffered_occurrences :
    (detach staged).1 = staged.execution ∧ pending (detach staged).2 = none ∧
      (detach (feed 10 4).2).2.delivery.log.rows = [101, 101, 103] := ⟨rfl, rfl, rfl⟩

theorem detached_is_distinct_from_completion :
    (pump driverStep captureEvent (fun _ => true) (fun _ => true) (detach (feed 10 4).2).2).1 =
      .detached := rfl

theorem empty_open_buffer_is_a_pause :
    (deliver (fun _ => true) signalStart 0 7).1 = .observed .paused := rfl

theorem empty_completed_buffer_is_completion :
    (deliver (fun _ => true) finished 0 7).1 = .observed .completed := rfl

abbrev EmptyPacket := Configuration Driver Nat Nat Nat Nat Empty Empty 0

def noCohort : EmptyPacket := initial ⟨OwnedPullDriver.exampleProgram, []⟩ 0 0

def noDemand : Packet :=
  {staged with delivery :=
    SharedOccurrenceOwnership.cancelConsumer (SharedOccurrenceOwnership.cancelConsumer staged.delivery 0) 1}

theorem empty_cohort_does_not_step_or_certify_exhaustion :
    pump driverStep captureEvent (fun _ => true) (fun _ => true) noCohort =
      (.noConsumers, noCohort) ∧ noCohort.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem cancelled_cohort_keeps_pending_return_and_residual :
    pump driverStep captureEvent (fun _ => true) (fun _ => true) noDemand =
      (.noConsumers, noDemand) ∧ pending noDemand = some 1 := ⟨rfl, rfl⟩

theorem absent_demand_is_not_completion :
    (pump driverStep captureEvent (fun _ => true) (fun _ => true) noCohort).1 ≠ .completed := by decide

def fullHandoff : SignalPacket :=
  {handedOff with delivery := {handedOff.delivery with log := {handedOff.delivery.log with limit := 0}}}

theorem retained_handoff_precedes_row_backpressure :
    pump (fun state => .returned 99 (state + 1)) captureEvent (fun _ => true) (fun _ => true) fullHandoff =
      (.handoff 8, fullHandoff) := rfl

end Controls

end Mettapedia.Machines.Cursor.ProducerOccurrenceLog
