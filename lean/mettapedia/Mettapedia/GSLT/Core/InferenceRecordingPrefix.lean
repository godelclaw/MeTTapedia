import Mettapedia.Machines.TraceObservationBoundary
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Bounded prefixes shared by execution history consumers

A prefix retains ordered occurrences, remaining capacity and explicit omissions.
Payload transport preserves those quantities. Complete readouts require every
retained payload and causal graph to pass their own checks. This storage layer
is independent of any controller or producer execution strategy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.InferenceControl.Recording

variable {Event Payload : Type*}

/-- A prefix retained in reverse order, with unused capacity and the number
of later items omitted. Once capacity is exhausted it is never replenished
by resumption. -/
structure Prefix (Event : Type*) where
  reversed : List Event
  remaining : Nat
  omitted : Nat
deriving DecidableEq, Repr

namespace Prefix

def initial (capacity : Nat) : Prefix Event := ⟨[], capacity, 0⟩

def items (record : Prefix Event) : List Event := record.reversed.reverse

/-- Transport retained payloads without changing capacity or omission status.
This is an observation of an existing record, not a request to record an
unavailable prefix of execution. -/
def map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Prefix Event) : Prefix NextEvent :=
  ⟨record.reversed.map mapping, record.remaining, record.omitted⟩

@[simp] theorem map_id (record : Prefix Event) : record.map id = record := by
  cases record
  simp [map]

theorem map_comp {NextEvent FinalEvent : Type*}
    (first : Event → NextEvent) (second : NextEvent → FinalEvent) (record : Prefix Event) :
    (record.map first).map second = record.map (second ∘ first) := by
  simp [map, List.map_map]

@[simp] theorem items_map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Prefix Event) : (record.map mapping).items = record.items.map mapping := by
  simp [map, items, List.map_reverse]

/-- The thunk is demanded only when storage is available. The omitted
count is recording overhead even when no payload is materialized. -/
def push (record : Prefix Event) (event : Unit → Event) : Prefix Event :=
  match record.remaining with
  | 0 => { record with omitted := record.omitted + 1 }
  | left + 1 => { record with reversed := event () :: record.reversed, remaining := left }

/-- Payload transport commutes with accepting an event, including a full
prefix that only increases its omission count. -/
theorem push_map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Prefix Event) (event : Unit → Event) :
    (record.push event).map mapping =
      (record.map mapping).push (fun _ => mapping (event ())) := by
  cases available : record.remaining <;> simp [push, map, available]

def append : Prefix Event → List Event → Prefix Event
  | record, [] => record
  | record, event :: rest => append (record.push (fun _ => event)) rest

/-- Only an untruncated prefix may be presented as the complete recording
since its captured start. It says nothing about execution before that start. -/
def complete? (record : Prefix Event) : Option (List Event) :=
  if record.omitted = 0 then some record.items else none

theorem complete?_map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Prefix Event) : (record.map mapping).complete? =
      record.complete?.map (List.map mapping) := by
  by_cases complete : record.omitted = 0 <;> simp [complete?, map, items, complete]

theorem push_full (record : Prefix Event) (full : record.remaining = 0)
    (first second : Unit → Event) : record.push first = record.push second := by
  simp [push, full]

theorem append_append (record : Prefix Event) (first second : List Event) :
    record.append (first ++ second) = (record.append first).append second := by
  induction first generalizing record with
  | nil => rfl
  | cons event rest ih => exact ih _

theorem append_state (record : Prefix Event) (events : List Event) :
    (record.append events).items = record.items ++ events.take record.remaining ∧
      (record.append events).remaining = record.remaining - events.length ∧
      (record.append events).omitted = record.omitted + (events.length - record.remaining) := by
  induction events generalizing record with
  | nil => simp [append]
  | cons event rest ih =>
      cases available : record.remaining with
      | zero =>
          obtain ⟨retained, left, omitted⟩ := ih (record.push (fun _ => event))
          simp only [append, push, available]
          simp only [push, available] at retained left omitted
          simp [items] at retained ⊢
          exact ⟨retained, by simpa using left, by omega⟩
      | succ availableCount =>
          obtain ⟨retained, left, omitted⟩ := ih (record.push (fun _ => event))
          simp only [append, push, available]
          simp only [push, available] at retained left omitted
          simp only [items, List.reverse_cons] at retained
          refine ⟨?_, ?_, ?_⟩
          · simpa [available, items, List.append_assoc] using retained
          · simpa [available] using left
          · simpa [available] using omitted

theorem initial_items (capacity : Nat) (events : List Event) :
    ((initial capacity : Prefix Event).append events).items = events.take capacity := by
  simpa [initial, items] using (append_state (initial capacity) events).1

theorem initial_omitted (capacity : Nat) (events : List Event) :
    ((initial capacity : Prefix Event).append events).omitted = events.length - capacity := by
  simpa [initial] using (append_state (initial capacity) events).2.2

theorem complete_iff (capacity : Nat) (events : List Event) :
    ((initial capacity : Prefix Event).append events).complete? = some events ↔
      events.length ≤ capacity := by
  rw [complete?, initial_omitted]
  by_cases fits : events.length ≤ capacity
  · simp [fits, Nat.sub_eq_zero_of_le fits, initial_items, List.take_of_length_le fits]
  · have positive : events.length - capacity ≠ 0 := by omega
    simp [fits, positive]

/-- A supplied checker sees the declared interval when that interval fits and
the checker accepts it. An omission leaves the checker unconsulted.
`complete?.bind check` evaluates the supplied checker when the record is
complete. The consumer chooses the checker, and validation grants no
authority to advance the live runtime. -/
theorem complete_bind_iff {Result : Type*} (check : List Event → Option Result)
    (capacity : Nat) (events : List Event) (result : Result) :
    ((initial capacity).append events).complete?.bind check = some result ↔
      events.length ≤ capacity ∧ check events = some result := by
  constructor
  · intro accepted
    by_cases fits : events.length ≤ capacity
    · rw [(complete_iff capacity events).mpr fits] at accepted
      exact ⟨fits, accepted⟩
    · have lost : ((initial capacity).append events).omitted ≠ 0 := by
        rw [initial_omitted]
        omega
      rw [complete?, if_neg lost] at accepted
      cases accepted
  · rintro ⟨fits, checked⟩
    rw [(complete_iff capacity events).mpr fits]
    exact checked

/-- Any omission refuses every passive checker. The retained items stay in
the prefix for a weaker reading. -/
theorem omitted_bind {Result : Type*} (check : List Event → Option Result)
    (record : Prefix Event) (lost : record.omitted ≠ 0) :
    record.complete?.bind check = none := by
  rw [complete?, if_neg lost]
  exact Option.bind_none check

/-- The two numerical readouts count retained payloads and omitted requests
separately. Their sum is the exact number of observed selections. -/
theorem request_account (capacity : Nat) (events : List Event) :
    ((initial capacity : Prefix Event).append events).items.length +
      ((initial capacity : Prefix Event).append events).omitted = events.length := by
  rw [initial_items, initial_omitted, List.length_take]
  omega


private theorem mapPayloads_iff (decode : Event → Option Payload)
    (events : List Event) (payloads : List Payload) :
    events.mapM decode = some payloads ↔
      List.Forall₂ (fun event payload => decode event = some payload) events payloads := by
  induction events generalizing payloads with
  | nil => cases payloads <;> simp
  | cons event rest ih =>
      cases decoded : decode event with
      | none => cases payloads <;> simp [List.mapM_cons, decoded]
      | some payload =>
          cases payloads with
          | nil =>
              cases tail : rest.mapM decode <;> simp [List.mapM_cons, decoded, tail]
          | cons first others =>
              cases tail : rest.mapM decode with
              | none => simp [List.mapM_cons, decoded, tail, ← ih]
              | some values => simp [List.mapM_cons, decoded, tail, ← ih]

/-- Decode every retained payload only when the outer prefix is complete.
A refused inner graph makes the projection incomplete, rather than silently
filtering that occurrence from a successful readout. -/
def project? (decode : Event → Option Payload) (record : Prefix Event) : Option (List Payload) :=
  record.complete?.bind (fun events => events.mapM decode)

theorem project?_iff (decode : Event → Option Payload) (record : Prefix Event)
    (payloads : List Payload) : project? decode record = some payloads ↔
    record.omitted = 0 ∧
      List.Forall₂ (fun event payload => decode event = some payload) record.items payloads := by
  by_cases complete : record.omitted = 0
  · simp [project?, complete?, complete, mapPayloads_iff]
  · simp [project?, complete?, complete]

theorem project?_length (decode : Event → Option Payload) (record : Prefix Event)
    (payloads : List Payload) (accepted : project? decode record = some payloads) :
    payloads.length = record.items.length :=
  ((project?_iff decode record payloads).mp accepted).2.length_eq.symm

theorem project?_truncated (decode : Event → Option Payload) (record : Prefix Event)
    (lost : record.omitted ≠ 0) : project? decode record = none := by
  simp [project?, complete?, lost]

/-- An inner refusal cannot disappear from a complete outer recording. -/
theorem project?_refused (decode : Event → Option Payload) (record : Prefix Event)
    (event : Event) (member : event ∈ record.items) (refused : decode event = none) :
    project? decode record = none := by
  cases result : project? decode record with
  | none => rfl
  | some payloads =>
      have related := ((project?_iff decode record payloads).mp result).2
      have all : ∀ event ∈ record.items, ∃ payload, decode event = some payload := by
        clear result
        generalize record.items = events at related ⊢
        induction related with
        | nil => simp
        | cons decoded rest ih =>
            intro event found
            rcases List.mem_cons.mp found with rfl | found
            · exact ⟨_, decoded⟩
            · exact ih event found
      obtain ⟨payload, decoded⟩ := all event member
      simp [refused] at decoded

/-- Occurrence keys are retained when the payload decoder preserves them.
Payload equality alone supplies no such identity law. -/
theorem project?_keys {Key : Type*} (decode : Event → Option Payload)
    (eventKey : Event → Key) (payloadKey : Payload → Key)
    (faithful : ∀ event payload, decode event = some payload → eventKey event = payloadKey payload)
    (record : Prefix Event) (payloads : List Payload)
    (accepted : project? decode record = some payloads) :
    record.items.map eventKey = payloads.map payloadKey := by
  have related := ((project?_iff decode record payloads).mp accepted).2
  clear accepted
  generalize record.items = events at related ⊢
  induction related with
  | nil => rfl
  | cons decoded rest ih =>
      simp only [List.map_cons]
      rw [faithful _ _ decoded, ih]

theorem initial_project?_iff (decode : Event → Option Payload) (capacity : Nat)
    (events : List Event) (payloads : List Payload) :
    project? decode ((initial capacity).append events) = some payloads ↔
      events.length ≤ capacity ∧
        List.Forall₂ (fun event payload => decode event = some payload) events payloads := by
  rw [project?_iff, initial_omitted, initial_items]
  by_cases fits : events.length ≤ capacity
  · simp [fits, Nat.sub_eq_zero_of_le fits, List.take_of_length_le fits]
  · have positive : events.length - capacity ≠ 0 := by omega
    simp [positive, fits]

/-- A conservative retained-storage charge is bounded only when every
retained payload has a supplied charge bound. Node count alone supplies none. -/
theorem retained_charge_bound (charge : Event → Nat) (capacity perItem : Nat)
    (events : List Event) (bounded : ∀ event ∈ events.take capacity, charge event ≤ perItem) :
    ((((initial capacity : Prefix Event).append events).items).map charge).sum ≤ capacity * perItem := by
  rw [initial_items]
  have localBound := List.sum_le_card_nsmul ((events.take capacity).map charge) perItem (by
    intro value member
    obtain ⟨event, eventMember, rfl⟩ := List.mem_map.mp member
    exact bounded event eventMember)
  simp only [List.length_map, List.length_take, nsmul_eq_mul] at localBound
  exact localBound.trans (Nat.mul_le_mul_right perItem (Nat.min_le_left _ _))

/-- A complete graph readout uses the existing causal receipt. Its explicit
boundary lists dependencies captured before this recording scope. Structural
checking does not authenticate the evaluator's claimed dependency edges. -/
def graph? [DecidableEq Event] (boundary roots : List Event)
    (record : Prefix (Mettapedia.Machines.CausalEvent Event)) :
    Option (Mettapedia.Machines.CausalReceipt Event) := do
  let events ← record.complete?
  let receipt : Mettapedia.Machines.CausalReceipt Event := ⟨roots, events⟩
  if receipt.check boundary then some receipt else none

theorem graph?_sound [DecidableEq Event] (boundary roots : List Event)
    (record : Prefix (Mettapedia.Machines.CausalEvent Event))
    (receipt : Mettapedia.Machines.CausalReceipt Event)
    (accepted : graph? boundary roots record = some receipt) :
    record.complete? = some receipt.events ∧ receipt.WellFormed boundary ∧ receipt.roots = roots := by
  unfold graph? at accepted
  cases complete : record.complete? with
  | none => simp [complete] at accepted
  | some events =>
    simp only [complete] at accepted
    change (if Mettapedia.Machines.CausalReceipt.check boundary ⟨roots, events⟩
      then some ⟨roots, events⟩ else none) = some receipt at accepted
    split at accepted
    · rename_i checked
      cases Option.some.inj accepted
      exact ⟨rfl, (Mettapedia.Machines.CausalReceipt.check_iff _ _).mp checked, rfl⟩
    · cases accepted

theorem graph?_truncated [DecidableEq Event] (boundary roots : List Event)
    (record : Prefix (Mettapedia.Machines.CausalEvent Event)) (lost : record.omitted ≠ 0) :
    graph? boundary roots record = none := by
  simp [graph?, complete?, lost]

/-- A complete graph readout requires both occurrence coverage and the
structural graph contract. Neither is inferred from the returned answer. -/
theorem initial_graph_iff [DecidableEq Event] (boundary roots : List Event)
    (capacity : Nat) (events : List (Mettapedia.Machines.CausalEvent Event)) :
    graph? boundary roots ((initial capacity).append events) = some ⟨roots, events⟩ ↔
      events.length ≤ capacity ∧ Mettapedia.Machines.CausalReceipt.WellFormed boundary
        ⟨roots, events⟩ := by
  constructor
  · intro accepted
    obtain ⟨complete, valid, _⟩ := graph?_sound boundary roots _ _ accepted
    exact ⟨(complete_iff capacity events).mp complete, valid⟩
  · rintro ⟨fits, valid⟩
    have complete := (complete_iff capacity events).mpr fits
    have checked := (Mettapedia.Machines.CausalReceipt.check_iff _ _).mpr valid
    simp [graph?, complete, checked]

end Prefix

/-- `none` is genuinely disabled; `some 0` records omissions from the first
selected occurrence. The two states have different observation contracts. -/
def initial (capacity : Option Nat) : Option (Prefix Event) :=
  capacity.map Prefix.initial

def accept (record : Option (Prefix Event)) (event : Unit → Event) : Option (Prefix Event) :=
  match record with
  | none => none
  | some record => some (record.push event)

theorem accept_map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Option (Prefix Event)) (event : Unit → Event) :
    (accept record event).map (Prefix.map mapping) =
      accept (record.map (Prefix.map mapping)) (fun _ => mapping (event ())) := by
  cases record with
  | none => rfl
  | some record => simp only [accept, Option.map_some, Prefix.push_map]

def append (record : Option (Prefix Event)) (events : List Event) : Option (Prefix Event) :=
  record.map (fun retained => retained.append events)

@[simp] theorem append_nil (record : Option (Prefix Event)) : append record [] = record := by
  cases record <;> rfl

theorem append_cons (record : Option (Prefix Event)) (event : Event) (rest : List Event) :
    append record (event :: rest) = append (accept record (fun _ => event)) rest := by
  cases record <;> rfl

theorem append_append (record : Option (Prefix Event)) (first second : List Event) :
    append record (first ++ second) = append (append record first) second := by
  cases record with
  | none => rfl
  | some record => simp [append, Prefix.append_append]

/-- Existing prefix append is the stateful observer's chronological consume
fold, including disabled recording and omission-only updates. -/
theorem append_foldl (record : Option (Prefix Event)) (events : List Event) :
    append record events =
      events.foldl (fun current event => accept current (fun _ => event)) record := by
  induction events generalizing record with
  | nil => exact append_nil _
  | cons event rest ih => rw [append_cons, List.foldl_cons, ih]

end Mettapedia.GSLT.Core.InferenceControl.Recording
