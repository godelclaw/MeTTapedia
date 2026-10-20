import Mettapedia.Machines.Cursor.Sequence
import Mettapedia.Machines.SnapshotBatch
import Mettapedia.Machines.BindingPublication

/-!
# A resumable fold client for a pull protocol

The client requests one occurrence, updates its retained accumulator, and asks
again. It neither allocates a collection of answers nor chooses an agenda.
The accumulator may be a count, a private store delta, an output sink, or an
ordinary list. Budget exhaustion retains both accumulator and producer state.

The finite list provider is the semantic reference. Existing provider homs
transfer its laws to independently implemented sequence representations.
The arbitrary-provider client can also run indefinitely; no finite list is
required in its state. Completion requires an actual exhaustion reply.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.Fold

open Mettapedia.TypeTheory
open CategoryTheory

variable {Item Accumulator : Type}

inductive State (Accumulator : Type) where
  | pulling (accumulator : Accumulator)
  | finished (accumulator : Accumulator)
  deriving Repr, DecidableEq

def client (consume : Accumulator → Item → Accumulator) :
    Client (P := Sequence.protocol Item) (Return := fun _ _ => Accumulator) where
  V _ _ := State Accumulator
  str := fun _ _ => ↾(fun state => match state with
    | .finished accumulator =>
        ⟨.inl accumulator, fun impossible => nomatch impossible⟩
    | .pulling accumulator =>
        ⟨.inr (), fun reply => match reply with
          | none => .finished accumulator
          | some item => .pulling (consume accumulator item)⟩)

def start (provider : Provider (Sequence.protocol Item))
    (consume : Accumulator → Item → Accumulator)
    (state : provider.State () ()) (accumulator : Accumulator) :
    Packet provider (client consume) () :=
  ⟨(), .pulling accumulator, state⟩

/-- A positive quantum consumes exactly that prefix when exhaustion has not
yet been inspected. Duplicate items are individual pulls. -/
theorem prefix_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (quantum : Nat)
    (within : quantum ≤ items.length) :
    advance (Sequence.tails Item) (client consume) (fun _ _ => 1) quantum
        (start _ consume items accumulator) =
      (quantum, .paused
        (start _ consume (items.drop quantum) ((items.take quantum).foldl consume accumulator))) := by
  induction quantum generalizing items accumulator with
  | zero => simp [advance, start]
  | succ quantum ih =>
      cases items with
      | nil => simp at within
      | cons item rest =>
          have bound : quantum ≤ rest.length := by simpa using within
          change (1 + (advance (Sequence.tails Item) (client consume) (fun _ _ => 1)
              quantum (start _ consume rest (consume accumulator item))).1,
            (advance (Sequence.tails Item) (client consume) (fun _ _ => 1)
              quantum (start _ consume rest (consume accumulator item))).2) = _
          rw [ih rest (consume accumulator item) bound]
          simp [Nat.add_comm]

/-- One final pull discovers exhaustion; one client inspection returns.
The receipt charges pulls, including the exhaustion check, not client return. -/
theorem complete_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) :
    advance (Sequence.tails Item) (client consume) (fun _ _ => 1) (items.length + 2)
        (start _ consume items accumulator) =
      (items.length + 1, .done ⟨(), items.foldl consume accumulator, []⟩) := by
  induction items generalizing accumulator with
  | nil => rfl
  | cons item rest ih =>
      change (1 + (advance (Sequence.tails Item) (client consume) (fun _ _ => 1)
          (rest.length + 2) (start _ consume rest (consume accumulator item))).1,
        (advance (Sequence.tails Item) (client consume) (fun _ _ => 1)
          (rest.length + 2) (start _ consume rest (consume accumulator item))).2) = _
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem resumed_prefix_completes (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (first rest : Nat)
    (enough : first + rest = items.length + 2) :
    resume (Sequence.tails Item) (client consume) (fun _ _ => 1) rest
      (advance (Sequence.tails Item) (client consume) (fun _ _ => 1) first
        (start _ consume items accumulator)) =
      (items.length + 1, .done ⟨(), items.foldl consume accumulator, []⟩) := by
  rw [← advance_add, enough, complete_exact]

/-- The same client can aggregate without storing its input occurrences. -/
theorem count_without_collection (items : List Item) (initial : Nat) :
    advance (Sequence.tails Item) (client (fun n _ => n + 1)) (fun _ _ => 1)
      (items.length + 2) (start _ (fun n _ => n + 1) items initial) =
      (items.length + 1, .done ⟨(), initial + items.length, []⟩) := by
  rw [complete_exact]
  have count : items.foldl (fun n _ => n + 1) initial = initial + items.length := by
    induction items generalizing initial with
    | nil => simp
    | cons item rest ih =>
        rw [List.foldl_cons, ih]
        simp only [List.length_cons]
        omega
  rw [count]

namespace Controls

theorem partial_delivery_is_retained :
    advance (Sequence.tails Nat) (client (· + ·)) (fun _ _ => 1) 2
      (start _ (· + ·) [3, 3, 5] 0) =
      (2, .paused (start _ (· + ·) [5] 6)) := rfl

theorem replay_duplicates_delivered_items :
    (advance (Sequence.tails Nat) (client (· + ·)) (fun _ _ => 1) 5
      (start _ (· + ·) [3, 3, 5] 6)).2 ≠
    (advance (Sequence.tails Nat) (client (· + ·)) (fun _ _ => 1) 3
      (start _ (· + ·) [5] 6)).2 := by
  intro equal
  have readout := congrArg (fun outcome => match outcome with
    | .done result => some result.2.1
    | .paused _ => none) equal
  change some 17 = some 11 at readout
  cases readout

end Controls

/-! ## An owned pending-return boundary

The producer removes an occurrence into a borrowed pending slot before the
consumer accepts it. Rejection retains that slot and the accumulator.
The allowance counts accepted returns; discovering exhaustion is a separate
producer request, distinct from semantic evaluation fuel.
-/

namespace OwnedSequence

structure Packet (Item Accumulator : Type) where
  remaining : List Item
  pending : Option Item
  accumulator : Accumulator
  accepted : Nat
  requested : Nat
  deriving DecidableEq, Repr

inductive Stop where
  | paused
  | complete
  deriving DecidableEq, Repr

def undelivered (state : Packet Item Accumulator) : List Item :=
  state.pending.toList ++ state.remaining

/-- A partial consumer commits only a successful update. Holding an item does
not change its bindings, delayed conditions or syntax/value provenance. -/
def sequence (consume : Accumulator → Item → Option Accumulator) :
    Nat → Packet Item Accumulator → Stop × Packet Item Accumulator
  | 0, state => (.paused, state)
  | allowance + 1, state =>
      match state.pending with
      | some item =>
          match consume state.accumulator item with
          | none => (.paused, state)
          | some accumulator => sequence consume allowance
              ⟨state.remaining, none, accumulator, state.accepted + 1, state.requested⟩
      | none =>
          match state.remaining with
          | [] => (.complete, {state with requested := state.requested + 1})
          | item :: rest =>
              let prepared : Packet Item Accumulator :=
                ⟨rest, some item, state.accumulator, state.accepted, state.requested + 1⟩
              match consume state.accumulator item with
              | none => (.paused, prepared)
              | some accumulator => sequence consume allowance
                  ⟨rest, none, accumulator, state.accepted + 1, state.requested + 1⟩

/-- Resuming a completed boundary does not inspect exhaustion again. A paused
boundary retries its retained loan before requesting another occurrence. -/
def resume (consume : Accumulator → Item → Option Accumulator)
    (allowance : Nat) (earlier : Stop × Packet Item Accumulator) :
    Stop × Packet Item Accumulator :=
  match earlier.1 with
  | .paused => sequence consume allowance earlier.2
  | .complete => earlier

/-- Partial acceptance grows its account monotonically and by at most the
acceptance allowance. Producer requests and terminal inspection are distinct.
A native bounded-word realization needs its separate nonwrapping premise. -/
theorem sequence_acceptance_bound
    (consume : Accumulator → Item → Option Accumulator)
    (allowance : Nat) (state : Packet Item Accumulator) :
    state.accepted ≤ (sequence consume allowance state).2.accepted ∧
    (sequence consume allowance state).2.accepted ≤ state.accepted + allowance := by
  induction allowance generalizing state with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ allowance ih =>
      rcases state with ⟨remaining, pending, accumulator, accepted, requested⟩
      cases pending with
      | some item =>
          cases decision : consume accumulator item with
          | none =>
              simp only [sequence, decision]
              exact ⟨Nat.le_refl accepted, Nat.le_add_right accepted (allowance + 1)⟩
          | some next =>
              have bounded := ih ⟨remaining, none, next, accepted + 1, requested⟩
              simp only [sequence, decision]
              change accepted + 1 ≤ _ ∧ _ ≤ accepted + 1 + allowance at bounded
              constructor
              · exact Nat.le_trans (Nat.le_succ accepted) bounded.1
              · rw [Nat.add_assoc, Nat.add_comm 1 allowance] at bounded
                exact bounded.2
      | none =>
          cases remaining with
          | nil =>
              change accepted ≤ accepted ∧ accepted ≤ accepted + (allowance + 1)
              exact ⟨Nat.le_refl accepted, Nat.le_add_right accepted (allowance + 1)⟩
          | cons item remaining =>
              cases decision : consume accumulator item with
              | none =>
                  simp only [sequence, decision]
                  exact ⟨Nat.le_refl accepted, Nat.le_add_right accepted (allowance + 1)⟩
              | some next =>
                  have bounded := ih ⟨remaining, none, next, accepted + 1, requested + 1⟩
                  simp only [sequence, decision]
                  change accepted + 1 ≤ _ ∧ _ ≤ accepted + 1 + allowance at bounded
                  constructor
                  · exact Nat.le_trans (Nat.le_succ accepted) bounded.1
                  · rw [Nat.add_assoc, Nat.add_comm 1 allowance] at bounded
                    exact bounded.2

/-- A finite native observation can admit a nonwrapping acceptance account
using an allowance bound, without equating acceptance with producer work. -/
theorem sequence_acceptance_below
    (consume : Accumulator → Item → Option Accumulator)
    (allowance bound : Nat) (state : Packet Item Accumulator)
    (within : state.accepted + allowance < bound) :
    (sequence consume allowance state).2.accepted < bound :=
  Nat.lt_of_le_of_lt (sequence_acceptance_bound consume allowance state).2 within

/-- Acceptance allowances compose for the actual pending-return boundary,
including refusal. Neither a rejected loan nor terminal exhaustion is replayed.
This statement concerns the pure consumer transition; it does not reorder
native callbacks, effects or authority observations. -/
theorem sequence_add (consume : Accumulator → Item → Option Accumulator)
    (first rest : Nat) (state : Packet Item Accumulator) :
    sequence consume (first + rest) state =
      resume consume rest (sequence consume first state) := by
  induction first generalizing state with
  | zero => simp [sequence, resume]
  | succ first ih =>
      rcases state with ⟨remaining, pending, accumulator, accepted, requested⟩
      cases pending with
      | some item =>
          cases decision : consume accumulator item with
          | none =>
              cases rest <;> simp [sequence, resume, decision]
          | some next =>
              simpa only [Nat.succ_add, sequence, decision] using
                ih ⟨remaining, none, next, accepted + 1, requested⟩
      | none =>
          cases remaining with
          | nil => simp [sequence, resume, Nat.succ_add]
          | cons item remaining =>
              cases decision : consume accumulator item with
              | none =>
                  cases rest <;> simp [sequence, resume, decision]
              | some next =>
                  simpa only [Nat.succ_add, sequence, decision] using
                    ih ⟨remaining, none, next, accepted + 1, requested + 1⟩

/-- Independent materialization followed by a fold is the finite reference.
The common boundary retains just the residual and accumulator. -/
theorem prefix_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (accepted requested allowance : Nat)
    (within : allowance ≤ items.length) :
    sequence (fun acc item => some (consume acc item)) allowance
        ⟨items, none, accumulator, accepted, requested⟩ =
      (.paused, ⟨items.drop allowance, none, (items.take allowance).foldl consume accumulator,
        accepted + allowance, requested + allowance⟩) := by
  induction allowance generalizing items accumulator accepted requested with
  | zero => simp [sequence]
  | succ allowance ih =>
      cases items with
      | nil => simp at within
      | cons item rest =>
          have bound : allowance ≤ rest.length := by simpa using within
          change sequence (fun acc item => some (consume acc item)) allowance
            ⟨rest, none, consume accumulator item, accepted + 1, requested + 1⟩ = _
          rw [ih rest (consume accumulator item) (accepted + 1) (requested + 1) bound]
          simp [Nat.add_comm, Nat.add_left_comm]

/-- Completion has inspected the producer's terminal state. Duplicate
occurrences each contribute an update and are never collapsed by value. -/
theorem complete_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (accepted requested : Nat) :
    sequence (fun acc item => some (consume acc item)) (items.length + 1)
        ⟨items, none, accumulator, accepted, requested⟩ =
      (.complete, ⟨[], none, items.foldl consume accumulator,
        accepted + items.length, requested + items.length + 1⟩) := by
  induction items generalizing accumulator accepted requested with
  | nil => simp [sequence]
  | cons item rest ih =>
      change sequence (fun acc item => some (consume acc item)) (rest.length + 1)
        ⟨rest, none, consume accumulator item, accepted + 1, requested + 1⟩ = _
      rw [ih (consume accumulator item) (accepted + 1) (requested + 1)]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- A retained return is accepted before the residual prefix, without an
additional producer request for that return. All previous counters survive. -/
theorem pending_complete_exact (consume : Accumulator → Item → Accumulator)
    (rest : List Item) (item : Item) (accumulator : Accumulator)
    (accepted requested : Nat) :
    sequence (fun acc value => some (consume acc value)) (rest.length + 2)
        ⟨rest, some item, accumulator, accepted, requested⟩ =
      (.complete, ⟨[], none, rest.foldl consume (consume accumulator item),
        accepted + (rest.length + 1), requested + rest.length + 1⟩) := by
  change sequence (fun acc value => some (consume acc value)) (rest.length + 1)
    ⟨rest, none, consume accumulator item, accepted + 1, requested⟩ = _
  rw [complete_exact]
  simp only [Nat.add_assoc, Nat.add_comm 1 rest.length]

/-- Splitting accepted-return allowances retains the whole accumulator and
exact counters, even when the first slice already discovers exhaustion. -/
theorem resumed_complete_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator)
    (accepted requested first rest : Nat)
    (enough : first + rest = items.length + 1) :
    resume (fun acc item => some (consume acc item)) rest
      (sequence (fun acc item => some (consume acc item)) first
        ⟨items, none, accumulator, accepted, requested⟩) =
      (.complete, ⟨[], none, items.foldl consume accumulator,
        accepted + items.length, requested + items.length + 1⟩) := by
  rw [← sequence_add, enough, complete_exact]

/-- A completed boundary never asks the producer to report exhaustion twice. -/
theorem completed_resume_is_inert
    (consume : Accumulator → Item → Option Accumulator)
    (allowance : Nat) (state : Packet Item Accumulator) :
    resume consume allowance (.complete, state) = (.complete, state) := rfl

theorem rejected_return_is_retained (consume : Accumulator → Item → Option Accumulator)
    (rest : List Item) (item : Item) (accumulator : Accumulator)
    (accepted requested allowance : Nat) (reject : consume accumulator item = none) :
    sequence consume (allowance + 1) ⟨rest, some item, accumulator, accepted, requested⟩ =
      (.paused, ⟨rest, some item, accumulator, accepted, requested⟩) := by
  simp [sequence, reject]

theorem pending_resume_does_not_pull_again (consume : Accumulator → Item → Accumulator)
    (rest : List Item) (item : Item) (accumulator : Accumulator) (accepted requested : Nat) :
    sequence (fun acc value => some (consume acc value)) 1
        ⟨rest, some item, accumulator, accepted, requested⟩ =
      (.paused, ⟨rest, none, consume accumulator item, accepted + 1, requested⟩) := rfl

/-- Moving a rejected occurrence into pending storage preserves its place in
the residual, including equal-valued predecessors or successors. -/
theorem rejected_fresh_return_preserves_residual
    (consume : Accumulator → Item → Option Accumulator)
    (rest : List Item) (item : Item) (accumulator : Accumulator)
    (accepted requested allowance : Nat) (reject : consume accumulator item = none) :
    undelivered (sequence consume (allowance + 1)
      ⟨item :: rest, none, accumulator, accepted, requested⟩).2 = item :: rest := by
  simp [sequence, reject, undelivered]

/-- Cancellation abandons undelivered work and keeps committed receipts. -/
def cancel (state : Packet Item Accumulator) : Packet Item Accumulator :=
  {state with remaining := [], pending := none}

/-- Change the representations of returns and committed consumer state. The
loan, occurrence order, and acceptance/request accounts are transported whole. -/
def Packet.map {Item' Accumulator' : Type}
    (itemMap : Item → Item') (accumulatorMap : Accumulator → Accumulator')
    (state : Packet Item Accumulator) : Packet Item' Accumulator' :=
  ⟨state.remaining.map itemMap, state.pending.map itemMap,
    accumulatorMap state.accumulator, state.accepted, state.requested⟩

theorem Packet.map_id (state : Packet Item Accumulator) : state.map id id = state := by
  cases state with
  | mk remaining pending accumulator accepted requested =>
      cases pending <;> simp [Packet.map]

theorem Packet.map_map {Item' Accumulator' Item'' Accumulator'' : Type}
    (itemMap : Item → Item') (accumulatorMap : Accumulator → Accumulator')
    (itemMap' : Item' → Item'') (accumulatorMap' : Accumulator' → Accumulator'')
    (state : Packet Item Accumulator) :
    (state.map itemMap accumulatorMap).map itemMap' accumulatorMap' =
      state.map (itemMap' ∘ itemMap) (accumulatorMap' ∘ accumulatorMap) := by
  cases state with
  | mk remaining pending accumulator accepted requested =>
      cases pending <;> simp [Packet.map, List.map_map]

theorem undelivered_map {Item' Accumulator' : Type}
    (itemMap : Item → Item') (accumulatorMap : Accumulator → Accumulator')
    (state : Packet Item Accumulator) :
    undelivered (state.map itemMap accumulatorMap) = (undelivered state).map itemMap := by
  cases state with
  | mk remaining pending accumulator accepted requested =>
      cases pending <;> simp [undelivered, Packet.map]

/-- Return transport commutes with partial consumption when each successful
consumer update and each refusal is preserved. This is a local operation
obligation; the theorem derives correspondence for arbitrary allowances,
pending loans, residuals, and accounting histories. It does not permit an
effectful consumer to discard its private post-state on refusal. -/
theorem sequence_map {Item' Accumulator' : Type}
    (itemMap : Item → Item') (accumulatorMap : Accumulator → Accumulator')
    (consume : Accumulator → Item → Option Accumulator)
    (consume' : Accumulator' → Item' → Option Accumulator')
    (compatible : ∀ accumulator item,
      consume' (accumulatorMap accumulator) (itemMap item) =
        (consume accumulator item).map accumulatorMap)
    (allowance : Nat) (state : Packet Item Accumulator) :
    sequence consume' allowance (state.map itemMap accumulatorMap) =
      Prod.map id (Packet.map itemMap accumulatorMap) (sequence consume allowance state) := by
  induction allowance generalizing state with
  | zero => rfl
  | succ allowance ih =>
      rcases state with ⟨remaining, pending, accumulator, accepted, requested⟩
      cases pending with
      | some item =>
          cases decision : consume accumulator item with
          | none => simp [Packet.map, sequence, compatible, decision]
          | some next =>
              simpa [Packet.map, sequence, compatible, decision] using
                ih ⟨remaining, none, next, accepted + 1, requested⟩
      | none =>
          cases remaining with
          | nil => rfl
          | cons item remaining =>
              cases decision : consume accumulator item with
              | none => simp [Packet.map, sequence, compatible, decision]
              | some next =>
                  simpa [Packet.map, sequence, compatible, decision] using
                    ih ⟨remaining, none, next, accepted + 1, requested + 1⟩

/-- A representation change at suspension preserves the held return and
continues that same computation. A completed result remains completed. -/
theorem resume_map {Item' Accumulator' : Type}
    (itemMap : Item → Item') (accumulatorMap : Accumulator → Accumulator')
    (consume : Accumulator → Item → Option Accumulator)
    (consume' : Accumulator' → Item' → Option Accumulator')
    (compatible : ∀ accumulator item,
      consume' (accumulatorMap accumulator) (itemMap item) =
        (consume accumulator item).map accumulatorMap)
    (allowance : Nat) (earlier : Stop × Packet Item Accumulator) :
    resume consume' allowance (Prod.map id (Packet.map itemMap accumulatorMap) earlier) =
      Prod.map id (Packet.map itemMap accumulatorMap) (resume consume allowance earlier) := by
  rcases earlier with ⟨stop, state⟩
  cases stop with
  | paused => exact sequence_map itemMap accumulatorMap consume consume' compatible allowance state
  | complete => rfl

theorem cancel_map {Item' Accumulator' : Type}
    (itemMap : Item → Item') (accumulatorMap : Accumulator → Accumulator')
    (state : Packet Item Accumulator) :
    cancel (state.map itemMap accumulatorMap) = (cancel state).map itemMap accumulatorMap := rfl

theorem cancellation_after_prefix (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (accepted requested allowance : Nat)
    (within : allowance ≤ items.length) :
    (cancel (sequence (fun acc item => some (consume acc item)) allowance
      ⟨items, none, accumulator, accepted, requested⟩).2).accumulator =
        (items.take allowance).foldl consume accumulator ∧
    (cancel (sequence (fun acc item => some (consume acc item)) allowance
      ⟨items, none, accumulator, accepted, requested⟩).2).accepted = accepted + allowance := by
  rw [prefix_exact consume items accumulator accepted requested allowance within]
  exact ⟨rfl, rfl⟩

namespace Controls

theorem last_return_does_not_certify_exhaustion :
    sequence (fun n item : Nat => some (n + item)) 2 ⟨[3, 3], none, 0, 0, 0⟩ =
      (.paused, ⟨[], none, 6, 2, 2⟩) ∧
    sequence (fun n item : Nat => some (n + item)) 1 ⟨[], none, 6, 2, 2⟩ =
      (.complete, ⟨[], none, 6, 2, 3⟩) := by decide

theorem partial_replay_changes_result :
    (sequence (fun n item : Nat => some (n + item)) 4
      ⟨[3, 3, 5], none, 6, 2, 2⟩).2.accumulator = 17 ∧
    (sequence (fun n item : Nat => some (n + item)) 2
      ⟨[5], none, 6, 2, 2⟩).2.accumulator = 11 := by decide

/-- An accepted stop has committed one return. A refusal retains that same
return as a loan. Their residuals and receipts distinguish the two outcomes. -/
theorem accepted_stop_is_not_refusal :
    sequence (fun (delivered : List Nat) (item : Nat) => some (delivered ++ [item])) 1
        ⟨[7, 7], none, [], 0, 0⟩ =
      (.paused, ⟨[7], none, [7], 1, 1⟩) ∧
    sequence (fun (_ : List Nat) (_ : Nat) => none) 1
        ⟨[7, 7], none, [], 0, 0⟩ =
      (.paused, ⟨[7], some 7, [], 0, 1⟩) := by decide

end Controls


/-! Returned occurrences retain provenance and conditions as well as payload.
The common sequencer transports this record; activation belongs to the dialect
adapter and is absent from the transport operation. -/

inductive ReturnForm where
  | source
  | completed
  | conditional
  deriving DecidableEq, Repr

structure Returned (Term Environment : Type) where
  payload : Term
  environment : Environment
  form : ReturnForm
  conditions : List Term
  deriving DecidableEq, Repr

/-- Re-encode a returned occurrence without changing its role. Conditions use
the same term representation as its payload; the complete captured environment
is passed to the environment map rather than reconstructed from the payload. -/
def Returned.map {Term Environment Term' Environment' : Type}
    (termMap : Term → Term') (environmentMap : Environment → Environment')
    (returned : Returned Term Environment) : Returned Term' Environment' :=
  ⟨termMap returned.payload, environmentMap returned.environment, returned.form,
    returned.conditions.map termMap⟩

theorem Returned.map_id {Term Environment : Type} (returned : Returned Term Environment) :
    returned.map id id = returned := by
  cases returned
  simp [Returned.map]

/-- A storage or lowering map preserves the form even when it changes the
representation of the written term. It supplies no new activation authority. -/
theorem Returned.map_form {Term Environment Term' Environment' : Type}
    (termMap : Term → Term') (environmentMap : Environment → Environment')
    (returned : Returned Term Environment) :
    (returned.map termMap environmentMap).form = returned.form := rfl

/-- Successive crossings compose on the whole return, including captured
context and delayed conditions. -/
theorem Returned.map_map {Term Environment Term' Environment' Term'' Environment'' : Type}
    (termMap : Term → Term') (environmentMap : Environment → Environment')
    (termMap' : Term' → Term'') (environmentMap' : Environment' → Environment'')
    (returned : Returned Term Environment) :
    (returned.map termMap environmentMap).map termMap' environmentMap' =
      returned.map (termMap' ∘ termMap) (environmentMap' ∘ environmentMap) := by
  cases returned
  simp [Returned.map, List.map_map]

/-- Faithful payload and context encodings also reflect equality of complete
returns. Preservation by mapping alone does not establish this reflection. -/
theorem Returned.map_injective {Term Environment Term' Environment' : Type}
    {termMap : Term → Term'} {environmentMap : Environment → Environment'}
    (terms : Function.Injective termMap) (environments : Function.Injective environmentMap) :
    Function.Injective (Returned.map termMap environmentMap) := by
  intro left right equal
  have payload := terms (congrArg Returned.payload equal)
  have environment := environments (congrArg Returned.environment equal)
  have form := congrArg Returned.form equal
  have conditions := (List.map_injective_iff.mpr terms)
    (congrArg Returned.conditions equal)
  cases left
  cases right
  simp only [Returned.map] at payload environment form conditions
  cases payload
  cases environment
  cases form
  cases conditions
  rfl

/-- Collecting returned occurrences is a concrete compatible consumer. Thus
representation transport preserves every prefix and retained loan, with no
injectivity or distinct-payload assumption and no deduplication. -/
theorem returned_collection_map {Term Environment Term' Environment' : Type}
    (termMap : Term → Term') (environmentMap : Environment → Environment')
    (allowance : Nat)
    (state : Packet (Returned Term Environment) (List (Returned Term Environment))) :
    sequence (fun delivered returned => some (delivered ++ [returned])) allowance
      (state.map (Returned.map termMap environmentMap)
        (List.map (Returned.map termMap environmentMap))) =
      Prod.map id
        (Packet.map (Returned.map termMap environmentMap)
          (List.map (Returned.map termMap environmentMap)))
        (sequence (fun delivered returned => some (delivered ++ [returned])) allowance state) := by
  apply sequence_map
  intro accumulator item
  simp

theorem whole_return_delivery {Term Environment : Type}
    (returns : List (Returned Term Environment)) :
    sequence (fun delivered returned => some (delivered ++ [returned]))
      (returns.length + 1) ⟨returns, none, [], 0, 0⟩ =
        (.complete, ⟨[], none, returns, returns.length, returns.length + 1⟩) := by
  rw [complete_exact]
  have appendFold (items accumulated : List (Returned Term Environment)) :
      items.foldl (fun delivered returned => delivered ++ [returned]) accumulated =
        accumulated ++ items := by
    induction items generalizing accumulated with
    | nil => simp
    | cons item rest ih => simpa [List.append_assoc] using ih (accumulated ++ [item])
  simp [appendFold]

/-- Chunked delivery transports every occurrence with its environment,
provenance and conditions; equal payloads do not collapse distinct returns. -/
theorem resumed_whole_return_delivery {Term Environment : Type}
    (returns : List (Returned Term Environment)) (first rest : Nat)
    (enough : first + rest = returns.length + 1) :
    resume (fun delivered returned => some (delivered ++ [returned])) rest
      (sequence (fun delivered returned => some (delivered ++ [returned])) first
        ⟨returns, none, [], 0, 0⟩) =
      (.complete, ⟨[], none, returns, returns.length, returns.length + 1⟩) := by
  rw [← sequence_add, enough, whole_return_delivery]

namespace ReturnControls

def held : Returned Nat (List Nat) := ⟨7, [4, 4], .completed, []⟩
def source : Returned Nat (List Nat) := ⟨7, [4, 4], .source, []⟩
def conditional : Returned Nat (List Nat) := ⟨7, [4, 4], .conditional, [9]⟩

theorem equal_payloads_are_not_equal_returns :
    held.payload = source.payload ∧ held ≠ source ∧ conditional ≠ held := by decide

/-- No classifier of the written payload alone can recover whether all
returned occurrences are pending computations or completed data. -/
theorem payload_alone_cannot_recover_form :
    ¬ ∃ classify : Nat → ReturnForm,
      ∀ returned : Returned Nat (List Nat), classify returned.payload = returned.form := by
  rintro ⟨classify, correct⟩
  have same := (correct held).symm.trans (correct source)
  cases same

theorem held_and_delayed_forms_are_delivered_unchanged :
    sequence (fun delivered returned => some (delivered ++ [returned])) 5
      ⟨[held, held, source, conditional], none, [], 0, 0⟩ =
        (.complete, ⟨[], none, [held, held, source, conditional], 4, 5⟩) := by
  exact whole_return_delivery [held, held, source, conditional]

end ReturnControls



#print axioms sequence_add
#print axioms pending_complete_exact
#print axioms resumed_complete_exact
#print axioms resumed_whole_return_delivery
#print axioms sequence_map
#print axioms resume_map
#print axioms returned_collection_map
#print axioms ReturnControls.payload_alone_cannot_recover_form



/-! ## An owned callback call as a common cursor client

Acceptance allowance and scheduler inspections are independent. Each callback
reply includes its complete provider post-state. A refusal retains the loan but
may change private callback state. Resuming that call therefore does not inherit
the pure finite-consumer allowance composition theorem above. Source callback
realization, bounded-word accounts and normal callback return remain separate
native obligations.
-/

namespace CallbackBoundary

open Mettapedia.TypeTheory.IndexedPolynomial

variable {Item Terminal : Type}

inductive Request (Item : Type) where
  | next
  | accept (item : Item)

inductive NextReply (Item Terminal : Type) where
  | returned (item : Item)
  | paused
  | terminal (reason : Terminal)

/-- The terminal payload can distinguish exhaustion, handoff, interruption
and their completion reasons. Refusal is a separate Boolean accept reply. -/
abbrev protocol (Item Terminal : Type) :
    IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Request Item
  Position request := match request with
    | .next => NextReply Item Terminal
    | .accept _ => Bool
  next _ _ := ()

structure Result (Item Terminal : Type) where
  terminal : Option Terminal
  pending : Option Item
  accepted : Nat
  deriving DecidableEq, Repr

inductive Control (Item Terminal : Type) where
  | running (allowance : Nat) (pending : Option Item) (accepted : Nat)
  | stopped (result : Result Item Terminal)

/-- This is the existing indexed-polynomial client, not a second evaluator.
The private accumulator and callback caches belong to the provider's state. -/
abbrev client (Item Terminal : Type)
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    Client (P := protocol Item Terminal) (Return := fun _ _ => Result Item Terminal) where
  V _ _ := Control Item Terminal
  str := fun _ _ => ↾(fun control => match control with
    | .stopped result => ⟨.inl result, fun impossible => nomatch impossible⟩
    | .running 0 pending accepted =>
        ⟨.inl ⟨none,pending,accepted⟩, fun impossible => nomatch impossible⟩
    | .running (allowance+1) (some item) accepted =>
        ⟨.inr (.accept item), fun decision =>
          match decision with
          | true => match terminalAfter item with
              | none => .running allowance none (accepted+1)
              | some reason => .stopped ⟨some reason,none,accepted+1⟩
          | false => .stopped ⟨none,some item,accepted⟩⟩
    | .running (allowance+1) none accepted =>
        ⟨.inr .next, fun reply => match reply with
          | .returned item => .running (allowance+1) (some item) accepted
          | .paused => .stopped ⟨none,none,accepted⟩
          | .terminal reason => .stopped ⟨some reason,none,accepted⟩⟩)

variable (M : Provider (protocol Item Terminal)) (charge : Charge M)

def packet (allowance : Nat) (pending : Option Item) (accepted : Nat)
    (state : M.State () ()) (terminalAfter : Item → Option Terminal := fun _ => none) :
    Mettapedia.Machines.Cursor.Packet M (client Item Terminal terminalAfter) () :=
  ⟨(),.running allowance pending accepted,state⟩

/-- Independent callback sequencing follows the ownership boundary's branch
order. An already held return is tried before a producer request; successful
acceptance alone spends the allowance. Every callback's post-state is retained.
`terminalAfter` reads a producer-certified marker from the complete return;
it never probes the producer and does not activate the returned payload. -/
def fromCallbacks (allowance : Nat) (pending : Option Item) (accepted : Nat)
    (state : M.State () ()) (terminalAfter : Item → Option Terminal := fun _ => none) :
    Nat × (Result Item Terminal × M.State () ()) :=
  match allowance, pending with
  | 0, pending => (0,⟨⟨none,pending,accepted⟩,state⟩)
  | allowance+1, some item =>
      let decision := M.step state (.accept item)
      match decision.1 with
      | true => match terminalAfter item with
          | some reason =>
              (charge state (.accept item),⟨⟨some reason,none,accepted+1⟩,decision.2⟩)
          | none =>
              let rest := fromCallbacks allowance none (accepted+1) decision.2 terminalAfter
              (charge state (.accept item)+rest.1,rest.2)
      | false => (charge state (.accept item),⟨⟨none,some item,accepted⟩,decision.2⟩)
  | allowance+1, none =>
      let response := M.step state .next
      match response.1 with
      | .paused => (charge state .next,⟨⟨none,none,accepted⟩,response.2⟩)
      | .terminal reason => (charge state .next,⟨⟨some reason,none,accepted⟩,response.2⟩)
      | .returned item =>
          let decision := M.step response.2 (.accept item)
          match decision.1 with
          | true => match terminalAfter item with
              | some reason => (charge state .next+charge response.2 (.accept item),
                  ⟨⟨some reason,none,accepted+1⟩,decision.2⟩)
              | none =>
                  let rest := fromCallbacks allowance none (accepted+1) decision.2 terminalAfter
                  (charge state .next+charge response.2 (.accept item)+rest.1,rest.2)
          | false => (charge state .next+charge response.2 (.accept item),
              ⟨⟨none,some item,accepted⟩,decision.2⟩)
termination_by structural allowance



private theorem advance_stopped (fuel : Nat) (result : Result Item Terminal)
    (state : M.State () ()) (terminalAfter : Item → Option Terminal := fun _ => none) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge (fuel+1)
      ⟨(),Control.stopped result,state⟩ =
        (0,.done ⟨(),result,state⟩) := rfl

private theorem advance_allowance_zero (fuel accepted : Nat) (pending : Option Item)
    (state : M.State () ()) (terminalAfter : Item → Option Terminal := fun _ => none) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge (fuel+1)
      (packet M 0 pending accepted state terminalAfter) =
        (0,.done ⟨(),⟨none,pending,accepted⟩,state⟩) := rfl

private theorem advance_pending (fuel allowance accepted : Nat) (item : Item)
    (state : M.State () ()) (terminalAfter : Item → Option Terminal := fun _ => none) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge (fuel+1)
      (packet M (allowance+1) (some item) accepted state terminalAfter) =
      let decision := M.step state (.accept item)
      let nextControl := match decision.1 with
        | true => match terminalAfter item with
            | none => Control.running allowance none (accepted+1)
            | some reason => Control.stopped ⟨some reason,none,accepted+1⟩
        | false => Control.stopped ⟨none,some item,accepted⟩
      let later := Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge fuel
        ⟨(),nextControl,decision.2⟩
      (charge state (.accept item)+later.1,later.2) := by
  cases response : M.step state (.accept item) with
  | mk decision after =>
      cases decision <;> simp [Mettapedia.Machines.Cursor.advance,packet,client,response]

private theorem advance_poll (fuel allowance accepted : Nat)
    (state : M.State () ()) (terminalAfter : Item → Option Terminal := fun _ => none) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge (fuel+1)
      (packet M (allowance+1) none accepted state terminalAfter) =
      let reply := M.step state .next
      let nextControl := match reply.1 with
        | .returned item => Control.running (allowance+1) (some item) accepted
        | .paused => Control.stopped ⟨none,none,accepted⟩
        | .terminal reason => Control.stopped ⟨some reason,none,accepted⟩
      let later := Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge fuel
        ⟨(),nextControl,reply.2⟩
      (charge state .next+later.1,later.2) := by
  cases response : M.step state .next with
  | mk reply after =>
      cases reply <;> simp [Mettapedia.Machines.Cursor.advance,packet,client,response]

private theorem inspection_allowance_succ (allowance extra : Nat) :
    2*(allowance+1)+extra+1 = (2*allowance+extra+1)+1+1 := by
  simp only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 2 extra]

/-- The independently sequenced callback call instantiates the common cursor.
At most two provider requests are inspected per accepted return, plus a final
client inspection. The result preserves the whole provider post-state and
loan even when the callback refuses. A producer-certified terminal marker is
read from the whole held item only after acceptance, without a second pull.
The marker's validity must be established by the producer; this sequencing
law alone does not certify it. The cursor's `done` finishes this
callback call: a nonterminal result can retain a loan or remain paused, so it
does not assert completion of the surrounding computation. This is a
mathematical realization; physical callback lifetime, protected control-state
access and bounded-word overflow need separate evidence. -/
theorem callback_call_instantiates_common_cursor
    (allowance extra accepted : Nat) (pending : Option Item) (state : M.State () ())
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge
      (2*allowance+extra+1) (packet M allowance pending accepted state terminalAfter) =
      let returned := fromCallbacks M charge allowance pending accepted state terminalAfter
      (returned.1,.done ⟨(),returned.2.1,returned.2.2⟩) := by
  induction allowance generalizing pending accepted state extra with
  | zero =>
      simpa only [Nat.mul_zero, Nat.zero_add, fromCallbacks] using
        advance_allowance_zero M charge extra accepted pending state terminalAfter
  | succ allowance ih =>
      rw [inspection_allowance_succ]
      cases pending with
      | some item =>
          rw [advance_pending (terminalAfter := terminalAfter)]
          cases decision : M.step state (.accept item) with
          | mk acceptedReply after =>
              cases acceptedReply with
              | false =>
                  have halted := advance_stopped M charge (2*allowance+extra+1)
                    ⟨none,some item,accepted⟩ after terminalAfter
                  simp [decision,halted,fromCallbacks]
              | true =>
                  cases final : terminalAfter item with
                  | none =>
                      dsimp only
                      have recursion := ih (extra+1) (accepted+1) none after
                      simpa only [packet,fromCallbacks,decision,final,Nat.add_assoc] using
                        congrArg (fun returned =>
                          (charge state (.accept item)+returned.1,returned.2)) recursion
                  | some reason =>
                      have halted := advance_stopped M charge (2*allowance+extra+1)
                        ⟨some reason,none,accepted+1⟩ after terminalAfter
                      simp [decision,final,halted,fromCallbacks]
      | none =>
          rw [advance_poll (terminalAfter := terminalAfter)]
          cases response : M.step state .next with
          | mk reply after =>
              cases reply with
              | paused =>
                  have halted := advance_stopped M charge (2*allowance+extra+1)
                    ⟨none,none,accepted⟩ after terminalAfter
                  simp [response,halted,fromCallbacks]
              | terminal reason =>
                  have halted := advance_stopped M charge (2*allowance+extra+1)
                    ⟨some reason,none,accepted⟩ after terminalAfter
                  simp [response,halted,fromCallbacks]
              | returned item =>
                  dsimp only
                  change (charge state .next +
                    (Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge
                      (2*allowance+extra+1+1)
                      (packet M (allowance+1) (some item) accepted after terminalAfter)).1,
                    (Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge
                      (2*allowance+extra+1+1)
                      (packet M (allowance+1) (some item) accepted after terminalAfter)).2) = _
                  rw [advance_pending M charge (2*allowance+extra+1)
                    allowance accepted item after terminalAfter]
                  cases decision : M.step after (.accept item) with
                  | mk acceptedReply afterAccept =>
                      cases acceptedReply with
                      | false =>
                          have halted := advance_stopped M charge (2*allowance+extra)
                            ⟨none,some item,accepted⟩ afterAccept terminalAfter
                          simp only [Nat.add_assoc] at halted
                          simp [decision,halted,fromCallbacks,response,Nat.add_assoc]
                      | true =>
                          cases final : terminalAfter item with
                          | none =>
                              have recursion := ih extra (accepted+1) none afterAccept
                              simpa only [packet,fromCallbacks,response,decision,final,Nat.add_assoc] using
                                congrArg (fun returned =>
                                  (charge state .next+charge after (.accept item)+returned.1,
                                    returned.2)) recursion
                          | some reason =>
                              have halted := advance_stopped M charge (2*allowance+extra)
                                ⟨some reason,none,accepted+1⟩ afterAccept terminalAfter
                              simp only [Nat.add_assoc] at halted
                              simp [response,decision,final,halted,fromCallbacks,Nat.add_assoc]

#print axioms callback_call_instantiates_common_cursor

/-- A local provider refinement transports a whole callback call, including
state changed by a refused acceptance. Charges may differ between realizations;
the complete result, pending return and provider post-state must correspond.
The proof reuses the common cursor refinement and the independently recursive
callback realization above. -/
theorem fromCallbacks_transport
    {target : Provider (protocol Item Terminal)} (h : Hom M target)
    (targetCharge : Charge target) (allowance accepted : Nat)
    (pending : Option Item) (state : M.State () ())
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    ((fromCallbacks M charge allowance pending accepted state terminalAfter).2.1,
      h.map (fromCallbacks M charge allowance pending accepted state terminalAfter).2.2) =
      (fromCallbacks target targetCharge allowance pending accepted (h.map state) terminalAfter).2 := by
  have transported := h.advance (client Item Terminal terminalAfter) charge targetCharge
    (2*allowance+0+1) (packet M allowance pending accepted state terminalAfter)
  change h.outcome (client Item Terminal terminalAfter)
      (Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge
        (2*allowance+0+1) (packet M allowance pending accepted state terminalAfter)).2 =
    (Mettapedia.Machines.Cursor.advance target (client Item Terminal terminalAfter) targetCharge
      (2*allowance+0+1) (packet target allowance pending accepted (h.map state) terminalAfter)).2
      at transported
  rw [callback_call_instantiates_common_cursor M charge allowance 0 accepted pending state terminalAfter,
    callback_call_instantiates_common_cursor target targetCharge allowance 0 accepted pending
      (h.map state) terminalAfter] at transported
  simpa only [Hom.outcome, Outcome.mapState, Outcome.done.injEq,
    Sigma.mk.inj_iff, heq_eq_eq, true_and] using transported

/-- A callback implementation's local resource inequalities compose over the
same retained call. A refused callback remains charged and retains the
potential of its actual post-state. This compares the declared resource
meters, independently of the observation equality above. -/
theorem fromCallbacks_amortized
    {target : Provider (protocol Item Terminal)} (h : Hom M target)
    (targetCharge : Charge target) (potential : Potential M)
    (localBound : Amortized h charge targetCharge potential)
    (allowance accepted : Nat) (pending : Option Item) (state : M.State () ())
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    (fromCallbacks M charge allowance pending accepted state terminalAfter).1 +
        potential (fromCallbacks M charge allowance pending accepted state terminalAfter).2.2 ≤
      (fromCallbacks target targetCharge allowance pending accepted (h.map state) terminalAfter).1 +
        potential state := by
  have bounded := advance_amortized (client Item Terminal terminalAfter) h charge targetCharge
    potential localBound (2*allowance+0+1) (packet M allowance pending accepted state terminalAfter)
  change (Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge
        (2*allowance+0+1) (packet M allowance pending accepted state terminalAfter)).1 +
      outcomePotential (client Item Terminal terminalAfter) potential
        (Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge
          (2*allowance+0+1) (packet M allowance pending accepted state terminalAfter)).2 ≤
    (Mettapedia.Machines.Cursor.advance target (client Item Terminal terminalAfter) targetCharge
      (2*allowance+0+1) (packet target allowance pending accepted (h.map state) terminalAfter)).1 +
        potential state at bounded
  rw [callback_call_instantiates_common_cursor M charge allowance 0 accepted pending state terminalAfter,
    callback_call_instantiates_common_cursor target targetCharge allowance 0 accepted pending
      (h.map state) terminalAfter] at bounded
  exact bounded

/-- Transport an already paid callback account without replay. This map keeps
the whole terminal/loan record and the corresponding provider state. -/
def mapCall {target : Provider (protocol Item Terminal)} (h : Hom M target)
    (previous : Nat × (Result Item Terminal × M.State () ())) :
    Nat × (Result Item Terminal × target.State () ()) :=
  (previous.1, previous.2.1, h.map previous.2.2)

theorem fromCallbacks_account_transport
    {target : Provider (protocol Item Terminal)} (h : Hom M target)
    (targetCharge : Charge target)
    (localCharge : ∀ {base index} (state : M.State base index)
      (request : (protocol Item Terminal).Shape base index),
      charge state request = targetCharge (h.map state) request)
    (allowance accepted : Nat) (pending : Option Item) (state : M.State () ())
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    mapCall M h (fromCallbacks M charge allowance pending accepted state terminalAfter) =
      fromCallbacks target targetCharge allowance pending accepted (h.map state) terminalAfter := by
  apply Prod.ext
  · have paid := h.advance_charge (client Item Terminal terminalAfter) charge targetCharge localCharge
      (2*allowance+0+1) (packet M allowance pending accepted state terminalAfter)
    change (Mettapedia.Machines.Cursor.advance M (client Item Terminal terminalAfter) charge
      (2*allowance+0+1) (packet M allowance pending accepted state terminalAfter)).1 =
      (Mettapedia.Machines.Cursor.advance target (client Item Terminal terminalAfter) targetCharge
        (2*allowance+0+1) (packet target allowance pending accepted (h.map state) terminalAfter)).1 at paid
    rw [callback_call_instantiates_common_cursor M charge allowance 0 accepted pending state terminalAfter,
      callback_call_instantiates_common_cursor target targetCharge allowance 0 accepted pending
        (h.map state) terminalAfter] at paid
    exact paid
  · exact fromCallbacks_transport M charge h targetCharge allowance accepted pending state terminalAfter



/-- A terminal call remains inert. A paused call resumes its retained loan and
full provider post-state. This does not restart the producer or erase refusal
side effects. -/
def resumeCall (allowance : Nat)
    (previous : Nat × (Result Item Terminal × M.State () ()))
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    Nat × (Result Item Terminal × M.State () ()) :=
  match previous.2.1.terminal with
  | some _ => previous
  | none =>
      let later := fromCallbacks M charge allowance previous.2.1.pending
        previous.2.1.accepted previous.2.2 terminalAfter
      (previous.1+later.1,later.2)

/-- A worker can be changed at a retained callback boundary when its complete
state has a provider refinement. Both sides resume the held return, rather
than reconstructing the source request or repeating an accepted prefix. -/
theorem resumeCall_transport
    {target : Provider (protocol Item Terminal)} (h : Hom M target)
    (targetCharge : Charge target) (allowance targetSpent : Nat)
    (previous : Nat × (Result Item Terminal × M.State () ()))
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    ((resumeCall M charge allowance previous terminalAfter).2.1,
      h.map (resumeCall M charge allowance previous terminalAfter).2.2) =
      (resumeCall target targetCharge allowance
        (targetSpent, previous.2.1, h.map previous.2.2) terminalAfter).2 := by
  unfold resumeCall
  cases previous.2.1.terminal with
  | some reason => rfl
  | none =>
      exact fromCallbacks_transport M charge h targetCharge allowance
        previous.2.1.accepted previous.2.1.pending previous.2.2 terminalAfter

theorem resumeCall_account_transport
    {target : Provider (protocol Item Terminal)} (h : Hom M target)
    (targetCharge : Charge target)
    (localCharge : ∀ {base index} (state : M.State base index)
      (request : (protocol Item Terminal).Shape base index),
      charge state request = targetCharge (h.map state) request)
    (allowance : Nat) (previous : Nat × (Result Item Terminal × M.State () ()))
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    mapCall M h (resumeCall M charge allowance previous terminalAfter) =
      resumeCall target targetCharge allowance (mapCall M h previous) terminalAfter := by
  unfold mapCall resumeCall
  cases previous.2.1.terminal with
  | some reason => rfl
  | none =>
      exact congrArg (fun later => (previous.1 + later.1, later.2))
        (fromCallbacks_account_transport M charge h targetCharge localCharge allowance
          previous.2.1.accepted previous.2.1.pending previous.2.2 terminalAfter)

#print axioms fromCallbacks_transport
#print axioms resumeCall_transport
#print axioms fromCallbacks_amortized
#print axioms resumeCall_account_transport


/-- Publication allowance bounds successful acknowledgments, independently of
producer inspections and the provider's declared operation charge. -/
theorem fromCallbacks_acceptance_bound (allowance accepted : Nat)
    (pending : Option Item) (state : M.State () ())
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    accepted ≤ (fromCallbacks M charge allowance pending accepted state terminalAfter).2.1.accepted ∧
      (fromCallbacks M charge allowance pending accepted state terminalAfter).2.1.accepted ≤ accepted + allowance := by
  induction allowance generalizing pending accepted state with
  | zero => simp [fromCallbacks]
  | succ allowance ih =>
      cases pending with
      | some item =>
          cases response : M.step state (.accept item) with
          | mk decision after =>
              cases decision with
              | false => simp [fromCallbacks, response]
              | true =>
                  cases final : terminalAfter item with
                  | none =>
                      have bound := ih (accepted+1) none after
                      simp only [fromCallbacks, response, final] at *
                      omega
                  | some reason => simp [fromCallbacks, response, final]
      | none =>
          cases response : M.step state .next with
          | mk reply after =>
              cases reply with
              | paused => simp [fromCallbacks, response]
              | terminal reason => simp [fromCallbacks, response]
              | returned item =>
                  cases acknowledgment : M.step after (.accept item) with
                  | mk decision final =>
                      cases decision with
                      | false => simp [fromCallbacks, response, acknowledgment]
                      | true =>
                          cases marked : terminalAfter item with
                          | none =>
                              have bound := ih (accepted+1) none final
                              simp only [fromCallbacks, response, acknowledgment, marked] at *
                              omega
                          | some reason =>
                              simp [fromCallbacks, response, acknowledgment, marked]

theorem resumeCall_zero (previous : Nat × (Result Item Terminal × M.State () ()))
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    resumeCall M charge 0 previous terminalAfter = previous := by
  rcases previous with ⟨spent,⟨⟨terminal,pending,accepted⟩,state⟩⟩
  cases terminal <;> rfl

/-- Refused work remains paid. Resuming a callback never subtracts its charge. -/
theorem resumeCall_charge_mono (allowance : Nat)
    (previous : Nat × (Result Item Terminal × M.State () ()))
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    previous.1 ≤ (resumeCall M charge allowance previous terminalAfter).1 := by
  unfold resumeCall
  cases previous.2.1.terminal <;> simp

theorem resumeCall_acceptance_bound (allowance : Nat)
    (previous : Nat × (Result Item Terminal × M.State () ()))
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    previous.2.1.accepted ≤ (resumeCall M charge allowance previous terminalAfter).2.1.accepted ∧
      (resumeCall M charge allowance previous terminalAfter).2.1.accepted ≤ previous.2.1.accepted + allowance := by
  unfold resumeCall
  cases previous.2.1.terminal with
  | some reason => simp
  | none =>
      exact fromCallbacks_acceptance_bound M charge allowance previous.2.1.accepted
        previous.2.1.pending previous.2.2 terminalAfter

/-- A private callback task carries cumulative work, its complete loan/terminal
result and the provider's complete post-state. This is the existing snapshot
kernel; native independence and external-effect admission remain obligations. -/
def kernel (Id : Type) (terminalAfter : Item → Option Terminal := fun _ => none) :
    SnapshotBatch.Kernel Unit (Id × Nat) Unit Id
      (Nat × (Result Item Terminal × M.State () ())) :=
  SnapshotBatch.Kernel.fromOwnerAction (fun _ allowance previous =>
    resumeCall M charge allowance previous terminalAfter)

/-- Reordering different owners retains each owner's command sequence. A
stateful refusal prevents replacing that sequence by its total allowance. -/
theorem kernel_interleaving {Id : Type} [DecidableEq Id]
    (pool : Id → Nat × (Result Item Terminal × M.State () ()))
    (first second : List (Id × Nat))
    (same : ∀ owner, first.filter (fun item => decide (item.1 = owner)) =
      second.filter (fun item => decide (item.1 = owner)))
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    (kernel M charge Id terminalAfter).run () (fun _ => ()) pool first =
      (kernel M charge Id terminalAfter).run () (fun _ => ()) pool second :=
  SnapshotBatch.Kernel.run_eq_of_owner_sequences _ _ _ _ _ _ same

/-- One quantum per distinct private owner can be prepared in any exact worker
partition. Publication installs the computed packets without rerunning them. -/
theorem kernel_partitioned {Id : Type} [DecidableEq Id]
    (pool : Id → Nat × (Result Item Terminal × M.State () ()))
    (parts : List (List (Id × Nat))) (schedule : List (Id × Nat))
    (coverage : parts.flatten.Perm schedule) (distinct : (schedule.map Prod.fst).Nodup)
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    (kernel M charge Id terminalAfter).partitioned () (fun _ => ()) pool parts =
      (kernel M charge Id terminalAfter).run () (fun _ => ()) pool schedule :=
  SnapshotBatch.Kernel.partitioned_eq_run _ _ _ _ _ _ coverage distinct

/-- Private worker execution and publication commute with a checked provider
representation change. Refusal state, loans and prior receipts are part of
the transported store, rather than reconstructed from the answer sequence. -/
theorem kernel_batch_transport {Id : Type} [DecidableEq Id]
    {target : Provider (protocol Item Terminal)} (h : Hom M target)
    (targetCharge : Charge target)
    (localCharge : ∀ {base index} (state : M.State base index)
      (request : (protocol Item Terminal).Shape base index),
      charge state request = targetCharge (h.map state) request)
    (pool : Id → Nat × (Result Item Terminal × M.State () ()))
    (schedule : List (Id × Nat))
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    (fun owner => mapCall M h ((kernel M charge Id terminalAfter).batch () (fun _ => ()) pool schedule owner)) =
      (kernel target targetCharge Id terminalAfter).batch () (fun _ => ())
        (fun owner => mapCall M h (pool owner)) schedule := by
  apply SnapshotBatch.Kernel.batch_map
  · intro item
    rfl
  · intro item seed previous
    exact resumeCall_account_transport M charge h targetCharge localCharge item.2 previous terminalAfter

/-- A qualified partition of distinct private owners transports to the
reference run with its complete per-owner states and declared receipts.
This requires ownership separation and exact schedule coverage; an answer
cardinality claim alone provides neither premise. -/
theorem kernel_partitioned_transport {Id : Type} [DecidableEq Id]
    {target : Provider (protocol Item Terminal)} (h : Hom M target)
    (targetCharge : Charge target)
    (localCharge : ∀ {base index} (state : M.State base index)
      (request : (protocol Item Terminal).Shape base index),
      charge state request = targetCharge (h.map state) request)
    (pool : Id → Nat × (Result Item Terminal × M.State () ()))
    (parts : List (List (Id × Nat))) (schedule : List (Id × Nat))
    (coverage : parts.flatten.Perm schedule) (distinct : (schedule.map Prod.fst).Nodup)
    (terminalAfter : Item → Option Terminal := fun _ => none) :
    (fun owner => mapCall M h
      ((kernel M charge Id terminalAfter).partitioned () (fun _ => ()) pool parts owner)) =
      (kernel target targetCharge Id terminalAfter).run () (fun _ => ())
        (fun owner => mapCall M h (pool owner)) schedule := by
  rw [SnapshotBatch.Kernel.partitioned_eq_batch,
    kernel_batch_transport M charge h targetCharge localCharge (terminalAfter := terminalAfter),
    ← SnapshotBatch.Kernel.partitioned_eq_batch]
  exact kernel_partitioned target targetCharge _ parts schedule coverage distinct terminalAfter


/-- The earlier pure finite boundary is an actual provider instance of this
callback protocol. Only its successful consumer update changes its accumulator;
producer inspection counts exhaustion as well as each returned occurrence. -/
abbrev finite (consume : Accumulator → Item → Option Accumulator) :
    Provider (protocol Item Unit) where
  State _ _ := List Item × Accumulator × Nat
  step := fun state request => match request with
    | .next => match state.1 with
        | [] => ⟨.terminal (),⟨[],state.2.1,state.2.2+1⟩⟩
        | item :: remaining => ⟨.returned item,⟨remaining,state.2.1,state.2.2+1⟩⟩
    | .accept item => match consume state.2.1 item with
        | none => ⟨false,state⟩
        | some accumulator => ⟨true,⟨state.1,accumulator,state.2.2⟩⟩

abbrev finiteCharge (consume : Accumulator → Item → Option Accumulator) :
    Charge (finite consume) := fun _ request => match request with
  | .next => 1
  | .accept _ => 0

def finiteResult (consume : Accumulator → Item → Option Accumulator)
    (result : Result Item Unit × (finite consume).State () ()) :
    Stop × OwnedSequence.Packet Item Accumulator :=
  (match result.1.terminal with
    | some _ => .complete
    | none => .paused,
    ⟨result.2.1,result.1.pending,result.2.2.1,result.1.accepted,result.2.2.2⟩)

private theorem prepend_request_account (expense requested : Nat) :
    1+expense+requested = expense+(requested+1) := by
  rw [Nat.add_comm 1 expense,Nat.add_assoc,Nat.add_comm 1 requested]

/-- The generic callback implementation agrees with the pre-existing owned
finite boundary, including duplicate occurrences, retained accumulator, pending
loan, accepted count and complete producer-request account. -/
theorem finite_callbacks_agree_with_owned_sequence
    (consume : Accumulator → Item → Option Accumulator) (allowance : Nat)
    (state : OwnedSequence.Packet Item Accumulator) :
    let actual := fromCallbacks (finite consume) (finiteCharge consume) allowance
      state.pending state.accepted ⟨state.remaining,state.accumulator,state.requested⟩
    (actual.1+state.requested,finiteResult consume actual.2) =
      ((sequence consume allowance state).2.requested,sequence consume allowance state) := by
  induction allowance generalizing state with
  | zero => simp [fromCallbacks,finiteResult,sequence]
  | succ allowance ih =>
      rcases state with ⟨remaining,pending,accumulator,accepted,requested⟩
      cases pending with
      | some item =>
          cases decision : consume accumulator item with
          | none => simp [fromCallbacks,finite,finiteCharge,sequence,finiteResult,decision]
          | some next =>
              simpa [fromCallbacks,finite,finiteCharge,sequence,finiteResult,decision] using
                ih ⟨remaining,none,next,accepted+1,requested⟩
      | none =>
          cases remaining with
          | nil => simp [fromCallbacks,finite,finiteCharge,sequence,finiteResult,Nat.add_comm 1 requested]
          | cons item rest =>
              cases decision : consume accumulator item with
              | none => simp [fromCallbacks,finite,finiteCharge,sequence,finiteResult,decision,Nat.add_comm 1 requested]
              | some next =>
                  simpa only [fromCallbacks,finite,finiteCharge,sequence,finiteResult,decision,
                    Nat.zero_add,Nat.add_zero,prepend_request_account] using
                    ih ⟨rest,none,next,accepted+1,requested+1⟩

namespace CallbackControls

structure Cache where
  remaining : List Nat
  delivered : List Nat
  requested : Nat
  warmed : Bool
  deriving DecidableEq, Repr

/-- Refusing the first callback warms a private cache. A retry can therefore
accept the same held item. Equal items remain distinct producer occurrences. -/
abbrev warming : Provider (protocol Nat String) where
  State _ _ := Cache
  step := fun state request => match request with
    | .next => match state.remaining with
        | [] => ⟨.terminal "complete",{state with requested := state.requested+1}⟩
        | item :: rest => ⟨.returned item,
            {state with remaining := rest, requested := state.requested+1}⟩
    | .accept item =>
        if state.warmed then
          ⟨true,{state with delivered := state.delivered++[item]}⟩
        else ⟨false,{state with warmed := true}⟩

def cold : Cache := ⟨[7,7],[],0,false⟩
def refused : Nat × (Result Nat String × Cache) :=
  ⟨2,⟨⟨none,some 7,0⟩,⟨[7],[],1,true⟩⟩⟩

/-- The alternative callback implementation retains an array window rather
than a list tail. Its refusal state and published occurrences remain private
consumer state, separate from the underlying pull representation. -/
structure WindowCache where
  remaining : Sequence.Slice Nat
  delivered : List Nat
  requested : Nat
  warmed : Bool

abbrev windowWarming : Provider (protocol Nat String) where
  State _ _ := WindowCache
  step := fun state request => match request with
    | .next =>
        let pulled := (Sequence.slices Nat).step (base := ()) (index := ()) state.remaining ()
        let next := {state with remaining := pulled.2, requested := state.requested + 1}
        match pulled.1 with
        | none => ⟨.terminal "complete", next⟩
        | some item => ⟨.returned item, next⟩
    | .accept item =>
        if state.warmed then
          ⟨true,{state with delivered := state.delivered ++ [item]}⟩
        else ⟨false,{state with warmed := true}⟩

/-- The actual array lookup uses the existing slice refinement. Acceptance
and refusal preserve the full private consumer state under that same map. -/
def windowHom : Hom windowWarming warming where
  map state :=
    ⟨(Sequence.sliceHom Nat).map (base := ()) (index := ()) state.remaining, state.delivered, state.requested, state.warmed⟩
  step state request := by
    cases request with
    | accept item =>
        cases warmed : state.warmed <;> simp [windowWarming, warming, warmed]
    | next =>
        have pull := (Sequence.sliceHom Nat).step (base := ()) (index := ()) state.remaining ()
        cases found : (Sequence.slices Nat).step (base := ()) (index := ()) state.remaining () with
        | mk reply after =>
            cases remaining : (Sequence.sliceHom Nat).map (base := ()) (index := ()) state.remaining with
            | nil =>
                simp only [found, remaining, Sequence.tails] at pull
                cases reply with
                | none =>
                    have rest := congrArg (fun pair => pair.2) pull
                    simp [windowWarming, warming, found]
                    exact congrArg (fun items =>
                      (⟨items, state.delivered, state.requested + 1, state.warmed⟩ : Cache)) rest
                | some item => cases congrArg (fun pair => pair.1) pull
            | cons item rest =>
                simp only [found, remaining, Sequence.tails] at pull
                cases reply with
                | none => cases congrArg (fun pair => pair.1) pull
                | some value =>
                    have same := congrArg (fun pair => pair.1) pull
                    have tail := congrArg (fun pair => pair.2) pull
                    cases Option.some.inj same
                    simp [windowWarming, warming, found]
                    exact congrArg (fun items =>
                      (⟨items, state.delivered, state.requested + 1, state.warmed⟩ : Cache)) tail

/-- This instance transports every state and allowance, including windows
whose remaining count extends beyond their backing array. The underlying
slice law determines the actual exhausted view in those cases. -/
theorem window_callback_refines_tail (allowance accepted : Nat) (pending : Option Nat)
    (state : WindowCache) :
    ((fromCallbacks windowWarming (fun _ _ => 1) allowance pending accepted state).2.1,
      windowHom.map
        (fromCallbacks windowWarming (fun _ _ => 1) allowance pending accepted state).2.2) =
      (fromCallbacks warming (fun _ _ => 1) allowance pending accepted (windowHom.map state)).2 :=
  fromCallbacks_transport windowWarming (fun _ _ => 1) windowHom
    (fun _ _ => 1) allowance accepted pending state

theorem changing_representation_after_refusal_keeps_retry_state :
    let initial : WindowCache := ⟨⟨#[99,7,7,42],1,2⟩,[],0,false⟩
    let paused := fromCallbacks windowWarming (fun _ _ => 1) 1 none 0 initial
    resumeCall warming (fun _ _ => 1) 1
      (paused.1, paused.2.1, windowHom.map paused.2.2) =
        ⟨3,⟨⟨none,none,1⟩,⟨[7],[7],1,true⟩⟩⟩ := by decide

/-- Moving only the array window loses the warmed consumer state. Even
though the remaining values agree, the next acceptance decision changes. -/
theorem moving_only_the_window_does_not_refine_resumption :
    let initial : WindowCache := ⟨⟨#[99,7,7,42],1,2⟩,[],0,false⟩
    let paused := fromCallbacks windowWarming (fun _ _ => 1) 1 none 0 initial
    (resumeCall warming (fun _ _ => 1) 1
      (paused.1, paused.2.1, {windowHom.map paused.2.2 with warmed := false})).2.1.accepted ≠
      (resumeCall warming (fun _ _ => 1) 1
        (paused.1, paused.2.1, windowHom.map paused.2.2)).2.1.accepted := by decide

/-- This concrete adapter certifies a last item from the actual list-tail
successor. Refusal still updates the original private cache. The marker is
part of the held return, rather than a second probe of the residual. -/
abbrev finalWarming : Provider (protocol (Nat × Bool) String) where
  State _ _ := Cache
  step := fun state request => match request with
    | .next =>
        let response := warming.step (base := ()) (index := ()) state .next
        match response.1 with
        | .returned item => ⟨.returned (item,response.2.remaining.isEmpty),response.2⟩
        | .paused => ⟨.paused,response.2⟩
        | .terminal reason => ⟨.terminal reason,response.2⟩
    | .accept item => warming.step (base := ()) (index := ()) state (.accept item.1)

def terminalMarker (item : Nat × Bool) : Option String :=
  if item.2 then some "complete" else none

/-- The final marker is derived from an empty successor, not from observing
that one answer has occurred or from a requested determinism annotation. -/
theorem final_marker_has_empty_residual (state : Cache) (item : Nat)
    (marked : (finalWarming.step (base := ()) (index := ()) state .next).1 =
      .returned (item,true)) :
    (finalWarming.step (base := ()) (index := ()) state .next).2.remaining = [] := by
  cases remaining : state.remaining with
  | nil => simp [finalWarming,warming,remaining] at marked
  | cons value rest =>
      cases rest with
      | nil => simp [finalWarming,warming,remaining]
      | cons next tail => simp [finalWarming,warming,remaining] at marked

theorem final_refusal_retains_the_whole_loan :
    fromCallbacks finalWarming (fun _ _ => 1) 4 none 0
      ⟨[7],[],0,false⟩ terminalMarker =
      ⟨2,⟨⟨none,some (7,true),0⟩,⟨[],[],1,true⟩⟩⟩ := rfl

theorem final_retry_finishes_without_polling :
    resumeCall finalWarming (fun _ _ => 1) 4
      (fromCallbacks finalWarming (fun _ _ => 1) 4 none 0
        ⟨[7],[],0,false⟩ terminalMarker) terminalMarker =
      ⟨3,⟨⟨some "complete",none,1⟩,⟨[],[7],1,true⟩⟩⟩ := rfl

theorem accepted_final_resume_is_inert (allowance : Nat) :
    resumeCall finalWarming (fun _ _ => 1) allowance
      (fromCallbacks finalWarming (fun _ _ => 1) 4 none 0
        ⟨[7],[],0,true⟩ terminalMarker) terminalMarker =
      ⟨2,⟨⟨some "complete",none,1⟩,⟨[],[7],1,true⟩⟩⟩ := rfl

theorem equal_payloads_keep_two_final_deliveries :
    fromCallbacks finalWarming (fun _ _ => 1) 4 none 0
      ⟨[7,7],[],0,true⟩ terminalMarker =
      ⟨4,⟨⟨some "complete",none,2⟩,⟨[],[7,7],2,true⟩⟩⟩ := rfl

/-- Sequencing cannot repair an unearned final claim: it would suppress the
second occurrence. The producer's separate final-marker proof is essential. -/
theorem unearned_final_marker_suppresses_an_occurrence :
    let dishonest := fromCallbacks warming (fun _ _ => 1) 4 none 0
      ⟨[7,7],[],0,true⟩ (fun _ => some "complete")
    dishonest.2.1.accepted = 1 ∧ dishonest.2.2.remaining = [7] ∧
      dishonest.2.1.terminal = some "complete" := ⟨rfl,rfl,rfl⟩

#print axioms final_marker_has_empty_residual
#print axioms final_refusal_retains_the_whole_loan
#print axioms final_retry_finishes_without_polling
#print axioms accepted_final_resume_is_inert
#print axioms equal_payloads_keep_two_final_deliveries
#print axioms unearned_final_marker_suppresses_an_occurrence

theorem refusal_keeps_full_poststate :
    fromCallbacks warming (fun _ _ => 1) 1 none 0 cold = refused := rfl

theorem retry_uses_pending_without_repolling :
    resumeCall warming (fun _ _ => 1) 1 refused =
      ⟨3,⟨⟨none,none,1⟩,⟨[7],[7],1,true⟩⟩⟩ := rfl

/-- An allowance split can retry a state-changing refusal, whereas one larger
call stops at that refusal. The pure finite-consumer cone does not license
moving callback effects or replacing this retained state with its input. -/
theorem stateful_refusal_breaks_naive_allowance_add :
    (resumeCall warming (fun _ _ => 1) 1
      (fromCallbacks warming (fun _ _ => 1) 1 none 0 cold)).2.1.accepted ≠
      (fromCallbacks warming (fun _ _ => 1) 2 none 0 cold).2.1.accepted := by decide

theorem duplicate_returns_keep_two_deliveries :
    fromCallbacks warming (fun _ _ => 1) 2 none 0 ⟨[7,7],[],0,true⟩ =
      ⟨4,⟨⟨none,none,2⟩,⟨[],[7,7],2,true⟩⟩⟩ := rfl

theorem terminal_call_never_repolls :
    let completed := fromCallbacks warming (fun _ _ => 1) 1 none 2 ⟨[],[7,7],2,true⟩
    resumeCall warming (fun _ _ => 1) 9 completed =
      ⟨1,⟨⟨some "complete",none,2⟩,⟨[],[7,7],3,true⟩⟩⟩ := rfl

private def privatePool : Nat → Nat × (Result Nat String × Cache) :=
  fun owner => (0,⟨⟨none,none,0⟩, if owner = 0 then cold else {cold with warmed := true}⟩)

private def windowPool : Nat → Nat × (Result Nat String × WindowCache) :=
  fun owner => (0, ⟨⟨none,none,0⟩, ⟨⟨#[99,7,7,42],1,2⟩,[],0,owner != 0⟩⟩)

/-- Two independent callback implementations, with reversed worker placement,
instantiate the common transport theorem. One owner refuses and retains its
warmed state and loan; the other publishes one of two equal occurrences. -/
theorem window_partition_uses_common_transport :
    (fun owner => mapCall windowWarming windowHom
      ((kernel windowWarming (fun _ _ => 1) Nat).partitioned () (fun _ => ())
        windowPool [[(1,1)],[(0,1)]] owner)) =
      (kernel warming (fun _ _ => 1) Nat).run () (fun _ => ()) privatePool [(0,1),(1,1)] := by
  have mapped : (fun owner => mapCall windowWarming windowHom (windowPool owner)) =
      privatePool := by
    funext owner
    by_cases same : owner = 0 <;>
      simp [mapCall, windowHom, windowPool, privatePool, cold, same, Sequence.sliceHom]
  have transported := kernel_partitioned_transport windowWarming (fun _ _ => 1) windowHom
    (fun _ _ => 1) (by intros; rfl) windowPool [[(1,1)],[(0,1)]] [(0,1),(1,1)]
    (by decide) (by decide)
  simpa only [mapped] using transported

theorem partitioned_callbacks_retain_refusal_and_accepted_state :
    let result := (kernel warming (fun _ _ => 1) Nat).partitioned () (fun _ => ())
      privatePool [[(0,1)],[(1,1)]]
    result 0 = refused ∧
      result 1 = ⟨2,⟨⟨none,none,1⟩,⟨[7],[7],1,true⟩⟩⟩ := by decide

/-- Two commands for one owner cannot both read its initial snapshot: the
second command must see the warmed cache and the retained pending return. -/
theorem repeated_owner_batch_loses_refusal_progress :
    let region := kernel warming (fun _ _ => 1) Nat
    (region.batch () (fun _ => ()) privatePool [(0,1),(0,1)] 0).2.1.accepted = 0 ∧
      (region.run () (fun _ => ()) privatePool [(0,1),(0,1)] 0).2.1.accepted = 1 := by decide


theorem grouped_callbacks_retry_without_repolling :
    let result := ((kernel warming (fun _ _ => 1) Nat).grouped () (fun _ => ())).partitioned
      () (fun _ => ()) privatePool [[(0,[(0,1),(0,1)])],[(1,[(1,1)])]]
    result 0 = ⟨3,⟨⟨none,none,1⟩,⟨[7],[7],1,true⟩⟩⟩ ∧
      result 1 = ⟨2,⟨⟨none,none,1⟩,⟨[7],[7],1,true⟩⟩⟩ := by decide

end CallbackControls

#print axioms finite_callbacks_agree_with_owned_sequence
#print axioms fromCallbacks_acceptance_bound
#print axioms resumeCall_zero
#print axioms resumeCall_charge_mono
#print axioms resumeCall_acceptance_bound
#print axioms kernel_interleaving
#print axioms kernel_partitioned
#print axioms kernel_batch_transport
#print axioms kernel_partitioned_transport
#print axioms CallbackControls.partitioned_callbacks_retain_refusal_and_accepted_state
#print axioms CallbackControls.repeated_owner_batch_loses_refusal_progress
#print axioms CallbackControls.grouped_callbacks_retry_without_repolling
#print axioms CallbackControls.stateful_refusal_breaks_naive_allowance_add
#print axioms CallbackControls.window_callback_refines_tail
#print axioms CallbackControls.changing_representation_after_refusal_keeps_retry_state
#print axioms CallbackControls.moving_only_the_window_does_not_refine_resumption
#print axioms CallbackControls.window_partition_uses_common_transport

/-! A retained computation supplies the callback boundary directly. Its
provider state keeps the actual indexed source outcome and consumer context;
there is no materialized list of future returns. -/

namespace Retained

variable {Base : Type} {Index : Base → Type}
    {P : IndexedPolynomial.{0, 0, 0, 0} Base Index}
    {Return : (base : Base) → Index base → Type}
    (source : Provider P) (reader : Client (P := P) (Return := Return))
    (base : Base) (Context : Type)

structure State where
  computation : Nat × Outcome source reader base
  context : Context

variable {Context}
    (sourceCharge : Charge source) (quantum : Nat)
    (isReturn : Finished source (Return := Return) base → Bool)
    (rearm : Finished source (Return := Return) base →
      Mettapedia.Machines.Cursor.Packet source reader base)
    (consume : Context → Finished source (Return := Return) base → Bool × Context)

/-- Acceptance reads the retained source return, rather than reconstructing
it from a payload. Even a refused callback keeps its actual context update. -/
def provider : Provider (protocol (Finished source (Return := Return) base)
    (Finished source (Return := Return) base)) where
  State _ _ := State source reader base Context
  step state request := match request with
    | .next =>
        let later := Mettapedia.Machines.Cursor.resume source reader sourceCharge quantum state.computation
        let next := {state with computation := later}
        match later.2 with
        | .paused _ => ⟨.paused, next⟩
        | .done result =>
            if isReturn result then ⟨.returned result, next⟩ else ⟨.terminal result, next⟩
    | .accept _ => match state.computation.2 with
        | .paused _ => ⟨false, state⟩
        | .done result =>
            if isReturn result then
              let decision := consume state.context result
              ⟨decision.1, ⟨if decision.1 then
                  (state.computation.1, .paused (rearm result)) else state.computation,
                decision.2⟩⟩
            else ⟨false, state⟩

theorem next_retains_outcome (state : State source reader base Context) :
    ((provider source reader base sourceCharge quantum isReturn rearm consume).step
      (base := ()) (index := ()) state .next).2 =
      ⟨Mettapedia.Machines.Cursor.resume source reader sourceCharge quantum state.computation,
        state.context⟩ := by
  cases later : (Mettapedia.Machines.Cursor.resume source reader sourceCharge quantum
    state.computation).2 with
  | paused packet => simp [provider, later]
  | done result => cases returned : isReturn result <;> simp [provider, later, returned]

theorem accept_refusal_keeps_computation
    (state : State source reader base Context)
    (item result : Finished source (Return := Return) base)
    (ready : state.computation.2 = .done result) (returned : isReturn result = true)
    (refused : (consume state.context result).1 = false) :
    ((provider source reader base sourceCharge quantum isReturn rearm consume).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨state.computation, (consume state.context result).2⟩ := by
  simp [provider, ready, returned, refused]

theorem accept_success_rearms_only
    (state : State source reader base Context)
    (item result : Finished source (Return := Return) base)
    (ready : state.computation.2 = .done result) (returned : isReturn result = true)
    (accepted : (consume state.context result).1 = true) :
    ((provider source reader base sourceCharge quantum isReturn rearm consume).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨(state.computation.1, .paused (rearm result)), (consume state.context result).2⟩ := by
  simp [provider, ready, returned, accepted]

theorem accept_preserves_source_charge (state : State source reader base Context)
    (item : Finished source (Return := Return) base) :
    ((provider source reader base sourceCharge quantum isReturn rearm consume).step
      (base := ()) (index := ()) state (.accept item)).2.computation.1 =
      state.computation.1 := by
  cases ready : state.computation.2 with
  | paused packet => simp [provider, ready]
  | done result =>
      cases returned : isReturn result <;> cases accepted : (consume state.context result).1 <;>
        simp [provider, ready, returned, accepted]

/-- Pure scheduler subdivision keeps the complete live callback packet.
This does not combine separate acceptance calls or move authority changes. -/
theorem inspection_split (allowance accepted earlier later : Nat)
    (pending : Option (Finished source (Return := Return) base))
    (state : State source reader base Context)
    (terminalAfter : Finished source (Return := Return) base →
      Option (Finished source (Return := Return) base))
    (charge : Charge (provider source reader base sourceCharge quantum isReturn rearm consume)) :
    let owned := provider source reader base sourceCharge quantum isReturn rearm consume
    Mettapedia.Machines.Cursor.advance owned (client _ _ terminalAfter) charge (earlier + later)
        (packet owned allowance pending accepted state terminalAfter) =
      Mettapedia.Machines.Cursor.resume owned (client _ _ terminalAfter) charge later
        (Mettapedia.Machines.Cursor.advance owned (client _ _ terminalAfter) charge earlier
          (packet owned allowance pending accepted state terminalAfter)) :=
  advance_add _ _ _ _ _ _

end Retained

/-- A local callback invariant lifts through the existing owned sequencer,
including the provider post-state of a refusal. -/
theorem fromCallbacks_invariant (Safe : M.State () () → Prop)
    (kept : ∀ state request, Safe state → Safe (M.step state request).2)
    (allowance accepted : Nat) (pending : Option Item) (state : M.State () ())
    (safe : Safe state) (terminalAfter : Item → Option Terminal := fun _ => none) :
    Safe (fromCallbacks M charge allowance pending accepted state terminalAfter).2.2 := by
  induction allowance generalizing pending accepted state with
  | zero => exact safe
  | succ allowance ih =>
      cases pending with
      | some item =>
          have after := kept state (.accept item) safe
          cases response : M.step state (.accept item) with
          | mk decision next =>
              simp only [response] at after
              cases decision <;> cases final : terminalAfter item <;>
                simp only [fromCallbacks, response, final]
              all_goals first | exact after | exact ih _ _ _ after
      | none =>
          have after := kept state .next safe
          cases response : M.step state .next with
          | mk reply next =>
              simp only [response] at after
              cases reply with
              | paused => simpa only [fromCallbacks, response] using after
              | terminal reason => simpa only [fromCallbacks, response] using after
              | returned item =>
                  have afterAccept := kept next (.accept item) after
                  cases decision : M.step next (.accept item) with
                  | mk answer finalState =>
                      simp only [decision] at afterAccept
                      cases answer <;> cases final : terminalAfter item <;>
                        simp only [fromCallbacks, response, decision, final]
                      all_goals first | exact afterAccept | exact ih _ _ _ afterAccept

#print axioms Retained.accept_refusal_keeps_computation
#print axioms Retained.next_retains_outcome
#print axioms Retained.accept_success_rearms_only
#print axioms Retained.accept_preserves_source_charge
#print axioms Retained.inspection_split
#print axioms fromCallbacks_invariant

/-! A frozen return is either an ordinary batch or one observation carrying
its residual. The existing callback sequencer drains its publication records;
enumerating this finite batch never resumes the saved source. A refused check
may prepare private context, but cannot commit the record or discard its loan.
-/
namespace FrozenPublication

variable {Saved Context Observation : Type}

abbrev State (Saved Item Context : Type) :=
  Saved × OwnedSequence.Packet Item (List Item × Context)

abbrev Call (Saved Item Context : Type) :=
  Nat × (Result Item Unit × State Saved Item Context)

/-- Complete records are retained, including environment, role and conditions
when `Item` is `Returned Term Environment`. The saved source is not a list of
future answers and is never interpreted by this publication provider. -/
def provider (check : Context → Item → Bool × Context) : Provider (protocol Item Unit) where
  State _ _ := State Saved Item Context
  step state request := match request with
    | .next => match state.2.pending with
      | some item => ⟨.returned item, state⟩
      | none => match state.2.remaining with
        | [] => ⟨.terminal (), (state.1, {state.2 with requested := state.2.requested + 1})⟩
        | item :: rest => ⟨.returned item, (state.1, {state.2 with
            remaining := rest, pending := some item, requested := state.2.requested + 1})⟩
    | .accept _ => match state.2.pending with
      | none => ⟨false, state⟩
      | some item =>
          let checked := check state.2.accumulator.2 item
          ⟨checked.1, (state.1, {state.2 with
            pending := if checked.1 then none else some item
            accumulator := (if checked.1 then state.2.accumulator.1 ++ [item]
              else state.2.accumulator.1, checked.2)
            accepted := state.2.accepted + if checked.1 then 1 else 0})⟩

def content (state : State Saved Item Context) : List Item :=
  state.2.accumulator.1 ++ OwnedSequence.undelivered state.2

def start (saved : Saved) (items : List Item) (context : Context) : Call Saved Item Context :=
  (0, ⟨none, none, 0⟩, saved, ⟨items, none, ([], context), 0, 0⟩)

/-- The tags describe result presentation, not another progress protocol.
A closed empty bag has no publication record; an open observation has one. -/
def records : List Item ⊕ Observation → List (Item ⊕ Observation)
  | .inl rows => rows.map Sum.inl
  | .inr observation => [Sum.inr observation]

/-- A paused source supplies no endpoint. A genuine closed batch and a genuine
open stop use the existing return/terminal distinction, retaining the source. -/
def prepare (saved : Saved) (context : Context)
    (reply : NextReply (List Item) Observation) : Option (Call Saved (Item ⊕ Observation) Context) :=
  match reply with
  | .paused => none
  | .returned rows => some (start saved (records (.inl rows)) context)
  | .terminal observation => some (start saved (records (.inr observation)) context)

def run (check : Context → Item → Bool × Context) (allowance : Nat)
    (call : Call Saved Item Context) : Call Saved Item Context :=
  resumeCall (provider check) (fun _ _ => 1) allowance call

/-- Both successful publication and stateful refusal conserve the exact
ordered batch. The internal pending record authenticates acceptance. -/
theorem step_preserves (check : Context → Item → Bool × Context)
    (state : State Saved Item Context) (request : Request Item) :
    ((provider check).step (base := ()) (index := ()) state request).2.1 = state.1 ∧
      content ((provider check).step (base := ()) (index := ()) state request).2 = content state := by
  rcases state with ⟨saved, remaining, pending, ⟨committed, context⟩, accepted, requested⟩
  cases request with
  | next =>
      cases pending with
      | some item => simp [provider, content, OwnedSequence.undelivered]
      | none => cases remaining <;> simp [provider, content, OwnedSequence.undelivered]
  | accept _ =>
      cases pending with
      | none => simp [provider, content, OwnedSequence.undelivered]
      | some item =>
          cases answer : (check context item).1 <;>
            simp [provider, content, OwnedSequence.undelivered, answer, List.append_assoc]

/-- This lifts the concrete publication invariant through the maintained
callback interpreter, including every refused callback's actual post-state. -/
theorem callbacks_preserve (check : Context → Item → Bool × Context)
    (allowance accepted : Nat) (pending : Option Item) (state : State Saved Item Context) :
    let later := fromCallbacks (provider check) (fun _ _ => 1) allowance pending accepted state
    later.2.2.1 = state.1 ∧ content later.2.2 = content state := by
  apply fromCallbacks_invariant (provider check) (fun _ _ => 1)
    (fun later => later.1 = state.1 ∧ content later = content state)
  · intro later request valid
    obtain ⟨source, batch⟩ := step_preserves check later request
    exact ⟨source.trans valid.1, batch.trans valid.2⟩
  · exact ⟨rfl, rfl⟩

theorem run_preserves (check : Context → Item → Bool × Context)
    (allowance : Nat) (call : Call Saved Item Context) :
    (run check allowance call).2.2.1 = call.2.2.1 ∧
      content (run check allowance call).2.2 = content call.2.2 := by
  unfold run resumeCall
  cases stopped : call.2.1.terminal with
  | some reason => exact ⟨rfl, rfl⟩
  | none => exact callbacks_preserve check allowance call.2.1.accepted call.2.1.pending call.2.2

/-- The full source, not just an answer count, is fixed while checked draining
partitions the original records into committed, held and remaining portions. -/
theorem run_partition (check : Context → Item → Bool × Context) (allowance : Nat)
    (saved : Saved) (items : List Item) (context : Context) :
    let later := run check allowance (start saved items context)
    later.2.2.1 = saved ∧
      later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++
        later.2.2.2.remaining = items := by
  simpa [start, content, OwnedSequence.undelivered, List.append_assoc] using
    run_preserves check allowance (start saved items context)

/-- A zero publication grant neither turns a pause into completion nor drops
an already paid source or the consumer's prepared context. -/
theorem run_zero (check : Context → Item → Bool × Context) (call : Call Saved Item Context) :
    run check 0 call = call := resumeCall_zero _ _ _

def schedule (check : Context → Item → Bool × Context) (grants : List Nat)
    (call : Call Saved Item Context) : Call Saved Item Context :=
  grants.foldl (fun previous allowance => run check allowance previous) call

/-- A word of actual grants retains stateful refusals. It is not replaced by
their sum, which could erase the opportunity to retry a prepared context. -/
theorem schedule_preserves (check : Context → Item → Bool × Context)
    (grants : List Nat) (call : Call Saved Item Context) :
    (schedule check grants call).2.2.1 = call.2.2.1 ∧
      content (schedule check grants call).2.2 = content call.2.2 := by
  induction grants generalizing call with
  | nil => exact ⟨rfl, rfl⟩
  | cons grant rest ih =>
      have one := run_preserves check grant call
      have later := ih (run check grant call)
      exact ⟨later.1.trans one.1, later.2.trans one.2⟩

theorem schedule_partition (check : Context → Item → Bool × Context)
    (grants : List Nat) (saved : Saved) (items : List Item) (context : Context) :
    let later := schedule check grants (start saved items context)
    later.2.2.1 = saved ∧
      later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++
        later.2.2.2.remaining = items := by
  simpa [start, content, OwnedSequence.undelivered, List.append_assoc] using
    schedule_preserves check grants (start saved items context)

theorem acceptance_preserves_saved (check : Context → Item → Bool × Context)
    (state : State Saved Item Context) (item : Item) :
    ((provider check).step (base := ()) (index := ()) state (.accept item)).2.1 = state.1 :=
  (step_preserves check state (.accept item)).1

/-- Publication charges are administrative callback charges. Refusal retains
that paid work while the separate saved source account stays fixed. -/
theorem run_charge_mono (check : Context → Item → Bool × Context)
    (allowance : Nat) (call : Call Saved Item Context) :
    call.1 ≤ (run check allowance call).1 :=
  resumeCall_charge_mono (provider check) (fun _ _ => 1) allowance call

namespace Controls

private def first : Returned Nat Nat := ⟨7, 11, .completed, [3]⟩
private def second : Returned Nat Nat := ⟨7, 22, .conditional, [4, 4]⟩
private def warm (ready : Bool) (_ : Returned Nat Nat) : Bool × Bool := (ready, true)

theorem refused_then_retried_records_keep_source_and_roles :
    let initial := start (17, [91, 92]) [first, second] false
    let refused := run warm 1 initial
    let accepted := run warm 1 refused
    let finished := run warm 2 accepted
    refused.2.1.pending = some first ∧ refused.2.2.2.accumulator = ([], true) ∧
      accepted.2.2.2.requested = refused.2.2.2.requested ∧
      finished.2.1.terminal = some () ∧
      finished.2.2.1 = (17, [91, 92]) ∧
      finished.2.2.2.accumulator = ([first, second], true) := by decide

theorem closed_zero_and_one_open_have_different_publication_shapes :
    records (Observation := Nat) (.inl ([] : List Nat)) = [] ∧
      records (Item := Nat) (Observation := Nat) (.inr 0) = [Sum.inr 0] ∧
      prepare (Item := Nat) (Observation := Nat) 9 false .paused = none ∧
      (run (fun (context : Bool) (_ : Nat) => (true, context)) 1
        (start 9 [] false)).2.1.terminal = some () := by decide

theorem returned_empty_collection_is_one_record :
    let value : Returned (List Nat) Nat := ⟨[], 4, .completed, []⟩
    let finished := run (fun (context : Unit) (_ : Returned (List Nat) Nat) => (true, context))
      2 (start 9 [value] ())
    finished.2.1.accepted = 1 ∧ finished.2.2.2.accumulator.1 = [value] := by decide

theorem insufficient_grant_is_not_a_closed_publication :
    let later := run (fun (context : Unit) (_ : Nat) => (true, context))
      1 (start 9 [7, 7] ())
    later.2.1.terminal = none ∧ later.2.2.2.accumulator.1 = [7] ∧
      later.2.2.2.remaining = [7] := by decide

theorem merging_grants_can_lose_a_stateful_retry :
    let initial := start (17, [91, 92]) [first, second] false
    run warm 2 initial ≠ run warm 1 (run warm 1 initial) := by
  intro initial same
  have counts := congrArg
    (fun call : Call (Nat × List Nat) (Returned Nat Nat) Bool => call.2.1.accepted) same
  have impossible : (0 : Nat) = 1 := counts
  cases impossible

end Controls

#print axioms step_preserves
#print axioms callbacks_preserve
#print axioms run_partition
#print axioms run_zero
#print axioms schedule_preserves
#print axioms schedule_partition
#print axioms acceptance_preserves_saved
#print axioms run_charge_mono
#print axioms Controls.refused_then_retried_records_keep_source_and_roles
#print axioms Controls.closed_zero_and_one_open_have_different_publication_shapes
#print axioms Controls.returned_empty_collection_is_one_record
#print axioms Controls.insufficient_grant_is_not_a_closed_publication
#print axioms Controls.merging_grants_can_lose_a_stateful_retry

/-! Preparation is a private callback phase of this same publisher. A proved
incompatible source row is disposed without emitting a value; refusal keeps
the raw loan. Once prepared, the complete record survives an append refusal
and its retry does not repeat preparation. -/
namespace CheckedPreparation

variable {Raw Ready Work Sink Refusal : Type}

structure PreparationContext (Raw Ready Work Sink : Type) where
  work : Work
  sink : Sink
  cached : Option Ready
  resolved : List (Raw × Option Ready)
  attempts : Nat

def initial (work : Work) (sink : Sink) : PreparationContext Raw Ready Work Sink :=
  ⟨work, sink, none, [], 0⟩

/-- A failed append may update its own private context. It retains the
already prepared record and does not add a resolved source occurrence. -/
def appendPrepared (append : Sink → Ready → Bool × Sink)
    (context : PreparationContext Raw Ready Work Sink) (raw : Raw) (ready : Ready) :
    Bool × PreparationContext Raw Ready Work Sink :=
  let checked := append context.sink ready
  (checked.1, {context with
    sink := checked.2
    cached := if checked.1 then none else some ready
    resolved := if checked.1 then context.resolved ++ [(raw, some ready)]
      else context.resolved})

/-- The Boolean acknowledges disposal of a raw candidate, not publication
of a value. `ok none` skips one incompatible candidate; `error` retains it. -/
def check (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink)
    (context : PreparationContext Raw Ready Work Sink) (raw : Raw) :
    Bool × PreparationContext Raw Ready Work Sink :=
  match context.cached with
  | some ready => appendPrepared append context raw ready
  | none =>
      let attempted := prepare context.work raw
      let next := {context with work := attempted.2, attempts := context.attempts + 1}
      match attempted.1 with
      | .error _ => (false, next)
      | .ok none => (true, {next with resolved := next.resolved ++ [(raw, none)]})
      | .ok (some ready) => appendPrepared append next raw ready

/-- Complete records are filtered only by an explicit incompatible verdict,
never by duplicate payloads or by operational refusal. -/
def published (context : PreparationContext Raw Ready Work Sink) : List Ready :=
  context.resolved.filterMap Prod.snd

def skipped (context : PreparationContext Raw Ready Work Sink) : List Raw :=
  context.resolved.filterMap fun row => match row.2 with
    | none => some row.1
    | some _ => none

theorem append_resolved_keys (append : Sink → Ready → Bool × Sink)
    (context : PreparationContext Raw Ready Work Sink) (raw : Raw) (ready : Ready) :
    (appendPrepared append context raw ready).2.resolved.map Prod.fst =
      if (appendPrepared append context raw ready).1
      then context.resolved.map Prod.fst ++ [raw] else context.resolved.map Prod.fst := by
  cases decision : append context.sink ready with
  | mk accepted sink => cases accepted <;> simp [appendPrepared, decision]

theorem check_resolved_keys
    (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink)
    (context : PreparationContext Raw Ready Work Sink) (raw : Raw) :
    (check prepare append context raw).2.resolved.map Prod.fst =
      if (check prepare append context raw).1
      then context.resolved.map Prod.fst ++ [raw] else context.resolved.map Prod.fst := by
  cases cached : context.cached with
  | some ready => simpa [check, cached] using append_resolved_keys append context raw ready
  | none =>
      cases attempted : prepare context.work raw with
      | mk verdict work =>
          cases verdict with
          | error reason => simp [check, cached, attempted]
          | ok result =>
              cases result with
              | none => simp [check, cached, attempted]
              | some ready =>
                  simpa [check, cached, attempted] using append_resolved_keys append
                    {context with work := work, attempts := context.attempts + 1} raw ready

theorem check_resolved_length
    (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink)
    (context : PreparationContext Raw Ready Work Sink) (raw : Raw) :
    (check prepare append context raw).2.resolved.length = context.resolved.length +
      if (check prepare append context raw).1 then 1 else 0 := by
  have keys := congrArg List.length (check_resolved_keys prepare append context raw)
  cases accepted : (check prepare append context raw).1 <;> simpa [accepted] using keys

/-- The existing packet logs all disposed candidates, including incompatible
ones. The callback context separately logs which full records were published. -/
def Coherent (state : State Saved Raw (PreparationContext Raw Ready Work Sink)) : Prop :=
  state.2.accumulator.2.resolved.map Prod.fst = state.2.accumulator.1 ∧
    state.2.accepted = state.2.accumulator.2.resolved.length

theorem step_coherent
    (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink)
    (state : State Saved Raw (PreparationContext Raw Ready Work Sink)) (request : Request Raw)
    (coherent : Coherent state) :
    Coherent ((provider (check prepare append)).step (base := ()) (index := ()) state request).2 := by
  rcases state with ⟨saved, remaining, pending, ⟨handled, context⟩, accepted, requested⟩
  change context.resolved.map Prod.fst = handled ∧ accepted = context.resolved.length at coherent
  cases request with
  | next =>
      cases pending with
      | some raw => simpa [provider, Coherent] using coherent
      | none => cases remaining <;> simpa [provider, Coherent] using coherent
  | accept _ =>
      cases pending with
      | none => simpa [provider, Coherent] using coherent
      | some raw =>
          have keys := check_resolved_keys prepare append context raw
          have length := check_resolved_length prepare append context raw
          cases decision : check prepare append context raw with
          | mk allowed next =>
              cases allowed <;>
                simp_all [provider, Coherent]

theorem callbacks_coherent
    (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink)
    (allowance accepted : Nat) (pending : Option Raw)
    (state : State Saved Raw (PreparationContext Raw Ready Work Sink)) (coherent : Coherent state) :
    Coherent (fromCallbacks (provider (check prepare append)) (fun _ _ => 1)
      allowance pending accepted state).2.2 := by
  apply fromCallbacks_invariant (provider (check prepare append)) (fun _ _ => 1) Coherent
  · intro later request valid
    exact step_coherent prepare append later request valid
  · exact coherent

theorem run_coherent
    (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink) (allowance : Nat)
    (call : Call Saved Raw (PreparationContext Raw Ready Work Sink))
    (coherent : Coherent call.2.2) :
    Coherent (run (check prepare append) allowance call).2.2 := by
  unfold run resumeCall
  cases stopped : call.2.1.terminal with
  | some reason => exact coherent
  | none => exact callbacks_coherent prepare append allowance _ _ _ coherent

theorem schedule_coherent
    (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink) (grants : List Nat)
    (call : Call Saved Raw (PreparationContext Raw Ready Work Sink))
    (coherent : Coherent call.2.2) :
    Coherent (schedule (check prepare append) grants call).2.2 := by
  induction grants generalizing call with
  | nil => exact coherent
  | cons grant rest ih => exact ih _ (run_coherent prepare append grant call coherent)

/-- Every actual grant word conserves the original raw occurrence partition,
the full saved source account, and the distinct disposal/publication accounts. -/
theorem schedule_partition
    (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink) (grants : List Nat)
    (saved : Saved) (items : List Raw) (work : Work) (sink : Sink) :
    let later := schedule (check prepare append) grants (start saved items (initial work sink))
    later.2.2.1 = saved ∧
      later.2.2.2.accumulator.2.resolved.map Prod.fst ++
        later.2.2.2.pending.toList ++ later.2.2.2.remaining = items ∧
      later.2.2.2.accepted = later.2.2.2.accumulator.2.resolved.length := by
  have partition := FrozenPublication.schedule_partition (check prepare append) grants
    saved items (initial work sink)
  have coherent := schedule_coherent prepare append grants (start saved items (initial work sink))
    (by simp [Coherent, start, initial])
  refine ⟨partition.1, ?_, coherent.2⟩
  rw [coherent.1]
  exact partition.2

theorem disposition_counts (context : PreparationContext Raw Ready Work Sink) :
    (published context).length + (skipped context).length = context.resolved.length := by
  suffices ∀ rows : List (Raw × Option Ready),
      (rows.filterMap Prod.snd).length +
        (rows.filterMap fun row => match row.2 with
          | none => some row.1 | some _ => none).length = rows.length by
    exact this context.resolved
  intro rows
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨raw, ready⟩
      cases ready <;> simp_all <;> omega

/-- Appending a cached value never repeats preparation, even if publication
refuses again. The private sink's post-state is retained. -/
theorem cached_refusal_retains_prepared
    (prepare : Work → Raw → Except Refusal (Option Ready) × Work)
    (append : Sink → Ready → Bool × Sink)
    (context : PreparationContext Raw Ready Work Sink) (raw : Raw) (ready : Ready)
    (cached : context.cached = some ready) (refused : (append context.sink ready).1 = false) :
    (check prepare append context raw).1 = false ∧
      (check prepare append context raw).2.cached = some ready ∧
      (check prepare append context raw).2.attempts = context.attempts ∧
      (check prepare append context raw).2.work = context.work ∧
      (check prepare append context raw).2.resolved = context.resolved ∧
      (check prepare append context raw).2.sink = (append context.sink ready).2 := by
  simp [check, cached, appendPrepared, refused]

/-- Bindings use their existing private-slot implementation. Only the
environment is replaced in a ready record; role and conditions stay earned. -/
def bindingPreparation {Key Value Metadata Operation Conflict Term : Type} [DecidableEq Key]
    (checker : Mettapedia.Machines.BindingPublication.Checker Key Value Metadata
      (Conflict ⊕ Refusal) Operation)
    (inventory : List Key) (spare : Nat) (operations : List Operation)
    (row : Returned Term (Mettapedia.Machines.BindingPublication.Environment Key Value Metadata)) :
    Except Refusal (Option (Returned Term
      (Mettapedia.Machines.BindingPublication.Environment Key Value Metadata))) :=
  (Mettapedia.Machines.BindingPublication.CheckedPreparation.run checker row.environment
    inventory spare operations).map (Option.map fun environment => {row with environment := environment})

theorem bindingPreparation_eq_checked_reference
    {Key Value Metadata Operation Conflict Term : Type} [DecidableEq Key]
    (checker : Mettapedia.Machines.BindingPublication.Checker Key Value Metadata
      (Conflict ⊕ Refusal) Operation)
    (inventory : List Key) (spare : Nat) (operations : List Operation)
    (row : Returned Term (Mettapedia.Machines.BindingPublication.Environment Key Value Metadata)) :
    bindingPreparation checker inventory spare operations row =
      (Mettapedia.Machines.BindingPublication.CheckedPreparation.classify
        (Mettapedia.Machines.BindingPublication.sequential checker row.environment operations)).map
          (Option.map fun environment => {row with environment := environment}) := by
  unfold bindingPreparation
  rw [Mettapedia.Machines.BindingPublication.CheckedPreparation.run_eq_sequential]

/-- Replacing private binding preparation by the independent checked-map
reference preserves the entire retained publication call under every actual
grant word, including cache state, skipped rows, sink state and charges. The
reference applies checked writes to logical maps; the target uses slots. -/
theorem binding_schedule_eq_checked_reference
    {Key Value Metadata Operation Conflict Term : Type} [DecidableEq Key]
    (checker : Work → Returned Term
      (Mettapedia.Machines.BindingPublication.Environment Key Value Metadata) →
        Mettapedia.Machines.BindingPublication.Checker Key Value Metadata
          (Conflict ⊕ Refusal) Operation)
    (inventory : List Key) (spare : Nat)
    (operations : Returned Term
      (Mettapedia.Machines.BindingPublication.Environment Key Value Metadata) → List Operation)
    (nextWork : Work → Returned Term
      (Mettapedia.Machines.BindingPublication.Environment Key Value Metadata) → Work)
    (append : Sink → Returned Term
      (Mettapedia.Machines.BindingPublication.Environment Key Value Metadata) → Bool × Sink)
    (grants : List Nat) (saved : Saved)
    (rows : List (Returned Term
      (Mettapedia.Machines.BindingPublication.Environment Key Value Metadata)))
    (work : Work) (sink : Sink) :
    schedule (check (fun state row =>
        (bindingPreparation (checker state row) inventory spare (operations row) row,
          nextWork state row)) append) grants (start saved rows (initial work sink)) =
      schedule (check (fun state row =>
        ((Mettapedia.Machines.BindingPublication.CheckedPreparation.classify
          (Mettapedia.Machines.BindingPublication.sequential (checker state row)
            row.environment (operations row))).map
              (Option.map fun environment => {row with environment := environment}),
          nextWork state row)) append) grants (start saved rows (initial work sink)) := by
  simp_rw [bindingPreparation_eq_checked_reference]

namespace Controls

private def first : Returned Nat Nat := ⟨7, 11, .completed, [3]⟩
private def second : Returned Nat Nat := ⟨7, 22, .conditional, [4, 4]⟩
private def preparing (warm : Bool) (raw : Nat) : Except Unit (Option (Returned Nat Nat)) × Bool :=
  if raw == 0 then (.ok none, warm)
  else if warm then (.ok (some (if raw == 1 then first else second)), warm)
  else (.error (), true)
private def appending (warm : Bool) (_ : Returned Nat Nat) : Bool × Bool := (warm, true)
private def begin : Call (Nat × List Nat) Nat (PreparationContext Nat (Returned Nat Nat) Bool Bool) :=
  start (33, [8, 9]) [0, 1, 2] (initial false false)

theorem incompatible_skip_does_not_drop_compatible_siblings :
    let later := schedule (check preparing appending) [1, 1, 1, 1, 2] begin
    later.2.1.terminal = some () ∧
      published later.2.2.2.accumulator.2 = [first, second] ∧
      skipped later.2.2.2.accumulator.2 = [0] ∧
      later.2.2.2.accepted = 3 ∧ later.2.2.2.accumulator.2.attempts = 4 ∧
      later.2.2.1 = (33, [8, 9]) := by decide

theorem refusal_is_not_incompatibility :
    let later := schedule (check preparing appending) [1, 1] begin
    later.2.1.terminal = none ∧ later.2.1.pending = some 1 ∧
      later.2.2.2.pending = some 1 ∧ later.2.2.2.accumulator.1 = [0] ∧
      later.2.2.2.accumulator.2.resolved = [(0, none)] ∧
      later.2.2.2.remaining = [2] := by decide

theorem append_retry_uses_cache_and_no_source_request :
    let refused := schedule (check preparing appending) [1, 1, 1] begin
    let accepted := run (check preparing appending) 1 refused
    refused.2.2.2.accumulator.2.cached = some first ∧
      accepted.2.2.2.accumulator.2.cached = none ∧
      accepted.2.2.2.accumulator.2.attempts = refused.2.2.2.accumulator.2.attempts ∧
      accepted.2.2.2.requested = refused.2.2.2.requested ∧
      accepted.2.2.1 = refused.2.2.1 ∧
      published accepted.2.2.2.accumulator.2 = [first] := by decide

theorem merging_grants_loses_a_preparation_retry :
    schedule (check preparing appending) [1, 1, 1, 1, 2] begin ≠
      run (check preparing appending) 6 begin := by
  intro same
  have observed := congrArg (fun call : Call (Nat × List Nat) Nat
      (PreparationContext Nat (Returned Nat Nat) Bool Bool) => call.2.2.2.accepted) same
  have impossible : (3 : Nat) = 1 := observed
  cases impossible

private abbrev BindingEnvironment :=
  Mettapedia.Machines.BindingPublication.Environment Nat Nat Nat

private def bindingChecker (warm : Bool) :
    Mettapedia.Machines.BindingPublication.Checker Nat Nat Nat (Unit ⊕ Unit) Nat :=
  fun environment operation =>
    ⟨⟨[(operation, operation + 10)], environment.metadata + 1⟩,
      if operation == 7 then .error (.inl ())
      else if operation == 8 && !warm then .error (.inr ()) else .ok ()⟩

private def bindingPreparing (warm : Bool) (row : Returned Nat BindingEnvironment) :
    Except Unit (Option (Returned Nat BindingEnvironment)) × Bool :=
  (bindingPreparation (bindingChecker warm) [0, 1, 7, 8] 1
    [0, if row.payload == 0 then 7 else 8, 1] row,
    if row.payload == 0 then warm else true)

private def bindingRows : List (Returned Nat BindingEnvironment) :=
  [⟨0, ⟨fun _ => none, 5⟩, .completed, []⟩,
   ⟨7, ⟨fun _ => none, 11⟩, .completed, [3]⟩,
   ⟨7, ⟨fun _ => none, 22⟩, .conditional, [4, 4]⟩]

private def bindingBegin : Call (Nat × List Nat) (Returned Nat BindingEnvironment)
    (PreparationContext (Returned Nat BindingEnvironment) (Returned Nat BindingEnvironment) Bool Unit) :=
  start (55, [13, 13]) bindingRows (initial false ())

/-- This instance uses actual checked private binding writes rather than
supplying an abstract three-way oracle. Equal payloads retain distinct worlds,
result roles and conditions after a skipped conflict and an operational retry. -/
theorem checked_bindings_publish_full_records_after_retry :
    let later := schedule (check bindingPreparing (fun _ _ => (true, ())))
      [1, 1, 3] bindingBegin
    later.2.1.terminal = some () ∧
      (published later.2.2.2.accumulator.2).map (fun row =>
        (row.payload, row.environment.get 0, row.environment.get 8,
          row.environment.get 1, row.environment.metadata, row.form, row.conditions)) =
        [(7, some 10, some 18, some 11, 14, .completed, [3]),
         (7, some 10, some 18, some 11, 25, .conditional, [4, 4])] ∧
      later.2.2.2.accepted = 3 ∧ later.2.2.1 = (55, [13, 13]) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A successful tentative write followed by refused work must neither look
matched nor publish its dirty buffer. Its unvisited suffix remains unchecked. -/
theorem refusal_after_write_preserves_input_and_unvisited_suffix :
    let row : Returned Nat BindingEnvironment := ⟨7, ⟨fun _ => none, 11⟩, .completed, [3]⟩
    bindingPreparation (bindingChecker false) [0, 1, 8] 1 [0, 8, 1] row = .error () ∧
      (Mettapedia.Machines.BindingPublication.privatelyBuild (bindingChecker false)
        (Mettapedia.Machines.BindingPublication.prepare row.environment [0, 1, 8] 1)
          [0, 8, 1]).original.get 0 = none ∧
      Mettapedia.Machines.BindingPublication.checkedPrefix (bindingChecker false)
        row.environment [0, 8, 1] = [0, 8] := by
  exact ⟨rfl, rfl, rfl⟩

end Controls

#print axioms check_resolved_keys
#print axioms step_coherent
#print axioms schedule_partition
#print axioms disposition_counts
#print axioms cached_refusal_retains_prepared
#print axioms bindingPreparation_eq_checked_reference
#print axioms binding_schedule_eq_checked_reference
#print axioms Controls.incompatible_skip_does_not_drop_compatible_siblings
#print axioms Controls.refusal_is_not_incompatibility
#print axioms Controls.append_retry_uses_cache_and_no_source_request
#print axioms Controls.merging_grants_loses_a_preparation_retry
#print axioms Controls.checked_bindings_publish_full_records_after_retry
#print axioms Controls.refusal_after_write_preserves_input_and_unvisited_suffix

end CheckedPreparation

end FrozenPublication

end CallbackBoundary

end OwnedSequence


#print axioms prefix_exact
#print axioms complete_exact
#print axioms resumed_prefix_completes
#print axioms count_without_collection

end Mettapedia.Machines.Cursor.Fold
