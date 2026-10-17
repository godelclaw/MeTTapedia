import Mettapedia.Machines.Cursor.Sequence

/-!
# A retained witness for an existential observation

An existence observer may advance a producer, but it retains the actual reply
and the producer's successor state. The next read delivers that reply without
polling again. Producer state can include an effect world: the laws preserve
that entire state, not only the Boolean answer. Exhaustion is remembered too.

This uses the existing sequence protocol. A native machine's suspension and
failure replies must remain distinct from this protocol's exhaustion. Native
ownership, binding transport and bounded-word arithmetic are separate duties.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.Peek

variable {Item : Type} (producer : Provider (Sequence.protocol Item))

structure State where
  inner : producer.State () ()
  pending : Option Item
  ended : Bool

def start (inner : producer.State () ()) : State producer :=
  ⟨inner, none, false⟩

/-- Deliver a held occurrence first; otherwise poll the producer once. -/
def read (state : State producer) : Option Item × State producer :=
  match state.pending with
  | some item => (some item, { state with pending := none })
  | none =>
      if state.ended then (none, state)
      else
        let reply := producer.step state.inner ()
        (reply.1, ⟨reply.2, none, reply.1.isNone⟩)

/-- A peek retains both the reply and the state after its production. -/
def peek (state : State producer) : Option Item × State producer :=
  let reply := read producer state
  (reply.1, { reply.2 with pending := reply.1 })

/-- The number of underlying producer polls performed by `read` or `peek`. -/
def polls (state : State producer) : Nat :=
  if state.pending.isSome || state.ended then 0 else 1

theorem read_pending (inner : producer.State () ()) (item : Item) (ended : Bool) :
    read producer ⟨inner, some item, ended⟩ =
      (some item, ⟨inner, none, ended⟩) := rfl

theorem peek_pending (inner : producer.State () ()) (item : Item) (ended : Bool) :
    peek producer ⟨inner, some item, ended⟩ =
      (some item, ⟨inner, some item, ended⟩) := rfl

theorem read_exhausted (inner : producer.State () ()) :
    read producer ⟨inner, none, true⟩ = (none, ⟨inner, none, true⟩) := rfl

/-- Arbitrarily many repeated existential observations do not repeat a poll. -/
theorem peek_idempotent (state : State producer) :
    peek producer (peek producer state).2 = peek producer state := by
  rcases state with ⟨inner, pending, ended⟩
  cases pending with
  | some item => rfl
  | none =>
      cases ended with
      | true => rfl
      | false =>
          cases reply : producer.step inner () with
          | mk item next =>
              cases item <;> simp [peek, read, reply]

/-- A read following a peek is exactly one ordinary read, including the
producer's complete successor state. No effect is replayed. -/
theorem read_after_peek (state : State producer) :
    read producer (peek producer state).2 = read producer state := by
  rcases state with ⟨inner, pending, ended⟩
  cases pending with
  | some item => rfl
  | none =>
      cases ended with
      | true => rfl
      | false =>
          cases reply : producer.step inner () with
          | mk item next =>
              cases item <;> simp [peek, read, reply]

theorem polls_after_peek (state : State producer) :
    polls producer (peek producer state).2 = 0 := by
  rcases state with ⟨inner, pending, ended⟩
  cases pending with
  | some item => simp [peek, read, polls]
  | none =>
      cases ended with
      | true => rfl
      | false =>
          cases reply : producer.step inner () with
          | mk item next =>
              cases item <;> simp [peek, read, polls, reply]

/-- Counting physical polls agrees too, independently of the producer's cost
or the amount of work required to produce one answer. -/
theorem peek_then_read_polls (state : State producer) :
    polls producer state + polls producer (peek producer state).2 =
      polls producer state := by
  rw [polls_after_peek, Nat.add_zero]

def buffered : Provider (Sequence.protocol Item) where
  State _ _ := State producer
  step state _ :=
    let reply := read producer state
    ⟨reply.1, reply.2⟩

/-- On the finite reference, peeking observes precisely the first occurrence,
including repeated equal values. -/
theorem finite_peek (items : List Item) :
    (peek (Sequence.tails Item) (start _ items)).1 = items.head? := by
  cases items <;> rfl

namespace Controls

/-- The counter represents an effect at each real producer request. -/
def effectful : Provider (Sequence.protocol Nat) where
  State _ _ := List Nat × Nat
  step state _ := match state.1 with
    | [] => ⟨none, ([], state.2 + 1)⟩
    | item :: rest => ⟨some item, (rest, state.2 + 1)⟩

theorem repeated_peek_effect_once :
    (peek effectful (peek effectful (start effectful ([7, 7], 0))).2).2.inner =
      ([7], 1) := rfl

theorem two_equal_occurrences_remain_two :
    let first := read effectful (peek effectful (start effectful ([7, 7], 0))).2
    let second := read effectful first.2
    first.1 = some 7 ∧ second.1 = some 7 ∧ second.2.inner = ([], 2) := by
  exact ⟨rfl, rfl, rfl⟩

theorem exhaustion_is_not_polled_twice :
    (read effectful (peek effectful (start effectful ([], 0))).2).2.inner =
      ([], 1) := rfl

theorem dropping_witness_changes_next :
    let held := (peek effectful (start effectful ([7, 8], 0))).2
    (read effectful { held with pending := none }).1 ≠
      (read effectful held).1 := by
  decide

theorem restarting_repeats_effect :
    let held := (peek effectful (start effectful ([7, 8], 0))).2
    (read effectful (start effectful ([7, 8], held.inner.2))).2.inner.2 ≠
      (read effectful held).2.inner.2 := by
  decide

end Controls
end Mettapedia.Machines.Cursor.Peek
