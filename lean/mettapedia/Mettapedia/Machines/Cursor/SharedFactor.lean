import Mettapedia.Machines.Cursor.SharedOccurrenceLog
import Mettapedia.Machines.Cursor.PrefixBuffer

/-!
# Caller-aware views of shared ordered answer factors

A view retains its caller and a half-open interval in immutable backing
storage. Consumer positions identify deliveries within that caller's table;
backing positions identify shared payloads. These identities are independent.
The operational cursor indexes backing storage directly. Its decoder is the
existing occurrence log, with a separate position for each consumer.

Contiguous suffixes are one regional factor representation. They preserve bags
and ordered streams as well as sets, and need no per-suffix membership index.
This construction does not admit arbitrary equations, merge choice instances,
or certify the physical cost of a native array operation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SharedFactor

universe u v
variable {Input : Type u} {Value : Type v} {clients : Nat}

structure View (Input : Type u) where
  caller : Input
  start : Nat
  stop : Nat
  completed : Bool
  deriving DecidableEq, Repr

def View.Valid (backing : Array Value) (view : View Input) : Prop :=
  view.start ≤ view.stop ∧ view.stop ≤ backing.size

instance (backing : Array Value) (view : View Input) : Decidable (view.Valid backing) := by
  unfold View.Valid
  infer_instance

def values (backing : Array Value) (view : View Input) : List Value :=
  (backing.extract view.start view.stop).toList

theorem values_full_suffix (backing : Array Value) (view : View Input)
    (terminal : view.stop = backing.size) :
    values backing view = backing.toList.drop view.start := by
  simp only [values, Array.toList_extract, List.extract_eq_take_drop, terminal,
    ← Array.length_toList]
  exact List.take_of_length_le (by simp)

/-- Independent answer records retain the caller's input, even when the
payload interval was selected from another table. -/
def records (backing : Array Value) (view : View Input) : List (Input × Value) :=
  (values backing view).map fun value => (view.caller, value)

def rebase (caller : Input) (child : View Input) : View Input :=
  { child with caller := caller }

@[simp] theorem values_rebase (backing : Array Value) (caller : Input) (child : View Input) :
    values backing (rebase caller child) = values backing child := rfl

theorem records_rebase (backing : Array Value) (caller : Input) (child : View Input) :
    records backing (rebase caller child) =
      (values backing child).map (fun value => (caller, value)) := rfl

@[simp] theorem length_values (backing : Array Value) (view : View Input)
    (valid : view.Valid backing) : (values backing view).length = view.stop - view.start := by
  simp only [values, Array.length_toList, Array.size_extract, Nat.min_eq_left valid.2]

theorem records_getElem? (backing : Array Value) (view : View Input)
    (valid : view.Valid backing) (position : Nat) :
    (records backing view)[position]? =
      if position < view.stop - view.start then
        backing[view.start + position]?.map (fun value => (view.caller, value))
      else none := by
  simp only [records, List.getElem?_map, values, Array.getElem?_toList,
    Array.getElem?_extract, Nat.min_eq_left valid.2]
  split <;> simp

@[simp] theorem length_records (backing : Array Value) (view : View Input)
    (valid : view.Valid backing) :
    (records backing view).length = view.stop - view.start := by
  simp only [records, List.length_map, length_values _ _ valid]

structure State (Input : Type u) (Value : Type v) (clients : Nat) where
  backing : Array Value
  view : View Input
  positions : Fin clients → Option Nat

def Valid (state : State Input Value clients) : Prop :=
  state.view.Valid state.backing ∧
    ∀ client position, state.positions client = some position →
      position ≤ state.view.stop - state.view.start

def decode (state : State Input Value clients) :
    SharedOccurrenceLog.State (Input × Value) clients :=
  ⟨0, records state.backing state.view, state.positions, state.view.completed,
    state.view.stop - state.view.start⟩

/-- Migrate a retained suffix to a smaller immutable backing allocation.
Positions remain relative to the caller's view. Native ownership must keep
the old allocation until all old readers and pending publications release it. -/
def trimBefore (lower : Nat) (state : State Input Value clients) : State Input Value clients :=
  { state with
    backing := state.backing.extract lower state.backing.size
    view := { state.view with start := state.view.start - lower, stop := state.view.stop - lower } }

theorem trimBefore_valid (lower : Nat) (state : State Input Value clients)
    (valid : state.view.Valid state.backing) (before : lower ≤ state.view.start) :
    (trimBefore lower state).view.Valid (trimBefore lower state).backing := by
  simp only [trimBefore, View.Valid, Array.size_extract, Nat.min_self]
  obtain ⟨ordered, bounded⟩ := valid
  constructor <;> omega

/-- The extracted backing and rebased interval retain exactly the original
payloads, including repeated values and their order. -/
theorem trimBefore_values (lower : Nat) (state : State Input Value clients)
    (valid : state.view.Valid state.backing) (before : lower ≤ state.view.start) :
    values (trimBefore lower state).backing (trimBefore lower state).view =
      values state.backing state.view := by
  have start : lower + (state.view.start - lower) = state.view.start := by omega
  have stop : lower + (state.view.stop - lower) = state.view.stop := by
    have := valid.1
    omega
  simp only [trimBefore, values, Array.extract_extract, start, stop,
    Nat.min_eq_left valid.2]

/-- Full occurrence readback survives compaction; completion and all
independent consumer positions remain unchanged. -/
theorem trimBefore_decode (lower : Nat) (state : State Input Value clients)
    (valid : state.view.Valid state.backing) (before : lower ≤ state.view.start) :
    decode (trimBefore lower state) = decode state := by
  have recordsEq : records (trimBefore lower state).backing (trimBefore lower state).view =
      records state.backing state.view := by
    simp only [records, trimBefore_values lower state valid before]
    rfl
  have sizeEq : (state.view.stop - lower) - (state.view.start - lower) =
      state.view.stop - state.view.start := by
    have := valid.1
    omega
  unfold decode
  rw [recordsEq]
  dsimp only [trimBefore]
  rw [sizeEq]

/-- Refuse migration if it would erase part of the retained view or if its
bounds are invalid. Refusal leaves the complete input state available. -/
def compact (lower : Nat) (state : State Input Value clients) : Option (State Input Value clients) :=
  if lower ≤ state.view.start ∧ state.view.Valid state.backing then
    some (trimBefore lower state)
  else none

theorem compact_preserves_readback (lower : Nat) (state next : State Input Value clients)
    (accepted : compact lower state = some next) : decode next = decode state := by
  unfold compact at accepted
  split at accepted
  next permitted =>
    cases Option.some.inj accepted
    exact trimBefore_decode lower state permitted.2 permitted.1
  next refused => simp at accepted

theorem compact_backing_size (lower : Nat) (state : State Input Value clients) :
    (trimBefore lower state).backing.size = state.backing.size - lower := by
  simp [trimBefore]

theorem compact_tail_with_independent_positions :
    ((compact 2 (⟨#[7, 8, 9], ⟨41, 2, 3, true⟩,
      fun client => if client = 0 then some 0 else some 1⟩ : State Nat Nat 2)).map
      fun state => (state.backing.toList, records state.backing state.view,
        state.positions 0, state.positions 1)) =
      some ([9], [(41, 9)], some 0, some 1) := by decide

theorem compact_refuses_live_prefix_loss :
    compact 2 (⟨#[7, 8, 9], ⟨41, 1, 3, true⟩, fun _ => some 0⟩ : State Nat Nat 1) =
      none := by decide

theorem decode_valid (state : State Input Value clients) (valid : Valid state) :
    SharedOccurrenceLog.Valid (decode state) := by
  simp only [SharedOccurrenceLog.Valid, decode, records, List.length_map,
    length_values _ _ valid.1, SharedOccurrenceLog.pastEnd, Nat.zero_add]
  exact ⟨le_refl _, fun client position present => ⟨Nat.zero_le _, valid.2 client position present⟩⟩

def peek (state : State Input Value clients) (client : Fin clients) :
    SharedOccurrenceLog.Reply (Input × Value) :=
  match state.positions client with
  | none => .cancelled
  | some position =>
      if position < state.view.stop - state.view.start then
        match state.backing[state.view.start + position]? with
        | some value => .answer position (state.view.caller, value)
        | none => .invalid
      else if position = state.view.stop - state.view.start then
        if state.view.completed then .completed else .paused
      else .invalid

/-- Direct backing lookup agrees with independently decoded answer records,
including order, duplicates, caller identity and genuine completion. -/
theorem peek_decode (state : State Input Value clients) (client : Fin clients)
    (valid : state.view.Valid state.backing) :
    peek state client = SharedOccurrenceLog.peek (decode state) client := by
  unfold peek SharedOccurrenceLog.peek
  dsimp only [decode]
  cases present : state.positions client with
  | none => rfl
  | some position =>
      simp only [Nat.zero_le, if_true, Nat.sub_zero, records_getElem? _ _ valid,
        SharedOccurrenceLog.pastEnd, length_records _ _ valid, Nat.zero_add]
      by_cases inside : position < state.view.stop - state.view.start
      · simp only [inside, if_true]
        have allocated : state.view.start + position < state.backing.size := by
          have := valid.1
          have := valid.2
          omega
        simp only [getElem?_pos state.backing (state.view.start + position) allocated,
          Option.map_some]
      · simp only [inside, if_false]
        rfl

def setPosition (state : State Input Value clients) (client : Fin clients)
    (position : Option Nat) : State Input Value clients :=
  { state with positions := Function.update state.positions client position }

@[simp] theorem decode_setPosition (state : State Input Value clients)
    (client : Fin clients) (position : Option Nat) :
    decode (setPosition state client position) =
      SharedOccurrenceLog.setPosition (decode state) client position := rfl

def pull (state : State Input Value clients) (client : Fin clients) :
    SharedOccurrenceLog.Reply (Input × Value) × State Input Value clients :=
  match peek state client with
  | .answer position value => (.answer position value, setPosition state client (some (position + 1)))
  | reply => (reply, state)

theorem pull_decode (state : State Input Value clients) (client : Fin clients)
    (valid : state.view.Valid state.backing) :
    ((pull state client).1, decode (pull state client).2) =
      SharedOccurrenceLog.pull (decode state) client := by
  unfold pull SharedOccurrenceLog.pull
  rw [← peek_decode state client valid]
  cases peek state client <;> rfl

theorem pull_preserves_other (state : State Input Value clients) (client other : Fin clients)
    (distinct : other ≠ client) : peek (pull state client).2 other = peek state other := by
  unfold pull
  cases peek state client with
  | answer position value =>
      simp only [peek, setPosition, Function.update_of_ne distinct]
      rfl
  | paused | completed | cancelled | invalid => rfl

def cancel (state : State Input Value clients) (client : Fin clients) :
    State Input Value clients := setPosition state client none

theorem cancel_keeps_other (state : State Input Value clients) (client other : Fin clients)
    (distinct : other ≠ client) : peek (cancel state client) other = peek state other := by
  simp [cancel, peek, setPosition, distinct]
  rfl

def drain : Nat → State Input Value clients → Fin clients →
    List (Nat × (Input × Value)) × State Input Value clients
  | 0, state, _ => ([], state)
  | budget + 1, state, client =>
      match pull state client with
      | (.answer position value, next) =>
          let rest := drain budget next client
          ((position, value) :: rest.1, rest.2)
      | (_, next) => ([], next)

theorem drain_decode (budget : Nat) (state : State Input Value clients) (client : Fin clients)
    (valid : state.view.Valid state.backing) :
    ((drain budget state client).1, decode (drain budget state client).2) =
      SharedOccurrenceLog.drain budget (decode state) client := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      have step := pull_decode state client valid
      have nextValid : (pull state client).2.view.Valid (pull state client).2.backing := by
        unfold pull
        cases peek state client <;> exact valid
      cases selected : pull state client with
      | mk reply next =>
          simp only [selected] at step nextValid
          cases reply with
          | answer position value =>
              simp only [drain, selected, SharedOccurrenceLog.drain, ← step]
              exact congrArg (fun result => ((position, value) :: result.1, result.2))
                (ih next nextValid)
          | paused | completed | cancelled | invalid =>
              simp only [drain, selected, SharedOccurrenceLog.drain, ← step]

theorem drain_answer (budget : Nat) (state : State Input Value clients) (client : Fin clients)
    (position : Nat) (value : Input × Value) (answer : peek state client = .answer position value) :
    drain (budget + 1) state client =
      (let rest := drain budget (setPosition state client (some (position + 1))) client
       ((position, value) :: rest.1, rest.2)) := by
  simp only [drain, pull, answer]

theorem drain_stopped (budget : Nat) (state : State Input Value clients) (client : Fin clients)
    (stopped : ∀ position value, peek state client ≠ .answer position value) :
    drain budget state client = ([], state) := by
  cases budget with
  | zero => rfl
  | succ budget =>
      cases reply : peek state client with
      | answer position value => exact False.elim (stopped position value reply)
      | paused | completed | cancelled | invalid => simp only [drain, pull, reply]

/-- Bounded pause/resume preserves the complete operational residual, not
only a projection of its answers. -/
theorem drain_split (first second : Nat) (state : State Input Value clients) (client : Fin clients) :
    drain (first + second) state client =
      (let earlier := drain first state client
       let later := drain second earlier.2 client
       (earlier.1 ++ later.1, later.2)) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, drain, List.nil_append]
  | succ first ih =>
      cases reply : peek state client with
      | answer position value =>
          rw [Nat.succ_add, drain_answer _ state client position value reply,
            drain_answer first state client position value reply, ih]
          simp only [List.cons_append]
      | paused | completed | cancelled | invalid =>
          have stopped : ∀ p value, peek state client ≠ .answer p value := by simp [reply]
          simp only [drain_stopped _ _ _ stopped, List.nil_append]

/-- A suffix slice is decoded against ordinary list suffixes, independently
of the cursor implementation. -/
theorem suffix_contents (source : List Value) (caller : Input) (start : Nat) :
    records source.toArray ⟨caller, start, source.length, true⟩ =
      (source.drop start).map (fun value => (caller, value)) := by
  simp [records, values, List.extract_eq_take_drop]

private def sample : State Nat Nat 2 :=
  ⟨#[7, 7, 9], ⟨41, 0, 3, true⟩, fun _ => some 0⟩

theorem duplicate_order_and_caller_control :
    (drain 4 sample 0).1 = [(0, (41, 7)), (1, (41, 7)), (2, (41, 9))] := by decide

theorem independent_bookmark_control :
    (pull sample 0).2.positions 0 = some 1 ∧
      (pull sample 0).2.positions 1 = some 0 := by decide

theorem child_record_is_not_caller_record :
    records #[7] (⟨2, 0, 1, true⟩ : View Nat) ≠
      records #[7] (rebase 1 ⟨2, 0, 1, true⟩) := by decide

theorem shared_cursor_loses_an_independent_delivery :
    peek (setPosition sample 1 (some 1)) 1 ≠ peek sample 1 := by decide

theorem absence_is_not_completion :
    peek (⟨#[], ⟨0, 0, 0, false⟩, fun _ => some 0⟩ : State Nat Nat 1) 0 = .paused ∧
    peek (⟨#[], ⟨0, 0, 0, true⟩, fun _ => some 0⟩ : State Nat Nat 1) 0 = .completed := by decide

end Mettapedia.Machines.Cursor.SharedFactor
