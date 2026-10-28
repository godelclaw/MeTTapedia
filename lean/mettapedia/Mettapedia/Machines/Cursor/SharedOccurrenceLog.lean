import Mathlib.Data.Finset.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Basic

/-!
# Independent consumers of a bounded occurrence log

A qualified producer supplies occurrences to one log for a fixed cohort of
consumers. Each consumer keeps an
absolute position, independent of every other position. Cancellation removes
one consumer; trimming drops only the prefix preceding all surviving positions.
Equal payloads remain different occurrences through their absolute positions.
Distinct consumer acknowledgments and cancellation commute with delivery to
other consumers, preserving replies and the complete residual. Publication of
new rows is a separate action: a waiting consumer can observe that publication.
Those positions identify occurrences within this log; producer identity and
source-context qualification remain separate. Appending newly produced answers
does not admit later mutations of the producer's captured source space.

The row limit is explicit. Admission to an open log at that limit returns backpressure with
the log unchanged, allowing the caller to retain the pending producer input.
Completion is separate from temporary absence of an answer. This is one bounded
retention policy, not a choice of defaults for the native evaluator.

These laws concern delivery after producer qualification. They do not license
computation sharing, discover dependencies or continuation roots, account for
payload bytes, or implement publication of borrowed native resources. A native
consumer must publish any retained answer graph before acknowledging its cursor.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SharedOccurrenceLog

universe u v
variable {Value : Type u} {clients : Nat}

structure State (Value : Type u) (clients : Nat) where
  base : Nat
  rows : List Value
  positions : Fin clients → Option Nat
  completed : Bool
  limit : Nat

def pastEnd (state : State Value clients) : Nat := state.base + state.rows.length

def Valid (state : State Value clients) : Prop :=
  state.rows.length ≤ state.limit ∧
    ∀ client position, state.positions client = some position →
      state.base ≤ position ∧ position ≤ pastEnd state

def initial (limit : Nat) : State Value clients :=
  ⟨0, [], fun _ => some 0, false, limit⟩

theorem initial_valid (limit : Nat) : Valid (initial (Value := Value) (clients := clients) limit) := by
  simp [Valid, initial, pastEnd]

inductive Reply (Value : Type u) where
  | answer (position : Nat) (value : Value)
  | paused
  | completed
  | cancelled
  | invalid
  deriving DecidableEq, Repr

def peek (state : State Value clients) (client : Fin clients) : Reply Value :=
  match state.positions client with
  | none => .cancelled
  | some position =>
      if state.base ≤ position then
        match state.rows[position - state.base]? with
        | some value => .answer position value
        | none =>
            if position = pastEnd state then
              if state.completed then .completed else .paused
            else .invalid
      else .invalid

def setPosition (state : State Value clients) (client : Fin clients)
    (position : Option Nat) : State Value clients :=
  { state with positions := Function.update state.positions client position }

@[simp] theorem setPosition_self (state : State Value clients) (client : Fin clients)
    (position : Option Nat) : (setPosition state client position).positions client = position := by
  simp [setPosition]

theorem setPosition_other (state : State Value clients) (client other : Fin clients)
    (position : Option Nat) (distinct : other ≠ client) :
    (setPosition state client position).positions other = state.positions other := by
  simp [setPosition, distinct]

theorem peek_setPosition_other (state : State Value clients) (client other : Fin clients)
    (position : Option Nat) (distinct : other ≠ client) :
    peek (setPosition state client position) other = peek state other := by
  unfold peek
  rw [setPosition_other state client other position distinct]
  rfl

theorem setPosition_existing (state : State Value clients) (client : Fin clients)
    (position : Option Nat) (present : state.positions client = position) :
    setPosition state client position = state := by
  unfold setPosition
  rw [← present, Function.update_eq_self]

theorem setPosition_twice (state : State Value clients) (client : Fin clients)
    (first second : Option Nat) :
    setPosition (setPosition state client first) client second = setPosition state client second := by
  simp only [setPosition, Function.update_idem]

/-- Acknowledgments of distinct consumers affect disjoint positions. The log,
producer completion and retention limit remain common read-only inputs. -/
theorem setPosition_commute (state : State Value clients) (left right : Fin clients)
    (leftPosition rightPosition : Option Nat) (distinct : left ≠ right) :
    setPosition (setPosition state left leftPosition) right rightPosition =
      setPosition (setPosition state right rightPosition) left leftPosition := by
  simp only [setPosition, Function.update_comm distinct]

/-- Acknowledgment follows publication of the returned graph in a native client. -/
def pull (state : State Value clients) (client : Fin clients) :
    Reply Value × State Value clients :=
  match peek state client with
  | .answer position value => (.answer position value, setPosition state client (some (position + 1)))
  | reply => (reply, state)

theorem pull_preserves_other (state : State Value clients) (client other : Fin clients)
    (distinct : other ≠ client) : peek (pull state client).2 other = peek state other := by
  unfold pull
  cases reply : peek state client <;> simp [peek_setPosition_other, distinct]

/-- Updating another consumer can be moved across the actual delivery action;
both the returned occurrence and complete residual are preserved. -/
theorem pull_setPosition_other (state : State Value clients) (left right : Fin clients)
    (position : Option Nat) (distinct : left ≠ right) :
    pull (setPosition state left position) right =
      ((pull state right).1, setPosition (pull state right).2 left position) := by
  unfold pull
  rw [peek_setPosition_other state left right position distinct.symm]
  cases reply : peek state right with
  | answer found value =>
      exact congrArg (Prod.mk (Reply.answer found value))
        (setPosition_commute state left right position (some (found + 1)) distinct)
  | paused => rfl
  | completed => rfl
  | cancelled => rfl
  | invalid => rfl

/-- Distinct consumers may acknowledge in either order. Replies are attached
to their requesting consumers, and equal payloads retain occurrence positions.
This law covers delivery from a fixed log, not concurrent producer publication. -/
theorem pull_commute (state : State Value clients) (left right : Fin clients)
    (distinct : left ≠ right) :
    (let first := pull state left
     let second := pull first.2 right
     (first.1, second.1, second.2)) =
      (let second := pull state right
       let first := pull second.2 left
       (first.1, second.1, first.2)) := by
  unfold pull
  cases first : peek state left <;> cases second : peek state right <;>
    simp [peek_setPosition_other, distinct, distinct.symm, first, second, setPosition_commute]

theorem answer_within (state : State Value clients) (client : Fin clients)
    (position : Nat) (value : Value) (answer : peek state client = .answer position value) :
    state.positions client = some position ∧ state.base ≤ position ∧ position < pastEnd state := by
  cases cursor : state.positions client with
  | none => simp [peek, cursor] at answer
  | some found =>
    by_cases lower : state.base ≤ found
    · cases present : state.rows[found - state.base]? with
      | some item =>
        simp only [peek, cursor, if_pos lower, present] at answer
        have same : found = position := (Reply.answer.inj answer).1
        have available : found - state.base < state.rows.length := by
          by_contra notAvailable
          have absent : state.rows[found - state.base]? = none :=
            List.getElem?_eq_none_iff.mpr (by omega)
          rw [absent] at present
          contradiction
        have upper : found < pastEnd state := by simp only [pastEnd]; omega
        exact ⟨congrArg some same, same ▸ lower, same ▸ upper⟩
      | none =>
        simp only [peek, cursor, if_pos lower, present] at answer
        by_cases last : found = pastEnd state
        · simp only [if_pos last] at answer
          cases done : state.completed <;> simp [done] at answer
        · simp only [if_neg last] at answer
          cases answer
    · simp [peek, cursor, lower] at answer

theorem pull_valid (state : State Value clients) (client : Fin clients) (valid : Valid state) :
    Valid (pull state client).2 := by
  unfold pull
  cases reply : peek state client with
  | answer position value =>
      obtain ⟨cursor, lower, upper⟩ := answer_within state client position value reply
      refine ⟨valid.1, ?_⟩
      intro other p present
      by_cases same : other = client
      · subst other
        have eq : p = position + 1 := by simpa using present.symm
        subst p
        simp only [pastEnd] at upper
        change state.base ≤ position + 1 ∧ position + 1 ≤ pastEnd state
        simp only [pastEnd]
        omega
      · have old : state.positions other = some p := by
          simpa [setPosition, same] using present
        simpa [setPosition, pastEnd] using valid.2 other p old
  | paused => exact valid
  | completed => exact valid
  | cancelled => exact valid
  | invalid => exact valid

theorem valid_peek_is_not_invalid (state : State Value clients) (client : Fin clients)
    (valid : Valid state) : peek state client ≠ .invalid := by
  cases cursor : state.positions client with
  | none => simp [peek, cursor]
  | some position =>
      obtain ⟨lower, upper⟩ := valid.2 client position cursor
      simp only [peek, cursor, if_pos lower]
      cases row : state.rows[position - state.base]? with
      | some value => simp
      | none =>
          have absent := List.getElem?_eq_none_iff.mp row
          have atEnd : position = pastEnd state := by
            simp only [pastEnd] at upper ⊢
            omega
          rw [if_pos atEnd]
          cases state.completed <;> simp

def cancel (state : State Value clients) (client : Fin clients) : State Value clients :=
  setPosition state client none

theorem cancel_valid (state : State Value clients) (client : Fin clients) (valid : Valid state) :
    Valid (cancel state client) := by
  refine ⟨valid.1, ?_⟩
  intro other p present
  by_cases same : other = client
  · subst other
    simp [cancel, setPosition] at present
  · have old : state.positions other = some p := by simpa [cancel, setPosition, same] using present
    simpa [cancel, setPosition, pastEnd] using valid.2 other p old

theorem cancel_preserves_other (state : State Value clients) (client other : Fin clients)
    (distinct : other ≠ client) : peek (cancel state client) other = peek state other :=
  peek_setPosition_other state client other none distinct

/-- Cancelling one consumer commutes with delivery to a distinct consumer.
It does not revoke that other consumer's returned occurrence or cursor. -/
theorem cancel_pull_other (state : State Value clients) (left right : Fin clients)
    (distinct : left ≠ right) :
    pull (cancel state left) right =
      ((pull state right).1, cancel (pull state right).2 left) :=
  pull_setPosition_other state left right none distinct

/-- The largest removable prefix boundary, capped at the existing log end. -/
def cutoff (state : State Value clients) : Nat :=
  Finset.univ.fold min (pastEnd state) (fun client => (state.positions client).getD (pastEnd state))

theorem cutoff_le_end (state : State Value clients) : cutoff state ≤ pastEnd state := by
  exact (Finset.fold_min_le (pastEnd state)).mpr (Or.inl le_rfl)

theorem cutoff_le_position (state : State Value clients) (client : Fin clients) (position : Nat)
    (present : state.positions client = some position) : cutoff state ≤ position := by
  apply (Finset.fold_min_le position).mpr
  exact Or.inr ⟨client, Finset.mem_univ _, by simp [present]⟩

theorem base_le_cutoff (state : State Value clients) (valid : Valid state) : state.base ≤ cutoff state := by
  apply (Finset.le_fold_min state.base).mpr
  refine ⟨by simp [pastEnd], ?_⟩
  intro client member
  cases present : state.positions client with
  | none => simp [pastEnd]
  | some position => simpa using (valid.2 client position present).1

theorem cutoff_maximal (state : State Value clients) (boundary : Nat)
    (endBound : boundary ≤ pastEnd state)
    (allPositions : ∀ client position, state.positions client = some position → boundary ≤ position) :
    boundary ≤ cutoff state := by
  apply (Finset.le_fold_min boundary).mpr
  refine ⟨endBound, ?_⟩
  intro client member
  cases present : state.positions client with
  | none => simpa using endBound
  | some position => simpa using allPositions client position present

def trim (state : State Value clients) : State Value clients :=
  { state with base := cutoff state, rows := state.rows.drop (cutoff state - state.base) }

theorem trim_end (state : State Value clients) (valid : Valid state) :
    pastEnd (trim state) = pastEnd state := by
  have lower := base_le_cutoff state valid
  have upper := cutoff_le_end state
  simp only [pastEnd] at upper ⊢
  simp only [trim, List.length_drop]
  omega

theorem trim_valid (state : State Value clients) (valid : Valid state) : Valid (trim state) := by
  refine ⟨?_, ?_⟩
  · simp only [trim, List.length_drop]
    exact Nat.le_trans (Nat.sub_le _ _) valid.1
  · intro client position present
    exact ⟨cutoff_le_position state client position present,
      by rw [trim_end state valid]; exact (valid.2 client position present).2⟩

theorem trim_lookup (state : State Value clients) (position : Nat) (valid : Valid state)
    (retained : cutoff state ≤ position) :
    (trim state).rows[position - (trim state).base]? = state.rows[position - state.base]? := by
  have lower := base_le_cutoff state valid
  simp only [trim, List.getElem?_drop]
  congr 1
  omega

theorem trim_preserves_peek (state : State Value clients) (client : Fin clients) (valid : Valid state) :
    peek (trim state) client = peek state client := by
  cases present : state.positions client with
  | none => simp [peek, trim, present]
  | some position =>
      have lower := (valid.2 client position present).1
      have retained := cutoff_le_position state client position present
      have rows := trim_lookup state position valid retained
      have newCursor : (trim state).positions client = some position := present
      have newLower : (trim state).base ≤ position := retained
      simp only [peek, newCursor, present, if_pos lower, if_pos newLower]
      rw [rows, trim_end state valid]
      rfl

theorem cancel_trim_preserves_other (state : State Value clients) (client other : Fin clients)
    (valid : Valid state) (distinct : other ≠ client) :
    peek (trim (cancel state client)) other = peek state other := by
  rw [trim_preserves_peek _ _ (cancel_valid state client valid)]
  exact cancel_preserves_other state client other distinct

theorem trim_row_count (state : State Value clients) (valid : Valid state) :
    (trim state).rows.length = pastEnd state - cutoff state := by
  have lower := base_le_cutoff state valid
  have upper := cutoff_le_end state
  simp only [pastEnd] at upper ⊢
  simp only [trim, List.length_drop]
  omega

theorem pinned_consumer_prevents_reclamation (state : State Value clients)
    (client : Fin clients) (valid : Valid state) (pinned : state.positions client = some state.base) :
    (trim state).base = state.base ∧ (trim state).rows = state.rows := by
  have same : cutoff state = state.base :=
    Nat.le_antisymm (cutoff_le_position state client state.base pinned) (base_le_cutoff state valid)
  simp [trim, same]

/-- An inactive consumer has no unread rows; an active one sees its whole
remaining suffix in the producer's occurrence order. -/
def unread (state : State Value clients) (client : Fin clients) : List Value :=
  match state.positions client with
  | none => []
  | some position => state.rows.drop (position - state.base)

theorem unread_setPosition_other (state : State Value clients) (client other : Fin clients)
    (position : Option Nat) (distinct : other ≠ client) :
    unread (setPosition state client position) other = unread state other := by
  unfold unread
  rw [setPosition_other state client other position distinct]
  rfl

theorem answer_unread (state : State Value clients) (client : Fin clients)
    (position : Nat) (value : Value) (answer : peek state client = .answer position value) :
    unread state client = value :: unread (setPosition state client (some (position + 1))) client := by
  obtain ⟨cursor, lower, upper⟩ := answer_within state client position value answer
  have available : position - state.base < state.rows.length := by
    simp only [pastEnd] at upper
    omega
  have same : state.rows[position - state.base] = value := by
    simpa only [peek, cursor, if_pos lower, List.getElem?_eq_getElem available,
      Reply.answer.injEq, true_and] using answer
  simp only [unread, cursor, setPosition_self]
  change state.rows.drop (position - state.base) =
    value :: state.rows.drop (position + 1 - state.base)
  rw [List.drop_eq_getElem_cons available, same]
  congr 2
  omega

theorem pull_unread_subset (state : State Value clients) (client other : Fin clients) :
    unread (pull state client).2 other ⊆ unread state other := by
  cases reply : peek state client with
  | answer position value =>
      simp only [pull, reply]
      by_cases same : other = client
      · subst other
        rw [answer_unread state client position value reply]
        intro item present
        exact List.mem_cons.mpr (Or.inr present)
      · rw [unread_setPosition_other state client other _ same]
        exact List.Subset.refl _
  | paused => simp only [pull, reply]; exact List.Subset.refl _
  | completed => simp only [pull, reply]; exact List.Subset.refl _
  | cancelled => simp only [pull, reply]; exact List.Subset.refl _
  | invalid => simp only [pull, reply]; exact List.Subset.refl _

theorem trim_preserves_unread (state : State Value clients) (client : Fin clients)
    (valid : Valid state) : unread (trim state) client = unread state client := by
  cases present : state.positions client with
  | none => simp [unread, trim, present]
  | some position =>
      have lower := base_le_cutoff state valid
      have retained := cutoff_le_position state client position present
      have newCursor : (trim state).positions client = some position := present
      simp only [unread, present, newCursor]
      change (state.rows.drop (cutoff state - state.base)).drop (position - cutoff state) =
        state.rows.drop (position - state.base)
      rw [List.drop_drop]
      congr 1
      omega

theorem no_consumers_releases_all_rows (state : State Value clients) (valid : Valid state)
    (cancelled : ∀ client, state.positions client = none) : (trim state).rows = [] := by
  have endCut : cutoff state = pastEnd state := by
    apply Nat.le_antisymm (cutoff_le_end state)
    exact cutoff_maximal state (pastEnd state) le_rfl (by
      intro client position present
      rw [cancelled client] at present
      cases present)
  have length : (trim state).rows.length = 0 := by
    rw [trim_row_count state valid, endCut, Nat.sub_self]
  exact List.length_eq_zero_iff.mp length

inductive Admission where
  | accepted
  | backpressure
  | completed
  deriving DecidableEq, Repr

/-- A refused input remains the caller's pending input; no earlier row is evicted. -/
def append (state : State Value clients) (value : Value) : Admission × State Value clients :=
  if state.completed then (.completed, state)
  else if state.rows.length < state.limit then
    (.accepted, { state with rows := state.rows ++ [value] })
  else (.backpressure, state)

theorem append_valid (state : State Value clients) (value : Value) (valid : Valid state) :
    Valid (append state value).2 := by
  unfold append
  split
  · exact valid
  · split
    · rename_i space
      refine ⟨by simp; omega, ?_⟩
      intro client position present
      obtain ⟨lower, upper⟩ := valid.2 client position present
      simp only [pastEnd, List.length_append, List.length_singleton] at upper ⊢
      exact ⟨lower, by omega⟩
    · exact valid

theorem full_log_preserves_residual (state : State Value clients) (value : Value)
    (pending : state.completed = false) (full : state.limit ≤ state.rows.length) :
    append state value = (.backpressure, state) := by
  simp [append, pending, Nat.not_lt.mpr full]

theorem completed_log_refuses_append (state : State Value clients) (value : Value)
    (complete : state.completed = true) : append state value = (.completed, state) := by
  simp [append, complete]

theorem append_resumes_waiting_consumer (state : State Value clients) (client : Fin clients)
    (value : Value) (pending : state.completed = false) (room : state.rows.length < state.limit)
    (waiting : state.positions client = some (pastEnd state)) :
    peek (append state value).2 client = .answer (pastEnd state) value := by
  have admitted : append state value =
      (.accepted, { state with rows := state.rows ++ [value] }) := by simp [append, pending, room]
  have lower : state.base ≤ pastEnd state := by simp [pastEnd]
  have index : pastEnd state - state.base = state.rows.length := by simp [pastEnd]
  have row : (state.rows ++ [value])[pastEnd state - state.base]? = some value := by
    rw [index, List.getElem?_append_right le_rfl]
    simp
  rw [admitted]
  simp only [peek, waiting, if_pos lower, row]

/-- Extending the retained suffix preserves an already buffered occurrence.
Completion and retention limits may change; the cursor and base must still
refer to the same immutable prefix. This does not cover a waiting cursor. -/
theorem extension_preserves_prior_answer (state next : State Value clients)
    (client : Fin clients) (suffix : List Value) (position : Nat) (value : Value)
    (sameBase : next.base = state.base)
    (sameCursor : next.positions client = state.positions client)
    (extended : next.rows = state.rows ++ suffix)
    (answer : peek state client = .answer position value) :
    peek next client = .answer position value := by
  obtain ⟨cursor, lower, upper⟩ := answer_within state client position value answer
  have available : position - state.base < state.rows.length := by
    simp only [pastEnd] at upper
    omega
  have retained : (state.rows ++ suffix)[position - state.base]? =
      state.rows[position - state.base]? := List.getElem?_append_left available
  simp only [peek, sameCursor, cursor, sameBase, if_pos lower, extended, retained]
  simp only [peek, cursor, if_pos lower] at answer
  cases found : state.rows[position - state.base]? with
  | some old => simpa only [found] using answer
  | none =>
      have missing := List.getElem?_eq_none_iff.mp found
      omega

theorem append_preserves_prior_answer (state : State Value clients) (client : Fin clients)
    (value item : Value) (position : Nat) (answer : peek state client = .answer position item) :
    peek (append state value).2 client = .answer position item := by
  unfold append
  split
  · exact answer
  · split
    · exact extension_preserves_prior_answer state _ client [value] position item
        rfl rfl rfl answer
    · exact answer

def complete (state : State Value clients) : State Value clients := { state with completed := true }

theorem complete_valid (state : State Value clients) (valid : Valid state) : Valid (complete state) := valid

theorem peek_at_end (state : State Value clients) (client : Fin clients)
    (cursor : state.positions client = some (pastEnd state)) :
    peek state client = if state.completed then .completed else .paused := by
  have lower : state.base ≤ pastEnd state := by simp [pastEnd]
  have missing : state.rows[pastEnd state - state.base]? = none := by
    apply List.getElem?_eq_none_iff.mpr
    simp [pastEnd]
  simp only [peek, cursor, if_pos lower, missing, ite_true]

/-- Bounded observation uses the actual cursor operation and stops at its first
non-answer. It never changes a paused, completed or cancelled residual. -/
def drain : Nat → State Value clients → Fin clients → List (Nat × Value) × State Value clients
  | 0, state, _ => ([], state)
  | budget + 1, state, client =>
      match pull state client with
      | (.answer position value, next) =>
          let rest := drain budget next client
          ((position, value) :: rest.1, rest.2)
      | (_, next) => ([], next)

theorem drain_answer (budget : Nat) (state : State Value clients) (client : Fin clients)
    (position : Nat) (value : Value) (answer : peek state client = .answer position value) :
    drain (budget + 1) state client =
      (let rest := drain budget (setPosition state client (some (position + 1))) client
       ((position, value) :: rest.1, rest.2)) := by
  simp only [drain, pull, answer]

theorem drain_stopped (budget : Nat) (state : State Value clients) (client : Fin clients)
    (stopped : ∀ position value, peek state client ≠ .answer position value) :
    drain budget state client = ([], state) := by
  cases budget with
  | zero => rfl
  | succ budget =>
      cases reply : peek state client with
      | answer position value => exact False.elim (stopped position value reply)
      | paused => simp only [drain, pull, reply]
      | completed => simp only [drain, pull, reply]
      | cancelled => simp only [drain, pull, reply]
      | invalid => simp only [drain, pull, reply]

/-- Reference enumeration numbers each stored row, including equal payloads. -/
def numberFrom (position : Nat) : List Value → List (Nat × Value)
  | [] => []
  | value :: rest => (position, value) :: numberFrom (position + 1) rest

@[simp] theorem numberFrom_length (position : Nat) (values : List Value) :
    (numberFrom position values).length = values.length := by
  induction values generalizing position with
  | nil => rfl
  | cons value rest ih => simp only [numberFrom, List.length_cons, ih]

/-- Cursor execution agrees with independently enumerating the unread suffix;
the complete residual differs only in this consumer's acknowledged position. -/
theorem drain_spec (budget : Nat) (state : State Value clients) (client : Fin clients)
    (position : Nat) (present : state.positions client = some position)
    (lower : state.base ≤ position) :
    (drain budget state client).1 =
        (numberFrom position (state.rows.drop (position - state.base))).take budget ∧
      (drain budget state client).2 = setPosition state client
        (some (position + min budget (state.rows.drop (position - state.base)).length)) := by
  induction budget generalizing state position with
  | zero =>
      simp only [drain, List.take_zero, Nat.zero_min, Nat.add_zero, true_and]
      exact (setPosition_existing state client (some position) present).symm
  | succ budget ih =>
      cases suffix : state.rows.drop (position - state.base) with
      | nil =>
          have missing : state.rows[position - state.base]? = none := by
            have head : (state.rows.drop (position - state.base))[0]? = none := by rw [suffix]; rfl
            simpa only [List.getElem?_drop, Nat.add_zero] using head
          have stopped : ∀ p value, peek state client ≠ .answer p value := by
            intro p value
            simp only [peek, present, if_pos lower, missing]
            split
            · split <;> simp
            · simp
          rw [drain_stopped _ _ _ stopped]
          simp only [numberFrom, List.take_nil, List.length_nil, Nat.min_zero,
            Nat.add_zero, true_and]
          exact (setPosition_existing state client (some position) present).symm
      | cons value rest =>
          have head : state.rows[position - state.base]? = some value := by
            have first : (state.rows.drop (position - state.base))[0]? = some value := by
              rw [suffix]; rfl
            simpa only [List.getElem?_drop, Nat.add_zero] using first
          have answer : peek state client = .answer position value := by
            simp only [peek, present, if_pos lower, head]
          have tail : state.rows.drop (position + 1 - state.base) = rest := by
            calc
              state.rows.drop (position + 1 - state.base) =
                  (state.rows.drop (position - state.base)).drop 1 := by
                    rw [List.drop_drop]
                    congr 1
                    omega
              _ = rest := by rw [suffix]; rfl
          have next := ih (setPosition state client (some (position + 1))) (position + 1)
            (setPosition_self _ _ _) (by change state.base ≤ position + 1; omega)
          change (drain budget (setPosition state client (some (position + 1))) client).1 =
              (numberFrom (position + 1) (state.rows.drop (position + 1 - state.base))).take budget ∧
            (drain budget (setPosition state client (some (position + 1))) client).2 =
              setPosition (setPosition state client (some (position + 1))) client
                (some (position + 1 + min budget
                  (state.rows.drop (position + 1 - state.base)).length)) at next
          rw [tail] at next
          rw [drain_answer budget state client position value answer]
          constructor
          · simp only [next.1, numberFrom, List.take_succ_cons]
          · rw [next.2, setPosition_twice]
            simp only [List.length_cons, Nat.succ_min_succ]
            congr 2
            omega

theorem drain_valid (budget : Nat) (state : State Value clients) (client : Fin clients)
    (valid : Valid state) : Valid (drain budget state client).2 := by
  induction budget generalizing state with
  | zero => exact valid
  | succ budget ih =>
      cases reply : peek state client with
      | answer position value =>
          rw [drain_answer budget state client position value reply]
          apply ih
          have next := pull_valid state client valid
          simpa only [pull, reply] using next
      | paused => simpa only [drain, pull, reply] using valid
      | completed => simpa only [drain, pull, reply] using valid
      | cancelled => simpa only [drain, pull, reply] using valid
      | invalid => simpa only [drain, pull, reply] using valid

theorem drain_preserves_other (budget : Nat) (state : State Value clients)
    (client other : Fin clients) (distinct : other ≠ client) :
    peek (drain budget state client).2 other = peek state other := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      cases reply : peek state client with
      | answer position value =>
          rw [drain_answer budget state client position value reply]
          rw [ih, peek_setPosition_other state client other _ distinct]
      | paused => simp only [drain, pull, reply]
      | completed => simp only [drain, pull, reply]
      | cancelled => simp only [drain, pull, reply]
      | invalid => simp only [drain, pull, reply]

theorem drain_split (first second : Nat) (state : State Value clients) (client : Fin clients) :
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
      | paused =>
          have stopped : ∀ p value, peek state client ≠ .answer p value := by simp [reply]
          simp only [drain_stopped _ _ _ stopped, List.nil_append]
      | completed =>
          have stopped : ∀ p value, peek state client ≠ .answer p value := by simp [reply]
          simp only [drain_stopped _ _ _ stopped, List.nil_append]
      | cancelled =>
          have stopped : ∀ p value, peek state client ≠ .answer p value := by simp [reply]
          simp only [drain_stopped _ _ _ stopped, List.nil_append]
      | invalid =>
          have stopped : ∀ p value, peek state client ≠ .answer p value := by simp [reply]
          simp only [drain_stopped _ _ _ stopped, List.nil_append]

theorem drain_trim_trace (budget : Nat) (state : State Value clients) (client : Fin clients)
    (valid : Valid state) : (drain budget (trim state) client).1 = (drain budget state client).1 := by
  cases present : state.positions client with
  | none =>
      have old : ∀ p value, peek state client ≠ .answer p value := by simp [peek, present]
      have new : ∀ p value, peek (trim state) client ≠ .answer p value := by
        rw [trim_preserves_peek state client valid]
        exact old
      rw [drain_stopped _ _ _ old, drain_stopped _ _ _ new]
  | some position =>
      have old := drain_spec budget state client position present (valid.2 client position present).1
      have new := drain_spec budget (trim state) client position present
        (cutoff_le_position state client position present)
      rw [old.1, new.1]
      have suffix := trim_preserves_unread state client valid
      have newCursor : (trim state).positions client = some position := present
      simpa only [unread, present, newCursor] using
        congrArg (fun rows => (numberFrom position rows).take budget) suffix

/-- Replay the returned value and keep the occurrence position. -/
def Reply.map {Other : Type u} (f : Value → Other) : Reply Value → Reply Other
  | .answer position value => .answer position (f value)
  | .paused => .paused
  | .completed => .completed
  | .cancelled => .cancelled
  | .invalid => .invalid

/-- Map every retained occurrence value. Base, cursors, completion and the row
limit stay, so an absolute position still names the same occurrence. -/
def State.map {Other : Type u} (f : Value → Other) (state : State Value clients) :
    State Other clients :=
  ⟨state.base, state.rows.map f, state.positions, state.completed, state.limit⟩

theorem map_pastEnd {Other : Type u} (f : Value → Other) (state : State Value clients) :
    pastEnd (state.map f) = pastEnd state := by
  simp [pastEnd, State.map, List.length_map]

theorem map_preserves_occurrence_positions {Other : Type u} (f : Value → Other)
    (state : State Value clients) (client : Fin clients) :
    (state.map f).base = state.base ∧
      (state.map f).positions client = state.positions client ∧
      (state.map f).completed = state.completed ∧
      (state.map f).limit = state.limit ∧
      pastEnd (state.map f) = pastEnd state := by
  exact ⟨rfl, rfl, rfl, rfl, map_pastEnd f state⟩

theorem map_id (state : State Value clients) : state.map id = state := by
  simp [State.map, List.map_id]

theorem map_setPosition {Other : Type u} (f : Value → Other) (state : State Value clients)
    (client : Fin clients) (position : Option Nat) :
    setPosition (state.map f) client position = (setPosition state client position).map f := by
  simp [setPosition, State.map]

theorem map_peek {Other : Type u} (f : Value → Other) (state : State Value clients)
    (client : Fin clients) :
    peek (state.map f) client = (peek state client).map f := by
  cases cursor : state.positions client with
  | none => simp [peek, State.map, Reply.map, cursor]
  | some position =>
      simp only [peek, State.map, cursor, List.getElem?_map, pastEnd, List.length_map]
      by_cases lower : state.base ≤ position
      · simp only [if_pos lower]
        cases row : state.rows[position - state.base]? with
        | some value => simp [Reply.map]
        | none =>
            by_cases last : position = state.base + state.rows.length
            · simp only [last, if_pos, Option.map_none]
              by_cases done : state.completed = true
              · simp [done, Reply.map]
              · simp [done, Reply.map]
            · simp [Reply.map, Option.map_none, last]
      · simp [if_neg lower, Reply.map]

theorem map_pull {Other : Type u} (f : Value → Other) (state : State Value clients)
    (client : Fin clients) :
    pull (state.map f) client =
      ((pull state client).1.map f, (pull state client).2.map f) := by
  simp only [pull, map_peek]
  cases peek state client <;> simp [Reply.map, map_setPosition]

theorem map_unread {Other : Type u} (f : Value → Other) (state : State Value clients)
    (client : Fin clients) :
    unread (state.map f) client = (unread state client).map f := by
  cases cursor : state.positions client with
  | none => simp [unread, State.map, cursor]
  | some position => simp [unread, State.map, cursor, List.map_drop]

theorem map_cutoff {Other : Type u} (f : Value → Other) (state : State Value clients) :
    cutoff (state.map f) = cutoff state := by
  simp only [cutoff, pastEnd, State.map, List.length_map]

theorem map_trim {Other : Type u} (f : Value → Other) (state : State Value clients) :
    trim (state.map f) = (trim state).map f := by
  unfold trim
  rw [map_cutoff]
  simp only [State.map, List.map_drop]

theorem append_map {Other : Type u} (f : Value → Other) (state : State Value clients)
    (value : Value) :
    append (state.map f) (f value) =
      ((append state value).1, (append state value).2.map f) := by
  unfold append
  simp only [State.map, List.length_map]
  split
  · rfl
  · split
    · simp [List.map_append]
    · rfl

theorem map_complete {Other : Type u} (f : Value → Other) (state : State Value clients) :
    complete (state.map f) = (complete state).map f := by
  simp [complete, State.map]

/-! ## Cursor travel

Delivery budgets can be measured from retained cursor positions without
comparing payloads. The relation excludes retirement and revival: those
change the set of observers and require their own ownership laws.
-/

open scoped BigOperators

/-- Travel of one retained cursor. Equal payloads never identify positions. -/
def cursorAdvance (start finish : Option Nat) : Nat :=
  match start, finish with
  | some s, some f => f - s
  | _, _ => 0

/-- A retained cursor moves forward; an absent cursor stays absent. -/
def CursorStep (start finish : Option Nat) : Prop :=
  match start, finish with
  | none, none => True
  | some s, some f => s ≤ f
  | _, _ => False

/-- Sum of per-consumer cursor travel. Cancelled cursors contribute nothing. -/
def cohortAdvance {clients : Nat}
    (start finish : Fin clients → Option Nat) : Nat :=
  ∑ client, cursorAdvance (start client) (finish client)

theorem cursorAdvance_refl (position : Option Nat) :
    cursorAdvance position position = 0 := by
  cases position with
  | none => rfl
  | some n => simp [cursorAdvance]

theorem cursorStep_refl (position : Option Nat) : CursorStep position position := by
  cases position with
  | none => simp [CursorStep]
  | some _ => simp [CursorStep]

theorem cursorAdvance_add (start mid finish : Option Nat)
    (left : CursorStep start mid) (right : CursorStep mid finish) :
    cursorAdvance start finish = cursorAdvance start mid + cursorAdvance mid finish := by
  cases start with
  | none =>
      cases mid with
      | none =>
          cases finish with
          | none => simp [cursorAdvance]
          | some _ => simp [CursorStep] at right
      | some _ => simp [CursorStep] at left
  | some s =>
      cases mid with
      | none => simp [CursorStep] at left
      | some m =>
          cases finish with
          | none => simp [CursorStep] at right
          | some f =>
              simp only [CursorStep, cursorAdvance] at left right ⊢
              omega

theorem cursorStep_trans {start mid finish : Option Nat}
    (left : CursorStep start mid) (right : CursorStep mid finish) :
    CursorStep start finish := by
  cases start with
  | none =>
      cases mid with
      | none =>
          cases finish with
          | none => simp [CursorStep]
          | some _ => simp [CursorStep] at right
      | some _ => simp [CursorStep] at left
  | some s =>
      cases mid with
      | none => simp [CursorStep] at left
      | some m =>
          cases finish with
          | none => simp [CursorStep] at right
          | some f =>
              simp only [CursorStep] at left right ⊢
              omega

theorem cohortAdvance_refl {clients : Nat} (positions : Fin clients → Option Nat) :
    cohortAdvance positions positions = 0 := by
  simp [cohortAdvance, cursorAdvance_refl]

theorem cohortAdvance_add {clients : Nat}
    (start mid finish : Fin clients → Option Nat)
    (left : ∀ client, CursorStep (start client) (mid client))
    (right : ∀ client, CursorStep (mid client) (finish client)) :
    cohortAdvance start finish = cohortAdvance start mid + cohortAdvance mid finish := by
  unfold cohortAdvance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun client _ =>
    cursorAdvance_add _ _ _ (left client) (right client))

/-- A complete, equally ordered advice stream determines the original rows. -/
theorem values_and_advice_reassemble {Advice : Type v} (rows : List (Value × Advice)) :
    List.zip (rows.map Prod.fst) (rows.map Prod.snd) = rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases row with
      | mk value advice =>
          exact congrArg (List.cons (value, advice)) ih

/-- A value stream, its first recorded advice and a later active advice cannot
    reconstruct every earlier advice stream: even the first equal-valued row
    can agree while the second row carries a different advice. -/
theorem erased_suffix_advice_not_recoverable {Advice : Type v}
    (value : Value) (first second current : Advice) (distinct : first ≠ second)
    (restore : List Value → Advice → Advice → List (Value × Advice)) :
    ¬ (restore [value, value] first current = [(value, first), (value, first)] ∧
      restore [value, value] first current = [(value, first), (value, second)]) := by
  rintro ⟨firstRestored, secondRestored⟩
  have rowsEqual := firstRestored.symm.trans secondRestored
  have pairEqual : (value, first) = (value, second) :=
    (List.cons.inj (List.cons.inj rowsEqual).2).1
  exact distinct (congrArg Prod.snd pairEqual)

namespace Controls

def sample : State Nat 2 := ⟨0, [7, 7, 9], fun _ => some 0, false, 4⟩

theorem sample_valid : Valid sample := by
  simp [Valid, sample, pastEnd]

theorem consumers_have_independent_occurrences :
    peek (pull sample 0).2 0 = .answer 1 7 ∧ peek (pull sample 0).2 1 = .answer 0 7 := by decide

theorem independent_delivery_keeps_the_full_log :
    (let first := pull sample 0
     let second := pull first.2 1
     (first.1, second.1, second.2.positions 0, second.2.positions 1, second.2.rows)) =
      (.answer 0 7, .answer 0 7, some 1, some 1, [7, 7, 9]) := by decide +kernel

/-- Equal values may carry different per-occurrence scheduling advice. -/
def advisedSample : State (Nat × Nat) 2 :=
  ⟨0, [(7, 3), (7, 9)], fun _ => some 0, false, 3⟩

theorem advisedSample_valid : Valid advisedSample := by
  simp [Valid, advisedSample, pastEnd]

theorem equal_values_keep_their_own_advice :
    (let first := pull advisedSample 0
     let second := pull first.2 0
     (first.1, second.1, peek second.2 1)) =
      (.answer 0 (7, 3), .answer 1 (7, 9), .answer 0 (7, 3)) := by
  decide +kernel

/-- Reattaching the first row's advice to every equal value changes the
    second delivery, even though the projected value stream is unchanged. -/
theorem one_advice_does_not_describe_equal_values :
    let flattened := advisedSample.map (fun row => (row.1, 3))
    flattened.rows.map Prod.fst = advisedSample.rows.map Prod.fst ∧
      (pull (pull flattened 0).2 0).1 ≠ (pull (pull advisedSample 0).2 0).1 := by
  decide +kernel

/-- Two requests using one cursor compete for successive occurrences, even
when their payloads are equal. Their requesting identities cannot be swapped. -/
theorem one_cursor_does_not_preserve_request_order :
    (let first := pull sample 0
     let second := pull first.2 0
     (first.1, second.1)) ≠
      (let first := pull sample 0
       let second := pull first.2 0
       (second.1, first.1)) := by decide +kernel

/-- A producer append cannot be commuted past a waiting consumer's request:
one order delivers the new occurrence, while the other retains a paused cursor. -/
theorem publication_and_waiting_delivery_are_distinct :
    (pull (append (initial (Value := Nat) (clients := 2) 4) 7).2 0).1 = .answer 0 7 ∧
      (pull (initial (Value := Nat) (clients := 2) 4) 0).1 = .paused ∧
      (pull (append (initial (Value := Nat) (clients := 2) 4) 7).2 0).2.positions 0 = some 1 ∧
      (append (pull (initial (Value := Nat) (clients := 2) 4) 0).2 7).2.positions 0 = some 0 := by
  decide +kernel

theorem cancellation_keeps_the_other_consumer :
    peek (trim (cancel sample 0)) 1 = .answer 0 7 ∧ (trim (cancel sample 0)).rows = [7, 7, 9] := by decide

theorem empty_open_log_is_a_pause :
    peek (initial (Value := Nat) (clients := 2) 4) 0 = .paused ∧
      peek (complete (initial (Value := Nat) (clients := 2) 4)) 0 = .completed := by decide

def full : State Nat 2 := { sample with limit := 3 }

theorem full_log_keeps_pending_work : append full 10 = (.backpressure, full) := by
  apply full_log_preserves_residual <;> decide

theorem sharing_one_cursor_loses_an_occurrence :
    peek (setPosition sample 1 ((pull sample 0).2.positions 0)) 1 = .answer 1 7 ∧
      peek (pull sample 0).2 1 ≠ .answer 1 7 := by decide

theorem draining_keeps_duplicate_payloads :
    (drain 8 sample 0).1 = [(0, 7), (1, 7), (2, 9)] ∧
      (drain 8 sample 0).2.positions 0 = some 3 ∧
      (drain 8 sample 0).2.positions 1 = some 0 := by decide

theorem split_draining_retains_the_same_residual :
    drain (1 + 7) sample 0 =
      (let earlier := drain 1 sample 0
       let later := drain 7 earlier.2 0
       (earlier.1 ++ later.1, later.2)) := drain_split 1 7 sample 0

theorem slow_consumer_requires_backpressure :
    append (trim (drain 3 full 0).2) 10 = (.backpressure, trim (drain 3 full 0).2) := by
  apply full_log_preserves_residual <;> decide

theorem cancelling_the_slow_consumer_allows_progress :
    (append (trim (cancel (drain 3 full 0).2 1)) 10).1 = .accepted ∧
      peek (append (trim (cancel (drain 3 full 0).2 1)) 10).2 0 = .answer 3 10 := by decide

end Controls

end Mettapedia.Machines.Cursor.SharedOccurrenceLog
