import Mettapedia.Computability.RegularLanguages.RegexMatchObservations
import Mettapedia.Computability.RegularLanguages.Utf8Spans
import Mathlib.Tactic

/-!
# Ordered nonoverlapping regex iteration

The iteration contract is an independent relation on returned observations.
An executable cursor consumes explicit search outcomes, suppresses an empty
candidate adjoining the previous returned end, and advances empty candidates
by one scalar. Completed absence, unfinished work and faults remain distinct.
This iterator observation does not delete candidates from an all-matches relation.

Search outcomes carry only the basic bounded-span contract. This file does not
prove the source-selected-capture adequacy of a regex compiler or a native C
implementation. Scalar-to-byte transport uses the existing UTF-8 span theory.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexIteration

open RegexMatchObservations (Observation Span)

structure Cursor where
  position : Nat
  previousEnd : Option Nat
  finished : Bool
  deriving DecidableEq, Repr

def Cursor.Valid (length : Nat) (cursor : Cursor) : Prop :=
  cursor.position ≤ length ∧ ∀ last, cursor.previousEnd = some last → last ≤ cursor.position

def initial : Cursor := ⟨0, none, false⟩

/-- Independent ordering and adjacency policy. A later nonempty span may
start at the previous end; a later empty span may not occupy that same end. -/
def Follows (previous : Option Nat) (observation : Observation) : Prop :=
  ∀ last, previous = some last → last ≤ observation.span.start ∧
    (observation.span.start = observation.span.stop → last ≠ observation.span.stop)

inductive Trace (length : Nat) : Option Nat → List Observation → Prop
  | nil (previous : Option Nat) : Trace length previous []
  | cons {previous observation rest} : observation.span.Valid length →
      Follows previous observation → Trace length (some observation.span.stop) rest →
      Trace length previous (observation :: rest)

inductive Fault where
  | invalidUtf8
  | invalidArgument
  | allocationFailure
  deriving DecidableEq, Repr

/-- The selector's interface states bounds, not how a selected answer is
justified. Source/compiler adequacy is a separate obligation. -/
inductive SearchOutcome (length position : Nat) where
  | found (observation : Observation) (bounded : observation.span.Valid length)
      (afterPosition : position ≤ observation.span.start)
  | closed
  | pending
  | fault (reason : Fault)

abbrev Search (length : Nat) := (position : Nat) → SearchOutcome length position

inductive Result where
  | yielded (observation : Observation) (cursor : Cursor)
  | closed (cursor : Cursor)
  | pending (cursor : Cursor)
  | fault (reason : Fault) (cursor : Cursor)
  deriving DecidableEq, Repr

def suppressed (cursor : Cursor) (observation : Observation) : Bool :=
  observation.span.start == observation.span.stop && cursor.previousEnd == some observation.span.stop

/-- The previous returned end changes only when an observation is delivered.
Suppressed candidates can advance the scan without changing that history. -/
def advance (length : Nat) (cursor : Cursor) (observation : Observation) : Cursor :=
  if observation.span.start = observation.span.stop then
    if observation.span.stop = length then ⟨observation.span.stop, cursor.previousEnd, true⟩
    else ⟨observation.span.stop + 1, cursor.previousEnd, false⟩
  else ⟨observation.span.stop, cursor.previousEnd, false⟩

def next (length : Nat) (search : Search length) : Nat → Cursor → Result
  | fuel, cursor =>
      if cursor.finished then .closed cursor else
        match fuel with
        | 0 => .pending cursor
        | fuel + 1 =>
            match search cursor.position with
            | .closed => .closed { cursor with finished := true }
            | .pending => .pending cursor
            | .fault reason => .fault reason cursor
            | .found observation _ _ =>
                let advanced := advance length cursor observation
                if suppressed cursor observation then
                  if advanced.finished then .closed advanced
                  else next length search fuel advanced
                else .yielded observation { advanced with previousEnd := some observation.span.stop }

theorem initial_valid (length : Nat) : Cursor.Valid length initial := by simp [Cursor.Valid, initial]

theorem follows_strict_end {length previous : Nat} {observation : Observation}
    (valid : observation.span.Valid length) (follows : Follows (some previous) observation) :
    previous < observation.span.stop := by
  have later := follows previous rfl
  unfold Span.Valid at valid
  by_cases empty : observation.span.start = observation.span.stop
  · have different := later.2 empty
    omega
  · omega

theorem advance_previous (length : Nat) (cursor : Cursor) (observation : Observation) :
    (advance length cursor observation).previousEnd = cursor.previousEnd := by
  unfold advance
  split <;> (try split) <;> rfl

theorem advance_bounds (length : Nat) (cursor : Cursor) (observation : Observation)
    (valid : observation.span.Valid length) (afterPosition : cursor.position ≤ observation.span.start) :
    cursor.position ≤ (advance length cursor observation).position ∧
      observation.span.stop ≤ (advance length cursor observation).position ∧
      (advance length cursor observation).position ≤ length := by
  unfold Span.Valid at valid
  unfold advance
  split <;> (try split) <;> simp_all <;> omega

theorem advance_valid (length : Nat) (cursor : Cursor) (observation : Observation)
    (cursorValid : Cursor.Valid length cursor) (valid : observation.span.Valid length)
    (afterPosition : cursor.position ≤ observation.span.start) : Cursor.Valid length (advance length cursor observation) := by
  have bounds := advance_bounds length cursor observation valid afterPosition
  refine ⟨bounds.2.2, ?_⟩
  intro last previous
  rw [advance_previous] at previous
  exact (cursorValid.2 last previous).trans bounds.1

theorem unsuppressed_follows (length : Nat) (cursor : Cursor) (observation : Observation)
    (cursorValid : Cursor.Valid length cursor) (afterPosition : cursor.position ≤ observation.span.start)
    (accepted : suppressed cursor observation = false) : Follows cursor.previousEnd observation := by
  intro last previous
  refine ⟨(cursorValid.2 last previous).trans afterPosition, ?_⟩
  intro empty same
  simp [suppressed, empty, previous, same] at accepted

/-- A result's postcondition is stated independently of the implementation
of `next`; delivered observations obey the trace contract. -/
def Post (length : Nat) (before : Cursor) : Result → Prop
  | .yielded observation after =>
      observation.span.Valid length ∧ before.position ≤ observation.span.start ∧
      Follows before.previousEnd observation ∧ Cursor.Valid length after ∧
      after.previousEnd = some observation.span.stop
  | .closed after => Cursor.Valid length after ∧ after.finished = true ∧
      after.previousEnd = before.previousEnd ∧ before.position ≤ after.position
  | .pending after | .fault _ after => Cursor.Valid length after ∧ after.finished = false ∧
      after.previousEnd = before.previousEnd ∧ before.position ≤ after.position

theorem Post.weaken {length : Nat} {before middle : Cursor} {result : Result}
    (positions : before.position ≤ middle.position) (previous : middle.previousEnd = before.previousEnd)
    (post : Post length middle result) : Post length before result := by
  cases result with
  | yielded observation after =>
      exact ⟨post.1, positions.trans post.2.1, previous ▸ post.2.2.1, post.2.2.2⟩
  | closed after => exact ⟨post.1, post.2.1, post.2.2.1.trans previous, positions.trans post.2.2.2⟩
  | pending after => exact ⟨post.1, post.2.1, post.2.2.1.trans previous, positions.trans post.2.2.2⟩
  | fault reason after => exact ⟨post.1, post.2.1, post.2.2.1.trans previous, positions.trans post.2.2.2⟩

theorem next_post (length : Nat) (search : Search length) (fuel : Nat) :
    ∀ cursor, Cursor.Valid length cursor → Post length cursor (next length search fuel cursor) := by
  induction fuel with
  | zero =>
      intro cursor valid
      by_cases finished : cursor.finished = true
      · simp [next, finished, Post, valid]
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        simp [next, unfinished, Post, valid]
  | succ fuel ih =>
      intro cursor valid
      by_cases finished : cursor.finished = true
      · simp [next, finished, Post, valid]
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        cases answer : search cursor.position with
        | closed => simp [next, unfinished, answer, Post, Cursor.Valid] at valid ⊢; exact valid
        | pending => simp [next, unfinished, answer, Post, valid]
        | fault reason => simp [next, unfinished, answer, Post, valid]
        | found observation bounded afterPosition =>
            have bounds := advance_bounds length cursor observation bounded afterPosition
            have advancedValid := advance_valid length cursor observation valid bounded afterPosition
            by_cases suppress : suppressed cursor observation = true
            · simp only [next, unfinished, Bool.false_eq_true, ↓reduceIte, answer, suppress]
              by_cases done : (advance length cursor observation).finished = true
              · simp only [done, ↓reduceIte, Post]
                exact ⟨advancedValid, by trivial, advance_previous _ _ _, bounds.1⟩
              · simp only [done]
                exact (ih _ advancedValid).weaken bounds.1 (advance_previous _ _ _)
            · have allowed : suppressed cursor observation = false := Bool.eq_false_iff.mpr suppress
              simp only [next, unfinished, Bool.false_eq_true, ↓reduceIte, answer, allowed, Post]
              refine ⟨bounded, afterPosition, unsuppressed_follows length cursor observation valid afterPosition allowed,
                ?_, by trivial⟩
              exact ⟨bounds.2.2, by intro last same; cases same; exact bounds.2.1⟩

/-- Completion is an absorbing observation and never calls the selector. -/
theorem completed_stable (length : Nat) (search : Search length) (fuel : Nat) (cursor : Cursor)
    (finished : cursor.finished = true) : next length search fuel cursor = .closed cursor := by
  cases fuel <;> simp [next, finished]

theorem suppression_advances_past_previous (length : Nat) (cursor : Cursor) (observation : Observation)
    (suppression : suppressed cursor observation = true)
    (unfinished : (advance length cursor observation).finished = false) :
    ∃ previous, cursor.previousEnd = some previous ∧
      previous < (advance length cursor observation).position := by
  simp only [suppressed, Bool.and_eq_true, beq_iff_eq] at suppression
  obtain ⟨empty, previous⟩ := suppression
  refine ⟨observation.span.stop, previous, ?_⟩
  unfold advance at unfinished ⊢
  simp only [empty, ↓reduceIte] at unfinished ⊢
  by_cases atEnd : observation.span.stop = length
  · simp [atEnd] at unfinished
  · simp [atEnd]

/-- There can be at most one suppressed candidate in a call to `next`.
After the scalar advance, another candidate cannot occupy the old end. -/
theorem suppression_cannot_repeat (length : Nat) (cursor : Cursor) (first second : Observation)
    (suppression : suppressed cursor first = true)
    (unfinished : (advance length cursor first).finished = false)
    (afterPosition : (advance length cursor first).position ≤ second.span.start) :
    suppressed (advance length cursor first) second = false := by
  apply Bool.eq_false_iff.mpr
  intro again
  obtain ⟨last, previous, beforePosition⟩ := suppression_advances_past_previous length cursor first suppression unfinished
  simp only [suppressed, Bool.and_eq_true, beq_iff_eq, advance_previous, previous,
    Option.some.injEq] at again
  omega

/-- Two selector attempts suffice to apply the adjacency policy. A pending
selector remains pending; this is not a time bound on either search attempt. -/
theorem next_stable_after_two_attempts (length : Nat) (search : Search length) (extra : Nat) (cursor : Cursor) :
    next length search (extra + 2) cursor = next length search 2 cursor := by
  by_cases finished : cursor.finished = true
  · simp [next, finished]
  · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
    cases firstAnswer : search cursor.position with
    | closed => simp [next, unfinished, firstAnswer]
    | pending => simp [next, unfinished, firstAnswer]
    | fault reason => simp [next, unfinished, firstAnswer]
    | found first bounded firstAfter =>
        by_cases suppression : suppressed cursor first = true
        · by_cases done : (advance length cursor first).finished = true
          · simp [next, unfinished, firstAnswer, suppression, done]
          · have notDone : (advance length cursor first).finished = false := Bool.eq_false_iff.mpr done
            cases secondAnswer : search (advance length cursor first).position with
            | closed => simp [next, unfinished, firstAnswer, suppression, notDone, secondAnswer]
            | pending => simp [next, unfinished, firstAnswer, suppression, notDone, secondAnswer]
            | fault reason => simp [next, unfinished, firstAnswer, suppression, notDone, secondAnswer]
            | found second secondBounded secondAfter =>
                have allowed := suppression_cannot_repeat length cursor first second suppression notDone secondAfter
                simp [next, unfinished, firstAnswer, suppression, notDone, secondAnswer, allowed]
        · have allowed : suppressed cursor first = false := Bool.eq_false_iff.mpr suppression
          simp [next, unfinished, firstAnswer, allowed]

def SearchDelivers {length : Nat} (search : Search length) (position : Nat) (observation : Observation) : Prop :=
  match search position with
  | .found candidate _ _ => candidate = observation
  | .closed | .pending | .fault _ => False

/-- Every delivered observation is unchanged data returned by an actual
selector invocation at or beyond the initial cursor. -/
theorem next_yield_from_search (length : Nat) (search : Search length) (fuel : Nat) :
    ∀ cursor observation after,
      next length search fuel cursor = .yielded observation after →
      ∃ position, cursor.position ≤ position ∧ SearchDelivers search position observation := by
  induction fuel with
  | zero =>
      intro cursor observation after selected
      cases finished : cursor.finished <;> simp [next, finished] at selected
  | succ fuel ih =>
      intro cursor observation after selected
      by_cases finished : cursor.finished = true
      · simp [next, finished] at selected
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        cases answer : search cursor.position with
        | closed => simp [next, unfinished, answer] at selected
        | pending => simp [next, unfinished, answer] at selected
        | fault reason => simp [next, unfinished, answer] at selected
        | found candidate bounded afterPosition =>
            by_cases suppression : suppressed cursor candidate = true
            · simp only [next, unfinished, Bool.false_eq_true, ↓reduceIte, answer, suppression] at selected
              split at selected
              · contradiction
              · obtain ⟨position, later, delivered⟩ := ih _ _ _ selected
                exact ⟨position, (advance_bounds length cursor candidate bounded afterPosition).1.trans later, delivered⟩
            · have allowed : suppressed cursor candidate = false := Bool.eq_false_iff.mpr suppression
              simp only [next, unfinished, Bool.false_eq_true, ↓reduceIte, answer, allowed,
                Result.yielded.injEq] at selected
              obtain ⟨rfl, _⟩ := selected
              exact ⟨cursor.position, le_rfl, by simp [SearchDelivers, answer]⟩

theorem Trace.all_valid {length : Nat} {previous : Option Nat} {observations : List Observation}
    (trace : Trace length previous observations) : ∀ observation ∈ observations, observation.span.Valid length := by
  induction trace with
  | nil => simp
  | cons valid follows rest ih =>
      intro observation member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact ih observation member

theorem Trace.starts_after_previous {length : Nat} {previous : Option Nat} {observations : List Observation}
    (trace : Trace length previous observations) :
    ∀ last, previous = some last → ∀ observation ∈ observations, last ≤ observation.span.start := by
  induction trace with
  | nil => simp
  | @cons previous first rest valid follows remaining ih =>
      intro last same observation member
      have earlier := (follows last same).1
      rcases List.mem_cons.mp member with rfl | member
      · exact earlier
      · exact (earlier.trans valid.1).trans (ih first.span.stop rfl observation member)

theorem Trace.stops_after_previous {length : Nat} {previous : Option Nat} {observations : List Observation}
    (trace : Trace length previous observations) :
    ∀ last, previous = some last → ∀ observation ∈ observations, last < observation.span.stop := by
  induction trace with
  | nil => simp
  | @cons previous first rest valid follows remaining ih =>
      intro last same observation member
      have firstLater : last < first.span.stop :=
        follows_strict_end valid (by simpa [same] using follows)
      rcases List.mem_cons.mp member with rfl | member
      · exact firstLater
      · exact firstLater.trans (ih first.span.stop rfl observation member)

theorem Trace.nonoverlapping {length : Nat} {previous : Option Nat} {observations : List Observation}
    (trace : Trace length previous observations) :
    observations.Pairwise (fun earlier later => earlier.span.stop ≤ later.span.start) := by
  induction trace with
  | nil => exact .nil
  | cons valid follows remaining ih =>
      apply List.pairwise_cons.mpr
      exact ⟨fun observation member => remaining.starts_after_previous _ rfl observation member, ih⟩

/-- In particular, no two returned empty matches occupy the same boundary.
The stronger fact is that all returned end positions increase strictly. -/
theorem Trace.strict_end_order {length : Nat} {previous : Option Nat} {observations : List Observation}
    (trace : Trace length previous observations) :
    observations.Pairwise (fun earlier later => earlier.span.stop < later.span.stop) := by
  induction trace with
  | nil => exact .nil
  | cons valid follows remaining ih =>
      apply List.pairwise_cons.mpr
      exact ⟨fun observation member => remaining.stops_after_previous _ rfl observation member, ih⟩

theorem Trace.no_repeated_end {length : Nat} {previous : Option Nat} {observations : List Observation}
    (trace : Trace length previous observations) :
    observations.Pairwise (fun earlier later => earlier.span.stop ≠ later.span.stop) :=
  trace.strict_end_order.imp (fun earlier => Nat.ne_of_lt earlier)

theorem Trace.remaining_count {length : Nat} {previous : Option Nat} {observations : List Observation}
    (trace : Trace length previous observations) :
    ∀ last, previous = some last → last ≤ length → observations.length + last ≤ length := by
  induction trace with
  | nil => intro last same bounded; simpa using bounded
  | @cons previous first rest valid follows remaining ih =>
      intro last same bounded
      have strict : last < first.span.stop := follows_strict_end valid (by simpa [same] using follows)
      have count := ih first.span.stop rfl valid.2
      simp only [List.length_cons]
      omega

/-- This counts returned occurrences, not the work needed to search for them. -/
theorem Trace.output_count {length : Nat} {previous : Option Nat} {observations : List Observation}
    (trace : Trace length previous observations) : observations.length ≤ length + 1 := by
  cases trace with
  | nil => simp
  | cons valid follows remaining =>
      have count := remaining.remaining_count _ rfl valid.2
      simp only [List.length_cons]
      omega

def finalEnd : Option Nat → List Observation → Option Nat
  | previous, [] => previous
  | _, observation :: rest => finalEnd (some observation.span.stop) rest

inductive Collection where
  | complete (observations : List Observation) (cursor : Cursor)
  | pending (observations : List Observation) (cursor : Cursor)
  | fault (reason : Fault) (observations : List Observation) (cursor : Cursor)
  deriving DecidableEq, Repr

def Collection.prepend (observation : Observation) : Collection → Collection
  | .complete observations cursor => .complete (observation :: observations) cursor
  | .pending observations cursor => .pending (observation :: observations) cursor
  | .fault reason observations cursor => .fault reason (observation :: observations) cursor

def Collection.observations : Collection → List Observation
  | .complete observations _ | .pending observations _ | .fault _ observations _ => observations

def Collection.cursor : Collection → Cursor
  | .complete _ cursor | .pending _ cursor | .fault _ _ cursor => cursor

def Collection.Legal (length : Nat) (previous : Option Nat) (collection : Collection) : Prop :=
  Trace length previous collection.observations ∧ Cursor.Valid length collection.cursor ∧
    collection.cursor.previousEnd = finalEnd previous collection.observations ∧
    match collection with
    | .complete _ cursor => cursor.finished = true
    | .pending _ cursor | .fault _ _ cursor => cursor.finished = false

def collect (length : Nat) (search : Search length) (searchFuel : Nat) : Nat → Cursor → Collection
  | fuel, cursor =>
      if cursor.finished then .complete [] cursor else
        match fuel with
        | 0 => .pending [] cursor
        | fuel + 1 =>
            match next length search searchFuel cursor with
            | .closed after => .complete [] after
            | .pending after => .pending [] after
            | .fault reason after => .fault reason [] after
            | .yielded observation after => (collect length search searchFuel fuel after).prepend observation

theorem prepend_legal {length : Nat} {previous : Option Nat} {observation : Observation} {collection : Collection}
    (valid : observation.span.Valid length) (follows : Follows previous observation)
    (legal : collection.Legal length (some observation.span.stop)) :
    (collection.prepend observation).Legal length previous := by
  cases collection <;> exact ⟨.cons valid follows legal.1, legal.2⟩

/-- Ordered results and the retained cursor obey one contract on completion,
unfinished work and faults alike; an unfinished prefix is never a no-match. -/
theorem collect_legal (length : Nat) (search : Search length) (searchFuel fuel : Nat) :
    ∀ cursor, Cursor.Valid length cursor →
      (collect length search searchFuel fuel cursor).Legal length cursor.previousEnd := by
  induction fuel with
  | zero =>
      intro cursor valid
      by_cases finished : cursor.finished = true
      · simp only [collect, finished, ↓reduceIte, Collection.Legal, Collection.observations, Collection.cursor]
        exact ⟨.nil _, valid, rfl, by trivial⟩
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        simp only [collect, unfinished, Bool.false_eq_true, ↓reduceIte,
          Collection.Legal, Collection.observations, Collection.cursor]
        exact ⟨.nil _, valid, rfl, by trivial⟩
  | succ fuel ih =>
      intro cursor valid
      by_cases finished : cursor.finished = true
      · simp only [collect, finished, ↓reduceIte, Collection.Legal, Collection.observations, Collection.cursor]
        exact ⟨.nil _, valid, rfl, by trivial⟩
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        have post := next_post length search searchFuel cursor valid
        cases result : next length search searchFuel cursor with
        | closed after =>
            simp only [result, Post] at post
            simp only [collect, unfinished, Bool.false_eq_true, ↓reduceIte, result,
              Collection.Legal, Collection.observations, Collection.cursor]
            exact ⟨.nil _, post.1, post.2.2.1, post.2.1⟩
        | pending after =>
            simp only [result, Post] at post
            simp only [collect, unfinished, Bool.false_eq_true, ↓reduceIte, result,
              Collection.Legal, Collection.observations, Collection.cursor]
            exact ⟨.nil _, post.1, post.2.2.1, post.2.1⟩
        | fault reason after =>
            simp only [result, Post] at post
            simp only [collect, unfinished, Bool.false_eq_true, ↓reduceIte, result,
              Collection.Legal, Collection.observations, Collection.cursor]
            exact ⟨.nil _, post.1, post.2.2.1, post.2.1⟩
        | yielded observation after =>
            simp only [result, Post] at post
            simp only [collect, unfinished, Bool.false_eq_true, ↓reduceIte, result]
            apply prepend_legal post.1 post.2.2.1
            simpa only [post.2.2.2.2] using ih after post.2.2.2.1

theorem collect_nonoverlapping (length : Nat) (search : Search length) (searchFuel fuel : Nat)
    (cursor : Cursor) (valid : Cursor.Valid length cursor) :
    (collect length search searchFuel fuel cursor).observations.Pairwise
      (fun earlier later => earlier.span.stop ≤ later.span.start) :=
  (collect_legal length search searchFuel fuel cursor valid).1.nonoverlapping

theorem collect_no_repeated_end (length : Nat) (search : Search length) (searchFuel fuel : Nat)
    (cursor : Cursor) (valid : Cursor.Valid length cursor) :
    (collect length search searchFuel fuel cursor).observations.Pairwise
      (fun earlier later => earlier.span.stop ≠ later.span.stop) :=
  (collect_legal length search searchFuel fuel cursor valid).1.no_repeated_end

theorem collect_output_count (length : Nat) (search : Search length) (searchFuel fuel : Nat)
    (cursor : Cursor) (valid : Cursor.Valid length cursor) :
    (collect length search searchFuel fuel cursor).observations.length ≤ length + 1 :=
  (collect_legal length search searchFuel fuel cursor valid).1.output_count

theorem collect_source_sound (length : Nat) (search : Search length) (searchFuel fuel : Nat) :
    ∀ cursor, Cursor.Valid length cursor →
      ∀ observation ∈ (collect length search searchFuel fuel cursor).observations,
        ∃ position, cursor.position ≤ position ∧ SearchDelivers search position observation := by
  induction fuel with
  | zero =>
      intro cursor valid observation member
      by_cases finished : cursor.finished = true
      · simp [collect, finished, Collection.observations] at member
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        simp [collect, unfinished, Collection.observations] at member
  | succ fuel ih =>
      intro cursor valid observation member
      by_cases finished : cursor.finished = true
      · simp [collect, finished, Collection.observations] at member
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        have post := next_post length search searchFuel cursor valid
        cases result : next length search searchFuel cursor with
        | closed after => simp [collect, unfinished, result, Collection.observations] at member
        | pending after => simp [collect, unfinished, result, Collection.observations] at member
        | fault reason after => simp [collect, unfinished, result, Collection.observations] at member
        | yielded candidate after =>
            simp only [result, Post] at post
            have nextPosition : cursor.position ≤ after.position :=
              (post.2.1.trans post.1.1).trans (post.2.2.2.1.2 candidate.span.stop post.2.2.2.2)
            simp only [collect, unfinished, Bool.false_eq_true, ↓reduceIte, result] at member
            have members : (Collection.prepend candidate
                (collect length search searchFuel fuel after)).observations =
                candidate :: (collect length search searchFuel fuel after).observations := by
              cases collect length search searchFuel fuel after <;> rfl
            rw [members] at member
            rcases List.mem_cons.mp member with rfl | later
            · exact next_yield_from_search length search searchFuel cursor observation after result
            · obtain ⟨position, begins, delivered⟩ := ih after post.2.2.2.1 observation later
              exact ⟨position, nextPosition.trans begins, delivered⟩

theorem collect_finished (length : Nat) (search : Search length) (searchFuel fuel : Nat)
    (cursor : Cursor) (finished : cursor.finished = true) :
    collect length search searchFuel fuel cursor = .complete [] cursor := by
  cases fuel <;> simp [collect, finished]

/-- Once enumeration completes, granting a larger result budget cannot add
answers or change the completed prefix. -/
theorem collect_completed_stable (length : Nat) (search : Search length) (searchFuel fuel extra : Nat) :
    ∀ cursor observations after,
      collect length search searchFuel fuel cursor = .complete observations after →
      collect length search searchFuel (fuel + extra) cursor = .complete observations after := by
  induction fuel with
  | zero =>
      intro cursor observations after complete
      by_cases finished : cursor.finished = true
      · rw [collect_finished length search searchFuel 0 cursor finished] at complete
        rw [collect_finished length search searchFuel (0 + extra) cursor finished]
        exact complete
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        simp [collect, unfinished] at complete
  | succ fuel ih =>
      intro cursor observations after complete
      by_cases finished : cursor.finished = true
      · rw [collect_finished length search searchFuel (fuel + 1) cursor finished] at complete
        rw [collect_finished length search searchFuel (fuel + 1 + extra) cursor finished]
        exact complete
      · have unfinished : cursor.finished = false := Bool.eq_false_iff.mpr finished
        cases result : next length search searchFuel cursor with
        | closed nextCursor => simpa [collect, unfinished, result, Nat.succ_add] using complete
        | pending nextCursor => simp [collect, unfinished, result] at complete
        | fault reason nextCursor => simp [collect, unfinished, result] at complete
        | yielded observation nextCursor =>
            simp only [Nat.succ_add, collect, unfinished, Bool.false_eq_true, ↓reduceIte, result] at complete ⊢
            cases tail : collect length search searchFuel fuel nextCursor with
            | pending values finalCursor => simp [tail, Collection.prepend] at complete
            | fault reason values finalCursor => simp [tail, Collection.prepend] at complete
            | complete values finalCursor =>
                simp only [tail, Collection.prepend, Collection.complete.injEq] at complete
                obtain ⟨rfl, rfl⟩ := complete
                simp only [ih nextCursor values finalCursor tail, Collection.prepend]

def ByteBoundary (input : List Char) (byte : Nat) : Prop :=
  ∃ position ≤ input.length, byte = byteOffset input position

def byteSpan (input : List Char) (span : Span) : Span :=
  ⟨byteOffset input span.start, byteOffset input span.stop⟩

theorem byteSpan_boundaries (input : List Char) (span : Span) (valid : span.Valid input.length) :
    ByteBoundary input (byteSpan input span).start ∧ ByteBoundary input (byteSpan input span).stop :=
  ⟨⟨span.start, valid.1.trans valid.2, rfl⟩, ⟨span.stop, valid.2, rfl⟩⟩

theorem scalar_successor_is_safe (input : List Char) (position : Nat) (within : position < input.length) :
    ByteBoundary input (byteOffset input (position + 1)) ∧
      byteOffset input position < byteOffset input (position + 1) :=
  ⟨⟨position + 1, by omega, rfl⟩, byteOffset_strictMono input (by omega) (by omega)⟩

theorem byteSpan_valid (input : List Char) (span : Span) (valid : span.Valid input.length) :
    (byteSpan input span).Valid (utf8Length input) := by
  refine ⟨byteOffset_mono input valid.1, ?_⟩
  have bounded := byteOffset_mono input valid.2
  simpa [byteSpan, byteOffset] using bounded

theorem collect_byte_boundaries (input : List Char) (search : Search input.length) (searchFuel fuel : Nat)
    (cursor : Cursor) (valid : Cursor.Valid input.length cursor) :
    ∀ observation ∈ (collect input.length search searchFuel fuel cursor).observations,
      ByteBoundary input (byteSpan input observation.span).start ∧
        ByteBoundary input (byteSpan input observation.span).stop := by
  intro observation member
  exact byteSpan_boundaries input observation.span
    ((collect_legal input.length search searchFuel fuel cursor valid).1.all_valid observation member)

namespace Controls

private def observation (start stop : Nat) : Observation := ⟨⟨start, stop⟩, [], []⟩

private def emptySearch (length : Nat) : Search length := fun position =>
  if within : position ≤ length then .found (observation position position) ⟨by rfl, within⟩ (by rfl)
  else .closed

private def spans (collection : Collection) : List (Nat × Nat) :=
  collection.observations.map (fun observation => (observation.span.start, observation.span.stop))

theorem empty_matches_advance_by_scalars :
    spans (collect 2 (emptySearch 2) 2 5 initial) = [(0, 0), (1, 1), (2, 2)] := by decide

theorem unicode_empty_matches_have_original_byte_boundaries :
    ((collect 2 (emptySearch 2) 2 5 initial).observations.map fun observation =>
      let span := byteSpan "aλ".toList observation.span
      (span.start, span.stop)) = [(0, 0), (1, 1), (3, 3)] := by decide

private def literalThenEmpty : Search 2 := fun position =>
  if atStart : position = 0 then .found (observation 0 1) (by simp [observation, Span.Valid]) (by simp only [observation]; omega)
  else emptySearch 2 position

theorem adjoining_empty_candidate_is_suppressed :
    spans (collect 2 literalThenEmpty 2 5 initial) = [(0, 1), (2, 2)] := by decide

theorem suppression_skips_a_whole_multibyte_scalar :
    ((collect 2 literalThenEmpty 2 5 initial).observations.map fun observation =>
      let span := byteSpan "aλ".toList observation.span
      (span.start, span.stop)) = [(0, 1), (3, 3)] := by decide

private def pendingAfterSuppression : Search 2 := fun position =>
  if atPrevious : position = 1 then .found (observation 1 1) (by simp [observation, Span.Valid]) (by simp only [observation]; omega)
  else .pending

theorem unfinished_work_retains_suppression_progress :
    next 2 pendingAfterSuppression 2 ⟨1, some 1, false⟩ = .pending ⟨2, some 1, false⟩ := by decide

theorem pending_progress_can_resume_without_duplicate_empty :
    next 2 (emptySearch 2) 2 ⟨2, some 1, false⟩ = .yielded (observation 2 2) ⟨2, some 2, true⟩ := by decide

theorem completed_cursor_does_not_call_failing_search :
    next 2 (fun _ => .fault .allocationFailure) 10 ⟨2, some 2, true⟩ = .closed ⟨2, some 2, true⟩ := by decide

theorem fault_is_not_closed_absence :
    collect 2 (fun _ => .fault .allocationFailure) 2 4 initial = .fault .allocationFailure [] initial ∧
      (Result.pending initial ≠ .closed { initial with finished := true }) ∧
      (Result.fault .allocationFailure initial ≠ .closed { initial with finished := true }) := by decide

theorem byte_increment_would_split_scalar :
    byteOffset "aλ".toList 1 + 1 = 2 ∧ ¬ ByteBoundary "aλ".toList 2 := by
  constructor
  · decide
  · rintro ⟨position, within, equal⟩
    change position ≤ 2 at within
    interval_cases position <;> contradiction

end Controls

#print axioms next_post
#print axioms completed_stable
#print axioms next_stable_after_two_attempts
#print axioms next_yield_from_search
#print axioms Trace.nonoverlapping
#print axioms Trace.no_repeated_end
#print axioms Trace.output_count
#print axioms collect_legal
#print axioms collect_completed_stable
#print axioms collect_source_sound
#print axioms collect_output_count
#print axioms scalar_successor_is_safe
#print axioms collect_byte_boundaries
#print axioms Controls.unicode_empty_matches_have_original_byte_boundaries
#print axioms Controls.unfinished_work_retains_suppression_progress
#print axioms Controls.byte_increment_would_split_scalar

end Mettapedia.Computability.RegularLanguages.RegexIteration
