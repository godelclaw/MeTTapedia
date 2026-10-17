import Mettapedia.Computability.RegularLanguages.RegexMemoizedSearch

/-!
# Capture-event replay and uniform futures

The continuation code and visited points of a graph execution are independent
of incoming capture registers and choice history. Capture events are replayed
on each incoming register snapshot; the snapshots themselves need not agree.
Terminal eligibility is required to depend only on the control point.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexUniformFutures

open RegexTaggedGraph RegexSelectionCorrespondence
open OrderedGraphSearch (Point Probe successor)

universe u v w z

structure CaptureEvent (length : Nat) where
  slot : Nat
  position : Fin (length + 1)
  deriving DecidableEq

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

/-- A capture log is executed in its original order, without consulting the
graph, the selected endpoint, or the incoming choice history. -/
def replay (events : List (CaptureEvent length)) (registers : Registers length) : Registers length :=
  events.foldl (fun current event => write current event.slot event.position) registers

@[simp] theorem replay_nil (registers : Registers length) : replay [] registers = registers := rfl

@[simp] theorem replay_cons (event : CaptureEvent length) (events : List (CaptureEvent length))
    (registers : Registers length) :
    replay (event :: events) registers = replay events (write registers event.slot event.position) := rfl

theorem replay_append (first second : List (CaptureEvent length)) (registers : Registers length) :
    replay (first ++ second) registers = replay second (replay first registers) := by
  simp [replay, List.foldl_append]

/-- The last event for a slot, specified by a right-to-left observation of the
event list rather than by register execution. -/
def lastWrite : List (CaptureEvent length) → Nat → Option (Fin (length + 1))
  | [], _ => none
  | event :: later, slot =>
      (lastWrite later slot).or (if event.slot = slot then some event.position else none)

/-- Slotwise capture semantics: the last save wins, and absence of a save
retains the caller's register. -/
theorem replay_slot (events : List (CaptureEvent length)) (registers : Registers length) (slot : Nat) :
    replay events registers slot = (lastWrite events slot).or (registers slot) := by
  induction events generalizing registers with
  | nil => rfl
  | cons event later ih =>
      rw [replay_cons, ih]
      cases latest : lastWrite later slot with
      | some position => simp [lastWrite, latest]
      | none =>
          by_cases same : event.slot = slot
          · subst slot; simp [lastWrite, latest, write]
          · simp [lastWrite, latest, write, same, Ne.symm same]

/-- Two incoming snapshots yield equal final captures exactly when they agree
on the slots not overwritten by this continuation. -/
theorem replay_eq_iff (events : List (CaptureEvent length))
    (first second : Registers length) :
    replay events first = replay events second ↔
      ∀ slot, lastWrite events slot = none → first slot = second slot := by
  constructor
  · intro equal slot untouched
    have observed := congrFun equal slot
    simpa [replay_slot, untouched] using observed
  · intro same
    funext slot
    rw [replay_slot, replay_slot]
    cases latest : lastWrite events slot with
    | none => simp [same slot latest]
    | some position => rfl

/-- A final write wins over every earlier value of its slot. -/
theorem replay_last_write (events : List (CaptureEvent length)) (registers : Registers length)
    (event : CaptureEvent length) :
    replay (events ++ [event]) registers event.slot = some event.position := by
  rw [replay_append]
  exact write_same _ _ _

/-- Slots absent from the event log retain their incoming values. -/
theorem replay_untouched (events : List (CaptureEvent length)) (registers : Registers length)
    (slot : Nat) (untouched : ∀ event ∈ events, event.slot ≠ slot) :
    replay events registers slot = registers slot := by
  induction events generalizing registers with
  | nil => rfl
  | cons event events ih =>
      rw [replay_cons, ih _ (fun later member => untouched later (by simp [member]))]
      exact write_other _ _ _ _ (Ne.symm (untouched event (by simp)))

/-- Replaying another branch from the original snapshot never incorporates
writes made only by the discarded branch. -/
theorem replay_branch_rollback (discarded chosen : List (CaptureEvent length))
    (registers : Registers length) (slot : Nat)
    (untouched : ∀ event ∈ chosen, event.slot ≠ slot) :
    replay chosen registers slot = registers slot ∧
      replay chosen (replay discarded registers) slot = replay discarded registers slot := by
  exact ⟨replay_untouched _ _ _ untouched, replay_untouched _ _ _ untouched⟩

/-- The save event issued at an instruction, independently of thread data. -/
def eventAt (graph : State → Node State Class Assertion Tag) (point : Point State length) :
    List (CaptureEvent length) :=
  match graph point.1 with
  | .save slot _ => [⟨slot, point.2⟩]
  | _ => []

/-- All capture events on a supplied point path, in traversal order. -/
def events (graph : State → Node State Class Assertion Tag) (points : List (Point State length)) :
    List (CaptureEvent length) := points.flatMap (eventAt graph)

@[simp] theorem events_nil (graph : State → Node State Class Assertion Tag) :
    events graph ([] : List (Point State length)) = [] := rfl

@[simp] theorem events_cons (graph : State → Node State Class Assertion Tag)
    (point : Point State length) (points : List (Point State length)) :
    events graph (point :: points) = eventAt graph point ++ events graph points := rfl

/-- The terminal case does not issue a capture write. -/
theorem action_accept_no_event (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length) (tag : Tag)
    (accepted : action graph probe first = .accept tag) : eventAt graph first.point = [] := by
  cases node : graph first.point.1 <;> simp only [action, node] at accepted
  · simp [eventAt, node]
  · cases accepted
  · cases accepted
  · cases accepted
  · split at accepted
    · cases advanced : successor first.point.2 <;> simp [advanced] at accepted
    · cases accepted
  · split at accepted <;> cases accepted
  · cases accepted

/-- One deterministic instruction transports to any register/history snapshot
at the same control point. Its save event is the only register change. -/
theorem action_next_transfer (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) {first target other : Thread State length}
    (same : other.point = first.point) (step : action graph probe first = .next target) :
    ∃ after : Thread State length, action graph probe other = .next after ∧
      after.point = target.point ∧
      after.registers = replay (eventAt graph first.point) other.registers ∧
      after.choices = other.choices := by
  cases node : graph first.point.1 <;> simp only [action, node] at step
  · cases step
  · cases step
  · cases step
    rename_i next
    refine ⟨other.at next, ?_, ?_, ?_, rfl⟩
    · simp [action, same, node]
    · simp [Thread.at, same]
    · simp [Thread.at, eventAt, node]
  · cases step
  · split at step
    · rename_i contains
      cases advanced : successor first.point.2 with
      | none => simp [advanced] at step
      | some position =>
        simp only [advanced, Action.next.injEq] at step
        subst target
        refine ⟨{ other with point := (_, position) }, ?_, rfl, ?_, rfl⟩
        · simp [action, same, node, contains, advanced]
        · simp [eventAt, node]
    · cases step
  · rename_i assertion next
    split at step
    · rename_i holds
      cases step
      refine ⟨other.at next, ?_, ?_, ?_, rfl⟩
      · simp [action, same, node, holds]
      · simp [Thread.at, same]
      · simp [Thread.at, eventAt, node]
    · cases step
  · cases step
    rename_i slot next
    refine ⟨other.saved next slot, ?_, ?_, ?_, rfl⟩
    · simp [action, same, node]
    · simp [Thread.saved, Thread.at, same]
    · simp [Thread.saved, Thread.at, eventAt, node, replay, same]

theorem action_accept_transfer (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) {first other : Thread State length} {tag : Tag}
    (same : other.point = first.point) (step : action graph probe first = .accept tag) :
    action graph probe other = .accept tag := by
  have terminal := action_accept_terminal graph probe first tag step
  cases node : graph first.point.1 <;> simp [RegexPikeVM.terminal, node] at terminal
  cases terminal
  simp [action, same, node]

/-- Ordered alternatives copy the incoming snapshot, append their own bit,
and do not issue a save event. -/
theorem action_branch_data (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) {first left right : Thread State length}
    (step : action graph probe first = .branch left right) :
    eventAt graph first.point = [] ∧ left.registers = first.registers ∧
      right.registers = first.registers := by
  cases node : graph first.point.1 <;> simp only [action, node] at step
  · cases step
  · cases step
  · cases step
  · cases step; simp [eventAt, node, Thread.branch, Thread.at]
  · split at step
    · cases advanced : successor first.point.2 <;> simp [advanced] at step
    · cases step
  · split at step <;> cases step
  · cases step

theorem action_branch_transfer (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) {first left right other : Thread State length}
    (same : other.point = first.point) (step : action graph probe first = .branch left right) :
    ∃ otherLeft otherRight : Thread State length,
      action graph probe other = .branch otherLeft otherRight ∧
        otherLeft.point = left.point ∧ otherRight.point = right.point := by
  cases node : graph first.point.1 <;> simp only [action, node] at step
  · cases step
  · cases step
  · cases step
  · cases step
    rename_i left right
    refine ⟨other.branch left false, other.branch right true, ?_, ?_, ?_⟩
    · simp [action, same, node]
    · simp [Thread.branch, Thread.at, same]
    · simp [Thread.branch, Thread.at, same]
  · split at step
    · cases advanced : successor first.point.2 <;> simp [advanced] at step
    · cases step
  · split at step <;> cases step
  · cases step

/-- The registers of an independently specified trace are exactly the replay
of its save events on the initial snapshot. -/
theorem Trace.capture_replay {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) :
    last.registers = replay (events graph points) first.registers := by
  induction trace with
  | done step _ =>
      simp [events, action_accept_no_event _ _ _ _ step]
  | next step _ ih =>
      obtain ⟨after, otherStep, _, registers, _⟩ := action_next_transfer graph probe rfl step
      have equal : after = _ := Action.next.inj (otherStep.symm.trans step)
      subst after
      rw [events_cons, replay_append, ← registers]
      exact ih
  | left step _ ih =>
      obtain ⟨noEvent, registers, _⟩ := action_branch_data _ _ step
      simpa [events_cons, noEvent, registers] using ih
  | right step _ ih =>
      obtain ⟨noEvent, _, registers⟩ := action_branch_data _ _ step
      simpa [events_cons, noEvent, registers] using ih

/-- Every accepted continuation transfers to arbitrary incoming captures and
choice history at the same point. The suffix code, complete visited-point list
and tag are preserved, not merely the existence of an accepting endpoint. -/
theorem Trace.transfer {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Point State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe (fun thread => eligible thread.point) first code points last tag) :
    ∀ other : Thread State length, other.point = first.point →
      ∃ after : Thread State length,
        Trace graph probe (fun thread => eligible thread.point) other code points after tag ∧
          after.point = last.point := by
  induction trace with
  | done step allowed =>
      intro other same
      refine ⟨other, ?_, same⟩
      have accepted := action_accept_transfer graph probe same step
      simpa [same] using (Trace.done accepted (by simpa [same] using allowed))
  | next step _ ih =>
      intro other same
      obtain ⟨otherTarget, otherStep, sameTarget, _, _⟩ := action_next_transfer graph probe same step
      obtain ⟨after, tail, lastPoint⟩ := ih otherTarget sameTarget
      exact ⟨after, by simpa [same] using Trace.next otherStep tail, lastPoint⟩
  | left step _ ih =>
      intro other same
      obtain ⟨otherLeft, otherRight, otherStep, sameLeft, _⟩ :=
        action_branch_transfer graph probe same step
      obtain ⟨after, tail, lastPoint⟩ := ih otherLeft sameLeft
      exact ⟨after, by simpa [same] using Trace.left otherStep tail, lastPoint⟩
  | right step _ ih =>
      intro other same
      obtain ⟨otherLeft, otherRight, otherStep, _, sameRight⟩ :=
        action_branch_transfer graph probe same step
      obtain ⟨after, tail, lastPoint⟩ := ih otherRight sameRight
      exact ⟨after, by simpa [same] using Trace.right otherStep tail, lastPoint⟩

/-- The transferred snapshot is computed, while its incoming history is kept
as a prefix of the common continuation code. -/
theorem Trace.transfer_with_replay {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Point State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe (fun thread => eligible thread.point) first code points last tag)
    (other : Thread State length) (same : other.point = first.point) :
    ∃ after : Thread State length,
      Trace graph probe (fun thread => eligible thread.point) other code points after tag ∧
        after.point = last.point ∧
        after.registers = replay (events graph points) other.registers ∧
        after.choices = other.choices ++ code := by
  obtain ⟨after, transferred, lastPoint⟩ := Trace.transfer trace other same
  exact ⟨after, transferred, lastPoint, Trace.capture_replay transferred, transferred.choices⟩

/-- The complete relation of accepting suffix codes, visited points and tags
is the same for all incoming snapshots at a fixed point. -/
theorem possibleTrace_iff (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    (first other : Thread State length) (same : other.point = first.point)
    (code : List Bool) (points : List (Point State length)) (tag : Tag) :
    (∃ last, Trace graph probe (fun thread => eligible thread.point) first code points last tag) ↔
      ∃ last, Trace graph probe (fun thread => eligible thread.point) other code points last tag := by
  constructor
  · rintro ⟨last, trace⟩
    obtain ⟨after, transferred, _⟩ := Trace.transfer trace other same
    exact ⟨after, transferred⟩
  · rintro ⟨last, trace⟩
    obtain ⟨after, transferred, _⟩ := Trace.transfer trace first same.symm
    exact ⟨after, transferred⟩

/-- The selected continuation's code and point trace are uniform as well.
Minimality is transported by reflecting every competing trace, not by
assuming that the selected executions already agree. -/
theorem leastSimple_transfer (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    {first last other : Thread State length} (same : other.point = first.point)
    (least : LeastSimple graph probe (fun thread => eligible thread.point) first last) :
    ∃ after, LeastSimple graph probe (fun thread => eligible thread.point) other after ∧
      after.point = last.point := by
  obtain ⟨code, points, tag, trace, simple, minimal⟩ := least
  obtain ⟨after, transferred, sameLast⟩ := Trace.transfer trace other same
  refine ⟨after, ⟨code, points, tag, transferred, simple, ?_⟩, sameLast⟩
  intro otherCode otherPoints otherLast otherTag competing competingSimple
  obtain ⟨back, reflected, _⟩ := Trace.transfer competing first same.symm
  exact minimal otherCode otherPoints back otherTag reflected competingSimple

theorem leastSimple_exists_iff (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    (first other : Thread State length) (same : other.point = first.point) :
    (∃ last, LeastSimple graph probe (fun thread => eligible thread.point) first last) ↔
      ∃ last, LeastSimple graph probe (fun thread => eligible thread.point) other last := by
  constructor
  · rintro ⟨last, least⟩
    obtain ⟨after, transferred, _⟩ := leastSimple_transfer graph probe eligible same least
    exact ⟨after, transferred⟩
  · rintro ⟨last, least⟩
    obtain ⟨after, transferred, _⟩ := leastSimple_transfer graph probe eligible same.symm least
    exact ⟨after, transferred⟩

namespace Controls

private def probe : Probe Unit Unit 1 :=
  ⟨fun _ position => position.val = 0, fun _ _ => false⟩

private def savedBranch : Fin 5 → Node (Fin 5) Unit Unit Nat := fun state =>
  match state.val with
  | 0 => .choice 1 4
  | 1 => .save 0 2
  | 2 => .consume () 3
  | 3 => .accept 17
  | _ => .dead

private def emptyThread : Thread (Fin 5) 1 := ⟨(0, 0), fun _ => none, []⟩
private def populatedThread : Thread (Fin 5) 1 := ⟨(0, 0), fun _ => some 1, [true, true]⟩

private def emptyLast : Thread (Fin 5) 1 :=
  { (emptyThread.branch 1 false).saved 2 0 with point := (3, 1) }

theorem arbitrary_captures_and_prefix_retain_the_same_continuation :
    ∃ after, Trace savedBranch probe (fun _ => true) populatedThread [false]
      [(0, 0), (1, 0), (2, 0), (3, 1)] after 17 ∧
      after.registers 0 = some 0 ∧ after.registers 8 = some 1 ∧
      after.choices = [true, true, false] := by
  have trace : Trace savedBranch probe (fun _ => true) emptyThread [false]
      [(0, 0), (1, 0), (2, 0), (3, 1)] emptyLast 17 :=
    .left rfl (.next rfl (.next rfl (.done rfl rfl)))
  obtain ⟨after, transferred, _, registers, choices⟩ :=
    Trace.transfer_with_replay (eligible := fun _ => true) (first := emptyThread)
      trace populatedThread rfl
  refine ⟨after, transferred, ?_, ?_, choices⟩
  · rw [registers]; simp [events, eventAt, savedBranch, replay, write]
  · rw [registers]; simp [events, eventAt, savedBranch, replay, write, populatedThread]

theorem discarded_branch_writes_are_not_carried_into_the_chosen_branch :
    let registers : Registers 1 := fun _ => none
    let discarded : List (CaptureEvent 1) := [⟨4, 1⟩]
    let chosen : List (CaptureEvent 1) := [⟨0, 0⟩, ⟨0, 1⟩]
    replay chosen registers 0 = some 1 ∧ replay chosen registers 4 = none ∧
      replay (discarded ++ chosen) registers 4 = some 1 := by
  simp [replay, write]

private def accepting : Unit → Node Unit Unit Unit Unit := fun _ => .accept ()
private def withCapture : Thread Unit 1 := ⟨((), 0), fun _ => some 0, []⟩
private def withoutCapture : Thread Unit 1 := ⟨((), 0), fun _ => none, []⟩
private def inspectsCapture (thread : Thread Unit 1) : Bool := (thread.registers 0).isSome

/-- Equal control points cannot justify merging when acceptance reads an
incoming capture. This is a counterexample, not a rejected regex syntax. -/
theorem capture_dependent_eligibility_breaks_uniform_futures :
    withCapture.point = withoutCapture.point ∧
      (∃ last, Trace accepting probe inspectsCapture withCapture [] [((), 0)] last ()) ∧
      ¬ ∃ last, Trace accepting probe inspectsCapture withoutCapture [] [((), 0)] last () := by
  refine ⟨rfl, ⟨withCapture, .done rfl rfl⟩, ?_⟩
  rintro ⟨last, trace⟩
  cases trace with
  | done _ allowed => cases allowed
  | next step _ => cases step

end Controls

#print axioms Trace.capture_replay
#print axioms Trace.transfer_with_replay
#print axioms possibleTrace_iff
#print axioms leastSimple_transfer
#print axioms Controls.capture_dependent_eligibility_breaks_uniform_futures

end Mettapedia.Computability.RegularLanguages.RegexUniformFutures
