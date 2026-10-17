import Mettapedia.Computability.RegularLanguages.RegexPikeSelection

/-!
# Simple preferred completions after a control-point merge

A shared accepting suffix can be replayed on a preferred capture snapshot.
Its concatenation with the preferred prefix may have cycles. The independent
memoized-search theorem removes those cycles while respecting an ancestor
barrier. Protecting the common prefix up to the first divergent choice then
preserves strict priority against a simple reference execution.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPriorityCycleCut

open RegexTaggedGraph RegexSelectionCorrespondence RegexPikeSelection RegexMemoizedSearch
open OrderedGraphSearch (Point Probe)
open RegexMatchObservations (HigherPriority)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

theorem trace_weaken_eligibility {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {source target : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe source first code points last tag)
    (weaken : ∀ thread, source thread = true → target thread = true) :
    Trace graph probe target first code points last tag := by
  induction trace with
  | done step allowed => exact .done step (weaken _ allowed)
  | next step _ ih => exact .next step ih
  | left step _ ih => exact .left step ih
  | right step _ ih => exact .right step ih

def endpointEligible [DecidableEq State] (eligible : Point State length → Bool)
    (endpoint : Point State length) (point : Point State length) : Bool :=
  eligible point && decide (point = endpoint)

theorem trace_restrict_endpoint [DecidableEq State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe (fun thread => eligible thread.point) first code points last tag) :
    Trace graph probe (fun thread => endpointEligible eligible last.point thread.point)
      first code points last tag := by
  induction trace with
  | done step allowed => exact .done step (by simp [endpointEligible, allowed])
  | next step _ ih => exact .next step ih
  | left step _ ih => exact .left step ih
  | right step _ ih => exact .right step ih

/-- Cycle removal preserves the accepted endpoint and its tag, but may change
capture registers. It promises no arbitrary preservation of path priority. -/
theorem simple_avoiding_of_trace [DecidableEq State] [Fintype State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe (fun thread => eligible thread.point) first code points last tag)
    (barrier : Finset (Point State length)) (avoids : Avoids barrier points) :
    ∃ nextCode nextPoints after,
      Trace graph probe (fun thread => eligible thread.point) first nextCode nextPoints after tag ∧
      nextPoints.Nodup ∧ Avoids barrier nextPoints ∧ after.point = last.point := by
  let restricted := endpointEligible eligible last.point
  have restrictedTrace : Trace graph probe (fun thread => restricted thread.point)
      first code points last tag := trace_restrict_endpoint trace
  have reachable := trace_reaches restrictedTrace barrier avoids
  have safe : Safe (children graph probe) (goal graph restricted) barrier barrier := by
    intro point member reached
    exact reached.not_blocked member
  let fuel := Fintype.card (Point State length) + 2
  have checked := search_contract graph probe restricted fuel barrier barrier first
    (Finset.Subset.refl _) safe (by dsimp [fuel]; omega)
  cases result : search Thread.point (action graph probe) restricted fuel barrier first with
  | incomplete => simp [result, Contract] at checked
  | absent after =>
      simp only [result, Contract] at checked
      exact False.elim (checked.2.2 reachable)
  | found after afterTag =>
      simp only [result, Contract] at checked
      obtain ⟨nextCode, nextPoints, nextTrace, simple, nextAvoids, _⟩ := checked
      have accepted := nextTrace.sound.2.2
      have samePoint : after.point = last.point :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).2
      have sameTerminal : RegexPikeVM.terminal graph after = RegexPikeVM.terminal graph last := by
        unfold RegexPikeVM.terminal
        rw [congrArg Prod.fst samePoint]
      have sameTag : afterTag = tag := Option.some.inj
        (nextTrace.sound.2.1.symm.trans (sameTerminal.trans trace.sound.2.1))
      subst afterTag
      refine ⟨nextCode, nextPoints, after, ?_, simple, nextAvoids, samePoint⟩
      exact trace_weaken_eligibility nextTrace (fun _ allowed => (Bool.and_eq_true_iff.mp allowed).1)

/-- Protected-common-prefix form of preferred completion. The ancestor
barrier ensures that cycle removal after the divergent branch cannot erase
the branch which established the comparison with the reference execution. -/
theorem preferred_completion_avoiding [DecidableEq State] [Fintype State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {initial preferred : Thread State length}
    {pCode : List Bool} {pPoints : List (Point State length)}
    (preferredHistory : Prefix graph probe initial pCode pPoints preferred) :
    ∀ {qCode : List Bool} {qPoints : List (Point State length)} {discarded : Thread State length},
      Prefix graph probe initial qCode qPoints discarded → preferred.point = discarded.point →
      ∀ {suffixCode : List Bool} {suffixPoints : List (Point State length)}
        {originalLast : Thread State length} {tag : Tag},
        Trace graph probe (fun thread => eligible thread.point) discarded suffixCode suffixPoints originalLast tag →
        (pPoints ++ [preferred.point]).Nodup → (qPoints ++ suffixPoints).Nodup →
        ∀ barrier : Finset (Point State length),
          Avoids barrier (pPoints ++ [preferred.point]) → Avoids barrier (qPoints ++ suffixPoints) →
          HigherPriority pCode qCode →
          ∃ nextCode nextPoints after,
            Trace graph probe (fun thread => eligible thread.point) initial nextCode nextPoints after tag ∧
            nextPoints.Nodup ∧ Avoids barrier nextPoints ∧
            HigherPriority nextCode (qCode ++ suffixCode) ∧ after.point = originalLast.point := by
  induction preferredHistory with
  | nil =>
      intro qCode qPoints discarded discardedHistory same suffixCode suffixPoints originalLast tag tail
        preferredSimple referenceSimple barrier preferredAvoid referenceAvoid higher
      cases higher
  | @next initial target pCode pPoints preferred step preferredTail ih =>
      intro qCode qPoints discarded discardedHistory same suffixCode suffixPoints originalLast tag tail
        preferredSimple referenceSimple barrier preferredAvoid referenceAvoid higher
      cases discardedHistory with
      | nil => cases higher
      | next otherStep discardedTail =>
          have targets := Action.next.inj (step.symm.trans otherStep)
          cases targets
          have preferredPart := admissible_tail preferredSimple preferredAvoid
          have referencePart := admissible_tail referenceSimple referenceAvoid
          obtain ⟨nextCode, nextPoints, after, trace, simple, avoids, priority, endpoint⟩ :=
            ih discardedTail same tail preferredPart.1 referencePart.1 (insert initial.point barrier)
              preferredPart.2 referencePart.2 higher
          have initialOutside := preferredAvoid initial.point (by simp)
          have admissible := admissible_cons initialOutside simple avoids
          exact ⟨nextCode, initial.point :: nextPoints, after, .next step trace,
            admissible.1, admissible.2, priority, endpoint⟩
      | left otherStep _ | right otherStep _ => simp_all
  | @left initial left right pCode pPoints preferred step preferredTail ih =>
      intro qCode qPoints discarded discardedHistory same suffixCode suffixPoints originalLast tag tail
        preferredSimple referenceSimple barrier preferredAvoid referenceAvoid higher
      cases discardedHistory with
      | nil => cases higher
      | next otherStep _ => simp_all
      | @left _ otherLeft otherRight qCode qPoints _ otherStep discardedTail =>
          have branches := Action.branch.inj (step.symm.trans otherStep)
          rcases branches with ⟨rfl, rfl⟩
          have preferredPart := admissible_tail preferredSimple preferredAvoid
          have referencePart := admissible_tail referenceSimple referenceAvoid
          have smaller : HigherPriority pCode qCode := by cases higher with | «prefix» _ priority => exact priority
          obtain ⟨nextCode, nextPoints, after, trace, simple, avoids, priority, endpoint⟩ :=
            ih discardedTail same tail preferredPart.1 referencePart.1 (insert initial.point barrier)
              preferredPart.2 referencePart.2 smaller
          have initialOutside := preferredAvoid initial.point (by simp)
          have admissible := admissible_cons initialOutside simple avoids
          exact ⟨false :: nextCode, initial.point :: nextPoints, after, .left step trace,
            admissible.1, admissible.2, .prefix false priority, endpoint⟩
      | @right _ otherLeft otherRight qCode qPoints _ otherStep discardedTail =>
          have branches := Action.branch.inj (step.symm.trans otherStep)
          rcases branches with ⟨rfl, rfl⟩
          have preferredPart := admissible_tail preferredSimple preferredAvoid
          have referencePart := admissible_tail referenceSimple referenceAvoid
          obtain ⟨replayedLast, replayed, endpoint⟩ := RegexUniformFutures.Trace.transfer tail preferred same
          have joined := preferredTail.follow_trace replayed
          have joinedAvoids : Avoids (insert initial.point barrier) (pPoints ++ suffixPoints) := by
            intro point member
            rcases List.mem_append.mp member with before | after
            · exact preferredPart.2 point (List.mem_append_left _ before)
            · exact referencePart.2 point (List.mem_append_right qPoints after)
          obtain ⟨nextCode, nextPoints, after, trace, simple, avoids, sameEndpoint⟩ :=
            simple_avoiding_of_trace joined (insert initial.point barrier) joinedAvoids
          have initialOutside := preferredAvoid initial.point (by simp)
          have admissible := admissible_cons initialOutside simple avoids
          exact ⟨false :: nextCode, initial.point :: nextPoints, after, .left step trace,
            admissible.1, admissible.2, .branch _ _, sameEndpoint.trans endpoint⟩
  | @right initial left right pCode pPoints preferred step preferredTail ih =>
      intro qCode qPoints discarded discardedHistory same suffixCode suffixPoints originalLast tag tail
        preferredSimple referenceSimple barrier preferredAvoid referenceAvoid higher
      cases discardedHistory with
      | nil => cases higher
      | next otherStep _ => simp_all
      | left _ _ => cases higher
      | @right _ otherLeft otherRight qCode qPoints _ otherStep discardedTail =>
          have branches := Action.branch.inj (step.symm.trans otherStep)
          rcases branches with ⟨rfl, rfl⟩
          have preferredPart := admissible_tail preferredSimple preferredAvoid
          have referencePart := admissible_tail referenceSimple referenceAvoid
          have smaller : HigherPriority pCode qCode := by cases higher with | «prefix» _ priority => exact priority
          obtain ⟨nextCode, nextPoints, after, trace, simple, avoids, priority, endpoint⟩ :=
            ih discardedTail same tail preferredPart.1 referencePart.1 (insert initial.point barrier)
              preferredPart.2 referencePart.2 smaller
          have initialOutside := preferredAvoid initial.point (by simp)
          have admissible := admissible_cons initialOutside simple avoids
          exact ⟨true :: nextCode, initial.point :: nextPoints, after, .right step trace,
            admissible.1, admissible.2, .prefix true priority, endpoint⟩

/-- A globally least simple reference path cannot encounter a strictly
preferred simple prefix at a shared control point. Any resulting cycles can
be cut without losing the first divergent preferred choice. -/
theorem preferred_completion [DecidableEq State] [Fintype State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {initial preferred discarded originalLast : Thread State length}
    {pCode qCode suffixCode : List Bool} {pPoints qPoints suffixPoints : List (Point State length)} {tag : Tag}
    (preferredHistory : Prefix graph probe initial pCode pPoints preferred)
    (discardedHistory : Prefix graph probe initial qCode qPoints discarded)
    (same : preferred.point = discarded.point)
    (preferredSimple : (pPoints ++ [preferred.point]).Nodup)
    (referenceTail : Trace graph probe (fun thread => eligible thread.point)
      discarded suffixCode suffixPoints originalLast tag)
    (referenceSimple : (qPoints ++ suffixPoints).Nodup)
    (higher : HigherPriority pCode qCode) :
    ∃ code points last,
      Trace graph probe (fun thread => eligible thread.point) initial code points last tag ∧
      points.Nodup ∧ HigherPriority code (qCode ++ suffixCode) ∧ last.point = originalLast.point := by
  obtain ⟨code, points, last, trace, simple, _, priority, endpoint⟩ :=
    preferred_completion_avoiding preferredHistory discardedHistory same referenceTail preferredSimple
      referenceSimple ∅ (by simp [Avoids]) (by simp [Avoids]) higher
  exact ⟨code, points, last, trace, simple, priority, endpoint⟩

/-- In a globally least reference execution, no shared point can have a
strictly preferred simple history from the same initial snapshot. This is
the phase-join contradiction used when an actual closure retains its owner. -/
theorem least_reference_rejects_preferred_prefix [DecidableEq State] [Fintype State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {initial preferred discarded originalLast : Thread State length}
    {pCode qCode suffixCode : List Bool} {pPoints qPoints suffixPoints : List (Point State length)} {tag : Tag}
    (preferredHistory : Prefix graph probe initial pCode pPoints preferred)
    (discardedHistory : Prefix graph probe initial qCode qPoints discarded)
    (same : preferred.point = discarded.point)
    (preferredSimple : (pPoints ++ [preferred.point]).Nodup)
    (referenceTail : Trace graph probe (fun thread => eligible thread.point)
      discarded suffixCode suffixPoints originalLast tag)
    (referenceSimple : (qPoints ++ suffixPoints).Nodup)
    (least : LeastSimple graph probe (fun thread => eligible thread.point) initial originalLast) :
    ¬ HigherPriority pCode qCode := by
  intro higher
  obtain ⟨code, points, last, trace, simple, priority, _⟩ :=
    preferred_completion preferredHistory discardedHistory same preferredSimple referenceTail referenceSimple higher
  obtain ⟨leastCode, leastPoints, leastTag, leastTrace, _, minimal⟩ := least
  have choicesSame := leastTrace.choices.symm.trans (discardedHistory.follow_trace referenceTail).choices
  have codeSame : leastCode = qCode ++ suffixCode := List.append_cancel_left choicesSame
  rw [codeSame] at minimal
  rcases minimal code points last tag trace simple with equal | reverse
  · exact higherPriority_irrefl code (by simpa only [equal] using priority)
  · exact higherPriority_asymm priority reverse

theorem priority_cancel_common_prefix (history : List Bool) {first second : List Bool}
    (priority : HigherPriority (history ++ first) (history ++ second)) : HigherPriority first second := by
  induction history with
  | nil => exact priority
  | cons bit history ih =>
      cases priority with
      | «prefix» _ smaller => exact ih smaller

/-- The phase driver stores full choice histories. Their common initial
history cancels before applying the independent prefix contradiction. -/
theorem least_reference_rejects_preferred_choices [DecidableEq State] [Fintype State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {initial preferred discarded originalLast : Thread State length}
    {pCode qCode suffixCode : List Bool} {pPoints qPoints suffixPoints : List (Point State length)} {tag : Tag}
    (preferredHistory : Prefix graph probe initial pCode pPoints preferred)
    (discardedHistory : Prefix graph probe initial qCode qPoints discarded)
    (same : preferred.point = discarded.point)
    (preferredSimple : (pPoints ++ [preferred.point]).Nodup)
    (referenceTail : Trace graph probe (fun thread => eligible thread.point)
      discarded suffixCode suffixPoints originalLast tag)
    (referenceSimple : (qPoints ++ suffixPoints).Nodup)
    (least : LeastSimple graph probe (fun thread => eligible thread.point) initial originalLast) :
    ¬ HigherPriority preferred.choices discarded.choices := by
  intro priority
  rw [preferredHistory.choices, discardedHistory.choices] at priority
  exact least_reference_rejects_preferred_prefix preferredHistory discardedHistory same preferredSimple
    referenceTail referenceSimple least (priority_cancel_common_prefix initial.choices priority)

namespace Controls

private def emptyProbe : Probe Unit Unit 0 := ⟨fun _ _ => false, fun _ _ => false⟩
private def cycleGraph : Fin 2 → Node (Fin 2) Unit Unit Nat := fun state =>
  if state = 0 then .choice 0 1 else .accept 7
private def cycleFirst : Thread (Fin 2) 0 := ⟨(0, 0), fun _ => none, []⟩
private def cycled : Thread (Fin 2) 0 := cycleFirst.branch 0 false
private def cycleLast : Thread (Fin 2) 0 := cycled.branch 1 true

private theorem rawCycle : Trace cycleGraph emptyProbe (fun _ => true)
    cycleFirst [false, true] [(0, 0), (0, 0), (1, 0)] cycleLast 7 := by
  have accepted : Trace cycleGraph emptyProbe (fun _ => true) cycleLast [] [(1, 0)] cycleLast 7 :=
    .done (by rfl) rfl
  have exit : Trace cycleGraph emptyProbe (fun _ => true) cycled [true] [(0, 0), (1, 0)] cycleLast 7 :=
    .right (left := cycled.branch 0 false) (right := cycleLast) (by rfl) accepted
  exact .left (left := cycled) (right := cycleFirst.branch 1 true) (by rfl) exit

theorem cyclic_acceptance_has_a_simple_same_endpoint :
    ∃ code points last,
      Trace cycleGraph emptyProbe (fun _ => true) cycleFirst code points last 7 ∧
      points.Nodup ∧ last.point = cycleLast.point := by
  obtain ⟨code, points, last, trace, simple, _, endpoint⟩ :=
    simple_avoiding_of_trace (eligible := fun _ => true) rawCycle ∅ (by simp [Avoids])
  exact ⟨code, points, last, trace, simple, endpoint⟩

private def crossingGraph : Fin 5 → Node (Fin 5) Unit Unit Nat := fun state =>
  match state.val with
  | 0 => .choice 1 2
  | 1 => .choice 3 4
  | 2 => .jump 3
  | 3 => .jump 1
  | _ => .accept 7
private def crossingFirst : Thread (Fin 5) 0 := ⟨(0, 0), fun _ => none, []⟩
private def preferredStart : Thread (Fin 5) 0 := crossingFirst.branch 1 false
private def preferredEnd : Thread (Fin 5) 0 := preferredStart.branch 3 false
private def discardedStart : Thread (Fin 5) 0 := crossingFirst.branch 2 true
private def discardedEnd : Thread (Fin 5) 0 := discardedStart.at 3
private def referenceBack : Thread (Fin 5) 0 := discardedEnd.at 1
private def referenceLast : Thread (Fin 5) 0 := referenceBack.branch 4 true

/-- The transferred suffix crosses the preferred prefix at state one. The
resulting cycle is removable without erasing the earlier choice at state zero. -/
theorem crossing_preferred_prefix_has_a_simple_preferred_completion :
    ∃ code points last,
      Trace crossingGraph emptyProbe (fun _ => true) crossingFirst code points last 7 ∧
      points.Nodup ∧ HigherPriority code [true, true] ∧ last.point = referenceLast.point := by
  have preferredTail : Prefix crossingGraph emptyProbe preferredStart [false] [(1, 0)] preferredEnd :=
    .left (left := preferredEnd) (right := preferredStart.branch 4 true) (by rfl) (.nil _)
  have preferred : Prefix crossingGraph emptyProbe crossingFirst [false, false]
      [(0, 0), (1, 0)] preferredEnd :=
    .left (left := preferredStart) (right := discardedStart) (by rfl) preferredTail
  have discardedTail : Prefix crossingGraph emptyProbe discardedStart [] [(2, 0)] discardedEnd :=
    .next (target := discardedEnd) (by rfl) (.nil _)
  have discarded : Prefix crossingGraph emptyProbe crossingFirst [true]
      [(0, 0), (2, 0)] discardedEnd :=
    .right (left := preferredStart) (right := discardedStart) (by rfl) discardedTail
  have accepted : Trace crossingGraph emptyProbe (fun _ => true) referenceLast [] [(4, 0)] referenceLast 7 :=
    .done (by rfl) rfl
  have decision : Trace crossingGraph emptyProbe (fun _ => true) referenceBack [true]
      [(1, 0), (4, 0)] referenceLast 7 :=
    .right (left := referenceBack.branch 3 false) (right := referenceLast) (by rfl) accepted
  have tail : Trace crossingGraph emptyProbe (fun _ => true) discardedEnd [true]
      [(3, 0), (1, 0), (4, 0)] referenceLast 7 :=
    .next (target := referenceBack) (by rfl) decision
  exact preferred_completion (eligible := fun _ => true) preferred discarded rfl
    (by decide) tail (by decide) (.branch _ _)

/-- Arbitrary priority preservation under cycle deletion is false. The raw
nullable loop chooses false before exiting, but every simple acceptance must
exit immediately via true. -/
theorem cannot_keep_arbitrary_cyclic_priority :
    ¬ ∃ code points last,
      Trace cycleGraph emptyProbe (fun _ => true) cycleFirst code points last 7 ∧
      points.Nodup ∧ HigherPriority code [true] := by
  rintro ⟨code, points, last, trace, simple, priority⟩
  cases trace with
  | done step _ => simp [action, cycleGraph, cycleFirst] at step
  | next step _ => simp [action, cycleGraph, cycleFirst] at step
  | @left _ left right code tailPoints _ _ step tail =>
      have branches := Action.branch.inj ((show action cycleGraph emptyProbe cycleFirst =
        .branch cycled (cycleFirst.branch 1 true) from rfl).symm.trans step)
      rcases branches with ⟨rfl, rfl⟩
      have repeated : cycleFirst.point ∈ tailPoints := by
        cases tail <;> simp [cycled, cycleFirst, Thread.branch, Thread.at]
      exact (List.nodup_cons.mp simple).1 repeated
  | right _ _ => cases priority with | «prefix» _ impossible => cases impossible

end Controls

end Mettapedia.Computability.RegularLanguages.RegexPriorityCycleCut
