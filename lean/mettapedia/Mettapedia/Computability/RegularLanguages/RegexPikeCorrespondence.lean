import Mettapedia.Computability.RegularLanguages.RegexPhaseComparison
import Mettapedia.Computability.RegularLanguages.RegexPriorityCycleCut
import Mettapedia.Computability.RegularLanguages.RegexPikeOrder
import Mettapedia.Computability.RegularLanguages.RegexPikeCandidate

/-!
# Survival of independently least regex executions

The proof compares actual first-arrival snapshots with a fixed independently
least simple reference execution. A preferred merge would give a better simple
completion; reference minimality therefore forces literal snapshot agreement.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikeCorrespondence

open RegexTaggedGraph RegexSelectionCorrespondence RegexPikeSelection
open RegexClosureComposition RegexEpsilonFirstArrival RegexPikeSimple
open OrderedGraphSearch (Point Probe)
open RegexMatchObservations (HigherPriority)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

theorem trace_points_cons {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) :
    ∃ after, points = first.point :: after := by
  cases trace <;> exact ⟨_, rfl⟩

theorem priority_remove_prefix (history : List Bool) {first second : List Bool}
    (higher : HigherPriority (history ++ first) (history ++ second)) : HigherPriority first second := by
  induction history with
  | nil => exact higher
  | cons bit rest ih =>
      cases higher with
      | «prefix» _ tail => exact ih tail

/-- No actual simple accepting snapshot may precede the independently least
one in its full branch history. -/
theorem least_rejects_higher_accept {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {initial reference other : Thread State length} {tag : Tag}
    (least : LeastSimple graph probe eligible initial reference)
    (accepted : SimpleAccept graph probe eligible initial other tag) :
    ¬ HigherPriority other.choices reference.choices := by
  obtain ⟨referenceCode, referencePoints, referenceTag, referenceTrace, _, minimum⟩ := least
  obtain ⟨otherCode, otherPoints, otherTrace, simple⟩ := accepted
  intro higher
  rw [referenceTrace.choices, otherTrace.choices] at higher
  have codeHigher := priority_remove_prefix initial.choices higher
  rcases minimum otherCode otherPoints other tag otherTrace simple with same | reverse
  · exact higherPriority_irrefl _ (same ▸ codeHigher)
  · exact higherPriority_asymm codeHigher reverse

/-- Split a reference at its first accepting or consuming node. The prefix
uses only original epsilon instructions; all observations concatenate exactly. -/
theorem split_frontier {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) :
    ∃ boundary epsilonCode epsilonPoints suffixCode suffixPoints,
      EpsilonArrival graph probe first epsilonCode epsilonPoints boundary ∧
      Trace graph probe eligible boundary suffixCode suffixPoints last tag ∧
      code = epsilonCode ++ suffixCode ∧ points = epsilonPoints ++ suffixPoints := by
  induction trace with
  | @done first tag step allowed =>
      have frontier : isFrontier (graph first.point.1) = true := by
        have terminal := action_accept_terminal graph probe first tag step
        cases node : graph first.point.1 <;> simp_all [RegexPikeVM.terminal, isFrontier]
      exact ⟨first, [], [], [], [first.point], ⟨.nil _, by simp, frontier⟩,
        .done step allowed, rfl, rfl⟩
  | @next first target code points last tag step tail ih =>
      by_cases frontier : isFrontier (graph first.point.1) = true
      · exact ⟨first, [], [], code, first.point :: points, ⟨.nil _, by simp, frontier⟩,
          .next step tail, rfl, rfl⟩
      · obtain ⟨boundary, eCode, ePoints, sCode, sPoints, arrival, suffix, codeSame, pointsSame⟩ := ih
        refine ⟨boundary, eCode, first.point :: ePoints, sCode, sPoints,
          ⟨.next step arrival.1, ?_, arrival.2.2⟩, suffix, codeSame, by simp [pointsSame]⟩
        intro point member
        rcases List.mem_cons.mp member with rfl | member
        · exact Bool.eq_false_iff.mpr frontier
        · exact arrival.2.1 point member
  | @left first left right code points last tag step tail ih =>
      by_cases frontier : isFrontier (graph first.point.1) = true
      · exact ⟨first, [], [], false :: code, first.point :: points, ⟨.nil _, by simp, frontier⟩,
          .left step tail, rfl, rfl⟩
      · obtain ⟨boundary, eCode, ePoints, sCode, sPoints, arrival, suffix, codeSame, pointsSame⟩ := ih
        refine ⟨boundary, false :: eCode, first.point :: ePoints, sCode, sPoints,
          ⟨.left step arrival.1, ?_, arrival.2.2⟩, suffix, by simp [codeSame], by simp [pointsSame]⟩
        intro point member
        rcases List.mem_cons.mp member with rfl | member
        · exact Bool.eq_false_iff.mpr frontier
        · exact arrival.2.1 point member
  | @right first left right code points last tag step tail ih =>
      by_cases frontier : isFrontier (graph first.point.1) = true
      · exact ⟨first, [], [], true :: code, first.point :: points, ⟨.nil _, by simp, frontier⟩,
          .right step tail, rfl, rfl⟩
      · obtain ⟨boundary, eCode, ePoints, sCode, sPoints, arrival, suffix, codeSame, pointsSame⟩ := ih
        refine ⟨boundary, true :: eCode, first.point :: ePoints, sCode, sPoints,
          ⟨.right step arrival.1, ?_, arrival.2.2⟩, suffix, by simp [codeSame], by simp [pointsSame]⟩
        intro point member
        rcases List.mem_cons.mp member with rfl | member
        · exact Bool.eq_false_iff.mpr frontier
        · exact arrival.2.1 point member

theorem epsilon_arrival_seen [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    {pending output : List (Thread State length)} {final : Finset (Point State length)}
    (closed : Closure Thread.point (epsilonChildren graph probe)
      (fun thread => isFrontier (graph thread.point.1)) pending ∅ output final)
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)}
    (arrival : EpsilonArrival graph probe first code points last) :
    first.point ∈ final → last.point ∈ final := by
  obtain ⟨history, earlier, frontier⟩ := arrival
  induction history with
  | nil => exact id
  | @next first target code points last step tail ih =>
      intro visited
      apply ih (fun point member => earlier point (by simp [member])) frontier
      exact RegexPikeCoverage.point_closure_expands graph probe closed first target visited
        (RegexPikeCoverage.nonfrontier_edge_is_epsilon graph probe first target
          (by rw [earlier first.point (by simp)]; decide) (action_next_edge _ _ _ _ step).1)
  | @left first left right code points last step tail ih =>
      intro visited
      apply ih (fun point member => earlier point (by simp [member])) frontier
      exact RegexPikeCoverage.point_closure_expands graph probe closed first left visited
        (RegexPikeCoverage.nonfrontier_edge_is_epsilon graph probe first left
          (by rw [earlier first.point (by simp)]; decide) (action_branch_edges _ _ _ _ _ step).1)
  | @right first left right code points last step tail ih =>
      intro visited
      apply ih (fun point member => earlier point (by simp [member])) frontier
      exact RegexPikeCoverage.point_closure_expands graph probe closed first right visited
        (RegexPikeCoverage.nonfrontier_edge_is_epsilon graph probe first right
          (by rw [earlier first.point (by simp)]; decide) (action_branch_edges _ _ _ _ _ step).2.1)

theorem epsilon_points_simple {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {boundary last : Thread State length} {code : List Bool}
    {suffixPoints before : List (Point State length)} {tag : Tag}
    (tail : Trace graph probe eligible boundary code suffixPoints last tag)
    (simple : (before ++ suffixPoints).Nodup) : (before ++ [boundary.point]).Nodup := by
  obtain ⟨after, equal⟩ := trace_points_cons tail
  rw [equal] at simple
  have decomposed : ((before ++ [boundary.point]) ++ after).Nodup := by
    simpa only [List.append_assoc, List.singleton_append] using simple
  exact (List.nodup_append.mp decomposed).1

/-- An independently least reference execution survives the actual epsilon
closure with exactly its captures. A strictly preferred competing owner is
excluded by a genuine simple preferred completion. -/
theorem closure_preserves_reference [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (initial reference root : Thread State length)
    (pending frontier : List (Thread State length)) (position : Fin (length + 1))
    (final : Finset State)
    (closed : Closure (fun thread : Thread State length => thread.point.1)
      (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
      pending ∅ frontier final)
    (histories : ∀ thread ∈ pending, History graph probe initial ∅ thread)
    (ordered : pending.Pairwise RegexPikeOrder.Before)
    (samePosition : ∀ thread ∈ pending, thread.point.2 = position)
    (rootMember : root ∈ pending)
    (least : LeastSimple graph probe (fun thread => eligible thread.point) initial reference)
    {prefixCode : List Bool} {prefixPoints : List (Point State length)}
    (history : Prefix graph probe initial prefixCode prefixPoints root)
    {suffixCode : List Bool} {suffixPoints : List (Point State length)} {tag : Tag}
    (tail : Trace graph probe (fun thread => eligible thread.point) root suffixCode suffixPoints reference tag)
    (simple : (prefixPoints ++ suffixPoints).Nodup) :
    ∃ boundary beforeCode beforePoints afterCode afterPoints,
      Prefix graph probe initial beforeCode beforePoints boundary ∧
      Trace graph probe (fun thread => eligible thread.point) boundary afterCode afterPoints reference tag ∧
      (beforePoints ++ afterPoints).Nodup ∧ boundary ∈ frontier ∧ isFrontier (graph boundary.point.1) = true := by
  obtain ⟨boundary, eCode, ePoints, sCode, sPoints, arrival, suffix, _, pointsSame⟩ := split_frontier tail
  have referenceHistory := history.append arrival.1
  have referenceSimple : ((prefixPoints ++ ePoints) ++ sPoints).Nodup := by
    simpa only [pointsSame, List.append_assoc] using simple
  have phaseSimple : (ePoints ++ [boundary.point]).Nodup :=
    epsilon_points_simple suffix (by
      have simpleTail := (List.nodup_append.mp simple).2.1
      simpa only [pointsSame] using simpleTail)
  let targetEligible : Point State length → Bool := fun point => decide (point = boundary.point)
  have referencePhase : Trace (phaseGraph graph) probe (fun thread => targetEligible thread.point)
      root eCode (ePoints ++ [boundary.point]) boundary boundary.point.1 :=
    arrival_phase_trace arrival (by simp [targetEligible])
  have pointClosed := same_position_rekey graph probe position closed samePosition
  simp only [Finset.image_empty] at pointClosed
  have boundarySeen := epsilon_arrival_seen graph probe pointClosed arrival
    (pointClosed.roots_seen root rootMember)
  obtain ⟨rawOwner, rawMember, sameRaw⟩ := RegexPikeCoverage.point_closure_emits graph probe
    pointClosed boundary boundarySeen arrival.2.2
  have rawFrontier : isFrontier (graph rawOwner.point.1) = true := by simpa [sameRaw] using arrival.2.2
  have rawTerminal := action_accept_terminal (phaseGraph graph) probe rawOwner rawOwner.point.1
    (phase_frontier_accept graph probe rawOwner rawFrontier)
  have rawEligible : targetEligible rawOwner.point = true := by simp [targetEligible, sameRaw]
  have frontierSimple := closure_simple graph probe initial closed histories
  cases picked : (RegexPikeVM.candidates (RegexPikeVM.terminal (phaseGraph graph))
      (fun thread => targetEligible thread.point) frontier).2 with
  | none =>
      have rejected := RegexPikeCoverage.candidates_none_rejects
        (RegexPikeVM.terminal (phaseGraph graph)) (fun thread => targetEligible thread.point)
        frontier picked rawOwner rawMember rawOwner.point.1 rawTerminal
      simp [rawEligible] at rejected
  | some pair =>
      obtain ⟨owner, ownerTag⟩ := pair
      have ownerSound := RegexPikeVM.candidates_selected_sound
        (RegexPikeVM.terminal (phaseGraph graph)) (fun thread => targetEligible thread.point)
        frontier owner ownerTag picked
      have ownerFrontier := (frontierSimple owner ownerSound.1).2
      have ownerTerminal := action_accept_terminal (phaseGraph graph) probe owner owner.point.1
        (phase_frontier_accept graph probe owner ownerFrontier)
      have tagSame : ownerTag = owner.point.1 := Option.some.inj (ownerSound.2.1.symm.trans ownerTerminal)
      subst ownerTag
      have before := RegexPhaseComparison.owner_precedes_reference graph probe targetEligible pending
        position frontier final owner root boundary closed samePosition picked ordered rootMember
        eCode (ePoints ++ [boundary.point]) boundary.point.1 referencePhase phaseSimple
      have sameOwner : owner = boundary := by
        rcases before with same | higher
        · exact same
        · obtain ⟨ownerCode, ownerPoints, ownerHistory, ownerSimple⟩ := (frontierSimple owner ownerSound.1).1
          have samePoint : owner.point = boundary.point := of_decide_eq_true ownerSound.2.2
          exact False.elim (RegexPriorityCycleCut.least_reference_rejects_preferred_choices
            ownerHistory referenceHistory samePoint ownerSimple suffix referenceSimple least higher)
      subst owner
      exact ⟨boundary, prefixCode ++ eCode, prefixPoints ++ ePoints, sCode, sPoints,
        referenceHistory, suffix, referenceSimple, ownerSound.1, arrival.2.2⟩

theorem frontier_trace_cases (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (frontier : isFrontier (graph first.point.1) = true)
    (trace : Trace graph probe eligible first code points last tag) :
    (first = last ∧ RegexPikeVM.terminal graph first = some tag ∧ eligible first = true) ∨
      ∃ target nextCode nextPoints,
        RegexPikeVM.terminal graph first = none ∧ action graph probe first = .next target ∧
        Trace graph probe eligible target nextCode nextPoints last tag ∧
        code = nextCode ∧ points = first.point :: nextPoints := by
  cases node : graph first.point.1 with
  | dead | jump _ | save _ _ | choice _ _ | assertion _ _ => simp [isFrontier, node] at frontier
  | accept accepted =>
      cases trace with
      | done step allowed => exact Or.inl ⟨rfl, action_accept_terminal _ _ _ _ step, allowed⟩
      | next step _ | left step _ | right step _ => simp [action, node] at step
  | consume class_ next =>
      cases trace with
      | done step _ =>
          have terminal := action_accept_terminal _ _ _ _ step
          simp [RegexPikeVM.terminal, node] at terminal
      | next step tail => exact Or.inr ⟨_, _, _, by simp [RegexPikeVM.terminal, node], step, tail, rfl, rfl⟩
      | @left _ left right _ _ _ _ step _ | @right _ left right _ _ _ _ step _ =>
          exact False.elim (RegexPikeCoverage.consume_action_not_branch _ _ _ left right class_ next node step)

/-- Every completed driver execution containing an independently least
reference continuation returns that exact reference snapshot and tag. -/
theorem execute_reference [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (initial reference : Thread State length) (tag : Tag)
    (least : LeastSimple graph probe (fun thread => eligible thread.point) initial reference)
    (closureFuel inputFuel : Nat) :
    ∀ (pending : List (Thread State length)) (previous selected : Option (Thread State length × Tag))
      (position : Fin (length + 1)) (root : Thread State length)
      (prefixCode : List Bool) (prefixPoints : List (Point State length))
      (suffixCode : List Bool) (suffixPoints : List (Point State length)),
      (∀ thread ∈ pending, History graph probe initial ∅ thread) →
      pending.Pairwise RegexPikeOrder.Before →
      (∀ thread ∈ pending, thread.point.2 = position) → root ∈ pending →
      Prefix graph probe initial prefixCode prefixPoints root →
      Trace graph probe (fun thread => eligible thread.point) root suffixCode suffixPoints reference tag →
      (prefixPoints ++ suffixPoints).Nodup →
      RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
        (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
        (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
        closureFuel inputFuel pending previous = .finished selected →
      selected = some (reference, tag) := by
  induction inputFuel with
  | zero => intros; contradiction
  | succ fuel ih =>
      intro pending previous selected position root prefixCode prefixPoints suffixCode suffixPoints
        histories ordered synchronous rootMember history tail simple finished
      cases closed : firstVisits (fun thread : Thread State length => thread.point.1)
          (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
          closureFuel pending ∅ with
      | none => simp [RegexPikeVM.execute, closed] at finished
      | some frontier =>
          obtain ⟨final, derivation⟩ := firstVisits_derivation closureFuel pending ∅ frontier closed
          have frontierHistories := closure_simple graph probe initial derivation histories
          have frontierOrder := RegexPikeOrder.close_ordered graph probe closureFuel pending frontier ordered closed
          have frontierPosition := close_same_position graph probe closureFuel position pending frontier synchronous closed
          obtain ⟨boundary, beforeCode, beforePoints, afterCode, afterPoints,
            beforeHistory, afterTrace, referenceSimple, boundaryMember, boundaryFrontier⟩ :=
            closure_preserves_reference graph probe eligible initial reference root pending frontier position final
              derivation histories ordered synchronous rootMember least history tail simple
          let active := (RegexPikeVM.candidates (RegexPikeVM.terminal graph)
            (fun thread => eligible thread.point) frontier).1
          let candidate := (RegexPikeVM.candidates (RegexPikeVM.terminal graph)
            (fun thread => eligible thread.point) frontier).2
          let advancing := active.flatMap (edges graph probe)
          have noEarlier : ∀ value ∈ frontier, ∀ found,
              RegexPikeVM.terminal graph value = some found → eligible value.point = true →
                ¬ RegexPikeOrder.Before value boundary := by
            intro value member found terminal allowed higher
            have accepted := (frontierHistories value member).1.accepted
              (eligible := fun thread => eligible thread.point) terminal allowed
            apply least_rejects_higher_accept least accepted
            rw [afterTrace.choices]
            simpa only [List.append_nil] using priority_append higher [] afterCode
          have advancingHistories : ∀ thread ∈ advancing, History graph probe initial ∅ thread := by
            intro thread member
            obtain ⟨source, sourceMember, edge⟩ := List.mem_flatMap.mp member
            have actual := RegexPikeVM.candidates_active_mem (RegexPikeVM.terminal graph)
              (fun thread => eligible thread.point) frontier source sourceMember
            have sourceHistory := frontierHistories source actual.1
            have advances := (RegexPikeVM.active_consume_bounds graph probe source
              sourceHistory.2 actual.2).2 thread edge
            exact sourceHistory.1.consume edge (by omega)
          have advancingOrder := RegexPikeOrder.advancing_ordered graph probe
            (fun thread => eligible thread.point) closureFuel pending frontier ordered closed
          rcases frontier_trace_cases graph probe (fun thread => eligible thread.point)
              boundaryFrontier afterTrace with accepted | consuming
          · obtain ⟨same, terminal, allowed⟩ := accepted
            subst boundary
            have picked : candidate = some (reference, tag) := RegexPikeOrder.candidates_selects_reference
              (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
              RegexPikeOrder.Before frontier reference tag frontierOrder boundaryMember terminal allowed noEarlier
            simp only [RegexPikeVM.execute, closed] at finished
            change (if advancing.isEmpty then RegexPikeVM.Result.finished (candidate.or previous)
              else RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
                (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
                (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
                closureFuel fuel advancing (candidate.or previous)) = .finished selected at finished
            rw [picked, Option.some_or] at finished
            cases empty : advancing.isEmpty with
            | true => simpa only [empty, ↓reduceIte, RegexPikeVM.Result.finished.injEq] using finished.symm
            | false =>
                simp only [empty, Bool.false_eq_true, ↓reduceIte] at finished
                apply RegexPikeCandidate.retain_least_candidate graph probe eligible initial reference tag
                  least closureFuel fuel advancing selected advancingHistories ?_ finished
                intro thread member
                obtain ⟨source, sourceMember, edge⟩ := List.mem_flatMap.mp member
                have before := RegexPikeOrder.candidates_active_before_selected (RegexPikeVM.terminal graph)
                  (fun thread => eligible thread.point) RegexPikeOrder.Before frontier reference tag
                  frontierOrder picked source sourceMember
                have actual := RegexPikeVM.candidates_active_mem (RegexPikeVM.terminal graph)
                  (fun thread => eligible thread.point) frontier source sourceMember
                have properties := RegexPikeOrder.consuming_edges_properties graph probe source
                  (frontierHistories source actual.1).2 actual.2
                change HigherPriority source.choices reference.choices at before
                rw [properties.2 thread edge]
                exact before
          · obtain ⟨target, nextCode, nextPoints, notTerminal, step, nextTrace, _, pointsSame⟩ := consuming
            have boundaryActive : boundary ∈ active := RegexPikeOrder.candidates_retains_active
              (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
              RegexPikeOrder.Before frontier boundary frontierOrder boundaryMember notTerminal noEarlier
            have edge := (action_next_edge graph probe boundary target step).1
            have targetMember : target ∈ advancing := List.mem_flatMap.mpr ⟨boundary, boundaryActive, edge⟩
            have advances := (RegexPikeVM.active_consume_bounds graph probe boundary
              boundaryFrontier notTerminal).2 target edge
            have newHistory : Prefix graph probe initial beforeCode (beforePoints ++ [boundary.point]) target := by
              simpa only [List.append_nil] using beforeHistory.append (Prefix.next step (.nil target))
            have newSimple : ((beforePoints ++ [boundary.point]) ++ nextPoints).Nodup := by
              simpa only [pointsSame, List.append_assoc, List.singleton_append] using referenceSimple
            have advancingPosition : ∀ thread ∈ advancing, thread.point.2 = target.point.2 := by
              intro thread member
              obtain ⟨source, sourceMember, sourceEdge⟩ := List.mem_flatMap.mp member
              have actual := RegexPikeVM.candidates_active_mem (RegexPikeVM.terminal graph)
                (fun thread => eligible thread.point) frontier source sourceMember
              have sourceAdvances := (RegexPikeVM.active_consume_bounds graph probe source
                (frontierHistories source actual.1).2 actual.2).2 thread sourceEdge
              have sourcePosition := frontierPosition source actual.1
              have boundaryPosition := frontierPosition boundary boundaryMember
              apply Fin.ext
              rw [sourceAdvances, advances, sourcePosition, boundaryPosition]
            have notEmpty : advancing.isEmpty = false := by
              cases empty : advancing with
              | nil => simp [empty] at targetMember
              | cons first rest => rfl
            simp only [RegexPikeVM.execute, closed] at finished
            change (if advancing.isEmpty then RegexPikeVM.Result.finished (candidate.or previous)
              else RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
                (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
                (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
                closureFuel fuel advancing (candidate.or previous)) = .finished selected at finished
            simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at finished
            exact ih advancing (candidate.or previous) selected target.point.2 target beforeCode
              (beforePoints ++ [boundary.point]) nextCode nextPoints advancingHistories advancingOrder
              advancingPosition targetMember newHistory nextTrace newSimple finished

theorem run_of_leastSimple [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first last : Thread State length) (tag : Tag)
    (least : LeastSimple graph probe (fun thread => eligible thread.point) first last)
    (terminal : RegexPikeVM.terminal graph last = some tag) (closureFuel inputFuel : Nat)
    (selected : Option (Thread State length × Tag))
    (completed : RegexPikeVM.run graph probe (fun thread => eligible thread.point)
      closureFuel inputFuel [first] = .finished selected) : selected = some (last, tag) := by
  have leastCopy := least
  obtain ⟨code, points, someTag, trace, simple, _⟩ := leastCopy
  have sameTag : someTag = tag := Option.some.inj (trace.sound.2.1.symm.trans terminal)
  subst someTag
  apply execute_reference graph probe eligible first last tag least closureFuel inputFuel
    [first] none selected first.point.2 first [] [] code points ?_ (by simp) ?_ (by simp)
    (.nil first) trace (by simpa only [Simple, List.nil_append] using simple) completed
  · intro thread member
    have same : thread = first := List.mem_singleton.mp member
    subst thread
    exact ⟨[], [], .nil first, by simp, by simp⟩
  · intro thread member
    have same : thread = first := List.mem_singleton.mp member
    rw [same]

/-- Selected-capture adequacy for the actual Pike driver. The independent
right-hand side is the least simple accepting graph execution; it does not
refer to DFS or define success by the returned Pike result. -/
theorem run_leastSimple [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first last : Thread State length) (tag : Tag)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) :
    RegexPikeVM.run graph probe (fun thread => eligible thread.point) closureFuel inputFuel [first] =
      .finished (some (last, tag)) ↔
      LeastSimple graph probe (fun thread => eligible thread.point) first last ∧
        RegexPikeVM.terminal graph last = some tag := by
  constructor
  · intro matched
    obtain ⟨code, points, trace, simple⟩ := RegexPikeSimple.run_match_simple graph probe
      (fun thread => eligible thread.point) closureFuel inputFuel first last tag matched
    obtain ⟨reference, least⟩ := leastSimple_exists graph probe (fun thread => eligible thread.point) first
      ⟨code, points, last, tag, trace, simple⟩
    have leastCopy := least
    obtain ⟨referenceCode, referencePoints, referenceTag, referenceTrace, _, _⟩ := leastCopy
    have predicted := run_of_leastSimple graph probe eligible first reference referenceTag least
      referenceTrace.sound.2.1 closureFuel inputFuel (some (last, tag)) matched
    have equal : (last, tag) = (reference, referenceTag) := Option.some.inj predicted
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    exact ⟨least, referenceTrace.sound.2.1⟩
  · rintro ⟨least, terminal⟩
    cases result : RegexPikeVM.run graph probe (fun thread => eligible thread.point)
        closureFuel inputFuel [first] with
    | incomplete =>
        exact False.elim (RegexPikeVM.run_ne_incomplete graph probe (fun thread => eligible thread.point)
          first closureFuel inputFuel closureEnough inputEnough result)
    | finished selected =>
        have predicted := run_of_leastSimple graph probe eligible first last tag least terminal
          closureFuel inputFuel selected result
        exact congrArg RegexPikeVM.Result.finished predicted

/-- Pike and the already verified global memoized DFS return the same full
selected snapshot and tag, with independently earned sufficient budgets. -/
theorem pike_dfs_selected_iff [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first last : Thread State length) (tag : Tag)
    (closureFuel inputFuel dfsFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel)
    (dfsEnough : Fintype.card (Point State length) + 1 < dfsFuel) :
    RegexPikeVM.run graph probe (fun thread => eligible thread.point) closureFuel inputFuel [first] =
      .finished (some (last, tag)) ↔
      RegexMemoizedSearch.taggedSearch graph probe eligible dfsFuel first = .found last tag := by
  rw [run_leastSimple graph probe eligible first last tag closureFuel inputFuel closureEnough inputEnough,
    RegexMemoizedSearch.taggedSearch_leastSimple graph probe eligible first last tag dfsFuel dfsEnough]

namespace Controls

private def probe (length : Nat) : Probe Unit Unit length :=
  ⟨fun _ position => position.val < length, fun _ _ => false⟩

private def initial {count : Nat} (state : Fin count) (length : Nat) : Thread (Fin count) length :=
  ⟨(state, 0), fun _ => none, []⟩

private def greedy : Fin 5 → Node (Fin 5) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .save 0 1
  | 1 => .choice 2 3
  | 2 => .consume () 1
  | 3 => .save 1 4
  | _ => .accept ()

private def greedyWinner : Thread (Fin 5) 3 :=
  ⟨(4, 3), write (write (fun _ => none) 0 0) 1 3, [false, false, false, true]⟩

private theorem greedy_matched : RegexPikeVM.run greedy (probe 3) (fun _ => true)
    24 4 [initial 0 3] = .finished (some (greedyWinner, ())) := rfl

theorem actual_greedy_captures_are_independently_least :
    LeastSimple greedy (probe 3) (fun _ => true) (initial 0 3) greedyWinner ∧
      greedyWinner.registers 0 = some 0 ∧ greedyWinner.registers 1 = some 3 := by
  exact ⟨((run_leastSimple greedy (probe 3) (fun _ => true) (initial 0 3) greedyWinner ()
    24 4 (by decide) (by decide)).mp greedy_matched).1, rfl, rfl⟩

private def alternatives : Fin 5 → Node (Fin 5) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 3
  | 1 => .consume () 2
  | 2 => .accept ()
  | 3 => .consume () 4
  | _ => .consume () 2

private def completeWinner : Thread (Fin 5) 2 := ⟨(2, 2), fun _ => none, [true]⟩
private def atEnd (point : Point (Fin 5) 2) : Bool := point.2.val == 2

theorem fullmatch_restricts_paths_before_selected_capture_adequacy :
    LeastSimple alternatives (probe 2) (fun thread => atEnd thread.point)
      (initial 0 2) completeWinner ∧ completeWinner.choices = [true] := by
  have matched : RegexPikeVM.run alternatives (probe 2) (fun thread => atEnd thread.point)
      24 3 [initial 0 2] = .finished (some (completeWinner, ())) := rfl
  exact ⟨((run_leastSimple alternatives (probe 2) atEnd (initial 0 2) completeWinner ()
    24 3 (by decide) (by decide)).mp matched).1, rfl⟩

/-- An independently valid least path does not turn an exhausted execution
into a completed match. The sufficient-budget hypotheses have content. -/
theorem insufficient_budget_does_not_refute_the_reference_path :
    LeastSimple greedy (probe 3) (fun _ => true) (initial 0 3) greedyWinner ∧
      RegexPikeVM.run greedy (probe 3) (fun _ => true) 24 0 [initial 0 3] = .incomplete := by
  exact ⟨actual_greedy_captures_are_independently_least.1, rfl⟩

end Controls

#print axioms closure_preserves_reference
#print axioms execute_reference
#print axioms run_of_leastSimple
#print axioms run_leastSimple
#print axioms pike_dfs_selected_iff
#print axioms Controls.actual_greedy_captures_are_independently_least
#print axioms Controls.fullmatch_restricts_paths_before_selected_capture_adequacy
#print axioms Controls.insufficient_budget_does_not_refute_the_reference_path

end Mettapedia.Computability.RegularLanguages.RegexPikeCorrespondence
