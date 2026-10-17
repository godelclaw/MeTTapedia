import Mettapedia.Computability.RegularLanguages.RegexPikeCoverage
import Mettapedia.Computability.RegularLanguages.RegexPikeSelection

/-!
# Actual Pike results have simple accepting capture histories

Pending snapshots carry independently checked path prefixes. At the current
input position, past prefix occurrences are already in the epsilon memo;
earlier input positions cannot be revisited. A fresh visit therefore extends
a simple history. Consumption makes the entire history strictly earlier than
the new input position, justifying the memo reset.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikeSimple

open RegexTaggedGraph RegexSelectionCorrespondence RegexPikeSelection RegexClosureComposition
open OrderedGraphSearch (Point Probe)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

theorem prefix_of_edge (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first target : Thread State length)
    (edge : target ∈ edges graph probe first) :
    ∃ code, Prefix graph probe first code [first.point] target := by
  rw [← RegexPikeCoverage.actionChildren_eq_edges graph probe first] at edge
  cases step : action graph probe first with
  | accept _ | dead => simp [step, RegexMemoizedSearch.actionChildren] at edge
  | next next =>
      simp only [step, RegexMemoizedSearch.actionChildren, List.mem_singleton] at edge
      subst target
      exact ⟨[], .next step (.nil _)⟩
  | branch left right =>
      simp only [step, RegexMemoizedSearch.actionChildren, List.mem_cons, List.not_mem_nil, or_false] at edge
      rcases edge with rfl | rfl
      · exact ⟨[false], .left step (.nil _)⟩
      · exact ⟨[true], .right step (.nil _)⟩

theorem epsilon_edge (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first target : Thread State length)
    (edge : target ∈ epsilonChildren graph probe first) : target ∈ edges graph probe first := by
  cases node : graph first.point.1 <;> simp_all [epsilonChildren]

theorem Prefix.positions_le {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)}
    (history : Prefix graph probe first code points last) :
    ∀ point ∈ points, point.2.val ≤ last.point.2.val := by
  induction history with
  | nil => simp
  | next step tail ih | left step tail ih | right step tail ih =>
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point
        exact Prefix.position_monotone (by first | exact .next step tail | exact .left step tail | exact .right step tail)
      · exact ih point member

def History [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (initial : Thread State length)
    (seen : Finset State) (current : Thread State length) : Prop :=
  ∃ code points, Prefix graph probe initial code points current ∧ points.Nodup ∧
    ∀ point ∈ points, point.2.val < current.point.2.val ∨ point.1 ∈ seen

def SimplePrefix (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (initial current : Thread State length) : Prop :=
  ∃ code points, Prefix graph probe initial code points current ∧ (points ++ [current.point]).Nodup

theorem History.mono [DecidableEq State] {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {initial current : Thread State length}
    {seen larger : Finset State} (history : History graph probe initial seen current)
    (subset : seen ⊆ larger) : History graph probe initial larger current := by
  obtain ⟨code, points, historyPrefix, simple, covered⟩ := history
  exact ⟨code, points, historyPrefix, simple, fun point member =>
    (covered point member).imp id (fun visited => subset visited)⟩

theorem History.fresh [DecidableEq State] {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {initial current : Thread State length}
    {seen : Finset State} (history : History graph probe initial seen current)
    (fresh : current.point.1 ∉ seen) : SimplePrefix graph probe initial current := by
  obtain ⟨code, points, historyPrefix, simple, covered⟩ := history
  refine ⟨code, points, historyPrefix, ?_⟩
  have absent : current.point ∉ points := by
    intro member
    rcases covered current.point member with past | visited
    · omega
    · exact fresh visited
  simpa only [List.concat_eq_append] using List.Nodup.concat absent simple

theorem History.epsilon [DecidableEq State] {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {initial current target : Thread State length}
    {seen : Finset State} (history : History graph probe initial seen current)
    (fresh : current.point.1 ∉ seen) (edge : target ∈ epsilonChildren graph probe current) :
    History graph probe initial (insert current.point.1 seen) target := by
  obtain ⟨code, points, historyPrefix, simple, covered⟩ := history
  obtain ⟨stepCode, step⟩ := prefix_of_edge graph probe current target (epsilon_edge graph probe current target edge)
  have samePosition := epsilonChildren_same_position graph probe current target edge
  have extendedSimple : (points ++ [current.point]).Nodup := by
    have absent : current.point ∉ points := by
      intro member
      rcases covered current.point member with past | visited
      · omega
      · exact fresh visited
    simpa only [List.concat_eq_append] using List.Nodup.concat absent simple
  refine ⟨code ++ stepCode, points ++ [current.point], historyPrefix.append step, extendedSimple, ?_⟩
  intro point member
  rcases List.mem_append.mp member with earlier | last
  · rcases covered point earlier with past | visited
    · exact Or.inl (by simpa only [samePosition] using past)
    · exact Or.inr (Finset.mem_insert_of_mem visited)
  · have same : point = current.point := List.mem_singleton.mp last
    subst point
    exact Or.inr (Finset.mem_insert_self _ _)

/-- Every emitted actual closure snapshot has a simple independent prefix,
including its endpoint and full capture register valuation. -/
theorem closure_simple [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (initial : Thread State length)
    {pending output : List (Thread State length)} {seen final : Finset State}
    (closed : Closure (fun thread => thread.point.1) (epsilonChildren graph probe)
      (fun thread => isFrontier (graph thread.point.1)) pending seen output final) :
    (∀ thread ∈ pending, History graph probe initial seen thread) →
      ∀ thread ∈ output, SimplePrefix graph probe initial thread ∧ isFrontier (graph thread.point.1) = true := by
  induction closed with
  | nil => intro _ thread member; simp at member
  | skip _ _ ih =>
      intro histories
      exact ih (fun thread member => histories thread (by simp [member]))
  | @visit current rest seen later final fresh tail ih =>
      intro histories
      have currentHistory := histories current (by simp)
      have laterHistory : ∀ thread ∈ epsilonChildren graph probe current ++ rest,
          History graph probe initial (insert current.point.1 seen) thread := by
        intro thread member
        rcases List.mem_append.mp member with child | pending
        · exact currentHistory.epsilon fresh child
        · exact (histories thread (by simp [pending])).mono (Finset.subset_insert _ _)
      have laterSimple := ih laterHistory
      intro thread member
      cases emitted : isFrontier (graph current.point.1) with
      | false =>
          simp only [emitted, Bool.false_eq_true, ↓reduceIte] at member
          exact laterSimple thread member
      | true =>
          simp only [emitted, ↓reduceIte, List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨currentHistory.fresh fresh, emitted⟩
          · exact laterSimple thread member

/-- A real consuming step safely starts a fresh epsilon memo. All earlier
history points are now strictly past, so their captures persist without
making any current-position occurrence spuriously fresh. -/
theorem SimplePrefix.consume [DecidableEq State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {initial current target : Thread State length}
    (history : SimplePrefix graph probe initial current)
    (edge : target ∈ edges graph probe current)
    (advances : current.point.2.val < target.point.2.val) : History graph probe initial ∅ target := by
  obtain ⟨code, points, historyPrefix, simple⟩ := history
  obtain ⟨stepCode, step⟩ := prefix_of_edge graph probe current target edge
  refine ⟨code ++ stepCode, points ++ [current.point], historyPrefix.append step, simple, ?_⟩
  intro point member
  apply Or.inl
  rcases List.mem_append.mp member with earlier | last
  · exact lt_of_le_of_lt (Prefix.positions_le historyPrefix point earlier) advances
  · have same : point = current.point := List.mem_singleton.mp last
    simpa only [same] using advances

def SimpleAccept (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    (initial last : Thread State length) (tag : Tag) : Prop :=
  ∃ code points, Trace graph probe eligible initial code points last tag ∧ points.Nodup

theorem terminal_action (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (thread : Thread State length) (tag : Tag)
    (terminal : RegexPikeVM.terminal graph thread = some tag) : action graph probe thread = .accept tag := by
  cases node : graph thread.point.1 <;> simp [RegexPikeVM.terminal, node] at terminal
  cases terminal
  simp [action, node]

theorem SimplePrefix.accepted {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {initial current : Thread State length} {tag : Tag}
    (history : SimplePrefix graph probe initial current)
    (terminal : RegexPikeVM.terminal graph current = some tag) (allowed : eligible current = true) :
    SimpleAccept graph probe eligible initial current tag := by
  obtain ⟨code, points, historyPrefix, simple⟩ := history
  refine ⟨code, points ++ [current.point], ?_, simple⟩
  simpa only [List.append_nil] using
    historyPrefix.follow_trace (.done (terminal_action graph probe current tag terminal) allowed)

/-- Successful actual execution retains a simple accepting prefix, whether
the final candidate was produced now or retained from a prior input layer. -/
theorem execute_simple [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    (initial : Thread State length) (closureFuel inputFuel : Nat) :
    ∀ pending previous last tag,
      (∀ thread ∈ pending, History graph probe initial ∅ thread) →
      (∀ thread found, previous = some (thread, found) → SimpleAccept graph probe eligible initial thread found) →
      RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
        (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
        (RegexPikeVM.terminal graph) eligible closureFuel inputFuel pending previous =
        .finished (some (last, tag)) → SimpleAccept graph probe eligible initial last tag := by
  induction inputFuel with
  | zero => intro pending previous last tag histories previousValid finished; cases finished
  | succ fuel ih =>
      intro pending previous last tag histories previousValid finished
      cases closed : firstVisits (fun thread : Thread State length => thread.point.1)
          (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
          closureFuel pending ∅ with
      | none => simp [RegexPikeVM.execute, closed] at finished
      | some frontier =>
          obtain ⟨final, derivation⟩ := firstVisits_derivation closureFuel pending ∅ frontier closed
          have frontierHistories := closure_simple graph probe initial derivation histories
          let active := (RegexPikeVM.candidates (RegexPikeVM.terminal graph) eligible frontier).1
          let candidate := (RegexPikeVM.candidates (RegexPikeVM.terminal graph) eligible frontier).2
          let selected := candidate.or previous
          let advancing := active.flatMap (edges graph probe)
          have selectedValid : ∀ thread found, selected = some (thread, found) →
              SimpleAccept graph probe eligible initial thread found := by
            intro thread found selectedSame
            cases picked : candidate with
            | none =>
                have same : previous = some (thread, found) := by
                  simpa only [selected, picked, Option.none_or] using selectedSame
                exact previousValid thread found same
            | some pair =>
                have same : pair = (thread, found) := by
                  simpa only [selected, picked, Option.some_or, Option.some.injEq] using selectedSame
                have candidateSame : candidate = some (thread, found) := picked.trans (congrArg some same)
                have member := RegexPikeVM.candidates_selected_sound (RegexPikeVM.terminal graph)
                  eligible frontier thread found candidateSame
                exact (frontierHistories thread member.1).1.accepted member.2.1 member.2.2
          have advancingHistories : ∀ thread ∈ advancing, History graph probe initial ∅ thread := by
            intro thread member
            obtain ⟨source, sourceMember, edge⟩ := List.mem_flatMap.mp member
            have activeSource := RegexPikeVM.candidates_active_mem (RegexPikeVM.terminal graph)
              eligible frontier source sourceMember
            have sourceHistory := frontierHistories source activeSource.1
            have advances := (RegexPikeVM.active_consume_bounds graph probe source
              sourceHistory.2 activeSource.2).2 thread edge
            exact sourceHistory.1.consume edge (by omega)
          simp only [RegexPikeVM.execute, closed] at finished
          change (if advancing.isEmpty then RegexPikeVM.Result.finished selected
            else RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
              (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
              (RegexPikeVM.terminal graph) eligible closureFuel fuel advancing selected) =
              .finished (some (last, tag)) at finished
          cases empty : advancing.isEmpty with
          | true =>
              simp only [empty, ↓reduceIte, RegexPikeVM.Result.finished.injEq] at finished
              exact selectedValid last tag finished
          | false =>
              simp only [empty, Bool.false_eq_true, ↓reduceIte] at finished
              exact ih advancing selected last tag advancingHistories selectedValid finished

/-- The actual Pike winner always has an independently valid point-simple
accepting trace with its exact final captures. This does not yet state that
the trace is the least-priority one. -/
theorem run_match_simple [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    (closureFuel inputFuel : Nat) (initial last : Thread State length) (tag : Tag)
    (finished : RegexPikeVM.run graph probe eligible closureFuel inputFuel [initial] =
      .finished (some (last, tag))) : SimpleAccept graph probe eligible initial last tag := by
  apply execute_simple graph probe eligible initial closureFuel inputFuel [initial] none last tag ?_ ?_ finished
  · intro thread member
    have same : thread = initial := List.mem_singleton.mp member
    subst thread
    exact ⟨[], [], .nil _, by simp, by simp⟩
  · intro thread found impossible
    cases impossible

namespace Controls

private def emptyProbe : Probe Unit Unit 0 := ⟨fun _ _ => false, fun _ _ => false⟩
private def cycleGraph : Fin 4 → Node (Fin 4) Unit Unit Nat := fun state =>
  match state.val with
  | 0 => .choice 1 2
  | 1 => .jump 0
  | 2 => .save 0 3
  | _ => .accept 9
private def cycleFirst : Thread (Fin 4) 0 := ⟨(0, 0), fun _ => none, []⟩
private def cycleLast : Thread (Fin 4) 0 := (cycleFirst.branch 2 true).saved 3 0

theorem epsilon_cycle_winner_has_simple_capture_trace :
    SimpleAccept cycleGraph emptyProbe (fun _ => true) cycleFirst cycleLast 9 :=
  run_match_simple cycleGraph emptyProbe (fun _ => true) 40 2 cycleFirst cycleLast 9 (by rfl)

private def oneProbe : Probe Unit Unit 1 :=
  ⟨fun _ position => position.val < 1, fun _ _ => false⟩
private def reentryGraph : Fin 3 → Node (Fin 3) Unit Unit Nat := fun state =>
  match state.val with
  | 0 => .choice 1 2
  | 1 => .consume () 0
  | _ => .accept 7
private def reentryFirst : Thread (Fin 3) 1 := ⟨(0, 0), fun _ => none, []⟩
private def reentryMiddle : Thread (Fin 3) 1 :=
  { reentryFirst.branch 1 false with point := (0, 1) }
private def reentryLast : Thread (Fin 3) 1 := reentryMiddle.branch 2 true

theorem consuming_reentry_winner_has_simple_trace :
    SimpleAccept reentryGraph oneProbe RegexPikeVM.atInputEnd reentryFirst reentryLast 7 :=
  run_match_simple reentryGraph oneProbe RegexPikeVM.atInputEnd 40 3
    reentryFirst reentryLast 7 (by rfl)

/-- Point simplicity must not be strengthened to state-only simplicity: a
legitimate consumed path revisits the same source occurrence at a new position. -/
theorem state_only_simplicity_rejects_a_real_accepting_trace :
    ∃ code points,
      Trace reentryGraph oneProbe RegexPikeVM.atInputEnd reentryFirst code points reentryLast 7 ∧
      points.Nodup ∧ ¬ (points.map Prod.fst).Nodup := by
  refine ⟨[false, true], [(0, 0), (1, 0), (0, 1), (2, 1)], ?_, by decide, by decide⟩
  have accepted : Trace reentryGraph oneProbe RegexPikeVM.atInputEnd reentryLast []
      [(2, 1)] reentryLast 7 := .done (by rfl) (by rfl)
  have choice : Trace reentryGraph oneProbe RegexPikeVM.atInputEnd reentryMiddle [true]
      [(0, 1), (2, 1)] reentryLast 7 :=
    .right (left := reentryMiddle.branch 1 false) (right := reentryLast) (by rfl) accepted
  have consumed : Trace reentryGraph oneProbe RegexPikeVM.atInputEnd (reentryFirst.branch 1 false) [true]
      [(1, 0), (0, 1), (2, 1)] reentryLast 7 := .next (target := reentryMiddle) (by rfl) choice
  exact .left (left := reentryFirst.branch 1 false) (right := reentryFirst.branch 2 true) (by rfl) consumed

end Controls

end Mettapedia.Computability.RegularLanguages.RegexPikeSimple
