import Mettapedia.Computability.RegularLanguages.RegexUniformFutures

/-!
# Histories and local dominance of suspended regex continuations

A prefix certifies the actual capture snapshot of a suspended continuation.
Its point list excludes its endpoint, so concatenation does not duplicate the
join point. These certificates are independent of the frontier scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikeSelection

open RegexTaggedGraph RegexSelectionCorrespondence
open OrderedGraphSearch (Point Probe)
open RegexMatchObservations (HigherPriority)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

/-- Priority fixed at the first different branch cannot be changed by either
continuation's later decisions. Prefix-comparable histories are deliberately
not included in this statement. -/
theorem priority_append {first second : List Bool} (before : HigherPriority first second)
    (firstSuffix secondSuffix : List Bool) :
    HigherPriority (first ++ firstSuffix) (second ++ secondSuffix) := by
  induction before with
  | branch left right => exact .branch _ _
  | «prefix» bit priority ih => exact .prefix bit ih

theorem priority_common_prefix (history : List Bool) {first second : List Bool}
    (before : HigherPriority first second) : HigherPriority (history ++ first) (history ++ second) := by
  induction history with
  | nil => exact before
  | cons bit rest ih => exact .prefix bit ih

/-- A finite prefix follows concrete instructions but need not end at an
accepting node. The endpoint is excluded from its point list. -/
inductive Prefix (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) :
    Thread State length → List Bool → List (Point State length) → Thread State length → Prop
  | nil (first) : Prefix graph probe first [] [] first
  | next {first target code points last} : action graph probe first = .next target →
      Prefix graph probe target code points last →
      Prefix graph probe first code (first.point :: points) last
  | left {first left right code points last} : action graph probe first = .branch left right →
      Prefix graph probe left code points last →
      Prefix graph probe first (false :: code) (first.point :: points) last
  | right {first left right code points last} : action graph probe first = .branch left right →
      Prefix graph probe right code points last →
      Prefix graph probe first (true :: code) (first.point :: points) last

theorem Prefix.choices {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)}
    (history : Prefix graph probe first code points last) : last.choices = first.choices ++ code := by
  induction history with
  | nil => simp
  | next step _ ih => simpa [(action_next_edge _ _ _ _ step).2] using ih
  | left step _ ih => simpa [(action_branch_edges _ _ _ _ _ step).2.2.1, List.append_assoc] using ih
  | right step _ ih => simpa [(action_branch_edges _ _ _ _ _ step).2.2.2, List.append_assoc] using ih

/-- Prefix concatenation preserves every intermediate register snapshot. -/
theorem Prefix.append {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {first middle last : Thread State length}
    {firstCode secondCode : List Bool} {firstPoints secondPoints : List (Point State length)}
    (before : Prefix graph probe first firstCode firstPoints middle)
    (after : Prefix graph probe middle secondCode secondPoints last) :
    Prefix graph probe first (firstCode ++ secondCode) (firstPoints ++ secondPoints) last := by
  induction before with
  | nil => exact after
  | next step _ ih => exact .next step (ih after)
  | left step _ ih => exact .left step (ih after)
  | right step _ ih => exact .right step (ih after)

/-- A suspended history followed by an independent accepting suffix gives a
complete path with the concatenated branch code and point observations. -/
theorem Prefix.follow_trace {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first middle last : Thread State length} {tag : Tag}
    {prefixCode suffixCode : List Bool} {prefixPoints suffixPoints : List (Point State length)}
    (history : Prefix graph probe first prefixCode prefixPoints middle)
    (trace : Trace graph probe eligible middle suffixCode suffixPoints last tag) :
    Trace graph probe eligible first (prefixCode ++ suffixCode) (prefixPoints ++ suffixPoints) last tag := by
  induction history with
  | nil => exact trace
  | next step _ ih => exact .next step (ih trace)
  | left step _ ih => exact .left step (ih trace)
  | right step _ ih => exact .right step (ih trace)

/-- A prefix's captures are computed from its own save events, not imported
from the existence of an eventual successful suffix. -/
theorem Prefix.capture_replay {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)}
    (history : Prefix graph probe first code points last) :
    last.registers = RegexUniformFutures.replay (RegexUniformFutures.events graph points) first.registers := by
  induction history with
  | nil => rfl
  | next step _ ih =>
      obtain ⟨after, otherStep, _, registers, _⟩ :=
        RegexUniformFutures.action_next_transfer graph probe rfl step
      have equal : after = _ := Action.next.inj (otherStep.symm.trans step)
      subst after
      rw [RegexUniformFutures.events_cons, RegexUniformFutures.replay_append, ← registers]
      exact ih
  | left step _ ih =>
      obtain ⟨noEvent, registers, _⟩ := RegexUniformFutures.action_branch_data _ _ step
      simpa [RegexUniformFutures.events_cons, noEvent, registers] using ih
  | right step _ ih =>
      obtain ⟨noEvent, _, registers⟩ := RegexUniformFutures.action_branch_data _ _ step
      simpa [RegexUniformFutures.events_cons, noEvent, registers] using ih

/-- Pending points sharing the same control continuation have identical
suffix possibilities. An earlier divergent prefix remains earlier after that
suffix is transferred, with captures replayed on the earlier snapshot. -/
theorem continuation_dominance (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    {preferred discarded last : Thread State length} {code : List Bool}
    {points : List (Point State length)} {tag : Tag}
    (same : preferred.point = discarded.point)
    (before : HigherPriority preferred.choices discarded.choices)
    (trace : Trace graph probe (fun thread => eligible thread.point) discarded code points last tag) :
    ∃ after, Trace graph probe (fun thread => eligible thread.point) preferred code points after tag ∧
      after.point = last.point ∧ HigherPriority after.choices last.choices ∧
      after.registers = RegexUniformFutures.replay (RegexUniformFutures.events graph points)
        preferred.registers := by
  obtain ⟨after, transferred, sameLast, registers, choices⟩ :=
    RegexUniformFutures.Trace.transfer_with_replay trace preferred same
  refine ⟨after, transferred, sameLast, ?_, registers⟩
  rw [choices, trace.choices]
  exact priority_append before code code

/-- Every real edge preserves or advances input position. Assertions retain
their original-haystack probe and do not change this property. -/
theorem edge_position_le (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first target : Thread State length)
    (edge : target ∈ edges graph probe first) : first.point.2.val ≤ target.point.2.val := by
  cases node : graph first.point.1 with
  | accept tag => simp [edges, node] at edge
  | dead => simp [edges, node] at edge
  | jump next =>
      simp only [edges, node, List.mem_singleton] at edge
      subst target; exact Nat.le_refl _
  | choice left right =>
      simp only [edges, node, List.mem_cons, List.not_mem_nil, or_false] at edge
      rcases edge with same | same <;> subst target <;> exact Nat.le_refl _
  | save slot next =>
      simp only [edges, node, List.mem_singleton] at edge
      subst target; exact Nat.le_refl _
  | consume class_ next =>
      have advances := consume_advances graph probe first target class_ next node edge
      omega
  | assertion assertion_ next =>
      simp only [edges, node] at edge
      split at edge
      · simp only [List.mem_singleton] at edge
        subst target; exact Nat.le_refl _
      · simp at edge

theorem Prefix.position_monotone {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)}
    (history : Prefix graph probe first code points last) : first.point.2.val ≤ last.point.2.val := by
  induction history with
  | nil => exact Nat.le_refl _
  | next step _ ih => exact (edge_position_le _ _ _ _ (action_next_edge _ _ _ _ step).1).trans ih
  | left step _ ih => exact (edge_position_le _ _ _ _ (action_branch_edges _ _ _ _ _ step).1).trans ih
  | right step _ ih => exact (edge_position_le _ _ _ _ (action_branch_edges _ _ _ _ _ step).2.1).trans ih

theorem Trace.positions_ge {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) :
    ∀ point ∈ points, first.point.2.val ≤ point.2.val := by
  induction trace with
  | done _ _ => simp
  | next step _ ih =>
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact Nat.le_refl _
      · exact (edge_position_le _ _ _ _ (action_next_edge _ _ _ _ step).1).trans (ih point member)
  | left step _ ih =>
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact Nat.le_refl _
      · exact (edge_position_le _ _ _ _ (action_branch_edges _ _ _ _ _ step).1).trans (ih point member)
  | right step _ ih =>
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact Nat.le_refl _
      · exact (edge_position_le _ _ _ _ (action_branch_edges _ _ _ _ _ step).2.1).trans (ih point member)

/-- Once consumption advances, every point at an earlier input position is
irrelevant to all continuations. This justifies dropping earlier-position
memo entries; it says nothing about dropping entries at the current position. -/
theorem Trace.avoids_earlier_positions {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag)
    (barrier : Finset (Point State length))
    (earlier : ∀ point ∈ barrier, point.2.val < first.point.2.val) :
    RegexMemoizedSearch.Avoids barrier points := by
  intro point member blocked
  have lower := Trace.positions_ge trace point member
  have upper := earlier point blocked
  omega

namespace Controls

private def probe : Probe Unit Unit 1 :=
  ⟨fun _ position => position.val < 1, fun _ _ => false⟩

private def graph : Fin 3 → Node (Fin 3) Unit Unit Nat := fun state =>
  match state.val with
  | 0 => .save 0 1
  | 1 => .consume () 2
  | _ => .accept 9

private def preferred : Thread (Fin 3) 1 := ⟨(0, 0), fun _ => none, [false]⟩
private def discarded : Thread (Fin 3) 1 := ⟨(0, 0), fun _ => some 1, [true]⟩
private def discardedLast : Thread (Fin 3) 1 :=
  { discarded.saved 1 0 with point := (2, 1) }

theorem preferred_snapshot_replays_a_shared_accepting_suffix :
    ∃ after, Trace graph probe (fun _ => true) preferred [] [(0, 0), (1, 0), (2, 1)] after 9 ∧
      HigherPriority after.choices discardedLast.choices ∧
      after.registers 0 = some 0 ∧ after.registers 4 = none := by
  have trace : Trace graph probe (fun _ => true) discarded []
      [(0, 0), (1, 0), (2, 1)] discardedLast 9 :=
    .next rfl (.next rfl (.done rfl rfl))
  obtain ⟨after, transferred, _, priority, registers⟩ :=
    continuation_dominance graph probe (fun _ => true) (preferred := preferred)
      (discarded := discarded) rfl (.branch [] []) trace
  refine ⟨after, transferred, priority, ?_, ?_⟩
  · rw [registers]; simp [RegexUniformFutures.events, RegexUniformFutures.eventAt,
      RegexUniformFutures.replay, graph, write]
  · rw [registers]; simp [RegexUniformFutures.events, RegexUniformFutures.eventAt,
      RegexUniformFutures.replay, graph, write, preferred]

theorem advancing_continuation_avoids_all_earlier_points :
    let first : Thread (Fin 3) 1 := ⟨(2, 1), fun _ => none, []⟩
    RegexMemoizedSearch.Avoids ({(0, 0), (1, 0), (2, 0)} : Finset (Point (Fin 3) 1))
      [first.point] := by
  dsimp
  have trace : Trace graph probe (fun _ => true)
      (⟨(2, 1), fun _ => none, []⟩ : Thread (Fin 3) 1) [] [(2, 1)]
      ⟨(2, 1), fun _ => none, []⟩ 9 := .done rfl rfl
  apply Trace.avoids_earlier_positions trace
  intro point member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl <;> decide

/-- Being recorded as seen cannot itself establish failed reachability: a
visited continuation may be suspended, and its accepting suffix is still real. -/
theorem visited_does_not_mean_failed :
    let first : Thread (Fin 3) 1 := ⟨(2, 1), fun _ => none, []⟩
    first.point ∈ ({first.point} : Finset (Point (Fin 3) 1)) ∧
      ∃ last, Trace graph probe (fun _ => true) first [] [first.point] last 9 := by
  exact ⟨Finset.mem_singleton_self _, _, .done rfl rfl⟩

end Controls

#print axioms Prefix.follow_trace
#print axioms Prefix.capture_replay
#print axioms continuation_dominance
#print axioms Trace.avoids_earlier_positions

end Mettapedia.Computability.RegularLanguages.RegexPikeSelection
