import Mettapedia.Computability.RegularLanguages.RegexPikeSelection

/-!
# Rigidity of simple histories at a shared control point

Two point-simple paths with the same start and endpoint cannot differ merely
by adding more choice bits to one code. Such an extension would revisit the
endpoint. Actual deterministic actions therefore identify equal codes with
equal capture snapshots; genuinely different paths have a divergent choice.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPrefixRigidity

open RegexTaggedGraph RegexSelectionCorrespondence RegexPikeSelection
open OrderedGraphSearch (Point Probe)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

theorem Prefix.return_is_empty {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)}
    (history : Prefix graph probe first code points last)
    (simple : (points ++ [last.point]).Nodup) (same : first.point = last.point) :
    first = last ∧ code = [] ∧ points = [] := by
  cases history with
  | nil first => exact ⟨rfl, rfl, rfl⟩
  | next step tail | left step tail | right step tail =>
      have fresh := (List.nodup_cons.mp simple).1
      exact False.elim (fresh (List.mem_append_right _ (by simp [same])))

/-- Prefix-comparable simple histories to the same point are the same path,
including all capture registers. Future equivalence alone would not prove this. -/
theorem Prefix.prefix_free {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)}
    (history : Prefix graph probe first code points last)
    (simple : (points ++ [last.point]).Nodup) :
    ∀ {otherCode otherPoints otherLast},
      Prefix graph probe first otherCode otherPoints otherLast →
      (otherPoints ++ [otherLast.point]).Nodup → last.point = otherLast.point →
      (code <+: otherCode ∨ otherCode <+: code) →
      code = otherCode ∧ points = otherPoints ∧ last = otherLast := by
  induction history with
  | nil first =>
      intro otherCode otherPoints otherLast other otherSimple same _
      obtain ⟨equal, emptyCode, emptyPoints⟩ := Prefix.return_is_empty other otherSimple same
      exact ⟨emptyCode.symm, emptyPoints.symm, equal⟩
  | @next first target code points last step tail ih =>
      intro otherCode otherPoints otherLast other otherSimple same comparable
      cases other with
      | nil =>
          obtain ⟨_, emptyCode, emptyPoints⟩ :=
            Prefix.return_is_empty (Prefix.next step tail) simple same.symm
          simp at emptyPoints
      | next otherStep other =>
          have targets := Action.next.inj (step.symm.trans otherStep)
          cases targets
          obtain ⟨codes, pointLists, endpoints⟩ :=
            ih (List.nodup_cons.mp simple).2 other (List.nodup_cons.mp otherSimple).2 same comparable
          exact ⟨codes, congrArg (first.point :: ·) pointLists, endpoints⟩
      | left otherStep other | right otherStep other => simp_all
  | @left first left right code points last step tail ih =>
      intro otherCode otherPoints otherLast other otherSimple same comparable
      cases other with
      | nil =>
          obtain ⟨_, _, emptyPoints⟩ := Prefix.return_is_empty (Prefix.left step tail) simple same.symm
          simp at emptyPoints
      | next otherStep other => simp_all
      | left otherStep other =>
          have branches := Action.branch.inj (step.symm.trans otherStep)
          rcases branches with ⟨rfl, rfl⟩
          obtain ⟨codes, pointLists, endpoints⟩ :=
            ih (List.nodup_cons.mp simple).2 other (List.nodup_cons.mp otherSimple).2 same
              (by simpa using comparable)
          exact ⟨congrArg (false :: ·) codes, congrArg (first.point :: ·) pointLists, endpoints⟩
      | right otherStep other => simp_all
  | @right first left right code points last step tail ih =>
      intro otherCode otherPoints otherLast other otherSimple same comparable
      cases other with
      | nil =>
          obtain ⟨_, _, emptyPoints⟩ := Prefix.return_is_empty (Prefix.right step tail) simple same.symm
          simp at emptyPoints
      | next otherStep other => simp_all
      | left otherStep other => simp_all
      | right otherStep other =>
          have branches := Action.branch.inj (step.symm.trans otherStep)
          rcases branches with ⟨rfl, rfl⟩
          obtain ⟨codes, pointLists, endpoints⟩ :=
            ih (List.nodup_cons.mp simple).2 other (List.nodup_cons.mp otherSimple).2 same
              (by simpa using comparable)
          exact ⟨congrArg (true :: ·) codes, congrArg (first.point :: ·) pointLists, endpoints⟩

theorem code_comparison (first second : List Bool) :
    RegexMatchObservations.HigherPriority first second ∨
      RegexMatchObservations.HigherPriority second first ∨ first <+: second ∨ second <+: first := by
  induction first generalizing second with
  | nil => exact Or.inr (Or.inr (Or.inl (by simp)))
  | cons bit rest ih =>
      cases second with
      | nil => exact Or.inr (Or.inr (Or.inr (by simp)))
      | cons other tail =>
          cases bit <;> cases other
          · rcases ih tail with before | before | pref | pref
            · exact Or.inl (.prefix _ before)
            · exact Or.inr (Or.inl (.prefix _ before))
            · exact Or.inr (Or.inr (Or.inl (by simpa using pref)))
            · exact Or.inr (Or.inr (Or.inr (by simpa using pref)))
          · exact Or.inl (.branch _ _)
          · exact Or.inr (Or.inl (.branch _ _))
          · rcases ih tail with before | before | pref | pref
            · exact Or.inl (.prefix _ before)
            · exact Or.inr (Or.inl (.prefix _ before))
            · exact Or.inr (Or.inr (Or.inl (by simpa using pref)))
            · exact Or.inr (Or.inr (Or.inr (by simpa using pref)))

/-- At a shared endpoint, two simple histories either agree in every field or
have a genuine priority divergence. Ancestor/code-prefix collisions are ruled
out by point simplicity, not by treating a visited point as unsuccessful. -/
theorem Prefix.equal_or_priority {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {first left right : Thread State length}
    {leftCode rightCode : List Bool} {leftPoints rightPoints : List (Point State length)}
    (before : Prefix graph probe first leftCode leftPoints left)
    (after : Prefix graph probe first rightCode rightPoints right)
    (leftSimple : (leftPoints ++ [left.point]).Nodup)
    (rightSimple : (rightPoints ++ [right.point]).Nodup) (same : left.point = right.point) :
    (leftCode = rightCode ∧ leftPoints = rightPoints ∧ left = right) ∨
      RegexMatchObservations.HigherPriority leftCode rightCode ∨
      RegexMatchObservations.HigherPriority rightCode leftCode := by
  rcases code_comparison leftCode rightCode with earlier | later | pref | pref
  · exact Or.inr (Or.inl earlier)
  · exact Or.inr (Or.inr later)
  · exact Or.inl (Prefix.prefix_free before leftSimple after rightSimple same (Or.inl pref))
  · exact Or.inl (Prefix.prefix_free before leftSimple after rightSimple same (Or.inr pref))

namespace Controls

private def probe : Probe Unit Unit 0 := ⟨fun _ _ => false, fun _ _ => false⟩
private def graph : Fin 4 → Node (Fin 4) Unit Unit Nat := fun state =>
  match state.val with
  | 0 => .jump 1
  | 1 => .save 0 2
  | 2 => .choice 3 3
  | _ => .accept 7
private def first : Thread (Fin 4) 0 := ⟨(0, 0), fun _ => none, []⟩
private def saved : Thread (Fin 4) 0 := (first.at 1).saved 2 0

theorem deterministic_prefix_retains_written_capture :
    Prefix graph probe first [] [first.point, (first.at 1).point] saved ∧
      saved.registers 0 = some 0 := by
  exact ⟨.next rfl (.next rfl (.nil _)), rfl⟩

theorem divergent_arrivals_to_shared_point_remain_ordered :
    Prefix graph probe saved [false] [saved.point] (saved.branch 3 false) ∧
      Prefix graph probe saved [true] [saved.point] (saved.branch 3 true) ∧
      (saved.branch 3 false).point = (saved.branch 3 true).point ∧
      RegexMatchObservations.HigherPriority (saved.branch 3 false).choices
        (saved.branch 3 true).choices := by
  exact ⟨.left rfl (.nil _), .right rfl (.nil _), rfl, .branch [] []⟩

private def loopGraph : Fin 2 → Node (Fin 2) Unit Unit Nat := fun state =>
  if state = 0 then .choice 0 1 else .accept 7
private def loopFirst : Thread (Fin 2) 0 := ⟨(0, 0), fun _ => none, []⟩

/-- Without point simplicity, comparable codes need not identify a snapshot. -/
theorem cyclic_prefix_does_not_satisfy_rigidity :
    Prefix loopGraph probe loopFirst [false] [loopFirst.point] (loopFirst.branch 0 false) ∧
      loopFirst.point = (loopFirst.branch 0 false).point ∧
      [] <+: [false] ∧ loopFirst ≠ loopFirst.branch 0 false ∧
      ¬([loopFirst.point, (loopFirst.branch 0 false).point]).Nodup := by
  refine ⟨.left rfl (.nil _), rfl, by simp, ?_, by simp [loopFirst, Thread.branch, Thread.at]⟩
  intro same
  have codes := congrArg Thread.choices same
  simp [loopFirst, Thread.branch, Thread.at] at codes

end Controls

end Mettapedia.Computability.RegularLanguages.RegexPrefixRigidity
