import Mettapedia.Computability.RegularLanguages.RegexClosureComposition

/-!
# Preferred-prefix preservation in the Pike frontier driver

The theorem concerns the real driver, including candidate replacement and
first-visit memoization. A successful preferred root list retains its result
when lower-priority roots are appended. A completed outcome on the combined
call is required: insufficient work is never silently treated as success.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikePrefix

open RegexTaggedGraph RegexPikeVM RegexClosureComposition

universe u v w

variable {Value : Type u} {Key : Type v} {Tag : Type w}

def appendCandidates (first second : List Value × Option (Value × Tag)) :
    List Value × Option (Value × Tag) :=
  match first.2 with
  | some _ => first
  | none => (first.1 ++ second.1, second.2)

theorem candidates_append (accepts : Value → Option Tag) (eligible : Value → Bool)
    (first second : List Value) :
    candidates accepts eligible (first ++ second) =
      appendCandidates (candidates accepts eligible first) (candidates accepts eligible second) := by
  induction first with
  | nil => simp [candidates, appendCandidates]
  | cons head rest ih =>
      cases accepted : accepts head with
      | some tag =>
          cases allowed : eligible head <;> simp [candidates, accepted, allowed, ih, appendCandidates]
      | none =>
          simp only [List.cons_append, candidates, accepted, ih]
          cases next : candidates accepts eligible rest with
          | mk active selected =>
              cases selected <;> simp [appendCandidates]

/-- Preferred roots are not displaced by later roots or by a provisional
candidate from those later roots. This theorem makes no assumption that all
visited control points are failures. -/
theorem execute_prefix_success [DecidableEq Key]
    (key : Value → Key) (epsilon : Value → List Value) (emit : Value → Bool)
    (consume : Value → List Value) (accepts : Value → Option Tag) (eligible : Value → Bool)
    (closureFuel fuel : Nat) :
    ∀ first second previous winner selected,
      execute key epsilon emit consume accepts eligible closureFuel fuel first none =
        .finished (some winner) →
      execute key epsilon emit consume accepts eligible closureFuel fuel (first ++ second) previous =
        .finished selected → selected = some winner := by
  induction fuel with
  | zero => simp [execute]
  | succ fuel ih =>
      intro first second previous winner selected left whole
      cases leftClosed : firstVisits key epsilon emit closureFuel first ∅ with
      | none => simp [execute, leftClosed] at left
      | some before =>
          cases wholeClosed : firstVisits key epsilon emit closureFuel (first ++ second) ∅ with
          | none => simp [execute, wholeClosed] at whole
          | some frontier =>
              obtain ⟨after, rfl⟩ := firstVisits_append_prefix closureFuel first second ∅
                before frontier leftClosed wholeClosed
              cases picked : candidates accepts eligible before with
              | mk active candidate =>
                  cases candidate with
                  | some found =>
                      have same :
                          execute key epsilon emit consume accepts eligible closureFuel (fuel + 1)
                              (first ++ second) previous =
                            execute key epsilon emit consume accepts eligible closureFuel (fuel + 1)
                              first none := by
                        simp [execute, leftClosed, wholeClosed, candidates_append, picked, appendCandidates]
                      exact Result.finished.inj (whole.symm.trans (same.trans left))
                  | none =>
                      simp only [execute, leftClosed, picked, Option.none_or] at left
                      cases empty : (active.flatMap consume).isEmpty with
                      | true => simp [empty] at left
                      | false =>
                          simp only [empty, Bool.false_eq_true, ↓reduceIte] at left
                          have advancing :
                              (active.flatMap consume ++
                                (candidates accepts eligible after).1.flatMap consume).isEmpty = false := by
                            cases activeSteps : active.flatMap consume with
                            | nil => simp [activeSteps] at empty
                            | cons head tail => rfl
                          simp only [execute, wholeClosed, candidates_append, picked, appendCandidates,
                            advancing, Bool.false_eq_true, ↓reduceIte, List.flatMap_append] at whole
                          exact ih (active.flatMap consume)
                            ((candidates accepts eligible after).1.flatMap consume)
                            ((candidates accepts eligible after).2.or previous) winner selected left whole

namespace Controls

private def graph : Fin 5 → Node (Fin 5) Unit Unit Nat := fun pc =>
  match pc.val with
  | 0 => .consume () 1
  | 1 => .accept 7
  | 2 => .consume () 3
  | 3 => .consume () 4
  | _ => .accept 9

private def probe : OrderedGraphSearch.Probe Unit Unit 2 :=
  ⟨fun _ position => position.val < 2, fun _ _ => false⟩

private def initial (pc : Fin 5) : Thread (Fin 5) 2 := ⟨(pc, 0), fun _ => none, []⟩

private def observed : Result (Thread (Fin 5) 2) Nat → Option (Nat × Nat)
  | .finished (some (thread, tag)) => some (thread.point.2.val, tag)
  | _ => none

theorem earlier_short_match_defeats_later_long_match :
    observed (run graph probe (fun _ => true) 40 3 [initial 0, initial 2]) = some (1, 7) := by decide

theorem earlier_long_match_replaces_a_later_provisional_short_match :
    observed (run graph probe (fun _ => true) 40 3 [initial 2, initial 0]) = some (2, 9) := by decide

/-- Additional roots can exhaust a supplied closure budget even though the
preferred singleton already completes. The prefix theorem requires completion. -/
theorem later_roots_can_require_more_work :
    observed (run graph probe (fun _ => true) 2 3 [initial 1]) = some (0, 7) ∧
      run graph probe (fun _ => true) 2 3 [initial 1, initial 4] = .incomplete := by
  constructor
  · decide
  · rfl

end Controls

end Mettapedia.Computability.RegularLanguages.RegexPikePrefix
