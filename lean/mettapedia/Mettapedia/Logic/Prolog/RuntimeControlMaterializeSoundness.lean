import Mettapedia.Logic.Prolog.RuntimeControl
import Mettapedia.Logic.LP.RuntimeMaterializeSoundness

/-!
# Heap-extension soundness for typed Prolog goal materialization

Typed Prolog control is represented in the same LP graph heap.  This module
proves that lowering a source `Goal` to runtime instructions only allocates in
that heap; it never gains a private store or an untracked mutation path.
-/

namespace Mettapedia.Logic.Prolog.RuntimeControl

open Mettapedia.Logic
open LP.RuntimeTerm LP.RuntimeMaterialize
open LP.RuntimeUnificationSoundness

private theorem pure_extends {sigma : LP.LPSignature} {alpha : Type _}
    (value : alpha) :
    ∀ (s0 s1 : BuilderState sigma) (result : alpha)
      (trail : Array (TrailEntry sigma)),
      (pure value : BuilderM sigma alpha).run s0 = .ok (result, s1) →
      Extends { heap := s0.heap, trail } { heap := s1.heap, trail } := by
  intro s0 s1 result trail run
  change Except.ok (value, s0) = Except.ok (result, s1) at run
  cases run
  exact .refl _

private theorem bind_extends {sigma : LP.LPSignature}
    {alpha beta : Type _} (action : BuilderM sigma alpha)
    (next : alpha → BuilderM sigma beta)
    (actionExtends : ∀ (s0 s1 : BuilderState sigma) (value : alpha)
      (trail : Array (TrailEntry sigma)),
      action.run s0 = .ok (value, s1) →
      Extends { heap := s0.heap, trail } { heap := s1.heap, trail })
    (nextExtends : ∀ (value : alpha) (s0 s1 : BuilderState sigma) (result : beta)
      (trail : Array (TrailEntry sigma)),
      (next value).run s0 = .ok (result, s1) →
      Extends { heap := s0.heap, trail } { heap := s1.heap, trail }) :
    ∀ (s0 s1 : BuilderState sigma) (result : beta)
      (trail : Array (TrailEntry sigma)),
      (action >>= next).run s0 = .ok (result, s1) →
      Extends { heap := s0.heap, trail } { heap := s1.heap, trail } := by
  intro s0 s1 result trail run
  change (BuilderM.bind action next).run s0 = .ok (result, s1) at run
  cases hAction : action.run s0 with
  | error error => simp [BuilderM.bind, hAction] at run
  | ok pair =>
      obtain ⟨value, middle⟩ := pair
      simp only [BuilderM.bind, hAction] at run
      exact (actionExtends s0 middle value trail hAction).trans
        (nextExtends value middle s1 result trail run)

/-- Lowering any typed source goal into the canonical runtime instruction
shape is an allocation-only `Extends` history.  Nested conjunction and
control payloads are traversed structurally, so no latent branch payload is
treated as opaque. -/
theorem materializeGoalAux_extends {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] :
    ∀ (goal : Goal sigma) {s0 s1 : BuilderState sigma}
      {goals : List (RuntimeGoal sigma)} (trail : Array (TrailEntry sigma)),
      (materializeGoalAux goal).run s0 = .ok (goals, s1) →
      Extends { heap := s0.heap, trail } { heap := s1.heap, trail } := by
  intro goal
  induction goal with
  | call atom =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeAtomAux atom)
        (fun copied => pure ([RuntimeGoal.call copied] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => materializeAtomAux_extends atom trail h)
        (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
        s0 s1 goals trail (by
          simpa [materializeGoalAux] using run)
  | succeed =>
      intro s0 s1 goals trail run
      exact pure_extends ([] : List (RuntimeGoal sigma)) s0 s1 goals trail
        (by simpa [materializeGoalAux] using run)
  | fail =>
      intro s0 s1 goals trail run
      exact pure_extends [RuntimeGoal.fail] s0 s1 goals trail
        (by simpa [materializeGoalAux] using run)
  | cut =>
      intro s0 s1 goals trail run
      exact pure_extends [RuntimeGoal.cut] s0 s1 goals trail
        (by simpa [materializeGoalAux] using run)
  | conj left right leftIH rightIH =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeGoalAux left) (fun copiedLeft => do
          let copiedRight ← materializeGoalAux right
          pure (copiedLeft ++ copiedRight))
        (fun _ _ _ trail h => leftIH trail h)
        (fun copiedLeft s0 s1 result trail h =>
          bind_extends (materializeGoalAux right)
            (fun copiedRight => pure (copiedLeft ++ copiedRight))
            (fun _ _ _ trail h => rightIH trail h)
            (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
            s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | disj left right leftIH rightIH =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeGoalAux left) (fun copiedLeft => do
          let copiedRight ← materializeGoalAux right
          pure ([RuntimeGoal.disj copiedLeft copiedRight] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => leftIH trail h)
        (fun copiedLeft s0 s1 result trail h =>
          bind_extends (materializeGoalAux right)
            (fun copiedRight => pure
              ([RuntimeGoal.disj copiedLeft copiedRight] : List (RuntimeGoal sigma)))
            (fun _ _ _ trail h => rightIH trail h)
            (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
            s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | ifThenElse condition thenBranch elseBranch conditionIH thenIH elseIH =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeGoalAux condition) (fun copiedCondition => do
          let copiedThen ← materializeGoalAux thenBranch
          let copiedElse ← materializeGoalAux elseBranch
          pure ([RuntimeGoal.ifThenElse copiedCondition copiedThen copiedElse] :
            List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => conditionIH trail h)
        (fun copiedCondition s0 s1 result trail h =>
          bind_extends (materializeGoalAux thenBranch) (fun copiedThen => do
              let copiedElse ← materializeGoalAux elseBranch
              pure ([RuntimeGoal.ifThenElse copiedCondition copiedThen copiedElse] :
                List (RuntimeGoal sigma)))
            (fun _ _ _ trail h => thenIH trail h)
            (fun copiedThen s0 s1 result trail h =>
              bind_extends (materializeGoalAux elseBranch)
                (fun copiedElse => pure
                  ([RuntimeGoal.ifThenElse copiedCondition copiedThen copiedElse] :
                    List (RuntimeGoal sigma)))
                (fun _ _ _ trail h => elseIH trail h)
                (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
                s0 s1 result trail h)
            s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | softIfThenElse condition thenBranch elseBranch conditionIH thenIH elseIH =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeGoalAux condition) (fun copiedCondition => do
          let copiedThen ← materializeGoalAux thenBranch
          let copiedElse ← materializeGoalAux elseBranch
          pure ([RuntimeGoal.softIfThenElse copiedCondition copiedThen copiedElse] :
            List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => conditionIH trail h)
        (fun copiedCondition s0 s1 result trail h =>
          bind_extends (materializeGoalAux thenBranch) (fun copiedThen => do
              let copiedElse ← materializeGoalAux elseBranch
              pure ([RuntimeGoal.softIfThenElse copiedCondition copiedThen copiedElse] :
                List (RuntimeGoal sigma)))
            (fun _ _ _ trail h => thenIH trail h)
            (fun copiedThen s0 s1 result trail h =>
              bind_extends (materializeGoalAux elseBranch)
                (fun copiedElse => pure
                  ([RuntimeGoal.softIfThenElse copiedCondition copiedThen copiedElse] :
                    List (RuntimeGoal sigma)))
                (fun _ _ _ trail h => elseIH trail h)
                (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
                s0 s1 result trail h)
            s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | once goal ih =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeGoalAux goal)
        (fun copied => pure ([RuntimeGoal.once copied] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => ih trail h)
        (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
        s0 s1 goals trail (by
          simpa [materializeGoalAux] using run)
  | transaction goal ih =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeGoalAux goal)
        (fun copied => pure ([RuntimeGoal.transaction copied] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => ih trail h)
        (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | neg goal ih =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeGoalAux goal)
        (fun copied => pure ([RuntimeGoal.neg copied] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => ih trail h)
        (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | unify left right =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeTermAux left) (fun copiedLeft => do
          let copiedRight ← materializeTermAux right
          pure ([RuntimeGoal.unify copiedLeft copiedRight] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => materializeTermAux_extends left trail h)
        (fun copiedLeft s0 s1 result trail h =>
          bind_extends (materializeTermAux right)
            (fun copiedRight => pure
              ([RuntimeGoal.unify copiedLeft copiedRight] : List (RuntimeGoal sigma)))
            (fun _ _ _ trail h => materializeTermAux_extends right trail h)
            (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
            s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | notUnify left right =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeTermAux left) (fun copiedLeft => do
          let copiedRight ← materializeTermAux right
          pure ([RuntimeGoal.notUnify copiedLeft copiedRight] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => materializeTermAux_extends left trail h)
        (fun copiedLeft s0 s1 result trail h =>
          bind_extends (materializeTermAux right)
            (fun copiedRight => pure
              ([RuntimeGoal.notUnify copiedLeft copiedRight] : List (RuntimeGoal sigma)))
            (fun _ _ _ trail h => materializeTermAux_extends right trail h)
            (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
            s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | isVar term =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeTermAux term)
        (fun copied => pure ([RuntimeGoal.isVar copied] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => materializeTermAux_extends term trail h)
        (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
        s0 s1 goals trail (by
          simpa [materializeGoalAux] using run)
  | findall template generator bag generatorIH =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeTermAux template) (fun copiedTemplate => do
          let copiedGenerator ← materializeGoalAux generator
          let copiedBag ← materializeTermAux bag
          pure ([RuntimeGoal.findall copiedTemplate copiedGenerator copiedBag] :
            List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => materializeTermAux_extends template trail h)
        (fun copiedTemplate s0 s1 result trail h =>
          bind_extends (materializeGoalAux generator) (fun copiedGenerator => do
              let copiedBag ← materializeTermAux bag
              pure ([RuntimeGoal.findall copiedTemplate copiedGenerator copiedBag] :
                List (RuntimeGoal sigma)))
            (fun _ _ _ trail h => generatorIH trail h)
            (fun copiedGenerator s0 s1 result trail h =>
              bind_extends (materializeTermAux bag)
                (fun copiedBag => pure
                  ([RuntimeGoal.findall copiedTemplate copiedGenerator copiedBag] :
                    List (RuntimeGoal sigma)))
                (fun _ _ _ trail h => materializeTermAux_extends bag trail h)
                (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
                s0 s1 result trail h)
            s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | «catch» guarded catcher recovery guardedIH recoveryIH =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeGoalAux guarded) (fun copiedGuarded => do
          let copiedCatcher ← materializeTermAux catcher
          let copiedRecovery ← materializeGoalAux recovery
          pure ([RuntimeGoal.catch copiedGuarded copiedCatcher copiedRecovery] :
            List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => guardedIH trail h)
        (fun copiedGuarded s0 s1 result trail h =>
          bind_extends (materializeTermAux catcher) (fun copiedCatcher => do
              let copiedRecovery ← materializeGoalAux recovery
              pure ([RuntimeGoal.catch copiedGuarded copiedCatcher copiedRecovery] :
                List (RuntimeGoal sigma)))
            (fun _ _ _ trail h => materializeTermAux_extends catcher trail h)
            (fun copiedCatcher s0 s1 result trail h =>
              bind_extends (materializeGoalAux recovery)
                (fun copiedRecovery => pure
                  ([RuntimeGoal.catch copiedGuarded copiedCatcher copiedRecovery] :
                    List (RuntimeGoal sigma)))
                (fun _ _ _ trail h => recoveryIH trail h)
                (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
                s0 s1 result trail h)
            s0 s1 result trail h)
        s0 s1 goals trail (by simpa [materializeGoalAux] using run)
  | «throw» ball =>
      intro s0 s1 goals trail run
      exact bind_extends (materializeTermAux ball)
        (fun copied => pure ([RuntimeGoal.throw copied] : List (RuntimeGoal sigma)))
        (fun _ _ _ trail h => materializeTermAux_extends ball trail h)
        (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
        s0 s1 goals trail (by
          simpa [materializeGoalAux] using run)

/-- The checked public goal materializer is therefore allocation-only in the
canonical heap. -/
theorem materializeGoal_extends {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] {memory : Memory sigma} {goal : Goal sigma}
    {result : MaterializedGoal sigma}
    (run : materializeGoal memory goal = .ok result) :
    Extends memory result.memory := by
  unfold materializeGoal at run
  cases checked : runChecked (materializeGoalAux goal) memory.heap with
  | error error => rw [checked] at run; cases run
  | ok pair =>
      obtain ⟨goals, state⟩ := pair
      rw [checked] at run
      dsimp only at run
      by_cases wellFormed : RuntimeGoal.checkAll state.heap goals = true
      · rw [if_pos wellFormed] at run
        cases run
        obtain ⟨_, _, raw, _, _⟩ := runChecked_ok checked
        simpa [BuilderState.start] using
          materializeGoalAux_extends goal memory.trail raw
      · rw [if_neg wellFormed] at run
        cases run

/-- Materializing a typed clause is likewise only the head allocation followed
by the structural body allocation in the same builder state. -/
theorem materializeClauseAux_extends {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] (clause : Clause sigma) :
    ∀ {s0 s1 : BuilderState sigma} {result : RuntimeClause sigma}
      (trail : Array (TrailEntry sigma)),
      (materializeClauseAux clause).run s0 = .ok (result, s1) →
      Extends { heap := s0.heap, trail } { heap := s1.heap, trail } := by
  intro s0 s1 result trail run
  exact bind_extends (materializeAtomAux clause.head) (fun head => do
      let body ← materializeGoalAux clause.body
      pure { head, body })
    (fun _ _ _ trail h => materializeAtomAux_extends clause.head trail h)
    (fun head s0 s1 result trail h =>
      bind_extends (materializeGoalAux clause.body)
        (fun body => pure { head, body })
        (fun _ _ _ trail h => materializeGoalAux_extends clause.body trail h)
        (fun _ s0 s1 result trail h => pure_extends _ s0 s1 result trail h)
        s0 s1 result trail h)
    s0 s1 result trail (by simpa [materializeClauseAux] using run)

/-- The checked public clause materializer is allocation-only in the canonical
heap. -/
theorem materializeClause_extends {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] {memory : Memory sigma} {clause : Clause sigma}
    {result : MaterializedClause sigma}
    (run : materializeClause memory clause = .ok result) :
    Extends memory result.memory := by
  unfold materializeClause at run
  cases checked : runChecked (materializeClauseAux clause) memory.heap with
  | error error => rw [checked] at run; cases run
  | ok pair =>
      obtain ⟨copied, state⟩ := pair
      rw [checked] at run
      dsimp only at run
      by_cases wellFormed : copied.checkWellFormed state.heap = true
      · rw [if_pos wellFormed] at run
        cases run
        obtain ⟨_, _, raw, _, _⟩ := runChecked_ok checked
        simpa [BuilderState.start] using
          materializeClauseAux_extends clause memory.trail raw
      · rw [if_neg wellFormed] at run
        cases run

/-- The typed Prolog clause-materializer adapter meets the same heap-history
contract as the LP materializer.  This is the source-level bridge required to
carry a branch checkpoint across a nested typed call without inventing a
Prolog-specific heap. -/
theorem clauseMaterializer_extends {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars] {memory : Memory sigma.scoped}
    {scope : Nat} {clause : Clause sigma}
    {result : LP.RuntimeQuery.MaterializedBody sigma (RuntimeGoal sigma.scoped)}
    (run : (clauseMaterializer (sigma := sigma)).materialize memory scope clause =
      .ok result) :
    Extends memory result.memory := by
  unfold clauseMaterializer at run
  cases copied : materializeClause memory (clause.atScope scope) with
  | error error => simp [copied] at run
  | ok body =>
      simp [copied] at run
      cases run
      exact materializeClause_extends copied

end Mettapedia.Logic.Prolog.RuntimeControl
