import Mettapedia.Languages.MeTTa.HE.ArgFrameMachine
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Argument traversal retaining selected values and pending siblings

The reference evaluator is the existing argument-product fold. The machine
instead keeps a stack of source frames and pending candidate frames. Selecting
a candidate starts its remaining arguments with that value and its bindings;
its siblings stay suspended below that child. Completed argument tuples are
published in depth-first order, including repeated equal occurrences.

The argument evaluator is an explicit parameter of this coarse traversal.
Its internal execution, effects and native realization require separate
contracts; one argument request is not assigned constant physical work.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ArgTraversal

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev ArgumentEvaluator := Atom → Atom → Bindings → ResultList
abbrev Configuration := List ArgEvalFrame

/-- The pending source and body denotations compose in exact stack order. -/
def residual (evaluate : ArgumentEvaluator) (frames : Configuration) : ResultList :=
  frames.flatMap (ArgEvalFrame.run evaluate)

/-- Enter the next argument, enter one selected child, retire an exhausted
candidate frame, or publish one completely assembled tuple. -/
def machine (evaluate : ArgumentEvaluator) :
    Machine Configuration ResultPair Configuration Empty where
  step
    | [] => some (.finish [])
    | .source ⟨done, [], env⟩ :: rest =>
        some (.publish [(.expression done, env)] rest)
    | .source ⟨done, (arg, type) :: arguments, env⟩ :: rest =>
        some (.silent
          (.body ⟨evaluate arg type env, ⟨done, arguments, env⟩⟩ :: rest))
    | .body ⟨[], _⟩ :: rest => some (.silent rest)
    | .body ⟨(value, env) :: pending, suspended⟩ :: rest =>
        some (.silent
          (.source ⟨suspended.done ++ [value], suspended.remaining, env⟩ ::
            .body ⟨pending, suspended⟩ :: rest))

/-- Every traversal transition preserves exactly the pending source tuples;
only publication removes a completed occurrence. -/
theorem step_residual (evaluate : ArgumentEvaluator) (frames : Configuration) :
    match (machine evaluate).step frames with
    | some (.silent next) => residual evaluate frames = residual evaluate next
    | some (.publish events next) =>
        residual evaluate frames = events ++ residual evaluate next
    | some (.finish final) => residual evaluate frames = residual evaluate final
    | _ => False := by
  cases frames with
  | nil => rfl
  | cons frame rest =>
      cases frame with
      | source source =>
          rcases source with ⟨done, remaining, env⟩
          cases remaining with
          | nil => simp [machine, residual, ArgEvalFrame.run, ArgEvalFrame.runFromSource]
          | cons argument arguments =>
              rcases argument with ⟨arg, type⟩
              simp [machine, residual, ArgEvalFrame.run]
      | body body =>
          rcases body with ⟨pending, suspended⟩
          cases pending with
          | nil => simp [machine, residual, ArgEvalFrame.run]
          | cons result results =>
              rcases result with ⟨value, env⟩
              simp [machine, residual, ArgEvalFrame.run, List.append_assoc]

/-- Every retained outcome has its complete pending source meaning. -/
def pending (evaluate : ArgumentEvaluator) :
    Outcome Configuration Configuration Empty → ResultList
  | .finished frames | .exhausted frames | .stuck frames => residual evaluate frames
  | .suspended request _ => nomatch request
  | .faulted => []

/-- Every finite run partitions the independently defined ordered result list
into its established prefix and the exact meaning of its retained stack. -/
theorem run_preserves_residual (evaluate : ArgumentEvaluator) (fuel : Nat)
    (frames : Configuration) :
    ((machine evaluate).run fuel frames).1 ++
        pending evaluate ((machine evaluate).run fuel frames).2 =
      residual evaluate frames := by
  induction fuel generalizing frames with
  | zero => simp [Machine.run, pending]
  | succ fuel ih =>
      have preserved := step_residual evaluate frames
      cases frames with
      | nil => simp [Machine.run, machine, pending, residual]
      | cons frame rest =>
          cases frame with
          | source source =>
              rcases source with ⟨done, remaining, env⟩
              cases remaining with
              | nil =>
                  simpa [Machine.run, machine, pending, residual, ArgEvalFrame.run,
                    ArgEvalFrame.runFromSource] using
                    congrArg ([(.expression done, env)] ++ ·) (ih rest)
              | cons argument arguments =>
                  rcases argument with ⟨arg, type⟩
                  simpa [Machine.run, machine] using
                    (ih (.body ⟨evaluate arg type env, ⟨done, arguments, env⟩⟩ :: rest)).trans
                      (by simpa [machine] using preserved.symm)
          | body body =>
              rcases body with ⟨candidates, suspended⟩
              cases candidates with
              | nil =>
                  simpa [Machine.run, machine] using
                    (ih rest).trans (by simpa [machine] using preserved.symm)
              | cons candidate candidates =>
                  rcases candidate with ⟨value, env⟩
                  simpa [Machine.run, machine] using
                    (ih (.source ⟨suspended.done ++ [value], suspended.remaining, env⟩ ::
                      .body ⟨candidates, suspended⟩ :: rest)).trans
                      (by simpa [machine] using preserved.symm)

/-- Prefix resumption keeps the selected argument values, their bindings and
all suspended candidate siblings at their exact saved endpoints. -/
theorem resume_after_prefix (evaluate : ArgumentEvaluator) (first second : Nat)
    (frames saved : Configuration) (events : ResultList)
    (paused : (machine evaluate).run first frames = (events, .exhausted saved)) :
    (machine evaluate).run (first + second) frames =
      (events ++ ((machine evaluate).run second saved).1,
        ((machine evaluate).run second saved).2) :=
  (machine evaluate).established_and_pending first second frames saved events paused

/-- Remaining traversal work includes candidate selection, child traversal,
retirement and tuple publication, with the argument evaluator priced separately. -/
def sourceWork (evaluate : ArgumentEvaluator) : ArgSourceFrame → Nat
  | ⟨_, [], _⟩ => 1
  | ⟨done, (arg, type) :: remaining, env⟩ =>
      2 + ((evaluate arg type env).map fun (value, nextEnv) =>
        1 + sourceWork evaluate ⟨done ++ [value], remaining, nextEnv⟩).sum
termination_by source => source.remaining.length

def frameWork (evaluate : ArgumentEvaluator) : ArgEvalFrame → Nat
  | .source source => sourceWork evaluate source
  | .body body =>
      1 + (body.pending.map fun (value, env) =>
        1 + sourceWork evaluate
          ⟨body.suspended.done ++ [value], body.suspended.remaining, env⟩).sum

def work (evaluate : ArgumentEvaluator) (frames : Configuration) : Nat :=
  (frames.map (frameWork evaluate)).sum

/-- Every nonterminal traversal step decreases the explicit remaining-work
measure. An exhausted candidate frame cannot restart a later argument. -/
theorem step_work_decreases (evaluate : ArgumentEvaluator) (frames : Configuration) :
    match (machine evaluate).step frames with
    | some (.silent next) | some (.publish _ next) =>
        work evaluate next < work evaluate frames
    | some (.finish _) => frames = []
    | _ => False := by
  cases frames with
  | nil => rfl
  | cons frame rest =>
      cases frame with
      | source source =>
          rcases source with ⟨done, remaining, env⟩
          cases remaining with
          | nil => simp [machine, work, frameWork, sourceWork]
          | cons argument remaining =>
              rcases argument with ⟨arg, type⟩
              simp [machine, work, frameWork, sourceWork]
      | body body =>
          rcases body with ⟨pending, suspended⟩
          cases pending with
          | nil => simp [machine, work, frameWork]
          | cons result results =>
              rcases result with ⟨value, env⟩
              simp [machine, work, frameWork]
              omega

/-- Administrative traversal settles between published tuples. This is a
rank for the outer traversal, not a termination theorem for argument evaluation. -/
def productive (evaluate : ArgumentEvaluator) : (machine evaluate).Productive where
  rank := work evaluate
  silent_decreases := by
    intro frames next stepped
    have decreases := step_work_decreases evaluate frames
    simpa [stepped] using decreases
  moves := by
    intro frames
    cases frames with
    | nil => simp [machine]
    | cons frame rest =>
        cases frame with
        | source source =>
            rcases source with ⟨done, remaining, env⟩
            cases remaining <;> simp [machine]
        | body body =>
            rcases body with ⟨pending, suspended⟩
            cases pending <;> simp [machine]

/-- A finite argument-product traversal completes within its derived work
bound; its argument computations must already supply their finite result lists. -/
theorem run_complete_of_work_lt (evaluate : ArgumentEvaluator) (fuel : Nat)
    (frames : Configuration) (bound : work evaluate frames < fuel) :
    ((machine evaluate).run fuel frames).2 = .finished [] := by
  induction fuel generalizing frames with
  | zero => omega
  | succ fuel ih =>
      have decreases := step_work_decreases evaluate frames
      cases frames with
      | nil => rfl
      | cons frame rest =>
          cases frame with
          | source source =>
              rcases source with ⟨done, remaining, env⟩
              cases remaining with
              | nil =>
                  simp only [machine] at decreases
                  simpa [Machine.run, machine] using ih rest (by omega)
              | cons argument remaining =>
                  rcases argument with ⟨arg, type⟩
                  simp only [machine] at decreases
                  simpa [Machine.run, machine] using
                    ih (.body ⟨evaluate arg type env, ⟨done, remaining, env⟩⟩ :: rest)
                      (by omega)
          | body body =>
              rcases body with ⟨pending, suspended⟩
              cases pending with
              | nil =>
                  simp only [machine] at decreases
                  simpa [Machine.run, machine] using ih rest (by omega)
              | cons result results =>
                  rcases result with ⟨value, env⟩
                  simp only [machine] at decreases
                  simpa [Machine.run, machine] using
                    ih (.source ⟨suspended.done ++ [value], suspended.remaining, env⟩ ::
                      .body ⟨results, suspended⟩ :: rest) (by omega)

/-- The independently recursive source argument evaluator is exactly the
ordered output of the explicit traversal from every source frame. -/
theorem run_initial_eq_reference (evaluate : ArgumentEvaluator) (source : ArgSourceFrame) :
    ((machine evaluate).run (work evaluate [.source source] + 1) [.source source]).1 =
      ArgEvalFrame.runFromSource evaluate source := by
  have completed := run_complete_of_work_lt evaluate
    (work evaluate [.source source] + 1) [.source source] (by omega)
  have preserved := run_preserves_residual evaluate
    (work evaluate [.source source] + 1) [.source source]
  simpa [completed, pending, residual, ArgEvalFrame.run] using preserved

end Mettapedia.Languages.MeTTa.HE.ArgTraversal
