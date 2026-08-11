import Mettapedia.Logic.Prolog.Syntax
import Mettapedia.Logic.LP.RuntimeMaterialize

/-!
# Runtime form of canonical Prolog control

This module materializes `Logic.Prolog.Goal` into the same heap and variable
map used by `Logic.LP.RuntimeQuery`.  It is not a resolver: it owns no search
state, choice stack, trail, or scope supply.

Conjunction becomes a goal stack.  Ordinary calls remain the established
`Logic.LP.RuntimeMaterialize.RuntimeAtom`; control constructors retain their
typed structure instead of being encoded as distinguished predicate symbols.
-/

namespace Mettapedia.Logic.Prolog.RuntimeControl

open Mettapedia.Logic
open LP.RuntimeTerm LP.RuntimeMaterialize

/-- Runtime control whose term arguments are roots in the canonical LP heap.
The list fields are ordered goal stacks; their head executes first. -/
inductive RuntimeGoal (sigma : LP.LPSignature) where
  | call (atom : RuntimeAtom sigma)
  | fail
  | cut
  | disj (left right : List (RuntimeGoal sigma))
  | ifThenElse (condition thenBranch elseBranch : List (RuntimeGoal sigma))
  | once (goals : List (RuntimeGoal sigma))
  | neg (goals : List (RuntimeGoal sigma))
  | unify (left right : Addr)
  | notUnify (left right : Addr)
  | isVar (term : Addr)
  | findall (template : Addr) (generator : List (RuntimeGoal sigma))
      (bag : Addr)
  | catch (guarded : List (RuntimeGoal sigma)) (catcher : Addr)
      (recovery : List (RuntimeGoal sigma))
  | throw (ball : Addr)

namespace RuntimeGoal

/-- The exact runtime embedding of a pure ordered atom list. -/
def calls {sigma : LP.LPSignature}
    (atoms : List (RuntimeAtom sigma)) : List (RuntimeGoal sigma) :=
  atoms.map .call

/-! The mutually recursive checker follows the nested goal-stack shape
directly.  This makes every descendant instruction part of the checked
boundary rather than treating lists of control as opaque payloads. -/
mutual
  /-- Executable validation of every call shape and heap root carried by one
  runtime control instruction. -/
  def checkWellFormed {sigma : LP.LPSignature} (heap : Heap sigma) :
      RuntimeGoal sigma → Bool
    | .call atom => atom.checkWellFormed heap
    | .fail => true
    | .cut => true
    | .disj left right => checkAll heap left && checkAll heap right
    | .ifThenElse condition thenBranch elseBranch =>
        checkAll heap condition && checkAll heap thenBranch &&
          checkAll heap elseBranch
    | .once goals => checkAll heap goals
    | .neg goals => checkAll heap goals
    | .unify left right => left < heap.size && right < heap.size
    | .notUnify left right => left < heap.size && right < heap.size
    | .isVar term => term < heap.size
    | .findall template generator bag =>
        template < heap.size && checkAll heap generator && bag < heap.size
    | .catch guarded catcher recovery =>
        checkAll heap guarded && catcher < heap.size &&
          checkAll heap recovery
    | .throw ball => ball < heap.size

  /-- Validate an ordered runtime goal stack. -/
  def checkAll {sigma : LP.LPSignature} (heap : Heap sigma) :
      List (RuntimeGoal sigma) → Bool
    | [] => true
    | goal :: rest => checkWellFormed heap goal && checkAll heap rest
end

@[simp]
theorem calls_all_checkWellFormed {sigma : LP.LPSignature}
    (heap : Heap sigma) (atoms : List (RuntimeAtom sigma)) :
    checkAll heap (calls atoms) =
      atoms.all (RuntimeAtom.checkWellFormed heap) := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      change (RuntimeAtom.checkWellFormed heap atom &&
        checkAll heap (calls rest)) =
        (RuntimeAtom.checkWellFormed heap atom &&
          rest.all (RuntimeAtom.checkWellFormed heap))
      rw [inductionHypothesis]

end RuntimeGoal

/-- Materialize a goal under the LP builder's one shared variable map.
Successful conjunction contributes no instruction; conjunction is flattened
left-to-right into the surrounding goal stack. -/
def materializeGoalAux {sigma : LP.LPSignature} [DecidableEq sigma.vars] :
    Goal sigma → BuilderM sigma (List (RuntimeGoal sigma))
  | .call atom => do
      let copied ← materializeAtomAux atom
      pure [.call copied]
  | .succeed => pure []
  | .fail => pure [.fail]
  | .cut => pure [.cut]
  | .conj left right => do
      let copiedLeft ← materializeGoalAux left
      let copiedRight ← materializeGoalAux right
      pure (copiedLeft ++ copiedRight)
  | .disj left right => do
      let copiedLeft ← materializeGoalAux left
      let copiedRight ← materializeGoalAux right
      pure [.disj copiedLeft copiedRight]
  | .ifThenElse condition thenBranch elseBranch => do
      let copiedCondition ← materializeGoalAux condition
      let copiedThen ← materializeGoalAux thenBranch
      let copiedElse ← materializeGoalAux elseBranch
      pure [.ifThenElse copiedCondition copiedThen copiedElse]
  | .once goal => do
      let copied ← materializeGoalAux goal
      pure [.once copied]
  | .neg goal => do
      let copied ← materializeGoalAux goal
      pure [.neg copied]
  | .unify left right => do
      let copiedLeft ← materializeTermAux left
      let copiedRight ← materializeTermAux right
      pure [.unify copiedLeft copiedRight]
  | .notUnify left right => do
      let copiedLeft ← materializeTermAux left
      let copiedRight ← materializeTermAux right
      pure [.notUnify copiedLeft copiedRight]
  | .isVar term => do
      let copied ← materializeTermAux term
      pure [.isVar copied]
  | .findall template generator bag => do
      let copiedTemplate ← materializeTermAux template
      let copiedGenerator ← materializeGoalAux generator
      let copiedBag ← materializeTermAux bag
      pure [.findall copiedTemplate copiedGenerator copiedBag]
  | .catch guarded catcher recovery => do
      let copiedGuarded ← materializeGoalAux guarded
      let copiedCatcher ← materializeTermAux catcher
      let copiedRecovery ← materializeGoalAux recovery
      pure [.catch copiedGuarded copiedCatcher copiedRecovery]
  | .throw ball => do
      let copied ← materializeTermAux ball
      pure [.throw copied]
termination_by goal => goal

/-- Pure conjunction materializes through exactly the LP goal materializer;
the only difference is the typed `RuntimeGoal.call` tag. -/
theorem materializeGoalAux_calls {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] (atoms : List (LP.Atom sigma)) :
    materializeGoalAux (Goal.calls atoms) = (do
      let copied ← materializeGoalsAux atoms
      pure (RuntimeGoal.calls copied)) := by
  induction atoms with
  | nil => simp [Goal.calls, materializeGoalAux, materializeGoalsAux,
      RuntimeGoal.calls]
  | cons atom rest inductionHypothesis =>
      cases rest with
      | nil => simp [Goal.calls, materializeGoalAux, materializeGoalsAux,
          RuntimeGoal.calls]
      | cons next tail =>
          simp [Goal.calls, materializeGoalAux, materializeGoalsAux,
            RuntimeGoal.calls, inductionHypothesis]

/-- Runtime form of a canonical Prolog clause.  Head and body share the same
per-activation variable map. -/
structure RuntimeClause (sigma : LP.LPSignature) where
  head : RuntimeAtom sigma
  body : List (RuntimeGoal sigma)

namespace RuntimeClause

/-- Exact runtime embedding of a pure LP runtime clause. -/
def ofLP {sigma : LP.LPSignature}
    (clause : LP.RuntimeMaterialize.RuntimeClause sigma) :
    RuntimeClause sigma where
  head := clause.head
  body := RuntimeGoal.calls clause.body

/-- Validate a runtime clause against the one shared heap. -/
def checkWellFormed {sigma : LP.LPSignature}
    (heap : Heap sigma) (clause : RuntimeClause sigma) : Bool :=
  clause.head.checkWellFormed heap &&
    RuntimeGoal.checkAll heap clause.body

@[simp]
theorem checkWellFormed_ofLP {sigma : LP.LPSignature}
    (heap : Heap sigma) (clause : LP.RuntimeMaterialize.RuntimeClause sigma) :
    checkWellFormed heap (ofLP clause) = clause.checkWellFormed heap := by
  cases clause
  simp [checkWellFormed, ofLP, LP.RuntimeMaterialize.RuntimeClause.checkWellFormed]

end RuntimeClause

/-- Materialize one already-standardized Prolog clause in head-then-body
order, matching the LP clause materializer. -/
def materializeClauseAux {sigma : LP.LPSignature} [DecidableEq sigma.vars]
    (clause : Clause sigma) : BuilderM sigma (RuntimeClause sigma) := do
  let head ← materializeAtomAux clause.head
  let body ← materializeGoalAux clause.body
  pure { head, body }

/-- Pure clauses use the LP clause materializer exactly, with only the typed
control wrapper added to the copied body. -/
theorem materializeClauseAux_ofLP {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] (clause : LP.Clause sigma) :
    materializeClauseAux (Clause.ofLP clause) =
      RuntimeClause.ofLP <$> LP.RuntimeMaterialize.materializeClauseAux clause := by
  cases clause with
  | mk head body =>
      simp only [materializeClauseAux, Clause.ofLP,
        LP.RuntimeMaterialize.materializeClauseAux]
      rw [materializeGoalAux_calls]
      simp [materializeGoalsAux, RuntimeClause.ofLP]

/-- Checked output of source-goal materialization. -/
structure MaterializedGoal (sigma : LP.LPSignature) where
  memory : Memory sigma
  goals : List (RuntimeGoal sigma)
  varMap : List (sigma.vars × Addr)

/-- Checked output of source-clause materialization. -/
structure MaterializedClause (sigma : LP.LPSignature) where
  memory : Memory sigma
  clause : RuntimeClause sigma
  varMap : List (sigma.vars × Addr)

/-- Materialize one canonical Prolog goal into an existing valid LP memory.
The trail is carried through unchanged. -/
def materializeGoal {sigma : LP.LPSignature} [DecidableEq sigma.vars]
    (memory : Memory sigma) (goal : Goal sigma) :
    Except MemoryError (MaterializedGoal sigma) :=
  match runChecked (materializeGoalAux goal) memory.heap with
  | .error error => .error error
  | .ok (goals, state) =>
      if RuntimeGoal.checkAll state.heap goals then
        .ok {
          memory := { heap := state.heap, trail := memory.trail }
          goals
          varMap := state.varMap
        }
      else
        .error .illFormedHeap

/-- The public pure-goal boundary is exactly the existing LP materializer,
including heap/trail state, variable identities, output checks, and failures.
Only the result atoms receive the typed `RuntimeGoal.call` constructor. -/
theorem materializeGoal_calls {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] (memory : Memory sigma)
    (atoms : List (LP.Atom sigma)) :
    materializeGoal memory (Goal.calls atoms) =
      match LP.RuntimeMaterialize.materializeGoals memory atoms with
      | .error error => .error error
      | .ok result => .ok {
          memory := result.memory
          goals := RuntimeGoal.calls result.goals
          varMap := result.varMap
        } := by
  simp only [materializeGoal, LP.RuntimeMaterialize.materializeGoals,
    materializeGoalAux_calls]
  have hMap :
      (do
        let copied ← materializeGoalsAux atoms
        pure (RuntimeGoal.calls copied)) =
        RuntimeGoal.calls <$> materializeGoalsAux atoms := by
    exact bind_pure_comp RuntimeGoal.calls (materializeGoalsAux atoms)
  rw [hMap]
  rw [runChecked_map]
  cases hChecked : runChecked (materializeGoalsAux atoms) memory.heap with
  | error error => rfl
  | ok result =>
      rcases result with ⟨runtimeAtoms, state⟩
      simp only [Functor.map, Except.map]
      rw [RuntimeGoal.calls_all_checkWellFormed]
      by_cases hCalls :
          runtimeAtoms.all (RuntimeAtom.checkWellFormed state.heap) = true
      · simp [hCalls]
      · simp [hCalls]

/-- Goal materialization allocates but never binds, so it cannot modify the
caller's trail. -/
theorem materializeGoal_trail_exact {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] {memory : Memory sigma} {goal : Goal sigma}
    {result : MaterializedGoal sigma}
    (h : materializeGoal memory goal = .ok result) :
    result.memory.trail = memory.trail := by
  simp only [materializeGoal] at h
  split at h
  · contradiction
  · split at h
    · cases h
      rfl
    · contradiction

/-- Materialize one canonical Prolog clause into an existing valid LP memory.
The caller standardizes the clause with `Clause.atScope` before entry. -/
def materializeClause {sigma : LP.LPSignature} [DecidableEq sigma.vars]
    (memory : Memory sigma) (clause : Clause sigma) :
    Except MemoryError (MaterializedClause sigma) :=
  match runChecked (materializeClauseAux clause) memory.heap with
  | .error error => .error error
  | .ok (runtimeClause, state) =>
      if runtimeClause.checkWellFormed state.heap then
        .ok {
          memory := { heap := state.heap, trail := memory.trail }
          clause := runtimeClause
          varMap := state.varMap
        }
      else
        .error .illFormedHeap

/-- The public pure-clause boundary is exactly the existing LP clause
materializer, including validation and failure behavior. -/
theorem materializeClause_ofLP {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] (memory : Memory sigma)
    (clause : LP.Clause sigma) :
    materializeClause memory (Clause.ofLP clause) =
      match LP.RuntimeMaterialize.materializeClause memory clause with
      | .error error => .error error
      | .ok result => .ok {
          memory := result.memory
          clause := RuntimeClause.ofLP result.clause
          varMap := result.varMap
        } := by
  simp only [materializeClause, LP.RuntimeMaterialize.materializeClause,
    materializeClauseAux_ofLP]
  rw [runChecked_map]
  cases hChecked :
      runChecked (LP.RuntimeMaterialize.materializeClauseAux clause) memory.heap with
  | error error => rfl
  | ok result =>
      rcases result with ⟨runtimeClause, state⟩
      simp only [Functor.map, Except.map]
      rw [RuntimeClause.checkWellFormed_ofLP]
      by_cases hClause : runtimeClause.checkWellFormed state.heap = true
      · simp [hClause]
      · simp [hClause]

/-- Clause materialization likewise leaves the caller's trail exact. -/
theorem materializeClause_trail_exact {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] {memory : Memory sigma} {clause : Clause sigma}
    {result : MaterializedClause sigma}
    (h : materializeClause memory clause = .ok result) :
    result.memory.trail = memory.trail := by
  simp only [materializeClause] at h
  split at h
  · contradiction
  · split at h
    · cases h
      rfl
    · contradiction

end Mettapedia.Logic.Prolog.RuntimeControl
