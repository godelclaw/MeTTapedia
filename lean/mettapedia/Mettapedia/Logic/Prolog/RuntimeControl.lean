import Mettapedia.Logic.Prolog.Syntax
import Mettapedia.Logic.LP.RuntimeQuery

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
  | softIfThenElse (condition thenBranch elseBranch : List (RuntimeGoal sigma))
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
    | .softIfThenElse condition thenBranch elseBranch =>
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
  | .softIfThenElse condition thenBranch elseBranch => do
      let copiedCondition ← materializeGoalAux condition
      let copiedThen ← materializeGoalAux thenBranch
      let copiedElse ← materializeGoalAux elseBranch
      pure [.softIfThenElse copiedCondition copiedThen copiedElse]
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

/-- Typed Prolog clauses instantiate the shared query machine's deliberately
narrow materializer interface.  The adapter can supply only the copied memory,
head, and body; the shared transition retains all search authority. -/
def clauseMaterializer {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars] :
    LP.RuntimeQuery.ClauseMaterializer sigma (RuntimeGoal sigma.scoped)
      (Clause sigma) where
  materialize memory scope clause :=
    match materializeClause memory (clause.atScope scope) with
    | .error error => .error error
    | .ok result => .ok {
        memory := result.memory
        head := result.clause.head
        body := result.clause.body
      }

/-! ## Shared base-control dispatch -/

/-- The typed program index agrees exactly with the established LP index on
embedded pure programs, including source order and duplicate clauses. -/
@[simp]
theorem clausesFor_ofLP {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (program : LP.Program sigma) (symbol : sigma.relationSymbols) :
    Program.clausesFor (Program.ofLP program) symbol =
      (LP.RuntimeQuery.clausesFor program symbol).map Clause.ofLP := by
  induction program with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      have hRest :
          List.filter (fun next : Clause sigma =>
              decide (next.head.symbol = symbol))
              (rest.map Clause.ofLP) =
            (List.filter (fun next : LP.Clause sigma =>
              decide (next.head.symbol = symbol)) rest).map Clause.ofLP := by
        simpa [Program.clausesFor, Program.ofLP,
          LP.RuntimeQuery.clausesFor] using inductionHypothesis
      by_cases hMatches : clause.head.symbol = symbol
      · simp [Program.clausesFor, Program.ofLP,
          LP.RuntimeQuery.clausesFor, Clause.ofLP, hMatches, hRest]
      · simp [Program.clausesFor, Program.ofLP,
          LP.RuntimeQuery.clausesFor, Clause.ofLP, hMatches, hRest]

/-- The canonical query state specialized only by typed Prolog instructions
and source clauses. -/
abbrev State (sigma : LP.LPSignature) :=
  LP.RuntimeQuery.StateCore sigma (RuntimeGoal sigma.scoped) (Clause sigma)

/-- One canonical typed-query transition result. -/
abbrev StepResult (sigma : LP.LPSignature) :=
  LP.RuntimeQuery.StepResultCore sigma (RuntimeGoal sigma.scoped) (Clause sigma)

/-- Typed source goals instantiate the shared query opener's narrow
materializer interface.  The adapter supplies only heap materialization,
ordered instructions, and query-variable roots. -/
def queryMaterializer {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars] :
    LP.RuntimeQuery.QueryMaterializer sigma (RuntimeGoal sigma.scoped)
      (Goal sigma) where
  materialize memory scope goal :=
    match materializeGoal memory (goal.atScope scope) with
    | .error error => .error error
    | .ok result => .ok {
        memory := result.memory
        current := result.goals
        varMap := result.varMap
      }

/-- On pure ordered calls, the typed query materializer is exactly the LP
materializer with `RuntimeGoal.call` tags added to its instruction list. -/
theorem queryMaterializer_calls {sigma : LP.LPSignature}
    [DecidableEq sigma.vars]
    (memory : Memory sigma.scoped) (scope : Nat)
    (atoms : List (LP.Atom sigma)) :
    (queryMaterializer (sigma := sigma)).materialize memory scope
        (Goal.calls atoms) =
      match (LP.RuntimeQuery.lpQueryMaterializer (σ := sigma)).materialize
          memory scope atoms with
      | .error error => .error error
      | .ok result => .ok {
          memory := result.memory
          current := RuntimeGoal.calls result.current
          varMap := result.varMap
        } := by
  simp only [queryMaterializer, Goal.atScope_calls, materializeGoal_calls,
    LP.RuntimeQuery.lpQueryMaterializer, LP.queryAtScope]
  have hMap :
      atoms.map (LP.Atom.atScope scope) =
        atoms.map (fun atom => LP.Atom.atScope scope atom) := rfl
  rw [← hMap]
  cases materializeGoals memory (atoms.map (LP.Atom.atScope scope)) <;> rfl

/-- Open a typed source goal through the canonical LP scope checks,
checkpoint owner, empty choice/frame state, and initial dispatch phase. -/
def openQuery {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    (memory : Memory sigma.scoped) (queryScope nextScope : Nat)
    (goal : Goal sigma) : Except LP.RuntimeQuery.QueryError (State sigma) :=
  LP.RuntimeQuery.openQueryCore (SourceClause := Clause sigma)
    queryMaterializer memory queryScope nextScope goal

/-- Classify a typed runtime instruction into the narrow authority accepted by
the shared phase loop.  Disjunction supplies only its already-materialized
branch payloads; checkpointing, DFS scheduling, restoration, and cut ownership
remain in `RuntimeQuery.branchStep`.  Other structured controls remain explicit
errors until their dedicated transitions are certified. -/
def dispatchAction {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (program : Program sigma)
    (instruction : RuntimeGoal sigma.scoped) :
    LP.RuntimeQuery.DispatchAction sigma (RuntimeGoal sigma.scoped)
      (Clause sigma) :=
  match instruction with
  | .call goal =>
      .call goal (Program.clausesFor program goal.symbol)
  | .fail => .fail
  | .cut => .cut
  | .disj left right => .branch left right
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse condition thenBranch elseBranch
  | .unify left right => .unify left right
  | .isVar address => .isVar address
  | _ => .error .unsupportedInstruction

/-- Execute one typed Prolog transition through the same phase loop, clause
entry, graph unifier, restoration, and answer mechanism as `Logic.LP`. -/
def step {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (program : Program sigma) (state : State sigma) : StepResult sigma :=
  LP.RuntimeQuery.stepCore clauseMaterializer (dispatchAction program) state

/-- One raw demand-driven result over the typed specialization. -/
abbrev PullResult (sigma : LP.LPSignature) :=
  LP.RuntimeQuery.PullResultCore sigma (RuntimeGoal sigma.scoped) (Clause sigma)

/-- Pull through the one canonical phase loop until one answer, terminal, or
open fuel boundary. -/
def pull {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (program : Program sigma) : Nat → State sigma → PullResult sigma :=
  LP.RuntimeQuery.pullCore clauseMaterializer (dispatchAction program)

/-- A resumable typed session retains source clauses beside the one canonical
query state; it owns no additional execution or substitution state. -/
structure Session (sigma : LP.LPSignature) where
  program : Program sigma
  state : State sigma

/-- Open one resumable typed session. -/
def openSession {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    (memory : Memory sigma.scoped) (queryScope nextScope : Nat)
    (program : Program sigma) (goal : Goal sigma) :
    Except LP.RuntimeQuery.QueryError (Session sigma) := do
  let state ← openQuery memory queryScope nextScope goal
  pure { program, state }

/-- Open an isolated typed session at the conventional query/activation
scopes used by the LP grounding theorem. -/
def openEmpty {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    (program : Program sigma) (goal : Goal sigma) :
    Except LP.RuntimeQuery.QueryError (Session sigma) :=
  openSession (Memory.empty sigma.scoped) 0 1 program goal

/-- Demand-driven session results retain the source program only when a live
state remains. -/
inductive SessionPullResult (sigma : LP.LPSignature) where
  | open (session : Session sigma)
  | answer (value : LP.RuntimeQuery.Answer sigma) (session : Session sigma)
  | terminal (result : LP.RuntimeQuery.Terminal sigma)

/-- Pull and repackage only the resumable session; execution remains in
`RuntimeQuery.pullCore`. -/
def pullSession {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (fuel : Nat) (session : Session sigma) : SessionPullResult sigma :=
  match pull session.program fuel session.state with
  | .open state => .open { session with state }
  | .answer answer state => .answer answer { session with state }
  | .terminal result => .terminal result

end Mettapedia.Logic.Prolog.RuntimeControl
