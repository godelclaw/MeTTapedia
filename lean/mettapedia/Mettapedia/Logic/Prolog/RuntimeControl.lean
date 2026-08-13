import Mettapedia.Logic.Prolog.Syntax
import Mettapedia.Logic.LP.RuntimeQuery
import Mettapedia.Logic.LP.RuntimeDatabase

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
  | transaction (goals : List (RuntimeGoal sigma))
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
    | .transaction goals => checkAll heap goals
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
  | .transaction goal => do
      let copied ← materializeGoalAux goal
      pure [.transaction copied]
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
narrow materializer interface.  The adapter supplies copied memory, head,
body, and the source neck's head-match policy; the shared transition alone
captures the caller prefix, runs the unifier, validates its writes, and owns
all search authority. -/
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
        headMatch := match clause.neck with
          | .ordinary => .unify
          | .singleSided => .singleSided
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

/-- Narrow services available to the typed Prolog realization of the one
shared runtime.  `metaCall?` only recognizes a call instruction and exposes
its heap roots; decoding remains a read-only capability invoked by the engine
itself.  Optional exception content carries no heap, trail, or control
authority. -/
structure Services (sigma : LP.LPSignature) where
  metaCall? : RuntimeAtom sigma.scoped → Option (Addr × List Addr)
  decoder : LP.RuntimeQuery.MetaCallDecoder sigma (RuntimeGoal sigma.scoped)
  /-- Recognize `phrase/3` without inspecting the heap.  Dynamic grammar
  interpretation remains a distinct read-only decoder mode so ordinary
  `call/N` can never acquire DCG terminal semantics accidentally. -/
  dcgCall? : RuntimeAtom sigma.scoped → Option (Addr × Addr × Addr) :=
    fun _ => none
  /-- Recognize read-only term tests without inspecting the heap. The shared
  engine owns dereference, graph traversal, corruption checks, success, and
  backtracking; a realization supplies only a test descriptor. -/
  termTest? : RuntimeAtom sigma.scoped →
    Option (Addr × LP.RuntimeQuery.TermTest sigma) := fun _ => none
  /-- Recognize one read-only term relation without inspecting the heap. The
  Bool is the expected result; graph comparison stays engine-owned. -/
  termRelation? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeQuery.TermRelation × Bool) := fun _ => none
  /-- Recognize `Term =.. List` without inspecting the heap.  The realization
  supplies only roots and its signature encoding; traversal, allocation, and
  unification remain owned by the shared engine. -/
  univ? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeQuery.UnivEncoding sigma) := fun _ => none
  /-- Recognize the integer `is/2` fragment without inspecting the heap. -/
  integerIs? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeQuery.IntegerArithmeticEncoding sigma) :=
      fun _ => none
  /-- Recognize integer numeric comparisons without evaluating operands. -/
  integerComparison? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeQuery.IntegerComparison ×
      LP.RuntimeQuery.IntegerArithmeticEncoding sigma) := fun _ => none
  /-- Recognize one `format/2` or `format/3` call without inspecting its
  roots. Read-only payload decoding is a separate capability; allocation,
  unification, and output observation remain in the shared engine. -/
  format? : RuntimeAtom sigma.scoped → Option LP.RuntimeQuery.FormatRequest :=
    fun _ => none
  formatter : LP.RuntimeQuery.FormatDecoder sigma :=
    LP.RuntimeQuery.rejectingFormatDecoder sigma
  /-- Recognize one bidirectional text/code call without inspecting either
  root.  The returned decoder has read-only heap access and no control or
  mutation authority. -/
  textConversion? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeQuery.TextConversionDecoder sigma) :=
      fun _ => none
  /-- Recognize a read-only binary predicate without inspecting either root.
  The returned decoder may inspect the heap but cannot bind, allocate,
  schedule, select a clause, or manufacture an answer. -/
  binaryTest? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeQuery.BinaryTestDecoder sigma) :=
      fun _ => none
  /-- Recognize a sorting predicate without inspecting the heap.  The
  returned decoder may order existing roots read-only; the shared engine owns
  allocation of the result spine and output unification. -/
  sort? : RuntimeAtom sigma.scoped → Option (LP.RuntimeQuery.SortDecoder sigma) :=
    fun _ => none
  /-- Recognize ISO `compare/3` without inspecting its operands.  The decoder
  returns only `Ordering`; result allocation and unification remain shared-
  engine work. -/
  termCompare? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × Addr × LP.RuntimeQuery.TermCompareDecoder sigma ×
      LP.RuntimeQuery.TermCompareEncoding sigma) := fun _ => none
  /-- Recognize finite deterministic `length/2` without inspecting the heap.
  The engine owns list traversal, result allocation, and unification. -/
  listLength? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeQuery.ListLengthEncoding sigma) :=
      fun _ => none
  /-- Recognize a ground `current_predicate/1` query.  The service supplies
  only representation syntax; membership is tested by the engine against
  the exact visible program passed to `dispatchActionWith`. -/
  currentPredicate? : RuntimeAtom sigma.scoped → Option Addr := fun _ => none
  predicateIndicatorEncoding :
    Option (LP.RuntimeQuery.PredicateIndicatorEncoding sigma) := none
  /-- Predicate indicators backed by actual engine transitions rather than
  source clauses.  This list is deliberately explicit: `current_predicate/1`
  may expose a builtin only in the tranche that installs its transition. -/
  runtimePredicates : List sigma.relationSymbols := []
  /-- Recognize finite `copy_term/2` without inspecting either root.  Capture,
  freshening, allocation, and output unification remain shared-engine work. -/
  copyTerm? : RuntimeAtom sigma.scoped → Option (Addr × Addr) := fun _ => none
  /-- Recognize `term_variables/2` without inspecting the term graph. -/
  termVariables? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeQuery.CollectionEncoding sigma) :=
      fun _ => none
  /-- Recognize `numbervars/3,4` without inspecting its heap operands.  The
  decoder is read-only; traversal, allocation, binding, and rollback remain
  shared-engine work. -/
  numberVariables? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × Addr × Option Addr ×
      LP.RuntimeQuery.NumberVariablesDecoder sigma) := fun _ => none
  /-- Recognize `term_hash/2`.  Token encoding is pure; traversal, cycle
  handling, allocation, and output unification remain shared-engine work. -/
  termHash? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × LP.RuntimeTermHash.Encoding sigma) := fun _ => none
  /-- Recognize `functor/3` without inspecting any operand graph. -/
  functor? : RuntimeAtom sigma.scoped →
    Option (Addr × Addr × Addr × LP.RuntimeQuery.FunctorEncoding sigma) :=
      fun _ => none
  /-- Recognize persistent database operations without inspecting the heap.
  The shared engine consumes the instruction and emits the request; only a
  `Session` may apply it. -/
  databaseRequest? : RuntimeAtom sigma.scoped →
    Option LP.RuntimeQuery.DatabaseRequest := fun _ => none
  /-- Resolve an explicitly recognized text-resource request.  This service
  returns only one atomic value; the persistent session invokes it read-only,
  while the shared engine owns allocation and output unification. -/
  textFileDecoder : LP.RuntimeQuery.TextFileDecoder sigma :=
    LP.RuntimeQuery.rejectingTextFileDecoder sigma
  /-- Decode the atom naming a non-backtrackable global.  Recognition remains
  heap-blind; only the persistent session may invoke this read-only decoder
  after the canonical engine has consumed the instruction. -/
  decodeGlobalName : Heap sigma.scoped → Addr →
    Except LP.RuntimeQuery.QueryError sigma.constants :=
      fun _ _ => .error .invalidGlobalVariableName
  /-- Read-only conversion of a heap root into the one canonical source-clause
  representation.  It owns neither mutation nor continuation scheduling. -/
  decodeClause : Heap sigma.scoped → Addr →
    Except LP.RuntimeQuery.QueryError (Clause sigma) :=
      fun _ _ => .error .invalidDynamicClause
  /-- Revalidate and expose the ordinary source term of one stored clause.
  The persistent session uses this only to build a source-ordered snapshot;
  matching and occurrence selection remain shared-engine operations. -/
  reflectClause : Clause sigma → Option (LP.Term sigma) := fun _ => none
  /-- Optional language-level payload for reading an absent non-backtrackable
  global. The persistent session decides that the name is absent; this
  callback supplies only immutable exception content. Raising, catcher
  selection, unwind, and recovery remain canonical engine transitions. -/
  undefinedGlobalError : sigma.constants →
    Option (LP.RuntimeException.Packet sigma) := fun _ => none
  /-- Optional language-level payload for `throw(Variable)`.  The shared
  engine alone decides whether the heap root is unbound and raises it through
  the canonical exception phases. -/
  unboundThrowError : Option (LP.RuntimeException.Packet sigma) := none
  /-- Optional language-level list symbols for answer collection.  The shared
  engine owns generator execution, copying, ordering, and bag unification. -/
  collectionEncoding : Option (LP.RuntimeQuery.CollectionEncoding sigma) := none
  /-- Optional canonical symbols used by the engine to normalize retract
  patterns before matching them against reflected clause data. -/
  clauseEncoding : Option (LP.RuntimeQuery.ClauseEncoding sigma) := none

/-- Base typed control has no implicit meta-call authority. -/
def noServices (sigma : LP.LPSignature) : Services sigma where
  metaCall? _ := none
  decoder := LP.RuntimeQuery.rejectingMetaCallDecoder sigma
    (RuntimeGoal sigma.scoped)
  dcgCall? _ := none
  termTest? _ := none
  termRelation? _ := none
  univ? _ := none
  integerIs? _ := none
  integerComparison? _ := none
  format? _ := none
  formatter := LP.RuntimeQuery.rejectingFormatDecoder sigma
  textConversion? _ := none
  binaryTest? _ := none
  sort? _ := none
  termCompare? _ := none
  listLength? _ := none
  currentPredicate? _ := none
  predicateIndicatorEncoding := none
  runtimePredicates := []
  copyTerm? _ := none
  termVariables? _ := none
  numberVariables? _ := none
  termHash? _ := none
  functor? _ := none
  databaseRequest? _ := none
  textFileDecoder := LP.RuntimeQuery.rejectingTextFileDecoder sigma
  decodeGlobalName _ _ := .error .invalidGlobalVariableName
  decodeClause _ _ := .error .invalidDynamicClause
  reflectClause _ := none
  undefinedGlobalError _ := none
  unboundThrowError := none
  collectionEncoding := none
  clauseEncoding := none

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
the shared phase loop.  Structured controls supply only already-materialized
payloads; checkpointing, DFS scheduling, restoration, cut ownership, and the
invocation of the explicit read-only meta-call service remain in
`RuntimeQuery`. -/
def dispatchActionWith {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma)
    (program : Program sigma)
    (instruction : RuntimeGoal sigma.scoped) :
    LP.RuntimeQuery.DispatchAction sigma (RuntimeGoal sigma.scoped)
      (Clause sigma) :=
  match instruction with
  | .call goal =>
      match services.databaseRequest? goal with
      | some request => .database request
      | none =>
          match services.metaCall? goal with
          | some (callable, extraArgs) => .metaCall callable extraArgs
          | none =>
              match services.termTest? goal with
              | some (address, test) => .termTest address test
              | none =>
                  match services.termRelation? goal with
                  | some (left, right, relation, expected) =>
                      .termRelation left right relation expected
                  | none =>
                      match services.univ? goal with
                      | some (termRoot, listRoot, encoding) =>
                          .univ termRoot listRoot encoding
                      | none =>
                          match services.integerIs? goal with
                          | some (resultRoot, expressionRoot, encoding) =>
                              .integerIs resultRoot expressionRoot encoding
                          | none =>
                              match services.integerComparison? goal with
                              | some (leftRoot, rightRoot, comparison, encoding) =>
                                  .integerCompare leftRoot rightRoot comparison
                                    encoding
                              | none =>
                                  match services.format? goal with
                                  | some request => .format request services.formatter
                                  | none =>
                                      match services.textConversion? goal with
                                      | some (text, codes, decoder) =>
                                          .textConversion text codes decoder
                                      | none =>
                                          match services.binaryTest? goal with
                                          | some (left, right, decoder) =>
                                              .binaryTest left right decoder
                                          | none =>
                                              match services.dcgCall? goal with
                                              | some (body, input, rest) =>
                                                  .dcgCall body input rest
                                              | none =>
                                                  match services.sort? goal with
                                                  | some decoder => .sort decoder
                                                  | none =>
                                                      match services.termCompare? goal with
                                                      | some (result, left, right, decoder,
                                                          encoding) =>
                                                          .termCompare result left right decoder
                                                            encoding
                                                      | none =>
                                                          match services.listLength? goal with
                                                          | some (listRoot, lengthRoot,
                                                              encoding) =>
                                                              .listLength listRoot lengthRoot
                                                                encoding
                                                          | none =>
                                                              match services.currentPredicate? goal,
                                                                  services.predicateIndicatorEncoding with
                                                              | some indicatorRoot, some encoding =>
                                                                  .predicateDefined indicatorRoot
                                                                    ((program.map fun clause =>
                                                                      clause.head.symbol) ++
                                                                      services.runtimePredicates)
                                                                    encoding
                                                              | some _, none =>
                                                                  .error .unsupportedInstruction
                                                              | none, _ =>
                                                                  match services.copyTerm? goal with
                                                                  | some (sourceRoot, targetRoot) =>
                                                                      .copyTerm sourceRoot targetRoot
                                                                  | none =>
                                                                      match services.termVariables? goal with
                                                                      | some (termRoot, variablesRoot,
                                                                          encoding) =>
                                                                          .termVariables termRoot
                                                                            variablesRoot encoding
                                                                      | none =>
                                                                          match services.numberVariables? goal with
                                                                          | some (termRoot, startRoot,
                                                                              endRoot, optionsRoot, decoder) =>
                                                                              .numberVariables termRoot
                                                                                startRoot endRoot optionsRoot
                                                                                decoder
                                                                          | none =>
                                                                              match services.termHash? goal with
                                                                              | some (termRoot, hashRoot,
                                                                                  encoding) =>
                                                                                  .termHash termRoot hashRoot
                                                                                    encoding
                                                                              | none =>
                                                                                  match services.functor? goal with
                                                                                  | some (termRoot, nameRoot,
                                                                                      arityRoot, encoding) =>
                                                                                      .functor termRoot nameRoot
                                                                                        arityRoot encoding
                                                                                  | none =>
                                                                                      .call goal
                                                                                        (Program.clausesFor program
                                                                                          goal.symbol)
  | .fail => .fail
  | .cut => .cut
  | .disj left right => .branch left right
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse condition thenBranch elseBranch
  | .softIfThenElse condition thenBranch elseBranch =>
      .softIfThenElse condition thenBranch elseBranch
  | .once goals => .once goals
  | .transaction goals => .transaction goals
  /- Negation as failure is the established hard-if checkpoint pattern: the
  first protected success commits to failure; exhaustion takes the empty
  success branch. No second search mechanism is introduced. -/
  | .neg goals => .ifThenElse goals [.fail] []
  | .unify left right => .unify left right
  /- Non-unifiability runs one canonical graph-unifier attempt behind the
  same protected hard-if checkpoint, so trial bindings cannot escape. -/
  | .notUnify left right =>
      .ifThenElse [.unify left right] [.fail] []
  | .isVar address => .termTest address .isVariable
  | .findall template generator bag =>
      match services.collectionEncoding with
      | some encoding => .findall template generator bag encoding
      | none => .error .unsupportedInstruction
  | .catch guarded catcher recovery => .catch guarded catcher recovery
  | .throw ball => .throw ball services.unboundThrowError

/-- Once mutation and meta-call recognition decline an ordinary call, a
language-supplied read-only test is handed to the engine unchanged.  The
service neither sees the heap nor performs the success/failure transition. -/
theorem dispatchActionWith_termTest {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (address : Addr)
    (test : LP.RuntimeQuery.TermTest sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = some (address, test)) :
    dispatchActionWith services program (.call goal) =
      .termTest address test := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest]

/-- A read-only graph relation is selected only after the earlier disjoint
services decline the call; the classifier supplies roots, relation, and
polarity, not the comparison result. -/
theorem dispatchActionWith_termRelation {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (left right : Addr)
    (relation : LP.RuntimeQuery.TermRelation) (expected : Bool)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal =
      some (left, right, relation, expected)) :
    dispatchActionWith services program (.call goal) =
      .termRelation left right relation expected := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation]

/-- `=../2` is selected only after the earlier disjoint services decline the
call.  The source realization supplies no heap-dependent result. -/
theorem dispatchActionWith_univ {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (termRoot listRoot : Addr)
    (encoding : LP.RuntimeQuery.UnivEncoding sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = some (termRoot, listRoot, encoding)) :
    dispatchActionWith services program (.call goal) =
      .univ termRoot listRoot encoding := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv]

theorem dispatchActionWith_integerIs {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (resultRoot expressionRoot : Addr)
    (encoding : LP.RuntimeQuery.IntegerArithmeticEncoding sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal =
      some (resultRoot, expressionRoot, encoding)) :
    dispatchActionWith services program (.call goal) =
      .integerIs resultRoot expressionRoot encoding := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs]

theorem dispatchActionWith_integerComparison {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (leftRoot rightRoot : Addr)
    (comparison : LP.RuntimeQuery.IntegerComparison)
    (encoding : LP.RuntimeQuery.IntegerArithmeticEncoding sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal =
      some (leftRoot, rightRoot, comparison, encoding)) :
    dispatchActionWith services program (.call goal) =
      .integerCompare leftRoot rightRoot comparison encoding := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison]

/-- A formatting call exposes only its existing roots and one read-only
decoder. No heap result or output is computed by the classifier. -/
theorem dispatchActionWith_format {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (request : LP.RuntimeQuery.FormatRequest)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal = none)
    (hFormat : services.format? goal = some request) :
    dispatchActionWith services program (.call goal) =
      .format request services.formatter := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison, hFormat]

/-- Text/code classification exposes only two existing roots and a read-only
decoder.  The classifier cannot precompute bindings or allocate output. -/
theorem dispatchActionWith_textConversion {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (text codes : Addr)
    (decoder : LP.RuntimeQuery.TextConversionDecoder sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal = none)
    (hFormat : services.format? goal = none)
    (hText : services.textConversion? goal = some (text, codes, decoder)) :
    dispatchActionWith services program (.call goal) =
      .textConversion text codes decoder := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison, hFormat, hText]

/-- A binary test reaches the engine only after every earlier disjoint
service declines the call.  Its classifier supplies roots and a read-only
decoder, never the result of the test. -/
theorem dispatchActionWith_binaryTest {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (left right : Addr)
    (decoder : LP.RuntimeQuery.BinaryTestDecoder sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal = none)
    (hFormat : services.format? goal = none)
    (hText : services.textConversion? goal = none)
    (hBinary : services.binaryTest? goal = some (left, right, decoder)) :
    dispatchActionWith services program (.call goal) =
      .binaryTest left right decoder := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison, hFormat, hText, hBinary]

/-- `phrase/3` reaches its distinct dynamic-grammar action only after every
earlier disjoint service declines the call.  The classifier supplies three
roots and no decoded instructions or memory. -/
theorem dispatchActionWith_dcgCall {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (body input rest : Addr)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal = none)
    (hFormat : services.format? goal = none)
    (hText : services.textConversion? goal = none)
    (hBinary : services.binaryTest? goal = none)
    (hDcg : services.dcgCall? goal = some (body, input, rest)) :
    dispatchActionWith services program (.call goal) =
      .dcgCall body input rest := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison, hFormat, hText, hBinary, hDcg]

/-- Sorting reaches the shared engine only after every earlier disjoint
service declines the call.  The classifier exports one read-only decoder;
allocation of the result list and output unification remain engine-owned. -/
theorem dispatchActionWith_sort {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped)
    (decoder : LP.RuntimeQuery.SortDecoder sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal = none)
    (hFormat : services.format? goal = none)
    (hText : services.textConversion? goal = none)
    (hBinary : services.binaryTest? goal = none)
    (hDcg : services.dcgCall? goal = none)
    (hSort : services.sort? goal = some decoder) :
    dispatchActionWith services program (.call goal) = .sort decoder := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison, hFormat, hText, hBinary, hDcg, hSort]

/-- Standard-term comparison reaches the shared engine as three existing
roots, one read-only decoder, and one result encoding. -/
theorem dispatchActionWith_termCompare {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (result left right : Addr)
    (decoder : LP.RuntimeQuery.TermCompareDecoder sigma)
    (encoding : LP.RuntimeQuery.TermCompareEncoding sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal = none)
    (hFormat : services.format? goal = none)
    (hText : services.textConversion? goal = none)
    (hBinary : services.binaryTest? goal = none)
    (hDcg : services.dcgCall? goal = none)
    (hSort : services.sort? goal = none)
    (hTermCompare : services.termCompare? goal =
      some (result, left, right, decoder, encoding)) :
    dispatchActionWith services program (.call goal) =
      .termCompare result left right decoder encoding := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison, hFormat, hText, hBinary, hDcg, hSort, hTermCompare]

/-- Finite deterministic `length/2` exposes only its two existing roots and
representation encoding.  Traversal, allocation, and unification are owned by
the shared engine. -/
theorem dispatchActionWith_listLength {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (listRoot lengthRoot : Addr)
    (encoding : LP.RuntimeQuery.ListLengthEncoding sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal = none)
    (hFormat : services.format? goal = none)
    (hText : services.textConversion? goal = none)
    (hBinary : services.binaryTest? goal = none)
    (hDcg : services.dcgCall? goal = none)
    (hSort : services.sort? goal = none)
    (hTermCompare : services.termCompare? goal = none)
    (hLength : services.listLength? goal =
      some (listRoot, lengthRoot, encoding)) :
    dispatchActionWith services program (.call goal) =
      .listLength listRoot lengthRoot encoding := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison, hFormat, hText, hBinary, hDcg, hSort, hTermCompare, hLength]

/-- Ground `current_predicate/1` membership is coupled to the exact program
visible at this dispatch plus the realization's explicit transition-backed
builtin inventory.  Neither source clauses nor runtime capabilities can be
substituted after the instruction is classified. -/
theorem dispatchActionWith_currentPredicate {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goal : RuntimeAtom sigma.scoped) (indicatorRoot : Addr)
    (encoding : LP.RuntimeQuery.PredicateIndicatorEncoding sigma)
    (hDatabase : services.databaseRequest? goal = none)
    (hMeta : services.metaCall? goal = none)
    (hTest : services.termTest? goal = none)
    (hRelation : services.termRelation? goal = none)
    (hUniv : services.univ? goal = none)
    (hIs : services.integerIs? goal = none)
    (hComparison : services.integerComparison? goal = none)
    (hFormat : services.format? goal = none)
    (hText : services.textConversion? goal = none)
    (hBinary : services.binaryTest? goal = none)
    (hDcg : services.dcgCall? goal = none)
    (hSort : services.sort? goal = none)
    (hTermCompare : services.termCompare? goal = none)
    (hLength : services.listLength? goal = none)
    (hCurrent : services.currentPredicate? goal = some indicatorRoot)
    (hEncoding : services.predicateIndicatorEncoding = some encoding) :
    dispatchActionWith services program (.call goal) =
      .predicateDefined indicatorRoot
        ((program.map fun clause => clause.head.symbol) ++
          services.runtimePredicates) encoding := by
  simp [dispatchActionWith, hDatabase, hMeta, hTest, hRelation, hUniv, hIs,
    hComparison, hFormat, hText, hBinary, hDcg, hSort, hTermCompare, hLength, hCurrent,
    hEncoding]

@[simp]
theorem dispatchActionWith_neg {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (goals : List (RuntimeGoal sigma.scoped)) :
    dispatchActionWith services program (.neg goals) =
      .ifThenElse goals [.fail] [] := rfl

@[simp]
theorem dispatchActionWith_notUnify {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (left right : Addr) :
    dispatchActionWith services program (.notUnify left right) =
      .ifThenElse [.unify left right] [.fail] [] := rfl

/-- The established typed classifier has no meta-call service.  Concrete
source execution opts in through `dispatchActionWith`; pure-fragment
conservation therefore keeps its previous boundary exactly. -/
def dispatchAction {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (program : Program sigma)
    (instruction : RuntimeGoal sigma.scoped) :
    LP.RuntimeQuery.DispatchAction sigma (RuntimeGoal sigma.scoped)
      (Clause sigma) :=
  dispatchActionWith (noServices sigma) program instruction

/-- Execute one typed transition with explicit callable services through the
same shared phase loop. -/
def stepWith {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma)
    (state : State sigma) : StepResult sigma :=
  LP.RuntimeQuery.stepCoreWithMeta clauseMaterializer services.decoder
    (dispatchActionWith services program) state

/-- Execute one typed Prolog transition through the same phase loop, clause
entry, graph unifier, restoration, and answer mechanism as `Logic.LP`. -/
def step {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (program : Program sigma) (state : State sigma) : StepResult sigma :=
  stepWith (noServices sigma) program state

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

/-- Pull through the shared phase loop with explicit callable services. -/
def pullWith {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (services : Services sigma) (program : Program sigma) : Nat → State sigma →
      PullResult sigma :=
  LP.RuntimeQuery.pullCoreWithMeta clauseMaterializer services.decoder
    (dispatchActionWith services program)

/-- One persistent non-backtrackable global names an ordinary root in the
canonical heap.  Roots below `StateCore.persistentHeapFloor` survive arena
restoration, while writes to their variables remain on the ordinary trail and
therefore still undo on Prolog backtracking. -/
abbrev GlobalStore (sigma : LP.LPSignature) := List (sigma.constants × Addr)

namespace GlobalStore

def lookup [DecidableEq sigma.constants] (store : GlobalStore sigma)
    (name : sigma.constants) : Option Addr :=
  (store.find? fun entry => entry.1 = name).map Prod.snd

def set [DecidableEq sigma.constants] (store : GlobalStore sigma)
    (name : sigma.constants) (root : Addr) : GlobalStore sigma :=
  (name, root) :: store.filter (fun entry => entry.1 != name)

def erase [DecidableEq sigma.constants] (store : GlobalStore sigma)
    (name : sigma.constants) : GlobalStore sigma :=
  store.filter (fun entry => entry.1 != name)

@[simp]
theorem lookup_set_self [DecidableEq sigma.constants]
    (store : GlobalStore sigma) (name : sigma.constants) (root : Addr) :
    (store.set name root).lookup name = some root := by
  simp [set, lookup]

@[simp]
theorem lookup_erase_self [DecidableEq sigma.constants]
    (store : GlobalStore sigma) (name : sigma.constants) :
    (store.erase name).lookup name = none := by
  simp [erase, lookup, List.find?_eq_none]

end GlobalStore

/-- Persistent state that crosses top-level source goals.  The database and
global-name table are non-backtrackable; `memory` contains their protected
heap graph and `nextScope` dominates every allocated variable identity. -/
structure World (sigma : LP.LPSignature) where
  database : LP.RuntimeDatabase.Database (Clause sigma)
  memory : Memory sigma.scoped
  nextScope : Nat
  globals : GlobalStore sigma := []

/-- A resumable typed session retains the persistent logical-update database
and non-backtrackable globals beside the one canonical query state.  Both are
structurally outside the backtrackable `State`, choice points, and return
frames; restoring those resources cannot restore stale persistent state. -/
structure Session (sigma : LP.LPSignature) where
  database : LP.RuntimeDatabase.Database (Clause sigma)
  globals : GlobalStore sigma := []
  state : State sigma
  services : Services sigma := noServices sigma
  /-- Newest-first entry snapshots of active database transactions.  This
  stack is persistent session state, never a query choice or return frame. -/
  transactionSnapshots :
    List (LP.RuntimeDatabase.Database (Clause sigma)) := []

namespace Session

/-- Source clauses currently visible to a newly opened predicate call. -/
def program (session : Session sigma) : Program sigma :=
  session.database.visibleClauses.map Prod.snd

/-- Database visible after defensively rolling every still-open transaction
back.  Nested snapshots are newest first, so the oldest entry is the outermost
transaction's exact pre-state. -/
def rollbackAllDatabase (session : Session sigma) :
    LP.RuntimeDatabase.Database (Clause sigma) :=
  let rec oldest? :
      List (LP.RuntimeDatabase.Database (Clause sigma)) →
        Option (LP.RuntimeDatabase.Database (Clause sigma))
    | [] => none
    | [snapshot] => some snapshot
    | _ :: rest => oldest? rest
  (oldest? session.transactionSnapshots).getD session.database

/-- Package the session's persistent resources around an explicitly selected
memory.  Database transactions roll back defensively; global updates do not. -/
def worldWithMemory (session : Session sigma)
    (memory : Memory sigma.scoped) : World sigma := {
  database := session.rollbackAllDatabase
  memory
  nextScope := session.state.nextScope
  globals := session.globals
}

/-- Commit the current successful query prefix as the next top-level world.
Clearing the trail commits its live bindings; protecting the complete current
heap makes every stored global root valid when the next query opens.  Hidden
query-local cells are harmless retained garbage and can be compacted later
without changing semantics. -/
def commitWorld (session : Session sigma) : World sigma := {
  database := session.database
  memory := { session.state.memory with trail := #[] }
  nextScope := session.state.nextScope
  globals := session.globals
}

end Session

/-- Open a resumable session with explicit read-only runtime services. -/
def openSessionWith {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars]
    (services : Services sigma)
    (memory : Memory sigma.scoped) (queryScope nextScope : Nat)
    (program : Program sigma) (goal : Goal sigma) :
    Except LP.RuntimeQuery.QueryError (Session sigma) := do
  let state ← openQuery memory queryScope nextScope goal
  pure {
    database := LP.RuntimeDatabase.Database.ofProgram program
    state
    services
  }

/-- Open a query against an already-persistent database.  The query state is
fresh, while clause generations and stable references are carried forward
unchanged from the prior session. -/
def openSessionDatabaseWith {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars]
    (services : Services sigma)
    (memory : Memory sigma.scoped) (queryScope nextScope : Nat)
    (database : LP.RuntimeDatabase.Database (Clause sigma))
    (goal : Goal sigma) :
    Except LP.RuntimeQuery.QueryError (Session sigma) := do
  let state ← openQuery memory queryScope nextScope goal
  pure { database, state, services }

/-- Open a fresh top-level query over the complete persistent world.  The new
query receives a fresh activation scope, and every carried heap cell starts
below the protected floor so no query-local choice can reclaim global roots. -/
def openSessionWorldWith {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars]
    (services : Services sigma) (world : World sigma) (goal : Goal sigma) :
    Except LP.RuntimeQuery.QueryError (Session sigma) := do
  let state ← openQuery world.memory world.nextScope (world.nextScope + 1) goal
  pure {
    database := world.database
    globals := world.globals
    state := { state with persistentHeapFloor := world.memory.heap.size }
    services
  }

/-- Opening a session installs exactly the supplied source program as the
generation-zero visible database.  Adding stable references is representation
preserving and does not reorder or deduplicate clauses. -/
theorem openSessionWith_program {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars]
    (services : Services sigma)
    (memory : Memory sigma.scoped) (queryScope nextScope : Nat)
    (program : Program sigma) (goal : Goal sigma) (session : Session sigma)
    (hOpen : openSessionWith services memory queryScope nextScope program goal =
      .ok session) :
    session.program = program := by
  unfold openSessionWith at hOpen
  cases hQuery : openQuery memory queryScope nextScope goal with
  | error error => simp [hQuery] at hOpen
  | ok state =>
      simp [hQuery] at hOpen
      subst session
      exact LP.RuntimeDatabase.Database.ofProgram_visibleClause_values program

/-- Open one resumable typed session. -/
def openSession {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    (memory : Memory sigma.scoped) (queryScope nextScope : Nat)
    (program : Program sigma) (goal : Goal sigma) :
    Except LP.RuntimeQuery.QueryError (Session sigma) := do
  openSessionWith (noServices sigma) memory queryScope nextScope program goal

/-- Open an isolated typed session at the conventional query/activation
scopes used by the LP grounding theorem. -/
def openEmpty {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    (program : Program sigma) (goal : Goal sigma) :
    Except LP.RuntimeQuery.QueryError (Session sigma) :=
  openSession (Memory.empty sigma.scoped) 0 1 program goal

/-- One session step either retains the complete live session or closes the
query while returning every persistent resource needed by a later query. -/
inductive SessionStepResult (sigma : LP.LPSignature) where
  | next (session : Session sigma)
      (observation : Option (LP.RuntimeQuery.Observation sigma))
  | terminal (result : LP.RuntimeQuery.Terminal sigma)
      (world : World sigma)

/-- Close a session error through the same exact query-checkpoint restoration
as the shared runtime, while preserving the complete persistent world. -/
def failSession (session : Session sigma)
    (state : State sigma) (error : LP.RuntimeQuery.QueryError) :
    SessionStepResult sigma :=
  match state.memory.restorePreserving state.persistentHeapFloor
      state.queryCheckpoint with
  | .ok memory =>
      .terminal (.runtimeError error memory) (session.worldWithMemory memory)
  | .error cleanup =>
      .terminal (.runtimeError (.cleanupFailed error cleanup) state.memory)
        (session.worldWithMemory state.memory)

/-- Call-time visible and successfully revalidated database-clause candidates,
in source order with stable identities. Invalid or absent provenance is
skipped rather than allowed to influence inspection or retraction. -/
def databaseClauseCandidates (session : Session sigma) :
    List (LP.RuntimeQuery.DatabaseClauseCandidate sigma) :=
  session.database.visibleClauses.filterMap fun entry =>
    session.services.reflectClause entry.2 |>.map fun clause => {
      reference := entry.1
      clause
    }

/-- Apply one engine-issued persistent request. Decoding/reflection is
read-only; generation advance and database replacement happen exactly here,
outside all backtrackable query resources. -/
def applyDatabaseRequest [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    (session : Session sigma)
    (state : State sigma) (request : LP.RuntimeQuery.DatabaseRequest) :
    SessionStepResult sigma :=
  match request with
  | .transactionBegin =>
      .next {
        session with
        state
        transactionSnapshots := session.database :: session.transactionSnapshots
      } none
  | .transactionCommit =>
      match session.transactionSnapshots with
      | [] => failSession session state .transactionStackUnderflow
      | _ :: snapshots =>
          .next { session with state, transactionSnapshots := snapshots } none
  | .transactionRollback =>
      match session.transactionSnapshots with
      | [] => failSession session state .transactionStackUnderflow
      | database :: snapshots =>
          .next {
            session with
            database
            state
            transactionSnapshots := snapshots
          } none
  | .asserta root =>
      match session.services.decodeClause state.memory.heap root with
      | .error error => failSession session state error
      | .ok clause =>
          .next {
            session with
            database := (session.database.asserta clause).2
            state
          } none
  | .assertz root =>
      match session.services.decodeClause state.memory.heap root with
      | .error error => failSession session state error
      | .ok clause =>
          .next {
            session with
            database := (session.database.assertz clause).2
            state
          } none
  | .assertaWithReference root referenceRoot =>
      match session.services.clauseEncoding with
      | none => failSession session state .unsupportedInstruction
      | some encoding =>
          match session.services.decodeClause state.memory.heap root with
          | .error error => failSession session state error
          | .ok clause =>
              let inserted := session.database.asserta clause
              match LP.RuntimeQuery.bindDatabaseReferenceStep state
                  referenceRoot (encoding.referenceConstant inserted.1) with
              | .next next observation =>
                  .next {
                    session with
                    database := inserted.2
                    state := next
                  } observation
              | .terminal terminal =>
                  .terminal terminal
                    (session.worldWithMemory terminal.memory)
              | .databaseRequest _ next =>
                  failSession session next .unhandledDatabaseRequest
  | .assertzWithReference root referenceRoot =>
      match session.services.clauseEncoding with
      | none => failSession session state .unsupportedInstruction
      | some encoding =>
          match session.services.decodeClause state.memory.heap root with
          | .error error => failSession session state error
          | .ok clause =>
              let inserted := session.database.assertz clause
              match LP.RuntimeQuery.bindDatabaseReferenceStep state
                  referenceRoot (encoding.referenceConstant inserted.1) with
              | .next next observation =>
                  .next {
                    session with
                    database := inserted.2
                    state := next
                  } observation
              | .terminal terminal =>
                  .terminal terminal
                    (session.worldWithMemory terminal.memory)
              | .databaseRequest _ next =>
                  failSession session next .unhandledDatabaseRequest
  | .retract pattern =>
      match session.services.clauseEncoding with
      | none => failSession session state .unsupportedInstruction
      | some encoding =>
          match LP.RuntimeQuery.openRetractStep encoding state pattern
              (databaseClauseCandidates session) with
          | .next next observation =>
              .next { session with state := next } observation
          | .terminal terminal =>
              .terminal terminal (session.worldWithMemory terminal.memory)
          | .databaseRequest _ next =>
              failSession session next .unhandledDatabaseRequest
  | .clause head body reference =>
      match session.services.clauseEncoding with
      | none => failSession session state .unsupportedInstruction
      | some encoding =>
          match LP.RuntimeQuery.openClauseStep encoding state head body reference
              (databaseClauseCandidates session) with
          | .next next observation =>
              .next { session with state := next } observation
          | .terminal terminal =>
              .terminal terminal (session.worldWithMemory terminal.memory)
          | .databaseRequest _ next =>
              failSession session next .unhandledDatabaseRequest
  | .eraseRef reference =>
      match session.database.eraseRef reference with
      | none => .next { session with state } none
      | some (_, database) => .next { session with database, state } none
  | .globalSet nameRoot valueRoot =>
      match session.services.decodeGlobalName state.memory.heap nameRoot with
      | .error error => failSession session state error
      | .ok name =>
          match LP.RuntimeException.capture state.memory.heap valueRoot with
          | .error error => failSession session state (.globalValueReadback error)
          | .ok packet =>
              match packet.install state.memory state.nextScope with
              | .error error => failSession session state (.memory error)
              | .ok installed =>
                  .next {
                    session with
                    globals := session.globals.set name installed.root
                    state := {
                      state with
                      memory := installed.memory
                      nextScope := installed.nextScope
                      persistentHeapFloor := installed.memory.heap.size
                    }
                  } none
  | .globalGet nameRoot valueRoot =>
      match session.services.decodeGlobalName state.memory.heap nameRoot with
      | .error error => failSession session state error
      | .ok name =>
          match session.globals.lookup name with
          | none =>
              match session.services.undefinedGlobalError name with
              | some packet =>
                  .next {
                    session with
                    state := { state with phase := .raising packet }
                  } none
              | none => failSession session state .undefinedGlobalVariable
          | some storedRoot =>
              match LP.RuntimeQuery.beginUnifyStep state storedRoot valueRoot
                  state.control.current with
              | .next next observation =>
                  .next { session with state := next } observation
              | .terminal terminal =>
                  .terminal terminal (session.worldWithMemory terminal.memory)
              | .databaseRequest _ next =>
                  failSession session next .unhandledDatabaseRequest
  | .globalDelete nameRoot =>
      match session.services.decodeGlobalName state.memory.heap nameRoot with
      | .error error => failSession session state error
      | .ok name =>
          .next { session with globals := session.globals.erase name, state } none
  | .readTextFile pathRoot textRoot optionsRoot =>
      match session.services.textFileDecoder.decode state.memory.heap
          pathRoot optionsRoot with
      | .error error => failSession session state error
      | .ok text =>
          match state.memory.allocate (.const text) with
          | .error error => failSession session state (.memory error)
          | .ok (textValueRoot, memory) =>
              match LP.RuntimeQuery.beginUnifyStep { state with memory }
                  textRoot textValueRoot state.control.current with
              | .next next observation =>
                  .next { session with state := next } observation
              | .terminal terminal =>
                  .terminal terminal (session.worldWithMemory terminal.memory)
              | .databaseRequest _ next =>
                  failSession session next .unhandledDatabaseRequest

/-- Beginning a transaction transfers the current persistent database into the
newest snapshot slot without changing the database or query state. -/
theorem applyDatabaseRequest_transactionBegin
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma) :
    applyDatabaseRequest session state .transactionBegin =
      .next {
        session with
        state
        transactionSnapshots := session.database :: session.transactionSnapshots
      } none := rfl

/-- Commit consumes exactly the newest snapshot and preserves the live database
produced by the protected computation. -/
theorem applyDatabaseRequest_transactionCommit
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma)
    (snapshot : LP.RuntimeDatabase.Database (Clause sigma)) (snapshots) :
    applyDatabaseRequest
        { session with transactionSnapshots := snapshot :: snapshots }
        state .transactionCommit =
      .next { session with state, transactionSnapshots := snapshots } none := rfl

/-- Rollback consumes exactly the newest snapshot and restores it as the live
database, leaving every enclosing transaction snapshot in place. -/
theorem applyDatabaseRequest_transactionRollback
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma)
    (snapshot : LP.RuntimeDatabase.Database (Clause sigma)) (snapshots) :
    applyDatabaseRequest
        { session with transactionSnapshots := snapshot :: snapshots }
        state .transactionRollback =
      .next {
        session with
        database := snapshot
        state
        transactionSnapshots := snapshots
      } none := rfl

/-- Defensive terminal cleanup of two nested transactions selects the outer
entry snapshot, not the inner one or the current partially updated database. -/
theorem Session.rollbackAllDatabase_two
    (session : Session sigma)
    (inner outer : LP.RuntimeDatabase.Database (Clause sigma)) :
    Session.rollbackAllDatabase
        ({ session with transactionSnapshots := [inner, outer] } : Session sigma) =
      outer := rfl

/-- A successfully decoded `asserta/1` request performs exactly one front
insertion and leaves the already-advanced canonical query state untouched. -/
theorem applyDatabaseRequest_asserta_of_decode
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma) (root : Addr)
    (clause : Clause sigma)
    (hDecode : session.services.decodeClause state.memory.heap root =
      .ok clause) :
    applyDatabaseRequest session state (.asserta root) =
      .next {
        session with
        database := (session.database.asserta clause).2
        state := state
      } none := by
  simp [applyDatabaseRequest, hDecode]

/-- A successfully decoded `assertz/1` request performs exactly one back
insertion and leaves the already-advanced canonical query state untouched. -/
theorem applyDatabaseRequest_assertz_of_decode
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma) (root : Addr)
    (clause : Clause sigma)
    (hDecode : session.services.decodeClause state.memory.heap root =
      .ok clause) :
    applyDatabaseRequest session state (.assertz root) =
      .next {
        session with
        database := (session.database.assertz clause).2
        state := state
      } none := by
  simp [applyDatabaseRequest, hDecode]

/-- `asserta/2` inserts exactly once only after the shared engine has begun
canonical binding of the stable reference output. -/
theorem applyDatabaseRequest_assertaWithReference_of_decode_bind
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state next : State sigma)
    (root referenceRoot : Addr) (clause : Clause sigma)
    (encoding : LP.RuntimeQuery.ClauseEncoding sigma)
    (observation : Option (LP.RuntimeQuery.Observation sigma))
    (hEncoding : session.services.clauseEncoding = some encoding)
    (hDecode : session.services.decodeClause state.memory.heap root =
      .ok clause)
    (hBind : LP.RuntimeQuery.bindDatabaseReferenceStep state referenceRoot
      (encoding.referenceConstant (session.database.asserta clause).1) =
        .next next observation) :
    applyDatabaseRequest session state
        (.assertaWithReference root referenceRoot) =
      .next {
        session with
        database := (session.database.asserta clause).2
        state := next
      } observation := by
  have hBind' : LP.RuntimeQuery.bindDatabaseReferenceStep state referenceRoot
      (encoding.referenceConstant session.database.nextRef) =
        .next next observation := by
    simpa using hBind
  simp [applyDatabaseRequest, hEncoding, hDecode, hBind']

/-- `assertz/2` has the analogous single-insertion/reference-binding handoff
for source-order back insertion. -/
theorem applyDatabaseRequest_assertzWithReference_of_decode_bind
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state next : State sigma)
    (root referenceRoot : Addr) (clause : Clause sigma)
    (encoding : LP.RuntimeQuery.ClauseEncoding sigma)
    (observation : Option (LP.RuntimeQuery.Observation sigma))
    (hEncoding : session.services.clauseEncoding = some encoding)
    (hDecode : session.services.decodeClause state.memory.heap root =
      .ok clause)
    (hBind : LP.RuntimeQuery.bindDatabaseReferenceStep state referenceRoot
      (encoding.referenceConstant (session.database.assertz clause).1) =
        .next next observation) :
    applyDatabaseRequest session state
        (.assertzWithReference root referenceRoot) =
      .next {
        session with
        database := (session.database.assertz clause).2
        state := next
      } observation := by
  have hBind' : LP.RuntimeQuery.bindDatabaseReferenceStep state referenceRoot
      (encoding.referenceConstant session.database.nextRef) =
        .next next observation := by
    simpa using hBind
  simp [applyDatabaseRequest, hEncoding, hDecode, hBind']

/-- Successful occurrence erasure advances exactly to the database returned
by the stable-reference operation and preserves the live query state. -/
theorem applyDatabaseRequest_eraseRef_of_some
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma) (reference : Nat)
    (clause : Clause sigma)
    (database : LP.RuntimeDatabase.Database (Clause sigma))
    (hErase : session.database.eraseRef reference = some (clause, database)) :
    applyDatabaseRequest session state (.eraseRef reference) =
      .next { session with database, state } none := by
  simp [applyDatabaseRequest, hErase]

/-- A snapshot occurrence already erased by an intervening persistent action
is a successful no-op on retry, matching SWI's redo discipline; it neither
rewinds nor advances the database. -/
theorem applyDatabaseRequest_eraseRef_of_none
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma) (reference : Nat)
    (hErase : session.database.eraseRef reference = none) :
    applyDatabaseRequest session state (.eraseRef reference) =
      .next { session with state } none := by
  simp [applyDatabaseRequest, hErase]

/-- A successful global set is one finite capture followed by one ordinary
packet installation.  The exact installed root is entered in the persistent
name table, and the protected floor advances to the resulting heap top. -/
theorem applyDatabaseRequest_globalSet_of_decode_capture_install
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma)
    (nameRoot valueRoot : Addr) (name : sigma.constants)
    (packet : LP.RuntimeException.Packet sigma)
    (installed : LP.RuntimeException.Installed sigma)
    (hName : session.services.decodeGlobalName state.memory.heap nameRoot =
      .ok name)
    (hCapture : LP.RuntimeException.capture state.memory.heap valueRoot =
      .ok packet)
    (hInstall : packet.install state.memory state.nextScope = .ok installed) :
    applyDatabaseRequest session state (.globalSet nameRoot valueRoot) =
      .next {
        session with
        globals := session.globals.set name installed.root
        state := {
          state with
          memory := installed.memory
          nextScope := installed.nextScope
          persistentHeapFloor := installed.memory.heap.size
        }
      } none := by
  simp [applyDatabaseRequest, hName, hCapture, hInstall]

/-- A successful global get selects exactly the root stored under the decoded
name and hands that root to the canonical unifier.  The session layer neither
copies nor otherwise interprets the stored graph. -/
theorem applyDatabaseRequest_globalGet_of_decode_lookup_bind
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state next : State sigma)
    (nameRoot valueRoot storedRoot : Addr) (name : sigma.constants)
    (observation : Option (LP.RuntimeQuery.Observation sigma))
    (hName : session.services.decodeGlobalName state.memory.heap nameRoot =
      .ok name)
    (hLookup : session.globals.lookup name = some storedRoot)
    (hBind : LP.RuntimeQuery.beginUnifyStep state storedRoot valueRoot
      state.control.current = .next next observation) :
    applyDatabaseRequest session state (.globalGet nameRoot valueRoot) =
      .next { session with state := next } observation := by
  simp only [applyDatabaseRequest, hName]
  simp only [hLookup]
  rw [hBind]

/-- A realization that supplies an exception packet for an absent global
enters the canonical raising phase. The session layer neither installs a
catcher nor unwinds any control frame itself. -/
theorem applyDatabaseRequest_globalGet_missing_of_error_packet
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma)
    (nameRoot valueRoot : Addr) (name : sigma.constants)
    (packet : LP.RuntimeException.Packet sigma)
    (hName : session.services.decodeGlobalName state.memory.heap nameRoot =
      .ok name)
    (hLookup : session.globals.lookup name = none)
    (hPacket : session.services.undefinedGlobalError name = some packet) :
    applyDatabaseRequest session state (.globalGet nameRoot valueRoot) =
      .next {
        session with
        state := { state with phase := .raising packet }
      } none := by
  simp [applyDatabaseRequest, hName, hLookup, hPacket]

/-- Generic realizations that provide no language packet retain the explicit
runtime error rather than silently turning an absent global into failure. -/
theorem applyDatabaseRequest_globalGet_missing_without_error_packet
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma)
    (nameRoot valueRoot : Addr) (name : sigma.constants)
    (hName : session.services.decodeGlobalName state.memory.heap nameRoot =
      .ok name)
    (hLookup : session.globals.lookup name = none)
    (hPacket : session.services.undefinedGlobalError name = none) :
    applyDatabaseRequest session state (.globalGet nameRoot valueRoot) =
      failSession session state .undefinedGlobalVariable := by
  simp [applyDatabaseRequest, hName, hLookup, hPacket]

/-- Deleting a decoded name is exactly persistent-map erasure and never
depends on whether that name was present. -/
theorem applyDatabaseRequest_globalDelete_of_decode
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma) (nameRoot : Addr)
    (name : sigma.constants)
    (hName : session.services.decodeGlobalName state.memory.heap nameRoot =
      .ok name) :
    applyDatabaseRequest session state (.globalDelete nameRoot) =
      .next { session with globals := session.globals.erase name, state } none := by
  simp [applyDatabaseRequest, hName]

/-- A successful host text lookup contributes only one atomic value.  The
session allocates that value on the canonical heap and delegates binding to
the canonical graph unifier; the decoder cannot manufacture the continuation
or an observation. -/
theorem applyDatabaseRequest_readTextFile_of_decode_allocate_bind
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state next : State sigma)
    (pathRoot textRoot optionsRoot textValueRoot : Addr)
    (text : sigma.constants) (memory : Memory sigma.scoped)
    (observation : Option (LP.RuntimeQuery.Observation sigma))
    (hDecode : session.services.textFileDecoder.decode state.memory.heap
      pathRoot optionsRoot = .ok text)
    (hAllocate : state.memory.allocate (.const text) =
      .ok (textValueRoot, memory))
    (hBind : LP.RuntimeQuery.beginUnifyStep { state with memory }
      textRoot textValueRoot state.control.current = .next next observation) :
    applyDatabaseRequest session state
        (.readTextFile pathRoot textRoot optionsRoot) =
      .next { session with state := next } observation := by
  simp only [applyDatabaseRequest, hDecode, hAllocate]
  rw [hBind]

/-- A rejected or unavailable host text lookup fails through the ordinary
cleanup path before allocation or unification. -/
theorem applyDatabaseRequest_readTextFile_of_error
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (session : Session sigma) (state : State sigma)
    (pathRoot textRoot optionsRoot : Addr)
    (error : LP.RuntimeQuery.QueryError)
    (hDecode : session.services.textFileDecoder.decode state.memory.heap
      pathRoot optionsRoot = .error error) :
    applyDatabaseRequest session state
        (.readTextFile pathRoot textRoot optionsRoot) =
      failSession session state error := by
  simp [applyDatabaseRequest, hDecode]

/-- One session transition delegates search to `stepCoreWithMeta` and handles
only the persistent request that the shared engine may return. -/
def stepSession {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (session : Session sigma) : SessionStepResult sigma :=
  match stepWith session.services session.program session.state with
  | .next state observation => .next { session with state } observation
  | .databaseRequest request state =>
      applyDatabaseRequest session state request
  | .terminal result =>
      .terminal result (session.worldWithMemory result.memory)

/-- An ordinary shared-machine step cannot change the persistent database;
only the explicit database-request arm above has that authority. -/
theorem stepSession_next_of_stepWith
    {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (session : Session sigma) (state : State sigma)
    (observation : Option (LP.RuntimeQuery.Observation sigma))
    (hStep : stepWith session.services session.program session.state =
      .next state observation) :
    stepSession session = .next { session with state } observation := by
  simp [stepSession, hStep]

inductive SessionPullResult (sigma : LP.LPSignature) where
  | open (session : Session sigma)
  | answer (value : LP.RuntimeQuery.Answer sigma) (session : Session sigma)
  | terminal (result : LP.RuntimeQuery.Terminal sigma)
      (world : World sigma)

/-- Pull and repackage only the resumable session; execution remains in
`RuntimeQuery.pullCore`. -/
def pullSession {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (fuel : Nat) (session : Session sigma) : SessionPullResult sigma :=
  match fuel with
  | 0 => .open session
  | fuel + 1 =>
      match stepSession session with
      | .terminal result world => .terminal result world
      | .next next none => pullSession fuel next
      | .next next (some (.answer answer)) => .answer answer next
      | .next next (some (.output _)) => pullSession fuel next

end Mettapedia.Logic.Prolog.RuntimeControl
