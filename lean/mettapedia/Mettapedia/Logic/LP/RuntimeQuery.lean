import Mettapedia.Logic.LP.RuntimeMaterialize
import Mettapedia.Logic.LP.RuntimeClauseEntry

/-!
# Demand-driven execution of typed LP clauses

This is the single executable query layer over the `Logic.LP` term graph.  It
does not compile PeTTa or define a second clause semantics: it selects ordinary
`Program` clauses, standardizes each live activation apart, materializes it in
the shared heap, and delegates head unification to `RuntimeUnification`.

The control layout follows the semantic spine of SWI-Prolog V10.1.9:

* `src/pl-incl.h`: `localFrame`, `choice`, and `CHP_CLAUSE`;
* `src/pl-vmi.c`: `shallow_backtrack`, `deep_backtrack`, and `I_CUT`;
* `src/pl-wam.c`: `discardChoicesAfter`; and
* `src/pl-wam.c`: `PL_next_solution` resumption.

The Lean representation is intentionally smaller than SWI's VM.  A return
frame stores a caller continuation and its cut depth.  A clause choice stores
the call-entry heap/trail checkpoint and the remaining source clauses.  Failure
restores that checkpoint before retrying; cut retains only choices older than
the current predicate frame.  The fresh activation scope is persistent query
state and is therefore never rewound by backtracking.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeQuery

open RuntimeTerm RuntimeMaterialize

/-- Runtime hooks whose control behavior must be handled by the query engine.
Only cut is needed for the pure-clause kernel; further built-ins extend this
record rather than becoming synthetic clauses. -/
structure Builtins (σ : LPSignature) where
  isCut : σ.relationSymbols → Bool
  cut_arity_zero : ∀ symbol, isCut symbol = true → σ.relationArity symbol = 0

/-- Structured query failures.  Unsupported/corrupt states do not become
ordinary Prolog failure. -/
inductive QueryError where
  | memory (error : MemoryError)
  | staleScopeSupply (queryScope nextScope : Nat)
  | malformedCut
  | invalidCutDepth (mark depth : Nat)
  | predicateMismatch
  | stalledUnifier
  | unsupportedInstruction
  | cleanupFailed (primary : QueryError) (cleanup : MemoryError)
deriving Repr

/-- Caller state saved while one predicate body is active.  The instruction
type is abstract so pure LP atoms and typed Prolog control share this exact
frame representation. -/
structure ReturnFrameCore (σ : LPSignature) (Instruction : Type*) where
  continuation : List Instruction
  callerCutDepth : Nat

/-- The established pure-LP return frame. -/
abbrev ReturnFrame (σ : LPSignature) :=
  ReturnFrameCore σ (RuntimeAtom σ.scoped)

/-- Backtrackable execution control, generic only in the instruction payload.
`cutDepth` counts the choice points that predate the current predicate
activation. -/
structure ControlCore (σ : LPSignature) (Instruction : Type*) where
  current : List Instruction
  cutDepth : Nat
  frames : List (ReturnFrameCore σ Instruction)

/-- The established pure-LP control state. -/
abbrev Control (σ : LPSignature) :=
  ControlCore σ (RuntimeAtom σ.scoped)

/-- A frozen, ordered clause cursor.  `checkpoint` is the state immediately
before entering this predicate call.  Retained clauses use the source-clause
type of the one instantiated language. -/
structure ClauseCursorCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  checkpoint : Memory.Checkpoint
  goal : RuntimeAtom σ.scoped
  clauses : List SourceClause
  cutDepth : Nat
  frames : List (ReturnFrameCore σ Instruction)

/-- The established pure-LP clause cursor. -/
abbrev ClauseCursor (σ : LPSignature) :=
  ClauseCursorCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- Information retained while the graph unifier executes one selected head. -/
structure AttemptCore (σ : LPSignature) (Instruction : Type*) where
  body : List Instruction
  cutDepth : Nat
  frames : List (ReturnFrameCore σ Instruction)

/-- The established pure-LP unification attempt. -/
abbrev Attempt (σ : LPSignature) :=
  AttemptCore σ (RuntimeAtom σ.scoped)

/-- Query phases are explicit so retry, restore, and every unification
microstep remain resumable. -/
inductive PhaseCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  | dispatch
  | select (cursor : ClauseCursorCore σ Instruction SourceClause)
  | unifying (attempt : AttemptCore σ Instruction)
      (machine : RuntimeUnification.Machine σ.scoped)
  | backtrack
  | afterAnswer

/-- The established pure-LP query phase. -/
abbrev Phase (σ : LPSignature) :=
  PhaseCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- One live query.  `nextScope` is persistent across choice restoration; the
heap, control, and choice stack are the backtrackable lane. -/
structure StateCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  memory : Memory σ.scoped
  control : ControlCore σ Instruction
  choices : List (ClauseCursorCore σ Instruction SourceClause)
  queryCheckpoint : Memory.Checkpoint
  queryVarMap : List (ScopedVar σ.vars × Addr)
  nextScope : Nat
  phase : PhaseCore σ Instruction SourceClause

/-- The established pure-LP query state.  Existing execution and soundness
theorems continue to use this exact specialization. -/
abbrev State (σ : LPSignature) :=
  StateCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- A yielded answer keeps the live memory and roots of the source query
variables.  The state returned alongside it is resumed for the next answer. -/
structure Answer (σ : LPSignature) where
  memory : Memory σ.scoped
  queryVarMap : List (ScopedVar σ.vars × Addr)

inductive Observation (σ : LPSignature) where
  | answer (value : Answer σ)

inductive Terminal (σ : LPSignature) where
  | completed (memory : Memory σ.scoped)
  | runtimeError (error : QueryError) (memory : Memory σ.scoped)

inductive StepResultCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  | next (state : StateCore σ Instruction SourceClause)
      (observation : Option (Observation σ))
  | terminal (result : Terminal σ)

abbrev StepResult (σ : LPSignature) :=
  StepResultCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- Fuel exhaustion is explicitly open; it never fabricates completion. -/
inductive PullResultCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  | open (state : StateCore σ Instruction SourceClause)
  | answer (value : Answer σ)
      (state : StateCore σ Instruction SourceClause)
  | terminal (result : Terminal σ)

abbrev PullResult (σ : LPSignature) :=
  PullResultCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-! ## Fresh-scope boundary -/

def Cell.scopeBelow {σ : LPSignature}
    (limit : Nat) : Cell σ.scoped → Bool
  | .var identity _ => identity.scope < limit
  | .const _ => true
  | .app _ _ => true

/-- All scoped variable identities already present in a heap are below the
next activation identity supplied by the caller. -/
def heapScopesBelow {σ : LPSignature}
    (heap : Heap σ.scoped) (limit : Nat) : Bool :=
  heap.all (Cell.scopeBelow limit)

/-! ## Ordered clauses and cut pruning -/

/-- Clause selection preserves source order. -/
def clausesFor {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (program : Program σ) (symbol : σ.relationSymbols) : List (Clause σ) :=
  program.filter fun clause => decide (clause.head.symbol = symbol)

@[simp]
theorem clausesFor_append {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (left right : Program σ) (symbol : σ.relationSymbols) :
    clausesFor (left ++ right) symbol =
      clausesFor left symbol ++ clausesFor right symbol := by
  simp [clausesFor]

/-- Keep exactly the oldest `mark` entries of a newest-first choice stack. -/
def retainBottom (mark : Nat) (choices : List α) : List α :=
  choices.drop (choices.length - mark)

theorem retainBottom_length_of_le {mark : Nat} {choices : List α}
    (h : mark ≤ choices.length) :
    (retainBottom mark choices).length = mark := by
  simp [retainBottom, Nat.sub_sub_self h]

@[simp]
theorem retainBottom_all (choices : List α) :
    retainBottom choices.length choices = choices := by
  simp [retainBottom]

/-! ## Opening and closing a query -/

/-- The only data a source-query materializer may supply to the shared query
opener.  It cannot initialize alternatives, frames, phases, or scope state. -/
structure MaterializedQuery (σ : LPSignature) (Instruction : Type*) where
  memory : Memory σ.scoped
  current : List Instruction
  varMap : List (ScopedVar σ.vars × Addr)

/-- Materialize one source query at an explicit scope into the canonical heap. -/
structure QueryMaterializer (σ : LPSignature)
    (Instruction SourceQuery : Type*) where
  materialize : Memory σ.scoped → Nat → SourceQuery →
    Except MemoryError (MaterializedQuery σ Instruction)

/-- The established LP source-query materializer. -/
def lpQueryMaterializer {σ : LPSignature} [DecidableEq σ.vars] :
    QueryMaterializer σ (RuntimeAtom σ.scoped) (List (Atom σ)) where
  materialize memory scope goals :=
    match materializeGoals memory (queryAtScope scope goals) with
    | .error error => .error error
    | .ok result => .ok {
        memory := result.memory
        current := result.goals
        varMap := result.varMap
      }

/-- Shared query opening.  Fresh-scope validation, checkpoint ownership, empty
choice/frame initialization, and the initial dispatch phase are constructed
once here for every instruction language. -/
def openQueryCore {σ : LPSignature}
    (materializer : QueryMaterializer σ Instruction SourceQuery)
    (memory : Memory σ.scoped) (queryScope nextScope : Nat)
    (query : SourceQuery) :
    Except QueryError (StateCore σ Instruction SourceClause) :=
  if queryScope < nextScope then
    if heapScopesBelow memory.heap nextScope then
      match materializer.materialize memory queryScope query with
      | .error error => .error (.memory error)
      | .ok result =>
          .ok {
            memory := result.memory
            control := { current := result.current, cutDepth := 0, frames := [] }
            choices := []
            queryCheckpoint := memory.checkpoint
            queryVarMap := result.varMap
            nextScope
            phase := .dispatch
          }
    else
      .error (.staleScopeSupply queryScope nextScope)
  else
    .error (.staleScopeSupply queryScope nextScope)

/-- Materialize a source query once.  `nextScope` must dominate both the query
scope and every scoped variable already live in the supplied heap. -/
def openQuery {σ : LPSignature} [DecidableEq σ.vars]
    (memory : Memory σ.scoped) (queryScope nextScope : Nat)
    (goals : List (Atom σ)) : Except QueryError (State σ) :=
  openQueryCore (SourceClause := Clause σ) lpQueryMaterializer memory
    queryScope nextScope goals

def closeMemory {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    Except MemoryError (Memory σ.scoped) :=
  state.memory.restore state.queryCheckpoint

def complete {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match closeMemory state with
  | .ok memory => .terminal (.completed memory)
  | .error error => .terminal (.runtimeError (.memory error) state.memory)

def failWith {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) (error : QueryError) :
    StepResultCore σ Instruction SourceClause :=
  match closeMemory state with
  | .ok memory => .terminal (.runtimeError error memory)
  | .error cleanup =>
      .terminal (.runtimeError (.cleanupFailed error cleanup) state.memory)

/-! ## One query transition -/

def replacementChoices {σ : LPSignature}
    (cursor : ClauseCursorCore σ Instruction SourceClause)
    (remaining : List SourceClause)
    (older : List (ClauseCursorCore σ Instruction SourceClause)) :
    List (ClauseCursorCore σ Instruction SourceClause) :=
  match remaining with
  | [] => older
  | _ => { cursor with clauses := remaining } :: older

/-- The only data a language-specific clause materializer may supply to the
shared selected-clause transition.  The type has no constructors for answers,
effects, alternatives, pruning, or scheduling. -/
structure MaterializedBody (σ : LPSignature) (Instruction : Type*) where
  memory : Memory σ.scoped
  head : RuntimeAtom σ.scoped
  body : List Instruction

/-- Materialize one source clause at an explicit activation scope.  Search
order, cursor retention, fresh-scope advancement, and head entry remain owned
by the shared query transition below. -/
structure ClauseMaterializer (σ : LPSignature)
    (Instruction SourceClause : Type*) where
  materialize : Memory σ.scoped → Nat → SourceClause →
    Except MemoryError (MaterializedBody σ Instruction)

/-- The pure LP clause materializer used by the established runtime. -/
def lpClauseMaterializer {σ : LPSignature} [DecidableEq σ.scoped.vars] :
    ClauseMaterializer σ (RuntimeAtom σ.scoped) (Clause σ) where
  materialize memory scope clause :=
    match RuntimeMaterialize.materializeClause memory (clause.atScope scope) with
    | .error error => .error error
    | .ok result => .ok {
        memory := result.memory
        head := result.clause.head
        body := result.clause.body
      }

/-- Shared selected-clause transition.  It owns source-order cursor advance,
choice retention, persistent scope advance, and entry into the canonical graph
unifier. -/
def selectStep {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (state : StateCore σ Instruction SourceClause)
    (cursor : ClauseCursorCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match cursor.clauses with
  | [] => .next { state with phase := .backtrack } none
  | clause :: remaining =>
      match materializer.materialize state.memory state.nextScope clause with
      | .error error => failWith state (.memory error)
      | .ok copied =>
          match RuntimeClauseEntry.enter cursor.goal copied.head
              copied.memory copied.body with
          | .error _ => failWith state .predicateMismatch
          | .ok entered =>
              let attempt : AttemptCore σ Instruction := {
                body := entered.body
                cutDepth := cursor.cutDepth
                frames := cursor.frames
              }
              .next {
                state with
                memory := entered.memory
                choices := replacementChoices cursor remaining state.choices
                nextScope := state.nextScope + 1
                phase := .unifying attempt entered.unifier
              } none

/-- Resume after a yielded answer by entering the shared backtracking phase. -/
@[simp]
def afterAnswerStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  .next { state with phase := .backtrack } none

/-- Restore and re-enter the newest retained cursor, or close the query when
no alternatives remain. -/
@[simp]
def backtrackStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match state.choices with
  | [] => complete state
  | cursor :: older =>
      match state.memory.restore cursor.checkpoint with
      | .error error => failWith state (.memory error)
      | .ok memory =>
          .next {
            state with
            memory
            choices := older
            phase := .select cursor
          } none

/-- An empty current goal stack either returns to its caller frame or yields
one answer at the outermost query. -/
@[simp]
def emptyCurrentStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match state.control.frames with
  | frame :: frames =>
      .next {
        state with
        control := {
          current := frame.continuation
          cutDepth := frame.callerCutDepth
          frames
        }
      } none
  | [] =>
      .next { state with phase := .afterAnswer }
        (some (.answer {
          memory := state.memory
          queryVarMap := state.queryVarMap
        }))

/-- Advance the canonical graph unifier by one microstep or install its
selected body/failure in the shared search state. -/
@[simp]
def unifyingStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (attempt : AttemptCore σ Instruction)
    (machine : RuntimeUnification.Machine σ.scoped) :
    StepResultCore σ Instruction SourceClause :=
  match machine with
  | .running _ =>
      match RuntimeUnification.step machine with
      | some next =>
          .next { state with phase := .unifying attempt next } none
      | none => failWith state .stalledUnifier
  | .terminal (.success memory) =>
      .next {
        state with
        memory
        control := {
          current := attempt.body
          cutDepth := attempt.cutDepth
          frames := attempt.frames
        }
        phase := .dispatch
      } none
  | .terminal (.failure memory) =>
      .next { state with memory, phase := .backtrack } none
  | .terminal (.runtimeError error memory) =>
      failWith { state with memory } (.memory error)

/-- Execute a validated cut against the choice depth captured by the current
predicate activation.  Instruction classification remains language-specific;
choice ownership and pruning are shared here. -/
@[simp]
def cutStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  if _hDepth : state.control.cutDepth ≤ state.choices.length then
    .next {
      state with
      control := { state.control with current := rest }
      choices := retainBottom state.control.cutDepth state.choices
    } none
  else
    failWith state
      (.invalidCutDepth state.control.cutDepth state.choices.length)

/-- Enter an ordinary predicate call by transferring its source-ordered
clause alternatives into the shared cursor representation.  This transition
does not select or execute a clause. -/
@[simp]
def callStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (goal : RuntimeAtom σ.scoped) (clauses : List SourceClause)
    (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let frame : ReturnFrameCore σ Instruction := {
    continuation := rest
    callerCutDepth := state.control.cutDepth
  }
  let cursor : ClauseCursorCore σ Instruction SourceClause := {
    checkpoint := state.memory.checkpoint
    goal
    clauses
    cutDepth := state.choices.length
    frames := frame :: state.control.frames
  }
  .next { state with phase := .select cursor } none

/-- Enter body unification through the same canonical graph unifier used for
clause heads.  SWI-Prolog V10.1.9 likewise routes `=/2` through `PL_unify`
(`src/pl-prims.c`) and body unification instructions (`src/pl-vmi.c`). -/
@[simp]
def beginUnifyStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let attempt : AttemptCore σ Instruction := {
    body := rest
    cutDepth := state.control.cutDepth
    frames := state.control.frames
  }
  .next {
    state with
    phase := .unifying attempt
      (RuntimeUnification.startMany state.memory [(left, right)])
  } none

/-- Test whether one dereferenced heap root is an unbound variable.  This is
the canonical finite-graph counterpart of SWI-Prolog V10.1.9 `var/1`, whose
implementation delegates to `PL_is_variable` (`src/pl-prims.c`).  A false
test enters ordinary backtracking; corrupt addresses and variable-only cycles
remain typed runtime errors. -/
@[simp]
def isVarStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (address : Addr) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match state.memory.heap.deref address with
  | .error error => failWith state (.memory error)
  | .ok (.variableCycle cycle) =>
      failWith state (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match state.memory.heap[root]? with
      | none => failWith state (.memory (.invalidAddress root))
      | some (.var _ none) =>
          .next {
            state with
            control := { state.control with current := rest }
          } none
      | some _ => .next { state with phase := .backtrack } none

/-- The complete authority granted to an instruction classifier.  It may name
an ordinary call's source clauses or identify base control, but it cannot emit
answers/effects, mutate memory, select a clause, or schedule a body. -/
inductive DispatchAction (σ : LPSignature) (SourceClause : Type*) where
  | call (goal : RuntimeAtom σ.scoped) (clauses : List SourceClause)
  | fail
  | cut
  | unify (left right : Addr)
  | isVar (address : Addr)
  | error (reason : QueryError)

/-- Apply one narrow classification to the canonical state.  The current
instruction has already been removed; `rest` always comes from the live goal
stack rather than from the classifier. -/
@[simp]
def dispatchActionStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (rest : List Instruction) :
    DispatchAction σ SourceClause →
      StepResultCore σ Instruction SourceClause
  | .call goal clauses => callStep state goal clauses rest
  | .fail => .next { state with phase := .backtrack } none
  | .cut => cutStep state rest
  | .unify left right => beginUnifyStep state left right rest
  | .isVar address => isVarStep state address rest
  | .error reason => failWith state reason

/-- The one phase loop shared by LP atoms and typed Prolog control.  Language
code supplies only clause materialization and the narrow instruction
classification above; all search transitions remain in this definition. -/
def stepCore {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (classify : Instruction → DispatchAction σ SourceClause)
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match state.phase with
  | .afterAnswer => afterAnswerStep state
  | .backtrack => backtrackStep state
  | .dispatch =>
      match state.control.current with
      | [] => emptyCurrentStep state
      | instruction :: rest =>
          dispatchActionStep state rest (classify instruction)
  | .select cursor => selectStep materializer state cursor
  | .unifying attempt machine => unifyingStep state attempt machine

/-- Classify an established LP runtime atom for the shared phase loop. -/
def lpDispatchAction {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ)
    (goal : RuntimeAtom σ.scoped) : DispatchAction σ (Clause σ) :=
  if builtins.isCut goal.symbol = true then
    if goal.args.isEmpty then .cut else .error .malformedCut
  else
    .call goal (clausesFor program goal.symbol)

/-- Execute one query transition.  A running graph unifier contributes exactly
one of its own microsteps. -/
def step {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ) :
    StepResult σ :=
  stepCore lpClauseMaterializer (lpDispatchAction builtins program) state

/-- The public LP step is exactly the canonical phase loop specialization.
This rewrite keeps downstream proofs phrased against the stable public name. -/
@[simp]
theorem lp_stepCore_eq_step {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ) :
    stepCore lpClauseMaterializer (lpDispatchAction builtins program) state =
      step builtins program state := rfl

/-! ## Local control laws -/

/-- A well-formed cut transition retains exactly the choices older than the
current predicate activation.  The theorem is stated directly about the one
executable transition; there is no mirror control machine. -/
theorem step_cut_of_dispatch {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ)
    (goal : RuntimeAtom σ.scoped) (rest : List (RuntimeAtom σ.scoped))
    (hPhase : state.phase = .dispatch)
    (hCurrent : state.control.current = goal :: rest)
    (hCut : builtins.isCut goal.symbol = true)
    (hEmpty : goal.args.isEmpty = true)
    (hDepth : state.control.cutDepth ≤ state.choices.length) :
    step builtins program state =
      .next {
        state with
        control := { state.control with current := rest }
        choices := retainBottom state.control.cutDepth state.choices
      } none := by
  simp [step, stepCore, lpDispatchAction, hPhase, hCurrent, hCut,
    hEmpty, hDepth]

/-- Consequently, cut leaves exactly the choice depth captured on predicate
entry; neither a nested call's alternatives nor later clauses survive. -/
theorem step_cut_choice_count {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ)
    (goal : RuntimeAtom σ.scoped) (rest : List (RuntimeAtom σ.scoped))
    (hPhase : state.phase = .dispatch)
    (hCurrent : state.control.current = goal :: rest)
    (hCut : builtins.isCut goal.symbol = true)
    (hEmpty : goal.args.isEmpty = true)
    (hDepth : state.control.cutDepth ≤ state.choices.length) :
    ∃ next,
      step builtins program state = .next next none ∧
      next.choices.length = state.control.cutDepth := by
  let next : State σ := {
    state with
    control := { state.control with current := rest }
    choices := retainBottom state.control.cutDepth state.choices
  }
  refine ⟨next, step_cut_of_dispatch builtins program state goal rest
    hPhase hCurrent hCut hEmpty hDepth, ?_⟩
  simp [next, retainBottom_length_of_le hDepth]

/-- Exhausting the outermost choice stack closes the query by restoring the
entry checkpoint.  Cleanup is part of the executable transition, not a test
fixture postcondition. -/
theorem step_empty_backtrack_completes {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ)
    (memory : Memory σ.scoped)
    (hPhase : state.phase = .backtrack)
    (hChoices : state.choices = [])
    (hRestore : state.memory.restore state.queryCheckpoint = .ok memory) :
    step builtins program state = .terminal (.completed memory) := by
  simp [step, stepCore, hPhase, hChoices, complete, closeMemory, hRestore]

/-- Demand-driven iteration of the shared phase loop.  The materializer and
classifier have the same narrow authority as `stepCore`; observations are
created only by the shared empty-stack transition.  Fuel exhaustion is open,
and the returned state resumes the same DFS search. -/
def pullCore {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (classify : Instruction → DispatchAction σ SourceClause) :
    Nat → StateCore σ Instruction SourceClause →
      PullResultCore σ Instruction SourceClause
  | 0, state => .open state
  | fuel + 1, state =>
      match stepCore materializer classify state with
      | .terminal result => .terminal result
      | .next next none => pullCore materializer classify fuel next
      | .next next (some (.answer answer)) => .answer answer next

/-- The established LP demand-driven specialization. -/
def pull {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) :
    Nat → State σ → PullResult σ :=
  pullCore lpClauseMaterializer (lpDispatchAction builtins program)

end RuntimeQuery
end Mettapedia.Logic.LP
