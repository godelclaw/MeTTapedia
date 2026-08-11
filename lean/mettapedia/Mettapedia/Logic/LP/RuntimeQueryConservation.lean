import Mettapedia.Logic.LP.RuntimeQuery

/-!
# Conservation across `RuntimeQuery.stepCore` realizations

`RuntimeQuery.stepCore` is the one search engine shared by the LP and typed
Prolog frontiers.  This file proves that changing only the instruction and
source-clause representations cannot change execution when classification and
materialization commute with those representation maps.

The theorem is deliberately about the executable `stepCore` itself.  It does
not introduce a second transition relation or restate resolution semantics.
-/

namespace Mettapedia.Logic.LP.RuntimeQuery

open RuntimeTerm RuntimeMaterialize

namespace Conservation

variable {sigma : LPSignature}
variable {Instruction₁ Instruction₂ SourceClause₁ SourceClause₂ : Type*}

/-- Map a saved continuation without changing its cut depth. -/
def mapReturnFrame (instruction : Instruction₁ → Instruction₂)
    (frame : ReturnFrameCore sigma Instruction₁) :
    ReturnFrameCore sigma Instruction₂ where
  continuation := frame.continuation.map instruction
  callerCutDepth := frame.callerCutDepth

/-- Map only the instruction payload of backtrackable control. -/
def mapControl (instruction : Instruction₁ → Instruction₂)
    (control : ControlCore sigma Instruction₁) :
    ControlCore sigma Instruction₂ where
  current := control.current.map instruction
  cutDepth := control.cutDepth
  frames := control.frames.map (mapReturnFrame instruction)

/-- Map the two language-owned payloads of a frozen clause cursor. -/
def mapCursor (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (cursor : ClauseCursorCore sigma Instruction₁ SourceClause₁) :
    ClauseCursorCore sigma Instruction₂ SourceClause₂ where
  checkpoint := cursor.checkpoint
  goal := cursor.goal
  clauses := cursor.clauses.map sourceClause
  cutDepth := cursor.cutDepth
  frames := cursor.frames.map (mapReturnFrame instruction)

/-- Map a selected clause body while retaining the canonical unifier state. -/
def mapAttempt (instruction : Instruction₁ → Instruction₂)
    (attempt : AttemptCore sigma Instruction₁) :
    AttemptCore sigma Instruction₂ where
  body := attempt.body.map instruction
  cutDepth := attempt.cutDepth
  frames := attempt.frames.map (mapReturnFrame instruction)

/-- Map one phase of the shared machine. -/
def mapPhase (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) :
    PhaseCore sigma Instruction₁ SourceClause₁ →
      PhaseCore sigma Instruction₂ SourceClause₂
  | .dispatch => .dispatch
  | .select cursor => .select (mapCursor instruction sourceClause cursor)
  | .unifying attempt machine => .unifying (mapAttempt instruction attempt) machine
  | .backtrack => .backtrack
  | .afterAnswer => .afterAnswer

/-- Representation change on a live state.  Memory, observations, checkpoints,
query roots, and the persistent scope supply are definitionally unchanged. -/
def mapState (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁) :
    StateCore sigma Instruction₂ SourceClause₂ where
  memory := state.memory
  control := mapControl instruction state.control
  choices := state.choices.map (mapCursor instruction sourceClause)
  queryCheckpoint := state.queryCheckpoint
  queryVarMap := state.queryVarMap
  nextScope := state.nextScope
  phase := mapPhase instruction sourceClause state.phase

/-- Representation change on the narrow output of clause materialization. -/
def mapMaterializedBody (instruction : Instruction₁ → Instruction₂)
    (body : MaterializedBody sigma Instruction₁) :
    MaterializedBody sigma Instruction₂ where
  memory := body.memory
  head := body.head
  body := body.body.map instruction

/-- Representation change on the narrow output of query materialization. -/
def mapMaterializedQuery (instruction : Instruction₁ → Instruction₂)
    (query : MaterializedQuery sigma Instruction₁) :
    MaterializedQuery sigma Instruction₂ where
  memory := query.memory
  current := query.current.map instruction
  varMap := query.varMap

/-- Representation change on a classifier result.  The classifier still has
no authority to create answers, effects, choices, or schedules. -/
def mapDispatchAction (sourceClause : SourceClause₁ → SourceClause₂) :
    DispatchAction sigma SourceClause₁ → DispatchAction sigma SourceClause₂
  | .call goal clauses => .call goal (clauses.map sourceClause)
  | .fail => .fail
  | .cut => .cut
  | .unify left right => .unify left right
  | .isVar address => .isVar address
  | .error reason => .error reason

/-- Representation change on one shared-machine result. -/
def mapStepResult (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) :
    StepResultCore sigma Instruction₁ SourceClause₁ →
      StepResultCore sigma Instruction₂ SourceClause₂
  | .next state observation =>
      .next (mapState instruction sourceClause state) observation
  | .terminal result => .terminal result

/-- Representation change on a demand-driven pull result. -/
def mapPullResult (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) :
    PullResultCore sigma Instruction₁ SourceClause₁ →
      PullResultCore sigma Instruction₂ SourceClause₂
  | .open state => .open (mapState instruction sourceClause state)
  | .answer answer state =>
      .answer answer (mapState instruction sourceClause state)
  | .terminal result => .terminal result

/-- The exact obligations for one representation to realize another through
the unchanged shared machine.  Both equations concern the only two pieces of
authority supplied to `stepCore`. -/
structure Realization
    (sourceMaterializer : ClauseMaterializer sigma Instruction₁ SourceClause₁)
    (targetMaterializer : ClauseMaterializer sigma Instruction₂ SourceClause₂)
    (sourceClassify : Instruction₁ → DispatchAction sigma SourceClause₁)
    (targetClassify : Instruction₂ → DispatchAction sigma SourceClause₂)
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) : Prop where
  materialize : ∀ memory scope clause,
    targetMaterializer.materialize memory scope (sourceClause clause) =
      (sourceMaterializer.materialize memory scope clause).map
        (mapMaterializedBody instruction)
  classify : ∀ next,
    targetClassify (instruction next) =
      mapDispatchAction sourceClause (sourceClassify next)

/-- The corresponding boundary equation for query opening. -/
structure QueryRealization {SourceQuery₁ SourceQuery₂ : Type*}
    (sourceMaterializer : QueryMaterializer sigma Instruction₁ SourceQuery₁)
    (targetMaterializer : QueryMaterializer sigma Instruction₂ SourceQuery₂)
    (instruction : Instruction₁ → Instruction₂)
    (sourceQuery : SourceQuery₁ → SourceQuery₂) : Prop where
  materialize : ∀ memory scope query,
    targetMaterializer.materialize memory scope (sourceQuery query) =
      (sourceMaterializer.materialize memory scope query).map
        (mapMaterializedQuery instruction)

/-- Shared query opening conserves any query representation satisfying its
single materialization equation. -/
theorem openQueryCore_conserves {SourceQuery₁ SourceQuery₂ : Type*}
    {sourceMaterializer : QueryMaterializer sigma Instruction₁ SourceQuery₁}
    {targetMaterializer : QueryMaterializer sigma Instruction₂ SourceQuery₂}
    {instruction : Instruction₁ → Instruction₂}
    {sourceClause : SourceClause₁ → SourceClause₂}
    {sourceQuery : SourceQuery₁ → SourceQuery₂}
    (realizes : QueryRealization sourceMaterializer targetMaterializer
      instruction sourceQuery)
    (memory : Memory sigma.scoped) (queryScope nextScope : Nat)
    (query : SourceQuery₁) :
    openQueryCore (SourceClause := SourceClause₂) targetMaterializer memory
        queryScope nextScope (sourceQuery query) =
      (openQueryCore (SourceClause := SourceClause₁) sourceMaterializer memory
        queryScope nextScope query).map (mapState instruction sourceClause) := by
  unfold openQueryCore
  rw [realizes.materialize memory queryScope query]
  by_cases hScope : queryScope < nextScope
  · simp only [hScope, if_true]
    by_cases hFresh : heapScopesBelow memory.heap nextScope
    · simp only [hFresh, if_true]
      cases sourceMaterializer.materialize memory queryScope query <;> rfl
    · simp [Except.map, hFresh]
  · simp [Except.map, hScope]

set_option linter.unusedSimpArgs false in
/-- The shared executable step conserves every realization satisfying the two
boundary equations.  This is the central anti-duplication theorem: languages
do not receive a separate transition system whose agreement must be trusted. -/
theorem stepCore_conserves [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols] [DecidableEq sigma.relationSymbols]
    {sourceMaterializer : ClauseMaterializer sigma Instruction₁ SourceClause₁}
    {targetMaterializer : ClauseMaterializer sigma Instruction₂ SourceClause₂}
    {sourceClassify : Instruction₁ → DispatchAction sigma SourceClause₁}
    {targetClassify : Instruction₂ → DispatchAction sigma SourceClause₂}
    {instruction : Instruction₁ → Instruction₂}
    {sourceClause : SourceClause₁ → SourceClause₂}
    (realizes : Realization sourceMaterializer targetMaterializer
      sourceClassify targetClassify instruction sourceClause)
    (state : StateCore sigma Instruction₁ SourceClause₁) :
    stepCore targetMaterializer targetClassify
        (mapState instruction sourceClause state) =
      mapStepResult instruction sourceClause
        (stepCore sourceMaterializer sourceClassify state) := by
  rcases state with ⟨memory, control, choices, checkpoint, queryVarMap,
    nextScope, phase⟩
  cases phase with
  | afterAnswer =>
      simp [stepCore, mapState, mapPhase, mapControl, mapStepResult,
        afterAnswerStep]
  | backtrack =>
      cases choices with
      | nil =>
          cases hRestore : memory.restore checkpoint <;>
            simp [stepCore, mapState, mapPhase, mapControl, mapStepResult,
              backtrackStep, complete, closeMemory, hRestore]
      | cons cursor older =>
          cases hRestore : memory.restore cursor.checkpoint <;>
            cases hCleanup : memory.restore checkpoint <;>
            simp [stepCore, mapState, mapPhase, mapControl, mapCursor,
              mapStepResult, backtrackStep, failWith, closeMemory, hRestore,
              hCleanup]
  | dispatch =>
      rcases control with ⟨current, cutDepth, frames⟩
      cases current with
      | nil =>
          cases frames <;>
            simp [stepCore, mapState, mapPhase, mapControl, mapReturnFrame,
              mapStepResult, emptyCurrentStep]
      | cons next rest =>
          simp only [stepCore, mapState, mapPhase, mapControl, List.map_cons]
          rw [realizes.classify next]
          cases hAction : sourceClassify next with
          | call goal clauses =>
              simp [mapDispatchAction, dispatchActionStep, callStep,
                mapState, mapControl, mapCursor, mapPhase, mapReturnFrame,
                mapStepResult]
          | fail =>
              simp [mapDispatchAction, dispatchActionStep, mapState,
                mapControl, mapPhase, mapStepResult]
          | cut =>
              by_cases hDepth : cutDepth ≤ choices.length
              · simp [mapDispatchAction, dispatchActionStep, cutStep,
                  mapState, mapControl, mapCursor, mapPhase, mapReturnFrame,
                  mapStepResult, retainBottom, hDepth]
              · cases hCleanup : memory.restore checkpoint <;>
                  simp [mapDispatchAction, dispatchActionStep, cutStep,
                    mapState, mapControl, mapCursor, mapPhase, mapReturnFrame,
                    mapStepResult, failWith, closeMemory, retainBottom,
                    hDepth, hCleanup]
          | unify left right =>
              simp [mapDispatchAction, dispatchActionStep, beginUnifyStep,
                mapState, mapControl, mapAttempt, mapPhase, mapReturnFrame,
                mapStepResult]
          | isVar address =>
              cases hDeref : memory.heap.deref address with
              | error error =>
                  cases hCleanup : memory.restore checkpoint <;>
                    simp [mapDispatchAction, dispatchActionStep, isVarStep,
                      mapState, mapControl, mapPhase, mapReturnFrame,
                      mapStepResult, failWith, closeMemory, hDeref, hCleanup]
              | ok result =>
                  cases result with
                  | variableCycle cycle =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [mapDispatchAction, dispatchActionStep, isVarStep,
                          mapState, mapControl, mapPhase, mapReturnFrame,
                          mapStepResult, failWith, closeMemory, hDeref,
                          hCleanup]
                  | root root =>
                      cases hCell : memory.heap[root]? with
                      | none =>
                          cases hCleanup : memory.restore checkpoint <;>
                            simp [mapDispatchAction, dispatchActionStep,
                              isVarStep, mapState, mapControl, mapPhase,
                              mapReturnFrame, mapStepResult, failWith,
                              closeMemory, hDeref, hCell, hCleanup]
                      | some cell =>
                          cases cell with
                          | var identity link =>
                              cases link <;>
                                simp [mapDispatchAction, dispatchActionStep,
                                  isVarStep, mapState, mapControl, mapPhase,
                                  mapReturnFrame, mapStepResult, hDeref, hCell]
                          | const symbol =>
                              simp [mapDispatchAction, dispatchActionStep,
                                isVarStep, mapState, mapControl, mapPhase,
                                mapReturnFrame, mapStepResult, hDeref, hCell]
                          | app symbol args =>
                              simp [mapDispatchAction, dispatchActionStep,
                                isVarStep, mapState, mapControl, mapPhase,
                                mapReturnFrame, mapStepResult, hDeref, hCell]
          | error reason =>
              cases hCleanup : memory.restore checkpoint <;>
                simp [mapDispatchAction, dispatchActionStep, mapState,
                  mapControl, mapPhase, mapStepResult, failWith, closeMemory,
                  hCleanup]
  | select cursor =>
      rcases cursor with ⟨cursorCheckpoint, goal, clauses, cutDepth, frames⟩
      cases clauses with
      | nil =>
          simp [stepCore, mapState, mapPhase, mapControl, mapCursor,
            mapStepResult, selectStep]
      | cons clause remaining =>
          simp only [stepCore, mapState, mapPhase, mapCursor, selectStep,
            List.map_cons]
          rw [realizes.materialize memory nextScope clause]
          cases hMaterialize :
              sourceMaterializer.materialize memory nextScope clause with
          | error error =>
              cases hCleanup : memory.restore checkpoint <;>
                simp [Except.map, mapStepResult, mapState, mapControl,
                  mapCursor, mapPhase, failWith, closeMemory, hMaterialize,
                  hCleanup]
          | ok copied =>
              by_cases hPredicate : goal.symbol = copied.head.symbol
              · by_cases hArity : goal.args.size = copied.head.args.size
                · cases remaining <;>
                    simp [Except.map, mapMaterializedBody, mapStepResult,
                      mapState, mapControl, mapCursor, mapAttempt, mapPhase,
                      mapReturnFrame, replacementChoices, hMaterialize,
                      RuntimeClauseEntry.enter, hPredicate, hArity]
                · cases hCleanup : memory.restore checkpoint <;>
                    simp [Except.map, mapMaterializedBody, mapStepResult,
                      mapState, mapControl, mapCursor, mapAttempt, mapPhase,
                      mapReturnFrame, replacementChoices, failWith,
                      closeMemory, hMaterialize, RuntimeClauseEntry.enter,
                      hPredicate, hArity, hCleanup]
              · cases hCleanup : memory.restore checkpoint <;>
                  simp [Except.map, mapMaterializedBody, mapStepResult,
                    mapState, mapControl, mapCursor, mapAttempt, mapPhase,
                    mapReturnFrame, replacementChoices, failWith,
                    closeMemory, hMaterialize, RuntimeClauseEntry.enter,
                    hPredicate, hCleanup]
  | unifying attempt machine =>
      cases machine with
      | running running =>
          cases hStep : RuntimeUnification.step (.running running) <;>
            cases hCleanup : memory.restore checkpoint <;>
            simp [stepCore, mapState, mapPhase, mapControl, mapAttempt,
              mapCursor, mapStepResult, unifyingStep, failWith, closeMemory,
              hStep, hCleanup]
      | terminal result =>
          cases result with
          | success successMemory =>
              simp [stepCore, mapState, mapPhase, mapControl, mapAttempt,
                mapCursor, mapStepResult, unifyingStep]
          | failure failureMemory =>
              simp [stepCore, mapState, mapPhase, mapControl, mapAttempt,
                mapCursor, mapStepResult, unifyingStep]
          | runtimeError error errorMemory =>
              cases hCleanup : errorMemory.restore checkpoint <;>
                simp [stepCore, mapState, mapPhase, mapControl, mapAttempt,
                  mapCursor, mapStepResult, unifyingStep, failWith,
                  closeMemory, hCleanup]

/-- Demand-driven execution conserves the realization for every exact fuel
prefix.  In particular, open prefixes remain open and answers keep the same
memory and query-variable roots. -/
theorem pullCore_conserves [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols] [DecidableEq sigma.relationSymbols]
    {sourceMaterializer : ClauseMaterializer sigma Instruction₁ SourceClause₁}
    {targetMaterializer : ClauseMaterializer sigma Instruction₂ SourceClause₂}
    {sourceClassify : Instruction₁ → DispatchAction sigma SourceClause₁}
    {targetClassify : Instruction₂ → DispatchAction sigma SourceClause₂}
    {instruction : Instruction₁ → Instruction₂}
    {sourceClause : SourceClause₁ → SourceClause₂}
    (realizes : Realization sourceMaterializer targetMaterializer
      sourceClassify targetClassify instruction sourceClause) :
    ∀ fuel (state : StateCore sigma Instruction₁ SourceClause₁),
      pullCore targetMaterializer targetClassify fuel
          (mapState instruction sourceClause state) =
        mapPullResult instruction sourceClause
          (pullCore sourceMaterializer sourceClassify fuel state) := by
  intro fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel inductionHypothesis =>
      intro state
      simp only [pullCore]
      rw [stepCore_conserves realizes state]
      cases hStep : stepCore sourceMaterializer sourceClassify state with
      | terminal result => rfl
      | next next observation =>
          cases observation with
          | none => exact inductionHypothesis next
          | some observation => cases observation; rfl

end Conservation
end Mettapedia.Logic.LP.RuntimeQuery
