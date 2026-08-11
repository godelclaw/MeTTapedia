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

/-- Map the recovery payload of one catch delimiter. -/
def mapCatchHandler (instruction : Instruction₁ → Instruction₂)
    (handler : CatchHandlerCore sigma Instruction₁) :
    CatchHandlerCore sigma Instruction₂ where
  checkpoint := handler.checkpoint
  choiceDepth := handler.choiceDepth
  catcher := handler.catcher
  recovery := handler.recovery.map instruction

/-- Map a saved continuation without changing its cut depth. -/
def mapReturnFrame (instruction : Instruction₁ → Instruction₂)
    (frame : ReturnFrameCore sigma Instruction₁) :
    ReturnFrameCore sigma Instruction₂ where
  continuation := frame.continuation.map instruction
  callerCutDepth := frame.callerCutDepth
  commit := frame.commit
  handler := frame.handler.map (mapCatchHandler instruction)
  collection := frame.collection

/-- Map the instruction payloads retained by catcher selection. -/
def mapCatchTarget (instruction : Instruction₁ → Instruction₂)
    (target : CatchTargetCore sigma Instruction₁) :
    CatchTargetCore sigma Instruction₂ where
  frame := mapReturnFrame instruction target.frame
  handler := mapCatchHandler instruction target.handler
  outerFrames := target.outerFrames.map (mapReturnFrame instruction)

def mapCatchSelection (instruction : Instruction₁ → Instruction₂)
    (selection : CatchSelectionCore sigma Instruction₁) :
    CatchSelectionCore sigma Instruction₂ where
  packet := selection.packet
  target := mapCatchTarget instruction selection.target
  throwMemory := selection.throwMemory
  packetRoot := selection.packetRoot

/-- Catcher search depends only on frame position and therefore commutes with
instruction representation changes. -/
@[simp]
theorem findCatchTarget_map (instruction : Instruction₁ → Instruction₂)
    (frames : List (ReturnFrameCore sigma Instruction₁)) :
    findCatchTarget (frames.map (mapReturnFrame instruction)) =
      (findCatchTarget frames).map (mapCatchTarget instruction) := by
  induction frames with
  | nil => rfl
  | cons frame outer inductionHypothesis =>
      cases hHandler : frame.handler with
      | none =>
          simp [findCatchTarget, mapReturnFrame, hHandler,
            inductionHypothesis]
      | some handler =>
          simp [findCatchTarget, mapReturnFrame, mapCatchTarget,
            mapCatchHandler, hHandler]

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

/-- Map a saved structured-control alternative without changing its owned
checkpoint. -/
def mapBranchChoice (instruction : Instruction₁ → Instruction₂)
    (alternative : BranchChoiceCore sigma Instruction₁) :
    BranchChoiceCore sigma Instruction₂ where
  checkpoint := alternative.checkpoint
  control := mapControl instruction alternative.control

/-- Map the transferred outer continuation of a collection sentinel while
leaving its detached answers and list encoding unchanged. -/
def mapCollectionChoice (instruction : Instruction₁ → Instruction₂)
    (boundary : CollectionChoiceCore sigma Instruction₁) :
    CollectionChoiceCore sigma Instruction₂ where
  checkpoint := boundary.checkpoint
  template := boundary.template
  bag := boundary.bag
  encoding := boundary.encoding
  continuation := boundary.continuation.map instruction
  callerCutDepth := boundary.callerCutDepth
  outerFrames := boundary.outerFrames.map (mapReturnFrame instruction)
  reversed := boundary.reversed

/-- Map the saved continuation of a database-clause cursor while leaving its
stable references, canonical clause terms, and success action unchanged. -/
def mapDatabaseClauseCursor (instruction : Instruction₁ → Instruction₂)
    (cursor : DatabaseClauseCursorCore sigma Instruction₁) :
    DatabaseClauseCursorCore sigma Instruction₂ where
  checkpoint := cursor.checkpoint
  pattern := cursor.pattern
  candidates := cursor.candidates
  control := mapControl instruction cursor.control
  action := cursor.action

/-- Map either resource kind in the one canonical choice stack. -/
def mapChoicePoint (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) :
    ChoicePointCore sigma Instruction₁ SourceClause₁ →
      ChoicePointCore sigma Instruction₂ SourceClause₂
  | .clause cursor => .clause (mapCursor instruction sourceClause cursor)
  | .branch alternative => .branch (mapBranchChoice instruction alternative)
  | .softElse alternative =>
      .softElse (mapBranchChoice instruction alternative)
  | .collection boundary =>
      .collection (mapCollectionChoice instruction boundary)
  | .databaseClause cursor =>
      .databaseClause (mapDatabaseClauseCursor instruction cursor)

/-- Recording a private collection answer changes only the sentinel's detached
answer list and therefore commutes with instruction and clause representation
changes. -/
@[simp]
theorem recordCollectionChoice_map
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (mark : Nat) (answer : Term sigma.scoped)
    (choices : List (ChoicePointCore sigma Instruction₁ SourceClause₁)) :
    recordCollectionChoice mark answer
        (choices.map (mapChoicePoint instruction sourceClause)) =
      (recordCollectionChoice mark answer choices).map
        (List.map (mapChoicePoint instruction sourceClause)) := by
  induction choices with
  | nil => rfl
  | cons choice older ih =>
      simp only [List.map_cons, recordCollectionChoice, List.length_map]
      by_cases h : older.length = mark
      · simp [h]
        cases choice <;> rfl
      · simp only [h, if_false]
        rw [ih]
        cases recordCollectionChoice mark answer older <;> rfl

/-- Removing a soft-conditional delimiter is independent of the instruction
and source-clause representation. -/
@[simp]
theorem eraseSoftElseAboveBottom_map
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (mark : Nat)
    (choices : List (ChoicePointCore sigma Instruction₁ SourceClause₁)) :
    eraseSoftElseAboveBottom mark
        (choices.map (mapChoicePoint instruction sourceClause)) =
      (eraseSoftElseAboveBottom mark choices).map
        (mapChoicePoint instruction sourceClause) := by
  induction choices with
  | nil => rfl
  | cons choice older ih =>
      simp only [List.map_cons, eraseSoftElseAboveBottom, List.length_map]
      by_cases h : older.length = mark
      · simp [h]
        cases choice <;> rfl
      · simp [h, ih]

/-- Map a selected clause body while retaining the canonical unifier state. -/
def mapAttempt (instruction : Instruction₁ → Instruction₂)
    (attempt : AttemptCore sigma Instruction₁) :
    AttemptCore sigma Instruction₂ where
  body := attempt.body.map instruction
  cutDepth := attempt.cutDepth
  frames := attempt.frames.map (mapReturnFrame instruction)
  onSuccess := attempt.onSuccess

/-- Map one phase of the shared machine. -/
def mapPhase (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) :
    PhaseCore sigma Instruction₁ SourceClause₁ →
      PhaseCore sigma Instruction₂ SourceClause₂
  | .dispatch => .dispatch
  | .select cursor => .select (mapCursor instruction sourceClause cursor)
  | .unifying attempt machine => .unifying (mapAttempt instruction attempt) machine
  | .raising packet => .raising packet
  | .catchSelecting selection machine =>
      .catchSelecting (mapCatchSelection instruction selection) machine
  | .catchRecovering selection machine =>
      .catchRecovering (mapCatchSelection instruction selection) machine
  | .databaseClauseSelect cursor =>
      .databaseClauseSelect (mapDatabaseClauseCursor instruction cursor)
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
  choices := state.choices.map (mapChoicePoint instruction sourceClause)
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

/-- Representation change on a classifier result.  Branch payloads are mapped,
while choice creation, ordering, checkpointing, and resumption remain owned by
the shared engine. -/
def mapDispatchAction (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) :
    DispatchAction sigma Instruction₁ SourceClause₁ →
      DispatchAction sigma Instruction₂ SourceClause₂
  | .call goal clauses => .call goal (clauses.map sourceClause)
  | .fail => .fail
  | .cut => .cut
  | .branch left right =>
      .branch (left.map instruction) (right.map instruction)
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse (condition.map instruction) (thenBranch.map instruction)
        (elseBranch.map instruction)
  | .softIfThenElse condition thenBranch elseBranch =>
      .softIfThenElse (condition.map instruction) (thenBranch.map instruction)
        (elseBranch.map instruction)
  | .once goals => .once (goals.map instruction)
  | .findall template generator bag encoding =>
      .findall template (generator.map instruction) bag encoding
  | .metaCall callable extraArgs => .metaCall callable extraArgs
  | .dcgCall body input rest => .dcgCall body input rest
  | .format destination format arguments decoder =>
      .format destination format arguments decoder
  | .catch guarded catcher recovery =>
      .catch (guarded.map instruction) catcher (recovery.map instruction)
  | .throw ball unboundError => .throw ball unboundError
  | .unify left right => .unify left right
  | .termTest address test => .termTest address test
  | .termIdentity left right expected =>
      .termIdentity left right expected
  | .univ termRoot listRoot encoding =>
      .univ termRoot listRoot encoding
  | .integerIs resultRoot expressionRoot encoding =>
      .integerIs resultRoot expressionRoot encoding
  | .integerCompare leftRoot rightRoot comparison encoding =>
      .integerCompare leftRoot rightRoot comparison encoding
  | .database request => .database request
  | .error reason => .error reason

/-- Representation change on one shared-machine result. -/
def mapStepResult (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) :
    StepResultCore sigma Instruction₁ SourceClause₁ →
      StepResultCore sigma Instruction₂ SourceClause₂
  | .next state observation =>
      .next (mapState instruction sourceClause state) observation
  | .databaseRequest request state =>
      .databaseRequest request (mapState instruction sourceClause state)
  | .terminal result => .terminal result

/-- Privately capturing one generator answer is representation-independent:
the shared engine reads the same heap, advances the same persistent scope, and
updates the same positional collection sentinel. -/
theorem collectAnswerStep_conserves
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (handler : CollectionHandlerCore sigma) :
    collectAnswerStep (mapState instruction sourceClause state) handler =
      mapStepResult instruction sourceClause
        (collectAnswerStep state handler) := by
  rcases state with ⟨memory, control, choices, checkpoint, queryVarMap,
    nextScope, phase⟩
  cases hCapture : RuntimeException.capture memory.heap handler.template with
  | error error =>
      cases hCleanup : memory.restore checkpoint <;>
        simp [collectAnswerStep, mapState, mapControl, mapPhase,
          mapStepResult, failWith, closeMemory, hCapture, hCleanup]
  | ok packet =>
      cases hRecord : recordCollectionChoice handler.choiceDepth
          (packet.freshTerm nextScope) choices with
      | none =>
          cases hCleanup : memory.restore checkpoint <;>
            simp [collectAnswerStep, mapState, mapControl, mapPhase,
              mapStepResult, failWith, closeMemory,
              hCapture, hRecord, hCleanup]
      | some updated =>
          simp [collectAnswerStep, mapState, mapControl, mapPhase,
            mapStepResult, hCapture, hRecord]

/-- Exhausting a collection restores and materializes the same finite answer
list on either representation; only the saved instruction continuation is
mapped. -/
theorem finalizeCollectionStep_conserves [DecidableEq sigma.scoped.vars]
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (boundary : CollectionChoiceCore sigma Instruction₁)
    (older : List (ChoicePointCore sigma Instruction₁ SourceClause₁)) :
    finalizeCollectionStep (mapState instruction sourceClause state)
        (mapCollectionChoice instruction boundary)
        (older.map (mapChoicePoint instruction sourceClause)) =
      mapStepResult instruction sourceClause
        (finalizeCollectionStep state boundary older) := by
  rcases state with ⟨stateMemory, control, choices, checkpoint, queryVarMap,
    nextScope, phase⟩
  cases hRestore : stateMemory.restore boundary.checkpoint with
  | error error =>
      cases hCleanup : stateMemory.restore checkpoint <;>
        simp [finalizeCollectionStep, mapState, mapControl, mapPhase,
          mapCollectionChoice, mapStepResult, failWith,
          closeMemory, hRestore, hCleanup]
  | ok restored =>
      cases hMaterialize : RuntimeMaterialize.materializeTerm restored
          (boundary.encoding.listTerm boundary.reversed.reverse) with
      | error error =>
          cases hCleanup : restored.restore checkpoint <;>
            simp [finalizeCollectionStep, mapState, mapControl, mapPhase,
              mapCollectionChoice, mapStepResult, failWith,
              closeMemory, hRestore, hMaterialize, hCleanup]
      | ok result =>
          simp [finalizeCollectionStep, mapState, mapControl, mapPhase,
            mapCollectionChoice, mapAttempt,
            mapStepResult, hRestore, hMaterialize]

/-- Ordinary finite packet capture is independent of instruction and clause
representations. -/
theorem captureThrowStep_conserves
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (ball : Addr) :
    captureThrowStep (mapState instruction sourceClause state) ball =
      mapStepResult instruction sourceClause (captureThrowStep state ball) := by
  rcases state with ⟨memory, control, choices, checkpoint, queryVarMap,
    nextScope, phase⟩
  cases hCapture : RuntimeException.capture memory.heap ball with
  | error error =>
      cases hCleanup : memory.restore checkpoint <;>
        simp [captureThrowStep, mapState, mapControl, mapPhase,
          mapStepResult, failWith, closeMemory, hCapture, hCleanup]
  | ok packet =>
      simp [captureThrowStep, mapState, mapControl, mapPhase,
        mapStepResult, hCapture]

/-- The engine-owned unbound-root check and its language-supplied packet also
commute with instruction and clause representation changes. -/
theorem throwStep_conserves
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (ball : Addr) (unboundError : Option (RuntimeException.Packet sigma)) :
    throwStep (mapState instruction sourceClause state) ball unboundError =
      mapStepResult instruction sourceClause
        (throwStep state ball unboundError) := by
  cases unboundError with
  | none =>
      simpa [throwStep] using
        captureThrowStep_conserves instruction sourceClause state ball
  | some errorPacket =>
      cases hDeref : state.memory.heap.deref ball with
      | error error =>
          simpa [throwStep, mapState, hDeref] using
            captureThrowStep_conserves instruction sourceClause state ball
      | ok result =>
          cases result with
          | variableCycle cycle =>
              simpa [throwStep, mapState, hDeref] using
                captureThrowStep_conserves instruction sourceClause state ball
          | root root =>
              cases hCell : state.memory.heap[root]? with
              | none =>
                  simpa [throwStep, mapState, hDeref, hCell] using
                    captureThrowStep_conserves instruction sourceClause state ball
              | some cell =>
                  cases cell with
                  | var identity link =>
                      cases link with
                      | none =>
                          simp [throwStep, mapState, mapControl, mapPhase,
                            mapStepResult, hDeref, hCell]
                      | some target =>
                          simpa [throwStep, mapState, hDeref, hCell] using
                            captureThrowStep_conserves instruction sourceClause
                              state ball
                  | const symbol =>
                      simpa [throwStep, mapState, hDeref, hCell] using
                        captureThrowStep_conserves instruction sourceClause
                          state ball
                  | app symbol arguments =>
                      simpa [throwStep, mapState, hDeref, hCell] using
                        captureThrowStep_conserves instruction sourceClause
                          state ball

set_option linter.unusedSimpArgs false in
theorem passException_conserves
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (selection : CatchSelectionCore sigma Instruction₁) :
    passException (mapState instruction sourceClause state)
        (mapCatchSelection instruction selection) =
      mapStepResult instruction sourceClause
        (passException state selection) := by
  rcases state with ⟨stateMemory, control, choices, checkpoint, queryVarMap,
    nextScope, phase⟩
  rcases selection with ⟨packet, target, throwMemory, packetRoot⟩
  rcases target with ⟨frame, handler, outerFrames⟩
  cases hOuter : findCatchTarget outerFrames with
  | none =>
      cases hCleanup : throwMemory.restore checkpoint <;>
        simp [passException, raiseUnhandled, mapState, mapPhase, mapControl,
          mapCatchSelection, mapCatchTarget, mapCatchHandler, mapReturnFrame,
          mapChoicePoint, mapStepResult, findCatchTarget_map, closeMemory,
          hOuter, hCleanup]
  | some nextTarget =>
      simp [passException, mapState, mapPhase, mapControl,
        mapCatchSelection, mapCatchTarget, mapCatchHandler, mapReturnFrame,
        mapChoicePoint, mapStepResult, findCatchTarget_map, hOuter]

set_option linter.unusedSimpArgs false in
theorem beginCatchRecovery_conserves [DecidableEq sigma.scoped.vars]
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (selection : CatchSelectionCore sigma Instruction₁)
    (memory : Memory sigma.scoped) :
    beginCatchRecovery (mapState instruction sourceClause state)
        (mapCatchSelection instruction selection) memory =
      mapStepResult instruction sourceClause
        (beginCatchRecovery state selection memory) := by
  rcases state with ⟨stateMemory, control, choices, checkpoint, queryVarMap,
    nextScope, phase⟩
  rcases selection with ⟨packet, target, throwMemory, packetRoot⟩
  rcases target with ⟨frame, handler, outerFrames⟩
  by_cases hDepth : handler.choiceDepth ≤ choices.length
  · cases hRestore : memory.restore handler.checkpoint with
    | error error =>
        cases hCleanup : memory.restore checkpoint <;>
          simp [beginCatchRecovery, mapState, mapPhase, mapControl,
            mapCatchSelection, mapCatchTarget, mapCatchHandler,
            mapReturnFrame, mapChoicePoint, mapStepResult, failWith,
            closeMemory, hDepth, hRestore, hCleanup]
    | ok restored =>
        cases hInstall : packet.install restored nextScope with
        | error error =>
            cases hCleanup : restored.restore checkpoint <;>
              simp [beginCatchRecovery, mapState, mapPhase, mapControl,
                mapCatchSelection, mapCatchTarget, mapCatchHandler,
                mapReturnFrame, mapChoicePoint, mapStepResult, failWith,
                closeMemory, hDepth, hRestore, hInstall, hCleanup]
        | ok installed =>
            simp [beginCatchRecovery, mapState, mapPhase, mapControl,
              mapCatchSelection, mapCatchTarget, mapCatchHandler,
              mapReturnFrame, mapChoicePoint, mapStepResult, retainBottom,
              hDepth, hRestore, hInstall]
  · cases hCleanup : memory.restore checkpoint <;>
      simp [beginCatchRecovery, mapState, mapPhase, mapControl,
        mapCatchSelection, mapCatchTarget, mapCatchHandler, mapReturnFrame,
        mapChoicePoint, mapStepResult, failWith, closeMemory, hDepth, hCleanup]

set_option linter.unusedSimpArgs false in
theorem raisingStep_conserves [DecidableEq sigma.scoped.vars]
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (packet : RuntimeException.Packet sigma) :
    raisingStep (mapState instruction sourceClause state) packet =
      mapStepResult instruction sourceClause (raisingStep state packet) := by
  rcases state with ⟨memory, control, choices, checkpoint, queryVarMap,
    nextScope, phase⟩
  cases hTarget : findCatchTarget control.frames with
  | none =>
      cases hCleanup : memory.restore checkpoint <;>
        simp [raisingStep, raiseUnhandled, mapState, mapPhase, mapControl,
          mapStepResult, findCatchTarget_map, hTarget, closeMemory, hCleanup]
  | some target =>
      cases hInstall : packet.install memory nextScope with
      | error error =>
          cases hCleanup : memory.restore checkpoint <;>
            simp [raisingStep, mapState, mapPhase, mapControl, mapStepResult,
              findCatchTarget_map, hTarget, failWith, closeMemory, hInstall,
              hCleanup]
      | ok installed =>
          simp [raisingStep, mapState, mapPhase, mapControl, mapStepResult,
            mapCatchSelection, mapCatchTarget, mapCatchHandler,
            findCatchTarget_map, hTarget, hInstall]

set_option linter.unusedSimpArgs false in
theorem catchSelectingStep_conserves [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (selection : CatchSelectionCore sigma Instruction₁)
    (machine : RuntimeUnification.Machine sigma.scoped) :
    catchSelectingStep (mapState instruction sourceClause state)
        (mapCatchSelection instruction selection) machine =
      mapStepResult instruction sourceClause
        (catchSelectingStep state selection machine) := by
  cases machine with
  | running running =>
      cases hStep : RuntimeUnification.step (.running running) with
      | none =>
          rcases state with ⟨memory, control, choices, checkpoint, queryVarMap,
            nextScope, phase⟩
          cases hCleanup : memory.restore checkpoint <;>
            simp [catchSelectingStep, mapState, mapPhase, mapControl,
              mapStepResult, failWith, closeMemory, hStep, hCleanup]
      | some next =>
          simp [catchSelectingStep, mapState, mapPhase, mapControl,
            mapStepResult, hStep]
  | terminal result =>
      cases result with
      | success memory =>
          exact beginCatchRecovery_conserves instruction sourceClause state
            selection memory
      | failure memory =>
          exact passException_conserves instruction sourceClause state
            selection
      | runtimeError error memory =>
          rcases state with ⟨stateMemory, control, choices, checkpoint,
            queryVarMap, nextScope, phase⟩
          cases hCleanup : memory.restore checkpoint <;>
            simp [catchSelectingStep, mapState, mapPhase, mapControl,
              mapStepResult, failWith, closeMemory, hCleanup]

set_option linter.unusedSimpArgs false in
theorem catchRecoveringStep_conserves [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols]
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂)
    (state : StateCore sigma Instruction₁ SourceClause₁)
    (selection : CatchSelectionCore sigma Instruction₁)
    (machine : RuntimeUnification.Machine sigma.scoped) :
    catchRecoveringStep (mapState instruction sourceClause state)
        (mapCatchSelection instruction selection) machine =
      mapStepResult instruction sourceClause
        (catchRecoveringStep state selection machine) := by
  cases machine with
  | running running =>
      cases hStep : RuntimeUnification.step (.running running) with
      | none =>
          rcases state with ⟨memory, control, choices, checkpoint, queryVarMap,
            nextScope, phase⟩
          cases hCleanup : memory.restore checkpoint <;>
            simp [catchRecoveringStep, mapState, mapPhase, mapControl,
              mapStepResult, failWith, closeMemory, hStep, hCleanup]
      | some next =>
          simp [catchRecoveringStep, mapState, mapPhase, mapControl,
            mapStepResult, hStep]
  | terminal result =>
      cases result with
      | success memory =>
          rcases selection with ⟨packet, target, throwMemory, packetRoot⟩
          rcases target with ⟨frame, handler, outerFrames⟩
          simp [catchRecoveringStep, mapState, mapPhase, mapControl,
            mapCatchSelection, mapCatchTarget, mapCatchHandler,
            mapReturnFrame, mapStepResult]
      | failure memory =>
          exact passException_conserves instruction sourceClause state
            selection
      | runtimeError error memory =>
          rcases state with ⟨stateMemory, control, choices, checkpoint,
            queryVarMap, nextScope, phase⟩
          cases hCleanup : memory.restore checkpoint <;>
            simp [catchRecoveringStep, mapState, mapPhase, mapControl,
              mapStepResult, failWith, closeMemory, hCleanup]

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
    (sourceClassify : Instruction₁ →
      DispatchAction sigma Instruction₁ SourceClause₁)
    (targetClassify : Instruction₂ →
      DispatchAction sigma Instruction₂ SourceClause₂)
    (instruction : Instruction₁ → Instruction₂)
    (sourceClause : SourceClause₁ → SourceClause₂) : Prop where
  materialize : ∀ memory scope clause,
    targetMaterializer.materialize memory scope (sourceClause clause) =
      (sourceMaterializer.materialize memory scope clause).map
        (mapMaterializedBody instruction)
  classify : ∀ next,
    targetClassify (instruction next) =
      mapDispatchAction instruction sourceClause (sourceClassify next)

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
theorem stepCore_conserves [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols] [DecidableEq sigma.relationSymbols]
    {sourceMaterializer : ClauseMaterializer sigma Instruction₁ SourceClause₁}
    {targetMaterializer : ClauseMaterializer sigma Instruction₂ SourceClause₂}
    {sourceClassify : Instruction₁ →
      DispatchAction sigma Instruction₁ SourceClause₁}
    {targetClassify : Instruction₂ →
      DispatchAction sigma Instruction₂ SourceClause₂}
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
  | raising packet =>
      simpa [stepCore, stepCoreWithMeta, mapState, mapPhase] using
        raisingStep_conserves instruction sourceClause
          (StateCore.mk memory control choices checkpoint queryVarMap nextScope
            (.raising packet)) packet
  | catchSelecting selection machine =>
      simpa [stepCore, stepCoreWithMeta, mapState, mapPhase] using
        catchSelectingStep_conserves instruction sourceClause
          (StateCore.mk memory control choices checkpoint queryVarMap nextScope
            (.catchSelecting selection machine)) selection machine
  | catchRecovering selection machine =>
      simpa [stepCore, stepCoreWithMeta, mapState, mapPhase] using
        catchRecoveringStep_conserves instruction sourceClause
          (StateCore.mk memory control choices checkpoint queryVarMap nextScope
            (.catchRecovering selection machine)) selection machine
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
          cases cursor with
          | clause cursor =>
              cases hRestore : memory.restore cursor.checkpoint <;>
                cases hCleanup : memory.restore checkpoint <;>
                simp [stepCore, mapState, mapPhase, mapControl, mapCursor,
                  mapChoicePoint, mapStepResult, backtrackStep, failWith,
                  closeMemory, hRestore, hCleanup]
          | branch alternative =>
              cases hRestore : memory.restore alternative.checkpoint <;>
                cases hCleanup : memory.restore checkpoint <;>
                simp [stepCore, mapState, mapPhase, mapControl,
                  mapBranchChoice, mapChoicePoint, mapStepResult,
                  backtrackStep, resumeBranchStep, failWith, closeMemory,
                  hRestore, hCleanup]
          | softElse alternative =>
              cases hRestore : memory.restore alternative.checkpoint <;>
                cases hCleanup : memory.restore checkpoint <;>
                simp [stepCore, mapState, mapPhase, mapControl,
                  mapBranchChoice, mapChoicePoint, mapStepResult,
                  backtrackStep, resumeBranchStep, failWith, closeMemory,
                  hRestore, hCleanup]
          | collection boundary =>
              simpa [stepCore, mapState, mapPhase, mapControl,
                mapChoicePoint, backtrackStep] using
                finalizeCollectionStep_conserves instruction sourceClause
                  (StateCore.mk memory control
                    (.collection boundary :: older) checkpoint queryVarMap
                    nextScope .backtrack) boundary older
          | databaseClause cursor =>
              cases hRestore : memory.restore cursor.checkpoint <;>
                cases hCleanup : memory.restore checkpoint <;>
                simp [stepCore, mapState, mapPhase, mapControl,
                  mapDatabaseClauseCursor, mapChoicePoint, mapStepResult,
                  backtrackStep, failWith, closeMemory, hRestore, hCleanup]
  | dispatch =>
      rcases control with ⟨current, cutDepth, frames⟩
      cases current with
      | nil =>
          cases frames with
          | nil =>
              simp [stepCore, mapState, mapPhase, mapControl,
                mapStepResult, emptyCurrentStep]
          | cons frame frames =>
              rcases frame with
                ⟨continuation, callerCutDepth, commit, handlerOption,
                  collectionOption⟩
              cases collectionOption with
              | some handler =>
                  simpa [stepCore, mapState, mapPhase, mapControl,
                    mapReturnFrame, emptyCurrentStep] using
                    collectAnswerStep_conserves instruction sourceClause
                      (StateCore.mk memory
                        ⟨[], cutDepth,
                          ⟨continuation, callerCutDepth, commit, handlerOption,
                            some handler⟩ :: frames⟩
                        choices checkpoint queryVarMap nextScope .dispatch)
                      handler
              | none =>
                  cases commit with
                  | ordinary =>
                      simp [stepCore, mapState, mapPhase, mapControl,
                        mapReturnFrame, mapStepResult, emptyCurrentStep]
                  | hard mark =>
                      by_cases hDepth : mark ≤ choices.length
                      · simp [stepCore, mapState, mapPhase, mapControl,
                          mapReturnFrame, mapChoicePoint, mapStepResult,
                          emptyCurrentStep, retainBottom, hDepth]
                      · cases hCleanup : memory.restore checkpoint <;>
                          simp [stepCore, mapState, mapPhase, mapControl,
                            mapReturnFrame, mapChoicePoint, mapStepResult,
                            emptyCurrentStep, failWith, closeMemory, hDepth,
                            hCleanup]
                  | soft mark =>
                      by_cases hDepth : mark ≤ choices.length
                      · simp [stepCore, mapState, mapPhase, mapControl,
                          mapReturnFrame, mapChoicePoint, mapStepResult,
                          emptyCurrentStep, hDepth]
                      · cases hCleanup : memory.restore checkpoint <;>
                          simp [stepCore, mapState, mapPhase, mapControl,
                            mapReturnFrame, mapChoicePoint, mapStepResult,
                            emptyCurrentStep, failWith, closeMemory, hDepth,
                            hCleanup]
      | cons next rest =>
          simp only [stepCore, stepCoreWithMeta, mapState, mapPhase, mapControl,
            List.map_cons]
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
          | branch left right =>
              simp [mapDispatchAction, dispatchActionStep, branchStep,
                mapState, mapControl, mapBranchChoice, mapChoicePoint,
                mapPhase, mapReturnFrame, mapStepResult, List.map_append]
          | ifThenElse condition thenBranch elseBranch =>
              simp [mapDispatchAction, dispatchActionStep, ifThenElseStep,
                mapState, mapControl, mapBranchChoice, mapChoicePoint,
                mapPhase, mapReturnFrame, mapStepResult, List.map_append]
          | softIfThenElse condition thenBranch elseBranch =>
              simp [mapDispatchAction, dispatchActionStep, softIfThenElseStep,
                mapState, mapControl, mapBranchChoice, mapChoicePoint,
                mapPhase, mapReturnFrame, mapStepResult, List.map_append]
          | once goals =>
              simp [mapDispatchAction, dispatchActionStep, onceStep,
                mapState, mapControl, mapPhase, mapReturnFrame, mapStepResult]
          | findall template generator bag encoding =>
              simp [mapDispatchAction, dispatchActionStep, findallStep,
                mapState, mapControl, mapPhase, mapReturnFrame,
                mapCollectionChoice, mapChoicePoint, mapStepResult,
                List.map_append]
          | metaCall callable extraArgs =>
              cases hCleanup : memory.restore checkpoint <;>
                simp [mapDispatchAction, dispatchActionStep, metaCallStep,
                  rejectingMetaCallDecoder, mapState, mapControl, mapPhase,
                  mapReturnFrame, mapStepResult, failWith, closeMemory,
                  hCleanup]
          | dcgCall body input restRoot =>
              cases hCleanup : memory.restore checkpoint <;>
                simp [mapDispatchAction, dispatchActionStep, dcgCallStep,
                  rejectingMetaCallDecoder, mapState, mapControl, mapPhase,
                  mapReturnFrame, mapStepResult, failWith, closeMemory,
                  hCleanup]
          | format destination format arguments decoder =>
              cases hDecode : decoder.decode memory.heap destination format
                  arguments with
              | error reason =>
                  cases hCleanup : memory.restore checkpoint <;>
                    simp [mapDispatchAction, dispatchActionStep, formatStep,
                      mapState, mapControl, mapPhase, mapReturnFrame,
                      mapStepResult, failWith, closeMemory, hDecode, hCleanup]
              | ok plan =>
                  cases plan with
                  | codes encoding head tail values =>
                      cases hAllocate : allocateConstants memory values with
                      | error error =>
                          cases hCleanup : memory.restore checkpoint <;>
                            simp [mapDispatchAction, dispatchActionStep,
                              formatStep, dcgConstantTerminalsStep,
                              mapState, mapControl, mapPhase, mapReturnFrame,
                              mapStepResult, failWith, closeMemory, hDecode,
                              hAllocate, hCleanup]
                      | ok allocated =>
                          rcases allocated with ⟨roots, middle⟩
                          cases hSegment : allocateAddressSegment encoding
                              middle roots tail with
                          | error error =>
                              cases hCleanup : middle.restore checkpoint <;>
                                simp [mapDispatchAction, dispatchActionStep,
                                  formatStep, dcgConstantTerminalsStep,
                                  dcgAddressTerminalsStep, mapState,
                                  mapControl, mapAttempt, mapPhase,
                                  mapReturnFrame, mapStepResult, failWith,
                                  closeMemory, hDecode, hAllocate, hSegment,
                                  hCleanup]
                          | ok segment =>
                              rcases segment with ⟨listRoot, final⟩
                              simp [mapDispatchAction, dispatchActionStep,
                                formatStep, dcgConstantTerminalsStep,
                                dcgAddressTerminalsStep, mapState, mapControl,
                                mapAttempt, mapPhase, mapReturnFrame,
                                mapStepResult, hDecode, hAllocate, hSegment]
          | «catch» guarded catcher recovery =>
              simp [mapDispatchAction, dispatchActionStep, catchStep,
                mapState, mapControl, mapPhase, mapReturnFrame,
                mapCatchHandler, mapStepResult]
          | throw ball unboundError =>
              simpa [mapDispatchAction, dispatchActionStep, mapState,
                mapControl, mapPhase, mapReturnFrame, mapChoicePoint] using
                throwStep_conserves instruction sourceClause
                  { memory := memory
                    control := {
                      current := next :: rest
                      cutDepth
                      frames
                    }
                    choices
                    queryCheckpoint := checkpoint
                    queryVarMap
                    nextScope
                    phase := .dispatch }
                  ball unboundError
          | unify left right =>
              simp [mapDispatchAction, dispatchActionStep, beginUnifyStep,
                mapState, mapControl, mapAttempt, mapPhase, mapReturnFrame,
                mapStepResult]
          | termTest address test =>
              cases hMode : test.mode with
              | properList encoding =>
                  cases hList : termProperList encoding memory.heap address with
                  | error error =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          termTestStep, mapState, mapControl, mapPhase,
                          mapReturnFrame, mapStepResult, failWith, closeMemory,
                          hMode, hList, hCleanup]
                  | ok accepted =>
                      cases accepted <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          termTestStep, mapState, mapControl, mapPhase,
                          mapReturnFrame, mapStepResult, hMode, hList]
              | ground =>
                  cases hGround : termGround memory.heap address with
                  | error error =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          termTestStep, mapState, mapControl, mapPhase,
                          mapReturnFrame, mapStepResult, failWith, closeMemory,
                          hMode, hGround, hCleanup]
                  | ok accepted =>
                      cases accepted <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          termTestStep, mapState, mapControl, mapPhase,
                          mapReturnFrame, mapStepResult, hMode, hGround]
              | shallow =>
                  cases hDeref : memory.heap.deref address with
                  | error error =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          termTestStep, mapState, mapControl, mapPhase,
                          mapReturnFrame, mapStepResult, failWith, closeMemory,
                          hMode, hDeref, hCleanup]
                  | ok result =>
                      cases result with
                      | variableCycle cycle =>
                          cases hCleanup : memory.restore checkpoint <;>
                            simp [mapDispatchAction, dispatchActionStep,
                              termTestStep, mapState, mapControl, mapPhase,
                              mapReturnFrame, mapStepResult, failWith,
                              closeMemory, hMode, hDeref, hCleanup]
                      | root root =>
                          cases hCell : memory.heap[root]? with
                          | none =>
                              cases hCleanup : memory.restore checkpoint <;>
                                simp [mapDispatchAction, dispatchActionStep,
                                  termTestStep, mapState, mapControl, mapPhase,
                                  mapReturnFrame, mapStepResult, failWith,
                                  closeMemory, hMode, hDeref, hCell, hCleanup]
                          | some cell =>
                              cases cell with
                              | var identity link =>
                                  cases link with
                                  | none =>
                                      cases hAccept : test.acceptsVariable <;>
                                        simp [mapDispatchAction,
                                          dispatchActionStep, termTestStep,
                                          TermTest.accepts, mapState,
                                          mapControl, mapPhase, mapReturnFrame,
                                          mapStepResult, hMode, hDeref, hCell,
                                          hAccept]
                                  | some value =>
                                      simp [mapDispatchAction,
                                        dispatchActionStep, termTestStep,
                                        TermTest.accepts, mapState, mapControl,
                                        mapPhase, mapReturnFrame, mapStepResult,
                                        hMode, hDeref, hCell]
                              | const symbol =>
                                  cases hAccept : test.acceptsConstant symbol <;>
                                    simp [mapDispatchAction,
                                      dispatchActionStep, termTestStep,
                                      TermTest.accepts, mapState, mapControl,
                                      mapPhase, mapReturnFrame, mapStepResult,
                                      hMode, hDeref, hCell, hAccept]
                              | app symbol args =>
                                  cases hAccept : test.acceptsApplication <;>
                                    simp [mapDispatchAction,
                                      dispatchActionStep, termTestStep,
                                      TermTest.accepts, mapState, mapControl,
                                      mapPhase, mapReturnFrame, mapStepResult,
                                      hMode, hDeref, hCell, hAccept]
          | termIdentity left right expected =>
              cases hResult : termIdentical memory.heap left right with
              | error error =>
                  cases hCleanup : memory.restore checkpoint <;>
                    simp [mapDispatchAction, dispatchActionStep,
                      termIdentityStep, mapState, mapControl, mapPhase,
                      mapReturnFrame, mapStepResult, failWith, closeMemory,
                      hResult, hCleanup]
              | ok actual =>
                  cases actual <;> cases expected <;>
                    simp [mapDispatchAction, dispatchActionStep,
                      termIdentityStep, mapState, mapControl, mapPhase,
                      mapReturnFrame, mapStepResult, hResult]
          | univ termRoot listRoot encoding =>
              cases hPrepare : prepareUniv encoding memory termRoot listRoot with
              | error error =>
                  cases hCleanup : memory.restore checkpoint <;>
                    simp [mapDispatchAction, dispatchActionStep, univStep,
                      mapState, mapControl, mapAttempt, mapPhase,
                      mapReturnFrame, mapStepResult, failWith, closeMemory,
                      hPrepare, hCleanup]
              | ok prepared =>
                  simp [mapDispatchAction, dispatchActionStep, univStep,
                    mapState, mapControl, mapAttempt, mapPhase,
                    mapReturnFrame, mapStepResult, hPrepare]
          | integerIs resultRoot expressionRoot encoding =>
              cases hEval : evalInteger encoding memory.heap expressionRoot with
              | error error =>
                  cases hCleanup : memory.restore checkpoint <;>
                    simp [mapDispatchAction, dispatchActionStep, integerIsStep,
                      mapState, mapControl, mapAttempt, mapPhase,
                      mapReturnFrame, mapStepResult, failWith, closeMemory,
                      hEval, hCleanup]
              | ok value =>
                  cases hAllocate : memory.allocate
                      (.const (encoding.encodeInteger value)) with
                  | error error =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          integerIsStep, mapState, mapControl, mapAttempt,
                          mapPhase, mapReturnFrame, mapStepResult, failWith,
                          closeMemory, hEval, hAllocate, hCleanup]
                  | ok allocated =>
                      rcases allocated with ⟨valueRoot, nextMemory⟩
                      simp [mapDispatchAction, dispatchActionStep,
                        integerIsStep, mapState, mapControl, mapAttempt,
                        mapPhase, mapReturnFrame, mapStepResult, hEval,
                        hAllocate]
          | integerCompare leftRoot rightRoot comparison encoding =>
              cases hLeft : evalInteger encoding memory.heap leftRoot with
              | error error =>
                  cases hCleanup : memory.restore checkpoint <;>
                    simp [mapDispatchAction, dispatchActionStep,
                      integerCompareStep, mapState, mapControl, mapPhase,
                      mapReturnFrame, mapStepResult, failWith, closeMemory,
                      hLeft, hCleanup]
              | ok left =>
                  cases hRight : evalInteger encoding memory.heap rightRoot with
                  | error error =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          integerCompareStep, mapState, mapControl, mapPhase,
                          mapReturnFrame, mapStepResult, failWith, closeMemory,
                          hLeft, hRight, hCleanup]
                  | ok right =>
                      cases hHolds : comparison.holds left right <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          integerCompareStep, mapState, mapControl, mapPhase,
                          mapReturnFrame, mapStepResult, hLeft, hRight, hHolds]
          | database request =>
              cases request with
              | asserta clauseRoot =>
                  simp [mapDispatchAction, dispatchActionStep,
                    checkedDatabaseRequestStep, databaseRequestStep,
                    mapState, mapControl, mapPhase, mapReturnFrame,
                    mapStepResult]
              | assertz clauseRoot =>
                  simp [mapDispatchAction, dispatchActionStep,
                    checkedDatabaseRequestStep, databaseRequestStep,
                    mapState, mapControl, mapPhase, mapReturnFrame,
                    mapStepResult]
              | retract patternRoot =>
                  simp [mapDispatchAction, dispatchActionStep,
                    checkedDatabaseRequestStep, databaseRequestStep,
                    mapState, mapControl, mapPhase, mapReturnFrame,
                    mapStepResult]
              | clause headRoot bodyRoot referenceRoot =>
                  simp [mapDispatchAction, dispatchActionStep,
                    checkedDatabaseRequestStep, databaseRequestStep,
                    mapState, mapControl, mapPhase, mapReturnFrame,
                    mapStepResult]
              | eraseRef reference =>
                  simp [mapDispatchAction, dispatchActionStep,
                    checkedDatabaseRequestStep, databaseRequestStep,
                    mapState, mapControl, mapPhase, mapReturnFrame,
                    mapStepResult]
              | assertaWithReference clauseRoot referenceRoot =>
                  cases hCheck : checkDatabaseReferenceOutput memory
                      referenceRoot with
                  | error error =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          checkedDatabaseRequestStep, databaseRequestStep,
                          mapState, mapControl, mapPhase, mapReturnFrame,
                          mapStepResult, hCheck, failWith, closeMemory,
                          hCleanup]
                  | ok _ =>
                      simp [mapDispatchAction, dispatchActionStep,
                        checkedDatabaseRequestStep, databaseRequestStep,
                        mapState, mapControl, mapPhase, mapReturnFrame,
                        mapStepResult, hCheck]
              | assertzWithReference clauseRoot referenceRoot =>
                  cases hCheck : checkDatabaseReferenceOutput memory
                      referenceRoot with
                  | error error =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [mapDispatchAction, dispatchActionStep,
                          checkedDatabaseRequestStep, databaseRequestStep,
                          mapState, mapControl, mapPhase, mapReturnFrame,
                          mapStepResult, hCheck, failWith, closeMemory,
                          hCleanup]
                  | ok _ =>
                      simp [mapDispatchAction, dispatchActionStep,
                        checkedDatabaseRequestStep, databaseRequestStep,
                        mapState, mapControl, mapPhase, mapReturnFrame,
                        mapStepResult, hCheck]
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
          simp only [stepCore, stepCoreWithMeta, mapState, mapPhase, mapCursor,
            selectStep,
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
                      mapState, mapControl, mapCursor, mapChoicePoint,
                      mapAttempt, mapPhase,
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
              cases hSuccess : attempt.onSuccess <;>
                simp [stepCore, mapState, mapPhase, mapControl, mapAttempt,
                  mapCursor, mapStepResult, unifyingStep, hSuccess]
          | failure failureMemory =>
              simp [stepCore, mapState, mapPhase, mapControl, mapAttempt,
                mapCursor, mapStepResult, unifyingStep]
          | runtimeError error errorMemory =>
              cases hCleanup : errorMemory.restore checkpoint <;>
                simp [stepCore, mapState, mapPhase, mapControl, mapAttempt,
                  mapCursor, mapStepResult, unifyingStep, failWith,
                  closeMemory, hCleanup]
  | databaseClauseSelect cursor =>
      cases hCandidates : cursor.candidates with
      | nil =>
          simp [stepCore, stepCoreWithMeta, mapState, mapPhase, mapControl,
            mapDatabaseClauseCursor, databaseClauseSelectStep, hCandidates, mapStepResult]
      | cons candidate remaining =>
          cases hMaterialize : RuntimeMaterialize.materializeTerm memory
              (candidate.clause.atScope nextScope) with
          | error error =>
              cases hCleanup : memory.restore checkpoint <;>
                simp [stepCore, stepCoreWithMeta, mapState, mapPhase,
                  mapControl, mapDatabaseClauseCursor, mapChoicePoint, mapAttempt,
                  mapStepResult, databaseClauseSelectStep, hCandidates,
                  hMaterialize, failWith, closeMemory, hCleanup]
          | ok copied =>
              cases hAction : cursor.action with
              | retract =>
                  cases remaining <;>
                    simp [stepCore, stepCoreWithMeta, mapState, mapPhase,
                      mapControl, mapDatabaseClauseCursor, mapChoicePoint,
                      mapAttempt, mapReturnFrame, mapStepResult,
                      databaseClauseSelectStep,
                      replacementDatabaseClauseChoices, hCandidates,
                      hMaterialize, hAction]
              | inspect referenceRoot referenceConstant =>
                  cases hAllocate : copied.memory.allocate
                      (.const (referenceConstant candidate.reference)) with
                  | error error =>
                      cases hCleanup : memory.restore checkpoint <;>
                        simp [stepCore, stepCoreWithMeta, mapState, mapPhase,
                          mapControl, mapDatabaseClauseCursor, mapChoicePoint,
                          mapAttempt, mapReturnFrame, mapStepResult,
                          databaseClauseSelectStep, hCandidates, hMaterialize,
                          hAction, hAllocate, failWith, closeMemory, hCleanup]
                  | ok allocated =>
                      rcases allocated with ⟨copiedReference, allocatedMemory⟩
                      cases remaining <;>
                        simp [stepCore, stepCoreWithMeta, mapState, mapPhase,
                          mapControl, mapDatabaseClauseCursor, mapChoicePoint,
                          mapAttempt, mapReturnFrame, mapStepResult,
                          databaseClauseSelectStep,
                          replacementDatabaseClauseChoices, hCandidates,
                          hMaterialize, hAction, hAllocate]

/-- Demand-driven execution conserves the realization for every exact fuel
prefix.  In particular, open prefixes remain open and answers keep the same
memory and query-variable roots. -/
theorem pullCore_conserves [DecidableEq sigma.scoped.vars]
    [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols] [DecidableEq sigma.relationSymbols]
    {sourceMaterializer : ClauseMaterializer sigma Instruction₁ SourceClause₁}
    {targetMaterializer : ClauseMaterializer sigma Instruction₂ SourceClause₂}
    {sourceClassify : Instruction₁ →
      DispatchAction sigma Instruction₁ SourceClause₁}
    {targetClassify : Instruction₂ →
      DispatchAction sigma Instruction₂ SourceClause₂}
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
      rw [pullCore_succ, pullCore_succ]
      rw [stepCore_conserves realizes state]
      cases hStep : stepCore sourceMaterializer sourceClassify state with
      | terminal result => rfl
      | databaseRequest request next =>
          cases hRestore : next.memory.restore next.queryCheckpoint <;>
            simp [mapStepResult, mapPullResult, mapState, failPullWith,
              closeMemory, hRestore]
      | next next observation =>
          cases observation with
          | none => exact inductionHypothesis next
          | some observation => cases observation; rfl

end Conservation
end Mettapedia.Logic.LP.RuntimeQuery
