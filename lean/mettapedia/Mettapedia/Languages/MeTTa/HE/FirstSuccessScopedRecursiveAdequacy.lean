import Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy

/-!
# Earned Recursive Adequacy for the Checked Scoped HE Worker

This module builds the configuration-sensitive recursive realization on the
local squares and stack-polymorphic block algebra in `FirstSuccessScopedAdequacy`.
It records the concrete saved stacks and publication prefixes that determine
scoped type freshening, while leaving the contextual source semantics and the
generic equation spine unchanged.

The plain-Atom first-success worker is a restricted realization profile: its
admission requires closed type annotations and excludes held-readiness reuse
and embedded minimal instructions. These are worker boundaries, not limits on
the contextual HE semantics or on HO MeTTa Prime.
-/

open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Machines.OrderedProtocol.Completion
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open RecursiveTasks
open FirstSuccessRecursiveStrategy
open FirstSuccessRecursiveExecution
open FirstSuccessSourceExecution
open FirstSuccessSourceApplicability
open ScopedPolymorphicCompletion
open Spec.Eval
open Spec.Eval.Completed
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation
open Spec.Match.Merge
open ScopedRetainedRelation
open UniversalScopedCastAndHeadBoundary

set_option autoImplicit false

namespace UniversalScopedPolymorphicApplication

/-! ### Stack-indexed earned ordinary-equation recursion

`ScopedOpenEquationWorksSpine` remains the stack-polymorphic algebra used by
raw invocation and minimal `eval`.  Recursive schematic type lookup instead
depends on the actual saved stack and emitted prefix.  The structures below
record that concrete boundary without changing either source semantics or the
generic spine. -/

/-- One earned task execution at its actual caller stack and publication
prefix.  This is the common output interface of the recursive D2 induction;
constructors of that induction provide it rather than taking machine runs as
admission premises. -/
structure ScopedTaskRun
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wTask : RecursiveTasks.Task) (cTask : RecursiveTasks.Contextual.Task)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (steps : Nat) (wResults : ResultSet)
    (cResults : List Completed.Result) : Prop where
  positive : steps > 0
  results_rel : List.Forall₂ ScopedResultRel wResults cResults
  worker_run : ∀ budget,
    (Checked.machine dispatch scopedTypes).run (steps + budget)
      ⟨space, .work wTask, wStack, wEmitted⟩ =
    (Checked.machine dispatch scopedTypes).run budget
      ⟨space, .returning wResults, wStack, wEmitted⟩
  contextual_steps :
    RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
      (.work cTask, cStack) (.returning cResults, cStack)

/-- Observer-generalized task completion.  The executions remain exact; only
the endpoint occurrence lists are compared up to the public bag observer. -/
structure ScopedBagTaskRun
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wTask : RecursiveTasks.Task) (cTask : RecursiveTasks.Contextual.Task)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (steps : Nat) (wResults : ResultSet)
    (cResults : List Completed.Result) : Prop where
  positive : steps > 0
  results_rel : ScopedEmittedBagRel wResults cResults
  worker_run : ∀ budget,
    (Checked.machine dispatch scopedTypes).run (steps + budget)
      ⟨space, .work wTask, wStack, wEmitted⟩ =
    (Checked.machine dispatch scopedTypes).run budget
      ⟨space, .returning wResults, wStack, wEmitted⟩
  contextual_steps :
    RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
      (.work cTask, cStack) (.returning cResults, cStack)

/-- Exact task completion embeds into bag-observed task completion. -/
theorem ScopedTaskRun.to_bag
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wTask : RecursiveTasks.Task} {cTask : RecursiveTasks.Contextual.Task}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {steps : Nat} {wResults : ResultSet} {cResults : List Completed.Result}
    (run : ScopedTaskRun space dispatch hostDispatch policy wTask cTask
      wStack cStack wEmitted cEmitted steps wResults cResults) :
    ScopedBagTaskRun space dispatch hostDispatch policy wTask cTask
      wStack cStack wEmitted cEmitted steps wResults cResults :=
  ⟨run.positive, ScopedEmittedBagRel.of_forall2 run.results_rel,
    run.worker_run, run.contextual_steps⟩

/-- Empty/error entry earns a concrete one-step task run. -/
theorem ScopedTaskRun.atomEmptyOrError
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (value expected : Atom) (wB : Bindings) (depth : Nat)
    (wLive cLive : List Atom) (scope : List String)
    (ctxVal : Entry.Value) (cFrame : Completed.Frame)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (entryReady : ScopedAtomEntryReady policy value ctxVal cFrame)
    (stopped : isEmptyOrError value = true)
    (actRel : ScopedActivationRel wB cFrame) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom value expected wB (depth + 1) wLive)
      (.atom cLive scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted 1
      [(value, wB)] [(cFrame.read policy ctxVal, cFrame)] := by
  have wStep : (Checked.machine dispatch scopedTypes).step
      ⟨space,.work (.atom value expected wB (depth + 1) wLive),wStack,wEmitted⟩ =
      some (.silent ⟨space,.returning [(value,wB)],wStack,wEmitted⟩) := by
    simp [Checked.machine,RecursiveMachine.Checked.guardMachine,Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady,RecursiveMachine.Checked.taskReady,
      FirstSuccessRecursiveExecution.machine,FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter,RecursiveMachine.enter,stopped,Transition.relabel]
  have cStopped : IsEmptyOrErrorRel (cFrame.read policy ctxVal).erase := by
    rw [entryReady.2.1,Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
    exact stopped
  have entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      (cFrame.read policy ctxVal).erase expected .deliver := .stopped cStopped
  have cStep : RecursiveMachine.Contextual.LocalStep space hostDispatch
      Completed.scopedLookup policy
      (.work (.atom cLive scope ctxVal expected cFrame),cStack)
      (.returning [(cFrame.read policy ctxVal,cFrame)],cStack) := .delivered entered
  refine ⟨by omega,.cons ⟨entryReady.2.1.symm,actRel⟩ .nil,?_,.single cStep⟩
  intro budget
  rw [Nat.add_comm 1 budget,
    (Checked.machine dispatch scopedTypes).run_succ_silent wStep]

/-- Ordinary type delivery earns a concrete one-step task run. -/
theorem ScopedTaskRun.atomTypePass
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (value expected : Atom) (wB : Bindings) (depth : Nat)
    (wLive cLive : List Atom) (scope : List String)
    (ctxVal : Entry.Value) (cFrame : Completed.Frame)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (entryReady : ScopedAtomEntryReady policy value ctxVal cFrame)
    (notStopped : isEmptyOrError value = false)
    (typePass : expected = Atom.atomType ∨ expected = getMetaType value ∨
      getMetaType value = Atom.variableType)
    (actRel : ScopedActivationRel wB cFrame) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom value expected wB (depth + 1) wLive)
      (.atom cLive scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted 1
      [(value, wB)] [(cFrame.read policy ctxVal, cFrame)] := by
  have hPass :
      (expected = Atom.atomType ∨ expected = getMetaType value) ∨
        getMetaType value = Atom.variableType := by
    rcases typePass with h1 | h2 | h3
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h2)
    · exact Or.inr h3
  have wStep : (Checked.machine dispatch scopedTypes).step
      ⟨space,.work (.atom value expected wB (depth + 1) wLive),wStack,wEmitted⟩ =
      some (.silent ⟨space,.returning [(value,wB)],wStack,wEmitted⟩) := by
    simp [Checked.machine,RecursiveMachine.Checked.guardMachine,Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady,RecursiveMachine.Checked.taskReady,
      FirstSuccessRecursiveExecution.machine,FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter,RecursiveMachine.enter,
      notStopped,hPass,Transition.relabel]
  have cNotStopped : ¬IsEmptyOrErrorRel (cFrame.read policy ctxVal).erase := by
    rw [entryReady.2.1,Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
    simp [notStopped]
  have cMeta : MetaTypeRel (cFrame.read policy ctxVal).erase (getMetaType value) := by
    rw [entryReady.2.1,Conformance.metaTypeRel_iff_getMetaType]
  have entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      (cFrame.read policy ctxVal).erase expected .deliver :=
    .pass cNotStopped cMeta typePass
  have cStep : RecursiveMachine.Contextual.LocalStep space hostDispatch
      Completed.scopedLookup policy
      (.work (.atom cLive scope ctxVal expected cFrame),cStack)
      (.returning [(cFrame.read policy ctxVal,cFrame)],cStack) := .delivered entered
  refine ⟨by omega,.cons ⟨entryReady.2.1.symm,actRel⟩ .nil,?_,.single cStep⟩
  intro budget
  rw [Nat.add_comm 1 budget,
    (Checked.machine dispatch scopedTypes).run_succ_silent wStep]

/-- Structural admission for one complete atom-cast batch at the exact worker
configuration whose retained stack and emitted prefix determine scoped type
freshening.  The record contains the worker's finite cast calculation, the
independent contextual cast relations, and only the representation relation
between their result occurrences; it contains no machine execution. -/
structure ScopedCastAdmission
    (space : Space) (policy : Policy)
    (value expected : Atom) (ctxVal : Entry.Value)
    (wB : Bindings) (cFrame : Completed.Frame)
    (depth : Nat) (wLive cLive : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet)
    (wResults rawResults : ResultSet)
    (cResults : List Completed.Result) : Prop where
  entry_ready : ScopedAtomEntryReady policy value ctxVal cFrame
  entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
    (cFrame.read policy ctxVal).erase expected .cast
  worker_covered :
    typeCastCovered value expected space wB depth
      (invocationTypes
        ⟨space, .work (.atom value expected wB (depth + 1) wLive), wStack, wEmitted⟩) = true
  worker_result :
    typeCast value expected space wB depth
      (invocationTypes
        ⟨space, .work (.atom value expected wB (depth + 1) wLive), wStack, wEmitted⟩) =
      wResults
  source_batch :
    TypeCastBatchRel space (cFrame.read policy ctxVal).erase expected cFrame.bindings
      rawResults
      (lookup := Completed.scopedLookup
        (invocationTypeScope scope cLive (cFrame.read policy ctxVal).erase
          expected cFrame.bindings) space)
      (matching := policy.matching.Rel)
  cast_results : List.Forall₂
    (Completed.CastResultRel policy
      (Completed.scopedLookup
        (invocationTypeScope scope cLive (cFrame.read policy ctxVal).erase
          expected cFrame.bindings) space)
      cFrame (cFrame.read policy ctxVal) expected)
    rawResults cResults
  results_rel : List.Forall₂ ScopedResultRel wResults cResults
  input_activation : ScopedActivationRel wB cFrame

/-- An exact declared type that preserves the reached frame gives the common
singleton cast admission.  This is the reusable monomorphic operator/argument
case; schematic renewals use the general record above. -/
theorem ScopedCastAdmission.unchanged
    (space : Space) (policy : Policy)
    (value expected : Atom) (ctxVal : Entry.Value)
    (wB : Bindings) (cFrame : Completed.Frame)
    (depth : Nat) (wLive cLive : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet)
    (entryReady : ScopedAtomEntryReady policy value ctxVal cFrame)
    (entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      (cFrame.read policy ctxVal).erase expected .cast)
    (workerCovered :
      typeCastCovered value expected space wB depth
        (invocationTypes
          ⟨space, .work (.atom value expected wB (depth + 1) wLive), wStack, wEmitted⟩) = true)
    (workerResult :
      typeCast value expected space wB depth
        (invocationTypes
          ⟨space, .work (.atom value expected wB (depth + 1) wLive), wStack, wEmitted⟩) =
        [(value, wB)])
    (sourceQuery : Completed.scopedLookup
      (invocationTypeScope scope cLive (cFrame.read policy ctxVal).erase
        expected cFrame.bindings)
      space cFrame.bindings (cFrame.read policy ctxVal).erase expected [expected])
    (matched : policy.matching.Rel expected expected cFrame.bindings cFrame.bindings)
    (actRel : ScopedActivationRel wB cFrame) :
    ScopedCastAdmission space policy value expected ctxVal wB cFrame
      depth wLive cLive scope wStack wEmitted
      [(value, wB)]
      [((cFrame.read policy ctxVal).erase, cFrame.bindings)]
      [(cFrame.read policy ctxVal, cFrame)] := by
  refine ⟨entryReady, entered, workerCovered, workerResult, ?_, ?_, ?_, actRel⟩
  · exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
      sourceQuery rfl (by simp) matched
  · exact .cons ⟨rfl, .same _, by simp⟩ .nil
  · exact .cons ⟨entryReady.2.1.symm, actRel⟩ .nil

/-- A structurally admitted complete cast batch earns one checked-worker step
and the corresponding contextual cast step. -/
theorem ScopedTaskRun.atomCast
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (value expected : Atom) (ctxVal : Entry.Value)
    (wB : Bindings) (cFrame : Completed.Frame)
    (depth : Nat) (wLive cLive : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (wResults rawResults : ResultSet)
    (cResults : List Completed.Result)
    (admission : ScopedCastAdmission space policy value expected ctxVal wB cFrame
      depth wLive cLive scope wStack wEmitted wResults rawResults cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom value expected wB (depth + 1) wLive)
      (.atom cLive scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted 1
      wResults cResults := by
  let wState : Configuration :=
    ⟨space, .work (.atom value expected wB (depth + 1) wLive), wStack, wEmitted⟩
  have workerEntered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      value expected .cast := by
    simpa only [admission.entry_ready.2.1] using admission.entered
  have wStep := worker_cast_step wState dispatch scopedTypes value expected wB depth
    wLive policy.reentry (cFrame.read policy ctxVal).status rfl workerEntered
    admission.worker_covered
  have workerResultAt :
      typeCast value expected wState.space wB depth (scopedTypes.types wState) =
        wResults := by
    simpa only [wState, scopedTypes] using admission.worker_result
  rw [workerResultAt] at wStep
  have cStep : RecursiveMachine.Contextual.LocalStep space hostDispatch
      Completed.scopedLookup policy
      (.work (.atom cLive scope ctxVal expected cFrame), cStack)
      (.returning cResults, cStack) :=
    .cast admission.entered admission.source_batch admission.cast_results
  refine ⟨by omega, admission.results_rel, ?_, .single cStep⟩
  intro budget
  rw [Nat.add_comm 1 budget,
    (Checked.machine dispatch scopedTypes).run_succ_silent wStep]

/-- Structural admission for an exhausted complete function-type scan.  The
boolean index distinguishes tuple-eligible exhaustion from terminal selection
failure; both profiles share the same lookup, entry, and diagnostic laws.  The
record contains no machine transition. -/
structure ScopedExhaustedSelectionAdmission
    (space : Space) (policy : Policy)
    (operator : Atom) (arguments : List Atom) (expected : Atom)
    (wB : Bindings) (fuel : Nat) (live : List Atom) (scope : List String)
    (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
    (cFrame : Completed.Frame) (readiness : Entry.Status)
    (candidates errors : List Atom) (tupleEligible : Bool)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet) : Prop where
  entry_ready : ScopedAtomEntryReady policy
    (.expression (operator :: arguments)) ctxVal cFrame
  read_shape : cFrame.read policy ctxVal =
    .expression readiness (ctxOp :: ctxArgs)
  operator_erase : ctxOp.erase = operator
  arguments_erase : ctxArgs.map Entry.Value.erase = arguments
  input_not_stopped : isEmptyOrError (.expression (operator :: arguments)) = false
  expected_not_atom : expected ≠ Atom.atomType
  expected_not_expression : expected ≠ Atom.expressionType
  candidate_eq :
    invocationTypes
      ⟨space,
        .work (.expression (.expression (operator :: arguments)) expected wB
          (fuel + 1) live),
        .filter :: wStack, wEmitted⟩
      wB operator expected = candidates
  selection_ready :
    FirstSuccessRecursiveStrategy.selectionReady
      (lookup := invocationTypes
        ⟨space, .work (.functions (.expression (operator :: arguments)) expected wB
          fuel candidates live), .filter :: wStack, wEmitted⟩)
      space (.expression (operator :: arguments)) expected wB fuel candidates = true
  worker_exhausted :
    FirstSuccessRecursiveStrategy.select
      (lookup := invocationTypes
        ⟨space, .work (.functions (.expression (operator :: arguments)) expected wB
          fuel candidates live), .filter :: wStack, wEmitted⟩)
      space (.expression (operator :: arguments)) expected wB fuel candidates =
        .exhausted errors tupleEligible
  contextual_exhausted :
    Completed.InvocationSelectionRel space Completed.scopedLookup policy live scope
      (.expression (operator :: arguments)) operator expected cFrame
      (.exhausted errors tupleEligible)
  input_activation : ScopedActivationRel wB cFrame
  diagnostics_rel : List.Forall₂ ScopedResultRel
    (errors.map fun error => (error, wB))
    ((Completed.diagnosticResults errors cFrame).map (Completed.readResult policy))

/-- Terminal selection failure is exhausted selection with tuple fallback
disabled. -/
abbrev ScopedSelectionFailureAdmission
    (space : Space) (policy : Policy)
    (operator : Atom) (arguments : List Atom) (expected : Atom)
    (wB : Bindings) (fuel : Nat) (live : List Atom) (scope : List String)
    (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
    (cFrame : Completed.Frame) (readiness : Entry.Status)
    (candidates errors : List Atom)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet) : Prop :=
  ScopedExhaustedSelectionAdmission space policy operator arguments expected
    wB fuel live scope ctxVal ctxOp ctxArgs cFrame readiness candidates errors
    false wStack wEmitted

/-- Tuple fallback is exhausted selection with tuple eligibility enabled. -/
abbrev ScopedTupleFallbackAdmission
    (space : Space) (policy : Policy)
    (operator : Atom) (arguments : List Atom) (expected : Atom)
    (wB : Bindings) (fuel : Nat) (live : List Atom) (scope : List String)
    (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
    (cFrame : Completed.Frame) (readiness : Entry.Status)
    (candidates errors : List Atom)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet) : Prop :=
  ScopedExhaustedSelectionAdmission space policy operator arguments expected
    wB fuel live scope ctxVal ctxOp ctxArgs cFrame readiness candidates errors
    true wStack wEmitted

/-- A complete nonempty list of non-function declarations constructs the
tuple-fallback admission directly.  This factors the structural half of the
older local square away from its machine steps. -/
theorem ScopedTupleFallbackAdmission.of_nonfunctions
    (space : Space) (policy : Policy)
    (operator : Atom) (arguments : List Atom) (expected : Atom)
    (wB : Bindings) (fuel : Nat) (live : List Atom) (scope : List String)
    (ctxVal : Entry.Value) (cFrame : Completed.Frame)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet)
    (entryReady : ScopedAtomEntryReady policy
      (.expression (operator :: arguments)) ctxVal cFrame)
    (notStopped : isEmptyOrError (.expression (operator :: arguments)) = false)
    (notAtom : expected ≠ Atom.atomType)
    (notExpr : expected ≠ Atom.expressionType)
    (nonemptyRaw : getAtomTypes space operator ≠ [])
    (nonfunctions : ∀ candidate ∈ getAtomTypes space operator,
      isFunctionType candidate = false)
    (actRel : ScopedActivationRel wB cFrame)
    (retained : ∀ name ∈ scope,
      name ∈ RecursiveScope.configurationNames
        ⟨space,
          .work (.atom (.expression (operator :: arguments)) expected wB
            (fuel + 2) live),
          wStack, wEmitted⟩) :
    let expr := Atom.expression (operator :: arguments)
    let w0 : Configuration :=
      ⟨space, .work (.atom expr expected wB (fuel + 2) live), wStack, wEmitted⟩
    let candidates := invocationTypes w0 wB operator expected
    ∃ readiness ctxOp ctxArgs,
      ScopedTupleFallbackAdmission space policy operator arguments expected
        wB fuel live scope ctxVal ctxOp ctxArgs cFrame readiness candidates []
        wStack wEmitted := by
  intro expr w0 candidates
  obtain ⟨readiness, ctxOp, ctxArgs, readShape, operatorErase, argumentsErase⟩ :=
    erase_eq_expression_cons entryReady.2.1
  have queried : Completed.scopedLookup
      (invocationTypeScope scope live expr expected cFrame.bindings)
      space cFrame.bindings operator Atom.undefinedType candidates :=
    scopedLookup_of_expression_invocationTypes_related space operator arguments expected
      wB cFrame (fuel + 2) live scope wStack wEmitted actRel retained
  have queriedForSelection := queried
  obtain ⟨raw, rawTypes, variants⟩ := queried
  have rawEq : raw = getAtomTypes space operator :=
    rawTypes.unique (FirstSuccessSourceReplies.source_types space operator)
  subst rawEq
  obtain ⟨isEmptyEq, candidateNonfunctions⟩ :=
    ArgumentAlphaVariantsRel.nonfunctions variants nonfunctions
  have candidatesNonempty : (!candidates.isEmpty) = true := by
    rw [isEmptyEq]
    simp [List.isEmpty_eq_false_iff.mpr nonemptyRaw]
  have scanned : Completed.InvocationScanRel space
      (Completed.scopedLookup
        (invocationTypeScope scope live expr expected cFrame.bindings) space)
      policy expr expected cFrame candidates (.exhausted [] true) := by
    rw [← candidatesNonempty]
    exact invocationScanRel_of_nonfunctions space _ policy expr expected cFrame
      candidates candidateNonfunctions
  have contextual : Completed.InvocationSelectionRel space Completed.scopedLookup
      policy live scope expr operator expected cFrame (.exhausted [] true) :=
    ⟨candidates, queriedForSelection, scanned⟩
  let w1 : Configuration :=
    ⟨space, .work (.expression expr expected wB (fuel + 1) live),
      .filter :: wStack, wEmitted⟩
  let w2 : Configuration :=
    ⟨space, .work (.functions expr expected wB fuel candidates live),
      .filter :: wStack, wEmitted⟩
  have ready : FirstSuccessRecursiveStrategy.selectionReady
      (lookup := invocationTypes w2) space expr expected wB fuel candidates = true :=
    selectionReady_of_nonfunctions space (invocationTypes w2) expr expected
      wB fuel candidates candidateNonfunctions
  have exhausted : FirstSuccessRecursiveStrategy.select
      (lookup := invocationTypes w2) space expr expected wB fuel candidates =
        .exhausted [] true := by
    rw [select_of_nonfunctions space (invocationTypes w2) expr expected
      wB fuel candidates candidateNonfunctions, candidatesNonempty]
  refine ⟨readiness, ctxOp, ctxArgs,
    { entry_ready := entryReady
      read_shape := readShape
      operator_erase := operatorErase
      arguments_erase := argumentsErase
      input_not_stopped := notStopped
      expected_not_atom := notAtom
      expected_not_expression := notExpr
      candidate_eq := ?_
      selection_ready := ready
      worker_exhausted := exhausted
      contextual_exhausted := contextual
      input_activation := actRel
      diagnostics_rel := .nil }⟩
  rfl

/-- A complete failed selection runs in three dispatch steps plus one
publication-priority step.  Contextual execution is reconstructed from the
independent `AtomRel.selectionFailed` judgment at the actual caller stack. -/
theorem ScopedTaskRun.atomSelectionFailed
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator : Atom) (arguments : List Atom) (expected : Atom)
    (wB : Bindings) (fuel : Nat) (live : List Atom) (scope : List String)
    (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
    (cFrame : Completed.Frame) (readiness : Entry.Status)
    (candidates errors : List Atom)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (admission : ScopedSelectionFailureAdmission space policy operator arguments expected
      wB fuel live scope ctxVal ctxOp ctxArgs cFrame readiness candidates errors
      wStack wEmitted) :
    let expr := Atom.expression (operator :: arguments)
    let wDiag : ResultSet := errors.map fun error => (error, wB)
    let cDiag := (Completed.diagnosticResults errors cFrame).map
      (Completed.readResult policy)
    let cSelected := completedSuccessPriority cDiag
    let cPublished := cSelected.map (Completed.publishResult policy expr)
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom expr expected wB (fuel + 2) live)
      (.atom live scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted 4
      (successPriority wDiag) cPublished := by
  intro expr wDiag cDiag cSelected cPublished
  let w0 : Configuration :=
    ⟨space, .work (.atom expr expected wB (fuel + 2) live), wStack, wEmitted⟩
  let w1 : Configuration :=
    ⟨space, .work (.expression expr expected wB (fuel + 1) live),
      .filter :: wStack, wEmitted⟩
  let w2 : Configuration :=
    ⟨space, .work (.functions expr expected wB fuel candidates live),
      .filter :: wStack, wEmitted⟩
  let w3 : Configuration :=
    ⟨space, .returning wDiag, .filter :: wStack, wEmitted⟩
  let w4 : Configuration :=
    ⟨space, .returning (successPriority wDiag), wStack, wEmitted⟩
  have notVarT : Atom.expressionType ≠ Atom.variableType := by decide
  have notSymT : Atom.expressionType ≠ Atom.symbolType := by decide
  have notGrdT : Atom.expressionType ≠ Atom.groundedType := by decide
  have notUnit : expr ≠ Atom.unit := by simp [expr, Atom.unit]
  have step0 : (Checked.machine dispatch scopedTypes).step w0 = some (.silent w1) := by
    simp [w0, w1, expr, Checked.machine, RecursiveMachine.Checked.guardMachine,
      Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
      RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
      RecursiveMachine.enter, getMetaType, admission.input_not_stopped,
      admission.expected_not_atom, admission.expected_not_expression,
      notVarT, notSymT, notGrdT, notUnit, Transition.relabel]
  have step1 : (Checked.machine dispatch scopedTypes).step w1 = some (.silent w2) := by
    simp [w1, w2, expr, Checked.machine, RecursiveMachine.Checked.guardMachine,
      Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
      RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
      scopedTypes, admission.candidate_eq, Transition.relabel]
  have step2 : (Checked.machine dispatch scopedTypes).step w2 = some (.silent w3) := by
    simp [w2, w3, wDiag, expr, Checked.machine,
      RecursiveMachine.Checked.guardMachine, Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady, scopedTypes,
      admission.selection_ready, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
      admission.worker_exhausted, Transition.relabel]
  have step3 : (Checked.machine dispatch scopedTypes).step w3 = some (.silent w4) := by
    simp [w3, w4, Checked.machine, RecursiveMachine.Checked.guardMachine,
      Checked.blocked, RecursiveMachine.Checked.frameReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      RecursiveMachine.resume, Transition.relabel]
  have workerRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run (4 + budget) w0 =
        (Checked.machine dispatch scopedTypes).run budget w4 := by
    intro budget
    rw [show 4 + budget = (((budget + 1) + 1) + 1) + 1 by omega,
      (Checked.machine dispatch scopedTypes).run_succ_silent step0,
      (Checked.machine dispatch scopedTypes).run_succ_silent step1,
      (Checked.machine dispatch scopedTypes).run_succ_silent step2,
      (Checked.machine dispatch scopedTypes).run_succ_silent step3]
  have entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      (cFrame.read policy ctxVal).erase expected .interpret :=
    admission.entry_ready.entry_interpret admission.input_not_stopped
      admission.expected_not_atom admission.expected_not_expression
  have selectedAtRead : Completed.InvocationSelectionRel space Completed.scopedLookup
      policy live scope (cFrame.read policy ctxVal).erase ctxOp.erase expected cFrame
      (.exhausted errors false) := by
    simpa only [admission.entry_ready.2.1, admission.operator_erase] using
      admission.contextual_exhausted
  have source : Completed.AtomRel space hostDispatch Completed.scopedLookup live scope
      ctxVal expected cFrame cPublished (policy := policy) := by
    simpa only [admission.entry_ready.2.1] using
      (Completed.AtomRel.selectionFailed entered admission.read_shape selectedAtRead
        (completedSuccessPriority_rel cDiag))
  have resultsRel : List.Forall₂ ScopedResultRel
      (successPriority wDiag) cPublished :=
    ScopedResultRel.forall2_publishResult policy expr
      (ScopedResultRel.forall2_successPriority admission.diagnostics_rel)
  exact ⟨by omega, resultsRel, workerRun,
    RecursiveExecution.Contextual.atom_complete source cStack⟩

/-- Structural agreement for a selected function entry at the exact worker
configuration whose scoped lookup performs freshening.  Both sides retain their
own selection judgment; this record contains no execution trace. -/
structure ScopedSelectedFunctionEntry
    (space : Space) (policy : Policy)
    (operator : Atom) (arguments : List Atom) (opVal expected : Atom)
    (wB wBSelected : Bindings) (fuel : Nat)
    (live : List Atom) (scope : List String)
    (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
    (cFrame cFrameSelected : Completed.Frame)
    (readiness : Entry.Status)
    (signature : SelectedTypePolicy) (candidates : List Atom)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet) : Prop where
  entry_ready : ScopedAtomEntryReady policy
    (.expression (operator :: arguments)) ctxVal cFrame
  read_shape : cFrame.read policy ctxVal =
    .expression readiness (ctxOp :: ctxArgs)
  operator_erase : ctxOp.erase = operator
  arguments_erase : ctxArgs.map Entry.Value.erase = arguments
  input_not_stopped : isEmptyOrError (.expression (operator :: arguments)) = false
  expected_not_atom : expected ≠ Atom.atomType
  expected_not_expression : expected ≠ Atom.expressionType
  candidate_eq :
    invocationTypes
      ⟨space,
        .work (.expression (.expression (operator :: arguments)) expected wB
          (fuel + 3) live),
        .filter :: wStack, wEmitted⟩
      wB operator expected = candidates
  selection_ready :
    FirstSuccessRecursiveStrategy.selectionReady
      (lookup := invocationTypes
        ⟨space, .work (.functions (.expression (operator :: arguments)) expected wB
          (fuel + 2) candidates live), .filter :: wStack, wEmitted⟩)
      space (.expression (operator :: arguments)) expected wB (fuel + 2) candidates = true
  worker_selected :
    FirstSuccessRecursiveStrategy.select
      (lookup := invocationTypes
        ⟨space, .work (.functions (.expression (operator :: arguments)) expected wB
          (fuel + 2) candidates live), .filter :: wStack, wEmitted⟩)
      space (.expression (operator :: arguments)) expected wB (fuel + 2) candidates =
        .selected signature [wBSelected]
  contextual_selected :
    Completed.InvocationSelectionRel space Completed.scopedLookup policy live scope
      (.expression (operator :: arguments)) operator expected cFrame
      (.selected signature [cFrameSelected])
  input_activation : ScopedActivationRel wB cFrame
  selected_activation : ScopedActivationRel wBSelected cFrameSelected
  arity_eq : ctxArgs.length = signature.argumentTypes.length
  argument_types_eq :
    getFunctionArgTypes signature.functionType = some signature.argumentTypes
  operator_not_stopped : isEmptyOrError opVal = false

/-- A successful type-selection result advances an expression atom to the same
invocation state in both machines.  The premise compares the two selection
judgments themselves; no evaluator execution is assumed.  Keeping the actual
worker configurations explicit is essential because `scopedTypes` freshens
against their saved stacks and emitted prefixes. -/
theorem scoped_selected_function_entry_run
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator : Atom) (arguments : List Atom) (expected : Atom)
    (wB wBSelected : Bindings) (fuel : Nat)
    (live : List Atom) (scope : List String)
    (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
    (cFrame cFrameSelected : Completed.Frame)
    (readiness : Entry.Status)
    (signature : SelectedTypePolicy) (candidates : List Atom)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (entryReady : ScopedAtomEntryReady policy
      (.expression (operator :: arguments)) ctxVal cFrame)
    (readShape : cFrame.read policy ctxVal = .expression readiness (ctxOp :: ctxArgs))
    (opEq : ctxOp.erase = operator)
    (notStopped : isEmptyOrError (.expression (operator :: arguments)) = false)
    (notAtom : expected ≠ Atom.atomType)
    (notExpr : expected ≠ Atom.expressionType)
    (candidateEq :
      invocationTypes
        ⟨space,
          .work (.expression (.expression (operator :: arguments)) expected wB
            (fuel + 1) live),
          .filter :: wStack, wEmitted⟩
        wB operator expected = candidates)
    (selectionReady :
      FirstSuccessRecursiveStrategy.selectionReady
        (lookup := invocationTypes
          ⟨space, .work (.functions (.expression (operator :: arguments)) expected wB
            fuel candidates live), .filter :: wStack, wEmitted⟩)
        space (.expression (operator :: arguments)) expected wB fuel candidates = true)
    (selected :
      FirstSuccessRecursiveStrategy.select
        (lookup := invocationTypes
          ⟨space, .work (.functions (.expression (operator :: arguments)) expected wB
            fuel candidates live), .filter :: wStack, wEmitted⟩)
        space (.expression (operator :: arguments)) expected wB fuel candidates =
          .selected signature [wBSelected])
    (contextualSelected :
      Completed.InvocationSelectionRel space Completed.scopedLookup policy live scope
        (.expression (operator :: arguments)) operator expected cFrame
        (.selected signature [cFrameSelected]))
    :
    let expr := Atom.expression (operator :: arguments)
    let resultType := Completed.invocationReturnType signature
    let wBefore : Configuration :=
      ⟨space, .work (.atom expr expected wB (fuel + 2) live), wStack, wEmitted⟩
    let wAfter : Configuration :=
      ⟨space, .work (.bindingAlternatives expr signature.functionType resultType fuel
        [wBSelected] live), .filter :: wStack, wEmitted⟩
    let cBefore : RecursiveTasks.Contextual.Configuration :=
      ⟨space, .work (.atom live scope ctxVal expected cFrame), cStack, cEmitted⟩
    let cAfter : RecursiveTasks.Contextual.Configuration :=
      ⟨space, .work (.invocations live scope expected signature ctxOp ctxArgs
        [cFrameSelected]), .publish expr :: cStack, cEmitted⟩
    (Checked.machine dispatch scopedTypes).run 3 wBefore = ([], .exhausted wAfter) ∧
    (∀ budget,
      (Checked.machine dispatch scopedTypes).run (3 + budget) wBefore =
        (Checked.machine dispatch scopedTypes).run budget wAfter) ∧
    RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
      (cBefore.control, cBefore.stack) (cAfter.control, cAfter.stack) := by
  intro expr resultType wBefore wAfter cBefore cAfter
  let wExpression : Configuration :=
    ⟨space, .work (.expression expr expected wB (fuel + 1) live),
      .filter :: wStack, wEmitted⟩
  let wFunctions : Configuration :=
    ⟨space, .work (.functions expr expected wB fuel candidates live),
      .filter :: wStack, wEmitted⟩
  have notVarT : Atom.expressionType ≠ Atom.variableType := by decide
  have notSymT : Atom.expressionType ≠ Atom.symbolType := by decide
  have notGrdT : Atom.expressionType ≠ Atom.groundedType := by decide
  have notUnit : expr ≠ Atom.unit := by simp [expr, Atom.unit]
  have step0 : (Checked.machine dispatch scopedTypes).step wBefore =
      some (.silent wExpression) := by
    simp [wBefore, wExpression, expr, Checked.machine,
      RecursiveMachine.Checked.guardMachine, Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, getMetaType,
      notStopped, notAtom, notExpr, notVarT, notSymT, notGrdT, notUnit,
      Transition.relabel]
  have step1 : (Checked.machine dispatch scopedTypes).step wExpression =
      some (.silent wFunctions) := by
    simp [wExpression, wFunctions, expr, Checked.machine,
      RecursiveMachine.Checked.guardMachine, Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter, scopedTypes, candidateEq, Transition.relabel]
  have step2 : (Checked.machine dispatch scopedTypes).step wFunctions =
      some (.silent wAfter) := by
    simp [wFunctions, wAfter, expr, resultType, Checked.machine,
      RecursiveMachine.Checked.guardMachine, Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady, scopedTypes, selectionReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter, selected, Completed.invocationReturnType,
      Transition.relabel]
  have runPrefix : ∀ budget,
      (Checked.machine dispatch scopedTypes).run (3 + budget) wBefore =
        (Checked.machine dispatch scopedTypes).run budget wAfter := by
    intro budget
    rw [show 3 + budget = ((budget + 1) + 1) + 1 by omega,
      (Checked.machine dispatch scopedTypes).run_succ_silent step0,
      (Checked.machine dispatch scopedTypes).run_succ_silent step1,
      (Checked.machine dispatch scopedTypes).run_succ_silent step2]
  have hEntry :
      Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
        (cFrame.read policy ctxVal).erase expected .interpret :=
    entryReady.entry_interpret notStopped notAtom notExpr
  have hSelectedRead :
      Completed.InvocationSelectionRel space Completed.scopedLookup policy live scope
        (cFrame.read policy ctxVal).erase ctxOp.erase expected cFrame
        (.selected signature [cFrameSelected]) := by
    rwa [entryReady.2.1, opEq]
  have cStep :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (cBefore.control, cBefore.stack) (cAfter.control, cAfter.stack) := by
    simpa only [cBefore, cAfter, entryReady.2.1] using
      (RecursiveMachine.Contextual.LocalStep.atomFunction
        hEntry readShape hSelectedRead)
  exact ⟨(runPrefix 0).trans rfl, runPrefix, cStep⟩

/-- Structural admission for the ordinary equation-call portion of a selected
function.  Query coverage, the contextual frontier, and publication
materialization are recorded here so recursive task realization itself has no
external side conditions. -/
structure ScopedEquationCallAdmission
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch)
    (expr expected : Atom) (wB : Bindings) (fuel : Nat)
    (live : List Atom) (ctxCall : Entry.Value) (cFrame : Completed.Frame)
    (rows : List (Atom × Bindings))
    (works : List Spec.Eval.Steps.EquationWork)
    (bodyResults finalResults : ResultSet) (readDepth : Nat) : Prop where
  value_erase : ctxCall.erase = expr
  not_error : isErrorAtom expr = false
  not_executable : ∀ op args,
    expr = .expression (op :: args) → dispatch.isExecutable op = false
  non_grounded : NonGroundedCallRel hostDispatch ctxCall.erase
  not_minimal : minimalInstruction expr = false
  query_covered :
    queryEquationsCovered (equationScope live expr expected wB)
      space expr (fuel + 1) = true
  query_eq :
    queryEquationsAvoiding (equationScope live expr expected wB)
      space expr (fuel + 1) = rows
  bodies_nonempty : bodyResults ≠ []
  frontier :
    Spec.Eval.Steps.EquationFrontierRel space (expected :: live)
      ctxCall.erase cFrame.bindings works
  works_nonempty : works ≠ []
  returned_covered : ∀ pair ∈ finalResults,
    pair.2.applyFullCovered pair.1 readDepth = true
  returned_stable : ∀ pair ∈ finalResults,
    pair.2.applyFull pair.1 readDepth = pair.1

/-- Concrete ordinary equation rows.  Passes one and two remain independent of
the caller stack.  Pass three and the contextual equation traversal carry the
actual return/equation stacks on which recursive schematic lookup depends. -/
inductive ScopedConcreteEquationWorksSpine
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (expr expected : Atom) (wBIn : Bindings) (depth : Nat)
    (live : List Atom) (scope : List String)
    (ctxCall : Entry.Value) (cFrameIn : Completed.Frame)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    Nat → Nat → Nat →
    List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation →
    List (Atom × Bindings) → List Spec.Eval.Steps.EquationWork →
    ResultSet → ResultSet → List Completed.Result →
    ResultSet → List Completed.Result → Prop where
  | nil (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation) :
      ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
        expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
        1 1 1 wRetStack cEqStack [] [] [] [] [] [] []
  | cons_rejected
      (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation)
      (rhs : Atom) (selected : Bindings)
      (remEqSteps remProdSteps remRetSteps : Nat)
      (remRows : List (Atom × Bindings))
      (works : List Spec.Eval.Steps.EquationWork)
      (bodyResults prodResults : ResultSet)
      (ctxProdResults : List Completed.Result)
      (finalResults : ResultSet)
      (ctxFinalResults : List Completed.Result)
      (eqReady :
        (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
          (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
            (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
      (mergeFilterEmpty :
        ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) = [])
      (tailSpine :
        ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
          expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
          remEqSteps remProdSteps remRetSteps wRetStack cEqStack
          remRows works bodyResults prodResults ctxProdResults
          finalResults ctxFinalResults) :
      ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
        expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
        (remEqSteps + 3) remProdSteps remRetSteps wRetStack cEqStack
        ((rhs, selected) :: remRows) works bodyResults prodResults ctxProdResults
        finalResults ctxFinalResults
  | cons_ordinary_notReducible
      (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation)
      (rhs : Atom) (selected wBMid : Bindings)
      (work : Spec.Eval.Steps.EquationWork) (ctxProdVal : Entry.Value)
      (cFrameMid : Completed.Frame)
      (remEqSteps remProdSteps remRetSteps : Nat)
      (remRows : List (Atom × Bindings))
      (remWorks : List Spec.Eval.Steps.EquationWork)
      (remBodyResults remProdResults : ResultSet)
      (remCtxProdResults : List Completed.Result)
      (remFinalResults : ResultSet)
      (remCtxFinalResults : List Completed.Result)
      (eqReady :
        (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
          (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
            (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
      (mergeFilterEq :
        ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
        [(Atom.notReducible, wBMid)])
      (outBindingsEq : cFrameMid.bindings = work.bindings)
      (unifyRel :
        Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
          (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
      (ctxProdEq : ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
      (bodyEraseEq : ctxProdVal.erase = Atom.notReducible)
      (callEq : ctxCall.erase = expr)
      (actMid : ScopedActivationRel wBMid cFrameMid)
      (tailSpine :
        ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
          expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
          remEqSteps remProdSteps remRetSteps
          (.prepend [(expr, wBMid)] :: wRetStack)
          (.prepend [(ctxCall, cFrameMid)] :: cEqStack)
          remRows remWorks remBodyResults remProdResults remCtxProdResults
          remFinalResults remCtxFinalResults) :
      ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
        expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
        (remEqSteps + 3) (1 + remProdSteps + 3) (1 + remRetSteps + 3)
        wRetStack cEqStack ((rhs, selected) :: remRows) (work :: remWorks)
        ((Atom.notReducible, wBMid) :: remBodyResults)
        ((Atom.notReducible, wBMid) :: remProdResults)
        ((ctxProdVal, cFrameMid) :: remCtxProdResults)
        ((expr, wBMid) :: remFinalResults)
        ((ctxCall, cFrameMid) :: remCtxFinalResults)
  | cons_ordinary_stopped
      (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation)
      (rhs wBodyVal : Atom) (selected wBMid : Bindings)
      (work : Spec.Eval.Steps.EquationWork) (ctxProdVal : Entry.Value)
      (cFrameMid : Completed.Frame)
      (remEqSteps remProdSteps remRetSteps : Nat)
      (remRows : List (Atom × Bindings))
      (remWorks : List Spec.Eval.Steps.EquationWork)
      (remBodyResults remProdResults : ResultSet)
      (remCtxProdResults : List Completed.Result)
      (remFinalResults : ResultSet)
      (remCtxFinalResults : List Completed.Result)
      (eqReady :
        (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
          (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
            (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
      (mergeFilterEq :
        ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
        [(wBodyVal, wBMid)])
      (outBindingsEq : cFrameMid.bindings = work.bindings)
      (unifyRel :
        Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
          (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
      (ctxProdEq : ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
      (bodyEraseEq : ctxProdVal.erase = wBodyVal)
      (notFunc : ∀ body, wBodyVal ≠ .expression [.symbol "function", body])
      (notRefused : wBodyVal ≠ Atom.notReducible)
      (stopped : isEmptyOrError wBodyVal = true)
      (actMid : ScopedActivationRel wBMid cFrameMid)
      (tailSpine :
        ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
          expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
          remEqSteps remProdSteps remRetSteps
          (.prepend [(wBodyVal, wBMid)] :: wRetStack)
          (.prepend [(ctxProdVal, cFrameMid)] :: cEqStack)
          remRows remWorks remBodyResults remProdResults remCtxProdResults
          remFinalResults remCtxFinalResults) :
      ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
        expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
        (remEqSteps + 3) (1 + remProdSteps + 3) (1 + remRetSteps + 3)
        wRetStack cEqStack ((rhs, selected) :: remRows) (work :: remWorks)
        ((wBodyVal, wBMid) :: remBodyResults)
        ((wBodyVal, wBMid) :: remProdResults)
        ((ctxProdVal, cFrameMid) :: remCtxProdResults)
        ((wBodyVal, wBMid) :: remFinalResults)
        ((ctxProdVal, cFrameMid) :: remCtxFinalResults)
  | cons_ordinary_evaluate
      (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation)
      (rhs wBodyVal : Atom) (selected wBMid : Bindings)
      (work : Spec.Eval.Steps.EquationWork) (ctxProdVal : Entry.Value)
      (cFrameMid : Completed.Frame)
      (childSteps remEqSteps remProdSteps remRetSteps : Nat)
      (remRows : List (Atom × Bindings))
      (remWorks : List Spec.Eval.Steps.EquationWork)
      (remBodyResults remProdResults : ResultSet)
      (remCtxProdResults : List Completed.Result)
      (headFinalResults remFinalResults : ResultSet)
      (headCtxFinalResults remCtxFinalResults : List Completed.Result)
      (eqReady :
        (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
          (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
            (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
      (mergeFilterEq :
        ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
        [(wBodyVal, wBMid)])
      (outBindingsEq : cFrameMid.bindings = work.bindings)
      (unifyRel :
        Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
          (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
      (ctxProdEq :
        ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
      (bodyEraseEq : ctxProdVal.erase = wBodyVal)
      (notFunc : ∀ body, wBodyVal ≠ .expression [.symbol "function", body])
      (notRefused : wBodyVal ≠ Atom.notReducible)
      (clean : isEmptyOrError wBodyVal = false)
      (actMid : ScopedActivationRel wBMid cFrameMid)
      (childRun :
        ScopedTaskRun space dispatch hostDispatch policy
          (.atom wBodyVal expected wBMid (depth + 1) live)
          (.atom live scope ctxProdVal expected cFrameMid)
          (.append (.returns expr expected (depth + 1) remProdResults live) :: wRetStack)
          (.append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
          wEmitted cEmitted childSteps headFinalResults headCtxFinalResults)
      (tailSpine :
        ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
          expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
          remEqSteps remProdSteps remRetSteps
          (.prepend headFinalResults :: wRetStack)
          (.prepend headCtxFinalResults :: cEqStack)
          remRows remWorks remBodyResults remProdResults remCtxProdResults
          remFinalResults remCtxFinalResults) :
      ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
        expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
        (remEqSteps + 3) (1 + remProdSteps + 3)
        ((childSteps + 1) + remRetSteps + 3) wRetStack cEqStack
        ((rhs, selected) :: remRows) (work :: remWorks)
        ((wBodyVal, wBMid) :: remBodyResults)
        ((wBodyVal, wBMid) :: remProdResults)
        ((ctxProdVal, cFrameMid) :: remCtxProdResults)
        (headFinalResults ++ remFinalResults)
        (headCtxFinalResults ++ remCtxFinalResults)

/-- An ordinary equation row whose materialized body already passes its expected
type earns its child run at the concrete return and equation stacks.  This is
the first leaf constructor used by the recursive worker induction: no machine
execution is supplied by the caller. -/
theorem ScopedConcreteEquationWorksSpine.cons_ordinary_typePass
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    (rhs wBodyVal : Atom) (selected wBMid : Bindings)
    (work : Spec.Eval.Steps.EquationWork) (ctxProdVal : Entry.Value)
    (cFrameMid : Completed.Frame)
    {remEqSteps remProdSteps remRetSteps : Nat}
    {remRows : List (Atom × Bindings)}
    {remWorks : List Spec.Eval.Steps.EquationWork}
    {remBodyResults remProdResults : ResultSet}
    {remCtxProdResults : List Completed.Result}
    {remFinalResults : ResultSet}
    {remCtxFinalResults : List Completed.Result}
    (eqReady :
      (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
        (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
          (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
    (mergeFilterEq :
      ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
      [(wBodyVal, wBMid)])
    (outBindingsEq : cFrameMid.bindings = work.bindings)
    (unifyRel :
      Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
        (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
    (ctxProdEq : ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
    (bodyEraseEq : ctxProdVal.erase = wBodyVal)
    (notFunc : ∀ body, wBodyVal ≠ .expression [.symbol "function", body])
    (notRefused : wBodyVal ≠ Atom.notReducible)
    (clean : isEmptyOrError wBodyVal = false)
    (typePass : expected = Atom.atomType ∨ expected = getMetaType wBodyVal ∨
      getMetaType wBodyVal = Atom.variableType)
    (entryReady : ScopedAtomEntryReady policy wBodyVal ctxProdVal cFrameMid)
    (actMid : ScopedActivationRel wBMid cFrameMid)
    (tailSpine :
      ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
        expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
        remEqSteps remProdSteps remRetSteps
        (.prepend [(wBodyVal, wBMid)] :: wRetStack)
        (.prepend [(cFrameMid.read policy ctxProdVal, cFrameMid)] :: cEqStack)
        remRows remWorks remBodyResults remProdResults remCtxProdResults
        remFinalResults remCtxFinalResults) :
    ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
      expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
      (remEqSteps + 3) (1 + remProdSteps + 3) (2 + remRetSteps + 3)
      wRetStack cEqStack ((rhs, selected) :: remRows) (work :: remWorks)
      ((wBodyVal, wBMid) :: remBodyResults)
      ((wBodyVal, wBMid) :: remProdResults)
      ((ctxProdVal, cFrameMid) :: remCtxProdResults)
      ((wBodyVal, wBMid) :: remFinalResults)
      ((cFrameMid.read policy ctxProdVal, cFrameMid) :: remCtxFinalResults) := by
  apply ScopedConcreteEquationWorksSpine.cons_ordinary_evaluate
    (wRetStack := wRetStack) (cEqStack := cEqStack)
    (rhs := rhs) (wBodyVal := wBodyVal) (selected := selected) (wBMid := wBMid)
    (work := work) (ctxProdVal := ctxProdVal) (cFrameMid := cFrameMid)
    (childSteps := 1) (remEqSteps := remEqSteps) (remProdSteps := remProdSteps)
    (remRetSteps := remRetSteps) (remRows := remRows) (remWorks := remWorks)
    (remBodyResults := remBodyResults) (remProdResults := remProdResults)
    (remCtxProdResults := remCtxProdResults)
    (headFinalResults := [(wBodyVal, wBMid)])
    (remFinalResults := remFinalResults)
    (headCtxFinalResults := [(cFrameMid.read policy ctxProdVal, cFrameMid)])
    (remCtxFinalResults := remCtxFinalResults)
    eqReady mergeFilterEq outBindingsEq unifyRel ctxProdEq bodyEraseEq notFunc
    notRefused clean actMid
  · exact ScopedTaskRun.atomTypePass space dispatch hostDispatch policy
      wBodyVal expected wBMid depth live live scope ctxProdVal cFrameMid
      (.append (.returns expr expected (depth + 1) remProdResults live) :: wRetStack)
      (.append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
        .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
      wEmitted cEmitted entryReady clean typePass actMid
  · exact tailSpine

/-- The concrete equation spine preserves every ordered returned occurrence. -/
theorem ScopedConcreteEquationWorksSpine.finalResults_forall2
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {eqSteps prodSteps retSteps : Nat}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    {rows : List (Atom × Bindings)} {works : List Spec.Eval.Steps.EquationWork}
    {bodyResults prodResults : ResultSet} {ctxProdResults : List Completed.Result}
    {finalResults : ResultSet} {ctxFinalResults : List Completed.Result}
    (spine : ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
      expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
      eqSteps prodSteps retSteps wRetStack cEqStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults) :
    List.Forall₂ ScopedResultRel finalResults ctxFinalResults := by
  induction spine with
  | nil => exact .nil
  | cons_rejected => assumption
  | cons_ordinary_notReducible =>
      refine List.Forall₂.cons ?_ (by assumption)
      exact ⟨by symm; assumption, by assumption⟩
  | cons_ordinary_stopped =>
      refine List.Forall₂.cons ?_ (by assumption)
      exact ⟨by symm; assumption, by assumption⟩
  | cons_ordinary_evaluate =>
      apply List.rel_append
      · apply ScopedTaskRun.results_rel
        assumption
      · assumption

/-- One accepted worker equation row followed by the remaining equation pass. -/
theorem worker_equations_cons_run
    (space : Space) (dispatch : HE.GroundedDispatch)
    (expr expected : Atom) (wBIn : Bindings) (depth : Nat)
    (live : List Atom) (wEmitted : ResultSet)
    (rhs wVal : Atom) (selected wBMid : Bindings)
    (remEqSteps : Nat) (remRows : List (Atom × Bindings))
    (remBodyResults : ResultSet) (wStack : List RecursiveTasks.Frame)
    (eqReady :
      (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
        (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
          (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
    (mergeFilterEq :
      ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
      [(wVal, wBMid)])
    (tailRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run (remEqSteps + budget)
        ⟨space, .work (.equations expr expected wBIn (depth + 1) remRows live),
          .prepend [(wVal, wBMid)] :: wStack, wEmitted⟩ =
      (Checked.machine dispatch scopedTypes).run budget
        ⟨space, .returning remBodyResults,
          .prepend [(wVal, wBMid)] :: wStack, wEmitted⟩)
    (budget : Nat) :
    (Checked.machine dispatch scopedTypes).run ((remEqSteps + 3) + budget)
      ⟨space, .work (.equations expr expected wBIn (depth + 1)
        ((rhs, selected) :: remRows) live), wStack, wEmitted⟩ =
    (Checked.machine dispatch scopedTypes).run budget
      ⟨space, .returning ((wVal, wBMid) :: remBodyResults), wStack, wEmitted⟩ := by
  have hEqReady : ∀ lookup,
      RecursiveMachine.Checked.taskReady space dispatch
        (.equations expr expected wBIn (depth + 1)
          ((rhs, selected) :: remRows) live) lookup = true := by
    intro lookup
    simp [RecursiveMachine.Checked.taskReady, eqReady]
  have hEqEnter : ∀ lookup,
      RecursiveMachine.enter space dispatch
        (.equations expr expected wBIn (depth + 1)
          ((rhs, selected) :: remRows) live) lookup =
      (.returning [(wVal, wBMid)],
        [.append (.equations expr expected wBIn (depth + 1) remRows live)]) := by
    intro lookup
    simp [RecursiveMachine.enter, mergeFilterEq]
  have wStep1 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.equations expr expected wBIn (depth + 1)
            ((rhs, selected) :: remRows) live), wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [(wVal, wBMid)],
          .append (.equations expr expected wBIn (depth + 1) remRows live) :: wStack,
          wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady, hEqReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter, hEqEnter, Transition.relabel]
  have wStep2 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning [(wVal, wBMid)],
          .append (.equations expr expected wBIn (depth + 1) remRows live) :: wStack,
          wEmitted⟩ =
      some (.silent
        ⟨space, .work (.equations expr expected wBIn (depth + 1) remRows live),
          .prepend [(wVal, wBMid)] :: wStack, wEmitted⟩) := rfl
  have wStep3 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning remBodyResults,
          .prepend [(wVal, wBMid)] :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning ((wVal, wBMid) :: remBodyResults), wStack, wEmitted⟩) := rfl
  calc
    (Checked.machine dispatch scopedTypes).run ((remEqSteps + 3) + budget) _ =
        (Checked.machine dispatch scopedTypes).run
          (((remEqSteps + (budget + 1)) + 1) + 1) _ := by
            rw [show (remEqSteps + 3) + budget =
              ((remEqSteps + (budget + 1)) + 1) + 1 by omega]
    _ = (Checked.machine dispatch scopedTypes).run
          ((remEqSteps + (budget + 1)) + 1) _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep1
    _ = (Checked.machine dispatch scopedTypes).run
          (remEqSteps + (budget + 1)) _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep2
    _ = (Checked.machine dispatch scopedTypes).run (budget + 1) _ :=
          tailRun (budget + 1)
    _ = (Checked.machine dispatch scopedTypes).run budget _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep3

/-- Pass one remains stack-polymorphic: equation matching itself never
consults the configuration-sensitive type lookup. -/
theorem ScopedConcreteEquationWorksSpine.equations_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {eqSteps prodSteps retSteps : Nat}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    {rows : List (Atom × Bindings)} {works : List Spec.Eval.Steps.EquationWork}
    {bodyResults prodResults : ResultSet} {ctxProdResults : List Completed.Result}
    {finalResults : ResultSet} {ctxFinalResults : List Completed.Result}
    (spine : ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
      expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
      eqSteps prodSteps retSteps wRetStack cEqStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults)
    (wStack : List RecursiveTasks.Frame) (budget : Nat) :
    (Checked.machine dispatch scopedTypes).run (eqSteps + budget)
      ⟨space, .work (.equations expr expected wBIn (depth + 1) rows live),
        wStack, wEmitted⟩ =
    (Checked.machine dispatch scopedTypes).run budget
      ⟨space, .returning bodyResults, wStack, wEmitted⟩ := by
  induction spine generalizing wStack budget with
  | nil =>
      have wStep :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.equations expr expected wBIn (depth + 1) [] live),
              wStack, wEmitted⟩ =
          some (.silent ⟨space, .returning [], wStack, wEmitted⟩) := rfl
      rw [Nat.add_comm 1 budget,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep]
  | cons_rejected wRetStack cEqStack rhs selected remEqSteps remProdSteps
      remRetSteps remRows works bodyResults prodResults ctxProdResults
      finalResults ctxFinalResults eqReady mergeFilterEmpty _ ih =>
      have hEqReady : ∀ lookup,
          RecursiveMachine.Checked.taskReady space dispatch
            (.equations expr expected wBIn (depth + 1)
              ((rhs, selected) :: remRows) live) lookup = true := by
        intro lookup
        simp [RecursiveMachine.Checked.taskReady,eqReady]
      have hEqEnter : ∀ lookup,
          RecursiveMachine.enter space dispatch
            (.equations expr expected wBIn (depth + 1)
              ((rhs, selected) :: remRows) live) lookup =
          (.returning [],
            [.append (.equations expr expected wBIn (depth + 1) remRows live)]) := by
        intro lookup
        simp [RecursiveMachine.enter,mergeFilterEmpty]
      have wStep1 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.equations expr expected wBIn (depth + 1)
                ((rhs, selected) :: remRows) live), wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [],
              .append (.equations expr expected wBIn (depth + 1) remRows live) :: wStack,
              wEmitted⟩) := by
        simp [Checked.machine,RecursiveMachine.Checked.guardMachine,Checked.blocked,
          FirstSuccessRecursiveStrategy.taskReady,hEqReady,
          FirstSuccessRecursiveExecution.machine,FirstSuccessRecursiveExecution.next,
          FirstSuccessRecursiveStrategy.enter,hEqEnter,Transition.relabel]
      have wStep2 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .returning [],
              .append (.equations expr expected wBIn (depth + 1) remRows live) :: wStack,
              wEmitted⟩ =
          some (.silent
            ⟨space, .work (.equations expr expected wBIn (depth + 1) remRows live),
              .prepend [] :: wStack,wEmitted⟩) := rfl
      have wStep3 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .returning bodyResults,.prepend [] :: wStack,wEmitted⟩ =
          some (.silent ⟨space, .returning bodyResults,wStack,wEmitted⟩) := rfl
      calc
        (Checked.machine dispatch scopedTypes).run ((remEqSteps + 3) + budget) _
            = (Checked.machine dispatch scopedTypes).run
                (((remEqSteps + (budget + 1)) + 1) + 1) _ := by
                rw [show (remEqSteps + 3) + budget =
                  ((remEqSteps + (budget + 1)) + 1) + 1 by omega]
        _ = (Checked.machine dispatch scopedTypes).run
              ((remEqSteps + (budget + 1)) + 1) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep1
        _ = (Checked.machine dispatch scopedTypes).run
              (remEqSteps + (budget + 1)) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep2
        _ = (Checked.machine dispatch scopedTypes).run (budget + 1) _ :=
              ih (.prepend [] :: wStack) (budget + 1)
        _ = (Checked.machine dispatch scopedTypes).run budget _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep3
  | cons_ordinary_notReducible wRetStack cEqStack rhs selected wBMid work
      ctxProdVal cFrameMid remEqSteps remProdSteps remRetSteps remRows remWorks
      remBodyResults remProdResults remCtxProdResults remFinalResults
      remCtxFinalResults eqReady mergeFilterEq _outBindingsEq _unifyRel _ctxProdEq
      _bodyEraseEq _callEq _actMid _tailSpine ih =>
      exact worker_equations_cons_run space dispatch expr expected wBIn depth live
        wEmitted rhs Atom.notReducible selected wBMid remEqSteps remRows remBodyResults
        wStack eqReady mergeFilterEq
        (fun later => ih (.prepend [(Atom.notReducible, wBMid)] :: wStack) later) budget
  | cons_ordinary_stopped wRetStack cEqStack rhs wBodyVal selected wBMid work
      ctxProdVal cFrameMid remEqSteps remProdSteps remRetSteps remRows remWorks
      remBodyResults remProdResults remCtxProdResults remFinalResults
      remCtxFinalResults eqReady mergeFilterEq _outBindingsEq _unifyRel _ctxProdEq
      _bodyEraseEq _notFunc _notRefused _stopped _actMid _tailSpine ih =>
      exact worker_equations_cons_run space dispatch expr expected wBIn depth live
        wEmitted rhs wBodyVal selected wBMid remEqSteps remRows remBodyResults
        wStack eqReady mergeFilterEq
        (fun later => ih (.prepend [(wBodyVal, wBMid)] :: wStack) later) budget
  | cons_ordinary_evaluate wRetStack cEqStack rhs wBodyVal selected wBMid work
      ctxProdVal cFrameMid childSteps remEqSteps remProdSteps remRetSteps remRows
      remWorks remBodyResults remProdResults remCtxProdResults headFinalResults
      remFinalResults headCtxFinalResults remCtxFinalResults eqReady mergeFilterEq
      _outBindingsEq _unifyRel _ctxProdEq _bodyEraseEq _notFunc _notRefused _clean
      _actMid _childRun _tailSpine ih =>
      have hEqReady : ∀ lookup,
          RecursiveMachine.Checked.taskReady space dispatch
            (.equations expr expected wBIn (depth + 1)
              ((rhs, selected) :: remRows) live) lookup = true := by
        intro lookup
        simp [RecursiveMachine.Checked.taskReady,eqReady]
      have hEqEnter : ∀ lookup,
          RecursiveMachine.enter space dispatch
            (.equations expr expected wBIn (depth + 1)
              ((rhs, selected) :: remRows) live) lookup =
          (.returning [(wBodyVal,wBMid)],
            [.append (.equations expr expected wBIn (depth + 1) remRows live)]) := by
        intro lookup
        simp [RecursiveMachine.enter,mergeFilterEq]
      have wStep1 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.equations expr expected wBIn (depth + 1)
                ((rhs, selected) :: remRows) live),wStack,wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(wBodyVal,wBMid)],
              .append (.equations expr expected wBIn (depth + 1) remRows live) :: wStack,
              wEmitted⟩) := by
        simp [Checked.machine,RecursiveMachine.Checked.guardMachine,Checked.blocked,
          FirstSuccessRecursiveStrategy.taskReady,hEqReady,
          FirstSuccessRecursiveExecution.machine,FirstSuccessRecursiveExecution.next,
          FirstSuccessRecursiveStrategy.enter,hEqEnter,Transition.relabel]
      have wStep2 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .returning [(wBodyVal,wBMid)],
              .append (.equations expr expected wBIn (depth + 1) remRows live) :: wStack,
              wEmitted⟩ =
          some (.silent
            ⟨space, .work (.equations expr expected wBIn (depth + 1) remRows live),
              .prepend [(wBodyVal,wBMid)] :: wStack,wEmitted⟩) := rfl
      have wStep3 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .returning remBodyResults,
              .prepend [(wBodyVal,wBMid)] :: wStack,wEmitted⟩ =
          some (.silent
            ⟨space, .returning ((wBodyVal,wBMid) :: remBodyResults),wStack,wEmitted⟩) := rfl
      calc
        (Checked.machine dispatch scopedTypes).run ((remEqSteps + 3) + budget) _
            = (Checked.machine dispatch scopedTypes).run
                (((remEqSteps + (budget + 1)) + 1) + 1) _ := by
                rw [show (remEqSteps + 3) + budget =
                  ((remEqSteps + (budget + 1)) + 1) + 1 by omega]
        _ = (Checked.machine dispatch scopedTypes).run
              ((remEqSteps + (budget + 1)) + 1) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep1
        _ = (Checked.machine dispatch scopedTypes).run
              (remEqSteps + (budget + 1)) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep2
        _ = (Checked.machine dispatch scopedTypes).run (budget + 1) _ :=
              ih (.prepend [(wBodyVal,wBMid)] :: wStack) (budget + 1)
        _ = (Checked.machine dispatch scopedTypes).run budget _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep3

/-- One ordinary raw producer row followed by the remaining production pass. -/
theorem worker_productions_cons_run
    (space : Space) (dispatch : HE.GroundedDispatch)
    (expr expected wVal : Atom) (wB : Bindings) (depth : Nat)
    (live : List Atom) (wEmitted : ResultSet)
    (remProdSteps : Nat) (remBodyResults remProdResults : ResultSet)
    (wStack : List RecursiveTasks.Frame)
    (notFunc : ∀ body, wVal ≠ .expression [.symbol "function", body])
    (tailRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run (remProdSteps + budget)
        ⟨space, .work (.productions (depth + 1) remBodyResults (expected :: live)
          (some expr) .emitted), .prepend [(wVal, wB)] :: wStack, wEmitted⟩ =
      (Checked.machine dispatch scopedTypes).run budget
        ⟨space, .returning remProdResults,
          .prepend [(wVal, wB)] :: wStack, wEmitted⟩)
    (budget : Nat) :
    (Checked.machine dispatch scopedTypes).run ((1 + remProdSteps + 3) + budget)
      ⟨space, .work (.productions (depth + 1)
        ((wVal, wB) :: remBodyResults) (expected :: live) (some expr) .emitted),
        wStack, wEmitted⟩ =
    (Checked.machine dispatch scopedTypes).run budget
      ⟨space, .returning ((wVal, wB) :: remProdResults), wStack, wEmitted⟩ := by
  have wStep1 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.productions (depth + 1)
          ((wVal, wB) :: remBodyResults) (expected :: live) (some expr) .emitted),
          wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.produced wVal wB (depth + 1)
          (expected :: live) (some expr) .emitted),
          .append (.productions (depth + 1) remBodyResults (expected :: live)
            (some expr) .emitted) :: wStack, wEmitted⟩) := rfl
  have wRaw := worker_producedRaw_silent_step
    space dispatch wVal wB depth (expected :: live) (some expr)
    (.append (.productions (depth + 1) remBodyResults (expected :: live)
      (some expr) .emitted) :: wStack) wEmitted notFunc
  have wStep2 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning [(wVal, wB)],
          .append (.productions (depth + 1) remBodyResults (expected :: live)
            (some expr) .emitted) :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.productions (depth + 1) remBodyResults (expected :: live)
          (some expr) .emitted), .prepend [(wVal, wB)] :: wStack, wEmitted⟩) := rfl
  have wStep3 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning remProdResults,
          .prepend [(wVal, wB)] :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning ((wVal, wB) :: remProdResults), wStack, wEmitted⟩) := rfl
  calc
    (Checked.machine dispatch scopedTypes).run ((1 + remProdSteps + 3) + budget) _ =
        (Checked.machine dispatch scopedTypes).run
          ((((remProdSteps + (budget + 1)) + 1) + 1) + 1) _ := by
            rw [show (1 + remProdSteps + 3) + budget =
              (((remProdSteps + (budget + 1)) + 1) + 1) + 1 by omega]
    _ = (Checked.machine dispatch scopedTypes).run
          (((remProdSteps + (budget + 1)) + 1) + 1) _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep1
    _ = (Checked.machine dispatch scopedTypes).run
          ((remProdSteps + (budget + 1)) + 1) _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wRaw
    _ = (Checked.machine dispatch scopedTypes).run
          (remProdSteps + (budget + 1)) _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep2
    _ = (Checked.machine dispatch scopedTypes).run (budget + 1) _ :=
          tailRun (budget + 1)
    _ = (Checked.machine dispatch scopedTypes).run budget _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep3

/-- Pass two remains stack-polymorphic for the ordinary non-function producer
profile; each body value is returned raw in one semantic step. -/
theorem ScopedConcreteEquationWorksSpine.productions_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {eqSteps prodSteps retSteps : Nat}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    {rows : List (Atom × Bindings)} {works : List Spec.Eval.Steps.EquationWork}
    {bodyResults prodResults : ResultSet} {ctxProdResults : List Completed.Result}
    {finalResults : ResultSet} {ctxFinalResults : List Completed.Result}
    (spine : ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
      expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
      eqSteps prodSteps retSteps wRetStack cEqStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults)
    (wStack : List RecursiveTasks.Frame) (budget : Nat) :
    (Checked.machine dispatch scopedTypes).run (prodSteps + budget)
      ⟨space, .work (.productions (depth + 1) bodyResults (expected :: live)
        (some expr) .emitted),wStack,wEmitted⟩ =
    (Checked.machine dispatch scopedTypes).run budget
      ⟨space, .returning prodResults,wStack,wEmitted⟩ := by
  induction spine generalizing wStack budget with
  | nil =>
      have wStep :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.productions (depth + 1) [] (expected :: live)
              (some expr) .emitted),wStack,wEmitted⟩ =
          some (.silent ⟨space, .returning [],wStack,wEmitted⟩) := rfl
      rw [Nat.add_comm 1 budget,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep]
  | cons_rejected wRetStack cEqStack rhs selected remEqSteps remProdSteps
      remRetSteps remRows works bodyResults prodResults ctxProdResults
      finalResults ctxFinalResults eqReady mergeFilterEmpty tailSpine ih =>
      exact ih wStack budget
  | cons_ordinary_notReducible wRetStack cEqStack rhs selected wBMid work
      ctxProdVal cFrameMid remEqSteps remProdSteps remRetSteps remRows remWorks
      remBodyResults remProdResults remCtxProdResults remFinalResults
      remCtxFinalResults _eqReady _mergeFilterEq _outBindingsEq _unifyRel _ctxProdEq
      _bodyEraseEq _callEq _actMid _tailSpine ih =>
      exact worker_productions_cons_run space dispatch expr expected Atom.notReducible
        wBMid depth live wEmitted remProdSteps remBodyResults remProdResults wStack
        (by intro body h; cases h)
        (fun later => ih (.prepend [(Atom.notReducible, wBMid)] :: wStack) later) budget
  | cons_ordinary_stopped wRetStack cEqStack rhs wBodyVal selected wBMid work
      ctxProdVal cFrameMid remEqSteps remProdSteps remRetSteps remRows remWorks
      remBodyResults remProdResults remCtxProdResults remFinalResults
      remCtxFinalResults _eqReady _mergeFilterEq _outBindingsEq _unifyRel _ctxProdEq
      _bodyEraseEq notFunc _notRefused _stopped _actMid _tailSpine ih =>
      exact worker_productions_cons_run space dispatch expr expected wBodyVal wBMid
        depth live wEmitted remProdSteps remBodyResults remProdResults wStack notFunc
        (fun later => ih (.prepend [(wBodyVal, wBMid)] :: wStack) later) budget
  | cons_ordinary_evaluate wRetStack cEqStack rhs wBodyVal selected wBMid work
      ctxProdVal cFrameMid childSteps remEqSteps remProdSteps remRetSteps remRows
      remWorks remBodyResults remProdResults remCtxProdResults headFinalResults
      remFinalResults headCtxFinalResults remCtxFinalResults _eqReady _mergeFilterEq
      _outBindingsEq _unifyRel _ctxProdEq _bodyEraseEq notFunc _notRefused _clean
      _actMid _childRun _tailSpine ih =>
      have wStep1 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.productions (depth + 1)
                ((wBodyVal,wBMid) :: remBodyResults) (expected :: live)
                (some expr) .emitted),wStack,wEmitted⟩ =
          some (.silent
            ⟨space, .work (.produced wBodyVal wBMid (depth + 1)
                (expected :: live) (some expr) .emitted),
              .append (.productions (depth + 1) remBodyResults (expected :: live)
                (some expr) .emitted) :: wStack,wEmitted⟩) := rfl
      have wRaw := worker_producedRaw_silent_step
        space dispatch wBodyVal wBMid depth (expected :: live) (some expr)
        (.append (.productions (depth + 1) remBodyResults (expected :: live)
          (some expr) .emitted) :: wStack) wEmitted notFunc
      have wStep2 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .returning [(wBodyVal,wBMid)],
              .append (.productions (depth + 1) remBodyResults (expected :: live)
                (some expr) .emitted) :: wStack,wEmitted⟩ =
          some (.silent
            ⟨space, .work (.productions (depth + 1) remBodyResults (expected :: live)
                (some expr) .emitted),
              .prepend [(wBodyVal,wBMid)] :: wStack,wEmitted⟩) := rfl
      have wStep3 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .returning remProdResults,
              .prepend [(wBodyVal,wBMid)] :: wStack,wEmitted⟩ =
          some (.silent
            ⟨space, .returning ((wBodyVal,wBMid) :: remProdResults),wStack,wEmitted⟩) := rfl
      calc
        (Checked.machine dispatch scopedTypes).run
            ((1 + remProdSteps + 3) + budget) _ =
          (Checked.machine dispatch scopedTypes).run
            ((((remProdSteps + (budget + 1)) + 1) + 1) + 1) _ := by
            rw [show (1 + remProdSteps + 3) + budget =
              (((remProdSteps + (budget + 1)) + 1) + 1) + 1 by omega]
        _ = (Checked.machine dispatch scopedTypes).run
              (((remProdSteps + (budget + 1)) + 1) + 1) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep1
        _ = (Checked.machine dispatch scopedTypes).run
              ((remProdSteps + (budget + 1)) + 1) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wRaw
        _ = (Checked.machine dispatch scopedTypes).run
              (remProdSteps + (budget + 1)) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep2
        _ = (Checked.machine dispatch scopedTypes).run (budget + 1) _ :=
              ih (.prepend [(wBodyVal,wBMid)] :: wStack) (budget + 1)
        _ = (Checked.machine dispatch scopedTypes).run budget _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep3

/-- One non-recursive returned value followed by the remaining return pass. -/
theorem worker_returns_leaf_cons_run
    (space : Space) (dispatch : HE.GroundedDispatch)
    (expr value expected : Atom) (wB : Bindings) (depth : Nat)
    (live : List Atom) (wEmitted : ResultSet)
    (remRetSteps : Nat) (remProdResults headResults remFinalResults : ResultSet)
    (wRetStack : List RecursiveTasks.Frame)
    (leafStep :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.returned expr value expected wB (depth + 1) live),
          .append (.returns expr expected (depth + 1) remProdResults live) :: wRetStack,
          wEmitted⟩ =
      some (.silent
        ⟨space, .returning headResults,
          .append (.returns expr expected (depth + 1) remProdResults live) :: wRetStack,
          wEmitted⟩))
    (tailRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run (remRetSteps + budget)
        ⟨space, .work (.returns expr expected (depth + 1) remProdResults live),
          .prepend headResults :: wRetStack, wEmitted⟩ =
      (Checked.machine dispatch scopedTypes).run budget
        ⟨space, .returning remFinalResults,
          .prepend headResults :: wRetStack, wEmitted⟩)
    (budget : Nat) :
    (Checked.machine dispatch scopedTypes).run ((1 + remRetSteps + 3) + budget)
      ⟨space, .work (.returns expr expected (depth + 1)
        ((value, wB) :: remProdResults) live), wRetStack, wEmitted⟩ =
    (Checked.machine dispatch scopedTypes).run budget
      ⟨space, .returning (headResults ++ remFinalResults), wRetStack, wEmitted⟩ := by
  have wStep1 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.returns expr expected (depth + 1)
          ((value, wB) :: remProdResults) live), wRetStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.returned expr value expected wB (depth + 1) live),
          .append (.returns expr expected (depth + 1) remProdResults live) :: wRetStack,
          wEmitted⟩) := rfl
  have wStep3 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning headResults,
          .append (.returns expr expected (depth + 1) remProdResults live) :: wRetStack,
          wEmitted⟩ =
      some (.silent
        ⟨space, .work (.returns expr expected (depth + 1) remProdResults live),
          .prepend headResults :: wRetStack, wEmitted⟩) := rfl
  have wStep4 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning remFinalResults,
          .prepend headResults :: wRetStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning (headResults ++ remFinalResults), wRetStack, wEmitted⟩) := rfl
  calc
    (Checked.machine dispatch scopedTypes).run ((1 + remRetSteps + 3) + budget) _ =
        (Checked.machine dispatch scopedTypes).run
          (((remRetSteps + (budget + 1)) + 1) + 1 + 1) _ := by
            rw [show (1 + remRetSteps + 3) + budget =
              ((remRetSteps + (budget + 1)) + 1) + 1 + 1 by omega]
    _ = (Checked.machine dispatch scopedTypes).run
          (((remRetSteps + (budget + 1)) + 1) + 1) _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep1
    _ = (Checked.machine dispatch scopedTypes).run
          ((remRetSteps + (budget + 1)) + 1) _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent leafStep
    _ = (Checked.machine dispatch scopedTypes).run
          (remRetSteps + (budget + 1)) _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep3
    _ = (Checked.machine dispatch scopedTypes).run (budget + 1) _ :=
          tailRun (budget + 1)
    _ = (Checked.machine dispatch scopedTypes).run budget _ :=
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep4

/-- Pass three follows the concrete saved return stack.  Each equation body may
produce an arbitrary recursive result batch, which is prepended before the
remaining equation rows. -/
theorem ScopedConcreteEquationWorksSpine.returns_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {eqSteps prodSteps retSteps : Nat}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    {rows : List (Atom × Bindings)} {works : List Spec.Eval.Steps.EquationWork}
    {bodyResults prodResults : ResultSet} {ctxProdResults : List Completed.Result}
    {finalResults : ResultSet} {ctxFinalResults : List Completed.Result}
    (spine : ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
      expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
      eqSteps prodSteps retSteps wRetStack cEqStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults)
    (budget : Nat) :
    (Checked.machine dispatch scopedTypes).run (retSteps + budget)
      ⟨space, .work (.returns expr expected (depth + 1) prodResults live),
        wRetStack,wEmitted⟩ =
    (Checked.machine dispatch scopedTypes).run budget
      ⟨space, .returning finalResults,wRetStack,wEmitted⟩ := by
  induction spine generalizing budget with
  | nil wRetStack cEqStack =>
      have wStep :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.returns expr expected (depth + 1) [] live),
              wRetStack,wEmitted⟩ =
          some (.silent ⟨space, .returning [],wRetStack,wEmitted⟩) := rfl
      rw [Nat.add_comm 1 budget,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep]
  | cons_rejected wRetStack cEqStack rhs selected remEqSteps remProdSteps
      remRetSteps remRows works bodyResults prodResults ctxProdResults
      finalResults ctxFinalResults eqReady mergeFilterEmpty tailSpine ih =>
      exact ih budget
  | cons_ordinary_notReducible wRetStack cEqStack rhs selected wBMid work
      ctxProdVal cFrameMid remEqSteps remProdSteps remRetSteps remRows remWorks
      remBodyResults remProdResults remCtxProdResults remFinalResults
      remCtxFinalResults _eqReady _mergeFilterEq _outBindingsEq _unifyRel _ctxProdEq
      _bodyEraseEq _callEq _actMid _tailSpine ih =>
      have leafStep :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.returned expr Atom.notReducible expected wBMid
              (depth + 1) live),
              .append (.returns expr expected (depth + 1) remProdResults live) ::
                wRetStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(expr, wBMid)],
              .append (.returns expr expected (depth + 1) remProdResults live) ::
                wRetStack, wEmitted⟩) := rfl
      exact worker_returns_leaf_cons_run space dispatch expr Atom.notReducible expected
        wBMid depth live wEmitted remRetSteps remProdResults [(expr, wBMid)]
        remFinalResults wRetStack leafStep (fun later => ih later) budget
  | cons_ordinary_stopped wRetStack cEqStack rhs wBodyVal selected wBMid work
      ctxProdVal cFrameMid remEqSteps remProdSteps remRetSteps remRows remWorks
      remBodyResults remProdResults remCtxProdResults remFinalResults
      remCtxFinalResults _eqReady _mergeFilterEq _outBindingsEq _unifyRel _ctxProdEq
      _bodyEraseEq _notFunc notRefused stopped _actMid _tailSpine ih =>
      have leafStep :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.returned expr wBodyVal expected wBMid
              (depth + 1) live),
              .append (.returns expr expected (depth + 1) remProdResults live) ::
                wRetStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(wBodyVal, wBMid)],
              .append (.returns expr expected (depth + 1) remProdResults live) ::
                wRetStack, wEmitted⟩) := by
        simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
          FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
          FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
          FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
          notRefused, stopped, Transition.relabel]
      exact worker_returns_leaf_cons_run space dispatch expr wBodyVal expected
        wBMid depth live wEmitted remRetSteps remProdResults [(wBodyVal, wBMid)]
        remFinalResults wRetStack leafStep (fun later => ih later) budget
  | cons_ordinary_evaluate wRetStack cEqStack rhs wBodyVal selected wBMid work
      ctxProdVal cFrameMid childSteps remEqSteps remProdSteps remRetSteps remRows
      remWorks remBodyResults remProdResults remCtxProdResults headFinalResults
      remFinalResults headCtxFinalResults remCtxFinalResults _eqReady _mergeFilterEq
      _outBindingsEq _unifyRel _ctxProdEq _bodyEraseEq _notFunc notRefused clean
      _actMid childRun _tailSpine ih =>
      have wStep1 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.returns expr expected (depth + 1)
                ((wBodyVal,wBMid) :: remProdResults) live),wRetStack,wEmitted⟩ =
          some (.silent
            ⟨space, .work (.returned expr wBodyVal expected wBMid (depth + 1) live),
              .append (.returns expr expected (depth + 1) remProdResults live) ::
                wRetStack,wEmitted⟩) := rfl
      have wStep2 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .work (.returned expr wBodyVal expected wBMid (depth + 1) live),
              .append (.returns expr expected (depth + 1) remProdResults live) ::
                wRetStack,wEmitted⟩ =
          some (.silent
            ⟨space, .work (.atom wBodyVal expected wBMid (depth + 1) live),
              .append (.returns expr expected (depth + 1) remProdResults live) ::
                wRetStack,wEmitted⟩) := by
        simp [Checked.machine,RecursiveMachine.Checked.guardMachine,Checked.blocked,
          FirstSuccessRecursiveStrategy.taskReady,RecursiveMachine.Checked.taskReady,
          FirstSuccessRecursiveExecution.machine,FirstSuccessRecursiveExecution.next,
          FirstSuccessRecursiveStrategy.enter,RecursiveMachine.enter,
          notRefused,clean,Transition.relabel]
      have wStep3 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .returning headFinalResults,
              .append (.returns expr expected (depth + 1) remProdResults live) ::
                wRetStack,wEmitted⟩ =
          some (.silent
            ⟨space, .work (.returns expr expected (depth + 1) remProdResults live),
              .prepend headFinalResults :: wRetStack,wEmitted⟩) := rfl
      have wStep4 :
          (Checked.machine dispatch scopedTypes).step
            ⟨space, .returning remFinalResults,
              .prepend headFinalResults :: wRetStack,wEmitted⟩ =
          some (.silent
            ⟨space, .returning (headFinalResults ++ remFinalResults),
              wRetStack,wEmitted⟩) := rfl
      calc
        (Checked.machine dispatch scopedTypes).run
            (((childSteps + 1) + remRetSteps + 3) + budget) _ =
          (Checked.machine dispatch scopedTypes).run
            (((childSteps + ((remRetSteps + (budget + 1)) + 1)) + 1) + 1) _ := by
            rw [show ((childSteps + 1) + remRetSteps + 3) + budget =
              ((childSteps + ((remRetSteps + (budget + 1)) + 1)) + 1) + 1 by omega]
        _ = (Checked.machine dispatch scopedTypes).run
              ((childSteps + ((remRetSteps + (budget + 1)) + 1)) + 1) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep1
        _ = (Checked.machine dispatch scopedTypes).run
              (childSteps + ((remRetSteps + (budget + 1)) + 1))
              ⟨space, .work (.atom wBodyVal expected wBMid (depth + 1) live),
                .append (.returns expr expected (depth + 1) remProdResults live) ::
                  wRetStack,wEmitted⟩ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep2
        _ = (Checked.machine dispatch scopedTypes).run
              ((remRetSteps + (budget + 1)) + 1)
              ⟨space, .returning headFinalResults,
                .append (.returns expr expected (depth + 1) remProdResults live) ::
                  wRetStack,wEmitted⟩ :=
              childRun.worker_run ((remRetSteps + (budget + 1)) + 1)
        _ = (Checked.machine dispatch scopedTypes).run
              (remRetSteps + (budget + 1)) _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep3
        _ = (Checked.machine dispatch scopedTypes).run (budget + 1) _ := ih (budget + 1)
        _ = (Checked.machine dispatch scopedTypes).run budget _ :=
              (Checked.machine dispatch scopedTypes).run_succ_silent wStep4

/-- Contextual traversal of one non-recursive ordinary equation result followed
by the remaining equation rows. -/
theorem contextual_equations_leaf_localSteps
    (space : Space) (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (live : List Atom) (scope : List String)
    (ctxCall : Entry.Value) (expected : Atom) (cFrameIn : Completed.Frame)
    (work : Spec.Eval.Steps.EquationWork)
    (remWorks : List Spec.Eval.Steps.EquationWork)
    (ctxProdVal : Entry.Value) (cFrameMid : Completed.Frame)
    (headCtxResults remCtxResults : List Completed.Result)
    (cEqStack : List RecursiveTasks.Contextual.Continuation)
    (outBindingsEq : cFrameMid.bindings = work.bindings)
    (unifyRel :
      Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
        (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
    (ctxProdEq : ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
    (notPending : ¬Completed.FunctionPending policy ctxProdVal)
    (returnStep :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.work (.returned live scope ctxCall expected ctxProdVal cFrameMid),
          .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.returning headCtxResults,
          .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack))
    (tailSteps :
      RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
        (.work (.equations live scope ctxCall expected cFrameIn remWorks),
          .prepend headCtxResults :: cEqStack)
        (.returning remCtxResults, .prepend headCtxResults :: cEqStack)) :
    RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
      (.work (.equations live scope ctxCall expected cFrameIn (work :: remWorks)), cEqStack)
      (.returning (headCtxResults ++ remCtxResults), cEqStack) := by
  have cLocal1 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.work (.equations live scope ctxCall expected cFrameIn (work :: remWorks)), cEqStack)
        (.work (.boundary (expected :: live) scope (some ctxCall.erase) .producer
          ctxProdVal cFrameMid),
          .boundaryBatch live scope none (.returned ctxCall expected) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) := by
    simpa only [ctxProdEq] using
      (RecursiveMachine.Contextual.LocalStep.equationsCons outBindingsEq unifyRel)
  have cLocal2 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.work (.boundary (expected :: live) scope (some ctxCall.erase) .producer
          ctxProdVal cFrameMid),
          .boundaryBatch live scope none (.returned ctxCall expected) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.returning [(ctxProdVal, cFrameMid)],
          .boundaryBatch live scope none (.returned ctxCall expected) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
    .boundaryProducerRaw notPending
  have cLocal3 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.returning [(ctxProdVal, cFrameMid)],
          .boundaryBatch live scope none (.returned ctxCall expected) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.work (.boundaryBatch live scope none (.returned ctxCall expected)
          [(ctxProdVal, cFrameMid)]),
          .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
    .boundaryBatch
  have cLocal4 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.work (.boundaryBatch live scope none (.returned ctxCall expected)
          [(ctxProdVal, cFrameMid)]),
          .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.work (.boundary live scope none (.returned ctxCall expected)
          ctxProdVal cFrameMid),
          .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
    .boundaryBatchCons
  have cLocal5 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.work (.boundary live scope none (.returned ctxCall expected)
          ctxProdVal cFrameMid),
          .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.work (.returned live scope ctxCall expected ctxProdVal cFrameMid),
          .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
    .boundaryReturned
  have cLocal7 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.returning headCtxResults,
          .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.work (.boundaryBatch live scope none (.returned ctxCall expected) []),
          .prepend headCtxResults ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
    .append
  have cLocal8 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.work (.boundaryBatch live scope none (.returned ctxCall expected) []),
          .prepend headCtxResults ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.returning [], .prepend headCtxResults ::
          .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
    .boundaryBatchNil
  have cLocal9 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.returning [], .prepend headCtxResults ::
          .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.returning headCtxResults,
          .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) := by
    simpa only [List.append_nil] using
      (RecursiveMachine.Contextual.LocalStep.prepend
        (selected := headCtxResults) (results := []))
  have cLocal10 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.returning headCtxResults,
          .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
        (.work (.equations live scope ctxCall expected cFrameIn remWorks),
          .prepend headCtxResults :: cEqStack) :=
    .append
  have cLocal11 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.returning remCtxResults, .prepend headCtxResults :: cEqStack)
        (.returning (headCtxResults ++ remCtxResults), cEqStack) :=
    .prepend
  have first := (((((Relation.ReflTransGen.single cLocal1).tail cLocal2).tail cLocal3).tail cLocal4).tail cLocal5).tail returnStep
  exact (((((first.tail cLocal7).tail cLocal8).tail cLocal9).tail cLocal10).trans tailSteps).tail cLocal11

/-- The contextual equation traversal follows the concrete equation stack and
uses the same earned child runs as the worker return pass. -/
theorem ScopedConcreteEquationWorksSpine.contextual_equations_localSteps
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {eqSteps prodSteps retSteps : Nat}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    {rows : List (Atom × Bindings)} {works : List Spec.Eval.Steps.EquationWork}
    {bodyResults prodResults : ResultSet} {ctxProdResults : List Completed.Result}
    {finalResults : ResultSet} {ctxFinalResults : List Completed.Result}
    (spine : ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
      expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
      eqSteps prodSteps retSteps wRetStack cEqStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults) :
    RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
      (.work (.equations live scope ctxCall expected cFrameIn works),cEqStack)
      (.returning ctxFinalResults,cEqStack) := by
  induction spine with
  | nil => exact .single .equationsNil
  | cons_rejected => assumption
  | cons_ordinary_notReducible wRetStack cEqStack rhs selected wBMid work
      ctxProdVal cFrameMid remEqSteps remProdSteps remRetSteps remRows remWorks
      remBodyResults remProdResults remCtxProdResults remFinalResults
      remCtxFinalResults _eqReady _mergeFilterEq outBindingsEq unifyRel ctxProdEq
      bodyEraseEq _callEq _actMid _tailSpine ih =>
      have notPending : ¬Completed.FunctionPending policy ctxProdVal := by
        rintro ⟨⟨body, hErase⟩, _ready⟩
        have impossible : Atom.notReducible = .expression [.symbol "function", body] :=
          bodyEraseEq.symm.trans hErase
        cases impossible
      have returnStep :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.work (.returned live scope ctxCall expected ctxProdVal cFrameMid),
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.returning [(ctxCall, cFrameMid)],
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .returnRefused bodyEraseEq
      exact contextual_equations_leaf_localSteps space hostDispatch policy live scope
        ctxCall expected cFrameIn work remWorks ctxProdVal cFrameMid
        [(ctxCall, cFrameMid)] remCtxFinalResults cEqStack outBindingsEq unifyRel
        ctxProdEq notPending returnStep ih
  | cons_ordinary_stopped wRetStack cEqStack rhs wBodyVal selected wBMid work
      ctxProdVal cFrameMid remEqSteps remProdSteps remRetSteps remRows remWorks
      remBodyResults remProdResults remCtxProdResults remFinalResults
      remCtxFinalResults _eqReady _mergeFilterEq outBindingsEq unifyRel ctxProdEq
      bodyEraseEq notFunc _notRefused stopped _actMid _tailSpine ih =>
      have notPending : ¬Completed.FunctionPending policy ctxProdVal := by
        rintro ⟨⟨body, hErase⟩, _ready⟩
        exact notFunc body (bodyEraseEq.symm.trans hErase)
      have cStopped : IsEmptyOrErrorRel ctxProdVal.erase := by
        rw [bodyEraseEq, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
        exact stopped
      have returnStep :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.work (.returned live scope ctxCall expected ctxProdVal cFrameMid),
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.returning [(ctxProdVal, cFrameMid)],
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .returnStopped cStopped
      exact contextual_equations_leaf_localSteps space hostDispatch policy live scope
        ctxCall expected cFrameIn work remWorks ctxProdVal cFrameMid
        [(ctxProdVal, cFrameMid)] remCtxFinalResults cEqStack outBindingsEq unifyRel
        ctxProdEq notPending returnStep ih
  | cons_ordinary_evaluate wRetStack cEqStack rhs wBodyVal selected wBMid work
      ctxProdVal cFrameMid childSteps remEqSteps remProdSteps remRetSteps remRows
      remWorks remBodyResults remProdResults remCtxProdResults headFinalResults
      remFinalResults headCtxFinalResults remCtxFinalResults _eqReady _mergeFilterEq
      outBindingsEq unifyRel ctxProdEq bodyEraseEq notFunc notRefused clean actMid
      childRun _tailSpine ih =>
      have cLocal1 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.work (.equations live scope ctxCall expected cFrameIn (work :: remWorks)),cEqStack)
            (.work (.boundary (expected :: live) scope (some ctxCall.erase) .producer
              ctxProdVal cFrameMid),
              .boundaryBatch live scope none (.returned ctxCall expected) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) := by
        simpa only [ctxProdEq] using
          (RecursiveMachine.Contextual.LocalStep.equationsCons outBindingsEq unifyRel)
      have notPending : ¬Completed.FunctionPending policy ctxProdVal := by
        rintro ⟨⟨body,hErase⟩,_ready⟩
        exact notFunc body (bodyEraseEq.symm.trans hErase)
      have cLocal2 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.work (.boundary (expected :: live) scope (some ctxCall.erase) .producer
              ctxProdVal cFrameMid),
              .boundaryBatch live scope none (.returned ctxCall expected) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.returning [(ctxProdVal,cFrameMid)],
              .boundaryBatch live scope none (.returned ctxCall expected) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .boundaryProducerRaw notPending
      have cLocal3 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.returning [(ctxProdVal,cFrameMid)],
              .boundaryBatch live scope none (.returned ctxCall expected) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.work (.boundaryBatch live scope none (.returned ctxCall expected)
              [(ctxProdVal,cFrameMid)]),
              .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .boundaryBatch
      have cLocal4 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.work (.boundaryBatch live scope none (.returned ctxCall expected)
              [(ctxProdVal,cFrameMid)]),
              .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.work (.boundary live scope none (.returned ctxCall expected)
              ctxProdVal cFrameMid),
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .boundaryBatchCons
      have cLocal5 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.work (.boundary live scope none (.returned ctxCall expected)
              ctxProdVal cFrameMid),
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.work (.returned live scope ctxCall expected ctxProdVal cFrameMid),
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .boundaryReturned
      have cNotRefused : ctxProdVal.erase ≠ Atom.notReducible := by
        rw [bodyEraseEq]
        exact notRefused
      have cNotStopped : ¬IsEmptyOrErrorRel ctxProdVal.erase := by
        rw [bodyEraseEq,Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
        simp [clean]
      have cLocal6 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.work (.returned live scope ctxCall expected ctxProdVal cFrameMid),
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.work (.atom live scope ctxProdVal expected cFrameMid),
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .returnEvaluate cNotRefused cNotStopped
      have cLocal7 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.returning headCtxFinalResults,
              .append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.work (.boundaryBatch live scope none (.returned ctxCall expected) []),
              .prepend headCtxFinalResults ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .append
      have cLocal8 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.work (.boundaryBatch live scope none (.returned ctxCall expected) []),
              .prepend headCtxFinalResults ::
                .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.returning [],.prepend headCtxFinalResults ::
              .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) :=
        .boundaryBatchNil
      have cLocal9 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.returning [],.prepend headCtxFinalResults ::
              .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.returning headCtxFinalResults,
              .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack) := by
        simpa only [List.append_nil] using
          (RecursiveMachine.Contextual.LocalStep.prepend
            (selected := headCtxFinalResults) (results := []))
      have cLocal10 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.returning headCtxFinalResults,
              .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
            (.work (.equations live scope ctxCall expected cFrameIn remWorks),
              .prepend headCtxFinalResults :: cEqStack) :=
        .append
      have cLocal11 :
          RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
            (.returning remCtxFinalResults,.prepend headCtxFinalResults :: cEqStack)
            (.returning (headCtxFinalResults ++ remCtxFinalResults),cEqStack) :=
        .prepend
      have p1 := (((((Relation.ReflTransGen.single cLocal1).tail cLocal2).tail cLocal3).tail cLocal4).tail cLocal5).tail cLocal6
      have p2 := p1.trans childRun.contextual_steps
      have p3 := ((((p2.tail cLocal7).tail cLocal8).tail cLocal9).tail cLocal10).trans ih
      exact p3.tail cLocal11

/-- A concrete ordinary equation spine earns the complete `.call` block at its
actual return/equation stacks.  No stack-uniform recursive child execution is
assumed. -/
theorem ScopedConcreteEquationWorksSpine.call_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {eqSteps prodSteps retSteps : Nat}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {rows : List (Atom × Bindings)} {works : List Spec.Eval.Steps.EquationWork}
    {bodyResults prodResults : ResultSet} {ctxProdResults : List Completed.Result}
    {finalResults : ResultSet} {ctxFinalResults : List Completed.Result}
    (spine : ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
      expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
      eqSteps prodSteps retSteps wStack cStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults)
    (valEq : ctxCall.erase = expr)
    (notError : isErrorAtom expr = false)
    (notExec : ∀ op args,
      expr = .expression (op :: args) → dispatch.isExecutable op = false)
    (nonGrounded : NonGroundedCallRel hostDispatch ctxCall.erase)
    (notMin : minimalInstruction expr = false)
    (queryCovered :
      queryEquationsCovered (equationScope live expr expected wBIn)
        space expr (depth + 1) = true)
    (queryEq :
      queryEquationsAvoiding (equationScope live expr expected wBIn)
        space expr (depth + 1) = rows)
    (bodyNonempty : bodyResults ≠ [])
    (frontierEq :
      Spec.Eval.Steps.EquationFrontierRel space (expected :: live)
        ctxCall.erase cFrameIn.bindings works)
    (worksNonempty : works ≠ []) :
    let wStart : Configuration :=
      ⟨space, .work (.call expr expected wBIn (depth + 2) live),wStack,wEmitted⟩
    let wFinal : Configuration :=
      ⟨space, .returning finalResults,wStack,wEmitted⟩
    let cStart : RecursiveTasks.Contextual.Configuration :=
      ⟨space, .work (.call live scope ctxCall expected cFrameIn),cStack,cEmitted⟩
    let cFinal : RecursiveTasks.Contextual.Configuration :=
      ⟨space, .returning ctxFinalResults,cStack,cEmitted⟩
    List.Forall₂ ScopedResultRel finalResults ctxFinalResults ∧
    (∀ budget,
      (Checked.machine dispatch scopedTypes).run
        ((eqSteps + prodSteps + retSteps + 5) + budget) wStart =
      (Checked.machine dispatch scopedTypes).run budget wFinal) ∧
    (Checked.machine dispatch scopedTypes).run
      (eqSteps + prodSteps + retSteps + 5) wStart = ([],.exhausted wFinal) ∧
    RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
      (cStart.control,cStart.stack) (cFinal.control,cFinal.stack) := by
  intro wStart wFinal cStart cFinal
  have wStep1 :
      (Checked.machine dispatch scopedTypes).step wStart =
      some (.silent
        ⟨space, .work (.invocation (.ordinary expected) expr wBIn (depth + 2) live none),
          wStack,wEmitted⟩) := rfl
  have noPass : (InvocationMode.ordinary expected).errorPassthrough expr = false := by
    simpa [InvocationMode.errorPassthrough] using notError
  have wStep2 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.invocation (.ordinary expected) expr wBIn (depth + 2) live none),
          wStack,wEmitted⟩ =
      some (.silent
        ⟨space, .work (.equations expr expected wBIn (depth + 1) rows live),
          .producerResults (.ordinary expected) expr wBIn (depth + 1) live
            Atom.notReducible :: wStack,wEmitted⟩) := by
    have step := worker_invocation_query_step space dispatch (.ordinary expected)
      expr wBIn (depth + 1) live none wStack wEmitted
      noPass notExec notMin queryCovered
    simpa only [InvocationMode.expected,queryEq] using step
  have wStep3 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning bodyResults,
          .producerResults (.ordinary expected) expr wBIn (depth + 1) live
            Atom.notReducible :: wStack,wEmitted⟩ =
      some (.silent
        ⟨space, .work (.producerResults (.ordinary expected) expr wBIn (depth + 1)
            live Atom.notReducible bodyResults),wStack,wEmitted⟩) := rfl
  have wStep4 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.producerResults (.ordinary expected) expr wBIn (depth + 1)
            live Atom.notReducible bodyResults),wStack,wEmitted⟩ =
      some (.silent
        ⟨space, .work (.productions (depth + 1) bodyResults (expected :: live)
            (some expr) .emitted),
          .invocationReturn (.ordinary expected) expr (depth + 1) live :: wStack,
          wEmitted⟩) := by
    simp [Checked.machine,RecursiveMachine.Checked.guardMachine,Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady,RecursiveMachine.Checked.taskReady,
      FirstSuccessRecursiveExecution.machine,FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter,RecursiveMachine.enter,
      InvocationMode.pendingScope,bodyNonempty,Transition.relabel]
  have wStep5 :
      (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning prodResults,
          .invocationReturn (.ordinary expected) expr (depth + 1) live :: wStack,
          wEmitted⟩ =
      some (.silent
        ⟨space, .work (.returns expr expected (depth + 1) prodResults live),
          wStack,wEmitted⟩) := rfl
  have runAll : ∀ budget,
      (Checked.machine dispatch scopedTypes).run
        ((eqSteps + prodSteps + retSteps + 5) + budget) wStart =
      (Checked.machine dispatch scopedTypes).run budget wFinal := by
    intro budget
    calc
      (Checked.machine dispatch scopedTypes).run
          ((eqSteps + prodSteps + retSteps + 5) + budget) wStart =
        (Checked.machine dispatch scopedTypes).run
          (((eqSteps + (((prodSteps + ((retSteps + budget) + 1)) + 1) + 1)) + 1) + 1)
          wStart := by
            rw [show (eqSteps + prodSteps + retSteps + 5) + budget =
              ((eqSteps + (((prodSteps + ((retSteps + budget) + 1)) + 1) + 1)) + 1) + 1
              by omega]
      _ = (Checked.machine dispatch scopedTypes).run
            ((eqSteps + (((prodSteps + ((retSteps + budget) + 1)) + 1) + 1)) + 1) _ :=
            (Checked.machine dispatch scopedTypes).run_succ_silent wStep1
      _ = (Checked.machine dispatch scopedTypes).run
            (eqSteps + (((prodSteps + ((retSteps + budget) + 1)) + 1) + 1)) _ :=
            (Checked.machine dispatch scopedTypes).run_succ_silent wStep2
      _ = (Checked.machine dispatch scopedTypes).run
            (((prodSteps + ((retSteps + budget) + 1)) + 1) + 1) _ :=
            spine.equations_run
              (.producerResults (.ordinary expected) expr wBIn (depth + 1) live
                Atom.notReducible :: wStack)
              (((prodSteps + ((retSteps + budget) + 1)) + 1) + 1)
      _ = (Checked.machine dispatch scopedTypes).run
            ((prodSteps + ((retSteps + budget) + 1)) + 1) _ :=
            (Checked.machine dispatch scopedTypes).run_succ_silent wStep3
      _ = (Checked.machine dispatch scopedTypes).run
            (prodSteps + ((retSteps + budget) + 1)) _ :=
            (Checked.machine dispatch scopedTypes).run_succ_silent wStep4
      _ = (Checked.machine dispatch scopedTypes).run ((retSteps + budget) + 1) _ :=
            spine.productions_run
              (.invocationReturn (.ordinary expected) expr (depth + 1) live :: wStack)
              ((retSteps + budget) + 1)
      _ = (Checked.machine dispatch scopedTypes).run (retSteps + budget) _ :=
            (Checked.machine dispatch scopedTypes).run_succ_silent wStep5
      _ = (Checked.machine dispatch scopedTypes).run budget wFinal :=
            spine.returns_run budget
  have wRun0 :
      (Checked.machine dispatch scopedTypes).run
        (eqSteps + prodSteps + retSteps + 5) wStart = ([],.exhausted wFinal) :=
    (runAll 0).trans rfl
  have notErrRel : ¬IsErrorRel ctxCall.erase := by
    rw [valEq,Conformance.isErrorRel_iff_isErrorAtom]
    simp [notError]
  have cLocal1 :
      RecursiveMachine.Contextual.LocalStep space hostDispatch Completed.scopedLookup policy
        (.work (.call live scope ctxCall expected cFrameIn),cStack)
        (.work (.equations live scope ctxCall expected cFrameIn works),cStack) :=
    .callEquations notErrRel nonGrounded frontierEq worksNonempty
  have cLocalSteps :
      RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
        (cStart.control,cStart.stack) (cFinal.control,cFinal.stack) :=
    (Relation.ReflTransGen.single cLocal1).trans spine.contextual_equations_localSteps
  have finalRel := spine.finalResults_forall2
  exact ⟨finalRel,runAll,wRun0,cLocalSteps⟩

/-- The selected function pipeline is a non-recursive composition boundary.
Once its operator, argument spine, and equation spine have been earned, the
entry prefix and caller publication assemble them into one concrete task run. -/
theorem ScopedTaskRun.selected_function_of_parts
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator opVal expected : Atom) (arguments retVals : List Atom)
    (ctxVal ctxOp ctxOpVal : Entry.Value)
    (ctxArgs ctxRetVals : List Entry.Value)
    (wB wBSelected wBHead wBArgs : Bindings)
    (cFrame cFrameSelected cFrameHead cFrameArgs : Completed.Frame)
    (signature : SelectedTypePolicy) (candidates : List Atom)
    (rows : List (Atom × Bindings))
    (works : List Spec.Eval.Steps.EquationWork)
    (bodyResults prodResults finalResults : ResultSet)
    (ctxProdResults ctxFinalResults : List Completed.Result)
    (fuel opSteps argSteps eqSteps prodSteps retSteps readDepth : Nat)
    (live : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (readiness : Entry.Status)
    (entry : ScopedSelectedFunctionEntry space policy operator arguments opVal expected
      wB wBSelected fuel live scope ctxVal ctxOp ctxArgs cFrame cFrameSelected
      readiness signature candidates wStack wEmitted)
    (callAdmission : ScopedEquationCallAdmission space dispatch hostDispatch
      (.expression (opVal :: retVals)) (Completed.invocationReturnType signature)
      wBArgs fuel live (.expression .active (ctxOpVal :: ctxRetVals)) cFrameArgs
      rows works bodyResults finalResults readDepth)
    (opRun :
      let resultType := Completed.invocationReturnType signature
      let wCallStack : List RecursiveTasks.Frame :=
        .calls resultType (fuel + 2) live ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
      let cCallStack : List RecursiveTasks.Contextual.Continuation :=
        .calls live scope resultType ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
      ScopedTaskRun space dispatch hostDispatch policy
        (.atom operator signature.functionType wBSelected (fuel + 1)
          (signature.functionType :: arguments ++ (resultType :: live)))
        (.atom
          (signature.functionType :: ctxArgs.map Entry.Value.erase ++ (resultType :: live))
          (scope ++ expectedApplicationScope
            (.expression ((ctxOp :: ctxArgs).map Entry.Value.erase)) expected)
          ctxOp signature.functionType cFrameSelected)
        (.heads signature.functionType arguments (fuel + 1) (resultType :: live) :: wCallStack)
        (.functionHeads (resultType :: live) scope
          (ctxArgs.zip signature.argumentTypes) :: cCallStack)
        wEmitted cEmitted opSteps
        [(opVal, wBHead)] [(ctxOpVal, cFrameHead)])
    (argsRun :
      let resultType := Completed.invocationReturnType signature
      let wCallStack : List RecursiveTasks.Frame :=
        .calls resultType (fuel + 2) live ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
      let cCallStack : List RecursiveTasks.Contextual.Continuation :=
        .calls live scope resultType ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
      ScopedTaskRun space dispatch hostDispatch policy
        (.args arguments signature.argumentTypes wBHead (fuel + 1)
          (opVal :: resultType :: live))
        (.arguments (opVal :: resultType :: live) scope
          (ctxArgs.zip signature.argumentTypes) cFrameHead)
        (.functionTail opVal ::
          .append (.heads signature.functionType arguments (fuel + 1) []
            (resultType :: live)) :: wCallStack)
        (.functionAssemble ctxOpVal ::
          .append (.functionBranches (resultType :: live) scope
            (ctxArgs.zip signature.argumentTypes) []) :: cCallStack)
        wEmitted cEmitted argSteps
        [(argumentPacket retVals, wBArgs)]
        [(Entry.Value.argumentPacket ctxRetVals, cFrameArgs)])
    (eqSpine :
      let resultType := Completed.invocationReturnType signature
      let outAtom : Atom := .expression (opVal :: retVals)
      let ctxCall : Entry.Value := .expression .active (ctxOpVal :: ctxRetVals)
      let wDrainStack : List RecursiveTasks.Frame :=
        .append (.calls resultType (fuel + 2) [] live) ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
      let cDrainStack : List RecursiveTasks.Contextual.Continuation :=
        .append (.calls live scope resultType []) ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
      ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
        outAtom resultType wBArgs fuel live scope ctxCall cFrameArgs wEmitted cEmitted
        eqSteps prodSteps retSteps wDrainStack cDrainStack rows works
        bodyResults prodResults ctxProdResults finalResults ctxFinalResults)
    (source :
      Completed.AtomRel space hostDispatch Completed.scopedLookup live scope
        ctxVal expected cFrame
        ((completedSuccessPriority
          (ctxFinalResults.map (Completed.readResult policy))).map
            (Completed.publishResult policy (.expression (operator :: arguments))))
        (policy := policy)) :
    let expr := Atom.expression (operator :: arguments)
    let cSelected := completedSuccessPriority
      (ctxFinalResults.map (Completed.readResult policy))
    let cPublished := cSelected.map (Completed.publishResult policy expr)
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom expr expected wB (fuel + 4) live)
      (.atom live scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted
      (opSteps + argSteps + eqSteps + prodSteps + retSteps + 25)
      (successPriority finalResults) cPublished := by
  intro expr cSelected cPublished
  dsimp only at opRun argsRun eqSpine source
  let resultType := Completed.invocationReturnType signature
  let outAtom : Atom := .expression (opVal :: retVals)
  let ctxCall : Entry.Value := .expression .active (ctxOpVal :: ctxRetVals)
  let wInvAppend : RecursiveTasks.Frame :=
    .append (.bindingAlternatives expr signature.functionType resultType
      (fuel + 2) [] live)
  let wCallStack : List RecursiveTasks.Frame :=
    .calls resultType (fuel + 2) live :: wInvAppend :: .filter :: wStack
  let wOperatorStack : List RecursiveTasks.Frame :=
    .heads signature.functionType arguments (fuel + 1) (resultType :: live) :: wCallStack
  let wArgsStack : List RecursiveTasks.Frame :=
    .functionTail opVal ::
      .append (.heads signature.functionType arguments (fuel + 1) []
        (resultType :: live)) :: wCallStack
  let wDrainStack : List RecursiveTasks.Frame :=
    .append (.calls resultType (fuel + 2) [] live) ::
      wInvAppend :: .filter :: wStack
  have entryBlock := scoped_selected_function_entry_run
    space dispatch hostDispatch policy operator arguments expected
    wB wBSelected (fuel + 2) live scope ctxVal ctxOp ctxArgs cFrame cFrameSelected
    readiness signature candidates wStack cStack wEmitted cEmitted
    entry.entry_ready entry.read_shape entry.operator_erase
    entry.input_not_stopped entry.expected_not_atom entry.expected_not_expression
    (by simpa only [show fuel + 2 + 1 = fuel + 3 by omega] using entry.candidate_eq)
    entry.selection_ready entry.worker_selected entry.contextual_selected
  dsimp only at entryBlock
  have callRun := eqSpine.call_run
    callAdmission.value_erase callAdmission.not_error callAdmission.not_executable
    callAdmission.non_grounded callAdmission.not_minimal callAdmission.query_covered
    callAdmission.query_eq callAdmission.bodies_nonempty callAdmission.frontier
    callAdmission.works_nonempty
  have finalRel := callRun.1
  have readRel : List.Forall₂ ScopedResultRel finalResults
      (ctxFinalResults.map (Completed.readResult policy)) :=
    ScopedResultRel.forall2_materialized_readResult_stable policy finalRel readDepth
      callAdmission.returned_covered callAdmission.returned_stable
  have publishedRel : List.Forall₂ ScopedResultRel
      (successPriority finalResults) cPublished :=
    ScopedResultRel.forall2_publishResult policy expr
      (ScopedResultRel.forall2_successPriority readRel)
  have wStepInv : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.bindingAlternatives expr signature.functionType resultType
        (fuel + 2) [wBSelected] live), .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.func expr signature.functionType wBSelected
          (fuel + 2) (resultType :: live)), wCallStack, wEmitted⟩) := rfl
  have wStepFunc : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.func expr signature.functionType wBSelected
        (fuel + 2) (resultType :: live)), wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.atom operator signature.functionType wBSelected
          (fuel + 1) (signature.functionType :: arguments ++ (resultType :: live))),
          wOperatorStack, wEmitted⟩) := rfl
  have wStepHeads : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [(opVal, wBHead)], wOperatorStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.heads signature.functionType arguments (fuel + 1)
          [(opVal, wBHead)] (resultType :: live)), wCallStack, wEmitted⟩) := rfl
  have wStepArgs : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.heads signature.functionType arguments (fuel + 1)
        [(opVal, wBHead)] (resultType :: live)), wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.args arguments signature.argumentTypes wBHead
          (fuel + 1) (opVal :: resultType :: live)), wArgsStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      entry.operator_not_stopped, entry.argument_types_eq, wArgsStack, wCallStack,
      wInvAppend, Transition.relabel]
  have wStepFunctionTail : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [(argumentPacket retVals, wBArgs)], wArgsStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [(outAtom, wBArgs)],
          .append (.heads signature.functionType arguments (fuel + 1) []
            (resultType :: live)) :: wCallStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      RecursiveMachine.resume, RecursiveTasks.functionTail, argumentPacket,
      argumentsSucceeded, unpackArguments, argumentValues,
      outAtom, wArgsStack, Transition.relabel]
  have wStepAppendHeads : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [(outAtom, wBArgs)],
        .append (.heads signature.functionType arguments (fuel + 1) []
          (resultType :: live)) :: wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.heads signature.functionType arguments (fuel + 1) []
          (resultType :: live)), .prepend [(outAtom, wBArgs)] :: wCallStack,
          wEmitted⟩) := rfl
  have wStepHeadsNil : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.heads signature.functionType arguments (fuel + 1) []
        (resultType :: live)), .prepend [(outAtom, wBArgs)] :: wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [], .prepend [(outAtom, wBArgs)] :: wCallStack,
          wEmitted⟩) := rfl
  have wStepPrependHead : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [], .prepend [(outAtom, wBArgs)] :: wCallStack, wEmitted⟩ =
      some (.silent ⟨space, .returning [(outAtom, wBArgs)], wCallStack, wEmitted⟩) := rfl
  have wStepCalls : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [(outAtom, wBArgs)], wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.calls resultType (fuel + 2) [(outAtom, wBArgs)] live),
          wInvAppend :: .filter :: wStack, wEmitted⟩) := rfl
  have wStepCallsCons : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.calls resultType (fuel + 2) [(outAtom, wBArgs)] live),
        wInvAppend :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.call outAtom resultType wBArgs (fuel + 2) live),
          wDrainStack, wEmitted⟩) := rfl
  have wStepDrain1 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning finalResults, wDrainStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.calls resultType (fuel + 2) [] live),
          .prepend finalResults :: wInvAppend :: .filter :: wStack, wEmitted⟩) := rfl
  have wStepDrain2 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.calls resultType (fuel + 2) [] live),
        .prepend finalResults :: wInvAppend :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [],
          .prepend finalResults :: wInvAppend :: .filter :: wStack, wEmitted⟩) := rfl
  have wStepDrain3 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [],
        .prepend finalResults :: wInvAppend :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning finalResults, wInvAppend :: .filter :: wStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
  have wStepDrain4 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning finalResults, wInvAppend :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.bindingAlternatives expr signature.functionType resultType
          (fuel + 2) [] live), .prepend finalResults :: .filter :: wStack,
          wEmitted⟩) := rfl
  have wStepDrain5 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.bindingAlternatives expr signature.functionType resultType
        (fuel + 2) [] live), .prepend finalResults :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [], .prepend finalResults :: .filter :: wStack,
          wEmitted⟩) := rfl
  have wStepDrain6 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [], .prepend finalResults :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning finalResults, .filter :: wStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
  have wStepPublish : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning finalResults, .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning (successPriority finalResults), wStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
  have afterEntryRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run
        ((opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 17) + budget)
          ⟨space, .work (.bindingAlternatives expr signature.functionType resultType
            (fuel + 2) [wBSelected] live), .filter :: wStack, wEmitted⟩ =
      (Checked.machine dispatch scopedTypes).run budget
          ⟨space, .returning (successPriority finalResults), wStack, wEmitted⟩ := by
    intro budget
    calc
      (Checked.machine dispatch scopedTypes).run
          ((opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 17) + budget) _ =
        (Checked.machine dispatch scopedTypes).run
          (opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 16 + budget) _ := by
            rw [show (opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 17) + budget =
              (opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 16 + budget) + 1
              by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepInv
      _ = (Checked.machine dispatch scopedTypes).run
          (opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 15 + budget) _ := by
            rw [show opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 16 + budget =
              (opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 15 + budget) + 1
              by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepFunc
      _ = (Checked.machine dispatch scopedTypes).run
          (argSteps + (eqSteps + prodSteps + retSteps + 5) + 15 + budget) _ :=
            by
              simpa only [resultType, wOperatorStack, wCallStack, wInvAppend,
                Nat.add_assoc] using
                opRun.worker_run (argSteps + (eqSteps + prodSteps + retSteps + 5) + 15 + budget)
      _ = (Checked.machine dispatch scopedTypes).run
          (argSteps + (eqSteps + prodSteps + retSteps + 5) + 14 + budget) _ := by
            rw [show argSteps + (eqSteps + prodSteps + retSteps + 5) + 15 + budget =
              (argSteps + (eqSteps + prodSteps + retSteps + 5) + 14 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepHeads
      _ = (Checked.machine dispatch scopedTypes).run
          (argSteps + (eqSteps + prodSteps + retSteps + 5) + 13 + budget) _ := by
            rw [show argSteps + (eqSteps + prodSteps + retSteps + 5) + 14 + budget =
              (argSteps + (eqSteps + prodSteps + retSteps + 5) + 13 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepArgs
      _ = (Checked.machine dispatch scopedTypes).run
          ((eqSteps + prodSteps + retSteps + 5) + 13 + budget) _ :=
            by
              simpa only [resultType, wArgsStack, wCallStack, wInvAppend,
                Nat.add_assoc] using
                argsRun.worker_run ((eqSteps + prodSteps + retSteps + 5) + 13 + budget)
      _ = (Checked.machine dispatch scopedTypes).run
          ((eqSteps + prodSteps + retSteps + 5) + 12 + budget) _ := by
            rw [show (eqSteps + prodSteps + retSteps + 5) + 13 + budget =
              ((eqSteps + prodSteps + retSteps + 5) + 12 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepFunctionTail
      _ = (Checked.machine dispatch scopedTypes).run
          ((eqSteps + prodSteps + retSteps + 5) + 11 + budget) _ := by
            rw [show (eqSteps + prodSteps + retSteps + 5) + 12 + budget =
              ((eqSteps + prodSteps + retSteps + 5) + 11 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepAppendHeads
      _ = (Checked.machine dispatch scopedTypes).run
          ((eqSteps + prodSteps + retSteps + 5) + 10 + budget) _ := by
            rw [show (eqSteps + prodSteps + retSteps + 5) + 11 + budget =
              ((eqSteps + prodSteps + retSteps + 5) + 10 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepHeadsNil
      _ = (Checked.machine dispatch scopedTypes).run
          ((eqSteps + prodSteps + retSteps + 5) + 9 + budget) _ := by
            rw [show (eqSteps + prodSteps + retSteps + 5) + 10 + budget =
              ((eqSteps + prodSteps + retSteps + 5) + 9 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepPrependHead
      _ = (Checked.machine dispatch scopedTypes).run
          ((eqSteps + prodSteps + retSteps + 5) + 8 + budget) _ := by
            rw [show (eqSteps + prodSteps + retSteps + 5) + 9 + budget =
              ((eqSteps + prodSteps + retSteps + 5) + 8 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepCalls
      _ = (Checked.machine dispatch scopedTypes).run
          ((eqSteps + prodSteps + retSteps + 5) + 7 + budget) _ := by
            rw [show (eqSteps + prodSteps + retSteps + 5) + 8 + budget =
              ((eqSteps + prodSteps + retSteps + 5) + 7 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepCallsCons
      _ = (Checked.machine dispatch scopedTypes).run (7 + budget) _ :=
            by
              simpa only [resultType, outAtom, ctxCall, wDrainStack, wInvAppend,
                Nat.add_assoc] using callRun.2.1 (7 + budget)
      _ = (Checked.machine dispatch scopedTypes).run (6 + budget) _ := by
            rw [show 7 + budget = (6 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain1
      _ = (Checked.machine dispatch scopedTypes).run (5 + budget) _ := by
            rw [show 6 + budget = (5 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain2
      _ = (Checked.machine dispatch scopedTypes).run (4 + budget) _ := by
            rw [show 5 + budget = (4 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain3
      _ = (Checked.machine dispatch scopedTypes).run (3 + budget) _ := by
            rw [show 4 + budget = (3 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain4
      _ = (Checked.machine dispatch scopedTypes).run (2 + budget) _ := by
            rw [show 3 + budget = (2 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain5
      _ = (Checked.machine dispatch scopedTypes).run (1 + budget) _ := by
            rw [show 2 + budget = (1 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain6
      _ = (Checked.machine dispatch scopedTypes).run budget _ := by
            rw [Nat.add_comm 1 budget]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepPublish
  have workerRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run
        ((opSteps + argSteps + eqSteps + prodSteps + retSteps + 25) + budget)
          ⟨space, .work (.atom expr expected wB (fuel + 4) live),
            wStack, wEmitted⟩ =
      (Checked.machine dispatch scopedTypes).run budget
          ⟨space, .returning (successPriority finalResults), wStack, wEmitted⟩ := by
    intro budget
    rw [show (opSteps + argSteps + eqSteps + prodSteps + retSteps + 25) + budget =
        3 + ((opSteps + argSteps + (eqSteps + prodSteps + retSteps + 5) + 17) + budget)
        by omega,
      entryBlock.2.1 _, afterEntryRun budget]
  exact ⟨by omega, publishedRel, workerRun,
    RecursiveExecution.Contextual.atom_complete source cStack⟩

/-! ### Earned recursive proof objects

Only the three genuinely recursive edges are mutual: atom evaluation, a
left-to-right argument spine, and an equation-result spine.  Function entry and
call publication remain the non-recursive composition law above. -/

/-- Open-recursion signature for structural atom branches supplied by a
separate component.  Machine executions are deliberately absent. -/
abbrev ScopedAtomStepPred : Type :=
  Nat → List Atom → List Atom → List String →
  Atom → Entry.Value → Atom → Bindings → Completed.Frame →
  List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation →
  Nat → ResultSet → List Completed.Result → Prop

/-- One locally selected atom-extension relation.  Making it a fixed instance
parameter lets all existing derivation applications retain their syntax while
ranked recursive profiles install a different local instance. -/
class ScopedAtomExtension where
  pred : ScopedAtomStepPred

/-- Default profile: no external atom branch. -/
def ScopedNoExtraAtom : ScopedAtomStepPred :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => False

instance scopedAtomExtensionNoExtra : ScopedAtomExtension where
  pred := ScopedNoExtraAtom

/-- Source and checked-worker realization laws for the locally selected atom
extension.  These are component laws, separate from the structural predicate. -/
class ScopedAtomExtensionLaws
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension] : Prop where
  source : ∀ {fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults},
    extension.pred fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults →
    Completed.AtomRel space hostDispatch Completed.scopedLookup cLive scope
      ctxVal expected cFrame cResults (policy := policy)
  run : ∀ {fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults},
    extension.pred fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults →
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom value expected wB fuel wLive)
      (.atom cLive scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted steps wResults cResults

/-- The empty extension discharges both component laws by contradiction. -/
instance scopedAtomExtensionNoExtraLaws
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedAtomExtensionLaws space dispatch hostDispatch policy wEmitted cEmitted where
  source branch := False.elim branch
  run branch := False.elim branch

mutual

/-- Admitted scoped atom executions.  Every constructor records semantic and
coverage evidence; none accepts a worker run or contextual step path. -/
inductive ScopedAtomDerivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension] :
    Nat → List Atom → List Atom → List String →
    Atom → Entry.Value → Atom → Bindings → Completed.Frame →
    List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation →
    Nat → ResultSet → List Completed.Result → Prop where
  | empty_or_error
      (depth : Nat) (wLive cLive : List Atom) (scope : List String)
      (value expected : Atom) (ctxVal : Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (entryReady : ScopedAtomEntryReady policy value ctxVal cFrame)
      (stopped : isEmptyOrError value = true)
      (actRel : ScopedActivationRel wB cFrame) :
      ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
        (depth + 1) wLive cLive scope value ctxVal expected wB cFrame wStack cStack
        1 [(value, wB)] [(cFrame.read policy ctxVal, cFrame)]
  | type_pass
      (depth : Nat) (wLive cLive : List Atom) (scope : List String)
      (value expected : Atom) (ctxVal : Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (entryReady : ScopedAtomEntryReady policy value ctxVal cFrame)
      (notStopped : isEmptyOrError value = false)
      (typePass : expected = Atom.atomType ∨ expected = getMetaType value ∨
        getMetaType value = Atom.variableType)
      (actRel : ScopedActivationRel wB cFrame) :
      ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
        (depth + 1) wLive cLive scope value ctxVal expected wB cFrame wStack cStack
        1 [(value, wB)] [(cFrame.read policy ctxVal, cFrame)]
  | cast
      (depth : Nat) (wLive cLive : List Atom) (scope : List String)
      (value expected : Atom) (ctxVal : Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (wResults rawResults : ResultSet)
      (cResults : List Completed.Result)
      (admission : ScopedCastAdmission space policy value expected ctxVal wB cFrame
        depth wLive cLive scope wStack wEmitted wResults rawResults cResults) :
      ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
        (depth + 1) wLive cLive scope value ctxVal expected wB cFrame wStack cStack
        1 wResults cResults
  | selection_failed
      (operator expected : Atom) (arguments : List Atom)
      (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (fuel : Nat) (live : List Atom) (scope : List String)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (readiness : Entry.Status) (candidates errors : List Atom)
      (admission : ScopedSelectionFailureAdmission space policy operator arguments expected
        wB fuel live scope ctxVal ctxOp ctxArgs cFrame readiness candidates errors
        wStack wEmitted) :
      ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
        (fuel + 2) live live scope (.expression (operator :: arguments)) ctxVal expected
        wB cFrame wStack cStack 4
        (successPriority (errors.map fun error => (error, wB)))
        ((completedSuccessPriority
          ((Completed.diagnosticResults errors cFrame).map
            (Completed.readResult policy))).map
          (Completed.publishResult policy (.expression (operator :: arguments))))
  | extra
      (fuel : Nat) (wLive cLive : List Atom) (scope : List String)
      (value : Atom) (ctxVal : Entry.Value) (expected : Atom)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (steps : Nat) (wResults : ResultSet) (cResults : List Completed.Result)
      (entryReady : ScopedAtomEntryReady policy value ctxVal cFrame)
      (actRel : ScopedActivationRel wB cFrame)
      (branch : extension.pred fuel wLive cLive scope value ctxVal expected wB cFrame
        wStack cStack steps wResults cResults) :
      ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
        fuel wLive cLive scope value ctxVal expected wB cFrame wStack cStack
        steps wResults cResults
  | selected_function
      (operator opVal expected : Atom) (arguments retVals : List Atom)
      (ctxVal ctxOp ctxOpVal : Entry.Value)
      (ctxArgs ctxRetVals : List Entry.Value)
      (wB wBSelected wBHead wBArgs : Bindings)
      (cFrame cFrameSelected cFrameHead cFrameArgs : Completed.Frame)
      (signature : SelectedTypePolicy) (candidates : List Atom)
      (rows : List (Atom × Bindings))
      (works : List Spec.Eval.Steps.EquationWork)
      (bodyResults prodResults finalResults : ResultSet)
      (ctxProdResults ctxFinalResults : List Completed.Result)
      (fuel opSteps argSteps eqSteps prodSteps retSteps readDepth : Nat)
      (live : List Atom) (scope : List String)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (readiness : Entry.Status)
      (entry : ScopedSelectedFunctionEntry space policy operator arguments opVal expected
        wB wBSelected fuel live scope ctxVal ctxOp ctxArgs cFrame cFrameSelected
        readiness signature candidates wStack wEmitted)
      (callAdmission : ScopedEquationCallAdmission space dispatch hostDispatch
        (.expression (opVal :: retVals)) (Completed.invocationReturnType signature)
        wBArgs fuel live (.expression .active (ctxOpVal :: ctxRetVals)) cFrameArgs
        rows works bodyResults finalResults readDepth)
      (operatorResultRel : ScopedResultRel (opVal, wBHead) (ctxOpVal, cFrameHead))
      (operatorDerivation :
        let resultType := Completed.invocationReturnType signature
        let wCallStack : List RecursiveTasks.Frame :=
          .calls resultType (fuel + 2) live ::
            .append (.bindingAlternatives (.expression (operator :: arguments))
              signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
        let cCallStack : List RecursiveTasks.Contextual.Continuation :=
          .calls live scope resultType ::
            .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
        ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
          (fuel + 1)
          (signature.functionType :: arguments ++ (resultType :: live))
          (signature.functionType :: ctxArgs.map Entry.Value.erase ++ (resultType :: live))
          (scope ++ expectedApplicationScope
            (.expression ((ctxOp :: ctxArgs).map Entry.Value.erase)) expected)
          operator ctxOp signature.functionType wBSelected cFrameSelected
          (.heads signature.functionType arguments (fuel + 1) (resultType :: live) :: wCallStack)
          (.functionHeads (resultType :: live) scope
            (ctxArgs.zip signature.argumentTypes) :: cCallStack)
          opSteps [(opVal, wBHead)] [(ctxOpVal, cFrameHead)])
      (argumentsDerivation :
        let resultType := Completed.invocationReturnType signature
        let wCallStack : List RecursiveTasks.Frame :=
          .calls resultType (fuel + 2) live ::
            .append (.bindingAlternatives (.expression (operator :: arguments))
              signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
        let cCallStack : List RecursiveTasks.Contextual.Continuation :=
          .calls live scope resultType ::
            .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
        ScopedArgsDerivation space dispatch hostDispatch policy wEmitted cEmitted scope
          (fuel + 1) argSteps (opVal :: resultType :: live)
          arguments signature.argumentTypes (ctxArgs.zip signature.argumentTypes)
          retVals ctxRetVals wBHead cFrameHead wBArgs cFrameArgs
          (.functionTail opVal ::
            .append (.heads signature.functionType arguments (fuel + 1) []
              (resultType :: live)) :: wCallStack)
          (.functionAssemble ctxOpVal ::
            .append (.functionBranches (resultType :: live) scope
              (ctxArgs.zip signature.argumentTypes) []) :: cCallStack))
      (equationDerivation :
        let resultType := Completed.invocationReturnType signature
        let outAtom : Atom := .expression (opVal :: retVals)
        let ctxCall : Entry.Value := .expression .active (ctxOpVal :: ctxRetVals)
        let wDrainStack : List RecursiveTasks.Frame :=
          .append (.calls resultType (fuel + 2) [] live) ::
            .append (.bindingAlternatives (.expression (operator :: arguments))
              signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
        let cDrainStack : List RecursiveTasks.Contextual.Continuation :=
          .append (.calls live scope resultType []) ::
            .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
        ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
          outAtom resultType wBArgs fuel live scope ctxCall cFrameArgs
          eqSteps prodSteps retSteps wDrainStack cDrainStack rows works
          bodyResults prodResults ctxProdResults finalResults ctxFinalResults) :
      ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
        (fuel + 4) live live scope (.expression (operator :: arguments)) ctxVal expected
        wB cFrame wStack cStack
        (opSteps + argSteps + eqSteps + prodSteps + retSteps + 25)
        (successPriority finalResults)
        ((completedSuccessPriority (ctxFinalResults.map (Completed.readResult policy))).map
          (Completed.publishResult policy (.expression (operator :: arguments))))

/-- Earned left-to-right argument evaluation. -/
inductive ScopedArgsDerivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension] :
    List String → Nat → Nat → List Atom → List Atom → List Atom →
    List Completed.ArgumentRequest → List Atom → List Entry.Value →
    Bindings → Completed.Frame → Bindings → Completed.Frame →
    List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation → Prop where
  | nil
      (scope : List String) (fuel : Nat) (live : List Atom)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (actRel : ScopedActivationRel wB cFrame)
      :
      ScopedArgsDerivation space dispatch hostDispatch policy wEmitted cEmitted scope
        (fuel + 1) 1 live [] [] [] [] [] wB cFrame wB cFrame wStack cStack
  | cons
      (scope : List String) (fuel headSteps tailSteps : Nat) (live : List Atom)
      (argVal retVal expectedType : Atom)
      (remArgs remTypes retVals : List Atom)
      (ctxArg ctxRet : Entry.Value)
      (remReqs : List Completed.ArgumentRequest)
      (ctxRetVals : List Entry.Value)
      (wBIn wBMid wBOut : Bindings)
      (cFrameIn cFrameMid cFrameOut : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (argEq : ctxArg.erase = argVal)
      (retEq : ctxRet.erase = retVal)
      (remEq : (remReqs.map Prod.fst).map Entry.Value.erase = remArgs)
      (typesEq : remReqs.map Prod.snd = remTypes)
      (tailRetEq : ctxRetVals.map Entry.Value.erase = retVals)
      (notChangedStopped : (retVal != argVal && isEmptyOrError retVal) = false)
      (actIn : ScopedActivationRel wBIn cFrameIn)
      (actMid : ScopedActivationRel wBMid cFrameMid)
      (actOut : ScopedActivationRel wBOut cFrameOut)
      (headDerivation :
        ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
          fuel (remArgs ++ remTypes ++ live) (Completed.argumentScope remReqs ++ live)
          scope argVal ctxArg expectedType wBIn cFrameIn
          (.argumentHeads argVal remArgs remTypes fuel live :: wStack)
          (.arguments live scope ctxArg remReqs :: cStack)
          headSteps [(retVal, wBMid)] [(ctxRet, cFrameMid)])
      (tailDerivation :
        ScopedArgsDerivation space dispatch hostDispatch policy wEmitted cEmitted scope
          fuel tailSteps (retVal :: live) remArgs remTypes remReqs retVals ctxRetVals
          wBMid cFrameMid wBOut cFrameOut
          (.argumentTail retVal ::
            .append (.argumentHeads argVal remArgs remTypes fuel [] live) :: wStack)
          (.argumentTail ctxRet ::
            .append (.argumentBranches live scope ctxArg remReqs []) :: cStack)) :
      ScopedArgsDerivation space dispatch hostDispatch policy wEmitted cEmitted scope
        (fuel + 1) (headSteps + tailSteps + 7) live
        (argVal :: remArgs) (expectedType :: remTypes)
        ((ctxArg, expectedType) :: remReqs)
        (retVal :: retVals) (ctxRet :: ctxRetVals)
        wBIn cFrameIn wBOut cFrameOut wStack cStack

/-- Earned ordinary equation rows at the concrete return and contextual
equation stacks. -/
inductive ScopedEquationDerivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension] :
    Atom → Atom → Bindings → Nat → List Atom → List String →
    Entry.Value → Completed.Frame →
    Nat → Nat → Nat →
    List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation →
    List (Atom × Bindings) → List Spec.Eval.Steps.EquationWork →
    ResultSet → ResultSet → List Completed.Result →
    ResultSet → List Completed.Result → Prop where
  | nil (wRetStack : List RecursiveTasks.Frame)
      (expr expected : Atom) (wBIn : Bindings) (depth : Nat)
      (live : List Atom) (scope : List String)
      (ctxCall : Entry.Value) (cFrameIn : Completed.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation) :
      ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
        expr expected wBIn depth live scope ctxCall cFrameIn
        1 1 1 wRetStack cEqStack [] [] [] [] [] [] []
  | cons_rejected
      (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation)
      (expr expected : Atom) (wBIn : Bindings) (depth : Nat)
      (live : List Atom) (scope : List String)
      (ctxCall : Entry.Value) (cFrameIn : Completed.Frame)
      (rhs : Atom) (selected : Bindings)
      (remEqSteps remProdSteps remRetSteps : Nat)
      (remRows : List (Atom × Bindings))
      (works : List Spec.Eval.Steps.EquationWork)
      (bodyResults prodResults : ResultSet)
      (ctxProdResults : List Completed.Result)
      (finalResults : ResultSet)
      (ctxFinalResults : List Completed.Result)
      (eqReady :
        (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
          (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
            (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
      (mergeFilterEmpty :
        ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) = [])
      (tailDerivation :
        ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
          expr expected wBIn depth live scope ctxCall cFrameIn
          remEqSteps remProdSteps remRetSteps wRetStack cEqStack remRows works
          bodyResults prodResults ctxProdResults finalResults ctxFinalResults) :
      ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
        expr expected wBIn depth live scope ctxCall cFrameIn
        (remEqSteps + 3) remProdSteps remRetSteps wRetStack cEqStack
        ((rhs, selected) :: remRows) works bodyResults prodResults ctxProdResults
        finalResults ctxFinalResults
  | cons_ordinary_notReducible
      (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation)
      (expr expected : Atom) (wBIn : Bindings) (depth : Nat)
      (live : List Atom) (scope : List String)
      (ctxCall : Entry.Value) (cFrameIn : Completed.Frame)
      (rhs : Atom) (selected wBMid : Bindings)
      (work : Spec.Eval.Steps.EquationWork) (ctxProdVal : Entry.Value)
      (cFrameMid : Completed.Frame)
      (remEqSteps remProdSteps remRetSteps : Nat)
      (remRows : List (Atom × Bindings))
      (remWorks : List Spec.Eval.Steps.EquationWork)
      (remBodyResults remProdResults : ResultSet)
      (remCtxProdResults : List Completed.Result)
      (remFinalResults : ResultSet)
      (remCtxFinalResults : List Completed.Result)
      (eqReady :
        (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
          (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
            (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
      (mergeFilterEq :
        ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
        [(Atom.notReducible, wBMid)])
      (outBindingsEq : cFrameMid.bindings = work.bindings)
      (unifyRel :
        Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
          (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
      (ctxProdEq : ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
      (bodyEraseEq : ctxProdVal.erase = Atom.notReducible)
      (callEq : ctxCall.erase = expr)
      (actMid : ScopedActivationRel wBMid cFrameMid)
      (tailDerivation :
        ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
          expr expected wBIn depth live scope ctxCall cFrameIn
          remEqSteps remProdSteps remRetSteps
          (.prepend [(expr, wBMid)] :: wRetStack)
          (.prepend [(ctxCall, cFrameMid)] :: cEqStack)
          remRows remWorks remBodyResults remProdResults remCtxProdResults
          remFinalResults remCtxFinalResults) :
      ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
        expr expected wBIn depth live scope ctxCall cFrameIn
        (remEqSteps + 3) (1 + remProdSteps + 3) (1 + remRetSteps + 3)
        wRetStack cEqStack ((rhs, selected) :: remRows) (work :: remWorks)
        ((Atom.notReducible, wBMid) :: remBodyResults)
        ((Atom.notReducible, wBMid) :: remProdResults)
        ((ctxProdVal, cFrameMid) :: remCtxProdResults)
        ((expr, wBMid) :: remFinalResults)
        ((ctxCall, cFrameMid) :: remCtxFinalResults)
  | cons_ordinary_stopped
      (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation)
      (expr expected : Atom) (wBIn : Bindings) (depth : Nat)
      (live : List Atom) (scope : List String)
      (ctxCall : Entry.Value) (cFrameIn : Completed.Frame)
      (rhs wBodyVal : Atom) (selected wBMid : Bindings)
      (work : Spec.Eval.Steps.EquationWork) (ctxProdVal : Entry.Value)
      (cFrameMid : Completed.Frame)
      (remEqSteps remProdSteps remRetSteps : Nat)
      (remRows : List (Atom × Bindings))
      (remWorks : List Spec.Eval.Steps.EquationWork)
      (remBodyResults remProdResults : ResultSet)
      (remCtxProdResults : List Completed.Result)
      (remFinalResults : ResultSet)
      (remCtxFinalResults : List Completed.Result)
      (eqReady :
        (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
          (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
            (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
      (mergeFilterEq :
        ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
        [(wBodyVal, wBMid)])
      (outBindingsEq : cFrameMid.bindings = work.bindings)
      (unifyRel :
        Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
          (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
      (ctxProdEq : ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
      (bodyEraseEq : ctxProdVal.erase = wBodyVal)
      (notFunc : ∀ body, wBodyVal ≠ .expression [.symbol "function", body])
      (notRefused : wBodyVal ≠ Atom.notReducible)
      (stopped : isEmptyOrError wBodyVal = true)
      (actMid : ScopedActivationRel wBMid cFrameMid)
      (tailDerivation :
        ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
          expr expected wBIn depth live scope ctxCall cFrameIn
          remEqSteps remProdSteps remRetSteps
          (.prepend [(wBodyVal, wBMid)] :: wRetStack)
          (.prepend [(ctxProdVal, cFrameMid)] :: cEqStack)
          remRows remWorks remBodyResults remProdResults remCtxProdResults
          remFinalResults remCtxFinalResults) :
      ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
        expr expected wBIn depth live scope ctxCall cFrameIn
        (remEqSteps + 3) (1 + remProdSteps + 3) (1 + remRetSteps + 3)
        wRetStack cEqStack ((rhs, selected) :: remRows) (work :: remWorks)
        ((wBodyVal, wBMid) :: remBodyResults)
        ((wBodyVal, wBMid) :: remProdResults)
        ((ctxProdVal, cFrameMid) :: remCtxProdResults)
        ((wBodyVal, wBMid) :: remFinalResults)
        ((ctxProdVal, cFrameMid) :: remCtxFinalResults)
  | cons_ordinary_evaluate
      (wRetStack : List RecursiveTasks.Frame)
      (cEqStack : List RecursiveTasks.Contextual.Continuation)
      (expr expected : Atom) (wBIn : Bindings) (depth : Nat)
      (live : List Atom) (scope : List String)
      (ctxCall : Entry.Value) (cFrameIn : Completed.Frame)
      (rhs wBodyVal : Atom) (selected wBMid : Bindings)
      (work : Spec.Eval.Steps.EquationWork) (ctxProdVal : Entry.Value)
      (cFrameMid : Completed.Frame)
      (childSteps remEqSteps remProdSteps remRetSteps : Nat)
      (remRows : List (Atom × Bindings))
      (remWorks : List Spec.Eval.Steps.EquationWork)
      (remBodyResults remProdResults : ResultSet)
      (remCtxProdResults : List Completed.Result)
      (headFinalResults remFinalResults : ResultSet)
      (headCtxFinalResults remCtxFinalResults : List Completed.Result)
      (eqReady :
        (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
          (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
            (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
      (mergeFilterEq :
        ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
        [(wBodyVal, wBMid)])
      (outBindingsEq : cFrameMid.bindings = work.bindings)
      (unifyRel :
        Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
          (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
      (ctxProdEq : ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
      (bodyEraseEq : ctxProdVal.erase = wBodyVal)
      (notFunc : ∀ body, wBodyVal ≠ .expression [.symbol "function", body])
      (notRefused : wBodyVal ≠ Atom.notReducible)
      (clean : isEmptyOrError wBodyVal = false)
      (actMid : ScopedActivationRel wBMid cFrameMid)
      (childDerivation :
        ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
          (depth + 1) live live scope wBodyVal ctxProdVal expected wBMid cFrameMid
          (.append (.returns expr expected (depth + 1) remProdResults live) :: wRetStack)
          (.append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
            .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
          childSteps headFinalResults headCtxFinalResults)
      (tailDerivation :
        ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
          expr expected wBIn depth live scope ctxCall cFrameIn
          remEqSteps remProdSteps remRetSteps
          (.prepend headFinalResults :: wRetStack)
          (.prepend headCtxFinalResults :: cEqStack)
          remRows remWorks remBodyResults remProdResults remCtxProdResults
          remFinalResults remCtxFinalResults) :
      ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
        expr expected wBIn depth live scope ctxCall cFrameIn
        (remEqSteps + 3) (1 + remProdSteps + 3)
        ((childSteps + 1) + remRetSteps + 3) wRetStack cEqStack
        ((rhs, selected) :: remRows) (work :: remWorks)
        ((wBodyVal, wBMid) :: remBodyResults)
        ((wBodyVal, wBMid) :: remProdResults)
        ((ctxProdVal, cFrameMid) :: remCtxProdResults)
        (headFinalResults ++ remFinalResults)
        (headCtxFinalResults ++ remCtxFinalResults)

end

/-- A materialized ordinary equation body that passes its expected type earns
the recursive child derivation directly. -/
theorem ScopedEquationDerivation.cons_ordinary_typePass
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    (rhs wBodyVal : Atom) (selected wBMid : Bindings)
    (work : Spec.Eval.Steps.EquationWork) (ctxProdVal : Entry.Value)
    (cFrameMid : Completed.Frame)
    {remEqSteps remProdSteps remRetSteps : Nat}
    {remRows : List (Atom × Bindings)}
    {remWorks : List Spec.Eval.Steps.EquationWork}
    {remBodyResults remProdResults : ResultSet}
    {remCtxProdResults : List Completed.Result}
    {remFinalResults : ResultSet}
    {remCtxFinalResults : List Completed.Result}
    (eqReady :
      (matchCovered (depth + 1) (.merge selected (aliasConstraints wBIn)) &&
        (mergeBindings selected (aliasConstraints wBIn) (depth + 1)).all fun merged =>
          (merged.hasLoop || merged.applyFullCovered rhs (depth + 1))) = true)
    (mergeFilterEq :
      ((mergeBindings selected (aliasConstraints wBIn) (depth + 1)).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull rhs (depth + 1), merged)) =
      [(wBodyVal, wBMid)])
    (outBindingsEq : cFrameMid.bindings = work.bindings)
    (unifyRel :
      Entry.Value.UnifyRel policy.rebuilding cFrameIn.environment ctxCall
        (Entry.Value.ofAtom work.pattern) cFrameMid.environment)
    (ctxProdEq : ctxProdVal = cFrameMid.read policy (Entry.Value.ofAtom work.body))
    (notFunc : ∀ body, wBodyVal ≠ .expression [.symbol "function", body])
    (notRefused : wBodyVal ≠ Atom.notReducible)
    (clean : isEmptyOrError wBodyVal = false)
    (typePass : expected = Atom.atomType ∨ expected = getMetaType wBodyVal ∨
      getMetaType wBodyVal = Atom.variableType)
    (entryReady : ScopedAtomEntryReady policy wBodyVal ctxProdVal cFrameMid)
    (actMid : ScopedActivationRel wBMid cFrameMid)
    (tailDerivation :
      ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
        expr expected wBIn depth live scope ctxCall cFrameIn
        remEqSteps remProdSteps remRetSteps
        (.prepend [(wBodyVal, wBMid)] :: wRetStack)
        (.prepend [(cFrameMid.read policy ctxProdVal, cFrameMid)] :: cEqStack)
        remRows remWorks remBodyResults remProdResults remCtxProdResults
        remFinalResults remCtxFinalResults) :
    ScopedEquationDerivation space dispatch hostDispatch policy wEmitted cEmitted
      expr expected wBIn depth live scope ctxCall cFrameIn
      (remEqSteps + 3) (1 + remProdSteps + 3) (2 + remRetSteps + 3)
      wRetStack cEqStack ((rhs, selected) :: remRows) (work :: remWorks)
      ((wBodyVal, wBMid) :: remBodyResults)
      ((wBodyVal, wBMid) :: remProdResults)
      ((ctxProdVal, cFrameMid) :: remCtxProdResults)
      ((wBodyVal, wBMid) :: remFinalResults)
      ((cFrameMid.read policy ctxProdVal, cFrameMid) :: remCtxFinalResults) := by
  apply ScopedEquationDerivation.cons_ordinary_evaluate
    (ctxProdEq := ctxProdEq) (bodyEraseEq := entryReady.1)
    (childDerivation := ScopedAtomDerivation.type_pass depth live live scope
      wBodyVal expected ctxProdVal wBMid cFrameMid
      (.append (.returns expr expected (depth + 1) remProdResults live) :: wRetStack)
      (.append (.boundaryBatch live scope none (.returned ctxCall expected) []) ::
        .append (.equations live scope ctxCall expected cFrameIn remWorks) :: cEqStack)
      entryReady clean typePass actMid)
    (tailDerivation := tailDerivation)
  all_goals assumption

mutual

/-- The earned worker derivation reconstructs the authoritative completed
source judgment at arbitrary saved stacks.  This structural fold is independent
of the machine-execution theorem `ScopedAtomDerivation.task_run`. -/
theorem ScopedAtomDerivation.to_completed_atomRel
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {fuel : Nat} {wLive cLive : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults) :
    Completed.AtomRel space hostDispatch Completed.scopedLookup
      cLive scope ctxVal expected cFrame cResults (policy := policy) := by
  cases derivation
  case empty_or_error depth stopped entryReady actRel =>
      apply Completed.AtomRel.delivered
      apply Entry.Rel.stopped
      rw [entryReady.2.1, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
      exact stopped
  case type_pass depth notStopped typePass entryReady actRel =>
      apply Completed.AtomRel.delivered
      apply Entry.Rel.pass
      · rw [entryReady.2.1, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
        simp [notStopped]
      · rw [entryReady.2.1, Conformance.metaTypeRel_iff_getMetaType]
      · exact typePass
  case cast admission =>
      exact .cast admission.entered admission.source_batch admission.cast_results
  case selection_failed operator arguments ctxOp ctxArgs fuel readiness candidates errors admission =>
      have entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
          (cFrame.read policy ctxVal).erase expected .interpret :=
        admission.entry_ready.entry_interpret admission.input_not_stopped
          admission.expected_not_atom admission.expected_not_expression
      have selectedAtRead : Completed.InvocationSelectionRel space Completed.scopedLookup
          policy wLive scope (cFrame.read policy ctxVal).erase ctxOp.erase
          expected cFrame (.exhausted errors false) := by
        simpa only [admission.entry_ready.2.1, admission.operator_erase] using
          admission.contextual_exhausted
      simpa only [admission.entry_ready.2.1] using
        (Completed.AtomRel.selectionFailed entered admission.read_shape selectedAtRead
          (completedSuccessPriority_rel
            ((Completed.diagnosticResults errors cFrame).map
              (Completed.readResult policy))))
  case extra branch => exact extensionLaws.source branch
  case selected_function operator opVal arguments retVals ctxOp ctxOpVal ctxArgs ctxRetVals
      wBSelected wBHead wBArgs cFrameSelected cFrameHead cFrameArgs signature candidates
      rows works bodyResults prodResults finalResults ctxProdResults ctxFinalResults fuel
      opSteps argSteps eqSteps prodSteps retSteps readDepth readiness operatorResultRel
      callAdmission entry operatorDerivation argumentsDerivation equationDerivation =>
      have operatorSource := ScopedAtomDerivation.to_completed_atomRel operatorDerivation
      have argumentsSource := ScopedArgsDerivation.to_completed_argumentsRel argumentsDerivation
      have equationsSource :=
        ScopedEquationDerivation.to_completed_equationBodiesRel equationDerivation
      have operatorErase : ctxOpVal.erase = opVal := operatorResultRel.1.symm
      have operatorContinues : ¬IsEmptyOrErrorRel ctxOpVal.erase := by
        rw [operatorErase, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
        simp [entry.operator_not_stopped]
      have functionBranches : Completed.FunctionBranchesRel space hostDispatch
          Completed.scopedLookup (Completed.invocationReturnType signature :: wLive) scope
          (ctxArgs.zip signature.argumentTypes) [(ctxOpVal, cFrameHead)]
          [(.expression .active (ctxOpVal :: ctxRetVals), cFrameArgs)]
          (policy := policy) := by
        simpa [Completed.functionAssemble] using
          (Completed.FunctionBranchesRel.continuing
            (head := (ctxOpVal, cFrameHead)) (heads := [])
            (children := [(Entry.Value.argumentPacket ctxRetVals, cFrameArgs)])
            (rest := []) operatorContinues
            (by simpa only [operatorErase] using argumentsSource)
            (Completed.FunctionBranchesRel.nil (space := space)
              (dispatch := hostDispatch) (lookup := Completed.scopedLookup)
              (live := Completed.invocationReturnType signature :: wLive)
              (scope := scope) (requests := ctxArgs.zip signature.argumentTypes)
              (policy := policy)))
      have functionSource : Completed.FunctionRel space hostDispatch Completed.scopedLookup
          (Completed.invocationReturnType signature :: wLive) scope expected signature
          ctxOp ctxArgs cFrameSelected
          [(.expression .active (ctxOpVal :: ctxRetVals), cFrameArgs)]
          (policy := policy) :=
        .evaluated entry.arity_eq operatorSource functionBranches
      have callSource : Completed.CallRel space hostDispatch Completed.scopedLookup
          wLive scope (.expression .active (ctxOpVal :: ctxRetVals))
          (Completed.invocationReturnType signature) cFrameArgs ctxFinalResults
          (policy := policy) :=
        .equations (by
          rw [callAdmission.value_erase, Conformance.isErrorRel_iff_isErrorAtom]
          simp [callAdmission.not_error])
          callAdmission.non_grounded callAdmission.frontier callAdmission.works_nonempty
          equationsSource
      have callsSource : Completed.CallsRel space hostDispatch Completed.scopedLookup
          wLive scope (Completed.invocationReturnType signature)
          [(.expression .active (ctxOpVal :: ctxRetVals), cFrameArgs)] ctxFinalResults
          (policy := policy) := by
        simpa only [List.append_nil] using
          (Completed.CallsRel.cons callSource
            (Completed.CallsRel.nil (space := space) (dispatch := hostDispatch)
              (lookup := Completed.scopedLookup) (live := wLive) (scope := scope)
              (expected := Completed.invocationReturnType signature) (policy := policy)))
      have invocationsSource : Completed.InvocationsRel space hostDispatch
          Completed.scopedLookup wLive scope expected signature ctxOp ctxArgs
          [cFrameSelected] ctxFinalResults (policy := policy) := by
        simpa only [List.append_nil] using
          (Completed.InvocationsRel.cons functionSource callsSource
            (Completed.InvocationsRel.nil (space := space) (dispatch := hostDispatch)
              (lookup := Completed.scopedLookup) (live := wLive) (scope := scope)
              (expected := expected) (signature := signature) (operator := ctxOp)
              (arguments := ctxArgs) (policy := policy)))
      have entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
          (cFrame.read policy ctxVal).erase expected .interpret :=
        entry.entry_ready.entry_interpret entry.input_not_stopped
          entry.expected_not_atom entry.expected_not_expression
      have selectedAtRead : Completed.InvocationSelectionRel space Completed.scopedLookup
          policy wLive scope (cFrame.read policy ctxVal).erase ctxOp.erase expected cFrame
          (.selected signature [cFrameSelected]) := by
        simpa only [entry.entry_ready.2.1, entry.operator_erase] using
          entry.contextual_selected
      simpa only [entry.entry_ready.2.1] using
        (Completed.AtomRel.function entered entry.read_shape selectedAtRead
          invocationsSource (completedSuccessPriority_rel
            (ctxFinalResults.map (Completed.readResult policy))))
termination_by steps
decreasing_by all_goals omega

/-- The structural argument derivation is the corresponding completed
left-to-right argument judgment, including its reached output frame. -/
theorem ScopedArgsDerivation.to_completed_argumentsRel
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {scope : List String} {fuel steps : Nat} {live argVals argTypes : List Atom}
    {requests : List Completed.ArgumentRequest}
    {retVals : List Atom} {ctxRetVals : List Entry.Value}
    {wBIn wBOut : Bindings} {cFrameIn cFrameOut : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    (derivation : ScopedArgsDerivation space dispatch hostDispatch policy
      wEmitted cEmitted scope fuel steps live argVals argTypes requests retVals ctxRetVals
      wBIn cFrameIn wBOut cFrameOut wStack cStack) :
    Completed.ArgumentsRel space hostDispatch Completed.scopedLookup live scope requests
      cFrameIn [(Entry.Value.argumentPacket ctxRetVals, cFrameOut)] (policy := policy) := by
  cases derivation
  case nil => exact .nil
  case cons fuel headSteps tailSteps argVal retVal expectedType remArgs remTypes retVals
      ctxArg ctxRet remReqs ctxRetVals wBMid cFrameMid argEq retEq remEq typesEq
      tailRetEq notChangedStopped actMid actIn actOut headDerivation tailDerivation =>
      have headSource := ScopedAtomDerivation.to_completed_atomRel headDerivation
      have tailSource := ScopedArgsDerivation.to_completed_argumentsRel tailDerivation
      have continues : ¬Completed.ArgumentStopped ctxArg (ctxRet, cFrameMid) := by
        intro stopped
        have failed : isEmptyOrError retVal = true := by
          rw [← retEq, ← Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
          exact stopped.1
        have changed : retVal ≠ argVal := by
          intro same
          exact stopped.2 (retEq.trans (same.trans argEq.symm))
        have impossible : (retVal != argVal && isEmptyOrError retVal) = true := by
          exact Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr changed, failed⟩
        rw [notChangedStopped] at impossible
        contradiction
      have branches : Completed.ArgumentBranchesRel space hostDispatch
          Completed.scopedLookup live scope ctxArg remReqs [(ctxRet, cFrameMid)]
          [(Entry.Value.argumentPacket (ctxRet :: ctxRetVals), cFrameOut)]
          (policy := policy) := by
        simpa only [List.map_cons, List.map_nil, List.append_nil,
          Completed.argumentPrepend_packet] using
          (Completed.ArgumentBranchesRel.continuing
            (head := (ctxRet, cFrameMid)) (heads := [])
            (children := [(Entry.Value.argumentPacket ctxRetVals, cFrameOut)])
            (rest := []) continues (by simpa only [retEq] using tailSource)
            (Completed.ArgumentBranchesRel.nil (space := space) (dispatch := hostDispatch)
              (lookup := Completed.scopedLookup) (live := live) (scope := scope)
              (original := ctxArg) (requests := remReqs) (policy := policy)))
      exact Completed.ArgumentsRel.cons headSource branches
termination_by steps
decreasing_by all_goals omega

/-- Rejected concrete rows disappear before the completed frontier, while
every accepted row reconstructs its producer and returned-child boundaries. -/
theorem ScopedEquationDerivation.to_completed_equationBodiesRel
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {eqSteps prodSteps retSteps : Nat}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    {rows : List (Atom × Bindings)} {works : List Spec.Eval.Steps.EquationWork}
    {bodyResults prodResults : ResultSet} {ctxProdResults : List Completed.Result}
    {finalResults : ResultSet} {ctxFinalResults : List Completed.Result}
    (derivation : ScopedEquationDerivation space dispatch hostDispatch policy
      wEmitted cEmitted expr expected wBIn depth live scope ctxCall cFrameIn
      eqSteps prodSteps retSteps wRetStack cEqStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults) :
    Completed.EquationBodiesRel space hostDispatch Completed.scopedLookup live scope
      ctxCall expected cFrameIn works ctxFinalResults (policy := policy) := by
  cases derivation
  case nil => exact .nil
  case cons_rejected tailDerivation =>
      exact ScopedEquationDerivation.to_completed_equationBodiesRel tailDerivation
  case cons_ordinary_notReducible rhs selected wBMid work ctxProdVal cFrameMid
      remEqSteps remProdSteps remRetSteps remRows remWorks remBodyResults remProdResults
      remCtxProdResults remFinalResults remCtxFinalResults outBindingsEq ctxProdEq
      bodyEraseEq callEq actMid eqReady mergeFilterEq unifyRel tailDerivation =>
      have tailSource :=
        ScopedEquationDerivation.to_completed_equationBodiesRel tailDerivation
      have notPending : ¬Completed.FunctionPending policy ctxProdVal := by
        rintro ⟨⟨body, shape⟩, _⟩
        have impossible : Atom.notReducible = .expression [.symbol "function", body] :=
          bodyEraseEq.symm.trans shape
        cases impossible
      have producer : Completed.BoundaryRel space hostDispatch Completed.scopedLookup
          (expected :: live) scope (some ctxCall.erase) .producer ctxProdVal cFrameMid
          [(ctxProdVal, cFrameMid)] (policy := policy) :=
        .producerRaw notPending
      have returned : Completed.BoundaryBatchRel space hostDispatch
          Completed.scopedLookup live scope none (.returned ctxCall expected)
          [(ctxProdVal, cFrameMid)] [(ctxCall, cFrameMid)] (policy := policy) := by
        exact .cons (.returned (.notReducible bodyEraseEq)) .nil
      simpa only [List.singleton_append] using
        (Completed.EquationBodiesRel.cons outBindingsEq unifyRel
          (by simpa only [← ctxProdEq] using producer) returned tailSource)
  case cons_ordinary_stopped rhs wBodyVal selected wBMid work ctxProdVal cFrameMid
      remEqSteps remProdSteps remRetSteps remRows remWorks remBodyResults remProdResults
      remCtxProdResults remFinalResults remCtxFinalResults outBindingsEq ctxProdEq
      bodyEraseEq notFunc notRefused stopped actMid eqReady mergeFilterEq unifyRel
      tailDerivation =>
      have tailSource :=
        ScopedEquationDerivation.to_completed_equationBodiesRel tailDerivation
      have notPending : ¬Completed.FunctionPending policy ctxProdVal := by
        rintro ⟨⟨body, shape⟩, _⟩
        exact notFunc body (bodyEraseEq.symm.trans shape)
      have stoppedRel : IsEmptyOrErrorRel ctxProdVal.erase := by
        rw [bodyEraseEq, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
        exact stopped
      have producer : Completed.BoundaryRel space hostDispatch Completed.scopedLookup
          (expected :: live) scope (some ctxCall.erase) .producer ctxProdVal cFrameMid
          [(ctxProdVal, cFrameMid)] (policy := policy) :=
        .producerRaw notPending
      have returned : Completed.BoundaryBatchRel space hostDispatch
          Completed.scopedLookup live scope none (.returned ctxCall expected)
          [(ctxProdVal, cFrameMid)] [(ctxProdVal, cFrameMid)] (policy := policy) := by
        exact .cons (.returned (.stopped stoppedRel)) .nil
      simpa only [List.singleton_append] using
        (Completed.EquationBodiesRel.cons outBindingsEq unifyRel
          (by simpa only [← ctxProdEq] using producer) returned tailSource)
  case cons_ordinary_evaluate rhs wBodyVal selected wBMid work ctxProdVal cFrameMid
      childSteps remEqSteps remProdSteps remRetSteps remRows remWorks remBodyResults
      remProdResults remCtxProdResults headFinalResults remFinalResults
      headCtxFinalResults remCtxFinalResults outBindingsEq ctxProdEq bodyEraseEq notFunc
      notRefused clean actMid eqReady mergeFilterEq unifyRel childDerivation tailDerivation =>
      have childSource := ScopedAtomDerivation.to_completed_atomRel childDerivation
      have tailSource :=
        ScopedEquationDerivation.to_completed_equationBodiesRel tailDerivation
      have notPending : ¬Completed.FunctionPending policy ctxProdVal := by
        rintro ⟨⟨body, shape⟩, _⟩
        exact notFunc body (bodyEraseEq.symm.trans shape)
      have notRefusedRel : ctxProdVal.erase ≠ Atom.notReducible := by
        intro refused
        exact notRefused (bodyEraseEq.symm.trans refused)
      have continues : ¬IsEmptyOrErrorRel ctxProdVal.erase := by
        rw [bodyEraseEq, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
        simp [clean]
      have producer : Completed.BoundaryRel space hostDispatch Completed.scopedLookup
          (expected :: live) scope (some ctxCall.erase) .producer ctxProdVal cFrameMid
          [(ctxProdVal, cFrameMid)] (policy := policy) :=
        .producerRaw notPending
      have returned : Completed.BoundaryBatchRel space hostDispatch
          Completed.scopedLookup live scope none (.returned ctxCall expected)
          [(ctxProdVal, cFrameMid)] headCtxFinalResults (policy := policy) := by
        have returnRel : Completed.ReturnRel space hostDispatch Completed.scopedLookup
            live scope ctxCall expected ctxProdVal cFrameMid headCtxFinalResults
            (policy := policy) :=
          .evaluate notRefusedRel continues childSource
        have boundaryReturned : Completed.BoundaryRel space hostDispatch
            Completed.scopedLookup live scope none (.returned ctxCall expected)
            ctxProdVal cFrameMid headCtxFinalResults (policy := policy) :=
          .returned returnRel
        simpa only [List.append_nil] using
          (Completed.BoundaryBatchRel.cons
            (head := (ctxProdVal, cFrameMid)) (heads := [])
            (children := headCtxFinalResults) (rest := []) boundaryReturned
            (Completed.BoundaryBatchRel.nil (space := space) (dispatch := hostDispatch)
              (lookup := Completed.scopedLookup) (live := live) (scope := scope)
              (caller := none) (boundary := .returned ctxCall expected)
              (policy := policy)))
      exact Completed.EquationBodiesRel.cons outBindingsEq unifyRel
        (by simpa only [← ctxProdEq] using producer) returned tailSource
termination_by eqSteps + prodSteps + retSteps
decreasing_by all_goals omega

end


mutual

/-- Every admitted recursive atom derivation earns its exact worker/contextual
task run. -/
theorem ScopedAtomDerivation.task_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {fuel : Nat} {wLive cLive : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom value expected wB fuel wLive)
      (.atom cLive scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted steps wResults cResults := by
  have source := derivation.to_completed_atomRel
  cases derivation
  case empty_or_error =>
      apply ScopedTaskRun.atomEmptyOrError <;> assumption
  case type_pass =>
      apply ScopedTaskRun.atomTypePass <;> assumption
  case cast =>
      apply ScopedTaskRun.atomCast
      assumption
  case selection_failed =>
      apply ScopedTaskRun.atomSelectionFailed
      assumption
  case extra branch => exact extensionLaws.run branch
  case selected_function =>
      have opRun := ScopedAtomDerivation.task_run (derivation := by assumption)
      have argsRun := ScopedArgsDerivation.task_run (derivation := by assumption)
      have eqSpine := ScopedEquationDerivation.to_concreteSpine (derivation := by assumption)
      apply ScopedTaskRun.selected_function_of_parts
      all_goals assumption
termination_by steps
decreasing_by all_goals omega

/-- Argument execution is delimited above its actual caller stacks.  Its exact
worker cost is structural; the contextual path is reconstructed independently
from the completed argument judgment and therefore permits phase-shifted
continuation stacks. -/
theorem ScopedArgsDerivation.task_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {scope : List String} {fuel steps : Nat} {live argVals argTypes : List Atom}
    {requests : List Completed.ArgumentRequest}
    {retVals : List Atom} {ctxRetVals : List Entry.Value}
    {wBIn wBOut : Bindings} {cFrameIn cFrameOut : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    (derivation : ScopedArgsDerivation space dispatch hostDispatch policy
      wEmitted cEmitted scope fuel steps live argVals argTypes requests retVals ctxRetVals
      wBIn cFrameIn wBOut cFrameOut wStack cStack) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.args argVals argTypes wBIn fuel live)
      (.arguments live scope requests cFrameIn)
      wStack cStack wEmitted cEmitted steps
      [(argumentPacket retVals, wBOut)]
      [(Entry.Value.argumentPacket ctxRetVals, cFrameOut)] := by
  cases derivation
  case nil fuel actRel =>
      have wStep : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.args [] [] wBIn (fuel + 1) live), wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(argumentPacket [], wBIn)], wStack, wEmitted⟩) := rfl
      have nilDerivation : ScopedArgsDerivation space dispatch hostDispatch policy
          wEmitted cEmitted scope (fuel + 1) 1 live [] [] [] [] []
          wBIn cFrameIn wBIn cFrameIn wStack cStack :=
        ScopedArgsDerivation.nil scope fuel live wBIn cFrameIn wStack cStack actRel
      have source := ScopedArgsDerivation.to_completed_argumentsRel nilDerivation
      refine ⟨by omega, ?_, ?_, RecursiveExecution.Contextual.arguments_complete source cStack⟩
      · exact .cons
          ⟨by simp [argumentPacket, Entry.Value.argumentPacket, Entry.Value.erase], actRel⟩ .nil
      · intro budget
        rw [Nat.add_comm 1 budget,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep]
  case cons fuel headSteps tailSteps argVal retVal expectedType remArgs remTypes retVals
      ctxArg ctxRet remReqs ctxRetVals wBMid cFrameMid argEq retEq remEq typesEq
      tailRetEq notChangedStopped actMid actIn actOut headDerivation tailDerivation =>
      have headRun := ScopedAtomDerivation.task_run headDerivation
      have tailRun := ScopedArgsDerivation.task_run tailDerivation
      have wStep1 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.args (argVal :: remArgs) (expectedType :: remTypes)
            wBIn (fuel + 1) live), wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.atom argVal expectedType wBIn fuel
              (remArgs ++ remTypes ++ live)),
              .argumentHeads argVal remArgs remTypes fuel live :: wStack, wEmitted⟩) := rfl
      have wStep2 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [(retVal, wBMid)],
            .argumentHeads argVal remArgs remTypes fuel live :: wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.argumentHeads argVal remArgs remTypes fuel
              [(retVal, wBMid)] live), wStack, wEmitted⟩) := rfl
      have notCond : ¬(¬retVal = argVal ∧ isEmptyOrError retVal = true) := by
        rintro ⟨changed, stopped⟩
        have changedBool : (retVal != argVal) = true := bne_iff_ne.mpr changed
        simp [changedBool, stopped] at notChangedStopped
      have wStep3 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.argumentHeads argVal remArgs remTypes fuel
            [(retVal, wBMid)] live), wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.args remArgs remTypes wBMid fuel (retVal :: live)),
              .argumentTail retVal ::
                .append (.argumentHeads argVal remArgs remTypes fuel [] live) :: wStack,
              wEmitted⟩) := by
        simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
          FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
          FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
          FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, notCond,
          Transition.relabel]
      have wStep4 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [(argumentPacket retVals, wBOut)],
            .argumentTail retVal ::
              .append (.argumentHeads argVal remArgs remTypes fuel [] live) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(argumentPacket (retVal :: retVals), wBOut)],
              .append (.argumentHeads argVal remArgs remTypes fuel [] live) :: wStack,
              wEmitted⟩) := by
        simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
          RecursiveMachine.Checked.frameReady,
          FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
          RecursiveMachine.resume, RecursiveTasks.argumentTail, argumentPacket,
          argumentsSucceeded, unpackArguments, argumentValues,
          Transition.relabel]
      have wStep5 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [(argumentPacket (retVal :: retVals), wBOut)],
            .append (.argumentHeads argVal remArgs remTypes fuel [] live) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .work (.argumentHeads argVal remArgs remTypes fuel [] live),
              .prepend [(argumentPacket (retVal :: retVals), wBOut)] :: wStack,
              wEmitted⟩) := rfl
      have wStep6 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.argumentHeads argVal remArgs remTypes fuel [] live),
            .prepend [(argumentPacket (retVal :: retVals), wBOut)] :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .returning [],
              .prepend [(argumentPacket (retVal :: retVals), wBOut)] :: wStack,
              wEmitted⟩) := rfl
      have wStep7 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [],
            .prepend [(argumentPacket (retVal :: retVals), wBOut)] :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(argumentPacket (retVal :: retVals), wBOut)],
              wStack, wEmitted⟩) := rfl
      have runAll : ∀ budget,
          (Checked.machine dispatch scopedTypes).run
            ((headSteps + tailSteps + 7) + budget)
              ⟨space, .work (.args (argVal :: remArgs) (expectedType :: remTypes)
                wBIn (fuel + 1) live), wStack, wEmitted⟩ =
          (Checked.machine dispatch scopedTypes).run budget
              ⟨space, .returning [(argumentPacket (retVal :: retVals), wBOut)],
                wStack, wEmitted⟩ := by
        intro budget
        rw [show (headSteps + tailSteps + 7) + budget =
            (headSteps + (2 + (tailSteps + (4 + budget)))) + 1 by omega,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep1,
          headRun.worker_run (2 + (tailSteps + (4 + budget))),
          show 2 + (tailSteps + (4 + budget)) =
            ((tailSteps + (4 + budget)) + 1) + 1 by omega,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep2,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep3,
          tailRun.worker_run (4 + budget),
          show 4 + budget = (((budget + 1) + 1) + 1) + 1 by omega,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep4,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep5,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep6,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep7]
      have source := ScopedArgsDerivation.to_completed_argumentsRel
        (ScopedArgsDerivation.cons scope fuel headSteps tailSteps live argVal retVal
          expectedType remArgs remTypes retVals ctxArg ctxRet remReqs ctxRetVals
          wBIn wBMid wBOut cFrameIn cFrameMid cFrameOut wStack cStack
          argEq retEq remEq typesEq tailRetEq notChangedStopped actIn actMid actOut
          headDerivation tailDerivation)
      exact ⟨by omega,
        .cons ⟨by simp [argumentPacket, Entry.Value.argumentPacket, Entry.Value.erase,
          tailRetEq, retEq], actOut⟩ .nil,
        runAll, RecursiveExecution.Contextual.arguments_complete source cStack⟩
termination_by steps
decreasing_by all_goals omega

/-- Erasing earned recursive atom children from an equation derivation yields
the concrete stack-indexed equation spine. -/
theorem ScopedEquationDerivation.to_concreteSpine
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {expr expected : Atom} {wBIn : Bindings} {depth : Nat}
    {live : List Atom} {scope : List String}
    {ctxCall : Entry.Value} {cFrameIn : Completed.Frame}
    {eqSteps prodSteps retSteps : Nat}
    {wRetStack : List RecursiveTasks.Frame}
    {cEqStack : List RecursiveTasks.Contextual.Continuation}
    {rows : List (Atom × Bindings)} {works : List Spec.Eval.Steps.EquationWork}
    {bodyResults prodResults : ResultSet} {ctxProdResults : List Completed.Result}
    {finalResults : ResultSet} {ctxFinalResults : List Completed.Result}
    (derivation : ScopedEquationDerivation space dispatch hostDispatch policy
      wEmitted cEmitted expr expected wBIn depth live scope ctxCall cFrameIn
      eqSteps prodSteps retSteps wRetStack cEqStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults) :
    ScopedConcreteEquationWorksSpine space dispatch hostDispatch policy
      expr expected wBIn depth live scope ctxCall cFrameIn wEmitted cEmitted
      eqSteps prodSteps retSteps wRetStack cEqStack rows works
      bodyResults prodResults ctxProdResults finalResults ctxFinalResults := by
  cases derivation
  case nil =>
      apply ScopedConcreteEquationWorksSpine.nil
  case cons_rejected =>
      have tailSpine := ScopedEquationDerivation.to_concreteSpine
        (derivation := by assumption)
      apply ScopedConcreteEquationWorksSpine.cons_rejected
      all_goals assumption
  case cons_ordinary_notReducible =>
      have tailSpine := ScopedEquationDerivation.to_concreteSpine
        (derivation := by assumption)
      apply ScopedConcreteEquationWorksSpine.cons_ordinary_notReducible
      all_goals assumption
  case cons_ordinary_stopped =>
      have tailSpine := ScopedEquationDerivation.to_concreteSpine
        (derivation := by assumption)
      apply ScopedConcreteEquationWorksSpine.cons_ordinary_stopped
      all_goals assumption
  case cons_ordinary_evaluate =>
      have childRun := ScopedAtomDerivation.task_run (derivation := by assumption)
      have tailSpine := ScopedEquationDerivation.to_concreteSpine
        (derivation := by assumption)
      apply ScopedConcreteEquationWorksSpine.cons_ordinary_evaluate
      all_goals assumption
termination_by eqSteps + prodSteps + retSteps
decreasing_by all_goals omega

end


/-! ### Arbitrary-result tuple and tuple-branch recursion

Tuple evaluation is a separate recursive component: one atom evaluation may
produce many head occurrences, and every non-stopped occurrence evaluates the
same syntactic tail in its own reached frame.  These proof objects record that
branch tree without assuming a whole tuple evaluator or identifying the
worker's continuation layout with the contextual one. -/

mutual

/-- Earned tuple evaluation for arbitrary head-result multiplicity. -/
inductive ScopedTupleDerivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension] :
    List String → Nat → Nat → List Atom → List Atom → List Entry.Value →
    Bindings → Completed.Frame →
    List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation →
    ResultSet → List Completed.Result → Prop where
  | nil
      (scope : List String) (fuel : Nat) (live : List Atom)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (actRel : ScopedActivationRel wB cFrame) :
      ScopedTupleDerivation space dispatch hostDispatch policy wEmitted cEmitted
        scope (fuel + 1) 1 live [] [] wB cFrame wStack cStack
        [(Atom.unit, wB)] [(.expression .active [], cFrame)]
  | singleton
      (scope : List String) (fuel headSteps : Nat) (live : List Atom)
      (single : Atom) (ctxSingle : Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (wHeads : ResultSet) (cHeads : List Completed.Result)
      (singleEq : ctxSingle.erase = single)
      (headDerivation : ScopedAtomDerivation space dispatch hostDispatch policy
        wEmitted cEmitted fuel live live scope single ctxSingle Atom.undefinedType
        wB cFrame (.tupleSingleton :: wStack) (.singleton :: cStack)
        headSteps wHeads cHeads) :
      ScopedTupleDerivation space dispatch hostDispatch policy wEmitted cEmitted
        scope (fuel + 1) (headSteps + 2) live [single] [ctxSingle]
        wB cFrame wStack cStack
        (wHeads.map HE.tupleSingleton)
        (cHeads.map Completed.tupleSingleton)
  | cons
      (scope : List String) (fuel headSteps branchSteps : Nat) (live : List Atom)
      (head second : Atom) (remaining : List Atom)
      (ctxHead ctxSecond : Entry.Value) (ctxRemaining : List Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (wHeads wResults : ResultSet)
      (cHeads cResults : List Completed.Result)
      (headEq : ctxHead.erase = head)
      (secondEq : ctxSecond.erase = second)
      (remainingEq : ctxRemaining.map Entry.Value.erase = remaining)
      (headDerivation : ScopedAtomDerivation space dispatch hostDispatch policy
        wEmitted cEmitted fuel (.expression (second :: remaining) :: live)
        (.expression ((ctxSecond :: ctxRemaining).map Entry.Value.erase) :: live) scope
        head ctxHead Atom.undefinedType wB cFrame
        (.tupleHeads (.expression (second :: remaining)) fuel live :: wStack)
        (.branches live scope (ctxSecond :: ctxRemaining) :: cStack)
        headSteps wHeads cHeads)
      (branchDerivation : ScopedTupleBranchesDerivation space dispatch hostDispatch
        policy wEmitted cEmitted scope fuel branchSteps live (second :: remaining)
        (ctxSecond :: ctxRemaining)
        wHeads cHeads wStack cStack wResults cResults) :
      ScopedTupleDerivation space dispatch hostDispatch policy wEmitted cEmitted
        scope (fuel + 1) (headSteps + branchSteps + 2)
        live (head :: second :: remaining) (ctxHead :: ctxSecond :: ctxRemaining)
        wB cFrame wStack cStack wResults cResults

/-- Earned traversal of every physical head occurrence of a tuple. -/
inductive ScopedTupleBranchesDerivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension] :
    List String → Nat → Nat → List Atom → List Atom → List Entry.Value →
    ResultSet → List Completed.Result →
    List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation →
    ResultSet → List Completed.Result → Prop where
  | nil
      (scope : List String) (fuel : Nat) (live tail : List Atom)
      (ctxTail : List Entry.Value)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (tailEq : ctxTail.map Entry.Value.erase = tail) :
      ScopedTupleBranchesDerivation space dispatch hostDispatch policy
        wEmitted cEmitted scope fuel 1 live tail ctxTail [] [] wStack cStack [] []
  | stopped
      (scope : List String) (fuel restSteps : Nat) (live tail : List Atom)
      (ctxTail : List Entry.Value)
      (wHead : ResultPair) (cHead : Completed.Result)
      (wHeads wRest : ResultSet)
      (cHeads cRest : List Completed.Result)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (tailEq : ctxTail.map Entry.Value.erase = tail)
      (headRel : ScopedResultRel wHead cHead)
      (stopped : isEmptyOrError wHead.1 = true)
      (restDerivation : ScopedTupleBranchesDerivation space dispatch hostDispatch
        policy wEmitted cEmitted scope fuel restSteps live tail ctxTail
        wHeads cHeads (.prepend [wHead] :: wStack) (.prepend [cHead] :: cStack)
        wRest cRest) :
      ScopedTupleBranchesDerivation space dispatch hostDispatch policy
        wEmitted cEmitted scope fuel (restSteps + 3) live tail ctxTail
        (wHead :: wHeads) (cHead :: cHeads) wStack cStack
        (wHead :: wRest) (cHead :: cRest)
  | continuing
      (scope : List String) (fuel childSteps restSteps : Nat)
      (live tail : List Atom) (ctxTail : List Entry.Value)
      (wHead : ResultPair) (cHead : Completed.Result)
      (wHeads wChildren wRest : ResultSet)
      (cHeads cChildren cRest : List Completed.Result)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (tailEq : ctxTail.map Entry.Value.erase = tail)
      (headRel : ScopedResultRel wHead cHead)
      (running : isEmptyOrError wHead.1 = false)
      (childDerivation : ScopedTupleDerivation space dispatch hostDispatch policy
        wEmitted cEmitted scope fuel childSteps (wHead.1 :: live) tail ctxTail
        wHead.2 cHead.2
        (.tupleTail wHead.1 ::
          .append (.tupleHeads (.expression tail) fuel wHeads live) :: wStack)
        (.tupleTail cHead.1 ::
          .append (.branches live scope ctxTail cHeads) :: cStack)
        wChildren cChildren)
      (restDerivation : ScopedTupleBranchesDerivation space dispatch hostDispatch
        policy wEmitted cEmitted scope fuel restSteps live tail ctxTail
        wHeads cHeads
        (.prepend (RecursiveTasks.tupleTail wHead.1 wChildren) :: wStack)
        (.prepend (cChildren.map (Completed.tuplePrepend cHead.1)) :: cStack)
        wRest cRest) :
      ScopedTupleBranchesDerivation space dispatch hostDispatch policy
        wEmitted cEmitted scope fuel (childSteps + restSteps + 4) live tail ctxTail
        (wHead :: wHeads) (cHead :: cHeads) wStack cStack
        (RecursiveTasks.tupleTail wHead.1 wChildren ++ wRest)
        (cChildren.map (Completed.tuplePrepend cHead.1) ++ cRest)

end

mutual

/-- A structural tuple derivation reconstructs the authoritative completed
tuple judgment. -/
theorem ScopedTupleDerivation.to_completed_tupleRel
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {scope : List String} {fuel steps : Nat} {live values : List Atom}
    {ctxValues : List Entry.Value} {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedTupleDerivation space dispatch hostDispatch policy
      wEmitted cEmitted scope fuel steps live values ctxValues wB cFrame
      wStack cStack wResults cResults) :
    Completed.TupleRel space hostDispatch Completed.scopedLookup live scope
      ctxValues cFrame cResults (policy := policy) := by
  cases derivation
  case nil => exact .nil
  case singleton headDerivation =>
      exact .singleton (ScopedAtomDerivation.to_completed_atomRel headDerivation)
  case cons headDerivation branchDerivation =>
      exact .cons (ScopedAtomDerivation.to_completed_atomRel headDerivation)
        (ScopedTupleBranchesDerivation.to_completed_tupleBranchesRel branchDerivation)
termination_by steps
decreasing_by all_goals omega

/-- A structural physical-head traversal reconstructs the authoritative
completed tuple-branch judgment. -/
theorem ScopedTupleBranchesDerivation.to_completed_tupleBranchesRel
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {scope : List String} {fuel steps : Nat} {live tail : List Atom}
    {ctxTail : List Entry.Value} {wHeads : ResultSet}
    {cHeads : List Completed.Result}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedTupleBranchesDerivation space dispatch hostDispatch policy
      wEmitted cEmitted scope fuel steps live tail ctxTail wHeads cHeads
      wStack cStack wResults cResults) :
    Completed.TupleBranchesRel space hostDispatch Completed.scopedLookup live scope
      ctxTail cHeads cResults (policy := policy) := by
  cases derivation
  case nil => exact .nil
  case stopped headRel stopped tailEq restDerivation =>
      refine .stopped ?_
        (ScopedTupleBranchesDerivation.to_completed_tupleBranchesRel restDerivation)
      rw [← headRel.1, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
      exact stopped
  case continuing headRel running tailEq childDerivation restDerivation =>
      have childSource := ScopedTupleDerivation.to_completed_tupleRel childDerivation
      have restSource :=
        ScopedTupleBranchesDerivation.to_completed_tupleBranchesRel restDerivation
      refine .continuing ?_ (by simpa only [headRel.1] using childSource) restSource
      rw [← headRel.1, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
      simpa only [Bool.not_eq_true] using running
termination_by steps
decreasing_by all_goals omega

end


mutual

/-- An earned tuple derivation executes the checked worker for the exact
structural cost and completes the independently reconstructed contextual
tuple judgment above the actual caller stacks. -/
theorem ScopedTupleDerivation.task_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {scope : List String} {fuel steps : Nat} {live values : List Atom}
    {ctxValues : List Entry.Value} {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedTupleDerivation space dispatch hostDispatch policy
      wEmitted cEmitted scope fuel steps live values ctxValues wB cFrame
      wStack cStack wResults cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.tuple (.expression values) wB fuel live)
      (.tuple live scope ctxValues cFrame)
      wStack cStack wEmitted cEmitted steps wResults cResults := by
  cases derivation
  case nil fuel actRel =>
      have wStep : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.tuple (.expression []) wB (fuel + 1) live),
            wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(Atom.unit, wB)], wStack, wEmitted⟩) := rfl
      have source : Completed.TupleRel space hostDispatch Completed.scopedLookup
          live scope [] cFrame [(.expression .active [], cFrame)]
          (policy := policy) := .nil
      refine ⟨by omega, .cons ?_ .nil, ?_,
        RecursiveExecution.Contextual.tuple_complete source cStack⟩
      · exact ⟨by simp [Atom.unit, Entry.Value.erase], actRel⟩
      · intro budget
        rw [Nat.add_comm 1 budget,
          (Checked.machine dispatch scopedTypes).run_succ_silent wStep]
  case singleton fuel headSteps single ctxSingle wHeads cHeads singleEq
      headDerivation =>
      have headRun := ScopedAtomDerivation.task_run headDerivation
      have wStep0 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.tuple (.expression [single]) wB (fuel + 1) live),
            wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.atom single Atom.undefinedType wB fuel live),
              .tupleSingleton :: wStack, wEmitted⟩) := rfl
      have wStep1 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning wHeads, .tupleSingleton :: wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning (wHeads.map HE.tupleSingleton),
              wStack, wEmitted⟩) := rfl
      have source : Completed.TupleRel space hostDispatch Completed.scopedLookup
          live scope [ctxSingle] cFrame (cHeads.map Completed.tupleSingleton)
          (policy := policy) :=
        .singleton (ScopedAtomDerivation.to_completed_atomRel headDerivation)
      refine ⟨by omega, ScopedResultRel.forall2_tupleSingleton headRun.results_rel,
        ?_, RecursiveExecution.Contextual.tuple_complete source cStack⟩
      intro budget
      rw [show (headSteps + 2) + budget = (headSteps + (budget + 1)) + 1 by omega,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep0,
        headRun.worker_run (budget + 1),
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep1]
  case cons fuel headSteps branchSteps head second remaining ctxHead ctxSecond
      ctxRemaining wHeads cHeads headEq secondEq remainingEq headDerivation
      branchDerivation =>
      have headRun := ScopedAtomDerivation.task_run headDerivation
      have branchRun := ScopedTupleBranchesDerivation.task_run branchDerivation
      have wStep0 : (Checked.machine dispatch scopedTypes).step
          ⟨space,
            .work (.tuple (.expression (head :: second :: remaining)) wB
              (fuel + 1) live), wStack, wEmitted⟩ =
          some (.silent
            ⟨space,
              .work (.atom head Atom.undefinedType wB fuel
                (.expression (second :: remaining) :: live)),
              .tupleHeads (.expression (second :: remaining)) fuel live :: wStack,
              wEmitted⟩) := rfl
      have wStep1 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning wHeads,
            .tupleHeads (.expression (second :: remaining)) fuel live :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space,
              .work (.tupleHeads (.expression (second :: remaining)) fuel
                wHeads live), wStack, wEmitted⟩) := rfl
      have source : Completed.TupleRel space hostDispatch Completed.scopedLookup
          live scope (ctxHead :: ctxSecond :: ctxRemaining) cFrame cResults
          (policy := policy) :=
        .cons (ScopedAtomDerivation.to_completed_atomRel headDerivation)
          (ScopedTupleBranchesDerivation.to_completed_tupleBranchesRel branchDerivation)
      refine ⟨by omega, branchRun.results_rel, ?_,
        RecursiveExecution.Contextual.tuple_complete source cStack⟩
      intro budget
      rw [show (headSteps + branchSteps + 2) + budget =
          (headSteps + (branchSteps + budget + 1)) + 1 by omega,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep0,
        headRun.worker_run (branchSteps + budget + 1),
        show branchSteps + budget + 1 = (branchSteps + budget) + 1 by omega,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep1,
        branchRun.worker_run budget]
termination_by steps
decreasing_by all_goals omega

/-- Every stopped or continuing physical head occurrence is drained exactly
once by the checked worker, preserving order and multiplicity. -/
theorem ScopedTupleBranchesDerivation.task_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {scope : List String} {fuel steps : Nat} {live tail : List Atom}
    {ctxTail : List Entry.Value} {wHeads : ResultSet}
    {cHeads : List Completed.Result}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedTupleBranchesDerivation space dispatch hostDispatch policy
      wEmitted cEmitted scope fuel steps live tail ctxTail wHeads cHeads
      wStack cStack wResults cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.tupleHeads (.expression tail) fuel wHeads live)
      (.branches live scope ctxTail cHeads)
      wStack cStack wEmitted cEmitted steps wResults cResults := by
  cases derivation
  case nil =>
      have wStep : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.tupleHeads (.expression tail) fuel [] live),
            wStack, wEmitted⟩ =
          some (.silent ⟨space, .returning [], wStack, wEmitted⟩) := rfl
      have source : Completed.TupleBranchesRel space hostDispatch
          Completed.scopedLookup live scope ctxTail [] [] (policy := policy) := .nil
      refine ⟨by omega, .nil, ?_,
        RecursiveExecution.Contextual.branches_complete source cStack⟩
      intro budget
      rw [Nat.add_comm 1 budget,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep]
  case stopped restSteps wHead cHead wHeads wRest cHeads cRest headRel stopped
      tailEq restDerivation =>
      have restRun := ScopedTupleBranchesDerivation.task_run restDerivation
      have wStep0 : (Checked.machine dispatch scopedTypes).step
          ⟨space,
            .work (.tupleHeads (.expression tail) fuel (wHead :: wHeads) live),
            wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [wHead],
              .append (.tupleHeads (.expression tail) fuel wHeads live) :: wStack,
              wEmitted⟩) := by
        simp [Checked.machine, RecursiveMachine.Checked.guardMachine,
          Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
          RecursiveMachine.Checked.taskReady,
          FirstSuccessRecursiveExecution.machine,
          FirstSuccessRecursiveExecution.next,
          FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
          stopped, Transition.relabel]
      have wStep1 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [wHead],
            .append (.tupleHeads (.expression tail) fuel wHeads live) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .work (.tupleHeads (.expression tail) fuel wHeads live),
              .prepend [wHead] :: wStack, wEmitted⟩) := rfl
      have wStep2 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning wRest, .prepend [wHead] :: wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning (wHead :: wRest), wStack, wEmitted⟩) := rfl
      have sourceStopped : IsEmptyOrErrorRel cHead.1.erase := by
        rw [← headRel.1, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
        exact stopped
      have source : Completed.TupleBranchesRel space hostDispatch
          Completed.scopedLookup live scope ctxTail (cHead :: cHeads)
          (cHead :: cRest) (policy := policy) :=
        .stopped sourceStopped
          (ScopedTupleBranchesDerivation.to_completed_tupleBranchesRel restDerivation)
      refine ⟨by omega, .cons headRel restRun.results_rel, ?_,
        RecursiveExecution.Contextual.branches_complete source cStack⟩
      intro budget
      rw [show (restSteps + 3) + budget =
          ((restSteps + (budget + 1)) + 1) + 1 by omega,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep0,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep1,
        restRun.worker_run (budget + 1),
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep2]
  case continuing childSteps restSteps wHead cHead wHeads wChildren wRest cHeads
      cChildren cRest headRel running tailEq childDerivation restDerivation =>
      have childRun := ScopedTupleDerivation.task_run childDerivation
      have restRun := ScopedTupleBranchesDerivation.task_run restDerivation
      have wStep0 : (Checked.machine dispatch scopedTypes).step
          ⟨space,
            .work (.tupleHeads (.expression tail) fuel (wHead :: wHeads) live),
            wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.tuple (.expression tail) wHead.2 fuel
                (wHead.1 :: live)),
              .tupleTail wHead.1 ::
                .append (.tupleHeads (.expression tail) fuel wHeads live) :: wStack,
              wEmitted⟩) := by
        simp [Checked.machine, RecursiveMachine.Checked.guardMachine,
          Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
          RecursiveMachine.Checked.taskReady,
          FirstSuccessRecursiveExecution.machine,
          FirstSuccessRecursiveExecution.next,
          FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
          running, Transition.relabel]
      have wStep1 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning wChildren,
            .tupleTail wHead.1 ::
              .append (.tupleHeads (.expression tail) fuel wHeads live) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .returning (RecursiveTasks.tupleTail wHead.1 wChildren),
              .append (.tupleHeads (.expression tail) fuel wHeads live) :: wStack,
              wEmitted⟩) := rfl
      have wStep2 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning (RecursiveTasks.tupleTail wHead.1 wChildren),
            .append (.tupleHeads (.expression tail) fuel wHeads live) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .work (.tupleHeads (.expression tail) fuel wHeads live),
              .prepend (RecursiveTasks.tupleTail wHead.1 wChildren) :: wStack,
              wEmitted⟩) := rfl
      have wStep3 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning wRest,
            .prepend (RecursiveTasks.tupleTail wHead.1 wChildren) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space,
              .returning (RecursiveTasks.tupleTail wHead.1 wChildren ++ wRest),
              wStack, wEmitted⟩) := rfl
      have childrenRel := ScopedResultRel.forall2_tupleTail headRel.1.symm
        childRun.results_rel
      have sourceRunning : ¬IsEmptyOrErrorRel cHead.1.erase := by
        rw [← headRel.1, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
        simpa only [Bool.not_eq_true] using running
      have childSource := ScopedTupleDerivation.to_completed_tupleRel childDerivation
      have source : Completed.TupleBranchesRel space hostDispatch
          Completed.scopedLookup live scope ctxTail (cHead :: cHeads)
          (cChildren.map (Completed.tuplePrepend cHead.1) ++ cRest)
          (policy := policy) :=
        .continuing sourceRunning (by simpa only [headRel.1] using childSource)
          (ScopedTupleBranchesDerivation.to_completed_tupleBranchesRel restDerivation)
      refine ⟨by omega,
        ScopedResultRel.forall2_append childrenRel restRun.results_rel, ?_,
        RecursiveExecution.Contextual.branches_complete source cStack⟩
      intro budget
      rw [show (childSteps + restSteps + 4) + budget =
          (childSteps + (((restSteps + (budget + 1)) + 1) + 1)) + 1 by omega,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep0,
        childRun.worker_run (((restSteps + (budget + 1)) + 1) + 1),
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep1,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep2,
        restRun.worker_run (budget + 1),
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep3]
termination_by steps
decreasing_by all_goals omega

end


/-! ### Ordinary call and call-list realization

The ordinary call profile contains error passthrough, an empty equation
frontier, and a nonempty equation frontier.  Embedded minimal instructions are
owned by the separate minimal-instruction profile.  Keeping that boundary
explicit avoids turning ordinary equation recursion into a meta-interpreter
mutual block. -/

/-- Structural admission for an ordinary call whose complete equation query
has no occurrence.  It contains the worker query equations and independent
contextual frontier, but no execution premise. -/
structure ScopedAbsentCallAdmission
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch)
    (expr expected : Atom) (wB : Bindings) (fuel : Nat)
    (live : List Atom) (ctxVal : Entry.Value) (cFrame : Completed.Frame) : Prop where
  value_erase : ctxVal.erase = expr
  not_error : isErrorAtom expr = false
  not_executable : ∀ op args,
    expr = .expression (op :: args) → dispatch.isExecutable op = false
  non_grounded : NonGroundedCallRel hostDispatch ctxVal.erase
  not_minimal : minimalInstruction expr = false
  query_covered :
    queryEquationsCovered (equationScope live expr expected wB)
      space expr fuel = true
  query_nil :
    queryEquationsAvoiding (equationScope live expr expected wB)
      space expr fuel = []
  frontier_nil :
    Spec.Eval.Steps.EquationFrontierRel space (expected :: live)
      ctxVal.erase cFrame.bindings []
  input_activation : ScopedActivationRel wB cFrame

/-- Earned calls in the ordinary equation profile. -/
inductive ScopedOrdinaryCallDerivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension] :
    Nat → Nat → List Atom → List String → Atom → Entry.Value → Atom →
    Bindings → Completed.Frame →
    List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation →
    ResultSet → List Completed.Result → Prop where
  | error
      (fuel : Nat) (live : List Atom) (scope : List String)
      (value expected : Atom) (ctxVal : Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (valueEq : ctxVal.erase = value)
      (isError : isErrorAtom value = true)
      (actRel : ScopedActivationRel wB cFrame) :
      ScopedOrdinaryCallDerivation space dispatch hostDispatch policy
        wEmitted cEmitted (fuel + 1) 2 live scope value ctxVal expected
        wB cFrame wStack cStack [(value, wB)] [(ctxVal, cFrame)]
  | absent
      (fuel : Nat) (live : List Atom) (scope : List String)
      (expr expected : Atom) (ctxVal : Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (admission : ScopedAbsentCallAdmission space dispatch hostDispatch
        expr expected wB fuel live ctxVal cFrame) :
      ScopedOrdinaryCallDerivation space dispatch hostDispatch policy
        wEmitted cEmitted (fuel + 1) 11 live scope expr ctxVal expected
        wB cFrame wStack cStack [(expr, wB)] [(ctxVal, cFrame)]
  | equations
      (depth eqSteps prodSteps retSteps : Nat)
      (live : List Atom) (scope : List String)
      (expr expected : Atom) (ctxCall : Entry.Value)
      (wB : Bindings) (cFrame : Completed.Frame)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (rows : List (Atom × Bindings))
      (works : List Spec.Eval.Steps.EquationWork)
      (bodyResults prodResults finalResults : ResultSet)
      (ctxProdResults ctxFinalResults : List Completed.Result)
      (readDepth : Nat)
      (admission : ScopedEquationCallAdmission space dispatch hostDispatch
        expr expected wB depth live ctxCall cFrame rows works bodyResults
        finalResults readDepth)
      (equationDerivation : ScopedEquationDerivation space dispatch hostDispatch
        policy wEmitted cEmitted expr expected wB depth live scope ctxCall cFrame
        eqSteps prodSteps retSteps wStack cStack rows works bodyResults prodResults
        ctxProdResults finalResults ctxFinalResults) :
      ScopedOrdinaryCallDerivation space dispatch hostDispatch policy
        wEmitted cEmitted (depth + 2) (eqSteps + prodSteps + retSteps + 5)
        live scope expr ctxCall expected wB cFrame wStack cStack
        finalResults ctxFinalResults

/-- Ordered realization of every ordinary call occurrence in a returned tuple
batch. -/
inductive ScopedOrdinaryCallsDerivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension] :
    Nat → Nat → List Atom → List String → Atom →
    ResultSet → List Completed.Result →
    List RecursiveTasks.Frame → List RecursiveTasks.Contextual.Continuation →
    ResultSet → List Completed.Result → Prop where
  | nil
      (fuel : Nat) (live : List Atom) (scope : List String) (expected : Atom)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation) :
      ScopedOrdinaryCallsDerivation space dispatch hostDispatch policy
        wEmitted cEmitted fuel 1 live scope expected [] [] wStack cStack [] []
  | cons
      (fuel childSteps restSteps : Nat)
      (live : List Atom) (scope : List String) (expected : Atom)
      (wHead : ResultPair) (cHead : Completed.Result)
      (wHeads wChildren wRest : ResultSet)
      (cHeads cChildren cRest : List Completed.Result)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (headRel : ScopedResultRel wHead cHead)
      (childDerivation : ScopedOrdinaryCallDerivation space dispatch hostDispatch
        policy wEmitted cEmitted fuel childSteps live scope wHead.1 cHead.1 expected
        wHead.2 cHead.2
        (.append (.calls expected fuel wHeads live) :: wStack)
        (.append (.calls live scope expected cHeads) :: cStack)
        wChildren cChildren)
      (restDerivation : ScopedOrdinaryCallsDerivation space dispatch hostDispatch
        policy wEmitted cEmitted fuel restSteps live scope expected wHeads cHeads
        (.prepend wChildren :: wStack) (.prepend cChildren :: cStack)
        wRest cRest) :
      ScopedOrdinaryCallsDerivation space dispatch hostDispatch policy
        wEmitted cEmitted fuel (childSteps + restSteps + 3) live scope expected
        (wHead :: wHeads) (cHead :: cHeads) wStack cStack
        (wChildren ++ wRest) (cChildren ++ cRest)

/-- Ordinary call admissions reconstruct the corresponding authoritative
completed call judgment. -/
theorem ScopedOrdinaryCallDerivation.to_completed_callRel
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {fuel steps : Nat} {live : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedOrdinaryCallDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel steps live scope value ctxVal expected wB cFrame
      wStack cStack wResults cResults) :
    Completed.CallRel space hostDispatch Completed.scopedLookup live scope
      ctxVal expected cFrame cResults (policy := policy) := by
  cases derivation
  case error isError valueEq _actRel =>
      exact Completed.CallRel.error (by
        rw [valueEq]
        rw [Conformance.isErrorRel_iff_isErrorAtom]
        exact isError)
  case absent admission =>
      exact .absent (by
        rw [admission.value_erase, Conformance.isErrorRel_iff_isErrorAtom]
        simp [admission.not_error]) admission.non_grounded admission.frontier_nil
  case equations admission equationDerivation =>
      exact .equations (by
        rw [admission.value_erase, Conformance.isErrorRel_iff_isErrorAtom]
        simp [admission.not_error]) admission.non_grounded admission.frontier
        admission.works_nonempty
        (ScopedEquationDerivation.to_completed_equationBodiesRel equationDerivation)

/-- The ordinary call-list proof object reconstructs `CallsRel`, including
ordered concatenation of every child batch. -/
theorem ScopedOrdinaryCallsDerivation.to_completed_callsRel
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {fuel steps : Nat} {live : List Atom} {scope : List String}
    {expected : Atom} {wRows : ResultSet} {cRows : List Completed.Result}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedOrdinaryCallsDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel steps live scope expected wRows cRows
      wStack cStack wResults cResults) :
    Completed.CallsRel space hostDispatch Completed.scopedLookup live scope
      expected cRows cResults (policy := policy) := by
  induction derivation with
  | nil fuel live expected wStack cStack => exact .nil
  | cons fuel childSteps restSteps live expected wHead cHead wHeads
      wChildren wRest cHeads cChildren cRest wStack cStack headRel
      childDerivation restDerivation ih =>
      exact .cons
        (ScopedOrdinaryCallDerivation.to_completed_callRel childDerivation)
        ih


/-- Every structurally admitted ordinary call earns its exact checked-worker
run.  The contextual run is derived independently from the reconstructed
`CallRel`; neither side is an admission premise. -/
theorem ScopedOrdinaryCallDerivation.task_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {fuel steps : Nat} {live : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedOrdinaryCallDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel steps live scope value ctxVal expected wB cFrame
      wStack cStack wResults cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.call value expected wB fuel live)
      (.call live scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted steps wResults cResults := by
  have source := ScopedOrdinaryCallDerivation.to_completed_callRel derivation
  cases derivation
  case error baseFuel isError valueEq actRel =>
      have wStep0 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.call value expected wB (baseFuel + 1) live),
            wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.invocation (.ordinary expected) value wB
              (baseFuel + 1) live none), wStack, wEmitted⟩) := rfl
      have wStep1 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.invocation (.ordinary expected) value wB
            (baseFuel + 1) live none), wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(value, wB)], wStack, wEmitted⟩) := by
        simp [Checked.machine, RecursiveMachine.Checked.guardMachine,
          Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
          RecursiveMachine.Checked.taskReady,
          FirstSuccessRecursiveExecution.machine,
          FirstSuccessRecursiveExecution.next,
          FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
          InvocationMode.errorPassthrough, isError, Transition.relabel]
      refine ⟨by omega, .cons ⟨valueEq.symm, actRel⟩ .nil, ?_,
        RecursiveExecution.Contextual.call_complete source cStack⟩
      intro budget
      rw [show 2 + budget = (budget + 1) + 1 by omega,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep0,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep1]
  case absent fuel admission =>
      have wStep0 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.call value expected wB (fuel + 1) live),
            wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.invocation (.ordinary expected) value wB
              (fuel + 1) live none), wStack, wEmitted⟩) := rfl
      have noPass : (InvocationMode.ordinary expected).errorPassthrough value = false := by
        simpa [InvocationMode.errorPassthrough] using admission.not_error
      have wStep1 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.invocation (.ordinary expected) value wB
            (fuel + 1) live none), wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.equations value expected wB fuel [] live),
              .producerResults (.ordinary expected) value wB fuel live
                Atom.notReducible :: wStack, wEmitted⟩) := by
        have step := worker_invocation_query_step space dispatch (.ordinary expected)
          value wB fuel live none wStack wEmitted noPass admission.not_executable
          admission.not_minimal admission.query_covered
        simpa only [InvocationMode.expected, admission.query_nil] using step
      have wStep2 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.equations value expected wB fuel [] live),
            .producerResults (.ordinary expected) value wB fuel live
              Atom.notReducible :: wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [],
              .producerResults (.ordinary expected) value wB fuel live
                Atom.notReducible :: wStack, wEmitted⟩) := rfl
      have wStep3 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [],
            .producerResults (.ordinary expected) value wB fuel live
              Atom.notReducible :: wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.producerResults (.ordinary expected) value wB fuel
              live Atom.notReducible []), wStack, wEmitted⟩) := rfl
      have wStep4 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.producerResults (.ordinary expected) value wB fuel
            live Atom.notReducible []), wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(Atom.notReducible, wB)],
              .invocationReturn (.ordinary expected) value fuel live :: wStack,
              wEmitted⟩) := rfl
      have wStep5 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [(Atom.notReducible, wB)],
            .invocationReturn (.ordinary expected) value fuel live :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .work (.returns value expected fuel
              [(Atom.notReducible, wB)] live), wStack, wEmitted⟩) := rfl
      have wStep6 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.returns value expected fuel
            [(Atom.notReducible, wB)] live), wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.returned value Atom.notReducible expected wB fuel live),
              .append (.returns value expected fuel [] live) :: wStack,
              wEmitted⟩) := rfl
      have wStep7 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.returned value Atom.notReducible expected wB fuel live),
            .append (.returns value expected fuel [] live) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(value, wB)],
              .append (.returns value expected fuel [] live) :: wStack,
              wEmitted⟩) := rfl
      have wStep8 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [(value, wB)],
            .append (.returns value expected fuel [] live) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .work (.returns value expected fuel [] live),
              .prepend [(value, wB)] :: wStack, wEmitted⟩) := rfl
      have wStep9 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.returns value expected fuel [] live),
            .prepend [(value, wB)] :: wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning [], .prepend [(value, wB)] :: wStack,
              wEmitted⟩) := rfl
      have wStep10 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning [], .prepend [(value, wB)] :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .returning [(value, wB)], wStack, wEmitted⟩) := rfl
      refine ⟨by omega,
        .cons ⟨admission.value_erase.symm, admission.input_activation⟩ .nil,
        ?_, RecursiveExecution.Contextual.call_complete source cStack⟩
      intro budget
      rw [show 11 + budget =
          (((((((((((budget + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
          by omega,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep0,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep1,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep2,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep3,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep4,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep5,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep6,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep7,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep8,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep9,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep10]
  case equations admission equationDerivation =>
      have spine := ScopedEquationDerivation.to_concreteSpine equationDerivation
      have realized := ScopedConcreteEquationWorksSpine.call_run spine
        admission.value_erase admission.not_error admission.not_executable
        admission.non_grounded admission.not_minimal admission.query_covered
        admission.query_eq admission.bodies_nonempty admission.frontier
        admission.works_nonempty
      exact ⟨by omega, realized.1, realized.2.1, realized.2.2.2⟩

/-- The ordinary calls spine earns exact checked-worker execution and the
independently reconstructed contextual `CallsRel`, preserving occurrence order
and duplicate child batches. -/
theorem ScopedOrdinaryCallsDerivation.task_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {fuel steps : Nat} {live : List Atom} {scope : List String}
    {expected : Atom} {wRows : ResultSet} {cRows : List Completed.Result}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedOrdinaryCallsDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel steps live scope expected wRows cRows
      wStack cStack wResults cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.calls expected fuel wRows live)
      (.calls live scope expected cRows)
      wStack cStack wEmitted cEmitted steps wResults cResults := by
  induction derivation with
  | nil live scope expected wStack cStack =>
      have wStep : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.calls expected fuel [] live), wStack, wEmitted⟩ =
          some (.silent ⟨space, .returning [], wStack, wEmitted⟩) := rfl
      refine ⟨by omega, .nil, ?_,
        RecursiveExecution.Contextual.calls_complete
          (Completed.CallsRel.nil (space := space) (dispatch := hostDispatch)
            (lookup := Completed.scopedLookup) (live := live) (scope := scope)
            (expected := expected) (policy := policy)) cStack⟩
      intro budget
      rw [Nat.add_comm 1 budget,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep]
  | cons childSteps restSteps live scope expected wHead cHead wHeads
      wChildren wRest cHeads cChildren cRest wStack cStack headRel
      childDerivation restDerivation ih =>
      have childRun := ScopedOrdinaryCallDerivation.task_run childDerivation
      have source : Completed.CallsRel space hostDispatch Completed.scopedLookup
          live scope expected (cHead :: cHeads) (cChildren ++ cRest)
          (policy := policy) :=
        .cons (ScopedOrdinaryCallDerivation.to_completed_callRel childDerivation)
          (ScopedOrdinaryCallsDerivation.to_completed_callsRel restDerivation)
      have wStep0 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .work (.calls expected fuel (wHead :: wHeads) live),
            wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .work (.call wHead.1 expected wHead.2 fuel live),
              .append (.calls expected fuel wHeads live) :: wStack,
              wEmitted⟩) := rfl
      have wStep1 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning wChildren,
            .append (.calls expected fuel wHeads live) :: wStack,
            wEmitted⟩ =
          some (.silent
            ⟨space, .work (.calls expected fuel wHeads live),
              .prepend wChildren :: wStack, wEmitted⟩) := rfl
      have wStep2 : (Checked.machine dispatch scopedTypes).step
          ⟨space, .returning wRest, .prepend wChildren :: wStack, wEmitted⟩ =
          some (.silent
            ⟨space, .returning (wChildren ++ wRest), wStack, wEmitted⟩) := rfl
      refine ⟨by omega,
        ScopedResultRel.forall2_append childRun.results_rel ih.results_rel, ?_,
        RecursiveExecution.Contextual.calls_complete source cStack⟩
      intro budget
      rw [show (childSteps + restSteps + 3) + budget =
          (childSteps + ((restSteps + (budget + 1)) + 1)) + 1 by omega,
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep0,
        childRun.worker_run ((restSteps + (budget + 1)) + 1),
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep1,
        ih.worker_run (budget + 1),
        (Checked.machine dispatch scopedTypes).run_succ_silent wStep2]

/-- A single absent ordinary call is the canonical one-row calls spine. -/
theorem ScopedOrdinaryCallsDerivation.singleton_absent
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    {baseFuel : Nat} {live : List Atom} {scope : List String}
    {expr expected : Atom} {ctxVal : Entry.Value}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    (rowRel : ScopedResultRel (expr, wB) (ctxVal, cFrame))
    (admission : ScopedAbsentCallAdmission space dispatch hostDispatch
      expr expected wB baseFuel live ctxVal cFrame) :
    ScopedOrdinaryCallsDerivation space dispatch hostDispatch policy
      wEmitted cEmitted (baseFuel + 1) 15 live scope expected
      [(expr, wB)] [(ctxVal, cFrame)] wStack cStack
      [(expr, wB)] [(ctxVal, cFrame)] := by
  have child : ScopedOrdinaryCallDerivation space dispatch hostDispatch policy
      wEmitted cEmitted (baseFuel + 1) 11 live scope expr ctxVal expected
      wB cFrame
      (.append (.calls expected (baseFuel + 1) [] live) :: wStack)
      (.append (.calls live scope expected []) :: cStack)
      [(expr, wB)] [(ctxVal, cFrame)] :=
    .absent baseFuel live scope expr expected ctxVal wB cFrame
      (.append (.calls expected (baseFuel + 1) [] live) :: wStack)
      (.append (.calls live scope expected []) :: cStack) admission
  have rest : ScopedOrdinaryCallsDerivation space dispatch hostDispatch policy
      wEmitted cEmitted (baseFuel + 1) 1 live scope expected [] []
      (.prepend [(expr, wB)] :: wStack)
      (.prepend [(ctxVal, cFrame)] :: cStack) [] [] :=
    .nil (baseFuel + 1) live scope expected
      (.prepend [(expr, wB)] :: wStack)
      (.prepend [(ctxVal, cFrame)] :: cStack)
  exact .cons (baseFuel + 1) 11 1 live scope expected
    (expr, wB) (ctxVal, cFrame) [] [(expr, wB)] [] []
    [(ctxVal, cFrame)] [] wStack cStack rowRel child rest


/-! ### Tuple-fallback composition boundary -/

/-- Exact ordered alignment is restored after tuple-fallback diagnostics when
there are no diagnostics, no tuple-call results, or at least one successful
tuple-call result.  The excluded all-error/two-nonempty case remains related by
`ScopedEmittedBagRel`, since the worker prepends diagnostics while the source
appends them. -/
theorem ScopedResultRel.forall2_fallbackPriority
    (policy : Policy) (original : Atom) (errors : List Atom)
    (wB : Bindings) (cFrame : Completed.Frame)
    (wRaw : ResultSet) (cRaw : List Completed.Result) (readDepth : Nat)
    (rawRel : List.Forall₂ ScopedResultRel wRaw cRaw)
    (diagReadRel : List.Forall₂ ScopedResultRel
      (errors.map fun error => (error, wB))
      ((Completed.diagnosticResults errors cFrame).map
        (Completed.readResult policy)))
    (rawCovered : ∀ pair ∈ wRaw,
      pair.2.applyFullCovered pair.1 readDepth = true)
    (rawStable : ∀ pair ∈ wRaw,
      pair.2.applyFull pair.1 readDepth = pair.1)
    (errorsAllErr : ∀ error ∈ errors, isErrorAtom error = true)
    (orderAligned : errors = [] ∨ wRaw = [] ∨
      ∃ pair ∈ wRaw, isErrorAtom pair.1 = false) :
    let wDiag : ResultSet := errors.map fun error => (error, wB)
    let cDiag := Completed.diagnosticResults errors cFrame
    let cSelected := completedSuccessPriority
      ((cRaw ++ cDiag).map (Completed.readResult policy))
    List.Forall₂ ScopedResultRel
      (successPriority (wDiag ++ wRaw))
      (cSelected.map (Completed.publishResult policy original)) := by
  intro wDiag cDiag cSelected
  have rawReadRel : List.Forall₂ ScopedResultRel wRaw
      (cRaw.map (Completed.readResult policy)) :=
    ScopedResultRel.forall2_materialized_readResult_stable policy rawRel
      readDepth rawCovered rawStable
  rcases orderAligned with noErrors | noRaw | hasSuccess
  · subst errors
    simpa [wDiag, cDiag, cSelected, Completed.diagnosticResults] using
      (ScopedResultRel.forall2_publishResult policy original
        (ScopedResultRel.forall2_successPriority rawReadRel))
  · subst wRaw
    cases rawRel
    simpa [wDiag, cDiag, cSelected, Completed.diagnosticResults] using
      (ScopedResultRel.forall2_publishResult policy original
        (ScopedResultRel.forall2_successPriority diagReadRel))
  · have wDiagAllErr : ∀ pair ∈ wDiag, isErrorAtom pair.1 = true := by
      intro pair member
      obtain ⟨error, errorMem, rfl⟩ := List.mem_map.mp member
      exact errorsAllErr error errorMem
    have cDiagAllErr : ∀ row ∈ cDiag.map (Completed.readResult policy),
        isErrorAtom row.1.erase = true :=
      forall2_scopedResultRel_all_errors diagReadRel wDiagAllErr
    have cHasSuccess : ∃ row ∈ cRaw.map (Completed.readResult policy),
        isErrorAtom row.1.erase = false :=
      forall2_scopedResultRel_has_success rawReadRel hasSuccess
    have wPriority : successPriority (wDiag ++ wRaw) = successPriority wRaw :=
      successPriority_prepend_errors_of_has_success wDiagAllErr hasSuccess
    have cPriority : cSelected =
        completedSuccessPriority (cRaw.map (Completed.readResult policy)) := by
      simp only [cSelected, List.map_append]
      exact completedSuccessPriority_append_errors_of_has_success
        cDiagAllErr cHasSuccess
    rw [wPriority, cPriority]
    exact ScopedResultRel.forall2_publishResult policy original
      (ScopedResultRel.forall2_successPriority rawReadRel)

/-- Compose the first-success tuple-fallback prefix, earned tuple recursion,
earned ordinary calls, diagnostic restoration, and final success priority.
Child executions are local realization contracts supplied by structural
derivations; the contextual result is reconstructed from the independent
source judgments. -/
theorem ScopedBagTaskRun.atomFallback_of_parts
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator : Atom) (arguments : List Atom) (expected : Atom)
    (wB : Bindings) (fuel : Nat) (live : List Atom) (scope : List String)
    (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
    (cFrame : Completed.Frame) (readiness : Entry.Status)
    (candidates errors : List Atom)
    (wTupleRows wRaw : ResultSet)
    (cTupleRows cRaw : List Completed.Result)
    (tupleSteps callsSteps readDepth : Nat)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (admission : ScopedTupleFallbackAdmission space policy operator arguments expected
      wB fuel live scope ctxVal ctxOp ctxArgs cFrame readiness candidates errors
      wStack wEmitted)
    (tupleSource : Completed.TupleRel space hostDispatch Completed.scopedLookup
      (expected :: live) scope (ctxOp :: ctxArgs) cFrame cTupleRows
      (policy := policy))
    (callsSource : Completed.CallsRel space hostDispatch Completed.scopedLookup
      live scope expected cTupleRows cRaw (policy := policy))
    (tupleRun : ScopedTaskRun space dispatch hostDispatch policy
      (.tuple (.expression (operator :: arguments)) wB fuel (expected :: live))
      (.tuple (expected :: live) scope (ctxOp :: ctxArgs) cFrame)
      (.calls expected fuel live ::
        .prepend (errors.map fun error => (error, wB)) :: .filter :: wStack)
      (.calls live scope expected :: .diagnostics errors cFrame ::
        .publish (.expression (operator :: arguments)) :: cStack)
      wEmitted cEmitted tupleSteps wTupleRows cTupleRows)
    (callsRun : ScopedTaskRun space dispatch hostDispatch policy
      (.calls expected fuel wTupleRows live)
      (.calls live scope expected cTupleRows)
      (.prepend (errors.map fun error => (error, wB)) :: .filter :: wStack)
      (.diagnostics errors cFrame ::
        .publish (.expression (operator :: arguments)) :: cStack)
      wEmitted cEmitted callsSteps wRaw cRaw)
    (rawCovered : ∀ pair ∈ wRaw,
      pair.2.applyFullCovered pair.1 readDepth = true)
    (rawStable : ∀ pair ∈ wRaw,
      pair.2.applyFull pair.1 readDepth = pair.1) :
    let expr := Atom.expression (operator :: arguments)
    let wDiag : ResultSet := errors.map fun error => (error, wB)
    let cDiag := Completed.diagnosticResults errors cFrame
    let cSelected := completedSuccessPriority
      ((cRaw ++ cDiag).map (Completed.readResult policy))
    let cPublished := cSelected.map (Completed.publishResult policy expr)
    ScopedBagTaskRun space dispatch hostDispatch policy
      (.atom expr expected wB (fuel + 2) live)
      (.atom live scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted (tupleSteps + callsSteps + 7)
      (successPriority (wDiag ++ wRaw)) cPublished := by
  intro expr wDiag cDiag cSelected cPublished
  let w0 : Configuration :=
    ⟨space, .work (.atom expr expected wB (fuel + 2) live), wStack, wEmitted⟩
  let w1 : Configuration :=
    ⟨space, .work (.expression expr expected wB (fuel + 1) live),
      .filter :: wStack, wEmitted⟩
  let w2 : Configuration :=
    ⟨space, .work (.functions expr expected wB fuel candidates live),
      .filter :: wStack, wEmitted⟩
  let w3 : Configuration :=
    ⟨space, .work (.tupleCalls expr expected wB fuel live),
      .prepend wDiag :: .filter :: wStack, wEmitted⟩
  let w4 : Configuration :=
    ⟨space, .work (.tuple expr wB fuel (expected :: live)),
      .calls expected fuel live :: .prepend wDiag :: .filter :: wStack,
      wEmitted⟩
  let w5 : Configuration :=
    ⟨space, .work (.calls expected fuel wTupleRows live),
      .prepend wDiag :: .filter :: wStack, wEmitted⟩
  let w6 : Configuration :=
    ⟨space, .returning (wDiag ++ wRaw), .filter :: wStack, wEmitted⟩
  let w7 : Configuration :=
    ⟨space, .returning (successPriority (wDiag ++ wRaw)), wStack, wEmitted⟩
  have notVarT : Atom.expressionType ≠ Atom.variableType := by decide
  have notSymT : Atom.expressionType ≠ Atom.symbolType := by decide
  have notGrdT : Atom.expressionType ≠ Atom.groundedType := by decide
  have notUnit : expr ≠ Atom.unit := by simp [expr, Atom.unit]
  have step0 : (Checked.machine dispatch scopedTypes).step w0 = some (.silent w1) := by
    simp [w0, w1, expr, Checked.machine, RecursiveMachine.Checked.guardMachine,
      Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
      RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
      RecursiveMachine.enter, getMetaType, admission.input_not_stopped,
      admission.expected_not_atom, admission.expected_not_expression,
      notVarT, notSymT, notGrdT, notUnit, Transition.relabel]
  have step1 : (Checked.machine dispatch scopedTypes).step w1 = some (.silent w2) := by
    simp [w1, w2, expr, Checked.machine, RecursiveMachine.Checked.guardMachine,
      Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
      RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
      scopedTypes, admission.candidate_eq, Transition.relabel]
  have step2 : (Checked.machine dispatch scopedTypes).step w2 = some (.silent w3) := by
    simp [w2, w3, wDiag, expr, Checked.machine,
      RecursiveMachine.Checked.guardMachine, Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady, scopedTypes,
      admission.selection_ready, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
      admission.worker_exhausted, Transition.relabel]
  have step3 : (Checked.machine dispatch scopedTypes).step w3 = some (.silent w4) := by
    simp [w3, w4, Checked.machine, RecursiveMachine.Checked.guardMachine,
      Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
      RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
      RecursiveMachine.enter, Transition.relabel]
  have step4 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning wTupleRows,
        .calls expected fuel live :: .prepend wDiag :: .filter :: wStack,
        wEmitted⟩ = some (.silent w5) := rfl
  have step5 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning wRaw, .prepend wDiag :: .filter :: wStack, wEmitted⟩ =
      some (.silent w6) := rfl
  have step6 : (Checked.machine dispatch scopedTypes).step w6 = some (.silent w7) := rfl
  have workerRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run
        (tupleSteps + callsSteps + 7 + budget) w0 =
      (Checked.machine dispatch scopedTypes).run budget w7 := by
    intro budget
    rw [show tupleSteps + callsSteps + 7 + budget =
        ((((tupleSteps + (callsSteps + (budget + 2) + 1)) + 1) + 1) + 1) + 1 by omega,
      (Checked.machine dispatch scopedTypes).run_succ_silent step0,
      (Checked.machine dispatch scopedTypes).run_succ_silent step1,
      (Checked.machine dispatch scopedTypes).run_succ_silent step2,
      (Checked.machine dispatch scopedTypes).run_succ_silent step3,
      tupleRun.worker_run (callsSteps + (budget + 2) + 1),
      show callsSteps + (budget + 2) + 1 = (callsSteps + (budget + 2)) + 1 by omega,
      (Checked.machine dispatch scopedTypes).run_succ_silent step4,
      callsRun.worker_run (budget + 2),
      show budget + 2 = (budget + 1) + 1 by omega,
      (Checked.machine dispatch scopedTypes).run_succ_silent step5,
      (Checked.machine dispatch scopedTypes).run_succ_silent step6]
  have entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      (cFrame.read policy ctxVal).erase expected .interpret :=
    admission.entry_ready.entry_interpret admission.input_not_stopped
      admission.expected_not_atom admission.expected_not_expression
  have selectedAtRead : Completed.InvocationSelectionRel space Completed.scopedLookup
      policy live scope (cFrame.read policy ctxVal).erase ctxOp.erase expected cFrame
      (.exhausted errors true) := by
    simpa only [admission.entry_ready.2.1, admission.operator_erase] using
      admission.contextual_exhausted
  have source : Completed.AtomRel space hostDispatch Completed.scopedLookup live scope
      ctxVal expected cFrame cPublished (policy := policy) := by
    simpa only [admission.entry_ready.2.1, cPublished, cSelected, cDiag] using
      (Completed.AtomRel.fallback entered admission.read_shape selectedAtRead
        tupleSource callsSource
        (completedSuccessPriority_rel
          ((cRaw ++ Completed.diagnosticResults errors cFrame).map
            (Completed.readResult policy))))
  have rawReadRel : ScopedEmittedBagRel wRaw
      (cRaw.map (Completed.readResult policy)) :=
    ScopedEmittedBagRel.materialized_readResult_stable policy
      (ScopedEmittedBagRel.of_forall2 callsRun.results_rel)
      readDepth rawCovered rawStable
  have diagReadRel : ScopedEmittedBagRel wDiag
      (cDiag.map (Completed.readResult policy)) :=
    ScopedEmittedBagRel.of_forall2 admission.diagnostics_rel
  have combinedReadRel : ScopedEmittedBagRel (wDiag ++ wRaw)
      ((cRaw ++ cDiag).map (Completed.readResult policy)) := by
    rw [List.map_append]
    exact ScopedEmittedBagRel.append_comm_left rawReadRel diagReadRel
  have resultsRel : ScopedEmittedBagRel
      (successPriority (wDiag ++ wRaw)) cPublished := by
    simpa only [cSelected, cPublished] using
      ScopedEmittedBagRel.publishResult policy expr
        (ScopedEmittedBagRel.successPriority combinedReadRel)
  exact ⟨by omega, resultsRel, workerRun,
    RecursiveExecution.Contextual.atom_complete source cStack⟩

/-- Structural atom-level tuple fallback assembled from the earned tuple and
ordinary-call proof objects.  This wrapper contains no execution premise.  It
is deliberately separate from `ScopedAtomDerivation` until the recursive
family admits the observer-sensitive diagnostic-order branch. -/
structure ScopedFallbackAtomDerivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension]
    (operator : Atom) (arguments : List Atom) (expected : Atom)
    (wB : Bindings) (fuel : Nat) (live : List Atom) (scope : List String)
    (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
    (cFrame : Completed.Frame) (readiness : Entry.Status)
    (candidates errors : List Atom)
    (tupleSteps callsSteps readDepth : Nat)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wTupleRows wRaw : ResultSet)
    (cTupleRows cRaw : List Completed.Result) : Prop where
  admission : ScopedTupleFallbackAdmission space policy operator arguments expected
    wB fuel live scope ctxVal ctxOp ctxArgs cFrame readiness candidates errors
    wStack wEmitted
  tuple_derivation : ScopedTupleDerivation space dispatch hostDispatch policy
    wEmitted cEmitted scope fuel tupleSteps (expected :: live)
    (operator :: arguments) (ctxOp :: ctxArgs) wB cFrame
    (.calls expected fuel live ::
      .prepend (errors.map fun error => (error, wB)) :: .filter :: wStack)
    (.calls live scope expected :: .diagnostics errors cFrame ::
      .publish (.expression (operator :: arguments)) :: cStack)
    wTupleRows cTupleRows
  calls_derivation : ScopedOrdinaryCallsDerivation space dispatch hostDispatch policy
    wEmitted cEmitted fuel callsSteps live scope expected wTupleRows cTupleRows
    (.prepend (errors.map fun error => (error, wB)) :: .filter :: wStack)
    (.diagnostics errors cFrame ::
      .publish (.expression (operator :: arguments)) :: cStack)
    wRaw cRaw
  raw_covered : ∀ pair ∈ wRaw,
    pair.2.applyFullCovered pair.1 readDepth = true
  raw_stable : ∀ pair ∈ wRaw,
    pair.2.applyFull pair.1 readDepth = pair.1

/-- The structural fallback wrapper reconstructs the authoritative source
`AtomRel.fallback` judgment. -/
theorem ScopedFallbackAtomDerivation.to_completed_atomRel
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {operator : Atom} {arguments : List Atom} {expected : Atom}
    {wB : Bindings} {fuel : Nat} {live : List Atom} {scope : List String}
    {ctxVal ctxOp : Entry.Value} {ctxArgs : List Entry.Value}
    {cFrame : Completed.Frame} {readiness : Entry.Status}
    {candidates errors : List Atom}
    {tupleSteps callsSteps readDepth : Nat}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wTupleRows wRaw : ResultSet}
    {cTupleRows cRaw : List Completed.Result}
    (derivation : ScopedFallbackAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted operator arguments expected wB fuel live scope
      ctxVal ctxOp ctxArgs cFrame readiness candidates errors
      tupleSteps callsSteps readDepth wStack cStack
      wTupleRows wRaw cTupleRows cRaw) :
    let expr := Atom.expression (operator :: arguments)
    let cDiag := Completed.diagnosticResults errors cFrame
    let cSelected := completedSuccessPriority
      ((cRaw ++ cDiag).map (Completed.readResult policy))
    Completed.AtomRel space hostDispatch Completed.scopedLookup live scope
      ctxVal expected cFrame
      (cSelected.map (Completed.publishResult policy expr))
      (policy := policy) := by
  intro expr cDiag cSelected
  have entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      (cFrame.read policy ctxVal).erase expected .interpret :=
    derivation.admission.entry_ready.entry_interpret
      derivation.admission.input_not_stopped
      derivation.admission.expected_not_atom
      derivation.admission.expected_not_expression
  have selectedAtRead : Completed.InvocationSelectionRel space Completed.scopedLookup
      policy live scope (cFrame.read policy ctxVal).erase ctxOp.erase expected cFrame
      (.exhausted errors true) := by
    simpa only [derivation.admission.entry_ready.2.1,
      derivation.admission.operator_erase] using
      derivation.admission.contextual_exhausted
  have tupleSource := ScopedTupleDerivation.to_completed_tupleRel
    derivation.tuple_derivation
  have callsSource := ScopedOrdinaryCallsDerivation.to_completed_callsRel
    derivation.calls_derivation
  simpa only [derivation.admission.entry_ready.2.1, cDiag, cSelected] using
    (Completed.AtomRel.fallback entered derivation.admission.read_shape selectedAtRead
      tupleSource callsSource
      (completedSuccessPriority_rel
        ((cRaw ++ Completed.diagnosticResults errors cFrame).map
          (Completed.readResult policy))))

/-- Every structural fallback wrapper earns the unrestricted bag-observed run.
This is the principal realization for the diagnostic-order boundary. -/
theorem ScopedFallbackAtomDerivation.bag_task_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {operator : Atom} {arguments : List Atom} {expected : Atom}
    {wB : Bindings} {fuel : Nat} {live : List Atom} {scope : List String}
    {ctxVal ctxOp : Entry.Value} {ctxArgs : List Entry.Value}
    {cFrame : Completed.Frame} {readiness : Entry.Status}
    {candidates errors : List Atom}
    {tupleSteps callsSteps readDepth : Nat}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wTupleRows wRaw : ResultSet}
    {cTupleRows cRaw : List Completed.Result}
    (derivation : ScopedFallbackAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted operator arguments expected wB fuel live scope
      ctxVal ctxOp ctxArgs cFrame readiness candidates errors
      tupleSteps callsSteps readDepth wStack cStack
      wTupleRows wRaw cTupleRows cRaw) :
    let expr := Atom.expression (operator :: arguments)
    let wDiag : ResultSet := errors.map fun error => (error, wB)
    let cDiag := Completed.diagnosticResults errors cFrame
    let cSelected := completedSuccessPriority
      ((cRaw ++ cDiag).map (Completed.readResult policy))
    let cPublished := cSelected.map (Completed.publishResult policy expr)
    ScopedBagTaskRun space dispatch hostDispatch policy
      (.atom expr expected wB (fuel + 2) live)
      (.atom live scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted (tupleSteps + callsSteps + 7)
      (successPriority (wDiag ++ wRaw)) cPublished := by
  apply ScopedBagTaskRun.atomFallback_of_parts
    (admission := derivation.admission)
    (tupleSource := ScopedTupleDerivation.to_completed_tupleRel
      derivation.tuple_derivation)
    (callsSource := ScopedOrdinaryCallsDerivation.to_completed_callsRel
      derivation.calls_derivation)
    (tupleRun := ScopedTupleDerivation.task_run derivation.tuple_derivation)
    (callsRun := ScopedOrdinaryCallsDerivation.task_run derivation.calls_derivation)
    (rawCovered := derivation.raw_covered)
    (rawStable := derivation.raw_stable)

/-- The same structural wrapper refines to exact ordered completion when the
diagnostic/raw block order is observationally aligned. -/
theorem ScopedFallbackAtomDerivation.task_run
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
      wEmitted cEmitted]
    {operator : Atom} {arguments : List Atom} {expected : Atom}
    {wB : Bindings} {fuel : Nat} {live : List Atom} {scope : List String}
    {ctxVal ctxOp : Entry.Value} {ctxArgs : List Entry.Value}
    {cFrame : Completed.Frame} {readiness : Entry.Status}
    {candidates errors : List Atom}
    {tupleSteps callsSteps readDepth : Nat}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wTupleRows wRaw : ResultSet}
    {cTupleRows cRaw : List Completed.Result}
    (derivation : ScopedFallbackAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted operator arguments expected wB fuel live scope
      ctxVal ctxOp ctxArgs cFrame readiness candidates errors
      tupleSteps callsSteps readDepth wStack cStack
      wTupleRows wRaw cTupleRows cRaw)
    (errorsAllErr : ∀ error ∈ errors, isErrorAtom error = true)
    (orderAligned : errors = [] ∨ wRaw = [] ∨
      ∃ pair ∈ wRaw, isErrorAtom pair.1 = false) :
    let expr := Atom.expression (operator :: arguments)
    let wDiag : ResultSet := errors.map fun error => (error, wB)
    let cDiag := Completed.diagnosticResults errors cFrame
    let cSelected := completedSuccessPriority
      ((cRaw ++ cDiag).map (Completed.readResult policy))
    let cPublished := cSelected.map (Completed.publishResult policy expr)
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom expr expected wB (fuel + 2) live)
      (.atom live scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted (tupleSteps + callsSteps + 7)
      (successPriority (wDiag ++ wRaw)) cPublished := by
  intro expr wDiag cDiag cSelected cPublished
  have bagRun := ScopedFallbackAtomDerivation.bag_task_run derivation
  dsimp only at bagRun
  have resultsRel : List.Forall₂ ScopedResultRel
      (successPriority (wDiag ++ wRaw)) cPublished := by
    simpa only [wDiag, cDiag, cSelected, cPublished] using
      ScopedResultRel.forall2_fallbackPriority policy expr errors wB cFrame
        wRaw cRaw readDepth
        (ScopedOrdinaryCallsDerivation.task_run derivation.calls_derivation).results_rel
        derivation.admission.diagnostics_rel derivation.raw_covered
        derivation.raw_stable errorsAllErr orderAligned
  exact ⟨bagRun.positive, resultsRel, bagRun.worker_run,
    bagRun.contextual_steps⟩


/-! ### Ranked open-recursive fallback closure -/

/-- Turn a predicate into the fixed atom-extension parameter expected by the
recursive families. -/
@[instance_reducible] def scopedAtomExtensionOf
    (pred : ScopedAtomStepPred) : ScopedAtomExtension where
  pred := pred

/-- One additional fallback layer over an already available atom relation.
`lift` embeds every shallower atom, while `fallback` adds exactly the structural
fallback component proved above. -/
inductive ScopedFallbackAtomStep
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (InnerAtom : ScopedAtomStepPred) : ScopedAtomStepPred where
  | lift
      {fuel : Nat} {wLive cLive : List Atom} {scope : List String}
      {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
      {wB : Bindings} {cFrame : Completed.Frame}
      {wStack : List RecursiveTasks.Frame}
      {cStack : List RecursiveTasks.Contextual.Continuation}
      {steps : Nat} {wResults : ResultSet} {cResults : List Completed.Result}
      (previous : InnerAtom fuel wLive cLive scope value ctxVal expected wB cFrame
        wStack cStack steps wResults cResults) :
      ScopedFallbackAtomStep space dispatch hostDispatch policy wEmitted cEmitted
        InnerAtom fuel wLive cLive scope value ctxVal expected wB cFrame
        wStack cStack steps wResults cResults
  | fallback
      (operator : Atom) (arguments : List Atom) (expected : Atom)
      (wB : Bindings) (fuel : Nat) (live : List Atom) (scope : List String)
      (ctxVal ctxOp : Entry.Value) (ctxArgs : List Entry.Value)
      (cFrame : Completed.Frame) (readiness : Entry.Status)
      (candidates errors : List Atom)
      (tupleSteps callsSteps readDepth : Nat)
      (wStack : List RecursiveTasks.Frame)
      (cStack : List RecursiveTasks.Contextual.Continuation)
      (wTupleRows wRaw : ResultSet)
      (cTupleRows cRaw : List Completed.Result)
      (derivation : ScopedFallbackAtomDerivation
        (extension := scopedAtomExtensionOf InnerAtom)
        space dispatch hostDispatch policy wEmitted cEmitted
        operator arguments expected wB fuel live scope
        ctxVal ctxOp ctxArgs cFrame readiness candidates errors
        tupleSteps callsSteps readDepth wStack cStack
        wTupleRows wRaw cTupleRows cRaw)
      (errorsAllErr : ∀ error ∈ errors, isErrorAtom error = true)
      (orderAligned : errors = [] ∨ wRaw = [] ∨
        ∃ pair ∈ wRaw, isErrorAtom pair.1 = false) :
      ScopedFallbackAtomStep space dispatch hostDispatch policy wEmitted cEmitted
        InnerAtom (fuel + 2) live live scope
        (.expression (operator :: arguments)) ctxVal expected wB cFrame
        wStack cStack (tupleSteps + callsSteps + 7)
        (successPriority ((errors.map fun error => (error, wB)) ++ wRaw))
        ((completedSuccessPriority
          ((cRaw ++ Completed.diagnosticResults errors cFrame).map
            (Completed.readResult policy))).map
          (Completed.publishResult policy (.expression (operator :: arguments))))

/-- Arbitrary finite nesting of the fallback extension, stratified by the
number of fallback layers.  The recursion is ordinary recursion on `Nat`,
outside every dependent mutual derivation. -/
def ScopedRankedFallbackStep
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    Nat → ScopedAtomStepPred
  | 0 => ScopedNoExtraAtom
  | rank + 1 =>
      ScopedFallbackAtomStep space dispatch hostDispatch policy wEmitted cEmitted
        (ScopedRankedFallbackStep space dispatch hostDispatch policy
          wEmitted cEmitted rank)

/-- The fixed extension instance at fallback rank `rank`. -/
@[instance_reducible] def scopedRankedFallbackExtension
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (rank : Nat) : ScopedAtomExtension :=
  scopedAtomExtensionOf
    (ScopedRankedFallbackStep space dispatch hostDispatch policy
      wEmitted cEmitted rank)

/- Every finite fallback rank supplies the source and exact-worker component
laws required by the open-recursive families.  The proof recurses only on the
rank; dependent machine indices never enter a mutual well-founded package. -/
set_option linter.style.haveILetI false in
theorem scopedRankedFallbackLaws
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    (rank : Nat) →
      @ScopedAtomExtensionLaws space dispatch hostDispatch policy
        wEmitted cEmitted
        (scopedRankedFallbackExtension space dispatch hostDispatch policy
          wEmitted cEmitted rank)
  | 0 =>
      letI : ScopedAtomExtension :=
        scopedRankedFallbackExtension space dispatch hostDispatch policy
          wEmitted cEmitted 0
      { source := by
          intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ impossible
          exact False.elim impossible
        run := by
          intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ impossible
          exact False.elim impossible }
  | rank + 1 =>
      letI : ScopedAtomExtension :=
        scopedRankedFallbackExtension space dispatch hostDispatch policy
          wEmitted cEmitted (rank + 1)
      { source := by
          intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ step
          cases step with
          | lift previous =>
              exact ScopedAtomExtensionLaws.source
                (space := space) (dispatch := dispatch)
                (hostDispatch := hostDispatch) (policy := policy)
                (wEmitted := wEmitted) (cEmitted := cEmitted)
                (extension := scopedRankedFallbackExtension space dispatch
                  hostDispatch policy wEmitted cEmitted rank)
                (self := scopedRankedFallbackLaws space dispatch hostDispatch
                  policy wEmitted cEmitted rank) previous
          | fallback operator arguments expected wB fuel live scope ctxVal ctxOp
              ctxArgs cFrame readiness candidates errors tupleSteps callsSteps
              readDepth wStack cStack wTupleRows wRaw cTupleRows cRaw derivation
              errorsAllErr orderAligned =>
              letI : ScopedAtomExtension :=
                scopedRankedFallbackExtension space dispatch hostDispatch policy
                  wEmitted cEmitted rank
              let innerLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
                  wEmitted cEmitted :=
                scopedRankedFallbackLaws space dispatch hostDispatch policy
                  wEmitted cEmitted rank
              exact ScopedFallbackAtomDerivation.to_completed_atomRel
                (extensionLaws := innerLaws) derivation
        run := by
          intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ step
          cases step with
          | lift previous =>
              exact ScopedAtomExtensionLaws.run
                (space := space) (dispatch := dispatch)
                (hostDispatch := hostDispatch) (policy := policy)
                (wEmitted := wEmitted) (cEmitted := cEmitted)
                (extension := scopedRankedFallbackExtension space dispatch
                  hostDispatch policy wEmitted cEmitted rank)
                (self := scopedRankedFallbackLaws space dispatch hostDispatch
                  policy wEmitted cEmitted rank) previous
          | fallback operator arguments expected wB fuel live scope ctxVal ctxOp
              ctxArgs cFrame readiness candidates errors tupleSteps callsSteps
              readDepth wStack cStack wTupleRows wRaw cTupleRows cRaw derivation
              errorsAllErr orderAligned =>
              letI : ScopedAtomExtension :=
                scopedRankedFallbackExtension space dispatch hostDispatch policy
                  wEmitted cEmitted rank
              let innerLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy
                  wEmitted cEmitted :=
                scopedRankedFallbackLaws space dispatch hostDispatch policy
                  wEmitted cEmitted rank
              exact ScopedFallbackAtomDerivation.task_run
                (extensionLaws := innerLaws) derivation
                errorsAllErr orderAligned }

/-- Source elimination for a ranked fallback branch. -/
theorem ScopedRankedFallbackStep.to_completed_atomRel
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (rank : Nat)
    {fuel : Nat} {wLive cLive : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {wResults : ResultSet} {cResults : List Completed.Result}
    (branch : ScopedRankedFallbackStep space dispatch hostDispatch policy
      wEmitted cEmitted rank fuel wLive cLive scope value ctxVal expected
      wB cFrame wStack cStack steps wResults cResults) :
    Completed.AtomRel space hostDispatch Completed.scopedLookup cLive scope
      ctxVal expected cFrame cResults (policy := policy) :=
  ScopedAtomExtensionLaws.source
    (space := space) (dispatch := dispatch) (hostDispatch := hostDispatch)
    (policy := policy) (wEmitted := wEmitted) (cEmitted := cEmitted)
    (extension := scopedRankedFallbackExtension space dispatch hostDispatch policy
      wEmitted cEmitted rank)
    (self := scopedRankedFallbackLaws space dispatch hostDispatch policy
      wEmitted cEmitted rank) branch

/-- Exact checked-worker elimination for a ranked fallback branch. -/
theorem ScopedRankedFallbackStep.task_run
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (rank : Nat)
    {fuel : Nat} {wLive cLive : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {wResults : ResultSet} {cResults : List Completed.Result}
    (branch : ScopedRankedFallbackStep space dispatch hostDispatch policy
      wEmitted cEmitted rank fuel wLive cLive scope value ctxVal expected
      wB cFrame wStack cStack steps wResults cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom value expected wB fuel wLive)
      (.atom cLive scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted steps wResults cResults :=
  ScopedAtomExtensionLaws.run
    (space := space) (dispatch := dispatch) (hostDispatch := hostDispatch)
    (policy := policy) (wEmitted := wEmitted) (cEmitted := cEmitted)
    (extension := scopedRankedFallbackExtension space dispatch hostDispatch policy
      wEmitted cEmitted rank)
    (self := scopedRankedFallbackLaws space dispatch hostDispatch policy
      wEmitted cEmitted rank) branch

/- Embed one proved, order-aligned fallback layer into the next ranked atom
profile.  All inner tuple, call, argument, and equation recursion continues to
use the preceding rank. -/
set_option linter.style.haveILetI false in
theorem ScopedAtomDerivation.of_ranked_fallback
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (rank : Nat)
    {operator : Atom} {arguments : List Atom} {expected : Atom}
    {wB : Bindings} {fuel : Nat} {live : List Atom} {scope : List String}
    {ctxVal ctxOp : Entry.Value} {ctxArgs : List Entry.Value}
    {cFrame : Completed.Frame} {readiness : Entry.Status}
    {candidates errors : List Atom}
    {tupleSteps callsSteps readDepth : Nat}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wTupleRows wRaw : ResultSet}
    {cTupleRows cRaw : List Completed.Result}
    (derivation : ScopedFallbackAtomDerivation
      (extension := scopedRankedFallbackExtension space dispatch hostDispatch
        policy wEmitted cEmitted rank)
      space dispatch hostDispatch policy wEmitted cEmitted
      operator arguments expected wB fuel live scope
      ctxVal ctxOp ctxArgs cFrame readiness candidates errors
      tupleSteps callsSteps readDepth wStack cStack
      wTupleRows wRaw cTupleRows cRaw)
    (errorsAllErr : ∀ error ∈ errors, isErrorAtom error = true)
    (orderAligned : errors = [] ∨ wRaw = [] ∨
      ∃ pair ∈ wRaw, isErrorAtom pair.1 = false) :
    let expr := Atom.expression (operator :: arguments)
    let wDiag : ResultSet := errors.map fun error => (error, wB)
    let cDiag := Completed.diagnosticResults errors cFrame
    let cSelected := completedSuccessPriority
      ((cRaw ++ cDiag).map (Completed.readResult policy))
    let cPublished := cSelected.map (Completed.publishResult policy expr)
    ScopedAtomDerivation
      (extension := scopedRankedFallbackExtension space dispatch hostDispatch
        policy wEmitted cEmitted (rank + 1))
      space dispatch hostDispatch policy wEmitted cEmitted
      (fuel + 2) live live scope expr ctxVal expected wB cFrame
      wStack cStack (tupleSteps + callsSteps + 7)
      (successPriority (wDiag ++ wRaw)) cPublished := by
  intro expr wDiag cDiag cSelected cPublished
  letI : ScopedAtomExtension :=
    scopedRankedFallbackExtension space dispatch hostDispatch policy
      wEmitted cEmitted rank
  have branch : ScopedRankedFallbackStep space dispatch hostDispatch policy
      wEmitted cEmitted (rank + 1)
      (fuel + 2) live live scope expr ctxVal expected wB cFrame
      wStack cStack (tupleSteps + callsSteps + 7)
      (successPriority (wDiag ++ wRaw)) cPublished := by
    exact ScopedFallbackAtomStep.fallback
      (space := space) (dispatch := dispatch) (hostDispatch := hostDispatch)
      (policy := policy) (wEmitted := wEmitted) (cEmitted := cEmitted)
      (InnerAtom := ScopedRankedFallbackStep space dispatch hostDispatch policy
        wEmitted cEmitted rank)
      (derivation := derivation) (errorsAllErr := errorsAllErr)
      (orderAligned := orderAligned)
  have entryReady := derivation.admission.entry_ready
  have inputActivation := derivation.admission.input_activation
  exact ScopedAtomDerivation.extra
    (space := space) (dispatch := dispatch) (hostDispatch := hostDispatch)
    (policy := policy) (wEmitted := wEmitted) (cEmitted := cEmitted)
    (extension := scopedRankedFallbackExtension space dispatch hostDispatch policy
      wEmitted cEmitted (rank + 1))
    (fuel := fuel + 2) (wLive := live) (cLive := live) (scope := scope)
    (value := expr) (ctxVal := ctxVal) (expected := expected)
    (wB := wB) (cFrame := cFrame) (wStack := wStack) (cStack := cStack)
    (steps := tupleSteps + callsSteps + 7)
    (wResults := successPriority (wDiag ++ wRaw)) (cResults := cPublished)
    entryReady inputActivation branch


/-- Every admitted atom derivation starts from aligned payload and activation
frames. -/
theorem ScopedAtomDerivation.input_relation
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    {fuel : Nat} {wLive cLive : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults) :
    ctxVal.erase = value ∧ ScopedActivationRel wB cFrame := by
  cases derivation
  case empty_or_error depth stopped entryReady actRel =>
    exact ⟨entryReady.1, actRel⟩
  case type_pass depth notStopped typePass entryReady actRel =>
    exact ⟨entryReady.1, actRel⟩
  case cast admission =>
    exact ⟨admission.entry_ready.1, admission.input_activation⟩
  case selection_failed admission =>
    exact ⟨admission.entry_ready.1, admission.input_activation⟩
  case extra entryReady actRel branch => exact ⟨entryReady.1, actRel⟩
  case selected_function operator opVal arguments retVals ctxOp ctxOpVal ctxArgs ctxRetVals
      wBSelected wBHead wBArgs cFrameSelected cFrameHead cFrameArgs signature candidates
      rows works bodyResults prodResults finalResults ctxProdResults ctxFinalResults fuel
      opSteps argSteps eqSteps prodSteps retSteps readDepth readiness operatorResultRel
      callAdmission entry operatorDerivation argumentsDerivation equationDerivation =>
    exact ⟨entry.entry_ready.1, entry.input_activation⟩

/-- The recursive worker profile never admits an atom at a contextual entry
where materialization and reentry status disagree with the plain-atom worker. -/
theorem ScopedAtomDerivation.entry_ready
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    {fuel : Nat} {wLive cLive : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults) :
    ScopedAtomEntryReady policy value ctxVal cFrame := by
  cases derivation
  case empty_or_error depth stopped entryReady actRel => exact entryReady
  case type_pass depth notStopped typePass entryReady actRel => exact entryReady
  case cast admission => exact admission.entry_ready
  case selection_failed admission => exact admission.entry_ready
  case extra entryReady actRel branch => exact entryReady
  case selected_function operator opVal arguments retVals ctxOp ctxOpVal ctxArgs ctxRetVals
      wBSelected wBHead wBArgs cFrameSelected cFrameHead cFrameArgs signature candidates
      rows works bodyResults prodResults finalResults ctxProdResults ctxFinalResults fuel
      opSteps argSteps eqSteps prodSteps retSteps readDepth readiness operatorResultRel
      callAdmission entry operatorDerivation argumentsDerivation equationDerivation =>
    exact entry.entry_ready

/-- A completed source delivery at an admissible entry is either stopped or
an ordinary meta-type pass.  The held/reuse case is incompatible with the
worker's readiness disjunction. -/
private theorem entry_delivery_ready_cases
    {reentry : Entry.ReentryPolicy} {status : Entry.Status}
    {atom expected : Atom}
    (delivered : Entry.Rel reentry status atom expected .deliver)
    (ready : reentry = .reinterpret ∨ status = .active) :
    IsEmptyOrErrorRel atom ∨
      ∃ metaType, ¬IsEmptyOrErrorRel atom ∧ MetaTypeRel atom metaType ∧
        (expected = Atom.atomType ∨ expected = metaType ∨ metaType = Atom.variableType) := by
  cases delivered with
  | stopped stopped => exact Or.inl stopped
  | pass clean typed accepted => exact Or.inr ⟨_, clean, typed, accepted⟩
  | held clean rejected reuses held =>
      rcases ready with reinterpret | active
      · rw [reuses] at reinterpret
        cases reinterpret
      · rw [held] at active
        cases active

/-- Reflect an actual completed-source delivery classification into the earned
worker admission.  Stopped and ordinary pass cases become the corresponding
constructors; a held/reuse delivery contradicts `ScopedAtomEntryReady`, which
is precisely the plain-Atom worker's declared boundary. -/
theorem ScopedAtomDerivation.of_completed_delivered
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    [extension : ScopedAtomExtension]
    {depth : Nat} {wLive cLive : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    (entryReady : ScopedAtomEntryReady policy value ctxVal cFrame)
    (actRel : ScopedActivationRel wB cFrame)
    (delivered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      (cFrame.read policy ctxVal).erase expected .deliver) :
    ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
      (depth + 1) wLive cLive scope value ctxVal expected wB cFrame wStack cStack
      1 [(value, wB)] [(cFrame.read policy ctxVal, cFrame)] := by
  have classified := entry_delivery_ready_cases delivered entryReady.2.2
  rcases classified with stopped | ⟨metaType, clean, typed, accepted⟩
  ·
      apply ScopedAtomDerivation.empty_or_error depth wLive cLive scope value expected
        ctxVal wB cFrame wStack cStack entryReady
      · exact (Conformance.isEmptyOrErrorRel_iff_isEmptyOrError value).mp
          (entryReady.2.1 ▸ stopped)
      · exact actRel
  ·
      have cleanValue : ¬IsEmptyOrErrorRel value := by
        simpa only [entryReady.2.1] using clean
      have notStopped : isEmptyOrError value = false := by
        apply Bool.eq_false_iff.mpr
        intro stopped
        exact cleanValue ((Conformance.isEmptyOrErrorRel_iff_isEmptyOrError value).mpr stopped)
      have metaEq : getMetaType value = metaType := by
        have source := (Conformance.metaTypeRel_iff_getMetaType _ _).mp typed
        simpa only [entryReady.2.1] using source
      rw [← metaEq] at accepted
      exact ScopedAtomDerivation.type_pass depth wLive cLive scope value expected
        ctxVal wB cFrame wStack cStack entryReady notStopped accepted actRel


/-- Negative reentry control: a held contextual read under `.reuse` cannot be
represented by the plain-atom recursive profile. -/
theorem held_reuse_not_admitted
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {fuel : Nat} {live : List Atom} {scope : List String}
    {value expected : Atom} {ctxVal : Entry.Value}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    (reuses : policy.reentry = .reuse)
    (held : (cFrame.read policy ctxVal).status = .held) :
    ¬∃ steps wResults cResults,
      ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
        fuel live live scope value ctxVal expected wB cFrame wStack cStack
        steps wResults cResults := by
  rintro ⟨steps, wResults, cResults, derivation⟩
  rcases derivation.entry_ready.2.2 with reinterpret | active
  · rw [reuses] at reinterpret
    cases reinterpret
  · rw [held] at active
    cases active

/-- A top-level earned recursive atom derivation completes both machines,
preserves duplicate answer occurrences as a bag, and gives identical public
joint-binding observations for every requested scope. -/
theorem ScopedAtomDerivation.complete_and_drain_bag
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy [] []]
    {fuel steps : Nat} {live : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      [] [] fuel live live scope value ctxVal expected wB cFrame
      [] [] steps wResults cResults) :
    let wStart : Configuration :=
      ⟨space, .work (.atom value expected wB fuel live), [], []⟩
    let cStart : RecursiveTasks.Contextual.Configuration :=
      ⟨space, .work (.atom live scope ctxVal expected cFrame), [], []⟩
    let wCompleted : Configuration :=
      ⟨space, .returning [], [], wResults⟩
    let cCompleted : RecursiveTasks.Contextual.Configuration :=
      ⟨space, .returning [], [], cResults⟩
    ScopedBagConfigurationRel wCompleted cCompleted ∧
    ScopedEmittedBagRel wResults cResults ∧
    wCompleted.emitted.length = cCompleted.emitted.length ∧
    (∃ wBudget,
      (Checked.machine dispatch scopedTypes).run wBudget wStart =
        (wResults, .finished wCompleted)) ∧
    RecursiveMachine.Contextual.Steps hostDispatch Completed.scopedLookup policy
      cStart cCompleted ∧
    (∃ cBudget cEvents,
      Derivation
        (RecursiveExecution.Contextual.Protocol.Rule hostDispatch Completed.scopedLookup policy)
        cBudget cStart cEvents (.finished cCompleted.emitted)) ∧
    (∀ publicScope : List String,
      workerPublicAnswers publicScope wCompleted.emitted =
        RecursiveExecution.Contextual.Protocol.publicAnswers publicScope cCompleted.emitted ∧
      workerPublicAnswers publicScope wCompleted.emitted =
        (RecursiveExecution.Contextual.Protocol.readout publicScope).verdict
          cCompleted.emitted) := by
  intro wStart cStart wCompleted cCompleted
  have run := derivation.task_run
  have inputRel := derivation.input_relation
  have startRel : ScopedConfigurationRel wStart cStart :=
    ⟨rfl, .work (.atom inputRel.1 inputRel.2), .nil, .nil⟩
  have endRel : ScopedConfigurationRel
      ⟨space, .returning wResults, [], []⟩
      ⟨space, .returning cResults, [], []⟩ :=
    ⟨rfl, .returning run.results_rel, .nil, .nil⟩
  have wRun : (Checked.machine dispatch scopedTypes).run steps wStart =
      ([], .exhausted ⟨space, .returning wResults, [], []⟩) :=
    (run.worker_run 0).trans rfl
  have cSilent : ContextualSilentPath hostDispatch Completed.scopedLookup policy
      cStart ⟨space, .returning cResults, [], []⟩ :=
    localSteps_to_contextualSilentPath run.contextual_steps
  have block : ScopedSilentBlock dispatch hostDispatch policy
      wStart cStart
      ⟨space, .returning wResults, [], []⟩
      ⟨space, .returning cResults, [], []⟩ :=
    ScopedSilentBlock.of_multi_step run.positive startRel endRel wRun cSilent
  exact (ScopedSilentBlockTrace.step block
    (.refl (ScopedConfigurationRel.to_bagConfigurationRel endRel))).complete_and_drain_bag

/-- Every admitted top-level worker derivation has the authoritative
independent completed atom judgment.  The proof is the stack-generic structural
reconstruction above; top-level execution is not used to recover semantics. -/
theorem ScopedAtomDerivation.contextual_source
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy [] []]
    {fuel steps : Nat} {live : List Atom} {scope : List String}
    {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      [] [] fuel live live scope value ctxVal expected wB cFrame
      [] [] steps wResults cResults) :
    Completed.AtomRel space hostDispatch Completed.scopedLookup
      live scope ctxVal expected cFrame cResults (policy := policy) := by
  exact derivation.to_completed_atomRel

/-- Positive non-vacuity control for the earned recursive interface.  A passive
symbol at atom demand constructs a derivation and completes the checked worker
with its exact occurrence. -/
theorem control_type_pass_derivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) :
    let value : Atom := .symbol "recursive-control"
    let ctxVal : Entry.Value := Entry.Value.ofAtom value
    ScopedAtomDerivation space dispatch hostDispatch Policy.unmarked
      [] [] 1 [] [] [] value ctxVal Atom.atomType Bindings.empty
      Completed.Frame.empty [] [] 1
      [(value, Bindings.empty)]
      [(Completed.Frame.empty.read Policy.unmarked ctxVal, Completed.Frame.empty)] ∧
      ∃ budget,
        (Checked.machine dispatch scopedTypes).run budget
          ⟨space, .work (.atom value Atom.atomType Bindings.empty 1 []), [], []⟩ =
        ([(value, Bindings.empty)],
          .finished ⟨space, .returning [], [], [(value, Bindings.empty)]⟩) := by
  intro value ctxVal
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have ready : ScopedAtomEntryReady Policy.unmarked value ctxVal Completed.Frame.empty := by
    simpa [ctxVal, value] using
      (ScopedAtomEntryReady.initial Policy.unmarked ctxVal (Or.inl rfl))
  have derivation : ScopedAtomDerivation space dispatch hostDispatch Policy.unmarked
      [] [] 1 [] [] [] value ctxVal Atom.atomType Bindings.empty
      Completed.Frame.empty [] [] 1
      [(value, Bindings.empty)]
      [(Completed.Frame.empty.read Policy.unmarked ctxVal, Completed.Frame.empty)] :=
    .type_pass 0 [] [] [] value Atom.atomType ctxVal Bindings.empty
      Completed.Frame.empty [] [] ready (by decide) (Or.inl rfl) actEmpty
  have completed := derivation.complete_and_drain_bag
  dsimp only at completed
  obtain ⟨budget, workerRun⟩ := completed.2.2.2.1
  exact ⟨derivation, budget, workerRun⟩

/-- Positive non-vacuity control for the selected-cast edge.  The existing
completed-source `hold : (-> Atom Atom)` fixture supplies both the complete
scoped type query and its unchanged contextual renewal; the earned derivation
then executes and drains the checked worker. -/
theorem control_selected_cast_derivation
    (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) :
    let space := Completed.Controls.typedInvocationSpace
    let value : Atom := .symbol "hold"
    let expected : Atom := Completed.Controls.rawSignature.functionType
    let ctxVal : Entry.Value := .symbol "hold"
    ScopedAtomDerivation space dispatch hostDispatch Policy.unmarked
      [] [] 9 [] [] [] value ctxVal expected Bindings.empty
      Completed.Frame.empty [] [] 1
      [(value, Bindings.empty)] [(ctxVal, Completed.Frame.empty)] ∧
      ∃ budget,
        (Checked.machine dispatch scopedTypes).run budget
          ⟨space, .work (.atom value expected Bindings.empty 9 []), [], []⟩ =
        ([(value, Bindings.empty)],
          .finished ⟨space, .returning [], [], [(value, Bindings.empty)]⟩) := by
  intro space value expected ctxVal
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have ctxErase : ctxVal.erase = value := by
    simp only [ctxVal, value, Entry.Value.erase]
  have ready : ScopedAtomEntryReady Policy.unmarked value ctxVal Completed.Frame.empty := by
    simpa only [ctxErase] using
      (ScopedAtomEntryReady.initial Policy.unmarked ctxVal (Or.inl rfl))
  have entered : Entry.Rel Policy.unmarked.reentry
      (Completed.Frame.empty.read Policy.unmarked ctxVal).status
      (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected .cast := by
    have rawEntered : Entry.Rel Policy.unmarked.reentry .active
        (.symbol "hold") expected .cast :=
      (Entry.Rel.cast (policy := Policy.unmarked.reentry) (status := .active)
        (atom := .symbol "hold") (expected := expected)
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (.symbol "hold") (by decide) (Or.inl ⟨"hold", rfl⟩)
        (by intro impossible; cases impossible))
    simpa only [Completed.Frame.read_empty, ctxVal, Entry.Value.status, ctxErase] using rawEntered
  have sourceQuery : Completed.scopedLookup
      (invocationTypeScope [] [] value expected Completed.Frame.empty.bindings)
      space Completed.Frame.empty.bindings value expected [expected] := by
    refine ⟨[expected], ?_, .cons ?_ (.nil _)⟩
    · simpa [space, value, expected] using Completed.Controls.typed_operator_query
    · exact ⟨id, Function.injective_id, by simp,
        by simp [expected, Completed.Controls.rawSignature, TypeSubst.typeVars,
          TypeSubst.typeVarsList, Atom.atomType]⟩
  have matched : Policy.unmarked.matching.Rel expected expected
      Completed.Frame.empty.bindings Completed.Frame.empty.bindings := by
    simpa [expected] using
      (Completed.Frame.empty.preserved_type_match Policy.unmarked
        Completed.Controls.typed_operator_match)
  have sourceQueryAtRead : Completed.scopedLookup
      (invocationTypeScope [] []
        (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected
        Completed.Frame.empty.bindings)
      space Completed.Frame.empty.bindings
      (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected [expected] := by
    simpa only [Completed.Frame.read_empty, ctxErase] using sourceQuery
  have admission : ScopedCastAdmission space Policy.unmarked value expected ctxVal
      Bindings.empty Completed.Frame.empty 8 [] [] [] [] []
      [(value, Bindings.empty)]
      [((Completed.Frame.empty.read Policy.unmarked ctxVal).erase,
        Completed.Frame.empty.bindings)]
      [(Completed.Frame.empty.read Policy.unmarked ctxVal, Completed.Frame.empty)] := by
    apply ScopedCastAdmission.unchanged
    · exact ready
    · exact entered
    · decide +kernel
    · decide +kernel
    · exact sourceQueryAtRead
    · exact matched
    · exact actEmpty
  have derivationRaw : ScopedAtomDerivation space dispatch hostDispatch Policy.unmarked
      [] [] 9 [] [] [] value ctxVal expected Bindings.empty
      Completed.Frame.empty [] [] 1
      [(value, Bindings.empty)]
      [(Completed.Frame.empty.read Policy.unmarked ctxVal, Completed.Frame.empty)] :=
    .cast 8 [] [] [] value expected ctxVal Bindings.empty Completed.Frame.empty [] []
      [(value, Bindings.empty)]
      [((Completed.Frame.empty.read Policy.unmarked ctxVal).erase,
        Completed.Frame.empty.bindings)]
      [(Completed.Frame.empty.read Policy.unmarked ctxVal, Completed.Frame.empty)] admission
  have derivation : ScopedAtomDerivation space dispatch hostDispatch Policy.unmarked
      [] [] 9 [] [] [] value ctxVal expected Bindings.empty
      Completed.Frame.empty [] [] 1
      [(value, Bindings.empty)] [(ctxVal, Completed.Frame.empty)] := by
    simpa only [Completed.Frame.read_empty] using derivationRaw
  have completed := derivation.complete_and_drain_bag
  dsimp only at completed
  obtain ⟨budget, workerRun⟩ := completed.2.2.2.1
  exact ⟨derivation, budget, workerRun⟩

/-- Negative/positive cast control: an incompatible complete type query is
admitted as its full diagnostic batch, never as a successful unchanged
payload.  The same generic cast constructor executes and drains that batch. -/
theorem control_rejected_cast_batch_derivation
    (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) :
    let space := Completed.Controls.typedInvocationSpace
    let value : Atom := .symbol "hold"
    let expected : Atom := .symbol "Bool"
    let actual : Atom := Completed.Controls.rawSignature.functionType
    let error : Atom := mkError value (.badType expected actual)
    let ctxVal : Entry.Value := .symbol "hold"
    error ≠ value ∧
      ScopedAtomDerivation space dispatch hostDispatch Policy.unmarked
        [] [] 9 [] [] [] value ctxVal expected Bindings.empty
        Completed.Frame.empty [] [] 1
        [(error, Bindings.empty)]
        [(Entry.Value.ofAtom error, Completed.Frame.empty)] ∧
      ∃ budget,
        (Checked.machine dispatch scopedTypes).run budget
          ⟨space, .work (.atom value expected Bindings.empty 9 []), [], []⟩ =
        ([(error, Bindings.empty)],
          .finished ⟨space, .returning [], [], [(error, Bindings.empty)]⟩) := by
  intro space value expected actual error ctxVal
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have ctxErase : ctxVal.erase = value := by
    simp only [ctxVal, value, Entry.Value.erase]
  have ready : ScopedAtomEntryReady Policy.unmarked value ctxVal Completed.Frame.empty := by
    simpa only [ctxErase] using
      (ScopedAtomEntryReady.initial Policy.unmarked ctxVal (Or.inl rfl))
  have entered : Entry.Rel Policy.unmarked.reentry
      (Completed.Frame.empty.read Policy.unmarked ctxVal).status
      (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected .cast := by
    have rawEntered : Entry.Rel Policy.unmarked.reentry .active
        (.symbol "hold") expected .cast :=
      Entry.Rel.cast (policy := Policy.unmarked.reentry) (status := .active)
        (atom := .symbol "hold") (expected := expected)
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (.symbol "hold") (by decide) (Or.inl ⟨"hold", rfl⟩)
        (by intro impossible; cases impossible)
    simpa only [Completed.Frame.read_empty, ctxVal, Entry.Value.status, ctxErase] using rawEntered
  have sourceQuery : Completed.scopedLookup
      (invocationTypeScope [] [] value expected Completed.Frame.empty.bindings)
      space Completed.Frame.empty.bindings value expected [actual] := by
    refine ⟨[actual], ?_, .cons ?_ (.nil _)⟩
    · simpa [space, value, actual] using Completed.Controls.typed_operator_query
    · exact ⟨id, Function.injective_id, by simp,
        by simp [actual, Completed.Controls.rawSignature, TypeSubst.typeVars,
          TypeSubst.typeVarsList, Atom.atomType]⟩
  have rejected : ∀ candidateType ∈ [actual], ∀ candidate,
      ¬Policy.unmarked.matching.Rel expected candidateType
        Completed.Frame.empty.bindings candidate := by
    intro candidateType present candidate matched
    obtain rfl := List.mem_singleton.mp present
    change TypeMatchRel expected actual Bindings.empty candidate at matched
    have sourceMatch : TypeMatchRel (.symbol "Bool")
        (.expression [.symbol "->", Atom.atomType, Atom.atomType])
        Bindings.empty candidate := by
      simpa [expected, actual, Completed.Controls.rawSignature] using matched
    obtain ⟨matchedBindings, structural, _merged⟩ := sourceMatch.structural_of_nonWildcard
      (by decide) (by decide) (by decide) (by decide)
    cases structural
  have sourceQueryAtRead : Completed.scopedLookup
      (invocationTypeScope [] []
        (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected
        Completed.Frame.empty.bindings)
      space Completed.Frame.empty.bindings
      (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected [actual] := by
    simpa only [Completed.Frame.read_empty, ctxErase] using sourceQuery
  have sourceBatch : TypeCastBatchRel space
      (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected
      Completed.Frame.empty.bindings
      [(error, Completed.Frame.empty.bindings)]
      (lookup := Completed.scopedLookup
        (invocationTypeScope [] []
          (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected
          Completed.Frame.empty.bindings) space)
      (matching := Policy.unmarked.matching.Rel) := by
    simpa only [List.map_singleton, Completed.Frame.read_empty, ctxErase, error] using
      (TypeCastBatchRel.failure sourceQueryAtRead rejected)
  have castResults : List.Forall₂
      (Completed.CastResultRel Policy.unmarked
        (Completed.scopedLookup
          (invocationTypeScope [] []
            (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected
            Completed.Frame.empty.bindings) space)
        Completed.Frame.empty (Completed.Frame.empty.read Policy.unmarked ctxVal) expected)
      [(error, Completed.Frame.empty.bindings)]
      [(Entry.Value.ofAtom error, Completed.Frame.empty)] := by
    simpa only [List.map_singleton, Completed.diagnosticResults,
      Completed.Frame.read_empty, ctxErase, error] using
      (castResultRel_forall2_diagnostics Policy.unmarked
        (Completed.scopedLookup
          (invocationTypeScope [] []
            (Completed.Frame.empty.read Policy.unmarked ctxVal).erase expected
            Completed.Frame.empty.bindings) space)
        Completed.Frame.empty (Completed.Frame.empty.read Policy.unmarked ctxVal)
        expected [actual])
  have resultsRel : List.Forall₂ ScopedResultRel
      [(error, Bindings.empty)]
      [(Entry.Value.ofAtom error, Completed.Frame.empty)] := by
    simpa only [Completed.diagnosticResults, List.map_singleton] using
      (ScopedResultRel.forall2_diagnosticResults actEmpty [error])
  have admission : ScopedCastAdmission space Policy.unmarked value expected ctxVal
      Bindings.empty Completed.Frame.empty 8 [] [] [] [] []
      [(error, Bindings.empty)] [(error, Completed.Frame.empty.bindings)]
      [(Entry.Value.ofAtom error, Completed.Frame.empty)] := by
    refine ⟨ready, entered, ?_, ?_, sourceBatch, castResults, resultsRel, actEmpty⟩
    · decide +kernel
    · decide +kernel
  have derivation : ScopedAtomDerivation space dispatch hostDispatch Policy.unmarked
      [] [] 9 [] [] [] value ctxVal expected Bindings.empty Completed.Frame.empty
      [] [] 1 [(error, Bindings.empty)]
      [(Entry.Value.ofAtom error, Completed.Frame.empty)] :=
    .cast 8 [] [] [] value expected ctxVal Bindings.empty Completed.Frame.empty
      [] [] [(error, Bindings.empty)] [(error, Completed.Frame.empty.bindings)]
      [(Entry.Value.ofAtom error, Completed.Frame.empty)] admission
  have completed := derivation.complete_and_drain_bag
  dsimp only at completed
  obtain ⟨budget, workerRun⟩ := completed.2.2.2.1
  exact ⟨by simp [error, mkError, Atom.error], derivation, budget, workerRun⟩

/-- Nonempty failed-selection control.  The declared `hold` arrow rejects the
zero-argument invocation, producing the real incorrect-arity diagnostic.  The
same structural admission constructs the independent source judgment and the
checked worker completion; tuple fallback is excluded by the selection result's
`false` eligibility flag. -/
theorem control_nonempty_selection_failure_derivation :
    let space := Completed.Controls.typedInvocationSpace
    let expr : Atom := .expression [.symbol "hold"]
    let ctxVal := Completed.Controls.wrongArityInvocation
    let error := mkError expr .incorrectNumberOfArguments
    let ctxError :=
      (Completed.publishResult Policy.unmarked expr
        (Entry.Value.ofAtom error, Completed.Frame.empty)).1
    error ≠ Atom.empty ∧
    ScopedAtomDerivation space HE.GroundedDispatch.none Completed.Controls.typedDispatch
      Policy.unmarked [] [] 10 [] [] [] expr ctxVal Atom.undefinedType
      Bindings.empty Completed.Frame.empty [] [] 4
      [(error, Bindings.empty)] [(ctxError, Completed.Frame.empty)] ∧
    Completed.AtomRel space Completed.Controls.typedDispatch Completed.scopedLookup
      [] [] ctxVal Atom.undefinedType Completed.Frame.empty
      [(ctxError, Completed.Frame.empty)] (policy := Policy.unmarked) ∧
    ∃ budget,
      (Checked.machine HE.GroundedDispatch.none scopedTypes).run budget
        ⟨space, .work (.atom expr Atom.undefinedType Bindings.empty 10 []), [], []⟩ =
      ([(error, Bindings.empty)],
        .finished ⟨space, .returning [], [], [(error, Bindings.empty)]⟩) := by
  intro space expr ctxVal error ctxError
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have ctxErase : ctxVal.erase = expr := by
    simp only [ctxVal, expr, Completed.Controls.wrongArityInvocation,
      Entry.Value.erase, List.map_cons, List.map_nil]
  have entryReady : ScopedAtomEntryReady Policy.unmarked expr ctxVal
      Completed.Frame.empty := by
    rw [← ctxErase]
    exact ScopedAtomEntryReady.initial Policy.unmarked ctxVal (Or.inl rfl)
  have sourceQuery : Completed.scopedLookup
      (invocationTypeScope [] [] expr Atom.undefinedType Completed.Frame.empty.bindings)
      space Completed.Frame.empty.bindings (.symbol "hold") Atom.undefinedType
      [Completed.Controls.rawSignature.functionType] := by
    refine ⟨[Completed.Controls.rawSignature.functionType], ?_, .cons ?_ (.nil _)⟩
    · simpa [space] using Completed.Controls.typed_operator_query
    · exact ⟨id, Function.injective_id, by simp,
        by simp [Completed.Controls.rawSignature, TypeSubst.typeVars,
          TypeSubst.typeVarsList, Atom.atomType]⟩
  have rejected : Completed.ApplicationChecksRel space
      (Completed.scopedLookup
        (invocationTypeScope [] [] expr Atom.undefinedType Completed.Frame.empty.bindings)
        space)
      Policy.unmarked expr Atom.undefinedType Completed.Controls.rawSignature
      Completed.Frame.empty [] [error] := by
    simpa [space, expr, ctxVal, error, Completed.Controls.wrongArityInvocation] using
      (Completed.ApplicationChecksRel.wrongArity
        (space := space)
        (lookup := Completed.scopedLookup
          (invocationTypeScope [] [] expr Atom.undefinedType Completed.Frame.empty.bindings)
          space)
        (policy := Policy.unmarked) (expected := Atom.undefinedType)
        (selected := Completed.Controls.rawSignature)
        (before := Completed.Frame.empty) (operator := .symbol "hold") (arguments := [])
        rfl (by decide))
  have contextualExhausted : Completed.InvocationSelectionRel space
      Completed.scopedLookup Policy.unmarked [] [] expr (.symbol "hold")
      Atom.undefinedType Completed.Frame.empty (.exhausted [error] false) :=
    ⟨[Completed.Controls.rawSignature.functionType], sourceQuery,
      .rejected rejected .nil⟩
  have diagnosticsRel : List.Forall₂ ScopedResultRel
      [(error, Bindings.empty)]
      [((Completed.Frame.empty.read Policy.unmarked (Entry.Value.ofAtom error)),
        Completed.Frame.empty)] := by
    simpa [Completed.diagnosticResults, Completed.readResult,
      Completed.Frame.read_empty] using
      (ScopedResultRel.forall2_diagnosticResults actEmpty [error])
  have admission : ScopedSelectionFailureAdmission space Policy.unmarked
      (.symbol "hold") [] Atom.undefinedType Bindings.empty 8 [] [] ctxVal
      (.symbol "hold") [] Completed.Frame.empty .active
      [Completed.Controls.rawSignature.functionType] [error] [] [] := by
    refine
      { entry_ready := by
          simpa [expr, ctxVal, Completed.Controls.wrongArityInvocation,
            Entry.Value.erase] using entryReady
        read_shape := by simp [ctxVal, Completed.Controls.wrongArityInvocation]
        operator_erase := by simp only [Entry.Value.erase]
        arguments_erase := rfl
        input_not_stopped := by decide
        expected_not_atom := by decide
        expected_not_expression := by decide
        candidate_eq := by decide +kernel
        selection_ready := by decide +kernel
        worker_exhausted := by
          let state : Configuration :=
            ⟨space, .work (.functions (.expression [.symbol "hold"])
              Atom.undefinedType Bindings.empty 8
              [Completed.Controls.rawSignature.functionType]), [.filter], []⟩
          have checked : checkIfFunctionTypeIsApplicable
              (lookup := invocationTypes state)
              (.expression [.symbol "hold"]) Completed.Controls.rawSignature.functionType
              Atom.undefinedType space Bindings.empty 8 = .inl [error] := by
            have checkedRaw : checkIfFunctionTypeIsApplicable
                (lookup := invocationTypes state)
                (.expression [.symbol "hold"])
                Completed.Controls.rawSignature.functionType Atom.undefinedType
                space Bindings.empty 8 =
                .inl [mkError (.expression [.symbol "hold"])
                  .incorrectNumberOfArguments] := by
              rfl
            simpa only [error] using checkedRaw
          simpa [state, space, expr, error, Completed.Controls.wrongArityError,
            Completed.Controls.wrongArityInvocation,
            FirstSuccessRecursiveStrategy.noteErrors] using
            (FirstSuccessRecursiveStrategy.select_complete
              (FirstSuccessRecursiveStrategy.SelectionRel.failed
                (remaining := []) (result := .exhausted [] false)
                (policy := Completed.Controls.rawSignature)
                (errors := [error]) (by rfl) checked
                (FirstSuccessRecursiveStrategy.SelectionRel.nil
                  (space := space) (expression := .expression [.symbol "hold"])
                  (expected := Atom.undefinedType) (incoming := Bindings.empty)
                  (fuel := 8) (lookup := invocationTypes state))))
        contextual_exhausted := by
          simpa [expr, ctxVal, Completed.Controls.wrongArityInvocation,
            Entry.Value.erase] using contextualExhausted
        input_activation := actEmpty
        diagnostics_rel := by
          simpa [Completed.diagnosticResults, Completed.readResult,
            Completed.Frame.read_empty] using diagnosticsRel }
  have derivationRaw := ScopedAtomDerivation.selection_failed
    (dispatch := HE.GroundedDispatch.none)
    (hostDispatch := Completed.Controls.typedDispatch) (cEmitted := [])
    (.symbol "hold") Atom.undefinedType [] ctxVal (.symbol "hold") []
    Bindings.empty Completed.Frame.empty 8 [] [] [] [] .active
    [Completed.Controls.rawSignature.functionType] [error] admission
  have derivation : ScopedAtomDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] 10 [] [] [] expr ctxVal
      Atom.undefinedType Bindings.empty Completed.Frame.empty [] [] 4
      [(error, Bindings.empty)] [(ctxError, Completed.Frame.empty)] := by
    simpa [space, expr, ctxVal, error, ctxError, successPriority,
      completedSuccessPriority, Completed.diagnosticResults, Completed.readResult,
      Completed.publishResult, Completed.Frame.read_empty, Entry.Value.publish,
      Entry.publish, Entry.Value.withStatus, isErrorAtom,
      Completed.Controls.wrongArityError, Completed.Controls.wrongArityInvocation,
      Atom.error, mkError] using derivationRaw
  have completed := derivation.complete_and_drain_bag
  dsimp only at completed
  obtain ⟨budget, workerRun⟩ := completed.2.2.2.1
  exact ⟨by decide, derivation, derivation.contextual_source, budget, workerRun⟩

/-- Positive duplicate-row control for the recursive equation edge.  Two
physical equation works each earn their own type-pass child derivation, and
both occurrences survive in order. -/
theorem control_duplicate_equation_derivation
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) :
    let call : Atom := .expression [.symbol "f"]
    let body : Atom := .symbol "A"
    let ctxCall : Entry.Value := Entry.Value.ofAtom call
    let ctxBody : Entry.Value := Entry.Value.ofAtom body
    let work0 : Spec.Eval.Steps.EquationWork :=
      ⟨0, call, body, call, body, Bindings.empty⟩
    let work1 : Spec.Eval.Steps.EquationWork :=
      ⟨1, call, body, call, body, Bindings.empty⟩
    let ctxResult : Completed.Result :=
      (Completed.Frame.empty.read Policy.unmarked ctxBody, Completed.Frame.empty)
    ScopedEquationDerivation space dispatch hostDispatch Policy.unmarked [] []
      call Atom.atomType Bindings.empty 1 [] [] ctxCall Completed.Frame.empty
      7 9 11 [] []
      [(body, Bindings.empty), (body, Bindings.empty)] [work0, work1]
      [(body, Bindings.empty), (body, Bindings.empty)]
      [(body, Bindings.empty), (body, Bindings.empty)]
      [(ctxBody, Completed.Frame.empty), (ctxBody, Completed.Frame.empty)]
      [(body, Bindings.empty), (body, Bindings.empty)]
      [ctxResult, ctxResult] := by
  intro call body ctxCall ctxBody work0 work1 ctxResult
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have eqReady :
      (matchCovered 2 (.merge Bindings.empty (aliasConstraints Bindings.empty)) &&
        (mergeBindings Bindings.empty (aliasConstraints Bindings.empty) 2).all fun merged =>
          (merged.hasLoop || merged.applyFullCovered body 2)) = true := by
    decide +kernel
  have mergeFilterEq :
      ((mergeBindings Bindings.empty (aliasConstraints Bindings.empty) 2).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull body 2, merged)) =
      [(body, Bindings.empty)] := by
    decide +kernel
  have unify0 : Entry.Value.UnifyRel Policy.unmarked.rebuilding
      Completed.Frame.empty.environment ctxCall (Entry.Value.ofAtom work0.pattern)
      Completed.Frame.empty.environment := by
    simpa [call, ctxCall, work0, Completed.Frame.empty] using
      (Entry.Value.UnifyRel.ordinary
        (Entry.Value.AppliedUnifyRel.identical (policy := Policy.unmarked.rebuilding)
          (environment := []) (by rfl)))
  have unify1 : Entry.Value.UnifyRel Policy.unmarked.rebuilding
      Completed.Frame.empty.environment ctxCall (Entry.Value.ofAtom work1.pattern)
      Completed.Frame.empty.environment := by
    simpa [call, ctxCall, work1, Completed.Frame.empty] using
      (Entry.Value.UnifyRel.ordinary
        (Entry.Value.AppliedUnifyRel.identical (policy := Policy.unmarked.rebuilding)
          (environment := []) (by rfl)))
  have ready : ScopedAtomEntryReady Policy.unmarked body ctxBody Completed.Frame.empty := by
    simpa [body, ctxBody] using
      (ScopedAtomEntryReady.initial Policy.unmarked ctxBody (Or.inl rfl))
  have outBindings0 : Completed.Frame.empty.bindings = work0.bindings := by
    simp [work0, Completed.Frame.empty]
  have outBindings1 : Completed.Frame.empty.bindings = work1.bindings := by
    simp [work1, Completed.Frame.empty]
  have ctxProd0 : ctxBody =
      Completed.Frame.empty.read Policy.unmarked (Entry.Value.ofAtom work0.body) := by
    simp [work0, ctxBody, body]
  have ctxProd1 : ctxBody =
      Completed.Frame.empty.read Policy.unmarked (Entry.Value.ofAtom work1.body) := by
    simp [work1, ctxBody, body]
  have notFunc : ∀ functionBody, body ≠ .expression [.symbol "function", functionBody] := by
    intro functionBody
    simp [body]
  have nilDerivation : ScopedEquationDerivation space dispatch hostDispatch Policy.unmarked
      [] [] call Atom.atomType Bindings.empty 1 [] [] ctxCall Completed.Frame.empty
      1 1 1
      [.prepend [(body, Bindings.empty)], .prepend [(body, Bindings.empty)]]
      [.prepend [ctxResult], .prepend [ctxResult]]
      [] [] [] [] [] [] [] := by
    exact ScopedEquationDerivation.nil
      (wRetStack := [.prepend [(body, Bindings.empty)], .prepend [(body, Bindings.empty)]])
      (expr := call) (expected := Atom.atomType) (wBIn := Bindings.empty)
      (depth := 1) (live := []) (scope := []) (ctxCall := ctxCall)
      (cFrameIn := Completed.Frame.empty)
      (cEqStack := [.prepend [ctxResult], .prepend [ctxResult]])
  have second : ScopedEquationDerivation space dispatch hostDispatch Policy.unmarked
      [] [] call Atom.atomType Bindings.empty 1 [] [] ctxCall Completed.Frame.empty
      4 5 6 [.prepend [(body, Bindings.empty)]] [.prepend [ctxResult]]
      [(body, Bindings.empty)] [work1]
      [(body, Bindings.empty)] [(body, Bindings.empty)]
      [(ctxBody, Completed.Frame.empty)] [(body, Bindings.empty)] [ctxResult] := by
    apply ScopedEquationDerivation.cons_ordinary_typePass
      (rhs := body) (wBodyVal := body) (selected := Bindings.empty)
      (wBMid := Bindings.empty) (work := work1) (ctxProdVal := ctxBody)
      (cFrameMid := Completed.Frame.empty)
      (eqReady := eqReady) (mergeFilterEq := mergeFilterEq)
      (outBindingsEq := outBindings1) (unifyRel := unify1)
      (ctxProdEq := ctxProd1) (notFunc := notFunc)
      (notRefused := by decide) (clean := by decide)
      (typePass := Or.inl rfl) (entryReady := ready) (actMid := actEmpty)
      (tailDerivation := nilDerivation)
  apply ScopedEquationDerivation.cons_ordinary_typePass
    (rhs := body) (wBodyVal := body) (selected := Bindings.empty)
    (wBMid := Bindings.empty) (work := work0) (ctxProdVal := ctxBody)
    (cFrameMid := Completed.Frame.empty)
    (eqReady := eqReady) (mergeFilterEq := mergeFilterEq)
    (outBindingsEq := outBindings0) (unifyRel := unify0)
    (ctxProdEq := ctxProd0) (notFunc := notFunc)
    (notRefused := by decide) (clean := by decide)
    (typePass := Or.inl rfl) (entryReady := ready) (actMid := actEmpty)
    (tailDerivation := second)

/-- Negative tuple control: the empty tuple has its unit occurrence on both
sides and therefore cannot be admitted as an empty result batch. -/
theorem ScopedTupleDerivation.empty_cannot_return_no_results
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {scope : List String} {fuel steps : Nat} {live : List Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    (_derivation : ScopedTupleDerivation space dispatch hostDispatch policy
      wEmitted cEmitted scope fuel steps live [] [] wB cFrame
      wStack cStack wResults cResults) :
    wResults ≠ [] ∧ cResults ≠ [] := by
  cases _derivation
  simp

/-- Positive continuing-branch control.  Two open variables form a tuple;
the first occurrence reaches the tail frame, the second is evaluated there,
and both the checked worker and contextual source return the ordered pair. -/
theorem control_open_pair_tuple_derivation :
    let space := Completed.Controls.typedInvocationSpace
    let x : Atom := .var "x"
    let y : Atom := .var "y"
    let ctxX : Entry.Value := .var "x"
    let ctxY : Entry.Value := .var "y"
    let wTail : ResultSet := [(HE.tupleSingleton (y, Bindings.empty))]
    let cTail : List Completed.Result :=
      [Completed.tupleSingleton (ctxY, Completed.Frame.empty)]
    let wPair := RecursiveTasks.tupleTail x wTail
    let cPair := cTail.map (Completed.tuplePrepend ctxX)
    ∃ _derivation : ScopedTupleDerivation space HE.GroundedDispatch.none
        Completed.Controls.typedDispatch Policy.unmarked [] [] []
        3 11 [] [x, y] [ctxX, ctxY] Bindings.empty Completed.Frame.empty
        [] [] wPair cPair,
      wPair = [(.expression [x, y], Bindings.empty)] ∧
      cPair = [(.expression .active [ctxX, ctxY], Completed.Frame.empty)] ∧
      Completed.TupleRel space Completed.Controls.typedDispatch
        Completed.scopedLookup [] [] [ctxX, ctxY] Completed.Frame.empty cPair
        (policy := Policy.unmarked) ∧
      ∀ budget,
        (Checked.machine HE.GroundedDispatch.none scopedTypes).run (11 + budget)
          ⟨space,
            .work (.tuple (.expression [x, y]) Bindings.empty 3 []), [], []⟩ =
        (Checked.machine HE.GroundedDispatch.none scopedTypes).run budget
          ⟨space, .returning wPair, [], []⟩ := by
  intro space x y ctxX ctxY wTail cTail wPair cPair
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have xErase : ctxX.erase = x := by
    simp only [ctxX, x, Entry.Value.erase]
  have yErase : ctxY.erase = y := by
    simp only [ctxY, y, Entry.Value.erase]
  have xReady : ScopedAtomEntryReady Policy.unmarked x ctxX Completed.Frame.empty := by
    rw [← xErase]
    exact ScopedAtomEntryReady.initial Policy.unmarked ctxX (Or.inl rfl)
  have yReady : ScopedAtomEntryReady Policy.unmarked y ctxY Completed.Frame.empty := by
    rw [← yErase]
    exact ScopedAtomEntryReady.initial Policy.unmarked ctxY (Or.inl rfl)
  have headDerivation : ScopedAtomDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] []
      2 [.expression [y]] [.expression [y]] [] x ctxX Atom.undefinedType
      Bindings.empty Completed.Frame.empty
      [.tupleHeads (.expression [y]) 2 []]
      [.branches [] [] [ctxY]] 1
      [(x, Bindings.empty)] [(ctxX, Completed.Frame.empty)] := by
    simpa only [Completed.Frame.read_empty] using
      (ScopedAtomDerivation.type_pass
        (space := space) (dispatch := HE.GroundedDispatch.none)
        (hostDispatch := Completed.Controls.typedDispatch)
        (wEmitted := []) (cEmitted := [])
        1 [.expression [y]] [.expression [y]] [] x
        Atom.undefinedType ctxX Bindings.empty Completed.Frame.empty
        [.tupleHeads (.expression [y]) 2 []] [.branches [] [] [ctxY]]
        xReady (by decide) (Or.inr (Or.inr rfl)) actEmpty)
  have tailHeadDerivation : ScopedAtomDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] []
      1 [x] [x] [] y ctxY Atom.undefinedType Bindings.empty Completed.Frame.empty
      [.tupleSingleton, .tupleTail x,
        .append (.tupleHeads (.expression [y]) 2 [] [])]
      [.singleton, .tupleTail ctxX,
        .append (.branches [] [] [ctxY] [])]
      1 [(y, Bindings.empty)] [(ctxY, Completed.Frame.empty)] := by
    simpa only [Completed.Frame.read_empty] using
      (ScopedAtomDerivation.type_pass
        (space := space) (dispatch := HE.GroundedDispatch.none)
        (hostDispatch := Completed.Controls.typedDispatch)
        (wEmitted := []) (cEmitted := [])
        0 [x] [x] [] y Atom.undefinedType ctxY Bindings.empty
        Completed.Frame.empty
        [.tupleSingleton, .tupleTail x,
          .append (.tupleHeads (.expression [y]) 2 [] [])]
        [.singleton, .tupleTail ctxX,
          .append (.branches [] [] [ctxY] [])]
        yReady (by decide) (Or.inr (Or.inr rfl)) actEmpty)
  have tailDerivation : ScopedTupleDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] []
      2 3 [x] [y] [ctxY] Bindings.empty Completed.Frame.empty
      [.tupleTail x, .append (.tupleHeads (.expression [y]) 2 [] [])]
      [.tupleTail ctxX, .append (.branches [] [] [ctxY] [])]
      wTail cTail := by
    exact .singleton [] 1 1 [x] y ctxY Bindings.empty Completed.Frame.empty
      [.tupleTail x, .append (.tupleHeads (.expression [y]) 2 [] [])]
      [.tupleTail ctxX, .append (.branches [] [] [ctxY] [])]
      [(y, Bindings.empty)] [(ctxY, Completed.Frame.empty)] yErase
      tailHeadDerivation
  have restDerivation : ScopedTupleBranchesDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] []
      2 1 [] [y] [ctxY] [] [] [.prepend wPair] [.prepend cPair] [] [] := by
    exact .nil [] 2 [] [y] [ctxY] [.prepend wPair] [.prepend cPair]
      (by simpa only [List.map_cons, List.map_nil] using congrArg (fun value => [value]) yErase)
  have branchDerivation : ScopedTupleBranchesDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] []
      2 8 [] [y] [ctxY]
      [(x, Bindings.empty)] [(ctxX, Completed.Frame.empty)] [] [] wPair cPair := by
    exact .continuing [] 2 3 1 [] [y] [ctxY]
      (x, Bindings.empty) (ctxX, Completed.Frame.empty) [] wTail [] [] cTail []
      [] [] (by
        simpa only [List.map_cons, List.map_nil] using congrArg (fun value => [value]) yErase)
      ⟨xErase.symm, actEmpty⟩ (by decide) tailDerivation restDerivation
  have derivation : ScopedTupleDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] []
      3 11 [] [x, y] [ctxX, ctxY] Bindings.empty Completed.Frame.empty
      [] [] wPair cPair := by
    exact .cons [] 2 1 8 [] x y [] ctxX ctxY [] Bindings.empty
      Completed.Frame.empty [] [] [(x, Bindings.empty)] wPair
      [(ctxX, Completed.Frame.empty)] cPair xErase yErase rfl
      (by
        simpa only [List.map_cons, List.map_nil, yErase] using headDerivation)
      branchDerivation
  have run := ScopedTupleDerivation.task_run derivation
  refine ⟨derivation, ?_, ?_, ScopedTupleDerivation.to_completed_tupleRel derivation,
    run.worker_run⟩
  · change RecursiveTasks.tupleTail (.var "x")
      [HE.tupleSingleton (.var "y", Bindings.empty)] =
        [(.expression [.var "x", .var "y"], Bindings.empty)]
    decide +kernel
  · change
      [Completed.tuplePrepend (.var "x")
        (Completed.tupleSingleton
          ((.var "y" : Entry.Value), Completed.Frame.empty))] =
      [(.expression .active [(.var "x" : Entry.Value), .var "y"],
        Completed.Frame.empty)]
    simp [Completed.tupleSingleton, Completed.tuplePrepend, Entry.Value.erase,
      isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty]

/-- Positive atom-level fallback control.  The empty constructor is tuple data
under the complete non-function type scan.  The singleton tuple is evaluated,
called through the ordinary absent-equation branch, and published by the
structural fallback wrapper in twenty-five checked-worker steps. -/
theorem control_singleton_empty_fallback_derivation :
    let space := Space.empty
    let x : Atom := Atom.empty
    let ctxX : Entry.Value := Entry.Value.ofAtom x
    let expr : Atom := .expression [x]
    let ctxVal : Entry.Value := .expression .active [ctxX]
    let wRow : ResultPair := (x, Bindings.empty)
    let cRow : Completed.Result := (ctxX, Completed.Frame.empty)
    let cDiag := Completed.diagnosticResults [] Completed.Frame.empty
    let cSelected := completedSuccessPriority
      (([cRow] ++ cDiag).map (Completed.readResult Policy.unmarked))
    let cPublished := cSelected.map (Completed.publishResult Policy.unmarked expr)
    ∃ candidates,
      ScopedFallbackAtomDerivation space HE.GroundedDispatch.none
        Completed.Controls.typedDispatch Policy.unmarked [] []
        x [] Atom.undefinedType Bindings.empty 2 [] []
        ctxVal ctxX [] Completed.Frame.empty .active candidates []
        3 15 1 [] [] [wRow] [wRow] [cRow] [cRow] ∧
      Completed.AtomRel space Completed.Controls.typedDispatch
        Completed.scopedLookup [] [] ctxVal Atom.undefinedType
        Completed.Frame.empty cPublished (policy := Policy.unmarked) ∧
      ∀ budget,
        (Checked.machine HE.GroundedDispatch.none scopedTypes).run (25 + budget)
          ⟨space, .work (.atom expr Atom.undefinedType Bindings.empty 4 []), [], []⟩ =
        (Checked.machine HE.GroundedDispatch.none scopedTypes).run budget
          ⟨space, .returning [wRow], [], []⟩ := by
  intro space x ctxX expr ctxVal wRow cRow cDiag cSelected cPublished
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have xErase : ctxX.erase = x := by simp [ctxX]
  have valueErase : ctxVal.erase = expr := by
    simp [ctxVal, expr, ctxX, x, Entry.Value.erase]
  have valueReady : ScopedAtomEntryReady Policy.unmarked expr ctxVal
      Completed.Frame.empty := by
    rw [← valueErase]
    exact ScopedAtomEntryReady.initial Policy.unmarked ctxVal (Or.inl rfl)
  obtain ⟨readiness, ctxOp, ctxArgs, admission⟩ :=
    ScopedTupleFallbackAdmission.of_nonfunctions space Policy.unmarked x []
      Atom.undefinedType Bindings.empty 2 [] [] ctxVal Completed.Frame.empty
      [] [] valueReady (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) actEmpty (by simp)
  have shaped : (.expression .active [ctxX] : Entry.Value) =
      .expression readiness (ctxOp :: ctxArgs) := by
    simpa [ctxVal, Completed.Frame.read_empty] using admission.read_shape
  have shapeParts := Entry.Value.expression.inj shaped
  have readinessEq : readiness = .active := shapeParts.1.symm
  have childrenEq : ctxOp :: ctxArgs = [ctxX] := shapeParts.2.symm
  obtain ⟨ctxOpEq, ctxArgsEq⟩ := List.cons.inj childrenEq
  subst readiness
  subst ctxOp
  subst ctxArgs
  have xReady : ScopedAtomEntryReady Policy.unmarked x ctxX Completed.Frame.empty := by
    rw [← xErase]
    exact ScopedAtomEntryReady.initial Policy.unmarked ctxX (Or.inl rfl)
  let wTupleStack : List RecursiveTasks.Frame :=
    [.calls Atom.undefinedType 2 [], .prepend [], .filter]
  let cTupleStack : List RecursiveTasks.Contextual.Continuation :=
    [.calls [] [] Atom.undefinedType, .diagnostics [] Completed.Frame.empty,
      .publish expr]
  have headDerivation : ScopedAtomDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] []
      1 [Atom.undefinedType] [Atom.undefinedType] [] x ctxX Atom.undefinedType
      Bindings.empty Completed.Frame.empty (.tupleSingleton :: wTupleStack)
      (.singleton :: cTupleStack) 1
      [(x, Bindings.empty)] [(ctxX, Completed.Frame.empty)] := by
    simpa only [Completed.Frame.read_empty] using
      (ScopedAtomDerivation.empty_or_error
        (space := space) (dispatch := HE.GroundedDispatch.none)
        (hostDispatch := Completed.Controls.typedDispatch)
        (wEmitted := []) (cEmitted := [])
        0 [Atom.undefinedType] [Atom.undefinedType] [] x Atom.undefinedType
        ctxX Bindings.empty Completed.Frame.empty
        (.tupleSingleton :: wTupleStack) (.singleton :: cTupleStack)
        xReady (by decide) actEmpty)
  have tupleDerivation : ScopedTupleDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] []
      2 3 [Atom.undefinedType] [x] [ctxX] Bindings.empty Completed.Frame.empty
      wTupleStack cTupleStack [wRow] [cRow] := by
    simpa [wRow, cRow, x, ctxX, HE.tupleSingleton,
      Completed.tupleSingleton, Entry.Value.erase, isEmptyOrError, isEmptyAtom,
      isErrorAtom, Atom.empty] using
      (ScopedTupleDerivation.singleton
        (space := space) (dispatch := HE.GroundedDispatch.none)
        (hostDispatch := Completed.Controls.typedDispatch)
        (policy := Policy.unmarked) (wEmitted := []) (cEmitted := [])
        [] 1 1 [Atom.undefinedType] x ctxX Bindings.empty Completed.Frame.empty
        wTupleStack cTupleStack [(x, Bindings.empty)]
        [(ctxX, Completed.Frame.empty)] xErase headDerivation)
  have rowRel : ScopedResultRel wRow cRow := by
    exact ⟨by simpa [wRow, cRow] using xErase.symm, actEmpty⟩
  have absentAdmission : ScopedAbsentCallAdmission space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch x Atom.undefinedType Bindings.empty
      1 [] ctxX Completed.Frame.empty := by
    refine
      { value_erase := xErase
        not_error := by decide
        not_executable := by simp [x, HE.GroundedDispatch.none]
        non_grounded := by
          refine ⟨?_, ?_⟩
          · simp [Spec.Eval.Minimal.HostCall, Completed.Controls.typedDispatch,
              ctxX, x]
          · rw [xErase]
            simp [x, Atom.empty, Spec.Eval.Minimal.embeddedInstruction]
        not_minimal := by
          change minimalInstruction Atom.empty = false
          rfl
        query_covered := by decide +kernel
        query_nil := by decide +kernel
        frontier_nil := by
          simpa [space, xErase, Completed.Frame.empty] using
            (Spec.Eval.Steps.EquationFrontierRel.completed
              (space := Space.empty) (live := [Atom.undefinedType])
              (query := x) (incoming := Bindings.empty)
              (blocks := []) List.Forall₂.nil)
        input_activation := actEmpty }
  let wCallsStack : List RecursiveTasks.Frame := [.prepend [], .filter]
  let cCallsStack : List RecursiveTasks.Contextual.Continuation :=
    [.diagnostics [] Completed.Frame.empty, .publish expr]
  have callsDerivation : ScopedOrdinaryCallsDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] 2 15 [] []
      Atom.undefinedType [wRow] [cRow] wCallsStack cCallsStack [wRow] [cRow] := by
    exact ScopedOrdinaryCallsDerivation.singleton_absent rowRel absentAdmission
  let candidates := invocationTypes
    ⟨space, .work (.atom expr Atom.undefinedType Bindings.empty 4 []), [], []⟩
    Bindings.empty x Atom.undefinedType
  have admissionAt : ScopedTupleFallbackAdmission space Policy.unmarked x []
      Atom.undefinedType Bindings.empty 2 [] [] ctxVal ctxX []
      Completed.Frame.empty .active candidates [] [] [] := by
    simpa [candidates, expr] using admission
  have derivation : ScopedFallbackAtomDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] []
      x [] Atom.undefinedType Bindings.empty 2 [] []
      ctxVal ctxX [] Completed.Frame.empty .active candidates []
      3 15 1 [] [] [wRow] [wRow] [cRow] [cRow] := by
    refine
      { admission := admissionAt
        tuple_derivation := ?_
        calls_derivation := ?_
        raw_covered := by
          intro pair member
          simp [wRow] at member
          subst pair
          change Bindings.empty.applyFullCovered Atom.empty 1 = true
          decide +kernel
        raw_stable := by
          intro pair member
          simp [wRow] at member
          subst pair
          change Bindings.empty.applyFull Atom.empty 1 = Atom.empty
          rfl }
    · simpa [wTupleStack, cTupleStack, expr] using tupleDerivation
    · simpa [wCallsStack, cCallsStack, expr] using callsDerivation
  have source := ScopedFallbackAtomDerivation.to_completed_atomRel derivation
  have run := ScopedFallbackAtomDerivation.task_run derivation (by simp) (Or.inl rfl)
  refine ⟨candidates, derivation, ?_, ?_⟩
  · simpa [cDiag, cSelected, cPublished] using source
  · have priority : successPriority [wRow] = [wRow] := by
      change successPriority [(Atom.empty, Bindings.empty)] =
        [(Atom.empty, Bindings.empty)]
      decide +kernel
    simpa [expr, wRow, x, priority] using run.worker_run

/-- Positive ordered ordinary-call control.  An error occurrence is passed
through first and a later symbol has a complete empty equation frontier.  Both
occurrences survive the calls spine in that order. -/
theorem control_error_then_absent_calls_derivation :
    let space := Space.empty
    let error : Atom := Atom.error (.symbol "subject") (.symbol "message")
    let datum : Atom := .symbol "datum"
    let ctxError := Entry.Value.ofAtom error
    let ctxDatum : Entry.Value := .symbol "datum"
    let wRows : ResultSet := [(error, Bindings.empty), (datum, Bindings.empty)]
    let cRows : List Completed.Result :=
      [(ctxError, Completed.Frame.empty), (ctxDatum, Completed.Frame.empty)]
    ∃ _derivation : ScopedOrdinaryCallsDerivation space HE.GroundedDispatch.none
        Completed.Controls.typedDispatch Policy.unmarked [] [] 4 20 [] []
        Atom.undefinedType wRows cRows [] [] wRows cRows,
      Completed.CallsRel space Completed.Controls.typedDispatch
        Completed.scopedLookup [] [] Atom.undefinedType cRows cRows
        (policy := Policy.unmarked) ∧
      ∀ budget,
        (Checked.machine HE.GroundedDispatch.none scopedTypes).run (20 + budget)
          ⟨space, .work (.calls Atom.undefinedType 4 wRows []), [], []⟩ =
        (Checked.machine HE.GroundedDispatch.none scopedTypes).run budget
          ⟨space, .returning wRows, [], []⟩ := by
  intro space error datum ctxError ctxDatum wRows cRows
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have errorRel : ScopedResultRel (error, Bindings.empty)
      (ctxError, Completed.Frame.empty) := by
    exact ⟨by simp [ctxError], actEmpty⟩
  have datumRel : ScopedResultRel (datum, Bindings.empty)
      (ctxDatum, Completed.Frame.empty) := by
    exact ⟨by simp [datum, ctxDatum, Entry.Value.erase], actEmpty⟩
  have absentAdmission : ScopedAbsentCallAdmission space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch datum Atom.undefinedType Bindings.empty
      3 [] ctxDatum Completed.Frame.empty := by
    refine
      { value_erase := by simp [datum, ctxDatum, Entry.Value.erase]
        not_error := by decide
        not_executable := by intro op args impossible; simp [datum] at impossible
        non_grounded := by
          simp [NonGroundedCallRel, Spec.Eval.Minimal.HostCall,
            Completed.Controls.typedDispatch, ctxDatum, Entry.Value.erase,
            Spec.Eval.Minimal.embeddedInstruction]
        not_minimal := by decide
        query_covered := by decide +kernel
        query_nil := by decide +kernel
        frontier_nil := by
          simpa [space, ctxDatum, Entry.Value.erase, Completed.Frame.empty] using
            (Spec.Eval.Steps.EquationFrontierRel.completed
              (space := Space.empty) (live := [Atom.undefinedType])
              (query := .symbol "datum") (incoming := Bindings.empty)
              (blocks := []) List.Forall₂.nil)
        input_activation := actEmpty }
  have errorChild : ScopedOrdinaryCallDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] 4 2 [] []
      error ctxError Atom.undefinedType Bindings.empty Completed.Frame.empty
      [.append (.calls Atom.undefinedType 4 [(datum, Bindings.empty)] [])]
      [.append (.calls [] [] Atom.undefinedType
        [(ctxDatum, Completed.Frame.empty)])]
      [(error, Bindings.empty)] [(ctxError, Completed.Frame.empty)] := by
    exact .error 3 [] [] error Atom.undefinedType ctxError Bindings.empty
      Completed.Frame.empty
      [.append (.calls Atom.undefinedType 4 [(datum, Bindings.empty)] [])]
      [.append (.calls [] [] Atom.undefinedType
        [(ctxDatum, Completed.Frame.empty)])]
      (by simp [ctxError]) (by simp [error, Atom.error, isErrorAtom]) actEmpty
  have absentChild : ScopedOrdinaryCallDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] 4 11 [] []
      datum ctxDatum Atom.undefinedType Bindings.empty Completed.Frame.empty
      [.append (.calls Atom.undefinedType 4 [] []),
        .prepend [(error, Bindings.empty)]]
      [.append (.calls [] [] Atom.undefinedType []),
        .prepend [(ctxError, Completed.Frame.empty)]]
      [(datum, Bindings.empty)] [(ctxDatum, Completed.Frame.empty)] := by
    exact .absent 3 [] [] datum Atom.undefinedType ctxDatum Bindings.empty
      Completed.Frame.empty
      [.append (.calls Atom.undefinedType 4 [] []),
        .prepend [(error, Bindings.empty)]]
      [.append (.calls [] [] Atom.undefinedType []),
        .prepend [(ctxError, Completed.Frame.empty)]] absentAdmission
  have nilTail : ScopedOrdinaryCallsDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] 4 1 [] []
      Atom.undefinedType [] []
      [.prepend [(datum, Bindings.empty)], .prepend [(error, Bindings.empty)]]
      [.prepend [(ctxDatum, Completed.Frame.empty)],
        .prepend [(ctxError, Completed.Frame.empty)]] [] [] := by
    exact .nil 4 [] [] Atom.undefinedType
      [.prepend [(datum, Bindings.empty)], .prepend [(error, Bindings.empty)]]
      [.prepend [(ctxDatum, Completed.Frame.empty)],
        .prepend [(ctxError, Completed.Frame.empty)]]
  have second : ScopedOrdinaryCallsDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] 4 15 [] []
      Atom.undefinedType [(datum, Bindings.empty)]
      [(ctxDatum, Completed.Frame.empty)]
      [.prepend [(error, Bindings.empty)]]
      [.prepend [(ctxError, Completed.Frame.empty)]]
      [(datum, Bindings.empty)] [(ctxDatum, Completed.Frame.empty)] := by
    exact .cons 4 11 1 [] [] Atom.undefinedType
      (datum, Bindings.empty) (ctxDatum, Completed.Frame.empty)
      [] [(datum, Bindings.empty)] [] [] [(ctxDatum, Completed.Frame.empty)] []
      [.prepend [(error, Bindings.empty)]]
      [.prepend [(ctxError, Completed.Frame.empty)]] datumRel absentChild nilTail
  have derivation : ScopedOrdinaryCallsDerivation space HE.GroundedDispatch.none
      Completed.Controls.typedDispatch Policy.unmarked [] [] 4 20 [] []
      Atom.undefinedType wRows cRows [] [] wRows cRows := by
    exact .cons 4 2 15 [] [] Atom.undefinedType
      (error, Bindings.empty) (ctxError, Completed.Frame.empty)
      [(datum, Bindings.empty)] [(error, Bindings.empty)]
      [(datum, Bindings.empty)] [(ctxDatum, Completed.Frame.empty)]
      [(ctxError, Completed.Frame.empty)] [(ctxDatum, Completed.Frame.empty)]
      [] [] errorRel errorChild second
  have run := ScopedOrdinaryCallsDerivation.task_run derivation
  exact ⟨derivation, ScopedOrdinaryCallsDerivation.to_completed_callsRel derivation,
    run.worker_run⟩

/-- Negative profile control: an embedded `cons-atom` call cannot be certified
as an ordinary equation call. -/
theorem embedded_cons_atom_not_ordinary
    {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy}
    {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {fuel steps : Nat} {live : List Atom} {scope : List String}
    {ctxVal : Entry.Value} {expected : Atom}
    {wB : Bindings} {cFrame : Completed.Frame}
    {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation}
    {wResults : ResultSet} {cResults : List Completed.Result}
    : ¬ScopedOrdinaryCallDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel steps live scope
      (.expression [.symbol "cons-atom", .symbol "A", .expression []])
      ctxVal expected wB cFrame wStack cStack wResults cResults := by
  intro derivation
  cases derivation
  case error isError _valueEq _actRel => simp [isErrorAtom] at isError
  case absent admission =>
      have notMinimal := admission.not_minimal
      simp [minimalInstruction] at notMinimal
  case equations admission _equationDerivation =>
      have notMinimal := admission.not_minimal
      simp [minimalInstruction] at notMinimal

end UniversalScopedPolymorphicApplication

#print axioms UniversalScopedPolymorphicApplication.ScopedTaskRun.atomTypePass
#print axioms UniversalScopedPolymorphicApplication.ScopedTaskRun.atomEmptyOrError
#print axioms UniversalScopedPolymorphicApplication.ScopedTaskRun.atomCast
#print axioms UniversalScopedPolymorphicApplication.ScopedTaskRun.atomSelectionFailed
#print axioms UniversalScopedPolymorphicApplication.scoped_selected_function_entry_run
#print axioms UniversalScopedPolymorphicApplication.worker_producedRaw_silent_step
#print axioms UniversalScopedPolymorphicApplication.worker_equations_cons_run
#print axioms UniversalScopedPolymorphicApplication.worker_productions_cons_run
#print axioms UniversalScopedPolymorphicApplication.worker_returns_leaf_cons_run
#print axioms UniversalScopedPolymorphicApplication.contextual_equations_leaf_localSteps
#print axioms UniversalScopedPolymorphicApplication.ScopedConcreteEquationWorksSpine.cons_ordinary_typePass
#print axioms UniversalScopedPolymorphicApplication.ScopedConcreteEquationWorksSpine.finalResults_forall2
#print axioms UniversalScopedPolymorphicApplication.ScopedConcreteEquationWorksSpine.returns_run
#print axioms UniversalScopedPolymorphicApplication.ScopedConcreteEquationWorksSpine.contextual_equations_localSteps
#print axioms UniversalScopedPolymorphicApplication.ScopedConcreteEquationWorksSpine.call_run
#print axioms UniversalScopedPolymorphicApplication.ScopedTaskRun.selected_function_of_parts
#print axioms UniversalScopedPolymorphicApplication.ScopedAtomDerivation.task_run
#print axioms UniversalScopedPolymorphicApplication.ScopedArgsDerivation.task_run
#print axioms UniversalScopedPolymorphicApplication.ScopedTupleDerivation.task_run
#print axioms UniversalScopedPolymorphicApplication.ScopedTupleBranchesDerivation.task_run
#print axioms UniversalScopedPolymorphicApplication.ScopedEquationDerivation.to_concreteSpine
#print axioms UniversalScopedPolymorphicApplication.ScopedEquationDerivation.cons_ordinary_typePass
#print axioms UniversalScopedPolymorphicApplication.ScopedEquationDerivation.cons_ordinary_notReducible
#print axioms UniversalScopedPolymorphicApplication.ScopedEquationDerivation.cons_ordinary_stopped
#print axioms UniversalScopedPolymorphicApplication.ScopedAtomDerivation.input_relation
#print axioms UniversalScopedPolymorphicApplication.ScopedAtomDerivation.entry_ready
#print axioms UniversalScopedPolymorphicApplication.ScopedAtomDerivation.of_completed_delivered
#print axioms UniversalScopedPolymorphicApplication.ScopedAtomDerivation.to_completed_atomRel
#print axioms UniversalScopedPolymorphicApplication.ScopedArgsDerivation.to_completed_argumentsRel
#print axioms UniversalScopedPolymorphicApplication.ScopedTupleDerivation.to_completed_tupleRel
#print axioms UniversalScopedPolymorphicApplication.ScopedTupleBranchesDerivation.to_completed_tupleBranchesRel
#print axioms UniversalScopedPolymorphicApplication.ScopedEquationDerivation.to_completed_equationBodiesRel
#print axioms UniversalScopedPolymorphicApplication.held_reuse_not_admitted
#print axioms UniversalScopedPolymorphicApplication.ScopedAtomDerivation.complete_and_drain_bag
#print axioms UniversalScopedPolymorphicApplication.ScopedAtomDerivation.contextual_source
#print axioms UniversalScopedPolymorphicApplication.control_type_pass_derivation
#print axioms UniversalScopedPolymorphicApplication.control_selected_cast_derivation
#print axioms UniversalScopedPolymorphicApplication.control_rejected_cast_batch_derivation
#print axioms UniversalScopedPolymorphicApplication.control_nonempty_selection_failure_derivation
#print axioms UniversalScopedPolymorphicApplication.control_duplicate_equation_derivation
#print axioms UniversalScopedPolymorphicApplication.ScopedTupleDerivation.empty_cannot_return_no_results
#print axioms UniversalScopedPolymorphicApplication.control_open_pair_tuple_derivation
#print axioms UniversalScopedPolymorphicApplication.ScopedOrdinaryCallDerivation.to_completed_callRel
#print axioms UniversalScopedPolymorphicApplication.ScopedOrdinaryCallsDerivation.to_completed_callsRel
#print axioms UniversalScopedPolymorphicApplication.ScopedOrdinaryCallDerivation.task_run
#print axioms UniversalScopedPolymorphicApplication.ScopedOrdinaryCallsDerivation.task_run
#print axioms UniversalScopedPolymorphicApplication.control_error_then_absent_calls_derivation
#print axioms UniversalScopedPolymorphicApplication.embedded_cons_atom_not_ordinary
#print axioms UniversalScopedPolymorphicApplication.ScopedTupleFallbackAdmission.of_nonfunctions
#print axioms UniversalScopedPolymorphicApplication.ScopedOrdinaryCallsDerivation.singleton_absent
#print axioms UniversalScopedPolymorphicApplication.ScopedResultRel.forall2_fallbackPriority
#print axioms UniversalScopedPolymorphicApplication.ScopedTaskRun.to_bag
#print axioms UniversalScopedPolymorphicApplication.ScopedBagTaskRun.atomFallback_of_parts
#print axioms UniversalScopedPolymorphicApplication.ScopedFallbackAtomDerivation.to_completed_atomRel
#print axioms UniversalScopedPolymorphicApplication.ScopedFallbackAtomDerivation.bag_task_run
#print axioms UniversalScopedPolymorphicApplication.ScopedFallbackAtomDerivation.task_run
#print axioms UniversalScopedPolymorphicApplication.scopedRankedFallbackLaws
#print axioms UniversalScopedPolymorphicApplication.ScopedRankedFallbackStep.to_completed_atomRel
#print axioms UniversalScopedPolymorphicApplication.ScopedRankedFallbackStep.task_run
#print axioms UniversalScopedPolymorphicApplication.ScopedAtomDerivation.of_ranked_fallback
#print axioms UniversalScopedPolymorphicApplication.control_singleton_empty_fallback_derivation
#print axioms UniversalScopedPolymorphicApplication.controlP_nonempty_diagnostics_and_results_bag_and_priority_blocks

end Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy
