import Mettapedia.Machines.BranchLocalNeed.WeightedResumption
import Mettapedia.Machines.BranchLocalNeed.DependentService
import Mettapedia.Languages.MeTTa.PrimeCandidates.Strategies.NativeDerivationGrades
import Mettapedia.Languages.MeTTa.PrimeCandidates.Strategies.NativeGradeAttachment
import Mettapedia.GSLT.Dynamics.ResumptionCategory
import Mettapedia.GSLT.Causality.OccurrenceMachineHistory
import Mettapedia.GSLT.Core.InferenceRecording
import Mettapedia.GSLT.Core.FiniteSearchCertificate
import Mathlib.Tactic.Convert
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachineExamples
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.Machines.SourceProducerCardinality
import Mettapedia.Machines.Cursor.ReadOnlyQuery
import Mettapedia.GSLT.LanguageDef.NativeControlCursor
import Mettapedia.GSLT.LanguageDef.OperationCostProtocol
import Mettapedia.Languages.MeTTa.PrimeCandidates.Strategies.NativeReceiptCorrespondence
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.List.Sigma
import Mettapedia.GSLT.Distinction.LevelAccounts

/-!
# Native equation weights as a resumption handler

The Prime adapter selects the existing Need specification and binding-local
graded-where interpretation. Free operations, weighted sequencing, retained
worlds and resumption are supplied by their general mathematical modules.

Equation coefficients are charged on actual physical choice receipts, before
executing the right-hand side. The settled and pending adapters share one
handler. A pending coefficient executes with the captured bindings; its body
resumes with the completed coefficient's world, preserving shared lazy choices.
An uninterpreted coefficient result retains that body and the actual score.
Authored predicates use the same handler and owned account. Their phase changes
add no Need instruction; completed coefficient work is not counted twice.
Caller agreement is supplied by the common nested handler and actual captures;
it preserves suspended states without identifying equal occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler

open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Mettapedia.GSLT.Dynamics
open NativeEquationNeed NativeCandidateGrades NativeDerivationGrades

abbrev WorkState := WorkOccurrence NativeMachine

def source {V : Type} [Semiring V] (program : Program) (clause : WeighClause V Row) :
    WeightedBranchingResumption.Coalgebra WorkState WorkState V :=
  NeedWeightedResumption.source (specification program) (edgeGrade clause)

theorem immediate_successors_erase {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (before : WorkState) :
    (NeedWeightedResumption.successors (specification program) (edgeGrade clause) before).map
      Prod.fst = (occurrenceSystem program).successors before :=
  NeedWeightedResumption.successors_erasure _ _ _

/-- Authored physical row admission supplies the coefficient environment. -/
theorem coefficient_of_actual_capture {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (head : String)
    (arguments : List CellId) (machine : NativeMachine) (cell : CellId)
    (stack : List (Frame Resume)) (capture : Captured)
    (member : capture ∈ captureApplication program head arguments machine cell stack) :
    edgeGrade clause machine capture.body = WeighClause.eval capture.row clause := by
  rw [edgeGrade, application_capture_choice program head arguments machine cell stack capture member]

/-- The actual native weighted frontier is the interpretation of its free unfolding. -/
theorem native_handler_agrees {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat) (before : WorkState) :
    WeightedResumption.interpret WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (source program clause) fuel before) =
      WeightedBranchingResumption.contributions (source program clause) fuel before :=
  NeedWeightedResumption.handler_agrees _ _ _ _

/-- Native execution is interpreted by the actual Mathlib writer/list handler. -/
theorem native_kleisli_handler_agrees {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat) (before : WorkState) :
    (ResumptionCategory.handle WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (source program clause) fuel before)).run =
      WeightedBranchingResumption.contributions (source program clause) fuel before :=
  native_handler_agrees program clause fuel before

/-- Both the ordered coefficient and the complete residual world survive a split run. -/
theorem native_resume_exact {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row)
    (first second : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions (source program clause) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions (source program clause) first before)
        (fun leaf => match leaf with
          | .inl done => [(.inl done, (1 : V))]
          | .inr pending =>
              WeightedBranchingResumption.contributions (source program clause) second pending) :=
  by
    rw [WeightedBranchingResumption.contributions_add]
    apply congrArg (WeightedResumption.sequence
      (WeightedBranchingResumption.contributions (source program clause) first before))
    funext leaf
    cases leaf <;> rfl

/-- Declared coefficient erasure recovers the separately implemented native
frontier. It preserves physical zero contributions; it is not a support filter. -/
theorem native_frontier_erasure {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat) (before : WorkState) :
    (WeightedBranchingResumption.contributions (source program clause) fuel before).map
      (fun leaf => (NeedWeightedResumption.retained leaf.1).state) =
      runFrontier (specification program) fuel [before.state] :=
  NeedWeightedResumption.batch_frontier_erasure _ _ _ _

/-- Observing halted values after erasure agrees with ordinary native answers. -/
theorem native_answers_erasure {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat) (before : WorkState) :
    ((WeightedBranchingResumption.contributions (source program clause) fuel before).map
      (fun leaf => (NeedWeightedResumption.retained leaf.1).state)).filterMap haltedOutcome =
      answers (specification program) fuel before.state := by
  rw [native_frontier_erasure]
  rfl

theorem native_returned_is_halted {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat)
    (before after : WorkState) (value : V)
    (member : (.inl after, value) ∈
      WeightedBranchingResumption.contributions (source program clause) fuel before) :
    isHalted after.state = true :=
  NeedWeightedResumption.returned_is_halted _ _ _ _ _ _ member

/-- The handler's retained evidence carries the original machine's exact cost. -/
theorem native_retained_transition_cost {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row)
    (initial : NativeMachine) (fuel : Nat)
    {leaf : (WorkState ⊕ WorkState) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions
      (source program clause) fuel (WorkOccurrence.root initial)) :
    (NeedWeightedResumption.retained leaf.1).state.work.transitions =
      initial.work.transitions + (NeedWeightedResumption.retained leaf.1).trace.length :=
  NeedWeightedResumption.retained_transition_cost _ _ _ _ member

/-! ## Prepared native operations with parent-controlled publication -/

/-- The native machine's executable path interpreter, used only to validate
captured occurrence inputs. It uses the actual Need step and outcome functions. -/
abbrev capturePathMachine (program : Program) (initialMachine : NativeMachine) :
    Mettapedia.Machines.OccurrenceMachineCore Unit NativeMachine Outcome :=
  NeedInferenceControl.Reference.pathMachine (specification program) initialMachine

section AuthoredHistories

open Mettapedia.GSLT.Ultrainfinite.Route

open _root_.CategoryTheory
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.OSLF.Binding

/-- Read physical authored choices from real machine events. This observation
omits administrative events; the original history still retains them. -/
def authoredRowAccount (program : Program) (initial : NativeMachine) :=
  eventAccount (capturePathMachine program initial)
    (fun before after _ => FreeMonoid.ofList (newRow before after).toList)

/-- Reading a machine history yields the independently defined authored-row
trace, with the exact number of machine transitions. -/
theorem history_row_trace (program : Program) (initial : NativeMachine)
    {before after : RewriteEventHistory.State (system (capturePathMachine program initial))}
    (history : Quiver.Path before after) :
    RowTrace program (indices (capturePathMachine program initial) history).length
      before.term after.term
      (FreeMonoid.toList ((authoredRowAccount program initial).of history)) := by
  exact ObservedTrace.map _ _
    (fun event => ⟨event.val, event.property⟩) (fun _ => rfl)
    (history_observed_trace (capturePathMachine program initial)
      (fun before after _ => (newRow before after).toList) history)

/-- Every trace admitted by the independent row relation has a machine history.
This is coverage at the row observation, not uniqueness of a history after
administrative events or repeated occurrences have been forgotten. -/
theorem row_trace_history (program : Program) (initial : NativeMachine)
    {count : Nat} {before after : NativeMachine} {choices : List Row}
    (trace : RowTrace program count before after choices) :
    ∃ history : History (capturePathMachine program initial) before after,
      (indices (capturePathMachine program initial) history).length = count ∧
      FreeMonoid.toList ((authoredRowAccount program initial).of history) = choices := by
  apply observed_trace_history (capturePathMachine program initial)
    (fun before after _ => (newRow before after).toList)
  exact ObservedTrace.map _ _
    (fun edge => ⟨edge.index, edge.successorAt⟩) (fun _ => rfl) trace

/-- Interpreting authored provenance recovers the native history coefficient.
Multiplication follows the history order; no commutativity is assumed. -/
theorem history_row_interpretation {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (initial : NativeMachine)
    {before after : RewriteEventHistory.State (system (capturePathMachine program initial))}
    (history : Quiver.Path before after) :
    interpret clause (FreeMonoid.toList ((authoredRowAccount program initial).of history)) =
      (NeedWeightedResumption.coefficientAccount (specification program)
        (edgeGrade clause) initial).of history := by
  let change : FreeMonoid Row →* V := FreeMonoid.lift (fun row => WeighClause.eval row clause)
  have accounts := eventAccount_map (capturePathMachine program initial)
    (fun before after _ => FreeMonoid.ofList (newRow before after).toList) change
  have grades :
      (fun (before after : NativeMachine) (_ : Nat) =>
        change (FreeMonoid.ofList (newRow before after).toList)) =
      (fun before after (_ : Nat) => edgeGrade clause before after) := by
    funext before after index
    cases chosen : newRow before after <;>
      simp [change, edgeGrade, chosen]
  rw [grades] at accounts
  have evaluated := congrArg (fun account => account.of history) accounts
  change change ((authoredRowAccount program initial).of history) =
    (NeedWeightedResumption.coefficientAccount (specification program)
      (edgeGrade clause) initial).of history at evaluated
  simpa only [change, FreeMonoid.lift_apply, interpret,
    ProvenanceInterpretation.interpDeriv] using evaluated

/-- Every independently admitted row trace is represented in the weighted
native frontier at its exact transition depth. The complete producing trace
and coefficient remain, including contributions whose coefficient is zero. -/
theorem row_trace_covered {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (initial : NativeMachine)
    {count : Nat} {before after : NativeMachine} {choices : List Row}
    (trace : RowTrace program count before after choices) (priorTrace : List Nat) :
    ∃ events : List Nat,
      events.length = count ∧
      (capturePathMachine program initial).follow before events = some after ∧
      (.inr ⟨after, priorTrace ++ events⟩, interpret clause choices) ∈
        WeightedBranchingResumption.contributions (source program clause)
          count ⟨before, priorTrace⟩ := by
  obtain ⟨history, depth, rows⟩ := row_trace_history program initial trace
  refine ⟨indices (capturePathMachine program initial) history, depth,
    follow_indices _ history, ?_⟩
  have present := NeedWeightedResumption.history_pending_contribution
    (specification program) (edgeGrade clause) initial history priorTrace
  have coefficient := history_row_interpretation program clause initial history
  rw [rows] at coefficient
  rw [← coefficient] at present
  simpa only [source, capturePathMachine, depth] using present

/-- Bounded recording of the actual Need controller retains its complete
semantic snapshot after erasure. The observer cannot select work or alter
worlds; this comparison fixes the original controller and tick allowance. -/
theorem recording_erasure {Memory Event : Type}
    (program : Program) (base : Controller WorkState (Outcome × List Nat) Memory)
    (observe : Memory → WorkState → Option (Outcome × List Nat) → List WorkState → Event)
    (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot WorkState (Outcome × List Nat) Memory) :
    Recording.erase (Recording.runSelected (occurrenceSystem program)
      base observe fuel (Recording.start snapshot capacity)) =
        Snapshot.run (occurrenceSystem program) base fuel snapshot := by
  rw [Recording.runSelected_erasure, Recording.erase_start]

/-- Each retained selected Need occurrence has its ordinary replay history
and independently admitted authored-row trace. Recording exhaustion does not
certify search exhaustion, and the trace is relative to this program and root. -/
theorem recorded_authored_history {Memory : Type}
    (program : Program) (base : Controller WorkState (Outcome × List Nat) Memory)
    (initial : NativeMachine) (capacity fuel : Nat) (record : Recording.Prefix WorkState)
    (retained : (Snapshot.run (occurrenceSystem program)
      (Recording.controller base (fun _ selected _ _ => selected) (some capacity)) fuel
        (Recording.start (Snapshot.initial base [WorkOccurrence.root initial])
          (some capacity))).memory.2 = some record)
    {node : WorkState} (member : node ∈ record.items) :
    ∃ history : History (capturePathMachine program initial) initial node.state,
      indices (capturePathMachine program initial) history = node.trace ∧
      RowTrace program node.trace.length initial node.state
        (FreeMonoid.toList ((authoredRowAccount program initial).of history)) := by
  have replay := Recording.retained_occurrence_replays
    (capturePathMachine program initial) base initial capacity fuel record retained member
  let history := ofTrace (capturePathMachine program initial) node.trace replay
  have exactTrace : indices (capturePathMachine program initial) history = node.trace :=
    indices_ofTrace _ _ replay
  refine ⟨history, exactTrace, ?_⟩
  simpa only [exactTrace] using history_row_trace program initial history

end AuthoredHistories

def captureDomain (program : Program) (initialMachine : NativeMachine)
    (node : WorkState) : Prop :=
  WorkOccurrence.ValidFrom (capturePathMachine program initialMachine) initialMachine node

/-- Both returned and pending weighted contributions retain a replayable
history in the shared event category. The same history accounts for the ordered
coefficient and actual Need transition counter, including physical zero-weight contributions. This
is an executable semantic-machine statement, not a C-memory refinement. -/
theorem native_retained_history {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row)
    (initial : NativeMachine) (fuel : Nat)
    {leaf : (WorkState ⊕ WorkState) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions
      (source program clause) fuel (WorkOccurrence.root initial)) :
    ∃ history : Mettapedia.GSLT.Causality.OccurrenceMachineHistory.History
        (capturePathMachine program initial) initial
        (NeedWeightedResumption.retained leaf.1).state,
      Mettapedia.GSLT.Causality.OccurrenceMachineHistory.indices
          (capturePathMachine program initial) history =
        (NeedWeightedResumption.retained leaf.1).trace ∧
      (NeedWeightedResumption.coefficientAccount (specification program)
        (edgeGrade clause) initial).of history = leaf.2 ∧
      (NeedWeightedResumption.retained leaf.1).state.work.transitions =
        initial.work.transitions +
          (Mettapedia.GSLT.Causality.OccurrenceMachineHistory.indices
            (capturePathMachine program initial) history).length := by
  obtain ⟨history, trace, coefficient⟩ := NeedWeightedResumption.retained_history
    (specification program) (edgeGrade clause) initial fuel (WorkOccurrence.root initial) member
  have exactTrace : Mettapedia.GSLT.Causality.OccurrenceMachineHistory.indices
      (capturePathMachine program initial) history =
      (NeedWeightedResumption.retained leaf.1).trace := by
    simpa [WorkOccurrence.root] using trace
  refine ⟨history, exactTrace, coefficient, ?_⟩
  erw [exactTrace]
  exact native_retained_transition_cost program clause initial fuel member

/-- Every retained contribution is interpreted from an independently valid
row trace, and each recorded row has authored activation authority. This includes
a suspended body or a coefficient of zero. -/
theorem native_retained_provenance {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row)
    (initial : NativeMachine) (fuel : Nat)
    {leaf : (WorkState ⊕ WorkState) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions
      (source program clause) fuel (WorkOccurrence.root initial)) :
    ∃ choices : List Row,
      RowTrace program (NeedWeightedResumption.retained leaf.1).trace.length
        initial (NeedWeightedResumption.retained leaf.1).state choices ∧
      interpret clause choices = leaf.2 ∧
      ∀ row ∈ choices, ∃ (head : String) (arguments : List CellId),
        Activates program head arguments (.equation row.index)
          (.evaluate row.body row.environment) := by
  obtain ⟨history, trace, coefficient, _⟩ :=
    native_retained_history program clause initial fuel member
  have rows := history_row_trace program initial history
  erw [trace] at rows
  refine ⟨FreeMonoid.toList ((authoredRowAccount program initial).of history), rows, ?_, ?_⟩
  · exact (history_row_interpretation program clause initial history).trans coefficient
  · exact fun row member => row_trace_admitted program rows row member

/-- The initial machine and source program belong to the capture scope. Within
that scope an executable occurrence path identifies the whole machine input. -/
def captureInput (before after : WorkState) : Bool := decide (before.trace = after.trace)

theorem captureInput_sound (program : Program) (initialMachine : NativeMachine) :
    Preparation.SoundMatch (occurrenceSystem program) (captureDomain program initialMachine)
      captureInput := by
  intro before after beforeValid afterValid accepted
  have traces : before.trace = after.trace := by simpa [captureInput] using accepted
  have same := WorkOccurrence.eq_of_valid_trace
    (capturePathMachine program initialMachine) beforeValid afterValid traces
  subst after
  exact ⟨rfl, rfl⟩

theorem captureDomain_closed (program : Program) (initialMachine : NativeMachine)
    (before : WorkState) (valid : captureDomain program initialMachine before)
    (after : WorkState) (member : after ∈ (occurrenceSystem program).successors before) :
    captureDomain program initialMachine after :=
  WorkOccurrence.successor_valid (capturePathMachine program initialMachine) valid member

abbrev PreparedSession (Memory : Type*) :=
  Preparation.Session (List Nat) WorkState (Outcome × List Nat) Memory

def preparedInitial {Memory : Type*}
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) : PreparedSession Memory :=
  ⟨Snapshot.initial controller [WorkOccurrence.root initialMachine], fun _ => none⟩

theorem preparedInitial_valid {Memory : Type*} (program : Program)
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) :
    (preparedInitial controller initialMachine).Valid (occurrenceSystem program)
      (captureDomain program initialMachine) := by
  constructor
  · exact Preparation.empty_valid _ _
  · intro node member
    have root : node = WorkOccurrence.root initialMachine := by
      simpa [preparedInitial, Snapshot.initial, Mettapedia.GSLT.Core.BranchingTemporal.initial]
        using member
    subst node
    exact WorkOccurrence.root_valid (capturePathMachine program initialMachine) initialMachine

/-- Arbitrary preparation/publication slices preserve the actual native
ordered prefix and complete residual worlds. Preparation may spend speculative
work; this statement does not identify that expenditure with serial cost. -/
theorem native_prepared_prefix_exact {Memory : Type*} (program : Program)
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) (actions : List (Preparation.Action WorkState))
    (admitted : ∀ action ∈ actions, ∀ node ∈ action.inputs,
      captureDomain program initialMachine node) :
    (Preparation.execute (occurrenceSystem program) controller WorkOccurrence.trace captureInput
      actions (preparedInitial controller initialMachine)).state =
      Snapshot.run (occurrenceSystem program) controller (Preparation.publications actions)
        (Snapshot.initial controller [WorkOccurrence.root initialMachine]) :=
  Preparation.execute_agrees _ _ _ _ _ (captureInput_sound program initialMachine)
    (captureDomain_closed program initialMachine) actions _
    (preparedInitial_valid program controller initialMachine) admitted

/-- A bounded physical executor owns the still-unexecuted transcript together
with its prepared captures and original native snapshot. -/
def preparedCheckpoint {Memory : Type*}
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) (actions : List (Preparation.Action WorkState)) :
    Preparation.Checkpoint (List Nat) WorkState (Outcome × List Nat) Memory :=
  ⟨preparedInitial controller initialMachine, actions, 0⟩

/-- Strict input refusal and exhausted executor budget preserve the actual
native prefix at its accepted parent-tick count. The whole checkpoint retains
private captures and every unfinished physical action, including a refused
publication. Its tick counter is not a speculative cost receipt. -/
theorem native_prepared_checked_prefix {Memory : Type*} (program : Program)
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) (actions : List (Preparation.Action WorkState))
    (admitted : ∀ action ∈ actions, ∀ node ∈ action.inputs,
      captureDomain program initialMachine node) (fuel : Nat) :
    let result := Preparation.Checkpoint.run (occurrenceSystem program) controller
      WorkOccurrence.trace captureInput fuel (preparedCheckpoint controller initialMachine actions)
    result.session.state = Snapshot.run (occurrenceSystem program) controller result.ticks
      (Snapshot.initial controller [WorkOccurrence.root initialMachine]) := by
  apply Preparation.Checkpoint.run_agrees (occurrenceSystem program) controller
    WorkOccurrence.trace (captureDomain program initialMachine) captureInput
    (captureInput_sound program initialMachine) (captureDomain_closed program initialMachine)
  · exact ⟨preparedInitial_valid program controller initialMachine, admitted⟩
  · rfl

/-- Cumulative accepted ticks, unfinished actions and captured native worlds
are transported together on a bounded resume, without replaying the prefix. -/
theorem native_checked_resume_exact {Memory : Type*} (program : Program)
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (point : Preparation.Checkpoint (List Nat) WorkState (Outcome × List Nat) Memory)
    (first second : Nat) :
    Preparation.Checkpoint.run (occurrenceSystem program) controller WorkOccurrence.trace
      captureInput (first + second) point =
      Preparation.Checkpoint.run (occurrenceSystem program) controller WorkOccurrence.trace
        captureInput second (Preparation.Checkpoint.run (occurrenceSystem program) controller
          WorkOccurrence.trace captureInput first point) :=
  Preparation.Checkpoint.run_add _ _ _ _ _ _ _

/-- Root paths coincide across different goals. The program/initial-machine
scope in the input authority is therefore necessary. -/
theorem captureInput_root_scopes_collide (before after : NativeMachine) :
    captureInput (WorkOccurrence.root before) (WorkOccurrence.root after) = true := by
  simp [captureInput, WorkOccurrence.root]

/-- The scope check refuses a root belonging to a different authored goal,
even though its successor-index key is the same empty path. -/
theorem different_goal_capture_refused (program : Program) :
    ¬ captureDomain program (initial (.symbol "left"))
      (WorkOccurrence.root (initial (.symbol "right"))) := by
  intro valid
  have equality : initial (.symbol "left") = initial (.symbol "right") := by
    simpa [captureDomain, WorkOccurrence.ValidFrom, WorkOccurrence.root,
      Mettapedia.Machines.OccurrenceMachineCore.follow] using valid
  have lookupEquality := congrArg (fun machine => machine.world.heap.lookup rootCell) equality
  simp [initial, Heap.lookup] at lookupEquality

section PendingCoefficients

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- An absent annotation follows the original successor directly. An authored
annotation starts an actual coefficient computation at the captured row. -/
def coefficientJob {V : Type} [One V] (annotation : Row → Option Atom)
    (before after : NativeMachine) : V ⊕ Score :=
  match NativeGradeAttachment.captureNext before after with
  | none => .inl 1
  | some capture =>
      match annotation capture.row with
      | none => .inl 1
      | some expression => .inr (capture.score expression)

/-- Only an actually halted scoring machine has returned its result. Each
other quantum is an ordinary Need transition, retaining the capture. -/
def coefficientSource (program : Program) : Score → Score ⊕ List Score :=
  fun score => if isHalted score.machine then .inl score else .inr (scoreStep program score)

def coefficientReadout {V : Type} (interpretation : Outcome → Option V)
    (score : Score) : Option V := (scoreResult score).bind interpretation

/-- Semantic scoring shares the captured lazy world with its continuation.
It restores the retained body control and adds actual scoring work once.
Scheduling advice deliberately uses a different, detached continuation. -/
def resumeCoefficientMachine (machine : NativeMachine) (score : Score) : NativeMachine :=
  { machine with world := score.machine.world, work := machine.work.add score.machine.work }

def resumeCoefficient (body : WorkState) (score : Score) : WorkState :=
  { body with state := resumeCoefficientMachine body.state score }

/-- Nested scoring restores a parent's exact instruction and origin while
retaining the child's completed lazy world and expenditure. -/
def resumeCoefficientScore (parent child : Score) : Score :=
  { parent with machine := resumeCoefficientMachine parent.machine child }

/-- Scoring follows actual Need instructions and may evaluate a captured
child coefficient before restoring its parent. The return is permitted only
for a halted child belonging to that exact suspended machine. This relation
does not identify a nested return with an ordinary Need instruction. -/
inductive ScoreEvaluation (program : Program) : Score → Score → Prop where
  | root (score : Score) : ScoreEvaluation program score score
  | step {initial before after : Score} :
      ScoreEvaluation program initial before → after ∈ scoreStep program before →
      ScoreEvaluation program initial after
  | resume {initial parent child : Score} :
      ScoreEvaluation program initial parent →
      ScoreEvaluation program (child.origin.score child.expression) child →
      child.origin.body = parent.machine → isHalted child.machine = true →
      ScoreEvaluation program initial (resumeCoefficientScore parent child)

theorem score_evaluation_keeps_capture (program : Program) (initial next : Score)
    (evaluated : ScoreEvaluation program initial next) :
    next.origin = initial.origin ∧ next.expression = initial.expression := by
  induction evaluated with
  | root => exact ⟨rfl, rfl⟩
  | step _ member ih =>
      obtain ⟨origin, expression, _⟩ := score_step_origin program _ _ member
      exact ⟨origin.trans ih.1, expression.trans ih.2⟩
  | resume _ _ _ _ parentIH _ => exact parentIH

/-- Every actual equation admission encountered while scoring belongs to
the same coefficient account. In particular, an argument forced by a score
does not lose its own annotation when its cell is subsequently reused. -/
def gradedCoefficientSource {V : Type} [One V] (program : Program)
    (annotation : Row → Option Atom) :
    WeightedBranchingResumption.Coalgebra Score Score (V ⊕ Score) :=
  fun score => if isHalted score.machine then .inl score else
    .inr ((scoreStep program score).map fun next =>
      (next, coefficientJob annotation score.machine next.machine))

abbrev NestedWork := WeightedBranchingResumption.NestedPendingState WorkState Score
abbrev NestedResult :=
  WeightedBranchingResumption.NestedPendingAnswer WorkState WorkState Score Score

/-- A completed value observation reads the retained native control.
Retryable and stable faults remain full returns in the contribution list;
this selected value readout does not count them as successful values. -/
def completedValue (body : WorkState) : Option Atom :=
  match body.state.control with
  | .halted (.value value) => some value
  | _ => none

/-- The same completed value observation works for flat and nested pending
work. Parked grades and cut states are never emitted as body values. -/
def completedValues {V Retained Work : Type}
    (leaves : WeightedResumption.Contributions ((WorkState ⊕ Retained) ⊕ Work) V) :
    WeightedResumption.Contributions Atom V :=
  WeightedBranchingResumption.nestedSelected completedValue leaves

/-- Satisfying a value request may coexist with retained work. Claiming a
shortage requires absence of both parked grade results and pending states. -/
def nestedValueOutcome {V Retained Work : Type} (requested : Nat)
    (leaves : WeightedResumption.Contributions ((WorkState ⊕ Retained) ⊕ Work) V) :
    Mettapedia.GSLT.Core.BoundedSelection.SelectOutcome :=
  WeightedBranchingResumption.nestedSelectionOutcome completedValue requested leaves

theorem native_nested_value_saturation_iff {V Job Grade : Type} (requested : Nat)
    (leaves : WeightedResumption.Contributions
      (WeightedBranchingResumption.NestedPendingAnswer WorkState WorkState Job Grade ⊕
        WeightedBranchingResumption.NestedPendingState WorkState Job) V) :
    nestedValueOutcome requested leaves = .saturated ↔
      (completedValues leaves).length < requested ∧
        WeightedBranchingResumption.parkedGrades
          (WeightedBranchingResumption.nestedObligations leaves) = [] ∧
        WeightedBranchingResumption.pendingInstructions
          (WeightedBranchingResumption.nestedObligations leaves) = [] :=
  WeightedBranchingResumption.nested_selection_saturated_iff completedValue requested leaves

/-- The nested adapter uses the shared pending-coefficient stack. Both body
and score instructions run through the original Need step relation. -/
def nestedSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V) :
    WeightedBranchingResumption.Coalgebra NestedWork NestedResult V :=
  WeightedBranchingResumption.nestedPendingSource
    (NeedWeightedResumption.source (specification program) (coefficientJob annotation))
    (gradedCoefficientSource program annotation) (coefficientReadout interpretation)
    resumeCoefficient resumeCoefficientScore

def nestedAdmittedSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (admit : V → Bool) :
    WeightedBranchingResumption.Coalgebra NestedWork NestedResult V :=
  WeightedBranchingResumption.admittingSourceAt
    (nestedSource program annotation interpretation)
    (fun pending => match pending with
      | .inl _ => false
      | .inr (_, score, _) => isHalted score.machine) admit

/-- Nested admission preserves whole surviving occurrences, including all
parent frames. It cannot manufacture a contribution or replace its residual. -/
theorem native_nested_admitted_occurrences_sublist {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : NestedWork) :
    List.Sublist
      (WeightedBranchingResumption.contributions
        (nestedAdmittedSource program annotation interpretation admit) fuel before)
      (WeightedBranchingResumption.contributions
        (nestedSource program annotation interpretation) fuel before) :=
  WeightedBranchingResumption.admittingAt_contributions_sublist _ _ _ _ _

/-- A returned unknown grade is already parked, so later slices do not
poll it or repeat its scoring work. Its original factor and owned stack
remain a physical occurrence while other pending instructions continue. -/
theorem native_nested_parked_persists {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (first second : Nat) (before : NestedWork) :
    (WeightedBranchingResumption.parkedGrades
      (WeightedBranchingResumption.nestedObligations
        (WeightedBranchingResumption.contributions
          (nestedAdmittedSource program annotation interpretation admit) first before))).Sublist
    (WeightedBranchingResumption.parkedGrades
      (WeightedBranchingResumption.nestedObligations
        (WeightedBranchingResumption.contributions
          (nestedAdmittedSource program annotation interpretation admit)
          (first + second) before))) :=
  WeightedBranchingResumption.nested_parked_sublist_add _ _ _ _

/-- Refusing a completed inner coefficient exposes no executable parent
continuation. The parent and body have not run past this admission boundary. -/
theorem native_nested_parent_refused {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (body : WorkState) (child parent : Score) (parents : List Score) (value : V)
    (halted : isHalted child.machine = true)
    (decoded : coefficientReadout interpretation child = some value)
    (refused : admit value = false) :
    nestedAdmittedSource program annotation interpretation admit
      (.inr (body, child, parent :: parents)) = .inr [] := by
  simp [nestedAdmittedSource, WeightedBranchingResumption.admittingSourceAt,
    WeightedBranchingResumption.admittingSource,
    nestedSource, WeightedBranchingResumption.nestedPendingSource,
    gradedCoefficientSource, halted, decoded, refused]

/-- An uninterpreted inner coefficient remains a retained result with its
entire stack, regardless of the test on interpreted coefficients. -/
theorem native_nested_unknown_retains_stack {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (body : WorkState) (score : Score) (parents : List Score)
    (halted : isHalted score.machine = true)
    (unknown : coefficientReadout interpretation score = none) :
    nestedAdmittedSource program annotation interpretation admit (.inr (body, score, parents)) =
      .inl (.inr (body, score, parents)) := by
  simp [nestedAdmittedSource, WeightedBranchingResumption.admittingSourceAt,
    WeightedBranchingResumption.admittingSource,
    nestedSource, WeightedBranchingResumption.nestedPendingSource,
    gradedCoefficientSource, halted, unknown]

theorem nested_resume_preserves_parent (parent child : Score) :
    (resumeCoefficientScore parent child).origin = parent.origin ∧
    (resumeCoefficientScore parent child).expression = parent.expression ∧
    (resumeCoefficientScore parent child).machine.control = parent.machine.control ∧
    (resumeCoefficientScore parent child).machine.world = child.machine.world ∧
    (resumeCoefficientScore parent child).machine.work =
      parent.machine.work.add child.machine.work := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A split preserves all parent coefficient frames together with the body,
worlds and ordered product. No completed inner factor is charged again. -/
theorem native_nested_resume_exact {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (first second : Nat) (before : NestedWork) :
    WeightedBranchingResumption.contributions
      (nestedSource program annotation interpretation) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions
          (nestedSource program annotation interpretation) first before)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : V))]
          | .inr pending => WeightedBranchingResumption.contributions
              (nestedSource program annotation interpretation) second pending) := by
  rw [WeightedBranchingResumption.contributions_add]
  apply congrArg (WeightedResumption.sequence
    (WeightedBranchingResumption.contributions
      (nestedSource program annotation interpretation) first before))
  funext leaf
  cases leaf <;> rfl

abbrev PendingWork := WeightedBranchingResumption.PendingState WorkState Score
abbrev PendingResult := WeightedBranchingResumption.PendingAnswer WorkState WorkState Score

/-- This one-level interpretation executes scoring steps without further
annotations. The nested interpretation above is required when a score forces
graded argument work; the distinction has an executable negative control. -/
def pendingSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V) :
    WeightedBranchingResumption.Coalgebra PendingWork PendingResult V :=
  WeightedBranchingResumption.pendingSource
    (NeedWeightedResumption.source (specification program) (coefficientJob annotation))
    (coefficientSource program) (coefficientReadout interpretation) resumeCoefficient

/-- Candidate admission uses the same captured coefficient computation as
attachment. The declared test runs at its returned coefficient, before the
retained body has an executable successor. It is not a scheduling priority.
The test must already be resolved; a comparison computation belongs in the
pending coefficient job rather than an invented Boolean answer here. -/
def pendingAdmittedSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (admit : V → Bool) :
    WeightedBranchingResumption.Coalgebra PendingWork PendingResult V :=
  WeightedBranchingResumption.admittingSourceAt
    (pendingSource program annotation interpretation)
    (fun pending => match pending with
      | .inl _ => false
      | .inr (_, score) => isHalted score.machine) admit

/-- Admission cannot invent a result, duplicate it, change its coefficient,
or replace its open world. This compares complete occurrence lists, before
any aggregation or support readout. -/
theorem native_admitted_occurrences_sublist {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : PendingWork) :
    List.Sublist
      (WeightedBranchingResumption.contributions
        (pendingAdmittedSource program annotation interpretation admit) fuel before)
      (WeightedBranchingResumption.contributions
        (pendingSource program annotation interpretation) fuel before) :=
  WeightedBranchingResumption.admittingAt_contributions_sublist _ _ _ _ _

/-- A rejected coefficient exposes no body successor. Filtering an already
executed body at the answer read would not satisfy this boundary. -/
theorem native_admitted_body_refused {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (body : WorkState) (score : Score) (value : V)
    (halted : isHalted score.machine = true)
    (decoded : coefficientReadout interpretation score = some value)
    (refused : admit value = false) :
    pendingAdmittedSource program annotation interpretation admit (.inr (body, score)) =
      .inr [] := by
  simp [pendingAdmittedSource, WeightedBranchingResumption.admittingSourceAt,
    WeightedBranchingResumption.admittingSource,
    pendingSource, WeightedBranchingResumption.pendingSource, coefficientSource,
    halted, decoded, refused]

/-- An admitted coefficient resumes the exact retained control with the
score's completed lazy world, and contributes its value once. -/
theorem native_admitted_body_resumes {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (body : WorkState) (score : Score) (value : V)
    (halted : isHalted score.machine = true)
    (decoded : coefficientReadout interpretation score = some value)
    (accepted : admit value = true) :
    pendingAdmittedSource program annotation interpretation admit (.inr (body, score)) =
      .inr [(.inl (resumeCoefficient body score), value)] := by
  simp [pendingAdmittedSource, WeightedBranchingResumption.admittingSourceAt,
    WeightedBranchingResumption.admittingSource,
    pendingSource, WeightedBranchingResumption.pendingSource, coefficientSource,
    halted, decoded, accepted]

@[simp] theorem coefficient_job_unannotated {V : Type} [One V]
    (before after : NativeMachine) :
    coefficientJob (V := V) (fun _ => none) before after = .inl 1 := by
  cases inspected : NativeGradeAttachment.captureNext before after <;>
    simp [coefficientJob, inspected]

theorem unannotated_body_is_settled {V : Type} [One V] (program : Program) :
    NeedWeightedResumption.source (specification program)
      (coefficientJob (V := V) (fun _ => none)) =
    WeightedBranchingResumption.settledBody
      (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V))) := by
  funext state
  cases control : state.state.control <;>
    simp only [NeedWeightedResumption.source, control,
      WeightedBranchingResumption.settledBody, NeedWeightedResumption.successors,
      List.map_map, coefficient_job_unannotated] <;> rfl

/-- An unannotated native program has the exact original contributions at
the same budget. It creates no scoring job or administrative scoring step. -/
theorem native_pending_unannotated_exact {V : Type} [Monoid V] (program : Program)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (pendingSource program (fun _ => none) interpretation) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (WeightedBranchingResumption.settledLeaf leaf.1, leaf.2)) := by
  unfold pendingSource
  rw [unannotated_body_is_settled]
  exact WeightedBranchingResumption.pending_settled_agrees _ _ _ _ _ _

/-- Extending the coefficient stack does not change an unannotated program,
including its exact finite budget, occurrence order and full residuals. -/
theorem native_nested_unannotated_exact {V : Type} [Monoid V] (program : Program)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (nestedSource program (fun _ => none) interpretation) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (Sum.map Sum.inl Sum.inl leaf.1, leaf.2)) := by
  unfold nestedSource
  rw [unannotated_body_is_settled]
  exact WeightedBranchingResumption.nested_pending_settled_agrees _ _ _ _ _ _ _

/-- An authored guard does not test plain or administrative unit edges.
Unannotated programs keep their exact ordinary frontier, for any predicate. -/
theorem native_admitted_unannotated_exact {V : Type} [Monoid V] (program : Program)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (pendingAdmittedSource program (fun _ => none) interpretation admit) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (WeightedBranchingResumption.settledLeaf leaf.1, leaf.2)) := by
  unfold pendingAdmittedSource pendingSource
  rw [unannotated_body_is_settled]
  apply WeightedBranchingResumption.contributions_reindex
    (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
    _ Sum.inl Sum.inl ?_ fuel before
  intro state
  cases inspected : NeedWeightedResumption.source (specification program)
      (fun _ _ => (1 : V)) state <;>
    simp [WeightedBranchingResumption.admittingSourceAt,
      WeightedBranchingResumption.pendingSource, WeightedBranchingResumption.settledBody,
      inspected, List.map_map]

/-- Nested authored admission also preserves unannotated execution even
when the predicate would reject the unit coefficient of an ordinary step. -/
theorem native_nested_admitted_unannotated_exact {V : Type} [Monoid V]
    (program : Program) (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (nestedAdmittedSource program (fun _ => none) interpretation admit) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (Sum.map Sum.inl Sum.inl leaf.1, leaf.2)) := by
  unfold nestedAdmittedSource nestedSource
  rw [unannotated_body_is_settled]
  apply WeightedBranchingResumption.contributions_reindex
    (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
    _ Sum.inl Sum.inl ?_ fuel before
  intro state
  cases inspected : NeedWeightedResumption.source (specification program)
      (fun _ _ => (1 : V)) state <;>
    simp [WeightedBranchingResumption.admittingSourceAt,
      WeightedBranchingResumption.nestedPendingSource, WeightedBranchingResumption.settledBody,
      inspected, List.map_map]

/-- The physical admission, world and variable cells supply the coefficient;
neither a later environment nor a second enumeration supplies its bindings. -/
theorem coefficient_job_actual_capture {V : Type} [One V]
    (annotation : Row → Option Atom) (before after : NativeMachine)
    (capture : Captured) (expression : Atom)
    (captured : NativeGradeAttachment.captureNext before after = some capture)
    (authored : annotation capture.row = some expression) :
    coefficientJob (V := V) annotation before after = .inr (capture.score expression) ∧
    (capture.score expression).machine.world = after.world ∧
    (capture.score expression).machine.control =
      .run (.evaluate expression capture.row.environment) [] := by
  obtain ⟨same, _⟩ := NativeGradeAttachment.captured_next_exact before after capture captured
  refine ⟨by simp [coefficientJob, captured, authored], ?_, rfl⟩
  simpa only [Captured.score, Captured.body] using
    congrArg (fun machine : NativeMachine => machine.world) same

/-- A coefficient job retains the actual selected row and its authored
expression. The witness comes from capture, before scoring or body execution. -/
theorem coefficient_job_capture {V : Type} [One V]
    (annotation : Row → Option Atom) (before after : NativeMachine) (score : Score)
    (chosen : coefficientJob (V := V) annotation before after = .inr score) :
    ∃ capture expression,
      NativeGradeAttachment.captureNext before after = some capture ∧
      annotation capture.row = some expression ∧ score = capture.score expression := by
  cases captured : NativeGradeAttachment.captureNext before after with
  | none => simp [coefficientJob, captured] at chosen
  | some capture =>
      cases authored : annotation capture.row with
      | none => simp [coefficientJob, captured, authored] at chosen
      | some expression =>
          simp only [coefficientJob, captured, authored, Sum.inr.injEq] at chosen
          exact ⟨capture, expression, rfl, authored, chosen.symm⟩

theorem coefficient_job_starts_at_zero {V : Type} [One V]
    (annotation : Row → Option Atom) (before after : NativeMachine) (score : Score)
    (chosen : coefficientJob (V := V) annotation before after = .inr score) :
    score.machine.work.transitions = 0 := by
  obtain ⟨_, _, _, _, rfl⟩ := coefficient_job_capture annotation before after score chosen
  rfl

theorem coefficient_running_uses_need (program : Program) (score next : Score)
    (running : isHalted score.machine = false)
    (member : next ∈ scoreStep program score) :
    coefficientSource program score = .inr (scoreStep program score) ∧
    next.origin = score.origin ∧ next.expression = score.expression ∧
    next.machine.work.transitions = score.machine.work.transitions + 1 := by
  exact ⟨by simp [coefficientSource, running], score_step_origin program score next member⟩

theorem resume_coefficient_preserves_continuation (body : WorkState) (score : Score) :
    (resumeCoefficient body score).state.control = body.state.control ∧
    (resumeCoefficient body score).trace = body.trace ∧
    (resumeCoefficient body score).state.world = score.machine.world ∧
    (resumeCoefficient body score).state.work.transitions =
      body.state.work.transitions + score.machine.work.transitions := ⟨rfl, rfl, rfl, rfl⟩

/-- A pending score belongs to this physical body's capture and has an actual
native scoring derivation from that capture, including its evolving world. -/
def CapturedCoefficient (program : Program) (body : WorkState) (score : Score) : Prop :=
  score.origin.body = body.state ∧
    Mettapedia.GSLT.Core.BranchingTemporal.Generated (scoringSystem program)
      [score.origin.score score.expression] score

theorem coefficient_job_has_captured_derivation {V : Type} [One V]
    (program : Program) (annotation : Row → Option Atom)
    (before body : WorkState) (score : Score)
    (chosen : coefficientJob (V := V) annotation before.state body.state = .inr score) :
    CapturedCoefficient program body score := by
  obtain ⟨capture, expression, captured, _, rfl⟩ :=
    coefficient_job_capture annotation before.state body.state score chosen
  obtain ⟨same, _⟩ := NativeGradeAttachment.captured_next_exact
    before.state body.state capture captured
  exact ⟨same, .root (by simp [Captured.score])⟩

theorem captured_coefficient_step (program : Program) (body : WorkState) (score next : Score)
    (valid : CapturedCoefficient program body score) (member : next ∈ scoreStep program score) :
    CapturedCoefficient program body next := by
  obtain ⟨origin, expression, _⟩ := score_step_origin program score next member
  refine ⟨(congrArg Captured.body origin).trans valid.1, ?_⟩
  rw [origin, expression]
  exact .successor valid.2 member

def pendingValid (program : Program) : PendingWork → Prop :=
  Sum.elim (fun _ => True) (fun held => CapturedCoefficient program held.1 held.2)

def pendingResultValid (program : Program) : PendingResult → Prop :=
  Sum.elim (fun body => isHalted body.state = true)
    (fun held => CapturedCoefficient program held.1 held.2 ∧ isHalted held.2.machine = true)

/-- Every pending coefficient has a native derivation from the correct
captured body. Completed body answers and uninterpreted coefficient results
have distinct, actual halt obligations. -/
theorem native_pending_valid {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : PendingWork) (valid : pendingValid program before) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) fuel before,
      Sum.elim (pendingResultValid program) (pendingValid program) leaf.1 := by
  apply WeightedBranchingResumption.contributions_invariant
    (pendingSource program annotation interpretation) (pendingValid program)
    (pendingResultValid program) ?_ ?_ fuel before valid
  · intro state answer inherited returned
    cases state with
    | inl body =>
        cases inspected : NeedWeightedResumption.source (specification program)
            (coefficientJob (V := V) annotation) body with
        | inl done =>
            simp only [pendingSource, WeightedBranchingResumption.pendingSource,
              inspected, Sum.inl.injEq] at returned
            subst answer
            obtain ⟨rfl, halted⟩ := (NeedWeightedResumption.source_return_iff
              (specification program) (coefficientJob annotation) body done).mp inspected
            exact halted
        | inr children =>
            simp [pendingSource, WeightedBranchingResumption.pendingSource, inspected] at returned
    | inr held =>
        rcases held with ⟨body, score⟩
        cases halted : isHalted score.machine with
        | false =>
            simp [pendingSource, WeightedBranchingResumption.pendingSource,
              coefficientSource, halted] at returned
        | true =>
            cases decoded : coefficientReadout interpretation score with
            | some value =>
                simp [pendingSource, WeightedBranchingResumption.pendingSource,
                  coefficientSource, halted, decoded] at returned
            | none =>
                simp only [pendingSource, WeightedBranchingResumption.pendingSource,
                  coefficientSource, halted, ↓reduceIte, decoded,
                  Sum.inl.injEq] at returned
                subst answer
                exact ⟨inherited, halted⟩
  · intro state alternatives inherited requested next member
    cases state with
    | inl body =>
        cases inspected : NeedWeightedResumption.source (specification program)
            (coefficientJob (V := V) annotation) body with
        | inl done =>
            simp [pendingSource, WeightedBranchingResumption.pendingSource, inspected] at requested
        | inr children =>
            simp only [pendingSource, WeightedBranchingResumption.pendingSource,
              inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            cases coefficient with
            | inl value => cases same; exact True.intro
            | inr score =>
                cases same
                have located : (child, Sum.inr score) ∈ NeedWeightedResumption.successors
                    (specification program) (coefficientJob (V := V) annotation) body := by
                  cases control : body.state.control <;>
                    simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr,
                      Sum.inr.injEq]
                obtain ⟨_, _, _, caused⟩ := (NeedWeightedResumption.successor_iff
                  (specification program) (coefficientJob annotation) body child (.inr score)).mp located
                exact coefficient_job_has_captured_derivation
                  program annotation body child score caused.symm
    | inr held =>
        rcases held with ⟨body, score⟩
        cases halted : isHalted score.machine with
        | false =>
            simp only [pendingSource, WeightedBranchingResumption.pendingSource,
              coefficientSource, halted, Bool.false_eq_true, ↓reduceIte,
              Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
            exact captured_coefficient_step program body score child inherited present
        | true =>
            cases decoded : coefficientReadout interpretation score with
            | none =>
                simp [pendingSource, WeightedBranchingResumption.pendingSource,
                  coefficientSource, halted, decoded] at requested
            | some value =>
                simp only [pendingSource, WeightedBranchingResumption.pendingSource,
                  coefficientSource, halted, ↓reduceIte, decoded,
                  Sum.inr.injEq] at requested
                subst alternatives
                have same := List.mem_singleton.mp member
                subst next
                exact True.intro

/-- Each nested frame keeps its authored expression and an evaluation from
its captured bindings. Its origin belongs to the exact suspended caller;
the outermost caller is the retained body. -/
def NestedCapturedCoefficient (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) : Score → List Score → Prop
  | score, [] =>
      annotation score.origin.row = some score.expression ∧
      ScoreEvaluation program (score.origin.score score.expression) score ∧
      score.origin.body = body.state
  | score, parent :: parents =>
      annotation score.origin.row = some score.expression ∧
      ScoreEvaluation program (score.origin.score score.expression) score ∧
      score.origin.body = parent.machine ∧
      NestedCapturedCoefficient program annotation body parent parents

/-- The stronger authored-evaluation invariant supplies the common caller
agreement used by phased coefficients and predicates. -/
theorem nested_capture_caller_agreement (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (score : Score) (parents : List Score)
    (valid : NestedCapturedCoefficient program annotation body score parents) :
    WeightedBranchingResumption.nestedCallerAgreement
      (fun body : WorkState => body.state) (fun held : Score => held.machine)
      (fun held : Score => held.origin.body) body score parents := by
  induction parents generalizing score with
  | nil => exact valid.2.2
  | cons parent rest ih => exact ⟨valid.2.2.1, ih parent valid.2.2.2⟩

theorem nested_capture_head (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (score : Score) (parents : List Score)
    (valid : NestedCapturedCoefficient program annotation body score parents) :
    annotation score.origin.row = some score.expression ∧
      ScoreEvaluation program (score.origin.score score.expression) score := by
  cases parents <;> exact ⟨valid.1, valid.2.1⟩

private theorem nested_capture_replace (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (before after : Score) (parents : List Score)
    (same : after.origin = before.origin)
    (evaluated : annotation after.origin.row = some after.expression ∧
      ScoreEvaluation program (after.origin.score after.expression) after)
    (valid : NestedCapturedCoefficient program annotation body before parents) :
    NestedCapturedCoefficient program annotation body after parents := by
  cases parents with
  | nil =>
      exact ⟨evaluated.1, evaluated.2, (congrArg Captured.body same).trans valid.2.2⟩
  | cons parent rest =>
      exact ⟨evaluated.1, evaluated.2,
        (congrArg Captured.body same).trans valid.2.2.1, valid.2.2.2⟩

theorem coefficient_job_nested_capture {V : Type} [One V]
    (program : Program) (annotation : Row → Option Atom)
    (before after : NativeMachine) (score : Score)
    (chosen : coefficientJob (V := V) annotation before after = .inr score) :
    annotation score.origin.row = some score.expression ∧
      ScoreEvaluation program (score.origin.score score.expression) score ∧
      score.origin.body = after := by
  obtain ⟨capture, expression, captured, authored, rfl⟩ :=
    coefficient_job_capture annotation before after score chosen
  obtain ⟨same, _⟩ := NativeGradeAttachment.captured_next_exact before after capture captured
  exact ⟨authored, .root _, same⟩

theorem nested_capture_step (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (score next : Score) (parents : List Score)
    (valid : NestedCapturedCoefficient program annotation body score parents)
    (member : next ∈ scoreStep program score) :
    NestedCapturedCoefficient program annotation body next parents := by
  obtain ⟨origin, expression, _⟩ := score_step_origin program score next member
  obtain ⟨authored, evaluated⟩ := nested_capture_head program annotation body score parents valid
  apply nested_capture_replace program annotation body score next parents origin ?_ valid
  rw [origin, expression]
  exact ⟨authored, .step evaluated member⟩

theorem nested_capture_resumes (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (child parent : Score) (parents : List Score)
    (valid : NestedCapturedCoefficient program annotation body child (parent :: parents))
    (halted : isHalted child.machine = true) :
    NestedCapturedCoefficient program annotation body
      (resumeCoefficientScore parent child) parents := by
  obtain ⟨_, childEvaluation, captured, parentValid⟩ := valid
  obtain ⟨authored, parentEvaluation⟩ :=
    nested_capture_head program annotation body parent parents parentValid
  apply nested_capture_replace program annotation body parent
    (resumeCoefficientScore parent child) parents rfl ?_ parentValid
  exact ⟨authored, .resume parentEvaluation childEvaluation captured halted⟩

/-- A child cannot restore a different caller, even when the callers came
from the same authored equation or their coefficient values coincide. -/
theorem nested_capture_wrong_parent_refused (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (child parent : Score) (parents : List Score)
    (different : child.origin.body.control ≠ parent.machine.control) :
    ¬ NestedCapturedCoefficient program annotation body child (parent :: parents) := by
  intro valid
  exact different (congrArg (fun machine : NativeMachine => machine.control) valid.2.2.1)

def nestedValid (program : Program) (annotation : Row → Option Atom) : NestedWork → Prop :=
  Sum.elim (fun _ => True)
    (fun held => NestedCapturedCoefficient program annotation held.1 held.2.1 held.2.2)

def nestedResultValid (program : Program) (annotation : Row → Option Atom) :
    NestedResult → Prop :=
  Sum.elim (fun body => isHalted body.state = true)
    (fun held => NestedCapturedCoefficient program annotation held.1 held.2.1 held.2.2 ∧
      isHalted held.2.1.machine = true)

/-- Every active or retained parent score belongs to its captured caller.
Actual Need transitions and completed child returns establish its evaluation;
unknown readouts retain this evidence and the complete parent stack. -/
theorem native_nested_valid {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : NestedWork) (valid : nestedValid program annotation before) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (nestedSource program annotation interpretation) fuel before,
      Sum.elim (nestedResultValid program annotation) (nestedValid program annotation) leaf.1 := by
  apply WeightedBranchingResumption.contributions_invariant
    (nestedSource program annotation interpretation) (nestedValid program annotation)
    (nestedResultValid program annotation) ?_ ?_ fuel before valid
  · intro state answer inherited returned
    cases state with
    | inl body =>
        cases inspected : NeedWeightedResumption.source (specification program)
            (coefficientJob (V := V) annotation) body with
        | inl done =>
            simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              inspected, Sum.inl.injEq] at returned
            subst answer
            obtain ⟨rfl, halted⟩ := (NeedWeightedResumption.source_return_iff
              (specification program) (coefficientJob annotation) body done).mp inspected
            exact halted
        | inr children =>
            simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              inspected] at returned
    | inr held =>
        rcases held with ⟨body, score, parents⟩
        cases halted : isHalted score.machine with
        | false =>
            simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              gradedCoefficientSource, halted] at returned
        | true =>
            cases decoded : coefficientReadout interpretation score with
            | some value =>
                cases parents <;>
                  simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                    gradedCoefficientSource, halted, decoded] at returned
            | none =>
                simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                  gradedCoefficientSource, halted, ↓reduceIte, decoded,
                  Sum.inl.injEq] at returned
                subst answer
                exact ⟨inherited, halted⟩
  · intro state alternatives inherited requested next member
    cases state with
    | inl body =>
        cases inspected : NeedWeightedResumption.source (specification program)
            (coefficientJob (V := V) annotation) body with
        | inl done =>
            simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              inspected] at requested
        | inr children =>
            simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            cases coefficient with
            | inl value => cases same; exact True.intro
            | inr score =>
                cases same
                have located : (child, Sum.inr score) ∈ NeedWeightedResumption.successors
                    (specification program) (coefficientJob (V := V) annotation) body := by
                  cases control : body.state.control <;>
                    simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr,
                      Sum.inr.injEq]
                obtain ⟨_, _, _, caused⟩ := (NeedWeightedResumption.successor_iff
                  (specification program) (coefficientJob annotation) body child (.inr score)).mp located
                exact coefficient_job_nested_capture program annotation body.state child.state
                  score caused.symm
    | inr held =>
        rcases held with ⟨body, score, parents⟩
        cases halted : isHalted score.machine with
        | false =>
            simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              gradedCoefficientSource, halted, Bool.false_eq_true, ↓reduceIte,
              List.map_map, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨child, present, same⟩ := List.mem_map.mp member
            dsimp only [Function.comp_apply] at same
            have childValid := nested_capture_step program annotation body score child parents
              inherited present
            cases chosen : coefficientJob (V := V) annotation score.machine child.machine with
            | inl value =>
                cases same
                simp only [chosen, nestedValid]
                exact childValid
            | inr inner =>
                cases same
                simp only [chosen, nestedValid]
                obtain ⟨authored, evaluated, captured⟩ := coefficient_job_nested_capture
                  program annotation score.machine child.machine inner chosen
                exact ⟨authored, evaluated, captured, childValid⟩
        | true =>
            cases decoded : coefficientReadout interpretation score with
            | none =>
                simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                  gradedCoefficientSource, halted, decoded] at requested
            | some value =>
                cases parents with
                | nil =>
                    simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                      gradedCoefficientSource, halted, ↓reduceIte, decoded,
                      Sum.inr.injEq] at requested
                    subst alternatives
                    have same := List.mem_singleton.mp member
                    subst next
                    exact True.intro
                | cons parent rest =>
                    simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                      gradedCoefficientSource, halted, ↓reduceIte, decoded,
                      Sum.inr.injEq] at requested
                    subst alternatives
                    have same := List.mem_singleton.mp member
                    subst next
                    exact nested_capture_resumes program annotation body score parent rest
                      inherited halted

/-- The same capture obligations hold after declared filtering; the sublist
comparison transports surviving occurrences without replacing their worlds. -/
theorem native_nested_admitted_valid {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (admit : V → Bool) (fuel : Nat) (before : NestedWork)
    (valid : nestedValid program annotation before) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (nestedAdmittedSource program annotation interpretation admit) fuel before,
      Sum.elim (nestedResultValid program annotation) (nestedValid program annotation) leaf.1 := by
  intro leaf member
  apply native_nested_valid program annotation interpretation fuel before valid leaf
  exact (native_nested_admitted_occurrences_sublist program annotation interpretation
    admit fuel before).subset member

/-- This metric counts actual Need instructions, including those executed
inside grades. Suspended parents remain in the account. Administrative
coefficient returns are not Need instructions; runtime event costs and
cost-observation charges have their separate declared profiles. -/
def nestedInstructionCount : NestedWork → Nat :=
  WeightedBranchingResumption.nestedStateMeter
    (fun body : WorkState => body.state.work.transitions)
    (fun score : Score => score.machine.work.transitions)

/-- This observation forgets the worlds and coefficients, but retains the
instruction account of every owned frame. Construct it only when requested. -/
def nestedInstructionAccounts : NestedWork → List Nat :=
  WeightedBranchingResumption.nestedStateAccounts
    (fun body : WorkState => body.state.work.transitions)
    (fun score : Score => score.machine.work.transitions)

theorem nested_instruction_accounts_sum (pending : NestedWork) :
    (nestedInstructionAccounts pending).sum = nestedInstructionCount pending :=
  WeightedBranchingResumption.nested_state_accounts_sum _ _ pending

def nestedResultInstructionCount : NestedResult → Nat :=
  WeightedBranchingResumption.nestedAnswerMeter
    (fun body : WorkState => body.state.work.transitions)
    (fun body : WorkState => body.state.work.transitions)
    (fun score : Score => score.machine.work.transitions)
    (fun score : Score => score.machine.work.transitions)

/-- A finite weighted budget bounds actual instruction expenditure across
all owned frames. Returning a child transfers its work once; suspending or
resuming the computation never resets the cumulative instruction meter. -/
theorem native_nested_instruction_bounds {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : NestedWork) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (nestedSource program annotation interpretation) fuel before,
      nestedInstructionCount before ≤
        Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1 ∧
      Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1 ≤
        nestedInstructionCount before + fuel := by
  unfold nestedSource nestedInstructionCount nestedResultInstructionCount
  apply WeightedBranchingResumption.nested_contributions_meter_bounds
    (NeedWeightedResumption.source (specification program) (coefficientJob annotation))
    (gradedCoefficientSource program annotation) (coefficientReadout interpretation)
    resumeCoefficient resumeCoefficientScore
    (fun body : WorkState => body.state.work.transitions)
    (fun body : WorkState => body.state.work.transitions)
    (fun score : Score => score.machine.work.transitions)
    (fun score : Score => score.machine.work.transitions)
    ?_ ?_ ?_ ?_ ?_ ?_ fuel before
  · intro body answer returned
    obtain ⟨rfl, _⟩ := (NeedWeightedResumption.source_return_iff
      (specification program) (coefficientJob annotation) body answer).mp returned
    rfl
  · intro body alternatives requested next member
    rcases next with ⟨child, coefficient⟩
    have located : (child, coefficient) ∈ NeedWeightedResumption.successors
        (specification program) (coefficientJob annotation) body := by
      cases control : body.state.control <;>
        simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr, Sum.inr.injEq]
    obtain ⟨_, actual, _, caused⟩ := (NeedWeightedResumption.successor_iff
      (specification program) (coefficientJob annotation) body child coefficient).mp located
    refine ⟨step_increments_transition (specification program) _ _
      (List.mem_of_getElem? actual), ?_⟩
    cases coefficient with
    | inl value => exact True.intro
    | inr score =>
        exact coefficient_job_starts_at_zero (V := V) annotation body.state child.state
          score caused.symm
  · intro score result returned
    cases halted : isHalted score.machine with
    | false => simp [gradedCoefficientSource, halted] at returned
    | true =>
        simp only [gradedCoefficientSource, halted, ↓reduceIte, Sum.inl.injEq] at returned
        subst result
        rfl
  · intro score alternatives requested next member
    cases halted : isHalted score.machine with
    | true => simp [gradedCoefficientSource, halted] at requested
    | false =>
        simp only [gradedCoefficientSource, halted, Bool.false_eq_true, ↓reduceIte,
          Sum.inr.injEq] at requested
        subst alternatives
        obtain ⟨child, actual, rfl⟩ := List.mem_map.mp member
        refine ⟨(score_step_origin program score child actual).2.2, ?_⟩
        cases chosen : coefficientJob (V := V) annotation score.machine child.machine with
        | inl value => exact True.intro
        | inr inner =>
            exact coefficient_job_starts_at_zero (V := V) annotation score.machine
              child.machine inner chosen
  · intro body result
    rfl
  · intro parent result
    rfl

/-- Declared admission can remove a contribution, but cannot rewrite the
instruction account of a contribution that survives. -/
theorem native_nested_admitted_instruction_bounds {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (admit : V → Bool) (fuel : Nat) (before : NestedWork) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (nestedAdmittedSource program annotation interpretation admit) fuel before,
      nestedInstructionCount before ≤
        Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1 ∧
      Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1 ≤
        nestedInstructionCount before + fuel := by
  intro leaf member
  exact native_nested_instruction_bounds program annotation interpretation fuel before leaf
    ((native_nested_admitted_occurrences_sublist program annotation interpretation
      admit fuel before).subset member)

theorem native_pending_score_has_native_path {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before body : WorkState) (score : Score) (value : V)
    (member : (.inr (.inr (body, score)), value) ∈ WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) fuel (.inl before)) :
    score.origin.body = body.state ∧
      ∃ count, Steps (specification program) count
        (score.origin.score score.expression).machine score.machine := by
  have valid := native_pending_valid program annotation interpretation fuel (.inl before)
    True.intro (.inr (.inr (body, score)), value) member
  change CapturedCoefficient program body score at valid
  exact ⟨valid.1, (score_generated_native program _ _ valid.2).2.2⟩

/-- An uninterpreted completed coefficient preserves the actual native
calculation, its capture and its result; it is not a fabricated weight. -/
theorem native_uninterpreted_score_has_native_path {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before body : WorkState) (score : Score) (value : V)
    (member : (.inl (.inr (body, score)), value) ∈ WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) fuel (.inl before)) :
    score.origin.body = body.state ∧ isHalted score.machine = true ∧
      ∃ count, Steps (specification program) count
        (score.origin.score score.expression).machine score.machine := by
  have valid := native_pending_valid program annotation interpretation fuel (.inl before)
    True.intro (.inl (.inr (body, score)), value) member
  change CapturedCoefficient program body score ∧ isHalted score.machine = true at valid
  exact ⟨valid.1.1, valid.2, (score_generated_native program _ _ valid.1.2).2.2⟩

/-- The original handler law also covers unfinished coefficient machines,
their result readout and their complete body continuation. -/
theorem native_pending_handler_agrees {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : PendingWork) :
    WeightedResumption.interpret WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (pendingSource program annotation interpretation) fuel before) =
      WeightedBranchingResumption.contributions
        (pendingSource program annotation interpretation) fuel before :=
  WeightedBranchingResumption.interpret_cut _ _ _

theorem native_pending_resume_exact {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (first second : Nat) (before : PendingWork) :
    WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions
          (pendingSource program annotation interpretation) first before)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : V))]
          | .inr pending => WeightedBranchingResumption.contributions
              (pendingSource program annotation interpretation) second pending) :=
  by
    rw [WeightedBranchingResumption.contributions_add]
    apply congrArg (WeightedResumption.sequence
      (WeightedBranchingResumption.contributions
        (pendingSource program annotation interpretation) first before))
    funext leaf
    cases leaf <;> rfl

/-- A completed body answer is actually halted. Coefficient results outside
the declared algebra have their own result constructor and do not certify it. -/
theorem native_pending_returned_is_halted {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : PendingWork) (after : WorkState) (value : V)
    (member : (.inl (.inl after), value) ∈ WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) fuel before) :
    isHalted after.state = true := by
  have valid := WeightedBranchingResumption.pending_contributions_invariant
    (NeedWeightedResumption.source (specification program) (coefficientJob annotation))
    (coefficientSource program) (coefficientReadout interpretation) resumeCoefficient
    (fun _ => True) (fun done => isHalted done.state = true)
    (fun state answer _ returned => by
      obtain ⟨rfl, halted⟩ := (NeedWeightedResumption.source_return_iff (specification program)
        (coefficientJob annotation) state answer).mp returned
      exact halted)
    (fun _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro) fuel before True.intro
    (.inl (.inl after), value) member
  exact valid

/-- Admission retains the same whole-state split law, including coefficient
jobs and rejected alternatives. It does not reset a suspended score's world. -/
theorem native_admitted_resume_exact {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (first second : Nat) (before : PendingWork) :
    WeightedBranchingResumption.contributions
      (pendingAdmittedSource program annotation interpretation admit) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions
          (pendingAdmittedSource program annotation interpretation admit) first before)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : V))]
          | .inr pending => WeightedBranchingResumption.contributions
              (pendingAdmittedSource program annotation interpretation admit) second pending) :=
  by
    rw [WeightedBranchingResumption.contributions_add]
    apply congrArg (WeightedResumption.sequence
      (WeightedBranchingResumption.contributions
        (pendingAdmittedSource program annotation interpretation admit) first before))
    funext leaf
    cases leaf <;> rfl

theorem native_admitted_returned_is_halted {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : PendingWork) (after : WorkState) (value : V)
    (member : (.inl (.inl after), value) ∈ WeightedBranchingResumption.contributions
      (pendingAdmittedSource program annotation interpretation admit) fuel before) :
    isHalted after.state = true :=
  native_pending_returned_is_halted program annotation interpretation fuel before after value
    ((native_admitted_occurrences_sublist program annotation interpretation admit fuel before).subset
      member)

end PendingCoefficients

section AuthoredPredicates

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- A binding-local coefficient and an optional predicate applied to its
returned value. The predicate is a native computation, not a Boolean oracle. -/
structure AuthoredClause where
  coefficient : Atom
  predicate : Option Atom := none

/-- The predicate phase retains the completed coefficient computation.
Its factor is attached only after the predicate returns true. -/
inductive AuthoredPhase where
  | coefficient
  | predicate (completedCoefficient : Score)

structure AuthoredJob where
  score : Score
  predicate : Option Atom
  phase : AuthoredPhase := .coefficient

def authoredJob {V : Type} [One V] (annotation : Row → Option AuthoredClause)
    (before after : NativeMachine) : V ⊕ AuthoredJob :=
  match NativeGradeAttachment.captureNext before after with
  | none => .inl 1
  | some capture =>
      match annotation capture.row with
      | none => .inl 1
      | some clause =>
          .inr ⟨capture.score clause.coefficient, clause.predicate, .coefficient⟩

/-- Only the two declared Boolean returns decide admission. -/
def predicateVerdict (score : Score) : Option Bool :=
  match scoreResult score with
  | some (.value (.symbol "True")) => some true
  | some (.value (.symbol "False")) => some false
  | _ => none

/-- Start the predicate in the coefficient's completed world, with the same
captured cells. Its instruction count includes the work already performed. -/
def beginPredicate (job : AuthoredJob) (predicate value : Atom) : AuthoredJob :=
  let expression := Atom.expression [predicate, value]
  { job with
    score := { job.score with
      expression := expression
      machine := { job.score.machine with
        control := .run (.evaluate expression job.score.origin.row.environment) [] } }
    phase := .predicate job.score }

/-- Both phases use actual Need steps. Equation annotations encountered in
either computation suspend the same owned parent stack. -/
def authoredGradeSource {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) :
    WeightedBranchingResumption.Coalgebra AuthoredJob AuthoredJob (V ⊕ AuthoredJob) :=
  fun job => if isHalted job.score.machine then
    match job.phase with
    | .coefficient =>
        match job.predicate, scoreResult job.score with
        | some predicate, some (.value value) =>
            .inr [(beginPredicate job predicate value, .inl 1)]
        | _, _ => .inl job
    | .predicate _ =>
        match predicateVerdict job.score with
        | some false => .inr []
        | _ => .inl job
  else
    .inr ((scoreStep program job.score).map fun next =>
      ({ job with score := next }, authoredJob annotation job.score.machine next.machine))

def authoredReadout {V : Type} (interpretation : Outcome → Option V)
    (job : AuthoredJob) : Option V :=
  match job.phase with
  | .coefficient =>
      match job.predicate with
      | none => coefficientReadout interpretation job.score
      | some _ => none
  | .predicate completed =>
      if predicateVerdict job.score = some true then coefficientReadout interpretation completed
      else none

def resumeAuthoredBody (body : WorkState) (job : AuthoredJob) : WorkState :=
  resumeCoefficient body job.score

def resumeAuthoredParent (parent child : AuthoredJob) : AuthoredJob :=
  { parent with score := resumeCoefficientScore parent.score child.score }

abbrev AuthoredWork :=
  WeightedBranchingResumption.NestedPendingState WorkState AuthoredJob

abbrev AuthoredResult :=
  WeightedBranchingResumption.NestedPendingAnswer WorkState WorkState AuthoredJob AuthoredJob

/-- Authored predicates instantiate the existing nested coefficient handler.
No body executes between the coefficient return and its admission decision. -/
def authoredSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    WeightedBranchingResumption.Coalgebra AuthoredWork AuthoredResult V :=
  WeightedBranchingResumption.nestedPendingSource
    (NeedWeightedResumption.source (specification program) (authoredJob annotation))
    (authoredGradeSource program annotation) (authoredReadout interpretation)
    resumeAuthoredBody resumeAuthoredParent

/-- Every factor of the actual nested native source is either the unit or
an interpreted coefficient result. This includes coefficients produced while
executing another coefficient or its admission predicate. A scanner must
cover these results before using the corresponding factor law. -/
theorem authored_coefficients_satisfy {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (holds : V → Prop) (unit : holds 1)
    (interpreted : ∀ outcome value, interpretation outcome = some value → holds value) :
    WeightedBranchingResumption.CoefficientsSatisfy
      (authoredSource program annotation interpretation) holds := by
  have jobLaw : ∀ before after,
      Sum.elim holds (fun _ => True) (authoredJob annotation before after) := by
    intro before after
    cases captured : NativeGradeAttachment.captureNext before after with
    | none => simpa [authoredJob, captured] using unit
    | some capture =>
        cases annotated : annotation capture.row <;> simp [authoredJob, captured, annotated, unit]
  have readoutLaw : ∀ score value, coefficientReadout interpretation score = some value →
      holds value := by
    intro score value decoded
    simp only [coefficientReadout, Option.bind_eq_some_iff] at decoded
    obtain ⟨outcome, _, returned⟩ := decoded
    exact interpreted outcome value returned
  apply WeightedBranchingResumption.nested_coefficients_satisfy
    (holds := holds) (unit := unit)
  · exact NeedWeightedResumption.source_coefficients_satisfy
      (specification program) (authoredJob annotation) _ (fun before after _ => jobLaw before after)
  · intro job alternatives inspected next member
    unfold authoredGradeSource at inspected
    split at inspected
    · split at inspected
      · split at inspected
        · simp only [Sum.inr.injEq] at inspected
          subst alternatives
          obtain rfl := List.mem_singleton.mp member
          exact unit
        · cases inspected
      · split at inspected
        · cases inspected
          cases member
        · cases inspected
    · simp only [Sum.inr.injEq] at inspected
      subst alternatives
      obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp member
      exact jobLaw job.score.machine candidate.machine
  · intro job value decoded
    unfold authoredReadout at decoded
    split at decoded
    · split at decoded
      · exact readoutLaw _ value decoded
      · cases decoded
    · split at decoded
      · exact readoutLaw _ value decoded
      · cases decoded

@[simp] theorem authored_job_unannotated {V : Type} [One V]
    (before after : NativeMachine) :
    authoredJob (V := V) (fun _ => none) before after = .inl 1 := by
  cases inspected : NativeGradeAttachment.captureNext before after <;>
    simp [authoredJob, inspected]

theorem authored_unannotated_body_is_settled {V : Type} [One V] (program : Program) :
    NeedWeightedResumption.source (specification program)
      (authoredJob (V := V) (fun _ => none)) =
    WeightedBranchingResumption.settledBody
      (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V))) := by
  funext state
  cases control : state.state.control <;>
    simp only [NeedWeightedResumption.source, control,
      WeightedBranchingResumption.settledBody, NeedWeightedResumption.successors,
      List.map_map, authored_job_unannotated] <;> rfl

/-- The predicate extension creates no job or extra instruction for a plain
program. All ordered contributions and residual worlds agree at the same cut. -/
theorem native_authored_unannotated_exact {V : Type} [Monoid V] (program : Program)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (authoredSource program (fun _ => none) interpretation) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (Sum.map Sum.inl Sum.inl leaf.1, leaf.2)) := by
  unfold authoredSource
  rw [authored_unannotated_body_is_settled]
  exact WeightedBranchingResumption.nested_pending_settled_agrees _ _ _ _ _ _ _

theorem predicate_starts_in_completed_world (job : AuthoredJob) (predicate value : Atom) :
    (beginPredicate job predicate value).score.origin = job.score.origin ∧
    (beginPredicate job predicate value).score.machine.world = job.score.machine.world ∧
    (beginPredicate job predicate value).score.machine.work = job.score.machine.work ∧
    (beginPredicate job predicate value).score.machine.control =
      .run (.evaluate (.expression [predicate, value]) job.score.origin.row.environment) [] ∧
    (beginPredicate job predicate value).phase = .predicate job.score :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The completed coefficient is retained, rather than attached before the
predicate's own derivation factors or used to execute the body early. -/
theorem native_authored_starts_predicate {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job : AuthoredJob) (parents : List AuthoredJob)
    (predicate value : Atom) (halted : isHalted job.score.machine = true)
    (phase : job.phase = .coefficient) (declared : job.predicate = some predicate)
    (returned : scoreResult job.score = some (.value value)) :
    authoredSource program annotation interpretation (.inr (body, job, parents)) =
      .inr [(.inr (body, beginPredicate job predicate value, parents), 1)] := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, halted, phase, declared, returned]

theorem native_authored_false_refuses {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job : AuthoredJob) (parents : List AuthoredJob) (completed : Score)
    (halted : isHalted job.score.machine = true)
    (phase : job.phase = .predicate completed)
    (refused : predicateVerdict job.score = some false) :
    authoredSource program annotation interpretation (.inr (body, job, parents)) =
      .inr [] := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, halted, phase, refused]

theorem native_authored_unknown_retains_stack {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job : AuthoredJob) (parents : List AuthoredJob) (completed : Score)
    (halted : isHalted job.score.machine = true)
    (phase : job.phase = .predicate completed)
    (unknown : predicateVerdict job.score = none) :
    authoredSource program annotation interpretation (.inr (body, job, parents)) =
      .inl (.inr (body, job, parents)) := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, authoredReadout, halted, phase, unknown]

theorem native_authored_true_resumes_body {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job : AuthoredJob) (completed : Score) (value : V)
    (halted : isHalted job.score.machine = true)
    (phase : job.phase = .predicate completed)
    (admitted : predicateVerdict job.score = some true)
    (decoded : coefficientReadout interpretation completed = some value) :
    authoredSource program annotation interpretation (.inr (body, job, [])) =
      .inr [(.inl (resumeAuthoredBody body job), value)] := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, authoredReadout, halted, phase, admitted, decoded]

theorem native_authored_true_resumes_parent {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job parent : AuthoredJob) (parents : List AuthoredJob)
    (completed : Score) (value : V) (halted : isHalted job.score.machine = true)
    (phase : job.phase = .predicate completed)
    (admitted : predicateVerdict job.score = some true)
    (decoded : coefficientReadout interpretation completed = some value) :
    authoredSource program annotation interpretation (.inr (body, job, parent :: parents)) =
      .inr [(.inr (body, resumeAuthoredParent parent job, parents), value)] := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, authoredReadout, halted, phase, admitted, decoded]

theorem authored_resume_preserves_parent (parent child : AuthoredJob) :
    (resumeAuthoredParent parent child).phase = parent.phase ∧
    (resumeAuthoredParent parent child).predicate = parent.predicate ∧
    (resumeAuthoredParent parent child).score.origin = parent.score.origin ∧
    (resumeAuthoredParent parent child).score.expression = parent.score.expression ∧
    (resumeAuthoredParent parent child).score.machine.control = parent.score.machine.control ∧
    (resumeAuthoredParent parent child).score.machine.world = child.score.machine.world ∧
    (resumeAuthoredParent parent child).score.machine.work =
      parent.score.machine.work.add child.score.machine.work :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Running a predicate or coefficient performs an actual reference-machine
instruction. The completed coefficient retained by its phase stays fixed. -/
theorem authored_running_uses_need {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job next : AuthoredJob)
    (edge : V ⊕ AuthoredJob) (running : isHalted job.score.machine = false)
    (member : (next, edge) ∈ (scoreStep program job.score).map (fun score =>
      ({ job with score := score }, authoredJob annotation job.score.machine score.machine))) :
    authoredGradeSource (V := V) program annotation job =
      .inr ((scoreStep program job.score).map fun score =>
        ({ job with score := score }, authoredJob annotation job.score.machine score.machine)) ∧
    next.score.machine ∈ NeedReference.step (specification program) job.score.machine ∧
    next.phase = job.phase ∧ next.predicate = job.predicate ∧
    next.score.origin = job.score.origin ∧ next.score.expression = job.score.expression ∧
    next.score.machine.work.transitions = job.score.machine.work.transitions + 1 := by
  obtain ⟨score, stepped, same⟩ := List.mem_map.mp member
  have nextEqual : { job with score := score } = next := (Prod.mk.inj same).1
  subst next
  obtain ⟨machine, actual, changed⟩ := (score_step_iff program job.score score).mp stepped
  obtain ⟨origin, expression, work⟩ := score_step_origin program job.score score stepped
  refine ⟨by simp [authoredGradeSource, running], ?_, rfl, rfl, origin, expression, work⟩
  simpa only [changed] using actual

/-- The native phased adapter has the same independently executed weighted
frontier interpretation as the common free handler. -/
theorem native_authored_handler_agrees {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : AuthoredWork) :
    WeightedResumption.interpret WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (authoredSource program annotation interpretation)
        fuel before) =
      WeightedBranchingResumption.contributions
        (authoredSource program annotation interpretation) fuel before :=
  WeightedBranchingResumption.interpret_cut _ _ _

/-- Split execution retains the predicate phase, its completed coefficient,
all suspended parents and the full ordered contribution product. -/
theorem native_authored_resume_exact {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (first second : Nat) (before : AuthoredWork) :
    WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions
          (authoredSource program annotation interpretation) first before)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : V))]
          | .inr pending => WeightedBranchingResumption.contributions
              (authoredSource program annotation interpretation) second pending) := by
  rw [WeightedBranchingResumption.contributions_add]
  apply congrArg (WeightedResumption.sequence
    (WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) first before))
  funext leaf
  cases leaf <;> rfl

end AuthoredPredicates

section AuthoredInstructionAccount

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem authored_job_capture {V : Type} [One V]
    (annotation : Row → Option AuthoredClause) (before after : NativeMachine)
    (job : AuthoredJob)
    (chosen : authoredJob (V := V) annotation before after = .inr job) :
    ∃ capture clause,
      NativeGradeAttachment.captureNext before after = some capture ∧
      annotation capture.row = some clause ∧
      job = ⟨capture.score clause.coefficient, clause.predicate, .coefficient⟩ := by
  cases captured : NativeGradeAttachment.captureNext before after with
  | none => simp [authoredJob, captured] at chosen
  | some capture =>
      cases authored : annotation capture.row with
      | none => simp [authoredJob, captured, authored] at chosen
      | some clause =>
          simp only [authoredJob, captured, authored, Sum.inr.injEq] at chosen
          exact ⟨capture, clause, rfl, authored, chosen.symm⟩

theorem authored_job_starts_at_zero {V : Type} [One V]
    (annotation : Row → Option AuthoredClause) (before after : NativeMachine)
    (job : AuthoredJob)
    (chosen : authoredJob (V := V) annotation before after = .inr job) :
    job.score.machine.work.transitions = 0 := by
  obtain ⟨_, _, _, _, rfl⟩ := authored_job_capture annotation before after job chosen
  rfl

theorem authored_job_owns_actual_body {V : Type} [One V]
    (annotation : Row → Option AuthoredClause) (before after : NativeMachine)
    (job : AuthoredJob)
    (chosen : authoredJob (V := V) annotation before after = .inr job) :
    job.score.origin.body = after := by
  obtain ⟨capture, _, captured, _, rfl⟩ :=
    authored_job_capture annotation before after job chosen
  exact (NativeGradeAttachment.captured_next_exact before after capture captured).1

theorem authored_grade_return_same_job {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job result : AuthoredJob)
    (returned : authoredGradeSource (V := V) program annotation job = .inl result) :
    result = job := by
  unfold authoredGradeSource at returned
  split at returned
  · split at returned
    · split at returned <;> simp_all
    · split at returned <;> simp_all
  · simp at returned

/-- The actual Need instruction account of one retained contribution.
It is distinct from cumulative whole-search or runtime-event receipts. -/
def authoredInstructionCount : AuthoredWork → Nat :=
  WeightedBranchingResumption.nestedStateMeter
    (fun body : WorkState => body.state.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)

def authoredResultInstructionCount : AuthoredResult → Nat :=
  WeightedBranchingResumption.nestedAnswerMeter
    (fun body : WorkState => body.state.work.transitions)
    (fun body : WorkState => body.state.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)

/-- Read the owned accounts only when requested. The completed coefficient
retained by a predicate phase is not a second active work account. -/
def authoredInstructionAccounts : AuthoredWork → List Nat :=
  WeightedBranchingResumption.nestedStateAccounts
    (fun body : WorkState => body.state.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)

theorem authored_instruction_accounts_sum (pending : AuthoredWork) :
    (authoredInstructionAccounts pending).sum = authoredInstructionCount pending :=
  WeightedBranchingResumption.nested_state_accounts_sum _ _ pending

theorem authored_predicate_phase_adds_no_instruction (body : WorkState) (job : AuthoredJob)
    (parents : List AuthoredJob) (predicate value : Atom) :
    authoredInstructionCount (.inr (body, beginPredicate job predicate value, parents)) =
      authoredInstructionCount (.inr (body, job, parents)) := rfl

theorem authored_grade_return_keeps_account {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job result : AuthoredJob)
    (returned : authoredGradeSource (V := V) program annotation job = .inl result) :
    result.score.machine.work.transitions = job.score.machine.work.transitions :=
  congrArg (fun held : AuthoredJob => held.score.machine.work.transitions)
    (authored_grade_return_same_job program annotation job result returned)

theorem authored_grade_step_bounds {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job : AuthoredJob)
    (alternatives : List (AuthoredJob × (V ⊕ AuthoredJob)))
    (requested : authoredGradeSource program annotation job = .inr alternatives)
    (next : AuthoredJob × (V ⊕ AuthoredJob)) (member : next ∈ alternatives) :
    job.score.machine.work.transitions ≤ next.1.score.machine.work.transitions ∧
    next.1.score.machine.work.transitions ≤ job.score.machine.work.transitions + 1 ∧
    Sum.elim (fun _ => True) (fun child => child.score.machine.work.transitions = 0)
      next.2 := by
  unfold authoredGradeSource at requested
  split at requested
  · split at requested
    · split at requested
      · simp only [Sum.inr.injEq] at requested
        subst alternatives
        obtain rfl := List.mem_singleton.mp member
        simp [beginPredicate]
      · simp at requested
    · split at requested <;> simp_all
  · simp only [Sum.inr.injEq] at requested
    subst alternatives
    obtain ⟨score, actual, rfl⟩ := List.mem_map.mp member
    have spent := (score_step_origin program job.score score actual).2.2
    refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
    cases chosen : authoredJob (V := V) annotation job.score.machine score.machine with
    | inl value => trivial
    | inr inner =>
        exact authored_job_starts_at_zero (V := V) annotation job.score.machine
          score.machine inner chosen

/-- Every retained or returned contribution accounts for its coefficient,
predicate and suspended parents once. Phase changes may be administrative;
actual instructions never decrease and are bounded by the source allowance. -/
theorem native_authored_instruction_bounds {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : AuthoredWork) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel before,
      authoredInstructionCount before ≤
        Sum.elim authoredResultInstructionCount authoredInstructionCount leaf.1 ∧
      Sum.elim authoredResultInstructionCount authoredInstructionCount leaf.1 ≤
        authoredInstructionCount before + fuel := by
  unfold authoredSource authoredInstructionCount authoredResultInstructionCount
  apply WeightedBranchingResumption.nested_contributions_meter_bounds_le
    (NeedWeightedResumption.source (specification program) (authoredJob annotation))
    (authoredGradeSource program annotation) (authoredReadout interpretation)
    resumeAuthoredBody resumeAuthoredParent
    (fun body : WorkState => body.state.work.transitions)
    (fun body : WorkState => body.state.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)
    ?_ ?_ ?_ ?_ ?_ ?_ fuel before
  · intro body answer returned
    obtain ⟨rfl, _⟩ := (NeedWeightedResumption.source_return_iff
      (specification program) (authoredJob annotation) body answer).mp returned
    rfl
  · intro body alternatives requested next member
    rcases next with ⟨child, coefficient⟩
    have located : (child, coefficient) ∈ NeedWeightedResumption.successors
        (specification program) (authoredJob annotation) body := by
      cases control : body.state.control <;>
        simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr, Sum.inr.injEq]
    obtain ⟨_, actual, _, caused⟩ := (NeedWeightedResumption.successor_iff
      (specification program) (authoredJob annotation) body child coefficient).mp located
    have spent : child.state.work.transitions = body.state.work.transitions + 1 :=
      step_increments_transition (specification program) _ _ (List.mem_of_getElem? actual)
    refine ⟨?_, spent.le, ?_⟩
    · change body.state.work.transitions ≤ child.state.work.transitions
      omega
    cases coefficient with
    | inl value => trivial
    | inr job =>
        exact authored_job_starts_at_zero (V := V) annotation body.state child.state
          job caused.symm
  · exact authored_grade_return_keeps_account program annotation
  · exact authored_grade_step_bounds program annotation
  · intro body result
    rfl
  · intro parent result
    rfl

end AuthoredInstructionAccount

section AuthoredCallerAgreement

/-- Every child captures the actual suspended caller, including its complete
world and control. This view does not identify or merge occurrences. -/
def authoredCallerAgreement : AuthoredWork → Prop :=
  WeightedBranchingResumption.nestedWorkCallerAgreement
    (fun body : WorkState => body.state)
    (fun job : AuthoredJob => job.score.machine)
    (fun job : AuthoredJob => job.score.origin.body)

def authoredResultCallerAgreement : AuthoredResult → Prop :=
  WeightedBranchingResumption.nestedResultCallerAgreement
    (fun body : WorkState => body.state)
    (fun job : AuthoredJob => job.score.machine)
    (fun job : AuthoredJob => job.score.origin.body)

theorem authored_grade_steps_keep_caller {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job : AuthoredJob)
    (alternatives : List (AuthoredJob × (V ⊕ AuthoredJob)))
    (requested : authoredGradeSource program annotation job = .inr alternatives)
    (next : AuthoredJob × (V ⊕ AuthoredJob)) (member : next ∈ alternatives) :
    next.1.score.origin.body = job.score.origin.body ∧
    Sum.elim (fun _ => True)
      (fun child => child.score.origin.body = next.1.score.machine) next.2 := by
  unfold authoredGradeSource at requested
  split at requested
  · split at requested
    · split at requested
      · simp only [Sum.inr.injEq] at requested
        subst alternatives
        obtain rfl := List.mem_singleton.mp member
        simp [beginPredicate]
      · simp at requested
    · split at requested <;> simp_all
  · simp only [Sum.inr.injEq] at requested
    subst alternatives
    obtain ⟨score, actual, rfl⟩ := List.mem_map.mp member
    refine ⟨congrArg Captured.body (score_step_origin program job.score score actual).1, ?_⟩
    cases chosen : authoredJob (V := V) annotation job.score.machine score.machine with
    | inl value => trivial
    | inr inner =>
        exact authored_job_owns_actual_body (V := V) annotation job.score.machine
          score.machine inner chosen

/-- The actual authored adapter preserves caller agreement through phase
changes, nested Need instructions and child returns. Unknown readouts retain
it in the parked result; no normalization or successful readout is assumed. -/
theorem native_authored_caller_agreement {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : AuthoredWork)
    (valid : authoredCallerAgreement before) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel before,
      Sum.elim authoredResultCallerAgreement authoredCallerAgreement leaf.1 := by
  unfold authoredSource authoredCallerAgreement authoredResultCallerAgreement at *
  apply WeightedBranchingResumption.nested_contributions_caller_agreement
    (NeedWeightedResumption.source (specification program) (authoredJob annotation))
    (authoredGradeSource program annotation) (authoredReadout interpretation)
    resumeAuthoredBody resumeAuthoredParent
    (fun body : WorkState => body.state)
    (fun job : AuthoredJob => job.score.machine)
    (fun job : AuthoredJob => job.score.origin.body)
    ?_ ?_ ?_ ?_ fuel before valid
  · intro body alternatives requested next member job chosen
    rcases next with ⟨child, coefficient⟩
    have located : (child, coefficient) ∈ NeedWeightedResumption.successors
        (specification program) (authoredJob annotation) body := by
      cases control : body.state.control <;>
        simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr, Sum.inr.injEq]
    obtain ⟨_, _, _, caused⟩ := (NeedWeightedResumption.successor_iff
      (specification program) (authoredJob annotation) body child coefficient).mp located
    exact authored_job_owns_actual_body (V := V) annotation body.state child.state job
      (caused.symm.trans chosen)
  · intro job result returned
    exact congrArg (fun held : AuthoredJob => held.score.origin.body)
      (authored_grade_return_same_job program annotation job result returned)
  · exact authored_grade_steps_keep_caller program annotation
  · intro parent result
    rfl

theorem native_authored_root_caller_agreement {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (body : WorkState) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel (.inl body),
      Sum.elim authoredResultCallerAgreement authoredCallerAgreement leaf.1 :=
  native_authored_caller_agreement program annotation interpretation fuel (.inl body) True.intro

end AuthoredCallerAgreement

/-! ## Stateful agendas and recordings of authored coefficient computations -/

section ScheduledAuthored

open Mettapedia.GSLT.Core.BranchingTemporal

/-- The common scheduler executes the actual nested coefficient and predicate
source. Parked results retain their distinct `AuthoredResult` tag; an emitted
parked disposition is not a successful body answer. -/
def authoredSystem {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    BranchingSystem (AuthoredWork × V) (AuthoredResult × V) :=
  WeightedBranchingResumption.Scheduled.system (authoredSource program annotation interpretation)

/-- Actual nested coefficient and predicate computations use the common finite
source certificate. Completed controllers retain the entire result bag,
including parked dispositions and duplicate occurrences. No termination claim
about other programs, equality of prefixes, or equality of host costs follows. -/
theorem authored_completed_controllers_agree {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (depth : Nat)
    {FirstMemory SecondMemory : Type*}
    (first : Controller (AuthoredWork × V) (AuthoredResult × V) FirstMemory)
    (second : Controller (AuthoredWork × V) (AuthoredResult × V) SecondMemory)
    (roots : List (AuthoredWork × V))
    (certified : ∀ root ∈ roots, Mettapedia.GSLT.Core.FiniteSearchCertificate.Certified
      (authoredSystem program annotation interpretation) depth root)
    (firstFuel secondFuel : Nat)
    (firstClosed : (Snapshot.run (authoredSystem program annotation interpretation)
      first firstFuel (Snapshot.initial first roots)).search.frontier = [])
    (secondClosed : (Snapshot.run (authoredSystem program annotation interpretation)
      second secondFuel (Snapshot.initial second roots)).search.frontier = []) :
    eventBag (Snapshot.run (authoredSystem program annotation interpretation)
        first firstFuel (Snapshot.initial first roots)).search.events =
      eventBag (Snapshot.run (authoredSystem program annotation interpretation)
        second secondFuel (Snapshot.initial second roots)).search.events :=
  Mettapedia.GSLT.Core.FiniteSearchCertificate.completed_controllers_agree
    (authoredSystem program annotation interpretation) depth first second roots certified
    firstFuel secondFuel firstClosed secondClosed

/-- A superior multiplication supplies one sufficient stopping law for the
actual nested coefficient/predicate machine. The source continues to retain
zero, duplicate and uninterpreted occurrences. -/
theorem authored_coefficient_realized {V : Type} [Monoid V] [Preorder V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V)
    (superior : Mettapedia.GSLT.Core.WeightOrderedSelection.Superior V)
    (combines : ∀ left right, superior.combine left right = left * right) :
    Mettapedia.GSLT.Core.WeightOrderedSelection.Realized
      (authoredSystem program annotation interpretation) superior Prod.snd :=
  WeightedBranchingResumption.Scheduled.system_realized
    (authoredSource program annotation interpretation) superior combines

/-- The actual nested native machine supports descending product bounds on
all nonnegative carried values. Only factors produced by the interpretation
must be at most one; the starting coefficient has no upper bound. -/
theorem authored_product_step_bound {R : Type} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option R)
    (factors : ∀ outcome value, interpretation outcome = some value →
      0 ≤ value ∧ value ≤ 1) :
    Mettapedia.GSLT.Core.WeightOrderedSelection.StepBound
      (authoredSystem program annotation interpretation)
      (fun node => OrderDual.toDual node.2) (fun node => 0 ≤ node.2) :=
  WeightedBranchingResumption.Scheduled.product_stepBound _
    (authored_coefficients_satisfy program annotation interpretation _
      ⟨zero_le_one, le_rfl⟩ factors)

/-- A stateful native agenda may certify a selected batch against its full
residual using a one-sided law on a preserved coefficient domain. The
captured source/interpretation are fixed; both the runnable frontier and
retained unaccepted results need bounds. This does not provide a missing
interpretation for a parked coefficient or a requested batch size. -/
theorem authored_early_stop_selects_best {V W : Type} [Monoid V] [Preorder W]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V)
    (weight : V → W) (domain : V → Prop)
    (law : Mettapedia.GSLT.Core.WeightOrderedSelection.StepBound
      (authoredSystem program annotation interpretation)
      (fun node => weight node.2) (fun node => domain node.2))
    {Memory : Type*}
    (controller : Controller (AuthoredWork × V) (AuthoredResult × V) Memory)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (AuthoredWork × V) (AuthoredResult × V) Memory) (fuel : Nat)
    (frontierDomain : ∀ item ∈
      (Snapshot.run (authoredSystem program annotation interpretation)
        controller fuel snapshot).search.frontier, domain item.2) {bound : W}
    (accepted : Emission (AuthoredWork × V) (AuthoredResult × V) → Prop)
    (frontierBound : ∀ item ∈
      (Snapshot.run (authoredSystem program annotation interpretation)
        controller fuel snapshot).search.frontier, bound ≤ weight item.2)
    (retainedBound : ∀ event ∈
      (Snapshot.run (authoredSystem program annotation interpretation)
        controller fuel snapshot).search.events,
      ¬ accepted event → bound ≤ weight event.origin.2)
    {selections : List (AuthoredWork × V)}
    (selectedBound : ∀ chosen ∈ selections, weight chosen.2 ≤ bound)
    {node : AuthoredWork × V} {answer : AuthoredResult × V}
    (generated : Generated (authoredSystem program annotation interpretation)
      snapshot.search.frontier node)
    (emits : (authoredSystem program annotation interpretation).emit node = some answer)
    (unaccepted : ¬ accepted ⟨node, answer⟩) :
    ∀ chosen ∈ selections, weight chosen.2 ≤ weight node.2 :=
  Mettapedia.GSLT.Core.WeightOrderedSelection.Controlled.early_stop_selects_best
    (authoredSystem program annotation interpretation)
    (fun node => weight node.2) (fun node => domain node.2) law
    controller snapshot fuel frontierDomain accepted frontierBound retainedBound selectedBound
    generated emits unaccepted

/-- The actual native snapshot cannot establish answer shortage while a
coefficient/predicate result still owns a parked caller and parent stack. -/
theorem authored_saturation_iff {V Selected Memory : Type*}
    (select : WorkState → Option Selected) (requested : Nat)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (AuthoredWork × V) (AuthoredResult × V) Memory) :
    WeightedBranchingResumption.nestedSelectionOutcome select requested
      (WeightedBranchingResumption.Scheduled.observeSnapshot snapshot.search) = .saturated ↔
      (WeightedBranchingResumption.nestedSelected select
        (WeightedBranchingResumption.Scheduled.observeSnapshot snapshot.search)).length < requested ∧
      (snapshot.search.events.filterMap (fun event => match event.value.1 with
        | .inl _ => none
        | .inr parked => some (parked, event.value.2))) = [] ∧
      snapshot.search.frontier = [] := by
  convert WeightedBranchingResumption.Scheduled.nested_saturated_iff
    select requested snapshot.search using 1
  apply and_congr_right
  intro _
  apply and_congr_left
  intro _
  apply Iff.of_eq
  apply congrArg (fun values => values = [])
  apply congrArg (fun read => snapshot.search.events.filterMap read)
  funext event
  cases event.value.1 <;> rfl

/-- Arbitrary lawful agendas preserve the actual caller/world agreement in
every live instruction, nested parent frame and emitted parked result. The
proof passes through the independently defined weighted source cuts. -/
theorem native_authored_scheduled_callers {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (AuthoredWork × V) (AuthoredResult × V) Memory)
    (body : WorkState) (fuel : Nat) :
    let run := Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (authoredSystem program annotation interpretation) controller fuel
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller [(.inl body, 1)])
    (∀ node ∈ run.search.frontier, authoredCallerAgreement node.1) ∧
      (∀ event ∈ run.search.events, authoredResultCallerAgreement event.value.1) := by
  have sound := Mettapedia.GSLT.Core.InferenceControl.Snapshot.sound_run
    (authoredSystem program annotation interpretation) controller
    (snapshot := Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      controller [(.inl body, 1)])
    (initial_sound (authoredSystem program annotation interpretation) [(.inl body, 1)]) fuel
  constructor
  · intro node member
    obtain ⟨depth, present⟩ := WeightedBranchingResumption.Scheduled.generated_pending
      (authoredSource program annotation interpretation) (.inl body) (sound.1 node member)
    exact native_authored_root_caller_agreement program annotation interpretation
      depth body _ present
  · intro event member
    obtain ⟨depth, present⟩ := WeightedBranchingResumption.Scheduled.event_contribution
      (authoredSource program annotation interpretation) (.inl body) (sound.2 event member)
    exact native_authored_root_caller_agreement program annotation interpretation
      depth body _ present

/-- Enabling or truncating a recording preserves the complete weighted
snapshot, including coefficients, pending predicates and nested callers. -/
theorem authored_recording_erasure {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory Event : Type*}
    (controller : Controller (AuthoredWork × V) (AuthoredResult × V) Memory)
    (observe : Memory → (AuthoredWork × V) → Option (AuthoredResult × V) →
      List (AuthoredWork × V) → Event)
    (fuel : Nat)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (AuthoredWork × V) (AuthoredResult × V) (Memory × Option (Recording.Prefix Event))) :
    Recording.erase (Recording.runSelected
      (authoredSystem program annotation interpretation)
      controller observe fuel snapshot) =
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (authoredSystem program annotation interpretation) controller fuel
        (Recording.erase snapshot) :=
  Recording.runSelected_erasure _ _ _ _ _

/-- Retained graph nodes inherit the source's caller agreement even when the
recording omits later work. No completeness claim follows from this fact. -/
theorem recorded_authored_caller_agrees {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (AuthoredWork × V) (AuthoredResult × V) Memory)
    (body : WorkState) (capacity fuel : Nat)
    (record : Recording.Prefix (AuthoredWork × V))
    (retained : (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (authoredSystem program annotation interpretation)
      (Recording.controller controller (fun _ selected _ _ => selected) (some capacity)) fuel
      (Recording.start
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller [(.inl body, 1)])
        (some capacity))).memory.2 = some record)
    {node : AuthoredWork × V} (member : node ∈ record.items) :
    authoredCallerAgreement node.1 := by
  have generated := Recording.retained_node_generated
    (authoredSystem program annotation interpretation) controller capacity fuel
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller [(.inl body, 1)])
    [(.inl body, 1)] (initial_sound _ _) record retained member
  obtain ⟨depth, present⟩ := WeightedBranchingResumption.Scheduled.generated_pending
    (authoredSource program annotation interpretation) (.inl body) generated
  exact native_authored_root_caller_agreement program annotation interpretation
    depth body _ present

/-- Successor positions cover the complete authored source, including nested
coefficient and predicate phases. The inner Need receipt histories remain
part of the source states rather than being replaced by this decoration. -/
def authoredOccurrenceSystem {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    BranchingSystem (WorkOccurrence (AuthoredWork × V)) ((AuthoredResult × V) × List Nat) :=
  WorkOccurrence.system (WeightedBranchingResumption.Scheduled.pathMachine
    (authoredSource program annotation interpretation))

open Mettapedia.GSLT.Causality.OccurrenceMachineHistory

/-- With the source, coefficient interpretation and initial world fixed, a
retained occurrence replays to the same full nested state. Its coefficient
is the ordered account of actual selected source alternatives, including
zero factors. This does not authorize repeating external service effects. -/
theorem recorded_authored_weighted_history {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (AuthoredWork × V))
      ((AuthoredResult × V) × List Nat) Memory)
    (body : WorkState) (capacity fuel : Nat)
    (record : Recording.Prefix (WorkOccurrence (AuthoredWork × V)))
    (retained : (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (authoredOccurrenceSystem program annotation interpretation)
      (Recording.controller controller (fun _ selected _ _ => selected) (some capacity)) fuel
      (Recording.start
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller
          [WorkOccurrence.root (.inl body, 1)]) (some capacity))).memory.2 = some record)
    {node : WorkOccurrence (AuthoredWork × V)} (member : node ∈ record.items) :
    let source := authoredSource program annotation interpretation
    let machine := WeightedBranchingResumption.Scheduled.pathMachine source
    ∃ history : History machine (.inl body, 1) node.state,
      indices machine history = node.trace ∧
      node.state.2 = (eventAccount machine (fun before _ index =>
        WeightedBranchingResumption.Scheduled.edgeCoefficient source before.1 index)).of history := by
  let source := authoredSource program annotation interpretation
  let machine := WeightedBranchingResumption.Scheduled.pathMachine source
  have replayed := Recording.retained_occurrence_replays machine controller
    (.inl body, 1) capacity fuel record retained member
  let history := ofTrace machine node.trace replayed
  refine ⟨history, indices_ofTrace machine node.trace replayed, ?_⟩
  simpa only [one_mul] using
    WeightedBranchingResumption.Scheduled.history_coefficient source history

/-- Complete recorded expansions replay the actual nested native source,
including pending coefficient/predicate jobs and their captured callers.
The executable checker requires equality procedures for the retained states,
results and coefficient representation. This does not assert decidability for
arbitrary mathematical coefficients or authorize external-service replay. -/
theorem authored_recorded_replay {V : Type} [Monoid V] [DecidableEq V]
    [DecidableEq AuthoredWork] [DecidableEq AuthoredResult]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (AuthoredWork × V))
      ((AuthoredResult × V) × List Nat) Memory)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (WorkOccurrence (AuthoredWork × V)) ((AuthoredResult × V) × List Nat) Memory)
    (capacity fuel : Nat)
    (fits : (Recording.stream (authoredOccurrenceSystem program annotation interpretation)
      controller Recording.Replay.observe fuel snapshot).length ≤ capacity) :
    ((Recording.runSelected
      (authoredOccurrenceSystem program annotation interpretation)
      controller Recording.Replay.observe fuel
      (Recording.start snapshot (some capacity))).memory.2).bind
        (fun record => Recording.Replay.readout
          (authoredOccurrenceSystem program annotation interpretation) controller record snapshot) =
      some (.ok (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (authoredOccurrenceSystem program annotation interpretation) controller fuel snapshot)) :=
  Recording.Replay.selected_recorded_replay _ _ _ _ _ fits

/-- A rejected native replay preserves the full nested checkpoint and the
entire suffix. Its accepted prefix consists of actual source expansions. -/
theorem authored_replay_refusal {V : Type} [Monoid V] [DecidableEq V]
    [DecidableEq AuthoredWork] [DecidableEq AuthoredResult]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (AuthoredWork × V))
      ((AuthoredResult × V) × List Nat) Memory)
    (frames pending : List (Preparation.Capture (WorkOccurrence (AuthoredWork × V))
      ((AuthoredResult × V) × List Nat)))
    (snapshot cut : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (WorkOccurrence (AuthoredWork × V)) ((AuthoredResult × V) × List Nat) Memory)
    (refused : Recording.Replay.run (authoredOccurrenceSystem program annotation interpretation)
      controller frames snapshot = .error (cut, pending)) :
    ∃ acceptedFrames frame rest,
      frames = acceptedFrames ++ frame :: rest ∧ pending = frame :: rest ∧
      cut = Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (authoredOccurrenceSystem program annotation interpretation) controller
        acceptedFrames.length snapshot ∧
      Recording.Replay.step? (authoredOccurrenceSystem program annotation interpretation)
        controller cut frame = none :=
  Recording.Replay.run_refused _ _ _ _ _ _ refused

end ScheduledAuthored

/-! ## Lawful changes of native coefficients

The coefficient interpretation can change through a monoid homomorphism while
retaining the complete native states, owned grade jobs, caller frames, physical
contribution order and finite cut. The authored adapter also retains its
coefficient/predicate phase and the original predicate verdict.
-/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem coefficient_job_change {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (annotation : Row → Option Atom)
    (before after : NativeMachine) :
    coefficientJob (V := W) annotation before after =
      Sum.map change id (coefficientJob (V := V) annotation before after) := by
  cases capture : NativeGradeAttachment.captureNext before after with
  | none => simp [coefficientJob, capture]
  | some captured =>
      cases attached : annotation captured.row <;> simp [coefficientJob, capture, attached]

theorem coefficient_readout_change {V W : Type}
    (change : V → W) (interpretation : Outcome → Option V) (score : Score) :
    coefficientReadout (fun outcome => (interpretation outcome).map change) score =
      (coefficientReadout interpretation score).map change := by
  simp [coefficientReadout, Option.map_bind]

/-- Coefficient changes preserve the actual next native instruction, including
its captured body, score world and parent grade frames. -/
theorem native_nested_source_change_coefficients {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (pending : NestedWork) :
    nestedSource program annotation (fun outcome => (interpretation outcome).map change) pending =
      match nestedSource program annotation interpretation pending with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (WeightedResumption.mapCoefficients change alternatives) := by
  unfold nestedSource
  convert WeightedBranchingResumption.nested_pending_change_coefficients
    (State := WorkState) (Answer := WorkState) (Job := Score) (Grade := Score)
    change
    (NeedWeightedResumption.source (specification program) (coefficientJob (V := V) annotation))
    (NeedWeightedResumption.source (specification program) (coefficientJob (V := W) annotation))
    (gradedCoefficientSource (V := V) program annotation)
    (gradedCoefficientSource (V := W) program annotation) ?_ ?_
    (coefficientReadout interpretation)
    (coefficientReadout (fun outcome => (interpretation outcome).map change)) ?_
    resumeCoefficient resumeCoefficientScore pending using 1
  · cases inspected : WeightedBranchingResumption.nestedPendingSource
      (NeedWeightedResumption.source (specification program) (coefficientJob (V := V) annotation))
      (gradedCoefficientSource (V := V) program annotation) (coefficientReadout interpretation)
      resumeCoefficient resumeCoefficientScore pending <;> rfl
  · intro body
    cases control : body.state.control <;>
      simp [NeedWeightedResumption.source, NeedWeightedResumption.successors,
        control, List.map_map, coefficient_job_change change]
  · intro score
    by_cases halted : isHalted score.machine
    · simp [gradedCoefficientSource, halted]
    · simp [gradedCoefficientSource, halted, List.map_map, coefficient_job_change change]
  · exact coefficient_readout_change change interpretation

theorem native_nested_change_coefficients {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : NestedWork) :
    WeightedBranchingResumption.contributions
      (nestedSource program annotation (fun outcome => (interpretation outcome).map change))
      fuel before =
    WeightedResumption.mapCoefficients change
      (WeightedBranchingResumption.contributions
        (nestedSource program annotation interpretation) fuel before) := by
  apply WeightedBranchingResumption.contributions_change_coefficients change _ _ ?_ fuel before
  intro pending
  convert native_nested_source_change_coefficients change program annotation interpretation pending
    using 1
  cases inspected : nestedSource program annotation interpretation pending <;> rfl

/-- A declared grade guard commutes with a coefficient change only under its
separate admission law. The comparison retains whole native residuals. -/
theorem native_nested_admitted_change_coefficients {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admitSource : V → Bool) (admitTarget : W → Bool)
    (admits : ∀ value, admitTarget (change value) = admitSource value)
    (fuel : Nat) (before : NestedWork) :
    WeightedBranchingResumption.contributions
      (nestedAdmittedSource program annotation
        (fun outcome => (interpretation outcome).map change) admitTarget) fuel before =
    WeightedResumption.mapCoefficients change
      (WeightedBranchingResumption.contributions
        (nestedAdmittedSource program annotation interpretation admitSource) fuel before) := by
  apply WeightedBranchingResumption.admitting_at_contributions_change_coefficients
    change _ _ ?_ _ admitSource admitTarget admits fuel before
  intro pending
  convert native_nested_source_change_coefficients change program annotation interpretation pending
    using 1
  cases inspected : nestedSource program annotation interpretation pending <;> rfl

theorem authored_job_change {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (annotation : Row → Option AuthoredClause)
    (before after : NativeMachine) :
    authoredJob (V := W) annotation before after =
      Sum.map change id (authoredJob (V := V) annotation before after) := by
  cases capture : NativeGradeAttachment.captureNext before after with
  | none => simp [authoredJob, capture]
  | some captured =>
      cases attached : annotation captured.row <;> simp [authoredJob, capture, attached]

theorem authored_readout_change {V W : Type}
    (change : V → W) (interpretation : Outcome → Option V) (job : AuthoredJob) :
    authoredReadout (fun outcome => (interpretation outcome).map change) job =
      (authoredReadout interpretation job).map change := by
  cases phase : job.phase with
  | coefficient =>
      cases predicate : job.predicate <;>
        simp [authoredReadout, phase, predicate, coefficient_readout_change]
  | predicate completed =>
      by_cases verdict : predicateVerdict job.score = some true <;>
        simp [authoredReadout, phase, verdict, coefficient_readout_change]

theorem native_authored_change_coefficients {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : AuthoredWork) :
    WeightedBranchingResumption.contributions
      (authoredSource program annotation (fun outcome => (interpretation outcome).map change))
      fuel before =
    WeightedResumption.mapCoefficients change
      (WeightedBranchingResumption.contributions
        (authoredSource program annotation interpretation) fuel before) := by
  apply WeightedBranchingResumption.contributions_change_coefficients
    change _ _ ?_ fuel before
  intro pending
  unfold authoredSource
  convert WeightedBranchingResumption.nested_pending_change_coefficients
    (State := WorkState) (Answer := WorkState) (Job := AuthoredJob) (Grade := AuthoredJob)
    change
    (NeedWeightedResumption.source (specification program) (authoredJob (V := V) annotation))
    (NeedWeightedResumption.source (specification program) (authoredJob (V := W) annotation))
    (authoredGradeSource (V := V) program annotation)
    (authoredGradeSource (V := W) program annotation) ?_ ?_
    (authoredReadout interpretation)
    (authoredReadout (fun outcome => (interpretation outcome).map change)) ?_
    resumeAuthoredBody resumeAuthoredParent pending using 1
  · cases inspected : WeightedBranchingResumption.nestedPendingSource
      (NeedWeightedResumption.source (specification program) (authoredJob (V := V) annotation))
      (authoredGradeSource (V := V) program annotation) (authoredReadout interpretation)
      resumeAuthoredBody resumeAuthoredParent pending <;> rfl
  · intro body
    cases control : body.state.control <;>
      simp [NeedWeightedResumption.source, NeedWeightedResumption.successors,
        control, List.map_map, authored_job_change change]
  · intro job
    unfold authoredGradeSource
    by_cases halted : isHalted job.score.machine
    · simp only [halted, ↓reduceIte]
      cases phase : job.phase with
      | coefficient =>
          simp only []
          split <;> simp [map_one]
      | predicate completed =>
          simp only []
          split <;> simp
    · simp [halted, List.map_map, authored_job_change change]
  · exact authored_readout_change change interpretation


/-! ## Recorded heaps through authored coefficient continuations -/

namespace AuthoredPhase

def Recorded : AuthoredPhase → Prop
  | .coefficient => True
  | .predicate completed => completed.Recorded

end AuthoredPhase

namespace AuthoredJob

def Recorded (job : AuthoredJob) : Prop := job.score.Recorded ∧ job.phase.Recorded

end AuthoredJob

def authoredHeapsRecorded : AuthoredWork → Prop :=
  WeightedBranchingResumption.nestedWorkHolds
    (fun body : WorkState => body.state.world.heap.Recorded) AuthoredJob.Recorded

def authoredResultHeapsRecorded : AuthoredResult → Prop :=
  WeightedBranchingResumption.nestedResultHolds
    (fun body : WorkState => body.state.world.heap.Recorded)
    (fun body : WorkState => body.state.world.heap.Recorded)
    AuthoredJob.Recorded AuthoredJob.Recorded

theorem authored_job_recorded {V : Type} [One V]
    (annotation : Row → Option AuthoredClause) (before after : NativeMachine)
    (job : AuthoredJob) (valid : after.world.heap.Recorded)
    (chosen : authoredJob (V := V) annotation before after = .inr job) : job.Recorded := by
  obtain ⟨capture, clause, captured, _, rfl⟩ :=
    authored_job_capture annotation before after job chosen
  have body := (NativeGradeAttachment.captured_next_exact before after capture captured).1
  have capturedHeap := congrArg (fun machine : NativeMachine => machine.world.heap) body
  have originValid : capture.Recorded := by
    change capture.world.heap.Recorded
    change capture.world.heap = after.world.heap at capturedHeap
    rw [capturedHeap]
    exact valid
  exact ⟨Captured.score_recorded capture clause.coefficient originValid, True.intro⟩

theorem begin_predicate_recorded (job : AuthoredJob) (predicate value : Atom)
    (valid : job.Recorded) : (beginPredicate job predicate value).Recorded :=
  ⟨⟨valid.1.1, valid.1.2⟩, valid.1⟩

theorem resume_authored_body_recorded (body : WorkState) (job : AuthoredJob)
    (valid : job.Recorded) : (resumeAuthoredBody body job).state.world.heap.Recorded := valid.1.2

theorem resume_authored_parent_recorded (parent child : AuthoredJob)
    (parentValid : parent.Recorded) (childValid : child.Recorded) :
    (resumeAuthoredParent parent child).Recorded :=
  ⟨⟨parentValid.1.1, childValid.1.2⟩, parentValid.2⟩

theorem authored_grade_steps_recorded {V : Type} [One V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (job : AuthoredJob) (alternatives : List (AuthoredJob × (V ⊕ AuthoredJob)))
    (valid : job.Recorded)
    (requested : authoredGradeSource program annotation job = .inr alternatives)
    (next : AuthoredJob × (V ⊕ AuthoredJob)) (member : next ∈ alternatives) :
    next.1.Recorded ∧ ∀ child, next.2 = .inr child → child.Recorded := by
  unfold authoredGradeSource at requested
  split at requested
  · split at requested
    · split at requested
      · simp only [Sum.inr.injEq] at requested
        subst alternatives
        obtain rfl := List.mem_singleton.mp member
        exact ⟨begin_predicate_recorded _ _ _ valid, by intro child impossible; contradiction⟩
      · simp at requested
    · split at requested
      · simp only [Sum.inr.injEq] at requested
        subst alternatives
        simp at member
      · simp at requested
  · simp only [Sum.inr.injEq] at requested
    subst alternatives
    obtain ⟨score, actual, rfl⟩ := List.mem_map.mp member
    have scoreValid := score_step_recorded program job.score score valid.1 actual
    refine ⟨⟨scoreValid, valid.2⟩, ?_⟩
    intro child chosen
    exact authored_job_recorded annotation job.score.machine score.machine child scoreValid.2 chosen

/-- Every actual transition preserves all live, captured and suspended heaps.
The generic nested-handler rule supplies stack preservation; actual Need
instructions and captured-row construction discharge its native premises. -/
theorem authored_source_recorded {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) :
    (∀ work result, authoredHeapsRecorded work →
      authoredSource program annotation interpretation work = .inl result →
      authoredResultHeapsRecorded result) ∧
    (∀ work alternatives, authoredHeapsRecorded work →
      authoredSource program annotation interpretation work = .inr alternatives →
      ∀ next ∈ alternatives, authoredHeapsRecorded next.1) := by
  apply WeightedBranchingResumption.nested_source_preserves
    (NeedWeightedResumption.source (specification program) (authoredJob annotation))
    (authoredGradeSource program annotation) (authoredReadout interpretation)
    resumeAuthoredBody resumeAuthoredParent
    (fun body : WorkState => body.state.world.heap.Recorded)
    (fun body : WorkState => body.state.world.heap.Recorded)
    AuthoredJob.Recorded AuthoredJob.Recorded
  · intro body answer inherited returned
    obtain ⟨rfl, _⟩ := (NeedWeightedResumption.source_return_iff
      (specification program) (authoredJob annotation) body answer).mp returned
    exact inherited
  · intro body alternatives inherited requested next member
    rcases next with ⟨child, coefficient⟩
    have located : (child, coefficient) ∈ NeedWeightedResumption.successors
        (specification program) (authoredJob annotation) body := by
      cases control : body.state.control <;>
        simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr, Sum.inr.injEq]
    obtain ⟨_, actual, _, caused⟩ := (NeedWeightedResumption.successor_iff
      (specification program) (authoredJob annotation) body child coefficient).mp located
    have childValid := NeedReference.step_heap_recorded (specification program) _ _
      inherited (List.mem_of_getElem? actual)
    refine ⟨childValid, ?_⟩
    intro job chosen
    exact authored_job_recorded annotation body.state child.state job childValid
      (caused.symm.trans chosen)
  · intro job result inherited returned
    rw [authored_grade_return_same_job program annotation job result returned]
    exact inherited
  · exact authored_grade_steps_recorded program annotation
  · intro body job _ valid
    exact resume_authored_body_recorded body job valid
  · exact resume_authored_parent_recorded

theorem authored_contributions_recorded {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (work : AuthoredWork)
    (valid : authoredHeapsRecorded work) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel work,
      Sum.elim authoredResultHeapsRecorded authoredHeapsRecorded leaf.1 := by
  obtain ⟨returns, successors⟩ := authored_source_recorded program annotation interpretation
  exact WeightedBranchingResumption.contributions_invariant _ _ _
    returns successors fuel work valid

theorem authored_root_recorded (term : Atom) :
    authoredHeapsRecorded (.inl (WorkOccurrence.root (initial term))) :=
  initial_heap_recorded term


namespace AuthoredPhase

abbrev RecordedView := Option Score.RecordedView

instance instDecidableEqRecordedView : DecidableEq RecordedView :=
  inferInstanceAs (DecidableEq (Option Score.RecordedView))

def recordedView : AuthoredPhase → RecordedView
  | .coefficient => none
  | .predicate completed => some completed.recordedView

def ofRecordedView : RecordedView → AuthoredPhase
  | none => .coefficient
  | some completed => .predicate (Score.ofRecordedView completed)

theorem ofRecordedView_recorded (view : RecordedView) : (ofRecordedView view).Recorded := by
  cases view with
  | none => trivial
  | some completed => exact Score.ofRecordedView_recorded completed

@[simp] theorem recordedView_ofRecordedView (view : RecordedView) :
    (ofRecordedView view).recordedView = view := by cases view <;> rfl

theorem ofRecordedView_recordedView (phase : AuthoredPhase) (valid : phase.Recorded) :
    ofRecordedView phase.recordedView = phase := by
  cases phase with
  | coefficient => rfl
  | predicate completed =>
      change AuthoredPhase.predicate (Score.ofRecordedView completed.recordedView) = _
      rw [Score.ofRecordedView_recordedView completed valid]

end AuthoredPhase

namespace AuthoredJob

abbrev RecordedView := Score.RecordedView × Option Atom × AuthoredPhase.RecordedView

instance instDecidableEqRecordedView : DecidableEq RecordedView :=
  inferInstanceAs (DecidableEq (Score.RecordedView × Option Atom × AuthoredPhase.RecordedView))

def recordedView (job : AuthoredJob) : RecordedView :=
  (job.score.recordedView, job.predicate, job.phase.recordedView)

def ofRecordedView (view : RecordedView) : AuthoredJob :=
  ⟨Score.ofRecordedView view.1, view.2.1, AuthoredPhase.ofRecordedView view.2.2⟩

theorem ofRecordedView_recorded (view : RecordedView) : (ofRecordedView view).Recorded :=
  ⟨Score.ofRecordedView_recorded _, AuthoredPhase.ofRecordedView_recorded _⟩

@[simp] theorem recordedView_ofRecordedView (view : RecordedView) :
    (ofRecordedView view).recordedView = view := by
  simp only [ofRecordedView, recordedView, Score.recordedView_ofRecordedView,
    AuthoredPhase.recordedView_ofRecordedView]

theorem ofRecordedView_recordedView (job : AuthoredJob) (valid : job.Recorded) :
    ofRecordedView job.recordedView = job := by
  cases job with
  | mk score predicate phase =>
      simp only [ofRecordedView, recordedView]
      rw [Score.ofRecordedView_recordedView score valid.1,
        AuthoredPhase.ofRecordedView_recordedView phase valid.2]

theorem parents_roundtrip (parents : List AuthoredJob)
    (valid : ∀ parent ∈ parents, parent.Recorded) :
    (parents.map recordedView).map ofRecordedView = parents := by
  simp only [List.map_map]
  calc
    _ = parents.map id := by
      apply List.map_congr_left
      intro parent member
      exact ofRecordedView_recordedView parent (valid parent member)
    _ = _ := List.map_id _

end AuthoredJob

abbrev RecordedWorkView := WorkOccurrence
  (Machine.RecordedView Origin Local Resume Rule Atom Empty String Empty)

def workRecordedView (body : WorkState) : RecordedWorkView :=
  ⟨body.state.recordedView, body.trace⟩

def workOfRecordedView (view : RecordedWorkView) : WorkState :=
  ⟨Machine.ofRecordedView view.state, view.trace⟩

theorem workOfRecordedView_recorded (view : RecordedWorkView) :
    (workOfRecordedView view).state.world.heap.Recorded := Machine.ofRecordedView_recorded _

@[simp] theorem workRecordedView_ofRecordedView (view : RecordedWorkView) :
    workRecordedView (workOfRecordedView view) = view := rfl

theorem workOfRecordedView_recordedView (body : WorkState)
    (valid : body.state.world.heap.Recorded) : workOfRecordedView (workRecordedView body) = body := by
  cases body with
  | mk state trace =>
      simp only [workOfRecordedView, workRecordedView]
      rw [Machine.ofRecordedView_recordedView state valid]

abbrev AuthoredRecordedView :=
  WeightedBranchingResumption.NestedPendingState RecordedWorkView AuthoredJob.RecordedView

def authoredRecordedView : AuthoredWork → AuthoredRecordedView
  | .inl body => .inl (workRecordedView body)
  | .inr (body, job, parents) =>
      .inr (workRecordedView body, job.recordedView, parents.map AuthoredJob.recordedView)

def authoredOfRecordedView : AuthoredRecordedView → AuthoredWork
  | .inl body => .inl (workOfRecordedView body)
  | .inr (body, job, parents) =>
      .inr (workOfRecordedView body, AuthoredJob.ofRecordedView job,
        parents.map AuthoredJob.ofRecordedView)

theorem authoredOfRecordedView_recorded (view : AuthoredRecordedView) :
    authoredHeapsRecorded (authoredOfRecordedView view) := by
  cases view with
  | inl body => exact workOfRecordedView_recorded body
  | inr held =>
      rcases held with ⟨body, job, parents⟩
      refine ⟨workOfRecordedView_recorded body, AuthoredJob.ofRecordedView_recorded job, ?_⟩
      intro parent member
      obtain ⟨view, _, rfl⟩ := List.mem_map.mp member
      exact AuthoredJob.ofRecordedView_recorded view

@[simp] theorem authoredRecordedView_ofRecordedView (view : AuthoredRecordedView) :
    authoredRecordedView (authoredOfRecordedView view) = view := by
  cases view with
  | inl body => rfl
  | inr held =>
      rcases held with ⟨body, job, parents⟩
      simp only [authoredOfRecordedView, authoredRecordedView, workRecordedView_ofRecordedView,
        AuthoredJob.recordedView_ofRecordedView, List.map_map]
      simp only [Function.comp_def, AuthoredJob.recordedView_ofRecordedView, List.map_id']

theorem authoredOfRecordedView_recordedView (work : AuthoredWork)
    (valid : authoredHeapsRecorded work) : authoredOfRecordedView (authoredRecordedView work) = work := by
  cases work with
  | inl body =>
      simp only [authoredOfRecordedView, authoredRecordedView]
      rw [workOfRecordedView_recordedView body valid]
  | inr held =>
      rcases held with ⟨body, job, parents⟩
      rcases valid with ⟨bodyValid, jobValid, parentsValid⟩
      simp only [authoredOfRecordedView, authoredRecordedView]
      rw [workOfRecordedView_recordedView body bodyValid,
        AuthoredJob.ofRecordedView_recordedView job jobValid,
        AuthoredJob.parents_roundtrip parents parentsValid]

theorem authoredRecordedView_injective (left right : AuthoredWork)
    (leftValid : authoredHeapsRecorded left) (rightValid : authoredHeapsRecorded right)
    (same : authoredRecordedView left = authoredRecordedView right) : left = right :=
  (authoredOfRecordedView_recordedView left leftValid).symm.trans
    ((congrArg authoredOfRecordedView same).trans
      (authoredOfRecordedView_recordedView right rightValid))

/-- Equality of invariant-carrying native states executes on finite retained
data, including every captured heap and suspended coefficient parent. -/
instance : DecidableEq {work : AuthoredWork // authoredHeapsRecorded work} := fun left right =>
  if same : authoredRecordedView left.val = authoredRecordedView right.val then
    isTrue (Subtype.ext (authoredRecordedView_injective _ _ left.property right.property same))
  else isFalse (fun equal => same (congrArg (fun work => authoredRecordedView work.val) equal))

theorem authored_result_heaps_iff (result : AuthoredResult) :
    authoredResultHeapsRecorded result ↔ authoredHeapsRecorded result := by
  cases result <;> rfl

instance : DecidableEq {result : AuthoredResult // authoredResultHeapsRecorded result} :=
  fun left right =>
    if same : authoredRecordedView left.val = authoredRecordedView right.val then
      isTrue (Subtype.ext (authoredRecordedView_injective _ _
        ((authored_result_heaps_iff _).mp left.property)
        ((authored_result_heaps_iff _).mp right.property) same))
    else isFalse (fun equal => same (congrArg (fun work => authoredRecordedView work.val) equal))


/-! ## Executable replay over the actual retained native heaps

The invariant witnesses come from the native instruction and capture proofs.
They are erased at execution. Comparison uses finite views of every live and
captured world; it does not assume equality of arbitrary function-valued heaps.
-/

abbrev RecordedAuthoredWork := {work : AuthoredWork // authoredHeapsRecorded work}
abbrev RecordedAuthoredResult := {result : AuthoredResult // authoredResultHeapsRecorded result}

/-- The original source with its proved heap invariant carried in the type.
No successor, including an equal or zero-weight occurrence, is filtered. -/
def recordedAuthoredSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    WeightedBranchingResumption.Coalgebra RecordedAuthoredWork RecordedAuthoredResult V :=
  WeightedBranchingResumption.invariantSource
    (authoredSource program annotation interpretation)
    authoredHeapsRecorded authoredResultHeapsRecorded
    (authored_source_recorded program annotation interpretation).1
    (authored_source_recorded program annotation interpretation).2

def recordedAuthoredRoot (term : Atom) : RecordedAuthoredWork :=
  ⟨.inl (WorkOccurrence.root (initial term)), authored_root_recorded term⟩

/-- Erasure retains the complete ordered finite observation, including all
pending handler frames and coefficients, at every cut of the native run. -/
theorem recorded_authored_contributions_erasure {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (state : RecordedAuthoredWork) :
    WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel state.val =
      (WeightedBranchingResumption.contributions
        (recordedAuthoredSource program annotation interpretation) fuel state).map
          (fun leaf => (Sum.map Subtype.val Subtype.val leaf.1, leaf.2)) :=
  WeightedBranchingResumption.invariantSource_contributions _ _ _
    (authored_source_recorded program annotation interpretation).1
    (authored_source_recorded program annotation interpretation).2 fuel state

open Mettapedia.GSLT.Core.BranchingTemporal

/-- The existing occurrence scheduler applied to the preserved native
invariant. The outer path distinguishes equal successor occurrences. -/
def recordedAuthoredOccurrenceSystem {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    BranchingSystem (WorkOccurrence (RecordedAuthoredWork × V))
      ((RecordedAuthoredResult × V) × List Nat) :=
  WorkOccurrence.system (WeightedBranchingResumption.Scheduled.pathMachine
    (recordedAuthoredSource program annotation interpretation))

/-- Native replay now has an executable equality procedure for all retained
states and results. Only equality of the chosen coefficient representation
is requested from its provider. Rules, interpretation, controller and starting
snapshot stay fixed; repeating external effects requires another contract. -/
theorem recorded_native_replay {V : Type} [Monoid V] [DecidableEq V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (RecordedAuthoredWork × V))
      ((RecordedAuthoredResult × V) × List Nat) Memory)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (WorkOccurrence (RecordedAuthoredWork × V)) ((RecordedAuthoredResult × V) × List Nat) Memory)
    (capacity fuel : Nat)
    (fits : (Recording.stream (recordedAuthoredOccurrenceSystem program annotation interpretation)
      controller Recording.Replay.observe fuel snapshot).length ≤ capacity) :
    ((Recording.runSelected
      (recordedAuthoredOccurrenceSystem program annotation interpretation)
      controller Recording.Replay.observe fuel
      (Recording.start snapshot (some capacity))).memory.2).bind
        (fun record => Recording.Replay.readout
          (recordedAuthoredOccurrenceSystem program annotation interpretation) controller record snapshot) =
      some (.ok (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (recordedAuthoredOccurrenceSystem program annotation interpretation) controller fuel snapshot)) :=
  Recording.Replay.selected_recorded_replay _ _ _ _ _ fits

/-- A mismatch preserves its entire native checkpoint and unconsumed suffix.
The accepted prefix consists of actual recomputed source transitions. -/
theorem recorded_native_replay_refusal {V : Type} [Monoid V] [DecidableEq V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (RecordedAuthoredWork × V))
      ((RecordedAuthoredResult × V) × List Nat) Memory)
    (frames pending : List (Preparation.Capture (WorkOccurrence (RecordedAuthoredWork × V))
      ((RecordedAuthoredResult × V) × List Nat)))
    (snapshot cut : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (WorkOccurrence (RecordedAuthoredWork × V)) ((RecordedAuthoredResult × V) × List Nat) Memory)
    (refused : Recording.Replay.run (recordedAuthoredOccurrenceSystem program annotation interpretation)
      controller frames snapshot = .error (cut, pending)) :
    ∃ acceptedFrames frame rest,
      frames = acceptedFrames ++ frame :: rest ∧ pending = frame :: rest ∧
      cut = Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (recordedAuthoredOccurrenceSystem program annotation interpretation) controller
        acceptedFrames.length snapshot ∧
      Recording.Replay.step? (recordedAuthoredOccurrenceSystem program annotation interpretation)
        controller cut frame = none :=
  Recording.Replay.run_refused _ _ _ _ _ _ refused

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler


/-! ## Retained rich-Need invocation representation

This adapter uses the existing first-class scoped Need grammar and its actual
local/protocol transitions. The target delegates protocol instructions to the
independent receipt-policy executor. Both sides use the maintained occurrence
controller; no source evaluator or scheduler is defined from a target image.

The selected observer retains every ordered return, fault, successor position,
heap, lexical control and work counter. Receipt erasure is an explicit observer
choice. Native Atom decoding, receiving ownership, current external permissions
and physical primitive prices remain separate realization obligations. The
scoped grammar is a declared operational profile, not a choice of foundation
or a textual front end for the whole Prime language.
-/
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.RetainedInvocation

open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.ProductiveCoreAdapters.ComponentRealization

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

abbrev Rich := PolarizedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m
abbrev Native := NeedExecution.CoreMachine
  (PolarizedNeedMachine.Closure Head Operation Effect m)
  (PolarizedNeedMachine.Local Head Operation Effect StableFault NativeFault m)
  (PolarizedNeedMachine.Resume Head Operation Effect m) PolarizedNeedMachine.Rule
  (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault
  (PolarizedNeedMachine.Fault NativeFault) Effect
abbrev Result := PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m
abbrev Source := Snapshot (WorkOccurrence (Rich (Head := Head) (Operation := Operation)
  (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m)))
  (Result (Head := Head) (Operation := Operation) (Effect := Effect)
    (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat) Nat
abbrev Target := Snapshot (WorkOccurrence (Native (Head := Head) (Operation := Operation)
  (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m)))
  (Result (Head := Head) (Operation := Operation) (Effect := Effect)
    (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat) Nat

local notation "RState" => Source (Head := Head) (Operation := Operation) (Effect := Effect)
  (StableFault := StableFault) (NativeFault := NativeFault) (m := m)
local notation "IState" => Target (Head := Head) (Operation := Operation) (Effect := Effect)
  (StableFault := StableFault) (NativeFault := NativeFault) (m := m)
local notation "RNode" => WorkOccurrence (Rich (Head := Head) (Operation := Operation)
  (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m))
local notation "INode" => WorkOccurrence (Native (Head := Head) (Operation := Operation)
  (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m))
local notation "Results" => List (Result (Head := Head) (Operation := Operation)
  (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat)
local notation "Stores" => List (Heap (PolarizedNeedMachine.Closure Head Operation Effect m)
  (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault)
local notation "Controls" => Nat × List (Control
  (PolarizedNeedMachine.Local Head Operation Effect StableFault NativeFault m)
  (PolarizedNeedMachine.Resume Head Operation Effect m)
  (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault
  (PolarizedNeedMachine.Fault NativeFault))
local notation "Worlds" => List (NeedExecution.CoreWorld
  (PolarizedNeedMachine.Closure Head Operation Effect m) PolarizedNeedMachine.Rule
  (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault
  (PolarizedNeedMachine.Fault NativeFault) Effect)

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
  (keepReceipts : Bool)

def projectNode (node : WorkOccurrence (Rich (Head := Head) (Operation := Operation)
    (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m))) :
    WorkOccurrence (Native (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m)) :=
  ⟨NeedExecution.projectMachine keepReceipts node.state, node.trace⟩

def project (state : Source (Head := Head) (Operation := Operation) (Effect := Effect)
    (StableFault := StableFault) (NativeFault := NativeFault) (m := m)) :
    Target (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m) :=
  state.mapState (projectNode keepReceipts) id

def sourceSystem : BranchingSystem
    (WorkOccurrence (Rich (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m)))
    (Result (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat) :=
  WorkOccurrence.lift ⟨haltedOutcome, NeedLocalSteps.step (PolarizedNeedMachine.extension primitive)⟩

def nativeSystem : BranchingSystem
    (WorkOccurrence (Native (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m)))
    (Result (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat) :=
  WorkOccurrence.lift ⟨NeedExecution.haltedOutcome,
    NeedLocalSteps.coreStep (PolarizedNeedMachine.extension primitive)⟩

def controller (Node Answer : Type) : Controller Node Answer Nat where
  initialMemory := 0
  scheduler _ := Scheduler.breadthFirst
  advance memory _ _ _ := memory + 1

theorem local_emit (node : WorkOccurrence (Rich (Head := Head) (Operation := Operation)
    (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m))) :
    (sourceSystem primitive).emit node =
      (nativeSystem primitive).emit (projectNode keepReceipts node) := by
  simp only [sourceSystem, nativeSystem, WorkOccurrence.lift, projectNode,
    NeedExecution.haltedOutcome_project]

theorem local_successors (node : WorkOccurrence (Rich (Head := Head) (Operation := Operation)
    (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m))) :
    ((sourceSystem primitive).successors node).map (projectNode keepReceipts) =
      (nativeSystem primitive).successors (projectNode keepReceipts node) := by
  simp only [sourceSystem, nativeSystem, WorkOccurrence.lift, projectNode]
  rw [← NeedLocalSteps.project_local_step keepReceipts (PolarizedNeedMachine.extension primitive)]
  simp only [List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq, projectNode]

def sourceTick : RState → RState := Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick (sourceSystem primitive) (controller _ _)
def nativeTick : IState → IState := Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick (nativeSystem primitive) (controller _ _)

/-- The actual selected occurrence, all generated children and every archived
return commute with the representation. No completed-run equality is assumed. -/
theorem tick_representation (state : Source (Head := Head) (Operation := Operation)
    (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m)) :
    project keepReceipts (sourceTick primitive state) =
      nativeTick primitive (project keepReceipts state) := by
  exact Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick_mapState (projectNode keepReceipts) id (sourceSystem primitive)
    (nativeSystem primitive) (controller _ _) (controller _ _)
    (local_emit primitive keepReceipts) (local_successors primitive keepReceipts)
    (fun _ _ => rfl)
    (fun _ _ _ => by simp [controller, Scheduler.breadthFirst, List.map_append])
    (fun _ _ _ _ => rfl) state

/-- Live and archived states both retain the heap owners needed by a returned
closure. This is a semantic retained inventory; acquiring native owners is a
separate receiving contract. -/
def participants {State Answer : Type}
    (state : Snapshot (WorkOccurrence State) Answer Nat) : List State :=
  state.search.frontier.map WorkOccurrence.state ++
    state.search.events.map (fun event => event.origin.state)

theorem participants_project (state : Source (Head := Head) (Operation := Operation)
    (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m)) :
    participants (project keepReceipts state) =
      (participants state).map (NeedExecution.projectMachine keepReceipts) := by
  simp [participants, project, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapState, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapMemory,
    Mettapedia.GSLT.Core.BranchingTemporal.Snapshot.mapNodes, Emission.mapOrigin,
    projectNode, List.map_append, List.map_map, Function.comp_def]


/-- Ordered outcomes include stable and retryable faults. Completion of the
frontier does not turn either into an empty successful answer. -/
def publication {State Answer : Type}
    (state : Snapshot (WorkOccurrence State) Answer Nat) : List Answer :=
  state.search.events.map Emission.value

def logicalProjection : ComponentProjection RState Stores Controls
    (List (List Nat)) Worlds Results where
  store state := (participants state).map (fun machine => machine.world.heap)
  control state := (state.memory, (participants state).map (fun machine => machine.control))
  selection state := state.search.frontier.map WorkOccurrence.trace
  world state := (participants state).map (fun machine =>
    NeedExecution.projectWorld keepReceipts machine.world)
  publication := publication

def implementationProjection : ComponentProjection IState Stores Controls
    (List (List Nat)) Worlds Results where
  store state := (participants state).map (fun machine => machine.world.heap)
  control state := (state.memory, (participants state).map (fun machine => machine.control))
  selection state := state.search.frontier.map WorkOccurrence.trace
  world state := (participants state).map (fun machine => machine.world)
  publication := publication

/-- The relation retains all five projections, with the full represented
snapshot as their coherence witness. Its local control law is proved below
from the two actual successor functions. -/
def relation : FiveComponentRel (logicalProjection (Head := Head) (Operation := Operation)
    (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m)
    keepReceipts) (implementationProjection : ComponentProjection IState Stores Controls
      (List (List Nat)) Worlds Results) where
  storeRel := Eq
  controlRel := Eq
  selectionRel := Eq
  worldRel := Eq
  publicationRel := Eq
  coherent source target := target = project keepReceipts source

theorem represented (state : RState) :
    (relation keepReceipts).Holds state (project keepReceipts state) := by
  unfold FiveComponentRel.Holds relation
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
  · change (participants state).map (fun machine => machine.world.heap) =
      (participants (project keepReceipts state)).map (fun machine => machine.world.heap)
    rw [participants_project, List.map_map]
    rfl
  · change (state.memory, (participants state).map (fun machine => machine.control)) =
      ((project keepReceipts state).memory,
        (participants (project keepReceipts state)).map (fun machine => machine.control))
    rw [participants_project, List.map_map]
    rfl
  · change state.search.frontier.map WorkOccurrence.trace =
      (state.search.frontier.map (projectNode keepReceipts)).map WorkOccurrence.trace
    rw [List.map_map]
    rfl
  · change (participants state).map (fun machine =>
        NeedExecution.projectWorld keepReceipts machine.world) =
      (participants (project keepReceipts state)).map (fun machine => machine.world)
    rw [participants_project, List.map_map]
    rfl
  · change state.search.events.map Emission.value =
      (state.search.events.map (Emission.mapOrigin (projectNode keepReceipts))).map Emission.value
    rw [List.map_map]
    rfl

/-- One scheduler inspection uses the existing controller. The source and
implementation independently inspect their own frontier and successors. -/
def sourceMachine : Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine RState RNode Results Empty where
  step state := some (match state.search.frontier with
    | [] => .finish (publication state)
    | node :: _ => .publish [node] (sourceTick primitive state))

def implementationMachine : Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine IState INode Results Empty where
  step state := some (match state.search.frontier with
    | [] => .finish (publication state)
    | node :: _ => .publish [node] (nativeTick primitive state))

def sourceRule (state : RState) (transition : Option (Transition RState RNode Results Empty)) : Prop :=
  (sourceMachine primitive).step state = transition

def implementationRule (state : IState) (transition : Option (Transition IState INode Results Empty)) : Prop :=
  (implementationMachine primitive).step state = transition

def sourceReadout : ExecutionReadout RNode Results Empty INode Results Empty where
  event node := [projectNode keepReceipts node]
  verdict := id
  request := id

def implementationReadout : ExecutionReadout INode Results Empty INode Results Empty where
  event node := [node]
  verdict := id
  request := id

/-- A real source inspection is realized by a productive implementation
inspection. In particular a retained return origin and every unfinished child
are related at the actual cut; neither is reconstructed from the final bag. -/
theorem productive_block : ProductiveLocalBlock (Source := RState) (Target := IState)
    (sourceRule primitive) (implementationRule primitive) (relation keepReceipts).Holds
    (sourceReadout keepReceipts) implementationReadout := by
  constructor
  intro before target events outcome related path
  have coherent := related.2.2.2.2.2
  subst target
  cases ordered : before.search.frontier with
  | nil =>
      cases path with
      | silent moved rest => simp [sourceRule, sourceMachine, ordered] at moved
      | published moved rest => simp [sourceRule, sourceMachine, ordered] at moved
      | finished moved =>
          simp only [sourceRule, sourceMachine, ordered, Option.some.injEq,
            Transition.finish.injEq] at moved
          subst moved
          refine ⟨1, by omega, [], .finished (publication before), .finished ?_, rfl, .finished _⟩
          simp [implementationRule, implementationMachine, project, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapState,
            Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapMemory,
            Mettapedia.GSLT.Core.BranchingTemporal.Snapshot.mapNodes, publication,
            Emission.mapOrigin, ordered, List.map_map]
      | faulted moved => simp [sourceRule, sourceMachine, ordered] at moved
      | requested moved => simp [sourceRule, sourceMachine, ordered] at moved
      | stuck moved => simp [sourceRule, sourceMachine, ordered] at moved
  | cons node rest =>
      cases path with
      | silent moved rest => simp [sourceRule, sourceMachine, ordered] at moved
      | published moved tail =>
          cases tail
          simp only [sourceRule, sourceMachine, ordered, Option.some.injEq,
            Transition.publish.injEq] at moved
          obtain ⟨rfl, rfl⟩ := moved
          have advance : implementationRule primitive (project keepReceipts before)
              (some (.publish [projectNode keepReceipts node]
                (project keepReceipts (sourceTick primitive before)))) := by
            have displayed : (project keepReceipts before).search.frontier =
                projectNode keepReceipts node :: rest.map (projectNode keepReceipts) := by
              change before.search.frontier.map (projectNode keepReceipts) = _
              rw [ordered]
              rfl
            dsimp only [implementationRule, implementationMachine]
            rw [displayed, tick_representation primitive keepReceipts]
          refine ⟨1, by omega, [projectNode keepReceipts node],
            .exhausted (project keepReceipts (sourceTick primitive before)),
            ?_, rfl, .exhausted (represented keepReceipts _)⟩
          simpa only [List.append_nil] using Derivation.published advance (.pause _)
      | finished moved => simp [sourceRule, sourceMachine, ordered] at moved
      | faulted moved => simp [sourceRule, sourceMachine, ordered] at moved
      | requested moved => simp [sourceRule, sourceMachine, ordered] at moved
      | stuck moved => simp [sourceRule, sourceMachine, ordered] at moved

/-- A captured lexical root is entered in the supplied current Need world.
There is no world hidden inside the callable's lexical representation. -/
structure Load (Head Operation Effect StableFault NativeFault : Type) (m : Nat) where
  world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m
  closure : PolarizedNeedMachine.Closure Head Operation Effect m

def loadSource (input : Load Head Operation Effect StableFault NativeFault m) : RState :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial (controller _ _)
    [⟨⟨input.world, .run (.evaluate input.closure .done) [], {}⟩, []⟩]

def loadImplementation (input : Load Head Operation Effect StableFault NativeFault m) : IState :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial (controller _ _)
    [⟨⟨NeedExecution.projectWorld keepReceipts input.world,
      .run (.evaluate input.closure .done) [], {}⟩, []⟩]

/-- Reads address an actual retained heap in either a live or archived node.
Cell identity includes its lineage, birth path, slot and generation. -/
def readStore (stores : Stores) (query : Nat × CellId) :=
  (stores[query.1]?).bind (fun heap => heap.lookup query.2)

/-- M1--M7 are local constructed laws for distinct machine representations.
The common owner derives M8, including retained prefix/suffix composition. -/
def realization : ModularMachineAdequacy
    (Input := Load Head Operation Effect StableFault NativeFault m)
    (LogicalConfig := RState) (ImplConfig := IState)
    loadSource (loadImplementation keepReceipts)
    (logicalProjection keepReceipts) implementationProjection (relation keepReceipts)
    (sourceRule primitive) (implementationRule primitive)
    (sourceReadout keepReceipts) implementationReadout
    (List (List Nat)) (Nat × CellId)
    (Option (CellRecord (PolarizedNeedMachine.Closure Head Operation Effect m)
      (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault))
    Worlds Controls Results (Nat × CellId)
    (Option (CellRecord (PolarizedNeedMachine.Closure Head Operation Effect m)
      (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault)) where
  m1_load input := represented keepReceipts (loadSource input)
  observeLogicalSelection := id
  observeImplSelection := id
  m2_selection related := related.2.2.1
  readLogicalStore := readStore
  readImplStore := readStore
  m3_store_read related query := congrArg (fun stores => readStore stores query) related.1
  m4_control := productive_block primitive keepReceipts
  observeLogicalWorld := id
  observeImplWorld := id
  m5_world related := related.2.2.2.1
  observeLogicalControl := id
  observeImplControl := id
  m6_retained_control related := related.2.1
  observeLogicalPublication := id
  observeImplPublication := id
  m7_publication related := related.2.2.2.2.1
  observeLogicalFuture state query := readStore ((logicalProjection keepReceipts).store state) query
  observeImplFuture state query := readStore (implementationProjection.store state) query
  m7_future related query := congrArg (fun stores => readStore stores query) related.1

/-- Exact retained runs are obtained from the shared local-to-global theorem.
The semantic inspection counts here are not native callback or CPU bounds. -/
theorem retained_run (input : Load Head Operation Effect StableFault NativeFault m)
    {first second : Nat} {saved : RState} {events later : List RNode}
    {outcome : Outcome RState Results Empty}
    (initial : Derivation (sourceRule primitive) first (loadSource input) events (.exhausted saved))
    (suffix : Derivation (sourceRule primitive) second saved later outcome) :
    ∃ (first' second' : Nat) (saved' : IState) (events' later' : List INode)
      (outcome' : Outcome IState Results Empty),
      Derivation (implementationRule primitive) first' (loadImplementation keepReceipts input)
        events' (.exhausted saved') ∧
      Derivation (implementationRule primitive) second' saved' later' outcome' ∧
      (relation keepReceipts).Holds saved saved' ∧
      (realization primitive keepReceipts).ObservationsAgree saved saved' ∧
      events'.flatMap implementationReadout.event = events.flatMap (sourceReadout keepReceipts).event ∧
      later'.flatMap implementationReadout.event = later.flatMap (sourceReadout keepReceipts).event ∧
      OutcomeRel (relation keepReceipts).Holds outcome outcome' ∧
      Derivation (implementationRule primitive) (first' + second')
        (loadImplementation keepReceipts input) (events' ++ later') outcome' :=
  by
    simpa only [sourceReadout, implementationReadout, Outcome.relabel_id] using
      ModularMachineAdequacy.loaded_retained_run (realization primitive keepReceipts) input initial suffix


/-- Pure inspection of a receiving heap uses the same complete cell identity
in live and archived source/implementation states. It supplies no force right. -/
theorem future_cell_read (state : RState) (query : Nat × CellId) :
    readStore ((logicalProjection keepReceipts).store state) query =
      readStore (implementationProjection.store (project keepReceipts state)) query :=
  congrArg (fun stores => readStore stores query) (represented keepReceipts state).1

open Mettapedia.Machines.SourceProducerCardinality (CallingConvention ConventionAllows)

/-- Incomplete, faulted and cardinality-refused observations remain distinct.
The surrounding snapshot owns the exact residual and retained paid state. -/
inductive ModeReadout (Answer Stable Retry : Type) where
  | pending
  | faulted (outcomes : List (Produced Answer Stable Retry))
  | refused (values : List Answer)
  | ready (values : List Answer)

/-- A fault in an all-results computation is retained rather than silently
filtered into a successful smaller collection. -/
def successfulValues {Answer Stable Retry : Type} :
    List (Produced Answer Stable Retry) → Option (List Answer)
  | [] => some []
  | .value value :: rest => (successfulValues rest).map (value :: ·)
  | .stableFault _ :: _ | .retryableFault _ :: _ => none

theorem successfulValues_iff {Answer Stable Retry : Type}
    (outcomes : List (Produced Answer Stable Retry)) (values : List Answer) :
    successfulValues outcomes = some values ↔ outcomes = values.map Produced.value := by
  induction outcomes generalizing values with
  | nil => cases values <;> simp [successfulValues]
  | cons outcome rest ih =>
      cases outcome with
      | value value =>
          cases values with
          | nil => simp [successfulValues]
          | cons first values =>
              simp only [successfulValues, Option.map_eq_some_iff,
                List.map_cons, List.cons.injEq, Produced.value.injEq]
              constructor
              · rintro ⟨remaining, observed, same⟩
                rcases same with ⟨rfl, rfl⟩
                exact ⟨rfl, (ih _).mp observed⟩
              · rintro ⟨rfl, same⟩
                exact ⟨values, (ih _).mpr same, rfl, rfl⟩
      | stableFault fault => cases values <;> simp [successfulValues]
      | retryableFault fault => cases values <;> simp [successfulValues]

def checkMode : CallingConvention → Nat → Bool
  | .direct, count => decide (count = 1)
  | .optional, count => decide (count ≤ 1)
  | .nonemptyProducer, count => decide (1 ≤ count)
  | .producer, _ => true

theorem checkMode_iff (mode : CallingConvention) (count : Nat) :
    checkMode mode count = true ↔ ConventionAllows mode count := by
  cases mode <;> simp [checkMode, ConventionAllows]

/-- A completed mode is checked on the actual ordered return occurrences.
This readout is not a pre-execution cardinality oracle or an accelerator
admission rule. The existing source/cardinality compiler owns that contract. -/
def observeMode {State Answer Stable Retry : Type} (mode : CallingConvention)
    (state : Snapshot (WorkOccurrence State) (Produced Answer Stable Retry × List Nat) Nat) :
    ModeReadout Answer Stable Retry :=
  if state.search.frontier.isEmpty then
    let outcomes := (publication state).map Prod.fst
    match successfulValues outcomes with
    | none => .faulted outcomes
    | some values => if checkMode mode values.length then .ready values else .refused values
  else .pending

theorem completed_mode_readout {State Answer Stable Retry : Type} (mode : CallingConvention)
    (state : Snapshot (WorkOccurrence State) (Produced Answer Stable Retry × List Nat) Nat)
    (values : List Answer) (ready : observeMode mode state = .ready values) :
    state.search.frontier = [] ∧ ConventionAllows mode values.length ∧
      (publication state).map Prod.fst = values.map Produced.value := by
  unfold observeMode at ready
  split at ready
  · rename_i complete
    cases observed : successfulValues ((publication state).map Prod.fst) with
    | none => simp [observed] at ready
    | some actual =>
        simp only [observed] at ready
        split at ready
        · cases ready
          exact ⟨List.isEmpty_iff.mp complete, (checkMode_iff _ _).mp (by assumption),
            (successfulValues_iff _ _).mp observed⟩
        · cases ready
  · cases ready

theorem unfinished_mode_refused {State Answer Stable Retry : Type} (mode : CallingConvention)
    (state : Snapshot (WorkOccurrence State) (Produced Answer Stable Retry × List Nat) Nat)
    (pending : state.search.frontier ≠ []) : observeMode mode state = .pending := by
  simp [observeMode, List.isEmpty_iff, pending]

theorem mode_readout_representation (mode : CallingConvention) (state : RState) :
    observeMode mode state = observeMode mode (project keepReceipts state) := by
  simp [observeMode, publication, project, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapState, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapMemory, Mettapedia.GSLT.Core.BranchingTemporal.Snapshot.mapNodes,
    Emission.mapOrigin, List.map_map, Function.comp_def]


/-- All finite controlled executions compare, with complete snapshots on
both sides. The local list equality also gives no invention from represented
inputs, rather than only existence of some matching final answer. -/
theorem run_representation (fuel : Nat) (state : RState) :
    project keepReceipts (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (sourceSystem primitive) (controller _ _) fuel state) =
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (nativeSystem primitive) (controller _ _) fuel (project keepReceipts state) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [Mettapedia.GSLT.Core.InferenceControl.Snapshot.run]
      exact (tick_representation primitive keepReceipts _).trans (congrArg (nativeTick primitive) ih)

theorem run_mode_readout (fuel : Nat) (mode : CallingConvention) (state : RState) :
    observeMode mode (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (sourceSystem primitive) (controller _ _) fuel state) =
      observeMode mode (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (nativeSystem primitive) (controller _ _) fuel (project keepReceipts state)) := by
  rw [← run_representation primitive keepReceipts]
  exact mode_readout_representation keepReceipts mode _

/-- Only an actual `emit` control requests the external effect handler. A
cached value, data, ordinary force and an administrative local step do not
silently reissue that request. -/
def signal : Control (PolarizedNeedMachine.Local Head Operation Effect StableFault NativeFault m)
    (PolarizedNeedMachine.Resume Head Operation Effect m)
    (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault
    (PolarizedNeedMachine.Fault NativeFault) → Option Effect
  | .run (.evaluate ⟨_, _, _, .emit effect _, _, _, _⟩ _) _ => some effect
  | _ => none

def sourceSignal (state : RState) : Option Effect :=
  state.search.frontier.head?.bind (fun node => signal node.state.control)

def implementationSignal (state : IState) : Option Effect :=
  state.search.frontier.head?.bind (fun node => signal node.state.control)

theorem signal_representation (state : RState) :
    sourceSignal state = implementationSignal (project keepReceipts state) := by
  change state.search.frontier.head?.bind (fun node => signal node.state.control) =
    (state.search.frontier.map (projectNode keepReceipts)).head?.bind
      (fun node => signal node.state.control)
  cases state.search.frontier <;> rfl

namespace OwnData

open _root_.CategoryTheory
open Mettapedia.Machines
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport

variable {DataWorld Entry : Type} {width : Nat} [Category.{0} DataWorld]
  (authority : IndexedAuthority.{0, 0, 0} DataWorld)

/-- Execution currency and historical consulted reads have separate jobs.
A selected shared-data handler updates only live currency after its own
accepted write. It never repairs historical premises of a query. -/
structure Context where
  live : Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.State authority Entry width
  currency : OrderedDependencyStore.ReadStamp width
  pastReads : List (OrderedDependencyStore.ReadStamp width)

inductive Refused where
  | stale | admission | write
  deriving DecidableEq, Repr

variable (required : OrderedDependencyStore.Action Entry width →
    (world : DataWorld) → authority.Fibre world)
  (needed : (world : DataWorld) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority)
    (action : OrderedDependencyStore.Action Entry width),
    Decidable (FrameUpdate point.authority (required action point.world))]
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]
  (interpret : Effect → OrderedDependencyStore.Action Entry width)

/-- One handler entrance, using the existing current-authority store
primitive. Denial does not advance the Need source. Positive own work installs
its actual reached store and renews execution currency at the same reader;
past query stamps and the current authority point remain unchanged. This is
the selected shared-data interpretation, not automatic branch independence. -/
def step {State : Type} (turn : State → State) (effect : State → Option Effect)
    (state : State × Context authority (Entry := Entry) (width := width)) :
    (State × Context authority (Entry := Entry) (width := width)) × Except Refused Unit :=
  if OrderedDependencyStore.checkRead state.2.live.store state.2.currency then
    if FrameUpdate state.2.live.point.authority (needed state.2.live.point.world) then
      match effect state.1 with
      | none => ((turn state.1, state.2), .ok ())
      | some event =>
          match Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.step authority required state.2.live
              (.write (interpret event)) with
          | (live, .ok ()) =>
              ((turn state.1, ⟨live,
                OrderedDependencyStore.readStamp live.store state.2.currency.reader,
                state.2.pastReads⟩), .ok ())
          | (_, .error _) => (state, .error .write)
    else (state, .error .admission)
  else (state, .error .stale)

/-- Rich source and receipt-policy implementation interpret their own actual
control. The handler primitive is shared; the two Need turns are independent
and related by the proved local representation. -/
theorem step_representation (state : RState)
    (context : Context authority (Entry := Entry) (width := width)) :
    let before := step authority required needed interpret (sourceTick primitive) sourceSignal (state, context)
    let after := step authority required needed interpret (nativeTick primitive) implementationSignal
      (project keepReceipts state, context)
    ((project keepReceipts before.1.1, before.1.2), before.2) = after := by
  dsimp only
  unfold step
  rw [← signal_representation keepReceipts state]
  split
  · split
    · cases observed : sourceSignal state with
      | none => simp only [tick_representation]
      | some event =>
          simp only
          cases performed : Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.step authority required context.live
              (.write (interpret event)) with
          | mk live reply =>
              cases reply with
              | ok unitValue => cases unitValue; simp only [tick_representation]
              | error fault => rfl
    · rfl
  · rfl

theorem stale_keeps_the_whole_call {State : Type} (turn : State → State)
    (effect : State → Option Effect) (state : State × Context authority (Entry := Entry) (width := width))
    (stale : OrderedDependencyStore.checkRead state.2.live.store state.2.currency = false) :
    step authority required needed interpret turn effect state = (state, .error .stale) := by
  simp only [step, stale, Bool.false_eq_true, ↓reduceIte]

theorem revoked_keeps_the_whole_call {State : Type} (turn : State → State)
    (effect : State → Option Effect) (state : State × Context authority (Entry := Entry) (width := width))
    (current : OrderedDependencyStore.checkRead state.2.live.store state.2.currency = true)
    (denied : ¬ FrameUpdate state.2.live.point.authority (needed state.2.live.point.world)) :
    step authority required needed interpret turn effect state = (state, .error .admission) := by
  simp only [step, current, ↓reduceIte, denied]

theorem own_write_advances_currency {State : Type} (turn : State → State)
    (effect : State → Option Effect) (state : State × Context authority (Entry := Entry) (width := width))
    (event : Effect) (selected : effect state.1 = some event)
    (current : OrderedDependencyStore.checkRead state.2.live.store state.2.currency = true)
    (enabled : FrameUpdate state.2.live.point.authority (needed state.2.live.point.world))
    (allowed : FrameUpdate state.2.live.point.authority (required (interpret event) state.2.live.point.world)) :
    let live := {state.2.live with store := OrderedDependencyStore.step state.2.live.store (interpret event)}
    step authority required needed interpret turn effect state =
      ((turn state.1, ⟨live, OrderedDependencyStore.readStamp live.store state.2.currency.reader,
        state.2.pastReads⟩), .ok ()) := by
  dsimp only
  simp only [step, if_pos current, if_pos enabled, selected]
  rw [Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.own_write_uses_current_store authority required _ _ allowed]

/-- Admission reads only the selected request and its current context. It
does not execute a source turn to discover whether permission is available. -/
def gate {State : Type} (effect : State → Option Effect)
    (state : State × Context authority (Entry := Entry) (width := width)) : Except Refused Unit :=
  if OrderedDependencyStore.checkRead state.2.live.store state.2.currency then
    if FrameUpdate state.2.live.point.authority (needed state.2.live.point.world) then
      match effect state.1 with
      | none => .ok ()
      | some event =>
          if FrameUpdate state.2.live.point.authority (required (interpret event) state.2.live.point.world)
          then .ok () else .error .write
    else .error .admission
  else .error .stale

/-- The separately computed gate agrees with the actual primitive's status;
this follows from that primitive's successful/denied write branches. -/
theorem step_status {State : Type} (turn : State → State) (effect : State → Option Effect)
    (state : State × Context authority (Entry := Entry) (width := width)) :
    (step authority required needed interpret turn effect state).2 =
      gate authority required needed interpret effect state := by
  unfold step gate
  split
  · split
    · cases effect state.1 with
      | none => rfl
      | some event =>
          by_cases allowed : FrameUpdate state.2.live.point.authority
              (required (interpret event) state.2.live.point.world)
          · simp only [Cursor.ReadOnlyQuery.OwnWrite.step, if_pos allowed]
          · simp only [Cursor.ReadOnlyQuery.OwnWrite.step, if_neg allowed]
    · rfl
  · rfl

namespace Invocation

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Machines.Cursor

local notation "Answers" => Result (Head := Head) (Operation := Operation) (Effect := Effect)
  (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat

/-- The established polling protocol retains either the exact unfinished
source or a newly produced occurrence. The indexed gate below keeps refusal
separate from ordinary suspension. -/
def sourceProvider : Cursor.Provider (NativeControlCursor.protocol Answers) where
  State _ _ := RState × Context authority (Entry := Entry) (width := width)
  step state _ := match state.1.search.frontier with
    | [] => ⟨.done, state⟩
    | node :: _ =>
        let moved := step authority required needed interpret (sourceTick primitive) sourceSignal state
        match moved.2 with
        | .error _ => ⟨.suspend (), state⟩
        | .ok () => match (sourceSystem primitive).emit node with
          | none => ⟨.suspend (), moved.1⟩
          | some answer => ⟨.yield answer (), moved.1⟩

def targetProvider : Cursor.Provider (NativeControlCursor.protocol Answers) where
  State _ _ := IState × Context authority (Entry := Entry) (width := width)
  step state _ := match state.1.search.frontier with
    | [] => ⟨.done, state⟩
    | node :: _ =>
        let moved := step authority required needed interpret (nativeTick primitive) implementationSignal state
        match moved.2 with
        | .error _ => ⟨.suspend (), state⟩
        | .ok () => match (nativeSystem primitive).emit node with
          | none => ⟨.suspend (), moved.1⟩
          | some answer => ⟨.yield answer (), moved.1⟩

def representation : Cursor.Hom (sourceProvider primitive authority required needed interpret)
    (targetProvider primitive authority required needed interpret) where
  map state := (project keepReceipts state.1, state.2)
  step state request := by
    rcases state with ⟨source, context⟩
    have compared := step_representation primitive keepReceipts authority required needed interpret source context
    cases selected : source.search.frontier with
    | nil =>
        have frontier : (project keepReceipts source).search.frontier = [] := by
          change source.search.frontier.map (projectNode keepReceipts) = []
          rw [selected]
          rfl
        simp only [sourceProvider, targetProvider, selected, frontier]
    | cons node rest =>
        have frontier : (project keepReceipts source).search.frontier =
            projectNode keepReceipts node :: rest.map (projectNode keepReceipts) := by
          change source.search.frontier.map (projectNode keepReceipts) = _
          rw [selected]
          rfl
        simp only [sourceProvider, targetProvider, selected, frontier]
        cases moved : step authority required needed interpret (sourceTick primitive) sourceSignal
            (source, context) with
        | mk reached reply =>
            rcases reached with ⟨next, current⟩
            have targetMoved : step authority required needed interpret (nativeTick primitive) implementationSignal
                (project keepReceipts source, context) = ((project keepReceipts next, current), reply) := by
              simpa only [moved] using compared.symm
            simp only [targetMoved]
            cases reply with
            | error reason => rfl
            | ok unitValue =>
                cases unitValue
                rw [← local_emit primitive keepReceipts node]
                cases (sourceSystem primitive).emit node <;> rfl

def sourceGate : OperationCostProtocol.Indexed.Gate (Denied := Refused)
    (sourceProvider primitive authority required needed interpret) := fun state _ =>
  gate authority required needed interpret sourceSignal state

def targetGate : OperationCostProtocol.Indexed.Gate (Denied := Refused)
    (targetProvider primitive authority required needed interpret) := fun state _ =>
  gate authority required needed interpret implementationSignal state

theorem gate_representation {base index : Unit}
    (state : RState × Context authority (Entry := Entry) (width := width)) (request : Unit) :
    sourceGate primitive authority required needed interpret (base := base) (index := index) state request =
      targetGate primitive authority required needed interpret (base := base) (index := index)
        (project keepReceipts state.1, state.2) request := by
  dsimp only [sourceGate, targetGate, gate]
  rw [← signal_representation keepReceipts state.1]

/-- The invoice is a declared logical polling observation. A Need transition,
callback body, allocation and native instruction retain their own accounts;
one poll is not a bound on all of their costs. -/
def profile : OperationCostProtocol.Profile :=
  ⟨"rich-need-poll-v1", [("quantum", some .quantum)], .steps, none, .refused⟩

def pollInvoice (origin ordinal : Nat) : List OperationCostProtocol.Event :=
  [(Nat.pair origin ordinal, ⟨origin, ordinal, .quantum, 1⟩)]

def sourceInvoice (origin : Nat) : OperationCostProtocol.Indexed.Invoice
    (sourceProvider primitive authority required needed interpret) := fun state _ =>
  pollInvoice origin state.1.memory

def targetInvoice (origin : Nat) : OperationCostProtocol.Indexed.Invoice
    (targetProvider primitive authority required needed interpret) := fun state _ =>
  pollInvoice origin state.1.memory

/-- The actual providers, current gate and logical invoice instantiate the
existing indexed handler theorem. Profile/replay agreement concerns the
declared poll, while the nonidentity state map preserves the complete Need
control, heap, occurrence frontier and chosen receipt observer. -/
def handler (origin : Nat) : OperationCostProtocol.Indexed.HandlerHom
    (sourceProvider primitive authority required needed interpret)
    (targetProvider primitive authority required needed interpret)
    (sourceGate primitive authority required needed interpret)
    (targetGate primitive authority required needed interpret)
    (fun _ => profile) (fun _ => profile) (fun _ => false) (fun _ => false)
    (sourceInvoice primitive authority required needed interpret origin)
    (targetInvoice primitive authority required needed interpret origin) where
  representation := representation primitive keepReceipts authority required needed interpret
  gate_eq state request := gate_representation primitive keepReceipts authority required needed interpret state request
  profiles_eq _ := rfl
  replay_eq _ := rfl
  invoice_eq _ _ := rfl

/- The shared `HandlerHom.run`, `resume`, `mapOutcome_account` and
`publishCheckedGrant` laws apply directly to this constructed handler. The
component realization above separately derives full retained source runs. -/


end Invocation

end OwnData


namespace Examples

open PolarizedNeed (Computation Value)
open PolarizedNeedMachine
abbrev ExampleCode := Computation Nat Unit Nat 0 0 0
abbrev ExampleWorld := NeedWorld Nat Unit Nat Unit Unit 0
abbrev ExampleValue := RuntimeValue Nat Unit Nat 0
abbrev ExampleResult := Outcome Nat Unit Nat Unit Unit 0
abbrev ExampleState := Source (Head := Nat) (Operation := Unit) (Effect := Nat)
  (StableFault := Unit) (NativeFault := Unit) (m := 0)

abbrev examplePrimitive := PolarizedNeedMachineExamples.primitive

def emptyWorld : ExampleWorld := ⟨0, [], .empty, .empty, 0, 0⟩

def closedLoad (code : ExampleCode) : Load Nat Unit Nat Unit Unit 0 :=
  ⟨emptyWorld, ⟨0, 0, 0, code, ids, Fin.elim0, Fin.elim0⟩⟩

def execute (input : Load Nat Unit Nat Unit Unit 0) : ExampleState :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.run (sourceSystem examplePrimitive)
    (controller _ _) 80 (loadSource input)

/-- The observation keeps each answer's own final world. In particular an
exported thunk's next invocation receives the previous invocation's world;
this is not a replay from the old immutable image. -/
def returned (state : ExampleState) : Option (ExampleValue × ExampleWorld) :=
  state.search.events.findSome? fun event => match event.value.1 with
    | .value (.returned value) => some (value, event.origin.state.world)
    | _ => none

def effectCount (world : ExampleWorld) : Nat :=
  world.receipts.nodes.countP (fun node => match node.payload with | .effect 7 => true | _ => false)

def nativeAnswers (state : ExampleState) : List (Produced PolarizedNeedMachineExamples.AnswerView
    Unit (Fault Unit)) :=
  state.search.events.map (fun event => PolarizedNeedMachineExamples.outcomeView event.value.1)

def made {n v k : Nat} : Computation Nat Unit Nat n v k :=
  .emit 7 (.returnValue (.native (.head 42)))

/-- Construction allocates one shared producer and exports a callable that
retains its reference twice. The producer is not forced during export. -/
def exportShared : ExampleCode :=
  .letNeed made (.returnValue (.thunk (.nativeLambda
    (.sequenceSigma (.forceNeed 0) (.forceNeed 0)))))

def invoke (value : ExampleValue) (world : ExampleWorld) : Load Nat Unit Nat Unit Unit 0 :=
  ⟨world, ⟨0, 1, 0, .nativeApply (.forceThunk (.variable 0)) (.head 0),
    ids, Fin.cases value Fin.elim0, Fin.elim0⟩⟩

def exported := returned (execute (closedLoad exportShared))

def useTwice : Option (List (Produced PolarizedNeedMachineExamples.AnswerView Unit (Fault Unit)) ×
    List (Produced PolarizedNeedMachineExamples.AnswerView Unit (Fault Unit)) × Nat × Nat) := do
  let (value, captured) ← exported
  let first := execute (invoke value (captured.fork 17))
  let (_, live) ← returned first
  let second := execute (invoke value live)
  let (_, final) ← returned second
  return (nativeAnswers first, nativeAnswers second, effectCount final, final.path.headD 99)

theorem exporting_keeps_one_unforced_cell :
    exported.isSome = true ∧
      exported.map (fun pair => (effectCount pair.2, pair.2.nextCell)) = some (0, 1) := by
  decide +kernel

theorem exported_shared_producer_runs_once_in_the_threaded_receiver_world :
    useTwice = some
      ([.value (.native (.pair (.head 42) (.head 42)))],
       [.value (.native (.pair (.head 42) (.head 42)))], 1, 17) := by
  decide +kernel

/-- Replacing the captured cell by two copies of its origin gives the same
answers, but repeats the paid effect on every use. This is a separating
serialization control, not an alternative representation claimed lawful. -/
def copiedOrigin : ExampleValue :=
  .thunk (.nativeLambda (.sequenceSigma made made)) ids Fin.elim0 Fin.elim0

def useCopiedTwice := do
  let first := execute (invoke copiedOrigin emptyWorld)
  let (_, live) ← returned first
  let second := execute (invoke copiedOrigin live)
  let (_, final) ← returned second
  return (nativeAnswers first, nativeAnswers second, effectCount final)

theorem origin_copy_preserves_answers_but_duplicates_production :
    useCopiedTwice = some
      ([.value (.native (.pair (.head 42) (.head 42)))],
       [.value (.native (.pair (.head 42) (.head 42)))], 4) := by
  decide +kernel

def wrongWorld := do
  let (value, _) ← exported
  let call := execute (invoke value { emptyWorld with lineage := 9 })
  return (nativeAnswers call, call.search.frontier.isEmpty)

theorem a_callable_does_not_manufacture_its_missing_cell_world :
    wrongWorld = some
      ([.retryableFault (.outOfScope ⟨0, [], 0, 0⟩)], true) := by
  decide +kernel

def forkTwice := do
  let (value, captured) ← exported
  let first := execute (invoke value captured)
  let second := execute (invoke value captured)
  let (_, left) ← returned first
  let (_, right) ← returned second
  return (effectCount left, effectCount right)

theorem restarting_the_old_image_is_a_different_pair_of_worlds :
    forkTwice = some (1, 1) := by
  decide +kernel

/-- The producer contains a native variable whose lexical value is retained
by its cell. Closing that variable is not an allocation of a second cell. -/
def exportCapturedNative : Computation Nat Unit Nat 1 0 0 :=
  .letNeed (.emit 7 (.returnValue (.native (.var 0))))
    (.returnValue (.thunk (.nativeLambda (.sequenceSigma (.forceNeed 0) (.forceNeed 0)))))

def capturedNative := returned (execute
  ⟨emptyWorld, ⟨1, 0, 0, exportCapturedNative, Fin.cases (.head 65) Fin.elim0, Fin.elim0, Fin.elim0⟩⟩)

def firstCapturedCell : ExampleValue → Option CellId
  | .thunk (k := k) _ _ _ needs => if present : 0 < k then some (needs ⟨0, present⟩) else none
  | _ => none

/-- The first use is a direct authenticated reference supplied by the
receiver; the next two references are inside the exported callable. -/
def invokeMixed (value : ExampleValue) (cell : CellId) (world : ExampleWorld) :
    Load Nat Unit Nat Unit Unit 0 :=
  ⟨world, ⟨0, 1, 1,
    .sequenceSigma (.forceNeed 0) (.nativeApply (.forceThunk (.variable 0)) (.head 0)),
    ids, Fin.cases value Fin.elim0, Fin.cases cell Fin.elim0⟩⟩

def mixedCaptured := do
  let (value, world) ← capturedNative
  let cell ← firstCapturedCell value
  let state := execute (invokeMixed value cell (world.fork 23))
  let (_, after) ← returned state
  return (nativeAnswers state, effectCount after, after.path.headD 99)

theorem direct_and_captured_cell_aliases_share_the_open_native_origin :
    mixedCaptured = some
      ([.value (.native (.pair (.head 65) (.pair (.head 65) (.head 65))))], 1, 23) := by
  decide +kernel

/-- Reconstructing the closed origin and allocating it anew preserves the
printed answers but breaks the original direct/captured alias. This models
the distinction an implementation's image decoder must preserve, without
claiming that any particular storage encoding implements this conversion. -/
def recopyCaptured := do
  let (value, world) ← capturedNative
  let cell ← firstCapturedCell value
  let copied := execute
    { closedLoad (.letNeed (.emit 7 (.returnValue (.native (.head 65))))
        (.returnValue (.thunk (.nativeLambda (.sequenceSigma (.forceNeed 0) (.forceNeed 0))))))
      with world := world }
  let (fresh, reached) ← returned copied
  let state := execute (invokeMixed fresh cell (reached.fork 23))
  let (_, after) ← returned state
  return (nativeAnswers state, effectCount after)

theorem closing_the_origin_and_allocating_again_breaks_mixed_aliasing :
    recopyCaptured = some
      ([.value (.native (.pair (.head 65) (.pair (.head 65) (.head 65))))], 2) := by
  decide +kernel

def separatelyAllocated := do
  let captured := execute (closedLoad
    (.letNeed made (.letNeed made
      (.returnValue (.thunk (.nativeLambda (.sequenceSigma (.forceNeed 0) (.forceNeed 1))))))))
  let (value, world) ← returned captured
  let state := execute (invoke value world)
  let (_, after) ← returned state
  return (nativeAnswers state, effectCount after)

theorem equal_producer_text_does_not_merge_distinct_allocated_cells :
    separatelyAllocated = some
      ([.value (.native (.pair (.head 42) (.head 42)))], 2) := by
  decide +kernel

/-- Native Data may contain application syntax. Only an explicit thunk
eliminator executes code; passing it through a value lambda leaves it inert. -/
def callableData : ExampleCode :=
  .valueApply (.valueLambda (.returnValue (.variable 0)))
    (.native (.app (.head 13) (.head 42)))

theorem callable_data_is_retained_as_a_value :
    nativeAnswers (execute (closedLoad callableData)) =
      [.value (.native (.app (.head 13) (.head 42)))] := by
  decide +kernel

def duplicate : ExampleCode :=
  .choose (.returnValue (.native (.head 42))) (.returnValue (.native (.head 42)))

theorem actual_duplicate_branches_keep_distinct_paths :
    ((execute (closedLoad duplicate)).search.events.map (fun event => event.value.2)).length = 2 ∧
      ((execute (closedLoad duplicate)).search.events.map (fun event => event.value.2))[0]? ≠
        ((execute (closedLoad duplicate)).search.events.map (fun event => event.value.2))[1]? ∧
      nativeAnswers (execute (closedLoad duplicate)) =
        [.value (.native (.head 42)), .value (.native (.head 42))] := by
  decide +kernel

/-- The actual unfinished source cannot publish its provisional prefix as a
closed direct, optional or producer observation. -/
theorem zero_work_retains_an_unfinished_mode :
    observeMode .producer (loadSource (closedLoad duplicate)) = .pending ∧
      observeMode .direct (loadSource (closedLoad duplicate)) = .pending := by
  constructor <;> rfl

/-- A finite test observer records the status and its occurrence count. The
principal mode theorem above retains the actual values and fault payloads. -/
def modeSize {Answer Stable Retry : Type} : ModeReadout Answer Stable Retry → Nat × Nat
  | .pending => (0, 0)
  | .faulted outcomes => (1, outcomes.length)
  | .refused values => (2, values.length)
  | .ready values => (3, values.length)

/-- All four existing ABI cardinality modes observe the same completed return
collection, and refuse the cardinality that collection does not justify. -/
theorem four_modes_observe_actual_completed_occurrences :
    modeSize (observeMode .producer (execute (closedLoad duplicate))) = (3, 2) ∧
    modeSize (observeMode .nonemptyProducer (execute (closedLoad duplicate))) = (3, 2) ∧
    modeSize (observeMode .direct (execute (closedLoad duplicate))) = (2, 2) ∧
    modeSize (observeMode .optional (execute (closedLoad duplicate))) = (2, 2) := by
  decide +kernel

theorem one_real_return_is_admitted_by_every_cardinality_mode :
    modeSize (observeMode .direct (execute (closedLoad (.returnValue (.native (.head 42)))))) = (3, 1) ∧
    modeSize (observeMode .optional (execute (closedLoad (.returnValue (.native (.head 42)))))) = (3, 1) ∧
    modeSize (observeMode .producer (execute (closedLoad (.returnValue (.native (.head 42)))))) = (3, 1) ∧
    modeSize (observeMode .nonemptyProducer (execute (closedLoad (.returnValue (.native (.head 42)))))) = (3, 1) := by
  decide +kernel

theorem a_raw_polarity_fault_is_not_an_empty_success :
    modeSize (observeMode .optional (execute (closedLoad PolarizedNeedMachineExamples.badForce))) =
      (1, 1) := by
  decide +kernel

namespace OwnData

open _root_.CategoryTheory
open Mettapedia.Machines
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

abbrev fixture := Cursor.ReadOnlyQuery.OwnWrite.Controls.source
abbrev required := Cursor.ReadOnlyQuery.OwnWrite.Controls.requirement

def needed (_ : Bool) : Access := .consume

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (required change point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

def context : RetainedInvocation.OwnData.Context revocationWorlds (Entry := Nat) (width := 3) :=
  ⟨fixture, OrderedDependencyStore.readStamp fixture.store 0,
    [OrderedDependencyStore.readStamp fixture.store 0]⟩

def start : ExampleState := loadSource (closedLoad made)

def act (_ : Nat) : OrderedDependencyStore.Action Nat 3 := .append 0 [11]

def enter (current : RetainedInvocation.OwnData.Context revocationWorlds
    (Entry := Nat) (width := 3)) :=
  RetainedInvocation.OwnData.step revocationWorlds required needed act
    (sourceTick examplePrimitive) sourceSignal (start, current)

/-- The real effect control advances once in the receiving context. Its
own write refreshes live currency but leaves the captured query premise old. -/
theorem own_publication_renews_only_execution_currency :
    (enter context).2 = .ok () ∧
      OrderedDependencyStore.query (enter context).1.2.live.store 0 = [7, 7, 11] ∧
      OrderedDependencyStore.checkRead (enter context).1.2.live.store
        (enter context).1.2.currency = true ∧
      (enter context).1.2.pastReads = context.pastReads ∧
      OrderedDependencyStore.checkRead (enter context).1.2.live.store
        (OrderedDependencyStore.readStamp fixture.store 0) = false ∧
      (enter context).1.2.live.point = fixture.point ∧
      (enter context).1.1.memory = 1 ∧
      (participants (enter context).1.1).map (fun machine => effectCount machine.world) = [1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩ <;> decide +kernel

def revoked := { context with live := { fixture with
  point := Cursor.ReadOnlyQuery.OwnWrite.Controls.revoked } }

theorem a_current_stamp_cannot_replace_revoked_permission :
    OrderedDependencyStore.checkRead revoked.live.store revoked.currency = true ∧
      (enter revoked).2 = .error .admission ∧
      (enter revoked).1.1.memory = 0 ∧
      OrderedDependencyStore.query (enter revoked).1.2.live.store 0 = [7, 7] := by
  decide +kernel

def interfered := { context with live := { fixture with
  store := OrderedDependencyStore.appendOwn fixture.store 0 [99] } }

theorem external_write_does_not_heal_a_stale_query_or_restart_the_source :
    (enter interfered).2 = .error .stale ∧
      (enter interfered).1.1.memory = 0 ∧
      (enter interfered).1.2.currency = context.currency ∧
      (enter interfered).1.2.pastReads = context.pastReads ∧
      OrderedDependencyStore.query (enter interfered).1.2.live.store 0 = [7, 7, 99] := by
  decide +kernel

namespace Invocation

open Mettapedia.GSLT.LanguageDef

abbrev raw := RetainedInvocation.OwnData.Invocation.sourceProvider
  examplePrimitive revocationWorlds required needed act
abbrev guard : OperationCostProtocol.Indexed.Gate (Denied := RetainedInvocation.OwnData.Refused) raw :=
  RetainedInvocation.OwnData.Invocation.sourceGate
  examplePrimitive revocationWorlds required needed act
abbrev invoice : OperationCostProtocol.Indexed.Invoice raw :=
  RetainedInvocation.OwnData.Invocation.sourceInvoice
  examplePrimitive revocationWorlds required needed act 91

def profiles : {_base _index : Unit} → Unit → OperationCostProtocol.Profile :=
  fun _ => RetainedInvocation.OwnData.Invocation.profile
def replay : {_base _index : Unit} → Unit → Bool := fun _ => false
abbrev reader := NativeControlCursor.client (ExampleResult × List Nat)
def notice : OperationCostProtocol.Indexed.Notice
    (NativeControlCursor.protocol (ExampleResult × List Nat)) RetainedInvocation.OwnData.Refused :=
  fun _ _ => none
abbrev decorated := OperationCostProtocol.Indexed.provider raw guard (@profiles) (@replay) invoice
abbrev Saved := Nat × OperationCostProtocol.Indexed.Outcome raw guard (@profiles) (@replay) invoice reader notice ()

def packet (budget : Nat) (current : RetainedInvocation.OwnData.Context revocationWorlds
    (Entry := Nat) (width := 3)) :
    Cursor.Packet decorated (OperationCostProtocol.Indexed.client reader notice) () :=
  ⟨(), .inl (.pulling []), (start, current),
    OperationCostProtocol.initial RetainedInvocation.OwnData.Invocation.profile budget⟩

def advance (budget fuel : Nat) (current : RetainedInvocation.OwnData.Context revocationWorlds
    (Entry := Nat) (width := 3)) : Saved :=
  OperationCostProtocol.Indexed.run raw guard (@profiles) (@replay) invoice reader notice fuel (packet budget current)

def resume (fuel : Nat) (saved : Saved) : Saved :=
  OperationCostProtocol.Indexed.resume raw guard (@profiles) (@replay) invoice reader notice fuel saved

def stateOf (saved : Saved) : ExampleState × RetainedInvocation.OwnData.Context revocationWorlds
    (Entry := Nat) (width := 3) := match saved.2 with
  | .paused packet => packet.2.2.1
  | .done result => result.2.2.1

def accountOf (saved : Saved) : OperationCostProtocol.Account :=
  OperationCostProtocol.Indexed.accountOf raw guard (@profiles) (@replay) invoice reader notice saved.2

def refusal (saved : Saved) : Option (OperationCostProtocol.Indexed.Reason RetainedInvocation.OwnData.Refused) :=
  match saved.2 with
  | .done ⟨_, .inr (reason, _), _⟩ => some reason
  | _ => none

def completedValues (saved : Saved) :
    Option (List (Produced PolarizedNeedMachineExamples.AnswerView Unit (Fault Unit))) :=
  match saved.2 with
  | .done ⟨_, .inl values, _⟩ =>
      some (values.map (fun answer => PolarizedNeedMachineExamples.outcomeView answer.1))
  | _ => none

/-- These fixture updates supply a new current authority point or store; they
retain the client, Need state, currency, historical reads and paid account.
They are not operations by which the program creates its own authority. -/
def supplyPoint (point : IndexedAuthority.Point revocationWorlds) (saved : Saved) : Saved :=
  (saved.1, Cursor.Outcome.mapState (OperationCostProtocol.Indexed.client reader notice)
    (source := decorated) (target := decorated)
    (fun state => ((state.1.1, { state.1.2 with live := { state.1.2.live with point := point } }), state.2)) saved.2)

def externalWrite (saved : Saved) : Saved :=
  (saved.1, Cursor.Outcome.mapState (OperationCostProtocol.Indexed.client reader notice)
    (source := decorated) (target := decorated)
    (fun state => ((state.1.1, { state.1.2 with live := { state.1.2.live with
      store := OrderedDependencyStore.appendOwn state.1.2.live.store 0 [99] } }), state.2)) saved.2)

def paid := advance 12 1 context
def revokedPaid := resume 2 (supplyPoint Cursor.ReadOnlyQuery.OwnWrite.Controls.revoked paid)
def interferedPaid := resume 2 (externalWrite paid)
def recovered : Saved :=
  let restored := supplyPoint fixture.point revokedPaid
  resume 80 (restored.1, OperationCostProtocol.Indexed.retry raw guard (@profiles) (@replay) invoice reader notice restored.2)

theorem an_accepted_poll_keeps_its_exact_paid_and_unfinished_context :
    paid.1 = 1 ∧ (accountOf paid).remaining = 11 ∧ (accountOf paid).calls = 1 ∧
      (accountOf paid).events = RetainedInvocation.OwnData.Invocation.pollInvoice 91 0 ∧
      (stateOf paid).1.memory = 1 ∧ completedValues paid = none ∧
      OrderedDependencyStore.query (stateOf paid).2.live.store 0 = [7, 7, 11] := by
  decide +kernel

theorem revocation_stops_new_reliance_without_refunding_or_repeating_the_paid_prefix :
    refusal revokedPaid = some (.inl .admission) ∧ revokedPaid.1 = 1 ∧
      accountOf revokedPaid = accountOf paid ∧ (stateOf revokedPaid).1.memory = 1 ∧
      OrderedDependencyStore.query (stateOf revokedPaid).2.live.store 0 = [7, 7, 11] := by
  decide +kernel

theorem external_change_refuses_the_same_paid_continuation :
    refusal interferedPaid = some (.inl .stale) ∧ interferedPaid.1 = 1 ∧
      accountOf interferedPaid = accountOf paid ∧ (stateOf interferedPaid).1.memory = 1 ∧
      (stateOf interferedPaid).2.pastReads = context.pastReads ∧
      OrderedDependencyStore.query (stateOf interferedPaid).2.live.store 0 = [7, 7, 11, 99] := by
  decide +kernel

theorem a_fresh_current_grant_resumes_after_the_actual_effect :
    completedValues recovered = some [.value (.native (.head 42))] ∧
      OrderedDependencyStore.query (stateOf recovered).2.live.store 0 = [7, 7, 11] ∧
      (participants (stateOf recovered).1).map (fun machine => effectCount machine.world) = [1] ∧
      OrderedDependencyStore.checkRead (stateOf recovered).2.live.store
        (OrderedDependencyStore.readStamp fixture.store 0) = false := by
  decide +kernel

theorem missing_poll_credit_refuses_before_the_real_source_effect :
    refusal (advance 0 2 context) = some (.inr .budget) ∧
      (advance 0 2 context).1 = 0 ∧ (stateOf (advance 0 2 context)).1.memory = 0 ∧
      OrderedDependencyStore.query (stateOf (advance 0 2 context)).2.live.store 0 = [7, 7] := by
  decide +kernel

end Invocation

end OwnData

end Examples

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.RetainedInvocation

/-! ## Graded observations of the same retained invocation

The readers below inspect the actual selected control, heap and ordered
alternatives. Source firing, cache production, cache delivery, outward return
and the logical polling invoice are separate observations. Optional causal
recording is not an input to the cache-role or source-firing reader.
-/
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.RetainedInvocation.GradedHistory

open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.Languages.MeTTa.PrimeCandidates
open Mettapedia.Algebra.SharedCoefficientLedger

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

local notation "RState" => Source (Head := Head) (Operation := Operation) (Effect := Effect)
  (StableFault := StableFault) (NativeFault := NativeFault) (m := m)
local notation "IState" => Target (Head := Head) (Operation := Operation) (Effect := Effect)
  (StableFault := StableFault) (NativeFault := NativeFault) (m := m)
local notation "Answer" => PolarizedNeedMachine.Answer Head Operation Effect m
local notation "Failure" => PolarizedNeedMachine.Fault NativeFault
local notation "Returned" => Result (Head := Head) (Operation := Operation) (Effect := Effect)
  (StableFault := StableFault) (NativeFault := NativeFault) (m := m)

structure Inspection (Head Operation Effect StableFault NativeFault : Type) (m : Nat) where
  occurrence : List Nat
  firings : List (CellId × PolarizedNeedMachine.Rule)
  completed : Option (NeedCacheLaws.CompletedObservation
    (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault (PolarizedNeedMachine.Fault NativeFault))
  effect : Option Effect
  returned : Option (Result (Head := Head) (Operation := Operation) (Effect := Effect)
    (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat)

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
  (keepReceipts : Bool)

def sourceInspection (state : RState) : Option (Inspection Head Operation Effect StableFault NativeFault m) :=
  state.search.frontier.head?.map fun node =>
    ⟨node.trace,
      NeedLocalSteps.firingChoices (PolarizedNeedMachine.reference primitive)
        node.state.world.heap node.state.control,
      NeedCacheLaws.completedObservation? node.state.world.heap node.state.control,
      signal node.state.control, (sourceSystem primitive).emit node⟩

def targetInspection (state : IState) : Option (Inspection Head Operation Effect StableFault NativeFault m) :=
  state.search.frontier.head?.map fun node =>
    ⟨node.trace,
      NeedLocalSteps.firingChoices (PolarizedNeedMachine.reference primitive)
        node.state.world.heap node.state.control,
      NeedCacheLaws.completedObservation? node.state.world.heap node.state.control,
      signal node.state.control, (nativeSystem primitive).emit node⟩

/-- The independent readers agree on every representation, including receipt
absence. Their returned payloads retain the actual captured values and paths. -/
theorem inspection_projection (state : RState) :
    sourceInspection primitive state = targetInspection primitive (project keepReceipts state) := by
  change state.search.frontier.head?.map _ =
    (state.search.frontier.map (projectNode keepReceipts)).head?.map _
  cases selected : state.search.frontier with
  | nil => rfl
  | cons node rest =>
      simp only [List.head?_cons, List.map_cons, Option.map_some]
      rw [local_emit primitive keepReceipts node]
      rfl

/-- This declared inventory code is injective. Compatibility with native
session/cell fields is an explicit decoder obligation, not numeric identity
between a pointer and a natural number. -/
def nativeCell (cell : CellId) : NativeReceiptCorrespondence.NativeCell :=
  ⟨cell.lineage, Nat.pair (Encodable.encode cell.birth) (Nat.pair cell.slot cell.generation)⟩

theorem nativeCell_injective : Function.Injective nativeCell := by
  intro left right same
  have lineage := congrArg NativeReceiptCorrespondence.NativeCell.needSession same
  have body := congrArg NativeReceiptCorrespondence.NativeCell.cell same
  obtain ⟨birth, tail⟩ := Nat.pair_eq_pair.mp body
  obtain ⟨slot, generation⟩ := Nat.pair_eq_pair.mp tail
  have paths := Encodable.encode_injective birth
  cases left
  cases right
  simp_all [nativeCell]

def applicationNumber (cell : CellId) : Nat :=
  Nat.pair (nativeCell cell).needSession (nativeCell cell).cell

theorem applicationNumber_injective : Function.Injective applicationNumber := by
  intro left right same
  obtain ⟨session, cell⟩ := Nat.pair_eq_pair.mp same
  apply nativeCell_injective
  exact congrArg₂ NativeReceiptCorrespondence.NativeCell.mk session cell

def ruleNumber : PolarizedNeedMachine.Rule → Nat
  | .entry => 0
  | .left => 1
  | .right => 2

def eventNumber (origin ordinal position : Nat) : Nat :=
  Nat.pair origin (Nat.pair ordinal position)

theorem eventNumber_injective {origin ordinal position otherOrigin otherOrdinal otherPosition : Nat}
    (same : eventNumber origin ordinal position = eventNumber otherOrigin otherOrdinal otherPosition) :
    origin = otherOrigin ∧ ordinal = otherOrdinal ∧ position = otherPosition := by
  obtain ⟨origin, rest⟩ := Nat.pair_eq_pair.mp same
  exact ⟨origin, Nat.pair_eq_pair.mp rest⟩

variable {Observation V : Type}
  (observe : Result (Head := Head) (Operation := Operation) (Effect := Effect)
    (StableFault := StableFault) (NativeFault := NativeFault) (m := m) → Observation)

/-- An actual source alternative gets an evaluation record and a firing
record. Their distinct IDs retain physical alternative position. Cache
observations and effects occupy separate following positions. Outward return
is retained in `Inspection`; it is not forged as a cell observation. -/
def nativeEvents (origin ordinal : Nat)
    (note : Inspection Head Operation Effect StableFault NativeFault m) :
    List (NativeReceiptCorrespondence.NativeEvent Observation Effect) :=
  note.firings.zipIdx.flatMap (fun (firing, position) =>
    [⟨eventNumber origin ordinal (2 * position), .evaluateCell (nativeCell firing.1) none⟩,
     ⟨eventNumber origin ordinal (2 * position + 1),
       .useEquation (applicationNumber firing.1) (ruleNumber firing.2)⟩]) ++
    (note.completed.map fun completed =>
      ⟨eventNumber origin ordinal (2 * note.firings.length),
        .observeCell (nativeCell completed.cell) none (observe completed.outcome)⟩).toList ++
    (note.effect.map fun effect =>
      ⟨eventNumber origin ordinal (2 * note.firings.length + 1), .effect effect⟩).toList

/-- A source-factor readout consumes all three actual native fields: physical
occurrence, dynamic application dependency and declared coefficient. It does
not combine equal coefficients or charge a cached delivery as a new firing. -/
def nativeFactor? (coefficient : Nat → Nat → V)
    (event : NativeReceiptCorrespondence.NativeEvent Observation Effect) :
    Option (Factor Nat Nat V) :=
  match event.payload with
  | .useEquation application rule => some ⟨event.eventId, application, coefficient application rule⟩
  | _ => none

/-- Independently read the actual ordered generic Need alternatives. A
coefficient may be zero or a noncommutative word; none is filtered here.
`entry/left/right` include sequencing cells and are not authored equation row
IDs. This protocol-wide account records inspected successor choices; a
branch-local answer valuation must additionally select that branch's choices. -/
def sourceFactors (coefficient : Nat → Nat → V) (origin ordinal : Nat)
    (note : Inspection Head Operation Effect StableFault NativeFault m) : Ledger Nat Nat V :=
  note.firings.zipIdx.map fun (firing, position) =>
    ⟨eventNumber origin ordinal (2 * position + 1), applicationNumber firing.1,
      coefficient (applicationNumber firing.1) (ruleNumber firing.2)⟩

/-- Source factor records are the exact decoding of the emitted local block,
not an assumed agreement between complete runs. Cache/effect records cannot
silently introduce an additional source coefficient. -/
theorem native_factor_block (coefficient : Nat → Nat → V) (origin ordinal : Nat)
    (note : Inspection Head Operation Effect StableFault NativeFault m) :
    (nativeEvents observe origin ordinal note).filterMap (nativeFactor? coefficient) =
      sourceFactors coefficient origin ordinal note := by
  simp only [nativeEvents, List.filterMap_append, List.filterMap_flatMap,
    sourceFactors, List.filterMap_cons, nativeFactor?, List.filterMap_nil]
  cases note.completed <;> cases note.effect <;>
    simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
      List.filterMap_cons, List.filterMap_nil, nativeFactor?, List.append_nil,
      ← List.map_eq_flatMap]

/-- Distinct physical alternative positions have distinct factor IDs,
regardless of equal rules, equal values or equal coefficients. -/
theorem sourceFactors_valid (coefficient : Nat → Nat → V) (origin ordinal : Nat)
    (note : Inspection Head Operation Effect StableFault NativeFault m) :
    Valid (sourceFactors coefficient origin ordinal note) := by
  have injective : Function.Injective (fun position => eventNumber origin ordinal (2 * position + 1)) := by
    intro left right same
    have positions := (eventNumber_injective same).2.2
    omega
  have distinct := (List.nodup_map_iff injective).mpr (List.nodup_zipIdx_map_snd note.firings)
  simpa only [Valid, identities, sourceFactors, List.map_map, Function.comp_def] using distinct

/-- Different selected source ordinals cannot alias a physical factor,
even when both alternatives refer to the same dynamic application. -/
theorem sourceFactors_disjoint (coefficient : Nat → Nat → V) (origin first second : Nat)
    (left right : Inspection Head Operation Effect StableFault NativeFault m)
    (different : first ≠ second) :
    (identities (sourceFactors coefficient origin first left)).Disjoint
      (identities (sourceFactors coefficient origin second right)) := by
  rw [List.disjoint_left]
  intro identity inLeft inRight
  obtain ⟨leftFactor, leftMember, leftId⟩ := List.mem_map.mp inLeft
  obtain ⟨rightFactor, rightMember, rightId⟩ := List.mem_map.mp inRight
  obtain ⟨⟨leftFiring, leftPosition⟩, _, leftEq⟩ := List.mem_map.mp leftMember
  obtain ⟨⟨rightFiring, rightPosition⟩, _, rightEq⟩ := List.mem_map.mp rightMember
  subst leftFactor rightFactor
  have same := leftId.trans rightId.symm
  exact different (eventNumber_injective same).2.1

/-- Actual independent source blocks append without losing zero factors.
Their chronological interpretation therefore uses ordinary monoid product. -/
theorem sourceFactors_append_valid (coefficient : Nat → Nat → V) (origin first second : Nat)
    (left right : Inspection Head Operation Effect StableFault NativeFault m)
    (different : first ≠ second) :
    Valid (sourceFactors coefficient origin first left ++ sourceFactors coefficient origin second right) := by
  simp only [Valid, identities, List.map_append]
  refine List.nodup_append.mpr
    ⟨sourceFactors_valid _ _ _ _, sourceFactors_valid _ _ _ _, ?_⟩
  intro firstFactor inLeft secondFactor inRight same
  subst secondFactor
  exact List.disjoint_left.mp (sourceFactors_disjoint coefficient origin first second left right different)
    inLeft inRight

inductive View (Head Operation Effect StableFault NativeFault : Type) (m : Nat) where
  | inert
  | finish
  | refused (reason : Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Indexed.Reason OwnData.Refused)
  | paid (ordinal : Nat) (invoice : List Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Event)
      (selected : Option (Inspection Head Operation Effect StableFault NativeFault m))

namespace Invocation

open _root_.CategoryTheory
open Mettapedia.Machines
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Machines.Cursor

variable {DataWorld Entry : Type} {width : Nat} [Category.{0} DataWorld]
  (authority : IndexedAuthority.{0, 0, 0} DataWorld)
  (required : OrderedDependencyStore.Action Entry width → (world : DataWorld) → authority.Fibre world)
  (needed : (world : DataWorld) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Entry width),
    Decidable (FrameUpdate point.authority (required action point.world))]
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]
  (interpret : Effect → OrderedDependencyStore.Action Entry width)

local notation "RawSource" => OwnData.Invocation.sourceProvider primitive authority required needed interpret
local notation "RawTarget" => OwnData.Invocation.targetProvider primitive authority required needed interpret
local notation "SourceGate" => OwnData.Invocation.sourceGate primitive authority required needed interpret
local notation "TargetGate" => OwnData.Invocation.targetGate primitive authority required needed interpret
local notation "Profiles" => (fun _ => OwnData.Invocation.profile)
local notation "NoReplay" => (fun _ => false)
local notation "SourceInvoice" => OwnData.Invocation.sourceInvoice primitive authority required needed interpret
local notation "TargetInvoice" => OwnData.Invocation.targetInvoice primitive authority required needed interpret

def sourceProvider (origin : Nat) : Cursor.Provider
    (OperationCostProtocol.Indexed.protocol
      (NativeControlCursor.protocol (Returned × List Nat)) OwnData.Refused) :=
  OperationCostProtocol.Indexed.provider RawSource SourceGate Profiles NoReplay (SourceInvoice origin)

def targetProvider (origin : Nat) : Cursor.Provider
    (OperationCostProtocol.Indexed.protocol
      (NativeControlCursor.protocol (Returned × List Nat)) OwnData.Refused) :=
  OperationCostProtocol.Indexed.provider RawTarget TargetGate Profiles NoReplay (TargetInvoice origin)

def sourceCharge (origin : Nat) : Cursor.Charge (sourceProvider primitive authority required needed interpret origin) :=
  OperationCostProtocol.Indexed.charge RawSource SourceGate Profiles NoReplay (SourceInvoice origin)

def targetCharge (origin : Nat) : Cursor.Charge (targetProvider primitive authority required needed interpret origin) :=
  OperationCostProtocol.Indexed.charge RawTarget TargetGate Profiles NoReplay (TargetInvoice origin)

variable {Return : Unit → Unit → Type}
  (reader : Cursor.Client
    (P := NativeControlCursor.protocol
      (Result (Head := Head) (Operation := Operation) (Effect := Effect)
        (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat))
    (Return := Return))
  (notice : OperationCostProtocol.Indexed.Notice
    (NativeControlCursor.protocol
      (Result (Head := Head) (Operation := Operation) (Effect := Effect)
        (StableFault := StableFault) (NativeFault := NativeFault) (m := m) × List Nat)) OwnData.Refused)

local notation "Client" => OperationCostProtocol.Indexed.client reader notice

def sourceView (origin : Nat) {base : Unit} :
    Cursor.Outcome (sourceProvider primitive authority required needed interpret origin) Client base →
      View Head Operation Effect StableFault NativeFault m
  | .done _ => .inert
  | .paused ⟨index, control, state⟩ =>
      match (Client).str base index control with
      | ⟨.inl _, _⟩ => .finish
      | ⟨.inr request, _⟩ =>
          match OperationCostProtocol.Indexed.admit RawSource SourceGate Profiles NoReplay
              (SourceInvoice origin) state.1 request state.2 with
          | .error reason => .refused reason
          | .ok _ => .paid state.1.1.memory (SourceInvoice origin state.1 request)
              (sourceInspection primitive state.1.1)

def targetView (origin : Nat) {base : Unit} :
    Cursor.Outcome (targetProvider primitive authority required needed interpret origin) Client base →
      View Head Operation Effect StableFault NativeFault m
  | .done _ => .inert
  | .paused ⟨index, control, state⟩ =>
      match (Client).str base index control with
      | ⟨.inl _, _⟩ => .finish
      | ⟨.inr request, _⟩ =>
          match OperationCostProtocol.Indexed.admit RawTarget TargetGate Profiles NoReplay
              (TargetInvoice origin) state.1 request state.2 with
          | .error reason => .refused reason
          | .ok _ => .paid state.1.1.memory (TargetInvoice origin state.1 request)
              (targetInspection primitive state.1.1)

/-- The current gate, paid invoice and concrete operational observation agree
at every actual retained boundary. Finished client inspection is separate
from an original provider request and from a completed source answer. -/
theorem view_projection (origin : Nat) {base : Unit}
    (before : Cursor.Outcome (sourceProvider primitive authority required needed interpret origin) Client base) :
    sourceView primitive authority required needed interpret reader notice origin before =
      targetView primitive authority required needed interpret reader notice origin
        ((OwnData.Invocation.handler primitive keepReceipts authority required needed interpret origin).lift.outcome
          Client before) := by
  cases before with
  | done result => rfl
  | paused packet =>
      rcases packet with ⟨index, control, ⟨source, context⟩, account⟩
      change (match (Client).str base index control with
        | ⟨.inl _, _⟩ => (View.finish : View Head Operation Effect StableFault NativeFault m)
        | ⟨.inr request, _⟩ => _) =
        (match (Client).str base index control with
        | ⟨.inl _, _⟩ => (View.finish : View Head Operation Effect StableFault NativeFault m)
        | ⟨.inr request, _⟩ => _)
      cases exposed : (Client).str base index control with
      | mk shape children =>
          cases shape with
          | inl answer => rfl
          | inr request =>
              simp only [OperationCostProtocol.Indexed.HandlerHom.lift]
              erw [← (OwnData.Invocation.handler primitive keepReceipts authority required needed interpret origin).admit_eq]
              cases accepted : OperationCostProtocol.Indexed.admit RawSource SourceGate Profiles NoReplay
                  (SourceInvoice origin) (source, context) request account with
              | error reason => rfl
              | ok paid =>
                  change View.paid source.memory
                      (OwnData.Invocation.pollInvoice origin source.memory) (sourceInspection primitive source) =
                    View.paid source.memory
                      (OwnData.Invocation.pollInvoice origin source.memory)
                      (targetInspection primitive (project keepReceipts source))
                  exact congrArg (View.paid source.memory
                    (OwnData.Invocation.pollInvoice origin source.memory))
                    (inspection_projection primitive keepReceipts source)

open Mettapedia.GSLT.ProofRelevant
open Mettapedia.OSLF.Binding.RewriteEventHistory
open Mettapedia.Effects

local notation "Source" => sourceProvider primitive authority required needed interpret
local notation "Target" => targetProvider primitive authority required needed interpret
local notation "SourceView" => sourceView primitive authority required needed interpret reader notice
local notation "TargetView" => targetView primitive authority required needed interpret reader notice
local notation "Realization" => OwnData.Invocation.handler primitive keepReceipts authority required needed interpret

/-- Chronological protocol events retain their full invocation endpoints.
Only the passive local observation is projected to a coefficient. -/
def sourceAccount {Coefficient : Type} [Monoid Coefficient] (origin : Nat) (base : Unit)
    (value : View Head Operation Effect StableFault NativeFault m → Coefficient) :
    RunAccount (HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base))
      Coefficient :=
  NativeControlCursor.ProtocolHistory.eventAccount (Source origin) Client base
    (fun {before _} _ => value (SourceView origin before))

def targetAccount {Coefficient : Type} [Monoid Coefficient] (origin : Nat) (base : Unit)
    (value : View Head Operation Effect StableFault NativeFault m → Coefficient) :
    RunAccount (HistoryCategory (NativeControlCursor.ProtocolHistory.system (Target origin) Client base))
      Coefficient :=
  NativeControlCursor.ProtocolHistory.eventAccount (Target origin) Client base
    (fun {before _} _ => value (TargetView origin before))

/-- The constructed local operational reader calibrates every ordered
account, including noncommutative ones, on the actual handler lift. No
agreement of complete runs is an input. -/
theorem account_transport {Coefficient : Type} [Monoid Coefficient]
    (origin : Nat) (base : Unit)
    (value : View Head Operation Effect StableFault NativeFault m → Coefficient) :
    (targetAccount primitive authority required needed interpret reader notice origin base value).comap
        (NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories =
      sourceAccount primitive authority required needed interpret reader notice origin base value := by
  have transported := NativeControlCursor.ProtocolHistory.hom_account_preserved Client
    (Realization origin).lift base
    (fun {before _} _ => value (SourceView origin before))
    (fun {before _} _ => value (TargetView origin before)) (MonoidHom.id _) (by
      intro before after event
      exact congrArg value (view_projection primitive keepReceipts authority required needed
        interpret reader notice origin before).symm)
  ext before after run
  exact congrArg (fun account => account.of run) transported

/-- Read one actual paid turn as its ordered source firing block. A refused
request, a finishing client inspection and exhaustion create no factor. -/
def factorBlock (coefficient : Nat → Nat → V) (origin : Nat) :
    View Head Operation Effect StableFault NativeFault m → FreeMonoid (Factor Nat Nat V)
  | .paid ordinal _ (some note) => FreeMonoid.ofList (sourceFactors coefficient origin ordinal note)
  | _ => 1

/-- Native events and source factors use the same local, authenticated
selection. This decoder retains the physical firing ID and dependency. -/
def nativeBlock (origin : Nat) : View Head Operation Effect StableFault NativeFault m →
    FreeMonoid (NativeReceiptCorrespondence.NativeEvent Observation Effect)
  | .paid ordinal _ (some note) => FreeMonoid.ofList (nativeEvents observe origin ordinal note)
  | _ => 1

/-- Production and delivery are read from the actual control/cache role,
not inferred from repeated equal payloads in a lossy native event log. -/
def cacheBlock : View Head Operation Effect StableFault NativeFault m →
    FreeMonoid (CellId × NeedCacheLaws.CompletedReceiptKind)
  | .paid _ _ (some note) => FreeMonoid.ofList
      (note.completed.map fun completed => (completed.cell, completed.kind)).toList
  | _ => 1

/-- User effects are observed separately from polling and coefficient work. -/
def effectBlock : View Head Operation Effect StableFault NativeFault m → FreeMonoid Effect
  | .paid _ _ (some note) => FreeMonoid.ofList note.effect.toList
  | _ => 1

/-- Outward occurrences retain the returned runtime payload and source path,
including two equal answers from distinct branches. -/
def returnBlock : View Head Operation Effect StableFault NativeFault m → FreeMonoid (Returned × List Nat)
  | .paid _ _ (some note) => FreeMonoid.ofList note.returned.toList
  | _ => 1

/-- Logical invoice work is a separate account from source factors and
from cache delivery. No physical-cost identity is asserted here. -/
def invoiceValue : View Head Operation Effect StableFault NativeFault m → Multiplicative Nat
  | .paid _ invoice _ => Multiplicative.ofAdd (OperationCostProtocol.work invoice)
  | _ => 1

/-- The actual independently supplied provider meter agrees locally with
its successful invoice and charges a refused boundary zero. -/
theorem source_invoice_event (origin : Nat) {base : Unit}
    {before after : Cursor.Outcome (Source origin) Client base}
    (event : NativeControlCursor.ProtocolHistory.Event (Source origin) Client base before after) :
    invoiceValue (SourceView origin before) = Multiplicative.ofAdd
      (NativeControlCursor.ProtocolHistory.eventExpense (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) event) := by
  cases event with
  | finish control state answer children exposed =>
      simp only [sourceView, exposed, invoiceValue, NativeControlCursor.ProtocolHistory.eventExpense]
      rfl
  | request control state request children exposed =>
      simp only [sourceView, exposed, sourceCharge, OperationCostProtocol.Indexed.charge,
        NativeControlCursor.ProtocolHistory.eventExpense]
      cases accepted : OperationCostProtocol.Indexed.admit RawSource SourceGate Profiles NoReplay
          (SourceInvoice origin) state.1 request state.2 <;> rfl

/-- Invoice reconstruction is proved from actual request/finish events;
it is not another definition of the provider account. -/
theorem invoice_account (origin : Nat) (base : Unit) :
    sourceAccount primitive authority required needed interpret reader notice origin base invoiceValue =
      NativeControlCursor.ProtocolHistory.providerAccount (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) base := by
  unfold sourceAccount NativeControlCursor.ProtocolHistory.providerAccount
  congr 1
  funext before after event
  exact source_invoice_event primitive authority required needed interpret reader notice origin event

/-- The account of the actual generated bounded history is the paid poll
invoice. Source firing counts and recorded payload sizes remain distinct. -/
theorem invoice_advance (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base) :
    Multiplicative.toAdd
      ((sourceAccount primitive authority required needed interpret reader notice origin base invoiceValue).of
        (NativeControlCursor.ProtocolHistory.advanceHistory (Source origin) Client
          (sourceCharge primitive authority required needed interpret origin) allowance packet)) =
      (Cursor.advance (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) allowance packet).1 := by
  rw [invoice_account]
  exact NativeControlCursor.ProtocolHistory.advanceHistory_paid _ _ _ _ _

/-- Paid work before the pause is retained; the invoice of the exact suffix
is added once when the same invocation resumes. -/
theorem invoice_resume (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base) :
    earlier.1 + Multiplicative.toAdd
      ((sourceAccount primitive authority required needed interpret reader notice origin base invoiceValue).of
        (NativeControlCursor.ProtocolHistory.resumeHistory (Source origin) Client
          (sourceCharge primitive authority required needed interpret origin) allowance earlier)) =
      (Cursor.resume (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) allowance earlier).1 := by
  rw [invoice_account]
  exact NativeControlCursor.ProtocolHistory.resumeHistory_paid _ _ _ _ _

/-- Project each occurrence-bearing native record to zero or one factor.
This homomorphism preserves concatenation without combining equal values. -/
def factorDecoder (coefficient : Nat → Nat → V) :
    FreeMonoid (NativeReceiptCorrespondence.NativeEvent Observation Effect) →*
      FreeMonoid (Factor Nat Nat V) where
  toFun events := FreeMonoid.ofList (events.toList.filterMap (nativeFactor? coefficient))
  map_one' := rfl
  map_mul' first second := by
    simp only [FreeMonoid.toList_mul, List.filterMap_append, FreeMonoid.ofList_append]

/-- The printed native block decoder and actual source-factor reader agree
on each phase. A zero coefficient is retained as a physical factor. -/
theorem decode_native_block (coefficient : Nat → Nat → V) (origin : Nat)
    (view : View Head Operation Effect StableFault NativeFault m) :
    factorDecoder coefficient (nativeBlock observe origin view) = factorBlock coefficient origin view := by
  cases view with
  | inert => rfl
  | finish => rfl
  | refused reason => rfl
  | paid ordinal invoice note =>
      cases note with
      | none => rfl
      | some note =>
          change FreeMonoid.ofList _ = FreeMonoid.ofList _
          exact congrArg FreeMonoid.ofList (native_factor_block observe coefficient origin ordinal note)

/-- On the same complete endpoint-typed history, block decoding recovers
all source factors in order. The history may end unfinished or refused. -/
theorem history_factor_decoding (coefficient : Nat → Nat → V) (origin : Nat) (base : Unit) :
    (sourceAccount primitive authority required needed interpret reader notice origin base
      (nativeBlock observe origin)).map (factorDecoder coefficient) =
    sourceAccount primitive authority required needed interpret reader notice origin base
      (factorBlock coefficient origin) := by
  ext before after history
  change factorDecoder coefficient
      ((sourceAccount primitive authority required needed interpret reader notice origin base
        (nativeBlock observe origin)).of history) =
    (sourceAccount primitive authority required needed interpret reader notice origin base
      (factorBlock coefficient origin)).of history
  refine Paths.induction
    (P := fun route => factorDecoder coefficient
      ((sourceAccount primitive authority required needed interpret reader notice origin base
        (nativeBlock observe origin)).of route) =
      (sourceAccount primitive authority required needed interpret reader notice origin base
        (factorBlock coefficient origin)).of route) ?_ ?_ history
  · intro state
    simp only [RunAccount.of_id, map_one]
  · intro before middle after past event ih
    rw [RunAccount.of_comp, map_mul, ih, RunAccount.of_comp]
    congr 1
    change factorDecoder coefficient
        ((sourceAccount primitive authority required needed interpret reader notice origin base
          (nativeBlock observe origin)).of event.toPath) =
      (sourceAccount primitive authority required needed interpret reader notice origin base
        (factorBlock coefficient origin)).of event.toPath
    rw [sourceAccount, NativeControlCursor.ProtocolHistory.eventAccount_generator,
      sourceAccount, NativeControlCursor.ProtocolHistory.eventAccount_generator]
    exact decode_native_block observe coefficient origin _

/-- The chronological invocation word retains refusals, finishing
inspections, paid invoices and operational roles as distinct letters. -/
def sourceWord (origin : Nat) (base : Unit) :=
  sourceAccount primitive authority required needed interpret reader notice origin base FreeMonoid.of

def targetWord (origin : Nat) (base : Unit) :=
  targetAccount primitive authority required needed interpret reader notice origin base FreeMonoid.of

/-- Recording and weighted valuation use the same actual event order. -/
theorem word_concat (origin : Nat) (base : Unit)
    {before middle after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (first : before ⟶ middle) (second : middle ⟶ after) :
    ((sourceWord primitive authority required needed interpret reader notice origin base).of (first ≫ second)).toList =
      ((sourceWord primitive authority required needed interpret reader notice origin base).of first).toList ++
      ((sourceWord primitive authority required needed interpret reader notice origin base).of second).toList := by
  rw [RunAccount.of_comp, FreeMonoid.toList_mul]

/-- Optional recording receives the actual history only when enabled. The
unrecorded branch never evaluates its history thunk. Recording does not
participate in the operational transition or its invoice. -/
def recordSuffix (origin : Nat) (base : Unit)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (record : Option (Recording.Prefix (View Head Operation Effect StableFault NativeFault m)))
    (history : Unit → (before ⟶ after)) :
    Option (Recording.Prefix (View Head Operation Effect StableFault NativeFault m)) :=
  record.map fun record => record.append
    ((sourceWord primitive authority required needed interpret reader notice origin base).of (history ())).toList

/-- An enabled prefix composes over the real midpoint, including its
complete account and retained Need world. Capacity is not replenished. -/
theorem recording_concat (origin : Nat) (base : Unit)
    {before middle after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (record : Recording.Prefix (View Head Operation Effect StableFault NativeFault m))
    (first : before ⟶ middle) (second : middle ⟶ after) :
    recordSuffix primitive authority required needed interpret reader notice origin base
      (some record) (fun _ => first ≫ second) =
    recordSuffix primitive authority required needed interpret reader notice origin base
      (recordSuffix primitive authority required needed interpret reader notice origin base
        (some record) (fun _ => first)) (fun _ => second) := by
  simp only [recordSuffix, Option.map_some, word_concat, Recording.Prefix.append_append]

/-- History transport preserves the whole recorded suffix, not just its
length or a commutative aggregate. -/
theorem recording_transport (origin : Nat) (base : Unit)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (record : Recording.Prefix (View Head Operation Effect StableFault NativeFault m))
    (history : before ⟶ after) :
    record.append
        ((sourceWord primitive authority required needed interpret reader notice origin base).of history).toList =
      record.append
        ((targetWord primitive authority required needed interpret reader notice origin base).of
          ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map
            history)).toList := by
  have law := account_transport primitive keepReceipts authority required needed interpret reader notice
    origin base FreeMonoid.of
  exact congrArg (fun account => record.append (account.of history).toList) law.symm

/-- A complete readout is exactly the actual interval since recording was
started, provided the bounded prefix retained every event. -/
theorem recording_complete (origin capacity : Nat) (base : Unit)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (history : before ⟶ after) :
    ((Recording.Prefix.initial capacity).append
      ((sourceWord primitive authority required needed interpret reader notice origin base).of history).toList).complete? =
        some ((sourceWord primitive authority required needed interpret reader notice origin base).of history).toList ↔
      ((sourceWord primitive authority required needed interpret reader notice origin base).of history).toList.length ≤
        capacity :=
  Recording.Prefix.complete_iff _ _

/-- Refusing a partial native observation does not erase an occurrence from
an otherwise complete readout. Retry is an execution decision outside this
passive projection. -/
theorem recording_refuses_missing_payload (origin : Nat) (base : Unit)
    {Payload : Type}
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (decode : View Head Operation Effect StableFault NativeFault m → Option Payload)
    (record : Recording.Prefix (View Head Operation Effect StableFault NativeFault m))
    (history : before ⟶ after) (event : View Head Operation Effect StableFault NativeFault m)
    (member : event ∈ (record.append
      ((sourceWord primitive authority required needed interpret reader notice origin base).of history).toList).items)
    (refused : decode event = none) :
    Recording.Prefix.project? decode (record.append
      ((sourceWord primitive authority required needed interpret reader notice origin base).of history).toList) = none :=
  Recording.Prefix.project?_refused _ _ _ member refused

/-- A provider realization preserves and reflects replay qualification for
any declared local observation monoid. This is not permission to repeat a
native effect: current publication remains governed by its own gate. -/
theorem qualified_replay_transport {Coefficient : Type} [Monoid Coefficient]
    (origin : Nat) (base : Unit)
    (value : View Head Operation Effect StableFault NativeFault m → Coefficient)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (first second : before ⟶ after) :
    Mettapedia.GSLT.Distinction.LevelAccounts.QualifiedReplay
        (sourceAccount primitive authority required needed interpret reader notice origin base value) first second ↔
      Mettapedia.GSLT.Distinction.LevelAccounts.QualifiedReplay
        (targetAccount primitive authority required needed interpret reader notice origin base value)
        ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map first)
        ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map second) := by
  have law := account_transport primitive keepReceipts authority required needed interpret reader notice
    origin base value
  have left := congrArg (fun account => account.of first) law
  have right := congrArg (fun account => account.of second) law
  change _ = _ ↔ _ = _
  rw [show (targetAccount primitive authority required needed interpret reader notice origin base value).of
      ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map first) = _
    from left,
    show (targetAccount primitive authority required needed interpret reader notice origin base value).of
      ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map second) = _
    from right]

/-- Enabled and disabled observation delegate to the same cursor. The
optional buffer is outside the semantic packet, invoice and Need world. -/
def observedAdvance (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base)
    (record : Option (Recording.Prefix (View Head Operation Effect StableFault NativeFault m))) :=
  (Cursor.advance (Source origin) Client
      (sourceCharge primitive authority required needed interpret origin) allowance packet,
    recordSuffix primitive authority required needed interpret reader notice origin base record
      (fun _ => NativeControlCursor.ProtocolHistory.advanceHistory (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) allowance packet))

/-- Forgetting recording recovers the actual full cursor result, including
its retained continuation, current context and paid account. -/
theorem observed_advance_erasure (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base)
    (record : Option (Recording.Prefix (View Head Operation Effect StableFault NativeFault m))) :
    (observedAdvance primitive authority required needed interpret reader notice origin allowance packet record).1 =
      Cursor.advance (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) allowance packet := rfl

/-- Disabled observation neither reads a history nor changes the operational
outcome. This is a construction law; it is not a compiled-C cost claim. -/
theorem disabled_recording (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base) :
    observedAdvance primitive authority required needed interpret reader notice origin allowance packet none =
      (Cursor.advance (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) allowance packet, none) := rfl

/-- The resumed observer starts at the exact retained packet. An already
finished outcome supplies the empty suffix and cannot repeat source work. -/
def observedResume (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base)
    (record : Option (Recording.Prefix (View Head Operation Effect StableFault NativeFault m))) :=
  (Cursor.resume (Source origin) Client
      (sourceCharge primitive authority required needed interpret origin) allowance earlier,
    recordSuffix primitive authority required needed interpret reader notice origin base record
      (fun _ => NativeControlCursor.ProtocolHistory.resumeHistory (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) allowance earlier))

/-- Stopping retains the exact captured prefix; later execution continues
with recording disabled. Forgetting may then discard that saved prefix,
without changing either invocation outcome. -/
def stopAndResume (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base)
    (record : Recording.Prefix (View Head Operation Effect StableFault NativeFault m)) :=
  ((observedResume primitive authority required needed interpret reader notice origin allowance earlier none).1,
    record)

/-- Stopping at a paid boundary is conservative for execution and retains
the historical interval as it was, rather than calling the suffix complete. -/
theorem stop_preserves_prefix (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base)
    (record : Recording.Prefix (View Head Operation Effect StableFault NativeFault m)) :
    stopAndResume primitive authority required needed interpret reader notice origin allowance earlier record =
      (Cursor.resume (Source origin) Client
        (sourceCharge primitive authority required needed interpret origin) allowance earlier, record) := rfl

/-- The maintained ABI client determines how much of this actual provider
is consumed. Producer hands over its unpolled state; nonempty retains the
first yielded occurrence and residual; scalar modes await exhaustion. -/
def modePacket (mode : SourceProducerCardinality.CallingConvention) (origin : Nat)
    (state : RState × OwnData.Context authority (Entry := Entry) (width := width))
    (account : OperationCostProtocol.Account) :
    Cursor.Packet (Source origin)
      (OperationCostProtocol.Indexed.client
        (SourceProducerCardinality.CallingModes.client mode (Returned × List Nat)) notice) () :=
  ⟨(), .inl (if mode = .producer then .finished [] else .pulling []), state, account⟩

/-- This is a completion readout of the selected maintained ABI client,
not a pre-call cardinality oracle. A paused call stays unavailable and an
Indexed refusal stays separate from an empty optional result. -/
def modeReadout (mode : SourceProducerCardinality.CallingConvention)
    (isFault : Returned × List Nat → Bool)
    {provider : Cursor.Provider
      (OperationCostProtocol.Indexed.protocol (NativeControlCursor.protocol (Returned × List Nat)) OwnData.Refused)} :
    Cursor.Outcome provider
      (OperationCostProtocol.Indexed.client
        (SourceProducerCardinality.CallingModes.client mode (Returned × List Nat)) notice) () →
    Option (Except (OperationCostProtocol.Indexed.Reason OwnData.Refused)
      (SourceProducerCardinality.CallingModes.Result (Returned × List Nat)))
  | .paused _ => none
  | .done ⟨(), .inr (reason, _), _⟩ => some (.error reason)
  | .done ⟨(), .inl rows, _⟩ => some (.ok (SourceProducerCardinality.CallingModes.decode mode isFault rows))

/-- Every actual calling-mode client commutes with this nonidentity rich
handler substitution. The bounded result retains full provider state; its
separate completion readout preserves faults, duplicates and incompatibility. -/
theorem mode_readout_transport (mode : SourceProducerCardinality.CallingConvention)
    (isFault : Returned × List Nat → Bool) (origin allowance : Nat)
    (state : RState × OwnData.Context authority (Entry := Entry) (width := width))
    (account : OperationCostProtocol.Account) :
    modeReadout notice mode isFault
      (Cursor.advance (Source origin)
        (OperationCostProtocol.Indexed.client
          (SourceProducerCardinality.CallingModes.client mode (Returned × List Nat)) notice)
        (sourceCharge primitive authority required needed interpret origin) allowance
        (modePacket primitive authority required needed interpret notice mode origin state account)).2 =
    modeReadout notice mode isFault
      (Cursor.advance (Target origin)
        (OperationCostProtocol.Indexed.client
          (SourceProducerCardinality.CallingModes.client mode (Returned × List Nat)) notice)
        (targetCharge primitive authority required needed interpret origin) allowance
        ((Realization origin).lift.packet _
          (modePacket primitive authority required needed interpret notice mode origin state account))).2 := by
  let client := OperationCostProtocol.Indexed.client
    (SourceProducerCardinality.CallingModes.client mode (Returned × List Nat)) notice
  have same := (Realization origin).lift.advance client
    (sourceCharge primitive authority required needed interpret origin)
    (targetCharge primitive authority required needed interpret origin) allowance
    (modePacket primitive authority required needed interpret notice mode origin state account)
  have observes : ∀ (outcome : Cursor.Outcome (Source origin) client ()),
      modeReadout notice mode isFault outcome =
        modeReadout notice mode isFault ((Realization origin).lift.outcome client outcome) := by
    intro outcome
    cases outcome with
    | paused packet => rfl
    | done result => rcases result with ⟨index, value, state⟩; cases index; cases value <;> rfl
  exact (observes _).trans (congrArg (modeReadout notice mode isFault) same)

end Invocation

namespace Examples

open _root_.CategoryTheory
open Mettapedia.Machines Mettapedia.GSLT.Contracts Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Logic.SeparationTransport Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeed


local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (action : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (RetainedInvocation.Examples.OwnData.required action point.world)) :=
  RetainedInvocation.Examples.OwnData.permissionDecision point action

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (RetainedInvocation.Examples.OwnData.needed point.world)) :=
  RetainedInvocation.Examples.OwnData.admissionDecision point

abbrev operationPrimitive := RetainedInvocation.Examples.examplePrimitive
abbrev interpret := RetainedInvocation.Examples.OwnData.act
abbrev Provider := Invocation.sourceProvider operationPrimitive revocationWorlds
  RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed interpret 91
abbrev TargetProvider := Invocation.targetProvider operationPrimitive revocationWorlds
  RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed interpret 91
abbrev notice : OperationCostProtocol.Indexed.Notice
    (NativeControlCursor.protocol (RetainedInvocation.Examples.ExampleResult × List Nat)) OwnData.Refused :=
  RetainedInvocation.Examples.OwnData.Invocation.notice
abbrev Reader := SourceProducerCardinality.CallingModes.client
  .direct (RetainedInvocation.Examples.ExampleResult × List Nat)
abbrev Client := OperationCostProtocol.Indexed.client Reader notice
abbrev Charge : Cursor.Charge Provider := Invocation.sourceCharge operationPrimitive revocationWorlds
  RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed interpret 91
abbrev Word := Invocation.sourceWord operationPrimitive revocationWorlds
  RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed interpret Reader notice 91 ()

/-- Values, faults and captured worlds remain in the real source; these
finite readouts only select observables for executable controls. -/
def packet (code : RetainedInvocation.Examples.ExampleCode) (budget : Nat := 200) : Cursor.Packet Provider Client () :=
  ⟨(), .inl (.pulling []),
    (loadSource (RetainedInvocation.Examples.closedLoad code), RetainedInvocation.Examples.OwnData.context),
    OperationCostProtocol.initial OwnData.Invocation.profile budget⟩

def run (code : RetainedInvocation.Examples.ExampleCode) (fuel : Nat := 100) :=
  Cursor.advance Provider Client Charge fuel (packet code)

def history (code : RetainedInvocation.Examples.ExampleCode) (fuel : Nat := 100) :=
  NativeControlCursor.ProtocolHistory.advanceHistory Provider Client Charge fuel (packet code)

def factors (coefficient : Nat → Nat → Nat) (code : RetainedInvocation.Examples.ExampleCode) (fuel : Nat := 100) :=
  ((Invocation.sourceAccount operationPrimitive revocationWorlds RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed
    interpret Reader notice 91 () (Invocation.factorBlock coefficient 91)).of (history code fuel)).toList

/-- This is the actual rich source used by the retained closure controls,
now consumed by the direct-mode invocation client and current-world handler. -/
def shared : RetainedInvocation.Examples.ExampleCode :=
  .letNeed RetainedInvocation.Examples.made (.sequenceSigma (.forceNeed 0) (.forceNeed 0))

def fresh : RetainedInvocation.Examples.ExampleCode :=
  .letNeed RetainedInvocation.Examples.made (.letNeed RetainedInvocation.Examples.made (.sequenceSigma (.forceNeed 0) (.forceNeed 1)))

/-- A zero semantic coefficient retains its physical source occurrence. -/
theorem zero_source_factor_is_not_filtered :
    (factors (fun _ _ => 0) shared).map Factor.coefficient = [0, 0] := by
  decide +kernel

/-- The sequencing wrapper itself has one generic Need entry. Beyond that
entry, a shared producer contributes once; independently allocated producers
contribute twice. These are Need choices, not authored C equation row IDs. -/
theorem shared_production_is_once_but_distinct_cells_are_not_merged :
    (factors (fun _ _ => 2) shared).map Factor.coefficient = [2, 2] ∧
      (factors (fun _ _ => 2) fresh).map Factor.coefficient = [2, 2, 2] ∧
      ((factors (fun _ _ => 2) fresh).map Factor.dependency).Nodup := by
  decide +kernel

/-- Equal coefficient values do not identify physical firing occurrences. -/
theorem actual_factor_ids_are_unique :
    Valid (factors (fun _ _ => 2) shared) ∧ Valid (factors (fun _ _ => 2) fresh) := by
  decide +kernel

/-- Reusing this actual source snapshot shares its existing factor. Appending
a copied description with the same physical ID is refused. -/
theorem actual_source_prefix_shares_but_copying_is_refused :
    merge? (factors (fun _ _ => 2) shared) (factors (fun _ _ => 2) shared) =
        some (factors (fun _ _ => 2) shared) ∧
      merge? (factors (fun _ _ => 2) shared ++ factors (fun _ _ => 2) shared)
        (factors (fun _ _ => 2) shared) = none := by
  decide +kernel

/-- A handler claims a production before running its callback. Re-entering
that same real source snapshot cannot claim it again. -/
theorem actual_scope_claim_prevents_recounting :
    let ledger : Scoped Nat Nat Nat Nat := ⟨factors (fun _ _ => 2) shared, fun _ => none⟩
    Scoped.selected 0 (Scoped.handle 0 41 ledger) = [] :=
  Scoped.selected_after_handle _ _ _

def cacheEvents (code : RetainedInvocation.Examples.ExampleCode) (fuel : Nat := 100) :=
  ((Invocation.sourceAccount operationPrimitive revocationWorlds RetainedInvocation.Examples.OwnData.required
    RetainedInvocation.Examples.OwnData.needed interpret Reader notice 91 () Invocation.cacheBlock).of
      (history code fuel)).toList

def effects (code : RetainedInvocation.Examples.ExampleCode) (fuel : Nat := 100) :=
  ((Invocation.sourceAccount operationPrimitive revocationWorlds RetainedInvocation.Examples.OwnData.required
    RetainedInvocation.Examples.OwnData.needed interpret Reader notice 91 () Invocation.effectBlock).of
      (history code fuel)).toList

/-- These roles belong to the same actual paid invocation. The sequencing
cell and shared producer complete, then the second force is a delivery. -/
theorem cache_delivery_does_not_create_a_new_production_or_effect :
    (cacheEvents shared).map Prod.snd = [.production, .production, .delivery] ∧
      effects shared = [7] ∧ effects fresh = [7, 7] ∧
      (run shared).1 = 20 := by
  decide +kernel

def noncommutative (code : RetainedInvocation.Examples.ExampleCode) : FreeMonoid Nat :=
  ((factors (fun application _ => application) code).map
    (fun factor => FreeMonoid.of factor.coefficient)).prod

/-- Equal aggregate work and an unchanged factor bag do not justify
reordering an actual source history's noncommutative interpretation. -/
theorem source_factor_order_is_observable :
    (noncommutative shared).toList = [16, 0] ∧
      (noncommutative shared).toList ≠ (noncommutative shared).toList.reverse ∧
      ((factors (fun application _ => application) shared).map Factor.coefficient).prod =
        ((factors (fun application _ => application) shared).map Factor.coefficient).reverse.prod := by
  decide +kernel

/-- A current-permission refusal is a distinct protocol event. It cannot
fire the source, create a coefficient or become an empty successful result. -/
theorem current_refusal_has_no_factors_or_effects :
    Invocation.sourceView operationPrimitive revocationWorlds RetainedInvocation.Examples.OwnData.required
      RetainedInvocation.Examples.OwnData.needed interpret Reader notice 91 (base := ())
      (.paused ⟨(), .inl (.pulling []),
        (loadSource (RetainedInvocation.Examples.closedLoad shared), RetainedInvocation.Examples.OwnData.revoked),
        OperationCostProtocol.initial OwnData.Invocation.profile 200⟩) = .refused (.inl .admission) := by
  rfl

/-- The exact pause retains all unconsumed candidates and the old paid
prefix; concatenating suffix factors agrees with one unsplit invocation. -/
theorem actual_split_keeps_ordered_factors :
    let first := Cursor.advance Provider Client Charge 8 (packet shared)
    let firstFactors := ((Invocation.sourceAccount operationPrimitive revocationWorlds
      RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed
      interpret Reader notice 91 () (Invocation.factorBlock (fun _ _ => 2) 91)).of (history shared 8)).toList
    let secondFactors := ((Invocation.sourceAccount operationPrimitive revocationWorlds
      RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed
      interpret Reader notice 91 () (Invocation.factorBlock (fun _ _ => 2) 91)).of
        (NativeControlCursor.ProtocolHistory.resumeHistory Provider Client Charge 92 first)).toList
    firstFactors ++ secondFactors = factors (fun _ _ => 2) shared ∧
      (Cursor.resume Provider Client Charge 92 first).1 = (run shared).1 := by
  decide +kernel

def tag : View Nat Unit Nat Unit Unit 0 → Nat
  | .inert => 0
  | .finish => 1
  | .refused _ => 2
  | .paid _ _ none => 3
  | .paid _ _ (some note) =>
      match note.completed with
      | some completed => match completed.kind with | .production => 4 | .delivery => 5
      | none => if note.effect.isSome then 6 else if note.returned.isSome then 7
          else if note.firings.isEmpty then 9 else 8

def recording (code : RetainedInvocation.Examples.ExampleCode) (fuel capacity : Nat) :=
  ((Invocation.observedAdvance operationPrimitive revocationWorlds
    RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed
    interpret Reader notice 91 fuel (packet code) (some (Recording.Prefix.initial capacity))).2).map
      (Recording.Prefix.map tag)

/-- The actual enabled recording has twenty paid polling requests and one
free finishing inspection. This is not twenty-one source firings. -/
theorem enabled_history_keeps_every_protocol_occurrence :
    (recording shared 100 100).map (fun record => (record.items.length, record.omitted)) = some (21, 0) ∧
      ((recording shared 100 100).bind Recording.Prefix.complete?).isSome = true := by
  decide +kernel

/-- A full buffer retains its prefix and reports all later omissions; it
cannot advertise the partial buffer as the complete interaction interval. -/
theorem a_bounded_recording_is_honestly_incomplete :
    (recording shared 100 2).map (fun record => (record.items.length, record.omitted)) = some (2, 19) ∧
      (recording shared 100 2).bind Recording.Prefix.complete? = none := by
  decide +kernel

/-- Starting after a paid prefix records only the actual resumed suffix,
without replaying that prefix or resetting its own-write currency. -/
theorem starting_recording_after_a_paid_prefix_is_a_suffix :
    let first := Cursor.advance Provider Client Charge 8 (packet shared)
    let recorded := Invocation.observedResume operationPrimitive revocationWorlds
      RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed
      interpret Reader notice 91 92 first (some (Recording.Prefix.initial 100))
    recorded.1.1 = (run shared).1 ∧
      (recorded.2.map (fun record => record.items.length)) = some 13 := by
  decide +kernel

/-- Stopping preserves the captured prefix while the invocation continues.
The old prefix remains an interval of eight observations. -/
theorem stopping_does_not_rewrite_the_prefix_or_repeat_the_source :
    let first := Cursor.advance Provider Client Charge 8 (packet shared)
    let record := (Recording.Prefix.initial 100).append (Word.of (history shared 8)).toList
    let stopped := Invocation.stopAndResume operationPrimitive revocationWorlds
      RetainedInvocation.Examples.OwnData.required RetainedInvocation.Examples.OwnData.needed
      interpret Reader notice 91 92 first record
    stopped.1.1 = (run shared).1 ∧ (stopped.2.map tag).items.length = 8 := by
  decide +kernel

/-- A passive payload-decoder refusal cannot be hidden by filtering. A
retry with an admitted decoder reads the same complete retained interval. -/
theorem refused_payload_projection_does_not_erase_or_rerun_events :
    let record := (Recording.Prefix.initial 100).append (Word.of (history shared)).toList
    Recording.Prefix.project? (fun (_ : View Nat Unit Nat Unit Unit 0) => (none : Option Nat)) record = none ∧
      ((Recording.Prefix.project? (fun event => some (tag event)) record).map List.length) = some 21 ∧
      (run shared).1 = 20 := by
  decide +kernel

def modeSaved (mode : SourceProducerCardinality.CallingConvention)
    (code : RetainedInvocation.Examples.ExampleCode) (fuel : Nat := 100) :=
  Cursor.advance Provider
    (OperationCostProtocol.Indexed.client
      (SourceProducerCardinality.CallingModes.client mode (RetainedInvocation.Examples.ExampleResult × List Nat)) notice)
    Charge fuel
    (Invocation.modePacket operationPrimitive revocationWorlds RetainedInvocation.Examples.OwnData.required
      RetainedInvocation.Examples.OwnData.needed interpret notice mode 91
      (loadSource (RetainedInvocation.Examples.closedLoad code), RetainedInvocation.Examples.OwnData.context)
      (OperationCostProtocol.initial OwnData.Invocation.profile 200))

def isFault (item : RetainedInvocation.Examples.ExampleResult × List Nat) : Bool :=
  match item.1 with | .value _ => false | _ => true

def modeSummary (mode : SourceProducerCardinality.CallingConvention)
    (code : RetainedInvocation.Examples.ExampleCode) (fuel : Nat := 100) :=
  (Invocation.modeReadout notice mode isFault (modeSaved mode code fuel).2).map
    (Except.map (fun result => (result.successful, result.rows.length)))

/-- The producer plan hands over this actual unfinished Need source without
effects or polls. Nonempty consumes only its first occurrence; scalar modes
wait for the real exhaustion signal before decoding. -/
theorem actual_four_mode_clients_have_distinct_receiving_boundaries :
    modeSummary .producer shared = some (.ok (true, 0)) ∧
      (modeSaved .producer shared).1 = 0 ∧
      modeSummary .nonemptyProducer RetainedInvocation.Examples.duplicate = some (.ok (true, 1)) ∧
      modeSummary .direct RetainedInvocation.Examples.duplicate = some (.ok (false, 2)) ∧
      modeSummary .optional shared = some (.ok (true, 1)) ∧
      modeSummary .direct shared = some (.ok (true, 1)) := by
  decide +kernel

/-- Bounded scalar work cannot publish a provisional prefix. A completed
fault stays a faulted occurrence, rather than optional absence. -/
theorem actual_mode_pause_and_fault_are_not_absence :
    modeSummary .optional shared 0 = none ∧
      modeSummary .direct shared 1 = none ∧
      modeSummary .optional PolarizedNeedMachineExamples.badForce = some (.ok (false, 1)) := by
  decide +kernel

end Examples

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.RetainedInvocation.GradedHistory

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.RetainedInvocation.OwnData.Polling

open _root_.CategoryTheory
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Machines

variable {Effect DataWorld Entry State Target Item : Type} {width : Nat} [Category.{0} DataWorld]
  (authority : IndexedAuthority.{0, 0, 0} DataWorld)
  (required : OrderedDependencyStore.Action Entry width → (world : DataWorld) → authority.Fibre world)
  (needed : (world : DataWorld) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Entry width),
    Decidable (FrameUpdate point.authority (required action point.world))]
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]
  (interpret : Effect → OrderedDependencyStore.Action Entry width)

/-- One raw polling successor. Its reply remains separate from current
permission and the external data context. -/
def next (pull : State → HostCalls.Pull State Item) (state : State) : State :=
  ((NativeControlCursor.provider pull).step (base := ()) (index := ()) state ()).2

/-- A current-data handler around an existing polling face. `active` is a
cheap source-inventory observation; the separate indexed gate is checked
before this provider is invoked. Only an accepted own write advances source
state, and its result cannot replace the retained source context. -/
def provider (pull : State → HostCalls.Pull State Item) (active : State → Bool)
    (effect : State → Option Effect) : Cursor.Provider (NativeControlCursor.protocol Item) where
  State _ _ := State × OwnData.Context authority (Entry := Entry) (width := width)
  step state request :=
    if active state.1 then
      let moved := OwnData.step authority required needed interpret (next pull) effect state
      match moved.2 with
      | .error _ => ⟨.suspend (), state⟩
      | .ok () => ⟨((NativeControlCursor.provider pull).step (base := ()) (index := ()) state.1 request).1, moved.1⟩
    else ⟨.done, state⟩

def stateMap {sourcePull : State → HostCalls.Pull State Item}
    {targetPull : Target → HostCalls.Pull Target Item}
    (h : Cursor.Hom (NativeControlCursor.provider sourcePull) (NativeControlCursor.provider targetPull))
    (state : State) : Target := h.map (base := ()) (index := ()) state

variable (sourcePull : State → HostCalls.Pull State Item) (targetPull : Target → HostCalls.Pull Target Item)
  (sourceActive : State → Bool) (targetActive : Target → Bool)
  (sourceEffect : State → Option Effect) (targetEffect : Target → Option Effect)
  (h : Cursor.Hom (NativeControlCursor.provider sourcePull) (NativeControlCursor.provider targetPull))
  (active_eq : ∀ state, sourceActive state = targetActive (stateMap h state))
  (effect_eq : ∀ state, sourceEffect state = targetEffect (stateMap h state))

theorem next_projection (state : State) : stateMap h (next sourcePull state) = next targetPull (stateMap h state) := by
  exact congrArg (fun result => result.2) (h.step (base := ()) (index := ()) state ())

/-- A raw local request square, together with the actual effect observation,
transports the existing current-data primitive. No whole-run law is assumed. -/
theorem turn_projection (agrees : ∀ state, sourceEffect state = targetEffect (stateMap h state))
    (state : State) (context : OwnData.Context authority (Entry := Entry) (width := width)) :
    let moved := OwnData.step authority required needed interpret (next sourcePull) sourceEffect (state, context)
    ((stateMap h moved.1.1, moved.1.2), moved.2) =
      OwnData.step authority required needed interpret (next targetPull) targetEffect (stateMap h state, context) := by
  dsimp only
  unfold OwnData.step
  rw [← agrees state]
  split
  · split
    · cases observed : sourceEffect state with
      | none => simp only [next_projection]
      | some event =>
          simp only
          cases performed : Cursor.ReadOnlyQuery.OwnWrite.step authority required context.live (.write (interpret event)) with
          | mk live reply =>
              cases reply with
              | ok unitValue => cases unitValue; simp only [next_projection]
              | error fault => rfl
    · rfl
  · rfl

/-- The source's entire private state and current external context are kept
on refusal. Accepted polling replies use the constructed raw local map. -/
def representation : Cursor.Hom
    (provider authority required needed interpret sourcePull sourceActive sourceEffect)
    (provider authority required needed interpret targetPull targetActive targetEffect) where
  map state := (stateMap h state.1, state.2)
  step state request := by
    rcases state with ⟨source, context⟩
    dsimp only [provider]
    rw [← active_eq source]
    cases selected : sourceActive source with
    | false => rfl
    | true =>
        simp only [↓reduceIte]
        have compared := turn_projection authority required needed interpret sourcePull targetPull
          sourceEffect targetEffect h effect_eq source context
        cases moved : OwnData.step authority required needed interpret (next sourcePull) sourceEffect (source, context) with
        | mk reached reply =>
            rcases reached with ⟨after, current⟩
            have targetMoved : OwnData.step authority required needed interpret (next targetPull) targetEffect
                (stateMap h source, context) = ((stateMap h after, current), reply) := by
              simpa only [moved] using compared.symm
            simp only [targetMoved]
            cases reply with
            | error reason => rfl
            | ok unitValue =>
                cases unitValue
                have sameReply := congrArg (fun result => result.1) (h.step (base := ()) (index := ()) source request)
                exact Sigma.ext sameReply (heq_of_eq rfl)

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.RetainedInvocation.OwnData.Polling

/-! ## A shared Need world for authored sources and rich continuations

The joint profile below supplies language actions to the existing owned Need
engine. Authored atoms and callable rich answers have distinct representations;
only an explicit native-data pocket has a roundtrip view on both sides.
Source calls allocate an authored origin and demand it through the existing
resume stack. No producer is evaluated by the old atomic rich primitive.
-/
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource

open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive Operation where
  | identity
  | source (program : NativeEquationNeed.Program) (bindings : List (String × Nat))
  | frontier (program : NativeEquationNeed.Program) (bindings : List (String × Nat))

abbrev RichValue := PolarizedNeedMachine.Answer Atom Operation Nat 0
abbrev RichLocal := PolarizedNeedMachine.Local Atom Operation Nat Empty String 0
abbrev RichResume := PolarizedNeedMachine.Resume Atom Operation Nat 0
abbrev RichKont := PolarizedNeedMachine.Kont Atom Operation Nat 0
abbrev RichClosure := PolarizedNeedMachine.Closure Atom Operation Nat 0
abbrev Fault := PolarizedNeedMachine.Fault String

inductive Value where
  | native (atom : Atom)
  | rich (answer : RichValue)

/-- Native data is a closed atom pocket. Rich callables and non-atomic native
terms keep their original captured representation. -/
def richValue : RichValue → Value
  | .returned (.native (.head atom)) => .native atom
  | answer => .rich answer

def richView : Value → RichValue
  | .native atom => .returned (.native (.head atom))
  | .rich answer => answer

def nativeView : Value → Option Atom
  | .native atom => some atom
  | _ => none

theorem rich_value_roundtrip (answer : RichValue) : richView (richValue answer) = answer := by
  cases answer with
  | nativeFunction body => rfl
  | valueFunction body => rfl
  | returned value =>
      cases value with
      | thunk code native values needs => rfl
      | packNative index value => rfl
      | native term => cases term <;> rfl

theorem richValue_injective : Function.Injective richValue := by
  intro first second same
  exact (rich_value_roundtrip first).symm.trans
    ((congrArg richView same).trans (rich_value_roundtrip second))

inductive Origin where
  | authored (program : NativeEquationNeed.Program) (origin : NativeEquationNeed.Origin)
  | rich (closure : RichClosure)

inductive Rule where
  | authored (program : NativeEquationNeed.Program) (rule : NativeEquationNeed.Rule)
  | rich (rule : PolarizedNeedMachine.Rule)

inductive Local where
  | authored (program : NativeEquationNeed.Program) (state : NativeEquationNeed.Local)
  | rich (state : RichLocal)
  | sourceDemand (cell : CellId) (returns : RichKont)
  | enterSource (program : NativeEquationNeed.Program) (atom : Atom)
      (environment : NativeEquationNeed.Environment) (returns : RichKont)
  | output (outcome : Produced Value Empty Fault)

inductive Resume where
  | authored (program : NativeEquationNeed.Program) (resume : NativeEquationNeed.Resume)
  | rich (resume : RichResume)
  | sourceReturn (returns : RichKont)

abbrev World := NeedReference.World Origin Rule Value Empty Fault Nat
abbrev Machine := NeedReference.Machine Origin Local Resume Rule Value Empty Fault Nat
abbrev Outcome := Produced Value Empty Fault

/-- The existing generic representation maps retain actual cell, owner,
branch-path and work coordinates. No fresh cell is invented by either map. -/
def authoredMap (program : NativeEquationNeed.Program) : NeedRepresentation.Mapping
    NativeEquationNeed.Origin NativeEquationNeed.Local NativeEquationNeed.Resume
    NativeEquationNeed.Rule Atom Empty String Empty
    Origin Local Resume Rule Value Empty Fault Nat where
  origin := Origin.authored program
  state := Local.authored program
  resume := Resume.authored program
  rule := Rule.authored program
  value := Value.native
  stableFault := Empty.elim
  retryableFault := PolarizedNeedMachine.Fault.native
  effect := Empty.elim

def richMap : NeedRepresentation.Mapping
    RichClosure RichLocal RichResume PolarizedNeedMachine.Rule RichValue Empty Fault Nat
    Origin Local Resume Rule Value Empty Fault Nat where
  origin := Origin.rich
  state := Local.rich
  resume := Resume.rich
  rule := Rule.rich
  value := richValue
  stableFault := Empty.elim
  retryableFault := id
  effect := id

def richOutcome : Outcome → Produced RichValue Empty Fault
  | .value value => .value (richView value)
  | .stableFault impossible => nomatch impossible
  | .retryableFault reason => .retryableFault reason

def nativeRetry? : RetryReason Fault → Option (RetryReason String)
  | .domain (.native fault) => some (.domain fault)
  | .domain _ => none
  | .blackhole cell => some (.blackhole cell)
  | .outOfScope cell => some (.outOfScope cell)
  | .noRule cell => some (.noRule cell)
  | .ownershipLost cell expected actual => some (.ownershipLost cell expected actual)
  | .allocationCollision cell => some (.allocationCollision cell)

def nativeOutcome? : Outcome → Option NativeEquationNeed.Outcome
  | .value value => (nativeView value).map Produced.value
  | .stableFault impossible => nomatch impossible
  | .retryableFault reason => (nativeRetry? reason).map Produced.retryableFault

theorem rich_outcome_roundtrip (outcome : Produced RichValue Empty Fault) :
    richOutcome (richMap.mapOutcome outcome) = outcome := by
  cases outcome with
  | value value => exact congrArg Produced.value (rich_value_roundtrip value)
  | stableFault impossible => nomatch impossible
  | retryableFault reason => cases reason <;> rfl

theorem native_outcome_roundtrip (program : NativeEquationNeed.Program) (outcome : NativeEquationNeed.Outcome) :
    nativeOutcome? ((authoredMap program).mapOutcome outcome) = some outcome := by
  cases outcome with
  | value value => rfl
  | stableFault impossible => nomatch impossible
  | retryableFault reason => cases reason <;> rfl

/-- Captured source arguments borrow the exact lexical Need slots. Names
must be unique, and every numeric reference is checked before allocation. -/
def resolveBindings {count : Nat} (needs : Fin count → CellId)
    (bindings : List (String × Nat)) : Option NativeEquationNeed.Environment :=
  if (bindings.map Prod.fst).Nodup then
    bindings.mapM fun (name, position) =>
      if bound : position < count then some (name, needs ⟨position, bound⟩) else none
  else none

def primitive (operation : Operation) (argument : Tm Atom 0) : Produced (Tm Atom 0) Empty String :=
  match operation with
  | .identity => .value argument
  | .source _ _ | .frontier _ _ =>
      .retryableFault (.domain "source requires the shared invocation profile")

/-- Only this explicit profile interprets a source operation as an owned
allocation/demand. The current lexical environments and caller returns are
retained rather than reconstructed from a printed call. -/
def action : Local → Action Origin Local Resume Value Empty Fault Nat
  | .authored program state => (authoredMap program).mapAction (NativeEquationNeed.action state)
  | .rich (.evaluate ⟨_, _, _, .call (.source program bindings) argument, native, _, needs⟩ returns) =>
      match subst native argument with
      | .head atom =>
          match resolveBindings needs bindings with
          | some environment => .allocate (.authored program (.expression atom environment)) (.sourceReturn returns)
          | none => .done (.retryableFault (.domain (.native "invalid source bindings")))
      | _ => .done (.retryableFault (.domain .expectedNativeValue))
  | .rich state => richMap.mapAction ((PolarizedNeedMachine.reference primitive).action state)
  | .sourceDemand cell returns => .demand cell (.sourceReturn returns)
  | .enterSource program atom environment returns =>
      .allocate (.authored program (.expression atom environment)) (.sourceReturn returns)
  | .output outcome => .done outcome

def afterDemand : Resume → Outcome → Local
  | .rich resume, outcome =>
      .rich ((PolarizedNeedMachine.reference primitive).afterDemand resume (richOutcome outcome))
  | .sourceReturn returns, outcome => .rich (PolarizedNeedMachine.deliver (richOutcome outcome) returns)
  | .authored program resume, outcome =>
      match nativeOutcome? outcome with
      | some value => .authored program (NativeEquationNeed.afterDemand resume value)
      | none => match outcome with
        | .retryableFault _ => .output outcome
        | .value _ => .output (.retryableFault (.domain (.native "source expects native data")))
        | .stableFault impossible => nomatch impossible

def afterAllocation : Resume → CellId → Local
  | .rich resume, cell => .rich ((PolarizedNeedMachine.reference primitive).afterAllocation resume cell)
  | .authored program resume, cell => .authored program (NativeEquationNeed.afterAllocation resume cell)
  | .sourceReturn returns, cell => .sourceDemand cell returns

def specification :
    Spec Origin Local Resume Rule Value Empty Fault Nat where
  alternatives
    | .authored program origin => ((NativeEquationNeed.specification program).alternatives origin).map
        (fun pair => (Rule.authored program pair.1, Local.authored program pair.2))
    | .rich closure => ((PolarizedNeedMachine.reference primitive).alternatives closure).map
        (fun pair => (Rule.rich pair.1, Local.rich pair.2))
  action := action
  afterDemand := afterDemand
  afterAllocation := afterAllocation

def extension :
    NeedLocalSteps.Extension Origin Local Resume Rule Value Empty Fault Nat :=
  ⟨specification, fun state => match state with
    | .rich state => (PolarizedNeedMachine.localStep state).map Local.rich
    | _ => none⟩

/-- An explicitly declared finite frontier is source syntax in this
profile. An empty expression is interpreted as zero branches only at this
operation; returning that same atom as Data still yields one value. -/
def frontier? : Local → Option (List Local)
  | .rich (.evaluate ⟨_, _, _, .call (.frontier program bindings) argument, native, _, needs⟩ returns) =>
      match subst native argument, resolveBindings needs bindings with
      | .head (.expression bodies), some environment =>
          some (bodies.map fun atom => .enterSource program atom environment returns)
      | _, _ => none
  | _ => none

/-- The finite-frontier handler supplies the selected source's successor
family; every other instruction delegates to the existing Need executor.
The caller stack and inherited cells survive in each nonempty branch. -/
def step (machine : Machine) : List Machine :=
  match machine.control with
  | .run state stack =>
      match frontier? state with
      | some bodies => bodies.zipIdx.map fun (body, ordinal) =>
          finished machine (machine.world.fork ordinal) (.run body stack) 0 0 0 0
      | none => NeedLocalSteps.step extension machine
  | _ => NeedLocalSteps.step extension machine

/-- Ordinary source and Need semantics are unchanged outside the declared
finite-frontier request, including the native no-rule fault. -/
theorem ordinary_step (machine : Machine)
    (ordinary : ∀ state stack, machine.control = .run state stack → frontier? state = none) :
    step machine = NeedLocalSteps.step extension machine := by
  cases control : machine.control <;> simp only [step, control]
  rw [ordinary _ _ control]

/-- The empty source body consumes this activation with no answer. It does
not write a cached fault, and it does not invoke a native body. -/
theorem empty_frontier_step (machine : Machine) (state : Local) (stack : List (Frame Resume))
    (control : machine.control = .run state stack) (empty : frontier? state = some []) :
    step machine = [] := by
  simp only [step, control, empty, List.zipIdx_nil, List.map_nil]

/-- The declared finite inventory is checked before the source handler
branches. Each body retains the exact immutable program and lexical cells. -/
theorem frontier_request (program : NativeEquationNeed.Program) {n v k : Nat}
    (bindings : List (String × Nat)) (argument : Tm Atom n) (native : Sub Atom n 0)
    (values : Fin v → PolarizedNeedMachine.RuntimeValue Atom Operation Nat 0)
    (needs : Fin k → CellId) (returns : RichKont) (bodies : List Atom)
    (environment : NativeEquationNeed.Environment)
    (literal : subst native argument = .head (.expression bodies))
    (resolved : resolveBindings needs bindings = some environment) :
    frontier? (.rich (.evaluate
      ⟨n, v, k, .call (.frontier program bindings) argument, native, values, needs⟩ returns)) =
      some (bodies.map fun atom => .enterSource program atom environment returns) := by
  simp only [frontier?, literal, resolved]

/-- This local successor law accounts for the actual finite source face.
An empty inventory removes only this activation; a nonempty inventory keeps
every positional occurrence, inherited heap and caller stack. -/
theorem frontier_step (machine : Machine) (state : Local) (stack : List (Frame Resume))
    (bodies : List Local) (control : machine.control = .run state stack)
    (selected : frontier? state = some bodies) :
    step machine = bodies.zipIdx.map (fun (body, ordinal) =>
      finished machine (machine.world.fork ordinal) (.run body stack) 0 0 0 0) := by
  simp only [step, control, selected]

theorem frontier_preserves_multiplicity (machine : Machine) (state : Local)
    (stack : List (Frame Resume)) (bodies : List Local)
    (control : machine.control = .run state stack) (selected : frontier? state = some bodies) :
    (step machine).length = bodies.length := by
  rw [frontier_step machine state stack bodies control selected]
  simp only [List.length_map, List.length_zipIdx]

/-- This is a proved whole-specification compatibility for the actual
ungraded authored fragment. Cross-source calls have separate local laws. -/
theorem authoredCompatible (program : NativeEquationNeed.Program) :
    NeedRepresentation.Compatible (authoredMap program) (NativeEquationNeed.specification program)
      (specification) where
  alternatives _ := rfl
  action _ := rfl
  afterDemand resume outcome := by
    change afterDemand (.authored program resume) ((authoredMap program).mapOutcome outcome) =
      .authored program (NativeEquationNeed.afterDemand resume outcome)
    simp only [afterDemand.eq_def, native_outcome_roundtrip program]
  afterAllocation _ _ := rfl

/-- Source admission uses exactly the supplied borrowed cells and stores the
original caller continuation in the actual resume constructor. -/
theorem source_call_action (program : NativeEquationNeed.Program) {n v k : Nat} (bindings : List (String × Nat))
    (argument : Tm Atom n) (native : Sub Atom n 0)
    (values : Fin v → PolarizedNeedMachine.RuntimeValue Atom Operation Nat 0)
    (needs : Fin k → CellId) (returns : RichKont) (atom : Atom)
    (environment : NativeEquationNeed.Environment)
    (literal : subst native argument = .head atom)
    (resolved : resolveBindings needs bindings = some environment) :
    action (.rich (.evaluate ⟨n, v, k, .call (.source program bindings) argument, native, values, needs⟩ returns)) =
      .allocate (.authored program (.expression atom environment)) (.sourceReturn returns) := by
  simp only [action, literal, resolved]

/-- Re-entry uses the source's actual returned world. The resume value has
no world field that could silently substitute an old captured world. -/
theorem source_resume_control (outcome : Outcome) (returns : RichKont) :
    afterDemand (.sourceReturn returns) outcome =
      .rich (PolarizedNeedMachine.deliver (richOutcome outcome) returns) := rfl

/-- The actual source call executes the existing allocation instruction,
including its normal collision outcome, then retains the original caller. -/
theorem source_call_allocation (program : NativeEquationNeed.Program)
    (world : World) (stack : List (Frame Resume)) (work : Work)
    {n v k : Nat} (bindings : List (String × Nat))
    (argument : Tm Atom n) (native : Sub Atom n 0)
    (values : Fin v → PolarizedNeedMachine.RuntimeValue Atom Operation Nat 0)
    (needs : Fin k → CellId) (returns : RichKont) (atom : Atom)
    (environment : NativeEquationNeed.Environment)
    (literal : subst native argument = .head atom)
    (resolved : resolveBindings needs bindings = some environment) :
    NeedLocalSteps.step extension
      (⟨world, .run (.rich (.evaluate
        ⟨n, v, k, .call (.source program bindings) argument, native, values, needs⟩ returns)) stack, work⟩ : Machine) =
      match world.allocate? (.authored program (.expression atom environment)) with
      | none => [retryMachine
          (⟨world, .run (.rich (.evaluate
            ⟨n, v, k, .call (.source program bindings) argument, native, values, needs⟩ returns)) stack, work⟩ : Machine)
          world (world.freshCell 0) (.allocationCollision (world.freshCell 0)) stack 1 0 0 0]
      | some (reached, cell) =>
          [⟨reached, .run (.sourceDemand cell returns) stack, work.bump 1 1 1 1⟩] := by
  simp only [NeedLocalSteps.step, extension, PolarizedNeedMachine.localStep,
    Option.map_none, NeedReference.step, specification]
  rw [source_call_action program bindings argument native values needs returns atom environment literal resolved]
  simp only [afterAllocation, finished]
  generalize world.allocate? (.authored program (.expression atom environment)) = allocated
  cases allocated with
  | none => rfl
  | some pair => cases pair; rfl

/-- A language-local bridge demand installs the actual owner engine's resume
frame; it neither evaluates a source atom nor touches the shared heap. -/
theorem source_demand_step
    (world : World) (cell : CellId) (returns : RichKont) (stack : List (Frame Resume)) (work : Work) :
    NeedLocalSteps.step extension
      (⟨world, .run (.sourceDemand cell returns) stack, work⟩ : Machine) =
      [⟨world, .force cell (.resume (.sourceReturn returns) :: stack), work.bump 0 0 0 0⟩] := rfl

/-- Pure authored transitions are preserved occurrence by occurrence by the
constructed compatibility, including cache owner and full unmatched state. -/
theorem authored_step (program : NativeEquationNeed.Program) (machine : NativeEquationNeed.NativeMachine) :
    (NeedReference.step (NativeEquationNeed.specification program) machine).map (authoredMap program).mapMachine =
      NeedLocalSteps.step extension ((authoredMap program).mapMachine machine) := by
  rw [(authoredCompatible program).step_map]
  cases machine with
  | mk world control work => cases control <;> rfl

/-- Authored production evidence keeps the immutable program, actual source
row, shared argument references and physical invocation coordinates apart. -/
structure AuthoredProduction where
  program : NativeEquationNeed.Program
  cell : CellId
  evaluator : EvaluatorId
  path : WorldPath
  ordinal : Nat
  row : NativeCandidateGrades.Row
  head : String
  arguments : List CellId

/-- The independent row projection retains the full admitted application. -/
def productionOf (selected : NeedDependentService.SourceBranch.Selection Origin Local Resume Rule Value Empty)
    (path : WorldPath) (ordinal : Nat) : Option AuthoredProduction :=
  match selected.record.origin with
  | .authored program (.application head arguments) =>
      ((NativeCandidateGrades.rows program head arguments)[ordinal]?).map fun row =>
        ⟨program, selected.cell, selected.evaluator, path, ordinal, row, head, arguments⟩
  | _ => none

/-- Source-specific evidence is extracted only at a real selected authored
application, never by interpreting a rich entry label as a row number. -/
def production? (machine : Machine) (ordinal : Nat) : Option AuthoredProduction :=
  (NeedDependentService.SourceBranch.inspect specification machine ordinal).bind
    (fun selected => productionOf selected machine.world.path ordinal)

/-- A row emitted by the executable source reader has an independent authored
activation derivation. Its physical row is never a generic rich-choice label. -/
theorem production_has_activation {machine : Machine} {ordinal : Nat} {production : AuthoredProduction}
    (found : production? machine ordinal = some production) :
    NativeEquationNeed.Activates production.program production.head production.arguments
      (.equation production.row.index) (.evaluate production.row.body production.row.environment) := by
  obtain ⟨selection, _, recognized⟩ := Option.bind_eq_some_iff.mp found
  cases origin : selection.record.origin with
  | rich closure => simp only [productionOf, origin] at recognized; cases recognized
  | authored program nativeOrigin =>
      cases nativeOrigin with
      | expression atom environment => simp only [productionOf, origin] at recognized; cases recognized
      | application head arguments =>
          simp only [productionOf, origin] at recognized
          cases row : (NativeCandidateGrades.rows program head arguments)[ordinal]? with
          | none => simp only [row, Option.map_none] at recognized; cases recognized
          | some actual =>
              simp only [row, Option.map_some, Option.some.injEq] at recognized
              subst production
              exact (NativeCandidateGrades.row_admission_iff program head arguments actual).mp
                (List.mem_of_getElem? row)

/-- The source admission and row reader agree at the same list position.
This binds the selected body and its captured cells to the actual row. -/
theorem admitted_authored_row
    {machine : Machine} {ordinal : Nat}
    {selection : NeedDependentService.SourceBranch.Selection Origin Local Resume Rule Value Empty}
    (admitted : NeedDependentService.SourceBranch.Admitted specification machine ordinal selection)
    (program : NativeEquationNeed.Program) (head : String) (arguments : List CellId)
    (row : NativeCandidateGrades.Row)
    (origin : selection.record.origin = .authored program (.application head arguments))
    (position : (NativeCandidateGrades.rows program head arguments)[ordinal]? = some row) :
    selection.rule = .authored program (.equation row.index) ∧
      selection.state = .authored program (.evaluate row.body row.environment) := by
  have located := admitted.alternative
  rw [origin] at located
  change ((NativeEquationNeed.rowCandidates program head arguments).map
    (fun pair => (Rule.authored program pair.1, Local.authored program pair.2)))[ordinal]? =
      some (selection.rule, selection.state) at located
  rw [← NativeCandidateGrades.rows_alternatives, List.map_map, List.getElem?_map, position] at located
  simp only [Option.map_some, Option.some.injEq, Function.comp_apply,
    NativeCandidateGrades.Row.alternative, Prod.mk.injEq] at located
  exact ⟨located.1.symm, located.2.symm⟩

theorem admitted_shared_transition {machine : Machine} {ordinal : Nat}
    {selection : NeedDependentService.SourceBranch.Selection Origin Local Resume Rule Value Empty}
    (admitted : NeedDependentService.SourceBranch.Admitted specification machine ordinal selection) :
    (step machine)[ordinal]? = some (NeedDependentService.SourceBranch.realize machine selection) := by
  have original : step machine = NeedReference.step specification machine := by
    simp only [step, NeedLocalSteps.step, extension, admitted.control]
  rw [original]
  exact NeedDependentService.SourceBranch.admitted_transition specification admitted

/-- Production metadata, actual source-row admission and exact successor
coordinates are joined by the executable reader and the engine transition.
No equality of final answer bags is used to identify the selected body. -/
theorem production_admitted_body {machine : Machine} {ordinal : Nat} {production : AuthoredProduction}
    (found : production? machine ordinal = some production) :
    ∃ selection : NeedDependentService.SourceBranch.Selection Origin Local Resume Rule Value Empty,
      NeedDependentService.SourceBranch.Admitted specification machine ordinal selection ∧
      (step machine)[ordinal]? = some (NeedDependentService.SourceBranch.realize machine selection) ∧
      selection.cell = production.cell ∧ selection.evaluator = production.evaluator ∧
      selection.rule = .authored production.program (.equation production.row.index) ∧
      selection.state = .authored production.program (.evaluate production.row.body production.row.environment) := by
  obtain ⟨selection, inspected, recognized⟩ := Option.bind_eq_some_iff.mp found
  have admitted := NeedDependentService.SourceBranch.inspect_sound specification inspected
  cases origin : selection.record.origin with
  | rich closure => simp only [productionOf, origin] at recognized; cases recognized
  | authored program nativeOrigin =>
      cases nativeOrigin with
      | expression atom environment => simp only [productionOf, origin] at recognized; cases recognized
      | application head arguments =>
          simp only [productionOf, origin] at recognized
          cases row : (NativeCandidateGrades.rows program head arguments)[ordinal]? with
          | none => simp only [row, Option.map_none] at recognized; cases recognized
          | some actual =>
              simp only [row, Option.map_some, Option.some.injEq] at recognized
              subst production
              have agrees := admitted_authored_row admitted program head arguments actual origin row
              exact ⟨selection, admitted, admitted_shared_transition admitted, rfl, rfl, agrees⟩

/-- Actual selected-row evidence implies the independent native activation
judgment, including its physical index and positional binding derivation. -/
theorem selected_row_admitted (program : NativeEquationNeed.Program)
    {machine : Machine} {ordinal : Nat}
    {selection : NeedDependentService.SourceBranch.Selection Origin Local Resume Rule Value Empty}
    (admitted : NeedDependentService.SourceBranch.Admitted (specification) machine ordinal selection)
    (head : String) (arguments : List CellId) (row : NativeCandidateGrades.Row)
    (origin : selection.record.origin = .authored program (.application head arguments))
    (rule : selection.rule = .authored program (.equation row.index))
    (state : selection.state = .authored program (.evaluate row.body row.environment)) :
    NativeEquationNeed.Activates program head arguments (.equation row.index)
      (.evaluate row.body row.environment) := by
  have located := admitted.alternative
  rw [origin, rule, state] at located
  change ((NativeEquationNeed.rowCandidates program head arguments).map
    (fun pair => (Rule.authored program pair.1, Local.authored program pair.2)))[ordinal]? =
      some (.authored program (.equation row.index), .authored program (.evaluate row.body row.environment)) at located
  have member := List.mem_of_getElem? located
  obtain ⟨⟨originalRule, originalState⟩, actual, same⟩ := List.mem_map.mp member
  have sameRule := congrArg Prod.fst same
  have sameState := congrArg Prod.snd same
  simp only [Rule.authored.injEq, true_and] at sameRule
  simp only [Local.authored.injEq, true_and] at sameState
  subst originalRule originalState
  exact (NativeEquationNeed.rowCandidates_iff _ _ _ _ _).mp actual

/-- A completed shared cell is a delivery. It cannot acquire another source
row merely because the returned native atom equals an earlier result. -/
theorem cached_delivery_has_no_authored_production
    (world : World) (cell : CellId) (origin : Origin) (value : Value)
    (stack : List (Frame Resume)) (work : Work) (ordinal : Nat)
    (cached : world.heap.lookup cell = some ⟨origin, .value value⟩) :
    production? ⟨world, .force cell stack, work⟩ ordinal = none := by
  simp only [production?, NeedDependentService.SourceBranch.inspect, NeedDependentService.SourceBranch.inspectAt,
    cached, Option.bind_some]
  rfl

abbrev CoreMachine := NeedExecution.CoreMachine Origin Local Resume Rule Value Empty Fault Nat

/-- The receipt-policy executor handles the same admitted finite source
inventory. Ordinary protocol instructions use its independent Need executor. -/
def coreStep (machine : CoreMachine) : List CoreMachine :=
  match machine.control with
  | .run state stack =>
      match frontier? state with
      | some bodies => bodies.zipIdx.map fun (body, ordinal) =>
          ⟨machine.world.fork ordinal, .run body stack, machine.work.bump 0 0 0 0⟩
      | none => NeedLocalSteps.coreStep extension machine
  | _ => NeedLocalSteps.coreStep extension machine

/-- The independently executed local instruction square preserves every
successor occurrence, heap, control and work coordinate. Receipt storage is
the only selected erasure; it is not reported as an empty captured history. -/
theorem project_step (keepReceipts : Bool) (machine : Machine) :
    (step machine).map (NeedExecution.projectMachine keepReceipts) =
      coreStep (NeedExecution.projectMachine keepReceipts machine) := by
  cases control : machine.control with
  | run state stack =>
      cases selected : frontier? state with
      | none =>
          simpa only [step, coreStep, NeedExecution.projectMachine, control, selected] using
            NeedLocalSteps.project_local_step keepReceipts extension machine
      | some bodies =>
          simp only [step, coreStep, NeedExecution.projectMachine, control, selected,
            List.map_map, Function.comp_def, finished]
          rfl
  | force cell stack =>
      simpa only [step, coreStep, NeedExecution.projectMachine, control] using
        NeedLocalSteps.project_local_step keepReceipts extension machine
  | returned outcome stack =>
      simpa only [step, coreStep, NeedExecution.projectMachine, control] using
        NeedLocalSteps.project_local_step keepReceipts extension machine
  | halted outcome =>
      simpa only [step, coreStep, NeedExecution.projectMachine, control] using
        NeedLocalSteps.project_local_step keepReceipts extension machine

namespace Service

open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Machines

/-- This observer retains the selected Need heap, lineage, path and allocation
coordinates. Optional causal history is explicitly unavailable in this view. -/
def branchWorld (machine : Machine) : NeedExecution.CoreWorld Origin Rule Value Empty Fault Nat :=
  NeedExecution.projectWorld false machine.world

abbrev Node := WorkOccurrence Machine
abbrev Result := Produced Value Empty Fault
abbrev BranchWorld := NeedExecution.CoreWorld Origin Rule Value Empty Fault Nat
abbrev Inventory := NeedDependentService.Retained.Inventory
  (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule) (Value := Value)
  (StableFault := Empty) (RetryableFault := Fault) (Effect := Nat)
abbrev Item := Result × WorldPath × BranchWorld

def controller := RetainedInvocation.controller Node (Result × WorldPath)

def provider := NeedDependentService.Retained.provider step controller branchWorld

def initial (roots : List Machine) : Inventory :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller (roots.map WorkOccurrence.root)

def packet (mode : SourceProducerCardinality.CallingConvention) (roots : List Machine) :=
  SourceProducerCardinality.CallingModes.start mode provider (initial roots)

def run (mode : SourceProducerCardinality.CallingConvention) (allowance : Nat) (roots : List Machine) :=
  Cursor.advance provider (SourceProducerCardinality.CallingModes.client mode Item) (fun _ _ => 1)
    allowance (packet mode roots)

def isFault (item : Item) : Bool := match item.1 with | .value _ => false | _ => true

def receive (mode : SourceProducerCardinality.CallingConvention) :=
  SourceProducerCardinality.CallingModes.receive mode isFault provider

def summary (mode : SourceProducerCardinality.CallingConvention) (allowance : Nat) (roots : List Machine) :
    Option (Bool × Nat × Nat) :=
  match receive mode (run mode allowance roots).2 with
  | .inl _ => none
  | .inr (result, reached) => some (result.successful, result.rows.length, reached.search.frontier.length)

abbrev CoreNode := WorkOccurrence CoreMachine
abbrev CoreInventory := Mettapedia.GSLT.Core.InferenceControl.Snapshot CoreNode (Result × WorldPath) Nat

def projectNode (node : Node) : CoreNode := ⟨NeedExecution.projectMachine false node.state, node.trace⟩

def project (state : Inventory) : CoreInventory := state.mapState projectNode id

def coreController := RetainedInvocation.controller CoreNode (Result × WorldPath)

def sourceSystem := NeedDependentService.Retained.system step

def coreSystem : Mettapedia.GSLT.Core.BranchingTemporal.BranchingSystem CoreNode (Result × WorldPath) :=
  WorkOccurrence.lift ⟨NeedExecution.haltedOutcome, coreStep⟩

def sourceTick := Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick sourceSystem controller
def coreTick := Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick coreSystem coreController

theorem local_emit (node : Node) : sourceSystem.emit node = coreSystem.emit (projectNode node) := by
  simp only [sourceSystem, NeedDependentService.Retained.system, coreSystem, WorkOccurrence.lift,
    projectNode, NeedExecution.haltedOutcome_project]

theorem local_successors (node : Node) :
    (sourceSystem.successors node).map projectNode = coreSystem.successors (projectNode node) := by
  simp only [sourceSystem, NeedDependentService.Retained.system, coreSystem, WorkOccurrence.lift, projectNode]
  rw [← project_step false]
  simp only [List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq, projectNode]

/-- The real controller transports its full live frontier, returned origins
and memory from the local event and successor laws. -/
theorem tick_representation (state : Inventory) :
    project (sourceTick state) = coreTick (project state) := by
  exact Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick_mapState projectNode id sourceSystem coreSystem
    controller coreController local_emit local_successors (fun _ _ => rfl)
    (fun _ _ _ => by simp [controller, coreController, RetainedInvocation.controller,
      Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst, List.map_append])
    (fun _ _ _ _ => rfl) state

def corePull (inventory : CoreInventory) : HostCalls.Pull CoreInventory Item :=
  match Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected coreController inventory with
  | none => .done
  | some node =>
      let reached := coreTick inventory
      match NeedExecution.haltedOutcome node.state with
      | none => .suspend reached
      | some outcome => .yield (outcome, node.trace, node.state.world) reached

def coreProvider := NativeControlCursor.provider corePull

/-- Scalar, nonempty and producer clients all use this constructed local
provider map. A selected value carries that branch's complete represented
Need world; the state map separately retains all other live worlds. -/
def representation : Cursor.Hom provider coreProvider where
  map := project
  step state request := by
    have compared := tick_representation state
    cases chosen : state.search.frontier with
    | nil =>
        simp only [provider, NeedDependentService.Retained.provider, NativeControlCursor.provider,
          NeedDependentService.Retained.pull, coreProvider, corePull,
          Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected,
          Mettapedia.GSLT.Core.BranchingTemporal.selected, controller, coreController,
          RetainedInvocation.controller, Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst,
          project, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapState,
          Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes,
          Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapMemory,
          Mettapedia.GSLT.Core.BranchingTemporal.Snapshot.mapNodes, chosen, List.map_nil,
          List.head?_nil]
    | cons node rest =>
        have frontier : (project state).search.frontier = projectNode node :: rest.map projectNode := by
          change state.search.frontier.map projectNode = _
          rw [chosen]
          rfl
        simp only [provider, NeedDependentService.Retained.provider, NativeControlCursor.provider,
          NeedDependentService.Retained.pull, coreProvider, corePull,
          Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected,
          Mettapedia.GSLT.Core.BranchingTemporal.selected, controller, coreController,
          RetainedInvocation.controller, Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst,
          chosen, frontier, List.head?_cons]
        simp only [projectNode, NeedExecution.haltedOutcome_project]
        rw [← compared]
        cases haltedOutcome node.state <;> rfl

/-- The actual four receiving plans inherit complete retained-state and
poll-account transport from the constructed one-instruction provider map. -/
theorem mode_run_transport (mode : SourceProducerCardinality.CallingConvention)
    (allowance : Nat) (roots : List Machine) :
    ((run mode allowance roots).1,
      representation.outcome (SourceProducerCardinality.CallingModes.client mode Item)
        (run mode allowance roots).2) =
      Cursor.advance coreProvider (SourceProducerCardinality.CallingModes.client mode Item)
        (fun _ _ => 1) allowance
        (representation.packet (SourceProducerCardinality.CallingModes.client mode Item) (packet mode roots)) :=
  representation.advance_account (SourceProducerCardinality.CallingModes.client mode Item)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => rfl) allowance (packet mode roots)

/-- Already paid pulls and the reply-selected continuation survive a pause.
Neither branch worlds nor an unfinished scalar client are reconstructed from
the published bag at resume. -/
theorem mode_resume_transport (mode : SourceProducerCardinality.CallingConvention) (allowance : Nat)
    (previous : Nat × Cursor.Outcome provider
      (SourceProducerCardinality.CallingModes.client mode Item) ()) :
    ((Cursor.resume provider (SourceProducerCardinality.CallingModes.client mode Item)
        (fun _ _ => 1) allowance previous).1,
      representation.outcome (SourceProducerCardinality.CallingModes.client mode Item)
        (Cursor.resume provider (SourceProducerCardinality.CallingModes.client mode Item)
          (fun _ _ => 1) allowance previous).2) =
      Cursor.resume coreProvider (SourceProducerCardinality.CallingModes.client mode Item)
        (fun _ _ => 1) allowance
        (previous.1, representation.outcome (SourceProducerCardinality.CallingModes.client mode Item) previous.2) :=
  representation.resume_account (SourceProducerCardinality.CallingModes.client mode Item)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => rfl) allowance previous

namespace CurrentData

open _root_.CategoryTheory
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport

variable {DataWorld Entry : Type} {width : Nat} [Category.{0} DataWorld]
  (authority : IndexedAuthority.{0, 0, 0} DataWorld)
  (required : OrderedDependencyStore.Action Entry width → (world : DataWorld) → authority.Fibre world)
  (needed : (world : DataWorld) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Entry width),
    Decidable (FrameUpdate point.authority (required action point.world))]
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]
  (interpret : Nat → OrderedDependencyStore.Action Entry width)

abbrev Context := RetainedInvocation.OwnData.Context authority (Entry := Entry) (width := width)

/-- This profile serializes explicitly emitted effects in one external data
context. Branch-local Need heaps remain in the source inventory and in each
selected item; no branch heap is replaced by that external store. -/
def signal : Control Local Resume Value Empty Fault → Option Nat
  | .run (.rich (.evaluate ⟨_, _, _, .emit event _, _, _, _⟩ _)) _ => some event
  | _ => none

def sourceSignal (state : Inventory) : Option Nat :=
  state.search.frontier.head?.bind fun node => signal node.state.control

def coreSignal (state : CoreInventory) : Option Nat :=
  state.search.frontier.head?.bind fun node => signal node.state.control

theorem signal_representation (state : Inventory) : sourceSignal state = coreSignal (project state) := by
  change state.search.frontier.head?.bind (fun node => signal node.state.control) =
    (state.search.frontier.map projectNode).head?.bind (fun node => signal node.state.control)
  cases state.search.frontier <;> rfl

def sourceTurn := RetainedInvocation.OwnData.step authority required needed interpret sourceTick sourceSignal
def coreTurn := RetainedInvocation.OwnData.step authority required needed interpret coreTick coreSignal

/-- Current permission and read currency are checked before the Need turn.
The actual own-write result is shared by both representations; its new
currency never repairs a historical read premise. -/
theorem turn_representation (source : Inventory) (context : Context authority (Entry := Entry) (width := width)) :
    let moved := sourceTurn authority required needed interpret (source, context)
    ((project moved.1.1, moved.1.2), moved.2) =
      coreTurn authority required needed interpret (project source, context) := by
  dsimp only [sourceTurn, coreTurn]
  unfold RetainedInvocation.OwnData.step
  rw [← signal_representation source]
  split
  · split
    · cases observed : sourceSignal source with
      | none => simp only [tick_representation]
      | some event =>
          simp only
          cases performed : Cursor.ReadOnlyQuery.OwnWrite.step authority required context.live
              (.write (interpret event)) with
          | mk live reply =>
              cases reply with
              | ok unitValue => cases unitValue; simp only [tick_representation]
              | error fault => rfl
    · rfl
  · rfl

def sourceProvider : Cursor.Provider (NativeControlCursor.protocol Item) where
  State _ _ := Inventory × Context authority (Entry := Entry) (width := width)
  step state _ := match state.1.search.frontier with
    | [] => ⟨.done, state⟩
    | node :: _ =>
        let moved := sourceTurn authority required needed interpret state
        match moved.2 with
        | .error _ => ⟨.suspend (), state⟩
        | .ok () => match haltedOutcome node.state with
          | none => ⟨.suspend (), moved.1⟩
          | some answer => ⟨.yield (answer, node.trace, branchWorld node.state) (), moved.1⟩

def targetProvider : Cursor.Provider (NativeControlCursor.protocol Item) where
  State _ _ := CoreInventory × Context authority (Entry := Entry) (width := width)
  step state _ := match state.1.search.frontier with
    | [] => ⟨.done, state⟩
    | node :: _ =>
        let moved := coreTurn authority required needed interpret state
        match moved.2 with
        | .error _ => ⟨.suspend (), state⟩
        | .ok () => match NeedExecution.haltedOutcome node.state with
          | none => ⟨.suspend (), moved.1⟩
          | some answer => ⟨.yield (answer, node.trace, node.state.world) (), moved.1⟩

def representation : Cursor.Hom (sourceProvider authority required needed interpret)
    (targetProvider authority required needed interpret) where
  map state := (project state.1, state.2)
  step state request := by
    rcases state with ⟨source, context⟩
    have compared := turn_representation authority required needed interpret source context
    cases selected : source.search.frontier with
    | nil =>
        have frontier : (project source).search.frontier = [] := by
          change source.search.frontier.map projectNode = []
          rw [selected]
          rfl
        simp only [sourceProvider, targetProvider, selected, frontier]
    | cons node rest =>
        have frontier : (project source).search.frontier = projectNode node :: rest.map projectNode := by
          change source.search.frontier.map projectNode = _
          rw [selected]
          rfl
        simp only [sourceProvider, targetProvider, selected, frontier]
        cases moved : sourceTurn authority required needed interpret (source, context) with
        | mk reached reply =>
            rcases reached with ⟨next, current⟩
            have targetMoved : coreTurn authority required needed interpret (project source, context) =
                ((project next, current), reply) := by
              simpa only [moved] using compared.symm
            simp only [targetMoved]
            cases reply with
            | error reason => rfl
            | ok unitValue =>
                cases unitValue
                simp only [projectNode, NeedExecution.haltedOutcome_project]
                cases haltedOutcome node.state <;> rfl

def sourceGate : OperationCostProtocol.Indexed.Gate (Denied := RetainedInvocation.OwnData.Refused)
    (sourceProvider authority required needed interpret) := fun state _ =>
  RetainedInvocation.OwnData.gate authority required needed interpret sourceSignal state

def targetGate : OperationCostProtocol.Indexed.Gate (Denied := RetainedInvocation.OwnData.Refused)
    (targetProvider authority required needed interpret) := fun state _ =>
  RetainedInvocation.OwnData.gate authority required needed interpret coreSignal state

def profile : OperationCostProtocol.Profile :=
  ⟨"shared-need-source-poll-v1", [("quantum", some .quantum)], .steps, none, .refused⟩

/-- This invoice counts selected source polling work, including an empty
body's disappearing activation. The final exhaustion inspection is free.
Native preparation, callbacks, delivery and physical cost remain separate. -/
def sourceInvoice (origin : Nat) : OperationCostProtocol.Indexed.Invoice
    (sourceProvider authority required needed interpret) := fun state _ =>
  if state.1.search.frontier.isEmpty then [] else
    RetainedInvocation.OwnData.Invocation.pollInvoice origin state.1.memory

def targetInvoice (origin : Nat) : OperationCostProtocol.Indexed.Invoice
    (targetProvider authority required needed interpret) := fun state _ =>
  if state.1.search.frontier.isEmpty then [] else
    RetainedInvocation.OwnData.Invocation.pollInvoice origin state.1.memory

/-- Local state, permission, selected invoice and profile laws construct
the decorated invocation lift. No complete-run agreement is an input. -/
def handler (origin : Nat) : OperationCostProtocol.Indexed.HandlerHom
    (sourceProvider authority required needed interpret) (targetProvider authority required needed interpret)
    (sourceGate authority required needed interpret) (targetGate authority required needed interpret)
    (fun _ => profile) (fun _ => profile) (fun _ => false) (fun _ => false)
    (sourceInvoice authority required needed interpret origin) (targetInvoice authority required needed interpret origin) where
  representation := representation authority required needed interpret
  gate_eq state request := by
    dsimp only [sourceGate, targetGate, representation, RetainedInvocation.OwnData.gate]
    rw [← signal_representation state.1]
  profiles_eq _ := rfl
  replay_eq _ := rfl
  invoice_eq state request := by
    simp only [sourceInvoice, targetInvoice, representation, project,
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapState,
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes,
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapMemory,
      Mettapedia.GSLT.Core.BranchingTemporal.Snapshot.mapNodes, List.isEmpty_map, id_eq]

end CurrentData

end Service

namespace Weighted

open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Core.InferenceControl

/-- An annotation is either authored source in the row's actual cells or an
admitted rich closure. A returned application as Data is not an application
of either callback. -/
inductive Coefficient where
  | authored (expression : Atom)
  | rich (closure : RichClosure)

structure Factor where
  production : AuthoredProduction
  value : Atom

abbrev Word := FreeMonoid Factor

/-- Each job retains both the selected caller and its running callback.
The representation is shared with core jobs below by mapping these two
states, not by serializing either one as authored syntax. -/
structure JobState (State : Type) where
  production : AuthoredProduction
  coefficient : Coefficient
  caller : State
  cursor : State

abbrev Job := JobState Service.Node
abbrev Work := WeightedBranchingResumption.NestedPendingState Service.Node Job
abbrev Result := WeightedBranchingResumption.NestedPendingAnswer Service.Node Service.Node Job Job

def callbackControl (production : AuthoredProduction) : Coefficient → Control Local Resume Value Empty Fault
  | .authored expression => .run (.authored production.program
      (.evaluate expression production.row.environment)) []
  | .rich closure => .run (.rich (.evaluate closure .done)) []

def start (production : AuthoredProduction) (coefficient : Coefficient) (caller : Service.Node) : Job :=
  ⟨production, coefficient, caller,
    ⟨⟨caller.state.world, callbackControl production coefficient, {}⟩, []⟩⟩

def request (annotation : AuthoredProduction → Option Coefficient)
    (before after : Service.Node) (ordinal : Nat) : Word ⊕ Job :=
  match production? before.state ordinal with
  | none => .inl 1
  | some production => match annotation production with
    | none => .inl 1
    | some coefficient => .inr (start production coefficient after)

def nextNodes (before : Service.Node) : List Service.Node :=
  (step before.state).zipIdx.map fun (state, ordinal) => ⟨state, before.trace ++ [ordinal]⟩

/-- Each dispatch performs only one actual shared-source instruction.
Its physical successor position chooses the corresponding row annotation. -/
def body (annotation : AuthoredProduction → Option Coefficient) :
    WeightedBranchingResumption.Coalgebra Service.Node Service.Node (Word ⊕ Job) :=
  fun before => if isHalted before.state then .inl before else
    .inr ((nextNodes before).zipIdx.map fun (after, ordinal) =>
      (after, request annotation before after ordinal))

def grade (annotation : AuthoredProduction → Option Coefficient) :
    WeightedBranchingResumption.Coalgebra Job Job (Word ⊕ Job) :=
  fun job => if isHalted job.cursor.state then .inl job else
    .inr ((nextNodes job.cursor).zipIdx.map fun (after, ordinal) =>
      ({ job with cursor := after }, request annotation job.cursor after ordinal))

/-- Readout is partial and runs only on a genuine callback return. An
uninterpreted result remains a parked job with its original caller. -/
def readout (interpretation : AuthoredProduction → Outcome → Option Atom) (job : Job) : Option Word :=
  (haltedOutcome job.cursor.state).bind fun outcome =>
    (interpretation job.production outcome).map fun value => FreeMonoid.of ⟨job.production, value⟩

def resumeNode (caller : Service.Node) (job : Job) : Service.Node :=
  { caller with
    state := { caller.state with
      world := job.cursor.state.world
      work := caller.state.work.add job.cursor.state.work } }

def resumeJob (parent child : Job) : Job :=
  { parent with cursor := resumeNode parent.cursor child }

/-- The maintained nested handler supplies all parent suspension and
restoration. The body and every callback use the same shared-source machine. -/
def source (annotation : AuthoredProduction → Option Coefficient)
    (interpretation : AuthoredProduction → Outcome → Option Atom) :
    WeightedBranchingResumption.Coalgebra Work Result Word :=
  WeightedBranchingResumption.nestedPendingSource (body annotation) (grade annotation)
    (readout interpretation) resumeNode resumeJob

theorem fresh_callback_keeps_the_selected_world (production : AuthoredProduction)
    (coefficient : Coefficient) (caller : Service.Node) :
    (start production coefficient caller).caller = caller ∧
      (start production coefficient caller).cursor.state.world = caller.state.world ∧
      (start production coefficient caller).cursor.state.work = {} := ⟨rfl, rfl, rfl⟩

/-- A callback can start only from an actual authored activation. Its exact
selected successor is the captured caller, and fresh callback work is zero. -/
theorem requested_job_is_captured (annotation : AuthoredProduction → Option Coefficient)
    (before after : Service.Node) (ordinal : Nat) (job : Job)
    (requested : request annotation before after ordinal = .inr job) :
    job.caller = after ∧ job.cursor.state.world = after.state.world ∧
      job.cursor.state.work = {} ∧
      NativeEquationNeed.Activates job.production.program job.production.head job.production.arguments
        (.equation job.production.row.index)
        (.evaluate job.production.row.body job.production.row.environment) := by
  unfold request at requested
  cases selected : production? before.state ordinal with
  | none => simp only [selected] at requested; cases requested
  | some production =>
      simp only [selected] at requested
      cases attached : annotation production with
      | none => simp only [attached] at requested; cases requested
      | some coefficient =>
          simp only [attached, Sum.inr.injEq] at requested
          subst job
          exact ⟨rfl, rfl, rfl, production_has_activation selected⟩

theorem cached_delivery_starts_no_callback (annotation : AuthoredProduction → Option Coefficient)
    (world : World) (cell : CellId) (origin : Origin) (value : Value)
    (stack : List (Frame Resume)) (work : NeedReference.Work) (ordinal : Nat)
    (trace : WorldPath) (after : Service.Node)
    (cached : world.heap.lookup cell = some ⟨origin, .value value⟩) :
    request annotation ⟨⟨world, .force cell stack, work⟩, trace⟩ after ordinal = .inl 1 := by
  simp only [request, cached_delivery_has_no_authored_production world cell origin value stack work ordinal cached]

/-- Restoring the caller uses the actual callback world and adds its work
once. The captured future control and occurrence identity are not replaced by
the minimal support of the returned coefficient value. -/
theorem callback_restores_the_full_caller (caller : Service.Node) (job : Job) :
    (resumeNode caller job).state.control = caller.state.control ∧
      (resumeNode caller job).trace = caller.trace ∧
      (resumeNode caller job).state.world = job.cursor.state.world ∧
      (resumeNode caller job).state.work = caller.state.work.add job.cursor.state.work :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The complete nested retained stack has actual caller agreement at every
finite cut, derived from fresh captures and real parent restoration. -/
theorem retained_caller_agreement (annotation : AuthoredProduction → Option Coefficient)
    (interpretation : AuthoredProduction → Outcome → Option Atom) (fuel : Nat) (before : Service.Node) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions (source annotation interpretation) fuel (.inl before),
      Sum.elim
        (WeightedBranchingResumption.nestedResultCallerAgreement id JobState.cursor JobState.caller)
        (WeightedBranchingResumption.nestedWorkCallerAgreement id JobState.cursor JobState.caller) leaf.1 := by
  apply WeightedBranchingResumption.nested_contributions_caller_agreement
    (body annotation) (grade annotation) (readout interpretation) resumeNode resumeJob
    id JobState.cursor JobState.caller ?_ ?_ ?_ ?_ fuel (.inl before) True.intro
  · intro state alternatives inspected next member job requested
    cases stopped : isHalted state.state with
    | true => simp only [body, stopped, ↓reduceIte] at inspected; cases inspected
    | false =>
        simp only [body, stopped, Bool.false_eq_true, ↓reduceIte, Sum.inr.injEq] at inspected
        subst alternatives
        obtain ⟨⟨after, ordinal⟩, _, rfl⟩ := List.mem_map.mp member
        exact (requested_job_is_captured annotation state after ordinal job requested).1
  · intro job result returned
    cases stopped : isHalted job.cursor.state with
    | false => simp only [grade, stopped, Bool.false_eq_true, ↓reduceIte] at returned; cases returned
    | true =>
        simp only [grade, stopped, ↓reduceIte, Sum.inl.injEq] at returned
        subst result
        rfl
  · intro job alternatives inspected next member
    cases stopped : isHalted job.cursor.state with
    | true => simp only [grade, stopped, ↓reduceIte] at inspected; cases inspected
    | false =>
        simp only [grade, stopped, Bool.false_eq_true, ↓reduceIte, Sum.inr.injEq] at inspected
        subst alternatives
        obtain ⟨⟨after, ordinal⟩, _, rfl⟩ := List.mem_map.mp member
        refine ⟨rfl, ?_⟩
        cases requested : request annotation job.cursor after ordinal with
        | inl value => exact True.intro
        | inr child => exact (requested_job_is_captured annotation job.cursor after ordinal child requested).1
  · intro parent child
    rfl

theorem a_returned_but_uninterpreted_callback_retains_its_caller
    (annotation : AuthoredProduction → Option Coefficient)
    (interpretation : AuthoredProduction → Outcome → Option Atom)
    (caller : Service.Node) (job : Job) (parents : List Job)
    (returned : isHalted job.cursor.state = true) (uninterpreted : readout interpretation job = none) :
    source annotation interpretation (.inr (caller, job, parents)) = .inl (.inr (caller, job, parents)) := by
  simp only [source, WeightedBranchingResumption.nestedPendingSource, grade, returned, ↓reduceIte, uninterpreted]

/-- An interpreted callback contributes exactly one ordered factor before
the preserved caller is runnable again. -/
theorem interpreted_callback_resumes_once (annotation : AuthoredProduction → Option Coefficient)
    (interpretation : AuthoredProduction → Outcome → Option Atom) (caller : Service.Node) (job : Job)
    (factor : Word) (returned : isHalted job.cursor.state = true)
    (interpreted : readout interpretation job = some factor) :
    source annotation interpretation (.inr (caller, job, [])) =
      .inr [(.inl (resumeNode caller job), factor)] := by
  simp only [source, WeightedBranchingResumption.nestedPendingSource, grade, returned, ↓reduceIte, interpreted]

/-- The exact finite-cut composition preserves every branch's own copied
factor prefix and retained callback stack. No commutativity is assumed. -/
theorem resume_exact (annotation : AuthoredProduction → Option Coefficient)
    (interpretation : AuthoredProduction → Outcome → Option Atom) (first second : Nat) (before : Work) :
    WeightedBranchingResumption.contributions (source annotation interpretation) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions (source annotation interpretation) first before)
        (fun leaf => match leaf with
          | .inl answer => [(.inl answer, (1 : Word))]
          | .inr pending => WeightedBranchingResumption.contributions
              (source annotation interpretation) second pending) := by
  rw [WeightedBranchingResumption.contributions_add]
  apply congrArg (WeightedResumption.sequence
    (WeightedBranchingResumption.contributions (source annotation interpretation) first before))
  funext leaf
  cases leaf <;> rfl

abbrev CoreJob := JobState Service.CoreNode
abbrev CoreWork := WeightedBranchingResumption.NestedPendingState Service.CoreNode CoreJob
abbrev CoreResult := WeightedBranchingResumption.NestedPendingAnswer Service.CoreNode Service.CoreNode CoreJob CoreJob

def coreProduction? (machine : CoreMachine) (ordinal : Nat) : Option AuthoredProduction :=
  (NeedDependentService.SourceBranch.inspectCore specification machine ordinal).bind
    (fun selected => productionOf selected machine.world.path ordinal)

theorem production_projection (machine : Machine) (ordinal : Nat) :
    coreProduction? (NeedExecution.projectMachine false machine) ordinal = production? machine ordinal := rfl

def mapJob (job : Job) : CoreJob :=
  ⟨job.production, job.coefficient, Service.projectNode job.caller, Service.projectNode job.cursor⟩

def mapWork : Work → CoreWork :=
  Sum.map Service.projectNode fun held =>
    (Service.projectNode held.1, mapJob held.2.1, held.2.2.map mapJob)

def mapResult : Result → CoreResult := mapWork

def coreStart (production : AuthoredProduction) (coefficient : Coefficient) (caller : Service.CoreNode) : CoreJob :=
  ⟨production, coefficient, caller,
    ⟨⟨caller.state.world, callbackControl production coefficient, {}⟩, []⟩⟩

def coreRequest (annotation : AuthoredProduction → Option Coefficient)
    (before after : Service.CoreNode) (ordinal : Nat) : Word ⊕ CoreJob :=
  match coreProduction? before.state ordinal with
  | none => .inl 1
  | some production => match annotation production with
    | none => .inl 1
    | some coefficient => .inr (coreStart production coefficient after)

def coreNextNodes (before : Service.CoreNode) : List Service.CoreNode :=
  (coreStep before.state).zipIdx.map fun (state, ordinal) => ⟨state, before.trace ++ [ordinal]⟩

def coreBody (annotation : AuthoredProduction → Option Coefficient) :
    WeightedBranchingResumption.Coalgebra Service.CoreNode Service.CoreNode (Word ⊕ CoreJob) :=
  fun before => if NeedExecution.isHalted before.state then .inl before else
    .inr ((coreNextNodes before).zipIdx.map fun (after, ordinal) =>
      (after, coreRequest annotation before after ordinal))

def coreGrade (annotation : AuthoredProduction → Option Coefficient) :
    WeightedBranchingResumption.Coalgebra CoreJob CoreJob (Word ⊕ CoreJob) :=
  fun job => if NeedExecution.isHalted job.cursor.state then .inl job else
    .inr ((coreNextNodes job.cursor).zipIdx.map fun (after, ordinal) =>
      ({ job with cursor := after }, coreRequest annotation job.cursor after ordinal))

def coreReadout (interpretation : AuthoredProduction → Outcome → Option Atom) (job : CoreJob) : Option Word :=
  (NeedExecution.haltedOutcome job.cursor.state).bind fun outcome =>
    (interpretation job.production outcome).map fun value => FreeMonoid.of ⟨job.production, value⟩

def coreResumeNode (caller : Service.CoreNode) (job : CoreJob) : Service.CoreNode :=
  { caller with
    state := { caller.state with
      world := job.cursor.state.world
      work := caller.state.work.add job.cursor.state.work } }

def coreResumeJob (parent child : CoreJob) : CoreJob :=
  { parent with cursor := coreResumeNode parent.cursor child }

def coreSource (annotation : AuthoredProduction → Option Coefficient)
    (interpretation : AuthoredProduction → Outcome → Option Atom) :
    WeightedBranchingResumption.Coalgebra CoreWork CoreResult Word :=
  WeightedBranchingResumption.nestedPendingSource (coreBody annotation) (coreGrade annotation)
    (coreReadout interpretation) coreResumeNode coreResumeJob

theorem request_projection (annotation : AuthoredProduction → Option Coefficient)
    (before after : Service.Node) (ordinal : Nat) :
    coreRequest annotation (Service.projectNode before) (Service.projectNode after) ordinal =
      Sum.map id mapJob (request annotation before after ordinal) := by
  simp only [coreRequest, request, Service.projectNode, production_projection]
  cases production? before.state ordinal with
  | none => rfl
  | some production =>
      dsimp only
      cases annotation production <;> rfl

theorem next_projection (before : Service.Node) :
    coreNextNodes (Service.projectNode before) = (nextNodes before).map Service.projectNode := by
  simp only [coreNextNodes, nextNodes, Service.projectNode]
  rw [← project_step false]
  simp only [List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq]
  rfl

theorem body_projection (annotation : AuthoredProduction → Option Coefficient) (before : Service.Node) :
    coreBody annotation (Service.projectNode before) =
      match body annotation before with
      | .inl answer => .inl (Service.projectNode answer)
      | .inr alternatives => .inr (alternatives.map fun next =>
          (Service.projectNode next.1, Sum.map id mapJob next.2)) := by
  have stopped : NeedExecution.isHalted (Service.projectNode before).state = isHalted before.state := rfl
  simp only [coreBody, stopped, body]
  cases isHalted before.state with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, next_projection, List.zipIdx_map, List.map_map]
      congr 2
      funext pair
      exact congrArg (fun factor => (Service.projectNode pair.1, factor))
        (request_projection annotation before pair.1 pair.2)

theorem grade_projection (annotation : AuthoredProduction → Option Coefficient) (job : Job) :
    coreGrade annotation (mapJob job) =
      match grade annotation job with
      | .inl result => .inl (mapJob result)
      | .inr alternatives => .inr (alternatives.map fun next =>
          (mapJob next.1, Sum.map id mapJob next.2)) := by
  have stopped : NeedExecution.isHalted (mapJob job).cursor.state = isHalted job.cursor.state := rfl
  simp only [coreGrade, stopped, grade]
  cases isHalted job.cursor.state with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, mapJob, next_projection, List.zipIdx_map, List.map_map]
      congr 2
      funext pair
      exact congrArg (fun factor => (mapJob { job with cursor := pair.1 }, factor))
        (request_projection annotation job.cursor pair.1 pair.2)

theorem readout_projection (interpretation : AuthoredProduction → Outcome → Option Atom) (job : Job) :
    coreReadout interpretation (mapJob job) = readout interpretation job := by
  simp only [coreReadout, readout, mapJob, Service.projectNode, NeedExecution.haltedOutcome_project]

theorem resume_node_projection (caller : Service.Node) (job : Job) :
    coreResumeNode (Service.projectNode caller) (mapJob job) = Service.projectNode (resumeNode caller job) := rfl

theorem resume_job_projection (parent child : Job) :
    coreResumeJob (mapJob parent) (mapJob child) = mapJob (resumeJob parent child) := rfl

/-- The actual callback phases, including parked results and nested parent
restoration, commute locally with receipt-policy execution. -/
theorem source_projection (annotation : AuthoredProduction → Option Coefficient)
    (interpretation : AuthoredProduction → Outcome → Option Atom) (before : Work) :
    coreSource annotation interpretation (mapWork before) =
      match source annotation interpretation before with
      | .inl answer => .inl (mapResult answer)
      | .inr alternatives => .inr (alternatives.map fun next => (mapWork next.1, next.2)) := by
  cases before with
  | inl state =>
      simp only [source, coreSource, WeightedBranchingResumption.nestedPendingSource,
        mapWork, Sum.map_inl, body_projection]
      cases selected : body annotation state with
      | inl answer => rfl
      | inr alternatives =>
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          rintro ⟨next, coefficient⟩ _
          dsimp only [Function.comp_apply]
          cases coefficient <;> rfl
  | inr held =>
      rcases held with ⟨state, job, parents⟩
      simp only [source, coreSource, WeightedBranchingResumption.nestedPendingSource,
        mapWork, Sum.map_inr, grade_projection]
      cases selected : grade annotation job with
      | inr alternatives =>
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          rintro ⟨next, coefficient⟩ _
          dsimp only [Function.comp_apply]
          cases coefficient <;> rfl
      | inl result =>
          simp only [readout_projection]
          cases interpreted : readout interpretation result with
          | none => rfl
          | some factor =>
              cases parents with
              | nil => simp only [List.map_nil, resume_node_projection]; rfl
              | cons parent rest =>
                  simp only [List.map_cons, resume_job_projection]
                  rfl

/-- The local phase square derives full finite-cut agreement, preserving
ordered occurrence multiplicity, parked/runnable distinction, every captured
caller and each selected branch's factor word. -/
theorem retained_transport (annotation : AuthoredProduction → Option Coefficient)
    (interpretation : AuthoredProduction → Outcome → Option Atom) (fuel : Nat) (before : Work) :
    WeightedBranchingResumption.contributions (coreSource annotation interpretation) fuel (mapWork before) =
      (WeightedBranchingResumption.contributions (source annotation interpretation) fuel before).map
        (fun leaf => (Sum.map mapResult mapWork leaf.1, leaf.2)) := by
  apply WeightedBranchingResumption.contributions_reindex (source annotation interpretation)
    (coreSource annotation interpretation) mapWork mapResult ?_ fuel before
  intro state
  have compared := source_projection annotation interpretation state
  cases observed : source annotation interpretation state <;> simpa only [observed] using compared

namespace Provider

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Machines

abbrev Item := (Service.CoreNode × Word) × WorldPath
abbrev Node := WorkOccurrence (Work × Word)
abbrev CoreNode := WorkOccurrence (CoreWork × Word)
abbrev Inventory := Mettapedia.GSLT.Core.InferenceControl.Snapshot Node Item Nat
abbrev CoreInventory := Mettapedia.GSLT.Core.InferenceControl.Snapshot CoreNode Item Nat

variable (annotation : AuthoredProduction → Option Coefficient)
  (interpretation : AuthoredProduction → Outcome → Option Atom)

/-- The declared observation maps only emitted results. Its origin keeps the
entire rich body/callback state, while each agenda node carries its own word. -/
def sourceBase : BranchingSystem (Work × Word) (Service.CoreNode × Word) where
  emit state := match Weighted.source annotation interpretation state.1 with
    | .inl (.inl answer) => some (Service.projectNode answer, state.2)
    | _ => none
  successors state := match Weighted.source annotation interpretation state.1 with
    | .inl (.inl _) => []
    | .inl (.inr _) => [state]
    | .inr alternatives => alternatives.map fun next => (next.1, state.2 * next.2)

/-- A parked cut result is still an unfinished invocation. It remains in the
agenda with its exact caller, callback, parents and word; only a body return
may be emitted. Reinspection does not rerun the completed callback. -/
def targetBase : BranchingSystem (CoreWork × Word) (Service.CoreNode × Word) where
  emit state := match coreSource annotation interpretation state.1 with
    | .inl (.inl answer) => some (answer, state.2)
    | _ => none
  successors state := match coreSource annotation interpretation state.1 with
    | .inl (.inl _) => []
    | .inl (.inr _) => [state]
    | .inr alternatives => alternatives.map fun next => (next.1, state.2 * next.2)

theorem parked_source_is_retained (work : Work) (carried : Word)
    (held : Service.Node × Job × List Job)
    (parked : Weighted.source annotation interpretation work = .inl (.inr held)) :
    (sourceBase annotation interpretation).emit (work, carried) = none ∧
      (sourceBase annotation interpretation).successors (work, carried) = [(work, carried)] := by
  simp [sourceBase, parked]

theorem parked_target_is_retained (work : CoreWork) (carried : Word)
    (held : Service.CoreNode × CoreJob × List CoreJob)
    (parked : coreSource annotation interpretation work = .inl (.inr held)) :
    (targetBase annotation interpretation).emit (work, carried) = none ∧
      (targetBase annotation interpretation).successors (work, carried) = [(work, carried)] := by
  simp [targetBase, parked]
def sourceSystem := WorkOccurrence.lift (sourceBase annotation interpretation)
def targetSystem := WorkOccurrence.lift (targetBase annotation interpretation)
def controller := RetainedInvocation.controller Node Item
def coreController := RetainedInvocation.controller CoreNode Item

def mapNode (node : Node) : CoreNode := ⟨(mapWork node.state.1, node.state.2), node.trace⟩
def project (inventory : Inventory) : CoreInventory := inventory.mapState mapNode id

theorem local_emit (node : Node) :
    (sourceSystem annotation interpretation).emit node =
      (targetSystem annotation interpretation).emit (mapNode node) := by
  simp only [sourceSystem, targetSystem, WorkOccurrence.lift, sourceBase, targetBase,
    mapNode]
  rw [source_projection]
  cases Weighted.source annotation interpretation node.state.1 with
  | inl answer => cases answer <;> rfl
  | inr alternatives => rfl

theorem local_successors (node : Node) :
    ((sourceSystem annotation interpretation).successors node).map mapNode =
      (targetSystem annotation interpretation).successors (mapNode node) := by
  simp only [sourceSystem, targetSystem, WorkOccurrence.lift, sourceBase, targetBase,
    mapNode]
  rw [source_projection]
  cases Weighted.source annotation interpretation node.state.1 with
  | inl answer => cases answer <;> rfl
  | inr alternatives =>
      simp only [List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq]
      rfl

def sourceTick := Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick (sourceSystem annotation interpretation) controller
def targetTick := Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick (targetSystem annotation interpretation) coreController

theorem tick_representation (inventory : Inventory) :
    project (sourceTick annotation interpretation inventory) =
      targetTick annotation interpretation (project inventory) := by
  exact Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick_mapState mapNode id
    (sourceSystem annotation interpretation) (targetSystem annotation interpretation) controller coreController
    (local_emit annotation interpretation) (local_successors annotation interpretation) (fun _ _ => rfl)
    (fun _ _ _ => by simp [controller, coreController, RetainedInvocation.controller,
      Scheduler.breadthFirst, List.map_append]) (fun _ _ _ _ => rfl) inventory

def sourcePull (inventory : Inventory) : HostCalls.Pull Inventory Item :=
  match Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected controller inventory with
  | none => .done
  | some node =>
      let reached := sourceTick annotation interpretation inventory
      match (sourceSystem annotation interpretation).emit node with
      | none => .suspend reached
      | some item => .yield item reached

def targetPull (inventory : CoreInventory) : HostCalls.Pull CoreInventory Item :=
  match Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected coreController inventory with
  | none => .done
  | some node =>
      let reached := targetTick annotation interpretation inventory
      match (targetSystem annotation interpretation).emit node with
      | none => .suspend reached
      | some item => .yield item reached

def sourceProvider := NativeControlCursor.provider (sourcePull annotation interpretation)
def targetProvider := NativeControlCursor.provider (targetPull annotation interpretation)

/-- This local cursor lift preserves exact callback phases, residual branch
worlds, selected item worlds and copied factor words under any adaptive client. -/
def representation : Cursor.Hom (sourceProvider annotation interpretation) (targetProvider annotation interpretation) where
  map := project
  step inventory request := by
    have compared := tick_representation annotation interpretation inventory
    cases selected : inventory.search.frontier with
    | nil =>
        simp only [sourceProvider, targetProvider, NativeControlCursor.provider, sourcePull, targetPull,
          Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected, BranchingTemporal.selected,
          controller, coreController, RetainedInvocation.controller, Scheduler.breadthFirst,
          project, Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapState,
          Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes,
          Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapMemory, BranchingTemporal.Snapshot.mapNodes,
          selected, List.map_nil, List.head?_nil]
    | cons node rest =>
        have frontier : (project inventory).search.frontier = mapNode node :: rest.map mapNode := by
          change inventory.search.frontier.map mapNode = _
          rw [selected]
          rfl
        simp only [sourceProvider, targetProvider, NativeControlCursor.provider, sourcePull, targetPull,
          Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected, BranchingTemporal.selected,
          controller, coreController, RetainedInvocation.controller, Scheduler.breadthFirst,
          selected, frontier, List.head?_cons]
        rw [← compared, ← local_emit annotation interpretation node]
        cases (sourceSystem annotation interpretation).emit node <;> rfl

/-- Logical selected-source inspections, including a parked reinspection,
are distinct from callback instructions, factor multiplication and all
native preparation/delivery/physical costs. -/
def sourceCharge : Cursor.Charge (sourceProvider annotation interpretation) := fun inventory _ =>
  if inventory.search.frontier.isEmpty then 0 else 1

def targetCharge : Cursor.Charge (targetProvider annotation interpretation) := fun inventory _ =>
  if inventory.search.frontier.isEmpty then 0 else 1

theorem charge_representation {base index : Unit}
    (inventory : (sourceProvider annotation interpretation).State base index) (request : Unit) :
    sourceCharge annotation interpretation inventory request =
      targetCharge annotation interpretation ((representation annotation interpretation).map inventory) request := by
  simp only [sourceCharge, targetCharge, representation, project,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapState,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapMemory, BranchingTemporal.Snapshot.mapNodes,
    List.isEmpty_map]

/-- A received root has its own current Need world and coefficient prefix.
Re-entering an exported callable threads both; replaying an old immutable
root is a separate execution rather than an update to a mutable cache. -/
def initial (roots : List (Service.Node × Word)) : Inventory :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller
    (roots.map fun (node, carried) => WorkOccurrence.root (.inl node, carried))

def packet (mode : SourceProducerCardinality.CallingConvention) (roots : List (Service.Node × Word)) :=
  SourceProducerCardinality.CallingModes.start mode (sourceProvider annotation interpretation) (initial roots)

def run (mode : SourceProducerCardinality.CallingConvention) (allowance : Nat) (roots : List (Service.Node × Word)) :=
  Cursor.advance (sourceProvider annotation interpretation) (SourceProducerCardinality.CallingModes.client mode Item)
    (sourceCharge annotation interpretation) allowance (packet annotation interpretation mode roots)

theorem mode_run_transport (mode : SourceProducerCardinality.CallingConvention) (allowance : Nat)
    (roots : List (Service.Node × Word)) :
    ((run annotation interpretation mode allowance roots).1,
      (representation annotation interpretation).outcome (SourceProducerCardinality.CallingModes.client mode Item)
        (run annotation interpretation mode allowance roots).2) =
      Cursor.advance (targetProvider annotation interpretation) (SourceProducerCardinality.CallingModes.client mode Item)
        (targetCharge annotation interpretation) allowance
        ((representation annotation interpretation).packet (SourceProducerCardinality.CallingModes.client mode Item)
          (packet annotation interpretation mode roots)) :=
  (representation annotation interpretation).advance_account (SourceProducerCardinality.CallingModes.client mode Item)
    (sourceCharge annotation interpretation) (targetCharge annotation interpretation)
    (charge_representation annotation interpretation) allowance (packet annotation interpretation mode roots)

theorem mode_resume_transport (mode : SourceProducerCardinality.CallingConvention) (allowance : Nat)
    (previous : Nat × Cursor.Outcome (sourceProvider annotation interpretation)
      (SourceProducerCardinality.CallingModes.client mode Item) ()) :
    ((Cursor.resume (sourceProvider annotation interpretation) (SourceProducerCardinality.CallingModes.client mode Item)
        (sourceCharge annotation interpretation) allowance previous).1,
      (representation annotation interpretation).outcome (SourceProducerCardinality.CallingModes.client mode Item)
        (Cursor.resume (sourceProvider annotation interpretation) (SourceProducerCardinality.CallingModes.client mode Item)
          (sourceCharge annotation interpretation) allowance previous).2) =
      Cursor.resume (targetProvider annotation interpretation) (SourceProducerCardinality.CallingModes.client mode Item)
        (targetCharge annotation interpretation) allowance
        (previous.1, (representation annotation interpretation).outcome
          (SourceProducerCardinality.CallingModes.client mode Item) previous.2) :=
  (representation annotation interpretation).resume_account (SourceProducerCardinality.CallingModes.client mode Item)
    (sourceCharge annotation interpretation) (targetCharge annotation interpretation)
    (charge_representation annotation interpretation) allowance previous

end Provider

end Weighted

namespace Controls

open PolarizedNeed (Computation Value)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Machines

abbrev Code := Computation Atom Operation Nat 0 0 0
abbrev Runtime := PolarizedNeedMachine.RuntimeValue Atom Operation Nat 0

def integer (number : Int) : Atom := .grounded (.int number)

def program : NativeEquationNeed.Program :=
  [⟨"choose", ["x"], .var "x"⟩,
   ⟨"choose", ["x"], .expression [.symbol "+", .var "x", integer 1]⟩]

def emptyWorld : World := ⟨0, [], .empty, .empty, 0, 0⟩

def load (world : World) (code : Code) : Machine :=
  ⟨world, .run (.rich (.evaluate ⟨0, 0, 0, code, ids, Fin.elim0, Fin.elim0⟩ .done)) [], {}⟩

def run (steps : Nat) (machine : Machine) : List Machine :=
  NeedLocalSteps.runFrontier extension steps [machine]

def exportShared : Code :=
  .letNeed (.emit 7 (.returnValue (.native (.head (integer 7)))))
    (.letNeed (.call (.source program [("x", 0)]) (.head (.expression [.symbol "choose", .var "x"])))
      (.returnValue (.thunk (.nativeLambda (.sequenceSigma (.forceNeed 0) (.forceNeed 0))))))

def returned (machine : Machine) : Option (Runtime × World) :=
  match haltedOutcome machine with
  | some (.value value) => match richView value with
    | .returned value => some (value, machine.world)
    | _ => none
  | _ => none

def exported := (run 100 (load emptyWorld exportShared)).findSome? returned

def invoke (value : Runtime) (world : World) : Machine :=
  ⟨world, .run (.rich (.evaluate
    ⟨0, 1, 0, .nativeApply (.forceThunk (.variable 0)) (.head (.symbol "Unit")),
      ids, Fin.cases value Fin.elim0, Fin.elim0⟩ .done)) [], {}⟩

def resultTerm (machine : Machine) : Option (Tm Atom 0) :=
  match haltedOutcome machine with
  | some (.value value) => match richView value with
    | .returned (.native term) => some term
    | _ => none
  | _ => none

def effects (world : World) : List Nat := world.receipts.effects

def invokeExport := exported.map fun (value, world) => run 240 (invoke value world)

/-- Export allocates both actual Need cells without forcing the authored
source or its borrowed argument producer. -/
theorem actual_export_is_unforced :
    exported.map (fun pair => (pair.2.nextCell, effects pair.2)) = some (2, []) := by
  decide +kernel

/-- An actual authored source is forced through a captured rich callable.
Each branch returns a correlated pair and shares its borrowed producer once. -/
theorem exported_rich_callable_runs_actual_authored_source :
    invokeExport.map (fun states => states.filterMap resultTerm) =
      some [.pair (.head (integer 7)) (.head (integer 7)),
        .pair (.head (integer 8)) (.head (integer 8))] ∧
      invokeExport.map (fun states => states.map (fun state => effects state.world)) =
        some [[7], [7]] := by
  decide +kernel

/-- The raw atomic profile refuses this source operation. The enabled result
above therefore depends on the actual allocate/demand/resume bridge. -/
theorem source_is_not_an_atomic_primitive_alias :
    primitive (.source program [("x", 0)]) (.head (.expression [.symbol "choose", .var "x"])) =
      .retryableFault (.domain "source requires the shared invocation profile") := rfl

/-- The native-data view is deliberately partial. A captured callable is
retained as rich code and cannot masquerade as an authored atom or row. -/
theorem native_data_projection_refuses_an_exported_callable :
    exported.map (fun pair => nativeView (richValue (.returned pair.1))) = some none := by
  decide +kernel

def sourceFault (machine : Machine) : Bool :=
  match haltedOutcome machine with
  | some (.retryableFault (.noRule _)) => true
  | _ => false

def noMatchingArity : Code :=
  .call (.source program []) (.head (.expression [.symbol "choose"]))

/-- An empty authored row scan follows the existing no-rule fault path. It
is not a successful empty answer collection. -/
theorem unmatched_authored_application_is_a_real_retryable_fault :
    (run 160 (load emptyWorld noMatchingArity)).map sourceFault = [true] := by
  decide +kernel

/-- Both aliasing and range checks occur before creating the authored origin.
Copied names cannot silently replace another captured cell binding. -/
theorem checked_source_bindings_preserve_aliases_and_refuse_forgery :
    resolveBindings (fun (_ : Fin 1) => (⟨0, [], 9, 0⟩ : CellId)) [("x", 0), ("y", 0)] =
      some [("x", ⟨0, [], 9, 0⟩), ("y", ⟨0, [], 9, 0⟩)] ∧
      resolveBindings (fun (_ : Fin 1) => (⟨0, [], 9, 0⟩ : CellId)) [("x", 1)] = none ∧
      resolveBindings (fun (_ : Fin 1) => (⟨0, [], 9, 0⟩ : CellId)) [("x", 0), ("x", 0)] = none := by
  decide +kernel

def scalarSource : Code :=
  .call (.source [⟨"one", [], integer 41⟩] []) (.head (.expression [.symbol "one"]))

/-- Calling modes consume the same nontrivial source provider. Producer mode
retains the whole initial world inventory without any poll. -/
theorem actual_zero_one_many_and_unfinished_source_modes :
    Service.summary .optional 100 [] = some (true, 0, 0) ∧
      Service.summary .direct 100 [] = some (false, 0, 0) ∧
      Service.summary .direct 200 [load emptyWorld scalarSource] = some (true, 1, 0) ∧
      Service.summary .producer 1 [load emptyWorld scalarSource] = some (true, 0, 1) ∧
      (Service.run .producer 1 [load emptyWorld scalarSource]).1 = 0 ∧
      Service.summary .optional 0 [load emptyWorld scalarSource] = none := by
  decide +kernel

/-- No-rule remains a faulted occurrence after source-mode decoding. Empty
inventory and a failed application therefore have different meanings. -/
theorem source_fault_is_not_optional_exhaustion :
    Service.summary .optional 200 [load emptyWorld noMatchingArity] = some (false, 1, 0) := by
  decide +kernel

def invokeRoots := exported.toList.map fun (value, world) => invoke value world

/-- Nonempty receiving retains the source's unconsumed branch inventory;
scalar incompatibility retains both equal-or-distinct physical occurrences. -/
theorem mixed_source_modes_keep_the_actual_remaining_worlds :
    Service.summary .nonemptyProducer 300 invokeRoots = some (true, 1, 1) ∧
      Service.summary .direct 300 invokeRoots = some (false, 2, 0) ∧
      Service.summary .producer 1 invokeRoots = some (true, 0, 1) := by
  decide +kernel

def finiteSource (bodies : List Atom) : Code :=
  .call (.frontier program []) (.head (.expression bodies))

def rowView (item : Service.Item) : Option Atom × WorldPath × WorldPath :=
  ((match item.1 with | .value value => nativeView value | _ => none), item.2.1, item.2.2.path)

def receivedRows (mode : SourceProducerCardinality.CallingConvention)
    (allowance : Nat) (roots : List Machine) :=
  match Service.receive mode (Service.run mode allowance roots).2 with
  | .inl _ => none
  | .inr (result, _) => some (result.rows.map rowView)

/-- The empty source body is reached through the actual rich continuation.
It exhausts normally, whereas returning the same empty atom as Data produces
one value and a no-rule source still produces its fault occurrence. -/
theorem empty_source_body_is_not_empty_data_or_a_fault :
    Service.summary .optional 30 [load emptyWorld (.emit 9 (finiteSource []))] = some (true, 0, 0) ∧
      Service.summary .direct 30 [load emptyWorld (finiteSource [])] = some (false, 0, 0) ∧
      Service.summary .direct 30 [load emptyWorld (.returnValue (.native (.head (.expression []))))] =
        some (true, 1, 0) ∧
      Service.summary .optional 200 [load emptyWorld noMatchingArity] = some (false, 1, 0) := by
  decide +kernel

/-- Equal bodies remain distinct source occurrences. Their values agree but
their selected branch-world paths do not, and nonempty mode leaves the other
branch available instead of collecting it eagerly. -/
theorem finite_source_keeps_duplicate_occurrences_and_selected_worlds :
    Service.summary .direct 100 [load emptyWorld (finiteSource [integer 7, integer 7])] =
        some (false, 2, 0) ∧
      Service.summary .nonemptyProducer 100 [load emptyWorld (finiteSource [integer 7, integer 7])] =
        some (true, 1, 1) ∧
      (receivedRows .direct 100 [load emptyWorld (finiteSource [integer 7, integer 7])]).map
        (fun rows => rows.map fun row => row.1) = some [some (integer 7), some (integer 7)] ∧
      (receivedRows .direct 100 [load emptyWorld (finiteSource [integer 7, integer 7])]).map
        (fun rows => rows.map fun row => row.2.2) = some [[0, 0], [1, 0]] := by
  decide +kernel

/-- A body in the declared inventory is evaluated by the ordinary source
machine. A malformed application does not disappear as an empty branch. -/
theorem finite_source_does_not_filter_failed_bodies :
    Service.summary .optional 200
      [load emptyWorld (finiteSource [.expression [.symbol "choose"]])] = some (false, 1, 0) := by
  decide +kernel

namespace CurrentData

open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.SeparationAlgebra

abbrev required := RetainedInvocation.Examples.OwnData.required
abbrev needed := RetainedInvocation.Examples.OwnData.needed
abbrev context := RetainedInvocation.Examples.OwnData.context

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (required change point.world)) :=
  RetainedInvocation.Examples.OwnData.permissionDecision point change

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) :=
  RetainedInvocation.Examples.OwnData.admissionDecision point

def act (event : Nat) : OrderedDependencyStore.Action Nat 3 := .append 0 [event]
abbrev raw := Service.CurrentData.sourceProvider revocationWorlds required needed act
abbrev guard : OperationCostProtocol.Indexed.Gate (Denied := RetainedInvocation.OwnData.Refused) raw :=
  Service.CurrentData.sourceGate revocationWorlds required needed act
abbrev invoice : OperationCostProtocol.Indexed.Invoice raw :=
  Service.CurrentData.sourceInvoice revocationWorlds required needed act 203
def profiles : {_base _index : Unit} → Unit → OperationCostProtocol.Profile := fun _ => Service.CurrentData.profile
def replay : {_base _index : Unit} → Unit → Bool := fun _ => false
def notice : OperationCostProtocol.Indexed.Notice (NativeControlCursor.protocol Service.Item)
    RetainedInvocation.OwnData.Refused := fun _ _ => none
abbrev decorated := OperationCostProtocol.Indexed.provider raw guard (@profiles) (@replay) invoice

abbrev Saved (mode : SourceProducerCardinality.CallingConvention) := Nat ×
  OperationCostProtocol.Indexed.Outcome raw guard (@profiles) (@replay) invoice
    (SourceProducerCardinality.CallingModes.client mode Service.Item) notice ()

def packet (mode : SourceProducerCardinality.CallingConvention) (roots : List Machine)
    (current : Service.CurrentData.Context revocationWorlds (Entry := Nat) (width := 3)) :
    Cursor.Packet decorated
      (OperationCostProtocol.Indexed.client (SourceProducerCardinality.CallingModes.client mode Service.Item) notice) () :=
  ⟨(), .inl (if mode = .producer then .finished [] else .pulling []),
    (Service.initial roots, current), OperationCostProtocol.initial Service.CurrentData.profile 200⟩

def advance (mode : SourceProducerCardinality.CallingConvention) (allowance : Nat) (roots : List Machine)
    (current : Service.CurrentData.Context revocationWorlds (Entry := Nat) (width := 3)) : Saved mode :=
  OperationCostProtocol.Indexed.run raw guard (@profiles) (@replay) invoice
    (SourceProducerCardinality.CallingModes.client mode Service.Item) notice allowance (packet mode roots current)

def stateOf (mode : SourceProducerCardinality.CallingConvention) (saved : Saved mode) :=
  match saved.2 with
  | .paused packet => packet.2.2.1
  | .done result => result.2.2.1

def accountOf (mode : SourceProducerCardinality.CallingConvention) (saved : Saved mode) :=
  OperationCostProtocol.Indexed.accountOf raw guard (@profiles) (@replay) invoice
    (SourceProducerCardinality.CallingModes.client mode Service.Item) notice saved.2

def countOf (mode : SourceProducerCardinality.CallingConvention) (saved : Saved mode) :=
  match saved.2 with
  | .done ⟨(), .inl rows, _⟩ =>
      some ((SourceProducerCardinality.CallingModes.decode mode Service.isFault rows).successful, rows.length)
  | _ => none

def supplyPoint (mode : SourceProducerCardinality.CallingConvention)
    (point : IndexedAuthority.Point revocationWorlds) (saved : Saved mode) : Saved mode :=
  (saved.1, Cursor.Outcome.mapState _ (source := decorated) (target := decorated)
    (fun state => ((state.1.1, { state.1.2 with live := { state.1.2.live with point := point } }), state.2)) saved.2)

def resume (mode : SourceProducerCardinality.CallingConvention) (allowance : Nat) (saved : Saved mode) : Saved mode :=
  OperationCostProtocol.Indexed.resume raw guard (@profiles) (@replay) invoice
    (SourceProducerCardinality.CallingModes.client mode Service.Item) notice allowance saved

def retry (mode : SourceProducerCardinality.CallingConvention) (saved : Saved mode) : Saved mode :=
  (saved.1, OperationCostProtocol.Indexed.retry raw guard (@profiles) (@replay) invoice
    (SourceProducerCardinality.CallingModes.client mode Service.Item) notice saved.2)

def emptyAfterEffect := [load emptyWorld (.emit 9 (finiteSource []))]
def completed := advance .optional 100 emptyAfterEffect context
def paid := advance .optional 1 emptyAfterEffect context
def revoked := resume .optional 10
  (supplyPoint .optional Cursor.ReadOnlyQuery.OwnWrite.Controls.revoked paid)
def recovered := resume .optional 100 (retry .optional
  (supplyPoint .optional RetainedInvocation.Examples.OwnData.fixture.point revoked))

/-- Removing the last source activation does not undo its preceding accepted
external write or reset the invoice. Currency advances while the consulted
historical read remains the same old premise. -/
theorem empty_body_keeps_prior_effects_and_paid_progress :
    countOf .optional completed = some (true, 0) ∧
      OrderedDependencyStore.query (stateOf .optional completed).2.live.store 0 = [7, 7, 9] ∧
      completed.1 = 2 ∧ (accountOf .optional completed).remaining = 198 ∧
      (accountOf .optional completed).events.length = 2 ∧
      (stateOf .optional completed).2.pastReads = context.pastReads ∧
      OrderedDependencyStore.checkRead (stateOf .optional completed).2.live.store
        (stateOf .optional completed).2.currency = true ∧
      OrderedDependencyStore.checkRead (stateOf .optional completed).2.live.store
        context.currency = false := by
  decide +kernel

/-- Revocation after the accepted write stops new work and retains the paid
source continuation. Restoring current permission resumes that continuation;
the earlier effect is not redispatched. -/
theorem current_refusal_keeps_the_paid_empty_body_continuation :
    countOf .optional paid = none ∧
      countOf .optional revoked = none ∧
      revoked.1 = paid.1 ∧ accountOf .optional revoked = accountOf .optional paid ∧
      (stateOf .optional revoked).1.memory = (stateOf .optional paid).1.memory ∧
      OrderedDependencyStore.query (stateOf .optional revoked).2.live.store 0 = [7, 7, 9] ∧
      countOf .optional recovered = some (true, 0) ∧
      recovered.1 = completed.1 ∧
      OrderedDependencyStore.query (stateOf .optional recovered).2.live.store 0 = [7, 7, 9] := by
  decide +kernel

/-- A shared external prefix is executed before the finite fork. Both
equal-valued answer occurrences survive, while that one write stays one. -/
theorem duplicated_source_bodies_do_not_duplicate_the_external_prefix :
    let saved := advance .direct 200
      [load emptyWorld (.emit 9 (finiteSource [integer 7, integer 7]))] context
    countOf .direct saved = some (false, 2) ∧
      OrderedDependencyStore.query (stateOf .direct saved).2.live.store 0 = [7, 7, 9] := by
  decide +kernel

end CurrentData

end Controls

namespace Weighted.Controls

open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Core.InferenceControl
open PolarizedNeed (Computation Value)

def integer (number : Int) : Atom := SharedSource.Controls.integer number

def number (_ : AuthoredProduction) : Outcome → Option Atom
  | .value (.native (.grounded (.int value))) => some (integer value)
  | _ => none

def authored (production : AuthoredProduction) : Option Coefficient :=
  if production.head = "choose" then some (.authored (.var "x")) else none

def rich (production : AuthoredProduction) : Option Coefficient :=
  if production.head = "choose" then
    (NativeEquationNeed.lookup production.row.environment "x").map fun cell =>
      .rich ⟨0, 0, 1, .emit 5 (.forceNeed 0), ids, Fin.elim0, fun _ => cell⟩
  else none

def leaves (annotation : AuthoredProduction → Option Coefficient) (fuel : Nat) (machine : Machine) :=
  WeightedBranchingResumption.contributions (source annotation number) fuel (.inl (WorkOccurrence.root machine))

def answers (annotation : AuthoredProduction → Option Coefficient) (fuel : Nat) (machine : Machine) :=
  WeightedBranchingResumption.nestedAnswers (leaves annotation fuel machine)

def factorView (factor : Factor) : String × Nat × Atom :=
  (factor.production.head, factor.production.row.index, factor.value)

def view (answer : Service.Node × Word) :=
  (SharedSource.Controls.resultTerm answer.1.state,
    (FreeMonoid.toList answer.2).map factorView,
    SharedSource.Controls.effects answer.1.state.world)

def invoked (annotation : AuthoredProduction → Option Coefficient) :=
  SharedSource.Controls.invokeRoots.flatMap fun machine => (answers annotation 300 machine).map view

/-- A coefficient runs in the real authored binding context before the
rich caller resumes. The two resulting pairs are correlated, and each own
factor word contains only its selected row, not the global search inventory. -/
theorem authored_callbacks_keep_correlated_exported_closures :
    invoked authored =
      [(some (.pair (.head (integer 7)) (.head (integer 7))), [("choose", 0, integer 7)], [7]),
       (some (.pair (.head (integer 8)) (.head (integer 8))), [("choose", 1, integer 7)], [7])] := by
  decide +kernel

/-- The rich callback borrows the actual row cell, emits once, and forces the
shared producer. The restored body sees that cached world; its second force
does not start a second callback or repeat either effect. -/
theorem rich_callbacks_share_cells_and_restore_the_reached_world :
    invoked rich =
      [(some (.pair (.head (integer 7)) (.head (integer 7))), [("choose", 0, integer 7)], [5, 7]),
       (some (.pair (.head (integer 8)) (.head (integer 8))), [("choose", 1, integer 7)], [5, 7])] := by
  decide +kernel

def unresolved (production : AuthoredProduction) : Option Coefficient :=
  if production.head = "choose" then
    some (.rich ⟨0, 0, 0,
      .returnValue (.native (.pair (.head (integer 0)) (.head (integer 1)))),
      ids, Fin.elim0, Fin.elim0⟩)
  else none

def parkedView (parked : (Service.Node × Job × List Job) ⊕ Work) :=
  match parked with
  | .inl (caller, job, parents) =>
      some (job.production.row.index, isHalted caller.state, isHalted job.cursor.state, parents.length)
  | .inr _ => none

def unresolvedObligations := SharedSource.Controls.invokeRoots.flatMap fun machine =>
  (WeightedBranchingResumption.nestedObligations (leaves unresolved 300 machine)).map fun item => parkedView item.1

/-- A completed Data pair has no scalar coefficient interpretation. Both
actual callers remain parked and no body answer or zero weight is invented. -/
theorem uninterpreted_data_retains_every_actual_caller :
    invoked unresolved = [] ∧
      unresolvedObligations = [some (0, false, true, 0), some (1, false, true, 0)] := by
  decide +kernel

def zero (production : AuthoredProduction) : Option Coefficient :=
  if production.head = "choose" then some (.authored (integer 0)) else none

/-- Zero is an explicit factor value. The two physical contributions remain
present; the source traversal never filters them by a scalar product. -/
theorem zero_coefficients_do_not_remove_occurrences :
    (invoked zero).map (fun answer => answer.2.1) =
      [[("choose", 0, integer 0)], [("choose", 1, integer 0)]] := by
  decide +kernel

def richDuplicate : SharedSource.Controls.Code :=
  .choose (.returnValue (.native (.head (integer 7)))) (.returnValue (.native (.head (integer 7))))

/-- Generic rich choices are genuine duplicate answers but supply no authored
row annotation, even when their dynamic ordinals are zero and one. -/
theorem rich_choice_ordinals_do_not_mint_authored_rows :
    (answers authored 100 (SharedSource.Controls.load SharedSource.Controls.emptyWorld richDuplicate)).map view =
      [(some (.head (integer 7)), [], []), (some (.head (integer 7)), [], [])] := by
  decide +kernel

def scoreProgram : NativeEquationNeed.Program := [⟨"score", [], integer 2⟩]

def nested (production : AuthoredProduction) : Option Coefficient :=
  if production.head = "choose" then
    some (.rich ⟨0, 0, 0,
      .call (.source scoreProgram []) (.head (.expression [.symbol "score"])),
      ids, Fin.elim0, Fin.elim0⟩)
  else if production.head = "score" then some (.authored (integer 3)) else none

/-- The child score's factor precedes the outer row factor. Restoring the
outer coefficient and its original rich caller preserves noncommutative
order rather than flattening the two callbacks into a global sum. -/
theorem nested_callback_factor_words_keep_execution_order :
    (invoked nested).map (fun answer => answer.2.1) =
      [[("score", 0, integer 3), ("choose", 0, integer 2)],
       [("score", 0, integer 3), ("choose", 1, integer 2)]] := by
  decide +kernel

open Mettapedia.Machines

def roots : List (Service.Node × Word) :=
  SharedSource.Controls.invokeRoots.map fun machine => (WorkOccurrence.root machine, 1)

def itemFault (item : Provider.Item) : Bool :=
  match NeedExecution.haltedOutcome item.1.1.state with | some (.value _) => false | _ => true

abbrev Saved (annotation : AuthoredProduction → Option Coefficient)
    (mode : SourceProducerCardinality.CallingConvention) := Nat ×
  Cursor.Outcome (Provider.sourceProvider annotation number)
    (SourceProducerCardinality.CallingModes.client mode Provider.Item) ()

def stateOf (annotation : AuthoredProduction → Option Coefficient)
    (mode : SourceProducerCardinality.CallingConvention) (saved : Saved annotation mode) : Provider.Inventory :=
  match saved.2 with
  | .paused packet => packet.2.2
  | .done result => result.2.2

def summary (annotation : AuthoredProduction → Option Coefficient)
    (mode : SourceProducerCardinality.CallingConvention) (saved : Saved annotation mode) : Option (Bool × Nat × Nat) :=
  match SourceProducerCardinality.CallingModes.receive mode itemFault
      (Provider.sourceProvider annotation number) saved.2 with
  | .inl _ => none
  | .inr (result, reached) => some (result.successful, result.rows.length, reached.search.frontier.length)

def wordRows (annotation : AuthoredProduction → Option Coefficient)
    (mode : SourceProducerCardinality.CallingConvention) (saved : Saved annotation mode) :
    Option (List (List (String × Nat × Atom))) :=
  match SourceProducerCardinality.CallingModes.receive mode itemFault
      (Provider.sourceProvider annotation number) saved.2 with
  | .inl _ => none
  | .inr (result, _) => some (result.rows.map fun (item : Provider.Item) =>
      (FreeMonoid.toList item.1.2).map factorView)

/-- The maintained receiving modes run this same mixed weighted source.
Producer is unpolled, nonempty keeps the other branch, and scalar modes wait
for exhaustion before classifying both physical occurrences. -/
theorem actual_weighted_modes_keep_words_and_all_residual_worlds :
    summary rich .producer (Provider.run rich number .producer 1 roots) = some (true, 0, 1) ∧
      (Provider.run rich number .producer 1 roots).1 = 0 ∧
      summary rich .nonemptyProducer (Provider.run rich number .nonemptyProducer 400 roots) = some (true, 1, 1) ∧
      summary rich .direct (Provider.run rich number .direct 400 roots) = some (false, 2, 0) ∧
      summary rich .optional (Provider.run rich number .optional 0 roots) = none ∧
      wordRows rich .direct (Provider.run rich number .direct 400 roots) =
        some [[("choose", 0, integer 7)], [("choose", 1, integer 7)]] := by
  decide +kernel

def single (code : SharedSource.Controls.Code) : List (Service.Node × Word) :=
  [(WorkOccurrence.root (SharedSource.Controls.load SharedSource.Controls.emptyWorld code), 1)]

def parkedNodeView (node : Provider.Node) : Option (Nat × Bool × Bool × Nat × Nat) :=
  match node.state.1 with
  | .inl _ => none
  | .inr (caller, job, parents) =>
      some (job.production.row.index, isHalted caller.state, isHalted job.cursor.state,
        parents.length, (FreeMonoid.toList node.state.2).length)

/-- Actual empty bodies exhaust with no rows and an actual failed application
returns its fault. A parked coefficient remains an unfinished invocation with
both complete obligations, rather than any completed optional result. -/
theorem weighted_exhaustion_keeps_fault_and_parked_dispositions_separate :
    summary authored .optional (Provider.run authored number .optional 30
      (single (SharedSource.Controls.finiteSource []))) = some (true, 0, 0) ∧
      summary authored .optional (Provider.run authored number .optional 200
        (single SharedSource.Controls.noMatchingArity)) = some (false, 1, 0) ∧
      summary unresolved .optional (Provider.run unresolved number .optional 400 roots) = none ∧
      ((stateOf unresolved .optional (Provider.run unresolved number .optional 400 roots)).search.frontier.map
        parkedNodeView) =
        [some (1, false, true, 0, 0), some (0, false, true, 0, 0)] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

def prefixRun := Provider.run rich number .direct 5 roots
def resumed := Cursor.resume (Provider.sourceProvider rich number)
  (SourceProducerCardinality.CallingModes.client .direct Provider.Item)
  (Provider.sourceCharge rich number) 400 prefixRun

/-- Resumption keeps the actual paid prefix and both branch words. It cannot
restart a shared callback merely because no scalar result was ready yet. -/
theorem actual_weighted_split_resume_preserves_paid_prefix :
    summary rich .direct prefixRun = none ∧ prefixRun.1 = 5 ∧
      summary rich .direct resumed = some (false, 2, 0) ∧
      wordRows rich .direct resumed = wordRows rich .direct (Provider.run rich number .direct 405 roots) ∧
      resumed.1 = (Provider.run rich number .direct 405 roots).1 := by
  decide +kernel

def bodyWorlds (inventory : Provider.Inventory) : List (Service.Node × Word) :=
  inventory.search.events.filterMap fun event => match event.origin.state.1 with
    | .inl node => some (node, event.origin.state.2)
    | .inr _ => none

def threadedRoots : List (Service.Node × Word) :=
  SharedSource.Controls.exported.toList.flatMap fun (value, _) =>
    (bodyWorlds (stateOf rich .direct (Provider.run rich number .direct 400 roots))).map fun (node, carried) =>
      (WorkOccurrence.root (SharedSource.Controls.invoke value node.state.world), carried)

def threaded := Provider.run rich number .direct 400 threadedRoots

/-- Each receiver re-enters the actual exported callable with its selected
world and factor prefix. Cached delivery contributes no new row factor and
does not repeat the shared callback's effects. -/
theorem received_world_and_coefficient_prefix_are_threaded_together :
    wordRows rich .direct threaded = some [[("choose", 0, integer 7)], [("choose", 1, integer 7)]] ∧
      (bodyWorlds (stateOf rich .direct threaded)).map
        (fun pair => SharedSource.Controls.effects pair.1.state.world) = [[5, 7], [5, 7]] ∧
      (bodyWorlds (stateOf rich .direct threaded)).map
        (fun pair => SharedSource.Controls.resultTerm pair.1.state) =
        [some (.pair (.head (integer 7)) (.head (integer 7))),
         some (.pair (.head (integer 8)) (.head (integer 8)))] := by
  decide +kernel

end Weighted.Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource

/-! ## Current data and authority on the mixed weighted source

A coefficient can publish an effect before it returns. Revocation at that
point must keep its already paid callback and caller; restoring permission
does not repeat the accepted effect. A changed consulted store remains stale
even when permission is restored.
-/
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.CurrentData

open _root_.CategoryTheory
open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.LanguageDef

variable (annotation : AuthoredProduction → Option Coefficient)
  (interpretation : AuthoredProduction → Outcome → Option Mettapedia.Languages.MeTTa.OSLFCore.Atom)

/-- The running callback supplies the current control while its body and
all parents remain owned. A parked callback has halted control and emits no
further effect, independently of its retained caller's next instruction. -/
def activeControl : Work → Control Local Resume Value Empty Fault
  | .inl body => body.state.control
  | .inr (_, job, _) => job.cursor.state.control

def coreControl : CoreWork → Control Local Resume Value Empty Fault
  | .inl body => body.state.control
  | .inr (_, job, _) => job.cursor.state.control

theorem control_projection (work : Work) : coreControl (mapWork work) = activeControl work := by
  cases work with
  | inl body => rfl
  | inr held => rcases held with ⟨body, job, parents⟩; rfl

def sourceActive (state : Provider.Inventory) : Bool := !state.search.frontier.isEmpty
def targetActive (state : Provider.CoreInventory) : Bool := !state.search.frontier.isEmpty

def sourceEffect (state : Provider.Inventory) : Option Nat :=
  state.search.frontier.head?.bind fun node => Service.CurrentData.signal (activeControl node.state.1)

def targetEffect (state : Provider.CoreInventory) : Option Nat :=
  state.search.frontier.head?.bind fun node => Service.CurrentData.signal (coreControl node.state.1)

theorem active_projection (state : Provider.Inventory) :
    sourceActive state = targetActive (Provider.project state) := by
  simp only [sourceActive, targetActive, Provider.project,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapState,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapMemory,
    Mettapedia.GSLT.Core.BranchingTemporal.Snapshot.mapNodes, List.isEmpty_map]

theorem effect_projection (state : Provider.Inventory) :
    sourceEffect state = targetEffect (Provider.project state) := by
  change state.search.frontier.head?.bind (fun node => Service.CurrentData.signal (activeControl node.state.1)) =
    (state.search.frontier.map Provider.mapNode).head?.bind
      (fun node => Service.CurrentData.signal (coreControl node.state.1))
  cases state.search.frontier with
  | nil => rfl
  | cons node rest => simp only [List.map_cons, List.head?_cons, Option.bind_some, Provider.mapNode, control_projection]

variable {DataWorld Entry : Type} {width : Nat} [Category.{0} DataWorld]
  (authority : IndexedAuthority.{0, 0, 0} DataWorld)
  (required : OrderedDependencyStore.Action Entry width → (world : DataWorld) → authority.Fibre world)
  (needed : (world : DataWorld) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Entry width),
    Decidable (FrameUpdate point.authority (required action point.world))]
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]
  (interpret : Nat → OrderedDependencyStore.Action Entry width)

abbrev Context := RetainedInvocation.OwnData.Context authority (Entry := Entry) (width := width)

/-- Branch-local Need worlds and factor prefixes remain in the full source
inventory. The separately selected external store serializes emitted effects
and owns current permission and read currency. It is not a last branch heap. -/
def rawSource := RetainedInvocation.OwnData.Polling.provider authority required needed interpret
  (Provider.sourcePull annotation interpretation) sourceActive sourceEffect

def rawTarget := RetainedInvocation.OwnData.Polling.provider authority required needed interpret
  (Provider.targetPull annotation interpretation) targetActive targetEffect

def representation : Cursor.Hom (rawSource annotation interpretation authority required needed interpret)
    (rawTarget annotation interpretation authority required needed interpret) :=
  RetainedInvocation.OwnData.Polling.representation authority required needed interpret
    (Provider.sourcePull annotation interpretation) (Provider.targetPull annotation interpretation)
    sourceActive targetActive sourceEffect targetEffect (Provider.representation annotation interpretation)
    active_projection effect_projection

def sourceGate : OperationCostProtocol.Indexed.Gate (Denied := RetainedInvocation.OwnData.Refused)
    (rawSource annotation interpretation authority required needed interpret) := fun state _ =>
  RetainedInvocation.OwnData.gate authority required needed interpret sourceEffect state

def targetGate : OperationCostProtocol.Indexed.Gate (Denied := RetainedInvocation.OwnData.Refused)
    (rawTarget annotation interpretation authority required needed interpret) := fun state _ =>
  RetainedInvocation.OwnData.gate authority required needed interpret targetEffect state

def profile : OperationCostProtocol.Profile :=
  ⟨"mixed-weighted-source-poll-v1", [("quantum", some .quantum)], .steps, none, .refused⟩

def profiles : {_base _index : Unit} → Unit → OperationCostProtocol.Profile := fun _ => profile
def replay : {_base _index : Unit} → Unit → Bool := fun _ => false

def sourceInvoice (origin : Nat) : OperationCostProtocol.Indexed.Invoice
    (rawSource annotation interpretation authority required needed interpret) := fun state _ =>
  if sourceActive state.1 then RetainedInvocation.OwnData.Invocation.pollInvoice origin state.1.memory else []

def targetInvoice (origin : Nat) : OperationCostProtocol.Indexed.Invoice
    (rawTarget annotation interpretation authority required needed interpret) := fun state _ =>
  if targetActive state.1 then RetainedInvocation.OwnData.Invocation.pollInvoice origin state.1.memory else []

/-- Current permission and dependencies, profile, replay policy and invoice
commute locally with the actual mixed-source provider. The generic indexed
owner derives adaptive run, retry, resume and validated publication laws. -/
def handler (origin : Nat) : OperationCostProtocol.Indexed.HandlerHom
    (rawSource annotation interpretation authority required needed interpret)
    (rawTarget annotation interpretation authority required needed interpret)
    (sourceGate annotation interpretation authority required needed interpret)
    (targetGate annotation interpretation authority required needed interpret)
    (@profiles) (@profiles) (@replay) (@replay)
    (sourceInvoice annotation interpretation authority required needed interpret origin)
    (targetInvoice annotation interpretation authority required needed interpret origin) where
  representation := representation annotation interpretation authority required needed interpret
  gate_eq state request := by
    dsimp only [sourceGate, targetGate, representation, RetainedInvocation.OwnData.Polling.representation,
      RetainedInvocation.OwnData.Polling.stateMap, Provider.representation, RetainedInvocation.OwnData.gate]
    rw [← effect_projection state.1]
  profiles_eq _ := rfl
  replay_eq _ := rfl
  invoice_eq state request := by
    dsimp only [sourceInvoice, targetInvoice, representation, RetainedInvocation.OwnData.Polling.representation,
      RetainedInvocation.OwnData.Polling.stateMap, Provider.representation]
    rw [← active_projection state.1]
    rfl

def sourceProvider (origin : Nat) := OperationCostProtocol.Indexed.provider
  (rawSource annotation interpretation authority required needed interpret)
  (sourceGate annotation interpretation authority required needed interpret) (@profiles) (@replay)
  (sourceInvoice annotation interpretation authority required needed interpret origin)

def targetProvider (origin : Nat) := OperationCostProtocol.Indexed.provider
  (rawTarget annotation interpretation authority required needed interpret)
  (targetGate annotation interpretation authority required needed interpret) (@profiles) (@replay)
  (targetInvoice annotation interpretation authority required needed interpret origin)

def sourceCharge (origin : Nat) : Cursor.Charge
    (sourceProvider annotation interpretation authority required needed interpret origin) := OperationCostProtocol.Indexed.charge
  (rawSource annotation interpretation authority required needed interpret)
  (sourceGate annotation interpretation authority required needed interpret) (@profiles) (@replay)
  (sourceInvoice annotation interpretation authority required needed interpret origin)

def targetCharge (origin : Nat) : Cursor.Charge
    (targetProvider annotation interpretation authority required needed interpret origin) := OperationCostProtocol.Indexed.charge
  (rawTarget annotation interpretation authority required needed interpret)
  (targetGate annotation interpretation authority required needed interpret) (@profiles) (@replay)
  (targetInvoice annotation interpretation authority required needed interpret origin)

def notice : OperationCostProtocol.Indexed.Notice (NativeControlCursor.protocol Provider.Item)
    RetainedInvocation.OwnData.Refused := fun _ _ => none

def modePacket (mode : SourceProducerCardinality.CallingConvention) (origin : Nat)
    (state : Provider.Inventory × Context authority (Entry := Entry) (width := width))
    (account : OperationCostProtocol.Account) :
    Cursor.Packet (sourceProvider annotation interpretation authority required needed interpret origin)
      (OperationCostProtocol.Indexed.client
        (SourceProducerCardinality.CallingModes.client mode Provider.Item) notice) () :=
  ⟨(), .inl (if mode = .producer then .finished [] else .pulling []), state, account⟩

/-- All four existing receiving clients use the current gate on each actual
request. The local constructed handler transports the exact paid residual. -/
theorem mode_run_transport (mode : SourceProducerCardinality.CallingConvention) (origin fuel : Nat)
    (state : Provider.Inventory × Context authority (Entry := Entry) (width := width))
    (account : OperationCostProtocol.Account) :
    let reader := SourceProducerCardinality.CallingModes.client mode Provider.Item
    let held := modePacket annotation interpretation authority required needed interpret mode origin state account
    let result := Cursor.advance (sourceProvider annotation interpretation authority required needed interpret origin)
      (OperationCostProtocol.Indexed.client reader notice)
      (sourceCharge annotation interpretation authority required needed interpret origin) fuel held
    (result.1, (handler annotation interpretation authority required needed interpret origin).mapOutcome
      reader notice result.2) =
      Cursor.advance (targetProvider annotation interpretation authority required needed interpret origin)
        (OperationCostProtocol.Indexed.client reader notice)
        (targetCharge annotation interpretation authority required needed interpret origin) fuel
        ((handler annotation interpretation authority required needed interpret origin).lift.packet
          (OperationCostProtocol.Indexed.client reader notice) held) :=
  (handler annotation interpretation authority required needed interpret origin).run
    (SourceProducerCardinality.CallingModes.client mode Provider.Item) notice fuel
    (modePacket annotation interpretation authority required needed interpret mode origin state account)


/-- The receiving mode resumes the same complete paid state after a cut or
service-owner retry; its selected branch worlds are mapped individually. -/
theorem mode_resume_transport (mode : SourceProducerCardinality.CallingConvention) (origin fuel : Nat)
    (earlier : Nat × Cursor.Outcome
      (sourceProvider annotation interpretation authority required needed interpret origin)
      (OperationCostProtocol.Indexed.client
        (SourceProducerCardinality.CallingModes.client mode Provider.Item) notice) ()) :
    let reader := SourceProducerCardinality.CallingModes.client mode Provider.Item
    let resumed := Cursor.resume
      (sourceProvider annotation interpretation authority required needed interpret origin)
      (OperationCostProtocol.Indexed.client reader notice)
      (sourceCharge annotation interpretation authority required needed interpret origin) fuel earlier
    (resumed.1, (handler annotation interpretation authority required needed interpret origin).mapOutcome reader notice resumed.2) =
      Cursor.resume (targetProvider annotation interpretation authority required needed interpret origin)
        (OperationCostProtocol.Indexed.client reader notice)
        (targetCharge annotation interpretation authority required needed interpret origin) fuel
        (earlier.1, (handler annotation interpretation authority required needed interpret origin).mapOutcome reader notice earlier.2) :=
  (handler annotation interpretation authority required needed interpret origin).resume
    (SourceProducerCardinality.CallingModes.client mode Provider.Item) notice fuel earlier

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.CurrentData

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.CurrentData.Controls

open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.LanguageDef
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open PolarizedNeed (Computation Value)

abbrev required := RetainedInvocation.Examples.OwnData.required
abbrev needed := RetainedInvocation.Examples.OwnData.needed
abbrev context := RetainedInvocation.Examples.OwnData.context

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (required change point.world)) :=
  RetainedInvocation.Examples.OwnData.permissionDecision point change

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) :=
  RetainedInvocation.Examples.OwnData.admissionDecision point

def act (event : Nat) : OrderedDependencyStore.Action Nat 3 := .append 0 [event]
abbrev annotation := Weighted.Controls.rich
abbrev number := Weighted.Controls.number
abbrev source := sourceProvider annotation number revocationWorlds required needed act 305
abbrev target := targetProvider annotation number revocationWorlds required needed act 305
abbrev charge : Cursor.Charge source := sourceCharge annotation number revocationWorlds required needed act 305
abbrev reader := SourceProducerCardinality.CallingModes.client .direct Provider.Item
abbrev client := OperationCostProtocol.Indexed.client reader notice
abbrev Saved := Nat × Cursor.Outcome source client ()

def program : NativeEquationNeed.Program :=
  [⟨"choose", ["x"], .var "x"⟩]

def code : SharedSource.Controls.Code :=
  .letNeed (.emit 7 (.returnValue (.native (.head (SharedSource.Controls.integer 7)))))
    (.call (.source program [("x", 0)]) (.head (.expression [.symbol "choose", .var "x"])))

def roots : List (Service.Node × Word) :=
  [(WorkOccurrence.root (SharedSource.Controls.load SharedSource.Controls.emptyWorld code), 1)]

def packet (current : Context revocationWorlds (Entry := Nat) (width := 3)) :=
  modePacket annotation number revocationWorlds required needed act .direct 305
    (Provider.initial roots, current) (OperationCostProtocol.initial profile 1000)

def run (fuel : Nat) (current : Context revocationWorlds (Entry := Nat) (width := 3)) : Saved :=
  Cursor.advance source client charge fuel (packet current)

def stateOf (saved : Saved) : Provider.Inventory × Context revocationWorlds (Entry := Nat) (width := 3) :=
  match saved.2 with
  | .paused held => held.2.2.1
  | .done result => result.2.2.1

def accountOf (saved : Saved) : OperationCostProtocol.Account :=
  OperationCostProtocol.Indexed.accountOf
    (rawSource annotation number revocationWorlds required needed act)
    (sourceGate annotation number revocationWorlds required needed act) (@profiles) (@replay)
    (sourceInvoice annotation number revocationWorlds required needed act 305) reader notice saved.2

def rows (saved : Saved) : Option (List Provider.Item) :=
  match saved.2 with
  | .done ⟨(), .inl rows, _⟩ => some rows
  | _ => none

def refusal (saved : Saved) : Option (OperationCostProtocol.Indexed.Reason RetainedInvocation.OwnData.Refused) :=
  match saved.2 with
  | .done ⟨(), .inr (reason, _), _⟩ => some reason
  | _ => none

def supply (change : Context revocationWorlds (Entry := Nat) (width := 3) →
    Context revocationWorlds (Entry := Nat) (width := 3)) (saved : Saved) : Saved :=
  (saved.1, Cursor.Outcome.mapState client (source := source) (target := source)
    (fun state => ((state.1.1, change state.1.2), state.2)) saved.2)

def retry (saved : Saved) : Saved :=
  (saved.1, OperationCostProtocol.Indexed.retry
    (rawSource annotation number revocationWorlds required needed act)
    (sourceGate annotation number revocationWorlds required needed act) (@profiles) (@replay)
    (sourceInvoice annotation number revocationWorlds required needed act 305) reader notice saved.2)

def resume (fuel : Nat) (saved : Saved) : Saved := Cursor.resume source client charge fuel saved

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.CurrentData.Controls

/-! ## Passive history on the same weighted current-data invocation

An inner authored score can finish before an outer rich callback. Their
ordered factors belong to each selected answer path. A chronological observer
also sees sibling callbacks, zero factors, cached delivery, effects and
admission pauses; its whole-search word is not one answer's coefficient.
-/
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.History

open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

variable (annotation : AuthoredProduction → Option Coefficient)
  (interpretation : AuthoredProduction → Outcome → Option Atom)

def selectedMachine : Work → Machine
  | .inl body => body.state
  | .inr (_, job, _) => job.cursor.state

def coreMachine : CoreWork → CoreMachine
  | .inl body => body.state
  | .inr (_, job, _) => job.cursor.state

theorem selected_machine_projection (work : Work) :
    coreMachine (mapWork work) = NeedExecution.projectMachine false (selectedMachine work) := by
  cases work with
  | inl body => rfl
  | inr held => rcases held with ⟨body, job, parents⟩; rfl

/-- An accepted factor is observed at its actual callback return boundary.
Source selection and cached delivery remain different operational roles. -/
def factorBlock : Work → Word
  | .inl _ => 1
  | .inr (_, job, _) => if isHalted job.cursor.state then (readout interpretation job).getD 1 else 1

def coreFactorBlock : CoreWork → Word
  | .inl _ => 1
  | .inr (_, job, _) =>
      if NeedExecution.isHalted job.cursor.state then (coreReadout interpretation job).getD 1 else 1

theorem factor_block_projection (work : Work) :
    coreFactorBlock interpretation (mapWork work) = factorBlock interpretation work := by
  cases work with
  | inl body => rfl
  | inr held =>
      rcases held with ⟨body, job, parents⟩
      simp only [coreFactorBlock, factorBlock, mapWork, Sum.map_inr]
      have halted : NeedExecution.isHalted (mapJob job).cursor.state = isHalted job.cursor.state := rfl
      rw [halted, readout_projection]

inductive Phase where
  | body
  | callback (depth : Nat)
  | parked (depth : Nat)
  deriving DecidableEq, Repr

def phase : Work → Phase
  | .inl _ => .body
  | .inr (_, job, parents) =>
      if isHalted job.cursor.state && (readout interpretation job).isNone
      then .parked (parents.length + 1) else .callback (parents.length + 1)

def corePhase : CoreWork → Phase
  | .inl _ => .body
  | .inr (_, job, parents) =>
      if NeedExecution.isHalted job.cursor.state && (coreReadout interpretation job).isNone
      then .parked (parents.length + 1) else .callback (parents.length + 1)

theorem phase_projection (work : Work) : corePhase interpretation (mapWork work) = phase interpretation work := by
  cases work with
  | inl body => rfl
  | inr held =>
      rcases held with ⟨body, job, parents⟩
      simp only [corePhase, phase, mapWork, Sum.map_inr, List.length_map]
      have halted : NeedExecution.isHalted (mapJob job).cursor.state = isHalted job.cursor.state := rfl
      rw [halted, readout_projection]

/-- This role-bearing observation contains no reconstructed source code.
The tagged firings preserve actual authored rows versus generic rich choices;
the completed-cell view is the shared cache owner's checked classifier. -/
structure Inspection where
  occurrence : WorldPath
  phase : Phase
  firings : List (CellId × Rule)
  completed : Option (NeedCacheLaws.CompletedObservation Value Empty Fault)
  effect : Option Nat
  factors : Word
  returned : Option Provider.Item

def sourceInspection (state : Provider.Inventory) : Option Inspection :=
  state.search.frontier.head?.map fun node =>
    let active := selectedMachine node.state.1
    ⟨node.trace, phase interpretation node.state.1,
      NeedLocalSteps.firingChoices specification active.world.heap active.control,
      NeedCacheLaws.completedObservation? active.world.heap active.control,
      Service.CurrentData.signal active.control, factorBlock interpretation node.state.1,
      (Provider.sourceSystem annotation interpretation).emit node⟩

def targetInspection (state : Provider.CoreInventory) : Option Inspection :=
  state.search.frontier.head?.map fun node =>
    let active := coreMachine node.state.1
    ⟨node.trace, corePhase interpretation node.state.1,
      NeedLocalSteps.firingChoices specification active.world.heap active.control,
      NeedCacheLaws.completedObservation? active.world.heap active.control,
      Service.CurrentData.signal active.control, coreFactorBlock interpretation node.state.1,
      (Provider.targetSystem annotation interpretation).emit node⟩

theorem inspection_projection (state : Provider.Inventory) :
    sourceInspection annotation interpretation state =
      targetInspection annotation interpretation (Provider.project state) := by
  change state.search.frontier.head?.map _ =
    (state.search.frontier.map Provider.mapNode).head?.map _
  cases selected : state.search.frontier with
  | nil => rfl
  | cons node rest =>
      simp only [List.head?_cons, List.map_cons, Option.map_some]
      rw [Provider.local_emit annotation interpretation node]
      simp only [Provider.mapNode, selected_machine_projection, phase_projection, factor_block_projection,
        NeedExecution.projectMachine, NeedExecution.projectWorld]

inductive View where
  | inert
  | finish
  | refused (reason : OperationCostProtocol.Indexed.Reason RetainedInvocation.OwnData.Refused)
  | accepted (ordinal : Nat) (invoice : List OperationCostProtocol.Event) (selected : Option Inspection)

open _root_.CategoryTheory
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.OSLF.Binding.RewriteEventHistory
open Mettapedia.Effects

variable {DataWorld Entry : Type} {width : Nat} [Category.{0} DataWorld]
  (authority : IndexedAuthority.{0, 0, 0} DataWorld)
  (required : OrderedDependencyStore.Action Entry width → (world : DataWorld) → authority.Fibre world)
  (needed : (world : DataWorld) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Entry width),
    Decidable (FrameUpdate point.authority (required action point.world))]
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]
  (interpret : Nat → OrderedDependencyStore.Action Entry width)
  {Return : Unit → Unit → Type}
  (reader : Cursor.Client (P := NativeControlCursor.protocol Provider.Item) (Return := Return))
  (notice : OperationCostProtocol.Indexed.Notice (NativeControlCursor.protocol Provider.Item)
    RetainedInvocation.OwnData.Refused)

local notation "RawSource" => CurrentData.rawSource annotation interpretation authority required needed interpret
local notation "RawTarget" => CurrentData.rawTarget annotation interpretation authority required needed interpret
local notation "SourceGate" => CurrentData.sourceGate annotation interpretation authority required needed interpret
local notation "TargetGate" => CurrentData.targetGate annotation interpretation authority required needed interpret
local notation "SourceInvoice" => CurrentData.sourceInvoice annotation interpretation authority required needed interpret
local notation "TargetInvoice" => CurrentData.targetInvoice annotation interpretation authority required needed interpret
local notation "Source" => CurrentData.sourceProvider annotation interpretation authority required needed interpret
local notation "Target" => CurrentData.targetProvider annotation interpretation authority required needed interpret
local notation "Client" => OperationCostProtocol.Indexed.client reader notice
local notation "Realization" => CurrentData.handler annotation interpretation authority required needed interpret

def sourceView (origin : Nat) {base : Unit} : Cursor.Outcome (Source origin) Client base → View
  | .done _ => .inert
  | .paused ⟨index, control, state⟩ =>
      match (Client).str base index control with
      | ⟨.inl _, _⟩ => .finish
      | ⟨.inr request, _⟩ =>
          match OperationCostProtocol.Indexed.admit RawSource SourceGate (@CurrentData.profiles)
              (@CurrentData.replay) (SourceInvoice origin) state.1 request state.2 with
          | .error reason => .refused reason
          | .ok _ => .accepted state.1.1.memory (SourceInvoice origin state.1 request)
              (sourceInspection annotation interpretation state.1.1)

def targetView (origin : Nat) {base : Unit} : Cursor.Outcome (Target origin) Client base → View
  | .done _ => .inert
  | .paused ⟨index, control, state⟩ =>
      match (Client).str base index control with
      | ⟨.inl _, _⟩ => .finish
      | ⟨.inr request, _⟩ =>
          match OperationCostProtocol.Indexed.admit RawTarget TargetGate (@CurrentData.profiles)
              (@CurrentData.replay) (TargetInvoice origin) state.1 request state.2 with
          | .error reason => .refused reason
          | .ok _ => .accepted state.1.1.memory (TargetInvoice origin state.1 request)
              (targetInspection annotation interpretation state.1.1)

theorem view_projection (origin : Nat) {base : Unit} (before : Cursor.Outcome (Source origin) Client base) :
    sourceView annotation interpretation authority required needed interpret reader notice origin before =
      targetView annotation interpretation authority required needed interpret reader notice origin
        ((Realization origin).lift.outcome Client before) := by
  cases before with
  | done result => rfl
  | paused packet =>
      rcases packet with ⟨index, control, ⟨source, context⟩, account⟩
      change (match (Client).str base index control with
        | ⟨.inl _, _⟩ => View.finish
        | ⟨.inr request, _⟩ => _) =
        (match (Client).str base index control with
        | ⟨.inl _, _⟩ => View.finish
        | ⟨.inr request, _⟩ => _)
      cases exposed : (Client).str base index control with
      | mk shape children =>
          cases shape with
          | inl answer => rfl
          | inr request =>
              simp only [OperationCostProtocol.Indexed.HandlerHom.lift]
              erw [← (Realization origin).admit_eq]
              cases accepted : OperationCostProtocol.Indexed.admit RawSource SourceGate (@CurrentData.profiles)
                  (@CurrentData.replay) (SourceInvoice origin) (source, context) request account with
              | error reason => rfl
              | ok paid =>
                  change View.accepted source.memory (SourceInvoice origin (source, context) request)
                      (sourceInspection annotation interpretation source) =
                    View.accepted source.memory (TargetInvoice origin (Provider.project source, context) request)
                      (targetInspection annotation interpretation (Provider.project source))
                  have invoices := (Realization origin).invoice_eq (base := base) (index := index) (source, context) request
                  change SourceInvoice origin (source, context) request =
                    TargetInvoice origin (Provider.project source, context) request at invoices
                  rw [← invoices]
                  exact congrArg (View.accepted source.memory (SourceInvoice origin (source, context) request))
                    (inspection_projection annotation interpretation source)

def sourceAccount {Coefficient : Type} [Monoid Coefficient] (origin : Nat) (base : Unit)
    (value : View → Coefficient) :
    RunAccount (HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)) Coefficient :=
  NativeControlCursor.ProtocolHistory.eventAccount (Source origin) Client base
    (fun {before _} _ => value (sourceView annotation interpretation authority required needed interpret reader notice origin before))

def targetAccount {Coefficient : Type} [Monoid Coefficient] (origin : Nat) (base : Unit)
    (value : View → Coefficient) :
    RunAccount (HistoryCategory (NativeControlCursor.ProtocolHistory.system (Target origin) Client base)) Coefficient :=
  NativeControlCursor.ProtocolHistory.eventAccount (Target origin) Client base
    (fun {before _} _ => value (targetView annotation interpretation authority required needed interpret reader notice origin before))

/-- Ordered accounts are transported from the local role/invoice observation
law through the existing proof-relevant history owner. -/
theorem account_transport {Coefficient : Type} [Monoid Coefficient]
    (origin : Nat) (base : Unit) (value : View → Coefficient) :
    (targetAccount annotation interpretation authority required needed interpret reader notice origin base value).comap
        (NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories =
      sourceAccount annotation interpretation authority required needed interpret reader notice origin base value := by
  have transported := NativeControlCursor.ProtocolHistory.hom_account_preserved Client (Realization origin).lift base
    (fun {before _} _ => value (sourceView annotation interpretation authority required needed interpret reader notice origin before))
    (fun {before _} _ => value (targetView annotation interpretation authority required needed interpret reader notice origin before))
    (MonoidHom.id _) (by
      intro before after event
      exact congrArg value (view_projection annotation interpretation authority required needed interpret reader notice origin before).symm)
  ext before after run
  exact congrArg (fun account => account.of run) transported

def factorValue : View → Word
  | .accepted _ _ (some selected) => selected.factors
  | _ => 1

def effectValue : View → FreeMonoid Nat
  | .accepted _ _ (some selected) => FreeMonoid.ofList selected.effect.toList
  | _ => 1

def cacheValue : View → FreeMonoid (CellId × NeedCacheLaws.CompletedReceiptKind)
  | .accepted _ _ (some selected) => FreeMonoid.ofList
      (selected.completed.map fun completed => (completed.cell, completed.kind)).toList
  | _ => 1

def firingValue : View → FreeMonoid (CellId × Rule)
  | .accepted _ _ (some selected) => FreeMonoid.ofList selected.firings
  | _ => 1

def returnValue : View → FreeMonoid Provider.Item
  | .accepted _ _ (some selected) => FreeMonoid.ofList selected.returned.toList
  | _ => 1

def invoiceValue : View → Multiplicative Nat
  | .accepted _ invoice _ => Multiplicative.ofAdd (OperationCostProtocol.work invoice)
  | _ => 1

def sourceWord (origin : Nat) (base : Unit) :=
  sourceAccount annotation interpretation authority required needed interpret reader notice origin base FreeMonoid.of

def targetWord (origin : Nat) (base : Unit) :=
  targetAccount annotation interpretation authority required needed interpret reader notice origin base FreeMonoid.of

theorem word_concat (origin : Nat) (base : Unit)
    {before middle after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (first : before ⟶ middle) (second : middle ⟶ after) :
    ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of
      (first ≫ second)).toList =
      ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of first).toList ++
        ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of second).toList := by
  rw [RunAccount.of_comp, FreeMonoid.toList_mul]

theorem invoice_event (origin : Nat) {base : Unit} {before after : Cursor.Outcome (Source origin) Client base}
    (event : NativeControlCursor.ProtocolHistory.Event (Source origin) Client base before after) :
    invoiceValue (sourceView annotation interpretation authority required needed interpret reader notice origin before) =
      Multiplicative.ofAdd (NativeControlCursor.ProtocolHistory.eventExpense (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) event) := by
  cases event with
  | finish control state answer children exposed =>
      simp only [sourceView, exposed, invoiceValue, NativeControlCursor.ProtocolHistory.eventExpense]
      rfl
  | request control state request children exposed =>
      simp only [sourceView, exposed, CurrentData.sourceCharge, OperationCostProtocol.Indexed.charge,
        NativeControlCursor.ProtocolHistory.eventExpense]
      cases accepted : OperationCostProtocol.Indexed.admit RawSource SourceGate (@CurrentData.profiles)
          (@CurrentData.replay) (SourceInvoice origin) state.1 request state.2 <;> rfl

theorem invoice_account (origin : Nat) (base : Unit) :
    sourceAccount annotation interpretation authority required needed interpret reader notice origin base invoiceValue =
      NativeControlCursor.ProtocolHistory.providerAccount (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) base := by
  unfold sourceAccount NativeControlCursor.ProtocolHistory.providerAccount
  congr 1
  funext before after event
  exact invoice_event annotation interpretation authority required needed interpret reader notice origin event


/-! The passive reader folds observations of existing one-step cursor resumes.
It adds no source, Need or handler transition rules. The exact account theorem
below derives its complete ordered output from the established history laws. -/
namespace PassiveReader

local notation "Charge" => CurrentData.sourceCharge annotation interpretation authority required needed interpret
local notation "Account" => sourceAccount annotation interpretation authority required needed interpret reader notice
local notation "Observe" => sourceView annotation interpretation authority required needed interpret reader notice

def readSuffix {Coefficient : Type} [Monoid Coefficient] (origin : Nat) (value : View → Coefficient) :
    Nat → {base : Unit} → (Nat × Cursor.Outcome (Source origin) Client base) → Coefficient
  | 0, _, _ => 1
  | fuel + 1, _, before => match before.2 with
    | .done _ => 1
    | .paused _ => value (Observe origin before.2) *
        readSuffix origin value fuel (Cursor.resume (Source origin) Client (Charge origin) 1 before)

private theorem account_heq {S : ProofRelevantGSLT.{0}} {Coefficient : Type} [Monoid Coefficient]
    (account : RunAccount (HistoryCategory S) Coefficient)
    {before after other : HistoryCategory S} (sameEnd : after = other)
    (first : before ⟶ after) (second : before ⟶ other) (same : HEq first second) :
    account.of first = account.of second := by
  cases sameEnd
  exact congrArg (fun history => account.of history) (eq_of_heq same)

theorem one_inspection {Coefficient : Type} [Monoid Coefficient]
    (origin : Nat) (value : View → Coefficient) {base : Unit}
    (before : Nat × Cursor.Outcome (Source origin) Client base) :
    (Account origin base value).of
        (NativeControlCursor.ProtocolHistory.resumeHistory (Source origin) Client (Charge origin) 1 before) =
      readSuffix annotation interpretation authority required needed interpret reader notice origin value 1 before := by
  rcases before with ⟨paid, result⟩
  cases result with
  | done result => rfl
  | paused packet =>
      rcases packet with ⟨index, control, state⟩
      cases exposed : (Client).str base index control with
      | mk shape children =>
          cases shape with
          | inl answer =>
              have moved : Cursor.advance (Source origin) Client (Charge origin) 1 ⟨index, control, state⟩ =
                  (0, .done ⟨index, answer, state⟩) := by simp only [Cursor.advance, exposed]
              have endpoint := congrArg (fun result => (⟨result.2⟩ : State
                (NativeControlCursor.ProtocolHistory.system (Source origin) Client base))) moved
              have compared := NativeControlCursor.ProtocolHistory.advanceHistory_finish (Source origin) Client
                (Charge origin) 0 control state answer children exposed
              have exactAccount := account_heq (Account origin base value) endpoint _ _ compared
              change (Account origin base value).of
                (NativeControlCursor.ProtocolHistory.advanceHistory (Source origin) Client (Charge origin) 1
                  ⟨index, control, state⟩) = _
              rw [exactAccount, sourceAccount, NativeControlCursor.ProtocolHistory.eventAccount_generator]
              simp only [readSuffix, mul_one]
          | inr request =>
              let next : Cursor.Packet (Source origin) Client base :=
                ⟨_, children ((Source origin).step state request).1, ((Source origin).step state request).2⟩
              have moved : Cursor.advance (Source origin) Client (Charge origin) 1 ⟨index, control, state⟩ =
                  ((Charge origin) state request, .paused next) := by simp only [Cursor.advance, exposed]; rfl
              have endpoint := congrArg (fun result => (⟨result.2⟩ : State
                (NativeControlCursor.ProtocolHistory.system (Source origin) Client base))) moved
              have compared := NativeControlCursor.ProtocolHistory.advanceHistory_request (Source origin) Client
                (Charge origin) 0 control state request children exposed
              have exactAccount := account_heq (Account origin base value) endpoint _ _ compared
              change (Account origin base value).of
                (NativeControlCursor.ProtocolHistory.advanceHistory (Source origin) Client (Charge origin) 1
                  ⟨index, control, state⟩) = _
              rw [exactAccount]
              simp only [NativeControlCursor.ProtocolHistory.advanceHistory_zero]
              erw [Quiver.Path.comp_nil]
              erw [sourceAccount, NativeControlCursor.ProtocolHistory.eventAccount_generator]
              simp only [readSuffix, mul_one]

theorem exact_account {Coefficient : Type} [Monoid Coefficient]
    (origin : Nat) (value : View → Coefficient) (fuel : Nat) {base : Unit}
    (before : Nat × Cursor.Outcome (Source origin) Client base) :
    (Account origin base value).of
        (NativeControlCursor.ProtocolHistory.resumeHistory (Source origin) Client (Charge origin) fuel before) =
      readSuffix annotation interpretation authority required needed interpret reader notice origin value fuel before := by
  induction fuel generalizing before with
  | zero =>
      rcases before with ⟨paid, result⟩
      cases result with
      | done result => rfl
      | paused packet => rfl
  | succ fuel ih =>
      have moved := Cursor.resume_add (Source origin) Client (Charge origin) 1 fuel before
      have endpoint := congrArg (fun result => (⟨result.2⟩ : State
        (NativeControlCursor.ProtocolHistory.system (Source origin) Client base))) moved
      have compared := NativeControlCursor.ProtocolHistory.resumeHistory_add_exact (Source origin) Client
        (Charge origin) 1 fuel before
      have exactAccount := account_heq (Account origin base value) endpoint _ _ compared
      rw [Nat.add_comm 1 fuel] at exactAccount
      rw [exactAccount]
      erw [RunAccount.of_comp]
      rw [one_inspection, ih]
      rcases before with ⟨paid, result⟩
      cases result with
      | done result =>
          cases fuel <;> simp only [readSuffix, Cursor.resume_done, one_mul]
      | paused packet => simp only [readSuffix, mul_one]

@[simp] theorem readSuffix_done {Coefficient : Type} [Monoid Coefficient]
    (origin : Nat) (value : View → Coefficient) (fuel paid : Nat) {base : Unit}
    (finished : Cursor.Finished (Source origin) (Return := _) base) :
    readSuffix annotation interpretation authority required needed interpret reader notice origin value fuel
      (paid, .done finished) = 1 := by
  cases fuel <;> rfl

theorem readSuffix_add {Coefficient : Type} [Monoid Coefficient]
    (origin : Nat) (value : View → Coefficient) (first second : Nat) {base : Unit}
    (before : Nat × Cursor.Outcome (Source origin) Client base) :
    readSuffix annotation interpretation authority required needed interpret reader notice origin value (first + second) before =
      readSuffix annotation interpretation authority required needed interpret reader notice origin value first before *
        readSuffix annotation interpretation authority required needed interpret reader notice origin value second
          (Cursor.resume (Source origin) Client (Charge origin) first before) := by
  induction first generalizing before with
  | zero => simp only [Nat.zero_add, readSuffix, Cursor.resume_zero, one_mul]
  | succ first ih =>
      rcases before with ⟨paid, result⟩
      cases result with
      | done finished => simp only [readSuffix_done, Cursor.resume_done, one_mul]
      | paused packet =>
          have split := Cursor.resume_add (Source origin) Client (Charge origin) 1 first (paid, .paused packet)
          rw [Nat.add_comm 1 first] at split
          simp only [Nat.succ_add, readSuffix]
          rw [ih, split, mul_assoc]


end PassiveReader

/-- The account of the actual generated bounded history is the paid poll
invoice. Source firing counts and recorded payload sizes remain distinct. -/
theorem invoice_advance (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base) :
    Multiplicative.toAdd
      ((sourceAccount annotation interpretation authority required needed interpret reader notice origin base invoiceValue).of
        (NativeControlCursor.ProtocolHistory.advanceHistory (Source origin) Client
          (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance packet)) =
      (Cursor.advance (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance packet).1 := by
  rw [invoice_account]
  exact NativeControlCursor.ProtocolHistory.advanceHistory_paid _ _ _ _ _

/-- Paid work before the pause is retained; the invoice of the exact suffix
is added once when the same invocation resumes. -/
theorem invoice_resume (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base) :
    earlier.1 + Multiplicative.toAdd
      ((sourceAccount annotation interpretation authority required needed interpret reader notice origin base invoiceValue).of
        (NativeControlCursor.ProtocolHistory.resumeHistory (Source origin) Client
          (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance earlier)) =
      (Cursor.resume (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance earlier).1 := by
  rw [invoice_account]
  exact NativeControlCursor.ProtocolHistory.resumeHistory_paid _ _ _ _ _


/-- Optional recording receives the actual history only when enabled. The
unrecorded branch never evaluates its history thunk. Recording does not
participate in the operational transition or its invoice. -/
def recordSuffix (origin : Nat) (base : Unit)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (record : Option (Recording.Prefix (View)))
    (history : Unit → (before ⟶ after)) :
    Option (Recording.Prefix (View)) :=
  record.map fun record => record.append
    ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of (history ())).toList

/-- An enabled prefix composes over the real midpoint, including its
complete account and retained Need world. Capacity is not replenished. -/
theorem recording_concat (origin : Nat) (base : Unit)
    {before middle after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (record : Recording.Prefix (View))
    (first : before ⟶ middle) (second : middle ⟶ after) :
    recordSuffix annotation interpretation authority required needed interpret reader notice origin base
      (some record) (fun _ => first ≫ second) =
    recordSuffix annotation interpretation authority required needed interpret reader notice origin base
      (recordSuffix annotation interpretation authority required needed interpret reader notice origin base
        (some record) (fun _ => first)) (fun _ => second) := by
  simp only [recordSuffix, Option.map_some, word_concat, Recording.Prefix.append_append]

/-- History transport preserves the whole recorded suffix, not just its
length or a commutative aggregate. -/
theorem recording_transport (origin : Nat) (base : Unit)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (record : Recording.Prefix (View))
    (history : before ⟶ after) :
    record.append
        ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of history).toList =
      record.append
        ((targetWord annotation interpretation authority required needed interpret reader notice origin base).of
          ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map
            history)).toList := by
  have law := account_transport annotation interpretation authority required needed interpret reader notice
    origin base FreeMonoid.of
  exact congrArg (fun account => record.append (account.of history).toList) law.symm

/-- A complete readout is exactly the actual interval since recording was
started, provided the bounded prefix retained every event. -/
theorem recording_complete (origin capacity : Nat) (base : Unit)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (history : before ⟶ after) :
    ((Recording.Prefix.initial capacity).append
      ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of history).toList).complete? =
        some ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of history).toList ↔
      ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of history).toList.length ≤
        capacity :=
  Recording.Prefix.complete_iff _ _

/-- Refusing a partial native observation does not erase an occurrence from
an otherwise complete readout. Retry is an execution decision outside this
passive projection. -/
theorem recording_refuses_missing_payload (origin : Nat) (base : Unit)
    {Payload : Type}
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (decode : View → Option Payload)
    (record : Recording.Prefix (View))
    (history : before ⟶ after) (event : View)
    (member : event ∈ (record.append
      ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of history).toList).items)
    (refused : decode event = none) :
    Recording.Prefix.project? decode (record.append
      ((sourceWord annotation interpretation authority required needed interpret reader notice origin base).of history).toList) = none :=
  Recording.Prefix.project?_refused _ _ _ member refused

/-- A provider realization preserves and reflects replay qualification for
any declared local observation monoid. This is not permission to repeat a
native effect: current publication remains governed by its own gate. -/
theorem qualified_replay_transport {Coefficient : Type} [Monoid Coefficient]
    (origin : Nat) (base : Unit)
    (value : View → Coefficient)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (first second : before ⟶ after) :
    Mettapedia.GSLT.Distinction.LevelAccounts.QualifiedReplay
        (sourceAccount annotation interpretation authority required needed interpret reader notice origin base value) first second ↔
      Mettapedia.GSLT.Distinction.LevelAccounts.QualifiedReplay
        (targetAccount annotation interpretation authority required needed interpret reader notice origin base value)
        ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map first)
        ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map second) := by
  have law := account_transport annotation interpretation authority required needed interpret reader notice
    origin base value
  have left := congrArg (fun account => account.of first) law
  have right := congrArg (fun account => account.of second) law
  change _ = _ ↔ _ = _
  rw [show (targetAccount annotation interpretation authority required needed interpret reader notice origin base value).of
      ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map first) = _
    from left,
    show (targetAccount annotation interpretation authority required needed interpret reader notice origin base value).of
      ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map second) = _
    from right]

/-- Enabled and disabled observation delegate to the same cursor. The
optional buffer is outside the semantic packet, invoice and Need world. -/
def observedAdvance (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base)
    (record : Option (Recording.Prefix (View))) :=
  (Cursor.advance (Source origin) Client
      (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance packet,
    record.map fun captured => captured.append
      (PassiveReader.readSuffix annotation interpretation authority required needed interpret reader notice
        origin FreeMonoid.of allowance (0, .paused packet)).toList)

/-- Forgetting recording recovers the actual full cursor result, including
its retained continuation, current context and paid account. -/
theorem observed_advance_erasure (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base)
    (record : Option (Recording.Prefix (View))) :
    (observedAdvance annotation interpretation authority required needed interpret reader notice origin allowance packet record).1 =
      Cursor.advance (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance packet := rfl

/-- Disabled observation neither reads a history nor changes the operational
outcome. This is a construction law; it is not a compiled-C cost claim. -/
theorem disabled_recording (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base) :
    observedAdvance annotation interpretation authority required needed interpret reader notice origin allowance packet none =
      (Cursor.advance (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance packet, none) := rfl

/-- The resumed observer starts at the exact retained packet. An already
finished outcome supplies the empty suffix and cannot repeat source work. -/
def observedResume (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base)
    (record : Option (Recording.Prefix (View))) :=
  (Cursor.resume (Source origin) Client
      (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance earlier,
    record.map fun captured => captured.append
      (PassiveReader.readSuffix annotation interpretation authority required needed interpret reader notice
        origin FreeMonoid.of allowance earlier).toList)


/-- The efficient passive recording is exactly the full ordered account of
the existing generated history, including its return inspection. -/
theorem observed_advance_history (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base) (record : Option (Recording.Prefix View)) :
    (observedAdvance annotation interpretation authority required needed interpret reader notice origin allowance packet record).2 =
      recordSuffix annotation interpretation authority required needed interpret reader notice origin base record
        (fun _ => NativeControlCursor.ProtocolHistory.advanceHistory (Source origin) Client
          (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance packet) := by
  cases record with
  | none => rfl
  | some captured =>
      exact congrArg (fun word : FreeMonoid View => some (captured.append word.toList))
        (PassiveReader.exact_account annotation interpretation authority required needed interpret reader notice
          origin FreeMonoid.of allowance (0, .paused packet)).symm

/-- Resumed recording uses the same actual midpoint and full reached context.
Its account is the suffix alone; already paid work is not replayed. -/
theorem observed_resume_history (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base) (record : Option (Recording.Prefix View)) :
    (observedResume annotation interpretation authority required needed interpret reader notice origin allowance earlier record).2 =
      recordSuffix annotation interpretation authority required needed interpret reader notice origin base record
        (fun _ => NativeControlCursor.ProtocolHistory.resumeHistory (Source origin) Client
          (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance earlier) := by
  cases record with
  | none => rfl
  | some captured =>
      exact congrArg (fun word : FreeMonoid View => some (captured.append word.toList))
        (PassiveReader.exact_account annotation interpretation authority required needed interpret reader notice
          origin FreeMonoid.of allowance earlier).symm

/-- Stopping retains the exact captured prefix; later execution continues
with recording disabled. Forgetting may then discard that saved prefix,
without changing either invocation outcome. -/
def stopAndResume (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base)
    (record : Recording.Prefix (View)) :=
  ((observedResume annotation interpretation authority required needed interpret reader notice origin allowance earlier none).1,
    record)

/-- Stopping at a paid boundary is conservative for execution and retains
the historical interval as it was, rather than calling the suffix complete. -/
theorem stop_preserves_prefix (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base)
    (record : Recording.Prefix (View)) :
    stopAndResume annotation interpretation authority required needed interpret reader notice origin allowance earlier record =
      (Cursor.resume (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance earlier, record) := rfl



/-- A successful callback contributes to its own branch's copied prefix.
The global chronological account is not substituted for this local word. -/
theorem accepted_callback_appends_once (caller : Service.Node) (job : Job)
    (carried factor : Word) (returned : isHalted job.cursor.state = true)
    (interpreted : readout interpretation job = some factor) :
    (Provider.sourceBase annotation interpretation).emit (.inr (caller, job, []), carried) = none ∧
      (Provider.sourceBase annotation interpretation).successors (.inr (caller, job, []), carried) =
        [(.inl (resumeNode caller job), carried * factor)] := by
  simp [Provider.sourceBase,
    interpreted_callback_resumes_once annotation interpretation caller job factor returned interpreted]

/-- The child factor precedes the parent's later factor even when both are
zero or their coefficient multiplication would be noncommutative. -/
theorem nested_callback_appends_once (caller : Service.Node) (job parent : Job) (parents : List Job)
    (carried factor : Word) (returned : isHalted job.cursor.state = true)
    (interpreted : readout interpretation job = some factor) :
    (Provider.sourceBase annotation interpretation).successors
        (.inr (caller, job, parent :: parents), carried) =
      [(.inr (caller, resumeJob parent job, parents), carried * factor)] := by
  simp only [Provider.sourceBase, source, WeightedBranchingResumption.nestedPendingSource,
    grade, returned, ↓reduceIte, interpreted, List.map_cons, List.map_nil]

/-- The independently constructed core provider transports the entire generated
history, with its real start/end packets, not merely its coefficient product. -/
theorem advance_history_transport (origin allowance : Nat) {base : Unit}
    (packet : Cursor.Packet (Source origin) Client base) :
    HEq ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map
      (NativeControlCursor.ProtocolHistory.advanceHistory (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance packet))
      (NativeControlCursor.ProtocolHistory.advanceHistory (Target origin) Client
        (CurrentData.targetCharge annotation interpretation authority required needed interpret origin) allowance
        ((Realization origin).lift.packet Client packet)) :=
  NativeControlCursor.ProtocolHistory.hom_advanceHistory Client (Realization origin).lift _ _ allowance packet

/-- Paused and completed outcomes both transport their exact chronological
suffix; completion has no source event that could replay an effect. -/
theorem resume_history_transport (origin allowance : Nat) {base : Unit}
    (earlier : Nat × Cursor.Outcome (Source origin) Client base) :
    HEq ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map
      (NativeControlCursor.ProtocolHistory.resumeHistory (Source origin) Client
        (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance earlier))
      (NativeControlCursor.ProtocolHistory.resumeHistory (Target origin) Client
        (CurrentData.targetCharge annotation interpretation authority required needed interpret origin) allowance
        (earlier.1, (Realization origin).mapOutcome reader notice earlier.2)) :=
  NativeControlCursor.ProtocolHistory.hom_resumeHistory Client (Realization origin).lift _ _ allowance earlier

/-- Passive recording has the ordinary endpoint erasure of this actual
realization. The functor does not authorize source execution or publication. -/
theorem history_endpoint_erasure (origin : Nat) (base : Unit) :
    (NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories ⋙
        eraseHistory (NativeControlCursor.ProtocolHistory.system (Target origin) Client base) =
      eraseHistory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base) ⋙
        (NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).erasedHistories :=
  NativeControlCursor.ProtocolHistory.hom_histories_erasure Client (Realization origin).lift base

/-- Forgetting an optional recording changes no semantic state. Its discarded
payload is not interpreted as an instruction to repeat that historical run. -/
def forgetRecording (record : Option (Recording.Prefix View)) : Option (Recording.Prefix View) :=
  match record with | none | some _ => none

@[simp] theorem forget_recording_is_disabled (record : Option (Recording.Prefix View)) :
    forgetRecording record = none := by cases record <;> rfl


/-- Scoped consumers reuse the actual shared-coefficient ledger. Each entry
retains the complete authored production and coefficient; its observation ID
is the poll occurrence and its dependency is the genuine shared producer cell.
This chronological observation ledger does not merge alternative branch words
or issue authority. Each answer retains its own world and Word. -/
def ledgerBlock (origin : Nat) : View →
    FreeMonoid (Mettapedia.Algebra.SharedCoefficientLedger.Factor Nat CellId Factor)
  | .accepted ordinal _ (some selected) => FreeMonoid.ofList
      (selected.factors.toList.zipIdx.map fun (factor, position) =>
        ⟨RetainedInvocation.GradedHistory.eventNumber origin ordinal position,
          factor.production.cell, factor⟩)
  | _ => 1

/-- A consumer claims its selected real factor interval before readout.
Re-entering that scope cannot charge its already observed producers again. -/
theorem handled_factor_interval_is_not_recounted (entry owner : Nat)
    (origin : Nat) (base : Unit)
    {before after : HistoryCategory (NativeControlCursor.ProtocolHistory.system (Source origin) Client base)}
    (history : before ⟶ after) :
    Mettapedia.Algebra.SharedCoefficientLedger.Scoped.selected entry
      (Mettapedia.Algebra.SharedCoefficientLedger.Scoped.handle entry owner
        ⟨((sourceAccount annotation interpretation authority required needed interpret reader notice origin base
          (ledgerBlock origin)).of history).toList, fun _ => none⟩) = [] :=
  Mettapedia.Algebra.SharedCoefficientLedger.Scoped.selected_after_handle _ _ _


/-- Cached delivery of a genuine shared cell contributes neither a returned
callback factor nor a fresh authored-production request. The instruction still
has its ordinary polling and cache-delivery observation. -/
theorem cached_callback_delivery_has_no_new_factor (caller : Service.Node) (job : Job)
    (parents : List Job) (cell : CellId) (stack : List (Frame Resume))
    (origin : Origin) (value : Value)
    (control : job.cursor.state.control = .force cell stack)
    (cached : job.cursor.state.world.heap.lookup cell = some ⟨origin, .value value⟩) :
    factorBlock interpretation (.inr (caller, job, parents)) = 1 ∧
      ∀ (after : Service.Node) (ordinal : Nat), request annotation job.cursor after ordinal = .inl 1  := by
  rcases job with ⟨production, coefficient, captured, ⟨⟨world, actualControl, work⟩, trace⟩⟩
  dsimp only at control cached ⊢
  subst actualControl
  exact ⟨rfl, fun after ordinal =>
    cached_delivery_starts_no_callback annotation world cell origin value stack work ordinal trace after cached⟩

/-- A later handler can be composed from its own local cursor square. The
whole generated mixed-source history maps through the actual intermediate
representation, with no premise about complete-run agreement. -/
theorem advance_history_composition (origin allowance : Nat)
    (third : Cursor.Provider
      (OperationCostProtocol.Indexed.protocol (NativeControlCursor.protocol Provider.Item)
        RetainedInvocation.OwnData.Refused))
    (later : Cursor.Hom (Target origin) third) (thirdCharge : Cursor.Charge third)
    {base : Unit} (packet : Cursor.Packet (Source origin) Client base) :
    HEq ((NativeControlCursor.ProtocolHistory.homForward Client later base).histories.map
      ((NativeControlCursor.ProtocolHistory.homForward Client (Realization origin).lift base).histories.map
        (NativeControlCursor.ProtocolHistory.advanceHistory (Source origin) Client
          (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin) allowance packet)))
      (NativeControlCursor.ProtocolHistory.advanceHistory third Client thirdCharge allowance
        (((Realization origin).lift.comp later).packet Client packet)) :=
  NativeControlCursor.ProtocolHistory.hom_advanceHistory_comp Client (Realization origin).lift later
    (CurrentData.sourceCharge annotation interpretation authority required needed interpret origin)
    (CurrentData.targetCharge annotation interpretation authority required needed interpret origin)
    thirdCharge allowance packet

/-- Repeated inspections of a returned uninterpreted callback are parked
protocol observations, not callback progress or another production factor. -/
theorem parked_observation_is_not_callback_work (caller : Service.Node) (job : Job) (parents : List Job)
    (carried : Word)
    (returned : isHalted job.cursor.state = true) (uninterpreted : readout interpretation job = none) :
    phase interpretation (.inr (caller, job, parents)) = .parked (parents.length + 1) ∧
      factorBlock interpretation (.inr (caller, job, parents)) = 1 ∧
      (Provider.sourceBase annotation interpretation).emit (.inr (caller, job, parents), carried) = none ∧
      (Provider.sourceBase annotation interpretation).successors (.inr (caller, job, parents), carried) =
        [(.inr (caller, job, parents), carried)] := by
  have held := Provider.parked_source_is_retained annotation interpretation (.inr (caller, job, parents)) carried
    (caller, job, parents)
    (a_returned_but_uninterpreted_callback_retains_its_caller annotation interpretation caller job parents
      returned uninterpreted)
  refine ⟨?_, ?_, held.1, held.2⟩
  · simp only [phase, returned, uninterpreted, Option.isNone_none, Bool.true_and, ↓reduceIte]
  · simp only [factorBlock, returned, ↓reduceIte, uninterpreted, Option.getD_none]

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.History

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.CurrentData.Controls

open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef

def paidPrefix := run 9 context
def complete := run 100 context

/-- These are service-owner updates of the current authority, not operations
by which a program recovers permission from a copied description. -/
def revoke (saved : Saved) := supply
  (fun current => { current with live := { current.live with
    point := Cursor.ReadOnlyQuery.OwnWrite.Controls.revoked } }) saved

def regrant (saved : Saved) := supply
  (fun current => { current with live := { current.live with point := ⟨true, .consume⟩ } }) saved

def revoked := resume 10 (revoke paidPrefix)
def recovered := resume 100 (retry (regrant revoked))
def interfered := resume 10 (retry (supply
  (fun current => { current with live := { current.live with
    store := OrderedDependencyStore.appendOwn current.live.store 0 [99] } }) (regrant revoked)))

def phases (saved : Saved) := (stateOf saved).1.search.frontier.map fun node =>
  match node.state.1 with
  | .inl _ => none
  | .inr (_, job, parents) => some (job.production.row.index, parents.length,
      job.cursor.state.work.transitions, (FreeMonoid.toList node.state.2).length)

/-- The motivating accepted prefix really lies inside an owned callback,
after its first external effect and before forcing the borrowed producer. -/
theorem accepted_prefix_is_an_actual_running_callback :
    paidPrefix.1 = 9 ∧ rows paidPrefix = none ∧
      OrderedDependencyStore.query (stateOf paidPrefix).2.live.store 0 = [7, 7, 5] ∧
      (phases paidPrefix).length = 1 ∧
      ((stateOf paidPrefix).1.search.frontier.map fun node => match node.state.1 with
        | .inl _ => false
        | .inr (_, job, _) => !NeedReference.isHalted job.cursor.state) = [true] := by
  decide +kernel

/-- Revocation leaves the exact inventory, caller, callback, parents and
factor prefix untouched. It consumes no source poll and no further credit. -/
theorem revocation_retains_the_exact_paid_callback :
    refusal revoked = some (.inl .admission) ∧
      (stateOf revoked).1 = (stateOf paidPrefix).1 ∧
      accountOf revoked = accountOf paidPrefix ∧ revoked.1 = paidPrefix.1 ∧
      OrderedDependencyStore.query (stateOf revoked).2.live.store 0 = [7, 7, 5] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Fresh permission resumes the same actual callback world and cached
producer. Its two accepted effects occur once, and the complete source and
invoice coincide with an uninterrupted invocation. -/
theorem regrant_resumes_without_repeating_prior_effects :
    (rows recovered).map List.length = some 1 ∧
      OrderedDependencyStore.query (stateOf recovered).2.live.store 0 = [7, 7, 5, 7] ∧
      recovered.1 = complete.1 ∧ accountOf recovered = accountOf complete ∧
      (stateOf recovered).1 = (stateOf complete).1 ∧
      (rows recovered).map (fun items => items.map fun (item : Provider.Item) =>
        (FreeMonoid.toList item.1.2).map Weighted.Controls.factorView) =
        some [[("choose", 0, SharedSource.Controls.integer 7)]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rfl
  · decide +kernel

/-- Permission does not refresh the snapshot a retained query consulted.
An intervening same-scope data write refuses without advancing the callback,
changing its paid account, or repairing historical reads. -/
theorem fresh_permission_does_not_heal_stale_query_data :
    refusal interfered = some (.inl .stale) ∧
      (stateOf interfered).1 = (stateOf paidPrefix).1 ∧
      accountOf interfered = accountOf paidPrefix ∧ interfered.1 = paidPrefix.1 ∧
      OrderedDependencyStore.query (stateOf interfered).2.live.store 0 = [7, 7, 5, 99] ∧
      (stateOf interfered).2.pastReads = context.pastReads := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.CurrentData.Controls


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.CurrentData.Controls

open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef

attribute [local instance] permissionDecision admissionDecision

/-- The publication reads a genuine absent coordinate distinct from the
selected service's accepted effect coordinate. Its write is justified below
by the actual completed body value, not by a provisional coefficient. -/
def transaction : ValidatedCommit.Transaction (Fin 3) (List Nat) :=
  .read 1 fun found => .pure (if found.isEmpty then [(2, [7])] else [])

def returnedNumber (item : Provider.Item) : Option Nat :=
  match NeedExecution.haltedOutcome item.1.1.state with
  | some (.value (.native (.grounded (.int value)))) => some value.toNat
  | _ => none

def writes : List Provider.Item → ValidatedCommit.Writes (Fin 3) (List Nat) :=
  fun rows => (rows.filterMap returnedNumber).map fun number => (2, [number])

abbrev raw := rawSource annotation number revocationWorlds required needed act
abbrev guard : OperationCostProtocol.Indexed.Gate (Denied := RetainedInvocation.OwnData.Refused) raw :=
  sourceGate annotation number revocationWorlds required needed act
abbrev invoice : OperationCostProtocol.Indexed.Invoice raw :=
  sourceInvoice annotation number revocationWorlds required needed act 305
abbrev Inv := OperationCostProtocol.Indexed.Invocation (Key := Fin 3) (Value := List Nat)
  raw guard (@profiles) (@replay) invoice reader notice ()

def held : Inv :=
  ⟨(OrderedDependencyStore.query context.live.store, transaction), complete.1, complete.2⟩

def completedRows : List Provider.Item := (rows complete).getD []

/-- The real source completed exactly one body value, which realizes the
nonempty write list of the independently executed absence-reading transaction. -/
theorem completed_body_realizes_publication :
    completedRows.filterMap returnedNumber = [7] ∧
      ReadOnlyQuery.run held.submission.1 held.submission.2 =
        ⟨[(2, [7])], [(1, [])]⟩ ∧
      OperationCostProtocol.Indexed.Invocation.Ready (source := raw) (gate := guard)
        (profiles := @profiles) (replay := @replay) (invoice := invoice)
        (reader := reader) (notice := notice) writes held := by
  refine ⟨?_, ?_, (), completedRows, (stateOf complete, accountOf complete), ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

theorem ready : OperationCostProtocol.Indexed.Invocation.Ready (source := raw) (gate := guard)
    (profiles := @profiles) (replay := @replay) (invoice := invoice)
    (reader := reader) (notice := notice) writes held := completed_body_realizes_publication.2.2

def grant (generation : Nat) : OperationCostProtocol.Indexed.CheckedGrant.Requirement Nat Nat Access :=
  ⟨⟨19, 23, generation⟩, .consume⟩

local instance grantPermission (point : IndexedAuthority.Point revocationWorlds) (generation : Nat) :
    Decidable (FrameUpdate point.authority (grant generation).required) :=
  admissionDecision point

def published (point : IndexedAuthority.Point revocationWorlds) (generation current : Nat)
    (store : Fin 3 → List Nat) (history : OperationCostProtocol.NativePoll.History) :=
  held.publishCheckedGrant raw guard (@profiles) (@replay) invoice reader notice writes ready history
    revocationWorlds point (grant generation) (grant current).handle .admission store

def publicationView : OperationCostProtocol.Indexed.Invocation.PublicationResult (Key := Fin 3) (Value := List Nat)
    (source := raw) (gate := guard) (profiles := @profiles) (replay := @replay) (invoice := invoice)
    (reader := reader) (notice := notice) () → Nat × List Nat
  | .authorityRefused _ _ _ => (0, [])
  | .dependencyConflict _ _ => (1, [])
  | .committed store _ => (2, store 2)

/-- Current rights and generation permit publication of the completed body;
revocation or a same-right regrant cannot revive the obsolete handle. -/
theorem publication_rechecks_current_permission_and_generation (history : OperationCostProtocol.NativePoll.History) :
    publicationView (published ⟨true, .consume⟩ 1 1
      (OrderedDependencyStore.query (stateOf complete).2.live.store) history) = (2, [7]) ∧
      published Cursor.ReadOnlyQuery.OwnWrite.Controls.revoked 1 1
        (OrderedDependencyStore.query (stateOf complete).2.live.store) history =
          .authorityRefused .admission held history ∧
      published ⟨true, .consume⟩ 1 2
        (OrderedDependencyStore.query (stateOf complete).2.live.store) history =
          .authorityRefused .admission held history ∧
      publicationView (published ⟨true, .consume⟩ 2 2
        (OrderedDependencyStore.query (stateOf complete).2.live.store) history) = (2, [7]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- A fresh grant cannot validate an old absence premise. Refusal retains the
actual completed invocation, its exact paid account and the supplied history. -/
theorem fresh_grant_does_not_repair_a_changed_absence (history : OperationCostProtocol.NativePoll.History) :
    published ⟨true, .consume⟩ 2 2
      (OrderedDependencyStore.query (OrderedDependencyStore.appendOwn
        (stateOf complete).2.live.store 1 [99])) history =
      .dependencyConflict held history := by
  rfl

/-- The actual local mixed-source handler transports the full publication
choice, including stale-generation and dependency-refusal residuals. Native
construction/authentication of the supplied history is a separate boundary. -/
theorem current_publication_transport (point : IndexedAuthority.Point revocationWorlds)
    (generation current : Nat) (store : Fin 3 → List Nat)
    (history : OperationCostProtocol.NativePoll.History) :
    (handler annotation number revocationWorlds required needed act 305).publication reader notice
      (published point generation current store history) =
      ((handler annotation number revocationWorlds required needed act 305).invocation reader notice held).publishCheckedGrant
          (rawTarget annotation number revocationWorlds required needed act)
          (targetGate annotation number revocationWorlds required needed act) (@profiles) (@replay)
          (targetInvoice annotation number revocationWorlds required needed act 305) reader notice writes
          ((handler annotation number revocationWorlds required needed act 305).invocation_ready reader notice writes held ready)
          history revocationWorlds point (grant generation) (grant current).handle .admission store :=
  (handler annotation number revocationWorlds required needed act 305).publishCheckedGrant
    reader notice writes held ready history revocationWorlds point (grant generation) (grant current).handle .admission store

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.CurrentData.Controls


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.History.Controls

open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.LanguageDef
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

abbrev required := RetainedInvocation.Examples.OwnData.required
abbrev needed := RetainedInvocation.Examples.OwnData.needed
abbrev context := RetainedInvocation.Examples.OwnData.context

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (action : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (required action point.world)) :=
  RetainedInvocation.Examples.OwnData.permissionDecision point action

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) :=
  RetainedInvocation.Examples.OwnData.admissionDecision point

abbrev act := CurrentData.Controls.act
abbrev number := Weighted.Controls.number

/-- The rich outer callback actually invokes an authored score service. Its
nested coefficient is zero, rather than an absent production. -/
def annotation (production : AuthoredProduction) : Option Coefficient :=
  if production.head = "choose" then
    some (.rich ⟨0, 0, 0,
      .emit 5 (.call (.source Weighted.Controls.scoreProgram []) (.head (.expression [.symbol "score"]))),
      ids, Fin.elim0, Fin.elim0⟩)
  else if production.head = "score" then some (.authored (Weighted.Controls.integer 0)) else none

abbrev source := CurrentData.sourceProvider annotation number revocationWorlds required needed act 407
abbrev target := CurrentData.targetProvider annotation number revocationWorlds required needed act 407
abbrev charge : Cursor.Charge source := CurrentData.sourceCharge annotation number revocationWorlds required needed act 407
abbrev reader := SourceProducerCardinality.CallingModes.client .direct Provider.Item
abbrev notice : OperationCostProtocol.Indexed.Notice (NativeControlCursor.protocol Provider.Item)
    RetainedInvocation.OwnData.Refused := CurrentData.notice
abbrev client := OperationCostProtocol.Indexed.client reader notice
abbrev Saved := Nat × Cursor.Outcome source client ()

def packet := CurrentData.modePacket annotation number revocationWorlds required needed act .direct 407
  (Provider.initial Weighted.Controls.roots, context) (OperationCostProtocol.initial CurrentData.profile 1000)

def run (fuel : Nat := 400) : Saved := Cursor.advance source client charge fuel packet

def history (fuel : Nat := 400) := NativeControlCursor.ProtocolHistory.advanceHistory source client charge fuel packet

def factorSummary (factor : Factor) : String × Nat × Int :=
  (factor.production.head, factor.production.row.index,
    match factor.value with | .grounded (.int number) => number | _ => -1)

def factors (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 factorValue fuel (0, .paused packet)).toList.map factorSummary

def effects (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 effectValue fuel (0, .paused packet)).toList

def caches (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 cacheValue fuel (0, .paused packet)).toList

def ledger (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 (ledgerBlock 407) fuel (0, .paused packet)).toList

def word (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 FreeMonoid.of fuel (0, .paused packet)).toList

def rowsAt (saved : Saved) : Option (List Provider.Item) :=
  match saved.2 with | .done ⟨(), .inl rows, _⟩ => some rows | _ => none

def wordsAt (saved : Saved) := (rowsAt saved).map fun rows =>
  rows.map fun (item : Provider.Item) => item.1.2.toList.map factorSummary

def rows := rowsAt (run 400)
def words := wordsAt (run 400)

def stateOf (saved : Saved) : Provider.Inventory × CurrentData.Context revocationWorlds (Entry := Nat) (width := 3) :=
  match saved.2 with | .paused packet => packet.2.2.1 | .done result => result.2.2.1

def tag : View → Nat
  | .inert => 0
  | .finish => 1
  | .refused _ => 2
  | .accepted _ _ none => 3
  | .accepted _ _ (some inspected) =>
      if !inspected.factors.toList.isEmpty then 4 else
      match inspected.completed with
      | some completed => match completed.kind with | .production => 5 | .delivery => 6
      | none => if inspected.effect.isSome then 7 else if inspected.returned.isSome then 8
          else if inspected.firings.isEmpty then 9 else 10

def recorded (fuel capacity : Nat) :=
  (observedAdvance annotation number revocationWorlds required needed act reader notice 407 fuel packet
    (some (Recording.Prefix.initial capacity))).2


/-! The fixture certificates use the existing cursor transitions. Data fields
are materialized once; function closures stay shared. Their generated terms and
local equality proofs are checked by Lean's ordinary kernel. -/

open Lean Meta in
private partial def normalizeCutData (input : Expr) : MetaM Expr := do
  let rec visit (expression : Expr) : MonadCacheT Expr Expr MetaM Expr :=
    checkCache expression fun _ => Core.withIncRecDepth do
      if (← isType expression) || (← isProof expression) then return expression
      let expression ← whnf expression
      match expression with
      | .lam .. | .forallE .. => return expression
      | .app .. =>
          let head := expression.getAppFn
          let mut arguments := expression.getAppArgs
          let info ← getFunInfoNArgs head arguments.size
          for index in [:arguments.size] do
            if index >= info.paramInfo.size || info.paramInfo[index]!.isExplicit then
              arguments ← arguments.modifyM index visit
          return mkAppN head arguments
      | .proj owner field value => return mkProj owner field (← visit value)
      | _ => return expression
  visit input |>.run

open Lean Meta Elab Term in
elab "normalized_cursor_cut% " value:term : term <= expected => do
  let expression ← elabTerm value expected
  Term.synthesizeSyntheticMVarsNoPostponing
  normalizeCutData (← instantiateMVars expression)

private noncomputable def cut0 : Saved := normalized_cursor_cut% (0, .paused packet)

open Lean Meta Elab Tactic in
elab "checked_cut_rfl" : tactic => withMainContext do
  match ← getGoals with
  | [] => return
  | goal :: _ =>
      let target ← whnf (← instantiateMVars (← goal.getType))
      unless target.isAppOfArity ``Eq 3 do
        throwError "an equality is required, got {target}"
      goal.assign (← mkEqRefl target.getAppArgs[2]!)
      replaceMainGoal []
private noncomputable def cut1 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut0)
private theorem step1 : Cursor.resume source client charge 1 cut0 = cut1 := by checked_cut_rfl
private noncomputable def cut2 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut1)
private theorem step2 : Cursor.resume source client charge 1 cut1 = cut2 := by checked_cut_rfl
private noncomputable def cut3 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut2)
private theorem step3 : Cursor.resume source client charge 1 cut2 = cut3 := by checked_cut_rfl
private noncomputable def cut4 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut3)
private theorem step4 : Cursor.resume source client charge 1 cut3 = cut4 := by checked_cut_rfl
private noncomputable def cut5 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut4)
private theorem step5 : Cursor.resume source client charge 1 cut4 = cut5 := by checked_cut_rfl
private noncomputable def cut6 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut5)
private theorem step6 : Cursor.resume source client charge 1 cut5 = cut6 := by checked_cut_rfl
private noncomputable def cut7 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut6)
private theorem step7 : Cursor.resume source client charge 1 cut6 = cut7 := by checked_cut_rfl
private noncomputable def cut8 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut7)
private theorem step8 : Cursor.resume source client charge 1 cut7 = cut8 := by checked_cut_rfl
private noncomputable def cut9 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut8)
private theorem step9 : Cursor.resume source client charge 1 cut8 = cut9 := by checked_cut_rfl
private noncomputable def cut10 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut9)
private theorem step10 : Cursor.resume source client charge 1 cut9 = cut10 := by checked_cut_rfl
private noncomputable def cut11 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut10)
private theorem step11 : Cursor.resume source client charge 1 cut10 = cut11 := by checked_cut_rfl
private noncomputable def cut12 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut11)
private theorem step12 : Cursor.resume source client charge 1 cut11 = cut12 := by checked_cut_rfl
private noncomputable def cut13 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut12)
private theorem step13 : Cursor.resume source client charge 1 cut12 = cut13 := by checked_cut_rfl
private noncomputable def cut14 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut13)
private theorem step14 : Cursor.resume source client charge 1 cut13 = cut14 := by checked_cut_rfl
private noncomputable def cut15 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut14)
private theorem step15 : Cursor.resume source client charge 1 cut14 = cut15 := by checked_cut_rfl
private noncomputable def cut16 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut15)
private theorem step16 : Cursor.resume source client charge 1 cut15 = cut16 := by checked_cut_rfl
private noncomputable def cut17 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut16)
private theorem step17 : Cursor.resume source client charge 1 cut16 = cut17 := by checked_cut_rfl
private noncomputable def cut18 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut17)
private theorem step18 : Cursor.resume source client charge 1 cut17 = cut18 := by checked_cut_rfl
private noncomputable def cut19 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut18)
private theorem step19 : Cursor.resume source client charge 1 cut18 = cut19 := by checked_cut_rfl
private noncomputable def cut20 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut19)
private theorem step20 : Cursor.resume source client charge 1 cut19 = cut20 := by checked_cut_rfl
private noncomputable def cut21 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut20)
private theorem step21 : Cursor.resume source client charge 1 cut20 = cut21 := by checked_cut_rfl
private noncomputable def cut22 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut21)
private theorem step22 : Cursor.resume source client charge 1 cut21 = cut22 := by checked_cut_rfl
private noncomputable def cut23 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut22)
private theorem step23 : Cursor.resume source client charge 1 cut22 = cut23 := by checked_cut_rfl
private noncomputable def cut24 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut23)
private theorem step24 : Cursor.resume source client charge 1 cut23 = cut24 := by checked_cut_rfl
private noncomputable def cut25 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut24)
private theorem step25 : Cursor.resume source client charge 1 cut24 = cut25 := by checked_cut_rfl
private noncomputable def cut26 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut25)
private theorem step26 : Cursor.resume source client charge 1 cut25 = cut26 := by checked_cut_rfl
private noncomputable def cut27 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut26)
private theorem step27 : Cursor.resume source client charge 1 cut26 = cut27 := by checked_cut_rfl
private noncomputable def cut28 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut27)
private theorem step28 : Cursor.resume source client charge 1 cut27 = cut28 := by checked_cut_rfl
private noncomputable def cut29 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut28)
private theorem step29 : Cursor.resume source client charge 1 cut28 = cut29 := by checked_cut_rfl
private noncomputable def cut30 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut29)
private theorem step30 : Cursor.resume source client charge 1 cut29 = cut30 := by checked_cut_rfl
private noncomputable def cut31 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut30)
private theorem step31 : Cursor.resume source client charge 1 cut30 = cut31 := by checked_cut_rfl
private noncomputable def cut32 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut31)
private theorem step32 : Cursor.resume source client charge 1 cut31 = cut32 := by checked_cut_rfl
private noncomputable def cut33 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut32)
private theorem step33 : Cursor.resume source client charge 1 cut32 = cut33 := by checked_cut_rfl
private noncomputable def cut34 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut33)
private theorem step34 : Cursor.resume source client charge 1 cut33 = cut34 := by checked_cut_rfl
private noncomputable def cut35 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut34)
private theorem step35 : Cursor.resume source client charge 1 cut34 = cut35 := by checked_cut_rfl
private noncomputable def cut36 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut35)
private theorem step36 : Cursor.resume source client charge 1 cut35 = cut36 := by checked_cut_rfl
private noncomputable def cut37 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut36)
private theorem step37 : Cursor.resume source client charge 1 cut36 = cut37 := by checked_cut_rfl
private noncomputable def cut38 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut37)
private theorem step38 : Cursor.resume source client charge 1 cut37 = cut38 := by checked_cut_rfl
private noncomputable def cut39 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut38)
private theorem step39 : Cursor.resume source client charge 1 cut38 = cut39 := by checked_cut_rfl
private noncomputable def cut40 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut39)
private theorem step40 : Cursor.resume source client charge 1 cut39 = cut40 := by checked_cut_rfl
private noncomputable def cut41 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut40)
private theorem step41 : Cursor.resume source client charge 1 cut40 = cut41 := by checked_cut_rfl
private noncomputable def cut42 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut41)
private theorem step42 : Cursor.resume source client charge 1 cut41 = cut42 := by checked_cut_rfl
private noncomputable def cut43 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut42)
private theorem step43 : Cursor.resume source client charge 1 cut42 = cut43 := by checked_cut_rfl
private noncomputable def cut44 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut43)
private theorem step44 : Cursor.resume source client charge 1 cut43 = cut44 := by checked_cut_rfl
private noncomputable def cut45 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut44)
private theorem step45 : Cursor.resume source client charge 1 cut44 = cut45 := by checked_cut_rfl
private noncomputable def cut46 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut45)
private theorem step46 : Cursor.resume source client charge 1 cut45 = cut46 := by checked_cut_rfl
private noncomputable def cut47 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut46)
private theorem step47 : Cursor.resume source client charge 1 cut46 = cut47 := by checked_cut_rfl
private noncomputable def cut48 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut47)
private theorem step48 : Cursor.resume source client charge 1 cut47 = cut48 := by checked_cut_rfl
private noncomputable def cut49 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut48)
private theorem step49 : Cursor.resume source client charge 1 cut48 = cut49 := by checked_cut_rfl
private noncomputable def cut50 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut49)
private theorem step50 : Cursor.resume source client charge 1 cut49 = cut50 := by checked_cut_rfl
private noncomputable def cut51 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut50)
private theorem step51 : Cursor.resume source client charge 1 cut50 = cut51 := by checked_cut_rfl
private noncomputable def cut52 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut51)
private theorem step52 : Cursor.resume source client charge 1 cut51 = cut52 := by checked_cut_rfl
private noncomputable def cut53 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut52)
private theorem step53 : Cursor.resume source client charge 1 cut52 = cut53 := by checked_cut_rfl
private noncomputable def cut54 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut53)
private theorem step54 : Cursor.resume source client charge 1 cut53 = cut54 := by checked_cut_rfl
private noncomputable def cut55 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut54)
private theorem step55 : Cursor.resume source client charge 1 cut54 = cut55 := by checked_cut_rfl
private noncomputable def cut56 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut55)
private theorem step56 : Cursor.resume source client charge 1 cut55 = cut56 := by checked_cut_rfl
private noncomputable def cut57 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut56)
private theorem step57 : Cursor.resume source client charge 1 cut56 = cut57 := by checked_cut_rfl
private noncomputable def cut58 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut57)
private theorem step58 : Cursor.resume source client charge 1 cut57 = cut58 := by checked_cut_rfl
private noncomputable def cut59 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut58)
private theorem step59 : Cursor.resume source client charge 1 cut58 = cut59 := by checked_cut_rfl
private noncomputable def cut60 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut59)
private theorem step60 : Cursor.resume source client charge 1 cut59 = cut60 := by checked_cut_rfl
private noncomputable def cut61 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut60)
private theorem step61 : Cursor.resume source client charge 1 cut60 = cut61 := by checked_cut_rfl
private noncomputable def cut62 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut61)
private theorem step62 : Cursor.resume source client charge 1 cut61 = cut62 := by checked_cut_rfl
private noncomputable def cut63 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut62)
private theorem step63 : Cursor.resume source client charge 1 cut62 = cut63 := by checked_cut_rfl
private noncomputable def cut64 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut63)
private theorem step64 : Cursor.resume source client charge 1 cut63 = cut64 := by checked_cut_rfl
private noncomputable def cut65 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut64)
private theorem step65 : Cursor.resume source client charge 1 cut64 = cut65 := by checked_cut_rfl
private noncomputable def cut66 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut65)
private theorem step66 : Cursor.resume source client charge 1 cut65 = cut66 := by checked_cut_rfl
private noncomputable def cut67 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut66)
private theorem step67 : Cursor.resume source client charge 1 cut66 = cut67 := by checked_cut_rfl
private noncomputable def cut68 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut67)
private theorem step68 : Cursor.resume source client charge 1 cut67 = cut68 := by checked_cut_rfl
private noncomputable def cut69 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut68)
private theorem step69 : Cursor.resume source client charge 1 cut68 = cut69 := by checked_cut_rfl
private noncomputable def cut70 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut69)
private theorem step70 : Cursor.resume source client charge 1 cut69 = cut70 := by checked_cut_rfl
private noncomputable def cut71 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut70)
private theorem step71 : Cursor.resume source client charge 1 cut70 = cut71 := by checked_cut_rfl
private noncomputable def cut72 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut71)
private theorem step72 : Cursor.resume source client charge 1 cut71 = cut72 := by checked_cut_rfl
private noncomputable def cut73 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut72)
private theorem step73 : Cursor.resume source client charge 1 cut72 = cut73 := by checked_cut_rfl
private noncomputable def cut74 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut73)
private theorem step74 : Cursor.resume source client charge 1 cut73 = cut74 := by checked_cut_rfl
private noncomputable def cut75 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut74)
private theorem step75 : Cursor.resume source client charge 1 cut74 = cut75 := by checked_cut_rfl
private noncomputable def cut76 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut75)
private theorem step76 : Cursor.resume source client charge 1 cut75 = cut76 := by checked_cut_rfl
private noncomputable def cut77 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut76)
private theorem step77 : Cursor.resume source client charge 1 cut76 = cut77 := by checked_cut_rfl
private noncomputable def cut78 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut77)
private theorem step78 : Cursor.resume source client charge 1 cut77 = cut78 := by checked_cut_rfl
private noncomputable def cut79 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut78)
private theorem step79 : Cursor.resume source client charge 1 cut78 = cut79 := by checked_cut_rfl
private noncomputable def cut80 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut79)
private theorem step80 : Cursor.resume source client charge 1 cut79 = cut80 := by checked_cut_rfl
private noncomputable def cut81 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut80)
private theorem step81 : Cursor.resume source client charge 1 cut80 = cut81 := by checked_cut_rfl
private noncomputable def cut82 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut81)
private theorem step82 : Cursor.resume source client charge 1 cut81 = cut82 := by checked_cut_rfl
private noncomputable def cut83 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut82)
private theorem step83 : Cursor.resume source client charge 1 cut82 = cut83 := by checked_cut_rfl
private noncomputable def cut84 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut83)
private theorem step84 : Cursor.resume source client charge 1 cut83 = cut84 := by checked_cut_rfl
private noncomputable def cut85 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut84)
private theorem step85 : Cursor.resume source client charge 1 cut84 = cut85 := by checked_cut_rfl
private noncomputable def cut86 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut85)
private theorem step86 : Cursor.resume source client charge 1 cut85 = cut86 := by checked_cut_rfl
private noncomputable def cut87 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut86)
private theorem step87 : Cursor.resume source client charge 1 cut86 = cut87 := by checked_cut_rfl
private noncomputable def cut88 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut87)
private theorem step88 : Cursor.resume source client charge 1 cut87 = cut88 := by checked_cut_rfl
private noncomputable def cut89 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut88)
private theorem step89 : Cursor.resume source client charge 1 cut88 = cut89 := by checked_cut_rfl
private noncomputable def cut90 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut89)
private theorem step90 : Cursor.resume source client charge 1 cut89 = cut90 := by checked_cut_rfl
private noncomputable def cut91 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut90)
private theorem step91 : Cursor.resume source client charge 1 cut90 = cut91 := by checked_cut_rfl
private noncomputable def cut92 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut91)
private theorem step92 : Cursor.resume source client charge 1 cut91 = cut92 := by checked_cut_rfl
private noncomputable def cut93 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut92)
private theorem step93 : Cursor.resume source client charge 1 cut92 = cut93 := by checked_cut_rfl
private noncomputable def cut94 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut93)
private theorem step94 : Cursor.resume source client charge 1 cut93 = cut94 := by checked_cut_rfl
private noncomputable def cut95 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut94)
private theorem step95 : Cursor.resume source client charge 1 cut94 = cut95 := by checked_cut_rfl
private noncomputable def cut96 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut95)
private theorem step96 : Cursor.resume source client charge 1 cut95 = cut96 := by checked_cut_rfl
private noncomputable def cut97 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut96)
private theorem step97 : Cursor.resume source client charge 1 cut96 = cut97 := by checked_cut_rfl
private noncomputable def cut98 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut97)
private theorem step98 : Cursor.resume source client charge 1 cut97 = cut98 := by checked_cut_rfl
private noncomputable def cut99 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut98)
private theorem step99 : Cursor.resume source client charge 1 cut98 = cut99 := by checked_cut_rfl
private noncomputable def cut100 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut99)
private theorem step100 : Cursor.resume source client charge 1 cut99 = cut100 := by checked_cut_rfl
private noncomputable def cut101 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut100)
private theorem step101 : Cursor.resume source client charge 1 cut100 = cut101 := by checked_cut_rfl
private noncomputable def cut102 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut101)
private theorem step102 : Cursor.resume source client charge 1 cut101 = cut102 := by checked_cut_rfl
private noncomputable def cut103 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut102)
private theorem step103 : Cursor.resume source client charge 1 cut102 = cut103 := by checked_cut_rfl
private noncomputable def cut104 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut103)
private theorem step104 : Cursor.resume source client charge 1 cut103 = cut104 := by checked_cut_rfl
private noncomputable def cut105 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut104)
private theorem step105 : Cursor.resume source client charge 1 cut104 = cut105 := by checked_cut_rfl
private noncomputable def cut106 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut105)
private theorem step106 : Cursor.resume source client charge 1 cut105 = cut106 := by checked_cut_rfl
private noncomputable def cut107 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut106)
private theorem step107 : Cursor.resume source client charge 1 cut106 = cut107 := by checked_cut_rfl
private noncomputable def cut108 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut107)
private theorem step108 : Cursor.resume source client charge 1 cut107 = cut108 := by checked_cut_rfl
private noncomputable def cut109 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut108)
private theorem step109 : Cursor.resume source client charge 1 cut108 = cut109 := by checked_cut_rfl
private noncomputable def cut110 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut109)
private theorem step110 : Cursor.resume source client charge 1 cut109 = cut110 := by checked_cut_rfl
private noncomputable def cut111 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut110)
private theorem step111 : Cursor.resume source client charge 1 cut110 = cut111 := by checked_cut_rfl
private noncomputable def cut112 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut111)
private theorem step112 : Cursor.resume source client charge 1 cut111 = cut112 := by checked_cut_rfl
private noncomputable def cut113 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut112)
private theorem step113 : Cursor.resume source client charge 1 cut112 = cut113 := by checked_cut_rfl
private noncomputable def cut114 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut113)
private theorem step114 : Cursor.resume source client charge 1 cut113 = cut114 := by checked_cut_rfl
private noncomputable def cut115 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut114)
private theorem step115 : Cursor.resume source client charge 1 cut114 = cut115 := by checked_cut_rfl
private noncomputable def cut116 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut115)
private theorem step116 : Cursor.resume source client charge 1 cut115 = cut116 := by checked_cut_rfl
private noncomputable def cut117 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut116)
private theorem step117 : Cursor.resume source client charge 1 cut116 = cut117 := by checked_cut_rfl
private noncomputable def cut118 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut117)
private theorem step118 : Cursor.resume source client charge 1 cut117 = cut118 := by checked_cut_rfl
private noncomputable def cut119 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut118)
private theorem step119 : Cursor.resume source client charge 1 cut118 = cut119 := by checked_cut_rfl
private noncomputable def cut120 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut119)
private theorem step120 : Cursor.resume source client charge 1 cut119 = cut120 := by checked_cut_rfl
private noncomputable def cut121 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut120)
private theorem step121 : Cursor.resume source client charge 1 cut120 = cut121 := by checked_cut_rfl
private noncomputable def cut122 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut121)
private theorem step122 : Cursor.resume source client charge 1 cut121 = cut122 := by checked_cut_rfl
private noncomputable def cut123 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut122)
private theorem step123 : Cursor.resume source client charge 1 cut122 = cut123 := by checked_cut_rfl
private noncomputable def cut124 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut123)
private theorem step124 : Cursor.resume source client charge 1 cut123 = cut124 := by checked_cut_rfl
private noncomputable def cut125 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut124)
private theorem step125 : Cursor.resume source client charge 1 cut124 = cut125 := by checked_cut_rfl
private noncomputable def cut126 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut125)
private theorem step126 : Cursor.resume source client charge 1 cut125 = cut126 := by checked_cut_rfl
private noncomputable def cut127 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut126)
private theorem step127 : Cursor.resume source client charge 1 cut126 = cut127 := by checked_cut_rfl
private noncomputable def cut128 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut127)
private theorem step128 : Cursor.resume source client charge 1 cut127 = cut128 := by checked_cut_rfl
private noncomputable def cut129 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut128)
private theorem step129 : Cursor.resume source client charge 1 cut128 = cut129 := by checked_cut_rfl
private noncomputable def cut130 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut129)
private theorem step130 : Cursor.resume source client charge 1 cut129 = cut130 := by checked_cut_rfl
private noncomputable def cut131 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut130)
private theorem step131 : Cursor.resume source client charge 1 cut130 = cut131 := by checked_cut_rfl
private noncomputable def cut132 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut131)
private theorem step132 : Cursor.resume source client charge 1 cut131 = cut132 := by checked_cut_rfl
private noncomputable def cut133 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut132)
private theorem step133 : Cursor.resume source client charge 1 cut132 = cut133 := by checked_cut_rfl
private noncomputable def cut134 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut133)
private theorem step134 : Cursor.resume source client charge 1 cut133 = cut134 := by checked_cut_rfl
private noncomputable def cut135 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut134)
private theorem step135 : Cursor.resume source client charge 1 cut134 = cut135 := by checked_cut_rfl
private noncomputable def cut136 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut135)
private theorem step136 : Cursor.resume source client charge 1 cut135 = cut136 := by checked_cut_rfl
private noncomputable def cut137 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut136)
private theorem step137 : Cursor.resume source client charge 1 cut136 = cut137 := by checked_cut_rfl
private noncomputable def cut138 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut137)
private theorem step138 : Cursor.resume source client charge 1 cut137 = cut138 := by checked_cut_rfl
private noncomputable def cut139 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut138)
private theorem step139 : Cursor.resume source client charge 1 cut138 = cut139 := by checked_cut_rfl
private noncomputable def cut140 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut139)
private theorem step140 : Cursor.resume source client charge 1 cut139 = cut140 := by checked_cut_rfl
private noncomputable def cut141 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut140)
private theorem step141 : Cursor.resume source client charge 1 cut140 = cut141 := by checked_cut_rfl
private noncomputable def cut142 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut141)
private theorem step142 : Cursor.resume source client charge 1 cut141 = cut142 := by checked_cut_rfl
private noncomputable def cut143 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut142)
private theorem step143 : Cursor.resume source client charge 1 cut142 = cut143 := by checked_cut_rfl
private noncomputable def cut144 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut143)
private theorem step144 : Cursor.resume source client charge 1 cut143 = cut144 := by checked_cut_rfl
private noncomputable def cut145 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut144)
private theorem step145 : Cursor.resume source client charge 1 cut144 = cut145 := by checked_cut_rfl
private noncomputable def cut146 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut145)
private theorem step146 : Cursor.resume source client charge 1 cut145 = cut146 := by checked_cut_rfl
private noncomputable def cut147 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut146)
private theorem step147 : Cursor.resume source client charge 1 cut146 = cut147 := by checked_cut_rfl
private noncomputable def cut148 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut147)
private theorem step148 : Cursor.resume source client charge 1 cut147 = cut148 := by checked_cut_rfl
private noncomputable def cut149 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut148)
private theorem step149 : Cursor.resume source client charge 1 cut148 = cut149 := by checked_cut_rfl
private noncomputable def cut150 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut149)
private theorem step150 : Cursor.resume source client charge 1 cut149 = cut150 := by checked_cut_rfl
private noncomputable def cut151 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut150)
private theorem step151 : Cursor.resume source client charge 1 cut150 = cut151 := by checked_cut_rfl
private noncomputable def cut152 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut151)
private theorem step152 : Cursor.resume source client charge 1 cut151 = cut152 := by checked_cut_rfl
private noncomputable def cut153 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut152)
private theorem step153 : Cursor.resume source client charge 1 cut152 = cut153 := by checked_cut_rfl
private noncomputable def cut154 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut153)
private theorem step154 : Cursor.resume source client charge 1 cut153 = cut154 := by checked_cut_rfl
private noncomputable def cut155 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut154)
private theorem step155 : Cursor.resume source client charge 1 cut154 = cut155 := by checked_cut_rfl
private noncomputable def cut156 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut155)
private theorem step156 : Cursor.resume source client charge 1 cut155 = cut156 := by checked_cut_rfl
private noncomputable def cut157 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut156)
private theorem step157 : Cursor.resume source client charge 1 cut156 = cut157 := by checked_cut_rfl
private noncomputable def cut158 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut157)
private theorem step158 : Cursor.resume source client charge 1 cut157 = cut158 := by checked_cut_rfl
private noncomputable def cut159 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut158)
private theorem step159 : Cursor.resume source client charge 1 cut158 = cut159 := by checked_cut_rfl
private noncomputable def cut160 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut159)
private theorem step160 : Cursor.resume source client charge 1 cut159 = cut160 := by checked_cut_rfl
private noncomputable def cut161 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut160)
private theorem step161 : Cursor.resume source client charge 1 cut160 = cut161 := by checked_cut_rfl
private theorem actual_paid : cut161.1 = 159 := by checked_cut_rfl
private theorem actual_done : (match cut161.2 with | .done _ => true | _ => false) = true := by checked_cut_rfl

private theorem at0 : run 0 = cut0 := by checked_cut_rfl

private theorem extend_cut (fuel : Nat) (before after : Saved)
    (earlier : run fuel = before) (next : Cursor.resume source client charge 1 before = after) :
    run (fuel + 1) = after := by
  have split : run (fuel + 1) = Cursor.resume source client charge 1 (run fuel) :=
    Cursor.advance_add source client charge fuel 1 packet
  exact split.trans ((congrArg (fun saved => Cursor.resume source client charge 1 saved) earlier).trans next)

private theorem at1 : run 1 = cut1 := extend_cut 0 cut0 cut1 at0 step1
private theorem at2 : run 2 = cut2 := extend_cut 1 cut1 cut2 at1 step2
private theorem at3 : run 3 = cut3 := extend_cut 2 cut2 cut3 at2 step3
private theorem at4 : run 4 = cut4 := extend_cut 3 cut3 cut4 at3 step4
private theorem at5 : run 5 = cut5 := extend_cut 4 cut4 cut5 at4 step5
private theorem at6 : run 6 = cut6 := extend_cut 5 cut5 cut6 at5 step6
private theorem at7 : run 7 = cut7 := extend_cut 6 cut6 cut7 at6 step7
private theorem at8 : run 8 = cut8 := extend_cut 7 cut7 cut8 at7 step8
private theorem at9 : run 9 = cut9 := extend_cut 8 cut8 cut9 at8 step9
private theorem at10 : run 10 = cut10 := extend_cut 9 cut9 cut10 at9 step10
private theorem at11 : run 11 = cut11 := extend_cut 10 cut10 cut11 at10 step11
private theorem at12 : run 12 = cut12 := extend_cut 11 cut11 cut12 at11 step12
private theorem at13 : run 13 = cut13 := extend_cut 12 cut12 cut13 at12 step13
private theorem at14 : run 14 = cut14 := extend_cut 13 cut13 cut14 at13 step14
private theorem at15 : run 15 = cut15 := extend_cut 14 cut14 cut15 at14 step15
private theorem at16 : run 16 = cut16 := extend_cut 15 cut15 cut16 at15 step16
private theorem at17 : run 17 = cut17 := extend_cut 16 cut16 cut17 at16 step17
private theorem at18 : run 18 = cut18 := extend_cut 17 cut17 cut18 at17 step18
private theorem at19 : run 19 = cut19 := extend_cut 18 cut18 cut19 at18 step19
private theorem at20 : run 20 = cut20 := extend_cut 19 cut19 cut20 at19 step20
private theorem at21 : run 21 = cut21 := extend_cut 20 cut20 cut21 at20 step21
private theorem at22 : run 22 = cut22 := extend_cut 21 cut21 cut22 at21 step22
private theorem at23 : run 23 = cut23 := extend_cut 22 cut22 cut23 at22 step23
private theorem at24 : run 24 = cut24 := extend_cut 23 cut23 cut24 at23 step24
private theorem at25 : run 25 = cut25 := extend_cut 24 cut24 cut25 at24 step25
private theorem at26 : run 26 = cut26 := extend_cut 25 cut25 cut26 at25 step26
private theorem at27 : run 27 = cut27 := extend_cut 26 cut26 cut27 at26 step27
private theorem at28 : run 28 = cut28 := extend_cut 27 cut27 cut28 at27 step28
private theorem at29 : run 29 = cut29 := extend_cut 28 cut28 cut29 at28 step29
private theorem at30 : run 30 = cut30 := extend_cut 29 cut29 cut30 at29 step30
private theorem at31 : run 31 = cut31 := extend_cut 30 cut30 cut31 at30 step31
private theorem at32 : run 32 = cut32 := extend_cut 31 cut31 cut32 at31 step32
private theorem at33 : run 33 = cut33 := extend_cut 32 cut32 cut33 at32 step33
private theorem at34 : run 34 = cut34 := extend_cut 33 cut33 cut34 at33 step34
private theorem at35 : run 35 = cut35 := extend_cut 34 cut34 cut35 at34 step35
private theorem at36 : run 36 = cut36 := extend_cut 35 cut35 cut36 at35 step36
private theorem at37 : run 37 = cut37 := extend_cut 36 cut36 cut37 at36 step37
private theorem at38 : run 38 = cut38 := extend_cut 37 cut37 cut38 at37 step38
private theorem at39 : run 39 = cut39 := extend_cut 38 cut38 cut39 at38 step39
private theorem at40 : run 40 = cut40 := extend_cut 39 cut39 cut40 at39 step40
private theorem at41 : run 41 = cut41 := extend_cut 40 cut40 cut41 at40 step41
private theorem at42 : run 42 = cut42 := extend_cut 41 cut41 cut42 at41 step42
private theorem at43 : run 43 = cut43 := extend_cut 42 cut42 cut43 at42 step43
private theorem at44 : run 44 = cut44 := extend_cut 43 cut43 cut44 at43 step44
private theorem at45 : run 45 = cut45 := extend_cut 44 cut44 cut45 at44 step45
private theorem at46 : run 46 = cut46 := extend_cut 45 cut45 cut46 at45 step46
private theorem at47 : run 47 = cut47 := extend_cut 46 cut46 cut47 at46 step47
private theorem at48 : run 48 = cut48 := extend_cut 47 cut47 cut48 at47 step48
private theorem at49 : run 49 = cut49 := extend_cut 48 cut48 cut49 at48 step49
private theorem at50 : run 50 = cut50 := extend_cut 49 cut49 cut50 at49 step50
private theorem at51 : run 51 = cut51 := extend_cut 50 cut50 cut51 at50 step51
private theorem at52 : run 52 = cut52 := extend_cut 51 cut51 cut52 at51 step52
private theorem at53 : run 53 = cut53 := extend_cut 52 cut52 cut53 at52 step53
private theorem at54 : run 54 = cut54 := extend_cut 53 cut53 cut54 at53 step54
private theorem at55 : run 55 = cut55 := extend_cut 54 cut54 cut55 at54 step55
private theorem at56 : run 56 = cut56 := extend_cut 55 cut55 cut56 at55 step56
private theorem at57 : run 57 = cut57 := extend_cut 56 cut56 cut57 at56 step57
private theorem at58 : run 58 = cut58 := extend_cut 57 cut57 cut58 at57 step58
private theorem at59 : run 59 = cut59 := extend_cut 58 cut58 cut59 at58 step59
private theorem at60 : run 60 = cut60 := extend_cut 59 cut59 cut60 at59 step60
private theorem at61 : run 61 = cut61 := extend_cut 60 cut60 cut61 at60 step61
private theorem at62 : run 62 = cut62 := extend_cut 61 cut61 cut62 at61 step62
private theorem at63 : run 63 = cut63 := extend_cut 62 cut62 cut63 at62 step63
private theorem at64 : run 64 = cut64 := extend_cut 63 cut63 cut64 at63 step64
private theorem at65 : run 65 = cut65 := extend_cut 64 cut64 cut65 at64 step65
private theorem at66 : run 66 = cut66 := extend_cut 65 cut65 cut66 at65 step66
private theorem at67 : run 67 = cut67 := extend_cut 66 cut66 cut67 at66 step67
private theorem at68 : run 68 = cut68 := extend_cut 67 cut67 cut68 at67 step68
private theorem at69 : run 69 = cut69 := extend_cut 68 cut68 cut69 at68 step69
private theorem at70 : run 70 = cut70 := extend_cut 69 cut69 cut70 at69 step70
private theorem at71 : run 71 = cut71 := extend_cut 70 cut70 cut71 at70 step71
private theorem at72 : run 72 = cut72 := extend_cut 71 cut71 cut72 at71 step72
private theorem at73 : run 73 = cut73 := extend_cut 72 cut72 cut73 at72 step73
private theorem at74 : run 74 = cut74 := extend_cut 73 cut73 cut74 at73 step74
private theorem at75 : run 75 = cut75 := extend_cut 74 cut74 cut75 at74 step75
private theorem at76 : run 76 = cut76 := extend_cut 75 cut75 cut76 at75 step76
private theorem at77 : run 77 = cut77 := extend_cut 76 cut76 cut77 at76 step77
private theorem at78 : run 78 = cut78 := extend_cut 77 cut77 cut78 at77 step78
private theorem at79 : run 79 = cut79 := extend_cut 78 cut78 cut79 at78 step79
private theorem at80 : run 80 = cut80 := extend_cut 79 cut79 cut80 at79 step80
private theorem at81 : run 81 = cut81 := extend_cut 80 cut80 cut81 at80 step81
private theorem at82 : run 82 = cut82 := extend_cut 81 cut81 cut82 at81 step82
private theorem at83 : run 83 = cut83 := extend_cut 82 cut82 cut83 at82 step83
private theorem at84 : run 84 = cut84 := extend_cut 83 cut83 cut84 at83 step84
private theorem at85 : run 85 = cut85 := extend_cut 84 cut84 cut85 at84 step85
private theorem at86 : run 86 = cut86 := extend_cut 85 cut85 cut86 at85 step86
private theorem at87 : run 87 = cut87 := extend_cut 86 cut86 cut87 at86 step87
private theorem at88 : run 88 = cut88 := extend_cut 87 cut87 cut88 at87 step88
private theorem at89 : run 89 = cut89 := extend_cut 88 cut88 cut89 at88 step89
private theorem at90 : run 90 = cut90 := extend_cut 89 cut89 cut90 at89 step90
private theorem at91 : run 91 = cut91 := extend_cut 90 cut90 cut91 at90 step91
private theorem at92 : run 92 = cut92 := extend_cut 91 cut91 cut92 at91 step92
private theorem at93 : run 93 = cut93 := extend_cut 92 cut92 cut93 at92 step93
private theorem at94 : run 94 = cut94 := extend_cut 93 cut93 cut94 at93 step94
private theorem at95 : run 95 = cut95 := extend_cut 94 cut94 cut95 at94 step95
private theorem at96 : run 96 = cut96 := extend_cut 95 cut95 cut96 at95 step96
private theorem at97 : run 97 = cut97 := extend_cut 96 cut96 cut97 at96 step97
private theorem at98 : run 98 = cut98 := extend_cut 97 cut97 cut98 at97 step98
private theorem at99 : run 99 = cut99 := extend_cut 98 cut98 cut99 at98 step99
private theorem at100 : run 100 = cut100 := extend_cut 99 cut99 cut100 at99 step100
private theorem at101 : run 101 = cut101 := extend_cut 100 cut100 cut101 at100 step101
private theorem at102 : run 102 = cut102 := extend_cut 101 cut101 cut102 at101 step102
private theorem at103 : run 103 = cut103 := extend_cut 102 cut102 cut103 at102 step103
private theorem at104 : run 104 = cut104 := extend_cut 103 cut103 cut104 at103 step104
private theorem at105 : run 105 = cut105 := extend_cut 104 cut104 cut105 at104 step105
private theorem at106 : run 106 = cut106 := extend_cut 105 cut105 cut106 at105 step106
private theorem at107 : run 107 = cut107 := extend_cut 106 cut106 cut107 at106 step107
private theorem at108 : run 108 = cut108 := extend_cut 107 cut107 cut108 at107 step108
private theorem at109 : run 109 = cut109 := extend_cut 108 cut108 cut109 at108 step109
private theorem at110 : run 110 = cut110 := extend_cut 109 cut109 cut110 at109 step110
private theorem at111 : run 111 = cut111 := extend_cut 110 cut110 cut111 at110 step111
private theorem at112 : run 112 = cut112 := extend_cut 111 cut111 cut112 at111 step112
private theorem at113 : run 113 = cut113 := extend_cut 112 cut112 cut113 at112 step113
private theorem at114 : run 114 = cut114 := extend_cut 113 cut113 cut114 at113 step114
private theorem at115 : run 115 = cut115 := extend_cut 114 cut114 cut115 at114 step115
private theorem at116 : run 116 = cut116 := extend_cut 115 cut115 cut116 at115 step116
private theorem at117 : run 117 = cut117 := extend_cut 116 cut116 cut117 at116 step117
private theorem at118 : run 118 = cut118 := extend_cut 117 cut117 cut118 at117 step118
private theorem at119 : run 119 = cut119 := extend_cut 118 cut118 cut119 at118 step119
private theorem at120 : run 120 = cut120 := extend_cut 119 cut119 cut120 at119 step120
private theorem at121 : run 121 = cut121 := extend_cut 120 cut120 cut121 at120 step121
private theorem at122 : run 122 = cut122 := extend_cut 121 cut121 cut122 at121 step122
private theorem at123 : run 123 = cut123 := extend_cut 122 cut122 cut123 at122 step123
private theorem at124 : run 124 = cut124 := extend_cut 123 cut123 cut124 at123 step124
private theorem at125 : run 125 = cut125 := extend_cut 124 cut124 cut125 at124 step125
private theorem at126 : run 126 = cut126 := extend_cut 125 cut125 cut126 at125 step126
private theorem at127 : run 127 = cut127 := extend_cut 126 cut126 cut127 at126 step127
private theorem at128 : run 128 = cut128 := extend_cut 127 cut127 cut128 at127 step128
private theorem at129 : run 129 = cut129 := extend_cut 128 cut128 cut129 at128 step129
private theorem at130 : run 130 = cut130 := extend_cut 129 cut129 cut130 at129 step130
private theorem at131 : run 131 = cut131 := extend_cut 130 cut130 cut131 at130 step131
private theorem at132 : run 132 = cut132 := extend_cut 131 cut131 cut132 at131 step132
private theorem at133 : run 133 = cut133 := extend_cut 132 cut132 cut133 at132 step133
private theorem at134 : run 134 = cut134 := extend_cut 133 cut133 cut134 at133 step134
private theorem at135 : run 135 = cut135 := extend_cut 134 cut134 cut135 at134 step135
private theorem at136 : run 136 = cut136 := extend_cut 135 cut135 cut136 at135 step136
private theorem at137 : run 137 = cut137 := extend_cut 136 cut136 cut137 at136 step137
private theorem at138 : run 138 = cut138 := extend_cut 137 cut137 cut138 at137 step138
private theorem at139 : run 139 = cut139 := extend_cut 138 cut138 cut139 at138 step139
private theorem at140 : run 140 = cut140 := extend_cut 139 cut139 cut140 at139 step140
private theorem at141 : run 141 = cut141 := extend_cut 140 cut140 cut141 at140 step141
private theorem at142 : run 142 = cut142 := extend_cut 141 cut141 cut142 at141 step142
private theorem at143 : run 143 = cut143 := extend_cut 142 cut142 cut143 at142 step143
private theorem at144 : run 144 = cut144 := extend_cut 143 cut143 cut144 at143 step144
private theorem at145 : run 145 = cut145 := extend_cut 144 cut144 cut145 at144 step145
private theorem at146 : run 146 = cut146 := extend_cut 145 cut145 cut146 at145 step146
private theorem at147 : run 147 = cut147 := extend_cut 146 cut146 cut147 at146 step147
private theorem at148 : run 148 = cut148 := extend_cut 147 cut147 cut148 at147 step148
private theorem at149 : run 149 = cut149 := extend_cut 148 cut148 cut149 at148 step149
private theorem at150 : run 150 = cut150 := extend_cut 149 cut149 cut150 at149 step150
private theorem at151 : run 151 = cut151 := extend_cut 150 cut150 cut151 at150 step151
private theorem at152 : run 152 = cut152 := extend_cut 151 cut151 cut152 at151 step152
private theorem at153 : run 153 = cut153 := extend_cut 152 cut152 cut153 at152 step153
private theorem at154 : run 154 = cut154 := extend_cut 153 cut153 cut154 at153 step154
private theorem at155 : run 155 = cut155 := extend_cut 154 cut154 cut155 at154 step155
private theorem at156 : run 156 = cut156 := extend_cut 155 cut155 cut156 at155 step156
private theorem at157 : run 157 = cut157 := extend_cut 156 cut156 cut157 at156 step157
private theorem at158 : run 158 = cut158 := extend_cut 157 cut157 cut158 at157 step158
private theorem at159 : run 159 = cut159 := extend_cut 158 cut158 cut159 at158 step159
private theorem at160 : run 160 = cut160 := extend_cut 159 cut159 cut160 at159 step160
private theorem at161 : run 161 = cut161 := extend_cut 160 cut160 cut161 at160 step161

private theorem done_resume (fuel : Nat) : Cursor.resume source client charge fuel cut161 = cut161 := by
  checked_cut_rfl

private theorem whole_at17 : run 17 = cut17 := at17
private theorem whole_at161 : run 161 = cut161 := at161
private theorem at_zero : run 0 = cut0 := at0

private theorem whole : run 400 = cut161 := by
  have split : run 400 = Cursor.resume source client charge 239 (run 161) :=
    Cursor.advance_add source client charge 161 239 packet
  exact split.trans ((congrArg (fun saved => Cursor.resume source client charge 239 saved) at161).trans (done_resume 239))

local notation "Read" => PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice 407
local notation "Observe" => sourceView annotation number revocationWorlds required needed act reader notice 407

private theorem fold_step {Result : Type} [Monoid Result] (value : View → Result)
    {fuel : Nat} {before after : Saved} {head tail total : Result}
    (step : Cursor.resume source client charge 1 before = after)
    (one : Read value 1 before = head) (rest : Read value fuel after = tail)
    (product : head * tail = total) : Read value (1 + fuel) before = total :=
  (PassiveReader.readSuffix_add annotation number revocationWorlds required needed act reader notice
    407 value 1 fuel before).trans
      ((congrArg₂ (fun left right : Result => left * right) one
        ((congrArg (Read value fuel) step).trans rest)).trans product)

private noncomputable def view0 : View := normalized_cursor_cut% (Observe cut0.2)
private theorem view_eq0 : Observe cut0.2 = view0 := by checked_cut_rfl
private theorem read_one0 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut0 = value (Observe cut0.2) := by
  change value (Observe cut0.2) * 1 = value (Observe cut0.2)
  exact mul_one _
private theorem one0 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut0 = value view0 :=
  (read_one0 value).trans (congrArg value view_eq0)
private noncomputable def view1 : View := normalized_cursor_cut% (Observe cut1.2)
private theorem view_eq1 : Observe cut1.2 = view1 := by checked_cut_rfl
private theorem read_one1 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut1 = value (Observe cut1.2) := by
  change value (Observe cut1.2) * 1 = value (Observe cut1.2)
  exact mul_one _
private theorem one1 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut1 = value view1 :=
  (read_one1 value).trans (congrArg value view_eq1)
private noncomputable def view2 : View := normalized_cursor_cut% (Observe cut2.2)
private theorem view_eq2 : Observe cut2.2 = view2 := by checked_cut_rfl
private theorem read_one2 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut2 = value (Observe cut2.2) := by
  change value (Observe cut2.2) * 1 = value (Observe cut2.2)
  exact mul_one _
private theorem one2 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut2 = value view2 :=
  (read_one2 value).trans (congrArg value view_eq2)
private noncomputable def view3 : View := normalized_cursor_cut% (Observe cut3.2)
private theorem view_eq3 : Observe cut3.2 = view3 := by checked_cut_rfl
private theorem read_one3 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut3 = value (Observe cut3.2) := by
  change value (Observe cut3.2) * 1 = value (Observe cut3.2)
  exact mul_one _
private theorem one3 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut3 = value view3 :=
  (read_one3 value).trans (congrArg value view_eq3)
private noncomputable def view4 : View := normalized_cursor_cut% (Observe cut4.2)
private theorem view_eq4 : Observe cut4.2 = view4 := by checked_cut_rfl
private theorem read_one4 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut4 = value (Observe cut4.2) := by
  change value (Observe cut4.2) * 1 = value (Observe cut4.2)
  exact mul_one _
private theorem one4 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut4 = value view4 :=
  (read_one4 value).trans (congrArg value view_eq4)
private noncomputable def view5 : View := normalized_cursor_cut% (Observe cut5.2)
private theorem view_eq5 : Observe cut5.2 = view5 := by checked_cut_rfl
private theorem read_one5 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut5 = value (Observe cut5.2) := by
  change value (Observe cut5.2) * 1 = value (Observe cut5.2)
  exact mul_one _
private theorem one5 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut5 = value view5 :=
  (read_one5 value).trans (congrArg value view_eq5)
private noncomputable def view6 : View := normalized_cursor_cut% (Observe cut6.2)
private theorem view_eq6 : Observe cut6.2 = view6 := by checked_cut_rfl
private theorem read_one6 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut6 = value (Observe cut6.2) := by
  change value (Observe cut6.2) * 1 = value (Observe cut6.2)
  exact mul_one _
private theorem one6 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut6 = value view6 :=
  (read_one6 value).trans (congrArg value view_eq6)
private noncomputable def view7 : View := normalized_cursor_cut% (Observe cut7.2)
private theorem view_eq7 : Observe cut7.2 = view7 := by checked_cut_rfl
private theorem read_one7 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut7 = value (Observe cut7.2) := by
  change value (Observe cut7.2) * 1 = value (Observe cut7.2)
  exact mul_one _
private theorem one7 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut7 = value view7 :=
  (read_one7 value).trans (congrArg value view_eq7)
private noncomputable def view8 : View := normalized_cursor_cut% (Observe cut8.2)
private theorem view_eq8 : Observe cut8.2 = view8 := by checked_cut_rfl
private theorem read_one8 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut8 = value (Observe cut8.2) := by
  change value (Observe cut8.2) * 1 = value (Observe cut8.2)
  exact mul_one _
private theorem one8 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut8 = value view8 :=
  (read_one8 value).trans (congrArg value view_eq8)
private noncomputable def view9 : View := normalized_cursor_cut% (Observe cut9.2)
private theorem view_eq9 : Observe cut9.2 = view9 := by checked_cut_rfl
private theorem read_one9 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut9 = value (Observe cut9.2) := by
  change value (Observe cut9.2) * 1 = value (Observe cut9.2)
  exact mul_one _
private theorem one9 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut9 = value view9 :=
  (read_one9 value).trans (congrArg value view_eq9)
private noncomputable def view10 : View := normalized_cursor_cut% (Observe cut10.2)
private theorem view_eq10 : Observe cut10.2 = view10 := by checked_cut_rfl
private theorem read_one10 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut10 = value (Observe cut10.2) := by
  change value (Observe cut10.2) * 1 = value (Observe cut10.2)
  exact mul_one _
private theorem one10 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut10 = value view10 :=
  (read_one10 value).trans (congrArg value view_eq10)
private noncomputable def view11 : View := normalized_cursor_cut% (Observe cut11.2)
private theorem view_eq11 : Observe cut11.2 = view11 := by checked_cut_rfl
private theorem read_one11 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut11 = value (Observe cut11.2) := by
  change value (Observe cut11.2) * 1 = value (Observe cut11.2)
  exact mul_one _
private theorem one11 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut11 = value view11 :=
  (read_one11 value).trans (congrArg value view_eq11)
private noncomputable def view12 : View := normalized_cursor_cut% (Observe cut12.2)
private theorem view_eq12 : Observe cut12.2 = view12 := by checked_cut_rfl
private theorem read_one12 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut12 = value (Observe cut12.2) := by
  change value (Observe cut12.2) * 1 = value (Observe cut12.2)
  exact mul_one _
private theorem one12 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut12 = value view12 :=
  (read_one12 value).trans (congrArg value view_eq12)
private noncomputable def view13 : View := normalized_cursor_cut% (Observe cut13.2)
private theorem view_eq13 : Observe cut13.2 = view13 := by checked_cut_rfl
private theorem read_one13 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut13 = value (Observe cut13.2) := by
  change value (Observe cut13.2) * 1 = value (Observe cut13.2)
  exact mul_one _
private theorem one13 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut13 = value view13 :=
  (read_one13 value).trans (congrArg value view_eq13)
private noncomputable def view14 : View := normalized_cursor_cut% (Observe cut14.2)
private theorem view_eq14 : Observe cut14.2 = view14 := by checked_cut_rfl
private theorem read_one14 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut14 = value (Observe cut14.2) := by
  change value (Observe cut14.2) * 1 = value (Observe cut14.2)
  exact mul_one _
private theorem one14 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut14 = value view14 :=
  (read_one14 value).trans (congrArg value view_eq14)
private noncomputable def view15 : View := normalized_cursor_cut% (Observe cut15.2)
private theorem view_eq15 : Observe cut15.2 = view15 := by checked_cut_rfl
private theorem read_one15 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut15 = value (Observe cut15.2) := by
  change value (Observe cut15.2) * 1 = value (Observe cut15.2)
  exact mul_one _
private theorem one15 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut15 = value view15 :=
  (read_one15 value).trans (congrArg value view_eq15)
private noncomputable def view16 : View := normalized_cursor_cut% (Observe cut16.2)
private theorem view_eq16 : Observe cut16.2 = view16 := by checked_cut_rfl
private theorem read_one16 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut16 = value (Observe cut16.2) := by
  change value (Observe cut16.2) * 1 = value (Observe cut16.2)
  exact mul_one _
private theorem one16 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut16 = value view16 :=
  (read_one16 value).trans (congrArg value view_eq16)
private noncomputable def view17 : View := normalized_cursor_cut% (Observe cut17.2)
private theorem view_eq17 : Observe cut17.2 = view17 := by checked_cut_rfl
private theorem read_one17 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut17 = value (Observe cut17.2) := by
  change value (Observe cut17.2) * 1 = value (Observe cut17.2)
  exact mul_one _
private theorem one17 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut17 = value view17 :=
  (read_one17 value).trans (congrArg value view_eq17)
private noncomputable def view18 : View := normalized_cursor_cut% (Observe cut18.2)
private theorem view_eq18 : Observe cut18.2 = view18 := by checked_cut_rfl
private theorem read_one18 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut18 = value (Observe cut18.2) := by
  change value (Observe cut18.2) * 1 = value (Observe cut18.2)
  exact mul_one _
private theorem one18 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut18 = value view18 :=
  (read_one18 value).trans (congrArg value view_eq18)
private noncomputable def view19 : View := normalized_cursor_cut% (Observe cut19.2)
private theorem view_eq19 : Observe cut19.2 = view19 := by checked_cut_rfl
private theorem read_one19 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut19 = value (Observe cut19.2) := by
  change value (Observe cut19.2) * 1 = value (Observe cut19.2)
  exact mul_one _
private theorem one19 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut19 = value view19 :=
  (read_one19 value).trans (congrArg value view_eq19)
private noncomputable def view20 : View := normalized_cursor_cut% (Observe cut20.2)
private theorem view_eq20 : Observe cut20.2 = view20 := by checked_cut_rfl
private theorem read_one20 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut20 = value (Observe cut20.2) := by
  change value (Observe cut20.2) * 1 = value (Observe cut20.2)
  exact mul_one _
private theorem one20 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut20 = value view20 :=
  (read_one20 value).trans (congrArg value view_eq20)
private noncomputable def view21 : View := normalized_cursor_cut% (Observe cut21.2)
private theorem view_eq21 : Observe cut21.2 = view21 := by checked_cut_rfl
private theorem read_one21 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut21 = value (Observe cut21.2) := by
  change value (Observe cut21.2) * 1 = value (Observe cut21.2)
  exact mul_one _
private theorem one21 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut21 = value view21 :=
  (read_one21 value).trans (congrArg value view_eq21)
private noncomputable def view22 : View := normalized_cursor_cut% (Observe cut22.2)
private theorem view_eq22 : Observe cut22.2 = view22 := by checked_cut_rfl
private theorem read_one22 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut22 = value (Observe cut22.2) := by
  change value (Observe cut22.2) * 1 = value (Observe cut22.2)
  exact mul_one _
private theorem one22 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut22 = value view22 :=
  (read_one22 value).trans (congrArg value view_eq22)
private noncomputable def view23 : View := normalized_cursor_cut% (Observe cut23.2)
private theorem view_eq23 : Observe cut23.2 = view23 := by checked_cut_rfl
private theorem read_one23 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut23 = value (Observe cut23.2) := by
  change value (Observe cut23.2) * 1 = value (Observe cut23.2)
  exact mul_one _
private theorem one23 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut23 = value view23 :=
  (read_one23 value).trans (congrArg value view_eq23)
private noncomputable def view24 : View := normalized_cursor_cut% (Observe cut24.2)
private theorem view_eq24 : Observe cut24.2 = view24 := by checked_cut_rfl
private theorem read_one24 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut24 = value (Observe cut24.2) := by
  change value (Observe cut24.2) * 1 = value (Observe cut24.2)
  exact mul_one _
private theorem one24 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut24 = value view24 :=
  (read_one24 value).trans (congrArg value view_eq24)
private noncomputable def view25 : View := normalized_cursor_cut% (Observe cut25.2)
private theorem view_eq25 : Observe cut25.2 = view25 := by checked_cut_rfl
private theorem read_one25 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut25 = value (Observe cut25.2) := by
  change value (Observe cut25.2) * 1 = value (Observe cut25.2)
  exact mul_one _
private theorem one25 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut25 = value view25 :=
  (read_one25 value).trans (congrArg value view_eq25)
private noncomputable def view26 : View := normalized_cursor_cut% (Observe cut26.2)
private theorem view_eq26 : Observe cut26.2 = view26 := by checked_cut_rfl
private theorem read_one26 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut26 = value (Observe cut26.2) := by
  change value (Observe cut26.2) * 1 = value (Observe cut26.2)
  exact mul_one _
private theorem one26 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut26 = value view26 :=
  (read_one26 value).trans (congrArg value view_eq26)
private noncomputable def view27 : View := normalized_cursor_cut% (Observe cut27.2)
private theorem view_eq27 : Observe cut27.2 = view27 := by checked_cut_rfl
private theorem read_one27 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut27 = value (Observe cut27.2) := by
  change value (Observe cut27.2) * 1 = value (Observe cut27.2)
  exact mul_one _
private theorem one27 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut27 = value view27 :=
  (read_one27 value).trans (congrArg value view_eq27)
private noncomputable def view28 : View := normalized_cursor_cut% (Observe cut28.2)
private theorem view_eq28 : Observe cut28.2 = view28 := by checked_cut_rfl
private theorem read_one28 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut28 = value (Observe cut28.2) := by
  change value (Observe cut28.2) * 1 = value (Observe cut28.2)
  exact mul_one _
private theorem one28 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut28 = value view28 :=
  (read_one28 value).trans (congrArg value view_eq28)
private noncomputable def view29 : View := normalized_cursor_cut% (Observe cut29.2)
private theorem view_eq29 : Observe cut29.2 = view29 := by checked_cut_rfl
private theorem read_one29 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut29 = value (Observe cut29.2) := by
  change value (Observe cut29.2) * 1 = value (Observe cut29.2)
  exact mul_one _
private theorem one29 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut29 = value view29 :=
  (read_one29 value).trans (congrArg value view_eq29)
private noncomputable def view30 : View := normalized_cursor_cut% (Observe cut30.2)
private theorem view_eq30 : Observe cut30.2 = view30 := by checked_cut_rfl
private theorem read_one30 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut30 = value (Observe cut30.2) := by
  change value (Observe cut30.2) * 1 = value (Observe cut30.2)
  exact mul_one _
private theorem one30 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut30 = value view30 :=
  (read_one30 value).trans (congrArg value view_eq30)
private noncomputable def view31 : View := normalized_cursor_cut% (Observe cut31.2)
private theorem view_eq31 : Observe cut31.2 = view31 := by checked_cut_rfl
private theorem read_one31 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut31 = value (Observe cut31.2) := by
  change value (Observe cut31.2) * 1 = value (Observe cut31.2)
  exact mul_one _
private theorem one31 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut31 = value view31 :=
  (read_one31 value).trans (congrArg value view_eq31)
private noncomputable def view32 : View := normalized_cursor_cut% (Observe cut32.2)
private theorem view_eq32 : Observe cut32.2 = view32 := by checked_cut_rfl
private theorem read_one32 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut32 = value (Observe cut32.2) := by
  change value (Observe cut32.2) * 1 = value (Observe cut32.2)
  exact mul_one _
private theorem one32 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut32 = value view32 :=
  (read_one32 value).trans (congrArg value view_eq32)
private noncomputable def view33 : View := normalized_cursor_cut% (Observe cut33.2)
private theorem view_eq33 : Observe cut33.2 = view33 := by checked_cut_rfl
private theorem read_one33 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut33 = value (Observe cut33.2) := by
  change value (Observe cut33.2) * 1 = value (Observe cut33.2)
  exact mul_one _
private theorem one33 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut33 = value view33 :=
  (read_one33 value).trans (congrArg value view_eq33)
private noncomputable def view34 : View := normalized_cursor_cut% (Observe cut34.2)
private theorem view_eq34 : Observe cut34.2 = view34 := by checked_cut_rfl
private theorem read_one34 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut34 = value (Observe cut34.2) := by
  change value (Observe cut34.2) * 1 = value (Observe cut34.2)
  exact mul_one _
private theorem one34 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut34 = value view34 :=
  (read_one34 value).trans (congrArg value view_eq34)
private noncomputable def view35 : View := normalized_cursor_cut% (Observe cut35.2)
private theorem view_eq35 : Observe cut35.2 = view35 := by checked_cut_rfl
private theorem read_one35 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut35 = value (Observe cut35.2) := by
  change value (Observe cut35.2) * 1 = value (Observe cut35.2)
  exact mul_one _
private theorem one35 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut35 = value view35 :=
  (read_one35 value).trans (congrArg value view_eq35)
private noncomputable def view36 : View := normalized_cursor_cut% (Observe cut36.2)
private theorem view_eq36 : Observe cut36.2 = view36 := by checked_cut_rfl
private theorem read_one36 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut36 = value (Observe cut36.2) := by
  change value (Observe cut36.2) * 1 = value (Observe cut36.2)
  exact mul_one _
private theorem one36 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut36 = value view36 :=
  (read_one36 value).trans (congrArg value view_eq36)
private noncomputable def view37 : View := normalized_cursor_cut% (Observe cut37.2)
private theorem view_eq37 : Observe cut37.2 = view37 := by checked_cut_rfl
private theorem read_one37 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut37 = value (Observe cut37.2) := by
  change value (Observe cut37.2) * 1 = value (Observe cut37.2)
  exact mul_one _
private theorem one37 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut37 = value view37 :=
  (read_one37 value).trans (congrArg value view_eq37)
private noncomputable def view38 : View := normalized_cursor_cut% (Observe cut38.2)
private theorem view_eq38 : Observe cut38.2 = view38 := by checked_cut_rfl
private theorem read_one38 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut38 = value (Observe cut38.2) := by
  change value (Observe cut38.2) * 1 = value (Observe cut38.2)
  exact mul_one _
private theorem one38 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut38 = value view38 :=
  (read_one38 value).trans (congrArg value view_eq38)
private noncomputable def view39 : View := normalized_cursor_cut% (Observe cut39.2)
private theorem view_eq39 : Observe cut39.2 = view39 := by checked_cut_rfl
private theorem read_one39 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut39 = value (Observe cut39.2) := by
  change value (Observe cut39.2) * 1 = value (Observe cut39.2)
  exact mul_one _
private theorem one39 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut39 = value view39 :=
  (read_one39 value).trans (congrArg value view_eq39)
private noncomputable def view40 : View := normalized_cursor_cut% (Observe cut40.2)
private theorem view_eq40 : Observe cut40.2 = view40 := by checked_cut_rfl
private theorem read_one40 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut40 = value (Observe cut40.2) := by
  change value (Observe cut40.2) * 1 = value (Observe cut40.2)
  exact mul_one _
private theorem one40 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut40 = value view40 :=
  (read_one40 value).trans (congrArg value view_eq40)
private noncomputable def view41 : View := normalized_cursor_cut% (Observe cut41.2)
private theorem view_eq41 : Observe cut41.2 = view41 := by checked_cut_rfl
private theorem read_one41 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut41 = value (Observe cut41.2) := by
  change value (Observe cut41.2) * 1 = value (Observe cut41.2)
  exact mul_one _
private theorem one41 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut41 = value view41 :=
  (read_one41 value).trans (congrArg value view_eq41)
private noncomputable def view42 : View := normalized_cursor_cut% (Observe cut42.2)
private theorem view_eq42 : Observe cut42.2 = view42 := by checked_cut_rfl
private theorem read_one42 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut42 = value (Observe cut42.2) := by
  change value (Observe cut42.2) * 1 = value (Observe cut42.2)
  exact mul_one _
private theorem one42 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut42 = value view42 :=
  (read_one42 value).trans (congrArg value view_eq42)
private noncomputable def view43 : View := normalized_cursor_cut% (Observe cut43.2)
private theorem view_eq43 : Observe cut43.2 = view43 := by checked_cut_rfl
private theorem read_one43 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut43 = value (Observe cut43.2) := by
  change value (Observe cut43.2) * 1 = value (Observe cut43.2)
  exact mul_one _
private theorem one43 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut43 = value view43 :=
  (read_one43 value).trans (congrArg value view_eq43)
private noncomputable def view44 : View := normalized_cursor_cut% (Observe cut44.2)
private theorem view_eq44 : Observe cut44.2 = view44 := by checked_cut_rfl
private theorem read_one44 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut44 = value (Observe cut44.2) := by
  change value (Observe cut44.2) * 1 = value (Observe cut44.2)
  exact mul_one _
private theorem one44 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut44 = value view44 :=
  (read_one44 value).trans (congrArg value view_eq44)
private noncomputable def view45 : View := normalized_cursor_cut% (Observe cut45.2)
private theorem view_eq45 : Observe cut45.2 = view45 := by checked_cut_rfl
private theorem read_one45 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut45 = value (Observe cut45.2) := by
  change value (Observe cut45.2) * 1 = value (Observe cut45.2)
  exact mul_one _
private theorem one45 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut45 = value view45 :=
  (read_one45 value).trans (congrArg value view_eq45)
private noncomputable def view46 : View := normalized_cursor_cut% (Observe cut46.2)
private theorem view_eq46 : Observe cut46.2 = view46 := by checked_cut_rfl
private theorem read_one46 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut46 = value (Observe cut46.2) := by
  change value (Observe cut46.2) * 1 = value (Observe cut46.2)
  exact mul_one _
private theorem one46 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut46 = value view46 :=
  (read_one46 value).trans (congrArg value view_eq46)
private noncomputable def view47 : View := normalized_cursor_cut% (Observe cut47.2)
private theorem view_eq47 : Observe cut47.2 = view47 := by checked_cut_rfl
private theorem read_one47 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut47 = value (Observe cut47.2) := by
  change value (Observe cut47.2) * 1 = value (Observe cut47.2)
  exact mul_one _
private theorem one47 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut47 = value view47 :=
  (read_one47 value).trans (congrArg value view_eq47)
private noncomputable def view48 : View := normalized_cursor_cut% (Observe cut48.2)
private theorem view_eq48 : Observe cut48.2 = view48 := by checked_cut_rfl
private theorem read_one48 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut48 = value (Observe cut48.2) := by
  change value (Observe cut48.2) * 1 = value (Observe cut48.2)
  exact mul_one _
private theorem one48 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut48 = value view48 :=
  (read_one48 value).trans (congrArg value view_eq48)
private noncomputable def view49 : View := normalized_cursor_cut% (Observe cut49.2)
private theorem view_eq49 : Observe cut49.2 = view49 := by checked_cut_rfl
private theorem read_one49 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut49 = value (Observe cut49.2) := by
  change value (Observe cut49.2) * 1 = value (Observe cut49.2)
  exact mul_one _
private theorem one49 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut49 = value view49 :=
  (read_one49 value).trans (congrArg value view_eq49)
private noncomputable def view50 : View := normalized_cursor_cut% (Observe cut50.2)
private theorem view_eq50 : Observe cut50.2 = view50 := by checked_cut_rfl
private theorem read_one50 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut50 = value (Observe cut50.2) := by
  change value (Observe cut50.2) * 1 = value (Observe cut50.2)
  exact mul_one _
private theorem one50 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut50 = value view50 :=
  (read_one50 value).trans (congrArg value view_eq50)
private noncomputable def view51 : View := normalized_cursor_cut% (Observe cut51.2)
private theorem view_eq51 : Observe cut51.2 = view51 := by checked_cut_rfl
private theorem read_one51 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut51 = value (Observe cut51.2) := by
  change value (Observe cut51.2) * 1 = value (Observe cut51.2)
  exact mul_one _
private theorem one51 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut51 = value view51 :=
  (read_one51 value).trans (congrArg value view_eq51)
private noncomputable def view52 : View := normalized_cursor_cut% (Observe cut52.2)
private theorem view_eq52 : Observe cut52.2 = view52 := by checked_cut_rfl
private theorem read_one52 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut52 = value (Observe cut52.2) := by
  change value (Observe cut52.2) * 1 = value (Observe cut52.2)
  exact mul_one _
private theorem one52 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut52 = value view52 :=
  (read_one52 value).trans (congrArg value view_eq52)
private noncomputable def view53 : View := normalized_cursor_cut% (Observe cut53.2)
private theorem view_eq53 : Observe cut53.2 = view53 := by checked_cut_rfl
private theorem read_one53 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut53 = value (Observe cut53.2) := by
  change value (Observe cut53.2) * 1 = value (Observe cut53.2)
  exact mul_one _
private theorem one53 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut53 = value view53 :=
  (read_one53 value).trans (congrArg value view_eq53)
private noncomputable def view54 : View := normalized_cursor_cut% (Observe cut54.2)
private theorem view_eq54 : Observe cut54.2 = view54 := by checked_cut_rfl
private theorem read_one54 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut54 = value (Observe cut54.2) := by
  change value (Observe cut54.2) * 1 = value (Observe cut54.2)
  exact mul_one _
private theorem one54 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut54 = value view54 :=
  (read_one54 value).trans (congrArg value view_eq54)
private noncomputable def view55 : View := normalized_cursor_cut% (Observe cut55.2)
private theorem view_eq55 : Observe cut55.2 = view55 := by checked_cut_rfl
private theorem read_one55 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut55 = value (Observe cut55.2) := by
  change value (Observe cut55.2) * 1 = value (Observe cut55.2)
  exact mul_one _
private theorem one55 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut55 = value view55 :=
  (read_one55 value).trans (congrArg value view_eq55)
private noncomputable def view56 : View := normalized_cursor_cut% (Observe cut56.2)
private theorem view_eq56 : Observe cut56.2 = view56 := by checked_cut_rfl
private theorem read_one56 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut56 = value (Observe cut56.2) := by
  change value (Observe cut56.2) * 1 = value (Observe cut56.2)
  exact mul_one _
private theorem one56 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut56 = value view56 :=
  (read_one56 value).trans (congrArg value view_eq56)
private noncomputable def view57 : View := normalized_cursor_cut% (Observe cut57.2)
private theorem view_eq57 : Observe cut57.2 = view57 := by checked_cut_rfl
private theorem read_one57 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut57 = value (Observe cut57.2) := by
  change value (Observe cut57.2) * 1 = value (Observe cut57.2)
  exact mul_one _
private theorem one57 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut57 = value view57 :=
  (read_one57 value).trans (congrArg value view_eq57)
private noncomputable def view58 : View := normalized_cursor_cut% (Observe cut58.2)
private theorem view_eq58 : Observe cut58.2 = view58 := by checked_cut_rfl
private theorem read_one58 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut58 = value (Observe cut58.2) := by
  change value (Observe cut58.2) * 1 = value (Observe cut58.2)
  exact mul_one _
private theorem one58 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut58 = value view58 :=
  (read_one58 value).trans (congrArg value view_eq58)
private noncomputable def view59 : View := normalized_cursor_cut% (Observe cut59.2)
private theorem view_eq59 : Observe cut59.2 = view59 := by checked_cut_rfl
private theorem read_one59 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut59 = value (Observe cut59.2) := by
  change value (Observe cut59.2) * 1 = value (Observe cut59.2)
  exact mul_one _
private theorem one59 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut59 = value view59 :=
  (read_one59 value).trans (congrArg value view_eq59)
private noncomputable def view60 : View := normalized_cursor_cut% (Observe cut60.2)
private theorem view_eq60 : Observe cut60.2 = view60 := by checked_cut_rfl
private theorem read_one60 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut60 = value (Observe cut60.2) := by
  change value (Observe cut60.2) * 1 = value (Observe cut60.2)
  exact mul_one _
private theorem one60 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut60 = value view60 :=
  (read_one60 value).trans (congrArg value view_eq60)
private noncomputable def view61 : View := normalized_cursor_cut% (Observe cut61.2)
private theorem view_eq61 : Observe cut61.2 = view61 := by checked_cut_rfl
private theorem read_one61 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut61 = value (Observe cut61.2) := by
  change value (Observe cut61.2) * 1 = value (Observe cut61.2)
  exact mul_one _
private theorem one61 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut61 = value view61 :=
  (read_one61 value).trans (congrArg value view_eq61)
private noncomputable def view62 : View := normalized_cursor_cut% (Observe cut62.2)
private theorem view_eq62 : Observe cut62.2 = view62 := by checked_cut_rfl
private theorem read_one62 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut62 = value (Observe cut62.2) := by
  change value (Observe cut62.2) * 1 = value (Observe cut62.2)
  exact mul_one _
private theorem one62 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut62 = value view62 :=
  (read_one62 value).trans (congrArg value view_eq62)
private noncomputable def view63 : View := normalized_cursor_cut% (Observe cut63.2)
private theorem view_eq63 : Observe cut63.2 = view63 := by checked_cut_rfl
private theorem read_one63 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut63 = value (Observe cut63.2) := by
  change value (Observe cut63.2) * 1 = value (Observe cut63.2)
  exact mul_one _
private theorem one63 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut63 = value view63 :=
  (read_one63 value).trans (congrArg value view_eq63)
private noncomputable def view64 : View := normalized_cursor_cut% (Observe cut64.2)
private theorem view_eq64 : Observe cut64.2 = view64 := by checked_cut_rfl
private theorem read_one64 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut64 = value (Observe cut64.2) := by
  change value (Observe cut64.2) * 1 = value (Observe cut64.2)
  exact mul_one _
private theorem one64 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut64 = value view64 :=
  (read_one64 value).trans (congrArg value view_eq64)
private noncomputable def view65 : View := normalized_cursor_cut% (Observe cut65.2)
private theorem view_eq65 : Observe cut65.2 = view65 := by checked_cut_rfl
private theorem read_one65 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut65 = value (Observe cut65.2) := by
  change value (Observe cut65.2) * 1 = value (Observe cut65.2)
  exact mul_one _
private theorem one65 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut65 = value view65 :=
  (read_one65 value).trans (congrArg value view_eq65)
private noncomputable def view66 : View := normalized_cursor_cut% (Observe cut66.2)
private theorem view_eq66 : Observe cut66.2 = view66 := by checked_cut_rfl
private theorem read_one66 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut66 = value (Observe cut66.2) := by
  change value (Observe cut66.2) * 1 = value (Observe cut66.2)
  exact mul_one _
private theorem one66 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut66 = value view66 :=
  (read_one66 value).trans (congrArg value view_eq66)
private noncomputable def view67 : View := normalized_cursor_cut% (Observe cut67.2)
private theorem view_eq67 : Observe cut67.2 = view67 := by checked_cut_rfl
private theorem read_one67 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut67 = value (Observe cut67.2) := by
  change value (Observe cut67.2) * 1 = value (Observe cut67.2)
  exact mul_one _
private theorem one67 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut67 = value view67 :=
  (read_one67 value).trans (congrArg value view_eq67)
private noncomputable def view68 : View := normalized_cursor_cut% (Observe cut68.2)
private theorem view_eq68 : Observe cut68.2 = view68 := by checked_cut_rfl
private theorem read_one68 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut68 = value (Observe cut68.2) := by
  change value (Observe cut68.2) * 1 = value (Observe cut68.2)
  exact mul_one _
private theorem one68 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut68 = value view68 :=
  (read_one68 value).trans (congrArg value view_eq68)
private noncomputable def view69 : View := normalized_cursor_cut% (Observe cut69.2)
private theorem view_eq69 : Observe cut69.2 = view69 := by checked_cut_rfl
private theorem read_one69 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut69 = value (Observe cut69.2) := by
  change value (Observe cut69.2) * 1 = value (Observe cut69.2)
  exact mul_one _
private theorem one69 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut69 = value view69 :=
  (read_one69 value).trans (congrArg value view_eq69)
private noncomputable def view70 : View := normalized_cursor_cut% (Observe cut70.2)
private theorem view_eq70 : Observe cut70.2 = view70 := by checked_cut_rfl
private theorem read_one70 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut70 = value (Observe cut70.2) := by
  change value (Observe cut70.2) * 1 = value (Observe cut70.2)
  exact mul_one _
private theorem one70 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut70 = value view70 :=
  (read_one70 value).trans (congrArg value view_eq70)
private noncomputable def view71 : View := normalized_cursor_cut% (Observe cut71.2)
private theorem view_eq71 : Observe cut71.2 = view71 := by checked_cut_rfl
private theorem read_one71 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut71 = value (Observe cut71.2) := by
  change value (Observe cut71.2) * 1 = value (Observe cut71.2)
  exact mul_one _
private theorem one71 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut71 = value view71 :=
  (read_one71 value).trans (congrArg value view_eq71)
private noncomputable def view72 : View := normalized_cursor_cut% (Observe cut72.2)
private theorem view_eq72 : Observe cut72.2 = view72 := by checked_cut_rfl
private theorem read_one72 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut72 = value (Observe cut72.2) := by
  change value (Observe cut72.2) * 1 = value (Observe cut72.2)
  exact mul_one _
private theorem one72 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut72 = value view72 :=
  (read_one72 value).trans (congrArg value view_eq72)
private noncomputable def view73 : View := normalized_cursor_cut% (Observe cut73.2)
private theorem view_eq73 : Observe cut73.2 = view73 := by checked_cut_rfl
private theorem read_one73 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut73 = value (Observe cut73.2) := by
  change value (Observe cut73.2) * 1 = value (Observe cut73.2)
  exact mul_one _
private theorem one73 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut73 = value view73 :=
  (read_one73 value).trans (congrArg value view_eq73)
private noncomputable def view74 : View := normalized_cursor_cut% (Observe cut74.2)
private theorem view_eq74 : Observe cut74.2 = view74 := by checked_cut_rfl
private theorem read_one74 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut74 = value (Observe cut74.2) := by
  change value (Observe cut74.2) * 1 = value (Observe cut74.2)
  exact mul_one _
private theorem one74 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut74 = value view74 :=
  (read_one74 value).trans (congrArg value view_eq74)
private noncomputable def view75 : View := normalized_cursor_cut% (Observe cut75.2)
private theorem view_eq75 : Observe cut75.2 = view75 := by checked_cut_rfl
private theorem read_one75 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut75 = value (Observe cut75.2) := by
  change value (Observe cut75.2) * 1 = value (Observe cut75.2)
  exact mul_one _
private theorem one75 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut75 = value view75 :=
  (read_one75 value).trans (congrArg value view_eq75)
private noncomputable def view76 : View := normalized_cursor_cut% (Observe cut76.2)
private theorem view_eq76 : Observe cut76.2 = view76 := by checked_cut_rfl
private theorem read_one76 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut76 = value (Observe cut76.2) := by
  change value (Observe cut76.2) * 1 = value (Observe cut76.2)
  exact mul_one _
private theorem one76 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut76 = value view76 :=
  (read_one76 value).trans (congrArg value view_eq76)
private noncomputable def view77 : View := normalized_cursor_cut% (Observe cut77.2)
private theorem view_eq77 : Observe cut77.2 = view77 := by checked_cut_rfl
private theorem read_one77 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut77 = value (Observe cut77.2) := by
  change value (Observe cut77.2) * 1 = value (Observe cut77.2)
  exact mul_one _
private theorem one77 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut77 = value view77 :=
  (read_one77 value).trans (congrArg value view_eq77)
private noncomputable def view78 : View := normalized_cursor_cut% (Observe cut78.2)
private theorem view_eq78 : Observe cut78.2 = view78 := by checked_cut_rfl
private theorem read_one78 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut78 = value (Observe cut78.2) := by
  change value (Observe cut78.2) * 1 = value (Observe cut78.2)
  exact mul_one _
private theorem one78 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut78 = value view78 :=
  (read_one78 value).trans (congrArg value view_eq78)
private noncomputable def view79 : View := normalized_cursor_cut% (Observe cut79.2)
private theorem view_eq79 : Observe cut79.2 = view79 := by checked_cut_rfl
private theorem read_one79 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut79 = value (Observe cut79.2) := by
  change value (Observe cut79.2) * 1 = value (Observe cut79.2)
  exact mul_one _
private theorem one79 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut79 = value view79 :=
  (read_one79 value).trans (congrArg value view_eq79)
private noncomputable def view80 : View := normalized_cursor_cut% (Observe cut80.2)
private theorem view_eq80 : Observe cut80.2 = view80 := by checked_cut_rfl
private theorem read_one80 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut80 = value (Observe cut80.2) := by
  change value (Observe cut80.2) * 1 = value (Observe cut80.2)
  exact mul_one _
private theorem one80 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut80 = value view80 :=
  (read_one80 value).trans (congrArg value view_eq80)
private noncomputable def view81 : View := normalized_cursor_cut% (Observe cut81.2)
private theorem view_eq81 : Observe cut81.2 = view81 := by checked_cut_rfl
private theorem read_one81 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut81 = value (Observe cut81.2) := by
  change value (Observe cut81.2) * 1 = value (Observe cut81.2)
  exact mul_one _
private theorem one81 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut81 = value view81 :=
  (read_one81 value).trans (congrArg value view_eq81)
private noncomputable def view82 : View := normalized_cursor_cut% (Observe cut82.2)
private theorem view_eq82 : Observe cut82.2 = view82 := by checked_cut_rfl
private theorem read_one82 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut82 = value (Observe cut82.2) := by
  change value (Observe cut82.2) * 1 = value (Observe cut82.2)
  exact mul_one _
private theorem one82 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut82 = value view82 :=
  (read_one82 value).trans (congrArg value view_eq82)
private noncomputable def view83 : View := normalized_cursor_cut% (Observe cut83.2)
private theorem view_eq83 : Observe cut83.2 = view83 := by checked_cut_rfl
private theorem read_one83 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut83 = value (Observe cut83.2) := by
  change value (Observe cut83.2) * 1 = value (Observe cut83.2)
  exact mul_one _
private theorem one83 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut83 = value view83 :=
  (read_one83 value).trans (congrArg value view_eq83)
private noncomputable def view84 : View := normalized_cursor_cut% (Observe cut84.2)
private theorem view_eq84 : Observe cut84.2 = view84 := by checked_cut_rfl
private theorem read_one84 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut84 = value (Observe cut84.2) := by
  change value (Observe cut84.2) * 1 = value (Observe cut84.2)
  exact mul_one _
private theorem one84 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut84 = value view84 :=
  (read_one84 value).trans (congrArg value view_eq84)
private noncomputable def view85 : View := normalized_cursor_cut% (Observe cut85.2)
private theorem view_eq85 : Observe cut85.2 = view85 := by checked_cut_rfl
private theorem read_one85 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut85 = value (Observe cut85.2) := by
  change value (Observe cut85.2) * 1 = value (Observe cut85.2)
  exact mul_one _
private theorem one85 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut85 = value view85 :=
  (read_one85 value).trans (congrArg value view_eq85)
private noncomputable def view86 : View := normalized_cursor_cut% (Observe cut86.2)
private theorem view_eq86 : Observe cut86.2 = view86 := by checked_cut_rfl
private theorem read_one86 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut86 = value (Observe cut86.2) := by
  change value (Observe cut86.2) * 1 = value (Observe cut86.2)
  exact mul_one _
private theorem one86 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut86 = value view86 :=
  (read_one86 value).trans (congrArg value view_eq86)
private noncomputable def view87 : View := normalized_cursor_cut% (Observe cut87.2)
private theorem view_eq87 : Observe cut87.2 = view87 := by checked_cut_rfl
private theorem read_one87 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut87 = value (Observe cut87.2) := by
  change value (Observe cut87.2) * 1 = value (Observe cut87.2)
  exact mul_one _
private theorem one87 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut87 = value view87 :=
  (read_one87 value).trans (congrArg value view_eq87)
private noncomputable def view88 : View := normalized_cursor_cut% (Observe cut88.2)
private theorem view_eq88 : Observe cut88.2 = view88 := by checked_cut_rfl
private theorem read_one88 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut88 = value (Observe cut88.2) := by
  change value (Observe cut88.2) * 1 = value (Observe cut88.2)
  exact mul_one _
private theorem one88 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut88 = value view88 :=
  (read_one88 value).trans (congrArg value view_eq88)
private noncomputable def view89 : View := normalized_cursor_cut% (Observe cut89.2)
private theorem view_eq89 : Observe cut89.2 = view89 := by checked_cut_rfl
private theorem read_one89 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut89 = value (Observe cut89.2) := by
  change value (Observe cut89.2) * 1 = value (Observe cut89.2)
  exact mul_one _
private theorem one89 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut89 = value view89 :=
  (read_one89 value).trans (congrArg value view_eq89)
private noncomputable def view90 : View := normalized_cursor_cut% (Observe cut90.2)
private theorem view_eq90 : Observe cut90.2 = view90 := by checked_cut_rfl
private theorem read_one90 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut90 = value (Observe cut90.2) := by
  change value (Observe cut90.2) * 1 = value (Observe cut90.2)
  exact mul_one _
private theorem one90 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut90 = value view90 :=
  (read_one90 value).trans (congrArg value view_eq90)
private noncomputable def view91 : View := normalized_cursor_cut% (Observe cut91.2)
private theorem view_eq91 : Observe cut91.2 = view91 := by checked_cut_rfl
private theorem read_one91 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut91 = value (Observe cut91.2) := by
  change value (Observe cut91.2) * 1 = value (Observe cut91.2)
  exact mul_one _
private theorem one91 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut91 = value view91 :=
  (read_one91 value).trans (congrArg value view_eq91)
private noncomputable def view92 : View := normalized_cursor_cut% (Observe cut92.2)
private theorem view_eq92 : Observe cut92.2 = view92 := by checked_cut_rfl
private theorem read_one92 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut92 = value (Observe cut92.2) := by
  change value (Observe cut92.2) * 1 = value (Observe cut92.2)
  exact mul_one _
private theorem one92 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut92 = value view92 :=
  (read_one92 value).trans (congrArg value view_eq92)
private noncomputable def view93 : View := normalized_cursor_cut% (Observe cut93.2)
private theorem view_eq93 : Observe cut93.2 = view93 := by checked_cut_rfl
private theorem read_one93 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut93 = value (Observe cut93.2) := by
  change value (Observe cut93.2) * 1 = value (Observe cut93.2)
  exact mul_one _
private theorem one93 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut93 = value view93 :=
  (read_one93 value).trans (congrArg value view_eq93)
private noncomputable def view94 : View := normalized_cursor_cut% (Observe cut94.2)
private theorem view_eq94 : Observe cut94.2 = view94 := by checked_cut_rfl
private theorem read_one94 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut94 = value (Observe cut94.2) := by
  change value (Observe cut94.2) * 1 = value (Observe cut94.2)
  exact mul_one _
private theorem one94 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut94 = value view94 :=
  (read_one94 value).trans (congrArg value view_eq94)
private noncomputable def view95 : View := normalized_cursor_cut% (Observe cut95.2)
private theorem view_eq95 : Observe cut95.2 = view95 := by checked_cut_rfl
private theorem read_one95 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut95 = value (Observe cut95.2) := by
  change value (Observe cut95.2) * 1 = value (Observe cut95.2)
  exact mul_one _
private theorem one95 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut95 = value view95 :=
  (read_one95 value).trans (congrArg value view_eq95)
private noncomputable def view96 : View := normalized_cursor_cut% (Observe cut96.2)
private theorem view_eq96 : Observe cut96.2 = view96 := by checked_cut_rfl
private theorem read_one96 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut96 = value (Observe cut96.2) := by
  change value (Observe cut96.2) * 1 = value (Observe cut96.2)
  exact mul_one _
private theorem one96 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut96 = value view96 :=
  (read_one96 value).trans (congrArg value view_eq96)
private noncomputable def view97 : View := normalized_cursor_cut% (Observe cut97.2)
private theorem view_eq97 : Observe cut97.2 = view97 := by checked_cut_rfl
private theorem read_one97 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut97 = value (Observe cut97.2) := by
  change value (Observe cut97.2) * 1 = value (Observe cut97.2)
  exact mul_one _
private theorem one97 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut97 = value view97 :=
  (read_one97 value).trans (congrArg value view_eq97)
private noncomputable def view98 : View := normalized_cursor_cut% (Observe cut98.2)
private theorem view_eq98 : Observe cut98.2 = view98 := by checked_cut_rfl
private theorem read_one98 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut98 = value (Observe cut98.2) := by
  change value (Observe cut98.2) * 1 = value (Observe cut98.2)
  exact mul_one _
private theorem one98 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut98 = value view98 :=
  (read_one98 value).trans (congrArg value view_eq98)
private noncomputable def view99 : View := normalized_cursor_cut% (Observe cut99.2)
private theorem view_eq99 : Observe cut99.2 = view99 := by checked_cut_rfl
private theorem read_one99 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut99 = value (Observe cut99.2) := by
  change value (Observe cut99.2) * 1 = value (Observe cut99.2)
  exact mul_one _
private theorem one99 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut99 = value view99 :=
  (read_one99 value).trans (congrArg value view_eq99)
private noncomputable def view100 : View := normalized_cursor_cut% (Observe cut100.2)
private theorem view_eq100 : Observe cut100.2 = view100 := by checked_cut_rfl
private theorem read_one100 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut100 = value (Observe cut100.2) := by
  change value (Observe cut100.2) * 1 = value (Observe cut100.2)
  exact mul_one _
private theorem one100 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut100 = value view100 :=
  (read_one100 value).trans (congrArg value view_eq100)
private noncomputable def view101 : View := normalized_cursor_cut% (Observe cut101.2)
private theorem view_eq101 : Observe cut101.2 = view101 := by checked_cut_rfl
private theorem read_one101 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut101 = value (Observe cut101.2) := by
  change value (Observe cut101.2) * 1 = value (Observe cut101.2)
  exact mul_one _
private theorem one101 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut101 = value view101 :=
  (read_one101 value).trans (congrArg value view_eq101)
private noncomputable def view102 : View := normalized_cursor_cut% (Observe cut102.2)
private theorem view_eq102 : Observe cut102.2 = view102 := by checked_cut_rfl
private theorem read_one102 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut102 = value (Observe cut102.2) := by
  change value (Observe cut102.2) * 1 = value (Observe cut102.2)
  exact mul_one _
private theorem one102 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut102 = value view102 :=
  (read_one102 value).trans (congrArg value view_eq102)
private noncomputable def view103 : View := normalized_cursor_cut% (Observe cut103.2)
private theorem view_eq103 : Observe cut103.2 = view103 := by checked_cut_rfl
private theorem read_one103 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut103 = value (Observe cut103.2) := by
  change value (Observe cut103.2) * 1 = value (Observe cut103.2)
  exact mul_one _
private theorem one103 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut103 = value view103 :=
  (read_one103 value).trans (congrArg value view_eq103)
private noncomputable def view104 : View := normalized_cursor_cut% (Observe cut104.2)
private theorem view_eq104 : Observe cut104.2 = view104 := by checked_cut_rfl
private theorem read_one104 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut104 = value (Observe cut104.2) := by
  change value (Observe cut104.2) * 1 = value (Observe cut104.2)
  exact mul_one _
private theorem one104 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut104 = value view104 :=
  (read_one104 value).trans (congrArg value view_eq104)
private noncomputable def view105 : View := normalized_cursor_cut% (Observe cut105.2)
private theorem view_eq105 : Observe cut105.2 = view105 := by checked_cut_rfl
private theorem read_one105 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut105 = value (Observe cut105.2) := by
  change value (Observe cut105.2) * 1 = value (Observe cut105.2)
  exact mul_one _
private theorem one105 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut105 = value view105 :=
  (read_one105 value).trans (congrArg value view_eq105)
private noncomputable def view106 : View := normalized_cursor_cut% (Observe cut106.2)
private theorem view_eq106 : Observe cut106.2 = view106 := by checked_cut_rfl
private theorem read_one106 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut106 = value (Observe cut106.2) := by
  change value (Observe cut106.2) * 1 = value (Observe cut106.2)
  exact mul_one _
private theorem one106 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut106 = value view106 :=
  (read_one106 value).trans (congrArg value view_eq106)
private noncomputable def view107 : View := normalized_cursor_cut% (Observe cut107.2)
private theorem view_eq107 : Observe cut107.2 = view107 := by checked_cut_rfl
private theorem read_one107 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut107 = value (Observe cut107.2) := by
  change value (Observe cut107.2) * 1 = value (Observe cut107.2)
  exact mul_one _
private theorem one107 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut107 = value view107 :=
  (read_one107 value).trans (congrArg value view_eq107)
private noncomputable def view108 : View := normalized_cursor_cut% (Observe cut108.2)
private theorem view_eq108 : Observe cut108.2 = view108 := by checked_cut_rfl
private theorem read_one108 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut108 = value (Observe cut108.2) := by
  change value (Observe cut108.2) * 1 = value (Observe cut108.2)
  exact mul_one _
private theorem one108 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut108 = value view108 :=
  (read_one108 value).trans (congrArg value view_eq108)
private noncomputable def view109 : View := normalized_cursor_cut% (Observe cut109.2)
private theorem view_eq109 : Observe cut109.2 = view109 := by checked_cut_rfl
private theorem read_one109 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut109 = value (Observe cut109.2) := by
  change value (Observe cut109.2) * 1 = value (Observe cut109.2)
  exact mul_one _
private theorem one109 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut109 = value view109 :=
  (read_one109 value).trans (congrArg value view_eq109)
private noncomputable def view110 : View := normalized_cursor_cut% (Observe cut110.2)
private theorem view_eq110 : Observe cut110.2 = view110 := by checked_cut_rfl
private theorem read_one110 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut110 = value (Observe cut110.2) := by
  change value (Observe cut110.2) * 1 = value (Observe cut110.2)
  exact mul_one _
private theorem one110 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut110 = value view110 :=
  (read_one110 value).trans (congrArg value view_eq110)
private noncomputable def view111 : View := normalized_cursor_cut% (Observe cut111.2)
private theorem view_eq111 : Observe cut111.2 = view111 := by checked_cut_rfl
private theorem read_one111 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut111 = value (Observe cut111.2) := by
  change value (Observe cut111.2) * 1 = value (Observe cut111.2)
  exact mul_one _
private theorem one111 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut111 = value view111 :=
  (read_one111 value).trans (congrArg value view_eq111)
private noncomputable def view112 : View := normalized_cursor_cut% (Observe cut112.2)
private theorem view_eq112 : Observe cut112.2 = view112 := by checked_cut_rfl
private theorem read_one112 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut112 = value (Observe cut112.2) := by
  change value (Observe cut112.2) * 1 = value (Observe cut112.2)
  exact mul_one _
private theorem one112 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut112 = value view112 :=
  (read_one112 value).trans (congrArg value view_eq112)
private noncomputable def view113 : View := normalized_cursor_cut% (Observe cut113.2)
private theorem view_eq113 : Observe cut113.2 = view113 := by checked_cut_rfl
private theorem read_one113 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut113 = value (Observe cut113.2) := by
  change value (Observe cut113.2) * 1 = value (Observe cut113.2)
  exact mul_one _
private theorem one113 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut113 = value view113 :=
  (read_one113 value).trans (congrArg value view_eq113)
private noncomputable def view114 : View := normalized_cursor_cut% (Observe cut114.2)
private theorem view_eq114 : Observe cut114.2 = view114 := by checked_cut_rfl
private theorem read_one114 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut114 = value (Observe cut114.2) := by
  change value (Observe cut114.2) * 1 = value (Observe cut114.2)
  exact mul_one _
private theorem one114 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut114 = value view114 :=
  (read_one114 value).trans (congrArg value view_eq114)
private noncomputable def view115 : View := normalized_cursor_cut% (Observe cut115.2)
private theorem view_eq115 : Observe cut115.2 = view115 := by checked_cut_rfl
private theorem read_one115 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut115 = value (Observe cut115.2) := by
  change value (Observe cut115.2) * 1 = value (Observe cut115.2)
  exact mul_one _
private theorem one115 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut115 = value view115 :=
  (read_one115 value).trans (congrArg value view_eq115)
private noncomputable def view116 : View := normalized_cursor_cut% (Observe cut116.2)
private theorem view_eq116 : Observe cut116.2 = view116 := by checked_cut_rfl
private theorem read_one116 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut116 = value (Observe cut116.2) := by
  change value (Observe cut116.2) * 1 = value (Observe cut116.2)
  exact mul_one _
private theorem one116 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut116 = value view116 :=
  (read_one116 value).trans (congrArg value view_eq116)
private noncomputable def view117 : View := normalized_cursor_cut% (Observe cut117.2)
private theorem view_eq117 : Observe cut117.2 = view117 := by checked_cut_rfl
private theorem read_one117 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut117 = value (Observe cut117.2) := by
  change value (Observe cut117.2) * 1 = value (Observe cut117.2)
  exact mul_one _
private theorem one117 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut117 = value view117 :=
  (read_one117 value).trans (congrArg value view_eq117)
private noncomputable def view118 : View := normalized_cursor_cut% (Observe cut118.2)
private theorem view_eq118 : Observe cut118.2 = view118 := by checked_cut_rfl
private theorem read_one118 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut118 = value (Observe cut118.2) := by
  change value (Observe cut118.2) * 1 = value (Observe cut118.2)
  exact mul_one _
private theorem one118 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut118 = value view118 :=
  (read_one118 value).trans (congrArg value view_eq118)
private noncomputable def view119 : View := normalized_cursor_cut% (Observe cut119.2)
private theorem view_eq119 : Observe cut119.2 = view119 := by checked_cut_rfl
private theorem read_one119 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut119 = value (Observe cut119.2) := by
  change value (Observe cut119.2) * 1 = value (Observe cut119.2)
  exact mul_one _
private theorem one119 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut119 = value view119 :=
  (read_one119 value).trans (congrArg value view_eq119)
private noncomputable def view120 : View := normalized_cursor_cut% (Observe cut120.2)
private theorem view_eq120 : Observe cut120.2 = view120 := by checked_cut_rfl
private theorem read_one120 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut120 = value (Observe cut120.2) := by
  change value (Observe cut120.2) * 1 = value (Observe cut120.2)
  exact mul_one _
private theorem one120 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut120 = value view120 :=
  (read_one120 value).trans (congrArg value view_eq120)
private noncomputable def view121 : View := normalized_cursor_cut% (Observe cut121.2)
private theorem view_eq121 : Observe cut121.2 = view121 := by checked_cut_rfl
private theorem read_one121 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut121 = value (Observe cut121.2) := by
  change value (Observe cut121.2) * 1 = value (Observe cut121.2)
  exact mul_one _
private theorem one121 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut121 = value view121 :=
  (read_one121 value).trans (congrArg value view_eq121)
private noncomputable def view122 : View := normalized_cursor_cut% (Observe cut122.2)
private theorem view_eq122 : Observe cut122.2 = view122 := by checked_cut_rfl
private theorem read_one122 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut122 = value (Observe cut122.2) := by
  change value (Observe cut122.2) * 1 = value (Observe cut122.2)
  exact mul_one _
private theorem one122 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut122 = value view122 :=
  (read_one122 value).trans (congrArg value view_eq122)
private noncomputable def view123 : View := normalized_cursor_cut% (Observe cut123.2)
private theorem view_eq123 : Observe cut123.2 = view123 := by checked_cut_rfl
private theorem read_one123 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut123 = value (Observe cut123.2) := by
  change value (Observe cut123.2) * 1 = value (Observe cut123.2)
  exact mul_one _
private theorem one123 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut123 = value view123 :=
  (read_one123 value).trans (congrArg value view_eq123)
private noncomputable def view124 : View := normalized_cursor_cut% (Observe cut124.2)
private theorem view_eq124 : Observe cut124.2 = view124 := by checked_cut_rfl
private theorem read_one124 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut124 = value (Observe cut124.2) := by
  change value (Observe cut124.2) * 1 = value (Observe cut124.2)
  exact mul_one _
private theorem one124 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut124 = value view124 :=
  (read_one124 value).trans (congrArg value view_eq124)
private noncomputable def view125 : View := normalized_cursor_cut% (Observe cut125.2)
private theorem view_eq125 : Observe cut125.2 = view125 := by checked_cut_rfl
private theorem read_one125 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut125 = value (Observe cut125.2) := by
  change value (Observe cut125.2) * 1 = value (Observe cut125.2)
  exact mul_one _
private theorem one125 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut125 = value view125 :=
  (read_one125 value).trans (congrArg value view_eq125)
private noncomputable def view126 : View := normalized_cursor_cut% (Observe cut126.2)
private theorem view_eq126 : Observe cut126.2 = view126 := by checked_cut_rfl
private theorem read_one126 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut126 = value (Observe cut126.2) := by
  change value (Observe cut126.2) * 1 = value (Observe cut126.2)
  exact mul_one _
private theorem one126 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut126 = value view126 :=
  (read_one126 value).trans (congrArg value view_eq126)
private noncomputable def view127 : View := normalized_cursor_cut% (Observe cut127.2)
private theorem view_eq127 : Observe cut127.2 = view127 := by checked_cut_rfl
private theorem read_one127 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut127 = value (Observe cut127.2) := by
  change value (Observe cut127.2) * 1 = value (Observe cut127.2)
  exact mul_one _
private theorem one127 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut127 = value view127 :=
  (read_one127 value).trans (congrArg value view_eq127)
private noncomputable def view128 : View := normalized_cursor_cut% (Observe cut128.2)
private theorem view_eq128 : Observe cut128.2 = view128 := by checked_cut_rfl
private theorem read_one128 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut128 = value (Observe cut128.2) := by
  change value (Observe cut128.2) * 1 = value (Observe cut128.2)
  exact mul_one _
private theorem one128 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut128 = value view128 :=
  (read_one128 value).trans (congrArg value view_eq128)
private noncomputable def view129 : View := normalized_cursor_cut% (Observe cut129.2)
private theorem view_eq129 : Observe cut129.2 = view129 := by checked_cut_rfl
private theorem read_one129 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut129 = value (Observe cut129.2) := by
  change value (Observe cut129.2) * 1 = value (Observe cut129.2)
  exact mul_one _
private theorem one129 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut129 = value view129 :=
  (read_one129 value).trans (congrArg value view_eq129)
private noncomputable def view130 : View := normalized_cursor_cut% (Observe cut130.2)
private theorem view_eq130 : Observe cut130.2 = view130 := by checked_cut_rfl
private theorem read_one130 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut130 = value (Observe cut130.2) := by
  change value (Observe cut130.2) * 1 = value (Observe cut130.2)
  exact mul_one _
private theorem one130 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut130 = value view130 :=
  (read_one130 value).trans (congrArg value view_eq130)
private noncomputable def view131 : View := normalized_cursor_cut% (Observe cut131.2)
private theorem view_eq131 : Observe cut131.2 = view131 := by checked_cut_rfl
private theorem read_one131 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut131 = value (Observe cut131.2) := by
  change value (Observe cut131.2) * 1 = value (Observe cut131.2)
  exact mul_one _
private theorem one131 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut131 = value view131 :=
  (read_one131 value).trans (congrArg value view_eq131)
private noncomputable def view132 : View := normalized_cursor_cut% (Observe cut132.2)
private theorem view_eq132 : Observe cut132.2 = view132 := by checked_cut_rfl
private theorem read_one132 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut132 = value (Observe cut132.2) := by
  change value (Observe cut132.2) * 1 = value (Observe cut132.2)
  exact mul_one _
private theorem one132 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut132 = value view132 :=
  (read_one132 value).trans (congrArg value view_eq132)
private noncomputable def view133 : View := normalized_cursor_cut% (Observe cut133.2)
private theorem view_eq133 : Observe cut133.2 = view133 := by checked_cut_rfl
private theorem read_one133 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut133 = value (Observe cut133.2) := by
  change value (Observe cut133.2) * 1 = value (Observe cut133.2)
  exact mul_one _
private theorem one133 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut133 = value view133 :=
  (read_one133 value).trans (congrArg value view_eq133)
private noncomputable def view134 : View := normalized_cursor_cut% (Observe cut134.2)
private theorem view_eq134 : Observe cut134.2 = view134 := by checked_cut_rfl
private theorem read_one134 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut134 = value (Observe cut134.2) := by
  change value (Observe cut134.2) * 1 = value (Observe cut134.2)
  exact mul_one _
private theorem one134 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut134 = value view134 :=
  (read_one134 value).trans (congrArg value view_eq134)
private noncomputable def view135 : View := normalized_cursor_cut% (Observe cut135.2)
private theorem view_eq135 : Observe cut135.2 = view135 := by checked_cut_rfl
private theorem read_one135 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut135 = value (Observe cut135.2) := by
  change value (Observe cut135.2) * 1 = value (Observe cut135.2)
  exact mul_one _
private theorem one135 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut135 = value view135 :=
  (read_one135 value).trans (congrArg value view_eq135)
private noncomputable def view136 : View := normalized_cursor_cut% (Observe cut136.2)
private theorem view_eq136 : Observe cut136.2 = view136 := by checked_cut_rfl
private theorem read_one136 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut136 = value (Observe cut136.2) := by
  change value (Observe cut136.2) * 1 = value (Observe cut136.2)
  exact mul_one _
private theorem one136 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut136 = value view136 :=
  (read_one136 value).trans (congrArg value view_eq136)
private noncomputable def view137 : View := normalized_cursor_cut% (Observe cut137.2)
private theorem view_eq137 : Observe cut137.2 = view137 := by checked_cut_rfl
private theorem read_one137 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut137 = value (Observe cut137.2) := by
  change value (Observe cut137.2) * 1 = value (Observe cut137.2)
  exact mul_one _
private theorem one137 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut137 = value view137 :=
  (read_one137 value).trans (congrArg value view_eq137)
private noncomputable def view138 : View := normalized_cursor_cut% (Observe cut138.2)
private theorem view_eq138 : Observe cut138.2 = view138 := by checked_cut_rfl
private theorem read_one138 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut138 = value (Observe cut138.2) := by
  change value (Observe cut138.2) * 1 = value (Observe cut138.2)
  exact mul_one _
private theorem one138 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut138 = value view138 :=
  (read_one138 value).trans (congrArg value view_eq138)
private noncomputable def view139 : View := normalized_cursor_cut% (Observe cut139.2)
private theorem view_eq139 : Observe cut139.2 = view139 := by checked_cut_rfl
private theorem read_one139 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut139 = value (Observe cut139.2) := by
  change value (Observe cut139.2) * 1 = value (Observe cut139.2)
  exact mul_one _
private theorem one139 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut139 = value view139 :=
  (read_one139 value).trans (congrArg value view_eq139)
private noncomputable def view140 : View := normalized_cursor_cut% (Observe cut140.2)
private theorem view_eq140 : Observe cut140.2 = view140 := by checked_cut_rfl
private theorem read_one140 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut140 = value (Observe cut140.2) := by
  change value (Observe cut140.2) * 1 = value (Observe cut140.2)
  exact mul_one _
private theorem one140 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut140 = value view140 :=
  (read_one140 value).trans (congrArg value view_eq140)
private noncomputable def view141 : View := normalized_cursor_cut% (Observe cut141.2)
private theorem view_eq141 : Observe cut141.2 = view141 := by checked_cut_rfl
private theorem read_one141 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut141 = value (Observe cut141.2) := by
  change value (Observe cut141.2) * 1 = value (Observe cut141.2)
  exact mul_one _
private theorem one141 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut141 = value view141 :=
  (read_one141 value).trans (congrArg value view_eq141)
private noncomputable def view142 : View := normalized_cursor_cut% (Observe cut142.2)
private theorem view_eq142 : Observe cut142.2 = view142 := by checked_cut_rfl
private theorem read_one142 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut142 = value (Observe cut142.2) := by
  change value (Observe cut142.2) * 1 = value (Observe cut142.2)
  exact mul_one _
private theorem one142 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut142 = value view142 :=
  (read_one142 value).trans (congrArg value view_eq142)
private noncomputable def view143 : View := normalized_cursor_cut% (Observe cut143.2)
private theorem view_eq143 : Observe cut143.2 = view143 := by checked_cut_rfl
private theorem read_one143 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut143 = value (Observe cut143.2) := by
  change value (Observe cut143.2) * 1 = value (Observe cut143.2)
  exact mul_one _
private theorem one143 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut143 = value view143 :=
  (read_one143 value).trans (congrArg value view_eq143)
private noncomputable def view144 : View := normalized_cursor_cut% (Observe cut144.2)
private theorem view_eq144 : Observe cut144.2 = view144 := by checked_cut_rfl
private theorem read_one144 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut144 = value (Observe cut144.2) := by
  change value (Observe cut144.2) * 1 = value (Observe cut144.2)
  exact mul_one _
private theorem one144 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut144 = value view144 :=
  (read_one144 value).trans (congrArg value view_eq144)
private noncomputable def view145 : View := normalized_cursor_cut% (Observe cut145.2)
private theorem view_eq145 : Observe cut145.2 = view145 := by checked_cut_rfl
private theorem read_one145 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut145 = value (Observe cut145.2) := by
  change value (Observe cut145.2) * 1 = value (Observe cut145.2)
  exact mul_one _
private theorem one145 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut145 = value view145 :=
  (read_one145 value).trans (congrArg value view_eq145)
private noncomputable def view146 : View := normalized_cursor_cut% (Observe cut146.2)
private theorem view_eq146 : Observe cut146.2 = view146 := by checked_cut_rfl
private theorem read_one146 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut146 = value (Observe cut146.2) := by
  change value (Observe cut146.2) * 1 = value (Observe cut146.2)
  exact mul_one _
private theorem one146 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut146 = value view146 :=
  (read_one146 value).trans (congrArg value view_eq146)
private noncomputable def view147 : View := normalized_cursor_cut% (Observe cut147.2)
private theorem view_eq147 : Observe cut147.2 = view147 := by checked_cut_rfl
private theorem read_one147 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut147 = value (Observe cut147.2) := by
  change value (Observe cut147.2) * 1 = value (Observe cut147.2)
  exact mul_one _
private theorem one147 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut147 = value view147 :=
  (read_one147 value).trans (congrArg value view_eq147)
private noncomputable def view148 : View := normalized_cursor_cut% (Observe cut148.2)
private theorem view_eq148 : Observe cut148.2 = view148 := by checked_cut_rfl
private theorem read_one148 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut148 = value (Observe cut148.2) := by
  change value (Observe cut148.2) * 1 = value (Observe cut148.2)
  exact mul_one _
private theorem one148 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut148 = value view148 :=
  (read_one148 value).trans (congrArg value view_eq148)
private noncomputable def view149 : View := normalized_cursor_cut% (Observe cut149.2)
private theorem view_eq149 : Observe cut149.2 = view149 := by checked_cut_rfl
private theorem read_one149 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut149 = value (Observe cut149.2) := by
  change value (Observe cut149.2) * 1 = value (Observe cut149.2)
  exact mul_one _
private theorem one149 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut149 = value view149 :=
  (read_one149 value).trans (congrArg value view_eq149)
private noncomputable def view150 : View := normalized_cursor_cut% (Observe cut150.2)
private theorem view_eq150 : Observe cut150.2 = view150 := by checked_cut_rfl
private theorem read_one150 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut150 = value (Observe cut150.2) := by
  change value (Observe cut150.2) * 1 = value (Observe cut150.2)
  exact mul_one _
private theorem one150 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut150 = value view150 :=
  (read_one150 value).trans (congrArg value view_eq150)
private noncomputable def view151 : View := normalized_cursor_cut% (Observe cut151.2)
private theorem view_eq151 : Observe cut151.2 = view151 := by checked_cut_rfl
private theorem read_one151 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut151 = value (Observe cut151.2) := by
  change value (Observe cut151.2) * 1 = value (Observe cut151.2)
  exact mul_one _
private theorem one151 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut151 = value view151 :=
  (read_one151 value).trans (congrArg value view_eq151)
private noncomputable def view152 : View := normalized_cursor_cut% (Observe cut152.2)
private theorem view_eq152 : Observe cut152.2 = view152 := by checked_cut_rfl
private theorem read_one152 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut152 = value (Observe cut152.2) := by
  change value (Observe cut152.2) * 1 = value (Observe cut152.2)
  exact mul_one _
private theorem one152 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut152 = value view152 :=
  (read_one152 value).trans (congrArg value view_eq152)
private noncomputable def view153 : View := normalized_cursor_cut% (Observe cut153.2)
private theorem view_eq153 : Observe cut153.2 = view153 := by checked_cut_rfl
private theorem read_one153 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut153 = value (Observe cut153.2) := by
  change value (Observe cut153.2) * 1 = value (Observe cut153.2)
  exact mul_one _
private theorem one153 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut153 = value view153 :=
  (read_one153 value).trans (congrArg value view_eq153)
private noncomputable def view154 : View := normalized_cursor_cut% (Observe cut154.2)
private theorem view_eq154 : Observe cut154.2 = view154 := by checked_cut_rfl
private theorem read_one154 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut154 = value (Observe cut154.2) := by
  change value (Observe cut154.2) * 1 = value (Observe cut154.2)
  exact mul_one _
private theorem one154 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut154 = value view154 :=
  (read_one154 value).trans (congrArg value view_eq154)
private noncomputable def view155 : View := normalized_cursor_cut% (Observe cut155.2)
private theorem view_eq155 : Observe cut155.2 = view155 := by checked_cut_rfl
private theorem read_one155 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut155 = value (Observe cut155.2) := by
  change value (Observe cut155.2) * 1 = value (Observe cut155.2)
  exact mul_one _
private theorem one155 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut155 = value view155 :=
  (read_one155 value).trans (congrArg value view_eq155)
private noncomputable def view156 : View := normalized_cursor_cut% (Observe cut156.2)
private theorem view_eq156 : Observe cut156.2 = view156 := by checked_cut_rfl
private theorem read_one156 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut156 = value (Observe cut156.2) := by
  change value (Observe cut156.2) * 1 = value (Observe cut156.2)
  exact mul_one _
private theorem one156 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut156 = value view156 :=
  (read_one156 value).trans (congrArg value view_eq156)
private noncomputable def view157 : View := normalized_cursor_cut% (Observe cut157.2)
private theorem view_eq157 : Observe cut157.2 = view157 := by checked_cut_rfl
private theorem read_one157 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut157 = value (Observe cut157.2) := by
  change value (Observe cut157.2) * 1 = value (Observe cut157.2)
  exact mul_one _
private theorem one157 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut157 = value view157 :=
  (read_one157 value).trans (congrArg value view_eq157)
private noncomputable def view158 : View := normalized_cursor_cut% (Observe cut158.2)
private theorem view_eq158 : Observe cut158.2 = view158 := by checked_cut_rfl
private theorem read_one158 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut158 = value (Observe cut158.2) := by
  change value (Observe cut158.2) * 1 = value (Observe cut158.2)
  exact mul_one _
private theorem one158 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut158 = value view158 :=
  (read_one158 value).trans (congrArg value view_eq158)
private noncomputable def view159 : View := normalized_cursor_cut% (Observe cut159.2)
private theorem view_eq159 : Observe cut159.2 = view159 := by checked_cut_rfl
private theorem read_one159 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut159 = value (Observe cut159.2) := by
  change value (Observe cut159.2) * 1 = value (Observe cut159.2)
  exact mul_one _
private theorem one159 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut159 = value view159 :=
  (read_one159 value).trans (congrArg value view_eq159)
private noncomputable def view160 : View := normalized_cursor_cut% (Observe cut160.2)
private theorem view_eq160 : Observe cut160.2 = view160 := by checked_cut_rfl
private theorem read_one160 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut160 = value (Observe cut160.2) := by
  change value (Observe cut160.2) * 1 = value (Observe cut160.2)
  exact mul_one _
private theorem one160 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut160 = value view160 :=
  (read_one160 value).trans (congrArg value view_eq160)

private noncomputable def tail161 : List View := []
private noncomputable def tail160 : List View := view160 :: tail161
private noncomputable def tail159 : List View := view159 :: tail160
private noncomputable def tail158 : List View := view158 :: tail159
private noncomputable def tail157 : List View := view157 :: tail158
private noncomputable def tail156 : List View := view156 :: tail157
private noncomputable def tail155 : List View := view155 :: tail156
private noncomputable def tail154 : List View := view154 :: tail155
private noncomputable def tail153 : List View := view153 :: tail154
private noncomputable def tail152 : List View := view152 :: tail153
private noncomputable def tail151 : List View := view151 :: tail152
private noncomputable def tail150 : List View := view150 :: tail151
private noncomputable def tail149 : List View := view149 :: tail150
private noncomputable def tail148 : List View := view148 :: tail149
private noncomputable def tail147 : List View := view147 :: tail148
private noncomputable def tail146 : List View := view146 :: tail147
private noncomputable def tail145 : List View := view145 :: tail146
private noncomputable def tail144 : List View := view144 :: tail145
private noncomputable def tail143 : List View := view143 :: tail144
private noncomputable def tail142 : List View := view142 :: tail143
private noncomputable def tail141 : List View := view141 :: tail142
private noncomputable def tail140 : List View := view140 :: tail141
private noncomputable def tail139 : List View := view139 :: tail140
private noncomputable def tail138 : List View := view138 :: tail139
private noncomputable def tail137 : List View := view137 :: tail138
private noncomputable def tail136 : List View := view136 :: tail137
private noncomputable def tail135 : List View := view135 :: tail136
private noncomputable def tail134 : List View := view134 :: tail135
private noncomputable def tail133 : List View := view133 :: tail134
private noncomputable def tail132 : List View := view132 :: tail133
private noncomputable def tail131 : List View := view131 :: tail132
private noncomputable def tail130 : List View := view130 :: tail131
private noncomputable def tail129 : List View := view129 :: tail130
private noncomputable def tail128 : List View := view128 :: tail129
private noncomputable def tail127 : List View := view127 :: tail128
private noncomputable def tail126 : List View := view126 :: tail127
private noncomputable def tail125 : List View := view125 :: tail126
private noncomputable def tail124 : List View := view124 :: tail125
private noncomputable def tail123 : List View := view123 :: tail124
private noncomputable def tail122 : List View := view122 :: tail123
private noncomputable def tail121 : List View := view121 :: tail122
private noncomputable def tail120 : List View := view120 :: tail121
private noncomputable def tail119 : List View := view119 :: tail120
private noncomputable def tail118 : List View := view118 :: tail119
private noncomputable def tail117 : List View := view117 :: tail118
private noncomputable def tail116 : List View := view116 :: tail117
private noncomputable def tail115 : List View := view115 :: tail116
private noncomputable def tail114 : List View := view114 :: tail115
private noncomputable def tail113 : List View := view113 :: tail114
private noncomputable def tail112 : List View := view112 :: tail113
private noncomputable def tail111 : List View := view111 :: tail112
private noncomputable def tail110 : List View := view110 :: tail111
private noncomputable def tail109 : List View := view109 :: tail110
private noncomputable def tail108 : List View := view108 :: tail109
private noncomputable def tail107 : List View := view107 :: tail108
private noncomputable def tail106 : List View := view106 :: tail107
private noncomputable def tail105 : List View := view105 :: tail106
private noncomputable def tail104 : List View := view104 :: tail105
private noncomputable def tail103 : List View := view103 :: tail104
private noncomputable def tail102 : List View := view102 :: tail103
private noncomputable def tail101 : List View := view101 :: tail102
private noncomputable def tail100 : List View := view100 :: tail101
private noncomputable def tail99 : List View := view99 :: tail100
private noncomputable def tail98 : List View := view98 :: tail99
private noncomputable def tail97 : List View := view97 :: tail98
private noncomputable def tail96 : List View := view96 :: tail97
private noncomputable def tail95 : List View := view95 :: tail96
private noncomputable def tail94 : List View := view94 :: tail95
private noncomputable def tail93 : List View := view93 :: tail94
private noncomputable def tail92 : List View := view92 :: tail93
private noncomputable def tail91 : List View := view91 :: tail92
private noncomputable def tail90 : List View := view90 :: tail91
private noncomputable def tail89 : List View := view89 :: tail90
private noncomputable def tail88 : List View := view88 :: tail89
private noncomputable def tail87 : List View := view87 :: tail88
private noncomputable def tail86 : List View := view86 :: tail87
private noncomputable def tail85 : List View := view85 :: tail86
private noncomputable def tail84 : List View := view84 :: tail85
private noncomputable def tail83 : List View := view83 :: tail84
private noncomputable def tail82 : List View := view82 :: tail83
private noncomputable def tail81 : List View := view81 :: tail82
private noncomputable def tail80 : List View := view80 :: tail81
private noncomputable def tail79 : List View := view79 :: tail80
private noncomputable def tail78 : List View := view78 :: tail79
private noncomputable def tail77 : List View := view77 :: tail78
private noncomputable def tail76 : List View := view76 :: tail77
private noncomputable def tail75 : List View := view75 :: tail76
private noncomputable def tail74 : List View := view74 :: tail75
private noncomputable def tail73 : List View := view73 :: tail74
private noncomputable def tail72 : List View := view72 :: tail73
private noncomputable def tail71 : List View := view71 :: tail72
private noncomputable def tail70 : List View := view70 :: tail71
private noncomputable def tail69 : List View := view69 :: tail70
private noncomputable def tail68 : List View := view68 :: tail69
private noncomputable def tail67 : List View := view67 :: tail68
private noncomputable def tail66 : List View := view66 :: tail67
private noncomputable def tail65 : List View := view65 :: tail66
private noncomputable def tail64 : List View := view64 :: tail65
private noncomputable def tail63 : List View := view63 :: tail64
private noncomputable def tail62 : List View := view62 :: tail63
private noncomputable def tail61 : List View := view61 :: tail62
private noncomputable def tail60 : List View := view60 :: tail61
private noncomputable def tail59 : List View := view59 :: tail60
private noncomputable def tail58 : List View := view58 :: tail59
private noncomputable def tail57 : List View := view57 :: tail58
private noncomputable def tail56 : List View := view56 :: tail57
private noncomputable def tail55 : List View := view55 :: tail56
private noncomputable def tail54 : List View := view54 :: tail55
private noncomputable def tail53 : List View := view53 :: tail54
private noncomputable def tail52 : List View := view52 :: tail53
private noncomputable def tail51 : List View := view51 :: tail52
private noncomputable def tail50 : List View := view50 :: tail51
private noncomputable def tail49 : List View := view49 :: tail50
private noncomputable def tail48 : List View := view48 :: tail49
private noncomputable def tail47 : List View := view47 :: tail48
private noncomputable def tail46 : List View := view46 :: tail47
private noncomputable def tail45 : List View := view45 :: tail46
private noncomputable def tail44 : List View := view44 :: tail45
private noncomputable def tail43 : List View := view43 :: tail44
private noncomputable def tail42 : List View := view42 :: tail43
private noncomputable def tail41 : List View := view41 :: tail42
private noncomputable def tail40 : List View := view40 :: tail41
private noncomputable def tail39 : List View := view39 :: tail40
private noncomputable def tail38 : List View := view38 :: tail39
private noncomputable def tail37 : List View := view37 :: tail38
private noncomputable def tail36 : List View := view36 :: tail37
private noncomputable def tail35 : List View := view35 :: tail36
private noncomputable def tail34 : List View := view34 :: tail35
private noncomputable def tail33 : List View := view33 :: tail34
private noncomputable def tail32 : List View := view32 :: tail33
private noncomputable def tail31 : List View := view31 :: tail32
private noncomputable def tail30 : List View := view30 :: tail31
private noncomputable def tail29 : List View := view29 :: tail30
private noncomputable def tail28 : List View := view28 :: tail29
private noncomputable def tail27 : List View := view27 :: tail28
private noncomputable def tail26 : List View := view26 :: tail27
private noncomputable def tail25 : List View := view25 :: tail26
private noncomputable def tail24 : List View := view24 :: tail25
private noncomputable def tail23 : List View := view23 :: tail24
private noncomputable def tail22 : List View := view22 :: tail23
private noncomputable def tail21 : List View := view21 :: tail22
private noncomputable def tail20 : List View := view20 :: tail21
private noncomputable def tail19 : List View := view19 :: tail20
private noncomputable def tail18 : List View := view18 :: tail19
private noncomputable def tail17 : List View := view17 :: tail18
private noncomputable def tail16 : List View := view16 :: tail17
private noncomputable def tail15 : List View := view15 :: tail16
private noncomputable def tail14 : List View := view14 :: tail15
private noncomputable def tail13 : List View := view13 :: tail14
private noncomputable def tail12 : List View := view12 :: tail13
private noncomputable def tail11 : List View := view11 :: tail12
private noncomputable def tail10 : List View := view10 :: tail11
private noncomputable def tail9 : List View := view9 :: tail10
private noncomputable def tail8 : List View := view8 :: tail9
private noncomputable def tail7 : List View := view7 :: tail8
private noncomputable def tail6 : List View := view6 :: tail7
private noncomputable def tail5 : List View := view5 :: tail6
private noncomputable def tail4 : List View := view4 :: tail5
private noncomputable def tail3 : List View := view3 :: tail4
private noncomputable def tail2 : List View := view2 :: tail3
private noncomputable def tail1 : List View := view1 :: tail2
private noncomputable def tail0 : List View := view0 :: tail1

private theorem tail_read161 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 239 cut161 = (tail161.map value).prod := by checked_cut_rfl
private theorem tail_read160 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 240 cut160 = (tail160.map value).prod :=
  fold_step value step161 (one160 value) (tail_read161 value) rfl
private theorem tail_read159 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 241 cut159 = (tail159.map value).prod :=
  fold_step value step160 (one159 value) (tail_read160 value) rfl
private theorem tail_read158 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 242 cut158 = (tail158.map value).prod :=
  fold_step value step159 (one158 value) (tail_read159 value) rfl
private theorem tail_read157 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 243 cut157 = (tail157.map value).prod :=
  fold_step value step158 (one157 value) (tail_read158 value) rfl
private theorem tail_read156 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 244 cut156 = (tail156.map value).prod :=
  fold_step value step157 (one156 value) (tail_read157 value) rfl
private theorem tail_read155 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 245 cut155 = (tail155.map value).prod :=
  fold_step value step156 (one155 value) (tail_read156 value) rfl
private theorem tail_read154 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 246 cut154 = (tail154.map value).prod :=
  fold_step value step155 (one154 value) (tail_read155 value) rfl
private theorem tail_read153 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 247 cut153 = (tail153.map value).prod :=
  fold_step value step154 (one153 value) (tail_read154 value) rfl
private theorem tail_read152 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 248 cut152 = (tail152.map value).prod :=
  fold_step value step153 (one152 value) (tail_read153 value) rfl
private theorem tail_read151 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 249 cut151 = (tail151.map value).prod :=
  fold_step value step152 (one151 value) (tail_read152 value) rfl
private theorem tail_read150 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 250 cut150 = (tail150.map value).prod :=
  fold_step value step151 (one150 value) (tail_read151 value) rfl
private theorem tail_read149 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 251 cut149 = (tail149.map value).prod :=
  fold_step value step150 (one149 value) (tail_read150 value) rfl
private theorem tail_read148 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 252 cut148 = (tail148.map value).prod :=
  fold_step value step149 (one148 value) (tail_read149 value) rfl
private theorem tail_read147 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 253 cut147 = (tail147.map value).prod :=
  fold_step value step148 (one147 value) (tail_read148 value) rfl
private theorem tail_read146 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 254 cut146 = (tail146.map value).prod :=
  fold_step value step147 (one146 value) (tail_read147 value) rfl
private theorem tail_read145 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 255 cut145 = (tail145.map value).prod :=
  fold_step value step146 (one145 value) (tail_read146 value) rfl
private theorem tail_read144 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 256 cut144 = (tail144.map value).prod :=
  fold_step value step145 (one144 value) (tail_read145 value) rfl
private theorem tail_read143 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 257 cut143 = (tail143.map value).prod :=
  fold_step value step144 (one143 value) (tail_read144 value) rfl
private theorem tail_read142 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 258 cut142 = (tail142.map value).prod :=
  fold_step value step143 (one142 value) (tail_read143 value) rfl
private theorem tail_read141 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 259 cut141 = (tail141.map value).prod :=
  fold_step value step142 (one141 value) (tail_read142 value) rfl
private theorem tail_read140 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 260 cut140 = (tail140.map value).prod :=
  fold_step value step141 (one140 value) (tail_read141 value) rfl
private theorem tail_read139 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 261 cut139 = (tail139.map value).prod :=
  fold_step value step140 (one139 value) (tail_read140 value) rfl
private theorem tail_read138 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 262 cut138 = (tail138.map value).prod :=
  fold_step value step139 (one138 value) (tail_read139 value) rfl
private theorem tail_read137 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 263 cut137 = (tail137.map value).prod :=
  fold_step value step138 (one137 value) (tail_read138 value) rfl
private theorem tail_read136 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 264 cut136 = (tail136.map value).prod :=
  fold_step value step137 (one136 value) (tail_read137 value) rfl
private theorem tail_read135 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 265 cut135 = (tail135.map value).prod :=
  fold_step value step136 (one135 value) (tail_read136 value) rfl
private theorem tail_read134 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 266 cut134 = (tail134.map value).prod :=
  fold_step value step135 (one134 value) (tail_read135 value) rfl
private theorem tail_read133 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 267 cut133 = (tail133.map value).prod :=
  fold_step value step134 (one133 value) (tail_read134 value) rfl
private theorem tail_read132 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 268 cut132 = (tail132.map value).prod :=
  fold_step value step133 (one132 value) (tail_read133 value) rfl
private theorem tail_read131 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 269 cut131 = (tail131.map value).prod :=
  fold_step value step132 (one131 value) (tail_read132 value) rfl
private theorem tail_read130 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 270 cut130 = (tail130.map value).prod :=
  fold_step value step131 (one130 value) (tail_read131 value) rfl
private theorem tail_read129 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 271 cut129 = (tail129.map value).prod :=
  fold_step value step130 (one129 value) (tail_read130 value) rfl
private theorem tail_read128 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 272 cut128 = (tail128.map value).prod :=
  fold_step value step129 (one128 value) (tail_read129 value) rfl
private theorem tail_read127 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 273 cut127 = (tail127.map value).prod :=
  fold_step value step128 (one127 value) (tail_read128 value) rfl
private theorem tail_read126 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 274 cut126 = (tail126.map value).prod :=
  fold_step value step127 (one126 value) (tail_read127 value) rfl
private theorem tail_read125 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 275 cut125 = (tail125.map value).prod :=
  fold_step value step126 (one125 value) (tail_read126 value) rfl
private theorem tail_read124 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 276 cut124 = (tail124.map value).prod :=
  fold_step value step125 (one124 value) (tail_read125 value) rfl
private theorem tail_read123 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 277 cut123 = (tail123.map value).prod :=
  fold_step value step124 (one123 value) (tail_read124 value) rfl
private theorem tail_read122 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 278 cut122 = (tail122.map value).prod :=
  fold_step value step123 (one122 value) (tail_read123 value) rfl
private theorem tail_read121 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 279 cut121 = (tail121.map value).prod :=
  fold_step value step122 (one121 value) (tail_read122 value) rfl
private theorem tail_read120 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 280 cut120 = (tail120.map value).prod :=
  fold_step value step121 (one120 value) (tail_read121 value) rfl
private theorem tail_read119 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 281 cut119 = (tail119.map value).prod :=
  fold_step value step120 (one119 value) (tail_read120 value) rfl
private theorem tail_read118 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 282 cut118 = (tail118.map value).prod :=
  fold_step value step119 (one118 value) (tail_read119 value) rfl
private theorem tail_read117 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 283 cut117 = (tail117.map value).prod :=
  fold_step value step118 (one117 value) (tail_read118 value) rfl
private theorem tail_read116 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 284 cut116 = (tail116.map value).prod :=
  fold_step value step117 (one116 value) (tail_read117 value) rfl
private theorem tail_read115 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 285 cut115 = (tail115.map value).prod :=
  fold_step value step116 (one115 value) (tail_read116 value) rfl
private theorem tail_read114 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 286 cut114 = (tail114.map value).prod :=
  fold_step value step115 (one114 value) (tail_read115 value) rfl
private theorem tail_read113 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 287 cut113 = (tail113.map value).prod :=
  fold_step value step114 (one113 value) (tail_read114 value) rfl
private theorem tail_read112 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 288 cut112 = (tail112.map value).prod :=
  fold_step value step113 (one112 value) (tail_read113 value) rfl
private theorem tail_read111 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 289 cut111 = (tail111.map value).prod :=
  fold_step value step112 (one111 value) (tail_read112 value) rfl
private theorem tail_read110 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 290 cut110 = (tail110.map value).prod :=
  fold_step value step111 (one110 value) (tail_read111 value) rfl
private theorem tail_read109 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 291 cut109 = (tail109.map value).prod :=
  fold_step value step110 (one109 value) (tail_read110 value) rfl
private theorem tail_read108 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 292 cut108 = (tail108.map value).prod :=
  fold_step value step109 (one108 value) (tail_read109 value) rfl
private theorem tail_read107 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 293 cut107 = (tail107.map value).prod :=
  fold_step value step108 (one107 value) (tail_read108 value) rfl
private theorem tail_read106 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 294 cut106 = (tail106.map value).prod :=
  fold_step value step107 (one106 value) (tail_read107 value) rfl
private theorem tail_read105 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 295 cut105 = (tail105.map value).prod :=
  fold_step value step106 (one105 value) (tail_read106 value) rfl
private theorem tail_read104 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 296 cut104 = (tail104.map value).prod :=
  fold_step value step105 (one104 value) (tail_read105 value) rfl
private theorem tail_read103 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 297 cut103 = (tail103.map value).prod :=
  fold_step value step104 (one103 value) (tail_read104 value) rfl
private theorem tail_read102 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 298 cut102 = (tail102.map value).prod :=
  fold_step value step103 (one102 value) (tail_read103 value) rfl
private theorem tail_read101 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 299 cut101 = (tail101.map value).prod :=
  fold_step value step102 (one101 value) (tail_read102 value) rfl
private theorem tail_read100 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 300 cut100 = (tail100.map value).prod :=
  fold_step value step101 (one100 value) (tail_read101 value) rfl
private theorem tail_read99 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 301 cut99 = (tail99.map value).prod :=
  fold_step value step100 (one99 value) (tail_read100 value) rfl
private theorem tail_read98 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 302 cut98 = (tail98.map value).prod :=
  fold_step value step99 (one98 value) (tail_read99 value) rfl
private theorem tail_read97 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 303 cut97 = (tail97.map value).prod :=
  fold_step value step98 (one97 value) (tail_read98 value) rfl
private theorem tail_read96 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 304 cut96 = (tail96.map value).prod :=
  fold_step value step97 (one96 value) (tail_read97 value) rfl
private theorem tail_read95 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 305 cut95 = (tail95.map value).prod :=
  fold_step value step96 (one95 value) (tail_read96 value) rfl
private theorem tail_read94 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 306 cut94 = (tail94.map value).prod :=
  fold_step value step95 (one94 value) (tail_read95 value) rfl
private theorem tail_read93 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 307 cut93 = (tail93.map value).prod :=
  fold_step value step94 (one93 value) (tail_read94 value) rfl
private theorem tail_read92 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 308 cut92 = (tail92.map value).prod :=
  fold_step value step93 (one92 value) (tail_read93 value) rfl
private theorem tail_read91 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 309 cut91 = (tail91.map value).prod :=
  fold_step value step92 (one91 value) (tail_read92 value) rfl
private theorem tail_read90 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 310 cut90 = (tail90.map value).prod :=
  fold_step value step91 (one90 value) (tail_read91 value) rfl
private theorem tail_read89 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 311 cut89 = (tail89.map value).prod :=
  fold_step value step90 (one89 value) (tail_read90 value) rfl
private theorem tail_read88 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 312 cut88 = (tail88.map value).prod :=
  fold_step value step89 (one88 value) (tail_read89 value) rfl
private theorem tail_read87 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 313 cut87 = (tail87.map value).prod :=
  fold_step value step88 (one87 value) (tail_read88 value) rfl
private theorem tail_read86 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 314 cut86 = (tail86.map value).prod :=
  fold_step value step87 (one86 value) (tail_read87 value) rfl
private theorem tail_read85 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 315 cut85 = (tail85.map value).prod :=
  fold_step value step86 (one85 value) (tail_read86 value) rfl
private theorem tail_read84 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 316 cut84 = (tail84.map value).prod :=
  fold_step value step85 (one84 value) (tail_read85 value) rfl
private theorem tail_read83 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 317 cut83 = (tail83.map value).prod :=
  fold_step value step84 (one83 value) (tail_read84 value) rfl
private theorem tail_read82 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 318 cut82 = (tail82.map value).prod :=
  fold_step value step83 (one82 value) (tail_read83 value) rfl
private theorem tail_read81 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 319 cut81 = (tail81.map value).prod :=
  fold_step value step82 (one81 value) (tail_read82 value) rfl
private theorem tail_read80 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 320 cut80 = (tail80.map value).prod :=
  fold_step value step81 (one80 value) (tail_read81 value) rfl
private theorem tail_read79 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 321 cut79 = (tail79.map value).prod :=
  fold_step value step80 (one79 value) (tail_read80 value) rfl
private theorem tail_read78 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 322 cut78 = (tail78.map value).prod :=
  fold_step value step79 (one78 value) (tail_read79 value) rfl
private theorem tail_read77 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 323 cut77 = (tail77.map value).prod :=
  fold_step value step78 (one77 value) (tail_read78 value) rfl
private theorem tail_read76 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 324 cut76 = (tail76.map value).prod :=
  fold_step value step77 (one76 value) (tail_read77 value) rfl
private theorem tail_read75 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 325 cut75 = (tail75.map value).prod :=
  fold_step value step76 (one75 value) (tail_read76 value) rfl
private theorem tail_read74 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 326 cut74 = (tail74.map value).prod :=
  fold_step value step75 (one74 value) (tail_read75 value) rfl
private theorem tail_read73 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 327 cut73 = (tail73.map value).prod :=
  fold_step value step74 (one73 value) (tail_read74 value) rfl
private theorem tail_read72 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 328 cut72 = (tail72.map value).prod :=
  fold_step value step73 (one72 value) (tail_read73 value) rfl
private theorem tail_read71 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 329 cut71 = (tail71.map value).prod :=
  fold_step value step72 (one71 value) (tail_read72 value) rfl
private theorem tail_read70 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 330 cut70 = (tail70.map value).prod :=
  fold_step value step71 (one70 value) (tail_read71 value) rfl
private theorem tail_read69 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 331 cut69 = (tail69.map value).prod :=
  fold_step value step70 (one69 value) (tail_read70 value) rfl
private theorem tail_read68 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 332 cut68 = (tail68.map value).prod :=
  fold_step value step69 (one68 value) (tail_read69 value) rfl
private theorem tail_read67 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 333 cut67 = (tail67.map value).prod :=
  fold_step value step68 (one67 value) (tail_read68 value) rfl
private theorem tail_read66 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 334 cut66 = (tail66.map value).prod :=
  fold_step value step67 (one66 value) (tail_read67 value) rfl
private theorem tail_read65 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 335 cut65 = (tail65.map value).prod :=
  fold_step value step66 (one65 value) (tail_read66 value) rfl
private theorem tail_read64 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 336 cut64 = (tail64.map value).prod :=
  fold_step value step65 (one64 value) (tail_read65 value) rfl
private theorem tail_read63 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 337 cut63 = (tail63.map value).prod :=
  fold_step value step64 (one63 value) (tail_read64 value) rfl
private theorem tail_read62 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 338 cut62 = (tail62.map value).prod :=
  fold_step value step63 (one62 value) (tail_read63 value) rfl
private theorem tail_read61 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 339 cut61 = (tail61.map value).prod :=
  fold_step value step62 (one61 value) (tail_read62 value) rfl
private theorem tail_read60 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 340 cut60 = (tail60.map value).prod :=
  fold_step value step61 (one60 value) (tail_read61 value) rfl
private theorem tail_read59 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 341 cut59 = (tail59.map value).prod :=
  fold_step value step60 (one59 value) (tail_read60 value) rfl
private theorem tail_read58 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 342 cut58 = (tail58.map value).prod :=
  fold_step value step59 (one58 value) (tail_read59 value) rfl
private theorem tail_read57 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 343 cut57 = (tail57.map value).prod :=
  fold_step value step58 (one57 value) (tail_read58 value) rfl
private theorem tail_read56 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 344 cut56 = (tail56.map value).prod :=
  fold_step value step57 (one56 value) (tail_read57 value) rfl
private theorem tail_read55 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 345 cut55 = (tail55.map value).prod :=
  fold_step value step56 (one55 value) (tail_read56 value) rfl
private theorem tail_read54 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 346 cut54 = (tail54.map value).prod :=
  fold_step value step55 (one54 value) (tail_read55 value) rfl
private theorem tail_read53 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 347 cut53 = (tail53.map value).prod :=
  fold_step value step54 (one53 value) (tail_read54 value) rfl
private theorem tail_read52 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 348 cut52 = (tail52.map value).prod :=
  fold_step value step53 (one52 value) (tail_read53 value) rfl
private theorem tail_read51 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 349 cut51 = (tail51.map value).prod :=
  fold_step value step52 (one51 value) (tail_read52 value) rfl
private theorem tail_read50 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 350 cut50 = (tail50.map value).prod :=
  fold_step value step51 (one50 value) (tail_read51 value) rfl
private theorem tail_read49 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 351 cut49 = (tail49.map value).prod :=
  fold_step value step50 (one49 value) (tail_read50 value) rfl
private theorem tail_read48 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 352 cut48 = (tail48.map value).prod :=
  fold_step value step49 (one48 value) (tail_read49 value) rfl
private theorem tail_read47 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 353 cut47 = (tail47.map value).prod :=
  fold_step value step48 (one47 value) (tail_read48 value) rfl
private theorem tail_read46 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 354 cut46 = (tail46.map value).prod :=
  fold_step value step47 (one46 value) (tail_read47 value) rfl
private theorem tail_read45 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 355 cut45 = (tail45.map value).prod :=
  fold_step value step46 (one45 value) (tail_read46 value) rfl
private theorem tail_read44 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 356 cut44 = (tail44.map value).prod :=
  fold_step value step45 (one44 value) (tail_read45 value) rfl
private theorem tail_read43 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 357 cut43 = (tail43.map value).prod :=
  fold_step value step44 (one43 value) (tail_read44 value) rfl
private theorem tail_read42 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 358 cut42 = (tail42.map value).prod :=
  fold_step value step43 (one42 value) (tail_read43 value) rfl
private theorem tail_read41 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 359 cut41 = (tail41.map value).prod :=
  fold_step value step42 (one41 value) (tail_read42 value) rfl
private theorem tail_read40 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 360 cut40 = (tail40.map value).prod :=
  fold_step value step41 (one40 value) (tail_read41 value) rfl
private theorem tail_read39 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 361 cut39 = (tail39.map value).prod :=
  fold_step value step40 (one39 value) (tail_read40 value) rfl
private theorem tail_read38 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 362 cut38 = (tail38.map value).prod :=
  fold_step value step39 (one38 value) (tail_read39 value) rfl
private theorem tail_read37 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 363 cut37 = (tail37.map value).prod :=
  fold_step value step38 (one37 value) (tail_read38 value) rfl
private theorem tail_read36 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 364 cut36 = (tail36.map value).prod :=
  fold_step value step37 (one36 value) (tail_read37 value) rfl
private theorem tail_read35 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 365 cut35 = (tail35.map value).prod :=
  fold_step value step36 (one35 value) (tail_read36 value) rfl
private theorem tail_read34 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 366 cut34 = (tail34.map value).prod :=
  fold_step value step35 (one34 value) (tail_read35 value) rfl
private theorem tail_read33 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 367 cut33 = (tail33.map value).prod :=
  fold_step value step34 (one33 value) (tail_read34 value) rfl
private theorem tail_read32 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 368 cut32 = (tail32.map value).prod :=
  fold_step value step33 (one32 value) (tail_read33 value) rfl
private theorem tail_read31 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 369 cut31 = (tail31.map value).prod :=
  fold_step value step32 (one31 value) (tail_read32 value) rfl
private theorem tail_read30 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 370 cut30 = (tail30.map value).prod :=
  fold_step value step31 (one30 value) (tail_read31 value) rfl
private theorem tail_read29 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 371 cut29 = (tail29.map value).prod :=
  fold_step value step30 (one29 value) (tail_read30 value) rfl
private theorem tail_read28 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 372 cut28 = (tail28.map value).prod :=
  fold_step value step29 (one28 value) (tail_read29 value) rfl
private theorem tail_read27 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 373 cut27 = (tail27.map value).prod :=
  fold_step value step28 (one27 value) (tail_read28 value) rfl
private theorem tail_read26 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 374 cut26 = (tail26.map value).prod :=
  fold_step value step27 (one26 value) (tail_read27 value) rfl
private theorem tail_read25 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 375 cut25 = (tail25.map value).prod :=
  fold_step value step26 (one25 value) (tail_read26 value) rfl
private theorem tail_read24 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 376 cut24 = (tail24.map value).prod :=
  fold_step value step25 (one24 value) (tail_read25 value) rfl
private theorem tail_read23 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 377 cut23 = (tail23.map value).prod :=
  fold_step value step24 (one23 value) (tail_read24 value) rfl
private theorem tail_read22 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 378 cut22 = (tail22.map value).prod :=
  fold_step value step23 (one22 value) (tail_read23 value) rfl
private theorem tail_read21 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 379 cut21 = (tail21.map value).prod :=
  fold_step value step22 (one21 value) (tail_read22 value) rfl
private theorem tail_read20 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 380 cut20 = (tail20.map value).prod :=
  fold_step value step21 (one20 value) (tail_read21 value) rfl
private theorem tail_read19 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 381 cut19 = (tail19.map value).prod :=
  fold_step value step20 (one19 value) (tail_read20 value) rfl
private theorem tail_read18 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 382 cut18 = (tail18.map value).prod :=
  fold_step value step19 (one18 value) (tail_read19 value) rfl
private theorem tail_read17 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 383 cut17 = (tail17.map value).prod :=
  fold_step value step18 (one17 value) (tail_read18 value) rfl
private theorem tail_read16 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 384 cut16 = (tail16.map value).prod :=
  fold_step value step17 (one16 value) (tail_read17 value) rfl
private theorem tail_read15 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 385 cut15 = (tail15.map value).prod :=
  fold_step value step16 (one15 value) (tail_read16 value) rfl
private theorem tail_read14 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 386 cut14 = (tail14.map value).prod :=
  fold_step value step15 (one14 value) (tail_read15 value) rfl
private theorem tail_read13 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 387 cut13 = (tail13.map value).prod :=
  fold_step value step14 (one13 value) (tail_read14 value) rfl
private theorem tail_read12 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 388 cut12 = (tail12.map value).prod :=
  fold_step value step13 (one12 value) (tail_read13 value) rfl
private theorem tail_read11 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 389 cut11 = (tail11.map value).prod :=
  fold_step value step12 (one11 value) (tail_read12 value) rfl
private theorem tail_read10 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 390 cut10 = (tail10.map value).prod :=
  fold_step value step11 (one10 value) (tail_read11 value) rfl
private theorem tail_read9 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 391 cut9 = (tail9.map value).prod :=
  fold_step value step10 (one9 value) (tail_read10 value) rfl
private theorem tail_read8 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 392 cut8 = (tail8.map value).prod :=
  fold_step value step9 (one8 value) (tail_read9 value) rfl
private theorem tail_read7 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 393 cut7 = (tail7.map value).prod :=
  fold_step value step8 (one7 value) (tail_read8 value) rfl
private theorem tail_read6 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 394 cut6 = (tail6.map value).prod :=
  fold_step value step7 (one6 value) (tail_read7 value) rfl
private theorem tail_read5 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 395 cut5 = (tail5.map value).prod :=
  fold_step value step6 (one5 value) (tail_read6 value) rfl
private theorem tail_read4 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 396 cut4 = (tail4.map value).prod :=
  fold_step value step5 (one4 value) (tail_read5 value) rfl
private theorem tail_read3 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 397 cut3 = (tail3.map value).prod :=
  fold_step value step4 (one3 value) (tail_read4 value) rfl
private theorem tail_read2 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 398 cut2 = (tail2.map value).prod :=
  fold_step value step3 (one2 value) (tail_read3 value) rfl
private theorem tail_read1 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 399 cut1 = (tail1.map value).prod :=
  fold_step value step2 (one1 value) (tail_read2 value) rfl
private theorem tail_read0 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 400 cut0 = (tail0.map value).prod :=
  fold_step value step1 (one0 value) (tail_read1 value) rfl

private noncomputable def prefix17 : List View := []
private noncomputable def prefix16 : List View := view16 :: prefix17
private noncomputable def prefix15 : List View := view15 :: prefix16
private noncomputable def prefix14 : List View := view14 :: prefix15
private noncomputable def prefix13 : List View := view13 :: prefix14
private noncomputable def prefix12 : List View := view12 :: prefix13
private noncomputable def prefix11 : List View := view11 :: prefix12
private noncomputable def prefix10 : List View := view10 :: prefix11
private noncomputable def prefix9 : List View := view9 :: prefix10
private noncomputable def prefix8 : List View := view8 :: prefix9
private noncomputable def prefix7 : List View := view7 :: prefix8
private noncomputable def prefix6 : List View := view6 :: prefix7
private noncomputable def prefix5 : List View := view5 :: prefix6
private noncomputable def prefix4 : List View := view4 :: prefix5
private noncomputable def prefix3 : List View := view3 :: prefix4
private noncomputable def prefix2 : List View := view2 :: prefix3
private noncomputable def prefix1 : List View := view1 :: prefix2
private noncomputable def prefix0 : List View := view0 :: prefix1

private theorem prefix_read17 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 0 cut17 = (prefix17.map value).prod := by rfl
private theorem prefix_read16 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut16 = (prefix16.map value).prod :=
  fold_step value step17 (one16 value) (prefix_read17 value) rfl
private theorem prefix_read15 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 2 cut15 = (prefix15.map value).prod :=
  fold_step value step16 (one15 value) (prefix_read16 value) rfl
private theorem prefix_read14 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 3 cut14 = (prefix14.map value).prod :=
  fold_step value step15 (one14 value) (prefix_read15 value) rfl
private theorem prefix_read13 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 4 cut13 = (prefix13.map value).prod :=
  fold_step value step14 (one13 value) (prefix_read14 value) rfl
private theorem prefix_read12 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 5 cut12 = (prefix12.map value).prod :=
  fold_step value step13 (one12 value) (prefix_read13 value) rfl
private theorem prefix_read11 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 6 cut11 = (prefix11.map value).prod :=
  fold_step value step12 (one11 value) (prefix_read12 value) rfl
private theorem prefix_read10 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 7 cut10 = (prefix10.map value).prod :=
  fold_step value step11 (one10 value) (prefix_read11 value) rfl
private theorem prefix_read9 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 8 cut9 = (prefix9.map value).prod :=
  fold_step value step10 (one9 value) (prefix_read10 value) rfl
private theorem prefix_read8 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 9 cut8 = (prefix8.map value).prod :=
  fold_step value step9 (one8 value) (prefix_read9 value) rfl
private theorem prefix_read7 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 10 cut7 = (prefix7.map value).prod :=
  fold_step value step8 (one7 value) (prefix_read8 value) rfl
private theorem prefix_read6 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 11 cut6 = (prefix6.map value).prod :=
  fold_step value step7 (one6 value) (prefix_read7 value) rfl
private theorem prefix_read5 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 12 cut5 = (prefix5.map value).prod :=
  fold_step value step6 (one5 value) (prefix_read6 value) rfl
private theorem prefix_read4 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 13 cut4 = (prefix4.map value).prod :=
  fold_step value step5 (one4 value) (prefix_read5 value) rfl
private theorem prefix_read3 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 14 cut3 = (prefix3.map value).prod :=
  fold_step value step4 (one3 value) (prefix_read4 value) rfl
private theorem prefix_read2 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 15 cut2 = (prefix2.map value).prod :=
  fold_step value step3 (one2 value) (prefix_read3 value) rfl
private theorem prefix_read1 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 16 cut1 = (prefix1.map value).prod :=
  fold_step value step2 (one1 value) (prefix_read2 value) rfl
private theorem prefix_read0 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 17 cut0 = (prefix0.map value).prod :=
  fold_step value step1 (one0 value) (prefix_read1 value) rfl

private theorem initial_saved : (0, Cursor.Outcome.paused packet) = cut0 := by checked_cut_rfl

private theorem read_whole {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 400 (0, .paused packet) = (tail0.map value).prod :=
  (congrArg (Read value 400) initial_saved).trans (tail_read0 value)

private theorem read_prefix {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 17 (0, .paused packet) = (prefix0.map value).prod :=
  (congrArg (Read value 17) initial_saved).trans (prefix_read0 value)

private theorem word_literal : word 400 = tail0 := by
  have moved := congrArg FreeMonoid.toList (read_whole FreeMonoid.of)
  have literal : ((tail0.map FreeMonoid.of).prod).toList = tail0 := by checked_cut_rfl
  exact moved.trans literal

private theorem factors_literal :
    factors 400 = [("score", 0, 0), ("score", 0, 0), ("choose", 0, 2), ("choose", 1, 2)] := by
  have moved := congrArg (fun word : Word => word.toList.map factorSummary) (read_whole factorValue)
  have literal : ((tail0.map factorValue).prod).toList.map factorSummary =
      [("score", 0, 0), ("score", 0, 0), ("choose", 0, 2), ("choose", 1, 2)] := by checked_cut_rfl
  exact moved.trans literal

private theorem paid_literal : (run 400).1 = 159 :=
  (congrArg Prod.fst whole).trans actual_paid

private theorem effects_literal : effects 400 = [5, 5, 7, 7] := by
  have moved := congrArg FreeMonoid.toList (read_whole effectValue)
  have literal : ((tail0.map effectValue).prod).toList = [5, 5, 7, 7] := by checked_cut_rfl
  exact moved.trans literal

private theorem caches_count_literal :
    ((caches 400).filter fun completed => completed.2 = .delivery).length = 2 := by
  have moved := congrArg (fun word : FreeMonoid (CellId × NeedCacheLaws.CompletedReceiptKind) =>
    (word.toList.filter fun completed => completed.2 = .delivery).length) (read_whole cacheValue)
  have literal : (((tail0.map cacheValue).prod).toList.filter fun completed => completed.2 = .delivery).length = 2 := by
    checked_cut_rfl
  exact moved.trans literal

private theorem store_literal :
    OrderedDependencyStore.query (stateOf (run 400)).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  have moved := congrArg (fun saved => OrderedDependencyStore.query (stateOf saved).2.live.store 0) whole
  have literal : OrderedDependencyStore.query (stateOf cut161).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
    checked_cut_rfl
  exact moved.trans literal

private theorem recorded_eq (fuel capacity : Nat) :
    recorded fuel capacity = some ((Recording.Prefix.initial capacity).append (word fuel)) := by rfl

private theorem word_length : (word 400).length = 161 := by
  have moved := congrArg List.length word_literal
  have literal : tail0.length = 161 := by checked_cut_rfl
  exact moved.trans literal

theorem branch_words_literal :
    words = some [[("score", 0, 0), ("choose", 0, 2)], [("score", 0, 0), ("choose", 1, 2)]] := by
  have literal : wordsAt cut161 =
      some [[("score", 0, 0), ("choose", 0, 2)], [("score", 0, 0), ("choose", 1, 2)]] := by checked_cut_rfl
  exact (congrArg wordsAt whole).trans literal

theorem chronological_factors_literal :
    factors 400 = [("score", 0, 0), ("score", 0, 0), ("choose", 0, 2), ("choose", 1, 2)] := by
  exact factors_literal

theorem observed_ledger_identities_literal :
    Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400) =
      [4285307, 4674651, 32490407, 34246311] := by
  have moved := congrArg (fun word : FreeMonoid (Mettapedia.Algebra.SharedCoefficientLedger.Factor Nat CellId Factor) =>
    Mettapedia.Algebra.SharedCoefficientLedger.identities word.toList) (read_whole (ledgerBlock 407))
  have literal : Mettapedia.Algebra.SharedCoefficientLedger.identities ((tail0.map (ledgerBlock 407)).prod).toList =
      [4285307, 4674651, 32490407, 34246311] := by checked_cut_rfl
  exact moved.trans literal

/-- The same execution has two branch-local ordered words and one global
chronological observation. Neither the zero factors nor equal-valued rows
collapse, and the global word is not either answer's coefficient word. -/
theorem nested_zero_words_remain_per_answer :
    words = some [[("score", 0, 0), ("choose", 0, 2)], [("score", 0, 0), ("choose", 1, 2)]] ∧
      factors 400 = [("score", 0, 0), ("score", 0, 0), ("choose", 0, 2), ("choose", 1, 2)] ∧
      factors 400 ≠ (factors 400).reverse := by
  refine ⟨branch_words_literal, chronological_factors_literal, ?_⟩
  rw [chronological_factors_literal]
  decide +kernel

/-- Cache delivery, real effects and source coefficient production are
independent observations of this invocation. Both branches use their own
cached producer; the selected external handler serializes their effects. -/
theorem cached_delivery_adds_no_source_factor_or_effect :
    ((caches 400).filter fun completed => completed.2 = .delivery).length = 2 ∧
      (factors 400).length = 4 ∧ effects 400 = [5, 5, 7, 7] ∧
      OrderedDependencyStore.query (stateOf (run 400)).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  refine ⟨caches_count_literal, ?_, effects_literal, store_literal⟩
  rw [chronological_factors_literal]
  rfl

/-- These are physical observation occurrences, not a fold combining the
answer worlds. Copying their descriptions would repeat identities; claiming
this retained interval observes it at most once. -/
theorem chronological_ledger_keeps_occurrences_and_scope_claims :
    Mettapedia.Algebra.SharedCoefficientLedger.Valid (ledger 400) ∧
      ¬ Mettapedia.Algebra.SharedCoefficientLedger.Valid (ledger 400 ++ ledger 400) ∧
      Mettapedia.Algebra.SharedCoefficientLedger.Scoped.selected 0
        (Mettapedia.Algebra.SharedCoefficientLedger.Scoped.handle 0 17
          ⟨ledger 400, fun _ => none⟩) = [] := by
  refine ⟨?_, ?_, ?_⟩
  · change (Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400)).Nodup
    rw [observed_ledger_identities_literal]
    decide +kernel
  · change ¬ (Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400 ++ ledger 400)).Nodup
    simp only [Mettapedia.Algebra.SharedCoefficientLedger.identities, List.map_append]
    change ¬ (Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400) ++
      Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400)).Nodup
    rw [observed_ledger_identities_literal]
    decide +kernel
  · exact Mettapedia.Algebra.SharedCoefficientLedger.Scoped.selected_after_handle _ _ _

/-- Polling work counts accepted provider requests; finishing inspections and
source/cache roles are not silently billed as additional source firings. -/
theorem enabled_history_and_poll_invoice_are_separate :
    (run 400).1 = 159 ∧ (word 400).length = 161 ∧
      (recorded 400 1000).map (fun record => (record.items.length, record.omitted)) = some (161, 0) ∧
      ((recorded 400 1000).bind Recording.Prefix.complete?).isSome = true := by
  refine ⟨paid_literal, word_length, ?_, ?_⟩
  · rw [recorded_eq, word_literal]
    checked_cut_rfl
  · rw [recorded_eq, word_literal]
    checked_cut_rfl

/-- Recording capacity bounds only captured history. The omitted suffix is
never presented as a complete history or an empty semantic contribution. -/
theorem bounded_history_refuses_false_completeness :
    (recorded 400 2).map (fun record => (record.items.length, record.omitted)) = some (2, 159) ∧
      (recorded 400 2).bind Recording.Prefix.complete? = none := by
  rw [recorded_eq, word_literal]
  constructor <;> checked_cut_rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

open Lean Meta Elab Tactic in
elab "checked_control_rfl" : tactic => withMainContext do
  match ← getGoals with
  | [] => return
  | goal :: _ =>
      let target ← whnf (← instantiateMVars (← goal.getType))
      unless target.isAppOfArity ``Eq 3 do
        throwError "an equality is required, got {target}"
      goal.assign (← mkEqRefl target.getAppArgs[2]!)
      replaceMainGoal []

open Lean Meta Elab Tactic Term in
elab "checked_control_exact " proof:term : tactic => withMainContext do
  let goal ← getMainGoal
  let expression ← Term.elabTerm proof none
  Term.synthesizeSyntheticMVarsNoPostponing
  goal.assign (← instantiateMVars expression)
  replaceMainGoal []


private def suffixValue {Result : Type} [Monoid Result]
    (value : View → Result) (fuel : Nat) (earlier : Saved) : Result :=
  (sourceAccount annotation number revocationWorlds required needed act reader notice 407 () value).of
    (NativeControlCursor.ProtocolHistory.resumeHistory source client charge fuel earlier)

private theorem suffix_exact {Result : Type} [Monoid Result]
    (value : View → Result) (fuel : Nat) (earlier : Saved) :
    suffixValue value fuel earlier = Read value fuel earlier :=
  PassiveReader.exact_account annotation number revocationWorlds required needed act reader notice
    407 value fuel earlier

private theorem resumed_whole : Cursor.resume source client charge 383 (run 17) = run 400 :=
  (Cursor.advance_add source client charge 17 383 packet).symm

private theorem completed_inert (allowance : Nat) :
    Cursor.resume source client charge allowance (run 400) = run 400 := by
  have literal : Cursor.resume source client charge allowance cut161 = cut161 := by checked_control_rfl
  exact (congrArg (Cursor.resume source client charge allowance) whole).trans (literal.trans whole.symm)

private theorem resume_initial (fuel : Nat) :
    Cursor.resume source client charge fuel (0, .paused packet) = run fuel := by
  simpa only [Nat.zero_add, Cursor.advance_zero, run] using
    (Cursor.advance_add source client charge 0 fuel packet).symm

private theorem suffix_word : (Read FreeMonoid.of 383 (run 17)).toList = tail17 := by
  have moved := congrArg (fun saved => (Read FreeMonoid.of 383 saved).toList) whole_at17
  have folded := congrArg FreeMonoid.toList (tail_read17 FreeMonoid.of)
  have literal : ((tail17.map FreeMonoid.of).prod).toList = tail17 := by checked_control_rfl
  exact moved.trans (folded.trans literal)

private theorem prefix_word : word 17 = prefix0 := by
  have moved := congrArg FreeMonoid.toList (read_prefix FreeMonoid.of)
  have literal : ((prefix0.map FreeMonoid.of).prod).toList = prefix0 := by checked_control_rfl
  exact moved.trans literal

private theorem observed_erasure (fuel : Nat) (earlier : Saved) (record : Option (Recording.Prefix View)) :
    (observedResume annotation number revocationWorlds required needed act reader notice 407 fuel earlier record).1 =
      Cursor.resume source client charge fuel earlier := rfl

private theorem observed_record_eq (fuel : Nat) (earlier : Saved) (record : Recording.Prefix View) :
    (observedResume annotation number revocationWorlds required needed act reader notice 407 fuel earlier (some record)).2 =
      some (record.append (Read FreeMonoid.of fuel earlier).toList) := rfl

private theorem factors_split :
    factors 17 ++ (Read factorValue 383 (run 17)).toList.map factorSummary = factors 400 := by
  have split := PassiveReader.readSuffix_add annotation number revocationWorlds required needed act reader notice
    407 factorValue 17 383 (0, .paused packet)
  have moved := congrArg (fun word : Word => word.toList.map factorSummary) split
  simpa only [factors, resume_initial, FreeMonoid.toList_mul, List.map_append] using moved.symm

/-- Starting at this real paid cut observes only the later interval. Its
suffix factors concatenate with the prefix in actual callback order. -/
theorem start_recording_at_paid_cut_keeps_the_real_suffix :
    let first := run 17
    let suffixFactors := (suffixValue factorValue 383 first).toList.map factorSummary
    let observed := observedResume annotation number revocationWorlds required needed act reader notice
      407 383 first (some (Recording.Prefix.initial 1000))
    factors 17 ++ suffixFactors = factors 400 ∧ observed.1.1 = (run 400).1 ∧
      (observed.2.map fun record => record.items.length) = some 144 ∧
      OrderedDependencyStore.query (stateOf observed.1).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  have account := suffix_exact factorValue 383 (run 17)
  have described := congrArg (fun word : Word => word.toList.map factorSummary) account
  refine ⟨?_, ?_, ?_, ?_⟩
  · checked_control_exact (congrArg (fun later => factors 17 ++ later) described).trans factors_split
  · checked_control_exact (congrArg Prod.fst (observed_erasure 383 (run 17) (some (Recording.Prefix.initial 1000)))).trans (congrArg Prod.fst resumed_whole)
  · rw [observed_record_eq, suffix_word]
    checked_control_rfl
  · checked_control_exact (congrArg (fun saved => OrderedDependencyStore.query (stateOf saved).2.live.store 0)
      ((observed_erasure 383 (run 17) (some (Recording.Prefix.initial 1000))).trans resumed_whole)).trans store_literal

/-- Stopping preserves the selected prefix while the actual computation
continues; forgetting it disables future recording without restarting work. -/
theorem stop_and_forget_never_reissue_the_paid_prefix :
    let first := run 17
    let captured := (Recording.Prefix.initial 1000).append (word 17)
    let stopped := stopAndResume annotation number revocationWorlds required needed act reader notice
      407 383 first captured
    let forgotten := observedResume annotation number revocationWorlds required needed act reader notice
      407 10 stopped.1 (forgetRecording (some stopped.2))
    stopped.1.1 = (run 400).1 ∧ (stopped.2.map tag).items.length = 17 ∧
      forgotten.2 = none ∧ forgotten.1.1 = (run 400).1 ∧
      (stateOf forgotten.1).1 = (stateOf (run 400)).1 ∧
      OrderedDependencyStore.query (stateOf forgotten.1).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  dsimp only
  rw [stop_preserves_prefix annotation number revocationWorlds required needed act reader notice 407 383 (run 17) ((Recording.Prefix.initial 1000).append (word 17)), resumed_whole]
  change (run 400).1 = (run 400).1 ∧
    (((Recording.Prefix.initial 1000).append (word 17)).map tag).items.length = 17 ∧
    (observedResume annotation number revocationWorlds required needed act reader notice 407 10 (run 400) none).2 = none ∧
    (observedResume annotation number revocationWorlds required needed act reader notice 407 10 (run 400) none).1.1 = (run 400).1 ∧
    (stateOf (observedResume annotation number revocationWorlds required needed act reader notice 407 10 (run 400) none).1).1 =
      (stateOf (run 400)).1 ∧ _
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩
  · rw [prefix_word]
    checked_control_rfl
  · checked_control_exact congrArg Prod.fst ((observed_erasure 10 (run 400) none).trans (completed_inert 10))
  · checked_control_exact congrArg (fun saved => (stateOf saved).1) ((observed_erasure 10 (run 400) none).trans (completed_inert 10))
  · checked_control_exact (congrArg (fun saved => OrderedDependencyStore.query (stateOf saved).2.live.store 0)
      ((observed_erasure 10 (run 400) none).trans (completed_inert 10))).trans store_literal

/-- A rejected observation decoder does not filter the missing evidence.
Rechecking the same complete retained interval changes neither source state
nor the already accepted effects; it is not native execution authority. -/
theorem qualified_readback_is_passive_and_missing_payload_refuses :
    let captured := (Recording.Prefix.initial 1000).append (word 400)
    let reread := Recording.Prefix.project? (fun event => some (tag event)) captured
    let resumed := observedResume annotation number revocationWorlds required needed act reader notice
      407 10 (run 400) (some captured)
    Recording.Prefix.project? (fun (_ : View) => (none : Option Nat)) captured = none ∧
      reread.map List.length = some 161 ∧
      (resumed.2.map (fun record => record.items.length)) = some 161 ∧
      resumed.1.1 = (run 400).1 ∧
      (stateOf resumed.1).1 = (stateOf (run 400)).1 ∧
      OrderedDependencyStore.query (stateOf resumed.1).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [word_literal]
    checked_control_rfl
  · rw [word_literal]
    checked_control_rfl
  · rw [observed_record_eq]
    have quiet : Read FreeMonoid.of 10 (run 400) = 1 := by
      have moved := congrArg (Read FreeMonoid.of 10) whole
      have literal : Read FreeMonoid.of 10 cut161 = 1 := by checked_control_rfl
      exact moved.trans literal
    rw [quiet, word_literal]
    checked_control_rfl
  · checked_control_exact congrArg Prod.fst ((observed_erasure 10 (run 400) (some ((Recording.Prefix.initial 1000).append (word 400)))).trans (completed_inert 10))
  · checked_control_exact congrArg (fun saved => (stateOf saved).1) ((observed_erasure 10 (run 400) (some ((Recording.Prefix.initial 1000).append (word 400)))).trans (completed_inert 10))
  · checked_control_exact (congrArg (fun saved => OrderedDependencyStore.query (stateOf saved).2.live.store 0)
      ((observed_erasure 10 (run 400) (some ((Recording.Prefix.initial 1000).append (word 400)))).trans (completed_inert 10))).trans store_literal

def revoke (saved : Saved) : Saved :=
  (saved.1, Cursor.Outcome.mapState client (source := source) (target := source)
    (fun state => ((state.1.1, { state.1.2 with live := { state.1.2.live with
      point := Cursor.ReadOnlyQuery.OwnWrite.Controls.revoked } }), state.2)) saved.2)

def denied := Cursor.resume source client charge 10 (revoke (run 17))
def deniedHistory := NativeControlCursor.ProtocolHistory.resumeHistory source client charge 10 (revoke (run 17))

private noncomputable def deniedCut : Saved := normalized_cursor_cut% (Cursor.resume source client charge 10 (revoke cut17))
private theorem denied_step : Cursor.resume source client charge 10 (revoke cut17) = deniedCut := by checked_control_rfl
private theorem denied_eq : denied = deniedCut :=
  (congrArg (Cursor.resume source client charge 10) (congrArg revoke whole_at17)).trans denied_step

private theorem denied_account {Result : Type} [Monoid Result] (value : View → Result) :
    suffixValue value 10 (revoke (run 17)) = Read value 10 (revoke cut17) :=
  (suffix_exact value 10 (revoke (run 17))).trans
    (congrArg (Read value 10) (congrArg revoke whole_at17))

/-- Revocation adds an honest refused inspection to history, then the client
finishes that refusal. It emits no factor or effect and changes neither the
paid account nor the complete retained branch frontier. -/
theorem current_refusal_has_no_semantic_history_contribution :
    (suffixValue FreeMonoid.of 10 (revoke (run 17))).toList.map tag = [2, 1] ∧
      (suffixValue factorValue 10 (revoke (run 17))).toList = [] ∧
      (suffixValue effectValue 10 (revoke (run 17))).toList = [] ∧
      denied.1 = 17 ∧ (stateOf denied).1 = (stateOf (run 17)).1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have moved := congrArg (fun word : FreeMonoid View => word.toList.map tag) (denied_account FreeMonoid.of)
    have literal : (Read FreeMonoid.of 10 (revoke cut17)).toList.map tag = [2, 1] := by checked_control_rfl
    checked_control_exact moved.trans literal
  · have moved := congrArg FreeMonoid.toList (denied_account factorValue)
    have literal : (Read factorValue 10 (revoke cut17)).toList = [] := by checked_control_rfl
    checked_control_exact moved.trans literal
  · have moved := congrArg FreeMonoid.toList (denied_account effectValue)
    have literal : (Read effectValue 10 (revoke cut17)).toList = [] := by checked_control_rfl
    checked_control_exact moved.trans literal
  · have literal : deniedCut.1 = 17 := by checked_control_rfl
    checked_control_exact (congrArg Prod.fst denied_eq).trans literal
  · have literal : (stateOf deniedCut).1 = (stateOf cut17).1 := by checked_control_rfl
    checked_control_exact (congrArg (fun saved => (stateOf saved).1) denied_eq).trans
      (literal.trans (congrArg (fun saved => (stateOf saved).1) whole_at17.symm))

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.History.Controls
