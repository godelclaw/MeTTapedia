import Mettapedia.Languages.MeTTa.HE.RecursiveExecution
import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution
import Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy
import Mettapedia.Machines.BranchLocalNeed.DependentService
import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.Machines.Cursor.ReadOnlyQuery
import Mettapedia.Machines.Cursor.ProductiveBlocks
import Mettapedia.Machines.RevisionDependencySet

/-!
# The retained HE evaluator as a service machine

A host language may hand a request to the retained HE evaluator and receive one
value in reply. The evaluator's result occurrences are published as the
service's own events, and its completed result multiset determines the reply.
A single occurrence that reads as a value answers the request. Insufficient
evaluator or leaf depth suspends the retained configuration; it is not a
completed no-result reply. No occurrence,
several occurrences, or an occurrence that does not read as a value is a
failure: a reply never selects one result from several, so it does not depend
on the order of the results (`answer_perm`). A completed service run publishes
exactly the covered evaluator's results and replies with their answer
(`service_finished`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveService

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine RecursiveExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Why an evaluation does not answer a request with one value. -/
inductive Failure where
  | noResult
  | several (count : Nat)
  | unreadable (value : Atom)
  deriving DecidableEq, Repr

variable {Value : Type} (decode : Atom → Option Value)

/-- The reply to a request, from the complete result multiset. -/
def answer : ResultSet → Reply Value Failure
  | [] => .faulted .noResult
  | [(value, _)] =>
      match decode value with
      | some read => .returned read
      | none => .faulted (.unreadable value)
  | results => .faulted (.several results.length)

theorem answer_of_two_le (results : ResultSet) (several : 2 ≤ results.length) :
    answer decode results = .faulted (.several results.length) := by
  match results, several with
  | _ :: _ :: _, _ => rfl

/-- The reply depends only on the result multiset, not on the order of its occurrences. -/
theorem answer_perm {first second : ResultSet} (perm : first.Perm second) :
    answer decode first = answer decode second := by
  have length := perm.length_eq
  match first, second, perm, length with
  | [], second, perm, _ => rw [perm.nil_eq]
  | [single], second, perm, _ => rw [List.singleton_perm.mp perm]
  | _ :: _ :: rest, second, _, length =>
      rw [answer_of_two_le decode _ (by simp), answer_of_two_le decode second (by simp at length; omega), length]

/-- The evaluator as a service: its results become service events, and its final
result history becomes the reply. -/
def service {Event : Type} (dispatch : GroundedDispatch) (embed : ResultPair → Event) :
    Machine Configuration Event (Reply Value Failure) Checked.ResourceRequest :=
  (Checked.machine dispatch).relabel embed (fun final => answer decode final.emitted) id

/-- **A completed service run publishes exactly the evaluator's results and
replies with their answer.** -/
theorem service_finished {Event : Type} (dispatch : GroundedDispatch) (embed : ResultPair → Event)
    (space : Space) (task : Task) (fuel : Nat) (events : List Event) (reply : Reply Value Failure)
    (finished : (service decode dispatch embed).run fuel (Configuration.initial space task) =
      (events, .finished reply)) :
    events = (task.denote space dispatch).map embed ∧ reply = answer decode (task.denote space dispatch) := by
  rw [service, Machine.run_relabel] at finished
  rcases ran : (Checked.machine dispatch).run fuel (Configuration.initial space task) with ⟨results, outcome⟩
  rw [ran] at finished
  cases outcome with
  | finished final =>
      simp only [Outcome.relabel, Prod.mk.injEq, Outcome.finished.injEq] at finished
      obtain ⟨rfl, rfl⟩ := finished
      obtain ⟨meaning, history, _⟩ := finished_results space dispatch task fuel results final
        (Checked.finished_refines dispatch fuel _ results final ran)
      subst meaning
      exact ⟨rfl, by rw [history]⟩
  | faulted => simp [Outcome.relabel] at finished
  | suspended _ _ => simp [Outcome.relabel] at finished
  | stuck _ => simp [Outcome.relabel] at finished
  | exhausted _ => simp [Outcome.relabel] at finished

/-- The configuration-scoped worker uses the same host reply contract and
common callback interface. Its demand/type policy remains explicit. -/
def checkedService {Event : Type} (policy : FirstSuccessRecursiveExecution.TypePolicy)
    (dispatch : GroundedDispatch) (embed : ResultPair → Event) :
    Machine Configuration Event (Reply Value Failure) Checked.ResourceRequest :=
  (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).relabel embed
    (fun final => answer decode final.emitted) id

/-- Independent covered source evidence constructs a complete scoped host
service run. Closed annotations are the admitted transfer profile; equation
instances and caller constraints may remain open. -/
theorem checked_service_source_completed {Event : Type} (embed : ResultPair → Event)
    {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (source : FirstSuccessSourceExecution.AtomDerivation
      (comparison := comparison) space live value expected incoming fuel results)
    (covered : source.Covered) (closed : FirstSuccessScopedAdequacy.ClosedTypeAnnotations space) :
    ∃ budget, ∀ later,
      (checkedService decode FirstSuccessRecursiveExecution.scopedTypes GroundedDispatch.none embed).run
        (budget + later) (Configuration.initial space (.atom value expected incoming fuel live)) =
        (results.map embed,.finished (answer decode results)) := by
  obtain ⟨budget,completed⟩ := FirstSuccessScopedAdequacy.AtomDerivation.scoped_completed
    source covered closed []
  refine ⟨budget,fun later => ?_⟩
  rw [checkedService,Machine.run_relabel]
  simp only [Configuration.initial]
  rw [completed later]
  simp only [Outcome.relabel,List.nil_append]

/-- Every completed service observation agrees with the independent source
batch. No completed evaluator run or desired reply is supplied as source evidence. -/
theorem checked_service_source_finished {Event : Type} (embed : ResultPair → Event)
    {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (source : FirstSuccessSourceExecution.AtomDerivation
      (comparison := comparison) space live value expected incoming fuel results)
    (covered : source.Covered) (closed : FirstSuccessScopedAdequacy.ClosedTypeAnnotations space)
    (budget : Nat) (events : List Event) (reply : Reply Value Failure)
    (finished : (checkedService decode FirstSuccessRecursiveExecution.scopedTypes GroundedDispatch.none embed).run
      budget (Configuration.initial space (.atom value expected incoming fuel live)) =
        (events,.finished reply)) :
    events = results.map embed ∧ reply = answer decode results := by
  obtain ⟨bound,completed⟩ := checked_service_source_completed decode embed source covered closed
  have stable :=
    (checkedService decode FirstSuccessRecursiveExecution.scopedTypes GroundedDispatch.none embed).run_stable
      budget bound (Configuration.initial space (.atom value expected incoming fuel live)) (by
        intro residual impossible
        rw [finished] at impossible
        cases impossible)
  have same := completed budget
  rw [Nat.add_comm bound budget,stable,finished] at same
  exact ⟨(Prod.mk.inj same).1,Outcome.finished.inj (Prod.mk.inj same).2⟩

/-- A paused host service resumes from its actual saved configuration. Only
the remaining occurrence events are emitted; its one reply uses the complete
source batch, including the prefix already retained in that configuration. -/
theorem checked_service_source_resume {Event : Type} (embed : ResultPair → Event)
    {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (source : FirstSuccessSourceExecution.AtomDerivation
      (comparison := comparison) space live value expected incoming fuel results)
    (covered : source.Covered) (closed : FirstSuccessScopedAdequacy.ClosedTypeAnnotations space)
    (first : Nat) (before : List Event) (saved : Configuration)
    (paused : (checkedService decode FirstSuccessRecursiveExecution.scopedTypes GroundedDispatch.none embed).run
      first (Configuration.initial space (.atom value expected incoming fuel live)) =
        (before,.exhausted saved)) :
    ∃ budget after,
      (checkedService decode FirstSuccessRecursiveExecution.scopedTypes GroundedDispatch.none embed).run
        budget saved = (after,.finished (answer decode results)) ∧
      before ++ after = results.map embed := by
  obtain ⟨budget,completed⟩ := checked_service_source_completed decode embed source covered closed
  have pending :=
    (checkedService decode FirstSuccessRecursiveExecution.scopedTypes GroundedDispatch.none embed).established_and_pending
      first budget (Configuration.initial space (.atom value expected incoming fuel live)) saved before paused
  have whole := completed first
  rw [Nat.add_comm budget first,pending] at whole
  refine ⟨budget,
    ((checkedService decode FirstSuccessRecursiveExecution.scopedTypes GroundedDispatch.none embed).run budget saved).1,
    Prod.ext rfl (Prod.mk.inj whole).2,(Prod.mk.inj whole).1⟩

namespace CheckedServiceControls

private def caller : Bindings := ⟨[],[("x","y")]⟩
private def payload : Atom := .expression [.symbol "Pair",.var "x",.var "x"]
private def context : Space := ⟨[]⟩
private def initial : Configuration :=
  Configuration.initial context (.atom payload Atom.atomType caller 1 [])
private def afterPublication : Configuration :=
  ⟨context,.returning [],[],[(payload,caller)]⟩
private def server := checkedService (Value := Atom) some
  FirstSuccessRecursiveExecution.scopedTypes GroundedDispatch.none id

private theorem source : FirstSuccessSourceExecution.AtomDerivation
    (comparison := .records) context [] payload Atom.atomType caller 1 [(payload,caller)] :=
  .leaf [] payload Atom.atomType caller 0
    (Or.inr ⟨Atom.expressionType,.expression _,Or.inl rfl⟩)

/-- The service control is admitted by independent source evidence, while
retaining an open caller alias and repeated raw operand positions. -/
theorem independent_source_admission : source.Covered ∧
    FirstSuccessScopedAdequacy.ClosedTypeAnnotations context :=
  ⟨.leaf (leaf := Or.inr ⟨Atom.expressionType,.expression _,Or.inl rfl⟩),
    (FirstSuccessScopedAdequacy.closedColonAnnotations_of_bool
    (by decide +kernel)).closedTypeAnnotations⟩

/-- Publishing the final occurrence does not itself finish the service.
The complete retained configuration still owes its reply boundary. -/
theorem published_occurrence_is_not_a_reply :
    server.run 2 initial = ([(payload,caller)],.exhausted afterPublication) := by
  rfl

/-- Resuming the actual saved service emits no duplicate occurrence.
Restarting the request emits it again. -/
theorem resume_returns_once_without_republishing :
    server.run 1 afterPublication = ([],.finished (.returned payload)) ∧
      server.run 3 initial = ([(payload,caller)],.finished (.returned payload)) := by
  constructor <;> rfl

end CheckedServiceControls

namespace CheckedAdmission

open FirstSuccessRecursiveExecution (TypePolicy)
open Mettapedia.Machines
open Mettapedia.Machines.ProductiveCoreAdapters
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open _root_.CategoryTheory

abbrev Saved (dispatch : GroundedDispatch) (policy : TypePolicy) :=
  Nat × EventCursor.Result (FirstSuccessRecursiveExecution.Checked.machine dispatch policy)

/-- Every retained endpoint of an actual checked transition keeps the loaded
space. The checked worker does not implement a mutable host-space operation. -/
theorem step_space (dispatch : GroundedDispatch) (policy : TypePolicy)
    {before : Configuration}
    {action : Transition Configuration ResultPair Configuration RecursiveMachine.Checked.ResourceRequest}
    (advanced : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).step before = some action) :
    match action with
    | .silent saved | .publish _ saved | .finish saved | .call _ saved => saved.space = before.space
    | .fail _ => False := by
  cases before with
  | mk space control stack emitted =>
      cases blockedHere : FirstSuccessRecursiveExecution.Checked.blocked dispatch
          ⟨space, control, stack, emitted⟩ policy with
      | some request =>
          simp only [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
            blockedHere, Option.some.injEq] at advanced
          cases advanced
          rfl
      | none =>
          cases control with
          | work task =>
              simp only [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
                blockedHere, FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
                Option.map_some, Transition.relabel, Option.some.injEq] at advanced
              cases advanced
              rfl
          | returning results =>
              cases stack with
              | cons frame rest =>
                  simp only [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
                    blockedHere, FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
                    Option.map_some, Transition.relabel, Option.some.injEq] at advanced
                  cases advanced
                  rfl
              | nil =>
                  cases results <;>
                    simp only [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
                      blockedHere, FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
                      Option.map_some, Transition.relabel, Option.some.injEq] at advanced
                  all_goals cases advanced; rfl

/-- The loaded space invariant is earned by the actual run, including every
binding-changing child and retained caller; it is not a whole-run premise. -/
theorem paused_space (dispatch : GroundedDispatch) (policy : TypePolicy)
    {budget : Nat} {before saved : Configuration} {events : ResultSet}
    (paused : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run budget before =
      (events, .exhausted saved)) : saved.space = before.space := by
  induction budget generalizing before events with
  | zero => cases paused; rfl
  | succ budget ih =>
      cases stepped : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).step before with
      | none => simp [Machine.run, stepped] at paused
      | some action =>
          have space := step_space dispatch policy stepped
          cases action with
          | silent next =>
              have following : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run budget next =
                  (events, .exhausted saved) := by
                simpa only [Machine.run, stepped] using paused
              exact (ih following).trans space
          | publish added next =>
              have following : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run budget next =
                  (((FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run budget next).1,
                    .exhausted saved) := by
                apply Prod.ext
                · rfl
                · simpa only [Machine.run, stepped] using congrArg Prod.snd paused
              exact (ih following).trans space
          | finish _ => simp [Machine.run, stepped] at paused
          | fail _ => simp [Machine.run, stepped] at paused
          | call _ _ => simp [Machine.run, stepped] at paused

theorem requested_space (dispatch : GroundedDispatch) (policy : TypePolicy)
    {budget : Nat} {before saved : Configuration} {events : ResultSet}
    {request : RecursiveMachine.Checked.ResourceRequest}
    (pending : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run budget before =
      (events, .suspended request saved)) : saved.space = before.space := by
  induction budget generalizing before events with
  | zero => simp [Machine.run] at pending
  | succ budget ih =>
      cases stepped : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).step before with
      | none => simp [Machine.run, stepped] at pending
      | some action =>
          have space := step_space dispatch policy stepped
          cases action with
          | silent next =>
              have following : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run budget next =
                  (events, .suspended request saved) := by
                simpa only [Machine.run, stepped] using pending
              exact (ih following).trans space
          | publish added next =>
              have following : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run budget next =
                  (((FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run budget next).1,
                    .suspended request saved) := by
                apply Prod.ext
                · rfl
                · simpa only [Machine.run, stepped] using congrArg Prod.snd pending
              exact (ih following).trans space
          | finish _ => simp [Machine.run, stepped] at pending
          | fail _ => simp [Machine.run, stepped] at pending
          | call called target =>
              have same : called = request ∧ target = saved := by
                simpa only [Machine.run, stepped, Prod.mk.injEq, Outcome.suspended.injEq] using
                  congrArg Prod.snd pending
              obtain ⟨rfl, rfl⟩ := same
              exact space

variable {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
  (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld) {size : Nat}

/-- Re-enter a pending read-only HE cursor under its captured space dependency
and the current invocation right. Refusal retains the complete cursor and
account. An earned terminal outcome needs no new execution permission.
Authority eligibility is checked here; consumption and external host effects
remain the respective provider's operations. -/
def resume (captured current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (reader : Fin size) (required : authority.Fibre current.point.world)
    [Decidable (FrameUpdate current.point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget : Nat) (previous : Saved dispatch policy) (extra : Nat := 0) :
    Except (Saved dispatch policy) (Saved dispatch policy) :=
  if budget = 0 then .ok previous else
  let pending := match (EventCursor.read
      (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2).2 with
    | .exhausted _ => true
    | .suspended .evaluationDepth _ | .suspended .leafDepth _ => extra != 0
    | _ => false
  if pending then
    if OrderedDependencyStore.checkRead current.store
        (OrderedDependencyStore.readStamp captured.store reader) = true ∧
        FrameUpdate current.point.authority required then
      .ok (FirstSuccessRecursiveExecution.Checked.Scheduler.grant dispatch policy price budget extra previous)
    else .error previous
  else .ok previous

theorem resume_zero (captured current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (reader : Fin size) (required : authority.Fibre current.point.world)
    [Decidable (FrameUpdate current.point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (previous : Saved dispatch policy) :
    resume authority captured current reader required dispatch policy price 0 previous = .ok previous := rfl

theorem resume_refused (captured current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (reader : Fin size) (required : authority.Fibre current.point.world)
    [Decidable (FrameUpdate current.point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget : Nat) (previous : Saved dispatch policy) (events : ResultSet) (saved : Configuration)
    (pending : EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2 =
      (events, .exhausted saved))
    (denied : OrderedDependencyStore.checkRead current.store
        (OrderedDependencyStore.readStamp captured.store reader) = false ∨
        ¬ FrameUpdate current.point.authority required) :
    resume authority captured current reader required dispatch policy price (budget + 1) previous =
      .error previous := by
  rcases denied with stale | forbidden
  · simp [resume, pending, stale]
  · simp [resume, pending, forbidden]

theorem resume_granted (captured current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (reader : Fin size) (required : authority.Fibre current.point.world)
    [Decidable (FrameUpdate current.point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget : Nat) (previous : Saved dispatch policy) (events : ResultSet) (saved : Configuration)
    (pending : EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2 =
      (events, .exhausted saved))
    (valid : OrderedDependencyStore.checkRead current.store
      (OrderedDependencyStore.readStamp captured.store reader) = true)
    (allowed : FrameUpdate current.point.authority required) :
    resume authority captured current reader required dispatch policy price (budget + 1) previous =
      .ok (Cursor.resume (EventCursor.provider (FirstSuccessRecursiveExecution.Checked.machine dispatch policy))
        EventCursor.client
        (EventCursor.charge (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) price)
        (budget + 1) previous) := by
  simp [resume, pending, valid, allowed, FirstSuccessRecursiveExecution.Checked.Scheduler.grant]

/-- Scheduling does not turn an unserved host request, a fault, or a completed
answer into fresh worker execution. This includes a cursor whose terminal
reply has not yet had its final client inspection. -/
theorem resume_terminal (captured current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (reader : Fin size) (required : authority.Fibre current.point.world)
    [Decidable (FrameUpdate current.point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget : Nat) (previous : Saved dispatch policy)
    (terminal : ∀ saved, (EventCursor.read
      (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2).2 ≠ .exhausted saved) :
    resume authority captured current reader required dispatch policy price budget previous = .ok previous := by
  unfold resume
  split
  · rfl
  · cases observed : (EventCursor.read
        (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2).2
    case suspended request saved => cases request <;> rfl
    all_goals first | rfl | exact (terminal _ observed).elim

/-- A positive depth grant enters only after the same dependency and current
authority checks. The existing checked scheduler preserves the selected type
policy; this operation supplies no answer to an external primitive request. -/
theorem resume_depth_granted (captured current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (reader : Fin size) (required : authority.Fibre current.point.world)
    [Decidable (FrameUpdate current.point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget extra : Nat) (previous : Saved dispatch policy) (events : ResultSet)
    (request : RecursiveMachine.Checked.ResourceRequest) (saved : Configuration)
    (depth : request = .evaluationDepth ∨ request = .leafDepth)
    (pending : EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2 =
      (events, .suspended request saved))
    (valid : OrderedDependencyStore.checkRead current.store
      (OrderedDependencyStore.readStamp captured.store reader) = true)
    (allowed : FrameUpdate current.point.authority required) :
    resume authority captured current reader required dispatch policy price (budget + 1) previous (extra + 1) =
      .ok (FirstSuccessRecursiveExecution.Checked.Scheduler.grant dispatch policy price
        (budget + 1) (extra + 1) previous) := by
  rcases depth with rfl | rfl <;> simp [resume, pending, valid, allowed]

theorem resume_depth_refused (captured current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (reader : Fin size) (required : authority.Fibre current.point.world)
    [Decidable (FrameUpdate current.point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget extra : Nat) (previous : Saved dispatch policy) (events : ResultSet)
    (request : RecursiveMachine.Checked.ResourceRequest) (saved : Configuration)
    (depth : request = .evaluationDepth ∨ request = .leafDepth)
    (pending : EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2 =
      (events, .suspended request saved))
    (denied : OrderedDependencyStore.checkRead current.store
        (OrderedDependencyStore.readStamp captured.store reader) = false ∨
        ¬ FrameUpdate current.point.authority required) :
    resume authority captured current reader required dispatch policy price (budget + 1) previous (extra + 1) =
      .error previous := by
  rcases depth with rfl | rfl <;> rcases denied with stale | forbidden
  all_goals first | simp [resume, pending, stale] | simp [resume, pending, forbidden]

theorem resume_service_request_unchanged
    (captured current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (reader : Fin size) (required : authority.Fibre current.point.world)
    [Decidable (FrameUpdate current.point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget extra : Nat) (previous : Saved dispatch policy) (events : ResultSet)
    (instruction : Atom) (saved : Configuration)
    (pending : EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2 =
      (events, .suspended (.primitiveService instruction) saved)) :
    resume authority captured current reader required dispatch policy price budget previous extra = .ok previous := by
  simp [resume, pending]

/-- Currentness is established along the existing store update algorithm.
Equal counters in unrelated hand-built stores are not source evidence. The
same law covers absence and duplicate equation occurrences. -/
theorem current_space (captured : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (actions : List (OrderedDependencyStore.Action Atom size)) (reader : Fin size)
    (lawful : OrderedDependencyStore.ObserverInvariant captured.store)
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute captured.store actions)
      (OrderedDependencyStore.readStamp captured.store reader) = true)
    (saved : Configuration) (loaded : saved.space = ⟨OrderedDependencyStore.query captured.store reader⟩) :
    saved.space = ⟨OrderedDependencyStore.query (OrderedDependencyStore.execute captured.store actions) reader⟩ := by
  rw [Cursor.ReadOnlyQuery.OwnWrite.current_source_agrees authority captured actions reader lawful valid]
  exact loaded

/-- A reached HE cut is advanced through the existing dependency/authority
boundary. Its source view is the validated current view, and the same saved
worker contributes exactly the suffix account and suffix publications.
Neither its earlier publications nor its caller stack are recomputed. -/
theorem resume_reached_cut (captured : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (actions : List (OrderedDependencyStore.Action Atom size)) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (earlier later : Nat) (source saved : Configuration) (events : ResultSet)
    (lawful : OrderedDependencyStore.ObserverInvariant captured.store)
    (loaded : source.space = ⟨OrderedDependencyStore.query captured.store reader⟩)
    (reached : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run earlier source =
      (events, .exhausted saved))
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute captured.store actions)
      (OrderedDependencyStore.readStamp captured.store reader) = true)
    (allowed : FrameUpdate point.authority required) :
    let previous := FirstSuccessRecursiveExecution.Checked.Scheduler.visit dispatch policy price earlier source
    let current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size :=
      ⟨OrderedDependencyStore.execute captured.store actions, point⟩
    ∃ actual, resume authority captured current reader required dispatch policy price (later + 1) previous = .ok actual ∧
      saved.space = ⟨OrderedDependencyStore.query current.store reader⟩ ∧
      actual.1 = previous.1 +
        (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).spent price (later + 1) saved ∧
      EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) actual.2 =
        (events ++ ((FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run (later + 1) saved).1,
          ((FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run (later + 1) saved).2) := by
  let previous := FirstSuccessRecursiveExecution.Checked.Scheduler.visit dispatch policy price earlier source
  let current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size :=
    ⟨OrderedDependencyStore.execute captured.store actions, point⟩
  let actual := Cursor.resume
    (EventCursor.provider (FirstSuccessRecursiveExecution.Checked.machine dispatch policy)) EventCursor.client
    (EventCursor.charge (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) price)
    (later + 1) previous
  have pending : EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2 =
      (events, .exhausted saved) :=
    (FirstSuccessRecursiveExecution.Checked.Scheduler.visit_read dispatch policy price earlier source).trans reached
  have previous_eq : previous =
      ((FirstSuccessRecursiveExecution.Checked.machine dispatch policy).spent price earlier source,
        .paused (EventCursor.packet (FirstSuccessRecursiveExecution.Checked.machine dispatch policy)
          (events, .exhausted saved))) :=
    EventCursor.advance_exhausted (FirstSuccessRecursiveExecution.Checked.machine dispatch policy)
      price earlier source [] reached
  refine ⟨actual, resume_granted authority captured current reader required dispatch policy price later
    previous events saved pending valid allowed, ?_, ?_, ?_⟩
  · exact current_space authority captured actions reader lawful valid saved
      ((paused_space dispatch policy reached).trans loaded)
  · dsimp only [actual]
    rw [previous_eq]
    simpa only [Cursor.resume, FirstSuccessRecursiveExecution.Checked.Scheduler.visit_account] using congrArg
      ((FirstSuccessRecursiveExecution.Checked.machine dispatch policy).spent price earlier source + ·)
      (EventCursor.advance_run (FirstSuccessRecursiveExecution.Checked.machine dispatch policy)
        price (later + 1) saved events).1
  · dsimp only [actual]
    rw [previous_eq]
    exact (EventCursor.advance_run (FirstSuccessRecursiveExecution.Checked.machine dispatch policy)
      price (later + 1) saved events).2

/-- The same current-world admission precedes a grant to an actual reached
depth request. Replenishment retains its validated space, prior publications,
callers and type policy; only the pending operation receives the grant. -/
theorem resume_reached_depth (captured : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (actions : List (OrderedDependencyStore.Action Atom size)) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)]
    (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (earlier later extra : Nat) (source saved : Configuration) (events : ResultSet)
    (request : RecursiveMachine.Checked.ResourceRequest)
    (depth : request = .evaluationDepth ∨ request = .leafDepth)
    (lawful : OrderedDependencyStore.ObserverInvariant captured.store)
    (loaded : source.space = ⟨OrderedDependencyStore.query captured.store reader⟩)
    (reached : (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).run earlier source =
      (events, .suspended request saved))
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute captured.store actions)
      (OrderedDependencyStore.readStamp captured.store reader) = true)
    (allowed : FrameUpdate point.authority required) :
    let previous := FirstSuccessRecursiveExecution.Checked.Scheduler.visit dispatch policy price earlier source
    let current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size :=
      ⟨OrderedDependencyStore.execute captured.store actions, point⟩
    ∃ actual,
      resume authority captured current reader required dispatch policy price (later + 1) previous (extra + 1) = .ok actual ∧
      (RecursiveMachine.Checked.replenish (extra + 1) saved).space =
        ⟨OrderedDependencyStore.query current.store reader⟩ ∧
      actual.1 = previous.1 + (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).spent price
        (later + 1) (RecursiveMachine.Checked.replenish (extra + 1) saved) ∧
      EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) actual.2 =
        FirstSuccessRecursiveExecution.Checked.continueRun dispatch (later + 1) (extra + 1)
          (events, .suspended request saved) policy := by
  let previous := FirstSuccessRecursiveExecution.Checked.Scheduler.visit dispatch policy price earlier source
  let current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size :=
    ⟨OrderedDependencyStore.execute captured.store actions, point⟩
  have pending : EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine dispatch policy) previous.2 =
      (events, .suspended request saved) :=
    (FirstSuccessRecursiveExecution.Checked.Scheduler.visit_read dispatch policy price earlier source).trans reached
  refine ⟨FirstSuccessRecursiveExecution.Checked.Scheduler.grant dispatch policy price
    (later + 1) (extra + 1) previous,
    resume_depth_granted authority captured current reader required dispatch policy price later extra
      previous events request saved depth pending valid allowed, ?_, ?_, ?_⟩
  · rw [RecursiveMachine.Checked.replenish_space]
    exact current_space authority captured actions reader lawful valid saved
      ((requested_space dispatch policy reached).trans loaded)
  · exact FirstSuccessRecursiveExecution.Checked.Scheduler.grant_depth_account dispatch policy price
      (later + 1) (extra + 1) previous events request saved depth pending
  · exact FirstSuccessRecursiveExecution.Checked.Scheduler.grant_depth_read dispatch policy price
      (later + 1) (extra + 1) previous events request saved depth pending

/-- Independent covered source evidence completes a validated current-world
resumption of the scoped worker. The closed-annotation hypothesis is the exact
source family already proved by scoped adequacy; schematic annotations are not
silently included. Open caller bindings and covered fresh equation instances
remain those of the independent source derivation. -/
theorem scoped_source_resume_completed
    (captured : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size)
    (actions : List (OrderedDependencyStore.Action Atom size)) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)]
    {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : FirstSuccessSourceExecution.AtomDerivation
      (comparison := comparison) space live value expected incoming fuel results)
    (covered : derivation.Covered) (closed : FirstSuccessScopedAdequacy.ClosedTypeAnnotations space)
    (price : Configuration → Nat) (earned : ResultSet) (first : Nat) (before : ResultSet) (saved : Configuration)
    (lawful : OrderedDependencyStore.ObserverInvariant captured.store)
    (loaded : space = ⟨OrderedDependencyStore.query captured.store reader⟩)
    (paused : EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none
        FirstSuccessRecursiveExecution.scopedTypes)
      (FirstSuccessRecursiveExecution.Checked.Scheduler.visit GroundedDispatch.none
        FirstSuccessRecursiveExecution.scopedTypes price first
          ⟨space, .work (.atom value expected incoming fuel live), [], earned⟩).2 =
      (before, .exhausted saved))
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute captured.store actions)
      (OrderedDependencyStore.readStamp captured.store reader) = true)
    (allowed : FrameUpdate point.authority required) :
    let previous := FirstSuccessRecursiveExecution.Checked.Scheduler.visit GroundedDispatch.none
      FirstSuccessRecursiveExecution.scopedTypes price first
        ⟨space, .work (.atom value expected incoming fuel live), [], earned⟩
    let current : Cursor.ReadOnlyQuery.OwnWrite.State authority Atom size :=
      ⟨OrderedDependencyStore.execute captured.store actions, point⟩
    ∃ budget actual,
      resume authority captured current reader required GroundedDispatch.none
        FirstSuccessRecursiveExecution.scopedTypes price budget previous = .ok actual ∧
      saved.space = ⟨OrderedDependencyStore.query current.store reader⟩ ∧
      EventCursor.read (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none
        FirstSuccessRecursiveExecution.scopedTypes) actual.2 =
        (results, .finished ⟨space, .returning [], [], earned ++ results⟩) ∧
      actual.1 = previous.1 + (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none
        FirstSuccessRecursiveExecution.scopedTypes).spent price budget saved := by
  have pausedRun := paused
  rw [FirstSuccessRecursiveExecution.Checked.Scheduler.visit_read] at pausedRun
  obtain ⟨budget, after, suffix, history⟩ :=
    FirstSuccessScopedAdequacy.AtomDerivation.scoped_resume_completed derivation covered closed
      earned first before saved pausedRun
  cases budget with
  | zero => simp [Machine.run] at suffix
  | succ budget =>
      obtain ⟨actual, admitted, currentView, account, readout⟩ :=
        resume_reached_cut authority captured actions reader point required GroundedDispatch.none
          FirstSuccessRecursiveExecution.scopedTypes price first budget
          ⟨space, .work (.atom value expected incoming fuel live), [], earned⟩ saved before
          lawful loaded pausedRun valid allowed
      refine ⟨budget + 1, actual, admitted, currentView, ?_, account⟩
      simpa only [suffix, history] using readout

namespace Controls

open Mettapedia.GSLT.SeparationAlgebra

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

private def decision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (Access.consume : revocationWorlds.Fibre point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

def held : IndexedAuthority.Point revocationWorlds := ⟨false, .consume⟩
def revoked : IndexedAuthority.Point revocationWorlds :=
  IndexedAuthority.push held (homOfLE (by decide) : false ⟶ true)

def captured : Cursor.ReadOnlyQuery.OwnWrite.State revocationWorlds Atom 2 :=
  ⟨OrderedDependencyStore.initial 151 (fun _ => []), held⟩

def unrelated := OrderedDependencyStore.appendOwn captured.store 1 [.symbol "New"]
def changed := OrderedDependencyStore.appendOwn captured.store 0 [.symbol "New"]

def initial : Configuration :=
  ⟨Space.empty, .returning [(.symbol "Kept", Bindings.empty), (.symbol "Kept", Bindings.empty)], [], [(.symbol "Earlier", Bindings.empty)]⟩

def price (_ : Configuration) : Nat := 1

def pausedCursor := FirstSuccessRecursiveExecution.Checked.Scheduler.visit GroundedDispatch.none
  FirstSuccessRecursiveExecution.scopedTypes price 1 initial

def continueCurrent (live : OrderedDependencyStore.Store Atom 2)
    (point : IndexedAuthority.Point revocationWorlds) (budget : Nat)
    (previous : Saved GroundedDispatch.none FirstSuccessRecursiveExecution.scopedTypes) (extra : Nat := 0) :=
  letI := decision point
  resume revocationWorlds captured ⟨live, point⟩ 0 Access.consume GroundedDispatch.none
    FirstSuccessRecursiveExecution.scopedTypes price budget previous extra

def continued := Cursor.resume
  (EventCursor.provider (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none
    FirstSuccessRecursiveExecution.scopedTypes)) EventCursor.client
  (EventCursor.charge (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none
    FirstSuccessRecursiveExecution.scopedTypes) price) 2 pausedCursor

theorem prefix_has_actual_saved_work :
    pausedCursor.1 = 1 ∧ EventCursor.read
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none FirstSuccessRecursiveExecution.scopedTypes)
      pausedCursor.2 = ([ (.symbol "Kept", Bindings.empty) ], .exhausted
        ⟨Space.empty, .returning [(.symbol "Kept", Bindings.empty)], [],
          [(.symbol "Earlier", Bindings.empty), (.symbol "Kept", Bindings.empty)]⟩) := ⟨rfl, rfl⟩

/-- An unrelated edit admits the actual saved suffix. Earlier publications
stay retained and the two equal answer occurrences both survive. -/
theorem unrelated_edit_keeps_duplicate_occurrences :
    OrderedDependencyStore.checkRead unrelated (OrderedDependencyStore.readStamp captured.store 0) = true ∧
      continueCurrent unrelated held 2 pausedCursor = .ok continued ∧ continued.1 = 3 ∧
      EventCursor.read
        (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none FirstSuccessRecursiveExecution.scopedTypes)
        continued.2 =
        ([ (.symbol "Kept", Bindings.empty), (.symbol "Kept", Bindings.empty) ], .finished
          ⟨Space.empty, .returning [], [],
            [(.symbol "Earlier", Bindings.empty), (.symbol "Kept", Bindings.empty), (.symbol "Kept", Bindings.empty)]⟩) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem changed_source_retains_the_whole_paid_cut :
    OrderedDependencyStore.checkRead changed (OrderedDependencyStore.readStamp captured.store 0) = false ∧
      continueCurrent changed held 2 pausedCursor = .error pausedCursor := ⟨rfl, rfl⟩

theorem revocation_refuses_even_when_source_is_current :
    OrderedDependencyStore.checkRead captured.store (OrderedDependencyStore.readStamp captured.store 0) = true ∧
      continueCurrent captured.store revoked 2 pausedCursor = .error pausedCursor := ⟨rfl, rfl⟩

theorem earned_completion_survives_later_revocation :
    continueCurrent changed revoked 20 continued = .ok continued := rfl

def depthInitial : Configuration :=
  ⟨Space.empty, .work (.atom (.symbol "Kept") Atom.atomType Bindings.empty 0 []), [],
    [(.symbol "Earlier", Bindings.empty)]⟩

def depthCursor := FirstSuccessRecursiveExecution.Checked.Scheduler.visit GroundedDispatch.none
  FirstSuccessRecursiveExecution.scopedTypes price 1 depthInitial

def depthContinued := FirstSuccessRecursiveExecution.Checked.Scheduler.grant GroundedDispatch.none
  FirstSuccessRecursiveExecution.scopedTypes price 32 8 depthCursor

theorem actual_depth_request_is_not_completed_failure :
    depthCursor.1 = 1 ∧ EventCursor.read
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none FirstSuccessRecursiveExecution.scopedTypes)
      depthCursor.2 = ([], .suspended .evaluationDepth depthInitial) := ⟨rfl, rfl⟩

theorem depth_grant_uses_current_source_and_right :
    continueCurrent unrelated held 32 depthCursor 8 = .ok depthContinued ∧
      EventCursor.read
        (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none FirstSuccessRecursiveExecution.scopedTypes)
        depthContinued.2 =
        ([ (.symbol "Kept", Bindings.empty) ], .finished
          ⟨Space.empty, .returning [], [],
            [(.symbol "Earlier", Bindings.empty), (.symbol "Kept", Bindings.empty)]⟩) ∧
      continueCurrent changed held 32 depthCursor 8 = .error depthCursor ∧
      continueCurrent captured.store revoked 32 depthCursor 8 = .error depthCursor :=
  ⟨rfl, rfl, rfl, rfl⟩

end Controls

end CheckedAdmission

end Mettapedia.Languages.MeTTa.HE.RecursiveService

namespace Mettapedia.Languages.MeTTa.HE.RecursiveService.AuthorizedAppend

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open Mettapedia.Machines
open Mettapedia.Machines.Cursor
open Mettapedia.Machines.Cursor.ReadOnlyQuery
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open _root_.CategoryTheory

variable {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
  (authority : IndexedAuthority.{0,0,0} AuthorityWorld) {size : Nat}
  (required : OrderedDependencyStore.Action Atom size → (world : AuthorityWorld) → authority.Fibre world)

/-- One declared host operation uses the existing action's safety and update
judgments. The argument is stored as data, and its source frame is retained.
Permission is current eligibility; this profile does not consume a grant. -/
def services : WorldServices (Fin size) (OwnWrite.State authority Atom size) where
  contextPayload := fun reader => GroundedValue.int (Int.ofNat reader.val)
  nativeCall := fun reader before name function argument frame results after =>
    name = .symbol "indexed-space" ∧ function = .symbol "append" ∧
      (OwnWrite.action authority required (.write (.append reader [argument]))).Safe before ∧
      (OwnWrite.action authority required (.write (.append reader [argument]))).Step before () after ∧
      results = [(.symbol "ack",frame)]

def environment (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) :
    WorldEnvironment (Fin size) (OwnWrite.State authority Atom size) where
  view := fun state reader => ⟨OrderedDependencyStore.query state.store reader⟩
  services := services authority required
  dispatch := dispatch
  lookup := lookup

def instruction (argument : Atom) : Entry.Value :=
  .expression .active [.symbol "call-native",.symbol "indexed-space",.symbol "append",Entry.Value.ofAtom argument]

/-- The same primitive request is executed by the existing shared cursor.
Its reply-selected continuation contains only the earned acknowledgment. -/
def program (reader : Fin size) (argument : Atom) :
    Prog (OwnWrite.Request Atom size) OwnWrite.Reply Unit :=
  .call (.write (.append reader [argument])) (fun _ => .ret ())

theorem native_call_iff (reader : Fin size) (before after : OwnWrite.State authority Atom size)
    (argument : Atom) (frame : Frame) :
    (services authority required).nativeCall reader before (.symbol "indexed-space") (.symbol "append")
        argument frame [(.symbol "ack",frame)] after ↔
      FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world) ∧
        after = {before with store := OrderedDependencyStore.appendOwn before.store reader [argument]} := by
  simp [services,OwnWrite.action,OrderedDependencyStore.step]

/-- An authorized current-store action supplies independent source evidence
for the actual native instruction. No evaluator correspondence is assumed. -/
theorem source_operation (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (reader : Fin size) (before : OwnWrite.State authority Atom size)
    (argument : Atom) (frame : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (allowed : FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    Completed.Stateful.MinimalRel (environment authority required dispatch lookup) reader before live scope caller
      (instruction argument) frame [(.symbol "ack",frame)]
      {before with store := OrderedDependencyStore.appendOwn before.store reader [argument]} (policy := policy) := by
  apply Completed.Stateful.MinimalRel.native
  change (services authority required).nativeCall reader before _ _ _ frame _ _
  simpa only [Entry.Value.erase_ofAtom,Entry.Value.erase] using
    (native_call_iff authority required reader before _ argument frame).mpr ⟨allowed,rfl⟩

/-- Inverting the independent instruction judgment fixes the reply and the
entire reached world. The data rule cannot bypass this native instruction. -/
theorem source_completion_iff (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (reader : Fin size) (before after : OwnWrite.State authority Atom size)
    (argument : Atom) (frame : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (results : List Result) :
    Completed.Stateful.MinimalRel (environment authority required dispatch lookup) reader before live scope caller
      (instruction argument) frame results after (policy := policy) ↔
      FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world) ∧
        results = [(.symbol "ack",frame)] ∧
        after = {before with store := OrderedDependencyStore.appendOwn before.store reader [argument]} := by
  constructor
  · intro completed
    generalize hCode : instruction argument = code at completed
    cases completed <;> simp [instruction] at hCode
    case data plain =>
      subst code
      simp [Entry.Value.erase,Minimal.embeddedInstruction] at plain
    case native operation =>
      obtain ⟨rfl,rfl,rfl,rfl⟩ := hCode
      change (services authority required).nativeCall reader before _ _ _ frame results after at operation
      simp only [Entry.Value.erase_ofAtom,Entry.Value.erase,services] at operation
      obtain ⟨_,_,allowed,moved,reply⟩ := operation
      exact ⟨allowed,reply,by simpa [OwnWrite.action,OrderedDependencyStore.step] using moved⟩
  · rintro ⟨allowed,rfl,rfl⟩
    exact source_operation authority required dispatch lookup policy reader before argument frame live scope caller allowed

/-- Denied authority excludes every completed source result for this
instruction, including a fabricated successful or empty answer batch. -/
theorem denied_source_instruction (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (reader : Fin size) (before after : OwnWrite.State authority Atom size)
    (argument : Atom) (frame : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (results : List Result)
    (denied : ¬FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    ¬Completed.Stateful.MinimalRel (environment authority required dispatch lookup) reader before live scope caller
      (instruction argument) frame results after (policy := policy) :=
  fun completed => denied ((source_completion_iff authority required dispatch lookup policy reader before after
    argument frame live scope caller results).mp completed).1

/-- The local operation enters the existing world machine under arbitrary
saved callers and prior occurrences. Its one logical step may have a
different service cost from its implementation. -/
theorem machine_operation (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (reader : Fin size) (before : OwnWrite.State authority Atom size)
    (argument : Atom) (frame : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (stack : List Continuation) (emitted : List Result)
    (allowed : FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    RecursiveExecution.Contextual.Stateful.Protocol.Rule (environment authority required dispatch lookup) policy
      ⟨before,reader,.work (.minimal live scope caller (instruction argument) frame),stack,emitted⟩
      (some (.silent ⟨{before with store := OrderedDependencyStore.appendOwn before.store reader [argument]},
        reader,.returning [(.symbol "ack",frame)],stack,emitted⟩)) := by
  apply RecursiveExecution.Contextual.Stateful.Protocol.Rule.internal
  apply WorldLocalStep.native
  change (services authority required).nativeCall reader before _ _ _ frame _ _
  simpa only [Entry.Value.erase_ofAtom,Entry.Value.erase] using
    (native_call_iff authority required reader before _ argument frame).mpr ⟨allowed,rfl⟩

theorem denied_has_no_source_completion (reader : Fin size) (before after : OwnWrite.State authority Atom size)
    (argument : Atom) (frame : Frame)
    (denied : ¬FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    ¬(services authority required).nativeCall reader before (.symbol "indexed-space") (.symbol "append")
      argument frame [(.symbol "ack",frame)] after :=
  fun operation => denied ((native_call_iff authority required reader before after argument frame).mp operation).1

variable [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Atom size),
  Decidable (FrameUpdate point.authority (required action point.world))]

/-- One provider request performs the write and retains the return
continuation. The committed world is already present at this pause. -/
theorem service_prefix (reader : Fin size) (before : OwnWrite.State authority Atom size) (argument : Atom)
    (allowed : FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    let saved := OwnWrite.advance authority required 1 (program reader argument) before
    (saved.1,PrimitiveProgram.readOutcome (OwnWrite.step authority required) saved.2) =
      (1,Sum.inr (.ok (.ret ())),
        {before with store := OrderedDependencyStore.appendOwn before.store reader [argument]}) := by
  simpa [program,PrimitiveProgram.direct,OwnWrite.step,allowed,OrderedDependencyStore.step] using
    OwnWrite.finite_is_direct authority required 1 (program reader argument) before

theorem service_completed (reader : Fin size) (before : OwnWrite.State authority Atom size) (argument : Atom)
    (allowed : FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    let saved := OwnWrite.advance authority required 2 (program reader argument) before
    (saved.1,PrimitiveProgram.readOutcome (OwnWrite.step authority required) saved.2) =
      (1,Sum.inl (.ok ()),
        {before with store := OrderedDependencyStore.appendOwn before.store reader [argument]}) := by
  simpa [program,PrimitiveProgram.direct,OwnWrite.step,allowed,OrderedDependencyStore.step] using
    OwnWrite.finite_is_direct authority required 2 (program reader argument) before

/-- Resuming the actual post-write packet completes its return without
issuing the write again. The account still contains one provider request. -/
theorem service_resume_after_write (reader : Fin size) (before : OwnWrite.State authority Atom size) (argument : Atom)
    (allowed : FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    let saved := Cursor.resume (OwnWrite.provider authority required) (OwnWrite.client Unit) (fun _ _ => 1) 1
      (OwnWrite.advance authority required 1 (program reader argument) before)
    (saved.1,PrimitiveProgram.readOutcome (OwnWrite.step authority required) saved.2) =
      (1,Sum.inl (.ok ()),
        {before with store := OrderedDependencyStore.appendOwn before.store reader [argument]}) := by
  have split := OwnWrite.split_resume authority required 1 1 (program reader argument) before
  dsimp only
  rw [←split]
  exact service_completed authority required reader before argument allowed

/-- A refused current permission produces an explicit service fault and
leaves the actual store intact. It is not a successful language answer. -/
theorem service_denied (reader : Fin size) (before : OwnWrite.State authority Atom size) (argument : Atom)
    (denied : ¬FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    let saved := OwnWrite.advance authority required 2 (program reader argument) before
    (saved.1,PrimitiveProgram.readOutcome (OwnWrite.step authority required) saved.2) =
      (1,Sum.inl (.error .denied),before) := by
  simpa [program,PrimitiveProgram.direct,OwnWrite.step,denied] using
    OwnWrite.finite_is_direct authority required 2 (program reader argument) before

/-- The constructed local refinement square: one source operation and one
logical world step are realized by the actual permission-checked provider,
including its post-write pause and subsequent return. The caller and prior
history are arbitrary, and the reached world is a conclusion. -/
theorem operation_refinement_square (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (reader : Fin size) (before : OwnWrite.State authority Atom size)
    (argument : Atom) (frame : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (stack : List Continuation) (emitted : List Result)
    (allowed : FrameUpdate before.point.authority (required (.append reader [argument]) before.point.world)) :
    ∃ after : OwnWrite.State authority Atom size,
      Completed.Stateful.MinimalRel (environment authority required dispatch lookup) reader before live scope caller
        (instruction argument) frame [(.symbol "ack",frame)] after (policy := policy) ∧
      RecursiveExecution.Contextual.Stateful.Protocol.Rule (environment authority required dispatch lookup) policy
        ⟨before,reader,.work (.minimal live scope caller (instruction argument) frame),stack,emitted⟩
        (some (.silent ⟨after,reader,.returning [(.symbol "ack",frame)],stack,emitted⟩)) ∧
      (let saved := OwnWrite.advance authority required 1 (program reader argument) before
       (saved.1,PrimitiveProgram.readOutcome (OwnWrite.step authority required) saved.2) =
        (1,Sum.inr (.ok (.ret ())),after)) ∧
      (let saved := Cursor.resume (OwnWrite.provider authority required) (OwnWrite.client Unit) (fun _ _ => 1) 1
        (OwnWrite.advance authority required 1 (program reader argument) before)
       (saved.1,PrimitiveProgram.readOutcome (OwnWrite.step authority required) saved.2) =
        (1,Sum.inl (.ok ()),after)) := by
  exact ⟨_,source_operation authority required dispatch lookup policy reader before argument frame live scope caller allowed,
    machine_operation authority required dispatch lookup policy reader before argument frame live scope caller stack emitted allowed,
    service_prefix authority required reader before argument allowed,
    service_resume_after_write authority required reader before argument allowed⟩

namespace Retained

abbrev World := OwnWrite.State authority Atom size
abbrev Configuration := WorldConfiguration (Fin size) (World authority (size := size))

/-- The native operation captures the reached world and frame, rather than
reloading the original language query when its provider returns. -/
structure Request where
  world : World authority (size := size)
  reader : Fin size
  argument : Atom
  frame : Frame

abbrev Value := World authority (size := size) × List Result
abbrev Failure := World authority (size := size) × OwnWrite.Fault
abbrev Response := Reply (Value authority (size := size)) (Failure authority (size := size))

/-- A boundary service returns a retained HE configuration, not a completed
language answer. The caller's stack and earlier publications remain present. -/
inductive Parent where
  | enter (configuration : Configuration authority (size := size))
  | replied (configuration : Configuration authority (size := size))
      (response : Response authority (size := size))

abbrev Packet := Cursor.Packet (OwnWrite.provider authority required)
  (OwnWrite.client (List Result)) PUnit.unit
abbrev Receipt := Cursor.ProductiveBlocks.Receipt (OwnWrite.provider authority required) PUnit.unit

inductive Event where
  | requested (request : Request authority (size := size))
  | performed (receipt : Receipt authority required)
  | replied (response : Response authority (size := size))

/-- The existing primitive program supplies the reply-dependent continuation.
The acknowledgement carries the exact input activation. -/
def replyProgram (request : Request authority (size := size)) :
    Prog (OwnWrite.Request Atom size) OwnWrite.Reply (List Result) :=
  (program request.reader request.argument).bind fun _ => .ret [(.symbol "ack",request.frame)]

def load (request : Request authority (size := size)) : Packet authority required :=
  ⟨PUnit.unit,.ok (replyProgram authority request),request.world⟩

def response : Cursor.Finished (OwnWrite.provider authority required)
    (Return := fun _ _ => Except OwnWrite.Fault (List Result)) PUnit.unit →
      Response authority (size := size)
  | ⟨_,.ok results,world⟩ => .returned (world,results)
  | ⟨_,.error fault,world⟩ => .faulted (world,fault)

/-- Only the existing cursor executes provider operations. This adapter adds
no evaluation loop and retains the full world on both success and denial. -/
def service : Machine (Packet authority required) (Event authority required)
    (Response authority (size := size)) Empty :=
  (Cursor.ProductiveBlocks.machine (OwnWrite.provider authority required)
    (OwnWrite.client (List Result)) PUnit.unit).relabel Event.performed
      (response authority required) id

/-- A service site follows retained operational contexts, never arbitrary
positions in a term. Each context retains its own label and caller stack. -/
inductive Site (world : World authority (size := size)) :
    Fin size → Control (Fin size) → Request authority (size := size) → Prop where
  | native {reader live scope caller readiness argument frame} :
      Site world reader (.work (.minimal live scope caller (.expression readiness
        [.symbol "call-native",.symbol "indexed-space",.symbol "append",argument]) frame))
        ⟨world,reader,argument.erase,frame⟩
  | context {reader childLabel child inner request} :
      Site world childLabel child request →
      Site world reader (.context childLabel child inner) request

/-- Recognition earns the operational-site witness while following the
already selected context chain. It performs no language evaluation. -/
def locate (world : World authority (size := size)) (reader : Fin size) :
    (control : Control (Fin size)) →
      Option {request : Request authority (size := size) // Site authority world reader control request}
  | .work (.minimal _ _ _ (.expression _
      [.symbol "call-native",.symbol "indexed-space",.symbol "append",argument]) frame) =>
    some ⟨⟨world,reader,argument.erase,frame⟩,.native⟩
  | .context childLabel child _inner =>
    (locate world childLabel child).map fun found => ⟨found.1,.context found.2⟩
  | _ => none

def requested? (configuration : Configuration authority (size := size)) :
    Option (Request authority (size := size)) :=
  (locate authority configuration.world configuration.context configuration.control).map Subtype.val

/-- Only the selected focus receives the reply. All enclosing operational
contexts and their independently retained caller stacks remain intact. -/
def deliver (control : Control (Fin size)) (results : List Result) : Control (Fin size) :=
  match control with
  | .context label child inner => .context label (deliver child results) inner
  | _ => .returning results

theorem requested_site {configuration : Configuration authority (size := size)}
    {request : Request authority (size := size)}
    (found : requested? authority configuration = some request) :
    Site authority configuration.world configuration.context configuration.control request := by
  unfold requested? at found
  cases situated : locate authority configuration.world configuration.context configuration.control with
  | none => simp only [situated,Option.map_none] at found; cases found
  | some located =>
    simp only [situated,Option.map_some,Option.some.injEq] at found
    cases found
    exact located.2

omit permission in
theorem Site.world_eq {world : World authority (size := size)}
    {reader : Fin size} {control : Control (Fin size)} {request : Request authority (size := size)}
    (site : Site authority world reader control request) : request.world = world := by
  induction site with
  | native => rfl
  | context _ ih => exact ih

omit permission in
/-- Changing the world preserves a selected operational site. The retained
contexts, argument and activation are not reconstructed from source syntax. -/
theorem Site.rebase {world : World authority (size := size)}
    {reader : Fin size} {control : Control (Fin size)} {request : Request authority (size := size)}
    (site : Site authority world reader control request) (current : World authority (size := size)) :
    Site authority current reader control {request with world := current} := by
  induction site with
  | native => exact .native
  | context _ ih => exact .context ih

omit permission in
theorem Site.located {world : World authority (size := size)}
    {reader : Fin size} {control : Control (Fin size)} {request : Request authority (size := size)}
    (site : Site authority world reader control request) :
    (locate authority world reader control).map Subtype.val = some request := by
  induction site with
  | native => rfl
  | context _ ih => simpa only [locate,Option.map_map,Function.comp_def] using ih

omit permission in
/-- Recognition of the rebased request follows the existing context chain;
it is earned from the old site's source-structural witness. -/
theorem requested_rebase {configuration : Configuration authority (size := size)}
    {request : Request authority (size := size)}
    (found : requested? authority configuration = some request)
    (current : World authority (size := size)) :
    requested? authority {configuration with world := current} =
      some {request with world := current} :=
  ((requested_site authority found).rebase authority current).located authority

omit permission in
/-- Independent source authorization licenses the selected local operation
under every retained context and arbitrary enclosing callers. -/
theorem Site.world_step (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    {world reader control request} (site : Site authority world reader control request)
    (stack : List Continuation)
    (allowed : FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)) :
    WorldLocalStep (environment authority required dispatch lookup).view
      (environment authority required dispatch lookup).services dispatch lookup policy
      world reader (control,stack)
      {request.world with store := OrderedDependencyStore.appendOwn request.world.store request.reader [request.argument]}
      (deliver control [(.symbol "ack",request.frame)],stack) := by
  induction site generalizing stack with
  | @native reader live scope caller readiness argument frame =>
    apply WorldLocalStep.native
    change (services authority required).nativeCall _ _ _ _ _ _ _ _
    simpa only [Entry.Value.erase] using
      (native_call_iff authority required reader world _ argument.erase frame).mpr ⟨allowed,rfl⟩
  | context site ih => exact WorldLocalStep.context (ih _ allowed)

def reachedWorld (request : Request authority (size := size)) : World authority (size := size) :=
  {request.world with store := OrderedDependencyStore.appendOwn request.world.store request.reader [request.argument]}

def deliverConfiguration (configuration : Configuration authority (size := size))
    (world : World authority (size := size)) (results : List Result) : Configuration authority (size := size) :=
  {configuration with world,control := deliver configuration.control results}

def finish (configuration : Configuration authority (size := size)) :
    Response authority (size := size) →
      Reply (Configuration authority (size := size)) (Failure authority (size := size))
  | .returned (world,results) => .returned (deliverConfiguration authority configuration world results)
  | .faulted failure => .faulted failure
  | .cancelled => .cancelled

def parent : Machine (Parent authority (size := size)) (Event authority required)
    (Reply (Configuration authority (size := size)) (Failure authority (size := size)))
    (Request authority (size := size)) where
  step
    | .enter configuration =>
      (requested? authority configuration).map fun request => .call request (.enter configuration)
    | .replied configuration reply => some (.finish (finish authority configuration reply))

def callback : Callback (Parent authority (size := size)) (Event authority required)
    (Request authority (size := size)) (Value authority (size := size))
    (Failure authority (size := size)) where
  callEvent := .requested
  replyEvent := .replied
  resume
    | .enter configuration,reply | .replied configuration _,reply => .replied configuration reply

def handled : Machine
    (HandledState (Parent authority (size := size)) (Packet authority required)
      (Request authority (size := size)))
    (Event authority required)
    (Reply (Configuration authority (size := size)) (Failure authority (size := size))) Empty :=
  (parent authority required).handle (callback authority required)
    (service authority required) (load authority required)

private theorem service_request_step (request : Request authority (size := size)) :
    let actual := OwnWrite.step authority required request.world
      (.write (.append request.reader [request.argument]))
    (service authority required).step (load authority required request) =
      some (.publish
        [.performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),actual.2⟩]
        ⟨PUnit.unit,(match actual.2 with
          | .ok _ => .ok (.ret [(.symbol "ack",request.frame)])
          | .error fault => .error fault),actual.1⟩) := by
  have exposed : (OwnWrite.client (Entry := Atom) (size := size) (List Result)).str
      PUnit.unit PUnit.unit (.ok (replyProgram authority request)) =
      ⟨.inr (.write (.append request.reader [request.argument])),fun reply => match reply with
        | .error fault => .error fault
        | .ok _ => .ok (.ret [(.symbol "ack",request.frame)])⟩ := by
          dsimp only [OwnWrite.client,PrimitiveProgram.client,replyProgram,program,Prog.bind]
          refine Sigma.ext ?_ ?_
          · rfl
          · apply heq_of_eq
            funext reply
            cases reply with
            | error fault => rfl
            | ok value => cases value; rfl
  simp only [service,Machine.relabel,Cursor.ProductiveBlocks.machine,load,exposed,
    Option.map_some,Transition.relabel,List.map_cons,List.map_nil]
  cases reply : (OwnWrite.step authority required request.world
    (.write (.append request.reader [request.argument]))).2 <;> rfl

private theorem service_terminal_step (world : World authority (size := size))
    (answer : Except OwnWrite.Fault (List Result)) :
    (service authority required).step ⟨PUnit.unit,answer.map Prog.ret,world⟩ =
      some (.finish (match answer with
        | .ok results => .returned (world,results)
        | .error fault => .faulted (world,fault))) := by
  cases answer <;> rfl

/-- The post-write cut holds the real cursor's selected return continuation.
There is no completed reply or second provider request at this point. -/
theorem service_post_write (request : Request authority (size := size))
    (allowed : FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)) :
    let after := reachedWorld authority request
    (service authority required).run 1 (load authority required request) =
      ([Event.performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),.ok ()⟩],
        .exhausted ⟨PUnit.unit,.ok (.ret [(.symbol "ack",request.frame)]),after⟩) := by
  have moved := service_request_step authority required request
  simp only [OwnWrite.step,if_pos allowed,OrderedDependencyStore.step] at moved
  rw [(service authority required).run_succ_publish moved]
  rfl

theorem service_completed (request : Request authority (size := size))
    (allowed : FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)) :
    let after := {request.world with store :=
      OrderedDependencyStore.appendOwn request.world.store request.reader [request.argument]}
    (service authority required).run 2 (load authority required request) =
      ([Event.performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),.ok ()⟩],
        .finished (.returned (after,[(.symbol "ack",request.frame)]))) := by
  have moved := service_request_step authority required request
  simp only [OwnWrite.step,if_pos allowed,OrderedDependencyStore.step] at moved
  rw [(service authority required).run_succ_publish moved]
  have terminal := service_terminal_step authority required
    {request.world with store := OrderedDependencyStore.appendOwn request.world.store request.reader [request.argument]}
    (.ok [(.symbol "ack",request.frame)])
  simp only [Except.map] at terminal
  rw [(service authority required).run_succ_finish terminal]
  rfl

/-- Denial is a completed service fault with the unchanged provider world,
not an empty successful language batch. -/
theorem service_denied (request : Request authority (size := size))
    (denied : ¬FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)) :
    (service authority required).run 2 (load authority required request) =
      ([Event.performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),
        .error .denied⟩], .finished (.faulted (request.world,.denied))) := by
  have moved := service_request_step authority required request
  simp only [OwnWrite.step,if_neg denied] at moved
  rw [(service authority required).run_succ_publish moved]
  have terminal := service_terminal_step authority required request.world (.error .denied)
  simp only [Except.map] at terminal
  rw [(service authority required).run_succ_finish terminal]
  rfl

/-- The closed operation account is defined from the same primitive provider,
including its denial result. Independent source authorization is proved
separately by `source_operation` and `denied_source_instruction`. -/
def responses : Environment (Request authority (size := size)) (Event authority required)
    (Value authority (size := size)) (Failure authority (size := size)) := fun request =>
  let actual := OwnWrite.step authority required request.world
    (.write (.append request.reader [request.argument]))
  ([.performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),actual.2⟩],
    match actual.2 with
    | .ok () => .returned (actual.1,[(.symbol "ack",request.frame)])
    | .error fault => .faulted (actual.1,fault))

theorem service_responses (request : Request authority (size := size)) :
    (service authority required).run 2 (load authority required request) =
      ((responses authority required request).1,.finished (responses authority required request).2) := by
  by_cases allowed : FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)
  · simpa [responses,OwnWrite.step,allowed,OrderedDependencyStore.step] using
      service_completed authority required request allowed
  · simpa [responses,OwnWrite.step,allowed] using service_denied authority required request allowed

/-- The standard callback refinement now has a constructed service instance;
no completed child run is supplied as an interface hypothesis. -/
theorem close_handle_simulation :
    CostSimulation ((parent authority required).close (callback authority required) (responses authority required))
      (handled authority required) (fun state retained => retained = .running state) 3 :=
  (parent authority required).close_handle_costSimulation (callback authority required)
    (load authority required) (service authority required) (responses authority required) 2
    (service_responses authority required)

theorem close_handle_stuck :
    MatchesStuck ((parent authority required).close (callback authority required) (responses authority required))
      (handled authority required) (fun state retained => retained = .running state) 3 :=
  (parent authority required).close_handle_matchesStuck (callback authority required)
    (load authority required) (service authority required) (responses authority required) 2

private theorem enter_step (configuration : Configuration authority (size := size))
    (request : Request authority (size := size))
    (found : requested? authority configuration = some request) :
    (handled authority required).step (.running (.enter configuration)) =
      some (.publish [.requested request]
        (.handling request (.enter configuration) (load authority required request))) := by
  simp only [handled,Machine.handle,parent,found,Option.map_some,callback]

/-- A call and its one actual write retain the updated provider packet
inside the original caller. No language reply has been published yet. -/
theorem handled_post_write (configuration : Configuration authority (size := size))
    (request : Request authority (size := size))
    (found : requested? authority configuration = some request)
    (allowed : FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)) :
    let after := {request.world with store :=
      OrderedDependencyStore.appendOwn request.world.store request.reader [request.argument]}
    (handled authority required).run 2 (.running (.enter configuration)) =
      ([.requested request,
        .performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),.ok ()⟩],
        .exhausted (.handling request (.enter configuration)
          ⟨PUnit.unit,.ok (.ret [(.symbol "ack",request.frame)]),after⟩)) := by
  have moved := service_request_step authority required request
  simp only [OwnWrite.step,if_pos allowed,OrderedDependencyStore.step] at moved
  have written : (handled authority required).step
      (.handling request (.enter configuration) (load authority required request)) =
      some (.publish
        [.performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),.ok ()⟩]
        (.handling request (.enter configuration)
          ⟨PUnit.unit,.ok (.ret [(.symbol "ack",request.frame)]),reachedWorld authority request⟩)) := by
    simp only [handled,Machine.handle,moved,Option.map_some,reachedWorld]
  rw [(handled authority required).run_succ_publish (enter_step authority required configuration request found),
    (handled authority required).run_succ_publish written]
  rfl

/-- The saved post-write packet only returns and reinstalls its caller.
The suffix has no performed-operation occurrence and does not recheck or
repeat the already completed write. -/
theorem handled_resume_after_write (configuration : Configuration authority (size := size))
    (request : Request authority (size := size)) (world : World authority (size := size)) :
    (handled authority required).run 2
      (.handling request (.enter configuration)
        ⟨PUnit.unit,.ok (.ret [(.symbol "ack",request.frame)]),world⟩) =
      ([.replied (.returned (world,[(.symbol "ack",request.frame)]))],
        .finished (.returned (deliverConfiguration authority configuration world [(.symbol "ack",request.frame)]))) := by
  have terminal := service_terminal_step authority required world (.ok [(.symbol "ack",request.frame)])
  simp only [Except.map] at terminal
  have replying : (handled authority required).step
      (.handling request (.enter configuration)
        ⟨PUnit.unit,.ok (.ret [(.symbol "ack",request.frame)]),world⟩) =
      some (.publish [.replied (.returned (world,[(.symbol "ack",request.frame)]))]
        (.running (.replied configuration (.returned (world,[(.symbol "ack",request.frame)]))))) := by
    simp only [handled,Machine.handle,terminal,Option.map_some,callback]
  have returned : (handled authority required).step
      (.running (.replied configuration (.returned (world,[(.symbol "ack",request.frame)])))) =
      some (.finish (.returned (deliverConfiguration authority configuration world [(.symbol "ack",request.frame)]))) := rfl
  rw [(handled authority required).run_succ_publish replying,
    (handled authority required).run_succ_finish returned]
  rfl

theorem handled_completed (configuration : Configuration authority (size := size))
    (request : Request authority (size := size))
    (found : requested? authority configuration = some request)
    (allowed : FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)) :
    let after := reachedWorld authority request
    (handled authority required).run 4 (.running (.enter configuration)) =
      ([.requested request,
        .performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),.ok ()⟩,
        .replied (.returned (after,[(.symbol "ack",request.frame)]))],
        .finished (.returned (deliverConfiguration authority configuration after [(.symbol "ack",request.frame)]))) := by
  have paused := handled_post_write authority required configuration request found allowed
  rw [(handled authority required).established_and_pending 2 2 _ _ _ paused,
    handled_resume_after_write authority required]
  rfl

/-- The same retained service boundary returns a refusal with its unchanged
world. It does not manufacture an acknowledgement or a completed empty batch. -/
theorem handled_denied (configuration : Configuration authority (size := size))
    (request : Request authority (size := size))
    (found : requested? authority configuration = some request)
    (denied : ¬FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)) :
    (handled authority required).run 4 (.running (.enter configuration)) =
      ([.requested request,
        .performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),.error .denied⟩,
        .replied (.faulted (request.world,.denied))],.finished (.faulted (request.world,.denied))) := by
  have moved := service_request_step authority required request
  simp only [OwnWrite.step,if_neg denied] at moved
  have written : (handled authority required).step
      (.handling request (.enter configuration) (load authority required request)) =
      some (.publish
        [.performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),.error .denied⟩]
        (.handling request (.enter configuration) ⟨PUnit.unit,.error .denied,request.world⟩)) := by
    simp only [handled,Machine.handle,moved,Option.map_some]
  have terminal := service_terminal_step authority required request.world (.error .denied)
  simp only [Except.map] at terminal
  have replying : (handled authority required).step
      (.handling request (.enter configuration) ⟨PUnit.unit,.error .denied,request.world⟩) =
      some (.publish [.replied (.faulted (request.world,.denied))]
        (.running (.replied configuration (.faulted (request.world,.denied))))) := by
    simp only [handled,Machine.handle,terminal,Option.map_some,callback]
  have returned : (handled authority required).step
      (.running (.replied configuration (.faulted (request.world,.denied)))) =
      some (.finish (.faulted (request.world,.denied))) := rfl
  rw [(handled authority required).run_succ_publish (enter_step authority required configuration request found),
    (handled authority required).run_succ_publish written,
    (handled authority required).run_succ_publish replying,
    (handled authority required).run_succ_finish returned]
  rfl

/-- One independently licensed world step is realized by four service
inspections. This does not bound the work inside the provider operation.
The returned value is the retained evaluator state; its enclosing callers
and earlier publications are unchanged. -/
theorem operation_refinement (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (configuration : Configuration authority (size := size))
    (request : Request authority (size := size))
    (found : requested? authority configuration = some request)
    (allowed : FrameUpdate request.world.point.authority
      (required (.append request.reader [request.argument]) request.world.point.world)) :
    let world := reachedWorld authority request
    let next := deliverConfiguration authority configuration world [(.symbol "ack",request.frame)]
    RecursiveExecution.Contextual.Stateful.Protocol.Rule
      (environment authority required dispatch lookup) policy configuration (some (.silent next)) ∧
      (handled authority required).run 4 (.running (.enter configuration)) =
        ([.requested request,
          .performed ⟨PUnit.unit,request.world,.write (.append request.reader [request.argument]),.ok ()⟩,
          .replied (.returned (world,[(.symbol "ack",request.frame)]))],.finished (.returned next)) ∧
      next.stack = configuration.stack ∧ next.emitted = configuration.emitted ∧
      next.context = configuration.context := by
  refine ⟨?_,handled_completed authority required configuration request found allowed,rfl,rfl,rfl⟩
  exact RecursiveExecution.Contextual.Stateful.Protocol.Rule.internal
    ((requested_site authority found).world_step authority required dispatch lookup policy configuration.stack allowed)

/-- In flight, the provider's reached world is authoritative. The saved caller
still records the input world and is not used as a substitute for it.
A bare cancellation carries no reached world and has no such readout. -/
def currentWorld? : HandledState (Parent authority (size := size)) (Packet authority required)
    (Request authority (size := size)) → Option (World authority (size := size))
  | .handling _ _ packet => some packet.2.2
  | .running (.enter configuration) => some configuration.world
  | .running (.replied _ (.returned (world,_))) => some world
  | .running (.replied _ (.faulted (world,_))) => some world
  | .running (.replied _ .cancelled) => none

/-- Admit a new operation at a retained Contextual AM cut. Its dependency is
stamped in the reached world, and its operation right is checked in the
current world. Refusal retains the entire saved configuration. This is an
external-world boundary, not an evaluator transition or a restart. -/
def rebase (configuration : Configuration authority (size := size))
    (current : World authority (size := size)) :
    Except (Configuration authority (size := size)) (Configuration authority (size := size)) :=
  match requested? authority configuration with
  | none => .error configuration
  | some request =>
      if OrderedDependencyStore.checkRead current.store
          (OrderedDependencyStore.readStamp configuration.world.store request.reader) = true ∧
          FrameUpdate current.point.authority
            (required (.append request.reader [request.argument]) current.point.world) then
        .ok {configuration with world := current}
      else .error configuration

theorem rebase_admitted (configuration : Configuration authority (size := size))
    (request : Request authority (size := size)) (current : World authority (size := size))
    (found : requested? authority configuration = some request)
    (valid : OrderedDependencyStore.checkRead current.store
      (OrderedDependencyStore.readStamp configuration.world.store request.reader) = true)
    (allowed : FrameUpdate current.point.authority
      (required (.append request.reader [request.argument]) current.point.world)) :
    rebase authority required configuration current = .ok {configuration with world := current} := by
  simp only [rebase,found,valid,true_and,if_pos allowed]

theorem rebase_refused (configuration : Configuration authority (size := size))
    (request : Request authority (size := size)) (current : World authority (size := size))
    (found : requested? authority configuration = some request)
    (refused : OrderedDependencyStore.checkRead current.store
        (OrderedDependencyStore.readStamp configuration.world.store request.reader) = false ∨
      ¬FrameUpdate current.point.authority
        (required (.append request.reader [request.argument]) current.point.world)) :
    rebase authority required configuration current = .error configuration := by
  simp only [rebase,found]
  apply if_neg
  rcases refused with stale | denied
  · simp only [stale,Bool.false_eq_true,false_and,not_false_eq_true]
  · exact fun admitted => denied admitted.2

/-- Validate at the endpoint of an actual relational AM prefix, then resume
the selected operation in the current world. The update chain is external:
the theorem does not pretend it is an evaluator step. The service performs
only the newly pending write, while the old occurrence history and callers
remain in the returned configuration. No deterministic evaluator is chosen. -/
theorem validated_resume_reached_cut (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : CastLookup) (policy : Policy)
    {initial saved : Configuration authority (size := size)} {fuel : Nat} {events : List Result}
    (paused : Derivation
      (RecursiveExecution.Contextual.Stateful.Protocol.Rule
        (environment authority required dispatch lookup) policy)
      fuel initial events (.exhausted saved))
    (request : Request authority (size := size))
    (found : requested? authority saved = some request)
    (changes : List (OrderedDependencyStore.Action Atom size)) (point : IndexedAuthority.Point authority)
    (lawful : OrderedDependencyStore.ObserverInvariant saved.world.store)
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute saved.world.store changes)
      (OrderedDependencyStore.readStamp saved.world.store request.reader) = true)
    (allowed : FrameUpdate point.authority
      (required (.append request.reader [request.argument]) point.world)) :
    let current : World authority (size := size) :=
      ⟨OrderedDependencyStore.execute saved.world.store changes,point⟩
    let rebased := {saved with world := current}
    let pending := {request with world := current}
    let world := reachedWorld authority pending
    let next := deliverConfiguration authority rebased world [(.symbol "ack",request.frame)]
    rebase authority required saved current = .ok rebased ∧
      OrderedDependencyStore.query current.store request.reader =
        OrderedDependencyStore.query saved.world.store request.reader ∧
      requested? authority rebased = some pending ∧
      Derivation
        (RecursiveExecution.Contextual.Stateful.Protocol.Rule
          (environment authority required dispatch lookup) policy)
        1 rebased [] (.exhausted next) ∧
      (handled authority required).run 4 (.running (.enter rebased)) =
        ([.requested pending,
          .performed ⟨PUnit.unit,current,.write (.append request.reader [request.argument]),.ok ()⟩,
          .replied (.returned (world,[(.symbol "ack",request.frame)]))],.finished (.returned next)) ∧
      next.stack = saved.stack ∧ next.emitted = initial.emitted ++ events ∧
      next.context = saved.context := by
  dsimp only
  have currentSite := requested_rebase authority found
    (⟨OrderedDependencyStore.execute saved.world.store changes,point⟩ : World authority)
  have operation := (requested_site authority currentSite).world_step authority required
    dispatch lookup policy saved.stack allowed
  have history := (RecursiveExecution.Contextual.Stateful.Protocol.exhausted_steps paused).2
  refine ⟨rebase_admitted authority required saved request _ found valid allowed,
    OwnWrite.current_source_agrees authority saved.world changes request.reader lawful valid,
    currentSite,?_,handled_completed authority required _ _ currentSite allowed,rfl,history,rfl⟩
  exact .silent (.internal operation) (.pause _)

end Retained

end Mettapedia.Languages.MeTTa.HE.RecursiveService.AuthorizedAppend

namespace Mettapedia.Languages.MeTTa.HE.RecursiveService.CheckedAdmission.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual
open Mettapedia.Machines
open Mettapedia.Machines.Cursor.ReadOnlyQuery
open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def appendRequirement (_ : OrderedDependencyStore.Action Atom 2) (world : Bool) :
    revocationWorlds.Fibre world := Access.consume

local instance appendDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Atom 2) :
    Decidable (FrameUpdate point.authority (appendRequirement change point.world)) := decision point

private def storedData : Atom := .expression [.symbol "delayed",.var "x",.var "x"]
private def appended : OwnWrite.State revocationWorlds Atom 2 :=
  {captured with store := OrderedDependencyStore.appendOwn captured.store 0 [storedData]}

/-- The real provider and the independent native source rule agree while a
caller and an earlier publication are still retained. Raw stored syntax is
not evaluated by the append operation. -/
theorem authorized_native_append_has_source_and_retained_control
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy) :
    Completed.Stateful.MinimalRel
        (AuthorizedAppend.environment revocationWorlds appendRequirement dispatch lookup) 0 captured [] [] none
        (AuthorizedAppend.instruction storedData) Completed.Frame.empty
        [(.symbol "ack",Completed.Frame.empty)] appended (policy := policy) ∧
      RecursiveExecution.Contextual.Stateful.Protocol.Rule
        (AuthorizedAppend.environment revocationWorlds appendRequirement dispatch lookup) policy
        ⟨captured,0,.work (.minimal [] [] none (AuthorizedAppend.instruction storedData) Completed.Frame.empty),
          [.singleton],[(.symbol "earlier",Completed.Frame.empty)]⟩
        (some (.silent ⟨appended,0,.returning [(.symbol "ack",Completed.Frame.empty)],
          [.singleton],[(.symbol "earlier",Completed.Frame.empty)]⟩)) ∧
      OrderedDependencyStore.query appended.store 0 = [storedData] := by
  have allowed : FrameUpdate captured.point.authority
      (appendRequirement (.append 0 [storedData]) captured.point.world) := by decide
  exact ⟨AuthorizedAppend.source_operation revocationWorlds appendRequirement dispatch lookup policy 0 captured
      storedData Completed.Frame.empty [] [] none allowed,
    AuthorizedAppend.machine_operation revocationWorlds appendRequirement dispatch lookup policy 0 captured
      storedData Completed.Frame.empty [] [] none [.singleton] [(.symbol "earlier",Completed.Frame.empty)] allowed,rfl⟩

/-- Completing the saved return keeps one copy. Restarting the primitive
performs a second append, which is observably different. -/
theorem native_append_resume_is_not_restart :
    let resumed := Cursor.resume (OwnWrite.provider revocationWorlds appendRequirement) (OwnWrite.client Unit)
      (fun _ _ => 1) 1 (OwnWrite.advance revocationWorlds appendRequirement 1
        (AuthorizedAppend.program 0 storedData) captured)
    (resumed.1,PrimitiveProgram.readOutcome (OwnWrite.step revocationWorlds appendRequirement) resumed.2) =
      (1,Sum.inl (.ok ()),appended) ∧
      OrderedDependencyStore.query appended.store 0 = [storedData] ∧
      (let restarted := OwnWrite.advance revocationWorlds appendRequirement 2
        (AuthorizedAppend.program 0 storedData) appended
       (restarted.1,PrimitiveProgram.readOutcome (OwnWrite.step revocationWorlds appendRequirement) restarted.2) =
        (1,Sum.inl (.ok ()),{appended with store := OrderedDependencyStore.appendOwn appended.store 0 [storedData]})) ∧
      OrderedDependencyStore.query (OrderedDependencyStore.appendOwn appended.store 0 [storedData]) 0 ≠
        OrderedDependencyStore.query appended.store 0 := by
  dsimp only
  refine ⟨AuthorizedAppend.service_resume_after_write revocationWorlds appendRequirement 0 captured storedData
    (by decide),rfl,AuthorizedAppend.service_completed revocationWorlds appendRequirement 0 appended storedData
      (by decide),?_⟩
  decide

/-- Revocation changes the actual operation decision despite the same data
store. The refused service retains that world and supplies no source completion. -/
theorem revoked_native_append_is_not_an_acknowledgment :
    let current : OwnWrite.State revocationWorlds Atom 2 := {captured with point := revoked}
    let attempted := OwnWrite.advance revocationWorlds appendRequirement 2
      (AuthorizedAppend.program 0 storedData) current
    (attempted.1,PrimitiveProgram.readOutcome (OwnWrite.step revocationWorlds appendRequirement) attempted.2) =
      (1,Sum.inl (.error .denied),current) ∧
      ∀ after, ¬(AuthorizedAppend.services revocationWorlds appendRequirement).nativeCall
        0 current (.symbol "indexed-space") (.symbol "append") storedData Completed.Frame.empty
          [(.symbol "ack",Completed.Frame.empty)] after := by
  have denied : ¬FrameUpdate revoked.authority
      (appendRequirement (.append 0 [storedData]) revoked.world) := by decide
  exact ⟨AuthorizedAppend.service_denied revocationWorlds appendRequirement 0 _ storedData denied,
    fun after => AuthorizedAppend.denied_has_no_source_completion revocationWorlds appendRequirement 0 _ after
      storedData Completed.Frame.empty denied⟩

private def nativeCaller : AuthorizedAppend.Retained.Configuration revocationWorlds (size := 2) :=
  ⟨captured,0,
    .context 1 (.work (.minimal [] [] none (AuthorizedAppend.instruction storedData) Completed.Frame.empty))
      [.singleton],
    [.publish (.symbol "outer")],
    [(.symbol "earlier",Completed.Frame.empty),(.symbol "earlier",Completed.Frame.empty)]⟩

private def nativeRequest : AuthorizedAppend.Retained.Request revocationWorlds (size := 2) :=
  ⟨captured,1,storedData,Completed.Frame.empty⟩

private theorem nativeCaller_requested (world : OwnWrite.State revocationWorlds Atom 2) :
    AuthorizedAppend.Retained.requested? revocationWorlds {nativeCaller with world} =
      some {nativeRequest with world} := by
  simp only [AuthorizedAppend.Retained.requested?,nativeCaller,nativeRequest,AuthorizedAppend.Retained.locate,
    AuthorizedAppend.instruction,Option.map_some,Entry.Value.erase_ofAtom]

/-- The child context, rather than the root context, selects the writer.
The service returns both saved stacks and duplicate earlier occurrences. -/
theorem nested_native_service_retains_both_callers
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy) :
    let world := AuthorizedAppend.Retained.reachedWorld revocationWorlds nativeRequest
    let next := AuthorizedAppend.Retained.deliverConfiguration revocationWorlds nativeCaller world
      [(.symbol "ack",Completed.Frame.empty)]
    RecursiveExecution.Contextual.Stateful.Protocol.Rule
      (AuthorizedAppend.environment revocationWorlds appendRequirement dispatch lookup) policy nativeCaller
      (some (.silent next)) ∧
      (AuthorizedAppend.Retained.handled revocationWorlds appendRequirement).run 4 (.running (.enter nativeCaller)) =
        ([.requested nativeRequest,
          .performed ⟨PUnit.unit,captured,.write (.append 1 [storedData]),.ok ()⟩,
          .replied (.returned (world,[(.symbol "ack",Completed.Frame.empty)]))],.finished (.returned next)) ∧
      next.control = .context 1 (.returning [(.symbol "ack",Completed.Frame.empty)]) [.singleton] ∧
      next.stack = [.publish (.symbol "outer")] ∧
      next.emitted = [(.symbol "earlier",Completed.Frame.empty),(.symbol "earlier",Completed.Frame.empty)] ∧
      OrderedDependencyStore.query world.store 1 = [storedData] ∧
      OrderedDependencyStore.query world.store 0 = [] := by
  have found := nativeCaller_requested captured
  have square := AuthorizedAppend.Retained.operation_refinement revocationWorlds appendRequirement
    dispatch lookup policy nativeCaller nativeRequest found (by decide)
  exact ⟨square.1,square.2.1,rfl,rfl,rfl,rfl,rfl⟩

/-- At the cut, the provider world has changed although the saved caller
still contains the input world. Resumption has only the reply occurrence. -/
theorem nested_native_pause_keeps_the_reached_world :
    let world := AuthorizedAppend.Retained.reachedWorld revocationWorlds nativeRequest
    let retained := HandledState.handling nativeRequest (.enter nativeCaller)
      (⟨PUnit.unit,.ok (.ret [(.symbol "ack",Completed.Frame.empty)]),world⟩ :
        AuthorizedAppend.Retained.Packet revocationWorlds appendRequirement)
    (AuthorizedAppend.Retained.handled revocationWorlds appendRequirement).run 2 (.running (.enter nativeCaller)) =
      ([.requested nativeRequest,.performed ⟨PUnit.unit,captured,.write (.append 1 [storedData]),.ok ()⟩],
        .exhausted retained) ∧
      AuthorizedAppend.Retained.currentWorld? revocationWorlds appendRequirement retained = some world ∧
      OrderedDependencyStore.query world.store 1 = [storedData] ∧
      OrderedDependencyStore.query nativeCaller.world.store 1 = [] ∧
      (AuthorizedAppend.Retained.handled revocationWorlds appendRequirement).run 2 retained =
        ([.replied (.returned (world,[(.symbol "ack",Completed.Frame.empty)]))],
          .finished (.returned (AuthorizedAppend.Retained.deliverConfiguration revocationWorlds nativeCaller world
            [(.symbol "ack",Completed.Frame.empty)]))) := by
  exact ⟨AuthorizedAppend.Retained.handled_post_write revocationWorlds appendRequirement nativeCaller nativeRequest
      (nativeCaller_requested captured) (by decide),rfl,rfl,rfl,
    AuthorizedAppend.Retained.handled_resume_after_write revocationWorlds appendRequirement nativeCaller nativeRequest _⟩

/-- Restarting the instruction in the reached world performs a second write.
It is observably different from resuming the retained return continuation. -/
theorem nested_native_restart_duplicates_the_write :
    let first := AuthorizedAppend.Retained.reachedWorld revocationWorlds nativeRequest
    let restarted := {nativeCaller with world := first}
    let request := {nativeRequest with world := first}
    let second := AuthorizedAppend.Retained.reachedWorld revocationWorlds request
    (AuthorizedAppend.Retained.handled revocationWorlds appendRequirement).run 4 (.running (.enter restarted)) =
      ([.requested request,.performed ⟨PUnit.unit,first,.write (.append 1 [storedData]),.ok ()⟩,
        .replied (.returned (second,[(.symbol "ack",Completed.Frame.empty)]))],
        .finished (.returned (AuthorizedAppend.Retained.deliverConfiguration revocationWorlds restarted second
          [(.symbol "ack",Completed.Frame.empty)]))) ∧
      OrderedDependencyStore.query first.store 1 = [storedData] ∧
      OrderedDependencyStore.query second.store 1 = [storedData,storedData] := by
  exact ⟨AuthorizedAppend.Retained.handled_completed revocationWorlds appendRequirement _ _
    (nativeCaller_requested _) (by decide),rfl,rfl⟩

/-- A refused nested call leaves the world intact and admits no independent
source completion, for any fabricated result batch or reached world. -/
theorem nested_native_denial_is_a_fault :
    let current : OwnWrite.State revocationWorlds Atom 2 := {captured with point := revoked}
    let configuration := {nativeCaller with world := current}
    let request := {nativeRequest with world := current}
    (AuthorizedAppend.Retained.handled revocationWorlds appendRequirement).run 4 (.running (.enter configuration)) =
      ([.requested request,.performed ⟨PUnit.unit,current,.write (.append 1 [storedData]),.error .denied⟩,
        .replied (.faulted (current,.denied))],.finished (.faulted (current,.denied))) ∧
      ∀ (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy) results after,
        ¬Completed.Stateful.MinimalRel
          (AuthorizedAppend.environment revocationWorlds appendRequirement dispatch lookup) 1 current [] [] none
          (AuthorizedAppend.instruction storedData) Completed.Frame.empty results after (policy := policy) := by
  refine ⟨AuthorizedAppend.Retained.handled_denied revocationWorlds appendRequirement _ _
    (nativeCaller_requested _) (by decide),?_⟩
  intro dispatch lookup policy results after
  exact AuthorizedAppend.denied_source_instruction revocationWorlds appendRequirement dispatch lookup policy
    1 _ after storedData Completed.Frame.empty [] [] none results (by decide)

/-- A native instruction embedded inside ordinary syntax is not a selected
operational context. This service adapter cannot execute it by searching. -/
theorem nested_syntax_is_not_a_native_service_site :
    let configuration : AuthorizedAppend.Retained.Configuration revocationWorlds (size := 2) :=
      {nativeCaller with control := .work (.minimal [] [] none
        (.expression .active [.symbol "literal",AuthorizedAppend.instruction storedData]) Completed.Frame.empty)}
    AuthorizedAppend.Retained.requested? revocationWorlds configuration = none ∧
      (AuthorizedAppend.Retained.handled revocationWorlds appendRequirement).run 1 (.running (.enter configuration)) =
        ([],.stuck (.running (.enter configuration))) := by
  exact ⟨rfl,rfl⟩

private def continuingTask (frame : Frame) : Task :=
  .minimal [] [] none (AuthorizedAppend.instruction storedData) frame

private def continuingCaller (frame : Frame) : AuthorizedAppend.Retained.Configuration revocationWorlds (size := 2) :=
  ⟨captured,0,.context 1 (.work (continuingTask frame)) [.append (continuingTask frame),.singleton],
    [.publish (.symbol "outer")],[(.symbol "earlier",frame),(.symbol "earlier",frame)]⟩

private def reachedCut (frame : Frame) : AuthorizedAppend.Retained.Configuration revocationWorlds (size := 2) :=
  ⟨AuthorizedAppend.Retained.reachedWorld revocationWorlds nativeRequest,0,
    .context 1 (.work (continuingTask frame)) [.prepend [(.symbol "ack",frame)],.singleton],
    [.publish (.symbol "outer")],[(.symbol "earlier",frame),(.symbol "earlier",frame)]⟩

private def pendingRequest (frame : Frame) : AuthorizedAppend.Retained.Request revocationWorlds (size := 2) :=
  ⟨(reachedCut frame).world,1,storedData,frame⟩

private theorem reachedCut_requested (frame : Frame) :
    AuthorizedAppend.Retained.requested? revocationWorlds (reachedCut frame) = some (pendingRequest frame) := by
  simp only [AuthorizedAppend.Retained.requested?,reachedCut,pendingRequest,continuingTask,
    AuthorizedAppend.Retained.locate,AuthorizedAppend.instruction,Option.map_some,Entry.Value.erase_ofAtom]

/-- The cut is reached by a real native write and the existing append
continuation. Its world already contains that committed occurrence. -/
private theorem continuingCaller_prefix (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : CastLookup) (policy : Policy) (frame : Frame) :
    Derivation (RecursiveExecution.Contextual.Stateful.Protocol.Rule
        (AuthorizedAppend.environment revocationWorlds appendRequirement dispatch lookup) policy)
      2 (continuingCaller frame) [] (.exhausted (reachedCut frame)) := by
  have site : AuthorizedAppend.Retained.Site revocationWorlds captured 0 (continuingCaller frame).control
      ⟨captured,1,storedData,frame⟩ := by
    apply AuthorizedAppend.Retained.Site.context
    simpa only [continuingTask,AuthorizedAppend.instruction,Entry.Value.erase_ofAtom] using
      (AuthorizedAppend.Retained.Site.native (authority := revocationWorlds) (world := captured)
        (reader := (1 : Fin 2)) (live := []) (scope := []) (caller := none) (readiness := .active)
        (argument := Entry.Value.ofAtom storedData) (frame := frame))
  have written := site.world_step revocationWorlds appendRequirement dispatch lookup policy
    (continuingCaller frame).stack (by
      change FrameUpdate held.authority (Access.consume : revocationWorlds.Fibre held.world)
      let _ := decision held
      decide)
  refine .silent (.internal written) (.silent (.internal ?_) (.pause _))
  apply RecursiveMachine.Contextual.WorldLocalStep.context
  exact RecursiveMachine.Contextual.WorldLocalStep.core (.returning _) rfl .append (.work _)

/-- Validation uses the reached store, including its earlier own write.
An unrelated edit is admitted, and the resumed service adds only its one
pending occurrence. Arbitrary activation frames and both callers survive. -/
theorem reached_cut_unrelated_edit_resumes_once (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : CastLookup) (policy : Policy) (frame : Frame) :
    let current : OwnWrite.State revocationWorlds Atom 2 :=
      ⟨OrderedDependencyStore.execute (reachedCut frame).world.store [.append 0 [.symbol "New"]],held⟩
    let rebased := {reachedCut frame with world := current}
    let request := {pendingRequest frame with world := current}
    let world := AuthorizedAppend.Retained.reachedWorld revocationWorlds request
    let next := AuthorizedAppend.Retained.deliverConfiguration revocationWorlds rebased world [(.symbol "ack",frame)]
    AuthorizedAppend.Retained.rebase revocationWorlds appendRequirement (reachedCut frame) current = .ok rebased ∧
      Derivation (RecursiveExecution.Contextual.Stateful.Protocol.Rule
        (AuthorizedAppend.environment revocationWorlds appendRequirement dispatch lookup) policy)
        1 rebased [] (.exhausted next) ∧
      (AuthorizedAppend.Retained.handled revocationWorlds appendRequirement).run 4 (.running (.enter rebased)) =
        ([.requested request,.performed ⟨PUnit.unit,current,.write (.append 1 [storedData]),.ok ()⟩,
          .replied (.returned (world,[(.symbol "ack",frame)]))],.finished (.returned next)) ∧
      OrderedDependencyStore.query world.store 1 = [storedData,storedData] ∧
      OrderedDependencyStore.query world.store 0 = [.symbol "New"] ∧
      next.emitted = [(.symbol "earlier",frame),(.symbol "earlier",frame)] ∧
      OrderedDependencyStore.checkRead current.store (OrderedDependencyStore.readStamp captured.store 1) = false := by
  have lawful : OrderedDependencyStore.ObserverInvariant (reachedCut frame).world.store :=
    OrderedDependencyStore.step_observers captured.store (OrderedDependencyStore.initial_observers _ _)
      (.append 1 [storedData])
  obtain ⟨admitted,_,_,resumed,executed,_,history,_⟩ :=
    AuthorizedAppend.Retained.validated_resume_reached_cut revocationWorlds appendRequirement dispatch lookup policy
      (continuingCaller_prefix dispatch lookup policy frame) (pendingRequest frame) (reachedCut_requested frame)
      [.append 0 [.symbol "New"]] held lawful (by rfl) (by
        change FrameUpdate held.authority (Access.consume : revocationWorlds.Fibre held.world)
        let _ := decision held
        decide)
  exact ⟨admitted,resumed,executed,rfl,rfl,history,rfl⟩

/-- A changed dependency refuses the whole reached cut, without discarding
the previously committed write or either duplicate earlier occurrence. -/
theorem reached_cut_changed_source_refuses (frame : Frame) :
    let current : OwnWrite.State revocationWorlds Atom 2 :=
      ⟨OrderedDependencyStore.execute (reachedCut frame).world.store [.append 1 [.symbol "New"]],held⟩
    AuthorizedAppend.Retained.rebase revocationWorlds appendRequirement (reachedCut frame) current =
        .error (reachedCut frame) ∧
      OrderedDependencyStore.query (reachedCut frame).world.store 1 = [storedData] ∧
      (reachedCut frame).emitted = [(.symbol "earlier",frame),(.symbol "earlier",frame)] := by
  refine ⟨AuthorizedAppend.Retained.rebase_refused revocationWorlds appendRequirement
    (reachedCut frame) (pendingRequest frame) _ (reachedCut_requested frame) (.inl rfl),rfl,rfl⟩

/-- Source validation alone is insufficient: the same reached store is
refused after revocation, before a second provider operation is made. -/
theorem reached_cut_revocation_refuses_current_source (frame : Frame) :
    let current : OwnWrite.State revocationWorlds Atom 2 := {(reachedCut frame).world with point := revoked}
    OrderedDependencyStore.checkRead current.store
        (OrderedDependencyStore.readStamp (reachedCut frame).world.store 1) = true ∧
      AuthorizedAppend.Retained.rebase revocationWorlds appendRequirement (reachedCut frame) current =
        .error (reachedCut frame) ∧
      OrderedDependencyStore.query (reachedCut frame).world.store 1 = [storedData] := by
  refine ⟨rfl,AuthorizedAppend.Retained.rebase_refused revocationWorlds appendRequirement
    (reachedCut frame) (pendingRequest frame) _ (reachedCut_requested frame) (.inr ?_),rfl⟩
  change ¬FrameUpdate revoked.authority (Access.consume : revocationWorlds.Fibre revoked.world)
  let _ := decision revoked
  decide

end Mettapedia.Languages.MeTTa.HE.RecursiveService.CheckedAdmission.Controls

namespace Mettapedia.Languages.MeTTa.HE.RecursiveService.ComponentRealization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Bindings.ScopeObservation
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.ProductiveCoreAdapters.ComponentRealization

/-- A certified nonidentity load of the same restore task through two
solution-equivalent binding presentations. -/
structure RestoreLoad (Context World : Type) where
  world : World
  context : Context
  pairs : List Entry.Value
  saved : List Result
  caller : Frame
  bindings : Bindings
  stack : List Continuation
  emitted : List Result
  agreement : BindingSourceAgreement caller.bindings bindings

namespace RestoreLoad

variable {Context World : Type}

def logical (input : RestoreLoad Context World) : WorldConfiguration Context World :=
  ⟨input.world, input.context, .work (.restore input.pairs input.saved input.caller),
    input.stack, input.emitted⟩

def implementation (input : RestoreLoad Context World) : WorldConfiguration Context World :=
  ⟨input.world, input.context,
    .work (.restore input.pairs input.saved (input.caller.represent input.bindings input.agreement)),
    input.stack, input.emitted⟩

end RestoreLoad

/-- The store currently exposed by a restore phase. Other phases have no
restore-store observation in this component profile. -/
def restoreStore {Context World : Type} (state : WorldConfiguration Context World) : Option Bindings :=
  match state.control with
  | .work (.restore _ _ caller) => some caller.bindings
  | _ => none

/-- Retained caller/control envelope. The current restore store is factored
separately by `restoreStore`. -/
def controlEnvelope {Context World : Type} (state : WorldConfiguration Context World) :
    Context × List Context × List Continuation :=
  (state.context, state.control.contexts, state.stack)

def selectionSpace {Context World : Type} (view : World → Context → Space)
    (state : WorldConfiguration Context World) : Space :=
  view state.world state.context

def projection {Context World : Type} (view : World → Context → Space) :
    ComponentProjection (WorldConfiguration Context World) (Option Bindings)
      (Context × List Context × List Continuation) Space World (List Result) where
  store := restoreStore
  control := controlEnvelope
  selection := selectionSpace view
  world := WorldConfiguration.world
  publication := WorldConfiguration.emitted

/-- Semantic relation between optional restore stores. -/
def StoreRel : Option Bindings → Option Bindings → Prop
  | some left, some right => BindingSourceAgreement left right
  | none, none => True
  | _, _ => False

theorem storeRel_refl (store : Option Bindings) : StoreRel store store := by
  cases store with
  | none => trivial
  | some bindings => exact BindingSourceAgreement.refl bindings

/-- The five-component relation between two representations of the same HE
stateful protocol at a restore cut. This is not a second machine model. -/
def relation {Context World : Type} (view : World → Context → Space) :
    FiveComponentRel (projection view) (projection view) where
  storeRel := StoreRel
  controlRel := Eq
  selectionRel := Eq
  worldRel := Eq
  publicationRel := Eq
  coherent := RestoreRepresentation

/-- Every proved restore representation entails all five component laws. -/
theorem holds_of_restore {Context World : Type} {view : World → Context → Space}
    {before after : WorldConfiguration Context World}
    (related : RestoreRepresentation before after) :
    (relation view).Holds before after := by
  cases related with
  | same =>
      exact ⟨storeRel_refl _, rfl, rfl, rfl, rfl, .same before⟩
  | @pending world context pairs saved caller bindings stack emitted agreement =>
      refine ⟨?_, rfl, rfl, rfl, rfl, .pending agreement⟩
      change StoreRel (some caller.bindings)
        (some (caller.represent bindings agreement).bindings)
      simpa [StoreRel] using agreement

/-- The two certified loaders establish the full component relation. -/
theorem load_related {Context World : Type} (view : World → Context → Space)
    (input : RestoreLoad Context World) :
    (relation view).Holds input.logical input.implementation :=
  holds_of_restore (.pending input.agreement)

/-- Joint model readout of the optional store. -/
def storeObservation : Option Bindings → List Atom → Set (List Atom)
  | some bindings, atoms => observedTuples bindings atoms
  | none, _ => Set.univ

/-- Store agreement preserves every later joint binding observation. -/
theorem storeObservation_eq {left right : Option Bindings}
    (related : StoreRel left right) (atoms : List Atom) :
    storeObservation left atoms = storeObservation right atoms := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some => cases related
  | some left =>
      cases right with
      | none => cases related
      | some right =>
          have agreement : BindingSourceAgreement left right := related
          ext values
          constructor
          · rintro ⟨model, satisfied, returned⟩
            exact ⟨model, (agreement.solutions model).mp satisfied, returned⟩
          · rintro ⟨model, satisfied, returned⟩
            exact ⟨model, (agreement.solutions model).mpr satisfied, returned⟩

/-- Read a value through the currently retained restore frame. -/
def futureRead {Context World : Type} (policy : Policy)
    (state : WorldConfiguration Context World) (value : Entry.Value) : Entry.Value :=
  match state.control with
  | .work (.restore _ _ caller) => caller.read policy value
  | _ => value

/-- A restore representation preserves actual future frame reads. -/
theorem futureRead_eq {Context World : Type} {policy : Policy}
    {before after : WorldConfiguration Context World}
    (related : RestoreRepresentation before after) (value : Entry.Value) :
    futureRead policy before value = futureRead policy after value := by
  cases related with
  | same => rfl
  | @pending world context pairs saved caller bindings stack emitted agreement =>
      have represented : RestoreRepresentation
          (⟨world, context, .work (.restore pairs saved caller), stack, emitted⟩ :
            WorldConfiguration Context World)
          ⟨world, context,
            .work (.restore pairs saved (caller.represent bindings agreement)), stack, emitted⟩ :=
        .pending agreement
      exact (RestoreRepresentation.pending_read represented policy value).symm

/-- One HE protocol inspection is implemented by one productive inspection
under the nonidentity restore representation. -/
theorem restore_productive_block {Context World PublicWorld : Type}
    {environment : WorldEnvironment Context World} {policy : Policy}
    (publicScope : List String) (worldView : World → PublicWorld) :
    ProductiveLocalBlock
      (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
      (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
      (relation environment.view).Holds
      (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView)
      (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView) := by
  refine ⟨?_⟩
  intro before target events outcome related path
  have represented := related.2.2.2.2.2
  cases represented with
  | same =>
      refine ⟨1, by omega, events, outcome, path, rfl, ?_⟩
      cases outcome with
      | finished verdict => exact .finished _
      | faulted => exact .faulted
      | suspended request saved => exact .suspended request (holds_of_restore (.same saved))
      | stuck stopped => exact .stuck (holds_of_restore (.same stopped))
      | exhausted saved => exact .exhausted (holds_of_restore (.same saved))
  | @pending world context pairs saved caller bindings stack emitted agreement =>
      have represented : RestoreRepresentation
          (⟨world, context, .work (.restore pairs saved caller), stack, emitted⟩ :
            WorldConfiguration Context World)
          ⟨world, context,
            .work (.restore pairs saved (caller.represent bindings agreement)), stack, emitted⟩ :=
        .pending agreement
      cases path with
      | silent advanced rest =>
          cases rest
          cases advanced with
          | internal primitive =>
              obtain ⟨next, moved, retained⟩ := represented.step (.internal primitive)
              cases moved with
              | internal localStep =>
                  exact ⟨1, by omega, [], .exhausted _,
                    .silent (.internal localStep) (.pause _), rfl,
                    .exhausted (holds_of_restore retained)⟩
      | published advanced _ => cases advanced
      | finished advanced => cases advanced with | finished observed => cases observed
      | faulted advanced => cases advanced
      | requested advanced => cases advanced
      | stuck advanced =>
          cases advanced with
          | stuck observed blocked =>
              refine ⟨1, by omega, [], .stuck _, .stuck (fuel := 0) (.stuck rfl ?_), rfl,
                .stuck (holds_of_restore represented)⟩
              rintro ⟨next, moved⟩
              obtain ⟨original, advanced, _⟩ := represented.symm.step moved
              exact blocked ⟨original, advanced⟩

/-- The same-rule HE restore-representation profile discharges M1--M7; M8 is
obtained from the generic local-to-global theorem. This proves representation
independence, not AM-to-native refinement. -/
def realization {Context World PublicWorld : Type}
    (environment : WorldEnvironment Context World) (policy : Policy)
    (publicScope : List String) (worldView : World → PublicWorld) :
    ModularMachineAdequacy
      (fun input : RestoreLoad Context World => input.logical)
      (fun input : RestoreLoad Context World => input.implementation)
      (projection environment.view) (projection environment.view) (relation environment.view)
      (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
      (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
      (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView)
      (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView)
      (List Atom) (List Atom) (Set (List Atom)) PublicWorld
      (Context × List Context × List Continuation) (Multiset (Set (List Atom)))
      Entry.Value Entry.Value where
  m1_load := load_related environment.view
  observeLogicalSelection := Space.atoms
  observeImplSelection := Space.atoms
  m2_selection related := congrArg Space.atoms related.2.2.1
  readLogicalStore := storeObservation
  readImplStore := storeObservation
  m3_store_read related := storeObservation_eq related.1
  m4_control := restore_productive_block publicScope worldView
  observeLogicalWorld := worldView
  observeImplWorld := worldView
  m5_world related := congrArg worldView related.2.2.2.1
  observeLogicalControl := id
  observeImplControl := id
  m6_retained_control related := related.2.1
  observeLogicalPublication := RecursiveExecution.Contextual.Protocol.publicAnswers publicScope
  observeImplPublication := RecursiveExecution.Contextual.Protocol.publicAnswers publicScope
  m7_publication related := congrArg
    (RecursiveExecution.Contextual.Protocol.publicAnswers publicScope) related.2.2.2.2.1
  observeLogicalFuture := futureRead policy
  observeImplFuture := futureRead policy
  m7_future related := futureRead_eq related.2.2.2.2.2

/-- Principal M8 retained-run theorem for HE restore-representation invariance. -/
theorem retained_run {Context World PublicWorld : Type}
    (environment : WorldEnvironment Context World) (policy : Policy)
    (publicScope : List String) (worldView : World → PublicWorld)
    (input : RestoreLoad Context World)
    {first second : Nat} {saved : WorldConfiguration Context World}
    {events later : List Result}
    {outcome : Outcome (WorldConfiguration Context World) (World × List Result) Empty}
    (initial : Derivation (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
      first input.logical events (.exhausted saved))
    (suffix : Derivation (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
      second saved later outcome) :
    ∃ first' second' saved' events' later' outcome',
      Derivation (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
        first' input.implementation events' (.exhausted saved') ∧
      Derivation (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
        second' saved' later' outcome' ∧
      (relation environment.view).Holds saved saved' ∧
      (realization environment policy publicScope worldView).ObservationsAgree saved saved' ∧
      events'.flatMap
          (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView).event =
        events.flatMap
          (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView).event ∧
      later'.flatMap
          (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView).event =
        later.flatMap
          (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView).event ∧
      OutcomeRel (relation environment.view).Holds
        (outcome.relabel
          (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView).verdict
          (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView).request)
        (outcome'.relabel
          (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView).verdict
          (RecursiveExecution.Contextual.Stateful.Protocol.readout publicScope worldView).request) ∧
      Derivation (RecursiveExecution.Contextual.Stateful.Protocol.Rule environment policy)
        (first' + second') input.implementation (events' ++ later') outcome' :=
  (realization environment policy publicScope worldView).loaded_retained_run input initial suffix


end Mettapedia.Languages.MeTTa.HE.RecursiveService.ComponentRealization

namespace Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.Cursor.ReadOnlyQuery
open Mettapedia.Machines
open Mettapedia.GSLT.Contracts
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.Machines.BranchLocalNeed.NeedDependentService
open Mettapedia.TypeTheory.DisplayedEvidence
open Mettapedia.Machines.Cursor.OwnedLifecycle
open _root_.CategoryTheory

/-- The exact semantic identity of one indexed append request cached by Need. -/
structure AppendKey (size : Nat) where
  reader : Fin size
  argument : Atom
  stamp : OrderedDependencyStore.ReadStamp size
  deriving DecidableEq

/-- The Need origin includes the complete captured read stamp, so a later world
with the same reader and argument cannot reuse a stale cached reply. -/
def retainedKey
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size)) : AppendKey size :=
  ⟨request.reader, request.argument,
    OrderedDependencyStore.readStamp saved.world.store request.reader⟩

/-- A changed complete stamp changes the Need origin even when reader and
argument syntax are unchanged. -/
theorem retainedKey_ne_of_stale
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : OrderedDependencyStore.Store Atom size)
    (stale : OrderedDependencyStore.checkRead current
      (OrderedDependencyStore.readStamp saved.world.store request.reader) = false) :
    retainedKey saved request ≠
      ⟨request.reader, request.argument,
        OrderedDependencyStore.readStamp current request.reader⟩ := by
  intro equal
  have stampEq := congrArg AppendKey.stamp equal
  simp only [retainedKey] at stampEq
  have accepted : OrderedDependencyStore.checkRead current
      (OrderedDependencyStore.readStamp saved.world.store request.reader) = true := by
    simpa [OrderedDependencyStore.checkRead, OrderedDependencyStore.readStamp] using stampEq
  rw [stale] at accepted
  cases accepted

/-- Expose complete read stamps, including store identity and generation, as a
revision environment. Comparing only the numeric revision would be unsound. -/
def storeRevisionEnv {size : Nat} (store : OrderedDependencyStore.Store Atom size) :
    RevisionEnvironment (Fin size) (OrderedDependencyStore.ReadStamp size) :=
  ⟨fun reader => OrderedDependencyStore.readStamp store reader⟩

/-- Capture exactly the source stamp consulted by one pending append. -/
def capturedReaderView {size : Nat} (store : OrderedDependencyStore.Store Atom size)
    (reader : Fin size) :
    CapturedReadView (Fin size) (OrderedDependencyStore.ReadStamp size) :=
  (CapturedReadView.admit (storeRevisionEnv store)).consult (storeRevisionEnv store) reader

/-- Ordered-store stamp validation is exactly publication eligibility for the
corresponding one-reader captured view. -/
theorem checkRead_iff_canPublish {size : Nat}
    (captured current : OrderedDependencyStore.Store Atom size) (reader : Fin size) :
    OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp captured reader) = true ↔
      (capturedReaderView captured reader).CanPublish (storeRevisionEnv current) := by
  unfold CapturedReadView.CanPublish
  rw [CapturedReadView.valid_dependencies_iff]
  simp [OrderedDependencyStore.checkRead, capturedReaderView, storeRevisionEnv,
    CapturedReadView.admit, CapturedReadView.consult,
    CapturedReadView.mismatchAt]
  constructor
  · intro same observed member
    have observed_eq : observed = reader := Finset.mem_singleton.mp member
    subst observed
    exact same.symm
  · intro agrees
    exact (agrees reader (Finset.mem_singleton_self reader)).symm

/-- A dependency capture whose payload is the actual retained HE cut. -/
abbrev RetainedCapture {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld) (size : Nat) :=
  CapturedReadFrame Nat (Fin size) (OrderedDependencyStore.ReadStamp size)
    (AuthorizedAppend.Retained.Configuration authority (size := size))

/-- Issued returns are keyed by their exact Atom payload and indexed provider. -/
abbrev RetainedRegistry (size : Nat) := IssuedReturn.Registry Atom (Fin size)
abbrev RetainedHandle (size : Nat) := IssuedReturn.Handle Atom (Fin size)

/-- Build the dependency capture from the same saved cut and request that will
be resumed. -/
def retainedCapture {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (source : Nat) (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size)) :
    RetainedCapture authority size :=
  ⟨source, capturedReaderView saved.world.store request.reader, saved⟩

/-- Parent lineage, provider and payload must all name this pending request. -/
def HandleMatches {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat} (source : Nat)
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (handle : RetainedHandle size) : Prop :=
  handle.parent = source ∧ handle.row.provider = request.reader ∧
    handle.row.payload = request.argument

instance {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (source : Nat) (request : AuthorizedAppend.Retained.Request authority (size := size))
    (handle : RetainedHandle size) : Decidable (HandleMatches source request handle) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Refusals occur before the retained HE configuration is changed. -/
inductive RetainedReplyRefusal where
  | requestMismatch
  | staleDependencies
  | denied
  | unissued
  deriving DecidableEq, Repr

/-- A successful boundary returns the delivered cut, residual registry and
cleared physical handle, together with the lookup cost. -/
abbrev RetainedReplyResult {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld) (size : Nat) :=
  Except RetainedReplyRefusal
      (AuthorizedAppend.Retained.Configuration authority (size := size) ×
        RetainedRegistry size × RetainedHandle size) × Nat

/-- Validate the exact reached read, authenticate the exact pending request,
consume its issued row and only then construct the retained HE reply. -/
def deliverRetainedChecked {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (source : Nat)
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size))
    (registry : RetainedRegistry size) (handle : RetainedHandle size) :
    RetainedReplyResult authority size :=
  match AuthorizedAppend.Retained.requested? authority saved with
  | none => (.error .requestMismatch, 0)
  | some request =>
      let capture := retainedCapture source saved request
      let checked := capture.view.validate (storeRevisionEnv current.store)
      if HandleMatches source request handle then
        if checked.accepted then
          if FrameUpdate current.point.authority
              (required (.append request.reader [request.argument]) current.point.world) then
            let released := IssuedReturn.releaseIssued registry handle
            match released.1 with
            | none => (.error .unissued, released.2)
            | some (next, cleared) =>
                let pending := {request with world := current}
                let final := AuthorizedAppend.Retained.deliverConfiguration authority
                  {saved with world := current}
                  (AuthorizedAppend.Retained.reachedWorld authority pending)
                  [(.symbol "ack", request.frame)]
                (.ok (final, next, cleared), released.2)
          else (.error .denied, 0)
        else (.error .staleDependencies, 0)
      else (.error .requestMismatch, 0)

/-- The local checked boundary succeeds from current dependencies and issued
authority, preserves registry validity and revokes both old handle spellings. -/
theorem deliverRetainedChecked_admitted
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (source : Nat)
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size))
    (registry : RetainedRegistry size) (handle : RetainedHandle size)
    (registryValid : registry.Valid)
    (found : AuthorizedAppend.Retained.requested? authority saved = some request)
    (matched : HandleMatches source request handle)
    (valid : OrderedDependencyStore.checkRead current.store
      (OrderedDependencyStore.readStamp saved.world.store request.reader) = true)
    (allowed : FrameUpdate current.point.authority
      (required (.append request.reader [request.argument]) current.point.world))
    (authenticated : IssuedReturn.Authenticated registry handle) :
    ∃ next cleared,
      (deliverRetainedChecked required source saved current registry handle).1 =
        .ok (AuthorizedAppend.Retained.deliverConfiguration authority
          {saved with world := current}
          (AuthorizedAppend.Retained.reachedWorld authority {request with world := current})
          [(.symbol "ack", request.frame)], next, cleared) ∧
      next.Valid ∧ ¬IssuedReturn.Authenticated next handle ∧
      ¬IssuedReturn.Authenticated next cleared := by
  obtain ⟨next, cleared, released⟩ :=
    (IssuedReturn.releaseIssued_exists_iff registry handle).mpr authenticated
  have release : IssuedReturn.releaseIssued registry handle =
      (some (next, cleared), (IssuedReturn.releaseIssued registry handle).2) :=
    Prod.ext released rfl
  have currentView :
      ((retainedCapture source saved request).view.validate
        (storeRevisionEnv current.store)).accepted = true :=
    (CapturedReadView.validate_accepted_iff_canPublish _ _).2
      ((checkRead_iff_canPublish saved.world.store current.store request.reader).mp valid)
  refine ⟨next, cleared, ?_, ?_, ?_⟩
  · simp only [deliverRetainedChecked, found]
    rw [if_pos matched, if_pos currentView, if_pos allowed, release]
  · exact IssuedReturn.releaseIssued_preserves_validity registry handle next cleared _
      registryValid release
  · have revoked := IssuedReturn.releaseIssued_revokes_old_and_cleared
      registry handle next cleared _ registryValid release
    refine ⟨revoked.1, ?_⟩
    intro authenticatedCleared
    have present := (IssuedReturn.lookup_authenticates next cleared).mpr authenticatedCleared
    exact present (congrArg Prod.fst revoked.2)

/-- A copied saved cut cannot replay a handle already consumed in the current
registry. -/
theorem deliverRetainedChecked_unissued
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (source : Nat)
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size))
    (registry : RetainedRegistry size) (handle : RetainedHandle size)
    (found : AuthorizedAppend.Retained.requested? authority saved = some request)
    (matched : HandleMatches source request handle)
    (valid : OrderedDependencyStore.checkRead current.store
      (OrderedDependencyStore.readStamp saved.world.store request.reader) = true)
    (allowed : FrameUpdate current.point.authority
      (required (.append request.reader [request.argument]) current.point.world))
    (unissued : ¬IssuedReturn.Authenticated registry handle) :
    (deliverRetainedChecked required source saved current registry handle).1 = .error .unissued := by
  have release : (IssuedReturn.releaseIssued registry handle).1 = none := by
    cases released : (IssuedReturn.releaseIssued registry handle).1 with
    | none => rfl
    | some pair =>
        exact (unissued ((IssuedReturn.releaseIssued_exists_iff registry handle).mp
          ⟨pair.1, pair.2, released⟩)).elim
  have currentView :
      ((retainedCapture source saved request).view.validate
        (storeRevisionEnv current.store)).accepted = true :=
    (CapturedReadView.validate_accepted_iff_canPublish _ _).2
      ((checkRead_iff_canPublish saved.world.store current.store request.reader).mp valid)
  simp only [deliverRetainedChecked, found]
  rw [if_pos matched, if_pos currentView, if_pos allowed, release]

/-- Stale reached dependencies refuse before inspecting or consuming the issued
row. -/
theorem deliverRetainedChecked_stale
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (source : Nat)
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size))
    (registry : RetainedRegistry size) (handle : RetainedHandle size)
    (found : AuthorizedAppend.Retained.requested? authority saved = some request)
    (matched : HandleMatches source request handle)
    (stale : OrderedDependencyStore.checkRead current.store
      (OrderedDependencyStore.readStamp saved.world.store request.reader) = false) :
    (deliverRetainedChecked required source saved current registry handle).1 =
      .error .staleDependencies := by
  have noPublish : ¬(retainedCapture source saved request).view.CanPublish
      (storeRevisionEnv current.store) := by
    intro publishable
    have checked := (checkRead_iff_canPublish saved.world.store current.store request.reader).mpr
      publishable
    rw [stale] at checked
    cases checked
  have currentView :
      ((retainedCapture source saved request).view.validate
        (storeRevisionEnv current.store)).accepted = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    exact noPublish ((CapturedReadView.validate_accepted_iff_canPublish _ _).mp accepted)
  simp only [deliverRetainedChecked, found]
  rw [if_pos matched, if_neg (by simp [currentView])]

/-- Current dependencies do not substitute for the current operation right;
denial also happens before registry release. -/
theorem deliverRetainedChecked_denied
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (source : Nat)
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size))
    (registry : RetainedRegistry size) (handle : RetainedHandle size)
    (found : AuthorizedAppend.Retained.requested? authority saved = some request)
    (matched : HandleMatches source request handle)
    (valid : OrderedDependencyStore.checkRead current.store
      (OrderedDependencyStore.readStamp saved.world.store request.reader) = true)
    (denied : ¬FrameUpdate current.point.authority
      (required (.append request.reader [request.argument]) current.point.world)) :
    (deliverRetainedChecked required source saved current registry handle).1 = .error .denied := by
  have currentView :
      ((retainedCapture source saved request).view.validate
        (storeRevisionEnv current.store)).accepted = true :=
    (CapturedReadView.validate_accepted_iff_canPublish _ _).2
      ((checkRead_iff_canPublish saved.world.store current.store request.reader).mp valid)
  simp only [deliverRetainedChecked, found]
  rw [if_pos matched, if_pos currentView, if_neg denied]

/-- Returning at the selected native site removes that site, including beneath
arbitrary retained context frames. -/
theorem site_deliver_locate_none
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    {world : AuthorizedAppend.Retained.World authority (size := size)}
    {reader : Fin size} {control : Control (Fin size)}
    {request : AuthorizedAppend.Retained.Request authority (size := size)}
    (site : AuthorizedAppend.Retained.Site authority world reader control request)
    (current : AuthorizedAppend.Retained.World authority (size := size))
    (results : List Result) :
    AuthorizedAppend.Retained.locate authority current reader
      (AuthorizedAppend.Retained.deliver control results) = none := by
  induction site with
  | native => rfl
  | context _ ih => simpa [AuthorizedAppend.Retained.deliver,
      AuthorizedAppend.Retained.locate] using ih

/-- A delivered HE configuration cannot request the same native operation
again. -/
theorem requested?_deliverConfiguration_none
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    {saved : AuthorizedAppend.Retained.Configuration authority (size := size)}
    {request : AuthorizedAppend.Retained.Request authority (size := size)}
    (found : AuthorizedAppend.Retained.requested? authority saved = some request)
    (current : AuthorizedAppend.Retained.World authority (size := size))
    (results : List Result) :
    AuthorizedAppend.Retained.requested? authority
      (AuthorizedAppend.Retained.deliverConfiguration authority saved current results) = none := by
  unfold AuthorizedAppend.Retained.requested?
  simp only [AuthorizedAppend.Retained.deliverConfiguration]
  rw [site_deliver_locate_none (AuthorizedAppend.Retained.requested_site authority found)
    current results]
  rfl

/-- A dependent Need service indexed by the complete append key. -/
def retainedFamily (size : Nat) (Value : Type) : Family.{0, 0} where
  Raw := AppendKey size
  Exact := fun _ => Value

instance instDecidableEqRetainedRaw (size : Nat) (Value : Type) :
    DecidableEq (retainedFamily size Value).Raw :=
  inferInstanceAs (DecidableEq (AppendKey size))

/-- The service callback returns the already earned retained configuration; the
Need machine owns whether it is produced or read from cache. -/
def retainedProducer {size : Nat} {Value : Type} (value : Value) :
    (request : (retainedFamily size Value).Raw) →
      (retainedFamily size Value).Exact request :=
  fun _ => value

/-- First demand for the exact append key. -/
def retainedNeedBefore {size : Nat} {Value : Type}
    (world : NeedDependentService.ServiceWorld (retainedFamily size Value))
    (cell : CellId) (key : AppendKey size) :
    NeedDependentService.ServiceMachine (retainedFamily size Value) :=
  ⟨world, .run (.demand key cell) [], {}⟩

/-- After the demand and ownership claim, Need is poised at its one producer
action and the cache records the unique evaluating owner. -/
def retainedNeedEvaluating {size : Nat} {Value : Type}
    (world : NeedDependentService.ServiceWorld (retainedFamily size Value))
    (cell : CellId) (key : AppendKey size) :
    NeedDependentService.ServiceMachine (retainedFamily size Value) :=
  ⟨NeedDependentService.forceWorld (retainedFamily size Value) world cell key,
    .run (.produce key) [.commit cell world.nextEvaluator, .resume key],
    (({} : Work).bump 0 0 0 0).bump 1 1 2 0⟩

/-- Exact endpoint after the first demand has committed the retained result. -/
def retainedNeedAfter {size : Nat} {Value : Type}
    (world : NeedDependentService.ServiceWorld (retainedFamily size Value))
    (cell : CellId) (key : AppendKey size) (value : Value) :
    NeedDependentService.ServiceMachine (retainedFamily size Value) :=
  ⟨NeedDependentService.producedWorld (retainedFamily size Value) (retainedProducer value)
      world cell key,
    .halted (.value ⟨key, value⟩),
    NeedDependentService.consumerFinishWork
      (NeedDependentService.freshForceWork (({} : Work).bump 0 0 0 0))⟩

/-- The first two actual Need transitions demand and claim the suspended cell;
the effectful HE service has not run yet. -/
theorem retainedNeed_claim {size : Nat} {Value : Type}
    (world : NeedDependentService.ServiceWorld (retainedFamily size Value))
    (cell : CellId) (key : AppendKey size) (value : Value)
    (suspended : world.heap.lookup cell = some ⟨key, .suspended⟩) :
    runFrontier (NeedDependentService.spec (retainedFamily size Value)
      (retainedProducer value)) 2 [retainedNeedBefore world cell key] =
      [retainedNeedEvaluating world cell key] := by
  apply UniqueSteps.runFrontier_eq
  apply UniqueSteps.cons (by rfl)
  apply UniqueSteps.cons
    (NeedDependentService.step_force_suspended
      (retainedFamily size Value) (retainedProducer value) suspended)
  exact UniqueSteps.refl _

/-- Once the checked service has produced the retained configuration, five
actual Need transitions produce, commit and resume the waiting consumer. -/
theorem retainedNeed_commit_and_resume {size : Nat} {Value : Type}
    (world : NeedDependentService.ServiceWorld (retainedFamily size Value))
    (cell : CellId) (key : AppendKey size) (value : Value) :
    runFrontier (NeedDependentService.spec (retainedFamily size Value)
      (retainedProducer value)) 5 [retainedNeedEvaluating world cell key] =
      [retainedNeedAfter world cell key value] := by
  let afterClaim := NeedDependentService.forceWorld
    (retainedFamily size Value) world cell key
  let workClaim := (({} : Work).bump 0 0 0 0).bump 1 1 2 0
  let workProduced := workClaim.bump 0 0 0 0
  let workCommitted := workProduced.bump 1 1 1 0
  let packet : NeedDependentService.Packet (retainedFamily size Value) := ⟨key, value⟩
  have produce : UniqueSteps
      (NeedDependentService.spec (retainedFamily size Value) (retainedProducer value)) 1
      (retainedNeedEvaluating world cell key)
      ⟨afterClaim, .returned (.value packet)
        [.commit cell world.nextEvaluator, .resume key], workProduced⟩ := by
    apply UniqueSteps.cons
      (NeedDependentService.step_produce (retainedFamily size Value)
        (retainedProducer value) afterClaim key
        [.commit cell world.nextEvaluator, .resume key] workClaim)
    exact UniqueSteps.refl _
  have commit : UniqueSteps
      (NeedDependentService.spec (retainedFamily size Value) (retainedProducer value)) 1
      ⟨afterClaim, .returned (.value packet)
        [.commit cell world.nextEvaluator, .resume key], workProduced⟩
      ⟨NeedDependentService.producedWorld (retainedFamily size Value)
          (retainedProducer value) world cell key,
        .returned (.value packet) [.resume key], workCommitted⟩ := by
    apply UniqueSteps.cons
      (NeedDependentService.step_commit (retainedFamily size Value)
        (retainedProducer value)
        (NeedDependentService.forceWorld_lookup (retainedFamily size Value) world cell key))
    exact UniqueSteps.refl _
  have resume := NeedDependentService.resume_and_halt
    (retainedFamily size Value) (retainedProducer value)
    (NeedDependentService.producedWorld (retainedFamily size Value)
      (retainedProducer value) world cell key) key (.value packet)
    workCommitted
  simpa [retainedNeedAfter, NeedDependentService.freshForceWork,
    afterClaim, workClaim, workProduced, workCommitted, packet,
    NeedDependentService.consumeOutcome_matching (retainedFamily size Value) key value] using
    UniqueSteps.runFrontier_eq _ (produce.trans _ (commit.trans _ resume))

/-- A later demand starts from the already committed cell. -/
def retainedNeedCachedBefore {size : Nat} {Value : Type}
    (world : NeedDependentService.ServiceWorld (retainedFamily size Value))
    (cell : CellId) (key : AppendKey size) (value : Value) :
    NeedDependentService.ServiceMachine (retainedFamily size Value) :=
  ⟨NeedDependentService.producedWorld (retainedFamily size Value) (retainedProducer value)
      world cell key,
    .run (.demand key cell) [], {}⟩

/-- Current reached world after external changes, before the selected append. -/
def retainedCurrent
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (changes : List (OrderedDependencyStore.Action Atom size))
    (point : IndexedAuthority.Point authority) :
    AuthorizedAppend.Retained.World authority (size := size) :=
  ⟨OrderedDependencyStore.execute saved.world.store changes, point⟩

/-- The unique delivered HE configuration shared by service, reply authority
and Need cache. -/
def retainedFinal
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {authority : IndexedAuthority.{0, 0, 0} AuthorityWorld} {size : Nat}
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size)) :
    AuthorizedAppend.Retained.Configuration authority (size := size) :=
  AuthorizedAppend.Retained.deliverConfiguration authority {saved with world := current}
    (AuthorizedAppend.Retained.reachedWorld authority {request with world := current})
    [(.symbol "ack", request.frame)]

/-- Dependency and authority validation change only the reached world; the
pending operational site remains available for the checked reply edge. -/
structure RebaseAdvance
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld) {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size)) : Prop where
  rebased : AuthorizedAppend.Retained.rebase authority required saved current =
    .ok {saved with world := current}
  sourceStable : OrderedDependencyStore.query current.store request.reader =
    OrderedDependencyStore.query saved.world.store request.reader
  requestRetained : AuthorizedAppend.Retained.requested? authority {saved with world := current} =
    some {request with world := current}

/-- The actual one-append service block from the rebased live state to the
delivered HE configuration. -/
structure ServiceAdvance
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld) {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size))
    extends RebaseAdvance authority required dispatch lookup policy saved request current where
  machineStep : Derivation
    (RecursiveExecution.Contextual.Stateful.Protocol.Rule
      (AuthorizedAppend.environment authority required dispatch lookup) policy)
    1 {saved with world := current} [] (.exhausted (retainedFinal saved request current))
  serviceRun : (AuthorizedAppend.Retained.handled authority required).run 4
    (.running (.enter {saved with world := current})) =
      ([.requested {request with world := current},
        .performed ⟨PUnit.unit, current,
          .write (.append request.reader [request.argument]), .ok ()⟩,
        .replied (.returned
          (AuthorizedAppend.Retained.reachedWorld authority {request with world := current},
            [(.symbol "ack", request.frame)]))],
        .finished (.returned (retainedFinal saved request current)))
  stackRetained : (retainedFinal saved request current).stack = saved.stack
  publicationRetained : (retainedFinal saved request current).emitted = saved.emitted
  contextRetained : (retainedFinal saved request current).context = saved.context

/-- Ordered phases of the single shared retained interaction. -/
inductive JoinedPhase where
  | demand
  | service
  | reply
  | cache
  | done
  deriving DecidableEq, Repr

/-- One state contains the Need machine, retained HE configuration and issued
return registry together. -/
structure JoinedState
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld) (size : Nat) where
  phase : JoinedPhase
  need : NeedDependentService.ServiceMachine
    (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size)))
  he : AuthorizedAppend.Retained.Configuration authority (size := size)
  registry : RetainedRegistry size

/-- The joined transition relation: claim the Need cell, rebase the still-live
HE cut, execute and authenticate its reply, then commit that exact delivered
configuration to Need. Output registry witnesses are produced by the reply
edge, rather than fixed as parameters of the relation. -/
inductive JoinedStep
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld) {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (source : Nat)
    (saved : AuthorizedAppend.Retained.Configuration authority (size := size))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (current : AuthorizedAppend.Retained.World authority (size := size))
    (needWorld : NeedDependentService.ServiceWorld
      (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size))))
    (cell : CellId) (handle : RetainedHandle size) :
    JoinedState authority size → JoinedState authority size → Prop where
  | claim {registry : RetainedRegistry size}
      (ran : runFrontier
        (NeedDependentService.spec
          (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size)))
          (retainedProducer (retainedFinal saved request current))) 2
        [retainedNeedBefore needWorld cell (retainedKey saved request)] =
        [retainedNeedEvaluating needWorld cell (retainedKey saved request)]) :
      JoinedStep authority required dispatch lookup policy source saved request current
        needWorld cell handle
        ⟨.demand, retainedNeedBefore needWorld cell (retainedKey saved request),
          saved, registry⟩
        ⟨.service, retainedNeedEvaluating needWorld cell (retainedKey saved request),
          saved, registry⟩
  | rebase {registry : RetainedRegistry size}
      (advanced : RebaseAdvance authority required dispatch lookup policy saved request current) :
      JoinedStep authority required dispatch lookup policy source saved request current
        needWorld cell handle
        ⟨.service, retainedNeedEvaluating needWorld cell (retainedKey saved request),
          saved, registry⟩
        ⟨.reply, retainedNeedEvaluating needWorld cell (retainedKey saved request),
          {saved with world := current}, registry⟩
  | reply {registry next : RetainedRegistry size} {cleared : RetainedHandle size}
      (advanced : ServiceAdvance authority required dispatch lookup policy saved request current)
      (delivered : (deliverRetainedChecked required source saved current registry handle).1 =
        .ok (retainedFinal saved request current, next, cleared)) :
      JoinedStep authority required dispatch lookup policy source saved request current
        needWorld cell handle
        ⟨.reply, retainedNeedEvaluating needWorld cell (retainedKey saved request),
          {saved with world := current}, registry⟩
        ⟨.cache, retainedNeedEvaluating needWorld cell (retainedKey saved request),
          retainedFinal saved request current, next⟩
  | cache {registry : RetainedRegistry size}
      (ran : runFrontier
        (NeedDependentService.spec
          (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size)))
          (retainedProducer (retainedFinal saved request current))) 5
        [retainedNeedEvaluating needWorld cell (retainedKey saved request)] =
        [retainedNeedAfter needWorld cell (retainedKey saved request)
          (retainedFinal saved request current)]) :
      JoinedStep authority required dispatch lookup policy source saved request current
        needWorld cell handle
        ⟨.cache, retainedNeedEvaluating needWorld cell (retainedKey saved request),
          retainedFinal saved request current, registry⟩
        ⟨.done, retainedNeedAfter needWorld cell (retainedKey saved request)
          (retainedFinal saved request current), retainedFinal saved request current, registry⟩

/-- One shared retained trajectory: the reached HE service performs its pending
append, the exact delivered configuration is committed to one Need cell, and
the issued return row is consumed. Every later demand observes the cache, while
the copied pre-delivery handle cannot repeat the append/reply boundary. -/
theorem composed_retention_no_replay
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld) {size : Nat}
    (required : OrderedDependencyStore.Action Atom size →
      (world : AuthorityWorld) → authority.Fibre world)
    [permission : ∀ (point : IndexedAuthority.Point authority)
      (action : OrderedDependencyStore.Action Atom size),
      Decidable (FrameUpdate point.authority (required action point.world))]
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    {initial saved : AuthorizedAppend.Retained.Configuration authority (size := size)}
    {fuel : Nat} {events : List Result}
    (paused : Derivation
      (RecursiveExecution.Contextual.Stateful.Protocol.Rule
        (AuthorizedAppend.environment authority required dispatch lookup) policy)
      fuel initial events (.exhausted saved))
    (request : AuthorizedAppend.Retained.Request authority (size := size))
    (found : AuthorizedAppend.Retained.requested? authority saved = some request)
    (changes : List (OrderedDependencyStore.Action Atom size))
    (point : IndexedAuthority.Point authority)
    (lawful : OrderedDependencyStore.ObserverInvariant saved.world.store)
    (valid : OrderedDependencyStore.checkRead
      (OrderedDependencyStore.execute saved.world.store changes)
      (OrderedDependencyStore.readStamp saved.world.store request.reader) = true)
    (allowed : FrameUpdate point.authority
      (required (.append request.reader [request.argument]) point.world))
    (source : Nat) (registry : RetainedRegistry size) (handle : RetainedHandle size)
    (registryValid : registry.Valid) (matched : HandleMatches source request handle)
    (authenticated : IssuedReturn.Authenticated registry handle)
    (needWorld : NeedDependentService.ServiceWorld
      (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size))))
    (cell : CellId)
    (suspended : needWorld.heap.lookup cell =
      some ⟨((retainedKey saved request) : AppendKey size), .suspended⟩) :
    let current := retainedCurrent saved changes point
    let final := retainedFinal saved request current
    ∃ next cleared,
      Relation.TransGen
        (JoinedStep authority required dispatch lookup policy source saved request current
          needWorld cell handle)
        (⟨.demand,
          retainedNeedBefore needWorld cell (retainedKey saved request),
          saved, registry⟩ : JoinedState authority size)
        ⟨.done,
          retainedNeedAfter needWorld cell (retainedKey saved request) final,
          final, next⟩ ∧
      next.Valid ∧
      ¬IssuedReturn.Authenticated next cleared ∧
      (deliverRetainedChecked required source saved current next handle).1 = .error .unissued ∧
      AuthorizedAppend.Retained.requested? authority final = none ∧
      (∀ otherProducer : (key : (retainedFamily size
          (AuthorizedAppend.Retained.Configuration authority (size := size))).Raw) →
          (retainedFamily size
            (AuthorizedAppend.Retained.Configuration authority (size := size))).Exact key,
        runFrontier
            (NeedDependentService.spec
              (retainedFamily size
                (AuthorizedAppend.Retained.Configuration authority (size := size))) otherProducer) 5
            [retainedNeedCachedBefore needWorld cell (retainedKey saved request) final] =
          runFrontier
            (NeedDependentService.spec
              (retainedFamily size
                (AuthorizedAppend.Retained.Configuration authority (size := size)))
              (retainedProducer final)) 5
            [retainedNeedCachedBefore needWorld cell (retainedKey saved request) final]) := by
  dsimp only
  let current := retainedCurrent saved changes point
  let final := retainedFinal saved request current
  obtain ⟨rebased, sourceStable, requestRetained, machineStep, serviceRun,
      stackRetained, finalEmitted, contextRetained⟩ :=
    AuthorizedAppend.Retained.validated_resume_reached_cut authority required dispatch lookup
      policy paused request found changes point lawful valid allowed
  have savedEmitted :=
    (RecursiveExecution.Contextual.Stateful.Protocol.exhausted_steps paused).2
  have publicationRetained : final.emitted = saved.emitted :=
    finalEmitted.trans savedEmitted.symm
  have rebasedAdvance : RebaseAdvance authority required dispatch lookup policy
      saved request current :=
    ⟨rebased, sourceStable, requestRetained⟩
  have advanced : ServiceAdvance authority required dispatch lookup policy saved request current :=
    ⟨rebasedAdvance, machineStep, serviceRun,
      stackRetained, publicationRetained, contextRetained⟩
  obtain ⟨next, cleared, delivered, nextValid, revoked, clearedRevoked⟩ :=
    deliverRetainedChecked_admitted required source saved request current registry handle
      registryValid found matched valid allowed authenticated
  have needClaim : runFrontier
      (NeedDependentService.spec
        (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size)))
        (retainedProducer final)) 2
      [retainedNeedBefore needWorld cell (retainedKey saved request)] =
      [retainedNeedEvaluating needWorld cell (retainedKey saved request)] :=
    retainedNeed_claim needWorld cell (retainedKey saved request) final suspended
  have needFinish : runFrontier
      (NeedDependentService.spec
        (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size)))
        (retainedProducer final)) 5
      [retainedNeedEvaluating needWorld cell (retainedKey saved request)] =
      [retainedNeedAfter needWorld cell (retainedKey saved request) final] :=
    retainedNeed_commit_and_resume needWorld cell (retainedKey saved request) final
  have first : JoinedStep authority required dispatch lookup policy source saved request current
      needWorld cell handle
      (⟨.demand, retainedNeedBefore needWorld cell (retainedKey saved request),
        saved, registry⟩ : JoinedState authority size)
      ⟨.service, retainedNeedEvaluating needWorld cell (retainedKey saved request),
        saved, registry⟩ := .claim needClaim
  have second : JoinedStep authority required dispatch lookup policy source saved request current
      needWorld cell handle
      (⟨.service, retainedNeedEvaluating needWorld cell (retainedKey saved request),
        saved, registry⟩ : JoinedState authority size)
      ⟨.reply, retainedNeedEvaluating needWorld cell (retainedKey saved request),
        {saved with world := current}, registry⟩ := .rebase rebasedAdvance
  have third : JoinedStep authority required dispatch lookup policy source saved request current
      needWorld cell handle
      (⟨.reply, retainedNeedEvaluating needWorld cell (retainedKey saved request),
        {saved with world := current}, registry⟩ : JoinedState authority size)
      ⟨.cache, retainedNeedEvaluating needWorld cell (retainedKey saved request),
        final, next⟩ := .reply advanced delivered
  have fourth : JoinedStep authority required dispatch lookup policy source saved request current
      needWorld cell handle
      (⟨.cache, retainedNeedEvaluating needWorld cell (retainedKey saved request),
        final, next⟩ : JoinedState authority size)
      ⟨.done, retainedNeedAfter needWorld cell (retainedKey saved request) final,
        final, next⟩ := .cache needFinish
  refine ⟨next, cleared,
    Relation.TransGen.tail
      (Relation.TransGen.tail (Relation.TransGen.tail (.single first) second) third) fourth,
    nextValid, clearedRevoked, ?_, ?_, ?_⟩
  · exact deliverRetainedChecked_unissued required source saved request current next handle
      found matched valid allowed revoked
  · exact requested?_deliverConfiguration_none requestRetained
      (AuthorizedAppend.Retained.reachedWorld authority {request with world := current})
      [(.symbol "ack", request.frame)]
  · intro otherProducer
    exact NeedDependentService.cached_consumer_independent_of_producer
      (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size)))
      otherProducer (retainedProducer final) (retainedKey saved request) ({} : Work)
      (NeedDependentService.producedWorld_lookup
        (retainedFamily size (AuthorizedAppend.Retained.Configuration authority (size := size)))
        (retainedProducer final) needWorld cell (retainedKey saved request))

end Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention

#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComponentRealization.retained_run
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.retainedKey_ne_of_stale
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.checkRead_iff_canPublish
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.deliverRetainedChecked_admitted
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.deliverRetainedChecked_unissued
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.deliverRetainedChecked_stale
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.deliverRetainedChecked_denied
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.requested?_deliverConfiguration_none
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.retainedNeed_claim
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.retainedNeed_commit_and_resume
#print axioms Mettapedia.Languages.MeTTa.HE.RecursiveService.ComposedRetention.composed_retention_no_replay
