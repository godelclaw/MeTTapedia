import Mettapedia.Languages.MeTTa.HE.RecursiveExecution
import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution
import Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy
import Mettapedia.Machines.Cursor.ReadOnlyQuery
import Mettapedia.Machines.Cursor.ProductiveBlocks

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
