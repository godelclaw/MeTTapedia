import Mettapedia.GSLT.Core.InferenceRecording
import Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
import Mettapedia.GSLT.LanguageDef.CertificateGSLTCheckerCapabilities

/-!
# Recurrent GSLT certificates as productive occurrence routes

The recurrent CertificateGSLT checker already proves two distinct facts:
every controller edge is accepted by the authored local step authority, and an
accepting state recurs beyond every finite bound.  This module connects the
first fact to the occurrence-preserving finite-route algebra.

For every controlled execution and every demanded finite depth, an accepted
progress certificate constructs an exact route prefix.  Each occurrence keeps
its temporal index, source, checked action, and target, so repeated traversal
of one syntactic edge remains occurrence-distinct.  The route's history maps
to a genuine multi-step execution of the admitted GSLT.

Prefix productivity and Buechi recurrence remain separate properties.  A
locally valid nonaccepting loop has every finite prefix but no recurrent
acceptance certificate.  Neither property is promoted here to occurrence
fairness, finite closure, or complete-bag observation.

Continuing control reuses that same memoryless iteration.  A bounded advance
retains only the current state and is the canonical execution's iterate.
A requested note reads the action at that current state; it is not an input
to advancement and it does not rebuild a route from an execution.  Requested
recording is the existing `InferenceRecording.runSelected` loop on one live
indexed frontier node.  Each retained event is emitted by that bounded run.
Finite-state liveness is proved only for a controller with an explicit
yielding bound, or by the existing Büchi checker.  Iteration on an unbounded
carrier, and a finite label that recurs while a chosen identity is never
admitted, stay outside that claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities

universe uAuthority uCertificate

/-! ## The audited revision theory -/

/-- The local checked edge is the revision relation.  The unit query exposes
the current term only; recurrence remains a separate observation on the same
states. -/
def auditedRevisionTheory
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool) : Theory where
  World := theory.Term
  Revision := TraceLink theory stepAuthority.Certificate
  Query := Unit
  Observation := theory.Term
  Step := fun action source target =>
    (auditedLabeledSystem stepAuthority accepting).step
      source action target = true
  query := fun world _ => world

/-- One traversal occurrence is not merely an edge label.  Its temporal
position and endpoints remain part of its identity. -/
structure ControlledOccurrence
    (theory : GSLT)
    (StepCertificate : Type uCertificate) where
  index : Nat
  source : theory.Term
  action : TraceLink theory StepCertificate
  target : theory.Term

section Prefix

variable {AuthorityId : Type uAuthority} {theory : GSLT}
variable (stepAuthority : StepAuthority.{uAuthority, uCertificate}
  AuthorityId theory)
variable (accepting : theory.Term -> Bool)
variable (claim : RecurrentTraceClaim theory stepAuthority.Certificate)

/-- The exact occurrence performed at one controller index. -/
def occurrenceAt
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    ControlledOccurrence theory stepAuthority.Certificate where
  index := index
  source := execution.state index
  action := claim.controller.action (execution.state index)
  target := execution.state (index + 1)

/-- Chronological physical occurrence prefix. -/
def occurrencePrefix
    (execution : ControlledExecution claim.controller claim.root) :
    Nat -> List (ControlledOccurrence theory stepAuthority.Certificate)
  | 0 => []
  | depth + 1 => occurrencePrefix execution depth ++
      [occurrenceAt stepAuthority claim execution depth]

/-- Chronological semantic revision prefix, defined independently from the
physical occurrence projection. -/
def revisionPrefix
    (execution : ControlledExecution claim.controller claim.root) :
    Nat -> List (TraceLink theory stepAuthority.Certificate)
  | 0 => []
  | depth + 1 => revisionPrefix execution depth ++
      [claim.controller.action (execution.state depth)]

/-- Projecting the checked action from every occurrence recovers exactly the
independently defined semantic revision prefix. -/
theorem occurrencePrefix_actions
    (execution : ControlledExecution claim.controller claim.root) :
    forall depth,
      (occurrencePrefix stepAuthority claim execution depth).map
          (fun occurrence => occurrence.action) =
        revisionPrefix stepAuthority claim execution depth := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [occurrencePrefix, revisionPrefix, occurrenceAt,
        inductionHypothesis]

theorem occurrencePrefix_length
    (execution : ControlledExecution claim.controller claim.root) :
    forall depth,
      (occurrencePrefix stepAuthority claim execution depth).length =
        (revisionPrefix stepAuthority claim execution depth).length := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [occurrencePrefix, revisionPrefix, inductionHypothesis]

/-- Traversing the same labeled edge at two different indices still produces
distinct occurrences. -/
theorem occurrenceAt_index_injective
    (execution : ControlledExecution claim.controller claim.root)
    {first second : Nat} (different : first ≠ second) :
    occurrenceAt stepAuthority claim execution first ≠
      occurrenceAt stepAuthority claim execution second := by
  intro equalOccurrences
  exact different
    (congrArg ControlledOccurrence.index equalOccurrences)

variable [DecidableEq theory.Term]

/-- Local validity propagates along every controlled execution. -/
theorem execution_active
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root) :
    forall index, claim.controller.active (execution.state index) = true := by
  intro index
  induction index with
  | zero => simpa [execution.starts] using locallyValid.1
  | succ index inductionHypothesis =>
      rw [execution.follows index]
      exact (locallyValid.2 (execution.state index) inductionHypothesis).2

/-- Every selected controlled edge is accepted by the local authored step
authority at its exact occurrence index. -/
theorem audited_step_at
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    (auditedRevisionTheory stepAuthority accepting).Step
      (claim.controller.action (execution.state index))
      (execution.state index) (execution.state (index + 1)) := by
  have selected :=
    (locallyValid.2 (execution.state index)
      (execution_active stepAuthority accepting claim locallyValid execution index)).1
  rw [execution.follows index]
  exact selected

/-- The local checker soundness projects the same indexed edge to a genuine
step of the admitted GSLT. -/
theorem semantic_step_at
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    theory.Step (execution.state index) (execution.state (index + 1)) :=
  auditedLabeledSystem_step_sound stepAuthority accepting
    (audited_step_at stepAuthority accepting claim locallyValid execution index)

/-- Every demanded prefix has a checked chronological history. -/
theorem revisionPrefix_history
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root) :
    forall depth,
      (auditedRevisionTheory stepAuthority accepting).HistoryStep
        (revisionPrefix stepAuthority claim execution depth)
        claim.root (execution.state depth) := by
  intro depth
  induction depth with
  | zero =>
      change
        (auditedRevisionTheory stepAuthority accepting).HistoryStep []
          claim.root (execution.state 0)
      rw [execution.starts]
      exact @Theory.HistoryStep.nil
        (auditedRevisionTheory stepAuthority accepting) claim.root
  | succ depth inductionHypothesis =>
      simp only [revisionPrefix]
      exact inductionHypothesis.append
        (.single
          (audited_step_at stepAuthority accepting claim locallyValid execution depth))

/-- An audited revision history is also a genuine multi-step reduction in the
underlying GSLT after its occurrence evidence is forgotten. -/
theorem history_to_multistep
    : forall {revisions : List (TraceLink theory stepAuthority.Certificate)}
        {source target : theory.Term},
      (auditedRevisionTheory stepAuthority accepting).HistoryStep
          revisions source target ->
        theory.MultiStep source target
  | [], _, _, .nil world => .refl world
  | _ :: _, _, _, .cons checked rest =>
      .step (auditedLabeledSystem_step_sound stepAuthority accepting checked)
        (history_to_multistep rest)

/-- The canonical exact finite prefix obtained from local checker validity. -/
def finitePrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    FiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root where
  occurrences := occurrencePrefix stepAuthority claim execution depth
  revisions := revisionPrefix stepAuthority claim execution depth
  target := execution.state depth
  aligned := occurrencePrefix_length stepAuthority claim execution depth
  execution := revisionPrefix_history
    stepAuthority accepting claim locallyValid execution depth

/-- The one checked occurrence which extends a finite prefix by one step. -/
def atomicStep
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    FiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate)
      (execution.state index) :=
  FiniteRoute.single
    (occurrenceAt stepAuthority claim execution index)
    (claim.controller.action (execution.state index))
    (execution.state (index + 1))
    (audited_step_at stepAuthority accepting claim locallyValid execution index)

/-- Demanding one more element extends the same route by exactly one checked
occurrence.  Prefixes are therefore coherent views of one run, not unrelated
finite witnesses. -/
theorem finitePrefix_succ
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    finitePrefix stepAuthority accepting claim locallyValid execution
        (depth + 1) =
      (finitePrefix stepAuthority accepting claim locallyValid execution depth).append
        (atomicStep stepAuthority accepting claim locallyValid execution depth) := by
  apply FiniteRoute.ext <;> rfl

@[simp] theorem finitePrefix_occurrences
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (finitePrefix stepAuthority accepting claim locallyValid execution depth).occurrences =
      occurrencePrefix stepAuthority claim execution depth :=
  rfl

@[simp] theorem finitePrefix_revisions
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (finitePrefix stepAuthority accepting claim locallyValid execution depth).revisions =
      revisionPrefix stepAuthority claim execution depth :=
  rfl

@[simp] theorem finitePrefix_target
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (finitePrefix stepAuthority accepting claim locallyValid execution depth).target =
      execution.state depth :=
  rfl

/-- Each finite prefix reaches its endpoint by genuine GSLT reduction. -/
theorem finitePrefix_semantic
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    theory.MultiStep claim.root (execution.state depth) :=
  history_to_multistep stepAuthority accepting
    (finitePrefix stepAuthority accepting claim locallyValid execution depth).execution

/-- A prefix witness fixes all observable route data, rather than asserting
mere existence of some route from the root. -/
structure ExactPrefix
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) where
  route : FiniteRoute (auditedRevisionTheory stepAuthority accepting)
    (ControlledOccurrence theory stepAuthority.Certificate) claim.root
  occurrences_exact : route.occurrences =
    occurrencePrefix stepAuthority claim execution depth
  revisions_exact : route.revisions =
    revisionPrefix stepAuthority claim execution depth
  target_exact : route.target = execution.state depth

/-- Exact prefix productivity: every controlled execution can answer every
finite demand with the occurrence list, semantic revisions, and endpoint fixed
by that execution. -/
def AuditedPrefixProductive : Prop :=
  forall execution : ControlledExecution claim.controller claim.root,
    forall depth,
      Nonempty (ExactPrefix stepAuthority accepting claim execution depth)

/-- Local validity is sufficient for finite-prefix productivity.  Recurrence
is not used. -/
theorem prefixProductive_of_local
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root) :
    AuditedPrefixProductive stepAuthority accepting claim := by
  intro execution depth
  exact ⟨{
    route := finitePrefix stepAuthority accepting claim locallyValid execution depth
    occurrences_exact := rfl
    revisions_exact := rfl
    target_exact := rfl }⟩

/-- Acceptance by the ordinary recurrent checker constructs every exact
finite occurrence prefix. -/
theorem recurrentChecker_acceptance_implies_prefixProductive
    [Fintype theory.Term]
    (authorityId : AuthorityId)
    (measure : ProgressMeasure theory.Term)
    (accepted :
      (recurrentChecker authorityId stepAuthority accepting).check
        claim measure = true) :
    AuditedPrefixProductive stepAuthority accepting claim := by
  have valid : measure.Valid
      (auditedLabeledSystem stepAuthority accepting)
      claim.controller claim.root :=
    (ProgressMeasure.check_eq_true_iff
      (auditedLabeledSystem stepAuthority accepting)
      claim.controller measure claim.root).mp accepted
  exact prefixProductive_of_local stepAuthority accepting claim valid.1

/-- One accepted recurrent certificate supplies both finite-prefix
productivity and genuine recurrent GSLT meaning.  The conjunction keeps the
two obligations visible. -/
theorem recurrentChecker_acceptance_consequences
    [Fintype theory.Term]
    (authorityId : AuthorityId)
    (measure : ProgressMeasure theory.Term)
    (accepted :
      (recurrentChecker authorityId stepAuthority accepting).check
        claim measure = true) :
    AuditedPrefixProductive stepAuthority accepting claim /\
      claim.Meaning accepting := by
  exact ⟨recurrentChecker_acceptance_implies_prefixProductive
      stepAuthority accepting claim authorityId measure accepted,
    recurrentChecker_sound authorityId stepAuthority accepting
      claim measure accepted⟩

end Prefix

/-! ## Positive and negative recurrence controls -/

namespace Canary

/-- One state with one always-enabled rewrite is enough to distinguish finite
prefix productivity from recurrent acceptance. -/
@[reducible] def loopTheory : GSLT where
  Term := Unit
  equations :=
    ⟨fun _ _ => True,
      ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := fun _ _ => ⟨(), trivial, trivial⟩
  rewrites_resp_right := fun _ _ => trivial

def loopStepAuthority : StepAuthority Unit loopTheory where
  id := ()
  Certificate := Unit
  check := fun _ _ => true
  sound := fun _ => trivial

def loopController :
    MemorylessController loopTheory.Term
      (TraceLink loopTheory loopStepAuthority.Certificate) where
  active := fun _ => true
  action := fun _ => ⟨(), ()⟩
  next := fun _ => ()

def loopClaim :
    RecurrentTraceClaim loopTheory loopStepAuthority.Certificate where
  root := ()
  controller := loopController

def alwaysAccepting (_ : loopTheory.Term) : Bool := true
def neverAccepting (_ : loopTheory.Term) : Bool := false

def zeroMeasure : ProgressMeasure loopTheory.Term where
  rank := fun _ => 0

theorem loop_locally_valid (accepting : loopTheory.Term -> Bool) :
    loopController.LocallyValid
      (auditedLabeledSystem loopStepAuthority accepting) loopClaim.root := by
  constructor
  · rfl
  · intro state _
    cases state
    exact ⟨rfl, rfl⟩

/-- Positive control: the accepting loop passes the real recurrent checker. -/
theorem accepting_loop_checker_accepts :
    (recurrentChecker () loopStepAuthority alwaysAccepting).check
      loopClaim zeroMeasure = true := by
  decide

/-- The accepted loop consequently exposes every finite occurrence prefix and
genuine recurrent meaning. -/
theorem accepting_loop_has_both_consequences :
    AuditedPrefixProductive loopStepAuthority alwaysAccepting loopClaim /\
      loopClaim.Meaning alwaysAccepting :=
  recurrentChecker_acceptance_consequences loopStepAuthority alwaysAccepting
    loopClaim () zeroMeasure accepting_loop_checker_accepts

/-- Negative control: a nonaccepting loop still has every checked finite
prefix. -/
theorem nonaccepting_loop_prefixProductive :
    AuditedPrefixProductive loopStepAuthority neverAccepting loopClaim :=
  prefixProductive_of_local loopStepAuthority neverAccepting loopClaim
    (loop_locally_valid neverAccepting)

/-- But finite-prefix productivity does not imply Buechi recurrence. -/
theorem nonaccepting_loop_not_recurrent :
    ¬ loopController.BuchiWinning
      (auditedLabeledSystem loopStepAuthority neverAccepting) loopClaim.root := by
  intro recurrent
  obtain ⟨visit, _lower, accepted⟩ :=
    recurrent (loopController.canonicalExecution loopClaim.root) 0
  simp [auditedLabeledSystem, neverAccepting] at accepted

theorem prefixProductivity_does_not_imply_recurrence :
    AuditedPrefixProductive loopStepAuthority neverAccepting loopClaim /\
      ¬ loopController.BuchiWinning
        (auditedLabeledSystem loopStepAuthority neverAccepting)
        loopClaim.root :=
  ⟨nonaccepting_loop_prefixProductive,
    nonaccepting_loop_not_recurrent⟩

/-- Soundness forbids any progress measure from making the nonaccepting loop
pass the recurrent checker. -/
theorem nonaccepting_loop_rejects_every_measure
    (measure : ProgressMeasure loopTheory.Term) :
    (recurrentChecker () loopStepAuthority neverAccepting).check
      loopClaim measure = false := by
  cases checked :
      (recurrentChecker () loopStepAuthority neverAccepting).check
        loopClaim measure with
  | false => rfl
  | true =>
      have meaning := recurrentChecker_sound () loopStepAuthority
        neverAccepting loopClaim measure checked
      have recurrent : loopController.BuchiWinning
          (auditedLabeledSystem loopStepAuthority neverAccepting)
          loopClaim.root := by
        intro execution lowerBound
        exact (meaning execution).2 lowerBound
      exact False.elim (nonaccepting_loop_not_recurrent recurrent)

end Canary

/-! ## Trace-free bounded advancement

`MemorylessController.canonicalExecution` already iterates `controller.next`.
The algorithm below is that iteration, started from the current state and
stopped at a finite fuel.  It does not store occurrences, revisions, or a
recording.
-/

section Advance

variable {State Action : Type*}

/-- Advance a memoryless controller by `fuel` steps.  The result is the
current state alone.  This is the iterate already used by
`MemorylessController.canonicalExecution`. -/
def advanceState
    (controller : MemorylessController State Action)
    (fuel : Nat) (state : State) : State :=
  controller.next^[fuel] state

theorem advanceState_canonical
    (controller : MemorylessController State Action)
    (root : State) (fuel : Nat) :
    advanceState controller fuel root =
      (controller.canonicalExecution root).state fuel :=
  rfl

/-- One optional observation of the action at the current phase.  `false`
records nothing.  The note is not supplied to `advanceState`. -/
def currentNote
    (requested : Bool)
    (controller : MemorylessController State Action)
    (phase : State) : Option Action :=
  if requested then some (controller.action phase) else none

theorem currentNote_absent
    (controller : MemorylessController State Action) (phase : State) :
    currentNote false controller phase = none :=
  rfl

theorem currentNote_present
    (controller : MemorylessController State Action) (phase : State) :
    currentNote true controller phase =
      some (controller.action phase) :=
  rfl

theorem currentNote_requested_iff
    (requested : Bool)
    (controller : MemorylessController State Action)
    (phase : State) :
    (currentNote requested controller phase).isSome = requested := by
  cases requested <;> rfl

/-- Noting the current phase and advancing from it do not exchange data.
The advanced component is only the controller iterate. -/
theorem note_does_not_enter_advance
    (requested : Bool)
    (controller : MemorylessController State Action)
    (fuel : Nat) (phase : State) :
    (advanceState controller fuel phase,
      currentNote requested controller phase).1 =
      controller.next^[fuel] phase :=
  rfl

theorem advanceState_succ
    (controller : MemorylessController State Action)
    (fuel : Nat) (state : State) :
    advanceState controller (fuel + 1) state =
      controller.next (advanceState controller fuel state) := by
  unfold advanceState
  exact Function.iterate_succ_apply' controller.next fuel state

/-- Every controlled execution is the controller's iteration from its root.
The occurrence route is not an input. -/
theorem controlledExecution_state_iterate
    (controller : MemorylessController State Action)
    {root : State}
    (execution : ControlledExecution controller root)
    (index : Nat) :
    execution.state index = controller.next^[index] root := by
  induction index with
  | zero =>
      rw [Function.iterate_zero_apply]
      exact execution.starts
  | succ index inductionHypothesis =>
      rw [execution.follows, inductionHypothesis]
      exact (Function.iterate_succ_apply' controller.next index root).symm

theorem advanceState_execution
    (controller : MemorylessController State Action)
    {root : State}
    (execution : ControlledExecution controller root)
    (fuel : Nat) :
    advanceState controller fuel root = execution.state fuel := by
  unfold advanceState
  exact (controlledExecution_state_iterate controller execution fuel).symm

theorem advanceState_shift
    (controller : MemorylessController State Action)
    {root : State}
    (execution : ControlledExecution controller root)
    (start fuel : Nat) :
    advanceState controller fuel (execution.state start) =
      execution.state (start + fuel) := by
  induction fuel with
  | zero =>
      unfold advanceState
      rw [Function.iterate_zero_apply, Nat.add_zero]
  | succ fuel inductionHypothesis =>
      rw [advanceState_succ, inductionHypothesis, Nat.add_succ,
        ← execution.follows (start + fuel)]

/-- Recurrent acceptance from an explicit finite admission bound.  The bound
is a hypothesis about this controller.  It is not a fairness theorem for an
arbitrary identity supply, and it does not replace `ProgressMeasure.buchi_sound`. -/
theorem buchi_of_bounded_admission
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action}
    {root : State}
    (period : Nat)
    (admits :
      ∀ execution : ControlledExecution controller root,
        ∀ start,
          ∃ offset, offset ≤ period ∧
            system.accepting (execution.state (start + offset)) = true) :
    controller.BuchiWinning system root := by
  intro execution lowerBound
  obtain ⟨offset, _, accepted⟩ := admits execution lowerBound
  exact ⟨lowerBound + offset, Nat.le_add_right lowerBound offset, accepted⟩

end Advance

section TraceFree

variable {AuthorityId : Type uAuthority} {theory : GSLT}
variable (stepAuthority : StepAuthority.{uAuthority, uCertificate}
  AuthorityId theory)
variable (accepting : theory.Term -> Bool)
variable (claim : RecurrentTraceClaim theory stepAuthority.Certificate)

/-- The actions read off the trace-free iteration are the semantic revision
prefix.  The iteration itself does not retain that list. -/
theorem revisionPrefix_eq_advancedActions
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    revisionPrefix stepAuthority claim execution depth =
      (List.range depth).map fun index =>
        claim.controller.action
          (advanceState claim.controller index claim.root) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [revisionPrefix, List.range_succ, List.map_append, List.map_singleton,
        inductionHypothesis]
      exact congrArg
        (fun action =>
          (List.range depth).map (fun index =>
            claim.controller.action
              (advanceState claim.controller index claim.root)) ++
            [action])
        (congrArg claim.controller.action
          (advanceState_execution claim.controller execution depth).symm)

theorem revisionPrefix_advanced_length
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (revisionPrefix stepAuthority claim execution depth).length = depth := by
  rw [revisionPrefix_eq_advancedActions]
  simp [List.length_map, List.length_range]

/-- Each indexed occurrence is the current advanced state, its selected
action, and the next advanced state. -/
theorem occurrenceAt_advance
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    (occurrenceAt stepAuthority claim execution index).source =
        advanceState claim.controller index claim.root ∧
      (occurrenceAt stepAuthority claim execution index).target =
        advanceState claim.controller (index + 1) claim.root ∧
      (occurrenceAt stepAuthority claim execution index).action =
        claim.controller.action
          (advanceState claim.controller index claim.root) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [occurrenceAt]
    exact (advanceState_execution claim.controller execution index).symm
  · dsimp only [occurrenceAt]
    exact (advanceState_execution claim.controller execution (index + 1)).symm
  · dsimp only [occurrenceAt]
    exact congrArg claim.controller.action
      (advanceState_execution claim.controller execution index).symm

variable [DecidableEq theory.Term]

/-- The route demanded at `fuel` is the existing occurrence route.  Its
endpoint is the trace-free iterate; the prefix lists are not recomputed. -/
theorem advance_agrees_with_route
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (fuel : Nat) :
    (finitePrefix stepAuthority accepting claim locallyValid execution fuel).target =
        advanceState claim.controller fuel claim.root ∧
      (finitePrefix stepAuthority accepting claim locallyValid execution fuel).revisions =
        revisionPrefix stepAuthority claim execution fuel ∧
      (finitePrefix stepAuthority accepting claim locallyValid execution fuel).occurrences =
        occurrencePrefix stepAuthority claim execution fuel := by
  refine ⟨?_, ?_, ?_⟩
  · rw [finitePrefix_target]
    exact (advanceState_execution claim.controller execution fuel).symm
  · exact finitePrefix_revisions
      stepAuthority accepting claim locallyValid execution fuel
  · exact finitePrefix_occurrences
      stepAuthority accepting claim locallyValid execution fuel

/-- Ordinary GSLT execution of the advanced state.  The multi-step witness is
the existing audited history, not a second evaluator. -/
theorem advance_executes
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (fuel : Nat) :
    theory.MultiStep claim.root
      (advanceState claim.controller fuel claim.root) := by
  have targetEq :=
    (advance_agrees_with_route stepAuthority accepting claim
      locallyValid execution fuel).1
  rw [← targetEq]
  exact finitePrefix_semantic stepAuthority accepting claim
    locallyValid execution fuel

end TraceFree

/-! ## A finite heartbeat and service monitor

The carrier is three phases.  Yielding admission cycles through a heartbeat,
a waiting phase, and a serving phase.  Starvation leaves the heartbeat and
then remains waiting.  Both controllers are ordinary memoryless controllers
on this finite carrier.  Nothing here says an arbitrary infinite-state agent
is a finite automaton, or that a finite label fairly serves every identity.
-/

namespace Monitor

inductive Phase where
  | heartbeat
  | waiting
  | serving
  deriving DecidableEq, Repr

instance : Fintype Phase :=
  Fintype.ofList [.heartbeat, .waiting, .serving] (by
    intro phase
    cases phase <;> simp)

inductive Command where
  | beat
  | yield
  | resume
  | starve
  deriving DecidableEq, Repr

/-- Legal monitor edges: the yielding cycle, and the waiting self-loop used
by the starving control. -/
def rewrites : Phase → Phase → Prop
  | .heartbeat, .waiting => True
  | .waiting, .serving => True
  | .waiting, .waiting => True
  | .serving, .heartbeat => True
  | _, _ => False

@[reducible] def theory : GSLT where
  Term := Phase
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := rewrites
  rewrites_resp_left := by
    intro source source' target equivalent step
    cases equivalent
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    cases equivalent
    exact step

def admits : Phase → Phase → Command → Bool
  | .heartbeat, .waiting, .beat => true
  | .waiting, .serving, .yield => true
  | .serving, .heartbeat, .resume => true
  | .waiting, .waiting, .starve => true
  | _, _, _ => false

theorem admits_sound
    {source target : Phase} {command : Command}
    (accepted : admits source target command = true) :
    theory.Step source target := by
  cases source <;> cases target <;> cases command <;>
    simp [admits, GSLT.Step, rewrites] at accepted ⊢

def stepAuthority : StepAuthority Unit theory where
  id := ()
  Certificate := Command
  check := fun claim certificate =>
    admits claim.source claim.target certificate
  sound := by
    intro claim certificate accepted
    cases claim with
    | mk source target =>
        exact admits_sound accepted

/-- Service is the accepting phase.  A heartbeat is visible and is not itself
acceptance. -/
def serviceAccepting : Phase → Bool
  | .serving => true
  | _ => false

def yieldingController :
    MemorylessController theory.Term
      (TraceLink theory stepAuthority.Certificate) where
  active := fun _ => true
  action := fun phase =>
    match phase with
    | .heartbeat => ⟨.waiting, .beat⟩
    | .waiting => ⟨.serving, .yield⟩
    | .serving => ⟨.heartbeat, .resume⟩
  next := fun phase =>
    match phase with
    | .heartbeat => .waiting
    | .waiting => .serving
    | .serving => .heartbeat

def yieldingClaim : RecurrentTraceClaim theory stepAuthority.Certificate where
  root := .heartbeat
  controller := yieldingController

def yieldingMeasure : ProgressMeasure theory.Term where
  rank := fun phase =>
    match phase with
    | .heartbeat => 2
    | .waiting => 1
    | .serving => 0

def starvingController :
    MemorylessController theory.Term
      (TraceLink theory stepAuthority.Certificate) where
  active := fun _ => true
  action := fun phase =>
    match phase with
    | .heartbeat => ⟨.waiting, .beat⟩
    | .waiting => ⟨.waiting, .starve⟩
    | .serving => ⟨.heartbeat, .resume⟩
  next := fun phase =>
    match phase with
    | .heartbeat => .waiting
    | .waiting => .waiting
    | .serving => .heartbeat

def starvingClaim : RecurrentTraceClaim theory stepAuthority.Certificate where
  root := .heartbeat
  controller := starvingController

theorem yielding_not_identity :
    yieldingController.next .heartbeat ≠ .heartbeat := by
  intro equal
  cases equal

theorem yielding_not_constant :
    yieldingController.next .heartbeat ≠ yieldingController.next .waiting := by
  intro equal
  cases equal

theorem yielding_heartbeat_and_service :
    (yieldingController.action .heartbeat).evidence = .beat ∧
      (yieldingController.action .waiting).evidence = .yield ∧
      (yieldingController.action .serving).evidence = .resume :=
  ⟨rfl, rfl, rfl⟩

theorem yielding_period (phase : Phase) :
    advanceState yieldingController 3 phase = phase := by
  have zero : advanceState yieldingController 0 phase = phase := by
    unfold advanceState
    rw [Function.iterate_zero_apply]
  rw [show (3 : Nat) = 2 + 1 from rfl, advanceState_succ,
    show (2 : Nat) = 1 + 1 from rfl, advanceState_succ,
    show (1 : Nat) = 0 + 1 from rfl, advanceState_succ, zero]
  cases phase <;> rfl

theorem yielding_locally_valid :
    yieldingController.LocallyValid
      (auditedLabeledSystem stepAuthority serviceAccepting)
      yieldingClaim.root := by
  have checked :
      yieldingController.checkLocal
        (auditedLabeledSystem stepAuthority serviceAccepting)
        yieldingClaim.root = true := by
    decide
  exact (MemorylessController.checkLocal_eq_true_iff
    (auditedLabeledSystem stepAuthority serviceAccepting)
    yieldingController yieldingClaim.root).mp checked

theorem starving_locally_valid :
    starvingController.LocallyValid
      (auditedLabeledSystem stepAuthority serviceAccepting)
      starvingClaim.root := by
  have checked :
      starvingController.checkLocal
        (auditedLabeledSystem stepAuthority serviceAccepting)
        starvingClaim.root = true := by
    decide
  exact (MemorylessController.checkLocal_eq_true_iff
    (auditedLabeledSystem stepAuthority serviceAccepting)
    starvingController starvingClaim.root).mp checked

/-- From every phase of the yielding cycle, service is reached within two
further steps.  This is the admission hypothesis, read off `follows`. -/
theorem yielding_service_within
    (execution : ControlledExecution yieldingController yieldingClaim.root)
    (start : Nat) :
    ∃ offset, offset ≤ 2 ∧ execution.state (start + offset) = .serving := by
  cases phase : execution.state start with
  | serving =>
      exact ⟨0, Nat.zero_le _, by rw [Nat.add_zero]; exact phase⟩
  | waiting =>
      refine ⟨1, Nat.le_succ 1, ?_⟩
      have stepped := execution.follows start
      rw [phase] at stepped
      rw [stepped]
      rfl
  | heartbeat =>
      refine ⟨2, Nat.le_refl _, ?_⟩
      have first := execution.follows start
      have second := execution.follows (start + 1)
      rw [phase] at first
      rw [first] at second
      rw [(Nat.add_assoc start 1 1).symm, second]
      rfl

theorem yielding_heartbeat_within
    (execution : ControlledExecution yieldingController yieldingClaim.root)
    (start : Nat) :
    ∃ offset, offset ≤ 2 ∧ execution.state (start + offset) = .heartbeat := by
  cases phase : execution.state start with
  | heartbeat =>
      exact ⟨0, Nat.zero_le _, by rw [Nat.add_zero]; exact phase⟩
  | serving =>
      refine ⟨1, Nat.le_succ 1, ?_⟩
      have stepped := execution.follows start
      rw [phase] at stepped
      rw [stepped]
      rfl
  | waiting =>
      refine ⟨2, Nat.le_refl _, ?_⟩
      have first := execution.follows start
      have second := execution.follows (start + 1)
      rw [phase] at first
      rw [first] at second
      rw [(Nat.add_assoc start 1 1).symm, second]
      rfl

theorem yielding_buchi_of_admission :
    yieldingController.BuchiWinning
      (auditedLabeledSystem stepAuthority serviceAccepting)
      yieldingClaim.root :=
  buchi_of_bounded_admission 2 fun execution start => by
    obtain ⟨offset, bound, phase⟩ := yielding_service_within execution start
    refine ⟨offset, bound, ?_⟩
    rw [phase]
    rfl

/-- The existing recurrent checker accepts the yielding monitor. -/
theorem yielding_checker_accepts :
    (recurrentChecker () stepAuthority serviceAccepting).check
      yieldingClaim yieldingMeasure = true := by
  decide

theorem yielding_recurrent :
    AuditedPrefixProductive stepAuthority serviceAccepting yieldingClaim ∧
      yieldingClaim.Meaning serviceAccepting :=
  recurrentChecker_acceptance_consequences stepAuthority serviceAccepting
    yieldingClaim () yieldingMeasure yielding_checker_accepts

theorem yielding_advance_executes (fuel : Nat) :
    theory.MultiStep yieldingClaim.root
      (advanceState yieldingController fuel yieldingClaim.root) :=
  advance_executes stepAuthority serviceAccepting yieldingClaim
    yielding_locally_valid
    (yieldingController.canonicalExecution yieldingClaim.root) fuel

/-- After the first heartbeat the starving controller remains waiting, so the
service phase is never entered. -/
theorem starving_after_first
    (execution : ControlledExecution starvingController starvingClaim.root)
    (index : Nat) :
    execution.state (index + 1) = .waiting := by
  induction index with
  | zero =>
      rw [execution.follows, execution.starts]
      rfl
  | succ index inductionHypothesis =>
      rw [execution.follows, inductionHypothesis]
      rfl

theorem starving_not_recurrent :
    ¬ starvingController.BuchiWinning
        (auditedLabeledSystem stepAuthority serviceAccepting)
        starvingClaim.root := by
  intro winning
  obtain ⟨visit, lower, accepted⟩ :=
    winning (starvingController.canonicalExecution starvingClaim.root) 1
  have phase :=
    starving_after_first
      (starvingController.canonicalExecution starvingClaim.root) (visit - 1)
  have visitEq : (visit - 1) + 1 = visit := Nat.sub_add_cancel lower
  rw [visitEq] at phase
  rw [phase] at accepted
  change serviceAccepting .waiting = true at accepted
  exact Bool.false_ne_true accepted

theorem starving_admission_fails :
    ¬ ∀ execution : ControlledExecution starvingController starvingClaim.root,
        ∀ start, ∃ offset, offset ≤ 2 ∧
          serviceAccepting (execution.state (start + offset)) = true := by
  intro admits
  have execution := starvingController.canonicalExecution starvingClaim.root
  obtain ⟨offset, _, served⟩ := admits execution 1
  have phase := starving_after_first execution offset
  have notServing : serviceAccepting (execution.state (1 + offset)) = false := by
    rw [Nat.add_comm, phase]
    rfl
  rw [notServing] at served
  exact Bool.false_ne_true served

theorem starving_prefixProductive :
    AuditedPrefixProductive stepAuthority serviceAccepting starvingClaim :=
  prefixProductive_of_local stepAuthority serviceAccepting starvingClaim
    starving_locally_valid

theorem starvation_separates_prefix_from_recurrence :
    AuditedPrefixProductive stepAuthority serviceAccepting starvingClaim ∧
      ¬ starvingController.BuchiWinning
          (auditedLabeledSystem stepAuthority serviceAccepting)
          starvingClaim.root :=
  ⟨starving_prefixProductive, starving_not_recurrent⟩

theorem starving_rejects_every_measure
    (measure : ProgressMeasure theory.Term) :
    (recurrentChecker () stepAuthority serviceAccepting).check
      starvingClaim measure = false := by
  cases checked :
      (recurrentChecker () stepAuthority serviceAccepting).check
        starvingClaim measure with
  | false => rfl
  | true =>
      have meaning := recurrentChecker_sound () stepAuthority
        serviceAccepting starvingClaim measure checked
      have recurrent : starvingController.BuchiWinning
          (auditedLabeledSystem stepAuthority serviceAccepting)
          starvingClaim.root := by
        intro execution lowerBound
        exact (meaning execution).2 lowerBound
      exact False.elim (starving_not_recurrent recurrent)

theorem starving_leaves_heartbeat :
    starvingController.next .heartbeat = .waiting ∧
      starvingController.next .waiting = .waiting ∧
      (starvingController.action .waiting).evidence = .starve :=
  ⟨rfl, rfl, rfl⟩

end Monitor

/-! ## Indexed frontier recording

`runIndexed` is the existing `InferenceRecording.runSelected` loop.  The live
frontier is one indexed phase.  A requested record is whatever that bounded
run emits.  `recordedStep` is only the agreement target: it is the trace-free
iterate, and it is not an input to the run.
-/

/-- A phase tagged by the number of steps that produced it. -/
structure IndexedPhase (State : Type*) where
  index : Nat
  phase : State

/-- The occurrence read off one selected step. -/
structure StepRecord (State Action : Type*) where
  index : Nat
  source : State
  action : Action
  target : State

section IndexedFrontier

variable {State Action : Type*}

open Mettapedia.GSLT.Core.BranchingTemporal hiding Snapshot
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.InferenceControl.Recording

/-- One successor, indexed one step later.  Emission is the controller's
action at the current phase. -/
def indexedSystem (controller : MemorylessController State Action) :
    BranchingSystem (IndexedPhase State) Action where
  emit node := some (controller.action node.phase)
  successors node :=
    [{ index := node.index + 1, phase := controller.next node.phase }]

/-- Breadth-first selection with no controller memory.  The live phase is the
frontier node, not the memory. -/
def indexedController : Controller (IndexedPhase State) Action Unit :=
  Controller.fixed Scheduler.breadthFirst

/-- The run starts at the root, at index zero, with that single node live. -/
def indexedRoot (root : State) : Snapshot (IndexedPhase State) Action Unit :=
  Snapshot.initial indexedController [{ index := 0, phase := root }]

/-- Read the selected node, the emitted answer, and the generated successor.
The `none` and empty branches only make the observer total. -/
def observeStep (controller : MemorylessController State Action)
    (_memory : Unit) (node : IndexedPhase State) :
    Option Action → List (IndexedPhase State) → StepRecord State Action
  | some action, next :: _ =>
      { index := node.index, source := node.phase, action := action,
        target := next.phase }
  | none, next :: _ =>
      { index := node.index, source := node.phase,
        action := controller.action node.phase, target := next.phase }
  | some action, [] =>
      { index := node.index, source := node.phase, action := action,
        target := node.phase }
  | none, [] =>
      { index := node.index, source := node.phase,
        action := controller.action node.phase, target := node.phase }

/-- Run the existing selected loop for `fuel` steps.  `capacity` chooses
whether that loop retains a bounded record. -/
def runIndexed (controller : MemorylessController State Action)
    (root : State) (fuel : Nat) (capacity : Option Nat) :=
  runSelected (indexedSystem controller) indexedController
    (observeStep controller) fuel (start (indexedRoot root) capacity)

/-- Continue an ordinary unrecorded prefix, then emit records only for the
later bounded run. -/
def runIndexedLate (controller : MemorylessController State Action)
    (root : State) (first second capacity : Nat) :=
  runSelected (indexedSystem controller) indexedController
    (observeStep controller) second
    (start
      (Snapshot.run (indexedSystem controller) indexedController first
        (indexedRoot root))
      (some capacity))

/-- One step of the trace-free iterate.  This describes the event the selected
loop emits; the loop does not read this definition. -/
def recordedStep (controller : MemorylessController State Action)
    (root : State) (index : Nat) : StepRecord State Action where
  index := index
  source := advanceState controller index root
  action := controller.action (advanceState controller index root)
  target := advanceState controller (index + 1) root

/-- The finite occurrence list of the trace-free iterate. -/
def recordedPrefix (controller : MemorylessController State Action)
    (root : State) (fuel : Nat) : List (StepRecord State Action) :=
  (List.range fuel).map (recordedStep controller root)

theorem recordedPrefix_length
    (controller : MemorylessController State Action) (root : State)
    (fuel : Nat) :
    (recordedPrefix controller root fuel).length = fuel := by
  unfold recordedPrefix
  rw [List.length_map, List.length_range]

/-- One breadth-first step on a singleton frontier replaces that node by the
successor the indexed system generated. -/
theorem indexed_tick_frontier
    (controller : MemorylessController State Action)
    (snapshot : Snapshot (IndexedPhase State) Action Unit)
    (index : Nat) (phase : State)
    (frontierSingleton : snapshot.search.frontier =
      [{ index := index, phase := phase }]) :
    (Snapshot.tick (indexedSystem controller) indexedController
        snapshot).search.frontier =
      [{ index := index + 1, phase := controller.next phase }] := by
  cases snapshot with
  | mk search memory =>
    cases search with
    | mk events frontier =>
      have frontierEq : frontier = [{ index := index, phase := phase }] :=
        frontierSingleton
      rw [frontierEq]
      unfold indexedSystem indexedController Controller.fixed Snapshot.tick
        Mettapedia.GSLT.Core.BranchingTemporal.tick Scheduler.breadthFirst
      rfl

/-- The head selected by the ordinary loop is the controller step at that
phase.  The event comes from `emit` and `successors`, not from a stored path. -/
theorem indexed_selected_step
    (controller : MemorylessController State Action)
    (snapshot : Snapshot (IndexedPhase State) Action Unit)
    (index : Nat) (phase : State)
    (frontierSingleton : snapshot.search.frontier =
      [{ index := index, phase := phase }]) :
    next (indexedSystem controller) indexedController (observeStep controller)
        snapshot =
      some (StepRecord.mk index phase (controller.action phase)
        (controller.next phase)) := by
  cases snapshot with
  | mk search memory =>
    cases search with
    | mk events frontier =>
      have frontierEq : frontier = [{ index := index, phase := phase }] :=
        frontierSingleton
      rw [frontierEq]
      unfold next indexedSystem indexedController Controller.fixed observeStep
        Scheduler.breadthFirst
      rfl

/-- The ordinary unrecorded loop ends at the indexed `advanceState` node. -/
theorem indexed_run_frontier
    (controller : MemorylessController State Action) (root : State)
    (fuel : Nat) :
    (Snapshot.run (indexedSystem controller) indexedController fuel
        (indexedRoot root)).search.frontier =
      [{ index := fuel, phase := advanceState controller fuel root }] := by
  induction fuel with
  | zero =>
      unfold Snapshot.run indexedRoot Snapshot.initial
        Mettapedia.GSLT.Core.BranchingTemporal.initial advanceState
      rw [Function.iterate_zero_apply]
  | succ fuel inductionHypothesis =>
      rw [Snapshot.run,
        indexed_tick_frontier controller
          (Snapshot.run (indexedSystem controller) indexedController fuel
            (indexedRoot root))
          fuel (advanceState controller fuel root) inductionHypothesis,
        advanceState_succ]

/-- Every optional record uses the same selected execution.  For every
capacity, including no record, the frontier is the `advanceState` endpoint. -/
theorem runIndexed_frontier_eq_advanceState
    (controller : MemorylessController State Action) (root : State)
    (fuel : Nat) (capacity : Option Nat) :
    (runIndexed controller root fuel capacity).search.frontier =
      [{ index := fuel, phase := advanceState controller fuel root }] := by
  unfold runIndexed
  have erased :=
    runSelected_erasure (indexedSystem controller) indexedController
      (observeStep controller) fuel (start (indexedRoot root) capacity)
  rw [erase_start] at erased
  have searchSame :
      (runSelected (indexedSystem controller) indexedController
          (observeStep controller) fuel
          (start (indexedRoot root) capacity)).search =
        (erase (runSelected (indexedSystem controller) indexedController
          (observeStep controller) fuel
          (start (indexedRoot root) capacity))).search :=
    rfl
  rw [searchSame, erased]
  exact indexed_run_frontier controller root fuel

/-- Erasing the record restores the ordinary unrecorded run. -/
theorem runIndexed_erasure
    (controller : MemorylessController State Action) (root : State)
    (fuel : Nat) (capacity : Option Nat) :
    erase (runIndexed controller root fuel capacity) =
      Snapshot.run (indexedSystem controller) indexedController fuel
        (indexedRoot root) := by
  unfold runIndexed
  rw [runSelected_erasure, erase_start]

/-- The observation stream of the ordinary loop is the trace-free prefix. -/
theorem indexed_stream
    (controller : MemorylessController State Action) (root : State)
    (fuel : Nat) :
    stream (indexedSystem controller) indexedController (observeStep controller)
        fuel (indexedRoot root) =
      recordedPrefix controller root fuel := by
  induction fuel with
  | zero =>
      unfold stream recordedPrefix
      rw [List.range_zero, List.map_nil]
  | succ fuel inductionHypothesis =>
      rw [stream, inductionHypothesis,
        indexed_selected_step controller
          (Snapshot.run (indexedSystem controller) indexedController fuel
            (indexedRoot root))
          fuel (advanceState controller fuel root)
          (indexed_run_frontier controller root fuel),
        Option.toList_some, ← advanceState_succ]
      unfold recordedPrefix
      rw [List.range_succ, List.map_append, List.map_singleton]
      unfold recordedStep
      rfl

/-- The same stream, read after an unrecorded prefix, continues at that index. -/
theorem indexed_stream_shifted
    (controller : MemorylessController State Action) (root : State)
    (startIndex fuel : Nat) :
    stream (indexedSystem controller) indexedController (observeStep controller)
        fuel
        (Snapshot.run (indexedSystem controller) indexedController startIndex
          (indexedRoot root)) =
      (List.range fuel).map fun offset =>
        recordedStep controller root (startIndex + offset) := by
  induction fuel with
  | zero =>
      unfold stream
      rw [List.range_zero, List.map_nil]
  | succ fuel inductionHypothesis =>
      rw [stream, inductionHypothesis]
      have frontierShift :
          (Snapshot.run (indexedSystem controller) indexedController fuel
              (Snapshot.run (indexedSystem controller) indexedController
                startIndex (indexedRoot root))).search.frontier =
            [{ index := startIndex + fuel,
               phase := advanceState controller (startIndex + fuel) root }] := by
        rw [← Snapshot.run_add]
        exact indexed_run_frontier controller root (startIndex + fuel)
      rw [indexed_selected_step controller _ (startIndex + fuel)
            (advanceState controller (startIndex + fuel) root) frontierShift,
          Option.toList_some, ← advanceState_succ, List.range_succ,
          List.map_append, List.map_singleton]
      unfold recordedStep
      rfl

/-- The retained prefix is the existing bounded recording of this stream. -/
theorem runIndexed_record
    (controller : MemorylessController State Action) (root : State)
    (fuel : Nat) (capacity : Option Nat) :
    (runIndexed controller root fuel capacity).memory.2 =
      Recording.append (Recording.initial capacity)
        (recordedPrefix controller root fuel) := by
  unfold runIndexed
  rw [runSelected_record, erase_start, indexed_stream]
  rfl

/-- Disabled recording stores no prefix and keeps the recorded run's frontier. -/
theorem runIndexed_disabled
    (controller : MemorylessController State Action) (root : State)
    (fuel : Nat) :
    (runIndexed controller root fuel none).memory.2 = none ∧
      (runIndexed controller root fuel none).search.frontier =
        (runIndexed controller root fuel (some 0)).search.frontier := by
  constructor
  · rw [runIndexed_record]
    rfl
  · rw [runIndexed_frontier_eq_advanceState, runIndexed_frontier_eq_advanceState]

/-- A requested capacity that covers the run presents the whole emitted prefix. -/
theorem runIndexed_complete
    (controller : MemorylessController State Action) (root : State)
    (fuel capacity : Nat) (fits : fuel ≤ capacity) :
    ((runIndexed controller root fuel (some capacity)).memory.2).bind
        Prefix.complete? =
      some (recordedPrefix controller root fuel) := by
  rw [runIndexed_record]
  have expanded :
      Recording.append (Recording.initial (some capacity))
          (recordedPrefix controller root fuel) =
        some ((Prefix.initial capacity).append
          (recordedPrefix controller root fuel)) :=
    rfl
  rw [expanded]
  have fitsEvents :
      (recordedPrefix controller root fuel).length ≤ capacity := by
    rw [recordedPrefix_length]
    exact fits
  exact (Prefix.complete_iff capacity (recordedPrefix controller root fuel)).mpr
    fitsEvents

/-- A short capacity keeps the same frontier, retains only the emitted prefix
that fits, and reports the omitted tail. -/
theorem runIndexed_truncated
    (controller : MemorylessController State Action) (root : State)
    (fuel capacity : Nat) (short : capacity < fuel) :
    ((runIndexed controller root fuel (some capacity)).memory.2).bind
        Prefix.complete? = none ∧
      ((runIndexed controller root fuel (some capacity)).memory.2).map
          (fun record => record.omitted) =
        some (fuel - capacity) ∧
      ((runIndexed controller root fuel (some capacity)).memory.2).map
          Prefix.items =
        some ((recordedPrefix controller root fuel).take capacity) ∧
      (runIndexed controller root fuel (some capacity)).search.frontier =
        (runIndexed controller root fuel none).search.frontier := by
  have recorded :
      (runIndexed controller root fuel (some capacity)).memory.2 =
        some ((Prefix.initial capacity).append
          (recordedPrefix controller root fuel)) := by
    rw [runIndexed_record]
    rfl
  have omittedEq :=
    Prefix.initial_omitted capacity (recordedPrefix controller root fuel)
  rw [recordedPrefix_length] at omittedEq
  have positive : fuel - capacity ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt short)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [recorded]
    change Prefix.complete?
        ((Prefix.initial capacity).append
          (recordedPrefix controller root fuel)) = none
    unfold Prefix.complete?
    rw [omittedEq]
    exact if_neg positive
  · rw [recorded, Option.map_some, omittedEq]
  · rw [recorded, Option.map_some]
    exact congrArg some
      (Prefix.initial_items capacity (recordedPrefix controller root fuel))
  · rw [runIndexed_frontier_eq_advanceState, runIndexed_frontier_eq_advanceState]

/-- A recorder attached after an ordinary prefix stores only the later emitted
steps.  The frontier agrees with recording from the root, and a positive
skipped prefix is absent from the late record. -/
theorem runIndexed_late_same_frontier_omits_prefix
    (controller : MemorylessController State Action) (root : State)
    (first second capacity : Nat) (earlier : 0 < first)
    (fits : second ≤ capacity) :
    (runIndexedLate controller root first second capacity).search.frontier =
      (runIndexed controller root (first + second) none).search.frontier ∧
      ((runIndexedLate controller root first second capacity).memory.2).bind
          Prefix.complete? =
        some ((List.range second).map fun offset =>
          recordedStep controller root (first + offset)) ∧
      ((runIndexed controller root (first + second)
          (some (first + second))).memory.2).bind Prefix.complete? =
        some (recordedPrefix controller root (first + second)) ∧
      second ≠ first + second := by
  have lateFrontier :
      (runIndexedLate controller root first second capacity).search.frontier =
        [{ index := first + second,
           phase := advanceState controller (first + second) root }] := by
    unfold runIndexedLate
    have erased :=
      runSelected_erasure (indexedSystem controller) indexedController
        (observeStep controller) second
        (start (Snapshot.run (indexedSystem controller) indexedController first
          (indexedRoot root)) (some capacity))
    rw [erase_start] at erased
    have searchSame :
        (runSelected (indexedSystem controller) indexedController
            (observeStep controller) second
            (start (Snapshot.run (indexedSystem controller) indexedController
              first (indexedRoot root)) (some capacity))).search =
          (erase (runSelected (indexedSystem controller) indexedController
            (observeStep controller) second
            (start (Snapshot.run (indexedSystem controller) indexedController
              first (indexedRoot root)) (some capacity)))).search :=
      rfl
    rw [searchSame, erased, ← Snapshot.run_add]
    exact indexed_run_frontier controller root (first + second)
  have lateRecord :
      (runIndexedLate controller root first second capacity).memory.2 =
        some ((Prefix.initial capacity).append
          ((List.range second).map fun offset =>
            recordedStep controller root (first + offset))) := by
    unfold runIndexedLate
    rw [runSelected_record, erase_start, indexed_stream_shifted]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lateFrontier, runIndexed_frontier_eq_advanceState]
  · rw [lateRecord]
    have fitsEvents :
        ((List.range second).map fun offset =>
            recordedStep controller root (first + offset)).length ≤
          capacity := by
      rw [List.length_map, List.length_range]
      exact fits
    exact (Prefix.complete_iff capacity _).mpr fitsEvents
  · exact runIndexed_complete controller root (first + second) (first + second)
      (Nat.le_refl _)
  · intro equal
    exact Nat.ne_of_gt earlier
      (Nat.add_right_cancel <| by
        rw [Nat.zero_add]
        exact equal).symm

end IndexedFrontier

section RouteRecord

variable {AuthorityId : Type uAuthority} {theory : GSLT}
variable (stepAuthority : StepAuthority.{uAuthority, uCertificate}
  AuthorityId theory)
variable (claim : RecurrentTraceClaim theory stepAuthority.Certificate)

/-- Each emitted step is the existing occurrence at that index. -/
theorem recordedStep_eq_occurrence
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    recordedStep claim.controller claim.root index =
      StepRecord.mk
        (occurrenceAt stepAuthority claim execution index).index
        (occurrenceAt stepAuthority claim execution index).source
        (occurrenceAt stepAuthority claim execution index).action
        (occurrenceAt stepAuthority claim execution index).target := by
  unfold recordedStep occurrenceAt
  rw [advanceState_execution claim.controller execution index,
    advanceState_execution claim.controller execution (index + 1)]

/-- The trace-free prefix is the existing occurrence route, entry for entry. -/
theorem recordedPrefix_eq_occurrencePrefix
    (execution : ControlledExecution claim.controller claim.root)
    (fuel : Nat) :
    recordedPrefix claim.controller claim.root fuel =
      (occurrencePrefix stepAuthority claim execution fuel).map fun occurrence =>
        StepRecord.mk occurrence.index occurrence.source occurrence.action
          occurrence.target := by
  induction fuel with
  | zero =>
      unfold recordedPrefix
      rw [List.range_zero, List.map_nil, occurrencePrefix, List.map_nil]
  | succ fuel inductionHypothesis =>
      unfold recordedPrefix at inductionHypothesis ⊢
      rw [List.range_succ, List.map_append, List.map_singleton, occurrencePrefix,
        List.map_append, List.map_singleton, inductionHypothesis,
        recordedStep_eq_occurrence stepAuthority claim execution fuel]

/-- A complete requested record is the existing occurrence route. -/
theorem runIndexed_complete_eq_occurrencePrefix
    (execution : ControlledExecution claim.controller claim.root)
    (fuel capacity : Nat) (fits : fuel ≤ capacity) :
    ((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).bind
        Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix.complete? =
      some ((occurrencePrefix stepAuthority claim execution fuel).map
        fun occurrence =>
          StepRecord.mk occurrence.index occurrence.source occurrence.action
            occurrence.target) := by
  rw [runIndexed_complete claim.controller claim.root fuel capacity fits,
    recordedPrefix_eq_occurrencePrefix stepAuthority claim execution fuel]

/-- The actions in that complete record are the existing revision prefix. -/
theorem runIndexed_complete_actions_eq_revisionPrefix
    (execution : ControlledExecution claim.controller claim.root)
    (fuel capacity : Nat) (fits : fuel ≤ capacity) :
    (((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).bind
        Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix.complete?).map
        (List.map fun record => record.action) =
      some (revisionPrefix stepAuthority claim execution fuel) := by
  rw [runIndexed_complete claim.controller claim.root fuel capacity fits,
    revisionPrefix_eq_advancedActions stepAuthority claim execution fuel]
  rw [Option.map_some]
  apply congrArg some
  unfold recordedPrefix
  rw [List.map_map]
  unfold recordedStep
  rfl

end RouteRecord

section MonitorRun

open Monitor
open Mettapedia.GSLT.Core.InferenceControl.Recording

/-- Three requested steps emit the heartbeat, yield, and resume cycle, and the
frontier returns to heartbeat. -/
theorem yielding_complete_cycle :
    ((runIndexed yieldingController .heartbeat 3 (some 3)).memory.2).bind
        Prefix.complete? =
      some (recordedPrefix yieldingController .heartbeat 3) ∧
      (recordedStep yieldingController .heartbeat 0).source = .heartbeat ∧
      (recordedStep yieldingController .heartbeat 0).action.evidence = .beat ∧
      (recordedStep yieldingController .heartbeat 0).target = .waiting ∧
      (recordedStep yieldingController .heartbeat 1).source = .waiting ∧
      (recordedStep yieldingController .heartbeat 1).action.evidence = .yield ∧
      (recordedStep yieldingController .heartbeat 1).target = .serving ∧
      (recordedStep yieldingController .heartbeat 2).source = .serving ∧
      (recordedStep yieldingController .heartbeat 2).action.evidence = .resume ∧
      (recordedStep yieldingController .heartbeat 2).target = .heartbeat ∧
      (runIndexed yieldingController .heartbeat 3 (some 3)).search.frontier =
        [{ index := 3, phase := .heartbeat }] := by
  have at0 : advanceState yieldingController 0 .heartbeat = .heartbeat := by
    unfold advanceState
    rw [Function.iterate_zero_apply]
  have at1 : advanceState yieldingController 1 .heartbeat = .waiting := by
    rw [show (1 : Nat) = 0 + 1 from rfl, advanceState_succ, at0]
    rfl
  have at2 : advanceState yieldingController 2 .heartbeat = .serving := by
    rw [show (2 : Nat) = 1 + 1 from rfl, advanceState_succ, at1]
    rfl
  have at3 : advanceState yieldingController 3 .heartbeat = .heartbeat :=
    yielding_period .heartbeat
  refine ⟨runIndexed_complete yieldingController .heartbeat 3 3 (Nat.le_refl 3),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold recordedStep
    rw [at0]
  · unfold recordedStep
    rw [at0]
    exact yielding_heartbeat_and_service.1
  · unfold recordedStep
    rw [Nat.zero_add, at1]
  · unfold recordedStep
    rw [at1]
  · unfold recordedStep
    rw [at1]
    exact yielding_heartbeat_and_service.2.1
  · unfold recordedStep
    rw [show (1 + 1 : Nat) = 2 from rfl, at2]
  · unfold recordedStep
    rw [at2]
  · unfold recordedStep
    rw [at2]
    exact yielding_heartbeat_and_service.2.2
  · unfold recordedStep
    rw [show (2 + 1 : Nat) = 3 from rfl, at3]
  · rw [runIndexed_frontier_eq_advanceState, at3]

theorem starving_advance_waiting (fuel : Nat) :
    advanceState starvingController (fuel + 1) .heartbeat = .waiting := by
  induction fuel with
  | zero =>
      rw [advanceState_succ]
      unfold advanceState
      rw [Function.iterate_zero_apply]
      rfl
  | succ fuel inductionHypothesis =>
      rw [advanceState_succ, inductionHypothesis]
      rfl

/-- After the opening beat, every later emitted step stays in the waiting
phase and carries the starve command.  The frontier stays there whether or
not the record was requested. -/
theorem starving_run_exposes_stall
    (steps capacity : Nat) (fits : steps + 1 ≤ capacity) :
    ((runIndexed starvingController .heartbeat (steps + 1) (some capacity)).memory.2).bind
        Prefix.complete? =
      some (recordedPrefix starvingController .heartbeat (steps + 1)) ∧
      (recordedStep starvingController .heartbeat 0).action.evidence = .beat ∧
      (∀ offset, offset < steps →
        (recordedStep starvingController .heartbeat (offset + 1)).source =
            .waiting ∧
          (recordedStep starvingController .heartbeat (offset + 1)).target =
            .waiting ∧
          (recordedStep starvingController .heartbeat (offset + 1)).action.evidence =
            .starve) ∧
      (runIndexed starvingController .heartbeat (steps + 1) (some capacity)).search.frontier =
        [{ index := steps + 1, phase := .waiting }] ∧
      (runIndexed starvingController .heartbeat (steps + 1) none).search.frontier =
        (runIndexed starvingController .heartbeat (steps + 1)
          (some capacity)).search.frontier := by
  refine ⟨runIndexed_complete starvingController .heartbeat (steps + 1) capacity fits,
      ?_, ?_, ?_, ?_⟩
  · unfold recordedStep advanceState
    rw [Function.iterate_zero_apply]
    rfl
  · intro offset _
    have sourcePhase := starving_advance_waiting offset
    have targetPhase := starving_advance_waiting (offset + 1)
    refine ⟨?_, ?_, ?_⟩
    · unfold recordedStep
      rw [sourcePhase]
    · unfold recordedStep
      rw [targetPhase]
    · unfold recordedStep
      rw [sourcePhase]
      rfl
  · rw [runIndexed_frontier_eq_advanceState, starving_advance_waiting]
  · rw [runIndexed_frontier_eq_advanceState, runIndexed_frontier_eq_advanceState]

end MonitorRun

/-! ## What finite control does not say -/

namespace Scope

/-- Successor iteration is the same trace-free stepper on an unbounded
carrier.  Its image is unbounded, so the algorithm is not a construction of
a finite automaton for an arbitrary state type. -/
def successorController : MemorylessController Nat Bool where
  active := fun _ => true
  action := fun n => decide (n % 2 = 0)
  next := Nat.succ

theorem successor_advance (fuel : Nat) :
    advanceState successorController fuel 0 = fuel := by
  induction fuel with
  | zero =>
      unfold advanceState
      rw [Function.iterate_zero_apply]
  | succ fuel inductionHypothesis =>
      rw [advanceState_succ, inductionHypothesis]
      rfl

theorem successor_image_unbounded (bound : Nat) :
    ∃ fuel, bound < advanceState successorController fuel 0 :=
  ⟨bound + 1, by
      rw [successor_advance]
      exact Nat.lt_succ_self bound⟩

/-- Finite admission labels.  Recurrence of `admit` is not admission of every
identity. -/
inductive AdmissionLabel where
  | heartbeat
  | admit
  deriving DecidableEq

instance : Fintype AdmissionLabel :=
  Fintype.ofList [.heartbeat, .admit] (by
    intro label
    cases label <;> simp)

def admissionLabel (step : Nat) : AdmissionLabel :=
  if step % 2 = 0 then .heartbeat else .admit

/-- The only identity this finite labelling ever admits. -/
def admittedIdentity (_step : Nat) : Nat := 0

theorem admission_label_recurs (lower : Nat) :
    ∃ step, lower ≤ step ∧ admissionLabel step = .admit := by
  rcases Nat.mod_two_eq_zero_or_one lower with even | odd
  · refine ⟨lower + 1, Nat.le_succ lower, ?_⟩
    have nextOdd : (lower + 1) % 2 = 1 := by
      rw [Nat.add_mod, even]
    rw [admissionLabel, nextOdd]
    rfl
  · refine ⟨lower, Nat.le_refl lower, ?_⟩
    rw [admissionLabel, odd]
    rfl

theorem client_one_never_admitted (step : Nat)
    (_admitted : admissionLabel step = .admit) :
    admittedIdentity step ≠ 1 := by
  rw [admittedIdentity]
  decide

theorem finite_labels_do_not_fairly_serve_unbounded_identities :
    (∀ lower, ∃ step, lower ≤ step ∧ admissionLabel step = .admit) ∧
      (∀ step, admissionLabel step = .admit → admittedIdentity step ≠ 1) :=
  ⟨admission_label_recurs, client_one_never_admitted⟩

end Scope

/-! ## Admitted FIFO positions survive optional recording

`runIndexed` is the one-node special case of this runner.  An arbitrary
finite frontier uses `Controller.fixed Scheduler.breadthFirst`.  Erasing an
optional record restores that run, so the occurrence selected at fuel
`index` is the admitted position whether or not a prefix was retained.

Three assumptions stay outside that equality.

* Frontier admission is an index below the length of the supplied finite
  frontier.  `Snapshot.fifo_never_serves_unadmitted_client` and
  `Scope.client_one_never_admitted` are the negative statements: a client
  never placed on the frontier acquires no service guarantee.  Recurrence
  of an admit label is not that placement.
* Yielding service is the monitor phase cycle
  `Monitor.yielding_service_within`.  Reaching `.serving` within two steps
  is not admission of a frontier index.
* Total-step completion is `Snapshot.run_completes_at_rank`, which consumes
  a `DescentCertificate`.  The position bound does not.  This completion
  hypothesis is an abstract source assumption.  It is not a native
  response-time guarantee.  Fresh finite successors are served only after
  the admitted suffix, so an infinite successor stream does not postpone an
  admitted index.  Depth-first silent self-loop starvation is an unfair
  scheduler counterexample, not evidence of a native primitive that never
  yields.
* A finite external burst may arrive on every breadth-first step.  The
  burst is appended after that step's integration, behind the suffix
  retained from earlier positions.  Later bursts stay behind earlier ones.
  A repeated label in a burst is a new position.  `erase` and
  `tick_erasure` carry that same frontier through optional recording.
-/

section AdmittedFifo

open Mettapedia.GSLT.Core.BranchingTemporal hiding Snapshot
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.InferenceControl.Recording

variable {Node Answer Event : Type*}

/-- Recording changes the retained prefix, not which admitted occurrence the
breadth-first runner selects. -/
theorem recorded_fifo_serves_admitted_position
    (system : BranchingSystem Node Answer)
    (observe : Unit → Node → Option Answer → List Node → Event)
    (snapshot : Snapshot Node Answer Unit) (index : Nat) (capacity : Option Nat)
    (admitted : index < snapshot.search.frontier.length) :
    Snapshot.selected (Controller.fixed Scheduler.breadthFirst)
      (erase (runSelected system (Controller.fixed Scheduler.breadthFirst)
        observe index (start snapshot capacity))) =
        some snapshot.search.frontier[index] := by
  rw [runSelected_erasure, erase_start]
  exact Snapshot.fifo_serves_admitted_position system snapshot index admitted

/-- The admitted suffix remains in front of freshly generated work after the
record is erased. -/
theorem recorded_fifo_admitted_suffix
    (system : BranchingSystem Node Answer)
    (observe : Unit → Node → Option Answer → List Node → Event)
    (snapshot : Snapshot Node Answer Unit) (steps : Nat) (capacity : Option Nat)
    (bound : steps ≤ snapshot.search.frontier.length) :
    ∃ generated : List Node,
      (erase (runSelected system (Controller.fixed Scheduler.breadthFirst)
        observe steps (start snapshot capacity))).search.frontier =
        snapshot.search.frontier.drop steps ++ generated := by
  rw [runSelected_erasure, erase_start]
  exact Snapshot.fifo_admitted_suffix system snapshot steps bound

/-- The yielding cycle's two-step service bound and the refusal to admit
client 1 are separate facts.  Neither is the FIFO position theorem. -/
theorem yielding_cycle_is_not_client_admission
    (execution : ControlledExecution Monitor.yieldingController
      Monitor.yieldingClaim.root)
    (start step : Nat) :
    (∃ offset, offset ≤ 2 ∧
        execution.state (start + offset) = Monitor.Phase.serving) ∧
      (Scope.admissionLabel step = .admit →
        Scope.admittedIdentity step ≠ 1) :=
  ⟨Monitor.yielding_service_within execution start,
    fun admitted => Scope.client_one_never_admitted step admitted⟩

/-- Appending a burst changes the frontier and leaves the record alone, so
erasure commutes with admission. -/
theorem erase_admitTail {Memory : Type*}
    (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event)))
    (burst : List Node) :
    erase (Snapshot.admitTail snapshot burst) =
      Snapshot.admitTail (erase snapshot) burst := by
  cases snapshot
  rfl

/-- Optional recording does not move a tail-admitted frontier.  The recorded
controller is the existing observer around the breadth-first program runner. -/
theorem recorded_tail_admission_erasure
    (system : BranchingSystem Node Answer)
    (observe : Unit → Node → Option Answer → List Node → Event)
    (burst : Nat → List Node) (capacity : Option Nat) (steps : Nat)
    (snapshot : Snapshot Node Answer (Unit × Option (Prefix Event))) :
    erase (Snapshot.runAdmitting system
        (controller (Controller.fixed Scheduler.breadthFirst) observe capacity)
        burst steps snapshot) =
      Snapshot.runAdmitting system (Controller.fixed Scheduler.breadthFirst)
        burst steps (erase snapshot) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [Snapshot.runAdmitting, Snapshot.runAdmitting, erase_admitTail,
        tick_erasure, inductionHypothesis]

/-- The admitted suffix stays in front of generated work and of every external
burst after the record is erased. -/
theorem recorded_fifo_tail_admitted_suffix
    (system : BranchingSystem Node Answer)
    (observe : Unit → Node → Option Answer → List Node → Event)
    (burst : Nat → List Node) (snapshot : Snapshot Node Answer Unit) (steps : Nat)
    (capacity : Option Nat) (bound : steps ≤ snapshot.search.frontier.length) :
    ∃ generated : List Node,
      (erase (Snapshot.runAdmitting system
          (controller (Controller.fixed Scheduler.breadthFirst) observe capacity)
          burst steps (start snapshot capacity))).search.frontier =
        snapshot.search.frontier.drop steps ++ generated := by
  rw [recorded_tail_admission_erasure, erase_start]
  exact Snapshot.fifo_tail_admitted_suffix system burst snapshot steps bound

/-- Recording does not change which admitted occurrence the breadth-first
runner selects while finite bursts arrive at the tail. -/
theorem recorded_fifo_serves_admitted_position_with_tail_bursts
    (system : BranchingSystem Node Answer)
    (observe : Unit → Node → Option Answer → List Node → Event)
    (burst : Nat → List Node) (snapshot : Snapshot Node Answer Unit) (index : Nat)
    (capacity : Option Nat) (admitted : index < snapshot.search.frontier.length) :
    Snapshot.selected (Controller.fixed Scheduler.breadthFirst)
      (erase (Snapshot.runAdmitting system
        (controller (Controller.fixed Scheduler.breadthFirst) observe capacity)
        burst index (start snapshot capacity))) =
        some snapshot.search.frontier[index] := by
  rw [recorded_tail_admission_erasure, erase_start]
  exact Snapshot.fifo_serves_admitted_position_with_tail_bursts system burst
    snapshot index admitted

/-- A request inside the burst admitted by the next step keeps its tail index
after erasure.  Later recorded bursts stay behind that index. -/
theorem recorded_fifo_serves_tail_burst_position
    (system : BranchingSystem Node Answer)
    (observe : Unit → Node → Option Answer → List Node → Event)
    (burst : Nat → List Node) (snapshot : Snapshot Node Answer Unit) (head : Node)
    (tail : List Node) (offset : Nat) (capacity : Option Nat)
    (frontierEq : snapshot.search.frontier = head :: tail)
    (inBurst : offset < (burst 0).length) :
    Snapshot.selected (Controller.fixed Scheduler.breadthFirst)
      (erase (Snapshot.runAdmitting system
        (controller (Controller.fixed Scheduler.breadthFirst) observe capacity)
        (fun step => burst (step + 1))
        (offset + (tail ++ system.successors head).length)
        (Snapshot.runAdmitting system
          (controller (Controller.fixed Scheduler.breadthFirst) observe capacity)
          burst 1 (start snapshot capacity)))) =
      some (burst 0)[offset] := by
  have inner :=
    recorded_tail_admission_erasure system observe burst capacity 1
      (start snapshot capacity)
  rw [erase_start] at inner
  have outer :=
    recorded_tail_admission_erasure system observe (fun step => burst (step + 1))
      capacity (offset + (tail ++ system.successors head).length)
      (Snapshot.runAdmitting system
        (controller (Controller.fixed Scheduler.breadthFirst) observe capacity)
        burst 1 (start snapshot capacity))
  rw [outer, inner]
  exact Snapshot.fifo_serves_tail_burst_position system burst snapshot head tail
    offset frontierEq inBurst

end AdmittedFifo

#print axioms occurrencePrefix_actions
#print axioms occurrenceAt_index_injective
#print axioms revisionPrefix_history
#print axioms history_to_multistep
#print axioms finitePrefix_succ
#print axioms finitePrefix_semantic
#print axioms recurrentChecker_acceptance_consequences
#print axioms Canary.accepting_loop_has_both_consequences
#print axioms Canary.prefixProductivity_does_not_imply_recurrence
#print axioms Canary.nonaccepting_loop_rejects_every_measure
#print axioms advanceState_canonical
#print axioms currentNote_requested_iff
#print axioms note_does_not_enter_advance
#print axioms advanceState_shift
#print axioms buchi_of_bounded_admission
#print axioms advance_agrees_with_route
#print axioms advance_executes
#print axioms Monitor.yielding_recurrent
#print axioms Monitor.yielding_buchi_of_admission
#print axioms Monitor.starvation_separates_prefix_from_recurrence
#print axioms Monitor.starving_rejects_every_measure
#print axioms Scope.successor_image_unbounded
#print axioms Scope.finite_labels_do_not_fairly_serve_unbounded_identities
#print axioms runIndexed_frontier_eq_advanceState
#print axioms runIndexed_erasure
#print axioms runIndexed_complete
#print axioms runIndexed_truncated
#print axioms runIndexed_late_same_frontier_omits_prefix
#print axioms runIndexed_complete_eq_occurrencePrefix
#print axioms runIndexed_complete_actions_eq_revisionPrefix
#print axioms yielding_complete_cycle
#print axioms starving_run_exposes_stall
#print axioms recorded_fifo_serves_admitted_position
#print axioms recorded_fifo_admitted_suffix
#print axioms yielding_cycle_is_not_client_admission
#print axioms erase_admitTail
#print axioms recorded_tail_admission_erasure
#print axioms recorded_fifo_tail_admitted_suffix
#print axioms recorded_fifo_serves_admitted_position_with_tail_bursts
#print axioms recorded_fifo_serves_tail_burst_position

end Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
