import Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
import Mettapedia.GSLT.LanguageDef.GSLTILFiniteRevisionRouteBridge

/-!
# Recurrent occurrence routes in the GSLT-IL operational waist

A checked recurrent controller carries two independent kinds of evidence:

* every demanded finite prefix is a chronological, occurrence-retaining
  execution; and
* the selected accepting predicate recurs beyond every finite bound.

This module maps the first component into the existing GSLT-IL operational
equipment without weakening the second into finite reachability.  Each
controlled execution induces a coherent family of path-retaining finite
routes.  Every prefix projects to an ordinary execution path and then to an
institutional reachability sentence.  The Buechi witness remains a separate
liveness field on the same execution.

The negative control is load-bearing: a locally valid loop with no accepting
state has every finite operational prefix, but is not recurrent.  Finite
prefix productivity therefore cannot be used as a substitute for fairness,
recurrence, stream productivity, or complete closure.  A record produced by
`runIndexed` is one such finite prefix.  Completing that prefix, and Büchi
acceptance of the yielding phase monitor, do not admit every client identity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteBridge

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge

variable {AuthorityId : Type} {theory : GSLT}
variable (stepAuthority : StepAuthority AuthorityId theory)
variable (accepting : theory.Term -> Bool)
variable (claim : RecurrentTraceClaim theory stepAuthority.Certificate)

section Prefix

variable [DecidableEq theory.Term]

/-! ## Constructive retained prefixes -/

/-- The named chronological path selected by one controlled execution.
Unlike the existing proposition-valued history, this is data and can be
projected constructively into an execution-path fibre. -/
def namedRevisionPrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root) :
    (depth : Nat) ->
      NamedHistoryPath (auditedRevisionTheory stepAuthority accepting)
        (revisionPrefix stepAuthority claim execution depth)
        claim.root (execution.state depth)
  | 0 => by
      change NamedHistoryPath
        (auditedRevisionTheory stepAuthority accepting) [] claim.root
          (execution.state 0)
      rw [execution.starts]
      exact NamedHistoryPath.nil
        (theory := auditedRevisionTheory stepAuthority accepting) claim.root
  | depth + 1 => by
      let last : NamedHistoryPath
          (auditedRevisionTheory stepAuthority accepting)
          [claim.controller.action (execution.state depth)]
          (execution.state depth) (execution.state (depth + 1)) :=
        .cons
          ⟨audited_step_at stepAuthority accepting claim locallyValid
            execution depth⟩
          (.nil (theory := auditedRevisionTheory stepAuthority accepting)
            (execution.state (depth + 1)))
      change NamedHistoryPath
        (auditedRevisionTheory stepAuthority accepting)
        (revisionPrefix stepAuthority claim execution depth ++
          [claim.controller.action (execution.state depth)])
        claim.root (execution.state (depth + 1))
      exact (namedRevisionPrefix locallyValid execution depth).append last

/-- Every recurrent prefix retains temporal occurrence identity, named
revision identity, its endpoint, and the complete path constructor spine. -/
def retainedFinitePrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    PathRetainingFiniteRoute
      (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root where
  occurrences := occurrencePrefix stepAuthority claim execution depth
  revisions := revisionPrefix stepAuthority claim execution depth
  target := execution.state depth
  aligned := occurrencePrefix_length stepAuthority claim execution depth
  execution := namedRevisionPrefix stepAuthority accepting claim locallyValid
    execution depth

/-- The stronger retained prefix erases exactly to the established recurrent
finite route.  It is not a second execution semantics. -/
theorem retainedFinitePrefix_erases_to_finitePrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
      depth).erase =
      finitePrefix stepAuthority accepting claim locallyValid execution depth := by
  apply FiniteRoute.ext <;> rfl

omit [DecidableEq theory.Term] in
/-- A chronological controller prefix contains exactly one occurrence per
demanded epoch. -/
theorem occurrencePrefix_length_eq_depth
    (execution : ControlledExecution claim.controller claim.root) :
    forall depth,
      (occurrencePrefix stepAuthority claim execution depth).length = depth := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [occurrencePrefix, inductionHypothesis]

/-- Projection into the ordinary GSLT path fibre preserves the demanded
finite depth exactly. -/
@[simp] theorem retainedFinitePrefix_executionPath_length
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
      depth).executionPath.length = depth := by
  calc
    (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
        depth).executionPath.length =
        (retainedFinitePrefix stepAuthority accepting claim locallyValid
          execution depth).occurrences.length :=
      PathRetainingFiniteRoute.executionPath_length
        (theory := auditedRevisionTheory stepAuthority accepting)
        (Occurrence := ControlledOccurrence theory
          stepAuthority.Certificate)
        (source := claim.root) _
    _ = depth :=
      occurrencePrefix_length_eq_depth stepAuthority claim execution depth

/-- The one retained edge extending the prefix at a selected epoch. -/
def retainedAtomicStep
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    PathRetainingFiniteRoute
      (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate)
      (execution.state index) :=
  PathRetainingFiniteRoute.single
    (occurrenceAt stepAuthority claim execution index)
    (claim.controller.action (execution.state index))
    (audited_step_at stepAuthority accepting claim locallyValid execution index)

/-- Successive projections form one coherent execution-path cone: demanding
one more epoch appends exactly the selected checked edge. -/
theorem retainedFinitePrefix_executionPath_succ
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
        (depth + 1)).executionPath =
      (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          depth).executionPath.append
        (retainedAtomicStep stepAuthority accepting claim locallyValid execution
          depth).executionPath := by
  let last : NamedHistoryPath
      (auditedRevisionTheory stepAuthority accepting)
      [claim.controller.action (execution.state depth)]
      (execution.state depth) (execution.state (depth + 1)) :=
    .cons
      ⟨audited_step_at stepAuthority accepting claim locallyValid execution
        depth⟩
      (.nil (theory := auditedRevisionTheory stepAuthority accepting)
        (execution.state (depth + 1)))
  change
    ((namedRevisionPrefix stepAuthority accepting claim locallyValid execution
      depth).append last).toExecutionPath =
      (namedRevisionPrefix stepAuthority accepting claim locallyValid execution
        depth).toExecutionPath.append last.toExecutionPath
  exact NamedHistoryPath.toExecutionPath_append _ _

/-! ## One recurrent execution and its finite-prefix cone -/

/-- A particular controlled execution with independently visible local-edge
authority and Buechi liveness.  Prefix paths are derived from these fields;
they are not stored as unrelated witnesses. -/
structure AuditedRecurrentExecution where
  execution : ControlledExecution claim.controller claim.root
  locallyValid : claim.controller.LocallyValid
    (auditedLabeledSystem stepAuthority accepting) claim.root
  recurrent : forall lowerBound, exists visit,
    lowerBound <= visit /\ accepting (execution.state visit) = true

namespace AuditedRecurrentExecution

/-- An accepted recurrent checker constructs the route object for any
controlled execution. -/
def ofAccepted [Fintype theory.Term]
    (authorityId : AuthorityId) (measure : ProgressMeasure theory.Term)
    (accepted :
      (recurrentChecker authorityId stepAuthority accepting).check
        claim measure = true)
    (execution : ControlledExecution claim.controller claim.root) :
    AuditedRecurrentExecution stepAuthority accepting claim where
  execution := execution
  locallyValid :=
    ((ProgressMeasure.check_eq_true_iff
      (auditedLabeledSystem stepAuthority accepting)
      claim.controller measure claim.root).mp accepted).1
  recurrent :=
    (recurrentChecker_sound authorityId stepAuthority accepting
      claim measure accepted execution).2

/-- The retained finite prefix of this exact recurrent execution. -/
def retainedPrefix
    (route : AuditedRecurrentExecution stepAuthority accepting claim)
    (depth : Nat) :
    PathRetainingFiniteRoute
      (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root :=
  retainedFinitePrefix stepAuthority accepting claim route.locallyValid
    route.execution depth

/-- One prefix as a loose-route witness with its exact endpoint. -/
def prefixWitness
    (route : AuditedRecurrentExecution stepAuthority accepting claim)
    (depth : Nat) :
    retainedFiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate)
      claim.root (route.execution.state depth) :=
  ⟨retainedPrefix stepAuthority accepting claim route depth, rfl⟩

/-- Every finite prefix enters the operational equipment and the semantic
institution at its exact depth and endpoint. -/
theorem prefix_enters_operational_waist
    (route : AuditedRecurrentExecution stepAuthority accepting claim)
    (depth : Nat) :
    ((retainedToExecutionPathSquare
      (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate)).map
        (prefixWitness stepAuthority accepting claim route depth)).length =
        depth /\
      claim.root ∈ reachesTargetSentence
        (auditedRevisionTheory stepAuthority accepting)
        (route.execution.state depth) := by
  constructor
  · exact retainedFinitePrefix_executionPath_length stepAuthority accepting
      claim route.locallyValid route.execution depth
  · exact finiteRoute_in_reachesTargetSentence
      (retainedPrefix stepAuthority accepting claim route depth).erase

/-- The complete bridge keeps finite operational productivity and unbounded
recurrence as separate conjuncts over the same execution. -/
theorem operational_prefixes_and_recurrence
    (route : AuditedRecurrentExecution stepAuthority accepting claim) :
    (forall depth,
      ((retainedToExecutionPathSquare
        (auditedRevisionTheory stepAuthority accepting)
        (ControlledOccurrence theory stepAuthority.Certificate)).map
          (prefixWitness stepAuthority accepting claim route depth)).length =
          depth /\
        claim.root ∈ reachesTargetSentence
          (auditedRevisionTheory stepAuthority accepting)
          (route.execution.state depth)) /\
      (forall lowerBound, exists visit,
        lowerBound <= visit /\
          accepting (route.execution.state visit) = true) := by
  exact ⟨fun depth => prefix_enters_operational_waist stepAuthority accepting
      claim route depth,
    route.recurrent⟩

end AuditedRecurrentExecution

/-! ## Records produced by the indexed run

`runIndexed` is the route's existing `runSelected` adapter.  A presented
record is compared with `retainedFinitePrefix`, whose execution spine is
`namedRevisionPrefix` for the original `stepAuthority`.  The record is not
an authority and it is not a second recorder.  Completion, truncation, and a
late suffix are different views of that same checked prefix.
-/

section ProducedRecord

open Mettapedia.GSLT.Core.InferenceControl.Recording

omit [DecidableEq theory.Term] in
/-- Occurrence indices are the demanded epochs, in order. -/
theorem occurrencePrefix_indices
    (execution : ControlledExecution claim.controller claim.root)
    (fuel : Nat) :
    (occurrencePrefix stepAuthority claim execution fuel).map
        (fun occurrence => occurrence.index) =
      List.range fuel := by
  induction fuel with
  | zero =>
      rw [occurrencePrefix, List.map_nil, List.range_zero]
  | succ fuel inductionHypothesis =>
      rw [occurrencePrefix, List.map_append, List.map_singleton,
        inductionHypothesis, List.range_succ]
      unfold occurrenceAt
      rfl

omit [DecidableEq theory.Term] in
/-- Actions emitted by the trace-free prefix are the checked revision prefix. -/
theorem recordedPrefix_actions_eq_revisionPrefix
    (execution : ControlledExecution claim.controller claim.root)
    (fuel : Nat) :
    (recordedPrefix claim.controller claim.root fuel).map
        (fun record => record.action) =
      revisionPrefix stepAuthority claim execution fuel := by
  rw [revisionPrefix_eq_advancedActions stepAuthority claim execution fuel]
  unfold recordedPrefix
  rw [List.map_map]
  unfold recordedStep
  rfl

/-- A capacity that covers the run presents the checked source prefix: its
actions, its occurrence indices, and its endpoint.  The execution spine stays
the named prefix built from `stepAuthority`. -/
theorem runIndexed_complete_reflects_retainedPrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (fuel capacity : Nat) (fits : fuel ≤ capacity) :
    ((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).bind
        Prefix.complete? =
      some (recordedPrefix claim.controller claim.root fuel) ∧
      (((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).bind
          Prefix.complete?).map (List.map fun record => record.action) =
        some (retainedFinitePrefix stepAuthority accepting claim locallyValid
          execution fuel).revisions ∧
      (((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).bind
          Prefix.complete?).map (List.map fun record => record.index) =
        some ((retainedFinitePrefix stepAuthority accepting claim locallyValid
            execution fuel).occurrences.map fun occurrence => occurrence.index) ∧
      (runIndexed claim.controller claim.root fuel (some capacity)).search.frontier =
        [{ index := fuel,
           phase := (retainedFinitePrefix stepAuthority accepting claim
             locallyValid execution fuel).target }] ∧
      (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          fuel).execution =
        namedRevisionPrefix stepAuthority accepting claim locallyValid execution
          fuel ∧
      (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          fuel).executionPath.length = fuel := by
  refine ⟨runIndexed_complete claim.controller claim.root fuel capacity fits,
      ?_, ?_, ?_, rfl,
      retainedFinitePrefix_executionPath_length stepAuthority accepting claim
        locallyValid execution fuel⟩
  · rw [runIndexed_complete_actions_eq_revisionPrefix stepAuthority claim
        execution fuel capacity fits]
    rfl
  · rw [runIndexed_complete_eq_occurrencePrefix stepAuthority claim execution
        fuel capacity fits, Option.map_some, List.map_map]
    rfl
  · rw [runIndexed_frontier_eq_advanceState claim.controller claim.root fuel
        (some capacity),
      advanceState_execution claim.controller execution fuel]
    rfl

/-- A short capacity does not complete.  The visible actions and indices are
the corresponding proper prefix of the checked source, while the frontier
endpoint remains the endpoint of the full checked prefix. -/
theorem runIndexed_truncation_keeps_checked_endpoint
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (fuel capacity : Nat) (short : capacity < fuel) :
    ((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).bind
        Prefix.complete? = none ∧
      ((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).map
          (fun record => record.omitted) =
        some (fuel - capacity) ∧
      (((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).map
          Prefix.items).map (List.map fun record => record.action) =
        some ((retainedFinitePrefix stepAuthority accepting claim locallyValid
          execution fuel).revisions.take capacity) ∧
      (((runIndexed claim.controller claim.root fuel (some capacity)).memory.2).map
          Prefix.items).map (List.map fun record => record.index) =
        some (((retainedFinitePrefix stepAuthority accepting claim locallyValid
            execution fuel).occurrences.take capacity).map
          fun occurrence => occurrence.index) ∧
      (runIndexed claim.controller claim.root fuel (some capacity)).search.frontier =
        [{ index := fuel,
           phase := (retainedFinitePrefix stepAuthority accepting claim
             locallyValid execution fuel).target }] ∧
      (runIndexed claim.controller claim.root fuel none).search.frontier =
        (runIndexed claim.controller claim.root fuel (some capacity)).search.frontier ∧
      ((retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          fuel).revisions.take capacity).length = capacity ∧
      (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          fuel).revisions.length = fuel ∧
      (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          fuel).execution =
        namedRevisionPrefix stepAuthority accepting claim locallyValid execution
          fuel := by
  have truncated :=
    runIndexed_truncated claim.controller claim.root fuel capacity short
  have revisionsLength :
      (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          fuel).revisions.length = fuel := by
    rw [← (retainedFinitePrefix stepAuthority accepting claim locallyValid
        execution fuel).aligned,
      show (retainedFinitePrefix stepAuthority accepting claim locallyValid
          execution fuel).occurrences =
        occurrencePrefix stepAuthority claim execution fuel from rfl]
    exact occurrencePrefix_length_eq_depth stepAuthority claim execution fuel
  refine ⟨truncated.1, truncated.2.1, ?_, ?_, ?_, truncated.2.2.2.symm, ?_,
      revisionsLength, rfl⟩
  · rw [truncated.2.2.1, Option.map_some, List.map_take,
      recordedPrefix_actions_eq_revisionPrefix stepAuthority claim execution fuel]
    rfl
  · rw [truncated.2.2.1, Option.map_some, List.map_take,
      recordedPrefix_eq_occurrencePrefix stepAuthority claim execution fuel,
      List.map_map, ← List.map_take]
    rfl
  · rw [runIndexed_frontier_eq_advanceState claim.controller claim.root fuel
        (some capacity),
      advanceState_execution claim.controller execution fuel]
    rfl
  · exact List.length_take_of_le <| by
      rw [revisionsLength]
      exact Nat.le_of_lt short

/-- A recorder attached after an ordinary prefix stores the later checked
actions and their original occurrence indices.  The frontier is still the
endpoint of the whole checked prefix, and the skipped prefix is absent from
the late record. -/
theorem runIndexed_late_reflects_retained_suffix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (first second capacity : Nat) (earlier : 0 < first)
    (fits : second ≤ capacity) :
    (runIndexedLate claim.controller claim.root first second capacity).search.frontier =
      [{ index := first + second,
         phase := (retainedFinitePrefix stepAuthority accepting claim locallyValid
           execution (first + second)).target }] ∧
      (((runIndexedLate claim.controller claim.root first second capacity).memory.2).bind
          Prefix.complete?).map (List.map fun record => record.action) =
        some ((retainedFinitePrefix stepAuthority accepting claim locallyValid
          execution (first + second)).revisions.drop first) ∧
      (((runIndexedLate claim.controller claim.root first second capacity).memory.2).bind
          Prefix.complete?).map (List.map fun record => record.index) =
        some (((retainedFinitePrefix stepAuthority accepting claim locallyValid
            execution (first + second)).occurrences.drop first).map
          fun occurrence => occurrence.index) ∧
      ((runIndexed claim.controller claim.root (first + second)
          (some (first + second))).memory.2).bind Prefix.complete? =
        some (recordedPrefix claim.controller claim.root (first + second)) ∧
      second ≠ first + second ∧
      (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          (first + second)).execution =
        namedRevisionPrefix stepAuthority accepting claim locallyValid execution
          (first + second) := by
  have late :=
    runIndexed_late_same_frontier_omits_prefix claim.controller claim.root
      first second capacity earlier fits
  have suffix :
      (List.range (first + second)).drop first =
        (List.range second).map (fun offset => first + offset) := by
    rw [List.range_add, List.drop_left' (List.length_range (n := first))]
  have actionSuffix :
      ((List.range second).map fun offset =>
          (recordedStep claim.controller claim.root (first + offset)).action) =
        (revisionPrefix stepAuthority claim execution (first + second)).drop
          first := by
    rw [revisionPrefix_eq_advancedActions stepAuthority claim execution
        (first + second),
      ← List.map_drop, suffix, List.map_map]
    unfold recordedStep
    rfl
  refine ⟨?_, ?_, ?_, late.2.2.1, late.2.2.2, rfl⟩
  · rw [late.1, runIndexed_frontier_eq_advanceState claim.controller claim.root
        (first + second) none,
      advanceState_execution claim.controller execution (first + second)]
    rfl
  · rw [late.2.1, Option.map_some, List.map_map]
    exact congrArg some actionSuffix
  · rw [late.2.1, Option.map_some, List.map_map]
    unfold recordedStep
    rw [show (retainedFinitePrefix stepAuthority accepting claim locallyValid
          execution (first + second)).occurrences =
        occurrencePrefix stepAuthority claim execution (first + second) from rfl,
      List.map_drop,
      occurrencePrefix_indices stepAuthority claim execution (first + second),
      suffix]
    rfl

end ProducedRecord

end Prefix

/-! ## Produced records of the existing monitor controls -/

section Controls

open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor
open Mettapedia.GSLT.Core.InferenceControl.Recording

/-- The yielding controller's complete three-step record is the checked
operational prefix of that cycle, and the frontier returns to heartbeat. -/
theorem yielding_produced_cycle_matches_retained_prefix :
    ((runIndexed yieldingController .heartbeat 3 (some 3)).memory.2).bind
        Prefix.complete? =
      some (recordedPrefix yieldingController .heartbeat 3) ∧
      (((runIndexed yieldingController .heartbeat 3 (some 3)).memory.2).bind
          Prefix.complete?).map (List.map fun record => record.action) =
        some (retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting yieldingClaim
          yielding_locally_valid
          (yieldingController.canonicalExecution yieldingClaim.root) 3).revisions ∧
      (((runIndexed yieldingController .heartbeat 3 (some 3)).memory.2).bind
          Prefix.complete?).map (List.map fun record => record.index) =
        some ((retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting yieldingClaim
            yielding_locally_valid
            (yieldingController.canonicalExecution yieldingClaim.root)
            3).occurrences.map fun occurrence => occurrence.index) ∧
      (runIndexed yieldingController .heartbeat 3 (some 3)).search.frontier =
        [{ index := 3,
           phase := (retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting
             yieldingClaim yielding_locally_valid
             (yieldingController.canonicalExecution yieldingClaim.root) 3).target }] ∧
      (retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting yieldingClaim
          yielding_locally_valid
          (yieldingController.canonicalExecution yieldingClaim.root) 3).execution =
        namedRevisionPrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting yieldingClaim
          yielding_locally_valid
          (yieldingController.canonicalExecution yieldingClaim.root) 3 ∧
      (recordedStep yieldingController .heartbeat 0).source = .heartbeat ∧
      (recordedStep yieldingController .heartbeat 0).action.evidence = .beat ∧
      (recordedStep yieldingController .heartbeat 0).target = .waiting ∧
      (recordedStep yieldingController .heartbeat 1).source = .waiting ∧
      (recordedStep yieldingController .heartbeat 1).action.evidence = .yield ∧
      (recordedStep yieldingController .heartbeat 1).target = .serving ∧
      (recordedStep yieldingController .heartbeat 2).source = .serving ∧
      (recordedStep yieldingController .heartbeat 2).action.evidence = .resume ∧
      (recordedStep yieldingController .heartbeat 2).target = .heartbeat ∧
      (retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting yieldingClaim
          yielding_locally_valid
          (yieldingController.canonicalExecution yieldingClaim.root) 3).target =
        .heartbeat := by
  have reflected :=
    runIndexed_complete_reflects_retainedPrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting
      yieldingClaim yielding_locally_valid
      (yieldingController.canonicalExecution yieldingClaim.root) 3 3
      (Nat.le_refl 3)
  have cycle := yielding_complete_cycle
  refine ⟨cycle.1, reflected.2.1, reflected.2.2.1, reflected.2.2.2.1,
      reflected.2.2.2.2.1, cycle.2.1, cycle.2.2.1, cycle.2.2.2.1,
      cycle.2.2.2.2.1, cycle.2.2.2.2.2.1, cycle.2.2.2.2.2.2.1,
      cycle.2.2.2.2.2.2.2.1, cycle.2.2.2.2.2.2.2.2.1,
      cycle.2.2.2.2.2.2.2.2.2.1, ?_⟩
  · have same := cycle.2.2.2.2.2.2.2.2.2.2
    unfold yieldingClaim at reflected
    rw [reflected.2.2.2.1] at same
    exact congrArg (fun node => node.phase) (List.cons.inj same).1

/-- The starving controller's complete record follows the checked prefix and
then remains waiting.  That finite record is not Büchi recurrence. -/
theorem starving_produced_record_stalls
    (steps capacity : Nat) (fits : steps + 1 ≤ capacity) :
    ((runIndexed starvingController .heartbeat (steps + 1) (some capacity)).memory.2).bind
        Prefix.complete? =
      some (recordedPrefix starvingController .heartbeat (steps + 1)) ∧
      (((runIndexed starvingController .heartbeat (steps + 1)
            (some capacity)).memory.2).bind Prefix.complete?).map
          (List.map fun record => record.action) =
        some (retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting starvingClaim
          starving_locally_valid
          (starvingController.canonicalExecution starvingClaim.root)
          (steps + 1)).revisions ∧
      (((runIndexed starvingController .heartbeat (steps + 1)
            (some capacity)).memory.2).bind Prefix.complete?).map
          (List.map fun record => record.index) =
        some ((retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting starvingClaim
            starving_locally_valid
            (starvingController.canonicalExecution starvingClaim.root)
            (steps + 1)).occurrences.map fun occurrence => occurrence.index) ∧
      (runIndexed starvingController .heartbeat (steps + 1)
          (some capacity)).search.frontier =
        [{ index := steps + 1,
           phase := (retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting
             starvingClaim starving_locally_valid
             (starvingController.canonicalExecution starvingClaim.root)
             (steps + 1)).target }] ∧
      (retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting starvingClaim
          starving_locally_valid
          (starvingController.canonicalExecution starvingClaim.root)
          (steps + 1)).execution =
        namedRevisionPrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting starvingClaim
          starving_locally_valid
          (starvingController.canonicalExecution starvingClaim.root)
          (steps + 1) ∧
      (recordedStep starvingController .heartbeat 0).action.evidence = .beat ∧
      (∀ offset, offset < steps →
        (recordedStep starvingController .heartbeat (offset + 1)).source =
            .waiting ∧
          (recordedStep starvingController .heartbeat (offset + 1)).target =
            .waiting ∧
          (recordedStep starvingController .heartbeat (offset + 1)).action.evidence =
            .starve) ∧
      (retainedFinitePrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting starvingClaim
          starving_locally_valid
          (starvingController.canonicalExecution starvingClaim.root)
          (steps + 1)).target = .waiting ∧
      ¬ starvingController.BuchiWinning
          (auditedLabeledSystem Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting)
          starvingClaim.root := by
  have reflected :=
    runIndexed_complete_reflects_retainedPrefix Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
          serviceAccepting
      starvingClaim starving_locally_valid
      (starvingController.canonicalExecution starvingClaim.root) (steps + 1)
      capacity fits
  have stall := starving_run_exposes_stall steps capacity fits
  refine ⟨stall.1, reflected.2.1, reflected.2.2.1, reflected.2.2.2.1,
      reflected.2.2.2.2.1, stall.2.1, stall.2.2.1, ?_, starving_not_recurrent⟩
  · have same := stall.2.2.2.1
    unfold starvingClaim at reflected
    rw [reflected.2.2.2.1] at same
    exact congrArg (fun node => node.phase) (List.cons.inj same).1

/-- One finished yielding step, the checked three-step operational prefix, and
Büchi acceptance of the service phase still do not serve client identity `1`.
The finite `admit` label recurs on its own carrier. -/
theorem finite_produced_prefix_and_recurrence_do_not_serve_client_one :
    ((runIndexed yieldingController .heartbeat 1 (some 1)).memory.2).bind
        Prefix.complete? =
      some (recordedPrefix yieldingController .heartbeat 1) ∧
    ((runIndexed yieldingController .heartbeat 3 (some 3)).memory.2).bind
        Prefix.complete? =
      some (recordedPrefix yieldingController .heartbeat 3) ∧
    (retainedFinitePrefix
        Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
        serviceAccepting yieldingClaim yielding_locally_valid
        (yieldingController.canonicalExecution yieldingClaim.root) 3).execution =
      namedRevisionPrefix
        Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
        serviceAccepting yieldingClaim yielding_locally_valid
        (yieldingController.canonicalExecution yieldingClaim.root) 3 ∧
    yieldingController.BuchiWinning
      (auditedLabeledSystem
        Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Monitor.stepAuthority
        serviceAccepting)
      yieldingClaim.root ∧
    (∀ lower, ∃ step, lower ≤ step ∧ Scope.admissionLabel step = .admit) ∧
    (∀ step, Scope.admissionLabel step = .admit →
      Scope.admittedIdentity step ≠ 1) := by
  have cycle := yielding_produced_cycle_matches_retained_prefix
  exact ⟨runIndexed_complete yieldingController .heartbeat 1 1 (Nat.le_refl 1),
    cycle.1, cycle.2.2.2.2.1, yielding_buchi_of_admission,
    Scope.finite_labels_do_not_fairly_serve_unbounded_identities.1,
    Scope.finite_labels_do_not_fairly_serve_unbounded_identities.2⟩

end Controls

/-! ## Negative control: finite paths are not recurrence -/

namespace Canary

open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Canary

def nonacceptingExecution :
    ControlledExecution loopController loopClaim.root :=
  loopController.canonicalExecution loopClaim.root

/-- Even the nonaccepting loop constructs an exact retained path of every
finite depth and satisfies the corresponding endpoint reachability sentence. -/
theorem nonaccepting_loop_has_every_operational_prefix :
    forall depth,
      (retainedFinitePrefix loopStepAuthority neverAccepting loopClaim
          (loop_locally_valid neverAccepting) nonacceptingExecution
          depth).executionPath.length = depth /\
        loopClaim.root ∈ reachesTargetSentence
          (auditedRevisionTheory loopStepAuthority neverAccepting)
          (nonacceptingExecution.state depth) := by
  intro depth
  exact ⟨retainedFinitePrefix_executionPath_length loopStepAuthority
      neverAccepting loopClaim (loop_locally_valid neverAccepting)
      nonacceptingExecution depth,
    finiteRoute_in_reachesTargetSentence
      (retainedFinitePrefix loopStepAuthority neverAccepting loopClaim
        (loop_locally_valid neverAccepting) nonacceptingExecution depth).erase⟩

/-- Finite operational productivity does not imply Buechi recurrence.  This
rules out treating a stream of successful prefixes as a liveness proof. -/
theorem finite_operational_prefixes_do_not_imply_recurrence :
    (forall depth,
      (retainedFinitePrefix loopStepAuthority neverAccepting loopClaim
          (loop_locally_valid neverAccepting) nonacceptingExecution
          depth).executionPath.length = depth /\
        loopClaim.root ∈ reachesTargetSentence
          (auditedRevisionTheory loopStepAuthority neverAccepting)
          (nonacceptingExecution.state depth)) /\
      ¬ loopController.BuchiWinning
        (auditedLabeledSystem loopStepAuthority neverAccepting)
        loopClaim.root :=
  ⟨nonaccepting_loop_has_every_operational_prefix,
    nonaccepting_loop_not_recurrent⟩

end Canary

/-! ## A counter-carrying alternating monitor

The two-phase message contract keeps its counter in the concrete state.
Only the declared phase observation has a finite carrier. Native printing,
arithmetic and evaluator-yield fidelity are separate service obligations;
these semantic transitions do not count native evaluator quanta.
-/

namespace AlternatingMonitor

inductive Phase where
  | heartbeat | service
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  counter : Nat
  deriving DecidableEq, Repr

def phaseCode : Phase → Fin 2
  | .heartbeat => 0
  | .service => 1

theorem phaseCode_injective : Function.Injective phaseCode := by
  intro left right same
  cases left <;> cases right <;> simp_all [phaseCode]

def nextPhase : Phase → Phase
  | .heartbeat => .service
  | .service => .heartbeat

def next : State → State
  | ⟨.heartbeat, counter⟩ => ⟨.service, counter⟩
  | ⟨.service, counter⟩ => ⟨.heartbeat, counter + 1⟩

def controller : MemorylessController State State where
  active _ := true
  action := id
  next := next

def phaseController : MemorylessController Phase Phase where
  active _ := true
  action := id
  next := nextPhase

theorem local_phase (state : State) :
    (controller.next state).phase = phaseController.next state.phase := by
  rcases state with ⟨phase, counter⟩
  cases phase <;> rfl

/-- The local transition law supplies the phase observation for every finite
advance. It is not a supplied completed-run equality. -/
theorem advance_phase (fuel : Nat) (state : State) :
    (advanceState controller fuel state).phase =
      advanceState phaseController fuel state.phase := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [advanceState_succ, advanceState_succ]
      exact (local_phase _).trans (congrArg phaseController.next ih)

/-- A second burst starts at the retained counter, not the initial root. -/
theorem advance_resume (first second : Nat) (state : State) :
    advanceState controller (first + second) state =
      advanceState controller second (advanceState controller first state) := by
  unfold advanceState
  rw [Nat.add_comm first second, Function.iterate_add_apply]

theorem two_steps (state : State) :
    advanceState controller 2 state = ⟨state.phase, state.counter + 1⟩ := by
  rcases state with ⟨phase, counter⟩
  cases phase <;> rfl

theorem even_advance (counter cycles : Nat) :
    advanceState controller (2 * cycles) ⟨.heartbeat, counter⟩ =
      ⟨.heartbeat, counter + cycles⟩ := by
  induction cycles with
  | zero => simp [advanceState]
  | succ cycles ih =>
      rw [Nat.mul_succ, advance_resume, ih, two_steps]
      simp only [Nat.add_assoc]

theorem odd_advance (counter cycles : Nat) :
    advanceState controller (2 * cycles + 1) ⟨.heartbeat, counter⟩ =
      ⟨.service, counter + cycles⟩ := by
  rw [advanceState_succ, even_advance]
  rfl

/-- Both phases recur beyond every finite cut, while the full state remains
unbounded. This is phase recurrence, not per-request service or fairness. -/
theorem phase_recurrence (counter lower : Nat) :
    ∃ heartbeat service : Nat, lower ≤ heartbeat ∧ lower ≤ service ∧
      (advanceState controller heartbeat ⟨.heartbeat, counter⟩).phase = .heartbeat ∧
      (advanceState controller service ⟨.heartbeat, counter⟩).phase = .service := by
  refine ⟨2 * (lower + 1), 2 * (lower + 1) + 1, by omega, by omega, ?_, ?_⟩
  · rw [even_advance]
  · rw [odd_advance]

theorem concrete_counter_unbounded (bound : Nat) :
    ∃ fuel, bound < (advanceState controller fuel ⟨.heartbeat, 0⟩).counter := by
  refine ⟨2 * (bound + 1), ?_⟩
  rw [even_advance]
  simp

def projectRecord (record : StepRecord State State) : StepRecord Phase Phase where
  index := record.index
  source := record.source.phase
  action := record.action.phase
  target := record.target.phase

/-- Endpoints and temporal occurrence indices are projected together. The
source history, including its full counter values, is retained independently. -/
theorem record_phase (root : State) (index : Nat) :
    projectRecord (recordedStep controller root index) =
      recordedStep phaseController root.phase index := by
  unfold projectRecord recordedStep
  change (⟨index, (advanceState controller index root).phase,
    (advanceState controller index root).phase,
    (advanceState controller (index + 1) root).phase⟩ : StepRecord Phase Phase) = _
  rw [advance_phase, advance_phase]
  rfl

theorem prefix_phase (root : State) (fuel : Nat) :
    (recordedPrefix controller root fuel).map projectRecord =
      recordedPrefix phaseController root.phase fuel := by
  unfold recordedPrefix
  rw [List.map_map]
  apply List.map_congr_left
  intro index _
  exact record_phase root index

/-- The optional recorder observes the actual run and projects its complete
prefix; it does not construct a replacement execution from phase labels. -/
theorem recorded_phase (root : State) (fuel capacity : Nat) (fits : fuel ≤ capacity) :
    (((runIndexed controller root fuel (some capacity)).memory.2).bind
      Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix.complete?).map
        (List.map projectRecord) =
      some (recordedPrefix phaseController root.phase fuel) := by
  rw [runIndexed_complete controller root fuel capacity fits, Option.map_some, prefix_phase]

theorem recorded_frontier (root : State) (fuel : Nat) (capacity : Option Nat) :
    (runIndexed controller root fuel capacity).search.frontier =
      [{ index := fuel, phase := advanceState controller fuel root }] :=
  runIndexed_frontier_eq_advanceState controller root fuel capacity

/-- Re-entering heartbeat with zero after every service has the same finite
phase diagram but loses the counter that the actual message observer sees. -/
def resettingController : MemorylessController State State where
  active _ := true
  action := id
  next state := ⟨nextPhase state.phase, 0⟩

theorem phase_labels_do_not_detect_restarting :
    ((recordedPrefix controller ⟨.heartbeat, 0⟩ 4).map (fun record => record.action.phase)) =
      ((recordedPrefix resettingController ⟨.heartbeat, 0⟩ 4).map
        (fun record => record.action.phase)) ∧
    ((recordedPrefix controller ⟨.heartbeat, 0⟩ 4).map StepRecord.action) ≠
      ((recordedPrefix resettingController ⟨.heartbeat, 0⟩ 4).map StepRecord.action) := by
  decide

theorem two_bursts_preserve_printed_counter :
    (recordedPrefix controller ⟨.heartbeat, 0⟩ 4).map StepRecord.action =
      [⟨.heartbeat, 0⟩, ⟨.service, 0⟩, ⟨.heartbeat, 1⟩, ⟨.service, 1⟩] := by
  decide

end AlternatingMonitor

#print axioms namedRevisionPrefix
#print axioms retainedFinitePrefix_erases_to_finitePrefix
#print axioms retainedFinitePrefix_executionPath_length
#print axioms retainedFinitePrefix_executionPath_succ
#print axioms AuditedRecurrentExecution.ofAccepted
#print axioms AuditedRecurrentExecution.operational_prefixes_and_recurrence
#print axioms Canary.nonaccepting_loop_has_every_operational_prefix
#print axioms Canary.finite_operational_prefixes_do_not_imply_recurrence
#print axioms runIndexed_complete_reflects_retainedPrefix
#print axioms runIndexed_truncation_keeps_checked_endpoint
#print axioms runIndexed_late_reflects_retained_suffix
#print axioms yielding_produced_cycle_matches_retained_prefix
#print axioms starving_produced_record_stalls
#print axioms finite_produced_prefix_and_recurrence_do_not_serve_client_one

end Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteBridge
