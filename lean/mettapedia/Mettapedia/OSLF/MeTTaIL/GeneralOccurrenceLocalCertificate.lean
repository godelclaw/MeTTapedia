import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalWork
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceArchiveCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceAdjacencyTracking
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceModalReadouts

/-!
# Local drained jobs certify all equation-free occurrences

The source visit, all generated jobs, every typed matcher alternative and
every ordered premise result remain tracked by the existing archive and
publication invariants. In an equation-free profile there are no semantic
equation edges at any source, so these local archives establish the complete
occurrence and endpoint contracts without enumerating ambient terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open GeneralOccurrenceKeys GeneralOccurrenceSemantics

inductive Reachable (request : Request) : State request → Prop where
  | start : Reachable request (start request)
  | tick {state : State request} : Reachable request state → Reachable request (tick request state)

theorem reachable_run {request : Request} {state : State request}
    (reached : Reachable request state) (fuel : Nat) :
    Reachable request (GeneralOccurrenceFrontier.run request fuel state) := by
  induction fuel generalizing state with
  | zero => exact reached
  | succ fuel ih => exact ih (.tick reached)

theorem run_reachable (request : Request) (fuel : Nat) : Reachable request (run request fuel) :=
  reachable_run .start fuel

theorem ruleCoverage_start (request : Request) : RuleCoverage request (start request) := by
  intro representative visited
  unfold start at visited
  split at visited <;> simp only [List.not_mem_nil] at visited

theorem rulePublication_start (request : Request) : RulePublication request (start request) := by
  intro frame tracked
  unfold RuleTracked start at tracked
  split at tracked <;> simp at tracked

theorem ruleArchiveUnresolved_start (request : Request) : RuleArchiveUnresolved request (start request) := by
  intro archive member
  unfold start at member
  split at member <;> simp only [List.not_mem_nil] at member

theorem reachable_ruleCoverage {request : Request} {state : State request}
    (reached : Reachable request state) : RuleCoverage request state := by
  induction reached with
  | start => exact ruleCoverage_start request
  | tick _ ih => exact GeneralOccurrenceFrontier.ruleCoverage_tick request _ ih

theorem reachable_rulePublication {request : Request} {state : State request}
    (reached : Reachable request state) : RulePublication request state := by
  induction reached with
  | start => exact rulePublication_start request
  | tick _ ih => exact GeneralOccurrenceFrontier.rulePublication_tick request _ ih

theorem reachable_ruleArchiveUnresolved {request : Request} {state : State request}
    (reached : Reachable request state) : RuleArchiveUnresolved request state := by
  induction reached with
  | start => exact ruleArchiveUnresolved_start request
  | tick _ ih => exact GeneralOccurrenceFrontier.ruleArchiveUnresolved_tick request _ ih

theorem settled_rule_archived {request : Request} {state : State request}
    (reached : Reachable request state) (idle : state.agenda = [])
    (representative : Representative request) (visited : representative ∈ state.visited)
    (job : GeneralRuleJobs.Job)
    (member : job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern) :
    ∃ archive ∈ state.checkedRules,
      archive.frame.representative = representative ∧ archive.frame.job = job := by
  obtain ⟨frame, same, sameJob, tracked⟩ := reachable_ruleCoverage reached representative visited job member
  rcases tracked with active | ⟨archive, archived, exactFrame⟩
  · simp only [idle, List.not_mem_nil] at active
  · exact ⟨archive, archived, exactFrame ▸ same, exactFrame ▸ sameJob⟩

theorem ruleArchive_complete {request : Request} {state : State request}
    (reached : Reachable request state) (resolved : state.unresolved = [])
    (archive : RuleArchive request) (archived : archive ∈ state.checkedRules) :
    GeneralRuleJobExecution.complete archive.frame.state = true := by
  apply (GeneralRuleJobExecution.complete_iff archive.frame.state).mpr
  refine ⟨List.isEmpty_iff.mp archive.settled, ?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reason member
  have published := reachable_ruleArchiveUnresolved reached archive archived reason member
  simp only [resolved, List.not_mem_nil] at published

theorem completed_ruleJobCertified {request : Request} {state : State request}
    (reached : Reachable request state) (completed : complete request state = true)
    (representative : Representative request) (visited : representative ∈ state.visited)
    (job : GeneralRuleJobs.Job)
    (member : job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern) :
    RuleJobCertified request state representative job := by
  have facts := (complete_iff request state).mp completed
  obtain ⟨archive, archived, same, sameJob⟩ :=
    settled_rule_archived reached facts.1 representative visited job member
  refine ⟨archive, archived, congrArg Representative.pattern same, congrArg ruleJob sameJob,
    ruleArchive_complete reached facts.2.1 archive archived, ?_⟩
  intro answer emitted
  have read := reachable_rulePublication reached archive.frame (Or.inr ⟨archive, archived, rfl⟩)
  have published := ruleArchive_answers_published archive read answer emitted
  exact List.mem_map.mpr ⟨publishRuleAnswer request archive.frame answer, published, rfl⟩

theorem completed_representedJobsChecked {request : Request} {state : State request}
    (reached : Reachable request state) (completed : complete request state = true) :
    representedJobsChecked request state = true := by
  apply List.all_eq_true.mpr
  intro representative visited
  apply List.all_eq_true.mpr
  intro job member
  exact (ruleJobChecked_iff request state representative job).mpr
    (completed_ruleJobCertified reached completed representative visited job member)

theorem root_tracked_start {request : Request} (admitted : Admitted request) :
    PatternTracked request (start request) request.root := by
  right
  refine ⟨.visit (rootRepresentative request), ?_, rfl⟩
  simp [start, sourceChecked, checkOpenPatternWellSorted_complete admitted.rootSorted]

theorem reachable_root_tracked {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) : PatternTracked request state request.root := by
  induction reached with
  | start => exact root_tracked_start admitted
  | tick _ ih => exact patternTracked_tick request _ _ ih

theorem edges_empty {request : Request} (empty : request.plan.equations = []) (state : State request) :
    state.edges = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro edge _
  have selected := edge.valid.job.1
  rw [empty] at selected
  exact List.not_mem_nil selected

theorem equation_impossible {request : Request} (empty : request.plan.equations = []) (source target : Pattern) :
    ¬ Equation request.plan request.bound request.expected source target := by
  rintro ⟨receipt, completion, _⟩
  have selected := completion.job.1
  rw [empty] at selected
  exact List.not_mem_nil selected

theorem equation_equivalence_is_equality {request : Request} (empty : request.plan.equations = [])
    {first second : Pattern} (equivalent : Relation.EqvGen
      (Equation request.plan request.bound request.expected) first second) : first = second := by
  induction equivalent with
  | rel first second related => exact False.elim (equation_impossible empty first second related)
  | refl first => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- Every drained job and every published occurrence is checked. Empty
equation generators discharge all equation-source obligations uniformly. -/
theorem completed_checkCertificate {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = []) {state : State request}
    (reached : Reachable request state) (completed : complete request state = true) :
    checkCertificate request state = true := by
  have idle := ((complete_iff request state).mp completed).1
  have root := tracked_when_settled (reachable_root_tracked admitted reached) idle
  have rules := completed_representedJobsChecked reached completed
  have equations : universeJobsChecked request state = true := by
    simp only [universeJobsChecked, empty, List.isEmpty_nil, if_true]
  have adjacent : adjacencyChecked request state = true := by
    simp only [adjacencyChecked, edges_empty empty state, List.all_nil]
  simp only [checkCertificate, completed, decide_eq_true root, equations, rules,
    adjacent, Bool.and_self]

/-- Occurrence completeness retains each exact physical firing, rather than
merely showing that its endpoint belongs to a finite successor set. -/
theorem completed_occurrence_coverage {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = []) {state : State request}
    (reached : Reachable request state) (completed : complete request state = true)
    (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid request.plan request.bound request.expected request.root) :
    ∃ answer ∈ state.answers,
      answer.val.representative = request.root ∧ answer.val.firing = receipt :=
  certified_physical_occurrence admitted (completed_checkCertificate admitted empty reached completed)
    request.root (.refl _) receipt valid

theorem completed_endpoint_coverage {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = []) {state : State request}
    (reached : Reachable request state) (completed : complete request state = true) (target : Pattern) :
    target ∈ targets request state ↔ (gslt request.plan request.bound request.expected).Step request.root target := by
  rw [← certified_successor_classes admitted (completed_checkCertificate admitted empty reached completed) target]
  constructor
  · intro member
    obtain ⟨answer, present, same⟩ := List.mem_map.mp member
    exact ⟨answer, present, same ▸ Relation.EqvGen.refl _⟩
  · rintro ⟨answer, present, equivalent⟩
    exact List.mem_map.mpr ⟨answer, present, equation_equivalence_is_equality empty equivalent⟩

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree
