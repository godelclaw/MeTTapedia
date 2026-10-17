import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceReceiptKeys
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceTermination

/-!
# Executable retained coverage-certificate checks

The certificate checks every generated equation job in the source-derived
universe, every generated rule job at the reached representatives, and the
full answer readouts of the retained drained executions. Equation adjacency
is checked in both directions. Comparing complete occurrence keys retains
declaration, typing, matcher and premise origins beside the endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open GeneralOccurrenceKeys

def edgeKey {request : Request} (edge : Edge request) : Syntax.Pattern × EquationReplayRecord :=
  ⟨edge.source, equationReplayRecord edge.receipt⟩

def answerKeys (request : Request) (state : State request) : List (Syntax.Pattern × RuleReplayRecord) :=
  state.answers.map fun answer => replayOccurrence answer.val

def edgeKeys (request : Request) (state : State request) : List (Syntax.Pattern × EquationReplayRecord) :=
  state.edges.map edgeKey

def representedPatterns (request : Request) (state : State request) : List Syntax.Pattern :=
  state.visited.map Representative.pattern

def equationArchiveRead (request : Request) (state : State request) (archive : EquationArchive request) : Bool :=
  archive.frame.state.answers.all fun answer =>
    decide ((archive.frame.source, equationReplayRecord answer.val) ∈ edgeKeys request state)

def ruleArchiveRead (request : Request) (state : State request) (archive : RuleArchive request) : Bool :=
  archive.frame.state.answers.all fun answer =>
    decide ((archive.frame.representative.pattern, ruleReplayRecord answer.val) ∈ answerKeys request state)

def equationJobChecked (request : Request) (state : State request) (source : Syntax.Pattern)
    (job : GeneralEquationJobs.Job) : Bool :=
  state.checkedEquations.any fun archive =>
    decide (archive.frame.source = source) &&
    decide (equationJob archive.frame.job = equationJob job) &&
    GeneralEquationJobExecution.complete archive.frame.state && equationArchiveRead request state archive

def ruleJobChecked (request : Request) (state : State request) (representative : Representative request)
    (job : GeneralRuleJobs.Job) : Bool :=
  state.checkedRules.any fun archive =>
    decide (archive.frame.representative.pattern = representative.pattern) &&
    decide (ruleJob archive.frame.job = ruleJob job) &&
    GeneralRuleJobExecution.complete archive.frame.state && ruleArchiveRead request state archive

def universeJobsChecked (request : Request) (state : State request) : Bool :=
  if request.plan.equations.isEmpty then true
  else request.universe.all fun source =>
      (GeneralEquationJobs.jobs request.plan request.bound request.expected source).all
        (equationJobChecked request state source)

def representedJobsChecked (request : Request) (state : State request) : Bool :=
  state.visited.all fun representative =>
    (GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern).all
      (ruleJobChecked request state representative)

def adjacencyChecked (request : Request) (state : State request) : Bool :=
  state.edges.all fun edge =>
    decide ((edge.source ∈ representedPatterns request state →
      edge.receipt.target ∈ representedPatterns request state) ∧
      (edge.receipt.target ∈ representedPatterns request state →
        edge.source ∈ representedPatterns request state))

def checkCertificate (request : Request) (state : State request) : Bool :=
  complete request state && decide (request.root ∈ representedPatterns request state) &&
    universeJobsChecked request state && representedJobsChecked request state && adjacencyChecked request state

def EquationJobCertified (request : Request) (state : State request)
    (source : Syntax.Pattern) (job : GeneralEquationJobs.Job) : Prop :=
  ∃ archive ∈ state.checkedEquations,
    archive.frame.source = source ∧ equationJob archive.frame.job = equationJob job ∧
      GeneralEquationJobExecution.complete archive.frame.state = true ∧
      ∀ answer ∈ archive.frame.state.answers,
        (archive.frame.source, equationReplayRecord answer.val) ∈ edgeKeys request state

def RuleJobCertified (request : Request) (state : State request)
    (representative : Representative request) (job : GeneralRuleJobs.Job) : Prop :=
  ∃ archive ∈ state.checkedRules,
    archive.frame.representative.pattern = representative.pattern ∧
      ruleJob archive.frame.job = ruleJob job ∧ GeneralRuleJobExecution.complete archive.frame.state = true ∧
      ∀ answer ∈ archive.frame.state.answers,
        (archive.frame.representative.pattern, ruleReplayRecord answer.val) ∈ answerKeys request state

theorem equationJobChecked_iff (request : Request) (state : State request)
    (source : Syntax.Pattern) (job : GeneralEquationJobs.Job) :
    equationJobChecked request state source job = true ↔ EquationJobCertified request state source job := by
  simp only [equationJobChecked, EquationJobCertified, equationArchiveRead,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

theorem ruleJobChecked_iff (request : Request) (state : State request)
    (representative : Representative request) (job : GeneralRuleJobs.Job) :
    ruleJobChecked request state representative job = true ↔ RuleJobCertified request state representative job := by
  simp only [ruleJobChecked, RuleJobCertified, ruleArchiveRead,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

/-- An empty compiled equation list has no equation job at any source, so
coverage needs no traversal of an ambient term universe in this case. -/
theorem universeJobsChecked_iff (request : Request) (state : State request) :
    universeJobsChecked request state = true ↔
      ∀ source ∈ request.universe,
        ∀ job ∈ GeneralEquationJobs.jobs request.plan request.bound request.expected source,
          EquationJobCertified request state source job := by
  unfold universeJobsChecked
  split
  · rename_i empty
    have absent := List.isEmpty_iff.mp empty
    simp only [GeneralEquationJobs.jobs, absent, List.zipIdx_nil, List.flatMap_nil,
      List.not_mem_nil, false_implies, implies_true]
  · simp only [List.all_eq_true, equationJobChecked_iff]

theorem checkCertificate_iff (request : Request) (state : State request) :
    checkCertificate request state = true ↔
      complete request state = true ∧ request.root ∈ representedPatterns request state ∧
      (∀ source ∈ request.universe, ∀ job ∈ GeneralEquationJobs.jobs request.plan request.bound request.expected source,
        EquationJobCertified request state source job) ∧
      (∀ representative ∈ state.visited,
        ∀ job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern,
          RuleJobCertified request state representative job) ∧
      (∀ edge ∈ state.edges,
        (edge.source ∈ representedPatterns request state → edge.receipt.target ∈ representedPatterns request state) ∧
        (edge.receipt.target ∈ representedPatterns request state → edge.source ∈ representedPatterns request state)) := by
  simp only [checkCertificate, representedJobsChecked, adjacencyChecked,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    ruleJobChecked_iff, universeJobsChecked_iff, and_assoc]

theorem unfinished_certificate_rejected (request : Request) (state : State request)
    (unfinished : complete request state = false) : checkCertificate request state = false := by
  simp only [checkCertificate, unfinished, Bool.false_and]

theorem pending_certificate_rejected (request : Request) (state : State request)
    (pending : state.agenda ≠ []) : checkCertificate request state = false :=
  unfinished_certificate_rejected request state (pending_not_complete request state pending)

theorem unresolved_certificate_rejected (request : Request) (state : State request)
    (unresolved : state.unresolved ≠ []) : checkCertificate request state = false :=
  unfinished_certificate_rejected request state (unresolved_not_complete request state unresolved)

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
