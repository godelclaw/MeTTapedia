import Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine
import Mettapedia.OSLF.MeTTaIL.StructuralDescentExecution
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledExecution

/-!
# Collection matching as a backend of the generic root service

The collection allocator chooses a presentation and checks its proof-relevant
receipt.  The adapter then obtains an ordinary checked scoped-matcher answer at
that presentation.  Downstream typing, premises, reduct checking and receipt
construction can therefore consume the same matcher payload as every other
rule instead of using a second execution pipeline.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend

open Syntax CanonicalBags CollectionMatcherCompatibility

structure RootReady (request : ScopedCollectionMachine.Request) : Prop where
  ambient : request.ambient = 0
  site : request.site = .left
  path : request.path = []
  depth : request.depth = 0
  index : request.index = 0
  initial : request.initial = []
  schema : request.rule.left = .collection request.kind request.schemas request.rest

theorem request_ready {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {ordinal : Nat} {targets : List Pattern}
    {request : ScopedCollectionMachine.Request}
    (made : CollectionExecutionAdmission.request? plan certificate ordinal targets = some request) :
    RootReady request := by
  unfold CollectionExecutionAdmission.request? at made
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at made
  obtain ⟨declaration, _, made⟩ := made
  cases left : declaration.rule.left <;> simp [left] at made
  rename_i kind schemas rest
  cases kind with
  | vec => simp at made
  | hashBag | hashSet =>
      cases made
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, left⟩

/-- An ordinary checked answer selected by one collection firing. Membership
in `ordinaryAnswers` retains both its checker proof and agreement with the
collection assignment. -/
abbrev Adapted (firing : CollectionPlanMachine.Firing) :=
  {answer : {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid (ordinaryRequest firing.request firing.receipt.source)} //
    answer ∈ ordinaryAnswers firing.request firing.receipt.source}

def adaptations (firing : CollectionPlanMachine.Firing) : List (Adapted firing) :=
  (ordinaryAnswers firing.request firing.receipt.source).attach

theorem Adapted.assignment_eq {firing : CollectionPlanMachine.Firing}
    (adapted : Adapted firing) :
    adapted.val.val.assignment = firing.receipt.source.matching.assignment := by
  have selected := (List.mem_filter.mp adapted.property).2
  exact beq_iff_eq.mp selected

theorem adaptations_nonempty {firing : CollectionPlanMachine.Firing}
    (rootIndex : firing.request.index = 0)
    (unordered : firing.request.kind ≠ .vec)
    (valid : firing.Valid) : ∃ adapted, adapted ∈ adaptations firing := by
  obtain ⟨answer, member, _⟩ := ordinaryAnswers_complete rootIndex unordered valid.1
  refine ⟨⟨answer, member⟩, ?_⟩
  simpa only [adaptations] using
    (List.mem_attach (ordinaryAnswers firing.request firing.receipt.source) ⟨answer, member⟩)

/-- Every adapted answer is checked by the ordinary matcher at a presentation
equal to the collection source in the bag/set model. -/
theorem Adapted.source_equivalent {firing : CollectionPlanMachine.Firing}
    (_adapted : Adapted firing)
    (unordered : firing.request.kind ≠ .vec)
    (fixed : arrange firing.request.kind firing.request.targets = firing.request.targets)
    (valid : firing.Valid) :
    Relation.EqvGen BagStep
      (.collection firing.request.kind firing.request.targets none)
      (ordinaryTarget firing.request firing.receipt.source) :=
  valid_ordinary_target_equivalent unordered fixed valid.1

/-- A plan publication retains the authored plan coordinate and always adapts
to at least one ordinary checked matcher answer. -/
theorem publication_adapts
    (requests : List (Nat × ScopedCollectionMachine.Request)) (fuel : Nat)
    {firing : CollectionPlanMachine.Firing}
    (published : firing ∈ CollectionPlanMachine.publication
      (CollectionPlanMachine.resume fuel (CollectionPlanMachine.start requests)))
    (root : ∀ entry ∈ requests, entry.2.index = 0)
    (unordered : ∀ entry ∈ requests, entry.2.kind ≠ .vec) :
    (firing.ordinal, firing.request) ∈ requests ∧
      ∃ adapted, adapted ∈ adaptations firing := by
  have origin := CollectionPlanMachine.publication_origin fuel requests published
  have valid := CollectionPlanMachine.publication_sound fuel requests published
  exact ⟨origin, adaptations_nonempty
    (root (firing.ordinal, firing.request) origin)
    (unordered (firing.ordinal, firing.request) origin) valid⟩

theorem source_publication_adapts
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (fuel : Nat) {firing : CollectionPlanMachine.Firing}
    (published : firing ∈ CollectionPlanMachine.publication
      (CollectionPlanMachine.resume fuel (CollectionPlanMachine.start
        (CollectionExecutionAdmission.requestsForSource plan certificate source)))) :
    (firing.ordinal, firing.request) ∈
        CollectionExecutionAdmission.requestsForSource plan certificate source ∧
      RootReady firing.request ∧ ∃ adapted, adapted ∈ adaptations firing := by
  let requests := CollectionExecutionAdmission.requestsForSource plan certificate source
  have origin : (firing.ordinal, firing.request) ∈ requests :=
    CollectionPlanMachine.publication_origin fuel requests published
  have selectedForSource := CollectionExecutionAdmission.requestsForSource_selected origin
  obtain ⟨targets, selected⟩ :=
    CollectionExecutionAdmission.requestForSource?_requested selectedForSource
  have valid := CollectionPlanMachine.publication_sound fuel requests published
  exact ⟨by simpa only [requests] using origin, request_ready selected,
    adaptations_nonempty (request_ready selected).index
      (CollectionExecutionAdmission.request?_unordered selected) valid⟩

def Adapted.rootAnswer {firing : CollectionPlanMachine.Firing}
    (adapted : Adapted firing) (ready : RootReady firing.request) :
    {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨firing.request.rule, firing.request.spec, 0, .left, [], 0, [],
        firing.request.rule.left, ordinaryTarget firing.request firing.receipt.source⟩} :=
  ⟨adapted.val.val, by
    rw [ready.schema]
    simpa only [ordinaryRequest, ScopedCollectionMachine.Request.machine,
      ready.ambient, ready.site, ready.path, ready.depth, ready.initial] using
      adapted.val.property⟩

/-- Run the shared typed/premise/reduct continuation on an adapted collection
answer. This is the join point with the generic root service. -/
def finishAdapted
    (environment : GeneralPremise.Environment)
    (oracle : StructuralDescent.Execution.Oracle environment)
    (type : TypeExpr) (firing : CollectionPlanMachine.Firing)
    (adapted : Adapted firing) (ready : RootReady firing.request)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (ordinaryTarget firing.request firing.receipt.source)) :
    List (StructuralDescent.Execution.RootAnswer environment [] type
      (ordinaryTarget firing.request firing.receipt.source)) := by
  exact StructuralDescent.Execution.finishRootMatch environment oracle [] type
    (ordinaryTarget firing.request firing.receipt.source) firing.ordinal
    firing.request.rule firing.request.spec declared specified admitted sourceTyped
    (adapted.rootAnswer ready)

/-- The same adapter enters the fair scheduled executor used by the complete
explorer and emitted runner. -/
def continueAdapted
    (environment : GeneralPremise.Environment)
    (outer : StructuralDescent.Scheduled.Goal) (depth : Nat)
    (type : TypeExpr) (firing : CollectionPlanMachine.Firing)
    (adapted : Adapted firing) (ready : RootReady firing.request)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (ordinaryTarget firing.request firing.receipt.source))
    (tail : StructuralDescent.Scheduled.Continuation environment
      (.root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
        firing.ordinal) outer)
    (next : List (StructuralDescent.Scheduled.Task environment outer)) :
    GeneralPremise.Scheduler.Expansion (StructuralDescent.Scheduled.Task environment outer)
      (StructuralDescent.Scheduled.Result environment outer)
      StructuralDescent.Scheduled.Obligation :=
  StructuralDescent.Scheduled.continueRootAnswer environment outer depth [] type
    (ordinaryTarget firing.request firing.receipt.source) firing.ordinal
    firing.request.rule firing.request.spec declared specified admitted sourceTyped
    (adapted.rootAnswer ready).val (adapted.rootAnswer ready).property tail next

/-- A collection match enters the same scheduled executor as an ordinary root
match, starting immediately after matching. -/
def startAdapted
    (environment : GeneralPremise.Environment) (depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing) (adapted : Adapted firing)
    (ready : RootReady firing.request)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (ordinaryTarget firing.request firing.receipt.source)) :
    StructuralDescent.Scheduled.State environment
      (.root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
        firing.ordinal) :=
  let goal : StructuralDescent.Scheduled.Goal :=
    .root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
      firing.ordinal
  let expanded := continueAdapted environment goal depth type firing adapted ready
    declared specified admitted sourceTyped (.done goal) []
  { agenda := expanded.tasks, answers := expanded.answers,
    unresolved := expanded.unresolved, work := 0 }

@[simp] theorem startAdapted_work
    (environment : GeneralPremise.Environment) (depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing) (adapted : Adapted firing)
    (ready : RootReady firing.request)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (ordinaryTarget firing.request firing.receipt.source)) :
    (startAdapted environment depth type firing adapted ready declared specified admitted
      sourceTyped).work = 0 := rfl

end Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
