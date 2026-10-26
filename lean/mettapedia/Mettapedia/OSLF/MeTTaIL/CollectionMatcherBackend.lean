import Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine
import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch
import Mettapedia.OSLF.MeTTaIL.CanonicalTyping
import Mettapedia.OSLF.MeTTaIL.StructuralDescentExecution
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledExecution
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFrontier
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFootprint
import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot

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

/-- Everything the generic post-match continuation needs from admission and
the collection scheduler, except the source-typing proof transported at the
call site. -/
structure MatchAuthority (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (ordinal : Nat) (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) : Prop where
  origin : (ordinal, request) ∈
    CollectionExecutionAdmission.requestsForSource plan certificate source
  ready : RootReady request
  unordered : request.kind ≠ .vec
  fixed : arrange request.kind request.targets = request.targets
  declared : (GeneralPlanEnvironment.environment plan).language.rewrites[ordinal]? =
    some request.rule
  specified : GeneralPremise.specification? (GeneralPlanEnvironment.environment plan)
    ordinal = some request.spec
  admitted : RuleBinding.admittedFor request.rule request.spec = true
  valid : ScopedCollectionMachine.Valid request receipt

theorem match_authority_of_origin
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) {ordinal : Nat} {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (origin : (ordinal, request) ∈
      CollectionExecutionAdmission.requestsForSource plan certificate source)
    (valid : ScopedCollectionMachine.Valid request receipt) :
    MatchAuthority plan certificate source ordinal request receipt := by
  have selectedForSource := CollectionExecutionAdmission.requestsForSource_selected origin
  obtain ⟨targets, selected⟩ :=
    CollectionExecutionAdmission.requestForSource?_requested selectedForSource
  obtain ⟨declaration, position, ruleEq, specEq, _⟩ :=
    CollectionExecutionAdmission.request?_selected selected
  have member : declaration ∈ plan.rules := List.mem_of_getElem? position
  have declared := GeneralPlanEnvironment.selected_rule plan position
  have specified := GeneralPlanEnvironment.selected_specification plan position
  have admitted := CollectionExecutionAdmission.rules_admitted certificate member
  refine ⟨origin, request_ready selected,
    CollectionExecutionAdmission.request?_unordered selected,
    CollectionExecutionAdmission.requestForSource?_fixed selectedForSource,
    ?_, ?_, ?_, valid⟩
  · simpa only [ruleEq] using declared
  · simpa only [specEq] using specified
  · simpa only [ruleEq, specEq] using admitted

structure HandoffAuthority (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (firing : CollectionPlanMachine.Firing) : Prop where
  origin : (firing.ordinal, firing.request) ∈
    CollectionExecutionAdmission.requestsForSource plan certificate source
  ready : RootReady firing.request
  unordered : firing.request.kind ≠ .vec
  fixed : arrange firing.request.kind firing.request.targets = firing.request.targets
  declared : (GeneralPlanEnvironment.environment plan).language.rewrites[firing.ordinal]? =
    some firing.request.rule
  specified : GeneralPremise.specification? (GeneralPlanEnvironment.environment plan)
    firing.ordinal = some firing.request.spec
  admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true
  valid : firing.Valid

/-- Authored rule authority follows from the selected request and the checked
firing, independently of the scheduler that published it. -/
theorem authority_of_origin
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) {firing : CollectionPlanMachine.Firing}
    (origin : (firing.ordinal, firing.request) ∈
      CollectionExecutionAdmission.requestsForSource plan certificate source)
    (valid : firing.Valid) : HandoffAuthority plan certificate source firing := by
  have raw := match_authority_of_origin plan certificate source origin valid.1
  exact ⟨raw.origin, raw.ready, raw.unordered, raw.fixed, raw.declared,
    raw.specified, raw.admitted, valid⟩

theorem source_publication_authority
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (fuel : Nat) {firing : CollectionPlanMachine.Firing}
    (published : firing ∈ CollectionPlanMachine.publication
      (CollectionPlanMachine.resume fuel (CollectionPlanMachine.start
        (CollectionExecutionAdmission.requestsForSource plan certificate source)))) :
    HandoffAuthority plan certificate source firing :=
  authority_of_origin plan certificate source
    (CollectionPlanMachine.publication_origin fuel _ published)
    (CollectionPlanMachine.publication_sound fuel _ published)

/-- The chronological search retains exactly the authority needed by the
existing generic post-match continuation. -/
theorem logged_publication_authority
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (fuel : Nat) {firing : CollectionPlanMachine.Firing}
    (published : firing ∈ (CollectionLoggedSearch.run plan certificate source fuel).state.log) :
    HandoffAuthority plan certificate source firing := by
  have valid := (CollectionLoggedSearch.search_lawful plan certificate).sound
    source fuel firing published
  exact authority_of_origin plan certificate source valid.1 valid.2

/-- Source typing can be transported before any reduct exists. -/
theorem MatchAuthority.source_equivalent
    {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {ordinal : Nat} {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (authority : MatchAuthority plan certificate source ordinal request receipt) :
    Relation.EqvGen BagStep source (ordinaryTarget request receipt) := by
  have selected := CollectionExecutionAdmission.requestsForSource_selected authority.origin
  obtain ⟨targets, sourceEq, targetEq⟩ :=
    CollectionExecutionAdmission.requestForSource?_target selected
  rw [sourceEq]
  apply collection_equivalent_of_presents authority.unordered
  apply presents_trans ?_
    (presents_append_arrange (valid_allocation_presents authority.unordered authority.fixed authority.valid))
  rw [targetEq]
  exact presents_arrange _ _

theorem MatchAuthority.source_typed
    {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {ordinal : Nat} {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (authority : MatchAuthority plan certificate source ordinal request receipt)
    {type : TypeExpr}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source) :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type (ordinaryTarget request receipt) :=
  CanonicalBags.openPatternWellSorted_of_eqvGen authority.source_equivalent typed

/-- The existing firing adapter uses the same source-match authority. -/
theorem HandoffAuthority.source_equivalent
    {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {firing : CollectionPlanMachine.Firing}
    (authority : HandoffAuthority plan certificate source firing) :
    Relation.EqvGen BagStep source (ordinaryTarget firing.request firing.receipt.source) := by
  let raw : MatchAuthority plan certificate source firing.ordinal firing.request firing.receipt.source :=
    ⟨authority.origin, authority.ready, authority.unordered, authority.fixed,
      authority.declared, authority.specified, authority.admitted, authority.valid.1⟩
  exact raw.source_equivalent

/-- Full open-carrier typing is transported from the source itself; callers
need not separately type each allocation's equivalent presentation. -/
theorem HandoffAuthority.source_typed
    {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {firing : CollectionPlanMachine.Firing}
    (authority : HandoffAuthority plan certificate source firing)
    {type : TypeExpr}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source) :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type
      (ordinaryTarget firing.request firing.receipt.source) :=
  CanonicalBags.openPatternWellSorted_of_eqvGen authority.source_equivalent typed

def ordinaryRootAnswer (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) (ready : RootReady request)
    (answer : {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid (ordinaryRequest request receipt)}) :
    {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨request.rule, request.spec, 0, .left, [], 0, [], request.rule.left,
        ordinaryTarget request receipt⟩} :=
  ⟨answer.val, by
    rw [ready.schema]
    simpa only [ordinaryRequest, ScopedCollectionMachine.Request.machine,
      ready.ambient, ready.site, ready.path, ready.depth, ready.initial] using answer.property⟩

def rawRootAnswers (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) (ready : RootReady request) :=
  (ordinaryAnswers request receipt).map (ordinaryRootAnswer request receipt ready)

theorem rawRootAnswerValues_eq_ordinary (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) (ready : RootReady request) :
    (rawRootAnswers request receipt ready).map Subtype.val =
      ordinaryAnswerValues request receipt := by
  simp only [rawRootAnswers, ordinaryAnswerValues, List.map_map]
  rfl

/-- A source footprint also covers the equal presentation chosen by the
collection allocation. No reduct or completed premise assignment is needed. -/
theorem MatchAuthority.source_free_within
    {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {ordinal : Nat} {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (authority : MatchAuthority plan certificate source ordinal request receipt)
    (footprint : List String)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ (ordinaryTarget request receipt).freeFvarNames, name ∈ footprint := by
  have canonical := (CanonicalBags.canon_iff _ _).mpr authority.source_equivalent
  intro name present
  apply inside name
  apply (CanonicalBags.canon_freeFvarNames source name).mp
  rw [canonical]
  exact (CanonicalBags.canon_freeFvarNames (ordinaryTarget request receipt) name).mpr present

theorem MatchAuthority.captures_free_within
    {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {ordinal : Nat} {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (authority : MatchAuthority plan certificate source ordinal request receipt)
    (footprint : List String)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    ∀ answer ∈ rawRootAnswers request receipt authority.ready,
      ScopedRuleMatching.assignmentFreeWithin footprint answer.val.assignment := by
  intro answer _
  exact GeneralScopedMatch.matched_free_within answer.property.matching footprint
    (by intro entry present; cases present)
    (authority.source_free_within footprint inside)

theorem rawRootAnswers_take_length (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) (ready : RootReady request)
    (unordered : request.kind ≠ .vec) (valid : ScopedCollectionMachine.Valid request receipt) :
    ((rawRootAnswers request receipt ready).take 1).length = 1 := by
  obtain ⟨answer, present, _⟩ := ordinaryAnswers_complete ready.index unordered valid
  have member : ordinaryRootAnswer request receipt ready answer ∈ rawRootAnswers request receipt ready :=
    List.mem_map_of_mem present
  cases shape : rawRootAnswers request receipt ready with
  | nil => rw [shape] at member; cases member
  | cons head rest => simp

def Adapted.rootAnswer {firing : CollectionPlanMachine.Firing}
    (adapted : Adapted firing) (ready : RootReady firing.request) :=
  ordinaryRootAnswer firing.request firing.receipt.source ready adapted.val

/-- The complete certified frontier supplied to the generic continuation.
Every physical ordinary-matcher trace is retained. -/
def rootAnswers (firing : CollectionPlanMachine.Firing)
    (ready : RootReady firing.request) :
    List {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨firing.request.rule, firing.request.spec, 0, .left, [], 0, [],
        firing.request.rule.left, ordinaryTarget firing.request firing.receipt.source⟩} :=
  rawRootAnswers firing.request firing.receipt.source ready

theorem rootAnswerValues_eq_ordinary (firing : CollectionPlanMachine.Firing)
    (ready : RootReady firing.request) :
    (rootAnswers firing ready).map Subtype.val =
      ordinaryAnswerValues firing.request firing.receipt.source := by
  exact rawRootAnswerValues_eq_ordinary firing.request firing.receipt.source ready

/-- One ordinary proof witnesses a recorded collection occurrence. Further
ordinary traces are alternative proofs of that occurrence, not new firings. -/
def selectedRootAnswers (firing : CollectionPlanMachine.Firing)
    (ready : RootReady firing.request) := (rootAnswers firing ready).take 1

theorem selectedRootAnswers_length (firing : CollectionPlanMachine.Firing)
    (ready : RootReady firing.request) (unordered : firing.request.kind ≠ .vec)
    (valid : firing.Valid) : (selectedRootAnswers firing ready).length = 1 := by
  exact rawRootAnswers_take_length firing.request firing.receipt.source ready unordered valid.1

theorem rawRootAnswers_assignment (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) (ready : RootReady request)
    {answer : GeneralScopedMatchMachine.Answer}
    (present : answer ∈ (rawRootAnswers request receipt ready).map Subtype.val) :
    answer.assignment = receipt.matching.assignment := by
  simp only [rawRootAnswers, List.map_map] at present
  obtain ⟨ordinary, ordinaryMember, rfl⟩ := List.mem_map.mp present
  exact beq_iff_eq.mp (List.mem_filter.mp ordinaryMember).2

theorem rootAnswers_assignment {firing : CollectionPlanMachine.Firing}
    (ready : RootReady firing.request)
    {answer : GeneralScopedMatchMachine.Answer}
    (present : answer ∈ (rootAnswers firing ready).map Subtype.val) :
    answer.assignment = firing.receipt.source.matching.assignment :=
  rawRootAnswers_assignment firing.request firing.receipt.source ready present

/-- Changing the ordinary validating trace preserves captures, completed
assignments, premise histories and targets. The source collection firing is
kept separately; no source occurrence or premise branch is identified here. -/
theorem rootAnswer_rewitness
    (environment : GeneralPremise.Environment) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (first second : {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨firing.request.rule, firing.request.spec, 0, .left, [], 0, [],
        firing.request.rule.left, ordinaryTarget firing.request firing.receipt.source⟩})
    (same : first.val.assignment = second.val.assignment)
    (completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (held : GeneralPremise.RootFiring environment [] type
      (ordinaryTarget firing.request firing.receipt.source) firing.ordinal first.val.trace
      first.val.assignment completed history target) :
    GeneralPremise.RootFiring environment [] type
      (ordinaryTarget firing.request firing.receipt.source) firing.ordinal second.val.trace
      second.val.assignment completed history target := by
  cases held with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared' specified' admitted sorted _matched typed premises converted targetTyped =>
      have ruleEq := Option.some.inj (declared'.symm.trans declared)
      have specEq := Option.some.inj (specified'.symm.trans specified)
      subst rule
      subst spec
      rw [same] at typed premises
      exact .fire declared specified admitted sorted second.property typed premises converted targetTyped

/-- Selecting one validating witness preserves all completed assignments,
premise histories and targets available for this recorded source firing. -/
theorem selectedRootAnswers_outcomes_iff
    (environment : GeneralPremise.Environment) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing) (ready : RootReady firing.request)
    (unordered : firing.request.kind ≠ .vec) (valid : firing.Valid)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern) :
    (∃ answer ∈ rootAnswers firing ready,
      GeneralPremise.RootFiring environment [] type
        (ordinaryTarget firing.request firing.receipt.source) firing.ordinal
        answer.val.trace answer.val.assignment completed history target) ↔
    (∃ answer ∈ selectedRootAnswers firing ready,
      GeneralPremise.RootFiring environment [] type
        (ordinaryTarget firing.request firing.receipt.source) firing.ordinal
        answer.val.trace answer.val.assignment completed history target) := by
  constructor
  · rintro ⟨first, present, held⟩
    have length := selectedRootAnswers_length firing ready unordered valid
    cases selected : selectedRootAnswers firing ready with
    | nil => simp [selected] at length
    | cons second rest =>
        have member : second ∈ selectedRootAnswers firing ready := by rw [selected]; simp
        have sourceFirst := rootAnswers_assignment ready (List.mem_map_of_mem present)
        have sourceSecond := rootAnswers_assignment ready
          (List.mem_map_of_mem (List.mem_of_mem_take member))
        exact ⟨second, List.mem_cons_self, rootAnswer_rewitness environment type firing declared specified
          first second (sourceFirst.trans sourceSecond.symm) completed history target held⟩
  · rintro ⟨answer, present, held⟩
    exact ⟨answer, List.mem_of_mem_take present, held⟩

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

/-- Feed the whole collection-selected answer frontier through the same
post-match continuation as the ordinary root matcher. -/
def continueAll
    (environment : GeneralPremise.Environment)
    (outer : StructuralDescent.Scheduled.Goal) (depth : Nat)
    (type : TypeExpr) (firing : CollectionPlanMachine.Firing)
    (ready : RootReady firing.request)
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
  StructuralDescent.Scheduled.continueRootAnswers environment outer depth [] type
    (ordinaryTarget firing.request firing.receipt.source) firing.ordinal
    firing.request.rule firing.request.spec declared specified admitted sourceTyped
    (rootAnswers firing ready) tail next

/-- Start a scheduled generic continuation from every answer selected by one
collection firing. -/
def startAll
    (environment : GeneralPremise.Environment) (depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing) (ready : RootReady firing.request)
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
  let expanded := continueAll environment goal depth type firing ready declared specified
    admitted sourceTyped (.done goal) []
  { agenda := expanded.tasks, answers := expanded.answers,
    unresolved := expanded.unresolved, work := 0 }

/-- Every supplied finite match frontier drains at its selected recursion
depth. Unresolved obligations remain explicit in the resulting state. -/
theorem startAll_eventually_settled
    (environment : GeneralPremise.Environment) (depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing) (ready : RootReady firing.request)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (ordinaryTarget firing.request firing.receipt.source)) :
    ∃ fuel, (StructuralDescent.Scheduled.run environment
      (.root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
        firing.ordinal) fuel
      (startAll environment depth type firing ready declared specified admitted sourceTyped)).agenda = [] := by
  let goal : StructuralDescent.Scheduled.Goal :=
    .root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source) firing.ordinal
  exact StructuralDescent.Scheduled.continueRootAnswers_eventually_settled
    environment goal depth [] type (ordinaryTarget firing.request firing.receipt.source)
    firing.ordinal firing.request.rule firing.request.spec declared specified admitted sourceTyped
    (.done goal) (StructuralDescent.Scheduled.doneTrees environment goal) (rootAnswers firing ready)

/-- Start one recorded firing using a single ordinary validating witness.
Premise alternatives are still explored by the shared scheduled executor. -/
def startRequest
    (environment : GeneralPremise.Environment) (depth : Nat) (type : TypeExpr)
    (ordinal : Nat) (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) (ready : RootReady request)
    (declared : environment.language.rewrites[ordinal]? = some request.rule)
    (specified : GeneralPremise.specification? environment ordinal = some request.spec)
    (admitted : RuleBinding.admittedFor request.rule request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (ordinaryTarget request receipt)) :
    StructuralDescent.Scheduled.State environment
      (.root (depth + 1) [] type (ordinaryTarget request receipt)
        ordinal) :=
  let goal : StructuralDescent.Scheduled.Goal :=
    .root (depth + 1) [] type (ordinaryTarget request receipt) ordinal
  let expanded := StructuralDescent.Scheduled.continueRootAnswers environment goal depth [] type
    (ordinaryTarget request receipt) ordinal request.rule
    request.spec declared specified admitted sourceTyped ((rawRootAnswers request receipt ready).take 1)
    (.done goal) []
  { agenda := expanded.tasks, answers := expanded.answers,
    unresolved := expanded.unresolved, work := 0 }

/-- A semantic typed/premise outcome of a raw collection match is eventually
published by the actual retained continuation. The RHS may be supplied by a
premise; no provisional reduct is required. The depth bounds the independent
premise derivation and does not assume execution already succeeded. -/
theorem startRequest_covers
    (environment : GeneralPremise.Environment) (depth : Nat) (type : TypeExpr)
    (ordinal : Nat) (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) (ready : RootReady request)
    (unordered : request.kind ≠ .vec) (validMatch : ScopedCollectionMachine.Valid request receipt)
    (declared : environment.language.rewrites[ordinal]? = some request.rule)
    (specified : GeneralPremise.specification? environment ordinal = some request.spec)
    (admitted : RuleBinding.admittedFor request.rule request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type (ordinaryTarget request receipt))
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (held : GeneralPremise.RootFiring environment [] type (ordinaryTarget request receipt)
      ordinal trace receipt.matching.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ depth) :
    ∃ fuel chosenTrace, ∃ proved : GeneralPremise.RootFiring environment [] type
        (ordinaryTarget request receipt) ordinal chosenTrace receipt.matching.assignment
        completed history target,
      StructuralDescent.Scheduled.Result.root chosenTrace receipt.matching.assignment
        completed history target proved ∈
      (StructuralDescent.Scheduled.run environment
        (.root (depth + 1) [] type (ordinaryTarget request receipt) ordinal) fuel
        (startRequest environment depth type ordinal request receipt ready declared specified
          admitted sourceTyped)).answers := by
  let answers := (rawRootAnswers request receipt ready).take 1
  have length : answers.length = 1 := rawRootAnswers_take_length request receipt ready unordered validMatch
  obtain ⟨answer, member⟩ : ∃ answer, answer ∈ answers := by
    cases shape : answers with
    | nil => simp [shape] at length
    | cons answer rest => exact ⟨answer, List.mem_cons_self⟩
  have same : answer.val.assignment = receipt.matching.assignment :=
    rawRootAnswers_assignment request receipt ready
      (List.mem_map_of_mem (List.mem_of_mem_take member))
  let goal : StructuralDescent.Scheduled.Goal :=
    .root (depth + 1) [] type (ordinaryTarget request receipt) ordinal
  cases held with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared' specified' admitted' sorted matched typed premises reduced targetTyped =>
      have ruleEq := Option.some.inj (declared'.symm.trans declared)
      have specEq := Option.some.inj (specified'.symm.trans specified)
      subst rule
      subst spec
      have selectedTyped : GeneralPremise.TypedAssignment environment
          ⟨ordinal, request.rule, request.spec, [], 0, 0⟩ answer.val.assignment := by
        rw [same]
        exact typed
      have selectedPremises : GeneralPremise.PremisesHold environment
          ⟨ordinal, request.rule, request.spec, [], 0, 0⟩ request.rule.premises
          answer.val.assignment completed history := by
        rw [same]
        exact premises
      have selectedFiring : GeneralPremise.RootFiring environment [] type
          (ordinaryTarget request receipt) ordinal answer.val.trace answer.val.assignment
          completed history target :=
        .fire declared specified admitted sourceTyped answer.property selectedTyped
          selectedPremises reduced targetTyped
      let wanted : StructuralDescent.Scheduled.Result environment goal :=
        .root answer.val.trace answer.val.assignment completed history target selectedFiring
      have meaning : StructuralDescent.Scheduled.EvaluatesTo
          (.rootBody depth [] type (ordinaryTarget request receipt) ordinal request.rule request.spec
            declared specified admitted sourceTyped answer.val.trace answer.val.assignment
            answer.property selectedTyped (.done goal)) wanted := by
        refine ⟨.premises completed history selectedPremises, ?_, ?_⟩
        · simpa only [StructuralDescent.Scheduled.Interpreted.Result.ordered, decide_eq_true_eq] using bounded
        · exact ⟨target, reduced, targetTyped, rfl⟩
      have accepts := StructuralDescent.Scheduled.continueRootAnswers_covers environment goal depth [] type
        (ordinaryTarget request receipt) ordinal request.rule request.spec declared specified admitted
        sourceTyped (.done goal) answers answer member selectedTyped wanted meaning
      obtain ⟨fuel, drained⟩ := StructuralDescent.Scheduled.continueRootAnswers_eventually_settled
        environment goal depth [] type (ordinaryTarget request receipt) ordinal request.rule request.spec
        declared specified admitted sourceTyped (.done goal)
        (StructuralDescent.Scheduled.doneTrees environment goal) answers
      have emitted := StructuralDescent.Scheduled.continueRootAnswers_drained_contains
        environment goal depth [] type (ordinaryTarget request receipt) ordinal request.rule request.spec
        declared specified admitted sourceTyped (.done goal) answers fuel wanted accepts drained
      have chosen := selectedFiring
      rw [same] at chosen
      refine ⟨fuel, answer.val.trace, chosen, ?_⟩
      convert emitted using 1 <;> simp only [startRequest, answers, goal, wanted, same]
      rfl

def startFiring
    (environment : GeneralPremise.Environment) (depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing) (ready : RootReady firing.request)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (ordinaryTarget firing.request firing.receipt.source)) :
    StructuralDescent.Scheduled.State environment
      (.root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
        firing.ordinal) :=
  startRequest environment depth type firing.ordinal firing.request firing.receipt.source
    ready declared specified admitted sourceTyped

/-- A raw checked match enters the same continuation before an RHS is
instantiated. The original request ordinal and receipt remain its origin. -/
def startMatch
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (depth : Nat) (type : TypeExpr)
    (ordinal : Nat) (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt)
    (authority : MatchAuthority plan certificate source ordinal request receipt)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source) :
    StructuralDescent.Scheduled.State (GeneralPlanEnvironment.environment plan)
      (.root (depth + 1) [] type (ordinaryTarget request receipt) ordinal) :=
  startRequest (GeneralPlanEnvironment.environment plan) depth type ordinal request receipt
    authority.ready authority.declared authority.specified authority.admitted
    (authority.source_typed typed)

/-- The actual post-match tasks stay inside the source footprint. This is
derived from the selected captures, including before an RHS exists. -/
theorem startMatch_free_within
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (depth : Nat) (type : TypeExpr)
    (ordinal : Nat) (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt)
    (authority : MatchAuthority plan certificate source ordinal request receipt)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (footprint : List String)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    StructuralDescent.Scheduled.stateFreeWithin footprint (GeneralPlanEnvironment.environment plan)
      (.root (depth + 1) [] type (ordinaryTarget request receipt) ordinal)
      (startMatch plan certificate source depth type ordinal request receipt authority typed) := by
  let environment := GeneralPlanEnvironment.environment plan
  let presented := ordinaryTarget request receipt
  let goal : StructuralDescent.Scheduled.Goal := .root (depth + 1) [] type presented ordinal
  have sourceWithin := authority.source_free_within footprint inside
  have tasksWithin : ∀ answers : List {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨request.rule, request.spec, 0, .left, [], 0, [], request.rule.left, presented⟩},
      (∀ answer ∈ answers, ScopedRuleMatching.assignmentFreeWithin footprint answer.val.assignment) →
      ∀ task ∈ (StructuralDescent.Scheduled.continueRootAnswers
        (matcher := GeneralPremise.MatchingExecution.ordinary) environment goal depth [] type
        presented ordinal request.rule request.spec authority.declared authority.specified
        authority.admitted (authority.source_typed typed) answers (.done goal) []).tasks,
        StructuralDescent.Scheduled.taskFreeWithin footprint task := by
    intro answers
    induction answers with
    | nil => intro _ task member; cases member
    | cons answer answers ih =>
      intro captures task member
      have later := ih (fun other present => captures other (List.mem_cons_of_mem _ present))
      simp only [StructuralDescent.Scheduled.continueRootAnswers,
        StructuralDescent.Scheduled.continueRootAnswer] at member
      split at member
      · rcases List.mem_cons.mp member with rfl | member
        · exact ⟨⟨authority.admitted, captures answer List.mem_cons_self⟩,
            sourceWithin, captures answer List.mem_cons_self, sourceWithin⟩
        · exact later task member
      · exact later task member
  constructor
  · exact tasksWithin _ (fun answer present =>
      authority.captures_free_within footprint inside answer (List.mem_of_mem_take present))
  · intro result member
    change result ∈ (StructuralDescent.Scheduled.continueRootAnswers environment goal depth [] type
      presented ordinal request.rule request.spec authority.declared authority.specified
      authority.admitted (authority.source_typed typed)
      ((rawRootAnswers request receipt authority.ready).take 1) (.done goal) []).answers at member
    rw [StructuralDescent.Scheduled.continueRootAnswers_answers] at member
    cases member

theorem startMatch_eventually_settled
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (depth : Nat) (type : TypeExpr)
    (ordinal : Nat) (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt)
    (authority : MatchAuthority plan certificate source ordinal request receipt)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source) :
    ∃ fuel, (StructuralDescent.Scheduled.run (GeneralPlanEnvironment.environment plan)
      (.root (depth + 1) [] type (ordinaryTarget request receipt) ordinal) fuel
      (startMatch plan certificate source depth type ordinal request receipt authority typed)).agenda = [] := by
  let environment := GeneralPlanEnvironment.environment plan
  let goal : StructuralDescent.Scheduled.Goal :=
    .root (depth + 1) [] type (ordinaryTarget request receipt) ordinal
  exact StructuralDescent.Scheduled.continueRootAnswers_eventually_settled environment goal depth [] type
    (ordinaryTarget request receipt) ordinal request.rule request.spec authority.declared
    authority.specified authority.admitted (authority.source_typed typed) (.done goal)
    (StructuralDescent.Scheduled.doneTrees environment goal) ((rawRootAnswers request receipt authority.ready).take 1)

theorem startFiring_eventually_settled
    (environment : GeneralPremise.Environment) (depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing) (ready : RootReady firing.request)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal = some firing.request.spec)
    (admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (ordinaryTarget firing.request firing.receipt.source)) :
    ∃ fuel, (StructuralDescent.Scheduled.run environment
      (.root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
        firing.ordinal) fuel
      (startFiring environment depth type firing ready declared specified admitted sourceTyped)).agenda = [] := by
  let goal : StructuralDescent.Scheduled.Goal :=
    .root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source) firing.ordinal
  exact StructuralDescent.Scheduled.continueRootAnswers_eventually_settled
    environment goal depth [] type (ordinaryTarget firing.request firing.receipt.source)
    firing.ordinal firing.request.rule firing.request.spec declared specified admitted sourceTyped
    (.done goal) (StructuralDescent.Scheduled.doneTrees environment goal) (selectedRootAnswers firing ready)

/-- A published collection firing starts the ordinary generic scheduled
executor with all admission authority derived from its certificate. -/
def startPublished
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (fuel depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing)
    (published : firing ∈ CollectionPlanMachine.publication
      (CollectionPlanMachine.resume fuel (CollectionPlanMachine.start
        (CollectionExecutionAdmission.requestsForSource plan certificate source))))
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type
      (ordinaryTarget firing.request firing.receipt.source)) :
    StructuralDescent.Scheduled.State (GeneralPlanEnvironment.environment plan)
      (.root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
        firing.ordinal) :=
  let authority := source_publication_authority plan certificate source fuel published
  startFiring (GeneralPlanEnvironment.environment plan) depth type firing authority.ready
    authority.declared authority.specified authority.admitted sourceTyped

/-- A chronological firing enters the same scheduled continuation, deriving
its declaration, binding and source-typing evidence from the source contract. -/
def startLoggedPublished
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (fuel depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing)
    (published : firing ∈ (CollectionLoggedSearch.run plan certificate source fuel).state.log)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source) :
    StructuralDescent.Scheduled.State (GeneralPlanEnvironment.environment plan)
      (.root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
        firing.ordinal) :=
  let authority := logged_publication_authority plan certificate source fuel published
  startFiring (GeneralPlanEnvironment.environment plan) depth type firing authority.ready
    authority.declared authority.specified authority.admitted (authority.source_typed sourceTyped)

theorem startLoggedPublished_eventually_settled
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (fuel depth : Nat) (type : TypeExpr)
    (firing : CollectionPlanMachine.Firing)
    (published : firing ∈ (CollectionLoggedSearch.run plan certificate source fuel).state.log)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source) :
    ∃ work, (StructuralDescent.Scheduled.run (GeneralPlanEnvironment.environment plan)
      (.root (depth + 1) [] type (ordinaryTarget firing.request firing.receipt.source)
        firing.ordinal) work
      (startLoggedPublished plan certificate source fuel depth type firing published sourceTyped)).agenda = [] := by
  let authority := logged_publication_authority plan certificate source fuel published
  exact startFiring_eventually_settled (GeneralPlanEnvironment.environment plan) depth type firing
    authority.ready authority.declared authority.specified authority.admitted
    (authority.source_typed sourceTyped)

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

namespace Retained

/-- A source allocation, before typing, premises or RHS instantiation. -/
structure Match where
  ordinal : Nat
  request : ScopedCollectionMachine.Request
  receipt : ScopedCollectionMachine.Receipt

/-- The published outcome retains its source allocation separately from the
ordinary proof selected to validate that allocation. -/
structure Publication where
  matched : Match
  outcome : Complete.DeepRoot.Firing

def Publication.Valid (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (type : TypeExpr) (publication : Publication) : Prop :=
  MatchAuthority plan certificate source publication.matched.ordinal
      publication.matched.request publication.matched.receipt ∧
    publication.outcome.captured = publication.matched.receipt.matching.assignment ∧
    GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] type
      (ordinaryTarget publication.matched.request publication.matched.receipt)
      publication.matched.ordinal publication.outcome.trace publication.outcome.captured
      publication.outcome.completed publication.outcome.history publication.outcome.target

structure Frame (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (type : TypeExpr) where
  matched : Match
  authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt
  depth : Nat
  state : StructuralDescent.Scheduled.State (GeneralPlanEnvironment.environment plan)
    (.root (depth + 1) [] type (ordinaryTarget matched.request matched.receipt) matched.ordinal)

variable {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {type : TypeExpr}

def Frame.initial
    (matched : Match)
    (authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (depth : Nat) : Frame plan certificate source type :=
  ⟨matched, authority, depth, startMatch plan certificate source depth type
    matched.ordinal matched.request matched.receipt authority typed⟩

def Frame.run (work : Nat) (frame : Frame plan certificate source type) :
    Frame plan certificate source type :=
  {frame with
    state := StructuralDescent.Scheduled.run (GeneralPlanEnvironment.environment plan)
      (.root (frame.depth + 1) [] type
        (ordinaryTarget frame.matched.request frame.matched.receipt) frame.matched.ordinal)
      work frame.state}

def Frame.read (frame : Frame plan certificate source type)
    (result : StructuralDescent.Scheduled.Result (GeneralPlanEnvironment.environment plan)
      (.root (frame.depth + 1) [] type
        (ordinaryTarget frame.matched.request frame.matched.receipt) frame.matched.ordinal)) :
    Option Publication :=
  let outcome := Complete.DeepRoot.read
    (request := ⟨GeneralPlanEnvironment.environment plan, [], type,
      ordinaryTarget frame.matched.request frame.matched.receipt, frame.matched.ordinal⟩) result
  if outcome.captured == frame.matched.receipt.matching.assignment then
    some ⟨frame.matched, outcome⟩
  else none

def Frame.publication (frame : Frame plan certificate source type) : List Publication :=
  frame.state.answers.filterMap frame.read

theorem Frame.read_sound (frame : Frame plan certificate source type)
    (result : StructuralDescent.Scheduled.Result (GeneralPlanEnvironment.environment plan)
      (.root (frame.depth + 1) [] type
        (ordinaryTarget frame.matched.request frame.matched.receipt) frame.matched.ordinal))
    {publication : Publication} (read : frame.read result = some publication) :
    publication.Valid plan certificate source type := by
  have held := Complete.DeepRoot.read_valid
    (request := ⟨GeneralPlanEnvironment.environment plan, [], type,
      ordinaryTarget frame.matched.request frame.matched.receipt, frame.matched.ordinal⟩) result
  dsimp only [Frame.read] at read
  split at read
  · rename_i same
    cases read
    exact ⟨frame.authority, beq_iff_eq.mp same, held⟩
  · cases read

theorem Frame.publication_sound (frame : Frame plan certificate source type)
    {publication : Publication} (member : publication ∈ frame.publication) :
    publication.Valid plan certificate source type := by
  obtain ⟨result, _, read⟩ := List.mem_filterMap.mp member
  exact frame.read_sound result read

theorem Frame.run_add (first extra : Nat) (frame : Frame plan certificate source type) :
    Frame.run (first + extra) frame = Frame.run extra (Frame.run first frame) := by
  cases frame
  simp only [Frame.run, StructuralDescent.Scheduled.run_add]

/-- Each retained origin has its own append-only publication. Interleaving
other allocations cannot move its cursor behind or ahead of these results. -/
theorem Frame.publication_prefix (frame : Frame plan certificate source type) (work : Nat) :
    frame.publication <+: (Frame.run work frame).publication := by
  obtain ⟨suffix, grown⟩ := StructuralDescent.Scheduled.receipts_prefix
    (GeneralPlanEnvironment.environment plan) _ work frame.state
  refine ⟨suffix.filterMap frame.read, ?_⟩
  change frame.state.answers.filterMap frame.read ++ suffix.filterMap frame.read =
    (StructuralDescent.Scheduled.run (GeneralPlanEnvironment.environment plan) _
      work frame.state).answers.filterMap frame.read
  rw [grown, List.filterMap_append]

theorem Frame.run_idle (frame : Frame plan certificate source type)
    (idle : frame.state.agenda = []) (work : Nat) : Frame.run work frame = frame := by
  have stopped := GeneralPremise.Scheduler.run_idle
    (StructuralDescent.Scheduled.expand (GeneralPlanEnvironment.environment plan) _) work frame.state idle
  cases frame
  simpa only [Frame.run, StructuralDescent.Scheduled.run] using
    congrArg (fun state => Frame.mk _ _ _ state) stopped

theorem Frame.source_coverage
    (matched : Match)
    (authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (depth : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (held : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] type
      (ordinaryTarget matched.request matched.receipt) matched.ordinal trace
      matched.receipt.matching.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ depth) :
    ∃ work chosenTrace,
      (⟨matched, ⟨chosenTrace, matched.receipt.matching.assignment, completed, history, target⟩⟩ :
        Publication) ∈ (Frame.run work (Frame.initial matched authority typed depth)).publication := by
  obtain ⟨work, chosenTrace, proved, present⟩ := startRequest_covers
    (GeneralPlanEnvironment.environment plan) depth type matched.ordinal matched.request
    matched.receipt authority.ready authority.unordered authority.valid authority.declared
    authority.specified authority.admitted (authority.source_typed typed)
    trace completed history target held bounded
  refine ⟨work, chosenTrace, List.mem_filterMap.mpr ⟨_, present, ?_⟩⟩
  simp [Frame.read, Frame.initial, Frame.run, Complete.DeepRoot.read]

/-- Once this actual retained frontier has drained, every depth-qualified
source outcome is in its publication, independently of the chosen work budget. -/
theorem Frame.drained_source_coverage
    (matched : Match)
    (authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (depth work : Nat)
    (drained : (Frame.run work (Frame.initial matched authority typed depth)).state.agenda = [])
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (held : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] type
      (ordinaryTarget matched.request matched.receipt) matched.ordinal trace
      matched.receipt.matching.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ depth) :
    ∃ chosenTrace,
      (⟨matched, ⟨chosenTrace, matched.receipt.matching.assignment, completed, history, target⟩⟩ :
        Publication) ∈ (Frame.run work (Frame.initial matched authority typed depth)).publication := by
  obtain ⟨fuel, chosenTrace, present⟩ := Frame.source_coverage matched authority typed depth
    trace completed history target held bounded
  have later := (Frame.publication_prefix
    (Frame.run fuel (Frame.initial matched authority typed depth)) work).subset present
  rw [← Frame.run_add, Nat.add_comm fuel work, Frame.run_add,
    Frame.run_idle _ drained fuel] at later
  exact ⟨chosenTrace, later⟩

/-- Structural source admission earns the depth bound. It is not supplied
as a completeness field or inferred from a successful finite runtime test. -/
theorem Frame.structural_source_coverage
    (matched : Match)
    (authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (structural : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (held : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] type
      (ordinaryTarget matched.request matched.receipt) matched.ordinal trace
      matched.receipt.matching.assignment completed history target) :
    ∃ work chosenTrace,
      (⟨matched, ⟨chosenTrace, matched.receipt.matching.assignment, completed, history, target⟩⟩ :
        Publication) ∈ (Frame.run work (Frame.initial matched authority typed
          (PatternTreeSize.nodes (ordinaryTarget matched.request matched.receipt)))).publication := by
  have earned := StructuralDescent.firing_depth_bound
    (GeneralPlanEnvironment.environment plan) structural
    (ordinaryTarget matched.request matched.receipt) [] type
    ⟨matched.ordinal, trace, matched.receipt.matching.assignment, completed, history, target, held⟩
  have bounded : StructuralDescent.eventsDepth history ≤
      PatternTreeSize.nodes (ordinaryTarget matched.request matched.receipt) := by
    change 1 + StructuralDescent.eventsDepth history ≤ _ at earned
    omega
  exact Frame.source_coverage matched authority typed _ trace completed history target held bounded

/-- Drain this origin's new suffix before publications from other origins
are concatenated. A cursor over their flattened publications is unsound. -/
def Frame.fresh (frame : Frame plan certificate source type) : List Publication :=
  (Frame.run 1 frame).publication.drop frame.publication.length

theorem Frame.fresh_balance (frame : Frame plan certificate source type) :
    frame.publication ++ frame.fresh = (Frame.run 1 frame).publication := by
  have grown := Frame.publication_prefix frame 1
  change frame.publication ++ (Frame.run 1 frame).publication.drop frame.publication.length = _
  calc
    _ = (Frame.run 1 frame).publication.take frame.publication.length ++
        (Frame.run 1 frame).publication.drop frame.publication.length := by
      exact congrArg
        (fun items => items ++ (Frame.run 1 frame).publication.drop frame.publication.length)
        (List.prefix_iff_eq_take.mp grown)
    _ = _ := List.take_append_drop _ _

structure State (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (type : TypeExpr) where
  frames : List (Frame plan certificate source type)
  log : List Publication

def State.begin (frames : List (Frame plan certificate source type)) :
    State plan certificate source type :=
  ⟨frames, frames.flatMap Frame.publication⟩

def State.round (state : State plan certificate source type) :
    State plan certificate source type :=
  ⟨state.frames.map (Frame.run 1), state.log ++ state.frames.flatMap Frame.fresh⟩

def State.run : Nat → State plan certificate source type → State plan certificate source type
  | 0, state => state
  | work + 1, state => State.run work state.round

def State.Balanced (state : State plan certificate source type) : Prop :=
  state.log.Perm (state.frames.flatMap Frame.publication)

theorem State.begin_balanced (frames : List (Frame plan certificate source type)) :
    (State.begin frames).Balanced := List.Perm.refl _

private theorem frames_balance (frames : List (Frame plan certificate source type)) :
    ((frames.flatMap Frame.publication) ++ frames.flatMap Frame.fresh).Perm
      ((frames.map (Frame.run 1)).flatMap Frame.publication) := by
  induction frames with
  | nil => exact List.Perm.refl []
  | cons frame frames ih =>
    simp only [List.flatMap_cons, List.map_cons]
    have shuffled :
        (frame.publication ++ frames.flatMap Frame.publication ++
          (frame.fresh ++ frames.flatMap Frame.fresh)).Perm
        ((frame.publication ++ frame.fresh) ++
          (frames.flatMap Frame.publication ++ frames.flatMap Frame.fresh)) := by
      simpa only [List.append_assoc] using
        List.Perm.append_left frame.publication
          ((List.perm_append_comm
            (l₁ := frames.flatMap Frame.publication) (l₂ := frame.fresh)).append_right _)
    apply shuffled.trans
    rw [Frame.fresh_balance]
    exact (List.Perm.refl _).append ih

theorem State.round_balanced {state : State plan certificate source type}
    (balanced : state.Balanced) : state.round.Balanced :=
  (balanced.append_right _).trans (frames_balance state.frames)

/-- The chronological log accounts for every complete receipt once, up to
the interleaving of different origins. Permutation retains multiplicities. -/
theorem State.run_balanced (work : Nat) {state : State plan certificate source type}
    (balanced : state.Balanced) : (State.run work state).Balanced := by
  induction work generalizing state with
  | zero => exact balanced
  | succ work ih => exact ih (State.round_balanced balanced)

theorem State.run_add (first extra : Nat) (state : State plan certificate source type) :
    State.run (first + extra) state = State.run extra (State.run first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, State.run]
  | succ first ih => simpa only [Nat.succ_add, State.run] using ih state.round

theorem State.run_frames (work : Nat) (state : State plan certificate source type) :
    (State.run work state).frames = state.frames.map (Frame.run work) := by
  induction work generalizing state with
  | zero =>
    have idle (frame : Frame plan certificate source type) : Frame.run 0 frame = frame := by
      cases frame
      rfl
    have zero : (Frame.run 0 : Frame plan certificate source type → _) = id := funext idle
    change state.frames = state.frames.map (Frame.run 0)
    rw [zero, List.map_id]
  | succ work ih =>
    simp only [State.run, ih, State.round, List.map_map, Function.comp_def]
    rfl

theorem State.log_prefix (work : Nat) (state : State plan certificate source type) :
    state.log <+: (State.run work state).log := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih =>
    exact (List.prefix_append _ _).trans (ih state.round)

theorem State.publication_sound (work : Nat)
    (frames : List (Frame plan certificate source type))
    {publication : Publication}
    (member : publication ∈ (State.run work (State.begin frames)).log) :
    publication.Valid plan certificate source type := by
  have balanced := State.run_balanced work (State.begin_balanced frames)
  obtain ⟨frame, _, inside⟩ := List.mem_flatMap.mp (balanced.subset member)
  exact frame.publication_sound inside

/-- Every depth-qualified source outcome of every initial raw origin reaches
the one chronological log. Other retained origins cannot starve or erase it. -/
theorem State.source_coverage
    (frames : List (Frame plan certificate source type))
    (matched : Match)
    (authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (depth : Nat) (initial : Frame.initial matched authority typed depth ∈ frames)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (held : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] type
      (ordinaryTarget matched.request matched.receipt) matched.ordinal trace
      matched.receipt.matching.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ depth) :
    ∃ work chosenTrace,
      (⟨matched, ⟨chosenTrace, matched.receipt.matching.assignment, completed, history, target⟩⟩ :
        Publication) ∈ (State.run work (State.begin frames)).log := by
  obtain ⟨work, chosenTrace, emitted⟩ := Frame.source_coverage matched authority typed depth
    trace completed history target held bounded
  have retained : Frame.run work (Frame.initial matched authority typed depth) ∈
      (State.run work (State.begin frames)).frames := by
    rw [State.run_frames]
    exact List.mem_map_of_mem initial
  have completeLog := State.run_balanced work (State.begin_balanced frames)
  exact ⟨work, chosenTrace,
    completeLog.symm.subset (List.mem_flatMap.mpr ⟨_, retained, emitted⟩)⟩

abbrev CheckedMatch (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan) (source : Pattern) :=
  {matched : Match // MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt}

def State.initial
    (matchedOrigins : List (CheckedMatch plan certificate source))
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (depth : Match → Nat) : State plan certificate source type :=
  State.begin (matchedOrigins.map fun matched => Frame.initial matched.val matched.property typed (depth matched.val))

def State.complete (state : State plan certificate source type) : Bool :=
  state.frames.all fun frame => frame.state.agenda.isEmpty

theorem State.eventually_settled
    (matchedOrigins : List (CheckedMatch plan certificate source))
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (depth : Match → Nat) :
    ∃ work, (State.run work (State.initial matchedOrigins typed depth)).complete = true := by
  have finite : ∀ frames : List (Frame plan certificate source type),
      (∀ frame ∈ frames, ∃ work, (Frame.run work frame).state.agenda = []) →
      ∃ work, ∀ frame ∈ frames, (Frame.run work frame).state.agenda = [] := by
    intro frames
    induction frames with
    | nil => exact fun _ => ⟨0, by intro frame member; cases member⟩
    | cons frame frames ih =>
      intro each
      obtain ⟨first, headDone⟩ := each frame List.mem_cons_self
      obtain ⟨later, tailDone⟩ := ih (fun child member => each child (List.mem_cons_of_mem _ member))
      refine ⟨first + later, ?_⟩
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · rw [Frame.run_add, Frame.run_idle _ headDone later]
        exact headDone
      · rw [Nat.add_comm first later, Frame.run_add, Frame.run_idle _ (tailDone child member) first]
        exact tailDone child member
  let frames := (State.initial matchedOrigins typed depth).frames
  obtain ⟨work, settled⟩ := finite frames (by
    intro frame member
    obtain ⟨matched, _, rfl⟩ := List.mem_map.mp member
    exact startMatch_eventually_settled plan certificate source _ type
      matched.val.ordinal matched.val.request matched.val.receipt matched.property typed)
  refine ⟨work, List.all_eq_true.mpr ?_⟩
  intro frame member
  rw [State.run_frames] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact List.isEmpty_iff.mpr (settled original present)

end Retained

end Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
