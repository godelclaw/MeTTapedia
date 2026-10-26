import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionNames
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentationProofs
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledExecution
import Mettapedia.OSLF.MeTTaIL.CanonicalTyping

/-!
# Recursive matches enter the shared typed premise continuation

Preparation retains the allocation history and constructs one ordinary source
witness. It is a producer handoff, not a checker for arbitrary external
receipts: its validity follows from the retained matcher's published-receipt
theorem. Typing and premise evaluation belong to the existing continuation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff

open Syntax RuleBinding ScopedRuleMatching CanonicalBags
open GeneralPremise StructuralDescent.Scheduled
open Mettapedia.GSLT.LanguageDef.WellSorted
open RecursiveCollectionPresentation

/-- The same premise judgments can use recursive allocation semantics.
Inputs are compared in the declared bag/set theory. The repeated-capture
comparison remains a separate explicit policy. This definition alone does
not select a native execution profile or discharge its coverage obligation. -/
def matchingInterpretation (compare : EquationalScopedMatching.Comparison) :
    MatchingInterpretation EquationalScopedReceipts.Event where
  Input := fun request => ∃ value,
    instantiateAt? request.rule request.spec request.ambient request.site request.path
      request.depth request.initial request.schema = some value ∧ Same value request.target
  Matches := fun request trace final => EquationalScopedReceipts.Matches compare
    request.rule request.spec request.ambient request.site request.path request.depth
    request.initial request.schema request.target trace final
  extension := fun matched => matched.extends

/-- The authored occurrence and incoming captures stay fixed. Collection
normalization applies to the object passed to the matcher. -/
def canonicalRequest (request : RecursiveCollectionMachine.Request) :
    RecursiveCollectionMachine.Request :=
  { request with target := canon request.target }

/-- Collection-aware inputs and canonical matcher targets share one premise
interpretation. Incoming assignments are retained, not silently rewritten. -/
def canonicalMatchingInterpretation : MatchingInterpretation EquationalScopedReceipts.Event where
  Input := (matchingInterpretation literalBodyComparison).Input
  Matches := fun request =>
    (matchingInterpretation literalBodyComparison).Matches (canonicalRequest request)
  extension := fun matched => matched.extends

/-- The existing allocation machine supplies the retained matching service
used by all query, root and child-target frames. Its source interpretation
and publication validity are established independently of those frames. -/
def canonicalMatchingExecution : MatchingExecution where
  Choice := EquationalScopedReceipts.Event
  meaning := canonicalMatchingInterpretation
  State := RecursiveCollectionMachine.Request × RecursiveCollectionMachine.State
  Answer := RecursiveCollectionMachine.Answer
  assignment := RecursiveCollectionMachine.Answer.assignment
  trace := RecursiveCollectionMachine.Answer.trace
  start := fun request =>
    let canonical := canonicalRequest request
    (canonical, RecursiveCollectionMachine.start canonical)
  tick := fun _ state => (state.1, RecursiveCollectionMachine.tick state.1 state.2)
  answers := fun state => state.2.answers
  complete := fun state => RecursiveCollectionMachine.complete state.2
  Reachable := fun request state => ∃ fuel,
    state = (canonicalRequest request,
      RecursiveCollectionMachine.run (canonicalRequest request) fuel
        (RecursiveCollectionMachine.start (canonicalRequest request)))
  start_reachable := fun _ => ⟨0, rfl⟩
  tick_reachable := by
    intro request state reached
    obtain ⟨fuel, rfl⟩ := reached
    exact ⟨fuel + 1, by rw [RecursiveCollectionMachine.run_add]; rfl⟩
  answers_sound := by
    intro request state reached answer member
    obtain ⟨fuel, rfl⟩ := reached
    exact RecursiveCollectionMachine.published_trace_valid (canonicalRequest request) fuel member
  acceptsInput := fun request actual => canon actual == canon request.target
  input_sound := fun read same => ⟨_, read, beq_iff_eq.mp same⟩
  input_complete := fun ⟨actual, read, same⟩ => ⟨actual, read, beq_iff_eq.mpr same⟩

theorem canonical_preservesFreeNames : canonicalMatchingExecution.PreservesFreeNames := by
  intro request trace final matched footprint before target
  obtain ⟨presented, same, ordinary⟩ :=
    EquationalScopedMatching.meaning_has_ordinary_presentation matched.meaning
  apply GeneralScopedMatch.matched_free_within ordinary footprint before
  intro name occurs
  have canonicalOccurs := (canon_freeFvarNames presented name).mpr occurs
  change Same (canon request.target) presented at same
  simp only [Same, canon_idempotent] at same
  rw [← same] at canonicalOccurs
  exact target name ((canon_freeFvarNames request.target name).mp canonicalOccurs)

#print axioms canonical_preservesFreeNames

private def canonicalReference (request : RecursiveCollectionMachine.Request) : List RecursiveCollectionMachine.Answer :=
  let q := canonicalRequest request
  RecursiveCollectionMachine.referenceAt q.rule q.spec q.ambient q.site q.path q.depth q.initial q.schema q.target

private def canonicalUnread (request : RecursiveCollectionMachine.Request)
    (state : RecursiveCollectionMachine.Request × RecursiveCollectionMachine.State) (cursor : Nat) (answer : RecursiveCollectionMachine.Answer) : Prop :=
  answer ∈ state.2.answers.drop cursor ∨
    answer ∈ (canonicalReference request).drop state.2.answers.length

private theorem canonical_reference_prefix {request : RecursiveCollectionMachine.Request}
    {state : RecursiveCollectionMachine.Request × RecursiveCollectionMachine.State} (reached : canonicalMatchingExecution.Reachable request state) :
    canonicalMatchingExecution.answers state <+: canonicalReference request := by
  obtain ⟨fuel, rfl⟩ := reached
  exact RecursiveCollectionMachine.published_trace_prefix (canonicalRequest request) fuel

private theorem canonical_unread_at_cursor {request : RecursiveCollectionMachine.Request}
    {state : RecursiveCollectionMachine.Request × RecursiveCollectionMachine.State} {cursor : Nat} {answer : RecursiveCollectionMachine.Answer}
    (reached : canonicalMatchingExecution.Reachable request state)
    (bounded : cursor ≤ (canonicalMatchingExecution.answers state).length) :
    canonicalUnread request state cursor answer ↔ answer ∈ (canonicalReference request).drop cursor := by
  have prefixFact := canonical_reference_prefix reached
  change state.2.answers <+: canonicalReference request at prefixFact
  change cursor ≤ state.2.answers.length at bounded
  obtain ⟨suffix, same⟩ := prefixFact
  unfold canonicalUnread
  rw [← same, List.drop_append_of_le_length bounded,
    List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append,
    List.mem_append]

/-- Recursive collection allocation retains the same complete cursor contract. -/
def canonicalCursorLaws : MatchingExecution.CursorLaws canonicalMatchingExecution where
  Unread := canonicalUnread
  start := by
    intro request answer
    change RecursiveCollectionMachine.Answer at answer
    change (answer ∈ ([] : List RecursiveCollectionMachine.Answer) ∨ answer ∈ canonicalReference request) ↔
      EquationalScopedReceipts.Matches ScopedRuleMatching.literalBodyComparison
        (canonicalRequest request).rule (canonicalRequest request).spec (canonicalRequest request).ambient
        (canonicalRequest request).site (canonicalRequest request).path (canonicalRequest request).depth
        (canonicalRequest request).initial (canonicalRequest request).schema (canonicalRequest request).target
        answer.trace answer.assignment
    simp only [List.not_mem_nil, false_or]
    exact RecursiveCollectionMachine.referenceAt_exact
  split := by
    intro request state cursor answer
    change RecursiveCollectionMachine.Request × RecursiveCollectionMachine.State at state
    change RecursiveCollectionMachine.Answer at answer
    change (answer ∈ state.2.answers.drop cursor ∨ answer ∈ (canonicalReference request).drop state.2.answers.length) ↔
      state.2.answers[cursor]? = some answer ∨
      (answer ∈ state.2.answers.drop (cursor + 1) ∨ answer ∈ (canonicalReference request).drop state.2.answers.length)
    rw [GeneralScopedMatchMachine.mem_drop_cursor_iff]
    exact or_assoc
  tick := by
    intro request state cursor answer reached bounded _missing
    change RecursiveCollectionMachine.Request × RecursiveCollectionMachine.State at state
    change RecursiveCollectionMachine.Answer at answer
    have grows := RecursiveCollectionMachine.tick_answers_prefix state.1 state.2
    have nextBounded : cursor ≤ (canonicalMatchingExecution.answers
        (canonicalMatchingExecution.tick request state)).length := bounded.trans grows.length_le
    rw [canonical_unread_at_cursor (canonicalMatchingExecution.tick_reachable reached) nextBounded,
      canonical_unread_at_cursor reached bounded]
  complete := by
    intro request state cursor answer reached finished
    change RecursiveCollectionMachine.Request × RecursiveCollectionMachine.State at state
    change RecursiveCollectionMachine.Answer at answer
    obtain ⟨fuel, rfl⟩ := reached
    have same := RecursiveCollectionMachine.completed_traces (canonicalRequest request) fuel finished
    change (answer ∈ (RecursiveCollectionMachine.run (canonicalRequest request) fuel
        (RecursiveCollectionMachine.start (canonicalRequest request))).answers.drop cursor ∨
      answer ∈ (canonicalReference request).drop (RecursiveCollectionMachine.run (canonicalRequest request) fuel
        (RecursiveCollectionMachine.start (canonicalRequest request))).answers.length) ↔
      answer ∈ (RecursiveCollectionMachine.run (canonicalRequest request) fuel
        (RecursiveCollectionMachine.start (canonicalRequest request))).answers.drop cursor
    have remaining : (canonicalReference request).drop
        (RecursiveCollectionMachine.run (canonicalRequest request) fuel
          (RecursiveCollectionMachine.start (canonicalRequest request))).answers.length = [] := by
      rw [same]
      exact List.drop_length
    rw [remaining]
    simp only [List.not_mem_nil, or_false]
  answers_prefix := fun _ state => RecursiveCollectionMachine.tick_answers_prefix state.1 state.2


/-- The cached request measures the same agenda advanced by the canonical
service, including at every resumed state. -/
def canonicalCursorCost : MatchingExecution.CursorCost canonicalMatchingExecution where
  debt := fun _ state cursor =>
    (state.2.answers.length - cursor) +
      2 * RecursiveCollectionMachine.agendaCost state.1 state.2.agenda
  consume := by
    intro request state cursor answer _reached published
    change state.2.answers[cursor]? = some answer at published
    have within := (List.getElem?_eq_some_iff.mp published).1
    change state.2.answers.length - (cursor + 1) +
        2 * RecursiveCollectionMachine.agendaCost state.1 state.2.agenda <
      (state.2.answers.length - cursor) +
        2 * RecursiveCollectionMachine.agendaCost state.1 state.2.agenda
    omega
  tick := by
    intro request state cursor _reached missing pending
    change state.2.answers[cursor]? = none at missing
    change RecursiveCollectionMachine.complete state.2 = false at pending
    have consumed := List.getElem?_eq_none_iff.mp missing
    have decreases := RecursiveCollectionMachine.tick_cost (request := state.1) pending
    have published := RecursiveCollectionMachine.tick_answers_length state.1 state.2
    change (RecursiveCollectionMachine.tick state.1 state.2).answers.length - cursor +
        2 * RecursiveCollectionMachine.agendaCost state.1
          (RecursiveCollectionMachine.tick state.1 state.2).agenda <
      (state.2.answers.length - cursor) +
        2 * RecursiveCollectionMachine.agendaCost state.1 state.2.agenda
    omega

/-- Recursive allocation answers retain both the semantic assignment and
the complete collection trace in the actual record representation. -/
theorem canonical_answer_representation (request : GeneralScopedMatchMachine.Request)
    (trace : List EquationalScopedReceipts.Event) (final : Assignment)
    (_matched : canonicalMatchingExecution.meaning.Matches request trace final) :
    ∃ answer : canonicalMatchingExecution.Answer,
      canonicalMatchingExecution.trace answer = trace ∧
      canonicalMatchingExecution.assignment answer = final :=
  ⟨⟨final, trace⟩, rfl, rfl⟩

/-- Equivalent target presentations give exactly the same retained matcher
request, including its authored site and unchanged incoming assignment. -/
theorem canonicalRequest_same (request : RecursiveCollectionMachine.Request)
    (target : Pattern) (same : Same request.target target) :
    canonicalRequest {request with target := target} = canonicalRequest request := by
  change canon request.target = canon target at same
  simp only [canonicalRequest, same]

/-- Normalizing the target fixes the complete matching evidence at equivalent
objects. No allocation or validation event is added by this transport. -/
theorem canonical_matches_same_target {request : RecursiveCollectionMachine.Request}
    {target : Pattern} {trace : List EquationalScopedReceipts.Event} {final : Assignment}
    (same : Same request.target target)
    (matched : canonicalMatchingInterpretation.Matches request trace final) :
    canonicalMatchingInterpretation.Matches {request with target := target} trace final := by
  change (matchingInterpretation literalBodyComparison).Matches
    (canonicalRequest {request with target := target}) trace final
  rw [canonicalRequest_same request target same]
  exact matched

/-- The normalized source interpretation has the same firing payload at every
equivalent source. Captures, premise histories and the reduct stay fixed, so
this handles every premise form without separate syntactic fragments.
Agreement with another source GSLT remains a separate theorem. -/
theorem canonical_firing_same_source {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source presented target : Pattern} {index : Nat}
    {trace : List EquationalScopedReceipts.Event} {captured completed : Assignment}
    {history : List (Event EquationalScopedReceipts.Event)}
    (same : Same source presented)
    (fired : GeneralPremise.Interpreted.RootFiring canonicalMatchingInterpretation
      environment bound type source index trace captured completed history target) :
    GeneralPremise.Interpreted.RootFiring canonicalMatchingInterpretation
      environment bound type presented index trace captured completed history target := by
  cases fired with
  | fire declared specified admitted sorted matched capturedTyped premises reduced targetTyped =>
      exact .fire declared specified admitted
        (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp same) sorted)
        (canonical_matches_same_target same matched) capturedTyped premises reduced targetTyped

theorem canonical_firing_iff {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source presented target : Pattern} {index : Nat}
    {trace : List EquationalScopedReceipts.Event} {captured completed : Assignment}
    {history : List (Event EquationalScopedReceipts.Event)} (same : Same source presented) :
    GeneralPremise.Interpreted.RootFiring canonicalMatchingInterpretation
      environment bound type source index trace captured completed history target ↔
    GeneralPremise.Interpreted.RootFiring canonicalMatchingInterpretation
      environment bound type presented index trace captured completed history target :=
  ⟨canonical_firing_same_source same, canonical_firing_same_source same.symm⟩

/-- A published retained matcher answer realizes the allocation interpretation
at the actual authored occurrence, not a rule-specific substitute. -/
theorem published_interpretation (request : RecursiveCollectionMachine.Request) (fuel : Nat)
    {answer : RecursiveCollectionMachine.Answer}
    (published : answer ∈ (RecursiveCollectionMachine.run request fuel
      (RecursiveCollectionMachine.start request)).answers) :
    (matchingInterpretation literalBodyComparison).Matches request answer.trace answer.assignment :=
  RecursiveCollectionMachine.published_trace_valid request fuel published

/-- Normalize captures and the matched object while preserving the authored
scope and occurrence. The resulting history witnesses existence of a match;
comparison of allocation origins remains a separate obligation. -/
theorem canonical_match_exists {request : RecursiveCollectionMachine.Request}
    {trace : List EquationalScopedReceipts.Event} {final : Assignment}
    (increasing : IncreasingSpines request.rule request.spec)
    (matched : (matchingInterpretation literalBodyComparison).Matches request trace final) :
    ∃ canonicalTrace, (matchingInterpretation literalBodyComparison).Matches
      {request with initial := canonAssignment request.initial, target := canon request.target}
      canonicalTrace (canonAssignment final) := by
  obtain ⟨presented, _, same, ordinary⟩ := presentAt_complete matched []
  have meaning := EquationalScopedMatching.ordinary_canonical increasing ordinary.matching
  change canon request.target = canon presented at same
  rw [← same] at meaning
  exact EquationalScopedReceipts.Meaning.traced meaning

structure Prepared where
  source : Pattern
  ordinary : GeneralScopedMatchMachine.Answer
  history : List EquationalScopedReceipts.Event
  deriving Repr

def prepare (request : RecursiveCollectionMachine.Request) (answer : RecursiveCollectionMachine.Answer) :
    Option Prepared := do
  let (source, remaining) ← presentAt request.path request.schema request.target answer.trace
  if remaining.isEmpty then
    some ⟨source, ⟨answer.assignment, frontTraceAt request.path request.schema⟩, answer.trace⟩
  else none

structure Prepared.Valid (request : RecursiveCollectionMachine.Request)
    (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared) : Prop where
  source : Same request.target prepared.source
  matching : prepared.ordinary.Valid { request with target := prepared.source }
  assignment : prepared.ordinary.assignment = answer.assignment
  history : prepared.history = answer.trace
  allocation : EquationalScopedReceipts.Matches literalBodyComparison request.rule request.spec
    request.ambient request.site request.path request.depth request.initial request.schema request.target
    answer.trace answer.assignment

theorem prepare_complete (request : RecursiveCollectionMachine.Request) (answer : RecursiveCollectionMachine.Answer)
    (valid : EquationalScopedReceipts.Matches literalBodyComparison request.rule request.spec request.ambient
      request.site request.path request.depth request.initial request.schema request.target
      answer.trace answer.assignment) :
    ∃ prepared, prepare request answer = some prepared ∧ prepared.Valid request answer := by
  obtain ⟨source, reconstructed, same, ordinary⟩ := presentAt_complete valid []
  simp only [List.append_nil] at reconstructed
  refine ⟨⟨source, ⟨answer.assignment, frontTraceAt request.path request.schema⟩, answer.trace⟩,
    by simp [prepare, reconstructed], same, ordinary, rfl, rfl, valid⟩

theorem prepare_valid (request : RecursiveCollectionMachine.Request) (answer : RecursiveCollectionMachine.Answer)
    (valid : EquationalScopedReceipts.Matches literalBodyComparison request.rule request.spec request.ambient
      request.site request.path request.depth request.initial request.schema request.target
      answer.trace answer.assignment)
    {prepared : Prepared} (made : prepare request answer = some prepared) : prepared.Valid request answer := by
  obtain ⟨expected, computed, justified⟩ := prepare_complete request answer valid
  have same := Option.some.inj (computed.symm.trans made)
  exact same ▸ justified

theorem prepare_published (request : RecursiveCollectionMachine.Request) (fuel : Nat)
    {answer : RecursiveCollectionMachine.Answer}
    (published : answer ∈ (RecursiveCollectionMachine.run request fuel
      (RecursiveCollectionMachine.start request)).answers) :
    ∃ prepared, prepare request answer = some prepared ∧ prepared.Valid request answer :=
  prepare_complete request answer (RecursiveCollectionMachine.published_trace_valid request fuel published)

/-- Source formation transports at the actual ambient binder context, before
any right-hand side or premise result is requested. -/
theorem Prepared.Valid.typed {request : RecursiveCollectionMachine.Request}
    {answer : RecursiveCollectionMachine.Answer} {prepared : Prepared}
    (valid : prepared.Valid request answer) (environment : Environment)
    {bound : List TypeExpr} {type : TypeExpr}
    (sorted : OpenPatternWellSorted environment.language environment.free bound type request.target) :
    OpenPatternWellSorted environment.language environment.free bound type prepared.source :=
  openPatternWellSorted_of_eqvGen ((same_iff _ _).mp valid.source) sorted

/-- The existing root continuation owns capture typing, retained premise work
and reduct construction. This adapter allows any ambient binder context. -/
def continuePrepared (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
    (valid : prepared.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ answer)
    (tail : Continuation environment (.root (depth + 1) bound type prepared.source index) outer)
    (next : List (Task environment outer)) :
    Scheduler.Expansion
      (Task environment outer) (Result environment outer) Obligation :=
  continueRootAnswer environment outer depth bound type prepared.source index rule spec declared specified
    admitted (valid.typed environment sorted) prepared.ordinary valid.matching tail next

/-- Preparation cannot publish a reduct or a premise answer prematurely. -/
theorem continuePrepared_no_early_answers (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
    (valid : prepared.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ answer)
    (tail : Continuation environment (.root (depth + 1) bound type prepared.source index) outer)
    (next : List (Task environment outer)) :
    (continuePrepared environment outer depth bound type source index rule spec declared specified admitted
      sorted answer prepared valid tail next).answers = [] := by
  exact continueRootAnswer_answers ..

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax ScopedRuleMatching CanonicalCompare CanonicalCompare.AllNameSupport

theorem MatchingExecution.canonical_preservesNames :
    RecursiveCollectionHandoff.canonicalMatchingExecution.PreservesNames := by
  intro request trace final matched table before target
  obtain ⟨presented, same, ordinary⟩ := EquationalScopedMatching.meaning_has_ordinary_presentation matched.meaning
  exact matched_covered before (same_covered same (canon_covered target)) ordinary

theorem canonical_state_covered {table : List String} {request : GeneralScopedMatchMachine.Request}
    {state : RecursiveCollectionHandoff.canonicalMatchingExecution.State}
    (reachable : RecursiveCollectionHandoff.canonicalMatchingExecution.Reachable request state)
    (covered : Covered table request.target) : RecursiveCollectionMachine.StateCovered table state.2 := by
  obtain ⟨fuel, rfl⟩ := reachable
  exact RecursiveCollectionMachine.run_covered _ _ _
    (RecursiveCollectionMachine.start_covered _ _ (canon_covered covered))

end Mettapedia.OSLF.MeTTaIL.GeneralPremise

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport

open CanonicalCompare

theorem matcher_state_covered {table : List String} {environment : Environment} {request : Query.Request}
    {frame : Query.MatcherFrame environment request RecursiveCollectionHandoff.canonicalMatchingExecution}
    (covered : TaskCovered (table := table) (.matcher frame)) :
    RecursiveCollectionMachine.StateCovered table frame.state.2 :=
  canonical_state_covered frame.reachable covered.2.1

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.canonical_preservesNames
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.canonical_state_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.matcher_state_covered
