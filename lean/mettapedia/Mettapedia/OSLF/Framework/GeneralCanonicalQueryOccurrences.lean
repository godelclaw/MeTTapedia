import Mettapedia.OSLF.Framework.GeneralCanonicalCongruenceAgreement
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionOrder
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryTotality
import Mettapedia.OSLF.Syntax.CanonicalRelationQueryEvents
import Mettapedia.GSLT.Distinction.OrderedAdministration

/-!
# Query occurrences in the general and canonical semantics

The canonical engine reads a relation query against the provider's own relation
environment `providerRelEnv`, whose tuples are the provider's rows of that
relation in row order, duplicates included. Its recorded events retain each
tuple's position and each match's position (`CanonicalRelationQueryEvents`).

The general query machine scans the same rows in the same order. This module
shows that, for a first-order query of an admitted rule, the two lists are the
same occurrences, one for one and in order:
- the general answer of provider row `i` and the canonical event of that row;
- the event's tuple position is the number of rows of the relation before `i`;
- the two assignments correspond as in the step agreement.

Equal rows remain distinct occurrences on both sides. Membership agreement of a
relation environment (`ReadsProvider`) does not give this: a duplicated
environment reads the same provider but doubles the canonical events.

Read as an ordered machine, the query machine is a block simulation of the
canonical query step (`query_blockSimulation`). Its retained tasks are
bookkeeping, ranked by the work account of their expansion trees; its answers are stable and
stand for one canonical event each; unresolved obligations stay observable
terminals, which admitted queries never reach. One canonical query step is
therefore one saturated step of the machine (`admitted_query_saturated`), the
first instance of the ordered-administration theory on an actual interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.ContextualStep
open MeTTaIL.MatchSpec MeTTaIL.ScopedRuleMatching MeTTaIL.RuleBinding MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents (RecordedEvent recordedEvents relationTuples)

/-- One actual canonical query selection, with its premise position and the
original and instantiated arguments. The event retains tuple/match positions. -/
structure RecordedQueryStep where
  premisePosition : Nat
  relation : String
  arguments : List Pattern
  instantiated : List Pattern
  event : RecordedEvent

structure RecordedPremiseRun where
  bindings : Bindings
  queries : List RecordedQueryStep

/-- The raw root occurrence retains the stores and history in their original
layouts. The ordinal identifies its authored rule occurrence. -/
structure RootReadout where
  ordinal : Nat
  matcherTrace : List GeneralScopedMatchMachine.BagChoice
  captured : Assignment
  completed : Assignment
  history : List GeneralPremise.Event
  localTarget : Pattern
  target : Pattern

def rootReadout {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {index : Nat} :
    GeneralPremise.Execution.Result environment (.root bound type source index) → RootReadout
  | .root trace captured completed history target _ =>
      ⟨index, trace, captured, completed, history, target, target⟩

def receiptReadout (receipt : GeneralRuleJobs.Receipt) : RootReadout :=
  ⟨receipt.job.ordinal, receipt.matcherTrace, receipt.captured, receipt.completed,
    receipt.premiseHistory, receipt.localTarget, receipt.target⟩

structure RecordedRootRun where
  initial : Bindings
  completed : RecordedPremiseRun
  target : Pattern

def premiseHistory {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {pending : List Premise} {initial : Assignment} :
    GeneralPremise.Execution.Result environment (.premises context pending initial) → List GeneralPremise.Event
  | .premises _ history _ => history

def premiseEvent {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {premise : Premise} {initial : Assignment} :
    GeneralPremise.Execution.Result environment (.premise context premise initial) → GeneralPremise.Event
  | .premise _ event _ => event

/-- Instrument the canonical premise fold using its independently specified
recorded query events. Equal tuples remain separate selected occurrences. -/
def recordedPremiseRuns (relations : Engine.RelationEnv) (language : LanguageDef) :
    List Premise → Nat → Bindings → List RecordedPremiseRun
  | [], _, initial => [⟨initial, []⟩]
  | .relationQuery relation arguments :: remaining, position, initial =>
      (recordedEvents relations language initial relation arguments).flatMap fun event =>
        (recordedPremiseRuns relations language remaining (position + 1) event.final).map fun later =>
          ⟨later.bindings, ⟨position, relation, arguments, arguments.map (applyBindings initial), event⟩ :: later.queries⟩
  | premise :: remaining, position, initial =>
      (Engine.premiseStepWithEnv relations language initial premise).flatMap fun next =>
        recordedPremiseRuns relations language remaining (position + 1) next

/-- Record the original canonical root match and every selected premise row
before instantiating the authored right-hand side. -/
def recordedRootRuns (relations : Engine.RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (source : Pattern) : List RecordedRootRun :=
  (matchPattern rule.left source).flatMap fun initial =>
    (recordedPremiseRuns relations language rule.premises 0 initial).map fun completed =>
      ⟨initial, completed, applyBindings completed.bindings rule.right⟩

def recordedGuardedRootRuns (relations : Engine.RelationEnv) (language : LanguageDef)
    (provider : GeneralPremise.ProviderSnapshot) (rule : RewriteRule)
    (type : TypeExpr) (source : Pattern) : List RecordedRootRun :=
  if rootSortGuard language provider rule type then recordedRootRuns relations language rule source else []

structure RecordedRuleRun where
  ordinal : Nat
  run : RecordedRootRun

/-- The original authored rule order is retained before any unsuccessful
matches are filtered. Equal rules and equal query tuples stay distinct. -/
def recordedRootOccurrences (relations : Engine.RelationEnv) (language : LanguageDef)
    (source : Pattern) : List RecordedRuleRun :=
  language.rewrites.zipIdx.flatMap fun entry =>
    (recordedRootRuns relations language entry.1 source).map fun run => ⟨entry.2, run⟩

def rootInvocationGuard (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (type : TypeExpr) (ordinal : Nat) : Bool :=
  match (environment language provider).language.rewrites[ordinal]? with
  | none => false
  | some rule => rootSortGuard language provider rule type

/-- Enumerate original authored rules and query events, with checked invocation
selection supplied by the typed declaration at the same original ordinal. -/
def recordedGuardedRootOccurrences (relations : Engine.RelationEnv) (language : LanguageDef)
    (provider : GeneralPremise.ProviderSnapshot) (type : TypeExpr) (source : Pattern) : List RecordedRuleRun :=
  language.rewrites.zipIdx.flatMap fun entry =>
    (if rootInvocationGuard language provider type entry.2 then
      recordedRootRuns relations language entry.1 source else []).map fun run => ⟨entry.2, run⟩

theorem recordedRootRuns_eq_of_ruleCore (relations : Engine.RelationEnv) (language : LanguageDef)
    {first second : RewriteRule} (core : ruleCore first = ruleCore second) (source : Pattern) :
    recordedRootRuns relations language first source = recordedRootRuns relations language second source := by
  simp only [ruleCore, Prod.mk.injEq] at core
  simp only [recordedRootRuns, core.1, core.2.1, core.2.2]

private theorem canonical_zero_premise (relations : Engine.RelationEnv) (language : LanguageDef)
    (initial : Bindings) (premise : Premise) :
    premiseStepUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language 0) initial premise =
      Engine.premiseStepWithEnv relations language initial premise := by
  cases premise <;> simp [premiseStepUsing, engineBasePremises, rewriteAt, Engine.premiseStepWithEnv]

/-- Forgetting provenance returns the actual canonical engine's complete
ordered result list, not merely its membership relation. -/
theorem recordedPremiseRuns_bindings (relations : Engine.RelationEnv) (language : LanguageDef)
    (premises : List Premise) (position : Nat) (initial : Bindings) :
    (recordedPremiseRuns relations language premises position initial).map RecordedPremiseRun.bindings =
      Engine.applyPremisesWithEnv relations language premises initial := by
  rw [← premisesUsing_engineBase_zero_eq_applyPremisesWithEnv]
  induction premises generalizing position initial with
  | nil => rfl
  | cons premise premises ih =>
    cases premise with
    | relationQuery relation arguments =>
      simp only [recordedPremiseRuns, premisesUsing, canonical_zero_premise,
        Engine.premiseStepWithEnv, List.map_flatMap, List.map_map]
      change ((recordedEvents relations language initial relation arguments).flatMap fun event =>
        (recordedPremiseRuns relations language premises (position + 1) event.final).map RecordedPremiseRun.bindings) = _
      rw [← Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.recordedEvents_results
        relations language initial relation arguments, List.flatMap_map]
      exact List.flatMap_congr (fun event _ => ih (position + 1) event.final)
    | _ =>
      simp only [recordedPremiseRuns, premisesUsing, canonical_zero_premise, List.map_flatMap]
      apply List.flatMap_congr
      intro next _
      exact ih (position + 1) next

/-! ## The canonical matcher is deterministic on first-order arguments -/

private theorem length_flatMap_le_one {α β : Type} (items : List α) (expand : α → List β)
    (few : items.length ≤ 1) (each : ∀ item ∈ items, (expand item).length ≤ 1) :
    (items.flatMap expand).length ≤ 1 := by
  match items, few with
  | [], _ => simp
  | [item], _ => simpa using each item (List.mem_singleton_self _)

theorem matchArgs_length_le_one {patterns : List Pattern}
    (each : ∀ pattern ∈ patterns, ∀ value, (matchPattern pattern value).length ≤ 1) :
    ∀ values, (matchArgs patterns values).length ≤ 1 := by
  induction patterns with
  | nil => intro values; cases values <;> simp [matchArgs]
  | cons pattern rest ih =>
    intro values
    cases values with
    | nil => simp [matchArgs]
    | cons value values =>
      rw [matchArgs]
      apply length_flatMap_le_one _ _ (each pattern (List.mem_cons_self ..) value)
      intro _ _
      exact (List.length_filterMap_le _ _).trans
        (ih (fun other member => each other (List.mem_cons_of_mem _ member)) values)

theorem matchPattern_length_le_one {pattern : Pattern} (shape : FirstOrder pattern) :
    ∀ value, (matchPattern pattern value).length ≤ 1 := by
  induction shape with
  | metavariable name => intro value; simp [matchPattern]
  | constructor label arguments _ ih =>
    intro value
    cases value
    case apply actualLabel targets =>
      simp only [matchPattern]
      split
      · exact matchArgs_length_le_one (fun argument member => ih argument member) targets
      · simp
    all_goals simp [matchPattern]

theorem matchRelationArgument_length_le_one {seed : Bindings} {argument : Pattern}
    (shape : FirstOrder argument) (value : Pattern) :
    (Engine.matchRelationArgument seed argument value).length ≤ 1 := by
  cases shape with
  | metavariable name =>
    simp only [Engine.matchRelationArgument]
    split
    · split <;> simp
    · simp
  | constructor label arguments children =>
    simpa [Engine.matchRelationArgument] using
      matchPattern_length_le_one (.constructor label arguments children) value

theorem matchRelationArgs_length_le_one :
    ∀ {arguments values : List Pattern} {seed : Bindings},
      (∀ argument ∈ arguments, FirstOrder argument) →
        (Engine.matchRelationArgs seed arguments values).length ≤ 1
  | [], [], _, _ => by simp [Engine.matchRelationArgs]
  | [], _ :: _, _, _ => by simp [Engine.matchRelationArgs]
  | _ :: _, [], _, _ => by simp [Engine.matchRelationArgs]
  | argument :: arguments, value :: values, seed, shapes => by
    rw [Engine.matchRelationArgs]
    apply length_flatMap_le_one _ _
      (matchRelationArgument_length_le_one (shapes argument (List.mem_cons_self ..)) value)
    intro head _
    split
    · simp
    · exact (List.length_filterMap_le _ _).trans
        (matchRelationArgs_length_le_one (fun other member => shapes other (List.mem_cons_of_mem _ member)))

/-! ## Canonical events of the provider's own relation environment -/

/-- The canonical events of one tuple at a given tuple position. -/
def tupleEvents (initial : Bindings) (arguments tuple : List Pattern) (position : Nat) :
    List RecordedEvent :=
  (Engine.matchRelationArgs initial arguments tuple).zipIdx.filterMap fun (extension, matchPosition) =>
    (mergeBindings initial extension).map fun final =>
      { tuplePosition := position, tuple, matchPosition, extension, final }

/-- The canonical events of provider rows, numbering the relation's tuples from
`position`. Rows of other relations contribute no tuple. -/
def rowEvents (initial : Bindings) (relation : String) (arguments : List Pattern) :
    List GeneralPremise.ProviderRow → Nat → List RecordedEvent
  | [], _ => []
  | row :: rows, position =>
    if row.relation = relation then
      tupleEvents initial arguments row.values position ++
        rowEvents initial relation arguments rows (position + 1)
    else rowEvents initial relation arguments rows position

private theorem zipIdx_filterMap_flatMap (initial : Bindings) (relation : String) (arguments : List Pattern) :
    ∀ (rows : List GeneralPremise.ProviderRow) (position : Nat),
      ((rows.filterMap fun row => if row.relation = relation then some row.values else none).zipIdx
          position).flatMap (fun pair => tupleEvents initial arguments pair.1 pair.2) =
        rowEvents initial relation arguments rows position
  | [], _ => rfl
  | row :: rows, position => by
    by_cases same : row.relation = relation
    · simp only [List.filterMap_cons, same, if_true, List.zipIdx_cons, List.flatMap_cons, rowEvents]
      rw [zipIdx_filterMap_flatMap initial relation arguments rows (position + 1)]
    · simp only [List.filterMap_cons, same, if_false, rowEvents]
      exact zipIdx_filterMap_flatMap initial relation arguments rows position

/-- **The canonical events of a provided relation are its rows' events, in row
order.** -/
theorem recordedEvents_provider (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (initial : Bindings) {relation : String} (distinct : relation ≠ "eq") (arguments : List Pattern) :
    recordedEvents (providerRelEnv provider) language initial relation arguments =
      rowEvents initial relation arguments provider.rows 0 := by
  unfold recordedEvents relationTuples
  dsimp only
  rw [builtinRelationTuples_eq_nil distinct, List.nil_append]
  exact zipIdx_filterMap_flatMap initial relation arguments provider.rows 0

theorem tupleEvents_length_le_one {initial : Bindings} {arguments : List Pattern}
    (shapes : ∀ argument ∈ arguments, FirstOrder argument) (tuple : List Pattern) (position : Nat) :
    (tupleEvents initial arguments tuple position).length ≤ 1 := by
  unfold tupleEvents
  exact (List.length_filterMap_le _ _).trans (by
    rw [List.length_zipIdx]
    exact matchRelationArgs_length_le_one shapes)


theorem mem_tupleEvents {initial : Bindings} {arguments tuple : List Pattern} {position : Nat}
    {event : RecordedEvent} (member : event ∈ tupleEvents initial arguments tuple position) :
    ∃ extension matchPosition final,
      (Engine.matchRelationArgs initial arguments tuple)[matchPosition]? = some extension ∧
      mergeBindings initial extension = some final ∧
      event = { tuplePosition := position, tuple, matchPosition, extension, final } := by
  unfold tupleEvents at member
  obtain ⟨⟨extension, matchPosition⟩, pairMember, produced⟩ := List.mem_filterMap.mp member
  obtain ⟨final, merged, rfl⟩ := Option.map_eq_some_iff.mp produced
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp pairMember
  rw [List.getElem?_zipIdx] at found
  obtain ⟨selected, located, same⟩ := Option.map_eq_some_iff.mp found
  simp only [Prod.mk.injEq, Nat.zero_add] at same
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨selected, index, final, located, merged, rfl⟩

theorem tupleEvents_ne_nil {initial : Bindings} {arguments tuple : List Pattern} {position : Nat}
    {extension final : Bindings} (matched : extension ∈ Engine.matchRelationArgs initial arguments tuple)
    (merged : mergeBindings initial extension = some final) :
    tupleEvents initial arguments tuple position ≠ [] := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp matched
  intro empty
  have member : (extension, index) ∈ (Engine.matchRelationArgs initial arguments tuple).zipIdx := by
    apply List.mem_iff_getElem?.mpr
    exact ⟨index, by rw [List.getElem?_zipIdx, found]; simp⟩
  have produced : { tuplePosition := position, tuple, matchPosition := index, extension, final } ∈
      tupleEvents initial arguments tuple position := by
    unfold tupleEvents
    exact List.mem_filterMap.mpr ⟨(extension, index), member, by simp [merged]⟩
  rw [empty] at produced
  cases produced

/-! ## The state before a query -/

private theorem bindings_lookup_of_mem :
    ∀ {bindings : Bindings}, (bindings.map Prod.fst).Nodup →
      ∀ {entry : String × Pattern}, entry ∈ bindings → bindings.lookup entry.1 = some entry.2
  | [], _, _, member => nomatch member
  | head :: rest, unique, entry, member => by
    rw [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with rfl | later
    · simp [Bindings.lookup]
    · have distinct : (head.1 == entry.1) = false := by
        have outside : entry.1 ∈ rest.map Prod.fst := List.mem_map_of_mem later
        simpa using fun same : head.1 = entry.1 => unique.1 (same ▸ outside)
      have read := bindings_lookup_of_mem unique.2 later
      simpa [Bindings.lookup, List.find?_cons, distinct] using read

theorem mergeBindings_nodup :
    ∀ {first second combined : Bindings}, mergeBindings first second = some combined →
      (first.map Prod.fst).Nodup → (combined.map Prod.fst).Nodup
  | first, [], combined, merged, unique => by
    simp only [mergeBindings, List.foldlM_nil] at merged
    cases Option.some.inj merged
    exact unique
  | first, (name, value) :: rest, combined, merged, unique => by
    simp only [mergeBindings, List.foldlM_cons] at merged
    cases found : first.find? (fun entry => entry.1 == name) with
    | none =>
      simp only [found] at merged
      have fresh : name ∉ first.map Prod.fst := by
        intro member
        obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
        have tested := List.find?_eq_none.mp found entry entryMember
        simp [same] at tested
      exact mergeBindings_nodup (first := (name, value) :: first) merged
        (List.nodup_cons.mpr ⟨fresh, unique⟩)
    | some existing =>
      simp only [found] at merged
      split at merged
      · exact mergeBindings_nodup (first := first) merged unique
      · cases merged

/-- The state before a premise: the general assignment agrees with the canonical
bindings, which are typed, unique, and name only available names, all of which
the general assignment binds. This is the invariant of the canonical-to-general
step agreement. -/
structure QueryInvariant (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (bound : List TypeExpr) (available : List String)
    (assignment : Assignment) (bindings : Bindings) : Prop where
  compatible : ScopedCompatible bound.length bindings assignment
  typed : CapturesTyped (environment language provider).language (environment language provider).free bound
    rule.typeContext bindings
  bound : GeneralPremise.BoundNames assignment available
  names : ∀ name ∈ bindings.map Prod.fst, name ∈ available
  unique : (bindings.map Prod.fst).Nodup

variable {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}

theorem QueryInvariant.ordinary_compatible {rule : RewriteRule} {bound : List TypeExpr}
    {available : List String} {assignment : Assignment} {bindings : Bindings}
    (state : QueryInvariant language provider rule bound available assignment bindings) {later : Assignment}
    (grows : ∀ name value, lookup assignment name = some value → lookup later name = some value) :
    Compatible (ordinary later) bindings := by
  intro entry member
  obtain ⟨value, found⟩ := state.bound entry.1 (state.names entry.1 (List.mem_map_of_mem member))
  obtain ⟨_, _, read⟩ := state.compatible _ (lookup_member assignment entry.1 value found)
  rw [bindings_lookup_of_mem state.unique member] at read
  rw [ordinary_lookup, grows entry.1 value found, Option.some.inj read]
  rfl

/-- Each available name has the same value on both sides. -/
theorem QueryInvariant.lookup_eq {rule : RewriteRule} {bound : List TypeExpr} {available : List String}
    {assignment : Assignment} {bindings : Bindings}
    (state : QueryInvariant language provider rule bound available assignment bindings)
    {name : String} (member : name ∈ available) :
    (lookup assignment name).map ContextualValue.body = bindings.lookup name := by
  obtain ⟨value, found⟩ := state.bound name member
  obtain ⟨_, _, read⟩ := state.compatible _ (lookup_member assignment name value found)
  rw [found, read]
  rfl

/-- The available-name account is the exact domain on both sides, not merely
a list containing the successful captures. -/
theorem QueryInvariant.exact_names {rule : RewriteRule} {bound : List TypeExpr} {available : List String}
    {assignment : Assignment} {bindings : Bindings}
    (state : QueryInvariant language provider rule bound available assignment bindings) :
    SameNames bindings available ∧ ∀ name, name ∈ assignment.map Prod.fst ↔ name ∈ available := by
  have ordinaryNames : ∀ name, name ∈ assignment.map Prod.fst ↔ name ∈ bindings.map Prod.fst := by
    intro name
    constructor
    · intro member
      obtain ⟨entry, inList, key⟩ := List.mem_map.mp member
      have found := (state.compatible entry inList).2.2
      exact (lookup_some_iff_mem_names bindings name).mp ⟨entry.2.body, key ▸ found⟩
    · intro member
      obtain ⟨value, found⟩ := state.bound name (state.names name member)
      exact List.mem_map.mpr ⟨(name, value), lookup_member assignment name value found, rfl⟩
  have bindingsNames : SameNames bindings available := by
    intro name
    constructor
    · exact state.names name
    · intro member
      obtain ⟨value, found⟩ := state.bound name member
      exact (ordinaryNames name).mp
        (List.mem_map.mpr ⟨(name, value), lookup_member assignment name value found, rfl⟩)
  exact ⟨bindingsNames, fun name => (ordinaryNames name).trans (bindingsNames name)⟩

/-- Full lookup agreement includes `none` outside the exact bound domain. -/
theorem QueryInvariant.lookup_eq_all {rule : RewriteRule} {bound : List TypeExpr} {available : List String}
    {assignment : Assignment} {bindings : Bindings}
    (state : QueryInvariant language provider rule bound available assignment bindings) (name : String) :
    (lookup assignment name).map ContextualValue.body = bindings.lookup name := by
  by_cases present : name ∈ available
  · exact state.lookup_eq present
  · have domains := state.exact_names
    have scopedAbsent : lookup assignment name = none :=
      (scoped_lookup_none_iff_not_mem_names assignment name).mpr
        (fun member => present ((domains.2 name).mp member))
    have ordinaryAbsent : bindings.lookup name = none :=
      (lookup_none_iff_not_mem_names bindings name).mpr
        (fun member => present ((domains.1 name).mp member))
    rw [scopedAbsent, ordinaryAbsent]
    rfl

/-- Read logical bindings in the caller's declared order while retaining the
actual scoped and canonical stores, including their different list layouts. -/
theorem QueryInvariant.bindingReadout_eq {rule : RewriteRule} {bound : List TypeExpr}
    {available : List String} {assignment : Assignment} {bindings : Bindings}
    (state : QueryInvariant language provider rule bound available assignment bindings) (order : List String) :
    bindingReadout order (ordinary assignment) = bindingReadout order bindings :=
  bindingReadout_eq_of_lookups order (ordinary assignment) bindings
    (fun name => (ordinary_lookup assignment name).trans (state.lookup_eq_all name))

theorem QueryInvariant.bindingAgreement {rule : RewriteRule} {bound : List TypeExpr}
    {available : List String} {assignment : Assignment} {bindings : Bindings}
    (state : QueryInvariant language provider rule bound available assignment bindings)
    (scopedUnique : (assignment.map Prod.fst).Nodup) : BindingAgreement available assignment bindings :=
  ⟨scopedUnique, state.unique, state.exact_names.2, state.exact_names.1, state.lookup_eq_all⟩

theorem supported_premise_unique {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {premise : Premise} {initial final : Assignment} {event : GeneralPremise.Event}
    (supported : SupportedPremise premise)
    (held : GeneralPremise.PremiseHolds environment context premise initial final event)
    (unique : (initial.map Prod.fst).Nodup) : (final.map Prod.fst).Nodup := by
  cases held with
  | query traced =>
    rcases supported with ⟨_, _, impossible, _, _⟩ | ⟨_, impossible, _⟩ | ⟨_, _, same, _, shapes⟩
    · cases impossible
    · cases impossible
    · cases same
      cases traced.readout with
      | row _ _ _ arguments _ => exact query_arguments_unique shapes arguments unique
      | dynamicRow _ _ _ _ _ _ arguments _ => exact query_arguments_unique shapes arguments unique
  | freshness _ _ => exact unique
  | step _ _ _ matched _ =>
    rcases supported with ⟨_, _, same, _, shape⟩ | ⟨_, impossible, _⟩ | ⟨_, _, impossible, _, _⟩
    · cases same
      exact (matching_unique_names shape matched.matching unique).1
    · cases impossible
    · cases impossible
  | scopedStep =>
    rcases supported with ⟨_, _, impossible, _, _⟩ | ⟨_, impossible, _⟩ | ⟨_, _, impossible, _, _⟩ <;> cases impossible
  | quantified =>
    rcases supported with ⟨_, _, impossible, _, _⟩ | ⟨_, impossible, _⟩ | ⟨_, _, impossible, _, _⟩ <;> cases impossible

theorem supported_premises_unique {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {premises : List Premise} {initial final : Assignment} {history : List GeneralPremise.Event}
    (supported : ∀ premise ∈ premises, SupportedPremise premise)
    (held : GeneralPremise.PremisesHold environment context premises initial final history)
    (unique : (initial.map Prod.fst).Nodup) : (final.map Prod.fst).Nodup := by
  cases held with
  | nil => exact unique
  | cons first rest =>
    exact supported_premises_unique (fun premise member => supported premise (List.mem_cons_of_mem _ member)) rest
      (supported_premise_unique (supported _ (List.mem_cons_self ..)) first unique)
termination_by premises.length

theorem tracedArguments_rootValues {context : GeneralPremise.Context}
    (zero : GeneralPremise.checkZeroDependencies context.spec = true) {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins) :
    GeneralPremise.RootValues context.bound.length initial →
      GeneralPremise.RootValues context.bound.length final := by
  induction held with
  | nil => exact id
  | input _ _ ih => exact ih
  | output matched _ ih =>
    exact fun before => ih (GeneralPremise.matching_rootValues zero before matched.matching)

/-! ## One provider row, both ways -/

/-- The available names after a query. -/
abbrev queryAvailable (arguments : List Pattern) (signature : GeneralPremise.Signature)
    (available : List String) : List String :=
  (GeneralPremise.queryOutputNames arguments signature.modes ++ available).eraseDups

/-- The general query request of a premise. -/
abbrev queryRequest (index position : Nat) (rule : RewriteRule) (bound : List TypeExpr) (relation : String)
    (arguments : List Pattern) (assignment : Assignment) : GeneralPremise.Query.Request :=
  ⟨⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩, relation, arguments,
    assignment⟩

/-- The number of rows of a relation before position `index`: the canonical tuple
position of row `index`. -/
def relationPosition (rows : List GeneralPremise.ProviderRow) (relation : String) (index : Nat) : Nat :=
  ((rows.take index).filter fun row => decide (row.relation = relation)).length

/-- An actual general event and an actual canonical selected query agree on
the authored premise, tuple, and original provider-row occurrence. -/
structure QueryEventAgreement (provider : GeneralPremise.ProviderSnapshot) (rule : RewriteRule)
    (event : GeneralPremise.Event) (query : RecordedQueryStep) : Prop where
  authored : rule.premises[query.premisePosition]? = some (.relationQuery query.relation query.arguments)
  choice : ∃ rowIndex origins row,
    event = .query query.premisePosition 0 rowIndex origins ∧
      provider.rows[rowIndex]? = some row ∧ query.event.tuple = row.values ∧
      query.event.tuplePosition = relationPosition provider.rows query.relation rowIndex
  firstMatch : query.event.matchPosition = 0

/-- Pure freshness checks add no query occurrence. The original full event
history remains retained in the result/receipt throughout this relation. -/
inductive QueryHistoryAgreement (provider : GeneralPremise.ProviderSnapshot) (rule : RewriteRule) :
    List GeneralPremise.Event → List RecordedQueryStep → Prop
  | nil : QueryHistoryAgreement provider rule [] []
  | query {event : GeneralPremise.Event} {query : RecordedQueryStep}
      {history : List GeneralPremise.Event} {queries : List RecordedQueryStep} :
      QueryEventAgreement provider rule event query →
      QueryHistoryAgreement provider rule history queries →
      QueryHistoryAgreement provider rule (event :: history) (query :: queries)
  | freshness {position quantifiers : Nat} {name : String} {subject : Pattern}
      {history : List GeneralPremise.Event} {queries : List RecordedQueryStep} :
      QueryHistoryAgreement provider rule history queries →
      QueryHistoryAgreement provider rule (.freshness position quantifiers name subject :: history) queries

theorem relationPosition_succ {rows : List GeneralPremise.ProviderRow} {relation : String} {index : Nat}
    {row : GeneralPremise.ProviderRow} (selected : rows[index]? = some row) :
    relationPosition rows relation (index + 1) =
      relationPosition rows relation index + if row.relation = relation then 1 else 0 := by
  simp only [relationPosition, List.take_add_one, selected, Option.toList_some, List.filter_append,
    List.length_append]
  by_cases same : row.relation = relation <;> simp [same]

/-- A general query answer and a canonical event are the same occurrence: the same
provider row, at that row's tuple position and first match, with corresponding
states. -/
structure SameOccurrence (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (bound : List TypeExpr) (relation : String) (available : List String)
    {request : GeneralPremise.Query.Request}
    (answer : GeneralPremise.Query.Answer (environment language provider) request)
    (event : RecordedEvent) : Prop where
  row : ∃ row, provider.rows[answer.rowIndex]? = some row ∧ event.tuple = row.values
  position : event.tuplePosition = relationPosition provider.rows relation answer.rowIndex
  firstMatch : event.matchPosition = 0
  state : QueryInvariant language provider rule bound available answer.assignment event.final

section Rows

variable (profile : FirstOrderProfileFacts language provider) {index position : Nat} {rule : RewriteRule}
  (declared : (environment language provider).language.rewrites[index]? = some rule)
  {relation : String} {arguments : List Pattern}
  (here : rule.premises[position]? = some (.relationQuery relation arguments))
  {bound : List TypeExpr} {available : List String} {signature : GeneralPremise.Signature}
  (signatureFound : GeneralPremise.signature? (environment language provider).provider relation
    arguments.length = some signature)
  (inputsAvailable : GeneralPremise.namesAvailable available
    (GeneralPremise.queryInputNames arguments signature.modes) = true)

include profile declared here in
theorem query_shapes : relation ≠ "eq" ∧ ∀ argument ∈ arguments, FirstOrder argument := by
  rcases (profile.rowFacts declared).premises _ (List.mem_of_getElem? here) with
    ⟨_, _, same, _, _⟩ | ⟨_, same, _⟩ | ⟨relation', arguments', same, distinct, shapes⟩
  · cases same
  · cases same
  · injection same with sameRelation sameArguments
    subst sameRelation sameArguments
    exact ⟨distinct, shapes⟩

include profile declared here signatureFound inputsAvailable

/-- **A canonical tuple match is a general query answer at the same row.** -/
theorem tuple_toGeneral
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment language provider).language rule []
      arguments signature.argumentTypes = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current)
    {rowIndex : Nat} {row : GeneralPremise.ProviderRow}
    (selected : (environment language provider).provider.rows[rowIndex]? = some row)
    (sameRelation : row.relation = relation) {extension final : Bindings}
    (matched : extension ∈ Engine.matchRelationArgs current arguments row.values)
    (merged : mergeBindings current extension = some final) :
    ∃ next origins,
      GeneralPremise.TracedQuery (environment language provider)
        ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩ relation arguments
        assignment rowIndex next origins ∧
      QueryInvariant language provider rule bound (queryAvailable arguments signature available) next final := by
  have ruleRow := profile.rowFacts declared
  have shapes := (query_shapes profile declared here).2
  obtain ⟨_, signatureRelation, _, modesLength⟩ :=
    GeneralPremise.signature?_readout _ _ _ _ signatureFound
  have lengths : arguments.length = signature.modes.length := modesLength.symm
  obtain ⟨readback, middleDefined⟩ := relationArgs_sound shapes matched
    (fun _ _ found => mergeBindings_subsumed_left merged found)
    (fun _ _ found => mergeBindings_subsumed_right merged found)
  obtain ⟨closedSignature, closedFound, closedTyped⟩ :=
    GeneralPremise.checkProviderClosed_row _ _ _ profile.providerClosed row (List.mem_of_getElem? selected)
  have sameSignature : closedSignature = signature := by
    rw [sameRelation, ← readback, List.length_map, signatureFound] at closedFound
    exact (Option.some.inj closedFound).symm
  subst sameSignature
  have rowTyped := GeneralPremise.closed_row_in_bound closedTyped bound
  have schemasTyped := GeneralPremise.schemaValuesChecked_sound schemasChecked
  rw [lookupRuleType_eq] at schemasTyped
  have extensionTyped := relationArgs_typed profile.valid shapes matched schemasTyped rowTyped.2
  have middleTyped := capturesTyped_merge state.typed extensionTyped merged
  have lifted : ScopedCompatible bound.length final assignment :=
    compatible_lift state.compatible (fun _ _ read => merge_lookup_left merged read)
  obtain ⟨next, origins, argumentsHeld, nextCompatible, outputsBound, nextExtends⟩ :=
    tracedArguments_construct (ruleIndex := index) ruleRow.unique here middleTyped arguments
      closedSignature.modes 0 (fun _ _ found => by simpa using found) shapes lengths middleDefined
      (fun name member => state.bound name (GeneralPremise.namesAvailable_sound _ _ inputsAvailable name member))
      lifted
  rw [readback] at argumentsHeld
  refine ⟨next, origins, .row selected signatureFound rowTyped argumentsHeld
    (nextCompatible.typed middleTyped ruleRow.unique), nextCompatible, middleTyped, ?_, ?_,
    mergeBindings_nodup merged state.unique⟩
  · intro name member
    rw [List.mem_eraseDups, List.mem_append] at member
    rcases member with output | inAvailable
    · exact outputsBound name output
    · obtain ⟨value, found⟩ := state.bound name inAvailable
      exact ⟨value, nextExtends name value found⟩
  · intro name member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    rw [List.mem_eraseDups, List.mem_append]
    rcases List.mem_append.mp (merge_members merged entryMember) with earlier | later
    · exact Or.inr (state.names _ (List.mem_map_of_mem earlier))
    · rcases query_names_cover lengths _ (relationArgs_names shapes matched entry later) with input | output
      · exact Or.inr (GeneralPremise.namesAvailable_sound _ _ inputsAvailable _ input)
      · exact Or.inl output

/-- **A general query answer at a row is a canonical tuple match of that row.** -/
theorem general_toTuple {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current)
    {rowIndex : Nat} {row : GeneralPremise.ProviderRow}
    (selected : (environment language provider).provider.rows[rowIndex]? = some row)
    {next : Assignment} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (traced : GeneralPremise.TracedQuery (environment language provider)
      ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩ relation arguments
      assignment rowIndex next origins) :
    ∃ extension ∈ Engine.matchRelationArgs current arguments row.values,
      ∃ final, mergeBindings current extension = some final := by
  have shapes := (query_shapes profile declared here).2
  match traced with
  | .row (row := row') (signature := signature') selected' signatureFound' _ argumentsHeld _ =>
  have sameRow : row' = row := Option.some.inj (selected'.symm.trans selected)
  subst sameRow
  have sameSignature : signature' = signature := Option.some.inj (signatureFound'.symm.trans signatureFound)
  subst sameSignature
  obtain ⟨_, _, _, modesLength⟩ := GeneralPremise.signature?_readout _ _ _ _ signatureFound
  have lengths : arguments.length = signature'.modes.length := modesLength.symm
  have initialRoots : GeneralPremise.RootValues bound.length assignment :=
    state.compatible.rootValues state.typed
  have roots : GeneralPremise.RootValues bound.length next :=
    tracedArguments_rootValues (GeneralFirstOrderProjection.inferred_zero rule) argumentsHeld initialRoots
  have readback : arguments.map (applyBindings (ordinary next)) = row'.values :=
    tracedArguments_readout rfl roots argumentsHeld shapes (fun _ _ found => found)
  have grows : ∀ name value, lookup assignment name = some value → lookup next name = some value :=
    fun name value found => argumentsHeld.readout.extension name value found
  have defined : Defined (ordinary next) (arguments.flatMap Pattern.freeFvarNames) := by
    intro name member
    obtain ⟨value, found⟩ : ∃ value, lookup next name = some value := by
      rcases query_names_cover lengths name member with input | output
      · obtain ⟨value, found⟩ := state.bound name
          (GeneralPremise.namesAvailable_sound _ _ inputsAvailable name input)
        exact ⟨value, grows name value found⟩
      · exact tracedArguments_bound argumentsHeld name output
    exact ⟨value.body, by rw [ordinary_lookup, found]; rfl⟩
  have compatible := state.ordinary_compatible grows
  obtain ⟨extension, matched, extensionCompatible, _, _, _⟩ :=
    relationArgs_instance (ordinary next) shapes defined compatible state.unique
  rw [readback] at matched
  obtain ⟨final, merged, _⟩ :=
    merge_compatible (ordinary next) current extension compatible extensionCompatible state.unique
  exact ⟨extension, matched, final, merged⟩

/-- **One provider row.** The row's general answers and its canonical events are
the same occurrences. -/
theorem row_occurrences
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment language provider).language rule []
      arguments signature.argumentTypes = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current)
    {cursor : Nat} {row : GeneralPremise.ProviderRow}
    (selected : (environment language provider).provider.rows[cursor]? = some row)
    (sameRelation : row.relation = relation) :
    List.Forall₂ (SameOccurrence language provider rule bound relation (queryAvailable arguments signature available)
        (request := queryRequest index position rule bound relation arguments assignment))
      (if checked : GeneralPremise.checkRow (environment language provider).language
            (environment language provider).free bound signature row = true then
          GeneralPremise.Query.eventual (environment language provider)
            (queryRequest index position rule bound relation arguments assignment)
            (.arguments (GeneralPremise.Query.rowArguments ⟨signature, signatureFound, cursor⟩ row selected checked))
        else [])
      (tupleEvents current arguments row.values (relationPosition provider.rows relation cursor)) := by
  have shapes := (query_shapes profile declared here).2
  have canonicalShort := tupleEvents_length_le_one shapes (initial := current) row.values
    (relationPosition provider.rows relation cursor)
  cases canonicalEq : tupleEvents current arguments row.values (relationPosition provider.rows relation cursor) with
  | nil =>
    split
    · rename_i checked
      cases generalEq : GeneralPremise.Query.eventual (environment language provider)
          (queryRequest index position rule bound relation arguments assignment)
          (.arguments (GeneralPremise.Query.rowArguments ⟨signature, signatureFound, cursor⟩ row selected checked)) with
      | nil => exact .nil
      | cons answer _ =>
        exfalso
        have member : answer ∈ GeneralPremise.Query.eventual (environment language provider)
            (queryRequest index position rule bound relation arguments assignment)
            (.arguments (GeneralPremise.Query.rowArguments ⟨signature, signatureFound, cursor⟩ row selected checked)) := by
          rw [generalEq]
          exact List.mem_cons_self ..
        have atRow := GeneralPremise.Query.eventual_rowIndex _ _ _ (index := cursor) rfl answer member
        have rowSelected : (environment language provider).provider.rows[answer.rowIndex]? = some row := by
          rw [atRow]
          exact selected
        obtain ⟨_, matched, _, merged⟩ :=
          general_toTuple profile declared here signatureFound inputsAvailable state rowSelected answer.valid
        exact tupleEvents_ne_nil (position := relationPosition provider.rows relation cursor) matched merged
          canonicalEq
    · exact .nil
  | cons event rest =>
    have restNil : rest = [] := by
      rw [canonicalEq, List.length_cons] at canonicalShort
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst restNil
    obtain ⟨extension, matchPosition, final, located, merged, eventEq⟩ :=
      mem_tupleEvents (event := event) (by rw [canonicalEq]; exact List.mem_singleton_self _)
    subst eventEq
    have matched : extension ∈ Engine.matchRelationArgs current arguments row.values :=
      List.mem_of_getElem? located
    have firstMatch : matchPosition = 0 := by
      have within := (List.getElem?_eq_some_iff.mp located).1
      have short := matchRelationArgs_length_le_one (seed := current) (values := row.values) shapes
      omega
    obtain ⟨next, origins, traced, nextState⟩ :=
      tuple_toGeneral profile declared here signatureFound inputsAvailable schemasChecked state selected sameRelation
        matched merged
    let answer : GeneralPremise.Query.Answer (environment language provider)
        (queryRequest index position rule bound relation arguments assignment) := ⟨cursor, next, origins, traced⟩
    obtain ⟨row', rowFound, checked, member⟩ :=
      GeneralPremise.Query.mem_rowArguments (environment language provider) _ signatureFound answer
        (List.getElem?_eq_some_iff.mp selected).1
    have sameRow : row' = row := Option.some.inj (rowFound.symm.trans selected)
    subst sameRow
    rw [dif_pos checked]
    have short := GeneralPremise.Query.eventual_arguments_length_le_one (environment language provider)
      (queryRequest index position rule bound relation arguments assignment)
      (GeneralPremise.Query.rowArguments ⟨signature, signatureFound, cursor⟩ row' selected checked) shapes
    have member' : answer ∈ GeneralPremise.Query.eventual (environment language provider)
        (queryRequest index position rule bound relation arguments assignment)
        (.arguments (GeneralPremise.Query.rowArguments ⟨signature, signatureFound, cursor⟩ row' selected checked)) :=
      member
    cases generalEq : GeneralPremise.Query.eventual (environment language provider)
        (queryRequest index position rule bound relation arguments assignment)
        (.arguments (GeneralPremise.Query.rowArguments ⟨signature, signatureFound, cursor⟩ row' selected checked)) with
    | nil =>
      rw [generalEq] at member'
      cases member'
    | cons first others =>
      have othersNil : others = [] := by
        rw [generalEq, List.length_cons] at short
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst othersNil
      rw [generalEq] at member'
      have same : answer = first := List.mem_singleton.mp member'
      refine .cons ?_ .nil
      rw [← same]
      exact ⟨⟨row', selected, rfl⟩, rfl, firstMatch, nextState⟩

/-- **All provider rows from a cursor.** -/
theorem rows_occurrences
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment language provider).language rule []
      arguments signature.argumentTypes = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current) (cursor : Nat) :
    List.Forall₂ (SameOccurrence language provider rule bound relation (queryAvailable arguments signature available)
        (request := queryRequest index position rule bound relation arguments assignment))
      (GeneralPremise.Query.eventual (environment language provider)
        (queryRequest index position rule bound relation arguments assignment) (.rows ⟨signature, signatureFound, cursor⟩))
      (rowEvents current relation arguments (provider.rows.drop cursor)
        (relationPosition provider.rows relation cursor)) := by
  cases rowFound : provider.rows[cursor]? with
  | none =>
    rw [GeneralPremise.Query.eventual_rows_none _ _ _ rowFound,
      List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp rowFound)]
    exact .nil
  | some row =>
    have within : cursor < provider.rows.length := (List.getElem?_eq_some_iff.mp rowFound).1
    have head : provider.rows[cursor] = row := (List.getElem?_eq_some_iff.mp rowFound).2
    have next := rows_occurrences schemasChecked state (cursor + 1)
    rw [relationPosition_succ rowFound] at next
    rw [GeneralPremise.Query.eventual_rows_some _ _ _ rowFound, List.drop_eq_getElem_cons within, head]
    simp only [rowEvents]
    by_cases same : row.relation = relation
    · rw [if_pos same]
      rw [if_pos same] at next
      exact List.rel_append (row_occurrences profile declared here signatureFound inputsAvailable schemasChecked
        state rowFound same) next
    · rw [if_neg same]
      rw [if_neg same, Nat.add_zero] at next
      obtain ⟨_, signatureRelation, _, _⟩ := GeneralPremise.signature?_readout _ _ _ _ signatureFound
      have unchecked : ¬ GeneralPremise.checkRow (environment language provider).language
          (environment language provider).free bound signature row = true := by
        simp [GeneralPremise.checkRow, signatureRelation, same]
      rw [dif_neg unchecked, List.nil_append]
      exact next
termination_by provider.rows.length - cursor
decreasing_by omega

/-- **Ordered query occurrences.** For a first-order query of an admitted rule,
the answers of the general query machine and the events of the canonical engine
over the provider's own relation environment are the same occurrences, one for
one and in order. Equal rows remain distinct occurrences on both sides. -/
theorem query_occurrences
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment language provider).language rule []
      arguments signature.argumentTypes = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current) :
    List.Forall₂ (SameOccurrence language provider rule bound relation (queryAvailable arguments signature available)
        (request := queryRequest index position rule bound relation arguments assignment))
      (GeneralPremise.Query.eventual (environment language provider)
        (queryRequest index position rule bound relation arguments assignment) .start)
      (recordedEvents (providerRelEnv provider) language current relation arguments) := by
  rw [GeneralPremise.Query.eventual_start_some _ _ signatureFound,
    recordedEvents_provider language provider current (query_shapes profile declared here).1 arguments]
  have rows := rows_occurrences profile declared here signatureFound inputsAvailable schemasChecked state 0
  have unregistered : relation ∉ (environment language provider).provider.dynamicRelations := by
    change relation ∉ provider.dynamicRelations
    simp only [profile.noDynamic, List.not_mem_nil, not_false_eq_true]
  simpa [relationPosition, unregistered] using rows

/-- A drained run of the general query machine has emitted those occurrences. -/
theorem settled_query_occurrences
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment language provider).language rule []
      arguments signature.argumentTypes = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current) (fuel : Nat)
    (settled : (GeneralPremise.Query.run (environment language provider)
      (queryRequest index position rule bound relation arguments assignment) fuel
      (GeneralPremise.Query.start _ _)).agenda = []) :
    List.Forall₂ (SameOccurrence language provider rule bound relation (queryAvailable arguments signature available)
        (request := queryRequest index position rule bound relation arguments assignment))
      (GeneralPremise.Query.run (environment language provider)
        (queryRequest index position rule bound relation arguments assignment) fuel
        (GeneralPremise.Query.start _ _)).answers
      (recordedEvents (providerRelEnv provider) language current relation arguments) := by
  rw [GeneralPremise.Query.settled_answers _ _ fuel settled]
  exact query_occurrences profile declared here signatureFound inputsAvailable schemasChecked state

/-- **The canonical results, with multiplicity.** The general answers correspond,
position by position, to the canonical engine's results of the query. -/
theorem query_results
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment language provider).language rule []
      arguments signature.argumentTypes = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current) :
    List.Forall₂ (fun answer final =>
        QueryInvariant language provider rule bound (queryAvailable arguments signature available)
          (GeneralPremise.Query.Answer.assignment answer) final)
      (GeneralPremise.Query.eventual (environment language provider)
        (queryRequest index position rule bound relation arguments assignment) .start)
      (Engine.relationQueryStep (providerRelEnv provider) language current relation arguments) := by
  rw [← Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.recordedEvents_results, List.forall₂_map_right_iff]
  exact (query_occurrences profile declared here signatureFound inputsAvailable schemasChecked state).imp
    fun _ _ same => same.state

end Rows

/-! ## The query machine as a block simulation of the canonical query step -/

open Mettapedia.GSLT.Distinction

/-- The query machine read as an ordered machine. -/
inductive QueryNode (environment : GeneralPremise.Environment) (request : GeneralPremise.Query.Request) where
  /-- The query, before its first task. -/
  | query
  /-- Retained work, which is bookkeeping. -/
  | pending (task : GeneralPremise.Query.Task environment request)
  /-- An emitted answer. -/
  | emitted (answer : GeneralPremise.Query.Answer environment request)
  /-- An unresolved admission obligation, kept observable. -/
  | unresolved (obligation : GeneralPremise.Query.Obligation)

/-- Retained work is bookkeeping; everything else is stable. -/
def QueryNode.stable {environment : GeneralPremise.Environment} {request : GeneralPremise.Query.Request} :
    QueryNode environment request → Bool
  | .pending _ => false
  | _ => true

/-- A task's successors are its answers, its unresolved obligations and its
branches, in that order. -/
def queryMachine (environment : GeneralPremise.Environment) (request : GeneralPremise.Query.Request) :
    OrderedSystem (QueryNode environment request) where
  step
    | .query => [.pending .start]
    | .pending task =>
      (GeneralPremise.Query.expand environment request task).answers.map .emitted ++
        (GeneralPremise.Query.expand environment request task).unresolved.map .unresolved ++
        (GeneralPremise.Query.expand environment request task).tasks.map .pending
    | .emitted _ => []
    | .unresolved _ => []
  halted
    | .emitted _ => true
    | .unresolved _ => true
    | _ => false

private theorem forestOfTrees_cost_le (environment : GeneralPremise.Environment)
    (request : GeneralPremise.Query.Request) :
    ∀ (tasks : List (GeneralPremise.Query.Task environment request))
      {branch : GeneralPremise.Query.Task environment request}, branch ∈ tasks →
      (GeneralPremise.Query.taskTree environment request branch).cost ≤
        (GeneralPremise.Scheduler.forestOfTrees (GeneralPremise.Query.expand environment request) tasks
          fun branch _ => GeneralPremise.Query.taskTree environment request branch).cost
  | task :: tasks, branch, member => by
    simp only [GeneralPremise.Scheduler.forestOfTrees, GeneralPremise.Scheduler.TaskForest.cost]
    rcases List.mem_cons.mp member with rfl | later
    · omega
    · have := forestOfTrees_cost_le environment request tasks later
      omega

/-- A branch's expansion tree costs strictly less than its parent's. -/
theorem taskTree_branch_cost_lt {environment : GeneralPremise.Environment}
    {request : GeneralPremise.Query.Request} {task branch : GeneralPremise.Query.Task environment request}
    (member : branch ∈ (GeneralPremise.Query.expand environment request task).tasks) :
    (GeneralPremise.Query.taskTree environment request branch).cost <
      (GeneralPremise.Query.taskTree environment request task).cost := by
  have bound := forestOfTrees_cost_le environment request _ member
  conv_rhs => rw [GeneralPremise.Query.taskTree]
  simp only [GeneralPremise.Scheduler.TaskTree.cost]
  omega

theorem taskTree_cost_pos {environment : GeneralPremise.Environment} {request : GeneralPremise.Query.Request}
    (task : GeneralPremise.Query.Task environment request) :
    0 < (GeneralPremise.Query.taskTree environment request task).cost := by
  rw [GeneralPremise.Query.taskTree]
  simp only [GeneralPremise.Scheduler.TaskTree.cost]
  omega

/-- Bookkeeping is ranked by the work account of the task's expansion tree. -/
def QueryNode.rank {environment : GeneralPremise.Environment} {request : GeneralPremise.Query.Request} :
    QueryNode environment request → Nat
  | .pending task => (GeneralPremise.Query.taskTree environment request task).cost
  | _ => 0

theorem query_ranked (environment : GeneralPremise.Environment) (request : GeneralPremise.Query.Request) :
    (queryMachine environment request).AdministrationRanked QueryNode.stable QueryNode.rank := by
  intro node unstable next member
  cases node with
  | pending task =>
    simp only [queryMachine, List.mem_append, List.mem_map] at member
    rcases member with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨branch, branchMember, rfl⟩
    · exact taskTree_cost_pos task
    · exact taskTree_cost_pos task
    · exact taskTree_branch_cost_lt branchMember
  | query => cases unstable
  | emitted => cases unstable
  | unresolved => cases unstable

/-- The canonical query read as an ordered machine: one step from the query to
its recorded events. -/
inductive CanonicalNode where
  | query
  | result (event : RecordedEvent)

def canonicalMachine (events : List RecordedEvent) : OrderedSystem CanonicalNode where
  step
    | .query => events.map .result
    | .result _ => []
  halted
    | .result _ => true
    | .query => false

/-- What each node of the query machine stands for: the query for the query, a
retained task for the canonical events of its eventual answers, an answer for
its own event. An unresolved obligation stands for nothing, so a block
simulation cannot pass one silently. -/
def queryBlock (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) (rule : RewriteRule)
    (bound : List TypeExpr) (relation : String) (available : List String)
    {request : GeneralPremise.Query.Request}
    (admission : GeneralPremise.Query.InputAdmission (environment language provider) request) :
    List CanonicalNode → QueryNode (environment language provider) request → Prop
  | occurrences, .query => occurrences = [.query]
  | occurrences, .pending task => GeneralPremise.Query.TaskReady admission task ∧
      ∃ events, List.Forall₂ (SameOccurrence language provider rule bound relation available)
        (GeneralPremise.Query.eventual _ request task) events ∧ occurrences = events.map .result
  | occurrences, .emitted answer => ∃ event,
      SameOccurrence language provider rule bound relation available answer event ∧
        occurrences = [.result event]
  | _, .unresolved _ => False

private theorem forall₂_append_split {α β : Type} {related : α → β → Prop} :
    ∀ {front back : List α} {targets : List β}, List.Forall₂ related (front ++ back) targets →
      ∃ first second, targets = first ++ second ∧ List.Forall₂ related front first ∧
        List.Forall₂ related back second
  | [], _, targets, both => ⟨[], targets, rfl, .nil, both⟩
  | _ :: _, _, _, .cons head rest => by
    obtain ⟨first, second, split, front, back⟩ := forall₂_append_split rest
    exact ⟨_ :: first, second, by rw [split]; rfl, .cons head front, back⟩

private theorem forall₂_flatMap_split {α β γ : Type} {related : β → γ → Prop} (expand : α → List β) :
    ∀ {items : List α} {targets : List γ}, List.Forall₂ related (items.flatMap expand) targets →
      ∃ blocks : List (List γ),
        List.Forall₂ (fun item block => List.Forall₂ related (expand item) block) items blocks ∧
          targets = blocks.flatten
  | [], _, both => by
    cases both
    exact ⟨[], .nil, rfl⟩
  | item :: items, _, both => by
    rw [List.flatMap_cons] at both
    obtain ⟨first, second, split, front, back⟩ := forall₂_append_split both
    obtain ⟨blocks, related, flattened⟩ := forall₂_flatMap_split expand back
    exact ⟨first :: blocks, .cons front related, by rw [split, flattened]; rfl⟩

private theorem flatten_singletons {α β : Type} (items : List α) (wrap : α → β) :
    (items.map fun item => [wrap item]).flatten = items.map wrap := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

private theorem emitted_blocks (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (bound : List TypeExpr) (relation : String) (available : List String)
    {request : GeneralPremise.Query.Request}
    (admission : GeneralPremise.Query.InputAdmission (environment language provider) request) :
    ∀ {answers : List (GeneralPremise.Query.Answer (environment language provider) request)}
      {events : List RecordedEvent},
      List.Forall₂ (SameOccurrence language provider rule bound relation available) answers events →
        List.Forall₂ (queryBlock language provider rule bound relation available admission)
          (events.map fun event => [CanonicalNode.result event]) (answers.map QueryNode.emitted)
  | _, _, .nil => .nil
  | _, _, .cons head rest =>
    .cons ⟨_, head, rfl⟩ (emitted_blocks language provider rule bound relation available admission rest)

private theorem pending_blocks (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (bound : List TypeExpr) (relation : String) (available : List String)
    {request : GeneralPremise.Query.Request}
    (admission : GeneralPremise.Query.InputAdmission (environment language provider) request) :
    ∀ {branches : List (GeneralPremise.Query.Task (environment language provider) request)}
      {blocks : List (List RecordedEvent)},
      (∀ branch ∈ branches, GeneralPremise.Query.TaskReady admission branch) →
      List.Forall₂ (fun item block => List.Forall₂ (SameOccurrence language provider rule bound relation available)
        (GeneralPremise.Query.eventual _ request item) block) branches blocks →
        List.Forall₂ (queryBlock language provider rule bound relation available admission)
          (blocks.map fun block => block.map CanonicalNode.result) (branches.map QueryNode.pending)
  | _, _, _, .nil => .nil
  | _, _, ready, .cons head rest =>
    .cons ⟨ready _ (List.mem_cons_self ..), _, head, rfl⟩
      (pending_blocks language provider rule bound relation available admission
        (fun other member => ready other (List.mem_cons_of_mem _ member)) rest)

/-- **The query machine is a block simulation of the canonical query step**,
for every event list that its start task's answers correspond to. -/
theorem query_blockSimulation (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (bound : List TypeExpr) (relation : String) (available : List String)
    {request : GeneralPremise.Query.Request}
    (admission : GeneralPremise.Query.InputAdmission (environment language provider) request)
    {events : List RecordedEvent}
    (occurrences : List.Forall₂ (SameOccurrence language provider rule bound relation available)
      (GeneralPremise.Query.eventual _ request .start) events) :
    BlockSimulation (canonicalMachine events) (queryMachine (environment language provider) request)
      QueryNode.stable (queryBlock language provider rule bound relation available admission) where
  stable_single := by
    intro blockOccurrences node blocked isStable
    cases node with
    | query => exact ⟨.query, blocked, rfl⟩
    | pending => cases isStable
    | emitted =>
      obtain ⟨event, _, rfl⟩ := blocked
      exact ⟨.result event, rfl, rfl⟩
    | unresolved => exact blocked.elim
  stable_step := by
    intro state node blocked isStable
    cases node with
    | query =>
      have same : state = .query := List.singleton_inj.mp blocked
      subst same
      exact ⟨[events.map .result], .cons ⟨trivial, events, occurrences, rfl⟩ .nil, by
        simp [canonicalMachine]⟩
    | pending => cases isStable
    | emitted =>
      obtain ⟨event, _, same⟩ := blocked
      cases List.singleton_inj.mp same
      exact ⟨[], .nil, rfl⟩
    | unresolved => exact blocked.elim
  administrative_split := by
    intro blockOccurrences node blocked isStable
    cases node with
    | pending task =>
      obtain ⟨ready, taskEvents, related, rfl⟩ := blocked
      obtain ⟨noObligations, branchesReady⟩ := GeneralPremise.Query.expand_ready admission task ready
      rw [GeneralPremise.Query.eventual_eq] at related
      obtain ⟨answerEvents, branchEvents, split, answersRelated, branchesRelated⟩ := forall₂_append_split related
      obtain ⟨blocks, blocksRelated, flattened⟩ := forall₂_flatMap_split _ branchesRelated
      have answerBlocks := emitted_blocks language provider rule bound relation available admission answersRelated
      have branchBlocks := pending_blocks language provider rule bound relation available admission
        branchesReady blocksRelated
      refine ⟨answerEvents.map (fun event => [CanonicalNode.result event]) ++
          blocks.map (fun block => block.map CanonicalNode.result), ?_, ?_⟩
      · show List.Forall₂ _ _ ((GeneralPremise.Query.expand _ request task).answers.map QueryNode.emitted ++
          (GeneralPremise.Query.expand _ request task).unresolved.map QueryNode.unresolved ++
          (GeneralPremise.Query.expand _ request task).tasks.map QueryNode.pending)
        rw [noObligations, List.map_nil, List.append_nil]
        exact List.rel_append answerBlocks branchBlocks
      · rw [split, flattened, List.flatten_append, flatten_singletons, ← List.map_flatten, List.map_append]
    | query => cases isStable
    | emitted => cases isStable
    | unresolved => cases isStable

/-- **One canonical query step is one saturated step of the query machine.** -/
theorem query_saturated (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (bound : List TypeExpr) (relation : String) (available : List String)
    {request : GeneralPremise.Query.Request}
    (admission : GeneralPremise.Query.InputAdmission (environment language provider) request)
    {events : List RecordedEvent}
    (occurrences : List.Forall₂ (SameOccurrence language provider rule bound relation available)
      (GeneralPremise.Query.eventual _ request .start) events) :
    OrderedSimulation (canonicalMachine events)
        ((queryMachine (environment language provider) request).saturate QueryNode.stable QueryNode.rank)
        (BlockSimulation.StableRelated QueryNode.stable
          (queryBlock language provider rule bound relation available admission)) ∧
      BlockSimulation.StableRelated QueryNode.stable
        (queryBlock language provider rule bound relation available admission) .query .query :=
  ⟨(query_blockSimulation language provider rule bound relation available admission occurrences).saturated
    (query_ranked _ request), rfl, rfl⟩

section Admitted

variable (profile : FirstOrderProfileFacts language provider) {index position : Nat} {rule : RewriteRule}
  (declared : (environment language provider).language.rewrites[index]? = some rule)
  {relation : String} {arguments : List Pattern}
  (here : rule.premises[position]? = some (.relationQuery relation arguments))
  {bound : List TypeExpr} {available : List String} {signature : GeneralPremise.Signature}
  (signatureFound : GeneralPremise.signature? (environment language provider).provider relation
    arguments.length = some signature)
  (inputsAvailable : GeneralPremise.namesAvailable available
    (GeneralPremise.queryInputNames arguments signature.modes) = true)

/-- The query machine's input admission, from the state before the premise and
the static input check. -/
def queryAdmission {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current)
    (inputsChecked : GeneralPremise.Static.checkQueryInputs rule (GeneralRuleBindingInference.inferredSpec rule)
      position 0 available 0 arguments signature.modes = true) :
    GeneralPremise.Query.InputAdmission (environment language provider)
      (queryRequest index position rule bound relation arguments assignment) where
  available := available
  signature := signature
  signatureFound := signatureFound
  zero := GeneralFirstOrderProjection.inferred_zero rule
  schemas := inputsChecked
  values := state.compatible.rootValues state.typed
  names := state.bound
  dynamicAvailable := by
    intro registered
    change relation ∈ provider.dynamicRelations at registered
    simp only [profile.noDynamic, List.not_mem_nil] at registered

include profile declared here signatureFound inputsAvailable

/-- **For an admitted query, one canonical query step is one saturated step of
the actual query machine.** -/
theorem admitted_query_saturated
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment language provider).language rule []
      arguments signature.argumentTypes = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current)
    (inputsChecked : GeneralPremise.Static.checkQueryInputs rule (GeneralRuleBindingInference.inferredSpec rule)
      position 0 available 0 arguments signature.modes = true) :
    OrderedSimulation
        (canonicalMachine (recordedEvents (providerRelEnv provider) language current relation arguments))
        ((queryMachine (environment language provider)
          (queryRequest index position rule bound relation arguments assignment)).saturate
            QueryNode.stable QueryNode.rank)
        (BlockSimulation.StableRelated QueryNode.stable
          (queryBlock language provider rule bound relation (queryAvailable arguments signature available)
            (queryAdmission profile (index := index) signatureFound state inputsChecked))) ∧
      BlockSimulation.StableRelated QueryNode.stable
        (queryBlock language provider rule bound relation (queryAvailable arguments signature available)
          (queryAdmission profile (index := index) signatureFound state inputsChecked)) .query .query :=
  query_saturated language provider rule bound relation _ (queryAdmission profile (index := index) signatureFound state inputsChecked)
    (query_occurrences profile declared here signatureFound inputsAvailable schemasChecked state)

end Admitted


/-! ## Rule firings, in order -/

open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine

theorem matchArgs_nodup {patterns : List Pattern}
    (each : ∀ pattern ∈ patterns, ∀ value, ∀ bindings ∈ matchPattern pattern value,
      (bindings.map Prod.fst).Nodup) :
    ∀ values, ∀ bindings ∈ matchArgs patterns values, (bindings.map Prod.fst).Nodup := by
  induction patterns with
  | nil => intro values; cases values <;> simp [matchArgs]
  | cons pattern rest ih =>
    intro values
    cases values with
    | nil => simp [matchArgs]
    | cons value values =>
      intro bindings member
      rw [matchArgs] at member
      obtain ⟨head, headMember, tailMember⟩ := List.mem_flatMap.mp member
      obtain ⟨tail, _, merged⟩ := List.mem_filterMap.mp tailMember
      exact mergeBindings_nodup merged (each pattern (List.mem_cons_self ..) value head headMember)

/-- A canonical match of a first-order pattern names each metavariable once. -/
theorem matchPattern_nodup {pattern : Pattern} (shape : FirstOrder pattern) :
    ∀ value, ∀ bindings ∈ matchPattern pattern value, (bindings.map Prod.fst).Nodup := by
  induction shape with
  | metavariable name =>
    intro value bindings member
    simp only [matchPattern, List.mem_singleton] at member
    subst member
    simp
  | constructor label arguments _ ih =>
    intro value
    cases value
    case apply actualLabel targets =>
      simp only [matchPattern]
      split
      · exact matchArgs_nodup (fun argument member => ih argument member) targets
      · simp
    all_goals simp [matchPattern]

theorem forall₂_flatMap {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → List γ} {g : β → List δ} :
    ∀ {first : List α} {second : List β}, List.Forall₂ R first second →
      (∀ a b, R a b → List.Forall₂ S (f a) (g b)) →
      List.Forall₂ S (first.flatMap f) (second.flatMap g)
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons head tail, each => by
    simp only [List.flatMap_cons]
    exact List.rel_append (each _ _ head) (forall₂_flatMap tail each)

theorem flatMap_eq_of_forall₂ {α β γ : Type} {R : α → β → Prop} {f : α → List γ} {g : β → List γ} :
    ∀ {first : List α} {second : List β}, List.Forall₂ R first second →
      (∀ a b, R a b → f a = g b) → first.flatMap f = second.flatMap g
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons head tail, each => by
    rw [List.flatMap_cons, List.flatMap_cons, each _ _ head, flatMap_eq_of_forall₂ tail each]

theorem map_eq_of_forall₂ {α β : Type} {f : α → β} :
    ∀ {first : List α} {second : List β}, List.Forall₂ (fun a b => f a = b) first second →
      first.map f = second
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head tail => by
    rw [List.map_cons, head, map_eq_of_forall₂ tail]

/-- Common checked query facts do not require constructor-headed roots;
invocations may select a rule through its checked sort instead. -/
structure QueryProfileFacts (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) : Prop where
  firstOrder : FirstOrderProfileFacts language provider
  stepless : ∀ {index : Nat} {rule : RewriteRule},
    (environment language provider).language.rewrites[index]? = some rule →
      ∀ source target, Premise.congruence source target ∉ rule.premises

/-- A first-order profile whose premises are freshness conditions and queries:
no rule asks for a child step. -/
structure QueryProfile (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) : Prop where
  firstOrder : FirstOrderProfile language provider
  stepless : ∀ {index : Nat} {rule : RewriteRule},
    (environment language provider).language.rewrites[index]? = some rule →
      ∀ source target, Premise.congruence source target ∉ rule.premises

theorem QueryProfile.toFacts (profile : QueryProfile language provider) : QueryProfileFacts language provider :=
  ⟨profile.firstOrder.toFirstOrderProfileFacts, profile.stepless⟩

instance : Coe (QueryProfile language provider) (QueryProfileFacts language provider) :=
  ⟨QueryProfile.toFacts⟩

/-- No executed rule asks for a child step. -/
def checkStepless (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) : Bool :=
  (environment language provider).language.rewrites.all fun rule =>
    rule.premises.all fun premise =>
      match premise with
      | .congruence _ _ => false
      | _ => true

/-- The common query profile admits finite first-order wildcard roots while
retaining all existing provider, row, typing and flow checks. -/
def checkQueryProfileFacts (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) : Bool :=
  checkFirstOrderProfileFacts language provider && checkStepless language provider

theorem QueryProfileFacts.of_check (checked : checkQueryProfileFacts language provider = true) :
    QueryProfileFacts language provider := by
  simp only [checkQueryProfileFacts, Bool.and_eq_true] at checked
  obtain ⟨firstOrder, stepless⟩ := checked
  refine ⟨FirstOrderProfileFacts.of_check firstOrder, ?_⟩
  intro index rule declared source target member
  have ruleChecked := List.all_eq_true.mp stepless rule (List.mem_of_getElem? declared)
  have premiseChecked := List.all_eq_true.mp ruleChecked _ member
  simp at premiseChecked

/-- The query profile as one decidable check. -/
def checkQueryProfile (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) : Bool :=
  checkFirstOrderProfile language provider && checkStepless language provider

theorem QueryProfile.of_check (checked : checkQueryProfile language provider = true) :
    QueryProfile language provider := by
  simp only [checkQueryProfile, Bool.and_eq_true] at checked
  obtain ⟨firstOrder, stepless⟩ := checked
  refine ⟨FirstOrderProfile.of_check firstOrder, ?_⟩
  intro index rule declared source target member
  have ruleChecked := List.all_eq_true.mp stepless rule (List.mem_of_getElem? declared)
  have premiseChecked := List.all_eq_true.mp ruleChecked _ member
  simp at premiseChecked

/-- Query-only syntax from an actual first-order rule presentation earns
the existing static representation checker from its checked flow and types. -/
theorem FirstOrderRowFacts.static_of_queries {index : Nat} {rule : RewriteRule}
    (row : FirstOrderRowFacts language provider index rule)
    (queries : ∀ premise ∈ rule.premises, ∃ relation arguments,
      premise = .relationQuery relation arguments) :
    GeneralPremise.Static.checkRule (environment language provider).language
      (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule) = true := by
  have flow := row.flow
  simp only [GeneralPremise.rulePremisesAdmitted, Bool.and_eq_true] at flow
  have projections : ∀ offset relation arguments,
      rule.premises[offset]? = some (.relationQuery relation arguments) →
      ∀ argumentIndex schema, arguments[argumentIndex]? = some schema →
      GeneralPremise.checkRootProjectionSchema rule (GeneralRuleBindingInference.inferredSpec rule)
        (.premise (0 + offset) 0 argumentIndex) [] schema = true := by
    intro offset relation arguments selected argumentIndex schema argument
    obtain ⟨before, supported⟩ := GeneralPremise.Static.premiseFlow_supported_at
      (environment language provider).language (environment language provider).provider rule
      (GeneralRuleBindingInference.inferredSpec rule) rule.premises rule.left.freeFvarNames offset
      (.relationQuery relation arguments) flow.1 selected
    cases found : GeneralPremise.signature? (environment language provider).provider relation arguments.length with
    | none => simp [GeneralPremise.premiseFlow, found] at supported
    | some signature =>
      simp only [GeneralPremise.premiseFlow, found, Bool.and_eq_true] at supported
      have typed := GeneralPremise.schemaValuesChecked_sound supported.2
      obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp argument
      have childTyped := typed.get within (by rw [← typed.length_eq]; exact within)
      simp only [List.get_eq_getElem, same] at childTyped
      have shapes : FirstOrder schema := by
        rcases row.premises _ (List.mem_of_getElem? selected) with
          ⟨_, _, impossible, _, _⟩ | ⟨_, impossible, _⟩ | ⟨rel, args, equality, _, shapes⟩
        · cases impossible
        · cases impossible
        · cases equality
          exact shapes schema (List.mem_of_getElem? argument)
      exact GeneralPremise.Static.firstOrder_projection_of_typed row.unique shapes
        (nameCoherent_premise (sitePattern_query (by simpa only [Nat.zero_add] using selected) argument)) childTyped
  have staticFlow := GeneralPremise.Static.queryFlow_of_projection
    (environment language provider).language (environment language provider).provider rule
    (GeneralRuleBindingInference.inferredSpec rule) rule.premises 0 rule.left.freeFvarNames
    (GeneralPremise.Static.initialRefinement rule) (fun _ present => present) queries projections flow.1
  obtain ⟨type, _, rightTyped⟩ := row.typed
  have contexts : (fun name => GeneralPremise.lookupRuleType? rule name) =
      FreeTypeContext.ofList rule.typeContext := by
    funext name
    rw [GeneralPremise.lookupRuleType?_eq_lookup, context_ofList_lookup]
  have rightProjected := GeneralPremise.Static.firstOrder_projection_of_typed row.unique row.right
    (NameCoherent.right rule) (contexts ▸ rightTyped)
  have names := GeneralPremise.Static.namesAvailable_mono staticFlow.2 flow.2
  simp only [GeneralPremise.Static.checkRule, inferred_zero, staticFlow.1, rightProjected,
    names, Bool.and_self]

theorem QueryProfileFacts.static_of_queries (profile : QueryProfileFacts language provider)
    (queries : ∀ {index : Nat} {rule : RewriteRule},
      (environment language provider).language.rewrites[index]? = some rule →
      ∀ premise ∈ rule.premises, ∃ relation arguments, premise = .relationQuery relation arguments) :
    GeneralPremise.Static.checkLanguage (environment language provider) = true := by
  apply List.all_eq_true.mpr
  rintro ⟨rule, index⟩ member
  have declared := List.mk_mem_zipIdx_iff_getElem?.mp member
  have row := profile.firstOrder.rowFacts declared
  dsimp only
  rw [row.specified]
  simp only [row.admitted, Bool.true_and]
  exact row.static_of_queries (queries declared)

section PremiseFirings

variable (profile : QueryProfileFacts language provider) {index : Nat} {rule : RewriteRule}
  (declared : (environment language provider).language.rewrites[index]? = some rule)
  {bound : List TypeExpr}

include profile declared

/-- **A freshness premise, both ways.** Under the state before it, the general
result and the canonical bindings of a first-order freshness premise are both
present or both absent, and they leave the state unchanged. -/
theorem freshness_occurrences {position : Nat} {condition : FreshnessCondition}
    (here : rule.premises[position]? = some (.freshness condition)) {available : List String}
    (supported : (GeneralPremise.premiseFlow (environment language provider).language
      (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
      available (.freshness condition)).supported = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current)
    (relEnv : Engine.RelationEnv) :
    List.Forall₂ (fun result final => QueryInvariant language provider rule bound available
        (GeneralPremise.Execution.Result.continues result) final)
      (GeneralPremise.Execution.results (environment language provider)
        (.premise ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩
          (.freshness condition) assignment))
      (Engine.premiseStepWithEnv relEnv language current (.freshness condition)) := by
  have row := profile.firstOrder.rowFacts declared
  have termShape : FirstOrder condition.term := by
    rcases row.premises _ (List.mem_of_getElem? here) with
      ⟨_, _, same, _, _⟩ | ⟨condition', same, shape⟩ | ⟨_, _, same, _, _⟩
    · cases same
    · injection same with same
      subst same
      exact shape
    · cases same
  simp only [GeneralPremise.premiseFlow, Bool.and_eq_true] at supported
  obtain ⟨⟨_, termAvailable⟩, _⟩ := supported
  have termBound : GeneralPremise.BoundNames assignment condition.term.freeFvarNames :=
    fun name member => state.bound name (GeneralPremise.namesAvailable_sound _ _ termAvailable name member)
  have termDefined : Defined current condition.term.freeFvarNames :=
    compatible_defined state.compatible termBound
  have roots : GeneralPremise.RootValues bound.length assignment :=
    state.compatible.rootValues state.typed
  obtain ⟨subject, subjectRead⟩ := instantiation_total
    (operation := Substitution.instantiateBVar) termShape
    (nameCoherent_premise (sitePattern_freshness here)) termBound roots
    (dependencies_of_typed row.unique termDefined state.typed)
  have subjectSame : applyBindings current condition.term = subject :=
    (compatible_apply_eq state.compatible termShape termBound).symm.trans
      (instantiation_readout termShape roots subjectRead)
  have subjectAt : instantiateAt? rule (GeneralRuleBindingInference.inferredSpec rule) bound.length
      (.premise position 0 0) [] 0 assignment condition.term = some subject := subjectRead
  have named : GeneralPremise.freshnessName? bound.length assignment condition.varName =
      resolveFreshVarName current condition.varName := by
    unfold GeneralPremise.freshnessName? resolveFreshVarName
    cases foundAssignment : lookup assignment condition.varName with
    | none =>
      cases present : current.lookup condition.varName with
      | none => rfl
      | some value =>
        exfalso
        have inCurrent : condition.varName ∈ current.map Prod.fst :=
          List.mem_map.mpr ⟨(condition.varName, value), raw_lookup_member present, rfl⟩
        obtain ⟨_, found⟩ := state.bound _ (state.names _ inCurrent)
        rw [found] at foundAssignment
        cases foundAssignment
    | some value =>
      obtain ⟨_, _, read⟩ := state.compatible (condition.varName, value)
        (ConditionalEquationExecution.lookup_assignment_member assignment _ value foundAssignment)
      rw [read]
      dsimp only
      rw [root_value_readout (roots _ _ foundAssignment)]
      cases value.body <;> rfl
  rw [GeneralPremise.Execution.results]
  simp only [Engine.premiseStepWithEnv, subjectSame]
  cases resolved : resolveFreshVarName current condition.varName with
  | none =>
    have absent : GeneralPremise.freshnessSubject? rule (GeneralRuleBindingInference.inferredSpec rule)
        bound position 0 assignment condition = none := by
      simp [GeneralPremise.freshnessSubject?, named, resolved]
    split
    next => exact .nil
    next found => rw [absent] at found; cases found
  | some atom =>
    have present : GeneralPremise.freshnessSubject? rule (GeneralRuleBindingInference.inferredSpec rule)
        bound position 0 assignment condition = some (atom, subject) := by
      simp [GeneralPremise.freshnessSubject?, named, resolved, subjectAt]
    split
    next missing => rw [present] at missing; cases missing
    next found =>
      rw [present] at found
      cases found
      by_cases fresh : Substitution.isFresh atom subject = true
      · have checked : Substitution.checkFreshness ⟨atom, subject⟩ = true := fresh
        rw [dif_pos fresh]
        simp only [checked, ↓reduceIte]
        exact .cons state .nil
      · have unchecked : Substitution.checkFreshness ⟨atom, subject⟩ = false :=
          Bool.eq_false_iff.mpr fresh
        rw [dif_neg fresh]
        simp only [unchecked, Bool.false_eq_true, ↓reduceIte]
        exact .nil


/-- **A query premise, both ways**, in order: the general results of a
first-order query premise and the canonical bindings of the query over the
provider's own relation environment, one for one. -/
theorem queryPremise_recorded_occurrences {position : Nat} {relation : String} {arguments : List Pattern}
    (here : rule.premises[position]? = some (.relationQuery relation arguments))
    {available : List String}
    (supported : (GeneralPremise.premiseFlow (environment language provider).language
      (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
      available (.relationQuery relation arguments)).supported = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current) :
    List.Forall₂ (fun result event => QueryInvariant language provider rule bound
        (GeneralPremise.premiseFlow (environment language provider).language
          (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
          available (.relationQuery relation arguments)).available
        (GeneralPremise.Execution.Result.continues result) event.final ∧
      QueryEventAgreement provider rule (premiseEvent result)
        ⟨position, relation, arguments, arguments.map (applyBindings current), event⟩)
      (GeneralPremise.Execution.results (environment language provider)
        (.premise ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩
          (.relationQuery relation arguments) assignment))
      (recordedEvents (providerRelEnv provider) language current relation arguments) := by
  cases signatureFound : GeneralPremise.signature? (environment language provider).provider relation
      arguments.length with
  | none => simp [GeneralPremise.premiseFlow, signatureFound] at supported
  | some signature =>
    have flowEq : GeneralPremise.premiseFlow (environment language provider).language
        (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
        available (.relationQuery relation arguments) =
          ⟨queryAvailable arguments signature available,
            GeneralPremise.namesAvailable available
                (GeneralPremise.queryInputNames arguments signature.modes) &&
              GeneralPremise.schemaValuesChecked (environment language provider).language rule []
                arguments signature.argumentTypes⟩ := by
      simp only [GeneralPremise.premiseFlow, signatureFound]
    rw [flowEq] at supported ⊢
    simp only [Bool.and_eq_true] at supported
    obtain ⟨inputsAvailable, schemasChecked⟩ := supported
    rw [GeneralPremise.Execution.results]
    simp only [GeneralPremise.Query.pending, GeneralPremise.Query.start, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.nil_append, List.forall₂_map_left_iff]
    exact (query_occurrences profile.firstOrder declared here signatureFound inputsAvailable schemasChecked
      state).imp fun answer event same => by
        obtain ⟨row, selected, tuple⟩ := same.row
        exact ⟨same.state, ⟨here,
          ⟨answer.rowIndex, answer.origins, row, rfl, selected, tuple, same.position⟩,
          same.firstMatch⟩⟩

theorem queryPremise_occurrences {position : Nat} {relation : String} {arguments : List Pattern}
    (here : rule.premises[position]? = some (.relationQuery relation arguments))
    {available : List String}
    (supported : (GeneralPremise.premiseFlow (environment language provider).language
      (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
      available (.relationQuery relation arguments)).supported = true)
    {assignment : Assignment} {current : Bindings}
    (state : QueryInvariant language provider rule bound available assignment current) :
    List.Forall₂ (fun result final => QueryInvariant language provider rule bound
        (GeneralPremise.premiseFlow (environment language provider).language
          (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
          available (.relationQuery relation arguments)).available
        (GeneralPremise.Execution.Result.continues result) final)
      (GeneralPremise.Execution.results (environment language provider)
        (.premise ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩
          (.relationQuery relation arguments) assignment))
      (Engine.premiseStepWithEnv (providerRelEnv provider) language current
        (.relationQuery relation arguments)) := by
  rw [Engine.premiseStepWithEnv,
    ← Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.recordedEvents_results,
    List.forall₂_map_right_iff]
  exact (queryPremise_recorded_occurrences profile declared here supported state).imp
    fun _ _ related => related.1

/-- The actual general premise execution and the independent recorded
canonical fold preserve every ordered query occurrence, including equal rows. -/
theorem premises_recorded_occurrences :
    ∀ (pending : List Premise) (position : Nat) {available : List String}
      {assignment : Assignment} {current : Bindings},
      (∀ offset premise, pending[offset]? = some premise →
        rule.premises[position + offset]? = some premise) →
      (GeneralPremise.premisesFlow (environment language provider).language
        (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
        available pending).supported = true →
      QueryInvariant language provider rule bound available assignment current →
      List.Forall₂ (fun result run =>
        QueryInvariant language provider rule bound
          (GeneralPremise.premisesFlow (environment language provider).language
            (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
            available pending).available (GeneralPremise.Execution.Result.continues result) run.bindings ∧
        QueryHistoryAgreement provider rule (premiseHistory result) run.queries)
        (GeneralPremise.Execution.results (environment language provider)
          (.premises ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩
            pending assignment))
        (recordedPremiseRuns (providerRelEnv provider) language pending position current)
  | [], _, _, _, _, _, _, state => by
    rw [GeneralPremise.Execution.results, recordedPremiseRuns]
    exact .cons ⟨state, .nil⟩ .nil
  | premise :: pending, position, available, assignment, current, located, supported, state => by
    have here : rule.premises[position]? = some premise := by simpa using located 0 premise rfl
    have locatedRest : ∀ offset later, pending[offset]? = some later →
        rule.premises[position + 1 + offset]? = some later := fun offset later selected => by
      simpa [Nat.add_assoc, Nat.add_comm 1 offset] using located (offset + 1) later selected
    simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported ⊢
    obtain ⟨headSupported, tailSupported⟩ := supported
    cases premise with
    | relationQuery relation arguments =>
      rw [GeneralPremise.Execution.results, recordedPremiseRuns]
      apply forall₂_flatMap
        (queryPremise_recorded_occurrences profile declared here headSupported state)
      intro first event related
      have tail := premises_recorded_occurrences pending (position + 1) locatedRest tailSupported related.1
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact tail.imp fun result run agrees => by
        cases first with
        | premise middle head held =>
          cases result with
          | premises completed history heldTail =>
            exact ⟨agrees.1, .query related.2 agrees.2⟩
    | freshness condition =>
      rw [GeneralPremise.Execution.results]
      simp only [recordedPremiseRuns]
      apply forall₂_flatMap
        (freshness_occurrences profile declared here headSupported state (providerRelEnv provider))
      intro first next related
      have tail := premises_recorded_occurrences pending (position + 1) locatedRest tailSupported related
      rw [List.forall₂_map_left_iff]
      exact tail.imp fun result run agrees => by
        cases first with
        | premise middle head held =>
          cases held with
          | freshness read fresh =>
            cases result with
            | premises completed history heldTail => exact ⟨agrees.1, .freshness agrees.2⟩
    | congruence source target =>
      exact False.elim (profile.stepless declared source target (List.mem_of_getElem? here))
    | scopedStep step =>
      have unsupported := (profile.firstOrder.rowFacts declared).premises _ (List.mem_of_getElem? here)
      rcases unsupported with ⟨_, _, impossible, _, _⟩ | ⟨_, impossible, _⟩ | ⟨_, _, impossible, _, _⟩ <;> cases impossible
    | forAll collection parameter body =>
      have unsupported := (profile.firstOrder.rowFacts declared).premises _ (List.mem_of_getElem? here)
      rcases unsupported with ⟨_, _, impossible, _, _⟩ | ⟨_, impossible, _⟩ | ⟨_, _, impossible, _, _⟩ <;> cases impossible

/-- **The premises of a rule firing, in order.** From corresponding states,
the general results of the remaining premises and the canonical bindings they
produce correspond one for one, in order. -/
theorem premises_occurrences (recursiveStep : Pattern → List Pattern) :
    ∀ (pending : List Premise) (position : Nat) {available : List String}
      {assignment : Assignment} {current : Bindings},
      (∀ offset premise, pending[offset]? = some premise →
        rule.premises[position + offset]? = some premise) →
      (GeneralPremise.premisesFlow (environment language provider).language
        (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
        available pending).supported = true →
      QueryInvariant language provider rule bound available assignment current →
      List.Forall₂ (fun result final => QueryInvariant language provider rule bound
          (GeneralPremise.premisesFlow (environment language provider).language
            (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
            available pending).available (GeneralPremise.Execution.Result.continues result) final)
        (GeneralPremise.Execution.results (environment language provider)
          (.premises ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩
            pending assignment))
        (premisesUsing (engineBasePremises (providerRelEnv provider)) language recursiveStep pending
          current)
  | [], _, _, _, _, _, _, state => by
    rw [GeneralPremise.Execution.results]
    exact .cons state .nil
  | premise :: pending, position, available, assignment, current, located, supported, state => by
    have here : rule.premises[position]? = some premise := by simpa using located 0 premise rfl
    have locatedRest : ∀ offset later, pending[offset]? = some later →
        rule.premises[position + 1 + offset]? = some later := fun offset later selected => by
      simpa [Nat.add_assoc, Nat.add_comm 1 offset] using located (offset + 1) later selected
    simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported ⊢
    obtain ⟨headSupported, tailSupported⟩ := supported
    rw [GeneralPremise.Execution.results]
    simp only [premisesUsing]
    have head : List.Forall₂ (fun result middle => QueryInvariant language provider rule bound
          (GeneralPremise.premiseFlow (environment language provider).language
            (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
            available premise).available (GeneralPremise.Execution.Result.continues result) middle)
        (GeneralPremise.Execution.results (environment language provider)
          (.premise ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩
            premise assignment))
        (premiseStepUsing (engineBasePremises (providerRelEnv provider)) language recursiveStep current
          premise) := by
      rcases (profile.firstOrder.rowFacts declared).premises premise (List.mem_of_getElem? here) with
        ⟨source, target, same, _, _⟩ | ⟨condition, same, _⟩ | ⟨relation, arguments, same, _, _⟩
      · exact absurd (same ▸ List.mem_of_getElem? here) (profile.stepless declared source target)
      · subst same
        exact freshness_occurrences profile declared here headSupported state (providerRelEnv provider)
      · subst same
        exact queryPremise_occurrences profile declared here headSupported state
    apply forall₂_flatMap head
    intro result middle related
    rw [List.forall₂_map_left_iff]
    have tail := premises_occurrences recursiveStep pending (position + 1) locatedRest tailSupported related
    exact tail.imp fun rest final holds =>
      (congrArg (QueryInvariant language provider rule bound _ · final)
        (GeneralPremise.Execution.Result.prepend_continues result rest)).mpr holds


/-- Actual premise results preserve unique scoped names and have exactly the
canonical logical binding readout, including absent entries. -/
theorem premises_occurrences_bindingAgreement (recursiveStep : Pattern → List Pattern)
    (pending : List Premise) (position : Nat) {available : List String}
    {assignment : Assignment} {current : Bindings}
    (located : ∀ offset premise, pending[offset]? = some premise →
      rule.premises[position + offset]? = some premise)
    (supported : (GeneralPremise.premisesFlow (environment language provider).language
      (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
      available pending).supported = true)
    (state : QueryInvariant language provider rule bound available assignment current)
    (unique : (assignment.map Prod.fst).Nodup) :
    List.Forall₂ (fun result final =>
      QueryInvariant language provider rule bound
        (GeneralPremise.premisesFlow (environment language provider).language
          (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
          available pending).available (GeneralPremise.Execution.Result.continues result) final ∧
      BindingAgreement
        (GeneralPremise.premisesFlow (environment language provider).language
          (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
          available pending).available (GeneralPremise.Execution.Result.continues result) final)
      (GeneralPremise.Execution.results (environment language provider)
        (.premises ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩
          pending assignment))
      (premisesUsing (engineBasePremises (providerRelEnv provider)) language recursiveStep pending current) := by
  have eachSupported : ∀ premise ∈ pending, SupportedPremise premise := by
    intro premise member
    obtain ⟨offset, selected⟩ := List.mem_iff_getElem?.mp member
    exact (profile.firstOrder.rowFacts declared).premises premise (List.mem_of_getElem? (located offset premise selected))
  exact (premises_occurrences profile declared recursiveStep pending position located supported state).imp
    fun result final related => by
      cases result with
      | premises completed events held =>
        exact ⟨related, related.bindingAgreement (supported_premises_unique eachSupported held unique)⟩

end PremiseFirings

section RuleFirings

variable (profile : QueryProfile language provider) {index : Nat} {rule : RewriteRule}
  (declared : (environment language provider).language.rewrites[index]? = some rule)
  {bound : List TypeExpr}

include profile declared

/-- The general root match request of a rule at a source. -/
abbrev rootMatchRequest (rule : RewriteRule) (bound : List TypeExpr) (source : Pattern) :
    GeneralScopedMatchMachine.Request :=
  ⟨rule, GeneralRuleBindingInference.inferredSpec rule, bound.length, .left, [], 0, [], rule.left, source⟩

omit profile declared in
/-- The actual root matchers agree once each successful canonical match has
its independently earned typed-capture interpretation. -/
theorem root_matches_of_capturesTyped {source : Pattern}
    (shape : FirstOrder rule.left) (unique : (rule.typeContext.map Prod.fst).Nodup)
    (capturesTyped : ∀ initial, initial ∈ matchPattern rule.left source →
      CapturesTyped (environment language provider).language (environment language provider).free
        bound rule.typeContext initial) :
    List.Forall₂ (fun answer initial =>
        QueryInvariant language provider rule bound rule.left.freeFvarNames answer.val.assignment initial ∧
          GeneralPremise.checkTypedAssignment (environment language provider)
            ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩
            answer.val.assignment = true ∧
          applyBindings initial rule.left = source)
      (GeneralScopedMatchMachine.emits (rootMatchRequest rule bound source)
        (GeneralScopedMatchMachine.start (rootMatchRequest rule bound source)) .start 0)
      (matchPattern rule.left source) := by
  have generalFew := GeneralScopedMatchMachine.emits_start_length_le_one
    (request := rootMatchRequest rule bound source) shape
  have canonicalFew := matchPattern_length_le_one shape source
  cases canonical : matchPattern rule.left source with
  | nil =>
    cases general : GeneralScopedMatchMachine.emits (rootMatchRequest rule bound source)
        (GeneralScopedMatchMachine.start (rootMatchRequest rule bound source)) .start 0 with
    | nil => exact .nil
    | cons answer _ =>
      exfalso
      have matching := answer.property.matching
      have roots : GeneralPremise.RootValues bound.length answer.val.assignment :=
        GeneralPremise.matching_rootValues (inferred_zero rule)
          (fun _ _ found => by simp [lookup] at found) matching
      have leftSame := matching_reconstructs shape matching (GeneralScopedMatch.Extends.refl _) roots
      have leftDefined : Defined (ordinary answer.val.assignment) rule.left.freeFvarNames := by
        intro name member
        obtain ⟨value, found⟩ := GeneralPremise.matching_bound_names matching name member
        exact ⟨value.body, by rw [ordinary_lookup, found]; rfl⟩
      obtain ⟨bindings, matched, _⟩ := match_instance (ordinary answer.val.assignment) shape leftDefined
      rw [leftSame] at matched
      have member := matchRel_complete matched
      rw [canonical] at member
      cases member
  | cons initial rest =>
    have restNil : rest = [] := by
      rw [canonical] at canonicalFew
      simpa using canonicalFew
    subst restNil
    have initialMember : initial ∈ matchPattern rule.left source := by
      rw [canonical]
      exact List.mem_singleton_self _
    have leftMatched : MatchRel rule.left source initial := matchPattern_sound initialMember
    have leftSource : applyBindings initial rule.left = source :=
      matchRel_correct leftMatched shape.isMatchCorrect
    have initialTyped := capturesTyped initial initialMember
    have leftDefined : Defined initial rule.left.freeFvarNames := raw_matching_defined shape leftMatched
    obtain ⟨captured, leftMatches, leftCompatible⟩ := scoped_instance (initial := [])
      shape (NameCoherent.left rule) leftDefined initialTyped unique
      (fun _ member => by cases member)
    rw [leftSource] at leftMatches
    obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace leftMatches
    have present := GeneralScopedMatchMachine.mem_emits_start
      (request := rootMatchRequest rule bound source) (answer := ⟨captured, trace⟩) traced
    cases general : GeneralScopedMatchMachine.emits (rootMatchRequest rule bound source)
        (GeneralScopedMatchMachine.start (rootMatchRequest rule bound source)) .start 0 with
    | nil =>
      rw [general] at present
      cases present
    | cons answer more =>
      have moreNil : more = [] := by
        rw [general] at generalFew
        simpa using generalFew
      subst moreNil
      rw [general] at present
      have same : answer.val = ⟨captured, trace⟩ := by simpa [eq_comm] using present
      refine .cons ⟨?_, ?_, leftSource⟩ .nil
      · rw [same]
        exact ⟨leftCompatible, initialTyped, GeneralPremise.matching_bound_names leftMatches,
          fun name member => by
            obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
            exact matchRel_names shape leftMatched entry entryMember,
          matchPattern_nodup shape source initial initialMember⟩
      · rw [same]
        exact GeneralPremise.checkTypedAssignment_complete (leftCompatible.typed initialTyped unique)

/-- **The root match, both ways.** The legacy headed profile derives the
local typed-capture condition from the actual successful match. -/
theorem root_matches {type : TypeExpr} {source : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) :
    List.Forall₂ (fun answer initial =>
        QueryInvariant language provider rule bound rule.left.freeFvarNames answer.val.assignment initial ∧
          GeneralPremise.checkTypedAssignment (environment language provider)
            ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩
            answer.val.assignment = true ∧
          applyBindings initial rule.left = source)
      (GeneralScopedMatchMachine.emits (rootMatchRequest rule bound source)
        (GeneralScopedMatchMachine.start (rootMatchRequest rule bound source)) .start 0)
      (matchPattern rule.left source) := by
  have row := profile.firstOrder.rows declared
  apply root_matches_of_capturesTyped row.left row.unique
  intro initial member
  have matched := matchPattern_sound member
  have leftSource := matchRel_correct matched row.left.isMatchCorrect
  obtain ⟨label, arguments, headed⟩ := row.headed
  obtain ⟨ruleType, leftTyped, _⟩ := row.typed
  have sameType : ruleType = type := by
    have sourceHas := sourceTyped.1
    rw [← leftSource, headed] at sourceHas
    rw [headed] at leftTyped
    simp only [applyBindings] at sourceHas
    exact apply_types_agree profile.firstOrder.valid leftTyped sourceHas
  subst sameType
  exact matching_captures_typed profile.firstOrder.valid row.left matched leftTyped sourceTyped.1
    sourceTyped.2.1 sourceTyped.2.2.1

omit profile declared in
/-- The actual root firing loop tests capture typing after matching. The raw
matcher is left intact, including a wildcard match later refused by this test. -/
def typedRootMatchAnswers (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (index : Nat) (rule : RewriteRule) (bound : List TypeExpr) (source : Pattern) :=
  (GeneralScopedMatchMachine.emits (rootMatchRequest rule bound source)
    (GeneralScopedMatchMachine.start (rootMatchRequest rule bound source)) .start 0).filter fun answer =>
      GeneralPremise.checkTypedAssignment (environment language provider)
        ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ answer.val.assignment

omit profile declared in
/-- Typed root selection agrees with the checked invocation-sort guard for
all first-order roots, including a variable at the root. The raw matcher still
exposes its own matches and original store layout. -/
theorem guarded_root_matches (facts : FirstOrderProfileFacts language provider)
    {index : Nat} {rule : RewriteRule}
    (declared : (environment language provider).language.rewrites[index]? = some rule)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sourceShape : FirstOrder source)
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) :
    List.Forall₂ (fun answer initial =>
      QueryInvariant language provider rule bound rule.left.freeFvarNames answer.val.assignment initial ∧
      BindingAgreement rule.left.freeFvarNames answer.val.assignment initial ∧
      GeneralPremise.checkTypedAssignment (environment language provider)
        ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ answer.val.assignment = true ∧
      applyBindings initial rule.left = source)
      (typedRootMatchAnswers language provider index rule bound source)
      (guardedRootMatches language provider rule type source) := by
  have row := facts.rowFacts declared
  cases guard : rootSortGuard language provider rule type with
  | false =>
    have empty : typedRootMatchAnswers language provider index rule bound source = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro answer member typed
      have accepted := row.guard_of_typed_match facts.valid sourceShape sourceTyped.1
        answer.property.matching (GeneralPremise.checkTypedAssignment_sound typed)
      rw [guard] at accepted
      cases accepted
    rw [empty, guardedRootMatches_rejected guard]
    exact .nil
  | true =>
    rw [guardedRootMatches_accepted guard]
    have base := root_matches_of_capturesTyped (index := index) row.left row.unique
      (fun initial member => matching_captures_typed_of_rootSortGuard facts.valid row.left guard
        sourceTyped (matchPattern_sound member))
    have kept := List.rel_filter (p := fun answer =>
        GeneralPremise.checkTypedAssignment (environment language provider)
          ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ answer.val.assignment)
      (q := fun _ => true)
      (fun _ _ related => by simpa only [Bool.coe_true, iff_true] using related.2.1) base
    simp only [List.filter_true] at kept
    exact kept.imp fun answer initial related =>
      ⟨related.1, related.1.bindingAgreement
        (matching_unique_names row.left answer.property.matching (by simp)).1,
        related.2.1, related.2.2⟩

/-- The actual root match lists agree at the declared binding observer;
both raw stores retain their own unique-key layouts. -/
theorem root_matches_bindingAgreement {type : TypeExpr} {source : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) :
    List.Forall₂ (fun answer initial =>
      QueryInvariant language provider rule bound rule.left.freeFvarNames answer.val.assignment initial ∧
      BindingAgreement rule.left.freeFvarNames answer.val.assignment initial ∧
      GeneralPremise.checkTypedAssignment (environment language provider)
        ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ answer.val.assignment = true ∧
      applyBindings initial rule.left = source)
      (GeneralScopedMatchMachine.emits (rootMatchRequest rule bound source)
        (GeneralScopedMatchMachine.start (rootMatchRequest rule bound source)) .start 0)
      (matchPattern rule.left source) := by
  exact (root_matches profile declared sourceTyped).imp fun answer initial related =>
    ⟨related.1, related.1.bindingAgreement
      (matching_unique_names (profile.firstOrder.rows declared).left answer.property.matching (by simp)).1,
      related.2.1, related.2.2⟩

/-- Full root correspondence keeps both unique-key stores, their exact
bound-name domains, all lookups, the chosen query rows and the rule ordinal. -/
structure RootRunAgreement (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (index : Nat) (raw : RootReadout) (run : RecordedRootRun) : Prop where
  ordinal : raw.ordinal = index
  captured : BindingAgreement rule.left.freeFvarNames raw.captured run.initial
  completed : BindingAgreement
    (GeneralPremise.premisesFlow (environment language provider).language
      (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
      rule.left.freeFvarNames rule.premises).available raw.completed run.completed.bindings
  history : QueryHistoryAgreement provider rule raw.history run.completed.queries
  localTarget : raw.localTarget = run.target
  target : raw.target = run.target

end RuleFirings

section RootFinish

variable (profile : QueryProfileFacts language provider) {index : Nat} {rule : RewriteRule}
  (declared : (environment language provider).language.rewrites[index]? = some rule)
  {bound : List TypeExpr}

include profile declared

/-- **The reduct.** From corresponding final states, a completed root body
fires once, and its reduct is the canonical one. -/
theorem rootFinish_targets {type : TypeExpr} {source : Pattern}
    (rightTyped : HasType (environment language provider).language
      (FreeTypeContext.ofList rule.typeContext) [] rule.right type)
    (sorted : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment}
    (matched : GeneralScopedMatchMachine.TracedMatches rule (GeneralRuleBindingInference.inferredSpec rule)
      bound.length .left [] 0 [] rule.left source trace captured)
    (capturedTyped : GeneralPremise.TypedAssignment (environment language provider)
      ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ captured)
    (result : GeneralPremise.Execution.Result (environment language provider)
      (.premises ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩
        rule.premises captured))
    {final : Bindings}
    (state : QueryInvariant language provider rule bound
      (GeneralPremise.premisesFlow (environment language provider).language
        (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
        rule.left.freeFvarNames rule.premises).available
      (GeneralPremise.Execution.Result.continues result) final) :
    (GeneralPremise.Execution.rootFinish (environment language provider) declared
        (profile.firstOrder.rowFacts declared).specified (profile.firstOrder.rowFacts declared).admitted sorted
        matched capturedTyped result).map GeneralPremise.Execution.Result.target =
      [applyBindings final rule.right] := by
  have row := profile.firstOrder.rowFacts declared
  have flow := row.flow
  simp only [GeneralPremise.rulePremisesAdmitted, Bool.and_eq_true] at flow
  obtain ⟨_, rhsAvailable⟩ := flow
  cases result with
  | premises completed events held =>
    change QueryInvariant language provider rule bound _ completed final at state
    have rhsBound : GeneralPremise.BoundNames completed rule.right.freeFvarNames := fun name member =>
      state.bound name (GeneralPremise.namesAvailable_sound _ _ rhsAvailable name member)
    have rhsDefined : Defined final rule.right.freeFvarNames := compatible_defined state.compatible rhsBound
    have completedRoots : GeneralPremise.RootValues bound.length completed :=
      state.compatible.rootValues state.typed
    obtain ⟨reductTarget, reductRead⟩ := instantiation_total
      (operation := ScopedReflectiveExecution.binderOperation (environment language provider).reflection rule)
      row.right (NameCoherent.right rule) rhsBound completedRoots
      (dependencies_of_typed row.unique rhsDefined state.typed)
    have reductSame : reductTarget = applyBindings final rule.right := by
      rw [← instantiation_readout row.right completedRoots reductRead,
        compatible_apply_eq state.compatible row.right rhsBound]
    have targetTyped : OpenPatternWellSorted (environment language provider).language
        (environment language provider).free bound type reductTarget := by
      rw [reductSame]
      exact substituted_open row.right rightTyped rhsDefined state.typed
    simp only [GeneralPremise.Execution.rootFinish]
    split
    next missing => cases missing.symm.trans reductRead
    next target converted =>
      cases converted.symm.trans reductRead
      rw [dif_pos (checkOpenPatternWellSorted_complete targetTyped)]
      simp [GeneralPremise.Execution.Result.target, reductSame]


/-- A finished actual premise execution emits one complete corresponding
root occurrence, with its original stores and selected row history. -/
theorem rootFinish_recorded {type : TypeExpr} {source : Pattern}
    (rightTyped : HasType (environment language provider).language
      (FreeTypeContext.ofList rule.typeContext) [] rule.right type)
    (sorted : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment}
    (matched : GeneralScopedMatchMachine.TracedMatches rule (GeneralRuleBindingInference.inferredSpec rule)
      bound.length .left [] 0 [] rule.left source trace captured)
    (capturedTyped : GeneralPremise.TypedAssignment (environment language provider)
      ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ captured)
    (result : GeneralPremise.Execution.Result (environment language provider)
      (.premises ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩
        rule.premises captured)) (initial : Bindings) (run : RecordedPremiseRun)
    (capturedAgreement : BindingAgreement rule.left.freeFvarNames captured initial)
    (state : QueryInvariant language provider rule bound
      (GeneralPremise.premisesFlow (environment language provider).language
        (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
        rule.left.freeFvarNames rule.premises).available
      (GeneralPremise.Execution.Result.continues result) run.bindings)
    (history : QueryHistoryAgreement provider rule (premiseHistory result) run.queries) :
    List.Forall₂ (RootRunAgreement language provider rule index)
      ((GeneralPremise.Execution.rootFinish (environment language provider) declared
        (profile.firstOrder.rowFacts declared).specified (profile.firstOrder.rowFacts declared).admitted sorted
        matched capturedTyped result).map rootReadout)
      [⟨initial, run, applyBindings run.bindings rule.right⟩] := by
  have targets := rootFinish_targets profile declared rightTyped sorted matched capturedTyped result state
  have eachSupported := (profile.firstOrder.rowFacts declared).premises
  cases result with
  | premises completed events held =>
    have completedAgreement := state.bindingAgreement
      (supported_premises_unique eachSupported held capturedAgreement.scopedUnique)
    simp only [GeneralPremise.Execution.rootFinish] at targets ⊢
    split at targets
    next missing => simp at targets
    next target converted =>
      split at targets
      next checked =>
        have same : target = applyBindings run.bindings rule.right := by
          simpa only [List.map_singleton, GeneralPremise.Execution.Result.target,
            List.singleton_inj] using targets
        rw [dif_pos checked]
        exact .cons ⟨rfl, capturedAgreement, completedAgreement, history, same, same⟩ .nil
      next unchecked => simp at targets

/-- The actual root firing list agrees occurrence by occurrence with the
independently recorded canonical root fold, keeping initial and final binding
observers and selected row provenance. -/
theorem root_recorded_occurrences_of_match_readouts {type : TypeExpr} {source : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    (matchReadouts : List.Forall₂ (fun answer initial =>
      QueryInvariant language provider rule bound rule.left.freeFvarNames answer.val.assignment initial ∧
      BindingAgreement rule.left.freeFvarNames answer.val.assignment initial ∧
      GeneralPremise.checkTypedAssignment (environment language provider)
        ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ answer.val.assignment = true ∧
      applyBindings initial rule.left = source)
      (GeneralScopedMatchMachine.emits (rootMatchRequest rule bound source)
        (GeneralScopedMatchMachine.start (rootMatchRequest rule bound source)) .start 0)
      (matchPattern rule.left source))
    (rightTyped : ∀ initial, applyBindings initial rule.left = source →
      HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) [] rule.right type) :
    List.Forall₂ (RootRunAgreement language provider rule index)
      ((GeneralPremise.Execution.results (environment language provider)
        (.root bound type source index)).map rootReadout)
      (recordedRootRuns (providerRelEnv provider) language rule source) := by
  have row := profile.firstOrder.rowFacts declared
  have flow := row.flow
  simp only [GeneralPremise.rulePremisesAdmitted, Bool.and_eq_true] at flow
  rw [GeneralPremise.Execution.results]
  split
  next missing => cases missing.symm.trans declared
  next rule' declared' =>
    obtain rfl : rule = rule' := Option.some.inj (declared.symm.trans declared')
    split
    next missing => cases missing.symm.trans row.specified
    next spec specified =>
      obtain rfl : spec = GeneralRuleBindingInference.inferredSpec rule :=
        Option.some.inj (specified.symm.trans row.specified)
      rw [dif_pos row.admitted, dif_pos (checkOpenPatternWellSorted_complete sourceTyped)]
      simp only [recordedRootRuns, List.map_flatMap]
      apply forall₂_flatMap matchReadouts
      rintro answer initial ⟨state, captureAgreement, typed, leftSource⟩
      have typedRight := rightTyped initial leftSource
      rw [dif_pos typed, List.map_flatMap]
      conv_rhs => rw [List.map_eq_flatMap]
      apply forall₂_flatMap
        (premises_recorded_occurrences profile declared rule.premises 0
          (fun offset premise selected => by simpa using selected) flow.1 state)
      intro result run related
      exact rootFinish_recorded profile declared typedRight sourceTyped _ _ result initial run
        captureAgreement related.1 related.2

/-- Checked invocation-sort selection connects arbitrary first-order root
patterns, including wildcard roots, to the same independently recorded fold. -/
theorem guarded_root_recorded_occurrences {type : TypeExpr} {source : Pattern}
    (sourceShape : FirstOrder source)
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) :
    List.Forall₂ (RootRunAgreement language provider rule index)
      ((GeneralPremise.Execution.results (environment language provider)
        (.root bound type source index)).map rootReadout)
      (recordedGuardedRootRuns (providerRelEnv provider) language provider rule type source) := by
  have row := profile.firstOrder.rowFacts declared
  cases guard : rootSortGuard language provider rule type with
  | false =>
    rw [root_results_eq_nil_of_rootSortGuard_false row profile.firstOrder.valid declared sourceShape guard]
    simp only [recordedGuardedRootRuns, guard, Bool.false_eq_true, ↓reduceIte, List.map_nil]
    exact .nil
  | true =>
    simp only [recordedGuardedRootRuns, guard, ↓reduceIte]
    apply root_recorded_occurrences_of_match_readouts profile declared sourceTyped
    · have matchReadouts := root_matches_of_capturesTyped (index := index) row.left row.unique
        (fun initial member => matching_captures_typed_of_rootSortGuard profile.firstOrder.valid
          row.left guard sourceTyped (matchPattern_sound member))
      exact matchReadouts.imp fun answer initial related =>
        ⟨related.1, related.1.bindingAgreement
          (matching_unique_names row.left answer.property.matching (by simp)).1,
          related.2.1, related.2.2⟩
    · intro _ _
      exact (rootSortGuard_sound guard).2

end RootFinish

section RuleFirings

variable (profile : QueryProfile language provider) {index : Nat} {rule : RewriteRule}
  (declared : (environment language provider).language.rewrites[index]? = some rule)
  {bound : List TypeExpr}

include profile declared

/-- The legacy headed profile retains its unguarded canonical root fold. -/
theorem root_recorded_occurrences {type : TypeExpr} {source : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) :
    List.Forall₂ (RootRunAgreement language provider rule index)
      ((GeneralPremise.Execution.results (environment language provider)
        (.root bound type source index)).map rootReadout)
      (recordedRootRuns (providerRelEnv provider) language rule source) := by
  apply root_recorded_occurrences_of_match_readouts profile.toFacts declared sourceTyped
    (root_matches_bindingAgreement profile declared sourceTyped)
  intro initial leftSource
  have row := profile.firstOrder.rows declared
  obtain ⟨label, arguments, headed⟩ := row.headed
  obtain ⟨ruleType, leftTyped, rightTyped⟩ := row.typed
  have sameType : ruleType = type := by
    have sourceHas := sourceTyped.1
    rw [← leftSource, headed] at sourceHas
    rw [headed] at leftTyped
    simp only [applyBindings] at sourceHas
    exact apply_types_agree profile.firstOrder.valid leftTyped sourceHas
  subst sameType
  exact rightTyped

open MeTTaIL.ReflectiveCanonical MeTTaIL.ReflectiveSubstitution in
/-- **The firings of one rule, in order.** For a rule of the query profile and
a well-sorted source, the reducts of the general root firings are the canonical
reducts of the rule, one for one and in order. -/
theorem root_targets {type : TypeExpr} {source : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    {authored : RewriteRule} (authoredDeclared : language.rewrites[index]? = some authored)
    (recursiveStep : Pattern → List Pattern) :
    (GeneralPremise.Execution.results (environment language provider)
        (.root bound type source index)).map GeneralPremise.Execution.Result.target =
      applyRuleUsing (engineBasePremises (providerRelEnv provider)) language recursiveStep authored
        source := by
  have row := profile.firstOrder.rows declared
  obtain ⟨authored', authoredDeclared', core⟩ := profile.firstOrder.authored declared
  obtain rfl : authored = authored' := Option.some.inj (authoredDeclared.symm.trans authoredDeclared')
  simp only [ruleCore, Prod.mk.injEq] at core
  obtain ⟨leftCore, rightCore, premisesCore⟩ := core
  have aligned : ruleDepthAligned authored = true := by
    simpa only [ruleDepthAligned, leftCore, rightCore] using row.aligned
  obtain ⟨label, arguments, headed⟩ := row.headed
  obtain ⟨ruleType, leftTyped, rightTyped⟩ := row.typed
  have flow := row.flow
  simp only [GeneralPremise.rulePremisesAdmitted, Bool.and_eq_true] at flow
  obtain ⟨supported, _⟩ := flow
  rw [GeneralPremise.Execution.results]
  split
  next missing => cases missing.symm.trans declared
  next rule' declared' =>
    obtain rfl : rule = rule' := Option.some.inj (declared.symm.trans declared')
    split
    next missing => cases missing.symm.trans row.specified
    next spec specified =>
      obtain rfl : spec = GeneralRuleBindingInference.inferredSpec rule :=
        Option.some.inj (specified.symm.trans row.specified)
      rw [dif_pos row.admitted, dif_pos (checkOpenPatternWellSorted_complete sourceTyped)]
      simp only [applyRuleUsing, matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations
        (rfl : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty.presentations = []), leftCore,
        premisesCore, applyBindingsForRule, applyBindingsForRuleUsing_empty_eq_applyBindings _ _ aligned,
        rightCore, List.map_flatMap]
      apply flatMap_eq_of_forall₂ (root_matches profile declared sourceTyped)
      rintro answer initial ⟨state, typed, leftSource⟩
      have sameType : ruleType = type := by
        have sourceHas := sourceTyped.1
        rw [← leftSource, headed] at sourceHas
        rw [headed] at leftTyped
        simp only [applyBindings] at sourceHas
        exact apply_types_agree profile.firstOrder.valid leftTyped sourceHas
      subst sameType
      rw [dif_pos typed, List.map_flatMap, List.map_eq_flatMap]
      apply flatMap_eq_of_forall₂ (premises_occurrences profile declared recursiveStep rule.premises 0
        (fun offset premise selected => by simpa using selected) supported state)
      intro result final related
      exact rootFinish_targets profile declared rightTyped _ _ _ result related

end RuleFirings

theorem filterMap_map_of_some {α β γ : Type} {f : α → Option β} {h : β → γ} {k : α → γ} :
    ∀ {items : List α}, (∀ item ∈ items, (f item).map h = some (k item)) →
      (items.filterMap f).map h = items.map k
  | [], _ => rfl
  | item :: items, each => by
    have head := each item (List.mem_cons_self ..)
    cases found : f item with
    | none =>
      rw [found] at head
      cases head
    | some value =>
      rw [found, Option.map_some, Option.some.injEq] at head
      rw [List.filterMap_cons, found, List.map_cons, List.map_cons, head,
        filterMap_map_of_some (fun other member => each other (List.mem_cons_of_mem _ member))]

/-- At the root site, receipt formation preserves the complete raw occurrence:
rule ordinal, matcher trace, both stores, history and both target fields. -/
theorem root_receipt_readouts (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (site : request.job.site = .here request.bound request.expected request.source) :
    ((GeneralRuleJobExecution.finishState request licensed).answers.map Subtype.val).map
        receiptReadout =
      (GeneralPremise.Execution.results request.environment
        (.root request.bound request.expected request.source request.job.ordinal)).map
          rootReadout := by
  obtain ⟨plan, bound, expected, source, ⟨ordinal, declaration, siteData⟩⟩ := request
  dsimp only at site licensed ⊢
  subst site
  rw [GeneralRuleJobExecution.finishState_root_readouts, GeneralPremise.Execution.treeStart_answers,
    List.map_map]
  apply filterMap_map_of_some
  intro result _
  cases result with
  | root trace captured completed history target valid =>
    have sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
        (GeneralPlanEnvironment.environment plan).free bound expected target := by
      cases valid with
      | fire _ _ _ _ _ _ _ _ sorted => exact sorted
    have represented : (GeneralTypedSites.SiteData.here bound expected source).acceptsReplacementRepresentation
        (GeneralPlanEnvironment.environment plan).language target = true := rfl
    have filled : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
        (GeneralPlanEnvironment.environment plan).free bound expected
        ((GeneralTypedSites.SiteData.here bound expected source).context.fill target) = true :=
      checkOpenPatternWellSorted_complete sorted
    show Option.map (receiptReadout ∘ Subtype.val)
      (GeneralRuleJobExecution.finishRoot
        ⟨plan, bound, expected, source, ⟨ordinal, declaration, .here bound expected source⟩⟩ licensed
        trace captured completed history target valid) = some (rootReadout (.root trace captured completed history target valid))
    unfold GeneralRuleJobExecution.finishRoot
    simp only [GeneralRuleJobExecution.Request.environment, represented, filled, ↓reduceDIte,
      Option.map_some]
    rfl


/-- **At the root site, every root firing is a receipt with the same reduct.** -/
theorem root_receipt_targets (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (site : request.job.site = .here request.bound request.expected request.source) :
    ((GeneralRuleJobExecution.finishState request licensed).answers.map Subtype.val).map
        GeneralRuleJobs.Receipt.target =
      (GeneralPremise.Execution.results request.environment
        (.root request.bound request.expected request.source request.job.ordinal)).map
          GeneralPremise.Execution.Result.target := by
  have same := congrArg (List.map RootReadout.target) (root_receipt_readouts request licensed site)
  simp only [List.map_map] at same
  have actual : (RootReadout.target ∘ rootReadout) =
      (GeneralPremise.Execution.Result.target :
        GeneralPremise.Execution.Result request.environment
          (.root request.bound request.expected request.source request.job.ordinal) → Pattern) := by
    funext result
    cases result
    rfl
  simpa only [actual, Function.comp_def, receiptReadout, List.map_map] using same

/-- Complete receipts of one selected root job carry the recorded canonical
occurrences, including initial/final bindings and selected provider rows. -/
theorem root_receipt_recorded_occurrences (profile : QueryProfile language provider)
    (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (plan : request.plan = rootPlan language provider)
    (site : request.job.site = .here request.bound request.expected request.source)
    {rule : RewriteRule}
    (declared : (environment language provider).language.rewrites[request.job.ordinal]? = some rule)
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free request.bound request.expected request.source) :
    List.Forall₂ (RootRunAgreement language provider rule request.job.ordinal)
      (((GeneralRuleJobExecution.finishState request licensed).answers.map Subtype.val).map receiptReadout)
      (recordedRootRuns (providerRelEnv provider) language rule request.source) := by
  rw [root_receipt_readouts request licensed site]
  have sameEnvironment : request.environment = environment language provider := by
    simp only [GeneralRuleJobExecution.Request.environment, plan, environment]
  rw [sameEnvironment]
  exact root_recorded_occurrences profile declared sourceTyped

/-- The original rule ordinal selects the executed typed row; the recorded
run itself is enumerated by the original authored language. -/
def RuleRunAgreement (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (raw : RootReadout) (recorded : RecordedRuleRun) : Prop :=
  ∃ rule, (environment language provider).language.rewrites[recorded.ordinal]? = some rule ∧
    RootRunAgreement language provider rule recorded.ordinal raw recorded.run

theorem flatMap_attach_val {α β : Type} (items : List α) (f : α → List β) :
    items.attach.flatMap (fun item => f item.val) = items.flatMap f := by
  rw [← List.flatMap_map Subtype.val f items.attach, List.attach_map_subtype_val]

/-- Root-site receipt formation preserves the full ordered raw root results
before any comparison with another semantics. -/
theorem completedReceipts_root_readouts {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) :
    (GeneralRuleJobExecution.completedReceipts (rootPlan language provider) bound type source).map receiptReadout =
      (rootPlan language provider).rules.zipIdx.flatMap fun entry =>
        (GeneralPremise.Execution.results (environment language provider)
          (.root bound type source entry.2)).map rootReadout := by
  have checked : checkHasType (environment language provider).language
      (environment language provider).free bound source type = true :=
    checkHasType_complete_of_object sourceTyped.1 sourceTyped.2.2.1
  have jobsEq : GeneralRuleJobs.jobs (rootPlan language provider) bound type source =
      (rootPlan language provider).rules.zipIdx.map fun entry =>
        ⟨entry.2, entry.1, GeneralTypedSites.SiteData.here bound type source⟩ := by
    simp only [GeneralRuleJobs.jobs]
    rw [show (rootPlan language provider).permissions.sites = .rootOnly from rfl, GeneralTypedSites.generate_rootOnly,
      if_pos ⟨sourceTyped.2.2.1, checked⟩, List.map_eq_flatMap]
    rfl
  have sites : ∀ job ∈ GeneralRuleJobs.jobs (rootPlan language provider) bound type source,
      job.site = .here bound type source := by
    intro job member
    rw [jobsEq] at member
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    rfl
  unfold GeneralRuleJobExecution.completedReceipts
  rw [List.map_flatMap]
  rw [List.flatMap_congr (g := fun item =>
      (GeneralPremise.Execution.results (environment language provider)
        (.root bound type source item.val.ordinal)).map rootReadout)
    (fun item _ => root_receipt_readouts _ _ (sites item.val item.property))]
  rw [flatMap_attach_val (GeneralRuleJobs.jobs (rootPlan language provider) bound type source)
      (fun job => (GeneralPremise.Execution.results (environment language provider)
        (.root bound type source job.ordinal)).map rootReadout), jobsEq, List.flatMap_map]

/-- The common checked profile preserves every authored rule ordinal. -/
theorem root_rows_authored_order (facts : FirstOrderProfileFacts language provider) :
    List.Forall₂ (fun entry authored =>
      (environment language provider).language.rewrites[entry.2]? = some entry.1.rule ∧
        language.rewrites[authored.2]? = some authored.1 ∧ entry.2 = authored.2)
      (rootPlan language provider).rules.zipIdx language.rewrites.zipIdx := by
  rw [List.forall₂_iff_get]
  have lengths := congrArg List.length facts.sameRules
  simp only [List.length_map] at lengths
  refine ⟨?_, ?_⟩
  · simpa [environment, GeneralPlanEnvironment.environment] using lengths
  · intro position firstBound secondBound
    simp only [List.get_eq_getElem, List.getElem_zipIdx, Nat.zero_add]
    refine ⟨?_, List.getElem?_eq_getElem (by simpa using secondBound), True.intro⟩
    show ((rootPlan language provider).rules.map GeneralExecutionAdmission.RulePlan.rule)[position]? = _
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using firstBound)]
    rfl

section RootPlan

open MeTTaIL.GeneralTypedSites

variable (profile : QueryProfile language provider)

include profile

/-- **The root plan reads out the canonical reducts, in order.** For a language
of the query profile and a well-sorted source, the reducts of the completed
receipts of the root plan are the canonical reducts over the provider's own
relation environment, one for one and in order, equal reducts included. -/
theorem completedReceipts_targets {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) (fuel : Nat) :
    (GeneralRuleJobExecution.completedReceipts (rootPlan language provider) bound type source).map
        GeneralRuleJobs.Receipt.target =
      reductsUsing (providerRelEnv provider) language (fuel + 1) source := by
  have checked : checkHasType (environment language provider).language
      (environment language provider).free bound source type = true :=
    checkHasType_complete_of_object sourceTyped.1 sourceTyped.2.2.1
  have jobsEq : GeneralRuleJobs.jobs (rootPlan language provider) bound type source =
      (rootPlan language provider).rules.zipIdx.map fun entry =>
        ⟨entry.2, entry.1, SiteData.here bound type source⟩ := by
    simp only [GeneralRuleJobs.jobs]
    rw [show (rootPlan language provider).permissions.sites = .rootOnly from rfl, generate_rootOnly,
      if_pos ⟨sourceTyped.2.2.1, checked⟩, List.map_eq_flatMap]
    rfl
  have sites : ∀ job ∈ GeneralRuleJobs.jobs (rootPlan language provider) bound type source,
      job.site = .here bound type source := by
    intro job member
    rw [jobsEq] at member
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    rfl
  unfold GeneralRuleJobExecution.completedReceipts
  rw [List.map_flatMap]
  rw [List.flatMap_congr (g := fun item =>
      (GeneralPremise.Execution.results (environment language provider)
        (.root bound type source item.val.ordinal)).map GeneralPremise.Execution.Result.target)
    (fun item _ => root_receipt_targets _ _ (sites item.val item.property))]
  rw [flatMap_attach_val (GeneralRuleJobs.jobs (rootPlan language provider) bound type source)
      (fun job => (GeneralPremise.Execution.results (environment language provider)
        (.root bound type source job.ordinal)).map GeneralPremise.Execution.Result.target),
    jobsEq, List.flatMap_map]
  simp only [reductsUsing, rewriteAt]
  apply flatMap_eq_of_forall₂ (R := fun entry authored =>
    (environment language provider).language.rewrites[entry.2]? = some entry.1.rule ∧
      language.rewrites[entry.2]? = some authored)
  · rw [List.forall₂_iff_get]
    have lengths := congrArg List.length profile.firstOrder.sameRules
    simp only [List.length_map] at lengths
    refine ⟨?_, ?_⟩
    · simpa [environment, GeneralPlanEnvironment.environment] using lengths
    · intro position firstBound secondBound
      simp only [List.get_eq_getElem, List.getElem_zipIdx, Nat.zero_add]
      refine ⟨?_, List.getElem?_eq_getElem secondBound⟩
      show ((rootPlan language provider).rules.map GeneralExecutionAdmission.RulePlan.rule)[position]? = _
      rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using firstBound)]
      rfl
  · rintro ⟨declaration, position⟩ authored ⟨declared, authoredDeclared⟩
    exact root_targets profile declared sourceTyped authoredDeclared _

/-- All completed root receipts correspond to the original canonical rule
and query occurrences, one for one and in order. Raw binding layouts and
histories remain available on the receipt side. -/
theorem completedReceipts_recorded_occurrences {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) :
    List.Forall₂ (RuleRunAgreement language provider)
      ((GeneralRuleJobExecution.completedReceipts (rootPlan language provider) bound type source).map receiptReadout)
      (recordedRootOccurrences (providerRelEnv provider) language source) := by
  rw [completedReceipts_root_readouts sourceTyped]
  simp only [recordedRootOccurrences]
  apply forall₂_flatMap (root_rows_authored_order profile.firstOrder)
  rintro ⟨declaration, position⟩ ⟨authored, authoredPosition⟩ ⟨declared, authoredDeclared, rfl⟩
  obtain ⟨authored', selected, core⟩ := profile.firstOrder.authored declared
  obtain rfl : authored = authored' := Option.some.inj (authoredDeclared.symm.trans selected)
  rw [recordedRootRuns_eq_of_ruleCore _ _ core source, List.forall₂_map_right_iff]
  exact (root_recorded_occurrences profile declared sourceTyped).imp fun raw run related =>
    ⟨declaration.rule, declared, related⟩


omit profile in
/-- Complete receipts preserve the original rule/query occurrences for the
broader checked first-order region. Invocation-sort refusal is an empty
candidate at its original index, including for a wildcard root. -/
theorem completedReceipts_guarded_recorded_occurrences
    (facts : QueryProfileFacts language provider) {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} (sourceShape : FirstOrder source)
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source) :
    List.Forall₂ (RuleRunAgreement language provider)
      ((GeneralRuleJobExecution.completedReceipts (rootPlan language provider) bound type source).map receiptReadout)
      (recordedGuardedRootOccurrences (providerRelEnv provider) language provider type source) := by
  rw [completedReceipts_root_readouts sourceTyped]
  simp only [recordedGuardedRootOccurrences]
  apply forall₂_flatMap (root_rows_authored_order facts.firstOrder)
  rintro ⟨declaration, position⟩ ⟨authored, authoredPosition⟩ ⟨declared, authoredDeclared, rfl⟩
  obtain ⟨authored', selected, core⟩ := facts.firstOrder.authored declared
  obtain rfl : authored = authored' := Option.some.inj (authoredDeclared.symm.trans selected)
  have sameRuns : (if rootInvocationGuard language provider type position then
      recordedRootRuns (providerRelEnv provider) language authored source else []) =
      recordedGuardedRootRuns (providerRelEnv provider) language provider declaration.rule type source := by
    simp only [rootInvocationGuard, declared, recordedGuardedRootRuns]
    split
    · exact recordedRootRuns_eq_of_ruleCore _ _ core source
    · rfl
  rw [sameRuns, List.forall₂_map_right_iff]
  exact (guarded_root_recorded_occurrences facts declared sourceShape sourceTyped).imp fun raw run related =>
    ⟨declaration.rule, declared, related⟩

end RootPlan

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
