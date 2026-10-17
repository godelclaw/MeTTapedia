import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionTermination
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaTyping
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFlow
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticFlow
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryTotality
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryOrder

/-!
# Executed structural queries, freshness, quantification and scoped children

One authored parent rule uses all four premise forms. Its finite collection
contains the same element twice, and its directed child fires inside a typed
name binder. The query schema includes an explicit substitution. Controls
read only actual machine outputs and retained continuation work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Controls

open Syntax RuleBinding ScopedRuleMatching Execution
open Mettapedia.GSLT.LanguageDef.WellSorted

def term : TypeExpr := .base "Term"
def name : TypeExpr := .base "Name"
def zero : Pattern := .apply "Zero" []

def child : RewriteRule where
  name := "unwrap-successor"
  typeContext := [("X", term)]
  left := .apply "Successor" [.fvar "X"]
  right := .fvar "X"
  premises := []

def parent : RewriteRule where
  name := "guarded-parent"
  typeContext := [("X", term), ("A", name),
    ("L", .collection .vec term), ("element", term), ("Y", term)]
  left := .apply "Wrap" [.fvar "X", .fvar "A", .fvar "L"]
  right := .apply "Accept" [.fvar "Y"]
  premises := [
    .relationQuery "seen" [.subst (.fvar "X") (.fvar "A")],
    .freshness ⟨"A", .fvar "X"⟩,
    .forAll "L" "element" (.relationQuery "seen" [.fvar "element"]),
    .scopedStep ⟨[name], term, .apply "Successor" [.fvar "X"], .fvar "Y"⟩]

def language : LanguageDef where
  name := "ordered-guarded-scoped-premises"
  types := ["Term", "Name"]
  terms := [
    {label := "Zero", category := "Term", params := [], syntaxPattern := []},
    {label := "Successor", category := "Term", params := [.simple "term" term], syntaxPattern := []},
    {label := "Wrap", category := "Term",
      params := [.simple "term" term, .simple "name" name,
        .simple "elements" (.collection .vec term)], syntaxPattern := []},
    {label := "Accept", category := "Term", params := [.simple "term" term], syntaxPattern := []}]
  equations := []
  rewrites := [child, parent]

def provider : ProviderSnapshot where
  signatures := [⟨"seen", [term], [.input]⟩]
  rows := [⟨"seen", [zero]⟩]

def environment : Environment where
  language := language
  free := fun atomName => if atomName == "a" then some name else none
  provider := provider
  specifications := [(0, GeneralRuleBindingInference.inferredSpec child),
    (1, GeneralRuleBindingInference.inferredSpec parent)]

def source (elements : List Pattern) : Pattern :=
  .apply "Wrap" [zero, .fvar "a", .collection .vec elements none]

def goal (elements : List Pattern) : Goal := .root [] term (source elements) 1

def completed (elements : List Pattern) : State environment (goal elements) :=
  run environment (goal elements) 160 (start environment (goal elements))

def targetReadout (elements : List Pattern) : Result environment (goal elements) → Pattern
  | .root _ _ _ _ target _ => target

def eventKind : Event → Nat
  | .query _ _ _ _ => 0
  | .freshness _ _ _ _ => 1
  | .quantified _ _ _ _ => 2
  | .child _ _ _ _ _ _ _ _ _ _ _ => 3

def eventKinds (elements : List Pattern) : Result environment (goal elements) → List Nat
  | .root _ _ _ events _ _ => events.map eventKind

def quantifiedIndices : Event → List Nat
  | .quantified _ _ _ elements => elements.map fun entry => entry.1
  | _ => []

def quantifierReadout (elements : List Pattern) : Result environment (goal elements) → List Nat
  | .root _ _ _ events _ _ => events.flatMap quantifiedIndices

def scopedChildReadout : Event → List (Nat × List TypeExpr × Pattern × Pattern)
  | .child _ _ index bound source target _ _ _ _ _ => [(index, bound, source, target)]
  | _ => []

def childReadout (elements : List Pattern) : Result environment (goal elements) →
    List (Nat × List TypeExpr × Pattern × Pattern)
  | .root _ _ _ events _ _ => events.flatMap scopedChildReadout

theorem profile_admitted :
    checkProviderClosed language environment.free provider = true ∧
    rulePremisesAdmitted language provider parent (GeneralRuleBindingInference.inferredSpec parent) = true ∧
    checkStepStratification language = true := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  simp [rulePremisesAdmitted, parent, premisesFlow, premiseFlow,
    Pattern.freeFvarNames, provider, signature?, queryInputNames, queryOutputNames,
    namesAvailable, schemaValuesChecked, lookupRuleType?, sourceType?, collectionElement?,
    GeneralRuleBindingInference.inferredSpec, dependencies?, term, name, language,
    SchemaTyping.checkSchemaType, SchemaTyping.checkSchemaArguments,
    SchemaTyping.declaredDomains,
    SchemaTyping.typeVocabulary, parameterType?, usesBareCollection?,
    matchesParameterRepresentation?]

theorem nested_substitution_admitted :
    schemaValuesChecked language parent [] [.subst (.fvar "X") (.fvar "A")] [term] = true := by
  decide +kernel

theorem completed_target :
    (completed [zero, zero]).answers.map (targetReadout [zero, zero]) =
      [.apply "Accept" [zero]] := by decide +kernel

theorem completed_all_premise_forms :
    (completed [zero, zero]).answers.map (eventKinds [zero, zero]) = [[0, 1, 2, 3]] := by decide +kernel

theorem duplicate_quantified_occurrences_retained :
    (completed [zero, zero]).answers.map (quantifierReadout [zero, zero]) = [[0, 1]] := by decide +kernel

theorem scoped_child_actual_execution :
    (completed [zero, zero]).answers.map (childReadout [zero, zero]) =
      [[(0, [name], .apply "Successor" [zero], zero)]] := by decide +kernel

theorem completed_certified : complete environment (goal [zero, zero]) (completed [zero, zero]) = true := by
  decide +kernel

theorem empty_quantification_executes :
    (completed []).answers.map (targetReadout []) = [.apply "Accept" [zero]] ∧
      (completed []).answers.map (quantifierReadout []) = [[]] := by decide +kernel

theorem unfinished_not_complete :
    (start environment (goal [zero, zero])).answers = [] ∧
      complete environment (goal [zero, zero]) (start environment (goal [zero, zero])) = false := by
  decide +kernel

namespace Dynamic

/-- This source table specification is independent of the service dispatcher. -/
inductive Rows : String → List Pattern → List (List Pattern) → Prop where
  | seen : Rows "seen" [zero] [[zero], [zero]]
  | absent (value : Pattern) : value ≠ zero → Rows "seen" [value] []
  | mirror (value hole : Pattern) : Rows "mirror" [value, hole] [[value, value], [value, value]]
  | empty : Rows "empty" [] []

def nativeRows (relation : String) (arguments : List Pattern) : Option (List (List Pattern)) :=
  if relation = "seen" then
    match arguments with
    | [value] => some (if value == zero then [[value], [value]] else [])
    | _ => none
  else if relation = "mirror" then
    match arguments with
    | [value, _] => some [[value, value], [value, value]]
    | _ => none
  else if relation = "empty" then
    if arguments.isEmpty then some [] else none
  else none

theorem nativeRows_complete {relation : String} {arguments : List Pattern}
    {rows : List (List Pattern)} (source : Rows relation arguments rows) :
    nativeRows relation arguments = some rows := by
  cases source with
  | seen => simp [nativeRows]
  | absent value different => simp [nativeRows, different]
  | mirror value hole => simp [nativeRows]
  | empty => simp [nativeRows]

theorem nativeRows_sound {relation : String} {arguments : List Pattern}
    {rows : List (List Pattern)} (computed : nativeRows relation arguments = some rows) :
    Rows relation arguments rows := by
  unfold nativeRows at computed
  split at computed
  · rename_i selected
    subst relation
    cases arguments with
    | nil => simp at computed
    | cons value rest =>
      cases rest with
      | nil =>
        by_cases present : value = zero
        · subst value
          simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at computed
          subst rows
          exact .seen
        · have result : rows = [] := by simpa [present] using computed.symm
          rw [result]
          exact .absent value present
      | cons _ _ => simp at computed
  · split at computed
    · rename_i selected
      subst relation
      cases arguments with
      | nil => simp at computed
      | cons value rest =>
        cases rest with
        | nil => simp at computed
        | cons hole tail =>
          cases tail with
          | nil =>
            have result : rows = [[value, value], [value, value]] := Option.some.inj computed.symm
            subst rows
            exact .mirror value hole
          | cons _ _ => simp at computed
    · split at computed
      · rename_i selected
        subst relation
        cases arguments with
        | nil =>
            have result : rows = [] := by simpa using computed.symm
            subst rows
            exact .empty
        | cons _ _ => simp at computed
      · contradiction

def service : DynamicProvider where
  Source := Rows
  rows? := nativeRows
  rows_exact := fun _ _ _ => ⟨nativeRows_sound, nativeRows_complete⟩

def guardedChild : RewriteRule := { child with premises := [.relationQuery "seen" [.fvar "X"]] }
def dynamicLanguage : LanguageDef := { language with rewrites := [guardedChild, parent] }
def dynamicProvider : ProviderSnapshot where
  signatures := [⟨"seen", [term], [.input]⟩, ⟨"mirror", [term, term], [.input, .output]⟩,
    ⟨"empty", [], []⟩, ⟨"unavailable", [], []⟩]
  rows := [⟨"mirror", [zero, zero]⟩]
  dynamicRelations := ["seen", "mirror", "empty", "unavailable"]
def dynamicEnvironment : Environment where
  language := dynamicLanguage
  provider := dynamicProvider
  dynamic := service
  free := environment.free
  specifications := [(0, GeneralRuleBindingInference.inferredSpec guardedChild),
    (1, GeneralRuleBindingInference.inferredSpec parent)]
def initial : Assignment := [("X", localValue [] zero)]
def mirrorRule : RewriteRule :=
  { parent with premises := [.relationQuery "mirror" [.fvar "X", .fvar "Y"]] }
def context : Context := ⟨1, mirrorRule, GeneralRuleBindingInference.inferredSpec mirrorRule, [], 0, 0⟩
def mirrorRequest : Query.Request := ⟨context, "mirror", [.fvar "X", .fvar "Y"], initial⟩
def queryState := Query.run dynamicEnvironment mirrorRequest 120 (Query.start dynamicEnvironment mirrorRequest)
def queryReadout (answer : Query.Answer dynamicEnvironment mirrorRequest) :=
  (answer.rowIndex, (lookup answer.assignment "Y").map ContextualValue.body)

#guard queryState.answers.length == 3
#guard queryState.answers.map queryReadout == [(0, some zero), (1, some zero), (2, some zero)]
#guard queryState.unresolved.isEmpty
#guard Query.complete dynamicEnvironment mirrorRequest queryState
#guard (Query.run dynamicEnvironment mirrorRequest 17 (Query.start dynamicEnvironment mirrorRequest)).agenda.length > 0
#guard (Query.run dynamicEnvironment mirrorRequest 103
  (Query.run dynamicEnvironment mirrorRequest 17 (Query.start dynamicEnvironment mirrorRequest))).answers.length == 3

private def emptyRequest : Query.Request := ⟨context, "empty", [], initial⟩
private def emptyState := Query.run dynamicEnvironment emptyRequest 40 (Query.start dynamicEnvironment emptyRequest)
private def unknownRequest : Query.Request := ⟨context, "unavailable", [], initial⟩
private def unknownState := Query.run dynamicEnvironment unknownRequest 40 (Query.start dynamicEnvironment unknownRequest)
#guard emptyState.answers.isEmpty
#guard Query.complete dynamicEnvironment emptyRequest emptyState
#guard unknownState.answers.isEmpty
#guard !(Query.complete dynamicEnvironment unknownRequest unknownState)
#guard unknownState.unresolved == [.dynamicUnavailable "unavailable"]

private def rootState := Execution.run dynamicEnvironment (goal [zero, zero]) 1800
  (Execution.start dynamicEnvironment (goal [zero, zero]))
private def rootTargets : Result dynamicEnvironment (goal [zero, zero]) → Pattern
  | .root _ _ _ _ target _ => target
private def rootKinds : Result dynamicEnvironment (goal [zero, zero]) → List Nat
  | .root _ _ _ history _ _ => history.map eventKind
private def nestedQueries : Event → List Nat
  | .child _ _ _ _ _ _ _ _ _ _ history => history.filterMap fun event =>
      match event with | .query _ _ index _ => some index | _ => none
  | _ => []
private def childQueries : Result dynamicEnvironment (goal [zero, zero]) → List Nat
  | .root _ _ _ history _ _ => history.flatMap nestedQueries

#guard rootState.answers.length == 16
#guard rootState.answers.all fun answer => rootTargets answer == .apply "Accept" [zero]
#guard rootState.answers.all fun answer => rootKinds answer == [0, 1, 2, 3]
#guard rootState.answers.all fun answer => (childQueries answer).length == 1
#guard rootState.unresolved.isEmpty
#guard Execution.complete dynamicEnvironment (goal [zero, zero]) rootState
#guard !(Static.checkProviderRepresentation dynamicProvider "mirror" 0 (fun _ => true))

private def unregisteredEnvironment : Environment :=
  { dynamicEnvironment with provider := { dynamicProvider with dynamicRelations := [] } }
private def unregisteredState := Query.run unregisteredEnvironment mirrorRequest 120
  (Query.start unregisteredEnvironment mirrorRequest)
private def wrongContext : Context :=
  ⟨1, parent, GeneralRuleBindingInference.inferredSpec parent, [], 0, 0⟩
private def wrongRequest : Query.Request := ⟨wrongContext, "mirror", [.fvar "X", .fvar "Y"], initial⟩
private def wrongState := Query.run dynamicEnvironment wrongRequest 120
  (Query.start dynamicEnvironment wrongRequest)
private def rootQuantifiers : Result dynamicEnvironment (goal [zero, zero]) → List Nat
  | .root _ _ _ history _ _ => history.flatMap quantifiedIndices
private def resumedQuery := Query.run dynamicEnvironment mirrorRequest 103
  (Query.run dynamicEnvironment mirrorRequest 17 (Query.start dynamicEnvironment mirrorRequest))

#guard unregisteredState.answers.length == 1
#guard unregisteredState.unresolved.isEmpty
#guard wrongState.answers.isEmpty
#guard !(Query.complete dynamicEnvironment wrongRequest wrongState)
#guard resumedQuery.answers.map queryReadout == queryState.answers.map queryReadout
#guard resumedQuery.unresolved == queryState.unresolved
#guard rootState.answers.all fun answer => rootQuantifiers answer == [0, 1]
#guard rootState.answers.countP (fun answer => childQueries answer == [1]) == 8
#guard rootState.answers.countP (fun answer => childQueries answer == [2]) == 8

theorem mirror_resume_exact :
    Query.run dynamicEnvironment mirrorRequest 120 (Query.start dynamicEnvironment mirrorRequest) =
      Query.run dynamicEnvironment mirrorRequest 103
        (Query.run dynamicEnvironment mirrorRequest 17 (Query.start dynamicEnvironment mirrorRequest)) :=
  Query.run_add dynamicEnvironment mirrorRequest 17 103 _

#print axioms nativeRows_sound
#print axioms nativeRows_complete
#print axioms mirror_resume_exact

end Dynamic


end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Controls

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Controls.Dynamic

open Syntax RuleBinding ScopedRuleMatching Execution
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Actual source object sorts still govern every native row. -/
private def wrongSortRequest : Query.Request :=
  { mirrorRequest with initial := [("X", localValue [] (.fvar "a"))] }
private def wrongSortState := Query.run dynamicEnvironment wrongSortRequest 120
  (Query.start dynamicEnvironment wrongSortRequest)

#guard wrongSortState.answers.isEmpty
#guard wrongSortState.unresolved.isEmpty
#guard Query.complete dynamicEnvironment wrongSortRequest wrongSortState

/-- The closed-result primitive profile retains the existing service code and
independent source relation, while registering only its closed-result methods. -/
def closedEnvironment : Environment :=
  { dynamicEnvironment with provider :=
    { dynamicProvider with dynamicRelations := ["seen", "empty", "unavailable"] } }

theorem closed_output_support : Query.DynamicOutputsFreeWithin [] closedEnvironment := by
  intro relation registered resolved rows source
  cases source with
  | seen =>
      intro values member
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      subst values
      intro value present objectName occurs
      simp only [List.mem_singleton] at present
      subst value
      simp [zero, Pattern.freeFvarNames] at occurs
  | absent => intro values impossible; cases impossible
  | mirror value hole => simp [closedEnvironment, dynamicProvider] at registered
  | empty => intro values impossible; cases impossible

/-- A service that copies arbitrary object values cannot promise an empty
object footprint merely because its output schemas are holes. -/
theorem mirror_requires_input_support : ¬ Query.DynamicOutputsFreeWithin [] dynamicEnvironment := by
  intro covered
  have values := covered "mirror" (by decide) [.fvar "object", .fvar "Y"]
    [[.fvar "object", .fvar "object"], [.fvar "object", .fvar "object"]]
    (.mirror (.fvar "object") (.fvar "Y"))
    [.fvar "object", .fvar "object"] (by simp)
  have impossible := values (.fvar "object") (by simp) "object" (by simp [Pattern.freeFvarNames])
  cases impossible

example : Query.DynamicOutputsFreeWithin []
    { dynamicEnvironment with dynamic := DynamicProvider.empty } :=
  Query.DynamicOutputsFreeWithin.of_empty _ _ rfl

#print axioms closed_output_support
#print axioms mirror_requires_input_support

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Controls.Dynamic
