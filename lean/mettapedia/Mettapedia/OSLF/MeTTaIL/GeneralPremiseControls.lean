import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionTermination
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaTyping
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFlow

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

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Controls
