import Mettapedia.OSLF.MeTTaIL.GeneralOccurrencePaidReadouts
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseControls
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion

/-!
# A compiled authored profile with every supported premise form

The collection is captured at an actual rest occurrence, rather than inferred
finite from its sort. A literal freshness probe, structural substitution,
duplicate query rows, lexical quantification and a directed binder-local child
all run through the selected declarations of the generated environment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralAuthoredExecutionControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open GeneralPremise GeneralPremise.Execution

def term : TypeExpr := .base "Term"
def name : TypeExpr := .base "Name"
def zero : Pattern := .apply "Zero" []

def child : RewriteRule where
  name := "directed-child"
  typeContext := [("X", term)]
  left := .apply "Successor" [.fvar "X"]
  right := .fvar "X"
  premises := []

def parent : RewriteRule where
  name := "ordered-premise-parent"
  typeContext := [("X", term), ("L", .collection .vec term), ("element", term), ("Y", term)]
  left := .apply "Wrap" [.fvar "X", .collection .vec [] (some "L")]
  right := .apply "Accept" [.fvar "Y"]
  premises := [
    .relationQuery "seen" [.subst (.fvar "X") (.fvar "X")],
    .freshness ⟨"probe-atom", .fvar "X"⟩,
    .forAll "L" "element" (.relationQuery "seen" [.fvar "element"]),
    .scopedStep ⟨[name], term, .apply "Successor" [.fvar "X"], .fvar "Y"⟩]

def language : LanguageDef where
  name := "compiled-structural-premises"
  types := ["Term", "Name"]
  terms := [
    {label := "Zero", category := "Term", params := [], syntaxPattern := []},
    {label := "Successor", category := "Term", params := [.simple "term" term], syntaxPattern := []},
    {label := "Wrap", category := "Term", params := [
      .simple "term" term, .simple "elements" (.collection .vec term)], syntaxPattern := []},
    {label := "Accept", category := "Term", params := [.simple "term" term], syntaxPattern := []}]
  equations := []
  rewrites := [child, parent]

def snapshot (rows : List Pattern) : Snapshot :=
  ⟨language, [], {
    signatures := [⟨"seen", [term], [.input]⟩]
    rows := rows.map fun value => ⟨"seen", [value]⟩
    dynamicRelations := [] }⟩

def permissions : Permissions where
  equationIndices := some []
  includeDerivedEquations := false

def plan (rows : List Pattern) : Plan := GeneralExecutionAdmission.compile (snapshot rows) permissions
def environment (rows : List Pattern) : Environment := GeneralPlanEnvironment.environment (plan rows)

def declaration (index : Nat) (rule : RewriteRule) : RulePlan where
  declarationIndex := index
  authored := rule
  binding := ⟨GeneralRuleBindingInference.inferredSpec rule, .inferredRootInputs⟩

theorem compiled_bindings :
    GeneralRuleBindingInference.compile? language child = some (declaration 0 child).binding ∧
      GeneralRuleBindingInference.compile? language parent = some (declaration 1 parent).binding := by
  cbv

theorem compiled_premises (rows : List Pattern) :
    GeneralPremise.rulePremisesAdmitted language (snapshot rows).provider
      ((declaration 0 child).binding.elaborate child)
      (declaration 0 child).binding.spec = true ∧
    GeneralPremise.rulePremisesAdmitted language (snapshot rows).provider
      ((declaration 1 parent).binding.elaborate parent)
      (declaration 1 parent).binding.spec = true := by
  cbv

theorem compiled_templates :
    GeneralEquationCanonicalTemplates.checkRule child = true ∧
      GeneralEquationCanonicalTemplates.checkRule parent = true ∧
      GeneralEquationCanonicalTemplates.checkBinding (declaration 0 child).binding.spec = true ∧
      GeneralEquationCanonicalTemplates.checkBinding (declaration 1 parent).binding.spec = true := by
  decide +kernel

theorem compiled_rules (rows : List Pattern) :
    (plan rows).rules = [declaration 0 child, declaration 1 parent] := by
  have selectedRules : selectedRules (snapshot rows) permissions = [(child, 0), (parent, 1)] := rfl
  unfold plan GeneralExecutionAdmission.compile GeneralExecutionAdmission.rules
  rw [selectedRules]
  simp only [List.filterMap_cons, List.filterMap_nil, rulePlan?, Option.bind_eq_bind,
    show (snapshot rows).language = language from rfl, compiled_bindings.1,
    compiled_bindings.2, Option.bind_some, (compiled_premises rows).1,
    (compiled_premises rows).2, compiled_templates.1, compiled_templates.2.1,
    compiled_templates.2.2.1, compiled_templates.2.2.2, Bool.and_self, ↓reduceIte]
  rfl

def runtimeEnvironment (rows : List Pattern) : Environment where
  language := {language with rewrites :=
    [(declaration 0 child).rule, (declaration 1 parent).rule]}
  free := (snapshot rows).free
  provider := (snapshot rows).provider
  specifications := [(0, (declaration 0 child).binding.spec),
    (1, (declaration 1 parent).binding.spec)]
  reflection := permissions.reflection

theorem environment_actual (rows : List Pattern) :
    environment rows = runtimeEnvironment rows := by
  unfold environment GeneralPlanEnvironment.environment
  rw [compiled_rules]
  rfl

def source (elements : List Pattern) : Pattern := .apply "Wrap" [zero, .collection .vec elements none]
def goal (elements : List Pattern) : Goal := .root [] term (source elements) 1
def state (rows elements : List Pattern) (fuel : Nat) : State (runtimeEnvironment rows) (goal elements) :=
  run (runtimeEnvironment rows) (goal elements) fuel (start (runtimeEnvironment rows) (goal elements))

def targets (rows elements : List Pattern) : Result (runtimeEnvironment rows) (goal elements) → Pattern
  | .root _ _ _ _ target _ => target

def history (rows elements : List Pattern) : Result (runtimeEnvironment rows) (goal elements) → List Event
  | .root _ _ _ events _ _ => events

def quantifierIndices : Event → List Nat
  | .quantified _ _ _ elements => elements.map Prod.fst
  | _ => []

def childOrigins : Event → List (Nat × List TypeExpr × Pattern × Pattern)
  | .child _ _ index bound source target _ _ _ _ _ => [(index, bound, source, target)]
  | _ => []

theorem actual_plan_accepted : (plan [zero]).complete = true := by cbv

theorem static_profile_accepted : Static.checkLanguage (environment [zero]) = true := by cbv

theorem total_profile_accepted :
    (GeneralExecutionTotalAdmission.compile (snapshot [zero]) permissions).complete = true := by
  apply GeneralExecutionTotalAdmission.compile_complete_of_generic actual_plan_accepted
  cbv

theorem every_typed_input_certified {bound : List TypeExpr} {expected : TypeExpr} {input : Pattern}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.HasType language (snapshot [zero]).free
      bound input expected) (object : Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern input = true) :
    ∃ result, GeneralOccurrenceFrontier.executeCertified? (snapshot [zero]) permissions bound expected input =
        some result ∧
      GeneralOccurrenceFrontier.complete _ result = true ∧
      GeneralOccurrenceFrontier.checkCertificate _ result = true := by
  obtain ⟨result, executed⟩ := GeneralOccurrenceFrontier.executeCertified?_exists
    total_profile_accepted typed object
  exact ⟨result, executed, GeneralOccurrenceFrontier.executeCertified?_complete executed⟩

theorem actual_compiled_declaration_positions :
    (plan [zero]).rules.map RulePlan.declarationIndex = [0, 1] := by
  rw [compiled_rules]
  rfl

theorem actual_compiled_all_forms :
    (state [zero] [zero, zero] 200).answers.map (targets [zero] [zero, zero]) =
      [.apply "Accept" [zero]] := by decide +kernel

theorem actual_scoped_directed_child :
    (state [zero] [zero, zero] 200).answers.map
      (fun answer => (history [zero] [zero, zero] answer).flatMap childOrigins) =
      [[(0, [name], .apply "Successor" [zero], zero)]] := by decide +kernel

def failedChildGoal : Goal := .steps [name] term zero 1

def failedChildState : State (runtimeEnvironment [zero]) failedChildGoal :=
  run (runtimeEnvironment [zero]) failedChildGoal 50
    (start (runtimeEnvironment [zero]) failedChildGoal)

/-- The child executor searches the actual earlier declaration, but Zero has
no Successor redex. This is resolved failure, with no invented child event. -/
theorem directed_child_failure_resolved :
    failedChildState.answers = [] ∧ failedChildState.unresolved = [] ∧
      complete (runtimeEnvironment [zero]) failedChildGoal failedChildState = true := by
  decide +kernel

theorem actual_compiler_child_failure :
    (run (environment [zero]) failedChildGoal 50
      (start (environment [zero]) failedChildGoal)).answers = [] := by
  rw [environment_actual]
  exact directed_child_failure_resolved.1

theorem duplicate_elements_retain_order :
    (state [zero] [zero, zero] 200).answers.map
      (fun answer => (history [zero] [zero, zero] answer).flatMap quantifierIndices) = [[0, 1]] := by decide +kernel

theorem empty_quantifier_completed :
    (state [zero] [] 200).answers.map (targets [zero] []) = [.apply "Accept" [zero]] := by decide +kernel

theorem failed_query_resolved_without_answer :
    (state [] [zero] 200).answers = [] ∧ (state [] [zero] 200).unresolved = [] ∧
      GeneralPremise.Execution.complete (runtimeEnvironment []) (goal [zero]) (state [] [zero] 200) = true := by
  decide +kernel

theorem interrupted_keeps_work :
    (state [zero] [zero, zero] 4).answers = [] ∧ (state [zero] [zero, zero] 4).agenda ≠ [] := by decide +kernel

theorem resumed_hidden_firing :
    (run (runtimeEnvironment [zero]) (goal [zero, zero]) 196 (state [zero] [zero, zero] 4)).answers.map
      (targets [zero] [zero, zero]) = [.apply "Accept" [zero]] := by
  change (run (runtimeEnvironment [zero]) (goal [zero, zero]) 196
    (run (runtimeEnvironment [zero]) (goal [zero, zero]) 4
      (start (runtimeEnvironment [zero]) (goal [zero, zero])))).answers.map
      (targets [zero] [zero, zero]) = [.apply "Accept" [zero]]
  rw [← run_add]
  exact actual_compiled_all_forms

end Mettapedia.OSLF.MeTTaIL.GeneralAuthoredExecutionControls
