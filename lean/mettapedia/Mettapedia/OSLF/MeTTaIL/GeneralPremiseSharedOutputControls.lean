import Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage

/-!
# Compiled shared provider outputs and lexical quantification

Provider declarations with identical values remain distinct occurrences.
A later output matches the retained binding rather than replacing it. The
quantified parameter shadows an outer capture only while its body runs;
other outputs survive restoration. Empty quantification leaves an absent
output absent, and the compiler rejects relying on that output afterwards.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching Execution GeneralExecutionAdmission

def term : TypeExpr := .base "Term"
def zero : Pattern := .apply "Zero" []
def one : Pattern := .apply "Successor" [zero]

def quantifiedBody : Premise := .relationQuery "share" [.fvar "Y", .fvar "element"]
def quantified : Premise := .forAll "L" "element" quantifiedBody

def rule : RewriteRule where
  name := "shared-provider-output"
  typeContext := [("element", term), ("L", .collection .vec term), ("Y", term)]
  left := .apply "Wrap" [.fvar "element", .collection .vec [] (some "L")]
  right := .apply "Accept" [.fvar "Y", .fvar "element"]
  premises := [.relationQuery "choose" [.fvar "Y"], quantified,
    .relationQuery "confirm" [.fvar "Y"]]

def language : LanguageDef where
  name := "compiled-shared-output-quantification"
  types := ["Term"]
  terms := [
    {label := "Zero", category := "Term", params := [], syntaxPattern := []},
    {label := "Successor", category := "Term", params := [.simple "term" term], syntaxPattern := []},
    {label := "Wrap", category := "Term", params := [
      .simple "outer" term, .simple "elements" (.collection .vec term)], syntaxPattern := []},
    {label := "Accept", category := "Term", params := [
      .simple "answer" term, .simple "outer" term], syntaxPattern := []}]
  equations := []
  rewrites := [rule]

def provider : ProviderSnapshot where
  signatures := [⟨"choose", [term], [.output]⟩,
    ⟨"share", [term, term], [.output, .input]⟩,
    ⟨"confirm", [term], [.output]⟩]
  rows := [⟨"choose", [zero]⟩, ⟨"choose", [zero]⟩,
    ⟨"share", [zero, zero]⟩, ⟨"share", [one, zero]⟩,
    ⟨"confirm", [one]⟩, ⟨"confirm", [zero]⟩]

def snapshot : Snapshot := ⟨language, [], provider⟩
def permissions : Permissions where
  equationIndices := some []
  includeDerivedEquations := false

def admission : GeneralExecutionTotalAdmission.Admission :=
  GeneralExecutionTotalAdmission.compile snapshot permissions

def plan : Plan := admission.execution

def declaration : RulePlan where
  declarationIndex := 0
  authored := rule
  binding := ⟨GeneralRuleBindingInference.inferredSpec rule, .inferredRootInputs⟩

theorem compiled_binding :
    GeneralRuleBindingInference.compile? language rule = some declaration.binding := by decide +kernel

theorem compiled_premises :
    rulePremisesAdmitted language provider rule declaration.binding.spec = true := by cbv

theorem compiled_templates :
    GeneralEquationCanonicalTemplates.checkRule rule = true ∧
      GeneralEquationCanonicalTemplates.checkBinding declaration.binding.spec = true := by decide +kernel

theorem compiled_rules : plan.rules = [declaration] := by
  have selected : selectedRules snapshot permissions = [(rule, 0)] := rfl
  unfold plan admission GeneralExecutionTotalAdmission.compile GeneralExecutionAdmission.compile
    GeneralExecutionAdmission.rules
  rw [selected]
  simp only [List.filterMap_cons, List.filterMap_nil, rulePlan?, Option.bind_eq_bind,
    show snapshot.language = language from rfl, show snapshot.provider = provider from rfl,
    compiled_binding, Option.bind_some, compiled_premises, compiled_templates.1,
    compiled_templates.2, Bool.and_self, ↓reduceIte]
  rfl

def environment : Environment where
  language := {language with rewrites := [declaration.rule]}
  free := snapshot.free
  provider := snapshot.provider
  specifications := [(0, declaration.binding.spec)]
  reflection := permissions.reflection

theorem environment_actual : GeneralPlanEnvironment.environment plan = environment := by
  unfold GeneralPlanEnvironment.environment
  rw [compiled_rules]
  rfl

def source (elements : List Pattern) : Pattern :=
  .apply "Wrap" [one, .collection .vec elements none]

def rootGoal (elements : List Pattern) : Goal := .root [] term (source elements) 0
def rootState (elements : List Pattern) : State environment (rootGoal elements) :=
  run environment (rootGoal elements) 400 (start environment (rootGoal elements))

def rootTarget {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → Pattern
  | .root _ _ _ _ target _ => target

def rootAssignment {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → Assignment
  | .root _ _ completed _ _ _ => completed

def queryRow? : Event → Option Nat
  | .query _ _ row _ => some row
  | _ => none

def queryRows : Event → List Nat
  | .query _ _ row _ => [row]
  | .quantified _ _ _ elements =>
      elements.flatMap fun element => element.2.2.filterMap queryRow?
  | _ => []

def rootRows {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → List Nat
  | .root _ _ _ events _ _ => events.flatMap queryRows

def readBody (assignment : Assignment) (name : String) : Option Pattern :=
  (lookup assignment name).map ContextualValue.body

theorem whole_profile_accepted : admission.complete = true := by cbv

theorem actual_compiled_rule : plan.rules.map RulePlan.declarationIndex = [0] := by
  rw [compiled_rules]
  rfl

theorem root_keeps_duplicate_provider_origins :
    (rootState [zero, zero]).answers.map (rootRows [zero, zero]) =
      [[0, 2, 2, 5], [1, 2, 2, 5]] := by decide +kernel

theorem conflicting_later_rows_do_not_overwrite :
    (rootState [zero, zero]).answers.map (rootTarget [zero, zero]) =
      [.apply "Accept" [zero, one], .apply "Accept" [zero, one]] := by decide +kernel

theorem root_preserves_global_output_and_outer_parameter :
    (rootState [zero, zero]).answers.map (fun answer =>
      (readBody (rootAssignment [zero, zero] answer) "Y",
        readBody (rootAssignment [zero, zero] answer) "element")) =
      [(some zero, some one), (some zero, some one)] := by decide +kernel

theorem root_search_completed :
    complete environment (rootGoal [zero, zero]) (rootState [zero, zero]) = true := by decide +kernel

theorem root_empty_quantification_keeps_only_preexisting_output :
    (rootState []).answers.map (rootRows []) = [[0, 5], [1, 5]] ∧
      (rootState []).answers.map (rootTarget []) =
        [.apply "Accept" [zero, one], .apply "Accept" [zero, one]] := by decide +kernel

/-- The local consumer's declaration and binding plan have an exact compiled
position; no rule-name lookup or fallback is used. -/
def compiledRule : RulePlan := declaration
theorem compiled_rule_selected : plan.rules[0]? = some compiledRule := by
  rw [compiled_rules]
  rfl

def context : Context := ⟨0, compiledRule.rule, compiledRule.binding.spec, [], 1, 0⟩

def captures (elements : List Pattern) : Assignment :=
  [("L", localValue [] (.collection .vec elements none)), ("element", localValue [] one)]

theorem captures_from_actual_root_matching :
    matchRuleAt compiledRule.rule compiledRule.binding.spec 0 (source [zero, zero]) =
      [captures [zero, zero]] := by decide +kernel

def quantifierGoal (elements : List Pattern) : Goal :=
  .premise context quantified (captures elements)

def quantifierState (elements : List Pattern) : State environment (quantifierGoal elements) :=
  run environment (quantifierGoal elements) 200 (start environment (quantifierGoal elements))

def quantifierAssignment (elements : List Pattern) : Result environment (quantifierGoal elements) → Assignment
  | .premise completed _ _ => completed

def quantifierOrigins (elements : List Pattern) : Result environment (quantifierGoal elements) →
    List (Nat × Pattern × List Nat)
  | .premise _ event _ => match event with
    | .quantified _ _ _ entries => entries.map fun entry =>
        (entry.1, entry.2.1, entry.2.2.filterMap queryRow?)
    | _ => []

theorem nonempty_quantification_creates_and_retains_shared_output :
    (quantifierState [zero, zero]).answers.map (fun answer =>
      (readBody (quantifierAssignment [zero, zero] answer) "Y",
        readBody (quantifierAssignment [zero, zero] answer) "element")) =
      [(some zero, some one), (some one, some one)] := by decide +kernel

theorem quantified_duplicates_keep_shared_binding_and_element_origins :
    (quantifierState [zero, zero]).answers.map (quantifierOrigins [zero, zero]) =
      [[(0, zero, [2]), (1, zero, [2])], [(0, zero, [3]), (1, zero, [3])]] := by decide +kernel

theorem empty_quantification_cannot_manufacture_a_binding :
    (quantifierState []).answers.map (fun answer =>
      (readBody (quantifierAssignment [] answer) "Y",
        readBody (quantifierAssignment [] answer) "element")) = [(none, some one)] := by decide +kernel

theorem quantifier_search_completed :
    complete environment (quantifierGoal [zero, zero]) (quantifierState [zero, zero]) = true ∧
      complete environment (quantifierGoal []) (quantifierState []) = true := by decide +kernel

def unsafeRule : RewriteRule := {rule with premises := [quantified]}
def unsafeLanguage : LanguageDef := {language with rewrites := [unsafeRule]}
def unsafeSnapshot : Snapshot := {snapshot with language := unsafeLanguage}

theorem empty_capable_output_cannot_supply_required_binding :
    (GeneralExecutionTotalAdmission.compile unsafeSnapshot permissions).complete = false := by cbv

theorem unsafe_rule_retains_actual_flow_obligation :
    GeneralExecutionAdmission.Obligation.rulePremises 0 ∈
      (GeneralExecutionAdmission.compile unsafeSnapshot permissions).obligations := by
  cbv
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem actual_compiler_executes_shared_output_origins :
    (run (GeneralPlanEnvironment.environment plan) (rootGoal [zero, zero]) 400
      (start (GeneralPlanEnvironment.environment plan) (rootGoal [zero, zero]))).answers.map
      (rootRows [zero, zero]) = [[0, 2, 2, 5], [1, 2, 2, 5]] := by
  rw [environment_actual]
  exact root_keeps_duplicate_provider_origins

#print axioms whole_profile_accepted
#print axioms root_keeps_duplicate_provider_origins
#print axioms nonempty_quantification_creates_and_retains_shared_output
#print axioms empty_capable_output_cannot_supply_required_binding

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls
