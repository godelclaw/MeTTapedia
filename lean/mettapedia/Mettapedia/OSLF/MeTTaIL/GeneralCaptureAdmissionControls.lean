import Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage

/-!
# Capture and sort rejection in an admitted binding language

The typed binder admits a closed body capture with an empty input spine.
Its own bound variable cannot escape through that same capture. Independent
sort checks reject a well-scoped Name value at a Term metavariable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralCaptureAdmissionControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open GeneralExecutionAdmission GeneralPremise.Execution

def term : TypeExpr := .base "Term"
def name : TypeExpr := .base "Name"
def zero : Pattern := .apply "Zero" []
def binder (body : Pattern) : Pattern := .apply "Binder" [.lambda none body]
def spec : RuleBindingSpec := { dependencies := [("X", [])] }

def rule : RewriteRule where
  name := "release-independent-body"
  typeContext := [("X", term)]
  left := binder (.fvar "X")
  right := .fvar "X"
  premises := []
  bindings := some spec

def language : LanguageDef where
  name := "capture-boundary"
  types := ["Term", "Name"]
  terms := [
    {label := "Zero", category := "Term", params := [], syntaxPattern := []},
    {label := "Binder", category := "Term", params := [
      .abstraction "body" (.arrow term term)], syntaxPattern := []}]
  equations := []
  rewrites := [rule]

def snapshot : Snapshot := ⟨language, [], ⟨[], []⟩⟩
def permissions : Permissions where
  equationIndices := some []
  includeDerivedEquations := false
def plan : Plan := GeneralExecutionAdmission.compile snapshot permissions
def declaration : RulePlan := ⟨0, rule, ⟨spec, .authored⟩⟩

theorem binding_admitted : admittedFor rule spec = true := by decide +kernel

theorem compiled_rules : plan.rules = [declaration] := by cbv

def environment : GeneralPremise.Environment where
  language := {language with rewrites := [declaration.rule]}
  free := snapshot.free
  provider := snapshot.provider
  specifications := [(0, spec)]
  reflection := permissions.reflection

theorem environment_actual : GeneralPlanEnvironment.environment plan = environment := by
  unfold GeneralPlanEnvironment.environment
  rw [compiled_rules]
  rfl

theorem whole_profile_admitted :
    (GeneralExecutionTotalAdmission.compile snapshot permissions).complete = true := by cbv

def goal (body : Pattern) : Goal := .root [] term (binder body) 0
def state (body : Pattern) : State environment (goal body) :=
  run environment (goal body) 50 (start environment (goal body))
def target (body : Pattern) : Result environment (goal body) → Pattern
  | .root _ _ _ _ result _ => result

theorem typed_bound_variable_source :
    Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted language snapshot.free
      [] term (binder (.bvar 0)) = true := by decide +kernel

theorem actual_closed_body_released : (state zero).answers.map (target zero) = [zero] := by
  decide +kernel

theorem actual_local_capture_rejected :
    (state (.bvar 0)).answers = [] ∧ (state (.bvar 0)).unresolved = [] ∧
      GeneralPremise.Execution.complete environment (goal (.bvar 0)) (state (.bvar 0)) = true := by
  decide +kernel

theorem actual_compiler_rejects_capture :
    (run (GeneralPlanEnvironment.environment plan) (goal (.bvar 0)) 50
      (start (GeneralPlanEnvironment.environment plan) (goal (.bvar 0)))).answers = [] := by
  rw [environment_actual]
  exact actual_local_capture_rejected.1

def context (bound : List TypeExpr) : GeneralPremise.Context := ⟨0, declaration.rule, spec, bound, 0, 0⟩
def boundValue : Assignment := [("X", ⟨[], 1, .bvar 0⟩)]

theorem same_scoped_value_needs_the_right_sort :
    (.bvar 0 : Pattern).isWellScopedAt 1 = true ∧
      GeneralPremise.checkTypedAssignment environment (context [name]) boundValue = false ∧
      GeneralPremise.checkTypedAssignment environment (context [term]) boundValue = true := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.GeneralCaptureAdmissionControls
