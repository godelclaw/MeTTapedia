import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFlow

/-!
# Selected canonical presentation controls

Named display metadata on an authored target leaves a real compiler
obligation. Explicitly deselecting that declaration removes the obligation;
selecting its canonical presentation instead admits the actual rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalAdmissionControls

open Syntax GeneralExecutionAdmission

def rawTarget : RewriteRule where
  name := "publish-binder"
  typeContext := []
  premises := []
  left := .apply "A" []
  right := .apply "Nu" [.lambda (some "display") (.apply "A" [])]

def language : LanguageDef where
  name := "canonical-target-control"
  types := ["Proc", "Name"]
  terms := [
    {label := "A", category := "Proc", params := [], syntaxPattern := []},
    {label := "Nu", category := "Proc",
      params := [.abstraction "body" (.arrow .name .proc)], syntaxPattern := []}]
  equations := []
  rewrites := [rawTarget]

def snapshot : Snapshot where
  language := language
  freeTypes := []
  provider := ⟨[], [], []⟩

def permissions : Permissions where
  includeDerivedEquations := false

theorem raw_binding_supported :
    (GeneralRuleBindingInference.compile? language rawTarget).isSome = true := by
  cbv

theorem selected_named_target_rejected :
    (compile snapshot permissions).rules = [] ∧
      (compile snapshot permissions).obligations = [.ruleCanonical 0] ∧
      (compile snapshot permissions).complete = false := by
  cbv

theorem deselected_named_target_admitted :
    (compile snapshot {permissions with ruleIndices := some []}).complete = true := by
  cbv

def canonicalSnapshot : Snapshot :=
  {snapshot with language := {language with
    rewrites := [GeneralEquationCanonicalTemplates.normalizeRule rawTarget]}}

theorem normalized_target_admitted :
    (compile canonicalSnapshot permissions).complete = true ∧
      (compile canonicalSnapshot permissions).rules.length = 1 := by
  cbv

def rawEquation : Equation where
  name := "named-equation-side"
  typeContext := []
  premises := []
  left := .apply "Nu" [.lambda none (.apply "A" [])]
  right := .apply "Nu" [.lambda (some "display") (.apply "A" [])]

def equationSnapshot : Snapshot :=
  {snapshot with language := {language with rewrites := [], equations := [rawEquation]}}

theorem selected_named_equation_rejected :
    (compile equationSnapshot permissions).equations = [] ∧
      (compile equationSnapshot permissions).obligations =
        [.equationCanonical 0 .forward, .equationCanonical 0 .reverse] ∧
      (compile equationSnapshot permissions).complete = false := by
  cbv

theorem deselected_named_equation_admitted :
    (compile equationSnapshot {permissions with equationIndices := some []}).complete = true := by
  cbv

end Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalAdmissionControls
