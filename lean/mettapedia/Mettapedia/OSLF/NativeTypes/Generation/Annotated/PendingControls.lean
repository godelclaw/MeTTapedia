import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Checking
import Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls

open Mettapedia.OSLF.Framework

/-!
# Typed templates with unresolved operational binding admission

A metavariable beneath a binder is fully typed by an annotated source
certificate. Without authored dependency metadata, the conservative rule
compiler refuses to infer its binding interpretation. The generator retains
that distinction as an unresolved operational declaration.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Annotated.PendingControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Annotations
open Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls (carrier wrap wrapGrammar doneGrammar)

def source : Pattern := .lambda none (wrap (.fvar "B"))
def target : Pattern := .lambda none (.fvar "B")
def rule : RewriteRule where
  name := "unannotated-dependent-binding"
  typeContext := [("B", carrier)]
  premises := []
  left := source
  right := target

def language : LanguageDef :=
  {Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls.language with name := "pending-binding-admission", rewrites := [rule]}
def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩
def permissions : Permissions := {sites := .all}
def fragment : LanguageFragment := ⟨none, permissions⟩
def chosen : Snapshot := selectedSnapshot snapshot fragment

theorem chosen_snapshot : chosen = snapshot := by
  unfold chosen selectedSnapshot fragment
  rw [unrestricted_signature]

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)
def generated : Generated := generate snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment vertex

theorem actual_rules_pending : generated.plan.rules = [] := by
  change (compile chosen permissions).rules = []
  rw [chosen_snapshot]
  cbv

theorem root_template : generated.rawSites[0]? =
    some ({context := .hole, focus := source, declaration := 0, rule := rule} : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site) := by
  change (selectedSites chosen.language permissions)[0]? = _
  rw [chosen_snapshot]
  cbv

def annotation (domain : TypeExpr) (bound : List TypeExpr) : SourceAnnotation :=
  {bound := bound, programCarrier := .arrow domain carrier,
    focusBound := bound, focusCarrier := .arrow domain carrier,
    descent := .here (.lambda (.application 1 (.cons .fvar .nil)))}

theorem annotation_check (domain : TypeExpr) (bound : List TypeExpr) :
    generated.checkSourceAnnotation
      {context := .hole, focus := source, declaration := 0, rule := rule}
      (annotation domain bound) = true := by
  change checkDescent chosen.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree rule) source .hole bound
    (.arrow domain carrier) bound (.arrow domain carrier) _ = true
  rw [chosen_snapshot]
  change checkDescent language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree rule) source .hole bound
    (.arrow domain carrier) bound (.arrow domain carrier) _ = true
  simp [checkDescent, check, checkArguments, annotation, language, source, wrap, rule,
    Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls.language, Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree, wrapGrammar, carrier, usesBareCollection?, parameterType?,
    MatchesParameterRepresentation]

theorem every_typed_source_retained (domain : TypeExpr) (bound : List TypeExpr) :
    (generated.instantiateAnnotatedSource? 0 (annotation domain bound)).isOk = true := by
  unfold Generated.instantiateAnnotatedSource?
  split
  · rename_i missing
    rw [root_template] at missing
    contradiction
  · rename_i actual actualAt
    have same := Option.some.inj (actualAt.symm.trans root_template)
    subst actual
    have templateChecked : generated.checkRawTemplate
        {context := .hole, focus := source, declaration := 0, rule := rule} = true := by
      change (decide (chosen.language.rewrites[0]? = some rule) && selected permissions.ruleIndices 0 &&
        decide ((.hole : DerivedContexts.OneHoleContext).fill source = rule.left)) = true
      rw [chosen_snapshot]
      change (decide (language.rewrites[0]? = some rule) && selected permissions.ruleIndices 0 &&
        decide ((.hole : DerivedContexts.OneHoleContext).fill source = rule.left)) = true
      simp [language, permissions, rule, selected, DerivedContexts.OneHoleContext.fill]
    simp only [templateChecked, annotation_check domain bound, ↓reduceDIte, Except.isOk, Except.toBool]

theorem typed_source_does_not_launder_operational_admission (domain : TypeExpr) (bound : List TypeExpr) :
    generated.instantiateAnnotatedSchema? 0 (annotation domain bound) =
      .error (.unresolvedOperationalDeclaration 0) := by
  have success := every_typed_source_retained domain bound
  cases sourceAt : generated.instantiateAnnotatedSource? 0 (annotation domain bound) with
  | error issue => simp [sourceAt, Except.isOk, Except.toBool] at success
  | ok checkedSource =>
      have missing : checkedSource.ruleEntry? = none := by
        cases found : checkedSource.ruleEntry? with
        | none => rfl
        | some entry =>
            let payload : RulePlan × Nat := entry.val
            have member : payload ∈ generated.plan.rules.zipIdx := entry.property
            rw [actual_rules_pending] at member
            exact False.elim (List.not_mem_nil member)
      have retained := instantiated_source_input_retained sourceAt
      have actualAt := checkedSource.present
      rw [retained.1, root_template] at actualAt
      have same := Option.some.inj actualAt.symm
      rw [unadmitted_annotated_source_unresolved sourceAt missing, same]

theorem actual_change : source ≠ target := by decide +kernel

end Mettapedia.OSLF.NativeTypes.Generation.Annotated.PendingControls
