import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderTotality
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesFocus
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceResolvedLifting

/-!
# Resolved jobs at every occurrence of the original binder language

Every consume job and both oriented extrusion jobs drain their actual scoped
matcher and guard-query continuations. The proof ranges over arbitrary
canonical typed sources and all independently licensed grammar descents,
including nested binder bodies and all typing alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open EquationFrontierBinderProfile GeneralPremise GeneralPremise.Execution GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

def consumeChoice (again : Bool) : Choice := if again then .consumeAgain else .consume

theorem consume_position (allowed : List Token) (again : Bool) (bound : List TypeExpr) :
    (plan allowed).rules[(consumeChoice again |>.context bound).ruleIndex]? =
      some (consumePlan (consumeChoice again |>.context bound).ruleIndex) := by
  rw [compiled_rules]
  cases again <;> rfl

theorem consume_declared (allowed : List Token) (again : Bool) (bound : List TypeExpr) :
    (environment allowed).language.rewrites[(consumeChoice again |>.context bound).ruleIndex]? =
      some (consumeChoice again).rule := by
  have selected := GeneralPlanEnvironment.selected_rule (plan allowed) (consume_position allowed again bound)
  cases again <;> exact selected

theorem consume_specified (allowed : List Token) (again : Bool) (bound : List TypeExpr) :
    specification? (environment allowed) (consumeChoice again |>.context bound).ruleIndex =
      some (consumeChoice again).spec := by
  have selected := GeneralPlanEnvironment.selected_specification (plan allowed) (consume_position allowed again bound)
  cases again <;> exact selected

theorem choice_admitted (choice : Choice) : admittedFor choice.rule choice.spec = true := by
  cases choice <;> decide +kernel

def resolved_consume_root {allowed : List Token} (again : Bool) {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    (sorted : OpenPatternWellSorted (environment allowed).language (environment allowed).free bound type source)
    (outer : Goal)
    (tail : Continuation (environment allowed)
      (.root bound type source (consumeChoice again |>.context bound).ruleIndex) outer)
    (continued : ResolvedContinued (environment allowed) outer _ tail) :
    ResolvedTree (environment allowed) outer
      (.evaluate (.root bound type source (consumeChoice again |>.context bound).ruleIndex) tail) := by
  have declared := consume_declared allowed again bound
  have specified := consume_specified allowed again bound
  have admitted := choice_admitted (consumeChoice again)
  have checked := checkOpenPatternWellSorted_complete sorted
  apply ResolvedTree.branch
  · apply checkGoalReady_sound
    simp only [checkGoalReady, declared, specified, admitted, checked, Bool.and_self]
  · simp only [expand, evaluate]
    unfold evaluateRoot
    split
    · rename_i absent
      rw [declared] at absent
      cases absent
    · rename_i rule found
      have same : rule = (consumeChoice again).rule := Option.some.inj (found.symm.trans declared)
      subst rule
      split
      · rename_i absent
        rw [specified] at absent
        cases absent
      · rename_i spec found
        have same : spec = (consumeChoice again).spec := Option.some.inj (found.symm.trans specified)
        subst spec
        split
        · exact .cons
            (resolvedRootMatch _ _ _ (fun answer valid typed =>
              resolved_guard_root_body (choice := consumeChoice again)
                declared found admitted (checkOpenPatternWellSorted_sound checked)
                valid typed outer tail continued)) (.nil _ _)
        · rename_i rejected
          exact False.elim (rejected admitted)

theorem consume_root_resolved {allowed : List Token} (again : Bool) {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    (sorted : OpenPatternWellSorted (environment allowed).language (environment allowed).free bound type source) :
    (Execution.finish (environment allowed)
      (.root bound type source (consumeChoice again |>.context bound).ruleIndex)).unresolved = [] :=
  finish_resolved_of_tree _ _ (resolved_consume_root again sorted _ _ (resolvedDone _ _))

theorem rule_job_resolved {allowed : List Token} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {job : GeneralRuleJobs.Job}
    (sourceTyped : OpenPatternWellSorted language FreeTypeContext.empty bound type source)
    (licensed : job.Valid (plan allowed) bound type source) :
    (GeneralRuleJobExecution.finishState ⟨plan allowed, bound, type, source, job⟩ licensed).unresolved = [] := by
  apply GeneralRuleJobExecution.finishState_resolved
  have sorted := licensed.2.focus_sorted sourceTyped.2.1
  have position := licensed.1
  rw [compiled_rules] at position
  change (job.declaration, job.ordinal) ∈ [(consumePlan 0, 0), (consumePlan 1, 1)] at position
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at position
  rcases position with ⟨rule, index⟩ | ⟨rule, index⟩
  · change (Execution.finish (environment allowed)
      (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).unresolved = []
    rw [index]
    exact consume_root_resolved false sorted
  · change (Execution.finish (environment allowed)
      (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).unresolved = []
    rw [index]
    exact consume_root_resolved true sorted

theorem equation_job_resolved {allowed : List Token} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {job : GeneralEquationJobs.Job}
    (sourceTyped : OpenPatternWellSorted language FreeTypeContext.empty bound type source)
    (licensed : GeneralEquationJobs.LicensedJob (plan allowed) bound type source job) :
    (GeneralEquationJobExecution.finishJob ⟨plan allowed, bound, type, source, job⟩ licensed).unresolved = [] := by
  apply GeneralEquationJobExecution.finishJob_resolved _ _ sourceTyped
  intro trace captured matching typed
  have rulesLength : (plan allowed).rules.length = 2 := by rw [compiled_rules]; rfl
  have selected := List.fst_mem_of_mem_zipIdx licensed.1
  rw [compiled_equations] at selected
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  cases job with
  | mk position equation site =>
      rcases selected with forward | reverse
      · change equation = extrusionPlan .forward at forward
        subst equation
        have contextSame : (GeneralEquationJobs.Job.context ⟨position, extrusionPlan .forward, site⟩ (plan allowed)) =
            Choice.forward.context site.focusBound := by
          simp only [GeneralEquationJobs.Job.context, rulesLength]
          rfl
        change TypedAssignment (environment allowed) _ captured at typed
        rw [contextSame] at typed
        change (Execution.finish (environment allowed)
          (.premises _ Choice.forward.rule.premises captured)).unresolved = []
        rw [contextSame]
        exact authored_premises_resolved typed (matching_names (choice := .forward) matching.matching)
      · change equation = extrusionPlan .reverse at reverse
        subst equation
        have contextSame : (GeneralEquationJobs.Job.context ⟨position, extrusionPlan .reverse, site⟩ (plan allowed)) =
            Choice.reverse.context site.focusBound := by
          simp only [GeneralEquationJobs.Job.context, rulesLength]
          rfl
        change TypedAssignment (environment allowed) _ captured at typed
        rw [contextSame] at typed
        change (Execution.finish (environment allowed)
          (.premises _ Choice.reverse.rule.premises captured)).unresolved = []
        rw [contextSame]
        exact authored_premises_resolved typed (matching_names (choice := .reverse) matching.matching)

#print axioms consume_root_resolved
#print axioms rule_job_resolved
#print axioms equation_job_resolved

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution
