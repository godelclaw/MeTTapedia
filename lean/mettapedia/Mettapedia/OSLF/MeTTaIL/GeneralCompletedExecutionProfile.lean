import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceReceiptKeys

/-!
# Authored conditional-equation execution profile

The source language has three nullary terms, a conditional equation and two
distinct authored reductions. Duplicate equation-query rows are retained as
administrative evidence. The completion construction drains the actual scheduler and checks its
occurrence certificate. Its hypotheses are discharged from the authored
snapshot, rather than supplied as an external completion promise.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted

def term : TypeExpr := .base "Term"
def one : Pattern := .apply "One" []
def two : Pattern := .apply "Two" []
def done : Pattern := .apply "Done" []

def equation : Equation where
  name := "guarded-one-two"
  typeContext := []
  premises := [.relationQuery "allow" [one]]
  left := one
  right := two

def consume (name : String) : RewriteRule where
  name := name
  typeContext := []
  premises := []
  left := two
  right := done

def language : LanguageDef where
  name := "completed-equation-frontier"
  types := ["Term"]
  terms := [
    {label := "One", category := "Term", params := [], syntaxPattern := []},
    {label := "Two", category := "Term", params := [], syntaxPattern := []},
    {label := "Done", category := "Term", params := [], syntaxPattern := []}]
  equations := [equation]
  rewrites := [consume "consume-first", consume "consume-second"]

def snapshot (enabled : Bool) : Snapshot where
  language := language
  freeTypes := []
  provider := ⟨[⟨"allow", [term], [.input]⟩],
    (if enabled then [⟨"allow", [one]⟩, ⟨"allow", [one]⟩] else []), []⟩

def permissions : Permissions where
  sites := .all

def binding : GeneralRuleBindingInference.BindingPlan :=
  ⟨{dependencies := []}, .inferredRootInputs⟩

def declaration (index : Nat) : RulePlan where
  declarationIndex := index
  authored := consume (if index = 0 then "consume-first" else "consume-second")
  binding := binding

def oriented (direction : ScopedEquationExecution.Orientation) : EquationPlan where
  declarationIndex := 0
  authored := equation
  direction := direction
  binding := binding
  coverageReady := true

def runtimePlan (enabled : Bool) : Plan where
  snapshot := snapshot enabled
  permissions := permissions
  rules := [declaration 0, declaration 1]
  equations := [oriented .forward, oriented .reverse]
  obligations := []

theorem runtime_plan_actual (enabled : Bool) :
    compile (snapshot enabled) permissions = runtimePlan enabled := by
  cases enabled <;> cbv

theorem compilation_total (enabled : Bool) :
    (GeneralExecutionTotalAdmission.compile (snapshot enabled) permissions).complete = true := by
  apply GeneralExecutionTotalAdmission.compile_complete_of_generic
  · rw [runtime_plan_actual]
    rfl
  · rw [runtime_plan_actual]
    cases enabled <;> cbv

theorem source_typed (enabled : Bool) :
    HasType language (snapshot enabled).free [] one term := by
  refine .constructor (rule :=
    {label := "One", category := "Term", params := [], syntaxPattern := []})
    List.mem_cons_self ?_ .nil
  simp [UsesBareCollection]

def request (enabled : Bool) : GeneralOccurrenceFrontier.Request :=
  ⟨compile (snapshot enabled) permissions, [], term, one⟩

def runtimeRequest (enabled : Bool) : GeneralOccurrenceFrontier.Request :=
  ⟨runtimePlan enabled, [], term, one⟩

theorem runtime_request_actual (enabled : Bool) : request enabled = runtimeRequest enabled := by
  unfold request runtimeRequest
  rw [runtime_plan_actual]

theorem actual_start (enabled : Bool) :
    GeneralOccurrenceFrontier.start (runtimeRequest enabled) =
      { agenda := [.visit ⟨(runtimeRequest enabled).root, [], .nil _⟩, .universe] } := by
  cases enabled <;> cbv


theorem request_root (enabled : Bool) : (request enabled).root = one := by
  simp [GeneralOccurrenceFrontier.Request.root, request, one, Pattern.eraseBinderMetadata]

theorem admitted (enabled : Bool) : GeneralOccurrenceFrontier.Admitted (request enabled) :=
  GeneralOccurrenceFrontier.compiled_source_admitted (compilation_total enabled)
    (source_typed enabled) rfl

/-- The actual generic completion algorithm runs from this authored snapshot.
No caller supplies a fuel bound, finite carrier or completion certificate. -/
def completed (enabled : Bool) : GeneralOccurrenceFrontier.State (request enabled) :=
  GeneralOccurrenceFrontier.finish (request enabled) (admitted enabled)

theorem completed_complete (enabled : Bool) :
    GeneralOccurrenceFrontier.complete (request enabled) (completed enabled) = true :=
  GeneralOccurrenceFrontier.finish_complete_of_total_admission (admitted enabled)
    (GeneralExecutionTotalAdmission.compile_totality_checked (compilation_total enabled))

theorem completed_certificate (enabled : Bool) :
    GeneralOccurrenceFrontier.checkCertificate (request enabled) (completed enabled) = true :=
  GeneralOccurrenceFrontier.finish_certificate_of_total_admission (admitted enabled)
    (GeneralExecutionTotalAdmission.compile_totality_checked (compilation_total enabled))

theorem completed_actual_finite_run (enabled : Bool) :
    ∃ fuel, GeneralOccurrenceFrontier.run (request enabled) fuel
      (GeneralOccurrenceFrontier.start (request enabled)) = completed enabled :=
  GeneralOccurrenceFrontier.finish_actual_run (request enabled) (admitted enabled)

end Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls
