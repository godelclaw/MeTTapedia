import Mettapedia.OSLF.MeTTaIL.GeneralRhoFrontierControls

/-!
# Rho with its standard reduction contexts

In the rho calculus a process reduces only inside a parallel composition. A
process guarded by an input waits until the input fires, a sent process is
data, and a quoted name is never reduced. This plan keeps the original COMM
declaration and licenses only positions inside the parallel bag.

The all-sites plan `GeneralRho.plan` also fires COMM under input binders,
inside sent processes and inside quoted names. Both plans agree on the
declaration, the execution environment and every admission obligation; they
differ only in which positions are reduction contexts.

Positive examples: the bag, a bag nested in it, and their processes are
reduction contexts, and the COMMs there fire. Negative example: nothing under an
input is a reduction context, although the all-sites plan licenses thirteen
positions of the same source and fires the COMM under the input's binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho.Standard

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open GeneralScopedMatchMachine
open FrontierControls (zero channel receivedBody rootSource rootTarget inputSource parallelSource
  parallelTarget Readout readouts)

/-- Only the parallel bag is a reduction context. -/
def sites : GeneralTypedSites.OperationalPermissions := { collectionKinds := [.hashBag] }

def permissions : GeneralExecutionAdmission.Permissions := { GeneralRho.permissions with sites := sites }

/-- The rho plan with the standard reduction contexts. -/
def plan : GeneralExecutionAdmission.Plan := GeneralExecutionAdmission.compile snapshot permissions

theorem compiled_rules : plan.rules = [declaration] := GeneralRho.compiled_rules

theorem compilation_has_no_equations : plan.equations = [] := rfl

/-- The reduction contexts are the only difference from the all-sites plan. -/
theorem environment_eq : GeneralPlanEnvironment.environment plan = GeneralPlanEnvironment.environment GeneralRho.plan :=
  rfl

theorem compilation_complete : plan.complete = true := GeneralRho.compilation_complete

/-- COMM asks for no child step, so the compiled language is stratified. -/
theorem stratified :
    GeneralPremise.checkStepStratification (GeneralPlanEnvironment.environment plan).language = true := by
  change GeneralPremise.checkStepStratification
    { GeneralRho.language with rewrites := plan.rules.map GeneralExecutionAdmission.RulePlan.rule } = true
  rw [compiled_rules]
  rfl

/-- A COMM at the root of the bag is a valid receipt of the standard plan. -/
theorem root_receipt_valid {bound : List TypeExpr} {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : OpenPatternWellSorted language snapshot.free bound (.base "Name") channel)
    (bodyTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Proc") body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 1) body = true)
    (names : ReflectiveInstantiation.namesAdmitted
      rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language snapshot.free bound (.base "Proc") payload)
    (restTyped : ElementsHaveType language snapshot.free bound rest (.base "Proc"))
    (restRepresented : ∀ pattern ∈ rest, Represented pattern) :
    (rootReceipt bound channel body payload rest).Valid plan bound (.base "Proc")
      (source channel body payload rest) := by
  obtain ⟨⟨declared, _⟩, firing, accepted, filled, typed⟩ :=
    GeneralRho.root_receipt_valid channelTyped bodyTyped sealed names payloadTyped restTyped restRepresented
  have sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language snapshot.free
      bound (.base "Proc") (source channel body payload rest) := by
    cases firing with
    | fire _ _ _ sourceTyped _ _ _ _ _ => exact sourceTyped
  exact ⟨⟨declared, .here rfl sourceTyped.2.2.1 sourceTyped.1⟩, firing, accepted, filled, typed⟩

/-! ## Controls -/

def runtimePlan : GeneralExecutionAdmission.Plan where
  snapshot := snapshot
  permissions := permissions
  rules := [declaration]
  equations := []
  obligations := []

theorem runtime_plan_actual : plan = runtimePlan := by
  have obligations := List.isEmpty_iff.mp compilation_complete
  change (GeneralExecutionAdmission.compile snapshot permissions).obligations = [] at obligations
  have rules := compiled_rules
  have equations := compilation_has_no_equations
  unfold plan GeneralExecutionAdmission.compile at rules equations ⊢
  dsimp only [GeneralExecutionAdmission.compile] at obligations
  simp only at rules equations
  rw [rules, equations, obligations]
  rfl

def request (pattern : Pattern) : GeneralOccurrenceFrontier.Request := ⟨runtimePlan, [], .base "Proc", pattern⟩

theorem request_actual (pattern : Pattern) :
    (⟨plan, [], .base "Proc", pattern⟩ : GeneralOccurrenceFrontier.Request) = request pattern := by
  rw [runtime_plan_actual]
  rfl

theorem start_literal {pattern : Pattern}
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (checked : checkOpenPatternWellSorted language snapshot.free [] (.base "Proc") pattern = true) :
    GeneralOccurrenceFrontier.start (request pattern) =
      { agenda := [.visit ⟨pattern, [], by
          rw [show (request pattern).root = pattern from
            Pattern.eraseBinderMetadata_eq_self_of_canonical canonical]
          exact .nil pattern⟩, .universe] } := by
  simp only [GeneralOccurrenceFrontier.start, GeneralOccurrenceFrontier.Request.root, request,
    Pattern.eraseBinderMetadata_eq_self_of_canonical canonical]
  change (if checkOpenPatternWellSorted language snapshot.free [] (.base "Proc") pattern then _ else _) = _
  rw [checked]
  rfl

/-- The reduction contexts of a source: the address of every licensed site of the COMM declaration. -/
def contexts (plan : GeneralExecutionAdmission.Plan) (source : Pattern) : List (List Nat) :=
  (GeneralRuleJobs.jobs plan [] (.base "Proc") source).map (·.site.address)

/-- Positive: the bag and each of its processes are reduction contexts. -/
theorem root_contexts : contexts runtimePlan rootSource = [[], [0], [1]] := by decide +kernel

/-- Positive: a bag inside the bag, and each of its processes, are reduction contexts. -/
theorem nested_contexts : contexts runtimePlan parallelSource = [[], [0], [1], [1, 0], [1, 1]] := by
  decide +kernel

/-- Negative: an input is a reduction context only as a whole; nothing inside it is. -/
theorem guarded_contexts : contexts runtimePlan inputSource = [[]] := by decide +kernel

/-- The all-sites plan licenses thirteen positions of the same guarded source, among them the
channel, the input body under its binder at `[1, 0]`, and positions inside quoted names. -/
theorem all_sites_guarded_contexts : contexts FrontierControls.runtimePlan inputSource =
    [[], [0], [0, 0], [1], [1, 0], [1, 0, 0], [1, 0, 0, 0], [1, 0, 0, 1], [1, 0, 0, 1, 0],
      [1, 0, 0, 1, 0, 0], [1, 0, 1], [1, 0, 1, 0], [1, 0, 1, 1]] := by
  decide +kernel

/-- Positive, at a fixed fuel: the root COMM has been read out. -/
theorem root_comm_fires :
    readouts (request rootSource) 40 = [⟨0, [], [], commTrace, some receivedBody, rootTarget⟩] := by
  unfold readouts
  rw [start_literal (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- Positive, at a fixed fuel: the COMM inside the nested bag has been read out. -/
theorem nested_parallel_comm_fires :
    readouts (request parallelSource) 60 = [⟨0, [1], [], commTrace, some receivedBody, parallelTarget⟩] := by
  unfold readouts
  rw [start_literal (by decide +kernel) (by decide +kernel)]
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.GeneralRho.Standard
