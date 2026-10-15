import Mettapedia.OSLF.NativeTypes.Modal.QuerySearch
import Mettapedia.OSLF.NativeTypes.Generation.BudgetControls
import Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl

open Mettapedia.OSLF.Framework

/-!
# Early-stop controls on actual occurrence execution

These controls use the equation-bearing finite language and the permissive
COMM companion. They check the two witness polarities, a genuinely unknown
pause, retention of pending work, and stability under substantially increased
budgets. The companion's site policy is not the standard rho reduction policy.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.QuerySearchControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.QuerySearch

def anyTarget {request : Request} : InvariantTest request :=
  {accepts := fun _ => true, invariant := fun _ _ _ => rfl}

def noTarget {request : Request} : InvariantTest request :=
  {accepts := fun _ => false, invariant := fun _ _ _ => rfl}

def equationRun (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Generation.BudgetControls.generated.searchModal [] Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.carrier
    Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.other .possibility anyTarget budget

def companionRun (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.searchModal [] (.base "Proc")
    GeneralRho.FrontierControls.rootSource .possibility anyTarget budget

def companionCounterexample (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.searchModal [] (.base "Proc")
    GeneralRho.FrontierControls.rootSource .outgoingUniversal noTarget budget

#guard (equationRun 0).result == .unknown
#guard (equationRun 40).result == .decided true
#guard (equationRun 100000).state.work == (equationRun 40).state.work
#guard (companionRun 100000).result == .decided true
#guard (companionRun 100000).state.work < 40
#guard (companionRun 100000).state.answers.length == 1
#guard (companionCounterexample 100000).result == .decided false
#guard !(companionCounterexample 100000).state.agenda.isEmpty
#guard !(complete _ (companionCounterexample 100000).state)

theorem equation_query_is_still_unknown_without_budget :
    (equationRun 0).result = .unknown := by
  rw [equationRun, searchModal_zero]
  exact Mettapedia.OSLF.NativeTypes.Generation.BudgetControls.no_budget_is_unknown

theorem equation_query_finds_actual_evidence :
    evidenceFound .possibility _ (fun _ => true) (equationRun 40).state = true := by
  simp only [equationRun, Generated.searchModal]
  rw [Mettapedia.OSLF.NativeTypes.Generation.BudgetControls.actual_request,
    Mettapedia.OSLF.NativeTypes.Generation.BudgetControls.literal_start]
  decide +kernel

/-- A large budget cannot advance a successful query to universe scanning. -/
theorem equation_query_arbitrary_extra_budget (more : Nat) :
    (equationRun (40 + more)).state = (equationRun 40).state := by
  exact runUntil_after_evidence _ _ 40 more (start _) equation_query_finds_actual_evidence

theorem companion_counterexample_is_actual_and_unfinished :
    evidenceFound .outgoingUniversal _ (fun _ => false) (companionCounterexample 40).state = true ∧
      (companionCounterexample 40).state.answers.length = 1 ∧
      (companionCounterexample 40).state.agenda.isEmpty = false ∧
      complete _ (companionCounterexample 40).state = false := by
  have requestEq : Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.request [] (.base "Proc")
      GeneralRho.FrontierControls.rootSource =
        GeneralRho.FrontierControls.literalRequest GeneralRho.FrontierControls.rootSource := by
    rw [Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.actual_request]
    exact GeneralRho.FrontierControls.actual_request _
  simp only [companionCounterexample, Generated.searchModal]
  rw [requestEq]
  rw [GeneralRho.FrontierControls.literal_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- Query completion is not occurrence completeness: a duplicate-origin
campaign still has pending work when the first discriminating receipt arrives. -/
def duplicateOriginQuery :=
  Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.searchModal [] (.base "Proc")
    GeneralRho.FrontierControls.duplicates .possibility anyTarget 75

theorem duplicate_query_keeps_one_actual_origin_and_pending_work :
    evidenceFound .possibility _ (fun _ => true) duplicateOriginQuery.state = true ∧
      duplicateOriginQuery.state.answers.length = 1 ∧
      duplicateOriginQuery.state.agenda.isEmpty = false ∧
      complete _ duplicateOriginQuery.state = false := by
  have requestEq : Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.request [] (.base "Proc")
      GeneralRho.FrontierControls.duplicates =
        GeneralRho.FrontierControls.literalRequest GeneralRho.FrontierControls.duplicates := by
    rw [Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.actual_request]
    exact GeneralRho.FrontierControls.actual_request _
  simp only [duplicateOriginQuery, Generated.searchModal]
  rw [requestEq]
  rw [GeneralRho.FrontierControls.literal_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem early_stop_does_not_claim_absence :
    (equationRun 0).result = .unknown ∧
      (GeneralOccurrenceSemantics.gslt Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.runtimePlan []
        Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.carrier).Step Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.other
          Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha :=
  ⟨equation_query_is_still_unknown_without_budget, Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.other_steps_alpha⟩

end Mettapedia.OSLF.NativeTypes.Modal.QuerySearchControls
