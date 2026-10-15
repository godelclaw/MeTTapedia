import Mettapedia.OSLF.Syntax.RhoScopedParallelModalAdequacy
import Mettapedia.OSLF.Syntax.RhoScopedParallelReactiveControls
import Mettapedia.OSLF.Syntax.RhoScopedEquationInteractionControls

/-!
# Actual interaction queries separate bare reduction agreement in rho

A waiting input and zero are bisimilar in the independently defined bare
communication relation. The finite query providing an actual matching output
separates them in the derived least-context system. A nonconstant postcondition
accepts a returned inert process and rejects a process with immediate COMM.
The source equations and all binding scopes remain part of each statement.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedParallelModalControls

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelContexts RhoScopedParallelEvents RhoScopedParallelReactiveSystem
open RhoScopedParallelReactiveControls RhoScopedEquationEventControls RhoScopedParallelModalAdequacy
open Mettapedia.GSLT

theorem core_occurrence_inventory {context : Ctx sig}
    (event : Occurrence sourceRules core context) :
    0 < RhoSourceInputInventory.count (event.sourceClass rhoSourceE) ∧
      0 < RhoSourceOutputPredicate.count (event.sourceClass rhoSourceE) := by
  rcases event with ⟨⟨index, allowed⟩, holeContext, root, path, permission⟩
  cases index with
  | communication =>
      let witness : ScopedEquationEvents.Event RhoScopedEquationEventControls.rules
          parallelPermission (context, Srt.pr) :=
        ⟨0, holeContext, root, path, permission⟩
      exact ⟨RhoSourceInputInventory.event_source_has_input witness,
        RhoScopedEquationEventControls.event_source_has_output witness⟩
  | reflection => exact False.elim allowed

theorem core_step_inventory {context : Ctx sig} {first second : Process context}
    (step : RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := core) first second) :
    0 < RhoSourceInputInventory.count first ∧ 0 < RhoSourceOutputPredicate.count first := by
  obtain ⟨event, sourceRead, _⟩ := step
  exact sourceRead ▸ core_occurrence_inventory event

/-- This theory forgets interaction labels from the independently authored event support. -/
def reductionTheory (context : Ctx sig) : GSLT where
  Term := Process context
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := core)
  rewrites_resp_left := by
    rintro first _ second rfl firing
    exact ⟨second, firing, rfl⟩
  rewrites_resp_right := by
    rintro first second _ firing rfl
    exact firing

def WithoutOutput {context : Ctx sig} (first second : Process context) : Prop :=
  RhoSourceOutputPredicate.count first = 0 ∧ RhoSourceOutputPredicate.count second = 0

theorem withoutOutput_isBisimulation (context : Ctx sig) :
    (reductionTheory context).IsBisimulation WithoutOutput := by
  constructor
  · intro first second pair next firing
    have positive := (core_step_inventory firing).2
    rw [pair.1] at positive
    omega
  · intro first second pair next firing
    have positive := (core_step_inventory firing).2
    rw [pair.2] at positive
    omega

theorem input_zero_reduction_bisimilar :
    (reductionTheory []).Bisimilar (project waitingInput) (zero []) :=
  ⟨WithoutOutput, withoutOutput_isBisimulation [], rfl, rfl⟩

def outputQuery : Finitary.Formula [] :=
  .diamond (arrow (project RhoSourceOutputPredicate.output)) .top

theorem input_answers_outputQuery :
    Finitary.Holds sourceRules core outputQuery (project waitingInput) := by
  apply (Finitary.holds_iff_interface sourceRules core outputQuery _).mpr
  exact ⟨arrow (zero []), actual_comm_transition, trivial⟩

theorem zero_rejects_outputQuery : ¬ Finitary.Holds sourceRules core outputQuery (zero []) := by
  intro holds
  obtain ⟨next, firing, _⟩ :=
    Complete.diamond_supplies_actual_event sourceRules core
      (project RhoSourceOutputPredicate.output) .top (zero []) holds
  have positive := (core_step_inventory firing).1
  rw [join_zero_left] at positive
  change 0 < (0 : Nat) at positive
  omega

theorem input_zero_not_finitary_equivalent :
    ¬ Finitary.LogicallyEquivalent sourceRules core (project waitingInput) (zero []) := by
  intro equivalent
  exact zero_rejects_outputQuery ((equivalent outputQuery).mp input_answers_outputQuery)

theorem input_zero_not_ipo_bisimilar :
    ¬ Bisimilar (rules := sourceRules) (admitted := core) (project waitingInput) (zero []) :=
  fun related => input_zero_not_finitary_equivalent
    (Finitary.logicallyEquivalent_of_bisimilar sourceRules core related)

/-- This postcondition observes dynamics and is not a state-equality oracle. -/
def noImmediateCommunication : Finitary.Formula [] :=
  .neg (.diamond (𝟙 (interface [])) .top)

theorem zero_satisfies_noImmediateCommunication :
    Finitary.Holds sourceRules core noImmediateCommunication (zero []) := by
  apply (Finitary.holds_iff_interface sourceRules core noImmediateCommunication _).mpr
  rintro ⟨next, firing, _⟩
  have positive := (core_step_inventory ((step_iff_actIPO_identity _ _).mpr firing)).2
  change 0 < (0 : Nat) at positive
  omega

theorem communication_source_rejects_noImmediateCommunication :
    ¬ Finitary.Holds sourceRules core noImmediateCommunication commRoot.source := by
  intro holds
  have cannot := (Finitary.holds_iff_interface sourceRules core noImmediateCommunication _).mp holds
  apply cannot
  refine ⟨arrow (zero []), ?_, trivial⟩
  apply (step_iff_actIPO_identity _ _).mp
  exact (step_iff_root_surrounding _ _).mpr
    ⟨commRoot, zero [], (join_zero_right _).symm, (join_zero_right _).symm⟩

theorem input_receives_an_inert_result :
    Finitary.Holds sourceRules core
      (.diamond (arrow (project RhoSourceOutputPredicate.output)) noImmediateCommunication)
      (project waitingInput) := by
  apply (Finitary.holds_iff_interface sourceRules core _ _).mpr
  exact ⟨arrow (zero []), actual_comm_transition,
    (Finitary.holds_iff_interface sourceRules core noImmediateCommunication _).mp
      zero_satisfies_noImmediateCommunication⟩

theorem false_postcondition_rejected :
    ¬ Finitary.Holds sourceRules core
      (.diamond (arrow (project RhoSourceOutputPredicate.output)) (.neg .top))
      (project waitingInput) := by
  intro holds
  obtain ⟨_, _, fails⟩ := (Finitary.holds_iff_interface sourceRules core _ _).mp holds
  exact fails trivial

end Mettapedia.OSLF.Binding.RhoScopedParallelModalControls
