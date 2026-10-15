import Mettapedia.OSLF.Syntax.RhoSourceInputInventory

/-!+# Reduction agreement and actual interaction separate in rho

An inert input and null belong to a checked ordinary reduction bisimulation
for the declared output observations. Adding the same matching output admits
an actual communication only for the input. Hence that reduction relation is
not closed under contexts, and the independently generated saturated relation
separates the two processes. All statements use the complete source equations
and the explicitly parallel-only reaction profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedEquationInteractionControls

open _root_.CategoryTheory RhoSchema ScopedEncoding ScopedEquationContexts ScopedEquationEvents
open RhoScopedEquationContextControls RhoScopedEquationEventControls
open RhoEquationConstructorControls
open Mettapedia.GSLT IndexedContextEventSaturation

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

def withoutOutput (scope : ScopedEquationContexts.ContextCategory sig)
    (left right : State rhoSourceE scope) : Prop :=
  RhoSourceOutputPredicate.count left = 0 ∧ RhoSourceOutputPredicate.count right = 0

theorem withoutOutput_reduction_bisimulation : dynamics.ReductionBisimulation withoutOutput := by
  intro scope left right pair
  refine ⟨?_, ?_, ?_⟩
  · rintro next ⟨event, sourceEq, _⟩
    change event.sourceClass rhoSourceE = left at sourceEq
    have positive := event_source_has_output event
    rw [sourceEq, pair.1] at positive
    omega
  · rintro next ⟨event, sourceEq, _⟩
    change event.sourceClass rhoSourceE = right at sourceEq
    have positive := event_source_has_output event
    rw [sourceEq, pair.2] at positive
    omega
  · intro threshold
    change threshold ≤ RhoSourceOutputPredicate.count left ↔
      threshold ≤ RhoSourceOutputPredicate.count right
    rw [pair.1, pair.2]

theorem input_null_reduction_pair : withoutOutput (processInterface [])
    (project waitingInput) (project nilP) := ⟨rfl, rfl⟩

def twoProcesses (first second : Term sig [] Srt.pr) : Sub sig [Srt.pr, Srt.pr] []
  | _, .zero => first
  | _, .succ .zero => second

theorem parallel_commutes (first second : Term sig [] Srt.pr) :
    EqClosure rhoSourceE (parallel first second) (parallel second first) := by
  simpa [rhoSourceE, commPar, parallel, instantiate, instantiateArgs, bind, bindArgs,
    liftSub, twoProcesses] using
    (EqClosure.ax_closed (E := rhoSourceE) 0 contDiscard (twoProcesses first second))

def matchingOutputContext : BindingContext sig ([], Srt.pr) ([], Srt.pr) :=
  single (parallelFrame [] RhoSourceOutputPredicate.output)

theorem input_enabled_by_matching_output :
    dynamics.Step (interface := processInterface [])
      (fillClass rhoSourceE matchingOutputContext (project waitingInput)) (project nilP) := by
  refine ⟨occurrence 0, ?_, rfl⟩
  exact Quotient.sound (parallel_commutes RhoSourceOutputPredicate.output waitingInput)

theorem null_not_enabled_by_same_output (next : TermQ rhoSourceE [] Srt.pr) :
    ¬ dynamics.Step (interface := processInterface [])
      (fillClass rhoSourceE matchingOutputContext (project nilP)) next := by
  rintro ⟨event, sourceEq, _⟩
  change event.sourceClass rhoSourceE = _ at sourceEq
  have positive := RhoSourceInputInventory.event_source_has_input event
  rw [sourceEq] at positive
  change 0 < (0 : Nat) at positive
  omega

/-- Reduction observations alone do not license replacement in an interacting context. -/
theorem input_null_not_saturated_bisimilar :
    ¬ dynamics.Bisimilar (processInterface []) (project waitingInput) (project nilP) := by
  intro related
  obtain ⟨matched, step, _⟩ :=
    dynamics.forward related matchingOutputContext input_enabled_by_matching_output
  exact null_not_enabled_by_same_output matched step

theorem reduction_bisimulation_not_context_closed :
    ¬ Data.ContextClosed (states := ScopedEquationContexts.action rhoSourceE) withoutOutput := by
  intro closed
  have saturated := dynamics.largest withoutOutput_reduction_bisimulation closed
    (processInterface []) (project waitingInput) (project nilP) input_null_reduction_pair
  exact input_null_not_saturated_bisimilar saturated

/-- Equation-class context identification retains the interaction separator. -/
theorem quotient_input_null_not_bisimilar :
    ¬ (IndexedContextActionQuotient.quotientData dynamics).Bisimilar
      ((IndexedContextActionQuotient.projection (ScopedEquationContexts.action rhoSourceE)).obj
        (processInterface [])) (project waitingInput) (project nilP) := by
  intro related
  exact input_null_not_saturated_bisimilar
    (IndexedContextActionQuotient.raw_bisimilar_of_quotient dynamics related)

end Mettapedia.OSLF.Binding.RhoScopedEquationInteractionControls
