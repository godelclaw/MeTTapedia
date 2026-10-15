import Mettapedia.OSLF.Syntax.RhoScopedEquationContextControls
import Mettapedia.OSLF.Syntax.ScopedBindingEquationEventPresheaf

/-!+# Authored rho communication occurrences modulo the actual source equations

Two authored occurrences of the same communication schema have the same
source and target classes and different retained origins. Parallel positions
are explicitly permitted; an input-body position requires a different
permission profile. Every admitted communication source has a genuine output
occurrence, so null cannot acquire a communication merely by equation
saturation. Independently supplied target predicates are actually consulted.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedEquationEventControls

open _root_.CategoryTheory RhoSchema ScopedEncoding ScopedEquationContexts ScopedEquationEvents
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT IndexedContextEventSaturation
open RhoScopedEquationContextControls

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

/-- Two declaration occurrences retain independent indices. -/
def rules : Fin 2 → UnpositionedRewrite schemaSig := fun _ => comm.unpositioned

/-- The reaction positions in the parallel-only profile. -/
def parallelPermission : PositionPermission sig := fun _ operator _ =>
  match operator with
  | .par => True
  | _ => False

/-- A separate profile explicitly grants all constructor positions. -/
def allPositions : PositionPermission sig := fun _ _ _ => True

def discardRoot : ContextualRootEvents.Instance comm.unpositioned [] where
  body := ContextualAssignment.ofClosed contDiscard []
  close := closeComm

def waitingInput : Term sig [] Srt.pr :=
  .op Op.inp (.cons chan (.cons (.op Op.nil .nil) .nil))

def sourceProcess : Term sig [] Srt.pr :=
  .op Op.par (.cons RhoSourceOutputPredicate.output (.cons waitingInput .nil))

theorem discard_root_source : discardRoot.source = sourceProcess := rfl

theorem discard_root_target : discardRoot.target = nilP := rfl

def occurrence (index : Fin 2) : Event rules parallelPermission ([], Srt.pr) where
  index := index
  holeContext := []
  root := discardRoot
  context := .nil
  permitted := .nil _

theorem actual_source (index : Fin 2) : (occurrence index).source = sourceProcess := rfl

theorem actual_target (index : Fin 2) : (occurrence index).target = nilP := rfl

theorem actual_closed_root_step : RootStep comm sourceProcess nilP :=
  rootStep_of_instance comm { body := contDiscard, close := closeComm }

def observations {scope : ScopedEquationContexts.ContextCategory sig}
    (threshold : Nat) (value : State rhoSourceE scope) : Prop :=
  threshold ≤ RhoSourceOutputPredicate.count value

def dynamics := ScopedEquationSaturation.dynamics rhoSourceE rules parallelPermission observations

def firing (index : Fin 2) :
    dynamics.Firing (𝟙 (processInterface []))
      (Quotient.mk _ sourceProcess) (Quotient.mk _ nilP) where
  event := occurrence index
  source_eq := (fillClass_identity rhoSourceE _).symm
  target_eq := rfl

theorem communication_supplies_step :
    dynamics.Step (interface := processInterface [])
      (Quotient.mk _ sourceProcess) (Quotient.mk _ nilP) :=
  (dynamics.firing_iff_step _ _ _).mp ⟨firing 0⟩

theorem different_origins : occurrence 0 ≠ occurrence 1 := by
  intro same
  have indices : (0 : Fin 2) = 1 := congrArg Event.index same
  exact (by decide : (0 : Fin 2) ≠ 1) indices

theorem same_complete_endpoints :
    (occurrence 0).sourceClass rhoSourceE = (occurrence 1).sourceClass rhoSourceE ∧
      (occurrence 0).targetClass rhoSourceE = (occurrence 1).targetClass rhoSourceE := ⟨rfl, rfl⟩

theorem different_firing_receipts : firing 0 ≠ firing 1 := by
  intro same
  exact different_origins (congrArg Data.Firing.event same)

theorem root_source_has_output {context : Ctx sig}
    (root : ContextualRootEvents.Instance comm.unpositioned context) :
    0 < outputCount root.source := by
  change 0 < outputCount (ContextualAssignment.instantiate root.body
    (fun _ position => .var position) root.close commLhs)
  simp only [commLhs, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    liftSub, outputCount, outputCountArgs, outputHeadCount]
  omega

theorem frame_retains_output {source target : Scope sig} (frame : BindingFrame sig source target)
    (value : Term sig source.1 source.2) :
    outputCount value ≤ outputCount (frame.fill value) := by
  cases frame with
  | slot context sort operator position siblings =>
    cases operator <;> fin_cases position <;>
      simp [BindingFrame.fill, assembleArguments, outputCount, outputCountArgs, outputHeadCount] <;>
      omega

theorem context_retains_output {source target : Scope sig}
    (context : BindingContext sig source target) (value : Term sig source.1 source.2) :
    outputCount value ≤ outputCount (fillContext context value) := by
  induction context with
  | nil => exact Nat.le_refl _
  | cons previous frame inductionHypothesis =>
    exact inductionHypothesis.trans (frame_retains_output frame _)

/-- This statement covers all actual opened binder contexts and paths. -/
theorem event_source_has_output {scope : Scope sig} (event : Event rules parallelPermission scope) :
    0 < RhoSourceOutputPredicate.count (event.sourceClass rhoSourceE) :=
  (root_source_has_output event.root).trans_le (context_retains_output event.context _)

theorem null_has_no_communication {context : Ctx sig}
    (target : TermQ rhoSourceE context Srt.pr) :
    ¬ dynamics.Step (interface := processInterface context)
      (Quotient.mk _ (RhoEquationConstructorControls.null : Term sig context Srt.pr)) target := by
  rintro ⟨event, sourceEq, _⟩
  change event.sourceClass rhoSourceE = _ at sourceEq
  have positive := event_source_has_output event
  rw [sourceEq] at positive
  change 0 < (0 : Nat) at positive
  omega

theorem waiting_input_has_no_communication (target : TermQ rhoSourceE [] Srt.pr) :
    ¬ dynamics.Step (interface := processInterface []) (Quotient.mk _ waitingInput) target := by
  rintro ⟨event, sourceEq, _⟩
  change event.sourceClass rhoSourceE = _ at sourceEq
  have positive := event_source_has_output event
  rw [sourceEq] at positive
  change 0 < (0 : Nat) at positive
  omega

theorem target_predicate_satisfied :
    ∃ supplied : dynamics.Firing (𝟙 (processInterface []))
        (Quotient.mk _ sourceProcess) (Quotient.mk _ nilP),
      RhoSourceOutputPredicate.count (supplied.event.targetClass rhoSourceE) = 0 :=
  ⟨firing 0, rfl⟩

theorem target_predicate_rejected :
    ¬ ∃ supplied : dynamics.Firing (𝟙 (processInterface []))
        (Quotient.mk _ sourceProcess) (Quotient.mk _ nilP),
      RhoSourceOutputPredicate.count (supplied.event.targetClass rhoSourceE) = 1 := by
  rintro ⟨supplied, failed⟩
  have targetEq : supplied.event.targetClass rhoSourceE = (Quotient.mk _ nilP) :=
    supplied.target_eq
  rw [targetEq] at failed
  change (0 : Nat) = 1 at failed
  cases failed

/-- The contextual observation is nonconstant on the actual equation classes. -/
theorem observations_separate_output_and_null :
    ¬ dynamics.Bisimilar (processInterface [])
      (Quotient.mk _ RhoSourceOutputPredicate.output) (Quotient.mk _ nilP) := by
  intro related
  have comparison := dynamics.complete_observation related (𝟙 _) 1
  have before : observations (scope := processInterface []) 1
      ((ScopedEquationContexts.action rhoSourceE).map (𝟙 _) (Quotient.mk _
        RhoSourceOutputPredicate.output)) := by
    change (1 : Nat) ≤ 1
    exact Nat.le_refl _
  have after := comparison.mp before
  change (1 : Nat) ≤ 0 at after
  omega

end Mettapedia.OSLF.Binding.RhoScopedEquationEventControls
