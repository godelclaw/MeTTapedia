import Mettapedia.OSLF.Syntax.ScopedBindingFiringSubstitutionCoherence
import Mettapedia.OSLF.Syntax.ScopedBindingFiringSubstitutionControls

/-!
# Two genuine substitution routes through a complete binder firing

The first substitution sends the two original free variables to different
open terms. The second closes the remaining variable. The two-step and
direct constructions have the same entire firing readout, including both
paths and the protected reactum variable. Origins remain distinct even
when every term and path reading agrees. The authored original rule family
is not itself closed under these substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding.FiringCoherenceControls

open Mettapedia.CategoryTheory.GroundPath
open Controls FiringSubstitutionControls

local instance bindingCoherenceControlsQuiver : Quiver (Scope toy) := bindingFrameQuiver toy

def first : Binding.Sub toy [(), ()] [()] := fun sort position => by
  cases sort
  cases position with
  | zero => exact .var .zero
  | succ next =>
    cases next with
    | zero => exact pair (.var .zero) (number 2)
    | succ impossible => cases impossible

def second : Binding.Sub toy [()] [] := fun sort position => by
  cases sort
  cases position with
  | zero => exact number 11
  | succ impossible => cases impossible

def direct : Binding.Sub toy [(), ()] [] :=
  fun sort position => Binding.bind second (first sort position)

def firstFiring (origin : Nat) := rawFiringSubstitution (oldFiring origin) [()] first
def twoStepFiring (origin : Nat) := rawFiringSubstitution (firstFiring origin) [] second
def directFiring (origin : Nat) := rawFiringSubstitution (oldFiring origin) [] direct

def retainedSecondReceipt (origin : Nat) : BindingFiringSubstitutionReceipt
    (instantiatedDeclarations admitted)
    (Binding.bind (substituteContext left [()] first).holeVariables agent)
    (substituteContext left [()] first).path (Binding.bind first result) where
  original := firstFiring origin
  destination := []
  substitution := second

def firstPermittedFiring (origin : Nat) :=
  permittedFiringSubstitution permission left_allowed (permittedOldFiring origin) [()] first

def twoStepPermittedFiring (origin : Nat) :=
  permittedFiringSubstitution permission
    ((substituteContext_permission_iff permission left [()] first).mpr left_allowed)
    (firstPermittedFiring origin) [] second

def directPermittedFiring (origin : Nat) :=
  permittedFiringSubstitution permission left_allowed (permittedOldFiring origin) [] direct

theorem complete_identity_route (origin : Nat) :
    rawFiringReadout (rawFiringSubstitution (oldFiring origin) [(), ()] (fun _ value => .var value)) =
      rawFiringReadout (oldFiring origin) := rawFiringSubstitution_identity_readout (oldFiring origin)

theorem complete_composition_route (origin : Nat) :
    rawFiringReadout (twoStepFiring origin) = rawFiringReadout (directFiring origin) :=
  rawFiringSubstitution_composition_readout (oldFiring origin) [()] [] first second

theorem both_actual_permitted_routes_agree_completely (origin : Nat) :
    rawFiringReadout (twoStepPermittedFiring origin).raw =
      rawFiringReadout (directPermittedFiring origin).raw :=
  permittedFiringSubstitution_composition_readout permission left_allowed
    (permittedOldFiring origin) [()] [] first second

theorem both_complete_path_readouts_agree (origin : Nat) :
    (rawFiringReadout (twoStepFiring origin)).input = (rawFiringReadout (directFiring origin)).input ∧
      (rawFiringReadout (twoStepFiring origin)).rule = (rawFiringReadout (directFiring origin)).rule :=
  ⟨congrArg BindingFiringReadout.input (complete_composition_route origin),
    congrArg BindingFiringReadout.rule (complete_composition_route origin)⟩

theorem first_rule_keeps_the_complete_changed_redex (origin : Nat) :
    (firstFiring origin).declaration.redex =
      (pair (.var (.succ .zero)) (number 2) : Binding.Term toy [(), ()] ()) := rfl

theorem composed_rule_keeps_the_complete_redex (origin : Nat) :
    (twoStepFiring origin).declaration.redex = (pair (number 11) (number 2) : Binding.Term toy [()] ()) := rfl

theorem composed_rule_keeps_the_protected_reactum (origin : Nat) :
    (twoStepFiring origin).declaration.reactum = (Binding.Term.var .zero : Binding.Term toy [()] ()) := rfl

theorem independently_supplied_target_after_two_steps :
    Binding.bind second (Binding.bind first result) =
      (pair (abstraction (number 11)) (abstraction (.var .zero)) : Binding.Term toy [] ()) := rfl

theorem target_agrees_with_the_direct_route :
    Binding.bind second (Binding.bind first result) = Binding.bind direct result :=
  Binding.bind_comp first second result

theorem both_whole_paths_still_have_two_frames (origin : Nat) :
    (rawFiringReadout (twoStepFiring origin)).input.2.2.length = 2 ∧
      (rawFiringReadout (twoStepFiring origin)).rule.2.2.2.length = 2 := ⟨rfl, rfl⟩

theorem second_receipt_retains_the_entire_first_firing (origin : Nat) :
    (retainedSecondReceipt origin).original = firstFiring origin := rfl

theorem complete_second_receipt_is_the_actual_two_step_firing (origin : Nat) :
    (retainedSecondReceipt origin).result = twoStepFiring origin := rfl

theorem duplicate_origins_still_have_distinct_complete_readouts :
    rawFiringReadout (twoStepFiring 3) ≠ rawFiringReadout (twoStepFiring 9) := by
  intro same
  have impossible : (3 : Nat) = 9 := congrArg BindingFiringReadout.origin same
  cases impossible

theorem duplicate_origins_have_the_same_whole_input_rule_and_target :
    (rawFiringReadout (twoStepFiring 3)).input = (rawFiringReadout (twoStepFiring 9)).input ∧
      (rawFiringReadout (twoStepFiring 3)).rule = (rawFiringReadout (twoStepFiring 9)).rule ∧
      (rawFiringReadout (twoStepFiring 3)).target = (rawFiringReadout (twoStepFiring 9)).target :=
  ⟨rfl, rfl, rfl⟩

theorem the_original_authored_rule_family_is_not_substitution_closed (origin : Nat) :
    ¬admitted (directFiring origin).declaration := by
  rintro ⟨otherOrigin, same⟩
  have differentContexts : ([()] : Binding.Ctx toy) = [(), (), ()] :=
    congrArg (fun selected => selected.scope.1) same
  cases differentContexts

theorem the_actual_instantiated_rule_family_flattens (origin : Nat) :
    instantiatedDeclarations admitted (twoStepFiring origin).declaration :=
  (instantiatedDeclarations_iterated_iff admitted (twoStepFiring origin).declaration).mp
    (twoStepFiring origin).admitted

theorem dropping_a_redex_coordinate_changes_the_actual_readout (origin : Nat) :
    (twoStepFiring origin).declaration.redex ≠ (number 11 : Binding.Term toy [()] ()) := by
  intro same
  cases same

theorem skipping_the_changed_second_substitution_changes_the_actual_result :
    (Binding.bind direct result : Binding.Term toy [] ()) ≠ Binding.bind closing result := by
  intro same
  cases same

end Mettapedia.OSLF.Binding.ScopedEncoding.FiringCoherenceControls
