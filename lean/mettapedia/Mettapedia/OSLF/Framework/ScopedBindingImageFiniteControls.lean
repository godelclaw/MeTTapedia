import Mettapedia.OSLF.Framework.ScopedBindingImageFinite
import Mettapedia.OSLF.Syntax.ScopedBindingPermittedSearchControls

/-!
# Actual binder firings, complete targets and finite modal adequacy

The independently authored binder firing is observed by a complete context
diamond. A numeral with no matching declaration cannot answer that diamond.
The proper slot kit retains the binder firing; removing its binder slot
eliminates the reaction despite retaining the identity label. Ambient and
permission-indexed adequacy cover every actual category interface, including
the distinguished origin and its genuine cross-interface base firing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding.ImageFiniteControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.InterfaceModalLogic
open FiringSearchControls PermittedSearchControls

local instance bindingFiniteControlQuiver : Quiver (Scope language) := bindingFrameQuiver language

def observedRules := FramePermission.rawRules (bindingAction language)
  (fun declaration => declaration ∈ declarations)

def terminal : Binding.Term language [] () := number 9

theorem complete_target_list_retains_duplicates :
    bindingFiringTargets agent identityLabel declarations =
      [leftResult, rightResult, leftResult, rightResult] := by decide

theorem complete_permitted_target_list_retains_origins :
    bindingPermittedFiringTargets (permission := leftKit) agent identityLabel declarations =
      [leftResult, leftResult] := by decide

theorem terminal_complete_target_list_is_empty :
    bindingFiringTargets terminal identityLabel declarations = [] := by decide

theorem actual_binder_firing : ActIPO observedRules (bindingContextArrow identityLabel)
    (bindingTermArrow agent) (bindingTermArrow leftResult) :=
  FramePermission.rawFiring_iff_actIPO.mp ⟨independentLeftFiring⟩

theorem terminal_cannot_match (next : Binding.Term language [] ()) :
    ¬ActIPO observedRules (bindingContextArrow identityLabel)
      (bindingTermArrow terminal) (bindingTermArrow next) := by
  intro actual
  have member := (mem_bindingFiringTargets (source := ([], ())) (target := ([], ()))
    (declarations := declarations) terminal identityLabel next).mpr
      ((FramePermission.rawFiring_iff_actIPO (action := bindingAction language)
        (admitted := fun declaration => declaration ∈ declarations)
        (source := ([], ())) (target := ([], ())) (agent := terminal) (next := next)
        (label := bindingContextArrow identityLabel)).mpr actual)
  rw [terminal_complete_target_list_is_empty] at member
  exact List.not_mem_nil member

def binderDiamond : Formula (BindingContextObject language) (bindingInterface language ([], ())) :=
  .diamond (bindingContextArrow identityLabel) .top

theorem actual_diamond_holds : Holds observedRules binderDiamond (bindingTermArrow agent) :=
  ⟨bindingTermArrow leftResult, actual_binder_firing, by trivial⟩

theorem terminal_rejects_actual_diamond :
    ¬Holds observedRules binderDiamond (bindingTermArrow terminal) := by
  rintro ⟨next, actual, _postcondition⟩
  cases next with
  | value supplied => exact terminal_cannot_match supplied actual

theorem actual_agents_are_not_bisimilar :
    ¬IPOBisimilar observedRules (bindingTermArrow (S := language) (scope := ([], ())) agent)
      (bindingTermArrow (S := language) (scope := ([], ())) terminal) := by
  intro related
  have compared := logicallyEquivalent_of_ipoBisimilar observedRules related
  exact terminal_rejects_actual_diamond ((compared binderDiamond).mp actual_diamond_holds)

theorem every_interface_has_complete_ambient_adequacy {interface : BindingContextObject language}
    (first second : bindingOrigin language ⟶ interface) :
    IPOBisimilar observedRules first second ↔ LogicallyEquivalent observedRules first second :=
  bindingRawRules_modal_adequacy declarations first second

theorem every_interface_has_complete_proper_kit_adequacy
    {interface : PermittedContextObject language leftKit}
    (first second : permittedOrigin language leftKit ⟶ interface) :
    IPOBisimilar (FramePermission.rules (framePermission language leftKit) (bindingAction language)
        (fun declaration => declaration ∈ declarations)) first second ↔
      LogicallyEquivalent (FramePermission.rules (framePermission language leftKit) (bindingAction language)
        (fun declaration => declaration ∈ declarations)) first second :=
  bindingPermittedRules_modal_adequacy declarations leftKit first second

theorem permitted_actual_binder_firing :
    ActIPO (FramePermission.rules (framePermission language leftKit) (bindingAction language)
        (fun declaration => declaration ∈ declarations))
      (permittedContextArrow identityLabel identity_label_is_allowed)
      (permittedTermArrow agent) (permittedTermArrow leftResult) :=
  FramePermission.firing_iff_actIPO.mp ⟨selectedFiring⟩

theorem forbidden_binder_blocks_every_complete_target (next : Binding.Term language [] ()) :
    ¬ActIPO (FramePermission.rules (framePermission language noBinderKit) (bindingAction language)
        (fun declaration => declaration ∈ declarations))
      (permittedContextArrow identityLabel no_binder_kit_still_permits_the_supplied_label)
      (permittedTermArrow agent) (permittedTermArrow next) := by
  intro actual
  exact actual_restricted_firing_is_impossible_without_its_binder
    ⟨next, FramePermission.firing_iff_actIPO.mpr actual⟩

theorem actual_origin_cross_interface_firing :
    ActIPO observedRules (bindingTermArrow (declaration 3).redex)
      (𝟙 (bindingOrigin language)) (bindingTermArrow (declaration 3).reactum) := by
  refine ⟨(declaration 3).rawRule (bindingAction language),
    ⟨declaration 3, List.mem_cons_self, rfl⟩, 𝟙 _, rfl, ?_, rfl⟩
  intro candidate
  refine ⟨candidate.inr, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact candidate.comm.symm.trans (Category.id_comp _)
  · exact Category.id_comp _
  · exact candidate.fac_right
  · intro alternative compatible
    exact (Category.id_comp alternative).symm.trans compatible.2.1

theorem actual_origin_retains_the_bound_reactum :
    ∃ selected, selected ∈ declarations ∧
      (⟨([()], ()), (declaration 3).reactum⟩ :
        (scope : Scope language) × (bindingAction language).Value scope) =
        ⟨selected.scope, selected.reactum⟩ :=
  FramePermission.origin_actIPO_target_readout _ _ actual_origin_cross_interface_firing

end Mettapedia.OSLF.Binding.ScopedEncoding.ImageFiniteControls
