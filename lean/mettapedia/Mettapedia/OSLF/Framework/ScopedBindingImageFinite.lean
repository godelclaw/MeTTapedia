import Mettapedia.OSLF.Syntax.ScopedBindingFiringTargets
import Mettapedia.CategoryTheory.GroundPathOriginFiring
import Mettapedia.GSLT.Logic.InterfaceModalAdequacy

/-!
# Earned all-interface image finiteness for literal binding rules

The finite, complete target search supplies ordinary term-interface fibres.
The distinguished origin has a different argument: IPO minimality permits
only complete authored reacta as targets. Both cases belong to the actual
ground/context category, including every intrinsically scoped binder path.
The resulting modal adequacy quantifies over every formula and interface.

The finite declaration list consists of actual instantiated rules. No
schema-instance bound, equation quotient, all-label branching bound or
funded observer claim is inferred from this construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RedexRelativeCongruence Mettapedia.GSLT.InterfaceModalLogic

universe r

variable {S : Binding.Signature} {Origins : Type r}

local instance bindingImageFiniteQuiver : Quiver (Scope S) := bindingFrameQuiver S

variable [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)]
variable (declarations : List (FramePermission.Declaration (bindingAction S) Origins))

theorem bindingRawRules_imageFinite :
    ImageFinite (FramePermission.rawRules (bindingAction S)
      (fun declaration => declaration ∈ declarations)) := by
  intro first last label agent
  cases last with
  | origin =>
    apply Set.finite_empty.subset
    rintro next ⟨rule, ⟨declaration, _selected, rfl⟩, reaction, _square, _minimal, _result⟩
    cases reaction
  | interface target =>
    cases first with
    | origin =>
      cases agent
      refine ((FramePermission.origin_actIPO_values_finite declarations label).image
        (fun next => bindingTermArrow next)).subset ?_
      intro next actual
      cases next with
      | value supplied => exact ⟨supplied, actual, rfl⟩
    | interface source =>
      cases agent with
      | value supplied =>
        cases label with
        | context path =>
          refine ((bindingRawFiring_targets_finite (declarations := declarations) supplied path).image
            (fun next => bindingTermArrow next)).subset ?_
          intro next actual
          cases next with
          | value targetValue =>
            exact ⟨targetValue, FramePermission.rawFiring_iff_actIPO.mpr actual, rfl⟩

theorem bindingRawRules_modal_adequacy {interface : BindingContextObject S}
    (first second : bindingOrigin S ⟶ interface) :
    IPOBisimilar (FramePermission.rawRules (bindingAction S)
        (fun declaration => declaration ∈ declarations)) first second ↔
      LogicallyEquivalent (FramePermission.rawRules (bindingAction S)
        (fun declaration => declaration ∈ declarations)) first second :=
  ipoBisimilar_iff_logicallyEquivalent _ (bindingRawRules_imageFinite declarations) first second

variable (permission : SlotPermission S)

theorem bindingPermittedRules_imageFinite :
    ImageFinite (FramePermission.rules (framePermission S permission) (bindingAction S)
      (fun declaration => declaration ∈ declarations)) := by
  intro first last label agent
  rcases last with ⟨last⟩
  cases last with
  | origin =>
    apply Set.finite_empty.subset
    rintro next ⟨rule, ⟨declaration, _selected, rfl⟩, reaction, _square, _minimal, _result⟩
    rcases reaction with ⟨reaction, _allowed⟩
    cases reaction
  | interface target =>
    rcases first with ⟨first⟩
    cases first with
    | origin =>
      rcases agent with ⟨agent, _allowed⟩
      cases agent
      refine ((FramePermission.permitted_origin_actIPO_values_finite declarations label).image
        (fun next => permittedTermArrow (permission := permission) next)).subset ?_
      intro next actual
      rcases next with ⟨next, _nextAllowed⟩
      cases next with
      | value supplied => exact ⟨supplied, actual, Subtype.ext rfl⟩
    | interface source =>
      rcases agent with ⟨agent, _allowed⟩
      cases agent with
      | value supplied =>
        rcases label with ⟨label, _labelAllowed⟩
        cases label with
        | context path =>
          refine ((bindingRawFiring_targets_finite (declarations := declarations) supplied path).image
            (fun next => permittedTermArrow (permission := permission) next)).subset ?_
          intro next actual
          rcases next with ⟨next, _nextAllowed⟩
          cases next with
          | value targetValue =>
            obtain ⟨firing⟩ := FramePermission.firing_iff_actIPO.mpr actual
            exact ⟨targetValue, ⟨firing.raw⟩, Subtype.ext rfl⟩

theorem bindingPermittedRules_modal_adequacy {interface : PermittedContextObject S permission}
    (first second : permittedOrigin S permission ⟶ interface) :
    IPOBisimilar (FramePermission.rules (framePermission S permission) (bindingAction S)
        (fun declaration => declaration ∈ declarations)) first second ↔
      LogicallyEquivalent (FramePermission.rules (framePermission S permission) (bindingAction S)
        (fun declaration => declaration ∈ declarations)) first second :=
  ipoBisimilar_iff_logicallyEquivalent _ (bindingPermittedRules_imageFinite declarations permission)
    first second

end Mettapedia.OSLF.Binding.ScopedEncoding
