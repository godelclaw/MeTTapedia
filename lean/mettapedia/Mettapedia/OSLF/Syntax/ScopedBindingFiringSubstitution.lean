import Mettapedia.OSLF.Syntax.ScopedBindingIPOShape
import Mettapedia.OSLF.Syntax.ScopedBindingIdentityReactionSubstitution

/-!
# Substitution of complete binding firings

Every interface reaction is reconstructed as its actual context path.
Substituting the common outer context computes both inherited hole-variable
maps, instantiates the original complete declaration, and independently binds
the old target. The full matching and target squares follow from the filling
laws; minimality follows from the operator-and-slot characterization of IPOs.
The retained receipt keeps the entire old firing and supplied substitution.
The target rule family contains actual instances of admitted declarations;
closure of an independently fixed rule family is not asserted.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe r

variable {S : Binding.Signature}
local instance bindingFiringSubstitutionQuiver : Quiver (Scope S) := bindingFrameQuiver S

def bindingArrowPath {source target : Scope S}
    (arrow : bindingInterface S source ⟶ bindingInterface S target) :
    BindingContext S source target := by
  cases arrow with
  | context path => exact path

theorem bindingArrowPath_readout {source target : Scope S}
    (arrow : bindingInterface S source ⟶ bindingInterface S target) :
    bindingContextArrow (bindingArrowPath arrow) = arrow := by
  cases arrow
  rfl

variable {Origins : Type r}
variable {admitted : FramePermission.Declaration (bindingAction S) Origins → Prop}
variable {source target : Scope S}
variable {agent : Binding.Term S source.1 source.2} {next : Binding.Term S target.1 target.2}
variable {label : BindingContext S source target}

def rawFiringReactionPath
    (firing : FramePermission.RawFiring (admitted := admitted) agent
      (bindingContextArrow label) next) : BindingContext S firing.declaration.scope target :=
  bindingArrowPath firing.reaction

theorem rawFiring_path_square
    (firing : FramePermission.RawFiring (admitted := admitted) agent
      (bindingContextArrow label) next) :
    bindingTermArrow agent ≫ bindingContextArrow label =
      bindingTermArrow firing.declaration.redex ≫ bindingContextArrow (rawFiringReactionPath firing) := by
  rw [rawFiringReactionPath, bindingArrowPath_readout]
  exact firing.square

theorem rawFiring_path_minimal
    (firing : FramePermission.RawFiring (admitted := admitted) agent
      (bindingContextArrow label) next) :
    IsIdemPushout (bindingTermArrow agent) (bindingTermArrow firing.declaration.redex)
      (bindingContextArrow label) (bindingContextArrow (rawFiringReactionPath firing))
      (rawFiring_path_square firing) := by
  rcases firing with ⟨selected, member, reaction, square, minimal, targetRead⟩
  cases reaction with
  | context path =>
    change IsIdemPushout (valueArrow (bindingAction S) agent)
      (valueArrow (bindingAction S) selected.redex)
      (bindingContextArrow label) (contextArrow (bindingAction S) path) square
    exact minimal

theorem rawFiring_path_target
    (firing : FramePermission.RawFiring (admitted := admitted) agent
      (bindingContextArrow label) next) :
    next = fillContext (rawFiringReactionPath firing) firing.declaration.reactum := by
  have result := firing.target_readout
  rw [←bindingArrowPath_readout firing.reaction] at result
  exact Arrow.value.inj result

def firingSubstitutionInstance
    (firing : FramePermission.RawFiring (admitted := admitted) agent
      (bindingContextArrow label) next)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    BindingDeclarationInstance S Origins where
  original := firing.declaration
  destination := (substituteContext (rawFiringReactionPath firing) destination sigma).holeContext
  substitution := (substituteContext (rawFiringReactionPath firing) destination sigma).holeVariables

def rawFiringSubstitution
    (firing : FramePermission.RawFiring (admitted := admitted) agent
      (bindingContextArrow label) next)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    FramePermission.RawFiring
      (source := ((substituteContext label destination sigma).holeContext, source.2))
      (target := (destination, target.2)) (admitted := instantiatedDeclarations admitted)
      (Binding.bind (substituteContext label destination sigma).holeVariables agent)
      (bindingContextArrow (substituteContext label destination sigma).path)
      (Binding.bind sigma next) where
  declaration := (firingSubstitutionInstance firing destination sigma).realized
  admitted := ⟨firingSubstitutionInstance firing destination sigma, firing.admitted, rfl⟩
  reaction := bindingContextArrow
    (substituteContext (rawFiringReactionPath firing) destination sigma).path
  square := substituted_bound_square agent firing.declaration.redex label
    (rawFiringReactionPath firing) (rawFiring_path_square firing) destination sigma
  minimal := (binding_ipo_substitution_iff agent firing.declaration.redex label
    (rawFiringReactionPath firing) (rawFiring_path_square firing) destination sigma).mpr
      (rawFiring_path_minimal firing)
  target_readout := congrArg (bindingTermArrow (S := S) (scope := (destination, target.2)))
    ((congrArg (Binding.bind sigma) (rawFiring_path_target firing)).trans
      (substituteContext_fill (rawFiringReactionPath firing) destination sigma firing.declaration.reactum))

/-- Local input data retain the old complete occurrence and its substitution.
The transformed firing is constructed by `result`, not supplied as a field. -/
structure BindingFiringSubstitutionReceipt
    (admitted : FramePermission.Declaration (bindingAction S) Origins → Prop)
    {source target : Scope S} (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target) (next : Binding.Term S target.1 target.2) where
  original : FramePermission.RawFiring (admitted := admitted) agent (bindingContextArrow label) next
  destination : Binding.Ctx S
  substitution : Binding.Sub S target.1 destination

def BindingFiringSubstitutionReceipt.selected
    (receipt : BindingFiringSubstitutionReceipt admitted agent label next) :
    BindingDeclarationInstance S Origins :=
  firingSubstitutionInstance receipt.original receipt.destination receipt.substitution

def BindingFiringSubstitutionReceipt.result
    (receipt : BindingFiringSubstitutionReceipt admitted agent label next) :
    FramePermission.RawFiring
      (source := ((substituteContext label receipt.destination receipt.substitution).holeContext, source.2))
      (target := (receipt.destination, target.2)) (admitted := instantiatedDeclarations admitted)
      (Binding.bind (substituteContext label receipt.destination receipt.substitution).holeVariables agent)
      (bindingContextArrow (substituteContext label receipt.destination receipt.substitution).path)
      (Binding.bind receipt.substitution next) :=
  rawFiringSubstitution receipt.original receipt.destination receipt.substitution

theorem BindingFiringSubstitutionReceipt.original_declaration
    (receipt : BindingFiringSubstitutionReceipt admitted agent label next) :
    receipt.selected.original = receipt.original.declaration := rfl

theorem BindingFiringSubstitutionReceipt.origin
    (receipt : BindingFiringSubstitutionReceipt admitted agent label next) :
    receipt.result.declaration.origin = receipt.original.declaration.origin := rfl

theorem BindingFiringSubstitutionReceipt.complete_reactum
    (receipt : BindingFiringSubstitutionReceipt admitted agent label next) :
    receipt.result.declaration.reactum =
      Binding.bind receipt.selected.substitution receipt.original.declaration.reactum := rfl

theorem BindingFiringSubstitutionReceipt.complete_target
    (receipt : BindingFiringSubstitutionReceipt admitted agent label next) :
    Binding.bind receipt.substitution next =
      fillContext (substituteContext (rawFiringReactionPath receipt.original)
          receipt.destination receipt.substitution).path receipt.result.declaration.reactum :=
  Arrow.value.inj receipt.result.target_readout

theorem permittedFiring_reaction_path (permission : PositionPermission S)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (firing : FramePermission.Firing
      (permission := framePermission S (uniformSlotPermission S permission))
      (source := source) (target := target) (admitted := admitted)
      agent (permittedContextArrow label allowed) next) :
    FramePermission.PermittedPath (framePermission S (uniformSlotPermission S permission))
      (rawFiringReactionPath firing.raw) := by
  have given := firing.reaction.property
  rw [←bindingArrowPath_readout firing.reaction.val] at given
  cases given with
  | context pathAllowed => exact pathAllowed

def permittedFiringSubstitution (permission : PositionPermission S)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (firing : FramePermission.Firing
      (permission := framePermission S (uniformSlotPermission S permission))
      (source := source) (target := target) (admitted := admitted)
      agent (permittedContextArrow label allowed) next)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    FramePermission.Firing
      (permission := framePermission S (uniformSlotPermission S permission))
      (source := ((substituteContext label destination sigma).holeContext, source.2))
      (target := (destination, target.2)) (admitted := instantiatedDeclarations admitted)
      (Binding.bind (substituteContext label destination sigma).holeVariables agent)
      (permittedSubstitutionContext permission label allowed destination sigma)
      (Binding.bind sigma next) :=
  (rawFiringSubstitution firing.raw destination sigma).restrict
    (.context ((substituteContext_permission_iff permission (rawFiringReactionPath firing.raw)
      destination sigma).mpr (permittedFiring_reaction_path permission allowed firing)))

theorem permittedFiringSubstitution_complete_raw (permission : PositionPermission S)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (firing : FramePermission.Firing
      (permission := framePermission S (uniformSlotPermission S permission))
      (source := source) (target := target) (admitted := admitted)
      agent (permittedContextArrow label allowed) next)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    (permittedFiringSubstitution permission allowed firing destination sigma).raw =
      rawFiringSubstitution firing.raw destination sigma :=
  FramePermission.restrict_raw _ _

theorem permitted_substituted_complete_firing (permission : PositionPermission S)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (firing : FramePermission.Firing
      (permission := framePermission S (uniformSlotPermission S permission))
      (source := source) (target := target) (admitted := admitted)
      agent (permittedContextArrow label allowed) next)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    ActIPO (FramePermission.rules (framePermission S (uniformSlotPermission S permission))
        (bindingAction S) (instantiatedDeclarations admitted))
      (permittedSubstitutionContext permission label allowed destination sigma)
      (permittedTermArrow (S := S)
        (scope := ((substituteContext label destination sigma).holeContext, source.2))
        (Binding.bind (substituteContext label destination sigma).holeVariables agent))
      (permittedTermArrow (S := S) (scope := (destination, target.2)) (Binding.bind sigma next)) :=
  FramePermission.firing_iff_actIPO.mp
    ⟨permittedFiringSubstitution permission allowed firing destination sigma⟩

end Mettapedia.OSLF.Binding.ScopedEncoding
