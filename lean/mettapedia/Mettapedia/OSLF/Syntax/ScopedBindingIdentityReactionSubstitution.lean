import Mettapedia.OSLF.Syntax.ScopedBindingPermissionSubstitution
import Mettapedia.CategoryTheory.GroundPathFramePermissionFiring

/-!
# Complete instantiated firings with actual identity reaction contexts

An instance retains the original declaration and origin, an independently
supplied variable substitution, and its destination context. Its redex and
reactum are computed by capture-avoiding term substitution. The old matching
equation earns the new complete square through the actual inherited hole
variables. Identity reaction contexts earn minimality from every competing
candidate, so no substituted IPO or firing-preservation law is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RedexRelativeCongruence

universe r

variable (S : Binding.Signature)
local instance : Quiver (Scope S) := bindingFrameQuiver S

structure BindingDeclarationInstance (Origins : Type r) where
  original : FramePermission.Declaration (bindingAction S) Origins
  destination : Binding.Ctx S
  substitution : Binding.Sub S original.scope.1 destination

variable {S} {Origins : Type r}

def BindingDeclarationInstance.realized (selected : BindingDeclarationInstance S Origins) :
    FramePermission.Declaration (bindingAction S) Origins where
  origin := selected.original.origin
  scope := (selected.destination, selected.original.scope.2)
  redex := Binding.bind selected.substitution selected.original.redex
  reactum := Binding.bind selected.substitution selected.original.reactum

def instantiatedDeclarations
    (admitted : FramePermission.Declaration (bindingAction S) Origins → Prop)
    (declaration : FramePermission.Declaration (bindingAction S) Origins) : Prop :=
  ∃ selected : BindingDeclarationInstance S Origins,
    admitted selected.original ∧ selected.realized = declaration

theorem substituted_match {source : Scope S} (agent : Binding.Term S source.1 source.2)
    (selected : BindingDeclarationInstance S Origins)
    (label : BindingContext S source selected.original.scope)
    (matching : fillContext label agent = selected.original.redex) :
    fillContext (substituteContext label selected.destination selected.substitution).path
        (Binding.bind (substituteContext label selected.destination selected.substitution).holeVariables agent) =
      selected.realized.redex :=
  (substituteContext_fill label selected.destination selected.substitution agent).symm.trans
    (congrArg (Binding.bind selected.substitution) matching)

theorem identityReactionSubstitution_square {source : Scope S}
    (agent : Binding.Term S source.1 source.2)
    (selected : BindingDeclarationInstance S Origins)
    (label : BindingContext S source selected.original.scope)
    (matching : fillContext label agent = selected.original.redex) :
    bindingTermArrow (S := S)
        (scope := ((substituteContext label selected.destination selected.substitution).holeContext, source.2))
        (Binding.bind (substituteContext label selected.destination selected.substitution).holeVariables agent) ≫
        bindingContextArrow
          (source := ((substituteContext label selected.destination selected.substitution).holeContext, source.2))
          (target := selected.realized.scope)
          (substituteContext label selected.destination selected.substitution).path =
      bindingTermArrow (S := S) (scope := selected.realized.scope) selected.realized.redex ≫
        𝟙 (bindingInterface S selected.realized.scope) :=
  congrArg (bindingTermArrow (S := S) (scope := selected.realized.scope))
    (substituted_match agent selected label matching)

def identityReactionSubstitutionRaw
    {admitted : FramePermission.Declaration (bindingAction S) Origins → Prop}
    {source : Scope S} (agent : Binding.Term S source.1 source.2)
    (selected : BindingDeclarationInstance S Origins) (member : admitted selected.original)
    (label : BindingContext S source selected.original.scope)
    (matching : fillContext label agent = selected.original.redex) :
    FramePermission.RawFiring
      (source := ((substituteContext label selected.destination selected.substitution).holeContext, source.2))
      (target := selected.realized.scope) (admitted := instantiatedDeclarations admitted)
      (Binding.bind (substituteContext label selected.destination selected.substitution).holeVariables agent)
      (bindingContextArrow (substituteContext label selected.destination selected.substitution).path)
      selected.realized.reactum where
  declaration := selected.realized
  admitted := ⟨selected, member, rfl⟩
  reaction := 𝟙 (bindingInterface S selected.realized.scope)
  square := identityReactionSubstitution_square agent selected label matching
  minimal := ground_identityReactionIPO (bindingAction S) _ _ _
    (identityReactionSubstitution_square agent selected label matching)
  target_readout := rfl

def identityReactionSubstitutionFiring (permission : PositionPermission S)
    {admitted : FramePermission.Declaration (bindingAction S) Origins → Prop}
    {source : Scope S} (agent : Binding.Term S source.1 source.2)
    (selected : BindingDeclarationInstance S Origins) (member : admitted selected.original)
    (label : BindingContext S source selected.original.scope)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (matching : fillContext label agent = selected.original.redex) :
    FramePermission.Firing
      (permission := framePermission S (uniformSlotPermission S permission))
      (source := ((substituteContext label selected.destination selected.substitution).holeContext, source.2))
      (target := selected.realized.scope) (admitted := instantiatedDeclarations admitted)
      (Binding.bind (substituteContext label selected.destination selected.substitution).holeVariables agent)
      (permittedSubstitutionContext permission label allowed selected.destination selected.substitution)
      selected.realized.reactum :=
  (identityReactionSubstitutionRaw agent selected member label matching).restrict (.context (.nil _))

theorem substituted_firing_retains_complete_raw_receipt (permission : PositionPermission S)
    {admitted : FramePermission.Declaration (bindingAction S) Origins → Prop}
    {source : Scope S} (agent : Binding.Term S source.1 source.2)
    (selected : BindingDeclarationInstance S Origins) (member : admitted selected.original)
    (label : BindingContext S source selected.original.scope)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (matching : fillContext label agent = selected.original.redex) :
    (identityReactionSubstitutionFiring permission agent selected member label allowed matching).raw =
      identityReactionSubstitutionRaw agent selected member label matching :=
  FramePermission.restrict_raw _ _

theorem substituted_firing_retains_origin (permission : PositionPermission S)
    {admitted : FramePermission.Declaration (bindingAction S) Origins → Prop}
    {source : Scope S} (agent : Binding.Term S source.1 source.2)
    (selected : BindingDeclarationInstance S Origins) (member : admitted selected.original)
    (label : BindingContext S source selected.original.scope)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (matching : fillContext label agent = selected.original.redex) :
    (identityReactionSubstitutionFiring permission agent selected member label allowed matching).declaration.origin =
      selected.original.origin := rfl

theorem substituted_complete_firing_exists (permission : PositionPermission S)
    {admitted : FramePermission.Declaration (bindingAction S) Origins → Prop}
    {source : Scope S} (agent : Binding.Term S source.1 source.2)
    (selected : BindingDeclarationInstance S Origins) (member : admitted selected.original)
    (label : BindingContext S source selected.original.scope)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (matching : fillContext label agent = selected.original.redex) :
    ActIPO (FramePermission.rules (framePermission S (uniformSlotPermission S permission))
      (bindingAction S) (instantiatedDeclarations admitted))
      (permittedSubstitutionContext permission label allowed selected.destination selected.substitution)
      (permittedTermArrow (S := S)
        (scope := ((substituteContext label selected.destination selected.substitution).holeContext, source.2))
        (Binding.bind (substituteContext label selected.destination selected.substitution).holeVariables agent))
      (permittedTermArrow (S := S) (scope := selected.realized.scope) selected.realized.reactum) :=
  FramePermission.firing_iff_actIPO.mp
    ⟨identityReactionSubstitutionFiring permission agent selected member label allowed matching⟩

end Mettapedia.OSLF.Binding.ScopedEncoding
