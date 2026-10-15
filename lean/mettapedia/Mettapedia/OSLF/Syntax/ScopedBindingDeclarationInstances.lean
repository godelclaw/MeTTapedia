import Mettapedia.OSLF.Syntax.ScopedBindingIdentityReactionSubstitution

/-!
# Identity and composition of actual scoped declaration instances

The complete redex and reactum obey the independent term substitution laws.
Iterating an actual rule instance therefore flattens to a single composed
instance of the original declaration, while keeping its origin. Conversely,
the identity instance realizes the same declaration. The resulting rule
family is closed under actual instantiation; an independently authored rule
family need not have this property.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open Mettapedia.CategoryTheory.GroundPath

universe r
variable {S : Binding.Signature} {Origins : Type r}
local instance bindingDeclarationCoherenceQuiver : Quiver (Scope S) := bindingFrameQuiver S

def declarationIdentityInstance (declaration : FramePermission.Declaration (bindingAction S) Origins) :
    BindingDeclarationInstance S Origins where
  original := declaration
  destination := declaration.scope.1
  substitution := fun _ position => .var position

theorem declarationIdentityInstance_realized
    (declaration : FramePermission.Declaration (bindingAction S) Origins) :
    (declarationIdentityInstance declaration).realized = declaration := by
  rcases declaration with ⟨origin, ⟨context, sort⟩, redex, reactum⟩
  exact congrArg₂
    (fun (left right : Binding.Term S context sort) =>
      (⟨origin, (context, sort), left, right⟩ : FramePermission.Declaration (bindingAction S) Origins))
    (Binding.bind_id redex) (Binding.bind_id reactum)

def BindingDeclarationInstance.iterate (selected : BindingDeclarationInstance S Origins)
    (destination : Binding.Ctx S) (second : Binding.Sub S selected.destination destination) :
    BindingDeclarationInstance S Origins where
  original := selected.realized
  destination := destination
  substitution := second

def BindingDeclarationInstance.compose (selected : BindingDeclarationInstance S Origins)
    (destination : Binding.Ctx S) (second : Binding.Sub S selected.destination destination) :
    BindingDeclarationInstance S Origins where
  original := selected.original
  destination := destination
  substitution := fun sort position => Binding.bind second (selected.substitution sort position)

theorem BindingDeclarationInstance.iterate_realized (selected : BindingDeclarationInstance S Origins)
    (destination : Binding.Ctx S) (second : Binding.Sub S selected.destination destination) :
    (selected.iterate destination second).realized = (selected.compose destination second).realized := by
  exact congrArg₂
    (fun (left right : Binding.Term S destination selected.original.scope.2) =>
      (⟨selected.original.origin, (destination, selected.original.scope.2), left, right⟩ :
        FramePermission.Declaration (bindingAction S) Origins))
    (Binding.bind_comp selected.substitution second selected.original.redex)
    (Binding.bind_comp selected.substitution second selected.original.reactum)

theorem BindingDeclarationInstance.compose_origin (selected : BindingDeclarationInstance S Origins)
    (destination : Binding.Ctx S) (second : Binding.Sub S selected.destination destination) :
    (selected.compose destination second).realized.origin = selected.original.origin := rfl

theorem BindingDeclarationInstance.compose_complete_redex (selected : BindingDeclarationInstance S Origins)
    (destination : Binding.Ctx S) (second : Binding.Sub S selected.destination destination) :
    (selected.compose destination second).realized.redex = Binding.bind second selected.realized.redex :=
  (Binding.bind_comp selected.substitution second selected.original.redex).symm

theorem BindingDeclarationInstance.compose_complete_reactum (selected : BindingDeclarationInstance S Origins)
    (destination : Binding.Ctx S) (second : Binding.Sub S selected.destination destination) :
    (selected.compose destination second).realized.reactum = Binding.bind second selected.realized.reactum :=
  (Binding.bind_comp selected.substitution second selected.original.reactum).symm

theorem admitted_declaration_is_an_instance
    (admitted : FramePermission.Declaration (bindingAction S) Origins → Prop)
    (declaration : FramePermission.Declaration (bindingAction S) Origins)
    (member : admitted declaration) : instantiatedDeclarations admitted declaration :=
  ⟨declarationIdentityInstance declaration, member, declarationIdentityInstance_realized declaration⟩

theorem instantiatedDeclarations_iterated_iff
    (admitted : FramePermission.Declaration (bindingAction S) Origins → Prop)
    (declaration : FramePermission.Declaration (bindingAction S) Origins) :
    instantiatedDeclarations (instantiatedDeclarations admitted) declaration ↔
      instantiatedDeclarations admitted declaration := by
  constructor
  · rintro ⟨outer, ⟨inner, member, recovered⟩, outerRecovered⟩
    rcases outer with ⟨intermediate, destination, second⟩
    dsimp only at recovered outerRecovered
    subst intermediate
    exact ⟨inner.compose destination second, member,
      (inner.iterate_realized destination second).symm.trans outerRecovered⟩
  · intro member
    exact admitted_declaration_is_an_instance (instantiatedDeclarations admitted) declaration member

theorem instantiatedDeclarations_idempotent
    (admitted : FramePermission.Declaration (bindingAction S) Origins → Prop) :
    instantiatedDeclarations (instantiatedDeclarations admitted) = instantiatedDeclarations admitted := by
  funext declaration
  exact propext (instantiatedDeclarations_iterated_iff admitted declaration)

end Mettapedia.OSLF.Binding.ScopedEncoding
