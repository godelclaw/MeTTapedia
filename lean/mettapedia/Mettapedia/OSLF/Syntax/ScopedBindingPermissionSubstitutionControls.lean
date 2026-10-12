import Mettapedia.OSLF.Syntax.ScopedBindingIdentityReactionSubstitution
import Mettapedia.OSLF.Syntax.ScopedBindingContextControls

/-!
# Scoped substituted firings and a context-sensitive permission boundary

The complete nested-binder label substitutes an enclosing variable while
retaining both fresh variables. Its independently declared reactum keeps the
changed variable and its supplied origin. A wrong result is incompatible with
that same declaration and identity reaction. A separate permission depending
on an ambient variable is genuinely lost under a closing substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding.SubstitutionControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RedexRelativeCongruence
open Controls

local instance : Quiver (Scope toy) := bindingFrameQuiver toy

def permission : PositionPermission toy := fun _ operator _ => operator ≠ Operation.pair

abbrev frames : @FramePermission.Permission (Scope toy) (bindingFrameQuiver toy) :=
  framePermission toy (uniformSlotPermission toy permission)

theorem nested_allowed : FramePermission.PermittedPath frames nested :=
  (FramePermission.permittedPath_comp_iff frames _ _).mpr
    ⟨.cons (.nil _) (by intro wrong; cases wrong),
      .cons (.nil _) (by intro wrong; cases wrong)⟩

def declaration (origin : Nat) : FramePermission.Declaration (bindingAction toy) Nat where
  origin := origin
  scope := ([()], ())
  redex := fillContext nested body
  reactum := .var .zero

def admitted (selected : FramePermission.Declaration (bindingAction toy) Nat) : Prop :=
  ∃ origin, selected = declaration origin

def selected (origin : Nat) : BindingDeclarationInstance toy Nat where
  original := declaration origin
  destination := [(), ()]
  substitution := moveEnclosing

def firing (origin : Nat) :=
  identityReactionSubstitutionFiring (admitted := admitted) permission body (selected origin)
    (⟨origin, rfl⟩ : admitted (selected origin).original) nested nested_allowed rfl

def rawFiring (origin : Nat) :=
  identityReactionSubstitutionRaw (admitted := admitted) body (selected origin)
    (⟨origin, rfl⟩ : admitted (selected origin).original) nested rfl

theorem complete_retained_receipt (origin : Nat) : (firing origin).raw = rawFiring origin :=
  substituted_firing_retains_complete_raw_receipt (S := toy) (source := ([(), (), ()], ()))
    (admitted := admitted) permission body (selected origin)
    (⟨origin, rfl⟩ : admitted (selected origin).original) nested nested_allowed rfl

theorem complete_redex_after_substitution (origin : Nat) :
    (firing origin).declaration.redex = abstraction (abstraction expectedBody) := rfl

theorem complete_reactum_after_substitution (origin : Nat) :
    (firing origin).declaration.reactum = .var (.succ .zero) := rfl

theorem first_bound_variable_is_protected :
    (substituteContext nested [(), ()] moveEnclosing).holeVariables () .zero = .var .zero := rfl

theorem second_bound_variable_is_protected :
    (substituteContext nested [(), ()] moveEnclosing).holeVariables () (.succ .zero) =
      .var (.succ .zero) := rfl

theorem enclosing_variable_moves :
    (substituteContext nested [(), ()] moveEnclosing).holeVariables () (.succ (.succ .zero)) =
      .var (.succ (.succ (.succ .zero))) := rfl

theorem both_binder_frames_are_retained :
    (substituteContext nested [(), ()] moveEnclosing).path.length = 2 :=
  (substituteContext_frame_count nested [(), ()] moveEnclosing).trans rfl

theorem every_supplied_origin_has_an_actual_substituted_firing (origin : Nat) :
    ActIPO (FramePermission.rules frames (bindingAction toy) (instantiatedDeclarations admitted))
      (permittedSubstitutionContext permission nested nested_allowed [(), ()] moveEnclosing)
      (permittedTermArrow (S := toy) (scope := ([(), (), (), ()], ())) expectedBody)
      (permittedTermArrow (S := toy) (scope := ([(), ()], ())) (.var (.succ .zero))) :=
  substituted_complete_firing_exists (S := toy) (source := ([(), (), ()], ()))
    (admitted := admitted) permission body (selected origin)
    (⟨origin, rfl⟩ : admitted (selected origin).original) nested nested_allowed rfl

theorem actual_origin_readout (origin : Nat) : (firing origin).declaration.origin = origin := rfl

theorem changing_the_origin_changes_the_complete_firing : firing 3 ≠ firing 9 := by
  intro same
  have wrong : (3 : Nat) = 9 := congrArg (fun receipt => receipt.declaration.origin) same
  cases wrong

theorem changing_the_origin_keeps_the_complete_redex_and_reactum :
    (firing 3).declaration.redex = (firing 9).declaration.redex ∧
      (firing 3).declaration.reactum = (firing 9).declaration.reactum := ⟨rfl, rfl⟩

theorem wrong_target_cannot_retain_this_declaration_and_reaction (origin : Nat) :
    ¬ ∃ receipt : FramePermission.RawFiring
        (source := ([(), (), (), ()], ())) (target := ([(), ()], ()))
        (admitted := instantiatedDeclarations admitted) expectedBody
        (bindingContextArrow (substituteContext nested [(), ()] moveEnclosing).path)
        (Binding.Term.var .zero),
      receipt.declaration = (selected origin).realized ∧
        HEq receipt.reaction (𝟙 (bindingInterface toy ([(), ()], ()))) := by
  rintro ⟨receipt, same, unchanged⟩
  rcases receipt with ⟨declared, member, reaction, square, minimal, result⟩
  dsimp only at same unchanged
  subst declared
  have identity : reaction = 𝟙 (bindingInterface toy ([(), ()], ())) := eq_of_heq unchanged
  rw [identity] at result
  have impossible : (Binding.Term.var .zero : Binding.Term toy [(), ()] ()) =
      .var (.succ .zero) := Arrow.value.inj result
  cases impossible

def needsAmbientVariable : SlotPermission toy := fun context _ _ _ => context ≠ []

def closeToSeven : Binding.Sub toy [()] [] := fun sort position => by
  cases sort
  cases position with
  | zero => exact number 7
  | succ impossible => cases impossible

theorem original_frame_has_the_required_ambient_variable :
    framePermission toy needsAmbientVariable (binderFrame [()]) := by
  intro same
  cases same

theorem closing_substitution_loses_the_context_sensitive_permission :
    ¬FramePermission.PermittedPath (framePermission toy needsAmbientVariable)
      (substituteContext (single (binderFrame [()])) [] closeToSeven).path := by
  intro given
  have last := (FramePermission.permittedPath_cons_iff _ _ _).mp given |>.2
  exact last rfl

theorem closing_substitution_still_protects_the_bound_variable :
    Binding.bind closeToSeven (abstraction (.var .zero)) =
      (abstraction (.var .zero) : Binding.Term toy [] ()) := rfl

theorem closing_substitution_changes_the_free_variable :
    Binding.bind closeToSeven (abstraction (.var (.succ .zero))) =
      (abstraction (number 7) : Binding.Term toy [] ()) := rfl

theorem empty_origins_cannot_supply_a_declaration :
    ¬Nonempty (FramePermission.Declaration (bindingAction toy) Empty) :=
  fun ⟨declared⟩ => nomatch declared.origin

end Mettapedia.OSLF.Binding.ScopedEncoding.SubstitutionControls
