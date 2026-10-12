import Mettapedia.OSLF.Syntax.ScopedBindingFiringSubstitution
import Mettapedia.OSLF.Syntax.ScopedBindingContextControls

/-!
# A complete binder firing through a noninjective substitution

The two bounds select different binary positions after an actual binder.
Their old hole values are distinct free variables. Closing substitution
identifies those values and changes both stored sibling functions, but keeps
the selected positions and the bound variable in the complete reactum.
The reaction contains two frames. Distinct authored origins remain distinct
complete receipts, and a changed full target cannot keep that same reaction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding.FiringSubstitutionControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open Controls

local instance bindingFiringControlsQuiver : Quiver (Scope toy) := bindingFrameQuiver toy

def agent : Binding.Term toy [(), (), ()] () := .var (.succ .zero)
def redex : Binding.Term toy [(), (), ()] () := .var (.succ (.succ .zero))
def reactum : Binding.Term toy [(), (), ()] () := .var .zero

def left : BindingContext toy ([(), (), ()], ()) ([(), ()], ()) :=
  (single (binderFrame [(), ()])).comp (single (leftFrame [(), ()] (abstraction redex)))

def right : BindingContext toy ([(), (), ()], ()) ([(), ()], ()) :=
  (single (binderFrame [(), ()])).comp (single (rightFrame [(), ()] (abstraction agent)))

def result : Binding.Term toy [(), ()] () := pair (abstraction agent) (abstraction reactum)

def declaration (origin : Nat) : FramePermission.Declaration (bindingAction toy) Nat where
  origin := origin
  scope := ([(), (), ()], ())
  redex := redex
  reactum := reactum

def admitted (selected : FramePermission.Declaration (bindingAction toy) Nat) : Prop :=
  ∃ origin, selected = declaration origin

theorem square : bindingTermArrow agent ≫ bindingContextArrow left =
    bindingTermArrow redex ≫ bindingContextArrow right := rfl

theorem separate_outer_positions : ¬SharedOuterSlot left right := by
  rintro ⟨code, leftSlot, rightSlot⟩
  have impossible := (Option.some.inj leftSlot).trans (Option.some.inj rightSlot).symm
  cases impossible

def oldFiring (origin : Nat) : FramePermission.RawFiring (admitted := admitted)
    (source := ([(), (), ()], ())) (target := ([(), ()], ())) agent
    (bindingContextArrow left) result where
  declaration := declaration origin
  admitted := ⟨origin, rfl⟩
  reaction := bindingContextArrow right
  square := square
  minimal := by
    change IsIdemPushout (bindingTermArrow (S := toy) (scope := ([(), (), ()], ())) agent)
      (bindingTermArrow (S := toy) (scope := ([(), (), ()], ())) redex)
      (bindingContextArrow left) (bindingContextArrow right) square
    exact binding_ipo_of_no_shared_outer_slot (S := toy)
      (first := ([(), (), ()], ())) (second := ([(), (), ()], ())) (target := ([(), ()], ()))
      agent redex left right square separate_outer_positions
  target_readout := rfl

def closing : Binding.Sub toy [(), ()] [] := fun sort position => by
  cases sort
  cases position with
  | zero => exact number 7
  | succ next =>
    cases next with
    | zero => exact number 7
    | succ impossible => cases impossible

def receipt (origin : Nat) : BindingFiringSubstitutionReceipt admitted agent left result where
  original := oldFiring origin
  destination := []
  substitution := closing

theorem originally_different_hole_values : agent ≠ redex := by
  intro same
  cases same

theorem closing_identifies_the_hole_values :
    Binding.bind (substituteContext left [] closing).holeVariables agent =
      Binding.bind (substituteContext right [] closing).holeVariables redex := rfl

theorem original_reaction_is_nonidentity :
    (rawFiringReactionPath (oldFiring 3)).length ≠ 0 := by
  change (2 : Nat) ≠ 0
  decide

theorem complete_transformed_redex (origin : Nat) :
    (receipt origin).result.declaration.redex = (number 7 : Binding.Term toy [()] ()) := rfl

theorem complete_transformed_reactum (origin : Nat) :
    (receipt origin).result.declaration.reactum = (Binding.Term.var .zero : Binding.Term toy [()] ()) := rfl

theorem complete_transformed_target :
    (Binding.bind closing result : Binding.Term toy [] ()) =
      pair (abstraction (number 7)) (abstraction (.var .zero)) := rfl

theorem inherited_substitution_keeps_the_bound_variable :
    (receipt 3).selected.substitution () .zero = .var .zero := rfl

theorem inherited_substitution_changes_both_free_variables :
    (receipt 3).selected.substitution () (.succ .zero) = number 7 ∧
      (receipt 3).selected.substitution () (.succ (.succ .zero)) = number 7 := ⟨rfl, rfl⟩

theorem entire_old_occurrence_is_retained (origin : Nat) :
    (receipt origin).original = oldFiring origin := rfl

theorem entire_original_declaration_is_retained (origin : Nat) :
    (receipt origin).selected.original = declaration origin := rfl

theorem full_transformed_target_readout (origin : Nat) :
    pair (abstraction (number 7)) (abstraction (.var .zero)) =
      fillContext (substituteContext right [] closing).path
        (receipt origin).result.declaration.reactum :=
  (receipt origin).complete_target

theorem transformed_reaction_retains_both_frames (origin : Nat) :
    (bindingArrowPath (receipt origin).result.reaction).length = 2 := rfl

theorem different_origins_keep_different_complete_firings :
    (receipt 3).result ≠ (receipt 9).result := by
  intro same
  have impossible : (3 : Nat) = 9 := congrArg (fun firing => firing.declaration.origin) same
  cases impossible

theorem different_origins_have_the_same_complete_target :
    (receipt 3).result.declaration.reactum = (receipt 9).result.declaration.reactum := rfl

def permission : PositionPermission toy := fun _ operator _ =>
  operator = Operation.binder ∨ operator = Operation.pair

abbrev frames : @FramePermission.Permission (Scope toy) (bindingFrameQuiver toy) :=
  framePermission toy (uniformSlotPermission toy permission)

theorem left_allowed : FramePermission.PermittedPath frames left :=
  .cons (.cons (.nil _) (Or.inl rfl)) (Or.inr rfl)

theorem right_allowed : FramePermission.PermittedPath frames right :=
  .cons (.cons (.nil _) (Or.inl rfl)) (Or.inr rfl)

def permittedOldFiring (origin : Nat) : FramePermission.Firing
    (permission := frames) (admitted := admitted)
    (source := ([(), (), ()], ())) (target := ([(), ()], ())) agent
    (permittedContextArrow left left_allowed) result :=
  (oldFiring origin).restrict (.context right_allowed)

def permittedNewFiring (origin : Nat) :=
  permittedFiringSubstitution permission left_allowed (permittedOldFiring origin) [] closing

theorem every_supplied_origin_fires_with_the_whole_target (origin : Nat) :
    ActIPO (FramePermission.rules frames (bindingAction toy) (instantiatedDeclarations admitted))
      (permittedSubstitutionContext permission left left_allowed [] closing)
      (permittedTermArrow (S := toy) (scope := ([()], ())) (number 7))
      (permittedTermArrow (S := toy) (scope := ([], ()))
        (pair (abstraction (number 7)) (abstraction (.var .zero)))) :=
  permitted_substituted_complete_firing permission left_allowed (permittedOldFiring origin) [] closing

theorem permitted_comparison_retains_the_complete_raw_firing (origin : Nat) :
    (permittedNewFiring origin).raw = (receipt origin).result := by
  have retainedOld : (permittedOldFiring origin).raw = oldFiring origin :=
    FramePermission.restrict_raw (permission := frames) (action := bindingAction toy)
      (source := ([(), (), ()], ())) (target := ([(), ()], ())) (admitted := admitted)
      (label := permittedContextArrow left left_allowed)
      (oldFiring origin) (.context right_allowed)
  exact (permittedFiringSubstitution_complete_raw permission left_allowed
    (permittedOldFiring origin) [] closing).trans
    (congrArg (fun firing : FramePermission.RawFiring (source := ([(), (), ()], ()))
      (target := ([(), ()], ())) (admitted := admitted) agent (bindingContextArrow left) result =>
        rawFiringSubstitution firing [] closing) retainedOld)

theorem wrong_full_target_cannot_retain_this_rule_and_reaction (origin : Nat) :
    ¬∃ wrong : FramePermission.RawFiring (admitted := instantiatedDeclarations admitted)
        (source := ([()], ())) (target := ([], ())) (number 7)
        (bindingContextArrow (substituteContext left [] closing).path)
        (pair (abstraction (number 7)) (abstraction (number 7))),
      wrong.declaration = (receipt origin).result.declaration ∧
        HEq wrong.reaction (receipt origin).result.reaction := by
  rintro ⟨wrong, sameDeclaration, sameReaction⟩
  rcases wrong with ⟨selected, member, reaction, matching, minimal, targetRead⟩
  dsimp only at sameDeclaration sameReaction
  subst selected
  have unchanged : reaction = (receipt origin).result.reaction := eq_of_heq sameReaction
  rw [unchanged] at targetRead
  have impossible : (pair (abstraction (number 7)) (abstraction (number 7)) : Binding.Term toy [] ()) =
      pair (abstraction (number 7)) (abstraction (.var .zero)) := Arrow.value.inj targetRead
  cases impossible

theorem no_origin_cannot_supply_a_complete_substitution_receipt :
    ¬Nonempty (FramePermission.Declaration (bindingAction toy) Empty) :=
  fun ⟨selected⟩ => nomatch selected.origin

end Mettapedia.OSLF.Binding.ScopedEncoding.FiringSubstitutionControls
