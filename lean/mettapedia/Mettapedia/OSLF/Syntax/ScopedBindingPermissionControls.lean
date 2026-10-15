import Mettapedia.OSLF.Syntax.ScopedBindingContextPermission
import Mettapedia.CategoryTheory.GroundPathFramePermissionFiring

/-!
# Permitted binding and excluded quotation firings

A genuine binder frame is permitted while a quotation frame is excluded.
The complete minimal firing under the binder keeps its supplied origin.
Two origins have the same value readouts but different receipts. A real
ambient firing under quotation has an identity label; the label alone
therefore cannot justify restricting that supplied firing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding.PermissionControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

inductive Operation where
  | atom (value : Nat)
  | binder
  | quotation

abbrev language : Binding.Signature where
  Srt := Unit
  Op := fun _ => Operation
  arity := fun operator => match operator with
    | .atom _ => []
    | .binder => [([()], ())]
    | .quotation => [([], ())]

local instance : Quiver (Scope language) := bindingFrameQuiver language

def permission : SlotPermission language := fun _ _ operator _ => operator ≠ .quotation

abbrev frames : @FramePermission.Permission (Scope language) (bindingFrameQuiver language) :=
  framePermission language permission
abbrev action := bindingAction language

def atom {context : Binding.Ctx language} (value : Nat) : Binding.Term language context () :=
  .op (.atom value) .nil

def abstraction {context : Binding.Ctx language} (body : Binding.Term language (() :: context) ()) :
    Binding.Term language context () := .op .binder (.cons body .nil)

def quotation {context : Binding.Ctx language} (body : Binding.Term language context ()) :
    Binding.Term language context () := .op .quotation (.cons body .nil)

def binderFrame : BindingFrame language ([()], ()) ([], ()) :=
  BindingFrame.slot (S := language) [] () Operation.binder 0 (fun other absent =>
    False.elim (absent (@Subsingleton.elim (Fin 1) inferInstance other 0)))

def quoteFrame : BindingFrame language ([], ()) ([], ()) :=
  BindingFrame.slot (S := language) [] () Operation.quotation 0 (fun other absent =>
    False.elim (absent (@Subsingleton.elim (Fin 1) inferInstance other 0)))

def binderContext : BindingContext language ([()], ()) ([], ()) :=
  (.nil : BindingContext language ([()], ()) ([()], ())).cons binderFrame
def quoteContext : BindingContext language ([], ()) ([], ()) :=
  (.nil : BindingContext language ([], ()) ([], ())).cons quoteFrame

theorem binder_permitted : FramePermission.PermittedPath frames binderContext :=
  .cons (.nil _) (by intro wrong; cases wrong)

theorem quote_forbidden : ¬FramePermission.PermittedPath frames quoteContext := by
  intro allowed
  cases allowed with
  | cons previous last => exact last rfl

def binderDeclaration (origin : Nat) : FramePermission.Declaration action Nat where
  origin := origin
  scope := ([()], ())
  redex := atom 0
  reactum := atom 4

def quoteDeclaration (origin : Nat) : FramePermission.Declaration action Nat where
  origin := origin
  scope := ([], ())
  redex := atom 0
  reactum := atom 4

def admitted (declaration : FramePermission.Declaration action Nat) : Prop :=
  ∃ origin, declaration = binderDeclaration origin ∨ declaration = quoteDeclaration origin

def binderRaw (origin : Nat) : FramePermission.RawFiring (admitted := admitted)
    (abstraction (atom 0)) (contextArrow action (.nil : BindingContext language ([], ()) ([], ())))
    (abstraction (atom 4)) where
  declaration := binderDeclaration origin
  admitted := ⟨origin, Or.inl rfl⟩
  reaction := contextArrow action binderContext
  square := rfl
  minimal := by
    let candidate : PathCandidate action (first := ([], ())) (second := ([()], ()))
        (target := ([], ())) (abstraction (atom 0)) (atom (context := [()]) 0)
        (.nil : BindingContext language ([], ()) ([], ())) binderContext :=
      PathCandidate.self rfl
    exact PathCandidate.categorical_isRelativePushout candidate (fun other => other.descent_bounded)
  target_readout := rfl

def binderFiring (origin : Nat) : FramePermission.Firing (permission := frames) (admitted := admitted)
    (abstraction (atom 0)) (𝟙 (FramePermission.interface frames action ([], ())))
    (abstraction (atom 4)) :=
  (binderRaw origin).restrict (.context binder_permitted)

theorem complete_binder_firing_readout (origin : Nat) :
    (binderFiring origin).raw = binderRaw origin :=
  FramePermission.restrict_raw _ _

theorem binder_keeps_the_supplied_origin (origin : Nat) :
    (binderFiring origin).declaration.origin = origin := rfl

theorem duplicate_origins_have_different_complete_firings : binderFiring 3 ≠ binderFiring 9 := by
  intro same
  have impossible : (3 : Nat) = 9 := congrArg (fun firing => firing.declaration.origin) same
  cases impossible

theorem duplicate_origins_keep_identical_target_functions :
    (binderFiring 3).declaration.redex = (binderFiring 9).declaration.redex ∧
      (binderFiring 3).declaration.reactum = (binderFiring 9).declaration.reactum := ⟨rfl, rfl⟩

def quoteRaw (origin : Nat) : FramePermission.RawFiring (admitted := admitted)
    (quotation (atom 0)) (contextArrow action (.nil : BindingContext language ([], ()) ([], ())))
    (quotation (atom 4)) where
  declaration := quoteDeclaration origin
  admitted := ⟨origin, Or.inr rfl⟩
  reaction := contextArrow action quoteContext
  square := rfl
  minimal := by
    let candidate : PathCandidate action (first := ([], ())) (second := ([], ()))
        (target := ([], ())) (quotation (atom 0)) (atom (context := []) 0)
        (.nil : BindingContext language ([], ()) ([], ())) quoteContext :=
      PathCandidate.self rfl
    exact PathCandidate.categorical_isRelativePushout candidate (fun other => other.descent_bounded)
  target_readout := rfl

theorem quote_reaction_forbidden (origin : Nat) :
    ¬FramePermission.PermittedArrow frames action (quoteRaw origin).reaction := by
  intro allowed
  change FramePermission.PermittedArrow frames action (contextArrow action quoteContext) at allowed
  cases allowed with
  | context permitted => exact quote_forbidden permitted

theorem a_permitted_label_does_not_recover_the_supplied_firing (origin : Nat) :
    ¬ ∃ restricted : FramePermission.Firing (permission := frames) (admitted := admitted)
        (quotation (atom 0)) (𝟙 (FramePermission.interface frames action ([], ())))
        (quotation (atom 4)), restricted.raw = quoteRaw origin := by
  rintro ⟨restricted, same⟩
  have allowed := (congrArg
    (fun firing => FramePermission.PermittedArrow frames action firing.reaction) same).mp
      restricted.reaction.property
  exact quote_reaction_forbidden origin allowed

theorem permission_inclusion_is_not_full : ¬(permissionInclusion language permission).Full := by
  intro full
  let removed : permittedInterface language permission ([], ()) ⟶
      permittedInterface language permission ([], ()) :=
    (permissionInclusion language permission).preimage (bindingContextArrow quoteContext)
  have same : removed.val = bindingContextArrow quoteContext :=
    (permissionInclusion language permission).map_preimage (bindingContextArrow quoteContext)
  have allowed := same ▸ removed.property
  cases allowed with
  | context permitted => exact quote_forbidden permitted

theorem complete_context_congruence {source target : FramePermission.Object frames action}
    {first second : FramePermission.origin frames action ⟶ source}
    (related : IPOBisimilar (FramePermission.rules frames action admitted) first second)
    (context : source ⟶ target) :
    IPOBisimilar (FramePermission.rules frames action admitted) (first ≫ context) (second ≫ context) :=
  FramePermission.literal_context_congruence frames action admitted related context

end Mettapedia.OSLF.Binding.ScopedEncoding.PermissionControls
