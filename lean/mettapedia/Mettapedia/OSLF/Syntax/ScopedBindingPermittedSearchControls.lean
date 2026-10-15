import Mettapedia.OSLF.Syntax.ScopedBindingPermittedFiringSearch
import Mettapedia.OSLF.Syntax.ScopedBindingFiringSearchControls

/-!
# Whole reaction permission in the executable search

A proper slot kit permits exactly one of the two binary positions beneath
the binder. Another kit permits the supplied identity label but excludes
the entire binder reaction. Complete origins and protected reacta survive
restriction; permitted-label checking alone cannot reconstruct the firing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding.PermittedSearchControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open FiringSearchControls

local instance permittedSearchControlQuiver : Quiver (Scope language) := bindingFrameQuiver language

def leftKit : SlotPermission language := fun _ _ operator position =>
  operator = .binder ∨ (operator = .pair ∧ position.val = 0)

instance leftKitDecidable : ∀ context sort operator position,
    Decidable (leftKit context sort operator position) := by
  intro context sort operator position
  change Decidable (operator = .binder ∨ (operator = .pair ∧ position.val = 0))
  infer_instance

def noBinderKit : SlotPermission language := fun _ _ operator _ => operator = .pair

instance noBinderKitDecidable : ∀ context sort operator position,
    Decidable (noBinderKit context sort operator position) := by
  intro context sort operator position
  change Decidable (operator = .pair)
  infer_instance

def restricted := bindingPermittedFiringSearch (permission := leftKit) agent identityLabel declarations

theorem the_proper_kit_keeps_both_origins : restricted.length = 2 := by decide
theorem the_proper_kit_keeps_original_list_positions :
    restricted.map (fun candidate => candidate.position.val) = [0, 1] := by decide
theorem the_proper_kit_keeps_authored_origins :
    restricted.map (fun candidate => candidate.declaration.origin) = [3, 9] := by decide

theorem identity_label_is_allowed :
    FramePermission.PermittedPath (framePermission language leftKit) identityLabel := .nil _

def selected : BindingFiringCandidate language Nat ([], ()) declarations :=
  restricted.get ⟨0, by decide⟩

theorem selected_member : selected ∈ bindingPermittedFiringSearch
    (permission := leftKit) agent identityLabel declarations := List.get_mem restricted _

def selectedFiring := bindingPermittedFiringSearchSelected agent identityLabel
  identity_label_is_allowed selected selected_member

theorem whole_permitted_occurrence_retains_the_raw_one : selectedFiring.raw =
    bindingFiringSearchSelected agent identityLabel selected
      ((mem_bindingPermittedFiringSearch agent identityLabel selected).mp selected_member).1 :=
  bindingPermittedFiringSearchSelected_complete_raw
    (S := language) (source := ([], ())) (target := ([], ())) (permission := leftKit)
    agent identityLabel identity_label_is_allowed selected selected_member

theorem complete_permitted_target : selected.result identityLabel
    ((mem_bindingFiringSearch agent identityLabel selected).mp
      ((mem_bindingPermittedFiringSearch agent identityLabel selected).mp selected_member).1).2 =
    leftResult := rfl

theorem protected_reactum_and_origin : selectedFiring.declaration.origin = 3 ∧
    selectedFiring.declaration.reactum = (Binding.Term.var .zero : Binding.Term language [()] ()) :=
  ⟨rfl, rfl⟩

theorem no_binder_kit_still_permits_the_supplied_label :
    FramePermission.PermittedPath (framePermission language noBinderKit) identityLabel := .nil _

theorem permitted_label_alone_does_not_supply_a_reaction :
    bindingPermittedFiringSearch (permission := noBinderKit) agent identityLabel declarations = [] := by decide

theorem actual_restricted_firing_is_impossible_without_its_binder :
    ¬∃ next : Binding.Term language [] (),
      Nonempty (FramePermission.Firing (permission := framePermission language noBinderKit)
        (admitted := fun declaration => declaration ∈ declarations)
        (source := ([], ())) (target := ([], ()))
        agent (permittedContextArrow identityLabel no_binder_kit_still_permits_the_supplied_label) next) := by
  intro supplied
  have nonempty := (bindingPermittedFiringSearch_nonempty_iff agent identityLabel
    no_binder_kit_still_permits_the_supplied_label).mpr supplied
  exact nonempty permitted_label_alone_does_not_supply_a_reaction

theorem selected_pair_label_is_allowed :
    FramePermission.PermittedPath (framePermission language leftKit) collisionLabel :=
  .cons (.nil _) (Or.inr ⟨rfl, rfl⟩)

theorem the_other_minimal_hole_is_excluded_by_the_kit :
    bindingPermittedFiringSearch (permission := leftKit)
      (number (context := []) 7) collisionLabel [wrongScopeDeclaration] = [] := by decide

end Mettapedia.OSLF.Binding.ScopedEncoding.PermittedSearchControls
