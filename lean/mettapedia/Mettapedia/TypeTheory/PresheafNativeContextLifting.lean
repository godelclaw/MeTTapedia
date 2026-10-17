import Mettapedia.TypeTheory.NativeLocalTypeOperations
import Mettapedia.TypeTheory.ContextualTypePresentationCast

/-! # Actual fibres of native presheaf context lifting -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.PresheafNativeContextLifting

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open NativeLocalTypeFormers ContextualLocalUniverses
open DisplayedPresheafComprehension

universe u
variable {W : Type u} [Category.{u} W]
variable {P Q : Wᵒᵖ ⥤ Type u}

/-- The actual comprehension map, with the supplied equality of native
presentations transported by the canonical context isomorphism. -/
def lift (mapping : P ⟶ Q) (type : NativeType Q) (source : NativeType P)
    (same : type.reindex mapping = source) :
    totalSpace source.decoded ⟶ totalSpace type.decoded :=
  ContextualTypePresentationCast.extensionCast (K := NativeLocalTypeOperations.localModel W) same.symm ≫
    TypeOver.extensionSubstitution (C := NativeLocalTypeOperations.localModel W) mapping type

theorem lift_projection (mapping : P ⟶ Q) (type : NativeType Q) (source : NativeType P)
    (same : type.reindex mapping = source) :
    lift mapping type source same ≫ totalProjection type.decoded =
      totalProjection source.decoded ≫ mapping := by
  cases same
  rw [lift, ContextualTypePresentationCast.extensionCast_refl]
  change TypeOver.extensionSubstitution (C := NativeLocalTypeOperations.localModel W) mapping type ≫
    totalProjection type.decoded = totalProjection (type.reindex mapping).decoded ≫ mapping
  rw [NativeLocalTypeOperations.local_extensionSubstitution]
  rfl

/-- Every point in a target fibre is retained by native context lifting.
No finiteness, chosen point, or nonemptiness premise is imposed on the type. -/
theorem lift_fibre (mapping : P ⟶ Q) (type : NativeType Q) (source : NativeType P)
    (same : type.reindex mapping = source)
    (world : Wᵒᵖ) (base : P.obj world) (target : (totalSpace type.decoded).obj world)
    (over : target.1 = mapping.app world base) :
    ∃ value : (totalSpace source.decoded).obj world,
      value.1 = base ∧ (lift mapping type source same).app world value = target := by
  cases same
  rw [lift, ContextualTypePresentationCast.extensionCast_refl]
  change ∃ value : (totalSpace (type.reindex mapping).decoded).obj world,
    value.1 = base ∧
      (TypeOver.extensionSubstitution (C := NativeLocalTypeOperations.localModel W) mapping type).app world value = target
  rw [NativeLocalTypeOperations.local_extensionSubstitution]
  rcases target with ⟨point, argument⟩
  change point = mapping.app world base at over
  subst point
  exact ⟨⟨base, argument⟩, rfl, rfl⟩

end Mettapedia.TypeTheory.PresheafNativeContextLifting
