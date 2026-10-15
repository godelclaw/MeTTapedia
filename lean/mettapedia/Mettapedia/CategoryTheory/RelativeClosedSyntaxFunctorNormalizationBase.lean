import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationNative

/-!
# Complete base arrows under native normalization

Native normalization changes constructor choices while retaining base
objects. Naturality of its actual comparison gives the entire base-arrow
square, with the object readings made explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory

universe k w
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping]

theorem base_object (value : C) :
    (normalizedFunctor mapping).obj (baseObject signature value) =
      mapping.obj (baseObject signature value) :=
  congrArg ObjectImage.value (objectImage_base mapping value)

theorem base_arrow {before after : C} (route : before ⟶ after) :
    (normalizedFunctor mapping).map (baseArrow route) ≫ eqToHom (base_object mapping after) =
      eqToHom (base_object mapping before) ≫ mapping.map (baseArrow route) := by
  let actual := comparison mapping
  have beforeRead : actual.hom.app (baseObject signature before) ≫
      eqToHom (base_object mapping before) = 𝟙 _ :=
    comparison_transport mapping (objectImage_base mapping before)
  have afterRead : actual.hom.app (baseObject signature after) ≫
      eqToHom (base_object mapping after) = 𝟙 _ :=
    comparison_transport mapping (objectImage_base mapping after)
  apply (cancel_epi (actual.hom.app (baseObject signature before))).mp
  calc
    _ = (mapping.map (baseArrow route) ≫ actual.hom.app (baseObject signature after)) ≫
        eqToHom (base_object mapping after) := by
      rw [← Category.assoc, ← actual.hom.naturality]
    _ = mapping.map (baseArrow route) := by
      rw [Category.assoc, afterRead, Category.comp_id]
    _ = _ := by
      rw [← Category.assoc, beforeRead, Category.id_comp]

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
