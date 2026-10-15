import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Evaluation of a pointwise right Kan extension at a generic argument

When the actual future-argument comma category has an initial object,
its limit is the body value at that object. The comparison below retains
the chosen right-Kan extension and its evaluation map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RightKanInitialValue

open CategoryTheory Limits

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {E : Type w} [Category.{w'} E]

noncomputable section

def comparison (projection : C ⥤ D) (body : C ⥤ E)
    [∀ (F : C ⥤ E), projection.HasRightKanExtension F]
    [Functor.HasPointwiseRightKanExtension projection body]
    (point : D) (generic : StructuredArrow point projection)
    (initial : IsInitial generic) :
    (projection.ran.obj body).obj point ≅ body.obj generic.right := by
  let diagram : StructuredArrow point projection ⥤ E :=
    StructuredArrow.proj point projection ⋙ body
  exact projection.ranObjObjIsoLimit body point ≪≫
    (limit.isLimit diagram).conePointUniqueUpToIso (limitOfDiagramInitial initial diagram)

theorem comparison_evaluation (projection : C ⥤ D) (body : C ⥤ E)
    [∀ (F : C ⥤ E), projection.HasRightKanExtension F]
    [Functor.HasPointwiseRightKanExtension projection body]
    (point : D) (generic : StructuredArrow point projection)
    (initial : IsInitial generic) :
    (comparison projection body point generic initial).hom =
      (projection.ran.obj body).map generic.hom ≫
        (projection.ranCounit.app body).app generic.right := by
  change (projection.ranObjObjIsoLimit body point).hom ≫
    limit.π (StructuredArrow.proj point projection ⋙ body) generic = _
  exact projection.ranObjObjIsoLimit_hom_π body point generic

end

end Mettapedia.TypeTheory.RightKanInitialValue
