import Mettapedia.GSLT.Core.RelativeClosedStructuralImageLocalModels
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionCoherent
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCanonicalExtension

/-!
# Coherent classification of combined modal and constructor-image names

The target predicate, modal and structural operation values and their local
diagrams are independently supplied. A weak finite-limit closed candidate is admitted
by its base comparison, individual fresh-object isomorphisms and complete
images of the original declaration arrows. The added native inverse arrows
are forced by actual preservation and their defining equations.

Object reconstruction earns a comparison on every retained raw object
and every equation-class arrow. Only primitive components are imposed on
cells; their complete uniqueness is derived. Canonical admission and the
identity comparison are calibrated by the independent evaluator. No literal
raw-header equality or varying-theory free/forgetful action is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImageCoherent

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization
open ProgramReductionTheory RelativeClosedStructuralImageLocalModels

universe k w
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (model : LocalModel source selected constructors D)
variable (candidate : Object (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) ⥤ D)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]
variable (images : AtomicPresentation.PrimitiveImages candidate model.nativeModel.meanings)

abbrev LocalArrowAdmission := BaseExtension.Coherent.OldArrowImages model.meanings
  (RelativeClosedStructuralImagePresentation.headers source selected constructors) candidate images

variable (admitted : LocalArrowAdmission model candidate images)

include admitted in
theorem all_primitive_images : CoherentExtension.ArrowImages candidate model.nativeModel.meanings images
    (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors) :=
  BaseExtension.Coherent.all_arrow_images model.meanings
    (RelativeClosedStructuralImagePresentation.headers source selected constructors) candidate images admitted

def comparison : candidate ≅ model.nativeDiagram :=
  BaseExtension.Coherent.comparison model.meanings model.realized
    (RelativeClosedStructuralImagePresentation.headers source selected constructors) candidate images admitted

abbrev CellAdmission := BaseExtension.Coherent.CellAdmission model.meanings model.realized candidate images

theorem comparison_admitted : CellAdmission model candidate images
    (comparison model candidate images admitted).hom :=
  BaseExtension.Coherent.comparison_admitted model.meanings model.realized
    (RelativeClosedStructuralImagePresentation.headers source selected constructors) candidate images admitted

theorem admitted_cell_unique (cell : candidate ⟶ model.nativeDiagram)
    (localComponents : CellAdmission model candidate images cell) :
    cell = (comparison model candidate images admitted).hom :=
  BaseExtension.Coherent.admitted_cell_unique model.meanings model.realized
    (RelativeClosedStructuralImagePresentation.headers source selected constructors) candidate images admitted cell localComponents

@[instance_reducible] def admittedCellUnique :
    Unique {cell : candidate ⟶ model.nativeDiagram // CellAdmission model candidate images cell} :=
  BaseExtension.Coherent.admittedCellUnique model.meanings model.realized
    (RelativeClosedStructuralImagePresentation.headers source selected constructors) candidate images admitted

@[instance_reducible] def admittedIsoUnique :
    Unique {iso : candidate ≅ model.nativeDiagram // CellAdmission model candidate images iso.hom} :=
  BaseExtension.Coherent.admittedIsoUnique model.meanings model.realized
    (RelativeClosedStructuralImagePresentation.headers source selected constructors) candidate images admitted

theorem comparison_base (object : source.closed.Obj) :
    (comparison model candidate images admitted).hom.app
        (baseObject (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) object) =
      images.base.hom.app object ≫
        eqToHom (RelativeClosedSyntax.Interpretation.functor_base_object
          model.nativeModel.meanings model.nativeModel.realization object).symm :=
  (comparison_admitted model candidate images admitted).base object

theorem complete_base_component (object : source.closed.Obj) :
    (comparison model candidate images admitted).hom.app
        ((RelativeClosedStructuralImagePresentation.baseMap source selected constructors).functor.obj object) ≫
      (eqToIso model.base_readback).hom.app object = images.base.hom.app object := by
  simp only [eqToIso.hom, eqToHom_app]
  change (comparison model candidate images admitted).hom.app
      (baseObject (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) object) ≫
    eqToHom (RelativeClosedSyntax.Interpretation.functor_base_object
      model.nativeModel.meanings model.nativeModel.realization object) = _
  rw [comparison_base, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem comparison_object (origin : ULift.{k} (ULift.{k} Unit)) :
    (comparison model candidate images admitted).hom.app (namedObject origin) =
      (images.object origin).hom ≫
        eqToHom (CoherentExtension.target_named_object model.nativeModel.meanings
          model.nativeModel.realization origin).symm :=
  (comparison_admitted model candidate images admitted).object origin

def originalComparison :
    (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).functor ⋙ candidate ≅
      model.diagram :=
  Functor.isoWhiskerLeft (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).functor
    (comparison model candidate images admitted) ≪≫ eqToIso model.original_diagram_readback

theorem whole_arrow_square
    {first second : Object (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors)}
    (arrow : first ⟶ second) :
    candidate.map arrow ≫ (comparison model candidate images admitted).hom.app second =
      (comparison model candidate images admitted).hom.app first ≫ model.nativeDiagram.map arrow :=
  (comparison model candidate images admitted).hom.naturality arrow

section Canonical

instance native_finite : PreservesFiniteLimits model.nativeDiagram :=
  RelativeClosedSyntax.Interpretation.functor_preservesFiniteLimits
    model.nativeModel.meanings model.nativeModel.realization

instance native_closed : MonoidalClosedFunctor model.nativeDiagram :=
  RelativeClosedSyntax.Interpretation.functor_closed
    model.nativeModel.meanings model.nativeModel.realization

def canonicalImages : AtomicPresentation.PrimitiveImages model.nativeDiagram model.nativeModel.meanings :=
  CanonicalExtension.images model.nativeModel.meanings model.nativeModel.realization

theorem canonical_admitted : LocalArrowAdmission model model.nativeDiagram (canonicalImages model) where
  arrow origin :=
    (CanonicalExtension.arrow_images model.nativeModel.meanings model.nativeModel.realization
      (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)).arrow
        (BaseExtension.originalArrows origin)

theorem canonical_identity_admitted : CellAdmission model model.nativeDiagram (canonicalImages model)
    (𝟙 model.nativeDiagram) :=
  CanonicalExtension.identity_admitted model.nativeModel.meanings model.nativeModel.realization

theorem canonical_comparison_refl :
    comparison model model.nativeDiagram (canonicalImages model) (canonical_admitted model) =
      Iso.refl model.nativeDiagram := by
  apply Iso.ext
  exact (admitted_cell_unique model model.nativeDiagram (canonicalImages model) (canonical_admitted model)
    (𝟙 model.nativeDiagram) (canonical_identity_admitted model)).symm

end Canonical

end Mettapedia.GSLT.Core.RelativeClosedStructuralImageCoherent
