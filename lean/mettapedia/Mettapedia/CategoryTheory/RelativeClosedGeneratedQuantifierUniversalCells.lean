import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierUniversalReadout

/-!
# Intrinsic cell admission and complete coherent uniqueness

Cell admission records only the independently supplied embedded-base and
fresh-object comparisons. The constructed closure comparison is admitted;
constructor propagation determines every admitted complete natural cell or
isomorphism. A locally compatible cell between two candidates therefore
commutes with the whole comparisons, including every later quantifier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.UniversalCells

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory FunctorNormalization Iteration Closure
open UniversalReadout

universe k w
variable {C : Type k} [Category.{k} C] {stage : Stage C}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {quantifiers : InternalPredicateQuantifiedObject.Operations D}
variable (initial : Model quantifiers stage)
variable (mapping : Object (Closure.signature stage) ⥤ D)
variable [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]
variable (images : AtomicPresentation.PrimitiveImages mapping (modelAssignment initial))
variable (admitted : InitialArrowImages initial mapping images)

abbrev CellAdmission := CoherentExtension.CellAdmission mapping (modelAssignment initial)
  images (modelRealization initial)

theorem comparison_admitted : CellAdmission initial mapping images
    (comparison initial mapping images admitted).hom :=
  CoherentExtension.comparison_admitted mapping (modelAssignment initial) images (Closure.headers stage)
    (all_added_arrow_images initial mapping images admitted) (modelRealization initial)

theorem admitted_cell_unique (candidate : mapping ⟶ Closure.modelDiagram initial)
    (localReadings : CellAdmission initial mapping images candidate) :
    candidate = (comparison initial mapping images admitted).hom :=
  CoherentExtension.admitted_cell_unique mapping (modelAssignment initial) images (Closure.headers stage)
    (all_added_arrow_images initial mapping images admitted) (modelRealization initial) candidate localReadings

abbrev AdmittedCell := {candidate : mapping ⟶ Closure.modelDiagram initial //
  CellAdmission initial mapping images candidate}

@[instance_reducible] def admittedCellUnique : Unique (AdmittedCell initial mapping images) where
  default := ⟨(comparison initial mapping images admitted).hom,
    comparison_admitted initial mapping images admitted⟩
  uniq candidate := Subtype.ext (admitted_cell_unique initial mapping images admitted
    candidate.val candidate.property)

abbrev AdmittedIso := {candidate : mapping ≅ Closure.modelDiagram initial //
  CellAdmission initial mapping images candidate.hom}

@[instance_reducible] def admittedIsoUnique : Unique (AdmittedIso initial mapping images) where
  default := ⟨comparison initial mapping images admitted,
    comparison_admitted initial mapping images admitted⟩
  uniq candidate := Subtype.ext (Iso.ext (admitted_cell_unique initial mapping images admitted
    candidate.val.hom candidate.property))

variable (second : Object (Closure.signature stage) ⥤ D)
variable [PreservesFiniteLimits second] [MonoidalClosedFunctor second]
variable (secondImages : AtomicPresentation.PrimitiveImages second (modelAssignment initial))
variable (secondAdmission : InitialArrowImages initial second secondImages)

structure CellImages (cell : mapping ⟶ second) : Prop where
  base (object : C) : cell.app (baseObject (Closure.signature stage) object) ≫ secondImages.base.hom.app object =
    images.base.hom.app object
  object (origin : stage.symbols.ObjectName) : cell.app (namedObject origin) ≫ (secondImages.object origin).hom =
    (images.object origin).hom

include admitted secondAdmission in
theorem complete_comparison_square (cell : mapping ⟶ second)
    (localReadings : CellImages initial mapping images second secondImages cell) :
    cell ≫ (comparison initial second secondImages secondAdmission).hom =
      (comparison initial mapping images admitted).hom := by
  apply admitted_cell_unique initial mapping images admitted
  constructor
  · intro object
    change cell.app (baseObject (Closure.signature stage) object) ≫
        (comparison initial second secondImages secondAdmission).hom.app (baseObject (Closure.signature stage) object) = _
    rw [base_component, ← Category.assoc, localReadings.base]
  · intro origin
    change cell.app (namedObject origin) ≫
        (comparison initial second secondImages secondAdmission).hom.app (namedObject origin) = _
    rw [object_component, ← Category.assoc, localReadings.object]

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.UniversalCells
