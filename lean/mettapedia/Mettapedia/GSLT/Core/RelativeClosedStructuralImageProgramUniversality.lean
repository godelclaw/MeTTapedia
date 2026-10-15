import Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramReadout

/-!
# Coherent program classification of the combined named layers

A candidate program-theory map supplies only its actual weak closed
functor, local primitive images and the independently given program reading.
The combined presentation earns the full natural comparison, which agrees
with every original base component. That comparison and the local program
square determine an actual program-map isomorphism. Its entire event square
follows from the two endpoint equations and their joint cancellation.

The map isomorphism is unique over the supplied primitive cell components.
Raw context objects remain retained; literal equality of arbitrary weak
interpretations and the global varying-presentation adjunction are separate
obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramUniversality

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory
open RelativeClosedSyntax GeneratedCategory FunctorNormalization
open RelativeClosedStructuralImageProgramReadout

universe k
variable {source target : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable (model : RelativeClosedStructuralImageLocalModels.LocalModel
  source selected constructors target.closed.Obj)
variable (original : Map source target)
variable (originalBase : model.previous.base ≅ original.closed.functor)
variable (candidate : Map (generated (source := source) (selected := selected) (constructors := constructors)) target)

variable (images : AtomicPresentation.PrimitiveImages candidate.closed.functor model.nativeModel.meanings)
variable (admitted : @RelativeClosedStructuralImageCoherent.LocalArrowAdmission
  source Index Origins selected constructors target.closed.Obj inferInstance inferInstance inferInstance inferInstance
    model candidate.closed.functor candidate.closed.preservesFiniteLimits candidate.closed.preservesExponentials images)
variable (programSquare : images.base.hom.app source.program ≫
    (originalBase.hom.app source.program ≫ original.program.hom) = candidate.program.hom)

def closedComparison : candidate.closed.functor ≅ model.nativeDiagram :=
  @RelativeClosedStructuralImageCoherent.comparison
    source Index Origins selected constructors target.closed.Obj inferInstance inferInstance inferInstance inferInstance
      model candidate.closed.functor candidate.closed.preservesFiniteLimits candidate.closed.preservesExponentials images admitted

def comparison : ProgramReductionTheoryIsoClasses.MapIso candidate (extension model original originalBase) where
  comparison := closedComparison model candidate images admitted
  program := by
    rw [complete_program_comparison model original originalBase]
    simp only [baseComparison, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    have carried : (closedComparison model candidate images admitted).hom.app
        (generated (source := source) (selected := selected) (constructors := constructors)).program ≫
      (eqToIso model.base_readback).hom.app source.program = images.base.hom.app source.program :=
      @RelativeClosedStructuralImageCoherent.complete_base_component
      source Index Origins selected constructors target.closed.Obj inferInstance inferInstance inferInstance inferInstance
        model candidate.closed.functor candidate.closed.preservesFiniteLimits candidate.closed.preservesExponentials
          images admitted source.program
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun reading : candidate.closed.functor.obj
          (generated (source := source) (selected := selected) (constructors := constructors)).program ⟶
            model.previous.base.obj source.program =>
        reading ≫ (originalBase.hom.app source.program ≫ original.program.hom)) carried)).trans programSquare

theorem complete_event_square :
    (comparison model original originalBase candidate images admitted programSquare).comparison.hom.app
        (generated (source := source) (selected := selected) (constructors := constructors)).Event ≫
      (extension model original originalBase).reduction = candidate.reduction :=
  (comparison model original originalBase candidate images admitted programSquare).reduction_square

private theorem mapIso_ext {first second : Map
    (generated (source := source) (selected := selected) (constructors := constructors)) target}
    (before after : ProgramReductionTheoryIsoClasses.MapIso first second)
    (same : before.comparison = after.comparison) : before = after := by
  cases before
  cases after
  cases same
  rfl

theorem admitted_comparison_unique
    (other : ProgramReductionTheoryIsoClasses.MapIso candidate (extension model original originalBase))
    (localComponents : RelativeClosedStructuralImageCoherent.CellAdmission
      model candidate.closed.functor images other.comparison.hom) :
    other = comparison model original originalBase candidate images admitted programSquare := by
  apply mapIso_ext
  apply Iso.ext
  exact @RelativeClosedStructuralImageCoherent.admitted_cell_unique
    source Index Origins selected constructors target.closed.Obj inferInstance inferInstance inferInstance inferInstance
      model candidate.closed.functor candidate.closed.preservesFiniteLimits candidate.closed.preservesExponentials
        images admitted other.comparison.hom localComponents

@[instance_reducible] def admittedComparisonUnique :
    Unique {change : ProgramReductionTheoryIsoClasses.MapIso candidate (extension model original originalBase) //
      RelativeClosedStructuralImageCoherent.CellAdmission model candidate.closed.functor images change.comparison.hom} where
  default := ⟨comparison model original originalBase candidate images admitted programSquare,
    @RelativeClosedStructuralImageCoherent.comparison_admitted
      source Index Origins selected constructors target.closed.Obj inferInstance inferInstance inferInstance inferInstance
        model candidate.closed.functor candidate.closed.preservesFiniteLimits candidate.closed.preservesExponentials
          images admitted⟩
  uniq change := Subtype.ext
    (admitted_comparison_unique model original originalBase candidate images admitted programSquare
      change.val change.property)

end Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramUniversality
