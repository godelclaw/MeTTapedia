import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedControls
import Mettapedia.CategoryTheory.RelativeClosedImplicativeQuantifiedMonad

/-!
# Complete named operators and firing evidence through the construction fold

The combined named presentation is an actual implication-qualified program
theory. Its quantified construction has the varying-theory adjunction and
monad. The actual multiplication recovers every old complete arrow through
its independently earned base comparison. In particular, both kinds of
named function and the complete authored firing survive iteration.

This is the admitted conjunctive/implicative quantified profile. A free
extension from bare program theories and stronger logical capabilities
require their own admission and universal-property comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedConstruction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedNamedQuantifiedPresentation
open RelativeClosedImplicativeQuantified

universe k
variable (source : Theory.{k,k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)

def initial : ImplicativeProgramTheory.{k} where
  conjunctive := namedTheory source selected constructors
  implication := implication source selected constructors

abbrev result := freeObject (initial source selected constructors)
abbrev foldMap := Construction.multiplicationMap (initial source selected constructors)
abbrev foldComparison := Construction.baseComparison (initial source selected constructors)
abbrev iteratedUnit := RelativeClosedImplicativeQuantified.unitMap
  (result source selected constructors).implicative

def arrowReading
    {before after : (result source selected constructors).quantified.programTheory.closed.Obj}
    (arrow : before ⟶ after) :=
  (foldComparison source selected constructors).comparison.inv.app before ≫
    (foldMap source selected constructors).functor.map
      ((iteratedUnit source selected constructors).functor.map arrow) ≫
        (foldComparison source selected constructors).comparison.hom.app after

theorem complete_arrow_fold
    {before after : (result source selected constructors).quantified.programTheory.closed.Obj}
    (arrow : before ⟶ after) : arrowReading source selected constructors arrow = arrow := by
  have natural := (foldComparison source selected constructors).comparison.hom.naturality arrow
  change (foldMap source selected constructors).functor.map
      ((iteratedUnit source selected constructors).functor.map arrow) ≫
      (foldComparison source selected constructors).comparison.hom.app after =
    (foldComparison source selected constructors).comparison.hom.app before ≫ arrow at natural
  exact (congrArg (fun carried =>
    (foldComparison source selected constructors).comparison.inv.app before ≫ carried) natural).trans
      ((foldComparison source selected constructors).comparison.inv_hom_id_app_assoc _ _)

theorem complete_constructor_fold (origin : Origins) :
    arrowReading source selected constructors (constructorArrow source selected constructors origin) =
      constructorArrow source selected constructors origin :=
  complete_arrow_fold source selected constructors _

theorem complete_modal_fold (origin : Option Index) :
    arrowReading source selected constructors (modalArrow source selected constructors origin) =
      modalArrow source selected constructors origin :=
  complete_arrow_fold source selected constructors _

theorem complete_authored_firing_fold (origin : Index) :
    (foldComparison source selected constructors).comparison.inv.app
        ((programInclusion source selected constructors).closed.functor.obj (selected origin).rule.parameters) ≫
      (foldMap source selected constructors).functor.map
        ((iteratedUnit source selected constructors).functor.map
          (Rule.transport (programInclusion source selected constructors) (selected origin).rule).action ≫
            (iteratedUnit source selected constructors).reduction) ≫
              (foldMap source selected constructors).reduction =
      (Rule.transport (programInclusion source selected constructors) (selected origin).rule).action :=
  Construction.complete_event_readout (initial source selected constructors)
    (Rule.transport (programInclusion source selected constructors) (selected origin).rule).action

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedConstruction
