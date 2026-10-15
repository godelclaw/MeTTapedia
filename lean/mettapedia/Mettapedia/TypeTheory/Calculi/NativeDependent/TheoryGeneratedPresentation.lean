import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryRepresentableStructuralComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryRepresentableFamilies
import Mettapedia.CategoryTheory.AsSmallYoneda
import Mettapedia.GSLT.Core.LambdaTheory

/-!
# Conservative generated native presentations of arbitrary closed theories

The independently supplied theory may have different object and arrow
universes. Its actual upward equivalence puts both at their common bound.
The full generated native context, family, section and predicate quotients
then carry the original identity/composition and indexed projection equations.
The original arrows are conserved by the complete Yoneda readout.

Model soundness is the general local-equation rule interpretation, with no
restriction to representable models. The presheaf interpretation earns the
conservative original-theory comparison and canonical finite-limit/closed
comparisons. This does not assert pseudo initiality or strict equality of
independently chosen semantic type presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryGeneratedPresentation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core
open Mettapedia.CategoryTheory.AsSmallYoneda
open RepresentableIndexedDeclarations

universe u v

noncomputable section

variable (source : LambdaTheory.{u, v})

abbrev normalised : LambdaTheory.{max u v, max u v} :=
  LambdaTheory.ofCategory (Small source.Obj)

abbrev generated := TheoryRepresentables.theory (Small source.Obj)

abbrev contextCategory := TheoryEquations.Contextual.quotientContext (generated source)

abbrev dependentModel := TheoryEquations.Contextual.QuotientCwf.withTerminal (generated source)

/-- The original category enters the whole generated mixed-context category. -/
def original : source.Obj ⥤ contextCategory source :=
  up source.Obj ⋙ TheoryRepresentables.originalFunctor

instance original_faithful : (original source).Faithful := inferInstanceAs
  (up source.Obj ⋙ TheoryRepresentables.originalFunctor).Faithful

theorem original_equation_iff {first last : source.Obj} (left right : first ⟶ last) :
    (original source).map left = (original source).map right ↔ left = right :=
  ⟨fun same => (original source).map_injective same, congrArg (original source).map⟩

/-- The complete represented context is calibrated against the transported
original representable, retaining all of its generalized elements. -/
def objectComparison (object : source.Obj) :
    (objectScope ((up source.Obj).obj object)).1 ≅ raisePresheaf (yoneda.obj object) :=
  (TheoryRepresentables.originalYonedaComparison.app ((up source.Obj).obj object)) ≪≫
    representableIso object

theorem complete_original_readout {first last world : source.Obj}
    (arrow : first ⟶ last) (argument : world ⟶ first) :
    ((objectName ((up source.Obj).obj last)).app
      (Opposite.op ((up source.Obj).obj world))
      ((TheoryRepresentables.quotientReadout ((original source).map arrow)).app
        (Opposite.op ((up source.Obj).obj world))
        ((objectNameInverse ((up source.Obj).obj first)).app
          (Opposite.op ((up source.Obj).obj world)) ((up source.Obj).map argument)))).down =
      argument ≫ arrow := by
  exact congrArg (fun read : (up source.Obj).obj world ⟶ (up source.Obj).obj last => read.down)
    (TheoryRepresentables.generalized_original_readout
      ((up source.Obj).map arrow) ((up source.Obj).map argument))

/-- The constructor comparison uses the actual common-universe closed
theory and its canonical exponential comparison. -/
abbrev productComparison (first last : (normalised source).Obj) :=
  TheoryRepresentables.productComparison first last

abbrev functionComparison (first last : (normalised source).Obj) :=
  TheoryRepresentables.functionComparison first last

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryGeneratedPresentation
