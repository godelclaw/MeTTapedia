import Mettapedia.CategoryTheory.ImplicativeProgramTheory

/-!
# Forgetting complete logic to the actual program theory

The functor forgets the proposition operations and qualifications while
retaining each closed program map and its compatible program comparison.
Its morphisms remain classes of independently supplied weak maps.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.QuantifiedImplicativeProgramTheory

open _root_.CategoryTheory

universe k

def forgetProgram : QuantifiedImplicativeProgramTheory.{k} ⥤ ProgramReductionTheoryIsoClasses.{k} :=
  forget ⋙ ImplicativeProgramTheory.forget ⋙ ConjunctiveProgramTheory.forget

theorem forgetProgram_classOf {source target : QuantifiedImplicativeProgramTheory.{k}}
    (mapping : Map source target) :
    forgetProgram.map (classOf mapping) = ProgramReductionTheoryIsoClasses.classOf mapping.underlying := rfl

end Mettapedia.CategoryTheory.QuantifiedImplicativeProgramTheory
