import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramFrameAction
import Mettapedia.CategoryTheory.InternalPredicateConstructorMaps

/-!
# Structural constructor action in the universal program extension

Every actual source constructor supplies an existential image operation in
the quantified completion. The universal program map acts on this operation
with its independently earned program reading. An independently supplied
target constructor and argument comparison need one local constructor
equation; the complete operator and every future input then follow.

These are structural image bodies. Exclusive syntactic root classification
and equation descent retain their additional admission obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory
open RelativeClosedQuantified RelativeClosedQuantifiedRuleFrames
open InternalPredicateFunctionObject InternalPredicateConstructorMaps

universe k
variable {source target : Theory.{k,k}}
variable {predicates : InternalConjunctiveObject.Operations source.closed.Obj} {laws : predicates.Laws}
variable {quantified : InternalPredicateQuantifiedObject.Operations target.closed.Obj}
variable {arguments : source.closed.Obj} (constructor : arguments ⟶ source.program)

def structuralImage :
    power (freeObject (conjunctive source predicates laws)).operations.predicates
        ((inclusion source predicates laws).functor.obj arguments) ⟶
      power (freeObject (conjunctive source predicates laws)).operations.predicates
        (generatedTheory source predicates laws).program :=
  ((freeObject (conjunctive source predicates laws)).operations.existential
    ((inclusion source predicates laws).functor.map constructor)).operation

namespace Supplied

variable (supplied : Supplied source target predicates laws quantified)

variable {actualArguments : target.closed.Obj}
variable (argumentComparison : supplied.extension.functor.obj
  ((inclusion source predicates laws).functor.obj arguments) ≅ actualArguments)
variable (actualConstructor : actualArguments ⟶ target.program)
variable (square : supplied.extension.functor.map
    ((inclusion source predicates laws).functor.map constructor) ≫ supplied.extendedProgram.hom =
  argumentComparison.hom ≫ actualConstructor)

include square in
theorem complete_structural_image_square :
    supplied.extension.functor.map (structuralImage (source := source) (predicates := predicates)
        (laws := laws) constructor) ≫
        (comparedPower supplied.predicateComparison.quantified
          (generatedTheory source predicates laws).program supplied.extendedProgram).hom =
      (comparedPower supplied.predicateComparison.quantified
          ((inclusion source predicates laws).functor.obj arguments) argumentComparison).hom ≫
        (quantified.existential actualConstructor).operation :=
  complete_independent_square supplied.predicateComparison.quantified
    ((inclusion source predicates laws).functor.map constructor)
    argumentComparison supplied.extendedProgram actualConstructor square

include square in
theorem complete_structural_future_family {first second : (generatedTheory source predicates laws).closed.Obj}
    (future : first ⟶ second)
    (predicate : second ⟶ power (freeObject (conjunctive source predicates laws)).operations.predicates
      ((inclusion source predicates laws).functor.obj arguments)) :
    supplied.extension.functor.map ((future ≫ predicate) ≫
        structuralImage (source := source) (predicates := predicates) (laws := laws) constructor) ≫
        (comparedPower supplied.predicateComparison.quantified
          (generatedTheory source predicates laws).program supplied.extendedProgram).hom =
      supplied.extension.functor.map future ≫
        ((supplied.extension.functor.map predicate ≫
          (comparedPower supplied.predicateComparison.quantified
            ((inclusion source predicates laws).functor.obj arguments) argumentComparison).hom) ≫
              (quantified.existential actualConstructor).operation) :=
  complete_future_family supplied.predicateComparison.quantified
    ((inclusion source predicates laws).functor.map constructor)
    argumentComparison supplied.extendedProgram actualConstructor square future predicate

end Supplied

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps
