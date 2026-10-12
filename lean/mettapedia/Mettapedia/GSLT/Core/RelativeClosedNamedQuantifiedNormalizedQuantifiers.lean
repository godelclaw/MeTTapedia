import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedNormalizedFunctions
import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedNativeDeclarations
import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowValueComparison

/-!
# Complete normalized quantifier values are independently determined

The native finite qualifications force both operations under the candidate's
weak closed interpretation. Whole function comparisons then recover their
independently formed argument and result objects. Equality of the complete
base functors identifies these values with the original program map's
chosen target quantifiers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization Interpretation
open ProgramReductionTheory RelativeClosedNamedQuantifiedPresentation
open InternalPredicateFunctionObjectMaps

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable {target : QuantifiedImplicativeProgramTheory.{k}}
variable (data : OriginComparison (source := source) (selected := selected) (constructors := constructors) target)

def universalValue (target : QuantifiedImplicativeProgramTheory.{k}) (base : source.closed.Obj ⥤ target.quantified.programTheory.closed.Obj)
    {before after : source.closed.Obj} (route : before ⟶ after) :
    ArrowValue target.quantified.programTheory.closed.Obj :=
  ⟨InternalPredicateFunctionObject.power target.quantified.operations.predicates (base.obj before),
    InternalPredicateFunctionObject.power target.quantified.operations.predicates (base.obj after),
    (target.quantified.operations.universal (base.map route)).operation⟩

def existentialValue (target : QuantifiedImplicativeProgramTheory.{k}) (base : source.closed.Obj ⥤ target.quantified.programTheory.closed.Obj)
    {before after : source.closed.Obj} (route : before ⟶ after) :
    ArrowValue target.quantified.programTheory.closed.Obj :=
  ⟨InternalPredicateFunctionObject.power target.quantified.operations.predicates (base.obj before),
    InternalPredicateFunctionObject.power target.quantified.operations.predicates (base.obj after),
    (target.quantified.operations.existential (base.map route)).operation⟩

theorem normalized_universal_value {before after : source.closed.Obj} (route : before ⟶ after) :
    (⟨(normalized data).obj (InternalPredicateFunctionObject.power
          (predicates source selected constructors) (baseObject _ before)),
      (normalized data).obj (InternalPredicateFunctionObject.power
          (predicates source selected constructors) (baseObject _ after)),
      (normalized data).map (nativeUniversal source selected constructors route).operation⟩ :
        ArrowValue target.quantified.programTheory.closed.Obj) =
      universalValue target data.original.closed.functor route := by
  let first := baseObject (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) before
  let second := baseObject (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) after
  have forced := InternalPredicateQuantifierMaps.universal_image (normalizedPredicates data)
    (nativeBaseRoute source selected constructors route) target.quantified.operations.laws
    (nativeUniversal source selected constructors route)
    (target.quantified.operations.universal
      ((normalized data).map (nativeBaseRoute source selected constructors route)))
  have read :
      eqToHom (normalized_function_object data first).symm ≫
        (normalized data).map (nativeUniversal source selected constructors route).operation ≫
          eqToHom (normalized_function_object data second) =
        (target.quantified.operations.universal
          ((normalized data).map (nativeBaseRoute source selected constructors route))).operation :=
    (congrArg₂
      (fun incoming outgoing => incoming ≫
        (normalized data).map (nativeUniversal source selected constructors route).operation ≫ outgoing)
      (normalized_function_inv data first).symm
      (normalized_function_hom data second).symm).trans forced
  exact (ArrowValue.eq_of_cast (normalized_function_object data first)
      (normalized_function_object data second) _ _ read).trans
    (congrArg (fun base : source.closed.Obj ⥤ target.quantified.programTheory.closed.Obj =>
      universalValue target base route) (entire_normalized_base data))

theorem normalized_existential_value {before after : source.closed.Obj} (route : before ⟶ after) :
    (⟨(normalized data).obj (InternalPredicateFunctionObject.power
          (predicates source selected constructors) (baseObject _ before)),
      (normalized data).obj (InternalPredicateFunctionObject.power
          (predicates source selected constructors) (baseObject _ after)),
      (normalized data).map (nativeExistential source selected constructors route).operation⟩ :
        ArrowValue target.quantified.programTheory.closed.Obj) =
      existentialValue target data.original.closed.functor route := by
  let first := baseObject (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) before
  let second := baseObject (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) after
  have forced := InternalPredicateQuantifierMaps.existential_image (normalizedPredicates data)
    (nativeBaseRoute source selected constructors route) target.quantified.operations.laws
    (nativeExistential source selected constructors route)
    (target.quantified.operations.existential
      ((normalized data).map (nativeBaseRoute source selected constructors route)))
  have read :
      eqToHom (normalized_function_object data first).symm ≫
        (normalized data).map (nativeExistential source selected constructors route).operation ≫
          eqToHom (normalized_function_object data second) =
        (target.quantified.operations.existential
          ((normalized data).map (nativeBaseRoute source selected constructors route))).operation :=
    (congrArg₂
      (fun incoming outgoing => incoming ≫
        (normalized data).map (nativeExistential source selected constructors route).operation ≫ outgoing)
      (normalized_function_inv data first).symm
      (normalized_function_hom data second).symm).trans forced
  exact (ArrowValue.eq_of_cast (normalized_function_object data first)
      (normalized_function_object data second) _ _ read).trans
    (congrArg (fun base : source.closed.Obj ⥤ target.quantified.programTheory.closed.Obj =>
      existentialValue target base route) (entire_normalized_base data))

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
