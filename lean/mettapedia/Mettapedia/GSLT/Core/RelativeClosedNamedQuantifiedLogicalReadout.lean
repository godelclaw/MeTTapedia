import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedPresentation
import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicQuantifiers

/-!
# Old logical declarations agree with complete quantified operations

The original three-diagram quantifier qualifications transport through the
combined named inclusion and quantified completion. Operation uniqueness
then identifies their complete function images with the independently
constructed quantifiers of the completed theory. This supplies both whole
operator and parameterized-section readings, rather than agreement only at
truth or at one supplied argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedLogicalReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory
open RelativeClosedNamedQuantifiedPresentation
open RelativeClosedGeneratedQuantifier
open RelativeClosedGeneratedQuantifier.SourceOperations
open InternalPredicateFunctionObjectMaps

universe k
variable (source : Theory.{k,k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)

local instance unit_finite : PreservesFiniteLimits (unitMap source selected constructors).functor :=
  (unitMap source selected constructors).conjunctive.finite

local instance unit_closed : MonoidalClosedFunctor (unitMap source selected constructors).functor :=
  (unitMap source selected constructors).conjunctive.closed

def logicalMap : InternalConjunctiveObject.Map
    (SourceOperations.operations (initialLanguage source) (initialTruth source))
    (completed source selected constructors).operations.predicates :=
  InternalConjunctiveObject.Map.comp
    (translatedMap (initialLanguage source) (initialTruth source) (logicalInclusion source selected constructors))
    (unitMap source selected constructors).conjunctive.declarations

instance logicalMap_finite : PreservesFiniteLimits (logicalMap source selected constructors).functor := by
  change PreservesFiniteLimits ((logicalInclusion source selected constructors).functor ⋙
    (unitMap source selected constructors).conjunctive.declarations.functor)
  let := (unitMap source selected constructors).conjunctive.finite
  exact comp_preservesFiniteLimits (logicalInclusion source selected constructors).functor
    (unitMap source selected constructors).conjunctive.declarations.functor

local instance complete_composite_finite : PreservesFiniteLimits
    ((logicalInclusion source selected constructors).functor ⋙
      (unitMap source selected constructors).conjunctive.declarations.functor) :=
  logicalMap_finite source selected constructors

instance logicalMap_closed : MonoidalClosedFunctor (logicalMap source selected constructors).functor := by
  change MonoidalClosedFunctor ((logicalInclusion source selected constructors).functor ⋙
    (unitMap source selected constructors).conjunctive.declarations.functor)
  let := (unitMap source selected constructors).conjunctive.finite
  let := (unitMap source selected constructors).conjunctive.closed
  exact CartesianClosedFunctorCoherence.closed_composition (logicalInclusion source selected constructors).functor
    (unitMap source selected constructors).conjunctive.declarations.functor

def baseRoute {before after : source.closed.Obj} (route : before ⟶ after) :=
  (baseFunctor (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))).map route

theorem complete_base_route {before after : source.closed.Obj} (route : before ⟶ after) :
    (logicalMap source selected constructors).functor.map (baseRoute source route) =
      (programInclusion source selected constructors).closed.functor.map route := rfl

theorem universal_read {before after : source.closed.Obj} (route : before ⟶ after) :
    arrowImage (logicalMap source selected constructors)
        (RelativeClosedPredicateLogic.SourceOperations.universalQualification route).operation =
      ((completed source selected constructors).operations.universal
        ((programInclusion source selected constructors).closed.functor.map route)).operation :=
  InternalPredicateQuantifierMaps.universal_image (logicalMap source selected constructors)
    (baseRoute source route) (completed source selected constructors).operations.laws
    (RelativeClosedPredicateLogic.SourceOperations.universalQualification route)
    ((completed source selected constructors).operations.universal
      ((programInclusion source selected constructors).closed.functor.map route))

theorem existential_read {before after : source.closed.Obj} (route : before ⟶ after) :
    arrowImage (logicalMap source selected constructors)
        (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route).operation =
      ((completed source selected constructors).operations.existential
        ((programInclusion source selected constructors).closed.functor.map route)).operation :=
  InternalPredicateQuantifierMaps.existential_image (logicalMap source selected constructors)
    (baseRoute source route) (completed source selected constructors).operations.laws
    (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route)
    ((completed source selected constructors).operations.existential
      ((programInclusion source selected constructors).closed.functor.map route))

theorem complete_universal_section {before after : source.closed.Obj}
    {parameter : Object (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))}
    (route : before ⟶ after)
    (predicate : parameter ⟶ InternalPredicateFunctionObject.power
      (SourceOperations.operations (initialLanguage source) (initialTruth source)) (baseObject _ before)) :
    sectionImage (logicalMap source selected constructors)
        (predicate ≫ (RelativeClosedPredicateLogic.SourceOperations.universalQualification route).operation) =
      sectionImage (logicalMap source selected constructors) predicate ≫
        ((completed source selected constructors).operations.universal
          ((programInclusion source selected constructors).closed.functor.map route)).operation := by
  have carried := arrowImage_section (logicalMap source selected constructors) predicate
    (RelativeClosedPredicateLogic.SourceOperations.universalQualification route).operation
  exact carried.trans (congrArg
    (fun operation => sectionImage (logicalMap source selected constructors) predicate ≫ operation)
    (universal_read source selected constructors route))

theorem complete_existential_section {before after : source.closed.Obj}
    {parameter : Object (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))}
    (route : before ⟶ after)
    (predicate : parameter ⟶ InternalPredicateFunctionObject.power
      (SourceOperations.operations (initialLanguage source) (initialTruth source)) (baseObject _ before)) :
    sectionImage (logicalMap source selected constructors)
        (predicate ≫ (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route).operation) =
      sectionImage (logicalMap source selected constructors) predicate ≫
        ((completed source selected constructors).operations.existential
          ((programInclusion source selected constructors).closed.functor.map route)).operation := by
  have carried := arrowImage_section (logicalMap source selected constructors) predicate
    (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route).operation
  exact carried.trans (congrArg
    (fun operation => sectionImage (logicalMap source selected constructors) predicate ≫ operation)
    (existential_read source selected constructors route))

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedLogicalReadout
