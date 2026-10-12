import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

/-!
# Old logical readings forced by an arbitrary completed interpretation

Finite-limit closedness and the supplied truth/conjunction comparison
transport the old finite qualifications. Uniqueness of the qualified
operations identifies their complete function images with the target's
independently chosen implication and quantifiers. The parameterized readings
retain every supplied section and its argument context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open ProgramReductionTheory RelativeClosedNamedQuantifiedPresentation
open RelativeClosedGeneratedQuantifier RelativeClosedGeneratedQuantifier.SourceOperations
open InternalPredicateFunctionObjectMaps

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable (target : QuantifiedImplicativeProgramTheory.{k})
variable (candidate : QuantifiedProgramTheory.Map (completed source selected constructors) target.quantified)

def logicalPredicates : InternalConjunctiveObject.Map
    (SourceOperations.operations (initialLanguage source) (initialTruth source))
    target.quantified.operations.predicates :=
  InternalConjunctiveObject.Map.comp
    (translatedMap (initialLanguage source) (initialTruth source) (logicalInclusion source selected constructors))
    (named target candidate).conjunctive.declarations

instance logicalPredicates_finite : PreservesFiniteLimits (logicalPredicates target candidate).functor := by
  let := (named target candidate).conjunctive.finite
  change PreservesFiniteLimits ((logicalInclusion source selected constructors).functor ⋙
    (named target candidate).conjunctive.declarations.functor)
  exact comp_preservesFiniteLimits _ _

local instance composite_finite : PreservesFiniteLimits
    ((logicalInclusion source selected constructors).functor ⋙
      (named target candidate).conjunctive.declarations.functor) :=
  logicalPredicates_finite target candidate

instance logicalPredicates_closed : MonoidalClosedFunctor (logicalPredicates target candidate).functor := by
  let := (named target candidate).conjunctive.finite
  let := (named target candidate).conjunctive.closed
  change MonoidalClosedFunctor ((logicalInclusion source selected constructors).functor ⋙
    (named target candidate).conjunctive.declarations.functor)
  exact CartesianClosedFunctorCoherence.closed_composition _ _

theorem logical_base_route {before after : source.closed.Obj} (route : before ⟶ after) :
    (logicalPredicates target candidate).functor.map
        (RelativeClosedNamedQuantifiedLogicalReadout.baseRoute source route) =
      (original target candidate).closed.functor.map route := rfl

theorem universal_forced {before after : source.closed.Obj} (route : before ⟶ after) :
    arrowImage (logicalPredicates target candidate)
        (RelativeClosedPredicateLogic.SourceOperations.universalQualification route).operation =
      (target.quantified.operations.universal
        ((original target candidate).closed.functor.map route)).operation :=
  InternalPredicateQuantifierMaps.universal_image (logicalPredicates target candidate)
    (RelativeClosedNamedQuantifiedLogicalReadout.baseRoute source route) target.quantified.operations.laws
    (RelativeClosedPredicateLogic.SourceOperations.universalQualification route)
    (target.quantified.operations.universal ((original target candidate).closed.functor.map route))

theorem existential_forced {before after : source.closed.Obj} (route : before ⟶ after) :
    arrowImage (logicalPredicates target candidate)
        (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route).operation =
      (target.quantified.operations.existential
        ((original target candidate).closed.functor.map route)).operation :=
  InternalPredicateQuantifierMaps.existential_image (logicalPredicates target candidate)
    (RelativeClosedNamedQuantifiedLogicalReadout.baseRoute source route) target.quantified.operations.laws
    (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route)
    (target.quantified.operations.existential ((original target candidate).closed.functor.map route))

theorem implication_forced :
    InternalPredicateImplicationMaps.operationImage (logicalPredicates target candidate)
        (initialImplication source).operation = target.implication.operation :=
  InternalPredicateImplicationMaps.implication_image (logicalPredicates target candidate)
    target.quantified.operations.laws (initialImplication source) target.implication

theorem universal_complete_section {before after : source.closed.Obj}
    {parameter : Object (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))}
    (route : before ⟶ after)
    (predicate : parameter ⟶ InternalPredicateFunctionObject.power
      (SourceOperations.operations (initialLanguage source) (initialTruth source)) (baseObject _ before)) :
    sectionImage (logicalPredicates target candidate)
        (predicate ≫ (RelativeClosedPredicateLogic.SourceOperations.universalQualification route).operation) =
      sectionImage (logicalPredicates target candidate) predicate ≫
        (target.quantified.operations.universal
          ((original target candidate).closed.functor.map route)).operation :=
  (arrowImage_section (logicalPredicates target candidate) predicate _).trans
    (congrArg (fun operation => sectionImage (logicalPredicates target candidate) predicate ≫ operation)
      (universal_forced target candidate route))

theorem existential_complete_section {before after : source.closed.Obj}
    {parameter : Object (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))}
    (route : before ⟶ after)
    (predicate : parameter ⟶ InternalPredicateFunctionObject.power
      (SourceOperations.operations (initialLanguage source) (initialTruth source)) (baseObject _ before)) :
    sectionImage (logicalPredicates target candidate)
        (predicate ≫ (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route).operation) =
      sectionImage (logicalPredicates target candidate) predicate ≫
        (target.quantified.operations.existential
          ((original target candidate).closed.functor.map route)).operation :=
  (arrowImage_section (logicalPredicates target candidate) predicate _).trans
    (congrArg (fun operation => sectionImage (logicalPredicates target candidate) predicate ≫ operation)
      (existential_forced target candidate route))

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
