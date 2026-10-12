import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedPresentation
import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedLogicalReadout
import Mettapedia.CategoryTheory.RelativeClosedGeneratedPredicateOperationMaps

/-!
# Logical qualifications on the actual combined native declarations

The original finite law diagrams transport into the combined named syntax.
Both quantified operations are the actual translated declaration arrows;
the function comparisons do not insert a different operation. Implication
has the corresponding complete binary-arrow reading.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory
open RelativeClosedGeneratedQuantifier RelativeClosedGeneratedQuantifier.SourceOperations

universe k
variable (source : Theory.{k,k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)

def nativeLogicalMap := translatedMap (initialLanguage source) (initialTruth source)
  (logicalInclusion source selected constructors)

instance nativeLogical_finite : PreservesFiniteLimits (nativeLogicalMap source selected constructors).functor := by
  change PreservesFiniteLimits (logicalInclusion source selected constructors).functor
  infer_instance

instance nativeLogical_closed : MonoidalClosedFunctor (nativeLogicalMap source selected constructors).functor := by
  change MonoidalClosedFunctor (logicalInclusion source selected constructors).functor
  infer_instance

def nativeBaseRoute {before after : source.closed.Obj} (route : before ⟶ after) :=
  baseArrow (signature := RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) route

def nativeUniversal {before after : source.closed.Obj} (route : before ⟶ after) :
    InternalPredicateQuantifier.Universal (predicates source selected constructors)
      (nativeBaseRoute source selected constructors route) :=
  InternalPredicateQuantifierMaps.universalImage (nativeLogicalMap source selected constructors)
    (RelativeClosedNamedQuantifiedLogicalReadout.baseRoute source route)
    (RelativeClosedPredicateLogic.SourceOperations.universalQualification route)

def nativeExistential {before after : source.closed.Obj} (route : before ⟶ after) :
    InternalPredicateExistential.Existential (predicates source selected constructors)
      (nativeBaseRoute source selected constructors route) :=
  InternalPredicateQuantifierMaps.existentialImage (nativeLogicalMap source selected constructors)
    (RelativeClosedNamedQuantifiedLogicalReadout.baseRoute source route)
    (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route)

theorem native_universal_operation {before after : source.closed.Obj} (route : before ⟶ after) :
    (nativeUniversal source selected constructors route).operation =
      (logicalInclusion source selected constructors).functor.map
        (RelativeClosedPredicateLogic.SourceOperations.universalQualification route).operation :=
  translated_operation (initialLanguage source) (initialTruth source)
    (logicalInclusion source selected constructors) _

theorem native_existential_operation {before after : source.closed.Obj} (route : before ⟶ after) :
    (nativeExistential source selected constructors route).operation =
      (logicalInclusion source selected constructors).functor.map
        (RelativeClosedPredicateLogic.SourceOperations.existentialQualification route).operation :=
  translated_operation (initialLanguage source) (initialTruth source)
    (logicalInclusion source selected constructors) _

theorem native_implication_operation :
    (implication source selected constructors).operation =
      (logicalInclusion source selected constructors).functor.map (initialImplication source).operation :=
  translated_binary_operation (initialLanguage source) (initialTruth source)
    (logicalInclusion source selected constructors) _

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedPresentation
