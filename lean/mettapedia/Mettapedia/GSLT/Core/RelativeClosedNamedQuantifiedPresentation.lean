import Mettapedia.GSLT.Core.RelativeClosedStructuralImagePresentation
import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicOperations
import Mettapedia.CategoryTheory.RelativeClosedGeneratedPredicateMaps
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgramHomEquivalence
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedImplication

/-!
# Complete quantification over the combined named presentation

The actual predicate, positioned-modal and constructor-image presentation
first receives its earned internal conjunctive object and implication.
Quantified program completion then supplies both quantifiers along every
arrow of the completed theory, including arrows introduced by completion.
The inclusion retains the complete program relation and the independently
indexed modal and constructor names with their defining equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory
open RelativeClosedGeneratedQuantifier

universe k
variable (source : Theory.{k,k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)

def initialLanguage : PredicateSyntax (RelativeClosedPredicateLogic.lawfulSignature
    (C := source.closed.Obj)) where
  proposition := RelativeClosedPredicateLogic.equationInclusion.object RelativeClosedPredicateLogic.omega
  conjunction := RelativeClosedPredicateLogic.equationInclusion.rawArrow
    RelativeClosedPredicateLogic.conjunctionRaw

def initialTruth := RelativeClosedPredicateLogic.equationInclusion.rawArrow
  (RelativeClosedPredicateLogic.truthRaw (C := source.closed.Obj))

def logicalInclusion :=
  (RelativeClosedPositionedModalPresentation.arrowInclusion source selected).compose
    ((RelativeClosedPositionedModalPresentation.definingInclusion source selected).compose
      ((RelativeClosedStructuralImagePresentation.inclusion source selected constructors).compose
        (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors)))

def language := (initialLanguage source).translate (logicalInclusion source selected constructors)
def truth := (logicalInclusion source selected constructors).rawArrow (initialTruth source)

def predicates := SourceOperations.operations (language source selected constructors)
  (truth source selected constructors)

theorem initial_laws : (SourceOperations.operations (initialLanguage source) (initialTruth source)).Laws :=
  RelativeClosedPredicateLogic.SourceOperations.laws

theorem laws : (predicates source selected constructors).Laws :=
  SourceOperations.translated_laws_across_bases (initialLanguage source) (initialTruth source)
    (logicalInclusion source selected constructors) (initial_laws source)

def initialImplication : InternalPredicateImplication.Qualification
    (SourceOperations.operations (initialLanguage source) (initialTruth source)) :=
  RelativeClosedPredicateLogic.SourceOperations.implicationQualification

def implication : InternalPredicateImplication.Qualification (predicates source selected constructors) :=
  SourceOperations.translatedImplication (initialLanguage source) (initialTruth source)
    (logicalInclusion source selected constructors) (initialImplication source)

def namedTheory : ConjunctiveProgramTheory.{k} where
  programTheory := RelativeClosedStructuralImagePresentation.programTheory source selected constructors
  operations := predicates source selected constructors
  laws := laws source selected constructors

def completed : QuantifiedProgramTheory.{k} :=
  RelativeClosedQuantifiedProgram.freeObject (namedTheory source selected constructors)

def unitMap : ConjunctiveProgramTheory.Map (namedTheory source selected constructors)
    (completed source selected constructors).conjunctive :=
  RelativeClosedQuantifiedProgram.unitMap (namedTheory source selected constructors)

def completeImplication : InternalPredicateImplication.Qualification
    (completed source selected constructors).operations.predicates :=
  RelativeClosedQuantified.Implication.freeQualification
    (namedTheory source selected constructors).conjunctive (implication source selected constructors)

def programInclusion : Map source (completed source selected constructors).programTheory :=
  Map.compose (RelativeClosedStructuralImagePresentation.programInclusion source selected constructors)
    (unitMap source selected constructors).underlying

def constructorArrow (origin : Origins) :=
  (unitMap source selected constructors).functor.map
    (classOf ((RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).rawArrow
      (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin)))

def constructorBody (origin : Origins) :=
  (unitMap source selected constructors).functor.map
    (classOf ((RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).rawArrow
      (RelativeClosedStructuralImagePresentation.definedRaw source selected constructors origin)))

theorem constructor_definition (origin : Origins) :
    constructorArrow source selected constructors origin = constructorBody source selected constructors origin := by
  have retained := congrArg
    (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).functor.map
    (RelativeClosedStructuralImagePresentation.named_operation_is_constructor_image
      source selected constructors origin)
  exact congrArg (unitMap source selected constructors).functor.map retained

def modalInclusion := (RelativeClosedStructuralImagePresentation.inclusion source selected constructors).compose
  (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors)

def modalArrow (origin : Option Index) :=
  (unitMap source selected constructors).functor.map
    (classOf ((modalInclusion source selected constructors).rawArrow
      (RelativeClosedPositionedModalPresentation.namedRaw source selected origin)))

def modalBody (origin : Option Index) :=
  (unitMap source selected constructors).functor.map
    (classOf ((modalInclusion source selected constructors).rawArrow
      (RelativeClosedPositionedModalPresentation.definedRaw source selected origin)))

theorem modal_definition (origin : Option Index) :
    modalArrow source selected constructors origin = modalBody source selected constructors origin := by
  have retained := congrArg (modalInclusion source selected constructors).functor.map
    (RelativeClosedPositionedModalPresentation.named_operation_is_the_authored_expression source selected origin)
  exact congrArg (unitMap source selected constructors).functor.map retained

theorem complete_implication_read {context : (namedTheory source selected constructors).closed.Obj}
    (first second : (predicates source selected constructors).Fiber context) :
    (unitMap source selected constructors).conjunctive.declarations.image
        ((implication source selected constructors).implies (predicates source selected constructors) first second) =
      (completeImplication source selected constructors).implies
        (completed source selected constructors).operations.predicates
        ((unitMap source selected constructors).conjunctive.declarations.image first)
        ((unitMap source selected constructors).conjunctive.declarations.image second) :=
  RelativeClosedQuantified.Implication.unit_supplied
    (namedTheory source selected constructors).conjunctive (implication source selected constructors) first second

variable {source selected constructors}
variable {target : QuantifiedProgramTheory.{k}}
variable (mapping : QuantifiedProgramTheory.Map (completed source selected constructors) target)

local instance mapping_predicates_finite : PreservesFiniteLimits mapping.conjunctive.declarations.functor :=
  mapping.conjunctive.finite

local instance mapping_predicates_closed : MonoidalClosedFunctor mapping.conjunctive.declarations.functor :=
  mapping.conjunctive.closed

theorem both_quantifiers_on_every_arrow
    {before after : (completed source selected constructors).programTheory.closed.Obj}
    (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage mapping.conjunctive.declarations
        ((completed source selected constructors).operations.universal route).operation =
      (target.operations.universal (mapping.functor.map route)).operation ∧
    InternalPredicateFunctionObjectMaps.arrowImage mapping.conjunctive.declarations
        ((completed source selected constructors).operations.existential route).operation =
      (target.operations.existential (mapping.functor.map route)).operation :=
  ⟨QuantifiedProgramTheory.complete_universal_action mapping route,
    QuantifiedProgramTheory.complete_existential_action mapping route⟩

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedPresentation
