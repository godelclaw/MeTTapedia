import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedModels

/-!
# Local named meanings from an arbitrary quantified target

An independently supplied weak base functor, a quantified target program
theory and its locally qualified implication construct all thirteen logical
diagram families. Actual existential and positioned-modal operations supply
the named meanings. Their local evaluations earn a realized combined model
and its three predicate readings without requiring a presheaf target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedMeaning

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory
open RelativeClosedGeneratedQuantifier.SourceOperations
open RelativeClosedNamedQuantifiedPresentation

universe k
variable (source : Theory.{k,k}) (target : QuantifiedProgramTheory.{k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)
variable (base : source.closed.Obj ⥤ target.programTheory.closed.Obj)
variable [PreservesFiniteLimits base] [MonoidalClosedFunctor base]
variable (qualified : InternalPredicateImplication.Qualification target.operations.predicates)

def meaning : RelativeClosedPredicateLogic.Interpretation.Meaning base where
  predicates := target.operations.predicates
  implication := qualified.operation
  universal route := (target.operations.universal (base.map route)).operation
  existential route := (target.operations.existential (base.map route)).operation

omit [PreservesFiniteLimits base] [MonoidalClosedFunctor base] in
theorem admitted : RelativeClosedPredicateLogic.Interpretation.Admission base (meaning source target base qualified) where
  conjunction := target.operations.laws
  implicationMonotonicity := qualified.monotonicity
  implicationUnit := qualified.unit
  implicationCounit := qualified.counit
  universalMonotonicity route := (target.operations.universal (base.map route)).monotonicity
  universalUnit route := (target.operations.universal (base.map route)).unit
  universalCounit route := (target.operations.universal (base.map route)).counit
  existentialMonotonicity route := (target.operations.existential (base.map route)).monotonicity
  existentialUnit route := (target.operations.existential (base.map route)).unit
  existentialCounit route := (target.operations.existential (base.map route)).counit

def localModel : RelativeClosedStructuralImageLocalModels.LocalModel source selected constructors
    target.programTheory.closed.Obj where
  previous := {
    base := base
    baseFinite := inferInstance
    baseClosed := inferInstance
    predicates := meaning source target base qualified
    finiteDiagrams := admitted source target base qualified
    modalValues := RelativeClosedPositionedModalRealization.expectedValue source selected base
      (meaning source target base qualified)
    modalDiagrams := fun _ => rfl }
  constructorValues := RelativeClosedStructuralImageRealization.expectedValue source constructors base
    (meaning source target base qualified)
  constructorDiagrams := fun _ => rfl

theorem predicateReadings : PredicateReadings (language source selected constructors)
    (truth source selected constructors)
    (localModel source target selected constructors base qualified).nativeModel target.operations.predicates where
  proposition := rfl
  truth := rfl
  conjunction := rfl

variable (original : Map source target.programTheory)

def extension : QuantifiedProgramTheory.Map (completed source selected constructors) target :=
  RelativeClosedNamedQuantifiedModels.extension
    (localModel source target selected constructors original.closed.functor qualified)
    (predicateReadings source target selected constructors original.closed.functor qualified)
    original (Iso.refl _)

theorem complete_authored_firing (origin : Index) :
    (extension source target selected constructors qualified original).functor.map
        (AuthoredClosedTheory.Rule.transport (programInclusion source selected constructors)
          (selected origin).rule).action ≫
          (extension source target selected constructors qualified original).reduction =
      (RelativeClosedNamedQuantifiedModels.sourceComparison
        (localModel source target selected constructors original.closed.functor qualified)
        (predicateReadings source target selected constructors original.closed.functor qualified)
        original (Iso.refl _)).comparison.hom.app (selected origin).rule.parameters ≫
          (original.closed.functor.map (selected origin).rule.action ≫ original.reduction) :=
  RelativeClosedNamedQuantifiedModels.complete_authored_firing
    (localModel source target selected constructors original.closed.functor qualified)
    (predicateReadings source target selected constructors original.closed.functor qualified)
    original (Iso.refl _) origin

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedMeaning
