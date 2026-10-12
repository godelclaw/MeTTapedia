import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedProgramComparison

/-!
# Complete extension and restriction comparisons for bare program maps

An arbitrary original program map into a quantified implication-qualified
target constructs the complete named logical interpretation. Restriction
recovers that program map through its actual compatible comparison. Every
completed interpretation is in turn coherently isomorphic to the extension
of its own original restriction, without a supplied native admission.

These concrete-map comparisons retain raw contexts and extend arbitrary
compatible original-map isomorphisms. The hom-class equivalence and the
resulting varying-theory adjunction require their additional constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedNamedQuantifiedPresentation

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)
variable (target : QuantifiedImplicativeProgramTheory.{k})

def extendOriginal (original : Map source target.quantified.programTheory) :
    QuantifiedProgramTheory.Map (completed source selected constructors) target.quantified :=
  RelativeClosedNamedQuantifiedMeaning.extension source target.quantified selected constructors target.implication original

def recoverOriginal (original : Map source target.quantified.programTheory) :
    ProgramReductionTheoryIsoClasses.MapIso
      (Map.compose (programInclusion source selected constructors)
        (extendOriginal selected constructors target original).underlying) original :=
  RelativeClosedNamedQuantifiedModels.sourceComparison
    (RelativeClosedNamedQuantifiedMeaning.localModel source target.quantified selected constructors
      original.closed.functor target.implication)
    (RelativeClosedNamedQuantifiedMeaning.predicateReadings source target.quantified selected constructors
      original.closed.functor target.implication) original (Iso.refl _)

variable {selected constructors}
variable (candidate : QuantifiedProgramTheory.Map (completed source selected constructors) target.quantified)

def comparedOrigin (originalMap : Map source target.quantified.programTheory)
    (comparison : ProgramReductionTheoryIsoClasses.MapIso (original target candidate) originalMap) :
    OriginComparison (source := source) (selected := selected) (constructors := constructors) target where
  named := named target candidate
  original := originalMap
  restriction := by
    rw [← original_as_named target candidate]
    exact comparison

def completeComparisonWithOriginal (originalMap : Map source target.quantified.programTheory)
    (comparison : ProgramReductionTheoryIsoClasses.MapIso (original target candidate) originalMap) :
    QuantifiedProgramTheory.MapIso candidate (extendOriginal selected constructors target originalMap) :=
  RelativeClosedNamedQuantifiedModels.completeComparison (model (comparedOrigin target candidate originalMap comparison))
    (RelativeClosedNamedQuantifiedMeaning.predicateReadings source target.quantified selected constructors
      originalMap.closed.functor target.implication)
    originalMap (Iso.refl _) candidate (namedComparison (comparedOrigin target candidate originalMap comparison))

def completeComparison : QuantifiedProgramTheory.MapIso candidate
    (extendOriginal selected constructors target (original target candidate)) :=
  completeComparisonWithOriginal target candidate (original target candidate)
    (ProgramReductionTheoryIsoClasses.MapIso.refl _)

def extensionComparison {first second : Map source target.quantified.programTheory}
    (comparison : ProgramReductionTheoryIsoClasses.MapIso first second) :
    QuantifiedProgramTheory.MapIso
      (extendOriginal selected constructors target first)
      (extendOriginal selected constructors target second) :=
  completeComparisonWithOriginal target (extendOriginal selected constructors target first) second
    ((recoverOriginal selected constructors target first).trans comparison)

theorem entire_completed_event_square :
    (completeComparison target candidate).comparison.hom.app (completed source selected constructors).programTheory.Event ≫
        (extendOriginal selected constructors target (original target candidate)).reduction = candidate.reduction :=
  (completeComparison target candidate).underlying.reduction_square

theorem entire_completed_firing (origin : Index) :
    candidate.functor.map
        (Rule.transport (programInclusion source selected constructors) (selected origin).rule).action ≫
          candidate.reduction =
      (completeComparison target candidate).comparison.hom.app
          (Rule.transport (programInclusion source selected constructors) (selected origin).rule).parameters ≫
        ((extendOriginal selected constructors target (original target candidate)).functor.map
          (Rule.transport (programInclusion source selected constructors) (selected origin).rule).action ≫
            (extendOriginal selected constructors target (original target candidate)).reduction) := by
  have natural := (completeComparison target candidate).comparison.hom.naturality
    (Rule.transport (programInclusion source selected constructors) (selected origin).rule).action
  rw [← entire_completed_event_square target candidate, ← Category.assoc, natural, Category.assoc]

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
