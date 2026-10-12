import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

/-!
# Independent comparisons on the original program theory

A named interpretation may be compared with an independently chosen
original program map. The compatible program-map isomorphism supplies the
base comparison; the named predicate map supplies the proposition
comparison. Neither input presupposes the interpretation of primitive
logical, modal or constructor declarations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization
open ProgramReductionTheory RelativeClosedNamedQuantifiedPresentation

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable (target : QuantifiedImplicativeProgramTheory.{k})

structure OriginComparison where
  named : ConjunctiveProgramTheory.Map (namedTheory source selected constructors)
    target.quantified.conjunctive
  original : Map source target.quantified.programTheory
  restriction : ProgramReductionTheoryIsoClasses.MapIso
    (Map.compose (RelativeClosedStructuralImagePresentation.programInclusion source selected constructors)
      named.underlying) original

def ownOriginComparison
    (candidate : QuantifiedProgramTheory.Map (completed source selected constructors) target.quantified) :
    OriginComparison (source := source) (selected := selected) (constructors := constructors) target where
  named := named target candidate
  original := original target candidate
  restriction := by
    rw [← original_as_named target candidate]
    exact ProgramReductionTheoryIsoClasses.MapIso.refl _

variable {target}
variable (data : OriginComparison (source := source) (selected := selected) (constructors := constructors) target)

instance origin_named_finite : PreservesFiniteLimits data.named.functor := data.named.conjunctive.finite

instance origin_named_closed : MonoidalClosedFunctor data.named.functor := data.named.conjunctive.closed

def model := RelativeClosedNamedQuantifiedMeaning.localModel source target.quantified selected constructors
  data.original.closed.functor target.implication

def primitiveImages : AtomicPresentation.PrimitiveImages data.named.functor
    (model data).nativeModel.meanings where
  base := data.restriction.comparison
  object := by
    rintro ⟨⟨⟨⟩⟩⟩
    exact data.named.conjunctive.declarations.proposition

def atomicFunctor := AtomicPresentation.functor data.named.functor
  (model data).nativeModel.meanings (primitiveImages data)

instance atomic_finite : PreservesFiniteLimits (atomicFunctor data) := by
  let := data.named.conjunctive.finite
  exact AtomicPresentation.functor_preservesFiniteLimits _ _ _

instance atomic_closed : MonoidalClosedFunctor (atomicFunctor data) := by
  let := data.named.conjunctive.finite
  let := data.named.conjunctive.closed
  exact AtomicPresentation.functor_closed _ _ _

def atomicPredicates : InternalConjunctiveObject.Map (predicates source selected constructors)
    target.quantified.operations.predicates :=
  InternalConjunctiveObject.Map.ofFunctorIso data.named.conjunctive.declarations
    (AtomicPresentation.comparison data.named.functor
      (model data).nativeModel.meanings (primitiveImages data))

theorem entire_original_base :
    baseFunctor (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) ⋙
      atomicFunctor data = data.original.closed.functor :=
  AtomicPresentation.functor_base _ _ _

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
