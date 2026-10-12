import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedMeaning
import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedLogicalReadout
import Mettapedia.GSLT.Core.RelativeClosedStructuralImageCoherent
import Mettapedia.CategoryTheory.InternalConjunctiveFunctorComparison
import Mettapedia.CategoryTheory.ImplicativeProgramTheory

/-!
# Primitive object comparisons from a completed logical interpretation

Restrict an independently supplied quantified program map to the combined
named presentation and to the original program theory. Its own proposition
comparison then supplies the fresh logical object; the original program
functor supplies the entire base comparison. Both are earned from the
candidate, without an extra primitive-admission field.
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
variable (candidate : QuantifiedProgramTheory.Map (completed source selected constructors) target.quantified)

def named : ConjunctiveProgramTheory.Map (namedTheory source selected constructors)
    target.quantified.conjunctive :=
  ConjunctiveProgramTheory.Map.compose (unitMap source selected constructors) candidate

instance named_finite : PreservesFiniteLimits (named target candidate).functor :=
  (named target candidate).conjunctive.finite

instance named_closed : MonoidalClosedFunctor (named target candidate).functor :=
  (named target candidate).conjunctive.closed

def original : Map source target.quantified.programTheory :=
  Map.compose (programInclusion source selected constructors) candidate.underlying

theorem original_as_named : original target candidate =
    Map.compose (RelativeClosedStructuralImagePresentation.programInclusion source selected constructors)
      (named target candidate).underlying :=
  Map.compose_assoc (RelativeClosedStructuralImagePresentation.programInclusion source selected constructors)
    (unitMap source selected constructors).underlying candidate.underlying

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
