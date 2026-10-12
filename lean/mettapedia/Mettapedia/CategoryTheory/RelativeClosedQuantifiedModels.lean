import Mettapedia.CategoryTheory.RelativeClosedQuantifiedStage
import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObjectTransport
import Mettapedia.CategoryTheory.RelativeClosedBaseCanonicalReadout

/-!
# Independent quantified target models over weak closed maps

The original proposition comparison re-presents the target predicate object
at the image of the supplied source proposition. Actual inverse terminal and
product comparisons interpret the two initial operation expressions. Their
finite local operation squares prove the complete truth and conjunction
readings. Every later quantifier is then constructed by the already earned
closure interpretation; no initial model or whole-arrow interpretation is
supplied as a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.Models

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory
open RelativeClosedGeneratedQuantifier Iteration

universe k
variable {source : ConjunctiveClosedTheory.{k}} {target : QuantifiedClosedTheory.{k}}
variable (mapping : ConjunctiveClosedTheory.Map source target.conjunctive)

abbrev quantifiers := InternalPredicateQuantifiedObject.Transport.operations
  target.operations mapping.declarations.proposition

abbrev meanings := BaseComparisons.WeakDiagram.assignment mapping.functor
abbrev realization := BaseComparisons.WeakDiagram.realization mapping.functor

instance meanings_finite : PreservesFiniteLimits (meanings mapping).base := mapping.finite
instance meanings_closed : MonoidalClosedFunctor (meanings mapping).base := mapping.closed

theorem truth_arrow :
    inv (CartesianMonoidalCategory.terminalComparison mapping.functor) ≫ mapping.functor.map source.operations.truth =
      (quantifiers mapping).predicates.truth := by
  change inv (CartesianMonoidalCategory.terminalComparison mapping.functor) ≫ mapping.functor.map source.operations.truth =
    target.operations.predicates.truth ≫ mapping.declarations.proposition.inv
  apply (cancel_mono mapping.declarations.proposition.hom).mp
  simp only [Category.assoc, mapping.declarations.proposition.inv_hom_id]
  rw [mapping.declarations.truth, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  exact (Category.comp_id target.operations.predicates.truth).symm

theorem conjunction_arrow :
    inv (CartesianMonoidalCategory.prodComparison mapping.functor source.operations.proposition source.operations.proposition) ≫
        mapping.functor.map source.operations.conjunction = (quantifiers mapping).predicates.conjunction := by
  change inv (CartesianMonoidalCategory.prodComparison mapping.functor source.operations.proposition source.operations.proposition) ≫
      mapping.functor.map source.operations.conjunction =
    lift (fst _ _ ≫ mapping.declarations.proposition.hom) (snd _ _ ≫ mapping.declarations.proposition.hom) ≫
      target.operations.predicates.conjunction ≫ mapping.declarations.proposition.inv
  apply (cancel_mono mapping.declarations.proposition.hom).mp
  simp only [Category.assoc, mapping.declarations.proposition.inv_hom_id]
  rw [mapping.declarations.conjunction, ← Category.assoc, comp_lift]
  simp only [← Category.assoc, CartesianMonoidalCategory.inv_prodComparison_map_fst,
    CartesianMonoidalCategory.inv_prodComparison_map_snd]
  exact (Category.comp_id _).symm

theorem truth_read : RawInterpretation.Reads (meanings mapping) (truthRaw source)
    (quantifiers mapping).predicates.truth :=
  ((meanings mapping).evaluate_compose _ _
    (BaseComparisons.CanonicalReadout.complete_arrow (meanings mapping)
      (realization mapping) .terminal)
    ((meanings mapping).evaluate_base_arrow source.operations.truth)).trans
      (congrArg (fun arrow => some (⟨𝟙_ target.closed.Obj,
        mapping.functor.obj source.operations.proposition, arrow⟩ :
          RelativeClosedSyntax.Interpretation.ArrowValue target.closed.Obj)) (truth_arrow mapping))

theorem conjunction_read : RawInterpretation.Reads (meanings mapping) (conjunctionRaw source)
    (quantifiers mapping).predicates.conjunction :=
  ((meanings mapping).evaluate_compose _ _
    (BaseComparisons.CanonicalReadout.complete_arrow (meanings mapping)
      (realization mapping) (.product source.operations.proposition source.operations.proposition))
    ((meanings mapping).evaluate_base_arrow source.operations.conjunction)).trans
      (congrArg (fun arrow => some (⟨mapping.functor.obj source.operations.proposition ⊗
        mapping.functor.obj source.operations.proposition, mapping.functor.obj source.operations.proposition,
          arrow⟩ : RelativeClosedSyntax.Interpretation.ArrowValue target.closed.Obj))
        (conjunction_arrow mapping))

def initial : Model (quantifiers mapping) (stage source) where
  meanings := meanings mapping
  admitted := realization mapping
  proposition := rfl
  truth := truth_read mapping
  conjunction := conjunction_read mapping

abbrev diagram := Closure.modelDiagram (initial mapping)

theorem complete_extension_readout {before after : Object (Closure.signature (stage source))}
    (arrow : RawHom before after) :
    (Closure.modelAssignment (initial mapping)).evaluateArrow arrow.code =
      some ⟨(diagram mapping).obj before, (diagram mapping).obj after,
        (diagram mapping).map (classOf arrow)⟩ :=
  Closure.model_complete_readout (initial mapping) arrow

end Mettapedia.CategoryTheory.RelativeClosedQuantified.Models
