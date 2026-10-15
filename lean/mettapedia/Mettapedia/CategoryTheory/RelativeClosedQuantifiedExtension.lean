import Mettapedia.CategoryTheory.RelativeClosedQuantifiedModels
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelPredicates

/-!
# Actual unit and weak-map quantifier extension

The unit retains the original proposition and its authored truth and
conjunction through actual terminal/product inverse declarations and the
closure inclusion. An independently supplied weak conjunctive map constructs
the quantified target model. Its earned local predicate interpretation and
the original proposition isomorphism give the complete extended weak map.
Restriction recovers the supplied full base functor, including every arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.Extension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory
open RelativeClosedGeneratedQuantifier Iteration

universe k
variable (source : ConjunctiveClosedTheory.{k})

def basePredicates : InternalConjunctiveObject.Map source.operations (initialOperations source) where
  functor := BaseComparisons.base (C := source.closed.Obj)
  proposition := Iso.refl _
  truth := by
    change (BaseComparisons.base (C := source.closed.Obj)).map source.operations.truth ≫ 𝟙 _ =
      (BaseComparisons.comparison (C := source.closed.Obj) .terminal).hom ≫
        ((BaseComparisons.comparison (C := source.closed.Obj) .terminal).inv ≫
          (BaseComparisons.base (C := source.closed.Obj)).map source.operations.truth)
    rw [Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  conjunction := by
    simp only [Iso.refl_hom, Category.comp_id]
    change (BaseComparisons.base (C := source.closed.Obj)).map source.operations.conjunction =
      CartesianMonoidalCategory.prodComparison (BaseComparisons.base (C := source.closed.Obj))
        source.operations.proposition source.operations.proposition ≫
      ((BaseComparisons.comparison (C := source.closed.Obj)
        (.product source.operations.proposition source.operations.proposition)).inv ≫
          (BaseComparisons.base (C := source.closed.Obj)).map source.operations.conjunction)
    rw [← BaseComparisons.product_comparison_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

def retainedPredicates : InternalConjunctiveObject.Map (initialOperations source)
    (freeObject source).operations.predicates where
  functor := (Closure.stageMap (stage source) 0).functor
  proposition := eqToIso (Closure.proposition_retained (stage source) 0)
  truth := by
    change (Closure.stageMap (stage source) 0).functor.map (initialOperations source).truth ≫ 𝟙 _ =
      toUnit (𝟙_ (Object (Closure.signature (stage source)))) ≫
        (freeObject source).operations.predicates.truth
    rw [Category.comp_id, toUnit_unit, Category.id_comp]
    rfl
  conjunction := by
    change (Closure.stageMap (stage source) 0).functor.map (initialOperations source).conjunction ≫ 𝟙 _ =
      lift (fst (freeObject source).operations.predicates.proposition
          (freeObject source).operations.predicates.proposition ≫ 𝟙 _)
        (snd (freeObject source).operations.predicates.proposition
          (freeObject source).operations.predicates.proposition ≫ 𝟙 _) ≫
        (freeObject source).operations.predicates.conjunction
    rw [Category.comp_id, Category.comp_id, Category.comp_id, lift_fst_snd, Category.id_comp]
    rfl

def unitMap : ConjunctiveClosedTheory.Map source (freeObject source).conjunctive where
  declarations := InternalConjunctiveObject.Map.comp (basePredicates source) (retainedPredicates source)
  finite := comp_preservesFiniteLimits (BaseComparisons.base (C := source.closed.Obj))
    (Closure.stageMap (stage source) 0).functor
  closed := CartesianClosedFunctorCoherence.closed_composition
    (BaseComparisons.base (C := source.closed.Obj)) (Closure.stageMap (stage source) 0).functor

theorem unit_functor_base : (unitMap source).functor =
    baseFunctor (Closure.signature (stage source)) :=
  ((Closure.stageMap (stage source) 0).functor_base).trans (Functor.id_comp _)

theorem unit_proposition_read :
    (unitMap source).functor.obj source.operations.proposition =
      (freeObject source).operations.predicates.proposition := rfl

theorem unit_proposition_hom : (unitMap source).declarations.proposition.hom =
    eqToHom (unit_proposition_read source) := by
  change (Closure.stageMap (stage source) 0).functor.map (𝟙 (proposition source)) ≫
    eqToHom (Closure.proposition_retained (stage source) 0) = eqToHom (unit_proposition_read source)
  exact (congrArg (fun arrow => arrow ≫ eqToHom (Closure.proposition_retained (stage source) 0))
    ((Closure.stageMap (stage source) 0).functor.map_id (stages (stage source) 0).language.proposition)).trans
      (Category.id_comp _)

variable {source} {target : QuantifiedClosedTheory.{k}}
variable (mapping : ConjunctiveClosedTheory.Map source target.conjunctive)

def extendMap : QuantifiedClosedTheory.Map (freeObject source) target where
  declarations := InternalConjunctiveObject.Map.comp
    (Closure.modelPredicateMap (Models.initial mapping))
    (InternalPredicateQuantifiedObject.Transport.forward target.operations mapping.declarations.proposition)
  finite := comp_preservesFiniteLimits (Models.diagram mapping) (𝟭 target.closed.Obj)
  closed := by
    let : MonoidalClosedFunctor (Models.diagram mapping) :=
      (Closure.modelQuantifiedMap (Models.initial mapping)).closed
    let : MonoidalClosedFunctor (𝟭 target.closed.Obj) :=
      InternalPredicateQuantifiedObject.Transport.forward_closed
        target.operations mapping.declarations.proposition
    exact CartesianClosedFunctorCoherence.closed_composition
      (Models.diagram mapping) (𝟭 target.closed.Obj)

def restrictMap (candidate : QuantifiedClosedTheory.Map (freeObject source) target) :
    ConjunctiveClosedTheory.Map source target.conjunctive :=
  ConjunctiveClosedTheory.Map.compose (unitMap source) candidate

theorem complete_base_recovered : (restrictMap (extendMap mapping)).functor = mapping.functor := by
  change (BaseComparisons.base (C := source.closed.Obj) ⋙ (Closure.stageMap (stage source) 0).functor) ⋙
    (Models.diagram mapping ⋙ 𝟭 target.closed.Obj) = mapping.functor
  rw [Functor.comp_id, Functor.assoc, Closure.model_whole_stage_restriction]
  exact RelativeClosedSyntax.Interpretation.functor_base (Models.meanings mapping) (Models.realization mapping)

end Mettapedia.CategoryTheory.RelativeClosedQuantified.Extension
