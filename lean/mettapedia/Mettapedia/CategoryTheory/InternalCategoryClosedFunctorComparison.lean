import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportComposition
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Closed functors compare complete return-indexed internal categories

The canonical exponential comparison is a natural isomorphism between the
two actual base functor composites. Transporting this isomorphism and both
chosen composition comparisons gives an isomorphism of internal categories.
Its vertex and edge arrows are the canonical exponential comparisons; its
matching-pair, unit and composition squares retain the complete edges.

Object sizes are independent. The hom size is shared, as required by the
underlying canonical closed-functor comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryClosedFunctorComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory MonoidalClosed
open InternalCategoryFunctorCategory InternalCategoryFiniteLimitTransport

universe u v w

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasPullbacks C]
variable {D : Type w} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [MonoidalClosedFunctor F]
variable (argument : C) (original : InternalCategory C)

def exponential : ihom argument ⋙ F ≅ F ⋙ ihom (F.obj argument) :=
  asIso ((expComparison F argument).natTrans)

def comparison : category F (category (ihom argument) original) ≅
    category (ihom (F.obj argument)) (category F original) :=
  (InternalCategoryFiniteLimitTransportComposition.component (ihom argument) F original).symm ≪≫
    (InternalCategoryFiniteLimitTransportCells.comparison (exponential F argument)).app original ≪≫
      InternalCategoryFiniteLimitTransportComposition.component F (ihom (F.obj argument)) original

theorem whole_vertex : (comparison F argument original).hom.vertex =
    (expComparison F argument).natTrans.app original.vertex := by
  change 𝟙 _ ≫ ((exponential F argument).hom.app original.vertex ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id, exponential, asIso_hom]

theorem whole_edge : (comparison F argument original).hom.edge =
    (expComparison F argument).natTrans.app original.edge := by
  change 𝟙 _ ≫ ((exponential F argument).hom.app original.edge ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id, exponential, asIso_hom]

theorem whole_evaluation : F.obj argument ◁ (comparison F argument original).hom.edge ≫
    (ihom.ev (F.obj argument)).app (F.obj original.edge) =
      inv (CartesianMonoidalCategory.prodComparison F argument ((ihom argument).obj original.edge)) ≫
        F.map ((ihom.ev argument).app original.edge) := by
  rw [whole_edge]
  exact expComparison_ev F argument original.edge

theorem whole_abstraction {stage : C} (body : argument ⊗ stage ⟶ original.edge) :
    MonoidalClosed.uncurry
      (F.map (MonoidalClosed.curry body) ≫ (comparison F argument original).hom.edge) =
      inv (CartesianMonoidalCategory.prodComparison F argument stage) ≫ F.map body := by
  rw [whole_edge, MonoidalClosed.uncurry_natural_left, uncurry_expComparison,
    ← Category.assoc, ← CartesianMonoidalCategory.prodComparison_inv_natural_whiskerLeft,
    Category.assoc, ← F.map_comp]
  change _ ≫ F.map (MonoidalClosed.uncurry (MonoidalClosed.curry body)) = _
  rw [MonoidalClosed.uncurry_curry]

theorem whole_pair_first : (comparison F argument original).hom.toHom.composableMap ≫
    pullback.fst (category (ihom (F.obj argument)) (category F original)).target
      (category (ihom (F.obj argument)) (category F original)).source =
        pullback.fst (category F (category (ihom argument) original)).target
          (category F (category (ihom argument) original)).source ≫
            (expComparison F argument).natTrans.app original.edge := by
  rw [← whole_edge]
  exact (comparison F argument original).hom.toHom.composableMap_first

theorem whole_pair_second : (comparison F argument original).hom.toHom.composableMap ≫
    pullback.snd (category (ihom (F.obj argument)) (category F original)).target
      (category (ihom (F.obj argument)) (category F original)).source =
        pullback.snd (category F (category (ihom argument) original)).target
          (category F (category (ihom argument) original)).source ≫
            (expComparison F argument).natTrans.app original.edge := by
  rw [← whole_edge]
  exact (comparison F argument original).hom.toHom.composableMap_second

theorem whole_unit : (category F (category (ihom argument) original)).unit ≫
    (expComparison F argument).natTrans.app original.edge =
      (expComparison F argument).natTrans.app original.vertex ≫
        (category (ihom (F.obj argument)) (category F original)).unit := by
  rw [← whole_edge, ← whole_vertex]
  exact (comparison F argument original).hom.unit

theorem whole_composition : (category F (category (ihom argument) original)).composition ≫
    (expComparison F argument).natTrans.app original.edge =
      (comparison F argument original).hom.toHom.composableMap ≫
        (category (ihom (F.obj argument)) (category F original)).composition := by
  rw [← whole_edge]
  exact (comparison F argument original).hom.composition

theorem whole_matching {stage : D}
    (before after : stage ⟶ (category F (category (ihom argument) original)).edge)
    (matching : before ≫ (category F (category (ihom argument) original)).target =
      after ≫ (category F (category (ihom argument) original)).source) :
    (before ≫ (comparison F argument original).hom.edge) ≫
      (category (ihom (F.obj argument)) (category F original)).target =
        (after ≫ (comparison F argument original).hom.edge) ≫
          (category (ihom (F.obj argument)) (category F original)).source := by
  rw [Category.assoc, (comparison F argument original).hom.target, ← Category.assoc,
    matching, Category.assoc, ← (comparison F argument original).hom.source, ← Category.assoc]

theorem whole_matching_readout {stage : D}
    (before after : stage ⟶ (category F (category (ihom argument) original)).edge)
    (matching : before ≫ (category F (category (ihom argument) original)).target =
      after ≫ (category F (category (ihom argument) original)).source) :
    (category F (category (ihom argument) original)).compose before after matching ≫
      (comparison F argument original).hom.edge =
        (category (ihom (F.obj argument)) (category F original)).compose
          (before ≫ (comparison F argument original).hom.edge)
          (after ≫ (comparison F argument original).hom.edge)
          (whole_matching F argument original before after matching) :=
  (comparison F argument original).hom.compose_readout before after matching

end Mettapedia.CategoryTheory.InternalCategoryClosedFunctorComparison
