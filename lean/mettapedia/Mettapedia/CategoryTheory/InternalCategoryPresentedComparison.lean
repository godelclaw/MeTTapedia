import Mettapedia.CategoryTheory.InternalCategoryPresentedDiagrams
import Mettapedia.CategoryTheory.InternalCategoryFunctorCategory

/-!
# Complete category comparisons from presented matching pairs

The supplied local source, target, unit and composition squares concern an
independently presented matching-pair object. Its actual universal property
earns the comparison on the chosen pullback. Thus the resulting internal
functor preserves the complete category operations and every supplied pair
of matching generalized edges.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryPresentedComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (source : InternalCategoryPresentedDiagrams.Endpoints C)
variable (target : InternalCategory C)
variable (vertices : source.vertex ⟶ target.vertex) (edges : source.edge ⟶ target.edge)
variable (sourceSquare : edges ≫ target.source = source.source ≫ vertices)
variable (targetSquare : edges ≫ target.target = source.target ≫ vertices)

def pairMap : source.pair.pt ⟶ target.toInternalGraph.Composable :=
  pullback.lift (source.pair.fst ≫ edges) (source.pair.snd ≫ edges) (by
    rw [Category.assoc, targetSquare, ← Category.assoc, source.pair.condition,
      Category.assoc, ← sourceSquare, ← Category.assoc])

theorem pairMap_first : pairMap source target vertices edges sourceSquare targetSquare ≫
    pullback.fst target.target target.source = source.pair.fst ≫ edges := pullback.lift_fst _ _ _

theorem pairMap_second : pairMap source target vertices edges sourceSquare targetSquare ≫
    pullback.snd target.target target.source = source.pair.snd ≫ edges := pullback.lift_snd _ _ _

variable (triples : InternalCategoryPresentedDiagrams.TripleCone source)
variable (tripleLimit : IsLimit triples)
variable (laws : InternalCategoryPresentedDiagrams.Laws source triples)

abbrev sourceCategory := InternalCategoryPresentedDiagrams.category source triples tripleLimit laws

def graphMap : InternalGraph.Hom
    (sourceCategory source triples tripleLimit laws).toInternalGraph target.toInternalGraph where
  vertex := vertices
  edge := edges
  source := sourceSquare
  target := targetSquare

theorem complete_chosen_pair :
    InternalCategoryPresentedDiagrams.pairLift source
        (pullback.fst source.target source.source) (pullback.snd source.target source.source)
          pullback.condition ≫ pairMap source target vertices edges sourceSquare targetSquare =
      (graphMap source target vertices edges sourceSquare targetSquare triples tripleLimit laws).composableMap := by
  apply pullback.hom_ext
  · rw [Category.assoc, pairMap_first, ← Category.assoc,
      PullbackCone.IsLimit.lift_fst, InternalGraph.Hom.composableMap_first]
    rfl
  · rw [Category.assoc, pairMap_second, ← Category.assoc,
      PullbackCone.IsLimit.lift_snd, InternalGraph.Hom.composableMap_second]
    rfl

variable (unitSquare : source.unit ≫ edges = vertices ≫ target.unit)
variable (compositionSquare : source.composition ≫ edges =
  pairMap source target vertices edges sourceSquare targetSquare ≫ target.composition)

def hom : InternalCategory.Hom (sourceCategory source triples tripleLimit laws) target where
  toHom := graphMap source target vertices edges sourceSquare targetSquare triples tripleLimit laws
  unit := unitSquare
  composition := by
    change (InternalCategoryPresentedDiagrams.pairLift source
      (pullback.fst source.target source.source) (pullback.snd source.target source.source)
        pullback.condition ≫ source.composition) ≫ edges = _
    rw [Category.assoc, compositionSquare, ← Category.assoc, complete_chosen_pair]

theorem complete_vertex :
    (hom source target vertices edges sourceSquare targetSquare triples tripleLimit laws unitSquare compositionSquare).vertex =
      vertices := rfl

theorem complete_edge :
    (hom source target vertices edges sourceSquare targetSquare triples tripleLimit laws unitSquare compositionSquare).edge =
      edges := rfl

theorem complete_unit :
    (sourceCategory source triples tripleLimit laws).unit ≫
      (hom source target vertices edges sourceSquare targetSquare triples tripleLimit laws unitSquare compositionSquare).edge =
      (hom source target vertices edges sourceSquare targetSquare triples tripleLimit laws unitSquare compositionSquare).vertex ≫
        target.unit :=
  (hom source target vertices edges sourceSquare targetSquare triples tripleLimit laws unitSquare compositionSquare).unit

theorem complete_composition :
    (sourceCategory source triples tripleLimit laws).composition ≫
      (hom source target vertices edges sourceSquare targetSquare triples tripleLimit laws unitSquare compositionSquare).edge =
      (hom source target vertices edges sourceSquare targetSquare triples tripleLimit laws unitSquare compositionSquare).toHom.composableMap ≫
        target.composition :=
  (hom source target vertices edges sourceSquare targetSquare triples tripleLimit laws unitSquare compositionSquare).composition

end Mettapedia.CategoryTheory.InternalCategoryPresentedComparison
