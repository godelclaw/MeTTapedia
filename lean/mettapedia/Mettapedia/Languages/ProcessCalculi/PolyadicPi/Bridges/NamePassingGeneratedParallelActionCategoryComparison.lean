import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionComparison
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCategoryComparison
import Mettapedia.CategoryTheory.InternalCategoryClosedFunctorComparison

/-!
# The cumulative return-indexed category comparison in the action guest

The independently generated source category is first mapped by the complete
compiler. Its old category comparison is then transported through the actual
action-equation inclusion. The canonical exponential comparison identifies
this result with the return-indexed category of the extended target.

Both chosen matching projections and the whole unit and composition survive
this pasting. Matching edges can have any supplied stage; no reading of a
current endpoint is used to determine a complete function section.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionCategoryComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalClosed
open Mettapedia.CategoryTheory InternalCategoryFunctorCategory

universe k

abbrev Source := NamePassingGeneratedParallelActionComparison.Source.{k}
abbrev Target := NamePassingGeneratedParallelActionComparison.Target.{k}
abbrev compilerFunctor := NamePassingGeneratedParallelActionComparison.compiler.{k}.functor
abbrev oldCompilerFunctor := NamePassingGeneratedOperationalCategoryComparison.compilerFunctor.{k}
abbrev quotient := NamePassingGeneratedParallelActionComparison.quotient.{k}
abbrev sourceCategory := NamePassingGeneratedOperationalPresentation.category.{k}
abbrev originalCategory := BindingClosedGeneratedParallelAction.oldCategory.{k}
abbrev names := BindingClosedGeneratedParallelAction.oldOrdinary.{k}.names

instance compiler_finite : PreservesFiniteLimits compilerFunctor.{k} :=
  NamePassingGeneratedParallelActionComparison.compiler.preservesFiniteLimits

def mappedCategory : InternalCategory Target.{k} :=
  InternalCategoryFiniteLimitTransport.category compilerFunctor sourceCategory

def actualCategory : InternalCategory Target.{k} :=
  InternalCategoryFiniteLimitTransport.category (ihom (quotient.obj names))
    BindingClosedGeneratedParallelAction.category

def exponential : ihom names ⋙ quotient ≅ quotient ⋙ ihom (quotient.obj names) :=
  InternalCategoryClosedFunctorComparison.exponential quotient names

def comparison : mappedCategory.{k} ≅ actualCategory :=
  InternalCategoryFiniteLimitTransportComposition.component oldCompilerFunctor quotient sourceCategory ≪≫
    (InternalCategoryFiniteLimitTransportFunctor.action quotient).mapIso
      NamePassingGeneratedOperationalCategoryComparison.comparison ≪≫
        InternalCategoryClosedFunctorComparison.comparison quotient names originalCategory

theorem whole_vertex : comparison.{k}.hom.vertex =
    quotient.map NamePassingGeneratedOperationalCategoryComparison.comparison.hom.vertex ≫
      (expComparison quotient names).natTrans.app originalCategory.vertex := by
  change 𝟙 _ ≫ (quotient.map NamePassingGeneratedOperationalCategoryComparison.comparison.hom.vertex ≫
    (InternalCategoryClosedFunctorComparison.comparison quotient names originalCategory).hom.vertex) = _
  rw [Category.id_comp, InternalCategoryClosedFunctorComparison.whole_vertex]

theorem whole_edge : comparison.{k}.hom.edge =
    quotient.map NamePassingGeneratedOperationalCategoryComparison.comparison.hom.edge ≫
      (expComparison quotient names).natTrans.app originalCategory.edge := by
  change 𝟙 _ ≫ (quotient.map NamePassingGeneratedOperationalCategoryComparison.comparison.hom.edge ≫
    (InternalCategoryClosedFunctorComparison.comparison quotient names originalCategory).hom.edge) = _
  rw [Category.id_comp, InternalCategoryClosedFunctorComparison.whole_edge]

theorem whole_source : mappedCategory.{k}.source ≫ comparison.hom.vertex =
    comparison.hom.edge ≫ actualCategory.source := comparison.hom.source.symm

theorem whole_target : mappedCategory.{k}.target ≫ comparison.hom.vertex =
    comparison.hom.edge ≫ actualCategory.target := comparison.hom.target.symm

theorem whole_unit : mappedCategory.{k}.unit ≫ comparison.hom.edge =
    comparison.hom.vertex ≫ actualCategory.unit := comparison.hom.unit

theorem whole_composition : mappedCategory.{k}.composition ≫ comparison.hom.edge =
    comparison.hom.toHom.composableMap ≫ actualCategory.composition := comparison.hom.composition

theorem whole_pair_first : comparison.{k}.hom.toHom.composableMap ≫
    pullback.fst actualCategory.target actualCategory.source =
      pullback.fst mappedCategory.target mappedCategory.source ≫ comparison.hom.edge :=
  comparison.hom.toHom.composableMap_first

theorem whole_pair_second : comparison.{k}.hom.toHom.composableMap ≫
    pullback.snd actualCategory.target actualCategory.source =
      pullback.snd mappedCategory.target mappedCategory.source ≫ comparison.hom.edge :=
  comparison.hom.toHom.composableMap_second

theorem translated_matching {stage : Source.{k}}
    (before after : stage ⟶ sourceCategory.edge)
    (matching : before ≫ sourceCategory.target = after ≫ sourceCategory.source) :
    (compilerFunctor.map before ≫ comparison.hom.edge) ≫ actualCategory.target =
      (compilerFunctor.map after ≫ comparison.hom.edge) ≫ actualCategory.source := by
  rw [Category.assoc, comparison.hom.target, ← Category.assoc]
  change (compilerFunctor.map before ≫ compilerFunctor.map sourceCategory.target) ≫
    comparison.hom.vertex = _
  erw [← compilerFunctor.map_comp, matching, compilerFunctor.map_comp]
  erw [Category.assoc, ← comparison.hom.source, ← Category.assoc]

theorem whole_matching_readout {stage : Source.{k}}
    (before after : stage ⟶ sourceCategory.edge)
    (matching : before ≫ sourceCategory.target = after ≫ sourceCategory.source) :
    compilerFunctor.map (sourceCategory.compose before after matching) ≫ comparison.hom.edge =
      actualCategory.compose (compilerFunctor.map before ≫ comparison.hom.edge)
        (compilerFunctor.map after ≫ comparison.hom.edge) (translated_matching before after matching) := by
  have actual := comparison.hom.compose_readout (compilerFunctor.map before) (compilerFunctor.map after)
    (InternalCategoryFiniteLimitTransport.mapped_matching compilerFunctor sourceCategory before after matching)
  erw [InternalCategoryFiniteLimitTransport.category_compose_read] at actual
  exact actual

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionCategoryComparison
