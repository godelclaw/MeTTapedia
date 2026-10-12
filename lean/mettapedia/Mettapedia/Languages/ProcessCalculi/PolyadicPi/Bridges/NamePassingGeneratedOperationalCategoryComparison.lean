import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalInterpretation
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryModelComparison
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapFunctorComposition

/-!
# The whole generated compiler preserves the return-indexed category

The actual five-rule interpretation recovers the original category model on
restriction. Its complete unit and composition readings compare the mapped
source internal category with the name-indexed target category. Both chosen
matching-pullback projections, arbitrary generalized matching edges and the
inverse vertex and edge components are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCategoryComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation

universe k

abbrev Source := Object NamePassingGeneratedOperationalPresentation.signature.{k}
abbrev Target := BindingClosedGeneratedOperationalModel.Target.{k}
abbrev compiler := NamePassingGeneratedOperationalInterpretation.interpretation.{k}

def compilerFunctor : Source.{k} ⥤ Target := compiler.functor

instance compiler_finite : PreservesFiniteLimits compilerFunctor.{k} :=
  compiler.preservesFiniteLimits

def categoryExtension := RelativeClosedInternalCategory.RulePresentation.extendedCategoryMap
  NamePassingGeneratedOperationalPresentation.vertex.{k}
  NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration

theorem complete_category_restriction : categoryExtension.{k}.functor ⋙ compilerFunctor =
    NamePassingGeneratedOperationalCategory.categoryInterpretation := by
  simp only [categoryExtension, RelativeClosedInternalCategory.RulePresentation.extendedCategoryMap,
    SignatureMap.functor_compose, Functor.assoc]
  erw [NamePassingGeneratedOperationalInterpretation.complete_original_restriction,
    NamePassingGeneratedOperationalCategory.complete_category_restriction]

def mappedCategory : InternalCategory Target.{k} :=
  InternalCategoryFiniteLimitTransport.category compilerFunctor NamePassingGeneratedOperationalPresentation.category

def comparison : mappedCategory.{k} ≅ NamePassingGeneratedOperationalCategory.actualCategory :=
  @RelativeClosedInternalCategory.ModelComparison.comparison
    _ _ NamePassingGeneratedOperationalPresentation.vertex _ _ _ _ categoryExtension _ _ _ _ _
    NamePassingGeneratedOperationalCategory.base NamePassingGeneratedOperationalCategory.actualCategory
    NamePassingGeneratedOperationalCategory.programComparison compilerFunctor complete_category_restriction
    (compiler_finite.preservesFiniteLimits WalkingCospan)

theorem complete_unit : mappedCategory.{k}.unit ≫ comparison.hom.edge =
    comparison.hom.vertex ≫ NamePassingGeneratedOperationalCategory.actualCategory.unit := comparison.hom.unit

theorem complete_composition : mappedCategory.{k}.composition ≫ comparison.hom.edge =
    comparison.hom.toHom.composableMap ≫ NamePassingGeneratedOperationalCategory.actualCategory.composition :=
  comparison.hom.composition

theorem complete_pair_first : comparison.{k}.hom.toHom.composableMap ≫
    pullback.fst NamePassingGeneratedOperationalCategory.actualCategory.target
      NamePassingGeneratedOperationalCategory.actualCategory.source =
      pullback.fst mappedCategory.target mappedCategory.source ≫ comparison.hom.edge :=
  comparison.hom.toHom.composableMap_first

theorem complete_pair_second : comparison.{k}.hom.toHom.composableMap ≫
    pullback.snd NamePassingGeneratedOperationalCategory.actualCategory.target
      NamePassingGeneratedOperationalCategory.actualCategory.source =
      pullback.snd mappedCategory.target mappedCategory.source ≫ comparison.hom.edge :=
  comparison.hom.toHom.composableMap_second

theorem translated_matching {stage : Source.{k}}
    (before after : stage ⟶ NamePassingGeneratedOperationalPresentation.category.edge)
    (matching : before ≫ NamePassingGeneratedOperationalPresentation.category.target =
      after ≫ NamePassingGeneratedOperationalPresentation.category.source) :
    (compilerFunctor.map before ≫ comparison.hom.edge) ≫
      NamePassingGeneratedOperationalCategory.actualCategory.target =
        (compilerFunctor.map after ≫ comparison.hom.edge) ≫
          NamePassingGeneratedOperationalCategory.actualCategory.source := by
  rw [Category.assoc, comparison.hom.target, ← Category.assoc]
  change (compilerFunctor.map before ≫
    compilerFunctor.map NamePassingGeneratedOperationalPresentation.category.target) ≫
      comparison.hom.vertex = _
  erw [← compilerFunctor.map_comp, matching, compilerFunctor.map_comp]
  erw [Category.assoc, ← comparison.hom.source, ← Category.assoc]

theorem complete_matching_readout {stage : Source.{k}}
    (before after : stage ⟶ NamePassingGeneratedOperationalPresentation.category.edge)
    (matching : before ≫ NamePassingGeneratedOperationalPresentation.category.target =
      after ≫ NamePassingGeneratedOperationalPresentation.category.source) :
    compilerFunctor.map (NamePassingGeneratedOperationalPresentation.category.compose before after matching) ≫
      comparison.hom.edge = NamePassingGeneratedOperationalCategory.actualCategory.compose
        (compilerFunctor.map before ≫ comparison.hom.edge)
        (compilerFunctor.map after ≫ comparison.hom.edge)
        (translated_matching before after matching) := by
  have actual := comparison.hom.compose_readout
    (compilerFunctor.map before) (compilerFunctor.map after)
    (InternalCategoryFiniteLimitTransport.mapped_matching compilerFunctor
      NamePassingGeneratedOperationalPresentation.category before after matching)
  erw [InternalCategoryFiniteLimitTransport.category_compose_read] at actual
  exact actual

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCategoryComparison
