import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedParallelAction
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedNativeLanguage

/-!
# The whole compiler into the parallel-action equation guest

Postcomposition with the actual finite-limit and closed equation inclusion
retains every independently admitted source firing and both endpoint arrows.
The comparisons include the complete premise and result objects; they do
not equate supplied firing origins or execution histories.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionComparison

open _root_.CategoryTheory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation

universe k

abbrev Source := NamePassingGeneratedNativeLanguage.Source.{k}
abbrev Original := NamePassingGeneratedNativeLanguage.Target.{k}
abbrev Target := BindingClosedGeneratedParallelAction.Guest.{k}
abbrev quotient := BindingClosedGeneratedParallelAction.inclusion.{k}.functor
abbrev oldCompiler := NamePassingGeneratedOperationalInterpretation.interpretation.{k}

def compiler := Mettapedia.GSLT.Core.LambdaTheoryMap.comp
  BindingClosedGeneratedParallelAction.theoryMap oldCompiler.{k}

abbrev Origin := NamePassingGeneratedNativeLanguage.Origin.{k}
abbrev sourceDomain := NamePassingGeneratedNativeLanguage.domain.{k}
abbrev sourceFiring := NamePassingGeneratedNativeLanguage.ruleArrow.{k}

def firing (origin : Origin.{k}) := quotient.map (NamePassingGeneratedOperationalInterpretation.firing origin)

def premiseComparison (origin : Origin.{k}) :=
  quotient.mapIso (NamePassingGeneratedNativeLanguage.premiseComparison origin)

def resultComparison (origin : Origin.{k}) :=
  quotient.mapIso (NamePassingGeneratedNativeLanguage.resultComparison origin)

theorem complete_firing_square (origin : Origin.{k}) :
    compiler.functor.map (sourceFiring origin) ≫ (resultComparison origin).hom =
      (premiseComparison origin).hom ≫ firing origin := by
  have whole := congrArg quotient.map (NamePassingGeneratedNativeLanguage.independent_firing_square origin)
  simp only [quotient.map_comp] at whole
  exact whole

theorem whole_independent_firing (origin : Origin.{k}) :
    (⟨compiler.functor.obj (sourceDomain origin),
      compiler.functor.obj NamePassingGeneratedOperationalPresentation.category.edge,
      compiler.functor.map (sourceFiring origin)⟩ : ArrowValue Target) =
    ⟨quotient.obj (RelativeClosedInternalCategory.RuleInterpretation.premise
        NamePassingGeneratedOperationalPresentation.vertex NamePassingGeneratedOperationalPresentation.categoryMap
        NamePassingGeneratedOperationalPresentation.declaration
        NamePassingGeneratedOperationalInterpretation.meanings
        NamePassingGeneratedOperationalInterpretation.realized origin),
      quotient.obj (RelativeClosedInternalCategory.RuleInterpretation.edges
        NamePassingGeneratedOperationalPresentation.vertex NamePassingGeneratedOperationalPresentation.categoryMap
        NamePassingGeneratedOperationalInterpretation.meanings
        NamePassingGeneratedOperationalInterpretation.realized), firing origin⟩ := by
  exact congrArg (fun value : ArrowValue Original =>
    (⟨quotient.obj value.source, quotient.obj value.target, quotient.map value.arrow⟩ : ArrowValue Target))
      (NamePassingGeneratedOperationalInterpretation.whole_firing_readout origin)

theorem complete_endpoint (origin : Origin.{k}) (side : Bool) :
    compiler.functor.map (sourceFiring origin) ≫
      compiler.functor.map (NamePassingGeneratedNativeLanguage.sourcePort side) =
    compiler.functor.map (NamePassingGeneratedNativeLanguage.declaredEndpoint origin side) := by
  rw [← compiler.functor.map_comp, NamePassingGeneratedNativeLanguage.declared_endpoint]

def originalInclusion :=
  (RelativeClosedInternalCategory.RulePresentation.arrowInclusion
    NamePassingGeneratedOperationalPresentation.vertex.{k}
    NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration).functor ⋙
  (RelativeClosedInternalCategory.RulePresentation.equationInclusion
    NamePassingGeneratedOperationalPresentation.vertex
    NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration).functor

theorem complete_original_restriction : originalInclusion.{k} ⋙ compiler.functor =
    NamePassingGeneratedConstructorComparison.compiler ⋙ quotient := by
  change originalInclusion ⋙ (oldCompiler.functor ⋙ quotient) = _
  rw [← Functor.assoc]
  exact congrArg (· ⋙ quotient) NamePassingGeneratedOperationalInterpretation.complete_original_restriction

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionComparison
