import Mettapedia.CategoryTheory.RelativeClosedGeneratedPredicateMaps
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSemanticModels
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationClosed

/-!
# Earning predicate maps from independently realized local meanings

Three successful readings specify the proposition object, truth and
conjunction. The generated interpretation supplies the terminal and product
readings and both projection readings. Their commuting squares earn a weak
closed conjunctive map on the complete equation quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k w
variable {C : Type k} [Category.{k} C] {names : Symbols.{k}}
variable {presentation : Signature (C := C) (symbols := names)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (language : PredicateSyntax presentation)
variable (truth : RawHom (terminal presentation) language.proposition)
variable (model : SemanticModels.Model presentation D)
variable (meaning : InternalConjunctiveObject.Operations D)

structure PredicateReadings where
  proposition : model.meanings.evaluateObject language.proposition.code = some meaning.proposition
  truth : model.meanings.evaluateArrow truth.code = some ⟨𝟙_ D, meaning.proposition, meaning.truth⟩
  conjunction : model.meanings.evaluateArrow language.conjunction.code =
    some ⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, meaning.conjunction⟩

variable {language truth model meaning}
variable (readings : PredicateReadings language truth model meaning)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem postcast {before after first second : D}
    (source : before = first) (target : after = second)
    {original : before ⟶ after} {value : first ⟶ second} (reading : HEq original value) :
    original ≫ eqToHom target = eqToHom source ≫ value := by
  subst first
  subst second
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using eq_of_heq reading

def PredicateReadings.propositionComparison :
    model.diagram.obj (operations language truth).proposition ≅ meaning.proposition :=
  eqToIso (RelativeClosedSyntax.Interpretation.objectValue_unique model.meanings model.realization
    language.proposition meaning.proposition readings.proposition)

theorem PredicateReadings.truth_square :
    model.diagram.map (operations language truth).truth ≫ readings.propositionComparison.hom =
      toUnit (model.diagram.obj (𝟙_ (Object presentation))) ≫ meaning.truth := by
  have terminalRead := RelativeClosedSyntax.Interpretation.functor_terminal_object
    model.meanings model.realization
  have truthRead := RelativeClosedSyntax.Interpretation.functor_map_heq
    model.meanings model.realization truth meaning.truth readings.truth
  exact (postcast terminalRead
    (RelativeClosedSyntax.Interpretation.objectValue_unique model.meanings model.realization
      language.proposition meaning.proposition readings.proposition) truthRead).trans
    (congrArg (fun arrow => arrow ≫ meaning.truth) (toUnit_unique _ _))

theorem PredicateReadings.conjunction_square :
    model.diagram.map (operations language truth).conjunction ≫ readings.propositionComparison.hom =
      lift (model.diagram.map (fst language.proposition language.proposition) ≫ readings.propositionComparison.hom)
        (model.diagram.map (snd language.proposition language.proposition) ≫ readings.propositionComparison.hom) ≫
          meaning.conjunction := by
  have propositionRead := RelativeClosedSyntax.Interpretation.objectValue_unique
    model.meanings model.realization language.proposition meaning.proposition readings.proposition
  have productRead := RelativeClosedSyntax.Interpretation.objectValue_unique
    model.meanings model.realization (product language.proposition language.proposition)
    (meaning.proposition ⊗ meaning.proposition)
    (model.meanings.evaluate_product readings.proposition readings.proposition)
  have operationRead := RelativeClosedSyntax.Interpretation.functor_map_heq
    model.meanings model.realization language.conjunction meaning.conjunction readings.conjunction
  have retained := postcast productRead propositionRead operationRead
  have firstRead := RelativeClosedSyntax.Interpretation.functor_map_heq
    model.meanings model.realization (RawHom.first language.proposition language.proposition)
    (fst meaning.proposition meaning.proposition)
    (model.meanings.evaluate_first readings.proposition readings.proposition)
  have secondRead := RelativeClosedSyntax.Interpretation.functor_map_heq
    model.meanings model.realization (RawHom.second language.proposition language.proposition)
    (snd meaning.proposition meaning.proposition)
    (model.meanings.evaluate_second readings.proposition readings.proposition)
  have first := postcast productRead propositionRead firstRead
  have second := postcast productRead propositionRead secondRead
  change model.diagram.map (fst language.proposition language.proposition) ≫
    readings.propositionComparison.hom = eqToHom productRead ≫ fst meaning.proposition meaning.proposition at first
  change model.diagram.map (snd language.proposition language.proposition) ≫
    readings.propositionComparison.hom = eqToHom productRead ≫ snd meaning.proposition meaning.proposition at second
  rw [first, second, ← comp_lift, lift_fst_snd, Category.comp_id]
  exact retained

def PredicateReadings.predicateMap : InternalConjunctiveObject.Map (operations language truth) meaning where
  functor := model.diagram
  proposition := readings.propositionComparison
  truth := readings.truth_square
  conjunction := readings.conjunction_square

instance PredicateReadings.predicateMap_finite : PreservesFiniteLimits readings.predicateMap.functor := by
  change PreservesFiniteLimits (RelativeClosedSyntax.Interpretation.functor model.meanings model.realization)
  infer_instance

instance PredicateReadings.predicateMap_closed : MonoidalClosedFunctor readings.predicateMap.functor := by
  change MonoidalClosedFunctor (RelativeClosedSyntax.Interpretation.functor model.meanings model.realization)
  infer_instance

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations
