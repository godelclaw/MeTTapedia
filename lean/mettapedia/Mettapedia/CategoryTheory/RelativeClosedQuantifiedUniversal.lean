import Mettapedia.CategoryTheory.RelativeClosedQuantifiedExtension
import Mettapedia.CategoryTheory.RelativeClosedBaseRealizationUniqueness

/-!
# Complete weak-map comparison of quantified completion

The candidate is an independently supplied weak finite-limit closed map.
A compatible comparison on its restricted conjunctive theory determines
the original base presentations. Reconstruction supplies the local target
realization, and uniqueness of the authored base inverse declarations
recovers every initial arrow. The quantifier closure universal comparison
then determines the whole functor, with the original raw objects retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.Universal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory
open RelativeClosedGeneratedQuantifier Iteration

universe k
variable {source : ConjunctiveClosedTheory.{k}} {target : QuantifiedClosedTheory.{k}}
variable (mapping : ConjunctiveClosedTheory.Map source target.conjunctive)
variable (candidate : ConjunctiveClosedTheory.Map (freeObject source).conjunctive target.conjunctive)
variable (baseComparison : ConjunctiveClosedTheory.MapIso (Extension.restrictMap candidate) mapping)

local instance candidate_finite : PreservesFiniteLimits candidate.functor := candidate.finite
local instance candidate_closed : MonoidalClosedFunctor candidate.functor := candidate.closed

def primitiveImages : AtomicPresentation.PrimitiveImages candidate.functor
    (Closure.modelAssignment (Models.initial mapping)) where
  base := eqToIso
    (congrArg (fun functor => functor ⋙ candidate.functor)
      (Extension.unit_functor_base source)).symm ≪≫ baseComparison.comparison
  object origin := origin.down.elim

theorem primitive_base_component (object : source.closed.Obj) :
    (primitiveImages mapping candidate baseComparison).base.hom.app object =
      baseComparison.comparison.hom.app object := by
  change 𝟙 _ ≫ baseComparison.comparison.hom.app object = baseComparison.comparison.hom.app object
  exact Category.id_comp _

abbrev reconstructed : RelativeClosedSyntax.Interpretation.Assignment source.closed.Obj
    (Closure.symbols (stage source)) target.closed.Obj := by
  letI : PreservesFiniteLimits candidate.functor := candidate.finite
  letI : MonoidalClosedFunctor candidate.functor := candidate.closed
  exact UniversalReadout.extracted (Models.initial mapping)
    candidate.functor (primitiveImages mapping candidate baseComparison)

abbrev initialAssignment := (Closure.stageMap (stage source) 0).precompose
  (reconstructed mapping candidate baseComparison)

theorem initial_realization : RelativeClosedSyntax.Interpretation.Realization
    (initialSignature source) (initialAssignment mapping candidate baseComparison) := by
  let : PreservesFiniteLimits candidate.functor := candidate.finite
  let : MonoidalClosedFunctor candidate.functor := candidate.closed
  exact (Closure.stageMap (stage source) 0).realization_precompose
    (reconstructed mapping candidate baseComparison)
    (FunctorNormalization.reconstruction_realization
      (UniversalReadout.selected (Models.initial mapping) candidate.functor
        (primitiveImages mapping candidate baseComparison)) (Closure.headers (stage source)))

theorem initial_base_read : (initialAssignment mapping candidate baseComparison).base =
    (Models.meanings mapping).base := by
  let : PreservesFiniteLimits candidate.functor := candidate.finite
  let : MonoidalClosedFunctor candidate.functor := candidate.closed
  change 𝟭 source.closed.Obj ⋙
    (baseFunctor (Closure.signature (stage source)) ⋙
      UniversalReadout.selected (Models.initial mapping) candidate.functor
        (primitiveImages mapping candidate baseComparison)) = mapping.functor
  rw [Functor.id_comp]
  exact AtomicPresentation.functor_base candidate.functor
    (Closure.modelAssignment (Models.initial mapping)) (primitiveImages mapping candidate baseComparison)

theorem initial_arrows_recovered :
    let : PreservesFiniteLimits candidate.functor := candidate.finite
    let : MonoidalClosedFunctor candidate.functor := candidate.closed
    UniversalReadout.InitialArrowImages (Models.initial mapping) candidate.functor
      (primitiveImages mapping candidate baseComparison) := by
  let : PreservesFiniteLimits candidate.functor := candidate.finite
  let : MonoidalClosedFunctor candidate.functor := candidate.closed
  constructor
  intro origin
  exact BaseComparisons.RealizationUniqueness.arrow_equal
    (initialAssignment mapping candidate baseComparison)
    (initial_realization mapping candidate baseComparison) (Models.meanings mapping)
    (Models.realization mapping) (initial_base_read mapping candidate baseComparison) origin

def comparison : candidate.functor ≅ Models.diagram mapping := by
  let : PreservesFiniteLimits candidate.functor := candidate.finite
  let : MonoidalClosedFunctor candidate.functor := candidate.closed
  exact UniversalReadout.comparison (Models.initial mapping) candidate.functor
    (primitiveImages mapping candidate baseComparison)
    (initial_arrows_recovered mapping candidate baseComparison)

theorem base_component (object : source.closed.Obj) :
    (comparison mapping candidate baseComparison).hom.app
      (baseObject (Closure.signature (stage source)) object) =
        (primitiveImages mapping candidate baseComparison).base.hom.app object ≫
          eqToHom (RelativeClosedSyntax.Interpretation.functor_base_object
            (Closure.modelAssignment (Models.initial mapping))
            (Closure.modelRealization (Models.initial mapping)) object).symm := by
  let : PreservesFiniteLimits candidate.functor := candidate.finite
  let : MonoidalClosedFunctor candidate.functor := candidate.closed
  exact UniversalReadout.base_component (Models.initial mapping) candidate.functor
    (primitiveImages mapping candidate baseComparison)
    (initial_arrows_recovered mapping candidate baseComparison) object

theorem complete_arrow_square {before after : (freeObject source).closed.Obj}
    (arrow : before ⟶ after) :
    candidate.functor.map arrow ≫ (comparison mapping candidate baseComparison).hom.app after =
      (comparison mapping candidate baseComparison).hom.app before ≫ (Models.diagram mapping).map arrow :=
  (comparison mapping candidate baseComparison).hom.naturality arrow

def completeComparison : QuantifiedClosedTheory.MapIso candidate (Extension.extendMap mapping) where
  comparison := comparison mapping candidate baseComparison ≪≫ (Functor.rightUnitor (Models.diagram mapping)).symm
  proposition := by
    change ((comparison mapping candidate baseComparison).hom.app
        (Closure.operations (stage source)).proposition ≫ 𝟙 _) ≫
      ((𝟭 target.closed.Obj).map (eqToHom (Closure.model_proposition_read (Models.initial mapping))) ≫
        mapping.declarations.proposition.hom) = candidate.declarations.proposition.hom
    rw [Category.comp_id]
    simp only [_root_.CategoryTheory.Functor.id_map]
    change (comparison mapping candidate baseComparison).hom.app
      (baseObject (Closure.signature (stage source)) source.operations.proposition) ≫
        (eqToHom (Closure.model_proposition_read (Models.initial mapping)) ≫
          mapping.declarations.proposition.hom) = candidate.declarations.proposition.hom
    rw [base_component, primitive_base_component]
    simp only [Category.assoc, eqToHom_refl, Category.id_comp]
    have localSquare := baseComparison.proposition
    change baseComparison.comparison.hom.app source.operations.proposition ≫
      mapping.declarations.proposition.hom =
        candidate.functor.map (Extension.unitMap source).declarations.proposition.hom ≫
          candidate.declarations.proposition.hom at localSquare
    rw [Extension.unit_proposition_hom] at localSquare
    change baseComparison.comparison.hom.app source.operations.proposition ≫
      mapping.declarations.proposition.hom =
        candidate.functor.map (𝟙 (freeObject source).operations.predicates.proposition) ≫
          candidate.declarations.proposition.hom at localSquare
    simpa only [candidate.functor.map_id, Category.id_comp] using localSquare

end Mettapedia.CategoryTheory.RelativeClosedQuantified.Universal
