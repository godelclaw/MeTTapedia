import Mettapedia.CategoryTheory.InternalPredicatePositionedModalMaps

/-!+# Positioned-modal operators with an independent outgoing presentation

Contravariant predicate reindexing earns an actual isomorphism between the
complete postcondition function objects. The independent rely function is
retained. The conditional and quantified operator squares then follow from
the exponential adjunction and the two inverse equations of the outgoing
comparison; no whole-operator preservation assumption is supplied.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.PositionedModalOutgoingComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalPredicateFunctionObject InternalPredicatePositionedModalMaps

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C]
variable (predicates : InternalConjunctiveObject.Operations C)

theorem precomposition_eq_pre {before after : C} (route : before ⟶ after) :
    InternalPredicateQuantifier.precomposition predicates route =
      (MonoidalClosed.pre route).app predicates.proposition := by
  apply uncurry_injective
  change uncurry (curry ((route ▷ power predicates after) ≫
    (ihom.ev after).app predicates.proposition)) = _
  rw [uncurry_curry, MonoidalClosed.uncurry_pre]

theorem precomposition_identity (value : C) :
    InternalPredicateQuantifier.precomposition predicates (𝟙 value) =
      𝟙 (power predicates value) := by
  rw [precomposition_eq_pre, MonoidalClosed.pre_id]
  rfl

theorem precomposition_composition {first second third : C}
    (before : first ⟶ second) (after : second ⟶ third) :
    InternalPredicateQuantifier.precomposition predicates (before ≫ after) =
      InternalPredicateQuantifier.precomposition predicates after ≫
        InternalPredicateQuantifier.precomposition predicates before := by
  simp only [precomposition_eq_pre, MonoidalClosed.pre_map, NatTrans.comp_app]

def powerReindexIso {before after : C} (comparison : before ≅ after) :
    power predicates before ≅ power predicates after where
  hom := InternalPredicateQuantifier.precomposition predicates comparison.inv
  inv := InternalPredicateQuantifier.precomposition predicates comparison.hom
  hom_inv_id := by
    rw [← precomposition_composition, comparison.hom_inv_id, precomposition_identity]
  inv_hom_id := by
    rw [← precomposition_composition, comparison.inv_hom_id, precomposition_identity]

variable {predicates}
variable [HasEqualizers C]
variable (implication : InternalPredicateImplication.Qualification predicates)

theorem condition_comparison {instances assay before after parameter : C}
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ before)
    (comparison : before ≅ after)
    (relies : parameter ⟶ power predicates assay) (post : parameter ⟶ power predicates before) :
    condition predicates implication instantiate (reduct ≫ comparison.hom) relies
        (post ≫ (powerReindexIso predicates comparison).hom) =
      condition predicates implication instantiate reduct relies post := by
  unfold condition
  change curry (implication.implies predicates _
    (read predicates ((post ≫ InternalPredicateQuantifier.precomposition predicates comparison.inv) ≫
      InternalPredicateQuantifier.precomposition predicates (reduct ≫ comparison.hom)))) = _
  rw [Category.assoc, ← precomposition_composition, Category.assoc, comparison.hom_inv_id,
    Category.comp_id]

def profilesReindexIso {assay before after : C} (comparison : before ≅ after) :
    profiles predicates assay before ≅ profiles predicates assay after :=
  tensorIso (Iso.refl (power predicates assay)) (powerReindexIso predicates comparison)

theorem conditionOperator_comparison {instances assay before after : C}
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ before)
    (comparison : before ≅ after) :
    (profilesReindexIso (predicates := predicates) (assay := assay) comparison).hom ≫
        conditionOperator predicates implication instantiate (reduct ≫ comparison.hom) =
      conditionOperator predicates implication instantiate reduct := by
  change _ ≫ condition predicates implication instantiate (reduct ≫ comparison.hom) (fst _ _) (snd _ _) = _
  rw [← condition_substitution]
  have firstReading :
      (profilesReindexIso (predicates := predicates) (assay := assay) comparison).hom ≫ fst _ _ =
        (fst (power predicates assay) (power predicates before)) := by
    change tensorHom (𝟙 _) (powerReindexIso predicates comparison).hom ≫ fst _ _ = _
    rw [tensorHom_fst, Category.comp_id]
  have secondReading :
      (profilesReindexIso (predicates := predicates) (assay := assay) comparison).hom ≫ snd _ _ =
        snd (power predicates assay) (power predicates before) ≫
          (powerReindexIso predicates comparison).hom := by
    exact tensorHom_snd _ _
  rw [firstReading, secondReading]
  exact condition_comparison implication instantiate reduct comparison _ _

theorem modalityOperator_comparison
    (quantified : InternalPredicateQuantifiedObject.Operations C)
    (qualified : InternalPredicateImplication.Qualification quantified.predicates)
    {instances assignments assay carrier before after : C}
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ before)
    (comparison : before ≅ after) :
    (profilesReindexIso (predicates := quantified.predicates) (assay := assay) comparison).hom ≫
        modalityOperator quantified qualified forget focus instantiate (reduct ≫ comparison.hom) =
      modalityOperator quantified qualified forget focus instantiate reduct := by
  unfold modalityOperator
  rw [← Category.assoc, ← Category.assoc, conditionOperator_comparison]

end Mettapedia.CategoryTheory.PositionedModalOutgoingComparison
