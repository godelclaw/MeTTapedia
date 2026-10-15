import Mettapedia.CategoryTheory.InternalConjunctiveOrderComparison
import Mettapedia.CategoryTheory.InternalPredicateLogicalUniqueness

/-!
# Implication preservation from finite-limit predicate maps

The product and ordered-consequent comparisons transport all three finite
implication diagrams. Their earned uniqueness identifies the transported
operation with an independently qualified target operation. Both supplied
inputs and arbitrary context substitution are retained. No exponential
preservation or implication-preservation field is required.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateImplicationMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open InternalConjunctiveObject InternalPredicateImplication
open InternalConjunctiveOrderComparison

universe u v k l
variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C]
variable {D : Type v} [Category.{l} D] [CartesianMonoidalCategory D]
variable {source : Operations C} {target : Operations D}
variable (mapping : Map source target) [PreservesFiniteLimits mapping.functor]

def operationImage (operation : source.proposition ⊗ source.proposition ⟶ source.proposition) :
    target.proposition ⊗ target.proposition ⟶ target.proposition :=
  (tupleComparison mapping).inv ≫ mapping.functor.map operation ≫ mapping.proposition.hom

theorem operationImage_square (operation : source.proposition ⊗ source.proposition ⟶ source.proposition) :
    (tupleComparison mapping).hom ≫ operationImage mapping operation = mapping.image operation := by
  simp only [operationImage, Iso.hom_inv_id_assoc, Map.image]

theorem operationImage_read (operation : source.proposition ⊗ source.proposition ⟶ source.proposition)
    {context : C} (first second : source.Fiber context) :
    applyOperation target (operationImage mapping operation) (mapping.image first) (mapping.image second) =
      mapping.image (applyOperation source operation first second) := by
  change lift (mapping.image first) (mapping.image second) ≫ operationImage mapping operation =
    mapping.functor.map (lift first second ≫ operation) ≫ mapping.proposition.hom
  rw [← tupleComparison_pair, Category.assoc, operationImage_square]
  simp only [Map.image, Functor.map_comp, Category.assoc]

variable [HasEqualizers C] [HasEqualizers D]

def scopeComparison : mapping.functor.obj (monotonicityScope source) ≅ monotonicityScope target :=
  CartesianMonoidalCategory.prodComparisonIso mapping.functor source.proposition (orderedPairs source) ≪≫
    tensorIso mapping.proposition (orderComparison mapping)

theorem scopeComparison_antecedent :
    (scopeComparison mapping).hom ≫ antecedent target = mapping.image (antecedent source) := by
  change ((CartesianMonoidalCategory.prodComparisonIso mapping.functor source.proposition (orderedPairs source)).hom ≫
      (tensorIso mapping.proposition (orderComparison mapping)).hom) ≫ fst _ _ =
    mapping.functor.map (fst _ _) ≫ mapping.proposition.hom
  rw [CartesianMonoidalCategory.prodComparisonIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_fst, ← Category.assoc, CartesianMonoidalCategory.prodComparison_fst]

theorem scopeComparison_smaller :
    (scopeComparison mapping).hom ≫ smallerConsequent target = mapping.image (smallerConsequent source) := by
  change ((CartesianMonoidalCategory.prodComparisonIso mapping.functor source.proposition (orderedPairs source)).hom ≫
      (tensorIso mapping.proposition (orderComparison mapping)).hom) ≫ (snd _ _ ≫ smaller target) =
    mapping.functor.map (snd _ _ ≫ smaller source) ≫ mapping.proposition.hom
  rw [CartesianMonoidalCategory.prodComparisonIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_snd_assoc, orderComparison_smaller]
  simp only [Map.image, ← Category.assoc, CartesianMonoidalCategory.prodComparison_snd,
    ← Functor.map_comp]

theorem scopeComparison_larger :
    (scopeComparison mapping).hom ≫ largerConsequent target = mapping.image (largerConsequent source) := by
  change ((CartesianMonoidalCategory.prodComparisonIso mapping.functor source.proposition (orderedPairs source)).hom ≫
      (tensorIso mapping.proposition (orderComparison mapping)).hom) ≫ (snd _ _ ≫ larger target) =
    mapping.functor.map (snd _ _ ≫ larger source) ≫ mapping.proposition.hom
  rw [CartesianMonoidalCategory.prodComparisonIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_snd_assoc, orderComparison_larger]
  simp only [Map.image, ← Category.assoc, CartesianMonoidalCategory.prodComparison_snd,
    ← Functor.map_comp]

def qualificationImage (qualified : Qualification source) : Qualification target where
  operation := operationImage mapping qualified.operation
  monotonicity := by
    apply (cancel_epi (scopeComparison mapping).hom).mp
    have smallerRead : (scopeComparison mapping).hom ≫
        applyOperation target (operationImage mapping qualified.operation)
          (antecedent target) (smallerConsequent target) =
        mapping.image (applyOperation source qualified.operation
          (antecedent source) (smallerConsequent source)) :=
      (apply_substitution target _ _ _ _).trans
        ((congrArg₂ (applyOperation target (operationImage mapping qualified.operation))
          (scopeComparison_antecedent mapping) (scopeComparison_smaller mapping)).trans
            (operationImage_read mapping _ _ _))
    have largerRead : (scopeComparison mapping).hom ≫
        applyOperation target (operationImage mapping qualified.operation)
          (antecedent target) (largerConsequent target) =
        mapping.image (applyOperation source qualified.operation
          (antecedent source) (largerConsequent source)) :=
      (apply_substitution target _ _ _ _).trans
        ((congrArg₂ (applyOperation target (operationImage mapping qualified.operation))
          (scopeComparison_antecedent mapping) (scopeComparison_larger mapping)).trans
            (operationImage_read mapping _ _ _))
    exact (target.reindex_meet (scopeComparison mapping).hom _ _).trans
      ((congrArg₂ target.meet largerRead smallerRead).trans
        ((mapping.image_meet _ _).symm.trans
          ((congrArg mapping.image qualified.monotonicity).trans smallerRead.symm)))
  unit := by
    apply (cancel_epi (tupleComparison mapping).hom).mp
    have conjunctionRead : (tupleComparison mapping).hom ≫ target.meet (fst _ _) (snd _ _) =
        mapping.image (source.meet (fst _ _) (snd _ _)) :=
      (target.reindex_meet (tupleComparison mapping).hom _ _).trans
        ((congrArg₂ target.meet (tupleComparison_first mapping) (tupleComparison_second mapping)).trans
          (mapping.image_meet _ _).symm)
    have implicationRead : (tupleComparison mapping).hom ≫
        applyOperation target (operationImage mapping qualified.operation)
          (fst _ _) (target.meet (fst _ _) (snd _ _)) =
        mapping.image (applyOperation source qualified.operation (fst _ _)
          (source.meet (fst _ _) (snd _ _))) :=
      (apply_substitution target _ _ _ _).trans
        ((congrArg₂ (applyOperation target (operationImage mapping qualified.operation))
          (tupleComparison_first mapping) conjunctionRead).trans (operationImage_read mapping _ _ _))
    exact (target.reindex_meet (tupleComparison mapping).hom _ _).trans
      ((congrArg₂ target.meet implicationRead (tupleComparison_second mapping)).trans
        ((mapping.image_meet _ _).symm.trans
          ((congrArg mapping.image qualified.unit).trans (tupleComparison_second mapping).symm)))
  counit := by
    apply (cancel_epi (tupleComparison mapping).hom).mp
    have implicationRead : (tupleComparison mapping).hom ≫
        applyOperation target (operationImage mapping qualified.operation) (fst _ _) (snd _ _) =
        mapping.image (applyOperation source qualified.operation (fst _ _) (snd _ _)) :=
      (apply_substitution target _ _ _ _).trans
        ((congrArg₂ (applyOperation target (operationImage mapping qualified.operation))
          (tupleComparison_first mapping) (tupleComparison_second mapping)).trans
            (operationImage_read mapping _ _ _))
    have conjunctionRead : (tupleComparison mapping).hom ≫ target.meet (fst _ _)
        (applyOperation target (operationImage mapping qualified.operation) (fst _ _) (snd _ _)) =
        mapping.image (source.meet (fst _ _)
          (applyOperation source qualified.operation (fst _ _) (snd _ _))) :=
      (target.reindex_meet (tupleComparison mapping).hom _ _).trans
        ((congrArg₂ target.meet (tupleComparison_first mapping) implicationRead).trans
          (mapping.image_meet _ _).symm)
    exact (target.reindex_meet (tupleComparison mapping).hom _ _).trans
      ((congrArg₂ target.meet (tupleComparison_second mapping) conjunctionRead).trans
        ((mapping.image_meet _ _).symm.trans
          ((congrArg mapping.image qualified.counit).trans conjunctionRead.symm)))

theorem implication_image (targetLaws : target.Laws)
    (sourceImplication : Qualification source) (targetImplication : Qualification target) :
    operationImage mapping sourceImplication.operation = targetImplication.operation :=
  InternalPredicateLogicalUniqueness.implication_operation_unique target targetLaws
    (qualificationImage mapping sourceImplication) targetImplication

theorem implication_square (targetLaws : target.Laws)
    (sourceImplication : Qualification source) (targetImplication : Qualification target) :
    mapping.functor.map sourceImplication.operation ≫ mapping.proposition.hom =
      (tupleComparison mapping).hom ≫ targetImplication.operation :=
  (operationImage_square mapping sourceImplication.operation).symm.trans
    (congrArg (fun arrow => (tupleComparison mapping).hom ≫ arrow)
      (implication_image mapping targetLaws sourceImplication targetImplication))

theorem implication_supplied (targetLaws : target.Laws)
    (sourceImplication : Qualification source) (targetImplication : Qualification target)
    {context : C} (first second : source.Fiber context) :
    mapping.image (sourceImplication.implies source first second) =
      targetImplication.implies target (mapping.image first) (mapping.image second) :=
  (operationImage_read mapping sourceImplication.operation first second).symm.trans
    (congrArg (fun arrow => applyOperation target arrow (mapping.image first) (mapping.image second))
      (implication_image mapping targetLaws sourceImplication targetImplication))

theorem implication_substitution (targetLaws : target.Laws)
    (sourceImplication : Qualification source) (targetImplication : Qualification target)
    {context before : C} (incoming : context ⟶ before) (first second : source.Fiber before) :
    mapping.image (incoming ≫ sourceImplication.implies source first second) =
      targetImplication.implies target
        (mapping.functor.map incoming ≫ mapping.image first)
        (mapping.functor.map incoming ≫ mapping.image second) :=
  (mapping.image_reindex incoming _).trans
    ((congrArg (fun arrow => mapping.functor.map incoming ≫ arrow)
      (implication_supplied mapping targetLaws sourceImplication targetImplication first second)).trans
        (targetImplication.implies_substitution target _ _ _))

end Mettapedia.CategoryTheory.InternalPredicateImplicationMaps
