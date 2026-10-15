import Mettapedia.CategoryTheory.InternalPredicateFunctionObjectMaps
import Mettapedia.CategoryTheory.InternalPredicateLogicalUniqueness
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Quantifier preservation derived from finite-limit closed maps

The ordered-pair scope is compared by its actual preserved equalizer and
the complete predicate-function comparison. This transports the finite
monotonicity diagram to every target ordered pair. Canonical precomposition
and the two unit/counit diagrams then construct both target quantifiers.
Their independently earned uniqueness determines the complete operation
arrows; quantifier preservation is a consequence, not an input field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateQuantifierMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject InternalPredicateFunctionObject InternalPredicateQuantifier
open InternalPredicateFunctionObjectMaps

universe u v k
variable {C : Type u} [Category.{k} C]
variable {D : Type v} [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D]
variable {source : Operations C} {target : Operations D}
variable (mapping : InternalConjunctiveObject.Map source target)
variable [PreservesFiniteLimits mapping.functor] [MonoidalClosedFunctor mapping.functor]

def tupleComparison (value : C) :
    mapping.functor.obj (power source value ⊗ power source value) ≅
      power target (mapping.functor.obj value) ⊗ power target (mapping.functor.obj value) :=
  asIso (CartesianMonoidalCategory.prodComparison mapping.functor _ _) ≪≫
    tensorIso (powerComparison mapping value) (powerComparison mapping value)

theorem tupleComparison_first (value : C) :
    (tupleComparison mapping value).hom ≫ fst _ _ =
      mapping.functor.map (fst (power source value) (power source value)) ≫
        (powerComparison mapping value).hom := by
  rw [tupleComparison, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_fst, ← Category.assoc, CartesianMonoidalCategory.prodComparison_fst]

theorem tupleComparison_second (value : C) :
    (tupleComparison mapping value).hom ≫ snd _ _ =
      mapping.functor.map (snd (power source value) (power source value)) ≫
        (powerComparison mapping value).hom := by
  rw [tupleComparison, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_snd, ← Category.assoc, CartesianMonoidalCategory.prodComparison_snd]

theorem tupleComparison_tuple (value : C) :
    (tupleComparison mapping value).hom = CartesianMonoidalCategory.lift
      (mapping.functor.map (fst (power source value) (power source value)) ≫
        (powerComparison mapping value).hom)
      (mapping.functor.map (snd (power source value) (power source value)) ≫
        (powerComparison mapping value).hom) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (tupleComparison_first mapping value).trans (CartesianMonoidalCategory.lift_fst _ _).symm
  · exact (tupleComparison_second mapping value).trans (CartesianMonoidalCategory.lift_snd _ _).symm

theorem tupleComparison_conjunction (value : C) :
    (tupleComparison mapping value).hom ≫ (functions target (mapping.functor.obj value)).conjunction =
      mapping.functor.map (functions source value).conjunction ≫ (powerComparison mapping value).hom := by
  rw [tupleComparison_tuple]
  exact (powerMap mapping value).conjunction.symm

variable [HasEqualizers C] [HasEqualizers D]

def mappedOrderFork (value : C) :
    Fork (functions target (mapping.functor.obj value)).conjunction
      (fst (power target (mapping.functor.obj value)) (power target (mapping.functor.obj value))) :=
  Fork.ofι (mapping.functor.map (orderInclusion source value) ≫ (tupleComparison mapping value).hom) (by
    rw [Category.assoc, tupleComparison_conjunction, Category.assoc, tupleComparison_first]
    simp only [← Category.assoc, ← Functor.map_comp]
    exact congrArg (fun arrow => mapping.functor.map arrow ≫ (powerComparison mapping value).hom)
      (equalizer.condition (functions source value).conjunction (fst _ _)))

def mappedOrderIsLimit (value : C) : IsLimit (mappedOrderFork mapping value) :=
  Fork.isLimitOfIsos _
    (isLimitOfHasEqualizerOfPreservesLimit mapping.functor
      (functions source value).conjunction (fst (power source value) (power source value)))
    (mappedOrderFork mapping value) (tupleComparison mapping value) (powerComparison mapping value)
    (Iso.refl _) (tupleComparison_conjunction mapping value) (tupleComparison_first mapping value)
    (Category.id_comp _)

def orderComparison (value : C) :
    mapping.functor.obj (orderedPairs source value) ≅ orderedPairs target (mapping.functor.obj value) :=
  IsLimit.conePointUniqueUpToIso (mappedOrderIsLimit mapping value)
    (limit.isLimit (parallelPair (functions target (mapping.functor.obj value)).conjunction (fst _ _)))

theorem orderComparison_inclusion (value : C) :
    (orderComparison mapping value).hom ≫ orderInclusion target (mapping.functor.obj value) =
      mapping.functor.map (orderInclusion source value) ≫ (tupleComparison mapping value).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (mappedOrderIsLimit mapping value)
    (limit.isLimit (parallelPair (functions target (mapping.functor.obj value)).conjunction (fst _ _)))
    WalkingParallelPair.zero

theorem orderComparison_first (value : C) :
    (orderComparison mapping value).hom ≫ firstInput target (mapping.functor.obj value) =
      sectionImage mapping (firstInput source value) := by
  change (orderComparison mapping value).hom ≫ (orderInclusion target _ ≫ fst _ _) =
    mapping.functor.map (orderInclusion source value ≫ fst _ _) ≫ (powerComparison mapping value).hom
  rw [← Category.assoc, orderComparison_inclusion, Category.assoc, tupleComparison_first,
    Functor.map_comp, Category.assoc]

theorem orderComparison_second (value : C) :
    (orderComparison mapping value).hom ≫ secondInput target (mapping.functor.obj value) =
      sectionImage mapping (secondInput source value) := by
  change (orderComparison mapping value).hom ≫ (orderInclusion target _ ≫ snd _ _) =
    mapping.functor.map (orderInclusion source value ≫ snd _ _) ≫ (powerComparison mapping value).hom
  rw [← Category.assoc, orderComparison_inclusion, Category.assoc, tupleComparison_second,
    Functor.map_comp, Category.assoc]

theorem orderComparison_first_operation {before after : C}
    (operation : power source before ⟶ power source after) :
    (orderComparison mapping before).hom ≫
        (firstInput target (mapping.functor.obj before) ≫ arrowImage mapping operation) =
      sectionImage mapping (firstInput source before ≫ operation) := by
  rw [← Category.assoc, orderComparison_first]
  exact (arrowImage_section mapping _ operation).symm

theorem orderComparison_second_operation {before after : C}
    (operation : power source before ⟶ power source after) :
    (orderComparison mapping before).hom ≫
        (secondInput target (mapping.functor.obj before) ≫ arrowImage mapping operation) =
      sectionImage mapping (secondInput source before ≫ operation) := by
  rw [← Category.assoc, orderComparison_second]
  exact (arrowImage_section mapping _ operation).symm

theorem monotonicityImage {before after : C} (operation : power source before ⟶ power source after)
    (admitted : Monotonicity source operation) : Monotonicity target (arrowImage mapping operation) where
  ordered := by
    apply (cancel_epi (orderComparison mapping before).hom).mp
    have complete := (sectionImage_meet mapping
      (secondInput source before ≫ operation) (firstInput source before ≫ operation)).symm.trans
      (congrArg (sectionImage mapping) admitted.ordered)
    calc
      _ = (functions target (mapping.functor.obj after)).meet
          ((orderComparison mapping before).hom ≫
            (secondInput target (mapping.functor.obj before) ≫ arrowImage mapping operation))
          ((orderComparison mapping before).hom ≫
            (firstInput target (mapping.functor.obj before) ≫ arrowImage mapping operation)) :=
        (functions target (mapping.functor.obj after)).reindex_meet _ _ _
      _ = (functions target (mapping.functor.obj after)).meet
          (sectionImage mapping (secondInput source before ≫ operation))
          (sectionImage mapping (firstInput source before ≫ operation)) := by
        rw [orderComparison_second_operation, orderComparison_first_operation]
      _ = sectionImage mapping (firstInput source before ≫ operation) := complete
      _ = _ := (orderComparison_first_operation mapping operation).symm

omit [HasEqualizers C] [HasEqualizers D] in
theorem precomposition_image {before after : C} (route : before ⟶ after) :
    sectionImage mapping (precomposition source route) =
      (powerComparison mapping after).hom ≫ precomposition target (mapping.functor.map route) := by
  apply read_injective target
  rw [sectionImage_read, precomposition_read]
  change inv (CartesianMonoidalCategory.prodComparison mapping.functor before (power source after)) ≫
      mapping.functor.map (uncurry (precomposition source route)) ≫ mapping.proposition.hom =
    (mapping.functor.map route ▷ mapping.functor.obj (power source after)) ≫
      uncurry (powerComparison mapping after).hom
  rw [precomposition, quote, uncurry_curry, powerComparison_read, Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun arrow => arrow ≫ mapping.functor.map ((ihom.ev after).app source.proposition) ≫
      mapping.proposition.hom)
    (prodComparison_inv_natural_whiskerRight mapping.functor (B := power source after) route)

omit [HasEqualizers C] [HasEqualizers D] in
theorem arrowImage_precomposition {before after : C} (route : before ⟶ after) :
    arrowImage mapping (precomposition source route) = precomposition target (mapping.functor.map route) := by
  apply (cancel_epi (powerComparison mapping after).hom).mp
  exact (arrowImage_after mapping _).trans (precomposition_image mapping route)

def universalImage {before after : C} (route : before ⟶ after) (quantifier : Universal source route) :
    Universal target (mapping.functor.map route) where
  operation := arrowImage mapping quantifier.operation
  monotonicity := monotonicityImage mapping quantifier.operation quantifier.monotonicity
  unit := by
    have complete := congrArg (arrowImage mapping) quantifier.unit
    rw [arrowImage_meet, arrowImage_comp, arrowImage_precomposition, arrowImage_identity] at complete
    exact complete
  counit := by
    have complete := congrArg (arrowImage mapping) quantifier.counit
    rw [arrowImage_meet, arrowImage_comp, arrowImage_precomposition, arrowImage_identity] at complete
    exact complete

def existentialImage {before after : C} (route : before ⟶ after)
    (quantifier : InternalPredicateExistential.Existential source route) :
    InternalPredicateExistential.Existential target (mapping.functor.map route) where
  operation := arrowImage mapping quantifier.operation
  monotonicity := monotonicityImage mapping quantifier.operation quantifier.monotonicity
  unit := by
    have complete := congrArg (arrowImage mapping) quantifier.unit
    rw [arrowImage_meet, arrowImage_comp, arrowImage_precomposition, arrowImage_identity] at complete
    exact complete
  counit := by
    have complete := congrArg (arrowImage mapping) quantifier.counit
    rw [arrowImage_meet, arrowImage_comp, arrowImage_precomposition, arrowImage_identity] at complete
    exact complete

theorem universal_image {before after : C} (route : before ⟶ after)
    (targetLaws : target.Laws) (sourceQuantifier : Universal source route)
    (targetQuantifier : Universal target (mapping.functor.map route)) :
    arrowImage mapping sourceQuantifier.operation = targetQuantifier.operation :=
  InternalPredicateLogicalUniqueness.universal_operation_unique target targetLaws
    (mapping.functor.map route) (universalImage mapping route sourceQuantifier) targetQuantifier

theorem existential_image {before after : C} (route : before ⟶ after)
    (targetLaws : target.Laws) (sourceQuantifier : InternalPredicateExistential.Existential source route)
    (targetQuantifier : InternalPredicateExistential.Existential target (mapping.functor.map route)) :
    arrowImage mapping sourceQuantifier.operation = targetQuantifier.operation :=
  InternalPredicateLogicalUniqueness.existential_operation_unique target targetLaws
    (mapping.functor.map route) (existentialImage mapping route sourceQuantifier) targetQuantifier

end Mettapedia.CategoryTheory.InternalPredicateQuantifierMaps
