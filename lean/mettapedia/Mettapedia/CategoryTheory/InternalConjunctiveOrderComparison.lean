import Mettapedia.CategoryTheory.InternalConjunctiveObjectMaps
import Mettapedia.CategoryTheory.InternalPredicateImplication
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Canonical comparison of ordered predicate pairs

A finite-limit functor and its proposition-object isomorphism compare the
actual product and ordered-pair equalizer. Both predicate readings commute
with the comparison. The comparisons respect identity and composition,
including the complete equalizer inclusion.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalConjunctiveOrderComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open InternalConjunctiveObject InternalPredicateImplication

universe u v w k l m
variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C]
variable {D : Type v} [Category.{l} D] [CartesianMonoidalCategory D]
variable {E : Type w} [Category.{m} E] [CartesianMonoidalCategory E]
variable {source : Operations C} {target : Operations D} {last : Operations E}
variable (mapping : InternalConjunctiveObject.Map source target)
variable [PreservesFiniteLimits mapping.functor]

instance identity_finite : PreservesFiniteLimits (Map.identity source).functor := by
  change PreservesFiniteLimits (𝟭 C)
  infer_instance

instance comp_finite (before : Map source target) (after : Map target last)
    [PreservesFiniteLimits before.functor] [PreservesFiniteLimits after.functor] :
    PreservesFiniteLimits (Map.comp before after).functor :=
  comp_preservesFiniteLimits before.functor after.functor

def tupleComparison :
    mapping.functor.obj (source.proposition ⊗ source.proposition) ≅
      target.proposition ⊗ target.proposition :=
  asIso (CartesianMonoidalCategory.prodComparison mapping.functor _ _) ≪≫
    tensorIso mapping.proposition mapping.proposition

theorem tupleComparison_first :
    (tupleComparison mapping).hom ≫ fst _ _ =
      mapping.image (fst source.proposition source.proposition) := by
  rw [tupleComparison, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_fst, ← Category.assoc, CartesianMonoidalCategory.prodComparison_fst]
  rfl

theorem tupleComparison_second :
    (tupleComparison mapping).hom ≫ snd _ _ =
      mapping.image (snd source.proposition source.proposition) := by
  rw [tupleComparison, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_snd, ← Category.assoc, CartesianMonoidalCategory.prodComparison_snd]
  rfl

theorem tupleComparison_tuple :
    (tupleComparison mapping).hom = lift
      (mapping.image (fst source.proposition source.proposition))
      (mapping.image (snd source.proposition source.proposition)) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact tupleComparison_first mapping |>.trans (lift_fst _ _).symm
  · exact tupleComparison_second mapping |>.trans (lift_snd _ _).symm

theorem tupleComparison_conjunction :
    (tupleComparison mapping).hom ≫ target.conjunction = mapping.image source.conjunction := by
  rw [tupleComparison_tuple]
  exact mapping.conjunction.symm

theorem tupleComparison_pair {context : C} (first second : source.Fiber context) :
    mapping.functor.map (lift first second) ≫ (tupleComparison mapping).hom =
      lift (mapping.image first) (mapping.image second) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tupleComparison_first]
    exact (mapping.image_reindex (lift first second) (fst _ _)).symm.trans
      (congrArg mapping.image (lift_fst first second)) |>.trans (lift_fst _ _).symm
  · rw [Category.assoc, tupleComparison_second]
    exact (mapping.image_reindex (lift first second) (snd _ _)).symm.trans
      (congrArg mapping.image (lift_snd first second)) |>.trans (lift_snd _ _).symm

variable [HasEqualizers C] [HasEqualizers D]

def mappedOrderFork : Fork target.conjunction (fst target.proposition target.proposition) :=
  Fork.ofι (mapping.functor.map (orderInclusion source) ≫ (tupleComparison mapping).hom) (by
    rw [Category.assoc, tupleComparison_conjunction, Category.assoc, tupleComparison_first]
    simp only [Map.image, ← Category.assoc, ← Functor.map_comp]
    exact congrArg (fun arrow => mapping.functor.map arrow ≫ mapping.proposition.hom)
      (equalizer.condition source.conjunction (fst _ _)))

def mappedOrderIsLimit : IsLimit (mappedOrderFork mapping) :=
  Fork.isLimitOfIsos _
    (isLimitOfHasEqualizerOfPreservesLimit mapping.functor source.conjunction
      (fst source.proposition source.proposition))
    (mappedOrderFork mapping) (tupleComparison mapping) mapping.proposition (Iso.refl _)
    (tupleComparison_conjunction mapping) (tupleComparison_first mapping) (Category.id_comp _)

def orderComparison : mapping.functor.obj (orderedPairs source) ≅ orderedPairs target :=
  IsLimit.conePointUniqueUpToIso (mappedOrderIsLimit mapping)
    (limit.isLimit (parallelPair target.conjunction (fst _ _)))

theorem orderComparison_inclusion :
    (orderComparison mapping).hom ≫ orderInclusion target =
      mapping.functor.map (orderInclusion source) ≫ (tupleComparison mapping).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (mappedOrderIsLimit mapping)
    (limit.isLimit (parallelPair target.conjunction (fst _ _))) WalkingParallelPair.zero

theorem orderComparison_smaller :
    (orderComparison mapping).hom ≫ smaller target = mapping.image (smaller source) := by
  change (orderComparison mapping).hom ≫ (orderInclusion target ≫ fst _ _) =
    mapping.functor.map (orderInclusion source ≫ fst _ _) ≫ mapping.proposition.hom
  rw [← Category.assoc, orderComparison_inclusion, Category.assoc,
    tupleComparison_first, Functor.map_comp, Category.assoc]
  rfl

theorem orderComparison_larger :
    (orderComparison mapping).hom ≫ larger target = mapping.image (larger source) := by
  change (orderComparison mapping).hom ≫ (orderInclusion target ≫ snd _ _) =
    mapping.functor.map (orderInclusion source ≫ snd _ _) ≫ mapping.proposition.hom
  rw [← Category.assoc, orderComparison_inclusion, Category.assoc,
    tupleComparison_second, Functor.map_comp, Category.assoc]
  rfl

theorem orderFactor_image (sourceLaws : source.Laws) (targetLaws : target.Laws)
    {context : C} (first second : source.Fiber context)
    (ordered : source.meet second first = first) :
    mapping.functor.map (orderFactor source sourceLaws first second ordered) ≫
        (orderComparison mapping).hom =
      orderFactor target targetLaws (mapping.image first) (mapping.image second)
        ((mapping.image_meet second first).symm.trans (congrArg mapping.image ordered)) := by
  apply equalizer.hom_ext (f := target.conjunction) (g := fst target.proposition target.proposition)
  change _ ≫ orderInclusion target = _ ≫ orderInclusion target
  rw [Category.assoc, orderComparison_inclusion, ← Category.assoc, ← Functor.map_comp]
  have firstRead : orderFactor source sourceLaws first second ordered ≫ orderInclusion source =
      lift first second := equalizer.lift_ι _ _
  have secondRead : orderFactor target targetLaws (mapping.image first) (mapping.image second)
        ((mapping.image_meet second first).symm.trans (congrArg mapping.image ordered)) ≫
      orderInclusion target = lift (mapping.image first) (mapping.image second) := equalizer.lift_ι _ _
  rw [firstRead, secondRead]
  exact tupleComparison_pair mapping first second

omit [HasEqualizers C] [HasEqualizers D] in
theorem tupleComparison_identity :
    (tupleComparison (Map.identity source)).hom = 𝟙 (source.proposition ⊗ source.proposition) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (tupleComparison_first (Map.identity source)).trans
      ((Map.identity_image (fst _ _)).trans (Category.id_comp _).symm)
  · exact (tupleComparison_second (Map.identity source)).trans
      ((Map.identity_image (snd _ _)).trans (Category.id_comp _).symm)

theorem orderComparison_identity :
    (orderComparison (Map.identity source)).hom = 𝟙 (orderedPairs source) := by
  apply equalizer.hom_ext (f := source.conjunction) (g := fst source.proposition source.proposition)
  change _ ≫ orderInclusion source = _ ≫ orderInclusion source
  rw [orderComparison_inclusion, tupleComparison_identity]
  change orderInclusion source ≫ 𝟙 _ = 𝟙 _ ≫ orderInclusion source
  exact (Category.comp_id _).trans (Category.id_comp _).symm

omit [HasEqualizers C] [HasEqualizers D] in
theorem tupleComparison_comp (before : Map source target) (after : Map target last)
    [PreservesFiniteLimits before.functor] [PreservesFiniteLimits after.functor] :
    (tupleComparison (Map.comp before after)).hom =
      after.functor.map (tupleComparison before).hom ≫ (tupleComparison after).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (tupleComparison_first (Map.comp before after)).trans
      ((Map.comp_image before after (fst _ _)).trans
        ((congrArg after.image (tupleComparison_first before).symm).trans
          ((after.image_reindex (tupleComparison before).hom (fst _ _)).trans
            ((congrArg (fun arrow => after.functor.map (tupleComparison before).hom ≫ arrow)
              (tupleComparison_first after).symm).trans (Category.assoc _ _ _).symm))))
  · exact (tupleComparison_second (Map.comp before after)).trans
      ((Map.comp_image before after (snd _ _)).trans
        ((congrArg after.image (tupleComparison_second before).symm).trans
          ((after.image_reindex (tupleComparison before).hom (snd _ _)).trans
            ((congrArg (fun arrow => after.functor.map (tupleComparison before).hom ≫ arrow)
              (tupleComparison_second after).symm).trans (Category.assoc _ _ _).symm))))

variable [HasEqualizers E]

theorem orderComparison_comp (before : Map source target) (after : Map target last)
    [PreservesFiniteLimits before.functor] [PreservesFiniteLimits after.functor] :
    (orderComparison (Map.comp before after)).hom =
      after.functor.map (orderComparison before).hom ≫ (orderComparison after).hom := by
  apply equalizer.hom_ext (f := last.conjunction) (g := fst last.proposition last.proposition)
  change _ ≫ orderInclusion last = _ ≫ orderInclusion last
  refine (orderComparison_inclusion (Map.comp before after)).trans ?_
  change after.functor.map (before.functor.map (orderInclusion source)) ≫
    (tupleComparison (Map.comp before after)).hom =
      (after.functor.map (orderComparison before).hom ≫ (orderComparison after).hom) ≫ orderInclusion last
  rw [tupleComparison_comp, ← Category.assoc, ← Functor.map_comp,
    ← orderComparison_inclusion, Functor.map_comp, Category.assoc,
    Category.assoc, orderComparison_inclusion]

end Mettapedia.CategoryTheory.InternalConjunctiveOrderComparison
