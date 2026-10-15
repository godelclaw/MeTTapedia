import Mettapedia.CategoryTheory.PredicateDoctrine

/-!
# Products of indexed predicate doctrines

The two predicate coordinates retain their own substitution, quantifiers,
and evidence of entailment. The product generic predicate classifies the
declared product fibre through its two actual projection maps. Classification
does not identify that fibre with the base category's subobjects.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.PredicateDoctrineProduct

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open PredicateDoctrine

universe u v w z
variable {C : Type u} [Category.{v} C]

def indexed (first : IndexedHeyting.{u,v,w} C) (second : IndexedHeyting.{u,v,z} C) :
    IndexedHeyting.{u,v,max w z} C where
  Fiber X := first.Fiber X × second.Fiber X
  algebra _ := inferInstance
  reindex f predicate := (first.reindex f predicate.1, second.reindex f predicate.2)
  reindex_mono f := fun _ _ ordered =>
    ⟨first.reindex_mono f ordered.1, second.reindex_mono f ordered.2⟩
  reindex_id X predicate :=
    Prod.ext (first.reindex_id X predicate.1) (second.reindex_id X predicate.2)
  reindex_comp f g predicate :=
    Prod.ext (first.reindex_comp f g predicate.1) (second.reindex_comp f g predicate.2)
  reindex_top f := Prod.ext (first.reindex_top f) (second.reindex_top f)
  reindex_bot f := Prod.ext (first.reindex_bot f) (second.reindex_bot f)
  reindex_inf f left right :=
    Prod.ext (first.reindex_inf f left.1 right.1) (second.reindex_inf f left.2 right.2)
  reindex_sup f left right :=
    Prod.ext (first.reindex_sup f left.1 right.1) (second.reindex_sup f left.2 right.2)
  reindex_himp f left right :=
    Prod.ext (first.reindex_himp f left.1 right.1) (second.reindex_himp f left.2 right.2)

def firstOrder (first : FirstOrder.{u,v,w} C) (second : FirstOrder.{u,v,z} C) :
    FirstOrder.{u,v,max w z} C where
  toIndexedHeyting := indexed first.toIndexedHeyting second.toIndexedHeyting
  existsAlong f predicate := (first.existsAlong f predicate.1, second.existsAlong f predicate.2)
  forallAlong f predicate := (first.forallAlong f predicate.1, second.forallAlong f predicate.2)
  exists_mono f := fun _ _ ordered =>
    ⟨first.exists_mono f ordered.1, second.exists_mono f ordered.2⟩
  forall_mono f := fun _ _ ordered =>
    ⟨first.forall_mono f ordered.1, second.forall_mono f ordered.2⟩
  exists_adj f predicate target :=
    and_congr (first.exists_adj f predicate.1 target.1) (second.exists_adj f predicate.2 target.2)
  forall_adj f predicate target :=
    and_congr (first.forall_adj f predicate.1 target.1) (second.forall_adj f predicate.2 target.2)
  frobenius f predicate target :=
    Prod.ext (first.frobenius f predicate.1 target.1) (second.frobenius f predicate.2 target.2)
  exists_baseChange top left right bottom square predicate :=
    Prod.ext (first.exists_baseChange top left right bottom square predicate.1)
      (second.exists_baseChange top left right bottom square predicate.2)
  forall_baseChange top left right bottom square predicate :=
    Prod.ext (first.forall_baseChange top left right bottom square predicate.1)
      (second.forall_baseChange top left right bottom square predicate.2)

variable [CartesianMonoidalCategory C]

def generic (first : IndexedHeyting.{u,v,w} C) (second : IndexedHeyting.{u,v,z} C)
    (firstGeneric : GenericPredicate C first) (secondGeneric : GenericPredicate C second) :
    GenericPredicate C (indexed first second) where
  object := firstGeneric.object ⊗ secondGeneric.object
  truth := (first.reindex (fst _ _) firstGeneric.truth,
    second.reindex (snd _ _) secondGeneric.truth)
  characteristic X predicate := lift (firstGeneric.characteristic X predicate.1)
    (secondGeneric.characteristic X predicate.2)
  classifies X predicate := by
    apply Prod.ext
    · change first.reindex (lift _ _) (first.reindex (fst _ _) firstGeneric.truth) = predicate.1
      rw [← first.reindex_comp, lift_fst]
      exact firstGeneric.classifies X predicate.1
    · change second.reindex (lift _ _) (second.reindex (snd _ _) secondGeneric.truth) = predicate.2
      rw [← second.reindex_comp, lift_snd]
      exact secondGeneric.classifies X predicate.2
  unique X predicate candidate same := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply firstGeneric.unique
      have component := congrArg Prod.fst same
      change first.reindex candidate (first.reindex (fst _ _) firstGeneric.truth) = predicate.1
        at component
      exact (first.reindex_comp candidate (fst _ _) firstGeneric.truth).trans component
    · rw [lift_snd]
      apply secondGeneric.unique
      have component := congrArg Prod.snd same
      change second.reindex candidate (second.reindex (snd _ _) secondGeneric.truth) = predicate.2
        at component
      exact (second.reindex_comp candidate (snd _ _) secondGeneric.truth).trans component

variable [MonoidalClosed C]

def higherOrder (first : HigherOrder.{u,v,w} C) (second : HigherOrder.{u,v,z} C) :
    HigherOrder.{u,v,max w z} C where
  toFirstOrder := firstOrder first.toFirstOrder second.toFirstOrder
  generic := generic first.toIndexedHeyting second.toIndexedHeyting first.generic second.generic

theorem characteristic_first (first : HigherOrder.{u,v,w} C) (second : HigherOrder.{u,v,z} C)
    {X : C} (predicate : (higherOrder first second).Fiber X) :
    (higherOrder first second).generic.characteristic X predicate ≫ fst _ _ =
      first.generic.characteristic X predicate.1 := lift_fst _ _

theorem characteristic_second (first : HigherOrder.{u,v,w} C) (second : HigherOrder.{u,v,z} C)
    {X : C} (predicate : (higherOrder first second).Fiber X) :
    (higherOrder first second).generic.characteristic X predicate ≫ snd _ _ =
      second.generic.characteristic X predicate.2 := lift_snd _ _

/-- A contract in the total fibration contains entailment in both fibres,
over the same actual base program map. -/
def totalHomEquiv (first : HigherOrder.{u,v,w} C) (second : HigherOrder.{u,v,z} C)
    (source target : (higherOrder first second).toIndexedHeyting.Total) :
    (source ⟶ target) ≃ {program : source.base ⟶ target.base //
      source.fiber.1 ≤ first.reindex program target.fiber.1 ∧
        source.fiber.2 ≤ second.reindex program target.fiber.2} :=
  (higherOrder first second).toIndexedHeyting.totalHomEquiv source target

end Mettapedia.CategoryTheory.PredicateDoctrineProduct
