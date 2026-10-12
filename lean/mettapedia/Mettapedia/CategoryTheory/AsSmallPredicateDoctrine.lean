import Mettapedia.CategoryTheory.AsSmallYoneda
import Mettapedia.CategoryTheory.PredicateDoctrine
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Predicate doctrines across the actual category universe equivalence

The normalized fibre is the original fibre at the lowered object. Complete
arrow substitution and both quantifiers use the actual downward functor.
Its equivalence preserves pullbacks, so both base-change equations retain
their genuine pullback premise. The generic predicate is raised with its
entire characteristic arrow, including classification and uniqueness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.AsSmallPredicateDoctrine

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open AsSmallYoneda PredicateDoctrine

universe u v p
variable {C : Type u} [Category.{v} C]

def indexed (original : IndexedHeyting.{u,v,p} C) : IndexedHeyting.{max u v,max u v,p} (Small C) where
  Fiber object := original.Fiber ((down C).obj object)
  algebra object := original.algebra ((down C).obj object)
  reindex arrow predicate := original.reindex arrow.down predicate
  reindex_mono arrow := original.reindex_mono arrow.down
  reindex_id object predicate := original.reindex_id ((down C).obj object) predicate
  reindex_comp before after predicate := original.reindex_comp before.down after.down predicate
  reindex_top arrow := original.reindex_top arrow.down
  reindex_bot arrow := original.reindex_bot arrow.down
  reindex_inf arrow first second := original.reindex_inf arrow.down first second
  reindex_sup arrow first second := original.reindex_sup arrow.down first second
  reindex_himp arrow first second := original.reindex_himp arrow.down first second

variable [HasFiniteLimits C]

def firstOrder (original : FirstOrder.{u,v,p} C) : FirstOrder.{max u v,max u v,p} (Small C) where
  toIndexedHeyting := indexed original.toIndexedHeyting
  existsAlong arrow predicate := original.existsAlong arrow.down predicate
  forallAlong arrow predicate := original.forallAlong arrow.down predicate
  exists_mono arrow := original.exists_mono arrow.down
  forall_mono arrow := original.forall_mono arrow.down
  exists_adj arrow := original.exists_adj arrow.down
  forall_adj arrow := original.forall_adj arrow.down
  frobenius arrow first second := original.frobenius arrow.down first second
  exists_baseChange top left right bottom square predicate :=
    original.exists_baseChange top.down left.down right.down bottom.down
      (square.map (down C)) predicate
  forall_baseChange top left right bottom square predicate :=
    original.forall_baseChange top.down left.down right.down bottom.down
      (square.map (down C)) predicate

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

def higherOrder (original : HigherOrder.{u,v,p} C) : HigherOrder.{max u v,max u v,p} (Small C) where
  toFirstOrder := firstOrder original.toFirstOrder
  generic := {
    object := (up C).obj original.generic.object
    truth := original.generic.truth
    characteristic := fun object predicate => ULift.up (original.generic.characteristic ((down C).obj object) predicate)
    classifies := fun object predicate => original.generic.classifies ((down C).obj object) predicate
    unique := fun object predicate arrow reading =>
      ULift.ext _ _ (original.generic.unique ((down C).obj object) predicate arrow.down reading) }

theorem characteristic_readout (original : HigherOrder.{u,v,p} C) (object : C)
    (predicate : original.Fiber object) :
    ((higherOrder original).generic.characteristic ((up C).obj object) predicate).down =
      original.generic.characteristic object predicate := rfl

theorem substitution_readout (original : HigherOrder.{u,v,p} C) {before after : C}
    (arrow : before ⟶ after) (predicate : original.Fiber after) :
    (higherOrder original).reindex ((up C).map arrow) predicate = original.reindex arrow predicate := rfl

theorem both_quantifiers_readout (original : HigherOrder.{u,v,p} C) {before after : C}
    (arrow : before ⟶ after) (predicate : original.Fiber before) :
    (higherOrder original).existsAlong ((up C).map arrow) predicate = original.existsAlong arrow predicate ∧
      (higherOrder original).forallAlong ((up C).map arrow) predicate = original.forallAlong arrow predicate :=
  ⟨rfl, rfl⟩

end Mettapedia.CategoryTheory.AsSmallPredicateDoctrine
