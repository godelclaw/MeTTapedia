import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObjectMaps
import Mettapedia.CategoryTheory.InternalConjunctiveObjectLawReflection

/-!
# Re-presenting a quantified predicate object along an isomorphism

The proposition carrier may be an independently selected isomorphic object.
Truth and conjunction are conjugated by that supplied isomorphism, and the
finite conjunctive laws are reflected through the faithful identity functor.
Both quantifiers are then transported by the independently earned canonical
function-object and ordered-pair comparisons. Their complete arrows recover
the original operations; no quantifier or generalized-element law is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject.Transport

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open InternalPredicateFunctionObjectMaps

universe u k
variable {D : Type u} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (original : Operations D) {carrier : D}
variable (comparison : carrier ≅ original.predicates.proposition)

def predicates : InternalConjunctiveObject.Operations D where
  proposition := carrier
  truth := original.predicates.truth ≫ comparison.inv
  conjunction := lift (fst carrier carrier ≫ comparison.hom) (snd carrier carrier ≫ comparison.hom) ≫
    original.predicates.conjunction ≫ comparison.inv

def forward : InternalConjunctiveObject.Map (predicates original comparison) original.predicates where
  functor := 𝟭 D
  proposition := comparison
  truth := by
    change (original.predicates.truth ≫ comparison.inv) ≫ comparison.hom =
      toUnit (𝟙_ D) ≫ original.predicates.truth
    rw [Category.assoc, comparison.inv_hom_id, Category.comp_id, toUnit_unit, Category.id_comp]
  conjunction := by
    change (lift (fst carrier carrier ≫ comparison.hom) (snd carrier carrier ≫ comparison.hom) ≫
      original.predicates.conjunction ≫ comparison.inv) ≫ comparison.hom =
      lift (fst carrier carrier ≫ comparison.hom) (snd carrier carrier ≫ comparison.hom) ≫
        original.predicates.conjunction
    simp only [Category.assoc, comparison.inv_hom_id, Category.comp_id]

def backward : InternalConjunctiveObject.Map original.predicates (predicates original comparison) where
  functor := 𝟭 D
  proposition := comparison.symm
  truth := by
    change original.predicates.truth ≫ comparison.inv = toUnit (𝟙_ D) ≫
      (original.predicates.truth ≫ comparison.inv)
    rw [toUnit_unit, Category.id_comp]
  conjunction := by
    change original.predicates.conjunction ≫ comparison.inv =
      lift (fst _ _ ≫ comparison.inv) (snd _ _ ≫ comparison.inv) ≫
        (lift (fst carrier carrier ≫ comparison.hom) (snd carrier carrier ≫ comparison.hom) ≫
          original.predicates.conjunction ≫ comparison.inv)
    simp only [← Category.assoc, comp_lift, lift_fst, lift_snd]
    simp only [Category.assoc, comparison.inv_hom_id, Category.comp_id, lift_fst_snd, Category.id_comp]

instance forward_faithful : (forward original comparison).functor.Faithful :=
  inferInstanceAs (𝟭 D).Faithful

instance forward_finite : PreservesFiniteLimits (forward original comparison).functor :=
  inferInstanceAs (PreservesFiniteLimits (𝟭 D))

instance backward_finite : PreservesFiniteLimits (backward original comparison).functor :=
  inferInstanceAs (PreservesFiniteLimits (𝟭 D))

instance forward_closed : MonoidalClosedFunctor (forward original comparison).functor := by
  change MonoidalClosedFunctor (𝟭 D)
  exact cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ Adjunction.id

instance backward_closed : MonoidalClosedFunctor (backward original comparison).functor := by
  change MonoidalClosedFunctor (𝟭 D)
  exact cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ Adjunction.id

theorem laws : (predicates original comparison).Laws :=
  (forward original comparison).reflects_laws original.laws

def operations : Operations D where
  predicates := predicates original comparison
  laws := laws original comparison
  universal route := InternalPredicateQuantifierMaps.universalImage
    (backward original comparison) route (original.universal route)
  existential route := InternalPredicateQuantifierMaps.existentialImage
    (backward original comparison) route (original.existential route)

def forwardMap : Map (operations original comparison) original where
  predicates := forward original comparison
  finite := forward_finite original comparison
  closed := forward_closed original comparison

def backwardMap : Map original (operations original comparison) where
  predicates := backward original comparison
  finite := backward_finite original comparison
  closed := backward_closed original comparison

theorem universal_recovered {before after : D} (route : before ⟶ after) :
    arrowImage (forward original comparison)
      ((operations original comparison).universal route).operation =
        (original.universal route).operation :=
  (forwardMap original comparison).universal_image route

theorem existential_recovered {before after : D} (route : before ⟶ after) :
    arrowImage (forward original comparison)
      ((operations original comparison).existential route).operation =
        (original.existential route).operation :=
  (forwardMap original comparison).existential_image route

theorem predicate_recovered {context : D} (predicate : context ⟶ original.predicates.proposition) :
    (forward original comparison).image ((backward original comparison).image predicate) = predicate := by
  change (predicate ≫ comparison.inv) ≫ comparison.hom = predicate
  rw [Category.assoc, comparison.inv_hom_id, Category.comp_id]

end Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject.Transport
