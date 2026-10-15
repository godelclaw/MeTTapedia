import Mettapedia.GSLT.Topos.ConstructivePresheafFunctions
import Mettapedia.GSLT.Topos.PresheafPredicateGenericTruth

/-!
# Actual local predicates in the native power presheaf

A power section is a coherent family of sieve-valued predicates at every
restriction, not a global subfunctor lookup. Evaluation and generic truth
give its membership predicate. Every global subfunctor has a characteristic
name among these local sections, with an earned membership comparison.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.NativePowerPredicates

open _root_.CategoryTheory ConstructivePresheaf PresheafPredicateGenericTruth

universe u

variable {C : Type u} [Category.{u} C] (A : Cᵒᵖ ⥤ Type u)

def power : Cᵒᵖ ⥤ Type u := functions A (omegaFunctor (C := C))

def product : Cᵒᵖ ⥤ Type u := FunctorToTypes.prod A (power A)

def first : product A ⟶ A where
  app _ := TypeCat.ofHom Prod.fst
  naturality := by intros; rfl

def second : product A ⟶ power A where
  app _ := TypeCat.ofHom Prod.snd
  naturality := by intros; rfl

/-- Generic membership is evaluation into the actual sieve classifier. -/
noncomputable def membership : Subfunctor (product A) :=
  (truthPredicate C).preimage (evaluate A (omegaFunctor (C := C)))

theorem membership_iff (world : Cᵒᵖ) (value : (product A).obj world) :
    value ∈ (membership A).obj world ↔
      value.2.app world (𝟙 world) value.1 = (⊤ : Sieve world.unop) :=
  truth_iff_top _ _

/-- A global predicate produces an actual local power section; its
characteristic maps supply every restriction component. -/
noncomputable def name (predicate : Subfunctor A) (world : Cᵒᵖ) :
    (power A).obj world where
  app future _ := (chiOfSubfunctor A predicate).app future
  naturality arrow _ := (chiOfSubfunctor A predicate).naturality arrow

theorem name_restrict (predicate : Subfunctor A) {world future : Cᵒᵖ}
    (arrow : world ⟶ future) :
    (power A).map arrow (name A predicate world) = name A predicate future := by
  apply Functor.HomObj.ext
  funext target restriction
  rfl

noncomputable def pairName (predicate : Subfunctor A) : A ⟶ product A where
  app world := TypeCat.ofHom fun value => (value, name A predicate world)
  naturality world future arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext rfl (name_restrict A predicate arrow)

/-- Generic power membership recovers the independently supplied predicate. -/
theorem membership_pairName (predicate : Subfunctor A) :
    (membership A).preimage (pairName A predicate) = predicate := by
  ext world value
  change value ∈ ((truthPredicate C).preimage (chiOfSubfunctor A predicate)).obj world ↔ _
  rw [characteristic_classifies]

def guardedProduct (guard : Subfunctor (power A)) : Cᵒᵖ ⥤ Type u :=
  FunctorToTypes.prod A guard.toFunctor

def guardedFirst (guard : Subfunctor (power A)) : guardedProduct A guard ⟶ A where
  app _ := TypeCat.ofHom Prod.fst
  naturality := by intros; rfl

def inclusion (guard : Subfunctor (power A)) : guardedProduct A guard ⟶ product A where
  app _ := TypeCat.ofHom fun value => (value.1, value.2.val)
  naturality := by intros; rfl

/-- Restricting a predicate inequality to the satisfying guard subobject
earns the guarded inequality on all local power sections. -/
theorem guarded_inequality (guard : Subfunctor (power A))
    (left right : Subfunctor (product A))
    (restricted : left.preimage (inclusion A guard) ≤ right.preimage (inclusion A guard)) :
    left ⊓ guard.preimage (second A) ≤ right := by
  intro world value held
  exact restricted world
    (show (value.1, (⟨value.2, held.2⟩ : guard.obj world)) ∈
      (left.preimage (inclusion A guard)).obj world from held.1)

end Mettapedia.GSLT.Topos.NativePowerPredicates
