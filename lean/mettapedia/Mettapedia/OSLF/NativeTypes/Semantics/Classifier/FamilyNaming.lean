import Mettapedia.GSLT.Topos.NativePowerPredicates

/-!
# Naming classifiers with open parameters

A subfunctor of operational arguments and parameters determines a natural
family of local classifiers. The name carries parameters to every future
world. Its membership and substitution laws recover the original family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.FamilyNaming

open _root_.CategoryTheory
open Mettapedia.GSLT.Topos ConstructivePresheaf PresheafPredicateGenericTruth

universe u
variable {W : Type u} [Category.{u} W]
variable {A P Q : Wᵒᵖ ⥤ Type u}

/-- The argument is first, matching the actual function object's evaluation. -/
noncomputable def name (predicate : Subfunctor (FunctorToTypes.prod A P)) :
    P ⟶ NativePowerPredicates.power A :=
  curryFunction (chiOfSubfunctor _ predicate)

noncomputable def membership (predicate : Subfunctor (FunctorToTypes.prod A P)) :
    Subfunctor (FunctorToTypes.prod A P) :=
  (NativePowerPredicates.membership A).preimage
    { app world := TypeCat.ofHom fun pair => (pair.1, (name predicate).app world pair.2)
      naturality world future arrow := by
        apply ConcreteCategory.hom_ext
        intro pair
        change (A.map arrow pair.1, (name predicate).app future (P.map arrow pair.2)) =
          (A.map arrow pair.1, (NativePowerPredicates.power A).map arrow ((name predicate).app world pair.2))
        exact Prod.ext rfl ((name predicate).naturality_apply arrow pair.2) }

/-- Parameterized classifier application has precisely its independent meaning. -/
theorem membership_exact (predicate : Subfunctor (FunctorToTypes.prod A P)) :
    membership predicate = predicate := by
  ext world pair
  change (pair.1, (name predicate).app world pair.2) ∈ (NativePowerPredicates.membership A).obj world ↔ _
  refine (NativePowerPredicates.membership_iff A world (pair.1, (name predicate).app world pair.2)).trans ?_
  change (chiOfSubfunctor _ predicate).app world
      (pair.1, P.map (𝟙 world) pair.2) = (⊤ : Sieve world.unop) ↔ _
  rw [Functor.map_id_apply]
  exact (truth_iff_top _ _).symm.trans (Iff.of_eq (congrArg (fun p : Subfunctor (FunctorToTypes.prod A P) => pair ∈ p.obj world) (characteristic_classifies _ predicate)))

/-- Each local classifier retains the predicate's full parameter dependence. -/
theorem member_name (predicate : Subfunctor (FunctorToTypes.prod A P))
    (world : Wᵒᵖ) (argument : A.obj world) (parameter : P.obj world) :
    (argument, (name predicate).app world parameter) ∈
      (NativePowerPredicates.membership A).obj world ↔
        (argument, parameter) ∈ predicate.obj world := by
  change (argument, parameter) ∈ (membership predicate).obj world ↔ _
  rw [membership_exact]

def parameters (mapping : Q ⟶ P) :
    FunctorToTypes.prod A Q ⟶ FunctorToTypes.prod A P where
  app _ := TypeCat.ofHom fun pair => (pair.1, mapping.app _ pair.2)
  naturality world future arrow := by
    apply ConcreteCategory.hom_ext
    intro pair
    change (A.map arrow pair.1, mapping.app future (Q.map arrow pair.2)) =
      (A.map arrow pair.1, P.map arrow (mapping.app world pair.2))
    exact Prod.ext rfl (mapping.naturality_apply arrow pair.2)

/-- Ordinary substitution changes the name's parameters and all future values. -/
theorem substitution (predicate : Subfunctor (FunctorToTypes.prod A P)) (mapping : Q ⟶ P) :
    mapping ≫ name predicate = name (predicate.preimage (parameters mapping)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro parameter
  apply Functor.HomObj.ext
  funext future restriction
  apply ConcreteCategory.hom_ext
  intro argument
  change (chiOfSubfunctor _ predicate).app future
      (argument, P.map restriction (mapping.app world parameter)) =
    (chiOfSubfunctor _ (predicate.preimage (parameters mapping))).app future
      (argument, Q.map restriction parameter)
  change world ⟶ future at restriction
  rw [← mapping.naturality_apply restriction parameter]
  have comparison : parameters mapping ≫ chiOfSubfunctor _ predicate =
      chiOfSubfunctor _ (predicate.preimage (parameters mapping)) := by
    apply characteristic_unique
    rw [Subfunctor.preimage_comp, characteristic_classifies]
  exact congrArg (fun arrow : FunctorToTypes.prod A Q ⟶ omegaFunctor (C := W) =>
    arrow.app future (argument, Q.map restriction parameter)) comparison

end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.FamilyNaming
