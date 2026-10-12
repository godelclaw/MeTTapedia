import Mettapedia.GSLT.Topos.NativePowerPiComparison
import Mettapedia.GSLT.Topos.PresheafPredicateUniversalQuantifier

/-!
# Quantifiers retain the complete local predicate representation

A comparison of the entire quantified presheaf, commuting with its base
projection, transports both actual quantifiers. Universal quantification
keeps every future generalized section; existential quantification retains
its actual witness. Neither law is a global-fibre approximation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.NativePowerQuantifiers

open _root_.CategoryTheory

universe u
variable {C : Type u} [Category.{u} C]
variable {X Y P : Cᵒᵖ ⥤ Type u}

/-- Actual universal quantification is unchanged by a complete over-base
representation isomorphism. -/
theorem forall_comparison (comparison : X ≅ Y) (source : X ⟶ P) (target : Y ⟶ P)
    (square : comparison.hom ≫ target = source) (predicate : Subfunctor Y) :
    forallAlong source (predicate.preimage comparison.hom) = forallAlong target predicate := by
  have inverseSquare : comparison.inv ≫ source = target := by
    rw [← square, ← Category.assoc, comparison.inv_hom_id, Category.id_comp]
  ext world parameter
  constructor
  · intro held future restriction candidate above
    have projected := ConcreteCategory.congr_hom (NatTrans.congr_app inverseSquare future) candidate
    have supplied := held future restriction (comparison.inv.app future candidate)
      (projected.trans above)
    have roundtrip := ConcreteCategory.congr_hom (comparison.inv_hom_id_app future) candidate
    change comparison.hom.app future (comparison.inv.app future candidate) = candidate at roundtrip
    change comparison.hom.app future (comparison.inv.app future candidate) ∈ predicate.obj future at supplied
    rw [roundtrip] at supplied
    exact supplied
  · intro held future restriction candidate above
    have projected := ConcreteCategory.congr_hom (NatTrans.congr_app square future) candidate
    exact held future restriction (comparison.hom.app future candidate) (projected.trans above)

/-- Existential witnesses survive the same representation comparison. -/
theorem exists_comparison (comparison : X ≅ Y) (source : X ⟶ P) (target : Y ⟶ P)
    (square : comparison.hom ≫ target = source) (predicate : Subfunctor Y) :
    (predicate.preimage comparison.hom).image source = predicate.image target := by
  have inverseSquare : comparison.inv ≫ source = target := by
    rw [← square, ← Category.assoc, comparison.inv_hom_id, Category.id_comp]
  ext world parameter
  constructor
  · rintro ⟨candidate, held, above⟩
    refine ⟨comparison.hom.app world candidate, held, ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app square world) candidate).trans above
  · rintro ⟨candidate, held, above⟩
    refine ⟨comparison.inv.app world candidate, ?_, ?_⟩
    · change comparison.hom.app world (comparison.inv.app world candidate) ∈ predicate.obj world
      have roundtrip := ConcreteCategory.congr_hom (comparison.inv_hom_id_app world) candidate
      change comparison.hom.app world (comparison.inv.app world candidate) = candidate at roundtrip
      rw [roundtrip]
      exact held
    · exact (ConcreteCategory.congr_hom (NatTrans.congr_app inverseSquare world) candidate).trans above

end Mettapedia.GSLT.Topos.NativePowerQuantifiers
