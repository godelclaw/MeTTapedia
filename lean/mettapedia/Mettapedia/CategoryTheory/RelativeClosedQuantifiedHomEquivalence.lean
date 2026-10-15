import Mettapedia.CategoryTheory.RelativeClosedQuantifiedUniversal

/-!
# Both weak-map hom roundtrips for quantified completion

Restriction remembers the complete conjunctive map, including the supplied
proposition comparison. Extension independently constructs every quantifier
interpretation. The earned comparison from the restricted local structure
determines each arbitrary candidate on all objects and arrows. Compatible
natural-isomorphism classes therefore have an actual hom equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.HomEquivalence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory
open RelativeClosedGeneratedQuantifier Iteration

universe k
variable (source : ConjunctiveClosedTheory.{k}) (target : QuantifiedClosedTheory.{k})

def extension_restriction (mapping : ConjunctiveClosedTheory.Map source target.conjunctive) :
    ConjunctiveClosedTheory.MapIso (Extension.restrictMap (Extension.extendMap mapping)) mapping where
  comparison := eqToIso (Extension.complete_base_recovered mapping)
  proposition := by
    simp only [eqToIso.hom, eqToHom_app]
    change eqToHom (congrArg (fun functor => functor.obj source.operations.proposition)
        (Extension.complete_base_recovered mapping)) ≫ mapping.declarations.proposition.hom =
      (Models.diagram mapping ⋙ 𝟭 target.closed.Obj).map
        (Extension.unitMap source).declarations.proposition.hom ≫
        ((𝟭 target.closed.Obj).map (eqToHom (Closure.model_proposition_read (Models.initial mapping))) ≫
          mapping.declarations.proposition.hom)
    rw [Extension.unit_proposition_hom]
    change eqToHom (congrArg (fun functor => functor.obj source.operations.proposition)
        (Extension.complete_base_recovered mapping)) ≫ mapping.declarations.proposition.hom =
      (Models.diagram mapping ⋙ 𝟭 target.closed.Obj).map
        (𝟙 (freeObject source).operations.predicates.proposition) ≫
        (eqToHom (Closure.model_proposition_read (Models.initial mapping)) ≫
          mapping.declarations.proposition.hom)
    rw [(Models.diagram mapping ⋙ 𝟭 target.closed.Obj).map_id, Category.id_comp]

def restriction_comparison {first second : QuantifiedClosedTheory.Map (freeObject source) target}
    (comparison : QuantifiedClosedTheory.MapIso first second) :
    ConjunctiveClosedTheory.MapIso (Extension.restrictMap first) (Extension.restrictMap second) :=
  ConjunctiveClosedTheory.MapIso.precompose (Extension.unitMap source) comparison

def mapIsoOfRestriction {first second : QuantifiedClosedTheory.Map (freeObject source) target}
    (comparison : ConjunctiveClosedTheory.MapIso (Extension.restrictMap first) (Extension.restrictMap second)) :
    QuantifiedClosedTheory.MapIso first second :=
  (Universal.completeComparison (Extension.restrictMap second) first comparison).trans
    (Universal.completeComparison (Extension.restrictMap second) second
      (ConjunctiveClosedTheory.MapIso.refl _)).symm

def extension_comparison {first second : ConjunctiveClosedTheory.Map source target.conjunctive}
    (comparison : ConjunctiveClosedTheory.MapIso first second) :
    QuantifiedClosedTheory.MapIso (Extension.extendMap first) (Extension.extendMap second) :=
  mapIsoOfRestriction source target
    ((extension_restriction source target first).trans
      (comparison.trans (extension_restriction source target second).symm))

def restrict : (freeObject source ⟶ target) → (source ⟶ target.conjunctive) :=
  Quotient.map Extension.restrictMap (fun _ _ comparison => by
    obtain ⟨comparison⟩ := comparison
    exact ⟨restriction_comparison source target comparison⟩)

def extend : (source ⟶ target.conjunctive) → (freeObject source ⟶ target) :=
  Quotient.map Extension.extendMap (fun _ _ comparison => by
    obtain ⟨comparison⟩ := comparison
    exact ⟨extension_comparison source target comparison⟩)

theorem restrict_classOf (mapping : QuantifiedClosedTheory.Map (freeObject source) target) :
    restrict source target (QuantifiedClosedTheory.classOf mapping) =
      ConjunctiveClosedTheory.classOf (Extension.restrictMap mapping) := rfl

theorem extend_classOf (mapping : ConjunctiveClosedTheory.Map source target.conjunctive) :
    extend source target (ConjunctiveClosedTheory.classOf mapping) =
      QuantifiedClosedTheory.classOf (Extension.extendMap mapping) := rfl

theorem restrict_extend (mapping : source ⟶ target.conjunctive) :
    restrict source target (extend source target mapping) = mapping := by
  refine Quotient.inductionOn mapping fun mapping => ?_
  exact Quotient.sound ⟨extension_restriction source target mapping⟩

theorem restrict_injective : Function.Injective (restrict source target) := by
  intro first second
  refine Quotient.inductionOn₂ first second fun first second same => ?_
  obtain ⟨comparison⟩ := (ConjunctiveClosedTheory.classOf_equal_iff
    (Extension.restrictMap first) (Extension.restrictMap second)).mp same
  exact Quotient.sound ⟨mapIsoOfRestriction source target comparison⟩

theorem extend_restrict (mapping : freeObject source ⟶ target) :
    extend source target (restrict source target mapping) = mapping :=
  restrict_injective source target (restrict_extend source target (restrict source target mapping))

def homEquiv : (freeObject source ⟶ target) ≃ (source ⟶ target.conjunctive) where
  toFun := restrict source target
  invFun := extend source target
  left_inv := extend_restrict source target
  right_inv := restrict_extend source target

theorem restrict_as_base_composition (mapping : freeObject source ⟶ target) :
    restrict source target mapping =
      ConjunctiveClosedTheory.classOf (Extension.unitMap source) ≫ QuantifiedClosedTheory.forget.map mapping := by
  refine Quotient.inductionOn mapping fun mapping => ?_
  rfl

theorem restrict_postcompose {later : QuantifiedClosedTheory.{k}}
    (before : freeObject source ⟶ target) (after : target ⟶ later) :
    restrict source later (before ≫ after) =
      restrict source target before ≫ QuantifiedClosedTheory.forget.map after := by
  rw [restrict_as_base_composition, restrict_as_base_composition,
    QuantifiedClosedTheory.forget.map_comp, Category.assoc]

end Mettapedia.CategoryTheory.RelativeClosedQuantified.HomEquivalence
