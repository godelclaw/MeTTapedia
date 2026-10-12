import Mettapedia.CategoryTheory.RelativeClosedQuantifiedHomEquivalence
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The actual quantified-completion free-forgetful adjunction

Extension into the next free target constructs the functor action. The
complete restriction correspondence proves its identity and composition
laws and both hom naturalities. The resulting adjunction has actual unit,
counit and triangle equations on the compatible weak-map classes. It adds
quantifiers along every generated arrow while retaining the original
conjunctive proposition structure and raw object presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.FreeForgetful

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open HomEquivalence

universe k

def unit (source : ConjunctiveClosedTheory.{k}) : source ⟶ (freeObject source).conjunctive :=
  ConjunctiveClosedTheory.classOf (Extension.unitMap source)

def freeMap {source target : ConjunctiveClosedTheory.{k}} (mapping : source ⟶ target) :
    freeObject source ⟶ freeObject target := extend source (freeObject target) (mapping ≫ unit target)

theorem freeMap_restriction {source target : ConjunctiveClosedTheory.{k}} (mapping : source ⟶ target) :
    restrict source (freeObject target) (freeMap mapping) = mapping ≫ unit target :=
  restrict_extend source (freeObject target) (mapping ≫ unit target)

theorem freeMap_identity (source : ConjunctiveClosedTheory.{k}) :
    freeMap (𝟙 source) = 𝟙 (freeObject source) := by
  apply restrict_injective source (freeObject source)
  rw [freeMap_restriction, restrict_as_base_composition, QuantifiedClosedTheory.forget.map_id]
  change 𝟙 source ≫ unit source = unit source ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

theorem freeMap_compose {source middle target : ConjunctiveClosedTheory.{k}}
    (before : source ⟶ middle) (after : middle ⟶ target) :
    freeMap (before ≫ after) = freeMap before ≫ freeMap after := by
  apply restrict_injective source (freeObject target)
  rw [freeMap_restriction, restrict_postcompose, freeMap_restriction, Category.assoc]
  have complete := freeMap_restriction after
  rw [restrict_as_base_composition] at complete
  change unit middle ≫ QuantifiedClosedTheory.forget.map (freeMap after) = after ≫ unit target at complete
  exact (congrArg (fun value => before ≫ value) complete.symm).trans
    (Category.assoc before (unit middle) (QuantifiedClosedTheory.forget.map (freeMap after))).symm

def free : ConjunctiveClosedTheory.{k} ⥤ QuantifiedClosedTheory.{k} where
  obj := freeObject
  map := freeMap
  map_id := freeMap_identity
  map_comp := freeMap_compose

def homEquiv (source : ConjunctiveClosedTheory.{k}) (target : QuantifiedClosedTheory.{k}) :
    (free.obj source ⟶ target) ≃ (source ⟶ QuantifiedClosedTheory.forget.obj target) :=
  HomEquivalence.homEquiv source target

theorem homEquiv_natural_left_symm
    {source before : ConjunctiveClosedTheory.{k}} {target : QuantifiedClosedTheory.{k}}
    (mapping : before ⟶ source) (value : source ⟶ QuantifiedClosedTheory.forget.obj target) :
    (homEquiv before target).symm (mapping ≫ value) =
      free.map mapping ≫ (homEquiv source target).symm value := by
  apply restrict_injective before target
  change restrict before target (extend before target (mapping ≫ value)) =
    restrict before target (freeMap mapping ≫ extend source target value)
  rw [restrict_extend, restrict_postcompose, freeMap_restriction, Category.assoc]
  have complete := restrict_extend source target value
  rw [restrict_as_base_composition] at complete
  exact congrArg (fun result => mapping ≫ result) complete.symm

theorem homEquiv_natural_right
    {source : ConjunctiveClosedTheory.{k}} {before target : QuantifiedClosedTheory.{k}}
    (mapping : free.obj source ⟶ before) (after : before ⟶ target) :
    homEquiv source target (mapping ≫ after) =
      homEquiv source before mapping ≫ QuantifiedClosedTheory.forget.map after :=
  restrict_postcompose source before mapping after

def adjunction : free.{k} ⊣ QuantifiedClosedTheory.forget :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := homEquiv_natural_left_symm
    homEquiv_naturality_right := homEquiv_natural_right }

theorem unit_app (source : ConjunctiveClosedTheory.{k}) : adjunction.unit.app source = unit source := by
  change restrict source (freeObject source) (𝟙 (freeObject source)) = unit source
  rw [restrict_as_base_composition, QuantifiedClosedTheory.forget.map_id]
  change unit source ≫ 𝟙 _ = unit source
  exact Category.comp_id _

def counitMap (target : QuantifiedClosedTheory.{k}) :
    QuantifiedClosedTheory.Map (freeObject target.conjunctive) target :=
  Extension.extendMap (ConjunctiveClosedTheory.Map.identity target.conjunctive)

theorem counit_app (target : QuantifiedClosedTheory.{k}) :
    adjunction.counit.app target = QuantifiedClosedTheory.classOf (counitMap target) := rfl

theorem left_triangle (source : ConjunctiveClosedTheory.{k}) :
    free.map (adjunction.unit.app source) ≫ adjunction.counit.app (free.obj source) = 𝟙 (free.obj source) :=
  adjunction.left_triangle_components source

theorem right_triangle (target : QuantifiedClosedTheory.{k}) :
    adjunction.unit.app (QuantifiedClosedTheory.forget.obj target) ≫
      QuantifiedClosedTheory.forget.map (adjunction.counit.app target) =
        𝟙 (QuantifiedClosedTheory.forget.obj target) := adjunction.right_triangle_components target

end Mettapedia.CategoryTheory.RelativeClosedQuantified.FreeForgetful
