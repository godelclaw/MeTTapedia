import Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgramHomEquivalence

/-!
# Quantified program completion and its earned adjunction

The free functor installs the actual quantified category, program object
and reduction relation. Its arrow action is earned by the complete hom
correspondence, including the independent program and predicate readings.
Naturality and both triangle laws hold in the existing categories of
compatible map classes. This is the quantified program stratum, not an
unrestricted extension by every logical or binding constructor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgram.FreeForgetful

open _root_.CategoryTheory
open HomEquivalence

universe k

def unit (source : ConjunctiveProgramTheory.{k}) : source ⟶ (freeObject source).conjunctive :=
  ConjunctiveProgramTheory.classOf (unitMap source)

def freeMap {source target : ConjunctiveProgramTheory.{k}} (mapping : source ⟶ target) :
    freeObject source ⟶ freeObject target := extend source (freeObject target) (mapping ≫ unit target)

theorem freeMap_restriction {source target : ConjunctiveProgramTheory.{k}} (mapping : source ⟶ target) :
    restrict source (freeObject target) (freeMap mapping) = mapping ≫ unit target :=
  restrict_extend source (freeObject target) (mapping ≫ unit target)

theorem freeMap_identity (source : ConjunctiveProgramTheory.{k}) :
    freeMap (𝟙 source) = 𝟙 (freeObject source) := by
  apply restrict_injective source (freeObject source)
  rw [freeMap_restriction, restrict_as_base_composition, QuantifiedProgramTheory.forget.map_id]
  change 𝟙 source ≫ unit source = unit source ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

theorem freeMap_compose {source middle target : ConjunctiveProgramTheory.{k}}
    (before : source ⟶ middle) (after : middle ⟶ target) :
    freeMap (before ≫ after) = freeMap before ≫ freeMap after := by
  apply restrict_injective source (freeObject target)
  rw [freeMap_restriction, restrict_postcompose, freeMap_restriction, Category.assoc]
  have complete := freeMap_restriction after
  rw [restrict_as_base_composition] at complete
  change unit middle ≫ QuantifiedProgramTheory.forget.map (freeMap after) = after ≫ unit target at complete
  exact (congrArg (fun value => before ≫ value) complete.symm).trans
    (Category.assoc before (unit middle) (QuantifiedProgramTheory.forget.map (freeMap after))).symm

def free : ConjunctiveProgramTheory.{k} ⥤ QuantifiedProgramTheory.{k} where
  obj := freeObject
  map := freeMap
  map_id := freeMap_identity
  map_comp := freeMap_compose

def homEquiv (source : ConjunctiveProgramTheory.{k}) (target : QuantifiedProgramTheory.{k}) :
    (free.obj source ⟶ target) ≃ (source ⟶ QuantifiedProgramTheory.forget.obj target) :=
  HomEquivalence.homEquiv source target

theorem homEquiv_natural_left_symm
    {source before : ConjunctiveProgramTheory.{k}} {target : QuantifiedProgramTheory.{k}}
    (mapping : before ⟶ source) (value : source ⟶ QuantifiedProgramTheory.forget.obj target) :
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
    {source : ConjunctiveProgramTheory.{k}} {before target : QuantifiedProgramTheory.{k}}
    (mapping : free.obj source ⟶ before) (after : before ⟶ target) :
    homEquiv source target (mapping ≫ after) =
      homEquiv source before mapping ≫ QuantifiedProgramTheory.forget.map after :=
  restrict_postcompose source before mapping after

def adjunction : free.{k} ⊣ QuantifiedProgramTheory.forget :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := homEquiv_natural_left_symm
    homEquiv_naturality_right := homEquiv_natural_right }

theorem unit_app (source : ConjunctiveProgramTheory.{k}) : adjunction.unit.app source = unit source := by
  change restrict source (freeObject source) (𝟙 (freeObject source)) = unit source
  rw [restrict_as_base_composition, QuantifiedProgramTheory.forget.map_id]
  change unit source ≫ 𝟙 _ = unit source
  exact Category.comp_id _

def counitMap (target : QuantifiedProgramTheory.{k}) :
    QuantifiedProgramTheory.Map (freeObject target.conjunctive) target :=
  extension target.conjunctive target (ConjunctiveProgramTheory.Map.identity target.conjunctive)

theorem counit_app (target : QuantifiedProgramTheory.{k}) :
    adjunction.counit.app target = QuantifiedProgramTheory.classOf (counitMap target) := rfl

theorem left_triangle (source : ConjunctiveProgramTheory.{k}) :
    free.map (adjunction.unit.app source) ≫ adjunction.counit.app (free.obj source) = 𝟙 (free.obj source) :=
  adjunction.left_triangle_components source

theorem right_triangle (target : QuantifiedProgramTheory.{k}) :
    adjunction.unit.app (QuantifiedProgramTheory.forget.obj target) ≫
      QuantifiedProgramTheory.forget.map (adjunction.counit.app target) =
        𝟙 (QuantifiedProgramTheory.forget.obj target) := adjunction.right_triangle_components target

end Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgram.FreeForgetful
