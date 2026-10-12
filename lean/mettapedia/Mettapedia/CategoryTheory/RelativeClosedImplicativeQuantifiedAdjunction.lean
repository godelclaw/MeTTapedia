import Mettapedia.CategoryTheory.ImplicativeProgramTheory
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgramAdjunction
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedImplication

/-!
# Quantified completion over implication-qualified program theories

The completion installs quantifiers at every arrow while transporting the
three implication diagrams. Its actual map action and hom correspondence
vary over the entire category of implication-qualified program theories.
Both hom roundtrips, naturality and triangle laws retain the existing
compatible predicate/program map classes and complete event readings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedImplicativeQuantified

open _root_.CategoryTheory

universe k

def freeObject (source : ImplicativeProgramTheory.{k}) : QuantifiedImplicativeProgramTheory.{k} where
  quantified := RelativeClosedQuantifiedProgram.freeObject source.conjunctive
  implication := RelativeClosedQuantified.Implication.freeQualification source.conjunctive.conjunctive
    source.implication

def unitMap (source : ImplicativeProgramTheory.{k}) :
    ImplicativeProgramTheory.Map source (freeObject source).implicative :=
  RelativeClosedQuantifiedProgram.unitMap source.conjunctive

def unit (source : ImplicativeProgramTheory.{k}) : source ⟶ (freeObject source).implicative :=
  ImplicativeProgramTheory.classOf (unitMap source)

def extension (source : ImplicativeProgramTheory.{k}) (target : QuantifiedImplicativeProgramTheory.{k})
    (mapping : ImplicativeProgramTheory.Map source target.implicative) :
    QuantifiedImplicativeProgramTheory.Map (freeObject source) target :=
  RelativeClosedQuantifiedProgram.HomEquivalence.extension source.conjunctive target.quantified mapping

def restriction (source : ImplicativeProgramTheory.{k}) (target : QuantifiedImplicativeProgramTheory.{k})
    (mapping : QuantifiedImplicativeProgramTheory.Map (freeObject source) target) :
    ImplicativeProgramTheory.Map source target.implicative :=
  RelativeClosedQuantifiedProgram.HomEquivalence.restriction source.conjunctive target.quantified mapping

def extensionRestriction (source : ImplicativeProgramTheory.{k}) (target : QuantifiedImplicativeProgramTheory.{k})
    (mapping : ImplicativeProgramTheory.Map source target.implicative) :
    ImplicativeProgramTheory.MapIso (restriction source target (extension source target mapping)) mapping :=
  RelativeClosedQuantifiedProgram.HomEquivalence.extension_restriction source.conjunctive target.quantified mapping

def freeMap {source target : ImplicativeProgramTheory.{k}} (mapping : source ⟶ target) :
    freeObject source ⟶ freeObject target :=
  RelativeClosedQuantifiedProgram.FreeForgetful.freeMap mapping

theorem freeMap_identity (source : ImplicativeProgramTheory.{k}) :
    freeMap (𝟙 source) = 𝟙 (freeObject source) :=
  RelativeClosedQuantifiedProgram.FreeForgetful.freeMap_identity source.conjunctive

theorem freeMap_compose {source middle target : ImplicativeProgramTheory.{k}}
    (before : source ⟶ middle) (after : middle ⟶ target) :
    freeMap (before ≫ after) = freeMap before ≫ freeMap after :=
  RelativeClosedQuantifiedProgram.FreeForgetful.freeMap_compose before after

def free : ImplicativeProgramTheory.{k} ⥤ QuantifiedImplicativeProgramTheory.{k} where
  obj := freeObject
  map := freeMap
  map_id := freeMap_identity
  map_comp := freeMap_compose

def homEquiv (source : ImplicativeProgramTheory.{k}) (target : QuantifiedImplicativeProgramTheory.{k}) :
    (free.obj source ⟶ target) ≃ (source ⟶ QuantifiedImplicativeProgramTheory.forget.obj target) :=
  RelativeClosedQuantifiedProgram.HomEquivalence.homEquiv source.conjunctive target.quantified

theorem homEquiv_natural_left_symm
    {before source : ImplicativeProgramTheory.{k}} {target : QuantifiedImplicativeProgramTheory.{k}}
    (mapping : before ⟶ source) (value : source ⟶ QuantifiedImplicativeProgramTheory.forget.obj target) :
    (homEquiv before target).symm (mapping ≫ value) =
      free.map mapping ≫ (homEquiv source target).symm value :=
  RelativeClosedQuantifiedProgram.FreeForgetful.homEquiv_natural_left_symm mapping value

theorem homEquiv_natural_right
    {source : ImplicativeProgramTheory.{k}} {before target : QuantifiedImplicativeProgramTheory.{k}}
    (mapping : free.obj source ⟶ before) (after : before ⟶ target) :
    homEquiv source target (mapping ≫ after) =
      homEquiv source before mapping ≫ QuantifiedImplicativeProgramTheory.forget.map after :=
  RelativeClosedQuantifiedProgram.FreeForgetful.homEquiv_natural_right mapping after

def adjunction : free.{k} ⊣ QuantifiedImplicativeProgramTheory.forget :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := homEquiv_natural_left_symm
    homEquiv_naturality_right := homEquiv_natural_right }

theorem unit_app (source : ImplicativeProgramTheory.{k}) : adjunction.unit.app source = unit source :=
  RelativeClosedQuantifiedProgram.FreeForgetful.unit_app source.conjunctive

def counitMap (target : QuantifiedImplicativeProgramTheory.{k}) :
    QuantifiedImplicativeProgramTheory.Map (freeObject target.implicative) target :=
  RelativeClosedQuantifiedProgram.FreeForgetful.counitMap target.quantified

theorem counit_app (target : QuantifiedImplicativeProgramTheory.{k}) :
    adjunction.counit.app target = QuantifiedImplicativeProgramTheory.classOf (counitMap target) := rfl

theorem left_triangle (source : ImplicativeProgramTheory.{k}) :
    free.map (adjunction.unit.app source) ≫ adjunction.counit.app (free.obj source) = 𝟙 (free.obj source) :=
  adjunction.left_triangle_components source

theorem right_triangle (target : QuantifiedImplicativeProgramTheory.{k}) :
    adjunction.unit.app (QuantifiedImplicativeProgramTheory.forget.obj target) ≫
      QuantifiedImplicativeProgramTheory.forget.map (adjunction.counit.app target) =
        𝟙 (QuantifiedImplicativeProgramTheory.forget.obj target) := adjunction.right_triangle_components target

end Mettapedia.CategoryTheory.RelativeClosedImplicativeQuantified
