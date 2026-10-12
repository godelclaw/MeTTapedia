import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Algebra.Group.Action.Defs

/-!
# Complete internal actions in a cartesian category

The two action diagrams compare entire edge arrows. Their generalized-element
readouts retain every supplied edge and both frame arguments. The scalar
diagrams similarly give actual commutative monoids on all hom sets, and the
action diagrams give their actions on edge sections.

Endpoint compatibility is a separate property. It is not a replacement for
the unit or associativity diagram on the edge object.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.CartesianMonoidAction

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable (C) in
structure Data where
  edge : C
  scalar : C
  zero : 𝟙_ C ⟶ scalar
  merge : scalar ⊗ scalar ⟶ scalar
  act : edge ⊗ scalar ⟶ edge

variable (data : Data C)

def apply {Z : C} (edge : Z ⟶ data.edge) (frame : Z ⟶ data.scalar) : Z ⟶ data.edge :=
  lift edge frame ≫ data.act

def product {Z : C} (first second : Z ⟶ data.scalar) : Z ⟶ data.scalar :=
  lift first second ≫ data.merge

def neutral (Z : C) : Z ⟶ data.scalar := toUnit Z ≫ data.zero

def unitDiagram : data.edge ⟶ data.edge := apply data (𝟙 _) (neutral data _)

def twiceDiagram : (data.edge ⊗ data.scalar) ⊗ data.scalar ⟶ data.edge :=
  apply data (apply data (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _)) (snd _ _)

def mergedDiagram : (data.edge ⊗ data.scalar) ⊗ data.scalar ⟶ data.edge :=
  apply data (fst _ _ ≫ fst _ _) (product data (fst _ _ ≫ snd _ _) (snd _ _))

structure Laws : Prop where
  unit : unitDiagram data = 𝟙 data.edge
  associativity : twiceDiagram data = mergedDiagram data

def scalarUnitDiagram : data.scalar ⟶ data.scalar :=
  product data (𝟙 _) (neutral data _)

def scalarTwiceDiagram : (data.scalar ⊗ data.scalar) ⊗ data.scalar ⟶ data.scalar :=
  product data (product data (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _)) (snd _ _)

def scalarMergedDiagram : (data.scalar ⊗ data.scalar) ⊗ data.scalar ⟶ data.scalar :=
  product data (fst _ _ ≫ fst _ _) (product data (fst _ _ ≫ snd _ _) (snd _ _))

structure ScalarLaws : Prop where
  unit : scalarUnitDiagram data = 𝟙 data.scalar
  associativity : scalarTwiceDiagram data = scalarMergedDiagram data
  commutativity : data.merge = lift (snd _ _) (fst _ _) ≫ data.merge

theorem apply_precompose {Z W : C} (change : W ⟶ Z)
    (edge : Z ⟶ data.edge) (frame : Z ⟶ data.scalar) :
    change ≫ apply data edge frame = apply data (change ≫ edge) (change ≫ frame) := by
  simp only [apply, comp_lift_assoc]

theorem product_precompose {Z W : C} (change : W ⟶ Z)
    (first second : Z ⟶ data.scalar) :
    change ≫ product data first second = product data (change ≫ first) (change ≫ second) := by
  simp only [product, comp_lift_assoc]

theorem neutral_precompose {Z W : C} (change : W ⟶ Z) :
    change ≫ neutral data Z = neutral data W := by
  simp only [neutral, ← Category.assoc, comp_toUnit]

theorem apply_zero (laws : Laws data) {Z : C} (edge : Z ⟶ data.edge) :
    apply data edge (neutral data Z) = edge := by
  have result := congrArg (edge ≫ ·) laws.unit
  simpa only [unitDiagram, apply_precompose, neutral_precompose, Category.comp_id] using result

theorem apply_associativity (laws : Laws data) {Z : C}
    (edge : Z ⟶ data.edge) (first second : Z ⟶ data.scalar) :
    apply data (apply data edge first) second = apply data edge (product data first second) := by
  have result := congrArg (lift (lift edge first) second ≫ ·) laws.associativity
  simpa only [twiceDiagram, mergedDiagram, apply_precompose, product_precompose,
    Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using result

theorem laws_iff_sections : Laws data ↔
    (∀ (Z : C) (edge : Z ⟶ data.edge), apply data edge (neutral data Z) = edge) ∧
    (∀ (Z : C) (edge : Z ⟶ data.edge) (first second : Z ⟶ data.scalar),
      apply data (apply data edge first) second = apply data edge (product data first second)) := by
  constructor
  · intro laws
    exact ⟨fun _ => apply_zero data laws, fun _ => apply_associativity data laws⟩
  · rintro ⟨unit, associativity⟩
    exact ⟨unit _ (𝟙 _), associativity _ (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _)⟩

theorem product_zero (laws : ScalarLaws data) {Z : C} (scalar : Z ⟶ data.scalar) :
    product data scalar (neutral data Z) = scalar := by
  have result := congrArg (scalar ≫ ·) laws.unit
  simpa only [scalarUnitDiagram, product_precompose, neutral_precompose,
    Category.comp_id] using result

theorem product_associativity (laws : ScalarLaws data) {Z : C}
    (first second third : Z ⟶ data.scalar) :
    product data (product data first second) third = product data first (product data second third) := by
  have result := congrArg (lift (lift first second) third ≫ ·) laws.associativity
  simpa only [scalarTwiceDiagram, scalarMergedDiagram, product_precompose,
    Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using result

theorem product_commutativity (laws : ScalarLaws data) {Z : C}
    (first second : Z ⟶ data.scalar) : product data first second = product data second first := by
  have result := congrArg (lift first second ≫ ·) laws.commutativity
  simpa only [product, comp_lift_assoc, lift_fst, lift_snd] using result

theorem frame_exchange (laws : Laws data) (scalars : ScalarLaws data) {Z : C}
    (edge : Z ⟶ data.edge) (first second : Z ⟶ data.scalar) :
    apply data (apply data edge first) second = apply data (apply data edge second) first := by
  rw [apply_associativity data laws, apply_associativity data laws,
    product_commutativity data scalars first second]

@[instance_reducible] def sectionMonoid (scalars : ScalarLaws data) (Z : C) : CommMonoid (Z ⟶ data.scalar) where
  one := neutral data Z
  mul := product data
  mul_assoc := product_associativity data scalars
  one_mul scalar := (product_commutativity data scalars _ _).trans (product_zero data scalars scalar)
  mul_one := product_zero data scalars
  mul_comm := product_commutativity data scalars

@[instance_reducible] def sectionAction (scalars : ScalarLaws data) (laws : Laws data) (Z : C) :
    letI := sectionMonoid data scalars Z
    MulAction (Z ⟶ data.scalar) (Z ⟶ data.edge) := by
  letI := sectionMonoid data scalars Z
  exact {
    smul frame edge := apply data edge frame
    one_smul := apply_zero data laws
    mul_smul first second edge := by
      change apply data edge (product data first second) = apply data (apply data edge second) first
      rw [apply_associativity data laws, product_commutativity data scalars first second] }

end Mettapedia.CategoryTheory.CartesianMonoidAction
