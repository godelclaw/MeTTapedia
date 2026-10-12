import Mettapedia.CategoryTheory.InternalPredicateFunctionObject
import Mettapedia.CategoryTheory.InternalConjunctiveObjectMaps
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Complete predicate-function comparisons under closed maps

The canonical exponential comparison and the supplied proposition-object
isomorphism determine the comparison on predicate functions. Evaluation
retains the whole value and parameter context. The original truth and meet
squares then earn a conjunctive-object map on every function object.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateFunctionObjectMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject InternalPredicateFunctionObject

universe u v k

variable {C : Type u} [Category.{k} C]
variable {D : Type v} [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D]
variable {source : Operations C} {target : Operations D}
variable (mapping : InternalConjunctiveObject.Map source target)
variable [PreservesLimitsOfShape (Discrete WalkingPair) mapping.functor]
variable [MonoidalClosedFunctor mapping.functor]

def powerComparison (value : C) :
    mapping.functor.obj (power source value) ≅ power target (mapping.functor.obj value) :=
  asIso ((expComparison mapping.functor value).natTrans.app source.proposition) ≪≫
    (ihom (mapping.functor.obj value)).mapIso mapping.proposition

theorem powerComparison_read (value : C) :
    uncurry (powerComparison mapping value).hom =
      inv (CartesianMonoidalCategory.prodComparison mapping.functor value (power source value)) ≫
        mapping.functor.map ((ihom.ev value).app source.proposition) ≫ mapping.proposition.hom := by
  change uncurry (((expComparison mapping.functor value).natTrans.app source.proposition) ≫
      (ihom (mapping.functor.obj value)).map mapping.proposition.hom) = _
  rw [uncurry_natural_right, uncurry_expComparison, Category.assoc]

def sectionImage {value parameter : C} (predicate : parameter ⟶ power source value) :
    mapping.functor.obj parameter ⟶ power target (mapping.functor.obj value) :=
  mapping.functor.map predicate ≫ (powerComparison mapping value).hom

theorem sectionImage_read {value parameter : C} (predicate : parameter ⟶ power source value) :
    read target (sectionImage mapping predicate) =
      inv (CartesianMonoidalCategory.prodComparison mapping.functor value parameter) ≫
        mapping.image (read source predicate) := by
  change uncurry (mapping.functor.map predicate ≫ (powerComparison mapping value).hom) =
    inv (CartesianMonoidalCategory.prodComparison mapping.functor value parameter) ≫
      (mapping.functor.map (uncurry predicate) ≫ mapping.proposition.hom)
  rw [uncurry_natural_left, powerComparison_read]
  calc
    _ = inv (CartesianMonoidalCategory.prodComparison mapping.functor value parameter) ≫
        mapping.functor.map (value ◁ predicate) ≫
        mapping.functor.map ((ihom.ev value).app source.proposition) ≫
        mapping.proposition.hom := by
      simpa only [Category.assoc] using congrArg
        (fun arrow => arrow ≫ mapping.functor.map ((ihom.ev value).app source.proposition) ≫
          mapping.proposition.hom)
        (prodComparison_inv_natural_whiskerLeft mapping.functor (A := value) predicate).symm
    _ = _ := by simp only [uncurry_eq, Functor.map_comp, Category.assoc]

theorem sectionImage_substitution {value first second : C} (incoming : first ⟶ second)
    (predicate : second ⟶ power source value) :
    sectionImage mapping (incoming ≫ predicate) =
      mapping.functor.map incoming ≫ sectionImage mapping predicate := by
  simp only [sectionImage, Functor.map_comp, Category.assoc]

theorem sectionImage_top (value parameter : C) :
    sectionImage mapping ((operations source value).top parameter) =
      (operations target (mapping.functor.obj value)).top (mapping.functor.obj parameter) := by
  apply read_injective target
  rw [sectionImage_read, read_top, mapping.image_top, read_top]
  exact target.reindex_top (inv (CartesianMonoidalCategory.prodComparison mapping.functor value parameter))

theorem sectionImage_meet {value parameter : C}
    (first second : (operations source value).Fiber parameter) :
    sectionImage mapping ((operations source value).meet first second) =
      (operations target (mapping.functor.obj value)).meet
        (sectionImage mapping first) (sectionImage mapping second) := by
  apply read_injective target
  rw [sectionImage_read, read_meet, mapping.image_meet, read_meet,
    sectionImage_read, sectionImage_read]
  exact target.reindex_meet (inv (CartesianMonoidalCategory.prodComparison mapping.functor value parameter)) _ _

def powerMap (value : C) :
    InternalConjunctiveObject.Map (operations source value)
      (operations target (mapping.functor.obj value)) where
  functor := mapping.functor
  proposition := powerComparison mapping value
  truth := by
    have complete := sectionImage_top mapping value (𝟙_ C)
    simpa only [sectionImage, Operations.top, toUnit_unit, Category.id_comp] using complete
  conjunction := by
    have complete := sectionImage_meet mapping
      (fst (power source value) (power source value))
      (snd (power source value) (power source value))
    have original : (operations source value).meet
        (fst (power source value) (power source value))
        (snd (power source value) (power source value)) = (operations source value).conjunction := by
      change CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _)
        (CartesianMonoidalCategory.snd _ _) ≫ (operations source value).conjunction = _
      rw [CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]
    rw [original] at complete
    exact complete

theorem powerMap_image {value parameter : C} (predicate : parameter ⟶ power source value) :
    (powerMap mapping value).image predicate = sectionImage mapping predicate := rfl

def arrowImage {before after : C} (operation : power source before ⟶ power source after) :
    power target (mapping.functor.obj before) ⟶ power target (mapping.functor.obj after) :=
  (powerComparison mapping before).inv ≫ mapping.functor.map operation ≫
    (powerComparison mapping after).hom

theorem arrowImage_after {before after : C} (operation : power source before ⟶ power source after) :
    (powerComparison mapping before).hom ≫ arrowImage mapping operation =
      sectionImage mapping operation := by
  simp only [arrowImage, sectionImage, Iso.hom_inv_id_assoc]

theorem arrowImage_section {before after parameter : C}
    (predicate : parameter ⟶ power source before) (operation : power source before ⟶ power source after) :
    sectionImage mapping (predicate ≫ operation) =
      sectionImage mapping predicate ≫ arrowImage mapping operation := by
  simp only [sectionImage, arrowImage, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem arrowImage_identity (value : C) :
    arrowImage mapping (𝟙 (power source value)) = 𝟙 (power target (mapping.functor.obj value)) := by
  calc
    _ = (powerComparison mapping value).inv ≫ 𝟙 (mapping.functor.obj (power source value)) ≫
        (powerComparison mapping value).hom :=
      congrArg (fun arrow => (powerComparison mapping value).inv ≫ arrow ≫
        (powerComparison mapping value).hom) (mapping.functor.map_id (power source value))
    _ = _ := by rw [Category.id_comp, Iso.inv_hom_id]

theorem arrowImage_comp {before middle after : C}
    (first : power source before ⟶ power source middle)
    (second : power source middle ⟶ power source after) :
    arrowImage mapping (first ≫ second) = arrowImage mapping first ≫ arrowImage mapping second := by
  simp only [arrowImage, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem arrowImage_meet {before after : C}
    (first second : (operations source after).Fiber (power source before)) :
    arrowImage mapping ((operations source after).meet first second) =
      (operations target (mapping.functor.obj after)).meet
        (arrowImage mapping first) (arrowImage mapping second) := by
  apply (cancel_epi (powerComparison mapping before).hom).mp
  calc
    _ = sectionImage mapping ((operations source after).meet first second) :=
      arrowImage_after mapping _
    _ = (operations target (mapping.functor.obj after)).meet
        (sectionImage mapping first) (sectionImage mapping second) := sectionImage_meet mapping _ _
    _ = _ := by
      rw [← arrowImage_after mapping first, ← arrowImage_after mapping second]
      exact ((operations target (mapping.functor.obj after)).reindex_meet
        (powerComparison mapping before).hom _ _).symm

end Mettapedia.CategoryTheory.InternalPredicateFunctionObjectMaps
