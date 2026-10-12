import Mettapedia.CategoryTheory.CartesianMonoidAction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Canonical transport of complete cartesian action diagrams

A finite-product-preserving functor transports both scalar and edge arrows
using its actual terminal and product comparisons. The complete unit and
associativity diagrams commute with these choices. Thus local satisfaction
of the original two diagrams is equivalent to the action laws on the
independently chosen target products.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.CartesianMonoidAction

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits (PreservesFiniteProducts)
open MonoidalCategory CartesianMonoidalCategory

universe u v w z

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D]
variable (F : C ⥤ D) [PreservesFiniteProducts F] (data : Data C)

abbrev map : Data D where
  edge := F.obj data.edge
  scalar := F.obj data.scalar
  zero := inv (terminalComparison F) ≫ F.map data.zero
  merge := inv (prodComparison F data.scalar data.scalar) ≫ F.map data.merge
  act := inv (prodComparison F data.edge data.scalar) ≫ F.map data.act

theorem map_pair {Z X Y : C} (first : Z ⟶ X) (second : Z ⟶ Y) :
    F.map (lift first second) =
      lift (F.map first) (F.map second) ≫ inv (prodComparison F X Y) := by
  apply (cancel_mono (prodComparison F X Y)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, prodComparison_fst, ← F.map_comp, lift_fst]
  · simp only [Category.assoc, prodComparison_snd, ← F.map_comp, lift_snd]

theorem map_toUnit (Z : C) :
    F.map (toUnit Z) = toUnit (F.obj Z) ≫ inv (terminalComparison F) := by
  apply (cancel_mono (terminalComparison F)).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact map_toUnit_comp_terminalComparison F Z

theorem map_apply {Z : C} (edge : Z ⟶ data.edge) (frame : Z ⟶ data.scalar) :
    apply (map F data) (F.map edge) (F.map frame) = F.map (apply data edge frame) := by
  simp only [apply, map, F.map_comp, map_pair, Category.assoc]

theorem map_product {Z : C} (first second : Z ⟶ data.scalar) :
    product (map F data) (F.map first) (F.map second) = F.map (product data first second) := by
  simp only [product, map, F.map_comp, map_pair, Category.assoc]

theorem map_neutral (Z : C) : neutral (map F data) (F.obj Z) = F.map (neutral data Z) := by
  simp only [neutral, map, F.map_comp, map_toUnit, Category.assoc]

theorem unit_readout : unitDiagram (map F data) = F.map (unitDiagram data) := by
  change apply (map F data) (𝟙 (F.obj data.edge)) (neutral (map F data) (F.obj data.edge)) = _
  rw [map_neutral, ← F.map_id data.edge, map_apply]
  rfl

def tripleComparison : F.obj ((data.edge ⊗ data.scalar) ⊗ data.scalar) ⟶
    (F.obj data.edge ⊗ F.obj data.scalar) ⊗ F.obj data.scalar :=
  prodComparison F (data.edge ⊗ data.scalar) data.scalar ≫
    (prodComparison F data.edge data.scalar ⊗ₘ 𝟙 (F.obj data.scalar))

instance tripleComparison_isIso : IsIso (tripleComparison F data) := by
  unfold tripleComparison
  infer_instance

omit [PreservesFiniteProducts F] in
theorem triple_edge : tripleComparison F data ≫ fst _ _ ≫ fst _ _ =
    F.map (fst (data.edge ⊗ data.scalar) data.scalar ≫ fst data.edge data.scalar) := by
  simp only [tripleComparison, Category.assoc]
  rw [tensorHom_fst_assoc, prodComparison_fst, prodComparison_fst_assoc, ← F.map_comp]

omit [PreservesFiniteProducts F] in
theorem triple_first : tripleComparison F data ≫ fst _ _ ≫ snd _ _ =
    F.map (fst (data.edge ⊗ data.scalar) data.scalar ≫ snd data.edge data.scalar) := by
  simp only [tripleComparison, Category.assoc]
  rw [tensorHom_fst_assoc, prodComparison_snd, prodComparison_fst_assoc, ← F.map_comp]

omit [PreservesFiniteProducts F] in
theorem triple_second : tripleComparison F data ≫ snd _ _ =
    F.map (snd (data.edge ⊗ data.scalar) data.scalar) := by
  simp only [tripleComparison, Category.assoc, tensorHom_snd,
    Category.comp_id, prodComparison_snd]

theorem twice_readout : tripleComparison F data ≫ twiceDiagram (map F data) =
    F.map (twiceDiagram data) := by
  simp only [twiceDiagram, apply_precompose]
  rw [triple_edge, triple_first, triple_second, map_apply, map_apply]

theorem merged_readout : tripleComparison F data ≫ mergedDiagram (map F data) =
    F.map (mergedDiagram data) := by
  simp only [mergedDiagram, apply_precompose, product_precompose]
  rw [triple_edge, triple_first, triple_second, map_product, map_apply]

theorem mapped_laws_iff : Laws (map F data) ↔
    F.map (unitDiagram data) = 𝟙 (F.obj data.edge) ∧
      F.map (twiceDiagram data) = F.map (mergedDiagram data) := by
  constructor
  · intro laws
    refine ⟨(unit_readout F data).symm.trans laws.unit, ?_⟩
    rw [← twice_readout, ← merged_readout, laws.associativity]
  · rintro ⟨unit, associativity⟩
    refine ⟨(unit_readout F data).trans unit, ?_⟩
    apply (cancel_epi (tripleComparison F data)).mp
    rw [twice_readout, merged_readout, associativity]

theorem map_laws (laws : Laws data) : Laws (map F data) := by
  apply (mapped_laws_iff F data).mpr
  exact ⟨by rw [laws.unit, F.map_id], congrArg F.map laws.associativity⟩

theorem map_scalar_laws (laws : ScalarLaws data) : ScalarLaws (map F data) := by
  let regular : Data C := ⟨data.scalar, data.scalar, data.zero, data.merge, data.merge⟩
  have regularLaws : Laws regular := ⟨laws.unit, laws.associativity⟩
  have mapped := map_laws F regular regularLaws
  refine ⟨mapped.unit, mapped.associativity, ?_⟩
  change inv (prodComparison F data.scalar data.scalar) ≫ F.map data.merge =
    lift (snd _ _) (fst _ _) ≫ inv (prodComparison F data.scalar data.scalar) ≫ F.map data.merge
  apply (cancel_epi (prodComparison F data.scalar data.scalar)).mp
  simp only [IsIso.hom_inv_id_assoc, comp_lift_assoc, prodComparison_snd, prodComparison_fst]
  rw [← Category.assoc, ← map_pair, ← F.map_comp, ← laws.commutativity]

end Mettapedia.CategoryTheory.CartesianMonoidAction
