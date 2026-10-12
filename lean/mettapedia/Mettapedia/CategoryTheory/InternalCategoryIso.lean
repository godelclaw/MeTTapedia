import Mettapedia.CategoryTheory.InternalCategoryFunctorCategory

/-!
# Internal category isomorphisms from actual invertible components

The inverse graph squares, complete matching-pair maps and inverse category
operations are derived from an actual internal functor. Invertibility of
its vertex and edge components therefore gives an isomorphism of internal
categories, including the chosen-pullback composition operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryIso

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryFunctorCategory

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {first second : InternalCategory C} (original : InternalCategory.Hom first second)
variable (vertices : first.vertex ≅ second.vertex) (edges : first.edge ≅ second.edge)
variable (vertexRead : original.vertex = vertices.hom) (edgeRead : original.edge = edges.hom)

def inverseGraph : InternalGraph.Hom second.toInternalGraph first.toInternalGraph where
  vertex := vertices.inv
  edge := edges.inv
  source := by
    apply (cancel_mono vertices.hom).mp
    calc
      _ = edges.inv ≫ (first.source ≫ vertices.hom) := Category.assoc _ _ _
      _ = edges.inv ≫ (edges.hom ≫ second.source) := by rw [← vertexRead, ← original.source, edgeRead]
      _ = second.source := Iso.inv_hom_id_assoc edges _
      _ = (second.source ≫ vertices.inv) ≫ vertices.hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  target := by
    apply (cancel_mono vertices.hom).mp
    calc
      _ = edges.inv ≫ (first.target ≫ vertices.hom) := Category.assoc _ _ _
      _ = edges.inv ≫ (edges.hom ≫ second.target) := by rw [← vertexRead, ← original.target, edgeRead]
      _ = second.target := Iso.inv_hom_id_assoc edges _
      _ = (second.target ≫ vertices.inv) ≫ vertices.hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem inverse_pair :
    (inverseGraph original vertices edges vertexRead edgeRead).composableMap ≫ original.toHom.composableMap =
      𝟙 second.toInternalGraph.Composable := by
  apply pullback.hom_ext
  · rw [Category.assoc, original.toHom.composableMap_first, ← Category.assoc,
      InternalGraph.Hom.composableMap_first, Category.assoc]
    simp only [inverseGraph, edgeRead, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, original.toHom.composableMap_second, ← Category.assoc,
      InternalGraph.Hom.composableMap_second, Category.assoc]
    simp only [inverseGraph, edgeRead, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

def inverse : InternalCategory.Hom second first where
  toHom := inverseGraph original vertices edges vertexRead edgeRead
  unit := by
    apply (cancel_mono edges.hom).mp
    change (second.unit ≫ edges.inv) ≫ edges.hom = (vertices.inv ≫ first.unit) ≫ edges.hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, ← edgeRead,
      original.unit, vertexRead, Iso.inv_hom_id_assoc]
  composition := by
    apply (cancel_mono edges.hom).mp
    change (second.composition ≫ edges.inv) ≫ edges.hom =
      ((inverseGraph original vertices edges vertexRead edgeRead).composableMap ≫ first.composition) ≫ edges.hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, ← edgeRead,
      original.composition, ← Category.assoc, inverse_pair, Category.id_comp]

def iso : first ≅ second where
  hom := original
  inv := inverse original vertices edges vertexRead edgeRead
  hom_inv_id := by
    apply map_ext
    · change original.vertex ≫ vertices.inv = 𝟙 first.vertex
      rw [vertexRead, Iso.hom_inv_id]
    · change original.edge ≫ edges.inv = 𝟙 first.edge
      rw [edgeRead, Iso.hom_inv_id]
  inv_hom_id := by
    apply map_ext
    · change vertices.inv ≫ original.vertex = 𝟙 second.vertex
      rw [vertexRead, Iso.inv_hom_id]
    · change edges.inv ≫ original.edge = 𝟙 second.edge
      rw [edgeRead, Iso.inv_hom_id]

theorem complete_vertex : (iso original vertices edges vertexRead edgeRead).hom.vertex = vertices.hom := vertexRead
theorem complete_edge : (iso original vertices edges vertexRead edgeRead).hom.edge = edges.hom := edgeRead
theorem complete_inverse_vertex : (iso original vertices edges vertexRead edgeRead).inv.vertex = vertices.inv := rfl
theorem complete_inverse_edge : (iso original vertices edges vertexRead edgeRead).inv.edge = edges.inv := rfl

end Mettapedia.CategoryTheory.InternalCategoryIso
