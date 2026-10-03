import MettapediaFourColor.ThreeBlockDiskDeletion
import MettapediaFourColor.ThreeBlockDiskStars
import MettapediaFourColor.ResidualSeedPlanarReconstruction

/-! # Reconstruction from the induced exterior with its supplied boundary

Complete cyclic core readings supply the induced exterior, its ordered
facial ring and complete core stars. The remaining geometric inputs are
planarity of that rotation and triangularity away from its boundary.
The existing compact seed repair then returns compatible actual colourings.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FiveTriangleCollapseObstruction ExceptionalOverlap

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data) (tri : Triangular data)

theorem exterior_iff (v : V) : (patch r tri).Exterior v ↔ v ∈ keep r := by
  change (∀ i : Fin 18, 11 ≤ i.val → v ≠ r.hom i) ↔
    ¬ ∃ i : Fin 18, 11 ≤ i.val ∧ r.hom i = v
  simp only [not_exists, not_and, ne_eq, eq_comm]

def exteriorReading : ThreeBlockGeometry.ExteriorReading (patch r tri) (G.induce (keep r)) where
  embedding := { toFun := Subtype.val, inj' := Subtype.val_injective, map_rel_iff' := Iff.rfl }
  outside w := (exterior_iff r tri w.val).mpr w.property
  ports := port r
  boundary _ := rfl

theorem exterior_covers : ∀ v, (patch r tri).Exterior v →
    ∃ w, (exteriorReading r tri).embedding w = v :=
  fun v hv => ⟨⟨v, (exterior_iff r tri v).mp hv⟩, rfl⟩

include tri

/-- This operation deletes seven vertices and introduces none. -/
theorem deleted_count : Fintype.card V = Fintype.card (keep r) + 7 :=
  (exteriorReading r tri).exact_decrease (exterior_covers r tri)

/-- The source reading discharges boundary order, boundary distinctness,
vertex cycles and complete-star hypotheses of the planar repair consumer.
Planarity, the remaining faces and the seed colouring are still explicit. -/
theorem repair
    (cyclic : data.IsVertexwiseCyclic)
    (planar : (SimpleGraphBridge.rotationHypermap (outsideRotation r)).Planar)
    (triangles : ∀ d, d ∉ outsideRing r → (outsideRotation r).toRotationSystem.phi
      ((outsideRotation r).toRotationSystem.phi
        ((outsideRotation r).toRotationSystem.phi d)) = d)
    (C : (G.induce (keep r)).Coloring Color)
    (initial : ∀ j, C (port r j) = ThreeBlockCore.word false false false j) :
    ∃ D : (G.induce (keep r)).Coloring Color, ∃ K : G.Coloring Color,
      ∀ w, K w.val = D w := by
  exact ResidualSeedRepairCertificate.whole_repair_of_planar_disk
    (exteriorReading r tri) (exterior_covers r tri) (core_stars r cyclic)
    (outsideRotation r) (outside_cyclic r cyclic) planar
    (outsideRing r) (outside_boundary r tri) (outside_distinct r) triangles
    (by
      change (outsideRing r).map (fun d => d.fst) = (List.finRange 11).map (port r)
      simpa only [List.ofFn_eq_map] using outside_order r) C initial

end
end FourColor.ThreeBlockDiskBoundary
