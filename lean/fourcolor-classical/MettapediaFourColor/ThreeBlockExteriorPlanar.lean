import MettapediaFourColor.PatchDiskPlanar
import MettapediaFourColor.PatchDiskSources
import MettapediaFourColor.GraphTriangulationEuler
import MettapediaFourColor.ThreeBlockRemainingFaces
import MettapediaFourColor.ThreeBlockExteriorConnected
import MettapediaFourColor.ThreeBlockDeletionCount
import MettapediaFourColor.ThreeBlockDiskReconstruction

/-! # Uniform planar exterior supply and seed reconstruction

An injective full source reading in a connected spherical triangulation
supplies the entire exterior disk contract. Deletion removes seven vertices
and 58 darts. The retained boundary connects every attachment to the core,
and every other face stays triangular. Euler balance therefore proves
planarity of the actual first-return exterior rotation.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalOverlap KempeBoundarySplit

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data) (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)
  (conn : G.Connected) (ambient : (SimpleGraphBridge.rotationHypermap data).Planar)

include tri cyclic conn ambient

theorem outside_planar : (SimpleGraphBridge.rotationHypermap (outsideRotation r)).Planar :=
  PatchDisk.Reading.outside_planar (PatchDiskSources.of_d0092 r) tri cyclic conn ambient

/-- The joint boundary relation is closed for every exterior colouring;
no seed class or successful repair is assumed here. -/
theorem exterior_closed : KempeClosed
    (GraphTrace (G.induce (keep r)) ((List.finRange 11).map (port r))) := by
  have h := PlanarGraphBoundaryClosure.rotation_closed (outsideRotation r)
    (outside_cyclic r cyclic) (outside_planar r tri cyclic conn ambient)
    (outsideRing r) (outside_boundary r tri) (outside_distinct r)
    (outside_triangular r tri cyclic)
  rw [outside_order] at h
  simpa only [List.ofFn_eq_map] using h

/-- The actual ambient embedding supplies every geometric hypothesis of the
existing seed repair. The supplied initial colouring may be repaired. -/
theorem repair_of_ambient
    (C : (G.induce (keep r)).Coloring Color)
    (initial : ∀ j, C (port r j) = ThreeBlockCore.word false false false j) :
    ∃ D : (G.induce (keep r)).Coloring Color, ∃ K : G.Coloring Color,
      ∀ w, K w.val = D w :=
  repair r tri cyclic (outside_planar r tri cyclic conn ambient)
    (outside_triangular r tri cyclic) C initial

end
end FourColor.ThreeBlockDiskBoundary
