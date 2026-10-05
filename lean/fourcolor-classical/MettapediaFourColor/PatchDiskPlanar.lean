import MettapediaFourColor.PatchDiskRemaining
import MettapediaFourColor.PatchDiskCount
import MettapediaFourColor.GraphTriangulationEuler

/-! # Planar exterior supplied by the common core-deletion law

The actual induced graph has the retained cyclic boundary and triangular
remaining faces. Exact vertex and dart counts transport ambient Euler
balance to the disk balance. The reference Euler theorem then proves
planarity of the first-return exterior rotation. No exterior planarity or
Kempe closure is assumed.
-/

namespace FourColor.PatchDisk.Reading

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalOverlap KempeBoundarySplit

noncomputable section

variable {c b : ℕ} [NeZero b] {s : Source c b}
  {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading s data) (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)
  (conn : G.Connected) (ambient : (SimpleGraphBridge.rotationHypermap data).Planar)

include tri cyclic conn ambient

theorem outside_planar : (SimpleGraphBridge.rotationHypermap (outsideRotation r)).Planar := by
  classical
  let : Nontrivial V := ⟨⟨(port r 0).val, (port r (0 + 1)).val,
    fun h => (boundaryDart r 0).adj.ne (Subtype.ext h)⟩⟩
  let : Nontrivial (keep r) := ⟨⟨port r 0, port r (0 + 1), (boundaryDart r 0).adj.ne⟩⟩
  have connected := outside_connected r cyclic conn
  have counts := GraphTriangulationEuler.balance data cyclic conn
    (GraphTriangulationEuler.covered conn) tri ambient
  have vc := deletion_vertex_count r
  have dc := deletion_dart_count r cyclic
  have len : (outsideRing r).length = b := List.length_ofFn
  apply GraphDiskEuler.planar (outsideRotation r) (outside_cyclic r cyclic)
    connected (GraphTriangulationEuler.covered connected) (outsideRing r)
    (by intro h; have bad := congrArg List.length h; rw [len] at bad
        have := s.boundary_size; simp only [List.length_nil] at bad; omega)
    (outside_boundary r tri) (outside_distinct r tri) (outside_triangular r tri cyclic)
  rw [len]
  omega

/-- Every exterior colouring belongs to the same Kempe-closed boundary
relation; this follows from the ambient geometry and the source contract. -/
theorem exterior_closed : KempeClosed
    (GraphTrace (G.induce (keep r)) (List.ofFn (port r))) := by
  have h := PlanarGraphBoundaryClosure.rotation_closed (outsideRotation r)
    (outside_cyclic r cyclic) (outside_planar r tri cyclic conn ambient)
    (outsideRing r) (outside_boundary r tri) (outside_distinct r tri)
    (outside_triangular r tri cyclic)
  rw [outside_order] at h
  exact h

end
end FourColor.PatchDisk.Reading
