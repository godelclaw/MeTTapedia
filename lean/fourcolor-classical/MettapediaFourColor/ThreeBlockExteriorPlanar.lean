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

theorem outside_planar : (SimpleGraphBridge.rotationHypermap (outsideRotation r)).Planar := by
  classical
  letI : Nontrivial V := ⟨⟨r.hom 0, r.hom 1,
    fun h => (by decide : (0 : Fin 18) ≠ 1) (r.injective h)⟩⟩
  letI : Nontrivial (keep r) := ⟨⟨port r 0, port r 1,
    fun h => (by decide : (0 : Fin 11) ≠ 1) (port_injective r h)⟩⟩
  have connected := outside_connected r cyclic conn
  have counts := GraphTriangulationEuler.balance data cyclic conn
    (GraphTriangulationEuler.covered conn) tri ambient
  have vc : Nat.card V = Nat.card (keep r) + 7 := by
    simpa only [Nat.card_eq_fintype_card] using deleted_count r tri
  have dc := deletion_dart_count r cyclic
  have len : (outsideRing r).length = 11 := List.length_ofFn
  apply GraphDiskEuler.planar (outsideRotation r) (outside_cyclic r cyclic)
    connected (GraphTriangulationEuler.covered connected) (outsideRing r)
    (by intro h; have bad := congrArg List.length h; rw [len] at bad; contradiction)
    (outside_boundary r tri) (outside_distinct r) (outside_triangular r tri cyclic)
  rw [len]
  omega

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
