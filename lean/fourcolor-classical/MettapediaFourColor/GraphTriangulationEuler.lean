import MettapediaFourColor.GraphDiskEuler
import MettapediaFourColor.ExceptionalOverlap

/-! # Euler balance of a connected spherical triangulation

The mirrored dual turns all triangular faces into cubic vertices. The
Gonthier/Emery cubic Euler formula then counts the actual graph darts.
-/

namespace FourColor.GraphTriangulationEuler

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open Mettapedia.GraphTheory.Hypermap.Reference
open SimpleGraphBridge PlanarGraphBoundaryClosure

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem covered [Nontrivial V] (conn : G.Connected) :
    Function.Surjective (fun d : G.Dart => d.fst) := by
  intro v
  obtain ⟨w, h⟩ := conn.preconnected.exists_adj_of_nontrivial v
  exact ⟨⟨(v,w),h⟩, rfl⟩

theorem planar_iff_balance (data : Data G) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) (vertices : Function.Surjective (fun d : G.Dart => d.fst))
    (tri : ExceptionalOverlap.Triangular data) :
    (rotationHypermap data).Planar ↔ 6 * Nat.card V = Nat.card G.Dart + 12 := by
  let H := rotationHypermap data
  have plain : H.Plain := ⟨fun d => d.symm_symm, fun d => d.symm_ne⟩
  have vp : (view H).Plain :=
    (Hypermap.plain_mirror _).mpr ((Hypermap.plain_dual _).mpr plain)
  have vc : (view H).Cubic := by
    constructor
    · intro d _
      exact tri d
    · intro d _
      exact face_ne H (rotationHypermap_edge data) (rotationHypermap_node_fst data) d
  have connected : (view H).Connected := by
    simpa only [view, Hypermap.connected_mirror, Hypermap.connected_dual]
      using GraphDiskEuler.connected data cyclic conn
  have eq := Hypermap.cubic_Euler vp vc connected
  have count : cycleCount H.node = Nat.card V := GraphDiskEuler.node_count data cyclic vertices
  simpa only [view, Hypermap.planar_mirror, Hypermap.planar_dual,
    Hypermap.mirror_face, Hypermap.dual_face, inv_inv, count] using eq

theorem balance (data : Data G) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) (vertices : Function.Surjective (fun d : G.Dart => d.fst))
    (tri : ExceptionalOverlap.Triangular data)
    (planar : (rotationHypermap data).Planar) :
    6 * Nat.card V = Nat.card G.Dart + 12 :=
  (planar_iff_balance data cyclic conn vertices tri).mp planar

end
end FourColor.GraphTriangulationEuler
