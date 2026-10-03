import MettapediaFourColor.ThreeBlockExteriorPlanar
import MettapediaFourColor.ThreeBlockDiskBoundaryExample

/-! # The source cone consumes the uniform deletion geometry

The checked 19-vertex ambient triangulation has 102 darts. The uniform
theorems supply its connected planar 12-vertex exterior with 44 darts,
the ordered eleven-port boundary and triangular remaining faces.
-/

namespace FourColor.ThreeBlockDiskBoundary.Example

open SimpleGraph KempeBoundarySplit

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem connected : graph.Connected := by
  have ports : ∀ j : Fin 11, graph.Adj 18 (j.castAdd 8) := by decide +kernel
  have routes : ∀ v : Fin 19, v ≠ 18 → ∃ j : Fin 11,
      v = j.castAdd 8 ∨ graph.Adj (j.castAdd 8) v := by decide +kernel
  apply (connected_iff_exists_forall_reachable (G := graph)).mpr
  refine ⟨18, fun v => ?_⟩
  by_cases hv : v = 18
  · subst v; exact .refl _
  obtain ⟨j, hj | hj⟩ := routes v hv
  · subst v; exact (ports j).reachable
  · exact (ports j).reachable.trans hj.reachable

theorem dart_count : Nat.card graph.Dart = 102 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar := by
  apply (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
  rw [Nat.card_fin, dart_count]

theorem deleted_planar :
    (SimpleGraphBridge.rotationHypermap (outsideRotation reading)).Planar :=
  outside_planar reading triangular cyclic connected planar

theorem deleted_triangles (d : (graph.induce (keep reading)).Dart)
    (hd : d ∉ outsideRing reading) :
    (outsideRotation reading).toRotationSystem.phi
      ((outsideRotation reading).toRotationSystem.phi
        ((outsideRotation reading).toRotationSystem.phi d)) = d :=
  outside_triangular reading triangular cyclic d hd

theorem deleted_vertices : Fintype.card (keep reading) = 12 := by
  have h := deleted_count reading triangular
  rw [Fintype.card_fin] at h
  omega

theorem deleted_darts : Nat.card (graph.induce (keep reading)).Dart = 44 := by
  have h := deletion_dart_count reading cyclic
  rw [dart_count] at h
  omega

theorem closed : KempeClosed
    (GraphTrace (graph.induce (keep reading)) ((List.finRange 11).map (port reading))) :=
  exterior_closed reading triangular cyclic connected planar

end FourColor.ThreeBlockDiskBoundary.Example
