import Mettapedia.GraphTheory.FourColor.DualTruncateInverseRoundTrip
import Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample

/-!
# Recognition and reconstruction on the actual cube expansion

Actual square faces provide the target's unique marked corners. The inverse
recovers an eight-vertex source from the twenty-four-vertex target. Source
geometry is derived from the target; source colours are supplied by the
existing coupled cut argument and transported through the exact round trip.
The inverse adapter is consumed by target colouring and every complete GSLT
sweep, rather than reusing a previously proved target colouring.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateInverseExample

open DualTruncateColoring DualTruncateInverse
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev original := DualTruncateGeometryExample.source
abbrev target := rotation original

/-- The observation refers only to actual target faces. -/
def squareMarked (face : OrbitFace target) : Prop :=
  (orbitFaceDarts target face).card = 4

theorem square_marked_iff (x : target.D) :
    squareMarked (dartOrbitFace target x) ↔ x.2 = 2 := by
  rcases x with ⟨v, i⟩
  simp only [squareMarked, orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
  fin_cases i
  · change (target.faceOrbit (v, 0)).card = 4 ↔ (0 : Fin 3) = 2
    rw [DualTruncateFaceGeometry.vertex_face_length original
      DualTruncateGeometryExample.source_cubic DualTruncateGeometryExample.source_rotationCyclic]
    decide
  · change (target.faceOrbit (v, 1)).card = 4 ↔ (1 : Fin 3) = 2
    rw [DualTruncateFaceGeometry.vertex_face_length_one original
      DualTruncateGeometryExample.source_cubic DualTruncateGeometryExample.source_rotationCyclic]
    decide
  · change (target.faceOrbit (v, 2)).card = 4 ↔ (2 : Fin 3) = 2
    rw [DualTruncateFaceGeometry.faceOrbit_two_card original
      DualTruncateGeometryExample.source_rotationCyclic,
      DualTruncateGeometryExample.source_face_length]
    decide

def cover : DualTruncateFaceCoverFrame.Cover target where
  marked := squareMarked
  unique v := by
    refine ⟨(v, 2), ⟨rfl, (square_marked_iff _).mpr rfl⟩, ?_⟩
    rintro ⟨w, i⟩ ⟨hv, hm⟩
    change w = v at hv
    exact Prod.ext hv ((square_marked_iff _).mp hm)

theorem cover_eq : cover = DualTruncateInverseRoundTrip.cover original
    DualTruncateGeometryExample.source_cubic
    DualTruncateGeometryExample.source_rotationCyclic := by
  have hm : squareMarked = DualTruncateInverseRoundTrip.marked original
      DualTruncateGeometryExample.source_cubic
      DualTruncateGeometryExample.source_rotationCyclic := by
    funext face
    obtain ⟨x, rfl⟩ := exists_dartOrbitFace_eq target face
    exact propext ((square_marked_iff x).trans
      (DualTruncateInverseRoundTrip.marked_iff original
        DualTruncateGeometryExample.source_cubic
        DualTruncateGeometryExample.source_rotationCyclic x).symm)
  unfold cover DualTruncateInverseRoundTrip.cover
  simp only [hm]

def data : Data target := DualTruncateInverse.fromCover target (cubic original)
  (DualTruncateConstructionGSLT.rotationCyclic original) cover

theorem data_eq : data = DualTruncateInverseRoundTrip.data original
    DualTruncateGeometryExample.source_cubic
    DualTruncateGeometryExample.source_rotationCyclic := by
  unfold data
  rw [cover_eq]
  exact DualTruncateInverseRoundTrip.fromCover_data original
    DualTruncateGeometryExample.source_cubic DualTruncateGeometryExample.source_rotationCyclic

abbrev recovered := source target data (DualTruncateFaceGeometry.facesTwoSided original)

theorem unmarked_hexagons (x : target.D)
    (hm : ¬data.marked (dartOrbitFace target x)) : (target.faceOrbit x).card = 6 := by
  rw [data_eq] at hm
  exact DualTruncateInverseRoundTrip.unmarked_hexagons original
    DualTruncateGeometryExample.source_cubic DualTruncateGeometryExample.source_rotationCyclic x hm

theorem recovered_spherical : OrbitSphericalCubicMapData recovered :=
  DualTruncateInverseGeometry.source_spherical target data
    (DualTruncateFaceGeometry.facesTwoSided original) unmarked_hexagons
    DualTruncateGeometryExample.target_mapClass.spherical

theorem recovered_connected : (rotationPrimalGraph recovered).Connected :=
  DualTruncateInverseGeometry.source_connected target data
    (DualTruncateFaceGeometry.facesTwoSided original)
    DualTruncateGeometryExample.target_mapClass.primalConnected

theorem recovered_vertex_count : Fintype.card (SourceVertex target data) = 8 := by
  have hs := DualTruncateInverseGeometry.source_size target data
    (DualTruncateFaceGeometry.facesTwoSided original) unmarked_hexagons
  have ht : Fintype.card original.D = 24 := by decide +kernel
  omega

theorem recovered_edge_count : Fintype.card (SourceEdge target data) = 12 := by
  have hd := recovered.card_darts_eq_twice_card_edges
  have ht : Fintype.card recovered.D = 24 := by decide +kernel
  omega

theorem recovered_face_count : Fintype.card (OrbitFace recovered) = 6 := by
  have he := recovered_spherical.euler
  rw [recovered_vertex_count, recovered_edge_count] at he
  omega

/-- No source colour word is stored. The shared witness is transported into
the source which recognition actually constructed. -/
theorem recovered_colouring : Nonempty (ThreeVertexColoring recovered) := by
  obtain ⟨c⟩ := DualTruncateCyclicSource.source original
    DualTruncateCyclicSourceExample.regular DualTruncateCyclicSourceExample.cyclic_four
    DualTruncateCyclicSourceExample.connected DualTruncateCyclicSourceExample.noncomplete
  unfold recovered
  rw [data_eq]
  exact ⟨DualTruncateInverseRoundTrip.colouring original
    DualTruncateGeometryExample.source_cubic DualTruncateGeometryExample.source_rotationCyclic c⟩

theorem recognized_coloured_target :
    OrbitSphericalCubicMapData recovered ∧
      (rotationPrimalGraph recovered).Connected ∧
      Fintype.card (SourceVertex target data) < Fintype.card original.D ∧
      RotationSystemTaitColorable target := by
  obtain ⟨c⟩ := recovered_colouring
  exact ⟨recovered_spherical, recovered_connected,
    DualTruncateInverseGeometry.source_strictly_smaller target data
      (DualTruncateFaceGeometry.facesTwoSided original) unmarked_hexagons,
    DualTruncateInverseGeometry.tait target data
      (DualTruncateFaceGeometry.facesTwoSided original) c⟩

theorem every_complete_sweep (order : List original.D) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic original)
        (DualTruncateConstructionGSLT.rotationCyclic original) order hn he hcover).trace)
      Fin.elim0 Fin.elim0 := by
  obtain ⟨c⟩ := recovered_colouring
  exact DualTruncateInverseGeometry.every_complete_sweep target data
    (DualTruncateFaceGeometry.facesTwoSided original) c order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.DualTruncateInverseExample
