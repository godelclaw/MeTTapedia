import Mettapedia.GraphTheory.FourColor.DualTruncateMapGeometry
import Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSourceExample

/-! The cube supplies actual source geometry. The uniform face law derives
the expanded target's spherical map class, face count and colouring. -/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample

open DualTruncateColoring DualTruncateFaceGeometry DualTruncateMapGeometry
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
abbrev source := DualTruncateCoupledExample.source

theorem source_cubic : source.IsCubic :=
  DualTruncateCoupledExample.code.cubic DualTruncateCoupledExample.valid

theorem source_rotationCyclic : VertexRotationCyclic source := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  change v = w at h
  subst w
  have h01 : source.rho.SameCycle (v, 0) (v, 1) :=
    ⟨1, by simp [CubicRotationByteCertificate.Code.rho]⟩
  have h12 : source.rho.SameCycle (v, 1) (v, 2) :=
    ⟨1, by simp [CubicRotationByteCertificate.Code.rho]⟩
  have h02 := h01.trans h12
  fin_cases i <;> fin_cases j <;>
    first
    | exact Equiv.Perm.SameCycle.refl _ _
    | exact h01
    | exact h12
    | exact h02
    | exact h01.symm
    | exact h12.symm
    | exact h02.symm

theorem source_face_count : Fintype.card (OrbitFace source) = 6 := by
  change Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid source.phi)) = 6
  rw [card_permOrbit_eq_card_partition_parts]
  decide +kernel

theorem source_spherical : OrbitSphericalCubicMapData source where
  cubic := source_cubic
  euler := by rw [source_face_count]; decide +kernel

/-- Actual target geometry is supplied by the general face law and walk lift. -/
theorem target_mapClass : BridgelessSphericalCubicMapData (rotation source) :=
  mapClass_of source source_spherical DualTruncateCyclicSourceExample.connected
    source_rotationCyclic

theorem target_face_count : Fintype.card (OrbitFace (rotation source)) = 14 := by
  rw [face_count source source_cubic source_rotationCyclic, source_face_count]
  decide +kernel

theorem source_face_length (d : source.D) : (source.faceOrbit d).card = 4 := by
  fin_cases d <;> decide +kernel

/-- The two face kinds are reconstructed uniformly: squares from source
faces and hexagons from source vertices. -/
theorem target_face_lengths (d : source.D) :
    ((rotation source).faceOrbit (d, 0)).card = 6 ∧
    ((rotation source).faceOrbit (d, 2)).card = 4 := by
  exact ⟨vertex_face_length source source_cubic source_rotationCyclic d,
    (faceOrbit_two_card source source_rotationCyclic d).trans (source_face_length d)⟩

theorem target_coloured_geometry :
    BridgelessSphericalCubicMapData (rotation source) ∧
      RotationSystemTaitColorable (rotation source) :=
  ⟨target_mapClass, DualTruncateCyclicSourceExample.target_tait⟩

end
end Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample
