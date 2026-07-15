import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpace
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceCycleSpaceEquality

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The all-face boundary map is the finite linear combination of the scalar
indicators of the individual quotient facial boundaries. -/
theorem orbitFaceBoundaryLinearMap_eq_sum_indicators
    (data : Data G)
    (coefficients : OrbitFace data.toRotationSystem → F2) :
    orbitFaceBoundaryLinearMap data.toRotationSystem coefficients =
      ∑ face : OrbitFace data.toRotationSystem,
        coefficients face • orbitFaceBoundaryIndicator data face := by
  funext edge
  simp only [orbitFaceBoundaryLinearMap_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro face _
  by_cases hedge : edge ∈ orbitFaceBoundary data.toRotationSystem face <;>
    simp [orbitFaceBoundaryIndicator, hedge]

/-- Every linear combination of two-sided quotient facial boundaries is a
genuine graph cycle over `F2`. -/
theorem range_orbitFaceBoundaryLinearMap_le_f2CycleSpace
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem) :
    LinearMap.range (orbitFaceBoundaryLinearMap data.toRotationSystem) ≤
      f2CycleSpace G := by
  rintro vector ⟨coefficients, rfl⟩
  rw [orbitFaceBoundaryLinearMap_eq_sum_indicators]
  exact Submodule.sum_mem _ fun face _ =>
    Submodule.smul_mem _ _
      (orbitFaceBoundaryIndicator_mem_f2CycleSpace data htwoSided face)

/-- Spherical Euler arithmetic identifies the expected facial-boundary rank
with the connected graph cycle-space rank. -/
theorem orbitSphere_faceRank_eq_cycleRank
    (data : Data G) (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem) :
    Fintype.card (OrbitFace data.toRotationSystem) - 1 =
      Fintype.card G.edgeSet - (Fintype.card V - 1) := by
  have hvertices : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr hconnected.nonempty
  have heuler := hsphere.euler
  omega

/-- On a connected cellular sphere graph with two-sided faces and connected
facial dual, the quotient facial boundaries span the entire `F2` cycle space. -/
theorem range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem) :
    LinearMap.range (orbitFaceBoundaryLinearMap data.toRotationSystem) =
      f2CycleSpace G := by
  apply Submodule.eq_of_le_of_finrank_eq
    (range_orbitFaceBoundaryLinearMap_le_f2CycleSpace data htwoSided)
  rw [finrank_range_orbitFaceBoundaryLinearMap
      data.toRotationSystem htwoSided hdual,
    finrank_f2CycleSpace_eq G hconnected]
  exact orbitSphere_faceRank_eq_cycleRank data hconnected hsphere

end

end GoertzelV24OrbitFaceCycleSpaceEquality

end Mettapedia.GraphTheory.FourColor
