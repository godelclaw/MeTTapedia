import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierWeightedCurvature
import Mettapedia.GraphTheory.FourColor.GoertzelV24WeightedOrbitFaceCorridor

/-!
# Weighted clean corridors for annular frontiers

This is the annular, source-facing L1 extraction layer for Addendum XXV.
The exact weighted balance supplies the finite defect and face-size bounds;
the generic facial-dual extractor then produces a radius-one clean hexagonal
block.  The negative-curvature weight remains explicit, because signed excess
alone cannot erase it.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierWeightedCorridor

open GoertzelV24AnnularFrontierExcess.AnnularFrontierEmbeddingExcess
open GoertzelV24AnnularFrontierWeightedCurvature.AnnularFrontier
open GoertzelV24BulkCorridor
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexPathExtraction
open GoertzelV24WeightedOrbitFaceCorridor
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

variable {data : AnnularBoundaryData G outerCount}

/-- The weighted L1 threshold for one literal annular frontier. -/
def weightedCleanHexBlockThreshold
    (embedded : ClosedWebAnnularEmbedding data) (blockLength : Nat) : Nat :=
  let weight := interiorNegativeCurvatureWeight embedded
  let rho := boundarySurplus embedded
  (weight + 7) ^
    ((((2 * weight + rho) * (weight + 7) + 1) * blockLength) - 1)

/-- A radius-one clean hexagonal geodesic block in the internal face dual of
the source annular frontier. -/
def HasCleanHexagonalGeodesicBlock
    (embedded : ClosedWebAnnularEmbedding data) (blockLength : Nat) : Prop :=
  ∃ start finish : AmbientFace embedded.cellulation.interiorFaces,
    ∃ path : (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).Walk start finish,
      path.IsPath ∧
        path.length =
          (interiorDualGraph
            (orbitFaceBoundary
              embedded.cellulation.rotation.toRotationSystem)
            embedded.cellulation.interiorFaces).dist start finish ∧
        ((2 * interiorNegativeCurvatureWeight embedded +
            boundarySurplus embedded) *
            (interiorNegativeCurvatureWeight embedded + 7) + 1) *
            blockLength ≤ path.length + 1 ∧
        ∃ block : Fin
            ((2 * interiorNegativeCurvatureWeight embedded +
              boundarySurplus embedded) *
              (interiorNegativeCurvatureWeight embedded + 7) + 1),
          ∀ offset : Fin blockLength,
            (orbitFaceBoundary
              embedded.cellulation.rotation.toRotationSystem
              (path.getVert
                (corridorBlockIndex
                  (defectBudget :=
                    (2 * interiorNegativeCurvatureWeight embedded +
                      boundarySurplus embedded) *
                      (interiorNegativeCurvatureWeight embedded + 7))
                  block offset).val).1).card = 6 ∧
            ∀ neighbor : AmbientFace embedded.cellulation.interiorFaces,
              (interiorDualGraph
                (orbitFaceBoundary
                  embedded.cellulation.rotation.toRotationSystem)
                embedded.cellulation.interiorFaces).Adj
                  (path.getVert
                    (corridorBlockIndex
                      (defectBudget :=
                        (2 * interiorNegativeCurvatureWeight embedded +
                          boundarySurplus embedded) *
                          (interiorNegativeCurvatureWeight embedded + 7))
                      block offset).val)
                  neighbor →
                (orbitFaceBoundary
                  embedded.cellulation.rotation.toRotationSystem
                  neighbor.1).card = 6

/-- Weighted source-frontier L1.  Once its actual negative-curvature weight
is accounted for, a sufficiently large annular frontier contains the clean
hexagonal block consumed by the corridor and profile machinery. -/
theorem exists_cleanHexagonalGeodesicBlock_of_weightedAnnularExcess
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded)
    (blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge : weightedCleanHexBlockThreshold embedded blockLength <
      embedded.cellulation.interiorFaces.card) :
    HasCleanHexagonalGeodesicBlock embedded blockLength := by
  let weight := interiorNegativeCurvatureWeight embedded
  let rho := boundarySurplus embedded
  have hfaceSize : ∀ face ∈ embedded.cellulation.interiorFaces,
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card ≤ weight + 6 := by
    intro face hface
    exact internalFaceBoundary_card_le_weight_add_six embedded hface
  have hdefects :
      (faceDefectSet
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).card ≤ 2 * weight + rho := by
    simpa [faceDefectSet, interiorFaceDefectSet] using
      card_interiorFaceDefectSet_le_twiceWeight_add_boundarySurplus
        embedded hdata geometry
  have hlarge' :
      ((weight + 6) + 1) ^
          ((((2 * weight + rho) * ((weight + 6) + 1) + 1) *
            blockLength) - 1) < embedded.cellulation.interiorFaces.card := by
    simpa [weightedCleanHexBlockThreshold, weight, rho, Nat.add_assoc]
      using hlarge
  simpa [HasCleanHexagonalGeodesicBlock, weight, rho, Nat.add_assoc] using
    (connectedBoundedFaceDual_exists_cleanHexagonalGeodesicBlock
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces (internalFace_incidence_le_two embedded)
      (weight + 6) hfaceSize geometry.internalDualConnected
      (2 * weight + rho) blockLength hpositive hdefects hlarge')

/-- A uniform coarse threshold in any proposed negative-curvature bound.
The actual boundary surplus is retained because it is a literal part of the
source annular instance. -/
def boundedWeightCleanHexBlockThreshold
    (embedded : ClosedWebAnnularEmbedding data)
    (weightBound blockLength : Nat) : Nat :=
  let rho := boundarySurplus embedded
  (weightBound + 7) ^
    ((((2 * weightBound + rho) * (weightBound + 7) + 1) * blockLength) - 1)

/-- Honest L1 dichotomy at a chosen negative-curvature bound.  The first
branch is not hidden: controlling it is exactly the remaining structural
work needed to make the source's threshold uniform. -/
theorem weight_exceeds_bound_or_hasCleanHexagonalGeodesicBlock
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded)
    (weightBound blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge :
      boundedWeightCleanHexBlockThreshold embedded weightBound blockLength <
        embedded.cellulation.interiorFaces.card) :
    weightBound < interiorNegativeCurvatureWeight embedded ∨
      HasCleanHexagonalGeodesicBlock embedded blockLength := by
  let weight := interiorNegativeCurvatureWeight embedded
  let rho := boundarySurplus embedded
  by_cases hweight : weight ≤ weightBound
  · right
    have hbase : weight + 7 ≤ weightBound + 7 := by omega
    have hbudget : 2 * weight + rho ≤ 2 * weightBound + rho := by omega
    have hproduct :
        (2 * weight + rho) * (weight + 7) ≤
          (2 * weightBound + rho) * (weightBound + 7) :=
      Nat.mul_le_mul hbudget hbase
    have hpreExponent :
        ((2 * weight + rho) * (weight + 7) + 1) * blockLength ≤
          ((2 * weightBound + rho) * (weightBound + 7) + 1) *
            blockLength :=
      Nat.mul_le_mul_right blockLength (Nat.add_le_add_right hproduct 1)
    let leftExponent :=
      (((2 * weight + rho) * (weight + 7) + 1) * blockLength) - 1
    let rightExponent :=
      (((2 * weightBound + rho) * (weightBound + 7) + 1) * blockLength) - 1
    have hexponent : leftExponent ≤ rightExponent := by
      dsimp [leftExponent, rightExponent]
      exact Nat.sub_le_sub_right hpreExponent 1
    have hthreshold :
        (weight + 7) ^ leftExponent ≤
          (weightBound + 7) ^ rightExponent := by
      calc
        (weight + 7) ^ leftExponent ≤
            (weightBound + 7) ^ leftExponent :=
          Nat.pow_le_pow_left hbase leftExponent
        _ ≤ (weightBound + 7) ^ rightExponent :=
          Nat.pow_le_pow_right (by omega) hexponent
    apply exists_cleanHexagonalGeodesicBlock_of_weightedAnnularExcess
      embedded hdata geometry blockLength hpositive
    exact lt_of_le_of_lt
      (by simpa [weightedCleanHexBlockThreshold,
          boundedWeightCleanHexBlockThreshold, weight, rho,
          leftExponent, rightExponent]
        using hthreshold)
      hlarge
  · left
    simpa [weight] using (Nat.lt_of_not_ge hweight)

end

end GoertzelV24AnnularFrontierWeightedCorridor

end Mettapedia.GraphTheory.FourColor
