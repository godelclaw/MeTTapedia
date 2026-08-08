import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedWeightedCurvature
import Mettapedia.GraphTheory.FourColor.GoertzelV24WeightedOrbitFaceCorridor

/-!
# Weighted clean corridors inside embedded source trails

This is the deliberately heavier geometric layer above framed weighted
curvature.  It imports the generic clean-block extractor only to convert the
exact weighted L9 budget into a radius-one clean hexagonal geodesic block.
The negative-curvature weight remains explicit; controlling its high-weight
branch is a separate obligation of the reductive proof.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BulkCorridor
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexPathExtraction
open GoertzelV24WeightedOrbitFaceCorridor
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- Weighted L1 threshold for an embedded source trail. -/
def weightedCleanHexBlockThreshold {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) (blockLength : Nat) : Nat :=
  let weight := embedded.interiorNegativeCurvatureWeight
  let rho := embedded.cellulation.boundarySurplus source.toFramedTrailData
  (weight + 7) ^
    ((((2 * weight + rho) * (weight + 7) + 1) * blockLength) - 1)

/-- The radius-one clean geodesic block produced by weighted L1.  Naming the
conclusion separately lets later reductive steps use it without repeating the
full bounded-growth witness type. -/
def HasCleanHexagonalGeodesicBlock {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) (blockLength : Nat) : Prop :=
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
        ((2 * embedded.interiorNegativeCurvatureWeight +
            embedded.cellulation.boundarySurplus source.toFramedTrailData) *
            (embedded.interiorNegativeCurvatureWeight + 7) + 1) *
            blockLength ≤ path.length + 1 ∧
        ∃ block : Fin
            ((2 * embedded.interiorNegativeCurvatureWeight +
              embedded.cellulation.boundarySurplus
                source.toFramedTrailData) *
              (embedded.interiorNegativeCurvatureWeight + 7) + 1),
          ∀ offset : Fin blockLength,
            (orbitFaceBoundary
              embedded.cellulation.rotation.toRotationSystem
              (path.getVert
                (corridorBlockIndex
                  (defectBudget :=
                    (2 * embedded.interiorNegativeCurvatureWeight +
                      embedded.cellulation.boundarySurplus
                        source.toFramedTrailData) *
                      (embedded.interiorNegativeCurvatureWeight + 7))
                  block offset).val).1).card = 6 ∧
            ∀ neighbor : AmbientFace embedded.cellulation.interiorFaces,
              (interiorDualGraph
                (orbitFaceBoundary
                  embedded.cellulation.rotation.toRotationSystem)
                embedded.cellulation.interiorFaces).Adj
                  (path.getVert
                    (corridorBlockIndex
                      (defectBudget :=
                        (2 * embedded.interiorNegativeCurvatureWeight +
                          embedded.cellulation.boundarySurplus
                            source.toFramedTrailData) *
                          (embedded.interiorNegativeCurvatureWeight + 7))
                      block offset).val)
                  neighbor →
                (orbitFaceBoundary
                  embedded.cellulation.rotation.toRotationSystem
                  neighbor.1).card = 6

/-- Weighted repair of playbook flag L1.  Above the explicit threshold, the
internal facial dual contains a geodesic block whose faces and all their dual
neighbors are hexagons.  The theorem deliberately retains `W`; L9 alone does
not justify erasing it. -/
theorem exists_cleanHexagonalGeodesicBlock_of_weightedL9
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge : embedded.weightedCleanHexBlockThreshold blockLength <
      embedded.cellulation.interiorFaces.card) :
    embedded.HasCleanHexagonalGeodesicBlock blockLength := by
  let weight := embedded.interiorNegativeCurvatureWeight
  let rho := embedded.cellulation.boundarySurplus source.toFramedTrailData
  have hfaceSize : ∀ face ∈ embedded.cellulation.interiorFaces,
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card ≤ weight + 6 := by
    intro face hface
    exact embedded.internalFaceBoundary_card_le_weight_add_six hface
  have hdefects :
      (faceDefectSet
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).card ≤ 2 * weight + rho := by
    simpa [faceDefectSet, interiorFaceDefectSet] using
      embedded.card_interiorFaceDefectSet_le_twiceWeight_add_boundarySurplus
        hsource geometry
  have hlarge' :
      ((weight + 6) + 1) ^
          ((((2 * weight + rho) * ((weight + 6) + 1) + 1) *
            blockLength) - 1) < embedded.cellulation.interiorFaces.card := by
    simpa [weightedCleanHexBlockThreshold, weight, rho, Nat.add_assoc]
      using hlarge
  simpa [HasCleanHexagonalGeodesicBlock, weight, rho, Nat.add_assoc] using
    (connectedBoundedFaceDual_exists_cleanHexagonalGeodesicBlock
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces embedded.internalFace_incidence_le_two
      (weight + 6) hfaceSize geometry.internalDualConnected
      (2 * weight + rho) blockLength hpositive hdefects hlarge')

/-- A uniform coarse threshold valid whenever the actual negative-curvature
weight is at most `weightBound`.  The exponent intentionally omits the
harmless predecessor used by the sharp threshold, making monotonicity in the
weight bound explicit. -/
def boundedWeightCleanHexBlockThreshold {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) (weightBound blockLength : Nat) : Nat :=
  let rho := embedded.cellulation.boundarySurplus source.toFramedTrailData
  (weightBound + 7) ^
    (((2 * weightBound + rho) * (weightBound + 7) + 1) * blockLength)

/-- Honest L1 case split at any proposed uniform curvature bound.  A source
trail above the coarse threshold either has negative-curvature weight beyond
that bound, or contains the clean hexagonal block required by the corridor
engine.  Thus the source proof's remaining obligation is precisely the first
branch; signed L9 cannot silently discard it. -/
theorem weight_exceeds_bound_or_hasCleanHexagonalGeodesicBlock
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (weightBound blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge :
      embedded.boundedWeightCleanHexBlockThreshold weightBound blockLength <
        embedded.cellulation.interiorFaces.card) :
    weightBound < embedded.interiorNegativeCurvatureWeight ∨
      embedded.HasCleanHexagonalGeodesicBlock blockLength := by
  let weight := embedded.interiorNegativeCurvatureWeight
  let rho := embedded.cellulation.boundarySurplus source.toFramedTrailData
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
    have hexponent :
        (((2 * weight + rho) * (weight + 7) + 1) * blockLength) - 1 ≤
          ((2 * weightBound + rho) * (weightBound + 7) + 1) *
            blockLength :=
      (Nat.sub_le _ _).trans hpreExponent
    have hthreshold :
        (weight + 7) ^
            ((((2 * weight + rho) * (weight + 7) + 1) * blockLength) - 1) ≤
          (weightBound + 7) ^
            (((2 * weightBound + rho) * (weightBound + 7) + 1) *
              blockLength) := by
      calc
        (weight + 7) ^
              ((((2 * weight + rho) * (weight + 7) + 1) *
                blockLength) - 1) ≤
            (weightBound + 7) ^
              ((((2 * weight + rho) * (weight + 7) + 1) *
                blockLength) - 1) :=
          Nat.pow_le_pow_left hbase _
        _ ≤ (weightBound + 7) ^
              (((2 * weightBound + rho) * (weightBound + 7) + 1) *
                blockLength) :=
          Nat.pow_le_pow_right (by omega) hexponent
    apply embedded.exists_cleanHexagonalGeodesicBlock_of_weightedL9
      hsource geometry blockLength hpositive
    exact lt_of_le_of_lt
      (by simpa [weightedCleanHexBlockThreshold,
          boundedWeightCleanHexBlockThreshold, weight, rho]
        using hthreshold)
      hlarge
  · left
    simpa [weight] using (Nat.lt_of_not_ge hweight)

/-- A coarse clean-block threshold stated using a bound on pentagons rather
than an unexplained curvature parameter.  Exact weighted L9 pays the
negative-curvature weight from this bound plus the fixed source feet. -/
def pentagonBoundedCleanHexBlockThreshold {source : SourceTrail G}
    (embedded : source.AnnularEmbedding)
    (pentagonBound blockLength : Nat) : Nat :=
  embedded.boundedWeightCleanHexBlockThreshold
    (pentagonBound + 4 + 2 * source.frozenInterfaceStubVertices.card)
    blockLength

/-- Source-faithful L1 alternative.  Above the explicit threshold, either
the annulus contains more pentagons than the proposed bound, or the internal
facial dual contains the clean hexagonal geodesic block needed by the
compositional corridor engine.  The first branch remains a named structural
obligation; this theorem does not replace it by a classical covering step. -/
theorem pentagonCount_exceeds_bound_or_hasCleanHexagonalGeodesicBlock
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pentagonBound blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge :
      embedded.pentagonBoundedCleanHexBlockThreshold
          pentagonBound blockLength <
        embedded.cellulation.interiorFaces.card) :
    pentagonBound < embedded.interiorFaceLengths.count 5 ∨
      embedded.HasCleanHexagonalGeodesicBlock blockLength := by
  let weightBound :=
    pentagonBound + 4 + 2 * source.frozenInterfaceStubVertices.card
  obtain hweight | hclean :=
    embedded.weight_exceeds_bound_or_hasCleanHexagonalGeodesicBlock
      hsource geometry weightBound blockLength hpositive
        (by
          simpa [pentagonBoundedCleanHexBlockThreshold, weightBound]
            using hlarge)
  · left
    have hpaid :=
      embedded.interiorNegativeCurvatureWeight_le_pentagonCount_add_sourceFeet
        hsource geometry
    by_contra hnot
    have hpentagons :
        embedded.interiorFaceLengths.count 5 ≤ pentagonBound :=
      Nat.le_of_not_gt hnot
    dsimp [weightBound] at hweight
    omega
  · exact Or.inr hclean

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
