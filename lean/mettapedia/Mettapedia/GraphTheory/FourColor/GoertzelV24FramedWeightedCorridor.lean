import Mettapedia.GraphTheory.FourColor.GoertzelV24EmbeddedSourceTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24WeightedOrbitFaceCorridor

/-!
# Weighted clean corridors inside embedded source trails

The framed Excess Identity is signed: pentagonal and long-face curvature can
cancel.  It therefore does not give a constant bound on the number of
nonhexagonal internal faces.  This module keeps the missing quantity visible
as the total negative-curvature weight `W`.

For an embedded source trail whose internal faces have simple boundaries,
minimum length five, and connected internal dual, L9 gives the exact weighted
balance.  Consequently there are at most `2W + rho` internal nonhexagons, each
internal face has boundary size at most `W + 6`, and the existing bounded-dual
argument extracts a clean hexagonal geodesic block above an explicit weighted
threshold.  Controlling the high-`W` branch remains a separate part of the
reductive proof.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BulkCorridor
open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24HexPathExtraction
open GoertzelV24WeightedOrbitFaceCorridor
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- The geometric hypotheses on the internal cells needed by the clean-block
argument.  These are semantic properties of the annular embedding, not
numerical conclusions smuggled into its statement. -/
structure CorridorGeometry {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) : Prop where
  internalBoundarySimple :
    ∀ face ∈ embedded.cellulation.interiorFaces,
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card = embedded.cellulation.faceLength face
  internalMinimumFive :
    ∀ face ∈ embedded.cellulation.interiorFaces,
      5 ≤ (orbitFaceBoundary
        embedded.cellulation.rotation.toRotationSystem face).card
  internalDualConnected :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Connected

/-- Internal face-boundary lengths, with one entry for each internal facial
orbit. -/
def interiorFaceLengths {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) : Multiset Nat :=
  embedded.cellulation.interiorFaces.val.map fun face =>
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card

/-- Total long-face negative curvature carried by the internal cells. -/
def interiorNegativeCurvatureWeight {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) : Nat :=
  faceCycleNegativeCurvatureWeight embedded.interiorFaceLengths

theorem interiorFaceLengths_minimumFive
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    FaceCycleMinimumFive embedded.interiorFaceLengths := by
  intro length hlength
  unfold interiorFaceLengths at hlength
  rw [Multiset.mem_map] at hlength
  obtain ⟨face, hface, rfl⟩ := hlength
  exact geometry.internalMinimumFive face hface

/-- On simple internal face boundaries, the curvature sum of the boundary
length multiset is the negative of the signed annular excess. -/
theorem sum_interiorFaceLengthCurvature_eq_neg_interiorExcess
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    (embedded.interiorFaceLengths.map faceLengthCurvature).sum =
      -embedded.cellulation.interiorExcess := by
  unfold interiorFaceLengths
  rw [Multiset.map_map]
  unfold FramedAnnularCellulation.interiorExcess
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro face hface
  simp only [Function.comp_apply, faceLengthCurvature, neg_sub]
  rw [geometry.internalBoundarySimple face hface]

/-- Exact weighted L9 balance.  The long-face weight and boundary surplus pay
for every pentagon plus the two missing-edge feet and frozen stub feet. -/
theorem interiorPentagonCount_add_sourceFeet_eq_weight_add_boundarySurplus
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.interiorFaceLengths.count 5 + 4 +
        2 * source.frozenInterfaceStubVertices.card =
      embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
  have hcurvature :=
    embedded.sum_interiorFaceLengthCurvature_eq_neg_interiorExcess geometry
  have hweighted :=
    sum_faceLengthCurvature_eq_pentagonCount_sub_negativeWeight
      embedded.interiorFaceLengths
      (embedded.interiorFaceLengths_minimumFive geometry)
  have hexcess := embedded.interiorExcess_eq_source_framed_constant hsource
  unfold interiorNegativeCurvatureWeight
  rw [hweighted, hexcess] at hcurvature
  exact_mod_cast (show
    (embedded.interiorFaceLengths.count 5 : Int) + 4 +
          2 * source.frozenInterfaceStubVertices.card =
        faceCycleNegativeCurvatureWeight embedded.interiorFaceLengths +
          embedded.cellulation.boundarySurplus source.toFramedTrailData by
    omega)

theorem interiorPentagonCount_le_weight_add_boundarySurplus
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.interiorFaceLengths.count 5 ≤
      embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
  have hbalance :=
    embedded.interiorPentagonCount_add_sourceFeet_eq_weight_add_boundarySurplus
      hsource geometry
  omega

/-- Counting defects through the internal face set agrees with counting
nonhexagonal entries in the internal length multiset. -/
theorem card_interiorFaceDefectSet_eq_nonHexagonalFaceCount
    {source : SourceTrail G} (embedded : source.AnnularEmbedding) :
    (faceDefectSet
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).card =
        nonHexagonalFaceCount embedded.interiorFaceLengths := by
  unfold faceDefectSet
  rw [Finset.card_def, Finset.filter_val]
  unfold nonHexagonalFaceCount interiorFaceLengths
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- Faithful annular defect budget: it depends on the actual negative
curvature weight and cannot in general be replaced by a constant. -/
theorem card_interiorFaceDefectSet_le_twiceWeight_add_boundarySurplus
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    (faceDefectSet
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).card ≤
      2 * embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
  rw [embedded.card_interiorFaceDefectSet_eq_nonHexagonalFaceCount]
  calc
    nonHexagonalFaceCount embedded.interiorFaceLengths ≤
        embedded.interiorFaceLengths.count 5 +
          embedded.interiorNegativeCurvatureWeight :=
      nonHexagonalFaceCount_le_pentagonCount_add_negativeWeight
        embedded.interiorFaceLengths
        (embedded.interiorFaceLengths_minimumFive geometry)
    _ ≤ 2 * embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
      have hpentagons :=
        embedded.interiorPentagonCount_le_weight_add_boundarySurplus
          hsource geometry
      omega

theorem internalFaceBoundary_card_sub_six_le_weight
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    {face : OrbitFace embedded.cellulation.rotation.toRotationSystem}
    (hface : face ∈ embedded.cellulation.interiorFaces) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card - 6 ≤ embedded.interiorNegativeCurvatureWeight := by
  unfold interiorNegativeCurvatureWeight faceCycleNegativeCurvatureWeight
  apply Multiset.le_sum_of_mem
  rw [Multiset.mem_map]
  refine ⟨
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card, ?_, rfl⟩
  unfold interiorFaceLengths
  rw [Multiset.mem_map]
  exact ⟨face, hface, rfl⟩

/-- Every internal face has boundary size at most `W + 6`. -/
theorem internalFaceBoundary_card_le_weight_add_six
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    {face : OrbitFace embedded.cellulation.rotation.toRotationSystem}
    (hface : face ∈ embedded.cellulation.interiorFaces) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card ≤ embedded.interiorNegativeCurvatureWeight + 6 := by
  by_cases hshort :
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card ≤ 6
  · omega
  · have hexcess := embedded.internalFaceBoundary_card_sub_six_le_weight hface
    omega

/-- Restricting the full orbit-face incidence model to the internal faces
preserves the at-most-two-faces-per-edge bound. -/
theorem internalFace_incidence_le_two
    {source : SourceTrail G} (embedded : source.AnnularEmbedding) :
    ∀ edge,
      totalIncidenceCount
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces edge ≤ 2 := by
  intro edge
  calc
    totalIncidenceCount
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces edge ≤
      totalIncidenceCount
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) edge := by
        exact Finset.card_le_card
          (Finset.filter_subset_filter _ (by simp))
    _ ≤ 2 := orbitFace_incidence_le_two
      embedded.cellulation.rotation.toRotationSystem edge

/-- Weighted L1 threshold for an embedded source trail. -/
def weightedCleanHexBlockThreshold {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) (blockLength : Nat) : Nat :=
  let weight := embedded.interiorNegativeCurvatureWeight
  let rho := embedded.cellulation.boundarySurplus source.toFramedTrailData
  (weight + 7) ^
    ((((2 * weight + rho) * (weight + 7) + 1) * blockLength) - 1)

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
                    neighbor.1).card = 6 := by
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
    exact embedded.card_interiorFaceDefectSet_le_twiceWeight_add_boundarySurplus
      hsource geometry
  have hlarge' :
      ((weight + 6) + 1) ^
          ((((2 * weight + rho) * ((weight + 6) + 1) + 1) *
            blockLength) - 1) < embedded.cellulation.interiorFaces.card := by
    simpa [weightedCleanHexBlockThreshold, weight, rho, Nat.add_assoc]
      using hlarge
  simpa [weight, rho, Nat.add_assoc] using
    (connectedBoundedFaceDual_exists_cleanHexagonalGeodesicBlock
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces embedded.internalFace_incidence_le_two
      (weight + 6) hfaceSize geometry.internalDualConnected
      (2 * weight + rho) blockLength hpositive hdefects hlarge')

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
