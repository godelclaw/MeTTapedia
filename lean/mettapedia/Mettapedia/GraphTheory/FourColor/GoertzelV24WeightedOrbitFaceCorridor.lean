import Mettapedia.GraphTheory.FourColor.GoertzelV24CleanHexCorridor

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WeightedOrbitFaceCorridor

open GoertzelV24BoundedDegreePath
open GoertzelV24BulkCorridor
open GoertzelV24CleanHexCorridor
open GoertzelV24CurvatureScope
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexPathExtraction
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Boundary lengths indexed by the actual quotient faces of a rotation
system. Multiplicity is retained because the quotient carrier has one point
for every face-permutation orbit. -/
def orbitFaceBoundaryLengths (RS : RotationSystem V E) : Multiset Nat :=
  (Finset.univ : Finset (OrbitFace RS)).val.map fun face =>
    (orbitFaceBoundary RS face).card

/-- Minimum face length five, stated directly on quotient faces. -/
def OrbitFaceMinimumFive (RS : RotationSystem V E) : Prop :=
  ∀ face : OrbitFace RS, 5 ≤ (orbitFaceBoundary RS face).card

/-- Total negative-curvature magnitude on quotient faces. -/
def orbitFaceNegativeCurvatureWeight (RS : RotationSystem V E) : Nat :=
  faceCycleNegativeCurvatureWeight (orbitFaceBoundaryLengths RS)

theorem orbitFaceBoundaryLengths_minimumFive
    (RS : RotationSystem V E) (hminimum : OrbitFaceMinimumFive RS) :
    FaceCycleMinimumFive (orbitFaceBoundaryLengths RS) := by
  intro length hlength
  unfold orbitFaceBoundaryLengths at hlength
  rw [Multiset.mem_map] at hlength
  obtain ⟨face, _hface, rfl⟩ := hlength
  exact hminimum face

/-- The multiset curvature sum is the quotient-face curvature sum. -/
theorem sum_orbitFaceBoundaryLengthCurvature_eq_totalCurvature
    (RS : RotationSystem V E) :
    ((orbitFaceBoundaryLengths RS).map faceLengthCurvature).sum =
      orbitFaceTotalCurvature RS := by
  classical
  simp [orbitFaceBoundaryLengths, orbitFaceTotalCurvature,
    faceLengthCurvature]

/-- Weighted Gauss--Bonnet on quotient faces: pentagons pay both the base
twelve units and every unit of negative curvature carried by long faces. -/
theorem orbitFacePentagonCount_eq_twelve_add_negativeCurvatureWeight
    (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hminimum : OrbitFaceMinimumFive RS) :
    (orbitFaceBoundaryLengths RS).count 5 =
      12 + orbitFaceNegativeCurvatureWeight RS := by
  have hsimple := orbitFaceBoundarySimple_of_twoSided RS htwoSided
  have hcurvature := orbitFaceTotalCurvature_eq_twelve RS hsphere hsimple
  rw [← sum_orbitFaceBoundaryLengthCurvature_eq_totalCurvature RS,
    sum_faceLengthCurvature_eq_pentagonCount_sub_negativeWeight
      (orbitFaceBoundaryLengths RS)
      (orbitFaceBoundaryLengths_minimumFive RS hminimum)] at hcurvature
  unfold orbitFaceNegativeCurvatureWeight
  exact_mod_cast (show
    ((orbitFaceBoundaryLengths RS).count 5 : Int) =
      12 + faceCycleNegativeCurvatureWeight
        (orbitFaceBoundaryLengths RS) by omega)

/-- Counting quotient-face defects through the explicit face set agrees
with counting nonhexagonal entries in the quotient-face length multiset. -/
theorem card_orbitFaceDefectSet_eq_nonHexagonalFaceCount
    (RS : RotationSystem V E) :
    (faceDefectSet (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).card =
        nonHexagonalFaceCount (orbitFaceBoundaryLengths RS) := by
  unfold faceDefectSet
  rw [Finset.card_def, Finset.filter_val]
  unfold nonHexagonalFaceCount orbitFaceBoundaryLengths
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- The exact weighted curvature identity bounds the number of actual
nonhexagonal quotient faces by `12 + 2W`. -/
theorem card_orbitFaceDefectSet_le_twelve_add_twiceNegativeWeight
    (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hminimum : OrbitFaceMinimumFive RS) :
    (faceDefectSet (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).card ≤
        12 + 2 * orbitFaceNegativeCurvatureWeight RS := by
  rw [card_orbitFaceDefectSet_eq_nonHexagonalFaceCount]
  calc
    nonHexagonalFaceCount (orbitFaceBoundaryLengths RS) ≤
        (orbitFaceBoundaryLengths RS).count 5 +
          faceCycleNegativeCurvatureWeight (orbitFaceBoundaryLengths RS) :=
      nonHexagonalFaceCount_le_pentagonCount_add_negativeWeight
        (orbitFaceBoundaryLengths RS)
        (orbitFaceBoundaryLengths_minimumFive RS hminimum)
    _ = 12 + 2 * orbitFaceNegativeCurvatureWeight RS := by
      rw [orbitFacePentagonCount_eq_twelve_add_negativeCurvatureWeight
        RS hsphere htwoSided hminimum]
      simp only [orbitFaceNegativeCurvatureWeight]
      omega

/-- Every individual long-face excess is at most the total negative
curvature weight. -/
theorem orbitFaceBoundary_card_sub_six_le_negativeCurvatureWeight
    (RS : RotationSystem V E) (face : OrbitFace RS) :
    (orbitFaceBoundary RS face).card - 6 ≤
      orbitFaceNegativeCurvatureWeight RS := by
  unfold orbitFaceNegativeCurvatureWeight faceCycleNegativeCurvatureWeight
  apply Multiset.le_sum_of_mem
  simp [orbitFaceBoundaryLengths]

/-- Consequently every quotient face has length at most `W + 6`. This is
the variable-degree replacement for the fullerene-only bound by six. -/
theorem orbitFaceBoundary_card_le_negativeCurvatureWeight_add_six
    (RS : RotationSystem V E) (face : OrbitFace RS) :
    (orbitFaceBoundary RS face).card ≤
      orbitFaceNegativeCurvatureWeight RS + 6 := by
  by_cases hshort : (orbitFaceBoundary RS face).card ≤ 6
  · omega
  · have hexcess :=
      orbitFaceBoundary_card_sub_six_le_negativeCurvatureWeight RS face
    omega

section VariableDegreeCleanExtraction

variable {Face BoundaryEdge : Type*}
  [Fintype Face] [DecidableEq Face]
  [Fintype BoundaryEdge] [DecidableEq BoundaryEdge]

/-- With face size at most `D` and at most two incident faces per edge, the
closed dual neighborhood of all nonhexagonal faces has size at most the
number of defects times `D + 1`. -/
theorem card_faceDefectClosedNeighborhood_le_mul_degreeBound_add_one
    (faceBoundary : Face → Finset BoundaryEdge) (allFaces : Finset Face)
    (hincidence : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (degreeBound : Nat)
    (hfaceSize : ∀ face ∈ allFaces,
      (faceBoundary face).card ≤ degreeBound) :
    (faceDefectClosedNeighborhood faceBoundary allFaces).card ≤
      (faceDefectSet faceBoundary allFaces).card * (degreeBound + 1) := by
  classical
  let dual := interiorDualGraph faceBoundary allFaces
  letI : DecidableRel dual.Adj := Classical.decRel _
  have hdegree : ∀ face : AmbientFace allFaces,
      dual.degree face ≤ degreeBound := by
    intro face
    exact (interiorDualGraph_degree_le_faceBoundary_card
      faceBoundary allFaces hincidence face).trans
        (hfaceSize face.1 face.2)
  calc
    (faceDefectClosedNeighborhood faceBoundary allFaces).card ≤
        (ambientFaceDefectSet faceBoundary allFaces).card *
          (degreeBound + 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro defect _
      have hsubset :
          (Finset.univ.filter fun face : AmbientFace allFaces =>
            face = defect ∨ dual.Adj face defect) ⊆
            insert defect (dual.neighborFinset defect) := by
        intro face hface
        rcases (Finset.mem_filter.1 hface).2 with rfl | hadj
        · simp
        · exact Finset.mem_insert.2 (Or.inr (by simpa using hadj.symm))
      exact (Finset.card_le_card hsubset).trans
        (card_closedNeighborFinset_le
          dual degreeBound hdegree defect)
    _ = (faceDefectSet faceBoundary allFaces).card *
          (degreeBound + 1) := by
      rw [card_ambientFaceDefectSet_eq_faceDefectSet]

/-- Variable-degree clean bulk extraction. A connected facial dual with
maximum face size `D` and at most `B` nonhexagonal faces contains a geodesic
length-`L` block whose closed dual neighborhood is hexagonal once its face
count exceeds the displayed bounded-growth threshold. -/
theorem connectedBoundedFaceDual_exists_cleanHexagonalGeodesicBlock
    (faceBoundary : Face → Finset BoundaryEdge) (allFaces : Finset Face)
    (hincidence : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (degreeBound : Nat)
    (hfaceSize : ∀ face ∈ allFaces,
      (faceBoundary face).card ≤ degreeBound)
    (hconnected : (interiorDualGraph faceBoundary allFaces).Connected)
    (defectBudget blockLength : Nat) (hblockLength : 0 < blockLength)
    (hdefects : (faceDefectSet faceBoundary allFaces).card ≤ defectBudget)
    (hlarge :
      (degreeBound + 1) ^
          (((defectBudget * (degreeBound + 1) + 1) * blockLength) - 1) <
        allFaces.card) :
    ∃ start finish : AmbientFace allFaces,
      ∃ path : (interiorDualGraph faceBoundary allFaces).Walk start finish,
        path.IsPath ∧
          path.length =
            (interiorDualGraph faceBoundary allFaces).dist start finish ∧
          (defectBudget * (degreeBound + 1) + 1) * blockLength ≤
            path.length + 1 ∧
          ∃ block : Fin (defectBudget * (degreeBound + 1) + 1),
            ∀ offset : Fin blockLength,
              (faceBoundary
                (path.getVert
                  (corridorBlockIndex
                    (defectBudget := defectBudget * (degreeBound + 1))
                    block offset).val).1).card = 6 ∧
              ∀ neighbor : AmbientFace allFaces,
                (interiorDualGraph faceBoundary allFaces).Adj
                  (path.getVert
                    (corridorBlockIndex
                      (defectBudget := defectBudget * (degreeBound + 1))
                      block offset).val)
                  neighbor →
                (faceBoundary neighbor.1).card = 6 := by
  classical
  let dual := interiorDualGraph faceBoundary allFaces
  letI : DecidableRel dual.Adj := Classical.decRel _
  have hdegree : ∀ face : AmbientFace allFaces,
      dual.degree face ≤ degreeBound := by
    intro face
    exact (interiorDualGraph_degree_le_faceBoundary_card
      faceBoundary allFaces hincidence face).trans
        (hfaceSize face.1 face.2)
  obtain ⟨start, finish, path, hpath, hgeodesic, hpathLength⟩ :=
    exists_geodesicPath_length_ge_of_pow_lt_card
      dual hconnected degreeBound
        (((defectBudget * (degreeBound + 1) + 1) * blockLength) - 1)
      hdegree (by simpa [dual] using hlarge)
  have hpositionCount :
      (defectBudget * (degreeBound + 1) + 1) * blockLength ≤
        path.length + 1 := by
    omega
  have hneighborhood :
      (faceDefectClosedNeighborhood faceBoundary allFaces).card ≤
        defectBudget * (degreeBound + 1) := by
    calc
      (faceDefectClosedNeighborhood faceBoundary allFaces).card ≤
          (faceDefectSet faceBoundary allFaces).card *
            (degreeBound + 1) :=
        card_faceDefectClosedNeighborhood_le_mul_degreeBound_add_one
          faceBoundary allFaces hincidence degreeBound hfaceSize
      _ ≤ defectBudget * (degreeBound + 1) :=
        Nat.mul_le_mul_right (degreeBound + 1) hdefects
  have hbad :
      (pathContaminatedPositions faceBoundary allFaces path
        ((defectBudget * (degreeBound + 1) + 1) * blockLength)).card ≤
          defectBudget * (degreeBound + 1) :=
    (card_pathContaminatedPositions_le faceBoundary allFaces path hpath
      _ hpositionCount).trans hneighborhood
  obtain ⟨block, hblock⟩ := exists_corridorBlock_avoiding
    (defectBudget * (degreeBound + 1)) blockLength hblockLength
      (pathContaminatedPositions faceBoundary allFaces path
        ((defectBudget * (degreeBound + 1) + 1) * blockLength)) hbad
  refine ⟨start, finish, path, hpath, hgeodesic,
    hpositionCount, block, ?_⟩
  intro offset
  let position := corridorBlockIndex
    (defectBudget := defectBudget * (degreeBound + 1)) block offset
  have hclean : path.getVert position.val ∉
      faceDefectClosedNeighborhood faceBoundary allFaces := by
    intro hcontaminated
    exact hblock offset
      ((mem_pathContaminatedPositions_iff faceBoundary allFaces path
        ((defectBudget * (degreeBound + 1) + 1) * blockLength)
          position).2 hcontaminated)
  constructor
  · by_contra hnonhex
    exact hclean (mem_faceDefectClosedNeighborhood_of_defect
      faceBoundary allFaces (path.getVert position.val) hnonhex)
  · intro neighbor hadj
    by_contra hnonhex
    exact hclean (mem_faceDefectClosedNeighborhood_of_adj_defect
      faceBoundary allFaces hadj hnonhex)

end VariableDegreeCleanExtraction

/-- Face-count threshold for extracting a radius-one clean hexagonal
corridor of the requested length from a weighted-curvature sphere. -/
def weightedCleanHexCorridorFaceThreshold
    (RS : RotationSystem V E) (corridorLength : Nat) : Nat :=
  let weight := orbitFaceNegativeCurvatureWeight RS
  (weight + 7) ^
    ((((12 + 2 * weight) * (weight + 7) + 1) * corridorLength) - 1)

/-- Weighted-scope clean corridor extraction on actual quotient faces. No
upper face-size or fullerene hypothesis occurs: negative curvature controls
both the number of defects and the variable facial-dual degree. -/
theorem orbitFace_exists_cleanHexCorridorSkeleton_of_weightedCurvature
    (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hminimum : OrbitFaceMinimumFive RS)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (corridorLength : Nat) (hpositive : 0 < corridorLength)
    (hlarge : weightedCleanHexCorridorFaceThreshold RS corridorLength <
      Fintype.card (OrbitFace RS)) :
    Nonempty (CleanOrbitHexCorridorSkeleton RS corridorLength) := by
  let weight := orbitFaceNegativeCurvatureWeight RS
  have hfaceSize : ∀ face ∈
      (Finset.univ : Finset (OrbitFace RS)),
      (orbitFaceBoundary RS face).card ≤ weight + 6 := by
    intro face _
    exact orbitFaceBoundary_card_le_negativeCurvatureWeight_add_six
      RS face
  have hdefects :
      (faceDefectSet (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).card ≤
          12 + 2 * weight := by
    exact card_orbitFaceDefectSet_le_twelve_add_twiceNegativeWeight
      RS hsphere htwoSided hminimum
  have hconnected := orbitFaceInteriorDual_connected
    RS hsphere.cubic hprimal hrotation
  have hlarge' :
      ((weight + 6) + 1) ^
          ((((12 + 2 * weight) * ((weight + 6) + 1) + 1) *
            corridorLength) - 1) <
        (Finset.univ : Finset (OrbitFace RS)).card := by
    simpa [weightedCleanHexCorridorFaceThreshold, weight,
      Nat.add_assoc] using hlarge
  obtain ⟨start, finish, path, hpath, hgeodesic, hpositionBound,
      block, hclean⟩ :=
    connectedBoundedFaceDual_exists_cleanHexagonalGeodesicBlock
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) (weight + 6) hfaceSize hconnected
      (12 + 2 * weight) corridorLength hpositive hdefects hlarge'
  let corridor := OrbitHexCorridorSkeleton.ofPathBlockWithBudget
    RS path hpath hgeodesic
      ((12 + 2 * weight) * ((weight + 6) + 1)) corridorLength
      hpositionBound block (fun offset => (hclean offset).1)
  exact ⟨{
    toOrbitHexCorridorSkeleton := corridor
    neighbor_hexagonal := fun offset neighbor hadj =>
      (hclean offset).2 neighbor hadj
  }⟩

/-- Every weighted-curvature sphere is in one of two explicit regimes: its
face count is bounded by its negative-curvature weight, or it contains a
clean hexagonal corridor of any prescribed positive length. -/
theorem orbitFace_card_le_weightedThreshold_or_exists_cleanHexCorridor
    (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hminimum : OrbitFaceMinimumFive RS)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (corridorLength : Nat) (hpositive : 0 < corridorLength) :
    Fintype.card (OrbitFace RS) ≤
        weightedCleanHexCorridorFaceThreshold RS corridorLength ∨
      Nonempty (CleanOrbitHexCorridorSkeleton RS corridorLength) := by
  by_cases hlarge : weightedCleanHexCorridorFaceThreshold RS corridorLength <
      Fintype.card (OrbitFace RS)
  · exact Or.inr
      (orbitFace_exists_cleanHexCorridorSkeleton_of_weightedCurvature
        RS hsphere htwoSided hminimum hprimal hrotation
          corridorLength hpositive hlarge)
  · exact Or.inl (by omega)

end

end GoertzelV24WeightedOrbitFaceCorridor

end Mettapedia.GraphTheory.FourColor
