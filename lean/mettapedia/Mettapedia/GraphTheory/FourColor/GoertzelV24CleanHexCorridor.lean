import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CleanHexCorridor

open GoertzelV24BoundedDegreePath
open GoertzelV24BulkCorridor
open GoertzelV24CurvatureScope
open GoertzelV24CyclicFiveFaceIntersections
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexPathExtraction
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraphDartRotation

variable {Face Edge : Type*} [Fintype Face] [DecidableEq Face]
  [Fintype Edge] [DecidableEq Edge]

noncomputable section

/-- Nonhexagonal faces, represented directly as vertices of the ambient
facial dual. -/
def ambientFaceDefectSet (faceBoundary : Face → Finset Edge)
    (allFaces : Finset Face) : Finset (AmbientFace allFaces) :=
  Finset.univ.filter fun face => (faceBoundary face.1).card ≠ 6

@[simp]
theorem mem_ambientFaceDefectSet_iff
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    (face : AmbientFace allFaces) :
    face ∈ ambientFaceDefectSet faceBoundary allFaces ↔
      (faceBoundary face.1).card ≠ 6 := by
  simp [ambientFaceDefectSet]

/-- Passing from faces to the ambient-face subtype does not change the
number of defects. -/
theorem card_ambientFaceDefectSet_eq_faceDefectSet
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face) :
    (ambientFaceDefectSet faceBoundary allFaces).card =
      (faceDefectSet faceBoundary allFaces).card := by
  classical
  let forward : {face // face ∈ faceDefectSet faceBoundary allFaces} →
      {face // face ∈ ambientFaceDefectSet faceBoundary allFaces} :=
    fun face =>
      ⟨⟨face.1, (mem_faceDefectSet_iff faceBoundary allFaces face.1).1
        face.2 |>.1⟩,
       (mem_ambientFaceDefectSet_iff faceBoundary allFaces _).2
        ((mem_faceDefectSet_iff faceBoundary allFaces face.1).1 face.2 |>.2)⟩
  have hinjective : Function.Injective forward := by
    intro left right heq
    apply Subtype.ext
    exact congrArg (fun face => face.1.1) heq
  have hsurjective : Function.Surjective forward := by
    intro face
    let original : {face // face ∈ faceDefectSet faceBoundary allFaces} :=
      ⟨face.1.1, (mem_faceDefectSet_iff faceBoundary allFaces face.1.1).2
        ⟨face.1.2,
          (mem_ambientFaceDefectSet_iff faceBoundary allFaces face.1).1 face.2⟩⟩
    refine ⟨original, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hcard := Fintype.card_congr (Equiv.ofBijective forward ⟨hinjective, hsurjective⟩)
  simpa only [Fintype.card_coe] using hcard.symm

/-- Faces contaminated by a defect: each defect itself and every dual
neighbor of that defect. -/
noncomputable def faceDefectClosedNeighborhood
    (faceBoundary : Face → Finset Edge)
    (allFaces : Finset Face) : Finset (AmbientFace allFaces) := by
  classical
  exact (ambientFaceDefectSet faceBoundary allFaces).biUnion fun defect =>
    Finset.univ.filter fun face =>
      face = defect ∨ (interiorDualGraph faceBoundary allFaces).Adj face defect

theorem mem_faceDefectClosedNeighborhood_of_defect
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    (face : AmbientFace allFaces)
    (hdefect : (faceBoundary face.1).card ≠ 6) :
    face ∈ faceDefectClosedNeighborhood faceBoundary allFaces := by
  exact Finset.mem_biUnion.2
    ⟨face, (mem_ambientFaceDefectSet_iff faceBoundary allFaces face).2 hdefect,
      by simp⟩

theorem mem_faceDefectClosedNeighborhood_of_adj_defect
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    {face defect : AmbientFace allFaces}
    (hadj : (interiorDualGraph faceBoundary allFaces).Adj face defect)
    (hdefect : (faceBoundary defect.1).card ≠ 6) :
    face ∈ faceDefectClosedNeighborhood faceBoundary allFaces := by
  refine Finset.mem_biUnion.2
    ⟨defect,
      (mem_ambientFaceDefectSet_iff faceBoundary allFaces defect).2 hdefect, ?_⟩
  simp [hadj]

/-- With face size at most six and at most two faces per edge, the closed
dual neighborhood of every defect contains at most seven faces. -/
theorem card_faceDefectClosedNeighborhood_le_seven_mul
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    (hincidence : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hfaceSize : ∀ face ∈ allFaces, (faceBoundary face).card ≤ 6) :
    (faceDefectClosedNeighborhood faceBoundary allFaces).card ≤
      (faceDefectSet faceBoundary allFaces).card * 7 := by
  classical
  let dual := interiorDualGraph faceBoundary allFaces
  letI : DecidableRel dual.Adj := Classical.decRel _
  have hdegree : ∀ face : AmbientFace allFaces, dual.degree face ≤ 6 := by
    intro face
    exact (interiorDualGraph_degree_le_faceBoundary_card
      faceBoundary allFaces hincidence face).trans
        (hfaceSize face.1 face.2)
  calc
    (faceDefectClosedNeighborhood faceBoundary allFaces).card ≤
        (ambientFaceDefectSet faceBoundary allFaces).card * 7 := by
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
        (card_closedNeighborFinset_le dual 6 hdegree defect)
    _ = (faceDefectSet faceBoundary allFaces).card * 7 := by
      rw [card_ambientFaceDefectSet_eq_faceDefectSet]

/-- Positions among an initial segment of a facial-dual path that meet the
closed defect neighborhood. -/
def pathContaminatedPositions
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    {start finish : AmbientFace allFaces}
    (path : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (positionCount : Nat) : Finset (Fin positionCount) :=
  Finset.univ.filter fun position =>
    path.getVert position.val ∈
      faceDefectClosedNeighborhood faceBoundary allFaces

@[simp]
theorem mem_pathContaminatedPositions_iff
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    {start finish : AmbientFace allFaces}
    (path : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (positionCount : Nat) (position : Fin positionCount) :
    position ∈ pathContaminatedPositions faceBoundary allFaces path positionCount ↔
      path.getVert position.val ∈
        faceDefectClosedNeighborhood faceBoundary allFaces := by
  simp [pathContaminatedPositions]

/-- A simple path visits each contaminated face at most once. -/
theorem card_pathContaminatedPositions_le
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    {start finish : AmbientFace allFaces}
    (path : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hpath : path.IsPath) (positionCount : Nat)
    (hpositionCount : positionCount ≤ path.length + 1) :
    (pathContaminatedPositions faceBoundary allFaces path positionCount).card ≤
      (faceDefectClosedNeighborhood faceBoundary allFaces).card := by
  let positions := pathContaminatedPositions faceBoundary allFaces path positionCount
  let neighborhood := faceDefectClosedNeighborhood faceBoundary allFaces
  let pathFace : positions → neighborhood := fun position =>
    ⟨path.getVert position.1.val,
      (mem_pathContaminatedPositions_iff faceBoundary allFaces path
        positionCount position.1).1 position.2⟩
  have hinjective : Function.Injective pathFace := by
    intro left right hfaces
    have hvertices : path.getVert left.1.val = path.getVert right.1.val :=
      congrArg Subtype.val hfaces
    have hleftBound : left.1.val ≤ path.length := by
      have hleft := left.1.isLt
      omega
    have hrightBound : right.1.val ≤ path.length := by
      have hright := right.1.isLt
      omega
    have hindices := hpath.getVert_injOn
      (by simpa using hleftBound) (by simpa using hrightBound) hvertices
    apply Subtype.ext
    exact Fin.ext hindices
  have hcard := Fintype.card_le_of_injective pathFace hinjective
  simpa only [Fintype.card_coe] using hcard

/-- Among `B+1` equal consecutive blocks, at most `B` bad positions leave
one entire block clean. -/
theorem exists_corridorBlock_avoiding
    (badBudget blockLength : Nat) (hblockLength : 0 < blockLength)
    (badPositions : Finset (Fin ((badBudget + 1) * blockLength)))
    (hbad : badPositions.card ≤ badBudget) :
    ∃ block : Fin (badBudget + 1),
      ∀ offset : Fin blockLength,
        corridorBlockIndex block offset ∉ badPositions := by
  classical
  by_contra hnoBlock
  push Not at hnoBlock
  choose badOffset hbadOffset using hnoBlock
  let selectedBad : Fin (badBudget + 1) → {position // position ∈ badPositions} :=
    fun block => ⟨corridorBlockIndex block (badOffset block), hbadOffset block⟩
  have hinjective : Function.Injective selectedBad := by
    intro left right hequal
    apply corridorBlockIndex_injective_block hblockLength
      (badOffset left) (badOffset right)
    exact congrArg Subtype.val hequal
  have hcard := Fintype.card_le_of_injective selectedBad hinjective
  have htooMany : badBudget + 1 ≤ badPositions.card := by
    simpa using hcard
  omega

/-- A large connected bounded-degree face patch with at most `B` defects
contains a geodesic block whose entire closed dual neighborhood is
hexagonal. The loose contamination budget is `7B`. -/
theorem connectedSixFaceDual_exists_cleanHexagonalGeodesicBlock
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    (hincidence : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hfaceSize : ∀ face ∈ allFaces, (faceBoundary face).card ≤ 6)
    (hconnected : (interiorDualGraph faceBoundary allFaces).Connected)
    (defectBudget blockLength : Nat) (hblockLength : 0 < blockLength)
    (hdefects : (faceDefectSet faceBoundary allFaces).card ≤ defectBudget)
    (hlarge : 7 ^ ((defectBudget * 7 + 1) * blockLength - 1) <
      allFaces.card) :
    ∃ start finish : AmbientFace allFaces,
      ∃ path : (interiorDualGraph faceBoundary allFaces).Walk start finish,
        path.IsPath ∧
          path.length =
            (interiorDualGraph faceBoundary allFaces).dist start finish ∧
          (defectBudget * 7 + 1) * blockLength ≤ path.length + 1 ∧
          ∃ block : Fin (defectBudget * 7 + 1),
            ∀ offset : Fin blockLength,
              (faceBoundary
                (path.getVert
                  (corridorBlockIndex
                    (defectBudget := defectBudget * 7) block offset).val).1).card = 6 ∧
              ∀ neighbor : AmbientFace allFaces,
                (interiorDualGraph faceBoundary allFaces).Adj
                  (path.getVert
                    (corridorBlockIndex
                      (defectBudget := defectBudget * 7) block offset).val)
                  neighbor →
                (faceBoundary neighbor.1).card = 6 := by
  obtain ⟨start, finish, path, hpath, hgeodesic, hpathLength⟩ :=
    interiorDualGraph_exists_geodesicPath_length_ge_of_seven_pow_lt
      faceBoundary allFaces hincidence hfaceSize hconnected
        ((defectBudget * 7 + 1) * blockLength - 1) hlarge
  have hpositionCount : (defectBudget * 7 + 1) * blockLength ≤
      path.length + 1 := by
    omega
  have hneighborhood :
      (faceDefectClosedNeighborhood faceBoundary allFaces).card ≤
        defectBudget * 7 := by
    calc
      (faceDefectClosedNeighborhood faceBoundary allFaces).card ≤
          (faceDefectSet faceBoundary allFaces).card * 7 :=
        card_faceDefectClosedNeighborhood_le_seven_mul
          faceBoundary allFaces hincidence hfaceSize
      _ ≤ defectBudget * 7 := Nat.mul_le_mul_right 7 hdefects
  have hbad :
      (pathContaminatedPositions faceBoundary allFaces path
        ((defectBudget * 7 + 1) * blockLength)).card ≤ defectBudget * 7 :=
    (card_pathContaminatedPositions_le faceBoundary allFaces path hpath
      _ hpositionCount).trans hneighborhood
  obtain ⟨block, hblock⟩ := exists_corridorBlock_avoiding
    (defectBudget * 7) blockLength hblockLength
      (pathContaminatedPositions faceBoundary allFaces path
        ((defectBudget * 7 + 1) * blockLength)) hbad
  refine ⟨start, finish, path, hpath, hgeodesic, hpositionCount, block, ?_⟩
  intro offset
  let position := corridorBlockIndex
    (defectBudget := defectBudget * 7) block offset
  have hclean : path.getVert position.val ∉
      faceDefectClosedNeighborhood faceBoundary allFaces := by
    intro hcontaminated
    exact hblock offset
      ((mem_pathContaminatedPositions_iff faceBoundary allFaces path
        ((defectBudget * 7 + 1) * blockLength) position).2 hcontaminated)
  constructor
  · by_contra hnonhex
    exact hclean (mem_faceDefectClosedNeighborhood_of_defect
      faceBoundary allFaces (path.getVert position.val) hnonhex)
  · intro neighbor hadj
    by_contra hnonhex
    exact hclean (mem_faceDefectClosedNeighborhood_of_adj_defect
      faceBoundary allFaces hadj hnonhex)

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Fullerene specialization of clean bulk extraction. Avoiding the closed
dual neighborhoods of the twelve pentagons costs at most `12*7=84`
positions, so eighty-five blocks suffice. -/
theorem orbitFaceFullerene_exists_cleanHexagonalGeodesicBlock
    (RS : RotationSystem V E) (hsphere : SphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hfullerene : OrbitFaceFullerene RS)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (blockLength : Nat) (hblockLength : 0 < blockLength)
    (hlarge : 7 ^ (85 * blockLength - 1) < Fintype.card (OrbitFace RS)) :
    ∃ start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS)),
      ∃ path :
        (interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).Walk start finish,
        path.IsPath ∧
          path.length =
            (interiorDualGraph (orbitFaceBoundary RS)
              (Finset.univ : Finset (OrbitFace RS))).dist start finish ∧
          85 * blockLength ≤ path.length + 1 ∧
          ∃ block : Fin 85,
            ∀ offset : Fin blockLength,
              (orbitFaceBoundary RS
                (path.getVert
                  (corridorBlockIndex
                    (defectBudget := 84) block offset).val).1).card = 6 ∧
              ∀ neighbor : AmbientFace (Finset.univ : Finset (OrbitFace RS)),
                (interiorDualGraph (orbitFaceBoundary RS)
                  (Finset.univ : Finset (OrbitFace RS))).Adj
                    (path.getVert
                      (corridorBlockIndex
                        (defectBudget := 84) block offset).val)
                    neighbor →
                (orbitFaceBoundary RS neighbor.1).card = 6 := by
  have hsimple := orbitFaceBoundarySimple_of_twoSided RS htwoSided
  have hfaceSize : ∀ face ∈ (Finset.univ : Finset (OrbitFace RS)),
      (orbitFaceBoundary RS face).card ≤ 6 := by
    intro face _
    rcases hfullerene face with hfive | hsix <;> omega
  have hdefects :
      (faceDefectSet (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).card ≤ 12 := by
    rw [orbitFaceDefectSet_card_eq_twelve_of_fullerene
      RS (OrbitSphericalCubicMapData.ofSphericalCubicMapData RS hsphere)
        hsimple hfullerene]
  have hconnected := orbitFaceInteriorDual_connected
    RS hsphere.cubic hprimal hrotation
  simpa only [Nat.reduceMul, Nat.reduceAdd] using
    connectedSixFaceDual_exists_cleanHexagonalGeodesicBlock
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) hfaceSize hconnected
      12 blockLength hblockLength hdefects hlarge

/-- A clean block can be converted to a corridor skeleton for any finite
contamination budget. The earlier thirteen-block constructor is the special
case with budget twelve. -/
def OrbitHexCorridorSkeleton.ofPathBlockWithBudget
    (RS : RotationSystem V E) {start finish :
      AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (path : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (hpath : path.IsPath)
    (hgeodesic : path.length =
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).dist start finish)
    (blockBudget corridorLength : Nat)
    (hpositionBound : (blockBudget + 1) * corridorLength ≤ path.length + 1)
    (block : Fin (blockBudget + 1))
    (hhexagonal : ∀ offset : Fin corridorLength,
      (orbitFaceBoundary RS
        (path.getVert
          (corridorBlockIndex
            (defectBudget := blockBudget) block offset).val).1).card = 6) :
    OrbitHexCorridorSkeleton RS corridorLength where
  faceAt := fun offset =>
    path.getVert
      (corridorBlockIndex (defectBudget := blockBudget) block offset).val
  faceAt_injective := by
    intro left right hfaces
    have hleftBound :
        (corridorBlockIndex (defectBudget := blockBudget) block left).val ≤
          path.length := by
      have hindex := (corridorBlockIndex
        (defectBudget := blockBudget) block left).isLt
      omega
    have hrightBound :
        (corridorBlockIndex (defectBudget := blockBudget) block right).val ≤
          path.length := by
      have hindex := (corridorBlockIndex
        (defectBudget := blockBudget) block right).isLt
      omega
    have hindices := hpath.getVert_injOn
      (by simpa using hleftBound) (by simpa using hrightBound) hfaces
    apply Fin.ext
    change block.val * corridorLength + left.val =
      block.val * corridorLength + right.val at hindices
    omega
  hexagonal := hhexagonal
  consecutive_adjacent := by
    intro left right hsuccessor
    have hrightBound :
        (corridorBlockIndex (defectBudget := blockBudget) block right).val ≤
          path.length := by
      have hindex := (corridorBlockIndex
        (defectBudget := blockBudget) block right).isLt
      omega
    have hleftStrict :
        (corridorBlockIndex (defectBudget := blockBudget) block left).val <
          path.length := by
      change block.val * corridorLength + left.val < path.length
      change block.val * corridorLength + right.val ≤ path.length at hrightBound
      omega
    have hadj := path.adj_getVert_succ hleftStrict
    change (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (path.getVert (block.val * corridorLength + left.val))
        (path.getVert (block.val * corridorLength + right.val))
    change (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (path.getVert (block.val * corridorLength + left.val))
        (path.getVert ((block.val * corridorLength + left.val) + 1)) at hadj
    simpa only [hsuccessor, Nat.add_assoc] using hadj
  separated_not_adjacent := by
    intro left right hseparated
    have hleftBound :
        (corridorBlockIndex (defectBudget := blockBudget) block left).val ≤
          path.length := by
      have hindex := (corridorBlockIndex
        (defectBudget := blockBudget) block left).isLt
      omega
    have hrightBound :
        (corridorBlockIndex (defectBudget := blockBudget) block right).val ≤
          path.length := by
      have hindex := (corridorBlockIndex
        (defectBudget := blockBudget) block right).isLt
      omega
    apply not_adj_getVert_of_length_eq_dist_of_add_one_lt
      path hgeodesic
      (corridorBlockIndex (defectBudget := blockBudget) block left).val
      (corridorBlockIndex (defectBudget := blockBudget) block right).val
      hleftBound hrightBound
    change block.val * corridorLength + left.val + 1 <
      block.val * corridorLength + right.val
    omega

/-- A hex corridor together with the computed fact that every face adjacent
to the corridor is also hexagonal. This is the radius-one defect-free slab
needed before local transfer states can be made translation invariant. -/
structure CleanOrbitHexCorridorSkeleton (RS : RotationSystem V E)
    (corridorLength : Nat) where
  toOrbitHexCorridorSkeleton : OrbitHexCorridorSkeleton RS corridorLength
  neighbor_hexagonal : ∀ offset : Fin corridorLength,
    ∀ neighbor : AmbientFace (Finset.univ : Finset (OrbitFace RS)),
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Adj
          (toOrbitHexCorridorSkeleton.faceAt offset) neighbor →
        (orbitFaceBoundary RS neighbor.1).card = 6

/-- The closed-defect-neighborhood block extraction produces a genuine clean
corridor skeleton. -/
theorem orbitFaceFullerene_exists_cleanHexCorridorSkeleton
    (RS : RotationSystem V E) (hsphere : SphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hfullerene : OrbitFaceFullerene RS)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (corridorLength : Nat) (hpositive : 0 < corridorLength)
    (hlarge : 7 ^ (85 * corridorLength - 1) <
      Fintype.card (OrbitFace RS)) :
    Nonempty (CleanOrbitHexCorridorSkeleton RS corridorLength) := by
  obtain ⟨start, finish, path, hpath, hgeodesic, hpositionBound,
      block, hclean⟩ :=
    orbitFaceFullerene_exists_cleanHexagonalGeodesicBlock
      RS hsphere htwoSided hfullerene hprimal hrotation
        corridorLength hpositive hlarge
  let corridor := OrbitHexCorridorSkeleton.ofPathBlockWithBudget
    RS path hpath hgeodesic 84 corridorLength hpositionBound block
      (fun offset => (hclean offset).1)
  exact ⟨{
    toOrbitHexCorridorSkeleton := corridor
    neighbor_hexagonal := fun offset neighbor hadj =>
      (hclean offset).2 neighbor hadj
  }⟩

/-- A sufficiently large cyclically five-edge-connected fullerene contains a
radius-one defect-free induced hex corridor. Its canonical rungs are distinct,
and every internal face has one of the two non-adjacent rung types. -/
theorem orbitFaceFullerene_exists_cleanInducedHexCorridor_with_twoRungTypes
    {G : SimpleGraph V} [DecidableRel G.Adj] (data : Data G)
    (hsphere : SphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hfullerene : OrbitFaceFullerene data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hcyclicFive : CyclicallyFiveEdgeConnected G)
    (corridorLength : Nat) (hpositive : 0 < corridorLength)
    (hlarge : 7 ^ (85 * corridorLength - 1) <
      Fintype.card (OrbitFace data.toRotationSystem)) :
    ∃ clean : CleanOrbitHexCorridorSkeleton
        data.toRotationSystem corridorLength,
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)),
        Function.Injective
          (clean.toOrbitHexCorridorSkeleton.rungEdge hunique) ∧
        ∀ offset : Fin (corridorLength - 2),
          (internalHexRungTypeWord clean.toOrbitHexCorridorSkeleton
            htwoSided hunique offset) ≠ HexRungType.adjacent := by
  have hprimal :
      (rotationPrimalGraph data.toRotationSystem).Connected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  obtain ⟨clean⟩ := orbitFaceFullerene_exists_cleanHexCorridorSkeleton
    data.toRotationSystem hsphere htwoSided hfullerene hprimal hrotation
      corridorLength hpositive hlarge
  have hunique :=
    pairwiseUniqueSharedInteriorEdges_of_cyclicallyFiveEdgeConnected
      data htwoSided hconnected
        (OrbitSphericalCubicMapData.ofSphericalCubicMapData
          data.toRotationSystem hsphere)
        hrotation hcyclicFive
  let corridor := clean.toOrbitHexCorridorSkeleton
  exact ⟨clean, hunique,
    corridor.rungEdge_injective htwoSided hunique,
    fun offset =>
      GoertzelV24InducedHexCorridorTypes.InternalHexRungPlacement.rungType_ne_adjacent
        (internalHexRungPlacement corridor htwoSided hunique offset)
          hsphere.cubic hrotation htwoSided⟩

end

end GoertzelV24CleanHexCorridor

end Mettapedia.GraphTheory.FourColor
