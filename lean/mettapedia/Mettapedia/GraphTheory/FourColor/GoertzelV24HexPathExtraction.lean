import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedDegreePath
import Mettapedia.GraphTheory.FourColor.GoertzelV24BulkCorridor

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexPathExtraction

open GoertzelV24BoundedDegreePath
open GoertzelV24BulkCorridor

variable {Face Edge : Type*} [DecidableEq Face] [DecidableEq Edge]

/-- Nonhexagonal faces in an explicit finite face-incidence model. -/
def faceDefectSet (faceBoundary : Face → Finset Edge)
    (allFaces : Finset Face) : Finset Face :=
  allFaces.filter fun face => (faceBoundary face).card ≠ 6

omit [DecidableEq Face] [DecidableEq Edge] in
@[simp]
theorem mem_faceDefectSet_iff
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    (face : Face) :
    face ∈ faceDefectSet faceBoundary allFaces ↔
      face ∈ allFaces ∧ (faceBoundary face).card ≠ 6 := by
  simp [faceDefectSet]

omit [DecidableEq Face] in
/-- A simple dual path cannot encounter more distinct nonhexagonal positions
than exist in the ambient face set. The path is sampled only before its end,
so `getVert` does not enter its clamped range. -/
theorem card_pathDefectPositions_le_faceDefectSet
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    {start finish : AmbientFace allFaces}
    (path : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hpath : path.IsPath) (positionCount : Nat)
    (hpositionCount : positionCount ≤ path.length + 1) :
    (corridorDefectPositions fun position : Fin positionCount =>
      (faceBoundary (path.getVert position.val).1).card).card ≤
        (faceDefectSet faceBoundary allFaces).card := by
  classical
  let faceSize : Fin positionCount → Nat := fun position =>
    (faceBoundary (path.getVert position.val).1).card
  let pathDefects := corridorDefectPositions faceSize
  let globalDefects := faceDefectSet faceBoundary allFaces
  let pathFace : pathDefects → globalDefects := fun position => by
    have hdefect : faceSize position.1 ≠ 6 :=
      (mem_corridorDefectPositions_iff faceSize position.1).1 position.2
    exact ⟨(path.getVert position.1.val).1,
      (mem_faceDefectSet_iff faceBoundary allFaces _).2
        ⟨(path.getVert position.1.val).2, hdefect⟩⟩
  have hinjective : Function.Injective pathFace := by
    intro left right hfaces
    have hfaceValue : (path.getVert left.1.val).1 =
        (path.getVert right.1.val).1 := by
      have hvalue := congrArg (fun defect : globalDefects => defect.1) hfaces
      dsimp only [pathFace] at hvalue
      exact hvalue
    have hvertices : path.getVert left.1.val =
        path.getVert right.1.val :=
      Subtype.ext hfaceValue
    have hleftBound : left.1.val ≤ path.length := by
      have := left.1.isLt
      omega
    have hrightBound : right.1.val ≤ path.length := by
      have := right.1.isLt
      omega
    have hindices : left.1.val = right.1.val :=
      hpath.getVert_injOn
        (by simpa using hleftBound)
        (by simpa using hrightBound) hvertices
    apply Subtype.ext
    exact Fin.ext hindices
  have hcard := Fintype.card_le_of_injective pathFace hinjective
  simpa [faceSize, pathDefects, globalDefects] using hcard

omit [DecidableEq Face] in
/-- Defect-budget pigeonhole along an actual simple dual path. If the first
`(B+1)L` path vertices contain at most `B` nonhexagons, one of the `B+1`
consecutive length-`L` blocks is entirely hexagonal. -/
theorem exists_allHexagonalBlock_on_path
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    {start finish : AmbientFace allFaces}
    (path : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hpath : path.IsPath) (defectBudget blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hpathLength : (defectBudget + 1) * blockLength ≤ path.length + 1)
    (hdefects : (faceDefectSet faceBoundary allFaces).card ≤ defectBudget) :
    ∃ block : Fin (defectBudget + 1),
      ∀ offset : Fin blockLength,
        (faceBoundary
          (path.getVert
            (corridorBlockIndex
              (defectBudget := defectBudget) block offset).val).1).card = 6 := by
  let faceSize : Fin ((defectBudget + 1) * blockLength) → Nat :=
    fun position => (faceBoundary (path.getVert position.val).1).card
  apply exists_allHexagonalCorridorBlock
    defectBudget blockLength hblockLength faceSize
  exact (card_pathDefectPositions_le_faceDefectSet
    faceBoundary allFaces path hpath _ hpathLength).trans hdefects

/-- Effective curvature-to-hex-axis theorem in the explicit face-incidence
regime. In a connected patch of faces of size at most six, with at most `B`
nonhexagons, more than `7^((B+1)L-1)` faces force a geodesic dual path carrying
an all-hexagonal consecutive block of `L` vertices. The remaining L1 geometry
is the primal ladder realization around this block. -/
theorem connectedSixFaceDual_exists_allHexagonalGeodesicBlock
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    (hincidence : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hfaceSize : ∀ face ∈ allFaces, (faceBoundary face).card ≤ 6)
    (hconnected : (interiorDualGraph faceBoundary allFaces).Connected)
    (defectBudget blockLength : Nat) (hblockLength : 0 < blockLength)
    (hdefects : (faceDefectSet faceBoundary allFaces).card ≤ defectBudget)
    (hlarge : 7 ^ ((defectBudget + 1) * blockLength - 1) <
      allFaces.card) :
    ∃ start finish : AmbientFace allFaces,
      ∃ path : (interiorDualGraph faceBoundary allFaces).Walk start finish,
        path.IsPath ∧
          path.length =
            (interiorDualGraph faceBoundary allFaces).dist start finish ∧
          (defectBudget + 1) * blockLength ≤ path.length + 1 ∧
          ∃ block : Fin (defectBudget + 1),
            ∀ offset : Fin blockLength,
              (faceBoundary
                (path.getVert
                  (corridorBlockIndex
                    (defectBudget := defectBudget) block offset).val).1).card = 6 := by
  obtain ⟨start, finish, path, hpath, hgeodesic, hpathLength⟩ :=
    interiorDualGraph_exists_geodesicPath_length_ge_of_seven_pow_lt
      faceBoundary allFaces hincidence hfaceSize hconnected
      ((defectBudget + 1) * blockLength - 1) hlarge
  have hpositive : 0 < (defectBudget + 1) * blockLength :=
    Nat.mul_pos (by omega) hblockLength
  have hpositionCount : (defectBudget + 1) * blockLength ≤
      path.length + 1 := by
    omega
  obtain ⟨block, hblock⟩ := exists_allHexagonalBlock_on_path
    faceBoundary allFaces path hpath defectBudget blockLength
      hblockLength hpositionCount hdefects
  exact ⟨start, finish, path, hpath, hgeodesic,
    hpositionCount, block, hblock⟩

end GoertzelV24HexPathExtraction

end Mettapedia.GraphTheory.FourColor
