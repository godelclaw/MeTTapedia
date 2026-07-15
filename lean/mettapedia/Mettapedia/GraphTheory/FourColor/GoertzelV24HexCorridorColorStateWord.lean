import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorChiralityBarrier

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorColorStateWord

open GoertzelV24CleanHexCorridor
open GoertzelV24CorridorPumping
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorChiralityBarrier
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WindingClassification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The finite six-slot color state at every internal face of one actual
clean hex corridor, all extracted from the same ambient Tait coloring. -/
def hexCorridorColorStateWord
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    Fin (corridorLength - 2) → HexSlabColorState :=
  fun offset =>
    hexSlabColorStateOfPlacement
      (internalHexRungPlacement clean.toOrbitHexCorridorSkeleton
        htwoSided hunique offset) C hC

/-- An index in the `L-3` consecutive-pair range as the corresponding left
index in the `L-2` internal-face range. -/
def leftInternalOffset {corridorLength : Nat}
    (offset : Fin (corridorLength - 3)) : Fin (corridorLength - 2) :=
  ⟨offset.val, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    apply (Nat.lt_sub_iff_add_lt).2
    omega⟩

/-- The right internal-face index following `leftInternalOffset`. -/
def rightInternalOffset {corridorLength : Nat}
    (offset : Fin (corridorLength - 3)) : Fin (corridorLength - 2) :=
  ⟨offset.val + 1, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    apply (Nat.lt_sub_iff_add_lt).2
    omega⟩

theorem rightInternalOffset_eq_succ
    {corridorLength : Nat} (offset : Fin (corridorLength - 3)) :
    (rightInternalOffset offset).val = (leftInternalOffset offset).val + 1 :=
  rfl

/-- A relation holding between every consecutive entry of a finite indexed
word gives an exact relational transfer from its first to its last entry. -/
theorem exactRelationalTransfer_of_finChain
    {State : Type*} {oneStep : State → State → Prop}
    (length : Nat) (word : Fin (length + 1) → State)
    (hstep : ∀ offset : Fin length,
      oneStep
        (word ⟨offset.val, by omega⟩)
        (word ⟨offset.val + 1, by omega⟩)) :
    ExactRelationalTransfer oneStep length
      (word ⟨0, by omega⟩) (word ⟨length, by omega⟩) := by
  induction length with
  | zero =>
      exact ExactRelationalTransfer.zero _
  | succ tailLength ih =>
      let tailWord : Fin (tailLength + 1) → State :=
        fun offset => word ⟨offset.val + 1, by omega⟩
      have htailStep : ∀ offset : Fin tailLength,
          oneStep
            (tailWord ⟨offset.val, by omega⟩)
            (tailWord ⟨offset.val + 1, by omega⟩) := by
        intro offset
        exact hstep ⟨offset.val + 1, by omega⟩
      have htail := ih tailWord htailStep
      have hfirst := hstep ⟨0, by omega⟩
      simpa [tailWord] using ExactRelationalTransfer.succ hfirst htail

/-- The canonical interior record at the right offset is the `next` record
used by the local graph transition theorem. -/
theorem corridorInteriorOfOffset_right_eq_next
    {corridorLength : Nat} (offset : Fin (corridorLength - 3))
    (hnext : (corridorInteriorOfOffset (leftInternalOffset offset)).center.val +
      2 < corridorLength) :
    corridorInteriorOfOffset (rightInternalOffset offset) =
      nextCorridorInterior
        (corridorInteriorOfOffset (leftInternalOffset offset)) hnext := by
  have hcenter :
      (corridorInteriorOfOffset (rightInternalOffset offset)).center =
        (nextCorridorInterior
          (corridorInteriorOfOffset (leftInternalOffset offset)) hnext).center := by
    apply Fin.ext
    rfl
  cases hleft : corridorInteriorOfOffset (rightInternalOffset offset) with
  | mk leftCenter leftPositive leftSuccessor =>
    cases hright : nextCorridorInterior
        (corridorInteriorOfOffset (leftInternalOffset offset)) hnext with
    | mk rightCenter rightPositive rightSuccessor =>
      simp only [hleft, hright, CorridorInterior.mk.injEq] at hcenter ⊢
      exact hcenter

/-- Every adjacent pair in the graph-extracted state word satisfies the
finite oriented Tait transition. -/
theorem hexCorridorColorStateWord_step
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (offset : Fin (corridorLength - 3)) :
    FlankingTaitColorTransition
      (hexCorridorColorStateWord clean htwoSided hunique C hC
        (leftInternalOffset offset))
      (hexCorridorColorStateWord clean htwoSided hunique C hC
        (rightInternalOffset offset)) := by
  let leftOffset := leftInternalOffset offset
  let rightOffset := rightInternalOffset offset
  let leftInterior := corridorInteriorOfOffset leftOffset
  have hnext : leftInterior.center.val + 2 < corridorLength := by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    change offset.val + 1 + 2 < corridorLength
    omega
  have hinterior : corridorInteriorOfOffset rightOffset =
      nextCorridorInterior leftInterior hnext := by
    exact corridorInteriorOfOffset_right_eq_next offset hnext
  let leftPlacement := internalHexRungPlacement
    clean.toOrbitHexCorridorSkeleton htwoSided hunique leftOffset
  let rightPlacement := internalHexRungPlacement
    clean.toOrbitHexCorridorSkeleton htwoSided hunique rightOffset
  cases hinterior
  exact flankingTaitColorTransition_of_consecutivePlacements
    clean hcubic hrotation htwoSided hunique leftInterior hnext
      leftPlacement rightPlacement C hC

/-- First internal-face offset of a corridor of length at least three. -/
def firstInternalOffsetOfLength {corridorLength : Nat}
    (hlength : 3 ≤ corridorLength) : Fin (corridorLength - 2) :=
  ⟨0, by omega⟩

/-- Last internal-face offset of a corridor of length at least three. -/
def lastInternalOffsetOfLength {corridorLength : Nat}
    (hlength : 3 ≤ corridorLength) : Fin (corridorLength - 2) :=
  ⟨corridorLength - 3, by omega⟩

/-- The complete graph-extracted state word is an exact finite transfer path
from the first internal face to the last. -/
theorem hexCorridorColorStateWord_exactTransfer
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hlength : 3 ≤ corridorLength) :
    ExactRelationalTransfer FlankingTaitColorTransition (corridorLength - 3)
      (hexCorridorColorStateWord clean htwoSided hunique C hC
        (firstInternalOffsetOfLength hlength))
      (hexCorridorColorStateWord clean htwoSided hunique C hC
        (lastInternalOffsetOfLength hlength)) := by
  let transferLength := corridorLength - 3
  have hcard : transferLength + 1 = corridorLength - 2 := by
    dsimp [transferLength]
    omega
  let word : Fin (transferLength + 1) → HexSlabColorState :=
    fun offset => hexCorridorColorStateWord clean htwoSided hunique C hC
      (Fin.cast hcard offset)
  have hstep : ∀ offset : Fin transferLength,
      FlankingTaitColorTransition
        (word ⟨offset.val, by omega⟩)
        (word ⟨offset.val + 1, by omega⟩) := by
    intro offset
    have hraw := hexCorridorColorStateWord_step clean hcubic hrotation
      htwoSided hunique C hC
        (Fin.cast (by simp [transferLength]) offset)
    simpa [word, leftInternalOffset, rightInternalOffset] using hraw
  have hpath := exactRelationalTransfer_of_finChain
    transferLength word hstep
  have hfirstCast :
      Fin.cast hcard (⟨0, by omega⟩ : Fin (transferLength + 1)) =
        firstInternalOffsetOfLength hlength := by
    apply Fin.ext
    rfl
  have hlastCast :
      Fin.cast hcard
          (⟨transferLength, by omega⟩ : Fin (transferLength + 1)) =
        lastInternalOffsetOfLength hlength := by
    apply Fin.ext
    rfl
  have hfirstState : word ⟨0, by omega⟩ =
      hexCorridorColorStateWord clean htwoSided hunique C hC
        (firstInternalOffsetOfLength hlength) := by
    change hexCorridorColorStateWord clean htwoSided hunique C hC
      (Fin.cast hcard ⟨0, by omega⟩) = _
    rw [hfirstCast]
  have hlastState : word ⟨transferLength, by omega⟩ =
      hexCorridorColorStateWord clean htwoSided hunique C hC
        (lastInternalOffsetOfLength hlength) := by
    change hexCorridorColorStateWord clean htwoSided hunique C hC
      (Fin.cast hcard ⟨transferLength, by omega⟩) = _
    rw [hlastCast]
  rw [hfirstState, hlastState] at hpath
  simpa [transferLength] using hpath

/-- Opposite chiral endpoint faces of a real clean hex corridor force a
zero-winding state on the graph-extracted corridor path. -/
theorem hexCorridorColorStateWord_oppositeChirality_hasZeroWinding
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hlength : 3 ≤ corridorLength)
    (hopposite :
      let first := hexCorridorColorStateWord clean htwoSided hunique C hC
        (firstInternalOffsetOfLength hlength)
      let last := hexCorridorColorStateWord clean htwoSided hunique C hC
        (lastInternalOffsetOfLength hlength)
      (windingScore first.color = 6 ∧ windingScore last.color = -6) ∨
      (windingScore first.color = -6 ∧ windingScore last.color = 6)) :
    ∃ middle : HexSlabColorState,
      OccursOnExactFlankingTransfer (length := corridorLength - 3)
        (hexCorridorColorStateWord clean htwoSided hunique C hC
          (firstInternalOffsetOfLength hlength))
        (hexCorridorColorStateWord clean htwoSided hunique C hC
          (lastInternalOffsetOfLength hlength)) middle ∧
      windingScore middle.color = 0 :=
  exactFlankingTransfer_oppositeChirality_hasZeroWinding
    (hexCorridorColorStateWord_exactTransfer clean hcubic hrotation
      htwoSided hunique C hC hlength) hopposite

end

end GoertzelV24HexCorridorColorStateWord

end Mettapedia.GraphTheory.FourColor
