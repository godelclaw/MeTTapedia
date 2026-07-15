import Mettapedia.GraphTheory.FourColor.GoertzelV24CurvatureScope

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BulkCorridor

open GoertzelV24CurvatureScope

/-- Number of nonhexagonal entries in a multiset of face lengths. -/
def nonHexagonalFaceCount (faceLengths : Multiset Nat) : Nat :=
  (faceLengths.filter fun length => length ≠ 6).card

/-- Face-size multiset of an indexed corridor axis, retaining repeated
positions. -/
def corridorFaceSizeMultiset
    {length : Nat} (faceSize : Fin length → Nat) : Multiset Nat :=
  Finset.univ.val.map faceSize

/-- Defect positions along a proposed corridor axis. -/
def corridorDefectPositions
    {length : Nat} (faceSize : Fin length → Nat) : Finset (Fin length) :=
  Finset.univ.filter fun position => faceSize position ≠ 6

theorem mem_corridorDefectPositions_iff
    {length : Nat} (faceSize : Fin length → Nat) (position : Fin length) :
    position ∈ corridorDefectPositions faceSize ↔ faceSize position ≠ 6 := by
  simp [corridorDefectPositions]

/-- The indexed defect count is exactly the nonhexagonal count of its
position-preserving face-size multiset. -/
theorem card_corridorDefectPositions_eq_nonHexagonalFaceCount
    {length : Nat} (faceSize : Fin length → Nat) :
    (corridorDefectPositions faceSize).card =
      nonHexagonalFaceCount (corridorFaceSizeMultiset faceSize) := by
  unfold corridorDefectPositions
  rw [Finset.card_def, Finset.filter_val]
  unfold nonHexagonalFaceCount corridorFaceSizeMultiset
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- Under the fullerene restriction, nonhexagonal faces are exactly the
pentagons. -/
theorem nonHexagonalFaceCount_eq_pentagonCount_of_fullerene
    (faceLengths : Multiset Nat)
    (hfullerene : FaceCycleFullereneRestriction faceLengths) :
    nonHexagonalFaceCount faceLengths = faceLengths.count 5 := by
  induction faceLengths using Multiset.induction_on with
  | empty => simp [nonHexagonalFaceCount]
  | cons length rest ih =>
      have hlength := hfullerene length (by simp)
      have hrest : FaceCycleFullereneRestriction rest := by
        intro other hother
        exact hfullerene other (by simp [hother])
      have htail := ih hrest
      unfold nonHexagonalFaceCount at htail
      rcases hlength with rfl | rfl <;>
        simp [nonHexagonalFaceCount, htail]

/-- A cellular cubic fullerene sphere has exactly twelve nonhexagonal face
cycles, counted with facial-cycle multiplicity. -/
theorem faceCycleNonHexagonalFaceCount_eq_twelve_of_fullerene
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hsphere : SphericalCubicMapData RS)
    (hfullerene : FaceCycleFullereneRestriction (faceCycleLengths RS)) :
    nonHexagonalFaceCount (faceCycleLengths RS) = 12 := by
  rw [nonHexagonalFaceCount_eq_pentagonCount_of_fullerene _ hfullerene]
  exact faceCyclePentagonCount_eq_twelve_of_fullerene RS hsphere hfullerene

theorem nonHexagonalFaceCount_le_of_le
    {axis global : Multiset Nat} (haxis : axis ≤ global) :
    nonHexagonalFaceCount axis ≤ nonHexagonalFaceCount global := by
  exact Multiset.card_le_card
    (Multiset.filter_le_filter (fun length => length ≠ 6) haxis)

/-- With face lengths at least five, every nonhexagonal face is either one
pentagon or consumes at least one unit of long-face negative curvature. -/
theorem nonHexagonalFaceCount_le_pentagonCount_add_negativeWeight
    (faceLengths : Multiset Nat)
    (hminimum : FaceCycleMinimumFive faceLengths) :
    nonHexagonalFaceCount faceLengths ≤
      faceLengths.count 5 + faceCycleNegativeCurvatureWeight faceLengths := by
  induction faceLengths using Multiset.induction_on with
  | empty => simp [nonHexagonalFaceCount, faceCycleNegativeCurvatureWeight]
  | cons length rest ih =>
      have hlength : 5 ≤ length := hminimum length (by simp)
      have hrest : FaceCycleMinimumFive rest := by
        intro other hother
        exact hminimum other (by simp [hother])
      have htail := ih hrest
      unfold nonHexagonalFaceCount faceCycleNegativeCurvatureWeight at htail ⊢
      simp only [Multiset.filter_cons, Multiset.map_cons,
        Multiset.sum_cons, Multiset.count_cons]
      by_cases hfive : length = 5
      · subst length
        norm_num at htail ⊢
        omega
      · by_cases hsix : length = 6
        · subst length
          simpa using htail
        · have hseven : 7 ≤ length := by omega
          have hnotfive : ¬ 5 = length := fun h => hfive h.symm
          rw [if_pos hsix, if_neg hnotfive]
          rw [Multiset.card_add, Multiset.card_singleton]
          have hexcess : 1 ≤ length - 6 := by omega
          omega

/-- Weighted-curvature scope gate for the number of nonhexagonal facial
cycles. The factor two accounts separately for the extra pentagons and the
long faces paid for by the same negative-curvature weight. -/
theorem faceCycleNonHexagonalFaceCount_le_twelve_add_twiceNegativeWeight
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hsphere : SphericalCubicMapData RS)
    (hminimum : FaceCycleMinimumFive (faceCycleLengths RS)) :
    nonHexagonalFaceCount (faceCycleLengths RS) ≤
      12 + 2 * faceCycleNegativeCurvatureWeight (faceCycleLengths RS) := by
  calc
    nonHexagonalFaceCount (faceCycleLengths RS) ≤
        (faceCycleLengths RS).count 5 +
          faceCycleNegativeCurvatureWeight (faceCycleLengths RS) :=
      nonHexagonalFaceCount_le_pentagonCount_add_negativeWeight
        _ hminimum
    _ = 12 + 2 * faceCycleNegativeCurvatureWeight (faceCycleLengths RS) := by
      rw [faceCyclePentagonCount_eq_twelve_add_negativeCurvatureWeight
        RS hsphere hminimum]
      omega

theorem faceCycleNonHexagonalFaceCount_le_of_negativeWeight_le
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hsphere : SphericalCubicMapData RS)
    (hminimum : FaceCycleMinimumFive (faceCycleLengths RS))
    (weightBound : Nat)
    (hweight : faceCycleNegativeCurvatureWeight (faceCycleLengths RS) ≤
      weightBound) :
    nonHexagonalFaceCount (faceCycleLengths RS) ≤ 12 + 2 * weightBound := by
  have hcount :=
    faceCycleNonHexagonalFaceCount_le_twelve_add_twiceNegativeWeight
      RS hsphere hminimum
  omega

/-- Position `offset` in block `block`, for `defectBudget + 1` consecutive
blocks of equal positive length. -/
def corridorBlockIndex
    {defectBudget blockLength : Nat}
    (block : Fin (defectBudget + 1)) (offset : Fin blockLength) :
    Fin ((defectBudget + 1) * blockLength) := by
  refine ⟨block.val * blockLength + offset.val, ?_⟩
  calc
    block.val * blockLength + offset.val <
        block.val * blockLength + blockLength :=
      Nat.add_lt_add_left offset.isLt _
    _ = (block.val + 1) * blockLength := by
      rw [Nat.add_mul]
      simp
    _ ≤ (defectBudget + 1) * blockLength :=
      Nat.mul_le_mul_right blockLength block.isLt

theorem corridorBlockIndex_val_div
    {defectBudget blockLength : Nat} (hblockLength : 0 < blockLength)
    (block : Fin (defectBudget + 1)) (offset : Fin blockLength) :
    (corridorBlockIndex block offset).val / blockLength = block.val := by
  change (block.val * blockLength + offset.val) / blockLength = block.val
  rw [Nat.mul_comm block.val blockLength,
    Nat.mul_add_div hblockLength block.val offset.val,
    Nat.div_eq_of_lt offset.isLt]
  simp

/-- Positions selected from distinct equal-length blocks are distinct,
regardless of their within-block offsets. -/
theorem corridorBlockIndex_injective_block
    {defectBudget blockLength : Nat} (hblockLength : 0 < blockLength)
    {left right : Fin (defectBudget + 1)}
    (leftOffset rightOffset : Fin blockLength)
    (hindex : corridorBlockIndex left leftOffset =
      corridorBlockIndex right rightOffset) :
    left = right := by
  apply Fin.ext
  have hquotient := congrArg
    (fun index : Fin ((defectBudget + 1) * blockLength) =>
      index.val / blockLength) hindex
  simpa [corridorBlockIndex_val_div hblockLength] using hquotient

/-- Curvature-to-bulk pigeonhole on an already supplied corridor axis. If at
most `B` positions are nonhexagonal, then among `B+1` consecutive blocks of
positive length `L`, one whole block consists of hexagons. -/
theorem exists_allHexagonalCorridorBlock
    (defectBudget blockLength : Nat) (hblockLength : 0 < blockLength)
    (faceSize : Fin ((defectBudget + 1) * blockLength) → Nat)
    (hdefects : (corridorDefectPositions faceSize).card ≤ defectBudget) :
    ∃ block : Fin (defectBudget + 1),
      ∀ offset : Fin blockLength,
        faceSize (corridorBlockIndex block offset) = 6 := by
  classical
  by_contra hnoBlock
  push Not at hnoBlock
  choose badOffset hbadOffset using hnoBlock
  let defects := corridorDefectPositions faceSize
  let selectedDefect : Fin (defectBudget + 1) → defects := fun block =>
    ⟨corridorBlockIndex block (badOffset block), by
      exact (mem_corridorDefectPositions_iff faceSize _).2
        (hbadOffset block)⟩
  have hinjective : Function.Injective selectedDefect := by
    intro left right hequal
    apply corridorBlockIndex_injective_block hblockLength
      (badOffset left) (badOffset right)
    exact congrArg Subtype.val hequal
  have hcard := Fintype.card_le_of_injective selectedDefect hinjective
  have htooMany : defectBudget + 1 ≤ defects.card := by
    simpa [defects, Fintype.card_fin, Fintype.card_coe] using hcard
  dsimp [defects] at htooMany
  omega

/-- Fullerene specialization: a twelve-defect budget forces an all-hexagonal
block among thirteen consecutive blocks of any positive prescribed length. -/
theorem exists_allHexagonalCorridorBlock_of_twelve_defects
    (blockLength : Nat) (hblockLength : 0 < blockLength)
    (faceSize : Fin (13 * blockLength) → Nat)
    (hdefects : (corridorDefectPositions faceSize).card ≤ 12) :
    ∃ block : Fin 13,
      ∀ offset : Fin blockLength,
        faceSize (corridorBlockIndex block offset) = 6 := by
  simpa using
    exists_allHexagonalCorridorBlock 12 blockLength hblockLength
      faceSize hdefects

/-- Curvature-to-axis L1 consequence in the fullerene scope. If the indexed
corridor positions embed as a submultiset of the actual facial cycles, then
thirteen blocks force one all-hexagonal block. The remaining geometric L1
work is to extract such a sufficiently long bounded-width axis. -/
theorem exists_allHexagonalCorridorBlock_of_fullerene_faceCycles
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hsphere : SphericalCubicMapData RS)
    (hfullerene : FaceCycleFullereneRestriction (faceCycleLengths RS))
    (blockLength : Nat) (hblockLength : 0 < blockLength)
    (faceSize : Fin (13 * blockLength) → Nat)
    (haxis : corridorFaceSizeMultiset faceSize ≤ faceCycleLengths RS) :
    ∃ block : Fin 13,
      ∀ offset : Fin blockLength,
        faceSize (corridorBlockIndex block offset) = 6 := by
  apply exists_allHexagonalCorridorBlock_of_twelve_defects
    blockLength hblockLength faceSize
  rw [card_corridorDefectPositions_eq_nonHexagonalFaceCount]
  calc
    nonHexagonalFaceCount (corridorFaceSizeMultiset faceSize) ≤
        nonHexagonalFaceCount (faceCycleLengths RS) :=
      nonHexagonalFaceCount_le_of_le haxis
    _ = 12 :=
      faceCycleNonHexagonalFaceCount_eq_twelve_of_fullerene
        RS hsphere hfullerene

/-- Weighted-curvature L1 alternative. A negative-curvature bound `B` gives
`12 + 2B` possible nonhexagonal facial cycles, so `13 + 2B` blocks along any
embedded corridor axis force an all-hexagonal block. -/
theorem exists_allHexagonalCorridorBlock_of_negativeWeight_le
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hsphere : SphericalCubicMapData RS)
    (hminimum : FaceCycleMinimumFive (faceCycleLengths RS))
    (weightBound : Nat)
    (hweight : faceCycleNegativeCurvatureWeight (faceCycleLengths RS) ≤
      weightBound)
    (blockLength : Nat) (hblockLength : 0 < blockLength)
    (faceSize : Fin (((12 + 2 * weightBound) + 1) * blockLength) → Nat)
    (haxis : corridorFaceSizeMultiset faceSize ≤ faceCycleLengths RS) :
    ∃ block : Fin ((12 + 2 * weightBound) + 1),
      ∀ offset : Fin blockLength,
        faceSize (corridorBlockIndex
          (defectBudget := 12 + 2 * weightBound) block offset) = 6 := by
  have hdefects : (corridorDefectPositions faceSize).card ≤
      12 + 2 * weightBound := by
    rw [card_corridorDefectPositions_eq_nonHexagonalFaceCount]
    calc
      nonHexagonalFaceCount (corridorFaceSizeMultiset faceSize) ≤
          nonHexagonalFaceCount (faceCycleLengths RS) :=
        nonHexagonalFaceCount_le_of_le haxis
      _ ≤ 12 + 2 * weightBound :=
        faceCycleNonHexagonalFaceCount_le_of_negativeWeight_le
          RS hsphere hminimum weightBound hweight
  exact exists_allHexagonalCorridorBlock
    (12 + 2 * weightBound) blockLength hblockLength faceSize hdefects

end GoertzelV24BulkCorridor

end Mettapedia.GraphTheory.FourColor
