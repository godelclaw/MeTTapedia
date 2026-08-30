import Mathlib.Data.Fin.Rev
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshGlobalSites

/-!
# Shared side carriers for neighbouring ordered-mesh cells

Neighbouring coordinate rectangles traverse their common side in opposite
directions.  This file gives the exact reversal equivalences and proves that
both traversals select the same globally indexed mesh steps.  Consequently
they also select definitionally the same global Kempe sites.

This is carrier coherence only.  It does not assert flatness, a cell
factorization, or wall exclusion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshSharedSides

open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshAdjacentPairSites
open GoertzelV24OrderedMeshBoundaryWalk
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

variable
  (rotation : Data G)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a b)

/-- Two cells share a vertical side and the same row interval. -/
structure HorizontalNeighbours (left right : CellIndex a b) : Prop where
  topRow_eq : left.topRow = right.topRow
  bottomRow_eq : left.bottomRow = right.bottomRow
  seamCol_eq : left.rightCol = right.leftCol

/-- Two cells share a horizontal side and the same column interval. -/
structure VerticalNeighbours (top bottom : CellIndex a b) : Prop where
  leftCol_eq : top.leftCol = bottom.leftCol
  rightCol_eq : top.rightCol = bottom.rightCol
  seamRow_eq : top.bottomRow = bottom.topRow

/-! ## Arithmetic of opposite side orientations -/

theorem interval_forward_eq_reverse
    {lower upper position : Nat}
    (hstrict : lower < upper)
    (hposition : position < upper - lower) :
    lower + position =
      upper - 1 - ((upper - lower) - (position + 1)) := by
  omega

theorem interval_reverse_eq_forward
    {lower upper position : Nat}
    (hstrict : lower < upper)
    (hposition : position < upper - lower) :
    upper - 1 - position =
      lower + ((upper - lower) - (position + 1)) := by
  omega

theorem eastLength_eq_westLength
    {left right : CellIndex a b}
    (adjacent : HorizontalNeighbours left right) :
    eastLength rotation ordered left = westLength rotation ordered right := by
  unfold eastLength westLength
  rw [adjacent.topRow_eq, adjacent.bottomRow_eq, adjacent.seamCol_eq]

theorem southLength_eq_northLength
    {top bottom : CellIndex a b}
    (adjacent : VerticalNeighbours top bottom) :
    southLength rotation ordered top = northLength rotation ordered bottom := by
  unfold southLength northLength
  rw [adjacent.leftCol_eq, adjacent.rightCol_eq, adjacent.seamRow_eq]

/-- Reverse the clockwise east traversal of the left cell into the clockwise
west traversal of the right cell. -/
def eastWestPositionEquiv
    {left right : CellIndex a b}
    (adjacent : HorizontalNeighbours left right) :
    Fin (eastLength rotation ordered left) ≃
      Fin (westLength rotation ordered right) :=
  Fin.revPerm.trans
    (finCongr (eastLength_eq_westLength rotation ordered adjacent))

/-- Reverse the clockwise south traversal of the top cell into the clockwise
north traversal of the bottom cell. -/
def southNorthPositionEquiv
    {top bottom : CellIndex a b}
    (adjacent : VerticalNeighbours top bottom) :
    Fin (southLength rotation ordered top) ≃
      Fin (northLength rotation ordered bottom) :=
  Fin.revPerm.trans
    (finCongr (southLength_eq_northLength rotation ordered adjacent))

/-- Neighbouring east/west traversals identify the same global column step. -/
theorem boundaryToGlobalStep_east_eq_west
    {left right : CellIndex a b}
    (adjacent : HorizontalNeighbours left right)
    (position : Fin (eastLength rotation ordered left)) :
    boundaryToGlobalStep rotation ordered left (.east position) =
      boundaryToGlobalStep rotation ordered right
        (.west (eastWestPositionEquiv rotation ordered adjacent position)) := by
  simp only [boundaryToGlobalStep]
  apply congrArg Sum.inr
  apply Sigma.ext adjacent.seamCol_eq
  apply (Fin.heq_ext_iff (congrArg
    (fun col => (ordered.toMesh.col col).len) adjacent.seamCol_eq)).mpr
  simp only [eastPathStep, westPathStep, eastWestPositionEquiv,
    Equiv.trans_apply, Fin.revPerm_apply, finCongr_apply_coe, Fin.val_rev]
  have hbottom :
      (ordered.colBranchPosition left.bottomRow left.rightCol).val =
        (ordered.colBranchPosition right.bottomRow right.leftCol).val := by
    rw [adjacent.bottomRow_eq, adjacent.seamCol_eq]
  have hposition := position.isLt
  dsimp [eastLength] at hposition
  have hstrict := ordered.colBranchPosition_strictMono left.rightCol
    left.topRow_lt_bottomRow
  rw [← hbottom]
  simpa only [eastLength] using interval_forward_eq_reverse
    (show (ordered.colBranchPosition left.topRow left.rightCol).val <
      (ordered.colBranchPosition left.bottomRow left.rightCol).val from hstrict)
    hposition

/-- Neighbouring south/north traversals identify the same global row step. -/
theorem boundaryToGlobalStep_south_eq_north
    {top bottom : CellIndex a b}
    (adjacent : VerticalNeighbours top bottom)
    (position : Fin (southLength rotation ordered top)) :
    boundaryToGlobalStep rotation ordered top (.south position) =
      boundaryToGlobalStep rotation ordered bottom
        (.north (southNorthPositionEquiv rotation ordered adjacent position)) := by
  simp only [boundaryToGlobalStep]
  apply congrArg Sum.inl
  apply Sigma.ext adjacent.seamRow_eq
  apply (Fin.heq_ext_iff (congrArg
    (fun row => (ordered.toMesh.row row).len) adjacent.seamRow_eq)).mpr
  simp only [southPathStep, northPathStep, southNorthPositionEquiv,
    Equiv.trans_apply, Fin.revPerm_apply, finCongr_apply_coe, Fin.val_rev]
  have hleft :
      (ordered.rowBranchPosition top.bottomRow top.leftCol).val =
        (ordered.rowBranchPosition bottom.topRow bottom.leftCol).val := by
    rw [adjacent.seamRow_eq, adjacent.leftCol_eq]
  have hposition := position.isLt
  dsimp [southLength] at hposition
  have hstrict := ordered.rowBranchPosition_strictMono top.bottomRow
    top.leftCol_lt_rightCol
  rw [← hleft]
  simpa only [southLength] using interval_reverse_eq_forward
    (show (ordered.rowBranchPosition top.bottomRow top.leftCol).val <
      (ordered.rowBranchPosition top.bottomRow top.rightCol).val from hstrict)
    hposition

/-- The global steps along the east side of the left cell. -/
def eastGlobalStepSet (cell : CellIndex a b) :
    Finset (GlobalMeshStep rotation ordered) :=
  Finset.univ.image fun position =>
    boundaryToGlobalStep rotation ordered cell (.east position)

/-- The global steps along the west side of the right cell. -/
def westGlobalStepSet (cell : CellIndex a b) :
    Finset (GlobalMeshStep rotation ordered) :=
  Finset.univ.image fun position =>
    boundaryToGlobalStep rotation ordered cell (.west position)

/-- The global steps along the south side of the top cell. -/
def southGlobalStepSet (cell : CellIndex a b) :
    Finset (GlobalMeshStep rotation ordered) :=
  Finset.univ.image fun position =>
    boundaryToGlobalStep rotation ordered cell (.south position)

/-- The global steps along the north side of the bottom cell. -/
def northGlobalStepSet (cell : CellIndex a b) :
    Finset (GlobalMeshStep rotation ordered) :=
  Finset.univ.image fun position =>
    boundaryToGlobalStep rotation ordered cell (.north position)

theorem eastGlobalStepSet_eq_westGlobalStepSet
    {left right : CellIndex a b}
    (adjacent : HorizontalNeighbours left right) :
    eastGlobalStepSet rotation ordered left =
      westGlobalStepSet rotation ordered right := by
  classical
  ext step
  simp only [eastGlobalStepSet, westGlobalStepSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨position, rfl⟩
    exact ⟨eastWestPositionEquiv rotation ordered adjacent position,
      (boundaryToGlobalStep_east_eq_west
        rotation ordered adjacent position).symm⟩
  · rintro ⟨position, rfl⟩
    obtain ⟨preimage, rfl⟩ :=
      (eastWestPositionEquiv rotation ordered adjacent).surjective position
    exact ⟨preimage, boundaryToGlobalStep_east_eq_west
      rotation ordered adjacent preimage⟩

theorem southGlobalStepSet_eq_northGlobalStepSet
    {top bottom : CellIndex a b}
    (adjacent : VerticalNeighbours top bottom) :
    southGlobalStepSet rotation ordered top =
      northGlobalStepSet rotation ordered bottom := by
  classical
  ext step
  simp only [southGlobalStepSet, northGlobalStepSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨position, rfl⟩
    exact ⟨southNorthPositionEquiv rotation ordered adjacent position,
      (boundaryToGlobalStep_south_eq_north
        rotation ordered adjacent position).symm⟩
  · rintro ⟨position, rfl⟩
    obtain ⟨preimage, rfl⟩ :=
      (southNorthPositionEquiv rotation ordered adjacent).surjective position
    exact ⟨preimage, boundaryToGlobalStep_south_eq_north
      rotation ordered adjacent preimage⟩

variable
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)

/-- After forgetting boundary orientation, neighbouring east/west
occurrences use literally the same globally chosen forward site. -/
theorem selectedGlobalKempeSite_east_heq_west
    {left right : CellIndex a b}
    (adjacent : HorizontalNeighbours left right)
    (position : Fin (eastLength rotation ordered left)) :
    selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered left (.east position)) ≍
      selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered right
          (.west (eastWestPositionEquiv rotation ordered adjacent position))) := by
  rw [boundaryToGlobalStep_east_eq_west
    rotation ordered adjacent position]

/-- After forgetting boundary orientation, neighbouring south/north
occurrences use literally the same globally chosen forward site. -/
theorem selectedGlobalKempeSite_south_heq_north
    {top bottom : CellIndex a b}
    (adjacent : VerticalNeighbours top bottom)
    (position : Fin (southLength rotation ordered top)) :
    selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered top (.south position)) ≍
      selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered bottom
          (.north (southNorthPositionEquiv rotation ordered adjacent position))) := by
  rw [boundaryToGlobalStep_south_eq_north
    rotation ordered adjacent position]

end

end GoertzelV24OrderedMeshSharedSides

end Mettapedia.GraphTheory.FourColor
