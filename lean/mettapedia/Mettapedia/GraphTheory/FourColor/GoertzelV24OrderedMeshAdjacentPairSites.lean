import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonConstantOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeCell
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedInjectiveMeshWidthFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24RecoveredAdjacentPairData

/-!
# Adjacent-pair transport sites on an ordered mesh cell

The ordered mesh carrier records paths and the rectangular order of its
branch vertices.  This file connects that geometry to the adjacent-pair
Kempe interface.  Every path step is an ambient graph edge, hence determines
the canonical four-port deletion data in a graph-backed least
counterexample.  A consecutive coordinate rectangle selects four such steps
in boundary order, one anchored at each branch corner.

Minimality then supplies one rotation-ordered constant-word Kempe orbit at
each selected site.  Consequently every ordered mesh coordinate cell carries
a nonempty coherent overlap support.  No simplicity or disjointness of the
four intervening path segments, and no flatness, holonomy, or wall-exclusion
claim, is made: those are genuinely stronger geometric and global obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshAdjacentPairSites

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24FaceDualConnectedness
open GoertzelV24MeshIsoperimetry
open GoertzelV24MinimalTriangleFree
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Consecutive vertices of a mesh path are adjacent in the graph backing
the rotation system. -/
theorem meshPathStep_adjacent
    (rotation : Data G)
    (path : MeshPath (toMultigraph rotation.toRotationSystem))
    (step : Fin path.len) :
    G.Adj (path.vert step.castSucc) (path.vert step.succ) := by
  have hprimal :
      (rotationPrimalGraph rotation.toRotationSystem).Adj
        (path.vert step.castSucc) (path.vert step.succ) := by
    apply (step_iff_primal_adj rotation.toRotationSystem _ _).1
    exact ⟨path.edge step, by simp,
      path.edge_ends step⟩
  simpa only [rotationPrimalGraph_toRotationSystem_eq G rotation] using hprimal

/-- The forward orientation of a mesh-path step gives canonical ordered
four-port adjacent-pair data. -/
def adjacentPairDataAtStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (path : MeshPath (toMultigraph rotation.toRotationSystem))
    (step : Fin path.len) : AdjacentPairData G :=
  adjacentPairData rotation (meshPathStep_adjacent rotation path step)
    minimal.spherical.cubic minimal.vertexRotationCyclic
    (no_common_neighbor_of_vertexMinimalTaitCounterexample
      rotation minimal (meshPathStep_adjacent rotation path step))

/-- The reverse orientation of the same mesh-path step. -/
def adjacentPairDataAtStepReverse
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (path : MeshPath (toMultigraph rotation.toRotationSystem))
    (step : Fin path.len) : AdjacentPairData G :=
  adjacentPairData rotation (meshPathStep_adjacent rotation path step).symm
    minimal.spherical.cubic minimal.vertexRotationCyclic
    (no_common_neighbor_of_vertexMinimalTaitCounterexample
      rotation minimal (meshPathStep_adjacent rotation path step).symm)

/-- Consecutive row and column indices selecting one mesh-coordinate cell.
This does not assert that its four path segments bound an embedded disc. -/
structure CellIndex (a b : Nat) where
  topRow : Fin a
  bottomRow : Fin a
  leftCol : Fin b
  rightCol : Fin b
  row_succ : topRow.val + 1 = bottomRow.val
  col_succ : leftCol.val + 1 = rightCol.val

namespace CellIndex

variable {a b : Nat}

theorem topRow_lt_bottomRow (cell : CellIndex a b) :
    cell.topRow < cell.bottomRow := by
  have h := cell.row_succ
  omega

theorem leftCol_lt_rightCol (cell : CellIndex a b) :
    cell.leftCol < cell.rightCol := by
  have h := cell.col_succ
  omega

end CellIndex

variable {a b : Nat}
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a b)
  (cell : CellIndex a b)

/-- First row edge after the north-west branch position. -/
def northStep : Fin ((ordered.toMesh.row cell.topRow).len) :=
  ⟨(ordered.rowBranchPosition cell.topRow cell.leftCol).val, by
    have hltFin := ordered.rowBranchPosition_strictMono cell.topRow
      cell.leftCol_lt_rightCol
    have hlt :
        (ordered.rowBranchPosition cell.topRow cell.leftCol).val <
          (ordered.rowBranchPosition cell.topRow cell.rightCol).val := hltFin
    have hright :=
      (ordered.rowBranchPosition cell.topRow cell.rightCol).isLt
    omega⟩

/-- First column edge after the north-east branch position. -/
def eastStep : Fin ((ordered.toMesh.col cell.rightCol).len) :=
  ⟨(ordered.colBranchPosition cell.topRow cell.rightCol).val, by
    have hltFin := ordered.colBranchPosition_strictMono cell.rightCol
      cell.topRow_lt_bottomRow
    have hlt :
        (ordered.colBranchPosition cell.topRow cell.rightCol).val <
          (ordered.colBranchPosition cell.bottomRow cell.rightCol).val := hltFin
    have hbottom :=
      (ordered.colBranchPosition cell.bottomRow cell.rightCol).isLt
    omega⟩

/-- Last row edge before the south-east branch position. -/
def southStep : Fin ((ordered.toMesh.row cell.bottomRow).len) :=
  ⟨(ordered.rowBranchPosition cell.bottomRow cell.rightCol).val - 1, by
    have hltFin := ordered.rowBranchPosition_strictMono cell.bottomRow
      cell.leftCol_lt_rightCol
    have hlt :
        (ordered.rowBranchPosition cell.bottomRow cell.leftCol).val <
          (ordered.rowBranchPosition cell.bottomRow cell.rightCol).val := hltFin
    have hright :=
      (ordered.rowBranchPosition cell.bottomRow cell.rightCol).isLt
    omega⟩

/-- Last column edge before the south-west branch position. -/
def westStep : Fin ((ordered.toMesh.col cell.leftCol).len) :=
  ⟨(ordered.colBranchPosition cell.bottomRow cell.leftCol).val - 1, by
    have hltFin := ordered.colBranchPosition_strictMono cell.leftCol
      cell.topRow_lt_bottomRow
    have hlt :
        (ordered.colBranchPosition cell.topRow cell.leftCol).val <
          (ordered.colBranchPosition cell.bottomRow cell.leftCol).val := hltFin
    have hbottom :=
      (ordered.colBranchPosition cell.bottomRow cell.leftCol).isLt
    omega⟩

/-- Clockwise adjacent-pair site anchored at the north-west corner. -/
def northwestData : AdjacentPairData G :=
  adjacentPairDataAtStep rotation minimal
    (ordered.toMesh.row cell.topRow) (northStep rotation ordered cell)

/-- Clockwise adjacent-pair site anchored at the north-east corner. -/
def northeastData : AdjacentPairData G :=
  adjacentPairDataAtStep rotation minimal
    (ordered.toMesh.col cell.rightCol) (eastStep rotation ordered cell)

/-- Clockwise adjacent-pair site anchored at the south-east corner. -/
def southeastData : AdjacentPairData G :=
  adjacentPairDataAtStepReverse rotation minimal
    (ordered.toMesh.row cell.bottomRow) (southStep rotation ordered cell)

/-- Clockwise adjacent-pair site anchored at the south-west corner. -/
def southwestData : AdjacentPairData G :=
  adjacentPairDataAtStepReverse rotation minimal
    (ordered.toMesh.col cell.leftCol) (westStep rotation ordered cell)

theorem northwestData_firstVertex :
    (northwestData rotation minimal ordered cell).firstVertex =
      ordered.toMesh.branch cell.topRow cell.leftCol := by
  change (ordered.toMesh.row cell.topRow).vert
      (northStep rotation ordered cell).castSucc = _
  rw [← ordered.rowBranchPosition_spec cell.topRow cell.leftCol]
  congr 1

theorem northeastData_firstVertex :
    (northeastData rotation minimal ordered cell).firstVertex =
      ordered.toMesh.branch cell.topRow cell.rightCol := by
  change (ordered.toMesh.col cell.rightCol).vert
      (eastStep rotation ordered cell).castSucc = _
  rw [← ordered.colBranchPosition_spec cell.topRow cell.rightCol]
  congr 1

theorem southeastData_firstVertex :
    (southeastData rotation minimal ordered cell).firstVertex =
      ordered.toMesh.branch cell.bottomRow cell.rightCol := by
  change (ordered.toMesh.row cell.bottomRow).vert
      (southStep rotation ordered cell).succ = _
  rw [← ordered.rowBranchPosition_spec cell.bottomRow cell.rightCol]
  congr 1
  apply Fin.ext
  dsimp [southStep]
  have hltFin := ordered.rowBranchPosition_strictMono cell.bottomRow
    cell.leftCol_lt_rightCol
  have hlt :
      (ordered.rowBranchPosition cell.bottomRow cell.leftCol).val <
        (ordered.rowBranchPosition cell.bottomRow cell.rightCol).val := hltFin
  omega

theorem southwestData_firstVertex :
    (southwestData rotation minimal ordered cell).firstVertex =
      ordered.toMesh.branch cell.bottomRow cell.leftCol := by
  change (ordered.toMesh.col cell.leftCol).vert
      (westStep rotation ordered cell).succ = _
  rw [← ordered.colBranchPosition_spec cell.bottomRow cell.leftCol]
  congr 1
  apply Fin.ext
  dsimp [westStep]
  have hltFin := ordered.colBranchPosition_strictMono cell.leftCol
    cell.topRow_lt_bottomRow
  have hlt :
      (ordered.colBranchPosition cell.topRow cell.leftCol).val <
        (ordered.colBranchPosition cell.bottomRow cell.leftCol).val := hltFin
  omega

include minimal

/-- Every ordered mesh coordinate cell in a graph-backed least counterexample supplies
four rotation-ordered adjacent-pair orbits and a nonempty coherent cell
support.  The equalities anchor the selected sites at the four branch
corners. -/
theorem exists_nonempty_overlapKempeCellStateSupport :
    ∃ northwest northeast southeast southwest : AdjacentPairData G,
      northwest.firstVertex =
          ordered.toMesh.branch cell.topRow cell.leftCol ∧
      northeast.firstVertex =
          ordered.toMesh.branch cell.topRow cell.rightCol ∧
      southeast.firstVertex =
          ordered.toMesh.branch cell.bottomRow cell.rightCol ∧
      southwest.firstVertex =
          ordered.toMesh.branch cell.bottomRow cell.leftCol ∧
      ∃ northwestBase :
          (DeletedAdjacentPairGraph G northwest.firstVertex
            northwest.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G northwest.firstVertex
            northwest.secondVertex) northwestBase ∧
      ∃ northeastBase :
          (DeletedAdjacentPairGraph G northeast.firstVertex
            northeast.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G northeast.firstVertex
            northeast.secondVertex) northeastBase ∧
      ∃ southeastBase :
          (DeletedAdjacentPairGraph G southeast.firstVertex
            southeast.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G southeast.firstVertex
            southeast.secondVertex) southeastBase ∧
      ∃ southwestBase :
          (DeletedAdjacentPairGraph G southwest.firstVertex
            southwest.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G southwest.firstVertex
            southwest.secondVertex) southwestBase ∧
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.overlapKempeCellStateSupport
          northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase).Nonempty := by
  let northwestRaw := northwestData rotation minimal ordered cell
  let northeastRaw := northeastData rotation minimal ordered cell
  let southeastRaw := southeastData rotation minimal ordered cell
  let southwestRaw := southwestData rotation minimal ordered cell
  rcases northwestRaw.exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal
      rotation minimal with
    ⟨northwest, hnorthwestFirst, _, northwestBase,
      hnorthwestTait, _⟩
  rcases northeastRaw.exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal
      rotation minimal with
    ⟨northeast, hnortheastFirst, _, northeastBase,
      hnortheastTait, _⟩
  rcases southeastRaw.exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal
      rotation minimal with
    ⟨southeast, hsoutheastFirst, _, southeastBase,
      hsoutheastTait, _⟩
  rcases southwestRaw.exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal
      rotation minimal with
    ⟨southwest, hsouthwestFirst, _, southwestBase,
      hsouthwestTait, _⟩
  refine ⟨northwest, northeast, southeast, southwest,
    hnorthwestFirst.trans ?_, hnortheastFirst.trans ?_,
    hsoutheastFirst.trans ?_, hsouthwestFirst.trans ?_,
    northwestBase, hnorthwestTait,
    northeastBase, hnortheastTait,
    southeastBase, hsoutheastTait,
    southwestBase, hsouthwestTait, ?_⟩
  · exact northwestData_firstVertex rotation minimal ordered cell
  · exact northeastData_firstVertex rotation minimal ordered cell
  · exact southeastData_firstVertex rotation minimal ordered cell
  · exact southwestData_firstVertex rotation minimal ordered cell
  · exact GoertzelV24AdjacentPairInsertion.AdjacentPairData.overlapKempeCellStateSupport_nonempty
      northwest northeast southeast southwest
      northwestBase northeastBase southeastBase southwestBase
      hnorthwestTait hnortheastTait hsoutheastTait hsouthwestTait

end

end GoertzelV24OrderedMeshAdjacentPairSites

end Mettapedia.GraphTheory.FourColor
