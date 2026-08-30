import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairStateReversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshOrientedGlobalSites

/-!
# Boundary-state coherence across ordered-mesh cells

The global physical-site construction identifies the adjacent-pair deletion
used by two cells on a shared side.  The two clockwise cell traversals have
opposite orientations.  This file lifts that carrier identification to the
complete finite boundary Kempe state: neighbouring cells read the same state
through the proved involutive port reversal.

No relation between different physical sides, flatness, cancellation, or wall
exclusion is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshSharedBoundaryStates

open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairStateReversal
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshAdjacentPairSites
open GoertzelV24OrderedMeshBoundaryWalk
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshOrientedGlobalSites
open GoertzelV24OrderedMeshSharedSides
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
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a b)

/-- The complete finite state read at one clockwise cell-boundary site. -/
def orientedGlobalBoundaryKempeState
    (cell : CellIndex a b)
    (step : CellBoundaryStep rotation ordered cell) : BoundaryKempeState :=
  boundaryKempeState
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell step).data
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell step).base

/-- Across a shared vertical side, the west-facing cell reads exactly the
reversal of the east-facing cell's complete finite boundary state. -/
theorem west_boundaryKempeState_eq_reverse_east
    {left right : CellIndex a b}
    (adjacent : HorizontalNeighbours left right)
    (position : Fin (eastLength rotation ordered left)) :
    orientedGlobalBoundaryKempeState rotation minimal ordered right
        (.west (eastWestPositionEquiv rotation ordered adjacent position)) =
      reverseBoundaryKempeState
        (orientedGlobalBoundaryKempeState rotation minimal ordered left
          (.east position)) := by
  unfold orientedGlobalBoundaryKempeState
  apply boundaryKempeState_eq_reverse_of_data_eq_of_base_heq
  · exact orientedGlobalBoundaryKempeSite_west_eq_reverse_east
      rotation minimal ordered adjacent position
  · exact orientedGlobalBoundaryKempeSite_west_base_heq_reverse_east
      rotation minimal ordered adjacent position

/-- Across a shared horizontal side, the south-facing cell reads exactly the
reversal of the north-facing cell's complete finite boundary state. -/
theorem south_boundaryKempeState_eq_reverse_north
    {top bottom : CellIndex a b}
    (adjacent : VerticalNeighbours top bottom)
    (position : Fin (southLength rotation ordered top)) :
    orientedGlobalBoundaryKempeState rotation minimal ordered top
        (.south position) =
      reverseBoundaryKempeState
        (orientedGlobalBoundaryKempeState rotation minimal ordered bottom
          (.north (southNorthPositionEquiv
            rotation ordered adjacent position))) := by
  unfold orientedGlobalBoundaryKempeState
  apply boundaryKempeState_eq_reverse_of_data_eq_of_base_heq
  · exact orientedGlobalBoundaryKempeSite_south_eq_reverse_north
      rotation minimal ordered adjacent position
  · exact orientedGlobalBoundaryKempeSite_south_base_heq_reverse_north
      rotation minimal ordered adjacent position

end

end GoertzelV24OrderedMeshSharedBoundaryStates

end Mettapedia.GraphTheory.FourColor
