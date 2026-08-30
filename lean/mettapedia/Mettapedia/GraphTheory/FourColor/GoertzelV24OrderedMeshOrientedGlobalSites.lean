import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairReversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshSharedSides

/-!
# Globally shared sites in clockwise cell-boundary orientation

The global mesh-step carrier chooses one forward adjacent-pair deletion and
one base colouring for every physical row or column step.  A clockwise cell
boundary traverses its north and east sides forward and its south and west
sides backward.  This file reuses the forward choice in the first two cases
and transports it through the canonical adjacent-pair reversal in the last
two.

Thus every cell-boundary occurrence receives an existing `BoundaryKempeSite`
without making another choice.  Neighbouring cells use the same physical
global site, with the expected reversal on exactly one side.  No flatness,
support equality, or wall-exclusion conclusion is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshOrientedGlobalSites

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairReversal
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshAdjacentPairSites
open GoertzelV24OrderedMeshBoundaryWalk
open GoertzelV24OrderedMeshGlobalSites
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
  (cell : CellIndex a b)

/-- The globally selected physical site, transported into the clockwise
orientation of one cell-boundary occurrence.  This is the only boundary-site
choice used by the global mesh construction. -/
noncomputable def orientedGlobalBoundaryKempeSite
    (step : CellBoundaryStep rotation ordered cell) :
    BoundaryKempeSite rotation minimal ordered cell step := by
  cases step with
  | north position =>
      let site := selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered cell (.north position))
      exact {
        data := site.data
        first_eq := by
          simpa [site, boundaryToGlobalStep, globalFirstVertex] using site.first_eq
        second_eq := by
          simpa [site, boundaryToGlobalStep, globalSecondVertex] using site.second_eq
        base := site.base
        baseTait := site.baseTait }
  | east position =>
      let site := selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered cell (.east position))
      exact {
        data := site.data
        first_eq := by
          simpa [site, boundaryToGlobalStep, globalFirstVertex] using site.first_eq
        second_eq := by
          simpa [site, boundaryToGlobalStep, globalSecondVertex] using site.second_eq
        base := site.base
        baseTait := site.baseTait }
  | south position =>
      let site := selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered cell (.south position))
      exact {
        data := reverse site.data
        first_eq := by
          simpa [site, boundaryToGlobalStep, globalSecondVertex] using site.second_eq
        second_eq := by
          simpa [site, boundaryToGlobalStep, globalFirstVertex] using site.first_eq
        base := reverseColoring site.data site.base
        baseTait := isTaitEdgeColoring_reverseColoring
          site.data site.base site.baseTait }
  | west position =>
      let site := selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered cell (.west position))
      exact {
        data := reverse site.data
        first_eq := by
          simpa [site, boundaryToGlobalStep, globalSecondVertex] using site.second_eq
        second_eq := by
          simpa [site, boundaryToGlobalStep, globalFirstVertex] using site.first_eq
        base := reverseColoring site.data site.base
        baseTait := isTaitEdgeColoring_reverseColoring
          site.data site.base site.baseTait }

@[simp] theorem orientedGlobalBoundaryKempeSite_north_data
    (position : Fin (northLength rotation ordered cell)) :
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (.north position)).data =
      (selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered cell (.north position))).data := by
  rfl

@[simp] theorem orientedGlobalBoundaryKempeSite_east_data
    (position : Fin (eastLength rotation ordered cell)) :
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (.east position)).data =
      (selectedGlobalKempeSite rotation minimal ordered
        (boundaryToGlobalStep rotation ordered cell (.east position))).data := by
  rfl

@[simp] theorem orientedGlobalBoundaryKempeSite_south_data
    (position : Fin (southLength rotation ordered cell)) :
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (.south position)).data =
      reverse
        (selectedGlobalKempeSite rotation minimal ordered
          (boundaryToGlobalStep rotation ordered cell (.south position))).data := by
  rfl

@[simp] theorem orientedGlobalBoundaryKempeSite_west_data
    (position : Fin (westLength rotation ordered cell)) :
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (.west position)).data =
      reverse
        (selectedGlobalKempeSite rotation minimal ordered
          (boundaryToGlobalStep rotation ordered cell (.west position))).data := by
  rfl

/-- Every oriented global boundary site has the literal clockwise endpoints
recorded by the cell-boundary carrier. -/
theorem orientedGlobalBoundaryKempeSite_endpoint_eq
    (step : CellBoundaryStep rotation ordered cell) :
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell step).data.firstVertex =
        (boundaryData rotation minimal ordered cell step).firstVertex ∧
      (orientedGlobalBoundaryKempeSite rotation minimal ordered cell step).data.secondVertex =
        (boundaryData rotation minimal ordered cell step).secondVertex :=
  ⟨(orientedGlobalBoundaryKempeSite rotation minimal ordered cell step).first_eq,
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell step).second_eq⟩

/-! ## Exact reversal across a shared side -/

/-- On a shared vertical side, the right cell's clockwise west site is the
canonical reversal of the left cell's clockwise east site. -/
theorem orientedGlobalBoundaryKempeSite_west_eq_reverse_east
    {left right : CellIndex a b}
    (adjacent : HorizontalNeighbours left right)
    (position : Fin (eastLength rotation ordered left)) :
    (orientedGlobalBoundaryKempeSite rotation minimal ordered right
      (.west (eastWestPositionEquiv rotation ordered adjacent position))).data =
      reverse
        (orientedGlobalBoundaryKempeSite rotation minimal ordered left
          (.east position)).data := by
  simp only [orientedGlobalBoundaryKempeSite_west_data,
    orientedGlobalBoundaryKempeSite_east_data]
  rw [← boundaryToGlobalStep_east_eq_west
    rotation ordered adjacent position]

/-- The base colouring on the west traversal is exactly the canonical
transport of the base used by the east traversal of the neighbouring cell. -/
theorem orientedGlobalBoundaryKempeSite_west_base_heq_reverse_east
    {left right : CellIndex a b}
    (adjacent : HorizontalNeighbours left right)
    (position : Fin (eastLength rotation ordered left)) :
    HEq
      (orientedGlobalBoundaryKempeSite rotation minimal ordered right
        (.west (eastWestPositionEquiv rotation ordered adjacent position))).base
      (reverseColoring
        (orientedGlobalBoundaryKempeSite rotation minimal ordered left
          (.east position)).data
        (orientedGlobalBoundaryKempeSite rotation minimal ordered left
          (.east position)).base) := by
  simp only [orientedGlobalBoundaryKempeSite]
  rw [← boundaryToGlobalStep_east_eq_west
    rotation ordered adjacent position]

/-- On a shared horizontal side, the top cell's clockwise south site is the
canonical reversal of the bottom cell's clockwise north site. -/
theorem orientedGlobalBoundaryKempeSite_south_eq_reverse_north
    {top bottom : CellIndex a b}
    (adjacent : VerticalNeighbours top bottom)
    (position : Fin (southLength rotation ordered top)) :
    (orientedGlobalBoundaryKempeSite rotation minimal ordered top
      (.south position)).data =
      reverse
        (orientedGlobalBoundaryKempeSite rotation minimal ordered bottom
          (.north (southNorthPositionEquiv
            rotation ordered adjacent position))).data := by
  simp only [orientedGlobalBoundaryKempeSite_south_data,
    orientedGlobalBoundaryKempeSite_north_data]
  rw [boundaryToGlobalStep_south_eq_north
    rotation ordered adjacent position]

/-- The base colouring on the south traversal is exactly the canonical
transport of the base used by the north traversal of the neighbouring cell. -/
theorem orientedGlobalBoundaryKempeSite_south_base_heq_reverse_north
    {top bottom : CellIndex a b}
    (adjacent : VerticalNeighbours top bottom)
    (position : Fin (southLength rotation ordered top)) :
    HEq
      (orientedGlobalBoundaryKempeSite rotation minimal ordered top
        (.south position)).base
      (reverseColoring
        (orientedGlobalBoundaryKempeSite rotation minimal ordered bottom
          (.north (southNorthPositionEquiv
            rotation ordered adjacent position))).data
        (orientedGlobalBoundaryKempeSite rotation minimal ordered bottom
          (.north (southNorthPositionEquiv
            rotation ordered adjacent position))).base) := by
  simp only [orientedGlobalBoundaryKempeSite]
  rw [boundaryToGlobalStep_south_eq_north
    rotation ordered adjacent position]

end

end GoertzelV24OrderedMeshOrientedGlobalSites

end Mettapedia.GraphTheory.FourColor
