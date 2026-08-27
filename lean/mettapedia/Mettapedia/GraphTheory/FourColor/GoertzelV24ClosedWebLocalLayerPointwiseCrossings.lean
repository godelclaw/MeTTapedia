import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularInteriorFaceUniqueness
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCorridorLayer

/-!
# Pointwise crossing receipts for a literal Cell-3 layer

`Formation.LocalLayerPair` already contains only geometric data: two simple
two-step facial-dual walks through consecutive corridor hexagons, with all four
visited faces certified as annular-interior.  This file turns precisely those
certificates into the pointwise crossing-edge receipt.  It does not ask for a
colouring, a closed web, or global uniqueness of face intersections.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointwiseTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrientedHexSlab
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace Formation

namespace LocalLayerPair

/-- The first literal local layer, now stated on the colouring-free formation
carrier. -/
noncomputable def firstWalk
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    (interiorDualGraph (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))).Walk
      layers.firstFace layers.secondFace :=
  SimpleGraph.Walk.cons layers.first_adjacent_center
    (SimpleGraph.Walk.cons layers.center_adjacent_second SimpleGraph.Walk.nil)

/-- The second literal local layer passes through the next corridor centre. -/
noncomputable def secondWalk
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    (interiorDualGraph (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))).Walk
      layers.firstFace layers.secondFace :=
  SimpleGraph.Walk.cons layers.first_adjacent_nextCenter
    (SimpleGraph.Walk.cons layers.nextCenter_adjacent_second SimpleGraph.Walk.nil)

/-- Every visited face of the first two-step walk is annular-interior. -/
theorem firstWalk_getVert_internal
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (index : Fin (layers.firstWalk.length + 1)) :
    (layers.firstWalk.getVert index.val).1 ∈
      formation.annular.cellulation.interiorFaces := by
  change Fin 3 at index
  fin_cases index
  · simpa [firstWalk] using layers.first_internal
  · simpa [firstWalk] using corridor.face_internal leftInterior.center
  · simpa [firstWalk] using layers.second_internal

/-- Every visited face of the second two-step walk is annular-interior. -/
theorem secondWalk_getVert_internal
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (index : Fin (layers.secondWalk.length + 1)) :
    (layers.secondWalk.getVert index.val).1 ∈
      formation.annular.cellulation.interiorFaces := by
  change Fin 3 at index
  fin_cases index
  · simpa [secondWalk] using layers.first_internal
  · simpa [secondWalk] using
      corridor.face_internal (nextCorridorInterior leftInterior hnext).center
  · simpa [secondWalk] using layers.second_internal

/-- Restricted annular face uniqueness supplies the exact first-walk receipt. -/
theorem firstWalkStepUnique
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    DualWalkStepUnique (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.firstWalk :=
  dualWalkStepUnique_of_getVert_interior formation.annular.cellulation hinterior
    layers.firstWalk layers.firstWalk_getVert_internal

/-- Restricted annular face uniqueness supplies the exact second-walk receipt. -/
theorem secondWalkStepUnique
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    DualWalkStepUnique (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.secondWalk :=
  dualWalkStepUnique_of_getVert_interior formation.annular.cellulation hinterior
    layers.secondWalk layers.secondWalk_getVert_internal

/-- The first local rail's primal crossing at a chosen step. -/
noncomputable def firstCrossingEdge
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (step : Fin layers.firstWalk.length) : G.edgeSet :=
  pointwiseDualWalkCrossingEdge (orbitFaceBoundary formation.annular.RS)
    (Finset.univ : Finset (OrbitFace formation.annular.RS)) layers.firstWalk
    (layers.firstWalkStepUnique hinterior) step

/-- The second local rail's primal crossing at a chosen step. -/
noncomputable def secondCrossingEdge
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (step : Fin layers.secondWalk.length) : G.edgeSet :=
  pointwiseDualWalkCrossingEdge (orbitFaceBoundary formation.annular.RS)
    (Finset.univ : Finset (OrbitFace formation.annular.RS)) layers.secondWalk
    (layers.secondWalkStepUnique hinterior) step

end LocalLayerPair

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
