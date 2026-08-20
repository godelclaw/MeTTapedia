import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSecondBandResolution
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailSeparation

/-!
# L1: remote exclusion of the second-band far endpoint

The shifted middle--last square repair has one honest residue: the collision
may be the requested far endpoint of the fourth-cell rail.  A legal selected
`0+2` shape can leave one rail stationary, so merely appending the next cell
does not uniformly move that endpoint.

Remote source separation gives the exact replacement for that false shortcut.
Once a future selected cell centre lies at least three positions beyond the
fourth-cell centre, either fourth-cell far endpoint is absent from both future
local rail supports.  The proof uses the four already-established remote
track-separation theorems; it does not add a separation hypothesis.

This is the endpoint-movement receipt needed by the rolling L1 construction.
It does not itself preserve the old prefix through intermediate appends,
construct the end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstPlacement : SelectedInternalHexRungPlacement corridor rungs firstInterior}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}
    {fourthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {futureInterior : CorridorInterior blockLength}
    {futurePlacement : SelectedInternalHexRungPlacement corridor rungs futureInterior}
    {futureIncomingBefore futureIncomingAfter futureOutgoingBefore futureOutgoingAfter :
      {position // position ∈ selectedPlacementSidePositions futurePlacement}}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- **L1 second-band endpoint movement.** A fourth-cell far endpoint is absent
from both selected rail tracks of every source cell whose centre is at least
three positions later.  This conclusion is derived from source geometry, not
carried as a construction hypothesis. -/
theorem SecondFourthFarEndpoint.not_mem_futureRailSupports
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {face : SelectedFace (web := web)}
    (endpoint : SecondFourthFarEndpoint
      (fourthPlacement := fourthPlacement) (lastSuccessor := lastSuccessor) face)
    (future : SelectedSourceLocalRailPaths futurePlacement
      futureIncomingBefore futureIncomingAfter futureOutgoingBefore futureOutgoingAfter)
    (hremote :
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center.val + 2 < futureInterior.center.val) :
    face ∉ future.firstRail.support ∧ face ∉ future.secondRail.support := by
  rcases endpoint with ⟨endpoint, _, _, _⟩ | ⟨endpoint, _, _, _⟩
  · subst face
    constructor
    · intro hfuture
      exact (List.disjoint_left.mp
        (SelectedSourceLocalRailPaths.firstRail_support_disjoint_firstRail_of_add_two_lt
          hsource lastSuccessor.rightRails.paths future hremote)
        lastSuccessor.rightRails.paths.firstRail.end_mem_support) hfuture
    · intro hfuture
      exact (List.disjoint_left.mp
        (SelectedSourceLocalRailPaths.firstRail_support_disjoint_secondRail_of_add_two_lt
          hsource lastSuccessor.rightRails.paths future hremote)
        lastSuccessor.rightRails.paths.firstRail.end_mem_support) hfuture
  · subst face
    constructor
    · intro hfuture
      exact (List.disjoint_left.mp
        (SelectedSourceLocalRailPaths.secondRail_support_disjoint_firstRail_of_add_two_lt
          hsource lastSuccessor.rightRails.paths future hremote)
        lastSuccessor.rightRails.paths.secondRail.end_mem_support) hfuture
    · intro hfuture
      exact (List.disjoint_left.mp
        (SelectedSourceLocalRailPaths.secondRail_support_disjoint_secondRail_of_add_two_lt
          hsource lastSuccessor.rightRails.paths future hremote)
        lastSuccessor.rightRails.paths.secondRail.end_mem_support) hfuture

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
