import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailConstructionTrace
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFourCellRetainedCrossAppend

/-!
# L1: canonical traced four-cell rail transition

The retained four-cell classifier previously accepted arbitrary exact
terminal windows.  That is useful algebraically, but too broad for the finite
source repair: an arbitrary inhabitant need not expose which canonical local
repair produced its rails.

This module runs the actual adjacent classifier on both two-cell windows and
on their intervening seam, retains all three proof-relevant construction
traces, and then runs the strongest post-bypass four-cell classifier.  Every
bad branch is packaged with the already-proved five-position geometry and
both literal source-piece envelopes.  The remaining case table can therefore
inspect the two terminal branches together with the canonical repair of the
middle seam, rather than reason about arbitrary certified windows.

This is a constructed transition packet, not collision elimination, a
rolling arbitrary-length transition, either end cap, or closure of Fable flag
L1.
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
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
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
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

private abbrev BridgeLeft :=
  firstSuccessor.rightRailsAsNextLeft bridge

/-- Collision localization predicate on the strongest four-cell outcome. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.HasLocalizedCollisionData
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow) : Prop :=
  match outcome with
  | .straight _ | .swapped _ => True
  | .straightStraightCollision _ _ _ _ collision
  | .straightSwappedCollision _ _ _ _ collision
  | .swappedStraightCollision _ _ _ _ collision
  | .swappedSwappedCollision _ _ _ _ collision =>
      ExactSelectedLocalRailFourCellRetainedCollisionData
        firstWindow lastWindow collision.face

/-- Every retained collision returned by the source four-cell classifier is
localized in the five four-centre positions and in both literal piece
envelopes. -/
theorem classifyExactSelectedLocalRailFourCellRetained_hasLocalizedCollisionData
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))) :
    (classifyExactSelectedLocalRailFourCellRetained firstWindow lastWindow
      |>.HasLocalizedCollisionData) := by
  cases hresult : classifyExactSelectedLocalRailFourCellRetained
      firstWindow lastWindow with
  | straight assembly => trivial
  | swapped assembly => trivial
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact straightStraightRetainedCollision_data hsource firstWindow lastWindow
        firstAssembly lastAssembly hfirst hlast collision
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact straightSwappedRetainedCollision_data hsource firstWindow lastWindow
        firstAssembly lastAssembly hfirst hlast collision
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact swappedStraightRetainedCollision_data hsource firstWindow lastWindow
        firstAssembly lastAssembly hfirst hlast collision
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact swappedSwappedRetainedCollision_data hsource firstWindow lastWindow
        firstAssembly lastAssembly hfirst hlast collision

/-- The canonical finite transition packet: both actual local construction
branches, their exact windows, and the post-bypass four-cell result. -/
structure ExactSelectedLocalRailTracedFourCellTransition where
  firstTrace : ExactSelectedLocalRailConstructionTrace firstSuccessor firstLeft
  bridgeTrace : ExactSelectedLocalRailConstructionTrace bridge
    (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))
  lastTrace : ExactSelectedLocalRailConstructionTrace lastSuccessor
    (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
  outcome : ExactSelectedLocalRailFourCellRetainedOutcome
    firstTrace.toExactTerminalWindow lastTrace.toExactTerminalWindow
  hasLocalizedCollisionData : outcome.HasLocalizedCollisionData

/-- Construct the traced four-cell packet from the two actual adjacent
classifiers and the source-realization geometry. -/
noncomputable def ExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor) :
    ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) := by
  let firstTrace := ExactSelectedLocalRailConstructionTrace.ofClassifier
    (successor := firstSuccessor) (left := firstLeft)
  let bridgeTrace := ExactSelectedLocalRailConstructionTrace.ofClassifier
    (successor := bridge)
    (left := BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))
  let lastTrace := ExactSelectedLocalRailConstructionTrace.ofClassifier
    (successor := lastSuccessor)
    (left := LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
  let outcome := classifyExactSelectedLocalRailFourCellRetained
    firstTrace.toExactTerminalWindow lastTrace.toExactTerminalWindow
  exact
    { firstTrace := firstTrace
      bridgeTrace := bridgeTrace
      lastTrace := lastTrace
      outcome := outcome
      hasLocalizedCollisionData :=
        classifyExactSelectedLocalRailFourCellRetained_hasLocalizedCollisionData
          hsource firstTrace.toExactTerminalWindow
            lastTrace.toExactTerminalWindow }

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
