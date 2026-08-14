import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailExactFourCellCollision
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairRetainedCrossAppend

/-!
# L1: source four-cell append with only retained cross collisions

Two exact adjacent windows are composed after loop erasure, and separation is
tested on the final simple candidates.  Endpoint parity remains explicit.  A
bad branch stores the actual branch assemblies, their canonical seam rebase,
and the face which survives in both candidates.

This is the strongest fail-closed four-cell transition so far.  It does not
repair the retained cross collision, iterate the transition, attach either end
cap, or close Fable flag L1.
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

private abbrev FirstStraightAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace firstPlacement firstIncomingBefore)
    (selectedPlacementSideFace firstPlacement firstIncomingAfter)
    (selectedPlacementSideFace secondPlacement
      firstSuccessor.rightOutgoingBefore)
    (selectedPlacementSideFace secondPlacement
      firstSuccessor.rightOutgoingAfter)

private abbrev FirstSwappedAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace firstPlacement firstIncomingBefore)
    (selectedPlacementSideFace firstPlacement firstIncomingAfter)
    (selectedPlacementSideFace secondPlacement
      firstSuccessor.rightOutgoingAfter)
    (selectedPlacementSideFace secondPlacement
      firstSuccessor.rightOutgoingBefore)

private abbrev LastStraightAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace thirdPlacement bridge.frame.rightAfter)
    (selectedPlacementSideFace thirdPlacement bridge.frame.rightBefore)
    (selectedPlacementSideFace fourthPlacement
      lastSuccessor.rightOutgoingBefore)
    (selectedPlacementSideFace fourthPlacement
      lastSuccessor.rightOutgoingAfter)

private abbrev LastSwappedAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace thirdPlacement bridge.frame.rightAfter)
    (selectedPlacementSideFace thirdPlacement bridge.frame.rightBefore)
    (selectedPlacementSideFace fourthPlacement
      lastSuccessor.rightOutgoingAfter)
    (selectedPlacementSideFace fourthPlacement
      lastSuccessor.rightOutgoingBefore)

private abbrev rebaseLastStraight
    (assembly : LastStraightAssembly (lastSuccessor := lastSuccessor)) :=
  rebaseAssemblyStart assembly
    (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
    (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm

private abbrev rebaseLastSwapped
    (assembly : LastSwappedAssembly (lastSuccessor := lastSuccessor)) :=
  rebaseAssemblyStart assembly
    (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
    (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm

/-- Four-cell result after testing the supports which actually survive bypass.
The four collision constructors retain the exact endpoint-parity branch. -/
inductive ExactSelectedLocalRailFourCellRetainedOutcome
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter))
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore))
  | straightStraightCollision
      (firstAssembly : FirstStraightAssembly (firstSuccessor := firstSuccessor))
      (lastAssembly : LastStraightAssembly (lastSuccessor := lastSuccessor))
      (hfirst : firstWindow.outcome = .straight firstAssembly)
      (hlast : lastWindow.outcome = .straight lastAssembly)
      (collision : RetainedBypassCrossCollision firstAssembly
        (rebaseLastStraight (firstSuccessor := firstSuccessor) (bridge := bridge)
          lastAssembly))
  | straightSwappedCollision
      (firstAssembly : FirstStraightAssembly (firstSuccessor := firstSuccessor))
      (lastAssembly : LastSwappedAssembly (lastSuccessor := lastSuccessor))
      (hfirst : firstWindow.outcome = .straight firstAssembly)
      (hlast : lastWindow.outcome = .swapped lastAssembly)
      (collision : RetainedBypassCrossCollision firstAssembly
        (rebaseLastSwapped (firstSuccessor := firstSuccessor) (bridge := bridge)
          lastAssembly))
  | swappedStraightCollision
      (firstAssembly : FirstSwappedAssembly (firstSuccessor := firstSuccessor))
      (lastAssembly : LastStraightAssembly (lastSuccessor := lastSuccessor))
      (hfirst : firstWindow.outcome = .swapped firstAssembly)
      (hlast : lastWindow.outcome = .straight lastAssembly)
      (collision : CrossedRetainedBypassCrossCollision firstAssembly
        (rebaseLastStraight (firstSuccessor := firstSuccessor) (bridge := bridge)
          lastAssembly))
  | swappedSwappedCollision
      (firstAssembly : FirstSwappedAssembly (firstSuccessor := firstSuccessor))
      (lastAssembly : LastSwappedAssembly (lastSuccessor := lastSuccessor))
      (hfirst : firstWindow.outcome = .swapped firstAssembly)
      (hlast : lastWindow.outcome = .swapped lastAssembly)
      (collision : CrossedRetainedBypassCrossCollision firstAssembly
        (rebaseLastSwapped (firstSuccessor := firstSuccessor) (bridge := bridge)
          lastAssembly))

/-- **L1 retained four-cell transition.** Loop erase first, then return only a
cross collision which survives in both final simple candidates. -/
noncomputable def classifyExactSelectedLocalRailFourCellRetained
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))) :
    ExactSelectedLocalRailFourCellRetainedOutcome firstWindow lastWindow :=
  match hfirst : firstWindow.outcome with
  | .straight firstAssembly =>
      match hlast : lastWindow.outcome with
      | .straight lastAssembly =>
          match classifyRetainedBypassAppend firstAssembly
              (rebaseLastStraight (firstSuccessor := firstSuccessor)
                (bridge := bridge) lastAssembly) with
          | .assembled assembly => .straight assembly
          | .collision collision => .straightStraightCollision
              firstAssembly lastAssembly hfirst hlast collision
      | .swapped lastAssembly =>
          match classifyRetainedBypassAppend firstAssembly
              (rebaseLastSwapped (firstSuccessor := firstSuccessor)
                (bridge := bridge) lastAssembly) with
          | .assembled assembly => .swapped assembly
          | .collision collision => .straightSwappedCollision
              firstAssembly lastAssembly hfirst hlast collision
  | .swapped firstAssembly =>
      match hlast : lastWindow.outcome with
      | .straight lastAssembly =>
          match classifyCrossedRetainedBypassAppend firstAssembly
              (rebaseLastStraight (firstSuccessor := firstSuccessor)
                (bridge := bridge) lastAssembly) with
          | .assembled assembly => .swapped assembly
          | .collision collision => .swappedStraightCollision
              firstAssembly lastAssembly hfirst hlast collision
      | .swapped lastAssembly =>
          match classifyCrossedRetainedBypassAppend firstAssembly
              (rebaseLastSwapped (firstSuccessor := firstSuccessor)
                (bridge := bridge) lastAssembly) with
          | .assembled assembly => .straight assembly
          | .collision collision => .swappedSwappedCollision
              firstAssembly lastAssembly hfirst hlast collision

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
