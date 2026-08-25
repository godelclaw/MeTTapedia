import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailExactFourCellCollision
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairBypassAppend

/-!
# L1: loop-erased four-cell selected-rail transition

The generic bypass append removes all same-track revisits.  This module
specializes it to two exact consecutive terminal windows, preserving the
straight/swapped endpoint parity and the exact common face of either remaining
cross-track collision.

The returned cross collision is still an honest open branch.  This module does
not repair it, iterate the transition, attach either end cap, or close L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- Loop-erased four-cell composition, preserving endpoint parity and only
the two genuine cross-track failure kinds. -/
inductive ExactSelectedLocalRailFourCellBypassOutcome
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
  | orderedCrossCollision
      (witness : SelectedRailPairCrossCollision (web := web)
        firstWindow.toCertified.firstSupport
        firstWindow.toCertified.secondSupport
        lastWindow.toCertified.firstSupport
        lastWindow.toCertified.secondSupport)
  | crossedCrossCollision
      (witness : SelectedRailPairCrossCollision (web := web)
        firstWindow.toCertified.firstSupport
        firstWindow.toCertified.secondSupport
        lastWindow.toCertified.secondSupport
        lastWindow.toCertified.firstSupport)

/-- **L1 four-cell bypass transition.** Same-track revisits are erased before
the two exact windows are composed. -/
noncomputable def classifyExactSelectedLocalRailFourCellBypass
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))) :
    ExactSelectedLocalRailFourCellBypassOutcome firstWindow lastWindow :=
  match hfirst : firstWindow.outcome with
  | .straight firstAssembly =>
      match hlast : lastWindow.outcome with
      | .straight lastAssembly =>
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          match classifyAndAppendBypass firstAssembly rebased with
          | .assembled assembly => .straight assembly
          | .collision witness => .orderedCrossCollision (by
              have hfirstSupport : rebased.firstRail.support =
                  lastAssembly.firstRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_firstRail_support
              have hsecondSupport : rebased.secondRail.support =
                  lastAssembly.secondRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_secondRail_support
              rw [hfirstSupport, hsecondSupport] at witness
              simpa [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                CertifiedSelectedLocalRailTerminalWindow.firstSupport,
                CertifiedSelectedLocalRailTerminalWindow.secondSupport,
                hfirst, hlast] using witness)
      | .swapped lastAssembly =>
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          match classifyAndAppendBypass firstAssembly rebased with
          | .assembled assembly => .swapped assembly
          | .collision witness => .orderedCrossCollision (by
              have hfirstSupport : rebased.firstRail.support =
                  lastAssembly.firstRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_firstRail_support
              have hsecondSupport : rebased.secondRail.support =
                  lastAssembly.secondRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_secondRail_support
              rw [hfirstSupport, hsecondSupport] at witness
              simpa [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                CertifiedSelectedLocalRailTerminalWindow.firstSupport,
                CertifiedSelectedLocalRailTerminalWindow.secondSupport,
                hfirst, hlast] using witness)
  | .swapped firstAssembly =>
      match hlast : lastWindow.outcome with
      | .straight lastAssembly =>
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          match classifyAndAppendCrossedBypass firstAssembly rebased with
          | .assembled assembly => .swapped assembly
          | .collision witness => .crossedCrossCollision (by
              have hfirstSupport : rebased.firstRail.support =
                  lastAssembly.firstRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_firstRail_support
              have hsecondSupport : rebased.secondRail.support =
                  lastAssembly.secondRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_secondRail_support
              rw [hfirstSupport, hsecondSupport] at witness
              simpa [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                CertifiedSelectedLocalRailTerminalWindow.firstSupport,
                CertifiedSelectedLocalRailTerminalWindow.secondSupport,
                hfirst, hlast] using witness)
      | .swapped lastAssembly =>
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          match classifyAndAppendCrossedBypass firstAssembly rebased with
          | .assembled assembly => .straight assembly
          | .collision witness => .crossedCrossCollision (by
              have hfirstSupport : rebased.firstRail.support =
                  lastAssembly.firstRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_firstRail_support
              have hsecondSupport : rebased.secondRail.support =
                  lastAssembly.secondRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_secondRail_support
              rw [hfirstSupport, hsecondSupport] at witness
              simpa [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                CertifiedSelectedLocalRailTerminalWindow.firstSupport,
                CertifiedSelectedLocalRailTerminalWindow.secondSupport,
                hfirst, hlast] using witness)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
