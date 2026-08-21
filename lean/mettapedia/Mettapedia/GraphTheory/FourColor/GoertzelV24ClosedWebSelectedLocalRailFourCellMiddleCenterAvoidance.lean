import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTerminalPreviousCenterAvoidance
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedFourCellSupport

/-!
# L1: middle-centre avoidance for a support-certified four-cell rail

A successful traced four-cell rail is supported in its two exact terminal
windows.  The preceding modules prove that the first window avoids its right
centre and that the last window avoids the centre immediately before it,
under the corresponding local no-double-edge conditions.  These are the same
middle centre.  Window support provenance therefore proves that neither
successful assembled rail contains it.

This is a source-local companion-separation ingredient.  It does not prove
the two cardinality premises, eliminate their double-edge branches, repair a
pointed collision, iterate the rolling transition, attach end caps, construct
separated crosscuts, or close Fable flag L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- Four terminal-support exclusions transport through the canonical
successful-window provenance. -/
theorem ExactSelectedLocalRailFourCellRetainedOutcome.not_successfulRailContains_of_window_avoids
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow)
    {face : SelectedFace (web := web)}
    (hprovenance : outcome.HasWindowSupportProvenance)
    (hfirstFirst : face ∉ firstWindow.toCertified.firstSupport)
    (hfirstSecond : face ∉ firstWindow.toCertified.secondSupport)
    (hlastFirst : face ∉ lastWindow.toCertified.firstSupport)
    (hlastSecond : face ∉ lastWindow.toCertified.secondSupport) :
    ¬ outcome.SuccessfulRailContains face := by
  cases outcome with
  | straight assembly | swapped assembly =>
      change
        SupportContainedInExactTerminalWindowPair firstWindow lastWindow
              assembly.firstRail.support ∧
            SupportContainedInExactTerminalWindowPair firstWindow lastWindow
              assembly.secondRail.support at hprovenance
      change ¬ (face ∈ assembly.firstRail.support ∨
        face ∈ assembly.secondRail.support)
      intro hcontains
      rcases hcontains with hfirst | hsecond
      · rcases hprovenance.1 face hfirst with
          hfirstFirstMem | hfirstSecondMem | hlastFirstMem | hlastSecondMem
        · exact hfirstFirst hfirstFirstMem
        · exact hfirstSecond hfirstSecondMem
        · exact hlastFirst hlastFirstMem
        · exact hlastSecond hlastSecondMem
      · rcases hprovenance.2 face hsecond with
          hfirstFirstMem | hfirstSecondMem | hlastFirstMem | hlastSecondMem
        · exact hfirstFirst hfirstFirstMem
        · exact hfirstSecond hfirstSecondMem
        · exact hlastFirst hlastFirstMem
        · exact hlastSecond hlastSecondMem
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.SuccessfulRailContains]
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.SuccessfulRailContains]
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.SuccessfulRailContains]
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.SuccessfulRailContains]

/-- **L1 four-cell middle-centre avoidance.**  Under the two literal local
no-double-edge conditions, no successful rail returned by the support-
certified four-cell transition contains its second Cell--3 centre. -/
theorem SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.secondCenter_not_successfulRailContains_of_card_le_one
    (packet : SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft))
    (hfirstCard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        firstInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior firstInterior hfirstNext).center).1).card ≤ 1)
    (hsecondCard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior firstInterior hfirstNext).center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center).1).card
        ≤ 1) :
    ¬ packet.transition.outcome.SuccessfulRailContains
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) := by
  apply packet.transition.outcome.not_successfulRailContains_of_window_avoids
    packet.hasWindowSupportProvenance
  · exact packet.transition.firstTrace.toExactTerminalWindow
      |>.rightCenter_not_mem_firstSupport_of_card_le_one hfirstCard
  · exact packet.transition.firstTrace.toExactTerminalWindow
      |>.rightCenter_not_mem_secondSupport_of_card_le_one hfirstCard
  · exact packet.transition.lastTrace.toExactTerminalWindow
      |>.previousCenter_not_mem_firstSupport_of_card_le_one secondPlacement
        hsecondCard
  · exact packet.transition.lastTrace.toExactTerminalWindow
      |>.previousCenter_not_mem_secondSupport_of_card_le_one secondPlacement
        hsecondCard

/-- A straight successful four-cell outcome exposes the middle-centre
avoidance separately on both realized rails. -/
theorem SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.secondCenter_not_mem_straight_supports_of_card_le_one
    (packet : SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft))
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)
      (selectedPlacementSideFace fourthPlacement
        lastSuccessor.rightOutgoingBefore)
      (selectedPlacementSideFace fourthPlacement
        lastSuccessor.rightOutgoingAfter))
    (houtcome : packet.transition.outcome = .straight assembly)
    (hfirstCard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        firstInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior firstInterior hfirstNext).center).1).card ≤ 1)
    (hsecondCard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior firstInterior hfirstNext).center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center).1).card
        ≤ 1) :
    (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center ∉
        assembly.firstRail.support) ∧
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center ∉
        assembly.secondRail.support) := by
  have havoid := packet.secondCenter_not_successfulRailContains_of_card_le_one
    hfirstCard hsecondCard
  constructor
  · intro hmem
    apply havoid
    rw [houtcome]
    exact Or.inl hmem
  · intro hmem
    apply havoid
    rw [houtcome]
    exact Or.inr hmem

/-- A swapped successful four-cell outcome exposes the middle-centre
avoidance separately on both realized rails. -/
theorem SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.secondCenter_not_mem_swapped_supports_of_card_le_one
    (packet : SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft))
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)
      (selectedPlacementSideFace fourthPlacement
        lastSuccessor.rightOutgoingAfter)
      (selectedPlacementSideFace fourthPlacement
        lastSuccessor.rightOutgoingBefore))
    (houtcome : packet.transition.outcome = .swapped assembly)
    (hfirstCard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        firstInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior firstInterior hfirstNext).center).1).card ≤ 1)
    (hsecondCard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior firstInterior hfirstNext).center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center).1).card
        ≤ 1) :
    (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center ∉
        assembly.firstRail.support) ∧
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center ∉
        assembly.secondRail.support) := by
  have havoid := packet.secondCenter_not_successfulRailContains_of_card_le_one
    hfirstCard hsecondCard
  constructor
  · intro hmem
    apply havoid
    rw [houtcome]
    exact Or.inl hmem
  · intro hmem
    apply havoid
    rw [houtcome]
    exact Or.inr hmem

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
