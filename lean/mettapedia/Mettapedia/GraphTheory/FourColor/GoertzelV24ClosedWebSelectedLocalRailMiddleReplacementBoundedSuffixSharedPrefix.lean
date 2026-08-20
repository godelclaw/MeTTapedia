import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixCommonSpan

/-!
# L1: freeze the prefix at the shared live-rail start

Consecutive local construction traces overlap on a complete selected rail
piece.  Their flattened outcomes therefore cannot be appended: doing so would
count that piece twice.  The correct rolling cut lies immediately before the
shared piece.

This module extends the old interior-frozen prefix only through the literal
left pair in the first live cell, then rebases its two finishing faces across
the already-proved successor-frame equalities.  The result ends exactly where
the common-span future transition begins.  Its interior support is frozen at
the first live centre, so it is a valid input to the next append classifier.

This is a constructed cut-point prefix, not the prefix-to-future append.  It
does not classify the future collision branches, iterate, attach either end
cap, construct dual crosscuts, or close Fable flag L1.
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

private abbrev CurrentState
    {firstStart secondStart :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)) :=
  BoundedLiveMiddleReplacementState
    (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext)
    (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
    (thirdPlacement := thirdPlacement) (fourthPlacement := fourthPlacement)
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) prefixAssembly

/-- A prefix cut exactly before the live rail shared by two consecutive local
construction traces, together with the future-separation invariant needed for
the next append. -/
structure BoundedLiveSharedRailPrefix
    {firstStart secondStart :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))} where
  assembly : SelectedSourceLocalRailAssembly (web := web)
    firstStart secondStart
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
  interiorSeparated : InteriorSeparatedFromFutureSelectedWindows
    (corridor := corridor) assembly firstInterior.center.val

/-- The shared-cut prefix together with the source decomposition which built
it.  This stronger packet is what a later collision-localization theorem must
consume: the weak prefix alone intentionally forgets whether a face came from
the old frozen assembly or from the first live rail pair. -/
structure SourceTiedBoundedLiveSharedRailPrefix
    {firstStart secondStart :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)) where
  toBounded : BoundedLiveSharedRailPrefix
    (corridor := corridor) (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (firstPlacement := firstPlacement)
    (secondPlacement := secondPlacement) (firstSuccessor := firstSuccessor)
    (firstStart := firstStart) (secondStart := secondStart)
  supportProvenance : AssemblySupportContainedInAssemblyPair
    prefixAssembly firstLeft.toAssembly toBounded.assembly

/-- The first live local pair is supported in the first adjacent selected
window. -/
private theorem firstLeft_supportedByFirstWindow
    (firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter) :
    SupportedBySelectedCenterPair (corridor := corridor) firstLeft.toAssembly
      firstInterior.center (nextCorridorInterior firstInterior hfirstNext).center := by
  constructor
  · intro face hface
    exact Or.inr (Or.inr (Or.inl
      (firstLeft.paths.firstRail_support_adjacent_center face hface)))
  · intro face hface
    exact Or.inr (Or.inr (Or.inl
      (firstLeft.paths.secondRail_support_adjacent_center face hface)))

/-- **L1 shared-cut constructor.** Extend only through the first local pair,
freeze that extension, and rename its endpoints across the literal seam. -/
theorem boundedLiveSharedRailPrefix_nonempty_ofState
    {firstStart secondStart :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    (state : CurrentState
      (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (thirdPlacement := thirdPlacement) (fourthPlacement := fourthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
      prefixAssembly) :
    Nonempty (SourceTiedBoundedLiveSharedRailPrefix
      (V := V) (G := G) (data := data) (coloring := coloring) (web := web)
      (blockLength := blockLength) (corridor := corridor) (rungs := rungs)
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (firstSuccessor := firstSuccessor)
      (firstIncomingBefore := firstIncomingBefore)
      (firstIncomingAfter := firstIncomingAfter) (firstLeft := firstLeft)
      prefixAssembly) := by
  let localAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter) :=
    firstLeft.toAssembly
  have hlocalNear : SupportedBySelectedCenterPair (corridor := corridor) localAssembly
      firstInterior.center
      (nextCorridorInterior firstInterior hfirstNext).center :=
    firstLeft_supportedByFirstWindow
    (corridor := corridor) (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) firstLeft
  have hfirstFirst := state.frozenPrefix.1 localAssembly.firstRail.support
    hlocalNear.1 state.gapToLive
  have hsecondSecond := state.frozenPrefix.2 localAssembly.secondRail.support
    hlocalNear.2 state.gapToLive
  have hfirstSecond := state.frozenPrefix.1 localAssembly.secondRail.support
    hlocalNear.2 state.gapToLive
  have hsecondFirst := state.frozenPrefix.2 localAssembly.firstRail.support
    hlocalNear.1 state.gapToLive
  have hfirstEndNotSecondTail :
      selectedPlacementSideFace firstPlacement firstIncomingBefore ∉
        localAssembly.secondRail.support.tail := by
    intro hmem
    exact (List.disjoint_left.mp localAssembly.firstRail_support_disjoint_secondRail
      localAssembly.firstRail.start_mem_support) (List.mem_of_mem_tail hmem)
  have hsecondEndNotFirstTail :
      selectedPlacementSideFace firstPlacement firstIncomingAfter ∉
        localAssembly.firstRail.support.tail := by
    intro hmem
    exact (List.disjoint_left.mp localAssembly.firstRail_support_disjoint_secondRail
      (List.mem_of_mem_tail hmem)) localAssembly.secondRail.start_mem_support
  have hfirstPath := walk_support_disjoint_tail_of_dropLast_disjoint
    prefixAssembly.firstRail localAssembly.firstRail localAssembly.firstRail_isPath hfirstFirst
  have hsecondPath := walk_support_disjoint_tail_of_dropLast_disjoint
    prefixAssembly.secondRail localAssembly.secondRail localAssembly.secondRail_isPath hsecondSecond
  have hfirstSecondTail :=
    walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
      prefixAssembly.firstRail localAssembly.secondRail hfirstSecond hfirstEndNotSecondTail
  have hsecondFirstTail :=
    walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
      prefixAssembly.secondRail localAssembly.firstRail hsecondFirst hsecondEndNotFirstTail
  have hlocalFirstFuture : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) firstInterior.center.val localAssembly.firstRail.support := by
    intro futureInterior hfutureNext futureSupport hfutureNear hgap
    exact supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
      state.source localAssembly.firstRail.support futureSupport hlocalNear.1 hfutureNear hgap
  have hlocalSecondFuture : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) firstInterior.center.val localAssembly.secondRail.support := by
    intro futureInterior hfutureNext futureSupport hfutureNear hgap
    exact supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
      state.source localAssembly.secondRail.support futureSupport hlocalNear.2 hfutureNear hgap
  have hlocalInterior : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) localAssembly firstInterior.center.val :=
    ⟨supportSeparatedFromFutureSelectedWindows_dropLast hlocalFirstFuture,
      supportSeparatedFromFutureSelectedWindows_dropLast hlocalSecondFuture⟩
  have hcutoffLe : state.cutoff ≤ firstInterior.center.val := by
    have hgapToLive := state.gapToLive
    omega
  let joined : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter) :=
    appendAssembly prefixAssembly localAssembly hfirstPath hsecondPath
      hfirstSecondTail hsecondFirstTail
  have hjointInterior : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) joined firstInterior.center.val :=
    appendAssembly_interiorSeparatedFromFuture prefixAssembly localAssembly
      hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
      state.frozenPrefix hlocalInterior hcutoffLe
  let rebased : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore) :=
    rebaseAssemblyFinish joined
      firstSuccessor.frame.leftBeforeFace_eq_rightAfterFace
      firstSuccessor.frame.leftAfterFace_eq_rightBeforeFace
  have hjointProvenance : AssemblySupportContainedInAssemblyPair
      prefixAssembly localAssembly joined := by
    constructor
    · intro face hface
      change face ∈
        (prefixAssembly.firstRail.append localAssembly.firstRail).support at hface
      rw [SimpleGraph.Walk.support_append] at hface
      rcases List.mem_append.mp hface with hold | hlocal
      · exact .inl hold
      · exact .inr (.inr (.inl (List.mem_of_mem_tail hlocal)))
    · intro face hface
      change face ∈
        (prefixAssembly.secondRail.append localAssembly.secondRail).support at hface
      rw [SimpleGraph.Walk.support_append] at hface
      rcases List.mem_append.mp hface with hold | hlocal
      · exact .inr (.inl hold)
      · exact .inr (.inr (.inr (List.mem_of_mem_tail hlocal)))
  have hrebasedProvenance : AssemblySupportContainedInAssemblyPair
      prefixAssembly localAssembly rebased := by
    constructor
    · intro face hface
      rw [rebaseAssemblyFinish_firstRail_support] at hface
      exact hjointProvenance.1 face hface
    · intro face hface
      rw [rebaseAssemblyFinish_secondRail_support] at hface
      exact hjointProvenance.2 face hface
  exact ⟨
    { toBounded :=
        { assembly := rebased
          interiorSeparated := by
            simpa [InteriorSeparatedFromFutureSelectedWindows, rebased] using
              hjointInterior }
      supportProvenance := hrebasedProvenance }⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
