import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementFrozenPrepend

/-!
# L1: retain a bounded raw suffix beside the frozen rail prefix

The immediate middle-replacement recurrence cannot freeze its complete
four-cell result: its cutoff is the third centre, while the next block begins
at the adjacent fourth centre.  The gap required by the frozen-prefix API is
therefore arithmetically impossible.

The rolling state must retain more information than the flattened rail pair.
This module records the corrected state boundary.  It keeps the old
interior-frozen prefix, the exact proof-relevant middle-replacement packet,
and the verified flattened prepend result together.  The raw packet is the
bounded live suffix: later steps may inspect its literal construction trace
without claiming that an internal seam survived loop erasure.

The constructors below use the actual append and middle-replacement
classifiers plus the already-proved frozen prepend.  They introduce no new
separation premise.  The live suffix now shifts by one cell and its newly
exposed seam is classified fail-closed: a clean append is returned directly,
while an actual collision is immediately fed to the canonical wider repair.
The two branches do not yet share a common endpoint span, and no additional
prefix is frozen.  Arbitrary-length iteration, both end caps, the final dual
crosscuts, and Fable flag L1 remain open.
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

/-- The proof-relevant trace is canonical once its literal successor and left
rail pair are fixed.  Its data field is forced to be the actual finite
classifier result; the remaining fields are propositions.  This equality is
the overlap receipt used when consecutive bounded windows share a local
transition. -/
theorem ExactSelectedLocalRailConstructionTrace.eq_of_same
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}
    (first second : ExactSelectedLocalRailConstructionTrace successor left) :
    first = second := by
  rcases first with ⟨firstResolved, hfirst, hfirstProvenance⟩
  rcases second with ⟨secondResolved, hsecond, hsecondProvenance⟩
  have hresolved : firstResolved = secondResolved := hfirst.trans hsecond.symm
  cases hresolved
  rfl

instance exactSelectedLocalRailConstructionTraceSubsingleton
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter} :
    Subsingleton (ExactSelectedLocalRailConstructionTrace successor left) :=
  ⟨ExactSelectedLocalRailConstructionTrace.eq_of_same⟩

/-- The bounded raw suffix needed to slide a four-cell window by one corridor
position.  It retains the two overlapping canonical local construction
traces; no flattened rail is split to recover them. -/
structure BoundedLiveTracePair
    {leftInterior : CorridorInterior blockLength}
    {hfirstNext : leftInterior.center.val + 2 < blockLength}
    {hsecondNext :
      (nextCorridorInterior leftInterior hfirstNext).center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {middlePlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hfirstNext)}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hfirstNext) hsecondNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      leftPlacement middlePlacement}
    {secondSuccessor : SeparatedSelectedSourceLocalRailSuccessor hsecondNext
      middlePlacement rightPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    (firstLeft : SeparatedSelectedSourceLocalRailPaths leftPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter) where
  earlierTrace : ExactSelectedLocalRailConstructionTrace firstSuccessor firstLeft
  laterTrace : ExactSelectedLocalRailConstructionTrace secondSuccessor
    (firstSuccessor.rightRailsAsNextLeft secondSuccessor)

namespace BoundedLiveTracePair

/-- Construct the live pair from the two actual adjacent classifiers. -/
noncomputable def ofClassifiers
    {leftInterior : CorridorInterior blockLength}
    {hfirstNext : leftInterior.center.val + 2 < blockLength}
    {hsecondNext :
      (nextCorridorInterior leftInterior hfirstNext).center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {middlePlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hfirstNext)}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hfirstNext) hsecondNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      leftPlacement middlePlacement}
    {secondSuccessor : SeparatedSelectedSourceLocalRailSuccessor hsecondNext
      middlePlacement rightPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    (firstLeft : SeparatedSelectedSourceLocalRailPaths leftPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter) :
    BoundedLiveTracePair
      (leftInterior := leftInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hsecondNext)
      (leftPlacement := leftPlacement) (middlePlacement := middlePlacement)
      (rightPlacement := rightPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := secondSuccessor)
      firstLeft where
  earlierTrace := ExactSelectedLocalRailConstructionTrace.ofClassifier
  laterTrace := ExactSelectedLocalRailConstructionTrace.ofClassifier

/-- Slide the bounded raw suffix by one corridor position.  The old later
trace becomes the new earlier trace definitionally; only the newly exposed
successor is classified. -/
noncomputable def advance
    {leftInterior : CorridorInterior blockLength}
    {hfirstNext : leftInterior.center.val + 2 < blockLength}
    {hsecondNext :
      (nextCorridorInterior leftInterior hfirstNext).center.val + 2 < blockLength}
    {hthirdNext :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hfirstNext) hsecondNext).center.val +
          2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {middlePlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hfirstNext)}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hfirstNext) hsecondNext)}
    {fourthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior leftInterior hfirstNext) hsecondNext)
        hthirdNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      leftPlacement middlePlacement}
    {secondSuccessor : SeparatedSelectedSourceLocalRailSuccessor hsecondNext
      middlePlacement rightPlacement}
    {thirdSuccessor : SeparatedSelectedSourceLocalRailSuccessor hthirdNext
      rightPlacement fourthPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths leftPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}
    (live : BoundedLiveTracePair
      (leftInterior := leftInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hsecondNext)
      (leftPlacement := leftPlacement) (middlePlacement := middlePlacement)
      (rightPlacement := rightPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := secondSuccessor)
      firstLeft) :
    BoundedLiveTracePair
      (leftInterior := nextCorridorInterior leftInterior hfirstNext)
      (hfirstNext := hsecondNext) (hsecondNext := hthirdNext)
      (leftPlacement := middlePlacement) (middlePlacement := rightPlacement)
      (rightPlacement := fourthPlacement)
      (firstSuccessor := secondSuccessor) (secondSuccessor := thirdSuccessor)
      (firstSuccessor.rightRailsAsNextLeft secondSuccessor) where
  earlierTrace := live.laterTrace
  laterTrace := ExactSelectedLocalRailConstructionTrace.ofClassifier

/-- The first genuinely rolling local outcome carried by a bounded live
suffix.  After shifting the two canonical traces by one cell, either the new
adjacent append is already separated, or its actual collision is consumed by
the established four-cell middle replacement.

The two constructors deliberately have different endpoint spans: the direct
branch is the newly exposed adjacent append, while the replacement branch is
the wider repaired window beginning one cell earlier.  A later recurrence
must reconcile those spans before freezing any additional prefix. -/
inductive RepairAdvanceOutcome
    {hfourthNext :
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center.val + 2 < blockLength}
    {fifthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext)
        hfourthNext)}
    {fourthSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfourthNext
      fourthPlacement fifthPlacement}
    (live : BoundedLiveTracePair
      (leftInterior := firstInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hbridgeNext)
      (leftPlacement := firstPlacement) (middlePlacement := secondPlacement)
      (rightPlacement := thirdPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := bridge) firstLeft) :
    Type (u + 1)
  | directAppend
      (shifted : BoundedLiveTracePair
        (leftInterior := nextCorridorInterior firstInterior hfirstNext)
        (hfirstNext := hbridgeNext) (hsecondNext := hlastNext)
        (leftPlacement := secondPlacement) (middlePlacement := thirdPlacement)
        (rightPlacement := fourthPlacement)
        (firstSuccessor := bridge) (secondSuccessor := lastSuccessor)
        (firstSuccessor.rightRailsAsNextLeft bridge))
      (shifted_eq : shifted = live.advance)
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace thirdPlacement bridge.frame.rightAfter)
        (selectedPlacementSideFace thirdPlacement bridge.frame.rightBefore)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter))
  | middleReplacement
      (shifted : BoundedLiveTracePair
        (leftInterior := nextCorridorInterior firstInterior hfirstNext)
        (hfirstNext := hbridgeNext) (hsecondNext := hlastNext)
        (leftPlacement := secondPlacement) (middlePlacement := thirdPlacement)
        (rightPlacement := fourthPlacement)
        (firstSuccessor := bridge) (secondSuccessor := lastSuccessor)
        (firstSuccessor.rightRailsAsNextLeft bridge))
      (shifted_eq : shifted = live.advance)
      (collision : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        lastSuccessor (bridge.rightRailsAsNextLeft lastSuccessor))
      (replacement : ExactSelectedLocalRailMiddleReplacement
        (firstSuccessor := bridge) (bridge := lastSuccessor)
        (lastSuccessor := fourthSuccessor)
        (firstLeft := firstSuccessor.rightRailsAsNextLeft bridge)
        shifted.laterTrace collision)

/-- **L1 constructed raw recurrence step.**  Shift the bounded suffix and run
the actual append classifier at the newly exposed seam.  A clean seam returns
its literal assembly.  A bad seam returns its actual collision and immediately
runs the canonical middle replacement using the shifted trace.

No separation premise is introduced.  This does not yet prepend the old
frozen prefix, identify a common endpoint span for the two branches, iterate,
attach end caps, construct crosscuts, or close L1. -/
noncomputable def classifyRepairAdvance
    {hfourthNext :
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center.val + 2 < blockLength}
    {fifthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext)
        hfourthNext)}
    {fourthSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfourthNext
      fourthPlacement fifthPlacement}
    (live : BoundedLiveTracePair
      (leftInterior := firstInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hbridgeNext)
      (leftPlacement := firstPlacement) (middlePlacement := secondPlacement)
      (rightPlacement := thirdPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := bridge) firstLeft) :
    RepairAdvanceOutcome
      (lastSuccessor := lastSuccessor)
      (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
      (fourthSuccessor := fourthSuccessor) live := by
  let shifted := live.advance
    (hthirdNext := hlastNext) (fourthPlacement := fourthPlacement)
    (thirdSuccessor := lastSuccessor)
  apply Classical.choice
  rcases appendLocalSuccessor_or_actualCollision lastSuccessor
      (bridge.rightRailsAsNextLeft lastSuccessor) with hdirect | hcollision
  · exact ⟨.directAppend shifted rfl hdirect.some⟩
  · let collision := hcollision.some
    exact ⟨.middleReplacement shifted rfl collision
      (ExactSelectedLocalRailMiddleReplacement.ofClassifier
        (firstSuccessor := bridge) (bridge := lastSuccessor)
        (lastSuccessor := fourthSuccessor)
        (firstLeft := firstSuccessor.rightRailsAsNextLeft bridge)
        shifted.laterTrace collision)⟩

end BoundedLiveTracePair

/-- A rolling L1 state with a genuinely frozen old prefix and a bounded raw
four-cell suffix.

The `combined` field is the verified simple two-rail assembly obtained by
prepending the frozen prefix.  The separate `replacement` field deliberately
retains the construction trace from which that flattened result came. -/
structure BoundedLiveMiddleReplacementState
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)) where
  cutoff : Nat
  frozenPrefix : InteriorSeparatedFromFutureSelectedWindows
    (corridor := corridor) prefixAssembly cutoff
  gapToLive : cutoff + 3 < firstInterior.center.val
  source : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
    blockLength corridor
  liveTraces : BoundedLiveTracePair
    (leftInterior := firstInterior)
    (hfirstNext := hfirstNext) (hsecondNext := hbridgeNext)
    (leftPlacement := firstPlacement) (middlePlacement := secondPlacement)
    (rightPlacement := thirdPlacement)
    (firstSuccessor := firstSuccessor) (secondSuccessor := bridge) firstLeft
  liveTraces_eq : liveTraces = BoundedLiveTracePair.ofClassifiers firstLeft
  collision : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
    bridge (firstSuccessor.rightRailsAsNextLeft bridge)
  replacement : ExactSelectedLocalRailMiddleReplacement
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
    liveTraces.laterTrace collision
  replacement_eq : replacement =
    ExactSelectedLocalRailMiddleReplacement.ofClassifier
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
      liveTraces.laterTrace collision
  combined : replacement.outcome.InteriorFrozenPrependOutcome prefixAssembly
  combined_eq : combined = replacement.outcome.prependInteriorFrozen
    prefixAssembly source frozenPrefix gapToLive

namespace BoundedLiveMiddleReplacementState

private abbrev CurrentState
    {firstStart secondStart : SelectedFace (web := web)}
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

/-- **L1 constructed bounded-suffix seed.** Run the actual finite middle
replacement classifier and retain its raw packet beside the frozen prefix.
This is the source-faithful replacement for flattening and forgetting the
four-cell terminal window. -/
noncomputable def ofClassifier
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    {cutoff : Nat}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (hprefix : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) prefixAssembly cutoff)
    (hgap : cutoff + 3 < firstInterior.center.val)
    (collision : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      bridge (firstSuccessor.rightRailsAsNextLeft bridge)) :
    CurrentState
      (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (thirdPlacement := thirdPlacement) (fourthPlacement := fourthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
      prefixAssembly := by
  let liveTraces : BoundedLiveTracePair
      (leftInterior := firstInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hbridgeNext)
      (leftPlacement := firstPlacement) (middlePlacement := secondPlacement)
      (rightPlacement := thirdPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := bridge) firstLeft :=
    BoundedLiveTracePair.ofClassifiers
      (leftInterior := firstInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hbridgeNext)
      (leftPlacement := firstPlacement) (middlePlacement := secondPlacement)
      (rightPlacement := thirdPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := bridge) firstLeft
  let replacement := ExactSelectedLocalRailMiddleReplacement.ofClassifier
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
      liveTraces.laterTrace collision
  exact
    { cutoff := cutoff
      frozenPrefix := hprefix
      gapToLive := hgap
      source := hsource
      liveTraces := liveTraces
      liveTraces_eq := rfl
      collision := collision
      replacement := replacement
      replacement_eq := rfl
      combined := replacement.outcome.prependInteriorFrozen prefixAssembly hsource
        hprefix hgap
      combined_eq := rfl }

end BoundedLiveMiddleReplacementState

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
