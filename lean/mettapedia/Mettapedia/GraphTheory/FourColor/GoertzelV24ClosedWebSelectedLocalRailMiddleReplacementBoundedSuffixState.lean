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

The constructor below uses the actual middle-replacement classifier and the
already-proved frozen prepend.  It introduces no new separation premise.
This is the first state constructor for the wider recurrence; it does not yet
shift the live suffix, eliminate its collision result, iterate to arbitrary
length, attach either end cap, construct the final dual crosscuts, or close
Fable flag L1.
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
  trace : ExactSelectedLocalRailConstructionTrace bridge
    (firstSuccessor.rightRailsAsNextLeft bridge)
  collision : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
    bridge (firstSuccessor.rightRailsAsNextLeft bridge)
  replacement : ExactSelectedLocalRailMiddleReplacement
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace collision
  replacement_eq : replacement =
    ExactSelectedLocalRailMiddleReplacement.ofClassifier
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace collision
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
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge))
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
  let replacement := ExactSelectedLocalRailMiddleReplacement.ofClassifier
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace collision
  exact
    { cutoff := cutoff
      frozenPrefix := hprefix
      gapToLive := hgap
      source := hsource
      trace := trace
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
