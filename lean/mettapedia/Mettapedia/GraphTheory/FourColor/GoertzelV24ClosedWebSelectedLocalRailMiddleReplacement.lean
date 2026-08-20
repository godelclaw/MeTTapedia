import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleCollisionClearance

/-!
# L1: replace the overlapping middle window by its canonical repair

The canonical four-cell collision packet contains three adjacent two-cell
windows.  When its middle band is selected, the middle construction trace
already supplies a literal separated repair.  This file splices that repair
between the untouched first-cell rails and the untouched fourth-cell
continuations.

Both joins are tested after loop erasure.  A successful branch therefore
returns a concrete four-cell `SelectedSourceLocalRailAssembly`; a failing
branch retains the exact first or second join, endpoint parity, and surviving
collision witness.  No disjointness premise is added.

The result is a fail-closed middle replacement, not yet a proof that either
join must succeed, an arbitrary-length rolling transition, either end cap, a
pair of simple dual crosscuts, or closure of Fable flag L1.
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

private abbrev BridgeLeft :=
  firstSuccessor.rightRailsAsNextLeft bridge

private abbrev StraightMiddleAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)

private abbrev SwappedMiddleAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)

/-- The literal fourth-cell continuation pair, packaged with its already
proved path and separation certificates. -/
noncomputable def continuationAssembly
    (successor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement) :
    SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace thirdPlacement successor.frame.leftBefore)
      (selectedPlacementSideFace thirdPlacement successor.frame.leftAfter)
      (selectedPlacementSideFace fourthPlacement successor.rightOutgoingBefore)
      (selectedPlacementSideFace fourthPlacement successor.rightOutgoingAfter) where
  firstRail := successor.firstContinuation
  secondRail := successor.secondContinuation
  firstRail_isPath := successor.firstContinuation_isPath
  secondRail_isPath := successor.secondContinuation_isPath
  firstRail_support_disjoint_secondRail :=
    successor.firstContinuation_support_disjoint_secondContinuation

private noncomputable def rebaseMiddleStraight
    (assembly : StraightMiddleAssembly (firstSuccessor := firstSuccessor)
      (bridge := bridge)) :=
  rebaseAssemblyStart assembly
    firstSuccessor.frame.leftBeforeFace_eq_rightAfterFace.symm
    firstSuccessor.frame.leftAfterFace_eq_rightBeforeFace.symm

private noncomputable def rebaseMiddleSwapped
    (assembly : SwappedMiddleAssembly (firstSuccessor := firstSuccessor)
      (bridge := bridge)) :=
  rebaseAssemblyStart assembly
    firstSuccessor.frame.leftBeforeFace_eq_rightAfterFace.symm
    firstSuccessor.frame.leftAfterFace_eq_rightBeforeFace.symm

private noncomputable def rebaseLastContinuation :=
  rebaseAssemblyStart (continuationAssembly lastSuccessor)
    (congrArg (selectedPlacementSideFace thirdPlacement)
      (bridge.rightOutgoingBefore_eq_nextLeftBefore lastSuccessor)).symm
    (congrArg (selectedPlacementSideFace thirdPlacement)
      (bridge.rightOutgoingAfter_eq_nextLeftAfter lastSuccessor)).symm

/-- Exact surviving collision data from one of the two joins of a canonical
middle replacement.  The constructors retain the middle branch and the
classifier equation, so this cannot be inhabited by merely postulating a
failure face. -/
inductive ExactSelectedLocalRailMiddleReplacementCollision
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (face : SelectedFace (web := web)) : Prop
  | straightLeft
      (middle : StraightMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .straight middle)
      (witness : RetainedBypassCrossCollision firstLeft.toAssembly
        (rebaseMiddleStraight middle))
      (hclassified : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleStraight middle) = .collision witness)
      (hface : witness.face = face)
  | swappedLeft
      (middle : SwappedMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .swapped middle)
      (witness : RetainedBypassCrossCollision firstLeft.toAssembly
        (rebaseMiddleSwapped middle))
      (hclassified : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleSwapped middle) = .collision witness)
      (hface : witness.face = face)
  | straightRight
      (middle : StraightMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .straight middle)
      (prefixMiddle : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter))
      (hleft : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleStraight middle) = .assembled prefixMiddle)
      (witness : RetainedBypassCrossCollision prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)))
      (hright : classifyRetainedBypassAppend prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)) =
        .collision witness)
      (hface : witness.face = face)
  | swappedRight
      (middle : SwappedMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .swapped middle)
      (prefixMiddle : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore))
      (hleft : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleSwapped middle) = .assembled prefixMiddle)
      (witness : CrossedRetainedBypassCrossCollision prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)))
      (hright : classifyCrossedRetainedBypassAppend prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)) =
        .collision witness)
      (hface : witness.face = face)

/-- Result of replacing the overlapping middle window and testing both of
its literal joins after loop erasure. -/
inductive ExactSelectedLocalRailMiddleReplacementOutcome
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) : Type (u + 1)
  | straight
      (middle : StraightMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .straight middle)
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace fourthPlacement lastSuccessor.rightOutgoingBefore)
        (selectedPlacementSideFace fourthPlacement lastSuccessor.rightOutgoingAfter))
  | swapped
      (middle : SwappedMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .swapped middle)
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace fourthPlacement lastSuccessor.rightOutgoingAfter)
        (selectedPlacementSideFace fourthPlacement lastSuccessor.rightOutgoingBefore))
  | collision
      (face : SelectedFace (web := web))
      (data : ExactSelectedLocalRailMiddleReplacementCollision
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)

/-- Classify the literal replacement selected by the canonical middle trace.
The returned collision-avoiding rail is retained separately by
`collisionAvoidingMiddleRail`; this classifier tests whether the whole pair
can be joined to both untouched outer cells. -/
noncomputable def classifyExactSelectedLocalRailMiddleReplacement
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    ExactSelectedLocalRailMiddleReplacementOutcome
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace := by
  classical
  cases hresult : trace.toOutcome with
  | straight middle =>
      cases hleft : classifyRetainedBypassAppend firstLeft.toAssembly
          (rebaseMiddleStraight middle) with
      | collision witness =>
          exact .collision witness.face
            (.straightLeft middle hresult witness hleft rfl)
      | assembled prefixMiddle =>
          cases hright : classifyRetainedBypassAppend prefixMiddle
              (rebaseLastContinuation (bridge := bridge)
                (lastSuccessor := lastSuccessor)) with
          | assembled assembly => exact .straight middle hresult assembly
          | collision witness =>
              exact .collision witness.face
                (.straightRight middle hresult prefixMiddle hleft witness hright rfl)
  | swapped middle =>
      cases hleft : classifyRetainedBypassAppend firstLeft.toAssembly
          (rebaseMiddleSwapped middle) with
      | collision witness =>
          exact .collision witness.face
            (.swappedLeft middle hresult witness hleft rfl)
      | assembled prefixMiddle =>
          cases hright : classifyCrossedRetainedBypassAppend prefixMiddle
              (rebaseLastContinuation (bridge := bridge)
                (lastSuccessor := lastSuccessor)) with
          | assembled assembly => exact .swapped middle hresult assembly
          | collision witness =>
              exact .collision witness.face
                (.swappedRight middle hresult prefixMiddle hleft witness hright rfl)

/-- The replacement classifier retains the independently proved concrete rail
which avoids the original middle-band collision face. -/
structure ExactSelectedLocalRailMiddleReplacement
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (collision : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      bridge (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) where
  clearMiddleRail : CollisionAvoidingMiddleRail trace collision
  outcome : ExactSelectedLocalRailMiddleReplacementOutcome
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace

/-- Construct the proof-relevant middle replacement from the actual canonical
trace and an independently selected middle collision. -/
noncomputable def ExactSelectedLocalRailMiddleReplacement.ofClassifier
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (collision : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      bridge (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    ExactSelectedLocalRailMiddleReplacement
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace collision where
  clearMiddleRail := trace.collisionAvoidingMiddleRail collision
  outcome := classifyExactSelectedLocalRailMiddleReplacement
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
