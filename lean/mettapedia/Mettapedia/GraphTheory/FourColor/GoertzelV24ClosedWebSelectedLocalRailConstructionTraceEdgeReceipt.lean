import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailConstructionTrace
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailCenterEdgeReceipt

/-!
# L1: source receipts for repaired terminal-track edges

The proof-relevant adjacent construction trace retains the finite repair that
produced its terminal rails.  Before classifying those repair branches, this
module records the common invariant they preserve: every surviving dual edge
comes from a selected forward step in the old Cell-3 placement, a selected
forward step in the successor placement, or one of the explicitly receipted
old-centre connectors.

The elementary walk operations used by all terminal repairs---copy, append,
prefix truncation, and loop erasure---preserve this invariant because they
introduce no edge.  The later branch theorem may therefore concentrate only
on the finite constructor shapes.  This file does not identify either pointed
collision edge with a replacement-square endpoint triangle, iterate the
terminal transition, attach end caps, or close the source's bulk-corridor flag
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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- Exact source classification for an edge in one adjacent terminal repair.
The first two alternatives are literal selected forward steps in the old and
successor Cell-3 placements.  The final alternative is a named old-centre
connector edge. -/
def SelectedAdjacentTerminalEdgeReceipt
    (edge : Sym2 (SelectedFace (web := web))) : Prop :=
  SelectedPlacementForwardEdgeOrigin leftPlacement edge ∨
    SelectedPlacementForwardEdgeOrigin rightPlacement edge ∨
      ∃ position :
          {position // position ∈ selectedPlacementSidePositions leftPlacement},
        SelectedPlacementCenterSideEdgeReceipt leftPlacement position edge

/-- Every edge of a walk has one of the three adjacent terminal source
receipts. -/
def WalkHasSelectedAdjacentTerminalEdgeReceipts
    {start finish : SelectedFace (web := web)}
    (walk : SelectedDualGraph (web := web).Walk start finish) : Prop :=
  ∀ edge ∈ walk.edges, SelectedAdjacentTerminalEdgeReceipt
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) edge

/-- Copying endpoints changes no edge receipt. -/
theorem walkHasSelectedAdjacentTerminalEdgeReceipts_copy
    {start finish newStart newFinish : SelectedFace (web := web)}
    {walk : SelectedDualGraph (web := web).Walk start finish}
    (hreceipts : WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) walk)
    (hstart : start = newStart) (hfinish : finish = newFinish) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (walk.copy hstart hfinish) := by
  intro edge hedge
  apply hreceipts edge
  simpa only [SimpleGraph.Walk.edges_copy] using hedge

/-- Appending two receipted walks only concatenates their edge lists. -/
theorem walkHasSelectedAdjacentTerminalEdgeReceipts_append
    {start middle finish : SelectedFace (web := web)}
    {first : SelectedDualGraph (web := web).Walk start middle}
    {second : SelectedDualGraph (web := web).Walk middle finish}
    (hfirst : WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) first)
    (hsecond : WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) second) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (first.append second) := by
  intro edge hedge
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at hedge
  rcases hedge with hedge | hedge
  · exact hfirst edge hedge
  · exact hsecond edge hedge

/-- Loop erasure deletes edges and therefore preserves every receipt. -/
theorem walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
    {start finish : SelectedFace (web := web)}
    {walk : SelectedDualGraph (web := web).Walk start finish}
    (hreceipts : WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) walk) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      walk.bypass := by
  intro edge hedge
  exact hreceipts edge (walk.edges_bypass_subset_edges hedge)

/-- Truncating at an occurring face deletes a suffix and introduces no edge. -/
theorem walkHasSelectedAdjacentTerminalEdgeReceipts_takeUntil
    {start finish face : SelectedFace (web := web)}
    {walk : SelectedDualGraph (web := web).Walk start finish}
    (hreceipts : WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) walk)
    (hface : face ∈ walk.support) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (walk.takeUntil face hface) := by
  intro edge hedge
  exact hreceipts edge (walk.edges_takeUntil_subset_edges hface hedge)

/-- Keeping the suffix beginning at an occurring face also deletes edges
only. -/
theorem walkHasSelectedAdjacentTerminalEdgeReceipts_dropUntil
    {start finish face : SelectedFace (web := web)}
    {walk : SelectedDualGraph (web := web).Walk start finish}
    (hreceipts : WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) walk)
    (hface : face ∈ walk.support) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (walk.dropUntil face hface) := by
  intro edge hedge
  exact hreceipts edge (walk.edges_dropUntil_subset_edges hface hedge)

/-- Reversal changes edge order but not the underlying undirected edges. -/
theorem walkHasSelectedAdjacentTerminalEdgeReceipts_reverse
    {start finish : SelectedFace (web := web)}
    {walk : SelectedDualGraph (web := web).Walk start finish}
    (hreceipts : WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) walk) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      walk.reverse := by
  intro edge hedge
  apply hreceipts edge
  simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hedge

/-- A stationary walk has no edge requiring a receipt. -/
theorem nil_hasSelectedAdjacentTerminalEdgeReceipts
    (face : SelectedFace (web := web)) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (SimpleGraph.Walk.nil : SelectedDualGraph (web := web).Walk face face) := by
  intro edge hedge
  simp at hedge

/-- The first old rail already carries its selected forward-step receipts. -/
theorem leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      left.paths.firstRail := by
  intro edge hedge
  exact Or.inl (left.firstRail_edge_has_forward_origin edge hedge)

/-- The second old rail carries the same old-placement receipt. -/
theorem leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      left.paths.secondRail := by
  intro edge hedge
  exact Or.inl (left.secondRail_edge_has_forward_origin edge hedge)

/-- The first continuation retains the successor-placement receipt through
its endpoint rebase. -/
theorem firstContinuation_hasSelectedAdjacentTerminalEdgeReceipts :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      successor.firstContinuation := by
  intro edge hedge
  exact Or.inr (Or.inl
    (successor.firstContinuation_edge_has_forward_origin hedge))

/-- The second continuation has the analogous successor receipt. -/
theorem secondContinuation_hasSelectedAdjacentTerminalEdgeReceipts :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      successor.secondContinuation := by
  intro edge hedge
  exact Or.inr (Or.inl
    (successor.secondContinuation_edge_has_forward_origin hedge))

/-- A complete old-centre bridge has a selected side-slot receipt on either
of its two edges. -/
theorem selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
    (after before :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (selectedPlacementCenterBridge leftPlacement after before) := by
  intro edge hedge
  rcases selectedPlacementCenterBridge_edge_receipt leftPlacement after before
      edge hedge with hafter | hbefore
  · exact Or.inr (Or.inr ⟨after, hafter⟩)
  · exact Or.inr (Or.inr ⟨before, hbefore⟩)

/-- A side-to-centre half-connector has the corresponding side-slot
receipt. -/
theorem selectedPlacementSideToCenter_hasSelectedAdjacentTerminalEdgeReceipts
    (position :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (selectedPlacementSideToCenter leftPlacement position) := by
  intro edge hedge
  exact Or.inr (Or.inr
    ⟨position, selectedPlacementSideToCenter_edge_receipt
      leftPlacement position edge hedge⟩)

/-- The reverse half-connector has the identical undirected receipt. -/
theorem selectedPlacementCenterToSide_hasSelectedAdjacentTerminalEdgeReceipts
    (position :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (selectedPlacementCenterToSide leftPlacement position) := by
  intro edge hedge
  exact Or.inr (Or.inr
    ⟨position, selectedPlacementCenterToSide_edge_receipt
      leftPlacement position edge hedge⟩)

/-- The canonical first-to-second collision reroute uses only the old first
rail and the successor second continuation. -/
theorem firstToSecondReroute_hasSelectedAdjacentTerminalEdgeReceipts
    (collisionFace : SelectedFace (web := web))
    (hold : collisionFace ∈ left.paths.firstRail.support)
    (hnew : collisionFace ∈ successor.secondContinuation.support.tail) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collisionFace hold hnew).route := by
  have hnewFull : collisionFace ∈ successor.secondContinuation.support :=
    List.mem_of_mem_tail hnew
  have holdPart := walkHasSelectedAdjacentTerminalEdgeReceipts_takeUntil
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
    leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts hold
  have hnewPart := walkHasSelectedAdjacentTerminalEdgeReceipts_dropUntil
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
    secondContinuation_hasSelectedAdjacentTerminalEdgeReceipts hnewFull
  have hraw := walkHasSelectedAdjacentTerminalEdgeReceipts_append
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
    holdPart hnewPart
  have hbypass := walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) hraw
  simpa only [SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute]
    using hbypass

/-- The symmetric collision reroute uses only the old second rail and the
successor first continuation. -/
theorem secondToFirstReroute_hasSelectedAdjacentTerminalEdgeReceipts
    (collisionFace : SelectedFace (web := web))
    (hold : collisionFace ∈ left.paths.secondRail.support)
    (hnew : collisionFace ∈ successor.firstContinuation.support.tail) :
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collisionFace hold hnew).route := by
  have hnewFull : collisionFace ∈ successor.firstContinuation.support :=
    List.mem_of_mem_tail hnew
  have holdPart := walkHasSelectedAdjacentTerminalEdgeReceipts_takeUntil
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
    leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts hold
  have hnewPart := walkHasSelectedAdjacentTerminalEdgeReceipts_dropUntil
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
    firstContinuation_hasSelectedAdjacentTerminalEdgeReceipts hnewFull
  have hraw := walkHasSelectedAdjacentTerminalEdgeReceipts_append
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
    holdPart hnewPart
  have hbypass := walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) hraw
  simpa only [SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute]
    using hbypass

/-- Both rails of an assembled adjacent terminal result retain exact source
receipts on every surviving edge. -/
def AssemblyHasSelectedAdjacentTerminalEdgeReceipts
    {firstStart secondStart firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish) : Prop :=
  WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      assembly.firstRail ∧
    WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      assembly.secondRail

/-- The ordinary loop-erased append preserves source receipts on both
ordered rails. -/
theorem appendSuccessorBypass_hasSelectedAdjacentTerminalEdgeReceipts
    (hfirstSecond : left.paths.firstRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hsecondFirst : left.paths.secondRail.support.Disjoint
      successor.firstContinuation.support.tail) :
    AssemblyHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendSuccessorBypass successor left.toAssembly hfirstSecond hsecondFirst) := by
  constructor
  · change WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (left.paths.firstRail.append successor.firstContinuation).bypass
    exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
      (walkHasSelectedAdjacentTerminalEdgeReceipts_append
        leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts
        firstContinuation_hasSelectedAdjacentTerminalEdgeReceipts)
  · change WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (left.paths.secondRail.append successor.secondContinuation).bypass
    exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
      (walkHasSelectedAdjacentTerminalEdgeReceipts_append
        leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts
        secondContinuation_hasSelectedAdjacentTerminalEdgeReceipts)

/-- The double-cross repair preserves receipts on its two crossed reroutes. -/
theorem appendSuccessorSwapBothCrossCollisions_hasSelectedAdjacentTerminalEdgeReceipts
    (firstSecondFace secondFirstFace : SelectedFace (web := web))
    (hfirstSecondOld : firstSecondFace ∈ left.paths.firstRail.support)
    (hfirstSecondNew :
      firstSecondFace ∈ successor.secondContinuation.support.tail)
    (hsecondFirstOld : secondFirstFace ∈ left.paths.secondRail.support)
    (hsecondFirstNew :
      secondFirstFace ∈ successor.firstContinuation.support.tail)
    (hfirstFirst : left.paths.firstRail.support.Disjoint
      successor.firstContinuation.support.tail)
    (hsecondSecond : left.paths.secondRail.support.Disjoint
      successor.secondContinuation.support.tail) :
    AssemblyHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendSuccessorSwapBothCrossCollisions successor left firstSecondFace
        secondFirstFace hfirstSecondOld hfirstSecondNew hsecondFirstOld
        hsecondFirstNew hfirstFirst hsecondSecond) := by
  constructor
  · simpa only [appendSuccessorSwapBothCrossCollisions] using
      firstToSecondReroute_hasSelectedAdjacentTerminalEdgeReceipts
        firstSecondFace hfirstSecondOld hfirstSecondNew
  · simpa only [appendSuccessorSwapBothCrossCollisions] using
      secondToFirstReroute_hasSelectedAdjacentTerminalEdgeReceipts
        secondFirstFace hsecondFirstOld hsecondFirstNew

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
