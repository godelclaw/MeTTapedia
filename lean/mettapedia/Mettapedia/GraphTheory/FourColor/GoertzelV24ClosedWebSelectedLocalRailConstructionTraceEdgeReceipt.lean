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
introduce no edge.  The two immediate centre repairs and all six residual
repairs discharge it, after which the exhaustive classifier attaches it to
the public complete append and its proof-relevant construction trace.  This
file does not identify either pointed collision edge with a
replacement-square endpoint triangle, iterate the terminal transition,
attach end caps, or close the source's bulk-corridor flag L1.
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

/-- Receipt provenance for a finite repair which may preserve or exchange its
two outgoing endpoint labels. -/
def AssemblySumHasSelectedAdjacentTerminalEdgeReceipts
    (result :
      Sum (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
        (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))) : Prop :=
  match result with
  | .inl assembly =>
      AssemblyHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        assembly
  | .inr assembly =>
      AssemblyHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        assembly

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

/-- The immediate first-to-second repair also preserves receipts: its crossed
rail is the canonical reroute, while the companion rail is the old second
rail, the literal centre bridge, and the successor first continuation. -/
theorem appendSingleFirstSecondViaLeftCenter_hasSelectedAdjacentTerminalEdgeReceipts
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
    (holdSecond :
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support.Disjoint
          left.paths.secondRail.support)
    (hnewFirst :
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support.Disjoint
          successor.firstContinuation.support.tail)
    (hcenter :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∉
        (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
          (successor := successor) (left := left) collision.face
          collision.mem_old collision.mem_new).route.support) :
    AssemblyHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendSingleFirstSecondViaLeftCenter collision holdSecond hnewFirst
        hcenter) := by
  constructor
  · change WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route
    exact firstToSecondReroute_hasSelectedAdjacentTerminalEdgeReceipts
      collision.face collision.mem_old collision.mem_new
  · change WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      ((left.paths.secondRail.append
        (selectedPlacementCenterBridge leftPlacement successor.frame.leftAfter
          successor.frame.leftBefore)).append
            successor.firstContinuation).bypass
    exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
      (walkHasSelectedAdjacentTerminalEdgeReceipts_append
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts
          (selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
            successor.frame.leftAfter successor.frame.leftBefore))
        firstContinuation_hasSelectedAdjacentTerminalEdgeReceipts)

/-- The symmetric immediate repair preserves the same receipts; reversal of
the undirected centre bridge introduces no new edge. -/
theorem appendSingleSecondFirstViaLeftCenter_hasSelectedAdjacentTerminalEdgeReceipts
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
    (holdFirst :
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support.Disjoint
          left.paths.firstRail.support)
    (hnewSecond :
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support.Disjoint
          successor.secondContinuation.support.tail)
    (hcenter :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∉
        (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
          (successor := successor) (left := left) collision.face
          collision.mem_old collision.mem_new).route.support) :
    AssemblyHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendSingleSecondFirstViaLeftCenter collision holdFirst hnewSecond
        hcenter) := by
  constructor
  · change WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      ((left.paths.firstRail.append
        (selectedPlacementCenterBridge leftPlacement successor.frame.leftAfter
          successor.frame.leftBefore).reverse).append
            successor.secondContinuation).bypass
    exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
      (walkHasSelectedAdjacentTerminalEdgeReceipts_append
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts
          (walkHasSelectedAdjacentTerminalEdgeReceipts_reverse
            (selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
              successor.frame.leftAfter successor.frame.leftBefore)))
        secondContinuation_hasSelectedAdjacentTerminalEdgeReceipts)
  · change WalkHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route
    exact secondToFirstReroute_hasSelectedAdjacentTerminalEdgeReceipts
      collision.face collision.mem_old collision.mem_new

/-- The first same-track residue introduces no anonymous edge in either of
its two endpoint-order branches. -/
theorem appendFirstSecondSameFirst_hasSelectedAdjacentTerminalEdgeReceipts
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 2 ∧
      left.paths.secondRail.length = 0 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    AssemblySumHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendFirstSecondSameFirst cross same lengths) := by
  classical
  by_cases hcrossStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingBefore
  · simp only [appendFirstSecondSameFirst, hcrossStart,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · intro edge hedge
      simp at hedge
    · change WalkHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        ((left.paths.secondRail.append
          (selectedPlacementCenterBridge leftPlacement successor.frame.leftAfter
            successor.frame.leftBefore)).append
              successor.firstContinuation).bypass
      exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          (walkHasSelectedAdjacentTerminalEdgeReceipts_append
            leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts
            (selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
              successor.frame.leftAfter successor.frame.leftBefore))
          firstContinuation_hasSelectedAdjacentTerminalEdgeReceipts)
  · simp only [appendFirstSecondSameFirst, hcrossStart,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · intro edge hedge
      simp at hedge
    · intro edge hedge
      apply secondContinuation_hasSelectedAdjacentTerminalEdgeReceipts edge
      simpa only [SimpleGraph.Walk.edges_copy] using hedge

/-- The rail-exchanged same-track residue likewise introduces only the two
selected forward tracks and the old-centre connector. -/
theorem appendSecondFirstSameSecond_hasSelectedAdjacentTerminalEdgeReceipts
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 0 ∧
      left.paths.secondRail.length = 2 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    AssemblySumHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendSecondFirstSameSecond cross same lengths) := by
  classical
  by_cases hcrossStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingAfter
  · simp only [appendSecondFirstSameSecond, hcrossStart,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · change WalkHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        ((left.paths.firstRail.append
          (selectedPlacementCenterBridge leftPlacement successor.frame.leftBefore
            successor.frame.leftAfter)).append
              successor.secondContinuation).bypass
      exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          (walkHasSelectedAdjacentTerminalEdgeReceipts_append
            leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts
            (selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
              successor.frame.leftBefore successor.frame.leftAfter))
          secondContinuation_hasSelectedAdjacentTerminalEdgeReceipts)
    · intro edge hedge
      simp at hedge
  · simp only [appendSecondFirstSameSecond, hcrossStart,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · intro edge hedge
      apply firstContinuation_hasSelectedAdjacentTerminalEdgeReceipts edge
      simpa only [SimpleGraph.Walk.edges_copy] using hedge
    · intro edge hedge
      simp at hedge

/-- The seam-reversed first-to-second residue preserves literal receipts in
both endpoint-order branches. -/
theorem appendFirstSecondSameSecond_hasSelectedAdjacentTerminalEdgeReceipts
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    AssemblySumHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendFirstSecondSameSecond cross same lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter
  · simp only [appendFirstSecondSameSecond, hcrossEnd,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · intro edge hedge
      simp at hedge
    · change WalkHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        ((left.paths.secondRail.append
          (selectedPlacementCenterBridge leftPlacement successor.frame.leftAfter
            successor.frame.leftBefore)).append
              successor.firstContinuation).bypass
      exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          (walkHasSelectedAdjacentTerminalEdgeReceipts_append
            leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts
            (selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
              successor.frame.leftAfter successor.frame.leftBefore))
          firstContinuation_hasSelectedAdjacentTerminalEdgeReceipts)
  · simp only [appendFirstSecondSameSecond, hcrossEnd,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · intro edge hedge
      apply leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts edge
      simpa only [SimpleGraph.Walk.edges_copy] using hedge
    · intro edge hedge
      simp at hedge

/-- The rail-exchanged seam-reversed residue preserves the same literal
receipt trichotomy. -/
theorem appendSecondFirstSameFirst_hasSelectedAdjacentTerminalEdgeReceipts
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    AssemblySumHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendSecondFirstSameFirst cross same lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore
  · simp only [appendSecondFirstSameFirst, hcrossEnd,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · change WalkHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        ((left.paths.firstRail.append
          (selectedPlacementCenterBridge leftPlacement successor.frame.leftBefore
            successor.frame.leftAfter)).append
              successor.secondContinuation).bypass
      exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          (walkHasSelectedAdjacentTerminalEdgeReceipts_append
            leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts
            (selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
              successor.frame.leftBefore successor.frame.leftAfter))
          secondContinuation_hasSelectedAdjacentTerminalEdgeReceipts)
    · intro edge hedge
      simp at hedge
  · simp only [appendSecondFirstSameFirst, hcrossEnd,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · intro edge hedge
      simp at hedge
    · intro edge hedge
      apply leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts edge
      simpa only [SimpleGraph.Walk.edges_copy] using hedge

/-- The first centre-revisit repair either truncates the colliding old rail
or ends at the literal old centre; neither operation invents an edge. -/
theorem appendFirstSecondCenter_hasSelectedAdjacentTerminalEdgeReceipts
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.secondContinuation.support.tail)
    (lengths : 0 < left.paths.firstRail.length ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    AssemblySumHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendFirstSecondCenter cross center lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter
  · simp only [appendFirstSecondCenter, hcrossEnd,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · intro edge hedge
      apply walkHasSelectedAdjacentTerminalEdgeReceipts_takeUntil
        leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts cross.mem_old edge
      simpa only [SimpleGraph.Walk.edges_copy] using hedge
    · change WalkHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        ((left.paths.secondRail.append
          (selectedPlacementCenterBridge leftPlacement successor.frame.leftAfter
            successor.frame.leftBefore)).append
              successor.firstContinuation).bypass
      exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          (walkHasSelectedAdjacentTerminalEdgeReceipts_append
            leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts
            (selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
              successor.frame.leftAfter successor.frame.leftBefore))
          firstContinuation_hasSelectedAdjacentTerminalEdgeReceipts)
  · simp only [appendFirstSecondCenter, hcrossEnd,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · intro edge hedge
      apply leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts edge
      simpa only [SimpleGraph.Walk.edges_copy] using hedge
    · change WalkHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        ((left.paths.secondRail.append
          (selectedPlacementSideToCenter leftPlacement successor.frame.leftAfter)
            |>.bypass).copy rfl _)
      exact walkHasSelectedAdjacentTerminalEdgeReceipts_copy
        (walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts
          (selectedPlacementSideToCenter_hasSelectedAdjacentTerminalEdgeReceipts
            successor.frame.leftAfter))) rfl _

/-- The symmetric centre-revisit repair preserves the identical source-edge
receipt invariant. -/
theorem appendSecondFirstCenter_hasSelectedAdjacentTerminalEdgeReceipts
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.firstContinuation.support.tail)
    (lengths : 0 < left.paths.secondRail.length ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    AssemblySumHasSelectedAdjacentTerminalEdgeReceipts
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      (appendSecondFirstCenter cross center lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore
  · simp only [appendSecondFirstCenter, hcrossEnd,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · change WalkHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        ((left.paths.firstRail.append
          (selectedPlacementCenterBridge leftPlacement successor.frame.leftBefore
            successor.frame.leftAfter)).append
              successor.secondContinuation).bypass
      exact walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          (walkHasSelectedAdjacentTerminalEdgeReceipts_append
            leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts
            (selectedPlacementCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
              successor.frame.leftBefore successor.frame.leftAfter))
          secondContinuation_hasSelectedAdjacentTerminalEdgeReceipts)
    · intro edge hedge
      apply walkHasSelectedAdjacentTerminalEdgeReceipts_takeUntil
        leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts cross.mem_old edge
      simpa only [SimpleGraph.Walk.edges_copy] using hedge
  · simp only [appendSecondFirstCenter, hcrossEnd,
      AssemblySumHasSelectedAdjacentTerminalEdgeReceipts]
    constructor
    · change WalkHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        ((left.paths.firstRail.append
          (selectedPlacementSideToCenter leftPlacement successor.frame.leftBefore)
            |>.bypass).copy rfl _)
      exact walkHasSelectedAdjacentTerminalEdgeReceipts_copy
        (walkHasSelectedAdjacentTerminalEdgeReceipts_bypass
        (walkHasSelectedAdjacentTerminalEdgeReceipts_append
          leftFirstRail_hasSelectedAdjacentTerminalEdgeReceipts
          (selectedPlacementSideToCenter_hasSelectedAdjacentTerminalEdgeReceipts
            successor.frame.leftBefore))) rfl _
    · intro edge hedge
      apply leftSecondRail_hasSelectedAdjacentTerminalEdgeReceipts edge
      simpa only [SimpleGraph.Walk.edges_copy] using hedge

/-- Receipt provenance on a complete straight-or-swapped adjacent result. -/
def SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts
    (result : SelectedLocalRailAppendCompleteOutcome successor left) : Prop :=
  match result with
  | .straight assembly | .swapped assembly =>
      AssemblyHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        assembly

/-- Receipt predicate on the first exhaustive classifier.  Its unresolved
collision branches deliberately carry no claim yet. -/
def SelectedLocalRailAppendOutcome.HasSelectedAdjacentTerminalEdgeReceipts
    (result : SelectedLocalRailAppendOutcome successor left) : Prop :=
  match result with
  | .straight assembly | .swapped assembly =>
      AssemblyHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        assembly
  | .singleFirstSecond _ _ => True
  | .singleSecondFirst _ _ => True
  | .doubleCrossSameTrack _ _ _ => True

theorem classifyLocalSuccessorAppend_hasSelectedAdjacentTerminalEdgeReceipts :
    (classifyLocalSuccessorAppend successor left)
      |>.HasSelectedAdjacentTerminalEdgeReceipts := by
  classical
  unfold classifyLocalSuccessorAppend
  split
  · rename_i hfirstSecond
    split
    · rename_i hsecondFirst
      exact appendSuccessorBypass_hasSelectedAdjacentTerminalEdgeReceipts
        hfirstSecond hsecondFirst
    · trivial
  · rename_i hfirstSecond
    dsimp only
    split
    · trivial
    · rename_i hsecondFirst
      split
      · rename_i hfirstFirst
        split
        · rename_i hsecondSecond
          exact
            appendSuccessorSwapBothCrossCollisions_hasSelectedAdjacentTerminalEdgeReceipts
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).face
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).face
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).mem_old
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).mem_new
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).mem_old
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).mem_new
              hfirstFirst hsecondSecond
        · trivial
      · trivial

/-- Receipt predicate for the first centre-bridge classifier. -/
def SingleFirstSecondCenterBridgeOutcome.HasSelectedAdjacentTerminalEdgeReceipts
    {collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail}
    (result : SingleFirstSecondCenterBridgeOutcome collision) : Prop :=
  match result with
  | .assembly value =>
      AssemblyHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        value
  | .meetsOldSecond _ | .meetsNewFirst _ | .containsLeftCenter _ => True

theorem classifySingleFirstSecondCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail) :
    (classifySingleFirstSecondCenterBridge collision)
      |>.HasSelectedAdjacentTerminalEdgeReceipts := by
  classical
  unfold classifySingleFirstSecondCenterBridge
  dsimp only
  split
  · rename_i holdSecond
    split
    · rename_i hnewFirst
      split
      · trivial
      · rename_i hcenter
        exact
          appendSingleFirstSecondViaLeftCenter_hasSelectedAdjacentTerminalEdgeReceipts
            collision holdSecond hnewFirst hcenter
    · trivial
  · trivial

/-- Receipt predicate for the rail-exchanged centre-bridge classifier. -/
def SingleSecondFirstCenterBridgeOutcome.HasSelectedAdjacentTerminalEdgeReceipts
    {collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail}
    (result : SingleSecondFirstCenterBridgeOutcome collision) : Prop :=
  match result with
  | .assembly value =>
      AssemblyHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        value
  | .meetsOldFirst _ | .meetsNewSecond _ | .containsLeftCenter _ => True

theorem classifySingleSecondFirstCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail) :
    (classifySingleSecondFirstCenterBridge collision)
      |>.HasSelectedAdjacentTerminalEdgeReceipts := by
  classical
  unfold classifySingleSecondFirstCenterBridge
  dsimp only
  split
  · rename_i holdFirst
    split
    · rename_i hnewSecond
      split
      · trivial
      · rename_i hcenter
        exact
          appendSingleSecondFirstViaLeftCenter_hasSelectedAdjacentTerminalEdgeReceipts
            collision holdFirst hnewSecond hcenter
    · trivial
  · trivial

/-- Receipt provenance after removal of the impossible mixed double-cross
branch. -/
def SelectedLocalRailAppendResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts
    (result : SelectedLocalRailAppendResolvedOutcome successor left) : Prop :=
  match result with
  | .straight assembly | .swapped assembly =>
      AssemblyHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        assembly
  | .singleFirstSecond _ _ | .singleSecondFirst _ _ => True

theorem classifyLocalSuccessorAppendResolved_hasSelectedAdjacentTerminalEdgeReceipts :
    (classifyLocalSuccessorAppendResolved successor left)
      |>.HasSelectedAdjacentTerminalEdgeReceipts := by
  classical
  have hbase := classifyLocalSuccessorAppend_hasSelectedAdjacentTerminalEdgeReceipts
    (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppend successor left with
  | straight assembly =>
      simpa [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
        SelectedLocalRailAppendResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
        using hbase
  | swapped assembly =>
      simpa [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
        SelectedLocalRailAppendResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
        using hbase
  | singleFirstSecond _ _ =>
      simp [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
  | singleSecondFirst _ _ =>
      simp [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
  | doubleCrossSameTrack firstSecond secondFirst sameTrack =>
      exact False.elim
        (not_doubleCrossSameTrack firstSecond secondFirst sameTrack)

/-- Receipt provenance on the final finite length classifier. -/
def SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts
    (result : SelectedLocalRailAppendLengthResolvedOutcome successor left) : Prop :=
  match result with
  | .straight assembly | .swapped assembly =>
      AssemblyHasSelectedAdjacentTerminalEdgeReceipts
        (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
        assembly
  | .firstSecondSameFirst _ _ _ | .firstSecondSameSecond _ _ _ |
      .firstSecondCenter _ _ _ | .secondFirstSameFirst _ _ _ |
      .secondFirstSameSecond _ _ _ | .secondFirstCenter _ _ _ => True

theorem classifyLocalSuccessorAppendLengthResolved_hasSelectedAdjacentTerminalEdgeReceipts :
    (classifyLocalSuccessorAppendLengthResolved successor left)
      |>.HasSelectedAdjacentTerminalEdgeReceipts := by
  classical
  have hresolved :=
    classifyLocalSuccessorAppendResolved_hasSelectedAdjacentTerminalEdgeReceipts
      (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppendResolved successor left with
  | straight assembly =>
      simpa [classifyLocalSuccessorAppendLengthResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
        SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
        using hresolved
  | swapped assembly =>
      simpa [classifyLocalSuccessorAppendLengthResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
        SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
        using hresolved
  | singleFirstSecond cross _ =>
      have hs :=
        classifySingleFirstSecondCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
          cross
      cases hcenter : classifySingleFirstSecondCenterBridge cross with
      | assembly value =>
          simpa [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SingleFirstSecondCenterBridgeOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
            SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
            using hs
      | meetsOldSecond _ | meetsNewFirst _ | containsLeftCenter _ =>
          simp [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
  | singleSecondFirst cross _ =>
      have hs :=
        classifySingleSecondFirstCenterBridge_hasSelectedAdjacentTerminalEdgeReceipts
          cross
      cases hcenter : classifySingleSecondFirstCenterBridge cross with
      | assembly value =>
          simpa [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SingleSecondFirstCenterBridgeOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
            SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
            using hs
      | meetsOldFirst _ | meetsNewSecond _ | containsLeftCenter _ =>
          simp [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts]

/-- **L1 complete adjacent receipt theorem.** Every constructive branch of
the unconditional adjacent append retains a literal selected-step or named
old-centre connector receipt for every surviving edge. -/
theorem appendLocalSuccessorComplete_hasSelectedAdjacentTerminalEdgeReceipts :
    (appendLocalSuccessorComplete successor left)
      |>.HasSelectedAdjacentTerminalEdgeReceipts := by
  classical
  have hlength :=
    classifyLocalSuccessorAppendLengthResolved_hasSelectedAdjacentTerminalEdgeReceipts
      (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppendLengthResolved successor left with
  | straight assembly =>
      simpa [appendLocalSuccessorComplete, hresult,
        SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
        SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
        using hlength
  | swapped assembly =>
      simpa [appendLocalSuccessorComplete, hresult,
        SelectedLocalRailAppendLengthResolvedOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
        SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
        using hlength
  | firstSecondSameFirst cross same lengths =>
      have hs :=
        appendFirstSecondSameFirst_hasSelectedAdjacentTerminalEdgeReceipts
          cross same lengths
      cases hrepair : appendFirstSecondSameFirst cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumHasSelectedAdjacentTerminalEdgeReceipts,
          SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
          using hs
  | firstSecondSameSecond cross same lengths =>
      have hs :=
        appendFirstSecondSameSecond_hasSelectedAdjacentTerminalEdgeReceipts
          cross same lengths
      cases hrepair : appendFirstSecondSameSecond cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumHasSelectedAdjacentTerminalEdgeReceipts,
          SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
          using hs
  | firstSecondCenter cross center lengths =>
      have hs := appendFirstSecondCenter_hasSelectedAdjacentTerminalEdgeReceipts
        cross center lengths
      cases hrepair : appendFirstSecondCenter cross center lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumHasSelectedAdjacentTerminalEdgeReceipts,
          SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
          using hs
  | secondFirstSameFirst cross same lengths =>
      have hs :=
        appendSecondFirstSameFirst_hasSelectedAdjacentTerminalEdgeReceipts
          cross same lengths
      cases hrepair : appendSecondFirstSameFirst cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumHasSelectedAdjacentTerminalEdgeReceipts,
          SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
          using hs
  | secondFirstSameSecond cross same lengths =>
      have hs :=
        appendSecondFirstSameSecond_hasSelectedAdjacentTerminalEdgeReceipts
          cross same lengths
      cases hrepair : appendSecondFirstSameSecond cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumHasSelectedAdjacentTerminalEdgeReceipts,
          SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
          using hs
  | secondFirstCenter cross center lengths =>
      have hs := appendSecondFirstCenter_hasSelectedAdjacentTerminalEdgeReceipts
        cross center lengths
      cases hrepair : appendSecondFirstCenter cross center lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumHasSelectedAdjacentTerminalEdgeReceipts,
          SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts]
          using hs

/-- Every proof-relevant canonical construction trace retains the complete
terminal edge-receipt theorem after its finite repair branch is erased. -/
theorem ExactSelectedLocalRailConstructionTrace.toOutcome_hasSelectedAdjacentTerminalEdgeReceipts
    (trace : ExactSelectedLocalRailConstructionTrace successor left) :
    trace.toOutcome.HasSelectedAdjacentTerminalEdgeReceipts := by
  rw [trace.toOutcome_eq_complete]
  exact appendLocalSuccessorComplete_hasSelectedAdjacentTerminalEdgeReceipts

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
