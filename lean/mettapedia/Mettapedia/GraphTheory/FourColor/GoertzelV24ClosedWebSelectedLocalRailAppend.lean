import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversalAppend

/-!
# Append invariant for selected literal Cell-3 rails

The selected successor construction identifies the two exterior faces across
one literal Cell-3 seam and supplies a separated pair of paths through the
next cell.  This file packages the algebraic induction step: two accumulated
simple, mutually disjoint rails remain so after appending that selected local
pair, provided the four displayed old/new support conditions hold.

Those support conditions are deliberately fields of the theorem rather than
conclusions hidden in a constructor.  Remote selected cells are handled by
the existing gap-separation results; the remaining bounded neighbouring
interactions and the two end caps are geometric obligations of Fable flag L1.
Thus this module is an append-safe carrier for the construction, not yet the
global L1 crosscut pair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- The two accumulated selected rails, with exactly the invariant needed by
the next append: both walks are paths and their complete facial supports are
disjoint.  The endpoints remain explicit parameters so that a successor can
only be attached after its literal seam faces have been identified. -/
structure SelectedSourceLocalRailAssembly
    (firstStart secondStart firstFinish secondFinish : SelectedFace
      (web := web)) where
  firstRail : SelectedDualGraph (web := web).Walk firstStart firstFinish
  secondRail : SelectedDualGraph (web := web).Walk secondStart secondFinish
  firstRail_isPath : firstRail.IsPath
  secondRail_isPath : secondRail.IsPath
  firstRail_support_disjoint_secondRail :
    firstRail.support.Disjoint secondRail.support

namespace SeparatedSelectedSourceLocalRailPaths

variable
    {interior : CorridorInterior blockLength}
    {placement : SelectedInternalHexRungPlacement corridor rungs interior}
    {incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ selectedPlacementSidePositions placement}}

/-- A single separated selected Cell-3 rail pair is the base case of the
append invariant. -/
noncomputable def toAssembly
    (rails : SeparatedSelectedSourceLocalRailPaths placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) :
    SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace placement incomingBefore)
      (selectedPlacementSideFace placement incomingAfter)
      (selectedPlacementSideFace placement outgoingBefore)
      (selectedPlacementSideFace placement outgoingAfter) where
  firstRail := rails.paths.firstRail
  secondRail := rails.paths.secondRail
  firstRail_isPath := rails.paths.firstRail_isPath
  secondRail_isPath := rails.paths.secondRail_isPath
  firstRail_support_disjoint_secondRail :=
    rails.firstRail_support_disjoint_secondRail

@[simp] theorem toAssembly_firstRail
    (rails : SeparatedSelectedSourceLocalRailPaths placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) :
    rails.toAssembly.firstRail = rails.paths.firstRail := rfl

@[simp] theorem toAssembly_secondRail
    (rails : SeparatedSelectedSourceLocalRailPaths placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) :
    rails.toAssembly.secondRail = rails.paths.secondRail := rfl

end SeparatedSelectedSourceLocalRailPaths

namespace SeparatedSelectedSourceLocalRailSuccessor

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- Rebase the next cell's first selected rail at the literally equal first
outgoing face of the preceding cell. -/
noncomputable def firstContinuation
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) :
    SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace leftPlacement successor.frame.leftBefore)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore) :=
  successor.rightRails.paths.firstRail.copy
    successor.frame.leftBeforeFace_eq_rightAfterFace.symm rfl

/-- Rebase the second selected rail across the other literal seam face. -/
noncomputable def secondContinuation
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) :
    SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace leftPlacement successor.frame.leftAfter)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter) :=
  successor.rightRails.paths.secondRail.copy
    successor.frame.leftAfterFace_eq_rightBeforeFace.symm rfl

@[simp] theorem firstContinuation_support
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) :
    successor.firstContinuation.support =
      successor.rightRails.paths.firstRail.support := by
  simp [firstContinuation]

@[simp] theorem secondContinuation_support
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) :
    successor.secondContinuation.support =
      successor.rightRails.paths.secondRail.support := by
  simp [secondContinuation]

theorem firstContinuation_isPath
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) : successor.firstContinuation.IsPath := by
  simpa [firstContinuation] using successor.rightRails.paths.firstRail_isPath

theorem secondContinuation_isPath
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) : successor.secondContinuation.IsPath := by
  simpa [secondContinuation] using successor.rightRails.paths.secondRail_isPath

/-- The selected local continuations retain their same-cell separation after
rebasing across the literal successor seam. -/
theorem firstContinuation_support_disjoint_secondContinuation
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) :
    successor.firstContinuation.support.Disjoint
      successor.secondContinuation.support := by
  simpa using successor.rightRails.firstRail_support_disjoint_secondRail

end SeparatedSelectedSourceLocalRailSuccessor

namespace SelectedSourceLocalRailAssembly

variable
    {firstStart secondStart : SelectedFace (web := web)}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- **L1 append invariant.** Extend two accumulated selected rails by the
literal pair in the next Cell-3 hexagon.

The four premises are the complete remaining old/new geometry: two same-track
conditions preserve path simplicity and two crossed-track conditions preserve
mutual separation.  The new pair's own separation is already carried by the
selected successor.  Keeping these premises visible makes this theorem safe
to iterate without pretending that local path certificates imply global
simplicity. -/
noncomputable def appendSuccessor
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (assembly : SelectedSourceLocalRailAssembly
      (web := web) firstStart secondStart
      (selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore)
      (selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter))
    (hfirstPath : assembly.firstRail.support.Disjoint
      successor.firstContinuation.support.tail)
    (hsecondPath : assembly.secondRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hfirstSecond : assembly.firstRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hsecondFirst : assembly.secondRail.support.Disjoint
      successor.firstContinuation.support.tail) :
    SelectedSourceLocalRailAssembly (web := web) firstStart secondStart
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter) where
  firstRail := assembly.firstRail.append successor.firstContinuation
  secondRail := assembly.secondRail.append successor.secondContinuation
  firstRail_isPath :=
    GoertzelV24DualPathTransversal.walk_append_isPath_of_support_disjoint
      assembly.firstRail successor.firstContinuation assembly.firstRail_isPath
      successor.firstContinuation_isPath hfirstPath
  secondRail_isPath :=
    GoertzelV24DualPathTransversal.walk_append_isPath_of_support_disjoint
      assembly.secondRail successor.secondContinuation assembly.secondRail_isPath
      successor.secondContinuation_isPath hsecondPath
  firstRail_support_disjoint_secondRail := by
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
      List.disjoint_left]
    intro face hfirst hsecond
    rcases List.mem_append.mp hfirst with hfirstOld | hfirstNew
    · rcases List.mem_append.mp hsecond with hsecondOld | hsecondNew
      · exact (List.disjoint_left.mp
          assembly.firstRail_support_disjoint_secondRail hfirstOld) hsecondOld
      · exact (List.disjoint_left.mp hfirstSecond hfirstOld) hsecondNew
    · rcases List.mem_append.mp hsecond with hsecondOld | hsecondNew
      · exact (List.disjoint_left.mp hsecondFirst hsecondOld) hfirstNew
      · have hfirstFull : face ∈ successor.firstContinuation.support :=
          List.mem_of_mem_tail hfirstNew
        have hsecondFull : face ∈ successor.secondContinuation.support :=
          List.mem_of_mem_tail hsecondNew
        exact (List.disjoint_left.mp
          successor.firstContinuation_support_disjoint_secondContinuation
            hfirstFull) hsecondFull

@[simp] theorem appendSuccessor_firstRail
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (assembly : SelectedSourceLocalRailAssembly
      (web := web) firstStart secondStart
      (selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore)
      (selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter))
    (hfirstPath : assembly.firstRail.support.Disjoint
      successor.firstContinuation.support.tail)
    (hsecondPath : assembly.secondRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hfirstSecond : assembly.firstRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hsecondFirst : assembly.secondRail.support.Disjoint
      successor.firstContinuation.support.tail) :
    (appendSuccessor successor assembly hfirstPath hsecondPath hfirstSecond
      hsecondFirst).firstRail =
        assembly.firstRail.append successor.firstContinuation := rfl

@[simp] theorem appendSuccessor_secondRail
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (assembly : SelectedSourceLocalRailAssembly
      (web := web) firstStart secondStart
      (selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore)
      (selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter))
    (hfirstPath : assembly.firstRail.support.Disjoint
      successor.firstContinuation.support.tail)
    (hsecondPath : assembly.secondRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hfirstSecond : assembly.firstRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hsecondFirst : assembly.secondRail.support.Disjoint
      successor.firstContinuation.support.tail) :
    (appendSuccessor successor assembly hfirstPath hsecondPath hfirstSecond
      hsecondFirst).secondRail =
        assembly.secondRail.append successor.secondContinuation := rfl

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
