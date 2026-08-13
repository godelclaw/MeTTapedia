import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalRailSeparation

/-!
# Appending consecutive literal Cell-3 rail steps

The source-facing long radial witness is a pair of primal paths, whereas the
annular splice consumes facial-dual crosscuts.  The literal Cell-3 rail steps
are the local ribbon-boundary construction relating those two kinds of data.
This file identifies the exact bounded geometric condition under which two
consecutive steps append to two simple, mutually disjoint facial-dual rails.

The condition is not hidden in the constructor: consecutive corridor centres
must have no common full-dual neighbor other than the two named flank faces of
their shared rung.  Remote centres already satisfy the stronger disjointness
theorems in `GoertzelV24ClosedWebLocalRailSeparation`; proving this bounded
neighbor classification from the source annular geometry is the remaining
local part of L9.
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
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

private theorem walk_append_isPath_of_support_disjoint
    {F : Type*} {H : SimpleGraph F}
    {start middle finish : F}
    (left : H.Walk start middle) (right : H.Walk middle finish)
    (hleft : left.IsPath) (hright : right.IsPath)
    (hdisjoint : left.support.Disjoint right.support.tail) :
    (left.append right).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨hleft.support_nodup, hright.support_nodup.tail, hdisjoint⟩

namespace SourceLocalRailSuccessor

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior}
    {leftIncomingBefore leftIncomingAfter leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement}}
    {hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6]}
    {hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6]}
    {rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)}

/-- Rebase the first successor rail at the literally equal outgoing face of
the preceding Cell-3 placement. -/
noncomputable def firstContinuation
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (localPlacementSideFace leftPlacement leftBefore)
        (localPlacementSideFace rightPlacement
          successor.rightOutgoingBefore) :=
  successor.rails.firstRail.copy successor.beforeFace_eq.symm rfl

/-- Rebase the second successor rail at the other literally equal outgoing
face of the preceding Cell-3 placement. -/
noncomputable def secondContinuation
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (localPlacementSideFace leftPlacement leftAfter)
        (localPlacementSideFace rightPlacement
          successor.rightOutgoingAfter) :=
  successor.rails.secondRail.copy successor.afterFace_eq.symm rfl

@[simp] theorem firstContinuation_support
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    successor.firstContinuation.support = successor.rails.firstRail.support := by
  simp [firstContinuation]

@[simp] theorem secondContinuation_support
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    successor.secondContinuation.support = successor.rails.secondRail.support := by
  simp [secondContinuation]

theorem firstContinuation_isPath
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    successor.firstContinuation.IsPath := by
  simpa [firstContinuation] using successor.rails.firstRail_isPath

theorem secondContinuation_isPath
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    successor.secondContinuation.IsPath := by
  simpa [secondContinuation] using successor.rails.secondRail_isPath

/-- **L9 (bounded adjacent-neighbor classification).** The two expected
flank faces of the shared rung are all the common full-dual neighbors of two
consecutive Cell-3 centres.  This is the exact local rotation/annulus theorem
needed to append the literal rails; it is deliberately a named proposition,
not an implicit consequence of dual connectedness or a Menger hypothesis. -/
def CommonNeighborsExact
    (_successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) : Prop :=
  ∀ face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)),
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) face →
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt
            (nextCorridorInterior leftInterior hnext).center) face →
    face = localPlacementSideFace leftPlacement leftBefore ∨
      face = localPlacementSideFace leftPlacement leftAfter

private theorem start_not_mem_support_tail_of_isPath
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath) :
    start ∉ walk.support.tail := by
  have hnodup := hpath.support_nodup
  rw [← walk.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

private theorem end_mem_support
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) : finish ∈ walk.support := by
  simp

/-- The first rail appends simply once the exact adjacent common-neighbor
classification is available. -/
theorem firstRail_support_disjoint_firstContinuation_tail
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftBefore leftAfter)
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hexact : successor.CommonNeighborsExact) :
    left.firstRail.support.Disjoint successor.firstContinuation.support.tail := by
  rw [List.disjoint_left]
  intro face hleft hright
  have hrightFull : face ∈ successor.rails.firstRail.support := by
    rw [firstContinuation_support] at hright
    exact List.mem_of_mem_tail hright
  rcases hexact face
      (left.firstRail_support_adjacent_center face hleft)
      (successor.rails.firstRail_support_adjacent_center face hrightFull) with
    hbefore | hafter
  · rw [hbefore] at hright
    exact (start_not_mem_support_tail_of_isPath successor.firstContinuation
      successor.firstContinuation_isPath) hright
  · rw [hafter] at hleft
    have hother : localPlacementSideFace leftPlacement leftAfter ∈
        left.secondRail.support := end_mem_support left.secondRail
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hleft) hother

/-- The second rail appends simply under the same bounded classification. -/
theorem secondRail_support_disjoint_secondContinuation_tail
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftBefore leftAfter)
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hexact : successor.CommonNeighborsExact) :
    left.secondRail.support.Disjoint successor.secondContinuation.support.tail := by
  rw [List.disjoint_left]
  intro face hleft hright
  have hrightFull : face ∈ successor.rails.secondRail.support := by
    rw [secondContinuation_support] at hright
    exact List.mem_of_mem_tail hright
  rcases hexact face
      (left.secondRail_support_adjacent_center face hleft)
      (successor.rails.secondRail_support_adjacent_center face hrightFull) with
    hbefore | hafter
  · rw [hbefore] at hleft
    have hother : localPlacementSideFace leftPlacement leftBefore ∈
        left.firstRail.support := end_mem_support left.firstRail
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hother) hleft
  · rw [hafter] at hright
    exact (start_not_mem_support_tail_of_isPath successor.secondContinuation
      successor.secondContinuation_isPath) hright

/-- The old first track does not hit the new second-track tail.  The two
expected common neighbors are excluded by the old and new within-cell rail
separation respectively. -/
theorem firstRail_support_disjoint_secondContinuation_tail
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftBefore leftAfter)
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hexact : successor.CommonNeighborsExact) :
    left.firstRail.support.Disjoint successor.secondContinuation.support.tail := by
  rw [List.disjoint_left]
  intro face hleft hright
  have hrightFull : face ∈ successor.rails.secondRail.support := by
    rw [secondContinuation_support] at hright
    exact List.mem_of_mem_tail hright
  rcases hexact face
      (left.firstRail_support_adjacent_center face hleft)
      (successor.rails.secondRail_support_adjacent_center face hrightFull) with
    hbefore | hafter
  · rw [hbefore] at hrightFull
    have hfirstStart : localPlacementSideFace leftPlacement leftBefore ∈
        successor.rails.firstRail.support := by
      rw [successor.beforeFace_eq]
      exact successor.rails.firstRail.start_mem_support
    exact (List.disjoint_left.mp
      successor.rails.firstRail_support_disjoint_secondRail hfirstStart)
        hrightFull
  · rw [hafter] at hleft
    have hother : localPlacementSideFace leftPlacement leftAfter ∈
        left.secondRail.support := end_mem_support left.secondRail
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hleft) hother

/-- Symmetrically, the old second track does not hit the new first-track
tail. -/
theorem secondRail_support_disjoint_firstContinuation_tail
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftBefore leftAfter)
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hexact : successor.CommonNeighborsExact) :
    left.secondRail.support.Disjoint successor.firstContinuation.support.tail := by
  rw [List.disjoint_left]
  intro face hleft hright
  have hrightFull : face ∈ successor.rails.firstRail.support := by
    rw [firstContinuation_support] at hright
    exact List.mem_of_mem_tail hright
  rcases hexact face
      (left.secondRail_support_adjacent_center face hleft)
      (successor.rails.firstRail_support_adjacent_center face hrightFull) with
    hbefore | hafter
  · rw [hbefore] at hleft
    have hother : localPlacementSideFace leftPlacement leftBefore ∈
        left.firstRail.support := end_mem_support left.firstRail
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hother) hleft
  · rw [hafter] at hrightFull
    have hsecondStart : localPlacementSideFace leftPlacement leftAfter ∈
        successor.rails.secondRail.support := by
      rw [successor.afterFace_eq]
      exact successor.rails.secondRail.start_mem_support
    exact (List.disjoint_left.mp
      successor.rails.firstRail_support_disjoint_secondRail hrightFull)
        hsecondStart

/-- **L9 (two-cell literal rail append).** Under the one explicitly named
bounded neighbor theorem, the two source-generated successor steps append to
simple facial-dual paths.  No general disjoint-path existence theorem and no
caller-chosen path witness is used. -/
theorem firstRail_append_isPath
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftBefore leftAfter)
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hexact : successor.CommonNeighborsExact) :
    (left.firstRail.append successor.firstContinuation).IsPath :=
  walk_append_isPath_of_support_disjoint left.firstRail
    successor.firstContinuation left.firstRail_isPath
    successor.firstContinuation_isPath
    (successor.firstRail_support_disjoint_firstContinuation_tail left hexact)

theorem secondRail_append_isPath
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftBefore leftAfter)
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hexact : successor.CommonNeighborsExact) :
    (left.secondRail.append successor.secondContinuation).IsPath :=
  walk_append_isPath_of_support_disjoint left.secondRail
    successor.secondContinuation left.secondRail_isPath
    successor.secondContinuation_isPath
    (successor.secondRail_support_disjoint_secondContinuation_tail left hexact)

/-- The two appended rails remain mutually vertex-disjoint.  Together with
the preceding two path theorems this is the complete two-cell rail invariant
needed by a recursive L9 assembly. -/
theorem append_support_disjoint
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftBefore leftAfter)
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hexact : successor.CommonNeighborsExact) :
    (left.firstRail.append successor.firstContinuation).support.Disjoint
      (left.secondRail.append successor.secondContinuation).support := by
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
    List.disjoint_left]
  intro face hfirst hsecond
  rcases List.mem_append.mp hfirst with hleftFirst | hrightFirst
  · rcases List.mem_append.mp hsecond with hleftSecond | hrightSecond
    · exact (List.disjoint_left.mp
        left.firstRail_support_disjoint_secondRail hleftFirst) hleftSecond
    · exact (List.disjoint_left.mp
        (successor.firstRail_support_disjoint_secondContinuation_tail
          left hexact) hleftFirst) hrightSecond
  · rcases List.mem_append.mp hsecond with hleftSecond | hrightSecond
    · exact (List.disjoint_left.mp
        (successor.secondRail_support_disjoint_firstContinuation_tail
          left hexact) hleftSecond) hrightFirst
    · have hrightFirstFull : face ∈ successor.rails.firstRail.support := by
        rw [← firstContinuation_support]
        exact List.mem_of_mem_tail hrightFirst
      have hrightSecondFull : face ∈ successor.rails.secondRail.support := by
        rw [← secondContinuation_support]
        exact List.mem_of_mem_tail hrightSecond
      exact (List.disjoint_left.mp
        successor.rails.firstRail_support_disjoint_secondRail
          hrightFirstFull) hrightSecondFull

end SourceLocalRailSuccessor

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
