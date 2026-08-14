import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendResidueLengths

/-!
# L1: endpoint coordinates of the remaining append residues

A path of length two has exactly one interior support position.  Hence two
distinct support faces which both avoid the finish must include the start;
dually, two distinct faces in its support tail must include the finish.  This
file applies that elementary fact to every length-resolved Cell-3 residue.

The resulting binary endpoint alternatives are the final coordinate choices
for the local reroute.  They do not yet assemble those choices, iterate a
corridor, attach annular end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
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

namespace Instance.SelectedLocalLayerFormation

private theorem one_eq_start_of_two_distinct_nonend_support_faces
    {F : Type*} {H : SimpleGraph F} {start finish first second : F}
    (walk : H.Walk start finish) (hlength : walk.length = 2)
    (hfirst : first ∈ walk.support) (hsecond : second ∈ walk.support)
    (hne : first ≠ second) (hfirstEnd : first ≠ finish)
    (hsecondEnd : second ≠ finish) : first = start ∨ second = start := by
  cases walk with
  | nil => simp at hlength
  | @cons next _ _ hadj tail =>
      cases tail with
      | nil => simp at hlength
      | @cons last _ _ hnext rest =>
          cases rest with
          | nil =>
              simp only [SimpleGraph.Walk.support_cons,
                SimpleGraph.Walk.support_nil, List.mem_cons] at hfirst hsecond
              aesop
          | cons hthird more =>
              simp only [SimpleGraph.Walk.length_cons] at hlength
              omega

private theorem one_eq_end_of_two_distinct_tail_faces
    {F : Type*} {H : SimpleGraph F} {start finish first second : F}
    (walk : H.Walk start finish) (hlength : walk.length = 2)
    (hfirst : first ∈ walk.support.tail)
    (hsecond : second ∈ walk.support.tail)
    (hne : first ≠ second) : first = finish ∨ second = finish := by
  cases walk with
  | nil => simp at hlength
  | @cons next _ _ hadj tail =>
      cases tail with
      | nil => simp at hlength
      | @cons last _ _ hnext rest =>
          cases rest with
          | nil =>
              simp only [SimpleGraph.Walk.support_cons,
                SimpleGraph.Walk.support_nil, List.tail_cons,
                List.mem_cons] at hfirst hsecond
              aesop
          | cons hthird more =>
              simp only [SimpleGraph.Walk.length_cons] at hlength
              omega

namespace SelectedSourceLocalRailAssembly

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

private theorem collision_faces_ne_of_left_separation
    {first second : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (hfirst : first ∈ left.paths.firstRail.support)
    (hsecond : second ∈ left.paths.secondRail.support) : first ≠ second := by
  intro heq
  exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
    hfirst) (heq ▸ hsecond)

private theorem collision_faces_ne_of_right_separation
    {first second : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (hfirst : first ∈ successor.firstContinuation.support.tail)
    (hsecond : second ∈ successor.secondContinuation.support.tail) :
    first ≠ second := by
  intro heq
  exact (List.disjoint_left.mp
    successor.firstContinuation_support_disjoint_secondContinuation
      (List.mem_of_mem_tail hfirst))
    (List.mem_of_mem_tail (heq ▸ hsecond))

/-- In the `firstSecondSameFirst` residue, one of the two collision faces is
the incoming endpoint of the length-two old first rail. -/
theorem firstSecondSameFirst_cross_eq_start_or_same_eq_start
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 2 ∧
      left.paths.secondRail.length = 0 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    cross.face = selectedPlacementSideFace leftPlacement leftIncomingBefore ∨
      same.face = selectedPlacementSideFace leftPlacement leftIncomingBefore := by
  let crossActual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
        successor left := ⟨cross.face, Or.inl ⟨cross.mem_old, cross.mem_new⟩⟩
  let sameActual : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      successor left := ⟨same.face, Or.inl ⟨same.mem_old, same.mem_new⟩⟩
  exact one_eq_start_of_two_distinct_nonend_support_faces left.paths.firstRail
    lengths.1 cross.mem_old same.mem_old
    (collision_faces_ne_of_right_separation same.mem_new cross.mem_new).symm
    crossActual.toAdjacentDualTriangle.third_ne_before
    sameActual.toAdjacentDualTriangle.third_ne_before

/-- In the `firstSecondSameSecond` residue, one of the two collision faces is
the outgoing endpoint of the length-two next second rail. -/
theorem firstSecondSameSecond_cross_eq_end_or_same_eq_end
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    cross.face = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter ∨
      same.face = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter := by
  exact one_eq_end_of_two_distinct_tail_faces successor.secondContinuation
    lengths.2.2.2 cross.mem_new same.mem_new
    (collision_faces_ne_of_left_separation cross.mem_old same.mem_old)

/-- A centre residue on the next second rail places either the cross face or
the previous centre at that length-two rail's outgoing endpoint. -/
theorem firstSecondCenter_cross_eq_end_or_center_eq_end
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈ successor.secondContinuation.support.tail)
    (lengths : 0 < left.paths.firstRail.length ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    cross.face = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter ∨
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) =
        selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter := by
  let actual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
        successor left := ⟨cross.face, Or.inl ⟨cross.mem_old, cross.mem_new⟩⟩
  exact one_eq_end_of_two_distinct_tail_faces successor.secondContinuation
    lengths.2.2 cross.mem_new center
    actual.toAdjacentDualTriangle.leftCenter_adj_third.ne.symm

/-- Symmetric start-coordinate alternative for `secondFirstSameSecond`. -/
theorem secondFirstSameSecond_cross_eq_start_or_same_eq_start
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 0 ∧
      left.paths.secondRail.length = 2 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    cross.face = selectedPlacementSideFace leftPlacement leftIncomingAfter ∨
      same.face = selectedPlacementSideFace leftPlacement leftIncomingAfter := by
  let crossActual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
        successor left := ⟨cross.face, Or.inr ⟨cross.mem_old, cross.mem_new⟩⟩
  let sameActual : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      successor left := ⟨same.face, Or.inr (Or.inl
        ⟨same.mem_old, same.mem_new⟩)⟩
  exact one_eq_start_of_two_distinct_nonend_support_faces left.paths.secondRail
    lengths.2.1 cross.mem_old same.mem_old
    (collision_faces_ne_of_right_separation cross.mem_new same.mem_new)
    crossActual.toAdjacentDualTriangle.third_ne_after
    sameActual.toAdjacentDualTriangle.third_ne_after

/-- Symmetric end-coordinate alternative for `secondFirstSameFirst`. -/
theorem secondFirstSameFirst_cross_eq_end_or_same_eq_end
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    cross.face = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore ∨
      same.face = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore := by
  exact one_eq_end_of_two_distinct_tail_faces successor.firstContinuation
    lengths.2.2.1 cross.mem_new same.mem_new
    (collision_faces_ne_of_left_separation same.mem_old cross.mem_old).symm

/-- Symmetric centre-coordinate alternative on the next first rail. -/
theorem secondFirstCenter_cross_eq_end_or_center_eq_end
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈ successor.firstContinuation.support.tail)
    (lengths : 0 < left.paths.secondRail.length ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    cross.face = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore ∨
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) =
        selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore := by
  let actual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
        successor left := ⟨cross.face, Or.inr ⟨cross.mem_old, cross.mem_new⟩⟩
  exact one_eq_end_of_two_distinct_tail_faces successor.firstContinuation
    lengths.2.1 cross.mem_new center
    actual.toAdjacentDualTriangle.leftCenter_adj_third.ne.symm

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
