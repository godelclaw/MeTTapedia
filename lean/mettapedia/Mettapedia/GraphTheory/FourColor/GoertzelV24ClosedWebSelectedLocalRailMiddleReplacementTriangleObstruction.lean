import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendCyclicObstruction

/-!
# L1: adjacent triangle residues of the middle replacement are cyclic

The four-cell middle-replacement classifier has two adjacent-triangle cases.
The surviving collision face is already adjacent to the two corresponding
corridor centres.  The clearance theorems prove that it is neither named
flank of that interface, so the earlier adjacent-append API packages it as a
literal dual triangle.  Its selected outer-remote deletion component then
contains a primal cycle.

This consumes exactly the two triangle cases.  It does not discharge the
resulting cyclic obstruction, classify either square case, eliminate either
centre case, build the rolling rail assembly, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraph

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

/-- A first/second-cell triangle residue is an actual cyclic append
obstruction for the first successor. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.firstSecondTriangle_cyclicObstruction
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (first_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          firstInterior.center) face)
    (second_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center) face) :
    ∃ triangle :
        SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle
          firstSuccessor,
      Nonempty
        (SeparatedSelectedSourceLocalRailSuccessor.CyclicAppendObstruction
          firstSuccessor triangle) := by
  let triangle :
      SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle
        firstSuccessor := {
    third := face
    leftCenter_adj_third := first_adjacent
    rightCenter_adj_third := second_adjacent
    third_ne_before := (collision.face_ne_firstFlanks hsource).1
    third_ne_after := (collision.face_ne_firstFlanks hsource).2
  }
  rcases triangle.exists_component_away_from_outerRoot with
    ⟨component, hroot⟩
  exact ⟨triangle, ⟨{
    component := component
    outerRoot_not_mem := hroot
    hasCycle := triangle.hasCycleOnSide component hroot
  }⟩⟩

/-- A third/fourth-cell triangle residue is an actual cyclic append
obstruction for the last successor. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.thirdFourthTriangle_cyclicObstruction
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (third_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face)
    (fourth_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
            hlastNext).center) face) :
    ∃ triangle :
        SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle
          lastSuccessor,
      Nonempty
        (SeparatedSelectedSourceLocalRailSuccessor.CyclicAppendObstruction
          lastSuccessor triangle) := by
  let triangle :
      SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle
        lastSuccessor := {
    third := face
    leftCenter_adj_third := third_adjacent
    rightCenter_adj_third := fourth_adjacent
    third_ne_before := (collision.face_ne_lastFlanks hsource).1
    third_ne_after := (collision.face_ne_lastFlanks hsource).2
  }
  rcases triangle.exists_component_away_from_outerRoot with
    ⟨component, hroot⟩
  exact ⟨triangle, ⟨{
    component := component
    outerRoot_not_mem := hroot
    hasCycle := triangle.hasCycleOnSide component hroot
  }⟩⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
