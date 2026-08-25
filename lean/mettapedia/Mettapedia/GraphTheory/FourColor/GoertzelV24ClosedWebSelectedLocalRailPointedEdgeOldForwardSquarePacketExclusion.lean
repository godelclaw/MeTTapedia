import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeForwardArmRungExclusion
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareCrossingPacket

/-!
# L1: exclude an old-forward corner from the source square packet

For a forward receipt based at the second Cell--3 placement, neither of its
two boundary arms belongs to the canonical first--third source square's four
selected crossings.  The two rung cases are excluded by the local slot
coordinates.  The two collision-side cases are excluded by the at-most-two
face incidence of a primal edge: each collision side already belongs to the
two adjacent square faces, while each arm belongs to the second centre face.

Thus the source square cannot be attached to the pointed forward corner by
identifying either boundary arm with one of its four selected crossings.  This
is a finite negative coordinate result.  It does not classify the crossed
third edge, construct a rolling repair, attach end caps, construct separated
crosscuts, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorColorTransfer
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open SimpleGraphDartRotation

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
    {web : Instance data coloring}
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {left right :
      {position // position ∈ selectedPlacementSidePositions secondPlacement}}
    {edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS)))}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- **L1 old-forward source-square exclusion.**  At the second Cell--3
placement, neither boundary arm of a forward receipt can be one of the four
selected crossings of the canonical first--third square. -/
theorem SelectedPlacementSideForwardEdgeReceipt.arms_not_mem_sourceSquare_crossingEdges
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      secondPlacement left right edge)
    {face : SelectedFace (web := web)}
    (hfirst : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          firstInterior.center) face)
    (hthird : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
      (rungs := rungs) hfirst hthird hfaceSecond
    selectedPlacementSideForwardFirstArm secondPlacement left ∉
        square.cycle.selectedCycle.crossingEdges ∧
      selectedPlacementSideForwardSecondArm secondPlacement left ∉
        square.cycle.selectedCycle.crossingEdges := by
  classical
  dsimp only
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let secondInterior := nextCorridorInterior firstInterior hfirstNext
  let thirdInterior := nextCorridorInterior secondInterior hbridgeNext
  let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
    (rungs := rungs) hfirst hthird hfaceSecond
  let thirdStep := MiddleReplacementShortDualCycle.squareThirdStep square
  let fourthStep := MiddleReplacementShortDualCycle.squareFourthStep square
  let thirdEdge := square.cycle.selectedCycle.crossingEdge thirdStep
  let fourthEdge := square.cycle.selectedCycle.crossingEdge fourthStep
  let secondFace := skeleton.faceAt secondInterior.center
  let thirdFace := skeleton.faceAt thirdInterior.center
  let firstFace := skeleton.faceAt firstInterior.center
  have hsecondThird : secondFace.1 ≠ thirdFace.1 := by
    intro hfaces
    apply skeleton.faceAt_ne (left := secondInterior.center)
      (right := thirdInterior.center)
    · intro hcenters
      have hval := congrArg Fin.val hcenters
      simp [secondInterior, thirdInterior, nextCorridorInterior] at hval
    · exact Subtype.ext hfaces
  have hsecondFirst : secondFace.1 ≠ firstFace.1 := by
    intro hfaces
    apply skeleton.faceAt_ne (left := secondInterior.center)
      (right := firstInterior.center)
    · intro hcenters
      have hval := congrArg Fin.val hcenters
      simp [secondInterior, nextCorridorInterior] at hval
    · exact Subtype.ext hfaces
  have hfaceSecondValue : face.1 ≠ secondFace.1 := by
    intro hfaces
    apply hfaceSecond
    exact Subtype.ext hfaces
  have hthirdFaceValue : thirdFace.1 ≠ face.1 := by
    intro hfaces
    exact hthird.ne (Subtype.ext hfaces)
  have hfaceFirstValue : face.1 ≠ firstFace.1 := by
    intro hfaces
    exact hfirst.ne (Subtype.ext hfaces.symm)
  have hsquareZero : square.cycle.walk.getVert 0 = firstFace := by
    change (squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.walk.getVert 0 = firstFace
    simpa [firstFace, skeleton] using
      squareDualCycle_of_firstThirdSquare_getVert_zero
        (rungs := rungs) hfirst hthird hfaceSecond
  have hsquareTwo : square.cycle.walk.getVert 2 = thirdFace := by
    change (squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.walk.getVert 2 = thirdFace
    simpa [thirdFace, thirdInterior, secondInterior, skeleton] using
      squareDualCycle_of_firstThirdSquare_getVert_two
        (rungs := rungs) hfirst hthird hfaceSecond
  have hsquareThree : square.cycle.walk.getVert 3 = face := by
    change (squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.walk.getVert 3 = face
    exact squareDualCycle_of_firstThirdSquare_getVert_three
      (rungs := rungs) hfirst hthird hfaceSecond
  have hthirdLeft : thirdEdge ∈ orbitFaceBoundary web.annular.RS thirdFace.1 := by
    have hmem := square.cycle.selectedCycle.crossingEdge_mem_leftFace thirdStep
    change thirdEdge ∈ orbitFaceBoundary web.annular.RS
      (square.cycle.walk.getVert 2).1 at hmem
    rw [hsquareTwo] at hmem
    exact hmem
  have hthirdRight : thirdEdge ∈ orbitFaceBoundary web.annular.RS face.1 := by
    have hmem := square.cycle.selectedCycle.crossingEdge_mem_rightFace thirdStep
    change thirdEdge ∈ orbitFaceBoundary web.annular.RS
      (square.cycle.walk.getVert 3).1 at hmem
    rw [hsquareThree] at hmem
    exact hmem
  have hfourthLeft : fourthEdge ∈ orbitFaceBoundary web.annular.RS face.1 := by
    have hmem := square.cycle.selectedCycle.crossingEdge_mem_leftFace fourthStep
    change fourthEdge ∈ orbitFaceBoundary web.annular.RS
      (square.cycle.walk.getVert 3).1 at hmem
    rw [hsquareThree] at hmem
    exact hmem
  have hfourthRight : fourthEdge ∈ orbitFaceBoundary web.annular.RS firstFace.1 := by
    have hmem := square.cycle.selectedCycle.crossingEdge_mem_rightFace fourthStep
    change fourthEdge ∈ orbitFaceBoundary web.annular.RS
      (square.cycle.walk.getVert 4).1 at hmem
    have hlength : square.cycle.walk.length = 4 := square.length_eq_four
    rw [← hlength, SimpleGraph.Walk.getVert_length] at hmem
    change fourthEdge ∈ orbitFaceBoundary web.annular.RS square.cycle.start.1 at hmem
    have hstart : square.cycle.start = firstFace := by
      simpa only [SimpleGraph.Walk.getVert_zero] using hsquareZero
    rw [hstart] at hmem
    exact hmem
  have hthirdNotSecond :
      thirdEdge ∉ orbitFaceBoundary web.annular.RS secondFace.1 := by
    intro hmem
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS)
        thirdFace.2 face.2 secondFace.2 hthirdFaceValue
        hthirdLeft hthirdRight hmem
    rcases hcases with hcases | hcases
    · exact hsecondThird hcases
    · exact hfaceSecondValue hcases.symm
  have hfourthNotSecond :
      fourthEdge ∉ orbitFaceBoundary web.annular.RS secondFace.1 := by
    intro hmem
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS)
        face.2 firstFace.2 secondFace.2 hfaceFirstValue
        hfourthLeft hfourthRight hmem
    rcases hcases with hcases | hcases
    · exact hfaceSecondValue hcases.symm
    · exact hsecondFirst hcases
  have hfirstArmMem : selectedPlacementSideForwardFirstArm secondPlacement left ∈
      orbitFaceBoundary web.annular.RS secondFace.1 := by
    rw [Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.firstArm_eq_boundaryEdge
      receipt]
    have hmem := faceCycleEdge_mem web.annular.RS secondPlacement.root left.1
    rw [secondPlacement.root_face] at hmem
    simpa [secondFace, secondInterior, skeleton] using hmem
  have hsecondArmMem : selectedPlacementSideForwardSecondArm secondPlacement left ∈
      orbitFaceBoundary web.annular.RS secondFace.1 := by
    rw [Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.secondArm_eq_boundaryEdge
      receipt]
    have hmem := faceCycleEdge_mem web.annular.RS secondPlacement.root right.1
    rw [secondPlacement.root_face] at hmem
    simpa [secondFace, secondInterior, skeleton] using hmem
  have harms :=
    Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.arms_ne_selectedRungs
      receipt
  have hrungIncoming : rungs.edge secondInterior.incoming =
      rungs.edge firstInterior.outgoing := by
    apply congrArg rungs.edge
    exact nextCorridorInterior_incoming_eq_outgoing firstInterior hfirstNext
  have hpacket :=
    MiddleReplacementShortDualCycle.crossingEdges_eq_sourceRungs_insert_collisionSideCrossings
      (rungs := rungs) hfirst hthird hfaceSecond
  have excludeArm
      (arm : G.edgeSet)
      (harmMem : arm ∈ orbitFaceBoundary web.annular.RS secondFace.1)
      (hneIncoming : arm ≠ rungs.edge secondInterior.incoming)
      (hneOutgoing : arm ≠ rungs.edge secondInterior.outgoing) :
      arm ∉ square.cycle.selectedCycle.crossingEdges := by
    intro harm
    rw [hpacket] at harm
    simp only [Finset.mem_insert, Finset.mem_singleton] at harm
    rcases harm with hfirstRung | hsecondRung | hthird | hfourth
    · exact hneIncoming (hfirstRung.trans hrungIncoming.symm)
    · exact hneOutgoing hsecondRung
    · apply hthirdNotSecond
      simpa [thirdEdge, thirdStep, square] using hthird.symm ▸ harmMem
    · apply hfourthNotSecond
      simpa [fourthEdge, fourthStep, square] using hfourth.symm ▸ harmMem
  exact ⟨
    excludeArm _ hfirstArmMem harms.1 harms.2.1,
    excludeArm _ hsecondArmMem harms.2.2.1 harms.2.2.2⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
