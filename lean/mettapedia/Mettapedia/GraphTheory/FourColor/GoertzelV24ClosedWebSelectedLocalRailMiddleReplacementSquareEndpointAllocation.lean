import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareCrossingPacket
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareSourceRungAllocation

/-!
# L1: allocate all four source-square crossings to the bond endpoints

The exact source square has two named rung crossings and two named
collision-side crossings.  Each crossing meets one endpoint of the selected
two-vertex residue.  Local cubicity says exactly two selected square
crossings meet each endpoint, so the independent four-by-four allocation
table reduces to six genuine cases: two unsplit cases and four oriented
split cases.

This is the endpoint-incidence table for the four named square crossings.  It
does not classify either actual pointed rail crossing as one of those edges
or as the internal bond, construct or splice a bypass, prove companion
separation, iterate a repair, attach end caps, construct separated crosscuts,
or close Fable flag L1.
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

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

private abbrev SelectedFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace MiddleReplacementShortDualCycle

/-- The four possible incidences of the two collision-adjacent square
crossings with the two vertices of the exact square bond. -/
inductive SquareBondRealization.CollisionSideEndpointAllocation
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (thirdSide fourthSide : G.edgeSet) : Prop
  | sameFirst
      (third_mem : bond.first ∈ thirdSide.1)
      (fourth_mem : bond.first ∈ fourthSide.1)
  | sameSecond
      (third_mem : bond.second ∈ thirdSide.1)
      (fourth_mem : bond.second ∈ fourthSide.1)
  | firstThenSecond
      (third_mem : bond.first ∈ thirdSide.1)
      (fourth_mem : bond.second ∈ fourthSide.1)
  | secondThenFirst
      (third_mem : bond.second ∈ thirdSide.1)
      (fourth_mem : bond.first ∈ fourthSide.1)

/-- After imposing the two-crossings-per-endpoint count, the source-rung and
collision-side allocations have exactly six compatible orientations. -/
inductive SquareBondRealization.SourceAndCollisionEndpointAllocation
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (firstRung secondRung thirdSide fourthSide : G.edgeSet) : Prop
  | rungsFirst_sidesSecond
      (firstRung_mem : bond.first ∈ firstRung.1)
      (secondRung_mem : bond.first ∈ secondRung.1)
      (thirdSide_mem : bond.second ∈ thirdSide.1)
      (fourthSide_mem : bond.second ∈ fourthSide.1)
  | rungsSecond_sidesFirst
      (firstRung_mem : bond.second ∈ firstRung.1)
      (secondRung_mem : bond.second ∈ secondRung.1)
      (thirdSide_mem : bond.first ∈ thirdSide.1)
      (fourthSide_mem : bond.first ∈ fourthSide.1)
  | firstThenSecond_firstThenSecond
      (firstRung_mem : bond.first ∈ firstRung.1)
      (secondRung_mem : bond.second ∈ secondRung.1)
      (thirdSide_mem : bond.first ∈ thirdSide.1)
      (fourthSide_mem : bond.second ∈ fourthSide.1)
  | firstThenSecond_secondThenFirst
      (firstRung_mem : bond.first ∈ firstRung.1)
      (secondRung_mem : bond.second ∈ secondRung.1)
      (thirdSide_mem : bond.second ∈ thirdSide.1)
      (fourthSide_mem : bond.first ∈ fourthSide.1)
  | secondThenFirst_firstThenSecond
      (firstRung_mem : bond.second ∈ firstRung.1)
      (secondRung_mem : bond.first ∈ secondRung.1)
      (thirdSide_mem : bond.first ∈ thirdSide.1)
      (fourthSide_mem : bond.second ∈ fourthSide.1)
  | secondThenFirst_secondThenFirst
      (firstRung_mem : bond.second ∈ firstRung.1)
      (secondRung_mem : bond.first ∈ secondRung.1)
      (thirdSide_mem : bond.second ∈ thirdSide.1)
      (fourthSide_mem : bond.first ∈ fourthSide.1)

private theorem false_of_three_distinct_selected_crossings_meet
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {vertex : V} {firstEdge secondEdge thirdEdge : G.edgeSet}
    (hcard : ((incidentEdgeFinset G vertex).filter
      (fun edge => edge ∈ cycle.selectedCycle.crossingEdges)).card = 2)
    (hfirstCrossing : firstEdge ∈ cycle.selectedCycle.crossingEdges)
    (hsecondCrossing : secondEdge ∈ cycle.selectedCycle.crossingEdges)
    (hthirdCrossing : thirdEdge ∈ cycle.selectedCycle.crossingEdges)
    (hfirstIncident : vertex ∈ firstEdge.1)
    (hsecondIncident : vertex ∈ secondEdge.1)
    (hthirdIncident : vertex ∈ thirdEdge.1)
    (hfirstSecond : firstEdge ≠ secondEdge)
    (hfirstThird : firstEdge ≠ thirdEdge)
    (hsecondThird : secondEdge ≠ thirdEdge) : False := by
  classical
  let incidentCrossings := (incidentEdgeFinset G vertex).filter
    (fun edge => edge ∈ cycle.selectedCycle.crossingEdges)
  have hfirstMem : firstEdge ∈ incidentCrossings := by
    exact Finset.mem_filter.2
      ⟨by simpa [incidentEdgeFinset] using hfirstIncident, hfirstCrossing⟩
  have hsecondMem : secondEdge ∈ incidentCrossings := by
    exact Finset.mem_filter.2
      ⟨by simpa [incidentEdgeFinset] using hsecondIncident, hsecondCrossing⟩
  have hthirdMem : thirdEdge ∈ incidentCrossings := by
    exact Finset.mem_filter.2
      ⟨by simpa [incidentEdgeFinset] using hthirdIncident, hthirdCrossing⟩
  have hsubset : ({firstEdge, secondEdge, thirdEdge} : Finset G.edgeSet) ⊆
      incidentCrossings := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirstMem
    · exact hsecondMem
    · exact hthirdMem
  have hthree : ({firstEdge, secondEdge, thirdEdge} : Finset G.edgeSet).card = 3 := by
    simp [hfirstSecond, hfirstThird, hsecondThird]
  have hle := Finset.card_le_card hsubset
  rw [hthree, show incidentCrossings.card = 2 by exact hcard] at hle
  omega

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

/-- The two named collision sides have the same four-way endpoint
allocation as the two named source rungs. -/
theorem SquareBondRealization.collisionSideEndpointAllocation
    {face : SelectedFace web}
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
        (nextCorridorInterior firstInterior hfirstNext).center)
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        (squareDualCycleWithSecondRung (rungs := rungs)
          hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges)
        ).ConnectedComponent}
    (bond : SquareBondRealization
      (squareDualCycleWithSecondRung (rungs := rungs)
        hfirst hthird hfaceSecond).cycle component) :
    let square := squareDualCycleWithSecondRung (rungs := rungs)
      hfirst hthird hfaceSecond
    bond.CollisionSideEndpointAllocation
      (square.cycle.selectedCycle.crossingEdge (squareThirdStep square))
      (square.cycle.selectedCycle.crossingEdge (squareFourthStep square)) := by
  dsimp only
  let square := squareDualCycleWithSecondRung (rungs := rungs)
    hfirst hthird hfaceSecond
  let thirdEdge :=
    square.cycle.selectedCycle.crossingEdge (squareThirdStep square)
  let fourthEdge :=
    square.cycle.selectedCycle.crossingEdge (squareFourthStep square)
  have hthirdCrossing : thirdEdge ∈ square.cycle.selectedCycle.crossingEdges :=
    (square.cycle.selectedCycle.mem_crossingEdges_iff thirdEdge).2
      ⟨squareThirdStep square, rfl⟩
  have hfourthCrossing : fourthEdge ∈ square.cycle.selectedCycle.crossingEdges :=
    (square.cycle.selectedCycle.mem_crossingEdges_iff fourthEdge).2
      ⟨squareFourthStep square, rfl⟩
  rcases bond.covers_crossingEdges thirdEdge hthirdCrossing with
    hthirdFirst | hthirdSecond <;>
    rcases bond.covers_crossingEdges fourthEdge hfourthCrossing with
      hfourthFirst | hfourthSecond
  · exact .sameFirst hthirdFirst hfourthFirst
  · exact .firstThenSecond hthirdFirst hfourthSecond
  · exact .secondThenFirst hthirdSecond hfourthFirst
  · exact .sameSecond hthirdSecond hfourthSecond

/-- **L1 exact square endpoint allocation.**  The four named square
crossings have one of six, rather than sixteen, compatible endpoint
distributions.  The impossible cases are excluded solely by the proved local
cubic count of two selected crossings at each bond endpoint. -/
theorem SquareBondRealization.sourceAndCollisionEndpointAllocation
    {face : SelectedFace web}
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
        (nextCorridorInterior firstInterior hfirstNext).center)
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        (squareDualCycleWithSecondRung (rungs := rungs)
          hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges)
        ).ConnectedComponent}
    (bond : SquareBondRealization
      (squareDualCycleWithSecondRung (rungs := rungs)
        hfirst hthird hfaceSecond).cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    let square := squareDualCycleWithSecondRung (rungs := rungs)
      hfirst hthird hfaceSecond
    bond.SourceAndCollisionEndpointAllocation
      (rungs.edge firstInterior.outgoing)
      (rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing)
      (square.cycle.selectedCycle.crossingEdge (squareThirdStep square))
      (square.cycle.selectedCycle.crossingEdge (squareFourthStep square)) := by
  classical
  dsimp only
  let square := squareDualCycleWithSecondRung (rungs := rungs)
    hfirst hthird hfaceSecond
  let firstRung := rungs.edge firstInterior.outgoing
  let secondRung :=
    rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing
  let thirdEdge :=
    square.cycle.selectedCycle.crossingEdge (squareThirdStep square)
  let fourthEdge :=
    square.cycle.selectedCycle.crossingEdge (squareFourthStep square)
  have hrungs := bond.sourceRungEndpointAllocation
    (rungs := rungs) hfirst hthird hfaceSecond
  have hsides := bond.collisionSideEndpointAllocation
    (rungs := rungs) hfirst hthird hfaceSecond
  have hrungsCross := sourceRungs_mem_crossingEdges (rungs := rungs)
    hfirst hthird hfaceSecond
  have hthirdCross : thirdEdge ∈ square.cycle.selectedCycle.crossingEdges :=
    (square.cycle.selectedCycle.mem_crossingEdges_iff thirdEdge).2
      ⟨squareThirdStep square, rfl⟩
  have hfourthCross : fourthEdge ∈ square.cycle.selectedCycle.crossingEdges :=
    (square.cycle.selectedCycle.mem_crossingEdges_iff fourthEdge).2
      ⟨squareFourthStep square, rfl⟩
  have hremEq := sourceRungRemainder_eq_collisionSideCrossings
    (rungs := rungs) hfirst hthird hfaceSecond
  have hthirdRem : thirdEdge ∈ sourceRungRemainder (rungs := rungs)
      hfirst hthird hfaceSecond := by
    rw [hremEq]
    simp [square, thirdEdge]
  have hfourthRem : fourthEdge ∈ sourceRungRemainder (rungs := rungs)
      hfirst hthird hfaceSecond := by
    rw [hremEq]
    simp [square, fourthEdge]
  rw [sourceRungRemainder] at hthirdRem hfourthRem
  have hthirdSecond : thirdEdge ≠ secondRung := by
    simpa [secondRung] using (Finset.mem_erase.1 hthirdRem).1
  have hthirdFirst : thirdEdge ≠ firstRung := by
    simpa [firstRung] using (Finset.mem_erase.1
      (Finset.mem_erase.1 hthirdRem).2).1
  have hfourthSecond : fourthEdge ≠ secondRung := by
    simpa [secondRung] using (Finset.mem_erase.1 hfourthRem).1
  have hfourthFirst : fourthEdge ≠ firstRung := by
    simpa [firstRung] using (Finset.mem_erase.1
      (Finset.mem_erase.1 hfourthRem).2).1
  have hfirstSecond : firstRung ≠ secondRung := by
    simpa [firstRung, secondRung] using
      sourceRungs_ne (rungs := rungs) hfirst hthird hfaceSecond
  have hthirdFourth : thirdEdge ≠ fourthEdge := by
    intro heq
    have hstep := square.cycle.selectedCycle.crossingEdge_injective
      (orbitFace_incidence_le_two web.annular.RS) heq
    have hval := congrArg Fin.val hstep
    simp at hval
  have hfirstCard := bond.first_crossingEdges_card_eq_two hroot
  have hsecondCard := bond.second_crossingEdges_card_eq_two hroot
  change bond.SourceRungEndpointAllocation firstRung secondRung at hrungs
  change bond.CollisionSideEndpointAllocation thirdEdge fourthEdge at hsides
  change firstRung ∈ square.cycle.selectedCycle.crossingEdges ∧
    secondRung ∈ square.cycle.selectedCycle.crossingEdges at hrungsCross
  cases hrungs with
  | sameFirst hfirstRung hsecondRung =>
      cases hsides with
      | sameFirst hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.first) hfirstCard
            hrungsCross.1 hrungsCross.2 hthirdCross
            hfirstRung hsecondRung hthird hfirstSecond
            hthirdFirst.symm hthirdSecond.symm).elim
      | sameSecond hthird hfourth =>
          exact .rungsFirst_sidesSecond
            hfirstRung hsecondRung hthird hfourth
      | firstThenSecond hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.first) hfirstCard
            hrungsCross.1 hrungsCross.2 hthirdCross
            hfirstRung hsecondRung hthird hfirstSecond
            hthirdFirst.symm hthirdSecond.symm).elim
      | secondThenFirst hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.first) hfirstCard
            hrungsCross.1 hrungsCross.2 hfourthCross
            hfirstRung hsecondRung hfourth hfirstSecond
            hfourthFirst.symm hfourthSecond.symm).elim
  | sameSecond hfirstRung hsecondRung =>
      cases hsides with
      | sameFirst hthird hfourth =>
          exact .rungsSecond_sidesFirst
            hfirstRung hsecondRung hthird hfourth
      | sameSecond hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.second) hsecondCard
            hrungsCross.1 hrungsCross.2 hthirdCross
            hfirstRung hsecondRung hthird hfirstSecond
            hthirdFirst.symm hthirdSecond.symm).elim
      | firstThenSecond hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.second) hsecondCard
            hrungsCross.1 hrungsCross.2 hfourthCross
            hfirstRung hsecondRung hfourth hfirstSecond
            hfourthFirst.symm hfourthSecond.symm).elim
      | secondThenFirst hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.second) hsecondCard
            hrungsCross.1 hrungsCross.2 hthirdCross
            hfirstRung hsecondRung hthird hfirstSecond
            hthirdFirst.symm hthirdSecond.symm).elim
  | firstThenSecond hfirstRung hsecondRung =>
      cases hsides with
      | sameFirst hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.first) hfirstCard
            hrungsCross.1 hthirdCross hfourthCross
            hfirstRung hthird hfourth hthirdFirst.symm hfourthFirst.symm
            hthirdFourth).elim
      | sameSecond hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.second) hsecondCard
            hrungsCross.2 hthirdCross hfourthCross
            hsecondRung hthird hfourth hthirdSecond.symm hfourthSecond.symm
            hthirdFourth).elim
      | firstThenSecond hthird hfourth =>
          exact .firstThenSecond_firstThenSecond
            hfirstRung hsecondRung hthird hfourth
      | secondThenFirst hthird hfourth =>
          exact .firstThenSecond_secondThenFirst
            hfirstRung hsecondRung hthird hfourth
  | secondThenFirst hfirstRung hsecondRung =>
      cases hsides with
      | sameFirst hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.first) hfirstCard
            hrungsCross.2 hthirdCross hfourthCross
            hsecondRung hthird hfourth hthirdSecond.symm hfourthSecond.symm
            hthirdFourth).elim
      | sameSecond hthird hfourth =>
          exact (false_of_three_distinct_selected_crossings_meet
            (vertex := bond.second) hsecondCard
            hrungsCross.1 hthirdCross hfourthCross
            hfirstRung hthird hfourth hthirdFirst.symm hfourthFirst.symm
            hthirdFourth).elim
      | firstThenSecond hthird hfourth =>
          exact .secondThenFirst_firstThenSecond
            hfirstRung hsecondRung hthird hfourth
      | secondThenFirst hthird hfourth =>
          exact .secondThenFirst_secondThenFirst
            hfirstRung hsecondRung hthird hfourth

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
