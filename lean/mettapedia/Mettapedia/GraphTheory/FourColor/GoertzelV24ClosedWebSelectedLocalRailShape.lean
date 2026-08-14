import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalLayerFormation

/-!
# Finite selected rail shapes through one literal Cell-3 hexagon

Fable flag L1 requires a finite classification of the local connectors in the
hexagonal patch.  The older rail-shape theorem performed this calculation only
for placements carrying a global pairwise-unique-shared-edge hypothesis.  The
literal selected-rung representation needs no such hypothesis: the calculation
depends only on the two rung coordinates in a six-cycle.

The result retains all three source shapes: `0+2`, `1+1`, and `2+0`.  In
particular, a stationary rail is a legitimate local identity connector, not a
collision to be discarded.  This file classifies one local Cell-3 connector;
it does not yet prove appendwise simplicity, remote separation, end caps, or
the final long crosscut pair.
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
open GoertzelV24HexFaceRungType
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

/-- The three finite rail shapes through one literal selected Cell-3 hexagon.
The endpoints are the two side slots flanking its incoming rung and the two
side slots flanking its outgoing rung. -/
inductive SelectedSourceLocalRailShape
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ selectedPlacementSidePositions placement}) : Type where
  /-- Forward distance two: the first rail is stationary and the second rail
  has two successive local pieces. -/
  | forwardTwo
      (first_eq : incomingBefore = outgoingBefore)
      (middle : {position // position ∈ selectedPlacementSidePositions placement})
      (outgoingAfter_to_middle :
        middle.1.val ≡ outgoingAfter.1.val + 1 [MOD 6])
      (middle_to_incomingAfter :
        incomingAfter.1.val ≡ middle.1.val + 1 [MOD 6])
  /-- Forward distance three: both rails have one local piece. -/
  | forwardThree
      (first_step :
        outgoingBefore.1.val ≡ incomingBefore.1.val + 1 [MOD 6])
      (second_step :
        incomingAfter.1.val ≡ outgoingAfter.1.val + 1 [MOD 6])
  /-- Forward distance four: the first rail has two successive local pieces
  and the second rail is stationary. -/
  | forwardFour
      (middle : {position // position ∈ selectedPlacementSidePositions placement})
      (incomingBefore_to_middle :
        middle.1.val ≡ incomingBefore.1.val + 1 [MOD 6])
      (middle_to_outgoingBefore :
        outgoingBefore.1.val ≡ middle.1.val + 1 [MOD 6])
      (second_eq : incomingAfter = outgoingAfter)

private theorem selectedPlacementSidePosition_eq_of_modEq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left right :
      {position // position ∈ selectedPlacementSidePositions placement})
    (hmod : left.1.val ≡ right.1.val [MOD 6]) : left = right := by
  apply Subtype.ext
  apply Fin.ext
  rw [Nat.ModEq] at hmod
  have hleft : left.1.val < 6 := by
    simpa only [placement.orbit_card] using left.1.isLt
  have hright : right.1.val < 6 := by
    simpa only [placement.orbit_card] using right.1.isLt
  simpa [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] using hmod

private theorem selected_outgoing_modEq_of_hexForwardDistance_two
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 2) :
    outgoing.val ≡ incoming.val + 2 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

private theorem selected_outgoing_modEq_of_hexForwardDistance_three
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 3) :
    outgoing.val ≡ incoming.val + 3 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

private theorem selected_outgoing_modEq_of_hexForwardDistance_four
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 4) :
    outgoing.val ≡ incoming.val + 4 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

private theorem exists_selected_forwardTwo_middleSidePosition
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 2) :
    ∃ middle : {position // position ∈ hexSidePositions incoming outgoing},
      middle.1.val ≡ incoming.val + 4 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSidePositions, hexForwardDistance, Nat.ModEq] at * <;>
    decide

private theorem exists_selected_forwardFour_middleSidePosition
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 4) :
    ∃ middle : {position // position ∈ hexSidePositions incoming outgoing},
      middle.1.val ≡ incoming.val + 2 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSidePositions, hexForwardDistance, Nat.ModEq] at * <;>
    decide

/-- **L1 finite selected connector classification.** The four literal flank
slots around a selected Cell-3 placement have exactly one of the three source
rail shapes `0+2`, `1+1`, or `2+0`.

This calculation uses only the six-cycle coordinates and the Cell-3
nonadjacency theorem.  It does not import the closed-map global
pairwise-unique-shared-edge hypothesis. -/
theorem selectedSourceLocalRailShape_of_cell3
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ selectedPlacementSidePositions placement})
    (hincomingBefore : incomingBefore.1.val ≡
      placement.incomingPosition.val + 1 [MOD 6])
    (hincomingAfter : placement.incomingPosition.val ≡
      incomingAfter.1.val + 1 [MOD 6])
    (houtgoingBefore : placement.outgoingPosition.val ≡
      outgoingBefore.1.val + 1 [MOD 6])
    (houtgoingAfter : outgoingAfter.1.val ≡
      placement.outgoingPosition.val + 1 [MOD 6]) :
    Nonempty (SelectedSourceLocalRailShape placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) := by
  have hnonadjacent :=
    SelectedInternalHexRungPlacement.rungType_ne_adjacent_of_cell3
      corridor rungs interior placement
  rcases hexForwardDistance_eq_two_or_three_or_four
      placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent with htwo | hthree | hfour
  · have hforward6 := selected_outgoing_modEq_of_hexForwardDistance_two
      placement.incomingPosition6 placement.outgoingPosition6 htwo
    have hforward : placement.outgoingPosition.val ≡
        placement.incomingPosition.val + 2 [MOD 6] := by
      simpa [SelectedInternalHexRungPlacement.incomingPosition6,
        SelectedInternalHexRungPlacement.outgoingPosition6] using hforward6
    have hfirstMod : incomingBefore.1.val ≡
        outgoingBefore.1.val [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward ⊢
      omega
    have hfirstEq := selectedPlacementSidePosition_eq_of_modEq placement
      incomingBefore outgoingBefore hfirstMod
    rcases exists_selected_forwardTwo_middleSidePosition
        placement.incomingPosition6 placement.outgoingPosition6 htwo with
      ⟨middle6, hmiddle6⟩
    let middle := selectedPlacementSidePositionOfSix placement middle6
    have hmiddle : middle.1.val ≡
        placement.incomingPosition.val + 4 [MOD 6] := by
      simpa [middle, selectedPlacementSidePositionOfSix,
        selectedPlacementPositionOfSix,
        SelectedInternalHexRungPlacement.incomingPosition6] using hmiddle6
    have houtgoingAfterMiddle : middle.1.val ≡
        outgoingAfter.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward hmiddle ⊢
      omega
    have hmiddleIncomingAfter : incomingAfter.1.val ≡
        middle.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward hmiddle ⊢
      omega
    exact ⟨.forwardTwo hfirstEq middle houtgoingAfterMiddle
      hmiddleIncomingAfter⟩
  · have hforward6 := selected_outgoing_modEq_of_hexForwardDistance_three
      placement.incomingPosition6 placement.outgoingPosition6 hthree
    have hforward : placement.outgoingPosition.val ≡
        placement.incomingPosition.val + 3 [MOD 6] := by
      simpa [SelectedInternalHexRungPlacement.incomingPosition6,
        SelectedInternalHexRungPlacement.outgoingPosition6] using hforward6
    have hfirst : outgoingBefore.1.val ≡
        incomingBefore.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward ⊢
      omega
    have hsecond : incomingAfter.1.val ≡
        outgoingAfter.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward ⊢
      omega
    exact ⟨.forwardThree hfirst hsecond⟩
  · have hforward6 := selected_outgoing_modEq_of_hexForwardDistance_four
      placement.incomingPosition6 placement.outgoingPosition6 hfour
    have hforward : placement.outgoingPosition.val ≡
        placement.incomingPosition.val + 4 [MOD 6] := by
      simpa [SelectedInternalHexRungPlacement.incomingPosition6,
        SelectedInternalHexRungPlacement.outgoingPosition6] using hforward6
    rcases exists_selected_forwardFour_middleSidePosition
        placement.incomingPosition6 placement.outgoingPosition6 hfour with
      ⟨middle6, hmiddle6⟩
    let middle := selectedPlacementSidePositionOfSix placement middle6
    have hmiddle : middle.1.val ≡
        placement.incomingPosition.val + 2 [MOD 6] := by
      simpa [middle, selectedPlacementSidePositionOfSix,
        selectedPlacementPositionOfSix,
        SelectedInternalHexRungPlacement.incomingPosition6] using hmiddle6
    have hincomingBeforeMiddle : middle.1.val ≡
        incomingBefore.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward hmiddle ⊢
      omega
    have hmiddleOutgoingBefore : outgoingBefore.1.val ≡
        middle.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward hmiddle ⊢
      omega
    have hsecondMod : incomingAfter.1.val ≡
        outgoingAfter.1.val [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward hmiddle ⊢
      omega
    have hsecondEq := selectedPlacementSidePosition_eq_of_modEq placement
      incomingAfter outgoingAfter hsecondMod
    exact ⟨.forwardFour middle hincomingBeforeMiddle hmiddleOutgoingBefore
      hsecondEq⟩

/-- Two literal simple facial-dual paths read from one selected finite rail
shape.  The total length can drop below two when a local opposite-dart face
coincides with its successor; loop erasure retains the endpoints and removes
that harmless local repetition.

No mutual-support-disjointness field is included here.  That property belongs
to the subsequent L1 collision/separation classification, not to the finite
coordinate shape itself. -/
structure SelectedSourceLocalRailPaths
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ selectedPlacementSidePositions placement}) where
  firstRail :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace placement incomingBefore)
        (selectedPlacementSideFace placement outgoingBefore)
  secondRail :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace placement incomingAfter)
        (selectedPlacementSideFace placement outgoingAfter)
  firstRail_isPath : firstRail.IsPath
  secondRail_isPath : secondRail.IsPath
  firstRail_length_le_two : firstRail.length ≤ 2
  secondRail_length_le_two : secondRail.length ≤ 2
  firstRail_length_add_secondRail_length_le_two :
    firstRail.length + secondRail.length ≤ 2

/-- Realize a selected `0+2`, `1+1`, or `2+0` coordinate certificate as two
literal bounded simple facial-dual paths.  Each one-step constituent is read
from the selected opposite-dart geometry; `Walk.bypass` removes only repeated
local faces and never invents an adjacency. -/
noncomputable def selectedSourceLocalRailPathsOfShape
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ selectedPlacementSidePositions placement})
    (shape : SelectedSourceLocalRailShape placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) :
    SelectedSourceLocalRailPaths placement incomingBefore incomingAfter
      outgoingBefore outgoingAfter := by
  cases shape with
  | forwardTwo first_eq middle houtMiddle hmiddleIn =>
      let houtWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement outgoingAfter middle houtMiddle
      let outMiddle := Classical.choose houtWitness
      have houtMiddleLength : outMiddle.length ≤ 1 := by
        simpa [outMiddle] using (Classical.choose_spec houtWitness).2
      let hinWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement middle incomingAfter hmiddleIn
      let middleIn := Classical.choose hinWitness
      have hmiddleInLength : middleIn.length ≤ 1 := by
        simpa [middleIn] using (Classical.choose_spec hinWitness).2
      let rawFirst :
          (interiorDualGraph (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
              (selectedPlacementSideFace placement incomingBefore)
              (selectedPlacementSideFace placement outgoingBefore) :=
        SimpleGraph.Walk.nil.copy rfl
          (congrArg (selectedPlacementSideFace placement) first_eq)
      let rawSecond := middleIn.reverse.append outMiddle.reverse
      have hfirstBypass := rawFirst.length_bypass_le_length
      have hsecondBypass := rawSecond.length_bypass_le_length
      have hrawFirst : rawFirst.length = 0 := by simp [rawFirst]
      have hrawSecond : rawSecond.length = middleIn.length + outMiddle.length := by
        simp [rawSecond]
      refine {
        firstRail := rawFirst.bypass
        secondRail := rawSecond.bypass
        firstRail_isPath := rawFirst.bypass_isPath
        secondRail_isPath := rawSecond.bypass_isPath
        firstRail_length_le_two := by omega
        secondRail_length_le_two := by omega
        firstRail_length_add_secondRail_length_le_two := by
          omega }
  | forwardThree hfirst hsecond =>
      let hfirstWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement incomingBefore outgoingBefore hfirst
      let firstStep := Classical.choose hfirstWitness
      have hfirstLength : firstStep.length ≤ 1 := by
        simpa [firstStep] using (Classical.choose_spec hfirstWitness).2
      let hsecondWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement outgoingAfter incomingAfter hsecond
      let secondStep := Classical.choose hsecondWitness
      have hsecondLength : secondStep.length ≤ 1 := by
        simpa [secondStep] using (Classical.choose_spec hsecondWitness).2
      let rawFirst := firstStep
      let rawSecond := secondStep.reverse
      have hfirstBypass := rawFirst.length_bypass_le_length
      have hsecondBypass := rawSecond.length_bypass_le_length
      have hrawFirst : rawFirst.length = firstStep.length := by rfl
      have hrawSecond : rawSecond.length = secondStep.length := by
        simp [rawSecond]
      refine {
        firstRail := rawFirst.bypass
        secondRail := rawSecond.bypass
        firstRail_isPath := rawFirst.bypass_isPath
        secondRail_isPath := rawSecond.bypass_isPath
        firstRail_length_le_two := by omega
        secondRail_length_le_two := by omega
        firstRail_length_add_secondRail_length_le_two := by omega }
  | forwardFour middle hinMiddle hmiddleOut second_eq =>
      let hinWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement incomingBefore middle hinMiddle
      let inMiddle := Classical.choose hinWitness
      have hinMiddleLength : inMiddle.length ≤ 1 := by
        simpa [inMiddle] using (Classical.choose_spec hinWitness).2
      let houtWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement middle outgoingBefore hmiddleOut
      let middleOut := Classical.choose houtWitness
      have hmiddleOutLength : middleOut.length ≤ 1 := by
        simpa [middleOut] using (Classical.choose_spec houtWitness).2
      let rawFirst := inMiddle.append middleOut
      let rawSecond :
          (interiorDualGraph (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
              (selectedPlacementSideFace placement incomingAfter)
              (selectedPlacementSideFace placement outgoingAfter) :=
        SimpleGraph.Walk.nil.copy rfl
          (congrArg (selectedPlacementSideFace placement) second_eq)
      have hfirstBypass := rawFirst.length_bypass_le_length
      have hsecondBypass := rawSecond.length_bypass_le_length
      have hrawFirst : rawFirst.length = inMiddle.length + middleOut.length := by
        simp [rawFirst]
      have hrawSecond : rawSecond.length = 0 := by simp [rawSecond]
      refine {
        firstRail := rawFirst.bypass
        secondRail := rawSecond.bypass
        firstRail_isPath := rawFirst.bypass_isPath
        secondRail_isPath := rawSecond.bypass_isPath
        firstRail_length_le_two := by omega
        secondRail_length_le_two := by omega
        firstRail_length_add_secondRail_length_le_two := by omega }

/-- **L1 selected bounded local rails.** Every literal selected Cell-3
placement, together with its four oriented flank slots, constructs two simple
facial-dual rail paths of total length at most two.  The theorem preserves the
stationary alternatives rather than importing a global face-intersection
uniqueness assumption.

This is still one local connector.  It does not assert that the two paths are
mutually disjoint or that connectors from different cells append to a long
end-capped crosscut. -/
theorem exists_selectedSourceLocalRailPaths_of_cell3
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ selectedPlacementSidePositions placement})
    (hincomingBefore : incomingBefore.1.val ≡
      placement.incomingPosition.val + 1 [MOD 6])
    (hincomingAfter : placement.incomingPosition.val ≡
      incomingAfter.1.val + 1 [MOD 6])
    (houtgoingBefore : placement.outgoingPosition.val ≡
      outgoingBefore.1.val + 1 [MOD 6])
    (houtgoingAfter : outgoingAfter.1.val ≡
      placement.outgoingPosition.val + 1 [MOD 6]) :
    Nonempty (SelectedSourceLocalRailPaths placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) := by
  rcases selectedSourceLocalRailShape_of_cell3 placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter hincomingBefore hincomingAfter
      houtgoingBefore houtgoingAfter with ⟨shape⟩
  exact ⟨selectedSourceLocalRailPathsOfShape placement incomingBefore
    incomingAfter outgoingBefore outgoingAfter shape⟩

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
