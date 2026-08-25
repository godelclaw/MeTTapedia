import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalInterfaceOrientation

/-!
# Source-local Cell-3 rail steps

The closed-web carrier is not globally cubic.  Nevertheless, two consecutive
surviving side slots of one certified interior Cell-3 face determine adjacent
exterior faces: the only cubicity required is the three-dart rotation at their
single common corner.  This is the local incidence lemma needed to turn the
canonical rail coordinates into literal facial-dual rail segments.

This file constructs one local step.  It does not yet assert that repeated
steps append to simple end-capped rails or realize a global annular crosscut.
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
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

/-- **Local rail adjacency (not Fable flag L1).** Consecutive surviving slots of one
source-derived Cell-3 face give a genuine exterior facial-dual edge.  Unlike
the framed-corridor analogue, this theorem assumes no global cubicity: it uses
only the certified three-dart rotation at the displayed interior corner. -/
theorem localPlacementSideFaces_adjacent_of_forwardStep
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (left right : {position // position ∈ placementSidePositions placement})
    (hsuccessor : right.1.val ≡ left.1.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (localPlacementSideFace placement left)
        (localPlacementSideFace placement right) := by
  let leftDart := faceCycleDart web.annular.RS placement.root left.1
  let rightDart := faceCycleDart web.annular.RS placement.root right.1
  have hdarts : rightDart = web.annular.RS.phi leftDart := by
    exact faceCycleDart_successor_of_modEq web.annular.RS placement.root
      placement.orbit_card left.1 right.1 hsuccessor
  have hpositionsNe : left ≠ right := by
    intro heq
    have hvalEq : left.1.val = right.1.val :=
      congrArg (fun position => position.1.val) heq
    have hselfSuccessor : left.1.val ≡ left.1.val + 1 [MOD 6] := by
      simpa only [hvalEq] using hsuccessor
    have hleftBound : left.1.val < 6 := by
      simpa only [placement.orbit_card] using left.1.isLt
    interval_cases hleft : left.1.val <;>
      norm_num [Nat.ModEq, hleft] at hselfSuccessor
  have hfacesNe : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha leftDart) ≠
      dartOrbitFace web.annular.RS
        (web.annular.RS.alpha (web.annular.RS.phi leftDart)) := by
    intro hfaces
    apply hpositionsNe
    apply localPlacementSideFace_injective (corridor := corridor) placement
    apply Subtype.ext
    change dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart) =
      dartOrbitFace web.annular.RS (web.annular.RS.alpha rightDart)
    rw [hdarts]
    exact hfaces
  have hcornerCard : (web.annular.RS.dartsAt
      (web.annular.RS.vertOf (web.annular.RS.alpha leftDart))).card = 3 := by
    apply InteriorFace.dartsAt_card_eq_three web
    change (localPlacementSideFace placement left).1 ∈
      web.annular.cellulation.interiorFaces
    exact localPlacementSideFace_internal (corridor := corridor) placement left
  have hadj := oppositeFaces_adjacent_at_locally_cubic_corner web.annular.RS
    (InteriorFace.vertexRotationCyclic web) leftDart hcornerCard hfacesNe
  simpa only [localPlacementSideFace, leftDart, rightDart, hdarts] using hadj

/-- The three possible literal rail shapes through one nonadjacent Cell-3
hexagon.  The endpoints are the two side slots flanking its incoming rung and
the two side slots flanking its outgoing rung. -/
inductive SourceLocalRailShape
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ placementSidePositions placement}) : Type where
  /-- Forward distance two: the first rail is stationary and the second rail
  uses two consecutive exterior edges. -/
  | forwardTwo
      (first_eq : incomingBefore = outgoingBefore)
      (middle : {position // position ∈ placementSidePositions placement})
      (outgoingAfter_to_middle :
        middle.1.val ≡ outgoingAfter.1.val + 1 [MOD 6])
      (middle_to_incomingAfter :
        incomingAfter.1.val ≡ middle.1.val + 1 [MOD 6])
  /-- Forward distance three: each rail uses one exterior edge. -/
  | forwardThree
      (first_step :
        outgoingBefore.1.val ≡ incomingBefore.1.val + 1 [MOD 6])
      (second_step :
        incomingAfter.1.val ≡ outgoingAfter.1.val + 1 [MOD 6])
  /-- Forward distance four: the first rail uses two exterior edges and the
  second rail is stationary. -/
  | forwardFour
      (middle : {position // position ∈ placementSidePositions placement})
      (incomingBefore_to_middle :
        middle.1.val ≡ incomingBefore.1.val + 1 [MOD 6])
      (middle_to_outgoingBefore :
        outgoingBefore.1.val ≡ middle.1.val + 1 [MOD 6])
      (second_eq : incomingAfter = outgoingAfter)

private theorem placementSidePosition_eq_of_modEq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (left right : {position // position ∈ placementSidePositions placement})
    (hmod : left.1.val ≡ right.1.val [MOD 6]) : left = right := by
  apply Subtype.ext
  apply Fin.ext
  rw [Nat.ModEq] at hmod
  have hleft : left.1.val < 6 := by
    simpa only [placement.orbit_card] using left.1.isLt
  have hright : right.1.val < 6 := by
    simpa only [placement.orbit_card] using right.1.isLt
  simpa [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] using hmod

private theorem outgoing_modEq_of_hexForwardDistance_two
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 2) :
    outgoing.val ≡ incoming.val + 2 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

private theorem outgoing_modEq_of_hexForwardDistance_three
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 3) :
    outgoing.val ≡ incoming.val + 3 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

private theorem outgoing_modEq_of_hexForwardDistance_four
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 4) :
    outgoing.val ≡ incoming.val + 4 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

private theorem exists_forwardTwo_middleSidePosition
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 2) :
    ∃ middle : {position // position ∈ hexSidePositions incoming outgoing},
      middle.1.val ≡ incoming.val + 4 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSidePositions, hexForwardDistance, Nat.ModEq] at * <;>
    decide

private theorem exists_forwardFour_middleSidePosition
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 4) :
    ∃ middle : {position // position ∈ hexSidePositions incoming outgoing},
      middle.1.val ≡ incoming.val + 2 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSidePositions, hexForwardDistance, Nat.ModEq] at * <;>
    decide

/-- **Finite local rail shape (not Fable flag L1).** The four literal flank slots around a
nonadjacent source Cell-3 placement have exactly one of the three rail shapes
`0+2`, `1+1`, or `2+0`.  This is a finite cyclic-coordinate theorem, not an
assumption about an ambient rail chain. -/
theorem sourceLocalRailShape_of_nonadjacent
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ placementSidePositions placement})
    (hincomingBefore : incomingBefore.1.val ≡
      placement.incomingPosition.val + 1 [MOD 6])
    (hincomingAfter : placement.incomingPosition.val ≡
      incomingAfter.1.val + 1 [MOD 6])
    (houtgoingBefore : placement.outgoingPosition.val ≡
      outgoingBefore.1.val + 1 [MOD 6])
    (houtgoingAfter : outgoingAfter.1.val ≡
      placement.outgoingPosition.val + 1 [MOD 6])
    (hnonadjacent : placement.rungType ≠ HexRungType.adjacent) :
    Nonempty (SourceLocalRailShape placement incomingBefore incomingAfter
      outgoingBefore outgoingAfter) := by
  rcases hexForwardDistance_eq_two_or_three_or_four
      placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent with htwo | hthree | hfour
  · have hforward6 := outgoing_modEq_of_hexForwardDistance_two
      placement.incomingPosition6 placement.outgoingPosition6 htwo
    have hforward : placement.outgoingPosition.val ≡
        placement.incomingPosition.val + 2 [MOD 6] := by
      simpa [InternalHexRungPlacement.incomingPosition6,
        InternalHexRungPlacement.outgoingPosition6] using hforward6
    have hfirstMod : incomingBefore.1.val ≡
        outgoingBefore.1.val [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward ⊢
      omega
    have hfirstEq := placementSidePosition_eq_of_modEq placement
      incomingBefore outgoingBefore hfirstMod
    rcases exists_forwardTwo_middleSidePosition
        placement.incomingPosition6 placement.outgoingPosition6 htwo with
      ⟨middle6, hmiddle6⟩
    let middle := placementSidePositionOfSix placement middle6
    have hmiddle : middle.1.val ≡
        placement.incomingPosition.val + 4 [MOD 6] := by
      simpa [middle, placementSidePositionOfSix, placementPositionOfSix,
        InternalHexRungPlacement.incomingPosition6] using hmiddle6
    have houtgoingAfterMiddle : middle.1.val ≡
        outgoingAfter.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward hmiddle ⊢
      omega
    have hmiddleIncomingAfter : incomingAfter.1.val ≡
        middle.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward hmiddle ⊢
      omega
    exact ⟨SourceLocalRailShape.forwardTwo hfirstEq middle
      houtgoingAfterMiddle hmiddleIncomingAfter⟩
  · have hforward6 := outgoing_modEq_of_hexForwardDistance_three
      placement.incomingPosition6 placement.outgoingPosition6 hthree
    have hforward : placement.outgoingPosition.val ≡
        placement.incomingPosition.val + 3 [MOD 6] := by
      simpa [InternalHexRungPlacement.incomingPosition6,
        InternalHexRungPlacement.outgoingPosition6] using hforward6
    have hfirst : outgoingBefore.1.val ≡
        incomingBefore.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward ⊢
      omega
    have hsecond : incomingAfter.1.val ≡
        outgoingAfter.1.val + 1 [MOD 6] := by
      simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hforward ⊢
      omega
    exact ⟨SourceLocalRailShape.forwardThree hfirst hsecond⟩
  · have hforward6 := outgoing_modEq_of_hexForwardDistance_four
      placement.incomingPosition6 placement.outgoingPosition6 hfour
    have hforward : placement.outgoingPosition.val ≡
        placement.incomingPosition.val + 4 [MOD 6] := by
      simpa [InternalHexRungPlacement.incomingPosition6,
        InternalHexRungPlacement.outgoingPosition6] using hforward6
    rcases exists_forwardFour_middleSidePosition
        placement.incomingPosition6 placement.outgoingPosition6 hfour with
      ⟨middle6, hmiddle6⟩
    let middle := placementSidePositionOfSix placement middle6
    have hmiddle : middle.1.val ≡
        placement.incomingPosition.val + 2 [MOD 6] := by
      simpa [middle, placementSidePositionOfSix, placementPositionOfSix,
        InternalHexRungPlacement.incomingPosition6] using hmiddle6
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
    have hsecondEq := placementSidePosition_eq_of_modEq placement
      incomingAfter outgoingAfter hsecondMod
    exact ⟨SourceLocalRailShape.forwardFour middle hincomingBeforeMiddle
      hmiddleOutgoingBefore hsecondEq⟩

/-- Two literal exterior rail walks through one source Cell-3 placement.
Their endpoints are the incoming and outgoing flank slots retained by the
finite shape witness above. -/
structure SourceLocalRailWalkPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ placementSidePositions placement}) where
  firstRail :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (localPlacementSideFace placement incomingBefore)
        (localPlacementSideFace placement outgoingBefore)
  secondRail :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (localPlacementSideFace placement incomingAfter)
        (localPlacementSideFace placement outgoingAfter)
  firstRail_isPath : firstRail.IsPath
  secondRail_isPath : secondRail.IsPath
  firstRail_support_disjoint_secondRail :
    firstRail.support.Disjoint secondRail.support
  firstRail_support_adjacent_center : ∀ face ∈ firstRail.support,
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt interior.center) face
  secondRail_support_adjacent_center : ∀ face ∈ secondRail.support,
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt interior.center) face
  firstRail_length_le_two : firstRail.length ≤ 2
  secondRail_length_le_two : secondRail.length ≤ 2
  firstRail_length_add_secondRail_length_eq_two :
    firstRail.length + secondRail.length = 2

private theorem placementSidePosition_ne_of_two_forwardSteps
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    {placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior}
    (left middle right :
      {position // position ∈ placementSidePositions placement})
    (hfirst : middle.1.val ≡ left.1.val + 1 [MOD 6])
    (hsecond : right.1.val ≡ middle.1.val + 1 [MOD 6]) :
    left ≠ right := by
  intro heq
  have hvalEq : left.1.val = right.1.val :=
    congrArg (fun position => position.1.val) heq
  simp only [Nat.ModEq] at hfirst hsecond
  omega

private theorem localPlacementSideFace_ne_of_position_ne
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    {left right : {position // position ∈ placementSidePositions placement}}
    (hne : left ≠ right) :
    localPlacementSideFace placement left ≠
      localPlacementSideFace placement right := by
  intro hfaces
  exact hne (localPlacementSideFace_injective (corridor := corridor)
    placement hfaces)

private theorem localPlacementSideFace_ne_of_value_ne
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    {left right : {position // position ∈ placementSidePositions placement}}
    (hne : left.1.val ≠ right.1.val) :
    localPlacementSideFace placement left ≠
      localPlacementSideFace placement right := by
  apply localPlacementSideFace_ne_of_position_ne (corridor := corridor)
    placement
  intro hpositions
  exact hne (congrArg (fun position => position.1.val) hpositions)

/-- Read the finite cyclic rail shape as two actual simple facial-dual walks.
No path or length property is postulated: all three cases are built from the
source-local adjacency theorem above. -/
noncomputable def sourceLocalRailWalkPairOfShape
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ placementSidePositions placement})
    (hincomingBefore : incomingBefore.1.val ≡
      placement.incomingPosition.val + 1 [MOD 6])
    (hincomingAfter : placement.incomingPosition.val ≡
      incomingAfter.1.val + 1 [MOD 6])
    (houtgoingBefore : placement.outgoingPosition.val ≡
      outgoingBefore.1.val + 1 [MOD 6])
    (houtgoingAfter : outgoingAfter.1.val ≡
      placement.outgoingPosition.val + 1 [MOD 6])
    (shape : SourceLocalRailShape placement incomingBefore incomingAfter
      outgoingBefore outgoingAfter) :
    SourceLocalRailWalkPair placement incomingBefore incomingAfter
      outgoingBefore outgoingAfter := by
  cases shape with
  | forwardTwo first_eq middle houtMiddle hmiddleIn =>
      have houtAdj := localPlacementSideFaces_adjacent_of_forwardStep
        (corridor := corridor) placement outgoingAfter middle houtMiddle
      have hinAdj := localPlacementSideFaces_adjacent_of_forwardStep
        (corridor := corridor) placement middle incomingAfter hmiddleIn
      let firstRail :
          (interiorDualGraph (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
              (localPlacementSideFace placement incomingBefore)
              (localPlacementSideFace placement outgoingBefore) :=
        SimpleGraph.Walk.nil.copy rfl
          (congrArg (localPlacementSideFace placement) first_eq)
      let secondRail := SimpleGraph.Walk.cons hinAdj.symm
        (SimpleGraph.Walk.cons houtAdj.symm SimpleGraph.Walk.nil)
      have hfirstEqValues : incomingBefore.1.val = outgoingBefore.1.val :=
        congrArg (fun position => position.1.val) first_eq
      have hcrossValues :
          incomingBefore.1.val ≠ incomingAfter.1.val ∧
          incomingBefore.1.val ≠ middle.1.val ∧
          incomingBefore.1.val ≠ outgoingAfter.1.val := by
        simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter houtMiddle hmiddleIn
        constructor
        · intro heq
          omega
        constructor
        · intro heq
          omega
        · intro heq
          omega
      rcases hcrossValues with ⟨hABValue, hAMValue, hADValue⟩
      have hAB := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hABValue
      have hAM := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hAMValue
      have hAD := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hADValue
      have houterNe : localPlacementSideFace placement incomingAfter ≠
          localPlacementSideFace placement outgoingAfter := by
        apply localPlacementSideFace_ne_of_position_ne (corridor := corridor)
          placement
        exact (placementSidePosition_ne_of_two_forwardSteps outgoingAfter middle
          incomingAfter houtMiddle hmiddleIn).symm
      refine {
        firstRail := firstRail
        secondRail := secondRail
        firstRail_isPath := by simp [firstRail]
        secondRail_isPath := ?_
        firstRail_support_disjoint_secondRail := by
          apply List.disjoint_left.mpr
          intro face hfirst hsecond
          simp only [firstRail, secondRail, SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_nil, SimpleGraph.Walk.support_cons,
            List.mem_cons, List.not_mem_nil, or_false] at hfirst hsecond
          rcases hfirst with rfl
          rcases hsecond with hsecond | hsecond | hsecond
          · exact hAB hsecond
          · exact hAM hsecond
          · exact hAD hsecond
        firstRail_support_adjacent_center := by
          intro face hface
          simp only [firstRail, SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_nil, List.mem_singleton] at hface
          subst face
          exact localPlacementSideFace_adjacent_center (corridor := corridor)
            placement incomingBefore
        secondRail_support_adjacent_center := by
          intro face hface
          simp only [secondRail, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hface
          rcases hface with rfl | rfl | rfl
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement incomingAfter
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement middle
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement outgoingAfter
        firstRail_length_le_two := by simp [firstRail]
        secondRail_length_le_two := by simp [secondRail]
        firstRail_length_add_secondRail_length_eq_two := by
          simp [firstRail, secondRail] }
      simp only [secondRail]
      apply SimpleGraph.Walk.IsPath.cons
      · apply SimpleGraph.Walk.IsPath.cons
        · exact SimpleGraph.Walk.IsPath.nil
        · simpa using houtAdj.ne.symm
      · simp only [SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false, not_or]
        exact ⟨hinAdj.ne.symm, houterNe⟩
  | forwardThree hfirst hsecond =>
      have hfirstAdj := localPlacementSideFaces_adjacent_of_forwardStep
        (corridor := corridor) placement incomingBefore outgoingBefore hfirst
      have hsecondAdj := localPlacementSideFaces_adjacent_of_forwardStep
        (corridor := corridor) placement outgoingAfter incomingAfter hsecond
      have hcrossValues :
          incomingBefore.1.val ≠ incomingAfter.1.val ∧
          incomingBefore.1.val ≠ outgoingAfter.1.val ∧
          outgoingBefore.1.val ≠ incomingAfter.1.val ∧
          outgoingBefore.1.val ≠ outgoingAfter.1.val := by
        simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hfirst hsecond
        constructor
        · intro heq
          omega
        constructor
        · intro heq
          omega
        constructor
        · intro heq
          omega
        · intro heq
          omega
      rcases hcrossValues with ⟨hABValue, hADValue, hCBValue, hCDValue⟩
      have hAB := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hABValue
      have hAD := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hADValue
      have hCB := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hCBValue
      have hCD := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hCDValue
      refine {
        firstRail := hfirstAdj.toWalk
        secondRail := hsecondAdj.symm.toWalk
        firstRail_isPath := SimpleGraph.Walk.IsPath.of_adj hfirstAdj
        secondRail_isPath := SimpleGraph.Walk.IsPath.of_adj hsecondAdj.symm
        firstRail_support_disjoint_secondRail := by
          apply List.disjoint_left.mpr
          intro face hfirstMem hsecondMem
          simp only [SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hfirstMem hsecondMem
          rcases hfirstMem with rfl | rfl
          · rcases hsecondMem with hsecondMem | hsecondMem
            · exact hAB hsecondMem
            · exact hAD hsecondMem
          · rcases hsecondMem with hsecondMem | hsecondMem
            · exact hCB hsecondMem
            · exact hCD hsecondMem
        firstRail_support_adjacent_center := by
          intro face hface
          simp only [SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hface
          rcases hface with rfl | rfl
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement incomingBefore
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement outgoingBefore
        secondRail_support_adjacent_center := by
          intro face hface
          simp only [SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hface
          rcases hface with rfl | rfl
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement incomingAfter
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement outgoingAfter
        firstRail_length_le_two := by simp
        secondRail_length_le_two := by simp
        firstRail_length_add_secondRail_length_eq_two := by simp }
  | forwardFour middle hinMiddle hmiddleOut second_eq =>
      have hinAdj := localPlacementSideFaces_adjacent_of_forwardStep
        (corridor := corridor) placement incomingBefore middle hinMiddle
      have houtAdj := localPlacementSideFaces_adjacent_of_forwardStep
        (corridor := corridor) placement middle outgoingBefore hmiddleOut
      let firstRail := SimpleGraph.Walk.cons hinAdj
        (SimpleGraph.Walk.cons houtAdj SimpleGraph.Walk.nil)
      let secondRail :
          (interiorDualGraph (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
              (localPlacementSideFace placement incomingAfter)
              (localPlacementSideFace placement outgoingAfter) :=
        SimpleGraph.Walk.nil.copy rfl
          (congrArg (localPlacementSideFace placement) second_eq)
      have hsecondEqValues : incomingAfter.1.val = outgoingAfter.1.val :=
        congrArg (fun position => position.1.val) second_eq
      have hcrossValues :
          incomingBefore.1.val ≠ incomingAfter.1.val ∧
          middle.1.val ≠ incomingAfter.1.val ∧
          outgoingBefore.1.val ≠ incomingAfter.1.val := by
        simp only [Nat.ModEq] at hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter hinMiddle hmiddleOut
        constructor
        · intro heq
          omega
        constructor
        · intro heq
          omega
        · intro heq
          omega
      rcases hcrossValues with ⟨hABValue, hMBValue, hCBValue⟩
      have hAB := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hABValue
      have hMB := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hMBValue
      have hCB := localPlacementSideFace_ne_of_value_ne
        (corridor := corridor) placement hCBValue
      have houterNe : localPlacementSideFace placement incomingBefore ≠
          localPlacementSideFace placement outgoingBefore := by
        apply localPlacementSideFace_ne_of_position_ne (corridor := corridor)
          placement
        exact placementSidePosition_ne_of_two_forwardSteps incomingBefore middle
          outgoingBefore hinMiddle hmiddleOut
      refine {
        firstRail := firstRail
        secondRail := secondRail
        firstRail_isPath := ?_
        secondRail_isPath := by simp [secondRail]
        firstRail_support_disjoint_secondRail := by
          apply List.disjoint_left.mpr
          intro face hfirst hsecond
          simp only [firstRail, secondRail, SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_nil, SimpleGraph.Walk.support_cons,
            List.mem_cons, List.not_mem_nil, or_false] at hfirst hsecond
          rcases hfirst with rfl | rfl | rfl
          · exact hAB hsecond
          · exact hMB hsecond
          · exact hCB hsecond
        firstRail_support_adjacent_center := by
          intro face hface
          simp only [firstRail, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hface
          rcases hface with rfl | rfl | rfl
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement incomingBefore
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement middle
          · exact localPlacementSideFace_adjacent_center (corridor := corridor)
              placement outgoingBefore
        secondRail_support_adjacent_center := by
          intro face hface
          simp only [secondRail, SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_nil, List.mem_singleton] at hface
          subst face
          exact localPlacementSideFace_adjacent_center (corridor := corridor)
            placement incomingAfter
        firstRail_length_le_two := by simp [firstRail]
        secondRail_length_le_two := by simp [secondRail]
        firstRail_length_add_secondRail_length_eq_two := by
          simp [firstRail, secondRail] }
      simp only [firstRail]
      apply SimpleGraph.Walk.IsPath.cons
      · apply SimpleGraph.Walk.IsPath.cons
        · exact SimpleGraph.Walk.IsPath.nil
        · simpa using houtAdj.ne
      · simp only [SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false, not_or]
        exact ⟨hinAdj.ne, houterNe⟩

/-- **Literal local rail walks (not Fable flag L1).** Every nonadjacent source Cell-3 flank
quadruple constructs two simple exterior rail walks of total length two.  This
is still one cell only; mutual support separation and lengthwise/end-cap
assembly are stated and proved separately. -/
theorem exists_sourceLocalRailWalkPair_of_nonadjacent
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ placementSidePositions placement})
    (hincomingBefore : incomingBefore.1.val ≡
      placement.incomingPosition.val + 1 [MOD 6])
    (hincomingAfter : placement.incomingPosition.val ≡
      incomingAfter.1.val + 1 [MOD 6])
    (houtgoingBefore : placement.outgoingPosition.val ≡
      outgoingBefore.1.val + 1 [MOD 6])
    (houtgoingAfter : outgoingAfter.1.val ≡
      placement.outgoingPosition.val + 1 [MOD 6])
    (hnonadjacent : placement.rungType ≠ HexRungType.adjacent) :
    Nonempty (SourceLocalRailWalkPair placement incomingBefore incomingAfter
      outgoingBefore outgoingAfter) := by
  rcases sourceLocalRailShape_of_nonadjacent placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter hincomingBefore hincomingAfter
      houtgoingBefore houtgoingAfter hnonadjacent with ⟨shape⟩
  exact ⟨sourceLocalRailWalkPairOfShape placement incomingBefore incomingAfter
    outgoingBefore outgoingAfter hincomingBefore hincomingAfter
    houtgoingBefore houtgoingAfter shape⟩

/-- Complete two already oriented incoming flank slots by choosing the two
literal slots flanking the outgoing rung of the same Cell-3 face.  This is a
local existence theorem: the returned paths are separated, but no claim is
made about appending different cells. -/
theorem exists_sourceLocalRailWalkPair_of_incoming
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (incomingBefore incomingAfter :
      {position // position ∈ placementSidePositions placement})
    (hincomingBefore : incomingBefore.1.val ≡
      placement.incomingPosition.val + 1 [MOD 6])
    (hincomingAfter : placement.incomingPosition.val ≡
      incomingAfter.1.val + 1 [MOD 6])
    (hnonadjacent : placement.rungType ≠ HexRungType.adjacent) :
    ∃ outgoingBefore outgoingAfter :
        {position // position ∈ placementSidePositions placement},
      placement.outgoingPosition.val ≡
          outgoingBefore.1.val + 1 [MOD 6] ∧
        outgoingAfter.1.val ≡
          placement.outgoingPosition.val + 1 [MOD 6] ∧
        Nonempty (SourceLocalRailWalkPair placement incomingBefore incomingAfter
          outgoingBefore outgoingAfter) := by
  rcases exists_two_hexSidePositions_flanking_outgoing
      placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent with
    ⟨outgoingBefore6, outgoingAfter6, _, houtgoingBefore6,
      houtgoingAfter6⟩
  let outgoingBefore := placementSidePositionOfSix placement outgoingBefore6
  let outgoingAfter := placementSidePositionOfSix placement outgoingAfter6
  have houtgoingBefore : placement.outgoingPosition.val ≡
      outgoingBefore.1.val + 1 [MOD 6] := by
    simpa [outgoingBefore, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using houtgoingBefore6
  have houtgoingAfter : outgoingAfter.1.val ≡
      placement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [outgoingAfter, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using houtgoingAfter6
  refine ⟨outgoingBefore, outgoingAfter, houtgoingBefore, houtgoingAfter, ?_⟩
  exact exists_sourceLocalRailWalkPair_of_nonadjacent placement incomingBefore
    incomingAfter outgoingBefore outgoingAfter hincomingBefore hincomingAfter
    houtgoingBefore houtgoingAfter hnonadjacent

/-- One source-derived successor rail cell, retaining the finite shape that
generates its literal walks.  Keeping the shape in the same dependent package
prevents a later assembly from combining a case certificate with an unrelated
existential rail witness. -/
structure SourceLocalRailSuccessor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior)
    (leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement})
    (hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6])
    (hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6])
    (rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)) where
  rightBefore :
    {position // position ∈ placementSidePositions rightPlacement}
  rightAfter :
    {position // position ∈ placementSidePositions rightPlacement}
  rightOutgoingBefore :
    {position // position ∈ placementSidePositions rightPlacement}
  rightOutgoingAfter :
    {position // position ∈ placementSidePositions rightPlacement}
  beforeEdge_eq :
    web.annular.RS.edgeOf
        (faceCycleDart web.annular.RS rightPlacement.root rightBefore.1) =
      web.annular.RS.edgeOf
        (web.annular.RS.rho (web.annular.RS.phi
          (faceCycleDart web.annular.RS leftPlacement.root leftBefore.1)))
  beforeFace_eq :
    localPlacementSideFace leftPlacement leftBefore =
      localPlacementSideFace rightPlacement rightBefore
  afterEdge_eq :
    web.annular.RS.edgeOf
        (faceCycleDart web.annular.RS rightPlacement.root rightAfter.1) =
      web.annular.RS.edgeOf
        (web.annular.RS.rho (web.annular.RS.phi
          (faceCycleDart web.annular.RS leftPlacement.root
            leftPlacement.outgoingPosition)))
  afterFace_eq :
    localPlacementSideFace leftPlacement leftAfter =
      localPlacementSideFace rightPlacement rightAfter
  outgoingBefore_mod : rightPlacement.outgoingPosition.val ≡
    rightOutgoingBefore.1.val + 1 [MOD 6]
  outgoingAfter_mod : rightOutgoingAfter.1.val ≡
    rightPlacement.outgoingPosition.val + 1 [MOD 6]
  shape : SourceLocalRailShape rightPlacement rightBefore rightAfter
    rightOutgoingBefore rightOutgoingAfter

/-- The literal rail pair generated by the retained successor shape. -/
noncomputable def SourceLocalRailSuccessor.rails
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
    {leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement}}
    {hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6]}
    {hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6]}
    {rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)}
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    SourceLocalRailWalkPair rightPlacement successor.rightBefore
      successor.rightAfter successor.rightOutgoingBefore
      successor.rightOutgoingAfter :=
  sourceLocalRailWalkPairOfShape rightPlacement successor.rightBefore
    successor.rightAfter successor.rightOutgoingBefore
    successor.rightOutgoingAfter
    (nextLocalPlacement_sidePosition_after_incoming_of_edge_eq leftInterior
      hnext leftPlacement rightPlacement successor.rightBefore (by
        have hleftDart :
            faceCycleDart web.annular.RS leftPlacement.root
                leftPlacement.outgoingPosition =
              web.annular.RS.phi
                (faceCycleDart web.annular.RS leftPlacement.root leftBefore.1) :=
          faceCycleDart_successor_of_modEq web.annular.RS leftPlacement.root
            leftPlacement.orbit_card leftBefore.1
              leftPlacement.outgoingPosition hleftBefore
        rw [hleftDart]
        exact successor.beforeEdge_eq))
    (nextLocalPlacement_incoming_after_sidePosition_of_edge_eq leftInterior
      hnext leftPlacement rightPlacement successor.rightAfter
        successor.afterEdge_eq)
    successor.outgoingBefore_mod successor.outgoingAfter_mod successor.shape

/-- **Literal successor rail cell (not Fable flag L1).** Given the two outgoing flank slots
of one source Cell-3 placement, construct the next placement's two incoming
slots on the same ambient rail edges and return one dependent successor
package.  Its `shape` is the certificate consumed definitionally by `rails`;
there is no independent existential path witness to mismatch after a finite
case split. -/
theorem exists_nextSourceLocalRailWalkPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior)
    (leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement})
    (hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6])
    (hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6])
    (rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)) :
    Nonempty (SourceLocalRailSuccessor hnext leftPlacement leftBefore leftAfter
      hleftBefore hleftAfter rightPlacement) := by
  rcases exists_nextLocalPlacementSideEdge_eq_beforeOutgoingCornerEdge
      (corridor := corridor) hnext leftPlacement leftBefore hleftBefore
      rightPlacement with ⟨rightBefore, hbeforeEdge, hbeforeFace⟩
  rcases exists_nextLocalPlacementSideEdge_eq_afterOutgoingCornerEdge
      (corridor := corridor) hnext leftPlacement leftAfter hleftAfter
      rightPlacement with ⟨rightAfter, hafterEdge, hafterFace⟩
  have hrightBefore :=
    nextLocalPlacement_sidePosition_after_incoming_of_edge_eq leftInterior hnext
      leftPlacement rightPlacement rightBefore (by
        have hleftDart :
            faceCycleDart web.annular.RS leftPlacement.root
                leftPlacement.outgoingPosition =
              web.annular.RS.phi
                (faceCycleDart web.annular.RS leftPlacement.root leftBefore.1) :=
          faceCycleDart_successor_of_modEq web.annular.RS leftPlacement.root
            leftPlacement.orbit_card leftBefore.1
              leftPlacement.outgoingPosition hleftBefore
        rw [hleftDart]
        exact hbeforeEdge)
  have hrightAfter :=
    nextLocalPlacement_incoming_after_sidePosition_of_edge_eq leftInterior hnext
      leftPlacement rightPlacement rightAfter hafterEdge
  have hnonadjacent : rightPlacement.rungType ≠ HexRungType.adjacent :=
    InternalHexRungPlacement.rungType_ne_adjacent_of_cell3 corridor hunique
      (nextCorridorInterior leftInterior hnext) rightPlacement
  rcases exists_sourceLocalRailWalkPair_of_incoming rightPlacement rightBefore
      rightAfter hrightBefore hrightAfter hnonadjacent with
    ⟨rightOutgoingBefore, rightOutgoingAfter, houtgoingBefore,
      houtgoingAfter, _rails⟩
  rcases sourceLocalRailShape_of_nonadjacent rightPlacement rightBefore
      rightAfter rightOutgoingBefore rightOutgoingAfter hrightBefore hrightAfter
      houtgoingBefore houtgoingAfter hnonadjacent with ⟨shape⟩
  exact ⟨{
    rightBefore := rightBefore
    rightAfter := rightAfter
    rightOutgoingBefore := rightOutgoingBefore
    rightOutgoingAfter := rightOutgoingAfter
    beforeEdge_eq := hbeforeEdge
    beforeFace_eq := hbeforeFace
    afterEdge_eq := hafterEdge
    afterFace_eq := hafterFace
    outgoingBefore_mod := houtgoingBefore
    outgoingAfter_mod := houtgoingAfter
    shape := shape
  }⟩

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
