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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

/-- **L9 (local rail adjacency).** Consecutive surviving slots of one
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

/-- **L9 (finite local rail shape).** The four literal flank slots around a
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

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
