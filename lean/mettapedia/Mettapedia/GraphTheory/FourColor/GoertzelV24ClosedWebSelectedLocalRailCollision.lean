import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailShapeEdgeOrigin

/-!
# Exact local collision alternative for selected Cell-3 rails

The selected `0+2`, `1+1`, and `2+0` connectors are constructed without the
closed-map global face-intersection uniqueness premise.  Consequently their
two local rails must not be declared disjoint by fiat.  This module performs
the finite source-local check: the canonical rails are support-disjoint, or
two distinct literal side slots name the same face and hence produce the
existing `SelectedLocalLayerCollision` certificate.

This is the same-cell part of L1.  It does not settle either neighbouring-cell
gap, perform an arbitrary-length append, or attach the hole end caps.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

/-- A selected local rail pair together with the same-cell separation needed
by the later append invariant. -/
structure SeparatedSelectedSourceLocalRailPaths
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ selectedPlacementSidePositions placement}) where
  paths : SelectedSourceLocalRailPaths placement incomingBefore incomingAfter
    outgoingBefore outgoingAfter
  firstRail_support_disjoint_secondRail :
    paths.firstRail.support.Disjoint paths.secondRail.support
  firstRail_edge_has_forward_origin : ∀ edge ∈ paths.firstRail.edges,
    SelectedPlacementForwardEdgeOrigin placement edge
  secondRail_edge_has_forward_origin : ∀ edge ∈ paths.secondRail.edges,
    SelectedPlacementForwardEdgeOrigin placement edge

private def repeatCollisionOfFaceEq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left right : {position // position ∈ selectedPlacementSidePositions placement})
    (hne : left.1.val ≠ right.1.val)
    (hfaces : selectedPlacementSideFace placement left =
      selectedPlacementSideFace placement right) :
    SelectedLocalLayerCollision hnext placement :=
  .repeatsSide left right (by
    intro heq
    exact hne (congrArg Fin.val heq)) hfaces

private theorem walk_mem_support_eq_start_or_end_of_length_le_one
    {Vertex : Type*} {graph : SimpleGraph Vertex} {start finish face : Vertex}
    (walk : graph.Walk start finish) (hlength : walk.length ≤ 1)
    (hface : face ∈ walk.support) : face = start ∨ face = finish := by
  cases walk with
  | nil => simpa using hface
  | cons hadj tail =>
      cases tail with
      | nil => simpa using hface
      | cons hnext rest =>
          simp only [SimpleGraph.Walk.length_cons] at hlength
          omega

/-- **L1 selected same-cell rail alternative.** For one classified literal
Cell-3 connector, either its two canonical selected rails have disjoint face
support, or the exact repeated-side collision is returned. -/
theorem separatedSelectedSourceLocalRailPaths_or_collision_of_shape
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
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
      placement.outgoingPosition.val + 1 [MOD 6])
    (shape : SelectedSourceLocalRailShape placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) :
    Nonempty (SeparatedSelectedSourceLocalRailPaths placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) ∨
      SelectedLocalLayerCollision hnext placement := by
  cases shape with
  | forwardTwo first_eq middle houtMiddle hmiddleIn =>
      have hvalues :
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
      rcases hvalues with ⟨hneIn, hneMiddle, hneOut⟩
      by_cases hIn : selectedPlacementSideFace placement incomingBefore =
          selectedPlacementSideFace placement incomingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement incomingBefore
          incomingAfter hneIn hIn)
      by_cases hMiddle : selectedPlacementSideFace placement incomingBefore =
          selectedPlacementSideFace placement middle
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement incomingBefore
          middle hneMiddle hMiddle)
      by_cases hOut : selectedPlacementSideFace placement incomingBefore =
          selectedPlacementSideFace placement outgoingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement incomingBefore
          outgoingAfter hneOut hOut)
      left
      let paths := selectedSourceLocalRailPathsOfShape placement incomingBefore
        incomingAfter outgoingBefore outgoingAfter
        (.forwardTwo first_eq middle houtMiddle hmiddleIn)
      refine ⟨{
        paths := paths
        firstRail_support_disjoint_secondRail := ?_
        firstRail_edge_has_forward_origin := by
          intro edge hedge
          exact selectedSourceLocalRailPathsOfShape_edge_has_forward_origin
            placement incomingBefore incomingAfter outgoingBefore outgoingAfter
              (.forwardTwo first_eq middle houtMiddle hmiddleIn) edge
              (Or.inl hedge)
        secondRail_edge_has_forward_origin := by
          intro edge hedge
          exact selectedSourceLocalRailPathsOfShape_edge_has_forward_origin
            placement incomingBefore incomingAfter outgoingBefore outgoingAfter
              (.forwardTwo first_eq middle houtMiddle hmiddleIn) edge
              (Or.inr hedge)
      }⟩
      rw [List.disjoint_left]
      intro face hfirst hsecond
      let houtWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement outgoingAfter middle houtMiddle
      let outMiddle := Classical.choose houtWitness
      let hinWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement middle incomingAfter hmiddleIn
      let middleIn := Classical.choose hinWitness
      let rawFirst :
          (interiorDualGraph (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
              (selectedPlacementSideFace placement incomingBefore)
              (selectedPlacementSideFace placement outgoingBefore) :=
        SimpleGraph.Walk.nil.copy rfl
          (congrArg (selectedPlacementSideFace placement) first_eq)
      let rawSecond := middleIn.reverse.append outMiddle.reverse
      have hfirstRaw : face ∈ rawFirst.support := by
        exact rawFirst.support_bypass_subset_support (by
          simpa [paths, selectedSourceLocalRailPathsOfShape, rawFirst,
            rawSecond, houtWitness, outMiddle, hinWitness, middleIn] using hfirst)
      have hsecondRaw : face ∈ rawSecond.support := by
        exact rawSecond.support_bypass_subset_support (by
          simpa [paths, selectedSourceLocalRailPathsOfShape, rawFirst,
            rawSecond, houtWitness, outMiddle, hinWitness, middleIn] using hsecond)
      simp only [rawFirst, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_nil, List.mem_singleton] at hfirstRaw
      subst face
      have hparts : selectedPlacementSideFace placement incomingBefore ∈
          middleIn.reverse.support ∨
          selectedPlacementSideFace placement incomingBefore ∈
            outMiddle.reverse.support :=
        (SimpleGraph.Walk.mem_support_append_iff _ _).1 (by
          simpa [rawSecond] using hsecondRaw)
      rcases hparts with hpart | hpart
      · have hpart' : selectedPlacementSideFace placement incomingBefore ∈
            middleIn.support := by
          simpa [SimpleGraph.Walk.support_reverse] using hpart
        have hlength : middleIn.length ≤ 1 := by
          simpa [middleIn] using (Classical.choose_spec hinWitness).2
        rcases walk_mem_support_eq_start_or_end_of_length_le_one
            middleIn hlength hpart' with heq | heq
        · exact hMiddle heq
        · exact hIn heq
      · have hpart' : selectedPlacementSideFace placement incomingBefore ∈
            outMiddle.support := by
          simpa [SimpleGraph.Walk.support_reverse] using hpart
        have hlength : outMiddle.length ≤ 1 := by
          simpa [outMiddle] using (Classical.choose_spec houtWitness).2
        rcases walk_mem_support_eq_start_or_end_of_length_le_one
            outMiddle hlength hpart' with heq | heq
        · exact hOut heq
        · exact hMiddle heq
  | forwardThree hfirst hsecond =>
      have hvalues :
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
      rcases hvalues with ⟨hneII, hneIO, hneOI, hneOO⟩
      by_cases hII : selectedPlacementSideFace placement incomingBefore =
          selectedPlacementSideFace placement incomingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement incomingBefore
          incomingAfter hneII hII)
      by_cases hIO : selectedPlacementSideFace placement incomingBefore =
          selectedPlacementSideFace placement outgoingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement incomingBefore
          outgoingAfter hneIO hIO)
      by_cases hOI : selectedPlacementSideFace placement outgoingBefore =
          selectedPlacementSideFace placement incomingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement outgoingBefore
          incomingAfter hneOI hOI)
      by_cases hOO : selectedPlacementSideFace placement outgoingBefore =
          selectedPlacementSideFace placement outgoingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement outgoingBefore
          outgoingAfter hneOO hOO)
      left
      let paths := selectedSourceLocalRailPathsOfShape placement incomingBefore
        incomingAfter outgoingBefore outgoingAfter (.forwardThree hfirst hsecond)
      refine ⟨{
        paths := paths
        firstRail_support_disjoint_secondRail := ?_
        firstRail_edge_has_forward_origin := by
          intro edge hedge
          exact selectedSourceLocalRailPathsOfShape_edge_has_forward_origin
            placement incomingBefore incomingAfter outgoingBefore outgoingAfter
              (.forwardThree hfirst hsecond) edge (Or.inl hedge)
        secondRail_edge_has_forward_origin := by
          intro edge hedge
          exact selectedSourceLocalRailPathsOfShape_edge_has_forward_origin
            placement incomingBefore incomingAfter outgoingBefore outgoingAfter
              (.forwardThree hfirst hsecond) edge (Or.inr hedge)
      }⟩
      rw [List.disjoint_left]
      intro face hfirstMem hsecondMem
      let hfirstWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement incomingBefore outgoingBefore hfirst
      let firstStep := Classical.choose hfirstWitness
      let hsecondWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement outgoingAfter incomingAfter hsecond
      let secondStep := Classical.choose hsecondWitness
      let rawFirst := firstStep
      let rawSecond := secondStep.reverse
      have hfirstRaw : face ∈ rawFirst.support := by
        exact rawFirst.support_bypass_subset_support (by
          simpa [paths, selectedSourceLocalRailPathsOfShape, rawFirst,
            rawSecond, hfirstWitness, firstStep, hsecondWitness, secondStep]
            using hfirstMem)
      have hsecondRaw : face ∈ rawSecond.support := by
        exact rawSecond.support_bypass_subset_support (by
          simpa [paths, selectedSourceLocalRailPathsOfShape, rawFirst,
            rawSecond, hfirstWitness, firstStep, hsecondWitness, secondStep]
            using hsecondMem)
      have hfirstLength : firstStep.length ≤ 1 := by
        simpa [firstStep] using (Classical.choose_spec hfirstWitness).2
      have hsecondLength : secondStep.length ≤ 1 := by
        simpa [secondStep] using (Classical.choose_spec hsecondWitness).2
      rcases walk_mem_support_eq_start_or_end_of_length_le_one
          firstStep hfirstLength hfirstRaw with rfl | rfl
      · have hsecondRaw' : selectedPlacementSideFace placement incomingBefore ∈
            secondStep.support := by
          simpa [rawSecond, SimpleGraph.Walk.support_reverse] using hsecondRaw
        rcases walk_mem_support_eq_start_or_end_of_length_le_one
            secondStep hsecondLength hsecondRaw' with heq | heq
        · exact hIO heq
        · exact hII heq
      · have hsecondRaw' : selectedPlacementSideFace placement outgoingBefore ∈
            secondStep.support := by
          simpa [rawSecond, SimpleGraph.Walk.support_reverse] using hsecondRaw
        rcases walk_mem_support_eq_start_or_end_of_length_le_one
            secondStep hsecondLength hsecondRaw' with heq | heq
        · exact hOO heq
        · exact hOI heq
  | forwardFour middle hinMiddle hmiddleOut second_eq =>
      have hvalues :
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
      rcases hvalues with ⟨hneIn, hneMiddle, hneOut⟩
      by_cases hIn : selectedPlacementSideFace placement incomingBefore =
          selectedPlacementSideFace placement incomingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement incomingBefore
          incomingAfter hneIn hIn)
      by_cases hMiddle : selectedPlacementSideFace placement middle =
          selectedPlacementSideFace placement incomingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement middle
          incomingAfter hneMiddle hMiddle)
      by_cases hOut : selectedPlacementSideFace placement outgoingBefore =
          selectedPlacementSideFace placement incomingAfter
      · exact Or.inr (repeatCollisionOfFaceEq hnext placement outgoingBefore
          incomingAfter hneOut hOut)
      left
      let paths := selectedSourceLocalRailPathsOfShape placement incomingBefore
        incomingAfter outgoingBefore outgoingAfter
        (.forwardFour middle hinMiddle hmiddleOut second_eq)
      refine ⟨{
        paths := paths
        firstRail_support_disjoint_secondRail := ?_
        firstRail_edge_has_forward_origin := by
          intro edge hedge
          exact selectedSourceLocalRailPathsOfShape_edge_has_forward_origin
            placement incomingBefore incomingAfter outgoingBefore outgoingAfter
              (.forwardFour middle hinMiddle hmiddleOut second_eq) edge
              (Or.inl hedge)
        secondRail_edge_has_forward_origin := by
          intro edge hedge
          exact selectedSourceLocalRailPathsOfShape_edge_has_forward_origin
            placement incomingBefore incomingAfter outgoingBefore outgoingAfter
              (.forwardFour middle hinMiddle hmiddleOut second_eq) edge
              (Or.inr hedge)
      }⟩
      rw [List.disjoint_left]
      intro face hfirst hsecond
      let hinWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement incomingBefore middle hinMiddle
      let inMiddle := Classical.choose hinWitness
      let houtWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement middle outgoingBefore hmiddleOut
      let middleOut := Classical.choose houtWitness
      let rawFirst := inMiddle.append middleOut
      let rawSecond :
          (interiorDualGraph (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
              (selectedPlacementSideFace placement incomingAfter)
              (selectedPlacementSideFace placement outgoingAfter) :=
        SimpleGraph.Walk.nil.copy rfl
          (congrArg (selectedPlacementSideFace placement) second_eq)
      have hfirstRaw : face ∈ rawFirst.support := by
        exact rawFirst.support_bypass_subset_support (by
          simpa [paths, selectedSourceLocalRailPathsOfShape, rawFirst,
            rawSecond, hinWitness, inMiddle, houtWitness, middleOut] using hfirst)
      have hsecondRaw : face ∈ rawSecond.support := by
        exact rawSecond.support_bypass_subset_support (by
          simpa [paths, selectedSourceLocalRailPathsOfShape, rawFirst,
            rawSecond, hinWitness, inMiddle, houtWitness, middleOut] using hsecond)
      simp only [rawSecond, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_nil, List.mem_singleton] at hsecondRaw
      subst face
      have hparts : selectedPlacementSideFace placement incomingAfter ∈
          inMiddle.support ∨
          selectedPlacementSideFace placement incomingAfter ∈ middleOut.support :=
        (SimpleGraph.Walk.mem_support_append_iff _ _).1 (by
          simpa [rawFirst] using hfirstRaw)
      rcases hparts with hpart | hpart
      · have hlength : inMiddle.length ≤ 1 := by
          simpa [inMiddle] using (Classical.choose_spec hinWitness).2
        rcases walk_mem_support_eq_start_or_end_of_length_le_one
            inMiddle hlength hpart with heq | heq
        · exact hIn heq.symm
        · exact hMiddle heq.symm
      · have hlength : middleOut.length ≤ 1 := by
          simpa [middleOut] using (Classical.choose_spec houtWitness).2
        rcases walk_mem_support_eq_start_or_end_of_length_le_one
            middleOut hlength hpart with heq | heq
        · exact hMiddle heq.symm
        · exact hOut heq.symm

/-- Every literal selected Cell-3 connector has either a separated local rail
pair or the exact finite collision certificate. -/
theorem exists_separatedSelectedSourceLocalRailPaths_or_collision_of_cell3
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
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
    Nonempty (SeparatedSelectedSourceLocalRailPaths placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter) ∨
      SelectedLocalLayerCollision hnext placement := by
  rcases selectedSourceLocalRailShape_of_cell3 placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter hincomingBefore hincomingAfter
      houtgoingBefore houtgoingAfter with ⟨shape⟩
  exact separatedSelectedSourceLocalRailPaths_or_collision_of_shape hnext
    placement incomingBefore incomingAfter outgoingBefore outgoingAfter
    hincomingBefore hincomingAfter houtgoingBefore houtgoingAfter shape

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
