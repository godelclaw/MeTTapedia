import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFinitePredecessorDisjoint
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellInternal
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact

/-!
# Exact cap-six data on the selected rolling successor face interface

The selected finite contraction already computes the exact successor
connectivity and incidence rows.  This file supplies the remaining geometric
fact for its capped face-progress row: each live target component lies on one
annular-interior face, where primal-edge labels are injective on dart
occurrences.  The generic weighted-contraction theorem can then recover the
literal target-component support without overcounting.

Only the corrected interior-face uniqueness hypothesis is used.  No global
uniqueness assertion involving either annular hole is reintroduced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebPointwiseSelectedFaceFinitePredecessorDisjoint
open GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCode
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetIncidence
open GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorPointwiseRungs
open GoertzelV24HexCorridorSkeleton
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open GoertzelV24InterfaceExteriorLabelCapFactorForgetExact
open GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellInternal
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceTargetCapExactEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance pointwiseSelectedFaceTargetCapExactIncidenceLinearOrder
    {n : Nat} : LinearOrder (Fin n × Bool) :=
  LinearOrder.lift' (fun incidence : Fin n × Bool ↦ toLex incidence)
    toLex.injective

local instance pointwiseSelectedFaceTargetCapExactOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-! ## Interior-face locality -/

/-- At a cyclic three-dart vertex, the next face step changes the underlying
edge. -/
private theorem edgeOf_phi_ne_edgeOf_of_dartsAt_card_eq_three
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    (dart : RS.D)
    (hcard : (RS.dartsAt (RS.vertOf (RS.alpha dart))).card = 3) :
    RS.edgeOf (RS.phi dart) ≠ RS.edgeOf dart := by
  have halphaMem : RS.alpha dart ∈
      RS.dartsAt (RS.vertOf (RS.alpha dart)) := by
    simp [RotationSystem.dartsAt]
  have hnontrivialFinset :
      (RS.dartsAt (RS.vertOf (RS.alpha dart))).Nontrivial := by
    apply Finset.one_lt_card_iff_nontrivial.mp
    rw [hcard]
    omega
  have hnontrivial :
      (RS.dartsAt (RS.vertOf (RS.alpha dart)) : Set RS.D).Nontrivial := by
    simpa only [Finset.coe_sort_coe] using hnontrivialFinset
  have hrho : RS.rho (RS.alpha dart) ≠ RS.alpha dart :=
    (rho_isCycleOn_dartsAt RS hrotation
      (RS.vertOf (RS.alpha dart))).apply_ne hnontrivial halphaMem
  intro hedge
  rcases RS.edge_fiber_two_cases (d := dart) (y := RS.phi dart) rfl
      hedge with hsame | hopposite
  · apply RS.no_self_loops dart
    exact (congrArg RS.vertOf hsame).symm.trans
      (RS.vert_phi_eq_vert_alpha dart)
  · exact hrho (by simpa [RotationSystem.phi_apply] using hopposite)

/-- Every face incident to a selected outgoing crossing of a literal Cell is
annular-interior. -/
theorem pointwiseSelectedSourceLocalLayerRightCrossingAt_incidentFace_internal
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2)
    (face : OrbitFace formation.annular.RS)
    (hface : pointwiseSelectedSourceLocalLayerRightCrossingAt formation
        corridor hinterior offset step ∈
      orbitFaceBoundary formation.annular.RS face) :
    face ∈ formation.annular.cellulation.interiorFaces := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let crossingStep : Fin pair.right.crosscut.walk.length :=
    ⟨step.val, by
      simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
        Formation.LocalLayerPair.secondLayer,
        Formation.LocalLayerPair.secondWalk] using step.isLt⟩
  have hedgeCrossing : pair.right.crossingEdge crossingStep =
      pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset step := by
    simp [pointwiseSelectedSourceLocalLayerRightCrossingAt, layers, pair,
      crossingStep, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer,
      Formation.LocalLayerPair.secondWalk]
  let leftFace := pair.right.crosscut.walk.getVert crossingStep.val
  let rightFace := pair.right.crosscut.walk.getVert (crossingStep.val + 1)
  have hleftFace : pointwiseSelectedSourceLocalLayerRightCrossingAt formation
      corridor hinterior offset step ∈
        orbitFaceBoundary formation.annular.RS leftFace.1 := by
    rw [← hedgeCrossing]
    exact pair.right.crossingEdge_mem_leftFace crossingStep
  have hrightFace : pointwiseSelectedSourceLocalLayerRightCrossingAt formation
      corridor hinterior offset step ∈
        orbitFaceBoundary formation.annular.RS rightFace.1 := by
    rw [← hedgeCrossing]
    exact pair.right.crossingEdge_mem_rightFace crossingStep
  have hfacesNe : leftFace.1 ≠ rightFace.1 := by
    intro hfaces
    exact (pair.right.crosscut.walk.adj_getVert_succ crossingStep.isLt).ne
      (Subtype.ext hfaces)
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      (orbitFace_incidence_le_two formation.annular.RS) leftFace.2 rightFace.2
      (Finset.mem_univ face) hfacesNe hleftFace hrightFace hface
  have hwalk : pair.right.crosscut.walk = layers.secondWalk := by
    rfl
  have hleftInterior : leftFace.1 ∈
      formation.annular.cellulation.interiorFaces := by
    have hindex : crossingStep.val < layers.secondWalk.length + 1 := by
      have hlt : crossingStep.val < layers.secondWalk.length := by
        simpa [hwalk] using crossingStep.isLt
      omega
    have hinteriorLeft := layers.secondWalk_getVert_internal
      ⟨crossingStep.val, hindex⟩
    simpa [leftFace, pair,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer] using hinteriorLeft
  have hrightInterior : rightFace.1 ∈
      formation.annular.cellulation.interiorFaces := by
    have hindex : crossingStep.val + 1 < layers.secondWalk.length + 1 := by
      have hlt : crossingStep.val < layers.secondWalk.length := by
        simpa [hwalk] using crossingStep.isLt
      omega
    have hinteriorRight := layers.secondWalk_getVert_internal
      ⟨crossingStep.val + 1, hindex⟩
    simpa [rightFace, pair,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer] using hinteriorRight
  rcases hcases with hleft | hright
  · rw [hleft]
    exact hleftInterior
  · rw [hright]
    exact hrightInterior

/-- Every face incident to a selected incoming crossing of a literal Cell is
annular-interior. -/
theorem pointwiseSelectedSourceLocalLayerLeftCrossingAt_incidentFace_internal
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2)
    (face : OrbitFace formation.annular.RS)
    (hface : pointwiseSelectedSourceLocalLayerLeftCrossingAt formation
        corridor hinterior offset step ∈
      orbitFaceBoundary formation.annular.RS face) :
    face ∈ formation.annular.cellulation.interiorFaces := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let crossingStep : Fin pair.left.crosscut.walk.length :=
    ⟨step.val, by
      simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
        Formation.LocalLayerPair.firstLayer,
        Formation.LocalLayerPair.firstWalk] using step.isLt⟩
  have hedgeCrossing : pair.left.crossingEdge crossingStep =
      pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step := by
    simp [pointwiseSelectedSourceLocalLayerLeftCrossingAt, layers, pair,
      crossingStep, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.firstWalk]
  let leftFace := pair.left.crosscut.walk.getVert crossingStep.val
  let rightFace := pair.left.crosscut.walk.getVert (crossingStep.val + 1)
  have hleftFace : pointwiseSelectedSourceLocalLayerLeftCrossingAt formation
      corridor hinterior offset step ∈
        orbitFaceBoundary formation.annular.RS leftFace.1 := by
    rw [← hedgeCrossing]
    exact pair.left.crossingEdge_mem_leftFace crossingStep
  have hrightFace : pointwiseSelectedSourceLocalLayerLeftCrossingAt formation
      corridor hinterior offset step ∈
        orbitFaceBoundary formation.annular.RS rightFace.1 := by
    rw [← hedgeCrossing]
    exact pair.left.crossingEdge_mem_rightFace crossingStep
  have hfacesNe : leftFace.1 ≠ rightFace.1 := by
    intro hfaces
    exact (pair.left.crosscut.walk.adj_getVert_succ crossingStep.isLt).ne
      (Subtype.ext hfaces)
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      (orbitFace_incidence_le_two formation.annular.RS) leftFace.2 rightFace.2
      (Finset.mem_univ face) hfacesNe hleftFace hrightFace hface
  have hwalk : pair.left.crosscut.walk = layers.firstWalk := by
    rfl
  have hleftInterior : leftFace.1 ∈
      formation.annular.cellulation.interiorFaces := by
    have hindex : crossingStep.val < layers.firstWalk.length + 1 := by
      have hlt : crossingStep.val < layers.firstWalk.length := by
        simpa [hwalk] using crossingStep.isLt
      omega
    have hinteriorLeft := layers.firstWalk_getVert_internal
      ⟨crossingStep.val, hindex⟩
    simpa [leftFace, pair,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer] using hinteriorLeft
  have hrightInterior : rightFace.1 ∈
      formation.annular.cellulation.interiorFaces := by
    have hindex : crossingStep.val + 1 < layers.firstWalk.length + 1 := by
      have hlt : crossingStep.val < layers.firstWalk.length := by
        simpa [hwalk] using crossingStep.isLt
      omega
    have hinteriorRight := layers.firstWalk_getVert_internal
      ⟨crossingStep.val + 1, hindex⟩
    simpa [rightFace, pair,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer] using hinteriorRight
  rcases hcases with hleft | hright
  · rw [hleft]
    exact hleftInterior
  · rw [hright]
    exact hrightInterior

/-- Every face incident to an edge of the selected literal two-vertex Cell is
annular-interior.  A non-crossing Cell edge turns at either cubic endpoint
onto a crossing edge of the same Cell. -/
theorem pointwiseSelectedSourceLocalLayerCellRegionAt_incidentFace_internal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (dart : web.annular.RS.D)
    (hedge : web.annular.RS.edgeOf dart ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset) :
    dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt web.toFormation
    corridor hinterior offset
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt web.toFormation
    corridor hinterior offset
  let side := pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
    corridor hinterior offset
  have hfaceEdge : web.annular.RS.edgeOf dart ∈
      orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS dart) :=
    edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS dart
  by_cases hcrossing : web.annular.RS.edgeOf dart ∈
      vertexSetCrossingEdges web.annular.RS side
  · rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
        web.toFormation corridor hinterior offset
        (by simpa [side] using hcrossing) with
      ⟨step, hleft⟩ | ⟨step, hright⟩
    · apply pointwiseSelectedSourceLocalLayerLeftCrossingAt_incidentFace_internal
        web.toFormation corridor hinterior offset step
          (dartOrbitFace web.annular.RS dart)
      rw [← hleft]
      exact hfaceEdge
    · apply pointwiseSelectedSourceLocalLayerRightCrossingAt_incidentFace_internal
        web.toFormation corridor hinterior offset step
          (dartOrbitFace web.annular.RS dart)
      rw [← hright]
      exact hfaceEdge
  · have hendpoints :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side
        graphData minimal caps coloring web corridor hinterior offset hedge
          (by simpa [side] using hcrossing)
    have halphaEndpoint : web.annular.RS.vertOf
        (web.annular.RS.alpha dart) ∈ side := by
      change web.annular.RS.vertOf (web.annular.RS.alpha dart) ∈
        pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
          corridor hinterior offset
      rw [← hendpoints, RotationSystem.mem_endpoints_iff]
      exact ⟨web.annular.RS.alpha dart,
        web.annular.RS.mem_dartsOn.2 (web.annular.RS.edge_alpha dart), rfl⟩
    have hdegree :=
      layers.pointwiseSelectedLocalLayerCellVertexSide_degree_eq_three
        hinterior boundary
        (web.annular.RS.vertOf (web.annular.RS.alpha dart))
        (by simpa [side, pointwiseSelectedSourceLocalLayerCellVertexSideAt,
          layers, boundary] using halphaEndpoint)
    have hcard : (web.annular.RS.dartsAt
        (web.annular.RS.vertOf (web.annular.RS.alpha dart))).card = 3 := by
      change ({candidate :
          caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Dart |
        candidate.fst = (web.annular.RS.alpha dart).fst} : Finset _).card = 3
      rw [SimpleGraph.dart_fst_fiber_card_eq_degree]
      convert hdegree using 1
      apply GoertzelV24CubicSmallBoundaryCycle.degree_instance_independent
    have hneighborNe : web.annular.RS.edgeOf (web.annular.RS.phi dart) ≠
        web.annular.RS.edgeOf dart :=
      edgeOf_phi_ne_edgeOf_of_dartsAt_card_eq_three web.annular.RS
        (Instance.InteriorFace.vertexRotationCyclic web) dart hcard
    have hregionEq :
        pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
            hinterior offset =
          vertexSetRegionEdges web.annular.RS side := by
      exact pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges
        web.toFormation corridor hinterior offset
    have hneighborRegion : web.annular.RS.edgeOf
        (web.annular.RS.phi dart) ∈
        pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset := by
      rw [hregionEq, mem_vertexSetRegionEdges_iff]
      refine ⟨web.annular.RS.vertOf (web.annular.RS.phi dart), ?_, ?_⟩
      · rw [RotationSystem.mem_endpoints_iff]
        exact ⟨web.annular.RS.phi dart,
          web.annular.RS.mem_dartsOn.2 rfl, rfl⟩
      · rw [web.annular.RS.vert_phi_eq_vert_alpha]
        exact halphaEndpoint
    have hneighborCrossing : web.annular.RS.edgeOf
        (web.annular.RS.phi dart) ∈
        vertexSetCrossingEdges web.annular.RS side := by
      by_contra hnotCrossing
      have heq :=
        pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_subsingleton
          graphData minimal caps coloring web corridor hinterior offset hedge
            (by simpa [side] using hcrossing) hneighborRegion
              (by simpa [side] using hnotCrossing)
      exact hneighborNe heq.symm
    have hneighborFace : web.annular.RS.edgeOf
        (web.annular.RS.phi dart) ∈ orbitFaceBoundary web.annular.RS
          (dartOrbitFace web.annular.RS dart) := by
      rw [← dartOrbitFace_phi_eq web.annular.RS dart]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
        (web.annular.RS.phi dart)
    rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
        web.toFormation corridor hinterior offset
          (by simpa [side] using hneighborCrossing) with
      ⟨step, hleft⟩ | ⟨step, hright⟩
    · apply pointwiseSelectedSourceLocalLayerLeftCrossingAt_incidentFace_internal
        web.toFormation corridor hinterior offset step
          (dartOrbitFace web.annular.RS dart)
      rw [← hleft]
      exact hneighborFace
    · apply pointwiseSelectedSourceLocalLayerRightCrossingAt_incidentFace_internal
        web.toFormation corridor hinterior offset step
          (dartOrbitFace web.annular.RS dart)
      rw [← hright]
      exact hneighborFace

/-- Every face incident to the pointwise-selected shared outgoing rung is
annular-interior.  Only the consecutive-pair uniqueness receipt used to select
that rung is needed. -/
theorem pointwiseSelectedSourceLocalLayerSharedRungAt_incidentFace_internal
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (face : OrbitFace formation.annular.RS)
    (hface : pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
        hinterior offset ∈ orbitFaceBoundary formation.annular.RS face) :
    face ∈ formation.annular.cellulation.interiorFaces := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let hlocal := boundaryCleanCorridor_consecutiveRungUnique formation.annular
    hinterior corridor
  let rung := (pointwiseSelectedSourceLocalLayerInteriorAt offset).outgoing
  let left := skeleton.faceAt rung.left
  let right := skeleton.faceAt rung.right
  have hleftRight : left.1 ≠ right.1 := by
    intro heq
    exact (skeleton.consecutive_adjacent rung.left rung.right rfl).ne
      (Subtype.ext heq)
  have hleft : pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
      hinterior offset ∈ orbitFaceBoundary formation.annular.RS left.1 := by
    simpa [pointwiseSelectedSourceLocalLayerSharedRungAt, skeleton, hlocal,
      rung, left] using pointwiseRungEdge_mem_left skeleton hlocal rung
  have hright : pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
      hinterior offset ∈ orbitFaceBoundary formation.annular.RS right.1 := by
    simpa [pointwiseSelectedSourceLocalLayerSharedRungAt, skeleton, hlocal,
      rung, right] using pointwiseRungEdge_mem_right skeleton hlocal rung
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      (orbitFace_incidence_le_two formation.annular.RS) left.2 right.2
      (Finset.mem_univ face) hleftRight hleft hright hface
  rcases hcases with rfl | rfl
  · exact corridor.face_internal rung.left
  · exact corridor.face_internal rung.right

/-- Every face incident to one of the four pointwise-selected rebase roles is
annular-interior. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_incidentFace_internal
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (edge : G.edgeSet) (face : OrbitFace formation.annular.RS)
    (hedge : edge ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
      formation corridor hinterior offset hnext)
    (hface : edge ∈ orbitFaceBoundary formation.annular.RS face) :
    face ∈ formation.annular.cellulation.interiorFaces := by
  rcases
      (mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff
        formation corridor hinterior offset hnext edge).1 hedge with
    ⟨role, rfl⟩
  rcases role with role | role
  · exact pointwiseSelectedSourceLocalLayerSharedRungAt_incidentFace_internal
      formation corridor hinterior offset face (by
        simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt] using hface)
  · rcases role with step | role
    · exact pointwiseSelectedSourceLocalLayerLeftCrossingAt_incidentFace_internal
        formation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          step face (by
            simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt]
              using hface)
    · exact pointwiseSelectedSourceLocalLayerSharedRungAt_incidentFace_internal
        formation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          face (by
            simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt]
              using hface)

/-- Every active dart of the selected rolling target carrier lies on an
annular-interior face. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetDartAt_face_internal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (slot : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card)
    (hactive : web.annular.RS.edgeOf
        (((carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
            web.toFormation corridor hinterior
              (sourceLocalLayerNextOffset offset hnext))).symm slot).1) ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)) :
    dartOrbitFace web.annular.RS
        (((carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
            web.toFormation corridor hinterior
              (sourceLocalLayerNextOffset offset hnext))).symm slot).1) ∈
      web.annular.cellulation.interiorFaces := by
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
    web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)
  let targetDart : web.annular.RS.D := ((carrierCoordinate target).symm slot).1
  let targetEdge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)} :=
    ⟨web.annular.RS.edgeOf targetDart,
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_edgeOf_mem_tracked
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) targetDart
          ((carrierCoordinate target).symm slot).2⟩
  rcases
      pointwiseSelectedSourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
        graphData minimal caps coloring web corridor hinterior offset hnext
          targetEdge (by simpa [targetEdge, targetDart, target] using hactive) with
    hswitch | hcell
  · apply
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_incidentFace_internal
        web.toFormation corridor hinterior offset hnext
          (web.annular.RS.edgeOf targetDart)
            (dartOrbitFace web.annular.RS targetDart) hswitch
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS targetDart
  · exact pointwiseSelectedSourceLocalLayerCellRegionAt_incidentFace_internal
      graphData minimal caps coloring web corridor hinterior offset targetDart
        hcell

/-- Primal-edge labels are injective on the literal target-exterior component
denoted by any live contraction atom. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_label_injective
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (atom : SourceLocalLayerSerialCellRebaseUniformFaceTargetEntry
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext).card)
    (hentry :
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
        graphData minimal caps coloring web corridor hinterior offset hnext
          incidence = some atom) :
    let graph :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
        web.toFormation corridor hinterior offset hnext
    let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    let uniformDartAt :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
        web.toFormation corridor hinterior offset hnext
    Set.InjOn web.annular.RS.edgeOf
      {vertex |
        (exteriorGraph graph targetDartAt).Reachable
          (exteriorLabelCapContractionAtomVertex uniformDartAt
            (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) atom)
          vertex} := by
  classical
  dsimp only
  let graph :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
      web.toFormation corridor hinterior offset hnext
  let region := pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
    web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
    web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
  let atomVertex := exteriorLabelCapContractionAtomVertex uniformDartAt
    (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) atom
  have hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence :=
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
      graphData minimal caps coloring web corridor hinterior offset hnext
        incidence).1 (by simp [hentry])
  have htargetInternal : dartOrbitFace web.annular.RS
        (targetDartAt incidence.1) ∈
      web.annular.cellulation.interiorFaces := by
    apply
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetDartAt_face_internal
        graphData minimal caps coloring web corridor hinterior offset hnext
          incidence.1
    exact hpresent.2.2.2.1
  have htargetRootFace : dartOrbitFace web.annular.RS
        (targetDartAt incidence.1) =
      dartOrbitFace web.annular.RS
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence) :=
    faceRegionalDartGraph_adj_dartOrbitFace_eq web.annular.RS region hpresent.2
  have hatomVertex : atomVertex =
      faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence := by
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
        graphData minimal caps coloring web corridor hinterior offset hnext
          incidence atom hentry
  have hatomInternal : dartOrbitFace web.annular.RS atomVertex ∈
      web.annular.cellulation.interiorFaces := by
    rw [hatomVertex, ← htargetRootFace]
    exact htargetInternal
  have hexteriorLe : exteriorGraph graph targetDartAt ≤ graph := by
    intro first second hadj
    exact hadj.1
  intro left hleft right hright hedge
  have hleftFace : dartOrbitFace web.annular.RS atomVertex =
      dartOrbitFace web.annular.RS left :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
      (hleft.mono hexteriorLe)
  have hrightFace : dartOrbitFace web.annular.RS atomVertex =
      dartOrbitFace web.annular.RS right :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
      (hright.mono hexteriorLe)
  have hinjective : Set.InjOn web.annular.RS.edgeOf
      (orbitFaceDarts web.annular.RS
        (dartOrbitFace web.annular.RS atomVertex)) := by
    apply Finset.card_image_iff.mp
    exact InteriorFace.boundary_card_eq_darts_card web atomVertex hatomInternal
  exact hinjective
    ((mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS atomVertex) left).2 hleftFace.symm)
    ((mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS atomVertex) right).2 hrightFace.symm)
    hedge

/-- The selected rolling target's executable cap-six field is exactly the cap
of the distinct primal-edge labels in the literal successor exterior
component. -/
@[simp] theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceCap_val
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card × Bool) :
    ((pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hinterior offset hnext
      ).incidenceCap incidence).val =
      let graph :=
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
          web.toFormation corridor hinterior offset hnext
      let target :=
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      min (exteriorIncidenceLabelSupport graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
        web.annular.RS.edgeOf incidence).card 6 := by
  classical
  dsimp only
  let graph :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
      web.toFormation corridor hinterior offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
    web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)
  let uniform :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
  let retain :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
      web.toFormation corridor hinterior offset hnext
  let entry :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
      graphData minimal caps coloring web corridor hinterior offset hnext
  let code :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      web.toFormation corridor hinterior offset hnext
  change ((partialContractedInterfaceExteriorLabelCapCode code retain Prod.fst
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt
      corridor hinterior offset hnext) entry).incidenceCap incidence).val =
        min (exteriorIncidenceLabelSupport graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
          web.annular.RS.edgeOf incidence).card 6
  cases hentry : entry incidence with
  | none =>
      have hnotPresent : ¬ ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
          incidence := by
        intro hpresent
        have hsome :=
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
            graphData minimal caps coloring web corridor hinterior offset hnext
              incidence).2 hpresent
        simp [entry, hentry] at hsome
      rw [partialContractedInterfaceExteriorLabelCapCode_incidenceCap_val]
      simp [hentry, exteriorIncidenceLabelSupport, hnotPresent]
  | some atom =>
      have hatomPresent :=
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomPresent
          graphData minimal caps coloring web corridor hinterior offset hnext
            incidence atom (by simpa [entry] using hentry)
      have hatomPresentCode :
          exteriorLabelCapContractionAtomPresent code retain atom = true := by
        simpa [code, retain] using hatomPresent
      have hsome : ∀ retained slot, retain retained = some slot →
          uniformDartAt slot = targetDartAt retained := by
        intro retained slot hretain
        exact
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
            web.toFormation corridor hinterior offset hnext retained slot hretain
      have hnone : ∀ retained, retain retained = none →
          targetDartAt retained ∉ graph.support := by
        intro retained hretain
        exact
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_none_not_mem_support
            graphData minimal caps coloring web corridor hinterior offset hnext
              retained hretain
      have hcodeExact : code = exactInterfaceExteriorLabelCapCode graph
          uniformDartAt
          (fun dart => web.annular.RS.edgeOf dart ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior
                (sourceLocalLayerNextOffset offset hnext))
          Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf 6 := by
        exact
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
            web.toFormation corridor hinterior offset hnext
      have hconnectivity : code.connectivity =
          exactInterfaceExteriorCode graph uniformDartAt := by
        rw [hcodeExact]
        rfl
      have hinterfacePresent : ∀ slot,
          uniformDartAt slot ∈ graph.support →
            code.interfacePresent slot = true := by
        intro slot hsupport
        exact
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_interfacePresent_of_mem_support
            corridor hinterior offset hnext slot hsupport
      have hincidencePresent : ∀ oldIncidence,
          code.incidencePresent oldIncidence = true ↔
            ExteriorIncidencePresent graph uniformDartAt Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
              oldIncidence := by
        intro oldIncidence
        rw [hcodeExact]
        exact exactInterfaceExteriorLabelCapCode_incidencePresent_iff graph
          uniformDartAt
          (fun dart => web.annular.RS.edgeOf dart ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior
                (sourceLocalLayerNextOffset offset hnext))
          Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf oldIncidence 6
      have hincidenceConnected : ∀ first second,
          code.incidenceConnected first second = true ↔
            ExteriorIncidencePresent graph uniformDartAt Prod.fst
                (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
                first ∧
              ExteriorIncidencePresent graph uniformDartAt Prod.fst
                (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
                second ∧
              (exteriorGraph graph uniformDartAt).Reachable
                (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt first)
                (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt
                  second) := by
        intro first second
        rw [hcodeExact]
        exact exactInterfaceExteriorLabelCapCode_incidenceConnected_iff graph
          uniformDartAt
          (fun dart => web.annular.RS.edgeOf dart ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior
                (sourceLocalLayerNextOffset offset hnext))
          Prod.fst (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf first second 6
      have hincidenceComplete : ∀ slot outside,
          OutsideInterface uniformDartAt outside →
            graph.Adj (uniformDartAt slot) outside →
              ∃ oldIncidence : Fin uniform.card × Bool,
                oldIncidence.1 = slot ∧
                  faceInterfaceIncidenceVertex web.annular.RS uniformDartAt
                    oldIncidence = outside := by
        intro slot outside houtside hadj
        exact
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessor_incidenceComplete
            corridor hinterior offset hnext slot outside houtside hadj
      have hincidenceCap : ∀ oldIncidence,
          (code.incidenceCap oldIncidence).val =
            min (exteriorIncidenceLabelSupport graph uniformDartAt Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
              web.annular.RS.edgeOf oldIncidence).card 6 := by
        intro oldIncidence
        rw [hcodeExact]
        exact exactInterfaceExteriorLabelCapCode_incidenceCap_val graph
          uniformDartAt
          (fun dart => web.annular.RS.edgeOf dart ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior
                (sourceLocalLayerNextOffset offset hnext))
          Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf oldIncidence 6
      have hlabelInjective : Set.InjOn web.annular.RS.edgeOf
          {vertex |
            (exteriorGraph graph targetDartAt).Reachable
              (exteriorLabelCapContractionAtomVertex uniformDartAt
                (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
                atom) vertex} := by
        exact
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_label_injective
            graphData minimal caps coloring web corridor hinterior offset hnext
              incidence atom (by simpa [entry] using hentry)
      have hcomponent :=
        exteriorLabelCapContractionComponentCap_val_eq_literalLabelSupport
          graph uniformDartAt targetDartAt retain hsome hnone Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf code hconnectivity hinterfacePresent
          hincidencePresent hincidenceConnected hincidenceComplete hincidenceCap
          atom hatomPresentCode
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective
            web.toFormation corridor hinterior offset hnext)
          hlabelInjective
      have hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
          incidence :=
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
          graphData minimal caps coloring web corridor hinterior offset hnext
            incidence).1 (by simp [entry, hentry])
      have hatomVertex :=
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
          graphData minimal caps coloring web corridor hinterior offset hnext
            incidence atom (by simpa [entry] using hentry)
      have hatomVertex' :
          exteriorLabelCapContractionAtomVertex uniformDartAt
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) atom =
            faceInterfaceIncidenceVertex web.annular.RS targetDartAt
              incidence := by
        simpa [uniformDartAt, targetDartAt, target] using hatomVertex
      have hsupport :
          exteriorLabelCapContractionLiteralLabelSupport graph targetDartAt
              uniformDartAt
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
              web.annular.RS.edgeOf atom =
            exteriorIncidenceLabelSupport graph targetDartAt Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
              web.annular.RS.edgeOf incidence := by
        ext value
        simp [exteriorLabelCapContractionLiteralLabelSupport,
          exteriorIncidenceLabelSupport, hpresent, hatomVertex']
      rw [partialContractedInterfaceExteriorLabelCapCode_incidenceCap_val]
      simp only [hentry, hatomPresentCode, if_true]
      exact hcomponent.trans (by rw [hsupport])

/-- The complete executable selected rolling target code is the canonical
exact facial-interface code of the literal successor graph. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_exact
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
        graphData minimal caps coloring web corridor hinterior offset hnext =
      exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))
        targetDartAt 6 := by
  classical
  dsimp only
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
    web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  apply BoundedInterfaceExteriorLabelCapCode.ext
  · rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_connectivity]
    simpa [target, targetDartAt,
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt] using
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt_exact
        graphData minimal caps coloring web corridor hinterior offset hnext)
  · funext slot
    apply Bool.eq_iff_iff.mpr
    rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_interfacePresent_iff]
    exact (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
      web.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)) targetDartAt slot 6).symm
  · funext incidence
    apply Bool.eq_iff_iff.mpr
    rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidencePresent_iff]
    exact (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
      web.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)) targetDartAt incidence 6).symm
  · funext first second
    apply Bool.eq_iff_iff.mpr
    rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceConnected_iff]
    unfold pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
    change
      (ExteriorIncidencePresent
            (faceRegionalDartGraph web.annular.RS
              (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext)))
            targetDartAt Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) first ∧
          ExteriorIncidencePresent
            (faceRegionalDartGraph web.annular.RS
              (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext)))
            targetDartAt Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) second ∧
          (exteriorGraph
            (faceRegionalDartGraph web.annular.RS
              (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext)))
            targetDartAt).Reachable
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt first)
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt second)) ↔
        (exactInterfaceExteriorLabelCapCode
          (faceRegionalDartGraph web.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior
                (sourceLocalLayerNextOffset offset hnext)))
          targetDartAt
          (fun dart => web.annular.RS.edgeOf dart ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior
                (sourceLocalLayerNextOffset offset hnext))
          Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
          web.annular.RS.edgeOf 6).incidenceConnected first second = true
    exact (exactInterfaceExteriorLabelCapCode_incidenceConnected_iff
      (faceRegionalDartGraph web.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext)))
      targetDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
      web.annular.RS.edgeOf first second 6).symm
  · funext incidence
    apply Fin.ext
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceCap_val
        graphData minimal caps coloring web corridor hinterior offset hnext
          incidence

end

end GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact

end Mettapedia.GraphTheory.FourColor
