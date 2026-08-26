import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceRetainedCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact

/-!
# Exact cap-six data on the rolling successor face interface

The finite contraction already computes the exact successor connectivity.
This file proves the remaining source-geometric fact needed for its capped
face-progress field: every active target component lies on one certified
simple annular-interior face.  The generic contraction theorem can therefore
sum the disjoint primal-edge label supports without overcounting.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapExact

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetIncidence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24FacialPentagonCap
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open GoertzelV24InterfaceExteriorLabelCapFactorForgetExact
open GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact
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

local instance uniformFaceTargetCapExactEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformFaceTargetCapExactIncidenceLinearOrder {n : Nat} :
    LinearOrder (Fin n × Bool) :=
  LinearOrder.lift' (fun incidence : Fin n × Bool ↦ toLex incidence)
    toLex.injective

local instance uniformFaceTargetCapExactOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

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

/-- Every face incident to an outgoing crossing of a literal Cell is an
annular-interior face. -/
theorem sourceLocalLayerRightCrossingAt_incidentFace_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2)
    (face : OrbitFace web.annular.RS)
    (hface : sourceLocalLayerRightCrossingAt corridor hunique offset step ∈
      orbitFaceBoundary web.annular.RS face) :
    face ∈ web.annular.cellulation.interiorFaces := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let crossingStep : Fin layers.secondLayer.walk.length :=
    ⟨step.val, by
      simpa [LocalLayerPair.secondLayer, LocalLayerPair.secondWalk] using
        step.isLt⟩
  have hedge : sourceLocalLayerRightCrossingAt corridor hunique offset step ∈
      layers.secondLayer.crossingEdges hunique := by
    apply (layers.secondLayer.mem_crossingEdges_iff hunique _).2
    refine ⟨crossingStep, ?_⟩
    simp [sourceLocalLayerRightCrossingAt, layers, crossingStep]
  have hsupport :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset (OrbitFace web.annular.RS))) ∈
        layers.secondWalk.support :=
    layers.secondLayer.face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      hunique hedge hface
  apply layers.localLayerLoop_support_internal
    ⟨face, Finset.mem_univ face⟩
  change (⟨face, Finset.mem_univ face⟩ : AmbientFace
    (Finset.univ : Finset (OrbitFace web.annular.RS))) ∈
      layers.localLayerLoop.support
  simp [LocalLayerPair.localLayerLoop, LocalLayerPair.firstWalk,
    LocalLayerPair.secondWalk] at hsupport ⊢
  aesop

/-- Every face incident to an edge of the literal two-vertex Cell is an
annular-interior face.  A non-crossing Cell edge turns at either cubic endpoint
onto a crossing edge of the same Cell, so the crossing geometry covers that
case as well. -/
theorem sourceLocalLayerCellRegionAt_incidentFace_internal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (dart : web.annular.RS.D)
    (hedge : web.annular.RS.edgeOf dart ∈
      sourceLocalLayerCellRegionAt corridor hunique offset) :
    dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces := by
  let side := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  have hfaceEdge : web.annular.RS.edgeOf dart ∈
      orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS dart) :=
    edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS dart
  by_cases hcrossing : web.annular.RS.edgeOf dart ∈
      vertexSetCrossingEdges web.annular.RS side
  · rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
        offset (by simpa [side] using hcrossing) with
      ⟨step, hleft⟩ | ⟨step, hright⟩
    · apply sourceLocalLayerLeftCrossingAt_incidentFace_internal corridor
        hunique offset step (dartOrbitFace web.annular.RS dart)
      rw [← hleft]
      exact hfaceEdge
    · apply sourceLocalLayerRightCrossingAt_incidentFace_internal corridor
        hunique offset step (dartOrbitFace web.annular.RS dart)
      rw [← hright]
      exact hfaceEdge
  · have hendpoints :=
      sourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side graphData
        minimal caps coloring web corridor hunique offset hedge
          (by simpa [side] using hcrossing)
    have halphaEndpoint : web.annular.RS.vertOf
        (web.annular.RS.alpha dart) ∈ side := by
      change web.annular.RS.vertOf (web.annular.RS.alpha dart) ∈
        sourceLocalLayerCellVertexSide corridor hunique
          (sourceLocalLayerInteriorAt offset)
          (sourceLocalLayerInteriorAt_hasNext offset)
      rw [← hendpoints, RotationSystem.mem_endpoints_iff]
      exact ⟨web.annular.RS.alpha dart,
        web.annular.RS.mem_dartsOn.2 (web.annular.RS.edge_alpha dart), rfl⟩
    have hdegree :=
      sourceLocalLayerCellVertexSide_degree_eq_three corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
        (web.annular.RS.vertOf (web.annular.RS.alpha dart))
        (by simpa [side] using halphaEndpoint)
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
    have hregionEq : sourceLocalLayerCellRegionAt corridor hunique offset =
        vertexSetRegionEdges web.annular.RS side := by
      have hside := sourceLocalLayerCellVertexSide_eq_retained_compl
        corridor hunique (sourceLocalLayerInteriorAt offset)
          (sourceLocalLayerInteriorAt_hasNext offset)
      exact congrArg (vertexSetRegionEdges web.annular.RS) hside.symm
    have hneighborRegion : web.annular.RS.edgeOf
        (web.annular.RS.phi dart) ∈
        sourceLocalLayerCellRegionAt corridor hunique offset := by
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
      have heq := sourceLocalLayerCellRegionAt_internalEdge_subsingleton
        graphData minimal caps coloring web corridor hunique offset hedge
          (by simpa [side] using hcrossing) hneighborRegion
            (by simpa [side] using hnotCrossing)
      exact hneighborNe heq.symm
    have hneighborFace : web.annular.RS.edgeOf
        (web.annular.RS.phi dart) ∈ orbitFaceBoundary web.annular.RS
          (dartOrbitFace web.annular.RS dart) := by
      rw [← dartOrbitFace_phi_eq web.annular.RS dart]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
        (web.annular.RS.phi dart)
    rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
        offset (by simpa [side] using hneighborCrossing) with
      ⟨step, hleft⟩ | ⟨step, hright⟩
    · apply sourceLocalLayerLeftCrossingAt_incidentFace_internal corridor
        hunique offset step (dartOrbitFace web.annular.RS dart)
      rw [← hleft]
      exact hneighborFace
    · apply sourceLocalLayerRightCrossingAt_incidentFace_internal corridor
        hunique offset step (dartOrbitFace web.annular.RS dart)
      rw [← hright]
      exact hneighborFace

/-- Every active dart of the rolling successor carrier lies on an
annular-interior face.  The finite target coordinate itself supplies tracked
carrier membership; activity then localizes its edge to the four-edge rebase
switch or to the current literal Cell. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetDartAt_face_internal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (slot : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card)
    (hactive : web.annular.RS.edgeOf
        (((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext))).symm slot).1) ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)) :
    dartOrbitFace web.annular.RS
        (((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext))).symm slot).1) ∈
      web.annular.cellulation.interiorFaces := by
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let targetDart : web.annular.RS.D := ((carrierCoordinate target).symm slot).1
  let targetEdge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)} :=
    ⟨web.annular.RS.edgeOf targetDart,
      sourceLocalLayerSerialFaceTransitionCarrierAt_edgeOf_mem_tracked graphData
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) targetDart
          ((carrierCoordinate target).symm slot).2⟩
  rcases
      sourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
        graphData minimal caps coloring web corridor hunique offset hnext
          targetEdge (by simpa [targetEdge, targetDart, target] using hactive) with
    hswitch | hcell
  · apply sourceLocalLayerBoundaryRebaseSwitchAt_incidentFace_internal corridor
      hunique offset hnext (web.annular.RS.edgeOf targetDart)
        (dartOrbitFace web.annular.RS targetDart) hswitch
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS targetDart
  · exact sourceLocalLayerCellRegionAt_incidentFace_internal graphData minimal
      caps coloring web corridor hunique offset targetDart hcell

/-- Primal-edge labels are injective on every literal target-exterior
component denoted by a live contraction atom.  The target incidence first
places the root on an active interior face; exterior reachability then stays
on that face, whose Cell-3 certificate gives a simple edge boundary. -/
theorem
    sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_label_injective
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (atom : SourceLocalLayerSerialCellRebaseUniformFaceTargetEntry
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card)
    (hentry :
      sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
        caps coloring web corridor hunique offset hnext incidence = some atom) :
    let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
      hunique offset hnext
    let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    let uniformDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
      corridor hunique offset hnext
    Set.InjOn web.annular.RS.edgeOf
      {vertex |
        (exteriorGraph graph targetDartAt).Reachable
          (exteriorLabelCapContractionAtomVertex uniformDartAt
            (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) atom)
          vertex} := by
  classical
  dsimp only
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let region := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    corridor hunique offset hnext
  let atomVertex := exteriorLabelCapContractionAtomVertex uniformDartAt
    (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) atom
  have hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence :=
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
      graphData minimal caps coloring web corridor hunique offset hnext
        incidence).1 (by simp [hentry])
  have htargetInternal : dartOrbitFace web.annular.RS
        (targetDartAt incidence.1) ∈
      web.annular.cellulation.interiorFaces := by
    apply
      sourceLocalLayerSerialCellRebaseUniformFaceTargetDartAt_face_internal
        graphData minimal caps coloring web corridor hunique offset hnext
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
      sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
        graphData minimal caps coloring web corridor hunique offset hnext
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

/-- The rolling target's executable cap-six field is exactly the cap of the
distinct primal-edge labels in the literal successor exterior component. -/
@[simp] theorem
    sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceCap_val
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool) :
    ((sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext
      ).incidenceCap incidence).val =
      let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
        hunique offset hnext
      let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
        hunique (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      min (exteriorIncidenceLabelSupport graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
        web.annular.RS.edgeOf incidence).card 6 := by
  classical
  dsimp only
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    corridor hunique offset hnext
  let retain := sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
    corridor hunique offset hnext
  let entry := sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
    graphData minimal caps coloring web corridor hunique offset hnext
  let code :=
    sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      corridor hunique offset hnext
  change ((partialContractedInterfaceExteriorLabelCapCode code retain Prod.fst
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt corridor hunique
      offset hnext) entry).incidenceCap incidence).val =
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
          (sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
            graphData minimal caps coloring web corridor hunique offset hnext
              incidence).2 hpresent
        simp [entry, hentry] at hsome
      rw [partialContractedInterfaceExteriorLabelCapCode_incidenceCap_val]
      simp [hentry, exteriorIncidenceLabelSupport, hnotPresent]
  | some atom =>
      have hatomPresent :=
        sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomPresent
          graphData minimal caps coloring web corridor hunique offset hnext
            incidence atom (by simpa [entry] using hentry)
      have hatomPresentCode :
          exteriorLabelCapContractionAtomPresent code retain atom = true := by
        simpa [code, retain] using hatomPresent
      have hsome : ∀ retained slot, retain retained = some slot →
          uniformDartAt slot = targetDartAt retained := by
        intro retained slot hretain
        exact
          sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
            corridor hunique offset hnext retained slot hretain
      have hnone : ∀ retained, retain retained = none →
          targetDartAt retained ∉ graph.support := by
        intro retained hretain
        exact
          sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_none_not_mem_support
            graphData minimal caps coloring web corridor hunique offset hnext
              retained hretain
      have hcodeExact : code = exactInterfaceExteriorLabelCapCode graph
          uniformDartAt
          (fun dart => web.annular.RS.edgeOf dart ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext))
          Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf 6 := by
        exact
          sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
            corridor hunique offset hnext
      have hconnectivity : code.connectivity =
          exactInterfaceExteriorCode graph uniformDartAt := by
        rw [hcodeExact]
        rfl
      have hinterfacePresent : ∀ slot,
          uniformDartAt slot ∈ graph.support →
            code.interfacePresent slot = true := by
        intro slot hsupport
        exact
          sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_interfacePresent_of_mem_support
            corridor hunique offset hnext slot hsupport
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
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
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
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext))
          Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
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
          sourceLocalLayerSerialCellRebaseUniformFaceSuccessor_incidenceComplete
            corridor hunique offset hnext slot outside houtside hadj
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
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
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
          sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_label_injective
            graphData minimal caps coloring web corridor hunique offset hnext
              incidence atom (by simpa [entry] using hentry)
      have hcomponent :=
        exteriorLabelCapContractionComponentCap_val_eq_literalLabelSupport
          graph uniformDartAt targetDartAt retain hsome hnone Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf code hconnectivity hinterfacePresent
          hincidencePresent hincidenceConnected hincidenceComplete hincidenceCap
          atom hatomPresentCode
          (sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor
            hunique offset hnext)
          hlabelInjective
      have hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
          incidence :=
        (sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
          graphData minimal caps coloring web corridor hunique offset hnext
            incidence).1 (by simp [entry, hentry])
      have hatomVertex :=
        sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
          graphData minimal caps coloring web corridor hunique offset hnext
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

/-- The complete executable rolling target code is the canonical exact
facial-interface code of the literal successor graph.  This is the packaged
one-step factorization theorem: all five finite fields agree, including the
cap-six face-progress field. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_exact
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
        graphData minimal caps coloring web corridor hunique offset hnext =
      exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        targetDartAt 6 := by
  classical
  dsimp only
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  apply BoundedInterfaceExteriorLabelCapCode.ext
  · rw [sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_connectivity]
    simpa [target, targetDartAt,
      sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt] using
      (sourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt_exact
        graphData minimal caps coloring web corridor hunique offset hnext)
  · funext slot
    apply Bool.eq_iff_iff.mpr
    rw [sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_interfacePresent_iff]
    exact (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
      web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)) targetDartAt slot 6).symm
  · funext incidence
    apply Bool.eq_iff_iff.mpr
    rw [sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidencePresent_iff]
    exact (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
      web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)) targetDartAt incidence 6).symm
  · funext first second
    apply Bool.eq_iff_iff.mpr
    rw [sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceConnected_iff]
    unfold sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
    change
      (ExteriorIncidencePresent
            (faceRegionalDartGraph web.annular.RS
              (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                (sourceLocalLayerNextOffset offset hnext)))
            targetDartAt Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) first ∧
          ExteriorIncidencePresent
            (faceRegionalDartGraph web.annular.RS
              (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                (sourceLocalLayerNextOffset offset hnext)))
            targetDartAt Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) second ∧
          (exteriorGraph
            (faceRegionalDartGraph web.annular.RS
              (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                (sourceLocalLayerNextOffset offset hnext)))
            targetDartAt).Reachable
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt first)
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt second)) ↔
        (exactInterfaceExteriorLabelCapCode
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext)))
          targetDartAt
          (fun dart => web.annular.RS.edgeOf dart ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext))
          Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
          web.annular.RS.edgeOf 6).incidenceConnected first second = true
    exact (exactInterfaceExteriorLabelCapCode_incidenceConnected_iff
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)))
      targetDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
      web.annular.RS.edgeOf first second 6).symm
  · funext incidence
    apply Fin.ext
    exact
      sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceCap_val
        graphData minimal caps coloring web corridor hunique offset hnext
          incidence

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapExact

end Mettapedia.GraphTheory.FourColor
