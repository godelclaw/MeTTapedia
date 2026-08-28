import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalFaceBoundaryAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellInternal

/-!
# Historical overlap locality for pointwise-selected Cells

This file proves the occurrence-sensitive locality statement needed to
contract the exact selected Cell--rebase interaction code to the next rolling
carrier.  A strict historical Cell edge which reaches the successor carrier
must be one of the four selected rebase roles.  Hence every active target
coordinate is either a switch edge or belongs to the current literal Cell.

Unlike the historical argument, all crossings are selected independently at
their own corridor offsets and only restricted interior-face uniqueness is
used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalFaceBoundaryAdjacency
open GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellInternal
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SelectedDualPathTransversal
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedCellPastOverlapOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-! ## Literal selected crossings on their corridor centre faces -/

theorem pointwiseSelectedSourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step ∈
      orbitFaceBoundary formation.annular.RS
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt
            (pointwiseSelectedSourceLocalLayerInteriorAt offset).center).1 := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let index : Fin pair.left.crosscut.walk.length := ⟨step.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.firstWalk] using step.isLt⟩
  have hstep : step.val = 0 ∨ step.val = 1 := by omega
  rcases hstep with hzero | hone
  · have hstepEq : step = ⟨0, by omega⟩ := Fin.ext hzero
    have hmem := pair.left.crossingEdge_mem_rightFace index
    simpa [pointwiseSelectedSourceLocalLayerLeftCrossingAt, layers, pair, index,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer, Formation.LocalLayerPair.firstWalk,
      hzero, hstepEq] using hmem
  · have hstepEq : step = ⟨1, by omega⟩ := Fin.ext hone
    have hmem := pair.left.crossingEdge_mem_leftFace index
    simpa [pointwiseSelectedSourceLocalLayerLeftCrossingAt, layers, pair, index,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer, Formation.LocalLayerPair.firstWalk,
      hone, hstepEq] using hmem

theorem pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset step ∈
      orbitFaceBoundary formation.annular.RS
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt
            (nextCorridorInterior
              (pointwiseSelectedSourceLocalLayerInteriorAt offset)
              (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext offset)).center).1 := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let index : Fin pair.right.crosscut.walk.length := ⟨step.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer,
      Formation.LocalLayerPair.secondWalk] using step.isLt⟩
  have hstep : step.val = 0 ∨ step.val = 1 := by omega
  rcases hstep with hzero | hone
  · have hstepEq : step = ⟨0, by omega⟩ := Fin.ext hzero
    have hmem := pair.right.crossingEdge_mem_rightFace index
    simpa [pointwiseSelectedSourceLocalLayerRightCrossingAt, layers, pair, index,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer, Formation.LocalLayerPair.secondWalk,
      hzero, hstepEq] using hmem
  · have hstepEq : step = ⟨1, by omega⟩ := Fin.ext hone
    have hmem := pair.right.crossingEdge_mem_leftFace index
    simpa [pointwiseSelectedSourceLocalLayerRightCrossingAt, layers, pair, index,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer, Formation.LocalLayerPair.secondWalk,
      hone, hstepEq] using hmem

/-! ## The internal bond and adjacent portals -/

/-- The unique internal bond is adjacent to every genuine selected Cell
crossing. -/
theorem pointwiseSelected_internalEdge_adj_crossingEdge
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
    {internal boundary :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hinternalRegion : internal ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset)
    (hinternalNotCrossing : internal ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior offset))
    (hboundaryCrossing : boundary ∈ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior offset)) :
    web.annular.RS.edgeAdjacencyGraph.Adj internal boundary := by
  let side := pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
    corridor hinterior offset
  have hendpoints :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side
      graphData minimal caps coloring web corridor hinterior offset
        hinternalRegion hinternalNotCrossing
  rw [mem_vertexSetCrossingEdges_iff] at hboundaryCrossing
  rcases hboundaryCrossing with
    ⟨vertex, hvertexBoundary, hvertexSide, outer, houterBoundary,
      houterOutside⟩
  apply (web.annular.RS.edgeAdjacencyGraph_adj_iff).2
  refine ⟨?_, vertex, ?_, hvertexBoundary⟩
  · intro heq
    subst boundary
    exact hinternalNotCrossing (by
      rw [mem_vertexSetCrossingEdges_iff]
      exact ⟨vertex, hvertexBoundary, hvertexSide, outer, houterBoundary,
        houterOutside⟩)
  · rw [hendpoints]
    exact hvertexSide

/-- An edge adjacent to the internal bond is a Cell crossing. -/
theorem pointwiseSelected_crossingEdge_of_internalEdge_adj
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
    {internal neighbor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hinternalRegion : internal ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset)
    (hinternalNotCrossing : internal ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior offset))
    (hadj : web.annular.RS.edgeAdjacencyGraph.Adj internal neighbor) :
    neighbor ∈ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior offset) := by
  let side := pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
    corridor hinterior offset
  have hendpoints :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side
      graphData minimal caps coloring web corridor hinterior offset
        hinternalRegion hinternalNotCrossing
  rcases (web.annular.RS.edgeAdjacencyGraph_adj_iff).1 hadj with
    ⟨hne, vertex, hvertexInternal, hvertexNeighbor⟩
  have hneighborRegion : neighbor ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset := by
    rw [pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges,
      mem_vertexSetRegionEdges_iff]
    refine ⟨vertex, hvertexNeighbor, ?_⟩
    rw [← hendpoints]
    exact hvertexInternal
  by_contra hneighborNotCrossing
  have heq :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_subsingleton
      graphData minimal caps coloring web corridor hinterior offset
        hinternalRegion hinternalNotCrossing hneighborRegion
          hneighborNotCrossing
  exact hne heq

/-! ## Strict historical overlap is impossible away from the rebase roles -/

/-- A crossing of a strict historical selected Cell can neither coincide with
nor touch an outgoing crossing of the successor selected Cell. -/
theorem pointwiseSelected_not_pastCellCrossing_eq_or_adj_nextRightCrossing
    (graphData : Data G)
    (_minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
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
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    {edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (holdCrossing : edge ∈ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior prior))
    (newStep : Fin 2)
    (hrel : edge = pointwiseSelectedSourceLocalLayerRightCrossingAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) newStep ∨
      web.annular.RS.edgeAdjacencyGraph.Adj edge
        (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext)
            newStep)) : False := by
  let target := sourceLocalLayerNextOffset offset hnext
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let newCenter :=
    (nextCorridorInterior
      (pointwiseSelectedSourceLocalLayerInteriorAt target)
      (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext target)).center
  have hnewFace :
      pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation corridor
          hinterior target newStep ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt newCenter).1 := by
    simpa [newCenter, skeleton, target] using
      pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary
        web.toFormation corridor hinterior target newStep
  rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
      web.toFormation corridor hinterior prior holdCrossing with
      ⟨oldStep, hedge⟩ | ⟨oldStep, hedge⟩
  · let oldCenter :=
      (pointwiseSelectedSourceLocalLayerInteriorAt prior).center
    have holdFace : edge ∈ orbitFaceBoundary web.annular.RS
        (skeleton.faceAt oldCenter).1 := by
      rw [hedge]
      simpa [oldCenter, skeleton] using
        pointwiseSelectedSourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary
          web.toFormation corridor hinterior prior oldStep
    have hcentersNe : oldCenter ≠ newCenter := by
      intro hsame
      have hvalues := congrArg Fin.val hsame
      change prior.val + 1 = target.val + 2 at hvalues
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal] at hvalues
      omega
    have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
        (skeleton.faceAt newCenter).1 := by
      intro hsame
      exact hcentersNe (skeleton.faceAt_injective (Subtype.ext hsame))
    have hfaceAdj :
        (interiorDualGraph (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
            ⟨(skeleton.faceAt oldCenter).1, Finset.mem_univ _⟩
            ⟨(skeleton.faceAt newCenter).1, Finset.mem_univ _⟩ := by
      rcases hrel with heq | hadj
      · apply
          interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
            (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            (orbitFace_incidence_le_two web.annular.RS) hfacesNe
              (by simpa [target, heq] using holdFace) hnewFace
      · exact interiorDualGraph_adj_of_edgeAdjacencyGraph_adj web hfacesNe
          holdFace hnewFace (by simpa [target] using hadj)
    have hseparated : oldCenter.val + 1 < newCenter.val := by
      change prior.val + 1 + 1 < target.val + 2
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal]
      omega
    exact (skeleton.separated_not_adjacent oldCenter newCenter hseparated)
      hfaceAdj
  · let oldCenter :=
      (nextCorridorInterior
        (pointwiseSelectedSourceLocalLayerInteriorAt prior)
        (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext prior)).center
    have holdFace : edge ∈ orbitFaceBoundary web.annular.RS
        (skeleton.faceAt oldCenter).1 := by
      rw [hedge]
      simpa [oldCenter, skeleton] using
        pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary
          web.toFormation corridor hinterior prior oldStep
    have hcentersNe : oldCenter ≠ newCenter := by
      intro hsame
      have hvalues := congrArg Fin.val hsame
      change prior.val + 2 = target.val + 2 at hvalues
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal] at hvalues
      omega
    have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
        (skeleton.faceAt newCenter).1 := by
      intro hsame
      exact hcentersNe (skeleton.faceAt_injective (Subtype.ext hsame))
    have hfaceAdj :
        (interiorDualGraph (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
            ⟨(skeleton.faceAt oldCenter).1, Finset.mem_univ _⟩
            ⟨(skeleton.faceAt newCenter).1, Finset.mem_univ _⟩ := by
      rcases hrel with heq | hadj
      · apply
          interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
            (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            (orbitFace_incidence_le_two web.annular.RS) hfacesNe
              (by simpa [target, heq] using holdFace) hnewFace
      · exact interiorDualGraph_adj_of_edgeAdjacencyGraph_adj web hfacesNe
          holdFace hnewFace (by simpa [target] using hadj)
    have hseparated : oldCenter.val + 1 < newCenter.val := by
      change prior.val + 2 + 1 < target.val + 2
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal]
      omega
    exact (skeleton.separated_not_adjacent oldCenter newCenter hseparated)
      hfaceAdj

/-- A strict historical selected Cell and the successor selected Cell cannot
share an edge which is internal to both two-vertex sides. -/
theorem pointwiseSelected_not_common_internalEdge_of_lt_next
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
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    {edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hpriorRegion : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior prior)
    (hpriorNotCrossing : edge ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior prior))
    (hnextRegion : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext))
    (hnextNotCrossing : edge ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext))) :
    False := by
  let target := sourceLocalLayerNextOffset offset hnext
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have hsideEq :=
    pointwiseSelectedSourceLocalLayerCellVertexSideAt_eq_of_common_internalEdge
      graphData minimal caps coloring web corridor hinterior prior target
        hpriorRegion hpriorNotCrossing (by simpa [target] using hnextRegion)
          (by simpa [target] using hnextNotCrossing)
  rcases exists_pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_cellCrossing
      graphData minimal caps coloring web corridor hinterior target with
    ⟨newStep, hnewCrossing⟩
  have holdCrossing :
      pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation corridor
          hinterior target newStep ∈
        vertexSetCrossingEdges web.annular.RS
          (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
            corridor hinterior prior) := by
    rw [hsideEq]
    exact hnewCrossing
  have hnewFace :
      pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation corridor
          hinterior target newStep ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt
            (nextCorridorInterior
              (pointwiseSelectedSourceLocalLayerInteriorAt target)
              (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext target)).center).1 := by
    simpa [skeleton] using
      pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary
        web.toFormation corridor hinterior target newStep
  rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
      web.toFormation corridor hinterior prior holdCrossing with
      ⟨oldStep, hedge⟩ | ⟨oldStep, hedge⟩
  · let oldCenter :=
      (pointwiseSelectedSourceLocalLayerInteriorAt prior).center
    let newCenter :=
      (nextCorridorInterior
        (pointwiseSelectedSourceLocalLayerInteriorAt target)
        (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext target)).center
    have holdFace :
        pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
            corridor hinterior target newStep ∈
          orbitFaceBoundary web.annular.RS
            (skeleton.faceAt oldCenter).1 := by
      rw [hedge]
      simpa [oldCenter, skeleton] using
        pointwiseSelectedSourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary
          web.toFormation corridor hinterior prior oldStep
    have hcentersNe : oldCenter ≠ newCenter := by
      intro hsame
      have hvalues := congrArg Fin.val hsame
      change prior.val + 1 = target.val + 2 at hvalues
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal] at hvalues
      omega
    have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
        (skeleton.faceAt newCenter).1 := by
      intro hsame
      exact hcentersNe (skeleton.faceAt_injective (Subtype.ext hsame))
    have hadj :=
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS) hfacesNe holdFace
          (by simpa [newCenter, skeleton] using hnewFace)
    have hseparated : oldCenter.val + 1 < newCenter.val := by
      change prior.val + 1 + 1 < target.val + 2
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal]
      omega
    exact (skeleton.separated_not_adjacent oldCenter newCenter hseparated) hadj
  · let oldCenter :=
      (nextCorridorInterior
        (pointwiseSelectedSourceLocalLayerInteriorAt prior)
        (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext prior)).center
    let newCenter :=
      (nextCorridorInterior
        (pointwiseSelectedSourceLocalLayerInteriorAt target)
        (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext target)).center
    have holdFace :
        pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
            corridor hinterior target newStep ∈
          orbitFaceBoundary web.annular.RS
            (skeleton.faceAt oldCenter).1 := by
      rw [hedge]
      simpa [oldCenter, skeleton] using
        pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary
          web.toFormation corridor hinterior prior oldStep
    have hcentersNe : oldCenter ≠ newCenter := by
      intro hsame
      have hvalues := congrArg Fin.val hsame
      change prior.val + 2 = target.val + 2 at hvalues
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal] at hvalues
      omega
    have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
        (skeleton.faceAt newCenter).1 := by
      intro hsame
      exact hcentersNe (skeleton.faceAt_injective (Subtype.ext hsame))
    have hadj :=
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS) hfacesNe holdFace
          (by simpa [newCenter, skeleton] using hnewFace)
    have hseparated : oldCenter.val + 1 < newCenter.val := by
      change prior.val + 2 + 1 < target.val + 2
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal]
      omega
    exact (skeleton.separated_not_adjacent oldCenter newCenter hseparated) hadj

/-- Every strict historical selected Cell edge recurring in the successor
rolling carrier is one of the four selected rebase edges. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_pastCellOverlap_mem_switch
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
    ∀
      (targetEdge : {edge // edge ∈
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext)})
      (prior : Fin (blockLength - 3)),
      prior.val < offset.val →
      targetEdge.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt
          web.toFormation corridor hinterior prior →
        targetEdge.1 ∈
          pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
            web.toFormation corridor hinterior offset hnext := by
  intro targetEdge prior hprior hpriorRegion
  let target := sourceLocalLayerNextOffset offset hnext
  let priorSide :=
    pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation corridor
      hinterior prior
  let targetSide :=
    pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation corridor
      hinterior target
  have htargetCarrier := targetEdge.property
  change targetEdge.1 ∈
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior target ∪
        pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt
          web.toFormation corridor hinterior target) ∪
          {pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
            corridor hinterior target} at htargetCarrier
  rw [Finset.mem_union] at htargetCarrier
  rcases htargetCarrier with htargetCore | htargetRung
  · rw [Finset.mem_union] at htargetCore
    rcases htargetCore with htargetCell | htargetOutgoing
    · by_cases htargetCrossing : targetEdge.1 ∈
          vertexSetCrossingEdges web.annular.RS targetSide
      · rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
          web.toFormation corridor hinterior target
            (by simpa [targetSide] using htargetCrossing) with
          ⟨newStep, htargetLeft⟩ | ⟨newStep, htargetRight⟩
        · rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
          refine ⟨.inr (.inl newStep), ?_⟩
          simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, target]
            using htargetLeft.symm
        · by_cases hpriorCrossing : targetEdge.1 ∈
              vertexSetCrossingEdges web.annular.RS priorSide
          · exact
              (pointwiseSelected_not_pastCellCrossing_eq_or_adj_nextRightCrossing
                graphData minimal caps coloring web corridor hinterior offset
                  hnext prior hprior
                    (by simpa [priorSide] using hpriorCrossing) newStep
                      (Or.inl (by simpa [target] using htargetRight))).elim
          · rcases
                exists_pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_cellCrossing
                  graphData minimal caps coloring web corridor hinterior prior with
              ⟨oldStep, holdCrossing⟩
            have hadj := pointwiseSelected_internalEdge_adj_crossingEdge
              graphData minimal caps coloring web corridor hinterior prior
                hpriorRegion (by simpa [priorSide] using hpriorCrossing)
                  holdCrossing
            exact
              (pointwiseSelected_not_pastCellCrossing_eq_or_adj_nextRightCrossing
                graphData minimal caps coloring web corridor hinterior offset
                  hnext prior hprior holdCrossing newStep
                    (Or.inr (by
                      simpa [target, htargetRight] using hadj.symm))).elim
      · by_cases hpriorCrossing : targetEdge.1 ∈
            vertexSetCrossingEdges web.annular.RS priorSide
        · rcases
              exists_pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_cellCrossing
                graphData minimal caps coloring web corridor hinterior target with
            ⟨newStep, hnewCrossing⟩
          have hadj := pointwiseSelected_internalEdge_adj_crossingEdge
            graphData minimal caps coloring web corridor hinterior target
              htargetCell (by simpa [targetSide] using htargetCrossing)
                hnewCrossing
          exact
            (pointwiseSelected_not_pastCellCrossing_eq_or_adj_nextRightCrossing
              graphData minimal caps coloring web corridor hinterior offset
                hnext prior hprior
                  (by simpa [priorSide] using hpriorCrossing) newStep
                    (Or.inr (by simpa [target] using hadj))).elim
        · exact
            (pointwiseSelected_not_common_internalEdge_of_lt_next graphData
              minimal caps coloring web corridor hinterior offset hnext prior
                hprior hpriorRegion
                  (by simpa [priorSide] using hpriorCrossing) htargetCell
                    (by simpa [targetSide, target] using htargetCrossing)).elim
    · rcases (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff
          (indexedCrossingEdgeSet
            (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
              corridor hinterior target)) targetEdge.1).1
        (by simpa
          [pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt,
            target] using htargetOutgoing) with htargetRight | htargetAdj
      · rcases (mem_indexedCrossingEdgeSet_iff
            (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
              corridor hinterior target) targetEdge.1).1 htargetRight with
          ⟨newStep, htargetRightEq⟩
        by_cases hpriorCrossing : targetEdge.1 ∈
            vertexSetCrossingEdges web.annular.RS priorSide
        · exact
            (pointwiseSelected_not_pastCellCrossing_eq_or_adj_nextRightCrossing
              graphData minimal caps coloring web corridor hinterior offset
                hnext prior hprior
                  (by simpa [priorSide] using hpriorCrossing) newStep
                    (Or.inl (by
                      simpa [target] using htargetRightEq.symm))).elim
        · rcases
              exists_pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_cellCrossing
                graphData minimal caps coloring web corridor hinterior prior with
            ⟨oldStep, holdCrossing⟩
          have hadj := pointwiseSelected_internalEdge_adj_crossingEdge
            graphData minimal caps coloring web corridor hinterior prior
              hpriorRegion (by simpa [priorSide] using hpriorCrossing)
                holdCrossing
          exact
            (pointwiseSelected_not_pastCellCrossing_eq_or_adj_nextRightCrossing
              graphData minimal caps coloring web corridor hinterior offset
                hnext prior hprior holdCrossing newStep
                  (Or.inr (by
                    simpa [target, htargetRightEq] using hadj.symm))).elim
      · rcases htargetAdj with ⟨rightEdge, hrightEdge, hadj⟩
        rcases (mem_indexedCrossingEdgeSet_iff
            (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
              corridor hinterior target) rightEdge).1 hrightEdge with
          ⟨newStep, hrightEq⟩
        by_cases hpriorCrossing : targetEdge.1 ∈
            vertexSetCrossingEdges web.annular.RS priorSide
        · exact
            (pointwiseSelected_not_pastCellCrossing_eq_or_adj_nextRightCrossing
              graphData minimal caps coloring web corridor hinterior offset
                hnext prior hprior
                  (by simpa [priorSide] using hpriorCrossing) newStep
                    (Or.inr (by simpa [target, hrightEq] using hadj))).elim
        · have hrightPriorCrossing :=
            pointwiseSelected_crossingEdge_of_internalEdge_adj graphData
              minimal caps coloring web corridor hinterior prior hpriorRegion
                (by simpa [priorSide] using hpriorCrossing) hadj
          exact
            (pointwiseSelected_not_pastCellCrossing_eq_or_adj_nextRightCrossing
              graphData minimal caps coloring web corridor hinterior offset
                hnext prior hprior hrightPriorCrossing newStep
                  (Or.inl (by simpa [target] using hrightEq.symm))).elim
  · have htargetRungEq : targetEdge.1 =
        pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation corridor
          hinterior target := by
      simpa using htargetRung
    rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
    refine ⟨.inr (.inr ⟨0, by omega⟩), ?_⟩
    simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, target] using
      htargetRungEq.symm

/-- Every active edge of the next selected rolling carrier is either a rebase
switch edge or belongs to the current literal selected Cell. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
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
    (targetEdge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)})
    (hactive : targetEdge.1 ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)) :
    targetEdge.1 ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
        web.toFormation corridor hinterior offset hnext ∨
      targetEdge.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt
        web.toFormation corridor hinterior offset := by
  by_cases hswitch : targetEdge.1 ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
        corridor hinterior offset hnext
  · exact Or.inl hswitch
  have hpre : targetEdge.1 ∈
      pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
        web.toFormation corridor hinterior offset :=
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
      web.toFormation corridor hinterior offset hnext targetEdge.1 hswitch).2
        hactive
  rw [← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
    web.toFormation corridor hinterior offset, Finset.mem_union] at hpre
  rcases hpre with hold | hcell
  · rw [pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt,
      Finset.mem_union] at hold
    rcases hold with hinput | hrung
    · rw [pointwiseSelectedSourceLocalLayerSerialInputRegionAt,
        Finset.mem_union] at hinput
      rcases hinput with hprefix | hcrossing
      · rw [pointwiseSelectedSourceLocalLayerSerialPrefixRegion,
          Finset.mem_biUnion] at hprefix
        rcases hprefix with ⟨prior, hprior, hpriorCell⟩
        exact Or.inl
          (pointwiseSelectedSourceLocalLayerSerialCellRebase_pastCellOverlap_mem_switch
            graphData minimal caps coloring web corridor hinterior offset hnext
              targetEdge prior (Finset.mem_filter.mp hprior).2 hpriorCell)
      · rcases (mem_indexedCrossingEdgeSet_iff
            (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
              corridor hinterior offset) targetEdge.1).1 hcrossing with
          ⟨step, hedge⟩
        exact Or.inr (by
          rw [← hedge]
          exact pointwiseSelectedSourceLocalLayerCellRegionAt_leftCrossing
            web.toFormation corridor hinterior offset step)
    · apply Or.inl
      have hedge : targetEdge.1 =
          pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
            corridor hinterior offset := by
        simpa using hrung
      rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inl ⟨0, by omega⟩, ?_⟩
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt] using
        hedge.symm
  · exact Or.inr hcell

end


end GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap

end Mettapedia.GraphTheory.FourColor
