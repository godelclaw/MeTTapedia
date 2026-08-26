import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState

/-!
# Exactness of the rooted facial pre-rebase update

The graph-free update on a forty-eight-dart interaction root is exact on every
source-extracted arbitrary compatible prefix and every literal physical Cell.
The proof checks adjacency and literal presence separately, then applies the
generic weighted interface-update theorem.  In particular, an isolated but
present dart is not confused with an absent coordinate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseExact

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellSplicedFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceExteriorLabelCapFactorUpdate
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedInteractionFacePreRebaseExactEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance rootedInteractionFacePreRebaseExactOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- On a literal Cell factor, the native Boolean facial adjacency table is
the already verified exact Cell/seam row on the current rolling carrier. -/
theorem sourceLocalLayerSerialPhysicalFaceLocalAdjacencyAt_eq
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellCrossing : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (left right : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset
        hnext prefixColor hprefixCrossing
    let localFactor :=
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellCrossing).2.2
    sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency
        state.toSourceLocalLayerSerialColoredCumulativeState localFactor (by rfl)
        left right =
      sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset
        (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring
          web corridor hunique offset) left right := by
  classical
  simp only [sourceLocalLayerSerialRootedInteractionStateForColorAt,
    sourceLocalLayerSerialRootedCumulativeStateForColorAt,
    sourceLocalLayerSerialColoredCumulativeStateForColorAt,
    sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt,
    sourceLocalLayerSerialSplicedCellFiniteSupportLetterAt,
    sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency]
  simp only [ofGraphFamilyCode_toGraph]
  unfold sourceLocalLayerSerialFaceLocalAdjacencyAt
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor <;> intro hadj <;> exact hadj

/-- On source data, lifting the native Cell/seam facial row to the complete
interaction carrier reconstructs exactly the literal local facial graph. -/
theorem
    sourceLocalLayerSerialRootedInteractionFaceLocalAdjacencyAt_eq_true_iff
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellCrossing : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (hcount :
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext prefixColor
          hprefixCrossing).faceCapSix.vertexCount =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellCrossing
        ).2.2.faceCode.vertexCount)
    (left right : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card) :
    sourceLocalLayerSerialRootedInteractionFaceLocalAdjacency
        (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
          caps coloring web corridor hunique offset hnext prefixColor
            hprefixCrossing)
        (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
          caps coloring web corridor hunique offset cellColor hcellCrossing).2.2
        hcount left right = true ↔
      (sourceLocalLayerSerialFaceLocalGraphAt corridor hunique offset).Adj
        (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
          offset hnext left)
        (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
          offset hnext right) := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing
  let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
    minimal caps coloring web corridor hunique offset cellColor hcellCrossing
    ).2.2
  let current := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let interaction := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let extra := sourceLocalLayerSerialFaceLocalGraphAt corridor hunique offset
  let oldVertex := fun slot : Fin current.card =>
    ((carrierCoordinate current).symm slot).1
  let newVertex := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  have hcoordinate : ∀ old,
      newVertex (state.faceCurrentCoordinate old) = oldVertex old := by
    intro old
    exact
      sourceLocalLayerSerialRootedInteractionStateForColorAt_faceCurrentDart
        graphData minimal caps coloring web corridor hunique offset hnext
          prefixColor hprefixCrossing old
  have hnewInjective : Function.Injective newVertex :=
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor hunique
      offset hnext
  have hsupport : extra.support ⊆ Set.range oldVertex := by
    exact sourceLocalLayerSerialFaceLocalGraph_support_subset_range corridor
      hunique offset
  have hadjacency : ∀ oldLeft oldRight,
      sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency
          state.toSourceLocalLayerSerialColoredCumulativeState factor hcount
          oldLeft oldRight = true ↔
        extra.Adj (oldVertex oldLeft) (oldVertex oldRight) := by
    intro oldLeft oldRight
    change Fin current.card at oldLeft oldRight
    have hcountRfl : hcount = (by rfl) := Subsingleton.elim _ _
    rw [hcountRfl]
    rw [sourceLocalLayerSerialPhysicalFaceLocalAdjacencyAt_eq graphData minimal
      caps coloring web corridor hunique offset hnext prefixColor
        hprefixCrossing cellColor hcellCrossing oldLeft oldRight]
    simpa [extra, oldVertex, current] using
      (sourceLocalLayerSerialFaceLocalAdjacency_exact corridor hunique offset
        (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring
          web corridor hunique offset) oldLeft oldRight)
  exact liftInterfaceAdjacency_eq_true_iff extra oldVertex newVertex
    state.faceCurrentCoordinate hcoordinate hnewInjective hsupport
    (sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency
      state.toSourceLocalLayerSerialColoredCumulativeState factor hcount)
    hadjacency left right

/-- On source data, the lifted finite activity row is exactly literal Cell
membership on every coordinate of the complete facial interaction carrier. -/
theorem
    sourceLocalLayerSerialRootedInteractionFaceLocalPresenceAt_eq_true_iff
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellCrossing : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (slot : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card) :
    sourceLocalLayerSerialRootedInteractionFaceLocalPresence
        (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
          caps coloring web corridor hunique offset hnext prefixColor
            hprefixCrossing)
        (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
          caps coloring web corridor hunique offset cellColor hcellCrossing).2.2
        slot = true ↔
      web.annular.RS.edgeOf
          (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
            offset hnext slot) ∈
        sourceLocalLayerCellRegionAt corridor hunique offset := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing
  let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
    minimal caps coloring web corridor hunique offset cellColor hcellCrossing
    ).2.2
  let current := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let interaction := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let oldVertex := fun old : Fin current.card =>
    ((carrierCoordinate current).symm old).1
  let newVertex := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  have hcoordinate : ∀ old,
      newVertex (state.faceCurrentCoordinate old) = oldVertex old := by
    intro old
    exact
      sourceLocalLayerSerialRootedInteractionStateForColorAt_faceCurrentDart
        graphData minimal caps coloring web corridor hunique offset hnext
          prefixColor hprefixCrossing old
  have hnewInjective : Function.Injective newVertex :=
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor hunique
      offset hnext
  have hpresent : ∀ old,
      factor.faceEdgeState.cellPresent
          (Fin.castLE
            (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) old) = true ↔
        web.annular.RS.edgeOf (oldVertex old) ∈
          sourceLocalLayerCellRegionAt corridor hunique offset := by
    intro old
    change Fin current.card at old
    have hslot :
        Fin.castLE
            (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) old =
          sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
            (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
              coloring web corridor hunique offset)
            ((carrierCoordinate current).symm old) := by
      apply Fin.ext
      change old.val =
        (carrierCoordinate current
          ((carrierCoordinate current).symm (Fin.cast (by rfl) old))).val
      rw [Equiv.apply_symm_apply]
      rfl
    change
      (sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique offset
        (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring
          web corridor hunique offset)).cellPresent
          (Fin.castLE
            (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) old) = true ↔
        web.annular.RS.edgeOf (oldVertex old) ∈
          sourceLocalLayerCellRegionAt corridor hunique offset
    rw [hslot,
      sourceLocalLayerSerialFaceFiniteEdgeStateAt_cellPresent_iff]
  have hcovered : ∀ new,
      web.annular.RS.edgeOf (newVertex new) ∈
          sourceLocalLayerCellRegionAt corridor hunique offset →
        ∃ old, oldVertex old = newVertex new := by
    intro new hcell
    have hcurrent : newVertex new ∈ current := by
      apply Finset.mem_union_left
      exact (mem_dartsOnEdges_iff web.annular.RS _ _).2 hcell
    refine ⟨carrierCoordinate current ⟨newVertex new, hcurrent⟩, ?_⟩
    simp [oldVertex]
  exact
    GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState.liftInterfacePresence_eq_true_iff_of_exact
    oldVertex newVertex
    state.faceCurrentCoordinate hcoordinate hnewInjective
    (fun old ↦ factor.faceEdgeState.cellPresent
      (Fin.castLE
        (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) old))
    (fun dart ↦ web.annular.RS.edgeOf dart ∈
      sourceLocalLayerCellRegionAt corridor hunique offset)
    hpresent hcovered slot

/-- The literal Cell/seam facial graph is supported on the complete
forty-eight-coordinate interaction carrier. -/
theorem
    sourceLocalLayerSerialFaceLocalGraph_support_subset_interaction_range
    (graphData : Data G)
    (_minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
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
    let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    (sourceLocalLayerSerialFaceLocalGraphAt corridor hunique offset).support ⊆
      Set.range dartAt := by
  dsimp only
  intro dart hdart
  let current := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let interaction := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  have hcurrent : dart ∈ current :=
    sourceLocalLayerSerialFaceLocalGraph_support_subset_carrier corridor hunique
      offset hdart
  have hinteraction : dart ∈ interaction := Finset.mem_union_left _ hcurrent
  refine ⟨carrierCoordinate interaction ⟨dart, hinteraction⟩, ?_⟩
  simp [sourceLocalLayerSerialCellRebaseUniformFaceDartAt, interaction]

/-- Canonical exact cap-six facial code immediately before the boundary
rebase, on the complete bounded interaction carrier. -/
noncomputable def
    sourceLocalLayerSerialFaceInteractionPreRebaseStateAt
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
    SourceLocalLayerSerialFaceInteractionPrefixState :=
  let interaction := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  { vertexCount := ⟨interaction.card,
      Nat.lt_succ_of_le
        (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
          graphData minimal caps coloring web corridor hunique offset hnext)⟩
    code := fun _ ↦ exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      dartAt 6 }

/-- For an arbitrary compatible prefix and a literal physical Cell, the
graph-free enlarged update is exactly the canonical pre-rebase facial code. -/
theorem
    sourceLocalLayerSerialRootedInteractionFacePreRebaseStateAt_code_eq
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellCrossing : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (hcount :
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext prefixColor
          hprefixCrossing).faceCapSix.vertexCount =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellCrossing
        ).2.2.faceCode.vertexCount) :
    (sourceLocalLayerSerialRootedInteractionFacePreRebaseState
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext prefixColor
          hprefixCrossing)
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellCrossing).2.2
      hcount).code () =
    (sourceLocalLayerSerialFaceInteractionPreRebaseStateAt graphData minimal caps
      coloring web corridor hunique offset hnext).code () := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing
  let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
    minimal caps coloring web corridor hunique offset cellColor hcellCrossing
    ).2.2
  let interaction := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let prefixRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor
    hunique offset
  let cellRegion := sourceLocalLayerCellRegionAt corridor hunique offset
  let prefixGraph := faceRegionalDartGraph web.annular.RS prefixRegion
  let localGraph := sourceLocalLayerSerialFaceLocalGraphAt corridor hunique
    offset
  let adjacency :=
    sourceLocalLayerSerialRootedInteractionFaceLocalAdjacency state factor
      hcount
  let presence :=
    sourceLocalLayerSerialRootedInteractionFaceLocalPresence state factor
  have hadjacency : ∀ left right,
      adjacency left right = true ↔
        localGraph.Adj (dartAt left) (dartAt right) := by
    intro left right
    exact
      sourceLocalLayerSerialRootedInteractionFaceLocalAdjacencyAt_eq_true_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          prefixColor hprefixCrossing cellColor hcellCrossing hcount left right
  have hpresence : presence = fun slot ↦
      decide (web.annular.RS.edgeOf (dartAt slot) ∈ cellRegion) := by
    funext slot
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact
      sourceLocalLayerSerialRootedInteractionFaceLocalPresenceAt_eq_true_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          prefixColor hprefixCrossing cellColor hcellCrossing slot
  have hupdate := addInterfaceAdjacencyAndPresence_exact_code_eq
    prefixGraph localGraph dartAt
    (sourceLocalLayerSerialFaceLocalGraph_support_subset_interaction_range
      graphData minimal caps coloring web corridor hunique offset hnext)
    (fun dart ↦ web.annular.RS.edgeOf dart ∈ prefixRegion)
    (fun dart ↦ web.annular.RS.edgeOf dart ∈ cellRegion)
    Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
    web.annular.RS.edgeOf adjacency hadjacency 6
  change addInterfaceAdjacencyAndPresence
      (exactInterfaceExteriorLabelCapCode prefixGraph dartAt
        (fun dart ↦ web.annular.RS.edgeOf dart ∈ prefixRegion)
        Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
        web.annular.RS.edgeOf 6)
      adjacency presence =
    exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      dartAt 6
  rw [hpresence]
  unfold exactFaceInterfaceExteriorLabelCapCode
  rw [sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
    hunique offset, sup_assoc]
  rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor hunique
    offset]
  simpa only [prefixGraph, localGraph, prefixRegion, cellRegion,
    sourceLocalLayerSerialFaceLocalGraphAt, Finset.mem_union] using hupdate

/-- The guarded facial interaction update succeeds on every literal source
Cell and returns the canonical exact pre-rebase code. -/
theorem sourceLocalLayerSerialRootedInteractionFacePreRebaseState?_at
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellCrossing : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext
        prefixColor hprefixCrossing
    let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcellCrossing).2.2
    sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state factor =
      some (sourceLocalLayerSerialFaceInteractionPreRebaseStateAt graphData
        minimal caps coloring web corridor hunique offset hnext) := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing
  let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
    minimal caps coloring web corridor hunique offset cellColor hcellCrossing
    ).2.2
  let expected := sourceLocalLayerSerialFaceInteractionPreRebaseStateAt
    graphData minimal caps coloring web corridor hunique offset hnext
  change sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state factor =
    some expected
  unfold sourceLocalLayerSerialRootedInteractionFacePreRebaseState?
  split <;> rename_i hcount
  · congr 1
    unfold sourceLocalLayerSerialRootedInteractionFacePreRebaseState
    congr 1
    funext family
    exact
      sourceLocalLayerSerialRootedInteractionFacePreRebaseStateAt_code_eq
        graphData minimal caps coloring web corridor hunique offset hnext
          prefixColor hprefixCrossing cellColor hcellCrossing hcount
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseExact

end Mettapedia.GraphTheory.FourColor
