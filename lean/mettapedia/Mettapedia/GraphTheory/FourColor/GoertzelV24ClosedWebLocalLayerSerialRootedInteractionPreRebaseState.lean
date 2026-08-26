import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState

/-!
# Graph-free Cell update on the complete interaction carrier

The physical Cell factor is encoded on the current twenty-one-coordinate
carrier, while the rooted lookahead state records the prefix on the complete
forty-nine-coordinate Cell--rebase carrier.  This file lifts the Cell/seam
adjacency along the stored current-coordinate inclusion and adjoins it to the
lookahead exterior code.

The generic lifting theorem is representation invariant: whenever the old
and enlarged coordinate maps name the same vertices, the enlarged map is
injective, and the added graph is supported on the old interface, the lifted
Boolean adjacency is exact on the enlarged interface.  The source theorem
then shows that the finite update is precisely the literal tracked graph
immediately before the boundary rebase.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedPreRebaseState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedInteractionPreRebaseOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Lift an adjacency table from a smaller named interface to a larger one.
The existential form is alias-safe for arbitrary finite records. -/
def liftInterfaceAdjacency
    {Old New : Type*} [Fintype Old] [DecidableEq Old] [DecidableEq New]
    (coordinate : Old → New) (adjacency : Old → Old → Bool)
    (left right : New) : Bool :=
  decide (∃ oldLeft oldRight,
    coordinate oldLeft = left ∧ coordinate oldRight = right ∧
      adjacency oldLeft oldRight = true)

/-- Lifting along exact coordinate names reconstructs precisely an added
graph supported on the smaller interface. -/
theorem liftInterfaceAdjacency_eq_true_iff
    {N Old New : Type*} [Fintype Old] [DecidableEq Old] [DecidableEq New]
    (extra : SimpleGraph N)
    (oldVertex : Old → N) (newVertex : New → N)
    (coordinate : Old → New)
    (hcoordinate : ∀ old, newVertex (coordinate old) = oldVertex old)
    (hnewInjective : Function.Injective newVertex)
    (hsupport : extra.support ⊆ Set.range oldVertex)
    (adjacency : Old → Old → Bool)
    (hadjacency : ∀ left right,
      adjacency left right = true ↔
        extra.Adj (oldVertex left) (oldVertex right))
    (left right : New) :
    liftInterfaceAdjacency coordinate adjacency left right = true ↔
      extra.Adj (newVertex left) (newVertex right) := by
  classical
  simp only [liftInterfaceAdjacency, decide_eq_true_eq]
  constructor
  · rintro ⟨oldLeft, oldRight, hleft, hright, hadj⟩
    have hextra := (hadjacency oldLeft oldRight).1 hadj
    simpa [← hleft, ← hright, hcoordinate] using hextra
  · intro hadj
    have hleftSupport : newVertex left ∈ extra.support :=
      ⟨newVertex right, hadj⟩
    have hrightSupport : newVertex right ∈ extra.support :=
      ⟨newVertex left, hadj.symm⟩
    rcases hsupport hleftSupport with ⟨oldLeft, holdLeft⟩
    rcases hsupport hrightSupport with ⟨oldRight, holdRight⟩
    have hleft : coordinate oldLeft = left := by
      apply hnewInjective
      calc
        newVertex (coordinate oldLeft) = oldVertex oldLeft :=
          hcoordinate oldLeft
        _ = newVertex left := holdLeft
    have hright : coordinate oldRight = right := by
      apply hnewInjective
      calc
        newVertex (coordinate oldRight) = oldVertex oldRight :=
          hcoordinate oldRight
        _ = newVertex right := holdRight
    refine ⟨oldLeft, oldRight, hleft, hright, ?_⟩
    apply (hadjacency oldLeft oldRight).2
    simpa [← hleft, ← hright, hcoordinate] using hadj

/-- Lift the native physical Cell/seam table from the current coordinates to
the complete interaction coordinates stored in the rooted state. -/
def sourceLocalLayerSerialRootedInteractionLocalAdjacency
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      outputCount)
    (hcount : state.trackedExterior.vertexCount =
      localFactor.trackedGeometry.vertexCount)
    (pair : TrackedColorPair) :
    Fin state.interactionExterior.vertexCount.val →
      Fin state.interactionExterior.vertexCount.val → Bool :=
  liftInterfaceAdjacency state.currentCoordinate
    (sourceLocalLayerSerialRootedTrackedLocalAdjacency
      state.toSourceLocalLayerSerialRootedCumulativeState localFactor hcount pair)

/-- Adjoin one physical Cell and its seam to the complete interaction-rooted
prefix state. -/
def sourceLocalLayerSerialRootedInteractionPreRebaseState
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      outputCount)
    (hcount : state.trackedExterior.vertexCount =
      localFactor.trackedGeometry.vertexCount) :
    SourceLocalLayerSerialTrackedInteractionPrefixState where
  vertexCount := state.interactionExterior.vertexCount
  code := fun pair => addInterfaceAdjacency
    (state.interactionExterior.code pair)
    (sourceLocalLayerSerialRootedInteractionLocalAdjacency state localFactor
      hcount pair)

/-- Guarded executable form of the complete interaction-carrier update. -/
def sourceLocalLayerSerialRootedInteractionPreRebaseState?
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      outputCount) :
    Option SourceLocalLayerSerialTrackedInteractionPrefixState :=
  if hcount : state.trackedExterior.vertexCount =
      localFactor.trackedGeometry.vertexCount then
    some (sourceLocalLayerSerialRootedInteractionPreRebaseState state
      localFactor hcount)
  else none

/-- On literal source data, the lifted native table is exactly the local
Cell/seam graph on the complete interaction carrier. -/
theorem sourceLocalLayerSerialRootedInteractionLocalAdjacencyAt_eq_true_iff
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (hcount :
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext coloring
          (fun _ => web.tait _)).trackedExterior.vertexCount =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellColor
        ).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair)
    (left right : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext).card) :
    sourceLocalLayerSerialRootedInteractionLocalAdjacency
        (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
          caps coloring web corridor hunique offset hnext coloring
            (fun _ => web.tait _))
        (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
          caps coloring web corridor hunique offset cellColor hcellColor).2.2
        hcount pair left right = true ↔
      (sourceLocalLayerSerialTrackedLocalGraphForColorAt caps coloring web
        corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor) pair).Adj
        (((carrierCoordinate
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext)).symm left).1)
        (((carrierCoordinate
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext)).symm right).1) := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext coloring
      (fun _ => web.tait _)
  let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
    minimal caps coloring web corridor hunique offset cellColor hcellColor).2.2
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let spliced := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let extra := sourceLocalLayerSerialTrackedLocalGraphForColorAt caps coloring web
    corridor hunique offset spliced pair
  let oldVertex := fun slot : Fin current.card =>
    ((carrierCoordinate current).symm slot).1
  let newVertex := fun slot : Fin interaction.card =>
    ((carrierCoordinate interaction).symm slot).1
  have hcoordinate : ∀ old,
      newVertex (state.currentCoordinate old) = oldVertex old := by
    intro old
    exact sourceLocalLayerSerialRootedInteractionStateForColorAt_currentEdge
      graphData minimal caps coloring web corridor hunique offset hnext coloring
        (fun _ => web.tait _) old
  have hnewInjective : Function.Injective newVertex := by
    intro first second hedge
    apply (carrierCoordinate interaction).symm.injective
    exact Subtype.ext hedge
  have hsupport : extra.support ⊆ Set.range oldVertex := by
    exact sourceLocalLayerSerialTrackedLocalGraph_support_subset_range graphData
      caps coloring web corridor hunique offset spliced pair
  have hadjacency : ∀ oldLeft oldRight,
      sourceLocalLayerSerialRootedTrackedLocalAdjacency
          state.toSourceLocalLayerSerialRootedCumulativeState factor hcount pair
          oldLeft oldRight = true ↔
        extra.Adj (oldVertex oldLeft) (oldVertex oldRight) := by
    intro oldLeft oldRight
    change Fin current.card at oldLeft oldRight
    change
      sourceLocalLayerSerialRootedTrackedLocalAdjacency
          (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData
            minimal caps coloring web corridor hunique offset coloring
              (fun _ => web.tait _))
          (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
            minimal caps coloring web corridor hunique offset cellColor
              hcellColor).2.2
          hcount pair oldLeft oldRight = true ↔
        extra.Adj (oldVertex oldLeft) (oldVertex oldRight)
    have hnative := sourceLocalLayerSerialRootedTrackedLocalAdjacencyAt_eq
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcellColor hcount pair
    have hnativeAt := congrFun (congrFun hnative oldLeft) oldRight
    rw [hnativeAt]
    simpa [extra, oldVertex, current, spliced] using
      (sourceLocalLayerSerialTrackedLocalAdjacency_exact graphData minimal
        caps coloring web corridor hunique offset spliced pair oldLeft oldRight)
  exact liftInterfaceAdjacency_eq_true_iff extra oldVertex newVertex
    state.currentCoordinate hcoordinate hnewInjective hsupport
    (sourceLocalLayerSerialRootedTrackedLocalAdjacency
      state.toSourceLocalLayerSerialRootedCumulativeState factor hcount pair)
    hadjacency left right

/-- The literal Cell/seam graph is supported on the complete interaction
carrier, hence on the range of its canonical coordinate map. -/
theorem
    sourceLocalLayerSerialTrackedLocalGraph_support_subset_interaction_range
    (graphData : Data G)
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let interaction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext
    let edgeAt := fun slot : Fin interaction.card =>
      ((carrierCoordinate interaction).symm slot).1
    (sourceLocalLayerSerialTrackedLocalGraphForColorAt caps coloring web corridor
      hunique offset color pair).support ⊆ Set.range edgeAt := by
  dsimp only
  intro edge hedge
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  have hcurrent : edge ∈ current :=
    sourceLocalLayerSerialTrackedLocalGraph_support_subset_carrier graphData caps
      coloring web corridor hunique offset color pair hedge
  have hinteraction : edge ∈ interaction :=
    Finset.mem_union_left _ hcurrent
  refine ⟨carrierCoordinate interaction ⟨edge, hinteraction⟩, ?_⟩
  simp [interaction]

/-- Canonical exact pre-rebase code on the complete interaction carrier. -/
noncomputable def
    sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialTrackedInteractionPrefixState :=
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  boundedInterfaceExteriorFamilyCode interaction 49
    (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique offset hnext)
    (fun pair => regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)

/-- At a compatible literal Cell, every row of the graph-free enlarged update
is the exact pre-rebase row on the complete interaction carrier. -/
theorem
    sourceLocalLayerSerialRootedInteractionPreRebaseStateAt_code_eq
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (hcount :
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext coloring
          (fun _ => web.tait _)).trackedExterior.vertexCount =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellColor
        ).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair) :
    (sourceLocalLayerSerialRootedInteractionPreRebaseState
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext coloring
          (fun _ => web.tait _))
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellColor).2.2
      hcount).code pair =
      (sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        graphData minimal caps coloring web corridor hunique offset hnext
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor)).code pair := by
  classical
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let edgeAt := fun slot : Fin interaction.card =>
    ((carrierCoordinate interaction).symm slot).1
  let spliced := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let prefixGraph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    spliced (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let localGraph := sourceLocalLayerSerialTrackedLocalGraphForColorAt caps
    coloring web corridor hunique offset spliced pair
  let adjacency := sourceLocalLayerSerialRootedInteractionLocalAdjacency
    (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext coloring
        (fun _ => web.tait _))
    (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
      caps coloring web corridor hunique offset cellColor hcellColor).2.2
    hcount pair
  have hprefix : regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      spliced (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 =
      regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      coloring (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 :=
    regionalTrackedEdgeGraph_spliced_eq_prefix corridor hunique offset coloring
      cellColor hcompatible (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
  change addInterfaceAdjacency
      (exactInterfaceExteriorCode
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          coloring (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        edgeAt)
      adjacency =
    exactInterfaceExteriorCode
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        spliced (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      edgeAt
  rw [sourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor corridor
    hunique offset spliced (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2, sup_assoc, hprefix]
  apply addInterfaceAdjacency_exact_code_eq
  · exact
      sourceLocalLayerSerialTrackedLocalGraph_support_subset_interaction_range
        graphData caps coloring web corridor hunique offset hnext
          spliced pair
  · intro left right
    exact
      sourceLocalLayerSerialRootedInteractionLocalAdjacencyAt_eq_true_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          cellColor hcellColor hcount pair left right

/-- The guarded 49-coordinate update succeeds on every compatible literal
Cell and returns exactly the canonical pre-rebase interaction state. -/
theorem sourceLocalLayerSerialRootedInteractionPreRebaseState?_at
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext coloring
        (fun _ => web.tait _)
    let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcellColor).2.2
    sourceLocalLayerSerialRootedInteractionPreRebaseState? state factor =
      some (sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        graphData minimal caps coloring web corridor hunique offset hnext
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor)) := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext coloring
      (fun _ => web.tait _)
  let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
    minimal caps coloring web corridor hunique offset cellColor hcellColor).2.2
  let expected := sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
    graphData minimal caps coloring web corridor hunique offset hnext
      (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset coloring
        cellColor)
  change sourceLocalLayerSerialRootedInteractionPreRebaseState? state factor =
    some expected
  unfold sourceLocalLayerSerialRootedInteractionPreRebaseState?
  split <;> rename_i hcount
  · congr 1
    unfold sourceLocalLayerSerialRootedInteractionPreRebaseState
    congr 1
    funext pair
    exact sourceLocalLayerSerialRootedInteractionPreRebaseStateAt_code_eq
      graphData minimal caps coloring web corridor hunique offset hnext
        cellColor hcompatible hcellColor hcount pair
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState

end Mettapedia.GraphTheory.FourColor
