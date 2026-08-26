import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode

/-!
# Finite tracked successor of one rooted Cell--rebase step

The rooted interaction state and a physical Cell factor now compute the exact
pre-rebase exterior code on the complete forty-nine-coordinate interaction
carrier.  This file packages the remaining tracked rebase data as one finite
factor: the switch mask, the local successor adjacency, and the partial map
from the next rolling carrier back into the interaction carrier.

The transition is graph-free.  It masks the four retired switch edges, adds
the local successor graph, and contracts forgotten interaction coordinates
into the exterior row of the next twenty-one-coordinate carrier.  On literal
source data this finite computation is exactly the canonical deletion-stable
tracked state of the next cumulative prefix.

No arbitrary finite factor is asserted to be source-realizable, and no
reachable closure is measured here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedInteractionTrackedSuccessorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Source-independent tracked data for the boundary-rebase half of one
literal Cell transition.  Both dependent carriers retain their actual
cardinalities; no padded vertices or aliases are introduced. -/
structure SourceLocalLayerSerialTrackedRebaseFactor where
  interactionCount : Fin 50
  targetCount : Fin 22
  switchMask : Fin interactionCount.val → Bool
  localAdjacency :
    TrackedColorPair →
      Fin interactionCount.val → Fin interactionCount.val → Bool
  targetSource :
    Fin targetCount.val → Option (Fin interactionCount.val)

noncomputable instance :
    DecidableEq SourceLocalLayerSerialTrackedRebaseFactor :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialTrackedRebaseFactorCode :=
  Σ interactionCount : Fin 50,
    Σ targetCount : Fin 22,
      (Fin interactionCount.val → Bool) ×
      (TrackedColorPair → Fin interactionCount.val →
        Fin interactionCount.val → Bool) ×
      (Fin targetCount.val → Option (Fin interactionCount.val))

private def sourceLocalLayerSerialTrackedRebaseFactorEquiv :
    SourceLocalLayerSerialTrackedRebaseFactor ≃
      sourceLocalLayerSerialTrackedRebaseFactorCode where
  toFun factor :=
    ⟨factor.interactionCount, factor.targetCount, factor.switchMask,
      factor.localAdjacency, factor.targetSource⟩
  invFun factor := {
    interactionCount := factor.1
    targetCount := factor.2.1
    switchMask := factor.2.2.1
    localAdjacency := factor.2.2.2.1
    targetSource := factor.2.2.2.2 }
  left_inv factor := by cases factor; rfl
  right_inv factor := by
    rcases factor with ⟨interactionCount, targetCount, switchMask,
      localAdjacency, targetSource⟩
    rfl

set_option synthInstance.maxSize 256 in
deriving noncomputable instance Fintype for
  sourceLocalLayerSerialTrackedRebaseFactorCode

noncomputable instance :
    Fintype SourceLocalLayerSerialTrackedRebaseFactor :=
  Fintype.ofEquiv _ sourceLocalLayerSerialTrackedRebaseFactorEquiv.symm

/-- Apply the switch deletion and local successor adjacency on the complete
interaction carrier. -/
def SourceLocalLayerSerialTrackedRebaseFactor.uniformSuccessorCode
    (factor : SourceLocalLayerSerialTrackedRebaseFactor)
    (preRebase : SourceLocalLayerSerialTrackedInteractionPrefixState)
    (hcount : preRebase.vertexCount = factor.interactionCount)
    (pair : TrackedColorPair) :
    BoundedInterfaceExteriorCode (Fin factor.interactionCount.val) :=
  addInterfaceAdjacency
    (maskInterfaceExteriorCode (hcount ▸ preRebase.code pair)
      factor.switchMask)
    (factor.localAdjacency pair)

/-- Contract the updated interaction code onto the next rolling carrier.
Forgotten coordinates become exterior waypoints through the generic exact
finite contraction. -/
def SourceLocalLayerSerialTrackedRebaseFactor.targetState
    (factor : SourceLocalLayerSerialTrackedRebaseFactor)
    (preRebase : SourceLocalLayerSerialTrackedInteractionPrefixState)
    (hcount : preRebase.vertexCount = factor.interactionCount) :
    SourceLocalLayerSerialTrackedDeletionStablePrefixState where
  vertexCount := factor.targetCount
  code := fun pair => partialContractedInterfaceExteriorCode
    (factor.uniformSuccessorCode preRebase hcount pair)
    factor.targetSource

/-- Guarded executable target contraction. -/
def SourceLocalLayerSerialTrackedRebaseFactor.targetState?
    (factor : SourceLocalLayerSerialTrackedRebaseFactor)
    (preRebase : SourceLocalLayerSerialTrackedInteractionPrefixState) :
    Option SourceLocalLayerSerialTrackedDeletionStablePrefixState :=
  if hcount : preRebase.vertexCount = factor.interactionCount then
    some (factor.targetState preRebase hcount)
  else none

/-- Complete graph-free tracked half of a rooted Cell--rebase transition. -/
def sourceLocalLayerSerialRootedInteractionTrackedSuccessorState?
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      outputCount)
    (rebaseFactor : SourceLocalLayerSerialTrackedRebaseFactor) :
    Option SourceLocalLayerSerialTrackedDeletionStablePrefixState :=
  (sourceLocalLayerSerialRootedInteractionPreRebaseState? state localFactor
    ).bind rebaseFactor.targetState?

/-- Literal finite rebase factor on the complete interaction carrier and the
next rolling target carrier. -/
noncomputable def sourceLocalLayerSerialTrackedRebaseFactorAt
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
    SourceLocalLayerSerialTrackedRebaseFactor := by
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  have hinteraction : interaction.card ≤ 49 :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique offset hnext
  have htarget : target.card ≤ 21 :=
    sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext)
  exact {
    interactionCount := ⟨interaction.card, Nat.lt_succ_of_le hinteraction⟩
    targetCount := ⟨target.card, Nat.lt_succ_of_le htarget⟩
    switchMask :=
      sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt graphData caps coloring
        web corridor hunique offset hnext
    localAdjacency := fun pair left right => by
      classical
      exact decide
        ((localTrackedGraphForColorAt corridor hunique offset hnext color pair
          ).Adj
          (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
            coloring web corridor hunique offset hnext left)
          (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
            coloring web corridor hunique offset hnext right))
    targetSource :=
      sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt graphData caps
        coloring web corridor hunique offset hnext }

/-- The source factor records the literal interaction carrier count. -/
@[simp]
theorem sourceLocalLayerSerialTrackedRebaseFactorAt_interactionCount
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
    (sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext color).interactionCount.val =
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext).card := by
  rfl

/-- The source factor records the literal next rolling carrier count. -/
@[simp]
theorem sourceLocalLayerSerialTrackedRebaseFactorAt_targetCount
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
    (sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext color).targetCount.val =
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)).card := by
  rfl

/-- Applying the literal finite factor to the canonical pre-rebase code gives
the existing exact contracted target code, row for row. -/
theorem sourceLocalLayerSerialTrackedRebaseTargetStateAt_code_eq
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let preRebase :=
      sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt graphData
        minimal caps coloring web corridor hunique offset hnext color
    let factor := sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal
      caps coloring web corridor hunique offset hnext color
    (factor.targetState preRebase (by rfl)).code pair =
      sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt graphData caps
        coloring web corridor hunique offset hnext color pair := by
  rfl

/-- The finite target contraction is exactly the deletion-stable tracked code
of the literal next cumulative prefix. -/
theorem sourceLocalLayerSerialTrackedRebaseTargetStateAt_eq
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
    let preRebase :=
      sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt graphData
        minimal caps coloring web corridor hunique offset hnext color
    let factor := sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal
      caps coloring web corridor hunique offset hnext color
    factor.targetState preRebase (by rfl) =
      sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt graphData
        minimal caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) color := by
  dsimp only
  unfold SourceLocalLayerSerialTrackedRebaseFactor.targetState
  unfold sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
  rw [BoundedInterfaceExteriorFamilyCode.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  funext pair
  change
    sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt graphData caps
      coloring web corridor hunique offset hnext color pair = _
  rw [sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt_exact
    graphData minimal caps coloring web corridor hunique offset hnext color
      pair]
  rfl

/-- On every compatible literal Cell, the complete graph-free transition
succeeds and returns exactly the next cumulative tracked state. -/
theorem sourceLocalLayerSerialRootedInteractionTrackedSuccessorState?_at
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
    let localFactor :=
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellColor).2.2
    let color := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
      coloring cellColor
    let rebaseFactor := sourceLocalLayerSerialTrackedRebaseFactorAt graphData
      minimal caps coloring web corridor hunique offset hnext color
    sourceLocalLayerSerialRootedInteractionTrackedSuccessorState? state
        localFactor rebaseFactor =
      some
        (sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
          graphData minimal caps coloring web corridor hunique
            (sourceLocalLayerNextOffset offset hnext) color) := by
  dsimp only
  rw [sourceLocalLayerSerialRootedInteractionTrackedSuccessorState?]
  rw [sourceLocalLayerSerialRootedInteractionPreRebaseState?_at graphData
    minimal caps coloring web corridor hunique offset hnext cellColor hcompatible
      hcellColor]
  simp only [Option.bind_some]
  unfold SourceLocalLayerSerialTrackedRebaseFactor.targetState?
  split <;> rename_i hcount
  · congr 1
    exact sourceLocalLayerSerialTrackedRebaseTargetStateAt_eq graphData minimal
      caps coloring web corridor hunique offset hnext
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor)
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor

end Mettapedia.GraphTheory.FourColor
