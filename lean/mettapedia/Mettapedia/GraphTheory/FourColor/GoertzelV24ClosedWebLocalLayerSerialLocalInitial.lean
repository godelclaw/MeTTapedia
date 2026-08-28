import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedSourceClosure

/-!
# Prefix-local initial witnesses for the literal source corridor

The positioned serial construction formerly represented a positive prefix
colouring by a function on every edge of the opened graph.  The transition
only observes that function on its terminal-aware prefix region.  This file
replaces the over-encoded function by a positive colour function on that
finite region and proves that the realizable initial profile image is
unchanged.

The local witness carries no second positive-colour coordinate on the
unprocessed suffix.  An extension by the fixed nonzero colour `red` is only a
representation adapter for the older API; restricting the extension recovers
the local function literally, and extending the restriction of an old witness
preserves its rooted source state.  This does not remove the global Tait
colouring already present in `ClosedWebAtGoodWord.Instance`; it closes only the
additional ambient-function dependency of the realization witness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialLocalInitial

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedClosure
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedSourceClosure
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRealizableTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FiniteClosureInterfaces
open GoertzelV24SourceCorridorProfile
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance localInitialOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A positive colour function whose domain is exactly the active
terminal-aware prefix region at one serial position. -/
abbrev SourceLocalLayerSerialLocalPositivePrefixAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :=
  PositiveColorFunction
    {edge : G.edgeSet // edge ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset}

/-- Extend a local prefix function only to satisfy the older ambient-function
API.  The arbitrary value outside the prefix is the fixed nonzero colour
`red`; no suffix datum is consulted. -/
noncomputable def extendLocalPositivePrefixAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (localColor : SourceLocalLayerSerialLocalPositivePrefixAt corridor hunique
      offset) :
    PositiveColorFunction G.edgeSet :=
  ⟨fun edge => if hregion : edge ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset then
      localColor.1 ⟨edge, hregion⟩
    else red,
    by
      intro edge
      by_cases hregion : edge ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset
      · simp [hregion, localColor.2]
      · simp [hregion]⟩

@[simp] theorem extendLocalPositivePrefixAt_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (localColor : SourceLocalLayerSerialLocalPositivePrefixAt corridor hunique
      offset)
    (edge : G.edgeSet)
    (hregion : edge ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) :
    (extendLocalPositivePrefixAt corridor hunique offset localColor).1 edge =
      localColor.1 ⟨edge, hregion⟩ := by
  simp [extendLocalPositivePrefixAt, hregion]

/-- Restrict an ambient positive function to the only region observed by the
source state. -/
def restrictPositivePrefixAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (ambientColor : PositiveColorFunction G.edgeSet) :
    SourceLocalLayerSerialLocalPositivePrefixAt corridor hunique offset :=
  ⟨fun edge => ambientColor.1 edge.1, fun edge => ambientColor.2 edge.1⟩

@[simp] theorem extend_restrictPositivePrefixAt_eq_of_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (ambientColor : PositiveColorFunction G.edgeSet)
    (edge : G.edgeSet)
    (hregion : edge ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) :
    (extendLocalPositivePrefixAt corridor hunique offset
      (restrictPositivePrefixAt corridor hunique offset ambientColor)).1 edge =
        ambientColor.1 edge := by
  simp [extendLocalPositivePrefixAt, restrictPositivePrefixAt, hregion]

/-- A literal Cell witness compatible with a positive colouring of only the
active terminal-aware prefix. -/
abbrev SourceLocalLayerSerialLocalRealizationAt
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
    (offset : Fin (blockLength - 3)) :=
  { data :
      SourceLocalLayerSerialLocalPositivePrefixAt corridor hunique offset ×
        SourceLocalLayerCellLiteralOpenTaitColoring corridor hunique
          (sourceLocalLayerInteriorAt offset)
            (sourceLocalLayerInteriorAt_hasNext offset) //
    ∀ edge
      (hprefix : edge ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      (_hcell : edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset),
      data.1.1 ⟨edge, hprefix⟩ =
        sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
          offset data.2 edge }

/-- Extend one local witness to the older ambient representation. -/
noncomputable def extendLocalRealizationAt
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
    (witness : SourceLocalLayerSerialLocalRealizationAt graphData caps coloring
      web corridor hunique offset) :
    SourceLocalLayerSerialRootedInteractionRealizationAt graphData caps coloring
      web corridor hunique offset hnext :=
  ⟨⟨extendLocalPositivePrefixAt corridor hunique offset witness.1.1,
      witness.1.2⟩,
    by
      intro edge hprefix hcell
      rw [extendLocalPositivePrefixAt_eq corridor hunique offset witness.1.1
        edge hprefix]
      exact witness.2 edge hprefix hcell⟩

/-- Restrict an older ambient witness to its genuinely observed prefix. -/
def restrictRealizationAt
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
    (witness : SourceLocalLayerSerialRootedInteractionRealizationAt graphData
      caps coloring web corridor hunique offset hnext) :
    SourceLocalLayerSerialLocalRealizationAt graphData caps coloring web corridor
      hunique offset :=
  ⟨⟨restrictPositivePrefixAt corridor hunique offset witness.1.1,
      witness.1.2⟩,
    by
      intro edge hprefix hcell
      exact witness.2 edge hprefix hcell⟩

/-- Extending after restriction leaves the complete rooted source receipt
unchanged.  This is the formal statement that the receipt cannot observe an
unprocessed suffix colouring. -/
theorem sourceState_extend_restrictRealizationAt_eq
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (witness : SourceLocalLayerSerialRootedInteractionRealizationAt graphData
      caps coloring web corridor hunique offset hnext) :
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext
          (extendLocalRealizationAt graphData caps coloring web corridor hunique
            offset hnext
              (restrictRealizationAt graphData caps coloring web corridor hunique
                offset hnext witness))).source =
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext witness).source := by
  classical
  apply sourceLocalLayerSerialRootedInteractionStateForColorAt_eq_of_eq_on_terminal
  intro edge hregion
  exact extend_restrictPositivePrefixAt_eq_of_mem corridor hunique offset
    witness.1.1 edge hregion

/-- Local first-position witnesses, with no suffix colouring coordinate. -/
abbrev SourceLocalLayerSerialLocalFirstRealization
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
    (hlength : 2 < blockLength - 3) :=
  SourceLocalLayerSerialLocalRealizationAt graphData caps coloring web corridor
    hunique (sourceLocalLayerSerialFirstRollingPosition hlength).offset

/-- The source profile produced by a local first-position witness. -/
noncomputable def sourceLocalLayerSerialLocalFirstSourceProfile
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
    (hlength : 2 < blockLength - 3)
    (witness : SourceLocalLayerSerialLocalFirstRealization graphData caps coloring
      web corridor hunique hlength) :
    SourceLocalLayerSerialPositionedSourceProfile :=
  sourceLocalLayerSerialFirstSourceProfile graphData minimal caps coloring web
    corridor hunique hlength
      (extendLocalRealizationAt graphData caps coloring web corridor hunique
        (sourceLocalLayerSerialFirstRollingPosition hlength).offset
        (sourceLocalLayerSerialFirstRollingPosition hlength).hasNext witness)

/-- The exact initial profile image obtained from local prefix witnesses. -/
noncomputable def sourceLocalLayerSerialLocalInitialSourceProfileSet
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
    (hlength : 2 < blockLength - 3) :
    Finset SourceLocalLayerSerialPositionedSourceProfile :=
  realizedCodeImage
    (sourceLocalLayerSerialLocalFirstSourceProfile graphData minimal caps coloring
      web corridor hunique hlength)

/-- The old ambient-function initial image and the prefix-local initial image
are exactly equal. -/
theorem sourceLocalLayerSerialLocalInitialSourceProfileSet_eq
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
    (hlength : 2 < blockLength - 3) :
    sourceLocalLayerSerialLocalInitialSourceProfileSet graphData minimal caps
        coloring web corridor hunique hlength =
      sourceLocalLayerSerialRealizedInitialSourceProfileSet graphData minimal
        caps coloring web corridor hunique hlength := by
  classical
  ext profile
  simp only [sourceLocalLayerSerialLocalInitialSourceProfileSet,
    realizedCodeImage, Finset.mem_image, Finset.mem_univ, true_and,
    mem_sourceLocalLayerSerialRealizedInitialSourceProfileSet_iff]
  constructor
  · rintro ⟨localWitness, rfl⟩
    exact ⟨extendLocalRealizationAt graphData caps coloring web corridor hunique
      (sourceLocalLayerSerialFirstRollingPosition hlength).offset
      (sourceLocalLayerSerialFirstRollingPosition hlength).hasNext localWitness,
      rfl⟩
  · rintro ⟨oldWitness, rfl⟩
    let localWitness := restrictRealizationAt graphData caps coloring web corridor
      hunique (sourceLocalLayerSerialFirstRollingPosition hlength).offset
        (sourceLocalLayerSerialFirstRollingPosition hlength).hasNext oldWitness
    refine ⟨localWitness, ?_⟩
    unfold sourceLocalLayerSerialLocalFirstSourceProfile
    rw [sourceLocalLayerSerialFirstSourceProfile_eq]
    rw [sourceLocalLayerSerialFirstSourceProfile_eq]
    apply congrArg (fun state : SourceLocalLayerSerialRootedInteractionState =>
      toBoundedSourceProfile state.input)
    exact sourceState_extend_restrictRealizationAt_eq graphData minimal caps
      coloring web corridor hunique
        (sourceLocalLayerSerialFirstRollingPosition hlength).offset
        (sourceLocalLayerSerialFirstRollingPosition hlength).hasNext
        (sourceLocalLayerSerialFirstRollingPosition hlength).hasNextNext
        oldWitness

end

end GoertzelV24ClosedWebLocalLayerSerialLocalInitial

end Mettapedia.GraphTheory.FourColor
