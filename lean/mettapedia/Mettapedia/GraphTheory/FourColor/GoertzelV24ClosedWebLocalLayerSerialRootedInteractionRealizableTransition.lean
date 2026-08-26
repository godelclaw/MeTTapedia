import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellCountRootedRollingFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteClosureInterfaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalProfileColorCongruence

/-!
# Source-realizable rooted rolling transitions

The ambient rooted state and rolling-factor types are finite but intentionally
over-encoded.  Enumerating either complete carrier would therefore measure the
representation rather than the source transfer system.

This file first takes the finite image of literal source witnesses.  A witness
consists of a positive cumulative prefix and a literal open Tait colouring of
one Cell, with the exact overlap compatibility required by gluing.  Its full
step certificate is the rooted source/factor/target triple.  Thus:

* every literal compatible Cell has a code (completeness);
* every code has a literal representative and its executable successor is the
  coded target (soundness);
* equal full certificates induce equal transition relations.

The full step certificate is useful for replay, but retaining its target would
make representation invariance tautological.  The exact executable alphabet
below therefore quotients witnesses by their finite Cell--rebase factor alone.
Equal factors induce definitionally equal transition functions, and the target
is computed by `successor?`, never stored in the quotient key.

A smaller optional quotient by `(source, literal Cell)` is isolated afterward
as `SourceLocalLayerSerialRootedInteractionTargetCongruentAt`.  That theorem is
a minimization result, not a prerequisite for sound finite closure over the
executable factor alphabet.

No enumeration of the ambient state or factor carrier occurs here.  The next
layer may enumerate the realized image, or replay an externally generated
sparse certificate for that same image.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRealizableTransition

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionColorParametric
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
open GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FiniteClosureInterfaces
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexCorridorSkeleton
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance realizableTransitionOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A finite colour function with no zero entry. -/
abbrev PositiveColorFunction (Edge : Type*) :=
  {color : Edge → Color // ∀ edge, color edge ≠ 0}

noncomputable instance positiveColorFunctionFintype
    (Edge : Type*) [Fintype Edge] : Fintype (PositiveColorFunction Edge) :=
  Fintype.ofFinite _

/-- One source witness for a fixed rolling Cell position: a positive prefix,
a literal open Tait colouring of the Cell, and exact agreement on their
overlap. -/
abbrev SourceLocalLayerSerialRootedInteractionRealizationAt
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
    (_hnext : offset.val + 1 < blockLength - 3) :=
  { data :
      PositiveColorFunction
          caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet ×
        SourceLocalLayerCellLiteralOpenTaitColoring corridor hunique
          (sourceLocalLayerInteriorAt offset)
            (sourceLocalLayerInteriorAt_hasNext offset) //
    SourceLocalLayerSerialCellColorsCompatibleAt corridor hunique offset
      data.1.1
      (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
        offset data.2) }

noncomputable instance sourceRealizationAtFintype
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
    (hnext : offset.val + 1 < blockLength - 3) :
    Fintype (SourceLocalLayerSerialRootedInteractionRealizationAt graphData
      caps coloring web corridor hunique offset hnext) :=
  Fintype.ofFinite _

/-- The finite transition record retained from one literal source witness. -/
structure SourceLocalLayerSerialRootedInteractionRealizedStep where
  source : SourceLocalLayerSerialRootedInteractionState
  factor : SourceLocalLayerSerialRootedInteractionRollingCellFactor
  target : SourceLocalLayerSerialRootedInteractionState

noncomputable instance :
    DecidableEq SourceLocalLayerSerialRootedInteractionRealizedStep :=
  Classical.decEq _

deriving noncomputable instance Fintype for
  SourceLocalLayerSerialRootedInteractionRealizedStep

/-- Extract the exact finite source/factor/target triple from a compatible
literal witness. -/
noncomputable def sourceLocalLayerSerialRootedInteractionRealizedStepAt
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
    SourceLocalLayerSerialRootedInteractionRealizedStep := by
  let prefixColor := witness.1.1.1
  let hprefix := witness.1.1.2
  let cellColoring := witness.1.2
  let cellColor := sourceLocalLayerCellLiteralColorAt caps coloring web corridor
    hunique offset cellColoring
  let hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0 :=
    sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web corridor
      hunique offset cellColoring
  let hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor
        hunique offset).crossingEdge step) ≠ 0 := fun step =>
    hprefix ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
      offset).crossingEdge step)
  let source := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing
  let factor :=
    sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext
        prefixColor hprefix cellColor hcell
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
      corridor hunique offset hnext prefixColor cellColor hprefix hcell
  let hnextCrossing := successorCrossingNonzeroForColorAt corridor hunique offset
    hnext splice hrole
  let target := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique
      (sourceLocalLayerNextOffset offset hnext) hnextNext splice hnextCrossing
  exact ⟨source, factor, target⟩

/-- The graph-free transition relation carried by a realized step code. -/
def SourceLocalLayerSerialRootedInteractionRealizedStep.transition
    (step : SourceLocalLayerSerialRootedInteractionRealizedStep)
    (source target : SourceLocalLayerSerialRootedInteractionState) : Prop :=
  source = step.source ∧
    step.factor.successor? source = some target ∧ target = step.target

/-- Soundness of extraction: the executable finite factor of every source
witness accepts its source code and returns its target code exactly. -/
theorem sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition
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
    let step := sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext witness
    step.transition step.source step.target := by
  classical
  dsimp only
  refine ⟨rfl, ?_, rfl⟩
  exact
    sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt_successor_exact
      graphData minimal caps coloring web corridor hunique offset hnext hnextNext
        witness.1.1.1 witness.1.1.2
        (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
          offset witness.1.2)
        witness.2
        (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
          corridor hunique offset witness.1.2)

/-- The finite alphabet of source-realized rooted rolling steps at one fixed
Cell position. -/
abbrev SourceLocalLayerSerialRootedInteractionRealizedLetterAt
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :=
  RealizedCode
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext)

/-- Exact source presentation at one Cell position.  Its alphabet bound is
the cardinality of the realized image, not the ambient factor carrier. -/
noncomputable def sourceLocalLayerSerialRootedInteractionPresentationAt
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :=
  RootedLetterPresentation.ofFiniteImage
    (fun witness =>
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal
        caps coloring web corridor hunique offset hnext hnextNext witness
      ).transition)
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext)
    (by
      intro left right heq
      simp [heq])

/-- Every canonical letter in the realized image is sound: at its recorded
source it executes to its recorded target. -/
theorem sourceLocalLayerSerialRootedInteraction_codedTransition
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
    (letter : SourceLocalLayerSerialRootedInteractionRealizedLetterAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext) :
    (sourceLocalLayerSerialRootedInteractionPresentationAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext).codedTransition
        letter letter.1.source letter.1.target := by
  classical
  let encode :=
    sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext
  let representative := realizedCodeRepresentative encode letter
  have hrepresentative : encode representative = letter.1 := by
    exact congrArg Subtype.val (realizedCodeOf_representative encode letter)
  change
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext representative
    ).transition letter.1.source letter.1.target
  rw [← hrepresentative]
  exact sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition
    graphData minimal caps coloring web corridor hunique offset hnext hnextNext
      representative

/-- The finite image of source states which have at least one compatible
literal Cell witness at this position.  This is the exact realizable initial
carrier for a one-step closure, not a filter over the ambient state type. -/
abbrev SourceLocalLayerSerialRootedInteractionRealizedStateAt
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :=
  RealizedCode (fun witness =>
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext witness).source)

/-- The cardinality of the realizable one-step state carrier is exactly the
cardinality of the finite source image. -/
theorem card_sourceLocalLayerSerialRootedInteractionRealizedStateAt
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    Fintype.card
        (SourceLocalLayerSerialRootedInteractionRealizedStateAt graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext) =
      (realizedCodeImage (fun witness =>
        (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext witness
        ).source)).card := by
  exact card_realizedCode _

/-- The literal witness transition is exactly the canonical transition of its
full realized-step certificate.  This is useful certificate reflection, but it
does not by itself establish congruence after quotienting prefix witnesses by
their rooted source state. -/
theorem sourceLocalLayerSerialRootedInteraction_rawTransition_eq_codedTransition
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
    (sourceLocalLayerSerialRootedInteractionPresentationAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext).rawTransition
        witness =
      (sourceLocalLayerSerialRootedInteractionPresentationAt graphData minimal
        caps coloring web corridor hunique offset hnext hnextNext
      ).codedTransition
        ((sourceLocalLayerSerialRootedInteractionPresentationAt graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext).code
            witness) := by
  exact RootedLetterPresentation.rawTransition_eq_codedTransition _ witness

/-- The actual executable transition relation of one finite Cell--rebase
factor.  Unlike `RealizedStep.transition`, this relation does not retain a
source or target endpoint. -/
def sourceLocalLayerSerialRootedInteractionFactorTransition
    (factor : SourceLocalLayerSerialRootedInteractionRollingCellFactor)
    (source target : SourceLocalLayerSerialRootedInteractionState) : Prop :=
  factor.successor? source = some target

/-- The realized executable alphabet: precisely the finite factors compiled
from compatible positive prefix/Cell witnesses at this position. -/
abbrev SourceLocalLayerSerialRootedInteractionRealizedFactorAt
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :=
  RealizedCode (fun witness =>
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext witness).factor)

/-- Representation invariance of the executable alphabet.  Ambient witnesses
which compile to the same finite factor induce the same transition function
on every rooted source and target state. -/
theorem sourceLocalLayerSerialRootedInteraction_factorTransition_invariant
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
    {left right : SourceLocalLayerSerialRootedInteractionRealizationAt graphData
      caps coloring web corridor hunique offset hnext}
    (hfactor :
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext left).factor =
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).factor) :
    sourceLocalLayerSerialRootedInteractionFactorTransition
        (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext left).factor =
      sourceLocalLayerSerialRootedInteractionFactorTransition
        (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext right).factor := by
  exact congrArg sourceLocalLayerSerialRootedInteractionFactorTransition hfactor

/-- Exact source presentation through the realized executable factor image.
This is the representation-invariant alphabet needed by closure: two ambient
witnesses with the same compiled factor have the same transition relation,
and neither representative nor target is retained in the code. -/
noncomputable def sourceLocalLayerSerialRootedInteractionFactorPresentationAt
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :=
  RootedLetterPresentation.ofFiniteImage
    (fun witness =>
      sourceLocalLayerSerialRootedInteractionFactorTransition
        (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext witness).factor)
    (fun witness =>
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal
        caps coloring web corridor hunique offset hnext hnextNext witness).factor)
    (by
      intro left right heq
      exact
        sourceLocalLayerSerialRootedInteraction_factorTransition_invariant
          graphData minimal caps coloring web corridor hunique offset hnext
            hnextNext heq)

/-- Soundness: every compatible source witness executes through its canonical
realized factor code from the represented source to the represented target. -/
theorem sourceLocalLayerSerialRootedInteraction_factorCodedTransition
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
    let step := sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext witness
    (sourceLocalLayerSerialRootedInteractionFactorPresentationAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext
    ).codedTransition
      ((sourceLocalLayerSerialRootedInteractionFactorPresentationAt graphData
        minimal caps coloring web corridor hunique offset hnext hnextNext).code
          witness) step.source step.target := by
  classical
  dsimp only
  rw [
    ← RootedLetterPresentation.rawTransition_eq_codedTransition
      (sourceLocalLayerSerialRootedInteractionFactorPresentationAt graphData
        minimal caps coloring web corridor hunique offset hnext hnextNext)
      witness]
  exact
    sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt_successor_exact
      graphData minimal caps coloring web corridor hunique offset hnext hnextNext
        witness.1.1.1 witness.1.1.2
        (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
          offset witness.1.2)
        witness.2
        (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
          corridor hunique offset witness.1.2)

set_option maxHeartbeats 800000 in
/-- Completeness of the realized alphabet: every canonical factor code has a
compatible literal representative whose raw transition is its coded
transition. -/
theorem sourceLocalLayerSerialRootedInteraction_factorCode_hasRepresentative
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
    (letter : SourceLocalLayerSerialRootedInteractionRealizedFactorAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext) :
    ∃ witness : SourceLocalLayerSerialRootedInteractionRealizationAt graphData
        caps coloring web corridor hunique offset hnext,
      (sourceLocalLayerSerialRootedInteractionFactorPresentationAt graphData
        minimal caps coloring web corridor hunique offset hnext hnextNext).code
          witness = letter ∧
      (sourceLocalLayerSerialRootedInteractionFactorPresentationAt graphData
        minimal caps coloring web corridor hunique offset hnext hnextNext
      ).rawTransition witness =
        (sourceLocalLayerSerialRootedInteractionFactorPresentationAt graphData
          minimal caps coloring web corridor hunique offset hnext hnextNext
        ).codedTransition letter := by
  classical
  let presentation :=
    sourceLocalLayerSerialRootedInteractionFactorPresentationAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext
  let witness := presentation.representative letter
  refine ⟨witness, presentation.representative_code letter, ?_⟩
  have hinvariant := presentation.rawTransition_eq_codedTransition witness
  rw [presentation.representative_code letter] at hinvariant
  exact hinvariant

/-- A realized step has no transitions other than its recorded endpoint pair.
The executable middle conjunct is discharged by source exactness. -/
theorem sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition_iff
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
      caps coloring web corridor hunique offset hnext)
    (source target : SourceLocalLayerSerialRootedInteractionState) :
    let step := sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext witness
    step.transition source target ↔
      source = step.source ∧ target = step.target := by
  classical
  dsimp only
  let step := sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData
    minimal caps coloring web corridor hunique offset hnext hnextNext witness
  constructor
  · rintro ⟨hsource, _hsuccessor, htarget⟩
    exact ⟨hsource, htarget⟩
  · rintro ⟨hsource, htarget⟩
    subst source
    subst target
    exact sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition
      graphData minimal caps coloring web corridor hunique offset hnext
        hnextNext witness

private theorem sourceLocalLayerSerialRootedInteractionRealizedStepAt_localFactor_heq
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
    (left right : SourceLocalLayerSerialRootedInteractionRealizationAt graphData
      caps coloring web corridor hunique offset hnext)
    (hcell : left.1.2 = right.1.2) :
    HEq
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext left).factor.localFactor
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).factor.localFactor := by
  classical
  rcases left with ⟨⟨leftPrefix, leftCell⟩, hleftCompatible⟩
  rcases right with ⟨⟨rightPrefix, rightCell⟩, hrightCompatible⟩
  dsimp only at hcell
  subst rightCell
  simp only [sourceLocalLayerSerialRootedInteractionRealizedStepAt,
    sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt,
    sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt,
    sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt]
  apply heq_of_eq
  congr 1
  funext step
  apply StrandColor.toColor_injective
  rw [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt_edgeColor,
    sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt_edgeColor]

private theorem boundedCorridorCutProfile_eq_of_count_eq_of_profile_heq
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    {left right :
      GoertzelV24BoundaryProfileFiniteState.BoundedCorridorCutProfile
        crossingEdgeCount terminalCount faceFragmentBound}
    (hcount : left.faceFragmentCount = right.faceFragmentCount)
    (hprofile : HEq left.profile right.profile) :
    left = right := by
  cases left with
  | mk leftCount leftProfile =>
      cases right with
      | mk rightCount rightProfile =>
          cases hcount
          cases hprofile
          rfl

private theorem regionalTrackedEdgeGraph_eq_of_eq_on_region
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (RS : RotationSystem Vertex Edge) (region : Finset Edge)
    (leftColor rightColor : Edge → Color)
    (heq : ∀ edge, edge ∈ region → leftColor edge = rightColor edge)
    (first second : Color) :
    regionalTrackedEdgeGraph RS region leftColor first second =
      regionalTrackedEdgeGraph RS region rightColor first second := by
  ext left right
  simp only [regionalTrackedEdgeGraph, RotationSystem.trackedEdgeGraph]
  constructor
  · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
    exact ⟨⟨hadj, heq left hleft ▸ hleftTracked,
      heq right hright ▸ hrightTracked⟩, hleft, hright⟩
  · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
    exact ⟨⟨hadj, (heq left hleft).symm ▸ hleftTracked,
      (heq right hright).symm ▸ hrightTracked⟩, hleft, hright⟩

set_option maxHeartbeats 800000 in
/-- Every field of the rooted interaction state observes its colour function
only on the terminal input region named by that state. -/
private theorem sourceLocalLayerSerialRootedInteractionStateForColorAt_eq_of_eq_on_terminal
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
    (leftColor rightColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hleftCrossing : ∀ step,
      leftColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (hrightCrossing : ∀ step,
      rightColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (heq : ∀ edge, edge ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset →
        leftColor edge = rightColor edge) :
    sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal caps
        coloring web corridor hunique offset hnext leftColor hleftCrossing =
      sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal caps
        coloring web corridor hunique offset hnext rightColor hrightCrossing := by
  classical
  apply rootedInteractionState_ext
  · apply rootedCumulativeState_ext
    · apply coloredCumulativeState_ext
      · change terminalInputBoundedProfileForColorAt corridor hunique offset
            leftColor hleftCrossing =
          terminalInputBoundedProfileForColorAt corridor hunique offset
            rightColor hrightCrossing
        unfold terminalInputBoundedProfileForColorAt
        congr 1
        apply GraphCorridorCutData.regionalProfile_eq_of_eq_on_region
          (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset)
          (sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion corridor
            hunique offset)
        exact heq
      · change sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
            graphData caps coloring web corridor hunique offset leftColor =
          sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
            graphData caps coloring web corridor hunique offset rightColor
        unfold sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
        funext pair
        rw [regionalTrackedEdgeGraph_eq_of_eq_on_region _ _ _ _ heq]
      · rfl
      · change sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring
            web corridor hunique offset
              (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                offset) leftColor =
          sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
            corridor hunique offset
              (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                offset) rightColor
        funext slot
        unfold sourceLocalLayerSerialCarrierColorCodeAt
        cases hslot : sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData
            caps coloring web corridor hunique offset slot with
        | none => simp only [Option.bind_none]
        | some edge =>
            by_cases hedge : edge.1 ∈
                sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                  offset
            · simp only [Option.bind_some, hedge, if_true,
                heq edge.1 hedge]
            · simp only [Option.bind_some, hedge, if_false]
      · rfl
    · change sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
          graphData minimal caps coloring web corridor hunique offset leftColor =
        sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
          graphData minimal caps coloring web corridor hunique offset rightColor
      unfold sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
      dsimp only
      congr 1
      funext pair
      exact regionalTrackedEdgeGraph_eq_of_eq_on_region _ _ _ _ heq _ _
  · simp only [sourceLocalLayerSerialRootedInteractionStateForColorAt]
    congr 1
    funext pair
    exact regionalTrackedEdgeGraph_eq_of_eq_on_region _ _ _ _ heq _ _
  · simp only [sourceLocalLayerSerialRootedInteractionStateForColorAt]
    funext slot
    simp only [sourceLocalLayerSerialTrackedInteractionColorCodeAt]
    split <;> rename_i hlive
    · split <;> rename_i hregion
      · exact congrArg some (heq _ hregion)
      · rfl
    · rfl
  · apply heq_of_eq
    rfl
  · rfl
  · apply heq_of_eq
    rfl

/-- Equality of rooted states reads back equality of the represented prefix
colours at every live interaction coordinate in the active prefix region. -/
private theorem sourceLocalLayerSerialRootedInteractionStateForColorAt_color_eq
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
    (leftColor rightColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hleftCrossing : ∀ step,
      leftColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (hrightCrossing : ∀ step,
      rightColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (hstate :
      sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
          caps coloring web corridor hunique offset hnext leftColor
            hleftCrossing =
        sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
          caps coloring web corridor hunique offset hnext rightColor
            hrightCrossing)
    (edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (hcarrier : edge ∈
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext)
    (hregion : edge ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) :
    leftColor edge = rightColor edge := by
  classical
  let carrier :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let hcard : carrier.card ≤ 49 :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique offset hnext
  let live : Fin carrier.card := carrierCoordinate carrier ⟨edge, hcarrier⟩
  have hcode := congrArg
    (fun state : SourceLocalLayerSerialRootedInteractionState =>
      state.interactionColorCode (Fin.castLE hcard live)) hstate
  change sourceLocalLayerSerialTrackedInteractionColorCodeAt carrier hcard
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        leftColor (Fin.castLE hcard live) =
    sourceLocalLayerSerialTrackedInteractionColorCodeAt carrier hcard
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        rightColor (Fin.castLE hcard live) at hcode
  rw [sourceLocalLayerSerialTrackedInteractionColorCodeAt_live,
    sourceLocalLayerSerialTrackedInteractionColorCodeAt_live] at hcode
  have hedge : ((carrierCoordinate carrier).symm live).1 = edge := by
    exact congrArg Subtype.val ((carrierCoordinate carrier).symm_apply_apply
      ⟨edge, hcarrier⟩)
  rw [hedge] at hcode
  simp only [hregion, if_true, Option.some.injEq] at hcode
  exact hcode

/-- Equal rooted prefix receipts, one common literal Cell colouring, and equal
four-role rebase colours determine the splice on every active edge of the
finite rebase collar.  Values at inactive named collar edges are deliberately
irrelevant. -/
private theorem sourceLocalLayerSerialCellSplicedColorAt_eq_on_active_collar
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
    (leftPrefix rightPrefix :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hleftPrefix : ∀ edge, leftPrefix edge ≠ 0)
    (hrightPrefix : ∀ edge, rightPrefix edge ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0)
    (hsource :
      sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
          caps coloring web corridor hunique offset hnext leftPrefix
            (fun step => hleftPrefix
              ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
                offset).crossingEdge step)) =
        sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
          caps coloring web corridor hunique offset hnext rightPrefix
            (fun step => hrightPrefix
              ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
                offset).crossingEdge step)))
    (hrole :
      (fun role => strandColorOfNonzero
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          leftPrefix cellColor
          (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
            role))
        (sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
          corridor hunique offset hnext leftPrefix cellColor hleftPrefix hcell
            role)) =
      (fun role => strandColorOfNonzero
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          rightPrefix cellColor
          (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
            role))
        (sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
          corridor hunique offset hnext rightPrefix cellColor hrightPrefix hcell
            role)))
    (edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (hcollar : edge ∈
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext)
    (hactive : edge ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor
      hunique (sourceLocalLayerNextOffset offset hnext)) :
    sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset leftPrefix
        cellColor edge =
      sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset rightPrefix
        cellColor edge := by
  classical
  by_cases hswitch : edge ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext
  · rcases (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique
      offset hnext edge).1 hswitch with ⟨role, hroleEdge⟩
    have hroleValue := congrFun hrole role
    have hcolorValue := congrArg StrandColor.toColor hroleValue
    simpa [hroleEdge, strandColorOfNonzero_toColor] using hcolorValue
  · have hpre : edge ∈
        sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset :=
      (sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
        corridor hunique offset hnext edge hswitch).2 hactive
    rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
      hunique offset] at hpre
    by_cases hcellRegion : edge ∈
        sourceLocalLayerCellRegionAt corridor hunique offset
    · simp [sourceLocalLayerSerialCellSplicedColorAt, hcellRegion]
    · have hold : edge ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset := by
        exact (Finset.mem_union.mp hpre).resolve_right hcellRegion
      have hinteraction : edge ∈
          sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext := by
        exact Finset.mem_union_right _ hcollar
      have hpref :=
        sourceLocalLayerSerialRootedInteractionStateForColorAt_color_eq graphData
          minimal caps coloring web corridor hunique offset hnext leftPrefix
            rightPrefix (fun step => hleftPrefix _) (fun step => hrightPrefix _)
              hsource edge hinteraction hold
      simpa [sourceLocalLayerSerialCellSplicedColorAt, hcellRegion] using hpref

/-- The tracked rebase factor extracted from a witness depends on the prefix
representative only through the rooted source and the four rebase-role colors.
The literal Cell supplies the other active collar colors. -/
theorem sourceLocalLayerSerialRootedInteractionRealizedStepAt_trackedRebase_eq
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
    (left right : SourceLocalLayerSerialRootedInteractionRealizationAt graphData
      caps coloring web corridor hunique offset hnext)
    (hcell : left.1.2 = right.1.2)
    (hsource :
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext left).source =
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).source)
    (hrole :
      ((sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext left).factor
          ).rebaseLetter.outputCode.tracked.roleColor =
      ((sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).factor
          ).rebaseLetter.outputCode.tracked.roleColor) :
    ((sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext left).factor
        ).trackedRolling.rebase =
      ((sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).factor
          ).trackedRolling.rebase := by
  classical
  rcases left with ⟨⟨leftPrefix, leftCell⟩, hleftCompatible⟩
  rcases right with ⟨⟨rightPrefix, rightCell⟩, hrightCompatible⟩
  dsimp only at hcell
  subst rightCell
  let cellColor := sourceLocalLayerCellLiteralColorAt caps coloring web corridor
    hunique offset leftCell
  have hcellPositive : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0 :=
    sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web corridor
      hunique offset leftCell
  have hactive : ∀ edge, edge ∈
        sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
          hnext →
      edge ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) →
      sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          leftPrefix.1 cellColor edge =
        sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          rightPrefix.1 cellColor edge := by
    intro edge hcollar hregion
    apply sourceLocalLayerSerialCellSplicedColorAt_eq_on_active_collar graphData
      minimal caps coloring web corridor hunique offset hnext leftPrefix.1
        rightPrefix.1 leftPrefix.2 rightPrefix.2 cellColor hcellPositive
    · simpa [sourceLocalLayerSerialRootedInteractionRealizedStepAt] using hsource
    · simpa [sourceLocalLayerSerialRootedInteractionRealizedStepAt,
        sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt,
        finiteBoolSupportLetterForColorAt,
        finiteBoolOutputLetterCodeForColorAt, successorTrackedStateForColorAt,
        cellColor, hcellPositive] using hrole
    · exact hcollar
    · exact hregion
  have hlocal : ∀ pair,
      localTrackedGraphForColorAt corridor hunique offset hnext
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            leftPrefix.1 cellColor) pair =
        localTrackedGraphForColorAt corridor hunique offset hnext
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            rightPrefix.1 cellColor) pair := by
    intro pair
    exact localTrackedGraphForColorAt_eq_of_eq_on_active_collar corridor hunique
      offset hnext _ _ hactive pair
  have hrebase :
      sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal caps coloring
          web corridor hunique offset hnext
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              leftPrefix.1 cellColor) =
        sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal caps coloring
          web corridor hunique offset hnext
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              rightPrefix.1 cellColor) := by
    unfold sourceLocalLayerSerialTrackedRebaseFactorAt
    simp_rw [hlocal]
  change
    sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal caps coloring
        web corridor hunique offset hnext
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            leftPrefix.1 cellColor) =
      sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal caps coloring
        web corridor hunique offset hnext
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            rightPrefix.1 cellColor)
  exact hrebase

private theorem sourceLocalLayerSerialRootedInteractionRealizedStepAt_cellOutput_eq
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
    (left right : SourceLocalLayerSerialRootedInteractionRealizationAt graphData
      caps coloring web corridor hunique offset hnext)
    (hcell : left.1.2 = right.1.2)
    (hsource :
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext left).source =
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).source) :
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext left).factor.cellOutput =
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext right).factor.cellOutput := by
  classical
  let leftStep :=
    sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext left
  let rightStep :=
    sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext right
  have hleftSupport : leftStep.factor.supportsBool leftStep.source = true := by
    simpa [leftStep, sourceLocalLayerSerialRootedInteractionRealizedStepAt] using
      (sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt_supportsBool
        graphData minimal caps coloring web corridor hunique offset hnext hnextNext
          left.1.1.1 left.1.1.2
          (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
            offset left.1.2) left.2
          (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
            corridor hunique offset left.1.2))
  have hrightSupport : rightStep.factor.supportsBool rightStep.source = true := by
    simpa [rightStep, sourceLocalLayerSerialRootedInteractionRealizedStepAt] using
      (sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt_supportsBool
        graphData minimal caps coloring web corridor hunique offset hnext hnextNext
          right.1.1.1 right.1.1.2
          (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
            offset right.1.2) right.2
          (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
            corridor hunique offset right.1.2))
  rw [SourceLocalLayerSerialRootedInteractionRollingCellFactor.supportsBool,
    Bool.and_eq_true, Bool.and_eq_true] at hleftSupport hrightSupport
  have hlocal :=
    sourceLocalLayerSerialRootedInteractionRealizedStepAt_localFactor_heq
      graphData minimal caps coloring web corridor hunique offset hnext hnextNext
        left right hcell
  have hlocalEq : leftStep.factor.localFactor =
      rightStep.factor.localFactor := eq_of_heq hlocal
  have hcount : leftStep.factor.cellOutput.faceFragmentCount =
      rightStep.factor.cellOutput.faceFragmentCount := by rfl
  have hroot : leftStep.source = rightStep.source := hsource
  change leftStep.factor.cellOutput = rightStep.factor.cellOutput
  apply boundedCorridorCutProfile_eq_of_count_eq_of_profile_heq hcount
  cases hcount
  apply heq_of_eq
  exact sourceLocalLayerSerialCellPhysicalSupportsBool_output_unique
    rightStep.source.toSourceLocalLayerSerialColoredCumulativeState
      leftStep.factor.cellOutput.faceFragmentCount
      leftStep.factor.cellOutput.profile rightStep.factor.cellOutput.profile
      rightStep.factor.localFactor
      (by simpa [hroot, hlocalEq] using hleftSupport.1.1)
      hrightSupport.1.1

/-- The exact non-tautological smaller-quotient obligation.  Besides the
rooted source and literal Cell, it retains the four colors exposed by the
boundary rebase.  Those colors cannot in general be read from the current root:
a newly exposed role may lie outside its active prefix region. -/
def SourceLocalLayerSerialRootedInteractionTargetCongruentAt
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) : Prop :=
  ∀ left right : SourceLocalLayerSerialRootedInteractionRealizationAt
      graphData caps coloring web corridor hunique offset hnext,
    left.1.2 = right.1.2 →
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext left).source =
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).source →
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext left).factor.rebaseLetter.outputCode.tracked.roleColor =
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).factor.rebaseLetter.outputCode.tracked.roleColor →
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext left).target =
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).target

/-- The smaller quotient key: current rooted state, literal Cell, and exactly
the four rebase-role colors which may be newly exposed.  Neither the ambient
prefix representative nor the resulting target is retained. -/
structure SourceLocalLayerSerialRootedInteractionQuotientKeyAt
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
    (hnext : offset.val + 1 < blockLength - 3) where
  source : SourceLocalLayerSerialRootedInteractionState
  cell : SourceLocalLayerCellLiteralOpenTaitColoring corridor hunique
    (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)
  rebaseRoleColor :
    SourceLocalLayerBoundaryRebaseRole → StrandColor

noncomputable instance sourceLocalLayerSerialRootedInteractionQuotientKeyAtDecidableEq
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
    DecidableEq (SourceLocalLayerSerialRootedInteractionQuotientKeyAt graphData
      minimal caps coloring web corridor hunique offset hnext) :=
  Classical.decEq _

/-- Forget a witness representative while retaining precisely the information
allowed in the quotient alphabet. -/
noncomputable def sourceLocalLayerSerialRootedInteractionQuotientKeyAt
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
    SourceLocalLayerSerialRootedInteractionQuotientKeyAt graphData minimal caps
      coloring web corridor hunique offset hnext where
  source :=
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext witness).source
  cell := witness.1.2
  rebaseRoleColor :=
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext witness).factor
        |>.rebaseLetter.outputCode.tracked.roleColor

/-- Target congruence is exactly sufficient to make the raw witness transition
invariant under the smaller `(rooted source, literal Cell, role colors)`
quotient. -/
theorem sourceLocalLayerSerialRootedInteraction_transition_invariant_of_targetCongruent
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
    (hcongruent : SourceLocalLayerSerialRootedInteractionTargetCongruentAt
      graphData minimal caps coloring web corridor hunique offset hnext
        hnextNext)
    {left right : SourceLocalLayerSerialRootedInteractionRealizationAt graphData
      caps coloring web corridor hunique offset hnext}
    (hkey : sourceLocalLayerSerialRootedInteractionQuotientKeyAt graphData
        minimal caps coloring web corridor hunique offset hnext hnextNext left =
      sourceLocalLayerSerialRootedInteractionQuotientKeyAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right) :
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext left).transition =
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext right).transition := by
  classical
  have hsource := congrArg
    SourceLocalLayerSerialRootedInteractionQuotientKeyAt.source hkey
  have hcell := congrArg
    SourceLocalLayerSerialRootedInteractionQuotientKeyAt.cell hkey
  have hrole := congrArg
    SourceLocalLayerSerialRootedInteractionQuotientKeyAt.rebaseRoleColor hkey
  have htarget := hcongruent left right hcell hsource hrole
  funext source target
  apply propext
  constructor
  · intro htransition
    have hendpoints :=
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          hnextNext left source target).1 htransition
    apply
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          hnextNext right source target).2
    exact ⟨hendpoints.1.trans hsource, hendpoints.2.trans htarget⟩
  · intro htransition
    have hendpoints :=
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          hnextNext right source target).1 htransition
    apply
      (sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          hnextNext left source target).2
    exact ⟨hendpoints.1.trans hsource.symm, hendpoints.2.trans htarget.symm⟩

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRealizableTransition

end Mettapedia.GraphTheory.FourColor
