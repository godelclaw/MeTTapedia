import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionPathDichotomy
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedTrail

/-! Realizing a straight singleton companion trail by one Kempe component. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24FramedTrail
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

/-- Common-core line-graph adjacency is preserved by inclusion into the
source adjacent-pair deletion. -/
theorem commonEdgeInSource_lineGraph_adj
    {first second : collar.commonCore.edgeSet}
    (hadjacent : collar.commonCore.lineGraph.Adj first second) :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).lineGraph.Adj
        (collar.commonEdgeInSource first)
        (collar.commonEdgeInSource second) := by
  let embedding := deletedTwoPairsToFirstDeletionEmbedding G
    collar.sourceData.firstVertex collar.sourceData.secondVertex
    collar.targetData.firstVertex collar.targetData.secondVertex
  have hlift :=
    (embedding.toCopy.toLineGraphEmbedding.map_rel_iff).2 hadjacent
  change (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
    collar.sourceData.secondVertex).lineGraph.Adj
      (embedding.mapEdgeSet first) (embedding.mapEdgeSet second)
  convert hlift using 1 <;> apply Subtype.ext <;> rfl

/-- Source common-core colors are definitionally the colors on their source
deletion images. -/
@[simp]
theorem sourceCommonColoring_apply_commonEdgeInSource
    (edge : collar.commonCore.edgeSet) :
    collar.sourceCommonColoring sourceEscape edge =
      sourceEscape.coloring (collar.commonEdgeInSource edge) := rfl

namespace SingletonCompanionTransferPath

variable (transfer : SingletonCompanionTransferPath collar sourceEscape)

/-- Every inhabitant of the attached support-edge subtype occurs in its
canonical edge-retaining word. -/
theorem supportEdge_mem_supportEdgeWord (edge : transfer.SupportEdge) :
    edge ∈ transfer.supportEdgeWord := by
  exact List.mem_attach _ edge

/-- A fixed two-color pattern puts every source support edge in the selected
bicolored vertex set. -/
theorem sourceColor_mem_pair_of_fixedTwoColorPattern
    (companion : Color)
    (hpattern : ∀ edge ∈ transfer.supportEdgeWord,
      (collar.sourceCommonColoring sourceEscape edge.1 =
            crossFaceZeroColor transfer.coordinate ∧
          collar.targetCommonColoring edge.1 = companion) ∨
        (collar.sourceCommonColoring sourceEscape edge.1 = companion ∧
          collar.targetCommonColoring edge.1 =
            crossFaceZeroColor transfer.coordinate))
    (edge : transfer.SupportEdge) :
    collar.sourceCommonColoring sourceEscape edge.1 =
        crossFaceZeroColor transfer.coordinate ∨
      collar.sourceCommonColoring sourceEscape edge.1 = companion := by
  rcases hpattern edge (transfer.supportEdge_mem_supportEdgeWord edge) with
    hsource | htarget
  · exact Or.inl hsource.1
  · exact Or.inr htarget.1

/-- Consecutive edge identities in the singleton word are genuinely adjacent
in the common-core line graph. -/
theorem supportEdgeWord_isChain_lineGraphAdj :
    transfer.supportEdgeWord.IsChain
      (fun first second =>
        collar.commonCore.lineGraph.Adj first.1 second.1) := by
  exact transfer.supportEdgeWord_isChain_transition.imp
    (fun _ _ htransition => htransition.1)

/-- The same ordered trail is a line-graph chain inside the full source
adjacent-pair deletion. -/
theorem supportEdgeWord_isChain_sourceLineGraphAdj :
    transfer.supportEdgeWord.IsChain
      (fun first second =>
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).lineGraph.Adj
            (collar.commonEdgeInSource first.1)
            (collar.commonEdgeInSource second.1)) := by
  exact transfer.supportEdgeWord_isChain_lineGraphAdj.imp
    (fun _ _ hadjacent => collar.commonEdgeInSource_lineGraph_adj hadjacent)

/-- A straight fixed-color singleton trail is contained in one genuine
source Kempe component.  Swapping that component preserves the Tait condition
and agrees with the target coloring on every edge of the trail. -/
theorem exists_sourceKempeComponent_agrees_on_support
    (companion : Color)
    (hcompanionZero : companion ≠ 0)
    (hcompanionDistinguished :
      companion ≠ crossFaceZeroColor transfer.coordinate)
    (hpattern : ∀ edge ∈ transfer.supportEdgeWord,
      (collar.sourceCommonColoring sourceEscape edge.1 =
            crossFaceZeroColor transfer.coordinate ∧
          collar.targetCommonColoring edge.1 = companion) ∨
        (collar.sourceCommonColoring sourceEscape edge.1 = companion ∧
          collar.targetCommonColoring edge.1 =
            crossFaceZeroColor transfer.coordinate)) :
    ∃ K : ((collar.sourceCommonColoring sourceEscape).bicoloredSubgraph
        (crossFaceZeroColor transfer.coordinate) companion).ConnectedComponent,
      (∀ edge ∈ transfer.supportEdgeWord,
        edge.1 ∈ (collar.sourceCommonColoring sourceEscape).kempeComponentSet
          (crossFaceZeroColor transfer.coordinate) companion K) ∧
      IsTaitEdgeColoring collar.commonCore
        ((collar.sourceCommonColoring sourceEscape).swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K) ∧
      collar.commonCore.EdgeKempeStep
        (collar.sourceCommonColoring sourceEscape)
        ((collar.sourceCommonColoring sourceEscape).swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K) ∧
      ∀ edge ∈ transfer.supportEdgeWord,
        (collar.sourceCommonColoring sourceEscape).swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K edge.1 =
          collar.targetCommonColoring edge.1 := by
  let firstEdge :=
    transfer.supportEdgeWord.head transfer.supportEdgeWord_ne_nil
  have hfirstBicolored :
      collar.sourceCommonColoring sourceEscape firstEdge.1 =
          crossFaceZeroColor transfer.coordinate ∨
        collar.sourceCommonColoring sourceEscape firstEdge.1 = companion :=
    transfer.sourceColor_mem_pair_of_fixedTwoColorPattern
      companion hpattern firstEdge
  let K := ((collar.sourceCommonColoring sourceEscape).bicoloredSubgraph
    (crossFaceZeroColor transfer.coordinate) companion).connectedComponentMk
      ⟨firstEdge.1, hfirstBicolored⟩
  have hcomponent : ∀ edge ∈ transfer.supportEdgeWord,
      edge.1 ∈ (collar.sourceCommonColoring sourceEscape).kempeComponentSet
        (crossFaceZeroColor transfer.coordinate) companion K := by
    apply transfer.supportEdgeWord_isChain_lineGraphAdj.induction
      (p := fun edge =>
        edge.1 ∈
          (collar.sourceCommonColoring sourceEscape).kempeComponentSet
            (crossFaceZeroColor transfer.coordinate) companion K)
    · intro first second hadjacent hfirstComponent
      exact (collar.sourceCommonColoring sourceEscape).mem_kempeComponentSet_of_adj
          hfirstComponent hadjacent
          (transfer.sourceColor_mem_pair_of_fixedTwoColorPattern
            companion hpattern second)
    · intro hnonempty
      simpa [K, firstEdge] using
        (collar.sourceCommonColoring sourceEscape).mem_kempeComponentSet_self
          hfirstBicolored
  have hvalidPair : ValidColorPair
      (crossFaceZeroColor transfer.coordinate) companion :=
    ⟨crossFaceZeroColor_ne_zero transfer.coordinate,
      hcompanionZero, Ne.symm hcompanionDistinguished⟩
  refine ⟨K, hcomponent,
    isTaitEdgeColoring_swapOnKempeComponent
      (collar.sourceCommonColoring_isTait sourceEscape) hvalidPair K,
    collar.commonCore.edgeKempeStep_swapOnKempeComponent
      (collar.sourceCommonColoring sourceEscape)
      (crossFaceZeroColor transfer.coordinate) companion K, ?_⟩
  intro edge hedge
  rw [(collar.sourceCommonColoring sourceEscape).swapOnKempeComponent_apply_of_mem
    (hcomponent edge hedge)]
  rcases hpattern edge hedge with hsource | htarget
  · rw [hsource.1, hsource.2]
    exact Equiv.swap_apply_left _ _
  · rw [htarget.1, htarget.2]
    exact Equiv.swap_apply_right _ _

/-- The straight branch of the global dichotomy therefore supplies an actual
single Kempe move whose result agrees with the target on the whole singleton
support trail. -/
theorem exists_sourceKempeComponent_agrees_on_support_of_straight
    (hstraight :
      transfer.supportEdgeWord.IsChain transfer.SupportEdgeStraight) :
    ∃ companion : Color,
      companion ≠ 0 ∧
      companion ≠ crossFaceZeroColor transfer.coordinate ∧
      ∃ K : ((collar.sourceCommonColoring sourceEscape).bicoloredSubgraph
          (crossFaceZeroColor transfer.coordinate) companion).ConnectedComponent,
        (∀ edge ∈ transfer.supportEdgeWord,
          edge.1 ∈
            (collar.sourceCommonColoring sourceEscape).kempeComponentSet
              (crossFaceZeroColor transfer.coordinate) companion K) ∧
        IsTaitEdgeColoring collar.commonCore
          ((collar.sourceCommonColoring sourceEscape).swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K) ∧
        collar.commonCore.EdgeKempeStep
          (collar.sourceCommonColoring sourceEscape)
          ((collar.sourceCommonColoring sourceEscape).swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K) ∧
        ∀ edge ∈ transfer.supportEdgeWord,
          (collar.sourceCommonColoring sourceEscape).swapOnKempeComponent
              (crossFaceZeroColor transfer.coordinate) companion K edge.1 =
            collar.targetCommonColoring edge.1 := by
  rcases transfer.exists_fixedTwoColorPattern_of_straight hstraight with
    ⟨companion, hzero, hdistinguished, hpattern⟩
  exact ⟨companion, hzero, hdistinguished,
    transfer.exists_sourceKempeComponent_agrees_on_support
      companion hzero hdistinguished hpattern⟩

/-- The same fixed trail is realized by one Kempe component in the full
source adjacent-pair deletion, not merely in the common-core restriction.
The resulting source-side coloring is a genuine one-step same-base Kempe
successor and agrees with the target common-core coloring along the trail. -/
theorem exists_sourceDeletionKempeComponent_agrees_on_support
    (companion : Color)
    (hcompanionZero : companion ≠ 0)
    (hcompanionDistinguished :
      companion ≠ crossFaceZeroColor transfer.coordinate)
    (hpattern : ∀ edge ∈ transfer.supportEdgeWord,
      (collar.sourceCommonColoring sourceEscape edge.1 =
            crossFaceZeroColor transfer.coordinate ∧
          collar.targetCommonColoring edge.1 = companion) ∨
        (collar.sourceCommonColoring sourceEscape edge.1 = companion ∧
          collar.targetCommonColoring edge.1 =
            crossFaceZeroColor transfer.coordinate)) :
    ∃ K : (sourceEscape.coloring.bicoloredSubgraph
        (crossFaceZeroColor transfer.coordinate) companion).ConnectedComponent,
      (∀ edge ∈ transfer.supportEdgeWord,
        collar.commonEdgeInSource edge.1 ∈
          sourceEscape.coloring.kempeComponentSet
            (crossFaceZeroColor transfer.coordinate) companion K) ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex)
        (sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K) ∧
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeStep
        sourceEscape.coloring
        (sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K) ∧
      sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K ∈
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeClosure
            sourceEscape.coloring ∧
      sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K ∈
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeClosure
            sourceNormal.recoloring ∧
      sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K ∈
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeClosure
            sourceNormal.profile.coloring ∧
      ∀ edge ∈ transfer.supportEdgeWord,
        sourceEscape.coloring.swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K
              (collar.commonEdgeInSource edge.1) =
          collar.targetCommonColoring edge.1 := by
  let firstEdge :=
    transfer.supportEdgeWord.head transfer.supportEdgeWord_ne_nil
  have hfirstBicolored :
      sourceEscape.coloring (collar.commonEdgeInSource firstEdge.1) =
          crossFaceZeroColor transfer.coordinate ∨
        sourceEscape.coloring (collar.commonEdgeInSource firstEdge.1) =
          companion := by
    simpa only [← collar.sourceCommonColoring_apply_commonEdgeInSource] using
      transfer.sourceColor_mem_pair_of_fixedTwoColorPattern
        companion hpattern firstEdge
  let K := (sourceEscape.coloring.bicoloredSubgraph
    (crossFaceZeroColor transfer.coordinate) companion).connectedComponentMk
      ⟨collar.commonEdgeInSource firstEdge.1, hfirstBicolored⟩
  have hcomponent : ∀ edge ∈ transfer.supportEdgeWord,
      collar.commonEdgeInSource edge.1 ∈
        sourceEscape.coloring.kempeComponentSet
          (crossFaceZeroColor transfer.coordinate) companion K := by
    apply transfer.supportEdgeWord_isChain_sourceLineGraphAdj.induction
      (p := fun edge =>
        collar.commonEdgeInSource edge.1 ∈
          sourceEscape.coloring.kempeComponentSet
            (crossFaceZeroColor transfer.coordinate) companion K)
    · intro first second hadjacent hfirstComponent
      apply sourceEscape.coloring.mem_kempeComponentSet_of_adj
        hfirstComponent hadjacent
      change sourceEscape.coloring (collar.commonEdgeInSource second.1) =
          crossFaceZeroColor transfer.coordinate ∨
        sourceEscape.coloring (collar.commonEdgeInSource second.1) = companion
      rw [← collar.sourceCommonColoring_apply_commonEdgeInSource]
      exact transfer.sourceColor_mem_pair_of_fixedTwoColorPattern
        companion hpattern second
    · intro hnonempty
      simpa [K, firstEdge] using
        sourceEscape.coloring.mem_kempeComponentSet_self hfirstBicolored
  have hvalidPair : ValidColorPair
      (crossFaceZeroColor transfer.coordinate) companion :=
    ⟨crossFaceZeroColor_ne_zero transfer.coordinate,
      hcompanionZero, Ne.symm hcompanionDistinguished⟩
  have hTait : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex)
      (sourceEscape.coloring.swapOnKempeComponent
        (crossFaceZeroColor transfer.coordinate) companion K) :=
    isTaitEdgeColoring_swapOnKempeComponent
      sourceEscape.isTait hvalidPair K
  have hstep :
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeStep
        sourceEscape.coloring
        (sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K) :=
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeKempeStep_swapOnKempeComponent
        sourceEscape.coloring
        (crossFaceZeroColor transfer.coordinate) companion K
  have hreachable :
      sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K ∈
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeClosure
            sourceEscape.coloring :=
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).mem_edgeKempeClosure_of_step
        ((DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).mem_edgeKempeClosure_self
            sourceEscape.coloring) hstep
  have hfromAllEqual :
      sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K ∈
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeClosure
            sourceNormal.recoloring :=
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeKempeClosure_subset_of_mem
        sourceEscape.reachable_from_allEqual hreachable
  have hfromProfile :
      sourceEscape.coloring.swapOnKempeComponent
          (crossFaceZeroColor transfer.coordinate) companion K ∈
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeClosure
            sourceNormal.profile.coloring :=
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeKempeClosure_subset_of_mem
        sourceEscape.reachable_from_profile hreachable
  refine ⟨K, hcomponent, hTait, hstep, hreachable,
    hfromAllEqual, hfromProfile, ?_⟩
  intro edge hedge
  rw [sourceEscape.coloring.swapOnKempeComponent_apply_of_mem
    (hcomponent edge hedge)]
  rcases hpattern edge hedge with hsource | htarget
  · have hsourceColor :
        sourceEscape.coloring (collar.commonEdgeInSource edge.1) =
          crossFaceZeroColor transfer.coordinate := by
      rw [← collar.sourceCommonColoring_apply_commonEdgeInSource]
      exact hsource.1
    rw [hsourceColor, hsource.2]
    exact Equiv.swap_apply_left _ _
  · have hsourceColor :
        sourceEscape.coloring (collar.commonEdgeInSource edge.1) =
          companion := by
      rw [← collar.sourceCommonColoring_apply_commonEdgeInSource]
      exact htarget.1
    rw [hsourceColor, htarget.2]
    exact Equiv.swap_apply_right _ _

/-- Hence the straight branch always produces a full source-deletion Kempe
successor with exact target agreement on the selected common-core trail. -/
theorem exists_sourceDeletionKempeComponent_agrees_on_support_of_straight
    (hstraight :
      transfer.supportEdgeWord.IsChain transfer.SupportEdgeStraight) :
    ∃ companion : Color,
      companion ≠ 0 ∧
      companion ≠ crossFaceZeroColor transfer.coordinate ∧
      ∃ K : (sourceEscape.coloring.bicoloredSubgraph
          (crossFaceZeroColor transfer.coordinate) companion).ConnectedComponent,
        (∀ edge ∈ transfer.supportEdgeWord,
          collar.commonEdgeInSource edge.1 ∈
            sourceEscape.coloring.kempeComponentSet
              (crossFaceZeroColor transfer.coordinate) companion K) ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
            collar.sourceData.secondVertex)
          (sourceEscape.coloring.swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K) ∧
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
            collar.sourceData.secondVertex).EdgeKempeStep
          sourceEscape.coloring
          (sourceEscape.coloring.swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K) ∧
        sourceEscape.coloring.swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K ∈
          (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
            collar.sourceData.secondVertex).EdgeKempeClosure
              sourceEscape.coloring ∧
        sourceEscape.coloring.swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K ∈
          (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
            collar.sourceData.secondVertex).EdgeKempeClosure
              sourceNormal.recoloring ∧
        sourceEscape.coloring.swapOnKempeComponent
            (crossFaceZeroColor transfer.coordinate) companion K ∈
          (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
            collar.sourceData.secondVertex).EdgeKempeClosure
              sourceNormal.profile.coloring ∧
        ∀ edge ∈ transfer.supportEdgeWord,
          sourceEscape.coloring.swapOnKempeComponent
              (crossFaceZeroColor transfer.coordinate) companion K
                (collar.commonEdgeInSource edge.1) =
            collar.targetCommonColoring edge.1 := by
  rcases transfer.exists_fixedTwoColorPattern_of_straight hstraight with
    ⟨companion, hzero, hdistinguished, hpattern⟩
  exact ⟨companion, hzero, hdistinguished,
    transfer.exists_sourceDeletionKempeComponent_agrees_on_support
      companion hzero hdistinguished hpattern⟩

/-- The reusable same-base package carried by a straight singleton trail.
It records the actual component, all three relevant reachability facts, and
the exact cross-base agreement along the selected support. -/
structure SourceDeletionKempeRealization where
  companion : Color
  companion_ne_zero : companion ≠ 0
  companion_ne_distinguished :
    companion ≠ crossFaceZeroColor transfer.coordinate
  component : (sourceEscape.coloring.bicoloredSubgraph
    (crossFaceZeroColor transfer.coordinate) companion).ConnectedComponent
  support_mem_component : ∀ edge ∈ transfer.supportEdgeWord,
    collar.commonEdgeInSource edge.1 ∈
      sourceEscape.coloring.kempeComponentSet
        (crossFaceZeroColor transfer.coordinate) companion component
  isTait : IsTaitEdgeColoring
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex)
    (sourceEscape.coloring.swapOnKempeComponent
      (crossFaceZeroColor transfer.coordinate) companion component)
  oneStep : (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).EdgeKempeStep
    sourceEscape.coloring
    (sourceEscape.coloring.swapOnKempeComponent
      (crossFaceZeroColor transfer.coordinate) companion component)
  reachable_from_escape :
    sourceEscape.coloring.swapOnKempeComponent
        (crossFaceZeroColor transfer.coordinate) companion component ∈
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).EdgeKempeClosure sourceEscape.coloring
  reachable_from_allEqual :
    sourceEscape.coloring.swapOnKempeComponent
        (crossFaceZeroColor transfer.coordinate) companion component ∈
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).EdgeKempeClosure sourceNormal.recoloring
  reachable_from_profile :
    sourceEscape.coloring.swapOnKempeComponent
        (crossFaceZeroColor transfer.coordinate) companion component ∈
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).EdgeKempeClosure
          sourceNormal.profile.coloring
  agrees_on_support : ∀ edge ∈ transfer.supportEdgeWord,
    sourceEscape.coloring.swapOnKempeComponent
        (crossFaceZeroColor transfer.coordinate) companion component
          (collar.commonEdgeInSource edge.1) =
      collar.targetCommonColoring edge.1

namespace SourceDeletionKempeRealization

variable (realization : transfer.SourceDeletionKempeRealization)

/-- The realized source coloring after the selected component swap. -/
noncomputable abbrev coloring :=
  sourceEscape.coloring.swapOnKempeComponent
    (crossFaceZeroColor transfer.coordinate) realization.companion
      realization.component

/-- The four source ports after the selected component swap. -/
noncomputable abbrev boundaryWord : SquareBoundaryWord :=
  collar.sourceData.degreeTwoBoundaryData.colorWord realization.coloring

/-- The two colors selected by the realization form a valid Kempe pair. -/
theorem validColorPair : ValidColorPair
    (crossFaceZeroColor transfer.coordinate) realization.companion :=
  ⟨crossFaceZeroColor_ne_zero transfer.coordinate,
    realization.companion_ne_zero,
    Ne.symm realization.companion_ne_distinguished⟩

/-- The graph-level realization has exactly the finite boundary action of
its set of met source ports. -/
theorem boundaryWord_eq_boundaryKempeSwap :
    realization.boundaryWord =
      boundaryKempeSwap
        (crossFaceZeroColor transfer.coordinate) realization.companion
        (collar.sourceData.degreeTwoBoundaryData.kempePortSupport
          sourceEscape.coloring
          (crossFaceZeroColor transfer.coordinate) realization.companion
          realization.component)
        (collar.sourceData.degreeTwoBoundaryData.colorWord
          sourceEscape.coloring) := by
  exact collar.sourceData.degreeTwoBoundaryData
    |>.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      sourceEscape.coloring realization.validColorPair realization.component

/-- Minimal-counterexample uncolorability leaves only the all-equal or the
canonical adjacent-pair sector after the realized swap. -/
theorem boundary_allEqual_or_adjacent01_23 :
    realization.boundaryWord.AllEqual ∨
      realization.boundaryWord.Adjacent01_23 := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      collar.sourceData hcubic hnotColorable realization.coloring
        realization.isTait
  by_cases hsides :
      SourceDeletionKempeRealization.boundaryWord transfer realization 0 =
        SourceDeletionKempeRealization.boundaryWord transfer realization 2
  · exact Or.inl ⟨hsame.1, hsame.1.symm.trans hsides, hsame.2⟩
  · exact Or.inr ⟨hsame.1, hsame.2, hsides⟩

/-- An adjacent-boundary realization is itself a complete same-base Kempe
escape package for the source fusion normal. -/
noncomputable def toKempeOrbitAdjacentEscape
    (hadjacent : realization.boundaryWord.Adjacent01_23) :
    sourceNormal.KempeOrbitAdjacentEscape where
  coloring := realization.coloring
  isTait := realization.isTait
  boundary_adjacent01_23 := hadjacent
  reachable_from_allEqual := realization.reachable_from_allEqual
  same_kempeClosure_as_allEqual :=
    SimpleGraph.Coloring.kempeClosure_eq_of_mem
      realization.reachable_from_allEqual
  reachable_from_profile := realization.reachable_from_profile

end SourceDeletionKempeRealization

/-- The straight alternative constructs the reusable full-deletion
realization package without any additional hypothesis. -/
theorem nonempty_sourceDeletionKempeRealization_of_straight
    (hstraight :
      transfer.supportEdgeWord.IsChain transfer.SupportEdgeStraight) :
    Nonempty transfer.SourceDeletionKempeRealization := by
  rcases transfer.exists_sourceDeletionKempeComponent_agrees_on_support_of_straight
      hstraight with
    ⟨companion, hzero, hdistinguished, component, hcomponent,
      hTait, hstep, hescape, hallEqual, hprofile, hagrees⟩
  exact ⟨{
    companion := companion
    companion_ne_zero := hzero
    companion_ne_distinguished := hdistinguished
    component := component
    support_mem_component := hcomponent
    isTait := hTait
    oneStep := hstep
    reachable_from_escape := hescape
    reachable_from_allEqual := hallEqual
    reachable_from_profile := hprofile
    agrees_on_support := hagrees }⟩

/-- Thus the straight singleton branch ends in an exact all-equal source
state or re-enters the canonical adjacent Kempe orbit, with the same
realization retaining target agreement along the full support trail. -/
theorem exists_allEqualRealization_or_adjacentEscape_of_straight
    (hstraight :
      transfer.supportEdgeWord.IsChain transfer.SupportEdgeStraight) :
    ∃ realization : transfer.SourceDeletionKempeRealization,
      realization.boundaryWord.AllEqual ∨
        ∃ successor : sourceNormal.KempeOrbitAdjacentEscape,
          successor.coloring = realization.coloring := by
  let realization :=
    Classical.choice
      (transfer.nonempty_sourceDeletionKempeRealization_of_straight hstraight)
  refine ⟨realization, ?_⟩
  rcases realization.boundary_allEqual_or_adjacent01_23 with
    hallEqual | hadjacent
  · exact Or.inl hallEqual
  · exact Or.inr
      ⟨SourceDeletionKempeRealization.toKempeOrbitAdjacentEscape
        transfer realization hadjacent, rfl⟩

end SingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
