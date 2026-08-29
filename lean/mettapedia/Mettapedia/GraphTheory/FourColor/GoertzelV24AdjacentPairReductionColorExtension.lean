import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairReduction
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientOneZeroFlow
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutTaitSplice

/-!
# Extending compatible four-port colourings across a square reduction

The adjacent-pair reduction API previously supplied only the restriction
direction: a Tait colouring of a paired square reduction restricts to a Tait
colouring of the four-defect graph with the corresponding paired boundary
word.  This file proves the converse.

The construction uses the canonical one-zero ambient chain.  Its central
edge is the unique zero edge, while every dart retained by the square
reduction has a nonzero colour and the three colours at each retained vertex
are proper.  Compatibility of the four-port word says exactly that the two
old cut edges identified into each new seam have equal colours.  The generic
ordered-splice descent therefore produces the required Tait colouring.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourDefectBoundary
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrderedCutTaitSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SeamArcAmbientFace
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance reductionExtensionGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance reductionExtensionRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  oneZeroRetainedVertexSetFintype first second

local instance reductionExtensionRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  oneZeroRetainedVertexSetDecidableEq first second

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem extension_retainedEdgeToAmbientEdge_ne_centralEdge
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    retainedEdgeToAmbientEdge data edge ≠ centralEdge data := by
  intro heq
  have hfirst : data.firstVertex ∈
      ((retainedEdgeToAmbientEdge data edge).1 : Sym2 V) := by
    rw [heq]
    change data.firstVertex ∈ (centralEdgeValue data : Sym2 V)
    simp [GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue]
  rw [retainedEdgeToAmbientEdge_val] at hfirst
  rcases Sym2.mem_map.mp hfirst with ⟨retained, _hmem, hvalue⟩
  exact retained.2.1 hvalue

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem extension_retainedEdgeToAmbientEdge_ne_boundaryEdge
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (port : Fin 4) :
    retainedEdgeToAmbientEdge data edge ≠ boundaryEdge data port := by
  intro heq
  have hdeletedMem : data.boundaryDeletedVertex port ∈
      ((retainedEdgeToAmbientEdge data edge).1 : Sym2 V) := by
    rw [heq]
    change data.boundaryDeletedVertex port ∈
      (data.boundaryEdgeValue port : Sym2 V)
    rw [data.boundaryEdgeValue_eq]
    simp
  rw [retainedEdgeToAmbientEdge_val] at hdeletedMem
  rcases Sym2.mem_map.mp hdeletedMem with
    ⟨retained, _hretainedMem, hvalue⟩
  fin_cases port
  · exact retained.2.1 (by
      simpa [GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex]
        using hvalue)
  · exact retained.2.1 (by
      simpa [GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex]
        using hvalue)
  · exact retained.2.2 (by
      simpa [GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex]
        using hvalue)
  · exact retained.2.2 (by
      simpa [GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex]
        using hvalue)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem extension_retainedEdgeToAmbientEdge_isRetained
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    IsRetainedAmbientEdge data (retainedEdgeToAmbientEdge data edge) :=
  isRetainedAmbientEdge_of_ne data (retainedEdgeToAmbientEdge data edge)
    (by
      intro hvalue
      exact extension_retainedEdgeToAmbientEdge_ne_centralEdge data edge
        (Subtype.ext hvalue))
    (by
      intro hvalue
      exact extension_retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 0
        (Subtype.ext hvalue))
    (by
      intro hvalue
      exact extension_retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 1
        (Subtype.ext hvalue))
    (by
      intro hvalue
      exact extension_retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 2
        (Subtype.ext hvalue))
    (by
      intro hvalue
      exact extension_retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 3
        (Subtype.ext hvalue))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem extension_ambientEdgeToRetainedEdge_leftInverse
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    ambientEdgeToRetainedEdge data (retainedEdgeToAmbientEdge data edge)
        (extension_retainedEdgeToAmbientEdge_isRetained data edge) = edge := by
  apply data.retainedEdgeToAmbientEdge_injective
  exact retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge data
    (retainedEdgeToAmbientEdge data edge)
    (extension_retainedEdgeToAmbientEdge_isRetained data edge)

/-- The one-zero ambient chain is literally the deletion coloring on every
old retained edge. -/
@[simp] theorem oneZeroAmbientChain_reductionOldEdge
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    oneZeroAmbientChain data C (retainedEdgeToAmbientEdge data edge) =
      C edge := by
  rw [oneZeroAmbientChain_retained data C
    (retainedEdgeToAmbientEdge data edge)
    (extension_retainedEdgeToAmbientEdge_isRetained data edge),
    extension_ambientEdgeToRetainedEdge_leftInverse]

/-- The one-zero ambient chain agrees on the two old cut edges that become a
new seam precisely when the deletion word is compatible with that square
pairing. -/
theorem oneZeroAmbientChain_cutColors
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    (step : Fin 2) :
    oneZeroAmbientChain data C (data.leftCrossing side step) =
      oneZeroAmbientChain data C (data.rightCrossing side step) := by
  rw [SquareReductionSide.compatible_iff_pair_colors] at hcompatible
  simpa [leftCrossing, rightCrossing] using hcompatible step

/-- At retained darts the one-zero chain is proper.  The central zero edge
cannot meet a retained vertex, and all other incidences are exactly those of
the coloured induced deletion. -/
theorem oneZeroAmbientChain_proper_on_retainedDarts
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {left right : (data.rootedRotationSystem graphData).D}
    (hleft : deletedRegionKeep data.deletedVertices
      ((data.rootedRotationSystem graphData).vertOf left))
    (hright : deletedRegionKeep data.deletedVertices
      ((data.rootedRotationSystem graphData).vertOf right))
    (hvertex : (data.rootedRotationSystem graphData).vertOf left =
      (data.rootedRotationSystem graphData).vertOf right)
    (hne : left ≠ right) :
    oneZeroAmbientChain data C
        ((data.rootedRotationSystem graphData).edgeOf left) ≠
      oneZeroAmbientChain data C
        ((data.rootedRotationSystem graphData).edgeOf right) := by
  let RS := data.rootedRotationSystem graphData
  have hedgeNe : RS.edgeOf left ≠ RS.edgeOf right := by
    intro hedges
    apply hne
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf left)
    · simp [RotationSystem.dartsAt]
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change RS.vertOf left = RS.vertOf right at hvertex
        exact hvertex.symm⟩
    · exact hedges
  have hleftMem : RS.vertOf left ∈ ((RS.edgeOf left).1 : Sym2 V) := by
    apply (mem_simpleGraphRotationSystem_endpoints_iff
      (data.rootedGraphData graphData) (RS.edgeOf left) (RS.vertOf left)).1
    apply RS.mem_endpoints_iff.2
    exact ⟨left, RS.mem_dartsOn.2 rfl, rfl⟩
  have hrightMem : RS.vertOf left ∈ ((RS.edgeOf right).1 : Sym2 V) := by
    apply (mem_simpleGraphRotationSystem_endpoints_iff
      (data.rootedGraphData graphData) (RS.edgeOf right) (RS.vertOf left)).1
    apply RS.mem_endpoints_iff.2
    exact ⟨right, RS.mem_dartsOn.2 rfl, hvertex.symm⟩
  apply oneZeroAmbientChain_ne_of_distinct_at_retainedVertex data
    hcubic C hC (RS.vertOf left)
  · have hretained :
        (data.rootedRotationSystem graphData).vertOf left ∈
          retainedVertexSet data.firstVertex data.secondVertex := by
      change left.toProd.1 ∈ retainedVertexSet data.firstVertex data.secondVertex
      change ¬ left.toProd.1 ∈ data.deletedVertices at hleft
      simpa [deletedVertices] using hleft
    exact hretained
  · exact hleftMem
  · exact hrightMem
  · exact hedgeNe

/-- Every retained dart receives a nonzero value from the one-zero chain. -/
theorem oneZeroAmbientChain_nonzero_on_retainedDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (dart : (data.rootedRotationSystem graphData).D)
    (hkeep : deletedRegionKeep data.deletedVertices
      ((data.rootedRotationSystem graphData).vertOf dart)) :
    oneZeroAmbientChain data C
        ((data.rootedRotationSystem graphData).edgeOf dart) ≠ 0 := by
  let RS := data.rootedRotationSystem graphData
  apply oneZeroAmbientChain_ne_zero_of_ne_central data hcubic C hC
  intro hedge
  have hmem : RS.vertOf dart ∈ ((RS.edgeOf dart).1 : Sym2 V) := by
    apply (mem_simpleGraphRotationSystem_endpoints_iff
      (data.rootedGraphData graphData) (RS.edgeOf dart) (RS.vertOf dart)).1
    apply RS.mem_endpoints_iff.2
    exact ⟨dart, RS.mem_dartsOn.2 rfl, rfl⟩
  have hretained : (data.rootedRotationSystem graphData).vertOf dart ∈
      retainedVertexSet data.firstVertex data.secondVertex := by
    change dart.toProd.1 ∈ retainedVertexSet data.firstVertex data.secondVertex
    change ¬ dart.toProd.1 ∈ data.deletedVertices at hkeep
    simpa [deletedVertices] using hkeep
  apply centralEdge_not_mem_at_retainedVertex data (RS.vertOf dart) hretained
  rw [hedge] at hmem
  exact hmem

/-- Extend a compatible Tait colouring of the induced four-defect graph to
the selected planar paired reduction. -/
def reductionExtensionColoring
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C)) :
    (data.reductionRotationSystem graphData side).EdgeColoring Color := by
  let RS := data.rootedRotationSystem graphData
  let keep := deletedRegionKeep data.deletedVertices
  let dartColor := orderedCutDartColor RS keep
    (data.leftCrossing side) (data.rightCrossing side)
    (oneZeroAmbientChain data C)
  apply (data.reductionRewiredDartSystem graphData side).descendedColoring
    dartColor
  · exact orderedCutDartColor_alpha RS keep
      (data.leftCrossing side) (data.rightCrossing side)
      (data.leftCrosses graphData side) (data.rightCrosses graphData side)
      (data.leftCrossing_injective side)
      (data.rightCrossing_injective side)
      (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
      (data.outer_retained graphData) (oneZeroAmbientChain data C)
      (data.oneZeroAmbientChain_cutColors C side hcompatible)
  · intro left right hvertex hne
    apply data.oneZeroAmbientChain_proper_on_retainedDarts graphData hcubic C hC
    · exact keep_matchedPartUnderlyingDart RS keep
        (orderedCut (data.leftCrossing side))
        (orderedCut (data.rightCrossing side)) left
    · exact keep_matchedPartUnderlyingDart RS keep
        (orderedCut (data.leftCrossing side))
        (orderedCut (data.rightCrossing side)) right
    · exact congrArg Subtype.val hvertex
    · exact (matchedPartUnderlyingDart_injective RS keep
        (orderedCut (data.leftCrossing side))
        (orderedCut (data.rightCrossing side))
        (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)).ne hne

/-- On every old edge, the canonical cap extension is exactly the original
deletion coloring. -/
@[simp] theorem reductionExtensionColoring_reductionEdgeOfDeletedEdge
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    data.reductionExtensionColoring graphData hcubic C hC side hcompatible
        (data.reductionEdgeOfDeletedEdge graphData side edge) =
      C edge := by
  let RS := data.rootedRotationSystem graphData
  let keep := deletedRegionKeep data.deletedVertices
  let dartColor := orderedCutDartColor RS keep
    (data.leftCrossing side) (data.rightCrossing side)
    (oneZeroAmbientChain data C)
  have hAlpha : ∀ dart,
      dartColor ((data.reductionRewiredDartSystem graphData side).alpha dart) =
        dartColor dart :=
    orderedCutDartColor_alpha RS keep
      (data.leftCrossing side) (data.rightCrossing side)
      (data.leftCrosses graphData side) (data.rightCrosses graphData side)
      (data.leftCrossing_injective side)
      (data.rightCrossing_injective side)
      (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
      (data.outer_retained graphData) (oneZeroAmbientChain data C)
      (data.oneZeroAmbientChain_cutColors C side hcompatible)
  change (data.reductionRewiredDartSystem graphData side).descendedEdgeColor
      dartColor (data.reductionEdgeOfDeletedEdge graphData side edge) = C edge
  rw [show data.reductionEdgeOfDeletedEdge graphData side edge =
      (data.reductionRewiredDartSystem graphData side).edgeOf
        (Sum.inl (data.retainedEdgeInternalDart graphData edge)) by rfl]
  rw [GoertzelV24RotationSpliceConstructor.RewiredDartSystem.descendedEdgeColor_edgeOf
    (data.reductionRewiredDartSystem graphData side) dartColor hAlpha]
  change oneZeroAmbientChain data C
      ((data.rootedRotationSystem graphData).edgeOf
        (data.retainedEdgeInternalDart graphData edge).1.1) = C edge
  rw [data.retainedEdgeInternalDart_edgeOf graphData edge,
    oneZeroAmbientChain_reductionOldEdge]

/-- Extending through a compatible paired cap and then forgetting its two
seams is the identity. -/
@[simp] theorem reductionDeletedColoring_reductionExtensionColoring
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C)) :
    data.reductionDeletedColoring graphData side
        (data.reductionExtensionColoring graphData hcubic C hC side hcompatible) =
      C := by
  apply DFunLike.ext _ _
  intro edge
  exact data.reductionExtensionColoring_reductionEdgeOfDeletedEdge
    graphData hcubic C hC side hcompatible edge

/-- The compatible extension is a genuine nowhere-zero Tait colouring. -/
theorem reductionExtensionColoring_isTait
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C)) :
    (data.reductionRotationSystem graphData side).IsTaitEdgeColoring
      (data.reductionExtensionColoring graphData hcubic C hC side hcompatible) := by
  let RS := data.rootedRotationSystem graphData
  let keep := deletedRegionKeep data.deletedVertices
  let dartColor := orderedCutDartColor RS keep
    (data.leftCrossing side) (data.rightCrossing side)
    (oneZeroAmbientChain data C)
  apply (data.reductionRewiredDartSystem graphData side).descendedColoring_isTait
    dartColor
  · exact orderedCutDartColor_alpha RS keep
      (data.leftCrossing side) (data.rightCrossing side)
      (data.leftCrosses graphData side) (data.rightCrosses graphData side)
      (data.leftCrossing_injective side)
      (data.rightCrossing_injective side)
      (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
      (data.outer_retained graphData) (oneZeroAmbientChain data C)
      (data.oneZeroAmbientChain_cutColors C side hcompatible)
  · intro left right hvertex hne
    apply data.oneZeroAmbientChain_proper_on_retainedDarts graphData hcubic C hC
    · exact keep_matchedPartUnderlyingDart RS keep
        (orderedCut (data.leftCrossing side))
        (orderedCut (data.rightCrossing side)) left
    · exact keep_matchedPartUnderlyingDart RS keep
        (orderedCut (data.leftCrossing side))
        (orderedCut (data.rightCrossing side)) right
    · exact congrArg Subtype.val hvertex
    · exact (matchedPartUnderlyingDart_injective RS keep
        (orderedCut (data.leftCrossing side))
        (orderedCut (data.rightCrossing side))
        (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)).ne hne
  · intro dart
    apply data.oneZeroAmbientChain_nonzero_on_retainedDart
      graphData hcubic C hC
    exact keep_matchedPartUnderlyingDart RS keep
      (orderedCut (data.leftCrossing side))
      (orderedCut (data.rightCrossing side)) dart

/-- The colour put on a cap seam is exactly the missing boundary colour at
its left port.  Thus the extension constructor records the four-port word on
the two new seam edges, rather than merely producing some Tait colouring. -/
@[simp] theorem reductionExtensionColoring_reductionSeamEdge_left
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    (step : Fin 2) :
    data.reductionExtensionColoring graphData hcubic C hC side hcompatible
        (data.reductionSeamEdge graphData side step) =
      data.degreeTwoBoundaryData.colorWord C (side.leftPort step) := by
  have hseam := data.degreeTwoBoundaryColorWord_leftPort_eq_reductionSeamColor
    graphData hcubic side
    (data.reductionExtensionColoring graphData hcubic C hC side hcompatible)
    (data.reductionExtensionColoring_isTait
      graphData hcubic C hC side hcompatible) step
  rw [data.reductionDeletedColoring_reductionExtensionColoring
    graphData hcubic C hC side hcompatible] at hseam
  exact hseam.symm

/-- The symmetric right-port form of
`reductionExtensionColoring_reductionSeamEdge_left`. -/
@[simp] theorem reductionExtensionColoring_reductionSeamEdge_right
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    (step : Fin 2) :
    data.reductionExtensionColoring graphData hcubic C hC side hcompatible
        (data.reductionSeamEdge graphData side step) =
      data.degreeTwoBoundaryData.colorWord C (side.rightPort step) := by
  have hseam := data.degreeTwoBoundaryColorWord_rightPort_eq_reductionSeamColor
    graphData hcubic side
    (data.reductionExtensionColoring graphData hcubic C hC side hcompatible)
    (data.reductionExtensionColoring_isTait
      graphData hcubic C hC side hcompatible) step
  rw [data.reductionDeletedColoring_reductionExtensionColoring
    graphData hcubic C hC side hcompatible] at hseam
  exact hseam.symm

/-- Paired-reduction colourability is equivalent to realization of the
corresponding compatible four-port word. -/
theorem reductionTaitColorable_iff_exists_deletedColoring_compatible
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : SquareReductionSide) :
    RotationSystemTaitColorable (data.reductionRotationSystem graphData side) ↔
      ∃ C : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C ∧
        side.Compatible (data.degreeTwoBoundaryData.colorWord C) := by
  constructor
  · exact data.exists_deletedColoring_compatible_of_reductionTaitColorable
      graphData hcubic side
  · rintro ⟨C, hC, hcompatible⟩
    exact ⟨data.reductionExtensionColoring graphData hcubic C hC side hcompatible,
      data.reductionExtensionColoring_isTait graphData hcubic C hC side hcompatible⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

/-! Publication-facing alias. -/

alias GoertzelV24AdjacentPairReductionColorExtension.reductionTaitColorable_iff_exists_deletedColoring_compatible :=
  GoertzelV24AdjacentPairBoundary.AdjacentPairData.reductionTaitColorable_iff_exists_deletedColoring_compatible

end Mettapedia.GraphTheory.FourColor
