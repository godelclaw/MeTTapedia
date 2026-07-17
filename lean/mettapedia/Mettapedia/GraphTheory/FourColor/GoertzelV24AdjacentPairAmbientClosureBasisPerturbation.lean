import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureFlowPerturbation
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFacePairCompatibility

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Replace the standard red and blue coordinates of a color by two
chosen colors. -/
def colorBasisAddHom (first second : Color) : Color →+ Color where
  toFun coefficients := coefficients.1 • first + coefficients.2 • second
  map_zero' := by simp
  map_add' left right := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel

@[simp]
theorem colorBasisAddHom_red (first second : Color) :
    colorBasisAddHom first second red = first := by
  simp [colorBasisAddHom, red]

@[simp]
theorem colorBasisAddHom_blue (first second : Color) :
    colorBasisAddHom first second blue = second := by
  simp [colorBasisAddHom, blue]

@[simp]
theorem colorBasisAddHom_purple (first second : Color) :
    colorBasisAddHom first second purple = first + second := by
  simp [colorBasisAddHom, purple]

/-- Three pairwise distinct nonzero colors are the three nonzero vectors
of `F2²`; consequently each is the sum of the other two. -/
theorem color_eq_add_of_three_distinct_nonzero {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a = b + c := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with
      rfl | rfl | rfl <;>
    simp at hab hac hbc ⊢

/-- Two distinct nonzero colors form a basis of `F2²`. -/
theorem colorBasisAddHom_eq_zero_iff
    {first second : Color} (hfirst : first ≠ 0)
    (hsecond : second ≠ 0) (hdistinct : first ≠ second)
    (color : Color) :
    colorBasisAddHom first second color = 0 ↔ color = 0 := by
  by_cases hzero : color = 0
  · subst color
    simp
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero color hzero with
        rfl | rfl | rfl
    · simp [hfirst]
    · simp [hsecond]
    · simp [add_ne_zero_of_ne hdistinct]

/-- Replacing the two standard coordinates by distinct nonzero colors is
injective. -/
theorem colorBasisAddHom_injective
    {first second : Color} (hfirst : first ≠ 0)
    (hsecond : second ≠ 0) (hdistinct : first ≠ second) :
    Function.Injective (colorBasisAddHom first second) := by
  intro left right heq
  have hzero : colorBasisAddHom first second (left + right) = 0 := by
    rw [map_add, heq]
    exact color_add_self _
  exact (add_eq_zero_iff_eq left right).1
    ((colorBasisAddHom_eq_zero_iff hfirst hsecond hdistinct
      (left + right)).1 hzero)

/-- Additive images of graph flows are graph flows. -/
theorem IsGraphFlow.map_addHom
    {chain : G.edgeSet → Color} (hchain : IsGraphFlow G chain)
    (map : Color →+ Color) :
    IsGraphFlow G (fun edge => map (chain edge)) := by
  intro vertex
  unfold vertexKirchhoffSum
  calc
    ∑ edge ∈ incidentEdgeFinset G vertex, map (chain edge) =
        map (∑ edge ∈ incidentEdgeFinset G vertex, chain edge) := by
      rw [map_sum]
    _ = map 0 := congrArg map (hchain vertex)
    _ = 0 := map_zero map

/-- The pointwise sum of two graph flows is a graph flow. -/
theorem IsGraphFlow.add
    {first second : G.edgeSet → Color}
    (hfirst : IsGraphFlow G first) (hsecond : IsGraphFlow G second) :
    IsGraphFlow G (fun edge => first edge + second edge) := by
  intro vertex
  have hfirstVertex := hfirst vertex
  have hsecondVertex := hsecond vertex
  unfold vertexKirchhoffSum at hfirstVertex hsecondVertex ⊢
  rw [Finset.sum_add_distrib, hfirstVertex, hsecondVertex]
  exact add_zero 0

/-- At a cubic vertex, a graph flow with two distinct zero incident edges
is the all-zero local state. -/
theorem not_isCDLGoodAtVertex_of_isGraphFlow_of_two_zero
    {chain : G.edgeSet → Color} (hflow : IsGraphFlow G chain)
    (vertex : V) (hcubic : (incidentEdgeFinset G vertex).card = 3)
    (first second : G.edgeSet)
    (hfirst : first ∈ incidentEdgeFinset G vertex)
    (hsecond : second ∈ incidentEdgeFinset G vertex)
    (hdistinct : first ≠ second)
    (hfirstZero : chain first = 0) (hsecondZero : chain second = 0) :
    ¬ IsCDLGoodAtVertex G chain vertex := by
  rintro ⟨third, hthird, hthirdNonzero⟩
  have hthirdFirst : third ≠ first := by
    intro heq
    subst third
    exact hthirdNonzero hfirstZero
  have hthirdSecond : third ≠ second := by
    intro heq
    subst third
    exact hthirdNonzero hsecondZero
  have hsubset : ({first, second, third} : Finset G.edgeSet) ⊆
      incidentEdgeFinset G vertex := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirst
    · exact hsecond
    · exact hthird
  have htripleCard :
      ({first, second, third} : Finset G.edgeSet).card = 3 := by
    simp [hdistinct, Ne.symm hthirdFirst, Ne.symm hthirdSecond]
  have hset : ({first, second, third} : Finset G.edgeSet) =
      incidentEdgeFinset G vertex :=
    Finset.eq_of_subset_of_card_le hsubset (by
      rw [hcubic, htripleCard])
  have hvertexFlow := hflow vertex
  unfold vertexKirchhoffSum at hvertexFlow
  rw [← hset] at hvertexFlow
  simp [hfirstZero, hsecondZero, hdistinct] at hvertexFlow
  exact hthirdNonzero hvertexFlow

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The ambient image of an edge of the adjacent-pair deletion is retained. -/
theorem retainedEdgeToAmbientEdge_isRetainedAmbientEdge
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    IsRetainedAmbientEdge data (retainedEdgeToAmbientEdge data edge) :=
  isRetainedAmbientEdge_of_ne data
    (retainedEdgeToAmbientEdge data edge)
    (by
      intro hvalue
      exact retainedEdgeToAmbientEdge_ne_centralEdge data edge
        (Subtype.ext hvalue))
    (by
      intro hvalue
      exact retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 0
        (Subtype.ext hvalue))
    (by
      intro hvalue
      exact retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 1
        (Subtype.ext hvalue))
    (by
      intro hvalue
      exact retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 2
        (Subtype.ext hvalue))
    (by
      intro hvalue
      exact retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 3
        (Subtype.ext hvalue))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Converting a deleted-graph edge to the ambient graph and back is the
identity. -/
@[simp]
theorem ambientEdgeToRetainedEdge_retainedEdgeToAmbientEdge
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    ambientEdgeToRetainedEdge data (retainedEdgeToAmbientEdge data edge)
        (retainedEdgeToAmbientEdge_isRetainedAmbientEdge data edge) = edge := by
  apply data.retainedEdgeToAmbientEdge_injective
  exact retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge data
    (retainedEdgeToAmbientEdge data edge)
    (retainedEdgeToAmbientEdge_isRetainedAmbientEdge data edge)

/-- The singleton-zero ambient chain agrees with the deleted coloring on
every retained edge. -/
@[simp]
theorem oneZeroAmbientChain_retainedEdgeToAmbientEdge
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    oneZeroAmbientChain data C (retainedEdgeToAmbientEdge data edge) =
      C edge := by
  rw [oneZeroAmbientChain_retained data C
    (retainedEdgeToAmbientEdge data edge)
    (retainedEdgeToAmbientEdge_isRetainedAmbientEdge data edge),
    ambientEdgeToRetainedEdge_retainedEdgeToAmbientEdge]

/-- Express the two coordinates of the exact-closure circulation in a
chosen color basis. -/
def CrossCentralExactFaceCutPair.edgeTransferInBasis
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (first second : Color) (edge : G.edgeSet) : Color :=
  colorBasisAddHom first second (pair.edgeTransfer edge)

@[simp]
theorem CrossCentralExactFaceCutPair.edgeTransferInBasis_apply
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (first second : Color) (edge : G.edgeSet) :
    pair.edgeTransferInBasis first second edge =
      colorBasisAddHom first second (pair.edgeTransfer edge) :=
  rfl

/-- A rebased exact-closure transfer remains a graph circulation. -/
theorem CrossCentralExactFaceCutPair.edgeTransferInBasis_isGraphFlow
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (first second : Color) :
    IsGraphFlow G (pair.edgeTransferInBasis first second) :=
  (pair.edgeTransfer_isGraphFlow minimal).map_addHom
    (colorBasisAddHom first second)

theorem CrossCentralExactFaceCutPair.edgeTransferInBasis_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (first second : Color) :
    pair.edgeTransferInBasis first second (centralEdge data) =
      first + second := by
  rw [pair.edgeTransferInBasis_apply,
    pair.edgeTransfer_centralEdge minimal]
  exact colorBasisAddHom_purple first second

theorem CrossCentralExactFaceCutPair.edgeTransferInBasis_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (first second : Color) :
    pair.edgeTransferInBasis first second
        (retainedEdgeToAmbientEdge data cross) = first + second := by
  rw [pair.edgeTransferInBasis_apply,
    pair.edgeTransfer_retainedCross minimal]
  exact colorBasisAddHom_purple first second

/-- Perturb the singleton-zero ambient chain by an exact closure transfer
whose two coordinates are expressed in the route-color basis. -/
def CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet) : Color :=
  oneZeroAmbientChain data C edge +
    pair.edgeTransferInBasis first second edge

@[simp]
theorem CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation_apply
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet) :
    pair.oneZeroClosureBasisPerturbation C first second edge =
      oneZeroAmbientChain data C edge +
        pair.edgeTransferInBasis first second edge :=
  rfl

/-- Route-basis closure perturbation preserves Kirchhoff's law. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation_isGraphFlow
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second : Color) :
    IsGraphFlow G
      (pair.oneZeroClosureBasisPerturbation C first second) := by
  let hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  exact (oneZeroAmbientChain_isGraphFlow data hcubic C hC hsame).add
    (pair.edgeTransferInBasis_isGraphFlow minimal first second)

/-- A route-basis perturbation vanishes precisely when the reconstructed
and rebased closure values agree. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation_eq_zero_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet) :
    pair.oneZeroClosureBasisPerturbation C first second edge = 0 ↔
      oneZeroAmbientChain data C edge =
        pair.edgeTransferInBasis first second edge := by
  exact add_eq_zero_iff_eq _ _

/-- Local CDL-goodness of a route-basis perturbation is a mismatch on an
incident edge. -/
theorem CrossCentralExactFaceCutPair.isCDLGoodAtVertex_oneZeroClosureBasisPerturbation_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (vertex : V) :
    IsCDLGoodAtVertex G
        (pair.oneZeroClosureBasisPerturbation C first second) vertex ↔
      ∃ edge ∈ incidentEdgeFinset G vertex,
        oneZeroAmbientChain data C edge ≠
          pair.edgeTransferInBasis first second edge := by
  constructor
  · rintro ⟨edge, hedge, hnonzero⟩
    refine ⟨edge, hedge, ?_⟩
    intro heq
    apply hnonzero
    rw [pair.oneZeroClosureBasisPerturbation_apply, heq]
    exact color_add_self _
  · rintro ⟨edge, hedge, hne⟩
    exact ⟨edge, hedge, add_ne_zero_of_ne hne⟩

/-- A route-basis perturbation is CDL-bad exactly when its two summands
agree on every incident edge. -/
theorem CrossCentralExactFaceCutPair.not_isCDLGoodAtVertex_oneZeroClosureBasisPerturbation_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (vertex : V) :
    ¬ IsCDLGoodAtVertex G
        (pair.oneZeroClosureBasisPerturbation C first second) vertex ↔
      ∀ edge ∈ incidentEdgeFinset G vertex,
        oneZeroAmbientChain data C edge =
          pair.edgeTransferInBasis first second edge := by
  rw [pair.isCDLGoodAtVertex_oneZeroClosureBasisPerturbation_iff]
  push Not
  exact Iff.rfl

/-- The restored central edge receives the sum of the two basis colors. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) :
    pair.oneZeroClosureBasisPerturbation C first second
        (centralEdge data) = first + second := by
  rw [pair.oneZeroClosureBasisPerturbation_apply,
    oneZeroAmbientChain_central,
    pair.edgeTransferInBasis_centralEdge minimal]
  exact zero_add _

/-- Distinct basis colors make both restored central-edge endpoints
CDL-good after rebasing. -/
theorem CrossCentralExactFaceCutPair.isCDLGoodAtVertex_oneZeroClosureBasisPerturbation_of_mem_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (hdistinct : first ≠ second)
    (vertex : V) (hvertex : vertex ∈ centralEdgeValue data) :
    IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C first second) vertex := by
  refine ⟨centralEdge data, ?_, ?_⟩
  · simpa [incidentEdgeFinset] using hvertex
  · rw [pair.oneZeroClosureBasisPerturbation_centralEdge minimal]
    exact add_ne_zero_of_ne hdistinct

/-- If the selected cross edge has the sum color, the rebased perturbation
moves the distinguished zero from the restored central edge to that cross
edge. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color)
    (hcross : C cross = first + second) :
    pair.oneZeroClosureBasisPerturbation C first second
        (retainedEdgeToAmbientEdge data cross) = 0 := by
  rw [pair.oneZeroClosureBasisPerturbation_apply,
    oneZeroAmbientChain_retainedEdgeToAmbientEdge,
    pair.edgeTransferInBasis_retainedCross minimal,
    hcross]
  exact color_add_self _

/-- When the retained supports are exactly a unique cross's prefix and
suffix splices, both strict outgoing cross arms carry the second rebased
closure coordinate. -/
theorem CrossCentralExactFaceCutPair.edgeTransferInBasis_crossExitEdges
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a firstColor secondColor : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a firstColor firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a secondColor secondLeft secondRight)
    (haFirst : a ≠ firstColor) (haSecond : a ≠ secondColor)
    (hcolors : firstColor ≠ secondColor)
    (site : first.CrossSite second)
    (hunique : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge ∈ first.ambientPath.support →
      edge ∈ second.ambientPath.support → edge = site.1)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (first.crossSplice second site).support.map Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (first.crossSuffixSplice second site).support.map Subtype.val) :
    pair.edgeTransferInBasis firstColor secondColor
        (retainedEdgeToAmbientEdge data
          ((first.firstSuffixFromCrossSite second site).getVert 1)) =
          secondColor ∧
      pair.edgeTransferInBasis firstColor secondColor
        (retainedEdgeToAmbientEdge data
          ((first.secondSuffixFromCrossSite second site).getVert 1)) =
          secondColor := by
  let firstExit :=
    (first.firstSuffixFromCrossSite second site).getVert 1
  let secondExit :=
    (first.secondSuffixFromCrossSite second site).getVert 1
  have hfirstTail : firstExit ∈
      (first.firstSuffixFromCrossSite second site).support.tail := by
    simpa only [firstExit] using
      first.firstCrossExitEdge_mem_tail_support
        second haFirst hcolors site
  have hsecondTail : secondExit ∈
      (first.secondSuffixFromCrossSite second site).support.tail := by
    simpa only [secondExit] using
      first.secondCrossExitEdge_mem_tail_support
        second haSecond hcolors site
  have hfirstSuffixSupport : firstExit ∈
      (first.crossSuffixSplice second site).support := by
    rw [EvenKempePortPath.crossSuffixSplice,
      SimpleGraph.Walk.support_append]
    apply List.mem_append.mpr
    left
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      List.mem_of_mem_tail hfirstTail
  have hsecondSuffixSupport : secondExit ∈
      (first.crossSuffixSplice second site).support := by
    rw [EvenKempePortPath.crossSuffixSplice,
      SimpleGraph.Walk.support_append]
    apply List.mem_append.mpr
    exact Or.inr hsecondTail
  have hfirstNotPrefixSupport : firstExit ∉
      (first.crossSplice second site).support := by
    intro hprefix
    exact (List.disjoint_left.mp
      (first.firstSuffix_tail_disjoint_crossSplice_support
        second site hunique)) hfirstTail hprefix
  have hsecondNotPrefixSupport : secondExit ∉
      (first.crossSplice second site).support := by
    intro hprefix
    exact (List.disjoint_left.mp
      (first.secondSuffix_tail_disjoint_crossSplice_support
        second site hunique)) hsecondTail hprefix
  have hfirstNotPrefix :
      (retainedEdgeToAmbientEdge data firstExit).1 ∉
        (data.oppositePortClosure pair.prefixTrail).edges := by
    intro hmem
    have htrail :=
      (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data pair.prefixTrail firstExit).1 hmem
    rw [hprefixEdges] at htrail
    rcases List.mem_map.mp htrail with ⟨source, hsource, hvalue⟩
    have hsourceEq : source = firstExit := Subtype.ext hvalue
    exact hfirstNotPrefixSupport (hsourceEq ▸ hsource)
  have hsecondNotPrefix :
      (retainedEdgeToAmbientEdge data secondExit).1 ∉
        (data.oppositePortClosure pair.prefixTrail).edges := by
    intro hmem
    have htrail :=
      (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data pair.prefixTrail secondExit).1 hmem
    rw [hprefixEdges] at htrail
    rcases List.mem_map.mp htrail with ⟨source, hsource, hvalue⟩
    have hsourceEq : source = secondExit := Subtype.ext hvalue
    exact hsecondNotPrefixSupport (hsourceEq ▸ hsource)
  have hfirstTrail : firstExit.1 ∈ pair.suffixTrail.edges := by
    rw [hsuffixEdges]
    exact List.mem_map.mpr ⟨firstExit, hfirstSuffixSupport, rfl⟩
  have hsecondTrail : secondExit.1 ∈ pair.suffixTrail.edges := by
    rw [hsuffixEdges]
    exact List.mem_map.mpr ⟨secondExit, hsecondSuffixSupport, rfl⟩
  have hfirstSuffix :
      (retainedEdgeToAmbientEdge data firstExit).1 ∈
        (data.alternateOppositePortClosure pair.suffixTrail).edges := by
    rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.alternateOppositePortClosure,
      SimpleGraph.Walk.edges_append,
      List.mem_append]
    exact Or.inl
      ((retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data pair.suffixTrail firstExit).2 hfirstTrail)
  have hsecondSuffix :
      (retainedEdgeToAmbientEdge data secondExit).1 ∈
        (data.alternateOppositePortClosure pair.suffixTrail).edges := by
    rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.alternateOppositePortClosure,
      SimpleGraph.Walk.edges_append,
      List.mem_append]
    exact Or.inl
      ((retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data pair.suffixTrail secondExit).2 hsecondTrail)
  constructor
  · rw [pair.edgeTransferInBasis_apply,
      (pair.edgeTransfer_eq_blue_iff minimal
        (retainedEdgeToAmbientEdge data firstExit)).2
          ⟨hfirstNotPrefix, hfirstSuffix⟩,
      colorBasisAddHom_blue]
  · rw [pair.edgeTransferInBasis_apply,
      (pair.edgeTransfer_eq_blue_iff minimal
        (retainedEdgeToAmbientEdge data secondExit)).2
          ⟨hsecondNotPrefix, hsecondSuffix⟩,
      colorBasisAddHom_blue]

/-- In the reversed endpoint-pairing state, route-basis perturbation melts
the first entry endpoint of the cross while leaving its opposite endpoint
CDL-good. -/
theorem CrossCentralExactFaceCutPair.reversedCross_entry_bad_exit_good
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a firstColor secondColor : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a firstColor firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a secondColor secondLeft secondRight)
    (haFirst : a ≠ firstColor) (haSecond : a ≠ secondColor)
    (hcolors : firstColor ≠ secondColor)
    (site : first.CrossSite second)
    (hunique : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge ∈ first.ambientPath.support →
      edge ∈ second.ambientPath.support → edge = site.1)
    (hpairing : first.crossPairingBit second haFirst haSecond hcolors site =
      false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (first.crossSplice second site).support.map Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (first.crossSuffixSplice second site).support.map Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (hsum : a = firstColor + secondColor) :
    (¬ IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C firstColor secondColor)
      (first.firstCrossEntryVertex second haFirst hcolors site).1) ∧
      IsCDLGoodAtVertex G
        (pair.oneZeroClosureBasisPerturbation C firstColor secondColor)
        (first.firstCrossExitDart second haFirst hcolors site).fst.1 := by
  let entry := first.firstCrossEntryVertex second haFirst hcolors site
  let exit := (first.firstCrossExitDart second haFirst hcolors site).fst
  let firstExitEdge :=
    (first.firstSuffixFromCrossSite second site).getVert 1
  let secondExitEdge :=
    (first.secondSuffixFromCrossSite second site).getVert 1
  change (¬ IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C firstColor secondColor)
        entry.1) ∧
    IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C firstColor secondColor)
        exit.1
  have hflow : IsGraphFlow G
      (pair.oneZeroClosureBasisPerturbation C firstColor secondColor) :=
    pair.oneZeroClosureBasisPerturbation_isGraphFlow minimal C hC hsame
      firstColor secondColor
  let hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hsiteColor : C site.1 = a :=
    first.color_eq_first_of_crossSite second hcolors site
  have hfirstExitColor : C firstExitEdge = firstColor := by
    simpa only [firstExitEdge] using
      first.firstCrossExitEdge_color second haFirst hcolors site
  have hsecondExitColor : C secondExitEdge = secondColor := by
    simpa only [secondExitEdge] using
      first.secondCrossExitEdge_color second haSecond hcolors site
  have htransfers := pair.edgeTransferInBasis_crossExitEdges minimal
    first second haFirst haSecond hcolors site hunique hprefixEdges
      hsuffixEdges
  have hfirstTransfer : pair.edgeTransferInBasis firstColor secondColor
      (retainedEdgeToAmbientEdge data firstExitEdge) = secondColor := by
    simpa only [firstExitEdge] using htransfers.1
  have hsecondTransfer : pair.edgeTransferInBasis firstColor secondColor
      (retainedEdgeToAmbientEdge data secondExitEdge) = secondColor := by
    simpa only [secondExitEdge] using htransfers.2
  have hcrossZero :
      pair.oneZeroClosureBasisPerturbation C firstColor secondColor
        (retainedEdgeToAmbientEdge data site.1) = 0 :=
    pair.oneZeroClosureBasisPerturbation_retainedCross minimal C
      firstColor secondColor (hsiteColor.trans hsum)
  have hfirstExitValue :
      pair.oneZeroClosureBasisPerturbation C firstColor secondColor
        (retainedEdgeToAmbientEdge data firstExitEdge) =
          firstColor + secondColor := by
    rw [pair.oneZeroClosureBasisPerturbation_apply,
      oneZeroAmbientChain_retainedEdgeToAmbientEdge,
      hfirstExitColor, hfirstTransfer]
  have hfirstExitNonzero :
      pair.oneZeroClosureBasisPerturbation C firstColor secondColor
        (retainedEdgeToAmbientEdge data firstExitEdge) ≠ 0 := by
    rw [hfirstExitValue]
    exact add_ne_zero_of_ne hcolors
  have hsecondExitZero :
      pair.oneZeroClosureBasisPerturbation C firstColor secondColor
        (retainedEdgeToAmbientEdge data secondExitEdge) = 0 := by
    rw [pair.oneZeroClosureBasisPerturbation_apply,
      oneZeroAmbientChain_retainedEdgeToAmbientEdge,
      hsecondExitColor, hsecondTransfer]
    exact color_add_self _
  have hreversed :=
    first.secondCrossDart_eq_firstCrossDart_symm_of_pairing_false
      second haFirst haSecond hcolors site hpairing
  have hsecondExitBase :
      (first.secondCrossExitDart second haSecond hcolors site).fst =
        entry := by
    calc
      (first.secondCrossExitDart second haSecond hcolors site).fst =
          (first.secondCrossDart second haSecond hcolors site).snd := rfl
      _ = ((first.firstCrossDart second haFirst hcolors site).symm).snd :=
        congrArg (fun dart ↦ dart.snd) hreversed
      _ = entry := rfl
  have hcrossEntryRetained : entry ∈ (site.1.1 : Sym2 _) := by
    simpa only [entry] using
      first.firstCrossEntryVertex_mem_site second haFirst hcolors site
  have hcrossEntryAmbient : entry.1 ∈
      ((retainedEdgeToAmbientEdge data site.1).1 : Sym2 V) := by
    rw [retainedEdgeToAmbientEdge_val]
    exact Sym2.mem_map.mpr ⟨entry, hcrossEntryRetained, rfl⟩
  have hcrossIncident : retainedEdgeToAmbientEdge data site.1 ∈
      incidentEdgeFinset G entry.1 := by
    simpa [incidentEdgeFinset] using hcrossEntryAmbient
  have hsecondExitBaseRetained : entry ∈
      (secondExitEdge.1 : Sym2 _) := by
    rw [← hsecondExitBase]
    change
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨0, first.secondSuffixFromCrossSite_length_pos
            second haSecond hcolors site⟩ ∈
        (((first.secondSuffixFromCrossSite second site).getVert 1).1 :
          Sym2 _)
    have hmem :=
      (first.secondSuffixFromCrossSite second site)
        |>.lineGraphJunctionAt_mem_right
          ⟨0, first.secondSuffixFromCrossSite_length_pos
            second haSecond hcolors site⟩
    simpa only [Nat.zero_add] using hmem
  have hsecondExitAmbient : entry.1 ∈
      ((retainedEdgeToAmbientEdge data secondExitEdge).1 : Sym2 V) := by
    rw [retainedEdgeToAmbientEdge_val]
    exact Sym2.mem_map.mpr ⟨entry, hsecondExitBaseRetained, rfl⟩
  have hsecondExitIncident :
      retainedEdgeToAmbientEdge data secondExitEdge ∈
        incidentEdgeFinset G entry.1 := by
    simpa [incidentEdgeFinset] using hsecondExitAmbient
  have hcrossNeSecondExit : retainedEdgeToAmbientEdge data site.1 ≠
      retainedEdgeToAmbientEdge data secondExitEdge := by
    intro hambient
    have hretained : site.1 = secondExitEdge :=
      data.retainedEdgeToAmbientEdge_injective hambient
    have hcolor := congrArg C hretained
    rw [hsiteColor, hsecondExitColor] at hcolor
    exact haSecond hcolor
  have hfirstExitBaseRetained : exit ∈
      (firstExitEdge.1 : Sym2 _) := by
    change
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨0, first.firstSuffixFromCrossSite_length_pos
            second haFirst hcolors site⟩ ∈
        (((first.firstSuffixFromCrossSite second site).getVert 1).1 :
          Sym2 _)
    have hmem :=
      (first.firstSuffixFromCrossSite second site)
        |>.lineGraphJunctionAt_mem_right
          ⟨0, first.firstSuffixFromCrossSite_length_pos
            second haFirst hcolors site⟩
    simpa only [Nat.zero_add] using hmem
  have hfirstExitAmbient : exit.1 ∈
      ((retainedEdgeToAmbientEdge data firstExitEdge).1 : Sym2 V) := by
    rw [retainedEdgeToAmbientEdge_val]
    exact Sym2.mem_map.mpr ⟨exit, hfirstExitBaseRetained, rfl⟩
  have hfirstExitIncident : retainedEdgeToAmbientEdge data firstExitEdge ∈
      incidentEdgeFinset G exit.1 := by
    simpa [incidentEdgeFinset] using hfirstExitAmbient
  constructor
  · exact not_isCDLGoodAtVertex_of_isGraphFlow_of_two_zero
      hflow entry.1 (hcubic entry.1)
      (retainedEdgeToAmbientEdge data site.1)
      (retainedEdgeToAmbientEdge data secondExitEdge)
      hcrossIncident hsecondExitIncident hcrossNeSecondExit
      hcrossZero hsecondExitZero
  · exact ⟨retainedEdgeToAmbientEdge data firstExitEdge,
      hfirstExitIncident, hfirstExitNonzero⟩

/-- A rejected singleton `bc` cross has exactly the reversed local
endpoint state needed by the route-basis perturbation: its first entry
melts and the opposite endpoint remains CDL-good. -/
theorem EvenKempeFusionLens.bcCrossExactPair_entry_bad_exit_good
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    (¬ IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C b c)
      (lens01.bRoute.firstCrossEntryVertex lens23.cRoute
        hab hbc site).1) ∧
      IsCDLGoodAtVertex G
        (pair.oneZeroClosureBasisPerturbation C b c)
        (lens01.bRoute.firstCrossExitDart lens23.cRoute
          hab hbc site).fst.1 := by
  have hunique : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge ∈ lens01.bRoute.ambientPath.support →
      edge ∈ lens23.cRoute.ambientPath.support → edge = site.1 := by
    intro edge hfirst hsecond
    exact lens01.bcCrossSite_eq_of_length_le_one lens23 hcount site edge
      hfirst hsecond
  have hpairing : lens01.bRoute.crossPairingBit lens23.cRoute
      hab hac hbc site = false :=
    (crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
      data graphData lens01.bRoute lens23.cRoute hab hac hbc site).1
      (by
        simpa only [EvenKempeFusionLens.bcCrossExitFaceTransferBit] using
          hfalse) |>.1
  have ha : a ≠ 0 := by
    rw [← lens01.bRoute.color_eq_first_of_crossSite
      lens23.cRoute hbc site]
    exact hC site.1
  have hb : b ≠ 0 := by
    rw [← lens01.bRoute.firstCrossExitEdge_color
      lens23.cRoute hab hbc site]
    exact hC ((lens01.bRoute.firstSuffixFromCrossSite
      lens23.cRoute site).getVert 1)
  have hc : c ≠ 0 := by
    rw [← lens01.bRoute.secondCrossExitEdge_color
      lens23.cRoute hac hbc site]
    exact hC ((lens01.bRoute.secondSuffixFromCrossSite
      lens23.cRoute site).getVert 1)
  have hsum : a = b + c :=
    color_eq_add_of_three_distinct_nonzero ha hb hc hab hac hbc
  exact pair.reversedCross_entry_bad_exit_good minimal
    lens01.bRoute lens23.cRoute hab hac hbc site hunique hpairing
      hprefixEdges hsuffixEdges hC hsame hsum

/-- The symmetric rejected singleton `cb` cross melts the first entry of
the `c` route after rebasing to `(c,b)`, while its opposite endpoint stays
CDL-good. -/
theorem EvenKempeFusionLens.cbCrossExactPair_entry_bad_exit_good
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    (¬ IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C c b)
      (lens01.cRoute.firstCrossEntryVertex lens23.bRoute
        hac hbc.symm site).1) ∧
      IsCDLGoodAtVertex G
        (pair.oneZeroClosureBasisPerturbation C c b)
        (lens01.cRoute.firstCrossExitDart lens23.bRoute
          hac hbc.symm site).fst.1 := by
  have hunique : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge ∈ lens01.cRoute.ambientPath.support →
      edge ∈ lens23.bRoute.ambientPath.support → edge = site.1 := by
    intro edge hfirst hsecond
    exact lens01.cbCrossSite_eq_of_length_le_one lens23 hcount site edge
      hfirst hsecond
  have hpairing : lens01.cRoute.crossPairingBit lens23.bRoute
      hac hab hbc.symm site = false :=
    (crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
      data graphData lens01.cRoute lens23.bRoute hac hab hbc.symm site).1
      (by
        simpa only [EvenKempeFusionLens.cbCrossExitFaceTransferBit] using
          hfalse) |>.1
  have ha : a ≠ 0 := by
    rw [← lens01.cRoute.color_eq_first_of_crossSite
      lens23.bRoute hbc.symm site]
    exact hC site.1
  have hc : c ≠ 0 := by
    rw [← lens01.cRoute.firstCrossExitEdge_color
      lens23.bRoute hac hbc.symm site]
    exact hC ((lens01.cRoute.firstSuffixFromCrossSite
      lens23.bRoute site).getVert 1)
  have hb : b ≠ 0 := by
    rw [← lens01.cRoute.secondCrossExitEdge_color
      lens23.bRoute hab hbc.symm site]
    exact hC ((lens01.cRoute.secondSuffixFromCrossSite
      lens23.bRoute site).getVert 1)
  have hsum : a = c + b :=
    color_eq_add_of_three_distinct_nonzero ha hc hb hac hab hbc.symm
  exact pair.reversedCross_entry_bad_exit_good minimal
    lens01.cRoute lens23.bRoute hac hab hbc.symm site hunique hpairing
      hprefixEdges hsuffixEdges hC hsame hsum

private theorem localTaitTriple_contains_standard_basis
    {first second third : Color}
    (hlocal : IsLocalTaitTriple first second third) :
    (first = red ∨ second = red ∨ third = red) ∧
      (first = blue ∨ second = blue ∨ third = blue) := by
  rcases hlocal with ⟨⟨hfirst, hsecond, hthird⟩,
    hfirstSecond, hfirstThird, hsecondThird⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirst with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecond with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero third hthird with
      rfl | rfl | rfl <;>
    simp_all

/-- With distinct basis colors, every CDL-bad vertex of the rebased
perturbation is an endpoint of the selected retained cross edge. -/
theorem CrossCentralExactFaceCutPair.mem_retainedCross_of_not_isCDLGoodAtVertex_oneZeroClosureBasisPerturbation
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (first second : Color) (hdistinct : first ≠ second)
    (vertex : V)
    (hbad : ¬ IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C first second) vertex) :
    vertex ∈ (retainedEdgeToAmbientEdge data cross).1 := by
  let hcubic : ∀ current : V,
      (incidentEdgeFinset G current).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hagree : ∀ edge ∈ incidentEdgeFinset G vertex,
      oneZeroAmbientChain data C edge =
        pair.edgeTransferInBasis first second edge :=
    (pair.not_isCDLGoodAtVertex_oneZeroClosureBasisPerturbation_iff
      C first second vertex).1 hbad
  have hnotCentral : vertex ∉ centralEdgeValue data := by
    intro hcentral
    have hcentralIncident :
        centralEdge data ∈ incidentEdgeFinset G vertex := by
      simpa [incidentEdgeFinset] using hcentral
    have heq := hagree (centralEdge data) hcentralIncident
    rw [oneZeroAmbientChain_central,
      pair.edgeTransferInBasis_centralEdge minimal] at heq
    exact (add_ne_zero_of_ne hdistinct) heq.symm
  rcases Finset.card_eq_three.mp (hcubic vertex) with
    ⟨firstEdge, secondEdge, thirdEdge, hfirstSecond, hfirstThird,
      hsecondThird, hset⟩
  have hfirstIncident : firstEdge ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hsecondIncident : secondEdge ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hthirdIncident : thirdEdge ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hfirstVertex : vertex ∈ (firstEdge.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hfirstIncident
  have hsecondVertex : vertex ∈ (secondEdge.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hsecondIncident
  have hthirdVertex : vertex ∈ (thirdEdge.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hthirdIncident
  have hfirstNeCentral : firstEdge ≠ centralEdge data := by
    intro hedge
    subst firstEdge
    exact hnotCentral hfirstVertex
  have hsecondNeCentral : secondEdge ≠ centralEdge data := by
    intro hedge
    subst secondEdge
    exact hnotCentral hsecondVertex
  have hthirdNeCentral : thirdEdge ≠ centralEdge data := by
    intro hedge
    subst thirdEdge
    exact hnotCentral hthirdVertex
  have hfirstMappedNonzero :
      pair.edgeTransferInBasis first second firstEdge ≠ 0 := by
    rw [← hagree firstEdge hfirstIncident]
    exact oneZeroAmbientChain_ne_zero_of_ne_central
      data hcubic C hC firstEdge hfirstNeCentral
  have hsecondMappedNonzero :
      pair.edgeTransferInBasis first second secondEdge ≠ 0 := by
    rw [← hagree secondEdge hsecondIncident]
    exact oneZeroAmbientChain_ne_zero_of_ne_central
      data hcubic C hC secondEdge hsecondNeCentral
  have hthirdMappedNonzero :
      pair.edgeTransferInBasis first second thirdEdge ≠ 0 := by
    rw [← hagree thirdEdge hthirdIncident]
    exact oneZeroAmbientChain_ne_zero_of_ne_central
      data hcubic C hC thirdEdge hthirdNeCentral
  have hfirstNonzero : pair.edgeTransfer firstEdge ≠ 0 := by
    intro hzero
    apply hfirstMappedNonzero
    simp [CrossCentralExactFaceCutPair.edgeTransferInBasis, hzero]
  have hsecondNonzero : pair.edgeTransfer secondEdge ≠ 0 := by
    intro hzero
    apply hsecondMappedNonzero
    simp [CrossCentralExactFaceCutPair.edgeTransferInBasis, hzero]
  have hthirdNonzero : pair.edgeTransfer thirdEdge ≠ 0 := by
    intro hzero
    apply hthirdMappedNonzero
    simp [CrossCentralExactFaceCutPair.edgeTransferInBasis, hzero]
  have hflowVertex := pair.edgeTransfer_isGraphFlow minimal vertex
  have hlocalKirchhoff : IsLocalKirchhoffTriple
      (pair.edgeTransfer firstEdge) (pair.edgeTransfer secondEdge)
        (pair.edgeTransfer thirdEdge) := by
    unfold vertexKirchhoffSum at hflowVertex
    rw [hset] at hflowVertex
    simpa [IsLocalKirchhoffTriple, hfirstSecond, hfirstThird,
      hsecondThird, add_assoc] using hflowVertex
  have hlocalTait : IsLocalTaitTriple
      (pair.edgeTransfer firstEdge) (pair.edgeTransfer secondEdge)
        (pair.edgeTransfer thirdEdge) :=
    isLocalTaitTriple_of_kirchhoff_nowhereZero hlocalKirchhoff
      ⟨hfirstNonzero, hsecondNonzero, hthirdNonzero⟩
  have hcontains := localTaitTriple_contains_standard_basis hlocalTait
  have hprefix :
      vertex ∈ (data.oppositePortClosure pair.prefixTrail).support := by
    rcases hcontains.1 with hred | hred | hred
    · exact (data.oppositePortClosure pair.prefixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_red_iff minimal firstEdge).1 hred).1
          hfirstVertex
    · exact (data.oppositePortClosure pair.prefixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_red_iff minimal secondEdge).1 hred).1
          hsecondVertex
    · exact (data.oppositePortClosure pair.prefixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_red_iff minimal thirdEdge).1 hred).1
          hthirdVertex
  have hsuffix : vertex ∈
      (data.alternateOppositePortClosure pair.suffixTrail).support := by
    rcases hcontains.2 with hblue | hblue | hblue
    · exact (data.alternateOppositePortClosure pair.suffixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_blue_iff minimal firstEdge).1 hblue).2
          hfirstVertex
    · exact (data.alternateOppositePortClosure pair.suffixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_blue_iff minimal secondEdge).1 hblue).2
          hsecondVertex
    · exact (data.alternateOppositePortClosure pair.suffixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_blue_iff minimal thirdEdge).1 hblue).2
          hthirdVertex
  rcases (pair.mem_both_closure_support_iff minimal hprefixCycle
    hsuffixCycle vertex).1 ⟨hprefix, hsuffix⟩ with hcross | hcentral
  · exact hcross
  · exact False.elim (hnotCentral hcentral)

/-- The finite CDL-bad vertex set of a route-basis perturbation. -/
def CrossCentralExactFaceCutPair.cdlBadVertexFinsetInBasis
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) : Finset V := by
  classical
  exact Finset.univ.filter fun vertex =>
    ¬ IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C first second) vertex

@[simp]
theorem CrossCentralExactFaceCutPair.mem_cdlBadVertexFinsetInBasis_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (vertex : V) :
    vertex ∈ pair.cdlBadVertexFinsetInBasis C first second ↔
      ¬ IsCDLGoodAtVertex G
        (pair.oneZeroClosureBasisPerturbation C first second) vertex := by
  classical
  simp [CrossCentralExactFaceCutPair.cdlBadVertexFinsetInBasis]

/-- If the two cross endpoints are an explicitly bad entry and a good
exit, the localized bad set is exactly the singleton entry. -/
theorem CrossCentralExactFaceCutPair.cdlBadVertexFinsetInBasis_eq_singleton_of_cross_endpoints
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (first second : Color) (hdistinct : first ≠ second)
    (entry exit : V)
    (hcrossEndpoints : (retainedEdgeToAmbientEdge data cross).1 =
      s(entry, exit))
    (hentryBad : ¬ IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C first second) entry)
    (hexitGood : IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C first second) exit) :
    pair.cdlBadVertexFinsetInBasis C first second = {entry} := by
  classical
  ext vertex
  rw [pair.mem_cdlBadVertexFinsetInBasis_iff]
  simp only [Finset.mem_singleton]
  constructor
  · intro hbad
    have hmem :=
      pair.mem_retainedCross_of_not_isCDLGoodAtVertex_oneZeroClosureBasisPerturbation
        minimal hprefixCycle hsuffixCycle C hC first second hdistinct
          vertex hbad
    rw [hcrossEndpoints] at hmem
    rcases (Sym2.mem_iff.mp hmem) with hentry | hexit
    · exact hentry
    · subst vertex
      exact False.elim (hbad hexitGood)
  · rintro rfl
    exact hentryBad

/-- Finset form of the rejected singleton `bc` cross state: after rebasing
to `(b,c)`, exactly the first route's entry endpoint is CDL-bad. -/
theorem EvenKempeFusionLens.cdlBadVertexFinsetInBasis_eq_singleton_of_bcCrossExactPair
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
        Subtype.val)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    pair.cdlBadVertexFinsetInBasis C b c =
      {(lens01.bRoute.firstCrossEntryVertex lens23.cRoute
        hab hbc site).1} := by
  have hlocal := EvenKempeFusionLens.bcCrossExactPair_entry_bad_exit_good
    graphData minimal data lens01 lens23 hab hac hbc hcount site hfalse pair
      hprefixEdges hsuffixEdges hC hsame
  have hcrossEndpoints : (retainedEdgeToAmbientEdge data site.1).1 =
      s((lens01.bRoute.firstCrossEntryVertex lens23.cRoute
          hab hbc site).1,
        (lens01.bRoute.firstCrossExitDart lens23.cRoute
          hab hbc site).fst.1) := by
    rw [retainedEdgeToAmbientEdge_val,
      lens01.bRoute.crossSite_eq_firstEntry_exit
        lens23.cRoute hab hbc site, Sym2.map_mk]
  exact pair.cdlBadVertexFinsetInBasis_eq_singleton_of_cross_endpoints
    minimal hprefixCycle hsuffixCycle C hC b c hbc
      (lens01.bRoute.firstCrossEntryVertex lens23.cRoute hab hbc site).1
      (lens01.bRoute.firstCrossExitDart lens23.cRoute
        hab hbc site).fst.1
      hcrossEndpoints hlocal.1 hlocal.2

/-- Symmetric finset form for a rejected singleton `cb` cross: in the
`(c,b)` basis exactly the first `c`-route entry endpoint is CDL-bad. -/
theorem EvenKempeFusionLens.cdlBadVertexFinsetInBasis_eq_singleton_of_cbCrossExactPair
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
        Subtype.val)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    pair.cdlBadVertexFinsetInBasis C c b =
      {(lens01.cRoute.firstCrossEntryVertex lens23.bRoute
        hac hbc.symm site).1} := by
  have hlocal := EvenKempeFusionLens.cbCrossExactPair_entry_bad_exit_good
    graphData minimal data lens01 lens23 hab hac hbc hcount site hfalse pair
      hprefixEdges hsuffixEdges hC hsame
  have hcrossEndpoints : (retainedEdgeToAmbientEdge data site.1).1 =
      s((lens01.cRoute.firstCrossEntryVertex lens23.bRoute
          hac hbc.symm site).1,
        (lens01.cRoute.firstCrossExitDart lens23.bRoute
          hac hbc.symm site).fst.1) := by
    rw [retainedEdgeToAmbientEdge_val,
      lens01.cRoute.crossSite_eq_firstEntry_exit
        lens23.bRoute hac hbc.symm site, Sym2.map_mk]
  exact pair.cdlBadVertexFinsetInBasis_eq_singleton_of_cross_endpoints
    minimal hprefixCycle hsuffixCycle C hC c b hbc.symm
      (lens01.cRoute.firstCrossEntryVertex lens23.bRoute
        hac hbc.symm site).1
      (lens01.cRoute.firstCrossExitDart lens23.bRoute
        hac hbc.symm site).fst.1
      hcrossEndpoints hlocal.1 hlocal.2

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
