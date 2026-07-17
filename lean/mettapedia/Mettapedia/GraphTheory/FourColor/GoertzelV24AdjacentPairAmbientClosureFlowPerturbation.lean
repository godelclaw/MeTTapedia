import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientOneZeroFlow
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFlow

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation
open scoped BigOperators

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Add the paired exact-closure circulation to the singleton-zero chain
reconstructed from an adjacent-pair deletion. -/
def CrossCentralExactFaceCutPair.oneZeroClosurePerturbation
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (edge : G.edgeSet) : Color :=
  oneZeroAmbientChain data C edge + pair.edgeTransfer edge

@[simp]
theorem CrossCentralExactFaceCutPair.oneZeroClosurePerturbation_apply
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (edge : G.edgeSet) :
    pair.oneZeroClosurePerturbation C edge =
      oneZeroAmbientChain data C edge + pair.edgeTransfer edge :=
  rfl

private theorem isGraphFlow_add
    {first second : G.edgeSet → Color}
    (hfirst : IsGraphFlow G first) (hsecond : IsGraphFlow G second) :
    IsGraphFlow G (fun edge => first edge + second edge) := by
  intro vertex
  have hfirstVertex := hfirst vertex
  have hsecondVertex := hsecond vertex
  unfold vertexKirchhoffSum at hfirstVertex hsecondVertex
  unfold vertexKirchhoffSum
  rw [Finset.sum_add_distrib, hfirstVertex, hsecondVertex]
  exact add_zero 0

/-- The closure perturbation remains a graph flow. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosurePerturbation_isGraphFlow
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
          data.degreeTwoBoundaryData.colorWord C 3) :
    IsGraphFlow G (pair.oneZeroClosurePerturbation C) := by
  let hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  exact isGraphFlow_add
    (oneZeroAmbientChain_isGraphFlow data hcubic C hC hsame)
    (pair.edgeTransfer_isGraphFlow minimal)

/-- A perturbed edge is zero exactly when the reconstructed and closure
values agree there. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosurePerturbation_eq_zero_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (edge : G.edgeSet) :
    pair.oneZeroClosurePerturbation C edge = 0 ↔
      oneZeroAmbientChain data C edge = pair.edgeTransfer edge := by
  exact add_eq_zero_iff_eq _ _

/-- Local CDL-goodness after perturbation is exactly a mismatch between the
two summand chains on some incident edge. -/
theorem CrossCentralExactFaceCutPair.isCDLGoodAtVertex_oneZeroClosurePerturbation_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (vertex : V) :
    IsCDLGoodAtVertex G (pair.oneZeroClosurePerturbation C) vertex ↔
      ∃ edge ∈ incidentEdgeFinset G vertex,
        oneZeroAmbientChain data C edge ≠ pair.edgeTransfer edge := by
  constructor
  · rintro ⟨edge, hedge, hnonzero⟩
    refine ⟨edge, hedge, ?_⟩
    intro heq
    apply hnonzero
    rw [pair.oneZeroClosurePerturbation_apply, heq]
    exact color_add_self _
  · rintro ⟨edge, hedge, hne⟩
    exact ⟨edge, hedge, add_ne_zero_of_ne hne⟩

/-- Failure of local CDL-goodness is exact edgewise agreement of the two
summands on the whole incident triple. -/
theorem CrossCentralExactFaceCutPair.not_isCDLGoodAtVertex_oneZeroClosurePerturbation_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (vertex : V) :
    ¬ IsCDLGoodAtVertex G (pair.oneZeroClosurePerturbation C) vertex ↔
      ∀ edge ∈ incidentEdgeFinset G vertex,
        oneZeroAmbientChain data C edge = pair.edgeTransfer edge := by
  rw [pair.isCDLGoodAtVertex_oneZeroClosurePerturbation_iff]
  push Not
  exact Iff.rfl

/-- The exact-closure circulation takes the purple value on the restored
central edge. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.edgeTransfer (centralEdge data) = purple := by
  apply (pair.edgeTransfer_eq_purple_iff minimal (centralEdge data)).2
  exact Or.inr rfl

/-- The exact-closure circulation also takes the purple value on the
retained cross edge. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.edgeTransfer (retainedEdgeToAmbientEdge data cross) = purple := by
  apply (pair.edgeTransfer_eq_purple_iff minimal
    (retainedEdgeToAmbientEdge data cross)).2
  exact Or.inl rfl

/-- Perturbation removes the original zero on the central edge. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosurePerturbation_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) :
    pair.oneZeroClosurePerturbation C (centralEdge data) = purple := by
  rw [pair.oneZeroClosurePerturbation_apply,
    oneZeroAmbientChain_central, pair.edgeTransfer_centralEdge minimal]
  exact zero_add purple

/-- In particular, neither endpoint of the central edge can be CDL-bad after
the closure perturbation. -/
theorem CrossCentralExactFaceCutPair.isCDLGoodAtVertex_oneZeroClosurePerturbation_of_mem_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (vertex : V) (hvertex : vertex ∈ centralEdgeValue data) :
    IsCDLGoodAtVertex G (pair.oneZeroClosurePerturbation C) vertex := by
  refine ⟨centralEdge data, ?_, ?_⟩
  · simpa [incidentEdgeFinset] using hvertex
  · rw [pair.oneZeroClosurePerturbation_centralEdge minimal]
    exact purple_ne_zero

private theorem localTaitTriple_contains_red_and_blue
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

/-- Every CDL-bad vertex created by the closure perturbation is an endpoint
of the retained cross edge.  The two endpoints of the central edge are
excluded by their new purple central value; away from all four common
branches, edgewise agreement would force a nowhere-zero closure triple and
hence membership in both closure cycles. -/
theorem CrossCentralExactFaceCutPair.mem_retainedCross_of_not_isCDLGoodAtVertex_oneZeroClosurePerturbation
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
    (vertex : V)
    (hbad :
      ¬ IsCDLGoodAtVertex G
        (pair.oneZeroClosurePerturbation C) vertex) :
    vertex ∈ (retainedEdgeToAmbientEdge data cross).1 := by
  let hcubic : ∀ current : V,
      (incidentEdgeFinset G current).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hagree : ∀ edge ∈ incidentEdgeFinset G vertex,
      oneZeroAmbientChain data C edge = pair.edgeTransfer edge :=
    (pair.not_isCDLGoodAtVertex_oneZeroClosurePerturbation_iff
      C vertex).1 hbad
  have hnotCentral : vertex ∉ centralEdgeValue data := by
    intro hcentral
    have hcentralIncident :
        centralEdge data ∈ incidentEdgeFinset G vertex := by
      simpa [incidentEdgeFinset] using hcentral
    have heq := hagree (centralEdge data) hcentralIncident
    rw [oneZeroAmbientChain_central,
      pair.edgeTransfer_centralEdge minimal] at heq
    exact purple_ne_zero heq.symm
  rcases Finset.card_eq_three.mp (hcubic vertex) with
    ⟨first, second, third, hfirstSecond, hfirstThird,
      hsecondThird, hset⟩
  have hfirstIncident : first ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hsecondIncident : second ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hthirdIncident : third ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hfirstVertex : vertex ∈ (first.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hfirstIncident
  have hsecondVertex : vertex ∈ (second.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hsecondIncident
  have hthirdVertex : vertex ∈ (third.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hthirdIncident
  have hfirstNeCentral : first ≠ centralEdge data := by
    intro hedge
    subst first
    exact hnotCentral hfirstVertex
  have hsecondNeCentral : second ≠ centralEdge data := by
    intro hedge
    subst second
    exact hnotCentral hsecondVertex
  have hthirdNeCentral : third ≠ centralEdge data := by
    intro hedge
    subst third
    exact hnotCentral hthirdVertex
  have hfirstNonzero : pair.edgeTransfer first ≠ 0 := by
    rw [← hagree first hfirstIncident]
    exact oneZeroAmbientChain_ne_zero_of_ne_central
      data hcubic C hC first hfirstNeCentral
  have hsecondNonzero : pair.edgeTransfer second ≠ 0 := by
    rw [← hagree second hsecondIncident]
    exact oneZeroAmbientChain_ne_zero_of_ne_central
      data hcubic C hC second hsecondNeCentral
  have hthirdNonzero : pair.edgeTransfer third ≠ 0 := by
    rw [← hagree third hthirdIncident]
    exact oneZeroAmbientChain_ne_zero_of_ne_central
      data hcubic C hC third hthirdNeCentral
  have hflowVertex := pair.edgeTransfer_isGraphFlow minimal vertex
  have hlocalKirchhoff : IsLocalKirchhoffTriple
      (pair.edgeTransfer first) (pair.edgeTransfer second)
        (pair.edgeTransfer third) := by
    unfold vertexKirchhoffSum at hflowVertex
    rw [hset] at hflowVertex
    simpa [IsLocalKirchhoffTriple, hfirstSecond, hfirstThird,
      hsecondThird, add_assoc] using hflowVertex
  have hlocalTait : IsLocalTaitTriple
      (pair.edgeTransfer first) (pair.edgeTransfer second)
        (pair.edgeTransfer third) :=
    isLocalTaitTriple_of_kirchhoff_nowhereZero hlocalKirchhoff
      ⟨hfirstNonzero, hsecondNonzero, hthirdNonzero⟩
  have hcontains := localTaitTriple_contains_red_and_blue hlocalTait
  have hprefix :
      vertex ∈ (data.oppositePortClosure pair.prefixTrail).support := by
    rcases hcontains.1 with hred | hred | hred
    · exact (data.oppositePortClosure pair.prefixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_red_iff minimal first).1 hred).1
          hfirstVertex
    · exact (data.oppositePortClosure pair.prefixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_red_iff minimal second).1 hred).1
          hsecondVertex
    · exact (data.oppositePortClosure pair.prefixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_red_iff minimal third).1 hred).1
          hthirdVertex
  have hsuffix :
      vertex ∈
        (data.alternateOppositePortClosure pair.suffixTrail).support := by
    rcases hcontains.2 with hblue | hblue | hblue
    · exact (data.alternateOppositePortClosure pair.suffixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_blue_iff minimal first).1 hblue).2
          hfirstVertex
    · exact (data.alternateOppositePortClosure pair.suffixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_blue_iff minimal second).1 hblue).2
          hsecondVertex
    · exact (data.alternateOppositePortClosure pair.suffixTrail)
        |>.mem_support_of_mem_edges
          ((pair.edgeTransfer_eq_blue_iff minimal third).1 hblue).2
          hthirdVertex
  rcases (pair.mem_both_closure_support_iff minimal hprefixCycle
    hsuffixCycle vertex).1 ⟨hprefix, hsuffix⟩ with hcross | hcentral
  · exact hcross
  · exact False.elim (hnotCentral hcentral)

/-- The finite set of vertices where the closure perturbation is CDL-bad. -/
def CrossCentralExactFaceCutPair.cdlBadVertexFinset
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) : Finset V := by
  classical
  exact Finset.univ.filter fun vertex =>
    ¬ IsCDLGoodAtVertex G (pair.oneZeroClosurePerturbation C) vertex

@[simp]
theorem CrossCentralExactFaceCutPair.mem_cdlBadVertexFinset_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (vertex : V) :
    vertex ∈ pair.cdlBadVertexFinset C ↔
      ¬ IsCDLGoodAtVertex G
        (pair.oneZeroClosurePerturbation C) vertex := by
  classical
  simp [CrossCentralExactFaceCutPair.cdlBadVertexFinset]

/-- Finset form of the two-vertex localization of all perturbation defects. -/
theorem CrossCentralExactFaceCutPair.cdlBadVertices_oneZeroClosurePerturbation_subset_retainedCross
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
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    pair.cdlBadVertexFinset C ⊆
      (retainedEdgeToAmbientEdge data cross).1.toFinset := by
  intro vertex hvertex
  apply Sym2.mem_toFinset.mpr
  exact pair.mem_retainedCross_of_not_isCDLGoodAtVertex_oneZeroClosurePerturbation
    minimal hprefixCycle hsuffixCycle C hC vertex
      ((pair.mem_cdlBadVertexFinset_iff C vertex).1 hvertex)

/-- Consequently the closure perturbation has at most two CDL-bad vertices. -/
theorem CrossCentralExactFaceCutPair.card_cdlBadVertices_oneZeroClosurePerturbation_le_two
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
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    (pair.cdlBadVertexFinset C).card ≤ 2 := by
  calc
    (pair.cdlBadVertexFinset C).card ≤
        (retainedEdgeToAmbientEdge data cross).1.toFinset.card :=
      Finset.card_le_card
        (pair.cdlBadVertices_oneZeroClosurePerturbation_subset_retainedCross
          minimal hprefixCycle hsuffixCycle C hC)
    _ = 2 := Sym2.card_toFinset_of_not_isDiag
      (retainedEdgeToAmbientEdge data cross).1
      (G.not_isDiag_of_mem_edgeSet
        (retainedEdgeToAmbientEdge data cross).2)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
