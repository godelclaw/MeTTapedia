import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureBasisPerturbation

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- On a cubic graph, the zero edges of a CDL-good graph flow form a
matching.  Two distinct zero edges at one vertex would force the whole
Kirchhoff triple to vanish. -/
theorem zeroEdgesFormMatching_of_isCDLGoodFlow_of_card_three
    {chain : G.edgeSet → Color}
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hchain : IsCDLGoodFlow G chain) :
    ZeroEdgesFormMatching G chain := by
  intro vertex
  rw [zeroIncidentEdgeCount, Finset.card_le_one]
  intro first hfirst second hsecond
  by_contra hdistinct
  have hfirstIncident : first ∈ incidentEdgeFinset G vertex :=
    (Finset.mem_filter.mp hfirst).1
  have hsecondIncident : second ∈ incidentEdgeFinset G vertex :=
    (Finset.mem_filter.mp hsecond).1
  have hfirstZero : chain first = 0 :=
    (Finset.mem_filter.mp hfirst).2
  have hsecondZero : chain second = 0 :=
    (Finset.mem_filter.mp hsecond).2
  exact
    (not_isCDLGoodAtVertex_of_isGraphFlow_of_two_zero
      hchain.1 vertex (hcubic vertex) first second
        hfirstIncident hsecondIncident hdistinct hfirstZero hsecondZero)
      (hchain.2 vertex)

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- If the cross color differs from the sum of the two transfer
coefficients, the rebased perturbation is nonzero on the retained cross. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation_retainedCross_ne_zero
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color)
    (hmismatch : C cross ≠ first + second) :
    pair.oneZeroClosureBasisPerturbation C first second
        (retainedEdgeToAmbientEdge data cross) ≠ 0 := by
  rw [pair.oneZeroClosureBasisPerturbation_apply,
    oneZeroAmbientChain_retainedEdgeToAmbientEdge,
    pair.edgeTransferInBasis_retainedCross minimal]
  exact add_ne_zero_of_ne hmismatch

/-- A coefficient pair avoiding the cross color repairs the singleton
endpoint defect.  Every possible bad vertex is a cross endpoint, while the
cross itself is now a nonzero incident edge at both endpoints. -/
theorem CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation_isCDLGoodFlow_of_cross_mismatch
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
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second : Color) (hdistinct : first ≠ second)
    (hmismatch : C cross ≠ first + second) :
    IsCDLGoodFlow G
      (pair.oneZeroClosureBasisPerturbation C first second) := by
  have hflow := pair.oneZeroClosureBasisPerturbation_isGraphFlow
    minimal C hC hsame first second
  refine ⟨hflow, ?_⟩
  intro vertex
  by_contra hbad
  have hvertex : vertex ∈
      (retainedEdgeToAmbientEdge data cross).1 :=
    pair.mem_retainedCross_of_not_isCDLGoodAtVertex_oneZeroClosureBasisPerturbation
      minimal hprefixCycle hsuffixCycle C hC first second hdistinct
        vertex hbad
  apply hbad
  refine ⟨retainedEdgeToAmbientEdge data cross, ?_, ?_⟩
  · simpa [incidentEdgeFinset] using hvertex
  · exact pair.oneZeroClosureBasisPerturbation_retainedCross_ne_zero
      minimal C first second hmismatch

/-- The repaired transfer state has a matching zero pattern. -/
theorem CrossCentralExactFaceCutPair.zeroEdgesFormMatching_oneZeroClosureBasisPerturbation_of_cross_mismatch
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
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second : Color) (hdistinct : first ≠ second)
    (hmismatch : C cross ≠ first + second) :
    ZeroEdgesFormMatching G
      (pair.oneZeroClosureBasisPerturbation C first second) := by
  apply zeroEdgesFormMatching_of_isCDLGoodFlow_of_card_three
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic)
  exact
    pair.oneZeroClosureBasisPerturbation_isCDLGoodFlow_of_cross_mismatch
      minimal hprefixCycle hsuffixCycle C hC hsame first second
        hdistinct hmismatch

/-- An edge exclusively on the prefix closure where the singleton-zero
chain agrees with a prescribed transfer coefficient. -/
def CrossCentralExactFaceCutPair.IsPrefixCancellationEdge
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (coefficient : Color) (edge : G.edgeSet) : Prop :=
  edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∧
    edge.1 ∉
      (data.alternateOppositePortClosure pair.suffixTrail).edges ∧
    oneZeroAmbientChain data C edge = coefficient

/-- An edge exclusively on the suffix closure where the singleton-zero
chain agrees with a prescribed transfer coefficient. -/
def CrossCentralExactFaceCutPair.IsSuffixCancellationEdge
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (coefficient : Color) (edge : G.edgeSet) : Prop :=
  edge.1 ∉ (data.oppositePortClosure pair.prefixTrail).edges ∧
    edge.1 ∈
      (data.alternateOppositePortClosure pair.suffixTrail).edges ∧
    oneZeroAmbientChain data C edge = coefficient

/-- In a noncolorable cubic graph, every repaired coefficient state must
cancel somewhere else.  Exactness of the paired transfer places that zero
on exactly one closure, with the corresponding coefficient as its original
singleton-zero value. -/
theorem CrossCentralExactFaceCutPair.exists_exclusiveClosureCancellation_of_cross_mismatch
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
    (first second : Color) (hdistinct : first ≠ second)
    (hmismatch : C cross ≠ first + second) :
    (∃ edge : G.edgeSet,
        pair.IsPrefixCancellationEdge C first edge) ∨
      ∃ edge : G.edgeSet,
        pair.IsSuffixCancellationEdge C second edge := by
  let chain := pair.oneZeroClosureBasisPerturbation C first second
  have hflow : IsGraphFlow G chain :=
    pair.oneZeroClosureBasisPerturbation_isGraphFlow
      minimal C hC hsame first second
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hexistsZero : ∃ edge : G.edgeSet, chain edge = 0 := by
    by_contra hnone
    push Not at hnone
    have hnowhere : IsNowhereZeroFlow G chain := ⟨hflow, hnone⟩
    exact
      (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
        graphData minimal)
        (exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
          (hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
            hcubic)
          chain hnowhere)
  rcases hexistsZero with ⟨edge, hedgeZero⟩
  have hagree : oneZeroAmbientChain data C edge =
      pair.edgeTransferInBasis first second edge :=
    (pair.oneZeroClosureBasisPerturbation_eq_zero_iff
      C first second edge).1 hedgeZero
  by_cases htransferZero : pair.edgeTransfer edge = 0
  · have hchainZero : oneZeroAmbientChain data C edge = 0 := by
      rw [hagree, pair.edgeTransferInBasis_apply, htransferZero, map_zero]
    have hedgeCentral : edge = centralEdge data :=
      (oneZeroAmbientChain_eq_zero_iff data hcubic C hC edge).1 hchainZero
    subst edge
    rw [pair.edgeTransfer_centralEdge minimal] at htransferZero
    exact False.elim (purple_ne_zero htransferZero)
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
        (pair.edgeTransfer edge) htransferZero with
      hred | hblue | hpurple
    · left
      refine ⟨edge, ?_⟩
      have hmembership :=
        (pair.edgeTransfer_eq_red_iff minimal edge).1 hred
      refine ⟨hmembership.1, hmembership.2, ?_⟩
      rw [hagree, pair.edgeTransferInBasis_apply, hred,
        colorBasisAddHom_red]
    · right
      refine ⟨edge, ?_⟩
      have hmembership :=
        (pair.edgeTransfer_eq_blue_iff minimal edge).1 hblue
      refine ⟨hmembership.1, hmembership.2, ?_⟩
      rw [hagree, pair.edgeTransferInBasis_apply, hblue,
        colorBasisAddHom_blue]
    · rcases (pair.edgeTransfer_eq_purple_iff minimal edge).1 hpurple with
        hcross | hcentral
      · have hedgeCross : edge = retainedEdgeToAmbientEdge data cross :=
          Subtype.ext hcross
        subst edge
        rw [oneZeroAmbientChain_retainedEdgeToAmbientEdge,
          pair.edgeTransferInBasis_retainedCross minimal] at hagree
        exact False.elim (hmismatch hagree)
      · have hedgeCentral : edge = centralEdge data :=
          Subtype.ext hcentral
        subst edge
        rw [oneZeroAmbientChain_central,
          pair.edgeTransferInBasis_centralEdge minimal] at hagree
        exact False.elim ((add_ne_zero_of_ne hdistinct) hagree.symm)

/-- Four safe coefficient choices force a two-sided color profile.  On
each closure, either an exclusive edge carries the cross color, or the
opposite closure has exclusive cancellation edges of both other colors. -/
theorem CrossCentralExactFaceCutPair.forced_exclusiveClosureColorProfile
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
    (a b c : Color) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcrossColor : C cross = a) :
    ((∃ edge : G.edgeSet, pair.IsPrefixCancellationEdge C a edge) ∨
        ∃ bEdge cEdge : G.edgeSet,
          pair.IsSuffixCancellationEdge C b bEdge ∧
            pair.IsSuffixCancellationEdge C c cEdge ∧
            bEdge ≠ cEdge) ∧
      ((∃ edge : G.edgeSet, pair.IsSuffixCancellationEdge C a edge) ∨
        ∃ bEdge cEdge : G.edgeSet,
          pair.IsPrefixCancellationEdge C b bEdge ∧
            pair.IsPrefixCancellationEdge C c cEdge ∧
            bEdge ≠ cEdge) := by
  have hmismatchB : C cross ≠ a + b := by
    rw [hcrossColor]
    intro heq
    exact hb (by simpa using heq.symm)
  have hmismatchC : C cross ≠ a + c := by
    rw [hcrossColor]
    intro heq
    exact hc (by simpa using heq.symm)
  have hprefixAorSuffixB :=
    pair.exists_exclusiveClosureCancellation_of_cross_mismatch
      minimal C hC hsame a b hab hmismatchB
  have hprefixAorSuffixC :=
    pair.exists_exclusiveClosureCancellation_of_cross_mismatch
      minimal C hC hsame a c hac hmismatchC
  have hsuffixAorPrefixB :=
    pair.exists_exclusiveClosureCancellation_of_cross_mismatch
      minimal C hC hsame b a hab.symm (by simpa [add_comm] using hmismatchB)
  have hsuffixAorPrefixC :=
    pair.exists_exclusiveClosureCancellation_of_cross_mismatch
      minimal C hC hsame c a hac.symm (by simpa [add_comm] using hmismatchC)
  constructor
  · rcases hprefixAorSuffixB with hprefixA | hsuffixB
    · exact Or.inl hprefixA
    · rcases hprefixAorSuffixC with hprefixA | hsuffixC
      · exact Or.inl hprefixA
      · rcases hsuffixB with ⟨bEdge, hbEdge⟩
        rcases hsuffixC with ⟨cEdge, hcEdge⟩
        refine Or.inr ⟨bEdge, cEdge, hbEdge, hcEdge, ?_⟩
        intro hedge
        subst cEdge
        exact hbc (hbEdge.2.2.symm.trans hcEdge.2.2)
  · rcases hsuffixAorPrefixB with hprefixB | hsuffixA
    · rcases hsuffixAorPrefixC with hprefixC | hsuffixA
      · rcases hprefixB with ⟨bEdge, hbEdge⟩
        rcases hprefixC with ⟨cEdge, hcEdge⟩
        refine Or.inr ⟨bEdge, cEdge, hbEdge, hcEdge, ?_⟩
        intro hedge
        subst cEdge
        exact hbc (hbEdge.2.2.symm.trans hcEdge.2.2)
      · exact Or.inl hsuffixA
    · exact Or.inl hsuffixA

/-- A rejected singleton `bc` cross is not a terminal CDL obstruction.
The route-color basis `(b,c)` has the certified singleton melt, while the
two adjacent coefficient states `(a,b)` and `(a,c)` are globally CDL-good. -/
theorem EvenKempeFusionLens.bcCrossExactPair_singleton_bad_and_alternate_good
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
          hab hbc site).1} ∧
      IsCDLGoodFlow G
        (pair.oneZeroClosureBasisPerturbation C a b) ∧
      IsCDLGoodFlow G
        (pair.oneZeroClosureBasisPerturbation C a c) := by
  have hsiteColor : C site.1 = a :=
    lens01.bRoute.color_eq_first_of_crossSite lens23.cRoute hbc site
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
  have hmismatchB : C site.1 ≠ a + b := by
    rw [hsiteColor]
    intro heq
    exact hb (by simpa using heq.symm)
  have hmismatchC : C site.1 ≠ a + c := by
    rw [hsiteColor]
    intro heq
    exact hc (by simpa using heq.symm)
  exact ⟨
    EvenKempeFusionLens.cdlBadVertexFinsetInBasis_eq_singleton_of_bcCrossExactPair
      graphData minimal data lens01 lens23 hab hac hbc hcount site hfalse
        pair hprefixEdges hsuffixEdges hprefixCycle hsuffixCycle hC hsame,
    pair.oneZeroClosureBasisPerturbation_isCDLGoodFlow_of_cross_mismatch
      minimal hprefixCycle hsuffixCycle C hC hsame a b hab hmismatchB,
    pair.oneZeroClosureBasisPerturbation_isCDLGoodFlow_of_cross_mismatch
      minimal hprefixCycle hsuffixCycle C hC hsame a c hac hmismatchC⟩

/-- Symmetric transfer fiber at a rejected singleton `cb` cross: `(c,b)`
is the melted state and `(a,c)`, `(a,b)` are globally CDL-good. -/
theorem EvenKempeFusionLens.cbCrossExactPair_singleton_bad_and_alternate_good
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
          hac hbc.symm site).1} ∧
      IsCDLGoodFlow G
        (pair.oneZeroClosureBasisPerturbation C a c) ∧
      IsCDLGoodFlow G
        (pair.oneZeroClosureBasisPerturbation C a b) := by
  have hsiteColor : C site.1 = a :=
    lens01.cRoute.color_eq_first_of_crossSite lens23.bRoute hbc.symm site
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
  have hmismatchC : C site.1 ≠ a + c := by
    rw [hsiteColor]
    intro heq
    exact hc (by simpa using heq.symm)
  have hmismatchB : C site.1 ≠ a + b := by
    rw [hsiteColor]
    intro heq
    exact hb (by simpa using heq.symm)
  exact ⟨
    EvenKempeFusionLens.cdlBadVertexFinsetInBasis_eq_singleton_of_cbCrossExactPair
      graphData minimal data lens01 lens23 hab hac hbc hcount site hfalse
        pair hprefixEdges hsuffixEdges hprefixCycle hsuffixCycle hC hsame,
    pair.oneZeroClosureBasisPerturbation_isCDLGoodFlow_of_cross_mismatch
      minimal hprefixCycle hsuffixCycle C hC hsame a c hac hmismatchC,
    pair.oneZeroClosureBasisPerturbation_isCDLGoodFlow_of_cross_mismatch
      minimal hprefixCycle hsuffixCycle C hC hsame a b hab hmismatchB⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
