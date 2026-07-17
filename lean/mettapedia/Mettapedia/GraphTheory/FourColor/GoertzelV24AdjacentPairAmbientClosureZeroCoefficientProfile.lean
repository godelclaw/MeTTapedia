import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCoefficientRepair

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

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- If a singleton-zero value is nonzero and differs from every restored
boundary value, its ambient edge is retained. -/
theorem isRetainedAmbientEdge_of_oneZeroAmbientChain_eq_of_avoids_boundary
    {data : AdjacentPairData G}
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (coefficient : Color) (edge : G.edgeSet)
    (hcoefficient : coefficient ≠ 0)
    (hboundary : ∀ port : Fin 4,
      coefficient ≠ data.degreeTwoBoundaryData.colorWord C port)
    (hvalue : oneZeroAmbientChain data C edge = coefficient) :
    IsRetainedAmbientEdge data edge := by
  by_contra hnotRetained
  rcases (not_isRetainedAmbientEdge_iff data edge).1 hnotRetained with
    hcentral | ⟨port, hport⟩
  · have hedge : edge = centralEdge data := Subtype.ext hcentral
    subst edge
    rw [oneZeroAmbientChain_central] at hvalue
    exact hcoefficient hvalue.symm
  · have hedge : edge = boundaryEdge data port := Subtype.ext hport
    subst edge
    rw [oneZeroAmbientChain_boundary] at hvalue
    exact hboundary port hvalue.symm

/-- No prefix cancellation can carry coefficient zero.  The singleton-zero
chain vanishes only on the central edge, which belongs to both closures. -/
theorem CrossCentralExactFaceCutPair.not_exists_prefixCancellationEdge_zero
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ¬ ∃ edge : G.edgeSet, pair.IsPrefixCancellationEdge C 0 edge := by
  rintro ⟨edge, hedge⟩
  have hcentral : edge = centralEdge data :=
    (oneZeroAmbientChain_eq_zero_iff data hcubic C hC edge).1 hedge.2.2
  subst edge
  exact hedge.2.1
    (data.centralEdgeValue_mem_alternateOppositePortClosure_edges
      pair.suffixTrail)

/-- Symmetrically, coefficient zero cannot cancel exclusively on the suffix
closure. -/
theorem CrossCentralExactFaceCutPair.not_exists_suffixCancellationEdge_zero
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ¬ ∃ edge : G.edgeSet, pair.IsSuffixCancellationEdge C 0 edge := by
  rintro ⟨edge, hedge⟩
  have hcentral : edge = centralEdge data :=
    (oneZeroAmbientChain_eq_zero_iff data hcubic C hC edge).1 hedge.2.2
  subst edge
  exact hedge.1
    (data.centralEdgeValue_mem_oppositePortClosure_edges pair.prefixTrail)

/-- With zero in the second coefficient coordinate, cross mismatch forces a
genuine cancellation on the prefix closure. -/
theorem CrossCentralExactFaceCutPair.exists_prefixCancellation_of_zero_second
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
    (coefficient : Color) (hcoefficient : coefficient ≠ 0)
    (hmismatch : C cross ≠ coefficient) :
    ∃ edge : G.edgeSet,
      pair.IsPrefixCancellationEdge C coefficient edge := by
  have hcases := pair.exists_exclusiveClosureCancellation_of_cross_mismatch
    minimal C hC hsame coefficient 0 hcoefficient (by simpa using hmismatch)
  rcases hcases with hprefix | hsuffix
  · exact hprefix
  · exact False.elim
      (pair.not_exists_suffixCancellationEdge_zero
        (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
          graphData minimal.spherical.cubic)
        C hC hsuffix)

/-- With zero in the first coefficient coordinate, cross mismatch forces a
genuine cancellation on the suffix closure. -/
theorem CrossCentralExactFaceCutPair.exists_suffixCancellation_of_zero_first
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
    (coefficient : Color) (hcoefficient : coefficient ≠ 0)
    (hmismatch : C cross ≠ coefficient) :
    ∃ edge : G.edgeSet,
      pair.IsSuffixCancellationEdge C coefficient edge := by
  have hcases := pair.exists_exclusiveClosureCancellation_of_cross_mismatch
    minimal C hC hsame 0 coefficient hcoefficient.symm
      (by simpa using hmismatch)
  rcases hcases with hprefix | hsuffix
  · exact False.elim
      (pair.not_exists_prefixCancellationEdge_zero
        (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
          graphData minimal.spherical.cubic)
        C hC hprefix)
  · exact hsuffix

/-- Zero-coordinate coefficient states force both non-cross colors on both
exclusive closures.  The zero-coordinate alternative cannot be discharged
by the shared central edge. -/
theorem CrossCentralExactFaceCutPair.forced_exclusiveClosureNonzeroColorProfile
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
    (∃ bEdge cEdge : G.edgeSet,
        pair.IsPrefixCancellationEdge C b bEdge ∧
          pair.IsPrefixCancellationEdge C c cEdge ∧
          bEdge ≠ cEdge) ∧
      ∃ bEdge cEdge : G.edgeSet,
        pair.IsSuffixCancellationEdge C b bEdge ∧
          pair.IsSuffixCancellationEdge C c cEdge ∧
          bEdge ≠ cEdge := by
  have hcrossNeB : C cross ≠ b := by
    rw [hcrossColor]
    exact hab
  have hcrossNeC : C cross ≠ c := by
    rw [hcrossColor]
    exact hac
  rcases pair.exists_prefixCancellation_of_zero_second
      minimal C hC hsame b hb hcrossNeB with ⟨prefixB, hprefixB⟩
  rcases pair.exists_prefixCancellation_of_zero_second
      minimal C hC hsame c hc hcrossNeC with ⟨prefixC, hprefixC⟩
  rcases pair.exists_suffixCancellation_of_zero_first
      minimal C hC hsame b hb hcrossNeB with ⟨suffixB, hsuffixB⟩
  rcases pair.exists_suffixCancellation_of_zero_first
      minimal C hC hsame c hc hcrossNeC with ⟨suffixC, hsuffixC⟩
  constructor
  · refine ⟨prefixB, prefixC, hprefixB, hprefixC, ?_⟩
    intro hedge
    subst prefixC
    exact hbc (hprefixB.2.2.symm.trans hprefixC.2.2)
  · refine ⟨suffixB, suffixC, hsuffixB, hsuffixC, ?_⟩
    intro hedge
    subst suffixC
    exact hbc (hsuffixB.2.2.symm.trans hsuffixC.2.2)

/-- In a constant `a` boundary state, the forced `b`- and `c`-cancellations
are retained ambient edges on both closures. -/
theorem CrossCentralExactFaceCutPair.forced_retainedExclusiveClosureColorProfile
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
    (a b c : Color)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcrossColor : C cross = a) :
    (∃ bEdge cEdge : G.edgeSet,
        IsRetainedAmbientEdge data bEdge ∧
          IsRetainedAmbientEdge data cEdge ∧
          pair.IsPrefixCancellationEdge C b bEdge ∧
          pair.IsPrefixCancellationEdge C c cEdge ∧
          bEdge ≠ cEdge) ∧
      ∃ bEdge cEdge : G.edgeSet,
        IsRetainedAmbientEdge data bEdge ∧
          IsRetainedAmbientEdge data cEdge ∧
          pair.IsSuffixCancellationEdge C b bEdge ∧
          pair.IsSuffixCancellationEdge C c cEdge ∧
          bEdge ≠ cEdge := by
  have hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3 := by
    constructor <;> rw [hconstant, hconstant]
  rcases pair.forced_exclusiveClosureNonzeroColorProfile
      minimal C hC hsame a b c hb hc hab hac hbc hcrossColor with
    ⟨⟨prefixB, prefixC, hprefixB, hprefixC, hprefixNe⟩,
      suffixB, suffixC, hsuffixB, hsuffixC, hsuffixNe⟩
  have hretained (coefficient : Color) (edge : G.edgeSet)
      (hcoefficient : coefficient ≠ 0) (hcoefficientA : coefficient ≠ a)
      (hvalue : oneZeroAmbientChain data C edge = coefficient) :
      IsRetainedAmbientEdge data edge := by
    apply isRetainedAmbientEdge_of_oneZeroAmbientChain_eq_of_avoids_boundary
      C coefficient edge hcoefficient
    · intro port
      rw [hconstant port]
      exact hcoefficientA
    · exact hvalue
  exact ⟨
    ⟨prefixB, prefixC,
      hretained b prefixB hb hab.symm hprefixB.2.2,
      hretained c prefixC hc hac.symm hprefixC.2.2,
      hprefixB, hprefixC, hprefixNe⟩,
    suffixB, suffixC,
      hretained b suffixB hb hab.symm hsuffixB.2.2,
      hretained c suffixC hc hac.symm hsuffixC.2.2,
      hsuffixB, hsuffixC, hsuffixNe⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A retained edge belongs to an alternate opposite-port closure exactly
when its deleted-graph source belongs to the retained suffix trail. -/
theorem retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
    {data : AdjacentPairData G}
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    (retainedEdgeToAmbientEdge data edge).1 ∈
        (data.alternateOppositePortClosure path).edges ↔
      edge.1 ∈ path.edges := by
  change (retainedEdgeToAmbientEdge data edge).1 ∈
      ((data.retainedWalkToAmbient path).append
        data.alternateOppositePortCentralReturnRetained).edges ↔
      edge.1 ∈ path.edges
  rw [SimpleGraph.Walk.edges_append, List.mem_append]
  constructor
  · rintro (hpath | hreturn)
    · exact (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data path edge).1 hpath
    · rw [data.alternateOppositePortCentralReturnRetained_edges,
        data.alternateOppositePortCentralReturn_edges] at hreturn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hreturn
      rcases hreturn with hthree | hcentral | hone
      · exact False.elim
          (retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 3
            (Subtype.ext hthree))
      · exact False.elim
          (retainedEdgeToAmbientEdge_ne_centralEdge data edge
            (Subtype.ext hcentral))
      · exact False.elim
          (retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 1
            (Subtype.ext hone))
  · intro hpath
    exact Or.inl
      ((retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data path edge).2 hpath)

/-- A first-route-colored edge in a cross prefix splice lies on its first
prefix arm, not on the second two-color route. -/
theorem EvenKempePortPath.mem_firstPrefixToCrossSite_of_mem_crossSplice_of_color_eq_second
    {data : DegreeTwoBoundaryData
      (DeletedAdjacentPairGraph G firstVertex secondVertex) 4}
    {C : (DeletedAdjacentPairGraph G firstVertex
      secondVertex).EdgeColoring Color}
    {a b c : Color} {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) (edge :
      (DeletedAdjacentPairGraph G firstVertex secondVertex).edgeSet)
    (hsplice : edge ∈ (first.crossSplice second site).support)
    (hcolor : C edge = b) :
    edge ∈ (first.firstPrefixToCrossSite second site).support := by
  rw [EvenKempePortPath.crossSplice,
    SimpleGraph.Walk.support_append] at hsplice
  rcases List.mem_append.mp hsplice with hfirst | hsecondReverseTail
  · exact hfirst
  · have hsecondPrefix : edge ∈
        (first.secondPrefixToCrossSite second site).support := by
      have hreverse : edge ∈
          (first.secondPrefixToCrossSite second site).reverse.support :=
        List.mem_of_mem_tail hsecondReverseTail
      simpa only [SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hreverse
    have hsecondAmbient : edge ∈ second.ambientPath.support :=
      first.secondPrefixToCrossSite_support_subset second site hsecondPrefix
    rcases (second.mem_ambientPath_support_iff edge).1 hsecondAmbient with
      ⟨hselected, _hpath⟩
    rcases hselected with hcolorA | hcolorC
    · exact False.elim (hab (hcolorA.symm.trans hcolor))
    · exact False.elim (hbc (hcolor.symm.trans hcolorC))

/-- A second-route-colored edge in a cross prefix splice lies on its second
prefix arm. -/
theorem EvenKempePortPath.mem_secondPrefixToCrossSite_of_mem_crossSplice_of_color_eq_second
    {data : DegreeTwoBoundaryData
      (DeletedAdjacentPairGraph G firstVertex secondVertex) 4}
    {C : (DeletedAdjacentPairGraph G firstVertex
      secondVertex).EdgeColoring Color}
    {a b c : Color} {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) (edge :
      (DeletedAdjacentPairGraph G firstVertex secondVertex).edgeSet)
    (hsplice : edge ∈ (first.crossSplice second site).support)
    (hcolor : C edge = c) :
    edge ∈ (first.secondPrefixToCrossSite second site).support := by
  rw [EvenKempePortPath.crossSplice,
    SimpleGraph.Walk.support_append] at hsplice
  rcases List.mem_append.mp hsplice with hfirst | hsecondReverseTail
  · have hfirstAmbient : edge ∈ first.ambientPath.support :=
      first.firstPrefixToCrossSite_support_subset second site hfirst
    rcases (first.mem_ambientPath_support_iff edge).1 hfirstAmbient with
      ⟨hselected, _hpath⟩
    rcases hselected with hcolorA | hcolorB
    · exact False.elim (hac (hcolorA.symm.trans hcolor))
    · exact False.elim (hbc (hcolorB.symm.trans hcolor))
  · have hreverse : edge ∈
        (first.secondPrefixToCrossSite second site).reverse.support :=
      List.mem_of_mem_tail hsecondReverseTail
    simpa only [SimpleGraph.Walk.support_reverse,
      List.mem_reverse] using hreverse

/-- A first-route-colored edge in the suffix splice belongs to the first
suffix arm. -/
theorem EvenKempePortPath.mem_firstSuffixFromCrossSite_of_mem_crossSuffixSplice_of_color_eq_second
    {data : DegreeTwoBoundaryData
      (DeletedAdjacentPairGraph G firstVertex secondVertex) 4}
    {C : (DeletedAdjacentPairGraph G firstVertex
      secondVertex).EdgeColoring Color}
    {a b c : Color} {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) (edge :
      (DeletedAdjacentPairGraph G firstVertex secondVertex).edgeSet)
    (hsplice : edge ∈ (first.crossSuffixSplice second site).support)
    (hcolor : C edge = b) :
    edge ∈ (first.firstSuffixFromCrossSite second site).support := by
  rw [EvenKempePortPath.crossSuffixSplice,
    SimpleGraph.Walk.support_append] at hsplice
  rcases List.mem_append.mp hsplice with hfirstReverse | hsecondTail
  · simpa only [SimpleGraph.Walk.support_reverse,
      List.mem_reverse] using hfirstReverse
  · have hsecondSuffix : edge ∈
        (first.secondSuffixFromCrossSite second site).support :=
      List.mem_of_mem_tail hsecondTail
    have hsecondAmbient : edge ∈ second.ambientPath.support :=
      first.secondSuffixFromCrossSite_support_subset second site hsecondSuffix
    rcases (second.mem_ambientPath_support_iff edge).1 hsecondAmbient with
      ⟨hselected, _hpath⟩
    rcases hselected with hcolorA | hcolorC
    · exact False.elim (hab (hcolorA.symm.trans hcolor))
    · exact False.elim (hbc (hcolor.symm.trans hcolorC))

/-- A second-route-colored edge in the suffix splice belongs to the second
suffix arm. -/
theorem EvenKempePortPath.mem_secondSuffixFromCrossSite_of_mem_crossSuffixSplice_of_color_eq_second
    {data : DegreeTwoBoundaryData
      (DeletedAdjacentPairGraph G firstVertex secondVertex) 4}
    {C : (DeletedAdjacentPairGraph G firstVertex
      secondVertex).EdgeColoring Color}
    {a b c : Color} {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) (edge :
      (DeletedAdjacentPairGraph G firstVertex secondVertex).edgeSet)
    (hsplice : edge ∈ (first.crossSuffixSplice second site).support)
    (hcolor : C edge = c) :
    edge ∈ (first.secondSuffixFromCrossSite second site).support := by
  rw [EvenKempePortPath.crossSuffixSplice,
    SimpleGraph.Walk.support_append] at hsplice
  rcases List.mem_append.mp hsplice with hfirstReverse | hsecondTail
  · have hfirstSuffix : edge ∈
        (first.firstSuffixFromCrossSite second site).support := by
      simpa only [SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hfirstReverse
    have hfirstAmbient : edge ∈ first.ambientPath.support :=
      first.firstSuffixFromCrossSite_support_subset second site hfirstSuffix
    rcases (first.mem_ambientPath_support_iff edge).1 hfirstAmbient with
      ⟨hselected, _hpath⟩
    rcases hselected with hcolorA | hcolorB
    · exact False.elim (hac (hcolorA.symm.trans hcolor))
    · exact False.elim (hbc (hcolorB.symm.trans hcolor))
  · exact List.mem_of_mem_tail hsecondTail

/-- The strengthened cancellation profile localizes to any prescribed
retained supports for the two exact closures. -/
theorem CrossCentralExactFaceCutPair.forced_retainedSupportColorProfile
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
    (a b c : Color)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcrossColor : C cross = a)
    (prefixSupport suffixSupport : List
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet)
    (hprefixEdges : pair.prefixTrail.edges = prefixSupport.map Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges = suffixSupport.map Subtype.val) :
    (∃ bEdge cEdge : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
        bEdge ∈ prefixSupport ∧ C bEdge = b ∧
          pair.IsPrefixCancellationEdge C b
            (retainedEdgeToAmbientEdge data bEdge) ∧
          cEdge ∈ prefixSupport ∧ C cEdge = c ∧
          pair.IsPrefixCancellationEdge C c
            (retainedEdgeToAmbientEdge data cEdge) ∧
          bEdge ≠ cEdge) ∧
      ∃ bEdge cEdge : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
        bEdge ∈ suffixSupport ∧ C bEdge = b ∧
          pair.IsSuffixCancellationEdge C b
            (retainedEdgeToAmbientEdge data bEdge) ∧
          cEdge ∈ suffixSupport ∧ C cEdge = c ∧
          pair.IsSuffixCancellationEdge C c
            (retainedEdgeToAmbientEdge data cEdge) ∧
          bEdge ≠ cEdge := by
  rcases pair.forced_retainedExclusiveClosureColorProfile
      minimal C hC a b c hconstant hb hc hab hac hbc hcrossColor with
    ⟨⟨prefixB, prefixC, hprefixBRetained, hprefixCRetained,
        hprefixB, hprefixC, _hprefixNe⟩,
      suffixB, suffixC, hsuffixBRetained, hsuffixCRetained,
        hsuffixB, hsuffixC, _hsuffixNe⟩
  let prefixBRetained :=
    ambientEdgeToRetainedEdge data prefixB hprefixBRetained
  let prefixCRetained :=
    ambientEdgeToRetainedEdge data prefixC hprefixCRetained
  let suffixBRetained :=
    ambientEdgeToRetainedEdge data suffixB hsuffixBRetained
  let suffixCRetained :=
    ambientEdgeToRetainedEdge data suffixC hsuffixCRetained
  have mem_support_of_mem_mapped_edges
      (support : List (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet)
      (edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet)
      (hmem : edge.1 ∈ support.map Subtype.val) : edge ∈ support := by
    rcases List.mem_map.mp hmem with ⟨source, hsourceMem, hvalue⟩
    have hsourceEq : source = edge := Subtype.ext hvalue
    simpa only [hsourceEq] using hsourceMem
  have hprefixBTrail : prefixBRetained.1 ∈ pair.prefixTrail.edges := by
    apply (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
      data pair.prefixTrail prefixBRetained).1
    simpa only [prefixBRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hprefixB.1
  have hprefixCTrail : prefixCRetained.1 ∈ pair.prefixTrail.edges := by
    apply (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
      data pair.prefixTrail prefixCRetained).1
    simpa only [prefixCRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hprefixC.1
  have hsuffixBTrail : suffixBRetained.1 ∈ pair.suffixTrail.edges := by
    apply (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
      pair.suffixTrail suffixBRetained).1
    simpa only [suffixBRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hsuffixB.2.1
  have hsuffixCTrail : suffixCRetained.1 ∈ pair.suffixTrail.edges := by
    apply (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
      pair.suffixTrail suffixCRetained).1
    simpa only [suffixCRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hsuffixC.2.1
  have hprefixBSupport : prefixBRetained ∈ prefixSupport := by
    apply mem_support_of_mem_mapped_edges prefixSupport prefixBRetained
    rw [← hprefixEdges]
    exact hprefixBTrail
  have hprefixCSupport : prefixCRetained ∈ prefixSupport := by
    apply mem_support_of_mem_mapped_edges prefixSupport prefixCRetained
    rw [← hprefixEdges]
    exact hprefixCTrail
  have hsuffixBSupport : suffixBRetained ∈ suffixSupport := by
    apply mem_support_of_mem_mapped_edges suffixSupport suffixBRetained
    rw [← hsuffixEdges]
    exact hsuffixBTrail
  have hsuffixCSupport : suffixCRetained ∈ suffixSupport := by
    apply mem_support_of_mem_mapped_edges suffixSupport suffixCRetained
    rw [← hsuffixEdges]
    exact hsuffixCTrail
  have hprefixBColor : C prefixBRetained = b := by
    rw [← oneZeroAmbientChain_retainedEdgeToAmbientEdge]
    simpa only [prefixBRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hprefixB.2.2
  have hprefixCColor : C prefixCRetained = c := by
    rw [← oneZeroAmbientChain_retainedEdgeToAmbientEdge]
    simpa only [prefixCRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hprefixC.2.2
  have hsuffixBColor : C suffixBRetained = b := by
    rw [← oneZeroAmbientChain_retainedEdgeToAmbientEdge]
    simpa only [suffixBRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hsuffixB.2.2
  have hsuffixCColor : C suffixCRetained = c := by
    rw [← oneZeroAmbientChain_retainedEdgeToAmbientEdge]
    simpa only [suffixCRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hsuffixC.2.2
  have hprefixBCancellation : pair.IsPrefixCancellationEdge C b
      (retainedEdgeToAmbientEdge data prefixBRetained) := by
    simpa only [prefixBRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hprefixB
  have hprefixCCancellation : pair.IsPrefixCancellationEdge C c
      (retainedEdgeToAmbientEdge data prefixCRetained) := by
    simpa only [prefixCRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hprefixC
  have hsuffixBCancellation : pair.IsSuffixCancellationEdge C b
      (retainedEdgeToAmbientEdge data suffixBRetained) := by
    simpa only [suffixBRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hsuffixB
  have hsuffixCCancellation : pair.IsSuffixCancellationEdge C c
      (retainedEdgeToAmbientEdge data suffixCRetained) := by
    simpa only [suffixCRetained,
      retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge] using hsuffixC
  exact ⟨
    ⟨prefixBRetained, prefixCRetained,
      hprefixBSupport, hprefixBColor, hprefixBCancellation,
      hprefixCSupport, hprefixCColor, hprefixCCancellation,
      edge_ne_of_color_eq_of_color_eq_of_ne C
        hprefixBColor hprefixCColor hbc⟩,
    suffixBRetained, suffixCRetained,
      hsuffixBSupport, hsuffixBColor, hsuffixBCancellation,
      hsuffixCSupport, hsuffixCColor, hsuffixCCancellation,
      edge_ne_of_color_eq_of_color_eq_of_ne C
        hsuffixBColor hsuffixCColor hbc⟩

/-- For an exact `bc` cross pair, both its prefix and suffix splices contain
distinct retained cancellation witnesses of colors `b` and `c`. -/
theorem EvenKempeFusionLens.bcCrossExactPair_forced_spliceColorProfile
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
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a) :
    (∃ bEdge cEdge : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
        bEdge ∈ (lens01.bRoute.crossSplice
            lens23.cRoute site).support ∧
          C bEdge = b ∧
          pair.IsPrefixCancellationEdge C b
            (retainedEdgeToAmbientEdge data bEdge) ∧
          cEdge ∈ (lens01.bRoute.crossSplice
            lens23.cRoute site).support ∧
          C cEdge = c ∧
          pair.IsPrefixCancellationEdge C c
            (retainedEdgeToAmbientEdge data cEdge) ∧
          bEdge ≠ cEdge) ∧
      ∃ bEdge cEdge : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
        bEdge ∈ (lens01.bRoute.crossSuffixSplice
            lens23.cRoute site).support ∧
          C bEdge = b ∧
          pair.IsSuffixCancellationEdge C b
            (retainedEdgeToAmbientEdge data bEdge) ∧
          cEdge ∈ (lens01.bRoute.crossSuffixSplice
            lens23.cRoute site).support ∧
          C cEdge = c ∧
          pair.IsSuffixCancellationEdge C c
            (retainedEdgeToAmbientEdge data cEdge) ∧
          bEdge ≠ cEdge := by
  have hb : b ≠ 0 := by
    rw [← lens01.bRoute.leftColor]
    exact hC lens01.bRoute.leftEdge.1
  have hc : c ≠ 0 := by
    rw [← lens01.cRoute.leftColor]
    exact hC lens01.cRoute.leftEdge.1
  exact pair.forced_retainedSupportColorProfile
    minimal C hC a b c hconstant hb hc hab hac hbc
      (lens01.bRoute.color_eq_first_of_crossSite
        lens23.cRoute hbc site)
      (lens01.bRoute.crossSplice lens23.cRoute site).support
      (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support
      hprefixEdges hsuffixEdges

/-- The complementary exact `cb` pair has the same two-color witness profile
on both retained splices. -/
theorem EvenKempeFusionLens.cbCrossExactPair_forced_spliceColorProfile
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
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a) :
    (∃ bEdge cEdge : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
        bEdge ∈ (lens01.cRoute.crossSplice
            lens23.bRoute site).support ∧
          C bEdge = b ∧
          pair.IsPrefixCancellationEdge C b
            (retainedEdgeToAmbientEdge data bEdge) ∧
          cEdge ∈ (lens01.cRoute.crossSplice
            lens23.bRoute site).support ∧
          C cEdge = c ∧
          pair.IsPrefixCancellationEdge C c
            (retainedEdgeToAmbientEdge data cEdge) ∧
          bEdge ≠ cEdge) ∧
      ∃ bEdge cEdge : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
        bEdge ∈ (lens01.cRoute.crossSuffixSplice
            lens23.bRoute site).support ∧
          C bEdge = b ∧
          pair.IsSuffixCancellationEdge C b
            (retainedEdgeToAmbientEdge data bEdge) ∧
          cEdge ∈ (lens01.cRoute.crossSuffixSplice
            lens23.bRoute site).support ∧
          C cEdge = c ∧
          pair.IsSuffixCancellationEdge C c
            (retainedEdgeToAmbientEdge data cEdge) ∧
          bEdge ≠ cEdge := by
  have hb : b ≠ 0 := by
    rw [← lens01.bRoute.leftColor]
    exact hC lens01.bRoute.leftEdge.1
  have hc : c ≠ 0 := by
    rw [← lens01.cRoute.leftColor]
    exact hC lens01.cRoute.leftEdge.1
  exact pair.forced_retainedSupportColorProfile
    minimal C hC a b c hconstant hb hc hab hac hbc
      (lens01.cRoute.color_eq_first_of_crossSite
        lens23.bRoute hbc.symm site)
      (lens01.cRoute.crossSplice lens23.bRoute site).support
      (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support
      hprefixEdges hsuffixEdges

/-- In the `bc` orientation the four forced cancellation witnesses occupy
the four expected route arms: `b` on the first route and `c` on the second,
on each side of the cross. -/
theorem EvenKempeFusionLens.bcCrossExactPair_forced_fourArmCancellationProfile
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
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a) :
    ∃ prefixB prefixC suffixB suffixC :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
      prefixB ∈ (lens01.bRoute.firstPrefixToCrossSite
          lens23.cRoute site).support ∧
        C prefixB = b ∧
        pair.IsPrefixCancellationEdge C b
          (retainedEdgeToAmbientEdge data prefixB) ∧
        prefixC ∈ (lens01.bRoute.secondPrefixToCrossSite
          lens23.cRoute site).support ∧
        C prefixC = c ∧
        pair.IsPrefixCancellationEdge C c
          (retainedEdgeToAmbientEdge data prefixC) ∧
        prefixB ≠ prefixC ∧
        suffixB ∈ (lens01.bRoute.firstSuffixFromCrossSite
          lens23.cRoute site).support ∧
        C suffixB = b ∧
        pair.IsSuffixCancellationEdge C b
          (retainedEdgeToAmbientEdge data suffixB) ∧
        suffixC ∈ (lens01.bRoute.secondSuffixFromCrossSite
          lens23.cRoute site).support ∧
        C suffixC = c ∧
        pair.IsSuffixCancellationEdge C c
          (retainedEdgeToAmbientEdge data suffixC) ∧
        suffixB ≠ suffixC := by
  rcases EvenKempeFusionLens.bcCrossExactPair_forced_spliceColorProfile
      graphData minimal data lens01 lens23 hab hac hbc site pair
        hprefixEdges hsuffixEdges hC hconstant with
    ⟨⟨prefixB, prefixC, hprefixBSplice, hprefixBColor,
        hprefixBCancellation, hprefixCSplice, hprefixCColor,
        hprefixCCancellation, hprefixNe⟩,
      suffixB, suffixC, hsuffixBSplice, hsuffixBColor,
        hsuffixBCancellation, hsuffixCSplice, hsuffixCColor,
        hsuffixCCancellation, hsuffixNe⟩
  exact ⟨prefixB, prefixC, suffixB, suffixC,
    EvenKempePortPath.mem_firstPrefixToCrossSite_of_mem_crossSplice_of_color_eq_second
      lens01.bRoute lens23.cRoute hab hbc site prefixB hprefixBSplice
        hprefixBColor,
    hprefixBColor, hprefixBCancellation,
    EvenKempePortPath.mem_secondPrefixToCrossSite_of_mem_crossSplice_of_color_eq_second
      lens01.bRoute lens23.cRoute hac hbc site prefixC hprefixCSplice
        hprefixCColor,
    hprefixCColor, hprefixCCancellation, hprefixNe,
    EvenKempePortPath.mem_firstSuffixFromCrossSite_of_mem_crossSuffixSplice_of_color_eq_second
      lens01.bRoute lens23.cRoute hab hbc site suffixB hsuffixBSplice
        hsuffixBColor,
    hsuffixBColor, hsuffixBCancellation,
    EvenKempePortPath.mem_secondSuffixFromCrossSite_of_mem_crossSuffixSplice_of_color_eq_second
      lens01.bRoute lens23.cRoute hac hbc site suffixC hsuffixCSplice
        hsuffixCColor,
    hsuffixCColor, hsuffixCCancellation, hsuffixNe⟩

/-- In the `cb` orientation the arm colors are exchanged: `c` occupies the
first route arms and `b` the second route arms. -/
theorem EvenKempeFusionLens.cbCrossExactPair_forced_fourArmCancellationProfile
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
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a) :
    ∃ prefixC prefixB suffixC suffixB :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
      prefixC ∈ (lens01.cRoute.firstPrefixToCrossSite
          lens23.bRoute site).support ∧
        C prefixC = c ∧
        pair.IsPrefixCancellationEdge C c
          (retainedEdgeToAmbientEdge data prefixC) ∧
        prefixB ∈ (lens01.cRoute.secondPrefixToCrossSite
          lens23.bRoute site).support ∧
        C prefixB = b ∧
        pair.IsPrefixCancellationEdge C b
          (retainedEdgeToAmbientEdge data prefixB) ∧
        prefixC ≠ prefixB ∧
        suffixC ∈ (lens01.cRoute.firstSuffixFromCrossSite
          lens23.bRoute site).support ∧
        C suffixC = c ∧
        pair.IsSuffixCancellationEdge C c
          (retainedEdgeToAmbientEdge data suffixC) ∧
        suffixB ∈ (lens01.cRoute.secondSuffixFromCrossSite
          lens23.bRoute site).support ∧
        C suffixB = b ∧
        pair.IsSuffixCancellationEdge C b
          (retainedEdgeToAmbientEdge data suffixB) ∧
        suffixC ≠ suffixB := by
  rcases EvenKempeFusionLens.cbCrossExactPair_forced_spliceColorProfile
      graphData minimal data lens01 lens23 hab hac hbc site pair
        hprefixEdges hsuffixEdges hC hconstant with
    ⟨⟨prefixB, prefixC, hprefixBSplice, hprefixBColor,
        hprefixBCancellation, hprefixCSplice, hprefixCColor,
        hprefixCCancellation, hprefixBNeC⟩,
      suffixB, suffixC, hsuffixBSplice, hsuffixBColor,
        hsuffixBCancellation, hsuffixCSplice, hsuffixCColor,
        hsuffixCCancellation, hsuffixBNeC⟩
  exact ⟨prefixC, prefixB, suffixC, suffixB,
    EvenKempePortPath.mem_firstPrefixToCrossSite_of_mem_crossSplice_of_color_eq_second
      lens01.cRoute lens23.bRoute hac hbc.symm site prefixC hprefixCSplice
        hprefixCColor,
    hprefixCColor, hprefixCCancellation,
    EvenKempePortPath.mem_secondPrefixToCrossSite_of_mem_crossSplice_of_color_eq_second
      lens01.cRoute lens23.bRoute hab hbc.symm site prefixB hprefixBSplice
        hprefixBColor,
    hprefixBColor, hprefixBCancellation, hprefixBNeC.symm,
    EvenKempePortPath.mem_firstSuffixFromCrossSite_of_mem_crossSuffixSplice_of_color_eq_second
      lens01.cRoute lens23.bRoute hac hbc.symm site suffixC hsuffixCSplice
        hsuffixCColor,
    hsuffixCColor, hsuffixCCancellation,
    EvenKempePortPath.mem_secondSuffixFromCrossSite_of_mem_crossSuffixSplice_of_color_eq_second
      lens01.cRoute lens23.bRoute hab hbc.symm site suffixB hsuffixBSplice
        hsuffixBColor,
    hsuffixBColor, hsuffixBCancellation, hsuffixBNeC.symm⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
