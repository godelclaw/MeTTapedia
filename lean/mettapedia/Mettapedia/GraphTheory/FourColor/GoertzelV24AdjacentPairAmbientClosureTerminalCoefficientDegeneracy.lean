import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureZeroCoefficientProfile

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Every retained prefix-trail edge whose color differs from the retained
cross color is already a prefix cancellation edge. -/
theorem CrossCentralExactFaceCutPair.isPrefixCancellationEdge_retainedEdgeToAmbientEdge
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (coefficient : Color)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hprefix : edge.1 ∈ pair.prefixTrail.edges)
    (hcolor : C edge = coefficient)
    (hneCross : C edge ≠ C cross) :
    pair.IsPrefixCancellationEdge C coefficient
      (retainedEdgeToAmbientEdge data edge) := by
  refine ⟨
    (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
      data pair.prefixTrail edge).2 hprefix, ?_, ?_⟩
  · intro hsuffixClosure
    have hsuffix : edge.1 ∈ pair.suffixTrail.edges :=
      (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
        pair.suffixTrail edge).1 hsuffixClosure
    have hedge : edge.1 = cross.1 :=
      (pair.retainedIntersectionExact edge.1).1 ⟨hprefix, hsuffix⟩
    exact hneCross (congrArg C (Subtype.ext hedge))
  · simpa only [oneZeroAmbientChain_retainedEdgeToAmbientEdge] using hcolor

/-- Symmetrically, every retained suffix-trail edge of non-cross color is
already a suffix cancellation edge. -/
theorem CrossCentralExactFaceCutPair.isSuffixCancellationEdge_retainedEdgeToAmbientEdge
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (coefficient : Color)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hsuffix : edge.1 ∈ pair.suffixTrail.edges)
    (hcolor : C edge = coefficient)
    (hneCross : C edge ≠ C cross) :
    pair.IsSuffixCancellationEdge C coefficient
      (retainedEdgeToAmbientEdge data edge) := by
  refine ⟨?_,
    (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
      pair.suffixTrail edge).2 hsuffix, ?_⟩
  · intro hprefixClosure
    have hprefix : edge.1 ∈ pair.prefixTrail.edges :=
      (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data pair.prefixTrail edge).1 hprefixClosure
    have hedge : edge.1 = cross.1 :=
      (pair.retainedIntersectionExact edge.1).1 ⟨hprefix, hsuffix⟩
    exact hneCross (congrArg C (Subtype.ext hedge))
  · simpa only [oneZeroAmbientChain_retainedEdgeToAmbientEdge] using hcolor

/-- For an exact `bc` cross pair, the four boundary-terminal route edges
themselves realize the entire four-arm coefficient-cancellation profile.
No minimality or noncolorability argument is needed for these witnesses. -/
theorem EvenKempeFusionLens.bcCrossExactPair_terminalEdges_realize_fourArmCancellationProfile
    (graphData : SimpleGraphDartRotation.Data G)
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
        Subtype.val) :
    lens01.bRoute.leftEdge.1 ∈
        (lens01.bRoute.firstPrefixToCrossSite
          lens23.cRoute site).support ∧
      C lens01.bRoute.leftEdge.1 = b ∧
      pair.IsPrefixCancellationEdge C b
        (retainedEdgeToAmbientEdge data lens01.bRoute.leftEdge.1) ∧
      lens23.cRoute.leftEdge.1 ∈
        (lens01.bRoute.secondPrefixToCrossSite
          lens23.cRoute site).support ∧
      C lens23.cRoute.leftEdge.1 = c ∧
      pair.IsPrefixCancellationEdge C c
        (retainedEdgeToAmbientEdge data lens23.cRoute.leftEdge.1) ∧
      lens01.bRoute.leftEdge.1 ≠ lens23.cRoute.leftEdge.1 ∧
      lens01.bRoute.rightEdge.1 ∈
        (lens01.bRoute.firstSuffixFromCrossSite
          lens23.cRoute site).support ∧
      C lens01.bRoute.rightEdge.1 = b ∧
      pair.IsSuffixCancellationEdge C b
        (retainedEdgeToAmbientEdge data lens01.bRoute.rightEdge.1) ∧
      lens23.cRoute.rightEdge.1 ∈
        (lens01.bRoute.secondSuffixFromCrossSite
          lens23.cRoute site).support ∧
      C lens23.cRoute.rightEdge.1 = c ∧
      pair.IsSuffixCancellationEdge C c
        (retainedEdgeToAmbientEdge data lens23.cRoute.rightEdge.1) ∧
      lens01.bRoute.rightEdge.1 ≠ lens23.cRoute.rightEdge.1 := by
  have hcrossColor : C site.1 = a :=
    lens01.bRoute.color_eq_first_of_crossSite lens23.cRoute hbc site
  have hprefixBTrail : lens01.bRoute.leftEdge.1.1 ∈
      pair.prefixTrail.edges := by
    rw [hprefixEdges]
    apply List.mem_map.mpr
    exact ⟨lens01.bRoute.leftEdge.1,
      (lens01.bRoute.crossSplice lens23.cRoute site).start_mem_support,
      rfl⟩
  have hprefixCTrail : lens23.cRoute.leftEdge.1.1 ∈
      pair.prefixTrail.edges := by
    rw [hprefixEdges]
    apply List.mem_map.mpr
    exact ⟨lens23.cRoute.leftEdge.1,
      (lens01.bRoute.crossSplice lens23.cRoute site).end_mem_support,
      rfl⟩
  have hsuffixBTrail : lens01.bRoute.rightEdge.1.1 ∈
      pair.suffixTrail.edges := by
    rw [hsuffixEdges]
    apply List.mem_map.mpr
    exact ⟨lens01.bRoute.rightEdge.1,
      (lens01.bRoute.crossSuffixSplice
        lens23.cRoute site).start_mem_support, rfl⟩
  have hsuffixCTrail : lens23.cRoute.rightEdge.1.1 ∈
      pair.suffixTrail.edges := by
    rw [hsuffixEdges]
    apply List.mem_map.mpr
    exact ⟨lens23.cRoute.rightEdge.1,
      (lens01.bRoute.crossSuffixSplice
        lens23.cRoute site).end_mem_support, rfl⟩
  have hprefixBCancellation : pair.IsPrefixCancellationEdge C b
      (retainedEdgeToAmbientEdge data lens01.bRoute.leftEdge.1) := by
    apply pair.isPrefixCancellationEdge_retainedEdgeToAmbientEdge
      C b lens01.bRoute.leftEdge.1 hprefixBTrail lens01.bRoute.leftColor
    rw [lens01.bRoute.leftColor, hcrossColor]
    exact hab.symm
  have hprefixCCancellation : pair.IsPrefixCancellationEdge C c
      (retainedEdgeToAmbientEdge data lens23.cRoute.leftEdge.1) := by
    apply pair.isPrefixCancellationEdge_retainedEdgeToAmbientEdge
      C c lens23.cRoute.leftEdge.1 hprefixCTrail lens23.cRoute.leftColor
    rw [lens23.cRoute.leftColor, hcrossColor]
    exact hac.symm
  have hsuffixBCancellation : pair.IsSuffixCancellationEdge C b
      (retainedEdgeToAmbientEdge data lens01.bRoute.rightEdge.1) := by
    apply pair.isSuffixCancellationEdge_retainedEdgeToAmbientEdge
      C b lens01.bRoute.rightEdge.1 hsuffixBTrail lens01.bRoute.rightColor
    rw [lens01.bRoute.rightColor, hcrossColor]
    exact hab.symm
  have hsuffixCCancellation : pair.IsSuffixCancellationEdge C c
      (retainedEdgeToAmbientEdge data lens23.cRoute.rightEdge.1) := by
    apply pair.isSuffixCancellationEdge_retainedEdgeToAmbientEdge
      C c lens23.cRoute.rightEdge.1 hsuffixCTrail lens23.cRoute.rightColor
    rw [lens23.cRoute.rightColor, hcrossColor]
    exact hac.symm
  exact ⟨
    (lens01.bRoute.firstPrefixToCrossSite
      lens23.cRoute site).start_mem_support,
    lens01.bRoute.leftColor, hprefixBCancellation,
    (lens01.bRoute.secondPrefixToCrossSite
      lens23.cRoute site).start_mem_support,
    lens23.cRoute.leftColor, hprefixCCancellation,
    edge_ne_of_color_eq_of_color_eq_of_ne C
      lens01.bRoute.leftColor lens23.cRoute.leftColor hbc,
    (lens01.bRoute.firstSuffixFromCrossSite
      lens23.cRoute site).end_mem_support,
    lens01.bRoute.rightColor, hsuffixBCancellation,
    (lens01.bRoute.secondSuffixFromCrossSite
      lens23.cRoute site).end_mem_support,
    lens23.cRoute.rightColor, hsuffixCCancellation,
    edge_ne_of_color_eq_of_color_eq_of_ne C
      lens01.bRoute.rightColor lens23.cRoute.rightColor hbc⟩

/-- In the exact `cb` orientation, the same canonical terminal witnesses
realize the color-exchanged four-arm profile. -/
theorem EvenKempeFusionLens.cbCrossExactPair_terminalEdges_realize_fourArmCancellationProfile
    (graphData : SimpleGraphDartRotation.Data G)
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
        Subtype.val) :
    lens01.cRoute.leftEdge.1 ∈
        (lens01.cRoute.firstPrefixToCrossSite
          lens23.bRoute site).support ∧
      C lens01.cRoute.leftEdge.1 = c ∧
      pair.IsPrefixCancellationEdge C c
        (retainedEdgeToAmbientEdge data lens01.cRoute.leftEdge.1) ∧
      lens23.bRoute.leftEdge.1 ∈
        (lens01.cRoute.secondPrefixToCrossSite
          lens23.bRoute site).support ∧
      C lens23.bRoute.leftEdge.1 = b ∧
      pair.IsPrefixCancellationEdge C b
        (retainedEdgeToAmbientEdge data lens23.bRoute.leftEdge.1) ∧
      lens01.cRoute.leftEdge.1 ≠ lens23.bRoute.leftEdge.1 ∧
      lens01.cRoute.rightEdge.1 ∈
        (lens01.cRoute.firstSuffixFromCrossSite
          lens23.bRoute site).support ∧
      C lens01.cRoute.rightEdge.1 = c ∧
      pair.IsSuffixCancellationEdge C c
        (retainedEdgeToAmbientEdge data lens01.cRoute.rightEdge.1) ∧
      lens23.bRoute.rightEdge.1 ∈
        (lens01.cRoute.secondSuffixFromCrossSite
          lens23.bRoute site).support ∧
      C lens23.bRoute.rightEdge.1 = b ∧
      pair.IsSuffixCancellationEdge C b
        (retainedEdgeToAmbientEdge data lens23.bRoute.rightEdge.1) ∧
      lens01.cRoute.rightEdge.1 ≠ lens23.bRoute.rightEdge.1 := by
  have hcrossColor : C site.1 = a :=
    lens01.cRoute.color_eq_first_of_crossSite lens23.bRoute hbc.symm site
  have hprefixCTrail : lens01.cRoute.leftEdge.1.1 ∈
      pair.prefixTrail.edges := by
    rw [hprefixEdges]
    apply List.mem_map.mpr
    exact ⟨lens01.cRoute.leftEdge.1,
      (lens01.cRoute.crossSplice lens23.bRoute site).start_mem_support,
      rfl⟩
  have hprefixBTrail : lens23.bRoute.leftEdge.1.1 ∈
      pair.prefixTrail.edges := by
    rw [hprefixEdges]
    apply List.mem_map.mpr
    exact ⟨lens23.bRoute.leftEdge.1,
      (lens01.cRoute.crossSplice lens23.bRoute site).end_mem_support,
      rfl⟩
  have hsuffixCTrail : lens01.cRoute.rightEdge.1.1 ∈
      pair.suffixTrail.edges := by
    rw [hsuffixEdges]
    apply List.mem_map.mpr
    exact ⟨lens01.cRoute.rightEdge.1,
      (lens01.cRoute.crossSuffixSplice
        lens23.bRoute site).start_mem_support, rfl⟩
  have hsuffixBTrail : lens23.bRoute.rightEdge.1.1 ∈
      pair.suffixTrail.edges := by
    rw [hsuffixEdges]
    apply List.mem_map.mpr
    exact ⟨lens23.bRoute.rightEdge.1,
      (lens01.cRoute.crossSuffixSplice
        lens23.bRoute site).end_mem_support, rfl⟩
  have hprefixCCancellation : pair.IsPrefixCancellationEdge C c
      (retainedEdgeToAmbientEdge data lens01.cRoute.leftEdge.1) := by
    apply pair.isPrefixCancellationEdge_retainedEdgeToAmbientEdge
      C c lens01.cRoute.leftEdge.1 hprefixCTrail lens01.cRoute.leftColor
    rw [lens01.cRoute.leftColor, hcrossColor]
    exact hac.symm
  have hprefixBCancellation : pair.IsPrefixCancellationEdge C b
      (retainedEdgeToAmbientEdge data lens23.bRoute.leftEdge.1) := by
    apply pair.isPrefixCancellationEdge_retainedEdgeToAmbientEdge
      C b lens23.bRoute.leftEdge.1 hprefixBTrail lens23.bRoute.leftColor
    rw [lens23.bRoute.leftColor, hcrossColor]
    exact hab.symm
  have hsuffixCCancellation : pair.IsSuffixCancellationEdge C c
      (retainedEdgeToAmbientEdge data lens01.cRoute.rightEdge.1) := by
    apply pair.isSuffixCancellationEdge_retainedEdgeToAmbientEdge
      C c lens01.cRoute.rightEdge.1 hsuffixCTrail lens01.cRoute.rightColor
    rw [lens01.cRoute.rightColor, hcrossColor]
    exact hac.symm
  have hsuffixBCancellation : pair.IsSuffixCancellationEdge C b
      (retainedEdgeToAmbientEdge data lens23.bRoute.rightEdge.1) := by
    apply pair.isSuffixCancellationEdge_retainedEdgeToAmbientEdge
      C b lens23.bRoute.rightEdge.1 hsuffixBTrail lens23.bRoute.rightColor
    rw [lens23.bRoute.rightColor, hcrossColor]
    exact hab.symm
  exact ⟨
    (lens01.cRoute.firstPrefixToCrossSite
      lens23.bRoute site).start_mem_support,
    lens01.cRoute.leftColor, hprefixCCancellation,
    (lens01.cRoute.secondPrefixToCrossSite
      lens23.bRoute site).start_mem_support,
    lens23.bRoute.leftColor, hprefixBCancellation,
    edge_ne_of_color_eq_of_color_eq_of_ne C
      lens01.cRoute.leftColor lens23.bRoute.leftColor hbc.symm,
    (lens01.cRoute.firstSuffixFromCrossSite
      lens23.bRoute site).end_mem_support,
    lens01.cRoute.rightColor, hsuffixCCancellation,
    (lens01.cRoute.secondSuffixFromCrossSite
      lens23.bRoute site).end_mem_support,
    lens23.bRoute.rightColor, hsuffixBCancellation,
    edge_ne_of_color_eq_of_color_eq_of_ne C
      lens01.cRoute.rightColor lens23.bRoute.rightColor hbc.symm⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
