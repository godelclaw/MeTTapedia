import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelPrimalTrail

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24AdjacentPairBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelOutcomeGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Two complementary same-family-separated fusion lenses have an exact
structural alternative: a cross-family overlap lifts to a nontrivial primal
trail between opposite defects, while absence of both cross channels makes
the complete route containers edge-disjoint. -/
theorem EvenKempeFusionLens.exists_primalTrail_or_routeUnions_disjoint
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support) :
    (∃ trail : G.Walk (data.defectVertex 0) (data.defectVertex 2),
        trail.IsTrail ∧ 0 < trail.length) ∨
      (lens01.bRoute.ambientPath.support ++
          lens01.cRoute.ambientPath.support).Disjoint
        (lens23.bRoute.ambientPath.support ++
          lens23.cRoute.ambientPath.support) := by
  by_cases hbcSites : lens01.bcCrossSites lens23 = []
  · by_cases hcbSites : lens01.cbCrossSites lens23 = []
    · right
      rw [List.disjoint_left]
      intro edge hleft hright
      have hintersection :
          ∃ shared : G.edgeSet,
            shared ∈ lens01.bRoute.ambientPath.support ++
                lens01.cRoute.ambientPath.support ∧
              shared ∈ lens23.bRoute.ambientPath.support ++
                lens23.cRoute.ambientPath.support :=
        ⟨edge, hleft, hright⟩
      rcases (lens01.routeUnions_intersect_iff_crossChannel_nonempty
          lens23 hbDisjoint hcDisjoint).1 hintersection with
        hbcNonempty | hcbNonempty
      · exact hbcNonempty hbcSites
      · exact hcbNonempty hcbSites
    · left
      exact lens01.exists_cbPrimalTrail lens23 hdata hab hac hbc
        hbDisjoint hcDisjoint hcbSites
  · left
    exact lens01.exists_bcPrimalTrail lens23 hdata hab hac hbc
      hbDisjoint hcDisjoint hbcSites

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  adjacentFusionLensGraphEdgeSetDecidableEq
  adjacentFusionLensRetainedVertexSetFintype
  adjacentFusionLensRetainedVertexSetDecidableEq

/-- Every cyclic adjacent-pair profile in a graph-backed vertex-minimal
counterexample reaches a constant boundary state with two separated fusion
lenses.  Their interaction is witnessed either by a nontrivial primal trail
between opposite boundary defects or by disjoint complete route containers. -/
theorem CyclicKempeProfile.exists_primalTrail_or_disjointFusionContainers_of_minimal
    {graphData : SimpleGraphDartRotation.Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data)
    {a b : Color} (hab : ValidColorPair a b) :
    ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
      C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).lineGraph.KempeClosure profile.coloring ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
      (∀ port : Fin 4,
        data.degreeTwoBoundaryData.colorWord C' port = a) ∧
      ∃ (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
          C' a b (a + b) 0 1)
        (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
          C' a b (a + b) 2 3),
        lens01.bRoute.ambientPath.support.Disjoint
            lens23.bRoute.ambientPath.support ∧
          lens01.cRoute.ambientPath.support.Disjoint
            lens23.cRoute.ambientPath.support ∧
          ((∃ trail : (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).Walk
                (data.degreeTwoBoundaryData.defectVertex 0)
                (data.degreeTwoBoundaryData.defectVertex 2),
              trail.IsTrail ∧ 0 < trail.length) ∨
            (lens01.bRoute.ambientPath.support ++
                lens01.cRoute.ambientPath.support).Disjoint
              (lens23.bRoute.ambientPath.support ++
                lens23.cRoute.ambientPath.support)) := by
  rcases profile.exists_two_sameFamilySeparatedFusionLenses_of_minimal
      minimal hab with
    ⟨C', hclosure, hC', hconstant, lens01, lens23,
      hbDisjoint, hcDisjoint⟩
  have hthird := third_color_properties hab.1 hab.2.1 hab.2.2
  have hac : a ≠ a + b := hthird.2.1.symm
  have hbc : b ≠ a + b := hthird.2.2.symm
  have houtcome := lens01.exists_primalTrail_or_routeUnions_disjoint
    lens23 profile.boundaryWellFormed hab.2.2 hac hbc
      hbDisjoint hcDisjoint
  exact ⟨C', hclosure, hC', hconstant, lens01, lens23,
    hbDisjoint, hcDisjoint, houtcome⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
