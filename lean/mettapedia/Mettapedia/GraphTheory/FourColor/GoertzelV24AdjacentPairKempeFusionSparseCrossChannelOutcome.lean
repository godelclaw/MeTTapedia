import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelMultiplicityCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOppositePortCircuit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24AdjacentPairBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance sparseCrossChannelOutcomeGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Two separated fusion lenses either already contain a strictly shorter
primal circuit, or both cross channels are singletons at most and their
remaining interaction is exactly an opposite-port trail or disjoint route
containers. -/
theorem EvenKempeFusionLens.sparseCrossChannelOutcome_or_exists_shortPrimalCircuit
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
    (∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧
          circuit.length < lens01.bRoute.ambientPath.length +
            lens23.cRoute.ambientPath.length) ∨
      (∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧
          circuit.length < lens01.cRoute.ambientPath.length +
            lens23.bRoute.ambientPath.length) ∨
      ((lens01.bcCrossSites lens23).length ≤ 1 ∧
          (lens01.cbCrossSites lens23).length ≤ 1) ∧
        ((∃ trail : G.Walk (data.defectVertex 0) (data.defectVertex 2),
            trail.IsTrail ∧ 0 < trail.length ∧
              (trail.edges ⊆
                  (lens01.bRoute.ambientPath.support ++
                    lens23.cRoute.ambientPath.support).map Subtype.val ∨
                trail.edges ⊆
                  (lens01.cRoute.ambientPath.support ++
                    lens23.bRoute.ambientPath.support).map Subtype.val)) ∨
          (lens01.bRoute.ambientPath.support ++
              lens01.cRoute.ambientPath.support).Disjoint
            (lens23.bRoute.ambientPath.support ++
              lens23.cRoute.ambientPath.support)) := by
  have hmultiplicity :=
    lens01.crossChannels_subsingleton_or_exists_shortPrimalCircuit
      lens23 hab hac hbc
  have hinteraction :=
    lens01.exists_routeSupportedPrimalTrail_or_routeUnions_disjoint
      lens23 hdata hab hac hbc hbDisjoint hcDisjoint
  rcases hmultiplicity with hsparse | hshort
  · exact Or.inr (Or.inr ⟨hsparse, hinteraction⟩)
  · rcases hshort with hbcShort | hcbShort
    · exact Or.inl hbcShort
    · exact Or.inr (Or.inl hcbShort)

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

/-- Sparse cross-channel normal form for an adjacent-pair deletion.  The
opposite-port alternative is restored to a simple ambient cycle through the
central edge, while retaining the exact route support of its deleted arc. -/
theorem EvenKempeFusionLens.exists_oppositePortCycle_or_disjoint_of_sparse_or_shortPrimalCircuit
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support) :
    (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
        (circuit : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk start start),
        circuit.IsCircuit ∧
          circuit.length < lens01.bRoute.ambientPath.length +
            lens23.cRoute.ambientPath.length) ∨
      (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
        (circuit : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk start start),
        circuit.IsCircuit ∧
          circuit.length < lens01.cRoute.ambientPath.length +
            lens23.bRoute.ambientPath.length) ∨
      ((lens01.bcCrossSites lens23).length ≤ 1 ∧
          (lens01.cbCrossSites lens23).length ≤ 1) ∧
        ((∃ path : (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).Walk
              (data.retainedPort 0) (data.retainedPort 2),
            path.IsPath ∧
              (data.oppositePortClosure path).IsCycle ∧
              GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue
                  data ∈ (data.oppositePortClosure path).edges ∧
              (path.edges ⊆
                  (lens01.bRoute.ambientPath.support ++
                    lens23.cRoute.ambientPath.support).map Subtype.val ∨
                path.edges ⊆
                  (lens01.cRoute.ambientPath.support ++
                    lens23.bRoute.ambientPath.support).map Subtype.val)) ∨
          (lens01.bRoute.ambientPath.support ++
              lens01.cRoute.ambientPath.support).Disjoint
            (lens23.bRoute.ambientPath.support ++
              lens23.cRoute.ambientPath.support)) := by
  rcases lens01.sparseCrossChannelOutcome_or_exists_shortPrimalCircuit
      lens23 hdata hab hac hbc hbDisjoint hcDisjoint with
    hbcShort | hcbShort | ⟨hsparse, hinteraction⟩
  · exact Or.inl hbcShort
  · exact Or.inr (Or.inl hcbShort)
  · refine Or.inr (Or.inr ⟨hsparse, ?_⟩)
    rcases hinteraction with
      ⟨trail, _htrail, _hpositive, hrouteSupport⟩ | hdisjoint
    · let retainedTrail :
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2) :=
        trail.copy (by rfl) (by rfl)
      rcases data.exists_oppositePortClosure_isCycle_with_edges_subset
          retainedTrail with ⟨path, hpath, hcycle, hpathSubset⟩
      refine Or.inl ⟨path, hpath, hcycle,
        data.centralEdgeValue_mem_oppositePortClosure_edges path, ?_⟩
      rcases hrouteSupport with hbcSupport | hcbSupport
      · exact Or.inl (hpathSubset.trans (by
          simpa only [retainedTrail, SimpleGraph.Walk.edges_copy] using
            hbcSupport))
      · exact Or.inr (hpathSubset.trans (by
          simpa only [retainedTrail, SimpleGraph.Walk.edges_copy] using
            hcbSupport))
    · exact Or.inr hdisjoint

/-- The sparse cross-channel normal form is reached by the canonical cyclic
profile of every graph-backed vertex-minimal counterexample. -/
theorem CyclicKempeProfile.exists_sparseCrossChannelResolution_or_shortPrimalCircuit_of_minimal
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
          ((∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
              (circuit : (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).Walk start start),
              circuit.IsCircuit ∧
                circuit.length < lens01.bRoute.ambientPath.length +
                  lens23.cRoute.ambientPath.length) ∨
            (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
              (circuit : (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).Walk start start),
              circuit.IsCircuit ∧
                circuit.length < lens01.cRoute.ambientPath.length +
                  lens23.bRoute.ambientPath.length) ∨
            ((lens01.bcCrossSites lens23).length ≤ 1 ∧
                (lens01.cbCrossSites lens23).length ≤ 1) ∧
              ((∃ path : (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk
                    (data.retainedPort 0) (data.retainedPort 2),
                  path.IsPath ∧
                    (data.oppositePortClosure path).IsCycle ∧
                    GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue
                        data ∈ (data.oppositePortClosure path).edges ∧
                    (path.edges ⊆
                        (lens01.bRoute.ambientPath.support ++
                          lens23.cRoute.ambientPath.support).map Subtype.val ∨
                      path.edges ⊆
                        (lens01.cRoute.ambientPath.support ++
                          lens23.bRoute.ambientPath.support).map Subtype.val)) ∨
                (lens01.bRoute.ambientPath.support ++
                    lens01.cRoute.ambientPath.support).Disjoint
                  (lens23.bRoute.ambientPath.support ++
                    lens23.cRoute.ambientPath.support))) := by
  rcases profile.exists_two_sameFamilySeparatedFusionLenses_of_minimal
      minimal hab with
    ⟨C', hclosure, hC', hconstant, lens01, lens23,
      hbDisjoint, hcDisjoint⟩
  have hthird := third_color_properties hab.1 hab.2.1 hab.2.2
  have hac : a ≠ a + b := hthird.2.1.symm
  have hbc : b ≠ a + b := hthird.2.2.symm
  have houtcome :=
    EvenKempeFusionLens.exists_oppositePortCycle_or_disjoint_of_sparse_or_shortPrimalCircuit
      lens01 lens23 profile.boundaryWellFormed hab.2.2 hac hbc
        hbDisjoint hcDisjoint
  exact ⟨C', hclosure, hC', hconstant, lens01, lens23,
    hbDisjoint, hcDisjoint, houtcome⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
